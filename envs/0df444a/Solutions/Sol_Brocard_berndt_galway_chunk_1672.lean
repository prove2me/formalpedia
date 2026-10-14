-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1672
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:09:44.938739+00:00
-- url     : https://prove2.me/submissions/31bf86a1-9a6d-4434-979c-2616a32b1b45

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 300539568 ≤ n < 300719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 300540818 1250 300539568 300539581
    0xa060e0c0a06030b030a050106081506041a01080a0e06070305011d090d03020d060305070f17030304050303070c06091202031908060303040510140a18053a0804080f15 73
    0x411010b40100d20078540d950708100d0840e1000c000c200030082c0d120000300502c0751590710b02507451034581030111008105100044941c181170089200d880e000c0319031082a904180010b5401410082403440000d9883e5810b01c42800d08000c0ea42c0106130f1038500042039410302e0b01c090a403106240f072255000034040c080c40714205c4000352461310944107140c01031f01c03045103c4243e0003500040c1e1001d07140348034031031021440c2c400011401084680800784e0600d0f0541c0f407100c064403170000f1070700980700350000c6c000500981c0c0a0155200c0031342c454500001e01099580e1940610030403100e6000c016072011440310ba5965224440d1240c07801d050400400d145024ac000070781d81d126501520380100b0148d1070300750515020f002c0d0b010517451507140035034880180e054010720580c68401e070040c0812007c00000f0f42070510b50301c07101041c044d000555161036244600040b103e55504c1c415221418030007115404a11554080c0c005010701a01400d9503101c0c02c03a503e0710f45003100d24a030340c003104001c062005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 300542068 1250 300540818 300540829
    0x81303031413031101020c0d080c0d090305151905070903031407020a030f03050c1e120906031b25050106080607091e0e0103030f02060f0601091a16050a060e0c 70
    0x71250703c03004413134940107a500102c0c20422014805904401c590808a042115800c007800b10350005804840030941b83c1d1004442c1c0c00b030544005002900400c50f609100d0308407800459201c90f400d141c0350540c152030708441e022600112a41800a4640501803040584c00031094204a071405047c07424903110b90001a00c290395071000504880c54537800404040c050001c0d6120001e08106a81032001d40001c002c40c0e15041d50404203160042c101c81c40c0094107a203090700c6900c403015003098195030740d8480c6010b60384141d52001e003c2079418000310000a5404040c00c1000003548190000101d440c07400c2c030b09681c000c0c0c1110096130411001c000c8041c0c0c0c840c1150080715504041c11520700c200030748030140502240c028440040c240d100100a00d9003049040b0840d031003907800c031012640c4480f41302c6459041500d62600160151504000000b18040c03041c00300920b05a40500d4184030002c007281170780c004a0304550540003000c111090154030705c11400041c40c950054403002506800040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 300543318 1250 300542068 300542107
    0x61509010f0608090c0405130c080a080a031e0e010605040b060a0804021c020910031407080d0309030201020f0d1b031a0103020a02010e10020c16080d0f0c0813030314 73
    0x1003c1003103070000101c901d082000040003100010300f0422142c140030044a2040180c520305075241102440c00140501c000900308114940142141c0e041121304e8504401500c0c0c0090b03030140a00c42da044070706214000d40f040001d44d0034120000944a032410084c40207403810202d60a1080c0b00900010307408907003000707440b0340c066030413110b691f01c0000200280c29180d54841010b9001006a4100483c860300c5107824400d9a0184e000070001503404241c10340e0740c842c207024000542d0400e415080c803003802600f04000444c400c0c000541001181e0400c1607141d00002000240540c658101d07d01403230300005891060306044c41d050000881800d0030103511205209801d0400d40e00050348070b2413610030340c803514000d030f041000d441504007800e00c040041d40000e0f0000703415010b08184220000320180d0440210f03044040070302003032482d0503002d0300c4000c1610402c1c4180700c030310000700c0d00141d10312000303003405061402811380d2a801d41c10300500e400e14500d180b100030b0340c04100d5003407035440f03517100e24 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 300544568 1250 300543318 300543329
    0x160e0406051b070602070b0c07020d0212010609020f040302011704200f06070312051e010b0a0318060608060114060304020d051c020c04050702070608190207080c061509010f 76
    0x1240399200c140214003810035101d00b1002503040841d030f203010010749400803c411401034902006075110740010b18020b2044080095016003010f100d0f0005007040c8214050304480c403000021010340d149094800ea900851000d18103c2000409108560708064811000000040f03030f42110701d081e03078402150040e601c1c126608816400b45000340360742c0f48154800f03002070146c0741e1a100c584520380a0012145500048a0b07507040c14000f0b4640c0030010302001404481001036840c5910309404034000d40e00050001041648800303c0380c4503e07092078140005140308481c002900ca1400e10707103d04050068020310741030200b1001c141c08d01d5a0b030274140e941168045901d54107441030392900b6840c24401d442903945081c25102044c00141e00400c2e080c92451050b03d06221039030391103070106e840d94030500502c008641c0034004540d042034601c8101d03100d8105654010301c7c0c121151110401504001c00301d18050384003004200301210702990307603d01d01400b23075098591135041400d0a070041c0814041e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 300545818 1250 300544568 300544571
    0x209030f0f07060216121b0303120f0203061c1b1203032009040b01030b221802011e03090203031201090f05070e040c030b0a080d0801080d05090d03020a0210020d02160e0406 76
    0x40d50510000ca08007e01080a00030300e448426581d00c0d01409650519401c1e01d415403070aa1103445804650085912810340208180b55408007462905080c650300d40e03041d618605045c0d4100c1c00e0070241410700c000b50009080820007800c1030f103002400d41c1e13036100442c482d90441181d00c0350244000000d4901d032040c1101c002c00c1d00720032000120000c21003444880d52002e05007080000d503c4440101400c62640020180581052441025807034158424020300003100e008000300010072a2450004410f6545804200c081040d00041e1454010000c040c00812040d4010881c0f505c451080360b000c1c00401d4401d000518203084054811104810140d0255464601140c0e8070b5120f580903c0b00c241000b005400c001e61078200380c6594006240c0758002040c078140010480540000e000c4407002c4482e56401d190030b032a0024007c08100c49102102548214400d00380143c0e10750300e00003d031105590050505402450000340703804120420b000300017840c41801d101782231030702491035070058001b0750 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 300547068 1250 300545818 300545849
    0x2030a1e0b0a06091104051005030c0d060305030d0b09070c0206031b0705030a0906081302040906060b0a08070e0f0a141c030503010f060302040b1c0209030f0f07060216 74
    0x50355034a1161910300a0101c080442004002803080c0c1c010429520380d07800420904007000455402c0d446a03000340c0754007501c4010940703c010300c510002d591140d00e9811742d0341000c856200e0903059448540045803907410204c6c81c42540c68180c4940b80c844441181c0300e0004d030170a002d010300400640400030340a0300b400000209994490020b844a64040992035030341d8442030b0800a48a800074050303440010b038081c0000a49510500b0348a02451103104141e6078000960700b048020f0800e5a0111502621488001401100d01c0b0181a80c01c0880d102e00c4107a140050b00200395854a0950070300c10079181201c882c40740c4a400356042501c0012403401001481000003960301d1307800755410b0904910b201c1c843c0b020154000f002e1412501e1018217105050785681c400d609070f020f58000c840310f1180610aa00140e4221103140440240c2500300525150384540030a08060200c0c4242034603510a2403a00e03403c1404000e0140100300500c05086180c0c0680d0809145440d14410300e00c140b609620f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 300548318 1250 300547068 300547103
    0x201030b0a0f03030c05100209010206222009010801020f0d0f06080d020d02060702191509150b031c020a2004060f060315080606010f0e030102030a02120c0702030a 72
    0x54450000d08822400d0280c42c0c1e5036860018048100c0c54001c586600039030301d1000b401001d174001d03550382c81c0c0142c01078140ca94a00a00341951110380d94160010410281e0000c00702da650b00074039108881e907841c54200362440c0e40510a4000040e4444012070f03104010740d5400c0c41e282801d68045480c0504080740d038a00c8900081c0284c40c00d40c00c03604540c0103502e00f52442540010b00c44107482d240d50240c031400da03515003042c0c2c0c69007503031811843c0c081002d40c0e18900003003400d011103034281c544c2d403000070b0102c82d562107004240f42000c0c02260790b59a90380340c0c3c22480c0303420060602c11509000707000c5224040ca0340000c0d101c40360b0900090442d5500400409840c2c0ca030803860005420103403007000360319600e11104000784c2d0385200f42804245401004c841111200401400b900e40e254001c0015456800045424006600b6450100030842d0000f0207183e901b8002913014024009001da10f4442100725690702030b4000d07050b44099031013005840016180407540d00f00c6503800c801c42d60300922206 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 300549568 1250 300548318 300548329
    0x9020c0309040c0309020a081f022203110a08011505040510030515010914040224250201020c1212030a0e0f0f101118060f0729070c0201030b 62
    0x100c0034035910904201ea401c00700f03941940700c990018000c807a0b540d4483d986480c210b1315030841c1c0314000350309145902c10740000903060b0014001d14820518084401030104c00f04c0703a070030a054000321542d0082c0840895030340b404800d05401340100c403008000d09984101e808400207114800c0d02c0c000c0351203000041d0b400e183c2403090401503400c9020307101c3c494074840310300400000902800d8803107031400320504806580481102e20540d070181150004c00300c4c000c80790040a400b410420303180402004400c00182c41c0001d40d040010744101606243c1a840c40064103003003800705614090000740c640c001440b00d002079202514000700000070742e66141c1d200344e2009030541902c1841184251203144454a00000708050905200c5040e01d05549100d04650140d4401014411034150188602101c418060803014000c6000900725407514980b560ba4140f1174010b242c050343c404d28020550755548000c507008900020032031210742e20078a0001406040d81c1718605020b41010780c0d491450343d058991 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 300550818 1250 300549568 300549577
    0x60f0f0307030b160e0f19080a1b0602011e0f0f0504110f0906100e130e031b030405060f1b010e0d031802010f110a06020f0712020f030409020c03 64
    0x2405072545142c60381402c4007100400c2d66080c9184000b0341c03013400d00354410311001c50040380c0142568801c0302030b001000824442003030800e059a514207400904e42c1020040716588a2060f2010040700032404044c406600559103c1025039050404881c80385c01c424110641d02188900006420950901410028144108800c840d030740b0300420b10050002c8404420f44055081380d84082443e000340503c206080152600c0d0303000266200710a000c14051202041d5202024141d03e039180c5214000c0001d442c0d4039107040f0b08a40000500205a50030544c1c0c4407071a4200d070009628040c40d00b400718145101728980e404500d000440c4000e045820308058070b800b60700d00e0000740039601c085081141c44080c3c800600d00820720704006190601641076074442569016181c041c4080540e080c25510a141c10700220501d0180700e481c50b00094540c40138140029404984944a860318686400c9068007440b464080d984001c80103400320500100b11001c0e2481504050703100c4001c0c1074080d2446c00b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 300552068 1250 300550818 300550849
    0xc050d080f180405060d03051b0a1509030206090f070605030a09060c050301051c0b07030e100203090d1115180109020310050609180c040b0105043515060f 68
    0xe0010760b40740c0312000e4407407441124004440c10007540d1250401c100042030810030080100b0818411250550340036100300e114040004103840950140b0b03504d510034402605808090300d903490200c007082c544d04005450380104600e000b42101004120790f640d445080784074540c100517001001070482c0540340c00c00c9506950001083c802003154100152040e0001d008241c000c44121031440c0a04000d855100031051f0401c400900945565400324040c015806a02d100d9200b0080d0b035110380000c61000318810b006180c0036100c3c4900d4400024450000241d00c1c80b41a80440c010711014058521000d410130000070559401d030070300810150150440e0b01c00a54940102022454410101c2e04410700c644000c9904020320746c0c49030318480e0050585c01012419500c64102e594450500390300c80022100d0505119003001c1e070300c80e19854503801c2d1020b8001c641807005964400440b40880c0358030860a0b07500900050346105c0310011640000070410752290454046092003900c8220703107074600ca030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 300553318 1250 300552068 300552097
    0x110a0803030f013602030c071b0510050f0d0c021f0b09060d15090f060603030f02010b010206060d0809040e0627031201030b04060b1c020118030c050d08 67
    0x2c0c00203a0416040000d115441e0201130110f607203c4010030240f42e4421042c440c6018a400c0400d03506014001d40000b40101d01c24002080074001041d10709414010240c0801d5a0b100c40780d0800b020f014a440b041a48042800400d22111148640d42c00a5070302d580c0d0701c408001401031800100320714004980403c5180300c1e81c15001410300c4802c60304000807120090b14490429296441400348610b01800082d01146203106c5032180c040071a00031446440c0204000007268003140c82c2d5a0880b64160f008030f0203e0030400300200e4132074080c02a03039140d0b0424005045585440c030041a0444100c680c0104800c03030029030030005a8580d0b12102c40822410100c415600c0d04802c40902c204640500030188408148907803141c000000071141c0307190115606141692840da80c6070788a03040071748201ea105488041280c0c071600c80340d190b0b994041d0410180d4160100303070300000d05540e003138000c800c2030701c100c466050000c20207503404502155026900410340140b5400d00c0d5015005004880030b1030f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 300554568 1250 300553318 300553321
    0x813020a0306020310050301110412150608031b010f09080306060f070f12091211120f0a05101d0a03050f0705121207030b0102120c12040f0e010b0307020a110a080303 73
    0x5801305c01301c02d5600c16802040303c440d541c1403041c0540118400c12044101c544240c0002500c40c813a1201c00b666814004a9040d80740c40c0c0560550b04240c0e0210f02c000d428480700c48081c0e109000e070050301040604104240c010310340718003400344030080130980161030010300c58500303001090132511910303000a8210050500c0345482040d0460030250880020b00419011480d403844101180000e0340c0140d9003016109904c00348192800b1320400c0a00900800000154500b010300100c12401d1040001e84280030f139248503034013140e0f03020f0300815000c0e80c01711803550b481e4030002d02c06030035a805090132500c40d544031200d1036261080d4100140030380110020340e2413620a01d07019018040b0051045c0d6250390740c14000300c2c1100c2d1320b81c078a240107a1101400b004504141d800401c2c82c40c0002c800d07501150b88040c8008900c2c1c1c0309920450743d00d50900d900700b0981401c3c02400b80500011075041d0319504203c0c500039a240b09030000642083d50b10003950f010740d0344030009000108050400d4907101d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 300555818 1250 300554568 300554581
    0x6100324090b040522060c0e041b2003030f0619060504060806010305070c0215043c1a090d1202010c020c040506010f0305040c0515040f05090103030813020a03060203 73
    0x90302c0810030043c0560b007001c2c045941c0306141d040c4088950320014038503000080320784813840a4908514a01c09003d81800b0349a25511580100040b418503030650307040840800100400102081001c08000070b803203d0000b031003100100c11650400700c040a2038a03980c0f18040000e104040a02d184810790411050010b910303a04400a00110f980300e0312144034540e1084015803e45008842c07410004200060300c81c0146007609002d05038284c0c01070040d0034252981e00c14040900d41c00444100c0307400303280d00844d44684103018a12071140d24000600160f00d05070060039210081d003011900d4003404074410600340c552110b000c0070140c00c000003998a5413030301e401038002e1140e8002040140509031070254182002d00800d8041c0e44180d60b040010b15030380408400400c0058021a10342400c100001000e82c1d810301c0d1082c1001d4001c96003540c0340c0c079040000c102d01e0190343c40701d401080100c00404c00b10380c100b04859400120032401e8424401c1031320001d1000d4205800003002e8620200c2406403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 300557068 1250 300555818 300555821
    0xb04022101180b090601030518100b090108031206090702031611010305090c100e0a0f030b0708070810090e100f0204050316080d0f0216080a06060501080610032409 72
    0x100c481100c1ca190160804803a442c007502c9005030b0040d0880003000c0800d4055102c0c0d4070042d07206901a2041c011001e48140030390400140d840c0c61601c554450760208a0761400714400ba0040000c1d000451a06102000c110108070000300514400d0350300d0700026803424024400c98800807507101c8165506022803414107400d035590300c2d071140024980030024981100004550b0440c4c04024030382d040e01d0060603030407540074840014150304080d04c10000980718044c0103e81c80914031500e107909443c549110010140d0a00821980800c929079091010055007403402c0419107001030f82c081740b40c80e040c803001898424024045a074041c9007280103405060b4943c09001910300440603078403200d141501c8440c09810900030081250890265804001c0c000c40095022038020300644002d5405140003006000050b0b00410b106d400400c0d07044200304030f40c4100c01c040c01d024203206589040c14004030710f9201801e01804c0c1030650320364020038803183d28400180515a1442c6880c402625042801b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 300558318 1250 300557068 300557071
    0x6030c091b0c0106090c1107050402030606160c050315040c0b0a090b1c0612030206131406011205010c080106080a0e0f0106180b031f0c120f090b0c03060102100b040221 74
    0x5d405610b4241c01c041014404c0900b00e01c0c100343d0780002c04046040c0b5003017100030341c03016200359413042040040703270302e43c0e0031981400c50060301860612900c00d16140a040c20413080c0c03003803600481c2d020820400081c1110f0f2102095841141c8155280c482410090340d148a00b43c201190f00b103030205104030200d450409140d9103410750780051140d160b442c141c48059060000c0000d003d80c00060000c2c0d4080035800c43c0341c0c1c07200d0040d003a40080800c00074480d82006801e030070000004012560035000e2102c24010041450410314207a003240d850448010440e00340a0055031250382c40c0d03001704546180411000508039900402005210398440741684841010b10092100c2410054208418980400c1c0c041c41c401d40d22840d11b41888158110800800084000006100000c0b48007000c0080d01c3c890102e03060403100d0001007041c06403c0401e500b407001400d4003c076a10404c10030403d03907404510880e41100042010400c13510130340000d4068007540021440d06d2410344c060310700c4840c880007045d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 300559568 1250 300558318 300558329
    0x513080c030c09090c0108092407030b030d09050f01031512021807052a07060903050f010e03090609040605060f070309080d0507030509011808070f08010506030c091b0c0106 76
    0x228004142c800c28403412150440d0544016008015004402d500440129920440c0501984c110380b00d01814007c1c140103c180014446520004211106030548500000b50074210002e092030407441000400c0101d0900480340034002d442d4003880c099009401408a0700c1d648031440389401e0300c41c1040300f6882da8030101a40b003225031030f0b5045108040c0001c021701590340c50352650310308140a020824000400b4080e0304401856070003194440d03c06000d0400580500d42d5001826443c6007006480d28212084508080e403404001596220000080780d503112802d580040c0ca88201c9400100201803035409590031010010341c048124900b04018a42c161103612146000c83e1144c00446d940c854803148400030030000c101141c042401017018000303810052400280c80b141c40304100ca881e4189074414003160780022824014983e401e1440c601030111940200280c0c034251001a6491003501c007068042d40c40c03031003c19034030945d0520030445800a034010039581d10102ca50707a0300810252003031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 300560818 1250 300559568 300559573
    0xf18031209040f02190509030703050609010f0c050a091701090501020705060f0f0108060c0711060c010c02070801020906030415110a021c050702010203030a24030308040b0a090c030f030513080c03 86
    0x450603c1d500b18405c0d241c0308803c4c403241c4610801240001d80789644210700c1c1c0b076070501c96001c0c0000040c50030420148181c408030004190102d10051300016502d60307100010a011090000d08075865101041608031030b20344865481a0111404060060110400140035940001040d0003484400030301180621610340b004c020356610351401100f441028000c0c006c450b000000490344407a461340141c00103900512410903400e07810000604154401d107641c61340c0c1c0e51200d600c18081d44d0107021070401411260000e500d40a1020005503491000800040c81011214085030040a49174012400c0c42006c00200340c0d6204d048002a507907514140241416500d403039135603c03120340f0640558101c0703603042e0002d504640724102d41d20080c00880746a4071700511440c50b02000011040f8442d0025800394032150784070b08090a0a0001d860010000c2c164070703061551040025000701c400d881244d0300310a1a401d260f407980760403507640c030410440c101c8560340900d01090548010582d1040c3c00405c408 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 300562068 1250 300560818 300560831
    0x20c06011d040f0602090105091002062e03030c06060302031f0e0d05030403050702180c070c05030106080a0f03030f091101110607050a0c140d0f14070203030f1803120904 75
    0x2107440c12007504581c010300344101041160b00003042c540251100342814185182030a0240000c1100c0c00192084003005030301107014801600e240021001c00c40d4200c0c0300b004514200719240d0007d03107070507100090070040350300101d4040c081c1c40e5100c1c0010303540c000c080d00e044110724140d55000101000c0c1e8055154541038186a84079400164403440e2540c44d1501411035491391011346c0c5c1500303c040180e030448452586202612076400032a8402d5844441c0c06480c3c0c41581040800340b01550880c0740203a140200501001034001050740069034000b003554030f0442c1d50329089010b080f018080c0c034a0141040701e500c00304620f03500780c400c880c4000c1e650809240c1c0c1c0140401c6e540c4009440010110344200801c0780d0b00b40c4030301ca00900c080d00401135503440e046a80c80725490a03032644487c80c0042c03005e14206d00d1040d4028100a112030427901c5050400b0926000642c6901c111025600c842a0001e81c0c002c004030f0001500d00740c41c20060a41c0c08600f8002000d03c00f80d0f0090358034501c1a132400a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 300563318 1250 300562068 300562109
    0x20304030b15030f06150f1306030311010c020615120f0303091e01050f01030b0703021b010501090e0a050312070908010905010f0b040221091e0109030806100e190801020c0601 77
    0x511a4443d045102c0d143c0c407960090002e1041189a410849420074440350001d00700c86140e02a000c0192f12039603e1100d81c040074440c0a00319001035960b50f007190420400e11852102c01910700c0d40145088401000e0132303c840000618200d00d03024080c80b6400b0100820001720b0012070590580d1101e20301c454002949000c50900300d840888019880e800801c0040c0081100c1411250341311245040061900d802440040e5100441c070f00c0f03468031070391544010b201d5009140204d494402880f4010008600d036030b0340b6181c603070080902644c6015600e80c0054050b5105213a440001d03d050402041540d5290a0041c081c114101060804604046201065003003510031074100c440c00d00000080401c192005c03041041001d0002011803091000301e00060055080460b0360704010000081d207110549005400c0000c01440e49205220300044c03101c0c3c1540140c100940e110f401c4542410309082c4404060ba1291103070401e00b642d40c40490307a100d1445000481c00e041e0b400385032024101000c0308 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 300564568 1250 300563318 300563323
    0x916030f060b030406091401140402100206073204080114010e0603100b0f0402031311041e051b0307050a120b0a0b030a02040302100807110f1c020304030b15030f 71
    0xd02c0b0b0740200328000c00001c0c01086280e413201d034170755126050120600400e945a182910341c0c0840d00710869201900b8001146401c2c002540021030030300141180d80b52801002c1e1100c0018210380f9000d9198402e450784403402960308a1210406290340d54880b0b4a81c42064000d0454038468841c02c41c007c40042400384030711070001c0c81804000c3c0107100f402e4030b01d02c1030390141c204002c2c00c541109048104484903910341c00650310075015000040c2d400c000c581809641224181c0900c0c0c000c0c0d1914489040b50b00c0600b10501e5002c4014001042d01d4540c0d00c0006940c0c0a10f00400d25404404414004510750280081001c201e0a5583d56060940458030300d040f21800c10345154000c100d0b40d410440001014061030b03220320b1240c0d00508140da0b98001c5603c14903204079641c0001c202004000b802500031000324100c40c10300009100b46002080b0081d41c1e01c06000c6980800301541c000c58445a1007082110007a44d80503014043c82e08040301007141440303000800511a0140324030003844a0b500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 300565818 1250 300564568 300564581
    0x6090f02191d04021c110903160e0c030c09030d0305060301150b04031211030a020606041406100516020301020c010518030a140a030204050607050a03110c010509040c030603020916030f 81
    0x1203000014692074002c00c100083d80030101c0b44041d4040310345146031400203407003201151425420744070341e208146401c0504018003807048513281c0b4098401440300018440704140e0002405658682d291241d480c05541c500138061510f61500c0340c003800c0d45d0740744c1c0c1c10b400c801d0107440c0a80003800220310194884549424502610f41286009d2100304046416030080700c4001500703060040c2c088400d003900303a003176600901c50302000da44048207104d901d0903e4410640d5a070350340d0007102c1e01e87c2002e200143c00c00170104c40303910400a010407041c0c10300208080c00040702d07074010021581c4280d000000c5018000465a042640390402076102d1003e40c0402110000ca2041ea51240300c1130700b1510f0441242c001e541180e04255003071001046513280c0070b0003000c1c62801a8000e00c861011807a008041000503c2582c03800e80001c40c0e0f01080783d0b00a8141c50381c061044901140f15903244038201d009100941c8065800894a428403465000241010180411070340e1300b131103507280c0d81380090f0a80b2038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 300567068 1250 300565818 300565847
    0x3120a021c0905031614060408030901030c0219060e0f0604050a031b0606030308151014091302070c03050d080411210d020c120a050a140106090f0219 66
    0x200d20001858951450001c48105a60500d1601541c980c07001c40e01d007203040100c00050616a0b0b009116505065020780c0b14113070112540c0e440d190070078001640302e0084011407418107494800400d00103000b03021050b188942000b10542001c2c036824540054500a2042803841c05000e800588103100400c1c002d1040340c2001c014030501400d0b6404940d012562041840c0d1060300d6211140043c945000b040c00550080d510f802103400d18100b401a010718900e07105219540848501e21100d41140300100f130386401001ca10703121055000823400311b005442c16150740310700c0060541c00704280f403040001a01e02a03022281c03081204542a9103854040d0b0b40501000a100c0c6c448426190450741c1a500800d040a900c0701121070302680d5103401e104031424400350b084201ba51810342449040010300d9804400104200380407605d5558542e203640802819140c0c040e1100360800e02d09401c124010f04469000b00b1901c0550903800000b90801000402a201080403981420f440f42c290b00700c5140303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 300568318 1250 300567068 300567073
    0x506030609101e03051605032e020c010615180902301501020304030803150102250302090f0f07030b30060c030c070f14160503120a02 59
    0x31a400d040000c0399600501030000d00d910b4410208408040091145120b07496602d059582e03801c52030094104029290045141444c00307000700301c2650b000403c51105403c40c0c0d06910001090071101002c0000c1c5103904401500005034481e0688055211000719000c42d8012840c49080e04021aa580801000c8031b9588100d04820700108440c0d9001303010500c150202c42b01c6403e60000c0c480c0c0c2a014010074208509044810010316031030200c2549801c010034030143d46440d085a8a0369868040509501000003404104c1038499000300000303d4504805c0340004140d891a035418a16416103000490103031403c84042000703540c40400320b9015240030f070b54013006903882c00c10850040c080c6d2030900d5030200c012040f100031040a48064900039000b1002e0040400b100c0710901c1c600b0102800035200c03d0410004c0016688244040c1c0318000d9200f4200d5030700340304600b44407007688011401c105450046000d0803d0028440400038200c54065050703800c5c0302440d0781d01281500a005a07000940c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 300569568 1250 300568318 300568321
    0x803040608060d14010c02060109020f07060e030c06010b13140d11011b0803091516050a170108010b04060609060504060804150c12061202060904021308031602120601050603 76
    0x54090440070750300c658050441003c00f1481d84484100440b1880390b03800e265500c1c2600480b150b4188200350242c5042041589040c0c441c14020045c1d11512802409aa985001a00aa61003841156981c0c09400d046840d203584805c0a80f0340c552001c4e628100d0055034450014a55941d82c070800c0041500418808005000d516000c8179100c82c0c0c0d945504020303910803440315030003070103800c03a0701a030040b007580351a440c200d1011783c6801c918200c000039101007501040400c40d141c1440c400c01600700d2801c5a00d8205242c3c003900c140111022400c420300411001080a103c158040d40b1090011241804040d0b62110251107034006030180400103401080117100d21400f800d1415009845041410801e07030788800040c0071941070000300c80020701c16451307092a0000c1d50050380d018140d20b0304682880801c941c001002d134412001280e000d1a00802e0020746001c030152048000e01c03170b203420b40e0760315071400311903990008a10404900c201c0c0360500e003107000d90340010054181e810140032546035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 300570818 1250 300569568 300569579
    0x909160f0813060c020c030706021612020a03170f030a0e160b090f15033d17011d070f0b180609030304030609030e0901150806040e0f12190504080304 66
    0xc3d0162020381130a5114845665500b514204010341c01800316074040e0011b194440d01c09121102140d1040403220940800c80004da03031820303103640c100e0b540800c42c500c48004101c49010240a40d4280c014650804403c2082d50710b0300b03800c020350609014058840c0c016407c80030701002d01c894024840b031080c0900030204141010b002c04100c0703e100828464000c084400755034481d90080b14500c8450744400030200c0d00c000c4501c1c0b170101141240707042204240c11840c1c640340c410014454010082c40505a100300ca610070342c1710030704403030540e079440e448240000d05039980e07a107032403203164480244040c000400184440640d40703110602c260740a110a5408100044e80e00300c031054035810b0008200c000000b03a80c600c10036513541e00c07903141e025801e0006070410241100590100d5103020b1046c149054a55003c00e0f200e074072807412100083d044104070091441c118444001c07006074820004060124004c000141c004401484904e00402c110203c003150f140c0190710a0710060741c4180000d004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 300572068 1250 300570818 300570821
    0x3012402010e0c0f1212190203070b0c0a030603120e090c0702032508030d060504060609030201020c131b03020304150606020613050c04020d020d0515060409110909160f081306 77
    0x494100400708240d14085c01034150804486440b2818106030001300f20160f10744180742001e0900150000c0c50504e5095210341c40701d1800105200318024000412080650080e80b0000103581c0209103805242c2c600800900803042140080e84294030706400110000c1c2800215140030b0307809405000818250394542a03006656001000c0c10040e4084c007041d0b1440810140482c1602c0160200d4510301d00011700c81282d1042d0030180410140c4801400540d80010305040ca800081d681c2a42c6558950b47c88002001d907146003120240400c135100c0348503035041c1c0141d0f0240c0e001c1c4041c0d46245884800510850300306e4440e04025822103c0091500401d03640310000541c0190240c4840c401000c0005040343e1041807110207180d4007081d01c01464010344901503024407210002c1c000c42c4500e800282040c06103115400c846600c1e040c42c3d40b00340c5e6445040e54101c060142c008041e60800400001c107601507003172404000360007990a100c800344180d01d183d0080f600c0480c4040411465250341c1c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 300573318 1250 300572068 300572089
    0x9010807061d0306070906120203070f05030a09330e070302101101050f1f06090902070f06050f0f15060304030c02041407053f1b03012402010e0c 64
    0x144010201041c1c5186483c2481860320880b1a640d545010506001c406840100214612a4030070310600c10080c04030b0b04151080010a518145151a40d44032103900b0003400c2e01e60401070514501100c03c072224840806110517000c0500345030300c051420034055004036000050300b40c0d0168085081040541801c000007040c0704030f0791501c50f11750281c100704c0b1825114203031000d04480c01d0680030080c40503c56003441c1d6403043d110340400241840c1400050050340940501050b00d03500081e00d000308150501251300455100c0c4040c080340c545074800da0104a0101c03584031014800400064241e1512507540341d00d0a8001c0c42e450450310765440880c0d201542d0030702240c000d1380d11004040480c0400001512905683e942c607075030b40e00d07040c0c040d40d100c040c03001080303400c334855014100451184a040001d44d501e51891031030540d903008036200c2600d01c2d43c500c1007440b5030004004120680b019400d4034984190b02c52102c0c054000f160304a0880d21070710b03160781c041c2c2c002402e26803180c90f0816002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 300574568 1250 300573318 300573347
    0x605061201051c120e011205090607111e0d0e0114030406090609050102160501060503070f1707050a06030606031118120c04021b070f050d030806031009051b0901080706 74
    0x3e000346401d80d940d1804140d140541d003008100130500b5a0386940c0d0004581c2c4004084030028010f40c00c01c0c403851a5202e84c01b802c5001400705000e049006040b0070468510507052001c00041000707040b540306901c400b083c608420000d124a5070305042540104240c658164184071142c1c03465a550320740b18002c102145084a41544410587c1d000c40e4003400034000361489600b25207010017046c50001d00b100c1d1184e11079030080e004510101b2001004130250310444810b400000c240320b690306071142c10244150481c3d41d0000f104440800e80980c142d2004c416220591030030800e03030041080724200f5000302c035040c82c80c90341850300c0d4040504000c020049407000020440d40004900700004040c0e0f00103510b0b40e01d10140b40001002408800c00c00c03040100384104103e65450300303180114290070301e0b000300941406580f00c046a12900c04001c4c2d1303000c0240f88001040441c425141c656140d1100100004060300c1105140e061071419044540c100d40c80e4000900c08a07141c49003d499490100c00c18 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 300575818 1250 300574568 300574609
    0x913120804050c0a06031d010608120d090c06050c0d02010506150c070302060f1809251107030b1806010b190201020d0e060405060f07021504080d0e010e01060506120105 74
    0x690340f5841d02c81252018004640b80401c40c0c2e20021031141c115041d086031750300241e0400741c04000014011071509409203a8a500325031364400350883c0d0002d858660402412480c03255000503010743e00034054003c82072040c0a0b9861200c07002000c038240d440a5881c070740c2c0505000541d06000360114010060410254140c44802d503490b0005980d035044094030030220783c40050043d0785140e4900035601041c03002c8440310802e00308004103208440c203d100c4c00d0709010410100200e054001c50b2080e0840c00100c0c110f90300d080d180d00d40f0300080c3e00f00f56000c48445403840c2072042107060200d46541a20403444d166401c04074042a129004944d0070545d0055540c20000000111143e00500082c41d41c400005c101500345440c14030b26101c1c00a1a001501c03003024184810310354007140050031022201d81c000069100c81c1859403903881244139201c086440e24031220300061042d0070420054450b14020000d296441084c00300740c0c800d030380c4802c4030034100303900511030303460074428610203203207030969 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 300577068 1250 300575818 300575833
    0x11e090506090111010e010606030c020a0b0105010c0206130801020d0f090302100f020909010305030a09050d11130e150105030c0f030307140708070306090209180a02040c050c0318091312080405 85
    0x207134542150a00b10f400300a594540106000190b01400740000320a240c0c03000f000f502401d07480381000c142040c002c3c1c50401558890900540d6600000c0e03a400140115440c0041655030255078001e6002070a00b5400a08020322070442c51450312819070010340580291044601705000c0400030300103081010041c42d8244513090480c3ca4504403640070f548510019607480301030390009401a00c10ba40218032074183d1300a00c0c1b00060b43c00b99000c4c004642a5110401000300725074140103810910510542c2d44155900c51103400301c0a01518100e0b80c080e01910709008038201400b41d5110500d81c0d040d0154020448040001d188281003280c91600d0f10a41d00c2c42519080c0040c00c00704194403e40704142c6030f80d200c00035890410310710b50b08500d010001c031003400310219040f81c41d41d01402c0041c0c4a540d65140c040c00150080044a070204a41000d0365580c040300c0700c0034000305c42d004130001d0041505000281100900058000340241c00444c200c40c040d41038030007103901e401c1c010000c039058001c201 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 300578318 1250 300577068 300577097
    0x30306090a320f010503030708070c3201020d140912030403150b011b080307090b0409060f0b090d1202030c060a050a051608060423010602010605011e0905060901 71
    0xc2150041c5004004169203200121400051002c006440140010900c03030041000d50b0340007003190784582d400200d0a86030b05241c2002188a8115806000301d043d480096000310006c044459591030b00d0f505410701d401000e040126a220809c090345404640e0000d41d111107d12410080c0440e91002000613441170002101c20342940c006a000f00d0742908003059200000c1a82d0155121303030a400e10b0030308050300c1c1a600e003070320380c803e500c00c00f80a0b150000007061066106c1e100c030001400c8007000c8a80e03240d540300720b01d00040003140b10b42101a018140045101c0d0555422221138441c010511100010652620700302c203000c140c1c90906611040041c400c03000001d1041742e10a40c02c0d07a4002500703160910100d41a14801040162405907084180c0e119a4000b0714440d000300d016200001da500614242e0100d1003925513040148950358400000c120380e054201d80c081c0c90080ea40c2418015600e806540c0e24000241d00e28007142c210300040c01241810000f400342d0180514050a84c41940d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 300579568 1250 300578318 300578351
    0x14030a06110306090108060402030307080a031517010b032407050d090c090605090601020d081b1201090b0901030809010f05070f0614071106150102010b0901092309030306090a 77
    0x2100041c0492004010001c1d140b4090310072500520f400c001424803864a540041e880e44a5a14002c0000c0004941011914401e81c8140b03403000c0c0842c140c1140701e40b43c4903107040c6c001064425014543c01c1804126407070030302041e0396580075802003019089984420045041c80b50051a01c400c1200900c00807410701094001c4041c100c0c01007401ca49114204041001660480d8200e1405604a1400d108c9540d0740044c0002e484001d51800d4181a00c0c0c035801121120030080380088045008100303603004062005d401c0c2d0495902d000e08000d00c488100612110440c01d11003e40795031011300007401c580d401a041031003001c485103009450b00030540d48407070307440c800203100340c1d9410350300c07940740304c5100c110a5415000383e101c0c2416031140e0840540300c0e9641800500c0018440070206074580c169000b50041000d261005106070700e00c0da15012540002c10014910600441145011200c0601003151040c000c903075500281d0b165a0303079401070061041001d410114265504e56031091400c4d0403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 300580818 1250 300579568 300579581
    0x4020c0c0607060f05150f0d02031908180a0308180a05120102031b03090307060b0a0302040e0f0115030b0708250c0b0609090703020d031418040f050405030414030a06 73
    0x7180f0011300384080104510444000420f25241601c1c10b4882ea620780d0799070802a884002d084400a5441629101103070420201200c1d540c0800c000000c5a000c008070b0201814400d00ca201020110b0241c0104002c0706038494813019000400800c41800215000a6400a5080064800c03042c4c40d07914000708400e0b6a04d0780071801c06940c0807083c41415802520718002801340f0305180760860034400b8209459128031140108420350390b070b0265400c0d840703805450000350340040080003404481c88406444100400d41030b0040e52078508086121a0305801006c142d940006550083e640c601c402038940140180c070041c1c46040c5c0485000c103940740040c0001812040741c0e0b0340d8101c0001840c05611542010b0032051081e459941000b1146d1000202a0116901150030200049940c103060700d00311404a0401207249000450100e211115205520100c6017910100250a1a07500e44004c4031000d6038018030701e0300300b048100f280d80c000304801c906201c0024240c4882c0c4d402c2d035940c2d01c101c0b07a1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 300582068 1250 300580818 300580823
    0x901030f170a12050604050103031b020d1406010807170a08030a0b0307030c050414010b07062307021e06070e0f1503100e0f040f020103020a0e0904050601031712010504020c0c0607 79
    0x140400c0901088000303004d500c2e00420706075800d00c9554119078014110701c0b04042429a0066001684000d40d0f03a01d449201c011a0000c6040c0e410146c031800b0780351180c04c01d009482f4584181c0c5000140b01700c200c00c44135400011070f00640006000f5a48040c0c240d8005000701c44a40d449151100d821741d4107018045c010751160350318461080ca0b0000b440151070f00c1d0301e0802036101d80b0800421801903180b0031100c1d1154010800982c010f00c9420b01045505080c90401c80c451503c410000c496230006200316454a1090340048460800b0b00900d58501d800c036030000000352140008042401c14000340c07428070200401212504083c0412001640c1045520030840c0e00b03001e804128031613140030a6504261500010f034054505038503840400400b00c04002d04140e80064001202e5225041014440c000248444080c5c01c040c140503980742d03000e001c2994080c82d80e45480076400c0c8004102d9400c4002d002c80655640c1c601420030000b034100705200039031805400c03500541962801e00905282e0b1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 300583318 1250 300582068 300582077
    0xc0303110310030b132d08041d1305030a181805060f030a080301030803040f0b040605090c010e0f06031e01060807030f0b0607020d0c0801020c0d08060a050901030f170a 74
    0x1071460500f0441c0b1030026000e8942d6207500c24608001c00da0203526011044e450315881003211502000c4a40c00c03110030207003c0d02d501004100410815152600e02003c0da0270b80712190620340303444915030340380c2401c0b440061113139004000d103112460143c4000300d182815501054805a40c1d45100c044c48420480541c0c246540c0e4030812859161032515540c1c0e0140642c010300c640e5142d990b174901a44410700020300205008000601041610100c09a04603800203050360380707041c04c2c0350110190200f6215143e4078003a0300c51400f01c951050b00c644609040083c200107068a0503424419550710192003c18681081c45005203001300341900e071802840c06035a2504a40352800c001412110101c90324400d050820100f0340700781e0341e11000c4c0d96001350103d40e014003451f0340d841c1c1000c41c01d40c20f030f10510f00e0394004104240c4943d00030a004074103a0310b60302d80e00d03010360381d030000c01100c103645000d029403142d108401400451843c48941c3c079201d10a20312140381c03d011408032043c1d81c105500b0940040d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 300584568 1250 300583318 300583351
    0x151c030201061212080901021315020c1503060112023907060801090e030702030f01020405040e030c100e2e0e010e070b130b0f040806070215070c03031103 68
    0x25609114030402030040b0704601078403401643c0c1d100a03607420301c140502008140804036501410079411241c001d0710705030031070b10402d40c0c032048008803d1183d0003039000b600a0b00c500d54018282043c0100c1c2070b020045140e131a50341c40c4401950301c460a0006500184e41c00e116902650855202d40c680181201c40c030011303910203500c001c11440c010140c405078590084402000f0141d0001001d5042d91003104000c54002001c0034034619500600c007001c0d51600c50440d14080502c0c1c10b41c001e1082c0c0703800750f07401d111180000e10016503d2050300071031802c0e40d100001400c0c400003194000d0108000300c806440301000180b000150004425580101c2c8200c2011b200303020709941e10400441c407030034800a000c182c03c10701d850794441c0428450701c1402e1100040f4403030810100307145c20380a003030720f490420384030483c3c030300e00180e036400074051010a81b241c540451200c40c00041c066410341c0b841c105404203541c80b02ca00b20b620221200c070460615465803525807409800d900514450014099583d03c40b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 300585818 1250 300584568 300584573
    0x7080f0405090c07031b0206070b07210c020303040b040804051503061e030a0f03180b0c0c180c2109160e0705042303030721050918151c 60
    0x2c0c076405440148080010000100001d030420009184070080030b06620181c151070020440724441c141c00141200d044078100b0003001e42040c5002d19081c0a1140d00c2c0711040b450582e80201d5a440c004c050140c0d000703000140010742c204816a600c107219080460420799240042002c8011038851f80f1084103010041111a0409020716640b800d00c0781010f5180e45c0c1c01d41b0102e9284ca000038005811444403041c0130051601441c4c0c0c0c030221250b400d00c1180201c2e680d07144854550401003200130507001e02c41480003240380c00e101200100e0500d040d4240c50b0307150500d04000075808004c810428000304061804c4648040701b1580c404d44690001d0201a220403080c41159030743da41082c4c3c2d40050743c005100105502c001601c096600c0d10280d181070310f4540594442607100c0c090196418400080c44d40200600e50300d4050001000000420070420070000545d024080c1101040c1c0040c01c03191030191444940c003199400800c1d442960101140396008a80a15415007114800c0c20142c07a42404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 300587068 1250 300585818 300585829
    0xf16051615090b0a050c010e0610081203100b0c07050a1818170904060e040318080c011d0103090203010f15061103030a05041406070804060507050a021005070507080f0405 75
    0x800c07a0755151407103015003000e1504546003d1021004108000403d051501c000c007540565000d80e03006045621074541640c06200740c0da86405103030345c24001d2080d004101641d02058a004000c5405920302c92070600013040c400341c10814199045100721040050039443e401c8040001d026000c038244000d1003030b40708490036070729080300c0390f200d5180c032001080200b1081400440c0e480305d40e0031100c1d80d83d09070b54002006091140c010b0400c0c0340c1c43e003003403208068010f4200c00b50a4141d00c40c0078003040c0d885880a0f11900203801031804a04ea02141141c15940b031907201203c400305040c001082202a000f1a08403040007191201903079460004c00c84103500908024003e00ca50b181c0bc02001543c4241c407034176030101402c40307080c19840d50f000c1400c00411801c1080c2141c400c00807150a0310384040000e0240200341c8003618030701d1614011035402d40c860710403070303c012540d03800a00c000710302d4180c2c00000702030081840c82004020b01c004000502c100c401020705905030f80030540c840e0b090204002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 300588318 1250 300587068 300587099
    0xc02160902190c170315030105180c090405060613091202011d070501092102100804110d0b04020108040c05131d0c09040615030611120108030406050f160516 69
    0x2000d120580308640d0005204c070b0190200300c2c403080401503c176242c1400002c0000c010020b000d40c10b500302000c0081c5144c1c281d02440800c5040c10886229486c00014400800704c1501c1c090641d82100001400f07034202206103401c1070120105c006401045501c0b5016a011010107110041c0d45038044a030b8403200c858040d503840c40c80d6401400b00c10307150000103000741036a4030a10b1500c0d819501c242165241e0300c0710400030340d6005006900411903940000740030000844040300d5240f10800e0604031424801144000594849c4a0348510f0311660010b455064009200703ca0b03200d40d51002117007039214160191700802d040f00000c1002000c0107002da02c0c00840150451240d031000441a4a640e10b00c42e550350407a802c42400030358001107019500318190942c1000e083d1508203c0340c01c540c0c001c0a0020007c4004a82038407009980303805c5103545034481c030b00c19040080e8050289040c44035204000707011218410a014889035002e550f0103052045401d84181c400740485d50400154044500c0903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 300589568 1250 300588318 300588367
    0x1915060608100b0301180b0a0f2d06090b13050301061701050115092309040b06040e06010e06120a0c15020d03060b0f090303071a0601140910030c02160902 68
    0xf14150340c1009400b19241885003074820399185c40e00c030540d0141d01d0304400c040151a000681c682c4150315400030080048410240080001500021880c01030b090000403081d143c843d80c0d43c10511385412900705003900132107040d44104000030130000c0c013030b50700b44a000c00070803c10411030b46116071260f07102c1c21280140c1c800c6182080e01f044180015510000c010b082d56008120500301ea140081780000c0703a00c6003002c060b08005010140024070100c0483c040c4121012102800708001482c13817562644000e1044c240041c1040021032510b10700702c2c40400b80d221502003121300d100d0198440000307071001a413150800c00c07100c2030303d8500c0c40d40c1848958000640e60400b442600d240c5103500c08184207000e010030b02902c01180720005644c1c181b0071640784a8004a000340030300e0803602000403186e801e454842c041016090910034906950007900d85144000741000084140706409902800c1d8031885c40f02123010b0001000845681d00b54000081e2400c0100182c6030018503809141c1c40c50369802c0e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 300590818 1250 300589568 300589589
    0xe0106050a060f140a08012303070302090901090f0605041b1208181f030f0c080f04032c04050105010e031c1827050603191506060810 59
    0x28000c68450500340c808071510362815a10702d41c0b0000b021180d0340d98162268180000004054031500c0e844040c00d8140d40e0425010841c442c9140900d4a040400141c1580c1580003501c04001500d01030f8005a800030105e0004640d080d165a41d60802102c0a1000c0b0360075552282448240019603180361200c0b031040400101950415030240d008021006008100c024000f404000c2a090843c20402610340502002601641d90341c4007414a181c1e080040d000a1400100010000041c041d2002d110710075100c0c5000c0d612809800150761000600c01e4042c451203000c94680d11069407110803035500311190030403006039a48100000d03602d041e84018100800a6040415170398041032604060754400c00c2c5002d0030010480c1541c901e034020b43d015040550003c800104150303154018104080c0c10314802c10181c1d840200f42042705c0d4142c40311601503110114001c6c61108581c02698180e01481144450900f071103041820f842079a04050300060400061141c81880c410039400503100c0c5040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 300592068 1250 300590818 300590831
    0x140d0c1a0712050604200a080903030c0417010b09010b0d050705030103121d1201061707060512040f0609151407050a0e0105091e1207030503040303120b0a0f090e01 72
    0x40c000c102c81074007141200e0aaa03100003007200d82c1d84651000034001c00030314000040750030b1281608001e40103450208045404400041d01030036001c0200e9204183c4035214900381400c0c02d82003c4800c2e2a078103410455035844218208598030f04451038020151100500d80da68440d1002000b50761000d04074105200d803d10040c0001091100003c1c80075001d072070180085a6240d6a070320802d01e21000311a0458171261094a0484040d0000000c0da9940031650b04402080200a96181300520607030300050320a02c0415000d00520082e02d80150141c40c220a10807520340700e0700112024042c1c101c480139042c0300b00400c51360007800340140c15501e8039410304d120300e01400e02424034030455141c0e50400071007119105003a030040c0d0543e0000f81d03001d0702404c2c000e0030301c50300c1000113500f000071648241c4200e04c00d20b40c01c000c0060301200b40c3e0b80c008091420a2f14542c0e094400018508000a00584a0781502c44580740c191000300101072504040c00f07018035004081e811140ea000e200c0206905000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 300593318 1250 300592068 300592081
    0x807051f0801060c11220612050607080424090b010603020a080117030408031611030a080a0f0318030e042909060303120112051c020d0309140d0c1a 65
    0xc101d604585007400c014868001c58500028411401c00700e0340d51010500c410384034450340450507072070f003403240580800100e6194803c00e400b210748020014070b0f035030202001034001d510680c00030b030b0070a203d0306410a00417030941e051000042c08800101101e6658a001014000000356540c01000303d4281107180422003c001444504c05004810103440c8800202c0035204080040b01d000b40302e10000e503900c5006400c009020005910400e540c1000501300100e9246004202d0580315503118416134604079807054107032612072880f180007052507581c49031000d2400320f4404d070242a034071035940c4900c50002c80b01000100d80980c500d4011081c0d540c20440240920f04400e00760f0b80c5d508540b051100d96619000034554421494800c03003410743c1c040001003044070b890f641c1c3c3d101403280d01074620150000c0001505040074495000050b800b50401b070305414001c2d0300c900101801141294013440300d80c1c4215240544010700310700021381030400c800901414068007503144030340700c01d81c0e00c4d80c1c1007a1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 300594568 1250 300593318 300593327
    0x4030203031b0307200c04140103050c0a12030f021203070c1a0705220f03050a170711040507020c061308010e0a020d1b0503100506030f01060501230408070807051f 72
    0x6410116000170750300c40450002078100f080e0280014020000d0100c00d0546964005628080c03104994034441c91240c2880c9180500340c0350242c4a01c061712a968081a4070111100500001020154041d0108558452201c3c50040d40f140c2ca00b9220f00c00b28000d03500d01022056803061a0141c0410031100344045e0b141d0200485198842e80b004013805100b83e20302c580c0c48111594400400480840800803c1181c003046440c401802000d48008140c00600344159510480c03000500ca45954401c1440311b10309540034641020481c0b0480b01c49042007004281c00341d10110310045150340340c440c2045941c07402d005554605e00c0900180013031521a43c0456030714008000020699030320000310110110030310449100620004048a0743e03007a044407501d004040940340c0e40e020307000c1d40c01a05e05001050203070204503170060b5100402d01d5880700a200c41c000d42c0c41d04040d6440030070840003802c0741e0200442c0d005050640060868185090200144507400c4515007401000b065403c03050b69401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 300595818 1250 300594568 300594587
    0x70509010f090e160201140a090c060512181c050c21070b06060d0c0c020a120b010b09040e03030a050f010e010b0a05030c04030503070609110a0e0604020a020304080604030203031b0307 81
    0x1d14040c1084131103000c009a024210b0b0101008042c141c0c14200702d100c202d1900304c90f26150040d180161b0850711180229064800d0b030517142d00021a90f07000c550a0028030201240d8002074005032544507200c0c0440543c84a02c010110000030404180300c1740c0003600303110b142e8010710380d50308849100c0848580845180264900902101183e000240315501c1d140c00311004601c032a80100145846000080c01c00d1480801c164042d001d202c0c008610208806100d4801c550004148012603192020090550344040203480d00070b43c13241a401280700040000d18000d40005001042d989010040c2e0b0180a0f0140c0c0b05002140b10400104a034648a01c00c0303503010700e900c1c80c0003507aa5032200c1d10043d2078410340e030004181d4440050303458140080c41e0f0046124900c202007081f40013092008028155030785004907004180754001141d00c07171801ea07004280c070300010f005a90610742d89a8819080c000300706c0d400e03400741e00000b08124007040308a40400d00da12010360340a0940c00c1516000345040e15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 300597068 1250 300595818 300595831
    0x510120302151503060103050a030f080402010215090c15040801180209130c0509010306051609050f010516020301020a081f060e1c062f0405032d0303070509010f090e 73
    0x2403000104409040c9203074075003c407500c050100d61095950745415030f561a51210282c0014414a22046c0000c1c0324005a40c0a0307a0140e00405a4003100006080991000791070030f5054404c2c0814a031058860511007541c50a2880305151254a464055400d440c25031141d44c04007441401e091005990349040380fa0028803403140c03d01441042e140410880125800072030b4070480b020000402c004d09034000a2203120030190303444212084d0041500c00864600449a0040314a0104003955115030003800c0004190241400084010b402190899001e9070320140000c0318482040000415030007034468404d0f4521105001a14100c0d004060b100030070720283c807822071308242d13003914049280c040d5182d680000c8208088100f61001c040040c0042250002c46500c0e40d0300d03070605014000a030740071a00c01038050031303001f507110702d50018800c140125811422000302ca440a404000c0014501c21300c1d45848950b03550b8401000500480c4000f9880310420840c40010b01082290045e900e8020a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 300598318 1250 300597068 300597103
    0x7061b050f0a020c0306180c1002030d11070609030f02060711060118021b070512010608100b01110102031315050610050a020f1f11030f01030f0c0e0a0510120302 71
    0x140340040313040034a0400e070fa55140c401c134414000c401c1d501342c803240364400c00341c0110780840c00013000b845240c04201d9141b0015802c10722501d4035404541d040b40e0030407080d504000b03180c01c0451703540404860298406030006228601c0130344507290104642c50704100d8600b0f088555aa000210780e50b540c005014240b2107082d809880d24070307022950191140ca86040201d600d10207108480030355100c0c140c2c402d803440350b084e080d15038826100603c01e040c01d4480362000342035540e00072890a800b0f403403446082410070502c0303003450006140030720185001e02890314004e400440703503080c5050ba03003001644d010f0107245400180405030341d84c4900e07081c414055040c80e9850f010145004d17814141c04841c901c03020300a02e51020130031000018000da0a14404504002c020078100d80c11200e400700b19150b1403081c48070f600510115040c0c895050840f1310030549030131099150350180ca00042c003520084102034403441400340c40c264403c0c0081c06000c031440c60258403030460314002d649603a5140e0411050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 300599568 1250 300598318 300598327
    0x10e1015050906160209011401050d0905030702090108010f0f0c0c020d06110406030203010810060501021f0f14060f1c06020304061805061f0b07021009081207061b050f 74
    0x5034012802d450300d10000504081e10740d849811582640260716008900c105650000441c4046949410a012040607568a070410041c0c5210100a014200099a50f0b11042c031230140180e0700c03501494080c01d0b5000000c10003154440710300050326000a44108400e0a120710640d8050b4844040c54182c0d80407182070003107038072030f062000c02040c40314000f0001400004001c2400c03074043d0000c1d41211a081d0840310075590401004c01220030b6805090700503004490706a40e504c8003401d8040810790b021000090380c0b2890b01d00d00d822907600498010b5184001c00420010786030290382501c000034151684c0428001203e8a07800300c030b1010400038032559020000c1018004141c0c00b6408159400c0f0640a244145040c4141e0361501140c00d00942480a00c58480700da40f0003600401f25180303003140b00c1c200710043e400c0002c485400825001001629940040d1000003040780c1005084000711066890016003002400d5915080c080d20b4031150f10110002100d82c007408540011032100c2440303032078 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 300600818 1250 300599568 300599609
    0x40e0f0601230a0e060f090d060b0d06091103060709170705030106060c020a09022b0b1f030c0207050604050103332408180109050604060c08010e10 65
    0x8010203620042e9510141d020580031010490040403000fa882e00c45405150a000802100388900c11030300d0040d0300e0600c104860342c10010701c41c0740038601c610f034007041e00d050690129040403103c0200341d40382922505076038207021203011148049102a0082e00301031038405d00140452409110b201800d03001c2e02c20059903443c050002030044d04008000780300381c954030040103210f1100c06074203a10500300c41000081094140c8201e400365121101130103444031014448142d012101c03189411200d482c2d60b0314031600e82c0c800c240b80403580c208000364200c2c000782881c02807c580c40340c108401503501c851000d1001c0d6907510b080c1c608454007442d0108400e0b9003610040d900b4400c40a80600100b54101c0d03040002c482c80c04410255200084906043c80412141a0300c1111480d900310100300004081010540a20704482441821000100e40032426542d414500003040b14240d031544d94400d901c808203036104c8005070041c04046101246410301d0101c1000c3c1400038421840603154503000c9001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 300602068 1250 300600818 300600827
    0x120504030609080a09081b0d020d150c1d1c06090c0e070311040312080c0f04080309030f0c01050f0a020c0d031206050103020f0f030604060302100908060c040e0f0601 73
    0x2039a4099001e000080302c1d4a442d00c15034104e00301100200320701c0100030822400000316191001d100d21716503044000c54809100c402c070183d25003683c1004405001a002c540e43c0c807514003014020180c00a1034502d0007800415985c1e5040d42820b182d25000e5242000d07541d00c98001c03801304001c0384001c031004031500d4440c00400307450800514040d0756140003e82e009982c0e10302ca100710a1502d06010200001039070003154462800024180d034040b9900e070752021711502500c0e921900e84001e9501d0700c0d200c0d404000c81c035080356122500a03400000c08a03468141440500f0300c1820365030040030201030300c1002030018011030402d580c030102c002c40d1002c1420301c01c0020015081c0c02400203651440306082c0200000900c1d04580070841c24942d00050a512a03c2290901c1900341146410002c807246001070640c03000d0000c03075016072030f5100070000d030392a0910b40d19a02c6158a400d511075180030754440c10041c0c01404410031450500c8204420424800d01a901c00341d50400002d480d6200001030341e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 300603318 1250 300602068 300602077
    0x1512070912031115040b07020f01091205130e091b0a060903080c0102090a0e2403060c1c0507080103050d0207150503060315040b0901060b090d0f02011709012304020d1205 75
    0x2d40d0f40302c4eaa082c4414407401e220310394014621a400e0303820444900680361300303840c0003600003000d44034045404191903110b00060590340000807500e4004917034514001d07095001c10f40e0034800725044480a003c4207904da0034054078402080d42c80003201440d10f88c024080d4505484007510a01e0b000510000740d131404c0d4100c80001000074100700ca403903243c00d40e5000086040701d407104441c08068150032070003e4803500100c41d610040c01001709688050a01e00103800c4108480c00e100250112280c0f0700c2c44da8010350780300e0051130b41c0b40021503245090181c17034840c0d81c401800075034128070320034025010045000c0c2800a41c60900503600e440e26408640360540e4101c131440d04054510500c410491943c42060051800340b000303020940d2201004249441840d2846034403400414800002450b00c03c00404a240141020300840701801000740301c40200f255100d4071650746481507054503560b00208010304466102c40915468590b000c40c00c01e03006510701805400c5280c54a0807107504c18022113 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 300604568 1250 300603318 300603343
    0x60118090c0519050717090d05100207021507080d0504080f0307020a0c080c013c050901080a0c082403030706051017060115030b15120709120311 64
    0x8001080441800418541000d041107807508000f48444103080e103c0c2c0300b622a1690020b040e4066800c04103c0c0c2500703640440100c540015410342c4c00004948148002107000714110000342e030300e859a1040020441c44402804d00c084818480784002c0b070103e0094841d4010000c1c4e000a141c2c035141480c10aa00503aa0380c00d10702030300001005015a03001c60940d00700307442281c00000c0f1944402c4040d84800703958042c24001034601a8019152506030b100201c00218640c1e00b20303083d0b801068003410388000d155048003040e0002051012540d0050155078001c0f40c4410810a006d2428030080045a01030225001041001880c0c1c2e061502e070032040b14010002000c4a5842026103442409071200301c810721441000d1483c00a1940b20704201b914041c0614005000340d40c0c02c140781042c4101d41d0b26a108205036035070030800415206c0d55615501018502d602076107921221241140714a0010100010440e081c00208940505580c0300d00c0b540ba41400d0508802d00405c4d00e162810345040c0b0f05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 300605818 1250 300604568 300604571
    0x302030913140f19051003050706050417031c0b03071e030204050a060e0c1e12090f0d0207270609050103020108011e06081302090109050109200306011809 68
    0x142000041c03258441a20600101102c2840b41d6601c00e984540d600200c0e00c1e00855490303d840034120445681c00705500c550742001c01451261251185d9160105523002000800c900250a100c980b5440701040c440900c400d000b146010690040113410780d6441ca011560643c5032804041c103a9401c0c00080c001d0039201076a42240001109125008800b51005a000f2481d100109110042d179000d41c800342d0341040444241a15010345150095100c12464844008054111105200100014490411034083c1400c00e420282c00032401d21135221000903560b070101d520700210070340204626044418927284418110500a183c08804503024000500989400c101190000440d0b0040d81030b00e001380c0e2030b1b1946a07224030700c0b5501e02c3c00c500179440e2170001c0000c0070030039079224040d0660320951003440241700e08007030380c0861156802a00b200044076194001400000554490f902c43c511041c440150341030f5804810a521b8800a0400c904001c80c4001d4100d4101940113040c00a0901040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 300607068 1250 300605818 300605839
    0x80c0307140115050303030405070509090a0b0403021b0f0d02040c110a05150c040f09020a030b090411150a080c0d06050607030804030e04020723190b06090702030703080c030403020309 81
    0x75140242181e0880045441c282c83c4042410f040020540c4d1040d94420010480d4608001c100124080700038084081441000b00344000200001d25440c0500c0c420740080c041250a00e07425082e0342c1c481841103000e40c0c92210480b000340d40d64101e903002140c068400003540301c2003540844a0022049a9920611450700322000f00100095220b18103030486145070907545410103065420300c01d80c80340004819a0000c180180c58055000300b00c28051810002164030011000c104172800480e0169001358010b8800701e03003814409950103484500c5000c5030310b0030032481c41c0909121000350150109032400b08468480c520654840341c0600300090640d40c81d0300700c80ca001803090204075812000180d00c0b03004400340c0e042600a45204540c0003c5004410710740c6003c012a600b8120920039051280000f88000c07620007000302130265010340710b549454540002070007820720000d410542150300405c100c501103580031b41e085070814034040340c0c40d41d03d40f6641400c0b4914001d42c90001d1340101c6200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 300608318 1250 300607068 300607103
    0x3050c090a060509030d051204031103041518080105011d0915091015050a030204050403090308040b0703033603090306020f0417010b03060613110705010204210f080c0307 75
    0xc3c050a441c00044044521401202070700711000d029100e0b40d00400507904010030700090148080101d04141c1c0022281041e9a90485070707036681c42000100045044035007450f4059030b44126200103407a0a400900803545081d030289028808450100169010400803d61111060200c24140046100072a41c1c07420500c07505501c4080c1d805102d9800746c503060000da07115101580c90411900000c10690b82146150207210240400510440c208401590b002c0000341c840e0000d08080c0c119588003640700d0886203006001c5030a103248059414624041008000c0c0946403c3c0300a03001001d8030354807030a410714060350220b4081e040200b00340c0c004230315002640c0101d4050012030780100c00c902440e01e44410b8481c200c8090341e01682e090f1b045517000402c603041026825080c000303421000540000c01c845411a1500018070495103650002420000c4e200c602061221000011081a1070701885945c0e0b08440f80030341e04000d2034911b001c90001d030100828070984c0c91b03007500003007010388042c001c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 300609568 1250 300608318 300608327
    0x8090c0906010f202d16060c050c090a02040f050d0b0a09080408100c030501060503090714012303010303021e03120415090b0609070302180405250f080604090206070303050c090a06 79
    0x340046428060303000c0d10301490f00c40024900c500d0001101c81200c6903047c040201d444130b4115409592a104034500304800c0d4860403002480b41c40340706401620790b810f0040740d1001d220300f940920300c14600740328400f0215281c440c172f0541006641c032000a280340285025180d03401940c2c010001c170700500d800c3e00d40401042c2c00c03070020412240d4042105a880f603070155010302045c3c400503100c2d40580000d0100344c07070444407188039202c1410414000b404441e520030155407101e8201041450220040041603010071040d141059003500401d03c80d0200700c00165240aa19400404012003201103400d00c034070740341040c6a042c07848a00384050702c09410034141d04007090b22400e024507801000120041d20034800e4460740a4030f1415030031206000700800c0003a02c0084d01c0c10644c0020300341244404442c440c55013070b641080e0307121401c081c4000c4201400120700205200c1c011400c0290240c016a02c2c4d00844544950500303000450392656494960b0601800d8025a00200815808200203800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 300610818 1250 300609568 300609613
    0x80f2d1504170a0f0c0201020c120a050606011b0609080d020f09150903030d0b0f031e0c1801090f091b0e0606090d0f030302071208090c0906010f20 65
    0x2c1d060002c0e100d905440251224820b5499800009464149101c640f45c4642c4880c85107030f0052040781c1c040d4100000241140542002c004d2107944015000001c1003c01e105050b840a02404d05a03034070411203200104d460700140004140303d584009050405c50050241d131001481030a046480b510b4040000f078a81d40100348042c07140c1c000c514007080b01c900000440b442200080d0245041164a80314030000c2c20795000c0340d03035200005038080303c1d081d10100040d030b00c20800111a60085904401c0d820304028114092600030310f83c10340b0302c0180030500d11034241120810070002402c5808080210020646554002d00420703a086002094803100d81d03240d02503a600c00403520f4980c960504104aa00c203c8038003640100000d4030301800710f0b00a00800100502905016290807520baa60400c10f0581684d034402086174442880440081081844d075082400d5079540c03964188038001a02070b000e5407601c4000c0000047e00c84d05241450707119040c40c040d080c2c048942c803003c2007158022805c01e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 300612068 1250 300610818 300610823
    0xb0903120a14090a1509080c030a0309020918070e07200c0a0b03130b0402010215130c12210521062d061308160302040501080f2d1504 59
    0x700702001c2020f400780841e0780c02820f0b51141e03003a01900c0b42c4001603070182849840544004005000000c1228402d1008240c00f0000d07550008a03000c0a10401c0020b80014008220411448410990400001400009807900350706155481d0743e0361403080b07030445c503040070704d11040c1803912070300b901408002050400d405046840c40c00d5a52510310b620404d000c200c50204050100000c80400304030b8010340c46410600610542c3e00040a82d41c501c02040c030141d91444100600f40c20b600d00317104d03040407118044c1c081c040415600e50070316280c03100702088000300c162040c00700b6203000e01002d0090003101e0010003001074a4007140c0840359071000024044405501a03100f9145810615034041c95031003031031040b001010000003c020a00c000d603008265a440240e072808400b0030001e208202041c680e03d200e10903091305500b10f20502c0240c0301e040e804001542d20409580c1440c100100f80c0448002d000c28415410996240d40c900d01b11011110860b158041c4488000c0101348061195109a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 300613318 1250 300612068 300612101
    0x80a0b070806220213120506070f0518040507110106060e0a12030804060f0f060b0a02010c050a23070606080607030b0d03050a05160204020c0a0b090c010203070b0903120a 75
    0x2590344041c0700d42460403d6400340c0c000d201ea402054201e0359030740074014110306904081401078844107902c1000c0c40626080c0c46070307880300017008500b580c080251f0b80c1c031100601e4980d043c510500c0150081201a61965200700d450720300082c80d0318810b50407411420321820003031201075554007000e040c039443d4602240c0202c4000744007040d040e0341019a00000c561580e07032207195039a940c41e20320003000804c40c4103c0711625400035911401e040e0003002c01070130000c20156500c1802950180c02c4800c0e041007102844010300034190401c0d04100444000450b404a00224007008804603400c0e224124004110f0b925014001c40c44040003e02d4034424a060780302000590200000c101006e1b011540040c00984100a0303000b000744500054010005100804003080704141d00040590704800052243d0364851002c4009100d2007040060b0400025006440c26a2401d00001c4d103030f21481134003422201910020031b03d100340800c200d603e0a19035a140503a02c3c2400d00c4948003800b0030005c40081803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 300614568 1250 300613318 300613321
    0x9092205061e0915071107030204020f041e05030c060a2703150608061b070f051609060b040b0a050c0109151103070906030b04090f0f020306090d0507060203040c080a0b0708 76
    0x40e440002d50341c002c0110000142011750b00c121003122100011030f05a9400c1c0204800040103031540e0001d0b01c2071580d0344100540350342c1084600800300350b48546006000804400800c1030382c8010401c4d8881181c1550b9166440f000c64005a03050403104900202d120b8131403860783c0241495a401c0390540e4490181e90003014400008001560342c1801100b0705c03900306001003000a54030304038a11411130a08452414900c0645840000d045164010b0388c4580080f05040220149100950042e05003104100901400d00700072400c1030240b80690728422400103003056034580500c0036070b0542941300d0000e00070800c03107140c07480b40000d42e1034600001c01d007132450500788240c1040c156807107132840d940c0d080451407410030120b0183c5403510201b0b820668603003244010441400080900b240103814001301c441003072040c180382c6103004206042e541c00030300c85c00c800940c0c000101c40045400840258807034036a070030055940503d0f0348c0440c005119200000c4100a00302c2019403180074103480f8204a07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 300615818 1250 300614568 300614581
    0xb1206041103030c06011511060403020607080901110910140a050c150402012715021f020c1e010f02040305010902040608010b0303071b15091a09092205061e 69
    0x203e000c4c180b500c500c243c001d20018003440604c1006002c40c40042c2c640b00390807680d6038090703500f04201550300b070b00141c1280741082582038204481c290080d48180017009048a494507107022400b504110300d214402100384010141e00c034803111000c0c1c10f410620b0f550f5408a04402411b903510054010420703004d1584071401c20b0001550661280d0713010b84030641c1060b18600c40c1c03084a4502c82954000e5038203901c0214040080c2600c00c9404840794004201c9000841107560600050901c0000b8190040203d600c07403001c00709448071141d60723114505100000c10030000b0b000d07098421201400c103202140000c1400415041007020a0091b1000c015080d150182d141c281c2ea0440c3e0b02d1038159008002502c0050f0003045088402c02071840032130b00141e01c43d90103183c07540b07807034a0301800130356403641c1409040700001081060f4250174042620740310340c8002156203080300422510581900c0c03140d860050111a0410061071790000603a0a145022400c00045001c40c098401c0000007a40010340c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 300617068 1250 300615818 300615823
    0x9020702100302070f0503040f0503150405030a08090c030a060f0e07060e060d0f06080d120204120f05010b10051308070810051e040606061202210a0b1206041103 71
    0x1a540d00a0541014240241030540281d0b001180440e1441442c0500c40049801440600060000710b5104005289032608041c50464040500b1000f0340700401400000391000040700d0110545081c00884c99580030310003814111f181c1c3d02150140252000f85040008e10340c0705080d032006004040010840e000200d40d41c4480300d018a07408141031129801040c078009000e011034021041c800b040c915801600441079985507849810594404084a10b0807a00181c029220001c00e88007103042c00e12b00802400c65041e104000f41444c00406000700c1486002e4015900c1c0b200064010070211000c0c0d6002841903021030040402d003055510f0124091601254090803106800e000b0803804480c60082002840040d02440c030440c0b02410f000e03090500e0048052080b4021071001401070b203841c1c000341c210030208241e60040b520400458600401403100c035180d44445c94852409680c8101c141c20003020800c000c1c95021900c52852054148001080c9118a203e40d50010a08850740103259 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 300618318 1250 300617068 300617077
    0x60f06090c0206010b130816081903080714070b0f060406050a03020307140d0c0905070801060c1208100b0d0204080f01110d0902010905060c010b0414160e03070f0f0608010902 77
    0x1005820070001040821064030203000c0b806c0c540042c04644a0307071522502d02d402040d0840ea508488040820428004144a01022190019420505824195001001c1a0004082c10244010840300c4070200d44820160340329a5800810300090f428038010b021140d02c41181d80714400e40c240f0f00301003082e0600590400c00c1700c3e030150050540c141049000d0740d06087c00750001e60815102044000450a0240c5150007800342d108000b0381d070b040590000b4600441601301c241802b00c0450001300140c0c0300c0001d61401009031030101c0d42511000c54404111901750b000315100c00002c114101d41465540c010422924843e045840d0038070a00402030030383d02c07401801800c8400900501d2505030360f503004448081e105141c0904000d4607800056680c1e042817000c45803070f0b9561003420f40703241068070583d140d1841400040f07126142a0120500c048000100311007000709502001c810f039141080030201a2181b52620038559803aa0381c52a984e416174400c01d000500c880d40001031030300051082f80c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 300619568 1250 300618318 300618341
    0x80f16020d241b05070218010605180d03081909140706120507020303061513090605090624090409050604031e030504200d170a020705011103090f060412060f0609 71
    0xf07010800310f82000b80c68540011005a03000340c0104c40b1840e0243c0c2903280a03002c0c140c80d89807251030303294160b030900b180d0039400c210300c0c05251400045004a508039a14540c0240c20780000441d40c00502003807000f07000d107080018441c01d00c650403945c01c1e010110311002a079810381c0d58032050340c2d80c0c08149000d6443c190f42d0fa2025070400c2021403950b052080c01d0701e000c81c03112940c2a01c0c1032a621144142101c07990300c43c941d03456071041c09100300d2030451240798000c0c0302207410440000108a60b9140c144d00440500400100020310103d0f80e01c5d190080003526030000241d030038600d03180c01d01030b00940100c245606002c400d42ca00882e0030740240700d201d000c0c039041010302041c0820341c4c40010031300464640d00c0d540510400511000510859103070f030900040b0030921500c490f04d42d1400780c40c0021540001e41030088400505406040001c240c0e4419501203541e44c41041240d80400c03110f10803078012406682ca401c0b110003d200c46500b14040c0700b06042020418241c2e2400030b61700b12628000c06 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 300620818 1250 300619568 300619601
    0x3060f0f05010518060612090105070f0c050c040203090c030106090b100807050703050f3001050a030b060402160b0403020f06011a0703030e0c031006030611030103080f16020d24 78
    0xc1308114200035032190b0020016081c40d241a010301030540d1040801c0700e00d007070180e440c0e0080120640d800300200d95000f5950920495070a0355641d840e490b100c41e40c0d41e05015503408400501100c8041000d00c10802018008000907500c50002402600c00000354500449101c0d484007101031080c0c1c0a240304210950f6103030300b88540740d94210740c00c1c0d01144078272038185002e0161124a240c0c09150900d905900e56001c0d5052240101001e01c00c201680907610402d6501800c00100f0000b48170707140d101074100d41c010f030b640054a01452106e60106409016101550200030030181c0000700010b00304604400c4851a03030b030b85c01406000b05107500030b8080d2a0010f02845000a0181d082600018109029241130038052400700e4a00808a8580e40c2d07220740b501420414490103101e05042d15011840031440d542c11900d6141c0301e0710880c540ca49000307100080046511100740c00020040da402401e01d424500ea43c10180540b4000040c0342c0c00180203090040d8070f0704410b00c1342c072015201040c80e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 300622068 1250 300620818 300620839
    0x21f02070b0c1c0c03020d0527030913110d090b0114101202030a06080303130c050402040302010203041a090612271b0102070b0a2309060706020318060103060f0f050105 74
    0x140f601900c0c5822a91041c95002d001c000446086400b031503200303500380c0c000c041c0341c807424800c012035130100300110a0850300104581c3d007043e1505c136113951001301c2404001c2294003800c0b14824480c820ba880450800c0c2c076009511081214030b0410a040711030968216400304941000c014034044042118408164241020003081c2c1094003e1035002450403000100940d0362003200f030031a44202c401c00100c0c0040340c039132010046e861100402801c4260780c1142803c0c11070740080e50b82d2050780204448078200f02d8400e2003401e00c8004607224104041c00745038503103118808015003883c0540b00c4521720b903088281d00075030301c0720203071203441d60300300c05000300321201462704481011411000d40d58114011100d005c48d410030400000c0c041d80165a945980c1c20358454401004070314200300711280c0140420000d0780a0ba6280302761050309812190050381c90725041c4013004010080342e10500e160240c8000041070203110f9020f84c11031602c0100c18041d403070340c4034032550880e402402080c0e4026503410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 300623318 1250 300622068 300622117
    0x506131d010302211b030309100f030c020a050c0108040519050106090b060a0e1201062102120609070303080a020702040e25080304030b040203011404060e15010b09010807021f02070b0c 81
    0x44005d100b40c8005007d5a10740300180c4041004d543c03c400b12140461600c2c4c002120055040c85159410035a0b031000cbe0507501c0103075407031135111139014102c581003000e1103002c9024060184000315860129000240720103240d480d1a9010701098481c0d062643d2034041c48800b0b6040c004110752035241c4a0740d585032002c041c00100212107112070143c100c150340c3ca04020981c07810340225400e406004e00e5042c10000103510402c071112041c00d0010074035802810074008003050014001c81a41d41c0341c01c04009a90b110305400c0000d004c3c3c0c2c0d4000c0d60050400d50000c140950218490440310003068041000082003454096503940c0340c45000d9080d4403c0004201140c20324481039000f030310080000c00c0e003480103020624071000558050706c003d5a5114245448201003101070340543e0184107210f41e07503244c4100e824886c0100b042850600048500183c9010b200303110104400c1003443c0500d0400042420100003908050811611f0300071040125040141280035942e004a007407200c100300c0700894 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 300624568 1250 300623318 300623353
    0x60b04050913140106060c05060a110712020c0603010905040506060103050c0d020c01061a040906060e0a0311030c060a0e0109050d0b06100e030a06090201081f0506131d01030221 78
    0x141c400d0b10394203c1c200a007421030500380902c0e001440c8035034540380010301c3c0303042040c1000406032031140e100d4900760388000b01d40e01c00342c156128984c000010052181c5000f00503403d00f20031440580d071150000001095030503caa1006009500600403a1300780e94076040198221401034481408160f014090a50111500c2e002050f0201e4408004540c0555a00d82640703400405071500360b400c42c02050902502145214410060800d440d11840c1702c01c141b4081010500c00e404060416040f1501e24810354808100050500ca0040c00c0156500910b49009205180c03604030103000500c00240090903107444440c00002c0c0350020b00360340640e1074000400400e5080c01c54610144038240301c54035150f039003c0c0001000c45019002c080740c4940d80b4400100f801800400c1e0300030030500d07a045180d900780c0030b2440100fa41c2055500310360f912100d2042030f4424442c3d1703105143c04a15007040c1c1c6c00c0d2440c0420154100e1b882a60100d105c1360714039902c80100f056220318590103600c02e406400e5603a201 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 300625818 1250 300624568 300624601
    0xc0f0504050d0c080a030e01020d08010e060d1a04030302031b1309020c0f010c0f080a05190b060919031205030c0306010c17030f01030b0108070501080a090201051b070306060b040509 80
    0x22585505020741c3c0c4d522907814800300900a070085410800328141030f5805001044040245140030745040d0b060070700c0717000c00c010080e010b680620784025003c4100103e507040c0c40c048c2081c02d1103060b01850589001000380d0f20441c0c031000310a00c3d00d5840102d03e48000e0541c0c0d10605507018249030756003020700d414000d400406490125200784017800e01c0400c0b085c0310314607801507240d0f141c05ca00a45104054100c510141c46a580907241404210364a443c1d4501c0321600d07244403c0c0802c83c8250300d000568907000d2070f0030495110110141c00800c0c0e0062500302400c491294441c00c014848203030081c0e4031400101c07800c000488003000081c1c0c0640c8141c2c03a0082061140d1240c0c0408a200e00c0c144102d07400468050741090142d5006009000c281482c1e5801012203000420802d0b09007000201080005003015442da52035103011030440e0700031815207903a280103488142d5440044243c40760b03990800c0c44203485541c0307440313804a0111a0b81003190213440c0060142c01d0580c0311514249400b9a9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 300627068 1250 300625818 300625823
    0xa1e081b0f07030807080c190507091103070c0b150418050f03070812042102031e0405010906030203191b0e01020d1b05010917040f090204270e1f0c0f0504050d 70
    0x343c41c012396003c0081c1c0c0d152810b014003800040c41458285500001122800201405596070a108014509501540c256000f56201c0200c039602d0301d815941c890465070749201a6445801c2042c241d40c0103000a000701903950041c0201c4140503660800303203403030b07210303094020b844003804005245103129075049041d00544500900d40b080c441400c03224103083d0314201c90b900180c10000d030049084120b4010415403034500c5a0b41840c080c0b51400103814407480348a200c0c1819000b00000e01080c03c1174511603c400103028040c08151380c4a50740740402048141201d001c101c600507040e420794800a14503598254a4072014100e4411982007401c000503103030219155074031241020001040c0c60611758603440307016283c9071121b00b00039500800031403a41000c2841031050200f08550b400c03540c2c810b00e4000311901c42c0c0c0f00e00c46d0305084c03140c05804400024013a5101e41181203a018040e04042c0d5202c2c00390f01c3c03041081031071103042112001480c03508280002e40900050210f46000007000e4461407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 300628318 1250 300627068 300627073
    0x605092205030c1507080f0609010603110904020a0c030801091104030b060d051507110a05060708100b070c0f0509040f2405010e040605090f0a1e081b0f07030807080c 73
    0x3c2000400c5850600000c0380c03040b4081008062281305504209016048110840d034803400c0c0c81c1c1880070416111051080d0010152200302d072528951b0500125600410082d00035956541f8150010348090440fa034214000791111000103101081881003c40125124184a1920749903440f14111000e02400059120000c040c0035000103404000145504102e00b02d004824a0f020b40c0240226503181c46018054000c2d07106200054004283c03117030712480c2402d240502d81c0303480202c035400d500217410688071f808000a65005218038425004207c9803400207645215482c8c000703100c0050b4040c0c80040c00b00f440500d07000000746e014112021140c1c400f220b41e102d040d840041c40707030a8070004e034000310020164a082c0000d200043c0200da0b4003a41c040c0042286000d4640c900383e0f038000042010b804401c0c140d4041d0240c0e15004041420b09402030714040d2a07000c1516005c41c002c440211056561007a1000003080c264046001c8084036000040907040080365140e019a5920480e404a00b90 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 300629568 1250 300628318 300628327
    0xa03120609021803070803070b130f050a061a0f09060d03032d0c0e0a1206140702030d0615020c010804021201021c0c02070311040c0e0a120501060509220503 69
    0x1c1000e40701418401580c90403500306071400c1424113092640c02d030810a03160700b0400c00c00010502c1c4050880d0090000d030751000c41408a82409400e440d400c0c4001809802a01e00c0b107401e0000c140c020042090b400b605001018104a0410100107400d1030015000081a80003448500d03180300507481c418002c0c140403441c2c2c0c1044005541851510450204e50080701c981400c1900303840c41120a40c25003410243c1d048540b03c4000340680740d0500c5200700000003502d220082003001c0d048402c0000d45030750108602c5c100300d5000780d2240c00242c0d504645525241c0005080800389021444187c0340d500640044003190004548406c001002642c2200b8440703503280305c8007070902c001c0501104041007040d01202d401c01003000c1e2203104202900b10b501c440c80a0020030810201b5046080003154000b8004028180940f0002401c4007265440b1030100d42c00070701c00345007111512400d0f120b82d00820146807940e041140c40a801c0d564401c5101e000e00c09041c2000e031044d41c030401c3d075014104a070b080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 300630818 1250 300629568 300629579
    0x2010e030a020a060b060403021f050c031303330e0a05060c03011a03010b0f0d09020916140c060402040c050c01181e0308150a03020a081c050406020a031206 69
    0x3180d101100c10703401644194480000d0148912900d40c41200c12148103217880d10f0358000541c0b4143e603140c508482ea03107501130289904e0107107003211071600040f000d6070b8858101d540d01d9117030488140300030354801c444022101480c0b80129a503081c1211305c1e0400107504409005c03044000d06411110700001d02c90054444003140f000c00c060341c424005000c03890364a41c144544142040e03030381d51484403609014001070013190150803c0d03803e04400341d401241c07035010392203030280034220f200340203500501e06500780102c100304c40343c2c1c0345851992920740c50310b00048510541400d1080c0c2e0041103085d0801c0b801314006180c03035003206440030010302d483d9080c186910815030031500300105c03140922121409075810805003107200b902d64125000d040101c6442a02c000d410400d0040c4003400340c00181d9102c03042903950041c1070000c0c51300504400300b0b0035184c0300e0740c0340d0b5811100e545001e45d901c1b98400b402c1080c810011101514040d034054100c0164968082e203608032081880c1034403680f2500041903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 300632068 1250 300630818 300630823
    0x140304080f0706030b011404050103090f02040e072322020f040801020d1d1906020c0d0c0b0105090403020d080421050d0507080c04050d02040b06030906010f0b1c020a02010e 76
    0x40d6405a10701600d112807601c0d10140403240b100c05924140454407481c00c030b044644034159011a5400c0c00c000c24500a42d2034100d901c00e040120007940140b074112002e074a40c80009900d41540e00c0a000c031200051203502c000d2030740e080148156845600c95403907014607400300400344c9402c40c00039405400d1209980d201807007500650010700140c0e6010070303101240d41c1c07603008013410203070350b90300d070341d0b5000e00191002c2c0d11030784482d00b601c3e040710882c4030040070031240303604440c0e491681000356640034035140d100410121060400342c0f188211a030000c80e007485c0110070180200d071315800424103c0c0c04143c0a070b80300d00004105490055102024560080c108041400320300c0c642e81c4c54a035143c0d41c0c581c0c0c800c102d4002400e1b48040049200800600b84100c0302107400303a031800c841c100f2000c0703005e100060142c0004109140c00c1180072050200c2210009140d80c16140740e0000004065102d240c18007440c001c2540c5145083d544581045070b1641c55401464500c0861001140c032081e00c4a0b51031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 300633318 1250 300632068 300632083
    0xb10050c0c1008040b010506040f0b070507090507030204061101050c0901081812070303050703380d0c2301080601110f060c180901141c06150302010f03050f010314030408 75
    0x1404240444100020450005c0010380985005c40e0b4090502e03050220300b17405031a860040104603603000801030140b040c1000000014040c03040181301a180945000f00690814800c035008944080c03100e41921030107015403482440d031944c442d41400c1c001c40044030020360181809002c030200a440c01000401802029101c100da1030000c3c0d0b42d91460700c0c000781210703002009803040602d44030034816522040c5480c5d000301d8003003201416a40c1d24500318807442d43c0c4070400c03243d4005400d1010004101d1100411400c43d190038507101c400d80030071049820010000720201d07000542280000f640d641c001c3e6483c0014040305000c0303600b40412948418900581681c50100404011680c010110140400010802015650169a540341c800c1d07200d680344601c148a8810302a8000e005900a009001030329907c1d044042409a01d48130500038104810710302040c0d000807030120090030380e140603000d0540030f966420041110f581c41e64a9008000c02070301c80602d081c0c0801c05c4001a403040821011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 300634568 1250 300633318 300633349
    0x60f04120308150f280f0f0b0f0307200d020a05100c05120c1e0903010b09010303080a2703030b03010c111c0201020706230a0b10050c0c 60
    0x66000e0103041c10040d0400c0001080c414800301648810429a11303031500c05040c6440c261012138410803032800300003444070342154812100c0070f52203002500a99030203003001107900c04440303903118540b503201d0070700c0070321072061a0200210300700003081100b0300c20348403c0a03070b4860901005114400c02d14060030308100400c1040164001072003e800c0c8601440450f0506101c4041005620700407c0058040c1c01421103295120045400107411026103904548002a000740c101200c0507810b1324612060b0040b074242c50282d868400304001905103140a51b05881e0151035840c41662030440b80e0014100000d60350074000b000240c601c46800c0c201c4008140c3d64400c1e01d010840c3e120081c00e041c2120001c0340700f413080001c0c802c00c114103501c01040030300f040300051005145030a00a9020781c0039100d4548000d01180ca80041185a120110340304540030b500e100201b070b0680c40d0b420140040d41c4000303a580c3c1c0c1c0918042c503000d40240c005c2c0000c04c0710301901c400b61400e041049002502071140702e14030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 300635818 1250 300634568 300634589
    0x10e09150405010e0603070303050c0c15030106031a0a140f0415080f0714090916171e1c0c0804030605010f06020d050a030b030f0106270207050318060f04 68
    0xc0c024185818050340f030140103180c001c01305600d007100c0045e6070380e0040e1202906110340001c200700758078018010210364100281a01000502014081d4501d0780240b0070400041d140442d24042000300148074810300754000e11002ca40d908102101500c581d2072005a070b40040d0080b180c0321151240c0c0281041890391201041030645020307881030400c00b00c0d0942d109940c1001c20b05008041c00c000c0c25038100c69043d100c2d0042a62444015440d0542d4204c6103051800c03603a00000b8241c042d102000c2c2c031010000f0a842039001c42918100302e040000c0c1010388d094020324085884000305407481409840b17149031010f03884070f070f94940d0f00039607111782c00a540041e11030005200300d4417031214900003007a4620041140d00f0a4040090890141501d1803080580f200e806160580d0708000003035034092110000c000583e5104001c034210b030305072540d140c012456290200d21180c0d83d8800e072005903800002543c0340003500902c12020b03503135184115501c640300703015001030038003004003410203003420040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 300637068 1250 300635818 300635851
    0x21f05060307080a05060a090c08010632010f030c170a0c180f1401110f06040605090705060d02030c1c050717010b0d0e030c0a0c17060103080315010e09 67
    0x1d06080c04016004494180c1c00b4144107070004000080040c0e00503200000010b00c6021032070000d15042c0b00394402500b642c20643c3c08075031008101c0240420f00c0c0c40f070090300381401c2e11100403c20821a6611540450a50300c4c4032a8454040e80080e1840c0c610b600c2c000904900b82c084061050005903203001400ea40c8600010540780c0141d04c0c0d038804518216940e039450f00e80741e40d80c08001c04134011102000000a4140b0751a400344c00011030b09c0c40088160b543d00041c100d1125590075040794280c8859007002c01280140f4008540b01c01a620090301c2903181411040b56600654005070881f980c0c11000c02c54003002c2000480c0c1020301740d14110004c10b16040c10b0301c00400702c4074080d44c9001c1c91503c1a0041148452400803070f030302011280c0300032502600000141d402e5004014402d2401c0c0130782d4040c1420094004e00010980302c0b41500c0c02c4032207040d0303460130343e4403082404000c000e00010004140300e50040e0306039403810740052404511421500c2c0c041140890143e925910a685125 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 300638318 1250 300637068 300637081
    0x60b0702100201020f0a051e030a020d0c1b020f0316030308010e060307060e100e1e01080a0203090a0308100513020909070e060a1b0204090c050108090a0b060f01021f05 74
    0x360010004036007840254105010b001e0b00c440b4034401c01a2510a0000002c1c010140080103850408e0110103241165203a282005400010b9440040300c010090f2808075207a1a241c0223071107030a6203180c80e88062500c03012030707401e0010040481c1d000c6a414801c0c528860541400c0b9401800618400ea441c401e01c0d502d880804c0d1000d48000c0e00c4a031098102002c18042c05900040c0302c500403804072401140d8411b502401c2d500842100945a0030404520925142403409181070b00c129000303980300c54466030358039010003c0340029101640c407a0069842a400300e032050b14038a0300300e0032600c41c0c00e00181e916000101245680c0307460307900264002c150750605191a0001d107a10072000d0401e00040400c1200148041c0303c0c0075004814000c030320007a4015210b11148450384c4030360103442003003042c90600701410302c43c006205603800030b240380d0300084070045e000c103a0440880c0c5c0310703950044540f5140c041010b6815100c0f22030f4114429042c0900c50321520141d01e001814200d40d00085604028 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 300639568 1250 300638318 300638329
    0x151407120b210f1b010c060b0915190e060409080d0509010603140609060118060810050a050c040f05010e15070606030209360a05160608060f1c080409060b0702 70
    0x220f21000b01038029107940148207002a00d1196290003d1070600401e0000d032910400814661401c5034002240f00d0030018448815655284603030012941c103240c6401844810800f50035600a2001c03101e130342408036046007485d400c250b042920410b60b003424502d8110740c15049800841e99032696a444aa0402c20301600d540001c3c0c3d4800000094a210301d0301c0d000b81c80e51030314184508000343c803a5895a00042a0540c0403001400041e010f641e9854020185400604819200883c400e45000301041c4444a02c90071a0200c450a60340707411200d240c5001503500c800c4401406410154040d03001e4003560b42100101242440703a0000a2501d0850052105c0600d006000c0406501202d8507140c6500088910071407616554624217281414009402d00f414170b012801032151107070000228071510100801c034144e40065071101380c695500d0041010808000704070981080b807502070044015400000184d026000302d0846190940d03482c20f4a040b0342c400e0f8000151620041b40080c1107241c45d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 300640818 1250 300639568 300639583
    0xd050406110a0206180f0304031b08160b0304020105090901030b0f07080705090d0c0305010e030c160501080f04060605130c03050606040f12140105070c151407120b21 73
    0x1c0c40445081080c07122000e503603407901070f000b222241019044211500000c0201041c3d4602000c00d680d00c4690340d1070f0880003500204102c1d1076171440c000000c1400381001496150303500320b00c00c43d042c1c020b1414003410a10341c40034100360304010301042040560b40321406180c2c0254400e4482107010f00c5c20081c402803c1d40c028013140d00b0022a00e003402440c40e407003415105043e80c2205c2c60301e0204080e107008610303604140d000600c5542894110000d400020020b043c00ac00c072402558180d140e030082c41c1000c0f00c554001c4901040603c0d003c220075408c241c4040ba4401e01c2001f002a8407503c40000503001d0100602031a003168668900c11078541e4140511500308100341c82c0d441c00d003030410f038103040c3d089101e001c0c5043e012040203c003000d100905a040190100c140700810407410002402041040340980646070900c000100f20220b41d41e42c80f0711005c101003920400d8190b210700f402140d040c0c04100e00d000300c103902d03001000e080f96245a8008503042119400100c1c1010380f4035058282620f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 300642068 1250 300640818 300640841
    0xf030e040c0815131a0907020c0307090f0b120102031005060c070303050306060f21091f150306110403110604030f030c02060408010c0c02031213030204200d050406 72
    0x40152207112a5001815250062040401109401d1030040481c007441c0090f428080e18030b04041110250b8041031083c181e800a00b0383d080700503503880b21320a9945064241031541c065100ca001082000e00d070340c2c00343d0060821001c002c142000050001079022222041c1c0d04016540001400b0380d107004040c41d40000d11007074900c90304144414200300d4a074490f910000d001d000000000031460307612041161038070b800b83c010a60b155942ca04061a43c4c0700030031400407d110030b450204010354400200483c1c1903030400d880c910700c0d04501005d0400b400c4482d0a1a0100b480c088002c0001151030050600c00c0414945061703c0c4e6240d800d21002140d094103009010b01410481880450300744400d010481c0e4041c107040707120502601c0850440c2c8269401980745519000c0d0003881142e00900f501e10b510300880c00c5844080c501c00000003644100c504040d080000b400c010401820070b0780060b000845a40c1d00140c00f50041d00c0e910015911008018207041d41e03500030041002a184074903516004e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 300643318 1250 300642068 300642071
    0x40209010314070815040b210307020604030b09060a141b0d090809090705040305030711011404080f0607050910080a02040b03180706050f03130c05061902010b040b0a1206060506070f030e04 83
    0x809001003602d40500281c0c081080015540818234400308104072420706a0140c5801e655a650781810f15018070180da98015501030403000c500c0c2c5000c82e001c1c0c2040c0304041840141180c4401200420f000d00028a031070600000384110b0004034454030a600043e800f0b035403495502e106500412080e120000c0c00031060080502041c40407610000a40b21195407240700300860799915001130794443c00c1036044000300c8400040c0450002000310304422456005c00440c2c8803503d03038100c161814004c41030502d0b04025030388060841188182031064100d140a80010316003030725038074011116407023121604500903600c01036904401e4100200b070010521483d001d824000d21040e040e186102c003074070300740c0a200380b410504140010352442c000240001170030a81d0711608400007003c00e00c0c02140344c0f80503518080c076480300ea06142c025a000080010300400e40c441c10880951488141c940d0300392a241d54600f800f00c2d180d116203000701031701c40c01081204025541451300501448103418180d000d40d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 300644568 1250 300643318 300643331
    0x5061014031204170102040324050703290d0503030405061f0303051c0e060702100b0405010b1b0f0703030801050a0602030a020703080d0e060a09021c0b0604020901031407081504 78
    0x10030040041da03090341c040044c2c0c5410450714607901e5001e03020f690400342010140343c840380440e0301c0700c81410202c003c0200d418400340c4e80707200c0c00364119180385c20386041d111502c90b90050b00c07000b0082d00da09203420050800d103000c82661142441c5420481c0c0440e0f040c0e010b4024041e90664000942c85400b00c609841c588046c111f0394000d2a5000740c0302e0440303060001208400d400c00c02a0032111584680c00300b180c0c1c2c24076004da4029900e84900010440d02c9141c01c580040c0c42c1454021107041c0c034145072041d4603003035a002e1050058100b20b841c0d9041800745030b42c03084540302c0510141c1e0065001c1c1e6070349602e43d41000200801441c80742d00c00c1081d54001c011000ba02030300400c0400c1101d030440302c640d440301d240029140182909003a01e25a41c092042042941c0001d80d201c810b0180c000d480f1b0304a42c641c50b0072054060800c2d070802600f00011000055203901c4c00381c0003008640c00614010034203000f58a54104404000e854160100303501c80e041001c1c45400103105036515504680030300c80d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 300645818 1250 300644568 300644593
    0x50a05070e133008060a0603140411061c0902010e010c05250b0a050c15091905031b0d1e090302011218030f03140f0c0310030506101403 60
    0x1103911aa000b040448200c44428a03449803c41661000c11548030264000d201c010300200051000c403002d52181845450115003248079110320b080c03650222010010546540d26040b001d15428103480760300c400b007004030080c2c003104604150768840b400280454100c100b0310000d49a9841c200d0034904000d0384c0580a0042000003621844d081d0000b103404414426032045038140b18070503003111400d444006840604503030700000030b1108010314420f0751025144440b40c15550b075000e60346140660320038070a104407205404000c0b56410b11030300490f4903000481020403c400c00030000e2600d02e800078040d08500c03980101c190051805500103072481d14580c1000500846c6442c0000390400190f8030821303100310b074260b112100e041e203420181c01450000d490000e1299a80140c000c0000742080c104620741d511714918640540c03100e0b100c00d4441c5c1c0d01d00c0d10806054200806c1d9250190071036000101240007440b1050003515845014400c107400c0503184032941c10350013141030090703104542500300c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 300647068 1250 300645818 300645841
    0xf020a050d0b010c0b0f0403120507110709090c06141201030c05120f060c0d14010e071107080a080708071a010801060503123c03010e0c160303020307020712050a05070e 74
    0x1072200c2907142c21b002e5912241002c440c1d144044000d2042d0915140910640a400105aa04012010044900c05900c0350220400e90b032003004020210800030906010640c007803100d5215104685a40604010300d4135060091440280c3c400c0d04c0280c89803205011508150b018009041c807e40000d00341c078180782403001d5031400000c3c0310f0074034070b14007140001c608038094022880c6d210703040c41090170303550b10740301d805042034800e0b40c038400494a000c003000f9044402081241c12500d5000240c44180010745401045a0250404903100d0b10100400c0300010403105c2015540340500040240a604100801d404c450291b006144207a00070940580d1641e031550894401d64038245070400c481507000b00b6010b018000402d8101c210303401c2d1681108041c071402c0614102d6003001100941074440301025103044c402c407c24441d03101450000100481d00039001142c002e40316104032241c0326551fa101903070b40d21515004032401d8000c400d0b48010310604022150252107582c5d5068134505140c60b2884 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 300648318 1250 300647068 300647071
    0x603011b0e01120501030b0708061c0f020d061d010e030408100b061201030503030601090e2e0b0f09030607090e130201120507030e01060611031b010f020a050d0b010c0b 74
    0x401441e00d00c20030469200390300540702c40d494654180502c1d612071410920040084074414001684600064020704d001c0d03d0043d030004400e140c5d020804059101d00010381210310081e80c02c503030040e800000003407551161984c0b4101c510380c1c010155415040042c00c0d51403000001c65281d006000c1440716900104800c1c98101ca10500080c104501c0c01c00706a05000d00109245800030781c0c0000028014040001c510902007680c0f04606182c0380e403690103102c1416551070401c00200c1194603070785881110301c240c1160308003240380d8086a984501c903580380e000113121900e000f0007241c01e485e10308003004400d0300138801d428000c07941e0382840303084102900001c20f007410f901d154003508401e44e406424070210f542507080b02405076250003000079001d000d15603140b42184d86001c0001803d00d206002c100068107400d409540b400038000462800d02d44000301c060301035540c0750f120b4135142e04144000c0c00500300940b240c68460740f121400d41d003261002c0f11503505209812041b440003410468545 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 300649568 1250 300648318 300648371
    0x1b0d051905090c0919231608070507140d11010f0b09060607030302040e010b0405100e010e130b0307060306060f0207050307030305030c090424081c20100b0405060301 73
    0x400c4075505c0c0d0a00303203140101c01d000320022625007031080000780941524550700800c144455140c586810303420341c41e40a803003016540040c800b0804501c1d818455002003802c1401110703c258500005e10f5aa03040151600d40a0080340e243d01858140240a005100021200031030400a110340305011030140500100f1503403045030000768203070405000b40c1c182e6000d0b107075100b0b413040590385680440c0581c0d0f00c1405032900c1a42080c0300921030303c0c0f040001080000c1d0603515011103d4844050000b401c0c4e5900444903c070381c0305c06102c480340e102001814018401a503011845520b058070207440c41200c2c81c0c40e0341c119040f9040c1401540c40016958044030b51500e0115076030f96541e030800803613018800c01035500c203040440da01012100c021034181701e9182c43c44500300c07441e510071209070f8440220381e40001a4451403405481da600900341e60340c021101d4035020b880d900b240d0005c182001802c01ca4a0303030b070f29540c0e40405030504140c0328a962000c8103400801856210030303034290522030001e100d07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 300650818 1250 300649568 300649579
    0x9040e1b0120010612110906130b04110304060f0b01080919030e040504030f020c0406060c02040b0f060c060703050f070c1104020417100f060e010e1b0d051905090c 72
    0x182c0e9800d24000d0040c840349007075500801c00b29459205a18840c201c0f28000d844440b4020030b00c01980c0390503440d5501607440204182d042c0d151145400000d80030189c0030f20340c025554051001c6040c2110000d43c8940c0c070843d40011071610102080741103610210302241000482d8013005000796000595407a000361341101c012039203400c0d10701101c001c2030400c0c00d142c1203400c0209100404d60046090009c04000780c00f500c1c2007020b04d800740400c030340d41c2d842514000340d134440c03101e80075003041d034844003e1503405481300800d0009400411070300c3e449140000382c19404481000794256041c030905803c00a8401d8003031260030300040081c441c0c807030b10001802e0309020300145501c41c5d443d030f41120004c02c1c11944403040e503016801919102c2c00b54011302c0020904103448010b00002910900e800e8510f483c9820066908240385800c0c8a0130042004461800c10301492050b0303c00380000c0c0607040544030020509242000003449818200048009013a0802040c0721842340003150f2818000b900307841 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 300652068 1250 300650818 300650837
    0x70b010e04050712240522050f0118060f02040e0c03101502280f03080c0708033102010203031b07020402031e0106090308040501080601050d050c09040e1b01 69
    0x902c1c0e400c0c10301d10392021060900f1007031100c04002141c4500c031004000c0c0303210711500701160305a84d000d43e80701b200c1004900403240850b41c0e15000200344400c14a0051044400d030346480200f09084600035414804045000d11007101041464003801104400615045d4202031a103030328112805409022100700103404400545410714507041c0900400b0000034000e0480b601c842d019440e17030100070800c907168450300900301e5513600e00310000c06425405a801c01c0c01042d80e44003200c46031000380510107001c4040140e540421126406075004007080340c106802000c075480030740003078442c1c20b44800c0300c40825114400940e8001c003d49034002c010042081780c00c0e140284902080c400d42800a600030310200c1802100800542101c0061403c500920504d9880d07101c1516130140c1c070312006001c071108100034040b03540f0441090390800740c1030400c035007000c00d01160039041e41c504603420050400c0c08a0480c40c2d03032903c1d009074824204824003800592698090240c0000d9841e44c07030b28144507903540c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 300653318 1250 300652068 300652073
    0x22060f0f0e060909150f0d0503030c1309020d0b010e0102150415020702030a1a09060c0a1407200127090c1106010603140606030f1303050d0c0314010902070b010e04 72
    0x1182e0703181d14004c010039614507000c811043c03600c210000703032809101041c0d0340026a00704180d050100c2c0d60404000c50540d60b80c100c56619941c007007800440c04010660300010001d9190024040c4500080e01c0402c02d62030071800100201c00c2c038100d5034110761151610381050360048450fa034006810461f2100d480103200481d00181c8030f030000094252094400380380600c0b040a21014501034400000107440c5ca131300c003270540d03103150580b800d5002c00410410030580390b02440c108a6002c3c190758a0700e0412541e07440f40708414000c244011a1038400084012903583d202a04407201400268000d600c40d21391013414bc00380985014800202d9a00d103000c0c440240030b0114034110030240340455400b5a114840107020702018250304602501c07410100c1c031245408800d0324854082c210490000b6925040043c0d820702250b1010f40500004210440c9103d00394040c1002c01503482e1004034549500001e2081c03450380c168480403000f8030612160000400c0c0035089411283c1ea10000342490300c0c1c50 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 300654568 1250 300653318 300653329
    0xe0709050d1b0f0e091603050d0e010e090703090302070f0b040b031005090903070c0603050613200f0c070b0708031303030e01020415030515091f03050322060f0f0e 72
    0x3600f2007010b11100c0314000030180340424130103200e689004c0030355501220342c15080703000c10818000142241c02c86514601a140700d203401044c2603074140742c0b56200301d0007000454040d40051300c1d20f00010b6100c0800505140d010050980180b500640c241c0a0501d0100108101e004d64042c4803051840000800d60059107040f07410f010309001407144900d030618940e51aa00d0340080c000f100c540e410807000184d0760f0700a03c9001e1046501500121071aa4105c045000401240e0100104003261180d02d503d21401d100c00f030900c060080d500d00d80c0e120f10b0021414580030072640101c292000410161001030b412030140d070381210384090800042c03d100e03d070680c003038401d0010744203007507201040025070458580b031940715081c410380b4100080d443e0320b000d0a070749141d031102481c1c202180e01c003c2681b83c2d5511025040c8640c0b00b030751010705180c4a40c2e07060300f50350000c8440c00e8135400110020b40b02d028045890401040541420071142c48210b00c050280f600042b65907081c0004000043c0c01038488 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 300655818 1250 300654568 300654623
    0xd0501020c030a0509151e2a03040801111306050a020304031a0f0609060d1103150117240105090c1903090b180c12070f0f0e0709050d 59
    0xc0070140c0f6200c032000d0100505a4000203c0c175440b03604d11380174107050740180000300e41d100244041401511035482250340055884091034990000700d4000103448004904000c26401c52400041d42d9280c1c5000d076010301351102540100c180c602c04105401204100c8000e82049a04a06200c1d44844400e5130a9095001c1c55202500d85110000014516421070341214414854102c00e19a41d48800044c0002d04508036082608100d1207007a00c80400c209290702811013400408a0318040b80d401203001c544502039021203502e024000080e401d2136000e01c00d00c00c80241c42d01500007504c1090441e81841c44040c45114000c0b840d10001c14500e200d544c1c12a15120a1012100290100000d0043c0285200d000030358064404c0170125880495803449099000c02010051130b1031385082040024900700354071106c40da480b51540c006101601c00c08260001d000242541e4446444c00c60f460000070002860f4204100b05440c0c1803003240c2d100a042250b0341d030040d00c084128180400000c00c900714 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 300657068 1250 300655818 300655837
    0x16090b03070807020601150e33030a060605160605090a0c08160b13140607020d0f060b040c0c14011e090309080f0c0d06020f040303051902060103030207050d050102 72
    0xc2040207803508800902d01621055003282c83e240c2e601c03103a0044031898000301000258825010500914001c081e4500f100902011031140802c2c801d80d2442c40043c02c12120316040c000f10412100720414882e0200500d0f841c240300e4902412800c0900c02c0d1800c03d1300c000c01050351400404c410100400c460000b081d8003403102d459558603802c040756035041d4008009c2181c0240310307000c80d05002d1203003500c030030780b501c0e40b01507907002e0070308030450f4003a5030003400c45070030078800d010b06009a40d07180020000c1500030544c0c1c05280e000c031704207042030b40e00045419010380e08110031001000c1c3d1140c038451b84250041801540410715401c110301416840c8a01c844000c2d0749200301003804000e070300a041230307846525441c14184d99030021589403103004027141d413070381c100c20f400e00d00b14102510109002849010f00600c0c109100000c3e41c1e09030040d40042d0300103103001c1070700d0b2500071071103851050040641c002040c0b07540c51660001c1d038945c0280249802400c12003174840c104002501560701080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 300658318 1250 300657068 300657089
    0x120804030b251e11011118010906050f0a0c03030e071403070503010509060f0709090207050304050a05030615130204030c1221050703050a0504030b1302090108010e061609 75
    0x2409600240418194400584110103a1009111090140c3e048038403040d200440741d039165149030070035039602040240c0890700c2d540715800d00003418010342c001d044803208103800440c401218800105841c8403500b2000034480c08001d10400c50044100395001d2590510340726000c95060b10313003100036040c0340104803c41d00c50880041011855031400e0518036400344c086444143c0e0305c000300740c2a0f40081d21481ea0f2608184007040100385100c0d103250f4400c00301d041070f0103582d0703580322910200da202e0300066605030001305e402d21003403901c80306560040208500130507040c00d00313040c4562201008902c0e00d214a8100c604140b801d546038059500840d00202d80144044c3e5441c3c0e069080e02d41e440b0215140c0c010100192901c6048008840d001320566980d5401c00c1016076054940f903201d00401000d000040c0070000008440d509503501c0382e24255109020145144144100f040303040c1c10040c1141d0410341c84071040030300010078540c060307042c0042501002d0007403804c0e101e101040d0480e031040c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 300659568 1250 300658318 300658321
    0x151012021e190f051321050f0609012003151302040602031908040c0312022e140603030a03151d15030d0804060518061608060d030504120804030b 64
    0x4480c40c400b4058040155140c5202150345103034115031034401c0381c03030865801840c0202803000300a0400c1070703004c40c0e0000c03081400d43c43d20b64845620345411300c3c19099440d80900204005070200780510304c840e0b0861020000d80280f0303500d80c1d42290000401c840e0703040c94170141da1840d513a680004841c0c01c107020b00c000c650721074449a00035200d61110700d4000108103c0744100d4800c0f40720356071140c86250031032101d0507a14110341c2c50100d0407158403000e00461064442d03100846550781007000c0661100b0800804190030480410252440840741d42c0e0144171200070004251001300403515409010714000a00200c0c0464142200d400307500a012925001102d407060f1030b2440102c00d0182c0481c5048034100c0482038105036a60503100065000686241d0105000806070780003543c000320419a40300000444540080ca412800c94807080b084d80c2c4030f00000c00594100424582207241910242d4800700d154901030300c6445a8032400c04c298115504660503c16a081964095031340424211041e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 300660818 1250 300659568 300659587
    0x31f09090303180506070507030c061b020606030a080306010e03010609110306130603080403060f09020306040c18020301050901030f080c0a0c0509160c02120c18151012021e 76
    0x38a1160001c0380400d01e00310802103040c0103924100040d95210004042540e1952011612500400c100724140511080c2da6030000300e050150030001080b810114007510b403604802490444080e101c28002d4010050600200700704004a90f8844070a081088090500c200401d0040800e917001d04511460204580c0549038004003c5001d04421501c4100030b09000f000030044078114440106555410481040000e0803034001c111601c2e0f20341000a03205a058001c2400c00c4412101100d81441c401c205010042280300d10000c1e0f10741a5504600350f6040802080243d441800007612410340a8260130800201c3d07011100e02030107a000f550086070303251074081c0540105d07004807849040c8a2001840140c00c0b241c6500d050206070342c03205a81c54441e000d00ca01c00000a980012130b02642e85069840c6c0c40b203208542038400000380c100d120f850404d038414181039181207000e10a05030f0300c001c000c0c1c10340d110708803544040d07912a0050741e400b03c601c0202120000d41402860301c980101e0340001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 300662068 1250 300660818 300660821
    0xc0f0806100c0506150a06110a02130204080a0506010503060a0209281701062102010206061e03010204230d03080f150a170111030c04091109150a0906050306010f05031f09 75
    0x1c1c458000e40d000780f4030648a00059031102392903214128140d00c580403010140ca0854160245030a40c080c005181c02e40f00c0341d207075046c102528020f54603075103c40d004118900b020441030b54811501c503411424032560b2000650348082c0e441d0800c0c07900d2803080ba00b400c0c60449424240081035400d640b40502010301650a0203000288a600f40c2c115240e40c001c841052104210744107694143d000d414155149820031038032490b080d404080e602403042144610761424402800500078880c4104040054000c1c5180d1155030104181d0083c0d030341c1c100140019821001ca13942009011856408507980e200c42c0000c0003038100c4035207500c0808904001410710203000380f4828625004001d0000a404944103662484240d8162001540411040041043d568803240d040000407150925202e000d000151051400c3c0600312206000043e2001702540c02c10722420080c8403d0034010306501e8141c00190031f01d100c0d6145c0380184100000015114107202e007803c184201206050144291a201980f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 300663318 1250 300662068 300662101
    0x60313030801050a0b0f03090106050a090b090c07030c2301050103080301030620091507151d01050f071b0f0302031b07050d0f0206040e0108030d0c0f0806100c0506 72
    0x9010800070800410075040241c00c0205891030140b001d841e0250901d151104c6520042c205100f079560b030380c00480e440d680c914201e4000c0010a03400700320441c2107420420200e07809441d012842500b0050100001e40010940d03606031380040705003a10b20000c640c0c40c800e0304e0b13039000916101c0d483d1100200410400c0310146040e64007520081204910740360755000314202d10162290342510600c1a00440d240042e031040059103001019820250b8a60b40c000500d1842c030302440e02180c030741340c6212440d00d803402101e02e8805000e000b40074034105140c1e20800340c1da0141c036420421410058140107814211442c40501e54083d240307900407039060500a44030b820924650040002402c11100041c2d00050285e00b9214002c0c000a0b03101c849075140d1183c4101c51108a0f0400000d03c800a08a00e5148030039001340f40003400340d6aa04561190081210588a01817003032050030041480a107034005240c0b58043c006950101036040221010ba5099000d400011722600c00d40e020417545c508600d5444 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 300664568 1250 300663318 300663323
    0x70515120f04060506240901020f100f0c020313050105070606030b0708091e0601050910081e07050103110315040b060c03040311030606090f0705090a0602010c02300711060313 77
    0x30441383c1c60701002c020b086d03d1010320446690a8941030584844114401810310314014012619141e803034051840c10640b03181080300002d039079096404070718044c3d070060715100c3d011880911310700401040c002c408c01010b4050030381045000310f141020400503a018002442d000907000246240a0324006d0030884210f456984c11b000340c10641c046401004051910b2380d40220280c02180c0c00d000c00d20694a000400310350414459800001d49a08107005400e048080c4a01c1c410070300e9103421055282c45402e41c4064101850a4010200100d44006494000002010681c40802440002000b41c04088205940520001000040100004000d004403445907000d10000a5034404050303d80700d00b00c402c55000241d050000d40c2807142c3d200030030390211640c14081c0c1841c81d0400440c85e040c40c4c607007244016239524006205031035010030680c086110580c000c111458130300c1c2140404507006000305c5005a002007038150811007032010b60381d48440090066506ca2030480c044401002401406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 300665818 1250 300664568 300664571
    0xf060b0702040b0319060e0703140303160806090a020d060305010c0e03120403080f0714031207021504030915030b0904050c100f0e0d150f0203011e0305070515120f0406 74
    0x50400c0c0381004508041100031141d40c451080c0200e4680401410201c521f0f02850700030044007000090f0750018203809881080000e40e105d241511071b0700c00700d2090f4164202030111700d008003c4903035504107209034841d003405005a1600002e08005002d04843d410040141d420900c26201307059105101442c0010200d08131110000000d642d00124030542c04040c007503c80c200841c82c02d64081c0801403820381e00c0740c0070f6000500e0400342c625046420901803042065003240038007141c0341e41004981e41e00949945107608a081aa5018008054622034407200f51003180380060058002c0c0d002081005015080341164034182c03070260780345e0390445c48040c070843c00d0f460600942c900c904142d8052011580b41c00840c403080b4010044040d00510f02203849560590360355080c80c0c0e41c1e006070050f84006c041c015031a5414907001a0410641e041c80c5207848650507004c20105e40001011000c8845c1940c500e1440e10b605514207e16200309101a0003001c00081031059442d214030850f0b1085008400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 300667068 1250 300665818 300665831
    0xc1608280b0a0c030f0e030a1803060c0e04050a1803030507020102090301090c06020d08010609050d0206070206070302010c080912030109201602010909050c07110111010e071a030702030301060e040f060b070204 92
    0x20005c044a101c012004259070052000004041c090105030b040780c02c91401c0344104683d640e403240700384e030248a10200081c0c00d100e820740f02c03400c00740111900429090014002d070140290060520007841102030704241d10748000c04e540314000e5044400394400540288803801017402c004110206070700c43c081c01480347c54103103c0002e22a10300d450581da01c960b615145180f500d002c001030001182001c0c0da2150b1304105410045e0b841400401d03426119800205241c820040040d02c5108010201076554100d100160a590b500f00200c07415034032148000034040f0030030040c2100c4940d819001c1c444030040001c0c083c0f50700807122001845c96200b41ea0350700280340c0340c2e00c0c03200c2503c03020385483c0c4155405020040000e210400441d11403241894840c4018010082e002c1c00c1d52203500180b120f81e00003c00c18002d8013a4503000c48160405046554070b5805c0c9004003d41c2d0f48014811101000420101212580d0b41c54202c4040124440000e20401d034441c80f84100680c0514402c071711480c82c006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 300668318 1250 300667068 300667091
    0x412030203090a080d0909020d0b09040b15011d09130c0f090b03030a091401170109090c090b060313050c0310060e092a060d0e030c1608280b0a0c03 65
    0x501d900c142c2d8017030b41d10303581c14520f08500d07000070350080301b500d03030150b62150068580f07600e4201125108500428510b0001ccc1810b201c00d05811112050003810440308e42c43c00c0403030003104681000941410340b80668079540d81030440075012180702c030040030181540000a2444083c0700384a065445040c4208014403004082682d070384100c83c03455000c2800b410003041030311100c4c5400304c0d1050f418144a9000c45030301e4940b6071200402d8003c00a41136030340f21628203012425a001005c1c00c00341c4810001c804244000403407030b0100a001c59040002c0000d504200101030004800d12100501280c84c41d860080314080036086c4d0780107107106170061500003080c00c0c00029150403072801404410030820545070844ca00000b80c011303c40e8008000300300402d180c486610400760f804003240040c584032580322000310b042241c060034460ba20403d4400500c00e0440100e94404418007090a00c00400c0c0c0c49046080a080d4144001d012103a21000b04103a00e5603542140342107901a503420844105400d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 300669568 1250 300668318 300668323
    0x1021006030b040807050c04061e0b0906031807080a0b010311030a020a0b090f03120904140417090d0803090f0d111504032312150112110412030203090a08 68
    0xc0c07001900d0401d4a0340820042045071000b40300e0700b40604e055540c140b1078100880c0640b5180e078419242e000e00c004000b42400f04041c125401b40c0703415000c0300d1510445400041403400080d01091503817095411005095000704082c0d402030540300b044e40d6031210341d410b000549110034802a01e440d90b04201b1190a842d01040c5100107640c000d004103001410301c262550039411181c569500034a03c40410f6481d0340d010031400034410f003040c881d507940718140c809020665000210a5850354060014071000400d9440820200c0006071440b5880d241c0110001d01715000000e4040c1961030f001091110510b004500250790b0340b9171004540703040c0b0b071441003251003c4006c5400c0e0010740151201d0122a440c008c00c00d90402d000b441c01c8040d4200c20210344c500001006283c1000c40000200c56441100d0416180c6d800404603910007403184840001030038580c0803400c0f1400f05070b903c082c190101c818680c10395015264440d90f229a0080900d030207956644a041d40742d110741142800011402c000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 300670818 1250 300669568 300669581
    0x41203110d050c0a0b0a1d06010314011808130905010b0c06010611030702040515060309030c1c080403030c111603110604060c152406030b0d170c0f0d020c010210 71
    0x181d0001c00035002151551081d01030046c080c031031002e0300c401000145034041d20702c9a448011903000f0342103551440c0380c00d031ba03200300c4282120544d9051400802c55107141c0340e0720460381600214490361b0746450a60f0340e035660b010f41e0440d518252802c80041a0120014040d0802811040454104da621410f060700e10030503101041d481c69008214074001420190890f030b0700710310348011724021840c01000050041d0000c4491441942c0301081612800304204030711903c0b0a07071882d00302c00442c1c4036034004105c0350000308080e060603120007030090180d1154005091000406060b15920340020b41184c0d007006080c4001d58014151030540782c428540b010448040751140d1315a45031003546981e90f0341075000716510000c2d13169a1040b00c118498200c032000459540031132540c009443c20024007030202e66020001e0750103410754001410001c0c030582d551250320440110a503403540d00b00e103891481c007200b100d69030a00e8040d110490707a0345500001e290340c0c1a07100344c0903114044005034090084911 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 300672068 1250 300670818 300670837
    0x20f070b04120c2303070b280c21030b06040509060411160501050412020105090618010e030408060a1407020606010c08071407060f05120c0a05041203110d05 69
    0x28100010031010341040c25440e907051007900142c000f980e60b801169981c0702c51008180c0440e010062002040c5014004607025010054000d030800000070120090810a0007c502c4c440314244209001e0304c0c02580c00352840f40c1d10003482011111080024000041003410010110781031800d5500310b40b801905440c15641e0143c00600c0540e103030000c10014010000c4003c45603042040346800503c2d0000c1d40c7c00310b0303d0040c800400e06042928101d07050341450f07290b10086925100602800f04008190307550490b44140d046424162000c07a65401000100c0606d41288000500064190780101ea018820400c242040003861203096050f10850400c035040c8006804c03180016130650f01444005001502944c8071070f0400c0c0341c0395110003581811002038406580412030400c001e990000591300960490300d0b2545c100f42d6102483e24101c000a026003480c041c0100341400c0d44c0e07200b0750070388006000b407404807101c904a50034054000d00d4840180490742c003550f5006c01400d401442103894015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 300673318 1250 300672068 300672089
    0x3020a0210090305073804020f010e1309030210050717040803070306030605070e100306050d0b0405033109060f18090203100e190209040b15060a050a020f07 69
    0x281291104001882000400c4084c41000e02540002c41c1da0302c42000003010900451003450708030302040e44609100381d80100c91031500d8404100060300c441d040c60980c0c3c1020b0903c3e80f580362140d400654020700c1500e80040d500d151100200a06900250002c00c0c110110420080c0d500c0d44042120400d152140000508030702d00042800114800002d641c080c509250020301c071070f1243e0303a02e02502e000745c40080000d09079196a00e4607241c0000100c4840e1a14242004250314040205418020080014100d80081400038090010901c00c8a400190f8030801d081d00b0101c001c4c038207480e40c05503903c02400c01e082103000304061040f84945401e5401038a2402000b9150900881c0c07a05a90082c40a2150b00d420b00100140c03030030003c46958240c58180030a046000203112484c00c480340791001100e109180440c00983c03600c07a0801d811a4210705004a241e440841c4c40d0075420103041120340092001607200d10391688500030b0924802c01d41d003640c04854000c07401903504c265078010b064407034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 300674568 1250 300673318 300673333
    0x1507090e22030f03090204020d1a22110c0d03090c081b0f0d05010f02040501030b0607020a050105090a0f0b03071e0801090b040b0301020d0e010b03031903150321090603020a02 77
    0xa0083c01c614841d60403d10300444e2544c01603010a003643c10480f03e014074180c840e882604103214890301240548000d070342401401a0b8040b811510a13130f0b10101e02c10f4180e0b80c0c105a01c499045a007102c00c200c2d9100304a1380405918071004004059903401907560301c00303200020804110105a0542e214141d1806600c02d031205010003065002115160f0391102007118100c00150003800340500003110040c00684980c580f10026065031080004a80304030010020312006a0361165140c0941c0d8083c609a91503081c003201290b21b80200d90802e440c0954280740000e618039060004512130141c0c0d6840d415410481c1001c7c01540d50b00b4450740c0003007081c00005024113507007036110f8495808020400700e101c03403102001c2822a4000710400c0400da071210f407a018809424040c40994810a030000e520300814070300b98801e4112030f4203040b01090303101c1804401e100a9080d4941c00745030840d1200c811540ba00c0c0d0b40407000304808030720f040892074030500015018024805d4901403455038010b485078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 300675818 1250 300674568 300674573
    0xe01031b0b03090706201c080115121104030206070b0402130e150901060b0414040c0c03020a080708090a0e06010f022e0e0712050708061510021507090e22 68
    0x5450340d14080642c0c1b080002d9950100460410482d18041d614540c0c8807455429501f00418400d4140c003c07070401c4021642203c0c8081c2d000e044164038500c40880015044803512a0314000c6c4105d03403000c1c2d84000701040d40d40a010060b0005070041d0300c21100d01034015072307025a02c02078881a0002a40070740000681e0560702c1c0c0030100f00c0b41d210300281d000160242c1c0f070b00607007900341d0480d40099030480810741c0500c80d42c0c10b16205071181804c1e0780c102400c2c100e40e6603a009541c2c0e080c00000030908400420203404102d500010795441070001010170244a403100009481c0c031038101d8039240000e82d1710001d040954004a0610142e405200c0042c4034100070101840480ca0850162401169a0104981c5140040c4071090182c10361004c81420740b0403034100310380751004540000070310380c200c0c1d01807000e40305001c040e0380081c401c280d03141c190841d50501c1c140c1c00e04908180a5002003406400c202c8090340c841c01c0349041c0e45180c00301c81c04a03103c002d0201d04802107203c030346c06005150484c8002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 300677068 1250 300675818 300675827
    0xe040c06050c0f01061202090109020717130909120314060901120804031b080f03090f01030e010207171b010902130213030c080105010f14010e06090a0e01031b0b03090706 75
    0x200b2080b1070122005103880c0c8011500f12101e56000c04e50512002d1401d604520300030313000e60300500355039000390300700b18940e15500d410200945112941d201c00055180300c1c801c203034610744c0c000c02c9082c01c10841d000090910703012120540010600191805070300481c0b0a00740072509026840c0544000881c3c1e08140b00300c14000390800090720640343c01c0c80000001074040070308001e9080e00d404000750310b0b40760442daa861304c04400000f05160b0014800c11229031901c403401d042c4d80d0310074600841c503103000c120f1107402449100c80c040c10340b0751845089100c88c11003500030314000301d504514a01c0400c0511905080340d201000080d440307000043c8240070100300390040c1c04c02001c1c1003c00e0110aa0301e0781d50140d41d900b40d500c40e14150751508010046c010103008800020b00502c2c0702c0b80c58040d107101c0002d200d892001c00311841101c0c00b10f800d44554031001d4a400c06040200312003412540c40707061001030040d06a10482c1070911044021403c14503001c10baa004a140100a02c42541002000d65 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 300678318 1250 300677068 300677077
    0x7030606170a1104050405090d0e030615061e0a18210f0203120406170f0c09090a02190306090c03020a2328090b0306010f14070f080a090e040c0605 65
    0x88001040c8004609591184a200d0141100d02c00406c254024280081c0c00d54544000d2b0500c82c0d00008204a4080e00b00810b80e1000700d01214000e40e0780841105245c4450942e10108500380303404111048100d42140307401410880c0640e9141c6615602c02c0852000020500c3d4030f07524003a464900c0380011010025840040d100030140c94541f0880d03520281190003035404500040c400416510841c00d142c5040713601f00909054500c001c2c6044400c41c40e407841011360a5004904050010380d01c10410342c10b941504a43c400500c50090440400501800d000c0c0950a02c07603103070400600c0b8050003442140d1810f40c00d81c503079091a41c1a0182020000840380d13000084801c00c1008034407515401b10106c0c01c8520b03c110b00344031602c288000401d00180c5400156100a081052082e56a04845103103c2d90382a46081104440f4603400c0c21000e01070716038010500305020030a801081a5080908442c501c695101c24020359955110441c800054501410f03103a50780300e007806014441c00c01007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 300679568 1250 300678318 300678341
    0x101704050c090c0a18050a180906060b07150b01082d010308040314010e031c0905030406020304031707111309020a03260319091a090607030606170a 65
    0xc0740303540c0a50010464038441156003a542035400110084021740250180c03201c1503101e4500581c3c18113000c003103401c0d09000c0c043c000c0d801c9440025003000d05825084640400d030312030f00a00016a540203040000d0704490000c0b551628080d05d0300c10100d04030311480b10411816540c00c155038031003440400d003075010340100080c090100840d41111030018030b40d980c000d600c25514681d44515500782110403401e080340400301a4140091896a59000000e0b40d1078150a02152040c8400020341034005000580008042c2d010108000442d00c3d00440544101c3c1c2c0500c4140c064054a02c05001e0039111718000200000d03003900441415007020a00c07091320600410700000c1103106500000c0910030554000c84454070b05408010508003040c09904421040305062421420190890300d83c2d81144184003000d540c2d0381c80d091081c040031608204040c0e1907003224051900340a080540c441a040700d03040042030030050006030551041a007106004042804c1d112039840320800c01e4058400300a01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 300680818 1250 300679568 300679573
    0x90f01080408070501020a0c060f090f0803090304030213050f180706080403110a20060a140c01060e0403050901020c2d04060b04090212070e060301090b0303120f0f0610170405 77
    0x440f000500241b0040031110303403a4441028070040c6280c5801611962505030034034a05041240c800510955040d204c80c1c4c6c1e0040e00b040d126a180301c0c101d4030b14081d540c80603503c815900c0c000850020342d90700403409403540040c01c52090790384482e00c0500391340320b07080c0d502c0c941d10001d000c000080c410180c0ba50418840d10348041c81c00030079071416103040d00006045c0d0f41982c000e003900035407201c03a50592078100030955485e03042081c014805080b0380032030055030414100000741541c80d00e0702903010030701402c01252404900d061504004150350841c40d0001d001d031056418030101407415100500b4190003000400034050340700c1400c5401c4945000c0801d800c651150404100309000002610151521040060303c0313081243d541000c11070040c01c03001c10b021400e600781d809a01d03403100300d0f410360b8000440410b02c00c00d80d001092130340c42180010108243c1481c05c0c072070003a1803d400341d4014804401d003261240c03156810040035000d40302c0c4000128611440329503481c0200280554071038015000e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 300682068 1250 300680818 300680827
    0x11118011e0809010507031a0409140a140609060c07080c0a02030f0114100f03030f02031c050a0f0b130e030d02040e010e0a090503042601140a0b0303090f01080408 72
    0x4903007001c998244140480c1211082090b0000c0901c41d20342c1c42031a5180500c4882982013060040b2011a21110300072a2544942814403405e01e040c2e051103185103048034464040e50900800640303880b014802c4502540d030102e901c0000c0054041d016a00c045040c92a10340e80c1d07074402d411640a09540c0715103004016078034000d43d82c203000c501b980080810020403100044d80361141050360041c01d602c40594020020b2022000501100050700c1c0d040c01d052000c0e030030001080e890340c0038039045030f031158440c01e010b00c00701c406a800c040d00442002406001d441d96070b543c010241ca9030002c4507a044003141c2c24411143e100340c0c21021082a11300300352841c1c1a150207a0710182e82c0a03400000f40c2a1443d00100281d200d19034504d9800460721200f0007400b00c2942c0d4003626849544108549030b04d5000460881c00700401066014540c2c00008010110042074800840c40c401c6030301110440ca403414201681c00d0110444202490080c86180050032034401550401c40203001518001020320 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 300683318 1250 300682068 300682097
    0x105030a14010b0904060509190c1b06020d060821180603360307060506040f020c0106090f090203070b210403093b0604020d09060f06050301111801 65
    0x1e060602801c044143c0d6642d4002c2d5506001c04e44a042e441706000301d11050400180041400844c4820688100c001c0342406083d0811196180001903066010007412004001c002160703005000b00800c412040c4101e0742e03600c210a4881100610450b800d04100c8208400003144030028291110540219215003c4480204074540c1048070301d140048980000803407105c1121480200ca6801e034403508030315080b000e050949074052590000d001c681c46001090450342c43c1c0d00405403080c1318420854664100149103806080540324075118249440c0030342c0312550040c01003402c0395801030000c0c460349242004c0c0c0b02456010494180200b0207660a00c89035000d80301c20a40600d000341c0d100d092080c200b0b0b031610021400c01e11030503540e010307064000b0400f1400003100c62148804000c2c90161366600350218000c1e00c5900c105943c0c16103441c1541040203c964414030360741d480c10100300405515181814200c441c4801c5100b00600c05005545204030310000840c03010030185424007101c81c084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 300684568 1250 300683318 300683351
    0xf01060306020301081204080d08040618030c0b06040203070516020a030c03300905040b030a02040f02041a09010e0d0f08040306020405090601020a0c05100c05060702060907060311090105030a 84
    0x103400032140c40d0b4001004000e40c81080003800740d410003a4407005c0c5801d203019140395490302801170200900074010005014894503910003202c1b50311103082000f10741d85a20b401002201d0508044442e4103180d8041441401d0602c243c0b4450300103620385504c1d2441d140c00786550300e20380e42c0c000c0380d00c040c0101000c40064402030895005502c52850152205170040391007030880d4824548840502c6c061219049813a8002524004c072038042e0390002c0c0c8101c008020a0400d02c400301d003c2e41050505820741c2d1641407540c001c00407244825112921490710845400c5a0308c120086c10740080d81c01d00e1030b4806443d06010700c1c0c03440c5124030a100c1c01a5040e40d500c8042ea08664000d0f607402d54003127003c0119042140b0500d50205091000c0c0501080c1c5070f41e80b026a0500740503a82c020314084903a030600074040c2071149000b03500401214010f00d01036400030f6071850212134007840c0b0b009403a40014014024058400d44900c101d4030300d0700b00980100111407540004190800c01900ca000910880400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 300685818 1250 300684568 300684581
    0xf110d150f030f17070f080a050c0d020f160f030b06010c050d05071e020a14010c0803040c06110715120b130c0e0f0105070f1406100305060f010506090d0201020f01 72
    0x80701003400c84480d03801d000039032000b501a5255030010412441d00028a80102d031b4548551050340c80ba121002d9040c00c80d900e000b0100415854454420144402500003032481d000c0d20888045039a021001d01e59a00c511589201d181d40c402003000d000d0000030500710a9036030001e410315042d900b5500d107454061030640506441000300e00001071510078071441d08600d680200702d20307003c1a600e06c05980821030344d94882c8912030003110125590348060780b2a00a100c01541c00880c1c1940303905160400022a14080c400c100100c0e0000d90400d6002c1130119060301142c0300c403400080640e0540d10300752403c070340200000e103040d5907900b2460b000b03544003105a000340d410607074001050300c4c22420142c0b00c10511480140720702a003110350001070307910404440d02942e1018503258454a946030406800f4076500c02c0c014240540c004010301440703200301c0e94044034001c50417074410361282c903c5410120700c08c4c01119000b010401c10700b510f40c01c0000c3d150602d14030610450702c41103403400009084401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 300687068 1250 300685818 300685823
    0x40920031207030503040c0510050703270b1c0b03071512020309100e010b03071206090803090a120c031704020a03060c0e0a0807062015040b06040f110d150f03 70
    0x8005c4240003c0c8284060054003811050312000050400b08c440689103001c1c20000604221191860041104503018010046c0c003209420100217a110002c4407007980022001c0300306070b080400c1a058055550003201500d0f04050040d0005038109242081408581c0c4c01c50020f115840d45648030340e829078402944a030121001034a007054288032004152268a012216039038100a0110800d0342d02051500440c0e00c01087d1504410b0940780c8203018001540000c2c000c81400b0040110505012640c0f01c4020300c01d041e9290b000e440d6000a68281340c003030402400241100c140704c401c0d5541d002175150402c0c002040500407a03036940e2854255900c0800ca640001d41d03005041c040c07401c00000c2900035141410107041d0351418090000c20b5904882c200e40d244d0500309451460245040c440590046a00d5040c14110f20f401d0031f1404000c2c1c425180203001e249014a6020041c250380b00f176920510015030404d24080e20b007a10701d0050590304142401c00819041c00042030302002103200000e61 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 300688318 1250 300687068 300687077
    0x1401020f0f03093a020d0f11010609060b03070f090305060f0c070c060e01110102040311040c0c061a09090d090303050309030c190210140904021309020a1d04092003120703 75
    0xa6800c0b60580d5640700344c0600700f5544a51001030071103400c10401d40304c06020f45014004a032003041214098619030780014401446d103500820b600d082000110700c551070780d0f118200e21139400d0400b110646850700c0003404a8105d84003241c00c015030b40ca240751708401d00b545858141651501e5004480140d503000c0c802151001c1c1502c0c82c15600900c03010309504007032000714113141c59900d448001700c0b007903000c440c030403580d1701c614011241c00342c0c282451b4150050030402c955041141c00020411920443c1031088071100001640002b001402d194140217030350b242840c56203155825105600050650285400180311611162400f002131a107000d60703d0071410402d9620b401401101d4642c541034000704050a1004402c03103001c3c00499000c407000360303001a0f0f1800041d065100e15001c0760400700581c2c0c000102c10382ca40e58400003000c0307000c0f40d04a8844424001004000c2254107480e030007000c0a40d090a402e101c41440c01540c0300c9240050107940004004040c0600d503940409011000f08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 300689568 1250 300688318 300688393
    0x30507140705090105010c02010c020d031b08040513060303022517030301090e012d020f0d05070905040b0a03030309080d020a2c0a15030b060d091401020f0f0309 71
    0xf0b1504010041c010882030a01401268140d00024290003010602034002c031401080081010300ca03088150304112540e08000c00503481c0d140c0040740c1e03440b0b4400c0358490f1900380c000c016030440700c0c41580d0860313500d50020038180100250701d8200580c261100a102150174000003020512504004014543c01c0c0240d070b60b960500b2420000c035444091004400d038501701c0a16108051040650030455954640107426030b070000640c4064442c0900c50019890049010583c005158000e240604019100c01c2c0029884800340401c40e81d420000642c056001c000400100b8001c1d8040c03074103103010b202e0041c5001d0814100000f41ea01c1500d40d60300007880594080301d0700010312400340181104222040c2c61504580006010008034001e1070510071a48082c00c440c1c4c3d000e0350101109100c040c00704c540740d82e240125100101b100281c00c1d5030944c904115801ca50030180300700c401070344103180c1150a050005000c0042c50704010210710007485543c401e00b1142d882c601c1c07052806004080d00c03070400f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 300690818 1250 300689568 300689579
    0x20a05120112020607020111030c070f031203090302100908040e0c120123040e03090a030c0503012003150a0e0c03101d0a020a0c0b0c03010f0b0f0d090305071407 71
    0x24640142d00100e41a40d03100300110042e13440c40d003100c1002d074091910b5800d4204200b5014114070419a0106c000c0c480c9000000d1000101c407aa007045030b0040d08007542e04001d00c0c9095041e102c15400040058110340b4500c1900388990340080c0c24140038145103428141c9400c640096504240c0d2105819040401c1d0500460898041d46014000e44400b400001e1481c0c09c0012010501986852149440d50054154028104192002e18a00402c00980140d407030901d509410b0240c002d06010754241f108941c1034020104c502e010814011019a20351fa6130380000c607914000c0d648106a104072200d4000074030ba020100b590b80a500c401c91102d6481c00c013119900718202141d400444c1905110807107420088102103000d51217108002c015903200e0121000310340e4840c0d00362000f80206042030030b0100c5a0350001c06907040c0c4141000102c0e5075621002e0004140c041c100156440c110100b085058030102600007103401c6109080c40c81c142030441e992010342511220b803000d0140e2203001308200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 300692068 1250 300690818 300690847
    0x5010503071d0402060d110315040f09030230040b0406090f03030c2018040b01050406030b0118020f0c010b0a050405070c060b0f0409030203030103050f150f0a0f020a05 74
    0x918002141c031041c030602050014860030010303c00380c410440450008035001c04d0303402459120381d00c0503090781d82e0f140441098151080da41a6075002d0351034103242c5001802c0c280b01d2002c05503015001050408180c0307034501c0c00400d403600c03090341441003041d01d0200480b84002500140014200b1a62541c0c01c3c03901c01080c441455020a007028140b0b9410400700b50041c4100c0c4040782c00c40c40034900c03107040d585046400f0040e89540340d0084146620406003c080d0031426000d01e100d0b22038203615907695020403080d58594040a080050f00400400507014618042651000d8ae95009401c2510381c3c08000b00640084181c442075945840450180f4503056500102406045504002504205038010301d42c0ca944280104901da540000e00455a90306400c3c00f0000402071003489501c659140007034403030b0001c0c0720495075481407640a0b0320700c07840810f103403140b04a10b0b0f99005542c1d0307450383e0401c01c0000c05003410060030707510255810303105418001810741001548071b8a960f5180e00741d6000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 300693318 1250 300692068 300692083
    0xf0c060403110c180a0c090803031603050a0605030319020f1902091602071401090504060b1b0a020f210a05070f0611030405040b0a12110a0506090907030507090b0d05010503 76
    0x2445070b1506040116100024484e00350044c100781030006070b401c0300c1901901c4403403d58000008a100100410181c203280c07050040c081c42a83c0e4061245844080b42c4000740e5071940101070345034009000032a840c0000c6c912944070340304244125881a0481038400d800c02400d54a804004468401a41d003942041401c00390040d05903a4040c40640e58031743e00030b454080e14050035101000e1100640d185a1041c942d03400a418000c2c030400007103a4401c11800c1a81c8003807c45080c2c803003101555044140045400300c5415000790241312060344820401480c1c1d01201d40101c00e952180d20b841c24034110401201517a075104500511589040a07000c18000c0c0c500d500001c03c0282804d0705100192010007501c0840f1815140814000041b00010705048019049945840d040c0b901c000180410b0456401c44104244c8141340350a07114070a00625100d00a0140c1d0803c4c0380001081045c0e00c00d0340040c2d0721030098500701c0702c81c4e03803070b4a942d445030350008590800c40c80d1941d00600807460140b0045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 300694568 1250 300693318 300693343
    0x30e03070b01060503060301091a011703040f0608060a0e041209090612020d03020120041e0501170a0e0307050f0d11060c090d0c0306050906060a080c060f0c06040311 73
    0x21400c19a00390749403805401c05008800c1007202c0400030440d280ca0940041ca2400c0e1710031032201102070321019032540c4690034490303101e0580038100b86413803c600c0401203c059600c0c913141d100c446070401805440d2060003034002034100102e02070015102031010300303081c0120b1280141d0b0b840c4140b1802c0c010283c0b006500400c50052a2803002c100007072680810002082c0d054170148840d684508081e40100410f404010043c603100d03084c0228114240e0040085da001c02c2c54002e0502099607141c80c03c900b40307004130350105811050344402e03009540c500c251300040940c40482c1da207848052881c110340010704d0449540d4000d83c0481000071040c41844a074155070b141200c1605460a00c4030b0781c40308040c4c80d0b041000c1c000188032070300b5225030462090440e0411040c00149a403803030f0010041a00312070042c020b01650001c1009440c10085400c1100c00e140b0043c050412054100821540b00040070502441c081101c0c1440d800706100b5188241c0c0240c507007031a0301a074030f607915041001840e0003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 300695818 1250 300694568 300694573
    0xc0c0209010506040605040e150306190608010203070e040e0a0206161e02031f0b220e0d140d0b041503021203030f0112080c01090818120c091909060c030e 68
    0x24080745d540002601c040741c0c074004104596485644540d240b05001e603404c66054000d1a08111440806a83c2007a80800c405020016190303919007071401c074081520380e9400152800f004081500d810740040c801001000d090741c0744040d503580046c0041d4004c41a10b95076501c48503068042c1300801050211041d0785000c4c0d51040390003940060380755140c0300c4a594880c03180e03203444d0a10180a51120300e845002501c2c0b074070000202c2c1e00205541a4a0b1030001d400ba0401450800e42d010221f17061480d004152200c80c0880d02c0c44181a0454100e8054004190381da440a0079190f07842d800785849140c00c003860b00302c445017580140a10044510301c3c00c9420744c0100207001c2c3c20b20f16401480d0446d40ca5144c2c6d9480f40c0b00520f8014141d200e2192501c00035030800c084541482510030060030344141040d0300d050f8006400c1c0c10b01c034424040c5131428190b600041c00050550811001c01c6601080a000c5824222003020800044403002042610300694030803803d04c01540601c1818840c1440200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 300697068 1250 300695818 300695827
    0xa18050d0f140715110c09040f1406010602010218010e10030507030209031c0315030f0b04020114030405150115051c09020a08030a030c050403150b01030b060a030b0306070801360c0c0209010506 85
    0x85687c0c0e000152004203034074003003162403060000030295002c2d8085d146042d56003550751a54028041d4110343c1440c203000d6070b140c540c180300d58054030008030000303805014621106117412055000303005c000c00d1442455002c02081103507a80074009440742015070105407610043d0746800a0855003807902003413030203c0c150400e0011801c0030b040c9102c1035600090910359555944012664001c5034004005017030320210070b100410102040540840e07440641d10b956983e604c0184100325003000c50f0340800710701c0810060907606520100000e440510303110202e2449803d5010440b00001c960007000c1c83c1d0000302e5480701881d03041c090040c3e00c094500d081800c060441d1100101412100082d600c03041e528891303005507900a030418410088010452510384034980c0000e40501000f91559110740504030024141c64060154141a513000b004210325986030390717a2080340c64004007100726024410826285180e490750041441310000c43e601c170b03c10031003d8070610200c11410b1304401c4c80707080c0500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 300698318 1250 300697068 300697093
    0x503100b0c100207030c12050c0f03090105070f0c0b070318050415090f06030b090a0b0a0e1504030912142406010e04020c010603080a18050d0f14071511 67
    0x207400d03404010459030040e030b1100c1c40e1170203603801400d11200070400001024a12041c9030000c000e000f54441d004242c50305c0344069081940c69124001d240c5012400500c01c01020a059100c09139425110b140161580c0352120b45550a070341040c082100080d5001c40b2030100d0202c22802000102002d9070280078034410140d00b040d11141502410f840d80b03640340b200468240194000400035034001500d42c0f482d080002c00c19480b58044101504c001415001141c8100c5061017030000d10a802c1028110118100c01d1000303140c00c010f030003036040001015000c00c40f1100c42018822183c86041903c150300c030504001810884014681d20444011207500c1c0422108469816400718013440d10900341052200007500030300881c21542c12662030400d01000b003090150061088821175150303d840710440c0003041030640c506000b0540c200340440c00721700005902400b21400d861040145642c0e4008079220a8606219503000210000440380300441c0540c008090507041c650749800b0341001c050380b6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 300699568 1250 300698318 300698323
    0x6052706010e131b0b21010b0304170403080c010911031912090b04030c030203061f0501080a02120a0912110c090c0702030303090a0b0c190809010b100503100b0c 71
    0x142201040e001c181d01c07030400c001000c42e5084101d10050103100541d80c450700c00701c0c03003074108500600c0c080c40da07280c00c400c051b0031031a85641201c606000f120301d95503d0b550f41c101030014201802242c03050a100120000e1760842c05081c1410b03100c000050070758014208260426100d01019000343c0200c440c24034400c840c480b20500c0316421812001042000312000c4500000c281d0000d40700500200d004010001c0008a84003101e0003101113944079150181e020000c81010b114889404c8814034081080e54080d903101540680103a500500b0700f0091f5071511130000c000ca03200d6403a01c1d60313019881308104028a41c6000d041e41e51070084c04801403200038030f968042186102c7d04c1414150005141b00b041c000440d200c20368041c1c1500d85074145801c1c01d0340c0e5500c508000300c3d014024200054a4040e03600c041c0e4108040d4800b26581030120580140e902c00d001400100c1c04e9504c4200c080c003107840702c551504160310f084d551300c4c2d0b591521941c013141070322081c0c010008205c0108000c96820500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 300700818 1250 300699568 300699571
    0xb130b1302160f0c1a0304050f03040605160f0c030f050d02030a0203091e0a08100b04020f03041b2c100302030c01120e0d0f0f0207050a1205030706052706010e 70
    0x1003c190501001c0038200380316041199030000c405040d8840c003803c2e80300d01300b20240d802544141c089400c0f00a6404540d0f4480c0514003d032400140244944422110403106101090b406002e0b0100003c100d03444900d5221855001581d01a04001100c01040300c1000b00700b1b2019010701c091030800952601c025160b21640100502c500190344141e040c0c9280100e4098408000610810301696030f204c070146c4850850000740340c80e9203000070300302050403c3d000b143c9a21491480c0c0d81e156a550750b03280543c0b4a924840d2072144410400c02090f8000030092000d0000a40c0d40c8940c07079002400e500d4248510010500440e44803480030030001038500042d074000e4030000342030000e41619007041d0701c00140400d0358804814401c06000a80c081d8005c1804681038400c2e42e034010b881100c0b403a0580e030340c2c503442c881d05030000b04c1c4600c10800800d000651401c001c0c82041a68a00b001d1512042d040e40c0040e662250380b10001c1c2d0201c208140402c800340380c888283c0700644101d41c03500e004078010050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 300702068 1250 300700818 300700823
    0x30c090a0b030106094701020106080f01050f010f080d0318050f060a0c05040e0a02030c0d0204060e0906040207051b06040e16081e0a0207080c0a05070e0109060b0f09040b130b130216 80
    0x10a4a0f06c1c446078002e4001c0c2015108400c00c5440c1030498010250107441e041d0340e1a1581d60b000000030480c000d60704225410703280104018440110800401c03030003810910007480e0140c40e01d0b0112000101d0a1000741405a180302c010030890805200d41d600b1150340784541402c1c8031040008002c42c080c80342c540d9a200d08031100041c1c0b070303a40302947c80145100e06461452100d1000a0224806800c1401011340340801c0c2c803420483c0c0e40c0c210500c0100d00c6400030182556200101800500711030300d02d80d041004024248a041a646211080c0c43d000f058503410800d90b036180126210a0788400282d80c08180c00541025103044c2c080500d40c17221010384190600c5400049600901c1740e940106c411801500d0200c030041c05003410b0040d04d51442d0b0013403050b19031800c2c0000400c2026805094140c03200c8101c003e01c2e01c594614400055030021094540007a1501785025031035030360b103508111100340e40c01c000c04c4c000c1e070740000c101c10f1000300c5440c86891441400342c55403561600f1403034000c4a6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 300703318 1250 300702068 300702191
    0x3030b030309130f14090601030302010c0c05060a0905160b040806160801060c030c0807050c0301141006080a060e0711150115120e1903021605030c090a0b03010609 72
    0x100b142c1c0b0003001900110100b50a112081c05c18000314903000551141203d0185e4002c00491200100803110302c414558040d001e82e110502081800d040c96100c8211540700701b003120aa0701002d482014182c403290b0200764103140100f41085082d0b030901c07066501c01d1184c0c0e40200007210200780940381c2c9030103002d84410000e824000104160082c042480c0854201089503116603152415903551000440d000f80a03508100211a2022518000c20b01869803180c032038030300c142000d400700d410b104020114440346440f480000742407039041452500403440b030f540700c2d01410ba00030f0181d4030f045070100390308411100c41c1004100300d1420400003144400c4618011000c83d426503003400c040c3c807145c80c4004650007501d41c0d01801f40a8541103c942074800c2c1c00b51101e103408031803038046900c244d1007810781503045007092a01510302585059402620454002480840100400d0848810360080f036280c0b561110344403d000900c12000c48403200501e0700040ca1001004106503035250605a00c5258 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 300704568 1250 300703318 300703331
    0x1e0307081f0513020c011503120c020102100e06180607080112080c010c0f0e030604050c121513061b0e010e22020403170a0e01050a2a03030b03030913 66
    0x503100034070820002c0000400e46849007203d0401d07000294000c4140460662800c0186500d070701090b00c0620840b82c104450303008184002106440701c00744118101c0c11030042046208512005110b40036407032070024002c2945191002d00c0101100d81002e0780e821513440070040140e0f00d640311440605481c14045e0001c101e444520701a8568001e00e8545c100c5942008801c0310b140354810b80f517034003400140d030382c4400c1c2030f82c400141500d41c0016140070301960405e01c848101c0d1304100000b2034101c0355410882d00f41303100c3d40000141001041d01d100c500700c0d014007820018002c1c2402441c030303000150002c008004443d000b004d4a404a50304c1c4450600c04c14615580065036081c2001410100f030b600068680030110044a000798030500085490305c04401e1f50028060000303090300d10484468482c020146106001540c01d5005902910200101010b1611004101800b0014000151900d2a950302047d00d000380a03207908101c0e041c0203034400d2144403001e984411064904440a800002d881e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 300705818 1250 300704568 300704611
    0x32d0403030b12011a13110d02160c06030c020c040501080a0f02130c030b151e0319020c0a050c1c06020c0f0706050a0e0d080409050a060510051e030708 67
    0x411010310f010703001546008481402488080000188104102c495032000607184100708210782c00c1c0d01103e01d06200a200c10244056940d00610b10b00c8400402000c03014160b80e41d0000c078001070f4001e10001307038840301d5802c0010780401c4011440304045805104a42c14a00201d654958803c40501100204000b2a055496194001c030141c10464400d1102c0d00c15100040c001c1c0c100640300c0e5005d1462512b290101000803c261140407807021030302c03105c0d030f03080b003910a0640d0000f0f481744585403440200f24081c2c01d03443c030007844146e2044020740084905801d005007032044448495006417140344980541c5260002c103c4036581e448000144c03140e4001c48114640080c100b0340700742501ca02900450300c940c00c08003501c6091129501d000080d2003080c144907400140355402006050240f005010300313034032900802e500c86864079000910030b980d0300c0010307003e04c0c0b59140400859400140f28502c01400c181e00b141e010310f01601545142465100201a01401040880140108200d0510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 300707068 1250 300705818 300705829
    0xd200a030b0d061d070e010b040e070207080a150e060606090613050301050403090312140f0d1803080a0e1c0f021c08070f02010c020a02040203070210020c0102032d0403030b 76
    0xd041ea0402e004011411391341126040814403100990103e1240316000690051813080860581d205641158100780c64596015404a0040c01e0202940161100030444440c104020340160f80100700d403d08c1d94203c0d002c6101140c05414003490b440d046036042246a85640046960b04170007600c900d5a0741b0100c200302801a41c076038014643c554241782c180024180c0c40648030781924042c92083c91a030903198810b403114041d1100d00c2d900350300c0c00d00450303400030396900c058004200200008070b0072003004034100421249084044000c24556402c2c0a442e44040c03051895030a81100208180810480a81401d412052490f0f042101e00000400118401d100100303003400100700650140c1001c0301c002d001340e10100d5415000072901107413000b069105000d0540c50b40d84507000351080119540030311019600040c0301302c003544941a280e1454900714402003c8100e4800c0005840c2c1c01d1004240110a0880b40d95115401c403801c20751404003404064190804d926007400036840340613002040307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 300708318 1250 300707068 300707089
    0x181f06030204090b06040b0907090b07030c150608160e010b030603120309011a0411030f0703020c07090207020a0b040515280e03010c02030c0d03051003170d200a030b 73
    0xb034216003010210300420004800103801600200e90a0040c0c1c403413401031100003141104c00b0350004003025000c0010404400043c1a864003030310b000742c100001e07a00c9506070400410fa00e1550705030744e5a010403502c0c00a1115034594030f078403614650310070300e8150814104101801800c05003280040030800950b000c01002034102d510a8605450349007040140d0b0080c00c0080701540c0c080c94024454107a89014030440b0703041003982c4417840c103589031a1990503904000402182c149a402c010b80914a42d040246000808000401580c0d0345a18030501c4140e006680c02403040c448184400c1c000b654680c204281524000d24a00fa01c0f02452140786114268144603150914941000205c400b98000040104883c1c184c0080c810307185148401c980d41d1048441000041c0c02040c015103809101e50002608842c0b014044a01c454513521404004075800680c1d0138011000500a9046502070003121f1a5041340ca4030003480840240200700b891040804081c105aa40c07131111010b6030303c080700e54 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 300709568 1250 300708318 300708323
    0x60905060f04090603030203031b040e0c1804060b0a02010e162706030803092a0409020121050f1536090610090b0d060513170909181f0603 61
    0x4d1001940e2030401070f4690b8000c0d158038600c1004010444103416148040b94101c4000c04140310700e80d0765280a00400c0d80007806e041072145d40640032060107039a14028840581040c110081c0d8607074031584007a084514104200c41c00b9000101d0200003c1346510152007100c5225410410041052103800ca24001144000b10028502100801806007002c0a148075448503800c9a01c2d15407400007008983c1091051010364400000e025201400c045c1c0106030941c0c4181000440b03030b43c201d0f01c21482c0101e03203100c00c41d009a0318420844812600700c4125004a031503100c2043c1c0c041100003150391540001d80149400c04030b500ca0362800040a081e400203031001e25401546d90400700b002540b01c1c4015500081d0380d020b00180494220748a1094940c445d00080c11011102400d54415024090080210016890f11404031000c1903030030307103011082400c900079540c2d1002c242c0200404188060692816900d00000400c0311f1880010580e1400040d42920340d11018032028103030142c200ca8100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 300710818 1250 300709568 300709571
    0x50a05070b10030204180c0302060d0f0617011515080c0c0f010903020c06180d0203031905070c0f080d0e03070b0a0e0f0d12112404050c0406060905060f0409 69
    0x2002012003001510b0002c0d82d01c203d9041c010000e882407002604c6492150103080e240c0b070b11008000510303081c4001c0c54500c12005010a075051020024002c81d078103603100c5111140d0300071007100d0440c1c013807141c0728070101d481c115028000d0400582825100d071011500091003030220105000f44251002e8405400d090802c0f00d110054070301140b4080d008542045002d48121414403500d45070510039958504504003a1040321261101001800c0184960698241c04104207103480c8a138440c0e8004e9440c022911410340e035440034941810380882c0392380000001000d0000c02e03c80140042241d29070905540780c141038203641200028203042ea030b5441045040c0c4001207d0748002d40010394400342c100c00312507580b01200c14ad018401400184140200a124001d04000c10240a418a000080e132110100d403001c3d0060605000031020180b040076010b5051001c200c100030741007040785122081642d080c4011460b191010742550220f001d61403040001203030320102201280141c4001f840306010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 300712068 1250 300710818 300710821
    0x180b0a030609141b010c03050d0f1d1204031e140607031d03031003020909070e01030b0405060a1104051005190819060303020c04050712050f070e01091203050a05070b 73
    0x1004401115070001443d200d000e4103800b241507103001c001681c00c401041e100c4250000031641d0440d0350b54011400e1a013001e5880f01c03402c00c03c40741071040c002d1700f1002240005c0341d0542d40709024505120b0324031080248104110601c0043d411510700d242c0b42e855041c007144860041d00d0084049005a0b0b915000c038400e01042201081e415040314611126850140f91400b01414182d0b8a0f81310459400f00c0008a40307200704018200040c401c4d40c00105641640c001507100c101280c04e0600c207074815103141980b4410700040c02402d0010f19040000c01c6010040d920b401030103962180100c0c07142910032140c00f035441e24074900900844034004222048007504140701000500004001d81d100c007a005000080107c03400c0c03c078481c01c0c05072030b010340080484001260800c030203080001c014804018000c0c01c0304040460030300520f03029402d520000b072418a4030704002040c0d805e10703140b6a070403c50701c0c003410032104c080e40c21180e440ca901450050b680302c080c4c010640701d900c5082002000025402d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 300713318 1250 300712068 300712073
    0x905220903050a030b040605150721090905130b0a0b0102010209151e070c090507051903090506070c080301030803130c0e0f07031b08151005030f090106180b0a030609 73
    0xc01c0d03d000951020014010031005120484805005207500807049031100c2c40d00382440c40180606034491344059001f0700c500c0c0b0611002c4940306602ca00807441d80c241c14010a0218043c80780d006032040014401c2d800c80c8d88400b01e440c03002074440000c2c1d80d500c0302800d185034030030f4040700c800e60070180c880d0840340b96003030005c00399911500c0c0028002c1c54a095000c0e50f03061340401c44100e00c0e04420004415401d01c6c5008006010160085050100c100921183d40401c3c0100b032880c0c2e2051b031000145000355041443c14240010240c86c10044030807040e41c001030000055030b040d0b035041020640c8039900d0000d20380c00c403203244601925202c04c8480004008550107405440b4881401d41c2030320a4860308820307419581c0f0310011405040008800040d40d03841045026807040f444c50311080c0404040f8040b80201001c4076115001400010800c00c11000020f4a5900800d40350004c20a0514020441e1840000299058010751301c0c0d10304c601c09580c405010101450b0004402c102c0c05101d032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 300714568 1250 300713318 300713327
    0x60102031c0e0d1d060301050907030b1c0803070906020303062b1406010f060302190806032a010e1c02060307030905011509051608180f39010905220903 67
    0x130000101012030400440780a42011010349040341d00141c241d48181e15000401e4000d0f10b50080c00c2c1303801c4403c110298965410203825050024029505147d036418401001828108030b03800c14000c0d0750040007400090b40b40c40d920080c1264980b245940c010410200344a5078410242010381104e11001240c0c2c401080401c00604031212800d031020303541e0707075014190103030b0052451207600d9416079591888400e0152582030b1b0322080007401d81e09005c01d45a40704000c001e015080d80944000b500c08c0d1a41960014003401d4080c1080b104a0b0503804041c40800e804820200021301540300400405e034081c2c06900140c0c03050358000b009200701102c0600b43c2c0c48015080c8180070300241413074003046518804c0030058024078011b9407a881030350b840803d4a00303901c5807254441014403030b8412001c0304c802d052005041c421051821103810b6805100a03400c04020900c0d0032100c42001540c0340d5450384c2244418003102e0055078400490700010000c84807400403c1d80300402d040c01d1162403010181e01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 300715818 1250 300714568 300714587
    0x111c240b1005040e1e04121101050f100806010b07060e0307050a030e09010b0306030a0201080c091908061006050909040312020705060613090503030609060f100c02100305060102031c0e0d 82
    0x140901150250360303800d41d03194518240c1454004104410001c01d001c280f900c160448004002d04202c48c5229000c50b22900b103400440b0f60186200c110800c1c084d0103100000c0031001445060000c00480d41000c1065510b403141000081c0b1107a0744510f07105040c2014000d0ba5035040c1c02005480804405081c09403e096003030000c203100705182400400c18018100a4a00401d0050000c000c0000954019503120310040c1035058028802e00505400d50340b03681180380710840c55401d0120702403030700d280140703090380103403581500400c080800d201307069116042c3c3d1003d581c201e8440071252a241415560014032088100740e65000003001400d0080002e0424003440c004d580010100c4141e039020f408442a44170028625042000030605510308000056000400240b4031074441c08004002280f031172881c003e8001180484090340c4c151320340340c07202d080705260a04080c8a603241460000303441388180f450780a0013122060012801960691041009820450469006074020030000e410940d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 300717068 1250 300715818 300715829
    0x301030b010815090a0f0206090607080715020a0f2304080c0316060215040206130f080111090a0501050a0915031505030106060e0d050a0609111c240b100504 69
    0xe50001454048403c00210348a55001ea003c1c1100c5405681c0d211494403000b2405e0745d0120046c0a20f5145d80e840c2070003002034901c0b4000b010f86d00e0b5910b1400400d4160418600401e036441400b4a00340590810426070402e1003c0c500540601041000b900002d001c6200d6414400004100841c4204001901b04585c07402181158803000c0002c2e0b0341c228903e1540210001a040030041129107080d00c11070541092004100f142408104a14039034681d80e958402c580403080d100080150520038442c582c118820000424500b041361408030341c400401d4402e060420100040982c140740c400c10845000e460800881d1000300e24400e0010080c0c0464500788110070110440007840d072905114940c110751450300d0b20000700036503c0401c80710b104020320903502409040c1500001641c18451260000d00c5000c0c12600d000d0300c0e0f0103100d400042000d4841c2074000261118000c540e01c07130340b41c1106580300b41e400c050144000700700c800540583c4000316006104640114280d40e004400f4106440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 300718318 1250 300717068 300717073
    0xa17070305040b191107180c0e120d0f050f0f0a0e040509011a0d050607230a05040e0105040902010917010f1103011d100506130b27010f120914030301030b0108 70
    0x2103d03205c809441d0302180c0704814903a4200365011010048640040d2074030150342c10a00b2090312041c01090407440740b0642c0e4621608070114445079903030000068503812106140c0b550034055410f01c440a6445030010328140d5802c0821401107143c030403414500103cad4050010b010b24203242440c00d02800128580c901c6a030886480303c0d030903080c0102d80a841c1c4e42c11100a025a07103880c0c900356040700fa03504051440da4141401c951854040b00001c05541c1c2142d40d8070380d13807986003040074441e0300310681000d0f100b9400d0411400150383d100816030180c601c24040010340c84201c50915006200ea1078000801a0900042045104070040038504172070034031007512a4601200c46001304084201c03800707604904003660034001070811002901c11240000e100901254480700114100d4008130002d55504102c1c151014021240740f8001381000d000703003000e10201c003003000c001c3c08046070b400c5101100e40e9680100c1d42403101d230444044404040d0002c2d00d68030350b16428082581c103c2409a00d401c3e2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 300719424 1106 300718318 300718337
    0xd12050c04050d051506040227040213091a010201270c03060e160506130e04020301060e0106020610121101050c15160e030a17070305040b19 62
    0x140510002d00c802c02036120800d0780d203800242487e0281e4010722850340d400d4034030390724282d05a100c0c10324a1021083c41001c10000d0188101d00003107998a20030025500c04164040111603040940b10740000c01100016800d0301d503060348006902d40140103100601c2030140c0030009061148002011155a07030f240e5a06581708428a003440d80c02c440b1041084446400000c0c009000c251003850410300c200d01442102c5040307201d6900e00041e6400024110342e000c0d4450b001405a5407203145065031542d01c000d54405085580d6280000541c4011490072040d18072000e50039407001443e0960704100340115140c1e08888180e500c580720314100a080241da01c00c809124940d000c0d940c041d1000d8540c0024030166000c0005402504910f6241c070208414180507202e010035451525500d2100e4541102d40f440b0740da02143c0c0310000803403030048401040c0c044009150b942c1e82c032220030 = true := by decide +kernel

theorem cover : BRFrame.Cov 300539568 300719424 := by
  have h0 := BRFrame.cov_init 300539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 300539568 ≤ n) (h2 : n < 300719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
