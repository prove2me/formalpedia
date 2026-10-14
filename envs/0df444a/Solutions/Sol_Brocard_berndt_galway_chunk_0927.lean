-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0927
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:00:19.623132+00:00
-- url     : https://prove2.me/submissions/63b87b3d-985d-4850-b95c-30f11ec99a2c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 166546762 ≤ n < 166726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 166548012 1250 166546762 166546801
    0xa03061d0a050c0c01020c1506030106030b1909151e0b0607060b060903030408030d06090501060c0b0406060902030c3f10080307030504030501060510050a200106060c0605 75
    0x102100c0e103441d4041d00d400540001040321a083c601040141c41d000400d10007013207000b00d550040d180401820600381e0000c01c000c0c1c0440d10981c103200c0188081518101e07190f07003000d00618215008408210580003405a021000c2d1085e00b0315407000b0046031103608841d66224190911050600c2881b5440c0c08039001d2104c0550000d1040c0103010014002d80c1c40440c01103801454103040011400000e07203981e125800c1002e05802c0441c141c48100342c240100005001903d00038800341d814403600510344000040302918020121011605204142d07004d44042c02c000310081d5034034074101d0043d42c940d522400015446400600184900702c0c59071800940200011340d105003440c060030641440c0ca00e010305072050403001c241c8002480d260420040060754880d4462688032461410a02d00310340705031344005c3c0907025270a02c608415a0050031103902d00340604254420103900e030000703a1480600884904d1562804502246c031a80100e0341e405040d01c01c0100b882255520740307060071103015403003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 166549262 1250 166548012 166548059
    0x18030a020a0608152b111302090a0902071101050307050903060103080c0d090501020c040c0215010f0e10050f01051810050c0c060f07020105070503160b0115030902010c03260c0a0306 80
    0x511817801c01403c1080d465240900e450200d001035810016404120034090001c09617400140441d0600300315010070000d00c1608421420314400b1340b942d000502c12032020a040180020010706454040c02c180d070300500025007250600c1d0384900c2c104040c0d81c000281c0c100148214111141c0706442681d005041da18182d02800040000320140005004c450301100d0960103580d0900c03d90f15005131800d402001010030f040e5102c0d181c50003402c03404c84050080264907800d080148640d41341d00324074418a0b030342072038201c0d540d00c41c288044c400215030051055000c041c1440f0409820341c06800303400020129000e407000a446981007140d20320811001a880006c14007850b005903020b040070300401ca006400b52844c2103012814224000030341e417400c4541c5581030005000a1188440e0b2002003182400c00700100405500003800050070080000d0802c000c0d0740300c04081315002c05407aa001070a0308001c84d09d80c1041d1045600a401000201c00040e280c00000036014824603103007803240640740c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 166550512 1250 166549262 166549309
    0x50102040617100e070903081c0e060c0f2a010b0f0d020f040c02030c0f0a0302060c03010e1302030c1002060105030d020c3703060c120506030318030a020a060815 71
    0x10280d403844c4c1500600d04000d2101405c400004034540d07030001c0280c3c011f01400c06c140000141891001c45060301d10101190b48250f003004010000c0c0c01c216200c003011458035588440001311809070000080420361305075a60000d0261050405400503480307c142201d44001c0117500a041c4480782548400180d4024080c85a8102500742a030140700690304520540340741c100c00e030510503e03092030b1200f2143c49510031450901495070601c1101d400034002140306103507501d007940c40240e161002d09940c034040107120b4000304641c0c007001003003440000540203d034006581080691100803d202d903034041d0240590701c4503590b201007070b446403101000740510007200d040740f800c4800f1105011001c100d00d1580c43c00769500c0040c4203550b4011403040c00c0c0421a20000103008001803812401082040d0400d018000107580120a4800c0a0020b250550300407455200082c5415002d500180d04030003d1140440c00d07239800b241c19841045485a0040c544552405112203000070308900d01c40722240 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 166551762 1250 166550512 166550519
    0x140f0c010503040f02150a0207080c060301030303020904151707080607050f03131704081005100501120f0204030c0e010b0309030702011b120305190204030206090f0a1205010204061710 81
    0xd5409507070001e00031800c0e00c43d4906a6800b1850280c0d41b10445c03140755002244100c444c2e94104a060058030340000900940c1045101048140c00180402000e045c0c020405440984031039000050410000c603458203995a11010810300703005214440456004600b0f0100c0d2611000400900171042661102c0c5440050103c0d039a15400141144c0c2c814064007000d4008640704489500b81c2c08100500142e4552a01d0185498140043d030350141755400e000411107090890116142211403c1c289494580c0900701e070342c002003c85e807100e42c20251010501009000701d1351461000d03103490411050f03c41e43c80755000c0a01e13000444000d4050341c0704010340750040d482501c515140c500748480003d130740b00c926940c42001d804060b0f405000030355a0701c10003042e0500c0c042e5070065014851411881d042c1580c002c60050301c501660070b4001e241c280040c100130345440e10410300030001448003403024440c900e0480e000c0d5115205050024115600d858a00c885201500d40100411810300310120314 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 166553012 1250 166551762 166551767
    0x408070e1003031b0c030317180a12090b070609021203180d02130c020c01081609030b0c130909032a0b0c19020106030213110406030504111c140f0c01 66
    0x58404200f11250940e132136900143d04030982d035010314402c0d210510020a01425001c030310b40c3c001c0c21496113030b84180c811030420b01c0100b500c49083d41c00900e56060300d8400c2400f03a548054030742c0b12400b00400014004240106684a9426184210745c8041c4200d02c0c141115035070b010740c80c00b180040009204011541c580343c2d01d4036407102d02c0030305560400640040c100084540b04103100000d40c100d05000009581c0c40b1002c540c5c0215800c0164000820207140244004010702006007400c0c00070020a01207060b95007030300d000c81070111840c0c141f2521015960301400303206004401058940d2070703d400740f028500644200b261070108210582c002616159052036014100604501d400c114440d100d4101481c03814001403150000315203e80fa52042c000d95903000700c0e01e68105494060b40b40e5000806a0407079089584d00e2901103515225401d08043c0c0020b40d800040d44210f1515410799941141c0d1010107980340a69403c28000c180c94489940703442c00c440040c0040d4200b080030020b40d60 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 166554262 1250 166553012 166553027
    0xb0409090303090b0c07110603010b090d0516030c060e090402060d0207030c02060c3306010f050d060f08160806010603090c0308030c0309120403050c060a0512010b0408070e100303 79
    0x1d0280c07402060414203521844080384094440292030840020700501341300440310100b00310403065413424a5585400e00380540f5020742040e03e841000b58200000612070700300034200c1a8a260100070f0799195883c0b6021414400700e206070000703e17000c4888850646072103440c0d00d101343d0b005441e0910748118460900300952000c00d044007800405a2074101503110381c3c0103008502e40d4034000b411006484001d01100c90715120b40410310001100e1307003a0b045070701301403010b0f00f08100f03082540d94912041c2060b02d072406408000e02813146002400220358480d10100d00440e0600c0041d2084034070905081000d80d100e9024030041c82e0b00c070700300422031140700703500c0440302502441d80f919030f00d070300d84e5901c08403a07005079010301c100c00011082c486240000d0015070b176a426500803040c50030386599241511203010f443c005104001c007107110701d007030fa01074001c41d5101280b6450070f500c15038598208250f04c0c0c002c0e0144c600d00388a480741c0440c00c07649140191780580c0c0d0f40301040004a156550445100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 166555512 1250 166554262 166554281
    0x50a02040905030d0507200c1302070510090c0e010503150103170f0708090f190e06060d0e011a011403190e0303040302031e07120c02011e020c0301150b0409 69
    0x344410000f0b4419a4400e1041501030303101b03650303191401d46071108881e0002c5081002c2d851540c016010300805d943d40c445082c010042000303c0581c82c0d07081030030690705141c4990200144203003400394100400c10880751002c1507641e0303441c0140e1143d8960017490b580b04007690f00e0000414401c03005002248031540700b980c42600340110360b4580900260340760300c6038000700002c403403480d004103000441d490200012800010207907140340c2c1c0302c00894085000d82c0068801c2100c00b81490001c0750301e940f0344200700d40b0b50380b0340040c1c280b01b40c11169040350700030030300e400011801c1c1d0001c8092600e290b00c1441f64010102c86118a18119210841030040c8114032205009909030f0350460400c0040c01840a10300c81c5000390051030700c940e0114025021440740c00c140210f0414208190400902d0304607590043d00d0b52850302c1110000c16200503601c02c02a0030309101820701d901d484c200119800078041c000402c040d002440001c1c54440d045e030903400140200000c40d50207010510042c40c1e0f503030160028 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 166556762 1250 166555512 166555523
    0x206030403120b06071406090c01020304061803020a03290601050405010809030c061609050d03050f1e0c0d1107030c120501091502071b030b18030403020a06020105090d030603050a020409 82
    0x200030b4480008113141d1140070100e82d603c3c0c040034610301c00c280c2803200ea80d005c0c0c1030320041c1c1000907866000070345a11490260100b444070140403a03090400100a807009194040c1982c0a89900c03400c0000081a510802c0b81801d14482c0da0311000c1203e010555005040c1a1500e0f810541080c0040d42c03c0702c002020320302d8034801401a11004002005154040c2c60759401c801501d04580030000c0503036865030800c0e4007803548001c1d11130029900c04101c03042900c00c200c0498446000030701400700145041d482854a000100b0440c2c0c904201146014030790f10107854495040e0103c0d543d45483e00b209100c094140c00b420042009031014042811800f184910000120700840e40d07a0440e03803c001c1c400e030440b623960100d08407040000650401e000c80e811001d50403d40fa01e1a6222400800002c100c8a45045800840403c499040090758095076005280c0300900b0f8403510300071b000340350440b40449644140d4170980c610783c0c001e105a0080e04d4005026022208058007071001808818004441 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 166558012 1250 166556762 166556771
    0x510050109050d05210309070b120c031302030a1202010b0f03070620010204030308060a080604050d0f1101110901080c03160f050904050702070303090b0f04090b0402040503100609060e04020603040312 88
    0x101c02c5c0c42d0700f044400b0314070342500036522400c0001a50346401b026030011005034008008e410b040d544040000c55001e0035003498a40c0c0e90742c40340114004041c1075a0004c0d058030514084000308000c60b090144814000d60080100c1d0454030104107500c0c00d074404940d010f0b0042e110070b001041c1f1581e644078000c0c54400e400e021101100360304500f20b0f44154800d400091024052110710318000891500404501005001c5400e0585400d41c4421000b030a1800b03210072a1008000300d0301403500e072600010604020090020034000b0005c45030f1245504500003000d03400091550840d1a0980380030f603c0e89480b1003480792410000f1b803101300012403400c041c00018481c110742a640e0f030041500c600100d90240014501d140342c0508500340325080300140f40c5013404032400010203403040e03908881a01c0c201140800608010900030310468001c550180034002c1001c03030540c20b91700181e0407214481c0040086541e00c285003540d502041d100254058402c0020a000c13034841d4440481000300010000b0303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 166559262 1250 166558012 166558033
    0xb1e1306030f08070c0617160e10050408120a050d020306130c020c19060c02091305120301080c10090e04170d1e054c0503010510050109050d05 63
    0x1042c15000c0c03002c480004001511200f04681031a90b000108040c0c00e14251020a100210300740e44001000e00e0310705070701c02c1c20b40d0740c0962140503800201031000c0d10060014280c170400606940c4580100078451050159248940100c00201c44002d501540d55074148070010340950301950000c0c18981d400a0500f11502541480388070744800080035800901d0054001c03c2400710519620408000306101c00104002d51500800300d0381c0c0103981111101030310755403550410000c403c0040040c142c0d1040c2644c0c0c030000d0710107100440c1610440803c40c2c031030300c80c0382c41003010340224050104002a03100c1d0b020030856641d207075047d03080f038031881a43303c50080081c4009a55041010f080c07525a441d1580000c480350094058006801400820702591416900310161710720340c2c42c036020221003a0741a01ea071056070f40c0c51420741031510b8a10508622090b040640558406000300d0303103c1d5207007170302040c0081300e482e0030841141c6043e101c4038442c41c544000c105c0d494040c880192114002c0b000c854 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 166560512 1250 166559262 166559273
    0x61207020309150703020607231b0303010609050111070b1602040e06070e010e03030909060f0117011214010506010905010f03060b0706091415040f0f02060307120b1e130603 76
    0x40f207101000d00f001d99114409030500030315000001c2c00c0320062001d90850710b00d035840c140000c503420050714542c550f036070a500c1186680f4000c050b4961041c5010120010505035800f8203141d0480d4405da03125420701c5012907400340c44005601c14031211400410400a98612400c3d2061200e80000d0000507002e200132083c50030050225070b007400244412948403210340e00100c0c108441d0505030000d5085c00441c00c04140c000c00007809107881036404480c100016031007440074100400190380100710a59444907020048032007030004540b40c06140502180d070010504c2043e200b0217050b9039022006190000542e1a84c1589002808041d00c0d0032010801100e0040200211752141e2800600001c20341410314801b402a154106a40c000c40c0e91740101710342d1a15070a8009800c031642c110500ca00e803615a001e50038120b4002e4001c400841004038081d000142a480c80d101d8038000e003d440b05210400c800180000d800a60f010042d2009120034149440041409600240c00064164603034585 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 166561762 1250 166560512 166560529
    0x1052103040e070c0f03031b0203070b01120f02030a0f0204180b040b2a0304060e06010b0a11150403050702090601020c01230c030c03070c060302031b09040b04110c060c09061207020309 81
    0xe07000b0a0704c1d028031442200d0802070751f68048c2214405142000510f545083d1900c2040c801e40411364810306c0d1a00071703c468130445580280d801022940d070080300740303800c008030180d00340160b202d6460100d400500d0841409480c00c0154454002c01c03440d6035941c1c522034805406060a4a500c00070345446d5030b410058040c00785100c11030340e0129200e182500d4407806503221800010240e8010304010480c00a01c541501d4501860b400d01e145142002c072a1035203000d20302e0747c402c1c0902200350280807d240d0008000c00006000f520000002d5481d4001a0f07910282070f0100703800100103034003000c00d240400701c4082d2000040c02c081171400e01c144181506e0740c1c010b100000000d800014883c0101716401e0b95400c02000b20b41030550035031030320320042810614124003104691000041602899039103600004002400030400c2200d07801312841036030141c1100c61805010702c1003c02007540e003a995016034001d00c0f001401503144c050a109817482445001d8002c50943c0300c240444211952001c54 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 166563012 1250 166561762 166561793
    0x105090405010e07080a0519110907120207150525030e030909011706070905030705011202070b04061a01021911030f15252016080601052103040e070c 66
    0x100302151180c14400e060808561240b0316408c000c1000c0d00c00180c80e020300400700c0d10111810754407969008000d40300c20701310500c5085040e2001030680700300302c170080f0300500c0c0c4110385404100d01d40d114a0f5440700d00d1403018042e44030003484200d2160b6030303220b0b4028007000011001941e08008540b800300f0585c95007a007041442040e003241c40a02d2000410010385d00c04400d20302401d8003454000429250091402882c1c10040c0b541450b128520540c0c0496007010b910959010141c90207044c010018034000c0040d5143c89441480c4c0c08143d0700c0001d20500400b040c0d015005100b000f6035994100c945c02946540c1c06002d1041130307804d800001e00000312212108146148245845150350210301c1c0c00c1c4004440a840d183e0008291076400100239005c0204040c200c0c0540c170407484400d103454021521180e840003c050003082c59000807520f0341c12a80144d8401030400b00001c1040c0d005204c181021965500610041143c1003e03a100c0b00c0e000306080c1001d0944950503164203c0451100c070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 166564262 1250 166563012 166563029
    0xb03060f04030e01050a0905010813081611030304050a14030f03070f0317090a03030c021e0f060a0504080f0a090306020307050733050a0213080f0105060d0b0105090405010e07 77
    0x1081000745a000700750540044024179220f4506029240090450300080c000c07a8100280000000d404410781c070551048283c0000704a6245c008600007070f030385100800000c841c000280d1044526a04000041d01c050310b90080c207002c919400c0c2400c202c004024441442d60600c100701482079801002c0c8018240c241c0a10702041d440d4034141000380041d5059107801e000e41c60044100305280b60003040003001c003980351a020800a80300c0b00b040b0300c2d21100070300551116240713600d462100b480015134211500c4110090f036080381e50b071100485c200c440c12100070304440c00420807c0f42c401820340c0206210b95550410050158594841c0f100f00e030421140b01001c07500c0000c0600c1030080072080e40c645610f4010620562107400712040e0041e441c3c0d070646c0241541c03140d000c41c01c00c0c2056010380d00008468603110100c596240d050380d5840e00c1620890105518100121300d01c1e0514003070224413035400002c40401c2e40d00e01418402c613100010400d4581b55611100401503601c00d05c0003000030b05100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 166565512 1250 166564262 166564291
    0x6090c010e0f1c0605100609030b06031606021011030106020604021002010e030708070209090a0203031c060b030403050403200307050904060917030105121b0103050405030c151909020a09020a030b0306 88
    0x11324001c0300f110400f0340b008183e108840c0d8100020307680168607006aa901240e07810840c1c4400000c45e141c04140c4200d070402000184010849941c00143c07035802080b8100d00307101e40ca043c41c11914040c4000e008640051304030f0300c0050050304144032000000b525500c0000384203154031800f1411508000021500790400040c20029072a01b60f40160700600308102030941e213016540001d550303100b0f100c104440102d0305080e50000403001e91001c0020454260101c0e9a89860300d80140316510502045800d040c003601740702510b00c1c84180082140c1000b40081142c1070411080104044000b041223441a841d01c4c0650b0002e030ba001100d85070040a0072083d500e80d41082d0801184001050302c0c041781d54042c402d4584e60b100c1c5107074480301c410400e01380000c00303441c1d6041079070440c440c3c40110307403040c403a00285045a0328540c410701d100d0301034501c0781ca52840b8003103d10015660300f010003070b5004503221130500480c81154001c000462160800044c1e4081442c0071a0030160100c44002580445 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 166566762 1250 166565512 166565569
    0x3070903020f010503060f01110f03030109052a0409020711060a02071410090b070f17180a230310060308040306110f03190207060906050603070806090c010e0f 70
    0x88040b8005000003420014194544280440d2601400600d014100249042c80c3c204451041c82864400f11144083d030f5944d6845683e030101030403003a2000007014450035441940c6800c2000e44000002c07408080c949001e00c0c00030072402a4100110a507041d01d444070398585140d40b01402000c0202140c1c0103003960614000c04003140d4900c2c2c25440e4022161480324200f403c1e807142003801500d80d1007112544444050908802d41e100c0000000d018a46041001039070005103c081c1c449901074290800801b9461400d01c00c0b41c00c04e5124448902c005c030000c0003060042c2c000a410301079409401ca03058030b1680a01c08082d121175070b0081d100010000b5080c010f0040502950350b80300a81e0408518090314a410308840b880010321500765612041c410311030a4200350121042290040f009000344191400c1072002041c0c20781d055403292054141c0001e130407002003125440741c0034174000780103580011401074a0000c1d682ea040369105041014614080e51401000001203650420380070b0803c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 166568012 1250 166566762 166566769
    0x10031a0613091a07140a030e0309150d050c0a080711010b03030f0703030609020403020a030206070309030b250201140703110415030b01020f030f0304020d080c01050a051509100e1b0307090302 84
    0x4003500042c00c10684541411a980303a0070201c1b40d41720001d18001407101e081d040b846080d4055020142d5001e4080c1254040c3c13001c0034405040034220f941820019600d03900000852482180c40f03180204051100083c1d90601035540d08082c0d054400c00440c40e00b1503e070009003160301043d54031030480008140f090501d645803040d04094548150218607282c15a0001032a00740a840024030a040002c0d0707802c1090f10071160700d00250303030042c2072864500300041c401200080d2101d041814201d1000c0c03075413072207105018098804001904401580c3ca41003401c80142c400c2c681c440406020070000000d6140c01500341200c1e0320520740c0d0000d1065a8100020b040c520381700b91a1b00ca0b41d00500c095600c1c9104001141d4205074100d48100f030143c02c91510100302d001c2c00805010f00c1d440c0c0030400c032107148190420ba219100455404220980c414100880d60742d09442c011207000c01c181c0184080081c0d400ca03150018102410301d8201c1301518800805580200da48000251032039004004608 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 166569262 1250 166568012 166568063
    0x609120e0a2409170a110d031d060c03070602040501020105010e04030206150a18141806060609010309021003150905010b0307030504060204080a031710031a061309 72
    0x240d044800d200c0042c608454050401c1c64022030402840d01500001806401064544010f1800e44142503440c0c43c12a2100c0d1107440f0002c0688110110f04070445062824800c540c08040d49500c411041e00c03001198066032404081005804c98820850707110390240c104050310b05584160f40c0981c1d1a8180000203082d074a060380103207410b68010092000098010036070642c0b1501c820500010221640c0c002031148c200b42e4440f1034291500480d17081c4007089c9030800c1c55851440e0041c006581c071502c41c1d101c100cbc050902a66426002040031500c3e51800c0d80003070294207414540451518107030340004414504050380c07540807a58070348030210b02a55844034400201000a002c10071580b51020304801803200030241001c03d555a0700040402c4815416a00580381c0d8a045a0321000549400741c4407080c840b0000d010a100c080029503400c21f2000000d00b81ca80c04080c605225144028000040b500508002d0340b01c44048040c0581c0c0c55940700e40c084490140b521909200120310007081c820 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 166570512 1250 166569262 166569287
    0x501060b03040203031206180705131e0608090111210f07120b010909150e06030f15101e09051608071101060f06092d0b090d060912 58
    0xd680501c2080702580d00482070b91039031000324a007071039103079200d80014411041c4001000c0381011860184184030b54007001034000c5034008025201c10382d464640c2c402c0a9080c0f10001c0000500c4500c1c00d0041034468004a03410130303812000070070100c1c901d01d00e100300c5400543e105003020000e5441402c01c1d09c004482190000f20110000c5210300381440010b040032041c6140e40c40803030f1120030340d805036442455504000e0074089420030598204058085a02001344540541c0001e8940498290f00c0c01041c40d2001c440c0031401011000c0f1403161906080c0e2005001c01010030321400c002956202404c1031403240082640b2180c045420166904202c40d00a8404082c042c402d02c51280c1040d008222141c000e502401c00400100b0380c580c4840c0580002d800c2a41007a100c100000b900e160008120000d0340c09200c06484401341d0b240200b00d10340d004030b1110f40004805041003004005400040500403809000d41030010310079112034003039825800342280d030303010002c5190250541c0495106800d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 166571762 1250 166570512 166570529
    0x140f03131d0f0403050c120d0c0e030a120908030a020a0c090b0d170d0f0606020f0609030909060103020c0102211b0d0b0105041d0103120302030601120c050d06030f050106 75
    0x48215488418100d0300002e040c199090401004901414000d805590320782c02a2411507424500b01d84010429401240304c440701242400c184000c0745014007940e40c0310300c40c080c0082000603002d446202c0d0071001c5080303050078000f1450307001c21100c6090005202e80d041c1174005158582c01441d1400c41c030819a8000c2100030b161101e01200ba940fa54020b0040e03d800c00c20480c4507000d28840f10038284600c80c02000c0081c03030881a0540c0810b543c0001c0c08486154084d200300d90500304480d0340b0760300101c4030703228603410811004140c0d241080c0c0081e0440010f00d401400c1c5100000703180d089a1001c0c4100d459100040034a81c092040307450860340c0f111554003008603005ca0740340c01c02c051f401070300c404540301902d6801145a991207942614000c040107007807034001525046500031407c10a000c280c030456000c10782e05a05600a000b00e900070340040e0340b03507d482c85080e01d01c0001805041010000c109040140409201d43c0d4054a8095030013404000c43c0820301c0d00d480d508403032321a44800d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 166573012 1250 166571762 166571789
    0x2010507090b09030a06150b0409061d04050a030c080714250f0b031302031f0c03021905070f0b0705090f0d020105040506180306010b0c191e140f0313 66
    0x84130307140452030004140e407000c0702051000911881c02907510071508407020b502804540014201c5054010004403821060300c1183d1040e000c42c0c00890352011280504554080005000000d200b54110880c00740100f480780c2c2002480e80c0e48002c2403041d245522800e503c09e1300584424a03040d15009000000848101c44552501c0b982c0900c40303a00b403240c1080c42c0340100c000b894621400d41030301c0d0040d03801001d481307106020040d103010aa0418502050a52804048000040c024030032a2aa0b000d04181c40f00c00350380408d0304883e00d60103528210b0f8a030142103022400200b8241c4514004c800170345415445175446400d202e07820b075850110754401c0014041d00001b503600281200d05940d010340ea480e56518a00034060801c0e07403001344498044c0f0500000081a42d0260050407a8000e08402e03a5660302183c800180d9280e8240000340c11100803d218400c401c1800107091901889040f0f1601030700d5403890002d080401c60114042160000600c0d13070303009811290102c1c09080c0c04038500c203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 166574262 1250 166573012 166573027
    0xe0a0c090c08161d060703030c090b0f04030b0703020d05070801080c180109020705120a050306090604090b0106030e070518060306010e010e0403050a0e030607091701020f070822030302010507090b 86
    0x1411414000d00c81d018003550344d100340b0081d054220354801e00701000e00603542c2d072642450020b006160701240d5000151302c20b1404524003010504503a540304041280506060458860b40c03030341c000181041e000e042e4200030f8824400c1841c001d141c0b1404141d210059190300d0300c1d40c030750304204410140d036100780211407104050300a0301402505440d101100181c4443c44c91170090b05e440444100c0720606000814a0a00c0e40d910100451051000f9280d02206440e010140f000b034598201006000200d040018002180f00c2c2d400311854403102d4088030760095071100403616103010701d080b000b006c1c803007a0100401400c041004a004103011010801158980349059a030200c01a100400308040082d000c08861321603101e209a43c071008080c3d80040c24004d90183c01081c0701d10800300030f02c041841e1400160818429109100040c401c0185840c8013542d4542169010103884080082c0c0002c41241c1250319061400140d880703900005190f0824000141c10b03000564851442040b0420004c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 166575512 1250 166574262 166574281
    0x5030f03120a0e0f2e0c020a06090206040f0806010905091908070201030204030b2a0c030d231e150f121c090609050a06080c0d0e0a0c090c08 62
    0x200da101c807003040001031072203c02c0c40850404132540c168840c24804e0206840c0310960f802d401043d98120110100d2405000d4130300c540680301d40040c050f01581220511101055441d0001036846100600c035a00c1e01e0f4490342500360542a54000d080303d64080d100600401c00d451150355000f081440043c000c900340c01450540c20825640000e04041c00819288116400f940640c0d01450b801700071035010386400c68903480e8000720703d8218405500d0070204000300d09000000c440d0600c8250000e03501e89404010b080c400f0301400c118079240c16185950070021500f82c60140350181e2184104a0400c064001007620201c42c09080000c41c501c000c3c03060241303076a5645020040e90825144103280f000c0301054a41800725821800182c1c10308000c0003c0c070541d1010080003030340c80c15241c22000640340c105000c124002e03801101c02103542803000c202651081006000e0f501c449610118506440303000391410f01c1001c010444069004140038081031b1498014035a000360700d460f01441601e41940038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 166576762 1250 166575512 166575547
    0x22b120f0618140c0c0307060216050607090b0f0a020f0703081b060112020d050f0f330103020f0a0315020405040c0c0b040311010b06040b130b0406020705040507050405130605030f03 80
    0x10004c000800108004003250500c199020f01d600075108544a401c01c10780c00ca206406080c00300c50500400000800e4940078800127400e54081c1041b0b0341c205110941003296030b5104d120380700154802d001007407291200422480c406148a005a5a02c52111100e04c84401c1301d034a103400482e0300078000611071a4070040c4502881d60301200c80042d00c007000c0c10322030f05000d0812880c1116028088810004400001c0c011a483e4040b004181d8029103c0e041d1020903030110307240c0341e031184c0f1410042000d4945510444400350380201142503c2e55070745c0d1582e0200d00b01d43e04980641e03802050400440c50240b05a0400101c641050081d01149942c0c00090141c02000203041c850558032264003008258402d04a85101402240c0c1d5103468103829100b40d00275500b089030a40901401050040e0208240d604490464000341121410a02004080c140091808007000070502002641c0d9a81001c0452010f09550740020540c1c2058141820045201032404403039204002000c21041c01418 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 166578012 1250 166576762 166576771
    0x70809030d0f0c2303030702070311040b0a0b0306010201061512110c0a020909010204180207110a050315150402040b07020a1a18030f030a120c022b120f061814 70
    0xb01c01c4c2882c0b55081c2c1c0550b03407800f41d0307024042480b002c4100f00f8515000540b80003036070301030540c02e007844004030104800e8900c2d100c0c40303c0c0c100407580c504012a80f512405141c00600500001c512661145035046403030098545403c00a894403070000d40c0320f426031140c103035414400d80d2072906d00400020005e99860050800901442c20038000a950302000e42c1694050b1003d101c4465040b0b00c1818071802070b4000c00c42c281c41d2080b001c0b01505161030710b41e01d05402c03100054007034400c42d48210a5640c03210300c01420032500845a68000c07049680d948020000380c210704090b151140841e0040c00f054071804d803c60040256880740d510070725074616003540c000340175000d80c0c4c58100402c10301090070040035407000780442c070022402034102c41d00f00000f00f900c1d071a00c190420a04035070f41d600f00d030f98050714807410075006118040316088510852400da003e242c141040c41003c20802c50a01c1124072144140a9296880005000603075005103001c070560f20f03a1106200801851460780503c0d0710242 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 166579262 1250 166578012 166578023
    0x6050906090a030b2a0301060906080a0e0d0804050d08010803180f04020d1d0616030207021809070609050a30170a26070809070b070809030d0f0c 64
    0x1e168445a5074035203214060743d070000507403016091410428840040c41e152451221035038502c02960211107805030b0b13040720388950340c40588900d842070a59411402400351101152120400c2e02d1640082205035440c0b00b40d40d4030100c0c54501414041d0400c2c1307810740e0b028108440b2900400000308004190b4030404503281900c400c000b01d800000301d07030034012a030903074000d0700201e140b81d103a01641c1d11014009600010142003411103880654562008880011404150340c0c1581c040500c40d40c06810158400340c6100380c100c08030202425002000c8400c000d456002060900c071003a8000003200c020802aa40c0108590078078940f1032014955a045100003001c0980d02c481c95416151114002e030f07000100843c50f44103940d6085c03038551010818801080c1c4180c2d6100340840070106000148608010212083d142c850044880140242c107440d010b00c10040b01090f4405908014080544220f580d80e507113080e10343c145401d0108081c291000d00c81829007030b42c2d0f82a002641180500c1d07206 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 166580512 1250 166579262 166579267
    0x20a080609060607151a0105040609030803060a0902030f220b0408031e0106030b0916050711030c040e06040c050a0305060705030702030f0403030305090714060403260307200706050906 81
    0x410100e10300d0300455034060720112001d40d0000300c1160b26849186c0440d50101464040c544090066505208510130080020070410042010907031184c0034540114004240034449aa50303072407402a60015200100e6640c8150140319001da00140366000210000e03a00c0a1a81503540b0390746845040200060600f032000030020300301e50741d52035a0501070450b5039a9030cc060b584481c80100100281d210060141c074045010508842e00c03600745484602441c3c1d83e8038a04030140d80c03014268500e940741160180304481c41100d032555580100f010102e42c1000070011480d0504005001c04460361000740154450403092010174030100391240e00c03540c0c508000355241c985200480c9075110325803269400d0f440c041008010586d141e003246010302c0d40780e401c03030b058039840c4c0c100109515002103807913500c083c041101f0400108488107c00940c128082c03402c10720b00d90081c03110582d6000f161900c00081601600443e10720410558242d1010030b5401403c0b40703424004007928a21403000701e00d2055501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 166581762 1250 166580512 166580521
    0x12101710020904061a0c060a061203120b030714030106052e090f030b04031d06090f01050d051503070e0601080a1a040903050a022b030504030504080f06070f03020a080609 75
    0x951300031400910018025545a00034003c4403500c58012101c3c0001c14055980400c0c0316505902520094540d40082402070140769a0181c0e00485140522100b940e1110742100c805d950511500c8010108400e10010148038042050708485aa810881c8260701004c2100c00c1003070790446004041143c0c165140e808201e9070015190920319030f00013035400303404403070104c20400340b2503c090180f8400d446800503408907078120308010410b4094150084001e01c0480e40515207130210305801081810b01510348a050101601a564200c1795800c41e490710a00c01031943c01e0800084004007664000700c0c00904148000900340341c00900941001790302c80062080c490700d0001400112a0006c00401c044011494081c0050300001c07075480c098020b41e141d0044110307540c00e03c01c05900d05014090f844040001d0150018680984289d080250a1002003503c2c403007000115000401c15004143ca072400d03503030082106100c041d8940405005010b401c81c601d030490301258100104640f40d6034030307542d03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 166583012 1250 166581762 166581769
    0x1205030315150703020109120804021305270f0f0a0c0b13050402070b01090b0307030f060c0c08070b010f170604060e100f06080c0901061707020a08121017100209 71
    0x6941252994404000030381e0804c050301584a500c002d44141c0521400c1ea1b480700e4155501d00782194042d41000d59401400da00010079401a64070201d84d0007951640701320b89103030035034071200c0045c002031b141e04c00c3d06469081081040101c1c856250400103081c0707040150303918140c42050340f20f15084104041442c4040d25185070101014000107401191034068a040c541180c220a00c50049964a060040c40050401244250940b9004903856515050903561603005140c04403126080040302601100041c4440006000550089a00c203c4c60b50510480b104d2411150380001c4052100d02d0340a1703001800841c0087e489a0440b000060b40354103804080d0030311041240e02c940d100e142c5092010b08640a031b01240540b4903441c00c0310304a406c00c01c20312110300402c1c02408082041b281301c400511143c4501075600c0000ca205a590900e203d40ea4004030360003c082601d0700c00c070200100883d0040c880201c4005160040301083c0a1800da400c96403119494000110000d800003584d07a2242c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 166584262 1250 166583012 166583029
    0x61a150d0b0d061a240702031509100c03020331060e0d031d060f0c0c0d0f02061f050103021b0607020105060310050103240f050106090602071205030315 67
    0x900c0038002c1200d0010b0392401c0303001070072004180350040d1000790900e802800c000640c013221004013041001d80c825455503004050f0030150080380d1510500303850303c5ea0960507a40e15805503024800916030926503011b104140c4e0030100c400350401d1b1041c0100010034200e011456502042c0c207015070003031030700d6000d412031004d81c260740605034909003000b204003143e000481c24030030640c07950104180044141038030f400d0101c18038610301d21380c4031801141910144000e40754100140c00034443c0340200700c1c030b901420001c400c0c000750045000c00348030108481d01881000d910680c640880c082061002c55030844000300d034002c0d141055030100e1450340c0c01c01a894000829242d10040350803a2034031100081c06030804441c00c500a0040c001b2003099455640100e81c1a02e80c40070380300342e00441d481e01c030034410400411042d05554981400c207400b00e5040c442e050281c00150b0310042410b040420103441c0250f154014242907090a0701c40c00800c4c1c0103c00d481c0c00480c41c020002e0b280d1542000180c2c4030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 166585512 1250 166584262 166584281
    0x105040b06122506030b0301020f07060213090906021305030c09010b0c010612121710030305070204090807390b0309160810050c070308060405060316030f061a150d 72
    0x140c0c03400341c1412510f260034100c1e01c122005664188000082001030500340e001d00c030650288110280303c10070005095030091b2091b00a5003404c0180a03503140d80100c1035175420041600e01c141e00042100e0f030003e08084034006084154002c042007000301d40419000700b0144039820000d5030224128442d0002900200000c0000480c00480c05601d41402800058036040041c00700b100050000b030800b032403e0016204034009005582c226140d600c06850302c4d401100101d9110b561601294005240140604400f44c090015100c0108442c00d82010070842c0342c07040c0311480241074940c0d02c05010f01d42580c0503100a508402d85030388514401c40e1500551214145c25003a2810001c80c640d54009604001e40b0241c0b01d052180d81c6800750b040005105034070018000898280024190341050f8200d942c01080c0901141c2d89000101a1101c4240050b0403c40d0442e08044200e001c1c0700641c003580d402807103400f00b454100000c40c0e00040c03030081030754413503040700c1800700f0301c18607a410f19441450381 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 166586762 1250 166585512 166585543
    0x1020a060f0b120f0f1c0c0f080c0a03030c0806030a110a03020d03050d150e0a090c05031b032b08090f060f06040f0b0114090411040915080105040b0612 67
    0x400d810f0071041601e4091010503c03696103d402200c185a220010b607003010528a854044020b20042c0c0e0202c4100420500a1f00c000036004090070008010b40000c044c42503e0702c020380411103d0388ad0090030342d0410088901004006020702405950204410030f200d40d0240c4041400c400350740221300b4004990340702940c407079000d0300c400050541040040504200301481040104442109040020200e0143d510411000b500140900d00c07142d219507d0300d406001000d121985c1d40c0d0001c1c0c900f86000380c4d46c0403000c0003000744806a040c00c0080b000304285103081c00c80b10b00340e009d581041243c42d541c011410088a000400e098641c10b001803c840480c14041e14100e20304810040304210303080e10418000c41c0b0700202c06000140364460840b514005a56200400c0b43c02400390300c0039081494070b50b1384169038040030b8441d10000d070014001004122000305080d000800041c085898070740c040b0800da4104010040003461a40001358044021034050380c44540d0200894a0702c0c0025020008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 166588012 1250 166586762 166586779
    0x30105040507030507080604030504061d0310060f0e0c0d0c0c05060403030605150309120309070f0e040605061807031112071107210807020303071b0503150601020a060f0b 75
    0x107011001c02c100c0156801402140d000780d0703940e60780d0303030307a0380c10880300500014014441880001d100e40b0500e22080c1401d6800791140001000290815010248030781c00c080d5601020010061800300b418028050045000c0a501d0301c4864a00e461242c03400000d243d60350ba02800d280f640c021500d80105540240c200d50b1280b0f402d14000d0300030140c90140f9031154092140e04640da190417002c0300d101303441c40c1d03028240e011400b5801440d10b81003e410401240150f6501281c10380040301744000512000429480301e08060030301c001254009003055000710070254a400c4901c000c03a0303070701d60008058a80054603554001c8050143d0240b42800d650201d01d0310705201c01240e00062604480b50720b40242c95507283e81d00d2004081400880c528450107198a800310046011000078004450001e4142c03032811b580d070f5a8003d0f140e016030410804001c002c020030300590408210154540b41040000030350741c24600c0c0083d680c0c2030703030202c01444281c86141c45425036050b508941c4603840081e001c0e08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 166589262 1250 166588012 166588021
    0x40308160c090b03030702040b0303040b0703020303010e0601030902060403120509040e011d1612060e06100303020106090c05121005130903030f06060e090403030605101d010f1b11030105 82
    0x1002806144050301d4901c00c0080c04105900548514412140010b0085141080560070301c07000e0500c502110b41c0c5404280000600207504030020000e80b813080e4084c690f03c0d030410703144005101001d4900b5041519000ea82c00060300c45100b1201580c2c0c014001094541000d4801c440a10400c0e401c19001410160346242e80d18054019040701e0712682501503d030210503065690790204490350810004144138108062a00d50b010101603034015032012030500e040050540c41c0690580e090a101100b003901002415820704c24800500142e26050000040555000744507014050150710710f08144004500300c511071300e01703060003040090208d80340c008004403048000c1c200a10207402080c101003001302400d9003071140301d040d5802e03a01c40c103106503141418422405c00041048052565440d80411941e40e01c1c0141d040000b40caa6801c18030b034103044141040c121031100c20506105422280d83c0c0000c0e000340080e152078107402c44111840c115030400000441002d2a03440c1c141d4030300070610 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 166590512 1250 166589262 166589287
    0x41401020715060e06150a0c080f07050d020709022a0c030f1006050a030215091201060305070603060b0a0207090c02070f0b041707080606040209040908030a0c0f020111070611040308 80
    0x402258201280c401c070179540c49061083c045020b45010451203420040102018000c0c00218621030107002d030981804417003116860280c0c444203042e034032507100140828065504103d0040a440411015400c0c4000300008821200070070108100811103440407482403d4100304e8000714a40080c1141c0310781c1e02c2091801c0c1c1300c10030543c409030303c1401d1400c0072501d0700f4103210301000c80c0da001d0301e11401c0e202c1c1e0303541801041e01300c485240e0b4000694944118103480034010344024500820103030580500d0901d015040b40d80c3d0398004002420700344401091681c003c49c1807401c44010140c040b92a0b082c840c030480c1010aa908202c0c0c01c030741d10b002e0110319840590080c10030781c0c5e6031315640380c540090b1441040d0b8407481303072261500700e502580005100e4107080d0040e043c000c00251003c285c0ac0c60031380c1e40e44d030705d50400c94051114950365103041c0b00d601d50141041404040a00081101c0014200740c13003100e10a9000141031242c0711045204c100078000129070041d500040065101c51030602030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 166591762 1250 166590512 166590521
    0x1110d1d0301050f0f06010504050109090c140d14060414150307080d020a110a1203050702060d090302010203070e010305100b03090705040207030207032a03060c110d02010b01081608041401020715 86
    0x5c0b00100070500b00040c4555004404940c190f80c016100d0345005860110720402620b0704605900c200020315451082c00022000500710341c1c0454070b80450b03100490181614040d100520803803240b42030070f450003007043c0903089054010307150686014041840c000480d1900c915036101402c5031061541e8692410340c00300d5064200340c440c1001c508499180810813040a680b03019242444101240b2500024010342c000c10141d4405480503007082080104603040b00c0600b035007500540d40000070420303426809403c4010190702428200300908003034520218034422400382e01941c0100001080d00d0800c00c0103c00000c040041081d90f1350300e6503180094541d096440120b812444884010008007030b203a031203140c903040108252002c0c900e15160080644046501c040511011000c0007100c110f080c401e030202903400e40c0010400745c0c40c0030001002403000400c01444a18403244048116a1180700c058009810600b8030001c4070280403490300900c25510024000141224840800100d41c0c11 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 166593012 1250 166591762 166591771
    0x1020c120d080105031b010f1e050307110f03090f0a030209040c060f02010204050603150d06050414120421031407060903120e0706080a0b090a140601110d1d0301050f 73
    0x10342e22010799903403090503614800780141160007011408014000e5110b00410f0800007858135242c84a07221400310200c22088009000c80040e03000000c2045d0250820030681c446040700c03000300760050380c5a08080d01c1e0b0080c841032600c50844030a4285103955103005030b40103143c0003851001241018900300c1005070103840380e0700115142404214856006200362406c40d0b001030f19540c9596148410710802e1100c950080364841003079986000452203030b01c00c841c892803041c4480c1d244880e078420305619041c82044076078092942000300b800f4014941c1990407606980205204954449150035600101d0707582503400f5800002c42e240741071100d00c0c1c1010001d10f0007a102c4150307024a01c006102aa4a040440102603103c0f400170001e0900c5129a00d80c001c07203000001a60005040000c0e0003264240d82e10f6056a4680c0d100d2500200100030a0b03401100034241600030910100382c540c1c44240b0400000706002d1a800d82242c02050781c59040c0d0800c000500030803203880c140c1c482081103035081c1d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 166594262 1250 166593012 166593017
    0x6061103070b0f1305060f04230c060904060305031204050705101b021f0203030a050a06140907020f030703020c0306010f0315110d0c03020307020d18260a0b0a05060a2301020c120d 79
    0x41c0c1d45c56417880c1420003100312720002805807200011002c03e100099104491a42d0425074900f400008038100b4009004030b000c05200c00720b15424117050551911140d07420035403144070072110301070303c6540207880034112848003400440a0417041c000034071615860344c8039000300240c50795480101d50b8044019880356051903404c002646642011000300c1c0d03128000c0b4a18041c02040c003140520380039080e140c0c0903146104551100310404071850071900030220450141c1e20811014800b45828805a40035140e914a54242d0714519160049000000c60013580b0341607a071244400300c1138401003110b1081140031003e00180a094400030b009501c1200c3d100014040c001038074500600c11880880c0c11868480d54040450600b044807948142c5404842c1d07622446c2024800d0703000c2c007800342d425050f02504040d0641d01d40215a81e090304d400411407807090851640602090905d802c1c01c0a0a01c0b6100c20f0b9011510650010303468128610401903011a004503581c01070900084c014150301180c2c4e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 166595512 1250 166594262 166594283
    0x807030b071101060b1803010b0415050406150816020a02060403080c0609060103170a03090c0807030b1f060509010e0d050c030c0114030a0506060403080a0306061103070b0f1305060f04 81
    0x100351107800c80e02c090040200340d1904018902c41c000c0c03140140c03005071b040100006800448a03000404481c2041440c203480d4500820400141c84c0911800c4001c140b80013a62203100c3d40c81d034005101d1940205400d104005842a031212640700b04007030b6a5403070740a050f541d031300c68072410202c00c1500b0105a002c0c25118400004484c2c200104001d0304882d4000d50500449503114550b00d07198004103458410140d5030226080442c2c10074007500e00400c24880903227012400c4d810b15400c1170700010110410a02c0e80800c0c1280c031a038030842d403011a0030901e00700d03481c2c92800004880000300500440da0000d40d03807810310f080c8040800c8540d10080c0032001c480383d0503050f03070056035140c0c03a0210308403507034500b4000100c000d1455081240d119100820043c6040d0b10b81ea110b01e001d8010301e030f0050000765103220500100342c22003542d280c0340d04000c2c000d41c1002800c0d0394000038004000c002403008000f10001c500c020740303803421106640c2e40c4201540c4040c5460310400030350200494040d280f1041d407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 166596762 1250 166595512 166595537
    0x807030c0803120402130228091a0f070303140916050315060f03010e1510060512150303041203020a0204060504020906070611070f050607090b0a120f060807030b07 72
    0x2049541484503140f002c10340760b655408002403200714000e40152507408000e014070041c0450394039140c4202840841c1d40004130030000170850b00380e5270009043e528019020285010081c03041d20399102c0c41c400003581e500c03400d1800720007900c00d01c8440841e1901c25403d109245402040142d40c12207410084000c3e5a91070003003640d5000c981e00b441c5940c0c41130002280c03907030404d05d6103040d07440070140000c40c046a40040c0103241406a40701c40920b04900820b00800d41e8a00401c407000300254901b2506000000b027600721410f0000e05002400b45030f40c6062040e584041c420f503801007082c00d000c0180d820326810041d44890001c90100d1013140b40440220b0a031405109541c4003543c041c252a00b01380c2030b5a149002403141c0032600200344010312460340021070340b8030441c03e0385200b080907168600b84608003400b00403c0707802a030120241846000d0000c0d42c041e405280c07508a904000c07500481d8440a4001007445802c16945800350071808001d0024400556004280d540c0d10781c07011701d86 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 166598012 1250 166596762 166596779
    0x9090c1519051e0a080108060105010914061e0a120501120c05060309010906051005090906070530010b0901021c0518041d010b03010f141303090e010807030c 69
    0xa40421403901c00560080c07060280d02c80e002403c0e120301003c4030b66070031010103e403810b441e812408403800007402080050040f50014024103005181c2070030aa16414148810300c102810540c4000d0301400000c04c8610000f2020501d41031948035441c03000e40c3d07a88428500500d0111107101da4040c07241040000076032007851040c145c0c24690800201410503003040308120460f44041d294052035074a4052140200791b6512480d4041ca903001c41c1070100324a03207400d10a541000400191094005e03030204a4000d400208450f44035003070152440852040340d29000c40301c03282441010072a1040f4001180503280b4800030303c010003090302143e420040390040130414406400115000540c180540c40ca010f106000030070030b1680040c408511144550113044810340c40c42210034450b910f408118400d03040030b01c00c945032100c500c0000e200c2c00e0484008040d21541c080c1500880c0f52400c0d16010a051103085a0800b411441c0d00e21035955a4994900d0395a101901050b50000004940003803c11f2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 166599262 1250 166598012 166598017
    0xf02010b0f060304030311040e1e01050907090308130815011d010f09020307050d0c170a02040e060d02030111120f060a031e030e04110d0e03090109032009090c15 71
    0x70001001c89103150b80b80d6504401030b080000d070b1008412010720012890034440c1c01c890b4454001c1944250012a413030024040c030201c1030340903a018203130358030070b10204550210312242a20341010304150395400e500d000e400c0e8400b25a0080c5e032980240c445c41e104040d00100b190b0304840700450008103011720101240c00c809021712075401e006101100400000c030f550740286074000c0190401d42e0818800075140010b440381090544002b8400000c02d0284c1040c0c00c0a864101042c880c00310b040504040202e0b860580240c03086d4030811a403c2e025045507801d4000c66120a540b071040c5844510500c0404000201036900000e405040400241d60381400d0400d5821684c001c0020144105842038000a07005044e60541c100101002010059107950041e00031740001c1c45035440d40c030281c0d0300c448000c6650891030810b00341c004216a00c00b51380d00c0004031092340d802200c010409103200c40c0701020184d400b280180c2000a100400c024408086020a071012050700c065441382d02c512042c8079240b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 166600512 1250 166599262 166599289
    0x71101050a020607080403020106030b131b05060915090a031a0a023405010509070612020405030601060f0509040c0e1806090c070c0f0b2703030a1d09070f02010b 71
    0x1070b07220f4000260043c0c0308103000d40d0464000d000000324213481c2d444001c1080d50480e4546e51240304403680b0f40420002041c502d01c0d00694440c090011810f040010b4410321031710007060300c101c80100c6403503000c01d00c080444086c2000200440950341c1c1e17a181c41c0c1a0b4101c4c0807e41642000442d00107011903442d4006c4814485c0303594481c10318085000d41c039070354041891002171262566100720b100003030302c244101da006400b100d0081c02e129143c11001070801c000340e0100c4e40300500600082190f5100000d88a0640c2c8081c1000100c8941c80304c41120680900c4107000c2d4000d0a107120310001541150b40c01048060030b80f0500c0c0c0307a04101d0079000018a00b55039581d0001110b400041001c241c203000b42114900c1082125041e44d95140d0100444029400070007405000040088000c0d0141d0f0100da4901c43c41240180440c02d40780000f6128011906140e040c0550080c0108581c1c1c4007403843c1c094030302c1c0280f01e5101c1e8181000014401c426859200d005580380030b405000da40b91017184004507 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 166601762 1250 166600512 166600517
    0x6060f0f021f0f020921070803040e07030c050705190b0604090203060a0527010b03071211010c080d0e060a050109021201120212120d0c08010e150f0312071101050a 72
    0x1454501c1141c400108048142c00c500d807035091015403c0d543e942c8a00d01040c000d05404030800040c107124140c07c042d070640c0f00b240c0d10361040004020f00c0b40c01c1048694401c0e104d0400284a581c0c400c4162802e1140304001801400340a0300713150300005880599a586004100203040ca40d0fa07441840103d4640e4940691315610000010302c04401e03903004240c1c0b200e040c130071590781e00b2040002c000743d0165800c2e210310707165154040701d00e20b410b04000181c0180081404000c0240241c1c8a150300d040100903c1c504001c00c0120500c284004c01c000c4440d00000040c0412800483c030220980303c0b1015261400301d1400c1000000d202d202c039001303440c03201c12009106440359103811f40180d0708041d5070404981250389940f01c900741c428103221403c2500c50b00030724035545080c0074010104403450048084180103c400052041000c2c1203480d030303444120440780140d25a401c10008070000070309203005500d449800d1001410810110291a40a1260040c54400d6801074015602c901449060340700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 166603012 1250 166601762 166601803
    0xb0907054305160905010302040b03030f12090a020604150201050709081b04060807030f060b091b0c0a081306090902090108130609080a050a26010909080c0106060f0f02 74
    0x84261401c420740441900c07076012a070002150007500c14504070140c0c00385141c1941d5000410560415000e030014100b001c45c007039498601c62981e400000c2c0120307010122080b0444001503105c003002c103c034464054000708103a854541da1345090030000410507010703005508200201e08200e0168040d03c095071000c07005444940461412429402c1d040c810341c6612580300c0500140d640f1040c0131580c0030314003400300040c40c140203040200503140580c00c220701600c01401001100c00c0c0307001000310510388400000b6982e01e41e9200403454a503024070b010341900d070f000800c00d4200ea0030b580010225a40350300c60005032607480c18142c00b240a40402d4078085140480024441026580c1f00885203115000004003a041925526015008aa845000710b00c00280411446410900806504400c01d100d051500b02c0d0f150b00000d4000184140004151590b000c0340801c285141500d290b00b14000c0200130a40e51010000c051030603081400002c642c40041407942e503403000c90740d18055804e512240a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 166604262 1250 166603012 166603117
    0xc17010501140906070f06020a090b040b0d020d090b010609060f210905100203040f020111010e10112209050106110c1c02030105100509070c150b03010b090705 70
    0x30a0b641c0181000f0340d01800c01c004803000942485e0246100c40c0c0601d90050302c0d54152900030f82603c02a41210204000c180410044a083d80c01107e402a00c4038902680b41c410990707910703000d407001c1c0000030a030040070310002c103003154404040343c1280c529540d134645541201c40c00340e41807284220702c1145607034400c4920404907620382290380100c7c800d80c2200e6004009a8106040b070b042520215240203d01c3d0303c2406540c2d01ca0724010b403921140008200e220400c1c03500c80e59070b0441d4034140700c006840318074030354020b98040251070040d050030250002081020042d44150384079405401809490b040000c55024401c00038204109820401800d080e070342e18080040c50800e446543e511b083c0c0b01c010100050300c007801540d004d40401c841401e101410402049000d03c00201248100901c104070140070810060010342100c6500f203000503110403400200e4090300110000b039801018120511500d1640710700101040c1d0b010000000b10408995913240324000300b40d801c1403082001c04c1620 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 166605512 1250 166604262 166604297
    0xb010318021c0b0103030e031c0203270a0b0c100603030c08130b0d0504120e0112020f0702040c020a1e03080403050a02070509011701050108280f0b04060c17010501 72
    0x680020040100410b081a890b0750b80c85030041c0c240c000b20002519156000a1400d0402651083c00b81407403101515818040d402940c0b8061a900d410311100c400d44410240e042c2400c2d02030b80c04002500320b6100686683c1d541c0c0391070f0301c03440c6000780d51f00c45c0e1050300f400c1d08210310030042501d0f49a55003000e541021344480707589800c100303540b2540302c81c440400034452841d003004140000700c800c0c002c10b09207040e05110922030036158808082c0121081038180310f030303070003000d101c00700310100401a20380700110140741c1d990082c92802900301d0315014403a207010342c0019194080c2c0b44070f00012580c4250401c404120440300c0b8000074040b8070b590002c00c00290040c800340c0502c0cbc3c1035104440b0f45c0b0340d131880001c2510000783c2c002d000d01c14180e028140040c0b420300903d8054240500105030318410b080035191b504e100c481c030300030605241f00c40060822010f802c00e40d0045801100d20140350815060000081c120216007001140e4182841f0520710081d980103812100161a81d01054200002d031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 166606762 1250 166605512 166605529
    0x70206030702030904092102010507020601230a08151b0d0906090c030b092a0f0114030a02030a05061f050c0a08040b0703031103040809060f071a06040b01031802 71
    0x6400b5804103006007003d9858038401c00011a0043e01144646504001c0c1c11649090840081085905100c00c002100341c001400f541103e80c90f8603014080108603001100e940d00c3c0c558075070b600914240c00043c40703103c000f40c01c1d81e801e0304843c501000e5443d0040b080c80b001ca44024030748008a824041c0d134801c003550340e110000d281d015034000308103c043e5030313074191200c0031301d40080710001d810300705202140900f0000c1c001c80d20400d9a140d0351114281184c50541002c0400d035500c40c0ca02d801c40c0a0482c0d2280c4452480c0d03005040199840c0d0510010800c0a134000303c54145006242400246040c5400346614050102c21261401d04046001c02112580e2101d80043c50500c6040390010008800700c0080c030080c0b6400b442141c59a03a14540181611b011642c0407941075030a0041c00082080002101d0405108030b071466601c0451217404074090017164000b604109000c00700310003044020315514410b407000c403810885548200700540482d41c1c03d10408002da0f4078400740b040182005031a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 166608012 1250 166606762 166606771
    0x30b04060b060307020a030e0f01020601151806020c0f15090910050604030b04020a080111120a06090f090b010504110f0d060902131e0b030708151e0a0902040b07020603 74
    0x8505060508045002c5600035a0244016400340c2c07806024540e010054030841942121705180507124030000139640e00041c0641070050a40382c0040344040c0c02002c100d40c04400316040c9905082d501e4070b0183d2109040300ca03050040c8040c60b10140c0c0c5180c1440003009815016190300e05150b222020f0100001c1e0041c02d84020518110000c200c903618071000e400254440d000168940ca824414018003040543c410380c16603041840140d05c120540c402e9625400e00d01d6580c0c081550354071300242c05004e550b4002e0003543c1c44d0a9104480d0003460b00480031442c0112151a150b036642c9050000b150140e590b40005000144007113034001c80c08600030421484080f0b0041503058503905601c00320b074003c0b4a0200500c0d00f121041007030b09100b001c41c1c3e241c80844003a80691b00e00d401c0707026030345110041424040140d071400044a220000c40e00c0100307014042c200d032500d226095001000b03402c0e07803040280301d002e51050015202e4140e008a03015500600c1403a070030102d0303aa00313012440d0409003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 166609262 1250 166608012 166608023
    0x90507020c0307091509060e06060a05040f0b03071d0112020f090a090509210906032701270503040506090105070b310c050111070503060c040509070c0c030b04 70
    0x6103a10441e50300308010005414981c00004850304903c007590005482c1c2d41c41840b40d0740c01d0403420054540c80c8c20085601202c1940c0c802d41c0d4404078181222948a942c00440031420190004104d40d0341e0000510b110b4481d40c0c8443c07400001c0e084002c40048401600b182c0012402c20182d04a150740750090416404152811420f25030b030b900006a5800300e81d00101c803803950b10410050351031800c0069051000c03c00c0506075031a40e101c5600191489403010460003448008086a49501da00600c03a00d107081c1544080d520300084c80c03403e40a0100c1061628a91800c841003030361580c00365090180b600da0000c0114078040c80c02042c031141d80c0100c00541e0500c202403155001080000c0c1c5654810f0100b1038402c0d40000305800d01d5082070740205072072946440c002c041c0d00700042850041005695090034140260006100320702c1c07030726185401c800d4041c003d500c1440070b02c14069003d00169141110748101540ea0030a08680817585641c000d080c640d0070f071500700f01144009a8060f041409075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 166610512 1250 166609262 166609273
    0x30c0e0a030201140c01020309030c0d0507050c0409080712020a1103010b01120e0708030304060b0901060e090604050606190518011107140120030c060c18010e040912080912040f09050702 82
    0x3078484901f203030000c07104c0c480747d904000ba0b102f0901f038082c8034004440e480c9041c060304205036522084e0341d44452000040c012644c1e251031000380003100c000d480304158070043c1d4411042035501c0094031401e000d482100c0421200c000c0c801d06260600030030007003a10680d1b409080b04105002d07440640a03003080030720780f8060318001003505441030008500c140d011307038070119086860005200e14604140d00c40e10800480e46101121030b5500320310315800c1502250081010f4446c40002070170391244203800180415118465510140c009018149126000d1000711901100303100544040040701154400c0340c02c240018040854004440c04c1c413144180350043c1035140303080052101d030198110544542d4400700306008a1142006500e900044102d000c40c10480c4405010058203072052015041c48460800e801660300d86a00a400b82030300040c800c0d50054490401518120081d90620a24041c0205d0441c404512108850842c2c18440c8105146440c10210000508000c1c28960860140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 166611762 1250 166610512 166610527
    0x181906090c0b12073b0604060e040e06040b241504090c0c05031b010b0405180d03050705030402012a060f0609060302030a0201142107030c0e0a03020114 67
    0x1d0101d0320140c004000390903a69800c1e614084603034540100180f0800c96060b13111840e8641004404040201c00b0400104460082c1c0000240300c1040e4440f64000300041000a5076560203901101020400da400700300504510711429100c140c100c8028211000880210304065180000030905640b0004400304088480d0002041149401d282d10940400801c0500161501d4401c00041040c3c0e4101006050415071794143c480c007542c184010120319a101030b140c000c1d400e405c40001103200410801503450450b1510305a466545002c02452103020b40703403d00c0238020300c00d5038000c4107030b902d42c1d900350b503038aa00448842c040d98120b0b5040030075050440c0c040c0210041840d0030307a441100c0225145071404001c80441c3c036650700841d41c0341c0c00e001c01080580c80108030980c0f002d03024319201940210400ba00c01084c456000c00022500d00d410342c10314451240600c0034050f4045540134424003441c1c1d03a00701c07501400b022105074004450402080158011401e40038000202d004031414410b8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 166613012 1250 166611762 166611773
    0x3120714060114010e0d030c24060305010603050114010e0103020613030f0c170a0803010b03060307030c0605191706040e10061d0106020d02060a050901090206031e18190609 76
    0x20a0b807122040f00c0314000318800668220b03454441c00e8000741c82e854030900c440d44008001c80103111015102c3c0c40c0c6c144100d802c0a01022040c081d1004030441070050668901d0901c1c000c00c4c2503c02981d5651078514009002c43c89001600d040396401030024045900756001c000c1594007003610308a45004400b40000001d034805469883c0c1400f420441210525240ea1100545240002810303660014610071000903002e1081d01c1c15030b91056006510317a0307075400200303203010425040504124035403040001e2140c0e02000900e03040006101d001c100b05c416000a84052800f0301e0411210755004001511500f010f40c00300303019900e00821200035525810303c80301154a550040d68021040d480c03400320103290781304824010441407000f030681c203910810082d1a1000900380d00032458548010444100c2c00b50881c107a107980003401585c3c0ca0500c1c6242d0708040201410441010000c0400154002c1348406500c811000c080080c200022000902d804044061001180e0301c554895a0f20003082 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 166614262 1250 166613012 166613023
    0xd080406020a17072106050112090c1706010303090e0c1206041409030406030e06060d1403040f1401030b030f1906020c010c08010e0a0603020a030b06031e01020a091403120714 77
    0x1000f549031010603140000790f00990f441700800b0320342c0b410300b00300c8200456640000e41490441c1403c0d0b000070082420b241002540c0c030141c2c0a0184600c0340c581c0725411040109010341200c1c0300351185050560383e882c090614540880d2000e903000003d004141c25440c2101180ea403042d001080021020690840c120300e01c1e5003034450000d26031012806000303070340d0144a491400d501c2000200682d2515a00044000c540200001c00d882c1a6101e9056220400c0003a1000b80c480403264044c045d4840200c0f55001c4054010240081e051244007c00307403c1c0452091601a074031806000080180d40e100340092110980c00c5519603800c0098981c60f41c002e1140c0c1d1900a9683e503402c805502d00060088a00c1d0080d2a454049103080810030059803005020130480b0742c080001c200300c2e9504400a800d15a5480c0d84800715484481c014854803010343c000e088442881d110586030350344814058960b040c0b082100d5402d13a000300040101e001070f0002030304296201d44d09c0e44140480410709a070401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 166615512 1250 166614262 166614271
    0xa03020c07140f0109030213090f0501020c010c0906080618150616020f010504080c09061305071e030c09051509031501030303180506190204120b04140d080406020a17 73
    0x80d082c0e121000003494061403e07507155400f460000b00b00c505640024094900c0510510000c0b651084ca90040180c025400c034080b0f1b030440f00071911281e4000119010700000c1e161100082c1c0030140124840340254090b80c02090050081c8141d20503030341500482840161101c410303448060580344107645e4410003401d0300c08c00e0460401c03102c241d500c1880320000300850003e0501009000912080380001442d07107046030112041c1c1c2c040e03164040441c1032200b00a40250f0b140d0b0520041000240d04155442400580c490f4a241c200f9a0100100c0480c0c03c6a961a0300007800359404100d2031070303d9030221000710b031981c1d60305140800c5580080d1401b0030100e44203601c03400c483c4c010018190548966952100c0300340748052142800d6454544400d001413403448524400c40d002c1e00c0d0007403036a040e03801801100d80317072035802050b5042c0000502401c88007150f0403142600801c1d11300c68003003140341c0342d01c0340750f100e4840310749680d903680002e5082132204070304005086100e86c00c072440c000d1485005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 166616762 1250 166615512 166615529
    0x20103270c080a020d03050a03020d09050a0c050f0f0d0c26060106090312030903170c040503060903070507030206280f0e030a05030d0b0d05010c020312090f030702060a03020c07 78
    0x218215141141107030240b68424207160b00100e1580c00561030340380c0000e100b2941484c003103556400c450341c01e074002d00907481481502843d044032a000c0110004040b44158020038070382e4400e41d658010441c044c14040d01241c0c000420315100030b200d050090100403494070648400009603120314240e03001e50704d0074100711182c600d42e20214124050900c1158003400c054502485014116140c0c0c1510f4000020840b0805542d018113100341485021241c80b00406a48a11310300d08060031030354945d412500649210b4050140032a0703a0798400812100659481009082c1092031502080900d0b080104614160444442202052440409802c5014003513466001c2c90680c2c1d98802003c1441005055029a0165207600045000081915a051a902000302c0c0c0070b620007001c40c144c5258034200a00540c20014020441a0044068943c0841c51b0051a00940da2400d00941d1051740c2d200601054008000b64400350030850003c1548002d80d050251074610008140c900d0105c1540c0800c1c0c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 166618012 1250 166616762 166616831
    0x103140c09010912050601060e120d02030d0c030b1c39090504170d11031927030c0206070b041401061406030c0d0b0307030303060801050a020307020d0c020103 70
    0xc1d03800101000c0608144c001c282d1000307406945003641c1b9070060144005001030740d2031612159462811708218a016170040d0749030a0348005003e0754035089800e82180301c1e8108215043e80d1446845009050b000040070104281410040c40319044040b01342615808604c000924003920041e801010946081d4103901c04aa41841e1640c3d44039021781100740d074a4140020f00011810282044ca040402203c42076a03c04007000844020060f10540d003104a00110030400c4540740301d02d02c020565142c100a0116071003180e500c0306603159004000030080d4100790b030200404d03c5000c007000c2491020b40388515140d12916140030402007100c0440c0c00715000000c0d012103c000303003c0e076030003030402078040021003141400142060000034080e41402a01140003280c880c00307908400200704000e01960070058403420700a0203000b1a0003445000c5d030a000120744462214422a0300c070703417420303400b40204c58802c080496201d001c421099040580307403400840610704510340284410890451000d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 166619262 1250 166618012 166618027
    0x2071e0303090e070815010216030303020c0d03090b04030804020d08040902030603010f0605010e060c071d15060a0c0605042301021305030a08120405030d11041806050f0d020103140c 80
    0x500c440b0b01500103507007203075104003808902a0000c071050f40051a5070b01c242e40810703020004038540f40e4442ca0072041d400e14110b000040c981c06070700030084c0c1c02d2103030305454214151801c10380c15a0175140c0e00501c11030a5100280c0402d128020950300140b00400c0301180c01456201c6840703503081a0080c0c000542c0c00004e002d1306240134400c1415a42402c1000c0c040640741c00c00203081e0306503001c8d03540e0140c4000211082904400e00440b0064100c2c50601c3c072580700805814005100e0850f520243c8048800e00d411861410b64142c88074418075aa6015909400b6a43e440c003030080035004592410780f41d21980c4015600444820741c503000343c000180c66442001c80e0b42219541d60b0720083c040d800020548001c200650100d4452140010511141e078540b1319141d441c620030450b100100601c2c200d22044543c00600c01031080b5040c12a50341d4455035401c0e00c1e40200c9207148242d41c1d1265400100380ea030750502c0305400d510345d8014180040da112247c1c021049042040b116028413000025103074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 166620512 1250 166619262 166619267
    0x3120302210a1a10031a0315040b010b03040b011214010c0807170114040509031b0d09060503090d2712060c0f0f08101706011818110102071e0303 64
    0x2041d0f15510440c4a00c180c0d40b0b40c408944054038105048040540300d50760300c10760f000004400e002110000d0f00312039800030031505245003107405641c200c42c4110144000a201d02030074082d42c1c00303180c0103100340840d6440c140130400c0f801c107844412a07000900e084000301c944400c0c810340c415220036444403107407483d1040d001003001480d04201440500c42c040140400044c00a4004030390740181c400080f0b6481d030300d0055240d805228181c510000001c4500710001d240422102c10000243e107401c104980c03140340c280c0c1c4030302049030004143d034041d4602400c541d00c908030040c3c03080d050f0584078904450038940c01075100010741010860003d41c1104e03104100141c882c0f456011624a0a0340554081c0a0018070020100d17032680100700ca0b04021441c419491048003005100d0142340c0750400c245604400d03161704003446003100301489003541c1d41d10a00680140c95031091750b6010101c40040c140c1c4c030a8a00742442c0003d1341144107040700440e0b8883d401d14407048178001d2020703820815142d0f1400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 166621762 1250 166620512 166620521
    0x170c0c01030609020a050d0207060603020310020d0c09050f0d03050c12041517011a0909041104050a05090c130605090403020f070504140a0504171801140c0703120302210a 75
    0x1419483c1e10400018003255808401c1d5050500c030301d0005656100c00781003010103045640c00181d45401691030506c4100740980c014056402485000d00c409000d0760b400340c0700740310140700740d9030883d200098000032460869400440395200e420203500b0041055240361600079020801448168001000c2c0300c900541c0d0501510b0424501c0c0401c0f603400d01300790346985543c0601c224030301484407150390032200c0c0d4450709441001e180545001010318003420f00d06010044001d009014030300d0840495200811405003d00c6141d1790b1000f490414a00d0051209164641004520044d583c03000428a65604072115000364017a50080c44180c0079110300b14100b20440d07114510461a00d601035041904800e02d15501c00720045c0000364956850500505070310034540800c04205000482c00c18030301e1108000c80051000ba0b0b03035540308107658412150b181c4036074171500c802ea5003d141d00700b0005051513542480c580c180d160250803c0000000803c020503c020018800c800040401c103040645224 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 166623012 1250 166621762 166621769
    0x705090c040303050a0f050409090f020f040603051e01090209010e0115030612020402091306061206211b0308070602030a1109012724090509040b0f04170c0c010306 72
    0x4441c074051840d50701034494841e141d91081442588141c40020343c0c012000d98000b4001840180b02e42813045c40c007201e40c004c0200003244680e40d00c401d00c88490030700d841802c050b02e60103002480c01c6040000075032410250444014075540d01d442000005071640f0260300d001b02007403003000220f5410f182082030307020350b241001810540b8108080180c0c44809012194090b0181c2d40180c1e500b0040c80410780315010300084402c1c0c5800e1010000e040c40d44444024040b10403580200b15140d2150f0304003010b089907824161094001c000c520002c1200004101c050a02c0c0c4061104c8041d81c0340d95020007604146000d9031511350110400104100f10701449050107114640c840c40c00d0190030000e01002d1203180d8541c1000e0720b01c2d80a41381140200d030104003038000c454940e80c42804907030302c00090002c94001080041d9415100040ba400c02000b918040c40d40400e081405540303850101201d040010400c4d80c1e0200101090100302c1d44840040200f084c1600252103070042150000d82540e160b0303030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 166624262 1250 166623012 166623031
    0x1b010b01021c080103080d020c03181513030b09210702040c0c02010c0308181207060b030a08040b0705030405150d0e031303060b060c0d020609010b0f062b05010602070509 75
    0x2c0c102c402e403a52103200b107415654040161a1280c1034454040020300070f042c4060031920001139560f184a20844800302100b000322480c40c1c4010b0043c200c0c10303280c010602d0f02e00611050384410300020ba51a14010381c4401c84404841448440fa05509402c500340160b0300c0c032514000071a00194180380c058600307540c500b42011204100150b0000340300402101000c0c1c00c0044a002044100300038420030949404100215010305a140340d089000f44d010071012103450389001c0b000c010303a00380810307003a4505812040003410300b490840408069401150308407224002000080754540e40c00f410124100242041c098680b4006c0e40d22000300d8150b259444400e81c002d114030050765201948050589a22180101e000381402010070214000d03a8001c440360b000b486001790b025039000036003c4c8141846802403000308124011301c0031048005503031a41000080010601501c56081902a0600c44015612802d004200c0b200100c13842a0004401030304a800100054a0898000f603041301401c1c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 166625512 1250 166624262 166624303
    0x90f0609050405040f0b1009150e04080708040803031e06030c0303030a090219080d02070b03040807020f012016080303060306070e03070b040803120106111b04021b010b0102 76
    0x5a02810524aa206140c41542c40e840050204480740d003480d8030081e4851301800071030a20a0440900318110300a000119107042070748100300c844c040c0c1c0c072001c0f12000003421040da100c130303110100903512800060350b14500800001844a00410003544a4818008d441d40a00b010145c03056410102070310080c403d6110412141603994040f04407900800f1b148070000e01c1180d1440803030213060200c4800c01c0941c5105d040001c0815010452038860700007a420798499540b94a0f9800c4540001e403000f41041d40d05001e05401810186403e0010038014108000f2034032000c1641d81f0400c0302842d1101a5400100300001521040c10805020789001c00c040c1d82941383c4034021943d509402071078081007107507086404006481c207010890143c240201071581c0e0310380365407030f0035500d0717100c02c845040d22030540000140507842000c0c500c01d8050b60a018080c10001508100700304239920104a6200d1350030810f0303c1c1c0c00c07148200c4052071140b10720700110744140c1400000e400d003042ca441c2901180d915 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 166626762 1250 166625512 166625519
    0xe0303041104020d06030c0306051f0807060503070302040905240f010804060506011e0c110105120a1a04020c0f010c050301051f170103050a020a0602280f050a12090f 73
    0x30788400010089080d10010b0315280c031044a813001d01540d510141c482da014007c0402400000d4100500c80c01c0f4104010714070082e44011081c18161910440c04650402d44013032104911420041d84c0141c0d50303181c00341c100384d2504060021108161384911111100780720302441c0b440710881c081c00500c0708681020311119450000780401c0c600600c004c020030750758000507402d0ba00900c200c110748034400740c02c200402c00041c00501880c1d00550252503660050401c4252584035000700c490072149428143c0040e01d40141c044094003550b501c8454180702900d454585480e140b01510100e00030200070f020465400c01003130b003100c142250701010020304100600003500c0e0b083c1d03c403046910a14480144611f21101200c801407042c8080c1d5003810f580c400042032001c00110502110f0081303c60508590b5521021380e510944100d208a10030701046000340d001c1940310021274118043c100050011402c0e1b5140c80c03d1040d80c01040700c03600d444000030360000e58050405c10240c500300300014a410708 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 166628012 1250 166626762 166626773
    0x1080a110403080c0f03070309090b030309010c03030504050f2409010501050307030b04062301030b150306011a0f040905010609090b010804150f0f0b040e03030f06060a0c0c0909060e030304 83
    0x80d0b000260110000003104c090128081003030305100320420040c1d80d210700507860004c180045034425a0080d40c107140c2c0c0c141c400d10b008412030318019016180c045c402c5045070343c1603020380b0340104107a41c2c6000350305201a01a500b4030000343d1a41c020b106400559110049110100034080c04010302689003000600c62920700103030344401d81c1c1d0811813034001075a941c03a0080160003507012401d055006c010444c100c07842421181410703284030300d407803d99541d1084000071030a9400c440240d0305501920040003101c00f041000b050183c1c0c1e0030080c5140c0040b10441442d40e03442a80440c2d040c51307555004001059110000c0c10240010700404e121480552000030320703c0c44043d1019002080d0744040c01d500003401c0e4414003c000941c503090115032003680e0036000900085050b9401103007441240344e46000c4c048200c0b40324058407583c0203855160700d003e1214940101d103201c0240025003510034041800f425828004002542e00820381c00300e1071800750250348460458505581c01401130000151 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 166629262 1250 166628012 166628017
    0xa0906030c260708010b0111030702150c0316080a0207050102030c0a1b120b010603050a0902301507140703050d0b03030409090609060b060304020a12020a031e0201080a11 75
    0xb0401e4140c03a000340104424000c00c0c01c07030000101407a1040d488002003041c0190498038400030240c03100105110700360714041e03ca10590030002d6100d4050350441484562940180c100720529600310ba0400348561940c1d01d030702c205408182c420207408a05c040501c0d9041040c103028040071f20185041c450034000640c1e9440f0b040a00402c640c0c402520080400000088100104480300607404405224282200c544c0000c0c02000006030030400040c0f504105401510080303540a4180010004000501000c00140c04e104ca0502d40040c2840000c01d0000c000005440255003008402800c02d1803001c1d081260000300d21401000c14400400402d8000f01515003a0000b104080340007404080002e00318803440e0025501c00345490012414044503502864000b48214000c02c400b048140400240f030000b114000d50002e070606042c0300400001030909000341c4007400000840382c03681d0721600050b03844450034010380703a610101019581e0109000750001c07440501000303100c502407551825072 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 166630512 1250 166629262 166629269
    0x170705060a0b0316060804060c11030a0e0d020402190905010329010c0b07050a0206150d1506080303070e03060a060608010b0708130e06030706050c07060806040b1503060a0906030c 79
    0x50780d4820207202e06403003d00200c1e142510420710582d07402e803100005403940034291410340300d5521f03050115180314016030345a007212422100960800b100e80908840301a060f0461a410000001e0940300585071070000c3c10541c0001202d80c20010030b02507005090780680d621003410036060450308400d4050342028411643c0d148180c4000401d04040145d4804100b402c1c000c000300d0a40c81003280203680140a000000300320b174250b031410f4580030400208403001c0c410103648a0184040d0b40c0018004207441982982d110001081081e07880f1800e606507042169448049400c03a0400c2001e0300d0306100d0540d00900e41d1904100715410a4401002c16405015592848200041f030f1070034840043c0c10349284414030040222915110b030051031f100c540c255061402803123454004541c060151041c0c4900e4034140006260007898084100e8148801414007038100d640d48240d890962160305500440c2030620004a90300d05201d001d000c0c40700c7c4c442d40304902c458541382007032000541054105003207 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 166631762 1250 166630512 166630531
    0xd23060f180a0b04060b10080c0a0302160c0801090303060e090c10020309130e070509090d030207030e100e0f0a03030206130302010b2101110405060a1d060a080417070506 75
    0x100c07800420a203242c45108100900f0020510040004000e03054222403542403041d90004149642d40d0802d5600881c00c1d0341414202009206851940d8407a44c09800705200a0401d5901d10203180c903507498155507a040700c10b559460344605414980c16010b000000c12030040c14003801d181101c1d403140c47e82824900e4a110788042c5408040551080054070b141000c0141402401c11110007a080240b112840c015464000c5900c0001c00b45809003000784190030030070103800d92005440c821030080d403240008400f407224a0425502d00d845005842207807908640720b18000d0321800702003101100802074420300c00d00240030306200007540802d0040d08001a074110b10701100c024032701680900741080c043c640100714058900c46000f0b030f002140c0b0084640368001c2004600c00d00d10a45e0910543c054039410200070064606200d118036840211407100082404807848004c000850035400b008050313001415020511040c0542c01c0d44a1800b8071002c403507a840d00d0602c2d9900d5446140003084400c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 166633012 1250 166631762 166631791
    0xc030108162d1a0705010c08040203030403060903050409020d020309010f0209030705010c0f052406010504031a09071a070309050a03020d0206210c0304110d03050d09050c0d23060f 79
    0x345400002d1003600a007141d601e0302030888559490300740440d0010341043c0c845600340306420003c10302511b078450155401401031460f10382035859800150410440c01c40400c8002c010001d9042c0084c409804c541e50a110701503543d0401d40a080e0135a0061201c010740c00740304210250643e034000841c1800c540d82800d00503e0552642041c1e01c190f543c462004e0520300545040100d0301440c2d0180900342000e505c50030703c1e10340301d00c401180e03107001c0c0e40030081021010742e604980c518485480994007503450402c43d56801d032251110400c400080c0c06172180180081440010140c0204406014020540d1403211252550700003940c02c1c050060064014100002d0541108480ca0030081119418a540641070b040011032210b26a000301e50a8071015180940c4ad401c030318018583c01451034040c0d58403410710360700c0208200200741d2070404035054800c985d036100c49030320b48208810206021715910109050b083c03003d072419004d1141d80c038030150480741c200003882c200500c509802c25808540c415 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 166634262 1250 166633012 166633079
    0x10e011a09030703060207020112022104140f1f020315060f07060e030304200102070b0a03020409110901080f1006120e030d06030606090605060304290c03010816 71
    0x21014460704800c56058055540080140106a001010700318070030b9072401555418848d410040f401048907001c415031102c484505106100160160030030f029004420100c081000a18503000006410b20010f800c0b600c102c0820092070000076500e90300c005002e501e141b07080c0801c2c5054000ba0000305200b80000300340401d100c1201426103c1c0c0301d40c400d00811100002c0220f060b66901304480454100c1c0c103d14019010f1603114101d25002c3c44180c00070b025460600450b000e45d50000300c070b0300c0101682030100040004280c000c40f140d0b007140c180034550703d030034a10004082e114002c080c2980c015011041c00340c4044000001e50031a0fa81d0324200e09142c22001440014003080301c069051848003140748141c0107015071248003224880c80c010004256101311503400d41d49184070f016440802400042c0c085440e5110640003002c0c003e44610415031181c0d040030414205035002900345402100600c01440200641003108143c5040b504107a031415042c2c0c1c100e580c503012195800e12941c514030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 166635512 1250 166634262 166634309
    0x30912030c0609060a0f0e150a020903010609061e051c02010314072f12030a06030204020313060e072402011104080f1204030b0606250b1806010e01 65
    0x59141079281000d941160401ca2101c564500056030b035440352a20f8510030149860b620b01c02e901c035900420024240403051a1403401d81d003840108403101e01030702041045400d60b002e21a14000e44a00100080d0242c1003450100f50741043d5034140c0c451040001d4244034940c1e42180146600f40c1000002154900b60301c0120050190828111811520701040c026030340d4100074400400840d111214099130b840119422140d142031401c412150048c04048000c003035098011070b840110418085012941d903404a0102c1e44203c6001118011601e0000104001ca014000c0c5520b0408010000c0e80e09200305500e2000d03191303001d42c001c0e0a603540880d403981e00070b40150901c0700102c40c034035445581e140710f140c1e01c5a04c2c500c10f0548901400b181d104900b0000011740f41540c2d041000003000e07540b544c0500c0001e03441601c01c2c10b0f00b80880c030102031641802c1d2282c028018802d03201400d030390810403069600e0f000e00b01030599098003c900107100c295160b02589044a440d400c581000810407800c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 166636762 1250 166635512 166635517
    0x5060c030a0915050612010507050405060702010c02030609010b0901080102070305030f06131a01020f070b041a121510030212060402090409051218060406120b040b12100501050102010207030203091203 88
    0x900902c06030310207500c3c90030345511041c03190702d054440c41000021220301600300c8102319140e40200d83c3c184418890380c2868809840c90320f1041c108005003950b2a000a0319001048421100c0d0f0303034559681285600304100040c0c018509007009605100a554000d0403501000304802100004480003a80c1556014901d40c103040c40d8980420010203041c030360510303242c29044000c0c0540f141c219040740c20400050b419089610314412181424104540342c001040e14518160031044240180b03c1d8440d80c0c0c400c22406441e5551034407100e040c1a100b40070701349641e8642c40051501c1484804440c10030145202d901c04070469005a86484480c0000c0082c400c102018106200302c54a00c801c081940d0020425401072019100740c444102c410401144214000c840015001c0541540b80e00f106030818102030000510114140c83d02c680800c030079242c001d2590007160301c00c0280d4404610180305581c050f0000b0320007036141c0901514007a68a1042c1d68601d4058240040f6a0032113400034801d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 166638012 1250 166636762 166636781
    0x30c0604060203190c09050102061f1401050708040e04030207060c111912050c090906090a0f0c12060902010306060302090604170709020a111606120b030c0303160501060b0705060c030a 81
    0x1000c104a10381a04011b000480e24052507015200d04030106280c22550400b00c0540e00c0c80410300340955041c5040b54940700d140c0d41c0d449050120601110000460040140000c0c1c6038003280c510440c83c103401c00a103080540c0e4001d009000032a6440e1010a10228803e2008602610603008001954006002e40d41090b8030005a955032008000100b00e00841c6901c80d103801142c80714810f865040c81315840d10026182ca03032182d0300c25144032002600382d18118804030300501854203215074034400110340d080c01503c00c86502c0e60310944a4115078040c0b2400000d0425854214105020709000c68150f00c26401103526110700c400391001c0b8007008201850183c10344a03400e540b6a628500302810003c901c4411340840e018810400704502d4036100c0b0442107603216507641006001c414144030081240304109601070280105146244d182000207041c00e2100e00c4810722010f1a070300f01582110055000002c076141d003040108040741b4001882e0fa00412405d03a000e90340e45074100a10b000381400384 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 166639262 1250 166638012 166638061
    0x7170718080d020a150608060718031b0306140f010b070f05070605040509070e10080702190c08100b0f0f01022b030c0806010c060b010e0303030a05070306050102030c0604060203 78
    0x5030302c0600c155000c511140d03101d01c2400465020b04210011000707032805e0f0b00800649900079030009001e42c0c4120003416800495891852815490791a41880c03603400310070302d50a000c0b200302c041080219070702c698078181d00004640012030404840b409909101803103071520210001c191076007030002d84d041d1106929803010883c3c2a2583e0754901070040c0d0058030440348a8044003002075441406131041e9819000001c2c64084645600d110035542e6040181100d82148989500300c00c00018418040d0400c0e03008040d0440214604004030b803400304400100340f07200d410b0000e04212a11200c100c1c0c440c5031003c440d03880c0000126070040f803915040c2004000018021404440f5035080903880c21070112055800f88501c400401040d5000001500c02034001001349840700007007801940421744d0b50005160286504c040a40000d2440e001070f070b004128075580d0014020060f406100b5040205428000365040408025038951903140c018400391200d500000080c48102490540c0c0301ea856844 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 166640512 1250 166639262 166639273
    0x1914070806041e05160f021002071a04140f0d050304141501120201080105010504061b0204020903010903110d110d030c050906181008010803091c0203060f07080717071808 75
    0xf4081480648410749140a122101c01c8103146500c0c400c0420010794802a001070035541d10340c01c4d040340203621140c0c1c290741e8422466201c0348100c4062200e14061405001c0140710340c41400711070f0381004511110301086600c102d0048101c00c5d00705c400d80b940550007421600c503607260071200341c2c00d20808103034240c10319814900110b0720065815403421820300030b998014451781c94800544c1da078400c5000303420204014000360303102c130100311041211032803011b000075003054a8000841d0079a1b504020440102d2860703408442100340801051010141030303e043c92801e25420f04080d10340303045801280805490342182e84900d03000b03408a41200d103001d05019a9146003102027034000150309086031088071010415a0781c0351003a60300506036076903d0080d5180070030110400c0302201d61b04442d003900d64081c600010142e079040c03103540d00c40c011380000703042c442c5070030718005001c01740c0142114107010704500c4801d181190b00d6180340d4820b040f0308103d0030010292044081d0002e50754003841d400c1c40f50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 166641762 1250 166640512 166640561
    0x140d060303020610080d1b060f0f0f0b0306070c08070507050a060f020c03010917091c060e060a0509030703140d060816081504081c02070b191407080604 67
    0x800501c070711642d50030441645e4a4200554803800326000c03c80c006a8400e180f207945500d5104c0341000103101352400624900803042c1941960015461841030070740c1e50070841e08100d40b500070750141c1107040340075101b00e152040d0090408290304002810303200d00800e4582c10401c0c104408005064003c014460069407154018169418810f03040014000c5004840040c1014001c00c40d0840c1e00070f0000844050700c1401d51181c0d006081030f590b00045091410810081ea02004841d150003100086038980001c1d52080c0381c01c2000d02422180303890700701040311690010040d5040700e41c0c1894080c10215a1070f92003035041c0100c9018880a074039041c0c0000d178080c0002740a44401001e0000c220a0315602c0038417945030003202078a07105d0030007120006400a0b0140008148420400c03450340e141c2c1042e104500100d8100c0c0000f1580c02d0004414040d45c0402401d05058030446800103202c884488a41c4001101c4042e100409009003c404607000c0d07a80c940141440302d64803040114410780 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 166643012 1250 166641762 166641767
    0x904110d060515041b08010303050a090e090102190207030809040f020408150a1a0d080313080703090e0f010b12060f191401080709060e010c060903030903090510020706140d060303 79
    0x4404441903c0381c4e140041d132185007170307048003004140b01c9240c542076200e80c6140c4040d95282d1107040c4003c00c22844104c0442c1d075207280500180511403000c00140c644002c01c00100214a0050450080d0341c80b0450030400140d0b004102c4000d02420f03640400c0044070701140001a00590300002c405000f40c1b00c0884440c0181240b0314458004c854051003605084400c1031036076200c0c1c0c0c140603048000d400110022403030540c0219004041ca044a1480d005152100802900507200840000b0702d440c1040080c107401c0010f40e904110b040442803110351509401100c28465504000c05000000c000034034259600d9244065001c0003502251440510901d4403000c00300c10b00482000000c6154a2840d65101e00701651050003c2d445080440381040000d68114001021040c100a403540d076140010f1003034058110410322a8501040c2c9808074600980300e448240c00c101e004600711940340c01c040d9400140a4111034050078200381510820044203103a10943c00c1034a0200e0514000004040e07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 166644262 1250 166643012 166643041
    0x409020d14010b031509060f0427080315040506060d1e0509070608160509010c1523130302060a090813030c05010f05030907050111011b0801090b030c0904110d0605 72
    0x30414881903001c81d05d101c0030001100c1e4160340e0780342c00c10403d05440c40a0b00b055445050000411019610399482d03010440503941c40c2420201e551500c08024040503044c025460340711044219020302a91a004021580f14040e8080540c4181e0700d41d00000c070030401595a03a0301e21214600280710038078042059030383e41e983c244a0328000031140c0c00090707138865034404440349100c2a41e8481d880c0c608880300448241990300d009649021107004002200b4500381701d44200400000004003042c0c0818845d03602c40c240080c2240603004e052000388c1c000907400304d181c662010404c0c400084468903400d006405000390400a0303429800b041c00441800a87e0a0001c11944240d03607520310480c1161040301c2500042e074000ba45640414030511866000d00000c04400120000002e102c1d45c2d4020643e40780e072040703020440450b0503500144001d505600540244410a030002c140310100100414041c0da8010000740581d6505840d214103035450508140313607941c11200c10b10082c2407044080c00001d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 166645512 1250 166644262 166644271
    0x131b0905011101021c020705030c0a03090302040c050901120509190b0108072405070204020d020a0c030e0612061009030b0103050d120c0206060103050901060f0e09010e120409020d14010b03 83
    0x2580000503010090030500803070f107202c2d0405c80c0d0590b41103464111880a90003448040312903010900c09000ca00104106607400a8026550611000c1c6980188000c90f03c00d684854100207081199420b00d90b005a0190302c8419400c01c000380b00d03500c03007601c5400c0212544070040c0c07a0040c100c0080c14403504090032070586401e64141e652403941d0310802c0100c0e11003001d041c0300f000302c050059046580104080c2151a001410140c42e098001c01c541c41241e01240f90b54000c100d43c480840207244d0300c890b0700042c070082514180c0c641032501e1002c0c1d030a443d00070401071041c101c2003030100500d8800c5100380019684081c003058156100c1c0351098031240403501e0300700002c000003804030044626000d0400c9504440d009800725445540044018000041c01010590340386d4100180700201a0f081d6001414001032224840c140929040c0c00d4980004d407460556204580d84202c44504504950031500d40c920300681d14041c0d002c0c00405440112281c240600321400005401d000000085104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 166646762 1250 166645512 166645517
    0x303120405060604062907080301080a03140a2a020303130603050c18090402040905030307030f0b090609060d0606152d02030f0d020408030703020c0306070c0f02131b090501 76
    0x207a031944240011240e95105c4c0504583d42d145030b500c041c00c3ca0103500140c0c464286e040910b400c440c0d0b154048940d00a03880319050740d104090180505900080c0c00144003a01c2d01c02600d4aa80060001c04102c0c032084c040540311042c1c034860100d0a2856a000f012a0340541a81c0d143d800c800c1c0764082d0441c0307600c51400403904100c00500340080c0d04c82142c08a14400d0f5170880c409000d00b043c04401c18008104a800558503d21640481e40400c080c0d031040718556804a40e418441140000b5203040c3c160860040148071306021859603012071469000b901542c41d420203201d0790500001500107503000007100a00207104c070348000e620040c0c07081542c109884803072900915840300d90131034100411140040c3c000380712000c0850b00700307002003280300340105c00542041c1c0c49030314480c150303840840c00714050703480b4a400f1813540c101440f0140e0700c807000341080c4015501035110151007041940d4028032031610401d0303008100d4826404094060f2070b80420050f0b24003494000307025107000c3e0041030b01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 166648012 1250 166646762 166646773
    0x6030209010b1c050a02220503070e0903070f150c030501031e030f030c0302091f110703050307020603040c03061a01202a0618040c05030906070f0306050303120405 72
    0x14440300c00d4084034000e43c00007040903542c40c6125051001040b02501c004070841d0204001b0b1228000e100d00e0155008419a0110540e4a4081054030307102566004c0115207803543c007013001c880c0001c8181e503c038541100b0756003e000154502030a100842840c003a60725482c1183c0d4441c416810352003281031340e20600d6130141c030b620841c0e000741c0702000c032940c010001190a4102b003112446078211813031174200303414054241500d0384006000d040d0a071407250410002008550b8003e80c0c0044e0101c8000025006440c100d17007140c580c0d0b5105d04c52000060700419002005c1030410284414010040d0b4015004106004441c00e280f07100003840074040d8002284c6500c0540380d0050203070050030320040b520040050310780c1c06c02403845110484025103011140c0040711400c0d61a90300c02040700c0c0c0602041c0c010380d2200c2404100443d40b00c1484c0404018052040001c1540002211900641141002c08403668014000c5010701600c2e00f1060b003602000c140b01b660f405d851240c0c075000758850016220b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 166649262 1250 166648012 166648019
    0x9010603020309030714120d0b03060c0a090306021305040204080606040e06070e010813060219020106121e02031204150809010903050301380d0f050105241c0603020901 74
    0x38240e0005072001d0016401c10802c000c0020001000500070341400f0042d142e02c408104000031054002c0340c3d038407040c80e4844042c0e000f2440c0a00889520144d03e03880c007410200103180c01041c01030b03030b404010440d81d070004d0103140c01c045484100b402814018025581c880c0c90b42d1040b91134500070307904107002ea8201103014000c1c41021483c0f0f80328060396600c10021603040001168280006050409540b481942600c08210f403400140710b409403520701e1441c0045d10460090841d401580241200c03440221200300154031858410f21500c000c90070910200428000641040a07610b2050146d002c0081d000580d03030404206000d44c15400d44611145a9030880e00720b09a80c40e481005000030310802c014403610a840e0000503500491540001809840ca000034010b08008124480070401c040340c480580d15040c0a480c82a0600110a002d0395150802140303118a1003070200c07801500307402159800c10300d82810344200921220108c0c0b041d582d600a0040105024001640612007000c00407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 166650512 1250 166649262 166649267
    0x309031205010308030c0a0e0301090c08070b03040b0c0a02030c01090b100806010e0601030e07210c140d0212030d02030c07140f0a020f150d0c080601030b01090905040f020604030b0402090106 84
    0x80b81200d4001c0c490f00c1c40c42d030f24031440c5000d982c0610074103824041e45240b46030054400340314046003248158076000003030b802e00341c980b4034000155002c0404402d0400030400020207900c00d254010100480e09519414203180a90035402004030680c0f0641c6402219002e02c0403d00360240112902000c002078141c9441560392689000d0048402c400f0f4107a0120304554440c0e4049203840e945d020507500d10230340f0b5020307503182d0340307044c115502460048008a10500141c200910001c1a01b40344000841e40301d0000328400c804010000703489050f00c044003c1044c00305104072201a41800c0d82190390b403030107503100e4a040d04403c0082c0e440b0904007100948101000079810340c5000c0240c010706130500c15500f00071404444c0c00c0c002d500185480501d041200c0820003904002e80d98910210f041c161405005000290007000141098100211005e191743c0045a100644074200d070007081550395070501c6059510b06a4000b508800002000130074001107a40d00340c0158801c40c0c01602d0b69170313902c104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 166651762 1250 166650512 166650521
    0x16020d0506040c290909130b04030f1b030215180706020123011a07080702040c0206042d02060c0319020f01050a1415040605060f090319170a0e03070603090312 70
    0x24281c1c804e0410003144c4d686000104607602050b03c1c3c0900600e40001c0ea00d40490300025502100429159100e01b800c898025214003280031031482450203215032900c00070b5841c1032a0122010003203100340866001d14032400c1a2030004030440c1110401c0b551000c000303000745800580011501091200044007241c07290f000d80c100e540c1083c1e103901c1800d401e1000f070080e5000301130841e04400104030000048e1100d0140391140d1a040d0003501c00c521b418186505008010b00000601d03054208913802502440309400b555a901501c1990b1914102d40180d03145205040c1c03030307200310a00c0b4410312694603070000d0114050540c52000340000d0703d42c0d40e824407e8442503105c15801401c03030800036401d401c090010600807000100003040c020350710f4000ca100f03544410100c442c010320000e104101800c0800c05001c18844540050651032043c2d100c8030f5030104405450540788a002410200040c40342c42202040705004054403c06944c940700503000740b8141d0f502f103000c100b48494148100345a40306 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 166653012 1250 166651762 166651829
    0x10815010e0906010b0a02150109050f060d0206191101050c1b070501020304090902011205010905090c0a211a0106030203070e0616030e1306080106080c0303070816020d0506040c 78
    0x800059013445c040021035000118414214070844440b44640841422080e00803c0e004000041c1801d104042c003187d0031004040340d003e007000c182d0710001601e86600300d46000e2098221001c0060203010121984001c08046403402c0d802c05c0700388440c1c0110403008054041d90450714030342445032042c8090302e4803114414540543c20511003044205a542c020b030380114414500221598840041c48044910a0f080005110356400404c20720710420001c0c03020256089601c80305951402c00c081d841c6960400e240440700440122020421001c490804810140403507003c02c1c035038403460024000d4000301c43c4030300016803460b0340c00711500348a0101e03548848440080190550591400d8035100c50b40c030f0310aa081002e2003001203070554584170b0013010300304120004c1446850021464501b010209c0100d120380c0082002e000094540402c0381c1c40340480314400c95418040d0f0001500c100c180e4140035003170f40920741c2000b0401c1018040c0400703031504000d83c4242004040d0861300902080030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 166654262 1250 166653012 166653031
    0x122006060d0c08031813061a0d0b09040308090607030911040507020709020f040317090d06091110170f070c20040c0f0207061e0f0215010815010e 64
    0x306506040007015481c07014002c02e21208426500c004030382c079540c4025000070700d0444090000000340380448101e411400e81010034007110381004800700c115403003965014035500c80000c01d08060070031504603109014009001c03421501d42402d0180003000219841a101c8c000e00c000a1009030107441000d40e120b4100b000c4d900340f02c0c02c04082c04010300c400381c100c00a510030300100044955660000344003910164001c43e4070303546035141a00c58240e005c580c07007003007140612130612144c07130b26000003c070581c100402042151050030b14401d030240c0c051240f0f400810300030b072003079005401c00c4102558001c62124035055135100e00588180034010389151001651000c50540403403404a0a5003100c0318002144100392040e0300090700b110f001420000101d40411030000000b0340601c00c036130052400303040400344401290301c034203044407003403d11606001c40c00d102041031070b1080241401b0071140e80720000ca5035840d4100142d85132100128141c01000701e01c00410380b42c51040b5114092203944 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 166655512 1250 166654262 166654273
    0x604030e01030518070b0a0201050f090d18030204050f0105100903080a1101150e190908040612021b010204050301270b1306020409140702010207020a0501050a0c020d1220 75
    0x4400440142c030010b800e89003070382504d40340d0ba81400382c02e2254000030b040c003051166070380405010107400d441004291640703c0c1404001c101440c035020400c0b01c0541c03114500107640301004c412520521030a500042e41003840c000400003003804c0200b50318165082220001c0a41c0c43c0c2c1c0408a901c64040e000050844800340a80b40245000e401981d2100070030000114980006034100c0c1c602001c1648022444240c030401d2004078052904200700603c16542c09004070748540c3c454051701d2245201d44800c02048100910007a036860381503502d16144074070b9a4542180d4114494041d40150050301d209500c2c02d20f404407582118010200300f00000b01d075101d4040000c0d180d4007980c0c0c2000b00046541600b0071074000028116100500242c030b000c20700024884100100e00c02003074002010b40b03056a10420408016944444c0003d0480700246000d640d11013104a041b80c0c02e0400580007504002c0440c440820401002480381340c0318201d545130701d41605444680e1801d0142d803449a01182c100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 166656762 1250 166655512 166655537
    0x1112030f010f0504290f1f0906080705070b151207050901050402120c09040209030d050a0206060603040f1211030406020102071e0b191d0c0312040f0e06120307031709060403 76
    0x500d6403044490300811030240c14040c6d0022a06a034a0b400c614540359110742e03079055030385030003904540143c03c0c1890024468981080091b0140c498454007804240844001841c0d074503014541c400301c400c014000610886c030140003aa501c0c5a50f0061601c140041c1c4000b00301d80c14180b003a5002c0000050b01d450003601e0304c8492147c59440b0404158026800b00f02c2040152020040301030442560750b100e13075552111000c024144000a81060720483c0c080046c8170105d160708071341c480b107950000300e02c800c11110554281e90310842d19401d0300550001050014450343c0650141041e1344c042c10801400200c1d000d0b5110305000d00150041c4550354001c0800d000c005900c48900c00c20144800020714031070401405260480008003422040d40441c464902d20b003003c0c00a200c0c602440c16529081c9030416510300d0a241060040c0b403036413842d500004080e80c4e904450f510225448100340c03a90b40106040003000d6204d441c401440d070700102c3c804580c0c1004001080c5102da901640e803000380710803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 166658012 1250 166656762 166656821
    0x903010e0f0307110f0301050c031e010308090910030c15030e06010812030c07021801060e10020d0e0102030904060b121e0a180c06080a0f09050c011112030f010f0504 73
    0x9801300964005401d824000000c4d01e0901c03500d40100c00c0f01c0c50050300c03881d020444418221403183e800140c4001078004000085201085c2c40407404100c541c9050759550030150b0b84030003c41d07031014080460b000f6000480102488020941e030001740d03418010302c01c40c1c4002e15036800080c1704100850380302d174848250003603640010310b8000e1b80b604041403030007900e50001140349071401450b103c101d1484004028103900094020701810096500741c5102001c240080d40340c18014810005100541205104585c400d0003140e80368103006204005240d1181d8011070725802c6261034808003048500821500c506980752815070420380f0f034403d500c507a5290203c6014140c80300344400c00703605124a4900190480350302c28041c1410f031303403400d907203103003480b1040140c907040040e0b028010702d010342da127000c02c10105481e01c0800086c2040b4448080c000c440da031a200e84444a01d07001ca0307000c01444071880c40702440904a41c03a80c0c094440c9541c0721820081120352201c0010796651541002814524 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 166659262 1250 166658012 166658033
    0x604060513150e041803080604050606071e0201030e07030f030509130903020604020301051005031c0203070803070804260d052203020102070b0f070c0605040c03170903010e0f0307 79
    0x294405140080c20760300c60b5114020804403481d080820301269214402c0c1c1454070601c2c03c80038000000804a0301140c40c0504042c501804450041c1c0e142c10020380d890b11450110f8004a5001c55070b02d00e104030400312081c0144034001b0482c00a41894503600880b1070004044d0107903504070340002d40d8648144e50a49150b80308100d00b6401180325086000c040d415441561a00b074000c0d0050000d91030544101401c40d84020111005200551404d00c10340e10300081d030610480b5545214000c03210780c0031060b480d40c0110907000341f1130750000007004602d07030340402140d005900c207401e4400c1140c4110000c0e40181c0d01441d800e00d15981c01e010302c0111606d2500481c0e0052580300041c810207500310782d101d02c450f80d400c4060f400341c1e40000d0804200090b0601c03080e8440036100031185e45040070400105003075010302000d0302c040d0310350004c10140030a02115400441d80315000107010200b03503480107600c2c0c20068255200703518001940200003c0450034800501088002d10f20700012a0364248245 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 166660512 1250 166659262 166659277
    0x503100b0102150408120703060f05060d0b2107050402030601050304032601080c03070b07030207060c060e030310240f12110d24080d0c06140c03090c0406030206040605 74
    0x148106058590503030f00290010740100d000d41d42ca1a55000c60402500b03a46101804410415107421420410580c48409040a80320f080310304a0b40c1e003c00c0c600d903102508401c1034a0740d11240300402010700003031040a551003010900241d4400340d640c1c404010880c041143c116011075000c100042c00680300d40043c0c15080020281e014003010305400c80d98020000342c00c80d404035404801080c01520301013103040011321107001140e2a000031598000c1d21218070b4401d010500640380b500e401000501c3c4c0001030007180520880361203107085400306d031700b01000380310f00e80d0320061601000a441050801100ba400402e8507607030000e0351901c0080340c0049510340040000342c0d8402400c41c011a041e03000380300100c0403800100f095900c60004003015000c0c03900441f0001ca02c0941008560b0008c03d425070880c40c130b03007400c20a042487c1481c1020340f182e140090180f82e102c2040011654164000d94000c0c203001c401c4540c2140c11806100441d441408080c5d4881c4052004102d00e03845600141041c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 166661762 1250 166660512 166660517
    0x50a0917011b0e010201240e090f1014070302120103110f04020706060312080106090905070504032a051e0409060b3105070806040b010509030d050c010c090503100b01 73
    0x600e40320501984410900d08801c001450003c0e4083d440c0d070f424000d800700c0c000310890440416103003040c01448a84035109403019003000307400141c185281402601ca03100c03141c0007a00e01000701295450014580c200b49020142900c10110b1010381c4244242c0300d000c1905d0401002e164210346030150b2030b0140b0070109600800c2c921000c0c2080e10380c0d0000e40a46c501c244004180507003540307042d522003410340d2408030400c0b9420004100c051750003440d0f142220764400c00010b06485502044a50b84519000680707440c400646480d8070b00400d1104221441006140d01501030f01c6008000d603c40b10031320a407400c01c00c03006110700980340c56070084039014494500010300b1036101c008121605c803090364050345c802e144141ca000c1c4500030f101c2d410001001610400040c584000041c1c403242028101e140595642e10142109034059000c4030510380c801412503140700b151420061a96000500c0509254200310136024502d0103840b9034401c8d200300034007500003d25090740e1000200000c1c0381c0c0c10f04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 166663012 1250 166661762 166661771
    0x61d0904050c060c03070c0e0705030424060b03090105071404050105090a080a120f05090d0308040204060306050a09110307050904020909150103061d06010b0a0f0909020315030d050a091701 83
    0x6a507803004018004c01d182c1a02450301c618807420104042810396100a1051a60808010149074800c00710382d4480e9002074046000940c1072000e01d21032201c29404010f0514107007003c42c5184922025500c1140060028840c6680d003400c116641c903000302e18410000010b20062000b5800740010b404a65406000c25007069650707641d50b46450905207042d900c1548070700f504030b8501d030300c50a80000e02c4c40c2c50802d42d19000c0a400400c050004c1c9200141c104459400803904569507600114000c60300000c09102341d0400c004028028450407034110b80000d0074460400725403c01151100898070010503000032a9156024410465401080140c00e40143d034603802c07001c891101000e010b14052103001601c210440c0e00021001c07074103030501300d095002c0001000500320a20403980742d0811454040d20030403102500791841029600a098040d00100401c0740010014000f00f074000703011801c07a89003103940c64040d40c4c144078410141002420051040c8516501100307a481c13000022000001c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 166664262 1250 166663012 166663033
    0x5060315031f09030f0e0d020405040f050a03080709090509191e030c0c0e090d030b040e0f06040b07110c19121109010603021602190810020c07061d090405 68
    0x401030b0114007034100c2441d40d1403041509055100c583d070b00f0700c80d40c1c50804e42451000031001441d60705000c0e070020701c079075200e00c00a0304110f2106011841c585e40030040b9511903009183c003602a40c1e049810000295a02ca40014109003078052240035403400406040c000c0052420b00d00540034030310054a0b08501c80e20b174200340600100c1d902c10410300a54464030131114500e080e00300050340d40d110000c02c0b05164140708001602240e01c080180480c1000202030706020041000ba00c90201002e50b580918808060001c20201d00580300d6071049140702030341d03030b500034003034a07180400d41250740107500841e101006404c0c4004c3c3d543c1c0000128038000c02080c2e0b60420a24280255941102c40301c036a01303400b02c600d041806d011030250000341410340c24010260005070141c52131100280c030070110031449002069210f0411000342803841d0903194034442d251034220196005c4940000c66208101c00028560700c100c860004032036070350024540041081f0304015003020003810a580707601072003c410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 166665512 1250 166664262 166664293
    0x1090f030503041e050f09070e060706270b010605031b030117101811040b030304080a0c0503010504031b0c090216020910050904151e02090f01090506031503 69
    0x400203501c150010740d6298104814200d414402c00d0074890483d00b100d0050006070b40c0c428180b01210419500d108032551451011910448a45e151b66001100010310b0030500000341c20600a41c0710345410b0b20341c0119070080c0b580c048440040050044400b0400500141d840f038001035401501714003d038080ca14011452903d682e00c207a00500010440b600c2c3c0d04002d40302485211007919080c1810842000e110700d131100c58500141d002010601803028103001c5a90710340c45440302160140c1117980302c64564850b666201031004040c1d075894500400043d00e0700d4140101880340e5803507901e00b082c1410844081030700c5422240704840f905990301020400040a101a10840c50352015204035501a80180900b545005d004800f24482c80c0b1401d000d00e81b00c034001190002d501c181080c44920101d9046401007201910349c1c928286005500348061a568020f4908100115420011480f1480065a0b04002031103500e401c1030381880019401d441d51040100d42002c003900391003508000e900325 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 166666762 1250 166665512 166665539
    0x503181b0306090a0c050103020c03070b0721061a0702312304030507030c050a03030515061c150308070503040906050a0807030209070909150329040f020109 69
    0x10600e04a00600000c145402c12502e40c002d00d8142c042c0440c04c0254503a096107030064000e4a06040d00085d0000c8480b41c2001201c1515801c0703040d024841c10040c030020985281c4103000e00041030308c0e2034100000502031245104030359540d043c0300b40c00c070300c183c0d1404d03144d030042582a40e021800c0c003951410745c811184102d0800e60052020342e0060880a0f400701100e900c4001d4100046041e98220381c41c4064200550300b091b054185540c0721452031030100e4400490500090490080349010010540c268010900034144001c85030000c6101009010b118040c40c403c80e60707103034405c5c422410b01e40e1140d48000c40200074007140c045441d440780c403440d406030b1108400300c502c2e503c0014100841141c0340b20b01d001401c400c6800d502c0903451f04034001d651750418000a48038080c0324010420040c01074025000034040010305011800d0320884a0b082500b4a2000365888420340c48144944000e45d64203580c25204040c01c03100303035100c0d43c594105001071202d0890522011a40100301c84148954 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 166668012 1250 166666762 166666783
    0x6091104020d050117010218060c070f060504030501060909030e12010f14100f0509010b210702010b010207080727020f1209010b010c030c0803090109020402130608011205070501050318 81
    0x1400b09155251940d040800c0d44922944445d0b43d03c14008001c2c455442c541246480504449050312043c1841059003040c496030720010036600d914000003680e5030400040c000300c07030045008110b07540c0e951500380140c0300b02e0a002000508803c031206414503010014220300e910510002842c601c060400c0400c413070b083d08541c0c108009400c00c000d40000350300da020b0050b14005c880902460710300404a54120303018040d0750703900380c008540203584409001e140000450b0349403051003d428800c00282c003d1000b02d040c0c6005000f00388010500d800002408400c480414100b140e107000141c0d0328030701e90b0010784694201c1d0364082000500f4414401e001c1c085d1503801030010200340c10290044e6003151012131005040c0b19802c1ca2501c00311750054410000d107038010b0030650703480e61000e580a0050140c0c2c40000e40c018808034003420040f80440414043e50b180e9200c0322626603ca01c41e080009004001c028507da10842d02480154407407009190803822004030007046418071092941003810000307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 166669262 1250 166668012 166668037
    0x518060a030f23090c0a062610030515090d0e0102010b030307060203090f0105070804121e02030c0d0305091c090b04180b040c02061b0405093405070609110402 70
    0x2c4401440803540d0f1266038201d00c1d46802480d03800110404a0b03c00820342c400d942c140500c14090204500088540f80540d05c69505d03007142626059000140c0114503001c2580c0c68441c00103143e240d1038002c038201d8080c290000060100d003403407002c21130310550303010f0649045540b00e84c14801e041c2c5040011b0032215106200c003689920f0a002418036109560807070744101d030b0400c0240042d503904450442d41240c1c0002d40a080044503120544410014124425911000c1c0080e00d15066020000d4480424540165803404c0a103031821001c0e180f0581c0e10380010780080c0040807138049503400c43d1407804054109014503039603441e01c00c100c0f500168000b0001d040c1c600041e21080c841031080883d100000c03074040000285000c0000d564000042c0035050441c0c0c8501b88020b0b03040141e050320300030000209080d0750740c40c1002e281e840101d0b990665440d081c030020801d00d00385500340100c0140454643d0b8190500036161079550180890480503510740c80040303044405c50f12180003c24404104d903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 166670512 1250 166669262 166669301
    0x225030501060e01031718062109010c0f02070305070e090f030c0d030f11030a090302071206060306050c0703121512050a05060705180f0301020d0e0d0e010518060a030f 74
    0x608100c0304508044004891b0650208100900c95044543c01180721030281d40740b03519a525a1780440c81c094035500901d0100508400708081302005401002c0150250399034811441201c01c4260f135904400c0c00010201e03000220107101c0824507180c030507440303860141152029589101040c1c1564040002c0c1c00e8a80c200e0001501c10036050700910401c511241030030441c1084144c40003010340000740401905580f01d060172814180300b0010a4060036081041c00101005841e00d58010301c4644001ca488605000009143c1c2c1c0018003600c2c0001d800d601e6901117085070312084001411856428680d050300c14001090041041030409441c61003107000384441c41c945d0a11b586060401050030b0300b00f12003000754100e440c0a00840c4070345040c2c03d550a1f41406491400240a405170744810074020b0b02d883e40d1400104400603030000700d101180c84003540002d114004480500c940840f5102903007040d114200c4c0390415400400f0b1b003003c24900000d0000925440000782c0745a95240d00748100407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 166671762 1250 166670512 166670519
    0x118050a06020a030906050a0815040906020412020406080c030a0f0f0c0e011706061e03030f0c01021207111915060603060f0b04150f0c08120a0b0102030a0225030501060e01 76
    0x103c5e240a01400050a0031030410000d00350040c402c6900500c80f28411100440a0405855030b07004010419070108040d0349881d00c680c0072491100200500364815403d19000003101440800c000c10a2500a800341480d14070356214403000000002c0704441c002c102c43c440c4400314030340c156000007803d030f074225509440d450f14240b03240301214903507003003481d40000c0244481030b65407455030503410355120031801800d030306100040c1c1107000f1152588010f02e00000c04203e40a8103500825a043e0a0180031300291941081200c600310004082d03c0c50f5032002e14840c84e070f40c0341e00e005583e0551080600c003030b20000c0380ca104419951260300c0400442d4445005214201203101018007412402c2c0e40903092624181401009100c01d0300c01c2011f0200050154602c10b2007a0600407516400c508075a0341e80c00c200406c2c800d030750022115540c1c07642c504100c0c9580303988048112005c4004c1640107080200f0100c0980e290011070f07100008180004400000024200f0b0107000000c040c04e80b00c01d0301170f614 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 166673012 1250 166671762 166671767
    0x31c0c080117210c0313031218050405280b0306160212030c040503030c0304060201060b0f0a0f11010603060506180c031311090c0a23090118050a06020a03 68
    0x1a04055812107901640b00c010020000c0c00e030030a110b260030310800c02a0a00c881d100745102d600d9066056000002e440002ca807006485082141d105003c403100003482e00c0300407550346203250b4120200c20200c8008010758a803a070045904a9041a050004008450342020701d4810051600c01d17032a480f0248088540744c280116580180130320b92104ac2440c1080d002520b0b014149581e60403407401001296406048400340d8001d400003400f10b035076484040341402d6803030b081031141600560900c980801c3d05800c3e0b07000d480c0c44d0f84c0d6080b521400c1400c0460309490700309100c0382032810044000282d40e845002401800025070060100140a04105040c03100f000000c1180500541c03d01d420705c40601e0100c01103e07800801c00443c1e0413071000e50725003815600c8811a400c0d40c0302a0040c284509071450400500310703501945c480d103041e80741101c81080342001074002c03010060010f03c030308170139540200700c030000400640240103101500c0d200000e51001040e00017400607404582c0003c00c241c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 166674262 1250 166673012 166673027
    0xb01050913051b0906070204051f12060c0e0a03142806050f0601020604140307050a0b060319080d09030c08070302010c021e191b0e0a140115080603031c0c 68
    0x95210f500300d498145108041041446007402c02401150365500181d52001101843c0c412030f954600303240005c99907107014443c0c484e40d8200c26240c051504400012240c0034405081001c000030b0150400c051171526010b004007004881d260b868014854480c90781c3c032200880b21100f0503281101840b68503a030401408440c1d00605940d4540740580911161740e030005113207503019500c400802e5003400454101c609501940000402030320071554000108046000540d2064205804542241c00d80002286d070050800c40c010303090340c80420441c021401c058220b240c28500a060030003242c40c00380d0720700c1c4441d84410400d4006035900d05180380401d5040c04070726003200000c03210000041d400c600140e1a050108594240c49544c828084104580d4001680b210070000c95500d8100780d031140c00c0c1810020860f2510b103818078050700c030340c042d141c0b90710028140d42071134a41d41d00008501c102034440007800303810300383d00d444240305001c00d2960303210003040c108ac918140441d031601c0b035410180805 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 166675512 1250 166674262 166674301
    0x304060f03050c09040c090b0f04060323040b07020a0507080303010e010608010308030a0c030f020c060106023a0905060d090c050d0f15020d1a090708010503030d0b0105091305 77
    0x15080006001002c01410f0036600401004c80d80040c9508140f0401d8554840903409a00c1141c0041142201141c1c180003401c100e07441d42d1818800c0030b07018100c4110101c50440030210106e10b25001c10003103641810703016484a814011602441030540710300e0b181940d141d01400f01940008010300c004035400b0340540c018402030070a4903255040da9592030341d50000502c803411080d55500000ea10f10710035080141d088d2007a020840d610510800034948550b024001c52000d44603060704280e12003420b11031141440c0340781e190380c990481140d154102d44074954240d001000803000d8086525501c010003040c0c002114100016041c81a01c0c08440340d2455034080342c0704050400e0a0004600ca07029901182d560080f0252100804841900002c2c01440c0f640e002041c81d20106201d0b502054036517580061045403074040c5a601c0340c8044680c10824041c0c6038140d0018022007218005641040003880b005040845c10442941e0201d034805001040f210075403a211400c0c40b0402003201c1410005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 166676762 1250 166675512 166675517
    0xe0613050c19140306041a040f06060e0a05071d120708030c0601080c0f010906050306040e07180f0c0903030513030506151903050606061309020304060b09010609080601120303020d0e0304060f 84
    0x1458207403600a440c003031038583c24050000550004080008042799450f041d039210328100310540d200d0304803c0c0d401100b19400900c1500d00381c08140d0480c05041c12907814035190008414105664060080707075625601c4442c4244280d01000c2086001440a08000349106006080b1580340c2401c0360328022079111000e0140c1c5140352145800d0361b000d100d410503510107080c001d55a45645000c030300200070f414501007081c01891004105101c24504a0304620301d042c2c2c05209102c42c0000210480d4020000c080201714102000c1000a00a0010308400c0390b2010110380c0d50340d40d80d20f4140c1024030481d032203403054031201c00300d800c1403400300031040500c040284036100c40c0b401e42e500e5658554001d050507104040110306191441d010080100c00b60480c0b40040d5240d0811b46031100103040d40948040c4901c02410020906170f1091002008030b80c81c010007000164a409502444446400f50640030182c0821120300d00c0d540600521900c0b010001c02140d4461030300700014050310456030507008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 166678012 1250 166676762 166676773
    0x309010f1106040b071b140c01080c0a0c17190801090905070b1c090b0117030304030e011227051002040b0f0a0513090209040506040e0613050c191403 66
    0x4003624001110303540580d02c6a0700e036000351034a0341c003900e8001c1411100c040c800342c041546c13800c000201901c440f03032021361822910300f09070302001581c0101c012503c00001900074005021118490075220364054000e21030f01000003000024090150300020300890000607680c004010654000b0040e801021055801c03c400c03500740e91126290340c000c1c0720300d21038400301240401400204460004580c0c0161104125071032140c41c02194454003442164079803030a1240700c0f001c00310080300f241d1045525641d01e0045002e41001500c0f650903112a416109a841c944241c001c90301d16182081c1d0034000d42c0c01039240c50180303006486e1110b0700542201b03013801880200180e681c0d00d026243e295401011068413205052401c031014040d047d00381280c218031180014014001c1da005101d400c02c161824026650350000703100030380d040b207542e00307035141e100d140098041e161403648003900b50305c0f480031b5035a6010380c10001820604d5a4101c0c04043c0b1404c68108580350780c80703019a9181406601810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 166679262 1250 166678012 166678037
    0x91e1b0d03143c070609080c010c0905100e0603070f0c0b07050715020c120906070b010e010f080705060706021315030c0e09090304120309081f05060d0209060f0103020403140309010f 80
    0x980540f60340201003541b12440b0070100006241610715880302d04000300322540141000501c40c0740345220744d030b0160320811051110203214440034010700c1d07005801e2a00e1a1a0103404646c20f004a641100800c42c2480342d080010b2007031034001d8080c540980d510381e1100c606042810360340d0040f100c804100f503c100010241d03000085905400800020511900d681140380440c503e44034400006141401c03800011071038502c3c0c00c81045c10785145651b45545240ca41e15416990446030080f6070b80440309004100c00a0500e80040c8194403050994400131035980d818800c01e00c42811b415400b1a4403644100c40c0c0e00d500000028885804580207101820b0064040b0745a100e04d02420b444640c031800c404c0d05040c0a03000240051402d041120007200d944115014087e030513000780d210307650610012900c0c034a050744400c0c00c0990024400354003902c078801008000c00300d034980c5a0505400340400808680044025507070043c108020b1503a03505094001407101c11110120030503c5450000407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 166680512 1250 166679262 166679377
    0x40c0305040c061b020306010e0405060c040303050904020c03070609080307120207020a0b090604121a01081605130608100b0901061e08070c0209091e1b0d0314 70
    0x2e104030340b080c1c1408900c1810542e40042d41d0080e004000c0d4141c400e203000010f0310f0180c00c0400e482180100306a032015280d60581e2003440c4543e1101030300191090bc8000003618040d402024651440030807039140880903681e5000350782e01008240d4016002200304615a6003140451000300e42040045140941a0b80090500c403202d00407042840382c0403440c031443c2c0d01c0e284110b9018021050a0460022a40c80d001070240800720700780300c154000c0d100004210100144c03801a80180030454203020381040c090025000003590345142d0b40e5199103000680b940305115810f10340e00030000101f88194407400b8480c0d17081d01a40440200030b24445040300302044144095901000c13803906580079100d242048840d9005844082d6014102744140050744e41f0008030003041c8802c1c07401c0f070030788000c140125544a400840e075074000091020700040082c90b241081400052290030028020840c0d801c0d114115005915402a0116554160742c900b058500a5480114400c0b00d9411a610000c444 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 166681762 1250 166680512 166680533
    0x30608060c09031005070921020f0105090904170f0a180602060f0a05060301060506042c06060d02031f03080408010513330f0903080112082703030a0509040c030504 72
    0x20710460617911008205424400c86a1100901c1c200301130301100342800200216004100b04201e2080c80410852006540900141c2d544c3c620300900c00c803402d0340d8503190441620314103407a98410260070041c007404440c459002e05042e1050313945042d20304245008a1400c0758541d00320f1001c4d944180100405488a520081d5101d2880400452243c449a01007401742116400455102c40003040104002c0c1d04140039a1650400051200c001030104030901d2180c501030315031980150b01000000455440750f0020761300001108240e01741300000d400150300c040e055801c2210003400002d81088500d0b404d00032241c104118402c185002c1c1c41941d1131580940843c2c1d01c02140383c4030041d04484045c003d2588184121807003c0034411a103003160000c5c020b02030f40000700c010420020010585500c480c400001056200800c2c030704d040050421a0501d403030021007164154180c80d009000c82d28184060710322540640c90320354451a0420400041d10400074402c41007510f440d0800001c105548013 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 166683012 1250 166681762 166681783
    0x10e0103110d050a0819080609071b0201170408030103021005040f06110a0c0f090f0209030a0f0c0f030b0f060f0114090d0c080a030f0219060b0a090c030608060c0903 73
    0x51506070380ba49864140d04192826002420001010072902040080d00c9440040c0110b2a51040c1c4141d807000100407402c175007602c40500090741846204103038890034000845090050601d4001200d14024041c5e82c0f41049800f1507006401000400c114141450076910000003410801c0c00d003420186103984130420340c460361003001041108081c42c00c0d003c3c020101c80c160010305074800d09860b4040382d52901458420780310130034600505504c4107401032086d0b0350a804010090304002d021515610b4101e0b00419080c0c80307240002000103000e5030f10f0404040214407581d481c04092800910964011000a002500840004d03200140503a4440d460840f840c10a01d46980c881100b032010580c42514280020054000c0d0800400c2c050390000d41d90008030b1096139000d180c10102d0340700300d8903212243c400c0307060604500500c2000420a801000038603102a0220010070ba5440e000015203002c0070101c0c0c0881c0d038410b82404600802e0046581c01210920813610b03105601d404a07984000c4005c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 166684262 1250 166683012 166683019
    0xa030f0507230109020a0f030804090e0c090f1906080c120c061309050106020c130f021c0903230f0c01020f0403030206240a0e06030c040c090509010e010311 69
    0x892004010b0000c05440d82071a44800207801d00410007034482c02000402e0003a441848080000240380303111501c0e0f01c0603603600c2400c15040500e840d20301d4015041c2c1d42d010404034000e00720344103041d84445203054401e1079078811003107640c1071041303c0c81c03000080c0c02242c10405003042814402480d001030720510354001941c40c1c5c0d803a200390010080c01c0c060035608a40c0d02180000e554001450503001070713002e41b1000e01d010007250360794400c107903a54030a0300c025a400c60100155210b04441c40d91241282178104440585043c100d61004e200c108146400c50201d60b0b035032010541895440141040b1074020f100e00000382054010240c816805040c1d00e06a400000007030584902001f901070ba4010b0f01d0fa2042607455503224a4040c0d110042110000c243c2208c400c0045842c0700180c0c1401030841c8064841170640e414007010036030121008101c0c036014843c0342001c1120391128822042d0214503980c42035403441c2050100101c00b101030303201619510045006201107a40c800d01113183c4103044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 166685512 1250 166684262 166684267
    0x5040e0403020f011e05010f26010204030203010c0306080c011103270a0f180912031a180601030e030f0a080415060801020d05012408130204050c1b0a030f05 69
    0x1031904920380074455240c40003e5080103880c1140c10412004000d1084101174180642d0b81c0302c212850b80c0500c54400d0901800d03002c0302c250b00840b4209404d00c144031104001520b17003a140e4000c00d003550b90881e0780e48002591040100920402404800302441c4246008481b0f9281040c0d01592801307030103040e003002c00c002c0c2102d00c480300c070340688503040d0400500003c900d180e40d03100000d2030058900c10320309550a0075040e0015040c0300d1040711202d6074000c040354010300b185101200200f41c00d12000d02030100c10b00001700700b139903130580c1c90422500819840fa00791404000050545210315900c2500341d20510013501032501002c1641c09071551807901da165139481d4244441d0201c07010320004801451702d2404030300f80c4010b400500005807400010321141e640ca008403000da64500d05880c03254014848500813551140210903048002c09150682035441d0b03800040844000780e0340b1200c0d281000138041c2682040c1101c0d5010070040380b0240a80880c107803000341070341206210003410001c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 166686762 1250 166685512 166685521
    0x1306120f0e0c01200a08030f160c150605030a11010e03030a080105060f04030803040b04030f050910140f040b09030106090b15030a09140c19150e030106030501020a050403030e0d0305040e 82
    0x508040300740e22031354080300c5e04c40d44c10341040c180950045d9806880f4100d4400004c0b8401d201f41708603601140d0079078071803403220320a48034001b81d0020700c2c020345052074840c034000401d40e5080100e6121036000c0d0b0003030b00110740f8a200150a42d00703555005800313508140210b005245d04168000d04403641030326566600e401790961100d0500c241c0e0002003a038031010044c4070901c160b05c1c1d80984106d109881e13a00c18404c0800090741c0d180105210b065100d80c01c43c0300c580e1003512810103100c05204261929040040161036454039801c00c1e000307491440c10108200c03840e454240100d10080c034a110301000460400c3c400300b100c0d500005200403001e140080401d006070b0701030f882006a95001170142001100305d0441580ba410842c40c401d200c1c02c0d00054040d040b42850002344211000300e501c241040d403600c00159139682c0742d4a901c41e41556a641c000002c120280018410002559a2035a030f9504515010f4441c04044400e00e0069140031107041c0000e8010084a09945042450010350b644 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 166688012 1250 166686762 166686797
    0xf19181e03112b14010912030b040e0d02010e010b040216031b0204050c0301030201110c030c041505090c091504030c0506031f080d0e1806010e061306120f0e0c01 71
    0x1800c05440c0081414000110f04001c810f5941d8000c24459010540383d20f01d80c4554900341c86004074080c0c0302001d85038929528a00aa200b910410b002a0022604182494045003014801d9030040d0250351168400c48505500780b04030644624211411030800040048140241c0780c9000000d0610840e00c12555100390040403144080c1c0c0c0c010f009010500c1c040340100000d8200f848200e010800308202c2e00b24455000c07e01c0e00f003160003e030081801038165800c02018080c4041540342d81d40e00301c60045400e8803180c103410721903c81d991000741d8643c1e9a00900500d81d560071400c40b14403030180702c01c0c400100d450f0680022076004a0b4000e44130344442d44000e515400b09280652030030702c1c1c0e400006642102250104241001e9160004c0034503280003480313080407070705071100c1c0c021007180c0c001400344d03001c0d2444600e440000b8000c603040080300d9a0700c0d2642d4079207401444c0421051044141e80700824056a4107800c01591305000c0d01c15144000360390ba888815042d41482441c1c03001303604200c07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 166689262 1250 166688012 166688029
    0x1030c05040806070309030f0203211003020402070606031e0b0c1e0705070509180a06020313050a05011b030908160203120d051801060303050f0f19181e0311 69
    0x41078010b07036286007020704005c0d000309038407203044002c5a040c40c1e007120080d0001c400d9a60340c1e41e00d518220300301c1038010420118510028100012002c070450040050f071038601c007812246102d001e00107070b051f0950910400094840400220004100d54002c001405452441b46c1250b50002525107456010a50718011062560001110003012581c54140800000d90000f101d90039600d80c0165111504806541e45e800906410175078416401440040c00301c3c1d008641c019a94035003080200741c0d90303941a0074850508026a40e0b60344900d00c01a0301444408480e4a581c641d007010001844541c0c0c5a08139070149506084c0d40d480580c1c0300c1829500d06008075020968540b505959507003d08410400501c0d007a100c0d01c5a405540032803000c048014414503090f81e03010f40700c850074039820803207400a56201810310400300320700f485414850302c4644000190000c158031286610780351405110905080d66001d036030981c0321241c030070803141c91840e1442e040c2c03034000800c0e60100c0303511b5002c140d140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 166690512 1250 166689262 166689269
    0xd0f030b18150603070507030e03010207020d08030a0e0d0914030705060a02010f06050a06050306060304030306050607030305160810061101061d040c080a030e0409050a0515060a170a0201030c0504 86
    0x1914a031641c0e03041410507140a1148006038034040700110544103004a038002242d041d0045001000404042405400b102d490044010300161610300181c0c040b8407040b01d052000c841d89440803080c44620b00301c40c002c0030110441040103001444000d60024100c1919204026400c15042844d501c4c035182440301d40c01a0001415207a50788194a400078024007100308194041d03880c051001c50716107058600d101c00c0303034501d9135107504640707071402001019031000c0c004a007890740d24407002415448080103082064065140001c2504d0090b0383d1010b455000c5518a04000e04102007169160700c0421a4059802c4c0745024040d04040e085918018956908024840501c1d140c200310f00c40781c03159110f8860762090031007407212680c0b468410b94841e0600002008103004641d0810541000c1e0b1143c46403600410485940303074035544600e07003414484081211000f9062041000904004140c0c81c0103201c40c1002000c16100040c1e400e85803884480300904258a4552030314403e8400c4003510082c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 166691762 1250 166690512 166690519
    0xd0206090315160e030304121e060c0201322a0c0a0c17151302090a060e06030c03060a0207020d0b070206060102060c040b07030e130c0c0203100e0d0f030b 68
    0x64201814800c403140e40f000d10100000301c07140100d101360709000c01074070110f0304400380c00442c10b80950380341d100d04600052110b8020f484c000c40c01d030116040740903090b0390f400d01d42c00000702d54051058103541d01003030311151101206040038051100615a030300f96441418106038044015030307002d01e111080700002c40000f64240101780c056000901148903000d161240403030812507a5501410381d010ba9404030a60440c2e0032004048034203040d0070303443c0380c0d100c5c501c40b14039510189540d00088050300305a407500c40441ea0303608240110b1100421490f0420000c4008101601d920340020f5a201c60040194501e40c0d0003003654001c41d107401c41c8811100f135100c00141c0091a085400a550315822a209401482035034045000c01d11450704aa0a6440d8a08158039100c403a4605480e1540d0b45e09900783c01242491100d21100360511a000500e41203030740f0b01680120500400d03103001034500a40311210300e004034040c03c05000041180080c80c2c2070910140031240c00c1402c1e0000e2044042441c1c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 166693012 1250 166691762 166691803
    0x601090b0a181208031005041116030509150309010b04020c03040504110903120304170430061505030709060e071416230c0a090e010b042a02010b0d02060903 69
    0x2c10000c132000d10700c14403a54001524a50341d80741044103903262204000c00d143d2081002070a4a6105400700c101c150281c24198a003c0782500881c030440c0490503403040207540482403094400782805901c800c5d240c2101c055051003807905000d81c80344aa4846c0300d22450f540d12140b11984959070640c0c0150b00b0003029220080c0140e81803200960085908031540e0203426129031182c05072400750f400ba01c40d080c0d40c00d1400c040101102e4501110103401e03250001c10150100000740180c09522074019429100d800450702d000185860142503400241005082490501440e010100c406a020b1110314107800e03480c202c2c01c40340b15544550402e054680003440051800d014096959034074404061450508e91003c2c150f8a03030f2600b002c032148941c07042c0002400c100308002900094004c010240000920b4203103080001c0072120021141c041c400103520110310030040c0081d04200d9515140002c0c45040301c0f0b0800210b403d401c05034000e03c1198080342e01c030f6040c0c4003007101c1e20280c400e0451201303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 166694262 1250 166693012 166693049
    0x15020105040309120503040311060c0105090106080c0a0e0a021e0d020301061704050717010f09050a03090806090a02060a050c0312010f090209130504030201200c060601090b0a18 78
    0x2806000100d0303003030300424201d83c00022682e040150360120346800c01e01560500e4110ba0b070b0541110b880b4400c4c6684800180700324058a10700384103017402000306000000f84c2e5440c04081900b0540c03403a9910344194030b840000c02080400302036841d8400c1240000580c0c0d140300484070316420031441c8034003408a0000c1001002c8200c00d0b402541070303a149454a00c0200301148106240f1a411603006026801000e4100940c036600240c1c200d400100301c0010403410760103029202100c0c0c4480d001d44940d4003c2c0303c0181415001602040074101c400c1c050003071482c0500b8060341d513007040803009018410000d10031003c1c91064081e21280c00040069944c3c070741101e031846429084c02c4c0180c281d02417220f007002030700722214401c403000000040c000c41e4140345100b83d010001c150003081079065540310b13601801e0040040d401260810f41c102e0701c0e65200c2110311103441c60404000c0215041c4002d1354414030031089407a096490580d800c0c6059220103c0c006184a4444102d50014042d209880001c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 166695512 1250 166694262 166694267
    0x203040e04020316140108010909020d0f080408030a0302031f0807030803060d120f020142090606020607080105010813020d21020a060b030703080717072001030c020c0604090b01030615 81
    0x505095000342da451047e644c8800d14a4122034014000a45c80810300d41090001402e12030140030150082080a0030b00b540c80c403499041d9442360340c141000950000800070800c0501c1403850000c0c0c2c0d01131a03543c0071420031414a0340c5840034000a045280c003c0f0000d4000e82d5401410460360364400512404090140070180917002030340307810000743d420450714800500400001003010001e540c5a0107151078400030f034495501492403603100d0700503001d02c0803c003c00c0718020b03203004008030741c014906032400382c40040011106030880e50421191206004045601f41e1381d0a14442e0101da0490546005140ca03644405040c03008000c255640500d20041c540c001c01e0300341c03d150042000740040c21800d0201070b03c1e0b48450200801064041c4440d0010485402a140c05080114855860502e490700e406c0c11510aa00c41140c0d00c980001200906591500540c4109503141c00100200001c5600003482c0780900d008500041c2d80d1014143c001d60700c40e410410041c004001150356108001c3c200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 166696762 1250 166695512 166695539
    0x190e03041401022b120207080c070513060501020a021c06150f0603020c030301060e22091202010902092409040501020403140601080a080f0f160501110a0203040e04020316 75
    0x646000d8050000540a40c05003100340c406201850001525550500340066480d1254442071750200c41e0309104071400110303031000030501c0c500c1140c01054003914100c10040800291074030078a165040038410400e69800082814842c0da040368010358107600e01580c460400c52100003c0d200300d00b041212091030040e6851807003a11120f80e03010944989a071000d80a038400c50340408180da00400042108511a000010095100501200340200480c1964407003404505031490103c0c0e031005603004101c1c5482c080f00d012665030000744011101c40d00024000034006040d50400b030030b85202211104522085848541c000034254251400e207410114001c2d0814007007240d4504c00f50325400400403000403214101c454500091080d074540d580d0300d904c15004115046000c1405000a600306d0500300d014020b0103c0081c00310703c0301c0100b810014291505a0596040da6000f0051000d100d0740c088122025500f03005581c0020343c64078030101e4a020810039160080348054840030803c00443d810 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 166698012 1250 166696762 166696799
    0x2071e061506080c0d110a031a0f010203030601030905070b1606050f0118020a18080114160e210619060501091805060a08120a121103190e0304 63
    0x20801592956070110a01d12116004000100c0c4995000032a26042c0c00020000222194400f0480d117a02d0070400c112900040d168101290316101e400c50200349424030b210a20800302d4180032640c0081001070b480b40310181403a41019120103000c0288001000048010401024a107554402445400e540000c1111040f120070303082601003009a0740200306c2c641625410010b0208034000240018020352100c0d140d581030001c594800d02000100d000c4a10060003440d00205221040500502400c00024505441100500c03517403000c55a0201000070100f000b41c5080e03084600c0e42c142800b1005651105003114418181049050011060101014112001e05200c038640703d8005560900785030003070010030110081c1088005c40140c201c941c12030300142007a05138684a610103801c0c000c1d0b0200441d00040e0004e107224a06a11038040b40c1321074000741d030812402c401c1c0d80508406110140082c4a10340001c440380401c007510794080510b00360701d80102d0f41e9903a501c03030007580caa503800030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 166699262 1250 166698012 166698023
    0x80c031003080d0618020906030105100c0b0c030108010c0801061215090504030c050d05120f15030703051b090c0f09060417010504120c0f02040c02100501030b01170a0507050f0402071e 81
    0x5d0103583e03024510b0003910500391004003038034210b03801d14050240500084031100c0820030300091a00c0031540d040c2c0711601034848904110f50340d44c100958103003901c0c40f00099408000c040d60041008075445401001d600b0140354010403c901c0040d00c0d05803070b1240380c2000c5a510f190500748001c05030801039040f4114841c4065035a62284440c0644160082e0840d80399903d48410004003201b01c0d0201d01a8040c821540d84c0011130a44d00109140151582080311198400401403550be1150100c0440e5100126880e00b181c4c9040354070b16410f40600c2e40b208401c0030300490011151f0b501c0405a6000d006c0c50400ca81440c043c4010b240d010349000e940664100000401c4900c3c0f2500c12603280d140282c10400d031055a2225909010086c4000c0140000714010141d16030f00038041800381500840c00b50540070619410b104903e03481410a00d4800351a43c01030070728000040d8042621b0b8100d070000c07030b00d00d40001c0c1012301140203803041d014014030b00b6151544103040b1880c4140c0040c002e90140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 166700512 1250 166699262 166699289
    0xa1809020d060e040305030106030f0908030405061f03170705070810140c0421053406050309060103030e03102a0e030712020f030304030c060816080c031003080d06 72
    0x204141c0030801c0060750080c5c000741d020801030103400d000b50068698104c12480000360141c21791110b4455400550341201c4c0c6400000504c180d2820b1800200c401d582042c8104007000d20399540c4038084071000341e900031503c002040300c0e4203001c000d000401c028441a400e40d000d601d08000c01000800309105070703c08400303c44000c01e0442d40400c054a094540c83c00c82c098005103070460036058203c0c03400d01203d0510500010780b81d6440b00d5860189011031209804102e41d0646481810036481500081d0811100780100011414000384c1c803811280c140c241168044203800109040a000300d4050030141d0409400740c58403e860040d9040341c5455000c921420382e5008800c41c0c040804a00003641688104170502c840200c0c00818821a48020541c140800c031081c040390039600700358810b49000d4900703042003041ca078200c4440f0b0380c0001001c141803481035103030202400c0c2c1c0b40c0141c084c0500f12004400100c450904039800409960481c2251340c40320900c0000c20090581d0f4055201ca06815 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 166701762 1250 166700512 166700519
    0xb0403021203060a0303050702030709060618090e03030402060a0c0c240309050c040b030312010f08071a12060111060c040f09021201120312020309010b010f050313080a1809020d06 79
    0x89082e00d00600000301041c43c0305207992012241d40d04950010390f4103010f905030016130351240c0d101f0031004025a813107603500345d6180300c03800402d1199584583d10031410f02c425038001e610b020044940c05907040300e000352580802c80b402c0312040741c070300001000c40d003c1d0400881d000001d80118420014640c20b202c80c120b21404044060381e000000003450740d40540c190300d0251030b040d00300d0180034002030100c9084c01e40f001e142003001c003000e038000c0c84c8030b0072092814040701c40c082c80104080c0c4100480d040c1d0507150a100a081485421140c00c1620b0391600032440c241c0c81585020001d0f410300040b10090704000100074480d42c007600c0380c1060308118020008202d0b4142c001d4034002c00d000c00d03080031140c0ca0100c1106042245107001c4041100c1c40030f00c0281810b207840907501490907040005003c0d0b5a0000141608400090003000d000342801001401c40d03481040b1a0000d40c025001c42d11103c02080548103c041158017103001181070002150051807903001c0d1403001014a8144941c503503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 166703012 1250 166701762 166701793
    0x240105040b0102101a0901031a1f030f020406030506040b0a0e0d050f09040b03100608011109030a030c0204020c0a030c05150f0112110a0806100b03091e0a050a0b040302 74
    0x1078402816003da0081040c00742940e0490340400f1560a0321a448204805890700060180d40241c00440e50700c807401402c811640400c44a0503840707410329042a900c1100c16028800d06110b40c03000404607007500031300c44210740303464010328002c550000031034000e81860310700000480c1c4210344840500d0301e0115554007002d000600b558545c80d06d600c07090325000e10846002c046c1c0d80300e58100d5070130035280c0900000c15241000701c1a04064a404001990350a000045080d04c11100c0784600c5d0300c1e4148079440503035034007181e482d91141d0302d41010b04c107220700c510100c0c010740980380c90040c0a0040f00d50010504d074000051b201400d104900340c4680b0200c0f000d11419640003501c500703440b2002d400051100c2c1200c48907803c8800e001d1082c4c0030341c08c0031520000e403103441940c10141e5590403680c10f01c00d440782c0368442e142c050b0690b121240c0c15403a0440d4401d40e1146800c0c060100c481540c140000c08000c184400348910b0b4012050f80e09040316170070007840c0603000369801c400511480240c41030508 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 166704262 1250 166703012 166703021
    0x19020a09090803091b150d3c05010302060f07030c0206030c070528032001050103060218030f030901200706020601151e0f050c1006050307080f151824010504 69
    0x2000701b01001c0c0310001012000d01d500611400b07103c0c280d0b0b50801032082e28481c02c0c0035040003480d00040b4801340d54041d600001240e0b208035491160300b0480140300603600c64040c7d800c10311700380e1151fa445548504040f5031244469a000e500150700009101280324080e0040c061503006404842c20510004100c5601e00d40005000300844110012140041d12034104400c07a0a009020f01480c0c09102c8051400c40700283e004a64039070380003801184e10808410000d80c0b20808402420034150103940498881c803803160240e042020071006080d044159101c000003400302e082c1100d0400381c1764070010b0350b121020b000309074404845610400160b44240881d0144122800c800b68003110010001d0390308840c4000101c060000a109070b05824108008a01b840c0d81602c1d8007290b171914050030b150070000c8503005942540c1010300001451400062900505000561041d0382590b80014000c0d44000300c0c0350420040c016a0240d0140040710709024005c0f60740f08100ea126a41c0e160104800c44 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 166705512 1250 166704262 166704313
    0x9060801030c03060203060a081014060117041115040b12180d030b0d05030a02060423030921062d0f130303020408070803030f15010219020a0909080309 67
    0x142d5140510004000741c000e160011000f030300d06500749403100d07903050a08203202584288640d440082c1d084030b00340b410641d50000740a0034400b03c4c0d018111244441240d008201501800e02c2c2c80090190f5103d01003910712007450301c22a2174130780d61140c03032074070030ba6101500120881c0038075004103900242a8040d1100141c05000a092694034104150041c01100c80d12a40c490408211680820b60a000610008025501900f907a1426282007203168904a4080c403084912040c070100552000084442c01a01145d011202071101a01c442c0c61003e1034070300c0c079840d015600030310412903240d07036001914446480803001030303240d55405000c565074201c806c01c41c0b000054001c11649109000c1c40680c1900900d4003503e040e480746100c503e0040541c1c8002465440007040010b4640307111f0019422003c01405102c10160392030000b0f54482c1d40032035445030b5411002c089421503940a98a0b80108181801407040c0380e15401d1120380364000722002c5400b40600007208840f9030070200b0ac0c9402 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 166706762 1250 166705512 166705523
    0x70b07050f16080403060908130602010b100305131407090507020a03050a18051c050609160519090c08090d0f120f0e1203061c0f03030c1b0804060906080103 69
    0x400041402c40c0200d400140015250140304000100104250b40a1940b4a5020340c011650313814480c06000d00c01c4c07030f481d40500c1c11a403514550065598500b44540c01851442c540440c41d511150240d00d101e20f02d0482c000d000d5a101c0e40d00c0448604040790280c211011544104110740c0c0e000c5041c1d855240e042d000500040f01000100e42c101c0c02103003100d610040c0c11143c40c59140c0c441c1d022401714079050b68034410366a00401000d00b0003104010b01940009404058070003000c85c0450351050340c425010381881060484050f1908185007c1d50300000e0100c00014040540281c41c098225207081d9240700b0540244070182e802d181c00b03001600e2090a56640f4145150701002d0b540c0000c0045805451209880ea100c070700e035101d010000d40d40c07130104142981d40d0b6818100e00700a83c0e40a03c0c608440b004c03501c00140004a11101c016504590b05420086020b01902c00200d23451000d0000e2500e481d003078402032070b0900c040030010b84240d49180e150200940d0720f0705415900300728244001003e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 166708012 1250 166706762 166706767
    0xd0f02031306110f010905011b03090b01120f0503030a0912030e0606040c031d0601091b05070201030c2d0906030b031b03010e100504050c10020303070e0109050d08070b07050f 77
    0x200910032481072218541c80b0040e119030440604d00103094400f0349000303641a03034540b2007000d0100b005420394032484509040412120055581c1d4829040c41407003040184040324000c42c060010316070602c10700d90752220643c0d6407890284103080060586050a541c11746070004d4980035a4001d00c284d40f1800307001001040c840d551541080054450300c3d00c04800c041e1101c1910103400c008084000480c0440006880c082d8103001c8004101d495013031078030100c21602c0e03400ca04040c0d002412548400c2d02840c020603000b10a2100384d03400300d900da280d040603240c03201e2000401c00c02c040c054035a041940d0b58544080b56150012011b03540300042c9940e0503041401c0c0c03807508219a03d030113800ca131006000442c451010040d50b074107028810024400480e200c10070001000014442c82c4003041c0301b03d6944555190110000b90f581c00300402e00d90070300122540d060201d80c01072403654020301000b40110369401762407804a4540d0010281142c0a1541101103039010b8042d005039820310310105041d03030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 166709262 1250 166708012 166708019
    0x31b1202090a05150d080909060105070803040609020607020d08030f0a05090d0c021503010e1b0a05030f27010c09151403040602090301050a06050f041103060d050c09090d0f020313 79
    0x1e00400c0c000d04050078110000c803072031055031141c5e8800b00c1c0d2580602c8090b520b908000041c00003002000740890b04010040001b4030005031502c01380d90f0007070340085000600007038620200300181314020300a0b502c103010500c90f0b800c0088400c02540700c0c8840481d18149500c800340c031001914411303245000150401525089128401d51400ea0881d0000380000030b84005400610943c0d442a00072003e045a50000c00a140c08c282800d810000484200c0030f01c4c100612400408601014002050b880b001c00040745a00088010303901c540c0000045031105030114444140c0240a1030101038080394240d00005140c5072090413140440b440d68540501d42e041d42408509564402401120980d1382402811100d0f10b0912500740700d0004404c002030101d0824081007058546844a02c0c403640c00d00403203040c007220302000c3d43e41281098800e90b02039920b0b0302d80a4103003049201ca803500a14110100120503600161000c02021035403584100110608012a02d0707200c2c4420310780506003e8503081 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 166710512 1250 166709262 166709281
    0x70f530105130c1707020105040201080c040308030c0307020a0203101a1804030807020a0c030507091b0f050a020106030618060b1f050a141605060c160209040201031104031b120209 79
    0x43e00b05550b18000c50900b0f50484140525842656100d0060303568030100400c65800c6218a6001990040d01c94240740c03641c1d4824880380700080c404541c0f9031021010a076401c0c02000105800b9500a06860000e02443c02510040c50310011101204040e803205a00509003440658541d01e9842c0341c0042540d590f403401e40e61100301130f1241007148100848040403600300e41042024511a4000d8500d03541f501386a281980c800040da5096075260000c00c0305c00030f4001d0417000200030a401c06503250305402c04107a00606030fa81c0003400940c10600b8280ca4100074140f4828400c7c415282004010041d03c140301200c10011800d468440000198890860061000e00074000c010b00c2c01e40c0c000f00101207826910f070002048070a588900100803002c03c00140010380e0300490200005091842e1000007481040390707484041d000d1040c4c20301040c25644281c00040b0f00012503c00b40e603480396a890311034100314250700440580d0301142c202007541d91003550760500043d0000c00485190301c98404d003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 166711762 1250 166710512 166710521
    0x50f09010308090a05060403080a030c0302090f1011012f1303152316020c060a120b0a0602031b010603020607020f0307170c0a0b03070f53010513 64
    0xb8241d0140302c4c0180042d90ba958440100041c512030102961203028a210160030b645401401c401414018040081d01b6202d1070074002c42e8903800c0ba000c02c502004000c05840560356582c0c510f50550804180b1840c0740e00402c030f0400044000061020318950702640c0c001035008803128141094000c107001c0002c507061543d40302031342c829460005010711001038000c03c01c00c4002c204d0040b1242c031204210425145076800310300500740780042d000c0c92402000080140c814562040140201100182c2882000d9413084c0d0110b40c001d80701c8009142c841001035541c1c3c002d200d551286480490f1115000003060080404996020786140d00b0300c090f0780c0c2007020303080640300500c0d05841081c10018044000d00c800c21404030f4910042c00f0803442c0c0c030061003c0c4900c940c01601071641c040043c0b00300ba036070041040307401c03004034034008480d444d1000c0e50104102c81341349981e140c2d4107094088551800f030766500c0e00c100c3c0072421188200d5801c0000b044100c950920a41d0f5000c013528400038848481a040f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 166713012 1250 166711762 166711777
    0x9041a100e0f0709270618050901050606090111031908190c02030703050708120a0f0c031e09051e0106150e030c04020d060314030307091e15050405040c1107050f09010308 75
    0x200b000807005040030035040714540d81c81482864202c07c0c50081242c2d240c49250f411244030402408a480c2040210f82203100704004c3c20304001300d119140514007020b005a413030115500206022103500050000e002d004180d680040d10b00c07200d1241c040b0811a4410b00c1d096070202e80145081c00096101070b10903401000f419254868204035611400101c070300024403403007519900107060405100280119054941e10009041c40c000e41c1800b210b80301c0e180303032014401c0d85801203a200c0061800a0901c2c0f0f42002d100030151003101c00c035003408410740140081d101401e400120701e0120480450311845420649501030f041103400785c0c8181416001003406462140000c10000d40e6030fa1205030328100241480d009070804420310030419031000c104001400c080503031076a240c26048020032603c140344100982101c480da10180304900500a0f0784c0107280040c0200411740c150342d000350514000700d805801c82d01940c2c1001c50645414804440c0d82c0e1809800c000c840d03804c56030380302e045601c07804 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 166714262 1250 166713012 166713059
    0x140105030906072610080106120b010e041103030703020f10050f07110705130f0c090b2d1b0f03030912090a1521050103020f09041a100e0f0709 63
    0x8203010300d010101384801d00507100ca40440c22481d181ca2402070841d1290f800842a0215210094011402503d400350540d03c0085260f0459140c62a0403001c0b180010740d200d426000110345002807503004651613500c1c1038424185c8092440c5a201041161011203c00800c0d01408009ca20014403d800c0c00b103004080b003084405185d12080040d00d000108545509000d07158142d02da5100c1c464003c519a031211800d00c40c000382c1c200b110305220f90041080b0025a0781400b10040c607520743c2102000c41d420348081d10190343c1c48204041c8810001c1ca400900803a03c10884100035664000040782d200d1a0307440301400c0841402c12242641d84c2c0315852850f4402d1400c20045103040e84d60f0340314032103038031552906451900b1245201c909400101e400b100700603d454010400346e2100e0481c038211030411100c007081e60395541f5140b15812104900307100680724040801000e81c034400c04a000340c0b00e40410500c02541d44812064850204990b40c500160503c130040103008595082440c82100300e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 166715512 1250 166714262 166714307
    0x105090c0711010c021203041806151101140103031101050f01150c020a0512060403080f0405030f09012006010501090b0c0304051c0f24021e030a0204050603040c14010503090607 78
    0x250001b440a2840c014140700c69000002c040105451001d004c00e2182c4900c1001e01110303181502003903003002c000c42c0040030b024190b484984010004e40c4000c1c485450032915191658490130001d21000819040e800650700c5d00b0041a41c452070307180100d04840c040142480d1700929804c1c1160050401070703049801c68491040031070b01380d440136007900100c08184018180c82c50242801000c80c90050030360360708117001d40107200100303801200f100c040c4080e1180342559603620b18012558183e19040341600400d9402c038004c0801004100203040703c0090b690f100c41075071546241030b071912402000f09510381c402c100c100010300700000901c210110254860701d5445440d2070307032204d00c000c113041182d52110512101c500700c0b40410540c1201d4950309811800e24540045401e51240448443c3c1c034034110200c00200100c407d60112006004090070b0b083d224145440c00c0d50a1400c18001c52120341040010b042142d481030003500e109002507001010281c490203020381e144548051298210a81d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 166716762 1250 166715512 166715537
    0x71104020c03120135060703020a110105090a05071505091e03030d06060201061706070e030f0a0303090203010b1c0303020913020a0c0203060604060f060e0d05160e0105090c071101 79
    0x160103030320380240654070102c0b04000110f103c4e40c1404e51851105d140300f041e508000e5190f05800600303280c0c420428107005a841c85e50f240d09485c00384000208000a40c200400c110b80b00001180d400d41d010312400488a0039600c0d04544045201910003038000a60280810380781468040c00885822180e4420075000206810100b17041d580b140c00c040d04100d4880030200030841d8248100402050010080420f260f52040c0c8251142c0014003214200300305581181c0c803d5809100558030344118008980c8610400d240180240003802c8040c1d100754600200d400c030b41c0c03d018642014003a9144035001d00080c0c10f40d0141c0007900644001a0420080b4210f59110000e41c0b0041055401035115207455044610400d0710704a40180414000d600b40f07a010494149094541310070343e0124103080072120041004070b049014141d4018045204841e41e1640042003402404150780e0b090703528041d241c0c5c0318820700060240c2a14141c20900c010850440400d407100941d01401d54145040070101c3d52 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 166718012 1250 166716762 166716787
    0xe010e0418080310050a180e15181e071802070f0b0f09010e030d0b010c020406090c0f0905090a0207031107060e0301180209040f0201020a051002091203071104020c03 73
    0x1d000048906190020901245440042101e8000e100850b6400112418484041c19981c0b90b50548003031140c485038041034550301440813081448501000304510310300301c600091507004004410080c3d002d240e903420200520341c00e00c1c09807550414014103056141001242d204810703c02e000c10302a90a000c403074000317511201420b241d103002e600344400300d041c4105900041107010b0482c1080d60314060b04002c5166020007603407851a80c0d0703080003d040c051000142d68003261800025803143c0b81c88400703d2126040c0d8003800c900300f42030b40c411613001c44940381543c402d130450007201c3d400703500d81300000c003e42829002885442d02c240360411a00030900401894140c4c103402c82404a2007403400c0110a0800b440340030781071036154030610741840c9190003241c00701c000078201800c41d0710005900e1042d64002c0011241080e03215086981107480812440025000101c0c802e100380600210000318400010603034001c2c42d00008041180d521441c1000700035400302c102c03803c50380414070030361301070b180f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 166719262 1250 166718012 166718051
    0xb06120c1605070e09061311010201060308030906092e050a0207061a040507091d0403020109023d0e04051914061306030305040603180b010611060f070e010e04 70
    0x14410b400500c1d00c40d051507500c1040010040a0703800c5503100f10b04015860000c0c3c070a0070801c5400a1035600c3c807999841c0100c2c00351185420140a0b94400000d00c0000a00025410b104607030081c15110f440c3c0341c2c0c00003c04240c2a10801c440031a90345400c03a002c64400e54003240c0c111000400040c501400c03942c402c016100340d1a40441900ba41e6048420207041034054640e01202c40e1401c0030300541081008080c0c005000e525502c141d210400140826000f5801325558503002450000702d20300c0404882c10740888000da21555001811164020710350001015005c203440e80c442c2d420040c000380c180301c01000d004202051064915080c046012410f10588100ca880811112000c0c07400b403080c011481c1c04403010081182c0342110400100341d001064905460462901042481030f40e00c1c0e420640400c003201a00041c3c3d8103000103007054008403039002c1400400b0903200d0b155500b007404603040404407401d101243c10307144580b03559071180020f0344400c8001000050214100c8503035a481c0c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 166720512 1250 166719262 166719307
    0x11701120308090706200106050a0e180309131a12010f15060503040209190c080f0723090310050106020127080d1e1410090b06120c 58
    0x801411201416409075201d40d0000034031001303016603071074924014010402d0300d84e0250311420a1040304200d540c00e4008000401000745210341583d11042181d0140b10245c5a80c41582c0c14107502c441c203004003000380d801001e8002c0c1601145c030b55510342c001c0503002c00d8080c90702001f00d120710010307181e0750403c03528801440300300000381001d8035840090850780350502c100c2661032a901c1c204071b920b40c4801129805541520091070729120340410794040c0c9403254851002500b003200c04000903170700c0001c4611801e4070481107000d075110b000007502c804040006c00030007050451405441040c9501c01841490f402504a68034007a62040d1031040300e4007a0032000042c0d44412922074002200700c0c8c101d101c3d01243c5d0010359100348690310a48184280702004180d2610341034a49906481807030f550380114420203051050745c4184646451200d400c0b550700406107000940451491054420f46490320b0020700041d24088803d200c04106180040c03481e21600010000010074441000b0a142c0c070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 166721762 1250 166720512 166720529
    0x1b010c020303070e01082415070807030e0603040b013c0602070e01140405060a0302060304060c09090221060a031b061403060d03030b0a081e12030603060c0306011701 73
    0x40b420020001440c60504c220080d04110380c0794244980000344240000450b080030800b51400b02c0d001c80410030500100e02800c074a15800b20f007603001e101c140b0006140407031080d96040d0741718104004005003030006131070290a9480d5031b17005100c2c00741d40200000c0c00c0c2c2204c2c5541c16020403510074601c070200c000401030484506801080040c0c0d0f40401404024100c6111012115814174a0100744c103030118519034071035034a41000c14516150f90b024003024540141c903c913540e140c42d06085000d8070703400d4041000140c1c01c5400007940d50762803003996655840c007016072001042100c280c446601c0003410f416031018201c48000000f900304001a20810812074160100380c0c90250050f1040c600d080321b54040007030410130000035958100c0b00208056241c10001401d48901d0086a080202c640010b08144a8071544150a0f007504910030f203100d441d8400c45540100684c410310b820b00080c0da019030961300400114810480c20380c0510350004062408400f00d0004048004048030280d018205 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 166723012 1250 166721762 166721767
    0x204180605030c01140304110105070b04050609060106030c09030201080a020c0a030c1106030601090302010f031d01061701090201021f090602070f06051506030a02071707080c070801060e0c1b010c0203 88
    0x2e04003406503008890b403d00b0310060030034940c0480c0f6520300c0018801466111100c40d1685a80c0c095415030307a100c3e402090f00c0400346050710f810344c0d41da881a203040d16144100030001030350354030071700030000745805507901c480c9520303d190300645000713101805410f01c40d034090100441e004001c00010034140d0080d0f940c1c51a44945042c101d00c8180c00102ca00e0040c2802c20800155980102480d012640d0a18010091402500d03007140104400c00328040402c846840160b400311054100c171081c0c480100b031184009000074209400c1b03d5860200034090382042d901740218208904122071601503031300010030811b409954420032071344403107021141e01d40e51481e07680074090039119880c0e11445884042015024900010313030b941c00003c0c5002110764000401c04100114a001011300b048824002600c6100510301b443c0650040d801c444000d110381940040e401105004210031900388204041103500c80411031200b560166a902a030021690200030005c4424071403010700c415240d001c3d64 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 166724262 1250 166723012 166723019
    0x1d0609070507020609010c020409200109080a170c0f0109050d17070212030a0e0f070e0c0f0307031d0a2003010603030509041a030d0801031109190506030102041806 72
    0x140050060844801c0003018415180141ca88a00300c5601c50000d013000b00c1280704900c0010301801c03401c01d00400060001000768903260403803403400f6012100742c0300c20070303c503480740f10301c6503200d40c0c10030090b0425904140240601c0b80c12801000420088002d880408014200c02400c4d520000c0341162143e10000c405c02d101039000000312041c1e62410a5080c02d0f0a010b14025a0385001742000c050640d0000086030790580035a005a0826450b50103803502e000c0c0d00c0901e6611958140301d050040b071400030009181540b24800c5031040ca004420903030454941c0c0c002280101080340ca4103100c0c003807100c00c04801c0c1004200703007a20b05103c0c07841c10440e1106101c84030755440c28016000d0007607050070001d04c0042c1e08034040d910305010035100056981d1100641000c0c0c8038004d00fa00ba018040e40b190707414070750382c000b401070b040c0c82c00750840b0000e891b03050092058420044070f03907c2146034a20540c0f001c1c58503e030005a0040f070f0060001d418a500c1342200d5a03c400a0b0501000c4241c0d240000c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 166725512 1250 166724262 166724269
    0x10603060515031f080a20010203030105150a02011401120201031a150f070b070f0806100e19051504030b090303041113060b03040804030b0907080715091d06 69
    0x30040c1500740c1c1c0600e912504400351008502001d401c000c5a40c3d080d4003e480394444030b00c10440184410400c44507281d1040c14624041c08000b4820107001504240c1d4629a5000000702c90403940302906a449840c800045069039411190301501195203444a24401c4c841c200c204501816141d00c2250000d991480050102c9400a00882514041074416080355a9140c801080141c1c503200e60f43d943d810301e000c0c1001070300c540d181c0185000c1c5000103000030107078841301d1419404d041c0d481d60184d07500c0710010414000c110f07608100006100c7c818001031801c00d110548014001c01c850200e0340341d04ca80c002041100c680b000c02182c1c56004c80e040041c4030500c00fa0340d8011403818041c4d86103051a880386041c40a0501000d8000c0c1308148200c05260700300d500010080c2600c0d071a0300d403070341002e10741514160300920017070302d0445140000c01c0e903040e0045800411103640c40001d0040d42e180128070700d8202010610700050180d03524001541412560080d194188080e414491524111042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 166726618 1106 166725512 166725521
    0x50115050c0118110961021501080a141204030804030c0506090f0f010306080709050702070b0c030405012a05060402030c060a0804060903170f010603 66
    0x4540510140d2100981c24a1003160a400d59807104003030301b5a505040c40a03102008050403e40f84082c400c0d10041303405861641292040d0901d50048200709100106120070248001101112003a418011210080800b440b594900d5041c90318080e03031410030ba00000d103250001003000800d400e081003203d4040d4801c008050352185c592070f258007a50482d2100b11415803c00300041050300c1c02c4000e0b01c00d480c1d00030300380a2421026200304424011201c81043c14150364020101d0303003a10500404028200d15a00440e140c01c1c40c80c8000d00d0244168000d1030b105405200610103042d000c0100c0702142c0b024a03000c0c844805040c0030803501c1180c111452f007000c5441a81c682040004961a80301d5070003107023504c03801400c00090250303500c1182c003c03000042e48900000d000910941c40b040826000389045180586842014858600c05451001c00c41d0304040040020740e42c1400f4 = true := by decide +kernel

theorem cover : BRFrame.Cov 166546762 166726618 := by
  have h0 := BRFrame.cov_init 166546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 166546762 ≤ n) (h2 : n < 166726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
