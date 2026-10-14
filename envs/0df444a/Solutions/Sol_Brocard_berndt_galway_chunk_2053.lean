-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2053
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:32:43.894792+00:00
-- url     : https://prove2.me/submissions/01f2268e-254c-4089-9682-bbe510adf3e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 369064748 ≤ n < 369244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 369065998 1250 369064748 369064757
    0x13020406091d060307150509030105040f020102010e0304210303020c0619060504020a051804150608071209051506031908040806090a0804090c05070b07030b01030f021c0b0a0302090106 81
    0x141440e401c01c841c1502c10124048031605071040281544000c10148215803d0302d0f05400c0300c0c1c0c1ca1136402d0700c030380c016541601d40641c41d00e0108014403010110104d8514001e800800000100e6124103491780310324010710b03e03c4d0000300141c0703441c0a59100025003040c06490014104814841007a0800c0c0e800e1310141c9243c0403044900038035007004d00c110b10040000310390440c601400510041d00358000c0c0c0404c040031050114980c00e16442d01d40003c2100c01151950b100340a8542c84042c00281050b02d00d01c2c00100c08003404e02d46401d45110301c410f0070707801400500942c0c150501601d68840000d0080da014064040000c00400c0f003110569092485104400d490318102014549011001096107125038012010440410b11820864060b1a4031110200e043d903403c80040c2c03000e10070203a008160b1900c1c1410030089590541c403544605200340c0c1c06003e80050301108406900462040d40200040c0d8440c654844c0c0250b406a500d1200c084c0142c6d81080d9680c00140c0318850036407210300440c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 369067248 1250 369065998 369066017
    0x703021b010903150f1410140310050408030411030d050912070801020406030603110406050d081305090c030411010e060d0225080c060a090c12110a0620070e0a050613020406 76
    0x6803040c060201d010140c051401c4292a0601403149595140d110745e03440d0141802210322303d61020b001e0030071032200c140d000f48150b0400b40380005103640b0848041c0e03100b811070f03000c5498511b00440c622050180ca0340d500c47c02d1030005010011541c60900380d0302d00507c222075000403106000c1c000351000b000140c40002d07009256044c402a81003900c01c54078030461030035400340a255102e00c1c03040125a003000529450799070302110240780740c156400040c2c3c00390348602040717402d2403035400a520445c402c07100d04002d00d60681c01910324240302c032602548488144034001c03200c0499405003441d803410001910400301021144010384000d180240e401c080e00040311180f1960400c02c035500111888010030140c0b41c0d54840708403c440341d00855030240d0242c100301c02840300e41181c008030a00c0003440c2503a5203907035043c0a4a01410f0b220301c403020040c01c01561114a60114190046540d0304114640c0c503502d01001e0130050800401465100b500054800303441040c41c80500007502c110b4482018a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 369068498 1250 369067248 369067271
    0x504052406132d0f0606020307050c06180910140904120c061409010b040515011b02010513030503090406090204060e0108060402040810060302150703021b01090315 72
    0x40598020140c0d50304000030301c0929101c49404004008a5030000189a180e860103c41c480720851256000d498040700c420f0114407040d44103442c40060000100511a92907a0990b100e010713002000d041500080318511281c20084020428800c0d100c1640e81c0901507180040c0220360155400c3c1c0c08440c00d56000d00550401c54040d181e004e80c2101c1c03002c0c140c6081c1c0e86070344030700103032101306001c10450f01c51400c03c0100d5600110b42c02d10500131402d00c1850040c5905000349484085c4602c602d0a01c4040760050b140304040c1c4ca040c00040e074860003c40c01c001080341c10b550a000c0304a040081c20811b641450b0043d40210000c5c40c4244082c2d5035981c100810002038030344a4001007030b540d2042004001061b00002d001000050070f007840c070f801d580e134100083c009000c0c13940700308a1030044443c40540d070702140e80a2000d691080394000d0240a090034288824001c8a9000340983e0160203030601c9580d501c400907110100514151017030544079030b17a1021004011806e44509a11007103001031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 369069748 1250 369068498 369068533
    0x32030d3504021c08030a020d06090204060c030e0136050303030f011a0a08220510090201120902061e09130504050c0405160c02060c0307080403030809010207050a0b0a0b04050405 78
    0x19034501d54030f040c2c02a000640c664480610000e0911440d15500144078a26612182c0043c402040d003000119111755861030302510100102404600150860a03240b08941c000c01e1070400440040d81e80089000303826603000380100c600b218101c904003802034002415901040118440c10000807603180c0c80d454041ca003242d82e031140d211404a44410b000c0c0c510308a43c410600e5900090031412190004414402050502c01400b405841805441402aa0701304542c008000083c800c1c0e80307403044501c408a4a108490329600000e5002e0070800904034440c941201c50301d0038001c010007141c503141201000a0900740401400c0342e03034544480410050240034001e200210b0340c16102440185002030001680c40e400001020a2100502e00741d82551108000e03500100307940340480b643c1d00440d00348140e9035003151204400190403200081c100740818000e850300b003035108005008201d1a6038074010046802841103200035650401e6890230f5507107004890299010741c010b003044e030310441c54800c3c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 369070998 1250 369069748 369069769
    0x6081009170c062212020d020d031e0e1e160915060f170405070e1614030a0b0d11030d09030314030901020408030432030d350402 57
    0x41420301d080c40711085040000c42c15551041c90020740c0340081185683c8404048090303007000d4014aa0110b8042e41c3d179400140c0303030b080c440c17803902251011105408101c080d01d00200c4c2031900307284d0044082c0b00c40d41c520741100840d21417030b9054402d071400340b4011900c080e075448a0500c656001100658000800100003000707050051828001d485041c8130880640c2120300c01d01c4100025200c10107580c1d0310410080c00000849080c03100242094100203075100007900849804140d540080f403040340e1111044050800f550321981c00c00024051102d400341c04c003c146019260301d581d1410340507074801c50400142031146001c01900d211183c10b040c0f9020102c419607052220002d402c0c00801c3d00521466211400012029600e03660500407074064025503002d640c0d24031011501103804525a15034025100d0305060681007446103690521000796070754202a0180c1082c0011480d40388100e41600d0007c5541c0003c900e0040318100f00c411a80c031040c8d00d845d404032180700703100440c0740000505 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 369072248 1250 369070998 369071033
    0x306150a0f120b040303061502070e060306010e040602030c043204050903120a150f030b0c030c0a0c020f1905040e1b011b0605070e03010f14060d050106081009 70
    0x32094204a09890141c46119015183c11881800242010721a40001300a0154028030031509002440042e50b0755210307000d584448c104850020781c1030b0a000030001d040301c2103a6100e4203681ca6903207032000203520140150390000c100f004003255000031030030410307005d949107885615030703800d1207a8501d401c8584c10708480c07240303050000380100d0a03800002d41c0e508907107041200f00702d91031305100c10000780707801504110b440061440c00034070200c6805121088900a0400e40b450b43d440d02803c485600c0201c4008620400c01d2044210880c0f083ea08404800d1020b0007440740c000000340090b4102d4240d60745403501c040c254800340301a0a15000d02d4005030075120050004400605950042502c3c9031001410005420300d00241d01c1c0c1030130003240a098025904210174280200d008220503e081c402038020740c02c1007035148007035006202c0d81d8458070b80c011120506884505c208400150410000da81540d25484042203081060004180c202c0903000d0000d1041c0340f901d440d0040c84040d80d40c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 369073498 1250 369072248 369072269
    0xb0702370b0a03050a2a0c06141605160b0408090d050601060f050c12070c0f060c0b090303060d1106040b030a0504020111031e0706091e0b01140a090c05090306150a 72
    0x280c51ba980140d540d181c4605800103400c9802c0441c4d03d100700c0f441c1404c4280a803c150814124068014000124500420403001400b507091b412200940c0c0c1c500c140031640c0c0c06d0b411000e600c4c1d004550034841e515005071150071854a4085078000003045000c000500340c2d481d410060040221542046950121320000e040041c28100450a50760f00c55440e00c007405002c2d100040e0800401c24002c0c0c034a0302030105100e0081c400c40e107891006004a034000c40444003080810085580042c1c00400d0301d10490f4001c10207681c1c0c1146076075035004a842d000056400c0031043c8404196030140070095803240310140030000e414505030000401090002814096035081042480070410801c45c0c0c80d40b200c000244010740d038000618003d00204281c140c09002d100070700c8200702c01c0003c12196400d2150084d102d4400700c2c1d0322105102031080000f040942d02000940c410045509260030545039403070346052181c00e00106402203414004210340c8246000000d17281d160140c5400d124560140c20040030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 369074748 1250 369073498 369073511
    0xf080c06030a020c011b1d06040b07030c03020f0a0f171213020a050a060509041a030c0909030d060f0e0f01150302220902070b010b0702370b0a03050a 66
    0x400c59a210152000322155000109610b150109401980c241038201d441c07044c1081e4141c0008040c907200f1806085c0c040f844441c102c0040c038002040d81d0540301104210391500710107680584a07c000c4010071402c0d4050b0041800313864009028248034a4018988500d1049652401000040d00398421850502060100701c0d43c041840c10019130066030000003400800f12400040c242c1c00241d032165900000d0990b01091072584407026007220b00080d5428010a41310011140d1030000141d122501548410300d05d400d01c2c41d140700c1454000204406607440e0618210080003a04c6042c2c020590710103d540c02003040100f00240e19910660041c2058076a504050400101803000f9613007504041d004070303400060500c6804141015006030745280c00450781d80103000b000c2e420011003601ca4102c1040006001155442110310040e03008080d11400780c2c41440342d4207415a000c0d001030b40140d4186c500309401e00c50f40c0c650000341c40c0084c41c194072064081c0c4014103035030000b072558401340d04022 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 369075998 1250 369074748 369074773
    0x3030304050d141c0209090702120307030915020403050705031002040608010e060316090608070801090c09110705060f0412030c0f03050a18151b08060f1215010f08 72
    0x900d141c0500740510b44422259007103205a1800d0081e142e034600c402c07074504c04a40f2070f40450b41c018010038405031840c03102540c038083c09a8584c0f101e00b04004440c8400c2000030181031180d40410802031051a4a940c42d200c0000000304a820540080312942d009403801d20507454100f00c0c0f000300c800c13802810340c0b4207410410010f00350201031280c910448000b501280856400344400c1c401c41e03c0040c0409881d0707950740b4002c405003a543c41b0b80c5581c5d01510b000421000418004c00a40540000300450310340e15081c018030052031114450003903228148001d100054061081d10b00501000b030320107900782003a0409411508112482030b09051a00755207210701904400ca44024014a040004990361182c0e07040001c2c00700002143d03512036810850404010000440c01044000300314100b2658078581c60505135a01e602e100e000200e8010000a40b40f8070b40340d43c1014020002614110350b0705280c0c03078040c0c609231000000c0309008a040340184265071031405800d0041c800100180307640b00080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 369077248 1250 369075998 369076003
    0x110901210303110f2a0a17030603010b130c081513110d09031e02010c0203040b0c0304090218040b010813030305090a080c100506040507090501050a140d060905060303030405 76
    0x440007030900d9210702d00c0c81c41c820030503002c0d194042c640c0d08803199a4110b200c41c2c2010049213913040040c0301c0c2c0302e2940d1020920000b41e01180c00307500c02440d50000e82040c2e003040300d54200400c03140c0d1540d01c41c44196115100e000748a000100d100c207000c40c901a402c0000f92011070300520001001e05195510035490350303244440201d400307810030002201222401407502920480022000c80c504000f45034040603440070400a40c0450000c101c0e40314040402c0072400c0c1d0306264000c42c010780c0706000920004140c2c0f1700800184500f002164035142d680d2800740c050ba04910791008a51640300082080c43c24180034038030300e00600f4600103d0500d4088941ea80c0180025800341c101036440303002851410041010310300f01c50b000b03140e80d510b80a240000b00d588102103404484800d043c1000300707905c0e08041c000c4901400d030030703195200130b030307013401e0044540d40c021103100070400107070036040412031155600511102c403008501154180c20a4045001d8400182c2494000d074003c008120214202 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 369078498 1250 369077248 369077309
    0x105070b0f1306020c1b0d0b010515070c0609090e0d020d05090a12240b010215190623030c090c0903070e131218060503060406090207110901 62
    0xd031018101c0c0751101c0d5203041c644118520020a201e100043c005441080003440e550307404220120140d500200105008003004012401050401c60600501641ca0311346062850060604035060900c40591191710001d1226404580480c5511400b8440d40c0c6840c0035042c00c0c0303622180201601d800d2117800175602d401c41e000d102d003084408101506181e0395a00c0d000010418203002d030300702c60f0391400c0c90b05201c42c03100241d01402c4c0240e60082c000d90718a0240904c00d2405070058500b003d0500045201c000d401019450124041103c41102c0d602c20311503600a0a0300000e42c1c2e01c00b0309504041c0300000300138254a880b95020315415201c03070307a540f2040ea520005041c10741d51541810800719150210075080551503501c000b00704490f03891001c0841600c42c0c024001c2550803242c0c07400c155095000e07215590782e2144ca052007400824043c90007950090009003000849507a03640340001245c01c402e03012641c0d81440c9448404900d800f01da210b024018400515107800c1e884506410000503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 369079748 1250 369078498 369078511
    0x1b0f04051b0a09030b0a06060306050a081c0c02040c080a0e071211011e1d01050901050a20030d0e01050c030603030415051c1d06060d0201081503011b030b0105070b 72
    0x800112a8251446108808011360780102c45e02101d05200e240070000d04164041d10000919200000416150880d610003c8910020240000c00b4034003c00250345900e07421690709005003c10b0f40c0005841e90b100d2400c0354115985d500720036040003001e00c02500d00c141d01c00741c06507020031014425203105240021890368001041d050807000800182d03801c1c8044074940f484c09214280e0482d009410071100141102c0443c0407412014014005481382d0150361017043c0080d0301801880885809880130980714010502030002000b5000611803442c2c2c4280c4085051a440d950030317401c1e41078240200d40d0011510a00b950451600700c0c0829920f0145101d0f546541c180078001080841c0104110b902d841040400340702da401c0c00c4030441010f0000251800782a299085028a0000000c601140600401811050402017580045918010251040701210360050b103110869400f403090f6004400d441ca21440703034140540c0b02408135040742e111103041c01020070440000448901c003a80d880003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 369080998 1250 369079748 369079801
    0x10f09060e0607050a240b0402040608010b07020d120f080f0105090f040c080123090d09090906020c010c0f11030301061e0c050703050c0a0501110d0c050a051b0f0405 73
    0x980d107080c200d1404200d03400c09452030081c1c8040d0501d01b10b040d284030081d41038441043c09030290380d9083c08101c1c401c5215220008100100501083e405a40200f007060700003000d42c26405680d031244204496904502c00c0030500303c00f0b601402c0343d04400603a51020318660743e030250b58980004540e007080c0c001d0941044005202c000b0f400c00010b0080301000d081c3e440700801c110070000070204907a030b11070380f007649010100d82d000843c2c0010000f4580700310030751540c50f0010281b8010030140500808002210340a400b4405500c0c0c0e40d000b40304a448440007a40e8a4104020020019040315000c03402d480c410f4004000501045070044245080d80010260451810011610032030789080490303c01845070140d4480041804000104458030400884802c5181c550300d4005407541c014543e8141260340021408281c0309004900202505004905883c803040d525501c01d400d15400011080401c02803110300010f40c00c140ca4880086102658104400c0c1000f6001d00914080900640c001c81c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 369082248 1250 369080998 369081007
    0x17072604050a0609140f0304060914030a08161703040b1030050a05070305010b03010603050a1403130b030f070c080933030f070203192318010f09060e06 67
    0xc01c24841e403081c179180002e0b01c604008005007039403694003d115000018080e0440420b09104c1c40381030180085005000b4070b801c034806e0341c2e84a403d405c1880280202c030705001d003040120341c10015940001c500d01502c0703580d9150529082c915450058044242104e0f99001807220741c1644034080b8a001002191400615003c0442001e034440300c10300810f14059400c400080010009401c8103891045c0c00900c910b0040109141c00c8401324440540136500441c05c402c003040d052204444030500003001e81e440c1924903c0c0e01c203265081c030fa100c1a0351035000002c2100450a04100e0342e006a441d01c2c1180c06001d25464045003801003120080c802d445c0345043c6021807082d0340c1d9000030490091003015450414040c0c20740d2940046600010044007040010000b40c404000c070340043c00b04008040c4442c0000d1011240015100707501c44030014458100903802414078060014a00c102e2494042455000001483c10f42914a80d90911199000a01903030b0f802c10400c6658100543c1c10b151503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 369083498 1250 369082248 369082253
    0x51003020a3009050a020f03210f040b040f180504081c0e01180303050606040f061103070501021303150b13090302010b12060615030f01050402030717072604050a0609 73
    0x65040b11840c03803888525090303003a07042000105407448818021107006440b00207070003d050702c0348001400084084c04060004115101c814054141c01d400b81203014142078403440b80c18400d5100d500482c02c21462a40c0c01c1148040c0000760b0405001e001c20306001604090780c504916000b564590440c0790070280c8a0407143c0c030154450340009a1100007031268004403545900c8002d0b2241007070300040c1c18100052280e0130b00104840440c0c8082c8442c842035032070113404035090b6200b200704810b207020412881020401c04d0001d0071074540c001c1580d00c1128514989404d540e660400f03101c00c01030030325410404542d00d564030484c0c12501d0b440302041030013203441c00301e005114280035103030700440081c03102c0000e40b00041c00b1480360406540c2d04000f03000008122a66010840b0007a035032414000052040b0300b01500616045901c42c1404584955a4440c5400507001110800006800c0340104c44c8141040291060342441c4402c11800c14107081d00c50a4441d07a00c400040c001c80c2c0c941580208 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 369084748 1250 369083498 369083567
    0x80924071e0b0109020c210d05060a030f030203130909050a030f17040501060504051b0306010c0c03080703030e0c0d050a081b070e01090c080f0718150801051003020a 73
    0x1407a5520008902c9250303141c1d00c2c1d0300b000350025120341d003040c4201164090307141618541d03c0305c130042200d801c50802d44103c0c003002c09030074001c3c82075400503a8200000f000a0860282c1e0500510a1700699113480b01e40148520506e00b0b540204860350030f1902c4000032403004201e03900e400d9054900180c01403072130714058a80c0c03003001010614105990041005210041d80043c0c1614003c480c1406644c4540c481d0900000e955551a044210100046a030640c01500708004080c8508070240640b83e036030321407100e950091902500425200c06018103030440c1800b165000c503030121007800001485460341d5035581603074000140200030009a1601003d074510380241d03412401d401303e40706581c964000c1c3e51001028461071009504108a142e006d9015404003407041002d14603459041d607405808030b03110300c24000b0800c18010444801f00f1103507000c0241ca0071002c2241c43c0c0c1d0301554985421710000c0407520301c003c5d08151052040e031210691001001d11840d0501402000342e4a0f10944180c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 369085998 1250 369084748 369084803
    0xf06100c0c0f03030309020301050604150b031506070302010902030c1c110424060e0d080a05090409080a030b13020a02070b0a09120c03060e0a0b180102040905010308092407 76
    0x82c0300c030220120020401d507241d0030103e1101c2c070950003480a91280c005000c151605050b0790100120f00041c18003207143c1c40b001070340d4408501c00c2500318a0b840079000c03601c5035201404c01d4005035152000c510075401e0410500011260540d511155482d11605d514410098806c004040d11074809035a10f5540e52500145210400907046204280048a40411543c500d02c9100049000da98802c8a076252000407855250f400005d003030328040000c0c1d8211426400560204d5109642d40c13981c0300401c0402010340b021103200d440014150030300d1404c1140c10b800c0c80000c900042d00401829a0199005c01c1001c200e803c1c11601d2070311059402c40c02c1c0c80c0c08400381c10500043e14070154910034014150078103011a40200030801c803810035010440d4030340d141050050701411442c0089640840c13180c0160400b168607400042c18152a1091201514820f85c001e6480c244e0124500d1800d2418103c41021007500c0020140d07900030700411400c00b0300485030301400c216041e44400741d05403145241c04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 369087248 1250 369085998 369086009
    0x30f1e02010f0323012405190302091908061008030306030a060b0a0806190b030d0905091b070501061e08070e0601050706050907090e190b060301021c0b090f06100c0c 73
    0x8646540c0c4481d00d000700e456100700ca034442150083c0454207030324080c108a4401e0108d07040800014511610b003900030754400031909030094442c50b45141924107403c891806050780c20b001d04405d0814140c0c45c0d03240b4216030006003e41e0000c1043c03107816500041c0c40c07500c1036404a0701080b44121080018003200680d44950050b0040c8801c018456980503001840c40000a80400c1007046440506607100701d17107011a00401e924420510203850580f210a601030341c00046480040070586034107101b500304810807240c178bc0d1a80d900344100c0b0382496000744150404e5100324202031030716220310fa1b00c000307621540c241d03542424082249644034030700b11032040350050f40502c01030804480c11603945506104240d1270a00d02030014420440104032140319811510b11b410f494140f0340c407014400c80014010f5581507500b00a0042039002e901d011111040c54100000b505141c0d1400b4828441401404208041104402c010095442d01048096041c261134200030017811171800d0030719140c294011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 369088498 1250 369087248 369087311
    0xa050c010912060f06120c0303031a21010e032b0b03070b0a050f0a02060f0f09030906031512060a0501080c0d0b04060902091305210f0a1701030f1e02010f03 69
    0x2071091141c14a00041240c9c4295010002900d4011041c0030365203202100c164841e0040c01c000c6988001c078955020f22400c400000500c181c2440551407440d400010042800210381c00072218212038101d018482841070023041c451114040006900c82800f4010744d1a008804146a04118415800d884103481041c0e41140d6039845210065502d4108850b200340003040c0f103002076801d820403a441070080d001c51000f107082222100c108001a000280f803003003040b00c6101742c0c0e502a40d881d0b0759500f510b080400540824101a01c0102c16548144c004500b12f910040c0d000c01c80d074407040b01940c907054008081d13400c01d40b01c500d006c0340030b8422103602940c4036641205203e5a03c0c440d03001920f41d41d109074101d409841c07210401000180700201482051039085c030075500300c000000014203556030b0f0351422500f00000685041c0d10040281c000b6110584928510420806c4180d155500e030740c0c007078005c84d6250101c0d0380004c161350310b0865200b0800d500c1d19800801241921702210a03115000035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 369089748 1250 369088498 369088529
    0x90715140d0b03101512021206010608010e0a0e0a03030506040e0a03030f180b010501050702120f010b010e0d150b0609040609020918070507030309030504170a050c010912060f06 78
    0x803118080c1040d8004903100b0f02440e820581200540d103d11009042a40501c030b40316071400b4020002601500c06c01c0ea00840100042c3c0254001480014060191900c40c600d01d94100031514005680c020b042d0110b040c9040c4111411250002d00c5084030f683c5842d004c1641d507904404240a800e0000c1101428410a02030004040e09038100301d01901003900b0811192041200202e5800d5540b240502030f59002c0e001840154800c1004104042c0040d04c030412492100d9980b9123014041c0e18880c4090755600211030296900922101d48000f0450b05052030150036140c2d01100035001900d1008a607070743c036600c542c580300d1200351070541d10028003c20049a5445103c006944001219072007041600d0380310100008000d4000d010310301c0c695a2604101c1c1d19501940204a0620183c081c03010a11000440e405511000380060f40400c002e8250058180b80c81490a5098000681882101e0105005881c81c0603001541c5503000140441c80112489010000385410f41103d001c00c542c2c0d25 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 369090998 1250 369089748 369089767
    0x6090606370504020d092006030a0507031103090c010207060503010602190302010e0109050a061b0206041b170f010507030225261b0c0d0602280f03060e09071514 71
    0x10f02c1200c1c0c8074042e1021920003802030481c1e130320414601e17400940c23184080c80441d8603d01c446e031000398002e2a40c200094200c1602556202d035410840300d01c0007542c002103440e8810b507030500503400103000900707166003154108240a0b45400d402d0140d03042101d0a0481c407418180f003500150307c0790058500812201415050181d00c0d81c08414090381c0c290b0400b549071801c80821128415441a90303070142c5403a4850b0303a21680195022000240082508a00070541e0140c6004e50b80e41c2c0960800200810f2603654030403400c0d00c4004210b00c4c01c0c184103001139582c030a215081440c03240d00608041034844050b1811f01d01c1483ca0b0b1442c1001c61100d50343c10b006511070b00004184152892100b5401101d03e84102d5564124291820782c1090b1600c440100081464000d0062175124544000201e40384032480300c03ca5121501d0300002400001079400d0080d05803190758007400410090b41441e1601c00701540d9038498911a2444419810002c66103da11485182d04445041c1e19550355400b01c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 369092248 1250 369090998 369091001
    0xc020f090c041e030f201903030806010306050f1302070516030201120605010f03091a04030302090415140d050f01020d1e090c0302090603010b04020c06090606370504020d 75
    0x30b001d000719003d085a44140456240c100343c2040782d81c810640188440e043e503410008088280038000c03040c012005141386592080d000c481418080007001c030005140d400c0007490100080e142c2818903103044818401c640b00c09640c000c05c18425a45961844000d500c1c1b90b0081c0704541000e000c1c4e0003404100c000e82a240308032501228000da030f600030701e20084205c10007280c080d4403a1a0200c4d202801030641d6a0098104612150180e140803e4172011030404683c550340440b41140025800545018103192a10880340d1016013500400442424250601418003100810034410005101c0420030850100159248602503000070364403407420050384c102402e181760708110004455482040680d20305e11030240595001a0243c00c0c00e49150240041e008015124903055500e4041011aa8441d800101140308154008014170305d00800c0301410064080d08003803045e06404c204003c100e4a80d003c15408602a107040f1400d045d4400c80b9150b021260750003180c0040c00401e00800d0318085 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 369093498 1250 369092248 369092257
    0x50d05090a0201090b0a0f03110909070206011a120a050903090a0f0302010201290d020f0301140402100807080a0e011e0e0610060903080903010b0a0b0a030e030a0f0c020f090c 77
    0xc0c4c96a0820b00d48030002d1007241d01500c0741000026080650301c51042d4401d40100c140c00602c00d201c9071410f540d04012483c1c9a07030845184016074007000040203c1944203c459040b00544c054007810003044122001c1004805170540020544502c0031074808041030084a000c1100104820316a83e556103501c3c0d4400c9071484183c0c0503519101d40800c00c007400044d01c0c007000c03c2c000000c04801850030708204654103d09426a00440151405010341d01e0920a07148064031008100c4194517003841001203442c072105980e010072603106c0501c15610380002d002900322124590200f80d4002c5455040d00621403900994842c0c800741101c0c2849401c65400350914803120001e5600c9a601d14262240d0fa20080c800c07a400141d6014080004c500944080c200302c402c0100040303104800500015500703212600320340d1614800156141035160107100300b41c41400d840d400b85042129a0700d01522f0748444510310070502c10581c42c0c05086540e6081c0c88644c00c2402010445141059030780c501c0d89401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 369094748 1250 369093498 369093503
    0x506071a010303081506041235040f05040e060f0a0e010c11010b04051513020408071e0e040b0a020a122406090e011a0d020d0b090c180f01050d05090a 66
    0x485080102e0a0070840120341c00d503099105242c2081c42140c0d5601ca4161b000001d5080c2e40e06c898180b103291800c2400403a83e410001c2744101d0311241800c4051240312429400a03104600c0c0910b140c40c0344030007282d0a5408840c1074441c2c4620340d51401c019001d00030000c8200c0e519403921040c1043c5c0703500b200c9446070310554100204110803800c014001210015034980c080d907207000311040014601602c600500d003511000142c00c1c10f039075004052a154150300140d0703400c5165110382220b158160b5024008084002c6d08050606054584004030607001d00b810071515000164480030f00c2c00b40c500c2c000b1074001d0700307420045070b400c0c3c3d013a4400d0305130641c4041c01d0701115441c0c00175420348900004025075006100103030299281442e401402c001c3c50700c0d00b803241070302404a0004188188003130400200c0b00c0d140031403c0080b180401540500c000c000801d4120103200c40800071b07030407100c504403031403054550f12581e2005400507107590144080401d0880d081400300b0140c1c21003c60041c1c456032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 369095998 1250 369094748 369094771
    0x5072a06050603160504050702030408010e070303030525032012040209060411090f0a0806041b06030504080702040e010f0617010b060c0d0e1903081308160506071a01030308 76
    0x32034030000c0540b5114140880400009207681c217108a00c0e107540f1040d00180d0b240110703858031765151000c03070960f40d40407551501c94016a2040040c150103001e50344d072010190144982020800c003519041840031840c5004040d955039030821460803002d01200303410401050107403542492101401d055200300c1d41203010b40c5250021545505050240d0b120381e5048009040c14110701406202c0782c405080138040c1d1145003100c0029050200307002d5580600d00a002010300c20501120f40f09004003503500042c2014500307010000071035884015038032920780c1100c01060034010070300a103001d4900038141a40305d92a150001409003076010314146500981d00090040e200c074074040051034007914034140b105401941054030118032908003c90350a0004000f0000340d248094074958002d5240c00c1101c8900c0c1c0040c110038112605080703c0000c0c000c503c01803107405108481e80d0040f4070740d481018002c5e00045003d40801401014100c0d10910350b00c5a10b000c0d41e9641002816a8411b80f43c011014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 369097248 1250 369095998 369096001
    0xa140402040b1206011205100501050f0f030c0d06050f090a0504032c01140a0c0b18030a050304110f01050f1e0f191107030b090c040c090f1d060405072a0605 69
    0x1b09141c3c007847c0c1c842c4005591540e0120301e4080103480d950b110b2440d640e55003004001c07003511124040080c500802459000d15100c04039002c01904442c40c540001d0f2003044114010886561a05225a0b0180303d0020214660729286070907a8411441d0b100c07070301c0004603c0c550500d80700c41e01e18084011070b0240d031080010718450341059168401e00d50744c03800107a001100440401c1d1054042500706045400c800b59807210b0810f850705541004022000141002081c40700340218000c035052170040480fa8040d4807501d500000c0c086208072400d41ca010a4080780100c500485810f0b200e1035503030301072040e60f034030129281c0000040d482644103440e8070410003e40010184a04054443c1c518440024100320341103455460805100a000c88540d03c03801c2c2c4081d4454580307001d00c082c1303a1255241c00428604080d000d040c011481e401c00c0340102d41d0800e4000340000307000d050070f80140060364006002e0321003d00442d120b6031416651030b4a0b80d0040741403d10840c140342d18588060198104110300d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 369098498 1250 369097248 369097277
    0x30a06050f06040f11030411010c0501181106091f09080a051c02030c10050a020409142502150402190e1005040c0c1502190309140c0a140402040b120601 67
    0x100c40148205172040d500900000380000c1c121003c94444140504100511008540e649420340d121030b040018015813090703d6004215071081202d100c031100300e0f40b00d4100180c0b44045000300441d400c6400d540041580002000b50007224004050100a4107850f9405101d0420650311405c42c10140700a0108001e000000c0e80b0200958412554000141000e180740030780180103820090094642607608210004a84801e44a90903000c00411101d8101c0d14101c1d0b8010900700210066030000ba50324804010860790101d0000d500083c0800012819100d50011484046441c245560081038404000c40c0d182c00c214400d82c403e0210541c0c1b1280c483c0c40d9424842030324490b42844022460402107540000c05400718104010201c60b401810617440c1c03510f02200d014213030100030100b90f5446038031080c00448802201c4114454008050700e0700002c0101c2c40000551007034a4a0592100728814503607201d4040300c006100300c0d05280e07101c00d44541c01e00005407080d03944a02065846094020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 369099748 1250 369098498 369098501
    0x2030c03060103020d03030504050313260d0e09090c1002060a1503030c0602160804090903081f050105030901110a110c0a030305030105060c010b0a030620031003020f030a06050f06040f 81
    0x142ca0780a01905411117181c2c0d420f0340a490041e1044806000c04d1044008000c000c0403000c0044c68245540510703008500c00c0c01c17520150310104690f840d0403192210032580d40062189079510819142c01100daa0395401c4241000e03130103241e0b56402a508aa00e5000590000f401c9000e8229050100a661f80307050308040c4968662000501250084000d400822405e6000d0140180045a03103d41a10b1590300c00b00c8560040e0020014141e1301d01e404001e2541c8180391135400503031905992054000080340050052851080c02e040000000020314038083c2900710f420b0901c0c40c0185a502c440e41040050200782c004140d0010702d11030b903c8081514580702c5030040c2281d425459051031039090409010440d07200e04641c0b00c0964840070150f01e00e8444a106c0c0d0001c5000703201c0002c103403040ba004c09030380700300020880c5040b0f2003c1c014007412080c1454850102c13941210186550700b03038140800c0c1080c00c000c4015082e54a84030820540134a001203051061900b10b40401840100340e44240 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 369100998 1250 369099748 369099751
    0x40915080a050c120109020d0803070207060801140909030f040b04031127090c0a03150b150301050f01030e100c0e0a080a02060a0221090a120b1911041202030c0306 72
    0x2d041d0b0340158000100c5042c0b004450003010f10b1a000411000e84c035402080020748044001c49540308004200701c0040d905107c118041c001c00c1c030f00b40220354582851444921a0300030700c06d124000714800724440500030007c0f62400307000000c03040e8843d80d5540c00704986400c01d1205030340c0010400582152171605413003401000c049034210008458003401c0c00703003c005000701665068452a40303050030340c1d41e40260702402184034501e030b00701d0f01843d4031041088d59006103d9600400a60409001a403106415039055542c25901e070b9107540961401200a01480d0007030500d140108503500d400041c15402100c507400d155164103d52000c1d01c41402150603041c8548106600040320042c0145096402000040c030b8910444891708090122230b03100440e40e191209103403000095040c42400d28044820040c0b4503079281e0f90001d04992542000c0ea44010101030b109072001c044030311100e416034401d145001280c219180c890783c03912070712180005a80c000740c0c440d12070b801203501d0520340002c00c20b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 369102248 1250 369100998 369101003
    0x62214040c030c120902030106091e0c02070f03080901090302130f05061c0b04080702120a2105091003060803040602070e0603010203091510030f1110090f17030906040915080a 77
    0x40d1501e02e4142110300403d1780d00303c00c90381035495810000352607181c0e004041056055892031070490b140c8070034000488000c4240c450642d000010204807681c01c1044e0031044030380081d1003941d40d58601d00126003465543d08000e5000c410110440d0031008a1f500800140010b141c042140c1d0300c030002082410628454803400f2080000c202400280c2810011900f2912400d08542032200d1a4002010b0b00c648000c800103a900100c0d0060600a11020004071020000401201c107010844010854411651954003803000c91100c00c2c1401d10075441000106203c2c01506d4680341c0b036000083d21740b00e41d8070804150803440c00106a8626041c422240114101001030008450500000040e408000e00186008003003010000c08201034458aa00441c4640d075a034007021000c000300078103100c100804a0410003030103c10300207500300000220271b41c0c0140c441080d0b02c0180500701480d600c9592949900600045400503244281d50400003074a80c22006030f40312300c1d44845e061a955461b0302c001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 369103498 1250 369102248 369102257
    0x7120804170904090602220b0a0512091009060509010c02030c0a0b07110f03030103120203030f1503030433050a080604020d1404050a020a1d0402062214040c030c 71
    0x7000704080c00301c1c0c0242581c400280c03011070190404d450f407004a800024080030720401c1000c0d21b44e44031007448550300107043c2601e40d0609060446500a12600800c071030381c2004605840415510482041000c2d0244000d940a2106200311715056000d81025a000c90281d82015050420180040180d640d00080e0000600030340e440d070380303845101c0180600b83e00c0900c500520401c00001c400c0c44114280f110303101c000c6640e945545052108101d900b028002150010310501240c11009030940c0e4206210b0307440b82d010a0503041c0028158450b682c0415014142249484106050760020103811740280e40140404901e001e015105442818000400100c15000180d90b918107903001c0c151401c21a00c000400c603c0c2d05000c0020a03000392810781b07041c0d101d41100001c5180044003040038003115442080c600c1c180c41010a43301c400a080244941d00c00f1030080e2080711940e100402c43c2d085a642d0300449070b40c0e24210500c2030024400c1d24000d5090118264016020380907407440d44100f40d86 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 369104748 1250 369103498 369103523
    0x301051e0c1c111b070f0501091202130b0d0309030213050115110c12031b0c01020a0b1f0609030302060912041518090f0b030c0609060304050111030c07120804 70
    0x19110000d00f5081c900d440c01c40d4061052044250f03c101140300300388039203401400c0740c60500c10701d0b4180391150390013941001a201070030f020000050950500040e419240030064104000c403010140109401c49504514510440b0044c0342d031101028040307030b0080d40c020f54801002600002a103009000d03040310b4410300303143c03010090310402001d140c8054607019100349140410000c2d50800d419100d15149500c00f007182c018249050740301d440800f00c404010103100c180d00001070341b12982c3e040080c00c00a4254006032000031105803c10207101c80480040032039480d504050a1080a4041a8010300c1510006a011180050440790480900801606213450600c001886200907540142080001c07084000c0e100c0c0c10030307503540241154503001300b004071601403414103c0d11070210051107540424a120b40a8031440103e810480341505c8195070f9035100d061090140c802c50007840740d0401c0c000200141840c48001400c03040388100003101007144080701c201d591200649024020003800b00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 369105998 1250 369104748 369104797
    0x115150207060c0302030c010903030b100f1e0504080609060106140405090c090102010f0c110c03030f09040b0d0c06030516020a0515070201060803180109050a0b030c0a0e0301051e0c 80
    0x200c42d07080c10f51082c811070f89021081c1c1d10310360a468494004602103900e5100e90b00ac5441c1c600303a051400212854510300c4624060310082a01c07038050780e01c040000b42d482c5030f0b04000344a131f012130300a003e0b40340c1107a180782804034025035210401d20030107001445a4030780d020b40500610071070301124030040200c0100d481d500703802d00c0c0c036600c0083e03014190f40d690100c07146c032181c403070264030440455602e410f140d02c504980d0070713030802c60b03c0742c0c20701e2190b00100903d60744207c5620940d0b0014405070350006904000700e001c01c201340705a00d405014044100b500140035549a08542c2c400e00400c1c4142401c045200800e0b40c1d1100c454900400b240c0000701c4680c0c407900c40402280e4080300034400400c0c420390b5a0242c80c02c69100c0020a400461444501034495800019030f50003170405880c1520241d00c1c5c802d0703810507408094405410441d0000b0a40b01452162072506142ca00040c02000103082810141032156100c1c1000302031298001c000411030035244083c0e4203110480e03d12104000b4540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 369107248 1250 369105998 369106007
    0x108150c0d02092205010e07022107081201030602030411060a0804020111100c020c1011030f070f02040f0905011a0d0308100b070308010f080d0c0204200c011515020706 74
    0x221054200c07107115503490005984400c820382d60f00103400c0000d640d504110081c110300800a2031001550300980c0c2a0b48000ea0312410481c00028850320150bd0700c0c0e072454400311500c52f983e800c04081e0070000020043c424035a005500462150b0341800e44400d1500c14420360307000b44d403039403404030b001c100002d0b0155000c3c10a010b401c800000c1a030b51158080d84940c8200d890b118084001a40700041030740041c1021020b4610444546c00d00c6400c400b911b80140340d030f900c110050800030040104103070040010010307400181c0c940c0200300380050136507064208002c1202081c152501d60034080d04c84104100b482c06514005005171601c0c8609241e071b2416590300601038104c01e80c07080030400000c3c1d1260a800030f00221403007544d80c10f003a540f6042106504075001d03000080c180c1c00090603d182d050300840c0c2010340d240e0503100490f880b016800035110310360b00c118aa100b56800014524605141984441c0743c90000810f42404c1546030600000000c400a4850700580d100c0d29041c0718140c0036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 369108498 1250 369107248 369107257
    0x7170402041802030616030509011401031214032410092102090702030c0d0305130b090102190513141c020a120c03020a05121e0f0a0b0108150c0d02 65
    0x202e403180110100c0c0e03011a1170400200c0780801428007102c40103540e40d03410300880c0e410003c1000207000e10150140303144100070713040c440240b40a20b00b400c020b035060302a560100031200711496850702d038070707196020100d640415649040340e2000c0c03a4990506282212805050042c1075490080c0d150030215102c659001c00c001c01481c4814001a1000580e50988001d03c80d400641c082c58540b058251034510f06403c032f51b04181031604041c20005091083e010b08116030780c10034104405621075900c002e0082c8a80c0e1034070744c10300e941d900e11054101d800c18024041d62100c203090440d1255100d160849680b0b8440b945540003414110702ca03513001111800b000d2090000303200b40d0080355100c4030010103406a204c215849840048108294a0a17906080c010141078440c2400c50140c0b910081e1070764031250725181c0790242c040d0003801d6408100030400002c10042c04071a85c2c10043d060004082c842440350305c00d03a2080040910f07400c20080002400741d108007600c107003460000c0e04842c02030b421 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 369109748 1250 369108498 369108521
    0x90114190f5d0804140907020d031a0d051501090e1c14120604060906030812071b05010212070f1209111f020c03010b010e0409050a05010903020706080717040204 71
    0xc0d03601c04030b0501c550b11020450b0207100f055003c1e40e5524140100680d503144922961180b0468810031414940100c1c2801c041c84640c40d001a0075a03840c07000000c0710740c00720300c4260009a855466001c000002415102c080c8041c0c842c8041a07070f880c0400d0082e2400c01720407003900e402c08440b5440032821007400340c03180c038480d003400300c9401d05040f045c4289401403001880014000c038280500380c201840760801800726140148140c900750340f85c10500b1303c10452034184030348908000903220740c440e40c118203d503150441102d411243c1130a1240c045d410060241c1981001d89000c60960750049101d00e0540743e40e1b4840ca2100c02000305240028090160b080d1000601d8552001041d5285c00d11005c0524404e500310360b43c2003030700c0d9000789030404489401d8002e83c90100c0300c0302a0303030f00001000811070049070701040c0c07510b02e0b141c41c0c0c2c2000030b0094014050740c00e0603080780400d0780124031070050728820b0740c442c031082d650442c0440e142c1e1141e640c1c0000d441034000108001d0704054000d02150070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 369110998 1250 369109748 369109889
    0x30201080408040801141b0412080306030f03041403070510020a02011d030d030614040911060d0612140609060c0322050d0306090b040b090114190f 65
    0x96132280080d095078055001c00c00545603800c2009441c01d0712915502c000400003c620342481d04000084604000d041c00203082100084001000d6a800700044070915005d00150ba4503965108003501000c0440b5032424030034040d441001c541814041e80140802240f680104029000c41d00150380701101045920807403c04c086080d00070707072820012041e044400c0c0d54002070440c0f030300c03110f43c44003003410040d0752080e82041c940001182c090480410041c00450307481d50b981c2e512105a00c0244400e078000741421910040d400300744021486500201d02170030342698420780e1049241e0341c40704d07811a4000024401800810b0448203685a5440c4010490f01c003c200048151038452903c403041c8888070003c1d03120700d01409940c03030074040c4103541072054400388411585070000440f03031300d0140240d04008440503114103a607500c00f0750b25a000300c0009078440100391120401204103001f806590030381d40d440040010002103582d40c00c000503401034030604000c00e010745d0301d44014010329003d424a9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 369112248 1250 369110998 369111007
    0x913080c0105040503040f0602030c0c040f060e04060617060103080a052b0e07080c031506010905090f2a16020a05210105070e13020d14070c03080f0709030201080408 73
    0xc00c0240700702070140d4060380095848919005a0702c3e011700f03039500303d0344c11500144a40803a18000107403202904e602210013060b0b411640ca042401040c15a202c0c0d007980c000d020a02040c40020381c08031050f5110303083e240d0b0a00740c1b03403142c1275680d84080c40000d140c15020407103460354900c6040a44180f1405100d030002c44400551380d40a842d00084801d5110303542c1e020b4030100c2c01c1040041100418021010340010740b800000a41c6809104991030140030514000844503842450b13903074040d1a00802140003818141600c442010b811603180c4d0503c0b5024a0300c0e441c081c010705000603551b64055103c1d2820b048941c0881281c962143d04076004a41c0e43c4010600c1c0c3d40b00010041c904800c01c0850912011a4480c507003550b002506203c103000c64070f007440e950740c4c64ce002c4101041400c03410259a5442c1e80c1c018100a06a640907070900140510600242e6644029224030700e901035680c2c00c0d0140c60b2620010251101540d804001c036542840400055004d0042c7c241d1003400b84030414100b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 369113498 1250 369112248 369112267
    0x150d0c0902180915100f050a0818010501060f020d0206040230030c010e011112071d15030a050703151401110601030605040308010914010b1b0706050409060503030702091308 76
    0x169030b41910089401e111111403060759042170710846451000c40d25145020100c1c0c1c00f000741491280001c81360420540c54000340d41c4909140302e8400e400d500d600200429a5200c90041040342589410001801000300c484401c51000079601d01580d0000c00c5160312265403008004102210403004e401d0b850180000905100240007038403416000c0390020503200000516a07084a5240c4061101c10710207200089035640c0b504007060340140c01c1c0c14519509400e1007031600002c4138218005511140d1205c0d000380038030307130320018500174003900c0381c24066a25905002d0301514164042e401462440070010014407460340f02e01900785d441814413500b007102e04040c0c02d040140c02d0704296070752902c0705c091108060b40301074000e0040101001c200900c00c03219075146407001040c1b0558403102c5000c82c0b001e041400300c2c036100da010407060040ba4104c640d00c010113030403504180f1404c0f42c1e542c0782420000c1c1c58180403085640e610b50081208815554a4044140c01d101000b4140c41100081c4500c000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 369114748 1250 369113498 369113509
    0xf071a0d1a1306260309060310030b040c03210c02280e01030b1807030b06010527040f020406140d0207050706030f0b0a1508040305190305150d0c090218 67
    0xc086a0080d00800c00b5402d01c4d800c02070501c48140c1081108040d0000d5800038072001c819103900201c00c44902d0740c0c9848105006800080503000031301800d81403000c0c0000c00030032015200440740328150351980c01c03c8488e0440e40d0305005a546502250208800d08014501091940001c05e40d00d070000c00c80101d20440f200d400d0003103030032100c1c40348150f01c014400d11000c1c101c019800403066260001841841089503114962840014884107511022507596070164055421100d44880b20102d04511441c046186812018003a4041e40c640240300c94191403d0013114150b1728903842c0d00c6607a00070069104029480214038031315aa6081c0030000c00030b00305105500c02842740d9a0089009013840c1c1442c008c5a600842062041c44c1c040000c014200307403403604078182c01c3e003030415240d2680e59013026100d82c46a0000071900005da420f10b604074540543c800d0380910b802580615482c6034130300c240140ea4a801002610440b08400d007000780c0c40c5583c0041c040380c41416020106031148202050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 369115998 1250 369114748 369114769
    0x912033f06090b030601050604090509150705030619080a08030604020904090b010306050a02130302011b06051311031b1306080316110d0b061314090f071a0d1a 70
    0x4140c0352503007020400980240114140c5180860280210303500d0a80051389a00c51840340c016182d4540c800210803840c24003903445400d40c3c1c00000411440c01c06801441c035402240d95622070641103c410150b081401e03045400d6034028002080e100c022901c52900c103404c001c0495500030b40030000b200d1705490314010403014a104240c040d0303e550444c6014010b50754000d007015001391040c4440c90303a410030300d02c41c0c000702c90b020b00b040c021001d140210080341c00c0200c0c0d4091305180c00e003400d0024030b0202c420146155030190074400d04e152403000401d0781792281511b00f0a82d40c8100800450300c0d02e40321565100c001061440006c07031503602c00020703045421080e20141c0c200c11107180310061199800760900c501800f00c6004000c03142e10741e2a2520b040014000d0360107403640703c0c106c0d000018268080032040505055a519a1409014003030f5200301c9011203180c940a018000540050b15101450600340d144c87d03080d041c900020a4070004244a00c10350580c81c1480c42100c5d495100c0c106004c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 369117248 1250 369115998 369116117
    0x20d2a080403140a030207090b0f0904080d0608030f090f03030409060803030f0115120f1409010603020f06041d130b07020d022401121719091203 64
    0x854075240755041c1086a00705181001501d9081202d805000036804154001601c002000004140020b500842c1a0260341c41c0b0b5950001290f2003800207026101000e01003981880005100040d2185002d0b80c40780500c07100600e03c0f0f80c05001d03c40d100d207040c44000b090010040c045a04142da500103e1050764055440030090740c0000042c1f00c44480605561405080100c0e280c2c0410741d00480000e15104000c803545003035a550361840303400f43c800c6400c42c064a049010341b400f654180f802c3d4240c020200340c0300032072240c0c40b40300c541041801c103403040c1c41c1164402103524048005003100303084030314401043c07418021b6400302c4088c001400030850500408496008000c54102090080e240410310301c100c003007202903100141d20ba9440344ca04981540c00f110f40c10440340e800c520b0004d0360720b001b100b01e8804455002c94214900d41e92007174924149129956074000c0e4654600500d01c00d110344001c0030703000940143c0c04901d0445a00d500700500c1c1006103104105141c07800001400c0b43c05000d10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 369118498 1250 369117248 369117263
    0xa0509011d01020a03030f022a0d14180301150905070f050301140402091201110322030807052805042c04030c05120403150516020d2a 59
    0x10281559000d22580655280c060a5000000078140080c3da0341c20f00d688000c04050315004480070407038007601928000e803c0c00c020f0310728008040c202c5107114002d146002c003103031003121110840d1a03c01d41300032038822200c25031549841e4010542d0180c1d00040001e01e5019034a80701c44903400304180060322700070003200324002101c0c142842c0c000d141d83d004261540401c003042c001400365641c640f080c078514a60407540140c0c1c40070b160001c83c80010300080c281506500e0141d0700041600c2910040d807142c49541403548042102c00220310030b0a400d81406000218010b00240c906070050f0010141c03443c1c5001ea0811016400d6003202d105240004c891000520124040008160100300d511801100340d000c000c200f45a1742ca0b403456008020400f808100071003005005010040c04401207006940102036a219102c0c01e2041004c502d490703403101080d140200040d04002c0031f011700030360301e00d242e4050095051285801c54151000d1141202000c501501c195241403a0102702403205109904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 369119748 1250 369118498 369118507
    0x60408071b0509161b2d0803070f091505041203030e0105190e1902060a05070c0f0302210a030e0a09020412050d081303030507031e1a1801050907140a05 67
    0x300100021410584203017444441243c07400010769070b011040700408880c050641c1015400c20a43c034104082601800d582000002d03c103100b640242080419565611240b484513914415029180b65174481c01e00041c0c000c0c40140706a882d9070440d0b0542c40d00a16011a803480c07030083c00b0342112010754651103400710303079102070700320841c00e0041010404c0414003a0041c1e207000c00c080190310400c00300c001e20624000407025074050080c03041d20520b9422003031070f003421600c403080002c4402840c00240d200c1d0811020001007180314240c3c0301c410b1480a0064186010035503410313940d012801d042d5503400041110f0102e0490700500c090070089c00700c0c0012809071041d034213105050010982c0c2d03e1041081c41410040050001009805803540c18900000d90303903180042140200710510308961a0000340011707081900c0640c00691102c071b500315000184261440400118081103a1011021020b00340104640c3c0742c01c1c2401e07a0311016030704000c0003003a1458483e05443e40b0088000010a0002c40c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 369120998 1250 369119748 369119791
    0x912100f060b040f09020a05070519030816050a031a0607061d070b22090c050c0d03050105031b0f040c080a05060109050d02040203090a021003021b060408071b0509 72
    0x1e200020705945402030f140c5800c1a0f030102d050090703402420002600000c1500300103104000b00d811071500311054683c0168031641080c0d510700808400c0c0c1c00281c050300403130540c0040100c1581c15070a0307030700c42c9403034500c1d201cdc001d030003519869180b5410070388000c0b8a03017015201c24006100483c8509000200d11065881c0390140c0e1103110034001450707000500078400e100c0c824003141c80700c82400c101d05100381000b4070f4402c4500d4080c2c0009101c2401c0141c00f000a0fa044805000032801d142c0079903040c0440483d00302c0441e10244201c0e81d1503401480201066090306019240c101000340181c01040c81120200e8143d0742c1d00042c42c40000c602404024203032003680b007104c1c0c00000c00d02e810f600315840c10000940349480d480c0007920031507002003c6801d01504021013020150301411300c46034070490000150080d040680584614106001d03810101d00d40452028440c0c1d50240e40141040c4c4c1d10707110002c2c0c03615000c4200c0314440681c1408900d039616510440d02c01c82d1182610302c0c2074150b00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 369122248 1250 369120998 369121001
    0x3031503061a0114070804030f0606090903052107020601060e0607050316051903092d03120e1519020709020309030a0f080f010302060307030f020c0c040e030f030c0912100f 76
    0x40c030f00701513a04401d026000004101500b01d40803a80c2000818170790755058140f0b200200020390044048520701401c030b104054005000d40250024145100300d2206041100e540c140412503054005030401070040c00541d020f489522521440600f400d410440140d90b450316642c800c4441421511080c205402000010880c05c4582c21400f0341624802017644d40240038143c25028080049400c40da40002c1c400340388490352100040e86201c01c141607078030304100b00705180d1180840c00240c050403075034245007020f0030000c10942c48014941c0c6040d04052000080b40115180c5804501684d4400141c0d0001800a58041d030030342c101440e43c030300007040b01904003044401d800c1c2c00d101a05040000281034419140d0440350151060707952550f5552f0b0407001400b000c100d0060f02880400c070302203854400101141e21260580781082010a030380c0c20700d650b034060503440d014180c104100089142c461100580f4880034083c160f070114203030844101d4140003941440314071141d07070381080c5003404004e13 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 369123498 1250 369122248 369122267
    0xa0f0c08120711010c060e15060a170a060b01030204031407080d080708060d0303020c01020f18150a030c030939120204020c150f0405060106030b0d03031503061a01 72
    0x4044400d15165140e40c840c1c0c40410841103040c144817143d034004050020300e800c02e6070030196041c15240040d203000d40f07910440c07406585440c0a05243c0c5c00104103140c001801c0024040303480c1c028104003600340e032100302038180074000e60304149d001c3c44000005124266050709032038082001d05041d074141410b047c6840e90500401c4d0401841c0d03418000b01d10340090509810903402e881c080b240d01e40310306060340680f09901030741031250310008469200c0d22072800034080b503596042901074076031020010080b040070b15103c2c3c2d64096804101e401d076803074000c0d40242c044002e98100441d082c3e100340c40d44903800130045001e1103290b4410b100c160140c01e02100700c2c0d040d1007202911102d15802e00d01038022079008407038020300035907001030411001c4004201c1c003001060340c81017003d007500c1d040710740034001d85040d5070445082c42410008551503000e405030111401c0e014090342c07069070712074804501900c0c108245628900d41e4040c04004180c00b4010340044181c00b00e5032a081070390300000141000003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 369124748 1250 369123498 369123523
    0x1d0312071b06021e0c01080718031707020a12170c07030203060412020606120303061315031a010602011406040513050f06061804120503180f0105040b010e0f180a0f0c08 74
    0x89005c0814451381c00448080d00403409141007000c0305554110a40c034034145800213010941e0014004082015410082600703d100740c5080c000f0942d24520720040048010380142090b00d0011540c042d54520005040301030b10100880c1e203e981c1d2a00400c3c2080420b440076514100144c100d561029010400c09800c00000c1d586d14041c450030310b03902c90f1680000340c00c5038801c1100d40110005070b5504c1c2c01001d0000501e40b981840c44e90b40746055a00120608520001034504100004401d4018425456018188085003441d036850740100002044000c04811001610392405008a5400c0245000c03100d10200241f800341000400c010b5070141451b18005540c0b0f002040100013a1141e00c42c0181142500b0059166142e145010010444000410000c1d204a0305041d11424054003c0360207540281390024803030340c03514102c600c004000c580c1140780950078808904110006420ba81c441c120034415107010140c655030302d140c000f058010070b4403081ea1001c1e090000843c14450802c00b403e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 369125998 1250 369124748 369124753
    0x180c05072f1f0e0a030512040306050c160f0206070605070c050c040b0310020901020708030a0c1a091f0b0a0f18020306030a060b060f07050d1d0312071b06021e 70
    0x8052002d8420b034122035040820481c1c42507108806403038078811030000c2c5600c04181c44264070040b030000b5054000c1c0c407050b41c200382010f0104070381080c0c85007280c1c07601000086a80420711145c40b032480404c9a80d000f04d0f00700d0010405000803803e03621500e4000e0380999078199080103281412403070302d4000c51260b80b1071842c114011506903000035220b070011171204005a15007090b00010303401d201541d480308006020002d05600390a5000180c1f5030514401c06021500d940c801a00c060304600440300d0150f0756024440d411003111040707500f005008041e04022501410742d5022802440c000e03400004041004079060049005022a5040c1c002d200781045080d403030724100099582001550241031641d48500c5040b445d194481204c00c40d80c450000d456403140586081070b5982c4900d12040300145114440e00b10350f1420110203054040300070014038200c1c031000020103555010300002c840c02018181846040e003180c003400001402d01c0c1d0050090a5003490102c0821f581c100402201038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 369127248 1250 369125998 369126019
    0xf050a140f100e0705040b04060b0a02060a05070e1507050705030d02030c070503060f01120809030a0f1b180f09050d0509090a2d090b01080d0e0307180c05072f 70
    0x150f4000500f6011203004580105007072280d40701203001468650001ca40b01c1c00002035201501b90000f4003d801898030710b004000c10b0307550b0f4104480a400481c2c82a80c007401c548044409000d168003e406501d005105a43e0400d90343d800003031501d000c040740d0002580022888080641c010b101900c020041034014116a20385800b16182c00b18050113500030740350042d03c0800c00e219400303043d902803040103000c85005080c141450b8490001d0035604440c031a1001070040d900c400c8422036181100c019500300000c45e0050181c0401901d5824000403446550705241d2000c160100000409035166803220f695070a042170602907801c10003800d00078024103118101059008984a030b034000480e1751050911190241200786c06000010b402034500c030f61010011a0382540481c5a02501545d525407050f041d400f4014591107840724401d588105032500c042c1800900160411942c0074424a4041e00d884040c1c0d40d80180d0404840841140c8480034942d902c6291070882c901c424410304940d8120b00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 369128498 1250 369127248 369127271
    0x14070206010627062d17130209150d0507090c0f021606030c050403020d0b090d0c0b01030f112806031119051e0c0d030504050601030f050a140f10 64
    0x30703c081c85944c2c2000301c0f480a02540c207014400210142c00c0d45501c036819910350903001081405500c1195892032400d00104551494200b20500907942c05810701d10740350b03140090840350300c0c00090f6103508034840800520004206100d410050720301400c000505020001d4018640581100030314299442200c4250404421030150310485a0700d00c1d011648141040c0c0c11a418044c580c0002d412040c284254400c200d0203900702c900c1074409608030382c45c1660008088070070021070400070b402070102c0001032000c10000000000a039000c3c0880c2000c0c4c006040102e421070321049158540c559803410100d8100d82c1501d403400c0100b00724a41408480d98180c00d42d02141320b031521440400c8820104e0340745050007103003504c0c2d0111098020054030300700b004038221300d6131143c2d5450782140140d544070711850307000380b044900841c1c000c4000e120981c00c42da514140040d5107207007600d89205800c0e000d4000b45403214040030082c040c0020708020401c003440b0f00c4c50110008490701c1080d0800781500d10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 369129748 1250 369128498 369128567
    0x90a03080a091518050c09220c0b12010303142106040608030d0204030b0f01080a0b091213061e050307050901110105010909021206060112020d140702060106 69
    0xc01c01800500003034015401d19200750322103d0a145610501d04140c408402c8840c8010910b903450b001e101503950840700e01c0100003401700112540d1050010903001e9000b5610711021403c485417003052903403035031903c0b036504902a40014222801c8601048011301c10107901605000b0710f104100000c0f420030842c098500500b607000100128000381440000d00c2c15580c80d082400100745080549070f0704c0c00182c0020000e91712030302040c0c4a066070704003c07604042c21440f82034102c641d440d001d45202c0000c0d6039a00c041031800b4020001620992002c0c105400b904c00041021000b0440c54560700341c07800b54003801c0c1d0504150340c1d0541000903407003160b01d41c0d0010126a8084014a0026a5004d4140061b101c0d00081001c00469602e080e00114202c04254814140c0d00e000b201d0900c42d0718013440c0070039600c45003140c1590001b501e10352031000c07241041d006080103c0c1d04460106031002100a401d440e1207040b18014016400040100030041d000703003100290041c1d0403076424541d07030121804030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 369130998 1250 369129748 369129751
    0x604020402210a20130603021c050a05250e0108100902031905010f0609180905031204030e01180509091218011b021014090402071a090a0308 62
    0x90140d5000141101842c0d051901d0b404469400b40105655007008050040206413468101306000380000c2c03055014080c0000b0381e02c00000344250800c929003072010860194008941030803070178076a004003038032900c1c0d64043d03540f103500120340004961400002e0f24200c030801d00c076000d0b5842c1950024a40480c0c0c0710354150410682800d0407070403512030f42d0403082140c0540d4484001903102000303012005406401c000110740b11098141700592700d41c10340445601d10783c0f0403000401d03403145d410098240c42d40c3d994401450412800140c42030151125802c60703129841001011040340e080004043c0c0120755000081c1084c41c198661212294409086241c9401200d10a07503007a000200318078410018010042d400c0d00c0800e49500e4880c83ca032041d0800d5500700390100d0142d4900c0000301e07a804004841784d9070002c019030351041c20a001910040c0c10241101c11600c0304001019644d11140020020b031849400b0040303008007182c00c0720250580c090a446041e4014a0f03d80740400d51005005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 369132248 1250 369130998 369131003
    0x50708070e0d05120705060114013b150306150f09010507110301150807091e0504020a0f080709270201180519051207061d01020a0b0f04120e01020604 66
    0x26500091418010310b403420104c036946011100017404004c01c40f000c05c0180c122040f00c84014a0a0354910054818854a4015907000110340c00640a00e08603140049480304402001000982003140410342d001511045440340c98800000d2141a0070424850030301143c0966400d03046c4100c000c007140d02d911542c0b82040c1004bc0100c8c618061202100e07413443c001100074000c21034a8a186280d80c0b0808a030721685a140c010301000160b40c0515010b4004e580b0340e0704a01c200121000c003c61401080e0251003640c10040c0714002141200100154a000e000c003240207001c03162130134080c030065078501d00710025025000f5000128588041034020886642401c100e00d46044151030722140c00020341c0b0056004c4103070b546400c041a40241000c003620801e8551585a040583e00340390b071203100d446074800003518400400e1010706209070b40201c48405106450399103800340c03114042c1c1c4005880c00f864640b04081413100704104038001003c80c5186080120b0071512450020b5203440004002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 369133498 1250 369132248 369132259
    0xc031719020c0309130c111203010303030c0e09011e08030403020303071106070f06020301030308130506060f03030408060a020d0c170f040204060e0901090b060102122703060a02070501050708070e 86
    0x2c0b003a081042c81134402186002e40500100201580d503032002d80009510080442e00c2100b5101c698003010072400c46c07104644026030300c0c591031741c2c1e0218000c02640e5142010404c14051036942950713000c0d0071500030008410780aa6200700c01d6030a034030740402544200980c0e8810001000183c40c0030003a680c1d4544c008200d06401300c50040420058840c10800505c4200e1021744401040020382c041c40c141e074040c1ea0f81103601d55072601100010003181c8000351155100c4800120646000c007902c207200580034080d44e0030036603a41e50583c0742000650b480400b45401040815603c4224810b4100241d814902000410301c410050101da1320041c10144119140c00001400d54a84e90028030040c00d4081e6001c00750314000005500030801520100d072828586004a0500d610001d80081c4000e5240030342890102a040d41e0071008450403101d5441b01c070015040390307883e68140105445a404100e0245c0e5074540ea161090854000a007e6414130000006124440764007189884070030300207480 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 369134748 1250 369133498 369133507
    0x160f09051e0d0f0c061d0d0609241a04050f0a090501320108070617091e1e030a0c020f040b042d110a0c0309030c060c03171902 56
    0x125100a00120024140000ba906903900300072014000d80121444d0f031b641c4030115200d8081c0c2031110f4900c03036015584034090080107000303e9420f600082c0d19521032894600005070380140301a03108824204e03103090f2075451486402c00f0b610000d03a48607501085604110500d4201c40c0d0111300c59014200320225a6914900010003d0950042950882c42805100d4818043c2240f02000400c0d0740001c94900300e00000060f80140010804141c41322611031b5861102964510ba200001c01009422103100301c101c40e0401e0074049001050f802d440b10064551344000e242039444400350421850801e81c01009a00d2400341c1c0801280301c8580d0484081c1281042013001030054940000032076807140c58080540c00c0080c0058662207420b052514041c008000c01d800070003200c12990144d072403901c1c01c102602003135100e00c044520541c441d003000d00403103403241c0b0790300041082d540200c03003c176001113100400e0640120700c01c1c040f032a620a07900741ca4900303020075441c2d00c1550614400c3c003980204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 369135998 1250 369134748 369134809
    0x1e010f0f151e260f01060b0d0c20060106021603120804021306060e011403010317090a030f05010902090f0405070e070e041b030506010215010e0a0f0203160f0905 71
    0x180c25001040400c16254248000b2100758105032100c04941840f80b00c1e0f880034031100413040c09040c0480708900c0400d400c200d10354030000042c154008040c820800210394142207203415100c0c0307580d500c02c00c0b00140a0356042100103403910301c5c1c07810640c3e103032810b0301020800128400114880071040381303000030300360300c941c030110f80100d020504c1d8a0310941040d10124440d5841000c400000703500341d07600f194800d508500803500e88801e0101900700c1403ca10091103da034940c004125030700000d008006e4803076480e107800010f94188142227601740d440d80190000e40c0303050503e00340c200803000310300345250800d5610603a03146140d110300c4d0824202180060301c80340c00341c0303035161069a010f44107000c02c40c8242d140042d4070f00c0703081000011910b400040b8000707510002c1c4030300184840074071074141c80c2d00303000c1d8104016000600c1d0f0f015007611074980c442040d899001441c003c03241c048581003881c20003400034001007034801581c401c203d102d44041040d0b644c1c9450110090b00c20304980d10316102c60b032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 369137248 1250 369135998 369136049
    0x6050d050c0607080c010c020607080106050a1202160804030f0c09020a0f0e0a0807060c06050703020406050d0906093219140f070303020d020709020f0a0e031e010f0f15 74
    0x498017138410b520384004110580d0700800c1803441000346c0c1c0d4a51619a0b00d420080e5114044c2d91841d10004588603100301e04091203034020110402c00d01070320a1025184e5684e80400d5015400c1202c00e03502034415130007004080c020300d0b80645007412040d41084941e00d0000d0020801441d03403401c00034000400e540c0b9848600705c0308041e252041c191002c1316101c9a01900344c9400480450b049491b0500080003584240f0035501500c202c1e03a9058134103020f07801d80202800d500d440a0382c03c2c0ea41c0d185070200141601e05c100d030101c0314200c258000481c000b03074080640302207480281e00fa60030058403507500340301d440300c030314446640903285048103071007500258030700041a00b400489215030f00000c800e1540001c0e40000c40c01d125400c0f1a0759030b4803410901e05030300408032221040c0c8000d00081d03084902401c18101310b0400501201c50003002003000b8501c2c0483c44007401d003565900c0c1c4440d9011500340c003a11640d40c0500c0c4040c480303a2a003100001440c00765204821002d46941c0d121140745020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 369138498 1250 369137248 369137257
    0x40b130204020a09060e0d02031e01060b03070f020c03120409020c0a020d080306090a18030804081c020c0d0804020922050d02010507090509100311040f1407020106050d050c060708 79
    0x1d40115100c0d402e80c0400340510501d80116030205000009800903454165a0915442c2d4041e000d401000d4408900141c2100035200401c0b05541319480802d490000e2030182d07110340329968420350b540c2001d480280c1444c101041c20b5009411090100404d8070ba100c04407021666400401a81e031030354804070505050b406d0400940c412000e10601007400099409180204421180c001c544d0b203a0101c0320044138050101c444401c04650401c001082c0620701e011380c0540500c12440c43d00c80d401c420f9802404540c6c0c0ba040b012076000c0b59514403810100071242c00240c2a09010032a810560005403521000a02041c2c00410032020011280b07180340e40591555031182c121154114440d001a002e804111030300c0300001c5029034002004d1903c04942e5000341c0340c542d02c04203a070781503840700c50401d0403100350b050300031f034603800b0544c01041c1070310940d006c1c3c001c0d00000c400c40d4102410001c2c00d41c0c0071580414845c0c0b8243c09504042100031a900c01451011030761030381d0f14013451902031080c0c002c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 369139748 1250 369138498 369138503
    0x5161a090319050f0f16060e0604150f09021c0b0108030406020705060708120a09020906100e0103050a2c01053105101805010605031b04150f03050304080f15040b13 72
    0x4001c101c0d58100c906d1076040e0f04420740316501c01e000c08e04660b4111951303102c04031005490095503411003048840b8590007108900b0038940007140580c56600400d90000c80c44103a20355102d0102d01000a10088840c0140940b4490f0099443c0500c0c042c0000d64501040c000e862160800184100405c40c80208071071541015000140540c23401c0d000d05401042c8080090b4083c0700100001151442c10301c0c1c04003401109a03d42185070302c00300e00114010400202400720340ca950340ca44941040c55281d00444504103040b8211310f100a00f00610700707558014003500e116203011000d400e1006034040c081140550305a1900000b58028100349140c900310308450600a0710344101c80520114840c842410b03503015500038410959613078240340d52100c98404a01c04500d02c00401c1c180c614150700b16440b506034103a42ca0301050349034400e0007510f9800340e00031a51a8030010b405c003c040c03024420400c03e1000b41000e02059400a0400700468a00500041884600b080001d0b0702e00b802440d01480a0f4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 369140998 1250 369139748 369139777
    0x90d0206030a1d0d020c04091509060b0a15020f070b09010f0324050111151803070b0a14010803040609030b091e0c01030b190b070305161a090319050f 66
    0x7003103e030405455890b403622034401400307190a159400d003824016000890b50050000040d000410408001000d6100702203441c96240d40c8500a5950b03021150400b600c50701505c50f05281585d01d020b40381c0341c1d194203200784d00d40100c10200300742c140c21400e840400c071082c00c04440014220201310000c00203a44e65403640840400300c440c40c040c00640e884144c602c2a00c4080e480005054082e6541c00d0a42100c0d44510f000030005040840483c03200300c0d5602c0321421203003001455039400c0e482c0d1008a038842c1c1465646d003c41e4541c0d076903c242d5540141b951301c01a514281c10508000d145c04c010340005441c841d4110046421880100064114102c0e04101c0c1d208415044074203984402e480c0722880d000909004e200704040c6011039503403a1900520101c010428034200c2031490503004030703500703600340103042c03100401d0131060281c0c001d4480c0c0b01d5074104841c884031040480300d50300040d0460f0107943c003d00c00d0080038101d8031082504080380b800c2c516152000c05584140c98429000300387c002e01d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 369142248 1250 369140998 369141041
    0x4020a0306050f190b0f040209040b0d06020309071d0411150d05010608010807050a15020c0d061416020a020f03120705010f051806070c020a0306110306090903090d0206030a 76
    0x8042600005008403913824100c240181d400ca001c4056038812509280c0c40104080340602d41d203410703030040c408080f0141000c60100b09180000c3c11a8072500fa055031616000010002501002e000c50340103002c06081d500b84c22038a8a03110800f03e100240000c00780f8090018048041c0d4614140c0c1125426102040d80d403180341c8200c0c10301034002031085002058401d80041402d80000c01c003c01680d5014001410f0545041c2414140f0450b603200d0700b0543c0a0100c464441e070f1035001da440c42803401100041030180c0345d110340818910300100350300503040e618541c1684095004c0794282c1000e170111503c20801c15240002410300380325102e1a0301c5036800040c00000c100701074002c031860021401040006543d04400c951418640130792600254001000054039036025012226440b8005410310300c01980b00d60f01c3e40110340c40c3e600880d411100102c2005094646014820740c001120b40c040c5042c8200c103400f0864110401c20020302c00d681c040002001103405600034030314640301103c141a403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 369143498 1250 369142248 369142261
    0x3040302090702010b0906100c0b0a1104080f0705061309020d0b030303100602120c0a08030703020d060303050304050d0903050c042a09030c3620090f1905040504020a030605 76
    0x7172500c00300550180400d00c00064032860281034003d012030a80e100c0c2c00d094201a5502c240c040c130018140d40c50255070700e08035480b103140f0300094000b901c3c0b58001000c1d20000407910754039101080e4030480c46590704000e6050740d4404550240101c81580d400561100c000003180d0300600400c2c0255901403001004100160480031901030454080b50240d03104003480c00310010031340c850740c140100258040301c001c00009800e0001107503c2480751800506180e101581c1e00141d0344903030300a0f8009100070003400107202082c800c145400c0003030f052884005207103030741e02c603180e280302880548115528011515011001c1000c0095054402c1c1c0a44801843c01d001402d0b40f041c501040c0c0f244a804800440c4281c0c0541c000c035402070020703c006801164902c00011542131024201c140c080c1c072506508000748289245250f00000d001c3c0f030701d4461a85805001e89400010011403044460000499030903001002580c240c450540740800e4136030396170000c100640c1440d88010811450002000390 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 369144748 1250 369143498 369143501
    0x60b0f0a021029040b0913020a0803030103051f0b01170c3f070203070b061206090106091803050301210b07020109051501030b071808030a0224040f140304030209070201 74
    0x108080300c100e07400c0c900c0c103c031401d001c110707017040c0302d165000741d51741002c01c500350f1022003000f019510041050036200c0d118402241150001e034801c44040d8404100a40c00301b29450702d075520800c0702c200410000d110400007d1500c00f0b49142c02c04800301904c0810198481c0400300c840010619040420001c4a80d84012640c40820f001100300300b42c5013480302c0c032418005441030041e01542d00550031b08945454400c0c20385000381c1205d9004942d10300c41a080402844910300c0307104c03005c00020b005803a001d00601031322185031006204400b0300c00c0150010380c2050541f8151864a55400207041c180c00c3e2031a401c04425a015040502c0d100400401c40c0e030540185041a12842c00d64006034801524405988001e000080000d0403400004101500c161103401080314881041c0e01043e98030100a401e40c0d02c15034440300160825104d50030300c02c44085046507010036255031085245440c0e201c2410406108500034481e08041c903003c02000400c0055901560b0020514074032401c0c00c0303d0107030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 369145998 1250 369144748 369144791
    0x1d09060609220e0c040f0216120207030f080c0609071d091e21040e07230c0c01020606030a08090904030c080a09030b0a050c090f18012601060b0f0a0210 67
    0x1445076050181c061b12040c070b80e000780c0e07079842003e20103060a84807230344e52080c02035035004041c0218421300500101059071032603120801e600406440f82d5a5400c3c075900c901f00100107010140952210070f08020310b4446084190000b001d902044a190300d41d000102c1c1024040d40c0c4250201c00310038521442601e001c10758030400c4641d1341450a0101c0e6425131500680a188135488504a4400014800500a000e06040c008038950075076038800314044112215009189807000581c0504942441940c041003420f4000400710000d28110040383d654071300394414030341240c1c024100354010500f018090800c803420164040741481d1a085030075001840f14800344001d4039221000d03000708803050741c1c501ca4507028006002102c0e20300b984240602c1100b00d980c0c4041600403501070b40094640d035140300d60a01a140030348442e807800020204984075074199022600b101d901d000002c11503407d07044200c40c80154000c81d26a103603203502100340d00700541161001030550404c00b03160001907003a400342 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 369147248 1250 369145998 369146023
    0xd050108071403070e15090405070503120310090c0918051b0c0a060c050409090c0302010201111318390504080703062007031d09060609220e 62
    0x98003002d6803500029181c503901c01605070541c000714414070594640f01540d40d444001d51455035050030014000c10700c042030454041d074540d0001c1e4010f000529040c0030098002c4034128110b8118108400039a02082039442a01036069841e03c150b20300c070b40a080214020104502c04040404a040310100030b084112200130040400704101c07801c00c24920240e60180740c050000345158282903917504000c0c2040e80340b14003030007003d0200144240d403a018001815104410010752240b8502c00a400d56041000741c41540d1000d02401c2c6400800c2c0d0002822292950018100280715208400c01800b112142c40048401200c401c0103035075001040c01c1031503907440e46405400034506800c40e071038000c500401400303400041c42080458030030342194400001076950180d2032290202c0304a0654820701044021400d01010780b086a0500e1748880c0b205442902c81610034500900082d145101d022510f500c21390109400e142d02210103c107594010300903040070020000c0500c211035444050a114 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 369148498 1250 369147248 369147253
    0x5010e010b03040308041511040801020c01230a0504030512010806150105040609180e07030b010f0e01030b07080901091e140d05071401140f01080d030c08060111010902060d050108 79
    0x80c8141c1980100c0744101d80503511040740c0d482e95a58502c6601c0c0504403c06c0640d03c481c1c035a40b00100c81e0000300300802400000590b00c0440301c0c0e03440d00790341415440c50800c1c10000c961800140ca076005180c0d101580c21400500c41d44c079850151458090719a039240f01d0303803140b0004070b158000055580e0262030310345d550000b00c001903001180c0700d20540c0134000002d800303000c0820440c01d0307a10b0040404481d111021580c49440e50349289807144540c015200104684010032800206128000140400051281c2258190385801020703800150206042081c18000203501600070b501541440350b01400c80a00346040c0000424a554249020f032003101c0c1c45a040c0c03160542c00240100310b072101c1d880740c505000194030fa0151a07020060203441c1da54072507004000365035456039038512488480032900480e505114409150940c0185c2c40d00900d843d00d090300c0030303140d0005805940f1000902c0c02211140030b00c51902e000d031426010080d0000310200d800e070403501183d000603051b1100700e400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 369149748 1250 369148498 369148501
    0x50103140a08160c03050f0106181a01050a11061515090d020f19060210060b0901020703020402130b0412050d020d0807120e0f0a0b13110405070c0b040605010e 70
    0x20303840d40700e49200e14000d0035003204100100070180c054600e460954002c4000301101c681d60b484450904108084055159540d07076400e01c8000310756003101d186003c0c140d008101c0410384840543c032100039540d0540c14442d0100320a00403d1069100c0340160003940144c61f2103003001c020300040d80103d138079098401c2e200b264000d10340c50b602c041944c0c100f0000a0480400204903000c2c4901e0b4800d00d14074540000030381136603400340a8001c49d076900a0015600500750201c200c0c00c00800c4a03042d400c002c040200401250a02d6031740080c1ea0740a0301d03011500180c1d2202455002004030f0080d901c141c0000c5804a400030320720751100c2c1098402030082081e119680202c60080380c549140000c1e050104c0c07003642c040344502e48a101041003a030074011002030407001140e09d0034942004404580c402d6441034001c1420048070564413a00046810081c00080d400c1d40d0301d5020710414091910b000756071311000503c00d1071043c1000c071340b403070340082201d4000c4c28035041c4600641300900541102087e81c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 369150998 1250 369149748 369149783
    0x7231810120b06090a0302040507261e0f15040e100f15050a060e0a2601061403070501050c0312010e040b070206041106030406060521061617040512040306050103 71
    0x34102e9494000041170820002d0440e0308100003002e0250168040000480a44140c6550300010840408440000d440322b1702e006403403260402c10002000140340e40c0c1c0c2e0180f143c00e003080b000540d0080e0351030b4906440e144104001c00d000344031900e132840c041c1c841c5080c1090b42103426030284902e106041c009100e00d81d840000b0340f07940c02c0544074241d0031200440c41002214030072208400d000400400c003180d056a101420201e500b07640009507559554074082800c1d4807400d100c0c810007003064200e0003014040b41000652104c030a48030700c505020300020b42c0c107108a018011180c0c01c8404103400c0c000b5584540d5580c4810340100ca08581c1d0000660100d6a0f650002507410710030740e0320040d0004500c10031424000c1c80d41001c2c10442e441c0b40c4604001c107099603205204050888480752890035021040b007a10302d0020042d250098004034410121505580000e600c2090082c0e2b500c0c0a0b40c40d1540d20300b2034602102042e50740400701021a010042108076002a81240c1c081c196030010683e182 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 369152248 1250 369150998 369151009
    0x20312030705130b071e0303111c0f060806191103070309030215010e04230d02100f11031b1204031d010201020a0c02100203070203030f07060507231810120b 69
    0x1008050043e4180b40c130380f4000c450131b0450120302c0b039200f40b4000c100100085201580c40e000110700202d01c9400c44800804000c2c240301d000c03035078a00518240612480c1580e1141c541c4000f41503240c0600c0d0704190102c44483c0c0ba00b004540182000b1055924584150020014042c0880c1107005000d0b980030064150b046e00b07101d5040e164002442c2c2034580740c50750f448070608201c1850210080c80305218072840c4a041c8200f140d000300d684c015000c61204850080102c500c02c0360556001441d201d5280307072341a4014141e90340a08100f03988d002e08101381d04180c1050042c284010030b0340c05040104030400d0b500c00a0224043d081c0c8170fa0480002c00300c8016800d0b401807900010000340c4940700800540740c2110031100028103030041e05d20b0044540c01080c19680921441000c401c400942207040008621a1691204961401419003c0e01c20b140304100a03503a000f00817031400105e244440c81c20203040403220390f007008000710043c003a14200604003032a0741c000e0508032460207182c001d040c10007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 369153498 1250 369152248 369152257
    0x30f0506160905010c06140a0b01030b0d0c0b03040f0507081005010902030919020f0a0e041e08121012060c022803110a140609060109090803040b04020312030705130b 73
    0x1035120076291600f0400111505070070441c0c1950301035104c000030f800c0e0704090b0480a0107600302d61030100e0143e1100c000501910480ca80b440e0041465584880c04500341c4a070a60540310b4100850350fa07916603044c105400c81401d41c02404a004a0b00300003109c180018101411348600b42092240380c1e030ba840d00200728001144d03034002c99004440c0020104501a010510181c40109020321814510002c00c5030803c1640041240440b10b0003440b00f44500707100c0d03144081420342c04d01464010956140403a80c0503a40b800e241c6801241c0200360540181000e4601034400c0a8140b001c400b820b0500c98058003001c10780f2030141c0680304942a10302c500001d804581d6107034407505000c480c1140d40440c1d40c1d81da201d008401a0040007281000500005290320b81400010000d01090800c0340506081074010380c1304a0000d440e2107406000614040203032a40b00c2d030072102c0e4500301c4c0c0e02c80c000f0a040086500c00c1c500c54400000c200420716402101404002c101c9205500b0060346840e40c2e02a039204 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 369154748 1250 369153498 369153541
    0x90f1b07110d0609050616090b18090a0b030114070f0309120f050409060305030a08070201050105180a020714061501180b1608070818190e07020f0601030f0506 70
    0xa440c1c1d42580741002c0d000480c00a1040c0340c001421900c0b51505424a2415644034a203115480302c3e00c2c14503907002d03403550040c0c004c200b0b469240c46600d0491030304000011010900503625200007601c083c038254031019414401a0003840300101300341c40541c10600440c0c402000c00c041800d0380110341d119200da000d00030f90112600c2000c1052020a542c82c20303c8080c001d00304070040202103805800ca00800e030040d44900021912000c41440240c45480d005110f44116031500c401000165620110b034041d01a5600c2081d03000d441303010520000e80300d02940946a411002c1c403210b01a140001c080c0d10450306118080354900c00700004542808078410f101001642640c0140014004c10000f000720301d6150740300d81400340141c2d540324525084010b06031414400030840c0e10801c0a403083d000018507003103454003880051540c0d0511205421300400480010880000c0c211074020020005805d91f000101d0740e0a40e520b10344400b0004402c0804c0710789004a4010920349034103118440f0500c06c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 369155998 1250 369154748 369154763
    0xe15030a05271609150603022a06010302090708090705010c02010302071209090c0f0806090717130c06110318060405040603051c02011b14090402040e0702160513050a0605090f1b07 79
    0x61801c4c101f100a500008558600c804a441c00e00c1180c880c0d80b2075603030f40003145002514141d851401089901d1000070100d10502c4801740401c0404140410004241d400908014031010140c0c00101e0080c040c200c0d00421030226202d0180070030350031413003030070886118403424011100d041008444181c840340030200450795040100c0e165260104c0e100e43c0c00080c0349844907421015035000300800c401514241c4880700042c20750010f00903a0344c0340c1000703444d090404204040f01d0343c0d95240c0d40d101d030464404041d0a6820320084650300c1c941201c005000c002c00600c00d0640301e0402689034110750310664848074100d250400c04500600503d19401010124104420790101055a110f94403110746045140300300302030b12150341c0b00d20190000d00b00d81304007003c8600c3e0115001e85010110b034185080246d0100c81080190744181400481035511a008a000d440e25480040a07090300d0300450390050041c0b007000303040290007441c13512520300e2040c049000d036546101c094551060308030141ca1103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 369157248 1250 369155998 369156041
    0x70512030d1a090f0403090e010e04080d0e01150906080d2001061a09030606220e100608010902100c050303040206030402061909060e15030a05271609 66
    0x100c0c650b4003240d01c00c405a002074046189400000d90b07071000c11030341c40c00d1103850041444141503011807150050840744a0031300d442d505284c51300261190081000704144400100a01900c210740c102824039690b4200034850100e00c84200e401e038019502407400200d29204000404171000203d20180c2141c50f1540e4802844800c040300f0555150300072030000b90f403a0040003d07000036a00c2c42080c000090040300c2e8841100c081010704000f00500aa44a00b69a801c02d103000c81072104a4910320701104000100a0b241040241c00c0c00401075151180074a0b204001810351410342150608520840d01d01c01c0064070000162031040356840c0140c110f07030041c80000e0050400741e0085030401e00081200d810107100301030300400c000c00d185060000130503407081080440e400c144900070240c8101d8550b00d11200141c2c1d5041c1d42c0c00300600d407000c2c0780d8850000c207140308450000c00c21741c0040c00002070740f40004d01010720b0b40d480c0040345e81114002442c3c0000703007410982c0f00d41b5860840c0140e505410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 369158498 1250 369157248 369157267
    0x503010b030411180c04090c0e1f020703080c060103060b0d030203040509040303090813050307050105070f0f0804030203060117060a02091f09180b0405060f150708040b0301060e0307051203 83
    0x10420f002010390700300d143c0040e001601c1e541a2225441031240010040d6554104102c2c1000d0752084403000e400d0140310354040040c0c0e0740c2c105491591140c61030741b040704800d240000300d00d0901540d0014049601c00240f8651004010403080c2c16a4010305061040c06d0752031092002c0c00d6010100540107070401d1000b8001440d02841450304039005e8980412080c205440d00300580d44070798041c14081004000810060905000000c002c103002d090150412105885500d862150020000c00d85941c84941804004076101a90301858024040342c59540c0c4400b10702c02d2120310b50340390550f54406c034030004510410b607008540700120080c110344c04486d030100b106400003c4202803542400070000000c0340e0261400290420390780100c0c3c000c41c103d08c04405020468402402c0c40c2e005003010607049115459503004450a1480d500f04ea995617403590900c1c101d00e0146400c54004050300200004007254000000640d0307131811010385203082c3e0fa41c8104841e1480002c0e0080c500e1300140b14000d41c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 369159748 1250 369158498 369158513
    0xb010908060c030903190e09100b090904060f180b010e010f03110d02060f130b16082b1a01090e130312020d150b03040302070b03070c1709100503010b0304 68
    0xb0401e0b15081164180208076410040c4119845646c2000403003614a82c082450054a801d0f00190039050031020603080c440340407114801c6900321400340d484003010030204051a8001c000c1b210001c201040401e028001003018180c82c0003007560b107404660000b05141d1788600000b41260505007001480301e02e565038851031010031880081d401056103d0810145e1a0b100c007d0001014a046980e52902c141c1048c444151140d0400100b66900380690101c0000c1110f15880c80c58000c40c02c9616981040c141446100f036040860344c10354848001c007001159150040504011a0704040b90007288003130044800104a219412042d4032440c0424150301076200c0c000111400307440e14100c0d410760084a441664881c10341307002400c1c1e441221460304842040c13590040c00100130014510706090324020344d40d00490090011903a000000300c1d0a9170702440c2408815a44062200401c9088071582d1806800050f4000d015605415480049a114030101c0e816603100e40101410754480e0740329080d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 369160998 1250 369159748 369159751
    0xf0702060c07020d0201020109020a0f06031a0f09090732060a0c0b0c0c1e070b130302060f0c0a050a0201020105060301020a0804120203071505010501030c0801080d030e1c050705010b010908060c03 86
    0x6d0540d580c4a020401584a144104026103109500c1c1040c25203001c2c4020100c5103941c0310904001c00011a180d019030310090b80c1301da040c0c8100c0c2c042e81c00751561440c2c2410042698015840598016005001720480035104201040034000c98207203a642802445440c0c45480b41e00400500017010702d500140904c1111a00040000c000d607042c400e8480c6284d16051300058050801c220004c880c40d050700c0e0402010001c0c240708401c09080a040c3c0c08a031072081050300000748144000f00c0d054441d034038104203840401c00b5450031510020044e04000f91240d5165505130300550030400040c0050905008491000e241c40d925201e0f10740d10780e11001d8070081240300850850104101110228035862410112201c00c14000107007545480c00140c1203401d0315030141c0900c079603540104210f40e07001c1a940c00c0f40c0c01500380800c0440300d44c0e0f051420501d564001c8805640500d1714040d8031a0301c017000e04802440b502c000c22203c80c110006540c1030b00b4500c152542a030140f0006100514080049d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 369162248 1250 369160998 369161003
    0x2c0a1a09090c04080102180307050f03120a03020d090b060103290111010b21070501020a0309170f0d0210060b0f03010b1b06011212030b01090b090604051003050f0702060c07020d 78
    0x5420303c0e489812a40c2668002110b402c1120620a00700800b45002e101030030040c5411201c20624101c1000440c1d1038040b01c440d6000003003404170b01010b80d035001e03404a0740072031246035041001622916040c2c80881c8c041c1c4000e40028605003107003c1503000311004030761401d100750b80045ea6691704d000440c0d12800c403403459669552503008141c034a80315514600b8860001140d06007140625000003480c1c1021a0320003411540300c002b100d000309410034054410780300c2e1400c0e000340601c1c0b5200d503a85881310300710140400e0700c210000c0d9660070368040380360f01844648020910043d9907a001c410481c1c01a02c2800c480124100010086800008010190010803400010310b000030380205900f4441e003648055520b0702d83e11102420060003280d400d40304840750508200182c680720000340341d140c5600550010403000607a040c0703942d541e241650001c003c0288468031405080320010042c02040e0b03034140e00b42d1000808a01a1800400c200d4401e010f002c074414105903a603000c00840c01d034046d005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 369163498 1250 369162248 369162271
    0x9230109080c011413080901140c0a0605100611030d0510090c0c1a100302090a0f0518010e07151214090c0a051206010e072c0a1a0909 59
    0x340e0300003074001c101410858200b5800020840d034402100c480200d00180000701ca803803240000304c00180d044003964010402880c0041070030201c1c242c1e4a105200d0701071035003014851480302404126032508580e20078807190184c8000c49503205019544400b0900c040b400a400900c48180e401c121940300940c44184002c02d05040c41e0394082103811680c91140302d03c00a0f09041d9101c0038010100c10280c1e0b00001114400180e141c03210151310034070348602009100d8031140d800b181c0c80340c1642e0402200381c5805801000103081c030303503042d004605c0303074032802141d550030034905d811180c00201e005403c0354042c0c140f1819580f13000c4422150060340d07000000b20702c1d5403208102e20010101c0426485040018010f200104c100b0007008103000711540081e01c1607015000c054131500001c104581143c0e9a98503520803900c8401081d16500c11080b282c0590440c0028106850180b1035001e40c1405c00a0b16a040d0703d907114a0040d450720001c40030300040d1441001201c64505107520140d80c803004040c070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 369164748 1250 369163498 369163511
    0x12042607030c1706150d02220c0804020a0b070515040203010f0c0e010305090609070317090405040302071d101203020a0c09060305070512060c0711090f070e0103092301 74
    0x762504400b400da04282c1d001191560b41c030040003400c1018540082001c3c03e002480b601c40c000003000c076150311000034000c19146122a81c000f802c00d290f40e00752003554001b4004000c0f2200d0060041d042120164030803c0501800503502400604581e80c10760064060800d402c020aa540c030407800c040d20072601036581c1c0c14041d85c070303c401c0e00c034000d5503520540c0d807423003c06040c10004080d074801910b91140c0d0341000c014011401c00014146d011203a10100c4502c1c00103c44001c80c1e2a80181000c0c20380181c100b1080204040e070103d1130304140c50303110340d00b80e03480e10183c242c0701d140340f02c11207080c0b5001481400c00d01c503444d001410414400d00c40e06c11150550150396a07040e1401c182d40c8190030450b180e0340d00340104803050081e032000c0c120554404580a00007240780d6030702c9101410003948480e000800005012050580341090f40f8082c0003410642410b0340103a40c17201c4101d0b2820700003a07480b001e121842d0320901804c0130840e002007900e030f481c2e416244942e0341802804c0000e40b4640da21074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 369165998 1250 369164748 369164753
    0x50609011b152a0e03190c0509070503040209220807020d05010e03030a06140d02061e04081b030c09070305280e0106060203040b0f09010507050609010603051204260703 74
    0x75868001c50000800044114102100c0600041020f40031043c080c04441c0f074000b0340c030f00140c451540d091042c044140c065003400d20301c80f40c25260700260341144404080142460b0840011402a1320a481715050b0b551090105101a8210086200411011842440440c580901030081c3c03034001410311100150036550642142c4a4445912560b0004070410803000a68446d5200030001c04400244220f14080002c03450500800024460240030030a42d0030103012010034800700c0036070b40030140e131191200300359a602d95680d480801c007501071280b00200c0f4240410240303051035018241e1850703511340c25030a801070a070042824280007004580781208082420100c8484124000c00040d04c1c80382032059800c2d05c44540001c001d5500c200002c0000300801c10440e0010b056001001d510b0700780590049813144600000500b0501c1000d0900680070010740c0400d04582c4075a04070341107000482102d000c24000c510408034894400250340380c010185010204654417140180e9052319260b9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 369167248 1250 369165998 369166001
    0xb03010f03030e1c05010b030607020a0302030d180f050714040921021921020622020301020f04030602031e090a1b050d03080a05100b07030e24070606050609011b15 72
    0x3e0302c19031305da0b03444d8500f2078250b00f0148030458008034a440a8902c11440d42c501a64903c1071903c10b6a0203584c642c0522603008110a801c3da00952059802500c8040b074200315070349100c0d81c0070b8402c0920342d0b018186054580392284550f0640d008503501c0c043d01c0b0748101000b80c070a48001c1d52044d03000f0046202881880d403d00903070b80c284580e0a81140303410040c0c01c112420b9006410406550200341800804030a4a001900d0b800058181d04804c012920120307000e4040c900131592041e40225000c820000c00c1c0e00611b110704804030315482d503040428421441650180c0744540c03150000c0c0040b0010902d0641c43c0c41c40d03d2813040054850b01da44074042000110070755401d6002642d0710040c405c0d201c031310b0301a5582081c484810180d440742000b080062a106140e4000c040c0f042c60540008bd545a501c00008501c40721158111000401c114101c0c0710740c450301045880034501140420700d45021f0b0306403501030038181e403035035640c0855501c0480105900b00e000c1e40c2140d90f4080103000380720745 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 369168498 1250 369167248 369167299
    0xa1106070c03350c07030f0c180b031b060901120902060301060c0209070c0507090221010603150b12280e1014190b040b18010f0b03010f03030e 63
    0x3150804103881c4403800818580380d6941e0340301c0190f003410003c0320703a003200029055007a01e0b00918511102c016074507200034110410340c0810840c42e151480340050450a030f004198190058003643c0d60101c00121030240c0e800080c0c000713035029006002c448a03d510407452032659001c00c01c0002421188c2d45c00240c2c0340d810980c0301030001640c211180c4214248641c4064201c0c0540c100740040960740e59455403070b009540035402d1141d0780480c01c00c080c4d0907905a13085401d40c0101e211152561900700080290008000356112000991790005a04e40d0381400c0b0b5100503c0e46a0745151616a002c240218850200c00b0b04100ca803036501c400c200140a1140c26140440301380144800081c40389010300355141240c4201482c01c0d03160402a0044c203002c502030305600d528000061601d411400980140840c954440d0030030315802825803040c0781d00c940e860685009601e102021a602c60b40002207100034002c8498240f1300e4502000002e025481c1c0b10346411006088910300810702c080082d03c00714 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 369169748 1250 369168498 369168533
    0x50112090c0b0a021501030b0601030e07032a050904030c05011a0609241b010f09050606040b211516090b0706020702040509060415021809090a061d0c030a1106070c03 73
    0x8c2d001c05000103907030181310300224617802c3c4010701985403458456502c0301020061801d0302841c01580c8130340b01080d2800c00c4014050090130400303c0d0400d0f00f00140390070401101160158603000880b001160b40381c0c0f0200d89458020704103450440502e0510103804c52200040e0803501c50307603d1042c0c0400000c4050820507494070070f0101c541c459628082d00303541060303254044203840d11084c5004982e02003511940b00d081070720080303800c100b17101c0800c042c10045c2c3c400c4c078080411a0b50000d100040410b20409020303da21082501d40c8075010b00c0d000a8698041c0305000c070300c00e10420400890078001421105014200050821841c0d030003003016614120b81c0e03501650000010001000144000c00320b00c40c0741a4403c60601d81a14184007811045120840c4146108c40008107420010445021030319071203501404002e252401c81c100b1240145152019801180c041d0941030034000b40c620b07000c4c1d40000740428144480000c0c0700c899440301c80191071002110307402102048103849284e90001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 369170998 1250 369169748 369169763
    0x7050d020d020c04060e0f040203100c03020a0201050f070f0c08040b0d09061a01080c09031015030b130c06270f0801110405030c040e030c0115050112090c0b0a02150103 74
    0x2040028103000c2c3c0441c90314440c9103044024040c42d45c07946400c0340d0042c902d10035286651920700009103009442c0c0745016403241069911940c0a03807580141c11710300080e070020300c41500c2e40c200540310708208072510400161084003001c142e6201d903003207000e55406031602d10b2415454070b99200c0b4a51001c6020007010340c640c0a07003020404684140140401000701d000d4045242100080c140800035201103076626020880b00e01540d410f0205408400380704404004c1036604441a0010110f144006d4400c44141e40c0015031070035220059902c0c299219100034003860800b88103890406041080740c5c1c044c489601540c2442c1c420040007009002c50782801081d0619001c0600d080d602e20840300304c41203105010400c0540c80000e030300351038030004940100c3d205000001c2240b0354012908590b0041d820002c82c100000c20344103540c402d98200382d80d00c1401161102400c020766001c004001c1c01400b0780c1400b0000803503000d001d06400b242d1403041d51f0180c44d07504082881c001d0203030015034560 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 369172248 1250 369170998 369171013
    0x408010c0f08070206131202010b030105040f020907050f03070c030e030a050a0539010302091804050106090b1324030507050a0503150c2109030711042d0207050d02 72
    0x590030011140e0f00808910041103035203003044070280d030403d00300402440c2c04815010014094001c3d00002c0d03241c00040c00030001e0b843c0c02c0c01d02258490345002c1c164080d000701c00101b400c0c54030941c1100c40d4031f45102000791450311150340454050440398019000c0088280d004078040d58140500d19210b1300900050a040a0b90300b805030508000300644540c42e01c6010003244444840f0040380f00032007800300e070030400041c01070058010384116200c00e0f0307108804080030a40ba1200c00c60450086000c0e034020802103403620308200844c0ea1410381141d000c007800c4400c0407083d03066042130340c200350110080c041d95100020818207202e500c8d041240c807038100304000c0c02103060488400c0c1c014001180204001c1754140818241c04001401c00302621000061001c1c160340c000200550036850784040e1181d620302020f266803a604445003c80e461034450604144514150099520300301035400a6019100003188600c2d400354109900d08519409110000c01301c0d038240880c1c0e4079001c1903005840303078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 369173498 1250 369172248 369172277
    0xc0a03030f021b22060801050112060c0e0603040f0f080307020a1a07080f090313121209140105071406091e0619090302100e0102130b0304080a03050c0408010c 70
    0x2080a0041140c0b542030841c1140340c403a680300551a500508a070b80761030740b84e801040c1040003411940e0880c801c5d542c20b043c00052100e04010060048034003540d0200b1049100c1070003141c5041c20034a41d554491018070200c0c003c02e140b4030f00d000226104070702410a81c45a1340c2c1e80011a0802c542c2200076070012a03400051160084c1d4409c0055120803000c8120b00c5e080d00e01900181c0081d142c00b150254000024654490420807103400c0440b18140032810b50342e5031040300c48181c444900322041c007817920440010354060100740c8190385010000410074101d070001166207400010090f940602550901c845000062004a00035480c0101504100355a601c2c445c4150700c011040726200d80c8464204001560b038016090701c030b80c2103d8008140200c0c070341002c91034602441c0c20861407516245401d0740410055008050340d4151042402e00295240c001d0002d40c0421034010703161a0040040c0e03c2402d1199108507400700e20b2460980c10319484038a40c900b100c61100e10390700810b4280741102d04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 369174748 1250 369173498 369173503
    0xe0102210a0b1f08071b0507030c061b0b1e0a380d020612071701051009031106040305070e07020610060c020d02030f010c080a180302070b0304050c0a03030f02 70
    0x340142d0540d103012070082e8003902c10b0a0a5140460a800c1213158800300310b80c14401d4140003000c04030724042c210192100d0070200c0d11080740e032000700e440e500c0d04031001800c6406021451110b031608045240050181e4a075880f01c4800240b00c0303401c0d95417083d40002241703285000e06024070484440001d440c00b9500032215814403c0016811561a0100180e0341c085444036128170144195200f0000750090300c0072642d54010341034100c0c62101c03400300b0444842d50200710400c0b41045441e10000d980d983d10240001451040059030004040c0407050001c10f440c074030300746900b00c409440c40e450b2694940300c503400c01c6010f4100500a18440c001d04c034a80f03030f040140f03c1d00b0000010762a1949840c040001d840e205201c03034000d000f00071401c404015035409102d00c0521900a00003803100720503503400140600e40c100c520100c0782e4a410f00c071880c8000f03014918500640c1c1a0001c1080038107010305074840d900020000c0b9094402c03009440250780314000210011440307600c402100c50710504000c3e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 369175998 1250 369174748 369174761
    0xd1110030f060b121801020702060f0a03050c0c030406050c07150c030f031413020d1b180908040506070503040b0a051c0b0310020904020904090f0506101203030e0102210a 75
    0xf054205000d0781d0003422140755029041a50048a15800f281e00c3e11000c0c0a4090080040c0d80040c010903501d0480d41e08134003d1044a0096400704002d540389080d1800c14043c06108090760f920900060003980c1c007500080c41036004c0041281c00b0156240c03003c00241c01190062800200000010008c054200e40b201c9030143c1c96007070074821114041e49202082900038803464040e80c00340070b13800540d15580c2406850703039004440310f800f0324103000200d045801e50f8404e4003a483d41868010b001c104039403040f9925a5400160a07203040c3c500b20400020790002c01041d10940400c21001510710f14030390040a0108403600c1c0c4a450309140302241554440030003ca840060524200317140766034001c0703000f01c0e55010a1500584070700c11540820000d01501c026079401901c0c041b004001d001e100707036041450a106004944007682c03920b103036102a1001d4403441160301e08204415000a00076009003d0701d042c1b480c00182848040940c604c001e1103402c2411801428610a020f42010503000f400e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 369177248 1250 369175998 369176009
    0x70305060f15060304030e041401061407020901030b191b0801050607030206010905220b0402030f070303141c0c08061e011b020a051215010603060e04020d1110030f06 73
    0x401c151401c45203502001d180c0d44070841c03264000200143c1058015a14074a500c10041c208201c100f13004100340310000000c2c000e4a002c29000c42c040c0c100700c2d405008454126502911002e65646199a0b8103082403025242c0c0c000480200c0c00c48441b041c05100b895040702603010164204c0b90140c0c0041d10380101a080b07540544402c22000340441d80002d083c03411220280c0001403d03544240050095404154010404840804040040c080e45042150140d4000c0382a110091042042c076903903040c49200040100741004450079803452040041d0000c2000f00803e4407805000c6080c250444104048010200304450140031150030b08030882c0186420040c2d202150614820003e0419250389503043c8c449401c1c803010b00b045480c0c0684440c02400e003c4d00c05a9001d08004d04280c40304600c091040040300303200d00024225120b409083c048a40c410940040e43e141c0d502403015500380e104060350b80e500d1a040c1240940c0f40e0320700407951304c405554001032510080b0b00c00740c03c1e206941e000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 369178498 1250 369177248 369177271
    0x50d12200a0b180f030903060f010e0106050c1c0215010503030a050d0e0715080a0506041b030b0f091005131506111f020403110301140a0c020f0a0507030506 69
    0x80090329000140648034a6084484664180d0302e4032a6002c04540810541c03080b03004002e4410422074000000d0a0018402c83c2640c9807595850300480c032003a001d2281e84416504100108440e5014000030315110002606881c1c0182da40c00840040000406013840180c3c01001a0074080401890090242404a01561030010050401006401480c02105005503070304081262407004110318001841e14401d821808020342c0d40142642c081210301041d81414000025200d1078507100b06402c600c294080c401c411a03809804a000f8131030740d981e040c0c0290041d03200315040c0d40c2d2106058458244100110462814042400080d01c142441c8060450400c1c224500c554000382c1c02900352216442c001c40c41c900c0841e0400d00e828120665181c006000c130190608035900c3e50020400c0c1e0340620780c58000c0c0c02c0210b00385400c80381c0307000b445103d40255101188402c1c0310b680001011401c0c520455102c40b6041503181d08020700000304543c542d1013000104208041400025400000c0015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 369179748 1250 369178498 369178547
    0x403031b21020304030203060c0c0d02070e22060f0e0c01050717072102011508060717130803010e09240127020d06030b130305090603090304050d12 65
    0x5408011400e9030100303000728a1a0408400098401c00945000759002001c595013800c090304c449800790300c1444010024001d030302301c82d400103000003445011188698042d01040c0d5451780c0100c1c0d821500f96050100d006a07080c00404a249405940080b248c00100050400c48490350180b8112051607050305114003442844041803013003803059040051502c3c4596140507521f400040e11062605a11540c58105502682298150b001d14444000880e03e615040e845000c06651640304403060000545d0301c43c90500206068507405810001107003103061500c0c043c4c1ea802406400136000051148a10801c101400c401045010684d0003180c1c80c1d0403401005d00850365100e0380c14000e000c40092089c80e000c01c14030351600c440b001d01d51512021901e50400850f1600504900e21050b10f038031007401c0c0410703902d0882d450302d6801e00d645034079030b9450285008240b214a0b08000c01c040d540f0300040c4000159500d80030388040000f4403030301c6420440c3d64228005045018003001d800c0004a0889 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 369180998 1250 369179748 369179753
    0xf11010f0c1a22050705091e1f080f0c090a02040e01060804020d140c010206090615040908040f03030903060c05121801150b04090b040209010e06030c1204080403031b 73
    0x2da010b1000c1404480b0600340d6244035100285200f8840c81c09038007030550b0590414080081001d8040e900300700c44101581e103030742206541c0140418a41d441002003980400c0031100c0d484c00322110544000102083d1030740d00c040440c2420248001000d107030304043c802802c1441c00844c07482c0e001c001582c00b181010b0030000c00d9003850205025200500c101e510200f0259920014185051070380045103e02404021041c503440d01e01c0c242703c5c3d6001d449032001003070390010045501072180d00310302200040405503100b0030015100d14a03003611003203401c00001c90002c0300c4590b4100654003036110320407070500d0b520300881143e1420011074100002480781d29040c0000390fa070a6048a20040491610f02510403014010007010000e501400346500000401b0b0302c545000d041203d80c205410843c003084242030005070310a404490703000401c243c00c2442d0700c1c6480c1010315000100318903014108041c0303141c10400da00040c2c8068030f888001041c200308140d400b00d801031803200401e040008980039039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 369182248 1250 369180998 369181013
    0x230405091f0509190507090501031802030c06070303020c030406023a03111603110c0d050a03211a0f0402181210090b010512030c03190c0f11010f0c 65
    0x740500b900c02c030641c02c08500030484101181c140070b12482c2040010f07080c510000b81c5990100d12510340400d050484440020060248895506401401911000790b203c8100000741e03100007800c6003415428807603c0c4048074200040c1018100c0d03a001804912624804d00000b0b0310f114421003803c1d0780344076601d0074000084030070000041613801c0100d41d1400c4035180150602071f1443c40040382c290518a40d0a1580c401c1c601a0001100c600765602c10010405200ca07402454101800c95400344811a0000e0710916460300040d20004070b00350041502400101503840603108034501601d0844003040e1b500c0c110084e105811811102146400d05182ea2800d0054680f44014800c098401c526010010300740301583c10380c0c80003030042205400504d0500e44008013809007501031900d40380e115070921340001c201e49610300000015820841e0f0a9600f18198120039402420012401e24010004060000503c61107105241c8900700c074030b04038001070400302c14030030f40d80400c03004a0214000c00c850 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 369183498 1250 369182248 369182311
    0x2030c0f0a0c1502030a050d09020405090d090f030b04020d0f1208100b03090a11030f0d03050f0906010305030d0203041e0f21050a030b04111b0d0e0901140123040509 73
    0xda01f04140c032403000e0820100108000c89001e50000d0a00c0304210010700b01249166180c801c0f80c40340140c450b118620205c19481302d0000070582900360300802c01514000e40200c00740d5101c1c038922009200d160b640d00b88402000031035900880d0140c821301000c2404401b000014240703d203030301400e51900400345544c44802c14400340c4404901c203045812500c080c800d60081014103011250780c00710748030005005200842d14030040003144030126202100104d1418101c80d0410300031401c04c0e1900d01040003d50000d002266100c1c50400e101a1002030315480c001e0705070281403030b0b4882241e18103040c0c2403924140543d0021104007480d100800313410000703540e5848001c0c540040c0700c0030440c2c00b080042c8440b950340e15038100003081103181b04128116000c1401c0c2480217036081101400350641d20314080900160740300c0c04240050201c9100040401108207052410389000e024114910444d00c00480d010f0360407035800a0284001d0030400e40d925004507104043d036008503801c2000729882d202 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 369184748 1250 369183498 369183517
    0x19020f090a06080d020307020f0a0b0a1b06141e10120c0b0c0705120705061902150406050a0605030708030d020f070804090506040f0b150a02030c0f0a0c150203 70
    0x940c10003081c840c01156000d1009840414100c60065841d80c0019544c1d4100741402c0780b043d90a04607401246c105031b0002c200310341c03130f8009160401440c1401542c03951208560030402d0b00f81d448402c404030340317680544054090a94685412410100d2641444024050100c0020700e40d1206014018003c103252208803550860403260001d0303a03190003d40c5002a40c8121210200860b816004038008904101180d40880f218409041c507156025119150752054036403244081c04101038102200420241d000d070f0600c19a020b99070b0140320b9100841d02a90107441143d5640c042006041c403c1c41030401410382140204052858904804c0d603034031641346107010702d6401143c43c0b8400e18080c0142c1d0703840c0f54002e01081d00c5a403907408000c02084201d414178403850074001800c0300c5800780d1091010071100030380000c44401002c903c1e800710b90710840b583c1d021403008104070a40034030184201c00381c80c81260080c12205016082c03072602141170342c004140203450020802102c84c0c002080f10401c92 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 369185998 1250 369184748 369184759
    0x70b010306140402010c150e150604151811091314090f1b0f030303040501021309061202040908040914041109070804060c05040509010303031d120a03020706060b0c030a0219020f 78
    0x14a12800000d8442040da600231889070f01c0c05101c010040e030460600c64042524200842e401c0c94a1b04060810503119030000420640d0030402c004040740c029420408850244901c0c0c8550040403918900c8044c1c40386403065511070f0f003030300404d4021007440d07044000c42e1b0040000d00702c0c1801ca1034490346e085144030320b01d070320010f41460141c0b00d03132100b41d401a0000301942d4807481c003410894080d45c0084007154052220302c40c041070f100c1141c8203100658003e000c410a10300d50396824000282a881019940f0b84810f01002030020405e020b00d014003520000c2869040c1840d00d0079a40d4080c0c2c05002901c10b0200b4009c004a9951000d4110350107508a8804210f02002182c156594403942e000701c0d40010000c8004000d0607010b410003020102030303180c22040801c2c4101502c2c1c54a05684c0364408004040000c41d1005110341c014140c03842c003854000500c6130392007184116070750100d400d00d00d80783c00100300d208556406016400314000303c2083c4484410160f400034103442c060401451061 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 369187248 1250 369185998 369186023
    0x9060309070314060a1b1707030b090a0609050f01030201050f160203030d0603031d0108150609030a1110030b03060112060e1b03251217070b010306140402010c 70
    0x105042200d40000c40d0049400a4a0448116011340f50003040320a40c02d4603040400c20485d100d5484090034103400c1540d00c480003142030f200301400790030b0041e1040d401c01d41c81d54007a03a42c070b50310316000f1800340c00c4040c40041c4840c80e040040080c0d41e0014000214280c0d101c004002507600001250450016003200d40e6845110340c0b44403041d108030400280d05444041040e042d07001c0c160307000c031046d2406901e640340c90420250421109424088890340020310600110741d20b6445495150b00c22a801840e035400c108030400030924010400000755040ea0000b4030111313031402c0504140c9003041c01883d003842440e50343e501007940c0f10010b100d400d920280c051001400d000d81580204540d1141c00c01340c40700218543c240c01d590800440700c0522900840c1401811034025020030090300040c0701c0f6900c002d80c40c00c042103a034105d41130029075051030444d0001c030a4132100b000500e40d03148102c42c052501d5040d410940200e45420300340c9020015054103100160ba0010192441c15510030307809110f1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 369188498 1250 369187248 369187261
    0x311070906030321021c1d2401050a060f142511010c020f0913020306010303030c031a18070e03010216050105090a1709060f0409050a0c14090603 64
    0x91052a501000d03145180c81004020540e012030700c4841c1540300c200009201d108a4803001c101d2207141200d0110b0034004600030300002041d0800700300300d486c0304140207031160848102c07424082c450380460320000e00000f02e50b09008001802602412080d115100040d00380b404c00b070040c945d000c100c01d0502001080d00c0083c3d144c03040031a1741040d10012900c81002c0000c4100342550720140c000c807070448140980310000c0d40704800c0860b0f0681c0051a800080d200b4000344210004050b00b955820b00d0340c00741803400b42e1020800d050003144203581c0022a140300da40c0043c11194910103054070b940c25102d21018541e0f522003100300005400326101140c2d1203040b416503607034218a0301280c142d400481c1146000540c060000d80643c00740e4001d000a42d110ba41564032640e030410300800d000a070f0703003408500301c0441018004049001d00302a1900300e1f5401140b515400c84d41c0000551515201003204a020f24080c02c080703901036041419484990030301c2030b0b0290050500c2c950003000c011002806 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 369189748 1250 369188498 369188503
    0x2a07050307030f38010b0a121104091103040506092a220b03190b0103081605060f1909030807050904021e0310081b1005090405070e10020111070311 65
    0x8000e00b5001043c0c0c540031030212589003036611400071501540c01e000000b406c0c13840f5012502e17004065030320320366442c943d040440000c0154480a90701004140000300b640030061280040090141000d13940743e14280c507146181550050600649400083c4840b180d039100d0091046501220030b0140e0300d0440c0000840e4030740701c51400542001c40e05513200500612030794407a0b003005da402c1c2c080c0c0382152698400048494017902c4000e010403203460041020402e1007010380452449980d4280078603117151145031501300b054603010302c08031401c01070002c010111075020b00c10401d03844050010120f961006050b40c07400a000b40c0034000d0028820310180d440384d04485800c0340021004009824200c881d0030250000c481500d114984901c1c08201000d000075180042c10800c02205c080f1320b170504c20b1190b10740342c03403010406000040c07242904613a15406000e21030889a590107031560006410882c0c4264000c0070001035900d85445e030390f103820a40040720b005507054100401d03403403500b4500b1071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 369190998 1250 369189748 369189773
    0x10c0503040c06230a210f1a21070b03010b1b0a050d030e0a0206041401030b12030708090d0209090d1404080a02090402010507051f060b120a05041104022a07050307030f 74
    0x7543c148880c8211b03004030020340c454220700440f0482005000502c03240100c1c000c4900c00030652004100c10700d00852030607400c240941000e0501503031036103661201c81102941003038101031070714800031405c5440381441a0700c11004071003050040c81010507a495490315038440740c408204150312090803086c40c590803c043c681d0b480c2d0180c00b03036958941d00e0318940342454000c0d901038002805c1105a103910715055116445440c240c1d4003440c641815659040d24680c05032105a0708084060010300240c0d90b8030001600c500c50301d50180028510925004011032100c100900d0000f906020500032001e00280c60351203980d058414185940301c900041c0d031a0f000f600d03c001e059115002d000700300030303908103c0441d080d08480303c10301101d40c07200a40307900b5016002d1240e82c8030042c44005190b8034001d0300100d8015010707807000d044d0b47c10540007040680c0c0c448071070300481000c01d58145881c14429000e1080400c5024007400c1c40505140c0043c1c1c4030541c030312024142440e96403640f02409812000705 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 369192248 1250 369190998 369191027
    0x1080703090816020619030b0f090105030d030b0409020a060804060b0a0b1b030705070303090e06012102030601270f090b030a0210180e0603100e031c06030203010c0503040c06230a 79
    0xa1b280c00061900043c05010580110741c052411081e1600c1d0505102c000181660801070240400080c400d0088000740071915030168066183e07041d280c0540c0780d00d6008000341500d0741e43c40d00c4034a41800c2880556413021010350040c654980b00b082a00281da0603540300c4e0401c186d50081d01902e1a000c40d2450241410240060040340000000c060304100c030042110340304100000709c2d0b9548070040d00c4440741c0180554003000010010302014615a0007540e018005040290002041d12003011100320a004600702c01c03400e4000600c0180c02296896006042c2c0304014002c8010203404030751144100803000340150000d0360416040c03402046d28002c203620400440d90384a590b100001d4040005607041800390169001820600b00240204004070368014019880c0c50740c1204041404245000e41c43d86440d51004003100581c2c00380261803d00710305583d0a074483c20641800d050407030941e80301c6014004840a40300000602c101c004496010011080b9103c039140c1d01c06803120100c01c100c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 369193498 1250 369192248 369192277
    0xd08041a070c0f030203060108031204060c021c2c0d03050702010504030609060209090a0902030a02010807180806070e030a0b062b050f010506040614040515060406030209010807030908160206 84
    0x100e01c032403c0782c031040200d81c022012601c40c3c1c5d90300c003c41a12841861844403102c40414001004a522604502c02c8410303240b0468444070740307108840028404250703d0100180f0724102c00c440300607040113803042039a804017600318100040d40014800a45100000b0305100c00400e510081d60f010b0390655000b55009042809070140c01d1800c48020b40c4000840d03481920000c002c510415a41d00c50b40402c1030b4050000d282000740c036001581c1401c00180701e9802c0000e4941c00114210703195008000500181d0000c0005003030030b40001e06150011021075011b0345c0018107a6001c01e02c0b0f00d01c015006842542d8081d203040c604c20340143c0d004a2000100324244d50b000c070741e4003007020000b243d4400442c5d41c002000507455500400081d42d1241c42400003000c2a131040c03020a00d005c1d40300a40068582d420902ca9103c00f03c0821100c0c1c10690044002c2135010406074403e5800543d49644440545000c01ca101540d41d40c07030000340200ca60782c04164800503c4d450442d1520012a003e00e10710700c0f00d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 369194748 1250 369193498 369193523
    0x1506011107170111030606031513090b1501110d0c050c06030708190209031011130806161704060b01031e0e010f0212160e060706020d0b0d08041a07 65
    0x80c0100e5036001d42d0545142e602c2c280b180c640900c22801900c1c09514020201d500d592603a002c03880455036000f55040e4444000c440300c1d04000054400d8140b002c0c81118800714501d401084106030050005859060013040f51000454031004540c45e4031001540c10040201001410081d10301801c07140c003681c1004002062161040d08641d1443c86a0a2656032a4036403100000c02403d0740944244542c040d401002030a03c800380903081440d904140c05104c5050403000744062421840a5014000980001c0144904084520000301802d822400c103000545150034080200c44401080a0040c030380c0c4030031340c0105038801d81145100000e01c480e494000c007c0d810700b82e401071901c00c0e01141c0c45d610b801100d0101401c1e50084d01c4000e014070030003098603540c0714a01e8030410301c400458030030440041d40101055483c50003500c1014040e034001a201e04c0e484030000c0c2280c40b403603000c610030002c902400b40041c01c0d6004441c140e0356071036980243e042800c1030b116054003602e072004100d45d11024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 369195998 1250 369194748 369194759
    0x1403120126010c0305180a03090603110c070b0912070e06121c05090a14030a0803060d06020412020f03151603020c0717010522060b0105070209070908010c0905031506011107 76
    0x17000b260103040407140c500300c21244041015518455040c0050102c2d404580070480f03903000794807a9210098402c9494a000d4518149505004158001d840580ea0210303004840e8203000ca0b00d840c42c84141d2004108007800c00d082192110002031411348540300c14840b03c009140c05004928502c451805815a080d5290b4000303081030b00001c442c680910129440001d000307400d4412802160f00c040e015215004c16515000b03600d500003018142c00000c6400c40c1d1700080c3c0240700800042903d8041840603030319520401250402c002c40b460b10a41c040810340112500c0d0385c1605410414240440e1040080300c141500603024419003c8541c1c051001c0000301d96480780d0000d404522140c000f00140e650700e60381c10a00c1d4a00c20f4840181d48101d118000c00540240d120148106050400d80e0411010358001010b5500495410001521014040181800034002d5440200442c20281d6990307092001191760b410401d02c0c020500c46081c808100d10b64010710030007002141c0304080d2210b080e00c50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 369197248 1250 369195998 369196001
    0x301091e1514031204090504060905031c1a09070c02040e0a0f0501050124180312030f050c040605070b060406051005030f060927100e01091403120126010c03 69
    0x40c840c949216240b00c14148007843d0120300f8150450b22001100c1c186402c29000100030007004100702ca4081e6901040701c04a001000a0076800c515410b0712507000d908403544809030307510752614051440d4004000d801b03540d640c0e07051641c0001f4601e400c1754040d0702400014003402c111503000c00039002c0c654035001840520483d410340f49010350007d01559030ba8000c00c010203481604001d6001d4103c0300c076180e05500c80d0b080307095084e00a280d02e4000030344a494101c00700081d0b81820740801e95481c103108110030350340586503200c1a2151408d00300b5181000151691081c0b18004042e0507003d00001c0c4143d0720303580034001900e009040028030303825145004d0803d40c0244c444810f074658140000d2202c0c1342500c075480c03180e6103c04100a0400d031f0148504d45015200c1d0070f080e00760040d024407900c254201d00c40d54504110410010070800654280881200c211800030b440c0ca4208109100e013001c032031403460781110a64900e007458200e69080c00070424400845d00c1d02194241040e194a19a05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 369198498 1250 369197248 369197291
    0x8030a021203060906060c0a0503030a020a030b0906221b02061e010305122d0a0f0207030b040210140315100f0210020903210a091a0301091e 62
    0x16022503807980304480c80c45107640001c54241354044455030018107a4202540a007060b5412401220240911591454210b0b0000c6031401800c540c0490320b03240d19945030056800905055078150301504220000c10505903c00c11a18210940c0ba1400040f604403548134814002c0c1000c01003c4202d8a480000d484000944d08054045218070110404041c448640340c102c952240040c4044041d0201303201554020300088000f21303001e48054040b400d030f106100e0100b40d0712901c00c0c0d03658001c0090082c04c0401d08c1490704003103510040c010300001d000c07010b80941042d012903402d0301c20ba0400740c3c105c80c5203405c2c40d24071945000c0481031244c04402280800c020f028102c0340c000081d20070700e004840a401840100005034401c0401d680181e285034028154084094103640e80d80ca00c86103a50709840c0c51a1113448008400201400803507840000034014004900e48406100c8114020034011300040c00780602a42d079400d0850140b80200446021903404c84a0611050070050324061b107407280d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 369199748 1250 369198498 369198517
    0x806100c0512040e0603190618050d09290f0c0c1804060507050c0c0d05011112040b060f1003050604021215130b0303070303050c09041401080111070201051c1103010803 74
    0x1544c20106840e450089548035101c6400c0b01006000da080c1c4c1c071001c000d40910740d001c00d0144021031040000c640240318480c0003030341d691600280c0e14070709603410301c40b10f01e445031240408c80c290f00c1041c014000581101c640d200740c920103a451b04900042c440c140f402c0c0c004a00c1c0c0c4014035035040c075030b030212201c1d0b4144a0790080e0400c011598901c0803c2d20107119402012041d904030798480300c071501e01005036444490041b000000d00c0317501ca01074001c569002601c80c40e0003500f1541000208900c0800066011790180c0d03142d0300c804070b0030002c01d0160151a40d00d2082c55140c400041694945905441007085485011811420300c5113040070492000c1b640c0d140507000341500d658481c50b403400b4685954030098019032a00d881c9840442c01040098800e80118a04201e500807694a5008200d00d400d4054948210365241500c03160848402c1e17103400240c02002d000480150317810009541000c0c00c850310204185030043d803018001c00c001111141000408400403a5031800080a443c0942 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 369200998 1250 369199748 369199769
    0x9051801060e010b0405011b05010e01090b06030705060a1d090403120e0c28030f060501050108090d080c0f0c0106060e010905191208120420010503070806100c051204 73
    0x192542c1c2121030000d070900078100701000400040240b54810115003403441011900c0200c034611550b1000c4c2503a101035000c400580d1103210032030034000406201d54106000320001c03c80c0742c1c070307000210305207004129807039041c461281c1e40b010006480c401c40031070060008003407880c28074183c50050040480c3d207141107045071400107100340c03514000a5142e0f01080050000e0300c0e14000808032454ac000c51b01100701c401d29502000400551245280300c449407040700e0204040d030410000410400c0000d24100c0300c0d07404000700d00d403000d810460480d040100003800076512048102142054895100d481100e51301c0c1c202e0001c4c940744d00100143c5890340c241d0710754001581c0c400c00c2103a2445500091f142186201d8420058118981d4004007500e01c200040c5007403c060002e0700100e6101143c0548140a0f140f00b0101804112446101294001d003000c1e401d50404890041420703070020002e601646600390700a041070b000318000072500d68010204e8504c01c0e400c0702c0c40c21f01c0390403520450355400d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 369202248 1250 369200998 369201011
    0x150705041a0a20010906050c09091023040b12100509010905120306010306050a0b0a0215041e0c050613050a09090203250b03040602091e100c0c09051801 67
    0x90306100c00b20344000d600c0e03540b4034080048000e0b420010314a0048001015941d484603000011110b00039a4403810a480e0301c0b6443c3c800c000c06002882c8801404054800340c00041848100c420724a95110111396521102003100d501d00403800811130082155405412280c2d2200f014000141c13690079005004030a00040d00e50507200da00765207010300001c1c15900046501e02004582401840c0c0c1b0101c14900490f10694507800718000b500c15030826203030148005600d1a465404004018001c1d818070601d5000380b40a4848071054111810b000348442c60f0700306000144842d00811101a01c001003000b41d0f034500f1b01c1e05050080d031940c401c030703030144590400001e8600c0c018440c9410242d0007401401e110003600310803c6956103195031107800781602c00004580ca45040d000f440c03145100e01801a9600d03640001c22204420076881040d040100301c2c1c50b009540c880c81001c41420320181001550000a4680803c5203100c5400040318103180200300840e52809128070554541024020040e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 369203498 1250 369202248 369202289
    0x9030409020c0a02120607020a020103091115070308011e0e0402010309080c0a0204141e0702100c03060305060f0402330703030504030801170d201515090906040305030915070504 78
    0xc41b6401c0714854090b820003210f00001d54002c1c1c02141006d03111f902000d03420010b0000140001520b285c11116213036002c01d200c010183c11841050140034040c1d03030402e030b0640b600f07038040034080c16000340810455142d02017811a4040e4200c6101c00c1d1b80485581c3e00c0f202116203856458101010076441681080d40810002c240141c82c0c034001c003481760501c0c80c44990004440510003026040300c0441c450181082c9507008a44070754103018210765008102c1034a1410450300d020310190010100c848404107100046c0e448440905003128202e40c0b0765400440b0756805481c2c13220901c0c03a040b44030400501141016403591140744164480d898804e1030344d03254080980020440786070000c0540c040c1000305c50741d6000f4000030f03491100042ca4072010b2506082202d0410b1100c0b41c3c040c84500c0079601340300307200c981c40d071044481781000d45280aa51800200c056602c180182020741070201c00000f203049950140700851654240310b44c14050380c00e021b80d00038581d50061160300030130000704061810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 369204748 1250 369203498 369203503
    0x18040902030c370305060a02090d05070b0a0e010305070c020f040209091819051506060403081b01050a0c0c3c1203020306012f10050a0c020703081209030409020c0a0212 74
    0x713585e0030900800c056507034003018600940c0003100784c2ea401120421103000050081010368050016020003a40b180c040710005405d041c0480a401e050604101c100802e481d030200c49016003a40403210551003a94807000304d0003c0c464001801c2d00000200704201040d02140010282d0350801000c41310349104400408116180b14040101640c01c0030f6218008108101c0541c2e0b04210002d00c01442c15a999840d9121613110b061005004040d034508141517070340a1007001c0c0e1102803148107015100510b00c0c000c041d149400c000400001114015801142014188610b01c4a804070989080102800043c0000014100450f50040c0450450071954400d00949000d0501078403481d001c0d4040050208045681c807022109010f40301c1000c21500d90100a194080030910340001454141141a04281c0d02c1c10444101075601c0203000b0000a00390381c0880d003034200300c2d5208824a4498030b140d170781140303e0359000084040c0007061b0700c0d40013030b07000c00c501e040d682c400c0701c00032140c440f455403658 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 369205998 1250 369204748 369204859
    0x70f06140304080c07180b03010506010f09031704030c29130b030613021603080901090503040b0703030f06030606090b0f0303030a0f0615021e0318040902030c 70
    0x8a80050070710200e400288880050301100784500f040e601034030345415044107003544415840340c000f9200d10805225040030f225080e001b000c2881c00160349a02042c0c00707800c1d4480303440010401038100c442540d1080036001540d02445c1d00040e01c24240b56105040100b08041a92103104114908652003e8102600c2100d20070382001d181c500015180c00200700c055003009100c150018111100718012000602c0100040c0342240c41c46c03d004030490a0080500c02c0003401c88045a1600700b031a00810000015113044071404903079a036071011545411405001100401841c1504081c4048100085a0003401c00c0c1d5078144410000382428800300542040391801c45505074004002007114000d02c0c0d040b03a84055416503010800550f50208401c440054100100040e04010710100381071101420344200d03010390b40000c41c02e00c0000d945c1c99a101301c8030f000780d910940da95003140c011034a00f4481c2d40c8000c07a00a15a50700622014070051310804880c84041c0c0c210708071000e084600c0300b64246d42 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 369207248 1250 369205998 369206027
    0x801020301060f111e071505090d110315100e150f1005090d0605010e0f0412210e0d020d050406050f030a270201080a0605030c10120e070f06 62
    0x20301c2000280c030540d98030b00b4041d0201c0f03090180b01c050048880010b00c0c03584000090a00414509243c04a601f010444050103c0304010041044680d2980d0300040719020a400101c01c003d0030035154000303403805403890500703605446101c0812200000340b0040380c044458000c4c02d100642e46200030035100702c0b00103044541c00a60350301c2c51409030a01c07000300e00e140c0e04c1c1410807600d08094040040e0710820f0144007215a551100b00521084100030505d6070441da17041c030300180a0810340c0e54040c6000c40c0050407402c114a40c988215a50b081c41d1268032081600e0380100101d40361a03a1258555042400c0c250152181139820a03420b4483d0085508a03416076a40a0804510441c200c29035400600f00020407034a81040c070004500c0c411740091960b80c80d000383d0036402450f01c009400034100030f0403d18498600b40e020407150300c0c040395038414800102d0710320f00c84c40d80c0503406581c4c91001840d099a6540340c030f10804108400068420241d8140071204d0307111036030b40c1e2070484120340000080e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 369208498 1250 369207248 369207257
    0x13140603040308071812020a0501050705030304080c1e011506050307050a1101020c0d09030311060f0103030c1b0b0c15060a12031e0905120604020102031603031103010f0f080102030106 81
    0x40c003003440b0b0f60074a900300081d407904010141c04120401404000303600032074165813016129008500c2c012081c2d100a24080c24114203003200e5440762030b01c034040180007404103200002c4411b506003041c8040300c281c1c079241c0320724842d0840481e0018001d140c5959512148056010007290751809081540c0c0328110aa681901c0c1c0700805000b00c54000501d403880301950f40034068854501010300c0140c00d50074541d624030000e0f0f440c508000b0b004a4401c6054421900302c80d0501010040314000340b41542e4060502c1c44c030b86102450304200d12002850203003000e920002d404100c1c6036802006101103460b05044503007100c6007006480c541c1c1015100141d1040c40c0c92020482d52080c1c00c001030301280203090001ba011405070100610750000d080c4840002c1802034107001c14945180325078240e100100042030340d450039500207903503840780c400508014440542100700700b44c800d07040f080c5099070390b85202c0e8036941d480b07814040000c1d06004000421215450200369800148283c90499880350359 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 369209748 1250 369208498 369208501
    0x201140703180602030a0b130e070603091b0e0603100204150f0908060109060510020a0c060e120a06090201080906100b030a0605040218010909020a200a020d0813140603 74
    0x80640003004600000c071a00425a048000070880510240d407060031800d401140007d42d280411040c100d080350703402e5005103070a0034062301c4c2c0c2c40042c80030103880150a000403a200c040c00c04403240d080c62a01e1002201c50003601041144c14458410b0280320103a0803145c1d130741c8a07442c681c02a80141e00400344030301c030f030010151b240503c120926138000308581004914281c458081c075080030400d0308208101501d4003420001070030034031441b40c1b1031070251003d4100480c02c2d0741c03041e4212555118031000c110784232a608220b030340c6c2c554469090011079421a40c000919181c42c030054440313040700b80d002c0b441d0030001404000d00822102e01c00c41102d0b40e645c51701400e14248401d42c1c1c00142500090796601c460126a540341c0c1e00c001c00061202c00c41c200d880e40b01c0d103c0014404400c58129920050041c409c11901c039401c01034200d00166104181c20150003030907000ca241c414541d1020354403200580040c42409000401820041c4042490701700c84e60f141c1151070b22040c04413008a030000002c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 369210998 1250 369209748 369209761
    0x1030b030c062101092003091f0b10170f040f060c0c0b04050a02041505011b050a12051c0c0f180806190b090c120a0204090f050f07020114 61
    0x900030000860320404440e085001d0f81c8080d410a04260050f406046d0307507000c034400c2100d8406101c0030884020540720300c0c5140c450000350b1070300f101d142070100401c5282c0c401e58080919030070040d0f003884003910040d40308c40e040750002c1001c2c035a8151180000c2c0b2035000710b0403180c401030f4030034442c40d0000d10424030310900da0346180c02441c1c0a10820104101d490324100040c140c0307040700d4002c038000c42c01842c88895034010070045801c41803a00c01c03110303901e110400240c0d03040341f015031218400044443c2040750307038180315040c0380c003a000c0206038020441e2841c0c28240c00c680500309200100300c200c10344c542d42000361001c9a03002c5c205000490340528002c0501440b0b6002c0e00780b41a42c600b042440e00360384004081c5070030800c2e9100244c13200054581c41b03000910707204100040c031007200d20b9101410b01c0f04050540340306d140e1004d04000b401000280c2100d401e0340480703008005414040010199041e880b4000b040156102c1045400640106800c1c6105000b0b140e03011a94607150b2071140c4420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 369212248 1250 369210998 369211009
    0x1c110705240c0304060c0b090c2b0507120c06030b0603011205011401060201020c010c0822051507020304171b090601020c0d11090609011a090604210b0601030b030c 72
    0x1c10518009401005440010042070018000405141c1ca6140a42c80c41e89001c2e4107040006141250950003005085090741e14016804445001400c5514401c48008000e9200f80010b01020b080d44c4540c0c0c0d800035100e1280301040400b1402200c4100b07145032a024221706480394400b04075440181032005002c85040303044030200b828440c070300014881b69500105001c41100368410000b5075030214035074016207000c0c02024501403080c645001c8900d440081030394981d600e1880340040c1805102a030040050400c004481202c140d07001310781d14130345600000e66940c001e005054203d480b400c110804407800080002c003072248500d02c40510f46901c0c050205036140146868114490902080c800b601d800502c40110350290000d048406801380c1802200310000e80b1050095240c94010440c0d15130b20a002c44004009502d403603910715071440052040d0046800161105076442d0600c5508083d480c0c00007052480358498540c290b4580005504403052200301a4068110b0811950b280c80c0c030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 369213498 1250 369212248 369212299
    0x91201052409070207062a050607090b0703050d0e1e030702010f140703230d0506030114010302010f0813080f0d05070212040513091403030a05090102030408190903051c110705 77
    0x41c01101101003511010491f0700e040581c2060741c0300d0304020244404a0303400958075000d0301c202032025103001e609640080440c4103100ca814232455944885030601502440380648181452145425040b08442056141d40c4100c00403030205410262003440b4601400c1c518a4203805600c4042c1450601d8a0944154000302c0303042050030b40042c0e2188800031800080d011a25140c5000240e92a1540501d800c556014580d030288a200000405c0140e92101e03001c0000950751030320740e505840741266190220b5503510700800407800030030743d64210990b1034094120440302c0c107011702c00c944640c082a40c40d01c41c448510301000100f0401400a400d140c9001842810b102200283d92461038680000008011b581c2c4000c54100006010021184c4d0140b2030304101c040c8021403441c20541e8409484d4410031844001a98145e240c01c0d8080380a00b00040c025034011056411299408403954020010100301c44081480c1e8a501d44034401300040c650280c600241c280306501042e81c11080c0403040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 369214748 1250 369213498 369213527
    0x307020a0b100305070e090a03120905070902091809120705070e0705040503070e1e071704080a02011401030b0a0527010b040609090c030809120105240907020706 71
    0x10325003256000980c80c80c0701c1d03842240c00240d202402c500b103240c4107081407075641c4064650b1900a00380045104003080c543e074415498106007280e4030078a404600a0266100c014049000f00031000440e14000d0700284071494044682e881c0550034000c1e200b0310010180c4a03560140e120b45403402e4029001001402c0c0503002d00201c80c81c6c1da554104000407103070200e41c0d0344001200850208800d0404004400c06013100c4c84000401d13141a00080c001e4916668640031031048020119602e40d0144c1c8030710030544410404510545802d09045200d94051604e4034010361031321a0259100910007003031810789601c598250b40c83e44071100603074090423028121f00c050000c003d1000c2c91802003c201c0c100711503184000440c5090100b800c0104840e0150700080189081c1100000004c41071080d03c011b1741d90110b58691130b609010042054110319100c5c41c2059842c0070140680c131100e00000118252000c506810111178610500c48001016114080541c0c4101c80078820503008121240900e40c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 369215998 1250 369214748 369214753
    0x320703030609361b050a060816050a1407030c1b030f260c1b0109050d0f0510020409060305060a0c09031709040c0e040b01030204050f0f040f06030507060f080714030702 74
    0x7101e4036404c8503c1446101840b01d030019180801c01410490540001810a81000c0c142da00e080032600d10f903101c0d201115003c1200008854219500640180c00c02d520f5035011140c0303c0351030389000307003554821a2090700c9800080d510302c11550b0f164166030044da9440f5034404131181c855513030700d05841081d600c0c0303a108240841301398090f09016000f5003440c050341c500801c00c43d600b400d880d0840420b003500d41410410440424002601d40940c4602d07c44d5100d00c100c1d40384c84480c144181046440d40c0c4650610f4000100006c02e9004c81d00004140e9024000765215034841310300100413100202c030382c3c04c0451a0440300300040380341d078142d10906400d07481106190a031040005400c070343e003804401020030700c0320310f0607429400c2911a000100d2404c1c01c0451800b81080c0000d4200102038000c2407044840480400e21605c0d5038000300d56080b60b468081c0102600d2340380886d1144400d000d4200003e000b101c258082a00c00c0c100035000712419189c140403118200420b00040d84010610070551 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 369217248 1250 369215998 369216101
    0x8070b09060c0f030a080702010b0a060c1506080703030201060b07031e0203161a0610091a0c0f031e03040b0a0e0a020a0f15030615320703030609 64
    0x302001d0010f4003412000101075130351444400c00180802c01d0140404086a1418280405c00e8860720a104107a4580f400c1107032500f1501e1422021030b00b001e098881c411420035100040250380092040e054a00c281c000380442910349140c03420034081d04c0c0010300000d54100324060389201c03004852001001034810791745801662a07540310121902c001c111051560040311400c507880400080350015030456140481c042c00203001090510b4078018034905118402c3c285405125040c00c6580c810194030076525030300c1391072031a0340d00c0382c10298240d80201d22106039103410144001c1280c5c0306035400b591042250700c0c0e01440400402c001c280301e051910846560b440540d51340c0c203031080206546141e0040040c100a9440c02c0042c84290380424542048028000b202710b00a203a04504081d16081c0702c1102000010061524a0310b90300e10610740c000103d4840c50f07845802020700d10302036101440a42d580d1408041100c0382101c0300f4900080300000c80e110b4003100b03007030b42260314800b14441500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 369218498 1250 369217248 369217267
    0x6110a06090f11032a04140f01060305010b1c0207020d081c0e0a020a05120313060503090d0f0806010c03051e030402040e24060a0308040605030402010306090608070b0906 75
    0x8407120710005407640924203502604101d0f041c240d01d446404150054000e13042000c08400e11078495251400300c010b442d03128070090b900d4542c840c0552201c0b070002c0d4001401d16100031500f840d0203000e520006800c100003c40c00074820002c0365410904148a009480300c0d000c0303000c0c021f410050302245c0c809004c115803408910114094a14804201840400b00542480e8407040311000c01d018209900841108000742c0c0c1c40c100480c0403030744250341d0003015981f5803c005041d840754040208034030a20710b00c003240300d50344034001d98401c0d40c00310300719121400e60400a881c0713142e016a4050000b5211000202154804e0b25480100c1c0c0c441d0420a007000c486204580c00d01900c1e000c139203810f910200420007076161038001c41585048000140070940000718000303000f000c441c5039144a01c0505c1e00460419114aa0550011034000040c144c665131520401000c43d40700b92021b070700003814210045440e101900c18070085404020040176001d150644001d82d83e0005100c0c198402c10a0005002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 369219748 1250 369218498 369218501
    0x403090506030a241206051305010e070603060518180c1c1b0b0304031d06030a0501170f0d12020d15060809010504020a1a28030e0f0706110a06 63
    0x8803c0c1c4200420b100e4096039030203001c400c0514010306640c039004020000e42c0410110b0010b446e800c1000030586903200c0b0b41072981c055514000034495031034101e101c07a0307480300031910710103491980d5824005581d84a081103809841f000c26403c8481844000c10302e400040c407004414480300e0000d0710221818800020345449003600b6030100d14a50b40d0b1140c0400c4100446407103048405200112110b040c042041940e02000b00010309101c40d032983d03100110080c0050440814000b0416a41c920b060341e800000740c4000e00c580c1701c0c0c0144940b008201c842000c0b0b00c0e131b90480003a200070800b00310b104a00b03c4040e443c0d40f244c092201d81c2003150901e000c807503000b000c0802c00340c0c984000029213003110050200e04010803607915a49000107120050703451071f08c50000c4920440705400101ba56000d00c6009108054860031070164034040c10081240f501803d000c3c498003502c00f04070760041daa517110344800d0030142d40c03400340d04021030030710280c1e0050010f82c807030f001d20104807540542a540d4000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 369220998 1250 369219748 369219751
    0x70e0a080609010c05070f060c091a090f030c0102150c040504060b0c06010b070807020f0604150206061002010c0c080c0a1b14010507030e011d13050f0a060501020304030b040309050603 81
    0x80081d0050401c004100c0e4090161942a44440c54014504480e40c1ca0710210f40688600051200781c503500075000d1103115400c1b0b40094400c25040500d400c0380c02c000d0b039545074400c4c0c80b510b01031040302c890350109240129441800070300680141c146200c0084503290004c5008180780d03d09030301808003103126241c9105250260200ca040d1039036130300300c1e00002481d050050f4010208030900300010000200c0400580d0112903040d01c1c51007114403038100050307560081350803120407652000d000c3d500c0960f00082c42c502842c0141c1d1542d02200000004900766007034651082c01041c00304114200141045c3e000317000c91229481501c4e6421250b68400f003210011030203011010107480824084035414003d6080d00b0042400d2141c50110260303000f034100b44007014090306101403010b401d04048000585403280340b6006101286c80101c20340080001d00054512a80c4464884001205000baa10404007a98016001103060030328640e00d04480c050001e0045081110300b050000e240c0c0c07103c4d006103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 369222248 1250 369220998 369221009
    0x50423030106081006030b0c0304200310020c0c01120632030703051c031b08090c030105070c0c0905061503090304050307030803071706090c21040305070203210d0203070e0a 76
    0xb0510170b2860408110004c1f0250124084034400c01c10302002074040c1000c4114080710b00d142250445465000a050460504007c0940ea000181031240d400021803004241130090321a069419402641078045070003e001d400c4d296510302c3c12580c03200822450b4001c00c0b07460480321003520484640031900300000c584c811940c07070707010b0710320051403100d000508034a100c42864204400a40e040940040b82c442c040b0100600440e10b0100342da008042c40b031850481d2024000b40403a040c4040b000340b090f030400c2c1d003c0d910740c080040d011030000d002d40a003134058100140769290303224081c54240c2240d40003500105085c071007044005890307101409060f00950142403da80c41345410710001e801c200c0b54410241e00d10301c4000800c2a1a5180040180c00c04281e06290f912208030b09048000b55052502d0242e203a0107040070001010382c000000c00c60300341300354140c407814100c025411101c02c040450340c101d0001c0500c0446132444960380a50f50081c018a0180d900d01140c1c40443c40308100754004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 369223498 1250 369222248 369222251
    0x20706020d1a011d1008070c020907050d150e0408030c070c060309061404230a08030f01050f01020d05090d02040f091a06030d0c06090305040b0f0a0905010504230301060810 76
    0xc42c1c40d03d40e003203080442d11903014003003158070003074150000d1962007204440000303010052002c01c0c1e2091003007400d12052070307010b00000b0f26800c105102074250b07001088201229401c2a2084001114003045002159000002c05d8000d81312903448007081d0f00014441020300c84240591000b00f09004040760041c031f03c039100002c0b40c002e41d0030009c0c1913580000c1d0b8100c064400d241800005880c4031124a618003d480c1000041d9600701c20450900241380f0300580f032814040107111028452929540c100c40007110b010905010403001640c403840600c40d84000f2910a000380c08190501740710509080340700500000318500c40c86030070b0048843d0000280c980e099404819078a10008201064108500314001c0a81d0860301c580101200c5118800038201703901e0f1002c52003051301490584d03000d0b100a40c40a0385420300700c50020201d030440d480010001d50041400502540100116800d8607010071030590000d07109011b2030386165408004940541d81d81e00d0006520701c06010b03148401d00250340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 369224748 1250 369223498 369223541
    0x120c03072304080c06040e0a0b010219051605011809091a07050a0e030c0f0105070218041506090b090604180c090b0a090b0d030c03090503030406210e03040603020706020d 75
    0x10464505a401910301d40104070810044c01190301422039180c1c060031810b0040343c0d2142c9c4d07000403401d01c800e150740300c0c180802c01ca409504011b40400d145005000d18015988820f541c0d900454520720389061600c2940c0d0741807420302c020042d40e0882da403458000c84520b4008070420715103140b440800c640c0140082d40200b20086100e5012041c0d06920800300c009084a00c0000001070a0310000082d090600000003000f0045444d606d8650038007800703c040e585060b140c142048211549080b8005110500e4241702040100081c440c0380302c0f502010340303652070550300c3e14140310007001030101d4020f5200aa0312070900007403184c030141024000616020400d503022006000c0c0d880c146130020349045080c0725044201d82c6603105400101ca4044c900440d84890780d0400781c0d01410143c1041d50107010004010441980002c098003200c0444000800c45580b01d44820f030440da070300040c000051300100701c10400c052098003e0190742e0701400d401850001402d034440c04581004c206010504120302 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 369225998 1250 369224748 369224759
    0x1412010e010e090705030705040b010e030a0305040806090a1a06030f120d0b040b06030a091a091b030109020901060513050604090b09060d030905060d0615020a0512120c03072304 78
    0x100c8107030000c11110081004d14142000641c42c0e0300345000e07042c015030340e4203c03503045caa104020040b1080e0020b130503989081014107000784103510030300070204203101d00800710301c500310002000055550400002e03408a1380e03420f040b503041e0b18040d20203a450b226200d07900c0081c100034041c0c8009a8040c941c1e440c0d5400d0f405007007100740c03100c2078042c0d445146858045100d6444400440358055000d02001506400074a0500084e5500a004844105a07001089820714001400245018101e50a110000070080825080e5000002c5c02500000d10f0710040000c507000d04080c02814141e81c0e085035800d901c4001154041d0845d5100407001780c0c94500d01c00090810a43c420740100f020703100001001040e0718042c01952613441800d00a090003c0c40c1100d14a107648032001038a03031082e48045401c08110000e6803244e908609640902541b010307010700d882807604a40c2004070141d0320784c1899030b40103001641d54000030300e14018010301c0003805081101141c01d4031620001007c0140c4c8881c20701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 369227248 1250 369225998 369226019
    0xf01030c09060608010b0d0204030f0c1e062f1b04050f010f1404230a0e030309120d140702070303090b090618150c01021c11030105011412010e01 64
    0x39440081e10610b4040c0900090790300903d000d064070340203031307a2503960580f0002c004024131442c1d00103458500180c0c4030408016517005100221b03486120b00e41d46164000003280341c0d03124a486200c0115021141041d02c800401e0780580180700b401a4242c940404e0035071407401c0200441500f6080c190091a520b00c85c6070501c0b409811880c078201c000c3c038660400c0c41d042201c444502401d09505650f2032410410741e01c41d00040c49103606c4000a200ca103540300703c03036048040199140c65006080c4401854451000019a807084001307d00500f03024030100c82565940d402801ca01c14030545030400c55a80104d00418107000365240d80c010101c8502c2c60800510310111904001040e2104005d603910f145c2d105800d480d041c0000002d0503560075000c0d400204c0884072028901055040461005965001035014041000840104c18003544480858904488031803152541d450310a10050026500c60509036910043c40c100071854000640c580407645202680500302103105500188a0301d02c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 369228498 1250 369227248 369227273
    0xf0d03050f010e0106080c130e0712050708070e0d0512071505090616050c01060303020d0311070c030b040f08030a02130617010308090607080d020301031b0803030a021c050f0103 78
    0x51000079075414112201405581807143d081000b51403408601003800e11800c592007101c1800c0d484410355525810f4900d00b0304111138800226290481c3c0c0f0803000c015000d510f11400160f82c540203140e481c14020f84061000840103604a002910a400000c4082040e01c0d4080246a8038984490062030b040760303005400640200c885080800340540420001030441e040140c1c0201f060300c003a0041422140ca018001415510b9070030070f14000185038000c144c0110341001903400b0300000402191000c168411010300070808140e80c401000803948103401c00344c20038461000c0000310b0142da280c00c16582c1050f90780100b070070303400111501c001c0020244040106541e0914610f900054a48001354440c144009800b074072001035840000e0792900304486810b82d12044031503c596503200d6030380080d0400d0000b00c17240302003c0d5a00304002030a0440700115420400110701d503541c1c01a41c034004c0c0d0048a1051009000c1683c200c1d82c81010f80242d621945072010901c00d0b56140d4113001c061101c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 369229748 1250 369228498 369228511
    0x100e0303130504270807060e06100603151811040806070305011e05130e010b030706110c0316120f0f0b04030207090507050412050a020d0c080601080c131a030f0d0305 73
    0x4138492072611030b180c480c001000560304007040b6903c41b812800d02c1406000507420403060341c024401003002e0040d10840480c01da5500e40c3c3d08000b040705417a1071020201282c081c2c1c0188078449110b1100500c1c00da00070564448401d001c5908240d80c4210962501d00183c4034440440e49420040c01309926071040740c0040c000e00180f503160a0320782000b140406030b060b580070115036112007106a00a5007500320103180d41c800760854554a82d542c0004010b604c1200b1400d07454020988200340030706d0009a0000001c00d1602851203031441c28a80121900c0c46450440704210103480744070105a0034060740f1201c5005034120411480c1510b030007410180c05420500f500ba1800d414806002e40c410141d8007942e6100d1418503408005041c0180b806050a90080d03010344081811001c01c02c400c41608101c038003980032a1482c0e41c82d00705d13042c2c5541d51054031a070041050102c1190701042500132010603000c008401191141240200341000703003511000b29240d01c150200c0c9000d651611909a0110303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 369230998 1250 369229748 369229781
    0x20310081011070303020d0b0604060e031b031c02010608010903050a0206090a030e0d020f06071101020d0912060b0d050d09080c090613020a051b150a020a0e100e0303130504 76
    0x201c5501c0b44540c1c5000b406005010964049803042051846900100c80580020880e90b101d80d071300c0034024880e50012000d50701034052900640e920200100c9000f030010300c0140904190a200a209080e0001c0031038103004544d210034000420312802c0c454801e10394000c3d0f940e079599003401280a85090300103041014194003000c0300e800032039400084081c41c03400032164440c1c0000079000082c031151403840116030001307001418204004039607160101c600c9082e0291000d1a003216810340c0c40741d1076441030389101c0343c040b407203a8000366640c0d0110400c50801016094500556180c40d454049204428000f04070b10000c18400a071080111603513000d401c5171004134a00d45200402c4100041000e8144450f8001c2101c0140f03600440a54071130070100544c0200401e15040c040d0356910b00307041c600b101480c48501150500c2103500841e1102c0c04951584001c0c0c1081400b88503400d10254800c41c1040560340c8034008594060001f4254100551010701c103075400d003000c10045440b0320031442c0c10503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 369232248 1250 369230998 369231011
    0x106050c16141203090a14060c011e0c08070e27090a0b010b0403020d06020a0e150405090601050705061f051503010503010c03060612020313081b060c0408120309100203100810 77
    0xe584101501d0b00703440010b046060f40341f41e0b600104280f07008103402100d031542041482548580d03021802030b01103d0241702482040405402610078110590f41e00d000151580b42c510b2031410045803142080c0c04811100001103840d080c02c0c100c40806036600032203500102040c009101521015038050541d21001c40c2c030b40fa2441e8001114a4080300f80100010740102d2a0344107503005624070019110090144030080c80e044103007101c66030250107007610904034080030502551084040d40c0200f94004001d01c107544400040d80840031504070680f140115415012070302c0d8079100380b11000d5450b0504e2860700d0354103100806085d5041c2c0795221080503d03100c020024107621059009481180d03850040e602d480d0000002584402e030107000e4285100003030301d0300a03028170080914940300750009a80e2140c580c08205d440c18891413156003119440610b812218150440086811101241c00c88101c000288104130980c0c00884950714400348900080000d80c0050180c800c5a50100400300000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 369233498 1250 369232248 369232267
    0x120201060506070f080f070503120c03070903080702030c040c1814281d010303020118080301050402091201050901090c090c02060c0a031d0105060a080102070b0106050c16141203 78
    0x214081c90502408101804462070240651728003111800300040c001d0a03500c001600704941c0e40d0f80002d00d030300d00d911482c40c0001c4500c117803039048d01d00865495655074000784c60354940d00296089484180c0c1e02d0b004070307170301c0c0703801e0342c0e100c0c0310b02d6005034140d803100680502e071628030744200c4003203511003080d1311070640709001c4580d10801a4920019010404612030b040803241c413507109103c0e0403048070302120b0701359038440d09000038801e41207901c00e50090010741c070209502d404060540f84002d1100c01e00b400144075501c2e05801409034003070007030842108001c00045107800d645040d039800d405030759158800f20511095101560242c9080c2c00103201945440c00020350f40d00000f4035006c00d0071004950302c0034131803094200a18205020103d403910003841c40e02170740202402d440072031080c1482840081c0d43d00c2d06000740c40050b9008004000582c2c41c0c22000d85030342d03111080200d02c6004054444031440300c2c1322249000f030854030401c40c0600400805008a02d403032160b150819a2090100792903 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 369234748 1250 369233498 369233509
    0x11707140108180303040b0f13050a030f0210050406021908070207030b060f0402030a0c020105130215090a030c030803040b0c0c0c361506072a03080301030f1202010605 74
    0xe188a0a01e001801559080c5036600c0a1070412003906550100105110a000541600c0c0c0d00401e1034102d4501c2c07a443d084442c24407071407669402003a540003a4041004a03004580321684c40e43c2c03a00581e6088003040b0710203411113804a604480480e4080b681000c12031b080049842c44280c182003100290400c040b010399500049c2c803006000395444800160755444406180c4040c020203002591242050085c1c0400342007518800e000541c0790100080f5600c4081c01c864100315005011260340b42101031002c2c102e40d110307590054011400704400800a10100c0103c0c00850062025649908051500b98112400a02201c2c9401000e1140c440d0910740810400d21085c0102c1c1d00e180340c1c0b21000110305521882802e603c020707102d031100b0100704110b240b03000f5102d1021540381c540c10310450300030410301e802040c0300980b409103070284031009904a0000081c54400203e805039200303940c0d9580b803070b181d0f000741c00c100c0d00070301c0780301c0300c2c108126401c010261001c940b80001e00085003040302151 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 369235998 1250 369234748 369234779
    0x503030a050313170a0f0e03070510050c01110a08040302070509040c050d060b060d23011d04110d0305210103031b0201050d05040f0b07050a020703030e1801030308011707 75
    0x80d40b0446100100301040714000b4885001440c1c480f4654840c2403017403003e042c0b02100201e2201060f0740c0c020452851401107000c4d026140000e0400c50002440c2c1402c886d00e40244440400c1c0e9903841e900f800309002082e0203015504034690724030a5500d00b42c500241460550352069008803c000f0500c000130302401410003c0c0c0300e081e6041d8031850001d00700100603200c008070064026500090a20040880350003102100e4460554803e02e60104401c003103640009101d9159020b85c0716500c8424402d44401083c0c0040c0520940250500190006611520310000c21008136200250140ba840c68981404507881030340c41e0f2161056141da2000740c01885414072804108030b607510440300316130240d4181c84e0f500420040810030f6103454941040003049240341524100c69550000c1c180d00d206800700e8403140507990140180c2441c6a0f010b070703524890450620381c003080d03540000d41c40e84203100d1800c3c0210300030341e50540903524241e240d280c90604c5181c41d0280f500620780a1100e4002c070715489 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 369237248 1250 369235998 369236011
    0x30c0b0408031902010b0a0e010f24140d020c0102190203070201080a1d030d0e01112521081803090612090c031209010f091d0a060b07050a0c0503030a0503 68
    0x3200301035240f41c0103e004060540d1201e0307000e1101c08000c262061542800c40c16074401c003601381c0516840d054003600c400c1404030f944c0180d070700008031042010700c1221102c14482c0080443c1d070901810300c2c0314106a0300240c202d401c031a907022a20164901122650380110051030020b11315014094000030305a030402407419a0950701d500e401c940c5c0b40c12555501010000c11000c0c1c0b03488218038580c0001414144d10280203d45c01c00c92104c240800c000121354001c00c40d4030007280c040d0603400c03842d440302040c8407050f9860800d1458000803e8602c481d10032012510740d8030b00d95940f4152914103c0080c0191007904141e105200c02c08031a1204422600381541c2c01e03455805030343d5202d0009103000d0182c04d019801d40110303450014206e007410090004610300340c940300c0e100322150500701e82d030401521801c282404a1058076002c0c44070140e0b902c0d00300408510108100c4e8444200c65074030b0340701510840d80c0e584800c95a500b484450a81d2801900341100611320305031403004000d10300d000c0905003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 369238498 1250 369237248 369237277
    0x60c1903051512010b030c01030b061818090a051015050405061c03020624060301031101111c0815030c21011811030105190207020d1b030c0b040803 65
    0x4104401e4102c8000d000c080c4008000c032900c5002d804189010f000031680702c0d0700030300c01c18074008001d60080c080d40c459040c0241a450500600c82c91002d076a05550a106401c8080d1450000080c0721b40c0190030712400500000b441000c01529100d171070001840b480300c02d2103241110320011007100c0c003845800c8950864012580361500c02c000784101401152174010b51604e1060b06007010380118409203c3e200d80c0115400420704040c680d00c103075907a0140103510880c2003006000180c41c0d8034100352417040600d4095140106c414000e03243c07248112070b910010401c80d01890126a120340500d50040141080c10350065182003c20f0307440b40420000b03486000180c0c108804000501d10700310192103034600921608a03098028806003074900005d8480c9012040c1e002420b0034140a00c41c080e00300c41c00c0485000041a0702030f002500840303801c0380c1c450004044c201c00728840351042e1700c0c0c280b01108807280e03c9255282c2005850819840004c0786002880200b1002c8400301c251344001d003c4036503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 369239748 1250 369238498 369238501
    0x7020907083303061005100203070807061e050a0204090e0c030c0603190f0515011e05090409050106031406013c050607060b030606011701170c030f010c02060c190305 73
    0x404803050542c401c07650148035a508004907010b142c012441202c1003580c0d4000f08001c0c40600b00d0f164898968090300d00c000801c42000080e01a5001c5a481c41c80701c1c0000140b214614005000d698040e41e40485850f00801c0902480c07a55101e60003101061000130000c559044010a0311000080050f034410342c00400041da13070303003425103a10400d01d070800d004112901c0e010309920003d1100741d031000010921200200000c3d4024041c020610115045510248008801c101c03859881050140e403c95102e003003240014109020741c0d4040e511410f6150700440e2500d079074600d4000141d0040341c291551440d65990094145142d000300218a042e1210581d900c407001444500b0580c002e0b60003c6001415070244946a405540740070801c600340c0c0c0e440d803128001180c06000900d43c3d07000108121004100b44540507203450403052001d4251f03a22458060002070030155950a4010030340d456145569001c2e506000641c0d010035481da5040c1000849110345810308400c01004040c07541e10070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 369240998 1250 369239748 369239821
    0x6010b0711091006020d030e150a1107080913090803070c020301091713090c09050402090a080102030127060605030402130b060a0f08060405090c0d0f020904080702090708 75
    0x21a0520782080103081e1a02d54184002c601c03114400b80e205450050040c40c03180301d0031500c24041c84258040b200d00030880902c0d00e0300d54001c1c00801802803101030f82c1d100c0300d036400030396814050040540542c0289803590345003c14071030141c504500601c9164509003035800012000c205a98004100d032428004401e07031440480d0042c4448080641000038800e03500c41d1640446004201e0420081d15542040c2d0b40c84144c14150390a5010790fa010a80542003400a41801d074003070040001c005100d4a581030b0b07611485400c80c2c2c400c0e08929200f02d08005011400c00b0b01d42c00034040d148520108110940c5800300080c138030300010f00024810100701d90f014039a101e4079003015800401c02042642e03201008030001d0490603421100a000c40c00400004050346014402c2501c00c0003140003500800c29010704208481c0310100d0115886800c0614400241c0c803281a0315215610840702e15649040a004201074100c00401036410004890100142c0c0341100c0d000c00000d0700364000380a101c0d0140c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 369242248 1250 369240998 369241013
    0x6040609120f150204080114070f0c0501020409151703090a05060d1b110d11060103030f050f030a020715090c2c0a140108030c1b040b210c040b0306010b07 68
    0x2001e000e400c0110f641d03041c40400d80542d0090044500c06002045900341c40c94080700c10a0044610344080740719032610024450040c010500d04911a8000504d0651664643c104035250900365124480300d190040c014280e008040040f50b03103140c0015414850080c000030010a0240281c41c0240000304000c0c1041c3d00d1500000c002c0005c00441c069202210003000307204d049050384a0303420348600d01c60100000c3c0145241c0703030054541005040d039030382580c03030948880700808031036010050100141d4240d00880c001450241403e00781c05a0741d0328941c108039081d8a216603081c1203240c0b0300640180010b2980c0010022610607501c11440c45c49964501c00020710f4008108452107070000800407041c40590155400b0300418010080690301d41100ca50b0724090444080e1141e800f03440b810100c41140300c078480d00707070100a0002c03910040d80008658900f170000524402510400300c0440030101c00d104100c181e5a05440030400302d21403000080d920322041c4642500c00c44006213280030700141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 369243498 1250 369242248 369242273
    0x10e0d0816031805031207021f080a0518030304030c060f0212010f14010512060307180c030509160509061305010f0f05030c10030b010908070603020c010b0604060912 73
    0x49200107403240e800c0003800350500c160020850025001c501003403000748400262501303862010300248098040103540c04143d90000a05903405600010401d101e16039100310101c40c81f03079645c0d40020509010f0340c400140d0b00e028040d08030500c40040d0b80b580081000042d60f51198040c5440c11180c0d006052010050a004c11401030f100d0001501d00848520b80000504803000b40c54148600341d6100100d941e424884003000c0e00058040200c510054689080300750001c10050548180035950140002d100d840b2104403550240c54044c06110070350180702da95480300801d005000300c280f42c0b2150101002d0309010781c5200c0c40c0c402020130042c1c0c403920414038001031035000403c11561140e03199901c0c06241e100b181068211030401280c2801c0101e90150200d01c040d0214000103c0c40109070050035002d000b441c10080003440004110004026100c0100003a031001a030303070514803c8083c00c1d41d441075207060244e98200020480c903a84546040c04a511005442104000c0c91030700c401c80860 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 369244604 1106 369243498 369243503
    0x1a060a03200a12060e06150c0a1110030903050306120c04090305040503070609050f0f0f030a2a0b04090c050706060f091404053c010e0d0207080705010e0d 68
    0x83c0340a030880fa42c47c480085038108204040350341c0c60101050001d460f60030034542400303528100400e14504e518194039003481007040c6628090014030001e81154040c01031442d0400e500b0100b40108504844010801d0000345558107000300b06810901802d442030180000011b5400d001301c480340103c501c013409081304100c0b28403c011850107003801240d003100c00800070b10b04035035042c04502151842059990b0701104810600c4444400b01c080d80b000c0c90300d170281c00b1310905d0124029501120501c0e6004241d1031304924040342c0900542400034641414000c011842c2010341c0d825106503580200b007086040c401c0c000b006602c2c80241c401034240e8001c540b812080d550460704407071070a038648242c000240780c0c11554000c1d0032100c400015240e5513070a24440040024007103442d9050341c2d440101626070a05103210303110341644c480d85051046c840e9402195860310b02e894903100340c = true := by decide +kernel

theorem cover : BRFrame.Cov 369064748 369244604 := by
  have h0 := BRFrame.cov_init 369064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 369064748 ≤ n) (h2 : n < 369244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
