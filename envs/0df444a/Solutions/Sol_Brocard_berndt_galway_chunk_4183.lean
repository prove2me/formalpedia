-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4183
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:48:24.041102+00:00
-- url     : https://prove2.me/submissions/052af544-29b2-4019-bca8-3e4c3b18d41a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 752158273 ≤ n < 752338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 752159523 1250 752158273 752158283
    0x106090e0903030106050403140f0d0e100f0203191107080106030302160f06050307031803090f05091b0903030c0619060b03100311120f070f0e090307060b040e031204 73
    0x4140c072507a030740e10303038a0100b4030030300002840410003400043d9003044d251640ca40d1420807901c5202071400c0d80c40c107041d058a580c5000810040c0505201d2401d880d160b066803803d410050450380d0f10040c02522881022006c64505555400c00c1c0d69881c41881404841c1104109483c5496201c598050180a66200907030043c45600502a48071401404c00011511441407013195149414810394007900001c10803410b040c1e40b520507650461160f02d05030b410034402e55a2a81013400e00c0b886100c6005113401407402500c00808005401d226541e150340c015401281040d22600000f0002e86188914081e1214500401091003544400000b21640070202e0680c00c0c4079203a1070b00b000741c2d11404110707003020351100c0307022040010400c2a140d4030030410011b41840c410686448506190404820800c0346640c0404000c100a10100d00c10f40082c03c0d580060110608180324070325540c1c0215400680341c0ca40d603807120700f4190f03207540c080d4a90201301000e0b04e80300e80b055400381998041c12201613030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 752160773 1250 752159523 752159549
    0x3030c03040b133c0b04050705060a0f1202090d060c0207150503040b091906060e06040b03030306130f0204060e0f0307030203150a200901110613030c0c03081b1603080a0503041a010609 81
    0x13640d1610380c003982c60801d0be80d80c4458541c40582401caa61925030213120b00003d600700110141d0382c40b0f1898280d1814051140400d038140d800320000d00d000c00c10f80c80b281e02c81c80820b000300c0f03095074040220783d013150b0001502003564440b844600d05160038010407a14172094580600204903040d080348040b2812041c10615079a82e400c140025900a60b00c1168160400c00c0054102d2a09504041410211603400a00c1100d2849984d0490344107810100210300100b0700381542c1c2c0340100e2681d00b0104103801502040d8a19070110356150708030200c00c0c1c420074918001601c440102e5100f90b8400070305454480c2045003040154410b58040120f003030003d1102035684a0744440041e015004549452820800700425101210b405100b58811103032070000c9117002001c105c029014040d0812020050b85042a0001459103462484805403401e8414258208003144410040c0c03508181c160405079920756442c6000a82084481c1d030f054040380080002040441d80314100c00b0a44003000000a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 752162023 1250 752160773 752160779
    0x7020606030c220b040c050c010b0406120f0f0f240501290903032a16030b060609090c03160302281103030c03040b133c0b040507 57
    0x242d25a984550300326004001803c00c1c0e1100a5090308603003c0034109440080d48200000000d41030b40c050f80301070030010304080380301c100c3c103032080c0305441e02ca00303045070100507591826080c61410901c50001078040c503440304060060004d0050305c1041c1982c042441201c175500c0b440e2003c40c020ba0320401c4c1d0801c1c401030080d041d20030601d1040c64160792500d2883e00200c0381f5000f406500b9403a03180b2414450006002d0007441d5141007029100400790034030483c071070b850340c40714070301000307800c4805440c65620a04c075010314a8031204000040d650001c40900c044e5442c0804920a4800e076005a500680003008004c010442500550b0042c1c9450010015418a030b01044050380588100c0583c900d21007500a42520740c00d680d1328103416100d040541200b260844994203540040703c0e56a1409400400c000070000c1d20b21a1591040426641001d6000caa1711054440141c650041d00040f81031120128044c1c5d102ea64407450f000b942d02c01c0e45501d00e80e031500d007410400680742204d16102d0700b4004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 752163273 1250 752162023 752162029
    0x50c0304030b0a1e09032a0b1501080702030f070f03030905030a030903030c020a021503100e1003020406050406080618010b03031c060509061503100b03010305031905040522060503031207020606 85
    0x54a217064165940034044180a9415040340041a0021401138032071030312a4000b42903c544584500d0700c5d03d07507221085003a00009005a180140341d0000c5420804c10780c0020304501c2c0c00c1c5c50446030442c11032400c00326035160940003003444130400751443c480030a10481680d0b25400c0081210f10942d82400710b656420400c6e641ca02b54a10000e41c40030041d0440300d840d9080e03902840d40418041011141e40780d0760f220f00b608210058445810320b019030700051055003402e018480081c03400380c4080100d58a4181056290a0302801202c0003220385641e40d104418250400564200c00500b81c944d41d982040709881c0300124508200ba9042c00d046002032140f0b400712240d80700c2c84029211180f0740f8100340000e05154402040c050002c42d03250404949400b0200c095030203180302d8001540d81b0007604411030240200b051040f82044006c0000740034549440181c0035841e01107106212441045542c00c101800300758114540500c03001c41c12200050b4203429040c041d400c41d401307540c01d41d02d820f014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 752164523 1250 752163273 752163281
    0x30709090f03090e090c1c0b0117070f06050301050108060301090206040f0306060e0c1210030506100501121109010e0303040302040f14090f0c010503061906030515011e050c0304030b0a1e 82
    0x2810003186c01c885c1c4442a40e04001070708a001140d2244000d1010340f003961941c41c6102e080e00080480415003420b00b945042c104164000f030980c25100344c1c21145080d80040c1944014010241013002c02d4020401e1500d00350400e4074901c0d40148841d0300c0d2600c44050942035a540c0c4810307981641400740002e41200e07072450b040d0003141e00c180014506030303032030058607088800a0b00e1300c02011541c1c0d10000201d0000c1c071400d1300800b001c00c60f0340760b01450070303000501300c03240d83c1d034075103001d0380303001100c0aa00c0298070844180110a003440c1d01d000048900181c1140610ba1029400a0030706041440c46515503205985048a241c030700303200c80d1a803030680b6658503060418410315038001c00420700c0a602840c081c41d4420002810050301c8002072082c0304050380b09901c2400402c0d00e8809010b06081000c0c0346003a020741c00c0c40e0965004814480e04180100c45c07079410410300000080c20001e451060040b00e000e1030304001c4545503800c048003060001d22102c5981541001d0801c40048018032a0103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 752165773 1250 752164523 752164531
    0x10090213030f0201090801020c070614090109030201140f03090309032a0d0f020d060f053103090f03050c040f020702011d0f031b100203030c07030806030709090f03090e 74
    0x340601860309642d62500c60b0500c52030700b641448040b400002d4410001d0000701003084010380030740184e62070210f01421412072000345c4070320b00c0000e202c44030322a60700144c03600c210b0b502440c28244116204800000503c6030005003400c0d800d0000170441e600c1d1001008000019050b4111466405030f032100035041c25041d0400e801e8203044250041c29842d14a8500f60b900340140e154559100e10b69001400c0361501c504200c80464403401c210f80392680d180304080d0700c09000d40c8400380030340000a0194000030040d00c28400b412250710f901041c14030032031504021b0455001000d440c55140d0a00350354490b501c041d524070030380c02c1071070044d0341c01d0140c020341380c1b030301c0d410703108d030030019009140640001444020a039040300c00c46654072650307030b0204540d8100701c806844417881003840c0010311030745c01d240400001c2958400c0040c0300000790110200d074500354051800c42001c0e1520b10010341000ea49a00010803e81007055070b0042c80140840e1495480c032a807240703500c41e90340c2c1400c48501c1408079 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 752167023 1250 752165773 752165797
    0x114010f0206130503040f09050f0c0301060e041104030c0b1306050a081303020c090c070516050d0206280f11060912180409050304170a0f0222060e100902 68
    0x15003c07030b186900305a1a4940c0354454010b49040c9a100d03828412070b8a50350b400210410384500502c242c144442404030740003910840e00915560600384007400305450341050702c0c012076031007500b6130941300c0c0b4030103881c080c43d8003011400364140da41d0b41c104159040341040c50304100c2024000261030740110b0446070035001507118807545a8030b103c480410000b54003001c1e4154022840000c42c07540d15001c1c0780b8890410a9861903d46126040072450030302100c84014103000f0b080030502c087d03650501e8120350154104d031400c1d510f140702300c2c0105154881c46a40480102f280090201c1e56030002c201800c0780000380d440748240740100f1142555014281d601e94920303040360a10090144008000304450009032000799401c2e00841c001c201212600c0c501074a99810210b001c2c040c000e0501c25170804405000300818003205540c82d860250707000303804028410b0103806841c094882084245041c00c103450081004034982c3c03124100f08401045a803c034031071341c80042c017041c0c110882c401c0e222410044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 752168273 1250 752167023 752167033
    0x30210090c0e06130c022406131d060106030b01081e04060510052220030a0902010c020d0606030308100b040b0f16050a0c06050f12180a0b0114010f02 66
    0xb41e40101d050280420307070042a1414880001c000310702a9214200d480d5000380603076110220040302454451a05c0b0003008015000d01c0525900c1c1500c28101c1217418000040703e11001d0000c101c485507503001c030081405840000540150140d2140d40709200a032900d0130281da50080561440600c1603041c07441e40524000302d004660268082c0e070f0b02011000302c80301002d498a0005000c04078003050286060390941310180380c0521401054115210001451500c21a00307070100b5107400001c052010050341e078084a4250383c46406800011fa80150500030310b20300030304014010b09014042900868901004540158240c440010480303003050351700c50a050502d080c0c00080e600200f550a480c41050100714802c10b017500b072107040103210b00028000d5040c94030b00002d15070f0f6164015824040140003881d1640224800c40303103c44103e00140290795605070502e610030790070409040840c460320b03610714100260502814142c5010592590f429860b40c8011110005107509034001a040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 752169523 1250 752168273 752168279
    0x90e060a0b010e031501031205132705011706011a070b04020d051204090507051c0f09060f09050f1204030311030c03120609070e0f061312030c030210090c 68
    0x201da206441c0314005250a80181e00b0020003e0301d4040c41d009680908103103400108100300b250070b0300b8100030256003401400c103100e10a1102d640d02c424400e4000603032550b40f40c0c1514080c0c002d43c0441a5800c00010001542c4442100a440340c5191a03c42030b485404000710f0f02407160030110f2582144000c0c002e00e000741503941c0300c060310005002207821903054100702c0d0000b4810f00c03007a4510950200c2d06a122440c00e07144100781c0340302030001410b000007040f0100d200c0c0204108610310110503200800c034079120072158001428040400f401c40c0b403815070814200202138007e9044140140c3c11611180344811340c840c0c5402402d40d07120700725502040200300080c061640c00c801450039000707407410894407000003825a400004032400340c580140400c40c80340740000e1540e03000079443c0307002c0307210003902c0740454030381c2c011954042c0c0304040108030030041c191002d00d103c0141c00c901c0304101203940c1c0703464040c0400803401000c50150203203100d031000c812468030640709620307000440c00d01d500349 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 752170773 1250 752169523 752169541
    0x2730020604090b0a0b03040506071205010b03060618040c020c0a061416210801050406060219140109062307050c07050411122a0703021e0a05070b04050a090e06 70
    0x500c807901d603009129004d0000c2c0c2c514403078016601c0380340200041c1c0450300d007054005115846481062260525050050101e5440c48003076070f501500640c0d40954070b2003881c849540c0390511411599206003400c0080c41030503030100e032002600e001510304c0c0f01030a8032041e0030f660f194503b1202041425086c04000450a482058032640d14010145104c1c5d200209551100d8404010400000b0411040c010402801e0a1041c2c000400044c400f4103140b514002070414018030000018001c40c44109a61440440a60107400d14907408441006501400764402d080741c0300c484802804c16101100007031981d401034084030b190700b0444015212140c00c041c2000002c10700f040341031a072100180320300d55009180100c4c2900481301150158205c54150040c804040e60325000452942014031560340080d40000f030900d04401003c900c03c40240f0101c000c94501490032402038403a2290a000050709410000200103540065036158812a15442a40161b48840581940b00d0340300b0300000d60300d01e17 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 752172023 1250 752170773 752170781
    0x901020a120c080310030213050411010e0a0b0d06090501060828090b090c040501080d0903030c0819080108010b03070f05092e090b10090303273002060409 68
    0x5007541810a546079254850002c00e410440b01030407841350401081c02540362035604160b985440386014003140c50180e0fa2070f41210540c0c03000a042c8428003211407c0c1e65074203a00e05d000340c80030b8011103491f0391203490b00d040682110702c582c028040c40c200010561038842e8201500c82c6500e000190810b004443c100700c0300210403d042444d0603a188004800903205940b1a8000d410400040111b0014441040101c070410782c040421503210382c031860a040e030404140c004a9805042c00c0801c1880c82c00c0c0500035104100f000340155960300c001c8a0019005840e25040c0c0e500c0c103000b00482d41d1840e09040c0c1e21040c43c018012924020003041019280c22070a15601078411901e9403620811034036020f581c005203030803810b80301c2248601882510818072840f550750b002103590f80900003007500d01030700304540360001804000b07156080b030002001d10040008402c1100000d101d1941c0c1e1250748fd9000c000309600036820702d2184601c1a003d01a10901110b060b80082006280c949080c01100c018 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 752173273 1250 752172023 752172053
    0x9061b03030a021b0604080313031701060504062c0d0f020d0602031b0405090c09030a2315010e04020d0201051b0105040201090503150109020d06080102220b03090303011503090f050a14030901020a 86
    0x40250400d4040c0960103400050086c6001c0d142d2b661200d040640241460444814410306400b0011590000c080111da4800760790b00261004100020305041c100c041501d1024081e400c0442502c0a008101c81030b0300652003460700c03502d40210400a100500514801d91064940c04086a4041035072001701c1001015000002411200501d00d5a551000c0745840003400e80ca07600100811201910b0040c070041060b1485e0769400403496042610403103080030041d0010303014001c50ae842404590240d001c5442c061512030003545010741c0402002e020344812a0304a0000f50b000c1030000303090900180444640e0791125128856a0074802c2500c000d400058031011816103410002807688006c1c401020030f16178051001481030805529810b60000035400301480b40401c004204150038040300356410340304104182140030308a80f50460240c00e8150f0050450180704815404000700080c1d0204d40301d1081d02064036803845414255101c0c0030b1907070303a180541c00500350200044d914072801290 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 752174523 1250 752173273 752173277
    0x3030c0d0605091009050604093c0f1118060d0c09020705010e0106060c050a03080403090509070e130507021e0708030301060f020c0a050609061b03030a021b060408031303 75
    0x18030740c1d02d00005580d61002c0d0703042d00c080300007403e05000092540c042c955012005076410700ca01c14050303072503c0f48131111512000c50f40b40e01c644503000c2d46464590210b800d120041e925101070049003000c1c4240b42202c1022503a907100300c03401c030135a401c1250500c40c40740840b58070904039a03104400c0c443c4c1d0f207075200c904a07800401e0034000710701e030345440c80940703a11400f541c0000b8649082c0c5001500b1a00c05d9001007040c02100c80f2824002075000803c1c421490f45417a08850726111441e05681c2680e82e0b4000315480080b01080010f071940c803480700e00350940e0468541d0141210f03070100c01c04481c01900e440005802801040e450308034104154407071101c0010803605210380d22080c0d0350a5400030381214000450103145240fa055040100c00c6030350f88100c2c0d2980d0302c64644400100030b0720403c00014007a04d00414021801c2a906a00d02030700c0c902d900039a6560f00d086660700000358000d0203800c1102c8208054094450720000303e0701e02c95603203d001ca07850754072004a040100c40008030308a003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 752175773 1250 752174523 752174531
    0x3080705070e181b031c0905100509010f090b040b0a260f102601020910080703150312110a1a0406051807030204020c07050d08091002070803030c0d 65
    0x4040020b95038941c401c0384070074141592540050700c11401d042d10095104801200e4202c504182d070b0b8003040d0010900501d50011010008210702070741c0c0c000039503014a0f4044c0c00c1074480301c3c41582040050603003071400d0762030f4241840074040940301109a0702518411703210910050022580c004003c040398181800e1036a88006e050b280c180c420048504410401900a000d000c1d03000c1e103288030150800301000070010018103045001c48a05030010f044209056070882d800d20102c1c00b94110751a000000d8401c3d1140c030315600019102c000203648074800a480c100f075424a148001800d0705c16291301c10f100c400d440c001800201c68034900019040d1041c01651050f400092080260604001c40041103880501c0c0500707110040b00c00040a80c080c13412504410704010a0108089060700ea04580050300d03120352244c11840c0c050542c01054001040440e50f0044c409020040c0c42c1a103c11034603400d2030080c04800b20303224040b6202d081510303030062022840d030605080142c043c00c401880002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 752177023 1250 752175773 752175779
    0x2030604020423040612050d030c090e0906060a0504140a021317010501140907080727082a03060a0504080d05160e010e060706020d0b0904050f01060501030b0a0308070507 75
    0x425081501d400200d2506802520b01500381024081c0318010940200c20000441c0aa02c547d511100d021280d00e040598135200350307000502500320000035124046c1001121300c1c00052140e0380e000d00f84c480d1403280300203902c00644c5103071a0080d10500c01f040f152401807034540304100c0d406504910079035451035550210100300038010f408a001301c4180200082101e514215050120041281d4540e028180c80400c100c1081c0c0c01c044100d800000700d143c0b44506000343c100078194000b4103100e006001d8404800001e0b1030000060f002458100701500c483d110010001300f206030301d2107190a0b40c0503000000059410400d039030005620030702902174a0324059120080707808984085a0b458100d05603818180203d5a1201541070010000e0034035011600510000580790f00503c00002e048a400284a84648190303400c122906c0001802e184041c0c04c081c6801601c030300c014001d4104d19032a046000805610a00404880c2c200140564210b1415921403844070ba22801c4103449500c641c0b8000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 752178273 1250 752177023 752177039
    0x1509090213091401030b060a140609210705030609010207030206070f0c050102030106055212090e0a021801030207110a06030b030f01050c0a1b08070506041707030c06020306040204 79
    0x50399080d003c210003240382d815490140321010740500551f0280008040c03c0c09815520016181d05039406ca422940302c030410000551000404812040006040d5501d022140d40025002050b140100d05541080e550280703114201d00545001a0040c2e200354041303006140981d550340c14403030251402e9050308401c0e4a40e14260f038001e03400840080e0000500c070641900d0040c500883d040d6a48000341485005000d9101c561044604c000b0f0f0307101425000815091107401c10b02d065580020485542d02c80010040c1c840001882013003020b481400c0042d03406a280e03c00c88001400701642071150300c803610300440007500710031000c030341701024800594114ac0c0c602c0c0d4204000c10590340c0103e5a04120400d050a10711117090307182c2280c2c180000d00001c0c407402e606486210000345041e461610086441680e82d420701d44002d0140c1500040000070721401003079641c4204e010315117901554030808040070a07403040c83e6010300001d5030005aa40003038002d070000c503080100100302500301030302c40c408 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 752179523 1250 752178273 752178281
    0x307030606081605040c0c030e040207050615030d08091507121a030d090315020708280305010e040b18010213121b0b03040b060102120d1401150909021309 68
    0x7280207035500c0043e07803000c12a210004600900000d83d818441d003590f1703190150040703030060802000c4c40700750100c054042d100c40c2d050780d10203071300201155680d0802d090145405100140550f009018940e01344006601640c4046d0082034042c0040c10340c0c0780255070072600490f019010008002708903002103142d91072405480c0881920048031598a0701400806103060900f034092001e0281030001000400d004041520b0800c9508001607a01d145070b19020009214150a040b001d03400700c00002180003d41d0008900d0350f109450401060341c0343d40c0100403000d0b0450780240a00300070b400103215224003d00740480c400c032010001d801d00e24403005c05000b2805a810950050304002701c20014426141c800541d00c020752514495941d0a00002c003a070341c4401400a0041c0f15a41d01040705a4030030054403200304480c00721561500c42e124055000341c00d03145500080414254000314500c2e0038550141780c84007694032002102c524000759040a50440d04e43d180e0300000724100041d64a025000e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 752180773 1250 752179523 752179529
    0x61707060c300e0901060909150918110a0513091b06020c0a0b03131e020402040f0504150503100f0b0a0e19090c14030c120303160e060d0b0307030606 66
    0x42e0602182c00d0031801041403000d10115840307040003000401c40302d50008000004ea034000070011842c0203424030880c4400c4c0b21030b4080e0101a207414429031b180d50080e4130341b040300b51044001c40d4621091034100010310f00c1500603254400280b00301c0c251340910a51091480510038a41e548000d035020040307204191550384041c005d60424100001c85e0b14203003203501d0140034014072060450901c000c0c6040210840d1600800c0c008405003290341034003071002030b050b00301c4d1300810540da110740b91070070201410301030b204140c00341e810070b04201e29812416198000743ca00140080044041c01d11811010f05038405140142c0c66482c04074550310388890111001900d020b40200681e41045500c5e80381c500010041e00b82500d1038020040300041e4119000c1007210f10340b140b8200807400300d00000c0d050500c401d0403c0d42c802c40803104907012031070101c00b4610071800010702d400c17600f0454400f92209a04511500e03444041040a149401400da110180d00d28010f000c035860981c40380e40c0c0b00c04503402c81d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 752182023 1250 752180773 752180843
    0x2090f060f10050901032f070f061b030f180605060a0b1207020601051801181b030b0906010e0a0e070c0210080f070507030c030e010e03011e061707060c 67
    0x1800c411301d5601130203524620840d0b021008500310702c030800c22a00c842e00c924084083c1000040310418440020345003171b8001e421170b200b000f1800005000b604e80e4513a102c0e000b00070a041c14440b4022440a124000015100c00c0c400d003400f03200d50b551b0600801c0d00030000c9a004410321000326031840080041c00541c0c0e02d4441850541c2003c0c0c80103458284142e01007407043c88aa1040203011901d965031030b0440e060800117500c0c250500b19410003802c090041c403410b0301d000c0381304080c02907416042458080b405072100c7d0000d8031440011a02d103464246919041540b400c0200030390486661390650000e0030b46011180a0f200f540040c00c80f56000b10860000360f00d540621011031100c202c640d03005401070400d40e203000102d950240000800304006028800101c54644480c0d000300c4801d1040b003801402041030007807142a4145109c802640180340615200d8049070303003130000244481690503100200b14091030720700200c0d01c503500180d0886401e600382440500c40b0440e2070541c2600c45d0b0310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 752183273 1250 752182023 752182027
    0x130611070c0302210d0e1c0515090c01050708090303090d0c090b0612061009180e010605040608120a0e061801080f062b0c0e0106140702090f060f1005 66
    0x540100b03c0c40c04030b00c0c00c1052040404d09034200507400000390800c100c11180c240707000443c0c070a800260b02c17140038005d0940c52201307103410380302082804600e003054641e201d01000011780381d81103144d940d58006802c49000c11010828480460b03501806440b0070030700202100d14120080300400c605805000080b20280c180f01018060301800b4010b80007006002d494050402c1074041c940c40c12030703d015110034007528104400340c62042c03082d41d158002d85801e190540c8141401d456900c010007003880d140f0090b5103001d201040780e1610380540021514008010140000c0c15580300145610a5010400f80b20b074030001e842c119118440900401d00e1914040240401e00710005401002c00809004000d120002080900d68036a40e84a04001031081140ca100c40032400c40781051441010107820803064602c000380da10b06060050381a9840c6548100345070307099002c220f1007805020f00c025400010304000804c0d0f10007100150344d0003140100640b40c80160080401c1c1e0940e080e0000d00001140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 752184523 1250 752183273 752183279
    0xd0207050d0e130c05070f14010e0d110f03190512010801150e2a070503032a07150b010c141507090b030a02070f020a0801051e040803130611070c 64
    0x80880303020048802c94000740004c90100400404c941304500004200303251110030070090141d041d8803c00340c020820700800000320518000f80c4d17500440c901d48000291620742c4540b8024010900d0f003443d070040c100a40c286084100d4088029560701c000c00c0c104072061100d040741c6000945941e0080022100008008040854145012802e9000304441450748002e100320a80f0088040100800004502500300300d0a01e080e1014480e2000140c1984400700038403002e214086006d4548600d8004420100c92422100d02101d014410005e841c4001c010b0b0f91230034410054000101d0500c05142940307042d145561204803800c0f00300a120b5040d0710010310700344030b1047c07a803890307811001f01d050408182d45003055980041c4030041101c4001d50f0042050003c00c007102c0b90039103150364018068411162540c1104e40206001c0704c1980e40d2030006d10b00350200000f410903040c0a142c10141040ca15035520000900c881e500300001ca41842c0e13107132240300c0400c1995014142c0c0511404800108501d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 752185773 1250 752184523 752184529
    0x3010e0d050703090b0301061d011b03170f010b30070f0320340f05120f120718090209031b010906120b04050117160303080c0d0207050d0e 61
    0x580ba01702c41c44000041006010464000640b149510104004004051540c40049407038502c205011410a80c080c00301c0005c0541100d580504114070b21820701d200c0d0b98110340760556680038880d2800b01c140c00c20050021040420550181d45210031180024150a01d06107460b403000702c0b60000081e4210080d840c07070f16414007d02400c140e4084615181e601d100480c030a00f885000c0742d107503280c80c0884d5210021507954141c1d9002e1403106c90549175041c0d0906109090014000c001c03541c1e80102480c1c1c0100d00d4468058850010b540e03040e241c00c2c0581d203055480e00100141420003400741082d001c0800c500b0200c04e200290140f80780c00750301c1c1c1c030060080c140303408035030100005107a15007902078000d642c0c0050744508880d840e01d800c101150b00040d162000309543c50125402c036081000100d10058580752844035102d100c000c403103c1c101c403890340d40848880390000500251000001c11803105400d4040c0483d00d41c0a0b0005140c1919070b614245800601250310000c43c2e51031541c3c0105103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 752187023 1250 752185773 752185787
    0x72601050f060102071701060503062a04030b0c0d0f09030f0e0f031005071116030c0504090f0303020d11161a07120518010e150c0403051b03010e0d050703 68
    0x420360000038050034070b03000103900c0e04a0f600401000c400c15008802a090b02500904000e00c00601921007500700b00001e80320070143c4403684418814803840c0410320621ba00d0071101181e030000c1c0b0321081521480f00008842e40190791055000307845428a00700d0350010711420001500c0713502e0f080341301608020090030812215104a104070040310f20a441c40e140803e00d0301c15548030303510005644da1008420b0341c150b2000d00301a01c69100300343d900050100121060030549014010760013207682e80d18104410750702d02c144010030030400100000c000a020f5000ba110036840007201144003943d122596003039070006041e030300a0210240c980070900180e81c0c250000c1604a400c05035281c5080d0b68081d0054170420b6104126a90320710000700b41c2c2c00859501618004980c00a201c1400031042d43e5968041200350041c00c1c49801c0003083c071030b410b00400c8030100d03507102c4050001140c40c2100702d49076003102c0300305c0c0d5019526813050034029001804030380d9400b20b154403411f1700e9000c2410010560703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 752188273 1250 752187023 752187031
    0x703020714100e240f0402150f031015020a141e03130b07050304030f0206072a080705030c041e050106050309060703200d110d0b0f041a1207260105 65
    0xc070140c0b0780a103100703402c880513041c2e1001c06111124010348403480443e03100800403070008610240802d0050108801c080118080c424004d102c01c100e6840d0a143d14800d0b08210381400540c0c8103481c468001004c001c0c1c4180a140c03584156a02c80c07400348000440c0200d480c003100400e07000096003010f0320110700208005000340140710750618601c1d5540640d00d100c1ca0002801d0a0a15408c4200310f680c0d401c00c07100620303409659611034140c066010085a100001200318165680d40045480940003d00b40e007140c20050040c010449200f040c000206004140030300780c0c20301e541d115100c3d0000303402080c0c000c0a04e07030b5803a581e1780f030102e0300603050070380160040c400c050030990255500d030840c9050302190106440c101d9030398405040d01b000108001d543c2c80c802d02101044400c88210507502089440d4425502201c02c034254000b000b0842d40c2044148000441500e498240d500f00154045504010041220201c03030f22101ca5820014100c0c10071070340031051100c1e44018000a0041d030b900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 752189523 1250 752188273 752188303
    0xf032419030605040c080718290d060b10030c030509060f01090c1112030106080a090c0302010e0d0f0b061302040317070812040f14012a120e0705030d02060c030703020714100e 77
    0x9d506414000c0c00c000e40000c0c00e401c0c1c0302e1101c0e15200c43c14007400e0b1380700da2a00030f0000c01c4140c942e014150041c02822904840d800428900300c0014501e00307001c40c50511840f50307050001102ea0030300d86140001c03d03120300450108054403c0d144503000003044074249000c94902025201d44c90b041c1e00038078810300105220385413824a01c4040015200e101e60a00b80c0c3e50900345040440c1e419404030b2182064030038041c24049600390a04280058401c110b8024142500d1080c0418507205e000800d80c0300b1413000502442c450144200454400400b40c80003a01c2200183e00c0d10040413031407044240c050720192070302c00014a110b400c010107440940d9090031000000d01080c020742c0984203481c846c0da40c18101e4100a0007900c0707a41031040104481640c5a200f080002c82a195801c03950f404042c080d40f4080d10601c84c0000000e0700000d96540708550301c00244d4039507950088110069000a502100c02100f01403060b180c404003403040701b100c68051600010410a840b202c0b514080c1c0120800c12 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 752190773 1250 752189523 752189561
    0x5061207031707080d050411030c010203041202010c140114010501090e040201030b0429030105090316120c1208060a05060903150c0f032419030605040c080718 70
    0x4a25600800c0c628101c036002208040b01c424480003507511880b42100040a50340c0026030b42c10b8040d4598440740c0950701034881000300282d481c0030702d695440c000d17070140d016a009010030007500e51701c111605811841854942e00409103659141d075016440c001c90100c0365110801c8108c0b200041b140c2c41d005010134601044028134020f507900003e00c0c0a4006410144c03600b1a89070035032165041000c89221101d40b10084200046800905c1084100241d1280d420080895203111000041c1e82c920380c0a0764400c2e10504480d82c405027031010144400f000c0c4144200c50f4400f0038241c1044112907080c41e1521346107840d11404020707000015404c81071092800b40881806604c000070f440d1807590342801d04040540790095501054000c04815010f4604000200301c1c00c1030140d03000d00c0302c039021411b078035030f00940302da04000f000100a01070081201145508201082840c1c01031900540110002082c8546406146007403500c55000600c1300c0c2c50310b8420700302a840d14460090448141802c2c04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 752192023 1250 752190773 752190799
    0x150703091d010e0106050d0e071206050a06240e03151e090607210f020909010b07030e22090803100f1424070c05090a09050a02060a030e0304080604060506 68
    0x76100f00b82c1030240808002e400b042c0c040e40c03c4804c1e4071405011a01c83c0440d039045586404490200c40c4448040364041d040c03401140c117090140c019503060312450b0340c81c2000f041d407010301400a074402e0ba85000400580825155484e20184400c13007002601200440d0300c1e191501140a18a2444c40e5045200c0b0490040001c000004076040d07420080b5468018415040c41c4481d61140481d030002f81d40c0135261031100d50703a18407550700420030200140d800e406242e1780c40f8030107485806001000b90100351944294450ba240849600038200845002d000c4074061503884c0c00c0464014460880f01c60b18001705200900d1030950a140041c015040f690010074100f0700618481c8082602445c01441082c4000320300c00d003820005056102c82c0c0da09192524050f007824032040140d482098014440c14022507107881107401210301c0345800400a0118418640c280100f50b07101030711340c00802d9500c0050701c040b0b540500c001d0000f40a0403004140c9402c0c40c1c1800001c950028001c6031041602c05c80c0d032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 752193273 1250 752192023 752192039
    0x231e0f032b1409030c1e040e0105070f0f0906050f120a0f05060a030c05060313140a031733040c0c020306070201050601020613051513060606020118060b150703091d01 73
    0x4404010050306c013003045030784142c3c070154041c0034150015486400d190380015801d41c1540b00e288540e801756580c451404425406030344004c940300c807090000e00202828894240a0340050035100d50b400b8801e1326003803005918a6803408161500c40030107803034a00c8510300f4125402610342006086481210740f900e10703035442030107064038840d0f94050407000c03001400028040b6000040700c0c0d042985440e029840740c0c6102d0300e5a0046508070049044203180174010001480c0d02d034070030030010f18400e41c44080144201e075000031381c941000d6410099440c400c00d80d00c0c1e50042c169540081d454030314a0a01e50310405080c20002450802160700d018100006680d000441e603801480c100c03240c1c0191125424464200200075002c82c2000c081340040c011100088c04030040503a00600040200d940c072180228261039000841a80100740c0c0e1059001240e80c0d81c0c003049561800420000b52500b00301000c040b01c2e0802941a0049000003808020f07062441212241021440742101e40540c140044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 752194523 1250 752193273 752193283
    0x90605041805040f0204180b0a050415090c08070b0a03060801230a23070206090c0a091a04050c0405150901080f071107231e0f032b140903 61
    0x411000742c40e040440c041c040900c2d03146103240e401a0043c0184079003040000600d01002d40304440d942e84800000b940c4645521038103014a500c032105043c441d00100101c0c2c06054186070542d460000c02c0342c0024514810044080181001e000c01c0d9220b50b00300202804a85050b44803100d140d0402100700c00d004004003d064041c00b6100340080701b901e90502050040440189440422614000c09402900d038003240900c1040160f080340c0640da00c4484054450b6059880d40342c00100c1c1c048148290849600043d044040f960303203c0342100c00040005090302c2c42034500980e10707440081d00348901e0903e120714417403824035501c40e90300c1c0c104000c00003040da10005110301c40d0010303010b01080c0a903210380300ca0381c801800b400444264030784950340d058041e8401e9031044051101c09405480d20300f482c0c42986c1c881c84818040b040d12880702e005000ca00c0c00c805001e1985070243c040141d00004882c80342560742203030070880d22070441d12242c01070a001c0441e02c800500035405d00c082001341c3c2d000a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 752195773 1250 752194523 752194559
    0xe030a0b07030507180b18040c0c1214040b130e0403021207020a0902070b16020c0d02060a0212070f060b060702060d1e09150b060408061b090a0e060109060504 70
    0xb03800100c2d541e03056002c03a49503000a030b025203003e0108100180081072400a0081c0b00e0324030380f034090310811002c00c203c2200c1c000b102020224003091540c40c041003c96030b02000418603410080c40c98500040e1000c0c0d01d03481038108450404000c40c80c1080382d0742e801d486001a0010140c0e44c411070a15440c082d54a41c4102d846a0300b01c0e0002a0460031502c4070841c03540103001e400c1055445840b0341c50440354201c0110b0f4480103111408030700600c050301c00030301c50f04600800383c01920b01040f02d40901083e036103d60070040951080245e8090440ca0b00c1c0000d0008500a050302448000f003407800030140c0f0f401c224198407901d030900ca01005695aa0110b880507005000d00145510181078508100b03045a5607061019181c10450b20502400c1d105e03010039440c3d00e450422a044540c4100602c60103580680f8996078400400a041d0601281c0342409030540031402e10300b001207403000502c21014541004040381010400d00c000303560001610760203010141001402c2038104080e242000c50254 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 752197023 1250 752195773 752195777
    0xd080705040b030a1e05150402040501050a03050c090a0b0a0206010b0307080a02070f0b010b070c0f06141810030e06070c080d0c050717030402090f060102030909090c1306060e030a0b07 81
    0x10100d8511400c561100f06505d0000514030b400c001c656584074010241181c0d4026903481c21007001132103103010b108950940324161221410301500003011001020010002c0c04d0041c010010040b00c0e640b518404402043d00b001c4480e500c803860034000341458810b03400b08820400901c207014615400160942d800703000c00b4801a103400c0103040250045040d0b00e8045e240032100000801d02c0b2074000000e10046001d6000140c4081c0d840e000030b02c84030458030510300003410400b48641d0314016040102480d4002e8441403d4120501000440d61a030700400ca80100340d4901522034042030070300407544e1001c1c6070b04141203401541e840700e01c03292162003144c21655a035410b95802c09070040d42510b0788903400000b010071058184a034008554019101039110f8140701d030005180906800d8118411601a8081d600740b569500501038200c5015000408d1405800c1c09401c00392900b41c40782030421003440000c51082d160100280924440701002d1b03011380c2113094a40003080e1300d1100306800a400b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 752198273 1250 752197023 752197027
    0x20c0d1706090406090b09061017030d05090a05030f1306020d08060103020a0201020f0d090b0c07030507060b0109030f0b100b04050303030114040e030c070f06050909070e0f06070f050d080705040b 86
    0x40c601356000f0948007200810b0f21042c0710901500d1000054a240300d131014401d8281001c0d200d811300c000f4480040d200032540c1c1c0c03007000943d10002d440d401c0580c0107411802155001c0c1c04603540c403421034200d9606501c000f5808200020003001c03e41c441d82c01401140081d200310030000100400c0b0040050610341415000121119221b1007581100c03601007100c0300d100e44035244001483d02034117282d8410f86400d0002d1000c2090865071608848040e9455201e40e1b140860b203541f4200a001c1c1640f2081c10b11038540d500201042c2c03071040070318805114880b0310100c1e1404610301044044660400f40d0400410300c4248015103000046074150b80c00f0300c00407102e050f90b080020740981030162202c07005000204072610003080000b07402c0c090782c45c1071103140d0010f6100c01c01110070780160015940c2c40140640460f10441c05403523404503aa101801e915a85805070021803855440804c0c200c0e40e40031202c3d0045d0620506124581c55102c5a00e0001c482c1d08020400900d40d00a5000d02e400d08840 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 752199523 1250 752198273 752198281
    0x9030c2d150c0c05040c020304051504060903151808031e01060c060b030f15041104090c0311030a170a030e151621020c0f16181d01020c0d170609 64
    0xe01c0300f080e0018100248244400c6801010081d2250000d102d4280181c281343e4513100c40d90398203000c1c6e405030740c0e03999594001a0b2454660f001c00e2080c014a61120541d5901030700b55043c191650b01040310700564000b603883c1030805440c191141e41007414207146203c20b006102960344001003079402074110201041030543c42c000030b401c02000d8080c19070b09100707003055802490800716140b0303c507c1c01150021103034845801400291403c1b10f0005003d0034601c0001c0c4001640314210800b4084090112002000305584440c448a884624400ca00002084802d440c1e9498000c03400d043c040352010b031076042e407528031079074100c0c202501814460306e0545000d08101d00c0340c802c4480000074102d41d411481e00001d0680001c2d444010130240a00410100c2900400001041e00400281034206805680b40c106490104000d50382e40b5510071b41c031150340d00c407101084020001051039800005a952866203074452405c2c0c0c0750180d46007444907407648000010102d5440035406030701a2803007841c0c0c0e95 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 752200773 1250 752199523 752199533
    0x17091c122c0708031602030715031506021207021201020c0706180f0f0b070533090309010f1d06120a051e160c0503070309080d23070309030c2d150c 65
    0x44941002c10521884c2754800c9045a241d0401d11040d00ba801c2c0c0a1005501c600c0c040340c85240c07081c006000000100302600040c140100d074042c4041c141c900050030640c0d06030445003011030f2039000000155001ca000046428545900c00013050150008044c491501c1c1104032130700704034401e162541a011032400300b4014140094983c1d0b01907100300340c04483d00c02c55420001450a01d01840c101c0303030b1100040f803014001044520483c4140c482d9129a81d41c54401c554810b55072458400180418040712100d4071000040d000b001d09002110526152101c20401181e0004080c031042004060503001030328502e1020a400003019003984000700f60841066518601c29040244030303101c001803036800c0c0740d40300002d01c00b0785410000761946c44110000c1180c074031038021140101c3c4140f031280c240314680c040000300781440c445d040646c60140e489c0c83d01d0943c00c0c040d43c4000a070000c900c403025034601c280e9090422028002d054010a6070900c0a20041c003440400658180243c0e180b09105001b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 752202023 1250 752200773 752200783
    0x6061706012603040303030e07050f2d1c050d1b08070201090b0f03040c0503160603150e01150806010c0b01030f06060305030f0a17091c122c070803160203 68
    0x21044908480ea030300c2d175078a8024010012100e1364011406102e00104151504840901d0203020052201c400c02584822640c0c0030801c0700d000110741e9202112500c03407625000940030701d044203225524450482c03420104c1c18501c905002c40d0800038058a0505c10040c0c0e00c40010407283c10070000e030b07151502c910041e940d110841c1c0000300b0010000c51200300806041e0002c40c826480341e1551866070790380f01c00341541d500c1102c641400d50402e8650900005100b036008010301c014001d03820ba110742c0d44d24084c0314090020b800041c1c8102d40928401400782c0c2085205402403820b1920b428a1031403034407002c0c08030301c042c000105100f0359208030314140304690b0080c0010715004400d03a5034500d540d604900e030b1540304903000800f00302000e11296000d001440307010300c030b441110301070b00450600030080c0c48861400c680d0701040c046800407040d88004144241d14086001c0b10203010f808203540d012901c1c50b10b1344a03820000340d101440a0203840c0000c0242c40c035000d604006d24504428920001e0300308 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 752203273 1250 752202023 752202089
    0xf070312081909060f0e0a030518040b04020309070515040b030f06300d080103020603040b04030c1a060f090720010e03030f06150a020304060f090801180606170601 72
    0x1460503c40640c003884072951151494114404041100b03100d80341c2c210791903502a02d8081c000c40d00c2401284c405401148800254480050000541201c9807000074100c0c0c1080d11500c4240d4050030051205040000740c01c19104240071000707003000c0c0b600090305402d00c00144603840540440d00440c1c099110550210351121a00314a18624103060310f9103400107203250071500c0a03214184d047c1c40c2c100c0c0100310701816a034000d840103196035900d0300c034404112000791080f010803000c0541c00022800c026414260398000c50090141d5042440800541088031150320384100981c5080c08080c50b00011281ca0400c1d948004907001c201c1d10400c18010002c0c0d030f0108042e030000008019480541c1141984036000071140410038000350001100c49000d02040706016a00400c418010540076050b48a010b640c2032030710045868840a080342900c4800c2458965081685070311000c000c45070007040d001e80600e41d407103101c46c0044c5000c103a80d00c4040c881e501200d000d200c000b14520080002c15850 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 752204523 1250 752203273 752203321
    0x618030d110d030b0a0905092a03010f0b0f0907050f04030b0117070b04092004140114031501140d05090f0f06060d031b0210050a020f07031208 63
    0x1103084109018016450100d0201120700801000150550091244c200d81d00005001d50302803c0c00c02c8828801400007800c0c201d198410900e505100c05e1007110741c01c4040c20b5986000c01044854002c0c5030070364035215000c82c000340c20702c00d0b004a281c540c10100d2a1a5070200c0f40392499840348601a036043c841c0d40403440c0192000100442402aa60b41d224100c80038040076048a0403004045d98403840103008042d00b503101044104010340c0f0701d820408460b0721403402c24500c03100c1991141c2e5a070b07200c3d0780180300c0c0600e64030f00c80b2600d603013004007248d1b0055410503044c40c43ca04151001e100d01941c8988505200508029070f191940520950b42c107011090f00404c00e909154440656840c450304000ea000c2c41ba1541020b4201c6000c40c500c2d028010203407510140d020650b0341500c0c100388022080d1540d801d962001805030b034429941074120f403e591100795a840701154000c1c2032030501801c14403103a10804007000015640a1025054a0140303484ac03171070740760031403059101c04805c581100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 752205773 1250 752204523 752204533
    0x618040204111602150c121c090c0302210c04020d1103070c020307060201090512091206040b06011101060f05041e110a080115081f1a0c070503030315061803 69
    0x1c0310510200001083c0d038001c0710382004003140c00c2000700b280d01c12210000c1180e00a031800c00b0707511402001820b01040d115075920f1103030303402202e00b00454006070400e45401044c1002001541000200d4020b40407581301c010164075803ca11059954045c45442c50013241d000800340000d036030a500c01042c41d40c00c3d144c010360305c1c1050140182034158484042e882802000000102c803401442544a6560301c0005400522070394420301c0c2c0a604030940542d040b44030598080c040010610145101701d204060341c9000381401c01c0014101207042a05d00202d81c94020284035000310003813080b00704c690842e00890348104c10020911045441041c1401050400840c9141556014040c2480e08240d43d00d0380050707a41c8900328080042e02411600218081e41c2c0414420341280c00f44402c1060130312900500340f40e46841c2d5058110880e44000310883e4042030385c082240040c0021002080100c00071030071820405070440c0d0401100d0101c5220303120024000002c4568040501d1a000c001015a6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 752207023 1250 752205773 752205787
    0xd020d03081b13050f03030a170402010c020909011b09030c031e020904050609160e070f02011d011a1008190f020301030305090a0510090512070807260105061804020411 74
    0x60f00c00c50318001d56101e504111040815400e000060f5160742050360b5950600811000e0f1307601d54400040e200b40c0c1000007858020b0003680b10800381c2d900940501d40002140c91454013050007160032405046c0c1001141c440400100b0301806c020b20030741c1d8000c5802042d5078480e141106425004450003500903c1e10010481408404215103104203030440c15221101d401d00701d81402c9a4180c010306030020003100108841c140325081e048142c2d10ba600000890040c0ba105000701840324082e8101345a4550039228540d417000c0c0c180c4030904006995241c00480c1c011805050b00c00018030000c411007e11901400050f0660401211085551411560703941c407030900a0455006010450164140450000310f50801c0040040340c12010350310303400490706141c20041100c0402d040103031a0701c034010002c40c22100030301001c8024403121240914840c294140e0181e00000c610305104581d140104200140d141c996400b080e08885c248011822f50310792001030000c1c8428081a100c0e40400300d010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 752208273 1250 752207023 752207047
    0x906140405031e01061e121103010f0b150c1e07050a030c03030305060909070506090103062309150d0809012303100b041d090a0b0c0d0b0d020d03081b 66
    0x40043c80320300c14000e002c159261032642d80003104c0505c175a0781c00020050b081001803071400d08241c002d8030074503182040a202000280c00d50380e101303160703026460382d414841207a4540304040d0032928060324000c50602034070758109603d40307120031320248400b540c14002c025800c40030f216501c0544801807039021160740300e0500c401c072218580002c0300801d10781008640c252502020030303480343c4000802050558205414071800390040092903040c1074481030080313200b05a01d004d01d10b01d03080800424400c80003c000300802142c024040f41400e00081200010301c4d16007500d08255180c000383c0c042e50740c10124004890242c02d0414004211007405088020301e480003004600030780f018004000000c0d00c8000705429482244511408030401c64004143e08141c1e561b419400a100c00039605024800d8607a000f401004450400a10000007020715800c2d14601c5a5480f1110942d032198000107164007042d5601c000d1070001d0b0511007400002500b05203881081031407941d1000a0940b68400340c0c620b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 752209523 1250 752208273 752208313
    0x12031403010803030f010b07020d1514040f03140c120a050c01020d050711032b0207021e091005011215090e0c090619140f1507110907090614040503 65
    0x5984901d520140c00041c2c640d407400f0076100b0340e540060541140802c90754448030302070742259602c0300c81500d4560440388042e080503330a01c52401244142d100c1c4000b468000d114010714264052a003505004890000c1343c0011009243c0c030485590301e03039805240105a400e8018148030030541c0d8000201c01002e490b40d40c10081c050b001070307164822202c610506140d117900942101400345501081c60001e40f176030302c00803088055503501c0b005242c48240c0c0c02180c445c51020780b410f00546552040203c0c1d80c03c0054030140e001200d040c401c80f03594203040000b4034140c0d212540000f0710f40c07120320703229400403108039440052140c21805c105410402ca941a01e5100e00d44ca07142c410040c0030005a203034241011240950000001003401d2103040c42c031000b02420002c01c0980c0c111155803268a1203840f40d54851149600ca500320548804c0361b4a0802034444000c1e24036030141031182d0a004040303810000d14000c0c3c07585401c2454400322004400c0800780a254080c40e0f0611038401e20312450030fa11301c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 752210773 1250 752209523 752209531
    0x70204020a031d0d0e010309020409060c180509100306092a060201050f060105160503040905010308030a051006020c060c01110f1201060c050a030503090309040617150609011203140301080303 84
    0x3066a1101d0007414046846001014100c80419501c5c00701d001207610a40c010b080d20351008100182d00e800300e403914800c40300c2c0304d80301a0110300c008408089140c95180368a0040800f05c5080801d441d00c1d94801c2c1d42801248001440c07191201d0b402c6040000b4001c4070b0040121b041c074080304180301da0ba0442410300f19481504099480c0c000403500c00409032080c0b038030580d07040e12000e1800d1141d904c20400c00e449000203131500e010038400403a20711041d01600313001354000c82c002501c0f410301d12030210440d18060000380000c010440e04009554002c40ca00c900b002c81114a40d4036042022a07060140c10701806c403e140310380000c8d607445440c001d4009400401241940c892040e0f889a00a540081407458081c0860b480b10601000003440b45000355803100d4410300396401c0400b0080441c05031354054010442815502e40400c0c000401001032411500c80d01c01c01d804035040240106096103810f0081400c01c0d0050480790703045c1030140d60440c7c4504c2401c1c515954a43c0e5400106849420a503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 752212023 1250 752210773 752210801
    0x111504060f03022a0708031309060501110a0b09070b042c1e0423010b3307030c1b1a030705121503030406020a062a030f02070204020a03 60
    0x9503000d40410311900c242c0f030310070140c2981c0e081c3c9440000b016030700b13055071010030360001d11400001140c0001e003440a0001c0c035407200c1000c40d146080c0344082c02903d080d80c201504000f21807110007418940080d59070358064005c1000002a15000145800d04003903421980100d40005400640c40343e6801480758094145500100d0101c800c01c2404174100c01510101d40c42c2101003044d84c1c00a06002903240c0180c858502d07403400300d1098640c8125404c807145612100d9545d06031109003414403840d10001d550354102054100000c100601c0340c6401c510009a240c404046a07460403d402040c49642c0342c0d4111440d0070400840c6048000300507110f00800f03c1e400001d0b22556014403403030701a00d00890158550a042c8044860084c4244400030014016818403001800050b2014130007000500102d5024100054103824500d017038485484000e0b491340d000740c0301505000078210507003030003801c030f4136000c1182021401d950340a40a0100065840b17031002900482c0c054040d407041480306110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 752213273 1250 752212023 752212037
    0x11030d020c040b1c0803061f0216080c0a030f020301060b041815140d031707121b0e01050c010906021204050c0301110306040b0a0306020d06180c0f0c11150406 70
    0x10080c0080b0503044d41401c10903040b0190044c00250740300015552110001e001103101404c420308081c6040c1c2c8413640600540c1000c2440610684d0650645020b40b10b03050050042c48401c0010030300c0603c003440702070300d002804a556000c5640a4004a000303185414000d87c0b81e40e166000c40e02d12541c03d10740081050b141620355110100c228002d034040346d041f201104100341900003800f01c44040c00d001102003041d480104038419002801c1203019810030b5642c4001c518851303284504598805880c404580000c0e4000f00c4026030144880b1003000081c41c20688480b001503030940500500304004000301d002041c0ca00000b00c0710203949110324041d80840310b13010450000d06080795000031100309045010130014651303040c1038001a41d1900054050010140c0c0d0381c036203408030380250030314549141d1074035410050b4104910032607500b00f510038410000b01100000103040500c03488003410500c1410100041803040041c60031503030150240c01d0000c90408205082c02c1c0b40d00078041c24010500c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 752214523 1250 752213273 752213291
    0x106060201052d070e0f10020f1006050904080705032803050606070b0a0203060f12031209060f07080a0f18051e0703061148030a0c11030d020c04 64
    0x74602c505954400000582c1d49504c401c0c008499000703c00e440300d5002042019101e1082d22600307986c8140016550142080b0000c545a981c10401c0c0c115503d1102410b0010510450b56208021a0070a5200040c40d580e4840c5280150560041480d050002c02c0c913a06030011442008441e44407a001c1a5010401503444c0c60400015005e00800906200d0080e000100700c2c5146900035a04100c0040c2680b698003242c0c400214170400c003454089050b0170214280c0c02040d500000720ba040184440a0b100030300e00780720160103601c0000e00220400003114081801c549040d4421282c2c00580c001c10300c18214185030001940c80085400c0725240b04008440024400600020100d15400030140800900d50740715440586042c5052100c5d605080280c0c14420540614800c0440e20100300454002c0101000a00e50700300c4c0d10b151480701461180710303801d0f000007108603a003244403800c0402100301103040c4900520700c018035064040c07086001a404107600012080c440400881d000d12803585 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 752215773 1250 752214523 752214571
    0xa1b0b011d091b03010209060d022502090403301418210d02041205010b030c0619020715032c060402060703140406030204170a02210708010606020105 66
    0x1108440d00c40242e045014400d50010303200015003c0008002c00150400d440790300082c00304d600031401140800d900042d130f101c00120000181c030050004204860511000c0e80101c0d56007800180020104040341a03114a580060010040c0386400024000c2681000b60314910003000c1d40d403421a07a00030003a0000e1805412810107400c40b00290b0080d180450640c562020420801c04004066400500c030120010300c20380701030b100030304190420010300d0f4018248107085515200006001ea041b4104041c0c841d11071004940c2c40b180328100060601c220030a040741061190f410040c41c0c14200e03554100303181c0c0d2540148400201ca40f01511040b8440a003090b0401c561150300c5805401441c00500586010b10280403098000c2c02c00d82c940440d1500d0740c684a508c10f8106c0c0e400f080d80828144044c0c2c01424826418841003001030125602a0300051482400700c0d03050289141ba98940c001025001e0140e07100809905000703010594640b100130b800707094100c940200394a505800400c0c048 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 752217023 1250 752215773 752215829
    0x315060e15120a2a0b0304080415030c1b05030903060c091e0a0608130503122403060103060f020d090c1502030a0801091802060a09090b04020c0606060a1b0b01 70
    0x1540030a03c0c54001c26140ea0300c130440401100b403103154038a413000c002042000300b0003c41c401ca03c0742c98110340c0d543c2008100404040c1c1c3d00700710300402d49402001c503551074012801d08001214002035118071140c2d450810f1442c03080e41d40540c0c15008040a115200112001030160400c0481e03040504244203007403a0141e10300310380302c2680b0100d0300c81e0170000c150054000030b402440301ca103419500045030300c8803403860b805003807000307005111602004075601c04400600d110368500581c00d51014040300010741e913000107001c058052a520401c10141d03161943c125136517010318005c18010f08940d81004258410741e0b200306041e04414040c00c920f103d10201c1214040c0d001516161066400c1c104a10002c0c2240e1200105003013180e004400941e0310107024103804141c6550360501d46050034018011741d090000d2080c007560041c02241c99841004c0365440c0c0c4120261030301e80c1c0302c0d0744840003103c00707207070646000d20030001401c50103003806110f510940c123941d4401c94030114000c1480700c120f011b03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 752218273 1250 752217023 752217043
    0x50109020901020c10180b04080601061d0f061606050603150f010303140f04091e0c0f140d110703080f10060e0a0f081b030c0603010315060e1512 64
    0x60300015400107880c178083d80e90306201c550720315040c41244180402d480c4509110340242d02c0303c0740041010012600c04104081c0544210310781800ca100c1e540030742c07400d42c1c0348207a0f5480c8684c0a1009210098540708190341d28420b0f080c105100da00c0e00e17070510b4402008141d0f600c1c0d002c0d00070b880c0700c0450008080420750242860024140342a841c5842c01c6a905001840e01219201e080080b08074440c00390b0040c0010713003480e0341c00080e600c1480910b042464001c00b00c4942e601c0c10003095203030550b04400c00d40101e180d54142401540314420b034000c0f080c800d03001070105141c61b00a00700c403600422006417040d548030b40c80320449601d03400b16542100b0300c121500344c80da1402100c00e0004512500d1002c2d4464800340100e1505a15200300c0031440206410a4005074000b8503040400d001e050014810396400351301a000170b100580124190f032105010107481041c031144800da2501260f1302c0b1500402c4e030220408001d0615007049800c2c0f480001105120340001c0f4250340c554200440da00f114 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 752219523 1250 752218273 752218277
    0x509041a18040501020f0d05010510020d051e04090608160e10152d12020f03010b030403090b07031706030c2b0b010e0a36060906020a03090204050109020901 69
    0x205110201e001e80e40d004010012a00b0755001d02200b02d125115201914550044a074046a95810715051140c4c000c845454001191f109501c40c8240c1c0b038008003191348002c00003000d20080d018020f0000c5007880b850307001031450386c03500034001071400c40411810741c5032042d0000d01c0442d60380ca6035142d580510559121b03080f14840c3c441008200c041c0c03d203044450149091502542208641c03030312015109109003482108000500aa1558130100a062802000c0ca045080810503080c110940c00140075940a10b00004081070a060041a20600500416a201c3d40e588034501c0c0040941c1c04660004030304094a40100c0c500346404140700004980c060122450b29002c07203420103c4090003034482d00d141d52180c91860215480001050103030032141541809424110000341c111400780107500c070307000091481600c410703d044401c01d81b014954140758800c26040c1c2040001003d900c00c00800c01172001130090039040d00344c0c100040c1c46000b10f604011980c0c0c2d48103044160b21a030655280 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 752220773 1250 752219523 752219539
    0x60c021b0603070318060504211d030a05100b0a060306080c0f04020f07140d08040201201f0506100302160b04140d0203270a06031a060a0509041a 64
    0x50281411005107500420070b240124031712a00c408081c0407420190b50955602c5d0700d5104000c18003440c2d403003440d0120308003100b4005001400c40300a00c0503056803080000080840d05846c03071036400308400c1ca00c43e82c1040590b00c4061021340300d00001d125103130a6030700840391800300103101c03800780c0b18202c1281c1c1040b02070110003580208112541004600c03007a80540d09104446501e480b1002400c00c151080c1034800c0b0703401039150104d10300640d0300d42450400a2401c03c100050340d229801c908105081aa000340e06088800c0d1a810190700c5601d65101c0340000980d40b0504456800c043e00608081d01d0f403241d003041004045040c6c0c81480c1010818840205a17400050120032640da809401490309030720880211400509000c0454450300040c1d00c0030a6026030303000c80100c100c0c031840d80d0040782032038802c117440410641d411505c03900091564410742c0c2c54000520815042140f40014545551268001000750680c2c00a0030403600481c0341c0380217621852040c0184813a82c03000148054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 752222023 1250 752220773 752220823
    0xc07081908090613060e1c0f0806060309150c0909040f12230c0c1c030908060708010612200417010e06040f020a0305101b05071104050a1805030403060c02 68
    0x5e002d089507003029013040c460f8a19850040300348441040741c00c60aa90f844d4000c0c515840010300f15030014268501c1520308206000558500140024840724030101041284d0354241010115000381c100d881d1700440508100410017000c18850300c4160310503a024400c00c0d45070102111860180356402840121400840c3c0440030000c1c09849640c013400c00b03e030b111465080c04240c0030b40f05148131f5011003901c1c200c24010150084180d901038482c0d240101110310301a480117080d943d0612540741408075462541142c402c0c1c1e5048000c0306201007040c1980c50010301c46040480d4400d2190004241c118610131604010602030711403084034400c0180866191a210b1580c450309012080340d21902084c00003000941c2444403881e00c04074010b000911520300301c850700100100e10360807010090104040c9001811000742c0d8803000c1c005035400200d84e038403aa54500100700c85800d03413006001c65880700017000300c000024415244981700500600051700026a56049485154048105601404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 752223273 1250 752222023 752222033
    0x20309070611030403060212010509091b010e011704050607140901020604150e1507030c0503060108180f010e03090f09010806180106050402030405160e130b0c07081908090613 77
    0x29030201020000f601d18090f40c90b514441240c2c0072146001804980000400c460b240c0364a80b150300c01840006000f42100e00c011403803a900526180c2d80c180400100840e80e1a480b802c1500306200f96807960040e21709290400c5503503a0070403542100001c04c1606c00b600d18684500985054000c181c00826090f04c1c2e43c3d40f407220500d910080342d4000d039a0b03044010b004540030082584403441c254101842c42c1084030000b4140d6220346100310038440200140700d10341c1d92115085a210007624601542e03603410f07a40035410241e400544030102d600380110903040e40804001050342c14011511900031803109001d0054188c000d1241d1801a0880800142591064004029208c441e040006401a1640e0005049030000d440030b6030944c0c40103010b5039106000c0421500a4080302010f040b991600121300c80c03030440e00c0303240200400c0c055000710b401c10150f02d003a2200c1940c012090323030b02c070705502c3c4000c003588258200090000700460041503000d8004282240140701c0904d45602c052019103a13 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 752224523 1250 752223273 752223287
    0x91d21041703160b04110d0c0e180318130e0a020909010f090c0e070305090606010507031403012c060d0201050a170702030c0705010e0607021917031308010203090706 73
    0x70300390391070000700304002c6800801e0011000551181c21028030504150412010b0319601c500e98900071050011040c021803540442c1c0411500c0d1859018215070b81c4140d146044000301d101006284004216503806004484519a01c40c00507a109145940c0d0a06e0b500300f61090018800600d421662218015003401d610b82d0b54032103a46000462603486040c281d20840b12900e0007641c0c4002c07018400d100c00030400050541224581c94144140d04015132650303162080900203905225000543c04100f600801d40300d0303490400f40c0300e225280d43c0e659041d0710080e29205000710450440c07586c0141020b008001d00c1d0702406014018a10212441c1d00550340783d4041050340d010f0210308103400d00c10311110302c840c1d44503481580c06103032100c0d4410b420b585400803680140303050100501da003d4036500e070701c8281d841250301111510286440300c242c0b02c1c044034a98004071342040601c0201440420b00000a28440a034000100501075452410508074001a00c5618694001013803c00c4824482d0706 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 752225773 1250 752224523 752224559
    0xe01061203030504030c0803041104140601021c230309120f0403021e060307030c0806030a020f1e0607061e050c09210102180a120309091104091d2104 66
    0x1c1c903a046c25101d4030341401da03400494040340c06a02e0200612110b04260095070100304000d00c1010090501800103900c4e0912171040310713282850303100c0030508035100d07103107002000500b0308084020107580584059680d0041702d080d240e6220740c0b5101c0483c0d40c00181101d4a164586c0c01250030141542c5c20020f40326224441d440b518201c051901c2e240e503030f40304010340c01810fa64038000f80c511034030307038000d0700f0030300010039052080d000000c6d490b001d81c80303c90f10010340340000c440c130030b540620100c1801000100c82c55602d4100101103544c2040008991000380810554900c2c505a55910300301e01c415520111120403c810040c02580414108445440c04d1204a00c1c514000700b81084e09807400c82e00b00001d4441000300c0c040ca0042c0da8142904648043c4c003088010710341400013a00c010302481051304c6010482c80d80c03044d41c1c81c5203041e00310079a8050025488280680c028880d00030900d4500d0250340200c1c3e0050300d1400080a80300c14400c0360301a00d10402c0307414140f800301c1d50400040490 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 752227023 1250 752225773 752225777
    0x601080403050d1e06091a22050405070306050103050a0611030c0f07020a1a0706200313060e0d05070b0f010302011b1a040b01060207080c130504080912030a030e0106120303050403 79
    0x2400c04c4c01d04450140070003034602d40600040100c48030603c04584503041030428000e140d0500380f10000c46c0c030048240311b10a1104000f20709520380345000751420400d07130300191426240100100400c039000c1001c0b840300d40a40d0040c880120744030000c5003240710645215400308010050011803a0341c4c0805085e003140010190183d0517aa8200160034401307030f0112280c02c1d0030004490040000074461304080343c0c2c121122203165001c6c0c61000c003003440041e0000d0340b2808003501120401c030142d0090400014000281c80d4568201c5c0300141907034200000c1101c025421000140c1d9203041141164100d1341c05a4070f01d07282d09107880301402038925208080d141004030806c102d800010011072140654880c440c1c9599640c0b61643c000d081032001c2e00400d105400040350040340c1d0f61075001ca185440c1700440f000036692200c5c0f030b00788250300c0f80801081c4c020001428904441101101411510042d030303c0c00d000e003080f810200c90807240d207230107940410100340c1221004207100e9800154811b1281c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 752228273 1250 752227023 752227061
    0x1503020a350c04150809280f050303270a0308070215090a0308061801090c050c15160e0102030d05070203040512031c06031a0405011e090b0601080403050d 68
    0xd010700726821078086030361414215001070304114510907052094503c192034608400c03d414207410701501e41d01c4090310a10303010210803940003290f0343c491600140c1a8084003a50001d00e481c50036948a400031103081c039144130401d42c2c000f4460401107100800200540250010b980d1940d4192002d000280241086109008030203400742a000c2c0480d0103512640c1c010a1182c0d040c5c0303001404140b00802141c0590000780e440825440c14108040c10b5035040071012982a0603407504907031074042c248441115200f102110034929040070000741c003c0c91808050205400f0b107070710503500e0f8203160201500582c0200b1800702040f6441d031115800090300d01c1070340d280c603a07039000042850b403035402d200e800354100207645500b4581081c00723010003617002041841178500e903440f07500d00f00a0141c08890708141100008003003017820360101807400b002101011202c8180c8000100824841000b20703240803100380412182d40c02058a030384620752503641d5034502207256010b40094004020504010254 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 752229523 1250 752228273 752228357
    0x60c03050f0618180a150e15070e031603030e0301050a020306060904051503070e0115020a030c020f0310150620190807020a270c08010909020a030f030206011503020a 73
    0x6000784001e550080010000e1001b0f05081c2c24111460917503c4070060f80318440f94244440b0009245074003440300d052200701d1f092200c0c0403030306040c09070481d00002ca0044a0110405400c02a1402c1d682c200754001c000c2c55881000f074800300d100c143e58103070b407101040c04002d856140a4120941c0a111074080c0d00c001400000401d15140070b80d044400c103290203100500c102d02e240440d40100d00400d100408504003681ca010309000c0c482c2802a0098481404a02e540d40b005c02c01042030480303961081002039002002455a1086401984e0000310f09100d28440350641403010007180c846800035001e004840301c45000b40c034100800407220040244605001750381d42d21148001032919681030341e41000b0350001d542445585080c2c51140e60714000040b4101540400c54905440c0c0803c0000340e0380c955400061207620072540028003c6140d10a0386080540c045080390407140c1c66404030b5200070785110f06a042c6c0c090040c8040c00190b17000080c040034261001402d4119124940c88100720103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 752230773 1250 752229523 752229571
    0x2030f1309112502060d020d0b09040510060b090609120f160501031d1b010c05070f1409011a0f0706150e0a06030c09090305090607060c03050f0618 65
    0x144040b0341d100d0b9010100d0160300ba202d9100248040803007180141400a03115400600310f4010080f003c140d4030b03404500c00c1210300d0558803020803080003d1800c001450640b90165a03000f280c01c0038030300e00c0d080290015240c08010140c9a001800620b8203080024500034811450300c030150943c458415500d0791820382409004845000d6064205540c1c0d190404001405481c550400901c680c1002608030300740c14404211501c032003440303c44c000c0c640d00340c10b070040b00e022080d0400540b5600030500d000070181d90200c0a00100c032600c1101c07100810040d81000b000030b80911405502d10605138000e003890010400a00328000012881ca003001c245440e5801284c80d4850200308003094650240b201c01c10340c0d40c0c0d4039400703022132406000d02c41c00c680e00c12017062042d1055000107925030620004150080c02500d000c1c1c0c6000e04125100e072210b0903d1000f506510045002092070000814240c2c07000c50b80c0940300e040c02825200c440c000241484441c00307002408140038840d1a000050f150f9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 752232023 1250 752230773 752230781
    0x40b150403031d060408060a0905071701060e0702070f09230c27030c011824080108070e0403050307090e0a020421050d0503180303280c02030f1309 65
    0x502a682d0505000c0b030f50b028254401c600c03400403074401c00d4180300c20408081e0000300b155010100000110303ca030301a14000e49088100e4000c0310001031030071040c0c50403e07030550240b001c840c200b00c04c084164030380c6101a40c88804900a880290484980910109403560020071a0f801d004040d08aa002c2041842e248004141c5403402070303000025402071224151094020441c1c0440700000b21008010006950361a040d80c01a050200c0121030545c01103e590191008190041035501280d601c1008652800d400c00b55200100d1394640012680004c005071420a42e00000d1241699440317a031020b07500e5400081c02c660030805000008a420a50090403030302501040300c0c0983c8490510312500ca190b2403640050a1020001c03291002041c00010101d54003003003420615540e44a601d44031494a40d04000900c8500c40007081c005810081c07e080145100d02d087c015000301c19044200003500d41c00c44281c3e005034414840c900b80304a0b128020f10080d110150080010346e80d9030110000d075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 752233273 1250 752232023 752232029
    0x103170d09080a0210050c090f0103090611090102060702070b0f03090109140f070b0712030506030a050d0e0f040504150e01020d05130c0b0a02060408161e0c091505040b1504 76
    0x80c00c00802d43c02d03180c0f9010041a401444410b8044c0464580344030100300b0340c09092071a91054400c8468503030164025844640c02c2c80d0000c805010100e5000c0c500d00c01075220700c40050040c03207800c1c0003410891011a410042e80d00c1e1841061030803041400c00c01d010341001c0c041c00b980c0d550f00c1c03003e4400507840410074104008000040c003440750340103200300d080c09015401401d802ca0100100c100154282c103195460442600340082d40717895a20200e072416410402c000c105101d001034110483e90000607106044000315a00c211040d12001400242d0301c082d14020002c08034001c090174054060f4002800400e990b4000500300ba100c19103003c150380066072601c0c12401403081400034030403501c8022001d807101440c000d151524034207000303643d41d000800203000c1e21008103181040d64010140c04100d01e800c02c0e82850311640526554126400201044811211410002806406074081e625800717600b2007020781014075190621001d44806803059600562142c24062884c60010107040a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 752234523 1250 752233273 752233283
    0x10050907080106090803091807030605090c0c0c040b01081b160b18010204031e1509121d0f060d09380402100509130c03020a02061602060103170d09 65
    0x8551400c0c2c0090134015464000702c0454104218581080e150700440390726402c803420958040d42d5848100302d00030074440c0c00c815071040440c0c05100307a5032140e202600040f220a01070310b242c40b007840204021a00f224104a002c52250310008070050410855078135542480b1485034a880803001d14180044001c1500311000344080060100710440008440b03400c5c0c0c035003802149024107544900c1c00f40758020070800c50b0009030f14210f10030803a40c00c034000c08407401840c052000c10003520301f07189815041402200025840035024200440c04c01c0a440c0307400001d0720000c0741489120502000e0340c800302004062a8035070f64200d0014400e00c8500c800002c0c100215808803c40d14442c68803030341007842c1c02501c40c100d20140302c050398950103c60000425410626603078054007002c984075044100044800501c0d248a40900c00d8150b00204001c0c0895400d44034130f40d889c9855204040506821000141c0c4182c1c01030001448007640030300c0f0340c1300500d820350905282c03210790f03002c0c1c1304000c5c01203032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 752235773 1250 752234523 752234537
    0x925140c0d02212205180613060e0a0923010e160602030a0c02041506050315041e0b010203040f030309061d0f1005040b04120507050d110910050907 65
    0x94001d0b03042c002c524104482d45450020103844210041103805007450704d01214099408a031200b082c0c0f000507500a00d4054002e0284100d00c2c0219090144e041f04c81da8050585034150107000f0311544515015500c0c0003600c00c14584071020410028907070004122590011f00e0142c0315a00802d980c1035085808a0001081c400c03a01101d260424800000c0e0300c8507035524000c01e000b0541c004c41035a000841515008002e101940002006060b0048000c2c0c0360500c4404080b03201548880190321528a01d000d484500c5071035000c0c00304651045610290081c000002030300040556000901c3c0402c1c148112410161258019101d003040750f4000c402044401c0010440c0a421079005203440c0c030300303502c10203900b0007000c00b046021207403942c098407070f00c000c1036184000307402142940d01501c00b04c4c0240307845984035038034600d00b461500400d8034a03120f80b010004075450103e055118650784205200c0c001252402030001c0d2410241501da1207120042000c02c50f62600c50742c2c02d2007440b21b81d440ea1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 752237023 1250 752235773 752235793
    0x70804120302120f0a0f12090605160c15090204061a09040f051317041508101502030403110a0b030720010c0c031103090301020309070608060925140c 66
    0x40d10b802d0070441d5a84443c41c0900048140c1c5006000b6a03005800c0350030440d14050a4010072078626115a00c4a040c446c0740030280001d1107210b50210b48520300408100e801d0031000356061307400011140004000f40c0f911010383c001c554258201851962019001180682e119560410300090075200000141008121003a031450607001c1c03c000270307101c400204010300702044541d0030602802070181c06103416099801d940068201200c1c0101003040020b0205041414028000c0400340c0c0c505881100c64500170a10803410118180a51125002140380074a50360362261034080ea420001e501003240000020054100702c0103512a00281d95040380080000b0710a80c141d0f24000c0b83c140480c4e1620024401064020020b100125010706110070702600d4244036503c0d6100d81c2d607480d60954004818084558000240b4070183d86150b20b4085d241c1c0e0b590000d1018a6200f12012841c100c0d000e803d00414046c1d040c0810f0f00a00c40d41351101c0c42c0c0d8003070554400c00b0350025400e100d4070360040a44c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 752238273 1250 752237023 752237027
    0x5120d2f06040c0f030803060103020a0c0b0115020f01020a1b050a02030a032d080105191d04021002010509060a021b0a0b010f0504050f0414070f031a011205120f0708041203 76
    0x1070300a000103c08004c5000c1c00d5450700000360200400361f6042c903900040c1c2c0c005060042070103d038610341c4408188865030711641d000140c071200001c0400944075103d01050040018001e0701c8804545039901d00d5458607428210002c0b000b020300a541a004002032000540c0b010700070b040c40307076009403038030104041d002940903042803000c1800c0c0211030300b03107949210060340a90540e04651007102e1a0010041c06440c01c070b407900007030340000301c1e2503c114640508000010280b5216900840e0001400c0c0a6408203909131102241d4030342542d082000004c2000c40036174007501800512580e000c01114101024500d441385465040d904e0180c031900411074404108140c00240c40c0c203072020301c83c604109246950301c4c0c0019100a010480711401c440c0a62010022000140003200014090650303904048024044800c9034094022407a030004c03c00130300b140c9d0302d4803100340d0240060540c1c840c0403403444060780140d1207a5400d94402c1240304080f0707206101410180407040c0045041c00014640 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 752239523 1250 752238273 752238293
    0x2a0b1e16061e060603020315010c05120d1d0c03012f28020a121107050405090c0904060b0f0117040213061509080606011803060f0207061b0905120d2f0604 68
    0x101810008580c19040004d200031650807039507d4820b03c0c10360dc90b0302010246014195a004420012200005400d41d0a100054103414800103a00800c20301810311080c089581030981040e00320445c1c081502c49002c00721000306258a400381d04038104101c41c0c18803003103100c602e410f80c0005074440c40d010400d00000c0e1111802c071800c10b0902c1d400c2200c8140174280c07074507014402d45201d80d940d4000500c2c008414003207205120402420f454003481e05181000060100c07501c1c2a000e0341100403080900c1d400b40b0041e1441c00c0c41035003010810b9482e03a00b0018101c1c0e65141a822880d1202d2000a03020701c001095000d2188640381e050900d0b0508420308d00d803943c010211410021024842110000d41200c41c0302503940000d00484d03070580c10405003000c2d1151440017803090303160820f04910302c4400c46030404180419030305c42000301c2d0303280200100002c0c000c50702801078015040307110189000300e8440003115030a02c4000e001a1000500ca8401c00b03829900002035040b00080204004d8035000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 752240773 1250 752239523 752239561
    0x1110307120f0e03070c051c0f26213909040501080a03030f05040b1f08010e1e0102030c0f0c01020c06010609050f0907021e0a1406040c090203070c2a0b1e16061e0606030203 76
    0x107103c0708339002141a0050f0b440190b04035254070a03020350b0700e040040d208211600d40002500078011541d5031240c8a43d2203903100c02c1640081e00d0700b031094030050342d10301030b0a010300c2d049040d8001e9916050640d10084010750402041070341c10582c0010b00e03010030300840c440310401c40e0107014040711008600c11110040c0c064030780140d02c100200b08592403440f041d034004a6035000e02a8031410107a844a00910600821080b00d1090000000b600c9078400c02038400d941054803c1c61101e4038640510910b16020748804003d43c0054100c10221905801000c1a00d2000c0d400c5440450540c0c50340c40007280901e45003400340d0412010001842820018040100f89009045145182036034004220f010480310041071407800e907003420040d0300409010403a540f44240384022259540e01d1b428081d42c40300e4001549031401141c5455004c100c58142d42d01c46503007814000c16440b03150740c0c0000800c13000b0030044a051528070407140000103441004083c002c141c0f801a52420322562201008203103007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 752242023 1250 752240773 752240791
    0x60c06090c010f18120807150f0b09040b0c09042d1401080d0537120c0909020708040806150301110307120f0e03070c051c0f2621 57
    0xc200c25010b20f8880044044440742072001e802c94517249070620702449072600103041140c03110b48200c260104c0341d1002c2d2200e034800804008003041001803012091045070060151117620b030006000040b0400207041581c03005200180020002d100304000640d1080400c02120b0b40c0718141d0400b492038406c00c10300a130240d0701d020b00c079132400c3e51003680d4001140d154000c0090100e15142811400c1146003011b00700c40b002d43e140200c400c02600301c0742c5427210441e00040d840394a50b00704092a84243c1040114550b5682c0e841ca00b40003550019500000d01265540000c1200040070602400058041c01c0025502000803040b401011b080d9410100c0b0803105080420a2001164000c14620746810000038082034104081010000611400d800d00c0160302001075074804018010742003030103883d0203c6982208024a4019803001030200130001d0045113202120004100007034456140314000007240140c105101396000038a40004184191a1200c4104015500641200301d0740c00b611034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 752243273 1250 752242023 752242037
    0x5010902041208071b03081e04060e061b030a0c14120d0914070807081504030e0913020414010305010b030c01120b180411031002160b06060c06090c010f 67
    0x30100302c4403a10100400101610000240381c410040c209400d8844940f112100442981d60382c00c0c58a00c991024400241d01100c80b12a04401d824940541307040d610640c3d40c0031190780d41c003028030001c0e5018045000d0030326000c044468001c0070800091217000169680c14481003010700d0308040000102c100d10307410360042c44c11000e94418190990b05800c0444201017000300c104d00700940c01c261424140ba0b11070080c140f02250b50000020450212400308044aa07180540103001d840241d082c2c0b0001d000403203000000205262442c11641c21000c00d40c1c80148005e0f15500090464826100c515a4600130030010024803000b8418001482001d6000d402c0c5d034000d01c8002401810f40e80c4804c0303145580c0310f51030000c03034894010101407154502c0080c54503060500b4050300c51180c98058a104e8420001003040036030313090082e03a00c6100401c14140860341c103652680352400005000e15003003c01803000724441b50003007002c07030302030000343d4041c04401200400052050b000000c812084c40b1030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 752244523 1250 752243273 752243279
    0x70801020403080d09020f03011a010e090c07170c0d0c0c05300c060c010b101716030b030d0e01020d110601140312030109062108160305091302030105040501090204 72
    0x4004229030000544044c0040e0707a085601c002030301d03100da0704007058056107000781c0c01503407089101412005117400d81b604809050f900040090003041140e00b420b5450701401041c1c00150300c04c0c94401202400c0c030541d1700b0034054025061801c07200542c007400244004224106001d030b030310317400d00162000b40c941d04900132401201c100c1d0300050503004031032200c0c0c002c4603a00c122414011811194030051181d40d540070b007089410301030250043c211b40b2800388041440c00e154003460480040851078a40c00c5501e585004070000c0e1300c1101d403482c109241e02c41e02000703240e503428092400390b03400c0d644400780740c0c800c400c000a02e40400003a581c8103100c0d40e000070380c03180c02000134503a0440b80705111009403d1030000200c0c0c20882d0b8420740e071203121004800442d6407012908030b00152400c0c0d0b054414a11402c00703000d40351004540b4042e18040d01005486800362300c000060403501d00904200d45040e0500002c141c08100e980c68200150744c3c084014040303491f107801014010601c0750015410582 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 752245773 1250 752244523 752244533
    0x1e1a010f060e0f0112020a031508010902010c03030209031603060203041110050d0902030106050a030812090c09040b130212030912070b0f07031205011211031c1116060c05070801020403 81
    0x4a11402071041082c10328070000ea85c4901c0303983c2d140d4a038440c000d40d103881c66040042c0281000740360012080a62210119034100141f0440a14a8050751900c81c2800281c034240c00035400201c46a4050044a505001180041c0f6403180210720641e40113a0760714013030800032505a00441554070640c40440740805595220065401245e500c2d10001030b46240d034400a40100030315480310f50400c0c4424400002e102055015004181078000f061180d035840742c0a07030341c0741d8000c5901c0e260300040306408100499205202d840d8000d6505041030402121500050380188444003000384590002880d41e50ba030411081044840d071281c0001d214603130034880c259109010719400000d0002005c549402814407031842e020041d000c4500800855854030a00300821445480c207903011400c03250320400c6414000b540c0c140281032210303c00100b903c001e01c1211408149260840c0c3c61007500b045ca01c40e5482c800c0700c0c000502c6a07031100809042d1601e880c0d800e026440d4403110f03080c0d10500c01003010803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 752247023 1250 752245773 752245787
    0x11401270c021e030c010501150215010522020c10060906050603060d062a030902011d150d0902041a010807090b09091008060f0f0a060308070f1e1a010f06 68
    0x110550004069400e83c19101d0341345001d4000750451a40c02c0030000140890361400c140e000051705c2c1d003600e404c282c0d24092080064407e03c94035402844801148a014065183c5001e013801d4911015140200259110b0710b85904100700f002c6083d5206c401b00310004c2d4501c44c14000b007000303035842802c0d458001c000518102491070003800160312145601c00c1842441046111b050408403155004000b40f01c0c000e0040500d030340128003294088200241132080001c01c940c0580d001052542402442401d100082d04480040c448140e2550003090046c3c2c0d41d800340b40329205440c0c0106410040c040001020018007a160f003091100c590000d00800489070202d46024002703464100c40342d242c2000e10076240715183d1119440380a480309102e521030441c17030158003a0b00e42607451035080c2c51302d00700c0100300d07005440b005200040401101c0009580e05d60032443c0140154501c03013151450080118205171501030855040300303001610130165200fa00110b008d0200d006410303040ca401d24102410034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 752248273 1250 752247023 752247043
    0x6080f0c011202161407030b1003080a0c170c100501050f03060412020c0a0902030a0f061401180308031303030e07050f01052206181a040b0c011401270c02 68
    0xe030002480003210440c03c10b400480d60303100640c05c0055081c038540ca5154102800121140b420700804207403031240020031501903a4101aa8030b14140310040242c4040c130301c424046a07003610713540d04100e071030000c44050b120034028000a80b0111281c2c07500c5c2c00032038070141c210074400c41c181801c000c00c94030b001401c142d0003540246030122600c4150309c26890030412047c06a0b0100280303001044510705600558010a9060018088018075501020079960703035000720800020204021a0fa0f980308140994806480e8004004010303200d403a00b094030f90085541000300d0070855444820954503100c0c401c403424100300504496400c000008010b040320106181c100700c40841d03280c601c2190011605d1001054041098040b691808050698040440b041c2500ca03a00040012021210014072040c040707140344440c41c090901d600603149170404506a8000d650b2075103040000054009214003803e88180081c0c001725a5000048641d964080340030342040c1403400400405130001598988 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 752249523 1250 752248273 752248307
    0x1509151706010e281803020f07030206031b041206060602061b1c0b10110706090308030106030510081005061507020f0f0112230c03010e010b0f040905070306080f0c01 73
    0x904c0ea240b1020040301101002514101ca140001c3e04044012411010300d40c58420b13002e4900d140b139065030703840d2608060f00c4060f40001003040080c20906912070381c0c0c4481003e170703c540b0307040035100c015244a101fa13118040f50034640d2004113200b41034041200301c1c2d00c042410310842c4400b1424002400c00d00444040c1280e0f0070b548412303880c48800c1c9800c1100c5004010340780b003400c0801e80300000d010041401c200b12440c0682100480c100b8807070324998050380d42042d1410b01c2c1d40d1910742c00702c000f00001040304c1c0d080d5a01c40070114090740c00744011000250080300220316400d01104100c0300000603281004d130f4820420403140140c54502070501041c00c125010080c01a02c41c005072000c00c3c8414030400d80714a0070560030740c400c030f09802c0c480400b1071107038544920f941c8515294616100c280940151a0b100200400110150740d006103510015608080d02309071b42c4200610548205403508400700c8d460f000c05202c481010080081c4a4140200910b0f503150a0400a4011f03d200360381891 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 752250773 1250 752249523 752249551
    0x20a2108060303131a1605011b110a170c060a0209100302041203120b030d02150c0403020109120501090b010b0c0f160302060d1d061f0f05041509151706010e 69
    0x2618161301082c0d9440300c5518250803407201080c1f030801c0c0248125107200c0d02039000c1410030360b9038510582c031400c45040010007e0881d0201c0e5103a1b4108100040e0100b010427808200b114200c0d441030040c2409206030240c0035894079016410002c0e03c03a4249020801c161060100700b100c0c0f840c2c04508071280b41c040c10031103010780c040c050702409400e03603000d4a41c140c49540c01c46050703154000b92030b400311601e82d4000845134480015a42440c8103c0c44041e0000301080380501050340182480881a0320400002648460965601016100980c440021715501140f6001c001c41d0601003600c100301c0246c06002070903000d44610103103500b10b0002074040c0c08041418800d403a0541d000c0c115001920030a045003414509056550341d6040314045050340031400b0340e41802404020540c1030321941d031a01c1405c00d003003000303000080c90881412040f85080b14000182c12140d40324091401c45400c0c0c1d070122103400c01600d0750344005114844c036101e038403101c010403ca15010f06415041240044202 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 752252023 1250 752250773 752250809
    0x60603040b0a09080f0703120b3d090510020f120706091a010611120703120906141e13030e01090b030f04060b1f050901020a210806030313 61
    0x1401400c01c4100100074040000300641c9442255000e080703c1031180d603070302300d0401c008500e1000340c85885400701c1d08200220a28401c01d0702d030848501f80d42c84800d0091305901e0004050880c10802c016503000880c00c0c40b901445142007000d50403c1e060100d00081003d0403034508055a6101643c00c8000c2e28000420b0010030011582c2203550601d401006000e81020b02404421000c0c1080c0b080d64041000d84000901c3c2c00c1c4040b44070203007140c2c1045000c0c14415a514182c03406604003180c002c01e0795844004a000545c0d0744240d006449003500d42a4686c98611405050906861140d40044521004001d070301d1044181d1079481580c10300c3c0000f1a1424140180c070b0810050b04141064940842004141c13a03882c0416889580160f2081c000000711805122140c82e100202c582e0500c201034440b01e0440c020002070204e00b40610450b00951482c0e2513400e0480382d95202e9100302c038091050801c500d94071101154129504501643c604050040117807000074003841008101d40c8155048c3c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 752253273 1250 752252023 752252041
    0x140d09230703061e060f080d110705010c0602040918020310090c050f0d152703020d0e1908010e06060a05012106122603010f050904050708030a0c0b01060206060603040b 74
    0x140312861000300511030f10340c0f00c0008a0001d001401522264410400008c1072a4070071708030158108002400340c184503085c1001120074651600c0c0c1a5940c1d0340030440010700040794442c40304e100307100b00481d02566455104043c1000740b001c100b0b081c03550504c1c48030004941c24040e0b0904444088a5200803521848042000c035509103034041c0c50568200031542504125800c1808000140e035180645018800c0140c803900706908009801603000440104800d8040c0007040b080030f900070701d0706040040039028040501c0c42500a03400301d0351181c55034001c40c001005080d03080003044842c0b124850038903000074111809150014801000000200040d207078550001d801b608403c186072138604818204080c0c03502e81d9586101d40d21140141d5251380e162158243c034103803001c407803000c842a890401007001184000e4020342d4540120400062000300c00c20082602c044103841d116148486400c1190403d101603004070300791f400010070042c860780d4030001c13282e21542c08101e883d01c0e0b480e102e0403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 752254523 1250 752253273 752253311
    0x6030c06070f080a180f06080a050a0b061602040b0405041e030c051204030b090c031c05090a030b16021c030207060b090a020d0b030705060d020a140d0923070306 71
    0x5403030003d00084007144c0c19841903050307080b1500d40c614082c0041e0350310303a0155405800d105070f10010f440180840d154404580002d904074030b0b868030106030000001e00058480c2c1c02a0342d4400040c2c01c2e010b2040860902d8050402042021681006589030035100c3c04550540c0c049801e10122907c42d50b0f40800d40550740490f401a0000122a85503100070444080c9600c1800103680654103a800107070b49120000d4030f001d2204001d4058840d502011100c80402c8001c4048203090000502070300e0500e484403450f5000450190070800c2c00e500340260007200319036041000c181103400c5021218044503103c8104030080703409140c0140c0d0381a00b803c0c400010040801c50640c014401001c0c4803000510f9000b0307242c00b05c55000d080041e4117a81c01059a15681d0380b0400740c2151060140204108443d40a09810456800c1c00c1d90751450107a451410395201d8039507103003000c0c3d07214101c405002482c01d421884100c0200000040300c5101c0701c0d180c0c0c1c1e08032484010491512094080f189030401e0380 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 752255773 1250 752254523 752254553
    0xf0d03110304030b060405180727020d06060e0915060f0702100c12020a0b04020d0507210b0604060324060801020a1101050702060402010801140324160806030c0607 72
    0x9882d02c69860349002440d03140b090314804c0c8240d0074100400e01d2120900c8015000300c840308000c007801d524060202ea66060b2901400c10a0042e6950706078140900740020301c8081e00c800030004016082a1014007510411620f10303002c3e60465041108060901401c410307856003c035040781d11540072100315015071003460402908810a59040050580c000741100340c46441414002d0390b00f00180001c0744e507003e20120140000c821640410054107052006205039070041d07042e0749155441c0c80c4a0313408034203550101c149403040c040c1b62a00303000b914201507400c0b08048030180f04803440d6855a4049000c5441203000e82036885d0540794086106900040c01401560004d44d11460a8180a04102c0d0005802d4509500388400030742054070201e402c6104a034141c403590016402e0100442d080d4503da60300e2901885088008078400c0480c100c0c8410420300c80c3c2ca20701d1145010100070603001202803508050024010600005907070206500140c00f1003903a1058680c0380c00e041000c8031044981c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 752257023 1250 752255773 752255807
    0x30909020f0d11092b081b070305070812270d02040501090b030601090b063a02040618081e010f020714060c0f040306051e0907050a0609050f0d03 64
    0x1d01120790500410f4058000481e003107483c03809005034003a551050708000d1070b0401400200c0080d100020399203a001e8200300c0c84403005120b004007144000d900d000c80701c2c3c02c05c0c0d40640c0440030811000030104002449a91095241810142440202403c0758417018030481001e1544081040980314401c10104260700148140301700c1d65510741c0b40004008101060b4001e004400022844400d18000e580b8401d00142101c0d1609109508100c2c034003104d52018040350005050b030300c6580c0e44542411b000c02d000c0000050740c032850443d0241039103a8080c0c420b0380c0550905810082000d0105007041050704200e03041c040c4c0060f140805004001c0760384400782d91840466940244441c000c0341c00c013012034140440300561914401c0301014080c1c107058242040c020402031002a47e150080768005080c580321000d01050792041d2002d400b01120501030b1684841820000f0b49000c505582c010f002500740586132506103c046030149040c0d10790680100e45505c04002010301c00d0828482c3c0100d48 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 752258273 1250 752257023 752257031
    0xf0c011b02031c0e03070b040b071704090501080c0918060103060c020c1f02070602031204060f0f0212040507050d0503181c03022104080604060b04020c0304030b1012030909020f0d 79
    0x2840e030140c4011302c5568524000c0c4100040401c088110000301e800755075150100e50705049042e41e803281c481c44a209030008401081c000010340e0509401014040c0c5190f82c003800e103003210541030150059004160041d0342c5600c0c2401a02e104000c560035041d42d0b004040401d0018082c1d400760302d48046211115042200419000d10703032184e0711000022440d2aa09854a0554450b0104d03620300030003601504800fa03500205002840c40e40c00009401d41c645004980130042c03070701980803600000546511020a10704010811406001d000083c0c8003c4900c003180c078010751202ca54034000d04c41c01c001103032180480e00200e0b541c0c2030071030340d07e456181024441910080c64000d40343ca500b00340762055400b035006612140301920f004d88040d034090b8401400035680780e49640002d1324a500c0c2031a00150b003000301015804003880180042c50081504004504085100e05088846036100c0c00940d0f40f0b0010000000b40c0c403800100445402501c05600d654480d909400184a1803200300845890 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 752259523 1250 752258273 752258323
    0x5060f0d20120f060a0636060306090605060307060206240d0203070b0717040b1219052802032a0c03030f01090b030a0503091306170f0f0c011b0203 65
    0x100180d205d1003590b09050500120ba034680c2c40088040d0020202200c1c0900015020440406054082d8003841c0094010a0499480d160a01140c80c61101039411070b13150f508100443c03d041042400a02da184002c1c082803030062200c11800076865a9403908050780c08000d442651249113800c81aa002030540303007111b5450540c00103a52102d5000c8bd045d03928410322104a1703024900307580c112505020ba140c1303820314081c6c10640342100245070303041c003000c0c52a00d55000889482809d00c01d00d082501031032001d803503104465401442014100c2d4080c010010010326030001822507000300c3d110311400440315108800c550060041860f82c07449844044200728000f5042c16070203049540d04030040007240c0e00c0000b031644400c1103002c0500580e0080004e05036508040c403071248498000708001070200d48036180c1c1400f240c0c2011a05005610801007411000d00c00d1114040700329400340240248212140007034032028844420202c1c220102001c0010b40d02c0511080c00c401d00c605098440c0940c1d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 752260773 1250 752259523 752259553
    0x2115020c0a051009021e0619031508100b0306100302150c01050403020a2001020a030e0409150204060e0a0f05010f050c03030a1e1e110c060103030305060f0d2012 71
    0x500b13401c040c0d11424101c00e5442000d0440e0100341001c44010b8200c0c0e1070a05681035225000d2046160641015907403441101588004000d41014000040140c44030a002c03030750070016030703003c0c1400070304c29041319091258000c25013600008030796040d035403032340846081d41810180e4000d04020320540d500303060402c01059400308503c4a4107114141d80700e42c2c0b481440c8040c07160440014541d01590018140c0c1000c28098819001c2035003005001207020706030341d6540c3d11416407000e140c50f072154010905001c2c41e0b030800141b6104544c199520405240f03040f8400c51070780c20754882c50341800800a070380d04083d44280203d40f070450300034003180d07a83e0808031f846400400404080e850300000c00c200f082ca444809000e014440031004600e4000310ba03101f40c001c00100340d250b82c00301111201700550b10b8040002d1100a00842c0a80c0380040c95103040c1040c0501c0d0003000c1c81c42e81c401c070003408201d0001a4580921054403101510300c45a00d031000000c170b00f1403c1700b80c48002840c40b800228a100305 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 752262023 1250 752260773 752260781
    0xc0303070503012306030604200705010e060a0b0d17250308010b09060a031a2205010918061a0a091d0109020307120303020f040b042115020c0a0510 65
    0x2640e0310f0800c01c130740890603491403000100d410800c1c1d8004020400b0541f186465002164016917850501c207403417000c1c1c2075030b1703269512560044800da5150000a94103200920038594400340450341400722401c0f003c00582d0000c003443c4010b040501540c0d8440e00b01d07031140b00341c0301d480d2000f1130000c05001361400a54420746090004400240d5604004035540300e044040d192550005440075007803580c4200294051b0103105c220182c2c000c011080c401c00c51b41c5207104030710030824000420b0401d1100c0c61002c801d43d10160040d801c210b0410702c04038103c1000b8410340a00c030f034100e840014a0650856100c1c2f045050b207484030352005d5603080200700e0440e1a8442032120340070b04581c0900c480c808424900f80c84001c0d00103945604140c04c1040080801c00010f10158402e1400500c0e04070410b04000d107541043d009507200e02c81c0814140800c0c0001c88022408a224034503c0c035800042d41d50352400021040c440c1041a80c0100e280300ea00036041000030700c9158000240c4140c0c000050351a0002c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 752263273 1250 752262023 752262029
    0x61107080d2009130e100e0613030507110d050a14010b09240d153c150b2d040605190e0d1101030501060315051003020c030307050301 59
    0x554508024842d007012203078102041003405201c400d0800450a080001c54255104120708103911902c1c000a0b01d401807003449941c4c11138040010f03079815002d95491034050000c22809034660b5200759000460340180599246c0c5900ca03040907201080b0a01081c20880100c00082503803007114007039010002c8081111010300c103d540200000f030030f500104107101d401030b16545046410400c00020301844a2036441106202802c4590804484e69880d00d20085011000621642d115004e0b0b01e14214604141080d031509000c0000c404031040011407041c80440304e146031960368000725035011ba501d00400c001068914400ba44441482072030001041c15102d0030740507958403002c102a03111034003007980d0035104196645802c0c000f0146501c00004646d8501c08184082d5041c2a4507075640d6501c0d01380c00350721440300c0c2c100a540100014013070b55010780001c820700d400d04411039034510116400604546044507d01d0358404484000da0003445881c64802440c00b000040000c82a0000011030407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 752264523 1250 752263273 752263297
    0x21f0203040c32030307030e090606130e060a051e0108060307050301060803090301110f030115120f0912030507020a020d0606150206010303090501030920040609020c0f07120b04020d06110708 84
    0x600c0d140c3c0805840348110000100850201070188455091902c8840d500c40d002078040361800c2c00c00010442d041789e10780d0003503100d143d65504101c094104000844000c180076640074800c0480b4010b910110a108030250b41007085600000d92240e4040103034000070f00c0060000c00c038041c3c031410074544aa0140207c030740603600b0600007a2281821004031403400401c4c0101c14210303400e140d0003012458141941c03a007000002021406074403924441c8014110a949e00040d01c0862403034007080030785521102105040c9480d04201174550040303940c00d0500d030304803001d0203d400240341203001000c96822111051400000c016031060f0002010f6060b01c3c020384a41d1403181d943c00c011001d80b891188000d007860303a58880c00c00715080144003150b8111008202280c101d0315060700f202287c00c0b15901007469400034181141d500000c1c06080d029200c04480c0d000000c3c460348440700710100151009000700c02101d8030b40c1c03c1c8081940180d5691803103038016a5180d01504091840b03400034003420f85 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 752265773 1250 752264523 752264609
    0x3021203120c0307020d0f03060503070609080c040e1c1e0201050402190f050609010522090f0506030d0507030c050601081e1f02160f080705070501021f0203040c 71
    0x76420aa56055130700c9402203900a0030003ca120b00c00720390502d12060010207240d107494010949a4080c130004002c0c0c5456900c180005203030000151804003182083c1d801146426004070422101088200d42c1e050030080c882402803400808446186c0c0840d220a041c82001d0900618241d064111a0086000b121445928118900c00c8103041c8524440c4030079084400340700b0002400d090015114031541410440c3c200304042600c0303400c00548001c0d028201624640c2881400310303030b100703241c0035030b030000020026803a01e000030a90f120940481c010504c64007017548420103103e0106440c002e548a0299030455949211150340ea2914109486441e0403a011680070f00000003445001e40400041824010030040d031050000e501c0000e60700180c071003030f0040304c0100d41441c0c02a503403144a5801c0e140d54509906044d4240403842d00043c3c11504299040c1d000019401071102662842980c01641d9484514141c5a0256039600c01007034140091081c001030000b2060003248440340b018a40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 752267023 1250 752265773 752265781
    0x70c0f050313080d091a0c01090c051c030c0209040c15020d0f080f070c03030f06180c09051e0a091406010f08100b0c0f16031101050a17060a0302120312 67
    0x241e161005000004e0004038800000c1001c0f06040400c3e02462414000032407801c3d01c0303c00f096082d40d1255105a4004c05108020042400c2201c41c4030000030003034920090412681d90f00824401000b03001900c80c14880f004541032005c001250702c000c041e45140405500e140e0380029403222174400f8640003007202c005031003840e00d01800b0113904c20718102044807025517075420141c034100c14800b4150101360307a0362012000405540308030b1019114212031a44107080819a440556070003c03000020800350000070061a100c2500320608a074610741150008080c59000c0f030483e00280d07000f45100d5040211705040850036402c002c0c0507040c00c0c1c0c0c44011b604c000507000c2d55808c105691030051241021801c0010b06900c0024280070002e41c82034a01da103500150545c0307824140f00b034101484034450030410030010322820203410603000307082640c1000f034060006001242c1040c074034103210303560310300098107580c410621201450f40201070f0901c00c1802410290f881d04421a140b0031801001e001c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 752268273 1250 752267023 752267039
    0x9011b08010810022104051f0b150415120f060e010509060f060301150e0a0312111b010507240204090c030b13090c03141c2303070c0f050313 62
    0x45200c0340e4100300802c1700546000c02983c031450000c000391518020343c241060110403402800204101c02400410511165410000c031545488403002e23a80d00100420014114149000051258a800d01e100c0480f0390350041c0c0080c00444e001100c1035403800030080740e1a054220031034140e4a090300d00c508035648803810b001c1500f607241905580030105200400c54601850401d1703030850550714002d40950121004a5048010780d0000c5540000d030b1085100d11135402008500d0385803422000f00040e01d601400d280b80c41c0740c1d0f00074050400000040304000d015000a0740c6002c0ba03c1c0070150b20002aa80003840001e42040c05814505c500f010107445804d4464041c4030201c0c0c4004210200d0450100452402001c07403102c2105d0000c0c500d40d0000c0803801100d0014580e0303154101a103a0b440a0864406c01000d80c00b110300180300d040ca00c05240d02060300031041516038508511070352a2100d030f000703a44842003028004c00300f40301d01341058100000407010f41001981c61117103002c080d8540903c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 752269523 1250 752268273 752268277
    0x5070b0d0b01020a0f0b070c0f05060a1512020d02011e2f1504020d02060703050918010806071d04090507080c0109291b1b030309060a050309011b0801081002 69
    0x3400d01c2c41d50054500101c0ca00b44c0c1610340149403410b01511041d1160703910b010402d0002710666003608200c040200700601d41c09065011410030a140300c14506048800844c4040424068040c00011a07100110790088222240707554416501c2010281d011500910350711045041011501495440c2c80000e155180c030020035003e4800a01440002c142c3c03c0840d243c0c00500030790b0f211040f218144c0268541c40002c1450500981e00d403556130000206104182e405c52a60560b00f00040004000c20a0301040541d00b02000d4500b040007904030010395402c0060b4102000d611a00d403c401e00c1c00c010002803807008071002030f4282c0d014110740200558844486205803041a802c14288260000c40125020300003c0c0b0990001c0c01c04005440c2443c2148200c420041264484055411800700141002284103000c0b03008501e08000d84d00480e415010b010360701000d101d408004141c245c102034002c00c1480001c00319032580302002440040c0360700003e200342101e600445503000c446580b04d000f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 752270773 1250 752269523 752269543
    0xb04051006180203091203040f1406070806041a09090f0709020405010917010e03070b1e0108030f130b2107050304030e0f0402071505150609030c120a05070b0d0b0102 73
    0x20069402d025014a00020b0b50004240985902030100000070390044840034500682c02018080020762440c0351450441c2449418800c5580c840c00411040d82d074404000c0d540300f41c081d10003040c0041d41180d521200c0071800103450380050300008100130b05c4000a500e0780850056011200d24994407481c220892042d40100c41c0000c40030001401304a0800e16101c1114585000008280640e00e4140c0c0c01c581104808544450620051004488034402e01c0200940c0c4801b050040d545031004644c0c0d02d04c9070081c0300c8a801400306551400d1201030b0070410051640706416030340c801d40c0580c0d4610440e80301441c4000103c154011480441c81a03091300e128562546512100d801d6107410004103d000d80ca500303038026001c0040c00300145100b001d05044441d00c04000c2507500301364081e0020706080f0701d211401078401340018401541c0020342e0b4200e00d0b806a848203900000d180b071490408100c00405403643c411103c3c0040e0200d00c20f0010000d41070300f00b00802208104500498440d44030300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 752272023 1250 752270773 752270789
    0xa0b1f031b030b2103120c04060f02010213091113120c1e0b0f0903030d0b0102010b030d1202070f0f0308090c0109080307030e0303041203030504051b10080604180b04051006 76
    0x41d440701c0102015000b4844e500201000300c07420b024a20111038461001100e030350010100200c0d0402101360402c13011403641c1302c07900003541842e03640400da840d460001c0c860308900d6610360b0300a55450380503c04840c6084408802c800d8060b072a04034041c0700040080044440d030110010000b00712008507a244007030010450080041d1345800c003841d4180d04001c011040340c40003003101080540c2c0420040c5035141c245c0d6800f01e48100e81030006801c5a03018040d86000b80c01070500c0200c03881d48482c08003003a81115a006031030708050b0038003000184500d0340080c90001525100d0080c940c200291901ca181ca1303274100d42e5050800001111141440d2207400c0950707009110060000b070080c0801c1a040a0180c126410300e551a44410a09500328030180c012950310344c240024400e040c4030035411300116040f885942d00c0d80c2d2002caa0b945034400c40807001c1083d02c0001c11b010350750b03942020089110380c125603243d00e007841c204804556819071381200d00c0c0c828400712182a805e41d0203040d00b00c410710 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 752273273 1250 752272023 752272039
    0x2312070b040b0d020909040b191a0d140105100e0a110306040c0c0836060922051905060306040804050f0a0803040b0a020714090a0b1f031b030b 63
    0x5000d1a680d0700300c3c2880c3e500c941c1d000d1144001c1611440052803003103002d491181c5550400350b158030301e00f481241c07042840d10f0504c2d600003101d4010b100b0001d01080281d0f041c4008100500385032036180d80f50504403201e5400c1105028440607000100811785aa10b214035101d52103100c0aa0202c5d00d200d80540f4a204040c00010b038945800c1d0303c181c440c25054100359954081c19a0348101650004606030201c02c03211301c07000215007444d034280c0e0140783c6101840148004840000e155406041d144910504c000d0b00021034107000d01d60307162042200c1c51801d11171800e0014800c140c0340b1104800e032412915242c0000c46038540003810600450b00a10440d280c181898180030540321001d5a1541146c01c1070380024858104000a00050000c1d4231090303100d40c020003000341400b4042e03000220042c000e00c900a141e6071003441c185d070051060500000c442e003108001c5085803000d4000c028035034440d8a612858950107400500c1200f40e8015510747d00c07003c03854281c00701d907410310b20703180c105a00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 752274523 1250 752273273 752273279
    0xd0c0f1e08010b1606050a0e0d210507021c020307030e010f0903080f070f0c08060c030103032c060c010506030d03090b0f090a05060106030c09050607200a2312070b04 73
    0x1100140701010034480001c0301141907843d001c0c1522000c0e1f48540d54a07503100d2140e088001d0921070414440c10310300d480300b4912540e034200c2465019104107107074066554404144118000c2185210541001000f020700324603100001c0d44a0b0400a8190b0206001c0c9030001c00c0d640c4207a1010708008415191400e0440c00d41d252220990814007401c01000300408c01000851400c2d202d440509200310022032600f03003020203280c00c080e17016044004020781440180f0019400c50b028122020010345001c190380c400d01c000040300114005d10580105002030003040c40913064004612840055084907122181c8410440840d00d8181c4068240c02002d00421440014407007442d410242c40c0302211809142030326600e00302242a40241c02003580c80c2a601403858000c1811001000100d501c11305001e8152240c440740c042c0b040c000030410000500c03214040d51441c1d5000701400074843c101000d50003c821850400054410092003880711000f001c442c20400503a10050300c54a540f11400c3c80d01e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 752275773 1250 752274523 752274539
    0x2061206010c1b050a1d16090b040f090c0203030c0d020904090b07080a0c090803090904050c12060403020c100e090718080c041503030f080711010f1e05010321050d0c0f1e0801 77
    0x85080301f0002008070b843c10000d800d82c040c0c4003400140c40a62105072010f0700e4484203004440680711100c055410034010080c15a0040c0309444004000401c050f0f42c0300c100d800010020807200b80018480a001030600c90015849080ea80c416052403108100b414540038043e917010120748109603c0f640b00300442d0400e41401e02c0c0c00d5400510a20444406000560028030320300560802c0807155030100c420082410ba04101c919580320341900e900d261000003c0c4018100009443c6581c014941e40300440c00075485201029541c40c48801c501440d9519400c6454440c1c0c0c15000c0703a40710701e0909250910386130441d000942200d6150720f80c070b0120400c04900b5260544028102d40c1071101059a0b900f00340400e0180128540301036000088143e81804042d0706054036040303803485646070400600c00030303408003102421004580000500d610b501d5604454904c1080d158848080c2001506115950001d50b00c12803d01d55486600300e8100240c2c00e150300d0342084600d103000035000001003080314 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 752277023 1250 752275773 752275801
    0xd0305060310150b0c010b15031909051005090601050a1d0711070906080307021512010317090301021306020f06160c0618050c0108011202061206010c1b050a1d 70
    0x314240c0903d00c80d03860f400000c164208079908025030b5161840d4244500d01490500503011181e40d0341d074114204800c041c401c1d41028415003d0740b6968042d00001d110707082040c1c0d800400b10a0050000d486d000306142e4851000380304681c09103200d08000701c0ca402408079010300075088070440703c0b240c0d5240c0d01d04a40c8202142900c0903140105000403c104502d4041c5d1406007100c0d900659030303042d151041c00312071b020424200020304014030054000c4901c801b0040d0440e908840c01a12020741c00700411740510134411050780c190720004400e5400c007500da07189000c5510640030381d9003401c400c038407a81d180c4504070341104202c26809512000c06014602c00d00c8941e01039200003070321495258050700d01444091003566182d01013136030f0f400250780c03050045015200b240a401c9203200d43c0d41c0401c0090043d200701c1c030b4480142d0400110303a43d1042c941e8180301900005410b160210b2280021042101801603e018074101000854003c000c1401340c9100c031007984510009540e001600100c40c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 752278273 1250 752277023 752277041
    0x50f071406041a0f04020d0b0a021b07030203070504020a08160c120302180f030d0e06090418060b1c03050715020f1c0c050a050d23090d0305060310 65
    0x469414411000d1404004282c801d0307120704101c1c2102e95040c0c00315101c03980000d01c0c801510060404100042c0c41c3c407402412001c2d4042d0280d00e281c0c5401000c0e401900603040e8100740e0701c0820038030003010340d030014504040b6402503054840c1e454071035091200742e1280f0b0550300040354204010036002c240580b10300061030810700c2e101244150650340d02c9a034036255800c44000079004079040f0701481035045601c0449404566040c010b07000301c00407a440e0003600d9141070a00030403444d0a8441d48420040300e001c0940148200f151540408501c0c107403400000e004d444161030040b0f0303410f6509010300b02d00468020182c00540c4040159411201c59101c01c004a445826104040003c0f01e010300107031180350346c0003030403680ba03404c1d000d411003410740b1a0600f60384503402e200e54440e042e50400b00320703008900c191404c0d6599070210034054028059070343c803240740e89801c06103c10900d882c844586024804040c10781700110715480c822015640180c8080d03506070003070158200704000651006140d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 752279523 1250 752278273 752278283
    0x606070c0b03070f111f021303020a090e06010b12130203030c0601032004020708040e07091503091a090c0909010b0a0b030718060c15020405060a0e040e0706050f07 72
    0x41e40714803015015400c2510441c010400607a0080d00141d000414440320048900003085107000d035101c040c41c41c1c54550840301c040382e030001e1925612031403001038801468014105c001506d0761100b035000106400e0f48502124040c010011410620310000c551040d0821030b0283c89035201c1d103a0902c6248004041203900d4482040481c20b1408148551802140502c80003000ec0705c800c2340c0340d580b400e8242051441a031041042b440021082d1058405444100021400d0382c3c2c0d80020548640c0825000500b901140502d001846a459000452454443d44eaa0b1107400b42428480c54100419075020020303411580d042c80480c2040030501e0b500124640000ca0940410004a14003000c650441c6c03002d12000000c00000b590800c00140b140055522412945480c100000f4045485188010008404214500d61841142d01a200588401040706940300e002c0080500a050202d869900480c2020b00e40100f502c1c1c0441c0080c100c60a035141d83d45088450030311007174280d100a00c01c40d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 752280773 1250 752279523 752279543
    0x108070b040e060a0302120615030d081302180108010b1005070809041104050d080c15010302030d081b04141921061104060c0b150a09150b0a0309020f06030609060607 73
    0x702503581d41f00440740c041e8660300a800c050070400225600c04c246801428002c0d0300200344000c00716444003180703a21500300850a21452807510000d510712400a035a054114002400414034074410351110b2188502244c00d4100c6d211140310546080c0100c28029140d0741051013195814141070304a0403050a8034013009152030307100d0000820b1415148000d48001d03e011a40e6081e005c820002c0020b0726607c1802958558516800250385402c40c01e600c800f080301d108040303800300800300400004c3e060007840301c9032105d0300d0300c4a41d000410489580c6200e004080701480f030340022104040203813010070102d40c0006510f520807a0041400e171108445080d034603030300c0d01e00801c0090040c201804103940c8501c452080703814030502c400000b41042803c4040704440324170550750041d03190226030142401080401f40703064451084080ba038084142c2860004190140369810b50104130068400c4846040074284a010700046000440b40c2d01d0f00b00c600e0a000c030f1054500075000d01440d51082190030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 752282023 1250 752280773 752280779
    0x1030f0c020a030e040207210c050114150901061d0f0405010f0e09030a0909180b010e071205090c041e06062a050606040506180f0f0108070b040e060a 66
    0x1000c8030106640360005800c0160802e08055000c2068041114102c030300f0f50800200c1c2d11840a0705190880e0810301c0300762142000300d1180924070aa2450303400c80c00130020040c80503071140c1094421a050705800710320454208441c074100c15014181c1d810740c0c1d24049c7d80703468041200308019602108a601003441d543c403055580c0c03107000e824083c0c950440001d07101b07403501c0070f0341d614440058811035094005210f0196510340c481c10200865920b170f000801d05c001c0c50b0042d016460403040d0054860b169080021840280031202c41e8020b09041c0c9e83c400034990108607610441354250360144681e0494802c0484a1901e9040343c102d132000d180e15080302941d801ca4523801c451840d402000807913107400441c030b80c0c0307010f0150707410464203d040749603141802c5a031412f84074040103020510956407880450542e81301c03600d401c07003150340f8202014501e0401d01c640b1b886070001202d5046140300b8040002c283c070040030800c001100d9024a59500b05410026030031070b21070380181602d410491400c000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 752283273 1250 752282023 752282051
    0x1502100c0e060c0102040611073203010905010e0c0604050102120901031e090210030b0102030d150504020d090b0603160308031b0301090207050f032106180c030109150e0a05060103 79
    0x70203c0c900c001d0300040c0d6440c60041c001c1c1408110000e440d1264105075001c100825110090b01c507440011003031404c015540c10303a50f16019880d2401c054141d0328000041c0100101548120122090481141e080074056820000c15120740e006490050700280a5810805c011202038440c68905040c007245268280180032034882d8032115601025444000b00310940c10010000e9541000d40d190602104003a000040d50324814180c3d10b00040f9039441d00c030f01c5086503580c0100090a4000c000359075030320f28035081c1405803c100f641550300e4142500414414039000804904025450212085480c40c5448009041e040100111045010f420690b5030000a00f00118041c2213011001612014a424101e01c4d081c40c0b14034a080e0b56004005030312440054500a40688200440303503003140e65080081040060f000340030701e80b000c580c0e800b4012000103900c0a103050b240c00450400c41c03800240440c500340c1306140305e070a80c040740302ca000c552040560b41201d540108107042c04255603c1040075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 752284523 1250 752283273 752283277
    0x3240a06030f0e2b0306062a02151206060306030a0b220f05011508100903020a060908090909030901050703050a020a14010c0f0513060c020d14070f1502100c0e06 71
    0x1e50100a00b0129560031100c0c0d81060301c20384c8020610307041010504041c406080001181d4403081080c034116a00c0d8842d00108100121840c0d024104008480301201e0750340700c603040010404c100012213030000301282050800d8078030030903000340103002e90b030748070348803901070341005460035040c20b485a916100e0b81c07071400c0703660047e64807500c1c03584601006810010b086400b004105e0f8201910702c001040051000109217004107a20900040c805143d0b01e003c3e4605050b00030010141750a00032400d00780030030f20780070300320f0500240c954225a64a89154584900c20580406d000c91400c1c490307a03012902c01c00252008031420b00407180d0b284456202d069906500164501d51607441d90a02002d043e4490381d01020b40c8280c0c24814140307200c04102c445c0b000c04600444042285224a4030150359900d00400070064100d88075240c141c41132280c4030380360005801101c00c2c22103070800000c5d11030200580300400c4242e0754040c05400c000c0c3c0b201800a4204c01ca1120108100c1030b2901505030340e01c1c40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 752285773 1250 752284523 752284543
    0x6010308071509030914060703140c0a051b040e0d050315220902010e10080a150b03151014120723030402030d0206100b0306011808010203240a06030f0e 67
    0x1165140c8921b003031914400ea146d00034030765000300024440c9000194000c007603c01d091001001103925042c0260f1100e10700781241a02a00354403031203030090701e06a07158011600c034501c1030350b090000c1c80390340804640e90200002c1d0280020800c20000e014100c039503403806101000142002103140340e0010079000b1080c540204000307260380c3c04010701150303005140362103c00d000f0b60715020004400707940980300e040000d010145998a400800100624051002c4051305441c032041e9140d0400f280703003900d04484845034500445001c84018401800f0300041051030014200c010702e001001d1520b40d0380404007038052000d200c00700300300d1001c20704074050211100da01503030255180d14003801054076008682c07800c1419500090140a40f550105071034034241c0d0641c05901d5640d40300d107c012541400d00300700114100300c0d601d4001c1000501900110f000e20f030605803040111402000e4900e02c11000c66029500c001d200703004100250003504103401a00c2d40303000000d01703454045c0700b550401680b0a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 752287023 1250 752285773 752285777
    0x3010f05091006050a0602030a1206052214010e04030518101205011d160c051c020c010e0a061d0d0605010f0902031e0c16120e030f0601030807150903 66
    0x8564000d01c001d00d2183c240100400c4070031580440c509000a522441115644000c003d1850070804a4140f00e401803030083c13601070000c0d00303421080e107841001c1e21a01c0310001801810041501000c021466001d416110888981c0b40e054460b95400d852a90000d8802403223045614940f03905079403089503e484602194488807001e10310409070404494050b040a407640303e850f840c034000c403c4040c101907030200902404043d00781000780199813408204900922622074070010140303008030b1064411400640741c0850300a000c41000643e00e40c40700c05129500904036480070403100340715146031054036807101c01300301180072080d011654001901c0403d9500685500c0100083c88121516100030661581c0071401c6042c50004158544844441410491104400300e00226808012240902c043d21240c0195014078070780180f01e0030100401d00040ba8115100c503406007800704049408a01a03009001580e0075990380780d481da0070190307050381d0002144600c00c1210020b4850b0011a601079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 752288273 1250 752287023 752287033
    0x3101a010807030f0c09080706080c0a03020f0705120a0f02060631050a02070c06080708060904031b030801090b0303120f0a0e160f0614070201030b0411040321030504170903010f0509 80
    0xb20b091f03d4a49503940d03004100704400e103010804078038050416580001060b140140e980c030f02984c0f0a0080b4065803901611074062150701c0c98044075984024070100d14140c03224100c000503980c0503a1609001c880c0c10341c21003003103a640310ba06001c0342d41c80c0381c8c00b4031a0006204403003210135032901111402c8501265042e40059031a00340940d4408800c010005403806483e54500843c0003132602901500540c0200f0500c0042010940111900301080d03071809444100c1d41c0c220704000707161040a10030f00400078917045107401e1504011044450310200e400030a074240d15454001288802c0051622041e507070f83e100c40200511042c00701211000c4590906070040e41400d042014010f1154408428040d82a0101c01c60f800c2000c25959282c0d02401d0004410010901050140900d00103180810b10009804000c00c0000341b0303d09500c0d111408002d5061841105c01da003110340a035030180c901e4038503404101540d0703803900080070951000360001c540c9440c0c0d04c0505058030000d03107042d2084d0b005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 752289523 1250 752288273 752288279
    0x703030804021504081216170d0608010b330a050d360309031e06110306090609130c030b15010e060306102c03101a010807030f0c09 58
    0x711080840710003c10480141c9030510300107201c2d0340da540b0782081c03e649000c0414a010020444040c5464894002c85900d04034850581c0e080020791140344040243c074940035000c43c107868140701e4021000c402030315844414411800c1142e01c054008a80b0300101919000780042800310000703410710b81d6040d00c5050b101c18500741410300340d40c40b0368400341080f21208030300c1002da039062001014020140c061410b07081000e00b01103807807408a80014080c1502007119a100e088442e0814943e2801001704228801142c000034810788415580300c0d60051000b0041051740c40e0480740140c02000d0421b10801d0002260340b040e100c40360541c0103540d10100760040001450801c5c0020300045024640801c4044a0310009101808003a0140d40590b134480f4005c400c80d4096210304c000315105500814110101030441640018424171290003030050001000100c0b019004042c151101c2c200107110b52407000c00110340c4960b00a010708100341c1c550242c80c0380911144070700d0407030a840e503448000144c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 752290773 1250 752289523 752289529
    0x7020d05011b020111040512150c0c070e010f05090603030403150c09082a0d050f03040f0e0c040b0708070f030c0308060102030a05180111030d0b01080c0304151d070303080402 77
    0x2181002500659041828241c4170115020803181550f0003110350340002e42004201a241c83c2d82082540c103e14610024000d40c1c0c942440a402ca1040c817000b2030f00f445032261000c101809087c410200a0303442001c3c14003103441c0c144c0202d40d000101030110390a0070b0352034441c2c0300b0348460900131884841e680c0301070502503680602194040c19280e002040c3d0030700243d0074104010890b00a50080411070044200990f03074001ca1403028a03004400c6402080c1c1800e501c9449034803030310541040032844400064030400c1206518410640703d2521070805103003c0c092040d43e80b08080850394480200200000034100d83d000c031003d540666203148000405140141030800041c3c40c89040d5842030140e10425036114080720404814840e17002c0c0040b480000585030440f522032554428000450791400d092a507070b100215110b8241d840c0b054540f911030011110784410b58016180842c503c4007152801d06640003104800711881c0d003004880501c80406081508035003040300002c8401003403000398030b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 752292023 1250 752290773 752290811
    0xf062c36060a05030c040c0e030a06051012030507060908090901090b10140a210501150f090e13020f060a0504140901060206130606080303070c060f0e030a031107020d0501 75
    0x444207840d031a90b424203000000f03559088224041303210382e86501c1440c9006218102401c0031070800f030102c43c000141480c092001d40f400f1601086c51904007400020040410540300900c40d4042c1c0303800b49022655142e130000f4044488003660011400c0003640320345c1c0c4074103961a000341101e440004d41c11114200308180c1c18442ca04503801c10034014007148a00b04040c04030303944005641404421080101d0110085610300b9801010040c908000012000481d1804c818030751a60340d1042140d100600c2c01b07a500e0355090080705030002ca4200060380a4800c3c50104040300d000600703110b00c2f144c098000074541e030b2054480000188010900300a804484141076200d02e40031540c404996040050082d07a90720000c1c2245d4441c61050104d03402d00c0210307480100070340ba0401c1520703620b01c0d00810181190a80c0706084400c00d207850480d41d5101100e106070303400944110051807800040c0d903411030241c0344c0c1e0000060751040070400b03000140e0310014100005071003000003068502e60700203001c0c404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 752293273 1250 752292023 752292031
    0x1050603010603020a0902070606170601050109120b0a0c050d11093105180102040f050f030d020d0818060405010f11160201050f09040c08010f062c36 66
    0x41d03814041e041c40180e42d141d0300c08003a070b61842c40048c2c5404840c10401c010f880315078000004001c0b0300d4240300c80202d0114800c0d050320000c1e2154141550742d0f2240f040c6103420b03039138007800000044001c142ca911007a0060380c4540d071545003c030705061291551100301c50003009002c0c80004005001801340c02c03c1c000c1e0341d20720008807038ae404400f42112803075016607800d80c000380005030350340d4002039000946100d070325501e00c0031800854560f6180c52490300030400c1409403510400b50b58840c8910341c038000644c0880f240141d40604108811070310141c4503140c000d0b00715481440c0e0300100d0300d0f041d24200b00c00c502c998040c1c0000f0074000c0346001800103c1e03580600e41c1c00421401c01615500c1207403440ca49143c203a0a107040fa58644044868034824022417040e41c1c0d10600b0803c1c0d50a004d0790092046069030f450054024240da61080169003074642c60b0154820304038090f030509410ce1070241400006080580f80d4034690702000d01c2001d5035150703a5482c00e200c06660340724140e03a403450000c007980 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 752294523 1250 752293273 752293279
    0x31e1602063405040e010315060b0a050910021c0518061201120c03060e06040605090f1e0102040305120c12040e0a150807060e030c1c0f050f1905010506 67
    0x41244102845030301d529060740042e08007070b20301c0c4a01e842c40f44584101d80c001c0c0f804445134812541c5034504155030340d180301c2d0000607040c2402004180c2220b44800c5411825541c0c407100c2c946039011083c0205a021001e405040d80960b0300b28545405880012a1403900559129940c035200c1c080071010003605104030500805042c403078401c0901817505164107440d0060307848021002d041c5401e00c6103030110740005000a04045405030018030000e032480c0a68445c1d24144078540d02d82c2c00d410740c2c036100c0200813040d5070301440c880b425840c404120406440781113400503190030340b2038440500d4181e00c841810508440080c40d181f85007400d12100d5200d4681300100c500d400e00d0074400c41c441c500007500d007104d020b41c3c40458000c16240340300c2d250300a02801041d41e1600c0c2c1c0d9050301071b00c51200909801d000f409403d001d0451882c0404180d04a00c540d9403241e075000712241c607085032800102e001181c00f44100458140d07203031020002c10500380d141040e0500ba2010500d0083c2c00c0d92005809140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 752295773 1250 752294523 752294551
    0x50a15150206041403040b0406050903190209010501030911040510030c0e09060a020a120501030305090a170d0e0a030b0c0d0c030b01020a15090b041118010303050d02031e160206 78
    0x619650202d400e0350841d0b002410040c4015807101039504600c00e59021500344100014005001908500505011607044040d0f5000405040c1e02c1c180d90300030214020740c051358190050000d507000c0d40c004600700e8010b5018032243c401100208080f42c6d41550703107910041c10710100300108119183c0c2100138001642e44101d850429045581d503030759002d400110501d401040c0404840d200e40013114107042864024000303940d4a00f0003800c40d41c0130341e03100c5002d00b906507400f240c0c800d41000020303002444c0300d004041d199006281159083c402c6071803180d102000c140c0000206006034031305401040024100c0d41e56402c0d6424180441c1c08140d040300505040ca9144c1145a8010414002450f000302c002c4424031905401d210092201c0400200f5002c0920103000a015a1154204400c8810394012140c00c0e116981c8191410003480010000740f003c00401048040035000340d90842d50020800c0041402c504842680e41c0080382c8050154807200c0c248800c1642c104106504000c1c481c0da10f40c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 752297023 1250 752295773 752295809
    0x30f04080a11101b020f040c0906180b120a110c030a030c1d0d02120d05031b030103021c08040b12040506100815090717150a0b0105090d050c04050a15 66
    0x150481340c0355100480c044e02101d2548055445030b0b030602000f024000c204100d954200003002e000a24240194400608480410140d40031111040c0083e1040428405d080095140c4441044003000302015249030303c6142550074000c514021300886034000028544078600d000c4020f007164500e2103613004104100c0100780340505030207040b09140d40705603449220401d00f80046880c3c42d01c0c400e00f0092a22450b0fa0402044d42e0203006940284007810155100f040000a0307084280801e00002c0c0d44100c210400111030072100103840c1207140f0a10300036040c41d40d11010031034960050b6041198003107904042100700b0070300340302180d800303803000701040286410008099952550214400900ca8214020542102c410005000101030203410304030081c0040b80e115484a4034129000301e88100c0b03802050200341c40340542c80c00c103001a03441609080302c4008004035107010004c20f84840c0154405604652528000c0c00c0c4907c82c03484021803003580310300c0c2085980600342d0101d1011407400c1030039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 752298273 1250 752297023 752297027
    0x2041203270608071e0c03020c04050c120a1503080a180303081f1a0c07090c0f140c0d0305090f0304030519051912030501050301021303080c030f04080a1110 69
    0x1c4030a44400b450000040c2e0b03160716040d6004120040c0c41c0541080d06103018442c0c5901c8080300310114400c0c1d0030380d40c030b0549850920040e20010b840300307602e1000c2800b00b40510340cc040707003040e804040c4180100d000514000d022405e010540c10603901345100140120560b0340000c070038116800781d030840030364a61850300e008054503805003503465150308442400d1448094895803602621054000140303041000e4841400c9034001004c20000d4002c101000444107680e1141d040c10380c69507212945003c44c00e41c4105c1d815241c0003510ba189030310620030640e03101000c201000e0390303000c651070000d42406d00c0c0410516041b03042024070942d6008101c24400600081031680312095002c2c0031501502d403034941107003050082e440410700041980084424080e0101c43e02054025035141000141d03211418542070340301720040300008621040003080000e104000500178040c2d51790580b8103217400d10040303083c03641c031540c00003060341c2c840105c000a009520f60403100103181200c0402c2003208420700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 752299523 1250 752298273 752298347
    0x111030913020d020d06080a06050907060804080307030912030606270b03040f050303071d09091e070b0a230313150605120a05010b01090506070602030a09020402041203 74
    0x6800542d00410582c410021680507a001c805815000344001c0b5201c1c00c04a13030702d080003001900c5a60070322005c5000000c010801d0000d0f80c0003952070745403560f51034580202d56030018007a9030070999290001400304084400c100f25032070700390358080b90461038404028101c10000100c0d114665048803488108040400f0100c21070b54400341940c0c0303a5840f41000b65081040c00703406001030100004000d01d083c2d0118a4406040200c3c1401400c1e21906080c0040c5a20868614141d035001601242042c00040341d10a102c030204002c80301007d440e110103006540102c1000c3d808910060607280e04808a03450180c1a05016500d142c110300e003002203501220303014030014000001125103000003038019005200500740241c64154040084034034039544081d008425162546071441d4004550310441c0404215000207200a0429040c1d4480600135440039050203041075803002d003000107858a0001d800141070195051182450701d00b0050112018a40b01200421002d1400c00000d0300c0050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 752300773 1250 752299523 752299549
    0x40609140406050d0b07031a01200c03190302070803090d20031605120d080c0d0e06010314070f12140c04060305010b13050907060f050415080601110309 67
    0xc61148160148004180107000b260412500018607009503420300040301401d0340220640e03682002881d022401170708581c022034044030700017802075510391a84410b110203401c801414406841c40d5016041c001f91030300c8600101c070920b800d03c1e00c01c80b1091640501a400c02050710401552030403a08000080780445e20420081034603240c0d0200c42c5c0303081583c50a02c4d26401010b0300b241c1c031180040c1c813400400314880c400c5901c10215801100c03046100458101e0b010349003600c071007001e512041402c80c2c8075080360309281e1b00b06a6500d00050090b42c10403100c1d008600a495007103441c407101c002141400c00503003100d1072020640300c042200100044c4814a01398109562008500c0081e0049050401607600585e000c0c1c20244080140141944a01c6812108581410580c80c24400719015a01d0449000f8180d0704040b42c00c212107030003928140325203115440c003649400d0715030301d1191840c0b15a20140740021150b400700091942c100180e201020001d00003142403290075000200c034048504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 752302023 1250 752300773 752300789
    0xa0f0b1816120212180a030e0603090a051b0a0609030f02060d020904150e09010915110c0616090e0c070330020306040b01050c030406080705090d03020a020a06020102040609 76
    0x350000002a216038840741002d44003040a541d202a02e6119401e0380d1000d0321414440c0ca441e0a00386607034000020954401c41e410380710191040d140804101554000600122060265030b400300000b5006001910b00990380c010126080c01e803170390030300800005540210f024001c51035018008904500c25081c00c4a9040320102e07076804e003070f00b48034021b0300a10541a03082030929860907612508a810101075076044814000706554a02c0300ba400c4c0e4480c204007400f1070140086400c101ca0042c0c020350558807003014114030741074600107081c3ca00503045400070050b11408010366002e9a01c40d04000c020b003030185ca0b0307640900341030f80e0038049803040c940d0040500c0000861589440741c400d0b190700c1e032100f000701035040407018a802e10001e588100c0d801031240c1c2c90405911210741c05101039030540c0e0340b21401581400c0c1082c0042d10b4290010b003000b41030103800d000742c8406035034802c03903842c040384030b98042e1010041d2441407110b00803154104c58250f900602080c040698003503481c002302c600078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 752303273 1250 752302023 752302051
    0x10e130b040c0e131a07050403030c020f0910080c030a080a0807181205100c0f08100e0109020403110f010e0f06070602030106050910030b03030405010804020f03060a0f0b18 76
    0x2a2811003488030059000f0180704a00c1da040082401c0c101c01d1200c0502e024a84500030ba6241201404103120102c03050340120390144000d0010034816050f04860328406414102c0f01c0070407a00080c3c00110460780880c0410301071000348200355080c8404603000c04207600030b082d0b000d0103690780c20f00ae02400d0155402c102110740020889441201200e510890100980940f59140c503540c55541c0b242070780650721441141260240041c040c03060444101e081ea03903041c10741c4c00c8060b08541c00d800203021000e0402c941040410070444000481f8001d044100b40141d4441c5075282640304e80b1007460005104190300c00d808015641c01140003240308000701c6d01e1002d0707500b0700d00001e210784c040d890300948040e00c003200119109800c0700007080000340031260905002c064110032400c0d81c04c686043d0360940c005010400013540911500f0340c209100804e100036500400c00400e20b07000007211600041c07910360028403000c0b0441e02c01c4040c034a40c1a90094076040e90450707003040284000d00b50614407160 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 752304523 1250 752303273 752303281
    0xa061820030919050d020c01090e01031b0e01090903090806040b01050411040b030a020903010e0f030a030b0103020f0a0e101106060d030e03070306050105191809051023010e130b 78
    0x600c1030702079081208072a15482001e5080c0b2a030f8402d44d4000f03010241c4038041091f06158011a01a000c42e010407442805603070840c1d481140c1d41c01d0003035141d01403905001000c03443e07075052010746010b400540c00025203440c07541402852125180d00550440d0024018000400c202d110f08a0645006440c04a80ea661490744000c80348903c2d440300076030340008014890320074000c0e0020048410304034000d0046801100c50381d07882d10001c1c001c0360170950041010341089406030304090601da205050040c03e0803000350703040c8019400150b440c0c00280031126844114546141e01940500603407810008000e1030180455592101802d980e01c1b070303c03001c3c144408062140212240c03000380501070761501640c0e03181c2000503000a01500c0c1c880d0b2100d108011102d54000c007403404440b6818010095aa600000ca400034070b00c6100503603184c01100b4200080b1134050180701e07074076121a0300c0d051181e040d10002414101e0181c10290303841c09000c0c14011040409101c0c125210340142d000400c0c0c0c0c407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 752305773 1250 752304523 752304541
    0x90b0306101107061e0206190c1e0c030f140a081306091506080303060609040c090f080d030b060a020706051602040501150f0c030206180106030b0a06182003 69
    0x114522040400e4840d0f408046249503104404028a00500501240c8800c0e040c4003607843c1c00341184c269031516840314030001407481503040040d056100b402c201002210707070508100b040700d240306c880c804942451048810543d014004800305122403600034114602030850341d02c0c910404075403008104854020030555621991000d40700c1d5030100b4104a60001c034600028030032000c059885001d86080800504590302108985c42007100426251425141c00c1c10800185034151420301085003001021a454818084290140c6001c10041401c500c150100070181ca0f038541d0101e004541c2409030f200e030039800080e814280c550600341107403541e4103611000f801c0e814420004e07600604120000400009103501c1e0446035886503124108440a0b0000b0390743c0030ba030800d000f0f00603803201000440d08150b801041c02c46100c4880042845030341c2e41c0700c400541c0029034845442e0765946608101c50701008101000f4003038012020700000c0c0500c10507402d42020010032071401c100000000d91804 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 752307023 1250 752305773 752305787
    0xf020c03010204090b130203070e120a0f26070210050f160b0a11070b040305030901110408070510090605031302010903050a03270e01090b0102031603051306090b030610 74
    0x225014008648855030b0b249150091300c0021507260040c20100f52440140c102c1d4000c51f0300c0b80003035450741104800e60108ac04482405140300344428014001c640000500404ca14030035180504c85410440c402c10106403030122039802c400c0d050b46400c02038000103883c3c02103545400c040e2800c2164882c102a40301514902c40c2c80c80c0714818206121841c01000714031844c1c140942c0c0d21440802910801c041c10340d005105a14000d041e10003140e0021b0b000901c500300450b48004040000705003454200c1782e8540c9a0040d4000c003065400490040c03005081111034940a95024606204020310304000507050b440043c0442c142da0503004401d90669008036888002194010100d46d003003569400d004113072005c3c8096030050001044007605001c0000c4070240207440602c0000170b82a4604880c50008100c60000241580400d005081a908400407410461030082d10342c5c554131030b002c81040d070428a8940110741803003002d4205102c83c540506c1941d510117403d0b560001c60203d4003005803400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 752308273 1250 752307023 752307043
    0x803040513090f080c070305060114131a0a03050304090f0506010804110316062c13021e0a12150f030b07020f120919030b0408030a0b130506010e04140105010f02 71
    0x1310018110741d18250004441c030460f806001035810503601d540d90880180c240341201030b0b000b450100440708026956011400740c030340905c540030080c001c85003c00c0c40c0c03085992040d02c09030400706023080708156502030aa01e040c1d15000c00c0010785041000a010741b84050401350040c600c003640b00c1015207041242040a055000f020317460303155545c00040541c0d620341400c0200030304046031941500d81702210f0a41000f00100202628516080c01c18000c0d04200d02d04c1c0e6541614480b103005807545003000b0a07212280303598100ca9006074035021b0742035a86078159140404004481000340c3d10f513038007424058a40c0700030b1001542d00c0c0c854007249030810f030000350011800354502d02c0000f44004c40040039100b0042c2c3e5202640303190348241c20141400c0f844046d08040c40d4400040c00524503900840d40071504140004800742c100700450181d44254040410041d44d40f8244049513820003640000340d40d088809001900c1c0300d8420314214403041c41a2418095500c400301c01c0c03907000f0f1144400b5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 752309523 1250 752308273 752308283
    0xf0803040b01080f06010b31060201201e0f12073b06340201030e010507020c040b04090f080703110f0601120f0515040605010803040513090f 62
    0x490800d42040c007401142071007803002030701c00c0f000b00c95030950010800c40c0c102c07011060041d080c01c04000000000c0c1c461454101084694001c44035081d000759810030300a455030b40d0002071502d4502c80320303249030081e03682699445201800705202d410007142108030b0400c802100c0c01d468004100100f9030a00800002411341c0035000304001d00b0981c04140110210302c241c03224a80c94807080401001030f40600c0c150b6040e007122400e1543e4a040440081c07520010119500501c0d50421440c11f1803242c08044074a014940900504290760389406040100465040204518202060042d5076007030304903031031400f9030f8641004103850f544075408805020b4122006000d190040c0c50164071030390001e0380c1280400d0150606000c200b80021b00701d02580d0804009186607401c0c2002c4004d481c103032010441724880105c2c040d50014000b03024040c822410040d00070b41e0b9081038030704081683c4050304101c52030341c4113000c00c10807652030003a0400740440d403410024074989103040c0304881992058010b00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 752310773 1250 752309523 752309527
    0x12050a0e041a01020c041109090603031b06070f110d080c040f08060402030d02030c1905011b0e150a0e15070b07020a051915021c0e0c090a14130f08 65
    0x14420700b548142072004034090b8280c8600d81c4c9003208000440c1c0000103505030860301846040d04600f4003003407051f004031005044a061511082c1d01540c0e4010072816414650000380500680c070781c000030360f0f51a40006060461900807080180d59640c0e42122000c400c015116000c203254411000844018000b18800403601c90b4035003003c5036440d1030a1310100e003e1700c242e07411030312000e00c044107554400d4140c0015082034040f0179201d6519485d9480142c4055590313103040941044010544161042682c44800d4a11182402c100c00c40d4450340e60440680c60800808103d164082c9500c4142c0f142200c20580e010b01a411221541c01284001004255610103010550343c00248080200c5e10641c201c628141040090944403000c45000030a540d00840d400c1d40740d8102c90300030340043c0700421514180400b080301d01300240c483c00c04082066802001c03019070542440c90b101076001d03584100621503141480c050450340e50004118043d1444c0d01801070f010031441001e844460394004610b03503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 752312023 1250 752310773 752310791
    0x70503040210030f0e0709140f01030f03140c060f0f06031b21070801290307141807080702010e0609060a0209150d050109051320190b030a1812050a0e04 67
    0x30003400823030b806d0303d0a1050390000079100f0300c0710b8002c1d505032640310b1005c01c65001c5d80e03501a9041400c500f00e03c64025002c0c01841c1c890b40c000c11040e48100c091184001c11414552404034000e800034200034000d030400600e401e03c1070354004416000702401d80e1007142503065105420b51105030b1903014a00d43c02012000514070405402c0107600602820440800ca09024403121a034803500380c1843d010380042e2400c00c80c0621811405043c00e40c050041d00c4031010041154480c03280494420021441500070b00c15405e50900c03410f8215400800100894200300100300e54800c4000c00480d05242c000a0011064484a150018821003a0038075074481c40c41025810152034240518541e20349003a0003e5804600c03050000e4145801101100c00240c0081c0048840041c5030705007900440700b1410b252411580c41c86c00d000419155003010386030300b00707030021105607803a5120003070034060410460130220710040c485010305036150514941d640d41c0c2040075184400c140c1c610030741c0103103018142 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 752313273 1250 752312023 752312039
    0x18030819140609060a0e0114010509031c081501090e0a060305061503010c03141302060c10050402030f0721110a06050a0e01022103090a0206030903070b070503040210030f0e07 77
    0x541e010b18000c40e0300c441941e440790240f125080892140c9440d4801c8840104054114080701840c2c01d0410326020b4902080c2d400442d01d0a2114440c0d03468084810b60644036a0340e10080342d680240c15035805518a0b911074000904030085400b55a80741c40040c4041028511a83d00a000460748901a20090310b051308414188604008501d4042e5003411102c0308001d10034403078140c0451110100950316202d1800e0742c0c0500f610b541c0d080381c03c14070800562020703040401200d2000e00c4050f60205072071a05106150500c2d00c10b0b41004183c1d400303103030140040c0312845120121740c130950708440402c458900780034040180a041d1a0740101c41600045101a4060700030030f1400b296486a5014032066401241d0710561540440707100e01c489030004610403007480080d030304521801c0c11070301044259000910700c0e034405c1d5808121f82d80002035110400803511525136104809060403402c524240d00890b20f0590900d0034802010b0307440703a02e02d110b60788582c040241c1c0d0301003008032500c49448200c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 752314523 1250 752313273 752313311
    0x20f1c050604050f06160e012c011e0507120327020118081c02150c070203100203010302011b021908010606110705030c040507050d0510150318030819 66
    0x240d034580200000444002000100f45000303d001803880f407641c05968100315a031f01c65100c121410800e410702540c0d0b4001c2200254550034000c003d02511480707d8034000b41810903581260b02d81c00500e250001d1400f82c011050711560340d005000c07031a2081000800f05c000b4448003a01c003031100f2418401c24031005141041d40c11181c800e80303601e45501024048035000c450f45210308007035540701c9550719040c10300200c0343c100001603500403112140030004d4013542d000000c44045519050100e842c00542c074040000c2e031203504a54004629550450700000d221460b10700f0849004001e1001c0c41e400c40d2240f054010a41d0030b16080200c1d002e0301c3c0d4110398040d20701c501c10751000610900144100d1240460f80c1d0040310b0b401001045410030f900140f00113010002c0188050003814405040b8071601e90041503c200207900c40b40701c10504007845111004c2074100100201450031300320725503000c81c0c00c154200d19605418048060356032141c00c03c003220402c0038850030560505003d10000150504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 752315773 1250 752314523 752314531
    0x140a050601060f0c05060601110718020c0d05070b0622020d1b170f0c130602010605130522080c10050603010c020a031e1b0b04170301080307020f1c0506 67
    0x9601502940c0140c42144d03540c40440010302203400c142d02203212580542d040c000801c01d03100c06d85d2006030340e03400021140c43c5100c044071a13003500080c2c00510102c090103058072001c103a081881c103004040d00c43c040c00c514020314181c0500c3e411841e1000b8950451142900002995001c0d50340b81c001740b902001801c443c0b0000014210001c1c0354011507402202a40b10003051102c0680c005d65416803545407600000e825071402042c1088901d9084a20b0007010003c0d000c075800228260b841c000034012801244da140802051500c418498081905040000d011b00b0306c41d80f103c003400c0c180c104140d04c1e101c1c842d9148802e104840140d070141c0860b42200b84641d5044008112814550340b0580c0c45080000c4000c0c002801c1c001d034090710303c0880756460003400a6150038180050741c3c80f0103640b03103094040c05a40058a074000c000c00c015006045d44440420006454295494520040d40d81c0c099070328000d12803580031550a900d03031228820404200d810415101c01f5100c0b6042c10b94580707030255 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 752317023 1250 752315773 752315777
    0x12030a0c051c1a040b030a060515281401080c070c08060a0605091003053d02070b1005060d0c030b06040b040303020709050c09120a0f1209050406030519140a05060106 73
    0x203255101c403807804d0700c10b04002120180203404501001e903285030040000038040342401d54210241010f989520031224045046a0301c0700c00929030040c821752096100d0342c0311103d03030210011000d2669901c110b5503600001011041e03600c4139580d140c6100406441c0e00180341c41e208880c00c01a020106420a038215a01030742d400c1c800d80c558400a681e0b0042ca40005070003a4001c4030700c2062003182903001c603101802168181c6259050326034052005203081c5040304040d40100d035000c01d05c0001c01405030411034008034081150300d0803000c202c881c06415001400a0390b29842514420b0094201000300f64000b064980d407107441d10102d110b0760b001070100f50014411920045122001d03485154018107a2186540c10300100c3d104221545000000241b064000c07001c4080010b00b201c5c0d11208010b104401d103220039100448001d1801d245640410b100b2810200c0410118901285041007400119241e41d000d864508084170509440c1c8405080b91007903020391004c0c4103005c100320341038540036 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 752318273 1250 752317023 752317061
    0xa0b040524010f170d0c05100507020115170c01031d0303130c150507080711040e010614061606020c0304030f0b01090b04020702370806011712030a0c051c 68
    0x2400c0c602c8403400000d2804e02d45a485418031005550040011078031203032040b41120710802da00700e500c0055841c26200c0c0700142c0c3d103c4505050103420013048901400300940102d66841000013980e503141034108046040c19621588008100f05090402d01100b09207005c0b00ea03a410300d098040000d900f0208147c5042e040f510300401c5400000d020403c6500c1291317030750703420000c050b1100b00c126800400300b110713248101740d424400c588460007141022204031000185052a0a410074075490291380d07010310403031041020340441e018400c040d01c20140c02c038600503126109604654a9442550400b504d49101c40000c9820844c0c0e804d003030340c1a40c00c00c10091049c40b50043c00d0000f6406070b0781c0b001354054000304083e03119581c0c00540f03500103120a00b80820000e41202c440349004040c1c1c004410b50b402c020014841800d40e00502c06200c01d20500406184292034401c51807030001800e040d003940d442c0e113103518045224905690651020900d8420f007881c04000000080c602c815542d4801410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 752319523 1250 752318273 752318279
    0x30a0e07122301020306030d11010f0609140105010e061b24040c080102130e270106170307050a1b05090a0b090711030412030302041502010c02060f04050a0b040524010f 74
    0x1030083e06e00400028005181d0f40030340072001d40c0c00006500d06c95142c0d640e2400340b14144c0119000d104001d00c0c00c850300090011103002080e81c1108141c10507814400c44074000c5140782c8a1508403100000c103418050540000e1540280c1040062200c03d0700f58000c004c400c682525246006a0156108659241c1502d0380d070304456003030340209400d0040030664040b041201075000d11207a50b00c0b03c2c2d001c2c600041c01c0844408180e491403260351081040c1c1d0345001c1440004509200321051002c1c041c011400d007440d541d159941c3c0c008440c401094081c020f6002c10011a100164401404008ac0348545620f09204600002e006043e1500c1c82001a84045188280500441a203020240d0040d601d409e0a200020588010109048007015801c000014041c1d81885c510301c030410f059400803403d02c0c00e40c68003d00d000d101030205012100d44034280700001c0e40001d600c0d0701190b808588418a035407107040442c181071480b4182c2c04a0080d44072100d140c0c50f44101e0b514180c607080d641421040352 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 752320773 1250 752319523 752319593
    0x708100906290c10021306090b041401021e1006140d1e060212160801141c02060c150a0e0312130c090903140a0203030a0e0712 56
    0x800d41c070440606404101c01c12a00d0310140c03140150310a8600c0d001841d00ca1044500c03844c100c01d041c894950541d0120301d80131817119569130080104214907065196900303001d0700b4011840349102e00c0c21849403400780d4003c41c1e4000d01c820601503000740d10146815560103213054668001850f00500131340b42c0003000c26039900c0045840c0a000d000b0304408400e581e9551600300c454000070428403542c035105035990020701c450004010103055805240040d082000c0c060090180d5000d0140070b00034110f0060203444559110f510030a181180c0750350824545948a0400342a6094041c0d04010001041c00780213078000b40c55024103a031101480802d1340d90035191422100c0f860b141f14030030313001048506001100a100342e500300451401800441c4c20a0307a0b200c08140070b682c4803559081c0c547c4841020315810014035101d00003041010751501020450094803407000410b4841341c1903564040c410200010895a40644500080da11800003141440b800204511807191083c42c695400303031039004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 752322023 1250 752320773 752320781
    0x6030c050304020d060e030a09090605090c0d02070c12080a080c030613090515040b0a230103080a14040603090209060a120221010513030f0806010806010c0609080307081009 76
    0x20090391040d04584881e0b00f00f0010600100c0c2c1030313801c603499908481d51401c040c0300400d08190300c0d440f100304071440c02800310217034ac0b29980401c3c4621042e0701005201c001f200100c62001080450050342c072400e40c685216024200d8004c03003e03240004110604214004005007110b03840c4d5201c0c4481541da08242001903c011981d8075005010061100d101030392a42200b51680d100f4410394107030035003844c50b084031a602110141c2d16000c04c0b50a2003440380f250b200c0e514001c6910816040481040040f1201a607411710000340914400162403004174412100e584030b00c00c14000d00c0c5d0b0313200c1c0e4482000f80504090981640305a00e55004a1a203140c80e146030021118894905c0035145040c2c1c003001034150741d100320844e03507091440182c0e400c481e00307110b0349200b8400d080058052000c0d90400070801840640c40c00148480750040c0300e440e80e00320440503408142403810040c1d01b00c6918100c0003030084c1d800c0003007030600301105129045400000ca148204100203850150f650b89009400a031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 752323273 1250 752322023 752322041
    0x8100506150c030f0c0304051203040303080c09010210090c051816210c02061602030c061602010b060d090b100b0702090403090e0411211002071103250603 68
    0x105699841080c402200d000180c00401995000d43c0d0915090b051401e030325034000c4104850b1074000141c24420f44ca002020400c8400002000b54101411540d0160103164080c0011132031000105d240b040507031080000034030000001e041032010f02010b20703215100300359601032948150107105400004000c01c480440c8070b01272010201001c4005808143c613000c0172080e00b999440001c1c900082c010a0314014a507814106034005c10207072a015040a41524031000381000315001000040042100060b01c03a400408480c1a041d0b40c442d5104181d005100c11980250040c0000c101e40310390300640c0d07024010703407405600001c045a031200c85410302d44880d0300030007103440014800070303000d0b0604100c1c2c2c5502610905182405079156489481c4800c400c5504458900008680700445c0c28401550100301010706116100210180001c41d2034221529030b0920007507000c11b10307600f030010103240140000c0d405001d8540791048a51072882c800042c00e41106542c0103070b200016464030031320070b400c21 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 752324523 1250 752323273 752323279
    0x10305271f021309021312051c0c02060702010f121118040c0801030f020d060f0902100831081c20090904050a0c1401030e01181205040b031008100506 66
    0xc07444c18400b84600a42040c0400d540e55101c05001156a4044c4141ca0510302d010b4402030185070800d05c1500d140e001b03507841d25010003843c4283c0c0ca005803658400d8030483ca0f4242819501d2041b0f004c4111100c80c010b49100f10a14203184191021905200041c61204606903d0401c40390154060200365412502d800700002c5400004202060b10b200d401003e261000300f91720702141c01a1145015145444185a05240d0b00c0020703408518200c0c0703044d800c0d4503031420080310600d03212005550b099440500e40d1400355003210141d940a070440c12160751142e01001d6180c440300c040b100f4001c15014200c2e5580c0d00c50cd440c109201036400c1d010b29000d1071205184a51030121044207000441c00702910071a9980b0079000942e000400303880484000d84082d042c04010041494001401e903010420861603507450240c00708103803589801c113400b40903000488002d010740610700c200d59500c200e0380424070b6035401100b03005601c814116203800322140c48040f902502c3c2c480c50030343c088400580340d481e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 752325773 1250 752324523 752324557
    0x10b0901050423030a03030501090c0c020907050a0c06021b1e0d110f0106030305090a050d02090a020903190503070c092a030209190509070518010305271f02 69
    0x40421591000e21080144200c41c1c5040888a00c004c83d140002c02d00e421004242c85000501200f00c1c03a00c07d070f0383c10080d145010046207100303030042840c1e90400703000d1b0010450001054141280500d00d614103860303001c84c00315500d00e02c040c400810250010501c42c1310f8064400410000d800386481c0010651f00c4d040640403405c501141a43c11402e00c0d800360310703e0300691503800d418920a103d80300c0154065200c0a0751010a1030810180d0000c0e900058468440241d10360056200d14000c10b5109104441c0140d035164847c000034901a640c0500e0056000c0040c1076104008000c4003910a2a2045003243c0d0820b40303818040f8140e60605d490f5100d0160f10205a11842070701c43c10103405503419040062515800e4404212103118030194003130740c611101c40411650402d18030059114072a0f207003d505040440628090080301c0410341e0341003588030004544919100b8090f1000300d580e0b00745040c0d00503902c00006407178080c0f400075810803004580d000c2001c0c440c140210b400242034098146 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 752327023 1250 752325773 752325779
    0x405070c2d050f0c13020f0d0203130b010f0521060708071119110111030307140405040c02011a09010503070608041104020714010f0b060706020703020f0321010b09010504 75
    0x410400c1c20314841403000195100400204205002c0e4000c00340e21a009454401501070600c0a51720700c10841c09542031042199104248148054804008800c0340142e500e843d81a42601a00d00050006e00138030019000016106440b607040c1040b190141e0f1b1541a843c20b00d06442c02c500f040c0d840d24000c035041000040c0056204a82a0740d02000e00d04000050030030101c000345c0762903285800b0b0000c400309c103840b030414002104100981c608091038885c20b0382507400c030210b8913400080c218205003c050b0a441201c00c944c402681c018000291040001c030701c1685000740079002404084000580c004102851400c141d04401c3c1600c40290040c84900d2421104440f1050001c105450980c0c581c2003240c1c85585900040c0700c00c5003d1052036010f003e43d2418142141c131114622900146824a802115114001aa01350641015005803038045a040c180d051840003100300c40a40000940d49141c0d9400c44d0740c1d80d40c440ca0a1040d00d000c0c0e030b2103440c9400b4900c28a1281c03804242c3c144010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 752328273 1250 752327023 752327063
    0x30115030b010c05010c03090209090a1115040b03070531050f01110d08161b120302120f090709020c0a110a030803010e011d0411010f02160b090405070c 67
    0x1002080320185003561054100c0d40f80c44c0d0840300720000d941300003900c86842c00306519040901d6900f0001c003602070581e8481c1950746454008042d10014090314283c400413500466086c1a40c00902d407030440303d59640740050740246103038440c6802803490b2610b200e0b01940702011410507040640ea0b00c01a001050401042050003c5e03c005564100220a07607141c0f000e007410b0281a02c000040d4548141605080c2c605195020440b64150304110800a080903192510081111066000b41c40740500701080300303081300644104000c040c00701d243e0385c05000d44113040640321480742030200180e074003042e1a548a98180e214000030b20300e944c0e104d40c60240100d030000e002c40350310030401020a4482c95480c0c0d20380b02c0d03c0e0026403000c1c00c0529040c0c0108046400881c40c5048141c480e428220285001e076202c40c01c000c00220340c241000f0f4500c0c040070b08540200603400b40c00c1c00701652100455950740041c4401d5003e011007900031401c0c04080382c0342600035104d008910b640646c00134840c803d00c020b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 752329523 1250 752328273 752328281
    0x60819081303080f04030201110312150a0e090601060914010504141f0f120e030a2703140f2109030c0d060203061930060608060a060b03011503 63
    0x1201c81c0c200304207140040000c0f0070400801c8140c0403507030119200d5142d0f000160080412500c600c020350002c0004004c00c00780041a95444103203048220046500e42000c500c4554a80d00501c0c2030510420601c80075042c00126141200d010356503044400e503c03541070410b4072040c003990601046040c001400007000101c801c00b01a000034000d007000d40407100c3c1079000034107401d42440c003150314400f113010140e038841c0f510003009240003814030410503a0b240320b958074800c450480b420051190401141d201d1105540b9040194200704c1c554425141d040c04420524140c01004552140640d41080c1a6000c10742c6100e118140c00c141600d1001e0500803c0c1640c0b1041100c0c1e40750007203c40c829007550300e0500001085004900041c0c90f483c2c80c070148500241c075141031491b0300034040f00c02c018030300c01c411229000e080d420700c00c88415a05156030521400fa0702c01e0007040141000004034840c0d50028401d031207800c180d0014421613541d070002c0c0c40702e80300c00c0c00344401110800305440301185c045d0300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 752330773 1250 752329523 752329537
    0xf04060509130204060c060b09040f060203060117010f0618050619090504090308041a150607020102151f0f1401050a0c0b01150320090f060d110a0306081908 69
    0x81603032002e510b03856840072a4001d4000c0004915482d035250103001b4580b0882140e05003e607600b40c140d0820b515941c010f07a0900701c0c0204555000000070380c0592080c5240c41c915250300a4690b40380d61214050340c0d8201007805840009800512400c9a01d0030300c07070b012011610060150342c03500d80c520041d009040c0c074110034501446403106000800343c8440c400e9003142806982c070403005050a14201000442c8501c404082041c0300d01448200340480c03000c6801d10208545c41996482280b0060303007020354a501500e0a09400c0d070410000d0341c5c0c50000b24103004400c4088051140e101c41003403201030954050511512000c005802440d40a08000c0c0382e03009150a01d0188102556110100380d02c00b40c01400d9140c603e40e0042d606290180525242e02c2804041c468054105141c2c134200d074003502d0304540c400c0070180d5411307441c5c0c2c5488040320003480b00c41a062100001c4c1d40f10502090740011910030000b0710b031600008405201080e40440070819042008002c0c0701600c1c1c0c03d0345070700700c50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 752332023 1250 752330773 752330779
    0x1b09040809060f0c03040609060f020c01030b030a05010e0307030f090b0d0213150306030605071d040f060305030d0506010806101e0201150305150703020408031204080d020309060610050f04060509 86
    0x202d10109000058044c0c1480d4040d80000d40e84e460034000010400d03091035000d81c0c2400f0312200300c0e00b0b03410780100c1d11280c1002c080c41c001503a0400080040c0c500b41c40182c010380554600b035510103c118011005000c0e40d030003500e80310200e0060805c00c07603108045104400c0c07066418011300c903800006030024060200e0403000d0f1444581c981d041404901c16091402c0c01007592840b04004100b0a4010300790b1004250624440b500c140c0c00081c2c40c008501d882451040703a89a00c90f03864081c150f030240000c0c43c0c210b07046a845048441c40000109020b88169000c2101381001036020314004905c0e034035440300c56980d010308aa01a01d10500440461400019552039009062600d1011030a11004600820040030450800b00300d42c030fa1403401900d00410076004110a1000003000811101c4814500c0030300d40344c694070f500300307a803040c0150000c4200c3c890000060002084c2c0001d2402c0c05281e0444446100d4031320b02c0d42c162001c0c815181002c0809a052000f0400c01d800f80001c0d1000c90310103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 752333273 1250 752332023 752332027
    0x50a06034502010c0210020303042f150f0703090306050a0c0f08150613030317040302031611041e05070c020f01141308030c160f091107140c031b0904080906 69
    0x25030300081200900c6c48070315005074804000c02040c05500c1d1030315406c03c4030720b404800e0190310115950207160001207043d4000c8002c0780c0081919210038045652400c461f01d00140c0315403282c40e0043c03015640f440b05030340003401c00010422140b11440390701d40c0301600340c6840480c0c868000f01600c01f02d41c01802c41c00401c40352120201035440d1500144030b0300d40468982e8040d1411490058405480c41ea540560841d04030108000641c000088a00107545250088034904030740c0f511440b101d10f0008040e40081c24041041881c92507109862665410500140559a03e2080840f503580f840200a584545810420603455001d220300307120b0036000058681c1f40c004842c60b00711010400340d01c86400c5520008140ca0743c0001448100541d40260801e03083c01c0d4a81003801d950040716016210741030f6a150458424003800c00101ca0000d68026490030040e906c1c20041502c4c0d50b00c0da031801d4003a0050070303001c83c0b181c0c1504904440040000302078614548468071307186210381141003256004082 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 752334523 1250 752333273 752333297
    0x9010804062309070602060105030a0803040516090f0605040b0108040b060a0e1006030c050c06162d0e0f1f141306122d06050a0603450201 61
    0x8030282d40002d46022020b011602d091485119140c02d034564044000c40d000340d001407260366004a001504150465081c648030b49a5007021403d2464480300304903403889080000614034440d41040343c4901c45101d0404c1500d550340b09000a0358501084240040c8201001034000f420040304175400480c090807801310f07c0c2e01c1b0250820340d10000e581c94940344000b03403000c001c4070fa4075002e0380c1c241520501e810750600e100c6525403552118050004000d10041601d0014210702c26081030500c803a42c0503c569045000511200354400c00c0006140040c255080011940c281070010301d903401c03000303840000c06000500c40c0c1e4411203507404110082004032000c0543c0c03030401034050000440e6540300140c0041c41c0010140542c81e9000140c0241030400001060200e103115400e100500c0d0b030f480d02e0460076000c0f0704003001000c2c1138000543c0b0205581c0040307480b47c1d066000100010032500d80d42a0200440a0850821040c003941c0d1401251100f5101d07504442c2214814121f10604100c000e04903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 752335773 1250 752334523 752334551
    0x60c03060f011d100903021e060331030503040c0807081207020a090608060f070201090803060d0203070902030711070f0305211306211a0105090105040306181211030901080406 77
    0x142e0304e000303d00107503001005200b5031070701105110002004100001c2e0b0b00e001d001c00f1441c81d02000b84409044405200b04c00324240a482c4c41038890011310a80030242c9000340b6021300541c0040d84c0c1540c2d404d081000210300600000740034016500003000510013a61030303c07990383c0741d64003214081f0382110444c040001c0721151409001c02802005010301074070b141c0b40001540740c1000400d5841160f04145210700402c4615003120f03004001070b100301d0b8141d40b007800480e142c85800c0c5d015a600910020400c0201035110500908940f0300300117403892160b94040110245c0914080900075800000e410015041c07a011000040340c21445200d0414070300f0a54202403264a0303204d5008a03a0b0003606888a0821501d10042d8502c40001000716a2418074181d40d10a2031300d584505200c00010604181d070b01400658004580c840c000740900078100c9140403031340c250074100302e801002075900c210901d4000c855049012002100550030058417800450b0521009042a2941c40d0f0f180385c8020205 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 752337023 1250 752335773 752335789
    0x905040507020a0b0702060609220510020a030e0606090106030b010c0c09060306063201030207050f0c0916050f030601030219081b0903030706230106090305060c03060f011d 76
    0x1c4a207401818901d0228200480302c600014403036011500013004102803642ca142c0f500d5088240c44001800c59041c07410160048540c4100c00b407c1489800704080201c42190001c02c4814019a03050001000700030b0440e503160f03810b403062a48400c0f14030052003000d201e070740864940c02051415919448494590441c94001c64118034a1141c07146002d00500c01d00c0d02503900200614007951075a0070611292010000e48030600c4411405218005100c40c0e01c40d405403001540c009054402c0c01c1001420203545214150803c1d0007444601c4c0044c010041100314062101d120381c4400745000c0280621103070035800101030381c0c18141c0c2402100000410245040300070201ca4031040c07100c5c1007a98403c2c6083c0300144402100b21810814081d40e501d012080c0c0b0183e0398048400f180202d07030300e4000303800c400b06022400040380e00b59000003015a80044800c040b01d0290b0241c41464071540c2c0c503402c09100440f1b60725000385040b25a8142d6510402c00c1803c41000d0141c01c0d80d10b1850040010825 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 752338129 1106 752337023 752337031
    0xa1406061602040b040f06090f0e06040b13060501061706060a02151302031c120501060f18031709030f2d0c031f051b0409020a09050405 60
    0x545070f607003003004500d4008100b1320074181c110001c00c004182c00e00c10080c105003480c480000c014a1071281d15542883c44014151030380d21354890398600c0201800c0d41040c058004a4800030826a1180b18081c100325941d2004a81c04a050ba0104190180c0414451801007000b142a1713038002800a540710b0527044591400d030354050b001c109110030860040e406001e4045904551020340010b404601c811391034240020046e0080041250000d000c0e100105800780580c01b0034030b0240004419000740c0c4681c09070394903100d941d0f05104230170b070011070400544045107060883c5020704c141d034000030b10070009003001729820a48a020742034508800035a4041c1c0040082c1000741800721403200074018080307a920805058144419000441402d100240f4040115004a0000b03640e1806641c4c0010014101400d080c0000300a501090005050043e0880001416210b030300801e482 = true := by decide +kernel

theorem cover : BRFrame.Cov 752158273 752338129 := by
  have h0 := BRFrame.cov_init 752158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 752158273 ≤ n) (h2 : n < 752338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
