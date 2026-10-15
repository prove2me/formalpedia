-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4056
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:26:44.615853+00:00
-- url     : https://prove2.me/submissions/5fee9085-c767-4b18-a673-ea775e3d1780

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 729316546 ≤ n < 729496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 729317796 1250 729316546 729316559
    0x15051006020607020624040e0f12070b040b040201020f060a06030b0f06090a0f061a090f06120a021818010503060a111b010b0603040b060405010f060f0e040612030207050a 75
    0x507281d100d5030b0160014141902d0b2800607030742c806c0c40b0110303101210781903500c0700805480d14050ba02d9103e8504004103003503081e00c0340503400c00c18a020558030f00b00007030003e04d01081c2d4424403140c01680202c100700c42c039261400100e04014440000b00264403900301030101143d0294050412640104c44010003922000d01c810841101075503000d0b800204000801c0e071248081e444440c0c1c250840390001a4030fa83c03070701a80c201c2c42520344100401400803030452220304044451740c3c031000044468615105030749800551b800006040c0c000000e17404200340b559443d882c0b0a03410701140040900022600701140d107140300f1024082c1c1030190080e200403404c4010240175004580341800103a034100002c400300c2d2074034165400c0541001e503403694080c010a4680c9801140582d0042850203000e1070010244000d841d81a0b0080f03801c1c05010704100f0034280d110641440c0c03103206280c100110880d20001a014104c160820005014204074200405400248000417520280c0b00b070300000b696881c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 729319046 1250 729317796 729317803
    0x5070f080307030806030705030a030203030f06090103050d0309020406050402030103080d0f0e0d2a08190f0909020a03061e03060b04021905030901060306060e040203010f06260a1505100602 83
    0x41012030310790003030106100182c0181c01299000e07001804880741f82c1d9490001a10308081103800342e000d41c20000038020401d107920344040c1d100304c0a84007843c05503d545d0b2181c1d03690020080b840300f010340e1601d0075401c40d55250480c000410004106540b00e5849082c44a11a8800d0746008400da00d0100540e000c506207008460440126030003400000413600c02c280c40c2180c1540503071b02048086d035442103414507100100440c840c010f001003501e403a10341074941c03550600ca81d01c03041880380c0d080340c1100955001c803400013a544a008003584801104d6010b6018060170b80001c0d80981c220000c001c84000c0f0a455141100e01540051144c00b0101e402d000807407044401183ca81c01c00c007807100000e5030140300116006811400001282e0340d981c0c81d00011a42d20f90080c00c03860b1100414031007945002d003e010700c0d03289031070001c001c0a03150004030a220141982440002461071051051300360051005445094211102d00e00519408140c44020b04080380c80240080f4808400300707400c1e1000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 729320296 1250 729319046 729319049
    0x1403070323010f09090c1206050403020d020a05100b010507050a05030324060703080402130c1718100519060b0301030209180613230c0102010c03021303020f03030c030a0c05070f 78
    0x4000a40d030541004002c2c00503002d414400c0d10300c0006e02030001014002d1180c84040349000305000100ba0500e85402410310b500c0e00884011540b02c200d421000c0760340421041c10a900264000506410810040e00c090088900280c200c4c020740c000c40d42070210200c0214805d4400d0b40750104141c0c030700c0465020040404024a4000b0005e120030300019010381201c40d0044d0008000310400c911095010042d05e00c2d800c9200000b91403424038000ea01d00310080c19420140107842c20300e02030828045c03143e0701c52200340b8086174180c032040400c180b80c51001d01d520110650b4601444466142d5041c0e02c4154030070f1101720b0113128050009076100c9400110010301c1402100a8200c540701c0810500c820344454200742e4201c40107285a011a01949504030a0020044003030421038040c0b80019007100c403006100b0003418010001c80840f49403003055031090300d80c11a807040340c502545000c01c0c03440c0900c1215800c18400007034980003141c2c00c0381d07405260b0752250381210680358a528101005203001d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 729321546 1250 729320296 729320309
    0xa030e150706050703020f0f13090b010516140f03040807080a05070303180e13050c040e1f3306020304060801030305160b0106121404050319140307032301 68
    0x10300c01c40c00020026000160805000d2130050306103c00a00800d209510802c00241c41c00400a441600182c480e41c01000515100804000408806d00081c102e4071695001070800c1d003007401242d080215220b14861241d00c1402111035088508400c103569502c540202002d6110b10b10000455640c00503241041951080240c0082071a50790241d030314007500030580c1c4091020240204d10070b0031002c900703845001c15004200341c003551030504500307041c8a6006c01d07001f02e06119100450b5500051203240700100b1a034102448450345480e08010560341d1342c40c03031a445050750b030b501c200c035081040c1000d0800e1034691800b49070707542d00099950388254031401002c00c01100042004c00c0c01840038181440c0f203500000700c1300e01c1d15070b1500382c42c1400b40c215001241ca180c80da44a007000c0762103481000300e403007200c810041c101340c3c94032566405455107419001030341409055000c0d114480d540c04101e1040c013441c1d1030b4100702d400640902615080d00d11001002d003450201d0340070103121141210b60 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 729322796 1250 729321546 729321589
    0x5090a080c030a030f05041206020304020f090603062802070b060a0f0602061314070e10122001301b09051c0503030423060f220b090a030e 61
    0xf095500f40e88142c601005042801024400001c0c008210700c102c0a01601c03a16005a40c0d1070544100040e60a41c8101240107001c600100003454400046554010103214450355044940c4007d0164480081c249a10102e0000c074182040000002915004103001c540e0082c40a03190300650b0300d141694811100145c8c07000d4007080c100106024503104040c041c15181c40000707040d01c04c01e481d0516030f40c4102d41c070203102d43c2006580004c0c8085107001d014040c880c900784000c02d4a40642400483e1003d45405a484c9041440c9a000e54040c65600c8a8140d148140d070076040d41100300d0781e980d00c42c0440d220742030076561066040341c44101410300c04141c4400c0344250500040c0110040e03440c6124002e86481c142134070109804002941c03140e40318511569544d03200907043c41500fa8415807114040d40031700140001d001441000541c011000540c441c44258020714107900000b1400b0060007280011080c4103c0c00404220400715074066100e121054100030140502040c0000300080d5018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 729324046 1250 729322796 729322813
    0x5070c05010e06071a1602212b0b030c060c150a23010f09020a050403110a050607060c0927020705071a220f0308070203120a05090a080c03 61
    0x6005003109503042d100600000d0070f1611607030741c1c807450040c0218140c9051401d40c080040080307400107007601c0d0114920280400050104040d4070b02e400501e50480c0d170307030340100b850412070b0324520321008840e2603c10701c200c403100744403072100044c54801c0d52903009000380d50701c0030f4042c1050801c681401886100901c20328035558841b0340884000b410302e108103600c032118074441c0000800500107641d5841c8180307801d545015050000070442d51b2022003524014885030610a4115042d18116900f100301840a118090001400c404090b04400e0b4016004030708882401202e50144187e8503041d04c1d85150a41c440a11079a02d03142c21807a9203503016007400c0070104205c00d802404009120780c003100c0009865407c20704200c1d4041403032102c112408110200401c03c0307641c540c50035051421061415609090816101403154003000d800c000000030b2110131502c0803c84c4600d803010520b002a1030b05415000207089502129a0b02e00c284000c203408a541100495001c40002005000702a0359 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 729325296 1250 729324046 729324049
    0x90315180b010623090d060908042601060806060d05010b031b04051b0a0509061201080a0b010e07020303011a0c010c180605090f0f01021509211303150603020604080d020d05070c05 79
    0xf41401b1340441d41c1503294800030780001c0c09c03900a00058002ea081603801d401200c00c0700d00c400c40c000150071940b03a0400c0300400c240301c00440c00d19003290301a00c50192049031810301c64050414036150a4142c46819010f10800b4184102240f41c1c800131541072004c5c0e150200c00d01c0340c0d0002a02982d01450b0200003403000710340180b004041302c0d8009403005040c5a148201120703400c0d02680480502c0c0c004074030f10000c0001c8900010301406900700080c14a0030311a0000f9070700c1c001401980f0391902d421203800d086c21342940603518681c11820084c080034071100c2e402020700c59203001030003001c5400341001c1010760180c0240c3e240050060a2101c9403c074240810031510a420b08032410340c02a000030240c10794098143e14415901d190080524440c040078a42d040c4023003085071754000a0230b120502540c00c0174000c4c8000c46e80c0051030817002e00c3c0000b180000a1295600003580000d000900045447d8040784240c0c0320240c7d60261144c20442000546152241c0341005150703038061602485207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 729326546 1250 729325296 729325309
    0x70c020a06080a110409090204110c0d052a0c010e010f0203090d0c031a04050610031e1b060905180403080f09100207060905060610090315180b01062309 67
    0x38488200804c0241d041c034800890780c2d200c1d4209441721034540d0040c03010350415020300e0908180d140d102078034110b210f042d036070380b0b4503070f0300c3e1584041050000705105403084010701c900812000600c1c40b1600c005820600fa601c4c0e13049010745000c01c4000000b94010340c0641a041d000c580c01c0e80103589049502d404100b003000404a08480c40c1e02c002c107010000c5043d00d4007882d90112401036550303103410301d414042e1501c03200070440c1ca81c1002c032050500005d48182400e0000741301440d081795007a01c2070314120002030015440c8106545954400046040d44246064100d80c01606d000094807403c24070810130310b070120787c05008500c000012450703a107a0380f01450f0f4880d8808007581d41c4103900a082c41e050341d002c0707881551610788840800050100074010240c00920803291070b2900c1c0f020050181902d0f50307620002d0030a003000d81540419800c2500071010700c22a1010203550009646481c0444081c01e0003494000744504411107519a055581c0244800c00c900307140342006100c1040011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 729327796 1250 729326546 729326551
    0x6090b0a0e28090b09160c0f050111120108031303080a03110a11010b0d2f0d080a020f0606060f0315041401090e01091e02031c03060905070c020a0608 66
    0x2c00803a00c10300200c021900c1002e6120350086060002512842c00e1880340c1038442c691142445410b0324018032000c0b0040002c0c0e5109860036040013210721786541051080c80000b213030058515402c004210b2000070140c402000e900320145442c46850340c0311034030281c0d05d01602030b0404143e8a02c11090010405076400307024400a603150105007081c0103100034659030800100c06002c210b8144101e010000c0c04e000340e0364215820f50310071402600944900084240038078484100038070103444045011788021022104110207404020300c0040c910b0170200950000446800502032401258040240400d509025200007880d440c2402e40110b882c0109a202504200c807488203200100040e07183c5001d5074100b111108210842c070740c541580101076403924601400c207a45404880c5000507030400f995010300440e02280c1562000c9880070a182c40d28100d080c403410b07495007840310301c0c5950581044003983c58441050109854881068800110341c0030000e600030b00d00e202c284150340c80b43d1003a60703 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 729329046 1250 729327796 729327799
    0xf0b0d0803060a0f12060608010c020c120106090e0604030f110c090a0e06150901080a0312020d060e090f010c050313061a1201050901270f020d060c0e0a06090b0a0e 72
    0x20300c007a0b460006010f101a103900400342482c1c9170b60401c0a2203a2486144020310f41c0d000240424607500300c000b03480e0041481d89910600c1c04401c17500408009500c11001b030801c001c420450150860301e9540e5540c3c04480840010f2002a01402401d10030a140d950124081c4028100140c04a0420080050007080c07801c10f02d50300c0615036400ea5041007120300503151040d05180c0050214107020b46190140c0009080d90b003c100c1000009a21404001881c0c1c1a440d005881d6130030208290301030407040c2d00260307003500c4200900082c240c0104103000d61035100d000030030400c150b0000503215400220303001c0040580200e84100071402a800c85a25184900051149242a0400a07400000d1a0840c80c0e01e6075440c000c000b10002c1c244a00b030741c2c81440e030700c100e1100c2c3d0f10300e03200103444080382d0401040c00026010840464a5200c80021066030000040c88405004040101813803c0841102e00c10039041c040001c116009505110648040c02e1280d031070030f42c131903405540410141e240103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 729330296 1250 729329046 729329059
    0x1407081f1e0e10051515040605300103080309060702010c0e040b0102150901020a09050d020f01050715090819032a02150a0c09090c0e1309150e010f0b0d080306 70
    0x20a04122540b007402c0c49448a99005e4002116030401d000b41591149103076900c1d440200000e20001b908202943c8007010116002c1c40000901100143c02d2004520308039826008034001004004050000e584039052003400c403440e95035500c100b02d0995441090a2003c1050642c1740d166030300f400d41142c80450302c180112180494001c09007002508112012000ca96001c50141045a44181448001c0408481c2c0c04000c2e54240c00040010001500d114148140000d110301003105408110b040158020400c1129210b1814840c1d6207a00c9804030b43c10580e1032072100040c0d5030103441460a4000184100040b01d003405282c0c45034004071483c4a01941f25400e8a0307414044100321562052410110200300740040d507101410308252034011322002414408042e0005a0116a52032007880846200c109009031b12448001402e50041c080c184c1616a00000f0010300980c0000c003c01c044040208108401c0b0201d81040b00d441030341081d88401090000408503403041d003d1504564010400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 729331546 1250 729330296 729330313
    0x50f0d05070303050a030b0a2619030e010e090403090e07050403050613060501081c052a0a020102120909010b0901020c0a06030902180708131407081f1e0e 68
    0x115441d2858950040300018000511240d44a50500401c3c100078030540340e01d0000c0f8101071842207420034400304a080f4441c41012031640b1070082091000c4040c01c509807603440a403a04000300070140480d94680801c03511060103507030f401c003807550350301c52500b580d1112140c90620354014135100016105104001d006d01c004000b0510521026010700c03004007000c0100079891401900780c030030503880140d40350040d2020007150010341c103d2140e414a10301c1e0140d59103c0c114000000c0b4400c42842c1d0400c5101d146d0340c0d043d00c2c0700000ba0169528002d80840f8160319400b580d40800c1c0c426040c0c842d0b04006020010009888108090b0007100c01c140142d40e0b0858030040071618001c155800704c0c0000c1d440d2485882541001c0722009011014844100c04526000390080c040040181c01e2903c100001174030201172200e09660562102002e03000e0f1451030b950703645a160340c3c0214401502d6076103060740c180c203440005403003405041020b400c650301440381022050001804e6103100c014450162222 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 729332796 1250 729331546 729331553
    0x80d0f0201111b06090a17070309031403030417030907050910050d0b07030b01020d0e0906010c021201020a030e030405030a080a0e040c1d09060a152604032601050f0d 73
    0x500442142020101c2041810f124000c0c41c140f0094405045038200107441e1012414880c02e103107010100c5041583e9865151034112190005580040e02100f4800080d0703c10300300c040010342c0101d00034210885040d405114440d007911040d1884a46940554010440d604080343d01950003a00342c403030302005541c1d45001c103c02c00c4120001300e4540b00d0840410a03190f80603c10344007204001e20041188500a41000d004401e807000f119209180380340003e40300b070f84074965240c011680030f08100c02c20038203038002740d000c0e400600155020034108098a4120800002a5001ca54004005103000b2903242c44840a580c445203e100800a00d040389100b95202d41c05805514407040d0340d0f04221545112090109130717000004103111303006490501846a0300d4000e0b03d01680c0b80d0f1030a10544607403003102030f01c241d0b2903262480d00704130a4400700650049145481031042e03029482d440d03500d50030820200740002e221407402c15840042e0340184910305001c0c0c490910281e0140c0360000002807070301c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 729334046 1250 729332796 729332831
    0x70c03050c2e0606050409110903010e010203060f0303090607060228020a23100b0105070c03051b03061603110c03030f1009060305100b06041511010510080d0f0201 72
    0x4000288002c0d8000c090040d284110740c116042d510071600030402c440c200040208603128521031117503069210310110519039107840c101c1c4c0c16001b004008100315800d07000402c0c042d400c00c07109280300301c00e0700402002e18100441212a8040c00034406454143d203a51410001d41203c0080c90f11019908615104038074126611044806179800800c221941841c111a204d940d00e094210f4421660345021043c4200003504c0b6007070084844089108a25200121094002d1620142003510802000414044c0105841c114081608140b042890b44102855610007090f90b20341118410820503030a600e03c26800103655940c454141071074150360b102541c1c5150020380d0700145503d010b000748200124540c8910009003261541406020328680300e01d80c50300d41200c0715030492134a84811660b65a0351a0888001d07118041811109002c0400e0080250305512091101c540c82d10340403940c1090048000000c0b920002c00408501180c035500720f07a0405100c2807a420366403640340c0f1400f05000c04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 729335296 1250 729334046 729334063
    0x1b0a0203030d0e071212080703020f04090e010f02030c1819060f020c0f0604030813050a06080702061f03030e01031103010b1e070b010506180406150e030106060503070c03050c 77
    0x60045503040209010b2800c18413550b11102803030074442440c41c0060030040700d4019510103070929030026600c100056019100c2c1c0c8803d056141d50004022903140c2e0b1341d078070816010030384800030054034029105c0034080b440180c4141410034030600c100403070900d1825170001e0003000039010803014000031410682142c5d2035040700c0b0100d40a40100c0000c0b9604024003400c224080766251013034640304010450301c0c822400080c1ca001c0700081d81202003034441140038014540600b80c1461940e54800c014859038050f207001005010b8000481c14500b10482c410310458041010680854619a02990100f1000d181c4505264441d4049000360107401c018600800d18524456070f48c03025103560300ba61000030910032944980a00c05030010940c03100030b49041d6841a13070380d640d58503400000d000070400d0020304e955202d070812601046070706854a00c81d000c000030762121460300704a00c0402d800d0310000d00a100c00541d090001400052040c014468194000d003400f074600a0921000b40c00c00028 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 729336546 1250 729335296 729335317
    0x20411030105100e0a0b0d06030c15080c040302090c160204060816080a1a0709080105190b030d02333603030406092d1203020f1b0a020303 61
    0x44010056403d00030110420006140760a0000e211800005020f100d124042d03004450400301d2483e07601100303540280090740e0420300b03503120b40c1c1e51548681e0841c801410b0200010310548003140c28602680309441c1a00c1e03001b05480844d9841216603040c680007984600340300704103090450003588840c03040c0b002400c080c1019044803d0031081c1b54080c0000d0758440007180d03000100c440d0104400d4001051441214003d00740c0e0f544682c001150f01c050b554004a000e54078020501000c0c05202007801215800e940003407143c00c450200300740d03c54911141d08400340e00518038044d0110794040d134900f1080082442c0040300c5c0300c82d0041400d52182240c0c800d5140180050194141001101391039030315240e0403001d210040f49100b40c607202c0c0030250006100644543c2140100301c0610b00d036490615980420141c005100608442d0b2030b401003a00b42d84807a060034203011407900c40d00840b0030a00180c00300e9072500c14050480701135002010311400762030042081241c0140e4090008048060a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 729337796 1250 729336546 729336581
    0x60f05010e090d08150a0803280903080a030c11150406270f0602211008010b0a060516050607050a1101050424111b190305070f0c030204 60
    0x500d24000030140c4060202d00c5140d12101c1c000203555480601a903005000b8180c46603074049090100f20000b1075904103040368080802c0c0e0484200c1d00300034455008a202c820083c1d002c1442c2c00c20380c0c3d159194000a041e244081160b0b448a50003a003151140540501c2d143c041e40030002c01d02802d28880711000200c502c2c92009000500180d4003031240d010b94130121240010185884c0305004100d8150f0080588c0e0b40c544200041c48404d03410749540941605d49004a00262030421401c0e15044075040b2003602650303004681c80b80140b01e00140d5140281044c2cbd651420a001980c403072f04601e201010328443e0202040002e0320902a440c090300c40ca0312860b480b510b0607100600855002c00160705103038034040400002c1400c60160071003540030080f4102684480780c0020014000c0e10001d650b82c0000090400960180c491643c20400e800c1d20680754a1031801030b420035699148140a40018000d00c00b502c0414202226180c449125502c401c52160784c0e40d002ca015200e5a5045210081 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 729339046 1250 729337796 729337799
    0x3051c060f06080f0126120d0905060901060e0601030207060e030403050309091501082433090f0105130e040804030c0803070215030702160b03070311070c030b0402010c060f0501 78
    0xd4220441c9a0071020726041c009441d810013850aa0001c02c4580311143c1e07101201808240c08414407d00c1000030500400d0340c2d4581008800402900d007042044586100361000034043d02c01c10302c035840c250707410b036002602680c549000440103900021010b50b02a41d851504200f80d020030030042c00154441d40103940c881201c46c0402c00b095100a2240d1603030041b51420400680e4003521460380001c076452540b0b0b420400c14625041e88042c0d49209402402c1c907420a000107120700c40c10007000205906080000440350091001c1307000e010251038000304080b64415056005401400501d5a0504030540b070f5959410004d042c000c069030240c0c7c3c0705070f00060500901c21400800070280101038004c610b0581d00c0c1c1d001c0346c0400c02141d4a11070065001c408204024820700031400368022400b0185001e07601c40400301c5065200390b07001c0022920301001d10f52112540000c2d02d0201344c0004003000348030b10710f890300c4041c04e20050049041151001f00200084e400d0f100e2000c075026a40030004056 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 729340296 1250 729339046 729339059
    0xf15080115051e180901180b011a070f0c080f210d140a020d11040b370206090705092e0b07031205092a06040305370b0403051c060f 58
    0x5074010010100c0b03901c10034007c040481c422030f1401c3d0445c2c4884500c1c02541034066200c0c0c0240c0900c0b00003d00d920040300c01c40040c030480364020003c1e2000c2409070340c140e0f0b4580d40d1080c0c0c0d8516180601901c85101d099617103007071080350080c0045c41e064407404180010400a0b01d01501c50441c0c1600c0100d5000c01e2003030011803944101c805158015110601c2e044c140500c2588038040c0b001108154040e0449035a00d0b03498100300d1441d4032448540601c00b8490801010352201401c030b031900ea061040c15800030306490022113540c010b0a084403c5a0240c480009410741c01010000880029000b200d0002c0d0f600e032000d0081c80420301a503243d07503c41d440d0380030304030a83e031000e49044a184d1010007a000c5090924196201910004145107410180800410f44030700035540050300c02e00500ca80204038426044044000d000c6001ca088030040446d00207000d009000003002c1d00b807500040004000a000c0c000a140114113041c09900340907030080c140e0141c0c0d00e139030444008040c038501e040042 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 729341546 1250 729340296 729340301
    0x301020f210718091e061401080f0f0601050c030405030a03120c0315060302071b0603090b07020f06070c06090f0309060e0616030807050d0f15080115051e180901 71
    0x34040c038001a00e5503e410961200400742c2c091500301665800b009890300f103402c806a5550780140205100c03075a640c4034074805000f1030792580c50200e5520000100c080d42054500c610900081040204a4450a00440d015040340345600c403503220800000c1071640e003c00003d54043d220780d960808010254803c0d809440301e0744003c10074542040b1400a9410344004100700f80d5205160060301c0d081181007031000c80e4034011041039955600b02d40030681c540e154011981c030a000b040040c64945404400300e0360f85075040103805032030b048400441d801d1840384441c1d0a00500680000c0340c0400c01c1d446403000d5080303143e000c501240408608008540e00402c05542c0c1141c00c0b6503190a14200c20b80607000b44078040310040400c00b05030b0008032141c2c00f940668120761a5000b0811400e030800d40d15800030407408120184002c4103d200007413491050041e08801c506a005080d0720520300f006102c0c0c1e410100422841402641200c10b1158850305461080d035800d98407152064240344401c51b08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 729342796 1250 729341546 729341551
    0x9131103190b01021e070b030a0903090512060105010305060d02030d0206070f0e060714030c06130c0b043f050a0b0c031e0c040302060f120a02031509060301020f21 72
    0x10315060162200550382c020031405180c1d81403840c0c5d4420704412840603420258503400518a0b4100402440090b0302c4607400000a03c1c400d4880b0020303251580e04010015480c0005004943e008000500095209400030b540100300600117003403a03415a400039060030745020058006038480310410800b1076114000300060364a90400c008000c5035000031461901c10860043e15403101e8030028401c40c1e40070801c40712031030310110640e08681806514035800d1849504180d54029020402051076030812048030304803900b025210024103529410300006400b04180560150642c0c50030303e820070036842e680125a03200e50054409021140b906910240c03025000be8981c6400f13008001942d00700c0c150400c114504440328154903540d20048801074405c5401c000d42002c404500407a0301c40301580600760724104c00c01c6441d003603603034034201d48200c2c00100c541d140e54404046080102d801d1a003000c03030b0048409400946488034a441c034044d503a01100030b130744501114130700040308061064240398 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 729344046 1250 729342796 729342841
    0x2030f040b064006060c1205040605030106120608030d0209041512080705070807180f0507020718090f050705100507030807140d110307030c020c06030c09131103 71
    0x59283c98480441000001e0341c11a1001d81d036101909141e41815183c070f0a038500c0b40040103005054075808020304103080481d0071150007110303180c1020321600860645d82581e1641e52141c0c01d503840d02c02d01701e40d13070916901c1021802d940c078000440d056005100400061607100000740c0d4850044041c802100c0888100d01d083c0b5840e8102840444082c26800c0e14450708220610384a80143c02e0641c1400c00c6540410142d104c0d043c400640d0350351144c030b603501002c1c04603810800b80611407060026207404032000e400680084400b4820142c0001c04500300288040c80007a08469503512284100044401a9141d40c440701007000f40d46400c242008480300c103880d15500346041d950b006840c8507409070800341440013220b6039140e55001142078411483e54041e0a1100840e004020701e025130068a9420000341042021030f03005000003000100088040d111518594036108540440d40240c6607996001c803e40c002e08c074540015000350007140d9248454681c0e41d080c0b140d41e46944042500212 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 729345296 1250 729344046 729344059
    0x2707050a0908032a07274b060f03050c0a1404090f020d030c030305010b070f2015090f0109030503070209060f040f0e0f1203220602030f040b06 63
    0x1c1c001c0407074441c003444481d0106201d09119020602d0b581e08001d12900074400c038000d4010b40890b0502c0c0340001071514050306804114065001c241f0110001e01c3c4e400002107080065003000011540d9035540081924100c61000040c1c1c160940381c05a80d0320f80c4c0501c0741c00710f48403405e00500c039060000180000e0100c517441049868200c0300c80703001c80301d0800d103803045984a1109050100e006c52803006164002c014004109645c42c028024910292003500002d1a00c00080341d20400b802c02c9503007913a0000f2041c0030784085555003d04060151301c46012143e03061800307410b181c4903035010300352946045030328580350030004d8188001520555012410040045802c0010443c0401240c80064060b118508143e03a1040812042c1d103000200e1038200c4c1c5004600c44d000c0340c0c1c550245107040e0043c4140ca10320160301419555491203000c4030303c04a0000c00104805002c0b07480a18010801040c07840c03055511501e41030102d81003180d526080014460030401081403c803400c50380b0002c11200c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 729346546 1250 729345296 729345307
    0x19350a0c08130c1d04061109130914030309100b0f010f0e010c14010b15400303112b1202040e01142106062707050a090803 54
    0x1070580d0790103060a40c100320454444002c0c0120100303903201610510301e0131560400340c076a4034040040b04890a4803000c1c41c189001200741e560301c007101e5a00000030001c0c0d80342d58241641d20010700e80300c1021038944c80c4510f01400c4d045000d0000d1841600050083c1800412200c503c40c19a035141081910884402907400345680c0c01080022003441c5a14242c2e00310340280006840c1c0e0540c02002428511503900540c2d8030ba041504038a41c03100c0252070748040010395500c035801c280580c0110b0107158a80c1c031009903410f942075070940301c1000b5181840c50030010200e00301c130300c50805810690014501819602c06400308114644052a000980c429012103c005041410756019080002c1095052190751124056010380d00504541000c507009544d48240b002c04940740c0b007410038000c43d0b1160040e06403401c212658240c100d04440034011554803c410025031040c060461821148441004174070528011030040c880c050030744620380c0e103a10402015100460560100b41c00d648100503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 729347796 1250 729346546 729346571
    0xf030c09030b09010f0504080c0c04180204090c0e09070e0c070c0e060f040e0f19050a020906010c1e0507050d320a0804050f0f0619350a 60
    0x194402100c0d0000320030b02e040e84581c1c40c1d071405020711004903c412801c0c9001d010a21040c1d00c01017000d440755504507600b40050307800340b0068030030101103550711580180d8a070300542080e401c6100f00502c00c9820301c006d81e489522507101e1881c152000781096215940500c401c0d03021072030154002c402003015500b0040603540d100d814958178081c04d10a21101c00104100d5203540c1090001c0f0b580061040c019005107000c5035549507413060b8440c5091081500010003422084040d1940c1c0d508440a400e52001a4080c400000c0d00074180340c0c10490305000c4a00854022031441e2082e89650f0400c500701502c5003480c13441c1c00307140c0d000548a02c188400c114005120a242c1650803080c4110b1002c40b07101009500f240740c1045100d80c031b600d01507071044c1020041d5607002001520000c6958000800d000020b2200a0780240d20598100d50100065080401d00814120503007000d4a462559148076544110b540d1654940c04002d202c2111a12204940d03040412940031034103810411100c0045038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 729349046 1250 729347796 729347807
    0xc0f05060f03060409050c1804110409050d050906040509040b090f0f0a26210c18041509020c010618020c0a031115010e01031a0f0a150302150a0f030c 66
    0x41001e40304a03038a05c050b50800c003060240b0303030040000400455824221406000a001044400702c1b4401c1034034088148914003441417441842d04000203081d1101c614006a48503804202115406002400000381c240d441d9600244aa8030900e40300c40142013190380c032841c007680d108210385c194110170382c480041400001e000c0001ca402c003035a180804c640a42021004120705000e0010344000200340c0340006031051011406e510102041c1819a5408416407250061003281d107420b0624681131981480d0030b4000c1d018180c8514000c840156627545240e00700d070b02150703080c202651034000070010901412000c02501041c0759007549006411007105494032403094000b018405000c0942d07411100410030a4815840c40340c1040c12540c40d102038155a0100b4441200c081d0801a903500c03a4869940c5d000f401111000b5101e00d031a215507003088060041c0019150301d81490304400005030755600c0004201490b403024856940300ca55800030604e1550481c03820905003004000800d169101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 729350296 1250 729349046 729349051
    0x71110060e0c1303050109080a14040e0c030612070305010b0f09010b090607140d1d1e09090a02030102182416031b3005041a12040c0f05060f03 63
    0x110b0030150b4076958609004401c51180d0070241441d0320f00070113242000805c0700100003800183c3c0360704404000400090701c00348542c1c0600d068400352900441c001d80340e901c1c00345412000c0200075642600d80041c00718581035075903106440681d1510b090204a0403c1d1050902007401500c0d80416581001c40390500343c4134100415010700341c0043c2d490203001c1801c05040c0801040c400340e07090f4106008000703003e240c0c0d8500c01c070400070044030210451306d444030103800000075458400b40074000c0c060400800340802440050140a000f500c0801a9420b2000702001640c20070001c003503c02c1281445400d140313901da10b10400404961140e1007680041c291002c1e00d521502201d050106403804442d10001c0c2030100c000e5044040c0c01c04200002c210b100c50914105814000203181e02004100781e8170100700311640445e80400c4184625082c841004c1255601c0f651111315101008000b98000e501c00c8a0560304c01d506c894092100041e0dc544030307802008126205130509503907002c0b0504a1001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 729351546 1250 729350296 729350311
    0x9080a03120b040b01390c14010c0201080a0e0319022d0a080a1701090207051605210f06011e0b040b03280222051c0f060b09071110060e 60
    0x1c5000350043c02d0785455800074a400342900c1006c0c0c40c1c914043e0b40f90300300340c054030395407512400c40040c0e5540f044440400e0150141e4804174192905c0c50b2040c000e11501c840645507000c10403991b600c007034088994410203200d9a00812500e01409111070280d48200d400b244207200340300300d2110031070000030f003030b080b40d0340120403540d64074800c02094441c01d40d0304400e03640132140c880c00098400c4c0300b076000c0d06a1034022000c0d04c0350000b01c46420b4126003c54083c00354401a1f50324a10f0318840c640c00c0c0004030b02c5a640489003100c2e81404d40794034240090780702d1032400074101080403102604400c0310740140500c403492800c00d401c02504180900008000700c2402c40c0300e00094100f045c0c2c201c100d04007201200801c55030340050444441c004803032240702114036443c5013400901d500302001c14000305401d140400c0c20000341a540c43c8083c908400c03050300c865840d20141525581c0e00500c0720301640c02c9803200ca034100000b148550509000d0100c640c0c01c2403510604024116400050a510410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 729352796 1250 729351546 729351587
    0x603060e0112150b0a03110f0d12270e06030f031e0309010f06080c180103020306010303080405100e0607032307030222031b0e070c0807020109080a03120b040b01 71
    0x6424184078010a1040100b0f50f10851520703000080c4440c20782080d681c00d40994031000a00d85060901c84c480309c160740024503000007080356181151060600d28035011204402c540301584099681001c3c13103850304025a240350035800e00c005843c0404c04840758034040800740d4106011081c000315804900d00c0b8020a0860000c00200f9162080d40030140304001080704004590700d5840c0070356111917003080d0500911807200d078806503290b441c4000b41201c0d4024001c0c0056030843e9022596150050000c80e9944941403114940c0d0110303000c1c055030103108c90000c006074a005074002f82540ca100650b0b5a040d03004170b100c81c03109881580d02c00d80c00f4610341405030f0b803850149481d0981c03100d503400f0381c0a01c0b410820080b040210f40c9151000c8400800d04080341c1680380c6000d0f611105050390640041000c804407440042e50b088050701e000c81c0141008141c0955510206085c0b4041c600114002012043c03001c000306660b10800e0501401550100001000040042c2c400110340021940c02c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 729354046 1250 729352796 729352823
    0x6010215060904021305040506180a1518050601080f16053f07090e0106060504060c1514071206060c02240f040314120306040c020a080c03040603060e0112 68
    0x417140050380d004d003c1c00b01010040c80c5440d0034410f03103c0c401a500c1c000040748170403c1203629280040c400181940000080034020381032030f1a0701c0107200500602c02c100440b101910086001444554002e118810151445044100d040c030304000700109a08050700c1c94a4061003562258090780b5024103813980310b03103203072045c004002611300e1450802220308400d00501480c2084041400030490b4840c0341c040c08482c2c8940c0b08982a91110f0040c500014030030710040011070f11482d40740342e0300347c000c581c410002c02001d6642c5c0706940e03001c00000600d1000c1d0f410b00000c0d039400001c2d01484a1800c0c0d0800c001403c0c5003004141003c6180080e01c6801c545400710a0f9884107000000480c1181e00560343d00e03100170000d9007098000340f106a600814101012030312100200f1b140940708158460300b46555502c0c0104002401d20700c2c04c0d8411442406810310000d04224024010070300b030107008584461901000078141d542c1a04451181030091004026070a804024081c08960100792542d050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 729355296 1250 729354046 729354049
    0xf0207150b032d0f0102030103030806090c091818011b27060903030909051614130f050301060b0f0a050304021f09170102030702070b0306040609020706020c060601021506090402 78
    0x20828103550304000d015800c41c0703c6055041943c149501d0148420346040e40e881c2040c00e800c0340400d01c00980464500c0002980500d80440440d61010139145843c0c245520740000c0b901b9420b0480c2900c18109a402c10b100714007404d10b81d01c01351f02402e840280002c41a08080c281070a0310101820284503050301d010758000301239144450b014031801c9030000019505e0400402c41c005c54031069001c03820504000c5046c460500032248100b107510031050304068841d00445014a8128081188100510903415684010032a0700000d0869841d0031065604040415003101d00036449000c8480c420000b100440d03800d2000c2e1b8200e1905414241d890f540d8030300101c0e202c6169401c40c140a99144082c542c0c146400800150954100300210541d0601081e1040c0c201d10007901c103c000341e031004030108604076802c2c0c001e40c0d2003031010303001042150790381012400380d0300441d004442c050780210b020052044100003450740b060782403009121082048480c454a40400340000d80500300a41c00034065 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 729356546 1250 729355296 729355303
    0x609130c0b0901090e0a0f05100807030b0711060f06030d051e0c0102040b03161d010c150209060403051e0d1202030a090f03020606240a050d09081306030f0207150b03 73
    0x101502005c56086143c030010000080c10641c01d03d01e031142c41d05002c1844408032030810410398210300018030f005800c546404c00500001800301d020080c07510142c0d01020010b00c40d0b00d00400c4401500c880c1410180c0c100750078150780300141c400700030041c0480c081d111060f0450301d020300b103401c400c2030340c420103109141d0180c45541c109004508001060000f08030a11003a095086100e50b16280b94032040b8110507198106481c0482c0020032140e10342000c1000419801028003165000514000c2d01801065644c1c005500030381d503031740010b40d10000f00c15004050118583c0500080c11103283d0b00702d409452401c0720003d0700c0c0110350100004210844550050000c190040c903191198a070519009590361011261036024114a982191030311020180000360306240c0311080c2d05000b80320004450540002c01c92803c880e44030000071300811800030080c0700c0314800840c01350b0494201031015090f02c0711100b0303a001451040180d640484d00c400460710040501c00408240d514150000074034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 729357796 1250 729356546 729356549
    0xb090a0909050d1403060604090f2021091c0302070605010f050418080f18060c01050708090309030a080c0102091206191b0804080409090501050609130c0b090109 71
    0x405140844901c1800400150304030203003401d0b80d5101d4802c1d00486142140c0c0406e844864020703005120600900599402010045e1100070700000d00b040c044000d5025000c0705803880d0340c441e44c0010070040100c3c0c4010010440700074107885c08940c0c01c0000b040780c1d481080c0032514860f6041741c0c000081c11442501254a000e40240d803c0c44256107500c840714100110b40304084c41289010403141e900d004100e8020764158011080030305041d40310b880b40103e40e01c40c91070482c14903c071001d100c5036039460b400605a41305406000241600c1c02c00405469079001902003800ba51050000c00c0380c5690000d10900520340c40700c043c9841d0708001e9015400b90003480281ca0788411008107210704401c002401078401c0406402201245070a125254102c0308610070144648104440d000d180e03602404083e600103200f200328901c1c16075146030240444210f440d0440b41651a0428407030309240207140c0c50780114240d500786070021110b83d40c850036208680b0541941c828086202e086681c05800e1420 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 729359046 1250 729357796 729357809
    0x306031c03020301060f0c03020607080603240a0518100f0f0e0c01091208090f060f030a06030227150102010f06030f050d0c05030313020616030f02061b040b090a 71
    0x3040308032025024019400034011a8001100d11021022107445803242480d03040e09600a0401c0d519030240859003203400921150f058801d0005840b00b0141400f240030540300c80d408189142e040c141d41e03010550b00080d1104100e10004810141140702c08501c4191050400034002a041419890304000c1c0c105900c1d1185114035001364a580c07038002041008000d83c0903a030346a10b094540c0301d0240e054034284005862014140a8810300c2c0c109a44101030040c0c00074805c0f0f007010724601240090343c0c0304a03244500282c40d008100110300f4980c580199040030039036010016840b007100c0c210a080d008120400c001c102071400c0405074001e5011541c006412102441001e071a810101e0920052100495580c85052105a04c0c035204180301a0403a6126000d5440c40d160501c6100d481004076070140d80c00f031420809800e0b0039002c8503e10754624800c2d00c440c1c2c9169551040a401c0c68401445c035004a0f288101455488108000701d9040c3c6501034400c83e2500407620114449040c07a4004a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 729360296 1250 729359046 729359083
    0x305060d12110f0316030c020a092c0309100e040e03030709080c0402090a170c0d0c0501030c0c020112110c0105090309120705030712030c060c03061d06090705030603 73
    0x501c00d512011044800881c0012100d0b03078500d01d0300c000c0d5203202e9100e540e0608003200d001400041e00ca603c05640460005010408054440b814081103a2450040b8031290221402d01d1010b4000e0300c078070071000c160300360213542001c0300080031442801c40181c0302c0c01009220034000ca0039076a181d0000c10781404140849031030345899a8040c1c8100c0301401100100d2054001c14005071078070380200d40041c0c0020b00b4180ca44d0345490920401c035441c001589a841c0246002198903844291040322000d01451f4031000d140e160400240444112441032410010b280c0d10420140c0d8002e560918080718521001400c506c00c1c50480b4194000c044191400c1c0d42410107000e4507600000c09809140390450f0400301c02d501c002041555031805102b02a0150017880003048030180f03068003101011300074105a03482525542d1407030111a0f003a011a40402c0c0c0c7e0341c80038010744041006515030f9120085184c0e0032410503500040d89020020101003c0150000000c1e405440a1207480398000e440c1464 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 729361546 1250 729360296 729360323
    0x3010212040510140c040e04051912030501060f0e0616050a0f140f0601060518060a0c0b01050409021806030a0b0f0103021306030b06010e03011b05040306050108030903030a0305060d 80
    0x450348032000210300c0f550060030444100701d9808515000d60089054840403407400d45440d43d4180c0d246002482661180580748600d00082c0f9408428500a4814025244841e031015400ba0407107206800c110104403000d0324900c0c00030341000307021021406c120303413840d00c07450502e908050708481940c0c010f0550085038480c608001d007064100308400d100700101c2140e08601030041d6a40c0641c0303001441c0c0da0b4004001040700b07501490090031040302c4410000701d030482c0440400d0352a405000840b0019007581d1404e07050004100b40b180c05000225028069451aa00041c1c144400740074200340c240344031408111030b40c0d0100900f80310141c0c81205100c40703160031501c024a441d0244800d0340942600ca40e079414803030180c41030401382c3e980001807003032a4490b00011102010240f02c4641c0643d601d00441c0c200b00c80b200542e68018000e6036a0b02e950320b055290200603550306131305c031005e01d50003401401c03850f6034040700f80c4034404464035000400350707582000140a0512002c000e0701e11070020b060f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 729362796 1250 729361546 729361553
    0x1410020a0302030a2007080711060a050703030501050301020a0e040b06120103080417030f180a23010e04110a0503280504020108060d0309060c02010c05011103010f090c0f05090301021204 82
    0x41c1d4071404e040d8908001c103e46151141e8019034403c81070408400c4100808000250032030084c1c0011070103014984032031b58104001c5689540400c0e1510085840030070002c08140c0e16000c2c40d030160001750001d6041101c2c2d260044d00c044031968030030b0f120707030380302d4000e00c1c1d02d900c581c001e4603c0d84c4222200c602441d40d41e41072020300b0394024010b00c5d900c0c1015000b03058962400008070b60103141e00c02e66851501c1d2400c440030b04406510b2103001c1c1e0bc98155000050a0704148102070502d4040442c07181d940124440003404104900d04071900035428891601040790b11a001d960345242c0500306107980b60f440e110009030031740d1203011018000520440300e120150ba113911440c881c910070b80b144103451720b851041100d0001c030208021b00194010805014061107481103408041c8107050010544e000c990b42c05081d102c4007400300c66050303000b000400c452488080c0246c02840c00000c1001040720700e10004041aa85042d01c50a00400142e04641900d007541190040c40801001d2101c900b40b03450b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 729364046 1250 729362796 729362801
    0x507050d06150b13080d0c0b0403020c0907030608010c0813120c0609050a020a0509060d0305210f15090c0f07020a1e140a120f050f16030201081e041410020a03 70
    0x303a8002819401c0300303000c03960345c40004020000c0a03403500c4052680038643c0c1d41c003802400c020310403800c40c090803000421544440100c94050705480d100419841c1c1440c0e0f0316800c50340f5412841d41003014100a001040441032150001c041d0010307001e014483d400c230001d4030340f42c40100008041ca840c0990040502c100499070340c402510032101c200b9001c0d82c55042103400ac0040d20700d607901c10360010300880024061001801f02405805008195403a1072100b040302d14000c44030030f01c0209800302008240d080d841c0801d0702c000b00485100c03080e420290441c1c00705000701241c0e4142c916001403c0010b40d602c841d000c000030407405140d0001c141444503004110011882444010b10403048040c081e0f00e07000702400241c1b000000c284502201c40c5d1281440740071050004e440600401d404414602c9040c86106c5030b0800b0951900803003851071000504000340101081c2c0d203880c810742e00e0701c14070011a1100d41c2058201565040d5240c1c800d81e003030f0400008074400f800c620303c0014046241601078 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 729365296 1250 729364046 729364057
    0x2122524140103052512060b030105010b0c0a1101140318010605040e100902180108030403050d05040e010b0a02010e19171828180b0d0507050d06150b 66
    0x218024003100c0040561141d440100380402000354202e034100004200b50941d0307101d8000d181c4429408020b580d5911000035141051054941584504002660741001d020b62401000503840c25841d00c5044440a5110302c0054001826102a82607414040c1c1c400e2028a620641c01a442c66481c20000d40403001410f065224031019401c0000000d8189818070070359403001041d4010b00404601303101010010018403c08130780c042c8951610324540040a40d80c280640202c5005507503460444c1040c920f0101240c0206040100820043c00350010701140d4504490a45030000e49805117804240e0141c004440968214030a43e4500504101401032540c0454056050a0141150410071096500c18001d4210921640c03540d041224100303211f520030416001084055400c8610042e90b03000c400300e60080c22041c03001c1d65040200d014503c01e4907501c160860b01400b41070b00b1690f52179194140351066030301ca12003d401000610616420a1443c104003001034040b650300c82c110000c03190043e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 729366546 1250 729365296 729365363
    0x9050a0903080f040c1404020f070813120f0605070e0315060109090e06060d0305070623060d021e040609061205210301270c09030b07021225 62
    0x4100d80032036003440310b40611703000180040b9860911194030851038107400d00321741140e030810030542e44940380c1c0301924219114000c000d61f2501007003104070000c56181c104aa00b80c605020b64000505c00c1240c80d1101a405100428a6a0ba4030000d0b01c0140e51440301607003500a40f8514000d20310060b240c0781c45410300340c9400348001d84905c10740c42100c5200d800c0302c560740c2c0a0b90101324141380c140e40c0c004896202c3d1a08a103002c0c60f50f940e5400fa04e07015000b4402505101c82800d11a0b102103070140e61114060340d6258800071036170002025080c6a038007003214500342d8031210815444039040f24010346003100d400d120301c42e40d070045101e00500070f003010f485c00d006040c84401c8d0131810203c0d60b40c060b428a0007840c1035034201b6004007040011000030040c480350360302449110f18500d024142024203180c44449801c0c2c0385040c4900400c900611050031504030660001030004c040040c0c03040b1040d0441d44c51401883c0d403010320410360340042c0c094010700d5007040c00100c4104016241e000c9890 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 729367796 1250 729366546 729366557
    0x902060f191d01080103110f100201021e0c0604030c0c1208070203010e030304021e01121a04061e061b0b040b04061a09070302070309211a0402010903021002030409050a0903 76
    0x600305140b88040419455000600020042010415031560081c941400601e1b682e0000c0780c03400012980c281086421000d0703500071481d2640f05050280c03d20f103006074071143d0b62421041f0002c5036111000100000c0500800400740c500340462103070420058040c0540290000c5194140782d84a81c0201500b01d102c2d60800c1100103e4081c0402070321700942d4080c040c0301041c0341e124407000c541d483c1c0382e180c503040000d100820ba01c2214203004103100341425011a1145a43c1142404152582f942015096041183d001c007815540401d046089130018a05001c1455407054011050080144003a0611885206000511070b140c65828055031103190204210845100c0342c0e4080307099070404650042a42d40020a801d0003500103248061103460103480031f6456074020302c0e92145511100442c0e2802418220420400881400e20f4490610001056280640c0000c060200c0c3d400300900404168201881c420300800542d000ba00074000144507901e8460f20290040c0806542640000e4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 729369046 1250 729367796 729367817
    0x111040f08100b0616060b04020301060c02091e190b0d06051f0f03030c050c03061f0602010203130809180403081b0a1e14040e070e030706120902060f19 67
    0x21441c8140f009030103010301504d04050310b1600d042070001e03c00c0000d0320700c0381d104c03d101c19103a51244010350280c41252174060a040395401030001c1006c0083c0010f030000300c0f1404009001009021840c0d00c60780ca01c10488107281e40700d60383d902520301018980d030044207503011481040802c1c0c001c00e1103520141d82000c1145050a20b00d00e074032540b84124800b140c88401d040c40403911034400441048e0042c02242c41902c603010220740f400341d04580202250402c0007610342980c2c41d40303140380c0c0100541e1000b5030035400c050003403510ba801c1042c002090003800241091150300c56030058403540c2441141e10506203014100034044803c2191010001c007940c4c2d00c1181951401806c2e108e8140c0c2c0f40d0f070f4120703070800c22002d5503400c80743e103841030300c140032200d6076a420885650009001808442083c25524280582c000d000b0345502881d0921a0300002000d21059901150050100d1500130300803a0007401400403403010b100d00060542c8805000803142c4402580301c103841d204008681d550031203070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 729370296 1250 729369046 729369073
    0x90f0b1222080d061212020c0a03030813050a2103060b0f070609050c040e010b1c0305030a020723011a032806020f0c06450111040f08 59
    0x30441040114040c45144541d0000c1003402000e0514002a210001001d90b103d02c8a0b5011076a580c1c42140d408017108003460782d003a41404003c6402c0c0c0b0135150806480d0940c2e40c06010440020880c19444c1c50000b21401403100411608500c281c01c400840c100744055034450400c48503450907400828184440016284001d1086410b40500e2569160170207500395100d101a210300315060300c3c40d10513600c020910b80e1340c034490b02014049040c00060b01607020340c180010a0030380c21a0b101e410307116800e00000710741c0243c210b83d80304001550069690b583d620304074480001c07402940401c814000100140048150312003500015000301c1c0804511240301010780c2d41d40e4010b003540e01c046441d8800001d0342d1440b410100c6862003900003500b450f46003003044880303130408868a20030390301c0301060114102640b41c0400401000e10700c3d0004d20010f00702041110842681403000c1e0ba103a00107610038000b001e41c09603102e400045501642e60b5626000c003040c08115020303401041c010007140e480c0e030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 729371546 1250 729370296 729370321
    0x1d0d02070e0118020c0a080c03090a080106050a0302100903050106150810080d030903111002030105090106022a0d0b070f0e09010f03121404030c0608060f030a0210090f0b12 76
    0x100c030f00880420014401c003051500103500710045680e240d1088850100000c6c420a0140600803a00ca005588a0040c0010045000425400484035034903100c42486240c41e46010b0100b0760360140c9101c0d0754201002e80c103d0310f043c0564000f402c01c1d441c2002c00b0495001d1039050300c400c510580d07221a00c5840d0100d00c00281030f00c92160680300e174008034101c1d115900070b07089841d003203001782403011590440211140c2440c2020b910883c01070307030000040c481480c1c00480d01d400362125200501542c20303040c1480b4102084212680c1c100950444070304244e580f00e65141c80c00f0b5a210f02c51343e803107080ca46400352500b80100ca4803130104601e0403041e00d450a10802040c12140329410b40c81d540c510b5a00e4246070441c032030000c0010000d1041811440d0449c0f0b01c02800103501c101444211189041c074010201a0041e1a50b4402c240c80b0b20b180c9015500001c401c488942c04903114685819401c00a030740304025603011700800d41c010300380010703c1d8175114082e15103400c90036126040742d0b8070020003508 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 729372796 1250 729371546 729371549
    0x7050403120f0e1c0c080706020712030203030105090606040306090f151806050c090907020d1202090d1101020f0a030305041209030b011a090d1b0b03010f06050309011d0d02070e01 79
    0x83c0b00483c40c240b0602d000c02113074114080a030380002d09580c0a85031800c1d00581c0f41c01040c0c0f9a80150410482c5a44c1000740b04010007400c0d003421422516940d00070f4591006100b0980b18850303902c00b04080c0d54594085400842e4407100401c180c2806150403458070762082c0f41640c0186011050211440d9240030715503e01003100800c5c1400c0025a40381801010f000c0c1011070048418415848291101352455005406070f030003c28180410304801400d9160034510300c0c205034010700a01e82e0f55112207000c01c01e0281d002c8036a4562040000c0100d00d00500d800c808a0607200b07118502c0f0515400d41e010034046d41c098503000850403902c00059400041c144002000e40c03040200400000d603500ba0f0300b855603a01414503500d0706e542c0c0400a080c490950b0b1058940002c0c4074180001750000403101c200500c41005158203542c981801454840054400d54042c0f103c0000040e102c584298000c0d0741c4e6058009510310800c0d2025092990b03242403c0900d4050320441e04e01080f00d500c000700450 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 729374046 1250 729372796 729372827
    0xe06091b0d020d020426210a0507030320070b01120f1e0503210a090305190c0204140417070b18030912030306031020030417030705040312 61
    0x52a206507210200002e51008035000f002e02e80c01e0002103207528030b1010710b802070000c0c0b500c01c41c070b083c6140c12000d00b0640c403201080c2210128560380140c261700f02c400d88030001c109041c644e0b160019070400360068052040340c00c83c40c00c0c4d140011a07042000c00082c0c09814011050343e0384c40d0380c84845981002040c05000780c100c02e400800407000070204a032038071040407000484030041c0d00550315a4078542155510780441e42c40b0440c20b900c40702e15111100e078070030400441880b440489407005062445030f400c5036064400300361155240c1c5806400c00c200d499a000c4c20812585850090010400c1425a8101e40c070030301003800000005200d8050721569a003001c2c00841507100c4005000c0c04480005032030b03035180024003101030243c2da169802484c4244107005160b5a280807800c140c02d001c00d00341242d50303143c5020b1180b8012050407440040440202c0704141c0d981e211030030310010a6120500004d0303501400400c0244170355009018200f100d2042d200003150300040c500c140c039000c00600c0f009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 729375296 1250 729374046 729374101
    0x7050d052e020a1e230d0b1c0605060d03050301090c110609010f051612201809071407060506061605071805010b220f0e0609 55
    0x3100145200c00741d8200d00030140c010007880e03503a100c1080990b084200c001c40030032009030702081201c10301c442e5400984058500a1300c4007414400404c0204030b2103500f8116801c010800240014a40c5c0c4940755180c0002c0c05019102070000d02c03100810701c0ca00d0b0454500d030409022982c1c80c10600d65007201c0e0b0354076441d15405c581c00c00301800002c001c1c0e151b10800304401c1d5201001000014080c043c0600d4100c0700205040310b8022504003950b03405005000150714902600b501103512070113110702c62900d42004201842c0f0114415483c03840000f056070395100008180e12000340381c03080c0301c030302d44070680c0c0015050340e84900590706034440803201100c0010070407401000030142e50183d503211100512040c240442c802c8140618901405c0454181d40b05120910102041040c0c0e070120514205091000e0760400900c42c0b00d500848010581280348071401306038a1101c0c4002101070315440d4034440b403660351441003a98169043e40d480d0301490a01e0007044c283e20007008822080902c0c03003d035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 729376546 1250 729375296 729375313
    0x20c1c0210171f0504050c03090105060a15030b0a26060a06030201090909030c08030c0d1415010804031101090303050106030c11061501031d0a031404050f090c070c0e0907050d05 78
    0x1820004611101440960341c02d0070f80402c107555544078950181480150080c0c90b072030500c00355402c40300080c04a034803400810000f002030411417100b4040c000b01c01e02e00482c4103101c0c103011482400345504400342c1014080d60418080d0150481e0340c00c0d150410040b1000c03615004240303802c854060102038000391140c41c0074050072209801c2007001902c6460900156030a5440e0a15640c0050301c02d40002070000980c032041c40058055a0b06003120710313500441609144100c42e6403203904021545c14004800c0c0050181802000446c5800a000000303010b00d20351031074010001c0c4024002c88020a1620041c0d40c0458800e640c515098542c6d0340003400940c80380703c0003c2034121401a05810152220740c622880389410b005544200d0f524002024002003500d40600081e041905000c14800144404c11040d80c0b00c0c060310b40000707070030759002e1041d442d040480380c00c078842c0c42c10292a1080c1c8580008071030060f001c400344603c1800b001d481d2044e0301ca000700601065400c070060000c0d80308084 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 729377796 1250 729376546 729376561
    0x60b18060d0b040302030c0d020f070603110417030f0a050702090f190e0f0a0f031b051c030902030d0809120f030f09010213060302030a0609050c030a0c020c1c021017 73
    0xe40b590098002d004a074100303c5c40c441c2080ca400801070513100160840d8035841c840ca041004010060a620300b424001035121002d042d10500441c4140c08443c419a0039003220000144120380d0b1442c002c2405a0f6601c403005800781c0146d10000003280503000100000301c412550340d00c40c071300402a000014111000036001400540400035150340c0500408680b44280e1008012482a003031007010128800012814081c140e103c01301c1d82a401e4207011920030000400104402030714041c22014500b03c8018600c08400400d0044d40080d058072072400391445c0c80744c0100034988504441e40c2180d0509510422040c0302d80035039900207420050a10100c1c00c0360809a0040d40d0203401c00000504180c0300314400c0843d191341d64031450110b0ba001040c0701c030021190081c1d801030030b540744060100e81002d200143d80341c40010001004590b94640d040788044c800d00129080d0310000f040046400054202582404c0c54070808038811156030b140c1d20822402010000401d151801100040ea5038484 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 729379046 1250 729377796 729377813
    0x8010e04020d030323101703040b0c07030209010e250203090f060906070c18020f030a090204060506030c0c061609180609111c062108070f060b18060d 66
    0x10011010703d07032030703008585400440e6501180203a4900c2501442e03070500c1b40b080e5055224980021190340d40741e90084680150001c2120200d568890301c1036620303520240214107182040c2c0009501c0f040100000072419012034025018400508000392259070b8426401c02644800031200d015800a0100301b03001d01c3c0250b052030004501400c1c0301c2c580700040001817000e034040001191020301e408014032004846003080c2c441e0030940c1000310300e400030982500b0200d000040100c41404d0b00e42a118045496540040c4002c0c9400f0305855140e040c6010808101c0c0c00c0440005410f22803031000402a0101c00c0e40d8400421440d00c46030720300342c140300c8030542d411552000d006107503844910004c5c0004041c400c400d10602c100b000280c81c0c5206505c52034258440e0f60710003c11508000050100c01d040b1460012105521a0011041d60301450108114015528081c1070204801990014840203400190049404588814815680241c00c07600b00406030381c825004126011340c42d00098929 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 729380296 1250 729379046 729379069
    0x609020405361c0f17041a130c030305190905090a05061c050d0e01030c08190605030a0602070605011703040510050705010e150702030a211503111008010e0402 70
    0x2000d071040000840030400e1910010001500080c0642285000040e40304842c016420310303948540703061b400c054980240042420030640071100440001c40c0009104807841007041d0741c0082d400c1d108540d2070401610342d420074490380000d08031f800c04200c0c01501c145100015940c004003616810f0725884002001000c0007442039401c00400040452403005491120030258803903002403090101c0c07010000c000910f0b9060041c1130600f804803500380305404c01c5040398005880d9500404001d25043c40c00c01500495002c1d903014001d0781211fa0520045800406c10140201000c2c002030344d8490f003c200034003c0442807a80f40c0c0050100b400a0b01c1d01c401e030401020060320b4510304111040e100c40c0c0c03c46105884209040c3c0c03001d50006c5a00b40e001f0113450b401180390000d542840c410f00d01c050490400f0380148000052011420790803000150b0003c1000407010384081c0b44280c880c07130902c01c2421800c041c1781c4030b800390b5800500180d21681c003947c182c440404144055072283e50a000c0b595110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 729381546 1250 729380296 729380401
    0x5160b04060605060c0a060617030d48020c090c0a03060b040e07020c0a230310050106091e05100e030c091303090905071407050f01090609020405 64
    0x58100005244d526200640401041040580b2100301c1da407a088084406540c01800c0c00c4c000c4111001e002030011080d6580d16000d0300d000728100742c0c600ea0f1050f402c010034808140490107841c070846003000500110584003500b8560344102054100281c0e910303100c001034154040c1e080d00000e0039505002015041850050a010420a8607105072074441e800030741114042e000c00d07000300191036504100103029030341d007a5107805401e420308210450712184007043c0744e1200f4841100242c1601c0c10840d00041c440002800c02c1556110300700207221010314031591004140c114039920341c2d07440c52182081143e0000700301030b10400d54544192900b10100c0c0c2c90307d0b0b25000d45030484285403a0010503030b1003110118081d8074880168075024041c1d2000303401c0f10202d986407000300710003182c100d00000e03503006407e180e1640350005460032a15144210340170100550910281000b00030080d0000b60050303108440030301090f40c034540003000240754044140c051042200e0202031005d5000c0300c0704c0002e0301 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 729382796 1250 729381546 729381551
    0xa03120c0807111314011401050d0f0501030c0621051f1e09050103170f0c07080d2606060d0e1509190807060f06031a04110105160b0406 60
    0x103558450304010307085201d080eaa00f034006032688407030f0702d04110707001d041d140c50785001c005580d084002c1c2215420705000c0d080000d8015407814415a0041065070300c520b449010501007948100d10400242c003003807101700ea01d59404c0d0004a011401502c91080b5400301496140e0307800729140101c0b01130310000d818001e40718015000c02140d04101001c1c0350242c0a01c01034052114064118011120001d42c4403030741c80c900d080010f00000d0b0004801400c1140020f0a440d160240c6d0000c0045502c9080318070314161007220800240da00000c07600700c40100340c54907003600805140d4042003041c9a42450200340c0f0f117030a0001030207840c0040c00303030900f2402c0c900005030303001d03901c4002894502ca10b0060744000021000f04194804204129402c0c0c0c0600c42d14107110307003034507a20300c0481d011382d600c000e00b043d44406480300020510b9200034019030f00007035485d9080158080400903405e080d20159041044080c1e51409075015001b00c0c0e40d1078000032100362000419494800d119500580100c84894 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 729384046 1250 729382796 729382817
    0x506010903020414010806100605120402060909091b0a05030a0336030618330c050705060714041a0c0f0f010501060305101203020c03010218030f0c0a0312 68
    0x211a0304c0741ea0213841c0f030105007403003035414005030a20740640141311540c0c0c1c480030001848034a5000c0165082840800c0201e1070035141c81c40002c1c51801107008254110b04114200070029000141c1e051a9906184a400c14a180c84080c0020981c1a010340d907016800403402000107407044160b01704034000301c6244d841010307501215001010200200001001c1c180d503050040c03083c0d6219805250102045e2540e56442d642e490a0040281100031414880300c04082c1c1c40000d18000c4500551102c10810003002495450103007041d0007240081c0c59600c20000010b071140e01030440751400c100d10042d1607081c107140004c50b60042121f525002c1a10384103210050b80c1c2c0900300310441c008041c110150040b100c0003107000742107820503442142054208000e0151242611000d442900c100600d9842114041d04059180042800035190035610002c0d62030702888008e0b8008501150441c00e0302c3c4030700c0302c04011542c0d038200e5072002940310440310740800001e840d0030b40039140ca411030f08080c900d54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 729385296 1250 729384046 729384049
    0x51c020301050a061703070c060503040c080a030f0e0f0918031b2a010507150213091e0504050d180b0403030201020310051c0210051606090302120f030a050601090302 73
    0x40da8183d030000b404507112103041c40310020400d10b890988182d00000c5041001c2ca03225480381e204140700d41028050000301140500c003210703e07584054003e01c0b00b201c41200042c40d000b0240c003425100344000500ca19942d441c0351400290414804e02c0c0245040500d4a0f4407528a8402086018541e101e1108105980c003000807940c6581b044118680906002406c07040100340e003844003e504042d03c1e0b22024800802d81c2c21209485103690441642005c02032501c1d030200091041400301d014000003160700185a01c11034120394032000146680c40e22400c8540543d005641050f00d004101e900000644800241302c0c0710344284402108003854140c558465140607170764802d42023900180d4000080001c05100101600700400040c0c42d024401410310400c0d034500010f50744020720075100d08820003c4203102c2d20503690305205401d5698a200c2d081d1404400030000e56070110b0140c0a02c01d0681a5404428141e510081004071543e10310755807031550500070200100110b05018542c080800903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 729386546 1250 729385296 729385301
    0xf040e06040510140709260615030d0207030807020915060301080604030e010926010209221103010e0a050a020d05161107050307140301021b0d0e040510051c020301 72
    0x142c1c060300c00341000d440700014400950790fa020020005030044000e228040b5408071510381101d40c50351000760083e544d00410490340c0756858024843c2c1c443c031000e0003200081041d0781410200d08900b214114005058140c0c0c441146101c0540061401c1c0540c3d0050b04009002c298000065107591400320f1240e00001c02540003078200400310361000d01004105134004c0f1205004030303002d00303006002910f0910060a201007080e007000e0307003501110325185407450940648500700070044c020015001e03510315404110000039101c0700c84030300303040b0400100a010411a8183c41c0d10501c0405070340c0e902503026014010141441c00210b90030020002010f81c80e10070301e07014100c0400e08004c024008600200041c40e2094591002e0700102020441c5035800a060303030844010f250b101d060ba541c843c4c0003d0080c0070700d0103010410b816141240c200554081851000d005081d103801e0210300104c41800202d407022200b05510464449092009140290840c0210380e22001c03440d1140c45144d010909 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 729387796 1250 729386546 729386551
    0x60324033d050f150a050904020607060b040c051c0204080606011404080a1514090303130c170319030b0f133801021f09080d1401090f09020d020f040e06 67
    0x90f0741c1001c10030700030062200d0f0b241c440c1000007181c10030300e0706040200090866401820080c8502c0c2e001918800300080c030741025004900c0204108048421440090100c0c0d00c5030000c2c1e040080709a5035008905801d100b6101a43d08403070003040785944603001552201460705c40d4150944060000040d00e110821404804620031103000c1c0c00030b1802442c40b8140c52000981141c0020400104145840b0001c256030303210b1064454610070180c5828010b11310385150b08100a504600b5504d0400b0840000c010310584111758a41c074820075920a0850450718030440c0310f80d000954040030f044925104005502550104000162412800e4a44002840b900750309184040400a00c103650145882c03808140004c00e0000d88825038002038100402e109076010f91134490b07603400703032081880040401d941c6c944240c040100302c107501c09403011100c1a0248200703c542d904010700170245100c2d07400b072402400c1d40681039450041d065400c015402001001c8a81c115941d01149044030b501000805d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 729389046 1250 729387796 729387811
    0x1509010204060905030c030a03120b040e010b1215160324060305060102012003100302031b030601050d03050a032409050118110a080a0b060324033d05 66
    0x681d41da1800002506114195001d58400e40000c0c84130281030300c0106004041c030313601d841d141c41002c0400501d000203040c900f01c2e890f0001e00c0c054030414602c20541c4501005401160700c091141048501c15584ae030703044500310340020500010444002005903010742000543c10089400001ca00180c0d08410900069076810079103018100145a0144034030b60300b00d0002c5c03000340f24001a800380200740250041c0c4542c9070040000006e004d890f2100780d0340d005154018165900c0501c002c00c04074022111084443c464002c0f1300c00080d4901c2d1241c44035422903815221241004074007035007036000f40400d00c40441080e088800e007034101c0071510a02c80140c800010005020b5042000c488200301c00034158a2540d0b282006041c0204042016140c1003102458151030303d81c0c80c070150002512961203050b4020402100b4008000401000000001c001082da8040d0741a00d20070141d0f100c0c04540014000120005140c11108a000545241010340040c41d5851140f00c503c682c22a14200c4100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 729390296 1250 729389046 729389051
    0x1120b061608190305150f0303070b0f010e01061713050c090109090309080109020d0b07090302040f02210c0a180b181e0907030504140109080417070e0105060c150901 73
    0x4643c16243c0481c40815a40e150810440c07411040028203071142c0301036039100c0c0505465030300b0b20750380410480c1c039840d07802070740b001140c00c105030311f403c02c2c490038000c0c503880700c03441400458030340e10540c501c400c2c540e0300f25550704031030303e4484000007502200c500c01d681038002d488143c1c0081d1a080c20b020700800e4131040002e00081c25040040c0000200d400003031403079041001c9440941e54140807802e0090b0080d10052040d2910b4005072406001580000d400038140340240c40c65080d594045d2485a043c1221140304184494603040c40010071242d004040405102440101d44203a40d040d4010600c490070f40029501e50302c0031003180d0002c100e02a240c100c00d4845005c00e00340307203040c528040c10214040700c0b03280c4a280054068000205040c080503a06e000040c14420184541d4401140000c001c1000c2052402c0c400425480360184803240000c641c4100101e5a0020b5103100300c4007030403002e08069003030101300070f4241c6c400d001c042c94038440c1511030b41c40c9400d5018920300981e083d1000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 729391546 1250 729390296 729390307
    0xd1407150c022802030703061e110406090b0703140d0906020c0705010f080702060a050c1c0f05220809030a02090f01030b060a03050606131b05072001120b061608 71
    0x1824115003100383d40c200400401c1d9140070040e00d00040f540150b03640a0004640d07403048500c1044c000086c4103c0110386400c0030900e0400c3e0545000500a55400380e941c10a00c075129098101030f88102e8000a0000340b25040304160040f400001d00720b00034810801244200a80d1031742416600292846002504003402c1008590303001075140900540c0c40c18821583d150a120107519211700400050f0041c0d00c2e1000104a0400340c0c0c100c03a541c4c030752030b03203859903101c410210580240741c070724160100c040c030b024040ac0400801020703050410003c00c0084011407550341c2d400c242500070030305050f007512030340740c007400160380e00c10f0703076034820301144096546039891400c02c114414000740866000e203040d00810300200f90007141c110790201c000d4034200c51a40681244200030f000e0b14511210509030440c80c02e95080d8041e004001aa000d5620b00381c5000800603520090503c80d2003017408182000b6618407601250780010754000c0000741a942400340510220030158022101260301c1a400100c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 729392796 1250 729391546 729391573
    0x908070b0d0b04060b07060e011e0510050405150f06070209041401050f04021809070807270b181503100f0507020a03020c0607141015080d1407150c02 66
    0x280c0c0040b80c0040381c062000c01d2030010750b40583d204010700505050380365607203200c050a00750060310440c07050701110003110698090090081c0030030b4554105100e00d09400244924050103840c0c000c200b0b0b14400084005c13210700304000007284841c0e003a0480400d00401c00941e0711286e0a500c142d00a0111803004805060b031142119801000c43c80061466000e00c005078580000f03051071303408860401710280c6c0b190340d0340d2450452240d0124601c0d20540e600400c07200e50b900401890315008a440c0f6180400c0d18801c2425500c0501a00340c00071040d5030f0503d009400300c280c090300801c034103030f20000101c1104042410103989603003081d44140c6605d0464260301042c0b00300340d070002aa102030010080103580080d1a000e500b14918450310780491030406120940807515841d91002d4201d6a100707046020003c064403007410308003079480320203400043c3c0764001700d8441000c9400d696200426201400f403207071644c10148083d2413206807002010041d803000d200d8102c070083c0503001080d01429401d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 729394046 1250 729392796 729392801
    0xd0903020d030c080c0906090405180c0901120b130804030b07090b03041112120d0b09071706090439080c0f0d0326040b10240908070b0d 60
    0x89410081603d0a001d240d04684e01403c0250420954141296a403400c0000101a03014001c035070381d44136180c04180301d000d102c40d02c24481c01f0089103040d10088424002000a408024451041d101d00000782800015251948455101130b00e492095100083c4c2c1d2a6a00340360841d400446121000b901401102500010710000500502c0c100d20b01d10b01c0c050352040406001410510301800d040044114401c0341484a00006202c206a1a84a07000308032020007428141c0702c141c0c0212104004100356a10443c1a101603c1d108400c1003500e0f00c0c2c0c1d00900000890081058035020118054140c40e83c00341030a03011900c0340340d040b00c1007500000701c1d490400c4e00345a10014042e4012001d54689840d40706500b8041203045400061840d840e05081d80e565000c400001c1c12414400344d9491516086005640110b000b5010383c00d0304d50702d03074605040c5d006490141360a81c40714841540a03110924042001c031490a03c0d00d503076101c0d52440210b1500c0c155030042010140c0120340000b4690700751 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 729395296 1250 729394046 729394063
    0xc08010f0c021e01061703030f07050903151e04060c09090615050702061612021213031b1e050f04020708031f0b181002010b06030105060a020709020d090302 69
    0x40080003150309030840039603104910030f80ca4000c1035851048203400e01003907200d44001c05c580da00e05601030407540c0da040c0d142c1d40101c99460b0600000d001240740648900145e44101c5006801072a000314094000c64017a1303401040005807844038503003055102514000706000d948035a07400306901c2c1185102500162154000b48245450036204200005940d04411010142800c206c0c0d0345e020103001160b2a4441d2000310048400152515010000441654000c1200303d5003540d04259440043c080244140590b00040c60b11060003800802c40350050340d000c10500035040074131542e50302040c0c020150456902c80030640b03d07680c10130003800d05481071100f100c421a0214540007160340e070175225003c05017228600c50454200400c60001012102010b041074a008944410a051002220101100c081030090b80a004000500c6005018207038072040c0041c0b906007076030b09001c1480815003090600c0700452060010000c0d20081d58801007017030b0819210b0108400c0600e04020385080002e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 729396546 1250 729395296 729395321
    0x100206160e010207051206060a06080103020a150c140d02190b0106080613020d0906060503030c060117010f1803020106060513060302090a0b18030123060904020312070c0801 76
    0x501084a031084109000d8260062824a80c81c103150800040f4900100341e04401c0c5c011101c0300180c3d0800b40c0001e6501c1c420380c03080342c1202c401912094203c0d80c41000b84002900a00c0d006405c0c842c40b080441d00c040300c5e099502e040600220a602d5150711503480300701344112034205210300001c883d4103000a41400722814842154010595960360034000144103080c1001110404501780765544100e004601010b90f00a40d2142280b40d040d50040081400c22249280b0384880001c0e1b6042c00300540d0b1108a895000c3c0c030003686002ca141180030403e98000070305558070303082d0104001e154440c54001d1070f11041c445903032944034074019084890030341050041c05000d1082081401c44035043c1c0d07080ea6031130b00e03000d80c4a5501601007008076516401a041480e404101d00e4612403142d0180103604400714020300c0302075001801c00a46000c08010100014402000100c01d070600317016a43d0800d2001d01121180303440800305030125001004101d0303640803074620801000320300b4020513406800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 729397796 1250 729396546 729396553
    0xb120a0201080a0e1906020901080114091306110409021206060405030715021219030f0b010504032d0f0605060306010509160e030601080307150b0f12010216080403021002 75
    0x4140d00041c200d0440100300801c201d8584000325501c074418045008400c0503008400c0004a4500c4c0903400b941000c40900d0001d08100000140100200020084c44801030100d007000e449041e458040c01c9803500d4260b50094442c0b050100d103488042c000c00040c00180c0340113884407a1840e41d0035007000064021403141c9018041481151b4000c12101e046447c101b02c0c0421030b500c2100103a08082404805442900e4007080d0041c4848c40310007000d44a10700303564100300c162861304481040364103400603140094001c0c04107200156241200609072501c080340030301118440782292078624070445048400c2c10306007d0b10020001315000d45608800d0450203825698142004510442c234000c02c2050345250449003a442d0380d0164030170847c0d0400190545151750385032013140ba6030b544105000c9030841401b41c10f440c0443c003070348904500000014039140d454125403080010f091030608600d0b00d655420400009000c0c024801c41c06c1040c810340b151074691b0b01d10300400003c1d20b103c4103008190f42 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 729399046 1250 729397796 729397813
    0x501030b12070620010203240405040c09150b0a02010b150c0c0607110a06050319150b0a12020706050f071b1209050a0e0115050c0d030b060d09060b12 66
    0x20404140142614030324030b00703130280701c405034100290712150b00d030250407030b510002c140001c0c00c044055030503003100482140c3c000c004144c81030104483d01110007400c6001110f405100031000c80d0040d1203030075804501ca809058840520101c540d2180e5011230160f9580c1d0710b07070052800c00130095840109a021114104141d03504100d0300c4241c0400c4a9214400009044082054214004101c0d40d00a00308081d510313242c5001401c1c031f500c00c4d652007030103224903140060361034640c1c0a034641e011189000c000b07440d40b5018803202c3c150408403410007031241004010800c4607291002d400c0c590b0107171201003450f0620052914401c00f010303242c0303020003070703100003031030940409044450100742d01c5035688444003d040c03c00c49244900e6000f05511070300b203c100064040340a59901e06980c0e002801001c904400001500c0520440d200100187c102403007110681d030099020140c0c02102400c10352900c03d0b6451a181200c40c0c0307102c21100d0b1540c400c0303401424280b14070204550145a801040c1c10b4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 729400296 1250 729399046 729399079
    0x50d051b0607200f150919150f140403110d0204021209160e041212151806050102010e0d031512150b060913021b030703020a0b061518030a1401060501030b 68
    0x62040e22862030103440347d00b07103007a110044848180007d05001000034815034110318020881c250610b5040300080792000713844c1c900c01019044a04499009440285400303409051100080080400742e0b4829030900c5051020006c205906100303c0150000d840328101ca0300f003401c03850803550007030380c0d030b075580c2004000009128210f2184506010304050f40c0c024044041c5a018240c401c9128110302408540003c64a805400d25824446d00c00340620903192114012801c032180c00e200c18005902c507840c080e500d18065480080300e07828044560708103e444500402409079041c0040b0f50118542c04c903c034042c03c29119600300c200046808a01d846980da000508110311a80f18216a80e40010505000b0f041c610b401040743c1d100d0b03010741e61105c5142c1800782d2140540001602e924602c0c0700002d0b89868542c0004000a09410300079042c4032180815540702c10726614400d405104a00700f0601241c00ca08a0702002c1000000109a2504110006050700c0c10041d905001349442151542d60 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 729401546 1250 729400296 729400339
    0xc050610060e010e03010618020912030f12090120071202010606200c031006031502120a020702012303101a0f07021c0f02040501050d051b0607200f 65
    0xe402c82482e10345194079400e00042d006101a520099a03400e080214000061003a0040d0407208400c075002000135101900954803032003058000000e40e14100f0010401407007448070b268002200b50000a24130880100001805c86c440211498020380801c1a40421845580400c0300c81c100d44028050a4501503010b4000032103034406410506400c41304100382641084160101980202240d680720240c034207500c01841240000d56400044a05c12002280c49000721410100c81200780400c1d9945c071652031000f9000303618101e0410a03402d031000c0d000c0391081c0b450300d0b21030910450b9680d0386c1001c1000d509501103503481000072891061050700081c8217202618607812904175801d41e2085d20748005404040003e103c04103a0740922500300500c804103202050f054800c1d102000075988850402c9444000418020490791007000c00319105c00410582001611024000c0c034103040715684c580070300b40789040d0345448002080c00807800c1440c0800711068603035002c1d1072000b008031041d0414002e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 729402796 1250 729401546 729401567
    0x1404050c0a0f0e010c0b16020c0d0302100f0f02190e0d02131a0904050115061b060b01230903190213020306010519021c0815120a0209070c05061006 65
    0x2070000c800300f5000340e030340110244a0310550214010101d8501200001c40b40380100008034014070402d00006224100340030a064010303010f0b001014800640d44c0400302400e07083c1500002540c80b420000e1207482e650024100000600e003031011450201d81d0000c0200441c00203451050200b00c0c408000350321908803000d16084184000700d501c03541100404001d0004854254012001000300011f0110650189403803548001c108013216650303842c1268542c0203061382c414074012001c01580005e047d540888006881070421103480d4803030501506040720f1002c00207036200d10006c0c80c90410705e0248100c0c1005400c032070640c603035000c2580125002c24600c446075810284d0020119280344e005100752102c091010729000f411f13851300c0d8002515070010200001600340c907412900810303802001610700c14481c0d1081d10704a9641d00302001101e04074100c41d600300d4040c5425110260b1141c0054910500003038503810908880c61615500e0024000e04038040081031403414007249900010500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 729404046 1250 729402796 729402827
    0x2090c04050a0b341b06090b210c0d06091407180b16060510031106070204060b04081606050313020d020105090d150b01170615070c1404050c0a 63
    0x5854504240141300b640e4020351490300c2481030050302c0420741502c412043c82461244940318801500314002091001d803d02502d00400c0841c081800726201240203880c000011602c138100064480a042c0203183c8280c8100080e8080000c108054540c5c60007040c4c024034926034100100300f06016401181e10f8003919480402c404d202c1101400540ca50b14a0003070700c00951b0f040d81d1104e0440445a041d01c8105c41103a41c1d504080020b58001c409564070380403203030880101070140030420304014040d030042e403013203a210b5500c41020a2200b1050054805010b0140c0100b10300400407031201202c000a07072284c800c02c02c08101304103400303070709580c05445c1c1036042d2034441c00072041e0310060b2210300881c10099048240a20f203141403040c01940d800c1111002e04041108092010044440f001c02e461121540d82c540408603400741411040713208409180380c03080b800c100c25076032881c01c0d1481703a611101c0d0355884c07015580c009240c10b00c07856400080600d42c1c58908107180d43c1c0034004000010020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 729405296 1250 729404046 729404069
    0x2b02070f0806060913170d0c020a152003010b070b131a0a090b1501080612150a020912030c2b080604020f0a0207170d05040b0a030902091302090c04050a 67
    0x30303621440c02c1e0b0b100c92243e0780c02440040e46c4040c901008034142c1107000c0701c001d0386042c42040c4ca8554008078002800540100e0031035070b624200c0c00d0803009802590380e4500304082c55403850301400b00c140c1c050360103000c10389142980caa01500741010030f400054a425022141c1d00b140030005000d5051940031007004002407003a13035030350700348103c001c003108540034000351901c20400003105868139000c007000109803100c151b00e0315440203104910700d106407000e0b6941d0009058010400c0c0140045901c42c10343e001c007502d00798501000c00c1c001d00e1015404142a440420784240213482489906000c0c0c62050612901c4440315400310b2030f200d54005100180404030f0040f403040e8031190102c803000596611407940d2120780032402903941800d0310030600f0b021039044500744501c030041010030181c50f81d980c170581040d06083c60105260b110f0008202455603078454040140c54060485104550801c1260045203241c01402109131009000443c894001c110500440c2d440c034003c2c406031038105450 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 729406546 1250 729405296 729405301
    0xf01020909010614040f17120307050a120603050f0f1005060f010e01090e150f030c011707050d0501240927090602040e0103150b0f122b02070f08060609 67
    0x14809217101351340140310362030200b21001c1030116164100000d50401c031001c440c3e110404501021080c0816140080025020130101368028413a1821a500301800c90b0001081c40e81c84d07440c545801617000b60041590044001810401c8041c400111807a8080c00207008610301a4001480508002ca004e414014002062070259211300c080f00060000480b148a082c00c0801111000403100800301d80b02d42014031508041d420003040c0c08011500684404030003c01c41414884c44a00050011080090034084101c1511150007018005c0c0405468600115400d0b4102c42c0704200300c400c028244603012000b00030b60040c281200d0003451180390117201e4031102110300c201904036100d0280c2424000308012890400f0044998102d0380305520400462030881c820b201910340c5880403540c042506d00141d07055003014050302e0041031441c41520f040341000d600c41c81c9200100b010f48819031144d20380c0d00102680400c07802010b41440e5410f0200c1a1038025825618000117040c9805031744800701 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 729407796 1250 729406546 729406577
    0x1401120308010b2b1b140301092a0305060a060f12020a090b1903150e040204090311010f0b0f010302071104020904091a0a0b06030601021b210c030f010209090106 71
    0x1048000d01180f034007904080b400505001029244003100b030b80c803210401721402c40450145025692202c440c0403140c1c15a8a4241000001d080c035015500459013106004046501d5900380307850f410b0256100001c050424405010a0200035001032003480410010000802d0300880f604249418621015944140c1d9280031a0400e100c0e0b40200160a800b103084070118a1200036045040003503501085505640c021a0382007003441d2180719101c103000404a000341c1803d4004581c00e43c00780c00d02800d40880003034141d00311a00d403c1401e00c01d980c1c078a060141480e000245604031142440e095052100360b4844072020034032907d40c0c1d84030b40d40c00500c16001d40c6481e08078640e0240c10100260b21030000c44a042440d0104036022030311107181052022851400c4030541340203190690003016190000350305006a03a009481c80c680c064100620400c0440c402c000040d0340c800d0716000f91920521400c1418507190b854102841c207a40140b010003e180c03902e081d4141102d032146010743d4111503848 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 729409046 1250 729407796 729407827
    0x110a080706050105090f0402130b10081602010501030f03030b0613260c0f010e0a0f030803010806010f0f03110114030c040519080a03140f0a03240503060112050309030d02011401120308010b 83
    0x100d0280c128496400841c886500200d46610503c44020619400010003700703d003241d109000c01000407183d00c04103c040b0b03100e584840e02031903000d41514074000380c82c255100b010400e1f03403104038084403500c0381d50400000d0f80d00400c7e11003824802002014201030015041468a070315080c10014441c000704c20641d0341c101c0d5000200014100c030001c054680c145a01c0ca80d00901810185d48220070000981c1000c00050308108c94038201030320b171106d0560740d41100141c894465981040107180f1002c04809030100194020f0003c8086282c0e21031074201840644460380301a540ca89800c030030200302200b40480d40480721a814501591800c0c026103420505001e800c011500d0480046000b0b01901d81690281fa9202e00b020030940740445030007503480c60b200f10b5000f0150190044001041280c00c86055489100d21802c1506d050001100120346058003032a000c10050703454400c21000101da080da41c5026107103109541c0c100d940d090b1000303080000107100d9001c50500c0095005200046103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 729410296 1250 729409046 729409061
    0xd020c01120b060f0c0a0c06051e1803070b0d1109030303010b03071b05150604090c14010504030501021303021516020d060f0e0c10090e011401110a080706050105090f040213 76
    0x29080713251030b0840d090109a0360303402403c04550302080c00b840850154040c5054491119401601e1100c010151880035840c0c2c00144841800703e19070261300b030320340d0380600c0000007070100f0020f00c0341c4501d5040c0e544010359031030312803911407a04100300c0420142c40110440e0b040d2070b0080c00159030307600c03004400c80e10b81c00707068051f01c0030894201aa100308180401e5418840014030303c064050380b02c2c0b904210440b00f0f070102c004c0c80310881c00c104100e221804816501e00c2c00c0141049820b040c0d41c4cae103817213082e64880f0f608000102d09040d028070031403502d90003100507103681180150500d82001d900054050b0710401c003030b210300f80c1840903400704003998120381c00840e81103909001d4021150412507407106003c0140340303c0c200c4943d2003510244241d02c240302b00c900c4032000c0c15090b4685008101443c0d1411025810400101c695401d40c02e410804650b10600c54031515595a600d4242003080701c5040c3c00c11171013a60544c00340440315000c1c41c0313603035009070b011505203458a004200300401420030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 729411546 1250 729410296 729410317
    0x4122f0a02130b04060b0a0f0c0507090c210204060207030b060607020a030b0603010b030c0a0509090715081501030b010c03180f091e091e03090503060a09050d020c01120b06 76
    0x1448003070741ca0702c460f0418103030308400341c40c18840325440d1184041540600115900018100d25184120910440b40e20940030f011b603058848440c1c0350b00c003050a0302d00340c0f60034602141005103000c8201144640c0f00180415000c82181014148800203454100510000c1d0810b80020085889640d5240803201c50a41c01481d500380140e591902018169045460f035200354644942d13155181800b29407100742010082003c81031505020420a607103501901d030310707075a11640c400403820305008030403042040c0498458001610f0315000800b107800c5e92019950415051240200d981e9030070040a40000d90300d401c2c440e103040c40b14a6050780498061340610024080c0300000144031082c1d6100c5000301683c0c2c0e1021203181d10140e541c2c4191001000010484408254480043d403203102d05c6003401ca200f803501da42c48a50301c0740080d1408105440d1446010341d118912002c00004124200140520f400506000d108040018044030160f54000803440e450ba2440307005035072040200d0b510440c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 729412796 1250 729411546 729411559
    0x6030a03121e0c1209150903020a122106030b012c040308150f0303180d0f030206182b050d151403190221100504122f0a02 54
    0xb41020081c014282c480e0390312021420b904801813030340480380a84030900703070418101004001a02c08950090562010580031801044d00b03a80000c1e400200154070302246c1d0340d908022070950000145c01d0b246030b0441010041c50030f0400c00c005171900180d9411606540d0008009003030f007050240000382542c2f002c004a52001d01000704140e00210040c1c01a100005c01141040400007808015420001c40e42ea240e40184002d03925803030700b0011101035400c003030b2414915128541e00d41d060b44800e49401c0380507030406010410309001529001440552503070090505444a800000743c098644444091000c10070800070720150103901151941c8150b41402c1042d10b0818a0405640740c180c0954034100501b00d1401d80c0500c0e00041111300c0f0b504860811100001c56402c000d000e00c00702003542c5031400141c40f0045090420b104100840c0302c60b0101142624092500d00c26801d4500e50301021300c5034001001002000c0200090b43c40c0120b03d11542c0046051400d0030310f04000144001e500c00c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 729414046 1250 729412796 729412841
    0x301034808011d06070c03050306100e030a05030a020123070804050708030a020f0d02010606021209041119020705010810030b1504050112030e0a03080919080d020d1706030a0312 78
    0x202c601580340140c0f0302540c1a0f0707840e9150360400300c48104c804c0c1c401034000303801030001c56036520f4102c907100ca80311840e04080c44004200008a400d208490350255a103410105080c00300e1034080c021801d14146c1072402c02c91009044511107140c98024000804100d8808002401c0203800c10800b0f0250840608607500d4049041c0b0003940c45101c0a002d0350b441c00380c45608070350745005000380003e0301c60710b4001e080310303000780f05031014141c01c5580749a84c0700c1e4560150704204c9101c007008100c1d007a04d1081801ca4001c0c8110042d281840d1680034078100845003041180c99100c3c0f14643d420740c2e600c8580e16525807510408003a954581110843e070113460030000180e44c9910a052034803d5101c1e13140d140c410301e100c00070000c0006141c4000392400c40200710804540c50301c0101400104421030300700340741c0d5884600480c45d049c1200b070301c82c0142c2d000071054902d203a000f5100404040301564501101c0c0303451004640c480e00d8a60009052002000201c40380083c0f50b04507985081c3c807110b1011280 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 729415296 1250 729414046 729414071
    0xf0803360712030e1009120b01241b030c0605150a080f0a11130c18050604150c0302070816030b0c07050a0b1b0d02030103480801 57
    0x1904403598a5401d01c01e501002550003104941000c1c1d03a42c054540000c0545400c3c00e0043e00340039001040104840d80d1401b02c2c41500200894518034022a10822150704181000214a21070081d000c0c90760840e280f002d0150343c0c06404410420b00015082508824515095654034200d5100605081c00c140c00c00c900c0510041625028034000c0700d504500b2552845000e0715408030001c0c0000f1a00000e100d2004250302000c00d03034400038050905840006d050116000311070384814600e00050714040701517020440c1065000240c803040750142c1ca05442d00108205000071801418140078410410a09140c000d0215500400d90b03101030303425401c40f0b109003500001c0075020495252a8841c003050100d0780c00c2084c0c4010f698014000c01c0380a80f151607080c41918014094440042c01d00c243d404152564806003011000b078a20144c0c4a50452604150b00310010344c1e1060400000d01034180c2c0312820800c2100401540328441c3c1c4a950404815050b004142d08403900079801c19100034008e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 729416546 1250 729415296 729415381
    0x40c0e040608061e07080105090c0f0a08181f1104030c0905042f2107120519020d080705120a0e01030608030903070b0313060c0f08130f0803 62
    0x2e82a0a8a0441c080410b400c585081c0d9100ba15400c000841c406c005109501785407640c40e4120306aa90100c0c209008032030a86480e901179584c5000184584082c000d549a02d01752414004000f0030241810001c0411041c0d00d81030b07406204880385844a000d10100d004002c104d4000c0c1d904814866005a100d0320940c01410060728100c655450400c4025004041084e40b045403680240c258400b41d4904e204010041108040381148007c2035680006402020450a402031502000034503002c909400d1a900300801c1954000200d121322003000e0069540d41c980e04a4680d1042c01c8685a00c030174140755140030789000d901540355030001482a8001d821020000c0c02c444240c0e01401a1511034503400c0e101e01441c50120317090780c030100702401b00b050740d240519031240a00d030f00d04548030750540350541580c44a034129404202d00f000c4a400c41076010071140d82c0141000c0d5503c0508203955a4038000c10800507024010003408030110340b002038800d03141c0528000a80f01c0110040212030369880 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 729417796 1250 729416546 729416551
    0x230f1c180b01080604030507020105070c2610020f09120106052715030c010318020d0f15050108120304030203210907170601090b060f0d0b0f030a0f02040c0e04060806 73
    0x704180c4490001a0480c2d000840d14400e5605581d01800c101099006503280d400c03c2100300c0300801c1082000c40d02143c6a4005800268500007000d200c2c0d84a0102900b0943c0c4120a4030301d83d401046040c2900c680314089036006070007620380f01c44810300d880c00b140c01041d041c3c110607400712200c0a09004040b580306a400b21841074503522031280c81d510400492031780101d0030f0603015005490804060b41c0603a0005203c80ca00c03551405c031461690340010b0301002d82000c225604010032707101c4001d2103241c070800e00000350b021104002550620140c0c0351703100c1e2500c0303d5460b104000800641018400d00554004030b0810427428205c001b10000b0168100d0f0850b003982c2203200350031002400c0031142c01c4002910100e400608a0b590030080030001620102141d00d8000fa4100188442d081c08407000b07044044c1440000100001003074104501e200d5030022140c4258028401d003c082848000c03941b81055044400080201850f02c0548034a071021800c294802e15000c40041e40080c04200c061 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 729419046 1250 729417796 729417803
    0x30408100b181006031d060c0705061602210903030706060e0a090206040b0d2d0c0f02060f0a061502060406060603020408030313050c0604030f0201230f1c18 69
    0x2421014503603040a0301c1d060855407900c40f40e465003000c01c0307004c3c000d40c89010417290301030b10b070500102803020407490424241c41f0085513860005a41050040c00e001d141e0b000520003076080c80c00710b01c20300000d40c0d40c0c02c40034508000d0400560f0608481c2c24910490704980d40140030340e500c1d904281040301c0141024461428040480c0f00058030042ea544200308101d0f40c0284828140350810280017120307000206000c01142e03540360014100c107a40010808602c01e0195179100031505070103220290f68603040701c84d045c002e825200d900c82c1a004103c4513031107081c207019184261f4a41d400c5e1f4020b04001d50004141041c0c82e01070b2000c0e240e011030298420740c0124420b005e5035568103000c40c00ca00c1944034220054006001085c0341030151801415031078068812907144166071000241c582c6e03c10340c01150008856014002156084007400400348581c82420145000c000d02541c15445146040260203400003244e006402980001c01e0306040b1188080080442c401e24040c500210008140c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 729420296 1250 729419046 729419059
    0x13051507120e03100f112d030f070804051c23030c040e0406060306060f03060c030c0503130302100c02012a0f0e0d0b0709140607170c030408100b 64
    0x40618500480000d4000c160290081c66a40c00000800d001803040c4040c0c1c0010310703100e04141b0f107000d00c25405400080400740d01030051400030000d013a2000644076041101c01400c3c020029068032030a240c3d5401090340c00e111000d61f82c2c51420301c0c204011507141000c0906000030640e105603010340c004181c960400605030240c000f441041d62140412146100300341c40400003403040342114001c1c0b40c0c20501c0364a0100d10117490740c0e00c810035108103410a200b596a008400c10030b000c460f000c3c8048001c002d00b400c00002182110040803032000904440400280a40c407008240c802c020010604107015002c00c04011079500c000d01900a00c20030300c40703000d1001d544000007501c0c2c4820850004403034540f818010704405045d00c1804d0b084400c41e41c0300010594460114441c3c01d85039120b110300303595000c94541002e08904690000d40032940c0140404e0003200700140340079090002c0083c01030034203511030b0461000359103184140c0e0406222401408107a03000c2c105039030400e00070300b007084422 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 729421546 1250 729420296 729420323
    0xb03221b05040504020603061908010603080712080402130b0d06140403031d030d1503050d02070602062805040f020a06090815071704030201150e0105091b070813051507 74
    0x100b1054800950b0041d500150030400300c1c025280015040440c4010742006118099403856820b007112017607802950329450008814080010915903041112950b08060b0400d06050b004101e140392003401d41c802065588002d038500740e640d40e00d0144611b80c400c10501020140c05506494400c0039601140442d0070b00c510000e0754407010f1143d0784101410001941800003000780c010282641d1808460302e41d51515021010603400e0114000451150300100006403031f00314028a01880200755000b44030402111b0384c10000700a00c01c40500c000714138041a00e0315903007042103c030b52103018000e50192003002c000070070a03003148110040705c909034156000d00c0c45000035052030b901c3c212a1301000451810601030b80a01e50b05461760031038003a100005803100e0703152001d00303802c101c1e402104c070095103500100040e1070301e650160351105007200c0b94400d5041c0d1a0b0038040501039900010180b80380420020b06403c00300482000801000300502d281c0d10300c030031008100e5848100291501e80d1340720039 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 729422796 1250 729421546 729421549
    0x81506091c050c011b03030b190b07030806091302010513120f200d03081308180306010801020408341205010b0103331d18060609010b03221b05 63
    0x1000c5c407a1082c0d051000701c807060290381c100c0003402034442c03441e4401210360721341d4480b9050781081030151809646607a0b849030142000b40c42003400510b0f440c443e03045041044241c2006500640e0720f00d60a0038865203400b00c0880f51583d80100d50084440301d04c504003401c0c240007500441080a42c06000190003040541000c0800304031041034098010300782e0403004000034807074042598007101c510707800b94000744907a84c0c4074050780c4a403500e500256407030031b21060a403030148032a40c01000404000c61401d868081500e8840c003414040300c0d50300801070f4606044c44181c0891692440104042080c1e868541442044440384400d0542c2c1d80e620b4907854000c1540a440303510214090154074141c0c0030031740c4821824500c69500d25490001006400007a080c040543c0c90001d120f01c4144821640341240c05801c3c0803441785460525980110b05203d41c640384c11452605448661000a5590342c40a1441907820550b1007900304a50142910300140442000c107101c010b40c42c11300e02100346a8500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 729424046 1250 729422796 729422807
    0x3092709030304021804111008010f0b04030f0b09100e032a07030b06040b120607140406141e071b12050601150c0c03050715030507081506091c050c01 66
    0x103c00a400088070754012801e90309040340c0c075500034483c881c025840c50a01d070200300303c100800400c1c000f1441020043c4144c0050120311400350025210704d500703180c038503100c0f10203a804a0300040c0102c040100800c1d10394000784480c0d40107611002c002e2001044548c40c4950ba50301100322074000322564082d4601459120403071220200c100c2008002c40303030442d00c42041040c805411658007613610408002143c540c801090001094117002d000f03d032410302005031001040c058298580070082101740301c100c1d0403100d1a070740003000051b2a600d402d840030b4421001603055422401c6400701090141c10440240f04c2c81001c0008a841c0c00708656a542c2400c92084102000800b10303049800140010350401801c05005540c925021700000995125078000403601c2d003040d10710340c2007100c080c04441d208010002c80d581c81454108032a19051a0090420b4401f600f09841541440c20004c165540c080648207016030050200395140d80009036114110003e0b4004c442078011a0f0251080d9070140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 729425296 1250 729424046 729424051
    0xf0902070203100e1603050c1003020906070b0c070b091b04020c1011040302100203040806090613141c020d18080a0305030a020f1611030105010b1b030927090303 71
    0xe0000c00f1010083c1030710801600071801c80003414811a401140c90900c50580c020045000310b01030640122004240001000c0d000442804d040c01041589015102c800444000c43c0e0000e0701c07580c0340c0e10348070b81b4030703080f803080c0240981142941401e2011064000c903003010415030354030381264180c01401c28801a8000c0d0420b03150141c100b00c1030303105502916042140e42149200489191035100e90000c0c001001d40c5841c01c006910224081c0b200d030004024050b00301943d0b0b0010121850980d0136103a005a0305500240441c000005540a005d4104108903104a5101101d0031310480c001009580c0d6100c500b0303070000104005540420034985560b940b050b1201035010701000510740e1401c1c2c400b0380c80580b9040415038208907418604010b000601a02c07280d44031136205400b035509010300c950803d0b240b414800e914140041044140c07040844070001810180c10358451010000b132404d6018070034007190425a11425051210341c103140032440c400d001e43e40c902103500c8690b1080d40d81e0204 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 729426546 1250 729425296 729425299
    0xa0203012d06140f07050303010608070c080a0f0302161b2309040311030d02070204061d0a0b0111011e0c08010b040b0d060305012405030d08040602032a040f09020702 73
    0x10795806000c81c6108003040220309085001d664a0460700520518450b031110005076072980000c4014045e15078040742c81ca803c5042454121900000b0f500c0d140c8562003070400c04c00600902542d00d421950094043e1900607404040a90401c4010f0400203c0c80f03810b400f80e0203983d05005d0000c6541c03c1c05104041250102440d01d9014050820074030103e044094402d506000c4070104844c80403108100502d02260b01020140c0c541c0c10a10511040c1d44103038010741c0c5042d038040200840081240c10b000d5005031182c2000c1007d0300034900580e111905400c40507029401c00040907030420f030034825044007805500c4104547e4070600400c0328403040a0085d046c00c0d0b0340030001048100c1034130001d044680b00f03420000498996941d40d003401c56404410b50388104004180b900608040080042d00070b240c244c0103442c1c000c00501b001070044400a0000b40701035408408103045c1e905010403405201401810701000d12080b500034240da030050301c0303444001d950031007001c1100e04d014000d03640110f60 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 729427796 1250 729426546 729426629
    0xd0911011b1b050303180a060302090906041d01150e060d1211150f0402030c01111906110703080906090703030c150e0d0302041e030b010e070e090a020301 68
    0x3490b9a075034185880c1c40b9440c41d8002880301011800faa8240003c0a5175429500741d1600c00f0110018402a078030954010001c0c584140103011aa440b20340640794060411600010340c500200301d2600c18040d00300c00001a0342c81c06c510305080080310300011040e0359400101c1072690351680c00304407400e00000d00003444c00c40d1012102a60500031100340482040d183e043d90400d0800c00d409000103e0200c0d440d20000c0004018407095060038805508201c40a10f040781d0b500c4d1040f9a801d81d940b0f414846001303c1200c1c24140c0080c0070495119039840e802c07603030449641c0d10090070010400102500c2e0505180a850049521008000303203910403280e141e11905000300744d0b40c440d034a5011706c441090f0031040d01e410164440d18030520007404214055240183c80b5030130a02840d2402d0400e0300003900107005480d080c008209010b091078112540310600c030840750b440302402c45d00c21100640f9250840d01030024096110300c640c000c0c5050320706a4485010b450380c0103580d100046100c02403603d80e040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 729429046 1250 729427796 729427847
    0xf05010b25030302191e02060103050d1101020714060f0a050112030503060103021e0a030608060f280f05041e03200f160801050f090d03090201030b060d091101 70
    0x11002070101d0105009040c010f09180080d00c0c4c0e05001c000f00c14079031000603503403507013162a0380500110300d5500c2118401001c0960550b690fa030394800724101c9000500001c4600348020780c800350129408264040d210088440201050aa80c3e030702c00e60780701c8451004030001400c44002803180074104c0e007189081e003c010403251010703241c80d40094100da04254081103101e03030b02014040310b04680040403e065568011f1098000c045a071984c2000d6136a0700f0000c140103180001007021904000428024007002c440c00c880742076134001a42c071030008181400c1724941c0c0180c1551040e4441d41c0034040c06540128611640d000030101002d0003030104001207050984140ca4450b03101481071810205e07080000d0309100070386400b4030102e0b4034800480d50380061003107040070300a4603080598400d032a8420b092204c01e207525003c18521840c109a41c9240d20004c1d03a02c81d8000b43c0840d03401601c803550b40c0d0726040080000d81048c0f50265500f103002100220294811407000b0403142c4510040103099 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 729430296 1250 729429046 729429097
    0xc0c0f02060a0e1c03081317031f0e04051b03060a0b0604180e160509010605030a020d0c0e030606010509131802030d0513080a0b16210f05010b 63
    0x42d0415810042003060981c1110030315190b12405950b070819140507200141d41520300142609070003400161080c4415411000240d00d0030042d801c040700c40ca009a850f80d480414882c02e0003040d194003401800100d8002500401181083e030066025000b42d401902c0d240c0405841541621a49901984400b00149038540180c0c00780040f013070020840385c50641d403000c604100c0c200c0f0800c240c1c4019600c084005021004100090140c8500b0300c643e0260303460400002cac5003400510804003444070000020b0211500c6034101c0e01d0400850a042040480060004101c040b00a0b078035030007449224082400340d8044c00c00d84900c104000c1c401200c0c00f0315101c0010281c8000390008510350107007101040182d8040c0a20081050666a03154482c040d802060032818020780c813042054208038000f00200d07480c600f469a00c061402d10506083c40055012245618411310030000062001001c00a02407035400008101a0071740d0b06015590701c800f40c190b124070808500720341c1060320300054140f1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 729431546 1250 729430296 729430309
    0x70f05041a090409080d0c0e0f01020307120c0b010e010302010206070e0f1903020a0303030b130b130b030c030a03080108010b1c0308060102030f0c0a021329130f0b040c0c0f02 77
    0xb41c200c09400400c4092151342c544805402003408421442c0c1c07a0508020010383c8051203140046040303e0034445030700306c0e2002030340301d20850704060314030210801c1e40d45c032560140b07218060081d805201c811542d0313911105440b0400080c00200d00600a00f000f080c1054421010340c021003100801410290303903400100190190706180400485100e2000000540d40f84031008008500a40713010541030305800800c504801c000e081c04512501c4c1c01691290340d11220303250040b41034032540000d0300c181014002480d0001daa40b072564035110b81070900080582c00f00840b07040790344890003413002031110b00411558250342e0a107081d20104c010040d102003841120000d41150b41801502d02c3c015140407908655401544a15082d6001105075011402c00c024500c0f5103441e0241c0412141ca480440304042c2d0068810417001000d140030148403035aa09144e07030f0105101c6200030000e040b105035800c80a050340b8500c15100718174181d0030310410742c02460403030303041d9a12000032249100a035080221 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 729432796 1250 729431546 729431557
    0x80a02090a0b030a0f02030c0a030e0706050304020411040b2209090b06090403110a0f1a01140405280b0411090619140408030c060c0408190203150708070f05041a 71
    0x1a5a00c2c0c07817030404c203543c4600c002d600440d19042c415680d4820315902400340c44022a40c81040c7d40040c0c0c2c20851103900c601030300d4110380d044034041401c040301195560b47c0d0245401500f411000082c010403e62602c0102c401c00000c0300c04002d040b80d964001c0e52003250351041c80503103401c2807400040d1032071800e00390007030707006100c1e003080f001e02484080201c0c07a0500c166421103240782d4803540301c0240300c1d40a10129030030b02c0303a0324041705c51340c1481c105100c0600780741c000c240916156404962000d101d003082c3c480f1a0f81040311400c80701d4020064402511503803903024000c614002d84005080e04140c03c03961204130140074585440440c520080b09031020032410307800c10401544005140548000a00081820b08000c0d51102c034070f0340d0642d080080c00340c0300490041080104012103000401d0610b03c569440104000304419800800d003800300c550302e112046040c0004004c5a65003004400c0d010700b09503501c01e5103e03071520034103079414840c81c000d0f00c084001c180e0200d02801e894100801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 729434046 1250 729432796 729432811
    0x31d0a0204050903160822030b04031418010509010c02100e09060603061c11062b0c0207050111010906020d0e060f0903070210020f0d030b10090b09300706080a02090a0b03 75
    0x405064041c0101c0841a415810032210360f09102d00380410b16510032400c070000119410068030f442c0940ca040103050dd001411907041c00400304808080c2c0c0e0042600e1410503401925081615403c200c00a014200c4804942d105648180c0407803103906043c0c099030b10408000c0c051402c84e10383e120002d4118500001308030f40c1440070000207601a00e81001920030380c427154122074090800c00480c0c110204107a04006a041d03d8500803110180e40094014100e41082c2001002c0343c0e400c0c0311040c00f50204141c0900341c0b50001039010010718071707070703011440c400c1200060303d4540e00c2d60541d00002d03010680d0b517040e041c0c0c021b00c44800903141440540c007512101d4011179803948103a004840c00c0101010401d80803036600c00b07210b400e50804491308081c1140500d0300110f0035041403841c4619005081804e4054a03548240c0f0541201c1e085101114101e22190030f4810407414803030907550205402a00001640d100120352013021302d00030388a603140c2c0100700c2801c3d14202042007049801c01010384 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 729435296 1250 729434046 729434077
    0x31e150902070f0c060809060c0a09091b18060903150603120e040612030512100803070f060b090c1b0c0402130f050105120708040201031d0a02040509031608 69
    0x10840694070041c605248504201644815541400000649180c0c802c006001d99001041300b5480d0200f01d941d0b203c0c00040380c0a072034a500c50421500382e051604411304a030301c0c21320302456500c001d44030500c80141e960383c1c90f0010b00400e007071030300c0c501d156204d20801319405100c20310001e41d14001d220304d010f4241d000045d0140e41c81d201c103604000314030042800700c0d0b03840c05901400d050901501010b0242c0c0c00b0312680074000e60782c004140d0700c10611121600d81e1040301144910070b25200c00b00003812064102c07601c4040509000503c0340070144112003a900d0704c071400e0050f09040c1c44c041e21035484002d446040120032200f81d401c0e1280301032401810701440e00d5461060b80d55101810356030100101d445085403d000540c0c000f443c040d0811418440d09010b03810700c15091411895011209180904c52520ac0f031005801812401c031150301c0310041b1003d402d001c1c4d00000741c0030040a008aa091103251241180c954591054454103031701840d64152032030101d004000200b4121341d255120 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 729436546 1250 729435296 729435299
    0x6070f0c0b04030305060901170c010e0a0b04031406010519090c0e0603150301140c0a0f020307170c06241005090406030f17030603070302010f170f07030606031e15 72
    0x81420184085400700c004c283d0701c206106072403c00c41c1107280501003611140207a80240898a542c840701c41e107507241002201d025032403064543c640400d00500d09145a580c80d1174991800481d078603500b00300340c042d40c8500800040c4d0b902d003400c43d44541e0751003c081d24100c03908055003900034064405501c030500c11120b02d18140d54841c20001d6203e42004042010229600d5040609440c0500c2c00324402031420801d102040e41401e01b191010704250800d502c40740c036500400c6c0d040d0f014601d8040c000c00201082118007a0440300200380310868501a551156114012078010200d025039030110039907559265a254144586034030004c864a05041d0f04100c010000242a50050f0f0002c660075401e4985280400a4428a29111081601c170082c01c501c0e02d0401700381d40b20340f41c1c0700c0a4104036803580484000c500882610504d001b540300c16000a103484921442c0218080c0c5000e80000d290040024803103220b840b81c203081101201909055110100380c1001401c650f4001240c0440d01400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 729437796 1250 729436546 729436553
    0x20d08070807181707090207020609121c030b0114030f01140303040807081b0a1409060f04090501090b100612021e0703031e050103020d030c03050408010e0303010f06030b0306070f0c 80
    0x2240401000c00c45805900101c4e440407880c14900107510860a440c014000340380103070380c8c40041d20100e03c01691240c161000d611403091401e003403140e0342200424850b8004009541c160080d2404c1c038000e80b41d40f0002c00d030220b5040082d21085480c041ca07a40c1110041c0408a640401140540310040450f824151505801428618980e000300c980d944200c941080f000c400c0840714104075012180e90440d140341c958a8442c40c042c0c102c3c0907120303005540000d00c4694613000381d04004100500200407002c02450038034028268001c00391010941c0900061b89600b100d00150107540ea0340e5503000c0f440a20300e455402075002600c2d1564003624061030703030003a8a4014040c240c0b490081d03401044030f9800107044c0c584181007101c28030069040a0040c03002da03c4000d10180d40360780c186850402026203090403110360166400c0000749500385414030044044c000051410f892400700d0028809a5030f417000c4e41112000007440d901038000030700250b10140114808a441a203900b414500034503243d9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 729439046 1250 729437796 729437837
    0xf060807080f07060224130f0b1e09030a110708010510140402040b0a050a18080a030806060a080415090b01380d0911130b030d020d08070807 62
    0x10040c00465102000400b598141046018024001c40c0040c1282c400f19240c483c440811051046080e5a403000c00f0038006414144090032454000ca10100b0b2600f462400c03000181e010741c1e00d10300454107860104660401c00040a0041504000035443c048910b0300546035804201d040c4803840c0a1400e00007020002801410b10580300d000401c0d20490038442042c0220815504280c01580706100601c03030004104102c03003903455182031158a80d6000f85080360310030004018000d400c240035600045c6030100003151500c0d144251500403440e925101800003902800c2030f44400502c5010100d001700d00c40c202ca0006000c0720243c0481c2d803c02e283c680e5807070321500780d200c48107100c040c15103010b0003280305010405d202c04c2c050192400819804407030041d401894980d404c1c0a07504e24504042050100034115103d1001d086241c0540c05001004003c010884500b40203010750b80b006448144045207201c080c3c000358450f01c2640d01c44680499600da00204500203216401d452400c0c1c50340c150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 729440296 1250 729439046 729439049
    0x11e09090c1a030402030a11130e060a0f14070f022b14121603180602070c0503060c03010605160605090705190e0402150f030103080d1103040809040f060807 69
    0x180740400d540c62a041c040300c80c42c080d140311090244414020f0100581c0c01207201040150040001041c2043d00070009a002c00d000b90360701d06203442d000844140c010007141071442881201c60821140c2c0818091100383c43c00603080c171b2101c0c4400c80c0014000783c0a180e0f0007200d902d0600c1142c8141e0300480c034019110700b2940b0700c100d80d140380455100d003041e4030a044c0c0d04442c507221100b0f8186030a414881c4078000028050707540c10304610b5801000141719511030351401c01040c88880c1840110704014000303501007201540c04002080004ca003c5c140001c8030350103400c00030051890750f0b01c0c0c0f000407166a04941c180503041a090f05021010510758042e8034020203005001d800d0301460b10b802c0103c0c640380703024511005c0c446800c2c100300302580e008207298031a8050303910030304441c090804034400c1d224413912501030050100000c014462000003a24100780024410010240541d2001c010381c001224000d041c20001c0001c040c07181000d030001d4071001c0c0303188070106e081c50f00c403100350f402c14074207 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 729441546 1250 729440296 729440303
    0xc060e21030f0705070b0a091509080903120f04060c03050d290103060609031b15020615090c0304060207051509250b0f0c030409020f0405030c04060e011e0909 70
    0x10003804a010745032040d00307411050134246945849015610608140c50041c4202c2a2558502c18041031113411580703c80840b41c059020440f4282520b01648980c00c0307041644e00074071545e80d41213050100c010484800101408055092a2402d80101c641d00c0c8614421401c1200a105151001c0080e0103000700030791440710044c14a01c0e00e0044800740c1c040400e091810507040800410072250840b8445040c0c07500410000d01d00b4003044070009590280e0741c80040700c018041c0e40e40008541c007181d410300601d60f6840c0c0c1d00d4a41150300400c0440ca038151440b9107222020004a40018119070051503600d2003802514113004042c00070400c00c0394202d40c00031890304140c0344600d00741002004044248038501080003c2810403000c00d40d5801140d1031030038040c00000b900c44441c10b0400941e4020680b10400f9551002c10f00b05681d0950001c2c4940c9000c0d100d1040003490900c1c143c040c40c1c042d07860481807007095a2900030307503c000c12490301030300c1d0b40139410310f03004aa422000e000c2c0100c030a00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 729442796 1250 729441546 729441613
    0x3060d1202012301090b0109030c0b0a0c050303180708030742020d11030f04060c111204050909031e13050a14030c01020d0210020901030b0d03030507020d0f0c060e 72
    0x3501603a2016a1084003031681000492380090000902c00700030041541d410b120350540f510381740c070020785c0c543d11240c4005e081c40c0b001104000c0c040302aaa0781c8008203100900b0b50301010790302e01c01c00790342c1c0c000e081c030050004400c01404002495404510031181c1c4060b50030143c4034824100001c0b013640e81102e6104035076000548000001c81b43c1c051840141c1c0c2440304103240d89003210002200d044058030081045c0d8480c903246240138031403c0d558400340240c400703580c00800c040c1e0000251394042e1095038015510320002980c404c2020040c0c850420b0301241980c038101068402c0c00d016070226030b140305002c1146c90085459118540d0901c040c2040b0099006980a40004c1610307090310381c103d030383c1190f100220300140c09a0120b410102c440b0b2481000d03840c4c44100c0e00580240a200c4010303500040c4080d043c00038144d054204900407040c980a4910300a00c1e042d0460300b01440001040216040c5115000081c3d9182d00c0808802e4440058a180320071740072901112481104a00c10300c042d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 729444046 1250 729442796 729442799
    0xd060e0c09060d0506190902060a0305011a03070c0b0402041b0e0315010b071b090f0c0314100527180c03030406120203250207081203060d1202012301 66
    0x4010384116040b02003140c1c070030310341e01082e514030742e4510008211001a0b074030800061940c2820342c01140300158002d00d01e98607084203401c01402000d007480340b000301400802c032101c00080e202c000c41e40901001d5803198000480780d10703071000303401028000701e07001070351a1008101009030140f5403541007400c0c0d031000701001c80f120805191804562512820300c80c80d80040141d41e4141d000c68010303030303804068500d01c0e2160180882d07141c52507500c141800c07814003040c01c822541c1548004540000740e00d082081e8040c1e00c1041e0b09401c8115080840a0203d200030301030b52a0826010107c136038a0001c8000402039502c040d40000c0302903074208030140c0224a16801e400003880707081103950080d40250b040c103207000300052844e018006031244482d40040828285040d0640c0241e00b40350307050b00b8003101c0480301002552038081d84600b818030302560384007860410344541140d00450008114900501440c0c503084c22a0b4030000c400c1d401d541d44d03a8000041c1e0080f032602e002d0038000b47c03a1540402c0d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 729445296 1250 729444046 729444049
    0xf0305073006020c010603080301030b0f0402010906050f070f1208220201030b0102101103060a0801060b0708160c0303120f090f03081302090a0608071505070b060d060e0c 75
    0x140c5075000040500304503041203406503a624140c914114004810310a90340c900c0c1042c8000340320f80b468100d050f501b0310002005102e034690003507040b640b041c138901c0400da80e112030580d8004002e58000380001c41d00d410800c00e161050014040076410f80703822501d44851a9102a015a1000421903c000510a18911054024000703d078810703404000c04400303500d200c2020102ea415610000c1c145a03a82400b10402e9108026102c882500c3c1d100401c0b04107041c001604081e0070454506202d5600b240340402c5c03400741801303204c040b51060045c07141444410399441200c1d800c16510380340081306624001020581c8001c1c120025406034941c404021020f02c0003d081d140b031318040c00c001509009004001400700e04442150641601d041c5ca11a180c045d0326002c5401801e00296000c0b40354014030908610a520600882d04c4c80c01c100c8825503030300c00000f1305442003071442c50003096041c04200045407203080e900d5400703000200302c3c0e030100229903581d408444488003240c0c21988980400e1049 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 729446546 1250 729445296 729445303
    0x51b03090c040518120a050f12060f0f06040b0702060909010b0c0607093818040f27020406030f0302010f140c1b010b0307080a03080705030609070e0d020405010f0305 73
    0x24500c0e0b60000504d0f481c40c86443c1da01d0046100750382541400103201a4036a102d0b84c1980d1414844040c020381da116190200004210140c0300148144c0100c0f194030b901e4545403004a4039030b500588414101131610784c004172150004501a48c10070740130090030f92555500d14115000c0c00c258985162a01031f441d1801d46040300041007001481200751084c85500c900400410b00000c2d080070b61a189003240002500b22445e40c40d500d0300300c040c041168112521000249002c0e08000d503002c101140c61070305803106442481d2410207001c003154105d040141000010007c8181c0003400200d0015625507524156021505060300142d55030306172020303108158002c81c00c1402d40b241c1c40c0d03c01ca0512401d003100320701c00e003890340c0d405400865407041c00c0d0740c086d000005a81c0008083d500096520000315850780c540385404c60004013040000b4a00c140201d00780c2e8018040508010f5180e074076200180c1c3c84014907014241c1c041c00e09000b00006039214083c0c0c0c0d000c0c2810f20f1010b1002407451400500d07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 729447796 1250 729446546 729446551
    0xc09150e09070315020a09150c0311011103160912030903120f050f090109080303010f0e0a111b100e03090102010b040b030a020409020d0c0603060512010b090a051b03090c0405 77
    0x15203402008041011944880030040da46100410061ba2000302d001e041e40c42d0145079002e0200d41d04459030b4055160b41181d40c000b000d48c001d889601101c1d509180240c01c0b15112040300005082c05d0001c25992401c142ca4100c2603400360401600c465280c403a00900340040301021400115200001c1c4200613841890051030442030902180401c090900039141d4007940504ea11514004250713001036a100d80c002e038008018650549541c1d503100d962090408010340140f64018040c040846d80c507a01e140701c0d2803e4114901c6207541002c10108031000300745070301a50101b09105400400600d82414400d0001c00e6012100450340c070a418000642540c1d00c40050070300c56403400800c0303103894a0205010559560480b000101c00e0b90910024400c88040751028107030321031000000c11007035019071040c002d4a000f00c40d1035224160b50104c107800e0341d551880700c503007002c83ca002251604086030007654000c15211046149540d00412081d80c1c2d42084580c3c81056020311244c0c40c19040521900780c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 729449046 1250 729447796 729447811
    0x50114090307060809030f0706050702070e040c0e04060b030d110115030209060f04021209010b010e0d0f14011b122a0503091f09140d02070b070c09150e 67
    0x9040180e000300107034035000a4481d9405020030f4400191501030188116101c0500601e11030380c4440b40350411500414080741d1240140c482c1e6040411407904100469200310ba100f00320100700350902d61816690b0380701401c00c4a110f521140100324a40d000e02408825140341d5840c1c1c81619132005030f03a4203444a00001d48205000103000f030002d62226100968020420781c2ea6890501544010030002d200b441e082c04115624802400710b190350640016010200c244c1c2c9094030140700c4020440c840d20803030b1f40104000032a40610380042ca5004045502c40030803000094580e09000d1460a92403406901100045801c42c3c500f110640f00e1250100ca1403280701d403426002901c200d405242d640fa006070100388400070000401092003045000300c0b0f244010f50034030040b40005c400b480508a60a421258415035215840d000728001030325090a15080e40203000315490310b00c10480c1603016030020340740024514400f1075040d009000300565010034114000c1c15628051004410890160820 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 729450296 1250 729449046 729449087
    0x20301110c070605070f060c09080d1b02010804020d02130f050a090c050d05011e0e1504020105030115110f06100906030210030b04090f06061a040f03030f17100501 72
    0x607256260004081043d070f407182c1003040d0b031880c850605820103040044018407485c2098050406240d02000100480c1d020384121030021078201c0c0161070100c09201480ca003060806c0007900950700c214243c0780c200b8006851040030706929008200d6400840d4031520b505a00c500580d246d000c031038414198804007500c400c00060140381e49107045110540b140c070744512002c1c0c00e414140130003076021090030b03411a6031410840f028102c40101600c9102900c03c07550092203090b2854046a07402544120750595506155a0800c84103940086014000d5400c00440241504030b00c401040400010411301c80180200d00e0300c0b041c0d5504500040e00100710711410000c0400051700d41023213140c003845403410702180319400580894002c000103400030300240d90000d080c1c400c0c13000030f03404001515420321a0120602040c01b60800c24419071082403004240301d542040441d04c1254071404900c014940740030301e15000708403250515020354803022007420380c0604101030368000641c00d400740c1c0c82d0b0055 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 729451546 1250 729450296 729450307
    0x1b0201110906030415150f05010e090a0f02210f090a0812060f190513021309021e04142103120702070906140405011703040b0703030f050106080402030111 68
    0xc40e0980980c4200740d00511000c004941048150042d00104c908100010440680b0140032070075200d00b240314600c1d4290b540d0780c000c40c155110b69240704441c40064440320b202d40320482c0d8040201038603485001c0ba25800d001d41e884080c0007540c4592014000c050005d41c81c02c11034104040144050000c02c00c0d680242c28a10005540700280c07142c0c005030340202d85c03c076a80c040100300c502d640404080d46c041c0790301d4840c1c1c0211000400c0d0030140d40003580c5980c01e02c2e04140f0401e04912985034550303684810380c603080003076036134540080c000e016804c502184204800d61022007143c105802c03c5644404104211686007071a0304091016000484c3e0f0200c2305580a05181e01ca100313503090110004001c0c00001e8665008128039002004030610070401d440d9104602001000318100e2684140d0800c40006a50669500f8a03480d90340014051032905180c80180d0f44a5031014000f02c003815183c44030750424071054450580246110b8549100e00c1c07500d071042500b12406143c24401c4803909100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 729452796 1250 729451546 729451571
    0x15022b1505030604030522060c05060f1b0309101107060507050708040314070b0f09030708071a03070c0b10090525050c0307170a1407030f03021b0d031b0201 69
    0x43c0590401d4041c24019a41d500d800c405100500e50f00041c03544800f040440016100c0c1d011080c0451640070324182d48035030322120b03010200b12a00740e60b0503030f000780c1c5103c2c11006480207100841d0000c4031402161440d4038200071350f0301501c040303030440c9850034404a00c00007408124040c16600c42070600d485440c0907515500d42d002070080e8000a4002c0903c1c1c080d884031400200600c0c0e02901c50862400d031200039402c0038078860340c4008040390207801248800205014005000010f4460001035540482d44203510f0b00495003004001e14100140c4155400116030482c1c200d078003031442030b02c03590401c9003170150404c143c0c0e4010b0103220460010390f4580c00001c0e1080034001e200c0026283c119650600040c04034510b0140002c00361a04845100da00305030086c203001002080b44540719101810418010840c007030140c41c40203400b0034110903040c41c4403480795004156201c10142c60130b0a03142030b203101078648180070604d070740800da46c1c4400e10b100c0cac91104403440b0704c55070b64402400b041c2c60694 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 729454046 1250 729452796 729452803
    0x118020a151407031106041202010b0a05090c03190603030e181506030a020c071d31020a03120f1209020303070f050a0b1015090e0415022b150503 64
    0xc0e09100c0c0442d000c6100002c05100f000702120001200003212001d06282c2000c0b1030b0903e81180d520f000d9841c14464801038180244841c2c11280f000340761200300d996076804c4840d00c0e48003c04e00d41c4190800521207044009a2003a500950b000742e440018410300b00c000d00c11042099500080c02030046810071940f1000e4400c220001c20003610007070f4803620350721200000b0707006404c0703807a10b5402602c40210384c4840f24003070783c401204402050013483e01c83ea081210104843c814010b1244a142c10030001c000102844100c3d551001c0d050750b840c1556621003110400c0054020000544070300d601c003143d264403180c40c040102038000c0c20881056160b0000f50760b4803504000030602c0602802e01d406014081c0082d0401d250800c602ea0300c035182000c42e80f08281618000d002e00300503140c071000d00b454460301550040e20600d0420700000e8031151981056229803403100250607030200300c281c0b046281c1021400349022646070100c02802c000c0894010f40d405840d1882c0544030f055800c2101e0340d00003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 729455296 1250 729454046 729454067
    0x1051008031e040f180c050702030a0605100317091207060c0b0c07060507210c090e100b040602030715020903030a05180607230a111e030118020a15 65
    0x803402d4800b1400c219441c0006028981c48610380100c0d04800055080b04066aa5184100503200b00030700d040e95281940c4501500380082e40662041076982c00241c004e5004a410801144030454140d0740ca940309800340743d030044c40c1040c1c0c038004039110442c2c2c01c14a1480c2034030031480c0c000e0444c8500703100004110261080000c1c000c0c51101c0d0100b04580100c00440710241e4000409101e586030000f4090a000700303440c3c16001c80c000d0303240d419050300a00d03c42c2c04a4030049a0b11704891500d84112a80e0381c0c5006001141c0c4142443c2c800540e419100000b4802082140c025603100c415500b0011005071189240d40e040034010060010b40c1d503008012207140241c9e80c24425241c40c216a4190000701e25a955107401c40390005481c000c0c0840c1c00745000010b8103060303c41007101c0c2c1d90f03003010351144890400201484060301c026811854441140d07540d22090036840503206080b0b00002e400e680c5841111504980d1006000c410350618001403006001641801800d0422041c402460800403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 729456546 1250 729455296 729455317
    0x5030d0b010c020604030305090306010b190c030e030a110a0b0c030f0c03070b270c03070504050a1823070f060509040e1f1a0f040b040902030f01060303020105100803 73
    0x25000c04200d0341e030096150464640d0040e108a0b291a224a009030850340161402d9100e80309600c000200480e8000c201e40302c940350086080030640c0803030801e4920001181c42141441400c2040302c0703194800708010382d54203026440222014290034281301d413103a40b85d002140c1d004001c2009200310a000030480d000c100f00c824041d503803404401001030540c0a400801000d0a60010a10042c4515280081504001e913220188124900c0320840c1d5240881c4d18025016040f2000400a038905a40001d03444507500201150382520241d550a040c001c00c1002c6404000c042000c081021060f2010000f100003103004020030b50800d00841031030280c6100d104104280041d1140164403150400c00d242ca01800c01c80c1c9500151081600d103070f1010b5045149424a444007080900392001803a100c10300002d004902c00c5081e44042c0001781c03150180c3c0640090302d4170310400068400704614a03003040e144000045150451900900352403000c0c02c0c0705000050801c060080340008001c88119442 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 729457796 1250 729456546 729456551
    0x903020c090618090105060906060a1707050c010c02010905120901090e0a060b160201020f0105060d020904020d0203150709080a0c1503060e0a0c020105010e041e060603120c120c05030d 81
    0x21800300151449071202c80343c03581103d0f100248600f65005410035805004101e9416120780d880d4000d0200138010305801d10001091100130105c6400f90b074144540044851410610300002200b4032825502d400307060705c0041c5e54440224040c84002e002d10500e04905103112032910040500003020418240a03140d001c200c3c080c0851550b008992002e002040c2d10a01117841d104c1c036100d070381c0074144240821781c0076000740b484100310800180710700c03449444020104181600c0b66024061085802002280c102c5a070b1040e06000d0380c0c04010080f078094600030106064036114030020700c2e4511980c0206c41d40e0388015004800201400041429100020140c4840c1c1d03c9400c070880203025158460a0404018000d2041c140115003004018110980003800181d989035014002c010085901405103c1802504208040c0050038a1071141c0500c10101e040c5440b03449159003044401d1910020445407080e00c0304003d04404210001012400c14240c0b048071902d400361a0f200302c0211114895 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 729459046 1250 729457796 729457801
    0xe0408041a070203072301090806012c040c2603030a09110d03110f120a18080706030618090b0403030203070311071b23040b0418240903020c09 63
    0x20341907480d843c1d00203040f40c00fa107a50b4901c440404505468200740349441d1741e03150413994010b000c1e6030200c50210b00141090317840c0000b44801d510814561442004411304071801c00706064104500650141f201e60044a203003a416440210103059542d00074002013000103054140401920b40c070200e038443c0860440c2e46850410f412481c070002c0168054005050f01e800e241c0d001c0c124035100713860042110400140604410360b0354600100c507101030182000141c20b2588580c120708001e125038050100c0d5a519031440303d04103480c582001d0000f07130340c5400070022010001c143e0314000c0d00c01c4200b0411240e4170780301c0c0d070342e110801400034080c1900040890803851080d4059000c0765404090a500d54445203001c44101c00b0750f5a24404040829501003680b40d140d20400012003105090010311040d07100500c809420f07852070301075000c0e95074400707122200c2c00c80e2849000c0383c1c07007101f09003100115818690b1140f1a11240756114500e05410f900000c3c0d00028900f081d01ca0881e41d0b070010784d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 729460296 1250 729459046 729459089
    0x7060e0f010c0b0a050a0b0307080714010309050304090911090712111309050411030c0d060f0f02070f0c0e060a050409021513090b061e09041b050c070e040804 70
    0x400700c42c0008046075800004c1016101965002d103024a8000780d0910861a060b0f08140d610201802000c000341c2060030300308000645501304075003152040c140441d5840b20340d111036007141c00551194401c10303291404401002040f41d4501d080d01000c0320000401c1c186002d00070403000d4a08640040b0541d2456450000e92001c000d07078001d11190305900f182c0c03035120142d490242109842c02c0320140c01040c00107a0510700030030707940007407a005444401920510784aa0001e0610004d01c148201c0d81c440b20b1001a540b20f000034000a802a00f1962010909282085403051960302a42c0001298002c3c44103642d03904075410304a407400c84002ca0034682a00000b210104c0e8552000601c0c100011456103400c3c010000700102c0e203080300d0400180030304000344100c44c07286009414001c880c1548a49079070360803c0180c083d0560280001815485640312030900e000c0c41c0e0144004903401285049283c801000090090003d02400710381d9400d0a5680e41c406000e40e0241c04590780034009144144c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 729461546 1250 729460296 729460307
    0x3010b03070c022829030a0e1c02060a0b3015011a070b13050a0212100e1b121203010b0a0924140405060d0f0e07060e0f01 54
    0x7070b20340040c00c0440340e1030383d181d404500703205110398410000e5026a00050702d603405005040192461913800c0e249620703190812a141e40001c199042c815034851b11140700f050308102c0078a4540196074a11304440d001c01019103000d1008120290150412010b142d40ea111031248031424842d002510008000800d00300b10304040c640c80801282c0308100c04c11603011400484c403030403660b0400160060404091401000f07100c0c060b0060107641c0b00c5000310b42c08404c08810740f85030384e00139015500c9032002c41e8001244211005110080740d403201c0c5841e00548018410240c071180700ca80142444002c0d0801d0004500c90035801d075100310050741480440c03030418002c011502c10b80720170640c3d50703685922000d003158110780c101c0800101c103014045100041110701450102080c5200280c04807101d07002c0350041d61a161040341c40c0d009000000d241d4072250050000c1c10074503c0e011503105032080180b0101c0701c0031140d80d4055441114100169a0011b00708040d890069590b0f0182180c407100580c0c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 729462796 1250 729461546 729461567
    0x909030706150603062913030f03030903020c1c060e07170114130b040b1b0c03070219061d041d010e0c0a05060417240f060108040803010b0307 63
    0x6481c2011401051480c0040b16042a41d03071a480c200140f94640b2003032018a44c0d03100d07981c01c2e4600b14144c5010b0525494014000c3d1081a48042d10076503243c2e0f5030540c0b41601c482080700480c0d11075141c0c008040d0184401d0580442c01d80e05415420144242480303016680d84007d426140e039666048030b20750040c44154090025041460110b07012030f10610300030189100c0140309002d500d40400c503401c94090440da0b220f5000560500d89403980d444581348208007403c40524036000300412a550b079415070241c55101003000241d9201d04150040c010341150b00340300201228058042400007940040750050360f00d081d81c80000d0310080c100c1c082802400307104030081e0b6400344444a404030f0001500071130700800b81682600e00c0c0d24055401d00407100d00b18001d10343d01000c10b10081c40140c41d0714503c032880300001c2e07044944c1100c33120280005415040e190f51003035a107841c04c005903a100d42c1d506030381004080c680b66189240c140c8450400b800180107070b038031187c4c001020810f0a8071948620780c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 729464046 1250 729462796 729462803
    0x9030403200307121b05091f150c051b0312070302010e030d0603030e0301050105060414010917060402090f070f031e1d16050d020d020112020c070e0610020a0209090307 74
    0x304101c0d121880070345481c0c0700200488070301399000f2042d034881005e0304100c0200c03040901152843c2e00c9544808030400905010080850070840300000d042d0407003108500803810381d4450403455070140c201642026080210007240c148485410045624006000d0f850658441d00300d6403641403510303080780035008144604100d80700220b001414441c036a0f0100b0201c0344203031070710642080c0c03480030f0500743c0c1d009100703407540981c082c001040021030344580108059814907260004a0b2903282c5d800000d4603032000008a0762100c0100000c6044c0030710125045050052850907a10b801000100001d041105450405032601c003030001950320421990b02c48944460705004141030000b440d10740304d143c01c2d004006845016030382d11480604c00003203010b40ba4040c00c88000c0c1101074003031000c81d00d41c0e00e000300c0c10003540c40315200130328610748040d149201c03805010340031640c43e10b1454100000068100c1d4400c1d03c00306074282e119900000ca100410ba410340d641f1480f9542c01c07168034114011110302a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 729465296 1250 729464046 729464053
    0x1509150103080904051f0905090c0303070809090c0708030402270415051b03150a0b0c0c030d0e0f042403111c03020d0c17071a0a0203090304032003 65
    0x1c4100404140034143e50704050321308010036682c05d202042c2a08101d90850001d0f14184c0c402c1c0f00011150300b0080d4821818002c5440701001d60001c6407950f40281004c3d00d82442c041074000d181c2c5410034000390031a40d480000340c00d20300c4c692900f0340d01303100107071000f8420020f2614400d0f07165804030000d9803050840042520b0b074541402c00790500c1c10000e0703002c8d01c3d00c1d16020000304900d07010241c00c0307404403601d20480d0030b40d0340c0c000502000c59008a515644070200c540c0001b5104003850082420741302e00f8019019036200a01130614012000706090144005446401c1e010f4030b41842501a1260840d03000c0303030801c42c51103040d0109141c0d07a0b0300318415007810303804421b00c01c000701001e00b07103641510850582e084001c41c0b1502500ca0201c000c0c0160001242c404869100d103039500c04031805201200a0344003440306800341580219401c0310b02d6003034280c84468002c1003906180d071040040c1c0c4250700c0c1d8a4908003081c1c40f44030b03a01000301000e1005882070520300e50415190900c50b40a000c9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 729466546 1250 729465296 729465299
    0x405151e0910030c18170c0a140607060b0904080a09140105121003021f14070305031f05090f09010f1406060708120a050f09010606080114040912270815091501 70
    0x300c0210305030102c482603451054040200850a21002100c21142d50400c27001c0700300c4140c81008020f42c00308909881c82034868001c11501d69030021814022403041011954039520ba41d0084d11a6403942d00c03403295450024a44c2400340d0b00503040310744e00b450170001140e059030788240c080091303590f6810194100410150303110100c07266101580e95a1166102d10443c10711000e040d012502c12460024002401440443c00503050500c2c400c0381a0340e80f0458008040d1101c0110340c41142c104ca800c12607800ca0410300c011400284648070031554035100a010004510102d220200c0780545054002c0707000003040f1050180040a5a200d07203c4610440710605000c072045003c0c040c151014650000b41e04042a104a014464a02215110b0310f1700b00c840c1c3e10304102032602456420082d9001070b110801c04000542042a0381100c03142a12140c03144030544c080c00042c100d04031000340c866484c3c41c01c28000c02310001107451004e10312a6041d9043c3c2c1c0ca0410480c1400d024880014805c07028400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 729467796 1250 729466546 729466559
    0x618050102130e060a150507051203010311030c010906120f090b0108070b1206040504030512070917010e120904020702060c0c13021216050405151e0910030c18 70
    0x90a20180d004511070505468005010900000341c4a04d54007207180e0030108260402000b00f8541c0484a0401c10f0800000d926000e0070000c41840032402488000010300400c41c0d01c0b078024040c0380e4254010a05001060300184c00609140242d05c01d1152500c0d200711080c0d030315000f95510880b030388000d014045d101c0c0707002600d0501c2130107800418000c1200c0401d07400000301c2994040300300200e13a00e0713003030301c0b41d405000050802030025020040d0030801c4000c440d120b4222030380150815541da6884034a0083e070b0805856030300384001d1880c1d06001190400b600300184425500c10741d14401c81d51400d0080002e002403164041c000c0d0840c0c3e0103d808246d200001c42c02940c0508203075501e007012880b661702041284070b07401d4001041c000000202c3e0000c1401d0b600481c0c0340101341049898aa241e000090249010310144084d26200040740141030304e00101282000b0780600f2100c0c200089135001851307001c0241854010942c2c0c840703080c400b045c0f00c2d0381ca2040d200580045082100e4aa21 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 729469046 1250 729467796 729467801
    0x1903030201091e0c0608070201020733111206030f0d02030c0706140a050304151e0b0303030405060c0a03090b0c0c0c09010602030a030f0f361203050406180501 70
    0x2d60036601c0c500b02c0b05414800e00f0382c0a03081e4043c154401c03c2c0014507400e01c00c2c1501c005034080c1c07050341150350a000c070340002100003142ca13090b403210158200844040d2509805a10301c00e929042020341088800e107030100c804020f445d211080010000f81700d50780c65001c01c3c50706070f40740303843c01462123240540711400d40c0102c01801400480c500f5a0880b944900342aa00c28180000f0801440402c000c4c00f00300c1c80c03040b005150098400c840b058545002d032400700d025540e54010b11010000300c8003001103092414803483c080740c035041c0d001d1070440ca02512265103422000349000200040000c0301c2e00350f94865403203180c1d0300781e011141050311b060075203c08105402599040025114043c82030443c0e203400b805580c100c41c00c07035005510b0701404c644200e0151601c0420401104e44510410210b01c1140c081c405070414180c00444070844200c0c58034104000186000d00c0788030b000c40e0718801080089241a240f02d10794180450217480b54940b4100070950034611090300034540b0340325000c101c01074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 729470296 1250 729469046 729469061
    0x2010f05040b090d0809070b180307030503131706010e06011115010612092102070f0305060a1407050a08070c06091101080930070209150a0f1d061903030201 69
    0x4030f0458080b060000c6040e58452810361703a079002c60340044001c1141c0341c00c1600511035009180081c544610900d40824549240c64008607501e80001c54592110808640c00c03900800d8041c0054100d181c40c40749264a514041c0130700c41c2609402400136600382d0041040a201c401440202c1c0d02481140c100f840c49003c017802180d000849a400c0342c03620241ea40036003c1115080717903404010040024040f07403140850380710300e41580034041001910740100c160080095001b007014020760b02c2c0001c5240102e5540c007a65001820014050210141d480815075031020703401e05244c6115214290241c840b1070302005c000f082d0f02e0602c0d03042d0003088020401003845034420b0b200c0e8011911101d10490310303042d19900006419200d0090204202c81d20b07a209103201c040c422178140b4010741d44d0041800000c04843c2c82052010322819000c0605005400200070070710356940b148003030f00b44545240428825030740121200402e07800b10b10300fa503030125009c921031440c24201c0034103070f543d1030040c0c06044035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 729471546 1250 729470296 729470311
    0x3010b0901030b060c0c090601090503010e070906050406030f03050708040e01060210050c160b060a080f0f0706030b09060904020f060301140103050105030c01021905120301141e0f060a02010f05040b 87
    0x30400441c5190501505490341d2100d5003006c0c00101d003210051203244580186018100203041703070001980e8800703101c1c50000c1d40789207028285542c10480c10720280c6a196000b54000c62410204101003680714420b00341c119410319002d03a80e170b01682802d0000b80180e0308050f030102108400000c15031b8001402c222000d40c00740090140760b6490800d0034041c000d00310034010513011904910001902d8402c680d5029030020401e4224a4680c141103141c80031014199100307500001c4402090041081040010310561400340701601e210741c0440c0118001400180c001c41c0024089011542c0e05d5042281da00d07070240c1119201c0d80d403a255114000f400900c0035000c80c0c40c1000100d0b25080201c0d4138140d015042e0014175242502114280c6d101411050a41d00c038021804d00043c100d14100065008002c014210302e10002c0010801540c3e00420f0190400541415001256500c0310144140c060208943c01903c41400380816800340420f420308942c9149000204010800c1246400cad010710704 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 729472796 1250 729471546 729471551
    0x504060219052d1b0a080d02190303090209091f200c030c12030609090319051e270904030813060923210409090501090803010b090103 59
    0x409444001000d41040e0090650b0b004030f4800d00180750761400e602c0c90302000044030903038400075602c81d80c01d20812880c820311078a01010f9412541c6410b10241015080c10009049480c62a0388041e40e03c01c0c4642c2c580c405000c0122210341032601950080c5a400c2e0050400112032078000303406a00c8000340c027441102e13420700018080014489202e4600001b00d5420094202081d01c2c5164040750081d0704100e8980c88208426031a5000a2210350166100c100d111612403c1c460200322141030024091240d640c014400b44c00009130b950f500300c42c81921410990307900c140892040c4032280c100b1030b40c1c0c081004001003040300d01c0c5040380d100145e000510301000c40c840780d4a04205840d001514007800043e0600c000c1460a07541ca120344540340e100b198009640b16039580c8480c01031540c84540d0880014490740c1d08618102030048607c1002c06500901c221881818485064015801508640f55480e200602000703000d501c104003403504113407280d840e90b94504018455070b02241c80030b4000b03170 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 729474046 1250 729472796 729472813
    0xc030609030a05030f06060705070e09060606180f0a08190c0816060e0301090b0711070f06050f03040618050d03060e0f063109060b0603010806070809010b1005040602 73
    0x300110030b4035440d4146540d60b070b04e907072101c201c40e103815200608541e41c420300030895400024404c1000c40014103060203013a042e85400071407603040410080c800c90040c1010001100f40515105103a40720050441d490507000a0f4040822855083c54100440d1441442810b00c246007071912001045441111030000300743c1c40b0925207485090035201d01080020a0400340880c60141c1014010b80001800000314005251600d09400070b0568243d808a80d010142084580d014400c1c14082c0081c82e05400d149450304400500521880e40520350079903020010504024845d04062119000c90306c042c850300100741415a190010b0400e100042480c10318001384840c801d82c0c55034868001d0040b44003e981d1441c05120640b901c00141e032209007001c4a07000003000303100103039092a040700301001588140519000c800c4400900407039205540038001004040c000144d01a40300700b030342c504951191505e0003640c0c00340c03124096196100380030f52002088070394000044e00c11181c80b9800c455a90 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 729475296 1250 729474046 729474061
    0x120c130c080105060309030c011505010e09010303020c0d2603070801061716020a0b01090204150903080a0309020a08240a09050a06020c10050108010207050d02030a02070918050f0c0306 81
    0x480264180d0004141e4040c0100900e00d040341c00b85a0001460003035919003d1880015400c603454000d814030201c842d008140915607118408088241041c0c1d0101125415502c01030350b00c0890611480c460180e4524010030803c455000e01d03150210150380342511319925913008025081181c0000000744043c000090051013200c0000c500c0740c0c941840340c0e80780c0b1000803401104144d280000d007075100f588483c0300040d5111140c40e0080040b8038005845034141110442c0c190500c8100a042191900b001d02c00b0035104405c86954465a04002543c0324035071000c20030b080c42c580c3c48100d0310302039070b446141000e0030010b01e818806040c540050703140d61040362140445030b0400d0041c0282e44940c80107000100c075a4010820302100904441d148190400c502040d40c0003600241c41d1a500461780104018042011a10750225030000d1410aa0344100003940c070b03904c510411840070307212990384a00c40c5515012042140e000343c15640c04d1850441c0c6280e44852249205002780305010008401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 729476546 1250 729475296 729475301
    0x50d1401060f020a0b060d1a28020703051804060308070803040b060108090d0807120c020c1005030402061c0209040f051b03010f062307030c0309050402030118020d0b120c13 76
    0x480b50b00254100319600c0710014045503064804082398608141d0071100444031702803120511400d50002181e0300c071028406441ca069000078020550240188962400603400500380c1d02641000340c018603e0540840001307000d01100d50000c0c1c0700600014444042c0f26500000314801c60062021800645500e001140c1031341045403000120303001400c600208900ca21032254001d440c9140403080c1c011850028421034102c11030260259000b03158064090405102018142c40e107420014118940390300401e000f84504171116507458032050320040d40c1c41d00c03a4107440d0300f4600034104000400320328a1200040100307580d212003030604011602c0804c1503080072079050710b003611281110146800702c10784103244804d004000214111070010307240390144021300b102c2030103070b5641e001e132710960301303028182c207280307070402070103140100010712141c103c00c80000c1204950100044e550000e42481c04001d01102c402036130b002c010010342500005001416100b0040201e5100031420b00e0400481c04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 729477796 1250 729476546 729476563
    0x151005010f030c1107080a0b09010507090315020d1d2e0e1e0123060109051210050a0f11070c05040e1c0801170a2001050d1401060f02 59
    0x1040d0703691460324207220f600603490054032401d00b510b00c1c00341071038030506200040d00402c54543c0034910080a10040c0d0a445800102c8403008003d1030a05402c0100040a40d00001e0700c0620340711030020800900358100c90714800300c2c440801c4440300c080c0f22208104181901d4450300e00c5880010361124440300303800302c41100030b5030416001001d00c4840700050011805401114003c1c40d1085401011590b607525005102c0e000000b0200649d040076441c00400c0348080201c12041e030b0400986982040f841d0b4250303801201c64401a680410600780b6004030411290300d41402c020900c40d550040d80c000045861100740144450f06003000d40350320303c2c000e510010b090204901d004012504044d840b4080081c029402d54490000301011991007540c090f2000c00003d218000402150480700390f100c4881340c107400074215020132501c1d958000c214144a0092003001078610b01040d0f802102200c6142640a0051103c0028010404c0da0854244500004150492200041c0f544040743e0880c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 729479046 1250 729477796 729477799
    0xa021006140d2d051006170d140405060a090807062a0804030f0809091006020303041203060503011e0f0b030318010c02420405040b03030f030108151005 67
    0x1a8a00c20030340b9841c2c00701c1010350412180f050400c001c1500256604900007226005100411125146114000481c0c1a0350312480340100c0e004204084e80030b000c9001c00803121245054040503200c414214507500c516484642d00c25000200407040c150825003032021901030f002a50021655420280c030340500c5c841003012903041210325150903004290000b01c1c8503010f516a58140b44d1030f03a49a1400780d1035003406032010341012401e51100c2c030301040c130154000d88441c0c6513847c3c10301d0010301950302d0101620003802c11080400a00400b403090b40703e440145030050080c40303172080d82d150400a00110b440c001c83d65500307004007401601401e0090002d20324002d0000c51402c51011610712002c100c5002090410000c1d01e120805a900c2e4100800d00265001d0a180228002201400300300484140008002402d642021001c0c1c48101070f10110740e816507000c0f9108450302c0006e4207500c80e420301c2140c85000400081034101e4002016108900c04c4442e14000b83c580290713411300044541f00c0c15 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 729480296 1250 729479046 729479059
    0x1b030606020721110a2303071a0c0a0b13150b030c060a4407051603020703050303040606080709020c0601090f0b041a0312070b01030b0601020708030a02100614 70
    0x102020704040f20488a00e40201403811805001c44002101021254801c080310003d000c80003103141e4101014200301441180100071007460702e810621004080044402c2411000c41c486110301d034103210141d4840d40c000100007280c43d10120303061080c4c0024205403148007a1259002c1d10001600c40e00700c440c1802402004d11456401c00c10991f64002c2446100700160040c09141c0980c2c0314112108000d501c1082c2581180c6210300840001000b06104044402181c01d010034a41c0003030132281c0010f042c6c1802511421982010703442c082255000404900c000401c00c13041c0001e6a000105913101c81050710b000b5a5503421a9041e40112140c10b0b8079500020010030034038141e40d10501c0d812550307140c049003901c4100001400c0b40c013141d00901900c0c40c4111090302502d010b11030600c0300c0110018441c10b010640d21521507540701400300400c421050000f148142c0c1c0200207400007081508220380d03a51144000080d1501c0700e5440c0050001d0801102291305e03e03814030842d04004019010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 729481546 1250 729480296 729480329
    0x109050609060f0408101b1b110f0607150507080403080a181e0318080c06031512010e190b0f040201030b060d0506120a030c030309050c041b0306060207 67
    0x2007190552204007002140320303040000180c000000c3c400e0825400c685500001d81f0315a0743d100303003180944582e0110412030f00004400b2820390703036410171640355080001400c40c0fa5402003c12001c1001c0c410300d07070380810301013410810060311080784414802c400d0400d014a031a40c980a40e0b4030700c01075400038007041016000030102c080341d900820854180c01a800211202338440d010800510301c12100443c40000d2a401030641142e00321440320440030143c0741851401e14550349540503c0031480c07084100002007043e031803100c900000b0700c0720000e20b00f640702c02c21400780d640202000c1c05c40c85040d0291100d4047c0c2103520060014009400401004032541d91080c0030321214030041049051566074141903079281c45102c0903041c1403a003068006440e0600d181008441c06c44184842c0066104a0043d00003da0140301134400076414180446c0b1540b46181c900c2c1080030280c001038001d4540214500b0300140c0520290920174240c604001460700e40b20700301e0300c9408501861000c00c1d000c5030b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 729482796 1250 729481546 729481549
    0x5060705090f060d020c0f0d1431211220010213060201060503010c0212031305030d061d062412010902070302100903210902030d050307020c0109050609 67
    0x7003a18040003801440b860342110006007042e080184e521005543c00b1031690380e032002c200300341002403485500034800c10052000040c038911504030900005140405c81c682d00c00810b01114214400d80801800b0551205200400c0210a8030401d52400d81820240480401c1010300407041030300706044024440e0030b43e02c142c800032488021150300542c1d40c00b500800000c20b102400700084004281c4840300d03e001002800e481c441c1d0001c62180c1d15040101c80300d240c0004805c00c41201c10302089132650340324003445441040d1400081e006000000d01e004089050768400d1040c2c400c01c400e403a510100710b040022580314110380d40d5410003408500d243d0840300c8041c00c81c1d9014044c5101c1c40c500060100f408805003030a9010011450300401c0120402d40c0501c115407422030b161004100a09054800400c01400c0ca0259200001d6815003a0094039141e00030000042e000340807110300c41c5c10140020416801182c4000060107242e00789142c1c2e41c031407681002203072002030510f81001000c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 729484046 1250 729482796 729482807
    0x1e030d0c2313052e0f0e090c12060d060f090b13050c041a06070b06030d1419030e03071b09150e1e04080702180c030a0c020c03010f0605120a050607 65
    0x4e00c0c940703c85840c1d103038640c00d84580008100e5080c516a80d00c08640c1041e4400361042c1140d180b103034401d580520410504600a0050b91100d5001819009003034481c10003164004514041c003504071810844140c00c21600d139000030300800d2141d00341d2540d1f6520300072030504100c01030300d00411580100300c0700c0380c151800350000703c0e103000d08184102c0c100d052900000e030150b20600c000c5480075411001c12080d8a01030001c090400000c1c1804507040303204141304030651051800a0840342105169900b06910907400b4003609103414040ba984c84009040002c0741c90004201c43c19160304074080400c401505014442d4182c1420600701202c80c1801359400407a035008000b20f003c03018903aa4900f020115001c4d541c007590007030360015503400b010f0050180c0c03080303000d1100359000e840c00d090001d045200700490b980704044820002c1c81e030040300012070401314107001c19070740342d8200790100b00c0301c101c1948401308444040340c0c4165002c405a0155413901c0d1400009082c81d0811000901081c0c0541d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 729485296 1250 729484046 729484069
    0x30b0916020c0108070e191806050405011e210606081c0306051c06020906040e0406050708060f060a180b090102070504111b1f0212181e030d0c231305 66
    0x120080b04840e1640c4a41c80323914601c01034064400d48070803040116051600c0340b50701600181d000c031440301d00e8440c030383c026101c464400d51240d44c510003000042c000c0100061400d03264815024405141d8601489960344c140340e524550071038120a290f88103034003e2045904640c1c018200c20b100170000701d110008a813140700292802038080000300789507941c000041001d040d45010720350560510303052500c01c0307441c0140100c00f84440ca005110003030b43c41048000c01d180007101c0c00c0d035440310880e034210b4440f1807012080622074080700c008a96801010068003040b0307005e900f11f4014550f907038200320940d01c42c104e03002e80c414010440c0c00d601d40c0c001d11200f041c032030074403040f9001c1c0401064000d00140521003603403049035001c90b440322504001c20000b5080444003800054020043d80f03120348034401b5842444400d00d5003d0045903158041c03054070b80200e0f40100800803034850b85005850305408503120900b036200b40d1042c2607040744a5042d100e169200e0b09e5005001c1d030600c07003409180e1515 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 729486546 1250 729485296 729485329
    0x3150b060c010606020607090e060d020607060b0904050d3c0917010c092c130609080a093002010e091f0911090f01030b0916020c0108070e 61
    0x204035140210301c0c240500ba0060402d54000e0621b480d050344001c015003019002210035000b0320040c85220307514a115580c8841d01103074001ea4800e11482c04030020405d110743c507604404064104414080003007034a01d041503c6844014a01e10b903a5180d400525201e80c04e1502000c030503840b4044072160568a82d504505403c2800302d294a4149003040120a01c1070201c90f0b82d100c1d038a0f224030b642d100701c0da05c1c010690f052004500c0c20002c10380c09600d6004031026160110300000140950307400d402c00b8a600c9410150030813142c00300342048156503100f1503c00000c907650000006504400010b060620881100001400403080f01c8000d4182c000d070b04203a040200800ca52071099a03600d481300d010f08510601d14032905000070442010205680c4070f0075400d8a4900402d010244103400c60f11a00c10844030800304404410040c0c000f0300b900c0902c1c0da000501101001f1000035040221f4461909907000c49440c0b45aa600450b04140c007164500001100800c400f00c15040606501244004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 729487796 1250 729486546 729486559
    0x10b03190b1528330e0a030602030105030d050c070b07020109090c051903020c03091201150602030d0b0409031e0311340f120203040e0c030103051603150b 68
    0x111100040d003011003c56402c8420b22a01d9004007440551503040303030040c4001c2080d80b01102040300c0031002815214003076185520b125005514851150300e17040900c00703004101d02001d80d12428000000d400034090140207100d0742c44020081c6005505035510302c80620000d01145081140440345a00108000c90501010040c04112500c0e203000c1c2c0d82c00d41c891981c03115110180700202800380c6a60740c900e0414144100300070218500040203c0342e10344000d480d415258444510a580149000030460580c072003407503404078910b6070100040c900001213840c144030121080c0300b04130403241c2450340140801c1c020542d540c03040001100407003011059080000e0480300e10030384603119920510b0705240c4000800c1c084409040702c03202588042140820054903000d0b1f40e69102d010000d00100a00200c1e0050041c0003910300c204110340c06010055007030806800c00b90b900c00352941080c08200c82b18000c0e0b0080901c0b44000740c000d0011a43c100c6440701903145240416001400d1264100d90031a5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 729489046 1250 729487796 729487831
    0x1208090301230708160f0203040315020901090902130302041a09012706050907030908160b0f0105010f080408130e040818061e0d021b0f010b03190b 65
    0x10360a100b070110001071090400308081504541400300312005100700309020420052008202c9000c4003001500c015041555803070307100600036442d5024690004003004500303107180526400c0768001e000c00c4074080c1c8410702c525481d0030400c13060340034030f00040e0080031420100300094034040c2c0021240921001c1c030501da568001011480703910090b00800c0c581c3c2c0e40410385030280201c801400074070209029082215034180740004005580140c100c208142d22105040107021070382e41201c0c000340e1400446114521076151420310381c1001c41e0744014041d25000000f034294040c03440403030800001da0307c140c3c0e5561143e40c2d210154100d295194850101a600801d13202000d200c0c083c043c502482076141c45958040d9403c0d030100c041a85140900014484d00c40c4280d80c5c84601a001d20384d0515013030321981744a61101c0240501c078140030f1031800010141c1c001000104240b00052141402803040101c03200030f06985000ca6010860281c00b41e852050115840c10003464200c00c0d2040b6404142 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 729490296 1250 729489046 729489049
    0x8071d06030a0605090c0702031b01110304060201060f0f050d14100e0f010e0708030d0f140c0d0f0b010e0d050a020306040b1509010b0a05090d0501020d14150604120809 74
    0x2900200c810b480110750700c02c4103000915040c2c4c0411750103a00d80c5074aa03e001240e0340800c1d02c4014510740c001d00c00703103c061030950a80c010143c1080d2044841c04594540d6500c1000a0182806100d4028000c03013414001c607141030314003004000d40c2c401401d0f15640100702c0da83e90304929129501031101d40220610990b40118074040e000621440fa8010900841c0d81c032003031800c4811049000740d00d03600410003000080d402000355025400c0022000844020003148000948845410300c01d403240c0403002c0042d01081d01020b400700103400b4104000c0c0242c400035190403510304001c9940850301390516000340b450101107900c00d040c031030740984070252170f070780d01103890a1030036601128078500607030170040c4041c0c01202901001408030744464180d4500605c00455100741080c940c2007050003e840300894940185440320194400021942c0b17409041d4441d0041121441c4552410700c1d80d00410518840030181864010000f04040e00d0503281c07001480440d08502411074910b00b0520481020b03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 729491546 1250 729490296 729490309
    0x3030f1805040c180506030912031305010c0c150b09010510120207140d080408090603070e0a0609060201141005010804021503040b0609010b0a02061f030804140f1008071d 75
    0xe030503141c680c9004130000c00340320000c801c0943c100c680540c50900401460301000074002c030405456583c0e099494036030b1206500c0d4008102000345c045d41c01c003030030303041d100f54050084100742d40a0100c800254842244020030390b903a0415884e40030080794014040c83c54030300412080c102240c01c1640380100d01040800990700200030a841c100507500d417941051805016540f0b1402d0b85240400b440e02d0700ea41c8950181c0550442107004000210015004078019510010080c2d0010052401c0f1030f95404010300804190040340300650a11000c0d01500a00c0c041c50303409444541c0c500401c050614004540c40c0100400c20799000382105001804401a80002c44c001c5c0d00600e20000d05d850140c060014040042e401450b28100400140c481160702040c49504035012200c040700101c40d40a804a0750005500040c00c1000c000400003012030329245110340540054a0700040c500c4c110f0f003000880560f0160300c1c1c0104803d200000c1506100300104c0e50642406000155482014008182d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 729492796 1250 729491546 729491561
    0x11010e0f0108281a18070c02040e010203130c0812300907031a0c22150c050c030c01020736050406050a0203060a060806040e16060f05030103030f180504 67
    0x3c49035a5000807856004000c1c00c6241108800e4607842c403140351410480c0740c09600101048100942950b030075086580780d41000314260b41240081d510707414441c01410010030540d030102d90001c18043d0010712603401141916040c40300268007400c0c0f981c034118168540721840e0031416414140321000c0a00748034940405d004540420003016018203600c1d0008079184142c0c405800c0501d10000c122444c007012085600c1c064501480d8031251060019807011085590484004022003503100c55401d640803000341303280c030f000b030382103500c200d940c8000e00d91503140400d0203e006810049080c01000a11010310201004450000204825031803030002c0f05c035900c00b050070006440d00244000d10809018103500041509021451402c14400040081800d17101310002c1c0040d1200041c00c40d038507980140e855100400035158040d24a03550409805024052040851029047c0343c1e8031900ca007060302d069980c95201c40641020020782130310183c40c6c0074001002d20700141800309007501d0300d0050b4403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 729494046 1250 729492796 729492871
    0x108060403090602060c07022202031f0b0f190c0b010e0a0c2a151109030601080607080103062408010c0201200d050717040b0411010e0f0108 62
    0x92505003480d0080c941a00c0e9402201154800420700840040250864005a6045541c0a2070b1071311005020381012562680409491011042100c146000c2078900075910300c10040d1554107455001000f980c0c055000d4005034200c0a0240e115110700d500052500c1e003105050013613402241c0d07510306c0781d400000d801541c5030101300b01c140b100701d10481c060100d644e040c2e41050403840e50b0f09000019510300000c00c0803650704402400005200c2d600c0e04048880000d61000d1207071070780140311080c180d800604224064071518000041002d00443c849000d0807035659007501c0c691950f12540045c009402e00011719601d40d01c2a90f040360040583c5800400700c010000c180100d40f0765019007110340c810250280224200a494101400d42d811100c40c01042c01c400150b0b51181c40c400c0b0752106080440318100018501130100f4000441400d0744103920400281c030410740c4d00c100460340c0d02203034200c1c2604600d4009040b1119800f40c0c0c4050350254032600b42e40c1d054154840c210503d0800c525258 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 729495296 1250 729494046 729494053
    0xe0412030605120d0f03150803090906100c060b04021b0c09060d1a0c0c030708220e0f061c0605091002070b01170c06030a1a1c0201120f050108 63
    0x408464060060318010304040712111608224040d58944900c3c2c091200303020002e00f030070b07200d4410740030754032101408131041400641e9a032500e0010741d80740d0040005500c10800080000e17850f00d803400c085000e1014a550b851007d000555900c0040d200502d589075019400f800820803040441c90001c0c0c00d03031050001440358503038200500030240c0003d88400e0080300240344400c00300f81d2000a07040300c0c6880c1c06079a400c0e96207400003524540616100385400d80000621142400241e5000e403000c0d110745001030500001c0c04405401c0c0061b82d2041a8010010600040c4030f03060150f0b441e41d000401414100040441043c844010101d8110072900641d8850601420980c00c014407450000040300440c501441e603224880001014428510000311542d00c86031041014882000c0a00001c1d00041d241e080030101c4c503001e007640031b018568000b5020040c86051400c0d540f80b803c0c1d43c98420342080c1011040d0011100d060380c94030b4003011640c80c0d04010030107507003601c100e82c020440360018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 729496402 1106 729495296 729495323
    0x9060a17180a0b340f08011413060b03010801140a15052103070606061b020a06140f161a06100f110610050a05011d190e04 54
    0xc0a0100704c10442003400818400b0300f0985103165444140d40d1500038081125003e10901c01c0c4409600c80d131054681e5400c09181490800740183c402055850710b031155030805030700c00c8c2d020350f0060717544000c05041d1a00306124590001042401131001c210302c0c4c813007200b02090601a59215179000300f00391404400e4070240300d04007200402541c2d00c0d0803c90500740d000301200d01c507174030107e400400002c0e59030582000b200529030740184000030762420060300322240e011419060441d1507040191400707420304200034011500341a0800d0002509500c0c0c1600924800e211581c0c281c40e000040c07041581d03810741d2001c1c100301289004011310a071044201c60b2080206001d8146002b640180724180e170142c0c1c030304410b4510a403503110381d040c1e40303100442d04920429880345a441d100b000000d0a07251902c5490101111072008004050b00c544003801c0940c2c0c15a4101c0e042001d220784e = true := by decide +kernel

theorem cover : BRFrame.Cov 729316546 729496402 := by
  have h0 := BRFrame.cov_init 729316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 729316546 ≤ n) (h2 : n < 729496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
