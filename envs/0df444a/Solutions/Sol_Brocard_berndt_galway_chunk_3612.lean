-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3612
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:10:22.367476+00:00
-- url     : https://prove2.me/submissions/3b01e774-a4ff-4dff-81e4-c7700b7d27ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 649460431 ≤ n < 649640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 649461681 1250 649460431 649460531
    0x1020a27150804050a150218040207080f0c030c0a080a020631050c06040902031906050d0f2901150201360c0b13050d03170c0f040801 59
    0x14001c02100b8000a02070000504c420b10800d64800521804104040c003140f01035040141c1006524035410390070f184d0f52625201f2110000e601445803810911006204c1303245800040c0807030000d020401040c140881d0602081800d180302e020740316121102030100a1a0000040405080e242da88040000c1d0020f105c0003040c5119598585540c40c80e4246055402d206800c0d02854010901003000305a9103081c1e00650311036903400d080d0310840e600c1c0b0b6036100240d51452003030903086140409014041042c00c0340c18140d16000e81840b5a8030016403c42000e501084400d100c0a900e40c07000602c80e00340c8000c1c10a0380e1300103510091145442540041000e002c5250021403034020080b80207107440d14420548000580100492610790b9a60102ca016a4042d142d0440d801c4200311010499140010521540c5a096615080121082040c04417007200c0540501590107040c003450a4031002c2e100104003030b0840344004101c2154042c070038208183e640000c1e100c480c07011740c0c0503a03001c0181c90318 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 649462931 1250 649461681 649461719
    0xa05090c12070e090606010e030316020d0825020111071406130b1308010c0311030f091905011b080103082203020d030807081807091d01020a27 63
    0xd07031488409140d40081c0381180c0c0d54044000c0c82c0d21030007048400400443c2651254200781c03103410310028032a08240e26807140d0240c2c5081c0c3c00c506002c00d405820038940410303841c3e100b11030861420315400300044188485250309010303282a01407420444d64040c110301000c4440500501107907040c41c0d400389840300d030030061130700035100490800b061440f190602001882d02c19502961401020050781070101c00d030041c3d102d250b09016000340724030321910401c00d14200f110510740c1952912886540e07280e81c00b5003910400d1180e400c136103680e04506070700030200c01c1c030480000500c168110459080c40c43d00c050500180420a001000881c0c80d50341251001d1001d082e1a56803803180c10440c1048041170b800180d0000c41c2007040307408040d0040c0c441406502c60b511483e49507507c1c64800c50386090000000b510079040072400f04005a0250172070b0005846404980300c1091031500220708a800c80080500003075a00c19a104a8441d074407544045c00071205e43c9403200743c1c00d01c00c4c010702c007250040e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 649464181 1250 649462931 649462939
    0xb071106150108090a0209040506040c06090b0702100c060f0e010f0c05070b0a091e050105090c030304120c17010c0f020d0206040f08070f030e03100b030607140f120a050a05090c 78
    0x40d1350280920645013113590040c040c0c8800e09040c01d2481d80d803201190111420301c1c1307403c40071500ca070061084404a81c1c000290903c1c005059003406182084816800d0502082d4070301400011001e005001800000c20b0380040d03400c4103c0103040c00d445007203e101d91030134646000c0c41400780d4404100c66245070046460000d9032201c6101c000105194980680148102c641c0d100e0610000880412a00c0c043c8009001c0e0342c54a4144030307203a0301d04000650385580208030801501014922114210f4000da19a18000741d071890720f01a0102d07444441e10151f55100c24503207040d600544e0130f0340801d0062004102c0d8080460703010b541d820020700054100d040090303038441040b036134900720380d00154000e0007004000082c1c0ba0292410341c4ca0480390b0b00c20f014009040a580c0c00500c540860301600500034102a121040152481e0707206259181404800b0031401082c400c00400403c250003440203904c140d4500005548c04450018040c2c1070818107003000d01124003000142da25100808403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 649465431 1250 649464181 649464197
    0x109080d050310170d0908012a0302040803040f0e100315020d09140d1b2001020c060f0702100c1511190206150102030a0f050706060509040b0711061501 67
    0x4a07103c400b03000a5100715181d800c407040c0c07210040004111062405030f01e031101c01006480d4034000b400c1e10340c0aa83d014106000c1400d000040c451084c3c1c001e080c41c00c9003401494951941c1c0010b06691250b0410114035500260400040c1514a03809600940300905603507001c0c210b07a54490000c41c4070402d00020f58002c80c1c510300044144d841b115410303030700c14040b0201d0034043c3d401c5601c4020740220382020a00014120490400d00700d10360f5507403503102007024003c80040419082c1c01c42c42685040c114802d0403840110354580038020141700903040d20f1152210000c5c41044a10000700485504000b0215000c44c0000c10000000c0300c0d02540d110040b5807015110008213050142d100700a90a08000162160150b0007280c064013507a0103c800c90641c915010040e40d0383d2265500354400071394000c001c2c050051081c0c1c050513072144516404a11144d07903500141140b001910152850011907040c018025004007442845010b043e020300f0b01481d2210303042000c03865080505042c0a411 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 649466681 1250 649465431 649465441
    0xd0c300f020402040f06030b031c0e19050909030c07050d170a020c1c060f18031b06090305030609060d1205070212010e030a0f02011a0111030d050c09010306050109080d0503 76
    0x43c2c1c060300c000e0641a11040201d0341d659178020094801d11085034028000d41c0c5a1203554001e805842c00e00d0095900e802c0c030700e90f030f1044c1480301e54100700200f40c4500c00300540c04038259031442401400303101204019601c400c0002185030402da910b62203d4400c0e0b5001055600080981c80070000361965803107580c0d281d04048a003a404c00807801801d940c0006400c00d400c2504001800403403070b00e07024020404c0101c030b4802c4000d04903144030498800559055008071300003403150341c00180c1c2c0c0241c00d44010391001696913180a84001100403004540e010040101504040341c100c1c2e8003010071548030031808580d440300800c9060002220040010005190042d501e400402214500c5071400800c0100120a03055480e0b0b0400310706d00c40091031180d610721045105000d80c00350048a003c608044800b40f400544108100d041e01700400e010510659050070214482c0328814040000d0140d030322000f03040014110b440d0358000605001e61410180082680000d000c0d020340c81c1420400d0303494680d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 649467931 1250 649466681 649466689
    0x100e0a0807181e0504080c1006030b1b040806040b150118090b120f010507090617010909020d1208090609030705070b030718082a0d110109050d0c300f02 67
    0x307120b43e1810000d0070141403001700084940202000c40080e410780344140b4496140710f007510700b54030001d007200003400d000c203803030740320104e0181c540700e068800651505540703c800a05000b0300301c4041e038103044603d08004000081c10401c10b40d0240902e4510500107510a40a01d451014018000035a5a455100d440b50303d500300742102380086d0078116812040e00050701e81c0078180840d002800210380703190001d0001c1c02404412001c408a90790342c2d85e140e0800e01c1040081410400c2685c0c4a01c8014081d40403030001d24000204071910794036011145401c07420300e032400c0d101412030b02541c0d0040120346e01040740400c146054440354003110343d80303031200401224980c280009000e205540c00100083c0c02d01c000a00021b80401d02250440c00c489507040c450501a026440942204900c8803a00c0054040401c0810144050429011981d11080132644d0008003440c11110710071a8a406e0080100305204a084520382c500c0e100290043d07542d250b003d000340c3d510001c001100001c040821591 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 649469181 1250 649467931 649467971
    0xc0a060e01110f0c0c04090201050f03070c080c0309031e070509090a050312010906050d0c030b06040906150e0a090218070903150f0c0c051906020702100e0a080718 72
    0x480b0030912030310344001200000a030780c0480080310962045136100c001038201030048125003078051f19418100325200307040c841e050340010146810401c00850060000741500b02038615001c5a00085031901940c200741443e00340e20180c0d800d940c5154641c01d6080b03c10000c2c5400554034140c42c10483c6854880c030180c0381c44070100c0c000780280000316801c500c0c0090420028125500314900740440c542d20810310003a90604400580090600301d018030106402e89a02c41d0850405800014144110b4842800703e8000841c02d18100700344034410015200c001c4082e5402c01904103040108214650004080500c8030810b0701000c100f40c8001030040340030741003030700046821406c1c01c000c00c01c80d55121002071501200d0184041c0c505040c500d0301501c0b0b200c2d9008003e0340140100725240c0144800110a680f850045035907503003c104000041e01c80010300418030b01d80d40c5410360b20b032a04504002e000c0c41035411280c0164010101080340442c04601c58000350400300700050b49500c0c500104a802d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 649470431 1250 649469181 649469201
    0x2f090f0f240d0f020102120a0512060609030a0312061e03060e030c010e15130c05040b060c010905030904060803030c0d11072111030406050d1116030302030901110c0a060e01 76
    0x202c42e1000442c14443c41049000026100740d09031041915510410b03000c5001c4c008102d000600305001486000060702025500928010183c40c20816182d0000c2c0c901051284201e00041519440300900d42c2030707008800250104a1010690f41c20400129a002e0414800949116207503280b0030308420081c02190b0101d49010b00074060f00201902d516a11042d45480a042d003200342c00252030440c1e40d0004008540e40600305850f40ea1500081002034079150200a074000d0042220782442902445000e01c3c0c0380c49200034586a80c03170365040100300c82e1258810302440e0801c00030402811110411a403183d19846030006103042c540807010700c1070084400052803100b2102c50a0224200480c2e1504210225510300b04081c40320802a41c4900991207041c0108400388210003000c4015003180d810640d4044410303041c171011482000c2c3d080e0a07141e082c1c01081d0f0000c203215403200b0a010b02c4900c030401201c264031340341c7c1361000d042e5203800d52040074000d160b8a0b0a08070103041c081d04030901e04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 649471681 1250 649470431 649470439
    0x50a050709020c102c07060e040b0f04270309050a0801020c2e05040b060f0105250525031406060d0201030f060e09010b0a0806040503040e042f090f0f24 67
    0x40e0445c007030303055680c00c0301c0c0140804111003068841c1545024050b2085800780500b200746088018802c1c000503080c60b0140c400c04000c184080144002011920201c0074001d0391031a1001c0d18000c1448482d24030340d044501c9a13401040190000000010460a03070313901c00081d00520307000e640700048046454860340200700d041006010500c00300c2c0004d680503d4084842c10b42107003103040192078500c102001ca080201401c3c40d0052007090f0f0100103142103016105a5800d20000c0c0c40f000ba501250500050840445403010710510036080c44014001600d0f200a00541c18008c00143e030b9412403d200904040d03e480018510881f150895002802d89042801442c1411196035020308240c01c2820300590500c3c400043c00080001c0090086410001540c80c00e4103122400b050200001c000b80c3d0000000100c8800c00d1510072091b00c03401c2c0c1c00005d44146048242d080040d482d801070503c0000441640500480c122140107441c2c10100489007004541c41541d0344183c4170780c51116050b48 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 649472931 1250 649471681 649471751
    0x10030c090b0414010f3c030b0106050f04090e0102070510050601110a0b0109020c0a0f0c26060a0c0314011e0608010b07020108041a04050a050709020c10 67
    0x511a800001d0100c40850307090140214441d111007500c8002d1145500c20107030308908101100d00a040564101100e1403500403800c3d1070081001c01031500100c92810070b034444010800c2c44141801513001d0803051400b01d15294510306400d803039001e107004141880b69240030000013031001354122042c02c0d42c40b105566441c150404070100600382251045d0108441c40840305404c41c000c1001094030b54014511a00d503400c04240100039080701a150030184149855031011644c0c00341101411403054158550250400103401744048004907400a81003000414002c130b105e000c0349065000709801000940d15000341000c42c040c2c601958040825060f01d400811046040d0303003034014641100780c003542c42580d00c8600300c1f4050400d102c0c91008140502c00c400040d0b1081000e203400c40d01919203103140450900f4112580c450a50302100d11741d112044032030407c2020700c84000241180102142099040c42403561505003d54424a80b20368070303d41180c0481d501034504002513080500a12 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 649474181 1250 649472931 649472939
    0x6070b0703140108010204061b02010e130623010c02090c0d0c030f0b03070b161502040803071b080a02010804140304030f201507240b0109050a0e070810030c 69
    0x1004002d030082005008030540008120108140229405c40b00a80d1310020a0910f820132216540110310080303040081c001c920300c0c850f9507000301c28405454100b2002602e2850600540c8409108044081c0d0a00c044078095880303030b811000c40c0c1c0708160103a4020800f5680c00f1002d10302d521a25041c10303c594078001c56500c140d5490b03400106280080d80e01004044002c20030983c2d1811180f20b82e0710f500d48104400d1a404101d800e004154071310540080380d61101d0111407030b0503a04141c01c13103035442c0d101164007800d00c034400210154900340440510801803c0180c4252201201d2101030305000c0c050000c07604104100302c9d04003a070700b44c2c80709417a229601c2e880c182030407280200041c0c80112100c1d03110b044240c4170710145295001e0040c2001c2c14074a0a0b241d03550160004101030300d05403070720402d4040b400e03855002d504000d02c4904001801c4c55410001404000e29030300720b01c1c02065000e10a01c1802003074001681c004034981008200740d501c00c0c8040b1040e183c187c00003880780244050004d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 649475431 1250 649474181 649474187
    0x1031506030c0210053603030f0601030b090108060726040b100e091c0201022b0c0e0d260a02030301062703021512100305010c02240606070b07 63
    0x805000c941d80d09541000300410350b1a0140c850a4034241164000c3e100150f4a0740141002106402d540c600d4415200c6440003040d82075800032a0122822740c21401041681c1da498421501c0c0a03030226070f0300c2c2d000d5041802c000c1d510030000f0146028008074020440510b0050700700e0036036103070f09503080c0c0c0301d6440c10340790582040700e042c3d030ba0035080c0400001c04105a14000c201038840c1070001e000b440b280e514081e0b10300010031780c0603060042d55420400b904010b00c100e00303802036010780040d0026148a006405034101c0d04040096820415060758100465480904c8403c50903040541c03800807600b540c022992a41100c00341100e50f0350009483c410440e0044080d604a4940c4e407a9800c1d0b280c603104191414218914455403002c008a009000602c1d0031070700031014500018a09050022280251a1144003a10520090a8a00d00800070030000740141e4100e00ca192020b00b49000d507560050340095500d0740c0600384c007a592000218a13466100a42e500d8580260b409219401d08040107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 649476681 1250 649475431 649475441
    0x5030109060b030c031b101115070e0102070810090819120501051e0118080d05070507090b210c040203070509150301050612060319080307080a1104050f0103150603 72
    0x110b0080c02460380340d42d8545400702d086c00010207603d40b8420b58034052400c121111010200120900c1030740401040000720800203040b141d00c800d83c1074403150502d00800b8045194090846046620018060105000226040075000b120031404a008060361400000b00d0050000c0b5008203200c5448042002d5400303105015808841e59040040e640c9880c20301c0314003407406420b090310804101181301154418400c03140350342000c0e040452020740301c0040c141010042c1d411280000c0b4040b0340702d4140701c0d00b406528005c3c050b50740c00300650315144011800c801d01c00502817803208008008241008070600015044001c000c004560344c1c5401d4402800b2500050006030080710708003030301003000e085101242d041e100d00030030050a002542602d004654802041c198160007808840c0c0006100b000c0c00d00806845a14015128980320200030040140100b0078202daa08007103081c02d14803480412101510301c155211102c40700100010f0740505050a4002d4900c03840c0b15001508551642c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 649477931 1250 649476681 649476701
    0x60b06070c030b0903070f080c0a0204060b300414010902093102130c1e0503040b0a11070f02040b0a171e0c240d0203010f0801090c060f05040503010906 67
    0x15259013500ca241a55907280500304009044140f40100c1801043e800b60140400031205021142c49001943c0460301303a900640c4a100380d084085240241d84564031400c142206049900304c00460034500c3c0c4140c0b000e4043c0000d042d1414900000c2c0161000f908521104c64000d0242c0a179810300c1601050641859404080d416107403007108990002c0c56502c68000751b4005109200480000001c0f900820300c208843c8240300d001c001c40031120072120b000310062402502c99644a10b05414181d184010082550b40041d14000042c1d0a0740c1510f001e96000d1030708580440f000416520102e401802c60821995005d0680040011940041c1262400b85c0b01140c0c15a1f1100e450301068004401e01b040304ea115542080c502c3c0c6000e402c1820510710480c2800c8460001d00c20304501f80010340c0d000d0b01403100403580000050005080ba0300240d401049158003c20001d40c403600c4c0d0301c100c94414090350701003001010909040340c0c0320340c4c10380c0c002d444001c008101010003450008014101d4071a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 649479181 1250 649477931 649477943
    0x100c050a092405090d0209040b040c050d031b08120420100509041109060318010c0503061e0f0a1e061106070302070501090c0e2e12060b06070c03 64
    0x1004155540040c10001d04004818200ca0030340e41e0031001a20590810303140d06401280d171407035000141e81c41e00c541074095801040c5241e194280b6003084400090300b03800c1a8000c1e01c600b039294000a0b401804641604041e4880360640081c0d89030031f120303e1054403011aa40c4665070700340410301044182100c40030000041a111003203c6905000740b80c507091403500007203001400b4020700e90800c0d0300400e84000b60244034134680300c040000610719400c2503458100101500d44820070360942481100c0d40c18409090070780c2540b41100000b0b40b08680741d010401c42c04c448280504242d1241c0c880b030343c0742800080445600a444105004c04408030908801c845521010000b0703400740158140c0003c46031203006086540e99451058001c2d520910040702c0c20341d40c8611410204191317100c2c0c84041c0544881003a0f03a81032842c880148003880c441c5018000e2210078460003e00c141c43c00d5541103030610100d6031149205410018000e00c10a82042d030030400000700b200402141105076130a0382d102e04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 649480431 1250 649479181 649479197
    0x90d050c09090d050715090606030b0f060d080d090f0210120b04050105030c0904050705060d0b01030b010e01020606120f0a0804060807020705150d0207021e030c0909150702100c050a 80
    0x6084039a890151940080100b0810007910300843c1b20082c441416180300700c8081180c0f161075542400b1605030b40e00a403100138140b420702034640d4148098642114049481d00754004884d01c0e0543c0c01d21031154003020313055403050f1000800080640c040c00041d00108034504440e0072140c081c0c120640c40e800c0082c0c15151030303010140e03807403d0b101d1641a1a001380c020802100702d0024030610000251003a11075110b69000011199103000060528072011940807904120040014043c1d900001d00581880380103a855042e5036400985254010011500d5145144007100414200045010200c0590180b14000824000548010320846600340e03650707000740e038070460102e841d04003a0051340d52249200080b01101942308001d40400481e480c0f0051800d00c2c254006040d0045000403420b802134013003c4041c140c5000c1c42600010501503c2030010f500e05278401d42c0c1c0f100300c00c41580c44100c00040101c1d003178a1007040300600c0500c1542c800c0000e4500a01d010381142c20051a04000411107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 649481681 1250 649480431 649480441
    0x201150504180f14011b0311070b0406110f0c0c03121e030703020c030a0e0301270605070216030c0e0105041a01080402011b08040e092b0302090d050c09 67
    0x51052140c2000c01d0900040000700340c0d9101c00c03407243c80d01425202514107444440701590b080c41a82d072081e414810f40050f0004285010702511000310074200b07062024015040411403140a46074000da0000d0300050180d8900d04980c980e000f20302c009804e03950042100d10380818001603124035000214102e41c516142950311911600c240da42c4a03003c110203488444d005001c2001854109005007400350500d80744208092442e04044107040014031003001c0039030142801e1155160a503405010340c1a801118507292441d0514510020184d80d5100c4c00a15550310030300c05600441c01130306220f000c10b43e4a0900b4070482c1d100b0b010303011990300090700008040c5401e21810008403045401c1c028400c40c400b0064400d2400104141d0501240601c81040e48a02020441145104000e6140c07075604013443c0c48080b100080212615038000a0401203c110300541003100103101013030300f9040610500c0c200c010380034611250b900300001c0d0b0780020410501051101c81410195031042d9542d40b6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 649482931 1250 649481681 649481689
    0x3060718120b040b161b020a1a0d0608120f030a060302041b031a0a090b010e04020309030408010b06070302190f0c06050d0e1518030715020a0f0305040230010c02011505 74
    0x2034482c120100b9500d03035588601300c0000440b40c010600041100f00300315543d109d002c0d0340c1c4114542c40d03541110000703102040c800091045c175020340180e0f80100b00d010080d244800c000d20034140340c6080c1d840040300040c194016600900040c56000c0d009202c00e0808550403110f140d2001c1384c000110b800c02c0800103040c1e852030311111140300e00412408840c3d1801c02075000414051070000e040014141d1984040d4a0f00d000440c05040058011643e0302d2406841c103003141d40e80c01750f443c4030f0502049440046035001411440d0700b0086d09941d01402000e1404540304034020030028030800f482c0c0070018120390880098440503104c50400e0050100010741d007a01d40d40030b00c003105001e031000000710300440962040020004ca918007101d28014807525481e03180001902c460100640008400d11180d5002c0700070742c03448044d400d05100e41e080560029070a00704145045040e2459503541d0400b04030148200d46100324450020002201c0c0008000d0203400072400341c02c4400c1c1040400075403824 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 649484181 1250 649482931 649482961
    0x71e1a070309051c02090f1b0f04141309060203040605010b0304050a0b1e01030b010302030d090b0412020a0b0a0e190509040b060102030c1b010206011403060718120b040b 75
    0x581656480c50003820700c0f04100e11210301550700507401050b003c5010042c0c0750341e42460f00641003801c0c0c0d8200781c504600381c6d00000d20030f44042001402c0a0009203c0030940700b090302d066640800d1001208030a03403000c1160f400c500e1110094013030500c8004000e200d0300c0d038015405203015030030501040e80c135900066524032007035070010034a80c803445e51300300400c1200000c1030300180030860b02d05030b414403081e5802c04030030203030000d03102d10380c26a0041085260030403820000510034282002050b00e0024880005d00903441840c41d0800b0a5021408555484546c00050420700340d00e135813500c045800080580004000340c50007060b203c0310001c084a0b62110420483e24009c0a2007200c1e81c0e9a5202ca200d041c0181055041d0710003803240d50400c020a0200c4118030760403001103140001848002403400b0010b9100365040d418062429030142c0b80418802da1048039420280006503090442c021010304552040c040112400c00b2101080040b0b404c56005070302840013038107241c80e000f08840200c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 649485431 1250 649484181 649484183
    0x80f040305090118170105010905090a080a0305041a0906190b0d0201030b0d0b0712050a0c1403041406070903170a270902121608070917071e1a07 64
    0x1001840903020030f40c0300c0c401402034401300049042c282a0340e5600c0e166041400251014a03075141c9006200ea00c03000c1c070610398000f00810040c107c0007850307215078100d403080114650805031558001018055860800610146455880302ca21305e0000030851f16103c041d280c4420101051300040d017920b1007130180d040b941300c00030050300000115600540c004d00d488480140c000f0740010810300403d28450200388510015107500000614031094a42100d000920081c1c3d014506400301d011258055aa00e0100a0100e289503880c0c4640c01c010101031130b0055030707441c0d03803241c141000a2140d01900c128101e900c200b1b81c2400c2e00d01105805800b038004c400340b203000a5004c17201110381458603070b10722000c03640c50158401c0890b2114030b04001d99000c0441c0110940d01c810602c4801610306020300d0707052440346800082d90800c46401030514042d17209903043c0c141c00c0c2140034060032042c0491001401c02d0051090001c0c038000000d280c0d000d540c4600018588000d02c004040c04c000002c0f82c40b1a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 649486681 1250 649485431 649485437
    0x3060f09030f130306090c03150203010e07030b010c051b030f0f0303070804150c02010b0f09041703100807030f0507061805040f02040b0a090f08120d090302011503060606080f0403 79
    0x1048458103100c41d0b03900007068000c4403142c448800400700380ea038861554401d024004040001d42942004030b2010641600003500502c1000100310100d044428a50411440e00e00070514825800040b11030422118004d0311600458900800d0812050000440d03100144c05940880f4410351280ea1114103000407040c5680081000070107283c40303104c242d0b91041c40740c5040b00070f44824a0301a803c0700e04011058025170740da01380703000c0213141000e82031f4102c80c0c088070b00403003514140e0f50303066820509404540b00c1d8000400481c08647d01001c440d0080c000c818222410b0030750302c0c20904a00d1003400026640e50180390804280036103d210480c19071900d00c0d400d50107040c03074001840001c058000c1d82c2081c030f99080c07101040304e9120600a0005178140c0d50382d0a2018186515508084110790005902d80c0c0251000b2881c1d69018081c5c1c0d44501c00700c1d000180a90b0355040c03d0b805000034446204100303660120120402089600080c2945e055642d07445166503046590343c1d00e201e0543e005404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 649487931 1250 649486681 649486687
    0x30708010213171903030b01082d2d0a05060922050a060e1c08070c0201111513140606090a0213090608010603030305060a050a0302060f042303060f0903 67
    0x1841c0c151801d10502030352800100d5044080d2020144c803a140c07803080c100c00194889654580d55a88a15225040706048070425600c0e480481003443c42c44e09013801410b54060000024400031906a031149409002c10181f011200300d01810500582c04464010106103481c007c030303c0f10305105d030341d10744030382040404644607081203081c48d0000f03100300c10116218440c6c46801e10009059010300b00e41017000c00010880c1c2c18045965414082c52502c0f44c10402140a04222039594002c40511805d074080c2004400c01c01c404008070f00b8803414a8148000a200c4004d019004e10344440b02c0caa440d01601d03a60314001e80c4981060346070b22050346c00c0787c0c0c010f42c2e28001c0343c205145940146025222071260805040d03807410010240c0f8000c0d8030906444e50349840800174550103011b903550180048640d13005042c00c00002650f0080302d0700000e0b00480c40880e961080380203e00807035010740070028101100e0243e1010a80408480c40c0c441400380c021b0340042140f0440e9201c00900a400e0f820185003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 649489181 1250 649487931 649487939
    0xa05120904051b120c090402040e01060e040903080a0b0d08160b010f12020111011803020f0f1606050c120715110307080f07091e09061a04030201050f2205030708010213 74
    0x984d02001421281d40680100020f81140c0e490348001e2004003d808081c46480d850050064a04050001d05a00440c180020080080d0380b20f602d107a405090031100003150780900307000c10f02600480d01c0043c0b16140001d40311059104601024110b03510030400711510b6030300c41e99a040c003541c01e1300c01d4a6491140c10101c80040d03028510000c00d4201c04000007450041041c10510001c100f00c0f0b09401603000350600010030801845a11031a40798030000f4099040b40d001000e550752000d1040d00704009011440c0d000c1039005102205003220348121081c0c80300c000381443e11802d201040c040007041e00d883c1411a070801d4807070660380f062902d901c0300211940c3d80c0d19110121341005124004000b811080412144034102d0300c400f1071041100010a15800d00407107500326642074000814012600e6000d9002c2d090110464056a80c20300c3c105444800142c00c249081c000d0481c901c00204065008551150a00d9421070480700c00328211511659101002402c0380324500d0060998500018240 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 649490431 1250 649489181 649489207
    0x1804021b06100e063001020c0d051321141603081b0a080a0c1a01141014040e18160311060901080106030c020a05120904051b 55
    0xc18852048091900441a2021401c0c80e0044855401c100104030b020b114a500e21079803503500c00760a459405c43c1c14641240680c020b0501c400c80e2858080c05d400305120440203405072071084182400721508482c1e10840075040790000140b114840c0480a40003680c8500d05001c0a818003080c200540c43c0c2d80c180e2035a03142184500040c80d45482180074500c02e94000e42e00b0740000314001c0d1703101c544800c4680501e5929500c02c2114813002e0748944010030200e02c0c3c0c1c200300c8094060508245020300114136210308007459120021606060060001601c0030070b0b1000a10342c0d81c4100d03113100ca1002c400c07001345c030800400080180ca0b1f01041c030042c0405c00c5030740040d40e0040801c0e410700d481341041140c810314100e00100c0c04002500008002c01c100160303500c400c10190b40448032103080c02d00c4100001c1511005100b20790030182c030b900004078818001d110b1203050a0700041512844140c48400b92265400100028001da16180019951209550b4921212040b540b002407420341034043d84 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 649491681 1250 649490431 649490437
    0x30f03050f0601080709080726010203090c12190804050907080f070f0203190512090105011802160c0303030203011403010e030a2109061406060702032509020f0904060b180402 77
    0x6000340406d040d03002c0f590b98030810a1074003c01a100500c0d03c8208140c4245084800e1417002881982c014000d02c140a6000b0551546c3d809007500c9100c03074008e012015514042c400e49481c1e843e0000d800d8424288400c0070000c00540701c05580d80c1c111901d40303180468102e5000c5913311694040b1902080f40d1502c200449044030000b441220304080700d000107003400c0791910640b070020a80002c0c64849a00c861080b07154841c119600030820380d85046400f40c0b411030454410706100340d002139943c2501c01400d83c00c0d55040e82003007240300c80588a00e4054002d6000f80035148402051440800c250300e01402008030307940b00d090182d81000303d08041036401c03100b81d002c02c24251a2a52140388c03092200c0c0f1500400fa405114007084480f040050070703d880c2000b41005020396010071102015890001e0098100201161105030420180303001405101054112108190001440712154001200a8050b01c50704880070414a9940d20303c4c3d240c1d51040d50880d161801e90141d8103c99440c0981c05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 649492931 1250 649491681 649491691
    0x1809102f0c0304030614041a0f04022101090501090605010f05060f0a05040e070f0806040228030608011401080c010513031103100609020c0705060301120620070b04030f03050f060108 80
    0x100e0f41010344030364411068615000002001c1e0440b801007105002800310415100c0f0004080c0b4002c0d402c04070540c6060110041c4003a004885c0c00c0c1b214a00b4409102000c01460032030300003000090392601c1c1450192154140c252081810407001040e0049040c5845003210001031046141c5a003400c841c21141c0c02c040c10176414810300b404000b4101040c801210300c0307900fc541c1d81d50b0802150040241142030f000d00114091441840011070030404015500e86d071a44414031001801d00018048014041c150050101942480e5142c984080f100c03007014140d50703044060304c0108441e40c2c011500c80c01007000f02c0030755608480080020480003603807508594800350540c0c01c1c07505200445419142c2c154020078416500103250b035500074042c4500d2018200c100c4081d4955407400220202880118002504031681c41c200303000e2081c0e203155011101c0f43c00814040c0c0380c4d0082d0a160035107582c02c40c1c050300401c170010f4540d40c0e22440383c407031103118005071a510105611090b0044601480041c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 649494181 1250 649492931 649492933
    0x100c06021306110105070311041e030611090a05031506240a05041e0602100b031905010606231626090307090902030c06091809102f0c 59
    0x1c0380034080c020703504000074000544a4020003507209442a08445004080b00d007014034050720000d000f80312500312404c85490840d207031007818241381c0014404501d0340c4001e19540c40c061542044140e208003070404030074201c40b500102c9680c2c00a040c3ca4041a4550003102510b400003c0c00707a140440c1103001d100001902d90200369140e51040c2590350010b910100810380c04a000c016481c9103030b450440703250400064100151500c080039569440203485104000e445141100e6070b604c0c01c00c10345029205102000078555820f0400754000c000318021034001a40c10383c03c440c0c030380402610f0181d200803100c170381c0c5d45082580e85a548501000380b40490304004010001c0340d00d0521400151245c604002c660340d0b40d02d070500300305860900560700100c4080c1c00d0400b10340240e6804201954081802d0b0b80d07407603849290b00c0010302c241040e22501410400d055041c015083c1c0c000401444c00c2041ca1810850405690680c0801d03c03499144860215092807856500301d4a0340c3c081c040b0034070000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 649495431 1250 649494181 649494187
    0x314070b0403050c12010c12020a11030d090201080702030a090306020306010e04020703020105061c0201080115021905030a0e060306100c0602130e0603070e0403080703050c091804060b0f100c0602 86
    0x180803050741c0180d2007921198800c0d600301d0241e2405c83c02c0b000c9103562036002088010f143e0381d809040e5903c0c070201c03140410340c0030483c0b44145d40218420b0545d0b618140c1525911048140c0d05801481c6018050b800207440308002801c66000000f11078020800d9221446402c1c511303a20030003e136200400341410005283c600d20400d82361800a003421920070f80000c40e40d4034092090100c141509040452415250307007a410160344c10060302419110385154a5079100c0200509902c1c003054039410002000302d0368050000e202c404006880c0d800000c1e9600140e413220b01c01001001c2c0015640c896200003408043d8100394003880c0001c200910540c405800c04c008001c0c848048043c41e03001c8480c098501007000913030310381841030380090280041c03c5134503810b1640b001000780c4002080d1405055070b07200846c1c11020f901702580e800d600d00509405003910110301540d03541905440071180c0b24103184007000280f400543c05290f0301c40281000d6800300711070500300d404140b000340c2960015420 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 649496681 1250 649495431 649495439
    0xa030204050f04052b081005090421080402060f18090a0207140a11011103040519090c090503061512010f020408060c0316140c16050a060e0a031407 65
    0x60300401e0700c2a000c0c00b10388003842c64641001e5044c0140e4000c00c10080040e03c9840580320309107401c0c0740c40040107141c400d941d0b0752241d0013041880c14941000d58040e81103010041001461010b451801801c40301c85e0f85084104841a10b03605025a0002d41c010410b010902c600c42800c0090811401e1000c00381d41a00040404a00021070684140c07000c82e80009441d414429181d401c046000c4031400100810b401d603450b22015240c000e5640d60402c080d0605011404030108242c1c4c015080c010030b0340a09400b0008950600c50952060002e11810401e001c840507000e44100310031690054080c1039a5a140041010b41d00d100b0310000e644000c030728000300c118410900c20913000c2c3d400a000165240d040404031454682e00401d9044400d4041040000265900d17402d1020619281004401c0c298841d000f003400380102c003d0b40300184a02725406042c00340f019003c80c00c541c000d407801031426440d11000c6030424203000626822207000a0708100094089160551002081054a0100e034803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 649497931 1250 649496681 649496689
    0xf04240903050415090b0403140709020a030c0e0609010207090e0111040e0601090f08150a1107030201060f090204030b1306020415030c0306090b090f04060f090803043e0a0302 77
    0x2121030650000304045020701c2180410f41544400180c036050603445039141c5400a14548a0741c000104151041504408208030411044001d00450541552940d88090006000b8400001c00d5030001f0403042403400301c1c0c10884201c0761f5001060b40603000c5036040403490030182c0f090884081c0c484d90f8408504403507441040250000d40f150b17160710a01c2d410400001815806141c005283d100e50001b02004048000690030704000c070000000e20169880b01c030350200a0a000700e1060340c11304c0005684003015410340c0700300191503640590101154850f2014030881c052804000c00d00580d01d00840c40c41c45045080340703017407441240b0261916450316902c500440c50201c903000800c0e142c0000c0319107981c140c000c41010700321786042040070800200024882000103481021010b6098012800b4002141c01246030044607200a000c10f561916000c3c62540c8110380586d0294143c0200342d201c402c1e400700481541154903040000402c1e141c0740e415103000302035203580d84500c48070000401a21 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 649499181 1250 649497931 649497941
    0x31030141006080105060301020c07120c0f0e040506150f1203041d161815031103090a02041a0d1211060a0504110d021e030a0501060b210f0424 63
    0xc003803804150907142c0f800c820700351040600014400d0740140054011307140c001071180221440c55505800a202900740305058080907004007092079118000460069900c41c0d43c1401180300300100e032001d03619030000f4498020150070b03460380890135481040340c600d0544010380222175450140e03440c10380d07600e00105003070a2815100e58991003510800596003a4400030300e600700c5050412129099130940212880d10660240c4251036000039501c3d0038040c404e600a651314002215002d17030f80d0234903205561f030b6001c0c143c0b402c900c0b5034204020182039040f00700540700e8450015010880301c040a41ea0440c200c2400491041081514114211010b81c2040024000c0c00d002100251a0800d81080000c4c2240d42d1507030750150b02101c003002d0040e180c0181c1841006a6417244000000030000081c1c100091442c0180c2a507003807400104400c1c41120082040c401d08220b549000300155000700109002104c03191515030f600000a400305500c011441c25440031618104d203110280400301007110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 649500431 1250 649499181 649499203
    0x60e07093204050a051e28020c0703051b010e090f090f0106032010021519020d020a09050d0506010b0702120607080a061403030412020a080a060203103014 68
    0x581c654040c0000076001c0e24061201b5803e03640c1000152512034080c0207121042912011080350758615152a00c03e16410703a02102040e8040c0c0d00140e0723403420400c1d6110ba0000d034041c000c20f07864081006c10740c0a03035098a021840a080c044460303451480d4403412840003840315840d0701804100c4c07218824280300701000342d40b02e21003070743c144031601404100c1c00c007586a83c00d02955134220003a18448d00040d21000c4950307000c88079152a558040358000a07681d000455215500104603100401483c1e0007038102061241d6442d134000f6590003c001001021002c050b05c5504200700502c050740812004040c02c90001c2d0811002d00001a0094035243c0100d0360b0030001a01c45060100a044500070781c1c000b041c03503d045503480c3d000103001945070302c59031182240c4020794580c0f03e0115114043ea850042c6008800c0e5a004000c41c104a406940110f0f41400e0f84d031002d800209000e04a1000c400940082c000c1c0070b03800d8048103441307141441446c00c068446060080c01070001103010021100c800d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 649501681 1250 649500431 649500451
    0xc0607050102180409033006080622080d020315060d0209090705040515030a150e04050706090e04060509010902101218082a01020706060e0709320405 66
    0x900f500e40c81402150106904040c8605c0c00d145215000c81d03441481501c144007410701c1004100d105445c58030524008004164009060002c00164040042841031182051000c40300b4220907003425160142281400103056010074842d01405003d1380d405550301660668448118400d05400104250800d920340300c0c010f0340001d1540003900309100b155801000d50b0510a00706410b101c0013856500043c0c0c0200584400803002071611481030b0000150031100103055948103403129000a05083d0444060f640d61103081c10010b4690310075500c500466107001c038042415100e680c0d920000c0d000c058008200c9649501404016035902da9078403080080316100c02c1d8200d07031060bc4500980e014500004201442044440c000c01c0a81041b103100c6100e010000090304659604003170001400c107041000c661010030303100700f0003102d0360081c02512180e100e0402507544101e02150300711450301810100d407810001d80c0c12030b1005490310a00d007401d000300d200341c003522a10214040710002c50b0b0610340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 649502931 1250 649501681 649501687
    0x120103030215040b0105010e03010b0a08010e060f07080c0702063c03040b0a180c0b040e0a0b03070501031104120b06040b0a0e13060902090f01080609010225050c0607050102 76
    0x8054042003030001e800004802c080883c0f9140d2a4003440754014418541031207a1910f11600d541e40c01c2d03100446260004140c0046144c89004060080c00c81d2048100306100e54404603001000324421248540400d50303520303649036144149203456800c091012600144180460400203480c00c02e0000c840980500c03141010788155a1502da104544550a181000420a02000c01c10100030380d903005414940104040d229031003424250154500c0141808010000100f01e0340c030300100a0003180d404e00c000d05129101c000f203d8003200c1c107103031a032581a0700070381c01004554080d40049610003e44030046081641c3c2e01d44402c08064444000c46013500c094007006824134003841004a00d60084c0c1d151840a8282095420015400f5019810b440d000b002c0050030800349400c030358082503002d031002e540c5013400500745102010a004446c4140120310020740303400014425201044001c84440e80510042e02504021303441c0008191854018011601682c2e1110401080403500c6140010b80e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 649504181 1250 649502931 649502933
    0x50f1f0f02011d03070f021c050604020315132330040501050409020c03070f05060618130b0406060f0305100e030310051c05120d180206031803090303120103 69
    0x42101c4202109044181200c4203c0540c024000305480e9442d80c81540e11101104034000640921060005040500c40080c00d55007003000200b0020b008078421340890f01c18000c9650340c900d0100c400c542d4144100c03103240c00341d004034407800000c08025610020000404684c0d51140d4148110601505201d0006605080350003034400317081401081485030f1141001e0500000901c2403003144030fa2480c0b25004a00414403803030030310407256070940c848041c0c20b00c00c1c8180b50990310b611044030301c140720f1394207509050a24103000d48560b1041003030326035281194003160341d040c04e42a00580305490722940d031b00b40810445101c0c4d50400c081e500441c01840c400d08080c0c0204103a0742054114209900140203102404c2c14905802064030b8084603035001400307200754414080305607c1c401174103e1044170402d8072031070803100003001501e40400d07061100c05816000c402c00701981040080d001201040080c40c4880e0500074400c55491844c15a450043c105002a1450700302064200c031000310540104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 649505431 1250 649504181 649504183
    0x1309020f031b190303050324031c080a090c060c26070b1018021815030105040f06080a0803130c0e100602011a01030c0c0c080715050310050f1f0f02 65
    0x2000f03141042c03a61208040c25950018803c2c08080d00d5030b140340c030380c803144140300100310920303540394076406000c42e03014400e00043e03280050140c00889004c02c511070080f4070213003003900441c000c035034110201254162410008803010004080142c841407045000c0c2c1d9808030b1483c01308203403051544001a04c13120070341003100203600007429020384140d5103d17040001c0703070382003420558504615134010388540074484058400c08250705403590040055070900c1038800343c440511706031201a5820882e010b900760f883c40807100140684450303588902410000111002b0042d5030000c1019203101c0e141c811555103c40007025900a041c00d0214507040007a40b0720003003000401400b962000384020341070f030f0550314910300c0c030840d406040584843c5840f580e240502c600c1400b081d070203503002c8072096440901c02d03188c90190045800c4955030f803440101540c8510305480c010350760400c420403100d01e01810018a042d0702907a407500010f620603040e414117078070500320280c00e030a901c510704240e281190007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 649506681 1250 649505431 649505449
    0x120a110f01020c0f0a0b011a040e07030c180b030105091f08010f200a0309110a17060705070b2206051501020708030c0706050d0b0d080c070f051309020f031b 69
    0x13200e9540081d44010205542c000740c541115100f910a10500301142c1c0c0c007903814400c640104006a02c8501031290496040c0e00c0307040d91041550701c1c000c0d0000038007903d0042a0291107410b440c04001e100500c000d141810103241c00480f0046812138000044020f44074207801a84400b0b8140d40d540d25007a080c091030702900c0d603400318008454003618000b121032a81401040c0d44801050f0b9940401420804100a8022145001845004155075440c84140c070102502100f80e650701524001c202081e000d0819100c00540c07206185506907543c00744038002001d03191007180070203a038140c0840031410300d125890003801001416449890604d00182c03400605500c0390ba41940100086044540045031800c19601146086551140e031601c0300c2e005401404a0b2a80c00760780200e10408100c1c2c1c100081500d000011305981c4000c0e90707034210790100d096a00c5015081710700391f902030b444c03842580d01c080c02041c8000c00103540e44007400046842d00d141d95201d29804030f0101c850000320300d003681c20 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 649507931 1250 649506681 649506703
    0x50301030614060604120510051501120605010801060c0f06180b152805030d0801080d0903020a0e19061707050301181b080102030a05010f17120a110f01020c 69
    0x201031040c10a03001207a2217100b035106440b100b100c14a41c2c4c90820a0905c002c0b4004030305c100040c812410001010700071081a03070b41c5d0a0100c1d0107001a251b162009006100423240142c650726030a07843d1010580c0c550900090844041d280041c000000440a2140400484014003500340700030886c9840c1f0210400030f80440440d8000d080c06541d5507603892001c10f00c550700f542d021000300b03041070341c1d055481c00240c014550600039840ca081900c1e83c80410030b412688820103c0b80c2d02e0380943e0058883ca1140d00010b50814a0044180701750381c02d940d142900700d40c15001a0410700d040242e11006c03214a070b0440d143c001c07864612211283c0082002c0006000c04500811001ca903c0c200c02410440400d002080d1401425111815503900e848141c018401400250750720715182c0e56040050100340250300c6003c04420f00800c01e0803001c00d030540300810000040940c0203007105000415000b60844e4030030400103200c050856a000d109900000001c03800140c2c03134203000300b40c8600f400c40c0c25070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 649509181 1250 649507931 649507961
    0x812070614101a0c03040902090306131101140f18090106020115150e0d08040e070903080d1104150207030b13020604092a02060f090609030d1503020405070503010306 73
    0x1080c808040382840d42202196410f1000b085480d9040c0c04a034400e000f02c3d8003110300c40c04042800a24092650000e040044003141a121150f6588144c0b98000d200600082c03c480b03409031400d95154040d0184960340030890070340904203d0307900b000c00c415030f01c040150040c412509425a4481c02c02507642400b400f10350000380090b07914120345900c13602c0f26104824400003644da00480d05c1f8090400c2c2100c8141c0509400101c48040c2001801030340544907144100c2d540100141c1203030f10a1520308150f0760b008041d1454000f8442010014080943c0442003550007000000f83d02030104140c21645501600034004091450a1018401500034000e0050440c004c1500b00103070740b02000c603002e580e245d040008114070070204444604010160940c050003040701c0454130150001002c602c21007a03078283c942c041d910700000d50384039074080e2000c3c105940180006004d842c815088082c0c070361403660b00300303580301d90302e40020f0140d40041d00c202e000300c1c030b0020042c001e0001c42d001d036107500304401d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 649510431 1250 649509181 649509221
    0x402130e030a0807050f0706150924080c210708060a0c02060108070b0702010804030306050405010f08060a0e0d140c0303072c0a0302010e040b0a0303030614010903020d170408120706 80
    0x71050740c403030312134040c1c010b221b25a42d0a927903421701041c21100000d4000f002c401c0080c40102c00d5290441005070380c0090901300c00c1180051040350020754102440b070003902c405590400601814211380c09a003030704595000322100890b9001d0100b00c2c080c07117140141400f0981c1c8c100c0000103400c10300180c010b503005400114040c056944224202d6111235420311741540207681e1400d0480c0101f40c1030304516445814080006803c03010042103209540e00c000c10f0302c3c42038035950251307401c98460b40000410750300300050b5011424010405c003218203441460f45890981c190b00482d01f9a441160444045400c0c45e180720030400203920184164000c80305401103e200c43c00004061400c1884000d0401c6525100c032026515603400800018802800c001002600d0385005405000325000e04807100d2070a0b05585020b40c810401403049a402809113694070a098079070800ca48045400440000d00c00c00001500c80010402e1070f02e0448440911911003200f0700d002c1c002e4429000c0003049030b025038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 649511681 1250 649510431 649510447
    0x1614010c091d040b0c190203130902070c1e03020d0b010608070804210e0418060b040603080f1b0d0806150a020309041a062710170402130e030a080705 66
    0x80042c180c1c020741c00c00660070080c5e440c07a1340c08440c1d200301038400044598210603c86c10300d4001014102c0c910051070407114031034a071003540c02240582d080183c0200c000e03074400c00800d551004c2240c0480e05241e80341c160b0a40302c1e00402c40301c101c03034030381100c4a6520390010071445511203901a004410b6107001038040c1059150030b0030311000041e151007030a400602201c02d00e03015034911904801c01410a020050b1111000b03401c603000e038942074070b51606020ad00d08031441c0512170f29054982c8450004c1c18030582010082c03980c1c01101a90380344501c0744e508a00040020803019011100c03c9d61110202e03c3c0200501160200c1c624071164070460501c040b69800340c002c8180c49440b2400d0724001444c1c4442c47c548020900440007194100c1030009072a00090240003400102ca0100400c1c4032030507038000148000052407290450004410890040c0c0c1801c3c1c1107031440d0070500080005001c081c41201c00304c100d03003290205141d079074070004000e026140c010440760341c400340c2e03400d001c0c5c10240b04c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 649512931 1250 649511681 649511729
    0xd17070912032609010212010608070f08040f14030315031f380301110c1207030c020901060503040b15030601060c0215040b130b09151614010c09 64
    0x403104000d0601940111142100540c0444542c0d8562140460150341c107001844c64002e40c41041c0c00401101c50b4400491f40c00e0143c00800e000384040d507611444040703100d034201c41400b001760084594500c902c2c100760124480c01c200102100062000c1c0d40e0341d08040d850608036100441c04180a604032842c8400303605109090080400c07080100840d001250550b000300746100b12140c0c10b4034003516100400c190181507140075440c070741617000b000381d00280300d0038032440d029901c00140b06600c036101c289000a06d000107000024403034104011848402e81c001840e403031090b0090320026401004000900c158000d85a400581001e00511080d01da800840d4540d14140101024443c01c1c078075000841d01c0b00c0c1c11507180120300320103068540b83c0b01c8038942d11a5000e030704042da800400440c042414001d2904488011200811051221541e040300c0e00b80c80d000b20b600c20381d95407a40218100403482112030b600010000700000128105203180141410f800d0360441e0740b070240c040030b0182a01803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 649514181 1250 649512931 649512959
    0x2040512070609060f200309120105060f0607080301031101090f12030e04021204030818010f0b09010602030f03070309030e0910061107260a020a030c08100e2d0d170709 74
    0x950214008001b01204071840c5109a51680d0b4121a5000e4286034414041d808a400340c0000c0303840340d02c00c1100d442000300354000c1c40c40207444c4800c10001000001c0301c0362200100e640060510b41000da5481540b041c2c0031110b94070040c4032003038030101102056070115648001c04412030303085080c942c6180d2140f0b40f50100a0000b81404140000310300c0f0080c0c90556a10301d9520700700240420100200040c001d400c412032042e0043c460f901c004075003240003009851180c071003544d40c1c1d81140c0e10144101d02074403c9002c20340600c82070300d00259840d195031700ca151003120b60761054a01035260440c010181210141404240c1d0461002070081c24402c0080034088004a22404400c0c0c522115190a06c02808402507019040d84400002c000d00d107a001c1007101c0d145010346416842080d04403041d0f4604445802d07068020b441c8000001d00ba14141c864215104100c1d0821140d00c015928134003241484040c011481a1080c1d02c1c6149600ca1360643c0941c1d1441c20080c180c8c681080000251 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 649515431 1250 649514181 649514207
    0x61103180402040b0c03180d05060a20040b090f01050a050a0c140d0f14031b0715020412020a050d08030f0a02070f060e0d090b03010504020a0302040512070609060f 72
    0x415000c425001540ea20380580d00608850030728955104200c0781040d1746d1390b02103510084000d04500140c4803515142403c84015034000c0040d24199035140702e103c0c000d281c02d0b2485000c50310b401c502640421000c002420107445401e000c2690345980741e040256070b504400601d41002410000303485174550000c00d6480c0c044003414108515a2945841e0341000c0c2d000d02c1500043c4602c1714980112039200d503d1201e4041c6c10b45400740c1710110507030402c0a03480101d5032007000351a0078154a84070009400185415801442295103a0345c00340d2845e8180e92141d40201c203100c0440d101401586000f02a81004003821200f54400d4541c41d40c1d500c40c0c9002c0100703500788000d852070000316840ba1603011105100d601210303452846100d1310705040100a070510002075440390002201c800382c06205102d00340e070b81c0490412706582c40e010801004c2d520644c0d2000425400388000500750310303100ca034140396403111800341601a0402000809540f09680f21000b000302c21059055002c0d00109032800f42 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 649516681 1250 649515431 649515457
    0x15011e0914010e0402210a05100303051b0d032304050c0904051203040309031a060f060313021c02040c0504060518010c0f0609110d08160c03080a0c0b01061103 70
    0x401c14100050f948506503085140d0010b000046403441000c15108126480305140c042d440952501c0380e0420444008903805281c0010510062001c24002d101030019009030101d103820340d40765003800506014410b8330080c0465154410300c0000000c0c80c0700d59500d4804000c022a03640352a48038640c0d2150440c0d07a00e0702581c100c401040a02a003031110b0740a610b4001c49040d80d03410300d89401084c140086c401a5118243d40507040c0703e40d0040b1098034003801c070003004020184626010003955600140104500f00350104407140180c0b5008031503d6001c0c02c0d41592965034803540140000e4500d6501d0240420600b00400c2c040d07150010241c80c00e1102e141d05004208070140c0060300c20403112070014081c41c0b9940316150400080c3c0c1c202c41d00f5140300e00e54030440e0240c00e10600c40c0130800c010700244000ca0911407072914626410032209160300a11903002d020390b80e40c886410a5100d0040c650018051072000c00501078480d07000740c010080352900280802026610b541c80340200b02c2c0c2e000e04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 649517931 1250 649516681 649516709
    0x11209050703080f040608150f1302040503010905011a1c0f050139020304050a12052107030306050d02090402011d0613030203151b03040302070e15011e09 68
    0x240320303040140303070301550388604001d40d95007213504125615041171040c0c10000d42e42c0000039580c884070a011841712000a050420b540fa01e034001c00020400e0140140d0030150309000000e80c41d0303824099150b01d94001d400004043c1c03846c103c03140202d4410040c20380101c00c012101d8201e0543c010720300c408a42c0024004035401c91616185024101c5000380c85c003800c0031940300d005000c60802c40071050541d840040300303904c44215401d90710380c00b40d8440d0301ea0104050100f0062220740403031112417103124405440150312910000c0040102d01c1003401c081900100d1807030205505480f0700000390404460700c5059542a40c0091001080188001d04000414020030342090508038a46c08003407000300310302e8a50402440c1ca54008205110a07846071052600341080e1030311324880e903802103074409520458481f1039252512641d001401c01c50442c45000400145480d80007a2903000c3c03850a103049c010002460001040035120705e1180184001c0740322031026840c0c22503d400b007107903405541881 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 649519181 1250 649517931 649517933
    0xa0219120b04060f0602160b1b1204030309031a01030503030109090212120c0d0302030906070c17030103060b1314040b0a0914010509010509032104110d05010b1509011209 75
    0x2019001c00c1c0e1031550000e041910220300e11101c0309421080d141240c2c01c85030b1051342c282078050011074600c81d02148080400c10720038070303079031201882000c40007a02c103c40d80004020082441640710b58020340016480020a004001a0700b00310021080034004414040d419030301c40d561030703201c10301c916942659220010001c42d21190790b00500c089021040d9940320100d60201c0d0100c1d80011103804003030080c0705107080e02c68040e200b41c0b030007852603800910195588100903a2a042c003007000b991940f002c00c00009150503140c00440c040d5118007c00320300001901c082c85246402c642d20300e61081c0c101454030b950b80e600c8145440d80300b5000180e400050b155925000c00401c02801c1c054500000d003101711652110540215000784481d800030411607a511000507168050382640240e030003e075400c620f4002040011540d08a401400004440011080060700d150a9881c040300c440c1d44031007980002d0701d403100300340b02110041400103162000c1400000c0940c28264070b824401661454800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 649520431 1250 649519181 649519217
    0x20a090302100804020906030a03020a021201020f04090608120301060215180f0a020a06090e0708070201111c060e010501171012030203070b221212110406080a0219 72
    0x24021900640304280c10141e00100800a80c41214168042c420300c1001c91102d081c0043c00c0445250541e0240c0000c401540c200007040e1000305400c00190b4007400340d02c0740d80241070b0046c030060240d01000910649008a080d00b031030750a68207003420520510040140680200d03010300c8070710300f8400034038159440400348e510311011446000c0252041f115006d0503a00c0004000071900c1c02200d0b0160700654829045441d9109800b941d007490499601094045020f40e03001904002d05000103d40301340010781090017038100392200011002c0c1030003403610b460094401d0002920781907170341c41015810680081d000e10940c149603040605100c0c00940d010a4080d01c2c01e0103007515980d00c1c6140761190030000e6907608000000d891140203031020a1070002d07198018252098001e80b10b001036003868550740c40c0440c0a011210a000520b55030f0017940040e07209034903150000e40011078840741885001000309130014400d108280c41000701003200c206003845038290315414a05460340183d0180c180c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 649521681 1250 649520431 649520447
    0x403050414121f0e0d02030a12020c010c05120906060609010c0f29010602060f0c0c01140907180b182703040e070503160e0f060c010e010b01050406020709020a 70
    0xc1c040600030b1411001e007000f60300c0700390b5800050411080c822070b8954000b89440f250000c000102607481000f540ba9224010101c640e001c0e0710030ba60050130080311000307950070360703c0001a080025900107003107210121400611900280742400802e9185030000c04290340340300300c00e461410b02100c502c4a01c1000303400760880a0760342d40300544604c84280e540001c144840014a21803110350498004901e0380d1001410714490b081c4064040d906072a0082207400a6000202005055490340ca000314050002c1702060b01900482008001d541d1800310b400c0507a05034003084001450804105d023030540e0796001d926054509190320a00640c5850380350a520707180102583e00c10592886510b030650b00e01001030030480781520071002c510341d01d070303003040315544001c0310810b80100225401c80035480c41042c03503034030440380548182078075062040001c01e00d400c01d42d8802c461ba9111400030444400c2801000300f82d00003804d1090a1070309015020f503c6400c01c0c004c14800550200b0b0000149203e1518 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 649522931 1250 649521681 649521709
    0xe0601060e030f0714030f0a03050706090c09020711090106030b0d1b08070902070b0f0606070b07090803070c080c0f03030409020f190203030708100510050c0a0507170f060403050414 80
    0x486944d1666001081070f6a40d004e8002031290003039a100307101d4500042036444410b40d147da20f880c94190540d840000821100f00190f541500f41c0c400800c00401303c2c401050380a0180d0045442e00b87c5d01c000700900d24805030070120805003000c19040c0c07a07441e10080d1b0808568041150880c40300071034a4034030902055070140109129240340094401151380c0200304850088a00c03400c0c90b50740d080d045072041410384059401c0002001200d001c142c2c00001d0307540008252804d000b0309070341c8130300d40c0d451500700041c2901c090032148000c2020180811120820a1064035604941c200e42c1c0d000a4880c000c80c4580c5407581e40002c0d8110b0000c10950840b15115202c6660501514140302c00941d04d400441e80784002c52114400b041c42c04010740d081e4011514014458221b0284801c2c04403496041106005074034405c86090341d0010700c00b030110388094401520300310304001c6030b81c1e00c082c0b400441d04a4440503400c010700703110100354860100d03070503240441c1580c3c5140606402240c006000095 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 649524181 1250 649522931 649522933
    0x4260409050c070204050115090807051507020d0203030d060f050913031b020d030804060b12031c4106030703141c020f012a210c0905090a0e0601060e030f 68
    0x4000f00c0c0b20a940718188d20001916a5002c0c2c025444108041c0e540f40310b401001c0d8403c010400c5120301c010040010007000d4406008140c0c0d0380c00c25030220785903801c035101c40070001340ca822003484851030000d80c00c0000d0404848046260800c440b09014540d800300e03000d020803141180c0d030a0300c01c001d8603072512210fa020302984031518003400c004258041c259000c460301410552013444920301040f0383c107109169031000e91320f814420034900f13140d2180309400a50b01501c0780c0314410bc0c14903038500a004021400ca5a03448880e40d801c24600f000d4000220b15500c11000060241c135440020f80700c5e09403540803014898906860b0300b1030703181103400e01e40c510455440c40780e20606c290b80895807440c80c01c0b0190003402442840441844001c00c826102d400880200b40c2272156980319141da100c15907260f07076000700705102d09056081941e005442e02001300300c031990204030f0350a0201703e139944640440010014a01ea4030303031061b1200018401c40080191461280c5103550b001c1c41070f0f12a20082d20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 649525431 1250 649524181 649524191
    0x5430f0f12030b010e03070b1318020d150f09050403030b0402160b0108071a030a09080c0601050a050103060803031303030b03030a11070e01180c0507020d060504260409050c070204 79
    0x4a401c01c0c0002190801c01c0000741426041c16055000c0c02d1500c4030840c00902510406003410110115900300074403080d17800425840004903080c00da031403964400c442c02c0f005665195280e02d0b40082c0c860011310001440c208810411100c04000300c08020386100c80404541c0e0b4070b50b41001c40140001c206400d521501c0002c005e616200500c01e1562414483c1c1c01f00510390381d0b00c3c0d50054860f54688503c6070111010054034003c911030754000e5501440800002442d40c02c5600c2d20b440d0f5811400e04900ca690008005000c98074060383c05900504092a05004081c240510140c0320301020f406910300004a00c441002c0500a40000b0b86085001d0100ca4442c2000c0740010100300c100c14071800240a10280032400700440c0c0c4220b8107031100380c001d03c8076110000550700b00800c4000c3d405000c100c0144641c2005a40b40480a0610b5000e880041a24101406c00103038001c1c0901d5000941550049540200760601043c2e03011540042800034581d520780f000c1000030b20804900a6019240c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 649526681 1250 649525431 649525433
    0x504090c031d01180219030b010803031b070f030318140109020a0b0a0215070903120e12010b09070e040603050708060f1303091202030f060705430f0f 66
    0x250344004074801c1c0d00503501c0c02d40c400d10304800f801c072442040c3c032020f1000c0c21030580c0050b04000e1502a24008000a0a03000c00e80d04c1e10b50b00944c06080e0407151240d000003044c40800540d00c0c4106500e035014003000380c1b0b8901b07207079611501c8414010000303041c1526410401c5600c03600300301e0a4807842d0070a49290071111482d00c0d55000b0410240101d1091a40324808541545a40c0c140c0c0c9901107950014030003250ba4400c00e14800000410340c5080110001e00032000030769054408009008035220400d03038041c0c420401850403005401002c050385440c0e80024a541e60003800381e00010a42024040144448013180281080e80c00c080c0ca83c0c0304192000584900c0024100d11644840060041648950b0f06458141c00111001b60001e20701d071030140302d100c080e102d1582c452403004044400917035a11101d40c0c10014103c07901d1010a0004c11890030344405401c2c0c40380a0400018220310303421644800d1002c030104034500c07014006510b00014100318049590301303241600003920740200c0c621 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 649527931 1250 649526681 649526687
    0x1f0905150306070e10022a12030f040302040501141810120b070306230f06160303060f0503030715110913060501090b0a0c111c0506041703060d030c030504090c 70
    0x10410500e0282c0100745c155401035101050503032801b140121480e0f03281211015801e0240960703811158000c40c2e1410040c1e0510342000100b81d00c0c61200b580d1900c0302e285004010845005a00561804403036101c0e01500d50f81d00d9000d0103d0008a80c2c090f10507455042c4408501c20f256040301c2003400043c1c401c48140008501d41500c20141c81c0da060103056200d207001d1001ea4019a5000034401c20070b00c04140500e405220103140d503001820b040d040190300d0350280d14640360743c6807d4012990f01c4e10248840c405100f5908007415042e0000d62a1132041d6a035085152880c2d203000d1506951082111143c542903021610f084000400c000542118a04100c0080895111fa203010a541c464001a080c0c141400d45100e12200d0b1140501601e650301d950010404894110782e000d14290f9450b010401c941102541a60040c40240001e15262401c40810300c17042c091144004420300400c0f00c90750300c0700c00e05c0030070640c14039000349804400d1400395403500854114446850a10941c40c0101e54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 649529181 1250 649527931 649527947
    0x90f03111e03040806100f0b03070315090c02060a0b012c060408030d060503120a05070f0503030106050418022d120a0f0c0806010504050607260c061f090515030607 72
    0x404c0011340b4080d8640c0404800c10080ca40700b140d0070300440e003004000054291000c2c6074003804600307022808608042518a08001a4100c80c0300c80c0d548000307035000d56504200e8150300403c15842004000b180400181c041581d0320380c2004541c20020305642380190410280034030402c06000740b40c40c0c6890b403440540341e801c001000c0800a1070300300001824580010820591a101000589072841005089616900c0303032605541c00901a1281c5001500420066009044954070f0a8a8600b000340000c5100d00d03800c42401401c0c018480d00a400c600000400a8a4040ca6680001039100745a022650044440d004006e11041c0300b001b0006c0e241e60811903078405100310410030000080000c0c4c1c0c148100b45d0341240018000d000502483c28070000411070540035510000003904075188a0a641028456142e02c046001c9020701d0f0b010340821106800180d10b00d60304c1c01400d040c02c403640c000c450358410f0302445520b40b8081070121665440f010040312000d4280e0380e0390b00d454040a01260 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 649530431 1250 649529181 649529189
    0x1507150f0e12030106050706110c0a0606091805060a020307021906200711010e0f091311060406080402011808011d0f070b090f0312040909060f090f03111e0304 70
    0x20149a080c10801d02103142104d040e41c82c540c40c0c050030f20800c1e4a415000380110b61014154950800c10741110100c10440200c2303051040302c0104981d404d00601806661103810043c00c140c076051405d500040c00441c9a5901102c076120058480e40e90003000c07440c0038118a003014042e040c1d81a16014890030b504009502c1e45501d00007006101c03912103400031407103469000381024400f007000d1036440d0b04c01d042d05044074030b0013400c43c02a5442c2c07400085801d0001c0e240d41104068035000030b002c005000c141d08003034240450348641043d243c450003070010800140028100205031002c2a140a150b4102e5805488102c0c001c0050303500b800940e688041030000e4524440c4036a04402c040018009000400e80d070000e41e145041c5520303442442002d95242d40032030703411b018540d0354040380c541020286c4020950700f8030215880c000d50a00d00121100c50030300601d664240700c3c10780d0100e40340070405040c940d490724141d20b48142d400c2d41542031000c025031900100d9403002d006d405005000010700291 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 649531681 1250 649530431 649530433
    0x70e1305070e0c0304110111010e031b0304050d0b06042901021213030f020d120903120f05070b06150a050706060f0303020705060d0209030105010f150c021507150f0e 73
    0x3552180d000b50184601290110f8055104000080000c1e044d01c140184d140c0060610024007860b001006082d02ca420010310110381c40424003040d95012441911441780b5000c000c0c51801c0d0410002c900281156400070b4206103001c40414115101c6a21104107000051a0b1400b06078560803403189600c00682ca21303005100300c3e881956000e0f0644101c8864040c1c0c040d1803041545107694440f0f10810410302a0b07440100d050038080450500703000c0003000e2240341c1d030702c1000310304500d40b1204200d032201c0381d076003000380185200c0402c0d50002c0c01c40781e1464000340c61041c90b030385100021341e61500e03035184001190804141c80480c0c603000000b910841e42714503400e000c00c9894028188009a40748006030059019040401c050300b0b02400911104002180140c503001080d00480e003540c80aa01a9003082c403150f500300700701103580ca0005507820319403070400d03205003113600010001c3c14001d4000c070428000013000010807200c80709044504c0c480010a10842041000c0c41c001410300c40104001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 649532931 1250 649531681 649531693
    0x15030501140c032212030c080907060e0105180d0b0a110c1b06130e0a110306090a0f02090406030b09060105030a080316090b0334090302060903070e1305 67
    0x10307850050360062244400301c4046046560f491050015602111040500b210382d00c0380c2e0102280e07030306a0701d4100342c84c19100842c0f4015a480000e080b403030010040c1400e074022040c2031190962204640710708250901e00395403508080c03807641c12102c030514540d69001000a80ba001004840303da80c40c81070403001030410200014038949125071085406080350740d0083c0c140c0b500d4009000070700c004002c01c0501902d0030711001902c00c45040720950080c01c485208281001944080c500644a105410811403030450070254007007a6800e9010f8442c141c41611200c1000141e252035041c0d440c50080100244402c5a403821b01550b14201034459000500404c03002003101d0400080320907202e5448010f00c9d15598405420420511f00d80b000e94080020703c0400007008180c280155000712500c40351001c110441e440c3c1c0c000c6440105150001d4041c803440ea800c803a0b5040203241c0112901680c50a03603034002000002d080c02c102d5041620090a810144821a40d15140705145036200d01700701c802c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 649534181 1250 649532931 649532951
    0x501170a020307180e371109040302160b07020f04020304030206040b0c070c0314010506310f0e03040303030e1603080a0201090803070e09010f05150a05090415030501 73
    0x148035600020081e415a0090381e080020f04508902d1542e0240005400900604043c00050138041e1030f0390090404004c8940c14841500d91106082409098100d01c25400000d81e580080000300400400c3c41258100001010b050003070045014400952070744002a98841180400c02e40021400f41d01680241c50503c0007810700348210b07800b40350190001c02c100c2d81d441d41c528803520001800c0c00300ca9035040c0500e8001400545240c0080c6200b10382d4040018490030805003103c00040c1014440c00110941444003800d00c5007441054107240d1205031039a02502200014200074003464200fa4540145e01d25102404006401030b6031007540c051051b080071242043d44c403450108800010083c9440c100000707003c0d08010884011203000208507124581c407840c0d415001143d500d008030b041805544a1490a0313062280034048000d0f07142a514207020101c4d40c0003c0054408216402c0015a8111540101d003640c4499200420a01002c000e415070400c0c02c0280348411520b56082c0000c6034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 649535431 1250 649534181 649534183
    0x130c0509040b1303030e01060603020a11010902010f030b010c02091503061b04170f4e07021206160815010210050709030b0c030601080106050f0405041a04020c01050117 74
    0x9015640260031180141c43c0c092102c110a60003003400c40905540705841c0811b40400c1c01004000e0015850060b11401071a42c054055080342102d2542c99242454160042c2e030400840001d2460518000485c031050800507508102d401c0ca01035400b04501301044454200b005d2090030040301a0241e803000e0300d42c03075810b032121840d01d4004941a02c003880b0500c0340c01d079032240001040300c0540880d00c9501c55030000300d0415005658007034904011100147d41002e202000b004028198049852041c5521780043c0d0088611060142ca02c41c000840d8030940d81d07001c91381c00020300c248095541c0303030501c5000c01049034201090080402c00003000901c08130b00c0d69003408050881030300a0540e260f050494000203120040ca00d40c01c2c000c00a00220206401000c010300c5130400084040d070721304014001400400b0140d02030010032804005d42e054002042c02a5000c480c01680d0101d180b416041e400c400301c4501548007600030384085250503100300150003071070403240c080c0419401048051449 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 649536681 1250 649535431 649535449
    0x6140a03050a0213020415090f060f020705190e0910050f0c03041b0b07080c07050f06040e0403050d020f1308030a0f080a0603080c07030605010902071e050114130c05 73
    0x14003241c201e02c1d00d51015040a85040780e420100040c0185001c1e200c1408240c080c80c0c41102c0710000748049400d020a6001c4d184540203001c2500b0000b9100358034120095680c0002d0007264080c031031052996090302c801003000c10240407003440004040c54040d50060b51032009074540400c00341084003080e0f0602d150701340507028609c4d0460840c038540c0c56440710b0315601c0b9040c0d400c11500e2200303c000903d6a03a450060103100d0f2007070b011a40e40d500e0240800b031403c1610b81101c7d1040c03a280c0c0c40e5840b0395423540300301c40c100c82c030341400303260155034504080e9503038018440c0d540800790000950f14100c030300303480007002c249007a500c940c42c020f03441d280b415a5030300810111801190595054001e014080c1c103801c1e03072000000708007064040e121b548220311500540360702c031115032182c0c1d82403081043c130740134007070160078002802c60402c407840c0c41c2d10072101158480303052400c1d85001c0740c0003804003c0d000f0700c2c0300b980003c5420005007010900d9100c1240b415400b0345000d581c401c404100351902c0048 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 649537931 1250 649536681 649536683
    0x10b030a1a1003020a2703020915210a1506032915030a15060f150e0103020f070f0809150c0607080903042304050901200d0207080d06140a03 62
    0x101103001c2e0b007089401c3e00207510400b905000d10400c1b402c1e124240f1408412440c04940605d003c04074945180306118108a0113041005c1c1004581380244441d11100402c5401400e4403482c914885048031282c0e0a1017034201c1d0240243c540e40c686541486407a8100208491082d20380c2002c0d20310300c441d540401c04529401010043c40c0a02180c4080040f144007070305684020282c2d400d0046666845290300400c1501c1f0314410b0312020104186800f03408201c0003004076406100161840340710040400e44440701c420b05056001c5082492200d00b0003c0d01d0003940d0003800c070004602d284c02c0c180c0080d0001c2030524418400c0711082d034036100300e00c001d5405800081e4000d204079160808180c44143c0010407401d9103110a210010318491010312110066500d403a1680000d11802c2c2400b0903030700001c103108442d80c1450f020071020414480b94030048102800d0ba1900e4408040400c1c001e841940806891a280490151070481055110074210751400301110b100303101d60410704c4603810789480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 649539181 1250 649537931 649537939
    0x5090f01020303190203060301060518060108071403042301020a030f0f11090f01020c03030a051305090c2d0f0c010c08010b070326010e070e03120d0b030102040509010b030a1a 77
    0x1800820410860b0041c6030807c600038000305a054a0f240499400c41004640300507003440384003030003802e50300210615005001c03403400c0f20035042581c0c54541c040c4070281c002000345071000034100000720103c1d080119045000d009651340da10020008010741400707a10001058a02102084402c080d40b00d080a020120703041c0ba030806050782c0c2040400b5565856490550140d026000c41c1c0365401c3c4010803d0328010785803a6180d00c0710200300c0d05816010b030800f0317000d49015004e07c070b0190000c07400d4403403c410324290203462840342260112054105ca400d15003404011071a4010b0403008170107403c100003640001c200c00c244040003214003807020311504007591010040e40d0080f901c200c0f11100c50403441d031035000b00d10034080c08d64003e18200764031840d080e40400042c05507155101e4074501c40c42c00c04400510b0317491015114040c0c24426840111250b565402c3c811106480039010b039401001c1c001e0050005607940c552520841d481251401d0246103000500c1303000c0e000000402c1c02c14880a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 649540431 1250 649539181 649539211
    0xd090f060f02091e0a09290f01050f1e0a020f30030705040b132d0519030812061306030302071a0c01051503010b040504020f06070f080a05090f01020303 67
    0xc182040407071201d08446802144007040800d4020040c0914900c0c02c038000c108140c0410201c00380c030300a8450381e1f403807840340800c80c442c03031400d80c1d00105690300f4603145004195901c0794004880b0341c030f2000f0315400802c1000492804855078000c164079158611200503200b2515084030658591407005240c1c045444a1140b03000c0f90302c0d6810080c1d503204d90340d030612615140e00c9000d00b130101c0d001a801c40e040018800c009001d14034481c211540d04224200c1c03450074401d901014034a440c001800350381e0090066500d41426004c540044000a41c3c003c2c0c001c175980d58900c2c900d4078007070030122402c074011024070741001200d02c50f9214200c11030790550f002d8a840e0703040045000f0080c0e09480704d084001e40c180880c090030803083c850a4051003400713400c4240140c885003410300b555800d01c1c803d449a49041c0820025032030b0081002051072088a1440c0d440111340340c01201000c861314060819400820402107194000340180b1520400b11a17481300b00b09550012a60380c071040715100c41c0140d202c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 649541681 1250 649540431 649540459
    0x60a050309031314100e1819020c07090b100f05030a0e0d02060406180804090c031509050402010e0a14010c1511070204050603030307050714030d090f060f0209 70
    0x61018640100384142074074581204140f000021640542103d91242e41d20760908943d4030302040519400112030904e005000725610000d86c041040340c28160820303400e035000480003482070120040c6000c2004085445096842c240c90b076030705003806103401703061501c2da43d410315140c02400b0700b101c0905903664031402d45071b07800200c0310f640015106100068482c4000414070310103000750400e102140c0d0040084e440c0c2400c0510548001e41e030489516042e0006402c04031f420b020486003682c1d0509008070f02944501021002031034840701c1800e1400d04828045803d9010b5003100b8090381c000d0362040f200d0300805c010007078038007020300c14840a0b04210380212103550282200740001c90060020b001d50752017928a180c01d0325044e286462401c030f4005500c80c11483d040c4501070f04050207400940c01e40c500194060205d02c40c0380000b401076034a032410442c417650104121091800d101e50144210300a619010309203038546c0208031070071030418100040902061080c1c030350155005003420002d0002d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 649542931 1250 649541681 649541687
    0x140a03050d050c0c0d03020a1a010b0702040209061608040e0601020d0509040c110f0d02100204060807120209030109120305130c0b130911091305060a0306020c01090c15020705010806060a 82
    0x2100c0b140040d107020304d803440501e03a45c80380c510441c42030207900036084890192030001104218540c00705006052000103001412058040d9400142d05440c0140e4a80682000907102c0c003416148028000400c0c80c40e000700040003025008594540e2a2500c003900c50b00b005a0b1034000400641001132010b110701651480c1031341010364800b503030341004040d0700f4138881d00034148260f8102800065121241004440e41c0c100000c0e49074500c400811818542401002083c0b840068210030030440c4400c1540c040e003007203504544491030001c001b0880c01100c3d180c55164040d00c4c443c03203070100303151a001a1211400400d000e130030550203110700807807a00380b000003180381c0c0144c06854070240c5403100110350007a03d446100c400104616034a5140c500440c10041d03c50842024812080c4c1040c0c10b100749900c551082c401660b6002e2400350700d40c0d0000400c1401407034100c4010700b00d110300d80800078030040116080500490640e094505e40c0b0380b241c0041d202c40038141c540503041070f000c1010100f241c1c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 649544181 1250 649542931 649542937
    0x506090a1a0405041209080a2111030c16050103140a020a030e0f010b030712050c01120905060f2a0301030b06030f0a03050d0f14060d24020301140a03050d05 69
    0x400964440700c101ca400701040c100d07001128101c0d03100d01c0511100001075007019812000300039010090460b45104d5035622150031051440d4042c43c0071749003088450900882805c0707801101901201e803180c00f84281c00382d440c00030342c505450b04017080c9400700320b651190046003901c145940c4240c00644460f85054000d5216812050400da03586c1e061030b98004080c815410242440d5001040055940042500b44038407a40002a0200d40780c01082c0010004905020400001d08001170b41e43c0e441a20304001e45011000140381c0e0080000304442c0d00c0b00051080d000303800ca030502609180f0655005604000402449106040144010000250030400c616409400501540c070952500d5070b88074600080054124040f0383c02203011001ca8810b0b00c11071420310010042800f244001502008010501806980c043e4001a0342c507811b12605811340800200041c0d8002008078a8440308402074100b030040402c0d62000310761010b5545400303044a416030382c01c02d0152078090300180007540c181d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 649545431 1250 649544181 649544201
    0x90621140c0a0905061005071e03020a0206211b04030204020708190903030809060601141614010b27180c03070b0d0e0d02100c110105070309050d030506090a 69
    0x4441c0350129030300c035260302401000a01500d40302040078207043d010805001d0360007080c882003000600550001c07a0344050034000140344a01c001a0041140c03c040b0300308040500065040600041c25121400141c00b0a401607903100401c0f60241e1614640c01025a48024601e401e0920074041840546040d0380100a0700b07104020302c41c6010a42d541101142c2d20224400003c42c081401c100141034002d07030f201d5070021a00014052520f803a20018082e80c00400d8540043c1102141452103c40142e4480480c1d0390407000f1181c034040d40680482c06003007865140e502030b00e42d40444800c071022401d208000e41c400300e820140340e036440e0a0840581340142c250660503115a00d00c05441380c40a0164002610111010640d942040c0c0844070550300120301404c44e680c00300702a0080340d5804078990714203076100c59012030210100c00003203403000581c624000c82035103400280190305406600451007075118100f0b80324030404102c4150102c50040700e050b9040350b500d40004000c90281d500c089040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 649546681 1250 649545431 649545433
    0xc0901110a0c030c0902030c04090515122103010315050702070f0b030f06030f0c060d020c070e0a1401140d020d0506040303241802160b0c0409062114 66
    0x50000d03509040d141c5800d040066649410049050092000c9507040c240504000342c0e0561075800c01e40700b650902c2c81184075405400d40e80300003041032400860409401c451006284890500301000195118800405c058442c804c2540810708070108800942e412642c200aa4941108800f00c5010103840e004101c4401c60142400210b04040a4281c200207810714840254580c940520141d050300b0010b819144241d02c00d041c21102c4000004084034203403c161152074646000000c070700041d020303030f0901184c0d90140c04404240d44c3c172181d84451040c40d815000307002c144446030404000040c00c1c058142c009100c0e0052061604150110600d0f00e071000d062104480c00544409003407031020307035045001944903614a428400403c54020944039907128803410300d0306e00700000b40302074000f906565000783c01150909841010454150003240c000403c070681d0301d080b04a0071a5a40302d8050800350900d0100d000c075014070b01085186c050f04245d03a513501050103a441d03d103031114180c01401a5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 649547931 1250 649546681 649546697
    0x16051326010c020d0503040b10120b2a0a0c0c050d0506150409050a140709020a18080c0604030f02030c04020703050c070f0609030303020c0c04110901110123090703051b04050f040b0c0901 82
    0x308840391030100071420300be1821440c00f400d002c46a201000340c2c5031600c0040100200e040700d5410311880032125113a9841c14850b01001c00707890a83c200fa171607980300039408016520104180407000c01d40900c2603600c0601144d924052a0400080380c40d036802c0604160302550301000081e100f82c070040529440d035401c40e101c180e41d0b011014141e0f07000781600d01c002102442c0610108902400d48005498400d000e450400300d14004201e180c02140300140454007000d43c0082551002d20009040b010f01038010b6540b01203d081c0030700542d000090351160b52103041c00020f1034401042004080d079140da40c610848500d075071411800384d0072a0905a0755070141c09894460742e42d4501c036040700c600481181e00d80b42d00c031081c00507185a0701b1800d0024540d0401c24801d03404040540c0d41c00703101a1344035040f8880c3e2110413040c1d14040c981e400062241c4103080080d400021240a24843c11500b2182070003669105468036079803142c1030314010f180251b90030105010301c0122000d0303c025441890700d40b203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 649549181 1250 649547931 649547939
    0x60d0b2a0a0e010210110a0e01031b0f08130807020103090515160306060503010b070201051c150302090c0a12020a110703230616051326010c020d0503040b10 69
    0xc0315034000e403461400b080031001140c01a58042c440c0d08a204c4800404014514100296001c90f1143c2607c0307804129040402201c20b030302036448680852115641102c0c900d003424405008030080184200206980c500000d440144403280b40d440302d5448140f06080c031119a0064000d040102811281c41c050402601c0b000d21440c601c203840750030307c90f00480c1c40403507510000d401ca62068010f10704000702080140403a2091004a5160136428030300280c1d40c40c1c404000d50305003880b44520014150030f20050200b10b400604403001901d0003155002421b4460f01001d1880d44036005607100424440e60030304408010f03a6005d40700140e01c0b070804081d40414840d00074103048058000b00d40c040d05070141251761041201c01c8440120191000f0816070411f80d0f02d4a5001c4e10a0044ca4200040003d04030742e4501e1803546000181a01d5110f01c92090461004c0a220b400611911085601c1c0c1a514030f0000d10000d0b12051810858882d5403940d1070301c1d105c8a0060200500001042e480150006 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 649550431 1250 649549181 649549261
    0x30e010c02030102030f042916050c03041202040606170f040501020405030f0303090f010b010c060e0118060b1207052815050c0d17180a06180b060d0b 66
    0xd44501e4100b03504c020750741f41c80d02d40f204030860000a41c000003440c07010402d01c440713041a840703a000300b00035800c0840540e1000c0304640d0707841203140002040c0000f0900061403400400400780d00f5108840601c0450384450003191a1401000400304411650300468610380c1080e40c1e05401c18025400541b0f0940c1321008240b601007030060340c0c55691b0002042240c07405c0e00780266421008030340000d0005107110782c0000d200300761461019041540d03070070450a0000d002d40c0304940156201142004507049407c01100030300201e003005e802080c180310b5069445001140280c04d0b01c0000741056841408d22002c0745102e003801140f4020702d50900c2c00458600d203980002a001d18090356400d598040440009040070142003006052200408880110415003203070240e103c0c0c02c07000c160500700c0310386a0451400c80e03c00d2000c1e21191a0400e501900f61810440d13441c110300941e005d140c030351260810300140d0002040c01410400484020481100440304044102e2a03441010241c0303c60800f000c0e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 649551681 1250 649550431 649550437
    0x50106031b03060518070302012001050705041e0503070b0c0a020d1103070909030c2d06020a09080a02030a0b09070e0109020d05250e010203120103080307022503030e010c02030102 79
    0x907010001ea4074030800070419a4000c0d164010803540820b21380044440d045560307a009800b000f4140854090007040c0300c030103011381c1c16040d0709610090000381000c48001e0241c3c0d206018ae15142014942900300003d0510300c40021104c016000f0500d4031310700845006a908401d00e402007500810504501503518003440c010000c1c0a00c0da015512022001010314082080c2c3c0540702a50400504a0119802c1016443c0058102c04c1d907c90500c1118058540300f40036140340c802c4400c051154206105082e070180002010700c0e2034615050340c07940c000300d9542c4052a0002d40c5644100490780000f40c0300302c01242c2040c912021107180503155451760070a40003d80011a41c10307404184281c55141d1402955084000c50040e24102c24249404110640084000d5010f114680c40c0f02c01c01644208212203400c201801400e580e0350f16450400da86500c1901c1c424014030900000000030903c8007424002d2420398010100f55501d1a40d0130780d001c003120254a03040c000e0074801c48016031028002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 649552931 1250 649551681 649551713
    0x80702070b1201060e010801080a020d0606030609240e06010b0f04080a060911090411040b060c03070308180c031b0a1a070b1f0b0315030a0b010602071d06010c05010603 74
    0x52403083d41c1403141c020010300f076080035141080301031001002000c00215400641a40503100400b802c0030303034103043c13014060b0356200800062070200018240004c0c1030081e820902015100340c20034034004860b1043c6c560707a4203a031505802400c0108102c002d4480244202c042c5080c416080c55a107070551407c2000309134055403456200c2d0802010442c1c1001c0c14003d1800480d918042d90070300382c807042034007c0d041403510f0043d0350f924511065591040180c9424145007030840f59118540d2500030304200d8280c07200380002c695940f025604d070f100440c200040c42000b900034485079002c0302c001000c90900384542070b0071100304000491848031790008005031030b013070402d01583c403500b902d00038278a484000c015540380e080860600f084904291452400c840000e41c103152a0f84400904400000c603100c0d5030784d85480b4171480a0100403d1720140d0303040310225000d40360071035902d007c844510100f06e550b43e1024500c1000044540d80585070210155018100001d05c0c0754895032104d40721401414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 649554181 1250 649552931 649552957
    0x90212060108100c1d040605040c11060a0c0509100c02060304030804030f0e0a09020f0f031509070302031504181a150402040b04210c06080f0903090a06080702070b 72
    0x4018081c0c6031042040c142c1c1943d6481c4204100700407014014158126004003400801024203011000c1d0b889030000c0e0050000200100074807803004502610950882e25081054020503000400b001010f10998113007080740d480e076030b14010701c070000c000e451143c0d18215411300550000b26401358036000083d40c4554072035201c90381c03a4109070401070102104a0309205c08c01240307001d513800716155035407200b00f2541515005a11045c940142d03a01d94003c45034900500140402009808400c070b80340c08072107080a440440468071754040850607884102c410107000d0718241388140d214200b036408000f20083e1010790400480c2107a40d4446014000342003005460382e0b5605101c40000a401c840d2795004003141e04519142c83d21a1007212402070b0321540d149000c40701080502502c000000040d00d0b940030f035005115507200e51010b00000c00036110300d0380d0298544000760705540000101d6118070030062406a4251501808079203a65009000508500400c500040e2040342140600f00320800c0c00c07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 649555431 1250 649554181 649554193
    0x1120209010509100504050c0c1204090b06030708060607021329062706070c0312021b030307170d060806040b0a2009010917060f0a0b030d03050a090212 67
    0x1004004010300c0682159200b4090b503010700820000a003c0482200c0301030b2030110390369449126480c1d044c010010b4003070583c00b0f4140f5551103030310300340000e00c20b85060341420030a07108001c05000403408100e9000010580140200f4900d1801c040038100e103601c010120010300d0903400441c1c040d10300e003c01c8000b40c0f8455614208a08a2a080c001c0c45d41d0740682d0310074100608072a485181c40103040e0940c0b0020380400100b169911040c044998aa80200f40c0380030b15641c0c1d1070034110039114240e8400040c0aa401c0d54940c000c0d00300c1c00504180c000034002c0d401d0500c80d4a4840009030910102603a180c4c0c2042003600f240c006008441c01044140c000d091146007070304090f403180c0e1008200101403407410316000c507045242c24818601300c0b800e02400340c0351215040184e920220030340000d040c149500240225206000900900c140d40c1a403040010781c072940e80d803400f0f40b421008065410340104c1c41005000e072090784002d5002e100c92201280221454004c1480c000342c090190302190400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 649556681 1250 649555431 649555433
    0x904240504020c1f0905030304030908060123010315031b061e05030f0705040e0a06061e021b0109090204030803040516121101021507020304090c0c0b070503091002030112 75
    0x1008010005080a46055251041040f11070352240700c040e1041c0034002c00c09284d0004004580c3c4103041465001d000c40e43d407030815080c05846268071744141c2456125401c00450380e000708801c2204010010f900c40c0f140f581d00400154098a0000c8420443d192280340c004003192000002c2d001003540507076070204035420201c0c014000aa4101c40140900201003095402c40e0b01c0022240d0040300e440c650041501c85000c112968031940d031200d80c85001000900070004066449501100d0180c1c45140e4a55100a00e8086d0040c0d0410020050703080702d00340d12246c103420742d80100c600105141c010350503926a48a081260001d4100fa90451004400c0004004040003882c11808058945108040c944115148500e0035100c0040c1611540e86000500b079000308040d0412250440c1c0c0380f5400c3c90325510003580c9400c0b034802e1000603410314059040403409251404007007500401000740c1395445001c26500c1c1e80c40a40b10f02e40a105690010240408510240d800391414680d4440f001082d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 649557931 1250 649556681 649556741
    0x9060c014203021302030405100c020c1e01020d0513030507090e070617040f061112041205071722030f031416030e01090801060f030c09061511030904 66
    0x206009009146010102480540c4d180441405401075030707480035a580c1c0d2285411410701041880c070404240c00c0427441d4540700c0e008249800b10340c800303a800c10101044028010740840c850b20346203015810404003848900d2182e0002d014044400109481c01c681e40d9544a20700321040d841464070540e10324141c50703c40780921552005040f507140c40180400100303d01484a14050710040c4110410140003003004040c0d04002030114880001607125460b07180011032202049404644e1003042003c180c040390b02a006803800b058011480001442c0b00300541d4019610456900c0694141c88419101448440c10f14102a611441441e200e49950f45005020502038074511a607044041c0f100141001030a00315960040d058540035265184d12001a10446c606070045102075080000100b441040d200c1d400044038491594170707001d02d80d02d001c0b510484185001c7c100b030100002d007103000380d03520520940b0702d07400c42141541e24219000c0001422555140401446490110106124110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 649559181 1250 649557931 649558031
    0x390109080d050325120519050a0203040204050105030105101208070503040f091b08130c090509070314010b0a2c1005030d0201060f0501120e030304050102071b030809060c01 76
    0x140104da01c140100e041070010348044d414000609086075a840060440030740d480740704070340c0051260204068181080d004c400396004803800d901403030503c0e00001d02401d0500c0340340e21411703103111500d1020303052040752030700c2500c920000d986506042c000c90000c150240000c100400000c0304002d00c43d4a0b0000d01c0c0b0035a0640d00e140f18068001c0284440150b03001065a82c0c003040300b0501c1c040341c2485282812641020750040e8038640e14150400c1041540002e1344d5003a01d0042400d1016441204003080c240c6c0d010042d41c9400c24521107007040103450401c985009549100c10a42004102103200a0800000c40f415030b28010011000c020134141070010306595140ca1009020040c104000c8000002c402c0c80743e0343c10005812904540404a5400305400c0c5030040150390740c0f410181040d50103500321010a4603039600310039000d10040030246000b0226035201c00d5030f6081540305010041542c0003001c484045540f10000b00700c0c8820480450105144600c1d00d010140c24415840c8003090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 649560431 1250 649559181 649559221
    0xe09161e0309060f20090a1503020c102316030e1005070314070c050c06031f1412030408330907030c17030403080703090807030f05390109080d0503 65
    0x408101a041c1602c40d14500b0043d00c4c64454090701c0e88c488810110300a115210381c06021b40a000c110480019550b00100365080010400390052429558040304469041d2070b120b03410740b8400f0140c02224044d400510f020441300c0103442030001e41a02ca4000e84500711070440c0000c1d074400412514030800b4030070325008010fa1a00d018241c020b0703502e29503160607040100d80f06001c0480040c4a074190040500c5103540c000c071207070380306d1662129032860901c6000174881c400d0320340195041d120000081074030119191603000300040500084000d07030300099012a164030b005d005441c00d400740047c40c01e0902810710700c0c00804140f85941020070f416102038000010000910042c11081c0c80008140c80a498020882c41d5a0308064036054401302d245900105c0306003e02d550001c02d004141202c5643d05015105452060140e10700c0f2140c0043c1040d800c0710103962a40900300300086108007140091410f04180b18801e441d514100c0c0b91404c2d100740307080000d10000400c0300302020742d15110184 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 649561681 1250 649560431 649560491
    0xc150207120203060402010c150609020c06070f020a171306020c100f0905060c0f060c180d0b1504060f1e08070302060a0503041a01060e09161e0309060f 67
    0x481502d900098a900002d040a0304000171101c440742440500e021a000d0181090000c008107603446003a0340c0a5009410746482d10b001d0180007070f034031a014504081c0c080d60300c0c4d80581800d00840c1d4542c02003015911008000300c00600c942c1d00c1c90510982054007808041c5c00406c9442d02440030010f64001035010f080400505640c1010584e40040e43ca0054940803500c8503161540a41c1007807410001908500c0c443c0306034800e200301d1701030310401402d000f001c06201001d5411242c041c8801b24a10b01d0f802031002035031000042c41e842d00b20031001d120000c002c001144081e501c0d184940300c503406800030b1400d164061040c2c0e58071800489034000a286100140658a1079600064568044c2c21250400d012000001030104110031450107150261148045001c0d610358030001d022a00c003044180c01440100c001c83c5662310194984508580190342e00245c40c160130b191800114400ca082d0404d03d81c5482d200300c0046c4050240c010300c0b0700183d50020354030034500c0d198812406510400515 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 649562931 1250 649561681 649561709
    0xc071b05040507140f07020613032a1404092307230f0103090f050f0309040509060f040303150812070521030f2d0a051f0e130c150207 59
    0xc1300d115507017a40e040c00d1481c07800c00d440d1407003400172412522070160f41c400c1411a240010041005a40c14881d0341e0103030046031b520300c0440319106655030380240250810682c02d900d40e00002e18140d001040310320700c103401203282c2006640c0c0200c401d12620110b51a5500060014045040700fa03140d1855402c40c40c43c0c01000ca0400d0022604020740d6030041c1d410941c40d609414180f0240244080b20344c2e40c810200d070748c1c84c2c0b03040031419100d40149141921550a0002084510100049440c000e8142c1d808440c100e44980e42e00782d00500007010f41c1900006d0b009000140c032401400304190116079070421030b580d0510b034948241006400c0c00240741300c06060f0200b1401260080a40c0c0d4480d84401002c1029140c001c40801c17406198004510f2170b00400d4401003c075031602c40910301562a0320810302103a1680740e907641111030742518041041c4003510040041110403c096600302012040c2c014114102d5103070483c0000c0300340c0103584004011921010106d030704105c031200402d480723a1a021 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 649564181 1250 649562931 649562957
    0x19020c09100b250804030f0b130b06010f0306080106080105011d0f0406150b0c0d0e010806180414030f07050d030b0a0b030a0b060a0216080a020306040b0c071b05040507 74
    0x3815010380203400403c140490b0b201c0f03000d80d194101051406030400e82d00740e01d40790f0780e103054613800e121844100d481500c04000300e041d1920240b00c0b4004070754040d6810b4031580d02c00c0011500400c1c42ca0302c000803d80c8500700025490000e118060280100b40c0000c980c5605001860003a0404464005200d074079801c10058603010216040c2d8015a020001042c800880c3c2070529000400d5001481e03010f40001d4030100544000a2100d08000944c13201c1600f5003000b40195045c070f4048030304035003000006000c40d403240300c0003581a0380507204e00c030f141032206959418545503400056288031144130000309c41c824840c040180c3c16004071240340a00c00c510081c00401ca880d0a244a01108505c0100c0461070f1000e8640114a4130500540f100f51542d000e00402956034840000c0a051315120400200b0255008601c03031001c150042d001b080d4545640d40e0300402484001d0124080710002c0c040c2100242c0d02c034003210a58403c401800d410070303040c0f4003004120761026100106000d0017008101c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 649565431 1250 649564181 649564199
    0x3011e0f031a0a110f0301170109030912030c0507030f05070f1809020102011e02091009050f010e0102070b040602010c0e060304051507030b04151518090c0519020c0910 74
    0x110140d0704400c00c06030741c0f1003904200281a01000102c02d1620104a40d4440c0440d10041c5040303514403101c9940c0301c42c2c98403e903800ca4200c2d081c060005101d029040c800d42c1441241411020722030301d810800340b0312685a440c24180e15400c00c5603c501b00b02c108605020041258402800801d1000035680c2e2070300110150011085022114541c0c0316413603001560300079405440c40c0b01c0d15640d508542f42480d41c0c020000c0d40f00307201c01441406060307419120700b0300c1290240c0586002070002c601d644080380c01514201507212410381140300b01c1e036002c00c0c20303542e540c054030080c1180e4002044041d44542c0c0a00180c1d2682c03403150240c9014010040400c2002481c101c40b13405041d801c0100b52900a000c4002d05040e18031107070040d040034400d00c040082a54502d0407111500c0d02da03041d0354481101120303940f0b00d10040700a0000091401c1c001e2a0142c2d122514500e4a070410528105e00c5241ca00402c03010103180c00f01680007200c1410031810b1924500383d03c94241104010b800381021145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 649566681 1250 649565431 649565453
    0x904110405180601291c0606050901020a021302040513091a040201020c10110a150b060f030c13090e010c180b040303181706160306030804050402180603011e0f03 71
    0x1013100c40d0000c03485d0040c1148413200345c03070303203003d10255155035840a081c0120302c1e400300500340f4806901e402030014006104100b5a00c030700c0c1050303004e0100006a5000c00610326078242118950903420880000c055466050400c1d4440c02c0c1c00000c940c03403581e030130003014100505842c0d594a0804008000040c0e901265040303213214125003c3c00360068421080b141c54075501c0885241e403280c040c1c40c07020b0040032440c0b040a10401482841040c10b8142404614014200c4050f601101800441d1101c0940006040b82e41020f0404c00c10656481003070303100b601c0300c24008202d140d64030101d03c2c03202ea03400b21101588000754201948132910304103020306107104510000d4108132800c00c07060381380c07500e0001c0f4800070706241d150300403281110034501d501c581054400840544941d0440041c1c18042e00462044030b1300240001c0c2458544024000a540140b070203004d1240545001c210b1650b07080701035806072001e0800c01d58403c250b0700303039400d9039009500650256200443e00b0000184c3c01064 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 649567931 1250 649566681 649566689
    0xa140603070c0507080f2b0c0519080405090a1a010f020a0503130e07090803040e070302090415150c020a03060b030a06050415050705161e020904110405180601 70
    0x8615034a546600c0111142041000c000b0154090380304006503620b07000441120038100132090b547c005c11401c1d03010007003500b4224610f205100b000542c8181078018900071840d00d0080040c2c1c0d5160310002208042c83c107000c0401c942c1035401050510040c1425010395900801c9140108001d540e9000225902d030034098003079042268960941203010702c00d0159640183d80602142d031998002c0344d070075007000e5035800303109001c01e00c5074002007140e481000314404455860010714034090a0500b1444102c000500080074941c00b04403580aa4503613104800060103000c06940c0c9640c00c11703560f00303a0b016020030890104150b10718817101581c0c0d540c0145007104c3d803001001461488082c0072034140850380a01410b0036260034100001d00150b01e80d840080d2507140020812642e801c0c2c4c0a6542d4000c9d03411510700203400013040400200b584090b50b4a0200c02081403c2120355035000030085d0008079811030310000d03d80044812400c03e801015000ba0382e83c0814000d034511500d8103540c074601441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 649569181 1250 649567931 649567939
    0x102030f1b070803010b070b06180a0c031d0d080105010c0b0a0c020a02150310060f08150307050a29072f0d0605060310020a021b121c030b0a14 63
    0x854100004040790071140c1d1940c0c0415040e80782d40c6e5514906c8080c2e0071900c011f95062401c400040c6c01883d100c2e1000c4080c581c6011102c0c660740700d0b044464020468003280c00241952110b81d8084c10070808207030788580e0780c001c008105c100f2240a00520846060f841030381445000d82c039450008000b00452503003c4180c4400080d80c10610340c0407031600b20b000b1000b035004034123401c8140b1000300e810021031165007014401c00d0f516a44030003c40d0028060391144c00020f15803800709203050210004907044420060888004a8850001800e60445948004900a00c0d1600005107007801e440440c56180726010513030034080380384c0b07030310100d010f8a040035001005410720991410801c2c0021110101019003501071103c076500d8440020f0506854441c4288101304881030640c40c41e0080340d6110380c260740030302000c584500c0828000b0380118030301a80711008200905500a08000602e214071110080e0015000090300140403500104091801020741000c01d10590058002e48015007006071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 649570431 1250 649569181 649569211
    0x16090c05180f1c210f08040204062625060f02070f0b0a110a030e2e050a09090204051c0204020c01150603150806040b04080c0601260102030f 62
    0x280003030210241d50010319400640301038060300054402d1a4071180d070b485030904a075904c4210840c041d50411000c003010008410880d031040d1a845010b0382504103101130808920340b034441070011084000541e40c40c52600c09071400201c0700344e040240688140350031040070300200c0140c010340800285801908144641c0c00300415910b842004034000901080c4111105c80b03450740140005030340b105101d030780082e49500f030381e41c0c400e14040b80c13114050703a01d6140d40c0d0320041e01070248148900100800c80100300700c411001758074030f0240d08001005915503500366585060820107000340e1015040f40d18028814001030000307849090f080185c0c0c500c68904a6403506561002501131b200700c41802c10154203090b0f1402d04110b0320459a0151020360300c06201500701c0c4a070450b01c0381a244036001345c60b0311600101e000308940302141d941203030003224558507003002a040c003441c0050070782c0702d400180760200c24000281e25031035182c44440304046c020340c0b45050511000c20064800f078002c84084d0404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 649571681 1250 649570431 649570477
    0x402060304140d050a0306061d10050706020705060723180f061321050a120c0515010e01051002060a0e1c0201020d0546050916090c05 59
    0x21030048810341d200d9400b203d103100880300c0700420700e411a1015a001ca410f1140c0480c200d40907080c003d10743e24540c0360783d505a00030082000030400704c0130310000501100700007407004190140010041d5900401c000c225504180c000100031514a1130748525039815004448003004019080795818154517a2f01d04425040c600000c115080c42100964040000a840080c040030b00041d44200c37103031201c841d10002c00b82e0100c0840c0208821000300640c200c4038140000414201420700446580d1410040701c24240d03884c0d41c44c00300d4690b060b40300c1000050041141604070a04c40d1702509041c0c03100b005680351040003941d2148068280110b42e62a401c0320b40451404008001e007590301100c14403e000c50740c1c240039000354003070840315214a080c500098041d0000c5841c0c001c4041c8490240421780d0000c5100806c0340c800601e005075402140000100548060b000c3c0078000c1d2032010182c00365000704107080401c0c0081c7c1c1d2100311164101600c04051b29042010760b22000c0011408065803204 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 649572931 1250 649571681 649571693
    0x305090a081810170a05010b071403090d05060108120a0e210d0504080c120a0813120c090b040504030f051606020d060f0605090307061b050609010506010e040608060402060304 77
    0x30007076801e41010f07441c0d8451400b01da02151500840e02d49000c4180680c90781c03404502660402d0190b2607040c5010001240080e401c028804200030405041e40d0401c40c00400050b02c5455000083e6007a0340418010f01058400f844440031502841c007032146856084d40014152090080a4074411040d900320740d0048410840103680300c03030f0744c1810781e69002c505100c05006600280205c030301c18480d81043e06064100b0444041000b03c121000f0410010340355620b80042c0d0114180d070b114070380e0103640005c024400010003071110b441094404641402c0500e0345044a2123030410600c11814071041c8004a030304440c440c146694145883e9a4070b810092aa00040c1c3d810b03140101a58800038a00c4034141265001070290f40e020158907498585e6075100f1645400348848055042d00203450410545015119800515200240703140140302c0c262519402c00c54200ca1202e8903035113903003c2100969100b9015848424112403c10906092814031540d460000384002c0c051100003002c80e0034007407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 649574181 1250 649572931 649572967
    0x901090207080d0e0f0705010203120a02161a06040522021e090f100509090316150e070501030608030a0903120201020c16030b0f06011e2102090a060305090a08 70
    0x101009091241c6480c60700d41696500e110a000e905c140540e00d008140341d03201108a409981c801daa0880841d107802c4107100c000d6101e080760310002078030b503006100021000340201c2035115a41c0a10351036454800280720030750310001c04100e0080560421400c103401068000500700e9011343d62070820300c140c1040c00740c80c1d42c082c003403050b44003610300d003001610024819400e1040300c562408451103681e803002c1c03000c1c0c003c0603038003010703a6001402840f0310304a00c01001d10800340280362207200b0300c0500d1000341c1180c0f058071425405400c240b10620407543c0502807440100b1a0200443c0b6080d8000302c01001c4150b10301004282c80e0701101c411444a100350199004404100187e402a800b813040d01812142c50303220403514052280c0000e041da00c12000c1701c502c180410303102c01d04041d440c21600c09541e2010313841041807004041c69000d50006c0070084020f220b000030001607841414204100200e03040b680180c08140c2098200000b9000224401d150b06901100180e01c0c4c0804a0441d0388084e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 649575431 1250 649574181 649574197
    0x1101060f03050f0f030708041e051203090a0f150c060b09160e06030f041119140a0b091c06061a03070f030e03030613061e06080108030306090109020708 67
    0xc05410004818402c011030f400c410030820b04115540840040c544070344a0151540152a40005002c00c0006040c20070030700c051604134050004896131201c5c0020700705a000380042e02540d01c085147c1e41941004411400540070229022040601d000b00420a0040c26803001c020001d0f43ca1010003041056040003201a00051000c0074a2070f0100b081107070380c2001d591079030001e100c9495840d118108070003181d008103040e8005448950351622141007143c441240d203504900c026a1400400481c80048009040406c00c000c801c038141d40304011003049160800340c031196003001500c0382c5a540c195400b9000d150700864803514130586c200000104150b034045034036034584840c55420501c9542c019481084942c07605079590009a4040b4201c0c1c003000500e1405910030000318500d441c1c2045030448444000401096a548440b10303c10140780b00c224142c00d800d1040c405011094104040354050902c803001141945059000103803140c1041c0300321054198005261010f20803040700700c845507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 649576681 1250 649575431 649575449
    0x133003020d0f020d0e061b040608040317101d2a040306060906032003060f1801180b07110c0607030905030313080c040b031515090408040806070903050d110106 70
    0x10750303941c10944c0c001c4c00710079070107104600034000011601c120249411034580f13800310615040c14100b0303000b6580024090026002c0c002d03e03214103604404100d9a1511400301c4460320050141b41081012130014070700517185182c40d4050403c6002088008498a94540801e501d0001020079032509942d108940018102504050011804012079040802101d204620b007004800c004e401030a544070782e005c18181c2c10b81004012800b880c99003480c8541100030302a00c030408003003000ca91070031209641c20055546084000c001c0a00801011280d071101590a1400c4000303000c00d2581c0e11015081d0107907114800124115040c0b500c98440440604030142c200c96842e019480340748915001d038801c605052140030909141400d0a000d51903a1f128050020042807004c174041c02040800101071030740c0004400034030b0b58540e403081c1450740a68001c1003150b503540d081c0380540d410800020005005d018800310104002400050038400a030111b00d03040300900c800450590140115a20078101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 649577931 1250 649576681 649576687
    0x654070504270f29010b040b1210081e0c0307050d0f05070e13140325050307020301051e01090612060203040c0e0117010501050f0a050d060e010203133003020d0f02 72
    0x9a02e503983c1c2c0c0035008a040001e01450781c0e41e40108170943d10880c059402a0b413001d004c10b0702700c1d80b031842e442a005001e2070100b100e61502d4002d46490815410380000c40e00e411030744085011582444035550b80c030008c1e809822458184408154842c0001070000e100b000c00304403580c1408030900540e4040c01d499040c40410f4140280c0c50080034103041401e03142603144114079500788400104440307260980a46481040b02441500e44201c11443c4050310507010420410700141c0d428445c0034071403408620644003515400001020b484816084101d40c0c40c9805000d01c9125180b1014980c0c0c0d56001ca00940e403995240351061504501d07030700c0005140c0803a03001090500029180c1510300f641d0748002c0003241e0341c5400308981c01013441e100d150030540c0403805000c24140182e0301c802036801010302142e80d900c185001c070708980c421a0060501d0038000000c808000602070b405e407402c41d03003a95a000702c110030001d45103150307229070800c403c0c15070005008210401c3d940140c81c100b0003032441151 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 649579181 1250 649577931 649577963
    0x31b060507110d02190c03020607030c0b0a05010506070803060d05060705030702160e010603110c1f0b04020702100f090506040f06030507020654070504270f 69
    0x50a42924048081408003074180c2c4040380c001000030340c070200c5a000700180050450100900404030200766034641c0c592002102580702c000081046900ca0343c0d400d01601120704000c0e0b45010f019101c10f12032810600100210f82c2c1ea002600c141035000b060340b07a0f030381d10780741c000944100314404010540c0c0142003c0007404c54200c0c0c0a18840d03084d94099a00d0031080c0c4801c0c0c03208918a020301e603090495080140303c51031095101c441142c0080055502c0e1209240740079141104007020030b10300586000381c0c0307084458503000d160800706056605504006850f4001801441880d40c000d042004400354502c038244500780440c0100b00140c00aa40c940c1c8950501081849500800f0082410400440d0b155440003502c1c42c841c3c070f4107400f85108211815125503440202c810b612012408040401140310a601ca80d4034044003960b4081c82c4516000440780c2c00c05540ea4030061040303103080340346802c1c0f140308904848842c2c010358030046400f519107814110348401c03280181c07000240944c900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 649580431 1250 649579181 649579193
    0xc010509130c8a0207050c040e07090c0203030405010c080705040902030a020f0a021b01021b0f0406170f1b01051b10020a0c06150302030a020904031b 66
    0x3050000c0c156503030541070002900e402c100075030742d00c1e00d1a88146094403821041102c4404540c11181c00405070601450030076090700070204060868201a9400304000c0e0154254260072240f10200003083d81861380036250540c540b40f0507040240101d0300c501101051480074400103001c0c0107004000c101c65007800a000390b681d00202c074100c40a40c60a042850514001d40c0c403640b062180da0b9400345881d041c046124041e410203001181c0345c640a01c04180c02da6240005000c84410983c0140310909840560310100e03081900340700e066410880c3e0380704480e110300c2024110404140c98070205030000c03902003402071620b61f005072150882e102060007400004641c08a0000020003201c050381040c1d0f030300b011982002002c85000c10010001a00b0300000d0342c001104001e4080142c1e826400d00d0f010010581c0d000300e120000141c0c20346489030070000c1d0342c8078141118401c42c44405840d4155404207540e1103203508080d20880c00a070000e81050722030384010508014081d0a040466801d00d00301d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 649581681 1250 649580431 649580447
    0x302070e0903120c0304050a170c06190c03140105150d111306050c03030f07020a12030f06060e030705010e0a1806170123100b0415020f0f0c010509130c 67
    0xb4442203e4004049030a4000200075030380155046005402482c0c405d070f0b200248120714506580804c4024003015880902c2800340a00c01c1d00800c01751440c110590030003404556a04c1c562405041c50500b030891900401800d20341550710607601840941c296020504103400b5008007000031501700f14040080723132088d2000d000000301c0041200d20064640c80161550f02903001124810b900620014203183c0079040300130b420010300d0054036085074142c0c5502c0c003e04042001013021a407100e50b0340300d21401d10300c0386000170034191038200700b03008010300000d844d6046413080a0400c5070130a10207171556924030b4141c004290040520319007c10b01903101c4003618842c82a81e00480e002a0001d00d811418010360403a0717451410441d2690742041c2c0c8695151001419240a80398a4880070035409152001403001d0464090b40200024034080c000346007241030480d000d055007001ca210020b000d030015460504203001d081c2079031980c4200001c550110003642c040380045040902c00c00820b5004094 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 649582931 1250 649581681 649581697
    0xc0d020f250305120606090603090607090f0302010c080d0b03071508061507020d111507060e0d120507230703020706030e0c06090f0301061e0806011503090302070e0903 74
    0xa01d41600507204180721151612180240100d14200705054644500e02c1159600140c02001c09040c1244080811100d40003218034050541c0300106000384103801c03807040c0e4020f0540d41c00d60004981540e00007000080c83c6000104101c00c0402c440c248110181c210209814001c4e0480b04942d554005400e03a170204100b40c8000b040450010406500740300f541c031031000f28102600c918004855007032040c0900b502d00300356403034803281c0800e40b083e80d18060b60440d0070540c8814252036540c241000000c403080a503c90060344e2046960100c004c0e08082282110703000500009101e6131000d405407480390184006109101c01c9549a010906044020744040f9000390b084442881d22150306030112180110b407035070603500151050340c05240c0b1000400c0e0703012015045e441ba00904201003030941d00150000071103038804501c8061180b4035000c0d0365000748000c100900140d450f101c0c0f103100c065a4030b40e1503c1055210300005c4241402000400001d08400300c110b8482d01d81200320585030b030000c540f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 649584181 1250 649582931 649582957
    0x3010b09190c0206060a0b0a02160902040f0b0301060f05070501060f06050c0c100207050f010c1e0302150c030429010609060e03071d0601091706181507080c0d020f 72
    0x2c0c0382e05814030003d0854400c00000d840ca4010505109004a050704016401d004500c03a031210701a40300c02000e0000300401112a0150b142e60170000706c00011860ba422002c8141c0c1d061004200e480e030b200c4030061150070303035083c210366422031030400c1c2c0c0c0903044035000107040540a08001504581c08002407030008000c000b9916250f040754104100c0e1096201d0400044e88403001c1030003079140c580341400e000f0605040c40300e020300541d55000f00902c01d140390300e152907041d0a035a80c14140c0512540103022000340c0c040550346000403040d511808050805000d074040c0040110020242150000c803d03804000e1010f50340d03950f1703035008003103070020f001d000001003054032070684600b400141c400903140a010240041641801c2d070520aa40040c40b01e41080558080010654840c80c0d4141c0300075001c0b0302502e49854101c02a5000d0f44482402c95441d50080d030b504030644001001c0c258001c00c0e5403030414100d8590072105125030040842e440c13403462001603841c0c048a182e00080448a841c24 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 649585431 1250 649584181 649584191
    0xc010905280203060402012f01021207020303010326040e090601030201110307050703060c03110a1116051309061b0903050f010c0f080a0603080409050415020f090f03010b0919 77
    0x29000700291051458025019401400072a0066005070000b00c1d00605407031003002800101070a001a1049a40040340aa58005580702c000b00c0c80c00200d940c08007141c001035180d0351565a90216201c48840014861041c0c1d20701203a660689004450043c09202181d0b0340c282465502280c0300c0d01d00384030403404038024503020302c0903500100a9410789600600985002444c1d9141c03c40500f1001300950304150746e5280c99202c0d02c0c103a00140504503542d5640c84044143c002080b4607111214501c04000340008504001390b43c3d5001d044070301c81d82034003004100c103c014a4060042c05c0fa00343c0c01c1111841e0300d403003000d405134049000c100304c0c0d0040d000c89156400240100b403c0b14005610500011280000c0000e4036018030fa005d9004800794000161850f500d403a640500c1e0060f400613014070b503c0d41c0030b010072320503008401c00104c154507208520f4a4400c1410f084544105544503004a240c1c01e03811000c0e55081d40244251040641665440c2c50300d8994544025131094505829038540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 649586681 1250 649585431 649585483
    0x30b090f0714130608060103050f0105070804081c0f0e010e060c0c0601061b0b01030b0a150f050d02040f050903190810050603091014071407080f0f0c010905 69
    0x201e210880d04409203071503100096600340803149002250308450030f500c6440000750740707500b040000d000314080c030042d00c0912800c041c1c0c04c1c2501d802410403010050724105001c04108010b048440e503880748514401c00e1a05007130600050010701c00c0711804d0714a0140b824210002c10740003e00314120100c04d56200d581c80e0610318489000d24490006945e00101c014412580903c030b03854054050004500d0904946039a50500c0c42400d0b042191444014401c2c490345404074050021410700f84288100c040e414510310f031007590b8040c0f048900c1100002c21050654030cd60384a0b4181c8402c401d23003400345143c402410f5540c0d030711041100c0c24220f0340200b0311903000d00c10124035005020211811103054905020400c0582026005804501641c1d081201401041c416510241100e0154040c10319090030068031400e120044004080c1d8100441000103036072800300c030921501e04401c0c68440300000c0c1310b0001c50052024080700d81d881d100e00c081c10301c070000030300c8100140c2c0808800f1000d10a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 649587931 1250 649586681 649586683
    0x2010f1d1501261e0307120e302a15040524180913110d110a0306021c0207020306040b2a09150901080a111201030b090f 53
    0xd103e40c56050f00032210800d2940801a600c5500c0d00c200030884801504000580a45000b400300700480c541c4001040820400340c40c3c15550094420b0520450004d0300e00081440b070030100910648078920762248a080c0d480500401c828140810111083d0040f28401690015030040040300003000415070350301701e8070300201031002d04460a1107050420f0f150406100d000c02c00d000075020701654020300100c0a013076040240c0000c400003012941540b410000f80040000050120852000b000f0030705130100d10011500f204d03580b01030b6078140520545d800e02c00714852544030800c0c1d02c00902c0200200384546a00584003c03101c22000500c1e150040081c0e01c228465404000c1d010303000200054081030100000c01d0b4001d003041c9000329604640100d01c5494a2200d9081000c04804142c000c15030906694415031550300c0804907180c1018100080c1c0f0000c001001000c8a40e00c40c0d00401300402e03071070b081d43d5000c54509201d140c0380d61240381407844600110356140651050755142003074814 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 649589181 1250 649587931 649587973
    0x70503130b0f0d021608031302010e0405091e0a0c080f010510031104050604380406033219050c01140a110118051c0314061002010f1d 59
    0xc2d01c8050b2519000509000c41c001c0d40200f40d884048441d207200d9500400d1441c0002c61240301482c80c1c1418103605480050100e5400050a078015031602c000c10840c401c00103041401c1d841c020080ca030000c40e05115151620741d503010010449213030b02c04e000540700e10000d201c95903d09541c1c02407245940b0700c0f0001031084141d21010308800035804a0707074241d0030301c4d5009640000f40900007094100c8214440a0f030410001e44c8244102c05945041300ca4291190680d0100c5008803028041e00e85140c03500c120100408143d40720380742c1d110407015841c620316500101441d49100a0303070206054000c1600504c2040340050702c0a00031040f00a0304c645c440d901e01c0c1c83c00b5a8084039641410100007080382e80217610800704440d0742d0380f00c9081401520021058100500c1800200a016540b0030415084034110700e84600345802c00b50741040c102e80140784680d10440a81c0c00c82c0051a0891049025016010182115600d0b1424a0001c58000c61482001e403800a046900b0041c010003540c4401c9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 649590431 1250 649589181 649589197
    0x50306070509030d21090c0f0609080601050103050c0706142e0e0601050c010501080618030a300507020c010915082215060503010c0f020303161103070503130b 70
    0x2400c100310901c1c520b4010b54505171103005484004880c000c0a440078012070728800c1061300e980c06400f2003003001d40c040705007483c00740c442c0d49016800c0358640307220303960b503501c044c09078078141500c0b0000240b8020702902615030702900901c0900060042007540703012040c040d03032543c14000c5002500700d013202c21105419010310220b04968076062034108011011040030308014100a010440c0302d14008090103814060303d1500b010b42401e0404108003503e01c042c45040b0707441c40c0c200b80585401541c001110003807a13032403113000413080440d84568101c403408201c07440c03051710f01d40800d020100b40d00040c00d0710700c10000e0b203030100343d180c4845a68450340c00c1c60451303a0018071500c0001d1558a10454501e01d2042144603e074240e0100703959400c0c0e4401c45807a1961080d41e1404100020300d002d010340c0c0914030207818035440c03180980400a48a00c401442009182e80c0f0f0208003038881c1c0326104529030118401d00f540c1d1110340c2454815102c0e8400d4181c2d406800d600c0c00b0228500c0c034402d045600301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 649591681 1250 649590431 649590433
    0xc050901020d030914240601030908070b040c0e150306070801080a080f0706060b1c020403020d030318060c050a090801060b0a140412061d010920060f0d0605030607050903 75
    0x6118010b0085001c2e04c1d5203401101c0c1c0d4590309840006440d010080d181759602d1626403c0b5000204940c4030b100010010080350406051060440200c1c543d08200c1e88155040301e07820440d41d03103600305107024019980c400585115030508000e01c03c10103500709036420000700c056844a40301c1031000c8880040a024641c0c1c181c2080500d0310004420000510b640182600144e0414085072144812580340d49d00500b0b800c00005200310400004c41c0203500d01b440300c0a01182080d0039074000c609080581040142851380d220180310104402484c41c4e03d006a10201c02d1084a04100f0028003e40054224002144c10031101050306103041c02540f041c1e90000c84598100601103100300e4460481ca1300c0c0d050440001c0001041c0192090651085140102d20204c3c1320b001402d00f50000d055000303843e90b02c5900d8a18080c00050707008200220780b440783c4013428030741d074054000150940700c4c1103140008040009030140c424406c5800c007004844007282070300c1840c2d4a51000391211b100f090765282d49 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 649592931 1250 649591681 649591693
    0x4060e012d030207050f060906010302090a0e03180612010305210403084e010801050907030201030f390203030c070206030a0608160305010516090e060102030f120603010c05090102 79
    0x9010b1095000c1c203032030f501500c02c0715042c0c180843e1550600c5020b841c0c0100b550003840043c815414014501a00100720f80b804200080341c0a0200d512806140c410301c1031210514611903d07079480b0001e945070782040340c030f54040b15603491611035600da8203102c41040250001e0811201d505130310302a40d04403500303c0c1380d0500d4108012404500085810b4003240c100b200805448803600c590040e9806a42080140700c00e00a0355295521151034140d00c01000790b07040c4010040014404210641225828200860042c1b03201c690701000e0104500d00d41052980e2501d40e1b840007001e003400f65042d04000c640c0d03808891250303804030780b01c0c0300031690100c00e04420040480142814001964400142000065000e4640780000d0070071703d2081c81021420350105051003403000a1040c82d81200540b14840700900d40420007401c3e842a5101c2c60440d1010000040c0c40c590081c0100c0d91044c22401020b0799520301190707032420710314041d91061f010b50310301281065410b014400b201d012040580080c15 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 649594181 1250 649592931 649593017
    0xb010203041a04030f08030402040b04020435191101030b0a0605030613060909050705040b100809070b210c0f03270d0f08060306040f0b0c04030804060e01 68
    0x103650400c200d202d22510404020000c04039018581c0f8401d5144140303c0f140e501d04240c010441134a8040d0211481140b04200410a50a0003454080c482d4081c02104161141400a104408000504026040c082d601c1d80c243c0ca051800e6900340007500c1440f0702c10040c07402c00c004404480000746141d42092410200b48005801840075581c040c000500022549520b60f40300d90540d80d00754003280324103031960304040c2003101c28444030019180a0f0f90802c1501240f01c0014002d040082c80c10050014480120b03048100038404d02028103112039a081e0f1f100c2402e0803404421034001c0c00a01d500d290b0030049031001c2c14200848081c03404c2e02c3d0000b800c5440e00c01c1c52002c41c1d03280340c11400c04003c09031a406003008042c0500d0f0752842c090b44613400d00410310309015007810001031030302d4032a40000040000043c80c03c00803102c240e410640c0c3c1d4103da42d401e01703080403a200f10b40000e44030038404500003030050707481201d03c1001c01d4207a0302d558540d051a101454140d0040c0031891802284580b0a4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 649595431 1250 649594181 649594199
    0x30301120804080a15050603010b0303040512030706060b09130e0a020111010e060a05271c1b060504031403070917010609020c010c030507110303010603090c090509060702100b01020304 81
    0x15100c50080d01181e14066558a01529040300780c001143d0303104080c2521040d4901c6445a55440001503000b4012600300100290716403240c3d004503482202c008000c03504004041046e9855990320140800038151928a01025a040303140c159100f51000c8810f00242c00003409450780d040c03107047c010f0441c0155503005464030140c010503280103650b203140d046582c0508000c01401060b120800041c2e50030000d1342160035000703588002c0001d03407100c403200700c6040000450380c20f05541c5505466050441e00011035981100c0c810003805a80b0011880040c0119503020304e0041e40f080e111500074003d40d2403440d0380f0303010464014000c9013102004105000c880b00b542c5903101d10b07072000001d089440302101812600102c54080c0030b0780d510304000724080e805125a0b9000545414050600d840c41007180d42c0e2840140150000c040c2c49030340000c1000307801d22603c0e0140407030950502407480c20350781c00e0343d45842c00c40700b1030018030609051407511284c9101d140240001a405146000d060103058 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 649596681 1250 649595431 649595459
    0xa03150902031203250228080307030e010615021509160e1e06100320040323030909011203020c040219020c0109061d0d050d1115010e04030f172d0108030301 69
    0x1180401c1039050f800400510000b00650ac1950700f81c40004000d00d01c11001402c464142e00142c001000345001242d007290000340540980b80101403030400c555840c000c440c1080280420303440034128980c80860303050800e01840e4892041d1910101c6401e44081d0700c081c4540055442030313040401c1aa881c10881e100350050541429500c3c031065441c00e0584414000d076200364404c0e07807851000043c1080e55104500c0315507540843c030004602300b418400005000300c0c018803c088225085c0300c40700701094028010740441d400000c00031500c80310001e9529160baa210b180030b01c010b01804440315004d600601e0302c038060360311315528800b88500e40c421940c405072507444410382c0f1007171007810f00c40040e00800050700740517419a19031541c0c1c14444032684c9023040f0f2100c0040040f80b200c0041c002c8020802c2d2041d07126803d0f20300101500200c003000d580c4003041c0c10350421400c0c2044100303d18074030503a02c0a505420b81152020070034503054020b0550742c40a0040e1510307a002000100600d802050790 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 649597931 1250 649596681 649596733
    0x3140102070c12050a12170c0414061e030106050c0d0903030e01051b1009030206070903050c040f0209091014060906030a090c0b0304111005090a031509020312032502 73
    0x85986a0b5001d0f100e041001c3d11010701100081e09403000c03806681f520683c40d9401500c60341600d0f0a040c1403404000f810300701881040d00422004c03c80d20021804103072800000c9424010141c4d9075611010b0051050784000d203d030f46c1600c1190101084544512000c6044036051f5403040d41014035000112001c0c0c1c0100030030354044103860b9038280c6000050119021040c1118400102c401c078074035000e424084020840c9041c0016008104080703100070405803510a03088500007112411801a00d0003801080078894001c8454010407540700b030300c4544182034a20300c03c0b904103003640301820001c4e140304602d99142c01142c00e2000c5030810b411500049407051103614a045415180c403140e0791141c01c1140c0035900d81e1b0507103034000094100b8009086a484075450810b00c0c0a4029022400c0c2105a102c000d1801a10300c000c459400d80c660301505907154000c007542c04014400c01880200d030400c1e101c40e01a00200a0f03070400410000c40c203942c050001e40c02600340c029599891410003900202 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 649599181 1250 649597931 649597933
    0x3120411040617031201290f0c0a0f03080a0207030c0609080408062e06021e0102090406080102040503060708060307060c03140403051516050409091403070b0103140102070c1205 78
    0x20119007051081248025030740c03e00c0003903488415481400300d5001e01a401007290301190721400c050b0f0012541c84810502c40b220805039601c8160b50500281c0c400c0402c00800760049150310300c100303d005540c03d80410b000e6500d0b01510340320700d04c03100c04a20070440700401080d0081d05e0400010b49a03000508480d0080340510b050540c2c0314412410210212140000e202595400c0d00c1074007004a0790318442600b94899545450a05d0030103540c0c2d03480c444501c00b6028002c2c03400b410260007501111300c02c02e0003404c1801000c1d5650049400307500b150086a109001c0c5000040c62a0300c00c5110910440008000b4240189440400e42d0170fa0703017000c026010805900c0300e0621001d0008018001180308030300600b81c0105c0d81c6180700700b401002c1d2a003015882d143d8520780c0e240f580b0505072015101c11040001d80c0801c0c515200b0080c9005000401031804041200f07414440031041c0c3e9812070307003e80c180c40741c49064502d03081c1c200d2091880040140841e00c5062044c1e0044900e400c68440c0701d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 649600431 1250 649599181 649599191
    0x19080a0c033b0307030c06141311040b0a0f170606030705010804050a0c17150405030d15090e160f0807060e180c0a02010c0519082509050a05030312041104 68
    0x200b02d00c0c00c590201c00300fa00410844a0000d04201040c8191600000c1000c201003650070089045541e000d9014409421807041e0302c603e00444d5140e5020182d1b0202c02080400c00716510340008010442c2440768552054142240d00c0d075200000c07071002d100380350050140023103d00b05801581c461074050b0082c1d0702c03442403080c280e0006282d41c110700007a00d000c0610505001001d0100c600d00040701d410000d940501e9014000080c07000016213400b003ca04501282c2c05580b200c000205120917448a091582041503c0540010109000c0c1404848030035528050380c9400005011000c94402d031001584169820004148500d0380201030410040040313081c0050b016a607910060141d034540040300300012040c1c800c540900c50b142c1ea40f4030034100301e4144500c0380c1d2003000000341d51100d0b0051081c000300140202c28a850740310702494200c10031083c41c3e00e01910082c928040d0780202e0313000740780000000c980341c907002040d0f504407803141001c0b033455620703561104a04442041e072503410580322 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 649601681 1250 649600431 649600541
    0x506071d100f0207150302040e090a0308060906180a09061401060933020606040515150c120a081501080c16020f0a090b040b0a05030d0e0619080a0c03 66
    0x24a000c01200b421741c0e402503203e90a00c1220220034001400d160265406a200000080c1d04800c3d11a4051022074544019a58040224000441a043d16504031120344e04200804000340d00c524139160041c0820046c0c0c00d8100880781440c2400e0040001044420708208482d615607240e00c00ca003400c0d00c8204684141c0f5400d50031320f600c1c6400f40030025820100400078641058030605603c46540c407100e801e04007001c008184442101003094911410000704a840008100f01506000000f5404d841d41c8404042d002001e1000c1a40e907440740105540f2400c149610680d00c960284031200741180c50b009141c3d012017039001c122001260403e80f0480781307080d035070341c0e658032030005024060300450301c480c1101c104011208051a00362250f1901071043c800d503100011002d41100b820304110511b4035000000500d1805284480c1c0a240d81c00d0901e400300980c001d024901503403c03050705215000384464181c00f692044000c541d2403c50103048654048440c000303810382c00d610362030440c0c008030344 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 649602931 1250 649601681 649601699
    0xf0717060121020a021023040c030f0c030b010504020a200705060406020106060e0d050a02100507050105130201030e0106030210050d020c0601090207050d020706080703021b0a0506071d100f0207 85
    0x4030002e090302c01640070442c0f0020b43d4050041c0c400d90078607140200550103140c42d440c4407040302c603120f40d0078a28030b07500001c04000d030b00000d5030061a00002c07003040042a6207800000d800c0c1d0b030300013200c19200c0c141c000900c6091500030f85100001d82e8640400c0b18840741c03113207682d410244106c3c68044c8100e00001945880740d100400c00703409a940046111418080041c12000350703095090301424003e0804400300b02c0200e0789440007070341121060340780882d1001c1103401d8000c0c0c0501601c154a04000d00c03c01c00202c1d800c50f070300c1030f10070b0700c0600c0050b0140d041c0d14221102071001a420840b000c044030001c4d0300c00c000411030243c0d0310384010300b809075103441203190500c00d03000080001d6001807840c0a004003007040b01e104138900d03c0148185400d1110052080c00007900480c1455000700e89205030f079000144070003002060344215680801a030402c95900c80e8252a440b003c6040d4419050840000d58801e10407240c0240070f5002c0c07a85500740803202c0f00511024001103008003100402c1d4824 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 649604181 1250 649602931 649602977
    0xc06050403090911040812090121022502090606030703110705070611030c0c1003061e03020108010f030b15011b12080a06050102210c030a11060f07170601 68
    0x20199959180b201c3c2811204070442d1030541d6a40640f40303091008001401c2c00140d460554255285200d807035121000058030b1070101d95940d10b40b107000c0890316024400d041d40c054240e5500c5040c002c025580b420200d10703030000001102a400a02030300009a090401d02c000b190041858a00011400e229110b0023030701e038110400440b01c540100c141000300c2c41d480785c91120441c1840c0302445c9023040506203a0350340c1801400321402006541542c80303500c1e010782d00000041c4029084400024070301e4030b4240c3d42d641c0310300049002c1150303c0008074a941001c08580247d030352000ca08155034407807a400c50b0140ba40c640e80b082c10001d510760045510910304837001060b600c542021040920a14800303070280000403c00c81101c1d00d0400100983da134001182140e6511742c03a1041801d071200c0c0403103000c80c0304451100034580b10000704111150b910104103074007000802c0aa0f01c141d180d03136240c155800e00c16a200c8001549841c5a854800e03038000ca8140c1120050505080e0a40a07455194802c3c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 649605431 1250 649604181 649604183
    0x216031a0c1b070e01080105070935150109180602070c0f12060c05090901050613170313051206040212070906091a0108071b0c08060c090a060903150c0c060504 70
    0xe0000f0000708020141c10000e14090541e06000740428070b041000103090700301d41d115035056090a880041c0d041c50b801303101c1c0504100940c0c003191035840c00e840c00c01d554140d80d00764070000100840c000140c1004600c00c5c5800b104010a81203449409521007001a4201d41425a14a400301c500000c00b0850b0000c07035002000020303102491402d41d410720700121022609a41c042c4035080001c0c440b5540d8a80030340d415280d04840390307034603024000c0821441c007503d80c010500e0020400310303000c05030a0020103021101d000c0a0102d425940f11030601c0311a01d42d0100a9001b81d22800c003003001441d041407074040d41c0071040700b03c3e40300d103948440a41c1610185c0e0701c0030385416030f618040c41a0003041100290000300a0801c6a03070360078007880007001c407425014280e2014040031b034070343d041111700300001004011810031540942480040d10540c0d5002248261181680c048001941800f406501c801c6030b0f08480001c0c2c030381d50415044009040d90110490402c4100404100042c82907c075a40c012 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 649606681 1250 649605431 649605433
    0x9030f030409060317030c03010909050f0f0106050f0102011a061b010c0903021318031107050a03110306070f020304050f06070f0614010918060b042007030216031a0c1b 74
    0x503a113103003424450901d019652041200b01001080f80003222202208d0441d0b07101e1200044510003814481d040410b1100c03d51714901600c10322205200c815001501030f550111640400700500714016400c840e10302c030b100e40c901902003203072008518040300601088241003181c180712180003c80542140d104508050104000150500c1036040200e100050781d9182e8908000e0050744642c0d0b09165500c0c0781000341007200e88006142c4038035042c0107001c020880608a02e108039100c0c0f900d500e0324000121440e00a128920001300d50701d2050110307001155503a00030b58981400c001c2403128111a0b51452a0410f0301080301034000b4490034a03c040c0c49003d0400003403c0c00a9541d181801c15060b4060340070113080c81c1e040c0039880f00e01c2ea0152062a44440c000131980560004200500b4041d03190710780e1014405241c0d02040f04100007400400d120ba03094520b8207000740c4078a41e505211b07010143c00380204442c000001c820b452056500100a042482c0c20f0178181800311200703061000700c008007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 649607931 1250 649606681 649606691
    0xb04210306210506151201020f0405040e0607090e07200109050d05040f05090402121f1803140d0f15090b0d0b0402090c04030f060207031709060c09030f030409 70
    0x1081c6407504034051840300c520b0300242c09816111640d40340c40c0036044020218410740320090664541070205440700c1d50750002d54031604441100d40320758201d0300c5018011030800710444200c5030301060711842181c0a48038807043c681042c03091880707014028800c105000c41d0346208820700d2902c424080d0072485040004c101d4648078900203003440c9182c00a17205000040c00288001529240340d0001e0b160309944001a6554500001c1c0105100d0405203100380203840c075144005a5154074907244203207100c000d200a1142703407404000346015140c0039000404050b03001d1132000045000307144591603450b01003101305808604000322110407280c10391044011500b080706050a0054040d5800200c074441d10031001910340c050a04401007000b4400d078012000982480042000e03070300995000f40c1c03420140559450b104c0700961001c10300f034000c00d10204400d41000b01050040b032099001101800403a00c0c2c61175010640e400582c01c1d2581400b805084650081f410400f40000701020030000c20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 649609181 1250 649607931 649607939
    0x5120c0931090c062c060c0c0d03020102090109081501090e1e0d11070e1825050f27130b0c030a0b100906050f041205010c1209020d0b04210306 63
    0x320701003038042e200e0000001201840d1174024100b04000d58603800342d0b4216590001505e80500740a074201405a02180d2060071070181681580a01082c12003a29041d5581303455040302a070300d008000c0501c008401c40030041c4400c4e5580c0c1c204c0c0380311402c60811076144170f907101c1140c14070154404112070654840060854015400110030400c2001c010103400c200e8105a180c01d00c03000e004084810019942c2d00c0000d11a40411500e50035024403a00c425400c1c1c0c808a40094080072886401e02c519581c0c4104425450035203105440c0d1442c0d07465400d07510300403025a040c00c1d8402803100b00d0b404040059280030401e0000d000303100c7c0301c2c19084546c0c0ca192000e003c804840040203c0ca0050010091002c081900700540d0015580c0b2400d0079034961a000301c044507030b8451900294050541e4003110310402c01b054109006058103900c3e00030083d0404c80e410022282e10440c0030391320114407000c100c00b08003a20940354101d4054144509071800c0c001c40c1070694089030400000203599003600708 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 649610431 1250 649609181 649609187
    0xb04050a0c03050c0703020613080708040e0145020d180c060c0c0e0c0d060303030b030c030607090b0f0c060f090d02061303030203060a0f0605120c0931090c06 70
    0x903413000c04501c0303040c148251510003d41d070340b400a00c102c03900300da403103020030502c50104113881e140d980c4403d203a551191100100600715800703109a07465549003045403450341402e002c103c81c010b0b500311442c065200d980c0358600300e16a05c0e65103445610f9820030441c2403446403406858801c01003100c0c9105003c91500c1c102207401496404001080920204c1c000043c01800c0c7c030130122030000810300e10a8494107980550391040000c00017a8628040d000020141c0542083d1504c000031419030300490000000e0503264007044030300e8400114500c1042c030011400e01c01904018041c4128582800231070309206203000c00a40e000b03150880c5a40800c80d1088041149101c0040c0741e1018050078100020788140380581d429004007071540100003c0d1580e11403401c050000c041c103c0e040c40009664000290541e4040d5501c2d40c6201c00c42c4e00011004d8094800325000d404000d003c402e19881c003c100301001402d99141e03000908001040c1c0b491409071400b81110480c014040b000e01039185c08000303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 649611681 1250 649610431 649610441
    0x80a020c1e100804210809101a0d03090902180901080102090f060d0b13020a030c03051b030c1624050628030503070c0801060b04030b0402040c030b04050a0c03 70
    0x556108845410a072642034410944101d9410064000c0d1100d1422044004070502044501c00d1036205c01a81507500c0000e0b1400f030b400081c15101714002580061054440d0a1000b90740038444500d22007441c1004910908280d000b441e0201500f0386403201e41090740c0c4000154940240401d00300443c03858488400c0d070060107600c008600c2d100804021800b0340b40d03500d40140c406e0b18003041c0d1009080980d0410303c00d144004058a2000d03071000c10100094209440d1400041c2c50118140800c1d4020b102d0b0f5401400404645890201a020856035991005002200204041c0a005010003414103540340c840d1284041c40c940700d40348016000b03031800442c41d0181082c2007200703000b440d071544191611840745030314514a0401300bd080205503244103501c0101a440b00183c43d41c14000c1182404055400007802409581d945804c4515180110b000c00303080c1681a101003030041c0f81c5903000a2a80075603044c0031940301c00300000581290011030300aa40c540d20346040c40907080d8503100d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 649612931 1250 649611681 649611709
    0x3022715040b030a050d0c06021911061311041109130902030c090c090d02040b03121e0403170313020a030b07020607030608070e0402030a21090b041401030f0603080a020c 75
    0xc110340c01c425205c40d50b44401e01070500052111072100d00080c4031158044445411074030140720050b08486000402c4140315080620850041c0408565900301d48642182c09a81001d13506c6e01d00c1e00e001040200801e0245d0030701661400400c0341888507110030841e038407482c1d2620b02c0003a11b9100c5006140c1004410301d4003907c14143e19042104405c620820756088050a4442050108542c404a00100400384e00268580b154204198007240040d0061440600740310b02054131660b841c0740c21031b0500a17804001c0811012142c45554081214082e42c0e0251428502d04000c4d4900d030045041d206998100f0b50342ca41a20040041981d0100075580c1c124200349020096940340c0f03865207859200d00c0c000c030405200d6100c04030381555000c001034050990000c25202c1607101c00715003c80084406d448070008102c2043d4001940b1091300155030403200505520910300588900450003456001d0806000310b984140200212364404042c182c1003006800038614051000204075103c120000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 649614181 1250 649612931 649612933
    0x5070b0c040b1b010608030f0706060807060f0c0f0b01090507020616051c0207080d021b010221130b010609090b032a060f0a21090c03022715040b03 65
    0x200007186000080f075100888031078018035081011071026014000c20f600c00c00740d500c808a8449050b080b0080205a810701c100001c01c19241c1c0c441c1c1c2c4540b02d091520540001c20280d400841d441c2e4000d24684003803d2140311a040310b024141d403080314404080c3c105161059035441000b04280d0100a507913000b00e032000703a81800340c042150042444c800da1072040c030f070714650107031030300940e49240c040c4e52503e80e00c00045600c0307000c50320380c0b2070094103c1c04200c100c47c1d10800ba41406200c040c4200c070000041c0c039450114243c10f14140340103480b070140410511b50303601c0c0308100c00b0610b10714802c1d01810803551074510306440e11390303210151017000704003610980004000c07900c3c010f01400218020460503100c0800c0041020000c0c455014280791400752000c00200321340d04951010b40500c603000485580503040201501c20000c6550011008000840c5e480051001d80340451100078000c40407808000c80e8105103040040b0040182e448800031180c01e4400051407034540030b12580003405034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 649615431 1250 649614181 649614187
    0x90d1b0b0103080a11010504050d021c1707111005061005041d060402040b0403030e03060c0c19211107080a0c1e0506070305030406060503030a141b01090305070b0c 72
    0x24941405800042c0300003090800300251140790389001d520308080c1540188001c222501c0d0074180141ca400c0443d44010040c001d214099203042d07070300e0780d100381c42e03c21550f1114200c1c035641e12840041c10020b812101841041c507603880c0310442c104042c81c1041c0074101c010860b420800e082c07019080707030b103a101d405100c0180020300111200344000d4405131441203134040e903a144c03100030030002d05c030302e410000d148940000d021061680201030206070f400d081d421a141980e0300415405c0a014041d451a400c1d0045d00c0303100084001020646030f000e010300e12a5a003800c045500c00d80908004030700c240400e2104c5620701e07a1900030712903480100701b80c02c090109050741d170791940b101841c140a030040d544004402600229440281040942405000d5995442c804c0c200540030760401c8038100d0b400d9040c40408541820040305441d00a45503407a0000304c45c15802e910351050b041344440c0700300030740003680c0c40105e46024000d00b1105402500c0303090740c41c000ca04200034120401044000c15500070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 649616681 1250 649615431 649615433
    0xd090606080f1b1f09030308060118051324030b13050d0f0243030827100f081807030305030403200105011401180e04020d0b090d1b 58
    0x843c01954149940001c0d07450030400c071000a4408003c1c1c01e140c01e040010400e04d83e00a074012102030240e0340240c4521449540d6040115039003070903040e2011040c03030b0000c410015400d000c0b0b01200c00351490000801c0b004060703110095640d5004080c00e218801402e0b080052014450099421102caa44007202400e2180c560b0b40c2e0f9200e0800045041201c80c0b09030f040384a100744a40c4050111140c8c00c1040320b214203a20955540e400b8030241d001410382c042c80428043c000e84410200c0e80c1c001152030030801100e50384003904407018025080400c540000f0b07080340e03848080815648104d80c4030a5003000c5c46010040c0380c00c07001032450001888007030b808181c01000203000c20807640d2618002d81d9a0b47c0d10302d005c59a5800400b070200c00c44440c141d103604d0032001900402d043e21100398449101c40f00c8400110f401594079100c6203101218003005102c07541d1003d10342640640040c161450825550740c41c040302050441d0043c1d0190069030141501550100c1560100105404422034107002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 649617931 1250 649616681 649616683
    0x1c050405060415050d0e0d030e0a1718060c03070309050a03050c1507051e0613110904020105091e1e060a0807020c270702070f14040209060d090606080f 67
    0x3030b0380200c80e03202066250440c0d079948070b8070440e007603c1c4064006102c2440451002c0c0d80d07071020504c1c4500800c2c02e055403d0804940000d9850f078858000e00c03005500700d00e04a2100c243d034880c0b0740003006200400003a205640301c2c40020880b0220300c00003540d0315200e604000701031f01100c1d040f080c45641c0502c0200040760000032014050001104c01e01c128034250000d44900380b15000009041c1d0065544406046001d0100d051401302003600f5030342c1c1982c407040d84580700c02c0c1c0200028101c104190b808107807170500381d1035180c0c040c0c41810f00900d0301e51300d81c00242000740c500908060345507100415841904100e580041400003001103004010080da0000e038881c080c500021040112000005c1c820507c00c11004d0303030032000036200c0300ea101200e554034080600031a0340040d420019102103441036100003080403c403242c2c0148480725a00305415400c40311031840f070041d409030b020f00050040d666842c0c001e01100340110400506602c0c20310b000f0041d0340480d0301000c0c881d00711404003403001e04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 649619181 1250 649617931 649617937
    0xc02010501030f140c0d05011e0c230c070b03180c01050f031003020909151e011710050106030c1b0209061909020a0f0801090b060f07080d09051c05040506 68
    0x262113120300c42035810754860180740c03070400000c0551004114800809100d03041d4048020f50416082103010a40c00d030701c514056602c12518900090a544d0b225240200c80105035505003141c03a007418a40042c0d01d980500c2c10081d508148859280081401001c0310412840303407140200001810a007079144001a1907801041a1200e08240010000c2c0e101c1c9201c1540b04069607004120392038600780420a03d656039500c0040103901c051110100f0385142803680710071040c0d60b00c441d605103542c1c24a011110400e002c2410800c0d288a281e04201a0705421701809000c0e00341d42e6400980d88401140041c00c808203100020b05d00c2c1083c03002070015840342186503078054400e4803900400c554194100a0141480e440041601c0c80070403607586081e44013110040e04c046668848816980b1403880c0700272580e45c0000d42c1d40c400030808c4038000e480712010140c040306001303c1e5418149100300503520140c6103004d04c00c540300d402c51112070790121802c0c103019005c4d10451800c10700781800c11001c105184 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 649620431 1250 649619181 649619183
    0x2040e0a0b0a1509030b2d06100309080a050901052119020a0207090c0203090406030c06080c0309060610110a03020c040f02090d06151d041e080711190b0304060c02010501030f 77
    0x1c0070b0308002941c2c02a01d0f00b06603482c01f00091440544003442c629416210b1026103800f0702c2810950154990240310f80a680c00c01c68204030110b1030407441601c162410340c00f0401c998140310090104465040c880000488060007542210121307240c988034040c50500720f8403500b0318291060090300c160701e90005070b0b0400d0742c411000010745450300c0382d0164130f140034200a840d40181030032408410031403000d09140071214a5202e00c885500c41010318802d90004a5012040e680100d0000ba40e6290074548a40c050106017008070740340301c200b02000d05208440e00160051303486100720b05c41d6802c0504c925500d00d500f0300c1d021030030014400e0014000021840c000b43ca03041c0c50b00c1007151040d90b40e04000c802004e808003801c640c10a072200e00302c81d840c41203400782d440c1c0009143e8800e483e20071405d1030591a0b80949150b291508980c0c5d01034400070b800349140e0300041c888083c1280d80e000c062101001d418810040d640b40e140c14540002030f508100640300c1164141801000003818003601c6c0c124036 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 649621681 1250 649620431 649620443
    0x90c0909051515090c0f0c01411504051602060a18020f1503092116060f0e0d180807080703150b04020a05040801200d020d02040e0a0b0a150903 63
    0x307902c1c1c010144015001b19054489140c900080c41d030b0b403c031015800840c1030780c01c01101900f6034051a0414002509441198022001000b80c80d42240402e0000d690b200904458201c001040000420104c4074200d5445058804c1880101503081c1c0411903a03512041d04c103020700002c2d402c80c1a80c4882101010024028810f0000f560456954220503c01405040c070101e81c0301e240a902440c0c0c2c0b060890440141d401e03001035a004905400d80440c0c08101d02050703c10f41148181d91144010044140d00c416001d60b01c0c0d00190240c0000e120f04008100903640354030000710030b00501010060b1941c0002501e500c1400c003082104800300700032003120f4210024402c0881d0406ca00c80290003c0301506900c00c3c400202002d5039030f081000341081d201d48000810950301c034403040f143c00c01080081400020307814005080d0007145500107142210801c003000d0b080c550703151290304682406941c0500c28545400452a140c1030181084004007024008440250300050300640200405c1c08040e0030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 649622931 1250 649621681 649621699
    0x171014060a0c122a03020624090c0d1a130c02031207020304171504080f0d06090203160c030509011d0303070501153303090c0909051515 60
    0x50340c2c042d00082202d6a080451101004184000100480c500610030007940c10145180d1944200b0f01000c441d072030740d250300108460f40300d800e405c003810100380b01070f900c058080300e8078900c0b01d4652504460142d01c03040a80e03a216000d030704250003520f14038110002200c02e50703000c01d10140c1e59401c0180d070903494103800050411420b8030072400c40c81141c648031108a8036006100c0101d038004000c10494000f031300f40d2140104d42f1044607071154040f8000805001d84030300400d0104000f50020a100304001c04003a2074941503035014815031303d040d404010000da010007004040c0d19612102000d155051901c000007200390303600608a030003001100750420558200003511072300c1901d03000c03500c0c0c8070040403282c0f03400d16890298081e0404080801d1480b80000f0b0001c0c40b901c01c03c0d65000480d0314410141044c10910080c860107001041d80c07035081540320001c07800402c1c00b000c0003601507c05000040b8896519042480c0781c04543e2825483e03a2501100b045690701c1001c2801c408114100c900003c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 649624181 1250 649622931 649622947
    0xc020609040c0e0901080703031d010234060206090f030a08070e0f0d0f05210d090c090507020a050606060301050a120311061303022103010e090f0d17101406 69
    0x301070300c4940f0060f412040c004000315060400162030022203220350f54014400c0240d9071803c450900d400d14490241c0d0000000303103401124008041d240444441c10320749140c00c214504480301610743c0c00711f4056080780341444034204050000740303600e850000c000c51408481c1e010040c03c0000c000c00003404c00104090a000940d00c4002d49540a40000c20060051203141443c00c0c0300104004102c0b400d1040c00700c00100741000c4103141c02e1800603e45080d08000c01148800c002e40000203046a10102500021030040c0c0d1a100740c030700541480d401040300c1c0c0802d191151070101c02414141c825101800100420740d00c036002030055811030121050f00c0b40b0549000c3e202c1d8840c4102c0c46196003c3d046c1002801820900c40340840d0b802642191942d070039940214044c541c1480b49052002d404100601005069414040d0010031103002c4030841c54403c502c00d41092000c405840014090003040000c902410107a0781d00520103400040d000e91400c941c85880400c2e4000c200c0c082e81010600c00c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 649625431 1250 649624181 649624187
    0x40e0a090203010218190303050d0f1b0c020a0801050906061e10050d0c080c19020a0507080706030b101d03030403080f03090d05072a0b0c0606030601060c020609040c 73
    0xd564058029500c0d5007119030411551401c0c1401c0c0d501403e054100710303400683c0e122211045a0305500c81d2031412501c401007401070a07001d080c88a8194485480d500513102200010b911b483d000d5441e0a1085547e20422500040c540e2140b25185c2c100014011740f20400f040080d000384084a0451100050780c0201c06400210020660b000e04c054202240894204000f000106103109040040940848007550100703011344121031042c10600491f030907280b8505009000301d80310f00454002d006070ba92070b5898034202c0c0e0808501c541001804100300c03a010301031116000000c443c07400c2c00b0902240c00070010000140000c000c45060052280f298a0138001c98001c1c0d0342200d429a030b03c99030080010230a40c02074414160034400c0722400d0300c0051203101550141d0b80e00c4000b044030102c210412400b00032140310109055006294005005c2c4042c00040ca0803003022406005280b0f0f00c5401c050501405a0090040c00800c1480c05d00603500c2da01120b85007842101c2c00151926005021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 649626681 1250 649625431 649625441
    0x150f0b03040f1e0204110f09060f040e01090c0806010f05030601080406020405041805240a0c05040e042012030d020d0f0e06091204050d0b06010c05100c12060308040e0a 74
    0x10b81580000c039800d80c07200143d1810011180d00039074082c045e4244040344059244500161070404603414440159103103000340050031108480140d8609283c0c541002100b200d10a0b400203020366a5910310071821744e0802506681302600b42800b2900e0351b401d0a0180c07051000410190420082c1400501007060a80c10f5601900000c2c1041000800c40d4502c0c0310721280044c800d0718070344a01d0041152804064007441d0045c3d43c00000d500342500d0707021640b809041103014407410302c1401d00003ca082510f84200d1403285004084011503e40b103032014906d24006104540e005802e0790308032410002c4000100c0b00342880320000180c3e034414480c80b0038002d15150014144207030030316904602d07810340003030f050740914a0001075800c001148880e040091003280309140c1c10035070f4400d0113070209841d00050b903030100c018101038410154a564035030801700121115281c06035601e1084910540c081400800c02440c000308010b0142151174080c800c4c041c0d40702e07101c051003000002038110003d54001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 649627931 1250 649626681 649626683
    0x6090403030c27091d030a0c0812070c020f102f0d02070e07030207050d05070f0611030118020702031b011404090b040b0d03080712090f0c030501150f0b03040f 70
    0x180707100f403019004005501400900c0303074005aa040041e030071080c88409041d64041030402d030055190195410094400c1898104161200e1901380682186454220003651169000c1d0352040e0208480e40b0400c805108003000d003600400c03034291000150b50b000701c145414542902001d000c022081c0300c0c913492603041040c55103614064200301c056030361340004840040e106482742d5007296aa440204404074003580c42c02500d03940c0160110b4544600030001068aa40a900c83c111034800c5600c99405541680781d048030903003c000010440f42d190100881c0b103820b44140c042d2724183c10758000aa41c4c070908190054456442d9005a0850303010380e0302014940ca61107a46503d450b84e0f01c000c3c030000c040180000b401a030801404070f141d881c0c034500040d0410341c15111a42c00d51261902101d03102100364070380c180b656a5000c0310000c906000c5500120520030329000c0b84031411842d080d4203444000014501c0d41402c0c95091164109100049042c1c3c2c1403103a04684136507039400c080c518a0003c0070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 649629181 1250 649627931 649627967
    0x604020c01020c030316020a0b0c030a0e0f100608010603080415030617010b190303120c0e061206030c18150609060c061005060f09011407060e07060305060906090403030c 75
    0x510380c3c5030420040091442500d0200f051400010049010380e103c0009400044c44070001c3e80000c7c0403003200c2806940c1200e400c2000040ba02d90040315145406100c0101c0c0c0d500d584000c0d210344140700c040c0182800b0340600c1000380181441c50b03880d40c4070b40c041c9000c1c0140d64043d00045049981c40b1360b101800410301460000c2c000381f03c14000c94024a07030418058007030820411550b4291511030034000c1220b5048e9200a1002414a080707002410680c00e648208036203424a29520396a21015040d440c0d045104c502c2e160600908041c41d00018075172560240842145054000491045881d4000d00030640018140144000240b1610a01c040181c0c030800218100f0146040000c41c3d0744904070b84020000c82d10b4075142001120300a100c0c848c000380750100406048ca51240080e041c03400000381406081c034807103685280541c3c100d8a111269030344072140030426035516000f41c9800c10001e541707113119800e04070007250344d03034400801c0501455107501c05449064070403840603180c10f921f00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 649630431 1250 649629181 649629187
    0xc0f03040f03050111070b0601030506040b21010e0a0507060f0c02192606071805040504050f0d03020702093405030601270302121f0b0a0608070e090604020c0102 71
    0x40303010319a2501d40801d944561a1000300d0750703c4410582210790480c2c00c10146010355660000440250000404ca140c000746c070b400003075180d9100c0300d108600007044001c1e4240541c560280c0903003141d040d03100180c856484600d018011900101d095400d84005140c80c2c00c9207161707448280d904017009140250803044502800010402400030901030791500068460022900c1c40e25440d5643e940c1f594400e1504007402090b0164010071084030381d0781c00e14041803000303581c80700021308940c0201d80a598030340000350040329150081c072428401e1001030801314100000d68010504401c0010100041410300786400d51811684007241e400588410343c2c810304541040000904540040e604030b404683c0c10219051035000c4010a10050b032080d000f0a49060f145400700300d41c0c1075607843c80c948940a410101900c2c0c800462806000e40d0030160081a1005610300340081d9400d03d5001c001040551820b00c03d074a50b02401e0034070320790303030454013404079494100000d402849141001ca110790300c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 649631681 1250 649630431 649630439
    0x70b03070507030f0f0e1c060203040503220e01030611040b0a0c020a140d080d020c030403120e0d110d020609031b040506030a05030403240e06091c02070306020c0f0304 74
    0x84000c15a4501c40d40c4c4000180c00c00010030341d100300f00001550f01203420942d410300241040500f03c110f035116141004147c60054031174004980c01540d041e20240c10001d1841c2542030306000c43c00c0c24001a441d9604001e19080c0007446c811410701004200c25150420744801000c07020548024100309400c1d155213080c0880043c040c61003a441c1280900d03011038000464004003203010740340100c003500741d41200c2c0469840000c01c0c5e00401038005400da0034800c14440c4441080940003541c803400800841c030000c100c01034245094500b0081c440d03004802c43d400016214000701c000c540d81520781c80d032596014400942a0301440e04aa60548030350070301c1120300310620902c40d075030075410742c0c0802040c3c54403001c1c1916500c11000c043c010b41e00030403007000007500f400722810010001180c03800100050030311480503a541c03030240074015400f1805010000600780117071b12408030b55003580c6400c6040000e01945540243c4005404a50701080002844009000b010708100c03003042941d070b4550701c1d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 649632931 1250 649631681 649631687
    0x14150913120921060507110d050705030706150807210209060310020c030909240d0c09090c03150510061107031a041a040f06090204020c070e1f180e070b0307 69
    0x100f044140d030a02d0503c004035107542e00581c140580c1c11804009050340c40c282440c02e07220781d0701120382210b00744802c0240b9000300f4150f21581c80c844030b145196000451811070843e1802e40b85800540340d00d00407030381000c0c040d250006000c0b041641070b80c0101e0683c0c2d5240009040002d0000120748240c000150311024500100040c480000d04884640c49a1580421046800503850b1445411082a05150003525100c04c4035030741544036110100100c1d4075403003e80181c840c180c1d0100d801e6044448140104007450018a00055009000300114030740060805100d20b102d201d007006110040e40003411300b540902600003d1034000d84817440c81c050202d034040342841c0494080c0d070084542118240480c5403912294002c0d0380110103d0603c10141d00e0ba0001401400c3c0100e90050b800c12213214081c3c42448a0b100910a200f81c0803458030300310070700312060712a403041c0300b80c0280c2ea50380501c0703c0458204000f80f0103980840010b01a90101c60103841d00c0f299802c4804800400f20401a100703038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 649634181 1250 649632931 649632989
    0x140403110d0e0a030b06120a0c0905060409021302090d020301090516120305033105013c0f02090d080c010f060b0304120210141509131209 61
    0x14560049070300c40c03210040e00300e800c01d5070452140d81c011035507641000481c0d1140d10840c0c000000501d10080c25080540b110700d010703000c24040318898054030701041041c038244115540898240c805000f0100c070f6a000920a00c80d035501303851899030118000120351640100701c600725a014000b0400d1b102d16080032560ba2000b0b41410071020030007500410040003011200720301c241c3c540c075080c2c19621144003114040e40c484c030080840865000e110710703c1c140000456014540a01c0001900050500c00d407440414940101c5581d4001d01c8441202240184c0c540112902c0070200091150b451251b103001038459400017a5000508005400500003044000c2516001d500000c0000020130820181501c0b072030322070104080e0f0180005000b081050300b01d4000020300d8415030745c030300014112a500b1502154881c442d818412410825141d231200380d50154200c04031685815460102c50303401410306441c030010701d0700c080500d01054450082c3d0511028003060400441c0d00080c1d503000318400e907 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 649635431 1250 649634181 649634207
    0xf030b060c21070305030a0b13110c0609010b010c0f0c17060f1302150d060b03100305010e06160c1b1d0a05071e05090a1413020319090204140403 64
    0xb00aa8602940d000c6060040300c403c207525403280c508656500303d00710024280c6807449a00507080720503100c02c40700c1d2445413126600034000c0f080d4448020b01406407620704003e080b540183e01d131013840842c5130b030080d034058070080d4403460b00548054145803a03007000c40103600036922074201060040c080000414120b11685040301e1110007907540528070f401069070904041e4002405040d00078100811300014078850f0700041d004205696500010f440c00c0d40202e6444c2d0030207040703003024801c002080c0581051801c0c0e9600401c0b0b9400c040d000c503608841005a000c5c1070002c590010400c100c0111110b01400c15890031503070405d40e6840118500090400314140e054003144002828104107209035800703800107507200c0c12003c48000c0070107511458140074005010f0103010601e0703036035103681003040903054500e14004400c01300d0041c07101c140f0115003d038061900600400c00511822009040c0c030948030407010034000440d002040c0100344224040f20740700d1000041100b410341005c4843c0c400c13 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 649636681 1250 649635431 649635463
    0x304090612121e0f0302090d03090f06051206090403110d0320520311030a0206160c021c050d090303020c120c0901030b070905090105060a0f030b060c 66
    0x5441c00e940c1142e4410000d14101d003003030012000302050f24800c0e03140300703282e04481c10010300c2c001c55040012000058160100e0008008503030074048028000c102c4401007840703007031a9082021024441c20071a10042540d801500c0d6080081c0a241c032a18400e900c100401054801100382c04070020042c1802c1c5020384921052001c440305d071344000008840032031a41d2980407044809810581b403c0f00443d00701114007004120381d20740c450740038101c005995641c41d0f840c500c120b2118500a085040710110400c1541c00a01101c0da0407900441c607642e011070308042c0341d1055000d40900751045892694080c0d004800140101255030860340c00e990040c0c0100102e49010070700440031038110807540001070040e080342840e900d880c01c1240a0408140a0b0750966039582c00ba01c0119039400802d0b03000f56008511181800700b416041740710724000c0d080540d00150250f0420002c111140b01d49012201000701850f003807541c080c0701c0e03030107104188401000b150341d880d801c40015646480e000100c0c694 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 649637931 1250 649636681 649636703
    0x6020a030804170f13060914221d010f14071407030c140606030c0306060a1406040302030d0f0305010e0103030e010c050c0915040f0626070b0304060515300304090612 73
    0xc003403034600d800408c0c6c0300108032900d00d941344d1a0090064408035400380c03559072220070803402c0404403900d41161403140e2000049410788000c051060380c0180c00740c0940c40d016072061044165102c51040c2e9015420950305617684018541101c00080e4454041c1c1001400c2c1d60708890f1a0000c04e01900840c0c0c02c604403003d6404120805484102c00c1d18025030082c0352900030000b1501d02010240d00d008014286400d05503207401003401e02c3c6503954060001603040b8440804241c05200f443c0c003400c140d000d000069810b540c0d005c4c00700f41c46900058180004030681c202005820041803025420280012141c5d0500300302c000c1c443c40007805500c0c4540e09141108204a42e51310a01c81284c0b03180804842580c0310720000c01a290300448090400d0050340004503c20302020002c601441c4a07410024952238942d0841d02c0b41100c1c044443d100c3c0d6080c600d42181800940c00e5511008004035004616240500c400ca10350b100350f502c0038451500303203500003c00311019540d45410500032403003405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 649639181 1250 649637931 649637939
    0x103031d01031a190902041d01090e0601030f0f321903111c0e09150310020a020f07030f170f0a080705040315060303020706020a030804170f130609 65
    0x70f0f0751003920700c207103c4500c1d1210140c551070540000703043c2c60341450844e00c049480f007018500766449904009036406452845581e001000b6040700c0c01408003003000c008561482d4542030321500107210140502540d41002030038001030002c0046503551107000c51075496240390b9196145001e034129480d862528075400c1e10036200106000814450313154400c0d441c14034a940a541c4051001842d1403a440303600c034501070300d5400e00e007104003030180c44e220114642a000c04001c50321600400d00e45180802032004001a02c0000d135030100200300300809a2102100003007285084001d240c01d415900c10360b00c00106000c1086000301100b402490b90044a080c4804842168031405008000d03180c400c0000082c82846260442d800c02c03500d1400b5494603640381c0300c240ea1420071400148946a0704c08003081010f404109440040180d0b002400003011291030191007400d004002600f8026403060600101002c01c2c1211809094600ca07951100b4061a000c600d04045010310400700d0b00144002c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 649640287 1106 649639181 649639187
    0x314090102280507150b0a0e0f06040501030302030a032007062a0c0f02040902090f070e011403010b0a03090206160c0b090f06210103031d01 62
    0x35031948041140300c2100001d0000542d00d200d00b10801182e60354002c41582c014a0304006195207611720801d805002d032415880907a440f01d14014085551440c990459003c1c00b01581d20b0003135681c84030244400c4071420302024015074418051600d22601c01e81000070010035400300c2c21280d074034410354400150007442d011506c4544072403424201d0ba4204280d45030405900303500e031304c00756044100039150b4400f030080901115566071400044d5201c980205092650140036031085140170000c1504104040d562000050000440c0301815031082c10f5081e0a400040300c600c0c5541d10740621102ca540c0459880000c0c15115900000580e6030300c0081c2c070b07180706c065040458172480c62170f02c01c5000d2140d03082985000300901070030005807500704808000380000d62308130355107040c42d2031701c0307149480003004020306405980008410150702070790351000041040500091030907401c0041d = true := by decide +kernel

theorem cover : BRFrame.Cov 649460431 649640287 := by
  have h0 := BRFrame.cov_init 649460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 649460431 ≤ n) (h2 : n < 649640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
