-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3675
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:21:05.780926+00:00
-- url     : https://prove2.me/submissions/40796ef2-4c33-45c5-b02c-df80d295b684

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 660791366 ≤ n < 660971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 660792616 1250 660791366 660791413
    0xc08070c03030207151e1a0d0501231f03020f130605031b010e03060907060c0302030d020715050708070e0607050c060c06180f03030121140102041e0305 67
    0x1d04000d07240020944d100e81e0702500300001c5d04d0300c00342c0e00e1840344000d200c41200c0c84001c208401c810440b9940300500c0d010881c0e0880b06591003400451800d0302000030039081f000c030711520280045079a064007400d001940300100d81303010f4200928844524503856040007001100d0300580400341c88846001445003041c0700c1c070703c40c0c400582c4030440040c2c2d070f4a0401107601260704000070248026801e20004003400c404000319071003940031100703200201201180d0101142e0040c2001c0081110602e816030450042c1489804624800b140c0801801640c1041030140c0e160050304111a40d144181500c007090161131100c0062030842013000182003480043c88928064022910020347c00000209030342d10905801c003264010800303015600160302e40d011420a00280500b154040c10304050b42e480c0414407400720302c1c4030441c00c000040c8034208110f89440740c0208649403440b5000340840c0c00303588244110f80c003241c003c003000c000c4000001001070540703904c0000b03850443c4d0340d81e02c58691f040c040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 660793866 1250 660792616 660792623
    0x120e0f0d1407030501051b040f05090a090213020d0b0f0603070309021315060f020312010b0f090405240105070f02010305130f061d07051f0318060b0a05090c0a0f0210110c060106030c08070c 83
    0x6454837400541d0301c0d00c80303559030b60f00b400c9400f682da004112000416101034030b5805000d001c0403c0b43c010320781c0d40c540603250b00c0700d410705e0b000501241c01c0c000221211240c10030440ca4a01c0e20b061404500100300c2c500c0160380b125210082041c00c400d0007281e0302d1040e41c0751040010441c1d8014002207103500020001c4480d00100c10742003602c8000060700700c940030b0321502408001005000c1c001c480c8544170080001d800d017072950070903000343c68030700d500780c0011002410540d50300005401e08100700084000c090f0412014210202c651500301c1c01000c210b00c00a03445c0142241d2620310303000000311101a0360015000c2070031048403010402d803840d000118001030580360012001007242e540103c4400a00034440891036540280070300603c84400d0701f145005969005c10000c1c4d94100d4811145100781900e4850310400e00d22008a05200d1544800c043d145c0c205407240000320036100141103804120b0042d6812a642c81d07409800310341441c03d0000200c4e01d21800a40114015440340098031700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 660795116 1250 660793866 660793871
    0x611131d0f341e0206040b15030307060203040b06010206180a0b041523090d0504142209050106050306130318120305030103120e0f0d1407030501051b040f05090a 71
    0x290040503802d801010386001c000a05040785411200c1080c080e200716806150001e4400d6041c80e03212058014070080c15910351040d0342550a00984003042210700c400e40101c411502c0381000d2420140d0320304c1c1600c0c0d05006100b201e022a024401c10320158250b00ca26400501080f051540d0f0300d0b44143c8014400c0d2009800255174400612090050113000c11043d5040032400e040c40d1505201240e016158072910307440b810540c00072540060807070f01a116101c01c58000da0001e1000030b24255620380400c1c51b03440c4c07072542c214050f81c00c0d5044070358030078400c20092050544030000c0c50741e80e03402150f4040c28040c2e20385007000403d0240c5520500c0b100301d101c0c084800c6442d0502d220740c41070800b20890004100000400074841086c01a61070061146049015081004009184c414006880510401d641d00d1140100702d20300803e180003a140c4025078885035030340d042642c02401d0881e600000802215884100102258211303001c3e2210180ba401045060506101500380000c0c10b0354a2590f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 660796366 1250 660795116 660795181
    0x230c0a03020604170306011d0f0d0c17060906040b10030803040b0a05070e0d1509020d080703022b0c0c05210c04020702010206060d0611131d0f 63
    0x902480410901940040c0942e00b401e25008603240c00b44980074034426821310a201140ea80711521810181c2c40f84501c0e041a61013000007a1504000c1040541c8618105182401c1110003c00701c1c040314101400b040611441481c070381c0d11080101d401107010340248c00000c000401d884011034120003001c1c42d80307450381c5e1250b8840d80580c0c400e5a00781d480706503c104108040348513000301c80d40f1034114903002038880c50120101d9800c10140304000c0140c148a0521491410304e0340c416074580740c000f000500c3c05505070605c00c800e64000242500180644401c5055051601070100d03000c880c03c480007050088141f40403910b01213480c3d400c03224031442c00740004031940c60501984083e24841e40310703c07044800d02449460003440d0708140f802140107110b03050150383c022403280c0e44507034103441c5081c80030420301c0c0603002440c40c0104080e58500c0481c0800304e002320702c1030b0202610228801542446015400c614840b401124503490b524a4040010300c1e101140d0310303445810724103108680303180 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 660797616 1250 660796366 660796387
    0x24030618130c0506252d0b070c050c13020d0f02071a01030b181207150b0108010f092403030c05060606040509011206110c0f0c042f0d020403120e040c23 67
    0x1500c1c404406d0068000d00e034005806d101c011220f983e00701009041010326840c01c1e40d0f455489140c500e44151003101101d0207030362900c81603011540c6d003120185003000703000c6004c03c4560094000320820355240b0030340740c03202e514411840305041c162030700600482c60b20b590384041d4100300c0390155071002c1203005101c10311700c80450920141c03070054400d250b5041425040d02a1341c0403a20f00c0710820b810010703100010040c002080b42c068045e01c9109101156480680000c00030310020f81c540c82510880b40680001031540c040c3d4541e0b8082e1040c815203c0c0da8488100b0031401d4021070041c00d5005180c140104400000004540c0d20b113407280d0760100706a08007222144280e0010b01480c90581c01101c903400096800740240701c0c5a60b4122000c2003117041120080085030616442c0c000d6607015003003091440c400078000d403038000e5800c14040d0340e920b803a4903240703020b04051185040403546c000b0030304801e4500703400307042441d801079901d10200c01e13035905030340c1e80c0703a03604a20782092281c1c10814801e58 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 660798866 1250 660797616 660797663
    0xc120a0204020310050907030519200d050915060f01110c090a06080f010e0309010c17070804050a091e0209060c030c0604020f24030618130c050625 65
    0x103903000004e080711052030003051203001080241494100751400080004102a2201034140760011440008154104414042841c03001601582c44698003280500703003402560400c5204081c18003e442c020400400e071380c41001c40a44089600c0f0b509845c1c85401d03544140402e92420b5514011111100c1c581e07404a810301c0003c0d01e07400300b0152548000d000d400403c109020400790780f40c0c000c0014103141d001c1203841340100c84d400c40c1000540441c50082c00010b02000c00345e00b030507110066503841d071403611000301d5000f0302c512030103201d2925001441014074400e500f100e40c0ba219900c007a100002c1d8181e8000c0d80204c4145920600900000448900c100301a200e5000294003e201c641480c1c0100f124000700040000d2050b500001c085801400c201d14031441007501c610044d4482d00c40301e001841d00b40b400c401608050318000c0400800c2071140e40451440c0c0e00481c049000c8030707100c00520083d8866520840d072200d003011600b00034450310509021000b4000c0d910340d50f10320115201c5412 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 660800116 1250 660798866 660798871
    0xc05042c010902011e080f1302060a020304091406010f031509060303030e300306033d05151c050102030f01090b061812070f080d0908010e0c120a02040203 68
    0x14030381e654105080841d40c01c50b140f500c009000060f410484a10760100410400d03000308842003400580012440884078a002001076a9000b0089500c4550b02c01e002035494100cbe129188515041011181e09003441c0d40b550f42c002c101c107a5680702e40c01207802c029005000c141c148a00d0038203c20768005200d03685407003880702445c465900860341c0b405034424540380900e0b8080c0c00841c051070310f44001c2400541341440310113465a202c4191250390f0180000c0c2001c111301141c005600941c413180c044591107400400140c40c65000e40e09000603540c60881c103c801c229802198600341c181040c50324a08408108aa0b0320b030455414040b00d03170b03603803020b007079810a0b03078100c1655502000503c0310586600802500300020346906090071010308003e411110781111341c81c003d11942001c20070445041c480640a4010780c4a410f55407550384014607075680440315541c00245d00f001c8007044041044c080e88035214030500042110040c0c6404200740802844149609841034405810040c0c07901c1c0003071071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 660801366 1250 660800116 660800201
    0x20711060d0c0e0a080304360b1206060f0d0f0f08031803090f040c030906060f06030b01110c0913060c0504051201150317041208071e0c0504 62
    0x41002c000c500140c00480301c85850b074450403010342c0500002e00c0000075101103656018000c03d09442e00c6e2041e10100a0181c1401114440402d0743c5000c2d208a80040086d103805607108c40c51a41107125039504c0e10350070344000340d100c20b19209103c0640380c6804107141d228012030407180c480c0210354400c41a054280011600c80d103020040241070381c501c0041046a444203000b440ca02403112001030041d1043c03200440c0304940d41d1080c518001d100f82d200e030105a41c00700b01000030948542c00024991450701c141d0002134200401142294030400303014800304002d5004000e003001000400c02e071450024196017604507040d0400003c20a01d01940384a00301685403e6034940c00e04040c008154031080d1110456810b1400440301d603c00d00d00350701c0c100c913004140d4007402d43d100d00e90141103102c0c0707620032400070543c000a031080c0a402c038001c00801e07100f1001c044041c460784803410710440016a02400c0c102c00c1c40c0c2e081055003095041401142d40705c54910f520f509035200d420040100c11010403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 660802616 1250 660801366 660801371
    0x9210f150a060509070c080f090d060501030c060c0b130f02030304122f010c03031e050a0e0c1c0305130321140d02070203010605030601060c33020711060d 68
    0x2290041d81c0c842c0038041c04040d1040041e03132a10305009003d22441c41c0c0300034070501000642c04010740c8814266240400001d1000c45a09072a0400801810f807e00080da400d410740c0c4000078946019003116441c0c2a40f001c4282c071590b9035081e0000309207110080944c0c201816440550050b501880184040c1540c241124540403060800e0112000c006900c2a0307503503001a420741030703294072a080f411071803001d1a200040307604501d002c501620340c40c280030184005200d0110141451038100910503040d2090402c920b0302124900d99854160403d1241c01c0070190034000c1e484941c00e0a66a1100d00031300340302d85800100f40d03407450b00910582c000e880541e808049218803480c5500c40040054052401100740c840c0945281454400e007282c0c481400d500141036001c54400390440b0008050050554601e5070b56000013601681710710008850038601b90550040c1802082c80c00070b40c1480b59804400248070220416000354444101a200c0321b1080710345102c690381c2c00c80180310030310121101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 660803866 1250 660802616 660802621
    0x70b0901060501051204060e0a20032802060a031b0905041d0613030c060203010609170f150402190b1903050915180a0c03031409210f15 60
    0x1000d00712189604260704010041040005c003d4090762110b801942003c40000e02002d503c070140d2070001d42c10401030100d5590412050b200014000e900c1d11801c084e4240c501805410041000b07088034940072120031400c41c0111000340c10302e10054034862038941000079070360701c1107212070070502400d03402100011040c2c3c10911071803c1c14050202d00f1440202c0407902603030704990150f250b26006200a0078080402440d10605116228070010203801000441d03030380d45c403808020b2000101340518959012200040c0c20006400955407202015002c0503000c01c540301400d50382c1c4910040d000380d074825109880200b5020b80310282c40002d008548100c0c0d07440e4001c1c12451b041069144012041c10b24000400c02451400310b0207148020a440708078145a850700550044016050403000081c85220051000c00403005d0b61038064a01a803500e80000c203010520011074400c22210b107403c05595804103003aa01c0d01005415402c01c030b6000c0d81d4114640400c214034100c0c81d03190b8903400b034014400f03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 660805116 1250 660803866 660803881
    0x132109050d02090426031f0807181a030303091e190b06040221062b020f0604080102120a05060303040303020d0503133002011802041808070b 62
    0x150800034002a1107850314200c1540000e82c2c01040208040c0001c1040b0801c0301e0313403000b000511031403c010b001105450f820042c0302e045100c0314240c030050b40540010700c0400d08400000e41802141c1c072081c0201000c117903100c50b840151003412000c4420030314004104a81e80c0d0140051407182c11075400504550300b000210400129035050300f10425003002a42608494100300040000c40d000f001c841641d8a6840108000384241c10721a503442054070314040440c58404202d42c0a03030421580b400803a00e00703040c80040d01907204442c03030500c440c000400e001400c1503d01e01840741c20003881c050505640d454840e003a680f09036540c103100c1d55220b040055210f954420203400c003d00b83c0c02181440c1c15513030080e559221680e418070901c00c010000610040c800030903c0300f0640d20600d2901e640c95000001524114400100f40702500100740051078070f44148604038413024881c004030303000d101c0d60b000d000082c03a0202c2400b40b9201244550301c08200c0803001080310034454200007519181015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 660806366 1250 660805116 660805127
    0x5090a03060f0c140904050c0c1501060305250807020709060902070c0b0a0806060c160603050a0b010825030b040e03090118050904060209131d1509070e1321 69
    0x10140107000b0310111104c40492000103403400340000340c5002400c1c0d11550010f1002e40030306035166281c0d115807952104030103d10003400341211f180e40c505101b60b4682c0c106076413000300e4060400e070800c00b0808180001c10320031001160801e070540141d03501d0940b1180c0348010f0350800d401048c901e03038000a5900c1042681051800200000303c80340781019100b5030001c089040103070605110360408030314110000001c1c0008889062032201e40b100c039960390000507020341800c070f50114606143c2050302c0055400b840b03840d80304d40840c20b25880e41e0303455481203000284008501c0401c0540e1342b02c0c0c0d462151601c0c4194150f0307904c124020b60b141c1c000040010283d000c0c01c4041201e1841c50481004107031503c00200760400d41c07118015031a442d219000c01e0001d184400007010950511421841c00303140a9070681c40280c0c01c106030381c901046860717110344010701a150a042640b09040c01c00600202080716030f000000c400742da03841c401c40d68442c4001304800e200c2c1c0348080301000a80c1050240c000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 660807616 1250 660806366 660806381
    0x3090f0c080d021e0d180b03040f0b062403070c0c0b03060907020d0816120c081b040503250b030a0203190c020319090b0c0f06010e090601030f0305090a03060f 70
    0x15402c01c180903007200c240540f079001c01079002d401e000c2038220000c44458a0441034000d0060681f250b612480e09003020404640400030550300c2e0512140032078802d08144004d10b0141c0d81000ca84262407144003c454100da000420660070401d8003154038000503850300b41e41c001404e50300003044d124103007041001103041010301204103550101c03c403481419003010b0341c2a03000150000025401042d441c040d070325032880248041c038035403a0400042034160032003245401182d00500105800c2c07005822054144a04d000e02c5905911041c501c94007009080c200c032102d60f0301d6068002d446903a4896a4005800549540c0060f6402004010311004200007101c112500030030309220200ca0044043c2d200c0c0724540117000f403078aa40b071214690074094100c03640103200e0802a2565115440b0f280c5407600f034122484225401100700015241d011070304942e0240d070030b803000340856900c2c65455081d001c0d50104110706000c0207020001c0c5d140d44044100008501401011941c00140c0d154081141c020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 660808866 1250 660807616 660807643
    0x619090533040815131203050703140601020a0b1302060a05032217030703060806150a0807030c0b030a1b0903050c0306010f06050c0a06090302210f0a03090f0c080d02 73
    0x2c0c4820000c024001540303407500f070020705014080d40c459400301c802c4245a804082d0030f800c490b0360130000040e45603002502c00e0159603000c100c0004d5081c0c0c83c903094282580d40038016489020042c000c600714a107400e401540034000c04e0820aa541d02081e902d40210790480c010940100800043c100000c2c11070711408071410207034240c4c0c00c1a0303960b140c9100400401580a240100c00604164029802140501030340400c90b40103240c180d0764101e8820017000298041d1145a000141940740011240203803a0b1100d12101c03143d007081002940e9820043c0003861194881a82842d002440c009440103030103c1c0d52134110b090306508109103002d520450715030280e07020000400c8410a40007060054914a05e0040d40c6d68140d8007000b40f9008800b40060000f40c641440c540070035800240300410011903440618080aa00c0d058444901441c075400e03080301b2042044459042c8640e10180703250b880750840c00d028440c640c4410242e0f00564200300c895a2000c1c0d506e080d03150b010454805210348 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 660810116 1250 660808866 660808969
    0x90a0b0915040b210d0908030d0903090e01180e0a0f020f01022b0f0503011401230d0905070b07020105070209130218010e0604020906190905 62
    0x804603200d50001807a52101018003200c054140d52aa041940d101c1001032101070007180c11a00c180030115a04100303680c0d4815519001d6a81d40508044030484515001441c20a171020b40c400000d00040f1804404020707075081e0105110b414210100d0103000c4050081c40d519160080e89012100510340f881c407154090003484000400400b4503054466043d20303150417150b440700050386408510b00000907680700000703c42101d2020b01003004d81074519941ca5007a4101a03c0b000e5403244020b0080b41c030780c071194201034085540a074000400d00b0300140c80160001d00d00450780c28250700f0449225000c20703290318245050140801c041005044000c420701d140082540c000b800502c00e04000a0207046c004c00080c003e420003035141d40401da00601000690196520120008a406d000e03000d03543d83c054003c2001130415100ba0340c2c0b00d801c040c207400e14007096400200260000341c0f40d41010000003d1001c1110386500203081c40010628180b034035003800da01c01c6401c001d0180a0391400d203c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 660811366 1250 660810116 660810131
    0x12030201230106170c03072d020c0906010306031e050c040c11010533180403110f060606030127020c030705010f0b0a0303260f010503100c080712060306060305060402090a 75
    0x55100300c0742c020b006810008502c030160104c41041387e1094000200104801601c0205250041102cad0080130b811600c4400c9560f6034001982101d40f00c0c08040c22003031040400f121030850160700c1d6905580160122018800c80800090559201e51010b50000d11442022b5940042c240540380c1c101c002a544c0074406528103084c20b8059405504104a420010030403094644031800c0303881d40030340c0340915144545080d04026000d0010b1140203e254424140203001c224000709409004080040096180da460041c4a0b420080c0b00501034a041202034507030005098684010861511a88007031900c034603003401d29508460848405170b40302402c6c000c40c610641d0341c01004109907075060822541881040e481403031480360071403d600201c0c540c14103101020036a6848581200c0c01117044404400600c1d82001c2500c03148441032000c07803500310206103d60700a014800012040d20710002c0d41c075039079490b490143c42c020f80c426a1141c00c00001d1206500b400100e6907800f540070340c410321000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 660812616 1250 660811366 660811381
    0x6030c0212030a11120a1b02030301060206040f02030f070303110d030509030d0c050d020301180b061305121501170f030c0703030e01110a2010091203020123010617 72
    0x140b10040080300c1041da03404520121046840941c3d034640f0951120b00d00d646441e680060041c00800d5a103900e4115030075034601d078140f000045034142c403516070141649444540e640c140003000c524040745c0c103014103000e402c03c100041044400950086e5181d84504840d80c12250502100b03032410300030941004100400d10a000080311110301f1600d0000034a0800c0c030320100d4060142c60082e81850b4000400000d040014400c49040c0e00b00e140004c0000344039640400401d44611491039040030b0924808210314500100050110082001031362140f8209480f1214000c800b40c0140c2462100301805518207042002010038400c00340c0e006503d0402010513082d5902c40510005080050001c0600f040f40d12804c81c100300071041c2030445440340d5803407800300b6410301b0101c2c0318203904044041c0107050b46411904030540d08555168008014248515060b00c45813160703080e0107564848400903581c034a050482001c01040d09111819541031440c010000b1058090003c0100110801e0240740c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 660813866 1250 660812616 660812653
    0x9080c06030c03150a0612050106090e040605040201031d0a1b050a0905090709090311010c09120b04081201081e030f16030c050d0f083108090301110406030c02 70
    0x110300d0300c140355144c0d5522000c1280040919034000d4004610135070014030300d6040081464104021001030089a03200d18080310a051180f04503a0103440c001c003c07601050181e802241c0060040c900420058035050700c3e00500c004025442d90164428240b0105102c0301d06414000302001125404140780350500080800300300380551200913541c0c50103c1c40d844000c000b0800100384041080c409181a400c0103041000c0c003042d0445d040d403c01544422a5206060034015a06101c0c825072001000d51194000040001c0003142e100714100041010aa05250164020a40b400c014085030110600070585600030381c2c2d25146950082c060007074281c0038103050358040030b80000094000c00850408442d0500f600c50301510500901c0c101005240d400440d1021030030154603600a25180d2214282e0b0000c07c030601c640c141035800d0307507a0241c000203c1c82000f40f2400f03005224209020400040d00312642401c0c5081c00c01030000b02004455018001d0459078440e500107040c5403504907168200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 660815116 1250 660813866 660813871
    0x90312041209050d080a0206060a0f09020f070b011514120f040f0210030209011b110f0a08010c02070512010b010804030509041509270510021803010e0d09080c0603 72
    0x15590301240241d0312a01c81c0010600900d0000e1080507410f940e800c01107042d610003a4410014052200051910300300392850108070b0f8801c2c03a020218071702c1d140b1200003d41014170031007140d0380200107080120300c0800d2524040c01d9481c00d80041081c21766005820110b4103e0100480311062200003112180c40c80d46592010098140700380d10754585c5822110b40017104c400070740c01507001c00c28500c540d0303240e07001c0c0044000a1301d41c2030880b4410601d500980c40c48000003403025070350011403c5170303061201040c1900c10020308284440ca46840d40701e400e48081507140300050703011071802c201900d0f00035030081910040d6002000650140b200007000d04900034805001c1c440e0000c0c0078410780e2109d510143c4805901480301d0461500c0e26046400f0b011840d8491144960900050402c1d034016030402170303025030100013400c10004030315850b001b9410079910f0303602c00c60100c1d91150312614280544800800980080c0070402200384e40501074000390340007003100350b01c62880c200454032480d007102e8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 660816366 1250 660815116 660815123
    0x115080f0709030203032206140f16150b010e0913060c0e12010501150503090304150c021f030e0708030703080402030f240c0306090406020a02010e16030b09031204 72
    0x25181d80c40400c1070700c1590540e0300c025011711000420000680103860110129900005462005940d03078908541111110b040d145207001d003080102400c000358002440940b4102c0b070700f4a480e50480d01e40800c680340081c40b00441e2a11002d000c045513a2180082c40500c00440325402a030070060140c00221a10f41c0004142e15554541c02407854051600746a146800a101607101c03c1ca40034882d019010031300c103503c5015625203c04d814540910140e81c401c4100c00015170429140c0361240c0d4295040c140c11a00344828433a1000150316100d0003115091078000340340b40d000c2c1d110131000742150b04001c1441915000300d18284044238000c02180d40c12a00341c43e00c90340c1900e490000900f40a220f44a604507882002e0000300300d101301e920042842410f0001c590309654990203c10568402103500c2c943c0070701e9000003d030029600398041c00452195100000710260000d080c1858411403200201c00401005010000c00080c1c8142c036038404440c5020314180a441442e11910050180008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 660817616 1250 660816366 660816391
    0x1a120109021602190b0309070f0b0a0c0308100905010b1902010c080a2310030215190c030309050615030c010212090616061406091806061e04061d011508 67
    0x50000844113003031075001e0700c004001c403580c0f07040022140d0307540d0400c1c0c860440581c18080001560441d2102603032800b040684030451290b0040c0c0e0111016007006080301c0c0c82480e50303900890300a0741c500c42e0502030004006890359880ba06100001d110a403494180300b160b040950103204154008507441d002600c0c01c0c1c0101d25043c4c14003101104100e207104985410340d424081000800c40b004084045070f0007a540121301d1205d00210700e046104e60328141d1050303200100c50100c280d2050001c4509030f40a4030740045d4401c015500d80e41444030564141c0b8104010b00101c0940c0c0c64144102c000c0c010f0240010041810001c89042240c0203804405120b1305003c2002c0c0c10103541c41c802402c070190b0100041000489400c01c070fa03076040040d0ba585010700003041c005140404903100764408c2c2c10403070004010581c0c4100c07c22400944c0498400800003500038200d0190704e4038020340014110034140a03441c0784504410041a080c16800351207023590305039003502001d070020311603a005103851390207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 660818866 1250 660817616 660817639
    0x1e0b0603060d0b0c0708071b0f0b03010b070f02060c0c01090801060e0628080d0e090402030c0d020a1508010305010c050906030109020f040b1605100e0d181a120109021602 75
    0x250204c0740940c00f80030b8001708000403c14100400082c240300884100010a180c440d1a20308203400c0b100035014147e42600100f006100e6500703000090b05013584240c4220800b0520345d80801c849404c03400c9210110361105540030b0f41903030082d82034030107440040d000704030140c5030407419030f440f0b0300251150b402450303640860b001c2e945410703040009146c0190140140503a5610203103548800007100744001a44000c11407119181a405040c081c640080040c039a0041d8013081014480b080c0307000f01d0f0f1007035004000041040c64a081d1071303110b05807500c1c0c00d00f00d50f04d98113005094894990b105010820100252400c9994440550f8152840b410005880b500501c404a8180c821904601001c2c0e9003c566090055001c1010746d066500c1802a0398080c80180c00c80c50660700980c40a2441d0b401528084542910464092880006900c094228560307506951a0780b09180c1c0151030b03520b20002107000800b5a000b82c00c03070040c01d01503011464040f00b00c50118860300c41c00d40083c0719883c2c0541 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 660820116 1250 660818866 660818881
    0xa1406030c04150f0602060a0c050a0503070810180c0206090703050d0804030302070b01090603050c0109050901092007060525090506030c0c06102306040e040302101e0b0603060d0b 79
    0x40c4980513180008000c5911a01c481c806560307000d00700c4640c40e81b00c0c2440c240001c02e5200d241074600c602c8460b02c0d6a0b0550316410340030b1f903c0440c001d100c002c4110452200259070b00c0780808441c82e1800c0d88200145031507045200a041103030060140c4041d5012010400020340300003046100404540340000e81d5898034541240a44174425002e07040703000010001c00c04009542c007560460b88581c04413000a241d440c0190b900303201510070194014204001000b122080f50040c4a0785035a075441315580060405130420b040c0c2220100781c98007940c070320401c1024603450700c4811400565500404100e02c554a005200840c507000e007034001c035004004604205a074900b543c49000881058502510303003440e010749008041d1040f601412403091005802d402e0300700c008411100080d003441e281600780244509054405441101184920078108070100c24500c5a0041094550500d2a60a0b03081014a09035107810605521034201007041c000f041e41c50040c03061700c042d8081c02d0b00c0c03500d55600390b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 660821366 1250 660820116 660820151
    0xc0302040810052205162403050907151107030b010518090619090f150f060503330a0905010c030501060e0103090309151106070504081902270a1406030c04 68
    0x10801c0654000b4400412401c880b082c2c2c409111a55801f40c4079030000050046003078031802d544048168100000a05c111369011020300e00c600c003181084d40703000b0441d00032186000d6603036205841c600f507500c005001600d4150b01030105905000840c00c04c5090403065a0f0300c48401030100340541002c2000d501c01e1006a0700481d6800e41c00055065125a0504050740e00c00352122a2a040c240380c800c2054840c6071510801e010b894010b402840c41400030182c0c803007850102c2050072a80540c040d0040c0140c44401100392181c4082000410001081d2602d0760945034940008418541041c00500c0101e078001032600301008240380c007056650301030a060310300c0c0b00280c01158508030b5100c0d140c44050b4101071002020a040c03000c1f83c90036502d141044580b800349000d070044c0798025000520041c00d54444c1494001c0c0014504482c0000c07610b120b981e0062818810b0705240d029104000207900e880c4030b10884145083ca000c4400d1600c200000d8a4032820032006100e20782e03410901c2400b4507000f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 660822616 1250 660821366 660821383
    0x1314010e0405040506042f120102220f09110306130b03030c01090327031b0504150806060a060504090e01021c0b0306090304061403070c060c0302040810052205 70
    0x40c00400030743c14035062a40d183d0710100c4d000e5584609040c04540f40c0024207500f149104000d4484030b11001c4040c04200540d28064051181d030f64080c07004001e10120203146420281d459400070150714600520001107144036848010341da49014040c1c02142201c1d012294000780488041c076505803003003050001000c0303500003140c040c800444e8130301c80d8400540c02076111601a0b00d40c1103c090b00050044607802e1080296100c0c031810242c01c10000d42c1005410b03440c0301a0780b12240c1000c2e00c0d00041004c40c1d2003a40c141ca91418440c8040146620038011241c0001d020b41d580e6201c50700b1702c200130700507205600c60080865070b00c03117007a02004403c2d41a101e0807229980001404501201c0c510050040328681900c00d0081002165080000000711802c82d2526110b40300145003524221341c0d10781009000d101448154500703c4001010341c400c3d0064415180c03401612182468003c07464650a407424400451809040c4644420500d441040d0104010703d44409a08149070035070401c602c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 660823866 1250 660822616 660822619
    0x90307050a0b01061706030703141e100c0219110a030f060209030105060603011211010314040f0606080706120c0c02120d02101a010c02030f03070804090f021314010e 73
    0x1c044254080200403040300d07048402d80d56a0142d0610001c03480c4a1002081d0344596042d030010b081000010040c403d50030a0100d42c1b810f1302c07810102007140d2108030501c503207043c0b4290001e480a078002d110783c2c0701d01d25441c8401d00c01099400359004e4620421482594060810310042d5141c05c007a40d00d44c10041d003d1940649080390704889441d00c04c01a400160400e40300313509020001d02c040c103168080c1d0f070490b502d54840c803400d05034585541040e0741c4040d224604042c0c452990003000c800ca00b504070700852141c8408038070034005040c82d5040300c00d5500040d601d5040f107041000390079842501105a10151341780000e03040c0d48440240c030143c0c501c2c1402908902403e80c1c01503015404990312491691035021b5070000c40e449580c11049501e410310350380300c0540103a41102c1070351082c1907600710184080c00b20f8948c0c0218401241c86c0d80c000120031110f000002030305000c45401e034050b1003000c0e98035010540c10041c40c66112001c1078601c1c001c089006440c011550096841007602605c181c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 660825116 1250 660823866 660823873
    0x903130602030304110d0c0308070c0f060c0c061103040314071a1b0613140703020603160e0a081c03060f03030509031e031c090501060f05010f03060e060909030705 72
    0x6866030081e480e90803c0b1420b032800b4241c520030621034280000480506a44952050300590456844c40115080780d04162212a500c1c034021502c07045480c84180a401d150711001c000e41c2042c030341200518184d412400c200034000e05801080b88001081e281580da00021103c0034018821840c0d14100300c0398410303500b0698041c201141c0c20b6141c1d0040140d20040c0391460041c41070115103540ea41d01c1600e80c8402140216403a1011503501d8080c01d1180b032071003013503c110360340e44c0c0c00003000c40d0021b5801d240070b48400000858116084541c440d11654242c40007480d080c54420520b85072186c1704e1a0400c440d4009045140c260301c00c3d40b100001d468162050000b5603200d040040454102c0740c4050700a11a4069a030740c41071210296000d072440090045140440c0c03011100709091000c13240380601612034080c200000c10a0040c0c0300908803801d4410000362070580010031038003070301030300f44141881e080c03040c03214241d4080150f52250f81a0b6408015844001c10709144d84985a8082c00390300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 660826366 1250 660825116 660825119
    0xa050c010b0a0605031b0310060c0303141005040608071a070311030d020703032409020f040515070506130804050108060a0305060f01060f050406020c1c12021c1115090313 75
    0xa030000c4c05540944010030740900c040245021554451000b5100310008280c0d10008008e52442040f568101030700c00e18020410014000b0050860081510007242190800b00103104908151180c0002000b0f550001d00d0406d180c0406581c0008a1010840f01c0403400540c070400d260040c00f04960f00c009100489964400032003020009400041040b0000707800c1c50f50711030000c902c21403045074071079407070201c80d800900c1d2030442002940005404040301406000020300350342d45440c040e42d80050b801e2420741c0c0302010703d021410200000c005500702c20041c0c140c08081134010b02a2002c0d00c40a090078162520b400000a01c907200a501c020001e2040f5000c00000e0924402281c3c102e400648401004400601c801d4501e03005d20300406006910464610b281c500d854074129010041240030000b10140544030403150868030b100403800750344400054200d125120402070710b041c072a0f00d0f0045810002d80d034510f45545072500103502d030304400380c0416036407582801115507407031202c9011141c15 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 660827616 1250 660826366 660826379
    0xa110f0408030702011707020d2a0501140a0903120b060f0a020d0e09060117060f032e05040f0305030a0b04050703061403030c1c09120309090b040905030a050c010b0a 73
    0xd83c440442280062a0302000d41050129031050318000c0c4c90036005800301004c40d081c11104c10944901c0111103208011842e002540c4510344200c1ea68024070001c20841c10208a072000034002905840485181050b0100401d5000360f03964100800d06030049401d941100c0080c840d40900b51003030030301c10b100003101c080c01c03a00000d00f09040b981e6511a000c040310400c04110020380b044801a02288000a007041484100d0342402d5004000820b417201520fa01c00100c2d2800c140f03091081c4503813940c42901b42241c0c02840b201e8540c5454443e0034411850143d40710100007042000c0113050007400f0000c0760360031085070864442900d0181040006140c0600020081c0809205611140c0e0740c60511810030709000c030803213071002a0b0740014560714030102032030008208030415101c1004013003000898a40300031454000018003e9882c21101c504100d980c00455010400c11b51065150030070320400142c0100c01e4030900c00c2181002070300d5401d001402805000301d0b83c80184d00c00450740c40031070807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 660828866 1250 660827616 660827623
    0x603010b030f0912030a020d0e06010b220302010519030209040e0c04061a0a11070f0b03010e07050a0207060e010905041d010c020607170a021b0a05010c0212030a110f0408 75
    0xa1100404620b4058441403091a110300d004c1c00c40005090040001507011401c41d0002e00401410300f400041000d0b000c000507051500030703003141ca02501c00151284402101c00f0f10301e8000800940002c10303607451a40080d1840c852a03a48045007945015955020750080c2e05442d4000c00190060000c140c01c0d1000b982c5985010007824480c51074400301141c03402aa114800112841c145414a0b010312460140e88004500303500079598841c4250104030151481c0c0c2c480f008005840b1442d449504200c1c0700c91010800504140820106104443c489a0700180410032140b40f070404030381c00c43c0e281d001203801c0451504015003103400e08820015001d0070030800e60400c64104020010712582d500220b0300c5d01d00940b00c80c0c00003103400030304403105c0e141c400c603254202a44c8180145800c543c0c58461000480c3e83e5003100d020b401540224003031181c28007841c800891a440070f0525041c0140d01700b5114040905110411030307540301ca2940740322690040301d014800058001782c03a2540c5944d010303078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 660830116 1250 660828866 660828871
    0xa0e13171b0d030e010b09060402070606050607080301050411091e1908060a1a0a0902090415031b09110a080411030109080a1106070905040b1906020703170f09060c010b0603010b03 79
    0x1d203080c208504c0c0e2407062080b01c011041c0204140000e40701c80d010130000e5044044151101c5940328000551659000001c1140c2841022104d4076585401c3c01c20086840c8801c40c000d040ca802c21454440b540c88181501100800790750b030040c01c0d182d0501156602d502100740302c1911200c0381000c00c0c0d190001468030310074030001009110140c44540084800b0550214207034010040c1402440100c3c03480e0090300d940304000d0800640402d25038158034610400340d1003501c5a5103800c500800c4000416050b201400035408144404024449540164800d02299004112110002c00c042000c0040d200d0a0807000078000d02112505040001a540c407411910b0049214030079640700366100170441c940f1a08d41611003e00702880c1000303000107007004032420b42d400090200307481c5251001c20303c04806000c141d030080562a05504d80290703003044011074070360103000034450500445150012201040c0c1b06540e41511a418590414050003942481030390028000c400807441c03a054a01551 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 660831366 1250 660830116 660830143
    0xf04081002180d051216020102010f360516062705040b0613090507110127150f0c0e041406120c090405010b0a0e13171b 53
    0xc010300601030400d0224440e04102c01150054600d110b1080e00d030801e0070701070b0607003d1001c3ea260201498240c3c84160300c0b04800c00740300b00c11501c8036000d41d43d0900ca265155101068100318010b001c8041c005c446803135524154550100c8080c00050344a500d05810045500c10304840380e0801c100d490345446401c5029140008843c2c112086d5800c05c3c120480380c501070804c01c481030440c188018440036044092130150000e40800c0111541006009c40c207001b081c1d480d4000031141031840c40144455120354040e20319038148840c81c0d0901810780110046044620307580050350603580380040045040d20b4180d10b9103403405458103000c1c502900114031100c06680c0c0c20100040e8402000700321803000e40c80740c0b2150900000520740341004d544440039401920300701c41c0c044902400085c8048800c40d01207489945030201d00b88681886d0b604139014145800d048035043c0391922030f000182c50780803c090481281c5040c03070105600b004003146c44001801480701620034071400b00035910341e0800c0b0840e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 660832616 1250 660831366 660831373
    0x6020a02030c061e06010224060616050708060717010510020a0f0b040c0f06020c040c030b03010204181802060a0e0d0b010303020303100b0301060c1b0f060c0c3006110f0408 76
    0x1c0d103541c030110b54a008c6031140c0510382a031045c034020a040c0c0c40d000810051b0048810892100394a00503007400e030109208200030b00e144c03402d0956850900501a08900c203010362955005641e800051400d41035500680d001ea42a1043c0c0b0300c00ca00c0d0201c640ca01418a64001035100240011000e0481c8124041d588103010591340b000140714024951003610010381002c0079005882c5000e401003940a9801c0c070b8040380700b01404c0d0000342264400d51090070281da250480340600302140c020540a90340c0c80041100a14403500415614443ca4201c1020000560052a03542d640d080c0e4000396a41c01c0381c2e1300002c40da128a8080d40d82c1e072060340c001e84403201c5143d00040110051084134141c90b05a0b07a0201030700d12a60341c0c01c14002440145600c510054800840c0d1654042c800b00000d10300360383c800005120b2070509800b060b10541209060301c0c4800303c40400194104600c0c0c003417200da15003000504840e030909000800c08641ca10504160004a8014030814207002c2c0c0190340c402804e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 660833866 1250 660832616 660832621
    0x2040b16060b06122d01080d080604021e1605070b0705060a0e07060507020a081002040501090b07201f050901122307020f0d030f0b01080f0406020a02030c061e 70
    0x412039a80529000349404e8036080340000c101e582206003035140c00c180c4269403119003034449210310983d02d0980110f0010303403002c03207000e07552680180c07010f80040064508500d0310703240d82d171902c0e4010952252861040070005010700c41c4c5400412600900d6042002d40389000d480e007240d41031035031141100707907114429100031802c001c1440c072803030b42100d44181c02403402d503103003100035140340c1c1200c0c0c8142da1245910a001500f00020b01502900000e42c0400503903c500709800585040b10700d4002100d03010301070000b00e00213442c130741c4009503000a540b142c8240c00e01034000904280b042c110325010002e040707811a4042908000904078070308098903076040d1070100c08003400440e40701e0608108282031141503085007810010700581c2001c418410781d000c0038a51162203203030080c0d040307620380001e640c0c10803194890700c58030616892020900e0300c0d450b903042c0329400a04e50341c4044c0002e0483c0e0f50001e6038103c043e00030000c6504141c0381209455451910b00700702614100d8504102c03410700d001100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 660835116 1250 660833866 660833869
    0x30901090b090f0f01030b060403050f0d020d020d03020d0b0415090e030c0303041709121f11030414010b04110301030c060807020a1e1a09010f0621050102040b16060b 73
    0x54032060b002c080c00d210610303c04281080621011503141c681803680c4e8510038070654807120001d01c00f95000310001d040b00d402400701185030891850b2074000f10b410103030034003004580c00308402105ea4454940580c0321044001c404000b001d00c801455409450001c0e0309074060084c0d1071900483c1c005482c10414410345070301a07602c80c480c1d0107200d05180c1040001070300040c192000d03101c1c451000d808040c01c05800341c02003807180401050300711565200c1c103480b690220741e8960f410074144143c2030501c0650440c10101e003050101400060500040100d600e8030031000358850050a08020302c184400440070075403074166803080c0019191000b40030008942d0354042c030303015401540c0039401049600c8158540c007101e0300d07400c103400402c0c0144543d8503007c113142130799010900f040c1c0c94007200b05040000d150350840d80480e18035410641000d400f0440d040760f07100c1d80142204811070f1111501440d10b086c034020b2140341c108160029020615851500301c540d10300b02d606104000401c2140749210 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 660836366 1250 660835116 660835139
    0x12190e060f0702011809051305160f0b09150313050c10050a1206080a0605070206070f02070b0d0e060903070c092c0a06091b06050408030403112103090109 68
    0x7581d004050004001c0d01006510508030031030740c1410645010145a03c3c2c0c010f07034094402c00d41e030203001c1c10710b2035003a9001d000c010304c42c0c5003002c0300109401d180d0901d8440210307071120044c41030201c141408aa18070080e1280642100c0200c0ca500005980b4034240c10303c0c1c0f1385043d000c02d00303503183d01c1060f0040c400390408000c04a4040c0d032a841e00c03030a11000110803201e000c00f4251003003500ea15070500047d0b15138100848848148260700c00f04461030302d108005d1134540300600c2c5c80100240e2801520001c7c0e0045111419a403840040329030f6529048034400151100c001c41e4034003403040c5000c0207288940071020f0494140701d40e5003250016541e0425074256403500c2d4081c403082082031291552106006030b4010100e00705010b9455006464070352800310342c0903603001d4581482e5040a4000c04241340050380141030542055801d16043c0f154503980c80c0141d02000380032500a1130200c0450350382c1d803000440380d00007421100b400c0072102403072a1680c00600409000c1071f600329000c078400000a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 660837616 1250 660836366 660836377
    0xc0807090815060d080d020703020a020f04200904060f0f030209072118020301020a03060509070914090912031311091504094706100e0312190e06 64
    0xe036460855600c40b141080032948140c1005c807901d00c82045840c40500c1140081d0161030701036009004012454014002c150780c203041c0d1039104a2400031b140c130311880b40030a0a0147c0c1c0100c0d001c00c2d214801c00c0c0c085402000d464001c1084410340d040c0015102e0791107074180c001d8900c2901d09230140d460b1032a003903800065030703694820b9411746503c1c00c003804c02d1140e01c04034196030b08580f2240b0b0101e0a401080c00c992200d41140000f030384500d424802e40c1030600b000f682006051404400c4a45000c1250401d500e2195806204040e200c020440880b0308200d885050307003600034007130381e0307420580702d007864004d519102151442d041400048091800115036032045184170564600010b40d2000c000c01001c1005044607d030310301c0d04c0d0a0540e20002711030800c1502e032071840742d481044e04000c42c0900800d4050f4421042d03030349104024064507103280003402c000081c10041c0d0320745c0d10ba000180c1450182550070000d4040814500c80c00c80c81c8000d004000311040d00e40a00100c000c0c4244649440340 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 660838866 1250 660837616 660837643
    0xa0f11031803030402011403090a060c0c0507140d17040302061603020f0114070c170a11010605040b060f030a02070203010513140705010203030c0d1d06040302070603020705072102040c08070908 85
    0x7c000c10800b060203240001c6500c08007040a90703000080700d0355440222440700c645100014207008100d0100101000f421000e0500c12164034003030700300340000404a2076880b10080807500c0444101c0311800002041c0c4000d158020980307503c2e0b400901e01000e880c20030081c2070340188204002c070101070b075061144081c01e0028003003245060382c901d03c0c245c4035601d00c0c1c1001c450b4211b20b1480320001a04c1d03600503292a0240e0b0303640c0140d00c07400c0d22809003920160b400151290740b400700c119046945a000b00e90b840f41644404903281d030b131480e030900000e0040c10340294055080c41704101d42e0624007220200e1907442072880d245188100c140003075a0b84090301072a40941d000b000403c1d1202c008902801800c41d800e007000c0780c0c1c1442c0c802e5420b52848440070094855104105000425030140020b03c00340a80e4a02141032030040d894080c0d40d0501e620803000e0b1544100d090176030301c070103d02c14201050f4000e04107000c1d21000140003000800200e23080c100140302100701180c500c10105403c86280780 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 660840116 1250 660838866 660838877
    0x303050405041d07080f011113052e091505090f011b0f120306061b03080717130b0a09020d140327091503030d050a0f1103180303040201 60
    0x4000c2404010618030003114441105a5405446041c0402c04032000d001420701402d4080c0386c2070000390035503010100d441b044803020f1000510495071507003002c04071501143c0750058800310002071191204910801d60222800491703482c20030340c004407440c0864400703030411a900c8404040840f203c0c001d07590380b2640880c403070761045210341c4200881c6403044001c5c3c61400306601380d80d0303900121340c951000890310320002140f80581d0682601c2003c00402c00c034104a110082441550905c06512400044c01d200c05580407401c802d04c00d41200c900c1d40509652190310b07042c0403044005010900c14211801c42000b000100d220440e4012801d0807a4094000c521205996641040b8a144030000c0e0301544000c0c007148014500c0c018518030751144030540100d140225000340401e8560040c95a0034990800058604030b450000860300c0e01d402c00380e00060652a4020b0060140840b40c0c00c00724120300b000b081008101052004601820324a04160030140100100a84a0004030f401901040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 660841366 1250 660840116 660840119
    0x1060f03050a020c190b06010207030206030406091b030615080106060530040b04050c030303040b0f0a1b0e01080105120c121903030b0306130c05010e0402090303030403020a170403030504 82
    0xa0107900500d420040c91240541801ea070700c035080d8600a40c14481c01343c071901d14140d540900084071500c1d07400913130038805484910b00719000304a003403101400090215641d19104424001104820f8040d40d003040c40c420542540c0381400c0c0040c1c1414800203640d0182d42000007056041440f0b820110380b03507a00c401d03041003072500d100810340c90104015500d1308503410f0300695050034508030320300c241d100d500caa812500703040c1012031604c035031034042601980c42041400003142c0d10003000d075488514003640310542d981c1c0b80c1c0c020303018082142649501c01e1000c004080c09680295040d080d030b000a036a0514540c0e41d80d0204101614803100c64607040d00300e001c0010240c208130400140700c04891044420054214202910b0401d2061003900040e981e05070b40d00d124034040c0000e42c0c103c420f10040c6581c10140e91141100b108103442140c5c180a1420403014081d111074050b20b40410303008090b01e44a291134180a9211011640f049130218618070080c13006034003000036a000d583d01540d459007401d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 660842616 1250 660841366 660841397
    0xf0515011a07020d0204150806151e031603030525170702211c03020703020d1112030103080d0501060906050f0a09051e0f010207030308160504080709090c06080106 72
    0x5500842c003d0b40c12910007030000001d600c5900411110360840300321000340c1c6103846032103414410080c1814907504801c0f02681060390300c95102c10740b200080350540080e41d4098000030b00c0c1036036444280f40281c540310000400c2c581c2103005060402c0c1482080588070f000c2caa01e18104082c00d141c01003640341c107808220700c02d50006000d441650b00c050283c40d40c100f155400a01c0040080d120442140d00002c0c0410000240281194100d00c00b410158104070265602039120701d1501ea94008200c05c486404100443c2040b003844120303080342c1640c3d5256120705100401e94070035003410045500704000010303110320a008400484a480d9102400e000c0010f4406255078010042c2c07a04212090130003094a03900ca0100241907048078055214082c10f2900f4040301c0c1400201240c15034001800400100c0c0c2c0119a159000100000010040400060035204ca00494104207241d210301d004c045025001980b210440354001d00c080380c5116910401280c80f00001d010750000144031400c0320902 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 660843866 1250 660842616 660842669
    0x1b02060a05091516020c09150f0a0b0a0201090203010b090108060c3a0506150405010c080706021605061f144c0c03200a0f051501 57
    0xc02c803682030f1080300118140c501c03081a004e071240b02000220780c2c50f11144980410030107840c00e45c20f4a00d82c1951900e0304104c00d00f80c01114029018512103000c144499803018100b07805005404502912143c5486000740201441c000c01c901940c41c080d001d41480c034150305528102d0f20000d0007400990354007001490660010640140c10070030b4002502c2140c1c5810309460003514000e261b907845003010f150a4803d0307440180ca0140070f8058110320f213040c1c001c0702e01102d041d11000c1c240280c0c08034062501c5d410a02c50f140001c4c01a610105a800060441c0c1ea0f4100350107014030211990368943d5103949030546240f8584c124840e10802040120226280452414074401800740c6c29130009510410240c003000c030030219115201000700b10740540403100c440d00c1c654003011309503a4440c1540003d494041403900c017505020044940541150071a8000103402c0d40d44001c4c1c480d0a151442c02c41a10102c0c0441111640541703503490400ca501456418100c0c0c402501c403800d4840900c078403004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 660845116 1250 660843866 660843871
    0x2a0605100e18032d0a050315010801060e0d031709070501020d0806060307080720010b33070c031b14010c0c1e090204180c09080a031409040509060601031b02060a05 72
    0x150000780d10261107040c0031110240115440391340303c541e0760340303231800360711460040d076244d10f6042c802c07050f0041c80002e038000c40d00c000c0e0301c806840010034243c0c1420b040d20a803040d41800d1040520482c20400394401c0810483e08803407083c0c080340c3d90310b02032090586903200d04458140d0844002d01c0001c0016220b00782c40358110700141040f88500ca0042d051155107003943c5424442a0b4440d51030701418100310340302c0054514100d0721100d04410070021400114032110404183d00d001180d25418032409840c46001950322000010b0032100b40000f2042c0d02b5018860b080c0d104c0028903842490354002e00c00c2c4032203aa800b0703051a5580e410800300880c80c1ca440d01d50303400d461000302008580d01e2046d10041c03024005e052500c02004941c01809015a120b1802c25000c001d81800300700602007000510805041d4503003042085802012061300d907600071a504140e0041c107060510000d20801b0a9181c00f91400307980c00e1040409450408564808a210410050b40700500154110304294841c40c1c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 660846366 1250 660845116 660845167
    0x3020601270c090503030d0b03120a05030a0f020c07090509010c080c07022209061505060a170a0b09010b030a060902040501050d15050409031115072a0605100e1803 72
    0x107010710740b180003191540d040075040d041f1080d55183c410342c0c82c1c5401c00c80e4404044400c10564941408ad01c4020001e00020381205641a250f0103d0802402c0e0f80d011b8030ba04001110441d1545070391891040041e00d825281c01384103500e0b00c1411450b8610070b400c8988111065440686010816030034800d400c6412840c4a02074401070107942d881000500a0400c1075001d510041035420f8052245500d02c4626407110344274444c2004000c00086c1c00052080c1c0070301074400400400c4d5103680041000d41b40402d01d0b25400101e00d8000300725105c990001d18000c001a40c0100b200d16180c0007440101c2c8981d02403207021a1042c030082d0384400c600d0f00664a445000017a003c0001c4d50b0700d0105007076030401001140410002075041096030010485004020306120b0b001c00242060840500540d442200c0c0d90031076944170508a0551410010054489a200c0c2e0100098a0440d0000340341c0382d00c90103209418442d040115003c040000000040c0d4110a00038514040580e00f009400d85030509011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 660847616 1250 660846366 660846377
    0x31321020607020d170309010c090b16020d030e0303030c0307180605030a020f04080703050a0506070219140313080d030c09030c0506070203160e0a0501080a05120c1906060303020601270c 82
    0xf45c081c14400d4000c2c5000365001e41c00454041140d401c00380000080e43c02c26070110200b8403c80110031a8460004031558065610460040071170500325034103080b8500c11034152000105011a03024080009e502c51070301d0340d90740c4403421851a491001001d16100c0c150000c1c00900116004c80300d40c0e1300400d000740a0701391140c98582c1c1d441006080c90344950007910240c00030036001c0e00340710061041c554030030034620240c00701010442c80381540b00b001400c040e140105d148070400d0011001c0045401c506c4d42a50385200e829540c8118680e941d4607004c20000290800780071240c0d850280340320b00e00f900d030311802201c0828282005e0005130f40200e0011381c0e162050301d21103909400d19070040d2000e0040c840031183d0510782046901c05039503040c1d10501c1e4550100c6a1080481c1001c00d11605803281c0020780341c2d40f520104002840c00c1484040f041a54405c12034402c01c00c0322650000048910a8013038560f40d0380d13244c01504800d04903402d1f001c002070340001c10116103841603001d810348060b141040b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 660848866 1250 660847616 660847643
    0x6063105030a0c0f0e0907090b010c020301020316020c0409150b280f2c150a060e040c030b0d06020c03070f03120e0102181c05031321020607020d 64
    0xa494070794007031030580d050b0f100c5035014404580301c000b484000e051904c9600341d41d400c006080c01e0750340c00c0342c1c8202c0010700d0f0798600205590384210300818040390010700a540ba03081c008202911406074280020140c840d5035441151400c29000c0d0107440d07900aa03050000c400f5103417108001d0031b4807414080d40009881c40782d640300071800010744130016070100741c000700300e0804400c205010361710341005c117030015411405a01000c840c68641c3c6040d0014000f100720f91221141c803900840580c0b60507502911500001c5082944011243c001c110101c9007032000030320036481603084850204071036400841c2d940080c00840c640ba001040e000803403008480c540141501d8030059103440060490002d07403540c00003100c1492a010b1000302d1000b03038008518055203503542c43c4d014682060301d070307003e00d0214407c1d0080c0d0034800140705e501a0440243d076522038102075001610003190140d10141c1e00d5281e01c084001420103085038900d9809032015103060826001c104c09540011000c0b50101e5040030b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 660850116 1250 660848866 660848869
    0x7110d06060605042c04230316060b040212061909050106050d14060108060d02130504050a1506060203041206021308010608010f0506060d180f0b040b06063105 70
    0x1ca500900d12695201e440e14100343c0b80308a540c1a240c6940c003012409005241c8800d0344409681e000303948064225500d40d049101030310135a800210043d0039010200310302c01160b20a030b44100d1050f20445003041803901e1203041008a0280d00c00040c1d00155081c0012858184802000c10301c06000448400c0181d1760b851010546400340c1003480000c0010902c2000f01c0c4060043c1300340d2050803030f1031010520700a4002449064010b242c64414485450500300755101c081c0f46503c4640081000d015038901410116560089000104e41000020300201c44403000ca1003508281c407403d138095450103203800c00324256080e00101c2540e09079400c0100351840c100b800e00c4100106400000455143e00e003a01c41c6003110b41d8000c403020802c0c200801c00505503a03140c200c0d110160003c900003010000340104605170b4a00c81d00c010483d501c940086400c1c800c030700401501c542c3c03160b8401c01c1036943d401e00f0300046000300d018040d49043c1100c155001c007034158040700f03003462014450604090340e440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 660851366 1250 660850116 660850121
    0x7030c122a050c0c1302041a09180f04300801230a051002070f03030915050c0a0f032303010e090307021011160e070e1507110d06 57
    0x1000c0c181c400790042020020080c419440a00c0340c280e040071428007880020706500c591903006031510911015810001c82d0880e82c3c107590140401440b1038812260300221240a0b511007088144240f5044038400711040c40440c41510800840000810a03180e90b42d4070410402120140f54007403094400d9552040880041c81c03d0f50030780740d0740740406945408005604800c01c0c00b280142030045855600c510344a0001a5003160340540c1d040c030107104078180481c00d24501d85c00c10900d8480d0300c0740000a056005e18044103458805403c0011504840401d071060310411003106459041038212002081c0f01c41101d4a42c14007a041c0340303003452013048044500742103079459020207202c0840140401c0132201070382a409403805c0e00962806d03070f440e0005001203552000003000c000344444c070203801c402c060121068618440e4241c26800c0e4441c900400d002c1411100e100005101c181851521b1a00000c6840c50f1584044250724015170b45d102d07240b01ea10f101c0440c4d40c006a1102900c0001001031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 660852616 1250 660851366 660851381
    0x1009030e041b030e0c010e06160605091b0306070c0807050c04020a020312060f0a030b0702030c0105070e010806010306030b150d021203040f080609060f060d0c030b01290307030c12 79
    0xd81d4080d808981c08000d812110200c107400c03a02d50203001c1110999812004000c401d00c7d0484102d0740794240048022111042104018201400c00301840b1180c00300103030040041d001d142c81400f800030014145030781c3d482d0444070440010b0715401000b01140c1c010b0014508640141d0503070304c02000c1440400c003a80e01c0320f030245c001070b840022012034180c032641c1600e8100c50101e0700045500540700c0094600200c40c00080c1ca180c0100c2d0200381d550b4004c004465064002100030b103c0303480c040310041c01e4040c40065240c0810703c008002807680d03100e8800c1100b580c0c4d00c007480c0c00340c9031154002441002c40a28803035801041d071b40c0d03091003d0ba488040160b980b8007070704002e5a440b4144680604070210f15881201140d10450911007040f401041040d0720a6900003c200103544040c005140c09020201c0a4010b5503109800300c14486403152841c141c42d00780818140d090b1143d1244c49454a80e00c200800401061000c03842e460700c01d4100011481031403502e02080c440c1c89100f0812540c12 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 660853866 1250 660852616 660852641
    0x90c04050c0d0504150e0c03030901080c04120b10080d081f08060c07021903080d09020f09090d11070308041401170108010f05060904050322180203150f031009030e04 73
    0x1911417044c00d40ca0901035600406074243c090840d1490510209503a40102c64449050000040005013403081c16025100101100c103542c0107560b031203040c607503103007501a980c00c1c40c10f148044020810250006988160b00c005903a10082656181e034501a2444000b540a00306015500000350070541003102a0240c000c8110080d680c1c42c0d58030412841c0030016180d0500324401090800c00302c0d10784400d840200202c540c022407000f04500c0055030300300241c0001c56211120000b0f0044a0750005007405c5034501f142c8441a0306446100d059656031024480100300d40070400080c001d201101ea00b0a00144040c1042c1003401d88038244a03014803400d80180456130355400d640c009040d000d0007a190007810075101c00f410381c04e0fc0cbd100d4586a2080180456100c41d10a0450400c82c0c1b0112400300100503c0c0c80c4c40484078169400400654000d03224002e00058040c103035005440c00b41c90403025104010700402c1e00440341c80c0c00c24040c0a144070144e05007d80585c000040c0e071610300880a80300344 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 660855116 1250 660853866 660853883
    0xe1f0e15160804050303040611070204020414030f1b04020c010219120c0e0904080c0a0204020a0c21090303110102090a15080a0e0c010507080904060608180303090c04050c0d0504 78
    0x184881c41d408034164000c9404208504901408007080002c0704803500a5000350001c250041081d203941402c0c03041ca01c0094019200090010f40150302c14040130315820100d082d50ba281550701d0706240c1d24540d0350b012400341b200b1034840d84102e01d40381e03005040d00ea00c070700000340c200303c0d0241041580b4a42c100e240000f2440760702c01038104640700c1c85086411000c9040080c045183d00d40030a001810060000b08500400510703100041030800c0107988441e80140255616150303e03000502c4d207103114004541c80c540c5601e403400080c1c02c445440f1600d1895544408409185031001c40f000c3c860382c1c41d00c1c021558204012822925244c0700c840241c821040c1000701e0108a0900070550703040109607800080c90404c40c0e001c0d034403021503422610303042441d1264a0318000d0501c40e50912618140c55441860103c00045454100c41c0544c41080340c00e001210320800b1601003030b101d100c00c4484080d250000001e9040f589055032003140c011a800135018100b00541e213081c811a0025181902e40b0340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 660856366 1250 660855116 660855121
    0x909030304020a06020f0d051803010501030305180d08070308100b070605011403011e020903011d0601090605060f03042d050c130b0d0605040f1509150e1f0e15 70
    0x43c0002000e005010604c010300030b0300008020152160010303842c0030100b101c0016040d4a915644c1100589400d00400030412960360f8075000d40b060348840403008004c041d01c040d041091801c0365406031000d410150300c0740707004495903044030707442c1c401852000b10911002000c142c4900050240c144c03030b03116841c0010a9414034404408003d411443d480c4a6810001005081c07221410101510000d0120150f00c070041c00c03001070b000d00014407454a107640e84409ca440100d500003542c904960801904102c11600d410500c44503214901c03041c221030751300f000440c2c0012a409000f05821400d240b5500080c00c2c0494450803c1d141d188055403158000748180307001d446c0803014903019403100c0508000520216012030b00004a00e20003030191030391a400a018000400c240640050f0b01019014510104003a1800100a001000d450b0207541c0c43d10000c40c200248100c400200754440200340202e40f01004640320302c1591680c40e000341c1c1720140c0700500d2008010704103040c400303108074041d140b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 660857616 1250 660856366 660856369
    0x812032503050403030b100c0605040c150306150203120133020a0317060346110a030f152a14072a05030d05070218011a0d0b090903030402 61
    0x407180e0704540d901c02c60300602d00c0a182234024540c41c0c0c16540c068070104541c1c0e647c0c10070254400242d40405900d801c4004103d07a0158145e020000390b5040102159800c050304000300d0b6a03009690340034400c0407540e001440524110b40328041c110f4012045045134142581704080345080308420040942d212600a1040541003107040c440d035a00030804210514150001a07030715041e20100481c004000480e0000d8401c20300d940a0540001ca0380b411a400e1044034510148a032046050310a031120001c0c1990030b01e00385000c01e0840f9000310315010880300c561501c3d030031003284e4910707560a282d851482c2c00340c401c0c0c04a2039054925040c110a001d0b01b484170300282c5044001901ca154481c01081100b001900f802d90217410525075000f400c9203152901c030b08502e0100c00d500001d03414800c04107000a4168000014004035100740c0c1c02c422102c070348803400280d0700020b00541c0d03400902d0754401820f01c03111034080d041d000c00c5041c020458460420102d51070420030781e091185604000100700a5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 660858866 1250 660857616 660857621
    0x60c0a05070306020d2a0f020a050336030a061e14010f050904080d0914010204080c01110c0d03050f1e07061b0c0209041518020f0a081203250305040303 67
    0x350000805040d0380c00f081c0c0b059146c0c0c3c07140707828240c01e0001c00511040310070310801039044985c3c1e100c401c80340d582c0c0000020582103000304954686020700500d00c0051a07180c180791208170b29002e0020000b00005a503094050408a00f145081c88580000c242e10f000980c0250340c0300003040292001154142510740813141215048070340150540c9040c0000103940d03104860003403254940c00640811580341074426a03021200c0038500d07600210700400c4c004070108105480d01070988800d2a80d604070b548083c0c45415001c0e5540d40720030582060f00c0800d0040006110740800100745625044c0e0f00c0c0c2404100c2800b6810092940001140050400c501403003035100b142d500d0303d1541d94146a5400080042041c444000c2c012000342020404028a005103600900c000c403d051214485408000d080b407414250240d11601698001207074600b0140000740030340d0428805000413400d140f09000c040d5001a000b0200b861406a0000d00d01c0300308042498000f22540d00815682400e003402401d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 660860116 1250 660858866 660858881
    0xa0b060a030e0f0109020d02210607020601061e0f031d0102070305130e010302030d120f0216030e060310050d020a031b0303180e060d061b05070b010905100302060c0a05070306020d 79
    0x585c5402e0880001d69500b00c03030345501c01d40c1103404041c00c91134807104586155040c1c0d1004060304c10b000c01d0003005038000c10030505851141d92190080d04040652029054400c20204041001d00c901c004a1034825080504441c114a2502120f0550a42c816089a000542c250b0010f00c0102e0046a01ea61071120080246074012100d43c565055800103501d5401d4040c402c014861042403000b040d007182d810040c04107858141c110349480c0c0c0e5071040400b015521200b1030000741d8030030700c0840c20700d01036003a6800307910940d50345c52542c2e0900090218008c4500d10a0368884801d040001c0061841002c622030945002030303801c10149145009000384205503c120016214090244a0502d0b29214941c1c0100111240e00d00e00816090690050041000c817458044004000d00550b40e041401020311750320440035441140c4e40c0b450201d08907541960800c0102201880410240c42d00c000a40b41e50300d0320409440305c104040d030b00c0c80c0c50030702142d1084a001d40c02040440e14845c05101300c09 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 660861366 1250 660860116 660860143
    0x1021309050925050a0906090c03050c0d51030302152508070f181a0c071e05010305040b07030e0a020406031a100e0601080a0b060a030e 60
    0x10440c140580b01035215081d04052030001c01e1600544510800b004551030020803000d414504816101c100000c058007040c000c00540300d003000f801d807000501ca8030a0300c0c4240f00d600c581d1410b006420304220058101481c0b0310701d2400c5030500d843c580400d03041403a000048005884400ca404d0004840480d07030036102c00b03901041d00c0001c00c201207600030074003e8120350360038191822030b40c138551103c1201050711107a2048181c0046890b0365039400c080c45034003600d40c64481030145000e02c00215200510340c841311081e0000040104001882d9501130800354100030002410070001418092600b070055000c0b5030484039030740c0001c0328140c40300e03500009080e080c60240428a010303180e000306d08101500300070070550b840d0540c110740031060040114a03580203106000341643c0f4103201d005029400700c030150081800001c1120404030300108400c60366450021186035503a6001540d003104020850301c8859100d0078400416502c100050585150765203000584084044d900d03072500c0800281c00c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 660862616 1250 660861366 660861371
    0x60906040b0103030f05040918030e063c2d070b07230f030109050f01081504080d060e100b04050307090b060c0a032106030f0b070e030304060201021309 67
    0x403000c1400324200c1419650142400c5e005583d490340115580c0c85203510026459103464400d00060310011190207200e0302075034410042c05000b2041002d58850150f21000b45840300504075600c03069446910b4090346a207007200b0302000d2020400400381c0c080d41c4071580c25002c00e286010b4444603084071216180540314828140710340c640d640e0b10074400140c00c0b4800d10000030710011114070907410415181c0c418047c2c90351a510407207821b801035002800b540e03848509000000e0401020f10004a048039890001807046078500074043c04c0c1c1240161040d46d0410080204124003801c40c001ea500a040c1c41483c0c005c0c80c546011025800c0005400c50281d03039a08000810450742c0024128083c0c4030070b440c0c000b514540c001c00248081c0b04001030f0911300c1c01144040000c0c50380110a400710031848044910400d141c131074a860803944a8000140400c0c00e82141c0b101007400c1d020904e6114200f82131003112a1100d10000b03140d50440d07030080005070740018032008190703203004030b102c018011448203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 660863866 1250 660862616 660862621
    0x20717041503051f0e010614032412030a030c09080d05030c0a032318010b03250806100302031002040b0307081e090c0a0e040503030c1e040801060609061d04050a060306050a0e060906 80
    0x48651030380201d4001608010248001e00ba640d0b103c0d24bc0c0e0840310240c0040b25a1001c401002030003500400d00c0141c04581075400025106ca00891446154400c070341c1d0b02440c0d50340e40d00204809801c881608000c040d540d200c1d031014503852241709095030701964030007001450055400e68007003c0a0756004556410980f04040540780000d8000c070f80300602081d0540d0000c6540c0001c2c20700180e034086801807184105110342407068444032020782e4000e900f510001c2c54081a900103038461342c40303a2030303500000300001025544114951032b004440311b001c00884189102d1141c5144605680d0380d590b5800034a40c104403460440300d030b100202241c030a021541c0c545034580680f28080241840190307140000e480302c1075204120300014004251081c82c1d144c540f1203040e540203215038010900030070300855020440d58090a5148005a0285241c003001482241400f014010280001801548404000c00012014000c0620616400c0c80004002e041e00240d240703001c4010f03100030403d8208405 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 660865116 1250 660863866 660863881
    0x906051807030b040207020402130311090408030c07030e03150106181211040b1513276b070f08070303020717041503051f0e01061403 59
    0x105507440039650400040482402010801030f20504200030f501c240f00180c50020041080c444d50141c3e800350701d00d04507403d084030030300c0549401960050042c00303003400011680325180005200203442440c00c41e11150070300000ca45003400c103040080c3c10815400040c00711139400405055040400101c0c0d00e501c9141141c803010b41c0d01e82c10740152003070384482c031056841d8995800c803110b000030140558640c0c0c020901e51190b140c00c881103185981000d8075000400d4901c01c000c0304400c0c400d46442070480d42e68845030348000c01c40c8a001200c210000f070101c1d1500c82d540078510002103200c82d003844042103101909010500141055004185a28607500050131141d4041021400e10210300e99102e81500300341004507080742004088403000540107003090b6250700030307115017889000d82d02d0000300060729140c628003c50003059480c80301e2404003603100e0710a41146400211001c0540c210120310340084180c40c1d450b0300009001030640c3c00401220741c2c0043d0030744144194220541c290300f44010b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 660866366 1250 660865116 660865159
    0x121609060c060216030206090c192d171204270207020604091a030a0803060d06060e150102060f100506030402121c020d09151103130609090605 63
    0x1560308120700d00a8007400c106599044a83c004c0c40001030000061303181c540290f9807141115400c5e80d50055204013400350810702c4001d0402540441c4283c005070070003a44214146800280c0da24040d0004c1c00b01c2642021003000801401d10301c05d5074223a0074003060042d854035904101818031000e082004008180e40d07041009500c0e6034224003800301d00b0044a403880603000b5814065030200c0d0005000810340125403240f44007000e02640a901e081d5400b080540318019800041c10a60007000041c0003031400d100b200030494480c400025504e91608041074840d0022989801003401d481d1404485680402c480d80d800075107400400c002c1d2800a401e40c52800807440b4586c090034002c404101190b641300740d446455106d020444d00e450724151080b1050b8003026020700050f0198030140d54020b8468111034081d2940b036a2000010403d000c0c003140e606401e80704482c4c17140003d05c60b00c41807900920406004098a42c2c0f240061410300d40c12000f212820741c44288030b1800003d40e44031100c4450f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 660867616 1250 660866366 660866369
    0x1b0105040b0a050306030708100501090f050906070f230702090c0408100b0a090203040b013b040606080a080319090f02010c17131403030901091202190803121609 71
    0x145810383d180e445d0500407900c0c10303131280c0100c1072902400d803083e60020342c0b590009048441c002003d00c5086d48180d20328049130303402d840791001c80d00550b0004d0003560040300e90b2600081c252503d09030f1041010001d520741907410030800001e5400013140b078254a03111140980000c1d05003091403078189040f041c542e0f01d500c00301c207200e01d058413000c4003501a5107400f015001008074441c10342d40da01d4940f4101020341824021041d0f8040c40002c0c1e010090040840999280810303018803449450b1b01c4820300e221400284110343c3d03e81c80e00008034480e90107018185510b44641d10143e00c9007000f40802e950000824400c0214a00d49004140420f02c020f01c240c45154081c200a80040f10b5401c11600d10200501c00307a003080d10001d10140c2c8244201b61400481724040905900c564800d820161244142c0e031030240040c0204005000c060310740c4d551485200d100801d0705411100c0c0029139254106194843e603401c1d00041818100b81c461000c07000d600502140c4003003254070b54401c005e803066103035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 660868866 1250 660867616 660867637
    0x9090703170f0414030f030f0403060504110a0602030a02071d0f090c040c050d05090111121513050105190302010518010201090f06091a01082802040507021b0105040b 73
    0x11902403040da01071490868041410000e5225581d544030200395500c00360b481c924601900c00d00d0914a0440c20110a490840c9410703000c042c0f40a01d1501c1d200003811001d0019034400e851420014000d030780708043e1400070006a000780d0384030f0324603035006801c2c034a965011b0102410040500e4035144004d0341403135440a0244202c1003551a05013541707142089200d0f110703030072901d002202500b4541080c050500181d2050b0240003550310358295500361180c2851a164460040c0105c0784101038102d0740d0b0340e010701200c0d810540c1e140050001307840d4140111603a0501d0342d40b50b00600050420100500080e05c06014900790189903500080843c4604180020b05060303200220380242c0c401c0d0000f02da042c0d0080c1141000801c18108040244818081111285018520380c902c880100071054100c0d54400c01801a05e918117824062a103891506c1c850402260b032100c80050380c480c41158000c00b8554002c00c2a04094001e205a001c00c0b9100d0a0620a0071300041003000700280c101c40303a9410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 660870116 1250 660868866 660868883
    0x11b0f03021b0303010807080f10110c1015120b0a0203060d0b011d010f270204030209041b08010207020a05040902032e0b010f1e0e0a060e040b09090703 67
    0x40018003100240034106404140e03034805161001010740000285040e2403034a0161480d8550383da440664400203070881d0f036001d4000c0072105048084039800390421082440b826450680c4140f511424540018941c896090355171050407041c61403801004050080250000c1d0650016140e002c19118004c1000e19803d03000000103c5d82d85524060004841c4c0c003d030b04000550b102d1031602d6611418134041001005600c2c00002c86040c1c1e00c01e01c80032110074240c01450100040c800001500c0c10f14615503810f60208000001a229a403286100b94041c1e03c00d04410003000b00c001c0000031481c0c1c001c030348a03030050100601683d180c01004044480480c0c0005032a22544082403d100701c5031040d40e00d0382134020720000d0614203540140004421084200000c20841005450021010030040009142d0625460f0b01c010070600524050589003400b101185400b0001220301c0340b1038000800042812038100074a003000d015062104408035816220741c80c010034010344d110254803000d00b01c01c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 660871366 1250 660870116 660870137
    0xf08010b03130c12050a02030c040504020a120302031b0c0301140c1c0605220b0a18020306040b0a090609151a0a05090402130602061003030f032d0b010809011b 70
    0x143d10150001000b1122141213001d4041c00d040c0e40b90071824801342d002e809002240c10b014035040c4071344c910941d8018480680c480c200b1212200780b0200030f02c224254031081003e5090041803510300e82c82411100e0050022a51034000d02d420760300302100501b2440910028816802003080c217517005450054182c0b9174103110343ca4241c003d031101d9130103660056055500c95041442180c4880700300b8012240030b104126804051100c00c010314442c00700e47d0820004101060b1040b5001907412030f00c010004213040342250002503c501141d0710a8031210340e03400041003070548a0041c095180c10524660185618100402080325104142c010b41c10384005a02d000040c018405e9601c0004046c10031500c8848886450a401400b4001e20000d40b05050008604020501c0c2c0001500e070b05598582c40702c0000700d426030141181d02c6078100030211004140c0c2060f415002e074040102c045407008901030270b4030000505841400340071941164101080340541e00c9401c804041d500040d840c1c03985045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 660872616 1250 660871366 660871373
    0xf1401061a0a0201061e0e0f24221508071401052b0f05010b07031205070c02031f05071d0906130507020109050c010203090d081605030c0109030f08010b0313 69
    0x4040300c0d0001041c0100e040c0350341013402a40c1035140181e47c0300d000e42030516103e1800108881c48210f50340c2c9402c0702043d502a0354090070030207a00300c4240140c0181400000050541d6a0650203025503c0b01d0342c0d140000b03070b464041021800010711410014018450920712128401199220001c1c188440082c4d044101d00031491510781d01807075801c2d59400c5025018400b40607102c0f03000702401c00d0f414000003003409102c84d000c459540764181c440340c01903080380ca114400341c4401403218061001c05540b110141e18180841807020440c81605403500f0301505100046401c050b046004001640c46003c5881c59a902003101c6400212103013a519a43d440019114038058121040d030541040c052103026901500104d41e141d21131000e4444115144c8012642c038020001042d0f84a81c0140b00240032035402e600402c804010702ea1140b003a201191219071071a4449800c40e1100c0e035440303080314241507108001d8103022500b0310700a01107500d0020700d0b01d41d82c0405840302d00446044e031420800c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 660873866 1250 660872616 660872621
    0xf050609100e061603030c0f0e0f01111f0501080c0a091104030f1109060108090706050c03070c1706060621090a200a0b0a080c0a0c0507030f1401061a0a0201 69
    0x3030b45005141076030b10407448006800807824407400300c0200f4100084400c044d80107985102c0c0e90030545c0c0d01e1031300800d101010000c014046c40310041c1441900d03800d4a403030348001d0102000d41c0c2c180601e0304400c0f0224218031000c4802c141e20a08154000344540c0c800c0d61b0b19460b01c0d600b120a0f5940c08038a024009804440c0e170720071540010f0107000364172400b1040200d500b02d14040b03000c0441d202042592a1703401940c0910080f141071416402480c0c00b400701e00d0080c8042c105002d80700e022a814034800d075a4020300303061a034104800c5070b0183c20304d5a4100c0c4040010b503520100c1550340d03d0030481c10130000c0c0285c8007544480d21901c0414400101102e808001001645410921302d02610f22541842c9400d04007400c0694000c54040c2008584c10180d00304440e00855260345038403484d925480305107501d0b0002000401001014181d04012440c1000070ba4061805215420315040c41c5280c0b64100c085030030300c50324840c2d040c00d80421910f07111185c0c182c4401084414150340320f0300160220b00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 660875116 1250 660873866 660873887
    0x703060f060c120309080910090b041d07030c09050d030c06050c0d0c0302121f03060903051b010b030703240f0203010302040605190530060a060f05060910 68
    0x10811801840081c04640c00141c4410180c0036074a503840b09126110300301c068a030b02000203130240a080100008a0500c070708500d0740300189190680445c0d403202c4108a1541c010f40c00351401c0321b4000c0c05400c5600400410503048201420308010040503444040d000010511845202d101c0d41d00c1401c080c035002e040081105540020f0410280c5042559403150b0781082c01104070f02c500c0c00784046d0701d50b40a80b003180d019082c024207003e955aa032450704a501804032804030980c6050100010008402d4015064400e11a8984e6034071445a10040c0300e0103904d034514000c16a06114003504541c6002c99008162500050310ba2020382000300700c549001c10720083e8004c024036140a08a600039a50b0107141600c0c0308071000d121b030944d40d80400850008911a4100880b07103034a040001e0314009208440110341c180e02c091842c418542d1071000044004c918114540080040100c00b0310141b156601410080030a1490b0501303250204176240114410203004114042540c1b09041c052240c049 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 660876366 1250 660875116 660875129
    0x61d22050a060906050a030f080903031303080c060601050301050f010e0f1c02030f06240102010902060712111609020c0a060509070303110309060f090d1203090c09020906070308070306 81
    0x1074107104070018010000c52281103021440c2c92808202491700041d000c0c21203030042c0d00303c03044c00f60a40342e007a0180e003c001602d034548810882015010003458944004502a18969441d5600780413218203103500245891304022007080184110799801301301140c2c0c7e02e428a002e0110b800400085000444035845069110714040f02611030f100c2a80d4011054030700c281c0645da004410058820341d208019a4940010a02c02170f4100d00d220201050000e85441480041104d44e041d4000c54003a034002007058030b20b034000c02240c0ea80d150f08801c0c1d000c0210314050041141c87e01822840c3c0300c0ca02c0354081d4002c034540004403d01c24080411080c241c15421140402103070071300100c4981e6501040c48110b0104541d403200340204800031003925029200508400d20f01400e10145003402c1d400941d24603446102c100c5602c020441250200d0020b5980780c40c0090043d0341828a20070800050303003d15a40d41c0100b0400d24261103120a41d52000c0d4503081c2542180c031820000e40242550f0780080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 660877616 1250 660876366 660876371
    0xf03060906121707020603040215040b0d060509070e0a0b280c0b0c09030d0806030a120503100e041101031503080a02030702040617060c0c01021b0d0801061d22 70
    0x210b0103504903610300b4000c501c40c08040d21800c1104003041050300601101070352120040c80018054200145103d400141006181c8d00d09601d0b400a5080b0350400d40200b5001c0d40d5500060050781400a01305402090b0303400c00e1407a4010100004401d0011401108a000c1003c19201c507144842c00c90003120040000c40340d4601c514085006044100c1d00c041910802c0d842400300d010313103040300210b50040d00040c0c090121f00c4020030003a01c01581c0584120740600c2643e90140100e258200c0741c0401303e066541c2c0a95a040402d100c000880e1160002007040b07111406001c00a0369080304032585000c2802c0201d0b55401e1481d20708540e00080d44050925040050110b1100b075011009004e10b0348200c2e41041059160310049002400e40000c02a5680c0684003050007242400d0152000104120016140c0001d858461050301d038003507804403843e07103c0c00304a03240c1c41d0000c2c1c2c2540074104618052802b507508011b2442c0b56520400254040c41f0002015244100c40c041041e07500320a2060a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 660878866 1250 660877616 660877619
    0x411031603110328020405070507060510030b280506010c020a08060f100e04060b0a082401080f0604110406120f0b241c020d2409120f03060906 63
    0x510b00c15000c00110310034042d603514407107031003a0b500d9200c00445030754000000f00c020613428000204070150500050000c00d000710400144507020702d52103144184859036105155203805191004094070001e848041810440c090200d1800908144a00c0702c1020540b030b107858006071350141c20568041d410041424000c034208000080040c000d2801444030390540d0707146140254240064019609048044004a000710701a60414038069800030300c0740a205540c0d56038545003040e0803901201034840c144000300c180c40d083c1d0140d401000c858000d40110100b40c2d11031900c810000b04010110022618403240d1078440b40c1c054400740884500f8622043c0c1c0c0350800500c070b500c140c0000c544c11058003000070000c045d180480050304506014803442880c002080089060301c40c1c084a1414403416161000750351101a0445040d00522590715100c01300c0c1519220150b2100701c0140c410b04100ba010000fa443d107100c580e0f0400f192500f0890b2010010040740541807503408056403d06180e030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 660880116 1250 660878866 660878873
    0xa0f080c0304030b090c0420031b030a06060201050603011a010f03020c030a031b11060604020702030f060c032d0c072406090b010810210b07020615010c0b0411031603 73
    0x401da03016041e0780046888561b085420881a1441c0051002c006112041111f03081e0503000c0146421144850741c18412030004607103000b80780c00489841c0003064503200100f003803d030288109a00420103800038041c0514095903c40c401d004d607000785040041c1000034007d55131084d4181c8500c0b141950940390b031402191001130140049110000500c2c01880c0c3c9111064003401605000d101c440018010640d80c070800c02c8000d41004a05903010700030003489043c40030301402903900c070b01c0e60200016100d060030348000207075400e07141c480c43e80c00e02403446140c0844504109150b06c0b0740c12104d6a90340d0b442914140803940c000b4800580a0303030340ba480d11601d01566400420680300c959004100c8642454011030b5029029202a41016000e03e02800600d5140844866042240e00e011007070520540eaa00d00846040303c079480107030441402c0c413442c0202c004065090030001d1a00c0320115569481d005058180075000420007103400c640c103101610705211503524001d03d080314400b030360380e42d04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 660881366 1250 660880116 660880133
    0x3021804020117040f0c080102030702280807150b090411090a020706140a0f0c050f0705010204050a060c0b06120c0909010b030d030905010c0c050d0e010e0d06091208090a0f080c030403 81
    0x10011925175120f51b80214420105200f520b110b0301d840c0e4014180405400c3c0c2016400c3c5903041015081d6040c00c0c0e00c00081210940201212881400701d1007850783c2c2100c06008850b102c51040c1c4c803903680b44081c80041444e100110200400494007041d251311102d4140c0d009200d40380000300719504240d100340808403203900c2c1d68813480003400c0a000d9428550031381011617111401100128000380040d421071505c0c1c00152040034400c030001494603480da0001348050f58580c1c8000001901e82940c04200a00400440c0d04000140e40885003068418040d80d280c01c0316030f02450241d1000800251001c00940101c44ea5603805026a10340c882c2209004000c3e141290055a066080c10918045d452040d6410000650081d02a1550300d40c07405044401c0c061040b4414100320074070042ca28165a505403031031650b88903000005002c0084c0c03402150404000d500d94060000300002c0180504d404112074540c10b134400f0302c0718603002c46460050054040c8a0356015584004a0003004001100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 660882616 1250 660881366 660881393
    0x30c0308131e051005010503070b0f0d0e1b152b0f0e0c0f01020706120615121a010909090f060f02040f0b0415050d09051c180302180402011704 63
    0x200190383c0c3ca5a134a410300e4083d9542071151980660060004022038110200504510410140103621b00900750388850301b601c1081c0e030000c429400c1204403902985003480f0b15802c000040c0c440592036403044401d104075010b50310f00041a00c0c1122140c00482101214280389089255420402003201c0b00382c66008180000500c41640300b500140065441c0c2841e00a001940581c01443e900b0305107a0115105803409406140068031510046000d00b0140a00c2c008800d541d0b840d031224541100c50481951920031502c14840d0002d85c24a2072079a1068005055440540c0c0102d0301510600d0004211041800050400b600c2c050310b0000c80d110a80003081111110300b0b19090454440c03004001c0d40c401c92044a000182680054880c41c0c0242c1c040c101d001c440c844c1c00120210992146820003030040130ba02c0120060341a5089456000209031030380501034000f0403c20341c151381c0400c402e4078205040e214540d1800000030110780c4507490000b00001101804c144908143c80c0014521041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 660883866 1250 660882616 660882623
    0x50a0842101403060f011a04030c15090b090a23060d05090c06030112020904020a080f0105010608010605070512071e050706081302130902030709111305030307030c0308131e 76
    0x880c2c400c540c645000516580a03404044200b06181d103071a43c42c160f1a540d06001d8061504144000070125000704600c4004001e00802d0340c41e0502d031030f00c1c024691100c6801104030000c0501c050b000a403500c100c2c000a842403030140b5035581e0440d255100428940c006065401140092692009220360700103500078040e1100300c0d441d151001d8100600740c0024000e011400b48440c03480005860800b00d4070360000d001a0810209940b1b0f034801c68100035481c0810341d0386a45071401002202d0b40075210500411203132a01c1402d1500303665034541c41d803556140002c180385010500d0800d004000040310310b40020140d40f080c402869140582e02ca641070f00c203950108030414001804c44040164880002d90300130070710502090302840c514020150450103a0705403207180ca001ca0705c00310a100d00b07910b027031110442030f4039408412882a04043c480d0403981c002d0304180880710010341c01c0a05480c0180c1c1c5810040c00c03565601d0034002416041c0c80c03014000400041102d200d08800203805030f2111301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 660885116 1250 660883866 660883889
    0x5030708180106080d0e041b051611040903020303180106060e04050a0e0d0c1b180f09060213031b1a1e0d020d1d03031503010209030105040b01050a084210 68
    0xc0081c03452004003c004094030100d5401c0080560300c41030304ac070b1303140345c24424000c001c1105d41010119044a556a004034003591002003444040134060001d0140c100f212802440618204507004121103007110240e4081c64890300419008134040d0011000700c007280088039600b0807035040040200300000000c1c0c034460311203a070100035030b51541c0b8024241e80c03013505042d940741e64901440300141110705098007250b648200307040001b180c3d80021b10341038041e0802c43d140503095052203c5000700c01180c2c00c0079028000e004100c1d152450154408005140000544580408071100311002043c1906118260001804804c0c02003a07070252040744900b090411054001c26100171401c0c032407846c5021990310a000043c028015034000e0420404042d00150400c08036502190940c1d1041d00d003141d080386000014080c0c4c0c10b09100075401490168020008011041c0b10944410307100443d56002c1020285280e50302d02801d407080c407290000003c150242c2c5020540300fa154629401a40c1038540f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 660886366 1250 660885116 660885131
    0x160c0303090b0a05071103150c0903010c0314061c0804030602040303140a02070504050a060b040e061f0f0804020604120303150b130b090f090c0c060705030708180106080d0e04 77
    0xd4004043d549000500c3d1501460496107032a65071144d440703402502d07403510030080b0601002c1052030400e402000f000400710348808402c000c26095034068a000c4d4109440c01112040c002600455140c022405551011000440c081d802ca80c14000700d0340a002620009800820805580e004004890103942c40030344854060a88030440c0c480d0041400042c0e004141c103000d986001c1c0d00a81e004415130b1000200d00780c1e00d0030000504e42040e445440d940507840200541c609000071200c5c20503503c1844d0304103000141c400a8802c4e014041000d00b0051480000703011034032650202c502034401c1c010140110002407400a02400555010f0301604040b0b0500180c1d0b00304400c01e44105040ca0f4070700c05619400e240380401150045005e1a6002400b02528081c1f6221084414016500c0406c8079a460341314a08041c60708070060b200c0000c21004000700f0115030303400428140c1250346110003045c42e003034401c038480c0905125046644540103880b8010300380d682244010030b02c040159014070048 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 660887616 1250 660886366 660886379
    0x4031e08030c07030f260c04080106060c060f0c0c0f02010923040b062d221a03010f03080318030d0c020f0304032613030b150301151a160c030309 64
    0x8075103000e542c011002c0b007030811801b0610b1810390954044541d90480b07041c29940c0c0c00241c02e591003940b000000c1441603e5110512045c0d00403039144481d6803500b4000700c50b80050091141058440c00b424902d084c546030000c6a00c1003800c10014540c1c0c480744408001c400c0a000c040d0348111185030700c80d1b403400191a00300e0a1030401c0d117414619103c113100807022502a60b81501600203441c0446100400030005914845e03440300450301c94610000495600b007a1b01c10060b580130f905d00e200703294010300c0108110202100d140c020f595100034419101d0f199400e5010749100450062a024000032802e0310985125501c1404085e040d5400c9440c0041d203a10481d0301c911540c0000f03084443d150001410342903171801110701498040d0355992038500b55060454401505800c1110190720040900c0b1903180820900781000351f00700c000300141c000c0b00c540710808162510507120440c0526502044801642c015a4a02d03210442001c03a07204087c9880c0056040e580000c40100c3c0c40440c010814 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 660888866 1250 660887616 660887627
    0x190501020d020a030b0909121b0106081002070c080a0f02040c1814030d0c151113080c0f042306060c06010b041d04030f0e0a1d070e01031104031e08030c07030f 70
    0x200703070008d020340e49003040305110f480c4400c55a00d80c241d83d0b507407901000502104104592902c4400e040f07801600e03500c40e46002050b00c509a4004030083c2d2020654402081c3d408540782c038102c0e8100c3d400201341041020a5820380310084e0060039502c9a01c4001503030b41540c075807000c40350108030180d03510500c01010540310140d8812000d0301405841001f0300b01409031350f0000c200c20702103106050a00d004941040c0300e11140d50000121500a0340460000d800d103204090382030b2200b00d8003403083c4102074503503241c00c0003010507080c50080b4030008640662540c0c400c4601d03011a10095660960b1612503050459102d40700303225600070008a04141e0070010020030380650341c16500d6007d2030005400894030300785055130095018160b00d500140860658000402070070040400c00354500c2c00d500b000d0f00d0a034800030210b0505041c104400d0b01504204122000d0b0382d405101c596500c01040d41558a071110088000c1650000106001c4d40d14825405405102c1c42640c518140c0040a1000c070741 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 660890116 1250 660888866 660888883
    0x303200711100504031e0c1a0d050709080a110312090a0605070203010b040f090203100c0909020f0c0106080a0c0f030c050f04090512070203070e0603190501020d020a030b0909 77
    0x40d0704003800940c1d1803404044522030400c451620340d0409880341c0321001c100d07051941d016918041070032040c041280d00c85142c002448540121110701030301c208004824419100401d41107945c3e4000a020340d402281120301514008003103c42c1c40c035041c540081c0041840e07009074800d00c06c0d5485083d4801d105400c840a0304400b92450031161b141a409594540140004991554980c64200901d481e039100b1501c00d0355406102246041c0c0a005150a142d018821440340e00d04007400281940d400100710400c407001d484006a82d0201c0c80c20600030707070048400350703d407950a00c24001143c0c0000110801058050014003004644e0349181204a40b01880010050101c422040000d442c00c0d40c004000820098404540401a903407071904115001d003400c882024007041003010350508000740c1d00a084034400e006420300304240041d03541d8400d040c1085c080111020028200103080d01529650700790548195101c03000c074400034000c1d1014103a01c50103170141c080003c40e56003002942c800c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 660891366 1250 660890116 660890123
    0x50f1e010b15190e150306011209050d0c0302030c01020403031701091e1d0d020607020d1b0b060a1508071101051306020c03040f080307031128060e030703032007 71
    0x40c90101580744501801c40ea15900000f1300c100f404035840b40d0b4594811034000c0c81c1091040d01c1d50780c9015000074100410100e407080d0b0191405801500160001401d0b41d1044242e003480480460f00f403038100d10b148505c070444103040d400070400104058101280780500e4044136640010351380c07a00d508200301c0d45225107056003448a1107031078002140d00d0344484201e8a55034010310711a00d4a408031843d10704904926801a40070b28104404980d040c0a8207040714541d290015200d4110000500e16070480e61014241461181c04900645d48610030700c0010321354840341c020005000803020700a0031084600101064200c400c90140702018400c5511520001c540c05861140c10741b04e000080d08602c1e1070607118441000b0108000b207501403607000070309043c3c000b5aa100020702c0d0050030f66041c0d0b600e01c03990f50b0080c280003554029010000e98001c881030720900d96042c107814850050b045919010200d40800030f004002d050703140e040002101d082203e5a880e074031008040c00c0b40b038440c07040c01a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 660892616 1250 660891366 660891409
    0x705070b0106180305010219031a030604020609181303090f0b120402120703290402031c09050d11190b0a0e04020403170d0b090408070f050f1e010b 65
    0x50160b140620a040c421864940500c00e555450f0759407103007240d101d5015002c0d00c54648060480316941401170000c020010302c0b216214020b400d0100360340c1c04000c0d2009208079008580c0e0070075521001c651050000c00000e4040540c02c120480040e480e00c011801d40018214140104081030450741e03000c121240b40c000b10707240200d0744d01d91007840c0101070300c01c82e4030042e01c403925001c00d23004004c99000345010b042e841c00b070510005501c208030805034010805800007002080f02503a4003240540c0c0c0000408080680484c0306c0c541114091410b8000a80c0450011180303010b00140703000c007050821007a14280242c80160144812540d03d905c240904000308200c0e018620f4819000100113000107000541425120390b600c0600038000c0c101103059803070100710540c074888079000340080740c801078400300400d003040e4072606228890004d010304194260076110302085000c200c1048c096010b50151030040b500b561548002c41e52420744c5001541c24606500a5403600701c084500c0c0c90b00f050710a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 660893866 1250 660892616 660892619
    0x70801030f020d3311030c0a030b041d0d02010504120e03031902010504171207030e0a14030c0c01110604030f120905330402120102040503031803060705070b01 70
    0x404403000c0700000c04a03000600c0003011000100b4200038010310110140070b6410f840b02207100c01c500e8600007007000d4045402c01225018000c041c3c41140c0d001003c40c40d04a50360004c004c410b41c0030707003900c0e00c19039081490408412214000d91815400d001c40301d2050f51100252800c08a090b01c00c140c60290200c1e03580710038604402d0144008048220000d0705481c00c0c003110520303800c80c0c000391040e1000540d4641c42003108000e000e0130182e1044071803200340ca0408026102c00110000024506070901da940c20300d41844000400201d40d001d0b03801000240303c45201c030001603e0307400021030807880d8031400c480001c4944c0182c0204401c082d0440003440c00d95a552801c50701d005078102c071281400b0410030005150740d6180a400701403405280140745a40015800900310302d1800d100144075408a0104d40301103071086803141c1c125404403004100100303e044003900902c11548020342c103210004183c40700ea806078128408001d030032001d0714150f640e40d0f030041da207520405500802103400c1c2c400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 660895116 1250 660893866 660893873
    0x7110103020a02010e1516050c030414040219020c09090102071106030c070b10061e02030a030b010923030f03091003020d11120907090b1815040203040c0906060807080103 75
    0x182c03240c2c0c0384510022450b6030400314a00d0810950f120099050003140b000c0188066240340e0000d006601490524904685c5034030031507d0780100c1c01b4110107410684800107a90742c0c2c98060364600070094030f10031034652071200040e43c0c604401280c50700a43c2002c2c0011045034040c8283e40b032082d08020103200003005001000301c0c1d944020454030303038040e0501c110030220781501142d0b8441e03000b444a01d1410760038840c010309803840d95a051842521240003a0071815408026070f480304500f4200032440e40340160040c1d81e07070142130f04441c6000410ac204014207400340000322524100a4082d550820400d4003000d44034032422203055080340e070256007850300d54800d600920130041e4080b00003c0c04800007110118680c440c0701d03407400c0040c0100070700c52010b00910448004004496080101d41120800b0810a54030b240b14166041c2c1d00c0f80004840c1d80c580059070f070307000350300400440d82c83c0742924201100303000f5401b85400042c5854408101c281c044c0070002d01030081a2504c01d056881c558 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 660896366 1250 660895116 660895121
    0x1b030307020910030c27050103120c0f15060f080604030f120f02030109050a0c2a11030703060204030516050f061602040908041d010b0706020a14070c09060b07110103 73
    0x504248100f801101c000001c5071514a07035002508440d07030005000300d1401803030f411009164040712983c1d40b80100420001d501c1c5403600c1c2c501000c50400300001e00160070842080d14086c600070b006404500812021080640e0100007a00e402072807000c040e903101c680700b903034501003101c000f00440c641c180b0b401c902d00d01aa0550391506c0030102c002c0740d070040d142031081c1682c00a030b00403800ca680315400d0240c04c0d41140200000c0481c50318059030350421130282c038040c03d20f0024a00302c8841940003c0c006000c0c0c2c0c2d10b1203815141c006801c03103200954a00d8188029031061100752000d00986d0100c140214600007004111a00200400c0001800404200466002262407004411b0019002d40140c9440c090389200c103020b00c44141d100d901d4520591407291020440104802007a001446000e0012059031007203904402c0041c0c45104040069030090124003022000040c0030403588100b100035500380302500c1c078600c0240301456440101c61803500030104000c085850261450406510a9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 660897616 1250 660896366 660896371
    0x90503120907150309020a08150a05130605041101080f0c041a09040c0c1209030b0406180b0420040506060901110120130b0705030301060806010903061d1b0303070209 73
    0x1800b502c1c881d664a05503400003408a0262101003519603031100254600001003800034010000580100302c0240030100795440020500c805080d615000f06003001882004180e01640c00078040209041a01b8112200c210601e8600d0001e000764000500b416510421240601020342d403180c1090b04004249402d44101d40b2411024482842070b0325003561a409641d0002d0103d0329000d2141003181040e21401030080400c0c802c4c0a03058004000040502d00c078260300640208000a21013003e0131180d00f29212040041d203500ca1407410310003400000c0c00b0011b51501c162140c00c84a40b202c0085c803081d10b900310f458a5101009004c403541d15402603514032402d284c0100000b4079800d510047d08038a4000240400d001800450502c1180000c1d00c14607000c1c210010040b0304049540da21199603210501481c4108481000070a1059008a4050015660101040c07001c0c07000341e0042c4d011000c00f01034441c2d01c0c0c80f0340c0103e5000d01d002440c822220142c05405146041082e40a220070020003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 660898866 1250 660897616 660897631
    0x308090f03030915070510110310050105040602070b0906040317030703060905010b070f0311060c040801110327030904110c0c10050409200d0b01021029030307020901140a0909050312 80
    0x6098450413041f65074803501c9140f20f040325006440381803c01010a24100030b40042c2d060080410052015940000341542102d070039001c2c0313558500c0310070041041400795901c010080380e206042d48150302000390240d8842c10310b981d000c01905647d807114a003074840a01c500b0300b013003204010070404940380b800c0d180d02060003806c010380d6000214501510305982140c2041c0150000b16080c04418401c0c0540803101d1568001d403811030411004903100344c40060a11800c880b614000d21902050910584200e14802082088410000c81203080f1980c050f00c00201a80285840d90040c0d00e0011210f00501c0c4090381d94034201824402c6c42c10041c00c5140c442103007880140e07510905035070100d0041c06000c41428010500242d1007002919180c001442c41c1040c3c0c1c20b00009440c014010450666000c450800420642113040c002c242184a90030011f500914100004104803005056038000604250303103801d503c50b03079100190308903100340d81c0003002c5400400030020710010864505401410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 660900116 1250 660898866 660898873
    0x304080306011e090810050606180102101416080412032715050f0103110915040203090a030207090b301b040c0309030e1005130308090f030309150705 66
    0x604003032003c2800595030301c94000603008a000d214401c000e00083c41c10f00040c00060009003840000a141ca0048200f842d5051a104510205c0ca81c8200b15a0440d008194810068012a00d8400b9005003044944540c40341403010096400741c891141244202c0d00704241c1c130f0300b65503144ca0480203010112228241c07001c900c1d851304541200303400c4407402030f4800d008031144c0502ca80c103a80c00750342c0d0040c8038002141c000c40040010903804001220b4044c3d00712055032aa5680354049080c6160300b0ad8901c1e00300e4400700812031240b03000180074844601940803907242c40c0d034401c055000d503008100c1a540203010315815000c2071b1302564500d101e08207012032144405040d801d0142c40c0845201e6450501025031050750050304162003000c001e400c00c1c1c07900744502c440700d48018010180740c00a1a014403a41079080c5e0b0214854001e840800e90900071003088142d590a0500c502e8111113000ca201e000000c0d461101c5290000c115075003114041c04120750844240b8a04a554104490654a41c003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 660901366 1250 660900116 660900137
    0x6091207020f0f190e15090402031002031906170106080303070e09042d06110a09150c050f0c090f010e0126070e1f0b0315040f020406030501061103040b030408030601 73
    0x411110150f0043d0a948905d84810302e8000c5248070040340040d800c0d0b00070b140c12000c1c48096100402c0c6018801354420700541e681c1c44800064000b84010760b2a14005803509102060320002040042d40745500030700207009403515003a05503207a1205480003c080b42c0c1d5580d182059041009080750f1082c028015000d5010342465010500101c84010b85c001c806101801c508200c21031041856000c0d07030030225410b09a00020140010655004d1034180c103100c10b070029540e51285d00a070b03207907a03482016980d640c07081d10725040d56103003242c0c4400d01c618011000a50301904000b000c80c100c03071809030792810756443c10660f0b03005501c04102c6a20703116031000811000810411140b4000c00c41c8a1102c80340f480c003001d911440d41950940900e01072915841004160110b03000d481d00082203080c01e06401c0307001d00c00100200800004404141c2c0040340008d02c058241d072195040310102d440b2010a0003080c00c00300c1d200d00c103030f00816244800610100340420381701805107030301200604040d0302c00f0703 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 660902616 1250 660901366 660901399
    0x91a042d0618050303030705070203060f09060a05040519051e0105130201030b031e03030417070330050a020309012a0e01030b040e010e010b101704020a0f060206091207020f0f 77
    0x50741b045458101080000982c4411070804000e195402200e413611903d680c100346850a03110310014028200c0c0e25100d01c0400d050000a004032240c0d1003905400c50007090a5280c19502c070503050f10802c144c9040c09402403200305040c0070302c41c440c100c001e8451607580c00540c0154020102460080c0d018401c481900840e0442d0048a000d9400000021030711b0b441c01d464150307000c0d0001102000b4080c0c003031148000080c0c12001044103a420603801014008008d03845000d20701188510604440c00d0000f8040b072240b05178000d5004038081e000034000d9a09424041404070406045084200340910440e9212031144445030b000c4101494040303075000d161000103040d58001d0500302c99076551200d4607809a90300b40304241d0051019a94804c0c5010001006010501c3d0181c80c40c000b03040c100005411940c84049000141c4010020510500e4031140025680c41048413500b94501c070b0014040c05102064056651a950040c003001005808100340700490280001c12500b02c900104c4041380c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 660903866 1250 660902616 660902623
    0x40e03090d03090e1023030f010207030503010f1706070810050a0303030f0c031505061c0203040311070b030f01060c170301080307110604050102061303091a042d06180503 75
    0xc1400ba560315141c00342440380e02808403d019144101c1c15413009001c2007000c42d5152110040403c8400105051080c0c0c80401d00f00714108003030414a510005c3d20304105500500076506807071014800000c4240c82c2d52200503420a05e264100705a80404001941c1600c00c0200c198001100c00c1d0f0030104658a8000c608000295042140825140c00004d03a24490364441d25480321020b140a00000e011714040c40400d4a1a02a5500400c0009040f400c00c50146141d0710090100100071035507032400b410010240d46442803209190302480c84005a2440b0403000d89001d45486442e81036240d180c0482039484880d8500102c542000440c049015406060090b5000308003e902842e50ba91081c505200510014140c00d445550203000a000503640084c50301e0b0300c411b07207a1008842e20301d2400e00740d40d2410554800c010502e003d41213120300046103009441201c000c000c0c50240c0c4c0d030b8200011340c1071182e2005800d9004441c00010000148141c8000d0601503200c6040f03038449482c1c0d40030904 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 660905116 1250 660903866 660903889
    0xd0303060b03070309150506210f06180c010309080a0f020309090109020306180618180a110a05010203070c0302060f07051009110906150d091a070e060a1d0f030d030e01050a090c05040e0309 83
    0x103518425080803c4031330350034843e04040c00b10910f02040729007901c2c0e990300654000e0350031040411400b42c04984941d8020411501c0c0200001d00c84282582c3d81d035028000707540b044514a0240400b035409850740560a0802d17402003000501e8910601660b00f000311000720002d0240205a40c01c8203640c94401d0705110312420b0340c0c05041c42e91040c840b404188038040f680307a8007050440d481041380b8004a061f800c042025250304032881e66550300a0303007007020380c3d001d01d1501810f0390050480541c9081078561105842030721410305454050700500820250003011030702c090b08540c0d010104564601e900c4000c2c4140100310000040d450b0303180c2c4030450301498511403004200044800e220302c03240c10214403944032408503501d500c3e264100b00000c24840d074400381d4076003890f4503200b10180b659440280481940b0050105c8100003000c0000030040c1001a0b28814075520741008284d49400c1b6005146201d600000d008000b2454a014403004003400200a62640414010b803c19030f0b89400340c002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 660906366 1250 660905116 660905131
    0xc050d0507031e020303031b09031b03060705030f161413030c080102031b090114034f02030106210b0109060e060d0303060b03070309150506210f06 65
    0x160703040c214a0b04a035810300041c1d02030b41a6100c0d224010040c0d40001c1100c0d40f261840c03040e580303038118141154005010f04104d55070b141c06000506841c001c01a40100101d02c070440441c1e9641e05c0300c10b07083d6664401980c0651040c141c0c500000c0651041c03655040c410840c901d05440f03440b02e1b4084840c8130341c20840140b011081116010000c1c429070a0303d00c4003504015000314518103096172042c60f0881082401e03041a480400d404401b6070160350b038110016540d07518141c1d84d29085480016100d41741c000001188180341c504041910403844496100141c03040710025441008190405000c04100480c1d041d0f40300c84010030030a00d2840315001021700120303030002c1c40440303103881c0c805607005800903c000e5190850421140110030041038014000382d03200c185802c014242103000d880687c00501050500200b4807000d40e03416440094002c2c01000704503025040400e810060340d00c1500d003264480d03041d50300d006484140748800d000700082c11007111644409840060b040c840c0445081 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 660907616 1250 660906366 660906373
    0x114010b04150917030723060403230d0b0102011a030d031d010f02071a15010806012601091103040b010302150c0a0318060e030a031809050109240f030b040c050d05 72
    0x641c10030507861f2903c0c210300540702d00507107400214142e003556414000d01c054100811030450200c0451200e98040b11800c1641500d03540e00c0c0c41200c02d4001c0c0c000081c0541c0191b01c3c00740103408002d1414031200e034a0390005c000d4103c0211410040b0302800c1880807402010740c205044440910b8244200300c003034204101c0240c0c0f54030003420001c07044052030550601511140040026900000652407a41042420144140e03261170004032002580b01c20148c00c1d001c814052004201281700c0d08604076600325809005074032100010247c03074041580c0050032047e01000510061a240c03180620301710501942d103051600181040b0710b07046d20550203501280046242000c0c4040480d03084014250030f0410280007001c0502090350b50358403220180401c08211200490340400200100080c400c201d818001943c4807006000248160b640c40300790300c4d002c0100c19020341c035110611011102840403140e2207600c0c5850f641d00c010030003802104c0003044640c000c155591503103401040140610001c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 660908866 1250 660907616 660907627
    0x1e0f110f071a0c060106201006030b132001020109050709090204140c1206061308071d070c0f020f1302030a060801200d110a110114010b0415091703 65
    0x310b0320080e582040c058003211082100c00c40848000408504441c503e01d003c17454040581d030f000906080124007010240a1028001c0742c0303420315000780050340e0080000740d9064403601e000b00d2100003440303030081c510007882c58203250301e2030ba00912801e491410300021a800d039081c0e46017402d00c80e45400076190a90340c0d203012015428070b881258143c44072030f455141e203414600302c0b04005010b00395402c00342045640c0024030f203858010640e00130f10036141070f00c59030503142c92009407544001d01500803000c100702c02c0c0030b070051202c0102030700402064840c1d001440e065103400b210b40701180f074240e8000a52010031141c1d516400702d1844680000d2400513100e04100b07540d2020307100c8030b80c03084061b40c4c10851342074030707408082d140c00e0311891041e601c099851a00c030502d40080c0c9050040c4103040c19001c0780e809542c5400510740e014070b25030b80c4020010000b0801d5030404003031081c0901941c02c00c0600040c0070310b1071485507640c003100d000d00700714000b5681c501000c10320110215605186070004110b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 660910116 1250 660908866 660908879
    0x11d04050c0318012007020109080f01091502131703070506010e010305010b030c03031b010f0603080306090708070c021003450b060409020a0b0304030215071e0f110f07 74
    0x50b0f50342040c90840092155441400c8514981e107600e0000500c0490002007241c1160302980301c08005103109010344000740400c1010074000d0014510560b4002d18503007900d81c4801c800c1c402c030390075001420b40c54a1000c1c10640c0145035401d100d500b54855100c10801c0c0b40200e001002914000c00c003001400c143d960462602c41c2c255000c00d400d080c020383c421300202ca190740c4d02100345e0b10009001c01c040704401800400480c05000c0205e020380c10141340070408814444403000443c41000c082d90801f1458075400400c880c22082143d228000410709041c6000616061420900c10740c881c0c40c0109840c260700c500e46440d90354079072000c4402c4a1940b08120411012040c00d00207410b040590f45030121540ca680e1742c080001442144683e994901c07250856440d41d0364407000c6d100010240c0d032079107070600d4040d40e580c0380008900191150034002640d5217126402d424140d504030000d02c40040e82a207410f40d4030408206150003404018511994208420003107800c2040c1650010440d5618020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 660911366 1250 660910116 660910141
    0x80403020f0129010f0e0108060d0b04060b01180605030105010e0414150102071d01032a06050909060906011707031112160810061b0c080d02151302011d04050c03 71
    0x103c00307042c414140c405001c0560421050012040c080c00c2042d100d940e0000000e0700103800d1080100050200d805000900c9816070200c8410368081e21410f40c0c008540798038603103101b00e600c500f1000400402c01030003a5440707241221800c01020300041000003a2295070030322100d08940c0301c3c900001c0d00700060801d40e4104003040061001d4080ba0f60000c200e03074900d04641c04140006800c2844503c0e80c020a02c1a2034010700a82c1d00c40e00140000715242c0b20000c006074000e5146602c075099440214045140c02500310740a203405031101e130616620361540006a110040c0607205140c1e0b0f0300c50000d48540707200c0081814564081e80340c070440c5071588000008000c0314002c4400c1040703140030031038043c000702000400d0b100681041c1203404125403012110580f104801040c403003a45600040407400014152403044aa07000e40b000c101c4d18042c0d1074100e440c1261450200041ca492071405540102905001e10010307014022141d050000801e0540d002611050314401c400010000c0160029 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 660912616 1250 660911366 660911441
    0xc0f14011103010f03023a060e060601170604060e150405250c050c04110d0b040c091511010903020c032b120b10020303012102060406080403020f01 65
    0xc1c0461410b55040181c040300c0c14840e40002030280150aa9007105240c1c070804915228071203c006c01c484c4170490b005410080114401181e030700e410480716409412000c50310b00e00c260303410b0f541d9211000c0b26030304001c031440020f400079412994030710020400301004c501c058806e030442e4120f5840704042074180400c40300014491103070061130000c40c2085404440ba484a080403621702200e18508030b0074040e05000f40500701c1507100c1c0c9010001c0700071202d400702500b403603c0c4880040001a50040500098451400d1920300051910f1000c1c04441241403084d4800c21107880e2039003001880e100c1107802c5401402d4150056400760101440c81d00c1c00300035072000c1c041c02c0d44040d82c2091140f0110041503401c110454284101e55115444052596004125100c00144038003035600d0300b00c101940700e0780f003809030300c2e4400303e840c43c07182801c09601502c0c140594082c1c803852500d440c0170700032540c00c2e1025100310114043d550003a48220001d0080392001c01100c001c0154010021856000e00c0c02d04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 660913866 1250 660912616 660912641
    0x150f0807120f02210c09061b010626150a15030606030b1008070308030c03040f05060717090106120803040204110c010605040605041e0b1207060210180506010303030c0c0f1401 77
    0xc6904100b142c003203000541d0511b142c1607c613103464050b80100b40e0404584a0340c04c3c40c1c158608100000c040038485245041d10390081d480c0d03810500d0101a2076100e50324010b18003581402130000c101482c3c0380d94010064051050340810b151520303585ca040a69419a006868000072035080c001c42109012800d40200340792001010f90307500e950385002c401d000041450b0090140440040c0078048401c3c4080e00982e4441d01380c0784c007481c0510001d043c51031141242c6000c40c00030bc0c0000d00c141c0c414424442a602150220f407282900ca50322a0b2155000500407030f0041c0d2138490019101c08280c003d802c00d1b103900000414007500f00014481115129401144510b0900ca945121446665049403501164800114041e2840c030b0226424140380000385c0890f100e80400040c01035800325074802d509112420034800a54000002c6454001c6000c0c00340194003c1070040000a019900c081e000514904000503141c00b20713216502d00340032182c01501c04044000070702c440018207218503104840c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 660915116 1250 660913866 660913927
    0x1224021b010609180b0c0f04030b09010507020106060504090e031e04170303042d150207060b030a0c0e090a080d050f0619090b1801030f020a150f0807120f02 69
    0x4424000b40c03804160880580302800500101d10a000150107d588180101c081c40341e444c0d540c3e103401400c0c03100c121130420710780d441d000c0860300f43c034410b00400e070445400780d840314203103401c0000d9040102070340c02d6805003510040080b901040b66200d1408000260000c2043d196031600c0c25000389200b08000ca01400d030000c100704000184824041d4000300d8640111b44100861800e00040f070400f1444090440c1d080750684c0e001a034183d03001810260b104800501242e83e8034820300d5504c25860b06d000744040608841400140000040994800081e100301d400001c1c540c0c0f9040d03140d520540018035403a860f1010044000c5801c3c03060343e0800010768908952210008000c0902c00c101d0050184c0140c403040029030641c0d135090180004203a0307154503030903541c2d00d14001c9407a060b0600201d01a10318104000303030781415211040d08410b616142c00c60321181340d20701200c0b5042c0c02052503091203030030f038803846185501d482041201c0a01c0800185d550041c0d10510840c6501e09408076880007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 660916366 1250 660915116 660915131
    0x40e0f0105010c030e060d0906060f0f0b090108040203070f03032003162603010f06030c0c03020c01030c052a0f161202150706020301090c08011224021b010609 70
    0x340c0c4901c0f001481909464a030400314510000905284a005a0f00606504103203001d01070200a50012003100c0d813440b0740212007590340000011310940c6100f086050f01007403200d01041c0d4028400b0f50b40c068801015030344c400da2501c42003824040c2e60341082e0002181e212072154120072070114054500b4101000758188101c0f107682d25280d607004000286021a040344603110446460100816084403181c120703100e46c0c55032070030a481c0c2147d200d4840041d04004040d072100c1e02540b0041a06034065014000c40b08040300198090301c1a16000e60070440c04000d070688017580455000141c010100c84a61250381c009400340c80c142440a81c0c0c200d41d089178841030f0b0008520038018040399002600b5580c8014075000003a15401c114840d81941c00300050b001003000032941c0214140c0304a40f02c200309140031036500715010202401000c940061010b00f890204207040c85242448a0340705900e031b0703145010700b811301c01d980000030741e851403803100d03400c820700f0110a0248a0140c2281c400812502 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 660917616 1250 660916366 660916369
    0x6060103090525090c020c0910050d08090d06020f031b040501050403150b0a06090303020709090803071b0204060f1404140f0c0408030f0318011a040e0c090c040e0f0105 74
    0x2058000c43c1101220041d02c011401d00601020300d0005050410341003101c1c459800f0080c3d01d80ca80d0b001c18a110740302e00b20000b0080300000d40f03d10180d81020382084900d05079036440032f0b00c682c01103c506500542038004203000411a00040001801d8618031640701d04040384544015041e012200f600d8100500050055036802000d03102141d801c074048180d240781d01c134140e0f0f0080c41c00d5110300d900400e0800e80807800b04c1d04480b00c1c0b000c1324480d034200c40ca100c3e40c40600700c00312030030007100409400080010490b00b034070076403030050810066a903105004030b45a002908480d07440d031003121a605001e008000c01d500b0b0f001c0e000c01015050714107000c007003600d4003818001e14000b44682e40c102005000301c0c02105584e003d0300c0c003a00040341101d644070701d403c482c003009803c200e071201008440c0d0381b40174140103018018603501c4000485044581e001d0740e001c100241a0b50541c0c1690391082090802c540d0f039880c21154001c6c00366000c455070325401c001b948040944000c1070b111441d0384e81801000305 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 660918866 1250 660917616 660917623
    0x31903151403010c1119060905150108070905100e07030b0a17070801020712030e0304120501020301090e010902100e2b120c110907050c0114060a060207050906060c03070f06090203060601030905 85
    0x4850302c000f20050075691f2800300000e15508402410314402c000c04210301c11403d005890582e0f03141e0702160081030759014828207540e000c5a51a0150000c120200b10311981da4441582111040c05c010130049018004501064810391000c0307010302002a29103400e42081c4288009031050900075480c3c218143c0b01c03002c401618100003c100342e50391584c00600c4200380244c0c0c4c00381250040c0d40c02040b0503170620b00e010b50400c2c0610384c0260b190031130000c0c0c800c00520a283c1c071103a0140030b111402441001c15214081c40342c4da0a03400140e54494a920704680122007400104890700a030350704802402d0080218003100c01000600c807011039070001083c0a1b0f01d0403190720700304071861803455950340c3d000c0b07070075000c0c10074220b11039820100c400b90a10b105205c0c65108201c15a403c00b80c895817460101c0c3d903120144070316904031111001043c26804c109009190004c48181220f141c001d9640c0d907a4103115141c081030780c903543d9a40c049003c41c80e0501a82d03400a40902e0103106103c42912203a80307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 660920116 1250 660918866 660918883
    0x90212190605190305060114210708030a02060f0703050121020d0206160b07050307120510030f29070e06030601030e120a080f09031903151403010c11 66
    0x1020a00d88500d582030311200d0704404003030840074222607408912030160444208040c001240d20303001c2e19001050a0385500e83d9454000401001804d2208481860103501d81020504030745a0140c0d00c4003141900040000782220300b0385034002c0030301385081c00b40300b640d9600241c141820141803000421aa443d2503507020310f240c104203e14600c4040030b00c009001d8101c00500250402400700d0100d050301144c208005a16010f010442002c2d43c46520031034032407100b200d20301d000c40c5040950303940011040e4015a8401c600e0340010f20016100e40301c40212041000c001c8036440f1251449100424031441900c010140e140c6140c202400c0640010b0181c250350064070780603c0c0e004c4000b54041e0310070781280758001c483c081540c64111000710a25800da100d44e0000c00405e00344070109801c0c05855410030300c140743c5500598204500c03501c02200060140114100f015194441d038509910007640c094020115400710302111380b0802c0500d400c0d5100d20750380f6000d00c2440c148000c41c800c401b2a2004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 660921366 1250 660920116 660920131
    0x807121d0d171e1e0c07020f010305060108150a0305060109151203021c03140c03061521100e10031415010e18070806041412070609030311160c090212 66
    0x48480e503845100940c091442d0713031a410f4190031103060028030302000c001404034500a030380c954a8070b0b14517001503044e10000d40d0624001b03440c401c00181c90001084244203a90b20041520b5903156032920b5180c83c240003038000401ea02d0740c40315981d44645000c0350640c0140758050340c031101d0726a1a1000703501c8032070340410104504251260704002d00d2103a409003006400c60807a07031080c1d0900e800c2a0100f50421501e184c00b442400440320980110981a80d410111000d59800c0030141004160f064920181008520069001d00070501c1260841c1c818891803081140641452440c20403010700b100508803a8884c0d044004140c0030946460380d01415a10703201881001a00d600000c1c1480d45504200d14801c0c0c050140301040c101c9000c01c6581c0501d00a10b40326101214406840d900c3d110458140d000c0b00a0070400e00c000280da44c1c1080110034001e050004070a9074600b008000c540c0319204c5900c04009036000d110410107070210300c2c4042d242c00002107080103044920030b90061806049234 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 660922616 1250 660921366 660921421
    0x114160f050f0a0306140d02130902030c060c150105100e0409110303070303140109050f240901030302030c06071d04151e0807060f0807121d0d17 64
    0x12121540100202c03040844012105991403011103001401041e2a010300c40310721039510285d241350300c0d0401e4511000b540042002c40d1200e0903240b404000c0414480890f010702400c94119200d41e100300181c0000c2e591400034001d0312403d6032854005c05816001a232142c0295110100d5295100420313001c0401c0548000904c2880d078208803950104101209038117110010320360301059415003042d030010241c0080e0340729603600c0c0d20051060340c0c41103685170b018012203000207810b0001c50b0b00c40080121410072007100d007107480d800b0900c450b509801c10343c003590000942c0c07040c46404105a940c070051618000001e01c0c0c1750311a00403c0d008280c241071180d900c5a00441580c40038119241c01800c41140030413000203001d01c0d0100341c545c980301702042802521400a4001e0103042500d1022145a071004503a907244103080e6005000d5641906540d42c0e16072034000c0b590a01900380c14406507020081803e440d03440c400905460f569150300a80031280010b106034140311342c015a103c5111100c62 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 660923866 1250 660922616 660922637
    0x70c02010f090f150e040e0d120902060a090311010c02011b080c0f0c0a14130e0109050a061b090b0706090317190f200901121a03011416 60
    0x200d80c201400d070010591038800c40000101d55031075440c2110350904c2d640710560010b040204000484407044000400da1700704601a51859104605151099030300c22400a020300c000d8005c50750b25040218400c1c0030a40342c100900c10b1041954640c0e40c0c0718001d182c507c440000c00d41c0000d0a516100d0760f40c5185408a16841c41008498015209100c101c0d03001c5510008611088a40e180c61050350300380a0403098601107001d40015180070f5950300b020380611072a00241c0c00c504002e00d41100050744956907400040d0020340e040c4210340c2d07407500074000456046021552400342c000050042010700c00307115410003404000100b6102000d801c400005420304560609940a015400520040102c00401c01c90130701f6003507040d12658042d445007006200c801c80f00141c2140d4060030300c1c040101c3c1800c0050031040d42c2c030008000803103042c034012032030504580000c0195070805000d451622140603032200c081c14244148410142d49240d02c662a080c240f5103218103250031b5110340c2c10081c50121 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 660925116 1250 660923866 660923897
    0xa02090a0f09061a0307061d0f030109060501050901050a0e0a020a0504151124150112140a05060a030b0a05130209160905030304060906050d230405010c0503070c0201 73
    0x1c20540d4402481c41444000040c0c5400d000400c01c80b0340c140e1881950088440c0e40b4200011220251150768032901c00e071350150349060340101052080380e80c0c4890220300003026610700707024400410340326a9000c034481d41804100441c00d10160030042c011a082c000c00c0020000d0b4030240ea4210881003c0144d94600295048640748250340042704492180c0e1a08280d1961144042c50901461404e8948282202d01340500306817100410b010103607080404250a070821060310484007005040c2000131004020110003980c005156810940c0c4e200c00400c80c1051050050076486102212090000d03800c0d5614080b10400c05002c02034600d549400054000c4100c0303500300001a0020314ac441580350201c8002c146000f902c0300d11001071115400011181070000a940503211a512040a550300302003040380ca54220700101c0c03c1c5640c45030074181543ca101c04ca03003119a070804242b0441840c0c00d04189081d20610700c1044100b00007081003003071050b480712464800780d509181141b0600760000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 660926366 1250 660925116 660925121
    0x30a090909110607082104020d0201200607030b18060306010b180604090e16030206030c0a231b03040e180c040e03030a0c051e16150207020108011202030a02090a 71
    0x2c1445400034800a081c006100201014000e43e4442041814550060504203801e520701510001e4024500760a41d0005600038082000c50701d11814148001d035400750840d900c0c0020544540d008641d0742c2d0030303404160800300080d48100c00641c00c4211181461004a0f84d5180144158080100e003ca4680f403400d1b5025241c000b11a0002c01040e12070780c542c40414014480c1381102c802510807001d03984454102c0c400d5110480350010520b905542e42d004c00c04081c0c1c0c1c0640a6181089a51412030f981c4104d50a0011541c807103103040191540c96090701da00b41c1c40a40d07003d01300603030302c00d020406c2920b20270000e80e41c1c4050455031942103504203400c254a0448125541540281406028004240300001640c0302d1410030401388808400800b060b2070521480a00c20b007002c503d02c00031540428101f00030b0074038032400b4810045607045038650b034020000920100822a0300000c003401550b81c40083c40e03006d042c0440051508180960019503110b02035400240218207260019075a48402da = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 660927616 1250 660926366 660926393
    0x3150c0412080c012909150402210114190e011e0302040221070509031c090e040302070306050f01050612090c130f05070302160b060627010f02030a090909 68
    0x178081e600c401811000c20703036050094110b00c10355400b034110b502e1800302c1080d03000f00c0e64a0089104401c8801c01d000180d44405d0517100d404543c03101000810680d00c507840d00a103c0009020184810107082142e0300100010300380741514042c4003400725081079071001d0304640f00c81d0103070420215180700c200d00120311a440030354800d10210703003661a0300c210b0708055064119a0a00381041e9a10201a565070048510a070741607846080c1c40c40840168a1024002b14190b09000c46000d664003c0824020341c00c90301200140c005510820800c038032802010f4010903003507054421b42d8144004510b590140c10525070510140340003140c4c034400700340700c03100201c2000340c1502461180e504000c006004c80070555912103240c80009000c141c0700c6e00c2595211100300102c0120b00400b912200701e0320402410140d4404010800d4400d00d03000d0002d01d0020601ca0a01485940071403400540a00c54100d10841550000c01204200560103030042055808003803001038101224280496803203e407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 660928866 1250 660927616 660927637
    0x504020135010b0304020f12030405040f0905030f1b011a0108041401060f0806060d11090a060e0403270b0307270303030203160e150a030b03070303030b03150c041208 73
    0x100000c10f214014800031445036000b65101112411448140540e60701c108031040c14540060000348210314082e00140343e2244800700218101d50395466035403c55001e48620614000300146050258190319086c0035502040002041444948004201507030102c0c0001030411420b80c0000f0b0800003101d00e1175801c40202d000800006031200425030041c40c003802008114401c034400034046184c00d0862140850303202201600f00d0340300d0000c2c8110200b0117401403014a8580d036005c10c0c40145824020311841c0a5540c0360002e9044d40d50801321040c08044840800350241c00c02c7c000c4000c0c0c882101d801c07020600d020700ca0040720f4141d64100fa0b02059040041c58592100002450340c1500030318020602a8100500c51840089c103441c88031100f01c04a40000b06034900100c840304400161808503040e003008621500e14800187c04e18016130030840200b130362064030100c0350804000f0880b03011000440070141d810048100712641c0911f12030028401c0316030620208210100045d1101d1000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 660930116 1250 660928866 660928967
    0xa03020f1b0d030e0610050f01050d0f091203050412081008120301060207060f02150703020d050f090c1507020f0303040f0e09120f0306010c020a1503020909060405040201 75
    0x3001480d842d101c0c0e0050500c800000d06003082614898000301e01240503400d01c4455210700d40c544824480c00c030035001455410310030b007800710040400c402d02448a48001d080d50014a0f001a403400c44003505107969000f081600d0413080000048078207444400002d0300c0d0400c040e1741e0f07662031407601901d00c440e00409000c3c0580d180c8900c1e00b0716070f0380181d03040e00d0b2550259801e00d9150141110040441200d0000580c81400103800d00c00d00d10040c3c3d900427030b05250241c035142100d1080070a488003914030601b0408100e08002c1801e5080c005410025400c6910302d410380c40c502c9548007203000d542c501a00c100014041c1c11000d59040003241c0052420301c00003c0a41d5640400c41100d01c030132240d000d41c502440321401140c0003418101d035a200b101c00f190509580343e6000442c1c148811040032030b008000030074045400d001e400001030300c440f503540d400741e682c19980c0203000e001c14024005a000b1030404041c440180c2c2c0101007800810703030b0380c0c400211425200421000300c549003010700c842500c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 660931366 1250 660930116 660930157
    0x1a0406110a0e0a0501020f033004050a1205391504030311030601080411013609050402090f090a150b0907020a0b07050703050405041113090b060a03020f 67
    0x3070b0011184400541d00726410032203542d50b80c0042e62101c00c0c0c03807201c28803034200304800f40b0004070f90403001903440c4903440341242400b02d0201920754414189d6041d110703a0700c00301c0310500700304140142c03c074904000d10300305091110743c40c01800111098841e40440422008a02c04010740c0e04803005015440002110540003104106642c5003400350783c15000a1300f040580e0600c00244000c5030300075072042c3d540c0411542c6139102c40c401e04908481003410000d83e4190007481034009070110194071164004240c4403100c00c020030f0700b080550352061f581c1609180030480036a407446041d030350088046210000541c0c40e500540d0a085541c00c0003000500041e18401c45480658010074010100755a07281c00c0e034466200c140d0365030070316080082a6020035030005054a2052005d00710302840b030704186003040d03160000503040d10561b0001c071a01240200b072020450111794030200040222400410100d01c1f003501042192041128078014150009405150726140700100c400601f203000714040302a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 660932616 1250 660931366 660931387
    0x1805061003021c080a1b020a090507030e0f0c0906011b060515030615100203090301021c0623010f1e08010501020d0203180f24251a040611 61
    0x241441d000581c05080302a05030759281420000e100c6050f07400101d6181811240038044070030308406100b0100d40b52100c114040141c0b00c100c041405000b0240000c200c601d80080010100d600703404070003620740d02c500300d903000f4481c02040b503489401094501c003140e6510400181e514003030101044145902d980c2c0304406000c0369074042070141910b03400f80d03444441403004250ba5060103407129416588030b0501854a031070310342c0c1588220021801a28101911000006d00b207802c00417418004e4080502e5021501071039102d81c6002d400c1c04c001103500200710782c0c4509105840e00a40a061042841e0048881c501a5481d00c2c5000d900030041c5903d82c10510340103107020400c0c86164007520800040171041070000c419a003a902a01070010014003030801000200b440711102141c0000c20000e401000008810b4031040940741160950b41d103010b01c68540c2d2010b0941900e0307804403d0703001c20600004901212040080e18550041c456548882c00c020005114400e0046107d210005561084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 660933866 1250 660932616 660932641
    0x91110091502030d36030e030307050c030105013f1707020102010b060405130902060903030c060f011d06040228030c030f0b0d140109060c05030a0e1c03180506 70
    0x110310580b4140b00b0501015054030030103141c002c4086205c2c0407007000c20b180740f80d245c94410400b03002e4500300d40101d105802103411076001031002d846540142d4141e0b49541024058a401040310315914220180548903441801d504401c4541e508c201c401c4402e121591144100c0d14040e8220114403060001010b00010943c4403c0e0100d025508180b1160381d1442c2400c10742c3c0c201e03140030703140401001c0c44030b12110041c240030344120b0703101700c1c240000e1b1002d072400c001610040d4000d070010085801d002c07090000514050340003030b0b49800a0b08901c82ca13502c5107200342e5001079050b1000b584503001c0d0600022221143c1d190038030313030101d04440d40604691603081400b0418083e14204070303a220b591142d405560b68194642e40041e0311030f41c000000354068030009041c08000d0300000b43d03c101552040240c0c0c4500882c40006200030042c0000e200e01c92040c2c01c1655254802002071580120a002032031303803030030101010b15aa4242c40901c0600d1640b114015544c400c0a45038140f403c030119100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 660935116 1250 660933866 660933877
    0x20715050a021e07090c0512040f0515090c0d050f0f0601150309170a1407080406110f2d100c030b06070b15060d0e0a1509111009150203 60
    0x1031180c0740c006051610031112035002400154080d101c40c42c01d01c8817003c060540c2034005010400c04210001020f10441540d500136489400035410341104c030300b001c5190150440100c0d0400344d561040c007045620000f10b880c407c0c1c030207403a4081491014102070b401c1c0000ca00c05800381d800f4008940c440040d021803401d0507204d0103016030a69640c203c40840480e04031110050044150400d8400742c0e500200c00341c01049050314020b14036465000186d8440d421400040b0355801c4041010310441d504405007503144600385000305010940c404045a5440041d41200b01c08441c94030764441a90700d81c40590121340da45000c850046c004034010300c0041410340c0c00c5000203454031640342e10a01d05203045415458000e0308035410340d00c5400409040401b91040e580d031003001003000244046050144590708641d0038040d04658600c0d05051010380d540c2505919001e15040e8150300050074100e07401d02e4000706580c035406500d1417174403e0f100907036a500804141160101d4641845a00200400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 660936366 1250 660935116 660935137
    0x604030602190f090e150604120302010605210a030e280f080f030409020a02160311090604051b0c16080a0c21060902010e13020423150a02071505 64
    0x1a0f2442c3e48400407a9500050700502000c4650b040108019500d92072881225400040c6003500c0c0a0343c481082002c005100d00450250751030301805c200c103190000108180c0011905250111b011512007183c4403164030700018103000845204152645903038629000701c00c80c01c40800c00281c00d02c4001e102c0307242039125007445c5214519010036400c80c040b1381c0d9541c00c212030006608050030000194040e4000d60045021403003007240c105404040800075400a60040d41d1035050590440b051101c0041c004151600503401d00050000d44260140146040030880c04c00c079486030340c0100a58140405d001c0d003a03d0015640c0c0001c00c00700d8011035400140741c820789204481542c2c50840c0040130704801031003055100000380d0400070030792070341054101910500d40000c003808840005403042000c501828011507002c05c040c405c9600410700301040038846130406413540c0700b240006a4003500b400c011070001401080114030f0314000c00654000c0e00103040025038070404490000e10030f812015019 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 660937616 1250 660936366 660936377
    0x60c110402030a021b12041512110d0b030c0603011a07020a0914130c1202040f0c110115080c0d1407060c0606120f080a0e030304170111180d02060403060219 69
    0x185401700250103003078103190841c000c3c1403903d0701000d409440007080303400003070002118040210700031500ca1542c851714141c0b90f054880401c020003030122003400405600a5104010520180e9035130010b07603044032041102010340480c00b0351704a066000c2e03040b00030b4001072040c0c008106100385801507580c01e0b003440e82d01301440d0b4038194925849113481e840a445004014000d01c642401107407910f10719400903102240380f821280141d000c43d803000d142000040c664010002c010942806003012001c2c440e00507290307150234854256165150841c0140c0710ba054500d0f15400c000c80314015050000e502c8082e035414598501010381fa01445400440d58245840d00c081601201811805a4a50001704610b008038043d9241e84e1180e0100400c102402152158440300d40e4003000240b014201048507980c003150361030289401e680d064105a00012070502c4030128456011000ba050940103c68501e0110200d001041c003e205a81000d80554000101c0078400c00070390310340b00c034540e0035a50781 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 660938866 1250 660937616 660937657
    0x10c0b0a0b0a0b0705240f040b04060912020c01090603092a030f24060b030f070905030a080d1407021009021507110a091e09110603010806010608070504060504060c110402030a02 78
    0x140d5250880e0310016811f20000400c002c41c440312413499220b40300307280000c1e88075239640700c0d4249506006e0850005a008065031078195a000800c0001084142014000e2882ca992003d900d00c008a12140064178020740d81030b0f850711507004180080d60007016030200002c460501e04044100e03040b0601091201d201038040e60f9095203d06011070340b01000e298210307210700c0ca6581c51000c02600d02401c1001001001c2055503050041c503046500c103651882e60796220412010940320382400325040c03a0100000c0061054002c1180030001441410000c0d40c00c203280300003400c038544510b40070405080410348004200d8000c0940c481508112407000c03200f0340d502c070f001d0144e506e42d02c00140c400390b52500035510044550860501c0070f108030510141d0707410714404620f0b150426841040141d2082004200150700000e200f41c0180051402601c0e0609080018102d4800c9100340700400c0030141129080c028100c14860f600c0d40e00520640d600e00384818090042c1d04400c8516500c0c00043e40c6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 660940116 1250 660938866 660938923
    0x110405090609010513030503061909020c0c030c03010216080c031c050402130b0307090e030d02071b0f05061b010f090302031804050112140708010e0714010c0b0a0b0a0b0705 76
    0x134034101c1d050340751f980d6078030b941e5803a030502070800000304420300c00185582012680d0b920301e0000c0c11f980710b248401402c095050038100743ca412138031041540a6481000140035001090304a4800c1c250043c40302555044055030052441c858115802217900710012801700c030000036002079000d58001c8070302c3c05c10003140c80181300c210f03548110910340c1680104000c104441ca180c0012810401c1c000c10b40c0c0c14030040c071211a09036441108100c55845500e010300406070040c2080f48050048410f1034110503042901041c23480c0b040c00c5452588030102d0554003000030094003d180892280c03070302802803411500d401780d542c0e005141810300c003008840e100d2200e42030900c01c007412540101a4074172018a10740301c3d0a1a80c40c06c0b0411180380c02804030108850070240220f0240000344030041a40310300d0802410300090511542d0b5040021045240000c5140107a040350405c484000000701618a000000c402c1c0101e90b00070180c0700b40114032007044c8240800d10701500401d2400302e4421859101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 660941366 1250 660940116 660940141
    0x118091a010f0e21030d0b090c0705192f0307170303010927210507080901080a150e0109050f010302060d020705011d1e1f05041104050906090105 64
    0x88a1400103448440c3c0306240f443c000050180340490740d40440401c0c1075a41000d0304540c02042c085c00380c00d0311402d04400364204a09603e40c000c0c00e404529017000070594403a500c42d69803a042c1c964066461a150b070a000c8100d4084004064076005890309000101c010540142058140341c401c2c001d10708000b81c0010750348806041c00c400303000610725581c2040d408000074002c00f9400d04680700488440a10b00c11a10b01d4804000e00079007000240c1000000b441500c41c45641d240000c00405000100c00201e0200c2520300c008800d003091400c50780d802c0a420b00915a181c00044068204080010240090030505050799a544800d001ca0781c0c6440c550407000d0001e1100940003d0300300540711100126070302518400d0311480010428400345c2d103140c203000d506d91901c244160045041110100d0b04030351807501041000c005082074508406404d011062100201c0d84403984030301c0010700300810214407802a9200a01c00c008074205982c0c05907803a03104490048030781d071070000801d41119400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 660942616 1250 660941366 660941387
    0x30b01020a03080408040b280e06180d050304061d0a080a0f08040e01061d090c03010b070609020414040201092111010210240f03120e0118091a01 64
    0x1a0001d0881d14403694044491850040c003d5170140c0c000d01001c00c152050a0040c82014240c2c107002300780c501040c0710790300081e1116502405010190300032141644031401900c1210140c00901c20355840580042a009502c07000d0013071640c00001400704172160041c440359031025424861407014080c2c4801d003c074620040c06514041d5000b100c0041c005402401418940c0344140300160405a44450920140c0020303040f03140841d040204441003000c2600101041d0102150880000c0c00c001410111512040c084e141016400042c100b09003c0c45401c0546a030354081d1003004001240340031180303409803e0b00c0c120300250a4403c0007d07102102c207003817401703070040c48d0421101c00003599071a0b41480100c1c84039415401080d64a21101529106030404104441400021380040928403038030f140b001d030804d4507908200d54041c8042421580c00d252020030318285074040c2040710740180c42d90403488210040d425449800880c09200c540c0000c81040c001070002c1040c868003900540c0d5400c0003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 660943866 1250 660942616 660942619
    0x10f050603091e0a1e06230105040c26040606050d03020d0f0c0b130302010e0f030f0c010914010c14070b04020f010516030801080c030d1d0a0906140f01030b 69
    0x1014000c1006419480350f420300420311000c44810b58800c2e5100c1500c200a40448003041108118480c18000d103402004200711142d40f00281007800741c0e8503104040c6e418000c0d24020703640c43c14a08646d5000c0e24802c03d0720340100c1400c881c84150302004c907901403c1200e0844515003048070009881c2000605003140540c1500130b010000310304d05040f59038010241100d81009480c02c000700110382ca00a5040c002d600041210441096504001c1e00752809042001010380c02010103140c41400807069070f1556469001807a5a0109685018054800100040d01040001c82056010841580305001440392038135008a101102105900349000fa20b40203080004900f0000380103180081c1100d58410050411506004044000d10441142e06008074041031140005100250080010200082003103005105403000303284000c04100260301000d0701c003c44410010b006550302d01c0d00201505444404000d019918031414000c078a86000c0c0d0b50090003000706e07580c0503500c20701800c00443d40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 660945116 1250 660943866 660943873
    0x10f06150512071101060504060801020a020114010b1e0c0d0207030c0603061206090303060b0c0f0106080c06070b18030d091a090d0e012d110a12050d0b0406090203010f05060309 78
    0x441d20350580f2802c1304000b070410255603d000226a545e01c0340302c1c0c07401030280080016281c054081000e821210316903c4001c0c800500740c01003190440d03201c2180d1003002c1c42500341e0000fa140b0a107413180c60041d8502859540206003501c0700007a4002071210460b4000c08484c1c0f580e43d230764001901110b000b40500c00c0b40c0710441202070003042a80c0c00c0005490b05c20b00e00060f903550380302d94203070054100a0301d02510f5005000a990901801d000d000083c14034080039002c16a4503400041a51144010040040720f9190019102d26403c0080744002e880140070780c0da84e005004900801810742400455034180347e491301c101c1d110804118144240035102c01072070701c0350842000b6186000303c01c001e00e0412060780048ca895501141a0a044a4908211680024220310060302c80414999001c5c019840b1101000110782c120320400f44a41c024141655108d907480002c5000d00310440005800600b401d20000da4110303c0c2d401141280c1c1c0c25140008010b4490007003102c1c6120170340c1c49641079031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 660946366 1250 660945116 660945121
    0x331150c03030e100903030f0f0506030d0f090f030305040603051614161401051b0a08010306090215070c0602010f0c0e10031b08071b0f150608010f06150512 69
    0x1c0c000c1d8408003c01582108603a0854048004501541e00c1d681040740080d40318100391540000d00d004400f049900f42205000c94035151000c603540c0c00201e244001005140f04e15820114002c1c0c14000141c090080c0760000e41b42c807401c018003641e00601c2184006845c00c0300040d800c004616000b05250075643c1c1c0c0340d040c080c3c81c121b1021142c11201c0700b03421030b4900c4d1036402d0000d882d42c0300c040c41c038000c0e03c0b00114292a01c0c0504a0020392020b11003c2410010481901010307400180641035031703805000090441214000b0a8460341d0003500d01c00342d56000101841031000200c4420308a43c3c081d80240508102106d100c8140d0b268884c04c80040b45903041099610b26094101d04001c81441c40c000031030111a080c410b00055519103071601048142e0140070b0050703807218103884034414444440b07019a0481d0b031030320a0524540f50151165080d5001c0f20303540d07101034110074010600c0a009010b4003106203010401050548607580d42c01017545051f02c810781c05074050f10340f00ca1003401006110b9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 660947616 1250 660946366 660946373
    0x151b0309110f0f0910120309080c0105040608160e04051305011b051b0118030507060f150504020304031206140f030a1a1906030809040e07080c0f030331150c 69
    0x1030601411801c000c2464843c0890f0107071b1144c00c210030070340c000d5a500e0341052424581a081030500d00d259810000100002d1040ba90030040c1580c0001640e0408010500c10540c2190b43c08081c55030164420b0800f002d100310f00c0c41190108141e54001d0008002d800328400f09514040e4180c8200701c0429400d20900c1c940059141c011481c03900d00b28000726032003074a40402524900c0013182100464030110b02c138024400d05100f60b010030744c02402c04001e014520942c1c90301641c81407203400d1244e130f0000002001c02d845030745c007400400303008441440744949807039480320540c4000c041070380100c00e01c9807646c10a24000076540c403840d0708444a550303801248410811381c6030005200f100700d098914007420038445c0b03500c1000011401404407545550149042100340c41960000e440c0651083d1400d0240d8900030a403102c038108200e510181112486000c02d0440c010420680c0f1028000500440581240d84002c0200030403549845601c41d00d4401d1211000c164004000001d1815010fa4000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 660948866 1250 660947616 660947629
    0x150903031303061407120e0109080409022d0403080a0e12010e0d0513060323070806011d091906090509031806040e0c0d110a031a030d0507151b0309110f0f 68
    0x100700e12040082000c41052b03c071554940c1c030552000312025800900481c01e00d401c06a161515540e075a407201c1110800621074800e80518080680040c03c00034140da40030b4000d048480c2d030305c1ca02620980212400001050003080c410351940030034010b410110006612540448580b20120748164903000d0601b001100240b44500ac1c0c003e58010038554000340c910520701040c030404581d03860083c41d1800700c000405504006810451140c15013020704c00c00c0e130700e003504164040f003620000d03140d09495421140c050b00d26580551091460300061109145000c00201041c61400c5400304104080c1c5091101a11681c0f20b02020404000c0115120180e01d00052503a03596441c0040f8044010312044c40311540007581c0640807031b56415060030b0400c07103503e070b561418500b01c018200c02980c900c806841d500c0b03407007001800c200031411510b03000170b243d83c032400451042c0a02c910010030344401c00b40c020b10382c2000a4510350026503401318103160030460718542c428003501a80c010f484d040180944d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 660950116 1250 660948866 660948881
    0x515250210060b1318060810020901021e0a170904110408120705060c030402040209060301081c03200c10290406180b180c0a1403010b030615090303130306140712 71
    0x74429106e43d00000c0304441000081540340f844140140d86207100ea0003e40303051441490012580f00e0a01004200c040c04910082e0070303504600c006012159980520402e03102d0900202da01600e8512081d054200ca000540b00b9550004201c5001446e03004400c541030180c4040204258002400a241180550007440c0c0140c0b01401c050700f45010000026400d070000d0f0003e880d140d21601031062404a00001c200003540c0c5814104411080d8004036081214402280c4500200005a51001d103104100705401c90040e42c500704141c045880ca600458100301140b1903c0100c107007030b09d00d030320720b02440384104841e08050b80e403000301c1c00740b000140984103464401340e01034601c0c80100742c10002484007611800054001642d40d81001c0805088165020400502001c040c40113001011100382181e40094045818407070240c0c00140d8810203110360a50250540000309442c9540c000d8070030706000342c0703104d4001801000b144591080081c0350407545400058161024403c1d030019507407282d103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 660951366 1250 660950116 660950159
    0x403080a030908040e04021305070225180e1605030607081e010308031b091c080403140d090902121503030c01050c0c190515250210060b13 61
    0x101c880554503060030310740140d03005c0c0410904500400086140c012040f8030401d141352820016403c103824000c2d901c81890004c03021800010b600703000001040544040282010752012040c903071140102405041041140c0600c1d01c1030551790607240f503044945234162000500284042c1d603131110100c940c080090504030510b9017445a01e010902032042d01707400303503000d1002582d403030074401c4044001440c41e020507070342e4081c1402070481d55511049041005a40682c40d80000110740c1840d417410320490f40003c06040070111101e0b482d110202e4203100004094881ea9521965501030b00182d100359490070700c54840e0600040c60b0201743d4510100400005800c80e4101b87c8601e020608407101643d8000c411080841c0420b8006420051140e000d005d0230346580c5502415501c8507a151421034140e814001c0d80300000d104142c01c171040018510501034800c1c5110141a80a51a0082d43d00001300480c2031090100b41008150121a45400c0104c6400495490003200085207a18140d401c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 660952616 1250 660951366 660951371
    0x108011a13210b010f08030f1b0709050f010603091e0809280803070b15010507061a0907020106121502071211060604051e100522050c0702060403080a03 67
    0x460060b040d070035000c12014001042c0b921a607514103140540301016400205540514441400200c40100030b81d0744802d000e072807450b11422902071000c1071030487c5c040c0c80000e11441c17100084d0f0484542025001d40508440400b15034ac8448048013618075041000e40400324600c0d06c11480d0700c1044440c1e000500905040381450405000218411245480450b03226603541c20001d0b48010030010b18010108000110701d000c25560f90258014002400b408540003113042c641c28590140c0c0c00c58440c5548010108403036203280d002d0a0515202c01c0d4010300540e05400042c20060052050100303036900240500e04101c03003582c48410410a11a2000c603840d002d100380030010b0f40300c496509a174a0035403030342c44240c0f10702c0da100b500d488001081a8402c50521040c401d0700b056510600145515040c1600050b0792a0700070410140d220760b0000740c0080d030740090704480000d0403529030011030034094140401e48809006107554056060080c0d448241000f0420001d141030008101702c040500b0003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 660953866 1250 660952616 660952619
    0xe19051b0702190e16030e030901090b130b070c03120201090b0105101e0320090a03020f06070b04030f020d020105060a30030e010f0305070c022215140108011a13 71
    0x90341141c00340e0b544003200f100e1403141c05100e82c0600500300b01c003207d60011800c5c26a840002020310000e84916260440d0014002014201a10140c07000d480c080032215a1403141d490305800407842c034070055401200080262070a584180601811103070013601c0c4200700e90800c0200401c1803100340c60f460600030018200d80b00a00250703210101e5040644001680300354246900b20340400c540c41d4000c1c03103001040307605999a155160242580d03019100c82d041d01c020780c03001c43d85c00d2141e0340f809415070400070200300c20194841700d10b80d00b21149509495040c000c2140a1382603541c295802c65100e880c0310404e016604080c113090580507403090b01c15034030780c101080b189040030410b54140c0c00205c031810002540d50700503030460454003651a08210360b01e0111801465050280d0000744108140100709800c0100c0060700e103039403a074201d801c00c0208101c1c4d00d80c14008000d4890fa880c0c0d1107401c000d600c442d40c05114070604076854001d0b04d10700b4020380c2498030111750051140913002e07107041e0070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 660955116 1250 660953866 660953879
    0x1020709110406320327070806011502060f040c031a100902070302030412050c0d0b01091104050102061503030906040909051006120f020d080c06100b030c0a14040e19051b070219 78
    0xa0f01010324500c0250181f10b08000c1c0c1c40342440c905800041042c140080000205903001400d9a4001c0300401c40b50115202c9180c90070030031100750f1000e4098191032105142541d602552725001c0c10a200f2a031684968646480303060b4010841c020707001d0707002070100b044840204000b080d6024850826940c42c10800030000d01e0b03a805003142501d0682032000180209030f078500c1480020400d0044040c107061a040c0000d540380c000800c1c0504002103400c0007075464504109a5021940040c0f03c01d07100c50b01d84085500034824844c041c0d9040c4030360610300c0b070303485182d00c11801903070b082d0020450720807801e46594411206114080fa004070700b800c03544c0040707810080078200b0b0281101c082c002d281440513209402110b0354201c60003d2004000348082007140d1000c0301c003a2905800d20030720711440c0c2550500c0500843e0b200e4508a02c0c28000c0107055180b48401e480c1001940c0300810041d181c03001c400e24101c08440c1a0303201c0d40020000305015240000701082d4829103030652541450b201c80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 660956366 1250 660955116 660955171
    0x2310030203030c070312171603060e070e1504032a0317030609090706021f1d0f0f010209091801021c0e010e0303090307030509010207091104063203 65
    0x85040d016500100e5090040110f60356941010505c289003503400e121483c541f00810003000703441c51079201c14014a40c135155000303402140c02040b13107100c0c00c40c4910341000054040504800702d01c0c0b044140d80207500c0d10080344000d0b0780949800c040c02060741da100e200c928101c1070320f025099500700d420783c40000008980c0141d02d80c1740013803665220707280d05010043c0b241407203000d0070724038060300000428000c1c0c03076000400d00454480c1e0f0041c0d52130488492641030050480811040c0c2c0911000700702c1502d8080010b1190109828400b2684c86000e020055401c0703000e102c07100c1d41d101ca40c0d840450850802c1144030340483e04244001460b011080309401c0300b5294408400c0000c41c1c0340c0090041c405020f1154188007a0604051480d5142c101c14841d103030301ca1f01d40001c0c10311502107400b458503442008100060145120204000040f0902c20401c9401600c15940000d6240d40742c4601a160782c442900e80154201001030100000600c0454a810041c0b1044038115040e151105032109013 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 660957616 1250 660956366 660956377
    0xc0c0b1c0615030513030e040f02040f120c0b0a080a021c23091209120111071b0f0315050603011806020405130b0307120318090506100201231003020303 67
    0x20802d12410315801c0c80040c2c142d42006041001e4a2244080c800200e50401000d240e228030442e80080d02c0091081f01c90001e0180b0f4119403202000c0c210b011079404135965080700001c3c003607000c030b400c25540c0700e0681b15644200e4600400082c2404040303501c00416401500c080070307140c201c581e038140c14422248103d491000ea04441400c0040b48504a00e0307814425a170000038030b10141001d102d80e81b1288c1402d00c04d00440501410010084071190a030039480901d8190003000030503514140ea0610726601c03907400104008030030303008030000b41880c1454010812264007024030280340d80c803580039000900d40200340b80c1d055501c07900b050041c0884c5241e0000301d0742c814040162103d00300030034811606481d09103140128a4200c58001e25603000902000b1100c5c20b408100d820381d1185002c5070720021103140d00280c00085003001c90b44105503000a842401e05035401803050030300243c124260b8180a600110421000800c5210b00601461007a4400c2805030100d42d00e42c1d90740c1c00b191843c3e104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 660958866 1250 660957616 660957629
    0x90112020a052d1b0703022d09150618150403030e042c10020a050301050102011b0f11120c0303010315090b01050105070f120206160c0c0b1c06 63
    0x40f60042407200401c5095040e4500d01103900c6501203400c0140c584c130920783e00c902940c070305003410884500e04000d0f040c06198003070f0200a40510000300fa00381039002c84039082e20f0045032901c0d0380250410346203180c41007101c1c1c1090240c3d81d1000c401e12926501009110220704a0541c40204603203d01611180d490a02082e0701da9403803840c100100710028241600384940d003441d1001c040c8220207003030701c11806c14403103400074004007580c4105d00d00b030f10070784c00381381c40c9800454400061500f03c4081d504840702a0001e01ca07031a01c49550241c0440074105d03e130041046001e85c8914580314580c424a0218110101c03030401050186841c600d8101c0140a600c560001006004020900812581c4030b1290401480149076070768032031040d40014080c560400402141280502c0701140d424440250420200306080c0140340d00292288000c6030304a40840c5060012002c00b44600c007105c1426400180798803002e420861a41c81a40c44200381010004c05044100b18400c9503103d248001c002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 660960116 1250 660958866 660958877
    0x31b0f03080a06061107140d0b070305150102010e0d050307111608010b031906270b0a06080a050a020d08070b0703200405030606103f0504020312090112020a 69
    0x425503001c400f07444044d0000c40400010050241d500140002c0740c07801e540720001c0c0304080158040100300c400d0300e80400904004000411302003090b4055001e02e001d088140303200c000001c451001642602c02062034041594090501400c034144620007558100710b2501e04141c03a648044501850821030364032448001601000420181c5024400c4184040c410390140041158028015403c140d56941c060040ca80310178214030103d0940045040e1207111200044042c11141403010391408102d401c0c3c0034041c504103000c14aa000010502020781e030250040c045071394590b0921000d031660a10031200483c00f8410b00c400038031628441881444566070008074501c001500641110042c00100c2105c401008140300c9070710b010604946c803c1051305c1d04d000610b856881152420f03080d4580030883c0c8810300e07400702d000c540070380d4510503000d242c00200154075103c503d200407603006075070096041d0300c46a9041038203a4541c0c0134002d0030005040c81e4020300c5c0001000000e903407181c1d08290020b01c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 660961366 1250 660960116 660960121
    0x5100203120106020106060903080708451c0501020405060c0312160c060e0f01020a020c180f01051c0507090b030d2c06070210021501080a020607031b0f0308 69
    0x1c2140480303070040281c2d20003440308600d000e80c06084240d07280000741c802003000403840203100c1210308a450f070381c1000300c946110140c2028854000240c030340c0f0003141059000059424036a01090100c0d02c008010018400c05482ca01040c0c1e010400c01000c4441d95000d100005259032000c0c06407400c944c0400c0615501c002100400120180041441c0c0382d0b00c0d02d41c11040c0000c1d40c850700105846901c80400901204444176540c60600703600c0200380250f00029032007400c0c5a011802110785038007038a040403a80c80d03074401103001d400304580c2c4540800e0301c0e20040065290455019103101103411440380d0400c034a031905c50510b502500308500098550386090040e080c00c106110f00312505241085041e4000ac81000041c400d0078415611035801010b5440c5035074440c0200c1314819401044000410851030307000c0d441d098440040023142c40220000a0741c0c01c0b0114030700144681c010021850308001303a4050b41d42d05603004088507201c40b100c40c500c00041c0c1c800750880b65140207480e1070301c451 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 660962616 1250 660961366 660961387
    0x1050118090309051008100e0114010e0f280f0b0f130308030123030f0a1101050c0a0b010905010602030a09060804061407021524100311220b0403111905100203 70
    0x30541588000810223080c4c0c010012002604043c88410300b0901e01003901003451800509480c020380d50b41c03075100d03076400c444105041d80100c2103c2800d06500381d0340841980e42007503401041e411702ca61800c1020410028100440d807e00516210921495010110b80c07280c8941d6229042604411004413010035503590b044248600002c1b06101100140000410010181d4403103100400040c03802c5000012001640e02600680da540c440540886004d180541000001c80c0f50a2003407070301c07051810001044942c404400c5800032080f070788540d0112498a88103c5110318001c106441903580c41401a9481440703200301c13805641c15500501600c0e08007404c0c10422403001c2d000c400e41c01f041024484141240b400c0020f0100011203000f800881e607036400750041d0082014400b00340e000040d48490079554104002d40c0000482045a030709510b9006601c042e200d6400041c0034003074142605200d030b2070019850110b8151514400360301941d69402f140c45454a400c030540035810100b4581c201 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 660963866 1250 660962616 660962641
    0x607170c21041421032106010804050a111f0c060b0603150112090c03050601030c091103060d051f140a02131a070c0e0106030c0201050118090309051008 67
    0x501d007074054034240c41c209401d240d03841c0004000c1d019901c000542914070b4441d000e00c1c000c0709508415696258442081c0c0c00c4103484c0414603112240307402011484c1ca5209081541c400d607402001406401e0440d12032030a8802c0d81c18845500050b5000075014551580038034111144c0240ca5400703002c82d007440c15200f0703038002001043c0164410b00420001001588103c041a1002e0070075055a108529200c00948000000502030300c41c40107000042000001c4d13458100c03809001e501c06070360307200c569003000e81d0340b1000760189200307051000c16010702d8450046106148078004582c82940b024000780c0e1400c1d84414404881c075601c03598010b09005510a0591005035500c007185040c4990020342c10390038150090051940749003500d00c01080e0860125400250407030305601e01c0c07541d90b0f040000024401d014100001781481d4801e025680140030381c074107840440323420100c055640a08900204040d81e03043e0f0070088001310008054450b524614204640c039640d03c0c1851a10001e1900b5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 660965116 1250 660963866 660963913
    0x103050c09040c12060b0a0f03031b050604060c0e030d030b041808031b1b07050127140a0b030109020a09081c03090606030204022809080604020607170c 67
    0x1900e03914104000683d00c201ea000958004400c66407102d240c5091242c000c01000b0249034000d510400046140b25001400608985c42640d6614203070303030710304248000740420202c0180319511200204e00040c407141c10510b410581490f10310b031180e46010002c1e142414000300d6401080c0c0d104d1500e481403c2c140981da030008021200c00500f02c10a0b901c3d208180b000400040d840560819908441c400b00001c03184d0f20152142000e070f409113040030807503c5017254440c3c04e010404c1381720100140304024181c3d54002d140c2c025214265882c242042d00c00d501104000c0346e10440030744c030100e24200750314041d5002e000412001602c0b0111200d016240b26055003284446500040c9800300010b5450f18003010400742e845d002c101c51301c152070400c02070401500b00039030143c0045440d804080d8181070501140da8659100060b00b81906410b030f40c2c0a01368000c5101d65089940084c01604181c1c0061019078443c401c110304440d5a050341d02c04541104d40708160a0f00407103900800c540302608041c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 660966366 1250 660965116 660965119
    0xa06030b0c0906040e0c0403020303190909090b1503030f070501090b0106110d0e0d02060301030501090309091505150921121c0905010e07090b040e07120f060915050103050c 76
    0x107140c18841c0001803d140201d1042100315031000d0001001c48540c61300352401907038042d0489807034141c0300350301d000082c00480c1c1500010b00c21420002e11040e55004203580c090300010162540e071544542d940c400490220102d8143c8410003200c148d41e02c0040081601d0303800351000080b000003518000ca40d400701a484802009003c268240c100030000c41c00314080f16907800e10412265060380403681c400000080650b015030b004c40004107002040d0816034810f8860b9480300c0f525a19403480508803920001c100d200307104094414030031030400344100401149410707001e500b0b0401c10400920000c441440094080c0400d040501d2101020442e8020002c880105181844a4541f01d56071403000103030300c02402500e03080b2207024041c00b03501c84500100e5100c01c2d10829511640440302506804041600030b914140042c0f000714008200e6805030780c000340300700c1484071064030348814039000c2c402c05481c0e05030780745401e000241240b508075402604003c004607542d855800c0482c1800a20b58595 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 660967616 1250 660966366 660966391
    0x2040b0405060916120603030f08090f032a010606050a1403091f0e01110c12030103020303030a090507090c0c0c061b0210030209030a051b0612011a120a06030b 70
    0x841a507412524a500c0500085131000c1e0380d400794021150a181010841c40c918a807a42c084141a4000664201c0c031b095912a49419100c10791a90b956034900d0744003450980045c0281c50200c000082c4c004d080d491144911006010500320b954211601c9034041c2020500001d5541c6076160401115444a40e4480c42e42e42940f502084440d01d400e6920545102603c0d06451060b08107a10f500a21032480c01c60000c0004180110300d4113030a034468100c1d01007611552400010405040044906881e03001c0d000e141541c40300048840034109024089a090042080202e03013002c9500c01c40c004462544d59900d003080142c10b00481c00c41c1d80380c200404001070444008203141a01040b1301500d03a042e1031260400c207080c0780440090048041c0c00343d06006500021003845400500d418201c0c143c4007030001e507100400200000b0344108a41501010b2401c001000786868640300310701041800d00d4040d20b000259090f418a200040703400000040e035402080c02030184228190340c1c8210b11600c003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 660968866 1250 660967616 660967621
    0xc100605090f011d07110f06060a0b040b0d0c1e0201060302011709190201091a030402090907260106032a050102010c0e0f1f17090105010510030209041409010902040b0405 75
    0x20700013401003100180c00c0142d458404652030a1140080806849048041d0383d40041101566511000241c0d01c140c0300c0c1c01d0344800400c1d03191151084404441e40300c08000c1ca00300031800c109019120320303d4107105010840e2805403aa1000c0c0183c40c6011941e90b000284c01811480098602c8031054030101c241440c807020807c1003a400103d001c92001030080f00305c8d12400910040358119801d4010400401030940708040c50702d00e140103107010302e00c00c8400c804960341d8482c10503a5868030384a100700914690302103c100310f80005d66800840c00303802c00032800544984407004601c000c02865a1404030b034001e03c0715215a4417042c03d010300070903c02440800f10400e03008100c45541800c952007080c0e510755018090742c8651504207004640260720303400e00700d420409844020b0b140c0b02c1c160b003010700c0d800055042d0010f2298a068660090024050a80000d41103000b904104501e940081e035444c010f05650798a086118881c0c00c1000020400100902c140000d48050b0a0f23198051401d000c107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 660970116 1250 660968866 660968879
    0x1f03050a02090f06091201110717160b0403050408010c0c0614090601050f0a030c0306090209090c01200f06090115080c0d121b0308100506130314030c100605090f01 72
    0x5000340008080f031350f460302d0302141c4c0c0c0001e503100f0310600300030310a41c07810320309203100b18002000d840700074060031410080c45045854143c4038422102d150911100c00803900002409000229070090b00a191050403d40c90712001803c58001d442d0602c0441c007084038090400266000f1b050961503445801c9440c3c4c107007180c00355503e400c1801014810fa541c050304201c103031203807103c1800441d00b106c00300900d6903907401c20f40d008002c25071099000341660f000244100302e002880d07004484060355950b01c0807210401d08201d010000c20002024000c038018400086802c01026008072020b0000096104070900016080102e5501641540e000001d14281c3d982d54414900c1c01d85410103c40040000c000303408072011503030740383ca5480c410111501b08043c150b008550f42d1060135000c0f10618025140c80c1008010f0188010503185520515420b1001507800d0030309545800c00350048074107207888228220b0a01c0362007000000b1041d500d66040115142120983e42c0002040a0380310036941401e8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 660971223 1107 660970116 660970129
    0x213050a140c0904091e05070602071406091c08070b190608100b0a0f0905160e0a0902070f0218090f2802030c1f03050a0209 55
    0x3507941011101c8255a69008200010352541000710900401014110301c80c0c04a43c95202d135035031429041e0700d0071450880c4520804c050034200d03003040002443e02c2c5075940f10f14038880600501d840c81e03803656011210000380c1547c1c80c0c61301d0708042600c110165504080100201c60006990007405280358050380580c104410500400102c44032072000c1c1c0392540640394054100400034036110101c0d6020048100c405800180900c0c0d445000c2d880c40c02c110703032103c0c0002e52a00c0422142544180b880310920419007002c071152031010340464000000c0d40501c0c480294001051800d00c2643c0c803c00356417540c0144801c0090038561003c00c031911003078400460900c50000c603082c2100d80070626083d1030401c281c200290b100c000810b42414142d405041c1c2e010701403030503132903095166400c5101c0d800380c0c1e10200070a4035a50f05401021101d005020215851041c495880c5c0daa4034403 = true := by decide +kernel

theorem cover : BRFrame.Cov 660791366 660971223 := by
  have h0 := BRFrame.cov_init 660791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 660791366 ≤ n) (h2 : n < 660971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
