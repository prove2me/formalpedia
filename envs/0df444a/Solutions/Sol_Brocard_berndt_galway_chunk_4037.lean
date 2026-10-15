-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4037
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:23:35.118671+00:00
-- url     : https://prove2.me/submissions/99b8fb68-7b68-4d26-9d1a-8fe0eb351865

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 725899280 ≤ n < 726079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 725900530 1250 725899280 725899309
    0x1804060515210f12040506090406150c0302010f0e0c010809030409060f0302040b03030c070e09120a020105060301052a130519030b130b0406090c051507230d1d 70
    0x3501003007800b0306141c0c18950502c2034070300c0303030340c40f0783c0801c00d01311070440803542240c0003141c81954582d95200400c01405160344618a04a014010383c4900c6400c40007500206229074003c0040c01d500304002411681010610100c0e54401d0980c00d0065000742c18080d08600d0000460b4140790b9a164a0000e66500344c10409244004c00d40800c11030610303004100050310304801440c01c00780301081d503035941e82903807007040c1c5030f558100c011515240090203101425005450110395690310018040d000e0b01045d101180a90301e80400209840c81014051440d03214001305a030031460401d40061054008407400c2170300c821034890000c1e2940e25920f040000c061404180c0c0c6103546141003904d10000c1c002d1040f9101c10a40410780005168088002d504c9644040005044044e0341025110441c0d240c01c4207403c031161500f0680c0c810030810103040f076144200014840e50382d00016548181c80c01c210613000b1540482803d01846000e081124a9070141000f440182002d841c0040c0103900704002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 725901780 1250 725900530 725900569
    0x150821030c0412171b0f0a050d20060705030411040b030d0f03023903040e0403050a0e040606050c07050607080a1b050a0f0605060102030705070510050d090606060801051804060515 79
    0x500c0417200c0814002c002d121010350002d0040300e1400e03208ca90b1125600a421030400c807044103c03154040e0301002d0000c050401c841100e4582c0341106001d40540c0c415101a10000b511541d034004919090050600759100070f8080c2004114003003003074444002c001950300c140751f000c0c03102459101d144190411418404d03048194555800350400400c0036840c2d800c04696001000144a07064035060701070b070061381c14074005030b4564080303008441c480e0030002c0300d0380c0c46803e00d600015429401320180090ba082030b01555030b40d507035900810110344140c840c010301091003445292041401070040b84640c540414440c106440103a40360360038610042411500c0703010090a20081c84042e214083c2d001e0000c3c0021890801c454882039641e200354400d0030b208560000300441c08500c240d0030386408041c01001031007942e4141c40d20300007901442c050400041e10580c000510783ca086400c0902451038007040b04000e40721030700ca035800303407000a001c86230400b00a00c070800b41e45c64203a50410069250b04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 725903030 1250 725901780 725901817
    0x4050606180106080402062a010e1902011205090106030c24080c1b28110a06051e0405060d0f0e0607020d12150821030c041217 56
    0x2040002030300003a4290144440000018802c280d00704c1495501316404548032038403103c60402c810b50500c0f01a202e4510b1141001d030610014105411a406003081007040c0c50003401002110104910000301c043c0c0080e814100c041042401a8403840c2c00080c0f8800120f992512511080401d011f16440391030741542004020511000d03015540c2180d9240f40f805111608200340c04600a00442013404042e004c9200000403500c0b04200d0383e1015a102c266072004048940c401c00c00c92000018240d80000d2502c501410398500191100c0542d11151601c0e8145000c440141090804410180f29003401c1048082010340c0c915000e88004500244003140350321043c44924165840c02c9070002840e4019030a0008503600412800e0042a140c0b130018441d40211202a014003078052491403103242c040c42c0801c1b9540003052015803200d0324a00c0c0710000d000d0415501c11031008403413111082009201c2441042203d90f4200c2016000c3e0207543e0540701e1010600c1e210768401152100e8284508 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 725904280 1250 725903030 725903041
    0x5061803031c0b06040509150315070903021e0303031611030f09030c0904050c040b18010306021b0f0a030c0201120614010e040b0603010302120f0102040308040e0a0905101d06040506 80
    0x24094183d000d02d040d5081030415203014003207841c410014009500154101c420660039850401c4202c400400681843d469800c3c020f034045c02001550009070b005030310f0441a64000c900d501d82d10f6410280140045265995490903211003c1405908204110070349482d480d84110030006440042e09401c0744a03035591001c42054507204403c030890340281c40c410204004030700003095250046c4401d580104415945e10001703078003514056400c0c0440e51000e00040140f010660107000c16280800c81003050303c2140081c2a543c0c1249540d41d0b00c02d62001144600080c440c4081080940c818101901a00941c0f9800c0c0309a45458209901c03004c1c2d020b6035880075603400904400c0500c0107481c2042502c05d2840803400070b01c81400b000c2e000f42009080040d80f84010000e81e170564514100031074969440345848170503a4030a103d014258102c4201085002142d482200909a48035000704544200e580000340901031748070902882407409004442e07a0740003808418441c0c0c1c81400900300601d0403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 725905530 1250 725904280 725904337
    0x1060608060109080d0c240504060911120c010f0e040c020a110402070825380f1902091908010507081e040503070f050a0510150506180303 61
    0x1070340c810000b9510a40e130540318a40c01c2448030710804e41200b11000039152840c501e00e203011f0308052210b03050b0302e40760400c1309100041d4007040007030380308083c4184420842c0080180d101e0700c1110350005a045480403012540c0204a0b031594842c80341400b15040c51120001412903000304620704c09600221100c0c2c0070045072400400039540308540c110b04041c4680c0703a801041c024403403001580c010700e1800245854282d044c075440e86074054404010681c43d4401650384120792070940d502ca07010100c043e100308440c1d03481c1901c81e8056903c41540c50340c07680388100594003150100c108060342000910f00c0342d2121440e2402d21054a451164410310301440582141d800602003030400085000f486840340c030040702c0f094038110082c804d03051500c4904000b030661041110050a0388070103000001044001310b078a101c0c0c14018402d545040004104401c1030301c80140b031001d180115000107012510302a000b911030111040c0d1500c440b00280c0d0302003403850b4000f03410b807541102040e0040710817554 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 725906780 1250 725905530 725905547
    0x9090b0f2503021b01110d0c030207020d110f21061302011710090227030c0a1211060d0203010f0b07020907050706090b0a0203061005040f050904020d05010606080601 73
    0x5411140c0507904540786411600580080c00c070004054000a00d00241030903000c90b0040001e0a074002c1002c000b00c41481c60259000c006c0500b40785042460b00e1420034000d200303444e4004e80261010401c2c0060360b0701c0c20261001000001e030b010350242c081c50740075158944608070034640c404401c0c6180941903203451070244010305280c80c2c402e01d4914100141d0b0700c810682d0340784215010403031940e124a50750060b00316141e008000b80f10f1011031420007000a8504a0f59014060b83c1c41c4d0080d0030b800024141c652035038020311a00810907070810000c1004a86c3c40c0c4102a000b03c40c9a80310050444c0014540d911401a2100254010005200440d02c0548600060031a41901858000780d075000c80c10049000381800d00f84440030a64a007408001e07080300000e640d11600c0650203103402107505009400599580d03004c1c8040c09070f58079550b409841101e05503070500c0f03908202e03145040100012000010422a004a490002900054000d004d10009003544d9103a61003145040310004203403e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 725908030 1250 725906780 725906791
    0x2041407120e01201b0f030904050a0b01091707080312040506010605030f010e1009021903050c040f0911120103060905120a0e04050a02090a0603060e31020a09090b0f 73
    0x24546131882080080945042070140c907032240503612402c4008010f20761907031318209503086006040c135610607004044000c015800d000c80c0d040106817140103802c4101c8a80301c21503404208004000d2100340128211136882c042d400302100c0207035460b000024150b401c2100072600c0030b00d100c018081003040c00d1002c180940040e00d8818154030340440c074141040010f00c1100800418100440c100b00e00700c08640c80a064003120079555805066040c0202d981000700d00c80c00280740c03001098500c41c21408640c1140c1c0301d0800b01862505140f4000d0040c0414048d0740c001035020080c04818403000d40c0100d000794060131001410940c00c0c28143d080641c0d90000b042c1903c000c00c034540825030480350703644c0c180505a90002e4aa40c81401c0c08009101d4840c4095100d50080000071b051039140e001070040c0e03801c259455540740c0b1100c8902d042c503030707620303806410b000c81242c01c0880c0c0048804040e9100ca00081200003c0742d5501c4111046800943c026145170110108105600702d40040701900700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 725909280 1250 725908030 725908033
    0x409030e03150c03130204061a030415051302090a180b0403110c062d19030b100c0201080406090206040b0306120d092135030108060f0402041407120e 66
    0x1450240c2c1c942d900b1384401400c0c005103101000d042d405649030b5600400182921940020700b20754090309201c01508100c500715104003400c101100070203420701a090042800750014031444000350f003001008a0001c00c040c58469852058a04a00d4032103020b981c218061030b500074081c1803500300182120740300340c01a02542e005103109202a01c2e4001100d11441b54110f00c0015010001c4003850000e0749103001400c0303944041002560340d1400c1050342030840e00307a28100f0068044000703100c6403c0554030b5084c046290486041d0155010b0483d80c0c0e44240300341d0300080c08290940c006a01c90300b20350030006503001c001c0100502420068500b030400010302005101c801c40c0c1e9a1300410f004494043c0782c602003036466840c11400c1c021a0f2000b483c036482110120240b10310410011443c0b42c1001c603000c40c4411003041c5100c0d601d00350459041e101d0f680c02805960349d40300c85009030408090f1041341c00030707a5605075642d0152114900740c025540342d500c807044000e1031010802628a0b10340c1c13074542b6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 725910530 1250 725909280 725909323
    0xc01111e030709030204052203030e0f070e040308100f06020a060b06090306241c030801050a0b190908060708070909290f091f0f0e061e0409030e03 65
    0xb01d0b40c022015008a9504a50108484c2c2c0c9941000ca12446400c501006081c0c40b01e65200406030560082d031030705100d2004450340340409407089642c80d007062240b12a11b40a10000c1000310f88130f81c030100e5020262000301c1440c00e40d5450145d500001e20381c019401a0808100790040041d580101d84080e00f044a046040110080000361180e402400f43d80b0030000c80207820f11103180648a100044000624403200d0088100381070800c10036251003280021902000807440303140c1681c6940c2070304e40c0130913000e040808a03022a42d0b1029406000c20a00c89981c01c009000007040001521500f290380d01c0e0030f140d04002801805890740390b002980c046042400e4000d440341c55040c2c2c6202c01c2140c0020445146520002c519030032141c0c05055004660b00c420000400090b907510019a0358007110482030a546201907864102035025620400e003100c00441d026180c1100880304c106002c0384514500c0b2440d60001d8200c40c8004401c802044018003000316900d01403018410441a0a810110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 725911780 1250 725910530 725910541
    0x14011e050106021c0e1504050a0e0921070602031504050a0204180f060e090708060601031802061e040f08011b02070303080c0c070e061903021309080c01111e03 70
    0x4a442c00c0c0c40e60481d00550b81382d907006000b48101c40c030010b240b074064582001507009096511842c0c1c400d006a501414071000c001400961181d540792145206e100540300f61030200000c1e0b004400006001107040750140208008210240f00560040f25400001d00f1a16a803030284015104028150f000c1c407441808100054501d4100c01510241c0340c0c88000387e02d5032500740f004020b003080c0e04103512099414040284500c00010410113442e15801100c0c000d40e15240110103842201c100a0b4004982540303c500500300b21016250303482c0b00d108910000e0114840d4248160081ea01c100c2c0e180729225000c101450082c42049400907060f000c5000c03d4003016400f0350b0780c18151200400700300d03040340083c0c3c048600200f40d400304030780c080c1598400766039403041c2001c18400b5035000d4403e600e410180c2e0b60400d070f100031010031282d000e860026040d2895001500600b201a400c0e94800c1040105d02d0f400c020030701c50b051400c0102d2107101d403a4420030b0340c0040c080c039041d410700c454681c04005110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 725913030 1250 725911780 725911783
    0x60a030c090c03021306020d18031e0201262208030606031e0106030209040e030c0d030e0a02030a051528090c031b091b081f0314011e05010602 63
    0x162031500070089505451020b0450080c840c0841c802410500701e0804200c0360742c040b80044003030001c0c1c2e50b081002542c01d4441c05140304ca92000900d07428150175005100340d6800c404d01c003c180141058036032038040e9892034000c400c2003907404402011000800600d40030b0386440c242c0c1c101d000340402d000002c940e6150784030f42c40045c000e40d1142d44044001410104000302102d1046d401d00102400395959000203000303900131143e130724400c030300f040b0382000020360000c19580717001800d030010159500310b504103034014500004c00880c2c90103502c00000c0540c0702041024944c520810080000807400700c0624205000500b140c01c241188424002811641568010400106120001c1c00b68010b20f0050700b80c1c0f4160307100402d07455441104883c9243e9548015044402884080c480e48512034101d00b40304a6010320100400c240c400481c80b2000c00900200351208100d8111440585944602101a00141c0b4510541e9110f90f40341da440e00b203810340c8602c080042740040c000c550404d00e02a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 725914280 1250 725913030 725913053
    0x30601120206070f0302010209090a27030e060a121104030f14070f0e071701180e010212090d02070510080f07140a030b010915050714030705030a09030b060a03 70
    0x340301810391400d0000540da1041e00721004198050080b280691591401070b000c0e400500400b8881d18079400006e4a40100b406171031042e0b40c02c00c5c00307814910610450155803150000c0c00b40c042041407c6c03c000141c54080c02000304500039103a5514143c003514610382a030700034082c4403203070107000e20041000510340300300404115403140810403a000d020055601e084040d600c0404610800f460001e03181c2c0e40d80700094000c1041d5681c21079665140600c3c2c4d400002c0030711411a40f9446040501800201340e4068503800803024005807611004d2255400700c1e50055a00c200d494100440c0342c202c2c0d03030301088100020700e01550403821028907044c3c083c0008200501c0401c50b08407540c00904500d114000e5000101c0000800e039480d202d00404c024020301c00c041c0c01d0740c00728810f100080b41580c0d01c0c019503030a1003c6561280d1074001c19a40302411701c0e5440300b20b40b44034401880701c000092000d1016103408246907940308512443c5007403020f006900500802e0059a010703406101064500081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 725915530 1250 725914280 725914289
    0xa0b0301150f0f0530070f170601080712031b060203010e0a1119030b12030405130e0d14130e04020906010c1109060315011d01050316060e150705010b010807020a02030601 75
    0x1207440c05c02601c44450a06070b99100c49009016491010a0f48004a00d03000196500d5051202c54000242d02603943c0f102d0030701409125a104c00010401c4207808c0401a012520a00d401d042c016203628a124040d54095411500d664003c4014018000081403c59106103400c1c42802210070b400511000f91084142515002c00030000040b1381c20f0103600418541c4101500d040804a558810103032a42c00c20b000301880341003400820480500c3d98043c03030311807121240c090401800b080c4400e8400143d420150310058809108608003004d038200c00c80001d0001c0000305203149028410400485002041c070340c10701c4410909900440c2d450790843c18903104c1a038414801d80c541e000000d2600032031080030f0800003055800403600b22602246004034406000c4080c046981340d030201a11003c034102c042c01c0c9000558010808284a000d040c0041c1c04081c142010a00045100b0049a403041105640680d1500380240482d44c0c000d031a40c2d03018106201a0010741500d90000c4c0c0c413004180305 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 725916780 1250 725915530 725915569
    0x702121204060e060f1501090509130c03050f06011a0c0307110a09110c0120121b0711150f091e040c020d020601080c01080a02030a0b0301150f0f05 65
    0x50204500e0f82e2100329606890f500300c13403080c6012031103015000310848003501010903003108121503502810307131201a20402081480d059a441c2c01450300204140d005441841e0310b0040080402c1060101c0f070300001445000d04070a6040000904032140ca48410007000d2404100c4081001001b0003500e5845500802c0200c1800d203020000c0c0218520350084040d5500e001c80c0541324641460040075507010000003441405603d550030a500e42d03003428080401c0d101044440c0e0041026214281e00203001d1004240c3c0c0c88041003010340c41d401440007202e00034000b0706200d82c545090004400d102d414030000e1460890760b4201c4c00c0d02c2c1d0141142c1c1c03a0040c0300f10300c2410820440c1e122380301e540f024050310800030810302010003941e558038003203210098001e44d000482d00c1c6801144807103500806845040d8240c44125444009610041440030f5a40d9a03950000c0165028090400c2103000b6072802c900141c2030100040440f002e0307600200703406090480821198075014051050b22030fa002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 725918030 1250 725916780 725916817
    0x1403070c1205010e0105070c02090c030106212003010801050a1116061b1e03110702010503130c0b0318061b07170d06140f031b01020a06020403110306070212 69
    0x5821405404c402d6504103203542801c1c10402500d6110490040c3d02d8000c030361342d106646556400d0a1a48030a000c3c0704d000504504840da03092084e440c84001c212130340318000603149100f201801551811201c658124980040100500c4100340600d541042c0400020001c1120780c21412540b4803403e075448801115034400f00040c414694065659805031501d0700780d10f0028240002e002d2245800c1e81ca0050041c00361142d59184288103001c1403658800c100b51400e88650015201500010404280720442004c50000980110762003401020354688040c1c503801d0500c4802c1c40120000320507161644008104022900c40c0d0000d010100d44843c94940e90b0302c12805c001c21030301545288203041480010b0351141556032030b80804112841c0b82607440b45200c01c0010400000400003d180c1d040e40a004443d00fa14068400355030b03d004140126080402e482da40d40c4103036040b030703031080e100404611521141820140b015aa00070038900c00b600303503074441c0390200701d4074002c6607041c0d0606d8a482e0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 725919280 1250 725918030 725918033
    0x1103060108162a030f11190c05030f0105091b3a08071709091f080f010e07050901051503270604110105090604090e0a0b040f1403070c12 60
    0x142426209114070340f00f01040b464095910600d4001c449070100c000030301c034240b580d0a10748140a00340d50104244040c1200d52185090240e6030061103400340c404140d0b181000841d507900b0007502c0158911100081041d142c40c8402c94201407090103030710344141c01000210110350b200c85010520107445002c103441c4881101d550196003a180c050000c480004010086c140b0901101604016114219055660034460f461105501500e1203480d008101180801c0e0089100003000d03040c0210944100700c2030ba039031485c0c1803601d21815a01801a55100da000c000d201b42030012102a04098410103c154540f001044c51040c02c2d64200b1401d0ba0084046120006d0400c005900442e00c03840845410141d0015692146010b542c2141ca03000e11450b0118554021001d90f0055040105001d00305441c1441d040060030740100b820200e40162640c40c000540c540038041e01130380c010b40942180d81c10a1504c168a14130382503138800d559100b4001500090001342c1c020707064814205804128103940e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 725920530 1250 725919280 725919287
    0x406051b010c0801031b0e06130b060f0c060f0412050a180303080702010e0705031c0e0402040b0a020709050907090b120706080a060f1505130b03040c09110306010816 73
    0x1000003140c0907500707104a40d605194400780a5050b28000d080b80013071840c000e00c4400078100d19206260074061040000740052400c80090000860070100100355401d8140c0041c3d06a486100f141c1070a01010807440c00c280e40800c04c040e880061600d082c9820b040640f508001490070404107001c02100144441785d961041d10849560712a5403c0120790b1500d0746030260011500316820401923181071740c0b00800d410300051160031600060050001690186c1d203064641050042e55024040e05a41e14009a12248024402001d0644500d5103072054680003d05080d07450b0b0041381030508102c144040000c011580300200c0d412400300040d4000203001003030300302c8240d4103102100e0185040004400d5008040c040c0b149590410420042d51114450200c0e05070900030110303441e408800b000c0724140a07100801c01051a0b40384c04810319a40e0000d12859401224101d4005600e200100500003982c09840b81180b505c0300e480d400c40c6003650008105800092060300030b00581c0e144a250b02d4003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 725921780 1250 725920530 725920567
    0x70c03081b0307061a030c0a0302040c05120a0b0f090717040611030411010207081618060b040b040513050910050c090301060603050105100207030c060c02061312060b0f06040605 78
    0x2a0041543d466041d07a0509200401c0e0b0000380c16107240b801d48202ca0540b4020030000d100b00c40040a6421031819134081c030000b000600c401c10140310b410000c0040c002031240007140f0540303001c90081581c00c5030605100c0340e200c28903412030288075050244107009400001351800b100302c040d940388131075842c2c2c00d003000601038600d0014100e030070001c140414810300300a501980e00c030a80842c0c01c0c1d680d403040807907641c0184040c0003500000a42050060244003911008004030440000c90400e4450104091546c880d52201404120001d0304000780d080042070000b00140e00f007410000303031170300c1011640c03907021030390302d03003041c543e50307000040c03c50324544203036114800c025008200460f00d503c00078009140a0260703034410001924904016480092182e00756070f481650781103d140743c8001a603107025802c17001c981c0031708144119040780740f0102e0342c40f000f440100b0000b03c0c4600130342061421101c0c80910030740a00e21040f5003204a440d40c00840f000c5a01500c0c1c000c0d59084c03404550300c020305 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 725923030 1250 725921780 725921827
    0xb06040b1608121e01050f0415050603090304031202030403120e130608010c080906100618030b07171e3402010b090906310b2a070c0308 60
    0x2d0001c203650b001c0340078003180b240c4514950750041c80080e400d2402c51250031800d02c6016440481c0c0754540c031290400f500255003400c502640c41441071303140c5000550301d4104403080e00c002d9002080802c00d0110400408807031203510700240d46030a04580301c40300582007003090352090015280c1104803545500e0036415002000b00c0c800c202990700d41c0091406861006800e0000640b4000840d580c5400402ca1038058140c0c3c00d0b1154005103007030016100035031054040607400d901a5070004c0400ca141e2402c41c4142025541c22525143d014150500c1040c081c14041640100100100c59030800840340c0750401a2080c00e9103c2a80c11100600c04864408070350050a8502210368112a01508126100c4030308856101069441c20030b03190f940c840c01c58200c00d0021a0301d2801d403c8203a410b080544927a00301e004000131a0031602c400b5403640d81540c44040d100c0100da82c1a800d102c68815004862a1110025260407aa03032100030042c7e00502010781402030000d6070f00341c0040703120280c0042c00b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 725924280 1250 725923030 725923043
    0x7050d1113020d06210b09030c030703090e0106110a1403040801020417060c030f0c030703020f070311190317180609010506040f02040503100903050c0f0708010f0b06040b16 76
    0x1c82035040d070007942002e490707060000e04103100400c00755650b480805944070007025171110080d880d11034841c4101c01074081c248034041007140000c8240113100030103000b03001c0d031200400e1625000b0b00c05c00d0004140c1c403042c1000008500c6500030200804e18480380780c0c02522017103058031840720701030a610442e80030074100d610000b80081c0c00380800c910382d052000c00c181618482c1d602c0b1550f48090344021103086100603020400030381104030010180d60070035105d10740103003010200101c01100764001041a40407400003103000260784404c004900015066100c103000289465401500d2900c1c01c45c10070700750048403130000d48035a0400102103211400302d02241c0044c1048074130360b03000f010151103080c01542000200403d12400d40203d908682c03003c2c1c018010302c070b0207140c40000bd00c81480300b10b080000c20071460070302d414100008502c11202c4001f8010403443c2c4030045003100c10010503222550306001d43c330051980c405044d1001c59140d045140d030340d000546003084401340c100d03a004165 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 725925530 1250 725924280 725924299
    0x80f07030e1204090e010b0d0f030302160c0b0318010e072606040b241305070e090a0605130b010c23010c0804031803050d03110910021c0801050307050d11 68
    0x2405900e1704224003c401580003000800740c01c000340b003066940c0c8500984400c1c014054040000d109500400b41c1c240300d440c682e01c1c640740941d1030342030114190748100030000011050044840004001c12000c00f040002000004421110304d504c4140d10b114103407118100a042800702a0031001c1008150100019100945450716003130007012405d40c1c00d038031034100301c0e014070316403015984070101016002440170302d44110515202024050040c5400e0402c000c03590101083e80381c40110030700070303404000d0210f0b020781410244240c84400030401c607545400e02c20842c1460f608140c803c1405030300000f55540340080d074121a04022540049940c1a40c43e00e1072040070305a01642d903901503882541d0728584030106851844803a58140009403058209522040c600340c020b03800703d00401400300c8040d0030020030000054803804c1c420890005600318802c8099580344040044800c1d40309810260036950500c4003090f951071450040c0b0b8014403a105045040c0100400b86500d10342000749010380 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 725926780 1250 725925530 725925539
    0xf02010f0515191e1712030a180c0b03070f14030601050f13030f03081303082703031311030a0309140607020910030312142a04090e0d080f07030e1204 66
    0x713046940b48a002500c0030a072a03107509021002c68110054501c1242c11030940d10ba0103e9000100280d851900611214503c0780d4002031244178110003c18002c00720035202d2618403000b52542e01c1110380c1408014185003824080c0010178203480d04800c080c68a076440d8207000d512500a881500509a4421203000700001086182d0301e029101314072940d03c10101d9111002440070010140d90014081041d50f000228071005000340c03908891031011401e115400b00304400c600b5070f030040da0208428155074012505000c01c002100b240e141056000300214009502d00800c200031a0066441c041030200e90025141e4411050b5625140c00034030008450400302c460b0440c5190341e1100318040341c440c5020000c9031125120303032188520021040b0220356600303038044548813884203420343c0060322041c9420303a0a003640c3c05840502481c50300024036074039007003e103854190203a241c6001c200c6008204612400100d42c100d410142d1401c01003003103201043c40c2410314403c40291101d10902080025 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 725928030 1250 725926780 725926829
    0x10060605071403210a0b0d020105160804050607051606050406080f10150809100b28030506090303010f09021c1509020307030209040f0b0f09040c12030f02010f051519 73
    0x103025220005c410440c000481c0700340000c1881038034001c1d000c24402c1c80020400c101d880c0c1c18851003485148035514064944000840030742085000303031560b03449480440841074481d040da00152a15041c06810140342ca0320080c650000100800c0c80781d61400007080041e41c52042030b10142c45403482139a4920784400000b442d25030100c2e11010749100b0304a4120910b0424420406184005070100440050a803201f950104081c2d0a5400029034140c000022500500005004030140c0e4041c40c0e50b54944180038011009a4000d0140e191041107084a000108410a80038081c501e0000c074030030a1261010103407180c2d552007448054000000c12481c29803650003000c0360310080700e0402030300a040c2a41411504003072610b43c2c002d5403800a8000c1c134503004c420b9030340c003074490307160501082d880c1c1a401d500e03010b0a036021008103003420285585203030203000310081269054010802461b00f001324482c03100000e07049a01031000412000c40c107042c0c0404610107440704d4001001c0410700c07904040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 725929280 1250 725928030 725928097
    0xf07030e0a0b0406050c0a0c03050606091b040612090501050f0123060d110c0106030521031b0a02031201122f0910050d0501060810060605071403 64
    0x4600051010404a0051030010000800d41e00c40702c1d07400d030800f0b0070000140c9556010501900c1a8402e070f10003140019610f011b0300f0040c511880180031507040c01801c0c01318811014100c5500c0e0484040c541200b003445d2001d40c2c08032049031511a01c480ca00f0000c0100400a100c005000342d400c0104100c129644503881604035000c1c21944649145500c0c8000c0d080c4c07031840b40071540941c0800042e81e4070304013600400b044208248201d4945110f03580d81d1421100d91713a108482c15002440c1550004080e83d030114188950704440750300d54940060300b50340b103d0025000303072280c407000b14211603a17070303c02c000707680f01d0fa420040c00200c0e43d43c4848942e07030141521441210100d000c440880a6095910b01c182900000000c00d017031002c07041030401c20054070080c01d0031030201201e680011150303504045042c10754021000024502c1c1401e8459081130020120000310318141780c0304118549c1c2c080300302c9038003541000188483e991407000309803c40c850051126401c85600e64100401040070040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 725930530 1250 725929280 725929283
    0x20a0510020606090a020f040e04060605060304260403030221190203090406050303070510050a11040b030f0901060810020705120a11010621020d021201050c0711150304170706020f07 80
    0x43c1d009640c0c0d010300d640c160310078147e405400318424070040005460034034116404c00d1050714007145d4541ca03800800c2039604100c0d030035146010050303421034194610208009200140e49291440d143c19601d0103560b400d0b4504001c00a105180c130a10f045869200603509444609071034912250340b6040000d40d05c0e0000d94103103104510f040c0c00001c083c98004101c1d440179038010044c244e0001d114454200805008261498482e1914032110f103424054000344042e00740c0302003c07602c0f410140032888011000400c0c003822a07140032400e0055110000d51240d000c403140e01c0c0580d03160054903085090074080210701022520211300000b2a0b9080a00000c1c4023407420002c10000d0fa0b241c9100c0c51035a10000e000102401d4060b203038001d42049a111b0941390b0010305185003180c41c0090107800c44400303c1d001903920401240302d0b41000f4240d0b42c0c1402e100011070320840100c4501000145902c4080c1c0024000c048510b0031070700342558102a190f1244d0080000c40d182c0d42c038591400c505600003c0c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 725931780 1250 725930530 725930539
    0x20a030c0e0603070f0518030d0c060b0406081207022b031101020405010918140130170a090b0304080304170c0a142d0d1409010c020a0510020606 64
    0xa42091820b201090740d00c55061030384c070510031404e0240d0607a11540304a428040244a0103442c03040d907141001902c1100d441a42c95041c098400d08215041300e101d06200e511a03810240704000c6281d001a401e200240c2c0d00515030754074040b602c00541583c111214001d0041403000b40c0b0f02550341101c4000b803601d402a203c2c40c2d4110707002461a4202c3c8120f0180300d021544204040c800c4000d42d011882c549a12404c00040000c00d529480462140980c44501d61400506a500401034500c040b000d1041145103088660000c0742e840604802444005403203122001c202c540d1140c0c030500c0c034940141000084141d40e400e1905140c0b105910483e0280e130f00aa06000380340070072400c00101c1e507c96400c1c00c007400600f89141c1d120b001900e03020740e44440364070503060311040341c01c03a800c020b040440d4181d006041c161140395030203041c984d140714018244031001140000140f0b20008841411109280401e058202407000400307114280d00700a4100b51840c480c6030000d5000a02c03903014040403107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 725933030 1250 725931780 725931797
    0x6030d08090d0e010306081c0e0604080712080405060a02012322030908010609020d0c052a07090e06100f051302090301330f030b04020f011101020a030c 67
    0x108252800d500a4401c0380c55036200c004021203041c41000c0c0748035020340500d00410301680d100081864a40e00040142c408103890100681c0d442e00724001001d802801d0341d015003858a441030b40c40d159811882508205440802e4590401031102d0482c2c3c040e0900518480d100da0b50030100900038400c1c00da01202600d2091a1040c0c2c1c00301045405224941c000642c4045000423010380544400d4204100c0901c9402d4001060803882802840087c0c501a900180c8900303903411030205031040d141129060000400452a092394a0103060700d5400d10000b0740c100e88003d070300100c2e140034042d60010403624600944106004400300d441070250a18200a00b0402d031211146200c1c5d02c0944642c0761302a040c0c006038513503040d5036005440d0610700207000284612190850700f1580e8045120921042001e0001215910700d0201c6da0001e045c5261912000500310781e20317009411000341010344200f41c110b000c80c80a80c0703d500c841020200c0d0000a40d200c102c4068040c01801b003090001000c15100d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 725934280 1250 725933030 725933053
    0x70f170102030c0901050c07030c270b011b1b091b020d020d031d0304061106090c21100e0115060201180f0c030b010f14010f0e0108060a05180603 64
    0x1402070b01c3c0945000d00c1141d1a285506005680315805810905154040e540001000c1018545406c00915800090000301007400c0c040f112040b4034000c00c200024a0400070b944641d84c01001e1511945000c41c40280c02502402c00c059544465107030900040321251010910f0f03020340d04044149020798070020a4034061400590310780f00c840a02000591203084001101e502c030340c12402480d242124000d202004580000e13013194095084040829400c1c0240b400d03807001040440d80c041090700140403440b00003030000c2d80d0314040318030b2898103000340540c409105d10140a544050140290200001c582000c81980030705080880b04440d082e859000203205801806030f501c15507403a5615220180b10707581d5048241100a1042e10400c142150200c0019007441e696400382600328080d80342c0b5881c0040890313080e40c80007006410842c90a003003400b03050b0440200c0781254001d0030708240554403007000c1604401d055206a900900310310729920f50511504540d401810f00780c0030340341da4a950 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 725935530 1250 725934280 725934283
    0xc060f0f0b03031e030606040f0b07030228230a050d0e01020a03080a02070606031a010807060521071835060f060103021b01050609070315050103020d060305070f17 72
    0x1441c00d094104101500440313214000c19004640c4000d0042c83c0f82c1c1015117070390303251004940c80d8004803108480010341e0428160100403018501081c07440c0f0340e2600100400345104034500c4800100040d0400c5517160034000d6914100070740510307510403036a0940c054203040342d0b640003406000c2c0102d01041c01d42000755202050040354031350036231500d00e0161940c01d0641e00940c0a0802039500303607a91240480043e00b0b14010100301040e0845d81c124035414044410308100160f4445014007100b009030504841c54555000300c180c1d0701c0d007609441544c540e081555644510044000c462401c5c4c00d020a0b0042c01d0450301b980c0410080303030b00c0c1d0142c000409803144800d048525034040e0b40840d0003d28000c40d00c4040d194444010714001d030802d14101020385612542000c070b0301059440340100481410923440e80d55124070030345014007400d41c4070040c26484206070b014040c10181c001079003030032180060f00903e0003140e0040031502e0540d600c421041c2090302c18050500c14442001c08046070410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 725936780 1250 725935530 725935537
    0x2010605030c0d050c04090c1502031204030c0501060b030a0207140606060403120c0b100302130c0813030c05030a1110060b0d0507120e010605010e0105040311100c060f0f0b0303 78
    0x802400806401540904000c600d8007031031030484181c1700b0705200030741a40352030250740502c5108805125229003402c8101c00445415a40c20f41190300502540e0000420002c00c60342098150901e000203880600f00903002d09401e8100080318400007090080200065000708111402480d095940484c043caa80c2c0d12508140d8990b60700a0050000303102080c01c10100c40300113811401c28401c1c200782a911022420001c4520011483d81303440c08000b94145405443d519050010007000b01c0495220064002000a170141c49081c5c101e01c1341d841091b015240d007043e01a00901280c0d103800030040000c09a041104080095001e20074018044c041c00e80200c1d000d4400318202da5003400c000861880042ca0000d003c6c008020300c4000c0589900300c0303480303520740a2003158004503a46082500240000c42c81d17034100ca040081c00c100800c082200700c40410940c1c203040300c1400d02c440d2004000c4944010508019201901e0710200720b5080040342d0201d0481e01c042e00052101e0072038401050348a00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 725938030 1250 725936780 725936789
    0x60c110307061214040b0708071707020d0f050a090b0c2409070f27020f0a0306052103030a0504060209100e011205040818151201050405130c061404170a0b07020106 72
    0x1b2020000c551414015a1803503400f164915100381c05080ca0384100320255800e403910700141e0032aa241f071031140d511a13144210880b43c1c0c100356141c00f031039000041c0841074503c29a440c0c00004621120703141c5041c051101c0f10800e1428040e03001c41043c4880d081544241c80041c1c10744100b40000940846104605040b2100d04d200d88546800085460280c03805d00444042520750130080e0140b0040410f020b02809241039400161007820003040c006003011811095041030101c2141180745c0d0400401c03a81d201d0010b983c00324550306c640c0b0704000a400795001c00390f84100c0400b20400842d5104a111b40450000d070b80c0d50000c007030043d52400c101d0b4015503001e001501d0401003100310780c0d2190119070040c40d010300000f0a55405109415194014004214218043e50010006071916001315a040301e030101c000d030905080341e600d0810f0341c1c0702d0344100c41c02d021316501c1c21840403003d40c0a4400400e00d481200d21500059401151241038400c0c1c12034100d0314110104025910500c00c080640c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 725939280 1250 725938030 725938043
    0x3060103050a031215170601051c1518081c0908040918050f070816050f01140409140403030c0c020f06090d05030409050103050f0f07060c11030706121404 68
    0x502060302d0071114902c1d0b020300602e400e600c5803001c2d080b168500c2d001704001d02040f1003030382c0d0110a00c5e04039824440706910582c07003100c0c0507081100c0d103800b4150b01043c2c250f005039944128084540c50030044c0004a241101801102070030700144116000280504000744032410440c0401c40412001c859480780701410300641880240701c8a500b5910541c40080e0b64410300c000700b9501c1e51001c0c07a149449488206540000c001009101020403207001c074a000354202d00c56050904003c00c81101480c1800b50410101144400e0f00b4400ca108540140068000c184a8130580035a120714122041d1001c130002480d20852035240c034440c5020080076071b401800c4900c022505005c00002c1d8101c030300c60070307070001d5540c140900140081004000416968502042940c503500303141f401d000e9074200300801500000c0c98112a4080400d403030040c1c44440c104041800068104000d0852010002c2605807082c08070114440d41c11000c140014654427605100c48070403003a0102000009032402800c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 725940530 1250 725939280 725939293
    0x21b150105211608070503070503510105060c0d030209030f0708071a0f041505071505010f0b07020a050603070507050703080a0f0f020a11030f030f090405060306010305 74
    0x128505481ca09404111822070060003240c5486120f080c02114189040f020320240001c00480100340107070f10080200718050104207161001103a03d40018080405e9800c14000800c8001c2e070580b403480e50700c504200b02201514050135080304041e100845160b95408010300001501d00d00390045807a00240c050160540c0b21014000786c002e5000f080b80281e15010700c101c03403070740c3c40c01c1004140028401d00d402081030505d00318002a40504000121401107000c00400e1201520002142c0c11034a40d00100c550074400f20400311038901400f00010600e0035030354007108030f001c90364204505a41209018507441d50380c0e00300690191040c00d034000d4000540f500d080100d840d00344080d544c891031354200549800c0e201d598540c240301c80da401c200c03000300002c6500e0405030341c42050a80903001e107041509010b248250003035a959441c6034002c02d03002400d80b6040c0c4a840922454036006103001c1140d4070344a002e4611000d03a0030021001340202e241c08001101c0789800100c250490380c01c007028012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 725941780 1250 725940530 725940539
    0x70b1012140316060506040b2b0305041d0601031b0c0f0c0302101101051e041b17010218040606050f0d020405060415030c0309080f07170706021b1501 66
    0x6059003600c03038451240802d1020086403e071100550b00010320841d40001d0516040c0104402c40c0c001407502030080842c03010030901000013813403081180d40c00070000d812404062608941501c00c42c1c02112581000110103030f410911940300c1c80c010003090703d0502100c00c10040d607501d050207640040002603621242da9002c10018299080d185000d03c5105402036100c1c0c0224002c01d1001e1121400a0f2914144842d40d00003840341175001349040702c070741ca080c00c201c04400014410181007d00441c0d81a0f0040d6080c1c2040300000700105100092031140300d05800b0704034000c0d08540301c24501030307103a000e007031040b490144110780641c0c205464460800607091200c4501c0c0e040314401d0380c0d03401c0c1d08200c0800c503079a50b40003410090109240c00442c49800550081c10f03102c501e15100141410300001c040040e4600c030035101e0840083c1c03092a03c644150070075410300c030040d605034403240c04009480d030b00344a5036800030412409940a0101a02c02030300c487c541d00d4039440011170008210800500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 725943030 1250 725941780 725941793
    0x1f0f0e100e0406050406060504030c14030c0f06070f14070906210c1205030706110313020f06090901080307050d020607050a03230a06050a080111030a0b031203010b070b1012 76
    0x7070300760301d01070b1001480c5501d85001c5400c0350a9604075030301082001c5020070401ca1203010840150a5040d1844035003c0c1c40700c04207680b0a12003840a10504a0110095468a0b40e00c1551030301900020041401c080606141c4a000d400d81801c0125000b285808100c0300070314000c0c9402c56060191012005000703180100d2013540510003101c1c90b003204c40b000148091407100e4a603240380180081c6076160f003e49413041c12101d000381d4a408001c4107108001522240b861140103a94055440520410f9500000341c800d10403000780e541c1c40340906001107204c1031f0000c017400b2624170640440300128074850301640c0d14a400c60300c04002a8003001840b00d007501c00d800c20001c1c3c5540c40d030488050080143c145c81c451008840c001d440641e210810843e40c42d100c00101d00514503407000f0484d80b4400c24411501d403000508804209490720760154240d242082039120245440002d50f40300d5031640c0243d400c907031100700107468601803400820b1181600e00f00000c00c0300c00201d42c01554000654800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 725944280 1250 725943030 725943047
    0x60902010e0d05070e180309040b010504090c0504090c03020405031c12020a0807030605041a01051e040b070627030809070f060207080609010b060405120304051f0f0e10 74
    0x4a04001c414140001141c907000d0a005080348a103018001c0c050a0a03402e2860b8900281201c0e0910070b6001141e400001c044100c4603545029540802c03400e512000684041c032403940309044c4039180403c0c05100540c0300029201751510300109009002a45004400340e00807800340a500d07804c1b03c410609180d07900c04140320484c6890500c80b00201034031740c9240c100d030007c00710640803400810800003096490701c03030880a801d00320b40c10040240c010118105c80b2541d403c030701d4140440015a0301000d07000306144006000c0c201e140f036a5850700c800c0c0e002c50b183c1104100b00e8101e0b0402c900040702c0c8030380010b18028056080d90032810303119151000c6030464000742c80e46510b40111140424908144c03000f84000c1e10a0340c0081c207a846c90310151502e001340040c28171150380d01d81942c044041c1d42d404112021500116001c6c03843c0403043e180d0500f1031146501803030380903203081a0f040e0310080d900b5011780b100301151100b240e40181040e080e6a800c0100000690064814078a0f0350500d00400c2c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 725945530 1250 725944280 725944283
    0x40b0306010e19050114130c0509010c0c150c021c050607080604020c0a080310060503131b0906090504152a030b03070e0a0b06180607060f051f05030d08040609 70
    0x3111482c1e01440343d07004460f001e8205089680800451084900f003a03604040c1040000d54200190540e242005005000e210105810410038411480034002c1100c08140503080a159a0740d003501c0d150005002485803d00481c001e000c0c41c0714035020000500010305a95070408042e1220780d454402c210340e401c0300200160f034019030900880c000c0c0300e000c02484040600c5164030a503642000e40c3c003c441401d55600510421904100308002c4084562201107034503849105202d111020f0f255243d000354180e00040221340c600403001500c60001c1e04058000c0d03015200500302e4420210815040d01d4000620382c10302101c0802402d46070045080d842035001e401d15002440003280c3c0000790a200c290b9200020030b08021040c004031441c40e218148000b40c0843d03100349440a0200e003214003c00400c1c4041c442c1c0004900c0c03d06006031038200f052440e104240421040c54250742080300c0118651840c0032211107820041454100040c1c04049011240c07a00305495490341d0f2003030040c083d401d10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 725946780 1250 725945530 725945551
    0x212030613021602121b0d060615031514180a15090212011e0605071509150b03031606110c0d0c03080f070801090f1b0c020906040b0306010e 62
    0x5480000c00403407024114481c03c1041480500580c0d004110f006010032191400f59048480981d94421004040000d154001c3e1030406041c041400c08c40e000302010b40c8043d050fa0182e4904000027941a800204115011850400070303517290f4002c24a1508448c0c28690080240c400303038486036108d0820142d10400c0d605000c00c8120f02d85a902c1c0180d20240d12000d40d4540100e40540c0940e48980080c5c05410307240224040882c0700c582c40d101d0310078207100382418410f00003a000c044c04500c083e210f26038984648180b0000c0d0381450200083d903048492042f00c2c0740b4241041100303180100840c1d400041c413003071518201850b070300c0740001400811204102800b040000040c1c08000340100500c4425646a40035040f06504000c0c002a1001b000100200c8086c2c0401c03c1251300a0805070654050180002c0c103010040464001040c804607080f80d01c00204603030180d40c0c0d611041022000e0310a80d810100c54071030790103000c1503848408030107505420200050100c03221405105030300c00380d03144 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 725948030 1250 725946780 725946799
    0x207081c0905010e07060e0409031e0315151719020a05040503010c090f080a0f0b070c05100606120e0d0509010225090e03030f0121051f0c0c0302120306 67
    0x26240b6003182d001208808142e0020941045400d030030007030320742c0d41010030780b401e0107c2d1b030b100e5400a00c00700c1080700a54041c2c9071000d080d200d0038440c3e44444550300d0380c254440b00d02134a500031521848a900110340006940011f001840107002c028240120342101507040510402002d160194100000078010440140000600c070b942c00d0040034144000c40c0c039000344242c00c005003204000c001c1e400510040c2d009051610006008084104503241c0002060900b51103034502110710404400000c3c1003442441041d0120452960280080300c0080d02d403041e0b1865450440425a101d04450505a40001c896410410300070801003a0a04051040e603e88014000d020343c250380e1412000c61310108102400d10481d025403003507030302c0001900011b60440c030340b001642e210020140100d021045442c101d0382e14042c103c003040740a2583c840140d5450403d2002c0c0c102203c80304801c404180f07070800001c0704640c3d0085900d00c081941550140c07600c5d06900080341080d50010741400d40121803039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 725949280 1250 725948030 725948033
    0x21309020d29011e0609030b0408210f15010f052a101b030504020d12030f02070521070201020d0806010c060218040621320601180207081c09 62
    0x501e2800d028001c2d66031110881400460b041380d44d0903950f040786040c020080d5042c408501d122407008d40c0aa40b082c03159a488003039402d100983c107448911120300703010031400e0142200f030a0a02074841d110310030500c2102c01e400801103d501010380201d0000c108104840342a10005c4ca9840d003881e41c11501e02c0d03c2d034013030181c0100d25281030490039100e080d5071003540020001103e10982217801c00d6213010300c100c3c1003d030005181684181801008843c0381c420301182540203070000e05000581c810219101c01c041c0c209182c407200f14040d0603410b00c03800808216080025801d40d440560181c0c0105903105180b40183e44044000e0843c2c0c0c140210021120001500b50000300050421810b003c05070802d0202030009032034058101071181d02c2d901505800c1c03030300602c018548250300035180103d0303140c481030b441c810140c170314048071655000d00d8000b4107403040001d819030486034584144c1e00048840300300c4034103e003e142c00040002d503080000d0300e00540003c2c14010441d660300310004160005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 725950530 1250 725949280 725949353
    0x903080c1e070c05030a0f120e220f051005031c0e010503040c05060307030c03140103020f130f06030c030309121101030c05090d06060602010c020115062118021309020d 74
    0xc2c8811140c447c43da0f0311101c100301030310340c0480c808845814210102c86008000a02c4250b20b82090040f9403100c280030315611a0a4201849803000c110041010f4202610408080e00481c050b0340e000c1e200c0c1074090380c00320071a8911401d802c003096803040748e088083e200445d22903001410035900300785200d10200d155902d480045000710311a07200041e109044c0480034041d100150640300c503002c2d51000410260719000d150003e880b40c102c401d840c4500c031600a041c01803034102020b10b00c6902d406000700801000041c610183e034041c0d221031b441c1c1e5030b5030758076101103020b111070013400d80d182540c104081c1e5000360002c0b05103d02500f441c506180ca9100070400c0803a00340700076600182c43c0d50007040055028440c03e00a42e549100a03c14042100e8038001482c6103031180404000e03005120a00448030f03c0101007a05040207000e00c0305400c1051901b440c0c810707049c0c05911402d019082145e5030001071081d00120796014000c00f003140d1803900e40c0914107002c44880d030100b1403100c030f02292142a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 725951780 1250 725950530 725950543
    0x90402160812061023250807050c0303040326090303070b0103020405010503070e011403070803040e0a050f060f010309110d0c0e01121a040302011805010903080c1e070c0503 76
    0x62482d14598589000003c2081c5503440311121001d02c0384140d114065540041c00b14098511986052540c80f205c3d030912000e401542c0c04000c0b03122840140e59000c00035400010b00e040b41c001d04c100c0b1008040790b800c1645901c66480001d200702c44c21040c0be420036450408440c02040300d101118100036200740800d0660f44065022140120300000610440c54244a4a070240074107070010000581070180c9046e50040c103001e03244a0270307451084854182e07003c1010030060021074060325210355481a10241a10341510f000d40940d06000005020a82450382c06100300c0c8020410103090001500550040c444407000340c0b81000f0000c1c0c0348a054442c10080c1d0340f801c0c4924180c03440f0915100741c4044144040c2c0040c0d84010100c051440410501c0c184c0c0c020b0030550900703220041d1143d181c10f038018043c0001c2600c009103510404428003c040d0311419181e40a501c84280302d07070f034403240a40a8428211444000f00085200810861161010b08049840754940902c0c850320348000034a043e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 725953030 1250 725951780 725951797
    0x190903020d0b162313120308040b1b0a1b06051609120201080402011b0b010303050c0c2d0a0308120910022701020a0b0106110d050f0904021608 63
    0x2c0c039101c00c0c0081d0032400102503e00000c81d00d4070315003440c12582c10000712030a09450780009003002c03a6455102000c8030001c0010504404451a1003100d4a006010140111405c0d14036031807042c00180060140340c01d200b003405224503903500d0110200300a5801130182d0b80b56104180f20011300070001109031151a0048240c47c21040e05034105c0c560003411091517401c00c1810881071034804005036001041c05030060750908007a00200558064031040911944020340060a00c100010600d034000c00240800154141900c107807003014401e1001c031002c000210324503011010032000d07040d41010355100c201032000b0140380321640e0b40c0e203c02400d600101140d0104528046c24001c140304100600d1035580c000e180154245004040e65072007039054410809845550402003046c1c0368402d11030300850076403292074000e441d42c64890041000001441c20007451280280030849540180251540d0074500d00800c0c1c5001088002d00c0042d4020200c0ca00070a50904204000201014054041e0780c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 725954280 1250 725953030 725953043
    0xa0507121109030c0a050d1e200a0506070209040b090c0a03060f0b0d050a080d0b031b010e0d150e030c07060216140d1407050414010305120f190903020d 67
    0xa00b103001c00c05040404440c0118894003030f89408201c0303912103521990160340c03c40b240c480504620482c9040840c46414000c090801104120401c0c00011b2000c42d00321500340c807500b0140b0380b180d043c44410f2290f4a80a9031220b40840010005400c5618840e0b120b045841901ca910b065003001c2441d55007541c00403601e0540301c20080e20700001c10b114203201d01100b11071044070b4600f56140c1585407200d080f8080c04d980c20002e50060101c0c129000070100c03200107012100011017900e4000d10340142c41000034009045040141403d15103c1b036002c21036900000704642046c1c0c3c40d00d1040081250b5000380b100c0380014071442d4421001408410001d007540e4000d0442050031050040c10001c5640013050000c4600010f030100740c40b40400c02181c1a40300400c1444501e24203161858080e030b543c08a170b40103040002c1c03005e40300d42d1000c10504a910a4085441c42c0ea0a1a0100c285009606058911607820700ac0004603200030194540b0001007070820141564a94000c51b200442c50070058484 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 725955530 1250 725954280 725954287
    0xf0411100c0b06010302072105091503100b0f0d091103070b0a02210304020609130e010f0e01180f0c03150203010623091201020c01090303050f010801140a05071211 72
    0x9004811030b803194021405d00c2c04515005403551a020701071035020401c103a802c01b440c551035040340510120f840c03a03c40141607101c5d00d0007c410305480342d801111050003d410760325000510b24030b0740c3c06071210025000302c50341c00e154070145d240005000d21201920220080041e4410381d8400740141d0010f05015141c1c2550348110039006480c1c11410340205080059464183c03034003840f00c5081e240c0081e412500543d0f034015400c0020454044112006140b17460034003415095601580910007080d820201030210b503181040702c50880303949101400700103012882d10000514401611200310b03209110841080c0d860f40c0300c0020030440b0447c06136801d82c0c0000140409a000410b83c1c4840124034000001e1800c542e042040da4065141c00d14081e650f500200a4003000a4040c1c4140c902c1001c000c02908182c1e00f4002d01a003c00e407481c102a403840d20000c0740c82c14040c090303528118403403240c03c6034640710000360100401d0b0081064040028820710810505018011900051000b00041d41c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 725956780 1250 725955530 725955533
    0x20a09050108361f020d0b09060a03170706020a0207050a150905010e011112070308011208071205120708011a04240302210906070504030b0f0411100c 66
    0x21045000c0c0c81d00100d140719008034a20f000c0710000e00c400c426885440100c80c60f00d203040305807070700c070740c40c035810130a6104056840c0d40b40c2e0306a03010b40355200c49000e0a2100102801c14403004400644890703410400a10050000c20091000c07c130071410b0044e86245801c401d511018101c0c0c110940080050704000b004026910300040e507030b00503220b80d030040c02801e4080382000d010300c8076034420141484a00341c051102c42e8001e200030501c00d2000d0041e41c0a41c0a4076070b50305003d92103010202c02107622100080346c00c2d000f2400708000701d6405004681390001c1134540140c5c0d4a0404001010424200103822480381240101c6000d004a5290a1170702e505042806010201202e00c54221550074003040190382005801070355143c01c00300f003503603a10340200742c202c01910a1024600c0303102c1f2441a00c050100d82054003620420700c0c41e0a6400c99114088102c070284194440070702860f0400010807082c403020140507402503c103000d41c146248401d4042b5903111103080c4140089000000b00030f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 725958030 1250 725956780 725956787
    0x1c080408070e091c11030403150507090e0109020d020708040e0403110303270312010b070c0603050402222009040501150906110f0102270306061e060d020a090501 71
    0x40c08409941c2d8219140440d2030b82e079102100491043c0c10703e08809601201401a10545070200900d020741780e5968490601c0701c1c03100c030f0442544480758681000034006a00c1481844c3c282e90800000010603440d0907005400382d01f003092030036880360342000280005203120340104014010f02c50316030354034501402c0c080c1c01c0d94031491003d00300c1e400810400ac040388591500901c002040300d140b4094440c0712014900d10b00800407074601d115607882c0041020503407200540403684c441e284100c0281d46581c821816240150382c0250000b080602c1010310000e10900b20b6280094410005000c20501400284c0000c18401c4490b08040000ea00c01890405006507405031010031059803140c2c14682006040310300c0fa106010401c525002040d41180c01842000d2008400c44000d54907215210300700320b5401c1440f890220007242007040400382d400c0108866200e6100148011114030301d9120407901b1070a140d003495405041002035079481d120b1480074101380140c941da0000d0040c1410b0024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 725959280 1250 725958030 725958043
    0x2030604171603320f070516080c120f0c0f0409020d060b04140603030d020c0f01110a09090b01021c0504030609060b040e19110f030f0a1101030c05040e061c080408 72
    0x5503011345040da1040424000708044034a500b2210311207640d55100c1d1f0608504222001c054202150301d00c850003d5041c4000501e00002c82048551200300c01c401340010380c0c0e1302c08200c10003030660415207049005240040581c00d032154090b002090403100ca50008090300d40705c03a0102d5030165a401c0d504414200f0340304000d0403009903613840d040e904010380000c5d0389001c1c03800070100f02d035000540c0071580e180c184018060740c009580207020044010300c0c0c421194200c000d083c00001c5c8148400100f601c2d0034020000e41700030607000f51516010300e03031068850004003400b000601800b0800040060381c02d100d20992103015100004003101d64008010a1325600a4118204e5212410403160940d51b034240800300b035031022031151225081c10100d06400c1c10304c541d4a515016120700041c81c8040807030450a9144076410003d40d4207507640055080b140e4110b90000002c1e0280814002c0f4256501c419800c03000050041c1c0d80c4203074462000380d115016000c2241c6680010604006180c020400d2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 725960530 1250 725959280 725959337
    0x3050a05010f0f03060c03021c0501030203011b0806010f200c0f011107060c020a091406030d02070f0315150803120f0f0a020a03060510051e030402030604171603 71
    0x8165a0503e4201030f501840080c0c00040c001643c1c1d840080300f1a0f0082d4101ca00250503590046002c24116900c140144000d100980c080d50034003d2400c148002c18000110340350b12070301c4804280e01d800004491003101d0845400500003030000b8050503200100c0f101c2c00340341001004002900b5400180114412000c4540381803081c00c00b4150700c1250040f9590003681c0580c0b8021482c80c0f9540001041030300c980e800200014507140c0c42c4078116071443c6040d4420202075003100c2801d40054001c903955000740c810074403001d00c03811042c800107a8505400d04803004090000c15840c1c550352040c0e25414240e4001c031569440041c2030056100540f41c00f6602c2140f4501c0000180f0781240c61f0207150303100407c030b500010303400100c0c0c90403c1c0c06a4401d5001d007401404100c00100400d101810942c007144000d03c4a051100d40f1402c5100003a0490348101c1e0f01502802041e1943e58810081d1100a0207140c1049030a1012012000400440f60ba80034003d55030a105c0952107160b507928000800344 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 725961780 1250 725960530 725960549
    0xf070f05040207050d080703140f01050906240d02040806010f1805010e160216030615050402030411191503090c090219080a0623040e0d0207050f120d03050a0501 71
    0x10f1404100d0101d10400411701070b0800460559500368110014204141121407008036102804440a18001154141c50003a1408006600e0340010089007175603280c500c6001003500e0001d50300704100c410190143e0b0040700005800c00e52183d28090508030240c100840000c443c0404001c481c3c91041c0b00d15000c80061010086035040550b90024a03000602406d07181d0300180c1e484240032301c2000302000c0408109542e078034480d202d141c4000a0503601058842100f00008081079514041c402c0702d00450b407000392601d451907074401b400030020030071011080c0b103c40d94000081941e20300c1c9038118400c2c219900001c0310b04251030500100c00054019844442c814002424507a103104d40500d014810390a014074255540c581680240c031454100e10340483c0910804030713210f14541112400c1113030889042c803428406081880d6070b04403002541c00141c0c0205010040390900c60005440590060103244984170f40701c002c21300d000c0705442c200001a9a440030003020704124030030140504004103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 725963030 1250 725961780 725961787
    0x30c0105120f04080d050a0b03010e1b0d050c0901090b040f270c0807030503070c060e060d02030703090f051e060105012a0c0f1e030b130302010e0f070f050402 70
    0xc004040100a02d0955007031180300119090006071000c1e61000c600d0088240000c0c645219142c0240c000c1915681c001e6003009032244207448041015050403030103124500191440c60100141d101b61040300390342c2c0380281040b11401c1e854112489010708034000002c0361811360501880111036800c140f900c2c02501d04224652403a1854500355a000e902040d0b8200406007418944068545644044200e00c50141c00004000022014011147c020311091803210760724a02580e45044051240d07510000c108185a48040264081c40d0060030901c1c001900440594480b40d0b501b20043d0284d03410390140608040605403440b0445088407128003a01300e1b94900000038110910151280c0002c030700181d03081020b8101c0709a00c081d52071b08015041001e41e0703160b4502504182c28001c003011403440300c01301c6402111120500c002ca030380c4606440515924071080340c2d06844444001c034110b54a036408040ca403602044030341c001520314000790002a03c2c14010560a002591110740101e0050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 725964280 1250 725963030 725963047
    0x2041b0c1a07141c05100f0b090603041e06020708090909011a10020a0516080609010c0903020d0501020d111308010b030715110601030507260a08130f14030c0105 71
    0x7610322040c00900c00c03100c3d5240d04010aa4858072108881c05030700240c500b804101c42d0303888440c1440c080b17808001081c605141c0301c0400c4002d03440307141e40860b086032003000441c0015001222281d48580a8a04c1070204a015a41c0310182d82c80440199040b460103e20301d1924500b402c6c0264203c2d241e04001c21045101000202d190241021400c0c820003d00c135880c03a10500901c0100030840d0700100b03603046c982c40140f0310444803080b40540c02a81c0315807000078600b010148500b400d10b002640b603074942c2614650070012207649264048440703540034407140d02024194002c10151220100c503c3da251501d00504885948541d8001c1c01c21760304080c41c03298680c0b0701003000c5080c1d460402071500250071911064420403c8410303a8019486442c00000903c200810032906407005845411410000c420014080414003410a2900d0700003900003400580140010403410000c42c01c060051603032100028200422070f4801024602e8800c07161a180c030742030094600d16182400c0650401302d25 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 725965530 1250 725964280 725964287
    0x100915050609030a140105160804110d03170901140603070e150f10020f010606050415030e120408100b220902030109080304062c0c0d02041b0c1a07 65
    0x9100e414020000007607024010340701409079007645a0005160300004105600850003400d08594101e81903e94520b039541c0648108045405207410a03210040f40c080341c000c004101e40c400304110280806404103011601001c2c40d102c0c171480b0850000a17801c0941103400d0480080240b1091003500580000e02104410580c12600302e01c0310049030340c4801c029000f281e804018008040c1c1d00c4141040f4000d80540d00180749060f1121030002404170b99074a00f0252101e01842c028011010f89034011401460f11a90010414000b400110360311031029458021059000c5d40241c0f50769044050b0300c60f11400c0030700036103544400c01c1d174a90b0704802514584a140709e140a07000e12142d40c8520420003599425009070740300c3c0741c202c800305540c0d00b418540b52000b00104030074102c0c001d508040d00350a13840700b03a0344000541490400f420441251030100030002c03010710701c120303446541c0da0041e00c990b00c0801459030540702951030f0040041c4450610348215003203014568010b920344410020f420380d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 725966780 1250 725965530 725965571
    0xf0912040b160813030c06050a080a0b030a02090106050c12180603070201110d1a01080c030a090812090d1112040e070c050a03270e07082d1009 63
    0x9448903211800c080211101c0b8204150151a080740400c000049600d1150301408403407041075011034043c1e40b0007080d65640203288646010401550005016100940100c0d100c02e07030080681c0d03821025580043d15085003030b040a40050000f041a440c00303081088216201142070f00fa59061050303413400a45607031124130805000c0e402c00f20104030302c0d5000350003640d8001c2c0e40c044c08907211030600910f00010103c4c900c801809540c40c20801401d54041d9440501611059030307800d00d190741c0c140400c0c014180e00c071800c0350421000c20020622141500d1030700d0240007024003a04da140c41080000b004100c03500c603aa80d03203170002c466aa0344201003908079400c41c3c41e40400c00c0c4181e981e60034103482c4820782050141c40303405a1107410381019403054000078200d2010f4a004643d507a0b00000e2f244900040c0120755445086001082c11a4011020558000c0ca400540c0c102c84580c03c525034030740345441c030816407050784a07800e02c4101e1690140000140580c424200091440c580e0030720f45404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 725968030 1250 725966780 725966789
    0xf091112150103030203130605070209220807080414180103110a1e0305060106090b0d02030402031e0a15050702250b070b1014030607030c09120b0f091204 68
    0x40d0000e111240041407051101000201c1e03804009980d407420040e480b40d00860101000241c0c0d4500811a14003940035180c0b99500a002c46204c1d95802c030440c020300c003100c10721204159050140c1000030303018100a04140c1c7c4a11002c40d203071482c001040c1c2410b04110b81c224460307801005440c0303859542c1c10407181101d4011642169081054001c141c0341c8585400034144581d80000d20b0304c10a00143c1c118080324828030481d200750b82d03905400c8420031024042c03048240e6041106400341501038000e0b54000740001c0c1900c2c031520754034125501039404210400542e0b0003202328081800310510901c551400c0e040401e1042c0d107040b080007074683c130001c2441e01030080f03644508864681341b891458054007031f69022503501e1500742000c01004200311164140310581c070b04041074500340d0041c0845042005401001c1545400400740c0c050301c801c02403001000250080001c101611300380310000c2c240511071a11640c142164503100044006010360000da00c80d80200b44031000c60002c440844 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 725969280 1250 725968030 725968039
    0x305030c090f091303080c0a0f0c020a0f080a060501150f0f1106070905030105180c060a0e030a0305040e160207170307050f06010609090b06070305160b0c0c010f0911 73
    0x510410300040d80181c00b0421140d0409040c00810004a54203100c4203034890080e141d008031684d50004051a40c403490340e10300b00140650701803100e00c600800b130908989100a003411001911101a150750300e10313991294945610100e0405c2c1031102070312440b8058203000007031b4181c07200703140009022810301110000410910280450070a4400c00140c100280c40c001650714600385060000c020603024000c140c82940303094041200015460b9120b6545442400608150030b90601007040941100744110144043c6650100303103a6814020a0380d114880d84800e51281c0c20704c50034a02c00c0800812484005010b014400d03141c6400040c90012a41048121058034095034041421801003000040803407240e03150858403140081900340c16500f050350703003204090b42c942d800800e0341c0f8280c00c4290024400c001840c0441d22410092400c00c0564981e280400110b5803440c112a104981c0c100081c400030540b850701000a006442e0354107120320301031168142580b00c0c40c100c44109005035104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 725970530 1250 725969280 725969287
    0x207140114011403100c030209030f060115030216081611040e120c0f1e0616080f06221e020a0918150602070305010f05150d080c12091c0305030c 64
    0x103a99003001a4407441013003c0082c0701582c428131000d80a508015a20b030300c2401a20312f8400910000282c050484d03840c0e4443e91044038038268194025400a41004030440c035084208011456850080c0014021101d10407004200c1c0c0c280342c0188540c500065200d182440a9141030990010341001140c00808c40a035451801945151525030345a06200e0300703004504101482c1c0c042208100801211202910b44507a03440e000308075118640c0f00b4000101d8166004141e030441d1052503254811406840b044580003032081c8440c0e60304a944400c800c1e03e0300d80d0707480c040d1000c0d0700d4050801101d00c204254203001200a000c0d1981c0c10a00a0030a040f004c4000c1d22000400c58000400980c0e000c40100d0411740c4070342d0001e488042c0e60009580395800c1640d0300e0740ca5005031107900e101c0d280302800c03810300120310300400c000400e0390300003641c203d4000d120025000105010804240b0800e420443d662441d07031b030601c0b0702000d4590540411b20140a00100841d0b04074080b2641710312055081ea65 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 725971780 1250 725970530 725970569
    0x60e04151505130506040605040c09031103150a0b030106060f09062a140c09011a07021906020a02010917030906030c070b0a09020306090f03040b0d020418020714011401 74
    0x8400c4550350041d54441c418144403c410022035000701e0140d44191303421320820f5141c03000d200c261202003090000151400c14100041907110803105010302000301901d074a441419511030300406c09440c1c075002e040d915013040e4090301d82481040d00038200c0c0c2c14401c00d00030400401034050125841402c1c01c0c03191500e03c1491100400c50098900001ca00f1556052015800d1030b1486154904a00c419440394a0210415103048070081d4100c0b140f581d42d0070048800522850440c2c1c00075101241c00503064940f08da580d4a40c440008040c0a0715801032004103e540001444540503902100e0441c0c000300303013000c4056000c4129100a8000c1d22038550326150700480b01c03031b076200305000608110045001d224880b001d0350041d000c0035008038111043ca80720001c0c07160b1034007811211071009901c100010090701c1c0c4940060040c14403840f000508140d40c8485403600074482c6481c2e1050345600184c480104803800d041c110b240180700c0020001c0c030007401c00c9200400c0043c041d82944604d103811811 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 725973030 1250 725971780 725971811
    0x9030d11060c16080a05041a04050d140a060f1b0c080f0f070506010605071a06090106080604091b0f1a030106300e0607030b0105180d050303010315060e0415 69
    0xb0b01394000c26840e65848020001800c5801c1406280140317161788030720b82da4102d5802c040d0340917110300403c1c8007260003069656402044140c41e0306000c0703001e10040c175000302c1c0b118030407028080c0c2c00040c00316284060100c0d00079034125540d03a10003071105034a201000f2580703d000395507907101c4606003141d81c0e69400c90f00e503000303024000c4001c000d4030500b00040f8005a01102a0440e1440b506030900040942c12800000354000c89600d600104524010032500d44202819900414040d00000e00b8605a40b105480c10004c034642c854505e5038010100486510710052500500c0454030705c0300040100700d06040d9070312043c4103c01c10404150513442111a440f8810f41e0600107154010000350300c01030000018125080800c2d4a5001d43c4000070b000324020300543c849400c05070349103480c219104400c915200782c50003529821041428040000810400040d4003942c020480d1300034400070098810151643d03908180d006003036000c28800041e41152209442d0503200c440031803139a0002601c038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 725974280 1250 725973030 725973067
    0x203121b160302070f06110307020f04320a090302060708060103110a2d0c021203120c12010909080a05180301020d0c030b0d02090f0a2009030d11060c 66
    0x4400711000260204041c1c001810000b1a0310480000340c890380e40303a07025144000441c40460b45d0b904100301c80c50041c5461800d50250410082002030806408451441058a522403c10001c00304030074000c48440c101402541c8070309000b0050181c060301d950001c0d1900740c090040d9003401110710210300540c1c0250410f0030015209030020b5202e90709994000c100544802c00c4022021052200d0b40f640c0640507100d07000600c5c030392100c40c4901e02d59424480c502c880343c3c28440c402d0109004043c1c034002407a585c5401210341284060b15500f2a0003000600340040e07024140701c2c5c0c075042d0203100107880081695661419814195165060a07003400b1022070b110720750707075415480050682d0181c549a070001201c0350203560104600c0344240280001d41c01c0304030000e0350042c0c0e0703400000c3d0814220b205207076104640e0407020400400072500a41458a0700801c170603210000700d06d20040d41020084405110a103251490806030b035081040d49401c1c000e80400d000c000c0c00201e04103045c0701c0d080c07031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 725975530 1250 725974280 725974297
    0x50a0203030703200109030212070c030506010e040c091e09150606050a0f170115050f12010914061e01030b03070b030a0b0a080709020306011704060509010c0203121b 73
    0x141ca60318201468024a40100080451080d540d4842c40b21800e0405120310240954160014030790b5080f5000d03d410f09401c4880112016414008040009001405030354000e180e0250340d213640f41080d1030b01203103144064000401707042c94000e40c10406100111602d610103400b031400600404c5600b07007100080c0b41d0540081409003880ca00003000d0398048010824029282d55040540354141e07000c944128031040b004440c00000350041c40780139402007040b42c00e10100e00f025440d01410b148441143d8100801075003111000c58010801480c2c0d0740030b09601905945200165444c1c040000392841c2c18041d00c0c801080c200e2007210085034042d034045080040028110b4849940d211420300241d4402c80f800280305042a007100030600303000944034269060b04000d025141d0403e5600030080d040103010b1810042281c0f04001c040c0301640000d03014502a000204007850130101840c01d40d008883c0040465004125900455031001045904441908405000c0d031010141c01181d50284090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 725976780 1250 725975530 725975533
    0x50a090b0411010315050a1a1b030406180608070c05070803121608090a0f210c0302070f21050f031b010e0a0c03062a02010c02100b0d0f050a0203 64
    0xd200070320882c2d02c14400c08080076a01030055002205034008002054444c180d00802e40d10820b1080c1656803007860f80c001030346607003c0e0900750810049140103130705e00c1003940150000502882aa9440303500400c5050800200c5004503107400402401034000600200400c10344045c0a0100a024081580240020720440c2d8403050710f40d80a00345413906a58020f0b12115141103103003a1030151100c244901e000c20040c1590f050300e42c0b134000340c003400d4480450f900c02184000201c2820503d0790150312201d04c0c2d5951002000614019242003071681160444140040040000844083c000700c11b003a01c42d240d020991302940b03807040c40c0c00d010b132240c0c1001d40400f2501e50780c0f103e02c055501d4034020001e4001d21442090324100c5803030300030307500025264071122001400811001c0d0031841e400341403220040c0841c0e40310341030744840c820545070031001070f519465626007140d0b0411050210000150041001804060016041c40e144100040501c2c1d1015410720502009004060001c1e40140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 725978030 1250 725976780 725976803
    0x3021804111b0d0503040f290612010e0606040c1704030c12030b060304030e010e10021c0e030316020102071a030703050c12060910090603060e07051e04050a09 70
    0x701d515004816031030702d110304a48142e40b004000080c0c2c203421501a0301c9031403941d1a59210401520f503182402d8981c003844c0e86080c030414400d542c54190102c1c0d400c404580768140002082502d003002245a103182e8141200c503203801034080341d402c1d008401154002071781000c40d9425a210010032411041074141e110402040c1600040d8807804a0310801c21520304440044050702124603100015030020010300c00600000d020710100c05650340141010300b0140c2240b000540d8034000c0c14850320043e0065801d8044021503100080350000050a10300040c0c560440402d84c0c03401005400700515407440d02c50015079000f400203601400d403030300b405480400000310b070311115401541d50f80e0009140c0400104103031150015070740318880701c0208521a40b508806c000115002905c10a003c000402000944981c98410075008500c40c1c9000b0440c0340142e402c4505007a080da100e43d001e41c0e01ca119205401c50800c003501212a801c540000d1142c0f0b408481100500728814004c111140070b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 725979280 1250 725978030 725978051
    0x51b01020c0c030c03070b16020a0e07020f010e0f0c100e09010f0f0b160b06010e1207080c0604030203070e1f0b120105270a0f0c2114010603021804 65
    0x1042c1e40365001d00990494080d412400281079030b409491084640a0b0010b00c100c41400304090f40d2242001c0c001001109503580b0344002c3e111b5800150341150141c3d1000100b03940f805000e01030360b02400f1100c40540555490149013035101c3d6960840305204c4c21000602c2c1104900072800030640c0d5a0184c07010030690386600719843d01903458011106802c6040b8070018200c200c4030304440140c403e240e4280d8550015950305041030384081c1074070303050021603840f2515549072440308080c46001440100349041c60119424240120707082c5030b0340500700800081c40540c40010701642119988000c40040340d40301102880762042c00190220f00700103041c170020b00640c0e100060300f24a85821404811a40e0b1401001001c0c4d62002c0604075104a0780b0780e80040f203c0c26030b90a507001507603500126201d8482c01d080381c1107407915010000890004804e00d01c2d41d01e1880c481e201b241d103605008100e00c2246014908225505100c0c1c03408040d000107041500c600003c90b480d0400d14050b100340980c4041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 725980530 1250 725979280 725979283
    0x60e01090b0403020f03041206020a03091b03150204060203030c03040c03081207030b010905010e10050d06151409010806100e15031602011a010305040c24081305060106051b01020c 79
    0xd0b90150014814928040f42c02034004c0215401c40740314001c50705007842e03e03903600d101075048810700380d09141d51444c081001c04c001c845840004a81c0290742030341da500f94500500c40c2101110350000342881400b051084540000c1200d0b0407403140c02c0b5031516542c4d145840b0080c2c0080d504002d0000c030010071048954010700c101a4024030040d1020b00004039094011a0740d10058803c090000d02e078007581d40d03041d040c0000e44c80c1d102d5400d4945586465404000c0400b902c4907980b0204000780406001d402e11507200d0380c103524001540d080580b030300d00030b0000202100006071240307101c0c5c800c03503100107402805551a0300c00c810002c2c058220101c014040c5008030380085030381c66800f132403a203480e0340d49500c18030403286410031000e1981e00d841341d404011002414000c0c400c4a90060005e0041212182652141d44011400003010301c0168040340c000c0806801800c06180c00000c0a21000002c10100d0080e05541c1c1600d0303d16110900c5120341d6500903400303811182694800104e42444440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 725981780 1250 725980530 725980553
    0x60806060906090745090b0303030c0d0b041b0c05070f0303050d02031f1203020c011706010f021c030501080d091a090303070222110a0c020904060e0109 67
    0x9003201d90300720664606091014840c4100c40c4040020250303030445142440150300b141d680c0100f5071003000001403460400205400d294948804009221400c200a503958010f902c038070007045e0095030650900080150300744c010200040c1d0601c3d11140300e552680c0707070fa81c011054400841c8a891421280d010040c249075004d24090392a409058808540714518a103a01c044039030658400b45004920002c060003900082c00071102e1550502e20301c1220302d07401e05100c0162040c1c88440ca000c14040c5001b9190140392000070341440320300380340f154403442484d0596500000a0921070044800200201e06103c8400107140050181880000c409503156001e5416216a602100e00f00900791009464440c03161144101202010074240000b81004001c0e290710080601100c0c1031510755400680fa0314103148400c036100200071495200b8a4190045205003900c400c04240340008040c401080540e0002e40179008940583c0401d08021080d0701c942ea130160b07000001c108102040c9000c1e019400d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 725983030 1250 725981780 725981791
    0x1502030414070602030c0a08031f081e010c05041403070b0415090506090306070f0c06050f0f060a05012f01020406030b031b01020d121407030f15033201060806 70
    0x10a0002c003040b1280004115140c0c180e071000200024409681c4031800340c1d0004054182e4645000071001c004241962044040c0800d0005415040c120075040c80341c1e041201d91080007a07041c031314048035158100c41100c080d81c01d0a00024510900c140101e841c0910341da21200c0114030004000801c1145486104c002d821a9960001c00d15510f204014440c056100801e5068100c0e1001c0b4040074010200702e610402581061900032a06460b0007040740c0c01212160110300101080181440036810a50782c08a030440e84131514500b0400000c004800103000001440e0f04510f4ac02c0341c0450740d1202526040e8094003e56843da12448000e0143c010954194003a22603201c0407070030303900141c1414010304010b82c001c00034103a03442011903e0780311070118026196a101600bc0c404401468840d104070b805171800b043c1c4403800c90901c0104d4003e000c590344502c0c90f4103c24800190303148600c54030103101020005416040369041c0c0e265100d0038416142642c40c0c8040044c020300041007103845003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 725984280 1250 725983030 725983033
    0x3090d0c090f050c03010509070c05250b030403080411060d150815150d06020f07110a052e180e0403170105011b410705060304030c1502030414 63
    0x2e151610305441503d000703803803038000d080081c40148858207203501525489405440d01252110a40d04c40c07906100c8104015641090324040c0c015a140c1c1c41d0b240f45000b8010390075020710354078180e280201287c00140004007661080c03800c041056882009840740c107040e011082100d80d8a58480d001e91600364032408505008a411040b0307950000309106214110380d95144584284910400800950f15401198070907824400c2e400300400c210041c10419102e41000d64420490404000b03210f150f07584014443c04c010b40b0605240b60034040000c0394800d803000c0ca03009201c4c130100240c8034804c9160840400c0901080005541303212488110b0055000c0d4892000c143e441016800a10009000c2c003400724030110540d407910105010903417040350140c50311450458501304423100c00101031008141120401c810303d1045003510904020f400d5241c0004d040d46864100407508500000300301809100d40b440c40d10f800d12408441c0c00d82401d0309038100315078034901441c190b020780d44008000d6425 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 725985530 1250 725984280 725984291
    0x17180709021209010902060f0733060e15010809070e07120b0109030c030305030615030a0209031204121401020c010203010909050c03010621050a0b0a020c06070c0f0f0503090d0c09 79
    0x1824040c411642c0b451b4000e80032528000204400740d40f80d60003203008469074114020444000958070b002d036081c02610b1000c1d01d140c1601815460300b0707903038142c2013901940c845030300b0b1050b40050380d03401214144081c246400e650b81d5000340941003810b2039204110112020302007204107680480d001006a940350030070420004454011103c8010902000304204a20007044c800700c0c1c060000383d40e1210f0000c0140000d420f0861100000d60800c1d11040e0103160040303542030480c07030180080c942e0260032a1007a800c0c03d140c40c0c0701e0b0a40c001c5051020300401c2c0855082010290700713404135030401012200a5642e547d5440100d0014080300c081a200d81c0134070b88212400d4503042c041c0d0747c104c64103004c000e07550700100c21054140030104c0100f1103180c801d03024800300180281100c0c0c1e1050580c15001030b21108540391907802e12500401403010000381b0221140001d0700c03600543d2449400103c076003100302152404524600c03074500300790341c8442d500900d5410061035014840c15a041410148074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 725986780 1250 725985530 725985541
    0xa0206070f0503070507030819090b01090b01031a01140c06040f030f021c030b03031c14010e041e0c09092a05130b030102130b0304061803171807090212 67
    0x1040e0109480c1100000c504100c1d1b100401c0c400c46049810a2821000701c0c10800700455030b80444019250480d04034034060010000482e00d403146800441082c2018083c0e2951480d0324007900c104188200d043c4502c0441c0609066181420744a01ca56200c046900c2c50070b05007031255540c070880204800241020801a0703116201049605001505011100d40d40901a805401825007002410742512043c0440c00303040081d101428002243c0c808000f4a4011207000000044016006500b05030f1018082c08009040b04400340d1002d4a050380300418035003540703419039400c1d42039488110b000382040d1007402400710341c82d0300305551041c50744c0b0078104d05904110b000403070000384076880e480101e440140c071480d8255000207040c4200140018901403814040140010f056080604807400101c00c120401c0920700c078805020040300140305614040d5031f0b0042c0200c890030b4031f100b071689510000ca511048104012308a8607143c50943d5200d80e201c002c2100290410040d0f2009900034001082 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 725988030 1250 725986780 725986787
    0x60b030f01051f3908040f080c010918111206101107030b10080607050304060606390209011806140102060601050c0c060412140c010e1309080a0206070f 67
    0x400c84011922810b654640b101184020545840000724403820320481c3e042c00c1c1040c3c0c8165034081031055052548035404c00d51f040038181070940180c484ca520281c0200d13550f80e0400d494500710342c4075200000795010300c5800d0300040d284090074483c40c800e011a86120706005a645584a580107a4564100b101c4841003225007181000c00240ba94000c5801403020030446c83c001c40d80200d4a04141c1d58091741c544449251820403103079100050b9001c03050004000860041600504052414050603c091000000c0381c80361050908001e009051400c4482d50030180c00480141d00107000042540e9143c0860b034807406406c04074243e4510308000810019990700000c2c0111030113030700404441d51032400566065220702d80090481c8104409001030756034010040010b803d490071490150410351a0420400e41c003494018202e42013004101941e0764441001c1c1c00e1031804840da1400c41c1100103090005044180f806412201c0005202501940002c0e055000e14115034900e1001c038510038044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 725989280 1250 725988030 725988079
    0x20a0804050c18060411070209010603051b04030305040e070201090203120d321009150e070302120a18020a290703080604051806040302070f0603110913060b030f0105 73
    0x10683c0748050404a422030030964441c50b00c0f015031201c09403800c03400d6000201e00740f00136403204001030745800801c403441003001858806c0f2040b01001342d00b064250b5a02400038011402140f920005090004101c14401d4200d01e0400c0c1d006416240103003000c0c00300254942c094480d0142c25400d00400140c000c48820140500c0d14004e070525002d02015440c4810310800035000410290201c040860076107402d100c1c294100d501860969201840c00e200c140c51003070011b101409151060000d401d00c8543c0c0b2a40903480405a4400241c007901040c00c07120308001e4540207504800c0a03000420383c0801da00000450802c100400a0401c0c00c101d0a81024410300700014000b0310301c503001c180d0500303282d00110307045800e4521807040944010b0445150880444007540180e02c0000c04001603034402c80e60f8006002c20786010700900c0c2201844d15040c1c030910711418042e0f2016031402540392800d030b10003800b400c50400003950342e045c04070745046942001e0186900c10344101056039582070302c40222 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 725990530 1250 725989280 725989309
    0x706020304122c060901180e0403021002160201080c1c05060a08070f0b0304050102070b1e070201050702030a080a0b090403021606031401031b1806140a0302061e0d020a0804050c 78
    0x5190b10000c0ca40c040c0b1206170000b00003541441002c0007500d29021200c6400360160580c1c0f00070210303032720f072509000749001c0314030300c158400901c10001400a00c0c40c91001600494080c245599a40c9030000307062902e00c608050010300e1041c109450303200360141d030401c501403c1d01b1144109040d450328603140d26075516201310350140504140402000958601840d4002e020b0000141840c405440f0360004120890b2100d205030461012a900e49002464658225447e880204150315003003401948c0e81c411180000705101c0003100081d01100140c001c004c01c00d4001d0841c48045c2028540659a41403100d500f54071900d05003c04905540b080c800c1000040203400031210503443c644881540700d0901101d02c00e00c1304214000314601004040d07000d01c0190344140080c106240001c00f15020011100c0a1700c2208020804c0026030350300d03801d0302d04103806080380b1802040100d8180b50715209104100685a0000c10081c10302a00290040d1181d4028002d403003042401004010800341c40303002c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 725991780 1250 725990530 725990597
    0x20a231501260304080d03061815140f0409140d050306150c1501060806190506191b080d180c0621020415112a0105070602030412 57
    0x104646081c070715076099040344100680345001c2e102c0c2e4417941819072482e03024020a0302e500080042d100041d01140410304408000c00c01e10040307420207201c05d26144a10042142e864031320351b0003070f44c800514811111004000300704c1c41074940b50030502c800c0e42c00d00e400104c1c0109101040c2d268001c01c212841041c2c01454000c0f07550320041120156005641c0400300c5101d0494120714051079440c2c1c1601a02040e11099040c1c90188100701d6071030740203000c4001c5888111010401a1504401e40300c03080c200342c801001d00c244054049035491030302d0301c0401c0329420500c00d8006002101000300100c03182d2010902600d900d401e03180840305007202c0001e00780c0c10866004c109a2344644508007103030700c0c90b150340000424003408541c2070f84c00941141711024800581484841d0b002130241350800c034001c0150015696a44e2846c4480d5541c40040c059001d462a410003240e10075411602850f0340404110f441e400c06003040600c0100300b81203640480d50040c94420000d40740d07030043c04004100c95 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 725993030 1250 725991780 725991809
    0x50a0f0501140a231b0703020a170a0206090609090106080f0a0b090402040f02090307090212071b061a04050c030603010b0105042303011d03070b0c0702060703030b01020a231501 78
    0x508800312104812480000b601d8180205c00c0400d0305260030001100110b001801200e080d401088200105c81c0e01840d0f00414098001003040b00100700f02514540441d4520348900700d110100e0114464003400755800140c0c0d800104280d5017200030345000e95001c9101000540c0d43c603030034104491501080580c00051000020014a403e42150454400300200035007080c404401181c50034040303400011440343c0215a0449801894400c1e40c0e00000728070300101b00e13102e01007804181d59210307403000e4401502c405140c6c0344019004580e1a0486002d0010040c0c1d28014618038455007054a070107200754213101c2c5c00101584141e0584081d5020301c0004d4032880c0264214241620f01c4058144c0c2554a80901640541d010019948510f01d80350281d90b1703a00280c9080007840000515910348094280144805625080c2c1502c9140d070349414002a01d40342031005030b2802544100080c010340e28a0380d048103000e003d00f00a00008403c90843d010703451030556560404009001d158070743c01b21032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 725994280 1250 725993030 725993057
    0x215091227040501080304051207050609060d0605101205150f040c170703060f0b070c030b04060212090f0c04051e1b2803140a020a0504050a0f0501140a 67
    0x16500300c0019070a80e9541c8403a0300c0c0c420003040548a00342d10151164001007400c2040f070400b4034210700000d0403400501103190801000403d81c0c01040540c6000f090045030700c20003149264001c0018280040c0003c1d640d0414803002807043d08a11641c1400b1801c0c400802e603500f400182070704a400000700b1140c0e181101d601440002d1615080381e0040003617440902961940084231140102ca882c2e0300429041c0c203000e2010801b161a5204088030802000802c0110f00440205c006070380c1d0001c5000d540f51114203040300603010305046111903e02c8082840801c402c0010003100b01c8000e001607404003a0780c9410170089a2003103400c040300d10600c566904840402440090703011403544052520503004142107112900301040313201c004084107117031032140e800b1010011050b08903442c4c01d00c00810140079000030504081c01101001c0d4000c04c2403071421303000318103443c041d000c040c0250b83c40b01c0e960008200182da0500c40c11f404520f813001414030000038501100c0320b50f0707210303100c250100005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 725995530 1250 725994280 725994307
    0x141507050a142103060306060910090207030e04232202151207020f1207050a1104061a03061c02061615091b06020706020709051f0602150912 62
    0x50351401e00d52401030f081d040c4484a202621007001d8070f414224a601c0c2c1c64440c0c01d061808101401705841039024a04000500480320005810b440b07102c807004d41c0311401480c003a07a0800a40390230700d034000d041081d060000c502005600c0b0000f20340080040103900e85000744158150b050421740445071890f6403020140c1880710044170087c065a901c50700d04044010002c24001c019584100140c00ca403000c0c551102c01004502414560108454079060055440c40c0d07407a00c90440c01841c8400c0341110b52102e9641e580000020300c040e000c3d020b44014400040c1003664811100f0a1095068100d190300030158070400184080e070280c0420b15228046101880386400c00201300c0350205940c440300526801c5000d6a289180b15903414418403014410038003001100703030800021580210810041e0075030000d4144211100b0306000140c03134640b6090b100780401c0f00703020510198000c00001590b15400180d0148000e840a010100c0351600030110741c62700001ca8107401d41d8603050014195460a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 725996780 1250 725995530 725995553
    0x7170a0507170a0620040315050a0c05071104061509031407030f2004090803180d120902010c0204020f09030601090e121b060c030711030c0a08031906141507050a 71
    0x620043c1e00300540c2181714000700d0390340a0742040702d141c2c1000a210031404510300400d80c1040444005019100011500404900400201908031003a0300310064094449901400c013816032400c201e111041480c20140c0004000d200850b046681a6110020504045543c1041d240e008c001104241c049464072030041d4406001d01000380c090000e490915500d506ca0030310220f2241042c2c0b900ca15000c182d002c198016110074541d43d4001c04007480c2c0c451b41c001c203021031200600e440041d60300718900040b905c2c00c8400c0030080d0014800205103a0140701e03503004c1d000b888811000c44015a0703c4080c0003050307428800c402035a60344224505141c0c410910050000c10190303201c4a4812681500490300d003071801d840240501b44000140158280c0c410445449035542c08000c500d00200000d644d07035140d100c481301070200351021000c0f8546450040714191040482d607000d012076515030104801148410041910890101040445826071441a95442908030340a0203021805442d042402d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 725998030 1250 725996780 725996801
    0x1006050a0b070c23100804150f02121005040b1f030f0902060a0c03020610050a0e04050a080c01051006081501080601050d02040602010f0e0102161407170a0507170a06 73
    0xb0008011503050070300218080e48806103410f00d814900511300b401228181a046035080107806000c00001c146991a0f2920511480100007003201500c88140000d028412495026080180034845100b01008400003540c3c400c640c01c1010480502c05c102007402c541d0a5100d440618035061450140a0389c07241050040d255400700d4171415550004c0e000c4d510000a0101080d000b1030040d0505170704000c803a40c004030016901d11424148030000f01c00000307500c2a02c0d41d612200c000902008000e00840d940280e20482e0944c036203911202c42030281004035407204240031911000a0401d02c142c11031400385403010502101704072264011142601c00800701c42c1441410003206086642d244020b1000b44002d500000d840c0e81750840240542da440b41010003940c0c010301a11241b1907910031417030221341c0e2181c070341403031140d080d0329141c04c2131410b03808081c0c0e00481880f441004100460155035052040c0700350f41b00c070358481c1d03035280320001021901d000f60b9005409540008005900480498 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 725999280 1250 725998030 725998043
    0x1f09050c09090102030703150614221d070e0d020103180c3201020705011809060e0f181c17070c120203030c03150409150507021006050a0b07 62
    0x4100c04189880000c0c0ea58845a079030001c100245503625100d80f512030007031861541c49052802c50014448001000d0060054a00103072081a280d1054101074491090074440504035644124a405803107601502c500032121803000144424400c0b4038010309800014006014072401e80c00440082c01503040f2001c0030010402202c01091180b4540b0000380001d1500064407007140e12066040030309190311070b51380f9032142031a43d8603a8011400304e05403202071a041c40c40646c1d041d00c850070f520b003a0f4403d411851400c0ea0108035034036200f101903c03840c1c150030301340e58944070a03000c000c0e040c400d00c68080080e0000000c0441c1001100c1c507008604403985071844280780c0d2071060200c030300e80a894400c0400c401d142200d041189007662028012981d0000d942586890851f2041a05c00140f00a02200c00c802510f000b03542c1e194031000029410500740241140300c0d0280000401040e142000544142003801e2114003c80c0240e0301a200050440c106182c600000f500310360300102c0045408c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 726000530 1250 725999280 725999293
    0x60a1b050a120e2409010c0513030602090a15080411061303030807030b06030f0412090f060507170a08010e090a0c0b090301020405120705041b0206070c0c081b121f0905 74
    0x250b5100240f030b0400041e54030a02060421703107a030724210750000e01c03250203010302440035480e0358001d110400112500400056545c864810000f030082050360030042070007102241e28000c2c10352010545105030310891290030041070100400c20140a40326040140186802c0e05100091142241c60b400002034100070841a00250008401c0d801c215580050b43c50302d18208810b0001955070325001e90001e0900d030a1003420709511542e00c01040c0901414400300140c51410001e0380181314000d02000e40c000d5407540034207030008190850070702c036084940a10101003602d044000c80e0144c0c100b9808005121100c0c5004400800d5400c03c0c017180d03515550900c800100c82d190002000840900032010f414000e08040400003103910807100c01d9a00d4005044460f00590006036543d08081541050903282105180885501040d03801c00303145802100200604600c446051b41130700c6500301ca82510110031880e00990f80d45000b00c8442c07c0b601b82c1029104021525408081082d0058003500da1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 726001780 1250 726000530 726000553
    0x10302091c0c0e040203030301170a14031201050105180103050c0705121b2806090c15021009080306010c050a170702031006080d050c0f060a1b050a120e 67
    0x31070781211101e06001080c282441000880060a0081c1c02210a414120b01303003500400c1c1d403400140a01032921180707074440c850300c2c0400c02c1421a05980503250a0400c1e8049154545a400050b900d800ea14110000400c20398000d0040d0b540d99402c0910f40040c141e06136004402500010388800984078082008001241041c003100c80030200c005c4000307a0319030310490700d4070011140c10030180b841e4016100500e0610074a202c0c2080c0c0d4005440c05440c0d422081c2046030041070740800c003e014424810b000141003203140c0040c000b10500341c003661840340c000002d00042d1130305108000d120010410000e1070a602036081d03145100d01440880340754181c40e9444034510b5101d0031401342d0303280c40860682c0031841c040003406800102200140310b2540340c855100c3e503d00001304c0002c18084042100e4181c18001c0140f9460240302500722480c41c00c0150001006184220412a9140c880400c0d00b000d18021021240340c80c60940c2c0301145114038a41c120001c0c01c803a200c20b1554007882140c40c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 726003030 1250 726001780 726001789
    0x209250e06041a0307081302030c01120b0406080c10030207113303040c092306061e0c070b0301150c0c030203010f061e0302030307020d051c031b110307020d0201030209 74
    0x10760780311440d4101d0343c4d81c10401e201a040d10b038000c00c0e50200a40d0303848a1001610301041a0000b07034802e0034042c03500100c44003140041e0012000007900149000000503070300d503000030007a220701000e0350080e0b07410041943c118260f11a84001070b2003140707440e01c490254103082c116016024078035589038005605418019580103a1002c0c01001c20740080184414006440c4200e4014000f445041000e0003514106901501041103500482030403180055030b1516110111690b030520341c2018481d18a000b2103642c0070b40c000300c004a00038401e00c8800301d0609282c4003240c5c1a10311031030310341c00d030181c08510484248020340d2007203c525050050000c01078074240217101040d51050004181c050038600321101001041680001281c0064000c00c0507031008411100d0340c64054a2040018100b820400e1610004240c44240c940c0312500c0709602c290706902c424441c43c10b0f4102640041c6403010122000203030800582d00a42041013a0401840d02c001c03d04003c07441810054240285440085c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 726004280 1250 726003030 726003059
    0x16030b130b01080706022e1d0307050604050105070e490201020c0907090b030606090a03120912021305040512160b0903120f13020316030209250e0604 66
    0x10b495110780d505005c3c0c15014030441c10442101c6401485010400c12010700c55240031000030003241e40c03650074000790300410500704c2644180b00c0460b940c400d0310b0305e0900da480c04d0454080e1615485c20001c94905441060000f0007920003c2804c42c1880303106005009143d1050b145810b90341880060800680501100c18150580103091444500f1580000380c10a4000d01e07c552080380c01c1c008101e1100d0b00029032905860310a80c2c0c00e500c964407030700030508a10403141215440030f501100042040514100f40302e070141e941d51707000c5035103941d05241e130381000c98690001d6000345a076605054644c455840381d54028040c604480e5846607040c5001002c1d03000240405d92407400200080511840c40304c0350b038014074600000d40c13070000360701e950080f00342000c0d01440c14440c684000c078030b000700c94040489005400509030b03100243e4070180d0401c01121840304034080d0f030107040061410906400c808090820700000d00400da03040c80d40407203206103004c4031264400d4080c0320103d0000401c8500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 726005530 1250 726004280 726004289
    0xe0705210145020a0c05011404031101050417030a0b040e061b0f03070509010203040b0f04090b06071524170609030304050a0312020405090f07030e16030b130b01 71
    0x11003203141e850354084141501d40500400308688842c040c04101c0c1001c200711101106101001038407554116811207400c1c02d0407902400310360038520070401403544440c5060291f032007501c44900340c1500c5965682610307400c50b800391180c1c00e403a0000520012840c0255840200030000054608503440003404641c1c1d0b019819001d40d103c04100022010201901e1400c01008810f05051a448480500e0781e8031006000b0b6080040100c0c0d4021183d00810554000d0f280100b9225110004420045015040b034450407540504001d9040c410b41403550071140c0b41d035007013151914070034440351a40000d4480c0a941404440b400440031105404100c041006404450303401003004000080440c40c0080107480c60795640c0040082c040062400034082c030380380d5070609080d803c0310003000c0070000074001c0313600c05500128888100702094804c0395891b0701c541e840391001c000c200e0402c40c4071540c40c4110301c80d4000341c0b60108020700201d04a04c0d1015444917541402d1419407030107640e4150100800c0c0d01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 726006780 1250 726005530 726005549
    0x504030c0203340e0402121e06160e010806011815030504050c0a050d0611040e0106030212070f0e130b330a200a080a0909060e010e07052101 62
    0xc5407200c501c680c0c0114594044000041041d07400c103213064101003400341000384114181e000c282c581120a00070300c6509012124280381162042c130090fa111401107a48581080d01404500c1d44c59000728040c8a08090682d05c1151558400f030056400d403064801d032503200035a0200004e007084540c01000040102d07075801098074105894214a00601c07886500d100d00c0d0f0001041c0000d03219070100c070004640000340800c038180c1c81541da100901c240c1d0481d503010303050b00d0000300700d5039015001490011800c5c804c40c2c0255542510440300030010688900014000f001d0500d86440c0c0071411080c500c2012800048119030040003e02c0a040e0301c4089601040c2811070350010400e24901201000c003c01209182850180340144803050404414010303a620303001e40100145c0802c0004e804541c0f01040d596241c4241038003400324601446005141c42c140170b1301046106403008014100da118105440403900c540c2c1064450f5001992022000c150000c180c810030300540394203a00a001019 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 726008030 1250 726006780 726006823
    0x806030f031c0609090825060504030c2306010b09010306050a0f05030d0e090f070201090506270304050307090209150304060203060a05100f0f0e0a0305070f120c05040504030c0203 79
    0x200302c410b0702d5069025158840c134098600004c909090222180c050f003402c50340301c845481640c10680742203a68400707000a45400c2c02c0208260b0801c2610b00180d004003090490301c44505d02d000040380c808113a00c0340d01e4001100421000c1580000380840100504000c125280c0310000700c0c2c074602c900d5000130141c25210104000504050208007000781181c5004694031403400085652400050305180710316001c40c1c00203850741d10030352012507115808410713a045410500144801c000e0040c414081200c2a41e0004000c00c4e4000300b210211800580600422413400c4420402900441081078008129941044c055100c0380001c3d48110301c240c00068407414840d0600203800b42c1e03a04801e0080c0c810280c25003031150131a40c00f02ca00071240c0b0380642c010321076035411030300803130012030351a005880040b01008202021851a09503481c04071102d041c203656a441c0c4215400c6c9180141500407110428011030906401c619070050207070511040b100c0b110f83c0407920340900918030001d070001c0704 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 726009280 1250 726008030 726008077
    0xd030503190e07212a0512060a05010906030b13060e03030103080c0d0507330903090503011416080a0209060408010203070917100b030a0605180c011e0806030f03 71
    0x585640700303c0d4200715030007204085561303141d85c0010f00000d0051803d440124414148854298440207004046d060041306c10110703a180703603104001d4401445180c2002d00204e1800c0c20f510401c011613820584160258070354441c0981c6c2b45144600c20f90340f894603980c0d166404001080210f000b18407510a20b56074a0386424100d0800c0090f07c0c0d0403007005820484640426001841401602800740030079014515003180542100c14070003401c0411400c0803141414150000717000801ca0303000fa00240002611158030541d50003088610342c200404254503003081900c124000c1c0c0c1d2000560b04010715205002c000904203411690103c0d00c01c0e0b400100300010a0f40c4003600c1c03c02814000300244040f01480201500d0ba1084401d105200307030355100c00c13002550b007000b8080410350031074003c10250404040c140040074000c42e0000042c4110340324059903500c1482c0302c828901170501d002480c000e101c0000c6440b84809420f107a414810980e003843c1801082c0001e003a810075403640c0480b0b51002c2c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 726010530 1250 726009280 726009299
    0xe0619050903040501123b0c030a0b1f0305120703020d020d020d0c081b07080d0f0915021e011a150301032a031a150d030503190e07 58
    0x40080800b42c00521040000340d030010111030248164080200e078200c09a154007030200543d81001c0400e8407402c0860307000c0c03800311451a401502c0101605c0300c1c102100203159031100c040b00000c0a440c42c03440002d031500d4088180c0002000c60940300004a59242c441d1490700b401e00c41113010700c0400046030740c20035030100320044440813a030024090001c4040d8000c1d4442c4440c001c0c500c2401003100b141c1c0100220078003140c60100d108540c80f0440006d030750f145036650005000340750062040a84444035640103c410b0f40003046140e4802628906103c0c0800314444060f140c0c5042d8840c003220607500c416007661045d080c584400000440d1030f40d40b00c2416094421440d10b600840000c265104945000c500701c0e81503a40006c145030440d1501c04003104080381902100c0200445040040100103240310381c0407400300c102e01a000d00c0d444081650210f207001460f5241e000d27200440300d0f000a80100080c6038030149003018148012600740c070f408103076000269402e005400800040c03259110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 726011780 1250 726010530 726010541
    0x507170c0d03060e071e050d020706060603050c13030206090609030618070f0f0b0f0403020d0b010503070905090a0f03050c15041e200a0504020408060406110a120504060e0619 77
    0x902c1e82d000034101064040d00b0100058605107401c86e004072100d0b25035008400322a507042c002c580c00c6590b00d009041403030052601c2e001e000000b90804000c1020041003c054400340200305c1e2099119525503401c1000039480039110507040801481026099542400b80c13500c503a06056030150800041d41c0c50b681004001c0e04400010150f414050011000d0b060700304040c2c800d22401c85944200c6181805981d00a540c0b0081d07004000020381002c01034039001441c1211001e0f01255540c0e81c44e010481c00b601d50446050060b40e01448000c8007044d840d5002c0d00c0f00b603000f0b0901a03e81120f280019082c40007580c10604000070440510040005113029540e00010842e000d68400d07040d56501d0b400300e01c681c3e1401000007207102000f01b05d603840503807500c02000c00034401c568855071602541d444410484040d1980361400c04c8241c049014a01141c0c0c81008554403000045600340c03048009110240098912030750340e00c41040c00003030401404c0c1c090744000c038411344030100c3e09111005844 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 726013030 1250 726011780 726011789
    0x303090203010b090702120931050702010b0612100e0114031b0a030f0305090402030115021903050a140408030703080103050f0d02120306180a060906061701060507170c0d0306 77
    0x4503404c080002d46031b4086801a400703541020203c1d5501540300c0018a09070710003da81340400e10b141003003440f00c8503420075000c844054140500003640e4624050303080714042610644c002c8010000c000790800b18480d59a031081e940c201003003c02d521090403204000e401d030015041e803007009040a00a242c00c1144104054440d5010f80b140603400f008030b0f00c4000e0f107201c028030b140c505134084810180038100345da4003540081d05c215140d60f034a0005ea40c00c0e42c4010140f00150003031080103201c15040f00030011040d90152920b40c50007810318801c4485a44102c9041012002404046040d50b01070009100341c40c001d0383d40301c0242d41582803050034188031013a44100caa2108400e40850f40e00400e030a1031613110034a00070f44969a22020604030070943c1d0006900c8440d51041202c41c40082c2c1c0100140c61188034200481a11800c05403420745e420b203aa59107558048004200042c425002410214401c41040310000c025114842c2c0b150081212544560014007651711b50302da05110b110000c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 726014280 1250 726013030 726013039
    0x50a0b04060e15060304021302030c0405012a030e040b1306030204050601081e060f040903030527062d01060206010303080c09060d0506210a0b011a0d0c120501030303090203010b 78
    0x203003011800c031040480e129060f42d020300000b00c00142590f0b90950340c041c12202d2460706554030300d085058641280d20600072540440c0c0d541c0041c442c07000c0d101402c2a5416504601d00c0107035540c07501c0c2070b030720461018541f81e44a9150b00f140714941c2c99800c3d01e00c4aa8140724008981d140c110301c104020342c1e9000341124100001d02d41044403001c039804881031001a411405121a01d500002c11205000e905520303030018101710410042544c140c0c0418400c20545150b008601001344404840c2e40100150150650014020a2010f02d104940b801007174200310310325818031800d07007100703034111400d0b4420030250304a40010024160403003002e0341d12203ca54a0645414500000280140900301259900940d50f000060054035102e10801412100301c0c8015036184803400a035035500b1040c20102c40107c03000c000050504240348001c0e000040a0596505101c0d024040c48020a0599031090401101445140720070303505204041c085d601990340443c060440d40149400d4455070341500380603 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 726015530 1250 726014280 726014309
    0x3030f04090e19030e060f1204170a02030a0e0a1a0c100b0a0620030c0a030212090d1712130212060f06040f09020616021c0c090203090f01050a0b0406 66
    0x482c03c1034038642501580c1400c0591030300c020803000c07611500810800c070f4122170300090b042c10340c161200400c0780b0aa1141401500208108176040c000d801803803108001340c2c2c011721843c10b0407405490048054180039245003014ac5d506c5182d03485614081c0142041c200740011413101c1d050341401a0087c10704035030300034041c007610320300828034011030ba00c80d04003044000c85100044e100e950b0550800c070702e0720390211303038560148502894031071218203011005881081c105c5000000032074140c1e03924150052412002c50380303948981030035461035a102080840e0411002d0310341f402c0381117a01e0040200441641d4031500b0361040c40000d80b01800002e00030390000c81088280020308a0055010f5000d950101301d00700d078000d16034050100c9400082d40248003042414072180c03401101d006060086911b410081c01300d0000c0c08891004042c00b03022201c3c03411092109034400e03001103400050250486c2c1d400e041c00780000c0c1c2110002d440f070f420902d440700a5000903103450300654000d0301d1801030140c8d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 726016780 1250 726015530 726015553
    0x30f031e01060512070c0c061116080c010804031404061724100c0501020301030503030406110f0304111809250f05120f0a11031203071d030c03030f04090e 68
    0x103000f81c02d0720400c00411400064a030500c038081c0020003550064031147c1091710713804046c002c05480710699025206500508106907200700c4085c0c1151100806412030507070100c01100d00c0071000700198140a604240102c0d4a0310100080c0000c0000b6a1095000c0f580342038031141e40e01025008110210010000b00e4140d5102c0103407100d2b00e207049030b0070ba01c521612601654040701000c0050f06552010000006202d0044000d40c480c0c1d106031030400034242080b030b2004240c01080d1310000004010b100050000d41100382c03001c1000002800380d2107600f1064a509020f5400702ca080e1480d401040d6800c28100905082e01c1e0860280d0204d01240340c10a80c50f007908203d42c2c40b070148034154940140c14812428424103904201003811707659103070000e0501c0c00c0305059003d00d5034041d1203100c41c81d415140b8800141c2c1e0041607a951583d202407820100c103c6900c0d032070143c5d140d240c01814240f0b03023113540c00c1000701740f08003444d5886a01d441c5440d00003411a2080646d80a0b50b40081c506540d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 726018030 1250 726016780 726016787
    0xf0105060702131d0a03030204051c1e151b0e0301021608160c08061803070c03110315070c02030123040f0507090501030602041e0e0114030f030f031e0106 68
    0x11403c28250701d001400c2c1070b00351403d8242000c40c0008075594051181c1003020701d41e06800500c2034542c20b980c04091a404618140c21030300610f00c01500c06c0280c05258100010b003560300c07101d05806415900300242c0b000fa10030003101d803456000503c01d10038001d82110b0540050045d030302484201d00071420041c0780e2041400c180c8600b100280302c0d10300040d84803942d01903010705100c21600b10b9000000c298a07142e1042d550913007a50300c055401d00e40c00d00000c45c3ca20000c11a180302d82e101281c050000d1441d61500c608141c03030100340758940a01d4825070450300560031a01d02c107800783c5d5220352083c40d05006150868441c2c0072166141c28204011424060079200025086580041d44500c00c069a003002410300c0b603e41c001e1140d01e4100400002800303201c0c3c0180c010354a213581c0403140d12909074410021404d03544602e44810854400400c41d40c000d02e29446402d040203425691036003030b055085406d50341b001d420307414080808024407880c0d804983d1503030511100c80d204113055504164000c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 726019280 1250 726018030 726018049
    0x51005060d091401020705150c031006030914160603060512031207050c061312110606040b01020a0b041a1b0f0310182a0e12010605090f0f0105060702 66
    0x8072000c03900c0d081c00b0400c01080c03883c890300d034004110013151210f80c2840c1042c0c66202c03858500075a600c0007400300e12020705250444e80580094412000c0301440c2c000143d0140c5002801502c5005942d80950040b200612000c020001a00000380b081820100082c089a01d940c001e14003401000840000110303002046512002800505410341e83d1108011a00ca220b005149031540c000d81081c810000d11500d0010000781c8100d060008181c0020070480e0b6003c2000f08146481d801000804c007282421361064408081c180705441e83c241c04d0752100c00400b002600c040721040e14014002e1010340300010342541040b2a1180d40840e245050143c1801d401010403480c080d800c000042030060b900100100c0040400d45005c91a8541d007114440c01800c10074258060b00307280e95208010901c0c81c80c0198544102374880d0030505680c0801c2c48190b0700c0940341e500b450741d1b0300d45020441d0f03591202c030180310300c001e076070741216a250800190456100c1039010700d010705001d110100c016682c90010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 726020530 1250 726019280 726019297
    0x1a0601081513050a060305030d0c020c0108070e0d030519110106090203070203030f0907150e03010f06060504030b1b040305030703120504021c03120c0e030c0303030615030702010b0a0e040605100506 87
    0xc0340e0394413000034480044c64164001485448009480311200b41e8035084207420003160f400b81e030a0700030700340015100c04508039020000a800c8003035104c110b02d400e166040f4901d009141507401c105504c00d0910812000c400e010010520031011600001e109000c2c440150240050641c02c508003008003940ea400007501d602403031401c03400040e4007103500b04100700081c5103d07400401030341901c10014109486c0c0d414080c0c043e5080c000e90f402124601e014080441300d05640d07c524140c9552070b0058143c00141510f0902e103a90540c0420031000703040034001550294014503940c003c1460081c1580c5c41c1c143d64940d4035400c2c0740802c40136a8602a21501c6070192451540b0f514185181c03c030b900002d80314001c0d15182c030703000b01004442ea10410816198000f030f0300701d81030403100c40101583ca0104450850303101585000000015054001650300f00d48203000206964040710002401c8103400c0d080303005a222081e04000600c0054020190081d44149032441418104000b003904c52290444 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 726021780 1250 726020530 726020569
    0x30902031c0807110a021302031e06100f030b121e0601080a030e030c09150301140f0a0e12041e062c06071a0105030622030311071a06010815 62
    0x1598021401c1480741810340c0341d0040c410030b42e038603003408814000c9d0000c0e035800d0303220007400680c04441606c0300c03001d5004002c020303ca001e6003100900c04031001c01012800c00201a01c0d0181c54441d500c8204916684481d07080240c94090034070380841e1903c5900351030240384c652260f00100540400800c80ca40240d0b058580142034102e480c2c0403d01d014401031101c1d421486000800843d90070303140b80100e48030800c0b0020702002030320350000200300001350340007201610b548020442040c042c1c1e21001010758281c00f5110b55032b6030b50ac907110f019009603200312280040000d8035446090402840c0d00070b0086418440000c401d4039803001c3c1c0000d50702049491001c1e9540c58405143d039400e056400745907202402905c0c8101014400b030f00344500784110790191051030b0200340f00585850b04a240c451090019100e02e00c060b440031005002c3c4070001c00d406034401c101d890b0208201d444100c1d522002003828101d50705041000520001c0020101940341c0c0f045010000141d580a4640c1c1c02200c030341c403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 726023030 1250 726021780 726021797
    0x609110307032627030709140606030402040612050a0201120507050a030c020c04060b071203020405061c09140309010801080303010b2a030a09060e061e031b0a030902031c0807 77
    0xf003110688a50444241c801d20408841c0003076002c00400101400026070542d20a039980c0c0c601b180c1030b507a40e01440b02c01103000000084c0c10781058000b4680c401e000034404100c6654541c40a07217442206c003800c1d038194004d102640e00355600040741d89600d0341a80000c220350b2910410082013400783c121034008147e02d5503d1080418403c100380c02010000038020007085542d14240140c03503000310012542c3c0d41c0c019442d000b0f258041c0c4248c03402c0714400b40c05180b8244c410300040f040c460450f10340c00d000303a0391207210f4008612504400903c004803000250b580d15480030001d002c100e4142c1c0710705001c0d1710400040c03100c481c80c5401c0d540d0f69510001182003130040280c164040c6031160042024034407000c00d40441d03542d40700c09410101c0f21951209503514444900b4400184903100340d00102070740701900428210b408000444d44040d51402c4040206061290200f603580500003c00000382c03641c0f20b51f403c2d03207400e025005403840950710518404d1030910b00034040710b00052090040c0300030131 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 726024280 1250 726023030 726023093
    0x11d060f0402092d011e02120c010618050f060f060a05070201020703170301180908040308070f021203041517010302010c0f0609030f1b02150a050f0304060911030703 73
    0x1c036030300c3c00314850310101c0081c0c2ea00c0c080d16042c0c0c0700c2413100600d0015554a41c20701d180a12241a40012103440c0d014080c23010240c0138085490f8005c640c504400c2d0b5072910002218030010300144a100401c140100b00c5045c0303d00c40040c0c4800107000305208039801e10f45500380f550b0b82c804482c0861840e081c41d6440f9030083c00143e0800100b5400541120308141030082c1c44d9600380d0046042e18919414400e02c000134402c500c0841d41c4200c00140009402c11050000c00c0c0a02c01903c2d880b03204014080070340000d40d011440301c82d9812150b10440d4004101031000131007400040c2d144079102d152803008102c40c040311a01551b410320000e410b10511401d01028003001071a220803440c3c0085091081c0001881d000745a420008103160003c3e225402c01400c0c00c040ba02000040c070380080039642401e219000318500d41d40051100e505010042066182010524024501c5a80140c20003d031030951350a103009105407019445100340c001e40c10038400100c001d0324030340f206400c01e11081d0f0f400018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 726025530 1250 726024280 726024289
    0xb09010b030618010c020f070909141015050319020d0305091503040b01051c24180506061504060f050d0603060c0e0109150323010e011d060f040209 65
    0x40d459058250199008029060000c44201000440d24000070801000707032000480c1c5a404401005145410044040101c034000e60410074a01e40100e00e0fa082074a80c803040300e481d0040c40d01c2d00b4400345403500c481ca02c0d401000b07604d070401000c00342d02400c0c5203c2c0114862140c41420b4100034800c50740c05c4182002d2601c00d109035000c030a0041c0c1180000e41c0141110406a0000c5030200d500070440c2e00007040300d041c044203d558800b00104040f510002c0ea0392614400e0714031071641303080c02e000e000380d0025802c0503005400403109007c00301200f42110381015420103a0040826004810910218600325079580441d800c4401528080000340030300c94044607980f180c40e103040016800c0c0f040c00700a112440e0701140340300107243c683d02c024980c60401036405440b54825001540d2801c41c040c01c041c3d0094200f6640c84000d407940d0a500707062090b0485c500607081e0010f08000452000502c414842061800d01c1201130003441032440c039082000440705030840c064140a00c3e00801d4030045a140d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 726026780 1250 726025530 726025541
    0x101107060903120609140711010e030415140c0c060a0302070b151008240607050d02010509070b070b01050114070f06020d0b010c0b0103020d0f14010b0f060a0207030b0901 75
    0x2401501803000728024100100558003e4a902040030300e003c1000440204602c0380503500680d01e1480402e65a560105480120b0f0099800c1000c0d5240e500f40807100d0710a000400140ca164041408030f004c00c60700040100301c0098000600a80c1001015160200040e90a0300c03c0011200306030b075402900c600301c02900036548018203400503042031281078512407001d2400c8920940d0381001d80307140c80b5422180f141050b180c03056982d00c03400d115074601c00c25100000b051030010b00b515180000c00e03903503903203401420318400005075540c005000200005200610042c1044a00700b41000540c1e03d0740542c848042c401e0505000c001c0f510010320000083c150794140d500111890b0444140d07050500203540883d021010141ca02110090550301a12440d440a500100048666030841c0d00f404074003904c61206845075580141e1200000b2640f100c3c2c851404159070000c03524a11f00e4052002c502140000b880c0f06400901802c031031283d0000b0040c0032a500f00c18944940e44071040b0807401400c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 726028030 1250 726026780 726026783
    0x2319030f0c0801150329010e1017030403050601080f1002031003050d02160918080c0f0316020901060c081603120c181401020307031107090914120c101107 68
    0x142051200d00044e40050684011240102e0540001c4079040f082550703001c2e6000070261800c1100401403200d0f100c80c40301c1039072154510b903c00d8401512000082c03a0040603071503481c000d520002c1c0c18020400c0611000b4014a0f20600800c26194500d410f1512640f40c04039540300030b40d000c000070b072044c440c10050340011030308035050b10511641d529002b0b44403160810079041e20f0300b07110030020300800507114195010059040240c00c0c0c11143d80c50303410551081103940d074948182e0403829000314003400100380e4015100f04103010310b041407041c41004036050f8001f1041c8036810000c000420304c442c0c11107014980710910010b0514540ca42500c1c02c3d80c8941d18080b40d280f5052000b0030860700080d540c0300c0490007a898884c0315545080754000101001042401604244021000a4041c1640000c540c06501c10740b400c45864030414411201003400680701c15102c110011074203241800341001040c1684062442e01c3c08480c105503480002000003043d2a41d90110b81c0e40701c070201c0082d01c1081c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 726029280 1250 726028030 726028033
    0x190e0403121d1b03120a081b19020d0f05090906030a12030b040f0e071e0803030a090b0f010608070f0201140a06032d11030102132319030f0c08 63
    0x280b00622095a071070400d61603e11801c0e50082150006103000507505100190349182c8903d02003444100300d810080142190a14141808804001c0100c401c050b21000510507512038a0f00c0540500031728105040d81c0303000a20074183c016004843d8042c044500e001c4040c2d8101071142c696902082c40c0c05458075000d080c070040b5648002c1c1060385500004039100c030490b001e000c0704160780410300407100b9a0348084016807012104000f80002d00144c0c80d20f802e0313a440040d511964814055046500031581450f845a440000341c00300700c3c0c1e4010961b00042c6000801e01a0740c1000d102800542000d4070807014425283c98240c4418800d400c952108201c512660750b4606000f000a80681030900088441801c040c2c090740d020508000d4510f580d510b2074078985940180c6d904d84440c0c81c10801c4140382c040d50204046200c00c4045500131005190422600e000800201cad2a52030034000c2d07102d81e0303204122000354402d11680903482e42050300d40100720401402c40510b0142c0381940c80d94850300e810b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 726030530 1250 726029280 726029321
    0x201052b0e0615030705090a0c1112070201120209130509010f060f030b010e0c0d0203040c0305160e010504090f02120a0c06050a091508131e080405190e040312 70
    0x1500350200b01c40c0d000c0c0801502c2d410202d9014010541c83c0c00035030062070f800c240d5030b40c000382521109800501c40700a55081c180002c00d01421658101000c510b5541e04c075080000781d400c11542d00c9107550300100e030103a00450400a503a0009509805504032520005803a400031451500081d0300c00c1c3c18440058804000d00b50f5580304004010100340b000b40e40452446000281c2205610101803203010b1030f0340310518080321020341a00941020380156221980110701100040d000c20841c15420741100041148a141542141d052001604964092401c00140c100003d04038502380d0145c542c1110208000c81c22a0b480728a40455503030b011303110b94454403000994542140c01007620202d10340e0340c81d08094030b46150300c0310b5050641108000540507000a8411441032403100c0300c60b0700c2400005954808100380c540980d1740c580b030035142c4010005040101c0d1802c40c000001b100c6061400850341480c106c508079110400400240600281080a251078806c6600c0b030014003500c0c4c02d00014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 726031780 1250 726030530 726030551
    0x14090c2101030b0a02071e050c04061403010b040b100e0f0406060c110607030f1b0501060b040f0909020f2b0305070b1e010b13150509100c0201052b 65
    0x880e034000e202c01c0c0d41d07003100d80b03012420b50821030081b50340e0150000c080d542c039241084031004001c1340901043d245405075074800c9507240c1d203501408000f0b151a504222491088908160844a9000b003480c4114a89085811241c40302e031f0b0038002070b0465042c12503601c002c13003010400317030111582c4595000b840c0000224500d07402400900480340070b10303604100c20340c2040c2031007007510802001070b011407990100f0070522803040c80e01d5209110f5240c42110010002e40d03074603003540c255400541e102d0402040a10040140400704801820500401d102c0e4190503004145001c400400c094059070319001c06e141c0c6034168010303400c002c40c1485002c0217103054506000b03150384c0080500f180c00f03803110400304812502c0002030f000900091510492940d103041c03d500820b0b800102401c0216000840005000911000300b041d8030106031038690fa110441c0e420005020f030b10364000b42c240451045c541d005070740d000041c0d0303a01c40c1303451030142c0401180c0302c0c0d0040010003080c0303036400d800e080190626 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 726033030 1250 726031780 726031837
    0x1f030614010f0f03050304050603060d020927120a050f0705030d0b120109050c09180a0b010305010e21070c05060a0e0f01020d0206061014030a02030106140414090c 72
    0x24101d40b04141c214210036203820340c1040390031a61001804952060106000c94030b0310100031030300064020000031400c00b5503408102581c4007102e82606001c2c2c04078181240d010080c4418614071034a001400500c000c0300713082181409140000c4081100104e4004403d01512040340c0486400c03008507601d0b10b02d0520300401070000f4580480c01007030119100d41084105004020344550f02c90064045007009605000c4440c1c0010b040c4c0e021040401603140078500300380411940700c0d001f55611007087d0f0540c20079600b542c501d0039039a2081e81c4140380000780c01e880425511039000c004444959290303100e040044090b291070700815407060000030306040b200e80101808005e80302c00d9031001400da0311000166141c155610307000016170003050014401d8500146009801d4406003484c84241d9490006802650030444000b010b00746d00200501c443c40e08410444e40900703545000e81c1c541400e0580100381d861902d0140c0d402601410702040719540e1600558858040c0fa00711188400070461444 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 726034280 1250 726033030 726033071
    0x703230406060b0f16030207050a0b0d18030503040209042603090f0703170d06091d011b210e0706051c05010b09211914070b0f0714060a0c170105091f0306 68
    0x1446662401c02d0f242c071374094071009040c0b9280c060f200c460850ba556000d0114107040284119020900100400314041440c00d14040400c10014806d44a03d0706841c09da240460112100c1030340d500203041000001e145e400c0e4407403810405001c0da52280b009152900140009800807009a400c150846060903045440005003002d03840080c8000340e40070741d101151300848040716001500749000f013090398a911070940d50461441c0c00000b4065204a449420a0701396000340d0f00191000840c0ea03600d4608070b100140000c41d03280108240d504d4008180282e215a60070b0700d001d4000400c0300f20380c603010070300300039110001d050594018061285c10032605182c0100c00310b481c503082c6140c640a0f07940000d00501503d0480c039940f4504295900115142d410440049604942d0f00490208017030003403000708e000358a400070110f00c0300c420140281040800c80c00e180b21428000c0c0040025075944140a50400d48510342c0c6044054031844202c030455490300080c2946080c4000400c0700c25240b40203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 726035530 1250 726034280 726034297
    0x1f0b0a0509180618010303093003030c09080118060b0112050411011103040b0d020729060906120a030e0a1208130f03030c0305030703230406060b0f16030207050a0b 72
    0x2010003906104c2607100201804c0c040500001d1222009203c8004500682104101c165000c1c0d614000c0b5900144904288881c0440000c2c2c1c42e2401a001503400c90740d01809804000001c0c8031509001d1011607103426940d40150006886020000d0964001c140c4144402e450300c42c148224540341c208120076868400109001030f000c90107402a85030040280e40564000d400f1107841e0200e0042c8810280d00041c10070b807240c21407034200200015810054241134040f22030070118500d440b80c1001500a4010041401900b843c4032150741e100001c80c0d109091941410085440d59445000c40d6080c200c6800035041980009003441c180075641c000b40207642800109000c0e41602c482001074400b200f4440140890420b01c440000039001d10040c41d40f001140c48c0019a0b20b0394020090704282841444001041d1100e003400300b881010301421000e003409895043c605500c545050241d0b202d10003a03020a120101020700426100f030040074014400101010413030f80d10384a081c0c81c00c0d40030081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 726036780 1250 726035530 726035539
    0x712110d0614010207032103110a02060910050f04020d050705030d0233040303050a18030e01030b03240603100507050c071e140a0f120b1f0b0a05091806 67
    0x20050320741c4002a4030054a5104a903a00c08022007d40201e081304038101d58024181c0354010303409283c440314040e1050019a030700038403450404028060800c2038507400d03032441e54144000c00243c000a443c0031070300682d050380d44d4029540d9a081541c10040c0b160031450f4107001d02e107231001c62694002644168580000307448800441010394096612925854140203101e10f45c0000e40840d000f40d200a03800800f03070401085800600e60703190802d0f0709000048000c25001130b00440346580c180b2070b5082c240b0064006000920310140d1100710f0401c1c00c01c08460b460703002000038400d601d05001c0170004451250040c0102d00744100060280e80020692510318840e8120024544d60008450851380070800c641c0c00105003059007101032a00248000313604000c00d05800503407440031050007001401d9504403409407031000d240004140001904219a4030b15030b4409a959480c00107015081f14100701111366036554582041e1924042c2c1d1400c2948800b03c600a0300d0041600e01c800c0784034080448 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 726038030 1250 726036780 726036809
    0xc080115020a14030414040905060609090a02030604030f030c08060f12010f0203040317070302070b06040911030d0503070212312102040e0d0e04510e0712110d06 71
    0x20600c01100c80c52321021b0810b502c1500810440d0510165168000312101e080c0c50f030f2480300e81c0100f0325018043c0d4040b4001101d01c90741d01d044a5040c03059a40e48025450004183e003060340001c1d100c000c5110180340f0480311805010107a810941c030040c13560010b02d4041d9100d00d0142400380042c040b020841107016003440c00071301a00d101e442101d0304c840d808155648580c03a26024403008010340003040724400c0ea0130000034140d40c1c0070454813030f0144080d91001d80d2880d0540009081071a540d06c011014030090000804602d1201f2550f00c040c1d6078a49040f100b00c0380c1c40490742c58848207501025040e02c6240344d20022420351020030100700e0094405110810030103000c00d5448082c03a1b0701c003001030340303041c3c03828035070300e019002072031349010b90889807800c2900d8009841d040183c1400e201c1010700c1c0c0490f4034603038270326201c0b0b04180518654002d20009191144480c5031000041400d03003001410b07050070000c400d0951007020350703000e640c2010352100c0c22040070b9002000580030f00041d607090007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 726039280 1250 726038030 726038069
    0xc0312030f0f1a1206070e0609040912030b0a0308030408180d0302010905060f132012010b0301050c04030203060106142814040810020f0c0a031709010c080115020a140304 75
    0x10040e40c20403c2110700100350607600e41b0421501c03041302244095000500b04040340070359443d4040c48500c0c0f40200c04051001c40024000740403944036240f01f0b809032010351000c0012441c01c80a480d0f000340c2004110b0b41d144201c01e1002c0b5942124024142d0080109001e60700703040d0705512000c0003602c188120b42a0f034560b08545c00088008456800420740180e6201c0001242c2c0d00360348925014009a01c0d1000002200040140e01d042d0081c2d05181c0d51180030318010b203001d0151301c0d04544003c0f02a0300c0c02c3d08680210f500ea00f414010702c0d05100b030300e060401c40b0414110407910320321106041d6000b508205044034050049640c003800004503030a0b4403c6070b07064070404035401c4480f00b400400380ea009600111002c4e401c02400d0034088241841141e800140501c41c00103021311903601e02c02c2e21080c281e00340c0c41d1640c01601c01085a894480200500b540103031005041d40c200b941c0e480030a070080d60080340341144501008003036441405031480a00000005441901c0ba146401c42601018 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 726040530 1250 726039280 726039289
    0x70f1a07020c0a0b0a0239090103050325020d2102071404090312090606050a1401120b12072303010908040b0307050d14061003090c0312030f0f1a 64
    0x5540c030260f02c1120444100304158408004104814180c0141c50180c00c5e500060309041040e010880840040c0341c0d040c4003611621000c0c006550303800c8400054550460300e6056481c090b500002000d43e12490302c160701a02c80c101d0602185a008091010f0303031800b8600740c17000c9240200a011864245600e00384424000700385041a02c110203d044800c0d52840d00b000050300d01c02e4020313000e218000541c48000d00b451b00a401180d0300803500411860310741020300840c914544e201d0100d424004160900503a8000034181240348403140c0400e900d03400d080040c0c2d1302c22400700b0803005407040c0c0000091081c40e0a00c4610310001400940300742045203410305098400c200402448020304010921180b04040080c5400c420640742c014101440408601d048482944512124401c440c041201c0703850080501820000240750500a41010790f5400000c0800d50000900300da0724450b1103c0100d21942c804810b111082009001180501000c5001440400c4c02c0a0b40d410116000d44082c0c1070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 726041780 1250 726040530 726040543
    0x200321011205061b090306250903080702210607021606230c0a080a0c06060603090f17090a03060b0f030a0b010e0405100e03120108191403070f1a0702 66
    0x10000e0140c032a6a40b8416032490b500c1c14000030300130051061000e17059030340f410003029200741880304040c1c081c1c1080400c2c81449804c000090380c00c10100c0502400010006015143c0c80d69068580d23085400020000040c5007840010b0001c440c4038007810030550590004001408103c0070201c811900d44030101200c40294000043c1c1f003403481b141840840080f01e1000b001000c402c401510210080b80ea954404d99000d86072501c00220001e009809114140c41880020407442c2001c0000c00f4044d41e42c0d0709007031803400300586128400b0a000310344084c1b1108a9014200c014000c090840e03c0c3e14040c1c0040c40c00000141c0946c0480360a981c3d14240099220b0803030307400005150b500e038039020f80c4500c0e5010080040b65603028a180c084d40322003103401130011818402001d940c0320340000c1c14284c0901d80503407001c0d4040c1d0115000307600d1404900c00c42103100f034001006501d0081191a45440c61091000091803007071103507038000c240300440403034a101041d0b80424010710380750407208907501d13003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 726043030 1250 726041780 726041783
    0x608030412080c070b030c030103140a03090504200c010204090e0604080912030405030307061d01110d1119210c0f080a0f0501060503011a0c0d2003210112 68
    0x30110703800440c00340300280000580180c11a4052511001c0300b02ca617800030344018500b10400701c018010001001c500c00f514800d090001c00700c407082518000c1c0110401d00c2564050340d0780780c038030a51030b41d19a180c03082c00400a8030b031696a61840300380c5038002c0d44203118040701c2c00e251207950340c07ca90001c02d0b290300560304480c3d11400d0040c1801006480301120130311411a1104000000b510745042c80509281e6018100004440842c421030492074003d8004903400781c1d16104012010340742050a0b80d031a01000c0c04000303141d08400846600d54820681c0344600f035001442d01e140c025912a2444001c080000110000d921146183c0b0f0141c034501e10040c00410807280310220703001c0c03140c01c445a01c1552a40d000c03c140b000317010310101321030017070304904002040080180715514003400b1240d02d0403003038000c4500e4030f103061900c1501c4810020314842044807200031100e0f25003408030b2a0890b648020152a6a9020a040e138040491901000100c0d60000000000c1d4120003162200c101c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 726044280 1250 726043030 726043049
    0x7050603010b03310501020711241309140709050a032103180b060a0b04030c09020906070c0603021210081c051909030b09010b0a0b0a0c0602030c0d06080304 69
    0x15118910300134451200003244107450948580151500313001d110b9940070740c0e40554001643e40103182413840441000702040d602880d11140c8030b203118a8000f40c4c0380c4640a003504003546480c0755405440e00c0b502c4580c03142040c1414036170141c8004150184043c000c0700d003130b21103809055580c01807140c4044c0a103c080c108040354240003010b1800980c2445c84141c0b545400030f080310701c40c400c014450039041c1041e1020f0105000b006401e041c51000780c0050600b40c180780d03003820700c0d40c1d99400200741035002d100c04603500410351414a8490f5015182030640c407800622400f03859002c000c00030b410401d06500201302c07010124002c03d1644000c2425602084050314001c1000f40855007c01412144002003160030403101640841c035814100480041390b40700440c962a60410014180c40500b039001641d1415004100964448081500716100d00c04295129a0040e100ba120904440c8026260f14000000c0000c000b00c884020000001c18030001c010f800d8a9215459481c0100e010f0310040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 726045530 1250 726044280 726044287
    0x30506043201052509171207060b09071b020409050c270a0b06220f14030609030a0206270709020306180709050f06040b191b1509030e03011d07050603010b 68
    0xb82410b1006c0090146000044a4850a451008256903480028160ba201e5943d00d01c00549180040c1d8641d0800e525184c8000c10418035459400034022101e0000c0c80307141e40310140c0040010502c14a503524500031700c03110040488582da50100c410740c10302c0f42174801c100000201422912310410b10f25a0024200074200041004035004c0c0fa609101d00c88141811500d0010700350311241c2e1040041c005500c000617402090000385460010050401d906d5a002803120f4885180d00003403141d0302254486100c02031011003141d40b1100c00d00e1a4518041d400340b52000710383c03559160021401070600350352030f03a494101303d10307042540e282c1035940e100080c008907030410480c5442481c074000340c0001462145425a2901c20507a1680b02c1c0010180c0d0540c454042c1e040980c00440101000790140e462080700480ca0750f0303503051076040a030100710941d61000d00005162044d81d0701c1140d2500030b030003040010003011044800300000d20801c0c0b00b034800c29201003480d0400070140c07412100500080d90a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 726046780 1250 726045530 726045539
    0x100b0a0c08030601032406021504020f040b060c0105130309080a030e0108150a03050c0906060703091e0914010f08030a08180c0901140415030506043201052509 70
    0xc0c50360016083c9810580c580c004400c010b50072203142d481a070301c010042040c0b03900d40304c806410018400c0900500d000c68004001c00350700c42070811039840e141114005022850040001c0d030a01070880031604941c81c1204009a8864070020300c400076019849115509566071141d603510500020014006900002c90f0b110039409040100e070005aa44009007542200e0030206030b2155459006541c2640720291003e1282030150340e4a80000c402da848901d440c0070b0340c50140100030395204401d420240340c00c80748802854460010060414081c0500519001c00103030171702c8600a00960100e104c00303400000c1e11f0a800400c81d142000355444200f41640c0d07404201104102c40f921307840d07a40c02154658003490361822101c0d13010305905000c0360020141c88041c0b0048868a181614052090078000d001240c8001082030340240e001c04118032108100c40d00241510300c03804070a50381d02690b48003d0800d08190440c910502003013100d20008186801280708050021803000c1c00700d10541010301 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 726048030 1250 726046780 726046793
    0x109090e0316030e1210050a0e210403060e030307080c0405010e06130314030c010e0102031302130e0615271b0c1603020123041823100b0a0c 62
    0x201c0c0318000d0814804050081011032203903c450248501a60042e00e1240041c01b03e911910342c00180d600810002c140003070f11300c2c3d940c2e01d44000c81c3c03850821101e0f40080c1e0030000c071000c07030740651740c0700c031003844041488441541d0b60303042a01c240380862803150000d240d400900d0251822035005940d10b04d94241182c00340101580704600c0c03c2081d414454021011400034a03054150061041c01940c0d18080d4081c40350840301a000c84501e10390042042c00800801d5a01000c40316404480a1b480c00c00d00741440300c010029002009840d0003603104102c85581400c404149612042d910805803056000c82156901682c000b1150083c0d404004503286a5005109a69900001c00070915040175006045c3c5841c0c030303030500006048402c90707040c011564400c0c03002421000c0c1000b10260500844200241030060b8040c03003c0740d100484660382405c01d070303070400100014034000c0c5c0c2403001303084107640c214140125245e110030b0810140010340b01480c20112010300c0c2c3c1a45d25004141800d07558030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 726049280 1250 726048030 726048067
    0x518060a0f1401060801081c020d050d0f0903030501050f040612111c052b020d3005250503070507020a0815070306080a03090909020402040b1303020109090e03 70
    0x201e4820b66202912100700e03000084032806020306440e010361799032501790319600c3c4c440c3c43d54280c081c000c506401c081b070070307500001d22519900e0715080264032082c1d8100d1520003007403880300c4481e44a080c0f400c000c0c245505a8001c5058810a031007411050401e08144003e8410501c1a05c0f00164000000b4011136001d503084880d14034014508182d010080681940d94803070820292180c2c0c00c545805005903c1c469280070a000b00485082161008104060748621031a000034007030120722205080b602c8040d4120320411403030a04004042d2402c210040020b1400306c0740348400e007000b51020410a03100062401d0500965526546907940e94281110b10360040322003260071020100d408100c4510900025840745481d401c1150315152041004080d120700e80d001142540001d010100440e60000c40312059918400740822900d04501c0400c0c004c0c4034a5000402054001c81c802c0c3e0131040719000481200d000341d8410303600b141c0300c4443c01300722054950004415802000b04152911a0107441e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 726050530 1250 726049280 726049301
    0x3060c0309080d05010501031b020c1009090f050613020f1b0c090f061009060905040e0f01051f0807230d0501020f04090608030a050f2d0309010518060a 67
    0x4954400650380d480c2d07541e00121100020103071200c006001c00c0d41d15118640344060140c0c005181720f010b088000c2c1d00e44040c001180e015032101c144442449006404040080c200d213002001039114642880004290a9804510420200800381d81140f0f842c000c2d520f59024403801c10b458803c1c1402103115207100884203c400e80580449101d0580d0303030f918154403490342108005218030701102080b900d1400303000004103101090000b44015075008200341d06486080c0c13400600b0007400e0014074948250324581c2a02513003840c0030000744203070107911611271104e044071400c0308984400d415611140540100180c0071444210403040140c0c40c443c0c3c102510b0054044404204a80ca4280c20f80c0d0000c80c4103560f0110000303003004500701a11403500206040c001035800d011082d48020800d01c01c200c0307030a01412000c1015100300d60140c00d0824040c6c10507031844c134411803943d00e41185810440d4810125446c12002441d00c5d00540c510964061032000500b13000d544d032442c800011302c0e5400c40e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 726051780 1250 726050530 726050537
    0xf01080319090b0a050301090f05010e061e03010e0d140c1902010c15150905010510031d071e14031e0309040e03030a05060d08030a0b0f03030310081b060403060c 71
    0x300024851190b1005003894a41c4c0d5403229501d45c1000c1030b550695034070101094003245071100400c2842c030f00800094215000302d4201290449190314131441900d1400a2a41035191a1100305018000500d40700c03044a9526032074003400341240040020300808284805e0b03a0082401c0401c0084014104014680b05041034581c500080d101c1c02f280c40f6500b201c804406540b500714104038000c0e00804d00042c076400400340410340c10000030441c90345080d54504240750b1562010148506038401904121010f2021942e02907a2200400c1d00e8104682ca14440001d201501140401300e419503000c0c00c0350040d000f0031081e20580c0504000342481101c1c0360f01404240300000141c1d6540c021484c180d13490100031500d03810f00f401c034001112000f500c2d0910a0100d1034200c0d00107000e03c0301780c0740c1c0003e0311a00004c007021514042010203e40b21000c50f07140c00300004100c202c2c007040ea21380003550080300c11a801c0d64080c0d500440e00c18a80d540c0b4507413122050008000003080c80e0001d6030300c20503519 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 726053030 1250 726051780 726051797
    0xf0f04050a030c03051c1d0d090b03040203012304060c0c021008090712051e060601080c07020a030204021c054606030302071e05090106050304060e03210f01080319 72
    0xb0303003107140d00714501100406d481d200d003440c20345000d18012034001410709001910007180c203184003500d4504640b04000840c0c40220000381556003c0d405115103a01503881005280f1101141e000e00c01000c403000c440d01840c242c40040854403407400580303074640c0500340d644844810074041d141c42400034001609441400004030743c078540c80642c07030284ad124400500c03010b4100505034a4410004200580d560f0049081040581c0d1017580c1c0383d040b039242e4a2041d40c40000d4004110140700c40d420280d000307800003501c520401074a06404082d01c0c00200200502d4882d40d5040f01c0070599906080007442c0410040c141243c8640c40070340c50304858103c1d56a510806181e400d058460950bc19030168110503000c0107500070700c0c50a6201c240c410b01070b900c0000c0c00e1800203020b008042c01650104040440010100491a4031684444044004481e20780715000030941c1d6040d4850000f804203911000441c034504c00c00c50030581a10104400f8504000c1c01d00ea809140407000c1407078000300301050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 726054280 1250 726053030 726053047
    0x6052406030a2705060a050c0a0c06141503060601020a12122415030b06041a1201080601090605011b03080c16031206081506130603020a0e0f0f04050a030c0305 70
    0x1060003c0000010202c00d070010300c9410001d0411307000070701c11103101e8182002c2210000c081c5040700c00ba0b03c0d803800c000540400504200f0020400400c00c565901400c00c1800030722069071140310a9008128110b90040e40c55500498031640c840d20028904401080000e9000f4000c11080a083c5421000001d000c24407559100365242595180540130311426014401011520310140030410a810306100c4135545401081341446a4071903607540d400d100038810710200c0c0035001c0f1b0f40d01100d00300c0025403550311240007940b190400c0c030855030014030341800014154003400d14928000000000409500166142a034030a00001d00c03104010302d00300031050440e000f05036044201802942c402001804007440001129100e400012043e031140100e00c1900003071000c0d0b541e0003c8166410851845001d0030b0700080c1c08250402507201482d17001c04140ca82c40503030aa84182c229071050461915441c9105098170f1382690040d110360030150a2202083c05007007042c900760301c80d1074001d1400108 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 726055530 1250 726054280 726054311
    0x171b010603150b030f060105130e0318010e03122203080304050304030308061c060e0f01020d090209130b1b1902150c031611010f02120406052406030a 66
    0x4540080b2040341da0203841d080110310a114004031028181c004000e0003804103040c5940b002c051141e144940c4682074002200351a5400044034a10702e0b2017181e072a03100b81c0e00391300340d0461003d000a0010f04103003c3c40010b8500043d20030401090030071117510f40070020281c020800da05401c4401144444040000010343c220b00461086000700301a40d103031415440c00030200b66025001c0c034420441c1e98280a41301c0401701a10100d02e500c03020024034a07140040c407500300035203051a01c0e05948041034910f015007568020629461003101e40200d907036500380146c08035a501130b40c05020710705100e001416101d139290518080440d00300074a4284200c40000400500e41c2d4844800184c01c5201071568100d140c0d001c0c25001101010321038154505000002e0b1450014003852080103c0b071944c5101460003944803a206141c2d401d029540d130303a0148021142070b68160790441d81c50741303803a0019444502d051541081401c8e01c0004c40c8901303402c03000700320325504003404c14203034159035000c0b500c0040070307 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 726056780 1250 726055530 726055541
    0x50304080d0518010203031608060a05090723030112021302090910140f03030307140d06060509010f030b0d060b0f10030f0c0314040b040503040f08030d18171b01 71
    0x1903a696060382c0e8001d1020f0f030300040040403d4681558018030910480c1c000600030b400703482006140082080c3c5d50100040e200495591249402040e00414071207000d9002702001d100b06102c0c98015814210712825500511007442900d02e10121a40301d07000516181c1c12903203208242d1400941004134020000301005803d40b00c08000b222000c400b04285008840c480c12800402c507038400c6001c0c60613002ca40c8900c4000d0002041042d070703610120200300c003841911883c0034428010040349031560005841907000c1c0d00d00e240840d07032030031034141d45074403a00a840b42c40e100034240b00344e41c0c1819900c07400030300100d81c0c07103030b80c0500d00f000d50106a440e000720301e00c244010b50b600030070301c80e0ba0421543e040342d5041510104140c01c040c540740703e41c16100046608258003c04010403a900c03800d0041c19406031b508001c0c0985612200021099000000b0740801c9000117010082c0c40628501003100e00340308000107203106040201100e81c92100c00141446e4540c0c101850007061051400508494 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 726058030 1250 726056780 726056803
    0x14190c21090c050102191704080624121507031d2a0603160c0c0608010806070801180b04060914041406040512030702010f0504080306040e030a05041205030408 70
    0x1603640c0c03807240500260503415001040203002604c01c505000344034280c0b03699511009003007105d50340d080406540086c42254000c1184806480f040e02b448503222402c1d10043d004000761610140e121107607480d1500c800c48118204200030072401890707040c07404031640014440c02c10b242d6221300c405030b1041c07288502d403501401440940801c015900c1a907414581d100c5064110312520850714909448a80840c1c1d00000c078116418852220300340100d41140880c18000c000c80f000080c00212181c01c021024162861742c3c099800d503940364001151580386c02d02c2220314480c40c00b05902010790b50740e880703d900110042c00100c1c0e543d417a1041081690044001420049285800c11042c42810201c880500c1241d00103045141015101c680c0d0b540d180e01e992407820302c1c0000208a40d00d000758841141c2850020040c000b0b03182c01d041010392904125042350180741002042d4a9411b00070044031904800c81d202d20741006d0414020189401c0c00800440e0544020400441c550500300a2101101d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 726059280 1250 726058030 726058097
    0x90c06051c02090303120907170607080906070516030e0a150306081c050a050c0115090f0509120f040b13051c03050409090218090f0114190c 62
    0x495102480ca0070099100540140540c41030102d1407050b074002c41242c40c02001301d0300c4218142c88195450307081c0012980850b200110024810340e000b82d010802e14815820358845603101d5603040c60881e150a4100c52030800034804001075044c403034a410142d01c03014083c0c41c00360b60700b15000001c9034040d01703107030029080031128920504d905a41030144034050703c80c000c00782001c260602401d1841418920140080c020003144203d0301c079104a003600c0c108503184000744040103c00f20402c451080381c0c00fa0707041403400c0003880003140e40a40287c600402d40c2c400101104007408290042c00d03003060342c2081e60034004202c00503148400002405240c41c80c01480e1003258909000c11051607000f20074460011444c1c443c403c040f035008010344048460b29240400d8440d80c1c0d01c0050507088041f5841b45d01e030640c183c14080015800202c10040f90303000c0b03000f006910b802d943c2d20a16540115071141195030050641144852a50049003c020940c182902c440b10041d0460a404a6681069251 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 726060530 1250 726059280 726059287
    0x2091206060420030720070306060f17070306021c05010f05010e09070e040f0908030403020c1e030601030602090105120106050309061006050d0e0319030b090105040227010201090c0605 81
    0x1c40c5410b10a6240640d030140360103903009542c00c0341001c140001003d00050000040384203800e03000050721301000090007025110204c1d128a0708100a141c42d0158140300d4800d40b0012684290310402d0074400c100d00c40c0100552451a619000690312070b038070f940300e100700a10342402121090b0143e90301034500d000b04004540d0900e070004042244480360a441b039890f40c020310141c030760070404004050409540200341d40d840c40c640d110180c201c1d2103004114060000400c0300307050703011440044001d001c07070391a000d01d008140c2c0c0c00008019115010ba040d0030502c0108009500c1381d0040c02c004c08181030182c140369104e460014804801d82c80b20b40403440001c10090301400c28031070707141c0c00206444440800c0303041c502c0c01000c5002d003481d0056403a40d17031351040800110400a0f03d802420641050322030701450030f03008001d024007003481d5024511900010130351f4505402600d404054210944450780c05030b020080c030712101d041c2541c0c1595600e0844c03101065400c03001001901d5980c80703031640e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 726061780 1250 726060530 726060541
    0x1e020408120a05041406070807062913021312120807051303030507050f1009110d050a1514010b0309060615041e080a03020a0b070c1a0a02091206 64
    0xa1404000a440304040104500b01c042c0f40c100b426103058070f6070a61005080210400445d9241c0314050002c1c0a051004c2440d80411005401c200d42c0e0a4452a41c420503681d074400100d20200b14480180c3d02c10003590720020502103c0e806070450310045200e00911a60301c68500d00710382d41d24801583c403007441c0201c00800c4c0c0e4010044640148407480d0840c9411061102c41c0d2214101d80001001c02100040b0f2006005080100d06604040c1388107444484d80c1721400d900082a00d014201d5046125140c514400e20b422000401e8468016002e40103061503a0340d02c5920b88034517a802004180d44034444035451140d03d0f00a4060403da02e0104c1e901e04042030400e207450b000400302403041c08810a4103555424a00a40d8100c1d0860312042086000461000044103020340241005110b0265218140340d030003e01c0c5554580038401f084500e44600320b00700c50342040400b0150001c030407081b11400c0ca1080e213010030341c810060300b0014241a840350018600440c0b0001109203503104006020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 726063030 1250 726061780 726061783
    0x90e100c020115120203030f070302010b13060620030313152c03070201090b030613050f1f0e16030605030114041b050d06050406140c03040b010603020a120e011e020408 74
    0x14291300d0401004001030355002a54a00c110742c402e4019500201d442c0c810103001350001c002c00403004043c503060310202c0c0e601100511b41440b4010005000c0214000040c0010700e00308480445400a18650f07a82d4000303044a800c5114001c0b00c2038100c2100b000e41003d81c900c14240400b00301494005600b030000c118592250484003118241d030800c00400300145e0300700d050401261030b50001e40b0740b00c0d903c10b000680031031210784090410303900704000c114003650a000c402e44180d0f00401c0c00c00e0243d207024111410100303075020f43c10440c1d44071001f00d2240d43c0b0380c20b0700c05081945490041122910bc402003420740e8240869a0b042d244850b0601c01008500d949004441b50b9450102400c1c91500d000148150b800b00806405640d03204085000e00900350811380003095084403102c070504081c940b4080e29881150180c0340e00c00802c00110305a40320340229860045983c2c0c0d042640302c5003042110041004248100c1c5540d03a40c800300c0c1d84080c05c0040f04079014005c030001611186003010380c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 726064280 1250 726063030 726063071
    0x60b190815010609051f050f070302061f0f06080402030709021b1219110a0f03020a061406090103080309070f33080f070309150c0e03070501020304090e100c0201 71
    0x2004e114042800780600d458040040b18404800c114010a85080030416a12881000e080340c01d5134900041010070f00d5000204140079030b280c02451103e16409010061104000b40190f40c500e0828000403c080791003110f07a01d400a0005007510f03a00d66a40341c440049901800000050a001d244501140041403011001c0c40300f0401e500d502d400d0000001420340782504140c0020701c840b509507212074503802c0200c018000e43c0900d554012114500300a580c83c0071445081303503054246109828a1100c95003828000c9401404840381030f400d41e40c5040c15a0001070200e04140700d20440001c83c007110760b0004c0c00420000200600040440b03212035071425102c002000310400030040c007a10b65900a9507603610a00c8128926010745a104086020f809002e20251a9030a62112140c041d06968022503140c0381d41d03110400303c941c0c00c505058035802c0c00c2c407a99002d03030400d2000b040160300c07580104102d88025804d546a0407410b9031254101d8424450034001030795103905082c80784400100b071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 726065530 1250 726064280 726064289
    0xa031215090b09160e0d050a0219170109080a030e0c031b0102070602010506060d0c050403080d1e2a020f0604050f07051f030c0507150902030105060402070807060b19081501 76
    0x20070700003941c008010b440c500d400e01030725005401d5441d2140030b02c40b003488601c1203680e00800000c00f074035051b400745852b104280101c8400810156900e40c5e688414490003007e56408000c2a00300f09030a00c041d8010300350304010302001c1c0240c50850400d56402c0c4950076180100c5940803100c082e000000a2608070182c00600644e0324000900003150f80c0d034001d4030482c440a110201d40510950b03c122018091503000821045000c41d03200300c00000c1e078011110f0320f010036901c1700154801080741000d07980a201c4580c0b0b40a0710040da105400b030030082c0900d01164500440d0149503e100703c0d145020800c0724140e80c81d4000b0203007040000428407886000700381c201d588140c00c1d15014002000c04003890603140a01d41c1c1d8088409130540582c064807001900141c96400700c255024845000d803070f421801300e11075440c050002e18980342604c04d4a42650b04050402e003001d206903944001051103d0100c3d50140c0b034500d50303240c1c0410b681d0580015004083c003605008480d5164034204407010b801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 726066780 1250 726065530 726065551
    0x8040825051f090b01030803100b040b04090c0c080901120e0a230c0a0b180409080a0906081918060504200a030201210f060f080c0d050a031215090b09 66
    0x103c0010a100d039036041d040d2a00b10001c55502d860b41400300ca8502c0140d0b000c83c002d6000410f0000d41002e9000c003170001c40b40026020300401036100030440718041c07c514001c061501c00d01083e02c595114440b10308580c0104000080d41503106100a4500140c4c007000f2540c1003000c1c00390140c1c1e0340300c0c3c4141c410309450034001482180d2041000403015401d60055001c15180400c280280c20b000c41c50401c0340c0003001d00204854541403c04102d50740c010681040803410758800005c0c094441c440c5c03a4403544004d00503030010207420802c800a85034240e41c4004482c0708001c03103c00b280d01845114010740c8251441280c003d4800e2514150300c084110a6218445000003000540d03000414a0340d9803c03481d010f0032980c880e40100400920105014068080c503140300403d280705880c1440d41a1030500044500388083d4200700001c05c204018001c0043e0001140d24000038042c080a04060301415004540e18070f0011241c903026600b82d02000c1c91684076103824480e070a000e5811a0880c14009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 726068030 1250 726066780 726066791
    0x1e0f0604060c033b030607080f010605160b0f090609120702040b01031e020c012409021606090818040c021b0307170102220608040825051f 61
    0x20809880b40300c0c0d221014050210003000401d0501c88490201c1c0c16040084404180c0e071030741c000004c401a42d240d2180d000e8070581e40803420590003280040c0c41982d0060400000b6070030614200c550350002c3c0c0c900f14166a01503036040024611039907491242c89901c014481a00d8500740051402c0c10140080a45030071030440800941d0200c400c0b1242c958040e5070206690113007000490050490910140540b6100f1001c28502001c0c0d030014003480b2104402801080d604103180c02c44200c8421807c6903001a541c1e041103034082c20b030040e20713520480503a0b50030a411945c607042e09540400c038003203501890000c2e10640c8011400c0c50b4407100f00c002c0d10100000c081d6208041d54070000f40c9565500c0003e803130700c40f4401d960304100d01c1d800360881c050030f0b0070401052185280031b0340114100010000301c885540b00c0464984010100f00c40c3c490740d40c1d4200751110b855041c140d5000c60008840710001c102505001c8041c0d4410500e1203102e240100300440802d000c412180424480b102d00c0d860501c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 726069280 1250 726068030 726068039
    0x9011808030a0b1302030a0b100e280e09101401060c02090a060801020703020c10020606060712020c060c15071103040306050916031a060306070f050310051e0f0604 72
    0x590350300481c0c00c1000900b0b043c180380090b04441c041d4803201441d50000040210002e0a074211007108101038a80f82e034104441da505650071030180c2010341d0004004100c4d440030300850708a110b075141d10300b140ca0305110b89600703000c031310a50102c54082c4154040c070720581011049100d041303415141404154100e50400f44002d0131103640f000d02078400c5014a0114400c10003d5102100610500f4002c642c1c40559141c040d484450407468076202e0450441e4490310380d4008100d6510034803000f030107036107014010750700c0e800100d0003d0030800c2144121038038140d464035560000d183c2000200004c0c03040036101040c1c600010b8001f0501c4041248014010306015000170aa0f003e40307500c8600441c0b595a041100c51500031601c0c03902e60f100325000d1001080c480c0c03620350071211043c4459103640580c0c4080500d50b481d50b040c0c400c2c400141c030380c4140c0f0702d02e18403030b1018607084049242c1024006135243c0002e2a030003811501381c0002c0d80291a070303503520314100503803500b103201c00d4403a80c2c2410303c3d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 726070530 1250 726069280 726069293
    0x9060501090b0d2903160e060108040c0f060c050d0c080d09030509040516170411010e030c0312180d05060a0b19090b1201050405061b0c1203090118 65
    0x1e4410112800c038045002484030550707810104c110602601182d510004804a80f6414054440418001c3c0944e5070480d0802c000003072054196803041d00c100300c05031191001101d003a100200300341c0f1040121030020400209013002540241860f03614418000c07418107005042c468504002018442d140050800041c00c05040c0e60183c0086400090039140c18142503940d0f1044e0506182c0c040e107064100a8180b0b4940140b00062540d50340704a041c002d0400d0403552540152406003402510000103c0135602c00e109441c0301d0b160180954140d02c03180c0010a14119000c802d156240f0030104212850082700305c0020220081114aa1040041500e0b40ca0b00c41c0340103800d0311000303516006c50344041c0e2a2402217040105902c1c2054a8035651034503208000c6c0000051a0b10580317030484102d19880741401103034055a0404040d007617075186e05455050062100d0168460940103000c1c4200c440703028881c10415140748080f49a4170714058002c0350840314003500c28410880c8544151012496 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 726071780 1250 726070530 726070547
    0x20604020402030901020d021605070501020604081204030e06070510050702071d06040921090b091003051807080a1e080a0c0c0f0303050a17090d051606141009060501 73
    0x4041d500142c3d01c1c1c4500d544540a4410b501240660600008902c000c00d50300c251910409406141510800f075100c000491721210140e801030907902081c4022213440c1261600113402902c2414080c99803111034000c40c01d00d410075201659150007000100101c0b07007003030050b130b5403040c42131024240042c20301044901680340e600301d00c1201e2020800042c41c944940e0f110341040c0c0d4024403504442c10b000c00b204100f8880c8441000005071840600040a28410066803820300b4024054184e40402c4101240101801496100c5284402c501c01000e881c0912615014061420151000ca0b410341403011100e01802c100510b003c00100c6030101195809041e180c072a080d03072030f1090f0f000c3d065003400710714000580c10040c0e551455000000c205900030303008180030402a02d6001c003402c02039090040703940b000c80300300704070ba0001543e40704254482c50042c0903203602e05c01c1025001940d900c6550490b80300600f8240d60700b40c12018040700d0042d004140e0014030032000148481418500001c0c00b10700c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 726073030 1250 726071780 726071783
    0xc0705030d021510030c030813050103111c090602040b070204061a09150c01050a0f1811100309050d090303080f091509011d0d091715100b0c010f050f0601020604 71
    0x20600f00204009004081d8030100550304024005142512410000c0055210701c3e07215006e4400c4080008255029000e6154228250602c0d5030412181c20100010b5014440320f988107a035640410400190152000d00090131000881a49954103881440115107064102c404180d0702018804900b1901c0c0c0210f501d400d40c15280325a0038505420707955400c1c040c80580c000076500340810402ca00300958440c0c101c0c0101568144040100c141030114005802140908200c4401003600702c241401081010042d61030301d000641407800340c0b611400d081c048000400050920f400c2003040c10751208401b50060741000c40281141001c0f00a15528621020411100500d820000300c0e1054207501903400040c0c031055900d02c0300c003070b061800e48510100d506503012818114000c43c44030b00510001000002080080480d2503c001010a810f84000c0c038485c0075001d5120040f40102820340070703141001c03a0303100206024008050410603504010070388184400b2100401869a038002031044d0880d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 726074280 1250 726073030 726073063
    0xc030109080d0e03041d0a0b270603030c010212060a0501080c16020d020607060b131118150d020d0f05090a0b10170f2104090b061c020c0705030d02 65
    0xb29100d400782421030080d9803007021200d443c0b031b88503014186403030000b612508003401c041010414600070402d8401c409008641082d18440c0408000306401c0092500034400504403030038400181c461a082e80d21640798024895101c400740100e5007411032408015040900b0060002c0c82c10540000c50341c01542106015031010520382000d5403150010202465005403d15a8034042414884058942d144000f40929086160014400ba042c804c903200d14010210162428841c04101c1c03000ca00300010456000d000d0b5048201c07070444c60002081450807007840941c40c0c5541280305802c071150140025003c908050030000468000704440d408a5400a20b080c816100e82040811041c50768018080500c031203c5109035410001803540c10b190400c02c200c0d04200c940da011030707681107035030160184070803c03d12084c42012415000000d02001c060511803c10221a155800011540d01c0030800c01c0d5000400701c0042109100644c0a0101a0001c09480c952104001d540e46200201c010301c9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 726075530 1250 726074280 726074291
    0x131b0f181a06120619031406090d0f0e03030f0712030c0c0206190e060d0603110303090d15230711150112020616030215010602160506072609030c030109080d 69
    0x1d80c3e180200400003003080882c45100b15268945036007c0015200c4000591040c0c100240c01c40034005180001c0c0f600f295030341d04414014850a40380c48071201c00d925490301040c00040004846d50001d0032950307000304100a42004800c4002d0102e4040014220030031500c0d12445002d0f0310f4050460300780b00c800080380c4203600c9007000201e688180b4101c4d41948418005038484404459400c24401c8d240a00100141c0e216090205030b0389101c0c0034025a003282030f440c05900440c05030410b1404020381c102d00400c0c1603001c554800200c5550341c50000d00e03049220140704100c0d608c40e44d81c03444400000c0052070301880300c2c6120031101205100d8401880d2000b00c824085441d4502a80c40c0382e211200c0e4445406072500c0c019456170001d81640807071140010000131041d100003030341d89406003220700c440b54007030500e81400a81c0e402400203958020000d00350180c07a4400300400300e0300b0350480c40165162403030101054206549444017510a03030519403e100494240012540c030311a060000040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 726076780 1250 726075530 726075541
    0x108120d0906150807090501050a0501081b04030b0f0f0f0f070203040e0906040b060612071b0218090120090d030e1005120c03131b0f181a0612 63
    0x140000401c020003543c18414002800c0c401400a8001c0e924540251803080d9210100c0504070780c802d1046540c00804080101b11079409003900682041c11010112240307144a1400d40035a40300d507000b2504034085c60304104c44000880f0300f1581002400498130101c1c03c1109004084c480060401d49503c5400340c049000d984c001c004490003042c942c2100052450b1900400ea19442d0440c1c042d501c0001000c002a03042c90907a08440c1542e44e00d00103041a5180d1440884848070b103200c843da003c05c1c103090310303901599407210045140340054079011007074034190710247d00f99814030102c0702c040780c04044070b510902c0710b5100f50381d60790b407080c1c8420110742c460741002c0700c0103150320400d80e0300540100248940076511034000e000341d201552240503a6140c201c03050140d07110454007a030710101c051545000180811400b2000c004003070780510705003600c5840d010703840c0002e40e2041c1c40400f40851384041c1d26085014800132905200d0400340d502c200200030a00901c1501400c042e4886400c0000d40b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 726078030 1250 726076780 726076807
    0x406211b09090303050910020408060f06040204030204050c0d2a08092415030a1a090a021201021809011d070908120903060a110f0c01110c0102031608010812 69
    0x100105030058050060b2241424003500034103094a00c40d000e401110701a0090040c03134022103003203c42c40001070640c2d9552000c01c0c2d024100241206600980030040000560340341d00030903025203104131086580d07215100c0d007030301140c0d80d040d049001c0c0e0400215204075000c1142e00d2040c1d504650402c03443c0303951059140d40c1402c10141c04000c0c1c5651f001e00d130402c2402807042d054402c10700c10102801c400410003c02d5524400600024140e011100304c01038808001d03c0d100390404008000c4031505c0c01c0580c0000c0c0340c1840701290450603035002c141040308840001045075800300a031500c0800e5410403034502c14400d440a40041c41c0c83c2d4800115802c030303115480c054024129030050b222100c0d000d007201d0b03180c0d174040003406200f845040c0100301d01d06003a00c24801d844241c45081480c006242c801d6001035080008070703002c295a80c42c0d511242e900ba031001401d0103080c2900040e5603180031001005040c034940405c008200f50071005005101d0002040c0c0d407042c018201654840e00003000c1031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 726079136 1106 726078030 726078083
    0x10030203100608071a070c03060c09050415030201140d050c27010f0e010311030a060806010e040f081e120f011e0510020102040320040621 61
    0x4111143e285c074018030070070f443c01d03662504158041e1202d10341e10302590300940d0b0190b250340c102d80d24154130400e0040549012071342000b1066064020f0054138600f80402414000d4880003040d20401000035552080e804080600080c070700b9101d41200f54201488810f00703040701c0c803201404c42c1400c90595140c41d0041e905c044000480e910200c0b900c42c0c00205450506644041072a282299400290300c40d00c1d0030840402e0301d501e07268249290400c140d20010740d024801d1305000004a0b0590118202d540100c14152511003214003542c841050a2900d5071215000074082e4000c54580d0a4501c10080590b2000d4140e0385c1c0d2108a42a9240e0194000c4808000b00184090f107840a06403100da405c0b0b20005040c69129170700c0c1e50728007047e1046d08442140c3c1000191a40c40e186c06214003030121628450a4100b00c807800f280340004020004108079080811280e40901d01c0520 = true := by decide +kernel

theorem cover : BRFrame.Cov 725899280 726079136 := by
  have h0 := BRFrame.cov_init 725899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 725899280 ≤ n) (h2 : n < 726079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
