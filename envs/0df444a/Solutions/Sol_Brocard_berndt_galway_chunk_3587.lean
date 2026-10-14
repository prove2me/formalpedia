-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3587
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:05:28.563875+00:00
-- url     : https://prove2.me/submissions/d9018dcb-d8c8-47c1-b32e-cfb16fe669ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 644964028 ≤ n < 645143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 644965278 1250 644964028 644964053
    0x6011202071401060321170a18050a0501050c121611030a0309020906120c130e0304170f0c100e04150e0915130209060303090402070b010602010b04020414060a0c 71
    0x2240c0d136a00c402c3c8203101c2d001c01d503070302ca410781c403181c0c1201c1d44201c200c000d003c100014000021a80790a010406032000c40d001298426500700504101324001d05241da5220b0206606540039483c200119004182e100200c6029030403400306068991580c420400f04626541182000c10101604140d02c894042c0001d28980d1140e42e4041090302c21401040350800e0041c050318803a0007505041011807801003400c401420040700c101303070321503030400141003d000030110800c044d000009011030008103600100840d05051000c0f91450064009015942c000c144c15050303000e4a011520317082c1078460360014440c3d482c09003000c1000c1c008256900c4044945401a141001c06041000b507000c404000000c114902501d2615903070402c00740782c3c88150144d0704041e005003900d5001405a403001c20440e200310901034821591081c050030a120f20003800e004a030019400e1144606007441c281c0280e40a0394005110440348284410400100740c6c440a00041406a520601000320303182da803001c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 644966528 1250 644965278 644965313
    0xd1103070804140712111206090d0e03010501030203030f071403030c0a0329040f060b0f070b09030c06010612200406090f0e0609091009030e270601120207 68
    0x240041e04041c50f00700d02e51016000c0343c0c01c1070f40c0800c0040003001402c0001c8807090350411034218200309110702054025194206841151151100744815540e0020b00b00b8994022540c44460051144081500b6503c00b8440070f585036000b40000c10300fa1000700c0c010900142f00e89050a4020074200c046400e507041143e00071032810010482c00c0c51550140141d40203004220301d03100401134001212990300c4981c50034640581c3e510744400285088561046010b049034180d03c0d0b0304c403940e0100c001000d600c0100c048407210300643c00309060900010030345015001080141c00203071f080c224125209a248a070144480751680040000500e81c070304180c0c1000045003800c1d0303440f07081100281c440051a444003241d00300d0820108501c035480340e5140e401090449002d08262201c544075850008000c400e04030300e5140464400426800140b001c060700c03001c1e916080c180080184821490030700c000035181c4c84a985000840715803152010002114030580014200b003a0b03500c1b031502ca0701000200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 644967778 1250 644966528 644966537
    0x307061b1205100603020f070605010b03180a0f0b04020d0f0b07020c3703150207110103232509050a1502120f0f0a0203030a0f0605010c02060d110307 66
    0x1050615075101c241045007001c1c40074103100900700042c0450f021500c074881c9030700f095404110014621048021241e01513041a410320480d44c60341c500701d082c0d074820f4982081e102826119840104030104000a03e503800040300304c10560b081e02c072001100401001268440301140c00d02d40003d4a0170500e80b03d1500a00c1214400e2031300c940003a14020340414510f02c00c650364003815080d00c598203424540048254510a0126240101c0b00005c2c4403641004003c41c0044042c0c940a40080d400741c00e2040c050480c1b402c43c0c03c1c022006404a40482514022054641c07402c6051299041c8842e0b421035450780710320126003903174400c01540c2c034210071009001512aa208202e6450580c00d02005401010712046406045060180da200400000140c1c0d405021801c4540c0540c050300707481e020340f50090440d55407800d40b14020f443c0d50040710071903103a615005441142c8a440d2241406032001a1904040b1160f240c0030000140c0056010b42d4000b9222070320788040300c8087c405140240415102d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 644969028 1250 644967778 644967821
    0x61b0d0504110a1a1615050c0715020424090312022a06071202030903100507030c08240609040c09030314030420060904060b0318010203100308030702030706 69
    0x200b01900000f50b200a965188414000e0280680300c8100d9800c202a1011501d1055043c509603c101d0f0440e407a0302c0c00380717181c0f00801c201c840200c4009c290061040d203035a680c0d02c01c400e401c42d049024601403862020000305071648a40305608c02010b060301d95007030061141d03a49035a040e400800240c1114016001f4034041540a03188140020122010a10011030150010080381660096603005054184425800811103000b8002c032030190394041c050307c41200030400401c01030320081d0341400000b440c110440400794400c14405004104c0c4c3c41c541c1102909800c1d05030040d999004a10782c1c854010005002250341e035106078441245242c0b140341c00b603895030401810b1000b58113032180d2440c0b001c00802001074480200d80c845031901e0740034800598600710106005014908409030441e28108000c20011040030256101d10906e19500f00c21101c0a00708034240d000035500c3e40420b103080070090000075111405982d00c00c0c86407040340d0600d40141c68103416a0400c42101c5030024a401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 644970278 1250 644969028 644969063
    0x20a15020a1709130b0a0801111911031908090303130209060f1f1b0305090d150e070e0a020a1704140601120303110a1d061b03130501080702061b0d0504 67
    0x24080c0b002401208009c000400c000d0360f00c1203c030311680d000305154020425034070040c03500642c1021f032000c2280003140d40b140c07216011031404885007020400032442110006440507000000c480c030505580d46441002c25060b4240150000054069644250496012200e03900d60100039020503081d4004035207180c01480001e00008070b5101685150b10310305d1702c51004203400208070b030f040c2d00040d5403592500d80107041000c0040701154100d100582080030b45000700000180c0401030b103001011049060702c43e503900f4422881480a103402140b650300c5613690f040341c0000060b620a00900a0040300c403015210319080440036040f0f0f1003100d8005100205140d0b051049a11301034400500614050b91200b0142070242c51a887e00541400b80380744c402c040d03c445043d1238046043c003656886850b00c10322502d0300da070004a08a64400d0001c0130024203076201e98074880c00b881c0142c014121a45803007001124a1131100c9c100e501948040050381500d10080c410f80e407041d4005c0250142110052 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 644971528 1250 644970278 644970289
    0x4090507210b0c0a020304090915110301081b0d21030c09030b0a0f0908031303020f010c17070224190b010e1201150b0304020a15020a1709130b 63
    0xd05001c1030010500020008a1460242d80c01c960b0420741c1c2e640b50390132540101d144d031155130056003203103080045540400488018001c1084140701081c000750744840300c01922030009101c1c101c8254040039040d1038545034030292088400380a0316502c100c03d500d840c1c010350036504001841041402c000250b4410380c0c10700c80e0250f91206450000c40403443e41d01ca4044107071014002c04036140d564050314013100000c2e4005540558021a420703201c1c80c100f00c02602290690300290090702801c21300046415041c8218118079485448544e064030788507030f46144c61400200315030107621403405280a14100c0e2074542d162008030802c52800d0b40b406198125116042140008105007031006580a9a0300b05500c424a204c1c19a00070081d1011009024003515140259400d010f1141101080700902c0d140114400c6000fa200c01200940d41c2400302901584180c0f09401a001413110600041d0300b43c100044002010f0000e03414544c003840081c191541c052140c2281c1907031503030768140c5410328 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 644972778 1250 644971528 644971559
    0x30b0c030105060d180f2003161a0c0609010b0406270b0a030803011205060c0c0607081312110d0f0507060e010e0604050a030e0f0d0b0403020c04090507 67
    0x28004498155450070000c0740b118080c141801c4012511130384143e04c40e0903940c4120201c50740010741d25038843e40506010000d0b802da4a0203140c0f1003901c0042c12018140080d98140a0011012a0f480c040c40c00b172800060104030300c4600d00080741002800300e0180c08002003400751010000008210070382e04200400c07284581d100884003a85045009452000e145d0945040c110610b001b08003451301400080706a20703550401080c150700400007140ca86464032510300001c0c4180700b2102e040d00c1d10207595865005960113858941c0c41980001c82c602e01c1625515006966551405202111a501c4030a850540e9030807400103030310344040c5005000104034561814180e0f040001d0000b03400a0020324905c01c00320090040d40d100c90981c0844182580301c1c0c90075040f00c1c01640c81d5402c007454800d48403146508141e002034854100d00b201482c002c03400048243c4018215051011260380e0107245046c010400d409500a0310300880c001d4440e8051664118411000341c4151410407240c1540e9911 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 644974028 1250 644972778 644972791
    0x30403090e151f110a03051c0902030307110120010b01090504020a1704080d050108100e010b0f04180c0605090102300d0908070f020909010c0813020102121201030b 72
    0x381e5080ca01070b40c450b9001c4801010401c2403561070400c09060541d041100d80c46824428071806403840141b41e804805414083c01c1b03c4610024854112421400d40302e801602a501d504100180030000d24060058000810103041c04641e2042c0c050001c240d0051603220034609035101c00c00c0e01183c0d81e0010b040400340500301c2d000c50402600e11f0380180101e16100705a400d412101c1e0100c0c0600c01400255240d4828180d410300241d0784407401d80d80c4500080000f54552424002030000a07801030103861318000002d000759034440b20600421000e04400c40300000b0454018400d04085100c046083d00a004a602c03070640d900c2195000a1a0207001d2050040108401c244c1c21610440c000020785003080c041203284d00c0d46074082000e0014003080e44001d0100200145000810084280d2905028000c0f100840143e64241107142a12030b09495a4000303400c10300010703501400d070107408160b40c1c010310440d48000b0018422074100c2d400040070340180305109004100700000000744590004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 644975278 1250 644974028 644974051
    0x41502060906010510020a21090909110108040813030c1406120f04150c0e01110f0a020405090705131a010c03090b0f0f0a030903090f050904170906030403090e 70
    0xd05550041e0b10758a06001d1103201d0585807010b45450f901c00c22803a034483e6044444184940c03440f180c01142d41c0e50b40712150300800c02c101c0001940d81000d20812698a4100c100008042c2d020b500456001d44020805c41c0c51213801c0c8600c0c020a18010500e401440c81400f8240b00c3d02d0401103440d10402d550402c2e14805c0200f0045a1b00b00000034045540001030119882034a8403907103801e010030000c0c0d80c0c11601252610b14001080d0781c0c0300c40c082c46444000e8840003a107161403043c840e140d8441080c864015407101c9440d100501b01a80501d030720071041e2065560f43d03512940024800303010f42075412803650315501090403034000c10003130341c030341d0107003400c01054544180c1e5014010690500c2408180d0f200403c400c0e031160b10020465240141040e403180d5101c1c1d40940180c01813681c1c12055000600c4803a001c41c2c81141c0c3c0c0354087c20350328000c04c0c0d10220703600c0b55a992540c0b1b801c2c1c80643c1c0320a03c1400030300101c5c3c031210041c502442c0f04c3d84889074114106035030041d506d00020f10015810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 644976528 1250 644975278 644975281
    0x180c030303061e0510050f0c1b0a030b0f0c1903050a0b09041205030a06260f030c0a17210906061c1202070f0b040f0f0303050f07030e09040804150206 66
    0x8204601c0c407507045913400e50b50401c4d0440b144100781c5a0703002e00e0760203946614000520782c00009010601349003003101540c03205c0c00c07c03880c101400a000300500000303104000c260302203080071100700005035104442080c518500b030440340c40e04448404500909012980300d00600c200703500b160142d102c01100580300517585103080d48600007485000304070b4a050040000200b0004c02d0703190031040241031881e50341414181c01c8006040b07196000ea0302210240070b60089100714000c040102c841001005009050322022600c4820106415000d5400505420400c024141d10302d04001140050540c01408003894501c8440d07080080040c000b51090001600c1d40340d56500c4803449841890b000124411800c42e1285c0992800c00f050300000020942040c0c0014030700d00c894000c1c01915011500c015103940d42d4131280c4c42194280c000103010440074888098820498130141c02010f000345010003d0000c1200070500320354094500f55051200000e0620a0302624004174491000501c001d04e100d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 644977778 1250 644976528 644976569
    0xf061501020a0f08090402160605070e0a05100210110a02120403030906120b040f02130501020a020f06130e0a15060e183102120303010315050a180c03030306 69
    0x440c4210140100207060f0005020188507504c02a0307100340c50301800031960781d0b04440c20b030600205000000c4840c00d0511000a05d43d903c10051486240800b9042d545028146410405a120b461100c08214810118100c001c09500d0040c80da0198041c1f85060f526080494000c1c14000c0561454074441410003080000a501500b40d0044803c5494031540485020341c01d100504941c544030f80c0c1c0103041c8100c5041d003007825802011040180f40001e910582d440e001661540c100390340180d809070050030f003d6010f061000003000066402002e484d03103c0c4d258440c4079a0840141d5241007065a40c179461403c0300c49a940d1040a0700310b9092605c0490b03403503000901000d0a020b58401e5001d40d100218041c440200c02581e1a0041c1c54852150340302d401c82010008003a89406070720800140e00098481d100200031a41a40d4000341c0d483e51407094a4080c1000e4800501007509065581202c00524145040c0c44000d40340314a204c50101d9285041c0202550441c0c1c01990030183c8807060802d6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 644979028 1250 644977778 644977783
    0xf010201232a040b0f04080102030403080a0506030a0c03020616140f0730020609030a0807120305010308070305280309140f0d031a0a080307031103071218090e0f06150102 75
    0x480301c0380e0031030550300d0040c42c20340c103000d0045a0141607e58004000c1c001011782010b2130511501300458104030555591080541d184140c1c0313409084c0c43c60140060001d03062010042121040400d0001e110501554071901c510100340c58080540e000314210500341c40d024412140101242c4d007500b0040e00295101031203000c03102002040c1510780ca4280310440d1601000d03104207007001400d0b01c40307182460034100d2240d441030404603803500404002080460282c803031075050b250072000c0d0504020392981c0507a15984a0500202c140880c00499182039001480d1550303c1030150303030b01050340c00841c80c05004140c03030010741c8010303500160141d41654900007000d0006101900e40440c0503101521440b00200100c0d20090308082d10681c0404d540c0c10000040401301c1c400d9a40001801c1042c55568481c054550024500d14080d1542041e2034807640140195038440c94403016802e5541940c00101c2d010180c0300f551503002034844040c0b0800a10510742d100c099580c040c43e41d0204600000d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 644980278 1250 644979028 644979037
    0xe0a03020f09070909020408010b040f110714011407210605031c050d0c021e190609060209100f0e030c06030a1d030703090906050f0f0f010201232a 65
    0x180202c858a0016aa891140360800018096032100b107540720b455040d00303400f80c0348031240c1c2402241009540044400c29101d0440c3d452449503000b4140029a41d9120f0800c000344060181503403140b855a03441c4200c3c40f02107010320520386030440b40034445c6940f00d0a110070011113074080c030714009d000c10280d1000b1425000240480b412144e4501001c001601c40b40100c8030400c0c0c441c0e241800110355030b40c00044620082c40c0407030100361080c9619203401d80d00c985001444c0c44c40c990003100c0800203079003a000303034407614440c65000d03040072454408203e4404001342c481e0006101e50320b9064120350815400403040d64240c018044078010301e80819020b00c00a0002d9001907515026200046000d000000012401c0d1084d680e441e1018200103007038a030030307001c0c0034102c52410b07100240d40c0c0b51072a00c1c031400c8680038011944032240c0320108014407180c0720000d81595210240ba90840410075256030003140745a00d5840d0340d0409217600010318081000b070301605034003c49400304c0e4042010684 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 644981528 1250 644980278 644980309
    0xe0d0c090209030109061a090f010b0d021305101701050d03020309130b0901090e1002040302030d0c020301110d1b0c020a030b041e0b0912131e1e060e0a0302 69
    0x242c2d03640480d0380800e004026001003d000c4500d0134180341c020a51108072a10680e500b110402656140c0c1c4100c40042c2d070b03003882802540e510400c1007480f410702c80c1c0c020301025411040840f22041d41d91b00032840c0c0b0041c035100080001d0001140d10f010104c142d02c1203014103002c2e182d08a030008541e82c069a07034820b041c140e500c1140ca40d140d0f081c071020140c00800000ea4007906515075942c0d00c640c1c020242c0501705862070903000700c0d098030420b00c40b1403080d03804590f0018018103041d00714410a807016980710034166015503c0d44030350180381c204074005004900008800207505690111034052105864000703038104444201004090391700e0558420a40c0e030803041c3d03040306803540d141c0340c654240c0c5580840303202440604d24070140040408000d20520542090f16a0704598824075402c0d8400c10001c0864003560300c1c000d0050301002c800d08900004003000c03001c803458a80b222080201c101c030110342050040c075242846103680c09049407140328004c1d52600e4103241145e001890740301004080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 644982778 1250 644981528 644981531
    0xf0905060705010f06031a0a0b1804140319140301060c080a020c1807020114010e070302090a1e03031b0803060d0305120703051602030c0601060c05030706020309010203070e0d0c09 79
    0x4202441001c1d4850001d0743e8807143c040064030341d00c2c90281e0184851f140100b0091820000203200360403075002d02c94400400070010076484081c5207101454110103001990076100300c08090407030040030401405070046109220013000c1c541c0800411103259409128500d138000c1c00100700050700301c1c81d4140c0c1c082c2c0c040300154955640e04812840d0208281400e80c3c40031045652008881c90342030300501680044d4001d00c20400d100f481c10811580070b00c20f803d81c01d02900001100103100b0703809000e00341c4005190000700c0b0750312443c4410345501c51038048040f4011113001c100b010b80148502602069400805010f100c442d11140003d00008100c10302400e04803a2050805104204440703101d6000e80c820206804c003580300400a21007128140c00300489140c2c540e185c240000b080c1d40d0140c0000307001b051030b6820401e0403074a103c0444412150342c8800e10502780010b0082c0055031290103080001078503460902e1009020280c021b0459020761040c0e0710040110380003282100940301031800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 644984028 1250 644982778 644982787
    0x105010c05210909010902030403120506010c080c070608060d08040302010518130c08090c030606040e030702060d021801170f060a0816090506010e0a0608060103022502030d0f090506 80
    0x41070360502c050002c0070040c04201e00c2c20200080c021002a0003071071820340340b10529a072924035031002c80c40182c030003401090490990040e6106150495a401407061504894a00c00c3c0d64500b10760303400c103007041150b40d0020b01052002c40c0d8000c1a9590058044a940142a890391a81c031103a01ca10300020381000000580e40851903889500228050b2014008104240c120319048000780191401900021480d0010480700400020900300d00c07400200605102c6c1c0303469040200400c410144070b90a404107005440c00f40c0e94840c0a00310f840d44c003d07009aa130700c01001c407881c0482038071825241400041140b48840d14000310445030f0200703020b6540e80e801d845410000321030409581c8241801d228203440d50601c0f00490b4111011107005020600050f1101401564040070751342030315400c01802181045091f01c243d203102d0301303c40306040040c54902b45610208040ca50141c0c0000d007508040800001c5040400c40300d40001007500c0c0100c0078107000b010081907aa607070300c19103118910118 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 644985278 1250 644984028 644984033
    0x515090f0913080c1603080a09050415210b04080c0c031204061d030102041805060d1e08070b07090512010e0c0607020a080d08040b010e06012109061e060602150105010c 74
    0x10501c02d00c0c0181101c0e0101040d961f00e000d21890340076890b044000f60782d80900260600b083d0080308110041c03018403031300213410300c00800d451240e6070f0100e02c1141c0d1201c007501c01084941c0c0c06940914095540d45680e15007082c0142d140c5400080c85e80d0007503214050000083d00d11405a43c19182d1514100540e9401c480307640c01c40000030030729554154030000d000240700791240c800714152401c1c0141442241d0356441008003d0f040454054102d000c055039084513140440c4220302c142e0310821600e424000030740c4070404000b0045600c100440c032100e400740003a00d03206001c18400c03075241c170003070101500c40c00440d41c6031a020a403940c01a803012608100310760320011044050055102181d02e94181c80d0030007001d11209130313019200001448004584141d28402aa01c5020180c541d480e0f09041d8a040c0e190500c08000100701300c650319158040043d107140240d81b2042011000040303070f5039080c5156011107850350300220941d030207000e400c2d07140c0d107503621001c0c1118400d0030141000035950 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 644986528 1250 644985278 644985283
    0x70608071b05060703060807080c060f070c03081204021206060f010f050d020705010507080702030c1b15030406090506090102250203013e04060203030604050606040515090f0913080c 80
    0x2001c00400364000c11013044583e40c1e066020400b200c50000441d04c9441c0d40d00c0701d041e183c04901504035000070040041320222129007008201c580e119404003c0c1d6540e581e203030161142c20401070300d10b211900d00c0500c000d5140544910210104100140c80903051040000d51040f03044103105042c84181d0140c2e0005500440585490005c0c1030b0043d9a03901d100d01d02240282022107242c07021840c0100803070725881c4000180c422440c0760700001e151401d050718001c81c041404001d11640882000c0c0f02e00c55405e0044050b45c0104d01c100c3c000301c0c040000c1c3c034100b0704000000702150365581c4107100382d114113414840030300034000d01000030540d0031019001213030151001d6440444240f507046e4080e0710b1545805006691405050003038440c0e100b006981c5e0500c0d1095200ea40c00607481072002ca100da2a15511590700110008c14072442c050341c400201e007904901c44003951003400085081c000c0d604017403074000220903003140d02145520b020185080e0061ba45c841c0034110100115502e402034a08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 644987778 1250 644986528 644986577
    0xe190510020a0203011103010b0f031906150806090c0d0f14090d0e01030c0f03020d271b050a030b1e0c030a0c08010806060d0309150905030f07060807 66
    0x80d01030046952540006962180801e004038069864480050ba1408461040d40c1c169005a04d07450302d080d5845501440940000e82410924180d01c246021055441d2140c3c00081088000f4a06ca0040d0000e020b450500018405030065056404001d00c80c108442128425000d0f5100090002100c0c450b4100030b2030100b2094038103070016014405024000501c0038602ca00643e52440c00401c440c00440580741600360ba0b0340030900c0c03410500d101c20b01a8000c2c024120804070300052116408203441c488150711800e4009100c1107001c000e040c04101d0501080e1807000ba940c24440790b142201045014810740b00c054030540078000450b03000c110100200e4540714603080e10030920b05025541070300d998415204501000d107020020750482d8000c1000303034102c920310805009250b880200340414002291b0701101005031304a00442c40d14a604141d8903505e9180e554030500a00744806e01d0305e00705030701101d0300c0182c0c4518810481c0c00e9000317001c00d600207414500206660b117030b2105402c0a4a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 644989028 1250 644987778 644987789
    0x151107061d04180b0a09020a05090622020d06060c0537080910020114010b0f0f0d0204150908030a1d100315121a040c08030711100f0e19 60
    0x10440000e000580240000e0303007a5000d1300241d04070b41c564600300380c100c81c0c14020094000700c4d5200c08210500d8010300d2a0340c810406040340d26800011a8410725250403550103001d00e0780e0100e00060000340b05e22807040a4a01414444201e0b1200d4440d02c0d95103085051440c0c8030f02c080d80817070340e4080030b100381907803d094a0369a102020102e0b1801004503009520316a0265044010040280388140540e8080c840301c4941c010a51b401c00b103036426079500180b0442058082003255400d042000c0000301450b565400e1700580740d0741042d4030854406102c81b0003508000e66000c003070000341e0020081f07481c541c000e803d107644071611700441c2000140f8004402c45d88072400c0c800a00089805030400d00e540c0c80210b00d802191621241008103180f2009000b8020035109551900b464540d003000390b0300a402405074040c401e560b6400d951940e84805d10489200c40601c03000c2c195403d02e60301940100496091420243c01080e200a0403e25000c1c3c03490300c205041e004841c54280d036486032001030329 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 644990278 1250 644989028 644989031
    0x4170c030f03040602063301050c0307061b0c05070b0a1202030f0403081006020c01051305120a050706050901080601030c030905010c031d010612020d050f1501151107061d04 76
    0x81c1d070a211540b242c000e071240c400503009010014040040c0454a80403000002c641c905e81140c810449183c0110740c40d1a00d03050000c1044002c0e17240c40d0800c084d000c8648240e001242c042e8210880031a141141d640c21010311900e1010500040d4003c1616000d07902940c02e078030f03251306402c4011140c0018040d50701500a10000601ca417031205460414815402600e40794040e80300c1c0140c1e41002d801c070740309200040e0014240c0c9a5250b1081c0d0052494000304000d145020b51600001313102c0030b03607546841d11aa40203117408010031106104820061080341011070401401c0e00019152000041155040655036641c2c1d042d501c3c0264070501525800c0402000503030b80343d080c040d000340400450b250f080240c0281c482d116101c140200004e56196003c03160b00e1301215070038800e18014201c81200c4900900e0250f52407900d041103082510302030034801d1149949012010880700c200030041404115000c003001601d4140050003408503041840c0403000803540d0340304100b03440740031541d01c1c2c1e105 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 644991528 1250 644990278 644990293
    0x807020c0a090c020f160504200d1e150b03070c05120a170610110708060c0909130b04150213180b0607030921050d0306032604170c03 59
    0x50384a83d00c004403440454080301c0915914018965070b07200113101041c40c10900d00c6092107a41800d4000d00c000700110384501481c0103922000d40701681000e40e84c01240341c1c0d5150540310441070010030420308208240c1c04c0251a0110184000410a5026080c00d406c000400710303180c02d00c1119003182454000c4180e034485090b42c0203c00b0503034080750b074880018003460b425107440c0040001050042c98010400b02c400c1d800da2000352012080c65101035114015920000360740c1c170003070141c9807044004061441d0355190202c01c2000c4040702030440200300d1011800c940014040f160203d41140d0040c0100050b40d800c421808040d104444164800c648400c80004100c0b804484c1450241d00105003803010f080e08100f8884a40150200540092609042001003007100c1c144420300000705210511704a405403201403070f00581080480006c1e66401e000c0040c880390348101458560000c004159580092240402d03d008074013400295148144510135001c10422102d040c2c001d0250513203c05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 644992778 1250 644991528 644991539
    0x1b06020c0a020f040608070e090304120c0e1803092806050909180d030e0a0b04081801020607020312090114071d010516080c07050a151706100807020c0a 67
    0xc4000c0748004900501440550746100d10340b074010300c0c0a60702008010b1141d18a80103180e01d0200c006004a0030f640030070400400c500c060b40d40c0c44080c142c01038120010503450328603d07000c800c0c40280b0300d030101860349000181031040070080314460a0200c6900310180c41e0610080c09940c00365144010902d9152000560250043d0103000200c800f12202c9915a460f004d11071440c881d00940110341c2d0704a03019501080e4002d5009002a101075400c8610b11001550b404001603410344040c0c408440100741130600d000100080c442c0795000707202a1005040c070f244040e50328013411148005040840380001c0030740e4400d42c048921356089140140c2c083c100f00348090a4000d070614003184000c03101da80c501143d4010360171503582211240300c1402800164a074181950071a0120380340c58000d19800140030790790050f0080c00750100d6001c60442d5200110003409080200c1520b0700740003031100822103595182e280300090301d003040c100228107550b0640c08904001b1081d080540c0b111280001046 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 644994028 1250 644992778 644992783
    0x11419093b0c030615060a110115031b1a070206090913033002070312050103080a0f030908040e04080d020a020a11030f060a0e0313080d02060f13031b06020c 69
    0x1200610a020307611151008400d054aa0408075000181780030f40c040c444405040100040400140d1842c003202e03100211a851750035038299042c040070030980d9a2060051003506960301d40244070701081d0300c100714030740403480039402e50400c25040e80f1500441c030a025511110100e880c1c03900d000740000e420b484c0c070b54000c050300b0204140c242d001581440001e209046d010502c0380e4281c800120100d902030040b004207002c0d50045904808002d404a400d046421603800b405020b18450002103840304401031004100b1b020520b818401c0504191052020419107000c6800b628840030300d9151650316030401000d02d205003d01140b409200086611041e540880c001080910414010702c080c0705100806644018010304152641c00c14804a0324407901c6900840c80440c00c54140c1e41006281045014810203d030f0056041d500540c2c22002c4060b414040a503104900700c18a41150501800401064500c858010203100c070300886021245980711146000650025042d591359003405003154 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 644995278 1250 644994028 644994131
    0xc03030a050a060803130509071124150904020d060905070b03090115031a07030e031b0d09030f03050a02070b160b0906092503020306010e01141909 65
    0x309182ca49080422030183c040111b0380800300543c00c1901890030b18003001281003005c0c08035003e004081c0d04408240509020307200390090700c400c0000070480e440c603213100b4600f4010945080058103007aa8440c6584d00554070381c1080d015114582c00052520704031004080d030b0b00015199205100e00040d2003041ca81c001e51045000c44c000380240c0c41d5009440800388501c0c00014144000d01550503c485090304480781c1c0507100e03160220340c0601c01c01c034160071917000000d035032000910030b0342c0e5120026007001692045035652500d80741c6c0619545403400c074640c1c80b02c00142041400585403007610310800840b00038040500c2c84658030800320140c003002c450361341c5048802c4040e043c0043c64851022900b14482d101f024007410388045070710344208802488410180d105600000d010008d40ca041042c1ca01805464441161035414100c9800c1003142c040b40541c0304140700400c20a20704c4880910ae0200e80d1075410110700c51902280300d0326601e0f40b4056500b102d00b04100e50711800728480740b508 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 644996528 1250 644995278 644995291
    0x91204080f07140a120c05060a020109020109050306130206210109090605131707080708070302071a0412060e01090f0c061b0807031b0507091a010f1e03020c03030a05 73
    0x80e42c10a41e036240d05004600d0204020341c1c0640c4483d403c0112400c04605038103607503c03600c1a4070350741c0d855800258094200e4640180140e5460a01d00c1c11960803100810140c0001c030000c0031a4a8607015064804180c200d0003800f844001c80c452101c240d0601c0041504045800c0d95035440da12441104000c00100c002601c180b07081901090260408140b114070b142d820040e09001c401d04c01d981c0120683c440300044030303a81010844240801c0c001c0c4003a0451a20076405441602d107069581b000110ba420016a4a0301040004004007054039032180607540d8858000704160a9841c40780d03005022440b805040345984000d4102044654141c90050707810a803208141c94400d1550300303843c000a1040142003000400c43c62000c00d0203802034009041c0380c2c15040c0c0d00782007207030754580c00d10501e5407200da03520362150301c418540040100c0c9415903000a2a0207003980301c009000801b4502c041000405101100304440201442034046501300844103044943c2c0f0304014100038000c20707089828 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 644997778 1250 644996528 644996533
    0x4080a05190f120e0d0e060c03180a270c170a0f0f021e030c0412050604030210020f07030c080408070f091a010906080a0b10360608091204080f 63
    0x1407100c1c031084c0c40707a10ba8480d0f141c001400070644d01e10003651003d07041841d042d8046070901203c400f550f4200001c2c040880700d40c0080520391511303002d2001d0391503507401a01d41304507180e442204181103800509100040e4580c08148410108401c0c0c03034074001c1c001d80080e4140d0352010401003c0190b0090b8942808645003040300c8803020241e901203000341d5001c407403820540a15403005040e4900996003064004020a140660f40c0070308528480d42e84e030003210190800340800c4181a0107014511201502ea00294601100d03080061190f1140080c01001e01c10700703401c03907001c3c012140182c4019202c048115000a81c84102c81003040b51588202c2c403032a4200f1a080c40c54240e440420404054180c58250220f0b04140054540742c100038040394129a88500e40070996480845845800c6007a803a151031040782c0401e11408225a001654120101105403280f010f0042c1703040411142d10340340030f01c00b03034541240050829040c0d06450601001c041408240c141c00421340d81c6c10348184004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 644999028 1250 644997778 644997797
    0x50303091606020c0402031009320606030117101a1509030a080a050f0a0503012c0106030207050a02030a0506100f080303061e0a0312200604080a05190f 67
    0x181c003400300d919014034070050700481c44204003810950040d54000c1a52134075403801f40c3d10346100c0c208450f01c420b40034812170800308140e0b810001102800c009800c0b5000600310700d1804030b0204045100c107200c1c00e84604c249001a8007120300c140700702d62003103140160a2155043d040c0d903208820f0006084144903000300d0701400b020306254000c03103003501c0000c1c0281207042001d458050726500004040424031208128101c050140b80c0018145850306480e96516135050810605040010006484140d0a43c242602e03a4000a214007811100c117442c2c050b94070a901c0c0b51035820100c3d0754400941500c034102080d03040100c00304015109549507240e42410a82c0c442c042c07003440855114400094200300042130046c1010080a040c00d000c00706030304c03c080381030404206014966441910301c1000d040f280c42002d580316070f441c29680c03940305040b495589a062441d880b5040a4801858014009900e0703080074098000d9424071070425130610300e103d04150016101044010020001440c00031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 645000278 1250 644999028 644999053
    0x150605190207080d0e15070602040e160903020603190e0102030402040b1f0806120d20031e030402180403050304030e01050a0816030f0f0e0c0a08060a0506180405030309 74
    0x14450086a20150040402040c4500103456141105685c03c1c0c108002d20f551021441c001d1005058003481820700684e07540c6440a00780d80a00041c040403c01d103a0000d2154a0075030140c60b403c02c0c1c0b50101d907070a542c0c4e1586800c003ca040c400305000c0d0005410200c101c213041506601451196009490602245e41214100821348412611661140710801e180c2d086151180030f00640c8020040c0020280c13481317007550719140010340501c01300007907803840c3d984044244074840010340c801040015030a020342084a101c0790036410745007a10004000c00098203550f111803e52070840c41002540d092801c06007401011a130089034280c6c086026003540006031b506c00d004030341102006035502229603c40e40c0c0460313100c80904014400300754660040d03030a911414828079441581030364000030310003a9100098141074031000034612500031044100040040442e1456202000c5803002034541d80702400141503441054800c840e0b144150200020418008001d41c000c000384000c40e4030460601 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 645001528 1250 645000278 645000283
    0xa0e011d0c1309021e0d0b0a0c020706140d0f09020409030908070e04150e0c0301021306080124081e0103030903110405060604061409100f090b0c0d0509041506051902 73
    0xc3c040250058140d250703100c001c15141e10b0101c2155002800b510319000c0d55164074021640582d8506c0d07200741c1d605107260007a40c04100180c0100b1035030400034402d4084103c510000d000b4156101243d0303880744036980c036581455100280059006000f0442d02c2001d08004000b82d8007030081c5003a034400c00c0c00100c3c0070105804c58070707c0b0b50b82c480e11100010019000390400783c900040078078070a220b0341d600845503036400c0c009401211081b0300c41c3d500d41c41c07030f00100500c01b19042c0d004104c2c003280701c9003c100d06001034000c03202580d91814155015243c2d21901c486005014502c1c01c14800c43c8000030040507409241681101e00590f2801503104a040c02c01c8200d6100307550443d84942c7c100300030410103000340b140d6034407031243c0b40c0d48a0078105a82e0106540448090821000646445040752003542082c00f85000c0e00c00030741c0b41801e2421030301c2019580d10071144200c040c4500800c8841807541c076504800100d0500e0a040c9a27601c0d501d33800945650404503000e44562003070712a042c0b000b80700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 645002778 1250 645001528 645001541
    0x30b07020606030c062505011a0402090a12020109120614070e01021c0c0b01032d03081f1d041e030203040b070c0f0b030906130b0a0e011d0c13 63
    0xd0140040c1a408001c103d0580d00002506c2c0a544990f801100081198641000301c13900a50000c500c164188440c00341220b104d000e6148501d2060100800751f840b14800c10083c0c5125000c0300e02410154001641c164801d9440002011080d4400c0003c21016400a040240710003602c690540c03928030007034907081940302d20140180d10001c0c061245060909c0c5a030b505102c14100801d1001e0161164040170340240c000780c6455507400d15105c03280d05840c51009480900b1030014151000d640e0b001459581c0140c620803100e51450b50319821890307400c481c0030041c000980c6281207044050f03a0241120000c540c155580d03036010201c0c02d0f06a4801641684480c0d042c1d000e5031406040c00300f104d407660070074002501e000c0b4942d600424183c80200c10305025040e0134a202e902c80c68401480c1e40340000040c001c05100d01e0181080380051030100c1c6182e00528506070105014403801031242c01428001e19082c6410051601a20f10000115640c034005200341d41002c00d80811400240680d00b8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 645004028 1250 645002778 645002791
    0x91302010e010f1d0604090212090d0c0215180a1211030607120e07150216080318060313020a26010209061c140406050105040c2c12030c07030b070206 66
    0x72a031560513007a00101c550000e0340803000300041d00f05a25652a00101d030080903c132211221844180030740c451040003034150ba801c85140404000c0c440c2d40c0460814209694015503100000c40c140104000c0250148003596010700090300301a0340700040302801d03407280d20540b950300c00440060040d041c0812050f11030343c601d03103400001c0d030b080c05050001402e400201040c0c50241c0c00001c0b403194264031640c4d85141e0268000d00305000085502401614154042e0346030b58001c120910b048006a03000400454088418584981c2c03407815010300a00340038dc0082d40141207400c0401c6d40218121542c0c0004007640c01003402d08c800c202680c0c200d1050700a0640c0c02903082c00154094586100038a034100c003406d2001c11491104441c020311010183c0d8100e401c5030701e43e001808039041c103118641d00d456051a081c0d280e140b039141128000c0d0075071174000c26043c000242d03a618030f440d0780d50103c0e41008910304483d5034460708402547c42d0703101800100e4182d001c15000c034403242d1001034103902600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 645005278 1250 645004028 645004037
    0x3040209090624060906030a14010f060c110f1207060318050a110d05060a0b01031406090601080c160f0209072d09080607090f080a0312090809091302010e010f 70
    0x2800c1c00b0700c50f0800c0e022403641e29401141000740c0c0075a916000061409081d040e440440d0b0403009080c1a4540441602318204980c1c4a81082080541c4608200c04081c2c001d01500c41010103400031a00360700c103401125410140501e5503d00190000800c0c00840700c7c02e075020866095522000b40c40c1d403800031405440360340030a4806011903901c4a4900b01d00400070b0440181591658134036090031030441e6051030550341e84010a400d540c060044c540c480c0c0c03101c148031202d898200009101280091700450402036002e0010b0700c00f481c003000311016806070301e200703101d004e84926010a80d9220904101d02803c611000305480ca4040c2090710840e0b40e14030410303611007491005e114044680c4503005c000b040400700b000500c070403081c0302d4140103040c0f9546002c8c19909010281d0000da070b00d03a00c41500780e4491090f00011940c0991500302c800b50070080820f8221050400b000180118501c0a902c20007040601c807541d481c210803585080d03c00c0e00e40c6d800e0f04040c0701c0103482c01240f503000b607404076 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 645006528 1250 645005278 645005311
    0xf0c010c0209010e061c0b04021009061b11041113050904080318010209041d010509030a09051309081b010e070e0a0f1416141305100e15030402090906 66
    0x7130b2411200c85500c941e01401048090318040c111881c070f4004841c0135202880a0000d02c8103609108600000d901c3c2d5a08206450b5850468024007100c209580c07003000424121145040020341c440c3d00c5d040010083c4144404080302c0c484003201d90058050310030990956800140d00d04001d080d240c461604001503904550315141d03041c0c00b075210b90034103003019542044660000d035580d00c030300b510a500b01e044941c0391a10040350035085a0024061940c9035000307010700a1081d07448200c410036103100b13550110305040c5240d1508090640c2c2d180091095401146c03000ca910254501d032048001040001c0c8001d002444050303484510031f0040c4401541804000307407620600f504880c4625035103001c00241d6009500d034200a18030252802c1100a00c01070114000a9214400001e65400c0c13451081c03400010400003500c0e41141d05c20340740904c0341c60113810b5245000e28441402254060880d541c94004000d010807284c2c01158100c2c41542e9203804690b00c1e00002450303d00c0352042d044809400c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 645007778 1250 645006528 645006539
    0x6080f0d02150a0e06010f0e180c01050d020d02040b03070f0f09090e030c01050f090f011505010c050f0307060c03060603090b06091914011a03100306020f07140f0c010c020901 77
    0x240000400c01d000d0b25454032142401344070100301d014000c01e000041d02034400d003840007400f1084801b5202001c0c20003004500107081201080b988061642403c04541d50103110010700064001c07090021070161020074009501c1c22158011841007080365929040b400d241c11041e21654a2103c0c0300e000103036160700a00c11050154808a11b8049a40c00ca85c1469030b25a25182903400071280d410141c043d200902c03d080804100031405034800400905c06042d0380d45403496402c020303100381410018202a8842403003000d00140660000345402daa1b80c0d00d2040c140640581040840310001a14010b80010320f84d11a11482031020380c0200098041d0300c503007003001722022016183c07400040e6031000390b007178160003440f440c81c2851100c03031203450b550b14062581414000c6503010515a0100b08200140038200c1c2c50a402a243d01030390068540b50078062514983c05a0704006201501101120100da80002006d40c44902a401240c1101d21000d004545920000d1002504010114014840c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 645009028 1250 645007778 645007813
    0xa1d07030213050d0c090e010c0e090612120a08100605030a090503131212080c0a030906060e0c03100906050f0f04020f0f0d060504020f0a0c0f1506080f0d02 69
    0x1030107000c4506110b203652590000381e603080c0e5404040302d90518a0380c041040e00030034000c0f03d02c603004042c000c11001c0c3c408800504015031464103180300d1200000041c200ba6184440000900110402c54005900a100d84c07405d607803046d81003e01003070115000a41c10b0f480290102c09562055079402d04603110040b0f0a006452040d80499450100b0700100c036040400c000128010300e602100c02e161100b0038201070006031583c903040713010040c0400822030403144540c01c8800c900c0c1c0c11f180c000b0b03c244180c2400401015550001c440300f0484c0e80a220b0343d46090406135016900360b821803000c85958500010440351288111600100000c00b60310403071a00d840310907030700240a071002d4682144401c000d0084c1e80950800024804046124080070040c1d200740d00182105642c110b18001c0d050203015514091035403840f0410411140c104100421081c20b601e44a90000d480c1d8410000c00e46640082c0c040350040c02410f1040c0c00c20180450000100d111801c421034002d000032004d80600c942 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 645010278 1250 645009028 645009037
    0x60703142a0c1f051e0409050a0209010206090105160320210a0908030105041d06040503040527010b1605070905061810230616020a1d070302 62
    0x400081c2071507401103032086041031040c081255034015000401c1114200440e00128000502100010740102e03144540c00c01c040700c219504610301803007840304286070700c2c665100e81c1e04074000740c40c00d050a011101c559500900f2070301c1001d03000e0780d6482c0d0303d0f08102800c80e102120215000300380b030012089818040d901c000b040460307609004000d4100c01060580540c0710340350007510406089035981122002220b03881d040400003034140940d00080d100c0f0b2203d40018052a40300740e0b51340003240d200070515000314900000c48c130141c51403407620341071183e16500715109580c0108510a000311280e210078981060440c844200d01442e82d0829a401d0060380003241c0d04244040075079100f10200e0400c0010600070301502002190924280c800d00200c28400760300c0c02d00300b10608003408014094400600c1c1598074440800090001165003032960144051070942c00c90b83c009018078035041da171401340070b00324025501003003041c0d0340c0d8040c1e0001c2980e032011000c01ca040f070780100303480718403136001031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 645011528 1250 645010278 645010297
    0x171306050604060f0f03051c0c080f091008010503010b0604081c0908150a060f061e050f070c05030609030306010813050307020a090c03050c1e1b0a08041406070314 72
    0x7800d94031101d100050000755000842c1505c00c40c00100b04024040003903001482600040301500088540041c10500b81503500a03d2a0030100d080651901c9031401d44010201c02481040d9202c1e1a080150000321700f801200d0003542440800343d100e08004c403c0b40c040310301c110001c01e82100905080c03410198445040d40402044540020304080708005141310304c49203c4082c15981480301d00507046601d40da010300d850302941c107010402c90390000135441004c81e0b03c5000000300074020504a90a104840d024101400089528024406201041070595109600305c515540316041010340d28001111100d0008d200d190004c0d00c00c105544c2d03000b8500b4841c1003100d040110b25400925502c101c1d8219091942c0c3e140821301d103030780c0c0c5405119004031400381c426243c148a89021806115071b421040401d1600180c40c021620161246210450204068a44401303080c074000159622034810312010303000c100b404028a14011003201d01c0c4541c1501c0d01810346d008114907a06641011200c0e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 645012778 1250 645011528 645011531
    0x30b030c090411060c0d1106010315020a0311030903070c080309090c1e0d0225030503070332010608070810030f14010903200a1115070609060c171306050604 69
    0x7005960b8130380a014002071810400540705e580403006000300740f89602038424820758800d000410200c0c10800105510b203204580c05644d9041c500341c2a006000c0b0756a20800c926400000c22800c00c40c084068142244121149505141c1d21240d1030b0707881c014081b5040d40001c03814045920404100000c19062803610304001e04003450405051185d0445089038500c0380d0000b910581c10100c4001c521350b0003400c20703441c212842c04c54800918902004000d07070180341da2403040c903002414404c41c07000e0f102400e500c20b141054592840c41d000c007500b032203000d02140303090b03000c40d003080c0c000c02c0c03a60303c15a203100810748054559250310f4610b2980d45000c0e103890b07201c0c41c2c10f030364880000c0c001c220680b03001f0348614410940381d0212030440301a00c403207802c00c2d4102405082c0003910300c00140c03540e0041150500700c1d481070070507c424248164a0020b00440c0380001148c2080600d0b0006050542c1c01c0c0c5403003200c901340402862902000b00d546e070382d030745815640050020700603a00c281c2c0c2001d400b800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 645014028 1250 645012778 645012803
    0x50d02030f10020706141b0d060f0b0d0c020703050c04110f070b0411040e07151106091605060712080403090b071a090a023d030207030f030b030c0904 66
    0x640c50b091000e180400d00c42541c00203004014806031307015283c01c456820005103884e280260198601c0c0b201041e0700b40d02c1060001c5c4803003900c2140d4101c1805441e040c40040403481c0c1d41c108284680d80429412610542040c1d508a5218000315007082200d406c0f001034611042c1d508100402040300c0b110143c200f60050140b400c00050460103042c010303210b8040d81a5a0815040422048010780b1045114604002d031a2001810202c0c509045500f200b0f048840e059815000f03031651240101515854420b007003c01061040c0080d406c0707203140c200d5000c190015121414400d15104081016081800c020748400e1810b12558030782d0382c01800381c9480b45501e5140d10381180c203a40404000e5942242401404044104641c08107401c6074600300108a810700523400702d60040052142031070b098808002c079080006071400c0c200400d0001100d021140441d030301c0090000d41002d202070380000e4481942c1b606403806071041d061814001001403640d00440d40070010101c00090040341c50011034172 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 645015278 1250 645014028 645014053
    0x10020c070b0307020d1e1209061404120306152f030a0c0201030b06030405070b070302010e010630051902031005010b0702130504031205071b0b010603140f01050d0203 73
    0x20003440c003440c0f080d4094241c0c2c002d90b0000400c482404403103032000e8000b4aa85114498004864112403041442c0c00700d100b945905108000308444006c0c41680c0030038004000c00c1054000b141e494456664801b0014140c5550382c90740562004500b6a02151411030a100c90028010300c5000c40407140040c2070184054900c2c240c02c42e008821500c0101d03a90342d41d140119a0107001d96520400256041e50562909468182c0d0ba00d2403845141595000013071000d050620039040340200c242c0705402403040c80c1d5500300e003030391040803018000d2402c0c4102126a1685801403c0b028015402c400107145482d1302d1080a22080705000342281d052141401441034075000e405040d000344401c04000782c9894541c01440381c0080103c60802116107410308100c0003a4000000c05c1907541100d00010321a1740d14942604ca0303903150742d942c9040b000020f084100b0005103c0e8444d05a404a590034030442d20250b5064056100903a03880713952000f12401402641030600381c41841c9800281162240c40904 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 645016528 1250 645015278 645015299
    0x2030412021e21010b010305061c021318020a080c030c09130609080306030f0d140a05040504140105040e010b03120f040314250602030304020f0406090c1218020310020c07 75
    0x11035140e00d4800c40c40c0c41001c01001c0c28800e45c442000300b800d0500440c9400800950464801c500180321240f00e01c8401c8203540b52003038009881c1c84080e03420840703071040000c40c500f90511100300300c0c850100d0300c0007c150323944086100c0c1003604000e001850140c50000801548480c018042c0042060788003103000410014020000d0041c06513050741d40d40e04040041c98140301d01d4101d01c03002070748004035000d80c3c1540070744006100080140701603151100d04130200c4040c8540d03442a40d0180c03e15200c0c40344c41000c9a281412507604442c100075260103101c48609841494400e15410703004404018820b04039000181819108007122030310340341d2265581d0468020344800c2c4031244d40414a0048107541c00d00300d002d00400d0744450b21100b03a00e0711000954902c80240000d0141c6880c0b541c0030a81e84954015402600c003030082841020f45c0030070014045024903c02c21003290808114074000d506036547c0321015a00580500b0380d1543c1a807600c3d01072350040c40700b0721b9544184100003503148041c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 645017778 1250 645016528 645016549
    0x902070b151212030603190b0705131a0c011a1507150c18090207080405061605010f0213140d0b1e011706070f0f0c02150f030f0702030412021e 63
    0x102503c0907100d04110b01811301d8086582d0440310102e024017540c6000c544006c0d410350f44074141e4502203907626007400030758040358010b80c00400c21a83c580c90268820141c1c030050007c40c00b004000300700301039800042c580c1840d2174042c426004510184000c0c3c40c181c030342000f8207100d8054888030340d100b258614140100d5130b82050a000040e001d00c900380300310340029189401440c00000c1541001c8041c0c4440c54240305030700c5490302c101d200007a50542d00d450400182c41d12074102c0003c00c00524907400f200044e6000340c510100602c84943c000c00c20344102c1b4010004504050a600126210759a9080c45490040c11540c4054008cc07110000e5120f11180359010f003010401c0c0c114110891b94409145c40e202070310076030034070140109410780e49602441407d11082649458420100203001180e40102d004c0c0c5070081e00b40d8001100c84d66091030300300850040c400300030105810740c0e400104989901a078050343d401c80d403404a05c88007600d0161556005060f8446002c1038408205001420f11101c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 645019028 1250 645017778 645017803
    0x2100b0609010c0201170a15090509030928061d0303120103121e0e0f091b09040906061202100c030c0809060c0d0807020f07030b01050607060b0603070314010902070b1512 75
    0x4a800400780ea41c9140c10342315004054032070052000c0e0800303804594982c00392640c0300e40541141c80800c0100c40202403c2501c01c03240b07e010b5254180c6901005040d03034501110446030064016181c0d94a0a00008a84122180e03c10051480c0d0855a074410903104108003041000f926043c042c001d080300c0405400340c042c8544130703c0035951415050001815aa02c00244115040340401001280600d051003400400a40e070380e42c0c800034100010001d000948004d040203280c0440401c03c01d040c40104110b8500840d103c00044250600848495a442c8001070006218200f50b8000071100e0010301540b5800078541402c005418400c9440d0810300854080044c0d0218148400281c0600681848080c1940076281603030860302c2d04004010184240d5025403400140c0d0418041154006107101c000104240d6490034940d1009010300781d00c005040d00a800380000040a4000703108517070b03010303500491180d000e5681132415104400340c6440d030f9030002c00034a41191074510038480d4064800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 645020278 1250 645019028 645019031
    0x15030105010206180a0f05100e15060a030305040e06040f051513020903030f0f131d070503070c0303151e1e06080414072402100b0609010c0201170a 65
    0x18942000203280103006459292441001d000c1e4540e480e0740840d444d050140c00c940c0515120740d1b41d2911a04d40144074083c0c00429292004d16110b0000c04681e101e21003d55002c0e60099498000811103a0766051000501080342040b04225500b000901140e00801c02000052050242c20035070044d150101e0f0314203910039010703041d0811440c203c61380c00d8a070440c10303408604090200020035500d218a60358600c01c03030404102e41006035a00700843ea090780540d15049a407641d01c440c00c0d40807480000d00104188240c0f80000c4e44a4425415a84107aa4991710340902c0046500c096000f02081244403400385110a404030b1082140c039590035008080c4201e9503e41740ca0030b0650341c6075011507003410b2680a80c4a004100c07081e8041c40d0381d6000741d00441a503d19100d000ca0f0149040f0095100700040c0d4004007001d40c00d1210443c2da44020400758080d9801c0201000350b1074115030b82a030440780e0101080c80300b403210303503c01e0121030f0007a881810320210b502c286c000d00307481101c800c80e1000100c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 645021528 1250 645020278 645020281
    0xa05070f060201180c090f02161118040f021005070b1005010e0a03020a030204020c03040f0602100b0f09010603110f030405070f1a161a04061a0d050604060c0507021503 74
    0x41d982440f40041c42040c074104202083d04030f039601003d0000303511034007a81940326070255481500e1503044400c1c840c1710702800440d00c6c1d22882e11581c40610706c04443d210f41000381059010880c3c2c07201e260704c40c0780d004840c0b09504d05240e0810000545d2162600c04106003886014001502c015400b4010260504058406445d1a00050201e01902050760013282541c50030801601e403c0303460001e90782d0440340076071140108480c491a5006a0344015418020101c0028410b6004145001500840d100601c101800b9106100845ca0164100786c0c009001100401007244683d12039901140e07030300000f520b00a140e41e03d20859810030b0342c00b40c5041d00000e038204041c1a4600c2c23080d00814000300c206601d04180b150207462030150003c1528400b40c09500c1c5000c00852100b07240c1c04006043c0c0400281c00d240c2000d10080400d990091200b1495250040b41e518180991203130203035201c4001c04c0b130b40d0b0791560740381c0180c0030009160307044c030a0501580c0c0050381c408801042086200c06800d031603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 645022778 1250 645021528 645021539
    0x210f040c050d1a1b071101031505030a0f05012019030b010516080403080a03051b18011d0a061110111206010909110a090e0f010e0403020a05070f 64
    0x301550340c0d0005200d910900c10101c00100c0540780180541040c1807050310b00e90f212220881d00310300c0403442160100e00012100200300c040e903d5850300b000d0a9904000c1c2840700000d00840031030500a40c0d0303150340711410060000700f44000143e105840341001080600c2c11400a8543d6812704d00c00f01c80e2361b4804142c040c05090301c1e075403101c01c0502d18a400c0c00070448850019146200d1042d0714900082214000c030140075414080f00e004507400b844082d07a82911190080080c40103444c11650113520900441c0c040641c04242c40a1201c011103101d0803c0b24640150381092140b00000950000c100d40350f00c0c03030350302c0d10340c00c8000f031415403500c00c2442c1c1c0c2d11003018205650340e0140c020301803814659540040c240f80940700c0419400510700d41544803840141c40e02c0c0d400d40d0280c4181750801c280307001a1803515025129105040c1c4500486548038001c4401c4821301302c070361110b041d80040040200322106803995030020b003c0c0c01502c2d450403c40d22075900708003207900403c1c00300f00c40d16000c010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 645024028 1250 645022778 645022793
    0x17130305060a181502070533090c010e0f030d170901051902070602190210060f050f04050c07060504030e010e060306010c031206050d050120041a210f04 67
    0x520901e000400c00c11801415410f080c0718402c0007019002408000d240c038244a03083d41120076060f00310b01260324110800031400c0d203142c14820f010f00204143c100300c40c0014071000240b0b00445103000a0084100c1100044070080c0c1c4990710287e00110454481e81c41d910188500500030606554012440c0c0c034042081540a0010f003480040c1d0385043c2c10040d072501c058581403900c02001174096034500d65828954043d000c1c2d07272464070501e1080c54944081540019070204160340002040c0308030383e41c44001e03a00160661190a82007000060150001d00d820341c4815440342003101c1131820040749448060445d9421030701280410f641c06d04580c201c0da00422030741c031040b504442d458610300c0c2503400280301c038440d0a07004043c0300f594041c11802e50099005000a81405041c44a940480d81003403400b0300160301400881c00c8032400585040e00d90703079088a05a448403006601440035401d02108076900c009002c460138200f00d101c1b600303c4000045494051210010744000900305400d1100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 645025278 1250 645024028 645024031
    0x31509090303051e0403140d05070e0310021c1808040f081e1911032d061b0d18080c0d1805040b13060e09070909020f0d1713030506 58
    0x400d00f4031310342180000c8a40c4004490303440750b4945071580030020380350000311050007900c0d011341283e8205010400315075070003000c044800200b1800c0f50225590405140102d05c16a031070034001e007920403440741028225420880170085000740f2a10135070559103030708e10540c100b034000d00d4540412040030046800704000700c0d805007017506942915450800415a030307070480203205858080c0300d1703000c1800340418446106041c0d600075094540e0103d0300300c00d4511103e0b00000d89690b440b141641d1003841a40012a04e20800340413040c090440c0e4144100d02e41a04100a03072800036841c0c248440d00c90000142100c072080c072641040f40c5480e009500103051030014081d0008200d8082002c1c942c0000b54001c030000c0f181e0555000036114140e101042085110212050078281000390004102d160481801c1c4202d0780e01080d14965a29092442c094847d003040280d403001c0826000e080030b14140041c05007443c81600c0c00340b60613a150201d4165504101402e485855100404009000040c80a13a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 645026528 1250 645025278 645025291
    0xf0c0e120a2f0307150c11060a12061703121b0a1205060315160e030a0c03050d080702150c1b0f0709020705031806130905070f030c090b0a03150909030305 68
    0x303000c0e417404c0c25044155200e0702d0300054201301c1451554070034000143c0300051101c4002e024960381d166103c0d40a824680c0c08400301130300170b01d00240003800c2d01d0b17056207500381500d410303002d50f1400300c5900d4410354807500500340480c2000420402d41540011200400c01e01156840d0082d1400c00d400320708007219801031210303000750003468007540013002520388198440e0300010010035580c000001201c60142d050744650705880b500c5510024000314030340780d2040b02d2003002115102c21720300b001250890b070243c50a40150f84034a00d4151140c000b4207206038440c0c03610000c01e007401150551442e00755240c1402e00b0b0385411420100c03200420a000e40005845a24003d5140c0034143c1d5541750f43e40324802c20804003103d104113003180c590741c40044034440c0b40c0c0d04030501c01c00c03038540c1071607002000c05407548400b2590a00480801038040e010750111620561181032440c0e14000c14907200b0f038007541d02601007540c0c0d01c02601c09509106c501c000070702914040050140101d00d405001c884001c0c201 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 645027778 1250 645026528 645026533
    0xc0b210403090320030d03020d0603150501050306070f020307030c02010c02090a050115180506090301090b01090218043c1103060301061202100c0f0b040b04060f0c0e120a2f03 77
    0xe01d00603140043c05017008041887e00690707845c080c040240040c0001d803c010700e100b811007140b04040072a40c1100f07069983c210151051030b100e00d00d065a20f4580e14100d140960424052180441d00504038010400c0c01810070f424a03840550008041e038000300e0f8050f030100c0d0341c1e000600101d10104040c2c0d44d66070765400e102c4400743c08164603040205051181728811440002e6072401c0e52429001800030340d42c0301000304403035611447c0400180d0811411102d074414410200c558500d003d008035a904c12028800050740c41101400480000710b0103005808140b0588110100d620f03140b1030180b2003694064004d44904024081609562171a032140e05c0b2207040c403a200c000b5903640b0f00d1b5a81700001c05c2c18190b20195591600404840702601c0107005007011408000c14800802d5030301e03116a214010400104d000a90544112018104c4440000d08505110050742c1060503416108100311002c0f1015105950303a03181814a44801d0b20908003c2c1030b040008c22549241c9006101c00c0c00c030003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 645029028 1250 645027778 645027833
    0x30614040c08160e090115060207030605070e090f0a0b060a02070501030e03040302150c0f0703031d010c050726060a0c1e05030601031a0910060e0d0c0b2104030903 72
    0x510103016034501400e41d00d0114000450030601c407d5104240500e0001040314045075680c3d0080d446a40c81d100548042e820040080e44580c8100205110a00014140320081d140d00c150440e190300c008002e90403091340e5088045c111b650380409011814400c0d030052600741d041000040a80e44510038042140d4010302003400140c0c2d03824100c0420104480e2115182c2c0b500b01070161030000440c20514180c0600400841810fa0100d40c0c500d001c6000c2c0e40f4a100c038102d01d00115451080c3d040058096081760105100146103828034111400d140c03038194001c054000d130b1582c141403040c0ea45405856030b8109403640e040d04510071050a034100d0980082d100300800014005110081c011810150307200c140d584807038803114000703a003001d01812011940c9003844031075080b4045402140b0100b0107800301190fa519000c82c10244095000b03006100d450b142800918484e08034180e9030a12404081104d06582103a0325520700c15406a40c40000c12465803e01c003d03949500021341540c2403a000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 645030278 1250 645029028 645029053
    0x70b04080111030c0d050702160f09050c0703020705040e01022a0601050303070305040e1008010203070e0405090106050303120a02070512090f0402091c02030319200a030f0315030614040c08 83
    0x203050751100045c242c4003007950b994460080741480d00c07484401090102c100c40206015180c803124209945001c0c13410131070b580ba501d81060307450088103070041c01603001100900660078160846529501d15200150038030580785288100303496400e200e10b0f10040700700c00c00c1001002c00c00c002801000150b014500d05140d41c1c90042c414030560007103080300405400803034407901032241154001c000c800c0c021500ca0a045c50020486941c1e101c0c0a8031071810300340400c031910410300ca80021030f04010001c510b072940074020072245c1e1400401c5c4d407851503400c1c04804041507051001c50a050200718025039140e52000c20000c1c0d094005011074042c5205100ea26526203034260341040c0381400244600e4051840d10009240d40714050055039806244070016000c1e580089001d409074a80b19050480d5100c0030790541d99401c40741d0400307000102c011010b40d900c0da0180d80b001134500c0720038500d002c030291680c84102c2075070620304107036802141503020401440a205a4203010f000e00002902001c200311 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 645031528 1250 645030278 645030301
    0xf0b0c120103110a09020d09140610090e031b0f0d031109060702040b2107170d0516061b031b02250801140117151b0c070b0408011103 59
    0x140001000f2152030061028a543d42c004801d0080c13610744015559810080380200c00703003d601c9000c91383d00d40003410841c103201010445910134003900070b49094607440e04200310041d221645408440d40020402c48540b0030441062603c0c80003020000e00c41c900c4088031280c40c0c0402031006c0c000b054a001c0c0d000c02002c001c0d10071030b4002d0b4402c9504544070f8107240005001460707070b245625800f031040c940000e41841d80045481c0403940344401d6500e444c0c0d0702d1010450441a060111040c0d40100d10803031070143c00f4101505004440005540c228038031a80c0e0001140d01d002040054100000703114915164036008042c620462a03c00704007020707036014084c0d030700d280e940d103e44115401d207a0000c80a03000100c0180003440d890000707101e100300c4004039000c202001c0c0103078004504100d141007204940015251165480c2e84480b8400740c0e96812840d910281c080d0124100020801c001c0900e90010001a0b01504492000030b649600c0c2644442c21160518a140130880c0c050042207042d9052 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 645032778 1250 645031528 645031531
    0xe090a0c0314010b040f050115030522030212040b31090b010302090901090c021612020f06280f020708030315031e0a02030105060d0f0215040b070f0b0c12 68
    0x20140e0a0080e9001c440c2983c0907064004c902904945004c610902e0703c1c0ba1504164100c440e0740c2c2d0b0201950340301010440655804440c88124140755040301007140c02e0b015a0380c16018000e2058405e00b00010803001b804c2c0e031040e480101c441d40e01113a00b00509400082d0302203400d0320442448454201c0742c6210040083c0c2c0e10170880000c1e030722280d100059009404aa040d21002443c0703030250340e1900c0d03032000149000745800005104e40c501d000e00d031101003072546090315842d600c1030b42109855400c0100e009414002103400c02c000b402070950302102d90484041e03100e107940e0f0b0b0482c1503400e44001031054005000b544115403164200f082101004411280c0000f0001e29201d03401c050300003ca0309d0007003540c140b06844000440405030a2102140b0410400d101720020701158540c40c00300811200e0503000035046140084070800145001c1700c00c41507200c0801261401d1960700c41c9241000d41080b64151380c20709407034140d00b0801c152003a40c1c03584100348419880c141448000f42e000038040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 645034028 1250 645032778 645032783
    0x6120308160201150308070b0109020319020304020411070b041403033108040b03041b0b040608060109030209150117100302120307060504060209030c030f030a0509150c070e090a0c03 80
    0x3031030030011021900c02e4001a1813040084000d5100640da45032083c1690700212050320603140d81000416031034090b000301c074024602d01c07134145501485031400d40020740c80600100c0c1e01c903682e055001c0a04400c9005000514052641c00c1c050b803030241485d107001c04000c00d2b0700840d40c00c2001008412247c07420040c4c10480944c0d01a0701d42e0098070054500384034503080c0900079850102c1e0006508003040f00840c49144104250140f09003008400303004031300c15000f452407040d0240028404103100300681680f050051601c5109269260041181c00c002030f62400240e107010b9840310741650704280c141d03e2007409a40c610100d40381c00e191196000082d0f01000b44154819415070010840170800da42802e50000403c00490030240f81c41c03002035000742c501c240a409070306242c661616002c5a12106240c0c40c40c0507520301412500101d0b0258810f802c450741c014507100400400e024204090204140c1a03002000c0c590b0400c1d410403400c401c011315880c420784c0b00d600c00400286201c8440f000b10303607 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 645035278 1250 645034028 645034051
    0x9140c041205070504050a0615050405010206010302100309061104050f1801030f050a20150a200708030c01020901032702012307030f090803160b13050a060501050406120308 76
    0xc661801608040b0580e202da60701c242414140700080c42180d214504803107270020f44003d0034000d882c0c1901d00703009030b10a250140e0043c000420150820102c0d6030142c4010385000540d0030a965104030459003500220a8409000b003020b00003402c200402e8011203070102d441c542200114450b420b8a0b4505004c000c0034440210200b208000007001038015072640514180180307030030b400100c0c001e08103440f9005c0c031070f00425440c08050640207085500c01c1c0510b90b01d0b458805581000580c480c00c4214051410703100b114000030700782d0424809800c41c445032100140e52400d04500050688080d0030103000c1e61100c00c0f4450940c0b2180320b0300d0b6800d243c0e0a0804803905d410300b00004416181c0300c1c05103024454006414010150300c04e0390314021001039115907085c1621102055a02d01698244071348000c0b8144112011800220070141e0025416441113646442540d64900301060150304031a45a1584d0061015242c1402008094101d10750014001080c0f070b240249100005040030b503010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 645036528 1250 645035278 645035309
    0x5060c0a061d030a020105090d11211e0711040501150804060605040c0206060a080303090a02011b08160c050402030c070b0702010b030f0d1107060e09150d08030109140c04 75
    0x510341d02c10200c120144800c10380c1c0d00c80803d41000b901804040301c40d00514082c15511501c80c40c019000c0071354008420f0020a51542c503003080c03064420b40800e10440f40c0100340110260074554009080c05c4c1d0304005a003a45403040d91403c13407081e1100300c804500c164140001400034090401018a102e40240381c1240140c0b520300b00702009100541001d43c104c0e04201c00442e80c96000116603000342d60664141d480e03c4d60700e0155540340d0006a803644081c0d0408100540958410703000e60b4030070200088604401d81c07071a0740380035180d888040e0200f90404001d201c8410300000c008400300404d01600c003540795280c0191003001c41d21483c0c00040030300f45818003050711380d4802d601400035607174080c00301d6041024200380d995855212002d43c40005030301c15011401000085203000071900301e03460f5100b1421114080004040009044000062041140190964441140b0102180070301ea0342660781d4100142042920b00714400c06841d40c2c806028408541d038024115412580040c1c1d01c550740 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 645037778 1250 645036528 645036551
    0x605030307031b0f0203060703021c0b011b0317150a060f080c03224e14130f060c0201170a060302031204080705031f050a0f0c0c0c05060c0a06 63
    0x241c0e00c90b00c0313019401d48074400400203600c0c0c05038020b02242c407020241c00b41000400c03090500340c1e003c214206000850118541440c20010440700300054030906001c07421848106410011007000c035160362094442c00d1310500a401d10599600142c4024a8032482c0c110702c0c4000601042405003001107802070000000d0342144003442c2e000c100e4200c03a04418600c030042e00b0110304841c1c908242070f1a80c800d00c0e1440d20400014034013a2403802d0304400c0044013030503001d4541c4100004020b004184004030314015410b45280c0c00608860600c10701030b0a01504041c2200d0034482d05030060018008440003141c02f503a001841c9181842000c030078550b0b15039074644107101816860340000e41501c1000d034440d812a0f0120b000e032080c0c0b013860342150700c050b85d13032000c041d0344109580c596085a008030014800301c10381900044c0c2d02184808001c184519600341da402103c076004060000981488140010040300000344c0000701003c85100d41400b81404405442e82440c0c6001403080d503455090a10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 645039028 1250 645037778 645037793
    0x110d15170d0f0503180109030c030e04330f0b070c0603020901020c12191109060a060c06050703090b010603050901050105040c0f1809060b0c0f03030f1501110706120605030307031b 79
    0x1440c01c001f800040020f04d005409024003481c1140852421504001181460b11440450066040ba07850104130f084e020164034003900080d401c1550a240d402003089018842c2040c001d205804100b5940e1545040044050005401103401c050041080720070036a030011303120000d640c0448034204205043c510541c501452100c01d00394205074460640184008000c041140708010b40311403102e955602d080200c001507038040c071004030341020884000710740340c1d500031580b028a074280040c03241e6464641c0c25042c0d4090b07220000190b214000c00c15540e90a024480c01803a040d20144010389055001170106010b0100030030401c02c0b81225544040c810208030700003810321500801005031668509109c540c032000190711544030382c41218899802c00402c4038401d40482100307041e00e40711943c4000c8131040d07004040c0e0411038405114014030b80c05001c075400070102500c90000f044103942a20060b28001d0384818440d4100744940400309801510f01030708000f295204a0403031406180108 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 645040278 1250 645039028 645039061
    0x12060d17030915160210050c0304170721030e06091f0b150910090b04050405060f040e0607020d020c0a06030209010c0507060c0b1f0603110d15170d0f0503 68
    0x40400c0c2d000c806100100400748070402d08503095900f43c94541212034055010383e6410340d510501043c8c20000203001c035020410081c0f2180182102030720b0040c2e95220f00d940501c03480700400c81284040c21840322a038040c401c25600b09150f20241005240403a0316580700c0b01c8514203030000019220040c060009254030154100034018540c5003040c500e083c91081981020400600480441880070101c50041c0d005004a402d400fa00500d0039040000f44400703000c000d801c40d5000b400d082c139aa889540c45028000f03403c03200d5001800c56107046070000786029900552001950400c8050f2000c44e140c165655056810b24100540c2d00c2884c100125246806600f001c0c0607401101ea01140c1c0585c841c15000190740501420301c10f945a810224281c11698400256500d42c060390800030f06000b9000583c941d450f901c0410b05050840140400340c803c108800c40c042441014144071041c06c181204800c4000a8010840486d10704000f604448001d04c502e42400400300016011146060580 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 645041528 1250 645040278 645040303
    0x1020c070906290a0e03120d11250c050d06051f0e060d0507030209010e1f080a020427050304050406080105072003190f0f031e0504080909090312060d170309 69
    0x210300d40803c0311f0620000c2e810800c58224210f092040c0e07118003c82c914103440302c5c4d5003c1141d10508107123114204e01c4210b080941110740013654140001c5590322000000c0d04580104408100ca2421010680c408040055100c88280c100c040c14014041c0f0020610781c860820360342542c8e4404681401440c00503203500080d4070008035070001c1143c0e00416005c03400750700780654a00400c4080d8080c40b801c16840d0181410030350040207503d0151610303400c61448026403040d85034202c0140d42103000ca520700a0030035242e03a07100103410042400e040c0300b010700500c0f0050080240381080b010051080340440c039001c041085c3d040135a04401001d0007100e00c0c83c426880d036900e00c2403201c04081c06090004442d1070100c0c0c41c3e62120280b190082c01001b121909003100920101c000d030f210b0000410004d4800e40343c40f40c003408560044d4031284841c40c0102d60560056032595044079550b0070048005004c1030003030004190100001e52902e008a1600c40100704031500c83d541c8003481841c00300c620a26 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 645042778 1250 645041528 645041533
    0xa1b03020306280e0c160f1a010308070209040c050406081b040506012c040203040f0201030c020a021f0903050f01090224070f02190f050f040203090616050c01020c070906290a0e03 79
    0x8038010404403040c4020b043c0e1150801caa01010040044507140b08d00f403001904400040043d8001803034283c0f445940305201e50f5505055948500210701200c4c09a00140c07034a90100d001040d4100082c01041403503041201e00f8407070351031708000080c02c001595003e850014184540507546d4280c0000c060089003016004546900c1c040c2404900004039940590219141c60900500c0c03a10200e9240c0c00341e5000741600781c032041c40e0500a1108030300c4803015410448101c2e0b000c00050400d000030b12002e40c0c020004941e0503814010002e1100080305507640703d124043e8078200c50b9006a0956010f20742085000094940302d0000c07a999034081c5820f1b101140003458045140e11401082c441554810f581202200d800d600511080340b006445e012820b51107000011540b048801011042c095585062410013a1305240f00342a40c0040c400a001c2c0e40000c034003800b0000540c8180c1c001030100c12a000c43c034520006c000643d24004c040594418000054005800f5001e00c40c4000c000c40702404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 645044028 1250 645042778 645042817
    0x6030e1207062012040b0105011d090a0b03060a0204031109010f0b0f070807051e030703020312070e03061008190809040f0e07030b01090c051e030a1b03020306280e0c 73
    0x161310640c000102c40864400b580c0e41c0002c41c59520540d2070360020b5210031400051000354000704010508002d0180c0c040944901d0b060310b02d86c90500c8000d0107043c9042c0c2c0942c9490a6282c2400f0503486c0002090140e42c0b41d030010030154052415006c219200040c90075682d04c41040030011511454030042e060500001d408400c0050001d00408006005211100980321405020340c4034401c660024005038424448102800a01032a6541005c2c030341c00c4c4941009201008a07051000898010741c0341c410308001081034041c184400b84e0300421382400302040c80f209540381c840e00c1c00351030314039401503903030300c8048406a03060b41c45551600b41100494414640d40e28214140300300c240118041c5a04000f260035416025100382e4141014032400c00f0444524494282a01c4c0c0005104400080e02c0b00700201c95101c00c8215150702d800c9030b80d001750756498400305109107103024003640b000014080c0c492034448585040078406032504400b000303090361220400d08040b40580c28246503040103180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 645045278 1250 645044028 645044047
    0x4060617030a020d0509012007080d020d0206010e1003060f090606090f111801110c0d0b04021c0b06060a090305030409060611010e0705120f0105070906030e12070620 73
    0x400303499440c03003a0703003111300981c0b010404850501403030a107240803440d14900080d21800c035081058007044107408460384203544015081c40c7c04081100b001c00360308490290180240c1c1846180d0141c9141140c1c0c4903207050807030768254010303201d00c8083c0030103903a13986520b030100058010360809030300000c0c1400a5030301c40990500501055882480c078a00e0800240344025055040c0c4051518101e002c1d024005001c00644035900c0c82440300c03100d80212001d00009039620040d4000c00c0f401540114030924040c0f05203d5010302c038615426141a0040030f80c40082c40c200400c9a01c800b00380c800e02d49402a500301655400d042c0c1d00010b090703020105010926003001e610440c00c03034109564071507900042140c4c0c5d07800c9940d0320308005915081002c0521542c1025002d80c003c03002c00004031094a59400c078140d0031164141c0e0580c0005005c4401040f130345074035020710640951b0040250021800c80ca10400041c480e42d50300402c1252181c00041901e26104a0720b40b101c007900c482c403039403400d092 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 645046528 1250 645045278 645045283
    0x3081b0a050c10272d05060c071206020901031103040b013006020315060f030103030c020a0b0d0b0f1c11011e0306081005010608180c06040315061403030d0504060617 73
    0x1030045049050310b070b007a02500c8180c500305e282c080d000300700840c2052508100c24051240e01062a00d10a4070603100c00041600c0c04008000c031280c0500401600c55201c20001400c1d6000c0c0e455039403940714148107103c0852114541241103814408543c05034041c9011041e42e00d9440f06405445885000c0d509000e1142c0398000318429001c1c0900004803075242c40c10440d02d070080322805a9404818401440000d0040030f01c0d9215070b0004180880c0d095a03a100b41034298005400fa0114545034030346822282400c004003c1022401c880c4d1000c10075040070a065201182807003c0c00f002d9610444282c20313401008507078641e800054203c894542d0040c3c0190142000384180901489682150071380200c0c203103c3d840c182c3e126543d078240162203c0035600599156240241810700410006607826903c5600620007944070303030000310103010350510706800c41c1c0c91a8030040402e5611034110403130ba5070105c12a0b40c031036581d950000b00341e203490a11a000344000e40052810240318100c001c00161700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 645047778 1250 645046528 645046607
    0x15010e03150f01050a0807180603060e0a0515010b0a121401030c03030e010924030b0a140f0402090303030106081e07050304050115061d04021303081b0a050c10 70
    0x4000c9031042c2c40e6a1141400100b000d00c0c4143c001d036821860041c080106008c500c4e01c0511410340021407019220384400f011908000c1c081001c55000e8824401045028001c0b906d02c003047c0f411040c0598580001c110842c412261b410007005900302c0c800b40310700a180d00c9400000c114100580c01c540c1c4070300d801aaa12881c4c001640454404600b6801d07a40c0302c0d401c80c806030b4040070112001c2c480e83d00540d441c0810440381c800185500d5106568041d1074842c201c0c0f005050030010030014184041c14800303d1b401685545009600400480c4103944001048074112441d03031070214036a90314500c04410041e1180004034503d0310400601400a0340080954015801240204546800b001700d0040020141c411070011414888080d4444591404900c4010360040c00140c41c2911000c1c0141010a4175001162496000314584074003d9071000d5082d4030003000310042c2038403001905c07900d03511100d0a0180b48108046400f2a1107103206203041e0004800c0c108074100c1c0201000c400c051211503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 645049028 1250 645047778 645047791
    0xf060e010e0c030618060d0501051015020703050d210507020a17031524030c0a0f140f031504140a0f09031209030e12030405090604020f0315010e0315 66
    0x1c610010541031071a031800c41c0c1c0104e100600d00d5800d403800e10781e4100850001401d0540c05803440038440c000c10006e000f058844d02c035081075002202d0070308103c00f10003681100d484085500450041c07000850000d40b07022454405d0a04903400f080001b030100210800300f0781c440d02c80e41083c050041e1160001900e0803058810f641d040001000030700b50050501080761448031000b0300c07041d1040d903400c0c40c2c110b090181c0405040d03006042d1216002d054154400d40c4c0c20203a2480024640e8841c2d548010106200d588900e005418054000e424214500607503d04581c0d8145c000302003020048050040c0c00110f20150050200344208004000d40000031900045046d0030140050007280d541d200c2c100c0d140c0e500d502c070955812461340c600d00042495605c00c8041c040c0c01020074101303668010704200c01d101d18800441d0b48038102018842e417a000981403501480c010300180e0301c080d0b030250689604c2030003041001c002180d04401210b10525100303076141c25000b0107081c0c906105106540724490320 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 645050278 1250 645049028 645049049
    0x14032109070b07120e060919030512042306090a060c0209160c0f1401050c1c0203060a09091b09020d06080c0105030610110d1e02121b010f060e01 64
    0x5644850602c01c1e0710a8090081c0080c400d0134400b50f0440c02000c105090f10405040641450304490103e458060240c0f000841005039543c00c10400400300060124400c006d004075040030b01d00101400711030350866411b102201107190100e0341d034031a00155809038100601051000e070380c81401400c0100460420b901400c140d0b0001012640c0c040403450401e50140e40381c445500382c0d61682c4121546621040f91600070301c4601c49101002406450f0190003807500c081d03601c0c0d03118909500c0d884007050540300300b64014020480b540e034944030800110780c3d60100102d1a034809150610700d1500d4007403c042802000000411446c0e6140d02070640810503007000c000d202d48860110f60f80703103444140c01d40064000c000080c01b03030905c40e4080c00702030007030b0910001341485070130b60b107003031107500311a000000d161540c5580425010b03900c0788501c0e03480b50020b081592100012030001d881003080e0340d032001080284c01820104254800c6855822400081000d140c0391803040c0c03051030b000e00c10400b041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 645051528 1250 645050278 645050293
    0x90201023d1406030f070506070212070b0c060f04020315040609060c0503090c010203090a1e09020d0b040c0816031512050f07060f080105100306050d03030c080c04030c0314032109 79
    0x24100050075010308014017004110442c6454100103c0741e03c005012604254440ca00a000b0700040125801408500e1400c0e6180c0074640c0c2c8170f503e0004000c1250400c0038801c010f10015072004030303503001c09600c00301074107000e5650360a184000c3c04480c0d00040415150903114090309610602070360150001d18151403041250500481e668090b440d10303603900c100002010005590764907501c48000680094001c4802c0d41c40c00000c040340c1040d02e1184249032600304040766440c0038401d490001c0e0305070904441d42c1c145000c2102c090b45040e8a03072414595244444549002e0b295003c1c1c0003085400041c440341c06503440c00c252110002202c4404501ca036980105d0424024823007a0040b0391155242c1300168603000801c4003003903103022241c080c55076038200400d031901c4018200c800c10303000c1d0710003048164a0902c000c01e4020b00420444041401344021310001c0c0d4028000c0003160b80040801c602400e000c3c00040c00e5124180509003c14103a110b242a1460418501c0748211a540c0545404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 645052778 1250 645051528 645051541
    0xa05010c0302070918020d050606090a020703020a02092e0905011a030408091f0c0209010920090a05060412030e04061a0d270c0801090201023d14 64
    0x15440303105401009a0001d02050000c01c0d1664070809890512100c0400c1c0c2c60301a4010031902c000c601130030b8600b608148108207042c00d01c60f809030b41100c0510021450712a0300d460085d200d001c1c08200911400501010802d16072400f600020005401e4020b003e40301040040d20705001c51078456044041d04200c0001003442c0300400450340c20480c0e060712407640d41c4030b6449941540c0402d448591006880c04003100d40700da01c080541d442c0c0d20944450a04c0d440301e004104c0711a205a01c0001d03a14141031841024909480da0451000d50540440391a00e4000002540c000d2081c1c1066803c40b102003000160411401071182050b402503e4640503002084140000d07076011b8050b4071820340645080e803141c40b580c000288040c00300b40900284074034507000c0d81c045264000c10500d1002d164407a1302c90621058107251001480510020080c8052690020352100c202e403902c4a0007213007264a03001c400302940e5151442d000b004410a030320b039041021103001401005041005809000d000566 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 645054028 1250 645052778 645052787
    0x30c0408010b0d030207060c08040b030115022b0507061b020a0c120f030804032f0d17060f0105070605090102031b09090109020f070606031110170f0c0c0a110a0501 72
    0x740c1d2501980903003442400c07c48287e90013090128100c841410400001a8540f00100618068a207a600c641142108181c000b40350142d8540b44001d450803600011050105d0205c1e1a040744040381441c1d61115082d040400c006e020020003651005d841216030303c0042c1c0d0218488560718401c0220380442515904920b03940031640000a0000c0014482400401e02846c41e0784d900c20303c02d02c0c0c4162950401a0307842501d008031041d0b40301d00c3c09100b40b62290040e003400b03070041c001c03080d00d800e080106826089000715000502070034040e152102402d5010f9110b4400c492945411480520032411f0602da510b00035401124030704041a40882c08030403c80d01700080b41c010007801420308082d030b400d101c0040025409010fa1048400b41044400006400b9010303003001940504107420301c0c94001d009010440801c10805010403c00b500390651189441000b2030704140070f1030b0a001c06540d4038481a039a84120452400726100300c011a00030002440d07002a841c3d88183c40c0190066659001941d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 645055278 1250 645054028 645054049
    0x14010305030304020103020912010e1c0e090105040903090503250b0301030f060b0a1d040b18070e07120e011a060a02151e0f07030b0f0d120c08030c0408010b 69
    0x402a820402c081400340d0712907000f60104c400018140c01c0c0e104c00984000382101c41c04001c03043d854009003120301d45406e0341400815001a9410520081c01d032400002e2101d00341400307001c0c0710701d58a005c03d1061511541036400174101c09401c9032040214030341c54070074a110090907000b600b0010480401d07460782c1d010949048030f0340f017500d40c0a540300c203a50300e4000d00000d81c070746d64000e41d8000c1e0000321040c80140310344641001d0900c102141c00c240c24a4021845c00038080001340345520820f41480c2e600061007022104d03105a9401d5a0f15003c40440748180ca44040600700d9003806d040a03a500c0f01036000c0b149100b401031403200280d03800c005100781d0740100c1499001603081741050101c12a1001c40b0033341c2c40102a0303090b41c105100042c0003c4080c005403000416014101c04002040f85c02d44500203c20750210303806084859000700080c1ca400030482c000b04030590b044a92121f903400740e5040c900141d40941c1c155180d1400c1c4242d440d007a080782c481c0381141c0d0309082c240c1a00c0d091250404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 645056528 1250 645055278 645055283
    0x608010606090506160c090b01022803081008010c0518040b0f1201020708030a06050a0b040b18010e04092103060b120c0c060a200c070509131b09140103 67
    0xe041501d80003c005543d041aa1011142d0800d048650005546c60300e5005c00740c01c41042c00a40810b82d000028980440c2e0308407403118480444045503d4003501c0709401d0300d294940741c010000e6480110007148041c0c940e11480c101d42c01c00d0700310fa500c00c0e04140a4a50b0301100d17141a004400580300300402d4450031000b064000018240f918801e041c1010f8030303104140303004000b5240144507512140141d2084411185095884038140228a003003411100104185094036081070700300590080948103181104060854210161905034011084410481c100500130404003071207060583d00f03090100e82d0041c03c0e150f11800144124028402c0c0000d865402100e00c0c101010402008500c3e0009404002c40c5081030081403403a4104004d820310403a810080480d02144150302c010b40c1241c1d4000305800c2900500c0040055071000440500f01e601c100c410308000e4607500c80d024500140c03800040c0a0319030b08904005440e290300c03042d03c100d070405502002800020310400da0851070a0200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 645057778 1250 645056528 645056537
    0x8010e0a1404020123040f0f06110d050706060506030a050912040f050625150501140108042301020c0309030c0d050a060510050a080d080c130515070b190608010606 72
    0x401c015520504030390081e0540711484170742c3d080d202840140746030403aa00012180d411040c040c00b0042151400d680205043d0414617080c148400800d80c8682643d200d000c01c000c0d0214208083c85903541001000700005070149550f818102c3c0c01d031026200881300c54610384244248280d200c0000c004540031101703420944a0028107110800c110395000c001e6a40121400000202c40381c0324000c0161290341c03007038041400303202c0c0e00700c42202901e00c164020b84030220441c10789507059803c407040560065200d8841d07110703040d043c8120746c0c01441071244081c07a50720210b0a03403802c000020040640c81011411113042400843c100100340980d000000d2003a00400c1c0780d000025070a80206400011845004030b4080c0c4840c081590130b203d550010f003055205143e096005900100425002030410104903d007030701c0103140c059103c6441c0b00740d03401072900154000c00c101409050710706441c0c2c4103214940a040c00c80b810003240803090401500945048400182d84074144130701001c54226856 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 645059028 1250 645057778 645057781
    0xf06060815060706060503010518010612080d02030402031e250501230f0d060e06011713020607061b121b03090f0507090c300c090f0608010e0a14 64
    0x81c4212900f1101e412a411a00c41c100455542e500b801918411a154203054603821020302c002400e4942c0c07540716a8241000c0e443c6140407030251802c0b248820891b4801590b65260741c8040b07440e256400c1c0101075208205101d030b440585010880e05041e0860801940342d110940d81c000c0548031807880b5040c00300d0201c0782003103030200c10440b11071903a80c01070001038206600010321541e203901c04001102e03c60341e03840e018844014500d05054102500b07281c850b40c0e4000e00c2104204800c4082d140b03402d07103181080a00115501e04084400503940524148100c094501c030320314640102241d61000b1036407240044185484c00c2c82500701043c074120082c580031208950507801041040c030140caa898400085102003102041003100400d00004000340c003d941c0d074001802c40031303100f03918600001c0303071103500d00b046403603101e49000c00224400c002140d5404000070b4901108a80c00b6515070340303041c4c400040e00c03030308101c80d54100d41c40c9000660a80d507403800400110307a004030035000741c49950300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 645060278 1250 645059028 645059071
    0x6090904110a0b1201060809010c1d04091a06030712120c08090d050609011503080913020903060f060301051005010f0c02010207090f02030429010911040f090f060608 73
    0x1101e00c8996002400512202d921100352030b005034007130043c0c2e900d040504c1c00104070555000b101c40c5d80c003800304802008900c01d9008010032900000c07101c0719481500e000d0740c540c10340d1158015092207900448030a0058a084002ca0f8840401c13a4130510901659000060902801c0c60a0794007d41c0280503110b40701c60a0015a0040030160081e14a100d00380076958103520342904c9500d813903010f20f0040480e4544a2001425074031814040c48200c0100d00003040061129002c0e035400b24411101d01c82d00741524101d800003400b50b900340c10f906121b10f4052022428501a4050280030150020300c00d542c0c0b0b03403207210f009600502c01d10380042c80b81c07810003004e5441130b81030040c12841481581c490964407103140c000e9a400105491050364004103010411010030102c40a030881400c8100c0441c645881600c6845014890100312a48079481201c00000720021903001d04500c1c2c0480003100d03116044440140039450300300c3c51652502c000850514000c050007407040c101e880d540b604421201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 645061528 1250 645060278 645060293
    0x40902070f140109061d1f0e010c0c0302010507050f09060903010e010c0e030c030a11011409060d1a090402100c03111207021815120307020a09050a0b06090904 70
    0x644094415080d409024400115035200100380c09814a0020078105041d0070502c08854030b00007440b499042011b003140310341c2070118030b034801d1401650440c0814100c01c0441e00c0900b0503001c07070003100e529000c0d21030496078105010aa6890003036000f00866500e402d010384207803080f199081a032903020f000d0609585021001400c1010010300041240184030b020030303003035815000e08207000c1002c6070001c213018142007103010054441100280a0100d42e0f84412000b161003046042c100440308424030360140b01c440460782d8140c00504580e643c1e0984c800494024020100040c6c4088116a03290000349000c599484c0240e400034101502c0034611038060f214403050100450500040140240e0941002d00a421441c4050b040d079694031411071041080b400050700c4880c0c602001c08050000704c45248841641c045030907114400740c90003c90540d46180103d1000950201041c0c0020030b0340000e5401190280c04400300038000a1080c808010080c0104031505400034515000a800b05104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 645062778 1250 645061528 645061537
    0x12130e0601120509060702010e16051212043002090c090a031b0603110a0206070c39050a05060d1d0f060603060f06031c18121203020a05040902 63
    0x50501c18142c400d800381e2202500d034100c910a42c40c1e0451030130010b48036028021403907144151400707825080c04118102c520303d0518001c2a000f80c1141174038202c502010401c1d220301444c9510110744583d079896610b03550612918020714078204400b110b61440046c41d41519105174020150700300307562085401c1c2401e41042603030070f038091207076407001000c586490300706e41000040c0c0b80401c15a506054000c0c00340c42c4031280e00960b0043c05c200414160754081009038100c4254585010302d1041c40c00c0030550040c007416002d0074550000c9001e480c5000d840307014504000041000328585660308100510740340640b08c0c6a030010801c01007040d10801542c85407403003440b03584d641100000c110700c00b0f5141800848440440343d1203031301445202c2c0380c10480140d00807609030304196039191000100741ca03003441e008005048900e2945180b481c60083c681c000005442c40052141c3c56950304002d00d00c0c2d0300114060341c04a41c2119441c402500c20b0080b140c0030f8a4503241c20340342c50300e00941d5000a40c803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 645064028 1250 645062778 645062791
    0xa08161e211b05060402030c0d080414030102250b09120906130b070c0315110f030406060302100c1a0c03180106030203030a0908010f060e0601051b0f0f12130e 70
    0x44401d60080004080c00b64a6200d901600082400f40303403d106040c035026120308613500c94603022180b040040e06401c11a0291101c0f0601c40401450120210340a07008081001c1c5100e113188134245042c0c3c075240c0c00085810f0040d03040e0415600c1c3d0300d040646543d4000c1e91400070000402130001141450002440300141110400303000b40d035241c0081c0400d40041604544d58200c0500820a10211032468110003880030010000040d50400c2c40c1028403c141440c0481c42003c030014051008550200000715000f5010300e001003591a0020701034400810201e400504178103860401034118268144a525444142d5142d130300e80c8079070400074204901d4010101d40d200d40d404030058509101821280b407950712a003c0203400d0140260a5510400c2c41090491520400308240a072030307005c840c0c01c40b01c20300380190390f036170b42000015a0322080740e4441d000d4441e41060301c0744a500010120306100b0030070140c0e000000300b08904101840350f4050030103055110785060090306c80c58900d0580014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 645065278 1250 645064028 645064037
    0x1b151b031e11130611070906120609020105131410020c09130206040b0a0c150207052a0405010e0402010906080112060f0e0604030f030501081911030a08161e21 70
    0x488444540400c80b52034000000007002e005c10b08220500c01c02031840640025a000d11009003040800b0380504141000a04569100c115a0084d0f90151007118440d03410303012400080d0340c603040c9503440c00c3c11401c0700900440c100d558400e03203c0d2000c80e40c00c0110000170950700c03031900c480101e54284c00c52044180c3e88030108001c0000d42280d200000c20350036240740c6512040c40210309141d21111460320114400314010450140020070205a0181c9400b40c8003803a401758514000f030242e1110b503903644a40161404001050141e90099028401d0340b003607907505000754403060200e9144074207118840a0300650303a19800052829000400101c401c8900081c1205007411000e01e804801c0c4d5041d000b0860701404603401c9079041c0109409002c061004024580045a541c13110441c0d280000c1d04910b045c042c443c2295500784001107190b43c0010b802500c0c1c40011049040424911000700c9006500c1c01003c514103150161180320f494120042005456066000c0d4200c407020030803110401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 645066528 1250 645065278 645065287
    0x61003020a15110a12020606010503090c090403030608030a080114030307080a05180406030b06040e0601060507060e191506090c080412030905032b0501050307061b151b031e11 77
    0x603d08002442d038440c0610391410b12040090350181c10f1410103030030750381005030800410014050015483e805040143e420321202ea0b80d5007811001810160041d4030700b4000010441e8846a00c001003034181d071644c55107521703100002000c150756841b9012008200450500001c90094015406040e003002d1800d000304d990b201c21000601111140d420449004002806104150905104191003014100300401e00d039410402c014001c1c0c01070400c020300c481d84407104010032500500003444100b5001d0080f501c0020315141440c4450b402041902000d86482c40000e0464000d00890507a50704944405515890315181e01c1c51000265003a003080c96200c240c007000285c400c1008100c00008800003080c0900c6200403032020840d0783d40034000c1300c1d0070040103102d5540e002c0743c440e00b11400d500f415440e0700070b46040b08509200c001c0010b42a10503c0342d140440344825080300e4800044020045400755aa10b401d03011a803981051070f50082c00c0d00d43c0501e491031150320001035811031080705800c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 645067778 1250 645066528 645066557
    0xe0f0c04050a03150b0103092003030c010e0604050f01090c1221030c0f0207050f04021e0f13061803080c0c06030c070b070c0302060412030e1608061003020a15 70
    0x210150344111181c44e11044925032072002d900c03034010b04075800d18040c8840e92083d269400440c0c0d50401e4480040c0e0000c01082603554204211503404c54504000d00c02c05000e00041902d400c011102a201402643c107241043c42040c800c8203032590b4049104035140c1c0c20044030b05800d4883c40d804075100601c03600d82c0c0c00c42e8800700070504000002968086402e0304a80d00007012200020b40740e10955001d69001c1c03090765900c0150b000000025600143c40f01c83c1c8203101c2c102480c848940c10566503000894041c610034140091a4282910701c21003650341d51803c3c2125040e403058110300d410515110180000ba608900604945040004444495081d01c001500590bc1500c01492102d00005e5070300c2001054001c095005166042070802d48190307890194036501b000340007d01d01c6241c00d081052042c000d40c894108600c08108480c1d1104004010090701c03030f41400b17511903c0c030940000620061240080f102a2039015140020017071400844621810200300110240302c1c403400302d81d04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 645069028 1250 645067778 645067789
    0x304030c0e0a02250c0b120f040804120c03170c060a0f02090a1d070804020d030c1b1d0a1109011d15040608070f1b150609020a0909060e0f0c0405 64
    0xc1385072400304100340110b0b6490804000812540701c4c1c14000300038421001445150074005074889420000302c61a9507451800035942c3c8280d801c0190404401c1250f40d09201101c80418252882201014102944008451414001e40d42800802c0c0d12020004a03501140e0b000400e00030085c200c050309181d1030000080d030350744c100d4005c0c03141d2201280150009280c0394210036044500d605061f2403034282500403074003039000c444001d418446c1ca0341c012410404844545100006d0240c065115551220014540070f80c003c4100c1d021203160101050320604144290b035808001004500e161411980041d101640190382004000b2141c110b820241d89a07084985101c01011042da0b0761340d81480006040880080c045004100380c0001e11071800f41c11604201e050201c1d000f02c403003030340160300d0907000044550200915650030240b00085800036038029000c0201aa117400343c4907038a441d4104103d403034503c2500081a8100082200c5961861255800043d0420001d151070b803100c02055 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 645070278 1250 645069028 645069067
    0x40f15140d0b180603030703050309071503090203010f1518201306030903050f0304081b030301091802061e2b060504090c050f010e031009050705030304030c0e0a02 72
    0x414060312144020304600d080c0f680305a50100e402400d035642d0824502003692801902e00007001d0080c000042004040100440c10041c1407400100c803095045946c010094200345104a000c0c0d0309002c40c8541e00165070150610800e120b210756492540b41034481180045944250f0454075502c5442000b460311403c1080f0006038001e0031170fa92010b400100324210036040d40104201844d004400c000694008110b52901154117840d9407a034607142003641e0b440c4a903114121018208422100d0618800300185048070101a4204904041c100304e403980f2a0070450b009600441c01c101402e90b600b540c2000411010100c0b807050b05104803414150a034801d00c40800c00040c00c01044000c0d00d40082c051300014041c161014004120140d5406601e45040c1c09164807680303418281d080941d03c210400208158001c048500986074044050b004204004c03007a6202d01075241c001c00c0c1820008104c80840e94084440309100d0700d0103240d0f900006000d2700f008141c0343c081210035200d1482c500c404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 645071528 1250 645070278 645070297
    0x80618011203020f1f02070c0801022a030a021005071b0501020304110109050612191d01050606070503031501051201030305030f070306061b0f050109150c05040f1514 73
    0x1001c8481032810040e29000100010544a600074032034040080000090324420354010200980c032054203207000c424100c0c09400402481d88082294030705241a08155000148070480310004140445006a141d1140c04224409a40312010000302009a580250b50244c0e05182448440c039026100800c91564690207462076900481800140131989405140203e424200001d4042c54000400c41074001c4001000d001c284a07000101480c030740b60704101500003968001c000682000c140c00204882c00d040c5c450b1a586440001900c5080c050102d071050760b00310000703508568034403080700c0e00d0007051401c0303c0c1040411300c48502c9000051502c18041c6109403140364403850700300904804810000c2c610b00c10103080c0402081000e4000007012058506035240364103040180c200540c0070320000d440240550710f0007d144003449040302864440313489065040c0306900008a080301e6174095801501143c0715000710400600300010003518100085041030384205001210b007011302c1d0443d0814 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 645072778 1250 645071528 645071549
    0x30c0607140601061d03010b090a0c02210403060b0315010519031506050108100e180102070c08160905040b0c0307020a06050f10050402030115050a020304080703050a02040608030306010f08061801 86
    0x10350940d85e44003030303000f1140d041030b03000300081e940450015019640180c10303c1c2e01c040c0d43e0b00b00002000e1090049100c2d00510320910740f003071400100c603810b00d544030b44030036209070b4507003d0004650307c1c0100c0d4030f5510303041d40720703080c82030742d00700f8042056412004514002541034910004000b518424519420841c003000000d2503620781000907000f807500408100c0c0d41c08401c042842681a6200400e17044601803103480b40b40390100041c0c500a100c0c001c0c014003404189076001540c01c1c2c000440010b0b8540c8201721104d91035451188100742d441c2520700070b01e1203a6410001d1100c1d0680c078040c40d481005c9104403403042c0d506440e1081103a00039200801d06071500c41c10408210120942d01005000aa60462a42d0b00d4445001c0312007108100540411034000385060b9018804c005840103041c410f8252024076035245001503581c854900101d0003641000400508410003000303030380c03241c181a100c556002c1d030b81c900300f12100a4000c2c282c81d401010f4404070184011070b101d02902038880d0104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 645074028 1250 645072778 645072797
    0xe0a0c090b1507020d0602130e090708010e0a03020307020603070c1406040501051506070b040f05100204050316060e0103050c0c15151f05030915090a030f02010b030c060714060106 79
    0x14003841c00354400ca41c40316002c1c00c000b09401030b20b131a0740702d5940d107401400060300c6190b1100e4074a5050f00c1588541d8100488c0014030a440c080070039a08103c9071041c000700141960090300c0d41d12103180d85006805604180003140c05800e001000b15403240d60f9140500d0449080d036a501d02d801042800c0403402d034440310800c41086070900c01c180d0001c48003113a55244e4600c0700002500c600ca102d900901c8020240c0202e0100914110500314a6a02c40309960007104810501c000035003041c480c413482440faa641d040502c55000d1100c0707080e50800e65072090300c4950040154090b01000d814010006070030032400c429a00141310380b5144101c5040c1e40d4044d41441e0040520215403001041c0c4202030b016010b41414200e0f01b50b41450208505099480340d40707140c40941402c2444000d6030b480c042d410300700260300b140443c0000b8840d2003074582004a000740d440032404c80e003a01240d130b03806a10401b407100c045c0c5000c1e0090060988a1885400310304012030ba00d17070610a0a0348440c0105003443c0e0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 645075278 1250 645074028 645074051
    0x90f01060b0432030a050a2d030e010c0816170325020a0f0c030302060708071202070f1403030709080a0b040b1e040b01050a080705090106030e0a0c09 66
    0x64600818180c1e0340a41050b04264000c903940364009410107404180c8644914001069500304184603801001d96182c0c00d083c0c241540ca81100e484101d648581360f825901c02c5482c1800e00d1071240d506c1100d401540c001c0c0c2d81d016102c60041300f401030305108018041c240092400c034003d00c0007485624600e00008217a01e0201e45e03260702400034900c613031805d104108004c0d4210042d18440d4141c503601940390840c056099081c041141009003100e51109102014000e0111128084034420380c220303605683e85940494441900740e4411000540500c541003103440aa000390000c280580e013961000c04556070f80c0c3c1060100840c20784030582011040040e856000a0160000c001100180243c01d40360360310b4010341303074005100814410100010a038401a5120348000e240411074041006041900b040700c2d5904007407145074450b0100c06000700b0043c0340810035404541014001c2001a42402c40a07405840c0ca038580421034441c08620502248010420f0303c014000250009488136009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 645076528 1250 645075278 645075281
    0x4140c0d060501050c0c060f0f12010e0612070e100504050f0a0c1b0b07051603170702030a02060f04170406030b030106060f020c130e101d0604021c0c0905090f01 71
    0x1a840b050501c9030601070722807200e402203448445141e04894041d540d100141030950b06003d0203a11040c08100403a9100950403081080c070305940d10b03103550820341e80d2440104000c150001841004541105a04000094207490180e03000b20030300c0703402e402c10b645580110b01150001c46440814041c01010300c404072603a442080707501d42303441c641a500c02103907070351342070180121603c000d11520003003002600461041b0b0990f01500140c06040c0c00c24003650500509046025101c40c0040442c2030225002c48e000104403211001715030064020369440003a44450000000c00540d407540091401602c0d10700c00300300800c0580401e03100003d96003008005c7c5421a0410b8000c00c0600c03151184c000c0109800083c2c1c200416411200c0344841d28917401e08401804942c101d0007203902c00c89101440803607407030704020031300607841030052a48060045800e0381d1340001c1c2c5020b904008a06801030082085400003580c0c0c601a40742ca90f4070035070320100081240c404840883c0942c2101c5070840c01040207 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 645077778 1250 645076528 645076541
    0x62c06160c02150a0e040c050c16050a06050c0309040221090304060504050909010902090114090c16080a17010b0702100815060714010c11100908070b040204140c0d 72
    0xc52810701500480ea5011a08a080b60504000503820208201a40300d01c41e1400501024014000344020a61a84c01602c1c9030071441055005001f503101001c0b00d00c4162542c02c046482c020300b61403c0714a44081564154890040c284140c0020442c803042900c840c0010300030181c50150003140350070311003c0000038020280240225130801c100801240b03502400343c8040c1c420803100c0040c191503d0080a0042401403c02504625180e00024503d00b041a200f1078140d800e035441d0342c460790352507080030b828414074124200b000140b42c644000304d01c190010300302030f2030b0301d0809140410076050080c0b003400b0241d0140e01f8080700042c2c9001182000a0710565000c2d80b0b08002c2ea0314140b40c01040305011140100c3d600a00c4013054400c00c2c03101050040041c0796005000b0480c0840911700109201c4002d02c0590840c842c0004400c1c030540e4900c101c1c8e070302c1c3c2d40001c1c081c1c0c1450100c0e540e40002000150069900640341c000e2401102d100f05442c0380240c10420020383d46810203901003040d95403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 645079028 1250 645077778 645077821
    0x405010e04020109081f0e1903020c040b060903072706080a020411130308030a020d020c0f070803070c0303081306050711011503030507080705070e070504082107062c06 74
    0x480711400105000805030a030030315101090201f440c00078a4849460700b039603c400c15a00f00f800b98042c4042c190041507c0c400d608059400b03100403044001400b007140314a1091640642c8140d80801c07803a510071740b8050004000014604480f4400c85403481030740c20a410a41c559006070003844214034140c4241c07000064044912824142240d50003034070601144405480c0d140700100027010480242d04070341c10040603000441d1609803843d5141d945100c0d045500c01030384203004011410072000020f85510584c40750040c1d00c10b0b0304603902280c4124001e400c0d04e0714034003176440c5100000c0c094014dd504c607100969039000001c100076640350135a41c01203048200e84550003400c3c00401c4d4040b00702e034006600800c0155844a55107841498901031743e02032045000c0c103505021019900100910496800b882201d040c107502c000000d81002c82c0b440d500c140c0d10020020880004d6030f64101200c03410100c441001000c9101000b5101c1d01d5130004000030303942111040100c1884400301e035107a10341 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 645080278 1250 645079028 645079033
    0x70507150e090a09140708012c0607050a0509270105090115110304080d05070b07090f06030b030a0b010f0306050f0105180a09020607061b1d06180405010e0402010908 73
    0x300401080507800064016000d45455068072410312110b01d210390701740c02c00d12040362404c030f40e100d201d40c3c0244400480402500c403415060242002030780d0030780040d510a400602141d44440000762110342c8080265400d22038140b102c03182958400003010741c6030748480b80645c030071107080c80031140c0c8142c143c205600c580103c9005001426034100980260034580c1822401a6035181000e451401103500444161180d00000822568440050103074507120308400c11035600c80c0c040c00d480d11501806400d513040086242005082d02c290080d22a0403400ba040e58002c0300f540d00c03248440c140980040400c0640e0660820410603240720307035a40185400301022640d410800010911035600e042ca841405181021031180503403a4000c5054071383c0208039a030385003124078013500500042402040400c000c004d0701c15000e4006c0b0001c40c05980c10001c44019941e80070204081d5420214111000c41c241c01c503003290780e807258825030740030b0011010407005900d05480010003034030441d0054490368 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 645081528 1250 645080278 645080297
    0x30204080d021219210605090907030209070806010c1202030309070b07170708040906080d080708090a03110118140c0604030809152b0b030c010210050702011107050715 74
    0xf0525400c0d503508004100d54002c100302070950440b0002441e070540c0d041040b0b01c0800340419400395002008840b003d8541c080980c0d00c0d100c4094a60f0f00c41e01c40650402020000a5041c603c02c0e003d02e54800030504101464040c02d407140320842800100d50000350f80000140421648100283e00c02041340b00740f4145010030560700c81d000d8640c0c100c2c242e80c94103004201c0f101004070210607180070f0704d80c44204125499554181603610480c02481c0c4021520281c007040b03c1034800d0f540544900d504000916010b0b0840da4100c07407614101520410030b5503a0800402c0d519400c49080550501032001e0441c4a46e01013021410448180059481040d0421040000500b9141612403050003150180d00c040b035103141146c5244107a0700e08240340d5404100f03c0c9842c28000090410002c448a02041151a0030f0207241e680e501072040280542c1c0042c1c04103903071403c150400e40e445107240c800455952455080c00b01241c00040084400b500045014003c103040f90000d060110300c203117880c0001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 645082778 1250 645081528 645081553
    0x120b1803161e1109070c0b040339020d02030c0a080c040509030c0a030507080702060a03150e07053702071403010204030f020103240f050f0423040f0c0303030204080d02 74
    0xe80c001882510b00800041c00011780c13203400381e04800042034102c0200403451038603180091840c50305030300c4681c807502c03010318190300c24030494032291494218800311482c80d40c0603020401645002d4078100c0c0d140c07082e11290700540e1030b00e200e10401484050005c0400d14000c2081000b40c90000f40881c0056105119503511f800001504400e4103403d424119582e940500301603078548030325103010350080c41c00039401c000d0540c564010a125020700221001c01500c5520a581c0304505690040000f0010300904054400c2c1204000051992a6001d8082e03840c200c2080442c61200c030034600035821080d0100501501c3c1420020002d4086001710316050460b9140d0702c91006405010b8101a81c0f10311000180042a400c000302d044420849555150344007003032020521240507150098040c1042d034801e9041c1801a00942c80c096005010720002c0b14110703169241000b04180c4100c003e8002c0d400c04155408000406503009503030240e0f8407424008010b1500381c100b0030a41c04c651040095404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 645084028 1250 645082778 645082793
    0x1e010b12060610090e010e22081c1d06060a0602010b031f0b0307081c03060e01120213021204030906020f07031106130f050a050a120b1803161e 63
    0x24002c90440c1c507010305800c1c0900455908002e0341001002522050010400d0060400c803d889000d0006a20845140300c1c00d000204240516008010907000c0c0320b04000301c0c40504540d04c851085403c00181c02100070085106060242d240c10030030f41001092100e14146050800081d0000c0d0000744895007d05002c03ea9550300c8100014a0820000114244000c180c0003865040b200030201d90480307494070016a161f181407900780503c05008410181010b000e400b0f60380482d46c0da407440f400f00ba0729214545c11130700880d21040342c1c407000d41c001c2d00814103641e1020300300e0340003c075109031242d04d0203281c0607044c411147c01100c19507020a000c41800742d00000c1e00c0060f258070604850101120802050b010300440c402031801c8105200b002c102203d000201030101da004480b040440b03a07075903080c0700646006008030f07602d010480800c1004074079804401c50700400e0890341d281c044580c44800b6421600000758140740a21889080301c14004074900051440f03003c0d801c40781f0603007055540c154 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 645085278 1250 645084028 645084031
    0x1a0909030a1241100b0702060901140a090509010e040f060b0f03070b07110f0a0603050601050714150f07020a0308090f1203090106090207080d0b040603051e010b1206 73
    0x8801d25140c1128050b400300c09841c10081c809280584420380e11440000c1c0f960000151110710b10484010004e0041c1410710448001c451040e40c40601e803407119002d00486900c411106410310140c1842d03221004c00f8038004201d46441e594400500740d082c541004034151069000c02603030207603803090201007080d150341e012100f50b0001000034084510700114528520f90380b00c0a9060044100001d82ca05000000f801602e210301411039006400e00100508015403072083c43c4c006402c15814020540658040b03034100c9014140903003050300d955541b8041c01c0844c83c207401c081c1c12804600c210038601041c1203400401034400128245080f0f54001e50b03e003c84d041c00b808209540e004100004800c2c02070103141ba00f550255200c03003014500203251175005079080304080d841e114000860410600c00d94954035031100d4224603040440c4600d5004e003c29120b11039101c0d40d40c8400100003039080010b0f0382d15000104120401141032601d403030860310442051b40c014180d1040b4800e03003040109425 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 645086528 1250 645085278 645085307
    0x4050709140429010809010c1407080c01020403080a020f010c1b140d030203071b02013903030e01060b0702060d051f1409072d020a061a0909030a 64
    0x400056260000580903000d03900c440c2c008162a0519042c0f140350804030140760000c2030703c43d18250340b540400c80b4202d8000381001030003e000c0d5a51200c0c03012404000f00f02d540c0c00360314818182000d9902041c00c80e0703c00e0b0303c01c80c0d4890340001d200d04007540520030507810b406104000c0100c00c0b028a40500103182c0100c1c00e10096100040d43d50030068400120803842031500100c0c2d0207903003045e10240007503100b962030602250400d54000c0780741902c204400031726a8107950340811040c200304691404070307a120700e00341140041e1941040110601c0300109829021f503401140b17981030b400d8180c2c21220190080410345204007c1000507071941000c40e03603291014400050142d4400300000c0c061042e518440d038146081c0000000c002520f403100540240301100e0112254407140c000303586081c207d60010315046a000700c00c074130302c481c0c1d10708008542d07080b40152000541030703503500002c40d804544003c45d07045050040703044c0c40c00d007508002c1e80401c1c3c520055180020340d44015010401801c0d40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 645087778 1250 645086528 645086549
    0x50912061515070b01030c0305012d021b06040f031b170f0f13031a070e1011030c03041403070602030d0b0a0b0d020306030c0405011208130b1603020c04050709 70
    0x304204402d1981c1142d1090b908204000c03080d503101e2900170040040342c40107448940c28000c042c0040d40d280c3c500d070203c140b40e945601c6116070404801d04080e4000c003da81c00400100f0a0401e200003003440824803a62041103030072240700982c60090413500c002d000207910a00710324074040004a031211480b401030210185561603103410ba400b90020301c40d002d0407560356a004580760306080f200050740b00581340b003000c00180e44400009114000d2208440440c002900c3e400c441403942001c00030004075007018070381170411815801044d40346620103188842c040d400000c0c20000701031041030000c802101140680724051a0603c000c0d964021030710001030041d40c0381680c42680d910f0100204c010003100050689403418a03024034020342080b50018001c0c007805d03601412030300c2d245c807034541030b40c281c036a104001d010780b5110050750360030540d40701480101017403001c1040b94040010704001c0041034140c1c090b43e03038540750080c1000d82c1204058011424501446803581d00302800c142580d580054 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 645089028 1250 645087778 645087799
    0xb0705160605090d0c121a0702010507050414131e150506030f07111009020918070603020d0b0303041e06030e100c030b0a0b0901110c0d08070f120509120615 69
    0x91003038101d840355200501c22000986c1401c2008100010407a1070f9010028070200c42e511508142d09854003110220005403080000340f0011440380e03820002d400000d0803107000d00c010080700c0c0f801c03600300c01082c2d04200c008a410301181507030750082c1c00741164946580900d180c074000104116002c00b8100d03100d100040000200224820301001e400624104116801d11604003040001020001c3c816402103081000141d10503d0043d0030741c001c1e00b0448001c3c0340c20b510b4144118000e403c2030350610701d01502d661000d881550204040d10240c050f43c45040e0f070700c0201454004480709168040d1050606111240800040c0441d1310005203101c0840490380c0080c40c0c0c070450044ca00494200c0d0b006d80b00c8174020800203020009801204005c0c1c88100811900700c0d1420360310f10907040010b038000408a104c1d00080e09940140c45243d00c0303044108a07070082c0365183d502c241440590303640040e10100744a4100d251001000101c550300001030005410640c6a414003c0c031030441d082d006815900303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 645090278 1250 645089028 645089033
    0x1305060a0b070f020f01020a0b041b05040513060e12180906030f0304121a040605090c061e070602040f0801020a02060f040302060f1b0c010e120f0a0809010b04060b0705160605090d 79
    0x231080d1709906c450b402126141c607213480c02004080e40d00c9400510b04450001c034450815104950184a0b03070b0050100002035527440340041c08900324401c4480c020b00e0700c1c42c3da6491400c00078094410402034007812461849c41030140c00d640041031184240e020000d484c1e044134020040314186c580480c0504855101428180c84503290549549250901c18082105000305544028059244903095070840b581c52006c00105008a62000c1d148089240081918120081c0104010740c400c1002608140e5504926800d1044613440a0401c0e5000508800030076810b01186a102c0c0620300324080c1c504003078a009669400040c013070b0070140401d40103c1c240002551601103a8030300d2034181940c2d80c52081c60140609820444400c1d6445408841c007030942901d01520100c10100d0f44103801c01d913944504940b0380a024140c1c005a560701c2001c0c010a8a40380601d00191a0303482d225540c2d40041d00d0401d04e45a1050001c8000c0c0261010603c0459807010480f805200100d58291682a460 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 645091528 1250 645090278 645090283
    0xf0e060a03140a0212120f03190c020f010c08012111030d021b100e131e1e0b1c062a1701050603040f0302010b1305060a0b070f020f0102 60
    0x582024081d5001d80041100e20040010f070300283c2c41c42603542030311451580084036a80c0b24600120584410f0901c800e44540b0801d0001d198070100365071421030130300004900601164542c5980d0001604440d40301c0324103400c24000e4000300c2e440e034601301d07001d58940340171180c2084000190b81c05400c6804944e0b0144a100729051441c000024140c1d50022400d0328069030364031407039010507040d40d10080031208500d0500490014401c082d00c1d64541c042d90842046454446403a1f001544c03560f4480d40031021030409118001070031040000500e07810515501a110b240243c0c8601115007444400022920760f00c000000d0744160080121107414203103070a5024203500c2140c0d04482c60b082180500740300003040d020008500944030864848005490300a540000740074080d081035040010600290001001041483c042c0c400001d0300c94254001440101001043ca1003035900c92062003081c0c64600000f40080101e80050343c0740030200d40d81e0381140031001078042d2052804856035500c5900a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 645092778 1250 645091528 645091549
    0x901020723010605041401030f02030a120504050913111903140307060c05070506040803060a08030d050402010f020c09060d050102070c030f0b060a060c14070801020d0f150f0e06 78
    0x15030662000c8a40003502280c560841c442800d480d8284000001c00f41402d10901006403100c0100d050f0a80c215100c4003445250404126058464142007070701041100d0094000e4040903503031141e442e40b80800b00315210802905039440200c031440e0300c40008845004945070408291080ca0750030350305030540031008440f9030024090389140c03502d14401301000702c0100b42c860b1040104100701c641080b0100d900740074401c0001c10030750120f00030074040380600c0061a84180c00500001c942a11080801c3c203642105a140c4800351b1034200740800c560b0003a0490030309035580e100900c0700c00c44660001d003406402078030780d500400650140f01d050100a404031120340e500900b61040103503503403030084510100c0030020341d04910700300d0115180f40351921700c03c0c040f158030b80c0d51041540c1d03030f5813a4481c0450341c0d2241464107202c0d5810009a010013030025040c00342807800c0004012001c02c00d40c10030303500301140342c8084514440003888203200e03a50181c0291000c2030202c005580d42c6002242400c6003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 645094028 1250 645092778 645092783
    0x30c0406090f12140c040c091e031e0618030e090610020d030f090507060206010e0a0203040c05040203070908011e060b0901050a1404050a240804030f0509030a0812041b180509010207 80
    0xd26407c100702e0794005880c5c004071496015102103403400300f03071805050304980c00010718020303208410785a10800072444042441c0940e42c001190038460300c0c012001c21204104802003201c04000b505549451040664000401d841200480311340e41e0b8000d40f5122038441c2e00e014181d44000040007030003680d212a046950050895210b280c0744e09001e559000c007445250030280c800d00019081450303034026a070055501c85a0790070480d081a0800020b5000108607404011200400080c02042402b59505107041c440c40c1d6501c107900d000342c40c0305030f8010f41c1001148400803c41d50740d49907840001c807588128a480c0c60f1381c0001c45600c85000501c510390145501c210282c101081c110701c0003207507020854001c401004220102c0e2025918000105d130041c1c08291120b003a43e082600640041c030310110028152070070380c441503460000f260420000034501100160400c800c10060702c108641c91240b002c0c18170361461a01c2004d022212840707602041a94842002c02e280d408250180c030038555 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 645095278 1250 645094028 645094031
    0x70305030a030516050f0a0804031101110c0c03060f06060901140c07050103060e0610031e021206040b0102061b07140a060f0c03060e0406110906030c0406090f12140c04 74
    0x40c0d00031801070203004140d4a9101384024208a18030043c040c1c0221040c4003403944045040041d6008281c910031710041060701440200d061407000007000388039040d450251894003541f82d881d4180304614120780c0d03042960007580300005000e262170a2080d85980801e003140c04035a18030a503c0105c0b105250400380100d010008107040641280208200701a90b10a80c0c081200c0e03540c91303103004021039003610181e4010414a50220007903219407c182a500107a0000400d10049290080200d0348005106c085050040c814852076107013a0090400310002480100480e080100d0340d804140711092044d032000c88009559801c100c0d01c0c00c042685401c100d401e6800125160400f40c014020a00c04400c000340380141120b602406441400709031040f510003c603d6640d5540c841e070081c01603000114001c1c500344400d4a446d99a40025072040e210b020103c4d40341e40c0b800b03802404d070034140c3c2c0103014081003502040c00103004003000c2c0c42d1819003040c030390340752440500012401c200d2120081a0000e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 645096528 1250 645095278 645095287
    0x30b0a060f080c2d09030a0312110301080303010e3102010807030c0f210914120708091003060f12210e1512191808190207030503 57
    0xd640186040462103815100d2801c07030350340c1c121100726030b104a070300c8400180c1d074004020fa9096103503040d00014203d11210140780800240c00245031014038041200082d25103011103002500714000c03000707480e615420240c159410f000f0b04a480b40014043d40c90103c0080c40021341d6000f4500c29000287c0403556042c0020710500c110349140844844240d012a888078086603180d403003445108410000d941e648924034070100021200d500c905068030701c0740c2a030b4900001c1c13488480c2c410724414038401c07489401089509444282454114040e40309864020b0060b00b0202e02100100c3c0d4150381c044a482d500f000c10144150010038013070700425450b41030104041f0713005d80c0340d100b0103014a00403140385140c0119074141408041ca1030802000040504100c1025810050811114029044901810103036401039078140003030201c600f04002c1940520101d01c902d0350744626111091200941c1150007482e4a402d28284203a0309140352000760f801d144071500d407090215202a550020a581d5036 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 645097778 1250 645096528 645096539
    0x121b210f140f060109050f0a08060a151a040b03061201050c0a0908010b100525050a0b06030d1e0219060207030e0303031603050615071a01050f0307120201030b0a 71
    0xd00d250007025516006000c003280340c4901900600d40b0509050307480f1a61241030200f440340700352200050780d070029079414011031703c0c1c03d0910100f481542625400a000b01080649203440c110560249080b418880e0001d440028031034100e500391215289803d6590700ca541c08148041145540d0780c90075407800341448424244100200360f01145c96540c4400140c440c1080783c01c070342885140c103038005c40701007244200c0d03802000035001010310001d10b1641c0d003c001c00322001c43d15443c0780449503900700f030001d041003284020109400000035401050003009070040608540030500e00001c421003401c51140c0d034035100b003221680c0d08100b46061030b0b042200c1d1400c14040e4116640403004a082400d40411500300001980d1050b10303511303c0e20305a5030303880501350010403000e000541c020000800358080e00f07910400804071148078004a100d41e030f00204000d6910101030f0006440b0300012b00aa1100b9500068101b05903040901d0b00b0340a1509480160000e01c07114101c0c0d42c0221002100099 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 645099028 1250 645097778 645097781
    0x60e0a080102030403120605060a02100b0301180b1f12020f03010e120705241603060f1707080309130e03040e04141203190c0909020c030a121b210f 65
    0x8030340928081c181f1403903490750108100b9000754084540142e00c2281c0d91004507640d50844e0200711809400022a8103140b010b1101e003410094050302da4082000911040511000c441041001003400406c43c0b01d042846a0203045654840a44200e0108180314142d40d001c0d88003201c01e000c0c40c0201c1d080c0c0042454219029040500282c8450040c080c491409186405400c0c43c0c14030000caa5500550b900003031f102110403000ca018042580c1c8002c0419644815a13040e005400c400740d07040c00b090300b40e41c200c61030450301d5040748038650001c0c0005a45602e072002c0201400000340d00210741c03425140c81403072640c021035221030384408140c401d0009100c0a141480c00544413a02515941200014580318500c82503d03a521034007880900844114025440411394107618a00320044c40c1d522082c0c01300781d800440d0b02c0c1e40135410000b04a805980c00c10452200c559091409105c044600e4141047e8003070914040004d21003e815446202d80d046040740e043d2101c242c1007004000c0144030781c2c80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 645100278 1250 645099028 645099047
    0xb1807090b0a0207051207031122020a0804050c030703110103021e04060314010b03101502152d04021039030e0f0a0b0c0f0a0f0c120c060e0a080102030403 68
    0x2030140d201d86c042410402c80100d43da03401d807070700b008098403070340780300014440c0c100303500c040000c0302c0b50000001d101c0800050004024058866990049a00b450300309203050604103003038280702e81e102182c1000098440c1020582070300007400d006881e1403554070081003020b200030301c3d0301c1c400c0c0000501184c260742650040800b61a03511032404680c0c1c030744103c1c0039184010383e4080244079900074200400442c00b9010f4030f507040e25106075020003c05c00d2980042a0080c3c89004600610403242020500a039801c07400c0403550100c596040c3c1855000316000c80100d644020800c100c54040c80706900c08882a1040c6134680c03902c454020149040c180760b0703000301c0b100c1240042c0c4044070b009041e02e051420080d004100600700d040c5a403400250149036403001b020000705006011802d8900c00b41441180d031814003840714401c8421051426603030f4039030240c2140401206041d600d10204040c1c843c0b081c1641c00314140484440d558100050031482c4540c0900e045600000400040640c8001c840 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 645101528 1250 645100278 645100289
    0x30f0105030c0d24051e0c040b0904150803030f04060c050406080a0b0a03210207050f1c02130905010e061e0f0c09130c0f05180f040902040c081602010b1807090b0a0207 74
    0x11140f40c44011f1079072074910403032140d24034004080c0407101807440c1a9220b5140d4410344e4202c10359a942e0340c03c58609541007201c1d0203c003610380600700000e12981d402540c9440a9920700309160070305100020744440d901510402800390307a010316a0700ea45413108040e0140d9040100c1c8040d2041142c0d0404030504d00e40c04403401801500c200240d0760030911480b02c05408018200341512105208143c22490209000d903407050340202d4044240310288a0031f20241d0151001103104010300407210b02e0004c010340442c0c400f01500001a00750361000b050190003140e0000d40b00b840742c0301da41c0c51181e10b0103442207099000000300868605901240d200b0890b803211601c440e203c49507581415030791360054900f00c030042490400c54000300d190135010000c90503070081002919003910340108045a807446001d40c0070039040414490f0864402da00c62450b040c491000780700d004500f502040d07030f24092a841d001140d181c8004100c1440c003509441000c2c0049111a9440e0010320310020344c3c1e0951845174 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 645102778 1250 645101528 645101581
    0x50615040902010f26010b0d241a0d020a050a021b15090d1a101202030a48080f03160521030f0105030c0d2405 49
    0x12540503003403074025010095016150407840c03c1804009403411500d20000101c1e000f1003200c06207868100441041c0609581c1c440f042d151440300c0c1c800c80484a281c10301d011100c08080c3c1281c4180f01d00310441c0d0945d0303010ba0410740312041e034603280320190007103442410440b030010a40d425015405400f0300160001030742103079086040f40c095006a0b41c610102181c00131500c3c1703e002443c0c05194010020381d20b01030642c0e1919111501c0b24404912040d041002943d180c0041c000c002d15003202810251174000714102c900e2510303034000b03991088025001095104100100c0070416681c410041001140c40380ba850040040c1c1c11104c07072034010030078000242510350001f003241c007000984d5815135098103006500e000d000174050580b441c1c0120741100c45100b008000c030030010b86d0300789101081c8400d910030340e141d061581c240c15440d2016082940a070f84404c40301c1d0002d68030608a0030240c4c0d008050321000546010300b0380294952a405c5e103040301e0805e0148072020042c414001100004c8180 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 645104028 1250 645102778 645102811
    0x1020a031b081b0c0c0603190e061e1308030a1d01020f0d0e0304080f01050604050a020c03030a0908130f030b10050d29010b070203070f08030708090d0605040506 71
    0xc0030b0b10b02c008240c1e0030a10144018002503038901400b001002a07000e580101c83c4041001e000003121759008032600c000042403036100f14618884c502a1141401c040005400030b854004071208400c0204c080ca12028111200411300e4402c40c4017044071608c5d080f021080c4d50b071400445620150139004a00590f031b000d0b80c810000c2000040c402c0e20b040d0004480000c0c038001e0b07000c2e00c140c0034151300301c04d40c0850301040000060400080020b0601e91019800103d502e00c1d040307040000b155002040d240f8110300401ca0070a8451011040325400180c10000140ea0146030604e90120b015200f02110403030f000d803a0200e14038800b03a000104480c0700c1c1c544000c459942c11684040b0099610401e600001c0d03061074100029100c690342c2c0c1111100b2149540a2281d800c9902500c40080e40807004040703000590380c003903090600a840c0038040360360a1540c103e00c0e18210f40c0c1c0da44642c0c0c00c007a000c02c20210742020540d850704900d06507550406014452401c2900b80b0130344602c020364084044024405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 645105278 1250 645104028 645104081
    0xa031a06010504230a0503250b03010303080c0d0b1309150204030b07211a190312030b13060b0901090f0513020a02010b090106020c04110f0f090d0501020a03 69
    0x50031542521010035214144c00c0e1281850298a0304000c641584899404d002180b0f50300c0400001d00c02041034100c41d00c29030700b1090844071030b42803a0000d0100718402c000500c0469000191650000120b22081d559121303090002c80003800300143c1309a1000702620441801070036078001c1401c4d680a06400d141d030080349c00180c8100d101d1444000c002401c450001443e031350160450305441c011400c40c05c0307181b01d40304240c0021500d00d00c410458541298140c4040b030f0034200e00c80da441454021041c8a06400c60f11507010000b8480010001c05446009000703d948580c1c0e403003021242000c2052240d2500d403011104a60003c0c0c02c0030303001681800e400100c2c0307482c802032002180c0000e000803a032160300c505101d0181d4007070102e00c0150b64840c003a04c12240c5540025078000e06155015101c41c5c0070071810001921a00002420340f20030074000d1540e2a035180e003ca9164905880c1099698000ca40220b41a050302c4000900503502c0811010166500740d04180f00040415168130f80b12180715 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 645106528 1250 645105278 645105287
    0x1a0118090c092c01051806070c060e120d0b0316061b14030307090614121501030e0709020c0730060216030e03300a0e0a031a0601 57
    0xc20003500010309110204a40c40032907011280c01140503804150189610b2680742901c01038083c0740b105607543e07000300f0410b0b500c910310102125101101414103402c0c8050000c01d084101c95029151986d20b450300300c8940300811200c440c01d0340d0000c565444494a62802008007d54000710340a409280c201c05e50700c200c02c0d14180180c6000d07803030b01e41071100c2c0065156420b900d002070843e44c096500c40940e20100c420009035120f404c51b0355a4004090815200909144e250500d103020750100717200110b0b00c4021882941d80c0100030b410721400240c100320049000d04890020481c460107600c5011031030100c960010501d44400c441103604041c0d0324040d410300442d412605401c0340100d00880403100c2c0410b14a800d095008003005424107076911421203d040d00154110042002106006511705081c440d02c5643c200c07004024905201104a030b02060006071386280f0150400520004414020150030100c0700c40504000b41e03090b107a02d05450300c1d64650302801000c00b6808005445907214 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 645107778 1250 645106528 645106541
    0x60f1d150f090d080603030f041e091b0509130c0807080c041a0a020f07062a0804030f03020102040801060f090e01110406030b12150f0f01060e060706091a0118 70
    0xb200020200780850540896130880c01810b442c1d0f03d800208039642d0403400c00310240020342a1007919a204900302c5903422001500780c1e001c1d40c0d006050041c444040540c100011000340b009041043e41c80c151840003400010a480184c900c00303160034520300c0b80c00d900c0350400c1d20441d03607610749100584130a0602d540a01541c45005540d05803039a044902c2c4181d8000761070108a01e0040f01c200c48800c0c62540d0030b0040542000f00000c140342d107100e05c00210740c3e00c1c7d41150300b10b15150000c0e0f04025182c811540c071503400040e01c81420404c0f8101094400d41c12140140751580081064680b10948483d01324484d10510398414101a429a8001818072030300f40701404002c0d49a14182c940081900501070071810150b01421070b800391a0301d1762007481001c025007461921000c4610f13121340400c080c00d002400740e02155052000500209400c800541f032190b2003111100d8460742586454400750103e00c1c401041e10003400c0000021011404020f4162200ca8403c1501c440c29080d440c01200c01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 645109028 1250 645107778 645107791
    0x2b05090d020105041e080c060411130608151e04050d0f020f07030210030207080c030d0c0c0c12060605180702010609230403090e13050c040b060304060f1d150f 70
    0x415080080004480d400203103170342c1c0c40780b0706050408018104560520300211400d4805201c100c0c0183e06030306e00403c1300c0003440c00d140f82c10040d06052070030003691340741c00c1d0000700088058107021039868001d8100c00b8040c54010f0f5040e00c13140c0b034980341498941826805030300c0440d03080b04002a4407800459200b0700c01d200800200f00d440d1560702009181320609040a0038158208814404205c00800400b03581007000c00650f640c0295a01410498002182000410074452026000540124110360440300000e41d502c40a210500f0604010043c030f521643d030018060181c10001e50301e8000640c4182d405400030001140d840120900751014001d50104407900300b10300c0030040040c00c1350903030002e0003031801c0d1501c6600c541da401d001a40a5031902c0030b4640840285042140c108014110120700b503405016944410012584500000d040146104d48403100d1049024080c0e1010b5440d80c80f02241440d51611588080d4445201c0301403541c0c00c166040c00200440324900c0407078010403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 645110278 1250 645109028 645109043
    0x2030a020103090204021c0b0f120d1110020a0c02011d0319110a080718150b0d0912110f0a050616210c020c01232b05090d02010504 58
    0x1840d03801100145541c100407039109a0038042091072004080d4a14003c0e0801540012072424001c20045824880c2c0140c85c401c50b1008018900d49001040303421000300242080d00c404010800002e040913015215403c0e051700c041150500554054560340703146000781c80d16034802d28013181d100e1680114450f580d801d5800f62268001034070b9010080340e06c603400380401c6074403c4018800541000c840c0da000100a60110209024100f419203803c1c8917030403d00e200300f107100c0700d0421266088034288a280222400824007405d60090b9400c007140fa180d001416217808a40b8034000f800503e60740307d80801900c80c0544500500e000010a0304980380c110004081554038080d0310f005102081c0c0e901001c212901c4408900013001400100717050007403c9010078040034940b0000d291103001e4404c5410030149100c800300d486e00e810b002c641184050100750b55a41c0d8050100703804901b11850b10210300342c0019000f40b4604035981b00b980902045420b861400c00421800ca00b610401e850140c04031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 645111528 1250 645110278 645110293
    0xc07021027050627100801081203040f110d150507020f060c1608040b03070509040c0f0801090c11030c160510052d0c0a0201031503080d0b0303130303051e04030203 72
    0x7581340210000c4416000e25441140c101c2c0801085d0170b00039550b0594041103039440188034154050007824601480000c500e410b618140d121240340c3d45007110050501d04483d0030009280c2c844a8001c0f01094000407425844002408400700400003268135400600600310710b00301e0038002040c002d0003100c031500e80a0074000d8901c240012404d0302d0724201c03200d034000c11001800c28124805075104070f180b83c88158584840c841408103642c824400300d406c101d04030010b00c0e1510341050b1454155126290300007040c50302d401c030540b01e2100c695031040c2c0f148030101e002141441f000649a41400f0515080c031000c9644030f0500c5000d0302051000d901185052002d440e131400c1c201515214204001d004046007050740d1031094903a80140240b0445800c10143c6100f596007600a120001039403040c2064024556103954809015007040717200c0240d1500c0b0b40e08070b140d80400658000000703624407030310883e55908d005000c0340d02c000c0304a20511800041040101000c0303003642d0840e5009000750001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 645112778 1250 645111528 645111547
    0x150f0d11100c05120f04030c0b041805040803071218080301091b0c15110301031a010b1804021612020d080901050c090d24020a03050a0515090c070210270506 69
    0x4c0e8020101820410308244400800704500c50b209100070700d0002e0b5203603a0b5505040c2d038080c071442c8081d51444451300300018000002d6105040780c2c0e101c807140c070b0315044043e800c0781c48001508201400c0840300ba200a42c1c0700074484404004c604a0300399000030005108034958202d01103404844440209040d00c5d0b0034004610292101d1086507001040001c43c1000e0001500791078000381c200b921200a51031202113400303146a00b15001d003c130340141d14107111780b44001201c4510a05030700c9000d6500803404a0381c0040003001c0804d44c07540410790b40c56024102038000d50b50703403201e009200020710110100d0262a0184906402005000b2203a40750880e00d02c103000310728031408000c0f240705009008152401c06070b01c4904030790266450015a8441d088080182078600182000b00070078540410b10000d04031300c1803075180100c0c065071030000c036649049a00110703009582000e074010981c12000510b0542c40801c00c443c0c030700c0c411070307251310141100e00b07040c2d90410502500e9086242000340c04003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 645114028 1250 645112778 645112813
    0x6090d050a050c070f0501111501060e0f100513150206042901030804061701050906090903070524011401080c2505030903010507080c03150f0d11100c05 67
    0x804091414607503e801e07480303090140340c000703540e00c48072404204203014400b0b503a0121080c0003c00c0070314006c1200030754452502000d41e0041c41a40c00340119010382081d19142c5070002c02a16a001707018000c0d811728214060007545c0100140b01064103103e6000c150b08036407801135280300116500030106603855030b9850f544182c84070354104900003400741c9101055405002c060103103100c1c0143d291614608075007d0700e511085011030b0020b000c00390042c0860340b102d042e500d6005508441c40d41c2591100c840b40781c114459102c02404601401c029482480780480d00c503081482180030440d2540e99a480c1000c41d111244100c038005250700c030105016800f8032000c1e01b0090a8040c00c0e51a080002205103ca040040c008403100c1d0030100301d44101c0d143c207105e03680e0300c0f90640c100440355142081a141541c0700080c000403130100f01c910004103548402141d0402040d02501c0c9000402a505220b4114251482610310484000b002042e405200c1d619464506600100610502070280452030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 645115278 1250 645114028 645114037
    0x406091b2403140711010c02030f070f080415030e0705040507050d0903030b03250504090203070909081b060a0605030f07050d14150a0501140108010509060a0f0b040503060906090d05 80
    0x808264503405030003400160314003d140203202c2c13915120b1420b044d510325182500e8450f01e070f9109640081c01130f403100d1000407003140c42030f80c0d00401280c1c40054074500f4001d02e0080ba00311340b6200c804010544a401d425600c60880842204116900c3c160746004110698104031480c81c00a1400d0040f080d98050b59040844654405e04003c12070040303020100345029030420900010500c3c201048441203862244000a405c003500d0034000c9600380d402180e5601d140d0300c6100c0a6a0391422a6018001050161000300c020a00d885c0707041408500e0740b50b540c000540d00040d03007a02d401000541c514002402d10308015496020b8005ca070b03e40f400300803000d5110242643d880c0e4010804413100403082c48016034410400c04141c455040041484044800580211000308042480503c0d5aa0010f8603141141e000b1107402c00e0070380d203220101e401a03005078848843c0302c50070b03203011820b01980750140003644c4003542143c10a40d10628090307a5400d06560102c0ca5030450300d0380c2c002c024410070042 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 645116528 1250 645115278 645115349
    0xe090405011e0207030801080d02030712030204050d0c063009030c0b0c2106031c03020d1e0f020f0f1b060703051006020a0302100e010b06030406091b 66
    0x45600040d0004081924107100003010143d00050300d000b0150440e09407409810403400601c4011034400303002e9540c0c030a180c0f0252030000401c0401d0103040c442d804582c003600c00502880e018411510b07111000708064028000441c982040ca964003512141c180d02070b01029556005045031103841000c01030110f00800d1301045404050a4040b03500e102c1243d0195010040c16980c903080198040810b840d00c01200c464103510009022440d0380000d00c1c1c035401d01c41c0b1103072240b025100c124290024480c1c04130820307000d42068690004c8411041c00149a250404024400d000c005480a012441000049c103a00401881400d025410040141c04440b51208910a6039020140401d15164040320b8040c00030f074070743c42041185403018803540010310315800201183c0341f0302c1d9406510303030707214250b4108280d0750788610401001094204040600c0c004d0011952414141042000f40c420002c0540d408800b142160040e01c01e4601d0410031190407941c10321400c5144000104d080380c000b400c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 645117778 1250 645116528 645116531
    0x92f0906070b09070605030403080610170a061e03030504030b06030304120f05010b01140a08061f0206060901060e1c020a0513051e01050f1c05010627020a0e09040501 73
    0x2156400c0e20355100402040740542141d103194940890307154a080c2080e000102085418024000040d800181980d0059400c41d1030b0f0722850150141125282d1850b500d48c0440d050013404c1c41107400c01c69002c1425244c035104050704102c2200d0201d28068807a03c80100068405c00003080425490400203420410080c144c030300c0c00d5514861101d601040d0307081907400103480d6520740f00300403091242c0c101c01032080c20080b00380680c0e01d048038550b000c0d010481d000e102c00840081d81d1070361007070b41c00310300803c0503c0c220f00204401c0c08000d42c1d0342c1d401c40720680258008400070404602a00040a8085000700005002c208004014443c8800c0d03044c1260445180a408a003596419400440780d024108002403d8070b0400505074540802d4034081c0284841c00d40140056218111620000101515884440d03921800501a001e45285000c0d181d13518289002c180030405130810914801d0389070001e1955004092000c00704d1081e1054080490301d8402801200c0c180724080961180c000c000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 645119028 1250 645117778 645117787
    0x1b060403202116050f0609010c060c0201020c011a150c0102130311090f09100b15070303061e230f030601060306170c100327030e0a092f 60
    0x41503810032030112850300d040c030b1880b882c000201d00b00a40d006510b0b00480315010640f5100210f500c2200e403c010303e00800f400110440740d64050071483c1c00c00b950000d006c001d0840040c10081c000d420151400d40345508101d6803400c6a054044690700148004003c480da082d42c0300250f803200d51002803641c2d241d540903c229040301c4400b45420008502401da808290309000c001c00c1080c0d80000e008030120300240043c403c03401000164039501c00d03080c00c00020b46070460000240c00c01e02c003040d1800340c02d000055840c10981e240d00a48202c8003650183d20032130070791101c459503600403402118628000c0c0301e071420007900301c5002d10360b08200c05403401c020001e038400840d04054007608907030046034455104014100c90102d0791080c08280b540980303506515a0700007503841058a03859410103450364174540b50900d4115990603038012189078445941880d02d00070700700c081142481c51142080420005280045000716041c020b008001e1703106c603284982040c69051042c10445031807850910 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 645120278 1250 645119028 645119093
    0x70807090f08150906091509100216260d091a0403110c0312030f073b010f0c14030d1a0f010314040f081e07051b060403 53
    0x303408041c180b0340010b0580c4000450248064610243c41e02419600c400c003004201d0360080f40f05800702c40050201d4009807140c50099103002c550b5040341400c18800111920482c0f2241144c406d201e100e890400748a050a010146c44105524080049064100031503050302d941c0b580500707c002d114603541065104209520072882c04101c400700c0104e900444c400c00707503c404200c070311700301c103011002045800710f500341400d0180400f4040c040190000c0300490305c401e000340c9242d84450342c1051070800c1c01c2c0740b0601d0106074140340c5c2510780c0000351102c400c5c0d9441d4454a00604107a100d51103c00b02d103034503982c2c2c202f030f0440421800041408240310000c000ea11500441c40207900580d80c4241c0390b1090000c00c0200c0480401d01810716103009245e0f00c51a40200c0043d90042d080030003007100442c1d44c1045211407250912070a1140402c60491860075181d40c00742600340d000d0011140f949918102e06042c03d034500e1802c2d030344000140820400a402908640503100006080d1649001600c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 645121528 1250 645120278 645120299
    0xa050a0f050c0a0305010b1603030b0d020301140406050109060308040e070c060e0a05061e0c0d090b010303080f060f030714030f1207031701050d02040f021c0b0f0402030c0307080709 80
    0x240d07242c000300d090014554054661601945024241000c042441c0c81c1011a0300180880030305801801e15850f5100c030112a170328007449107007294000d00244003259542450700629801168100c64540c0380200208070f41c02144a05c1c1c0075240c0c4408403074904ad043c1138641150f580300404050070400c00b00302c06000104240120304500742c61a0003021002100d203080d50402400a00c507505030f05003e407070440e071003d6250102d0f42000c042c4ca02030360358150a02e0060040d0030340382c4c80030f0044030784c1c1c80c0000704041d403000352940325010700141000c00e902e80d0070030800c0840303100c0c0710244d055000d14070902419040145118014100074211003003886840541410014030380b0a900000c0310100d2920141030b0420100d038860350417807150850640c1080002a41440040e802900407a40e465000600d203601d0303412108941c1c0700c9038805a0000032441c490b0041d105040c0e404d801004820b2600c06e490605000341c1c2e0045800c81034040c01c580c4c6104003203948500080442d810084080000520b602c20b5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 645122778 1250 645121528 645121531
    0x14070609060e060106020d0c021c02010915050d050c090325031704080c03070e0c090a1d0103050d0f02060103060b1c15050f130f06110a09030203061501080a050a0f05 73
    0x2c00141c40c083d0314100e406403c100c910070710001400a03500c4114016074521a42818818030707440c03044454070017400103e0301580310707412103607030002c100c1541c015154024014000c11800daa9060055903620400702030300340950800b0320b4042c0c1c80301500310079080d00c08410300c0a114010320f0b907008c2269a52145a44441140e0300c45800c0706d00000c051101180900661040d17031010307802801074514240d5044018200180303842031130318001c61517048a61300d1040c1c840042000d9009000c5049160603083c04d5030360284401c480e40d1258100150f1440d018001c029429030041d0050300c00c40c2e2860f124000504150b031181c941c4805100360203500b8940c11150404124040c021104204560402403421100040e00c0041c03200b100000f081940c40816036607403022503000c21206001c0300c0da0314001000d018554640810684d000c62440c078403651140140d030072603008604a608a407203501d03071000b42e583c0515440c0c0c0010346510018501d1085900700700d4000a0403440001c250080f0071001c01201e40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 645124028 1250 645122778 645122801
    0x1109040f060f1205060a1e0c170708100608040c0f1d0112020a0b0a0905030d021f020a0206060d0804090603080403050d0f0203031f17030318060105011407060906 71
    0x10749450501c5014441880e10025046405a62081c030016032183c90703407582d0003402c0200e15920b03030f00c8110714a000003c509a07040e14121040c0000c03510020b01070000d00900b54081d00d0304c1ca83d40c0c00074403210f1141c903009002d00041c80405400d40c1c20981d04840080c40200203a6414007440d000181132403440ca000401400c40b1007410381a80301c1e0680b2985504410ba2003050244c05c041102c4025a0741e0890280842d0680002140e5030141350b207080e1011101035000c0c9600d4040c000071104c03101e801107a55046002404c521012101504442030105d000300f0101c01c0050703125a0004155041100300741c1c400c01d00507401981020b54506500301030700c0d965001141da514011030100b041150070841c0c03e2150b002802c1c04110b5040f40a8002d41e28040142040c03114644001c80a41503007612060703801901074400303c284020f03003110403a642c07580269840c2209008501c0c01c0360f8a00008250399068840c140d4480a8011010040c42580d80240c2001d076001581c40b15050b000880c1031099034001503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 645125278 1250 645124028 645124031
    0xa0510111209100203090f0105160f11040b04090c120309080102040626150f180a14060a03050604320c1201020406050904020d0905061e011212031109040f 68
    0x80c1c880c1c040c0f2885944241401c01913500a1200c507040e030340d174106022440785007882c103d42c6402601904c07905000c0601000b9044409103144034060180c803041d40c4000c04000d65007404040f1015080c8400c440385644040d0030307410185424016603480c454050325181c060f2401d40070140e100d0044a0890b449903001e240885c00c15120000d5851401c003811030100c2c1c480d00c9002c541d141c9400c004107503100807403213544503c100b12125542543d4558130001c1801ea0499140d80e14504075800e40b00030300d407044160380142e012500280d11860504082c034184c0e58098040c0c101919184d54038940d080b2404c000042e400040001020301f02019100446402c203120000d194960b040001d2040d07107100900080c0190340100818005250004112014250b0a8800603a02c14900840700014071203120010010b02900050103081000c038a0513042c3c42e18074411442c40e50360390b11502d00e50690401401001c107102502000b5405000354401480030350f200d03810a2605000d000041d04640f110040c50505d903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 645126528 1250 645125278 645125287
    0x10c0b0f070f080705191e090f210303050c0d1407030c050f0f09120a1505010f1a0a020f03030a0c03060503010e0304150c020a0b070209150a05101112 66
    0x56500c880e0b450b030003072128203008150b4102400014a144240d400003144c1000d08130044011503c40c1e404148a2048070002c9103e004400100a005400501c00c02500412200c40401c001d00643d000302100c07c014032614034410215503054000d048000c00340102c0c1c0506201d400c0020b05140510f2025041403056400740d03141405015044820f0201c1c10340c20003000348800d1103d104110200c8003200b0305900e0107a121010080040c00041c038140b089442400346240c14000c102503010301e000e400018580c144401e03a200d07810541c0038045881950742c00940c41d102c403d0203200600c028010b140440c0305071200700204100071403079640161100d400c60342d40d03403070f441410303951520803080900b600314001d0110204524601e50749015501544001c0e03000f061900281070700541e00781c40d065901528010080ba99444000d102c5d80181e001a805681d4040c00070302071802003105861030000081007100031b1810714080c8401035000e41c41600502102400494190a08202e440c4001c2d4155907860b60700d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 645127778 1250 645126528 645126541
    0xa02031b19121206060302041d010e060f03160f0305070902090607030305130204090506090d03050103050c09072a0b0f0402220b03031201060906050a021f06050402070506010503011104081b010c0b0f 87
    0x7101d540018889d0200c4251005000392100d4251454200400310746a140032004a80084e041020280c5400300386190710380001400756604000900b1680140140e501d01caa03607944100c01c0e44141d85046600903001c20a0b40c00183c0203a0140d038100c07089a084020a44c0503501080032100c02c0d9400b99066032101d020070002c60004c01810108a8281c80c05100c03650bd59515644e840b030311360341581e220b0710b0394000090b120f61181000091006003440d400500300305289404003440c02c20041918601c800000040000b0030030098940503076400b41079100d008650304c203000850865110304a10081c5c0f110b805041e5030703a0400242503c2e981d04003050040703515204e400381440440d81c1c041d1051100520941240075000700306441c0c807001c50900ea5000c41140e00300700008011395040320782d00920100320003080c00340020304176050718401d80c000c200e00d140c0030310301c4859809070307104034000b943c4009414000750080091006524006051140500e82c0941d100002c241c2c040b141c3e41281038414007007042 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 645129028 1250 645127778 645127799
    0xf090b0a0204030804030834020901060f08060f0f0a0314010509060106050d0b03120703050a080f27160b0304060b01051309050402150a02031b1912120606030204 71
    0x2008440390808600d0a8655612180d55025a10000d03141240109045081840360312413540d0300311035012811064540c0004403901900d680b40e007079025080c01d0303001023402405075050440d030300059290040e05641d0702080003d07030b410300c00c012034000e900a08a0191500d4100c1c20070007039403007510800e819502a02c0c0180c02c4401c0184501455800400100f00a0f50440110741e40300c40d1840c408180d01504201280c542034240c94006a00d41000075030100740b55100c0060305a041950b03071034a00e9130310382200c0c2e00c2180c2c00c151040c500d000c40c00d44554031000320f04000d5003003c0c41a2030947d0300c4818111030402100240d80d00040d4811070004c1004104540ca126007249008242031450619007607040b80c2c1c40201a50050f01089030741e0b9070105003955106c1540151b00350300300d50b4180d41c81c450a40000e4503034000b00d1500c0351415414407510f81e588001b20308500000d4544407400d00355801d548031501048190120702003445040500f103181e803240c03409000c010304590382b80565503a242042c44070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 645130278 1250 645129028 645129031
    0x80c070507241202340804180f060e0a0c02070e070c051c120905210c010b0f03060a0203100f0303030b0117091b0301020f070b0403080915070c0c05040f090b 69
    0x1a0284100980e001e40d61040842015000c400b5041e0120030000301042e10580400b010003030041c0102050008c0c4c04c00d2010300e203602407103401e9001d0010000d0344907100240d81c0300303000785070030040359000141074002d59030702c03100d000c0c4228811134009075a0b804a4500018059410070001241c120320101402403c1011440c1c258078100800da0540b1410001000718a641c2c01da0101c040e1036035900c02c01e1180402501c8140324a008104401d0500140c041e40141d2040030300391050b50800300b01001c140b505800b0300a074810301602412090341c4a070100e000a61008180c10f00c0c55203800004504800c4580d07021010713502c01c1c0c90005404d07a00d540003420b010403d059012070340d2049010419440c0c400700e91411600c010654002e50403201000180c0a030007451121401641e02007070010500480d480d072140258040e8403944820b40303a0f1390703003251918240d40c2c50555218502e80819086031050502c4030700f5500401c000d448154840700000c0c25100c56886061105850b002c4c03c00502c00c000d01c103c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 645131528 1250 645130278 645130307
    0x1b0221060115050921010227010905030312090f060705120609060102030a031e0906050a060608070516021f1d06160224040b1903090201080c07050724 66
    0x1480b600440c0900824074403034400c8407030246044400140318500e40015074400a00328100940d1a10702483c00782140b0710005a040ea03c138885070202d00901c0d4082c3e0506410f42c0c00140145140a00d184151b4840710009003210180344503400c40c9a40007542400402c6c082c44581e6221a40c459482d840001842c0b000741402c1e00c500c440405000a9071f800004450303198800e414042040404450400280c10ba802c1019100c1401c1088620401c4403d501c00c034032452000104100c559224181103800000032143d1102141d0108807403001d81e54014540045070f44010451400a01c445140e85140100000820003003075040c2d040125203003603803050000500045d100b0509040707001c20701c0c0074800194034010340074000e5504103512901801b030f90440004401c40c1c02ca80e545940d402c00b2440d07a0710002003102c1d030080401c0c40c0c400a61183c050000b12a80580d20482681c90f04e020402c21948242000c840030b1003a414000740d690391000d081000701c481052110850744030304102038101046d0b442c20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 645132778 1250 645131528 645131549
    0x81b0c0103050c090d1103010f0902040e030a171b070803011d09060c0a050708070503070b0a0501030803160302190e010e0a18230a0204062d1b02210601 67
    0x10000003e07402c074142d5840c20001c48110300003aa040c281803452100b07540c90b05402d5400d28800c0000401144c011881e0707244243c604000c4014820803a5890740204d1100c1800070f10014100b450300020041103d820540c104e62540801d00341c19a00c500715070201008845085001c00100708050b0491280d00104500409403102d81c9040d00c03940c2d4407400e004282c0002c8610128004100500c244281c4210582c4190702c603035034000324181150f0760b40160008032064102400041d10380405800303140d0403070f81e000c0611420343d10b031104d10340001c441803100c2804156003400307040c0c2d68004104c020340c2c05001c29180c1001c1501c0c440c2c0010300c0040d1042155000f0024280308028000d40c040d80d0300207189119100140d68841220321010b04041000034115280419061107201d24243d40140110b54064a805952045010340c03140c045400710182d521708204102803406241c09000f8150032408109a0056204069030000780356489030001d040d51122002e814800700f0200304121070241140900 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 645134028 1250 645132778 645132781
    0x504060b10270302063c0a12020f0d0603060506060a050405040c0519030f150b0307032c01060504050c280c14030a0e0604180203060d081b0c010305 65
    0x1400303003046160302c180649056100d40c0101c50704400304800d00145500600c2190340d42070280000350050801c01054800901c221105074a15030004880d215084a421b126410100c564030300f42e0311098401c07400380d0100d07000c0048601030004c40000301070031845100c0c0014444c2c21070034044c0495000800a82c02403604001510f00150414251402c17541c040f600802d0110100404a519004600b0041d0f841c4041c1e1800203d01e64054014a99011042c20b041010a800345404140b404443c8111110040d0800101c1d80303681c400c1e0090035006c00009005180305c60310f00011030101201d00b40c410010707551100240a141380c5801442c0d0040304001e40103040c28a00c0740442600740d100118140d141c04090070107503045015030812401d040e001490032003861a4183d010b0340b01c0d405402c540c1c00145c201019520b03c2e00d02002601c090701d4000715009000c41607200b4060082d4009401340f98050030001a800010301d43c1d800800420807102c80f240440d4101160742494104402c503054141400d080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 645135278 1250 645134028 645134059
    0x20109050c0f061602040b0409080304110102070303080103032f01091a15010c0501113106090b09040603120228030215041b03050d17060d0602130909060504060b 71
    0x3c0641d41c1c1112003e181050599482c800580203280c0910352a40140c1445c85034003d005a1070041c0d07110714000c2030f4180c000c0300f0316001262507150b0f902008003c2000b0030014030100f84030f400208082090782d41c207546440f100d01c0000715951001030000b14a61b4492600c442003100040d003400380491510000300c03c0b41406c60509501949109409040042c00d14060341131000035007201880d041905005651240700307140d40c0b503404541404014544540d01d0014250744c2104c0d030780c8000c40d80142c0d02c0000d054207000b1140d0140c0d000b81905503200317813900c0d00400403440070418415442c01c0b81c1c00400c1c0140300d40d03200015036410000c2074100310305074019400201e85c001c038174182d41000c41c0840f21740990343e9140c011010b040c49a0766980e07005000300e0201c02c211000a40100c19000c503107440464011000003d200d00c0001c540e035541040600c13904e00001942c075006002841d040da0301000d042a21085440c0c1110080765040d542d2035100c6040c402408040d01c6202c0303904030159602c015414010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 645136528 1250 645135278 645135289
    0x20c160308040f0503060c340507061b051018080d050f07020f1504020105121302040b0f011d03011e0207030e0d0308040209060f0409080c070f0612110d0507020109050c0f 75
    0x40c4220a00320a1038920ba500359230b4103141245c04c4682028469050062814074607596100f03801100c0102d54410341c03c41c000b44501078202d41c01c03588903000b4543c00b070240444034090f01d4400031040d91054100309600000300840c01511014554500024181c038040b0103c2001c2d0001611500654015010f504003440c00800da0300d00a8080c1d58080360b80752907501c0100d4440c443c2c6801ca05040348003805002041d01040c40881c0740740d00842d4140400d500701001c100d0054580c00101d804200150140000210717041c507800e4000400800001d00b401c09041041c0265031600d0481745003d81c0001c400c3e01b0141c100c12503421188041e50410490809950041e040b240050301c00b0f48a0791301d81e070008001c0d5540001843c59080d0281041c40103210502c0c05540750f400000020030345004000b00401c500c640c49084070103c800076030fa081440115405008014034102c4140f400d0070b1400c11200e46e1203a181c0c00380d580115102d0780006040012814401e00740400d4040c014464a550045124140c0d1203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 645137778 1250 645136528 645136537
    0x6050c0304201f0c050c0108060f090a02160302150901020a0807030504050f1009060b0409110d050705030d11060a0b0105190306080a0f0213180303020c160308040f0503060c 76
    0x2e00c80c500c0e4907001c07100042d204100c0d410f207015070318002060001c03210780c06408440c1141c800c03400c6030038207072400006486541c0102c5029810175050310f4641c41618102214036082003046400500e4103480700384010407620074403800c0d00981e0040c080540d207180030551a03644000b642c0001c5060000485000f419080701803d000201625140894140001400340c0358900300c80304111440601c02a00b401c02130002210269802840e00288404600700f50040c1800c56601240c90006609400700700000e01e00c0100c01a2050701c22844040f4042d20700308500801c070310b000d80710800c25403841d0b91705614244000308032144250400203030301c0440e40c00609840020310382007030b13000344052003800850061009601005907880b0343d50f030043c1403044408100030a80d009540f4000759015210400c0d081c0e42e00070b0b01c01c0b00d460240008000200c0c1c825805030421100c00300645d000c4440c00400c00b0002e411580065030340c03110000e0100061017102c441d420003020290003804c000d1500521070701c040e008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 645139028 1250 645137778 645137813
    0x5031501030c11060a05150301020c0a0224120f07030c090b0a0c0803010b130501020f0a0813030609031205060d020114180312190e06180f0402070503030406050c0304 73
    0xc580300b02da100d00340200382180d040300440007100c12a24049200c0800350100741c560204d62001c100c0021401d042c18021110b40c40001e00c005d010307000740e550030711030b549a12210160400741d00c2030031b11300102c6411008141d1203510500c20141810000021480440094417070818945054030151105402050400440d50103009071600d41512007016100c070803001c03000400051000001207081c4000703a003d081c445211600c000d00c0d19846500680e52042003d00000d0607038070020490001607400e400402603901202d070094142039599492400351202d41c0006c8010920200c140c1c907941125118240d80000d089482c918052003d400181c0500d102604035030240c84000b4105582e01d6040d0080451803a0103000c64400010b1401a8002a0050100d00e081942040d04043e01140b01b854940c030401c0000346a1443c04100341215205048d0407203c0ad80c1108900b40c244c0070a03584c61003d03102c094081c601540d901e20349880c00030219840101403100295051060001143d01055100380d41c20b03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 645140278 1250 645139028 645139031
    0x3050604034d160b0306031219111207031202120705040f0806010b16020f0406060905040e06090c01051602030709060e06030105061003150b040902190503150103 71
    0x101d4281224612466002e00c80010124a081102600c1c044030b1055880b90301000d888400c1a0018101c151075020040c034031140440c00400a01941d2000350040d50081e8009040b580081410328071462242c01c8501000040c1c5000e5102042003900078031440e00c0410f05c080605550205202e06080c0d5009070751300641000380700741a0603180d80c00350b4110b88018a5002c04c0081e189031031980148990300501500700c2400000300b00040b807207400104181a0755001800b079003410080c5c6030303082c2ca151554805036807210b0b02d800094100d4840b4030400c0068030709580c40078800f900744000c0c0829205458501e1080303601200811000c0c034400703d000c01c49e11800740303402d9603544440600c605a542080c0c801030742c1401f03032450001e2801c0d0709600c448110b9422200d451440e030740b42c0003010f003203440413103c07603410200400c0f1002e902842a4410390742e0a147c40820502e150b11030b6000c100b99001500180c01d03640d8001401e4845e026804002203c4242624000b842c601d040700c013403031038a48007000341410715 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 645141528 1250 645140278 645140297
    0x6151e0c0218090616030614270c09010908070f0b070c0f1202010306080105071211120a1a0603010b070f0206073207320303070503070c0608010305060403 68
    0x10341d240b1400c0d212000d841100034003039050001001d038031203005446240902d00c014a500328000d000f40686001c50740100441146a1078a6081c440b105408c0c284180300d0100c9440c0d00d25111200b04040c0f030080390007082194950710000c1c000741080071142c1040d545030340400010040305896940100603103039103403c440d0b201c54261034621034035140c9422020503402410000b0a0005c40707a003102c1e0350349000342d81c02d10241d030fa1115058225033041d98900002551015030101e19201a041044c902c281c03804103902d40191080c1c1100801002d4402e000e0303141d00d07040c1c184102c000c109003070b210b00780044608901d9549400c1c101071140c030a01c0002000040822242c1041d95100030560382c1040d000b44000307070040384081212504000390305842e10b542d1a41642040d80c58000100c800554800c9048080449414850f1810202424030112200d6801d242c5000356518148054000c2d18030a400564541209182c0310222801c3c0c0c0e01300c1c0040022010040012a00c006045900603405082c40c010341c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 645142778 1250 645141528 645141533
    0xc05011121070f1406060a091a01080408040f030f02043803070906062001020c100b0d050a03051c0b01090303050a0c06020310140d0308010510090504060906151e0c 72
    0x503201c600c3c0068036400040588100307900d40480d98501c146802c0340c81c004540d860341d01200454940d60038005195141460f410f800e07501800d0b0403900140a04280343c04c0942d90100c1e0b0180d6603868108030399101c07102403d14110b05090027100702000403100100c200900e5100c80c07050544244949001d0024803d600081da41c0b424400d8a01620700d50b070082c084075846100c0642500d003061507054000341030074035080050906200713844030103240401810704849419940e401a20900c1c01859100754011480e0001440030020241032074800c2d00c985480c0c8a201c120b070901d0000b111a04d05040f400c0155109690fa03000300a0016254141031440e200d9041c084c044170b0700c0260010003007000780300000344201101d52044803800c407940d65500b0342c9442102000c0c00302141e83c5010007000300c0c016070014030452606807045c003400683c41c50140c0311240c0e40c100040c141d50082c2d120a00b800d644010901c0482480000c8800c14901814a00c0c0f040301041c0c41d000d000c1101c402d1841c100403510859004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 645143884 1106 645142778 645142793
    0x11808030d0b060904020307031d070e010b0705010e0f0c030c1c0809060f030a0903030506011b0602090f030f06010e06010801080703060207020d0503070c0501112107 73
    0x1000c0500891101500400c05840d81c030201c1803104c50300c0ca4a540c130185128019584d4049580c0107420414a0684051028803809402601e0300340001a0441d8140d41101c88502030250346120500300300d80140300021150105010302419490020000500374840d0305c4214240c420380080e10f420800881403080c8a802412800e54250000c50b042901800ad06000549102c0c03521088591401d40381c0c1c4103c4048500395540e10498050660610809510032420708100c0c02808101086e02117003c100c00005040315000145240191200e460410b00484007134101c0c2c050b0640071207040d0320b0784824000c2c041c0c1026600c00061581d0b10840c002412550a640075051050958032804040d5000301410381e0080ca4444004000480070401008558081d062600c100e40c200000141030316041c990500c002c0d84415906a61b12201c2c010240c0d0552105100990710701d00c0d03180194 = true := by decide +kernel

theorem cover : BRFrame.Cov 644964028 645143884 := by
  have h0 := BRFrame.cov_init 644964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 644964028 ≤ n) (h2 : n < 645143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
