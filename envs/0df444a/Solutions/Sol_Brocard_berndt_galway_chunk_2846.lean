-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2846
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:54:54.302225+00:00
-- url     : https://prove2.me/submissions/7a302b4d-89e9-4f6c-bd45-19db458836db

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 511690647 ≤ n < 511870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 511691897 1250 511690647 511690687
    0x7030206010506130306150302090a11090d060b150403050c010302090619180b0c120f1b0a060f090302062202092a040f0f0509060d060b04021602121504030c08040b 72
    0x9480f010000d551f070141c0030049433171030070b1421030200d001c2c803074052542030444070b010107a0702c58400062440d07044c0700003594441d07407005520340d4154001424010010184160305582400382003d41c00c0960081c0051000d008111204215042080c0c607103c1c1644030b200240742c901000084118016103e218545481d03000001010152003100800900302085000320b400e009455a4207904024a2140000003c5182c00d40c0c0111840b84280081c046245482500d01881c00c0c040300042620796890042d0070404003c003122000007031022090044c0413440c1c0720382c0e821a1b0454000d40691b844032002c2c211000d0194001c242103a03110894413440155600900a03a4804140766507038030b07510035030030200c5c2c0c2c420701a96821541e6040426030311f04181c1240c6030010700c204004520300e0f50b90f10105040340c012250b5a541241c04101d110250b080510144a03002100f0300a0100030380c0e00d10a00c02d440c0c502a000404011107911144280440e5000341c0d00a0003c029100b6680c1c04803804101c07500c261 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 511693147 1250 511691897 511691899
    0x609050a141303050702010c0c091e180b060f0301021e040501090806010302011403092505040c03090803010e090a0f0f03120c020d14040e040503130b07030206010506130306150302 79
    0x40381c0c010821030010945031100d4181c1c95520b0b64944106a4011a80042d00d403100700e400500660300460400341c0e5008906441c0c0f0119101032502d00303152440d0007940c0001000005000c41d0201740b0010510300002c8980c4101c0903981080309030851404280284a03106429074403818000b0200c4038283d444000340b00f150001d80e41c204445e525184856140c0c20288030080c00f140d0642c24514003038032410007942c0d00c4030240050707482c01800050300e00001c4649000d00049051f40301820321140c03609209504040c080d52504002003031590b5144041c510045c0507440000307100328005180a8010007205001c4c950162103882d001800740b8200c3c503000c140071002c0f800b04003500d503500c60701038143c8904041d51002da8024405255841030136945051400b8060038960002c010100e0700101c000c540d940103520030001903960300f108418044e0119803d421030b00b21032004104a43c0800e40c0001e138241035860407074409903600d0550758400280501644018240d86c01d281c0c2c20701c804107600406c0d10840340 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 511694397 1250 511693147 511693181
    0xb0a020c092d090322030206031e0123060c01021e1e07050a02040509120c060609090109210903060615080f010f170a0b0f19021305090a0609050a 64
    0x41c141402d00004226002d03c0c0c00d80c000d00000184ca12110001180c12807078240c0d60703440c0e030388a030003045913075004541c038070100400080c40c020b0455190314000e00605e000440c2c03019104194814100c40a50340072400d01c916408940880d0243c0c081d4125907c441c20346100c00c1b09441c0d001c8081480350016003000440810441c00b40441c0702c804411107050682c080301510711071800703508000003404058000708042c482e100322036102c610300c00001c0c42d41181d00701c02800545440300821030240070007418080281d040010040010b2448900c8841341110340c0d05038049040c0ca03600841e030b031092903330020346514200b00307000540360400c05a40c0034904655a95107001c0c1e0f10020400c111020038032450b801380c00b00300020800c0640000c0300c8140441228280c0703c041066444005101c01c2c280c0e000b544811409040c04103041291010040d18075601c0c0303080d41004c050501c21011501248250b50045448400250b40c0034520380c0f00c039028200c58402004542044880d5000a04000404172180d235 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 511695647 1250 511694397 511694461
    0x161506080304031112012702031b01051903090c0e04050c0d1e020d020907020f07060306030506220506040605150306011202060f04030506041b140a0b0a020c09 70
    0x30000700032a0281c0e6004100315442441c2d0700140400c8691072070080209540e100314010520011316a0840101d07205458a903912415004050409a41c0e880c00320400551108030f84141e60458243d541c80c00d001c03e00c0d0941000c0141054028102ca8030005060a00a07580854401040c02c0001e0040b4020b1044404098040d820b00c0030140b141000078200744080d260399a10038460601e4648814800384c0031b980c50140c0d90340494404a015a80c01d009a000440d003680911801c000b060002c00075407a080c0281d03490340d102c15417200406000d81c0c04424144888001e01c92080000c490201d506c4000c540782450241000b800401e82620603034800f0280c07071020141da190005509060358000111072030365521907402c015055000900088205a0510000000c42c405001a91289016880b046012201150b5240b1041610340144d0f66510fa1021040002c3c1c5824003a10705035806080d075107548442d00f0805a24101c00c4102c038071340c45404032003000006140201c0b88075111a150003402800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 511696897 1250 511695647 511695659
    0x3030405070609060302030601200c06070b060108060904260c0a030e0906030307031d0f060a0509040b310f02040b040503011b082206060605120711070603020f161506 73
    0x6e48002ea4410340080d185c03142c4101a85840c070262a007a412100c100c604007514000820001d4000003000d5540390017100420104d5600703d800d2a0340b1182c00c44100d2844c0c44c00b0364940385030345810460042c45125030040c03c103e845900046403841c19041d003c0300d001d074169103070007459281c5c584140c034020782184020881c1801c2c000f0581d8a05607240e10b469124056082501c41e95040590905d81e1008038070200641c180c84510050002d400c2c00c4e56a156110702c00f5080c4007c1d00c1559101c00e01489014100d008603a0020040003001c425850401c29a02c1c003025440003c0c0c070100301070070190343c40050000b5891465070000c00c00c888080d002844a000c3c0c200c541d1854012004800000c120803000081c10329030b60050004100780031a5150842d00d003503869002c11110340d0742040300407900c009010f274440c403005404903602048510f4204100415001c2580d01d5030440d03c20b00061540200d0001c885406180a91300400b4441000901d0100581805400700d20903004c9030140524040f13002ca40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 511698147 1250 511696897 511696901
    0x207050c0105130b1e0f031005010c020f040e0c040609090b09010e0c1011070608070e1f120612030804021201050c07020d1e0620031303050a0908030304050706090603 73
    0x603d01c02851808290f619200c051086640018010184810302c40b41c452040c0c3d060a0282551503901e0040b5620707407501c900000500d61042d00320905006011809800503a0381054000c4c030307150140c4d8013143c50101400402e184c000c0b05d43c2c9469103d410041e010a008070141d124141c240d000345e00301000d40c1c60350036900307003203171503a044201441e000301413040c4580c141101d040761018070501e46800468103101100d814804181c000d400054060000c0c00b02d115881100e0000d8554102c503150500c00107441e841800c1e482c1441491b080c03010031405507e0304002d0743e03c103500410000f00c0c64201c0c0165460014401717035003203804a101d03514507000304d05120710521a0b98454031080d520075140010715002c01100707c003500e9040b03032500c40032079010000110a44014881a10a2030040b42203090a00c003c9261f90a070f40c04007510a80c1441002404000c01090500d02509420700700d82c0e451542c0c0f4111580a0309400000c01c81c0f2000092004000e800500b0300100c4240e5070300c4082d81d588400c41102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 511699397 1250 511698147 511698157
    0x9030901030b0613030b060d0803091f1b140403050105040609291b1b011b0309030806040f060e01080c0301050114032508070605071a0f16050d0f0207050c0105 70
    0x503030b801c3c0030130007030000903058401607410040c01008040e803000b00b50b907014400d503c1112007810a400001401070301d1440700d1f41d0b0039248403c000c003d10110300d194011407601c445400c3c00000700081c9403541038900c03d46104a50107190802c00074016443c241c100785002e8038100a08480301d4859030101c58104c0c0503c05c400040c0f200308240b51039552141d80b074200d420200c0384090441c907175040100101208295070a41004040d103400440e02454924608411032420724075030040c50706080b040c00002e03a1102c40b070780d80a001220000b400c102a200d410000b404160407107213155503c040041401c1c040080c1c2c5141c1c20a04600a01c403a81c0c07a014060217245640e01282e41641c007078110f440c9941c1e52140022a103424102460141c1980d4482052500c60036602c6100030070740c000b80d80418810000780403040c0390b40d941c1d16010113082c02c9514402c0300700000c105108444c801c0181050071032184049440070110b40e041400102500c0940d00000d501c0304004981d24410103040d11043e50003082998 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 511700647 1250 511699397 511699417
    0x120317010f12030c0503122a0c031b12040e1801020703090603020702040b1e01021b03121b0d20060f16090f09050405100614062109030901030b06 64
    0x10500b1480741d500351030007060340504540c2c07404140060895101300c2c607400c51181101d841345800079888540051110021300c940d40000a0302040701510000e8008100c41c203070f19a030b1580308414500c240c021410000380540e042d9001c04000b4001030900e81e200108c0d40111603800b1030b0340440401c121410b00f02d2060520040c04210a40000c115180c0650b020b014140c2c0058000300d600d20030b040001c0c109601640012a034030103850040f07041542c0c10403d0411207411847c54110390307d10100002d54901c80c04106600c5500002443e8115244800c469000b15030380300700b140c41c40800f8203005440060b2210b200819402c40c082e40142c00d20f0001080e03402108a03821414154660001842e01e20051110315024030244050000e203484810700480c0c0244150034bc0000d1030f0501345007031030900a003604008145070030a1014003410581e01c202c0d00c000001151900d03070b6103002c9028207100c582196440607007820005c04010800750007100030300a4003400d0ba0b08009400720581002200d00078036600b9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 511701897 1250 511700647 511700669
    0x150201051006030209151602311a1c050d0503011a03070f030f0207020a03050c0423071805040518070906060c020907051210060f050c1005060406120317010f 69
    0x380f5401c06c440750081a94410115030340013145242d40204503042c9040c010a41344480c0003c08440b01e41500340c05a540c0415514140000702e07141d01030030740c40c544070ba560317500c40d0201c808884501d01c89000c18400700d41d840703400d407400344440c000007500d01e0300244a981c048103901e00c250351200ba2a9011203100d80802d495107005d2800c4140c0c03c030001c102a041c014107090742041030801507550300351214001c611800c02021000c0c401ca05020540341d03400c3c4000064401800f40814010f000400c03150310840d94034180b2010000210f0401a209442d0303c069001494103040c003c0304800180090000b140b0f8a04540d609641c40700618100e5905115000000715801a08801440c2c92158590484207919105041c0700041c0300740b101c04002601e0301003002c60002c0b010440c581e0001c0d101d10118810f0b007841400e04280c401070f5134803003500310050400d865031100007403265075560344402e020f01024007013041c1590440c500900012010000c0c8170102c14404000100c186898807880155800340140b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 511703147 1250 511701897 511701919
    0x108010f1d04020303220512010e060f0402041b0c480f0e040c05010207050f09070201060b0c030c01150b0910020109060203040606170a050d0c020109150201051006030209 75
    0x703032448140c00b6000326414001002011424040314041804201407100f68050403451310f0b0402908140d000001b000340c3e414210b4081c0c006002103440340d4032818510000030540d4403480080c000305000e00d0054601134400a18240041d4488614408144144110f41412001034a11b01201c1501700c0e688400c01090f5514032440d1802e241ca0b4407081e10403103440b843c4141c9a50b0749402c4803603240c2000c050201c0e04401c000900410703644160080a003070000d003004604100100d0300ca540075580840c00783d40010007040c00a0310075030010740200a4480c446480380307042c1c01115182d50005a100c0f40d90360034042821902c11101c0d581e1002c4030040c0c209940341c191500c05200b00b0b01d409000134029956140158808a0142e000461266115440c0000c41d241400c0614641c5600c40554103015407080740e0031000200700040f504621042818400c000c1f800d42d00c01220461070ba500001c094107d4010850083d64054200d94050040918245910340c0c0700e20013141240140a000c50340309242c0c000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 511704397 1250 511703147 511703189
    0xc03051017030708030a020a09141518094b0403140d0f0c03090c03020603090304170102030f06030d12050c094605040c050c0f0109020108010f 63
    0x8036800c00c1d40d101026a410040c403511403d2280e0130071a00d41c50b2903030700004d01e5100380e50300a12400280422000ca1052440210b0100711224081c0031044140d220015100020003404103850a506800620055843c40c10700103401c11150200303454506070601900d90341c0c000300000c005500080d2003840384162480c0c092104d180c0700001038000d070244815007074224403991801008203500c1d1108413021944d021504550000c0369598030750001054540740b1500005040303000040116501211030380d8483d21126041821441540d000e040024904003c1c80001d11040d00914407a01002130025500d82e1901c007855124061440d00d000007424400d90302a6480059005d45c4c1c06c18490018036013000000342c0401d90004a00b0b12800450b01a00c0444842403902d00c2d006880511070210842176000d00e043d020504801405000c1c826074a9482042d6020702c80c00c00c2d20f03103818200d001ca8421282c1072041500030100800f00360300154660001148200d0924845412901505200900a40000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 511705647 1250 511704397 511704419
    0x21b1c0c1a1206090a0e0a050a0c060806030a020f0a0b070c23060d1808121501030b011704080f3f04020d1704060f02070503010605010905011b050102030c030405010c030510 76
    0xb0170140e43c0d5580c6000341405400c0c200074040c480380c071a0700148580005170400e0002004c4582c08102085002c0c010425252808a030030101254103a581592000050dc00260094150303001051212000301c0e4450900000c40c01410440302c0001030011142c0401810076103002c0d0003201e01d600800c040000ca1070010301a4051040401d5168940f1070b54080350ba1445260b03807140b00701d000fa0450701420b100c0014081a1604e01000090030f080140c2c80700b090001e881920600c9248090401d8000083c040c0018441291280366250303020a56643c0640c1490709172013100110343c2c06840d0000d4002c24140311081d040c1040c24008240fa81c081c1d5550707400c01040c1168070b9012900850744440c01400304c030324100070b00007800340b649800c1c0c00c060450900919081d0300c0c0d80711a02c2070b8109a000c100310398114141e1800e0b210280f070442c2c00026142400052005100e03401001507100104200e482c5c0481c0c0c020710300491154000380883c0b8503400c0220103a80c07054070300003a0030640c41c808024500c401c1f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 511706897 1250 511705647 511705651
    0x603030c0311330a0c0f180e01080d08090a0f0f0f021f23030403030c1809090201080a0e0d050d0e0106090504050606060703021b1c0c1a120609 63
    0x610841d01040c1d44484240701c14841d5030b0703401120000c20f840c1200b0803500c8428103603001425600800c08110b480000408551007000d240c001d0055088001842058000000f0040d02000b86000d02c01e50b9100c041a0b80d413404940b00200061540c000704604650115404002c5500811501c001c201151907090400320780c0f01044a1100c540414a00161641104000a20b442442c218049409444c0c0a40607803860301e4801200e904062942030f034205040b050700e0300103405140000d08984c0a00058401203914000034141c034503080400121903620303400c04d07899107100783d0f118542a01e400c240c00f000d030303040e13000010065041075403001c40440c403e10242080c000c94401c041082d54503150360601b141c2003904003581d99512101000700340107040016540010f03007940e8103864462581c400a494402442122199036400c440e03c0c0b41e6960380846001304a100c0c0810b501400341c852520100380d6909105000c607841000f03a81e01740c21100749095902920640ca00f00c282a030321141000002500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 511708147 1250 511706897 511706927
    0xb01030e19020a060e0603040807020d0b0124030c05070615210b0106020d05180621180106051e061608040618120f0215030705041403010603030c03 65
    0x180e40340e103400920041099005030038410701d9032040522103005115990704950441004d01c081c030516052a521044202daa0013900180860f07180c0b06684001030000c403080c0405000d9015a10000c07942d901e060045503c100125a8980c4d62900481e4040d415074184807140c80c085801448480d010030043c2d00041412000d010700f0b83e95250b22691441090056610201241d00c0e0244171002045920a03046015200600041ca05451881001815841021002500d14004280740560b544820080e1410b2441c0e609204050252802020340070700700490303006082c4000440c13403010b0003034184181011b17514041c0028040e0700c0030140140710490312154035600407608120308407d400d01640f04034400c51084003d02d030b480f413900c10000c2080b148614142d14130061584200009200380b40f010750410742c0800f10380d80c000348034000550b007015185100c010340400002000302c0c090b4410004c1040d40d40903059040303000c040b0001d140c00c076119800024040342000c0e91140110340a2030800e208802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 511709397 1250 511708147 511708151
    0xd0f03120f110418021303021909050f0405060f0601080a021b0109050619020405090a110904240608160810081203070905031c031503170714030a120b0103 68
    0x103001000c82140c40200501d4503214000ca8180407041c0e5a10020504e014000030135410171514070f0081503c803409100091103400d00d10200d002c04111142c0d2071009190b070382800c1283c0d01d000810340b1421202150216203601480c0d0004406861549406008038010303550404150f542e160b80400941c050340e019917100d028040c4001070f02009000e001c280034030910203407078203040ca01c0801c24900c1041c0d0a600d074042c010312041c03000381c40d071103155540540c80c3c03140072541504c240c0d01881c952003001c83c1541c0180c1801c846a909002110a402400940d201e1070340c5402daa40a08540c440d00690703410400d10794824140540c075108003000d607004210400c1c042e0742540e072008030070b14281c0c404559002d6080c0102c100b021482d040001040100003e402900c2001c012808400b030720400e40f10540c0a05030f4a0207111210000d443d901005075600440c0700451070b40d101c42d40701e05c0e0703004480c04850921032a200c10801140101c20b603149c0b0310403501e03064614000c9015000192012043c4581056 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 511710647 1250 511709397 511709411
    0xf20010902030a230a1e0201050f0c010902130c1b080912060603100c0e220f020d05060406030c061407060501091d06010501050d1a27060d0f0312 64
    0x2e54184204070382c051181d02c000c00d00c1d00c400030b41040146881c1020300c1280d08409050004103001002954041102c500050180c141e01e02c01a912030143d1070003a89100400300f190280c0c1b240540c00036808500031203141d00c0991111180f9416105864545c5c8002a908120340c00030124084100c0241481b48400c1d80c10300c928000030900f03c01003a5100301043c2e000006005050509209070900c90b02007800601c0702000403a8041c000000d091000c50180405070728602001e0141880c0c05c3c480c000b80042070048520400e42c039400f07500f00d20b406d620120320380008a03c10b4a000c2c0704000489070700140d2404200d281400541e080390803d020100000010494900026070502c5886c2c06082034050024440c042c21614039210303185111050483d501040c010702c030581c5c1040903103216001c0c120001c11216040002022404024066a0b0300541c00f42486802c1c0e0740511140c0c5500d00c0e0010b01d12a4940e100001c0180e140029a00507011010f05896007004c2442070a54100c0703480d10001c046400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 511711897 1250 511710647 511710649
    0xf2203050607050a0807080402011709071e03020901053c03060115020606031f0f02041211120a020a030f11030714011101050c0a032a0305010302100f20010902 70
    0x100d000c0300c0540000b24002101c80c055034004034070350303000700c0c003490541fa1511b01980007074030b40f84400d0203c0d0201008040041d04189040120b08098400d0014011035030600c084d002003c90124001203100365030000000c5032905089101d40c0d48112400c079500140d803a4007182030401044900300080203400001d01400130749040141a000b00703103110258001d0358100308000c0c28548082c120512a80060006486041c016801c0610701900d031030b00065041c03200c40c0c2040091046034442d10128240d81800001d01600c0d074080207140d0300560715044600020314000703271903421403c0001d51010a1880500220f5003150001080764450343c8001c48000d001c0000900e04180307a445080b2030b08809240490650f8800e818580004503280244614108070300c1c03120060042c144c2000400d651299194180840b0a08a00e44032451115201c2d403240701400080190109010907400744035071031500264244030303600d2104a03a00d26640c507a9100c29410070b468030314005520a94040d0b403603109801c05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 511713147 1250 511711897 511711903
    0x10120f0b040804051806091501020f15060901060c170a140d0b010e01020304030b04080304081309150605071a041103030c06060f0301060302010230030109090303110f220305 76
    0x1481c0a5210240c94518100801c0900008800070200085c0c1400c18032015459440c0e20300d4002c4041080402c45001143c0100d14103050f8008601282c41a02c803801440444030f82110301450096445002e540e803650302c180d46150508800515503507592448541c440c066601600710114580307030420780a04d07494000c042c1d90300103c502c00e111950300c4d0b1751242c80e5a005106140e1207842170001c0c0d410289140c4a00520400082014201c0d202c000009010001c0300b0048074084030b40c0014a0100c01c2d103030300d01b1100030a00d1340442c18400345400c41c0480d215000d80c003610082ea43c00034890140e02c6911040a4500d08080d01c08c58a00c400c0300c403842c0460b54140058001c18046274004e060a01d800010009840c403810310b00c0307010ba450161700b2710260364045065803559958480342c902550941110110700711188001061582c0d0104c0003003628107082d0406400d2901a980c01d105110b542d1001461a219590758904a1201017000c5011052500050300e0b141e0040040c10a109549880b4541 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 511714397 1250 511713147 511713151
    0x61206060417010f05071b081606050f01030b0a1401260d03090c050d050c120c03010606111506010f0c0f0f0b0103050f0a0f03050c160e01060e040510120f0b 69
    0x840c1d0751141561611041c0034412180d01120901d1f090020030610406103119250f810300103010128000350800d40b22201e040110021b95010008010758030300740100c0800c8140a00080b121007940307001242c0183c1440c01012400b010315406050164a4100b000c11010300003903010380b5504050000030305001e41800030103003050a580f0b0214802089161202e2007007840d401c030610507900d413220a03010807400070348011440c0782914142c205455681c1d20700e10b0412244a21075056080c09408507080e0f51007001e24650f05101402c075680e032408011094140c03001101c0040c00910003103403150590303100340184000c550162000140007402600d480300b500c16120301c19101030740f48070700400401000f046a15503401e0300e1070180c29500c425a444c04504200250b0107001c0101c041100c4041c0d039424480080c402c288407401000080e41c1d040681d400d10303000d11400002c00c6a2401101d103c3c103203030040c80d10170488120b412420350b040c040390f004c00540c400300a0718002040c210050000d0f1400e074102c0c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 511715647 1250 511714397 511714439
    0x30b0a0311091815060d0c081c02070806070e06070c060215072d11030315010f081303030f0f0c0e0f0f030703150b0307060c0605060411070b180d030902030106060801050612060604 79
    0x4010460f0388500160f009022014400842d03100c403404001215010481ca3b0b00103600e0f14040c58880da0000024285005860024211310001c02c00019407030340005003d204c803401c1c90302078109540c1d18007040d078680d001c821031005000e0403982080580382603e03410250382280c0b401c0851030303410f10348c1c90285503030005c0701c00c00d1801601241824440da0492407408581c4510314000c01c8601d003200401c0300c0050500e00080c28551550b0149068610340d0308503003800300322060100325407824445e008155400304030105000d0780101da8126404e00b0b0240c42c641201d04050010700c2420b165680d4154900810401c551a2070342d40e0f014a19a507500f80000b00c0103000756078540b09030207103a00b00b000031940058540340c81245001c1032107590805400680310324a4004802038000d50ba04825a40400c81001c140c004c68051208401c84082d003541c842c294150091300200710340340d2035620940e0004021301907140d00a10600c681209030640000b0946e0003000a01842d0400369504003400108026680c0c1c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 511716897 1250 511715647 511715653
    0x606160302160e040302281406061503060d112e0f0206160f122409020c0a080a1b03080403020f0c1f030b0a0311091815060d0c08 57
    0x6098000c07200b221806040250700c414080d0501d5a4065036400091200980641000c02206680c1401444103c45143c000403813000e031803c03020102e5100c040481c1d0b214070070058000d0b04480007a0040643c2d1250b800600310020750712264070b0781301e90300010880156000d20854031040f60017808102c040c2071550078104560355010f07180d0b0082c14080c03400246104640c0b0000c00c01c1490b0001c50309040e040700300390800540c0030320000000c5410b140c3d0003400f200d0702400c154030302000e888a50b0380143d58100f07410b121060280c5a0050005078403500031006905c0e03001400080c00f1804d140b0003406008031350308204c00c0070182d010281660052612042e00400c900e2410070003803603010300c2b010710704001600c050000001c09100080032700c000360b00901e0074801c484006c810003034003980c410310000320003c00080f0055a60314007a2414603041e0001c60140c4a0440030650403170034850071803450340c0c440c0b0181c00d40c810303d13150313101c42160000c010a80c00600d00d000f14020450344103084010b00302e20009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 511718147 1250 511716897 511716913
    0xf090306220201081f0b0405030c010219020f13050106030b011d0a0b0a02011806020c0c030a080405040b060702220e12030a0506030123010302130b0303030402090606160302 76
    0x406060180090031401c03103041000006540080d0080e25200165090800b1800d54a07a0043c18140d00507600b40b0034118038a0030800b0414183c407001400480b03c00314204c40305e91080030300490b102d004200704c0345054010450002c1c014606105c00101002000d080c0104d540d602c1d884a80540c0d20170303800b0601283c1d448083c4403c3d03590016094800c0c04821810909114001e0045070669484d442452503041c0c0c00729210550340d00c00c2d00a2883e564000d0152191340c0180d051a000a40c89001d0341055481405410742c010305000c034a83d2585030308131322514102854001031101800400e007803241c1c4410100b20150050350b850b2aa00520403180c0115815200f80d416440101c42c107816000d035050340f040030143c00844486007181e81c0080f1240c000300c3c182e10341e403010901516000b409030740000c84074001e10040142e060070b01030403240202d405904001d115640c00040f9600170f200d035a05074104200040140c00c001408070340003030002e406c181c50240e8031100c040c00d42c50b00d504110700607048901 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 511719397 1250 511718147 511718149
    0x15051207080708060d02210309190510090609060c020406090617010c1b02010c05010b1c170708040302091017030703090e0903030f040804030503030a140a09080d0b04110f09 76
    0x40c3c5668000c0080c2e0f440624400079400241550404840d5040e07803002d843c0c0700880c00c20080c0300ba00c000c040041c040c1d40f661401e44860080c0f200b010300480f070080c030f4036140700031205109421003c201e42030f90b12030080322820072030100e4480c0540b04040c2e8200e80c44060000350f281c0c0603c0741c14001c001882c008016403056000345425070f0b400101603020001d8407521003a60400540130400c0c0c550342402c00c9500c20300c051274031030b01501e40842d00c3d942c4003043e2a130f100b61100e880900910070354417a13190100115054007086071980101c86010700140360601040c80107051602185400c00044a06000e0386076488410801d08070b401e50107440642c00120f80d0f4401c060308106400090070f5492041d80c068030704103004a82c0d9020050990241007415000304007400112012940650b401000b03072941c030f1030140d00344005001b01c0d08600e002803a02400140c00008284119003003d540141041d01d05241c0200c4103015085001c40c1e60b0780a1b50744d0114080172005840200301611034064041d44030420b841c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 511720647 1250 511719397 511719407
    0x40c41040c02150a15030507060c291b0d060b0c010b06091302091c060606110309010f0e01120603062003010305030906070609020d050a0203070504060609150512070807 74
    0x30030009541c0f100caa444541c00d144100d80341c0c08000c5034000220400081c44168a00c04550703c0904a0b000e5001c0c0821a2580071520b40340450081c0d04002134038803c5000381001d011080e250009802645010034858500308001d000900840c001c52801c0c03020201942c401c850603940b00e000c000200196580300042c00b800f88030004082110654208407a2001041c1c000c1038007180b003610140d00003605145a510342980c070450003213860011a0003481c62805200400c00c0d8010320001c116102c040404000000080714050481a592842e40002c0e8020980c0e402484c040b401c0d0601030300c104040c40d425898440ca4006501584000c03e20302041a06034450b0b030081e9180c06d869260800050010840c00400c5030b1480c80282c03007165132041c0505180f402410020320096000e10b0011442c014000001000c0500f180224203642c2860faa80c42000216000b5205010100e03c200004001003902c0c50f000000c1c181c9103003003c6107000ea240c000032590300002c0ba21180401c84441c2844001c80e401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 511721897 1250 511720647 511720661
    0x121807080c06070206160f030c170304050a0308040303061a130509070c030c0201050708030c0901110321090c10051e1606020a090306230c03040c4104 66
    0x324041e118241d5640085006031041d000701a0060300005440b0207044003858103420900c0c0c0202010b21903009501d802403080b0300c0c200060b01c00180c003e17840e02c03401c0b0100c002c4a00035644040100b0b54403c142d641920f22a600500c16403d1503550000010f21414914005000035203c00318559100c0304400d510108900903003100380a40c031180200800702e6000704070f24441540500b0000e1a0781e085200403286071190b40d0000784181d0b004003d10a0055a07030014204400003600d94046020420800c29030300c1c040c2d0550b06d0007100c00824026a01c5c10b50b44040d540181c181d030309450340030b0050b00105550401c1820b090000400c0020261030f020781100055050302007102285180080d115112903840030b081002602d10f560010f0000c8100c5c3c083c441510065a11510074040c01d440282e208141c0740d40702402510026000c2d0014050742c160702c089038400c550003240b10707280314200700c0e012800c421210010540680d0840b00104007607210248003403c115500c2081d0218000201804242d92074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 511723147 1250 511721897 511721909
    0x703120902030d0503100b07200d0b160302090315011d0c25050d0203030709050406080d080417030906150409150c05070c09060e010e07020d0e0105121807 68
    0xa418402001642c0100b0040641c00481c0741150710394488041c800c80036021503005040640300000c40204210504a107071807140340c00610411030b80e1001c02440341410b98008003c0008050000240068140c8405010082900e140041c2400000710109140c09100c402001d8075207007080c0100120102000b001d580c0150000500816041500d031000c21402200c10030003c850816559510030201c030081004601d030400c0454030300c0f0021b0034001c0d450343d00580d146400100d03034003004540350905000e03840844074094024500000341c040112079040026104480d0190310031045203130407105001850050480e08050465800c103010540d00007499940014000c2e81000000070100b10000d0641864072180040402c40100d00c040440e00743c4545e0302d00401d004019800440c0d03185841e440700f026105802e034000c0b40c40e600c6038860500840221111001030b44444900401544a060001d405a2040c109207003448080d80200c0301191084400903000321407003410407503100d0100013000040030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 511724397 1250 511723147 511723151
    0x1101050f0a030504021c0f0c09020a0e06091503010f060806010c0f021504120305030603070603060f09090c050603042109060f05212d15092505070312 66
    0x31a4621052500505500e0400e140e80c40c0001015525284d141585402407200803541101080c51300e2000b500c51310f0402c3e100c5c280b02c808003040f00d501e035100310f40c4004501c2d00c8410308105250f040041c59400401401c0d00004c1ca1115480103112403009140a0090104075a85690134460000c04484005000e20b0421001440c1080410168404203400701e40507120805101d540c02c51321412441581d019008601c00c82822005040d030010295000b500210161844103650b604100c2c144d8649000f6094a039980d088104041d6003e0382c040060180f2541190f50069642c10000b0f100344c00c101c50a545010031500500480900c0700003c07131100c000746c1030180040d410b1032001098000c616400a050040008d40783c80b070a42d80e0035103030703c0740319005806464a20f001140c210400400503002903425010008558900a40c181031511621041c2e9480000a51403420800c410310041c00c00f1404d0b00080104600e1a864110601d40c0c444450b10f40c0c0c1c0c2d5450741c83c50001c041c082041c941d42d610318 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 511725647 1250 511724397 511724407
    0x2205040504150e070e0112050705130f1b20010906020a03022215120b120a03020d08150f041d0c0f0307050a1a0c0f0c150a0806041104030204050112110105 68
    0x2c45445c49280c151030130150448901401c524046140503010380040d035029a880300d000040c403c1f030381c01c541c01103c1c4403507003030050002d941002408089011540b4003c00c05100a812907107410206610102440e080080f0f00c1600a80705c04049030f204d60030520000f80c0002e48140c040644c00354020403c2074076152520356600d4003132183d0100d107903281103800b08801010f00c2040c02c2c800c0c0d000107608500c001c0c1410105480b4004d240d540e49400c101c1240540518444450903900401d0058440c400540411030f85064a0040041801c0e07a0080c40340d00c1075071045180303040d800110824051165081c0102100300807602008044403507030891134445d0380590300500003601c9001100e02201c07040200303480500c00e4441c00300801d005001c0b2484152260194003009400c0016144074506000c2c4e480241c041101d185030b800030300c54045e140c404101e81102240c080c0c10298001300c03681c40080c020351b00342034580c3e0000703007582c1c400e0780b05485111814010300288002c11491081e000000d0070040c0c03800d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 511726897 1250 511725647 511725659
    0xc211d030a11040b04110315120d0e011808060907051201090f0803040303020405090901020a0e040b09040f021f02031b030304050613050109020d05010207061d032205040504150e07 79
    0x1c4001d440b6190103507407180c200021070f071600e40142080a260409464403840e24552004400c0f20791854184580c140304203e4922074004200c10042d1003403580c0d1640300c2214040192844c030445442c1a030148071080b4000f86001081c88450300682d001005424040d00d40020030401803484000300c0610b903d4016440000b80003044000300065011810310340b80e50760382c00c003900240615407005810500c0c0100700300200c941940285000b0030140c58810400c445c0d14113200c1221034040980b50402880004900899003440c40c1c0022140300a01d1110710650016065000403c0035443c2c80150703001141185000008007034180c0092407400056080d881c0c140c481da580c1b07180140060444900e05459070003404000c0d0440b40b421a005001001d0710302080c41c8c028003d41c42154244d402c5071601c0001c061001d802582d8a0303904001d60025400c0c8016002d03c2807412184400a026104074031800107015100e80c02402c3c403540c05808490100001090401c042e21076007070302c0c1040d54211b810305101c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 511728147 1250 511726897 511726913
    0x9201918080706030e07120302030304050607080c030703020904111813020721050403051203010e130b151206010b09030601060e010f0e01020f12040f0909120c211d030a 74
    0x40383c0e841c3c603020510305100300220342010310707640202499030300c4207490806160b000002540030341d100e402250b81a0b0b480d400304a80e4060300f661001120082007000c00c1b446c500c00d8010b00030000004200262114540c409100d45510522101e01548268296800b5520300b962040c1e2014202403400d503c1c200f00f0781d45180d810200d9280c034030000d003c1b0000302c06050344035405a4025542c00f0040364440600312190081c0d5030800d2103810780200e500d00015401c1c80700d5207081d50405601c10010031141c1c0741e80080c0c5260050780180c0a400580102e85145840010061180203010030044540e030303015503000341800c1030300580005051000e01404a10666401007551484402601c3c00141c0030521000413800c0c90340c00074203480c041c882c101c04240d00b012034100800c01c442880d45891032981c2da0b4084401a82c11101016050540100c0448801e900a001d042d101074410317120504c503911300540c03540758900071078091000107040c21400441c80d405044011202c0e4000c40003003d15a1943d951842 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 511729397 1250 511728147 511728149
    0x2a0f0f0a06150e04050313060e011202031b070b01030201021e070b0304060204241b0804050415050a03050115141c0651092019180807 59
    0x700d82a624880b031905405010a4280544040351003002d1506260500640d2604412500306580c0c0d50310300b00050301401000411020001a150f60740790364003030b4000350000d41004052000ca140c8031103000000c07003498401094079034400c104020807541140002494490001900c2450318505002d00000c000700103005811109501240b0f41da9070340c0e91030043c000c0c2c001e03640080300c3c0c03405c8081c85401c40018016a440c0303003509a920200f01607d45c01103042d4507050040302a102c888200824480d40c00e040d00300c0041156281c070481c0525941e8404202c161006500a07a6981d568400765039140d03003c80c901800030600464245050b44840c4001002950381c00700c40802520302090800070009150485500024415419110075003140d0b070070600c0140d0000d030a1002c140f13119031134440700c031504000420303180b286401700350a604042d10300380200342d51900980e1a2401191032640510702030f0003030141c90303105828034241840340230014200c112500d00c504510841c1c00f006004c1c15400140c10300c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 511730647 1250 511729397 511729403
    0x31915030b090c10020a050d021b06090406081507110718090c030b1306061a160303090c12020405070306150522080706020d0c020112112a0f0f0a 64
    0x819242c10015a207803070f4007500407039000002808843d2280f9008513415148a000f9000d41e82d10f4401d5100407a11a4040c1020707648000e51310400348846e050071f40140104590107003002504544400c8560f16010000341010b030201000420010507540c8101109031030840e0324000c040f05410050b480c500d0400600c240142d0943d220b142206100e01d000383c0304000d42e040301c4102e44a09080016090715400400e05035017250410030002680b9440701c03511107100344c6003e805428840c403040182d090040d103141c181d0806840b80b681c007012401000d03182e0004c16001c040b00c0040d510310f1041c01305440000385280141450042c1c104440d0714110b0204941c50000c0c03400d955240012281242400c0e020708810504016002e004109000000b8072802900c0aa030200c825580b510b0381d0403954000c00c240020300003541880940c0c080002a04110002001135180c42e04010384d40017036038504040c00b5003038200560460302c5600318400c14030080794240c3c900009880c1750000b01e1080c1342c0d9100c0c042002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 511731897 1250 511730647 511730663
    0x1e030c060c0301320f06090d03030f11040819030903170d0b0102030a02070b0306130504050105041e080a12020c030d0603020a050f0d0209060d0f0809040b0a03050a14030904060b03191503 82
    0x7070420386c6c0311022541d14140c0180689881c0484e420010000d12008101c5420700d45000045040d0b150014140e40454108000800b108041e500c40f04051015003c3d00b01c0505c41041408400549041110114648080c031080d13183d40740c407407441099030b0a4008440c150341080201e00c0c041a40442d0340c50aa0f400c00c0a8103035241c450901040d880540c080e4600450303403401040c40104201900101e009030301032040202520000b08100c0d1114680c3c40b401040340000b0011584210b0150301c040404112401c4014203040103150f04504551010741042c0d107140d5551024000c42c80d05c64248405858103403101c00c3c01c0c03004840800c0d8881b07810640030340300e1104400010059074034400c08a40300e0390b2010b448a490743e500d1074440201e4004100d0a44698100b4800c001d403410a000d0141c120303038000000300f58850a40c0c07900000891819000015170000b004107807030301d4855000e590b00600000544994138a800c10401103e0340c440380000b04214141381402403040b840701802c4064a8014400d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 511733147 1250 511731897 511731919
    0x160f08010e1807120f17040f090b0a0e070512090304061202070c0b120a060b0a08040206070309080607050c010e0102070201020a0b0702030d052d091e030c060c030132 73
    0x1902e45082c2403680300e018040303015146135042006099090104c40d1140004011130084000d85102d01c0c002da001d0b52111030740d5050100440100c40c0c2110350414409004e074200c0a85401c0e840300c410608035001030224800103000f0400a01d454001c0b64480c1d9141c0155082c10300b0102c001f0101004c201c42380c8001c03a00850100c09200a240c0300d08000e20010744520368980c010740201d69807003002c41e00c00000c46d1070311400052100401c4225400c01041d6912010b40b56129820071045800400c8143c1c03c2280c0903d021402d8034080140600940147e110540c655444414140c2594000b208031242a40103008100040c2d80000e842c0501c40d501c40001000b964841000b24650701982103000e507214104000d210901c1940209500003041e401c5040c0c0e507080407c1000b0401c00c0003960007017050f5200b0490320960105d4004003422000465096a290844e060b9441d4984138040d14500c44000d8000010070043c092040905151282201104c1d100c0b00c070001d161000d10100c0840ca8015100a44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 511734397 1250 511733147 511733191
    0x905150705120406110708070303020d050c160603020c07170a0b19110415030c120c0c0501021908060126070905030a0f03091a0702040b18160f08010e 66
    0x510a5082c41086456071101d54a02c401000144985004000d5004134813002c07a01000129550701a2034064009100c600c0710a0412240303139101045c0c23000d81e40289840700108081c0100b00b44014000e5039805610740a94101183c00c040ca15800b40c060982801c0801034181e1020882c038600a030044110003282d900d109000989114000591406920f04402034880030b00c0f603000303481030760440d101c41c15400b5003003070040d001c494001d85004042a428140c1041c0741c3c0c03040e040900c01400b00d2620210003105550b1307803030030783e0026003617850001c0c0910b034898511540a1010b07a030000d02485c001c682000107440e055400c025441041001d0361201000840c642d0194030410010603001c1d0403281e260005042049009400d981c0442c00210703c10340020f00d150b082c68610050080400606280c455107608010042006141c0f40340c002042a089420541e200024079104401e00303508075081030070b640c20051480c1800200c00e01440383e60b030010700c400c0e050240f0481d800310754007901e81900c0c10300e46 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 511735647 1250 511734397 511734403
    0x9031202030c0f030342030708070e04140a1e020a0f060c03021b030c091005060408100501080109080414030a050106060f0806180f04080c120301080d0905150705 71
    0x200c51080d984111010981c00850004c0114410980362241d010f41c40c4c6600c4413008500c40d142058140c1c96040303902d42021640098200c0000e81004084074010380e96581c90f83c0c100302c003550001c00c5403c4008100024000c020520a1903010060003424019040750380b1210144900b03204186c40781d1160100700c08544a080c400d00260070703083c8114821603a20344000705840e0500000310010701482e400b01c003060340d41900e681c0d9007403402800b030840b01c113500d0148032002400030f040a05801d40c1002c0040c1c80e4a51200030700142c54040083c01711a01a00300c10300948006a000c45516071610401c42e02113180321040e04c06039101d004209802d41c04800000e454030700c01140183c140d503e0b01800103005600003a584441c1056500c8030400c5030707100c034200700026102488401c1041c2040300003130082d0515501082d401881100443e0034080740e09152031400c2900b1304250011400000140b11034070302044001a005400d1400704041390402000c103c5040400c4102d104001010402d041008014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 511736897 1250 511735647 511735657
    0xa09060f06030b01180908032502161502100905030a27030818040c180e0108030307030213122913060e2a010f08092e0504050d031b0903120203 63
    0x2d0328230b4032418101c014a0801140355814402c0844004401d41e80d00e002040d010407240700700c0704100c507030343c50840c80c080b00350003001c1c1d07070400c40c0101020030000c02d41c40d10901c1c10f110300804c000d41d2500e074241e101038080104503182600741c24640c031a02d1916200304540e00180c0ea4024a25626600c00d01c298041400c1c400001d90390150800170344031a45940b10031000166503801b03c40289065071034072401c4110b8400c0c020562150003c100054546010b07800401c1070041000d0005010399483c0850440c1a0943d1070440d01c000341d105042c0d0740c0401b12108489102d4488901c04414200f80e01c041001d1655504000d101d16121300c0c3d000b20fa0401845407504204080c044001d05c1c0000ca08005291500341c0c43c3d16000c603540c048060b0004d03104928275031080b4600d0004140c45030003002900941c1010341040c242241240f13855036814401401482d002d03500c0380307000b0301c9402452440038081d035021904000c2c88968400345031401d141d000002004607a000700010382c0c13031a54a41c04034218854 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 511738147 1250 511736897 511736903
    0x140d0201030204151e05070302190c0e090312010b162604080c040507020309010c0b060f040c050a020c0105090303220506030906040512160b0604140a09060f06030b011809 75
    0x2800c0e0308904c41c41d00301484138071400c2844d40f080000c560380301090700e280c000c094000c0d006034410603840100c3e0803540c0d841d282c007030701901099203842c0d0750304005107481d04119400740c501d40010500707107600044182c90034050061130031168180300b00720b0142042c9904e0450041d141510384052019180c01c100d203085802c25202450642d100d0320340000c3ca80c0c43c0c07041002540194600380015810902c0402651800c0f14141c0d58501e90704c10720b84800354103540192800707074400003c0c00010200c0ea0350b4451544601341580310300e9222280b03a54060300301208503080d581845410444d507803141d90003000300c849900080c019841d20a8070384035840a0040030340c100c19000b1000100384000c0d02c00000b403e520481c03145084444018400f904e1803001e000d07400c40115500342c2480440001044c1d201d0846d0700a5000d03100285011404101c0101e500381540c0401701255100d0403071081c440036028002c1c0003441b030042448540d18559400340e034403005108a4071002a2400d0b501c0c4102806d070031102125030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 511739397 1250 511738147 511738169
    0xa0b0a080d0207081501150e100c0b1506030106210903022503050d031a0406060332070302160c1d130c06120e011a0a060207140d0201030204 62
    0x80c45600841e03581d1101c041c100054401c1e10030010700c8480c0040e0442d80c1c01840b81505a4507480e00c003041400f040c400d20400280411584030026a44805e0079111075000310340d8134444c41da512800c00e0b0b0440100031f0701065440c4007a540702406626503000303c82c1161810301d403015003041c44600e002c00c03003188da07410040c0d05828400d000c4141603001900c020420303494907010030050742c405190350f4010640d100080858204a0f0780314145402035019040b0035181d07a148441c036241500000c2c0480f407094100d00c0201b0381d201040c2107070f0802c2c000007050704003e0b000c0a020301c0514600141c0c00344001480c3c1000c0680000c2c0ca803292180d100b0038800c5540d03000d10405519030700c0f54a5010485030240594408082000020f407510032215603043c40c460b04920b14400c4c8a080c404106d48500e40c101070011b40300c2c0ca0b01d40e4035180000c00d11807405400300c1400074211184982041105c0140250710250455219660600818113160030a9484003012200d4410030300e40303031006038040d0203240c3c00307131030340c10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 511740647 1250 511739397 511739399
    0x90f01050a0c14120c1b010903050a06020a030b0612041403070206070b090703080a02010c020c0a050f040c031b030b1002060603060723030f0402120d0f03020d02070602041d01080703030e0402030a0b0a 88
    0x8040003501c40f00481411100301b801840e1500111009045440003038080e9100c4004600410040d600902000d1502d14010611242141c00320750303030380c3c00703101c02d1720460745024208414050080b0209107403a4045028519000c40e90b00083c02c98054180050084da0404000c2070702c1070f10801281c00210f0780460141c5d11b034614501c000e07000300325480425001d0f01420030300e81d0712890300300d0341401a28030003040e40b4402e03c140e4050200401640c4809410b0560703418400b480721208a219609003131495034042180c514038000d12a10510b800228419940602c040c019a0f80d008120709030b0104091034810109408405203030701c0f40503c440000d440400c00020300514462008520744258000d40e01201a56490b000b440e541c1c003042481c20001a10003616404064480d40092414003800032000d41440c001e80c0b40c02040364480d40c000c402c01d0303000d070030307144141c17420308852500514001c40904101c80c69034030081e03c43c00300448040e2040f640000051010841c69000082d5031002500c017001c91 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 511741897 1250 511740647 511740667
    0x8071d120f0f0303011e030201090e06010c060e010923073c06110f03091201060e1501180b0f0304030c0f0b0a0f021e0c0f12090f01050a0c1412 63
    0xf0364003e00803007416104818040c4107582c0c80d0004801240d0341039603400c004614008001d621440007910140c10011008250008140140104060301d4400703000005e05500628202307a40001c6803540811181d94407a12959100c80032030200110341490070f0f1003464200984d170101140d600104c091010080f90b840c02c08103500000d025605032081a1191600c514140340c005030f9812000e1408820f0390300030045003105003402d9650480c104030000012441a4442007000d0100c141141e4582004811a074541115a031081d08a06036001c101107655070b80f0b050010080a45c41000125a00c518001000c0f5003054424506054a650010101d0750780300000d1414118206040d6021064582840c207001d403082164822600c400c0c100180302840c21103c038039000c0d19500a0f404521103030203200304900380c014007400f000343ca03052001c00d100d980d0701c160001c1003811042c030558241044018081b070a4055001110000ca454001444403100703000c0c2d10410b85070008802e0101101320012443c4014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 511743147 1250 511741897 511741903
    0x1107060201150e10030f0c0611010e07061112030a1a0105040303020c010e0105090d0302011e02040f0e0901090c0f0f0902070b04060e031c020304020907020a0213200703020d08071d120f0f 82
    0x903542140e503800c000d00c01c901185400c0c0c901440400702c9940cc03404040010a01440c0b4050321142c03d074050f116074000c81c180402c25504111644c51840b61112045210085582181c1110f21000d0134810300381410341e10000d5441280398074140c10b02581c260341012a038040c000303941c80c03c0b00041008002c580c2070b1500a0280c050344800300700031821407109c1c04844a0500a07a01620600b51100451901c0d100302d20190990141007044e86540c0c4101e48070108540a0b03121300902002c03010b849020b4904411a2214921980007038030540c070500081001580c582e8000d50003035002040450380c0602c001000c0e003076119411071045070f609441006c500c01c40207074010350b1146000702c4103c45280d461100680c0c07a003020150083d071000e41e400c078000c0040c1041d8400c3d132100c0032511020100c0780000e060300100340d101540940150340501e942d090340c03030340c08400710342e20420b240b0346550301c5546404001e8807100c44070354180c840d04015500c1014041c040260100d90403080f4100e8119482e002c0445032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 511744397 1250 511743147 511743149
    0x120201090905010b12040f0501090b0414061005040b0f0405070f23041203030605040504080d0e1b04020d0b15070c06050c15070c020d031107060201150e10030f0c 71
    0x40800c8411a000031030a91034800c581c102d68010141a00c0c0ca0031940600107414401441111282d6600007d440412400d114403400507104290001c0300317082504001081d10300c44900211590301240c10040040d100071168000c07110162008282c1d968070350300040540201c40e1013a5002454441000245980104201180ba80d107481e50140000142103103602c1d6201305100005803c010002041000c02c0201d00d0086a0302a140000f481612800010140e40341580c1c150ba00000108000540210600c20603484610000013446000d800701941444241001c02483c852580407540c143d84125580101d8408400180703118170b00c641d01d5000000700e0f002000c060b1074031f01010601103840e501420445600c588038170300501120850456481b02e00744010281000c1001640f02c00005880d0302020b018078a06ca622000e2800f07080e080118079001c00b9900c40d004582c14a002e070484001c1e0808050709a54031004a8000c5650340b070f00c5001d50a41640c0020540d1107074000302402d011480ca5580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 511745647 1250 511744397 511744399
    0xc0d05060601030c09050604030221060a06030b06030c0906060a03020c161a0a0c1b0b07030e01020613020108060d060e071701050a020a210e1b0a050105030702070e1f1202 75
    0x807905000c1c8007190004517a004050300290b080100f40702600d03040000f004250f9100d00f038854442411000107041101c00e440484510342c42e1741051081085003540d580c0e102005070000c021810003280050031a0300c000d07120340d01806000600190662282d01103c002c1e203440e204a0b000001c021001c6070801050b44140b1030f48000050f01901c8400c90401282e4241c10103945641c52036501c1e0700c80f02c5558046a2000001080d424000241400e016000d040c1c09402a250110010004400a0304068000b40002c0e5040c0c9545094001030381c10804694004009640e0019007601c01c0c940240100842701090106210744940050390901907692401e20703181440081c04607485251548042e1300030340c00c02030040f410350300e4003240e2881c0c00310041c4003618501802083c07051015510341e0500c0c04a004100c600b00c02192140d10030305050040c40c2c01404286401442e52500b800025100d4a042c011703400c3ca9000440461342c0343d0031080d82071f84aa001321410041d00369544a01c410215107084040b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 511746897 1250 511745647 511745651
    0xe061c0f0b03161502150109050603030904090b0f010905010605070605090309030a050303040c080712061a040204060509040608070546080c03060c090f0a0e0103050a051c1d030c0d0506060103 84
    0x40c03000510105620041a558000d40c011b16401c00e03038210301a00000f8503280d00341c8000c1c020b00707500d43d03594055120603502809000ca09810070105d00f000c80758050304011511402c0400400685500c00c2c01c0740c00b040e030048400117260311241901030941c415103c09561501c030b4205484181f0002000660085109416000e10150380d1520301e074541c0014400c0248915214217a03030081400d540001d42002a0350100e038452100d0040044c04a80040e0411400200045020001814507108550241844000400e280d80c81d1900042a03603401101c581101e000c0624800308809141d114480c017141c4d401929a07d40131200301c030340304072a0240b00b0340303e01c0c3c031032010709600b1f9090100748540901044001c55182c00c0c0580306009a803202598002e07001080f00e0300c0001c3c1c0001850401d40a5031280000e411007600e141003003440d0480e01825410018500d072614410250401545400c900941c0b002d03400405090001904201d44c0202064101300c002110508109001c620188600c40036202 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 511748147 1250 511746897 511746929
    0x20618102a08161113062103050c070f090b040513030513030614041a060906060c0f0609030403140706120908040e0712060f0b18030a050f0d0e061c0f0b0316 69
    0x31785020b82d0700f02d104105042402940c03040401c2010703034454000034000d003007260ad042c090800403803824600c0d138081c9a01803142901409411800d00900128071402c0380c041c01581800440b004503824400402028424000f6035a45005035a20071107000f55000030381002a011303011140300e903001048604560501901c4a103603190000c145100d401001d010f007100100e545c0d000c060194070350011429042503c030b42f1440940d980d0081004520600c5c0400186450b03914601d0302d00600311801c20b1541d100e8114000a1107034607840800311110051460340450628140d0500b5112841150080c840e00c203140c100300002541c01c40c42d4440c0c0e000804c40104013240e0b8481d5400c071814a14022140c100c20104180706062851031000032000300014292018400c3c0d40d9a03407403402d00c800428260a41150b90040714050300300400d1519401c00356516450020380340c180e107004407140c00741d40000c966601d80740fa4112115030300c00442100050229280c200c0107101551250341c40d0b2203181288021070b12 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 511749397 1250 511748147 511748179
    0xd0c06030b090c070f0204060f030503040510050f0307120f0c03050f0106030b1c0516080f0706030213090207030311131a0903060105011b020618102a081611 69
    0x7000b40e105450502c0000e0811506a4815000100d4031806a80c0561036000100c0e5050303421000200075803144000756911840c00c0b091000ca10040c081e25010b101c0d041c095071080302010000c41e5408082842c1520b1200580b41c500c200818850020300d0050745030588a0402681581c07045004814810807031545030307a141021400d94612410698100b90003082c42e840c5150700c0034202060a115605841d01c0309020580030140740d13603171342c0180d40b01d50082e10001d500000501521010302034915095190685240100129400501c10740641c032741e001501c2014140301e907000168180c48408101e0341c6d42134490301d00007020a580260b202905514641201d0403503030724216800c650380900600b10980c6408019a140041b10a520b80070403d03207a44100140e4502c001020181004040706d21050303214030500a038609440d4041060082c0c180305004401d428000680055441442060b035945140c64941203500500011282011400304004100706100c082da03402d8030826190b50100d0f0744508 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 511750647 1250 511749397 511749409
    0x60a0b1306050102070639030801090e0304030b040503130b0904141e060112050702010c0305010b160b07030b0a080f011401030c03063204030f050a0e0d050c0d0c06030b 74
    0x40300e0b03a80584d000c1d8604102d200c0c0505a070090705044145924400b9900d00301904801c5041c10021041f01003054031a010540c10401c00d50141c040e050b003c1000341218000345550348140d0201410851006000404000c0100300700e8803642006190448200e644820b41d01c8990040c0a0b12880380d030418024400c4118440c0010344110030220880b00512012100c00d654082d02900003410804841480343c0d0f1801d5034007402e405a01141d00009448406480050465106812052010394100f004180d80c100c01413440344516084201ca1702c9a0700e078088141d0040c501c02c4299500710300074030380c00100301c04080b880000d0b80c200503000780803a40c804544007860360000d020041075a0700c540310a0011410a038025000711541981510224039035031030030081e8071400b0089440020b1007004002c105a0303c002801c51720581c1e403c01e13508110701040054804c484a0148600a052010f030240034030070100308602c21081d0140c0410010a02070401c0a500002c2e80640804207090548a0910b41005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 511751897 1250 511750647 511750649
    0x60109060215010b3001080d03091a100f032a051e01020a0f06020721050924030c1b0c010f0804020f04021303050f0114010620060a0b1306 61
    0xa880a50701d60b0910a10a48a030000501c1d171154032140b41046003141c05c440c3e505080c05c507203001e54030007641c5044950780c64490420003600030517081007081400200c00b00742c10410f5003a0f940c94807999903512642d43c21800e2107a80607140100c82d200f800014007422030080c9901180c10098403001c4400c00071020011900707840340a400c00a085403010000c1b10401011201100510580d0860310b03190310743c4641c06005483c03d0720b80e60707030004007501040800c188690f80c50b442036107500c02c40c001608024140d80900500c0034014064003054150003846092010303045c650380c00e080358407070074590280012074101c80ca0500030155083d21200c0070394000a04020312120507510b0900301001d1590460366140301070000c03030300070324001100400f99941d0f0000e07104c0f503113075161605202451410814684071715104454204e9241014100c102c5c004502e461f810f590441c14a03401217070040a40702403040d0300c0c0c1e01c107541070b01480080c03044035802500100c40c8034004075014100d0340703c1e0380807440840b405 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 511753147 1250 511751897 511751923
    0x1201061806051e060c0c030607110c040b0112020904060e04050f0618060a0e010906090308150d05100203070512010603050412050a1e09030b01030606091b08010302010c060f0905060601090602 84
    0x90302c001c0c24070301d8004010720400f00003201b034413612008040800d2505400340c4e1403501042d00c0310301c1a03c00030001c000c1d07440640d9044030203105413160000041c14402560783c04556980c0c00103120182c81c2c5458110500928005c400c1d04502d2034941829a1588640380d15400c07103010340704c0460403240d44190011558010343c0c000d01101d40b141401ca00c010b25a0160501c00b40d52244800c0000c03034018400c0c410660701a40340c400f002d29100590b10007042c00c407850140b245c0002107102021490000d40c0d86800102403800590ba61282c0100f41d178140504406405241d0003a0000710b4101e6143c2c000074011032050104548010384032200762100c0c06002140d4000a50341c1c05d003651340001c015122103c6041504240d03056a0300c0e07403541003110703200740c1003a110180c0f42c01e002c021003e480d10038642900130841051313180900c4c031800101408010b22000c1d040100f00101c0d03105008481d48002c2e09070000c2d2400300248030842c41c245484410480303019000c1140481300290340b900120b1228a03001c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 511754397 1250 511753147 511753189
    0x106090803090f12030d0c0315081b010c020a08070303230a0c080d1119140a05030a020f040e04170c121c020a081f03080d0902120106180605 62
    0x10040280050080f6407200250b100c00520051448003d0900c0100b920341900e44001c00d10624000000e0181d9103481040021401c004034200540740010803075084690781c406108100081c4000102d510f1a02402c000e94011b402010000ea54900080c00d2403c4a201e5283e205101d4507a0b5a105a80302c49440014140a41000014055803080000640a6206480705410031401c98480000c0fa0103104082e20340050005060407851095080710070305400d24a82402083e00380700c0e4926040c041c08020b80240f00c0041f0200f4103203045038050700c04a1100300e00d482d403111b6644800e4186504155019074000074000701d14292119468102d52502c2034050040130004021600040c055110086818a01c000c000c88258086c9075400103254209c0301d0b075107842c802d0804084550705a83d5511581c0d400d071904080030000188140c00fa1000904035a8000031101c0c01d6002250384103001c140400c07560f52904a001c07030034840800b040f444c0c0140c2110f041010b5515102072014550902082e22203000d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 511755647 1250 511754397 511754407
    0x5030c0c01090b240303090a0e101a09040f05010b03010510020a0b1f060504031505041113021308010e030403060915060b040315020901080601140c060f040b0106090803 74
    0x921948014490000c10100001d010500342e1a4500642c030700303a8440c05803411544c03040045000003c80340d154100d084019500e000b04190024181c01e42c103107d8010754007405030019051050120078900103001c041801c01400c1044a80b0070026840259501e00c50392410b40b1041d0a040075110b56410f9070380c04907400f032643c2d0810003000400d4504000c210110f2050f9a0003600003420100880d015104030280c081c25800441e5190900030355503008881041410302040010917a100083e8084009a800c0010184c03a43e05003180340d81a40200c81e83c12002040070481030541e10390080443c2c541030700303051818540780c2200900340d4400001c81d0f08140e00901040c000300d002a4403420040b8842c0d500107140740380c035600c28826a0300541c4003a19020010a040041c420321040040c101031456104601e04002403002a20014010308090b0411504045080c1e2015620088480404448040301d00314601a40c5801420700105c40440d00c03540300c00000212a4002c40444c000ea51741d540c0514281 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 511756897 1250 511755647 511755661
    0x9051303080903040b1210050d050a200d0323041202041107020d0803010612022809350607020304061202040b04060e091b1606021911120702010503 65
    0x907000600044460b010030800001d050308000010484501051a000304a00d0f1021000b444803e0300d42c4401d00800915004400140000c1111070100354046200e2601404000340f00811300134400d803041e0058014281d00f07081c1074100b040a220030f40c400c00d00d1030615064020070300e6a1700452180d109050300803d101001481c25800480620381e620f105641444040d0700060341010801d00c00303540005e13000006215007948500e03c82c19054904038103616143d0ba00003102c0c0d0010380c401c8080303448104075204240c014801e07003c4c40d0051420088000651c0003038203103c0c5401d040c4100d4420305040383d9807401188000810342c0751245d600c81d00510704061601030300740e0760b0740052810010b5207642003001140c0c00074144050300143c007980c0e580203800d00d0100c1c00d02068820240440f03060a48030a04c1090b0340f0715420845019440301d081203060a01c0b28a447c1c40640240107400c0c006821b42c6000e02e2850341c0c08030404062443e4070048418501d05135400c1d0078280705085e8082e001500800c002118 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 511758147 1250 511756897 511756907
    0x1b030e0f04090b15090123010e030102030907080601171c02030c07090902120615010507050f190302060c0405130b01020f010f020d0e1507030b2407060609051303 71
    0x40580094000d40d02003011200150071922052012035030310041030300348007200044052521501405440c1242e455041c81c00262580311090362a201f840d40d039081614083e48100100100818040c00954990408240c010380300c1030070303014100c05441603800006494005181b016510030100c00684192190b035003140070f0780300380c031415079065100401134a01d900c1d5007000b040d0010314081c00001a0b5490303a00c100b18000c50200d0034100d0355440101401141900752800c42c0c0402004d09141e6618000c1d868a6414880203011030100c3d400390480c0816100c0104000300071162080e42a10b006644a40d5021280d000b64041d540e002071840e45540380600700c0740e2040c5180c0c00140121660200e056042c030742511804110f48403eaa0082250354030216503000d0031f461005520050034402a00480c0010500401006401055181c00018900340c640d84046100c4040341a410904100400404101580700d8001243e41d280b8040300080c4540551252a015400b40903100002c03e10310b0b101158 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 511759397 1250 511758147 511758167
    0x10b0409080315010507240c03140c1b0102030103140f0303070903020910240e0607050309042003010e1005090f180717010b04050f040b0a0207050309120a050c011b03 73
    0x13050290801200c40800c0364841c3d08404c00340e05420600c0c02c1201401c001081d10541080e80c1c6c2418100748441c6954901036404a50001d0020045a22001c0a0381b0034002c002103d05685025440040040103001c1881c07180b0301c05051703c501300c82081c030b800d41c43c00c0c0d543d201c11100e400c00140c11a00510052400030003880d0003013110010040255115000c10701c032021024920b0f03a4a81039035940b40036041d0007050913220000202c681509003030503500c9950710ba200304060284560b695816202070940e6265040340140e081040903030f1650307100d1103410b10110058441419422440300b0006042c5800c84605104012a94071001c0940702e108034002200300801c00340400303018440011880341e0600310000d00412000001040c0c110004050108030fa0780030300b5100b28450004204404900e45140305034020103a00001a074403451401c0040c294020500407e83c0401c41d02c0700210300040014604039034601940580e020314000f04015503600c400341030043e0203038102a0040b0042401004951 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 511760647 1250 511759397 511759399
    0x3070b07111e0112061d040c0b220807060903030503130605130b090d020a20090c040503010c0c1502090a030507030303050121031d060d0609020c010b0409080315 71
    0x281c01e0000c8080052480c140c06840c2450003003030704140754000e40c1c0c0030443c1c44800c1400f00c0100081c9043c81000810621882d21030000c40d90070402003810441200084402440c079401c0c0140c9610302e2044022916030f107030500c2e8040305160000810000000306141080b0741180e110032403031074078644c6d041d15590801809580c1954580310300001180d003a0261903c182d45608043c030780000d4605e4400402e00014200303003140ea02c8984c1d600415038000035400f400036048990341a01d180c946500485003414203110703a800000e00000d200001c1c030000c0280040d42d400710004e0100d03c4800c5c00c00c0310140d1503090003400ea00f2503642d500144125a41c010910510090800b101c213503100d4840619101213544110300003556540100b161070080c404400705606010303060903258101c0d46004290045010444400383d031144002c40181d511841118030750154800144400d136a9100004001e41000d150121a942031803040c1c0c44600d40b0b4400e03080450792000310305041d9241d038201d4000d9030203400041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 511761897 1250 511760647 511760663
    0x11031213080705060a0501090e070f061b21110604050c01050c010603020901150f021207080a17070c02040b010f05040e04020a030206120403022e050a020f0f040e070503040203070b07 80
    0x88040f0f0028000320340701c1c0e14a01001710741945030403040012208120041c80a5420a103014003040c11001c80f5101100e4441c580b01003042c010b20700c8003150204c8000c0007802a0350441242d1103088625154084c406d0303850316400d80461040c0310f8a41c80e003504440c008c02c035400200f003040e401e600130800b801d0f01c00a40400092541e459502142000b0005c0c0c02c1002074180c24101b5410ba40c0c0e00003880e400d0000280701401c440440400702910314001c401c401003040d50301040040034036105068541e8641c949040002c502c0c140060064844034000c44107900607030a124000045c3c0d4014050304100c40260381d2080d181900d042100e1051140c050012030344802c0c100000009680e564000d80b0158609141d040c92034101442c01a01d015048d03409020300715140d2003002a015200310070086211009107001c11680c0d24080301070300034414a0141110f12001142c024010038030f840141068484811048a40740c58541041e80c0c9408100d40003945640204070902070b0b032460704080d100b07107841500c81c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 511763147 1250 511761897 511761907
    0x150c060b0409030c1707050604031115070f030e010b0f0f1302042d03023006010602010c0207090525090f1502010f0b060a1805150a1103121308 63
    0x34103490b4500c0064002032800200c410500c810b0b04049a070102014641d06c1c90201140d8980b1740311300340103002034240024980541c1a5440a00c1a08007821442c00450300e00c1c505400d001c2d01400e1250500c000107843c04880881401051168050604000700584000311a400800071446d86a5800b5030300b0500300446c0805500d140d0010b04040c12070030700700c4801c410f0304404415250144505100c2c0c40d610400f03007000542c4401c000c600910b4491191030240048110060213081000b00c1d110710b042c0324540000a8139503065010f600c0300001e950a560780e03196982034050a481058607130900c4008617810001031030500c5884000e80444a00340614016a5481d50182d0414075510101c00c0b01a03017032054080580c28070079017980000030402000200d08180104469000c0c25694100b44904030070512000c1e00f90010a10003001e0007800d14003030000c2d48444440c035400c03030a2482c010403081810741c40088404019946801101c00e07014415540e0f820714034100ca5100c0c401030f03580d2201005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 511764397 1250 511763147 511763149
    0x10302220e070608160203031003032708160503120d2403080432061c0e070503151303120603080705070e0106030605030c040c0228050c0a150c060b 65
    0x4140300601d004d84401e852403501040e8071509440502149003150010010042101c410410080c19250035140208201070030703021665024064441d040440805410b0000307810348001143c03804101c0d00070395645900d6603241416540c010404101300d22a000780800200f00c82d0a500058090001a174007a481a100103004c492900d1a50410386100d10001000c1c080000040543c481450189030403900e03083d0031801d1810590b620484487c0b0078070000910144107804000506c11a581301c00040024058400d001c60352186c1600c1550300900503075003180701d00281300d0400c5d44504030750150209000140d5908460b9160882c841e01803c0d86d4506011000c2840b00002e080c1a9108a00901c1c0041c01d00c40780c00c0c03207040d05a1224007010704059003485152800305100504400607180801c4202c8448020307410000102d000c00d00c9030348403481c03c10301d9802d050001702100c4c0c054030550b25018080d105000301e00e0168010b03070f00c0d100000991030a03110300c80d20f414111540210000203403551240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 511765647 1250 511764397 511764403
    0x60c01061d01091505010210090501020904020406031401140105190c0f030309060b040204050f060706060509040c14300f03040815060d320109080a02060708010302220e 74
    0x100c0700c20011103540050041440610545101c03800d0540b80d50f25040c83d0000003555010810100c2c0c246548808940c01040025019030b100c040e40100155220703a00c450000b4001c0c28801c000a120302210f900004900707400190107a8000b406a5595140c140c4500c0450000c0340110441d40400070f02812090200c0c0d100903030311003400e2080e40d012484070041d041182c10f45120f045558415803041104200c95520761064500020003038a105888c0c283c0c2e82400c81c010b1505070b010382d40000c0303804201b0040003000d002407000d0b140b0300c0c036814029007921400d10201401d0703002d0b00c030203d840e1890366200d00d188401da0392042d8455481141e143e21f003640740150554005601140d0198010072200d20010a50b90302c01e03502c2207040e40c4840101c1101c1c1c964860b03001d84540c4415490340500f0410082460180c40301c41460358140c000c0c0108001d07031402e2040341e13100b42f03401e40050141c500403485181c41405d07200c2c12650000e25000d0301c14040e004140001da05002201308503543c600041c3d480312818 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 511766897 1250 511765647 511765679
    0x80102030106111b01020712051005071806050403020a0b0c0307170903010c050909280c050702040c032025050f0c030d050a12020c06150f060a0c02060c0106 69
    0x59407a80a1000080c0003e480c118426400c0903103065440544441646d0000d10324044410f2030b0300700f000481c00c9050090030b103030b804440d81590301d04003030030001041c0e0054264404807148a07a0700d180a0755034030003224140201e000c020750100340300704100021846c04c07014004103103001050760b1034401c00e07070349808180645a02c41c101c04000454241a0b51070300703100c2c0c0000c840640c2011403610740039a00054950800501c2130a5044103011060145d000341c1c4042044828030307400410040741105405442a0041c807005ca00c20380c2045088d1020b28400c1c02201454840e408810084594001c1000075a40101800642c00b600c00300208503400310408044001341c0c0140702801704070b280c0b01d500c40e061071200d40040c0c1c041c1c1e02c00da46000109600c0710444150a1891a00c030109a80340c9080300043d100f0500305405900c111402e000300451a60038a90581c581261040c3c038003160f101c00d02c1000d000e02442e40d00071490200b1907002508041e4000c004a85040c0b00000b20542c6940c038500310028a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 511768147 1250 511766897 511766909
    0x60506040b03010e0c1306080604050102070c17100b130f05040b01140117060a0b1902061f0506030c070b010b0307020c0306131b090e0a05070f03080306190801020301 73
    0x454050015500306482884040c940940c0280020fa015400056580c1007184c0c60340d000d41a2014154400b003803581c070000182c40c1040544101c0d042c9410000c1c080d4000d00d44c203a40b00c3d03210351000100950303c2c5071419046c0400c40b0250001710101e035205d000070140910802d030400d01f903000c0c0c5021982a840344280c001a00907001580d82424104144c1c8480c05803c602540f602c1100d011402e81c0e000808901ca0210941c524100c0e6a1150007068204e602c41e0b00c20032250742c010a000c110101c130030014225003e45503007101c00075921411107454480021400c207001d00c0d41810244140e050a50003182e00907a084051460554295903003a101e01c8241c1c0001d141d00c0000c408e000c8103030b40c14800c80e02001c0f42100108401d08222404407603080d03400c1c40c024003c020070301404120041000c145002090381e1041000315000301c40440c0c0e2240903108084a070b601540d1030110300c030040108010203485e0010200343c01c1d9a20841448807061041c0d0307100030114002e0700005039240c0b00740010350103010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 511769397 1250 511768147 511768151
    0xd0216030c05012115031406070e060c0c041119090b1c06031203090b0a020c0c090a1d07080c010903080f0c1c0210050a0c0212030c040e01120b0f1006050f1606 70
    0x40b45040c544687c41c4001001070b85a00148180300782280d20460705202110210f034500d039562407400210b032519803003101075500f02d420603154550340c61194000d0141e407500499084c544104a4000300c0350140720307020700c0c0b9541c1c0e024404200c03000203841d0540d00e40004003400144480e10f86e1207060760305014540c024000b0391100c00d980104001507860a0301300038610741c01c0d41004001c1940f0b5482d5000c0710030743d0380550300a070001001c07441c02d9004030000400c502c18040d08900c0c401003050b150715050054a080d44920768000000c2e510410b202000c481e040b4034458148510031813403041e01e40c803a44da082c20911607040c5001d050b03281c8541d00c8509100c030b40c00400912030180c1441050b2030004200c013000c00c2c80e14200c810b11980100300e10103500c030380c940c405599640e000500c803d44d0082e41c05c0707042d01c54001d07000440c03114416620001710600500c3d01181d2a9107040c100c91081c07808580030540c40f40c000c40f040101c91b00034009403a68410400e00c25040140c0040c8040c88105050030503601701d6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 511770647 1250 511769397 511769399
    0x80f150d050a1e08190504170f0c0d02030606040c0207030b0a02120123130204170601080610240306171c02030c12090609060c0d0216030c05012115 65
    0xc5681240300703d100c58200c29640b5081c2668449910a001d000d895030080c0c1c03403044001e00d440f03208a0440300a0280b540c00d400f000e2124852403035079800300c414101894404c880b08251245008074000394410380c028000d00c21603550900348405400403032500010b6225024011000440c1c0100f210720800c0c03420320060f1540628450040c1d9881c0c10f0744041000340c1c0d000d0b107451507104120ba000000340702c103035a000c0200840c204150001e10450b0300500c0790120a6080400c2c2400c082080b60490f6038000490340244c07500072001403d40710500c900b160130100c1400b0315100d240c1e001489901d8006c9404e0000e01d6540c0c4004541d000904e20f0300829040e0000f0071840c15044481498056110542c401141440e0803461150303035440c6c5102035071203001008182c0c20501e59071041118007000d40500403c2d00d0f100507044007540d5450031315a00c400350103522500e201025440182c4004c90350000c9045d401c0901d0030005640900142e80d454940d0f51802900d000c40780414000e030740c100d682d07007000ba489031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 511771897 1250 511770647 511770653
    0x2c24030c0d03020a17120a1505041b18080718020913091e0b06130f0e0a022d01030b031c0e032503111207030f060b060a080f150d050a 59
    0xc403400d218158010818400f1000412100380c0140e400880700c200083e101585100340d508e10600307640240d60050501c0c01200c030403100e0075902401d084603516544401c0f5502c05150000c0006409109026808070004014101c01d210700340081400062006261110340d03004148135120800310b01000c40d440b800c01200300b00c8145120001d040d003440d03402550902660300c2c3c081d090030240c0118031403010f940407152040020341c884107040445180c100300081880703211640364080d0801c140e200300e066801c8155203400030340c0703c1c074800b8441019808684410740d00660050050503400390b0103102c0c24015101404006032015024046c940303c0c048680e0001e01010b00d041c0794030808541e0280507186582141000d0200f540580c1d82c441000c504065031103000c1000d078481040320340d06600c1003070400000d0110310024100303803a005e8507041c040326440d00280b0040317225406a5000240500300013a03c00c280595034950854048000800c001208500041c0d02c040e01d01015a400c0e0403801e420010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 511773147 1250 511771897 511771913
    0xf12030906050901080723220f0608060409080c03031e0a06050102120705120f031b030f0402040906020c0a030305150111030f07030210062c24030c0d03020a 69
    0x24081482c201e072801d022080024040880036140c42e0610841c05140c4d026440d056500c4241011180000343c2c41d41e80140180e0303910041c246408032040354512001c2841014100310a0a850311501d42c8041c0b82c03986014080101802c0c041503070001400e0084458121f000d20055000e90301da4810010b1032500b400010380b0b40e00001d0100701d6801d1410030200003698020038103c009541d038882d440c0e120407039424604d040c02c10b000008140303200006007005101c01c0c010091405604110482104030038280314003019840151004206440780078009401171a2075081a0200c51090001504016411984500c0c5c00c42d0750b5402c4000c40d84540c2044140104840600380200c402d2802101d0034020b003141c40c0c0c4a10400d14903810380140080d080c4203050003040580c1e09260401d50420003030b070f038401c10008050018030101c00101440713000590704290170440c060140700d08005a0401002016007035001003e140911900f40c001d585040c0c1c4140c1d12202843c2c1d0460198024280c5d2152526000301e03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 511774397 1250 511773147 511773149
    0x12050c150c12030901330f0b1c14090d0e04200a0e0306070c061505031b0d060501030c050306100308070b09010e0703140c09091009020a0f120309 64
    0x100c0c100911040481c2000020800140c1c440d00200994036241d80808902600c040c00358110007a42c520391440c0c00c031602444e42c020038004815112540358031840006006000c522525844030340512140d0010080c101281081400407803000a07821044070a5040380f42045540c28056000403000e07200d81c0e0b8110343c0b10000c0b084115020030440c0b0020800104460442c401c2480d500800f05010030603e0180584150f8404020204d0380c0030311b00200e000340320000c1000d08031440c0342070403581801c0000301001d8200703030340f80200a448050701070340500610104500c0c8082c0d11112400242c2c0201d65039102e80381c06036001d400b10041c65400d240602d850b000e400341491004400024080002c10704900c296201c03107034014908100c603200ea0006a024020301c805400c4a401100400002c10280107594503102d1003100c00d540c2c5c0b0700c40f088104141f102e000c903001c0ca002e4021200800121090780d00c11240c89100a184c81d185544a0030351880c5210950000144041c0103c2035005142d00400020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 511775647 1250 511774397 511774429
    0x6061206050306010b0a1107030f060e0a1a092107020f010212070206070804090c030e0717060a020d020f0c070602071202180405031b06041208010303020a0305030c0412050c 76
    0x80300003898840400c0e9201c1d414403552101e000c01240480d402481800d81416406802085030000303500c0f4248030310705406003041140c00d04d280022981505a001c5020381c103694001e95880300b4040a5203509d003c1e5030b00208030b0105801041d41d03c0b403030f085808020104040d265045251a440c05d80f040c071900d030211503d01d5041d544100c003000c00aa0102086490301d59064840c2074480d80d09103061000b5026507001030303501c0c07801d20441400c42039143d404004111000400c44000b25070303e8103091000d451811121015800031800906154500c0e0000c2045101c041401403034411480c402c1c01306a080941044015000a601002099410002c00d00508900346a074038601d105031780010039078140e0416440d5505181c2000a06201090081c0c4980c260340e11248084424a4454541c41d20f00c02c480440314000c1404003600074621801e901816030394150010b00201201d03480c20340d000d8000418071007002e0b400300310200c0e10305011000294220310a03801070800c052071208118044010061403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 511776897 1250 511775647 511775651
    0x5150604030b1b0d02030112110a14090c0d0c05040f0b0316030f06050402040b09090a090825050304090504151506030c090b03270105040203100c0c050106060201060612 74
    0x91002c80d8079030074201e400101e0008030b480c001c4024100d0343d281c4d0049084402e0100d00c08400000d1000c600e5503040c206600c903940070307009180003030104905044e2034000c0b041c21184141000540b0304000b554550481c0c41341c0030942c00c05550200b48000d42c0d84042c04000003940c049410080c0240c0c8a0800c40506864400c80f4254034121012054010f0758002c00400c01d5110000141da684c580e9000c1800380c8000381c41035580b181c41e0400c24280350304c8001554020461130001581c1c2c18030a204501c1c0d040e60100320341d0310742034401954801d40c0e80e20480c40400d1812044040700040c0c0100001c00050580303400c00710311442c4c80c0c202050051291207128800a082104a050041151002005644090500141101c01800c00300e0740440c941e00b00c508507900c00400d02455003484100b13400c0c41c603450388100c03d03955004070b2000d00347e41080d100250036a00203a2641100e941a8000d0840c2c0c280f1880d01040c4050142c03100c03400d5400560000c800350b59a00d406100c01c0d90300120082e02803403da401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 511778147 1250 511776897 511776899
    0x2010e1c0221070b07021e0a0503030622090b04020906030a0c0b0c0f0318030c011b020609060d0c11060c090915041503081c05150d02010e03010c020105150604 70
    0x42e44480d422810148803602003070446006140c8141a01c01403908103102c01c10603d0305500103941d4061900700c000601c404a85c81c034420b642c00181102c9941e0f4490040d50840d1544002c6c445c80e40d142d170f02102d4005a0b80142070f0a0010103100c1c240342280124015085401c1c2401031100170f10300501b2140c021340049da80d032404200a00140400c451444c115150b443c40c6040d481800e08081c464454024040043c81e0701d02ca80c03c06142103031814089055505605c50340005444040030030b035000c0c441c048100040c10140c0381110151004071b6003e44064503140c07025811100300c0e507408880102180c0f0048011018090400515901c880440940c80ca401d1411000a6807158020040c51030030700001c00c070a12580b1141c0104104c4200d554000c264180c40b403401c9a02a00a4000c510364802544500d20960410380a0103000e1020340d84818030381c095141c01c2c88142c040403801641400880c90b005d1926880910401030114182d5000150b07908100b03104aa01c5041141218850101400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 511779397 1250 511778147 511778203
    0x1060e06040506030601080403091a0903011505010c060e031c05040c0b03060607140712140c0a051e0127060917071203020a08070309050111011e020901090504020a02010e 75
    0x4204d0342c01000c00d00300300f40710356224601207034100d070960401626011120050115054804050320b08000c0480c002c2c0680400c0794401d5a4858103880f829000455064410000c00c00b00d03400b0342d050101c3d02c025249010000e003414014005019210344d8056079a2041009000406000300e01908246041d10b1440c10500005046030080001c064407a1a911800d060145d81c2005010014007080a5031845039940b030903c907641c3c81d83e10f03400c12098061900e044502d4507240c044d81c015210003c040680c01000c00c0046504100007041c0c40e418803400d4405000d000c2d501d04415032000211140d1910500c0c201400100685055400f1004145405043c0d90050801091010a44001c2d60144d00a0041c07410201c0c41c190f05010043d040320000151403050550101e0340d0f000381d802c01e80b65410700000e11111542268100b8001c00300740703010000058602c95054004151412052501c40309407600e031400a404c9910031814500584c0d5514008a031418007402000b84d9852412071115084020507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 511780647 1250 511779397 511779409
    0x305120a0320040b0d0b0409030305090f01141b090301090c0501141e03090319080601110f0a030e040f06150311030408030c0702041407020f07090905100509070b0c0601060e060405 79
    0x80100c01412402003170006081a95900031084102c0092041c00a00800c1c10701400405050340e0704082c500070003004807008001401101c440d814482c102c4000c43d0342d80c400c1006405005da008148802042007850070945d024001c8408035030158050184040c0f4180c005009545460407a0040c0b02060040135595981d4040c40c10380748120400b81c41e03580e5610306407581148a108507504404007076880801c3c180b544804800e20a20003030702c94030941d04400c1c040584e03888a6a0080d01141d01421038a0006880307505e420401e91400307000865801070035000c0c50305485c180d4000e0404e4420141e0f00c1040300703600d0b000f250101132103c0ca842d480c50801d601c80b079000d44001480c203c07103e000042c0c082c0c219201d035404a052864445480e17402d501780710f440291112100248404144140319012404840300e04c2a003015681c00001400020f90304181d05d07000d0030006141c0b41d4680605100011b10014490041664210517030103059103604180015140105a880356400b6000510042c0190b031505 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 511781897 1250 511780647 511780649
    0x8060c030415153f0203030702060703030902040c0309050a022806030e060606041a030c0706180c05150a081e010f3002011d060c011406060a02060105010c05070305120a032004 77
    0x130100110165960003c00d14500c03036140000d40101000490b1410f060381540030300c000500c01c4606000d000d40f40d0030102c007610211080074040750026517141c1c0c01841c101d105110207442410281c00074008540d80c1500d50040307607000700d010986641c0700d4002403005000d1030358043c0b01152203038185410150020a890440f15280c2181c01000000c65002e48412041e00c1c00d103a0701440130b00614040310344550480c007a00c4011a000e60110a002c02d0600d0705021418401c0c0e115031109003001c80c0141c08030f880c010090a02e0b5022014010310040300d0744040000c42c06050380750720b041c202c81c0c07400a483e100e10200f2103001d40014a41c0403400080c10909914910958091801340fa84030414000798520412034205994030520024104d030501030190040b43c00b00340c1010700b09446940304002d02450340301d41e1095000603048800107121560288210b00b130301d1801441202e1419481c2d82d1340d58a0940c1c034104004172254042030385540168513001d0f01c403038001c40807252808106400b250189500503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 511783147 1250 511781897 511781999
    0x32101060e150f0304121d240d02030c07120e060a1d0d050706091202030c040e15040b0118022a2103040204060f08060c03041515 57
    0x44504030b840442c2d18207007076400f20144040803d50b07900b014034100b080940d5051415000c50500c92011552070b480e40031880e203150020f000e82c003c0314814121000400e4006094050902007440094040705052015500c554401000140c0d11225820701c4031142c04000062420000d0507501200c464070f8a809039121101a030511911440586034255082d003001c1000303542080c0e840319020140500052400d04039001d035140c103002d072503c0d240d20300343c1ca2415140c069003652181000480a0074290300200c0c0c9c2d1840030094518002e00441049081c3c10240e03815036540d400c450040c440f00450101125510103000e50840c5420031401d40b0000c5400d83c1e40508506020203a03003084922410311020301e03103041042c540415074558240010f100c1e00207850682c012031400b81c011541d281c0e20002070042d16065001001280c0c0d508902c0c6d0090343c0000c20442c0e0511040802c10b660f4100d50085600080c0703c0d02d96030380141e00f007408803800000980c150500030b2076180d014000c640019174441c1c00400c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 511784397 1250 511783147 511783159
    0x5060a12030c17120f0a060b1204050a0b010b0306091e13080408070b030912070201021c030216080c100b220e030301180c05070b0112150e032101060e 66
    0x629090180d01c1543c5202d402402860000c0c0303a450b0301510b05000d034424034219201e8800d0f03072a102c40241c100d5246019909032041d04202241d15500443c4104d503210380b00e801203441e01d018a68510a0200c400e07440341d0b40e0b02d140402071108901d00012601e90040b407d10b010f41201c8440314034004000c1c1c000d403441110f1a102c2d0417010a22841c5030481d400350600d403003100e800d50360b0740005c0803050740110f5020134a030040c458a01440221901140c0409805900822900640c1610100c80b0500201140103155003001000000d4010085c9508468003801c101c0f42ca600c1d0080109041c609240310000c03d082c90413031703030242da941d91004c0c16040d48030140501d9454190034000c00024101d040c003e59481c4004800010520301d005515004060050410b116000b00b607003068456005d451002006400c40000500601d142d0074450344000d0b01608042ca04544403020030703c112848000011625040010710328101c9940b2a1403002c0500d622401421039850003000401c1d800980c90414400c071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 511785647 1250 511784397 511784417
    0x3130e1308030a0902040e0a021f05030c030903040305070603020d0c1416020d060f0b010210050c09040203130f03030203060a0b070804140a080d0207050a08010e0703110310150905060a1203 83
    0x66a0f07039100c09440341c2d01800401c8040d2600c40400c0e681c90705a682244210b100b0215200c01c2490280c3c80380c120300d0241c0314107045455604010041c0e800c0103080501c148018040000807600801c1070600404d016140140c2d07509850101109944c641c02010703040c0b001c4500392480c0078041004a40d0b403446041d600d020100000d10010715a08100e040140596050009011b420381840e4032003011880c2c08d80844074003611568444c400e0b62412505101c0492042c0304090032030509030011a40840100d52118008180381d4480d0600c0545440a0700081d50200c100091801d08003901c2d00500340c0741c04400d0402e1031642d00c60989114a0040340701c02c226620032040c4503103800794101d01030091a82600d40b5035804440003955019a4403407548076500021000a58138010f1143e00b00c04c600e140050180242561140f201c4030102c2100b80d0382603c0307003410524481e6140c0c49400c481d0001200c10301500c2d4548045072068039405400540305040d1408200500c20300800085070307030f6506041031865a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 511786897 1250 511785647 511785661
    0x31119030623010f0906060206090a0b041505040b0601121104090c1803120f030b030d112802040605040507050a080606040b03011509061805120c0d030203130e130803 73
    0x200b0072044030302c645000d44000310301104815a0b1a056404000c0d04001c0c003a42d603601243c0c1c030741c801c1d03405080603040688040c1c0840c2a03c8000d6074054011000d01468038400d000076000c0b01c0e8111030136100c00c81c401c02400507039070b844000c5030700300050090280401805c0d820140001e10440c400c464425950324429204180a41d11984d28080b40001c81200543e503418290a41628039400d130300014425000c1001207406446500d1005c100a4024030b481c04412409803000810f11309112114840d4803d02180807403520700b03040030500e103401d04c23403800f007800c1c41800181d40d60307504010710880c103002c200400c8075884800c1e500f0500306864004626195500400c0e1584501e4200040449002001240c020144915009529043da84681891350f4035002141e114a100040050080029904000700c0c5007190300c858022180000350384400c00e1000002d040d0103580da40440140e000442d620b1004155201c85000500b4001c884c040640f03400303541544000c003400c4005104000100c041082 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 511788147 1250 511786897 511786931
    0x110607200f0a05070e0a3804020c010b011707050a050315100e0126010510180f0503161503020c01090b0117010b0a050f040b0111160311190306 63
    0x480d00002c1e2407071204103061080d11041d0700d026004008260707001003800035800b813003089440080000d0300010b5122202002e0040c44034590000031482d5810301240d502c2d5110b200070003000e00d150000003080c482120000d406400020101c2104062040400c99201e03040800c80301c00c00414039103d592640e8000d40c04015000c0d1011054009910305080340501da0010032028205500340c8425400b0141d290b0704101c00b000c1c0e2000c0042c07812201c001003105003090303188420010b40740c2c200f0080c58a00f11500400f03440090f442090504d40c0d040c0b0070031035814144500d83c050880ca02d03c102c10641051040c00584c011002260704040d40010a641c1c080000e501c0920352503484120881c86503502c4500c1341c41d05940a0301e1403e0340d484c00340c801c1e0303051030000c03400011500c01401000000035410200001801104406030611001c0c1c182800f00300010301c0728014a580f5440e16602039400c0d4100a5500d1030102d1215000f03c681d080c810034442031514840303040740c1d441000403803002c50b0032512080c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 511789397 1250 511788147 511788163
    0xa03170d05010303050a0e0609100806150c0604030e180103030503060103060305010e010603051603031d030f0a0503030412030c080a050c0f0409061a1201140328020111060720 77
    0x1003010329240c008410182c2c09002060401800d5852100068030b01040000c1c0e8426001d42561144104414080d17090140b410302d90322140080c501e010788200542000c0c41d039480480403900c0c0f50072400822081507048900441644400d842c240c400551803810110140f406010140c288040800040c48a038429001200030311b500130020301844200e65002406800c0c0380c042200c8034080c0400c10100241c5181c0c601048a4066840034280ca840d0f8000c8400b4124003180141c00d0300895040c07503040ba01c204040b81d111403080b001550f482c034141c1410820720303540782d40c0c80c070405052842005003554001c00840cac02241c170f9040040c039515444151113941c0708151012140b0100800d000691030050b622034800c0b260040410b02e000040c48100741d40f14802d0010005450a100c0014090b00b440401e0301001d01c40090304450340c410401c243d0380c0340722001c00040340d03503602165201c00031564040102549141c60b0700041c28142040c58025001000000441901000c1e103000d1000036a41001000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 511790647 1250 511789397 511789417
    0xc0503091905011e0c120218150403020910090e150a0b0d02032d010e030703111005010b0903101103131a0a1506020607050702130b0414070f0e0a0317 66
    0x420131130a01e91052001e04138003242400440c0d0a00190808011240200c07039012031701d0100910703101350940800a1150841c00c10005008040c480800140c4401a0032406030400400c01d0207010714149410041e2440e0840703102107030300209010a440f0414422994103c0030000010034410000408946d00c280c114070080d52620070f40c082d90004455a240040300e00d0384000072046403407001301c00c55081c0c0c0c5440200100640c030400c0001c012a02c0b078810700e20707001e00c1c0e101a0b680c03400882052600f512020380041c0c160100c0040e100780e451400700080c0d6004180d0b6042486882070817020307200030380001401c988045101442ca07400700698900720300700500c00804140c0c0b0328101013210320006e001d40c0480c0c1888019000c0c01042c0c1500000c2c22030b100d026680d85031441d04400c4c0c4d003400800200d120002c40029182e60b13440c0c05503600c6000b10049400c248002c03051614100b030004041b40c510881c02c038180b0079100c41c0351b58135031503625900381030b66000803040c070001000c10b07400b45030744c40344841c0e02e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 511791897 1250 511790647 511790681
    0x3032e0303050a020c0103150308030403050706060602010203060406090b0a05040e010603080304050303090601060c120c03171501080a090f08070807120309110603010b1c020408030a020304090c050309190501 91
    0x100c1059001000341c44414425402c540981c2e0031400154111030703820380d1400c80e6020002040001603024002190301074424a811420a1a940d4a040c140d0321150048c00c0503075004410090a814244106401084400e05c14840d0507006408114404018000c00e0300664030307601c14864000b025000000110340c80706200c0e03034034545810401e440342c205441c02000c0d8051000001841e5204111145589030005009650400304107019a11b4100e11042103080c04110310307408606001c248003c510441d0140d24000e612120f00d4001000c40750010104038281d03180075086008549008001d200311035104819a944400324188150503010f6a0402820b401e4560300101440f81e040d040542c00d14400d028080700341603c1801c0140a0209028100f50701e481800704a007030018a40e00c8000d040700c0c4000062034a40c80b030001c80e0a40c2e01a0444c1d130056030001030100501503c0b4480c0c05150703105442c0c050f0550500282c0d01d6260454070500c150008a66004042840300a6100c0750b403038505841c071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 511793147 1250 511791897 511791899
    0xd120305070e100c1a0702070902131512140709060507020d08041716030f080706110c010e1005070903140304051c021c0231020d05101703032e 63
    0x7000c1c4400010116001c1c01a0740c5d8400c000301900c013a040c02040550050035803182010720440094000060010240000e428001240200c1c2d40c1030151444203955030000307826440b2541c2058645610b40300119116080c1000342d8664080241002d945452401c69610440340c00015161448000041c090201c001400284045155540c621200301d50056842c04009030528401c0080b2900c80a00603103062808400015103540c002c018151007541c00181400300d00e600b91403c0c2e001168000d405a44d60301d40e10346010410411039581a5a07108288014a40040700401510091100a000300d0808504011041050042d10060729002d85035440350a40b64003a00e10140b80c000c2c00743c0c00781c1d810340c00c451520020107180b26050380d00548800c1d890745e1022091806c00095a0f044110440e543c1850300c0210001c0c0020500c0519020011410f070810540141c10140f407a8050040c0c102c4e4030000d003002c01c80100c03d682d07106615021000300d07401141c008141082401e130001e01c0032840d480d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 511794397 1250 511793147 511793179
    0xa090815010f0f050d030c021827061603110f0f07030e03150f0a0b0301110415050309100b01030e0d0c060f021314010507051005040b060d120305070e 66
    0x9000c5040b1640710220110080d603c0f1160885002c150182541107540091007801003400b40c02110003641c0702070b00612256080c8508c01d240c07040103484542c4c200e503205403480c40d1a040e25a50329003840c9040003411035401c00c82842d4105281c2c0d15803100500d6107a240101040b000c45094510300040c400843e5502c9020b03805220441d0300c801400c602140403d07510110b41c2c1400105465001402008450765854102c4801c2e0282402800b449149403a8105000c46440078019603081c0801c0040c0b071500c850070f20074269280ca41e02c080c1d1108100041c030030002d65403000110740a680818000005641303d035000104d0151864040340c0000d44540c161601145912900011009008540c200b0821315000100c00581c440c040c4032410b00507541c0418000b0204800c00f000640105041c010304e08030031982c0301800c3c400b40302c07208801107607a00100028401c280c5161036120404607960403070003040e565900b901060401000007090345d200c000a4519006e40e825070800c0030300802a03142d00814039 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 511795647 1250 511794397 511794433
    0xe040f090b252c240c10110f0705070e0705070c0e1302040b03011508070e0a09080318070305030d020d0e070605030f0a0213230a0509010b0a0908 64
    0x180b006141800d003010401540ca101c0c03425010000c08400c1d034801241d6944010340a100180c0c4405a03100398500303080703181d14020102130507485110340016522148a200381c6810100c1000000f42c1a074105076807151009003044c1100d40450f03880045584991503800d0a5203010503030340000000403042c0303090021240d009005041068070814038090010340701d06200f4050241600c002c0c9401c0e044045840c01458641c010f0002100041c3c00095009249501d0580920751a44050080d80090b181440300c8900400c180382c0c000d405607018880c4042e1ba51307a200c003d2100600301002310812004501084605100a03001160080c08481c3c80d1005a2a02c40080d4445d985030202c091814614800300640401c44008803040d580b64070341540c2e030309110404000001400c10030030b550b00704001305100c0000b06561019041001c1c585084204000c8510500d00442040c10300c10854041c0c2000319683c0d04560078150b03041903030a035486400c00d44054804c0c030000c0d00701101e0350086004201c010740d008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 511796897 1250 511795647 511795681
    0x308060f10050d110c06100302030609060403090302060702040b100302030717090d030216150b09060402032a09040e0a0201020c06121315090c14040c0e040f090b 71
    0x1180e00030121280c06040200025540722104003160060100352103480880e4418500c0365214050030345055100040b40303040c90001c03650520058800700c418429410100b0040d075004402c840207002c0b03801c040e2000340420210740300c000c0c85600c0000355002151201d40085445410242000c5207107106014098081c0d0011600000000e4018089202100c0c5008400780240c40d04c001520f00c0c8886003504402075401558000c62218200300100300141140d00300041c0700f40c0b441c00008402400c14200b01d407041018200610490050052001c00c810680034004206022600c213102c01074001d0140c0708500038002440d42c09880d2040c280c026200c08a54401114402d80c00d9030004402e400800c1490f0141050005400f042e0500103901d0025611000c00403900078030a046000d400c1d807404c2c9090300c0181d00304460102014104001800c0c102654890005045500b8080b8a10300700e0010324081d0081c1ca484e11564a515840600b2005540501640c9400400c80b54041c41d0000c20301000b5268 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 511798147 1250 511796897 511796899
    0x60306021b010b030c09060613050a06080106020601060809031227030d050603030a02250905070f110c030c0f060c0d081506031b130801060f08010b0a050105031f080a030806 76
    0xc200f681507031860042503c80d0481030041c090351403070704c8031030502c00c0b0703500102c00419101c03651240c0803409941d034500783c60051400c2e644080b101c2d030401c0390013420031406074010400e02158805110507100040180c4071441e07091407445500350786140700100103803601ca0340d0900c070f50154040b128281da0b02000620021810903030a115503100c00d01031540c0d920440c108200141c00640341c3c509605030100c1c24410740d4000c100c1d001d80c855110141c040480303c083d502c0b40081513060f0718082c240c0ba00503a1803004e0303450319405040c003d5882404240ca034070041c50002d00c0386565214160311503854000b96603520034000210344c10206c0840014050443c141c0f0450244000e02100c901d0030b10b420401c491183d8000e52415a41060b0f0100d20501a000300c029800081005003020642c06801d00c1032b4001030282a00311200145010182800c5460520300e117806659490f0062240c1d03604802140e4101d040c80a101c072840451b0303030004500380c40d5604100464060582480d05140e88000e8075801408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 511799397 1250 511798147 511798151
    0xf0c02010e07050a0b1612050c060702070302100f1b06061e050a03080304020f040504054206180c0301050a080a1a07020703020d0b04060c110601090b04060306021b01 73
    0x820181d10941d035600b00e201c0e0030750201558400740405152100500307146403010400020480311590b03885160075006001c0d400261f0041125403100c0300400080760800c1d0f03540054440c0c0da0954010402d442c03440d00600051102150480462921035000f00714a408048010040d000782407030100f010745054800c0074809902c08641005241d2098004070440381e00a00100c41145160303180b1505400081003a64890f114400030180345e02c4a015080c4580d12840c0545441028042c44030020003001120845031042000fa504000180d008280082105c0c100d210714540d4550000810114a443e00c1e6981e0004130302c20f01503502010000f41d8180c0d80e04550095070142c54400040c6d0728407090300c1c00307801e420720381c17078000003809114018640100051060700c401944030b801040c0000d48426040b10504011400c110500081344901040f075162494088451038100300c080e951000306004e4894120303aa030084c540c003603440b0b42c064402158811801d54843c0b202c0e04030005840b040c00c5059520f54 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 511800647 1250 511799397 511799411
    0x80a0806010216030f030c0f0b0105011407020a14120307060501061d1c0c1203050d0b0f0d031101200d1103130b0a09061806060807140d150f0c0201 65
    0x580089098000000314803c440c007010b2454135103504000701c510040d020302c0b07004c802110100714451010082103005a401c581d40354501000100411007143e000300505500340003420060360703525007520031183c0d84c040e194503000180c0000b464050352650207080303d04c0000380510401c042d9070031190489034148c50703015070100c0717541c1000c040c3c4666601259000e082805111601087c01d00a84511800f4410944545883e49007006007164000000e9010840c08900c4000c4030241e80110043c85d8070684100084880c3d4002041040c4091040282440b81f5113506071100002588246d04000c4006022118500200c2103022998002010300c81454180f001c400e03000791191080300d0107182051504502690a922405050140074280d01034294445c1200380101e10140a0000340780c540021014400304a03240410072104c01c1c0c2c0c42100c040c1c000d0076040000316069030540c54010415118140c032001c5034605001c107506241c0e550808545840c0c0c3c0340040000650102414414680080000e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 511801897 1250 511800647 511800649
    0x12092d07080d08010b0a11030a0c060b24030a020f0315010f0c080f07030903020402040923040201090501050c0309030708060109060e01050d1e05010f0f05070e03100506010c0f080a0806 81
    0x2d0480c40070240003282c00e10b001001500c040000501e42c01c1180e1800c484484c0114111342d0460340002d15180000d4000420701c020700200d403040300300005040310702d000eaa0072011200b40c6c8000b02520034205400c0003000050000416804641511860803050303a0341e81f85c40070481c3c0c040b000b42e24200340000c110405a081403400340ca144070855800c040d107281004200300070400d1640c03080504a041240c00400000182c0321400070708050031001101103014108044000900e100c0811140d07110340c060000d010244c1d800600324019101c0c00c0c41c2555071600b07556415842c51240503107068040c03040a50024a11707001044d8281660995981809181d41d5182824103104081c040d882d07028403032034100b40004d40b842c00c12001181042009440000c100c2c2c4556003101c0807202884030454855049900e610b0507446210361000e0141080480300c0f20201c00b090fa00c441c2c014407103030001c2d030311400b04006a01801e10310003200e40c41541e09060005515041141e0b821248581001c0b688500c0441c00e9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 511803147 1250 511801897 511801903
    0xc03120305060415030209060612010306061514041a19021c1815110d0206061306030b040201390c06080c0703080c090406060e010206090106060512092d0708 69
    0x38080c13000d016583c07038115020000c0082000e882141c2c01032007008501801000d07814118000d5000398000285c403031404902216803060100d40d5010000c016002c1110f0782c40c082c040e6020f941e180c20b501406404142c00c651124440c0c0c08460f82c0b540c0c0c04007c04280d15a0008034400d5a0010348a1445800340c446000d4a01c9241011100b01c0100c000105120294101c1c01c04907007010700d0314000300c0703132044125054240840c1c03e1080005801500800c0414108070a0382c00030080c07940e030108115459a00c421140d040044c1c0003d04000000c03a406401003081040019244880491520454880746621904c1c1130355080488403500070b50000501e0a00840d01180301d1f40c05513440350310344100c0d0b640444990b28014084c8140031424072206040da1240c0c0b2491006d80392075100c80180406a00019203022001004081c050b030500720305000700c55200d000d0358655620740d2140e030055140d010000e41462a02c0a401d1040404042d41e104019030541034185402010015584419140c0c11140e0b1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 511804397 1250 511803147 511803161
    0x140705010527030c0a170607050f03070513050616020108010e04080a0c080c061608090d09050f0f04090b40060905100c020118110904020d0c031203050604 68
    0x1491100084081ca181240d20741c01d406400c003c00352a0441005000500e5203a251781010b2004040c2c1d88154030b41590402c04c6503000b002a04249041480b0084102d0303040c0f2004040d0420480301040d1241c0c540c00506000c00944801048144c40705043c081203600080e0f0b038201640040c202c0d4000044030100d401a050040d82c2110110307150401c44002640c000c04001c5d4100d07000242007240203c2d0306001d00ca820301500c5800c21706240404000c80081c90b460f005030840c81160000c0b20071b441060380080110017100c5068920007031804c0d0110000d24680020100142c129081078003007420084003c081e24810380b24600c1c0c0c14070240c810020060351101403525008115900c440ba4901c1c1c1c1090345030243c081c1d02c40c200120798a05c0ca50768042c00c010402c6415402680c58001402c48250280589800210f203c0d5491300e40460300c2c4c40d02c02c000304480d003141d409600c03150007090a644a11100c0d582803a00a001804040c0c0c0da481c14903c1c2a030000c41c903400180c0b030301d80410070b1480c1a0080ea1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 511805647 1250 511804397 511804417
    0x8010f0f090f11010c0602030a05060934051309020403120c080f030411120d021e1903030b190f0f0b1b011b180b07030203070605060105040506071407050105 69
    0xd01e0384051903592075003507204100300c54140255081701500082583c00210300c00e0000000100700b5041210034040fa6590160152a84810141c10308004580200c1c201401c0c0f010800b640800700020801070741d59200780005c81c2c0300700351049000b056240d02d1787c0091044074456105844007030301d002412030391000d00d040d009007030040800525004031408006590058010501c01c482084071000180d401c0d01d0500d24945181c0144c001d441c1166014461018141c8418407550464044004000c0e1200300c211701381c2c403c921544250700107142c42980000500d4101a00a030300380700c801c10f4142590703041c1d48240d0301d112403000e9000c580681103c19050444030748500850802c9141002c81e000e9461140c035155a03990390f006402c44540c04010350f01c0c1c403007107030780c40c1c4811401000340c5078098200550400540344108210800000b81e00004a0b9845070300584000ba00d52100401210540f2469000960104011584a0034442d140154541d407070556004c0314402c9684070015151405904e00701 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 511806897 1250 511805647 511805663
    0x9040c092903010909021915080606030c0a0809160305210405090705071a0a0e070f1202100201091a01140301052e0b0d021908040b1b090a08010f0f09 66
    0x10800e000c1150405c0b689684001c10f44035000303c1244494400c540309921802e4004e02c68201d8002e015002100d4035041a0705445184c6140350070908601c0910480e07400c5e00030820307a0360000301529000c0c0040c004803030b00d440b42c8030300c0140d036810140d41e140d451020401c0020500c58191080f4416081101d04a44014080751000d513145041581d40e03030031998081d680030038020aa40c44003042010540d1140c2e00364180080c00b1644003446900c2e02e01c06401214003048151802c0c00340c00280795540312421303030444642c0030004007010100e0260071200002481c078a40d200b8051030b4054420303100c5040c1c7d0f000702e07030071172803032310702c80109400e17a84191048a4030301455190140294440b885409182b40702031010b1185580e6001c29001d2584452100035069a001c0307980080c90440107860311503440345103881030541c14030361205100d268024103660540da541041c0c0c49041e01d968415144c03a40d030000c0454801980e1611160301809804485110480c50300843ea090f501d107070301c900402160040c4030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 511808147 1250 511806897 511806899
    0xe0901020c0712020d1406010602070e0f0a150f03050a030e0108132a24080c03010504090f02040203040b0f060102030a050d05061f02030a090605091c02010509040c09290301 76
    0x703020f1042e00f180c402e07a0000044500c6501044404590550381c000c0c0c600204143d614110000381415099001400b00782158014401d00101440e2141e80000c010840000c0117031503120000c00358030156212129180c5505000014800f02080b110039441c02900c8041c1101c18800044600400460b1100190540c8907a2180400c0100809043c0416000b00045c804400c12009040058299110f42414480c12203e012554010720f0840107208480c20b18050508100481c50240e0105014850090ba03580d4042014448503a48400e42590040e108568030308142c00c0980c400242220403040c12845240421100c0d440003040b2400c1200603a1f0f40c508044400a60301c2c054600500b426901c024200700c3c00b440b00c00301c94071090300141107400466031024010006089100d1a50200c400d000060202982e00d440d481c0301d034040e4060b001c141c9240100e01d880103075024051044042d0304240740c00540d60f12079800c080d007803065031400200040b402d101d80c41c000345145c60324000c24040c1201440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 511809397 1250 511808147 511808159
    0x3060a0b030708011d0f070f0311040906020412170405010e0d06140f0103030f080106050a030e0a1709030714010519020a050318090702010903090b0d14010905010e0901020c07 77
    0x841510111001002d0b100441e59030701405083d18628402541c1c1c010200e55001c1c2e001c8001c10041342102003680151252500e406206d080500c010701c00070f000030803c03440c400c1c019070702d0b80e2205109541c000011925a522400081c58100490901710b40f08040048d5040410031040242c404480b4140d60b000300d9029210103102d0440c3c10400101c2e1441e0b00c5110703408d83d0891400d0641d100e01001070b0040069031650400819039400c00c11440f01340881600107105c00341c4e00508880c900295814007040010044111a2400c0c000100141800c40186d8060000910031002055440000c030100c0340e20940341c10042d0013100c40745a14030b0100c1c0c1d04001a40511012150750410102d050040d59442540b98407281c0c19984006014804000c41391010900c5140c20420035401201c10f02c02001400d66070342d030142000307174203004101214201107500c400c0d241d00d9401041031500351020300c0d07116503907030364018000d82001c1c011204c805210a002070204c0740c0c1442624208007004000b402a11701d042 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 511810647 1250 511809397 511809401
    0x501020c01020f19080d020a0e1807080105010309141c1101021305090606120702010902101b0b092a030c0105120f0604090b130b010503010c0915050c0d1d090603060a 73
    0xa04105c030721080038440d0466100c12440070340744454040d00d415001ca1030075002c00c91196094100d091001070b1000034000c80740e5101c00c2e468191242070800082c1182c20707042c52104003050700c0e0241c400b4070a10054510609924803241080314141d01c55011011402481d1401d03030295078140341881d03071402000c00007860181071040d0081d401030516840c04082e00805002e91100301c5014000d80e45942640007142400951400501090328044428880800300c1c0c40b4000350140000e400c1c0c100c0800401d1400d5424050000c0e901660092008540868021741c050300381450b009a00c00e000344d03140803140b5400f500440b02c2d072581880351800b1310303902c900e0302b010b5040c40944a075800991b40c0128800103010301e034010740502030962078000c0f02c1b145440c00d03e0040205820040c00307641401081d01d109034007e54080e080c0c4024420620014200c50403c81e510b01442c0d4079140b09200c0c04801004840d0072464000181c4030a86014850380360f0142480041c1c842940c140e6015803000340080c621050301c4d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 511811897 1250 511810647 511810693
    0x2250c090515360c030f061503040204051005060d050103060e010b060d020d090618020307051504060c0f050715030b040b0a03030c0f1203020405130b030a0b1b040f0501020c01020f 79
    0x2054009500b143c985651064040089403d58000880013050211240c80e0411147d03205000300c8255513210462980700034070340405000240030301e4072038000c11900c0580e81101e80281c10090a0603864990b518041400b4090a201c02d641c0240307468909035003004c06010343e1152100151080740742c080c0c0d10005100942c414401a00029500ea012000040007801155100b10300d00100307000012490041500740ac0c0300d980310b03a200e03410f881c0300c5040f04291b500580b01141c4250a144d00d484e1880c1c00c0c0b1441c40958408020081c0c0a24400400c04214a070051201d481895404110300b03060441404100c1c0c0c05044603a41c8280569002c000007441142e1506000d480f40c1e801200000036950380b840b008a00302034403400b1036008101440b49050410904503003d19502c414043c9450800100391502504500507000040010019258104100130030920748a913804003641d8960741c140215404025025247c014060041194955840021480d10100891010f04140390303960b0100da140780e5a03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 511813147 1250 511811897 511811959
    0x8160e090405070803030a24230109080a03050a14030f0408092d041802090c031803040e0709080a15020c010e030f040f0e1902250c090515 61
    0xa0f040e40071444100c1440554000d28100301c001c030744060055600820542c0070100c01d01e040a151600700104c405000c1d102d01d000d024890807103644455a030040326040c003e03801000c1e8910400042e5010164840028000005c0759079030000034030044e0001c24114402551005001c1500c0808038022907561702c02400244030040220b44100c40d000a484002841c4048144c600601300104000c1c0d030402d4050400760a20344045154036144683c0046c10300d020161403004d4222300400090320f000c8260b00701e009011030000440303031103d5550710041c005407c200c0746000001c101d0180060b45030800504600c0499010701c4448501d5204d42d4100020340204a0801042d92144141c00a1600a02c0101000c4c442c881643d5030fa2428802404148c5800350700107400c40940e6000c004158048459003005545c03040d10150340d03580840300964041640b00c4c0c44a402d04101400740c0200185403070744c2411035201340d0041c011a610300322422102c80c05080040e40107505a0b0540c402003c0380271101a030000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 511814397 1250 511813147 511813153
    0x302030a0305180f0604050606010207290714010c02150609040f150f02090a08030a0206071805090c07050c041a0f0a0f121103010c0e2e020d08160e090405 68
    0x1010303901d0703a24080301d401149181e600705c4d0061009201080c08050352050f000c1c0024802a07240a840360005c01c14580900800e02c081c1512520a0b8a000200c0b40115080508036451108803684513000b04180245c40740503108540b60750901c0303901c100150f4800c1c04020322240043e69240c41799902542c030004103c0d11088040c911904104140c801c190340b20044040c01601d68004400340503228180d908807140325442401002003d03580000d110f68420220b1a0250080460844031018090f0541000360b000c403410082001c14031409000d400210701500c111624050a54280000c403079600702e518401100e006c00b8480c940c10a1084a05044800342c2442d20301559100030100f01580c83d000300b2990540703420004113100c64002c3c10104401e084008014400c0049409052200800840d50250742e520629803200c9681d142121010450a44440c00e00000124001d40368451000310310f01044072103002c182c58118002c0142010b0010f0b844002502c001c0d1810080100380081040366984 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 511815647 1250 511814397 511814431
    0x5130206031614360a0618050a09020307020613050709090f061406090c03010e190b09010303020309011101061206090f1b090509010b0901060f1b0b0105040c020a0302030a0305 77
    0x40c03a0710040914204c04010124002c194a00391464010601d1510310124809420001d155681000780d2003181c1c0c0a081c000ca820480102d0500d141015502c00b80d80f007111620001408411030700218400c400d41da09855607a43d030700c0440e86500074602c00151483c0c0c0601003e0040d1106a0f020502d4103004074405481c214440e911030040d40c403811041101542d03001c00b0300c5400c0c10304800c030981100301100e0700f0b429903040410012100c44010f181c59901d568a01c144981500990704ca001c2ea84806456130b0307019038686c01d000c1d5903540b05607030850018404161030a50300d030040c81a02e06448000394903640655060320354001800c021502a103980321030142180000324001400b090040380e0ba03400526042c034000c0b4820841d40e00810001c40c59046c1b4809045550720b1400c01c90544003681005032803e40a040f08440f000500a42101c100c40c10341030030700901001c904c5030350499008079030034405400c100314202d0720340c1821500100903a000380000314019019800090f031107500e02200c08400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 511816897 1250 511815647 511815677
    0x5090118050c011707020604110a0b0a090807050d0b01050928060e0c09100f360801090c0308030408070b01090c022109010c0c090204080f01051302060316 68
    0x180d030100401c0300c695100607490342c801d503000808080c8070001c84521420f50324010707034040e489450040005000701c83d08015450303181e40d10301601c00a000034180064454091080291400129000720004c0d41308181c000250b0340381c2401074000709648248403444603480c002c14041d8030100a4107170b078070400c6040c100d07080c60200b9030000d4040d007011803008580645402c200b030040000c0a4140105000f04001030046c54445140c41d13800c1001d14504130b407441d020041d044482e14032480341d940c61350307101940300038803a240340d40c071413105883c160000c50505a0326612103088030396035413000f0100d9040c0034081000c5602e00000e19032041c020143c640c40c0030600e69540803002e40980140c1c11440d03482201e021090740c10410b540d0b01c81003045040c02d8034084102954206c1c00741014480c1001114120001040f00e601c900b48003c000c005015501c55480724100c07521104604000c00c030b55864140061034041c03840c0c0c25400d6550300074090500e0f68a03a14084000c0003540c0c02e22805001038203011600b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 511818147 1250 511816897 511816931
    0x709020913110403031b020d150f05070e0a0f0e22020405070309060b03011127120c010809010203010b03071b05103206010e0d21030b10020a06050901 66
    0x2100129100c1281e0721401c41c900a00401156030b030050300d48500161603801600d4071291003402300e8202c2519a2021140a00079000d00044203054400c541407070180001150070000c40480207030202c441d032030b003280c84943c036030702011007403052034001407003500803446802d02c42c1c0f0080c0c4002d252942008144a803500030800b0380341e054400328002070b5111011310510805200340e054a4000714002d019044200b00c54038028001d400710202c080d45000c1030b200c003020240602503005400a40b580c5071001140003041d0f1260301c1140b600780030501650018071528411701c01c480c10303a00b21310091411031f02c03405011900c850107000c0c81d080000c8a4100140414400c01c54410283c07020180071650307104031b80340d200c14070001d920b124035814081c40e10742100c004d800c0760240d0701c260b0a18241d08002d031660002483d0010524024089d001210540322541840c5100c40c03025282a0720b041c024000c0030b900740015000c1003041c0d5401078214041c4c5000003042d6400c290741000f02c0c50004924a0044002c1c0700d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 511819397 1250 511818147 511818161
    0x1d16091d010f05010e091501090305120d0c08010f1e08030d05040309060201060e19090206030c0c1902060d050c09300106060c1b1203030b01020105180709020913 71
    0x80d42212520041002072058039540020b46801c1c6010305c3c1e03403000d0002007800342d807015040c848800200c40c1c40200c6a446070080800a507001070480356585400e8807064542d9000154541d905418040c90400040c050245107049454500320406c00b0343c03405507401164080440c5078150200040c0b000511034000700083c0c168001d1b2280c000505083c2850090041142a4400015a41416010090b14040d1041c25910070b034030403041c607441c1c0740c001000c200405010340001c2d40901d022060041110025014005000824048606081e14400c03ca0210750800300000d5002d041000703032754040f00180d0031094110108060300f6007000c4840001454001e884050381d07128860032040715503c00a9509013105440650008001050800c080200001c2c00070b9005414510110024030403082c0d0b00e001000109a1040700c1d9004407510714006010b410340054580c015030031302010901e0b08100e07601c80a00e409070540105200c900c0c1c2a4040007035000b1170b014950100380d502c0e031402c8040090241074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 511820647 1250 511819397 511819439
    0x31c0213080610090e030409020309030f071a332b06060b0307020a03050708040b0307030f0f0b09060f010306051c0308070507050c13200c071d1609 65
    0x48828a480d5048030103ca00d194000c000b81030402508846080c2c0210440d02501c010600240e0b41e5038038446410700e1803282100c140c0c2855400580202449084548840400c0c20010070b001680c85040d114908003d2511064200e04038400a1144840c8010303070107480c1e050003810050340f1103081081d064bc030b8240d40410002117030083c100d138020010300b4810600503003581c008242c11810490300096445032076410040602400140440070300014400f038900410070f20088503034030b10340a04000d010b8100e14840128050030500c10608a4415005018486070040d02e0101980d0b0780c14100003010381040141c43c145a0f5511010481307841c1c0c0588800452083c902c2029200400d207001000c081005102c40308005040c01160300050002c01d00d1a0300c420102d414102903125500102c1c000c0807901040c10400042e91492420300c04d5500c003030850342090006540326103a4a4000b2001210710f100c2a2142141e12400a08800000d10034548010714030301d00b0a06103a1104848181107039040300d88 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 511821897 1250 511820647 511820653
    0x140103051b1905150d050a0209040b10020a021905040216120801120b04060e0303070306060306050a0501050d0504050307050f0106290d0e0c100503010e1305031c021308 74
    0x30100c1030044510451580d059800300160680011402144040c41c01401d104100c00a100e0b00c134400c0b440c094602c0b040e11040204024100309808000a521a04942c1e0007681000b0510015207070001700d2100b0300c0c6c0c00e40c0140a9200c070941c204403c00420301328811200303240f8000443ca81c0c84038030107002203250013504840418020b003055030302c1100e034410704010896124014456001901c1c0a02c0000d039204040944944691402c0c80c0541440c0e0350456207071002008108405600d40c20220441d00d081d01e08000b61a112003d200719a82c45008a90201c1c104001c50701c106051036000941c8180a2410b07a410800150344181c1425000c00c00d4042c40d80d140d030b209200b0076054001c0f03030400080c04044c1c81c0b44500040041003680c02500c0d4003040117640e8243e02581d03544140306080100000425088409a8150300501690130a005894607841007000080221003040480c0c1c1090ba0800019424110301307060030403c050358000295841b68003030115410515809a00c040902143c03c06 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 511823147 1250 511821897 511821913
    0x9061206060905040816080909040b100f08030a180302060f1306020d1e0309020604080a0b0108011a090c04032f1807030c0905120d020709060b18010314010305 70
    0x4108251510740d04030110640c6810113100010f4008002c0ba0700200c18000e240050b030b105030420344258040d4607062500b00a110040008000c0c3d2000803612418101c5109000f498681081e50340140b090b0041f04101c2c0d0042180040c81400342986101c00c40361904052661902d0b0b901145aa03040340319003140e54180424a102c00004502160024054502c01855030199a89000703050074580201d03407150b1080a40c0c0c4102a034442c0d0490510309030090320259583c4c3d5261041907584122142c1545c060354400300104000d0010701652180203c0280202c2e402003220701040351440c00a001c007260814100302c000000fa1843c2c1c1c2a003216007000800002848602c110301220001110344148950103035402140b482d0580300c607254016996150024038800e02510984540906402c200e9106100030107208036050000b48a03000c001440d420b550340c06546516075400c0e904103016845005409000c2060000c0140c81910081e541c145004034031000f102203030310b044150a0700182c41580110321 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 511824397 1250 511823147 511823153
    0x9060c07060509130b0f040f140f10050307050a0608070909110918040c09020d0e0f0a0c060809030a050f070204021803120c1b011107090516031e09020406090612 71
    0x7013211018880c5040c40407603012030015a1449410400c2c42c4910b649030180c0c03074002e6059010402c0c800304d54a11480c0e40c00c1c601c0e00b4032180e503070868070000080c66001020915080100e13480040324070141c5114107490401c9000d0350741c440001d20744000c01003000c000143c007807114094241204000c4000301d54425184081c8019a00703090070007070b981e03281c0b24184030010b0196214001214030107603006880b071560902440183c0720464650301107103d030a01c40c020310300f00464000b207454030035002080d4056445409641200c41164030110303d03007003403254030103542c000c10040001901c01030795689002c0142e40010100d13003000c880a90501403440d0182103906080009007030394800c91051078240b88450400c25620b052114850b46040014100880d80d41d00a014500c1c00c0c0f040c000582e0b0100d0b44401c007407030040038216007503914201303078002103600c840c002d00c9450307001c0170514038000480c118131480d00060400310b00708a0f042940c0d900c001031040003c0c0b10300d1000d8040300d10765213444090b40c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 511825647 1250 511824397 511824409
    0x1d0606100509100528050a0f02010209060406030509100c05030a0507020c0a0b0c010c02030301050a060c0203030d0908070309060e09060108090c03011e15060819020c03040b0304060e0706080c09060c07060509 91
    0x3100010340005c00348145500c0c94001050743d6005406150070382040c03c507940220302900800300240c5d00508040341c08500d564040e08001e00c241c1d03030340080b140c0c0520403c115600b51445203000d40c0205400700042507590080c0d4008030b90100540c01103c2c9800742c110f0210341083c446500210031782c0c1011034131166001080c0504044450a8801107055504207000980394036000d104400074403004560b02c004644090090f2000c01e0f090300741c02c01420345141007032800340d407010f40e0032000216507003404103145000d032000403002100600501c0080d03440d880151820032015184600e0b0703100e100045406540c0134020781060002e510951034141c20002c440c542a104030340012591030b036214406005156004040651219032205148007041500d001c1e00000d203d1102c01e41c145000014010425244420042d4011441003c0c100110b4420072502a12110b4501a01c8001070551004c01c00d90980d5a0143c142e03644020103417841c241e01420f840e480c01890f98003c50110f00c000c241c0303008610b41342c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 511826897 1250 511825647 511825687
    0x10306090b070c0305090d0611040902190306210f140c010e370317071101050309100b060f0c010515031506010c030302040b070c05041d06061005091005 67
    0x40d00307010450f070301c49503006020780c02880449030189071f43c51413003414080c50f600b00500b01503d05105503601c50301e604a50000c1c0d4000c07560012020444580c0001040c800d01c9500120b4049080d02120210350022250100654810036210026000401707070104e440c071a0f06a0f054844c0400030100724259000161500048134200351040c054084070603050002d00c80509002c040c0d10090000e0000d01840d58030924034560000b5051002c240c0c0c02d50026104440105015406808014000c204000044070300b80b04c01c5900a48070b80000820b806448e0807a000a40e400780001c1240c2e08203e4000e200d0707115030304a02100f2245a4442c021300101002d40649588070040c00e41c003400709022559403020b004140541321030b0400c0704003010001807501c640e05540107010391040d40c6950305200d0030700e018180d10303c0c0241882286441442c0900c0341128001c91229203c80b030281140381d035900308001080402102442c14441d003000904103a81d41c20701d1b00140154a80c417200d03240c98101018941601070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 511828147 1250 511826897 511826911
    0x140106050f07060b0d05060406020a0813471005030a02010903030f18060f0f020f0c0904061104030c14040b010e0d0c1503021b010516050c0f0303010306090b 69
    0x1040001c041d108445004840c4125000403010038251081d01c04a84843c0000001170464041c02c1700b4030040040c1d94005040407181380c0c0c2c44205680b1464607201e4554003031200245030702410b40f1056000070706c40816a00903420a04142c4100800200140c49403024811400061512000304000566401148000b807c000d40c02400a40019030019004080c280006818400c88000c001c5100c0c0c0708500740d122003110080080c094030760f02c400140800d0300c103c1c0e54201003030001c2c64049030f45100290440c0794070a000d00500e03550060b10b00b400402c08002c1c0041d6000381d200e42d03c40340520a0040140300a61003850004d41e80c52a0400d204c0b41c400582c018140b10700c0c14400854480d81c2e222072480d4650400319202034120389140340c911000404c652044c80c44850224545500c541c1550180c4140c90030110320340c20803d0081e084034203c0d4070407038a080358640e1980c00c41d1005481040034022181408048039100300650105a2654100742d10484646460300c62440130026800070403500518 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 511829397 1250 511828147 511828157
    0x150e03162c060603040f15060602010e060c030a0b0a05100f02070b03090d050a03090b040b101a16030504090203010f1703090a050f010e04110d14010f1203050702030d03140106 77
    0x1c08204040c80d10714026041c684200d2000c0081000c0c0074001102c0f6100a40c800008200d07400d12a81e21400303002544142000341d441c14909504000c80800c0d028410101700c0119032079982ca0401042c002c0c9118906150800c940c41d40105440d10303007410711912242c0d280c40710000e11600300402807030b0800b42d40140b48529411b2061164012001540c1300341c01119003403940d00c0d0070007200200c0003000c0c000c0d000340c000c280c001c00380b009004117128424094145100700c3c1c5106611010340c83c650041405d1000342441e0304001c140144401880140d000620a15007185055034855050090f60400c2e04132050095510904001d0100704020303070300042001402071400c007480540040d44420306482258083d02d03104162041580c46030180c070121101c020001c02151495411100080c1c1007410303804a518605038450046403982800d960407504600d0f240000c882c10040e0110942c1d500c40c10031401c0c858103100480041c3d030180510001d0501c26540085d95a6000b128140d035008103134000c50a003c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 511830647 1250 511829397 511829459
    0xa18080408061003050312060f061908010503010209010c12140703050301090b1f03090819050d05090604050d050729040c0b04080d0c080903061e06010f0504150e0316 73
    0x3c00106c1a80d441c104000c007582ca0f199107074000714a0840d000c4514660105001880b007041115600040c0c9070b01071b03a43e446403600da884006150803842515411400300d42108942c00000e0390f00160b500c10500c41c1c0c68005502e0303283c8860f40107542c00600049003c50804401400000c0c103c0c442c0103020041287c5244510358020342d580c01001c1903d042c003080540741d61950f418090040100d9a00e885542003074040e80d455004020300d15000001e2965080c3d040c00042a0400c00c0080c010b40070b00d401c00003521812143e03c00c2650241d00a0341c00300c0708054903c151400a41c2e038a691801403071175a00402c0704c940360903e444da8180301250010141010b0034042445110030004151400c00c0440c02c0812240c4803134100301c0204d000b03144c801c1e9030520599040080e142c610f50b44d600940700344511000c5054036010015600b00c01104156800254244401c100042c500031040611400c241001848202c1c1c0b40c000c82e051600400d4045d42d80046040c0030050401c43c800d010b000c0146c2900141c19003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 511831897 1250 511830647 511830653
    0xa0b10030210200f1014250e040f1409010c1d15030112020a080d170703020d1a0a090b060304060903120f09230c0402030a18080408061003 61
    0x81865002c02003000083d48001c030441001d505001c03880c1500b0031603078010180c152103a51210f40e0810082003905140010600c100c2c40b510045c00342c1c0c110742c410f0f65003610000c400c0c0501c000040f1118200800f1004151198880c5d22500000000c900350100e00c90400050700d09141102803c11040340e850080d0f003d80056010058003d519000070122000050fa40d00081900440c80660f0004400010000482081074240b01015520035514656515529614640c031031015503a603c000c03944c01008140c00c2c1080402c2c007540180141030040c2001c02c10710305a0211042c0902c0c20113030065802d2030445500c1c01c001064000e01c410182800782010510105a01e80005000242410b8407807036000101805088012500c4d04a0034040101c1ca40b2500c0010192641040544442c003143c4d08140080c1d041a04c150300100e5404000c110039120b42091200a40c070091480d5003855903900303011102c8a615032000e80c00c3d40101c640d83d03112810700d43c5060800c280076040e0f954a40c0f07102c1d810000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 511833147 1250 511831897 511831909
    0xd06170303060d060e07090f0b04150e0105010503130f0f06110a02120304020a03050d0207060311071113061505031e06030d110114040812010e010609030605180307050a0b100302 78
    0x485900284c0400e509140900b818505041600041140c40c02d041c0000c403100c80390f42c0f0480c031a00f41100d0501c113103008030018600d24031450203145424010840140281e5018000550300701c5000b50300b100058130551110000c111894404860381c01280c40550240700e10b5020700c4002c0054429039a180030600c0381c020b980c1d00c00c2a0280d80c610070000c40014195070300d910102c00150f8214050700e03604806c3c100001d490300d5160181e0301c042458540b000c13a003802c0d002d05695a21340d01060031180114000200010107030300c520342d00481511800301103810b00303104805901d003848030f45039a5200e09000001d0282140c0009035081180d44d1181004180d1758002200300201510b07080141014180000c624090110143c4249c080700040c003c0c0300c00c1010b400300070540c11003201c400d071a82d6620b40020240c0814280b0500001a4000340c05102180b890381c8400e4100d14483c0200028a00d18800107003140c0004c04203440580120082e02d061180400c0c0f003551040d044541800e902e800d40d400181 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 511834397 1250 511833147 511833169
    0x1e021c0210080112140c030d18061806120603140a1103150c030a02090d03080a1d0c01140d140613020c030f03090a350f0403060e0307080d0617030306 66
    0x1040249144400f0b1850805000714514168080c0c2034407510303c0c110401621b80482c545850031044203102780002d40c02c0c410704514440c0300d04d00c14010442441d18104403080103c0300301490840d60798580001c005204500100000d03a82400645005440c905200c001c17044d60004403401b03500a44d400b8060a9220300003c0d50005032034450759103940362618140e00038012120f00c5500208064031100c145900405401e10440b0307207030b9050100b040c00047d0001400c44020074095a41c1c45094600c0e80d560103064120741c2c40c0c3c0060515030410b1101503004060ba0b40b066031800000310310b04280601420017180c1903030300d1100610250b1510110121003540c0e4441c1109400002d18044003003041c02c0b10a00825525a422600d2a01d600400d50107400e22080104540540c840000c41951400c500020907100740030000807145080a2560722044040e110020b144000e80c0400c0211a00258101c0003070058610107500010342c5900b006800400c01018503901d485a51041c001c001c419610022001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 511835647 1250 511834397 511834403
    0x10b2106060103090f171b0c0a03080a112d2103040c030b09060703050709050108040f08040e071805041a0f060c011a180408071e021c0210080112 64
    0x90786480c9810140a940030170320300240000c00101c8210040c0808801034601e0008401c06400d401c12460803040d6182c0e082c03a2001d403c050034503410008030300c090010341202c15a07405c00402c03580c240c1e1080750400b0109807400c404a0395042d5481760000c094000c089940c240703200203004003114050500d01e200c885144502c5402d100100003010442d000c8d100c0c030001c540c0304080c072035207080c40024a03407600412a8400c1c0020314102c0000d09851081c9032450880394103854040d0300c2d07219519860201d5014917003d40d1a08802c00c40007648060104420b84a5807103503030303a0f01d81511000802e508140b45540807500c601e00b4160388104c403070b0f034a5070304002000e0111a11807006a405000c501d0901640308140c4142d480d0075120580c104c40000d00d004c8161044aa01c0716480c80c11155036400001520b000e03000a4043c0082d81c001200d03000d9141d1100386514102803082120790005207160001c08403002d130541c444c0038038411801c2ca01c0740e0f05248816070409003000d605001d102003501034402005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 511836897 1250 511835647 511835651
    0x22d0f03150301140702010504150b0d14010204170601030308010b12060402070201030609110405040e07120b100b0d0603051522030e04020f03060102061510031e0905010b2106060103 80
    0x2100d440c0c0c0c1c003503000c00584c90300841c0f00b004518142c4d1000c3c3c020402220b0955140e408500040c40a45d03241c403526002c5840201450324812064031098032014003400302c1c5e0007030340d0700700004a00b0050040c0020309104440000781000d40c111714000f004800e06038001c1d90b03541d606002020740011030f8034000380d0000d001e03280180c86001c1400120301802d5958032100e5000d1601c1700811481072441c0c024402d4a00607181400030340c101840325070740e5441d0b502c501c001241a0040340e41c002031050101c0d0307400c040b0f143c84480900d0f07254140d0100d44c0d030100c0c0040b4810395a400e802c0041090502c02c5104004460faa00c80c0545094203040d03c107d06030907245000440e02002d00003c16004042c2482d013048054030440d280c507038000c00c2c02c1c4964015203010f801b500c60b02d030004001041c000744000ca982e03800f402c03004507550354403015800740180c00040048615000040c0035008854401c1d920440d004a0002c100c141e0250140300a1040c01110801c031a60f151550343c3c1211800a8420f40152080ca40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 511838147 1250 511836897 511836931
    0x90703030804061b0207050f180c0309030f040602010f0f150501200718110703120203070c1202071a0906041502030903031207300b0310022d0f03 64
    0x114001380311400107102101401c2002d001c0d11a03000402c001910420744000303110003044002c0202c81a044a02e48031562120704c00103600c200c01101640c2c01c2140902280d0a005101c4800f44158000d9000341c401030303640300001800044e540c040c40401450b4100100094003040003181c510500f5800742c035040c09155001000c880071102100707510710840740c0a50f64078980700d01007208482d1403804e041c41c205080428445184042c1000c03250502c0d4075441d06041c07150b0200409001e03400c02040e0b4005d0105548044010500c0d0728031802c16102182c1c081e018660a041940803001144034203101303500700911849045844040440d03055075001240306840c81100302c4200c0c078510a0b40440398050002190158040b242007030039902840c400d8aa07490703017071800e4500100250300c02d000740c0c251204c1d0700311801c03009101e03900c040b00091000d0280c8034040b000150003010f0ba400349140071040c084502c9105403140350303c154800210100700f4203901e8407148003070090b420300028190207050100160 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 511839397 1250 511838147 511838153
    0x3050601020c1908063303100504080c2803050d0603021005040311060310061b06050115030506030d200c0915040e15010603110f03010b03041406090703030804 70
    0x11a00700700c0003c04103c0702d80ca035900a07039641c006500c00c0f1900b9218210216690480f06509152410001c1c244d03000300f442c0c401d0248a200c5030300c50802e40c15001c1c0b034034131100120840c040c4611443c020203845076a45503440b02c41d494048500b83d8090709900001c1c3c1030b81003071188507460b801c090b010b203400c0351611981040da000500311548025440b0001242048416411402902c201d90149002104407504501442168402100c151f12442000e407021700c4120300684592034601c501d0f0184501000550f40c1d00f40c01c0712800e8100e40441070b4a0002c030b081c0c80b48e260048036230082080e4058a0440c5201d1000340461007200c01c2e0207031000450803400c07409081005001c03603104006005035654200031200f000044510550a07004a007494111000d20400007040c8070600e000750071512083e1710f086d81c210000d02018140d885010303020030a0090380d12a1402443c042c150000d1901d03a40d050524188020500c90105c80b1080d170090340401c03442d0800031400e1821030380c150070074401666542c9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 511840647 1250 511839397 511839403
    0xe010c110112140405060f0109090206030c0c100c030f0b040204030b0402040c02030d050c09040c020f0a1202191103060609010e04060b15070309061b05060a020a140d0c030609020a0507030305060102 87
    0x500c0a000c3c01e03d4000411040c040c0018074180101c036492200c5107039980310710508095034a07001c40603412100c01c01c082581446d904000b007541c0c586c5602940d0214200084d6001a1104000b5500000e6251a03071070510003018412008520b0040b5800c519092460343c40203001200204081e114070740c1c03100300700c02c0710b8000c0c0100e03400c985840004010510700028020459041807624034001e40c80c181e24808014000501e024000c1a1800141001c0e4900e5a48420102a0b0700101086010b1680d120210513009440384074814860b54000808082c244241883c064009168501c07480142e80100002c04024440ca03030415085600400e07410a10b2000c24041c000c80484014500310001c0e5020a059000c8102003e5501036910498440c10000200700340a2402001919941203800840c286c94541d82c000c28800e102401c001204a07902032140c04141c000d044401e034a60b0706c2d042c10507421a81803060714050980910110300f4141d40080041103801944002014541e49801103040c5038020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 511841897 1250 511840647 511840661
    0x2120a12030603050601050405090a110a1703030a050c0702010c03080a060b0c0f1c090e090a02060301031406090703030801030b10030b0a0b1f02280615060e010c110112 74
    0x1200c200686504100802401041580300507165070007003000128040c078144c0a164042e0003030200a14000a4030b0b2514119402e134140f503a0b0f48070540c080d0001c0d40705a5400c040d403120030146d0245481c0d01d852188081680d900801503514200108208801030f030304030312184c2000b501498a071300c16640d1100b05500034003580d00309001c0103d010035524085000020b002c2d00c4200f5000540f05601150750440c200003a00014190100e6036080e8140810341400402c01c0e0700401850881d54103501c5900400c035545e0007030b0800e96201101c560015081d0508018136900314020500a001c40b0f840c2d500e00800f0300f032b410f0200a10091828021903181c80300508108051604600c03850240d041c840c0080c0d0083c004400f100340034510440109818100c0306e001c0c244005c4c1160080c03c5100c0440d07888071808000c800c000001c003146d820000c008900240304140300c0610300d088105070b075410800040c0840e200241d02c3e50401c10110308c06000201c00c105003040101084c201060074a05101400000e0300603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 511843147 1250 511841897 511841903
    0xf0d3c050d0f0f0c020d120b0103020f0a02160803071502030a0e0f0709110f0403020d050a0c030b0402120607020c01030221131103030309070b090a091401060f020d0c02120a 76
    0x7401c0b410807409200d50f000d00382d11034015038100600c5158900503600e42ca030440034100440d0509007402040c0e882d42d080f2107003a042c145030040ca081880451601c0f56000740c208400107034440d010500f42002e43e007100d01c1c003426015006500301b0301107940c1c030141d540300d0380701c02421282c012000c01c1c1000d42d02c0d00004e400c03e6064080d100c103400d01e004403a40c2c0307400c10700c13070040a103003003030034220300c001564003142d110740c0300781d614075143c20f08640a1241101e03201c401290640710b43c032101000320303401c21000c60165105e24005803241c00e190041040000c942d10b404080d0390881018000420f80008403808126420300303002d41c80b0082941c2a2401002c99002102d40b071205c1c0081150b82034840f1008035030b42e4458060302003007480e50000d05940b80402c0b03c0450803680918002d02c18209013102030480c0150090a01c50701c25141c0c4002c1068644540d0008901c540031001402101d80141522a804900c5d200400b1464940304004045901c20305010303001d1a80c454140440c180c00b485500c00c2290 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 511844397 1250 511843147 511843151
    0x313110303071a010927050a0209100302180601230c030f0d110405060a1d0618010e030318090c0d0203010602030a1205010b04030303051003050f0d3c050d 68
    0x1d00e0500707280540c05560020b404494100021a2842e0700d841b0f071460050707540d5815a0421550103150400d2024a0005d54951141d55074a000595881040038456242402c20010320b0f440e610500620b80f0440707044050207444202049243d0741d2000048580617917100e07190f609904415000c09040c07089002c490180d000009441d6403454400780100206050714030100007049068080c1800c2c1d0080b8041c0c0e650043c020015030720b000e071096008981c4038010380c220301c844825030800911719611000d0301070401c1c00003030810710166030041503d025000098010710f02e40000e82c080c0e42d1880041c44001d80c400d107100b070042503986d06450180c2d080c01400190071580c030f58450601030b640741c014142502c005034040c000043d4640203400f81504035081c030003c1d18240b604603a4240c025240003024201034414000b00080031540400081c00f49140724009051416609a00180400c030044114152580050303100d000e42c00c48864180e0400c04a07a00c0d0442c00000228101d94602c0380c821960840e43c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 511845647 1250 511844397 511844407
    0x7050c09070e0d0f230c03030c1509031c050601080601090503030d0905010902090925140402030c1204060b18060a060503040507080d12230a02090a03060513060b0d080313110303 78
    0x1700605695099409040071182d10860030400c1558070711405034003c8413601700c16031680a086103084a01c0e0003100d400c2c00e590401d03a0b03010b210714030010314615800a480d00c4806010803560083c0607150800000c1c43c02d01515414071020aa0364803565503451102c9075500c288200b40103003035110741c0c41903500500c4802d041c101900c0c0995500402202c51084d44400200340158640001001c0d0407116000a52240410a101000025000142007003800303082004a581c2941c84c00900901c00ca102d0300c00020000c0d064814003600511250340d604034100744030180805669908418003c8900604c0e00c1c0e03039240d03114038010f03041200c0303075100d9511489061460319815801c595420304150007040100001c071244050180307044080c441d45620081d004e000724480d4525031b0001c000703a041c082c2aa404e16590b070340e00c60f0200c0d1000c484840901035815203410030040d06005044451008842003510224640c54110b80c81c40042c0c08c403211204801a07034410059100c00044459000609a81e110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 511846897 1250 511845647 511845683
    0x303050d110d0b0f030f07031e1506060908010204080c0d1103070905150108010608060111120c030913021e160804090b1002071514130b07050c09070e0d0f 68
    0x80c0c0198500e40d4400c0c001c219240c0c03841c1c14005403024000503008007c0400900e95220f6100740320110741e031f90310b40840300c40460000c503055281a1054000c00240060000d1a1500060031011142c0010203035074010001005489000243c20314212001c03500c040803000c86e0300c1e024481c0420001815098064000002004803c9a102ea07200301940030504030305100c00401120041001d000c1d0002049103500030a00c0c9511402000011031a0171046944958041e052942d6640141c82d501909900c0001e058401d0304258000c12001a450314055080000d405450000c40b400480485a283d80c0403602d0103030b0204c1800d01d40601c0f90044007072961561250300086c00b07030120f284240c0c010010201c0c4000c0c01480002e00c0ba0845a00851036120782c828441c048903040c12010034044a101d042c442e841c003150040c080308000b860380c040803541e108038030b14200d07080220300c1d01300306d2040f0159410003964541290302402051011540c11226040d0791500c1c140e19840c0d603c0242118404544203451 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 511848147 1250 511846897 511846901
    0xd0c08131a1903141315050907080f07080319050d11041706070e0411070611030103050f151302060705011109040e0321060d050604150c03020901090303050d110d 71
    0x901c0945100809900c1000c1c88240c080d2210700130481211804040000c801d0040c070342080404500c14082000d5208101034640103886082d1003e010700d0300412001c10900204200303100346c0c151000090310650303250a1000d500e03400341ca20980c85d9a49854002c2c400c3c1482101102c030040d0b44488200704004d81071840e05d04a422034041c20710052800c8041400e1400b0018500e44917080664850386d089100c0307070900020b41020300c0d2400b007004040c000d6000145050040710503803580041c07200e8484d803560600380c2c075040d21014000100d80003a160340122000b280c000076070081844200c00350002c4a88082405c910410001a100d9440d00030005940e0b00017000500c11302108481c1441504000c0404070784902c2400820580f40c0203c417420000340c1c14080710700350710040041c881100703030049449030f074189403040310119a00c202d4291568090551441000c842e0205403504506010001c030019140d0b5031070b400702074140040442d030700085103a581c12800300b601e9985a10b07034580c101a04c051740 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 511849397 1250 511848147 511848157
    0x90c02010614031f0f06090f050906180c010e0a080303070c110109050310050621012f0901030e1204031407120f12020717060609090d0c08131a 63
    0xd0740d5038050070b401c007481c0740015500c507602c50354144920354001020700c6080141050002038000c11340322200003940c0070032403240861410032031901180903c0c1038100b407400d01000030500403a205071021034414162000031402104003081c00c00440410f001c0000451101c0380b0390200020b4407001041101c05075000e480082a644140344400d580b450590040d40c070001c660041680603800011405268030190b0006a044030000c0c01c1d441d00c0342ca03aa119640c50080541c0d0040c41070307444403d42000a0901b15034260400c5540380c07001c0c01c83c108040d44020f2032040319030140c10140c0b10030810a1540d01403040c01031031400d0428003035030b441d0b5a1038100d4001000340d01c40d5059004000b0001001500601c0c00502198810349100980f0300c595594005113071100782c00c00442c4181d21011642c4000a8400703199010a400100038070300d080820002141402040380106030040090186615044904482916880310040352a8801b034104212004641d91280d032000405004c0300c2008115400100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 511850647 1250 511849397 511849409
    0x2030313170f0d0f032a0f0e2b052a011d060717040b0a0507051605011d010309080301031202070b033711090a060c051c09090c020106 59
    0x2c080740040c0103030640310312800b0140e0010550703260080440c2c3e803003a4040d4081c20903609100c162400c445c888200003110b912545408521300c40a25a0b806070010002d648910013280c0300240c510b1102c4000d41c551f011000c000c1c0300006010b510317000301710080c04061440c01ca0516200c6504446c1180c02004010400085011a1740d008d1400880022a030126108820160145280680559075640c0310101070301098940329081c000440c90808400040007110084c3e51055140d0500d4207005040181500c1910100054180c040226903040220213041b0307403007001c2000d22a81c0000c01a000b4100242004014200000021040150250301102031040ac0d82c06c40e018140c03900e84120301840140d4200011101071100c506482440746c0c00c9001c0c1c2d2020024141140a80166003001d542400069600000b404180c0d04444e0030420880e5004000314503101414284c1c507110700d9141c0c03402003008648405a00c0b0300006180c0500107003001080c000300100001460301d50020f008008a001e22 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 511851897 1250 511850647 511850653
    0xb03181c030b060702090606090a0806090a0c14030c0114070203070305030325020a060207081b0109060510030305031305010b130c26072015041e15090203031317 71
    0x10300b0b20f42403410948015503400f46c4202c0d05a1180001c005040d00801035680d0700185140d40031514070401c0c42001c0c080c600401c01040185060724004425407240c0d040392513200044035203140980e4001507081c448000a090010f050310300702400c1d110340d11800001a425204800000013041000001140704044045a1640c1d903850380d000e04011043d10f10745400145d00080e50303140480c4d203583c0185003072131041d29010f141c542ea100d6518002e01002170010a965929004c6c00c003400058007403a0740c0700c0b1120411035a181e05641c0c0240c40b600014015402000580e80c2d9002044025030122028420003008007455120a60524010b002c4011001c0001022403801d544408510200700070035948003442d0034440e0366034400c02c0303d050380004070642c441c640903418444015401d00004205403906d820740442e9140908000c01285a031600398000e1851011a440c00308000c100c49070800c0211010120b0420705030f0001901d103000740c6000d07981c940d803041d50000355602e652400c0c03035641a4803c15 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 511853147 1250 511851897 511851911
    0x51605060a020601030618020a030b1608011a0903121c0b0103021216090e07090e011205120a0909020409020c06060409050d20010c050307090803090a0b03181c03 71
    0x601049019075812032000d81d10150040c40020804c0d04249100440b04000110f082100d40000300c00c0c540030b520030b64000e000070060003410507402e1001c410080c001d0400b003405500d404d00100280c0c0500c60914001c450110342c200c000d41d02441984030b1519a0100c240c1c50380711020500e04084440c43c0c501400c14640958a043c0b54040d0007550200806c8101c218450b5880b0003160300050010005e2804103e4110710200c1c4080800c07403c180a03121179520881e0060400340d5070603201d24180c12142103041805200b80001e44000f66402c08050981e0b03c440d214041c04d0011340303443c0442d400411410b0b001080102e10410658003a100d42603101c412202191511020b0000720741360070401030000c0c3c201e6000034040c0303400350860300d40f1449201c1c0500c0c101004001e9a6003100c80181c1d0030740014000209020660b540940041c0c00f0346030400241d4900458080003510000f031502c1750072030034500840012600b116082415107001410000d440450b640d568000d40c4030407400c00a00c011034500b00c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 511854397 1250 511853147 511853149
    0x20301051212040512010b100201020a020d03050c04031416120605070f080a0b0a0302041103060a06050f073003050603071e03260403060c12050c18030c030a051605 72
    0x289a81d02482c2100c0103072400e402c04051115040044282c0c00c4e580d92034070005c500c0c1b0b8442071000d25014110754001070b220703010708100900b40385203284000c041508000c213000b220b1500400305c500301c3c2e0f40f02d026059081050321501c0d0511100414080000d000304c0000200c0709607039490a48580e114441c10032166030380d40c40540300e116245c03502000041c0c24000051404205901c01a51000003c22401d001aaa58001401d6074901080ca04a4010100501050341480c00011000c1d29513414a9824604484000c2c50280941c99010380205451000e03120980b00000d10f800618a55020029113400300e000d02a01038041941c0141c02403195180c00580c0000902da40700ea071500a02010000d0b600d1074031180c841082c545000e80354802d100301205075903100b030001800214410b04010a4000c40c2103030150507034011010415109080c801084014040c4c14212204032040007480d085100c04036000c6031030b0032248101e098040c8141e0042c0014050002590000f1203034001d102c0304000d480e44 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 511855647 1250 511854397 511854403
    0x30e03060c03071b0606230a09051312090f091e02090102030f070c170a050d0f0503070809160f140d0309061209021f020f0f1b010c05010509010203010512 68
    0x100c41c3c0300011034884001420000d4250706820707441c0142004035007591074598080080d401211200628800e000d40c074210360074051101c5000b01740300503003000b40346402034106d0000400b0100c01059064584042c04c00c4034001c805000241014518958046451340d036044020505610a543c01008003099144e004d280350003180c10307854040e07001d5400c0001c1000188040d070080601250241003015000c5000a46400038022682c0100700038082c4140c0350400034140084420f840d0b080004288214044e035400504590b08029289000707180e1b40c2d2500d480710f051007000c0d13401030a0080b000e030b00041c480e41100a01016140c1d9642d401c4088035016007041501c844466000300801c0e1490420080c003405610b40c81d01c000340f65000441c0884250780001d514507031034801c003038112142a1400346215070410030f805420b07240c08000d002c0d4441d964111aa5400c10f074400d0410001e44161550190f4030403040b074160503610000070f02241c1041c45240e0f020790000d0207000d004003010705440c24824400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 511856897 1250 511855647 511855651
    0x10b0112092103090b010e0c090d050a06090c051810090b130c02030414040e06040204020903030c0604060615090e070f090b030f04060609020f0d1505030a030e03060c03 74
    0x140c484140030088885180003501c0750000680c2c00191640c0ca0041c4a1810000c0c0078811255960018000c09589003490041d1410b0300100800e04105040100c80d15040c0122841c54004035400d48a811840c0b50031860540f80c1c100041449080820000400031401039070800d0300d104680f8107002415802d51040810b00448605042e4003071520104100f052603400550403030000752180c180301164078141000d40c3d41100c0a600140d000041c1081514103080109030144400ca5050095459800a070b41e950b11000e00040d21407a4002009d508070f40c2c04100316010301000009569152502d414058020001840384070400b064001442000c05c1c42035501500303403080c11210511a48402d42c0407520502032440300001d105440300c0116190309800040c62191804810780c1d0800d20741441d010b807d039021903000840305801840342c90401075140c415900040910f03000084c0c4003d40403225001028150700461301030080d408601c05141c4c1c0580c1e4800d650760305130304488440d00e80170b207181450301c41 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 511858147 1250 511856897 511856899
    0x105040209090a090302210a08010e060d060c09270b1807080621011e02090d020402130b041508070801050a14011707030221040506190e120a030e010b 66
    0x100e000007408000d0584c80006803c0c060b104840c0383c030300b080024030310740c1c2d0030360000036080c000104c0c8185c0c2455000604901501c20001c0c009020704095011880c0712081d002c000300410b4440790b284a806209500b80300041c1541d9117503541040300a150800381451035050300900d1401c26039004040d0400900514800c14503001d00041c990f6182e404643e0180060700c03055210b15101004c0d0340d840322140034610021f41c01c1d000080c8440f481e20180e201080701c0040d03822046d0051058040301d170b44600d240e0355203540565000d41d503118041002c114500700f9070400c804082d00418041001d20100f550385000007015203c444064480000c15140e44609104250f40400c00d22014044840c01c0c4551801c04501814030a81c414862002c1c1d81d009501212070800090340401d441203c81400301003030724011314118000d0000d0500c4c0d214562103000040c01c1102c42002490305003450040d5031f01c444501d41c09030341a81c602c41c51910f5424039652054400000190500384c5100404030103208007507103800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 511859397 1250 511858147 511858159
    0x50c090a05091308070809011107060801180f06060c2a03150b0a080105090c01210510090207051b040b0306190b0307030f0b1008060105060f040503150109050105040209 74
    0x8640010808042d00050100d400c0003403018840300081c0ca214081d02c20030b88149030150b150641d0700c000400c82401d41c041e003a12075000c01c50400480d0b4000071001c0c1900c0f07c8541118007030020490100c0900f0080d2000c000541c0303056400507506910907805d4503400e101d2460309050780700c40e031045807000c8003060000c10b403001c852004000240d05401d6050701060350110100d5003190000001e25500c1580e40004078036510307102007084105003407151240702402400c1001e200c41c00c0384248502020521b440005c580d503510089050f400c0b4070503a02c0c0041c2030044040d5038400361881c0841d00d9080038240d2541e04007452044100614190013198114040680184507542c0c0b4240d04210805047c0030906032240d940d202c0e01d603030317032030920103080070710302900655131208414076014000c500020f203ca9106407800009000560b80822044c0c11140c2c11612281c50300041002d00700700d4815a44015031600c104001ea1064120345c440d5581211490380c0100401c1e80d07600184030603845141d0456074405c07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 511860647 1250 511859397 511859399
    0x6030501061805010819140103020a080109030c0b04030504031407051c12141603030e0606010c050d08040c210203120f0d110d0c181d07080703140a0f050c090a 70
    0x94402d80c030705540412060070703400c0e540c50051042d80c01c47d0b440c071007101100c01c10b03c0b0050082d070810003030160041105d00020401198140c800401e503d0540303200070b06040c00680132905152003003003034501441d00102c542e41c001850080c1c080d81d99015201d054014003040b1107180d00d81c482c481801494a40001100b03c40da01c8004084450900300c4030024480d03d014040144004203000d190508113110342c90020f4010807410300c031890044018041130400040f990454000782001c0b0344008024842d050182e5030f61241d20b00308411518641220300c0080072001d40820600502d0b4000807101d00a6056481d4070810781e1003620349100389004103032817500c00c0001e181609950390103280c20384100600e00d800c0c06c6172a85440280c640300383c0c480300090003c80541c00001d0040b10903c00405070303030244000700d00c400c22804542280090840c4184000b140c0081c82c03490098102c000000c401003c0e2550303901c0c00c401c4d4000203000c0780700030300e0001c0d1501000540340f0155904480d209040200701044c51 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 511861897 1250 511860647 511860649
    0x312070f080105010815040603170c01060e13150e0303070c0209070923030f030c01233c040b160e030c120f1504110405070e0915090405030406030501061805 69
    0x181b840e00340d030380d80140e55450000041040201c551202c52015503d10b03503100740b040781460030360306c194020520b0318032601c040c05607000d003000300700117106d6004800b808103114001c00c00c0c0c01011542020b40103400000108056030383e004120415107482250500c2181e1a6600112821401801903c003600708524040341d48403683c1c0080c1c41c0425001b02110f007100e001815040c10350300f11040703860382c580d1504030000f1401541400c602ca40f65052202c58824a000c150282d0000301d103030100c21500d03100b580c0c2801414a11000c03004c04020200c1c121510b41020302c0c107070309801000c548049914070001c0d26803007940d00c1052000b01d8500c0040040c0905003001040140d0071398012804145c07803180f041e03914901201400f40e010b20b08508400441c6a160500703186000c8d007040410b03a0b01c52850700c001c0045460700f01c0301c00000c2000075a1024000d07541e801440d1120900100e121760b00c80203441c200300400c1070000040040d02d5075941c0a02a513640c03180c0c140e1707030480402150301d40c24040070814006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 511863147 1250 511861897 511861921
    0x9090b010504051504111e1c1e020304030e101d1c05061501020705060918061201060b0304021009030b010b0c01060b0f0a03060605030c07140a02030312070f0801050108 74
    0x245944070800c0200000000800722002d8070010403041b90b0110340e044c1c05001e8000031241c0b040340c0e01091071400c0c900c808647c4210902020819905980e10180c440361003e1b041410261a2008011552070601d8100035050118082006103e0802982182d03903151242c81d01007940d03285040720703059079100c0c00e080002d103041403840298070800101000005c2182084450700521400841045070001c0c82c000a0a000194000500501d020454052a52140d94900105400c0c0b4003081300582c031500001642c96110080c468015801d0801c04941001d40b20300441c0520b00c200c501400c40c15080c002550302c00c034030303102c00341060924000421220b8500c10040410010803800082c080380c4403007501030381d6001180c0e4080503207030115045640f1038051041300090405401c1070750951504908012072440303608002040c2c010f42c03649115600b40c003000841b42d62680203095035181d00b4001d41024001d01d049685800048030100780d5485507004110140c180c48041c0d594101540d200202402 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 511864397 1250 511863147 511863151
    0x5180304181b0807090501090e130f02040c121404021f11070e041a010e0a0902130903050702130902010c1e0c03050708070602070803120606040f090603030909090b01050405 76
    0x6031850b00c91542c0c0c400301c1042490b02e00c0078a603946a500306401d00390401841d40000d904101c2c148603400c5014044a086514426030040040140240380407580c540312a403e0110345000f500107051032400c030840f6411480859881035031030b038104000c521806002049443c01e48010750024048505180c03c0142420f014914200c181488a120500c0c0042a031a180043d404a01c050580c9014042042040503402c1f0200c007021254040c00e504000305403100345d002406d0000840e544144580440d200d0007641c03075807103c207407004020b158500d05014046074401b00049200300b0380101d100110314500d01c61020456010381d40d4940c5841550b54a001c04c5410180700f900407150581e64000040c0f6a08002e4091417045010306900303460030030307002e2400311141c00204c10b541003054148048c0c18004140c0344550404061007036a612920086102c81c49550825a5810f00f00c003404107403440b02d038000e60f080302e05c25600e1444103591100610115003c1300030040414844a00401c81c510f002c1d04015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 511865647 1250 511864397 511864439
    0x231b0102071a040f05030721030b1e040608030c07080f03030c03131a04030201090b091908031b0a0504080c060405061b0705180108060f1003120c12050d05180304 71
    0x411303a8180342c0b1001d2840d0401042151890305e110400120201000e079000307554400c40c1024000004020000340440e0a0500d1040f0000c0302c080c00129180d0795600010000c0015001340c90341c40f5409400141c4074403050040115a10403000d400c92668800000c03684110400c03510682151241c20b000e4442c0c0d409960705036807000c0f03030b45114428042c0058000b40924485e400005292510745805002c102d00104810095045014400500c50394403408a1803264041c85a5a481c2c0d140010032041841c1c1441c40e419500c004030b03001090540040040c01038a03555401ca44180c6034403000c110071171040d8020141c01076024000c0030188062500102e900500d4802a6140580c655021403000c005c042e05501403e40290010818841d003800000e8005440503030600207842e1403030460720001d180f40b00c003d20007046020b010301c426100359448080c140e030100384a81c070130026030001015034100c64003d020303c40c03500c13002c140c04800040e080c4c03c0c0700034800051030406191131400382001c10508200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 511866897 1250 511865647 511865663
    0x3010b0c120408010b0901150210050a060306090f0b0a0203150f01030b0316170a080a0f0e0303040303050a0e030105100b070c0306050a0c020d02010507081303231b0102071a04 77
    0x4205207407503200190000d00b03110000001c450740300e5405c00000d400103030700c561309811140c1d030080700d410b50206086000041041020440341c80c0c000c0008000e256990025181d60300d406220010480511403001d115070140446040316192050504101e01c0161115400c45c18040341302411030a0044e00340c0302582050400080d95082e140200f41000b000144940c0341c2c0304900d1060000c590000c803950321048541000b03180400352a0340b0032110f0302c9000003400601150084041d0001d1148244007810303c40601500e441c0c030f99a1a01504d02d400c000380140108040b82031000c001e06051080a21039a014403082c01060b2030401004125400720300191400341c1e18810201c0455027030300905010f900402d80003d05a8540c1c01d00a0030910000041021079041000b0300400c90b40c41400b486c0c010030410b0709a10401a58681540da4004803a40f030080032382100302e0041483c1e103030809014841d90350310200d07800243e1101094200c4c8100346c402011a0300725916680240e09000350903a000b4861085 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 511868147 1250 511866897 511866913
    0xf0f050705061503010f022706040b0a03050f090a030c0222050103080403020a0e0708010e100306181707030c08090f0a0806010302030d030911040b0415080606030706020d0503010b0c 80
    0x361402c24408039024401d52410030010f09581c1024412482081003041045051030800c20302421110604c050307811102c04c0800c80c6209942e110011600100303480100725a07604640715001d00074020840d8000d0f20382102c04006509200c001c00c00c413100c00c0d8159907000e00e00d100c9a003040324950000e0380c4117503003188408662452030301c1c0b84a100e0195000380342c01515185103104115100400740c1207102240d51000500041e190400c1c2c5942c19165240e9213001c581d991180d008610144a80c00602080d080c080150003521000503542c403200c1c0500c01516440e110444107488500c0754270001400180200b034181c020551a030003800001c50010a048010351140c40014404000c580003804180c00c828010011840e040010303400f0388071242005d0000340c4c0c0e0758a071074180900030013101d0300680d2a0300302d52034141e41c0d0342d2103201c42d109581500b4007001c1d20350b0802661400708842a60180c4144080031a03490b0001610040d1441a03aa580e0311716030802507101e00580203002003108504c01c0d810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 511869397 1250 511868147 511868153
    0x10f0905030f0a150b060703030f1808190f050a0c0507150801090b01140d0902030a0204050a0c021504021f020a060203362a030a2f010f0f0507 63
    0x40a40707003006800c0000c2900f082c240c204540700401440000a8480c5400049901d0f92101e03015940165010705000070b10780b20310540f50014004d045800f041122280e8002800c200014001d4000d0007091140e03550f0710003048105a4020500b5410040402d01c01c0c406503640328440c800c41c40d5564072035010b59602d159140d86070820314450340008004150050010720007030700d462051074000030382441d02e080210884c0785880a1445000c14071030303070507459015210554900308150406036602609c00c02140c03800e800d1501c0248070305010000103004007040b44620342da006488500994008149510580000104c814207802c01144070f400c1d4000c200810f00070035000d20245210741808103d24114800403a00c0e4400880c004450b450040500d00500039031400001d11040215990420b00c0c1403010440003203025500074440b03941e07051050808e160100008010b0071030a00c407000c075100c2c0600070f55020b174680c1400201203190000b1403000c20071846520aa00042c0e24145604282d0714002c402c0d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 511870503 1106 511869397 511869403
    0xb1b040e070215010602010b181905040321020711010c0506040b0603100f14013201030b0405070f0809070f0e07030b06070524010b09010f090503 64
    0xd00080e203858000c200c07030307010040c1c1c02008000660351003030001e000c1c010300d8920901039100b03001040361400c04131083c14001e00091104008007240c00c0b0259000745030081c0198104011144103126080e505e140170091209a110096502d022900b02010311208070701005041003480720500c03000c01c502284881c1c006a005401c6002501d070307a40020310341050000b0b080042490402441400701c1a548540520701c550300d60a802030780e0b034141000f00d403421640010764a4800003011a40400c0c0714955076611041410001116190030010508a90b01115003e010aa00f403101800741034200d480c15500c0015207001781066418103e54039111069881542441e10301c5a02040880d40603800041003000040c100c3d54640f48941071507941e0710380400c095008074000100c0b08840700c0305039a2242c180ca10710040586044503100044510003446c282080401c0700f10341c0b01090a90f824 = true := by decide +kernel

theorem cover : BRFrame.Cov 511690647 511870503 := by
  have h0 := BRFrame.cov_init 511690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 511690647 ≤ n) (h2 : n < 511870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
