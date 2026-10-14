-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3566
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:01:53.748122+00:00
-- url     : https://prove2.me/submissions/f535fa2c-139e-4f66-9b89-7fd9abf8faa7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 641187050 ≤ n < 641366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 641188300 1250 641187050 641187089
    0x10b060412020f21010617150a02090a050303120609060108060607120905030a060b040e070b190509040218031209150d151502060109200d0e1606020f07 67
    0x41c1c410802c070b5800c0d03111148030a000700340030b0641c40058002040d070000041480c10307e50b400000c1000014040107a60190340c07040610126244950340120b034144015132288001d43c00994010707002d070040c507090f100125400c800384401d01e03500c40c05602e05541c1e20071580c50f440c0044801081c200e81150b0009410400c2c040060200311190780903e880b890304000c50744c0c80d100040c2c00d000019006a0f1116120b62060342d0500d010f1192101d06030300340c130041a04070324107100350040d40900514180c05850005406020a00030300c1181c2210340010000c43d900c500b140c00c40c6003000d4115100601a01c1000d290790a103006902c2210d4544000400018208403d855040d481d5448044450340303080d142d8000701d007503004410500c0c0103024030301c100040f40c000f0200c00a00c2c0201c168064040c080c1090403400080721000412501071511a20260380c0b01c480004032000b44c40942c03c600010320882100300e4207403050b8465442070320b080f6425188013040103007846641301c42c0c43c09039244c0c0d00c018640303182 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 641189550 1250 641188300 641188309
    0x121f02120412020a020307080313150c150b0603240d02031207171b12070f1104180507050114030606030610020a06020d050f010b0c0d030b0414090304030203010b06041202 75
    0x800c2282d440c81100c01c404c00c150301090070042e159004000e60741c0003180c0142d070643c1611042000e060340003101c05207100385e0070004102000908000e0140381c1c1d01c0c11648807000c0c0e0f94008440d40352010740056964140548035030020b488102071986080b00000704200303289404203000d075070039070001c00405500c1c501d00300555a59011040c121011410742122160780022207010746401c12071048000c0c898a00b150b0350381c0c10200c0c840c1400d030354082d08100031000a0b07540c001c00480c40c0c1d08504144440d0010305e0100b40108001c40c8080780743c00030402032204210001801d4400c0d508282d85030701002000d00007140e0b031400b00782c03000d69020300705000040d2142003842690803550154812242c071b403002d54070b0703640480e07109200ea520703083d84820801101c94040503000c0c1c01000084012032500c1c41d648140c0d502c440e003a02c0414201501e400240805a5458016100c0d001c9034184070380850078420000d554980c06884105c1c080e50804403504c6491405c003040d54201c1c2d00c40c548814600d0b42d2a820030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 641190800 1250 641189550 641189573
    0x90b030a09060e06040c120b0708041109090a02130209010c060f1d010506010816021c030e030d020301030c05120601090207020402250b0a0507020c060702030c121f021204 75
    0x100300380c079074506000e008150580601601514107001901c6075042c9401c102c0e210389410741209022104918445001542d8103108a038070408601c0c009050781c50307628000540c1018205403d60040f0a1300501c906603401044801c45107108540310b0341e500b0b032a020240140d0095500d07203408201c41c3c0c1c4240340440c0541d04250314070114080d0010740c0742c40d564500062907405034254500e80c0c0d074130800c01c0010b5800003905a008601d80003a014148000d102c000d681d0b000703820b2516041144406079800450003900601c110741455001e6948910341c0f1748039900203400920050f07401000724100040e003070422a800980c811000b4000e0b21040e13003816082e0020750700c10402240c10603420000001c0000c1401d21810892800154141c0710702e40301d06015440507000f4142d022064a814184450907070000740016008230300740c460949a441303e00029050503100d00d950341d0003546040060702400c00108490214140128561131820940040c0d001280600c00f1003204841d8104086008200c005190 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 641192050 1250 641190800 641190811
    0xa030212030c0303070504030618020d0609030e060a030c03110a050703360302031b0307140609060406050a09080a031b0204020c010e01023007050c0328030b03010b01090b03 76
    0x440c0c0c540402c1010701031842d0b008070703120000120080b50500030840603006501d0542c100c01902d2406e02c0650300094103a0317070030140c01072101d07a131010140c0c02c1500038014208405801096035403036294140003e40a080c043c0030b140c00007481c1c00b1040c50708110045c00c1e540f650040b59541820030007036940580345036038910786d41c4c0c0074040c0d07140585d01e030240c408500580e1220502c500f4580140f640c811b041c07030540070181c80c424604840c1901c1c0381a4030000394580c101c5c0c0540c0c1c1001800910303800800c8588c46007281603070f08a040020302092503030700000207102480b403c0c1e94006030650b8400d00c079030b2a17060b100320080c0065665107506409007401d0a000d02000c3c00180b005260800395052142181d8826120341c00c142d401050404081507000319a16990ba80d00250300b08404144526020f041e4000704600f080c0080860450f1000004205542a500910307030b450051049000d010f2118540c843c40b0407000034201180d0703030075a00b81130050344401305040e1aa011541d00b04104a44140c200502 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 641193300 1250 641192050 641192053
    0x130b0c04090507030c030c03090218060f0301020f03040b090a052e140703060906050a21351206040507300b1002060c0706090c0b0307080906060a030212 67
    0x72640c82075501c6524040d10440e1000255481c00746809401d0341c01102d0050241072900c00c116002d0303181e032800c048030340f00035803441841c0d682c030b0703400151010342800b030030982540c4003040c54008006800c006501450007100d40d04203c0d5a02081a542c5501c05000204035400008542650540c40791059085413591000c004e1410000034040d0304440c0e050100c400c103e118a0144a20a07802d445001c0107400304503400d0203158100303008200100440d1007001d8541c0340c003501141625003082e2080c2d00555225121458041e02030b43c050101c070755040d8600401c003d600d0748052003281580200ca082c42080c104411b15913842070f080200424000b0458018001ea1405100f01c0e4005c1c0119600c2006054400b1000b041d00758889074121501010f540340101e00248020413150b40000309660301514070703420300c3d036524501e00e0800083c2290b030384000c018290300b2402040300c40f04400a94403d52040e61560901d075101d06401ea0707038510580e100340d003018450900b40003500303100c1c0030304282120307160 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 641194550 1250 641193300 641193307
    0x5180103410a060e070f0e040206160f060b010f270f080708190209041b0f0f08010e0a03200106030803010b04170a050706201b04060905130b0c 63
    0x1031000708070307903000450094540100c1e031400304100162040c403c02c218101d0060850300d0800004169078002801601e004d4166a8001070466444d001103690030442c0c034001c0383c10070361180303801c2070382e054924400c42d0364500b0440d1011043d440380c04441c210000c0d5545034003555000c0c1c01c0008181c0700102001c0340040300c030080400d9080f05003526000814210000306050303440c01d05014180800d10007203140003100096402c0240e6100c0100b81d80003a0040d01d0300b0500d241d03650011141202c0c5a21101c50780000c4c00380020b0300032601030403000b141c030034400038817141c4200001c20b5101c280b200c0004002c201c404424080110442c01501080400c81000107034064507030f1241c40c82c6401c260720494a002c000034080c0001c03041c07200f02c54009400c060041c29940c51b1569420740ba10951b0042c10104461880724249103600384160b00c640d20714030011b031449449400400c1c8001007080d00600c5c010781c1040b800050150075841450701c0f6180c03043c2c00140d00c00503966034642e040f201a18483c00d40c6c1007170 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 641195800 1250 641194550 641194643
    0xa0216020301050c041d0105090a0b061e03040606170a0809010507020405090a0215280903020d0c06030509030a02100b04021207050c0d1d010f0201060812030105180103 74
    0x3d10030765001d4944201d095440c3c0d0b00c0c10b0044050108000150030900c00d2142c010407403030300c1c2c1c000c0a503044840d1322030201e50348640b0783c00306003140240328000b68103024035008501c101d8010300c0250b01450080d0300502030941c445040703040300400d11134a01071503400321405401080315140a8080c00c103051610b1868622541c0004003629400c3d109001c03550010400002140307000302c000c0300c01a1080d0200b505048000e0b101c0381d9980040c3c11000c070300c80c00c104801070145110f1480381c401b555004018804c4050382c1c2c10450a840a60700038180440e04d820003144085600000b51040741071a907000f051040c0711407182c1809403440000854100e0703028000419094070500596100728425614191504600d406152506220fa201c03401400020000400b4000d011503481c6402c840a003455202c42c01000000c078010102c6a010000c1c0303010701c90f1084503002c1520021412140e040301c02407107260040b080342281410a110040080e4442e004810f880c1510402004545065420454450842 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 641197050 1250 641195800 641195803
    0x1060504090c080d080709090e03070206030a0209190b0f1806071a0a1404080721050703030f1a090a093804120c06182907080a02160203 60
    0x401003118511000b1000740250f6404002ca0401512985010b41081c104202c003c1c04050305801a0070b078154480360144213100041088a990503405405541d49141081c1540300940000b203a26115001124004008460300321840c4113880d00e047c0d030103181114005045840d6030120184032003040307804000c800380e5911013000e4801b43e40941c420150445800204951020004001540c0949001020317004292540310b019841076000c402d050365002d4504155140310641d804d04205910006030365000980d00c03002500425209441c24002a84c3c603046000995590246613050340140403203642c541e24040400f183c00c0039400000261070525601e80071b80038002d000c4414029000405000360100c0881541c007100000c0c00007801d443c8c241540c03040d80c80c0c10380001500410003400844800d00515501021a110400d582110768600d00c0c6800141d184002d42c40b824140c00c2c0070070004610400780c0e1924814074203035451030255942c0058420083d04100050034407515280c0107800140c80 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 641198300 1250 641197050 641197061
    0x50a0e0f060409050f07091203030e0319180e010b0d05070507050d02010506011e02060a021809040b0106030e0f0c1504050d0b01030b06100c060c1e0c20010507060b0301060504 77
    0x1c1d2904007080c43d2030050751707480f200300d4003030405010455584420006404821a00628942e1618001c50003404d040c95103403460140340014030801000340600f00750b694000303034410302001140a60b403c4240d904d11a40301a16000d00c40d03c60446c00802406101c06040e51023141d000885041181c104162030729424a45540c0c40c0051015079541c0c02405002d40e040381100c40c1c42080c0c14406000d03682c018800a442d00c0024005c003203800d0300458001c00342a0620b0400c4501c84c00544540618502400d00344080e140c01c0c03041c000401d180c0b480f08049000042140301c1c05030b0220009025580c5000c1c280000d403c2c09840d0b2a903144001d00000c101d99461401d1202440c0c051020b240c0780d941981444c0005280107080c151045242071242c0388060b1700040c1c0b803005903400c0b4130001021140c51909841607a0708900000100d102d0a01000481d03801840d0300b14421300940c8224040265207150901c1e040c049040180410018469200003490a4200c0304004d1780143c00404c0c1144c0d40c001240039105c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 641199550 1250 641198300 641198309
    0x80711060f0f0a0e040b13090809181b030405060f060409170c1b0a141c03050a020d08011805040c32030309010912060209060a0c0b09060106050a0e0f0604 68
    0x1a0b00040c401003d03079201c6420b1a8400048404020320300042e4000340040f4141500601c50580f90458001440ba102040d03400c0d1100141c940507181d048140314002400085521103c0c006103c150394482500d01d00a9031b02c1650f1041c01452252503a880303500a84000a2410364003d40301c0004000081281d403280c4a0036800c202595100c8284078580c03400c0115488650519281003040c0500700d9031040180012643d9060000e03070200ca0480c0851500c000740300214915180e03401d054005c15034060024400285294281d0f60500400c50f01110040000e102e4214904004d84d10621524480e6016030380041c4240c0350848003694034121140a6840010711800200241804d48500200d450394030800c80000c402540c90115084c002802d2070089004004034826a166000c1c20020168115035181030020629503c90200100c0203218020f20501141c0c0398010b180403440076a000204181681e6031901d59a082c00e005400c100c42080b0015a016800206100c04845030b89a5900820260 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 641200800 1250 641199550 641199577
    0x30a020c012a020d0e010c1518150e0604020906060c07060203090a090e19150609150509130602030703110d1505031606030c090509090a021309080711060f 68
    0x44003070300e4800700e0085402d20380030364001c084001c08180e0b1120309050402001d0070314240400081c1480101c02000d04641c452441c6040c5c2810560310b224406d4105261150840d8040041210b683d041524041c240d00d00d265408a00030034010300d012000c0d258000c0380504450b0520301300010316071409843c1d078010301c09a00000f50602c1181088110000500b103d02c42c24172a030903042812654078250580301c440003600102c81501008140071000c1c60815889400b4002d090b1070701910f000070f140750b000d48200c0d403080c040c0000306801e00650710391003400e09200c40c40c01c1180680b20b480180d2301c01030100080540d1031311074403e41c0071110050041144840d5002804409070000a0601381035a00043d01c654042501c02e81102d56110108003540c125150120b9148115901500d006140d40c00c11603109410303008024040c0c074000380c0028894001c642480c01c1d070140904000c203c81030340c0405010350008101c2580810789041421038844d0014110a01d001480d85110045422054003480c84 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 641202050 1250 641200800 641200841
    0x318050d031422020603100e01080721020913061508030d0e0a0f32100c0305072003090d0b01060f090e0118090804060c1b1406030a020c01 61
    0x1881003104045070b100d07403008520004001003042c0b810020f050108001d05c43c40c400000941c506070b84000290042c0104c2c100d04800d561100001ca849044074090303115412000204180d111529a00d813500180d005020716480c2d403070b02d0881c2c500a40700754030161401900e50060902c103080801041e0010048800555190084440c084e000e8541e04c0301ca212a0b40c0c0b1030401c520208840c2401c80c0790303183d03020200c06041c05e014550303612481001380c60f04800303c4912503440440d02c8081610424042c4c0100c08016031100940c041c1d040700c2d0140c1e15940060b240150707915881c085200b000c1b802c03100c81011a4100340f0810000307186c0c140480400c031140c3c25014010410390341c0000010003800c1250900864a604040c3c1a80c0200014401c1c5040c0c0361500240c0300d655500c90b400243c1e0103400800c8243d469032110300141c6807402801d011100c504041c00740700ca08205202102e0141c81c2c080030f8400c0521403c508000e040c0d00301903c031151980c0d0030050354500e4442440b400c0040407503140364888 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 641203300 1250 641202050 641202071
    0x31031209030c0b0315060d0f060f0303230f090d17070b0f04020d0f060b03060a0c111603110a0902030907090515130e03091306050f0102031204030318050d03 69
    0x1d03201060b900400210f00d05001740301d42c5040a03464881e0602c0c2c15248591100b0308881c0c1480600040d441c0000c0c100c0c5010004141d1600c00351000003030300c1c0280c6a40c0b00b6880d19502550440d52841000385440c0740902240b52016007040061400c898000c00011110f01c00341c403082000e0254080d11520300c080040c80404101c03a4961040d44074000002403c001d1802c1d4010600b00304100c0c0300204035800e80c0b0402010810329600261014001408a54075450b202075075000403c0b1709181000819880c440d10a01c030000061104100102c55070107100c2103103550f5820b0710680400f14400d5200700d0451020030301d461144095403003429078a00402c03a070ba00c1e01003140300711b501c080d01202c00c000841140c0003603031300d8038800201d907940081c0002810f0360801034641e0643c000d9039400c0e648020f42c00e80c40607507030750f2a800035010358604403046c4080302a840d0040e65030744143c5a03800000c010040008001c01e020343d101818500c2d040090003807520f80b41c0c0d18903040c0740308084160040780d506d0f045c806 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 641204550 1250 641203300 641203313
    0x314010507020d0c0b0708061305070c03020c03121b01020405030a0309140a060c02120708120d05010b040e1612090b1902090a030204091b03030917033103120903 71
    0x40f4035015a05040035054101d4503400c0225000030b00c0b217418051078402158498682d030b41d0707004580c4040c510401060400d100000d0108607249020307070041c443c0383d0b4074408a14010403010f01c5c12403811501d51504002907490041d45e00c00c01c0402a40d551300b880000341a450274800c4801d8a817181e80c4892010341044000710401c002103154601600c048002800b8198001d201414225011248502d4444100c4402d038a004010740026891f0b00803c1170029000300800040d00340c1c050384170001d020a07a00e540740d204550046100b610303040341041010480c8940362502c001e0344036265141051041094416400540e0840d140803101d44a08070204443c20203044005414a03045850551030b003800e49000411072606030201a110b00e0b0344800d00310410030281301090341d25015110701c2c03042650301c2c1000b4200d0841c1c1c1c441d5086102c04650744409811001c0f00719010603803007a0928501580d4200e0302510b5010500c0c4203a8101c41420000c0049003043c9009c800f1407400369640a910341c10341c03170b011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 641205800 1250 641204550 641204563
    0xb040e1c0201050f060d031d06040f030212030c0c0907090815040506070207141327031e0f030914100c020705010207030c060806011b0506150105091513031401050702 73
    0x4502c0c180744da10901a041d601e02e805c0712902c41d0945412440806440b11303e245400c1c0e940e10550380300b4000a00000c4c0d50308201c2e910021203000b11007a0030884540d032038040e1a4803520418120b5600824620405c0f440e01c507030b00359000213591400c0c264044d11030780007a03d000c00d01d15603034002600c0441000104802040440d80c01481440034140b002d19100b0080d00804484111314400c039181c0600c0105000654072805021400c5100300a8011100d0f61a000300107140005400107140e404483c40c1c00c001c004170002914205668239039851035401c801301c0003850f4040080b00d03020400d201c03c0320091070800c60181556045180043c10f1074140c1c0000c3d02e8510315521050545d042484200041040c808c0c401c01203c07072504007003c103950b550004803204952280b2062602000e80802401c0c000001050351145000e9462610b0340105040190340798090f82e044d071030b4400501c40b4115085803400c000341c1011140c840a403e07409032683d403140e070104000c1480d50b83e56907480080107041641044003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 641207050 1250 641205800 641205811
    0x120e0f0c040504080714011d0c150c0f010615020d05070b160e090a27081c060f08071a09032a04020c06041b0b0307030509031204050102090f12100b040e1c020105 71
    0x100198050103011408ac1d02e51317070703c1e91081e607c00882c44030302c0b540c0c0500070030142c000741e20002c120315a11256031a0b03100004840d01c4005200d0042400d54541c050780444038466002100008180c2d40d0902000d12a8842c209810130010000381c1c41c0001e0300d8a421071802418402c402054807000448005c4844d003100d8003468039212040b140001041c000c0040f100e03905226031604521880301010780c0040c000c035600000c00d80d01603c00c00982c041000c6083e405640340e00d0b03142d5610024042d41008c3d14000c0f4114982d0540082d04076800c05400c417509400d20500b9541ea40d00300150b110300040891300710441076116504484200010031420348192147e040b070018000d1681420602155440d000c0103166a00b03155960000c1146680100195004c0c907070320b650807540f107140c5850014045d4100c0301c5200c1c02000e01040c0c121140c50035100c0301650700d280d84024510444100c11b2400501074071012650042c0c2c0c0c030741b003052460a0911a0006608440c6090a80440d51070070080c06c59034001d01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 641208300 1250 641207050 641207053
    0xf01150504030b0403050c011b1b060603020d03020f0c01030207020a09180c0b121f17030904090311100c1e050c06010f0510051204080304061407120e0f0c040504080714011d 76
    0x41404030f160011140c3c0c01030990440d544ac0b56041380d29200b07008107110340004c0d51184042d034000040503070000b54644034101800030740328501744003001541a4000c3d5117000794881850751041c80301040d51390040c4114910142d1310340f6200003549a841c4400d049130440b04020200040080640b107103580803c1d0040c6d4241140c03d1a401d084000d001d0035607050113070b800e100301c0c1000c0c184500a420400e8550700c61005100700711008281c175018200800d0307900c0459850040c0701d03500b410350b0024442c0310076040054403a01000c1c0d00b000040d140c50310034150030009008050000c1c60031282d00b0044140a80070f0104000140c5082401300b14981c8075840302041002030070414034410202c0308080d150403030b9001317603c01e40b0b9465510b0000b000c2d202407860418082911710401102c01da0001803148480800c4134208401140248180d403950103840c1d03051420307803003042c002c8280c0c10554402503105028895203400c0c40c081d5a1784102041d00c8405074082691180210700c601c0d80c0000702d6400d40081d980 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 641209550 1250 641208300 641208341
    0x11090d081e2508040b180a06050306011e020a061a0411041409040201030f0203040c21030206010b0a03090b01060c020a0905060d140106090c0804060507080f01150504030b0403050c01 80
    0x1c2c4071603141c200c400162041407070000911070801070601d003a140544003914415442c1c83d020000da400720412440454420400703594000765460099003207e000394010381d120000ca0b02c200c60f100031891101c40c2c0140441c414441e850001c02e441e8440e60804c000c00d02c14242603034440e0820401910704d00b00c1c14940b605003c210400031300001032156911450282c80c10f03c03a540d51800181c0043c600c524030002074900000421040003104840241038030a50321082d100c2091802c0000031640708a80f008001d644403100510000c0101400342010040e40d03c1c0100d8220426981c103c00a44c0a03032200c000f0075072604e00c001c214500450008040c002d008010003181c6055000a55010f0301d080d4068a004145122a000c1d0300b0290003c9028042040c004d100d090818a40201803000803030f0141d810318a040046150184a00040f078054158074200b41a16420704040700f0310b00b01040c050200380003080100000040745280c055108a0103502c3c1d05446005801f011800e5880c4442c05909064140d1b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 641210800 1250 641209550 641209567
    0x13051f0515040c0c1205090a03050a020a0b0901090e0903070602040f0e01080109020f091314070302120606012a0c091e090206030a0b040209121f050103080d11090d081e 74
    0x320444c6010b40d003115000b81d14581000003520288692170703403940c0001c50740401005220b80056070300c440b03d10030390b0540506546d80103107031a1806821100e500241501408000c903000c1201d03002d41040c1d012094a280250302e40d1510100e911940c04803001300b1a410b000c014411424129030300402c2081c00074400140554006003018030301c41203039403180080c00c02190303202008881d0303000000d501c0003540d200041c01c203848542c0c0d242d192004902c502890b441510350001c000c200a80661f030107840f040e480241d08142014056280c0011950007425401014080342c0c2c0d103079083c001030200f0b01c40042d1680041b2050304441142c464040c00050420b10101c00503121502126848148034000140114030b090026020b8400d02c941c0950010940c000e601781c101c0007103072000da80381d0400403004180c85030b0020b003c1980ca0900c00900400400d00c90703805040000d8220301c5085e0390000600345403111100008003810014038003a1180c2e100815010101c0d100072007001c440e40201c110756030070b01c002c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 641212050 1250 641210800 641210807
    0xd0206160516061a1302040e010608062b0b0109090c0501030e01060f080d08091507031a030d0c02040f020f0d02070206041a2701050313051f0515040c 66
    0x550350403400308140082c05044110b011003044031483d41c0a00f050000007086607140b03082d80e04400c5164410300345903181c4142808148216000c4840d42424050ba0741e00c0e1000039136a5030710040c00700d5040462502681c1198450031406480801401c004910360189410041c649820580040000500d06841600400c0d680710010084031400d28011604501c0c8031040e901502407540413034618034444001040401001c00c3c098000c1c0300968034403129550350035404e85c3c0c4045025000c00c080d43c26030040385082e4800d801a070b807803000c540302100884410402291070304500103484d500044a44402d1002c5242c42c2c0509108031812207402c2d4240b1403c0503000003644164803100c46010b6000645008640b582c00030b40b0010541c480803007a59001070364811005600c43c18041b10311110740e1802407032030340646604c00d080d0103045c0d6845055688807100c415100790801001d07252071107030a020304010740c200c52000c41c80c082003032004642400d107658100410a15615420300c2a401c21047c0d882d140c3d030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 641213300 1250 641212050 641212081
    0x1020d06090504110907120e0c090c0406090605220909060c110717010f02040e010303030b030318060c01110a1d0901060f2003040b07290606091315080d0206 69
    0xb285c00300703940d80f59080c01b034510703030000341c3c602c003110b4108280c5a201580204e20701414403c1070301c0f07000840e41c0d041e220484a01c250300400020480480c005c0c807400e0300c9800600b000500d0145083ca081d22412401e4003624060b034402641c503521021042c080010b180110031440845040c0032000e450343c842e445456030001e0294a0300852100002c8210703480075046003540441c000011562251600620100c1100c00d00054020a0030450440841e0a000080707620344454040303078111050700c420810000c0c0c0e00625a0402a640f282c51004598104100800c41040316444298002d00c890500045001c44000f1182c4600d078810700401401744c102d8600d2507024418038001e00700040746440300d03c4141d54049103490f2848041004101e81d40300e1402003070170901030188401e450a410050480440d00410344507110000e80e070104869040c820050044208001d00ba0000440e201c8608000c41e56014680740f61031558110070005550103100c01030003e000c501c090702c060b24002e001c0c48590398 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 641214550 1250 641213300 641213333
    0x305030a0e0d02060c0a0201021239060106020303011e08100e0f070e01030b0f13020f0114120f01060219080904061d0f130f020f0103021b01020d06090504 68
    0x1000301000d0040c0e9550b090240012070380244650348801c0034602c129501c42c40250101c0c00741c82262200320f10b4081400c1a681c100e40b400d0a0680e080c08410b00d00c416600b00da0307040c540d0a80c040241c40f141844240203d41c0680381c9507005503141d40c50b000090b0b40500c400c0c2d8040180040280c0140718001010443e213042d05590b820110b85000354400140c0b030086480004085c5009102001c240b110150107054100d82c000c000d56402a280c1c1500010702c7d200039618030040c2c24644180c00010f081c9440305624007201410240140b00c0203090300c3c151540402841290b03214200c081207010700c040d04545016114910003002c09415104041e0704d110b801136006010341201240320840c903901da0700018054505803070446200b00090700203a803048004e0f1600c0300140340300e00c00100c201c014141c920080705d402810611b41d01c4000e4091040440b40c80442a04240d000c0107003a003440e0706aa0f0308c9a410422074001603441c0e41d101801402c440300c83d007103110706074140020700000ca0317401c8882800e600b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 641215800 1250 641214550 641214557
    0x301050708060f0a030807260406090801140702061618170f0f07030807080405060f12071b080d0f0510030c0503161e0522051003330204030b010513060305030a 70
    0xc0b0001623446540460307840c55181d101b000a01003800c95011110f44100d69a460091007490100700100f1500c200031144280140e00620000714140145c10082c0c0c0030030f203242080098010055506442d007030141d000103010240240c440006840200308242280034100043c14007500f0f00c0941d180c440e10a440083d00310384003c2040c6040c81244811140240700080166070b440000c1481c01000b5005062101c03a62480d920004441900800c284401508030200d440d01103104c507502c0040c0d0390000c00102d206240c0d10300c0c3d0b1240c40110b51045900031071a40300d442c416580365142c007600d444466013015009400458110f80c03152960040c0d04203030350760580f410070806900914400b01401c41d5020b680d0100b00001981d19521000c060a000c0412040c1c4c107000d1580c5034103600528045030f04c402004001c4103040382d011301585003a410fa40c41c0c0c3c22800c1e800b2507558556204282e0308190025154240c944e00104024900b601d908400340152803428804189191512500d034000c04030f2000a1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 641217050 1250 641215800 641215823
    0x105010c05030903010f0507030e0708030d0c120923010e070b0d092a0905060d03110708150a060801050702070509060310021803010c17240301050708060f0a030807 72
    0x2000000c2c8166124200b0140080106800e4010303004003a11003501e00e04040b03480c0c204503141d0783c20f000c0f448006907005440103516040d0782100d00001008501d580d60104440c41d030800f07048000074003800e8400f5014501320400c0ca9102c0e0000d240346542c9580d0449a685051901c83c60b00c8000310b625001c4035002049036864002000000004d010117400052000c10114400c0d040030786600c1c900d6018154441006c04515110710704801141e50603501e050740601d4080500000070301c84c1c8000542c40940805541400d5680d502c15881c03c1d070000c11004d12a00c6020810014032030320b02c0344800504a0000a00941c182400c019440701d14500985000b20541000940b40f510204510759030850140307400c65480b03880034802040d4444080f140341c0300b542030610080320540304480003009111130394000b841c03580310414101c502c0717281d00c0c2c8800c4403034821141d480c05694082c0b1417103200d02525141d41c049860700008000409000c58901403003010f10030003d0010942c26829941070590128281a6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 641218300 1250 641217050 641217053
    0x142401050708031f09090c051207080d0f02010b010309020d2003340302060d090f121205070809032b0213032d06021b0601091416080105010c 62
    0x500740310301e140c0507000000000c148521030404035034411441e801c000390103000f940c840708400191703902c0d980c0160000b04a14810321032882c280d500601c480703240c002118040f5035510221030400550307040150100d0400c951042d0a2a02030288a070400c0c02460108089903050380001c1c1a51000716025021604204406a00540390710301408050001402c5500c00000d10041d03610202e901c146203084040149034401c0400d001d040424142c136402400a803d011411402d80001c0541e580240d0b0090200c005072404a11071011201701132200d90340d20700c4460010000d2100b0384001034049020040604100910340d02c010007914480c518200001c1111155680340007546200340c2e11402c0094400105040008004505841120711a444d100d112055007a048040c038102e00040511110b0a100c2074400242540d000309420b80b0840c810098890200b41001d00c5c1c40026002a148079546248101c0c0701c1e05c2940c005a8000c1e0090b0600030108881980204a40f406115141c103201d00b5600240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 641219550 1250 641218300 641218307
    0x3907030f151d0c01030f141603021312050d0923030f07150f110c090402130608060709090209100e030a0503070803071e08190e060c040504142401 64
    0x40000b0354000c5400e2886203000c480d4403014211100303804a03243ca0840358201013680206100c142240c0c0d0705c14242d54600c440c00f5241803814415070101a800c200d00703480c4104c070840c1580580145842c0790400401803074018070302010000410207102c1c041c0020800e4883d145501c04028500780b0440080030606000f091030881d00b1282e44507580600c040101c0c614081c422420000a240c1e543c6a51110710300c036043d611086500115074030b1350042154481c81d41400d48030305810900c0548041d107403010101d094400c603500741c0c209105c20b400503000d1006440c0c3c08060f030760190805000462504611000241a1380000940002404110301d400c6209943c24014480200d8001003602d40c0e88501345040a100e40c402c2352550701144011802105040703107003c64000240305515000e5146d03c1d0002141c1c030400241188450103a121041c0e503100103010310141d4010341007510856242e42c1064100001c0c1d48000300305054912028041002c640320f5004086000600016201010500d510048 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 641220800 1250 641219550 641219561
    0x303031802060c062d0609040c0905150108070302120105040b030f1c0206010b03011211060c030a02060603120304020a060f0c020603041202120301060f080c3907030f15 74
    0x203503001c42c01203181480f2520101d206442500358055260001c1100b80891484c101030740d13910310407072000c01c0000c0c0c42d60522503115500a4007940c3c0c40501e15984840d8841500c0c422900c8001040034801038000c4d558010142a4105080341825420151b051803003d035415014411244a991103141440315510300340040c0030002d95000507a030a40c81501c942c0d92081e0350741c8040500610030707a000000c208001c2003d49050711050850182e40141c0c985035500901c40000c45690f0052042001d181e0b59001080140141c1065402034065032501800f050304240a0491440a20200b0400c020050350fa41511205440d81400c5c155403423900700074200c0f281c1901c03d00c001c0d003040c000418031090001034080b900c81c0c43e88540c2280c120126030300b44503c86000038825900461480e071800701718180107141c0700d03a122a030b4600403400c0c40c40100c00e0035020304070703020780050131101c2c003030640491608500310310391003440a4001c00ea09403544c2d40f07241101a0950f00138200690180300c624850031160002d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 641222050 1250 641220800 641220803
    0xf051c091401141207090e0a2702120706030e070905040f08210c07020f1e0f0f04060b0405030d020102040501020d1209020a0f050102010f060311060a170a020a0e091003030318 77
    0x1544c0074940f0030406000100c85000306921030100a001804001c0e81c1d00070b542e1081d41c141131840200c18459481f003030b01440c14074100c0e88002159054800c02d03604008a00003031107565000b00e055003880070400d0420150380c000f509200d00304020040818a003031411001941d0005290b580c07502130702802011411940a440d01001e044414055545040d20250040343d000f01d07200100c807550581003080340891106980c01a200e00b4840807014902401c21540c1c0705000303000c0d0100f40320710b64001012120304d80c1001140c1e28001c40c05004a007010007500005003001e000840c641828400040d507a08040a401010094912900c0080b4001a04091220742e8090800716003183c6030001c128400c50f55019650056180c03584000084466001e804210f03900f1558000e406071a103014400640d00030407101050155845442054444200d91030740714120301c0200503105c0703a40c502d0040c158a0010308542c4160f10010038000c00c02078000301030048907071500300080d0040c0c54010344205030100860 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 641223300 1250 641222050 641222077
    0x8030c120a0c0f0836060a2f030c0d1b020a110414040209040516030f0314071203050a0b040c030b0901150203120c070f051c09140114 59
    0x81c000340e03500540054140d04010748440741c1c80d500c20030045825000c2110811a0b20302d4166140f0910340c0c0d1a8120008207101040116824408111042c6400010b6520780030081c0d4a03181d03444450028078445203e03440310b14000c1040a140b110002d254000603085d04540040021121480300c0c0652000220b0500000130020101d500613001c0d44030604400107641240d20f41c0d05503c03041c0340c188208150060603074010030711074590350280003241c04d0081c07080758140f28544501300c060b0a581c80b1100210b119400c03500c0e00c00d51504d030041c1280b00301e0b2040ca030f600c2e105208000000d100444007400802c02403030000f4943c0d807192140e0001c1e00b4010350183c1c03c41e10305001e0182807a4160052400468151029807860340c0c0c0340110124911141c401d20300581060011400342d80389000200d8101c0c030648031031402e1040e40d0301c075001d90700d00400088601e42c6c001210262140f0210948100f80c20150400e10b121500c4d2206048483e0040b1700d00c2810451319001c601016409401a9501807d0544 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 641224550 1250 641223300 641223337
    0xc01050a030c03230403140f0d090f0b0f04050709050709120302070302042301050a0e040f06020d02030a0603050d020c10050a02031b0d0212090604050d11030607180e090a08030c 78
    0x401032050160107607410b1b8001440c03041c03031011030400032003129018020303511214500315009014100810f01c00d2802c4500184440d510741c08680c294184a01607a01d600c0e02d0090303403d00341781081c5000d80320b45c0712000c59828282017000341904400c3d0141102d400c64010340c501103d40c6012405c02004e900001d5009250000d10759480c60040780711100d8074200d20801c50103903203a0b020000c03401200d00c242e43c4068502c00004000901d1840310f050b055100d14005800c1c0001d000c10788007a600200d400c01c40356542c40004109010042050040103071107400a0802100c0500102c0c1040c1e50080c4d0540504c040050742e0403006100304206c40e9000034a007030750082d8000c100851500c0d0008901ca0b900140b0554240d00710320050401100c02c0440001c00d900d01d0280341c030042c0400c0d50b189980c2501c01903240b5010840d1074405000c510301c10051030743d8444170114844012071030040550481c0450340c501500300507030910001010000b40f40c10440907034a95840d0000c1d9221407040301000001d80420741e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 641225800 1250 641224550 641224601
    0xe0a0f0e0d030213050a03080708090d0f050102090901050d0c06140d0203011d01060503100e07111b01030e07031e06020c0708061b030610031d010c0c060e0c01050a030c03 75
    0x5502402c81c00f03a61300a074074041c40e900c004000036a000c5001c00381c85403004008040c0019680402800418009820704010120a0b241c2a00d241c1c050320081c0c0f1035940005000e82c1c81e282ca00d04032405464212480484500c058607508840406070040c03205100020300744800f400c038494155480010301d414155504d40e110791a40390a0030360100040c80e0400f0000000c25203034021021b07030348140d801c24881c00700f1910b80300065034003440140488060003203022444c40d0b68030003801410442c800341000c41401034070172000181160020106c0c0c95698004010500004004601007440c940a0280d10365040d1500d050207402481101c0d0720507031922030320400141c540c01c003142107840341e900320144500340103801201c1542c40c4000c6035040e6000b48410240e11089003e0750144140340728100f010205a102491020b003120071070f0000b40046001000d040c005c000b541e010310b460707200040d80a00480058a00040c01d41d0003505020f00c18161581d403d220107510a5000751011168007403140700c9507054 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 641227050 1250 641225800 641225807
    0x5060f190311040b1305270c010f05090f010c14071d0603010b010c030507060f11040504060b0c151305010516120603020303030705250302070608070201060e0a0f0e0d 73
    0x103200c110b40701c0e842040c404030070780340c1440f98070340d800341c060080e0300044d00c18a6814000d00f401850401240030114500074000b0a851058000b400d900000b00450184800058003030300c07403e810442003200c00c10141c4100d49a40d40c40020f101d500b0b080403000a8072a140401303070755075030040850a91103a07440024201d00e80c41c5803d2170001003051841d41030b456807000d2509840381109554045040d2a80c4000060b01c00c02c01080f035240541e2000178100507070114030341034601e072001445111501003420300c8280303007030700ca034030002c09440b054a483c00d50b03c03803401504e820903800c2c0704103001c1027500062b0514882d224402d01c41c950003070080000b480c00500c020b0780c018682c082c4400041113084682410799961180c4020750760003e0085046030307960042122241d11084440010905262101150070006201d008086119401414006060007402811202c0c02403503141160704103201008054913450020340c2100d441007010810b5803040305030700c01500d001013151039070384204030325280a40d51 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 641228300 1250 641227050 641227099
    0x60f03020d090302031c0b09040f0303090c0f1401020601031121070b040f08060708040b0601051e030405011410050d1416051f050d05060d140706020d0c0302030d05060f 74
    0x144d40059800c02d900300c6800c10215a244000b04ea00251004080b401140441007800d08ac1480ba20300030684060503178414032510020341c0030041030f0307581080a201643c200c00c1500c0700c040c02880100702c60740c51034039100311020703032813140d14000ca4901d00408609148010f0031140d40041508460301d1b165031340d02c50b1186500c640b00d0050a03165505002c1084c6501003042c0d03005e0600d076500c40e034064450352240b4407154001307844c040c113004040069915400d02000280d03001a8500b4105480780350504209003913401c01e503200380c0007000304020400c1c002d2980801c001602c00c1a54900c40005041c40c1ca019a1006600c036007219204180320811040698405070007581c805541c0440542620440309003454100707100800414024021002811032550005a100b8001480030007500000d48414030125091003404000340c029001c00d214443d0104652800f1101610304845505240e842c004d44a01074406801c003c03548400110f030300c0765034180c211115920700414a80c901545110245036026 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 641229550 1250 641228300 641228317
    0xd050c0910230406051f0e0103020d0906020405120109020a0e0a0609050f160503070906081003140f28020d1112030703030b09010b030408070f170a031d0304060f03020d09030203 78
    0x504280010486040a1000d6400b00402010421840c0e8039420140c1f400010006034904065003032110701486005400360184603406040300596072030070b00003404401000f11415402c00d03814800500d0040e141d42803148101ca04550002c0c14903100e14540e00050000b5902002d00c41d8146000e1103941380e8000310300c03400b5014034012403454075030f400816a064001240e80e0800b00e50882e2003001103a01810405a02c9103001ca007100c7e07210740f40d40e5040341840181039600500c3d440408409103c520400c0202c0c1c0c0d4060005042c5544140b10741841c0c1749280c0a80000d0280c20030060840400071413030b120100d0f045d030007440ca03400b4820302e90905580783c001e060217400280c00c142d583c26050404101c15416289002c400f0384c95542c8030740351006030741d110b00d0007103815600a05808010400701400600c00b0030b02e10000940d50b0060320743c000c0c2501c0001c1101c00e50301e60034400040c4204d2000007140e003105c12604041014015242c0d05400a0040110001c812401d041d01002016030100041038090f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 641230800 1250 641229550 641229559
    0x1b09030a031d01020a0b0c0a12050406020301210203030d23040503090301060608160f0c050106090902090105182e0801090512160b062b03020c0d050c091023 69
    0x540ba44001266100680080034002112000209094003041d20040410610a0401003000b00184101104560003110b050311a41d60100c014040f80d204200310154030603810005418080700c81d00040d84920401c032003120b6540c1c0e11501d1000b0000b4501c0d1945541c1070450702c1c15110300e00f605003541c50380d001e110000d1007546032400104080303025014980c003601e11101a00c0400741310030802c3c1c428003070365100e4009200041400b40001007007402080e029140d941400310311500148184001d500043e0001071040020762030420020b9900e0200341e070300001e400d40071042448490840c42e0142000c04a40d818484081408545420150059102188a00b00b19008686111940c0c02d46000c2e20701030043c100081031500300880d154001c102d40020300140108581084070341c194002c034801e4082ca00e60040c00079080020b01d5018044142d114909443c2068040a90754520351038402240b040741c40740751080c021a0454201c3e62055000c0c001c0d000c000040b81d111070288540c408110203a20340719 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 641232050 1250 641230800 641230847
    0x207051e0102070c052701060c050c01090506031512030412021e0109062105070f020d0e1c0c0e040b04060501080a080301091a1e03070b121b09030a03 66
    0x4100d0500c2119070441d0440d28040c100c41c00d100401118805a280010500e1801840e60340c0004806030364900030031141c3c40751050554986000303400c00c1d040d041030b9414041c03241010891911410102e9620003e202d0881c1000001100042e0903003545c0d0340c0c2c1c042c0e24800858042413200c1210b40c0c808183c1d00807140101c1070380b000400700c41c01c0d0404410650000702e0300ca50170071240d8040c0d0600c3d9400b66407910340000740d14840ca441011140c00f10340c400b0025410803400300c903258043c0709141c0c940e60180741c5021084d80010114040440004c001e07074403200441480824070600e0829000540070110741d02881d810642843c440b49501510f080e12910f24081c00021550400940e80d8110742c0e021189505580c64081c1c420018803103160a01030304010b803071480905948040c4503141c0b4030700f6012400e001e0044a018945060000d0708480c020590400140c013100e40d52600060b8020300080990800c1c1c40d1703009c4815414092036000941600c110a4803d040540007100801c91104103103500c0381 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 641233300 1250 641232050 641232103
    0x2a04150215090a0218070c0803090109021c0204051b0913090605010e010e150117130203160f17190203070b030a060509070519080637050a0807090f0f020705 69
    0x1035864280c07940b001084a4151fa400020f02d04005180d20007800000045c4e0b086d21a00824414924140490550b0b070001040008616192091517000f50910011010100b0307000b00d20f000c58468200d040d845460b2a0000f00d0004449030081e0409980c0404184400d5070750b1202104110402e0007072100d0341407050002010340380350003071034504040141d50f00c8030341c008203502c01c00c1980d0001d0301c48582000c05890001c00341c1c804102c050312041c008003103481100c0ca412651003000040d0b03003240c290003a0411080b40524000204404003608465009440c02003620019140402503400051841004020441e1701d04640d4070407401c4642c01c2d1741900150f40d41900c1240c0390310880d820b800160320300890005189201e40304042d40411b015054400940840c0d0440ba01c01600d00d42c4800074031281007a22640b2170301c48544500500b015100c0030005801c0c048280d840f9403003401090a502d030ba42c0c0a21140d201c1ca40c0241000b5104000215550358041c14910f4548540c400c2c1c003141c0030702074916404e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 641234550 1250 641233300 641233339
    0x40b040512060705040308070804080a0f06060602010b0102101d1f0b04060b0d05042f030d300219020f2e020904021902062a04150215090a02 62
    0x34407414440c0e684c20310f09401c50b50fa1054075007026505440e013600034000403c1d8840304101d00d0082034059840031000ca0403d241c241c080e038895801a20459040000c0c081c21640c0005401b88034019030500440c10499882442c0e4920880101030b0800b4420120a00400d040c4058499084105c0340018403080410406020035103400d4440d11b480c010041140e01d01d25569540000d80085c441c8850003020540486190701102d202ca43c10301000281a51060a500d42001000c008000600341601e03141007074803101c05e000032200e0100078043c40500d9001e56000d95a41191104e00c01031708038113248801300384d00a669059447c1d00301213078801c412001e0b024403c0d1007581e061b51080b003c0d09000c021000301000d40a500104000e58100d034003800800c41c80f681140203016a0240c59004001c2450000988001058a0949a015545482441d03008000d4070340c05c480030386034031400241c07251900b214102d1030444d00d0b0165a22000c6031038140965000c01107605040140222004d10764921415041c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 641235800 1250 641234550 641234563
    0x321091a0a0b010912110301020a030b0a090e1207062c060f0402030c1e06180a090c0906030b060904051006030606050f09010807120c0c12020c09040219030503040b040512 75
    0x39001c99032224040040024505c81c083d282803080100d840b40308503507408a42a6000300c6c00391800f0903214500c1600b941044140c010040c030b850903052244440404015444101d8904400001c8100042c04414080d580d0000040d860220350340902c1d4060075a42020100d400300382d15540360148601080e8035683e8646260300454000f40034003941c10a200810050791010f165107500d40c1040f001000d0703c0e40e00c1801410a2030424003502d603517911081c0800c4080d04858012104d09403816503c1c42e00c0c00ea1040c0707000d0999581d400c00007140006040014150302030000829800341c20482008414203090b4400c00c01c5a0040e00e050156640390801034503580134414031040758900030301c43e4100740c0d886a03041da50030040900f0040110791021f1807007000e0710324050410001c90400510103080108180150191018a1000e00f452140040003d4007004006d04080e01c00e503411602c2c0044140030380d1056008550160841c1e5640d5510540f00c40d2582282c450184680c14048442c4074441c4041490f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 641237050 1250 641235800 641235821
    0x80c010f02060f06061b070b07030e030a08030406181e060e030f180d1b030b0a0e031b03130f0503060c040806160201090206041e0906050109030321091a0a 68
    0x1d034510f40d070343d00c02400025040110660a4090308240b02010414140034103000b0b001034150465950744d87c0d0601070014030f41c40c03031070500a03442400400c0200301240306594100394044800b0600da030301c2c900240e868400d034401c050715947d250200f00240c004c04407404030b0b0342440f40d00244240e407a4100186d4980c0512170403018428000c102c800d0300715009110030b584418008040c1c51540c50b044c0c9031200c194000101c5040c11070350554080c0301344025107481540c8400d08800510184040d0501c0d0780d01e80c010045662035820b01d0360f2140c40d14800031b00903120000d003070b4440155084e1f59442c4450800c03081d480b81c42d00900500010400500c915002c03102900c51aa0040030300362241e00d03130004101040207202003155610041c010040c1d40d0807004000521400c4040f99040e010107185140051325039010210440c50180200440e076006034954044a415041c02c1410000c1e40d03072040d42070324140b804030b24075900c0c14140c0740402c010007680f07025614582d1007000d0700740d07529018601200c3e9000c16 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 641238300 1250 641237050 641237071
    0x5030d18150e100902030a0b0129130603020d1413030801080a050d08100302060a0f08130201020c2e051909030b0408090d052d011e02130807080c010f0206 68
    0x4203215035603160b4104d0f6100074406401c44003c02d0442d101c0f0080340c40c081c0c100303e100032000c803481082a007240303034070f11282401c0c0140b05180040080b03003041420f00b14407440080c1500413400f00604030403640b03d10b801c800f07122854281458011401640d031071800d00210085034280d400441c4c1000300040308070308103a008000b4008078140c0082a14601001001d04259000900011006860300809032010072002c3e02d8524040420328006440740000411900880328840603020140c2c0e800100350540010030b64221643c488255071200308000100d1200307082c81c0001c10340c410600d911000410b8400c903407080c400842e182d5510102c44058040c030015040d65034840120380403030b010400800d0044402001101400120b544c4e8508104054440e0400003000141c01440b80b0101911600f201070020001c10004040d101c14580740d919044038640320b160b01240a019040c0e40800090103800a007007210f07201a80ca0980300d950302e06e0f696559000402c1e010307a003140755000045a6014568408 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 641239550 1250 641238300 641238313
    0x910021f05010b0f1b0102121014030a121b050a1a0405430303020616120b01020304030b01320d030f09090e0a050607050909011205030d18150e 63
    0x6000300c101e81c11007844140721005407030010f0b1741624248000d00510a00c17a40286142c07606502560030f0f002035500c01078015858059a0500c3d540101c0c07182d4a05d98071091094089252500889280b105a1a09107140d00301c004048240500090b6001c1c08074426801d681c0301070040c0b284a008424140c2c3d00900c10760080018540500c0c0d03d1038550141140126100101c0c058000e01c055944040c0c40490084007c00d1002d205150b81030000990052110030910a01d61240f1802000446240c0d104c0b4482c030740d074011995640c0e2007402150011038214540403125610340041180d5101c1d030310340e09290110300c080d01540008005e10340e01035040c0010550780c030304003094809854810a001c0e68808100e0b003e1408113401d40d403489250700801e12030000309078000c2c0e01d1400391315086010f080041403001c14407400b182c903034907080300d04e054500480d0031510a8000385041072850003921840d981e040d06150480c0e8040e07400c032800000250103501d841c5c02c0710380d00000035421a6800307a010102500400c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 641240800 1250 641239550 641239567
    0x61204060e0307020d06051315020c010b01030513060504050a0204090b070210060e07260907170f071a0d06140f0a06120b1c0b04020a06081303030905030910021f05010b 74
    0x2603200e66840742502301b5582d001580780d07030380c50002c1c441c40c0c0921200c240e02080055030302c1d0007446815034008081c2010001ca0a028030403481d021303202d04c0010712031a100d400040400c00103206a11030650301800902c0341d20858038041d10340c444100e80c228018411a00d81696071980703402030008981c0e550421f210b075074850328000c403204007400c0302d910b0050b103c441d062980c2e451140480351258000744054422142803050811104900502003407055000502c4449034043c081018002c0380c2d2528111400a40d5182c0304103c1809170b041130345800d6103424000200008803513840c0080041c202d0b01d80c104202000100070545c03607240611000126090b0050340c112005034002003d0000061500c8104003207a1101d00d04000810f4040f680c001c5400140421400d11301b003000e02800c40303800d141001c0d145c0485846170300a04110083c1c10140c031610001c1c14003400307000329005082c0c060b0803203050000040020f0740e40c15150004c14108030700f001e44030601050f1841228161090507415900d0100d98 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 641242050 1250 641240800 641240813
    0xc0f02120a0813050d030b040b010305040c0e0414030a0e120f120901020c0a080d03061a03160309022806050c0a060b2b0203150106210b061204060e0307020d 69
    0x40c42c1054926040e02c6a4004c51002c100c0c030301d01c0b40d83c550340128005003e5424802602c580c903010605150402c002d003c0000c601011200941c4c0381c41c1c4c05c0d890180d80e58200b1100c0b007500000c01030307507070301000070000d8800c0d90014003080000029142640001e03082c00d11151f444484200c40c1459800c09007204029191007001020000c0e0144100c800c103401150000c1c1c413140e4a5481166503620060495164607014040e200042c0700000c0740358420b41042160801501c0024045031401c0d02d5013103100d0711580290b020051164015000d10000304003102007588841c06a0700f49071a2a10180700064140d100d10101c0d10756540c600d01812180100341c0d1501d014140006c0e00310380c4200d1003184181112604400b9002c508000154180d60203c5401498240040d1070b440e415603068400040c4042a00001c1b004207600780b001e40300000e0741d40520007000030f00d01110b00382c2e800100044d07903100340140340c03001030b004500038041089441c01e2401d41681e00d115149009402c0081c007104480480c0a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 641243300 1250 641242050 641242067
    0xb070c020f060408030d0e010c09061206091e0506060a2709050f101505030c070501060b18090108011b11010b19060e0411090409030203090909010c0f02120a 69
    0x20103041c40785164041400a000d80c1c20540000300c3da544003051111030151180624400d1211a2000300003e0604007030052400095010f11300c240031491090101c24890359009400400741d03020200151409840070800c2a8810112000c00a0600e0007040c0d00d482e160044810b01301c510780300d1103038800c150040708048100d5089214040e88911800284003100350040611070644100200b0b41c510300703041021074454264018024403840611007810301500300003283d03044450308590702d84901c0346107010b078050310941e0090200000c0c00b14450805041407055010b650320708a43d0060b40d40e032104a42422a401805851086144a1404180d240c00f84aa400c11a68130000200740441e6180210f030030350480e01500a08500d1086040019551103022404010022242406108211103020286004d0300034070760b01c569a0f61541da42058020001c84d201004040c040a140340707482008140204139080c40e03500480c196403440100c2920101e02e080c41000c00603001410b0200750031003200c1c644c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 641244550 1250 641243300 641243303
    0x106030b01021516090902030403050409020319090305181804060c021608031209060f040303020f04090f0e07470c0d0e040612021203040f0b03041e0b070c 68
    0x1600c845058802e103c02d40040c0301d0000d480030b0071000d010020000b4410680c542c05210310b54814010b12000a13840021201109c85a500141c3c0381d80b10010011000303100304502118417403030850385100301038001015240440c0d260500c4000704a2035800d00c10960802e428011941104000060000302c059100b81d9001750148125107040040740c041c9420781000390000d4296501c0410041c050458903083ca51b07120059401920701030903c40d0400d40600c10140008080c9500420401c2e03c1b00440000da80081800c0c078014030a290035100840014166054007041c07174040c425010645002d0591201c0130380301c00d0450142c0c0c1c101a044000c41d11000d51084003a1300c00443c02c0d40c130182641c0c10140022012100c05085482074180002c1c21202200c85494002d074100f900c108a050460196000071580599a0f440b105100b00c0d07407a0300b18813850300619200c2c1d40110303010410304040c0e00070314070482c03203040b1240514049110400303924100d81d80040801d0f401c540080c400c2b52080750038068030b6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 641245800 1250 641244550 641244553
    0x90607030e0303030901140a0e1b060f0f030a151d06061c290a03150e0d020a05060c030f010902090307090507052505210f07030801090b01080603060106030b0102 71
    0xc28072800003415544151510031041c0c0d1603001c0d100c0c8015030101443e800c1444400100b1805500c001c01035145d00c40e404082910042a9174040380036102c56003160815100514016a55901942905480c0d001a02c01040d0203281c02c4841007508566a04001a00d10740d40c00b903400d4581180c11010310000c001c0c0704035005441405004071131890310300c00048181404d1000708080c11440c0c2e02c40425480780c00d240703940100071030300c0301000d40b00c0b401c1d0340d8144c0b41c1103001c08080600960070300014028003601c010f128441c00000e0310300c079603010600c540000d01c02c1d000e070f40d05500e030b80c04002d809000c1512100301d1100000c4c010011155194018200108040c06641020755918400000c407002155a200402d00c0040d120995508880e00d4452107200b001055071070410030f854180e61041a1400301d000d40c4110b04e0054401c3c0c4440050302c0d100741500b91240d5540701d00b0314000b804070030f00b0711901c6400ba061250303030051580550001c03403090344060010455a0328102d021000b5094140c0d903035065 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 641247050 1250 641245800 641245817
    0x12090c12030e090c0414180105060a09030203060c0909070503010f050d061e05190e030702060304020d081c0b0303090f0405150406030f120809150c120405010f05060402040b09060703 80
    0xc80d01d03483c040da4880c0322005511901c0b20700d0182c6100d0b00d45601c490403407081014001c0841c6071000304045e00e056070019503206440341074202003030b100b2403815000694584a00307010403014100324001400400d0040e981c503002900c0d119020340e03413400203003e074646541c240d050a01890070113600903103507035000d8800800c81d001e4201629a01e90407060380d01061640b0b5408025070051390404450301c2c4608601d0802c00c2040e0f0810040c3c072800345060080c801d40300040400c00790341d41d14a50901c81c03508201c000b640c07992400b015140c0101c3c51864103603c5410b16881d1000c07840d01000f501c0c80385101409001c444844a0104001003030300602c42944d15800700308028040c0c0b2030b44221400345102e0030701c00c0300c0d68240382407031308070340881d120641c003003100701810010355013004602c2190001c03006040003c55115440b2046e20380c091000c00802d0015680200004d200054103d00e421f101180420050b1b9100c81c0300303110a0340318600900702c15000c2008a07043c2410b02c2e0009001203406450001d04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 641248300 1250 641247050 641247077
    0x10f0b031c0f0c080d020a0e1c050a0b060f0a090b0108060405040b04060c05041e031a0c1204020120010b04051501230f07031e1701060e0103090506100612090c1203 72
    0x880e00b00c42403400c0007600c19550300e00c240c1010f46800c940c5209e01e13010244c405e0540d66516541d040c072880000c0c1003040340b101040103501c0e2001034100e841d000800c0f0b502001e807101070440080c111004541d00040190001c034000741010b00c2290b00890300b105024455a85a2301c81d2006080410300840c2000010070001451001004810741050540008010014614148564a00803240c01000121650414440d00c03021003c2240c0c480804480000201c0d6213600050741c02c03410403248290031500f50304195102e004c044d4014040400304031401c1207261540140702001c00c0101100d2800b0905900f03048403022031b46081c0f171803800c8a18407047d151040111031190543c0148000b1400310340d91600803101c41100300c050380d244041030b1802030155001d400f0b01040110044c0f18510038040425503401d8030340d00c83d4000c99801c6800c5400c58880d8103107103170b103030005040e00e1241a0004084460500c03c50400c1c0c082d100849400c4021030b12000d0409200c002040d00400d8220180711240c81d8102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 641249550 1250 641248300 641248327
    0x1c0609020a051e043b03090a060809060a0905030a030f0605120717010504020d02040902030a020405180c010203121b210118020c0a030509040905010f0b031c0f0c08 72
    0x4400c5118801e0601c01d403400308040c031080d174510b800c1c3e003240502c1000310300d880742c118445506021020100d8103104002004502c0b8154840c40303040b160020102d403004100960403900e500d01842a100032102995240041c81c1e0846000200050076900100070000c9014400e4000b0340206d01036480c0007445a40d0340c000100e00651098040205410074103080100d486030408814030022150000c2c0003a1905d5800180380c001402402803140d61f9914880095481c208890b40443d0f5010f80b00704050b04140100d04140c241e2031130704071a54840c0c1405036525510210503202000c0b0100d40b911115110000482009030b0b18160004207240f0600800001c01c440400c1450500c0000304001503950400014810f0031840c0c0e5810024030340100a9810140400280c150b501c64051401c02e0b102c08050707002074090311100801a040390700308110402215801d5100512204048040b81e02901c40c07006030f0880600c08a46d0840424007109040d400c0703034003d40d40c0e501c0d45032003000c0f4075141860890802 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 641250800 1250 641249550 641249569
    0x1406040f090c090509070909020a031d070e0a09030c06020c0f0607090e070509010c140c03071e0e06130c0c0b01060c11010203250c0b031f051c0609020a05 68
    0xc010503241c0750400300d81c0b90016082000f805060781e1140d41703850080000740c1404024441c45da2007940c000362520340f01d8400c0d4009154448010b10803800d4148070360700700b690380074540101c5500360712140c0842c404a80d20721030410503a0b8151111004642c190311120300a40002450f81454000e059103440f0300007052142e02d1082c211625400c107072340d06084040900c09002840036040c404104140f00113603800540c440c0c0b0181d401203201150003545100ca80c18a2291580240c040c8203103000841c2c5c1200007105c8180c4426034603440c000c455900e80c05820700040954010790410b10700304011109040e983c0140320460782030304000050400c0c0ba034440c80805800d80c403442c00a110000f90b00c041041800a08038a98400d2000751300b40300c0c0101e0024402000d62502d150a50754494048003044460500c1600804260000540ba40b406407200400045c0b030785c00100441d466040003283c02c0c07a21340d80c134519600780d58a001100c5c06040d03030758000a10640400340d070b01c01d0815a0028035680d030028907 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 641252050 1250 641250800 641250809
    0xa06020f1e07031a0a0c02030301050f2106010b0c06130c0e070e06030a02070308160e01030e120706050708090a050c0409020d06092a050f0f0a030b0901021b161406040f 74
    0x2044e0a500d010765001e801c0307941441452045400810040085660340420240080c000301d409042d103a608401101420628448034511400341d0000051041c51200c00303001015009403c0d58002e55032580c9034418011400c0d402000c0c204461410310461002d003541c0c5038800c1080c00c3c02e004003248070002540b942c004944019038a500010010201a03103c400355401c03190f049405101c040207000c01811502c22040f01c1070416544645841410070104003507000070b50700d0b400440e662030f100e003013110250108607000f40128810402040d464000081d240e00655000000352803035443d160b04110103440700031410380c0d104d084505a06c01142c030520405200720b1180c0c9469208141004200c407a543e03100c48403c0d203a4840d642d04104640701c5c041344040204040740c3c10514502e801000503e030010680016000000c000300700880782030154000c11904800c03540c01c0d003419034243c010750f580d0380380110f070019140078900d410400000803054080701003000070042d41c18030b525403034214102d18080c2e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 641253300 1250 641252050 641252093
    0xb0a12020309280f02060f0405191406040f0303050f07080a020105010f0b12010312140c0a032c01030b0a050301090525050d030f051201140a06020f1e0703 68
    0x1a40300310101000b0601c0f0842600d000207040d841030341c0c907040d103010b5045402a00810000074046480d25810084401400b8018442d018009001c62110030015490060b14440e0503020110111032074043d084d101114610342c02c0c4902c507801c1d40d80480f11038002c1200143d03a440140510300000f90404041c3c411200079a00004540d0314245101600480c80d03400002605001c11032145004803441c007003815079400240d1b203081414a000d003251001c82c142244501241c01203010909540007180281c0040d001c0d5685500b0000c400321040c1c05101c0c4c820300101d150580700c014103c954020b40002c1070640b4010841d0703484e16982d202023800c0d941803010440719a0000070603a800c90411700040c00fa144001080b902c0c4107402c14001c0384007001d980704080c051007000c85440a0040c131550482e00000d100c02007207001542e4841c0b4614030180c101424603c2084e1001000c10414400030341038000f001900010311403c4d0854862081c0c1e00c0480c0301c03007101406010300c00320102c2c0d60a442070013084400300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 641254550 1250 641253300 641253313
    0x1c020307050705011107062a0c150815010305040f050d0509090a02090d0f08070c030b190504240905010e0c0307060212091302070218090d020f03040b0a12020309 71
    0xa0310740d0901c4101c0e00500d05100c011007482c170440300e00240c0310054421608107492410b2103400312440201c40c05242038900952448600200881000680c1c1201c6010445003010300481d44107a81c00c42c0d04499000c103540c00290f00d4105503109030012500680a41d299074000802a00c1f802d06104001c0d44c0e1502154001400f24264101134400d29400354080404500300744003600000c0c000741c410308002d0300f15030040d110311051012a4007200d20f41c0b40d01003402c00f5040e40d03d2600d11090502200d0100c04590441c103120403100007406000c1c82107030f200350030049101440f5082100407008202070340100381d0303400110000900034400c115070142c0719401488020401e10030540341840c0e07500410115004a200720509484240aa4400390b03002c507000c290524085a9080081c087ca0101940c40700b285001408a003034484074540c040d450740300c240c40003132055000a0b030791034840c8004591150b104000070070413500d40034081c01a42e6070780d00e032480b1806808440582680c0040d07903411800d41101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 641255800 1250 641254550 641254553
    0x801202803230106020f060402061b251a03040c030210141206030601050d0309051e0402070615080a0b040204050603210a0201050106090e1303050c07090b0906220902031c020307 78
    0x400c8140004171246e80240715901e800e5012421030300890803403100407540402d20b000c181c4410f2000b00d98007503102c0c035041251442d80d2000301281380d141c0300d6802c41d240b50302d0100361a1107140003264401d82e08003890100f02861642840440c6010304105d80821a44000d41107403041c131103009140012100d4204042402c226081508205041c4d100d188502c8001c0c1025000075040403901080317a9007210540c14800410032000c107110750081145511502c009981c10801c4225400900203020030f2400980458981901075554003000402403d0040c10000050040c509600031590001c4050180d484054004401d20b0401c0d010b20480401c070040032a0080d0065030901c04c1a00400440c030781040020f103000d0490380c12102c080c040c01420a02c881000090601600464044819880448545a079030f000c2d078400404007806005d00c41e07080d540c08500c581c500442e00c060980e020442c04500e1240740182200100140f03c400ca030980240c83d040006c0520b05400140b00100e290050750765210103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 641257050 1250 641255800 641255803
    0x806031c051308280309060f02120a1107050303160602160503040e151014090409050d181a09190801110306010e01090b0d020f13080120280323010602 66
    0x304c58001c583e49400940500100364131460351030890ba07150400c1d014084005400301e0900c41f40300c0c05a18075250008040000940c400c1c4258001c1d00d20303005840807a51984201a100d10805418490700022040148046003c0364010000c41c55441c0c050300c002e40d4a5505c850540d00140e1020100d00f000c1e1040000b50b02c3c20554442803104111001d00072200c0d400d00c0600101305a02d450200400042103441e180e4546600554900340c11000300c800c988511040140802c0c8080031400d6092403ea20009070302841e2198807820b100c40440b00d50400a0f52018003804141080051085460b0b000000651407400c0c800c440c400c0a02c415059079900d80840094502c0050299850401c007000d2001c0040c0c408140546003456034650000d6920402645051030b54003404d0030395858481820000100040158000403540300e981000d542982d0220140c1c008600411040e03002444005c1c08015403803024017900701030340099040008540071480c155a100c0e28041d20f21001103020503005201440c4c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 641258300 1250 641257050 641257093
    0x8150a090603062408030313061508010c09240f021501080303180a0c06141e07021819020a031404060f0e01020c0a14150f160806031c051308 62
    0x13a070300700c1d0381514940460302d40e4904c03000f00782900003800059050708100317035500030784081c13285031042e5680b60761664846070080c50b003401e00c00c1c00318100c0000059210201c009601c400400c881c121810004001300580360942c030080e5000460044041c4a90407a41c90082c3c0c6001c2c0c100c4400950326840cbc0001c26481c100345101429010303070f1180040d400000c0d800c40085043d20313030b5450a079102401d0352080a010b13003c0c034907002d00d1020381e0300024001480008040c1144074000c45a40b03001c024440a40c20b03180070151076000c504003500410b4039030010301e6001090b40c802d075842c0c005504409198642078120003a00c0c1192a0b9445a0034a141160b89000c2c01c03030f400c0c0322200214138020074450707100da4036030b8031510080403d012640380d448601c10521100149809130f43c00201c2c41c0c44d00041035001d858044540340305480e039100b03000d003405220ba400588a81c001a00406858002c202c0c00d04c0081c030303251410810440300300040903070b4440c1c41468100070f00d000d5000704038221051204601105 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 641259550 1250 641258300 641258351
    0x8060406200405030a0323040303110d0804021008040f081209010f02040b1c0b0301050f100807060f03090521120606120f040f020303160209130308150a09060306 71
    0xd5050000b44240d03030f404241c54411640c1800c000c00410415a0103903c0381281607d052920b900c086000418950051414a80b010b624415203030050300c803c200f616403503030a603400703500f05600180c451805800740411a400900440310754840035240c2d40c4020035940483c24000000c100101030180c0c41c0000d001d04413000c070314400198103041c24150001001e00540280c0390101240c81066030f896155640444039a0a014009020764070b0202c400400d00030301940d061181d03c0c91070000213002800400c80d0419641203a580c25024000030000310060105000141c800e4000c1c68900119401c002000c1c501030340310f20907040c5e00d420940d0035507059004003d256131b000d01c80401a00b0600449288030941c0010700904108551f02c44e42070030002c0c000318480007505072000003080a48030700f00010340030550344203c3d01d60049584505503418000e1407800010040340003900403452056a0404450818201070180c01980c0d81d180d8518090350100e40c404c1d1803c1d940c4110500000400c4502c00b003281 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 641260800 1250 641259550 641259611
    0x409150b04051b0f07030c0b0a14090f0309040207080c190c09021306050a17070e27070c08040e0f012111100c02150a0206060d031d1302030412080108010b030304090b0a08060406 78
    0x8cc85080000381d281d11031b040703100d84a1540040c445040262060a0f02c103410100001c450741b1807900c5095a00d000ca0b105425941d1a54000b070020380700510340222084500c000c413020380c8880c900302094540381c1003079202500b440b18080b003900c0e01910b0900842d208501954508100c003d80d642071101d0600c40c200c40c00740b0424860025003081030f1002200d42c101d01d2619010007450100d0804003410b0050740c10480200c0c11080a00120401c44100141680c0c16010840400310035204e0880034158030010007840f0344070340b105c114207519100c040001c0100041c1410401c1e88070f19400508030300d000300c8110402110110341610460390400a8035402042034501d003016070101d8802521022a83c80d41100300c0741562103025841c0c80d1400d041040d000d82d01d10654407800c00b0314189a0040036000d010f00010242400004c03907a0050080210020010380998a01800c240c0b060700038003c01e0000d6900000410000104032404100c054465405103070001a004100d0000c07401c00a82c25101900c0e1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 641262050 1250 641260800 641260813
    0x90907060e2e0c031e020c121c030207030f0318060e030d0e15070201060e0c1c020a020c010f230c0705061b01050610090608060409150b04051b0f07030c0b0a1409 71
    0xc3e50005200c3d03400707180423586141f011600101e21440c0c99003502c40429110011690b50a8a54064020b03025091103501c0718001c07000c580008070f04072143c0c8150207102070090b00e0000d010985682c81850b0b0b44005400b0fa9140500c01d42c3c840c401c0d40c8500040420750340c4245071225204121214558204c2901d00c0240625858106070310b40e5400050418800305034000384000c1c0000d1440d40103542074003407510940d11707540c204001039111111b140c42940850101c0b403e0b10302c01d52003052204444045460002290380003a078403104d45030883d0508080e1489400c901041981e211030260510311801e0b507407a0803c991080281c1c1c00d560014103103501500b18000a054034076080f82204054902030300c0e06a01c26950400050068044d0120250042c3d81d0142544915200740e084280b00840603141030041d51554090314003000e050050070b62070a90140007c087e080044c00c001c140540c000d10f4400000107080e11208080710040d203a80b8080b50399504c024100400c1850110390022100c0090681c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 641263300 1250 641262050 641262107
    0x150c0b150603061e0406060f0f03051902070c0305031201050a0b07230a0b0705190503060a0605070201091805150d051b13050405010209090907060e2e0c03 68
    0x2850b010142c98144210b08803106603103000c1d80c00040020f8440300810520046a030740d00302038032120122000300700142134203170030142e110b009004043c01441c0c0410440d40181000700e4080080d00000c1003103a034101d5548000000c904100040c1020140780040e90345917501d004100030038071203070f5441044c5411041c402040401c50000c81c0c055041d02254a00380f6082031084270a080c4000b4110040c6440c411600b0300120507405009030550341c1c004825901c15208141045e100741c08103c078282d40c0411241c0084c820b45218401a00e80c2c1c40c03040c1401c10810ba1102c80702c554107220b118108094030360320030030007099141c0d0b600d4031203242806031440400c2d0700321501d0340b580b0f4801110440c0001c501c070100da00b049031100d61003220401840d510030003260802c0d18200d4042d40c00002a18403600c0800007140c1c401d400420002d040351829155000039203441018041c000c040480c0745600d00714640e41d201c1c8011141c404c0e0b40c40b00022a66100750f200428540908111ba0012542c1401840c2643c1d080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 641264550 1250 641263300 641263309
    0xa1106150108060a050402120405010c0e0609040c03290a270510080a030801050f091311030c13020a0f030b0d030c11060c0a03120912030e07150c0b15 66
    0x40c0e0105003868260315958400340030481d80391555020a130820310001d0305081042c10907860383e0050342701d60001e2010010f002d60031180000b0543e05941e00010400007002c252509034400b203025140c9007000720380010300380910302c107140d40246541c40700042c6440400984c680316a01102030b000d42c0110340444100c40b5480c0107030760700f00fa01c0c210703429a4a0004c40c986c2039039000c04500520840085444148051400920317451081c825140145210104462645025030041d8816604080a01d4100b03d00c2c0e01c071004080c1d280c1c4640d5070180611008141141c403500040950b41c1d10806000d42e407000842001001c680e06103d002081629200f001e04c00d03a601c0308000e541c1160149407240c0c112003c1c0c10440340410641410660007440024922030103070020401042c00c600a4036030108207400c1140e00416201c00c80402050106800c694508040c02503125010088040044038443c948a14424000d04a00e00310301001c076142458100820050781c1ca203c0e880320b15004c03600b030845040c8000c035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 641265800 1250 641264550 641264581
    0x9060b030c07060f1505041805060c0703170a050114010306151107090905070302120f150c0c07091d01091502030403050c06043c0b1308030c0a1106 65
    0x4515040700040c000052040d650000300035050340d001c04000305281c2004869900030b041c441c1d0350003207007400c0d040580c1105201d40c0c02d000c240c004001d0586540c0f409245c0981d0761065008038107020f00c2030310240544c04554000d510540040e04000707029410f00e010400740944000400d410141008410b02015284d00b0780030101400c20b040412840788004051424015150803a10003d45440c00000501a00003195421a40203540c121120400f0b600c0e5551a24003802780a44940d101c2425003203003008083c0354650020702c2880036424800345010250a0940342e9000c468655183c584600d14004d01e0201c0c900e10980100007005044400d6031803814600303c03182d140b403c2c158040300040526018008491940c18081c082e60624a01450600000081c1c071032a00c6068100391300d0f0021250703135840422044a11015021600041c9595001d590840200455044016083d00c5400904507201440c0240c1d8524003240c0c0303c03d040308c001407000d0103280007820309071711082c1400300c0441141c501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 641267050 1250 641265800 641265811
    0xe0108090d03153f32030f042903130c05040513031d0d12020a020a06030903080f0f0f0c091003060509092428140c0a020d0503091c02100609060b03 65
    0x4205ca1202451038204201000e41e400c4244d8000041e0662400340c8440040c03041d6601d510714a180c81400c2210b5000582c00c0902d8104069010000300e01011501d203410740074688503110075407032503898401241c2550002d4842010603042454840109500800d0582e8400441111840a4039400c4001491140800005880c4115983e800c500e914800c1c01020803498000c1e00180406a80310300c001c005007160401940054240000709102c6159500074500540850300282102e44429030fa4100850001d049034280d003d04001c2829941c0300c1c003001401c40200ba450014003039141c00203000141c84020203d089a401c00d0702c282011006c00c504004500c02c098401d468182d541000c00c0d070303296085401343c00b064070980c03030101c1d01000160031a58200190600056640e1105009844507015880702c0c500540c101500090b46944140e026640c044250340855003000ca46090302400204956807101c010382290001c80c0c20080c4c0d50154000034502a101080103900d400f051600c10b0202419 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 641268300 1250 641267050 641267093
    0xc01030506190305060912040f1806050a09150b0a08160908060f06040c14030a021809130317040b0c07020102031c06060e0108090d03153f 61
    0xc11038580741c0468034094030741c541e00501c403025101c1c100346642e060106c991000a100344040b0f420845403c4042c1c80844003001c0d0510b1410303051203440b410400701040c8540583d035070748200040c250380c1c1280a800414040c0400522131911318100b00b0908034580044403944810007131844820391203031103103510002d030b1b8507400c0301e0a004070000c4500074140e611044c41c0d0f100300300c2404160f95064085034082d000c02c9034100b205504038502620000010070f00b900d10b05805000040c1c44500c50340090030404001081148420407410000740c6140080d034500c445608401803103420550000311011010505a150300038520340f0365950407210b400117001b207910305000304120382164001c00035606003d00710703500c0b44200d4074220740343c900426031841a0800200102c02000c02c9500828216000b005141c024250000c171848080d4060500c2c0700b0702d0805440074120002d42603814a00704940190350101d0741e00b2403440400048110a0034100c0701d0700b240008080f030710020315810010104074a1149 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 641269550 1250 641268300 641268311
    0xd0b0604200307050310411c05070e150609060c0109060509060c0703140306030304170d180608040209060a080a0302070312110d1d210d08090c0103 65
    0x41c18003100400152403400d00ca002006000c00f1641003005103104800500c0d0000e40c40d541c0b100c0307950040207856044040034901032005809001c09500e454003c500f5544a500c41c4000700c0d0200306034a66a001d00140302d00340da00b0143c10050b0600c0890010a44050a0385a6040000d02000c040c140307101e00b1442986c0000b20b8003800e803107500903a124221f04d10001c0200b40d50508212016210403034103001c15001d050b0000d2500080601034600f00381d0140d41c0c848096070400c140b44915400600401e50600c000c0c00002201c0302801c00300929000b504014221120390315901410040d050785051403c002c0c3c5410a001d0203078442059a400780c0c048a1680701034850602141d50920340760403040c081e00554024000b45900052000222840390301011400a55110111912922a032680c5940d4002079980003056202d9800b103240000c144c09030851007482440000c2a120340c8260402d1080034800640602c0781080c0800480050f00e410030780894030300001e405444294540d1082d05059031103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 641270800 1250 641269550 641269571
    0xf03241b0c0213060b0304050c0306130605040f0605070f1107030206030604022107031a04020301050d03080403110615040c0e1302070503070506010b0715200307020c0a06090906050d0b0604 83
    0x50b0020f003203883c004100701c036110354030021581e00803602591944a2800a4070540c200011600d2007810b0464550300c0507801a41c0c0d4002510000c1c1081e00c00c01007410031900410128800c0c070340100b982e9120f10180000d07810024003c20a804105055900620390030000b507210402107a0340828100d0740141e9840c1d80380c20b0194800e948402b541080a140c80c100400103030140d0208245030046280401049040d000f040180d110901409400000c000c04e0000040e0282039682e400503c40e00700204100d0f80c055000c0d10b400b0045076807401c41050090030300c13460f0400d44905c100d2070509142500c003202c2c00c0b00100c1c60b090031241c5000c03200740e80010300800703100c0d0070320036541c041d640103040d41e070596500c03d045262a04601e1082c0c41d400b02e44440414010300d98030802c2c0013204800700c0d2480c9031801080118485d0001403c0d0340c203500410f4403032521940ea16460401038107181d1560310b069800c000c001001c5580702d8111074000d81e648018035022408031a50268041d204035004542d65460 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 641272050 1250 641270800 641270809
    0x12171018020c0109050709050108250302010305180105040b060a0b0307091e0308031317160f020f09070c1401110d02070c08030304030e18160e0a0f03241b0c02 70
    0x12403130054020b001d00000444c581100390041c5040794107410489042d42a42441c1e0b2110542511140da44001c1d040401c00055000b900203551100f4481c05600c04241242c0c0d605081d070700203c40031140c01c0014004c0105c140b90040e00326000e0a1409035444c01c518144001034981186806000d40f44542070440400840e00a03042e20f0140d41c0c001c131a0342d1a8100489204101c101e51541290761400350055900045540c03400d4030394044200c040500c080c0c0031a03c070300032103d401d04d1090740c00198440c4c0d00a01911078079000d50003843c00b980c8102c03070000f060602c03409031180750120443c0c0d6410917002c07000c1d0358030070f0094604440940750011703035801c0c5514243d45003149030350080c40f4900011040005241e0402c100074490300060f2095003030700f0359201e01c24005c0302044501d0084843c4a04d20351689510858902e03128401c0640030411a07034803a2420400241c044e8011290300200f5900d00e0100a46000105003207081010203010040204810641c41d52903142010100000c2100310803d5559 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 641273300 1250 641272050 641272061
    0x40809010e0a0b04090b04050105100212030601050d02041211060a090317070611030405070605040e0411030f0601080c1201050603060402121504140105151e0d12171018020c01 77
    0x10301c440d020355455640b5104805442d06c9988103101b00d00d000c0002030309042084a2051140c403950107008060540c030008162608007a1595041005c00d0100c6c0c0c2c8500600c0c401880600154070038800b4100451602075014042c6020300ca0242e40140b04403000f482d0059100402e60b540001203010350500f50b103c0740c81d507009410025140310700b040d00740144000024011401a0b0040055a0b041600c0340400e8030280b16a10405481117070304000500851102e55081c048000d0081c00e82d0440a9140407080c81c0907020703048801550000d4100226038503140740d1511580b0380ca44000c1c46140740c60000261103100081020780103054200e0b6030043e00d4410b101c0000e4100703080010b0062420075081c044a9040020389100300344d8a040d003c07c0c410030511a40f11036100005162020104c1c0403c29002c1100403107400c10b8201e103510b27000720005142c121140007480401d641e003103070800150742e40c03e20b541030240c012002000c0710341040c8480700080080020702000c081c0c0250f07481c070396020410300412 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 641274550 1250 641273300 641273309
    0x180e0111040f030c0b030c03061215010803180904050316020d05240a02030f01090c0903021e0301050106090b0706150e0a05090106060e010522030f08070204060608040809010e0a 78
    0x600026010030301108042582003a44c1c040c06041c140503480d0003000e811440250340d90b4890f0002440000c01524290b909800000c05100a50309010113125101054440c03c0c0c0008149800200c1c6220101101d0503000205c400110390482490034035840f1a9141c2c41990702c1c414040009035240e00a41d266007604505259108d4100d0f1a459025103154082030010032820400c6410385022904100550007981e02424031212190980d074a009010700042030303c104070b00140015600008051780c0c0706910713104081003040c4204c0c0714000304403c040c21944143c22201c1808040081480b0140c3c3c2001614940e50b0300080004810101006010001f6402d40c040031100811a08012400d829500710750700600c1e0100007801603a4450400342c0d40c0c90850141240001da09110300c010038031260302e000148891920072081203984940b144046014100d4081c0d6011a00155200442c1440d11540b002080280707400c00ca141803a0361440d9080c89510441c1d4100708200d11006010360380d404a010040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 641275800 1250 641274550 641274581
    0xd0e090703060b0a09180b011704020a15020a020406050a0b0a110118050f06150d030c1403040308120c0702010c062310030201090f05091602012c01050709180e01 71
    0x81d2118034000307080380d1141c0160545801605002c034200b103558015004141f405865103610f4000c5164612244c500081050f40e04c031000d84000502409a030141d103c41034296409045115220700510081d9030160b8803150140c160f648007005048009802c1c0c680c400481d191101c240b80031076008502611189020654082d42e000c0d00604104000030200642511002a40d08030742d01c500f075000380846034010319030f00007807246408000a0b02ca096003000c2c09100e40c1940345521850090305d80355030000e800c01c03a031546c40003e07004175022242e00c116500c1034030741310094904001036000900410b0440c0d0000c01075510362900031802003402e100300b40c28407040d4030464010724003000c004042c26014030090f0701240c503040740403598175280307140302058800150240d156512029181c0009031030a103410011550b980c0b483c04003002d0303d0341711144031503d4a1000c11101e02c600e05010b0866401400c050180a01100c081001450740985298030709407d4200080da011040c4d01c680c0906403507401040d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 641277050 1250 641275800 641275807
    0x24050a03060e010e15030106080c01260103030f02061f0b0f070605240603010b070b070c05030d0c121a0105030603161d06030f0a020d020d0f0c05120d0e090703060b 72
    0x1800e15031942071185c01c0c0310302d0200d140c1c980d420905080707451501a04d1800d420205421800794080c48100850a5003018003441a4084114200020000707820460005142020a0703c0e01c2d94100082030b04070082429206851500317103210501c00c8c146106000c03060001003034100c6100036a0080e11403494008001344250310f805800c0c0134440221001c01d00300410386944d110054201201601e050726030840c1003c2c941074460b11000b5529000411100030040d039048070000290051025002042c4101404250744583c0f501c0a040d103803040081d030003400e150801c1c02c2a946480108540b00304000c4c00d21a40e030740c986001207403e0002219500900e45004200040c48540d40680e0155641c0554802c00c1d40d42c94410403d5120301e051403000304190b000100e0b80b805846d21016030031020348002c10380c1100c0015175807000004640224107544d01c1040c1c030300808c2142403c24003d4886074002025082e1a07402102c007505150382402e03410b009a0f4540005180c2600a078020350150450800342c648 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 641278300 1250 641277050 641277059
    0x90a02070b2809081b030c0f0309010e0d020d020d030201060503030a020a1b0b1c1b0c02120606101407141606031104060503070e0910030c24050a03060e01 68
    0x41c4110380540c1124100000c840102c0e564100d4812186001da01c800c2c0715141403080c070721141d81e561200d0301d21003050208114800c080a0104096401d0040c00c1c809107442e034006400240c882da204000c06801012440c0c269070041c1d450389540c4a4840d81202c43d802d07183d0403070404900500b1180c10250f05440001003210119800045030072640c2e12480410241c035040410740d240da828240300f2000001390902c00c0d41161528849402440b140908002a00780496010540c90b004055605004640e40310138002c150709066108500b04580702c0f004201505260020440c1c815a01c07080c0c10403c5404800c801e11000b020007158a80c54000746c004ca404d20110f4895501c0b100c011020590b480084640020080c1c080d0050400d058400e0401c80e060600d0840141c0384d0380d000030042001c0020000c4040050780d01c2c0785605005072290440c800d8594210300c0d1030700030066aa0070007040302d030034a80d06007241400e0303503c1c4005178070746071900e03a44402c0c0d410410307400341040b9089080b2040c000c00c008107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 641279550 1250 641278300 641278321
    0x1d12030403050f0c0604060f0216090b1804110d02010903020312120f070504030803041112060109060602030c0705012703050c01030f02070c05101b050f0c03061005090a02070b 77
    0x2041c0d0740a6401d56510300c61921002c0d58440c2030180c0075800c40b030300380710401c0464000c000f05041d21001e03005498840d000310703200d546190b0054002c04bc0090f51111440454100400b00e10326080307041d402054141407540341d42d0700300c0c0003011070b00e842509501205c1c411a44101d0401004607400f40440e164450481c9540301c440e0894513041d10042155400a04042400030100d03001d2052078850a140030304545407003000d03078402001913651040300080060540c880d4622a986580400040c00d40341d410a0480000e0f108994003060856100f80b1a1640b880c1000c507039402211000d08001c441e03019420b103164074002540410302c41c400c000500000910002098400c14250242c0c0d0400000b0040c0036500101d00407001c0142540391501c10600007402c12030300000200b0b180341041140320344d00d00410317200b5550003c1c0c21100354002e5400313011907880c1040304042410045000e042c0c03524000c1841d0007441c8083c030500d880f480000c3e0210354409e40b55411100d0554009518241510f820490078 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 641280800 1250 641279550 641279557
    0x409050702010b0108040c3609030201060801200306040b03030a030c1707020a0b071b051f02030105090c030402012606030706050315040b060c010c21110a1d1203 71
    0x903000d075080603107119a030b610410315a84502e5009255045150030600c480110520400c0d1121205034051219135600c1c4103040c484c460310190040110b5803810a190007429907038150310545290381000e600c105104090f440700728050b000d4101e00c54492b0b803007030f000034040c06c1b603180b050b901070100144c04543c0c0d035030540012601603190b8545005031900c0c40c1c1003120b12001141c0c400f0050f00010103840c00600881d405070b0b002103107442c02c18240c6d00440a82c0b8140c2488000071103080d030008010100d00c6600160103058880c03610310460566160401041e51103400619031005224004005011a802138400440004004451a520301c0c1101c0004034000c0083c0c1d0712a03c039110b10400002c40c503225400b200d00c00c070f1888684850300007148080c88081e2901c00c201c6a400301e003d0040c0380d1401400d00c00e0700d0001503640d6421990020791021007000e85414130400440904140c10400d2045603602241e02c60742c454500a2900643c20720600068082c100d00690700c981c56400280d07104d00d0008c00b8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 641282050 1250 641280800 641280811
    0x627090b0f04110d030f0503070201110a2007080c1309081305120d1b080403080a0f081806060f010509040903020f010e0102031e1305010203070c120e032808040905 72
    0xc9030251181078100300e004d441d0014003d0000740e2410f480000b9600c141c0c05141c00c402d00780004a41c80106d050740703600315004014404001800000a1640f9280c2c40e20340c41c080d503084070050f0910a0814400d16103804c0303040011405040302142e44404603486a2181c40c5090300441d901d41c94403034401c14072958514502c207652052004450300359411401050380c810482c510348850740c0f500002006040d221020040550b0f0340c800912000010601d00070051110408039501d180f214a0381c0c500142c48103d020b4941204000c3c1e002546601400c00140c1541040301110900c0b08040c520004903068460312101641203070503e140203040507000101c0007149a000380007405041826a0464200c1c00b0403075080c840c6281440d040004401280d8900307400800e401303103c0000c034004d92982800d90b0300540743c0303c00207008120030005214401d040300b14100d0303c034a4109112100000003940e9501d001c00109a0101c09202d03245060003511940500d0a901076250754580d07581e5070b03082d0001c0608840 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 641283300 1250 641282050 641282063
    0x2120712050a12050a21021c0b040c1e030b0a170105010602070501141209030c0a031e0801061707110106030813140303030c030402131107030f030627090b0f04 70
    0x41e0f0b41525000314269000341c22280d40b06081c002d0b840c4214101d9502442c0384c8003405e603080000420710246030980101c900e1210601017031441d0381c1c1042c003080700c4070301c01c42600b0015008090a801e0b000c004026841c03144526011900204002c00614000b0081d0700408914002080c8101d4409040d04010f04940458099441c2e2650b500019a155104803c18441d1194100721a4402d5622018103981110040085a0500d9001c01440c0c0c40c01000315810f40120f100c52008070f00d2000c3d0341d1114100c0c4445c52030700303945039494080007501c1149501c43c1c96040c42c0c416000a040941305454201340c11404100910201d0350f0b90a02031a19403101d51615800410b002003c507000034000c00c0700700c2c0c034500600218607660350038070307507076070740d40001c1d0041b40c0c095145208944003502c0d900401404101c480d090035603410345864040d00307554296521005150401208006005208182c1c0c030240180900050001c40020f5080d001404a110300800100c248814070010344e00e420b500500c035a00c62503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 641284550 1250 641283300 641283323
    0x702011815060f083328090b0a05041a010618050303130b03100816140915100201020f0a09030233300a06050d080702120712050a 57
    0x503e007403001c219400781110303c0c2d000b03d0240485198025003140307010360b240710400341e102055101c2d0100701010b540140d040e94660341c039582c0081507000d41c0c2140c50001ca20400c01800f15540c1c001c0f1851006200840b6156030f440080c060040c1900c5000c101c2040140441e0b4541e155480a040000e6003020808811442030000c102414000121006d003200040c2100d4110b2412050001660000700044006184071a000a90000070014410020101c042c01907805040c1564020600c516010092107080e06d40d0a01000500c00403600391110016a44110102c02e1480300b80d0183c07141c500814100e21000540b202800e501054042c26244200d401110880580e550405503c0041d0803004d2803c00f008451451600300400074a06006800a5003422071aa881c070f600d520400725481c0a04c41c10b4a00400481800314400c803405040c08442074002500e00d5110701902d0300074450024000c500d4880084079031703082003200c0402002000fa8145400b0000d00d055901c880198600311140340000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 641285800 1250 641284550 641284559
    0x120c03060406151706041209030501020a0201020a030b310908041e080615010e011b05010b0f0a080714030a2114030702060712110d1409060108030a08070201181506 72
    0xd2042c642144c10303001c02003625840341e4650118003000208200c05003c04d40100000240c020300160070185029000107840e8400c041000d03003175814084d80c10340b29400b03000821b103201c120b1303203449a001080028080c0300340e07031407402100081c04d54100240c1014800710300021500554020540030340c6590030f481220543e13810105544043c25100b100a00d8140200725601d035105940a00103280140f60902e42e000c1c1501004001414401c025130b00c6035141d440081030740c288200c214003808026201904139900d440149902d0348003d0107141602480e60a0b148d004c0d0340c3c1000726030301d02e980104410081a00c078010140b81080341c0e50070b43c408a00490f80580010504800356449001c4075005480140c1c3c80000446170a046400c0203441c099036141101402c0d68904058a01c0d60b0000c50002258010805180c0e012140146120070300d07804000188074403c0040141c0310074001c03d003404003080c1c5592005901502034841004e14a03540c0c6404007060280c2c1d84005c0f10322081c010360030041a42ca8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 641287050 1250 641285800 641285819
    0x21100e06070c030224070e1005040513020d06060c06150e0402010e010306031416080c061608091005092d0d1e06140c070f02120c0306040615 62
    0x108414028180c004a000580203400340c01090501d40c8031348142d601040101d01d210608070b03844155884c0800001d4104108260400107255480c18101d40d541c480d070b40c5d084402010761040d400740600580103080e401c0c0d1402e00607010395120302c032031080a001c0c058640c1c0009091035420041541c0c000c0c18200044403900d195503240041e00d1227800c0d601a03c0c1d0303540c3c00540b01400c0517030b00300341010b60b6074000001040c0c050055102c0c2e91030304005440900841e0700b007100400181d0300302100581142d88190300d035541c0d150803a002d02500c603914000340707005410600460b000d81549660071080c201a01000168070a0007002000340c00c803100c0c4a070442031540480c20010400e4041242e0311400f02c841440e00d4420300004c56503100e007810071685001280d141002d0840300784203c507165120071182015107020003440d54464800814182804203c2d21542003040c041040640204008102815600024000307030b01080310240490700c0505061902200800f03108004540100b4a00004184000f1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 641288300 1250 641287050 641287061
    0x2010f031503020405130501050108070512060c180d1514090d0815060c01090c0e161b1a10090b0d031409121509060a0207031d0105092110 61
    0x3645824901c0140c1183d090000400c00540005204c516040b060300c001002401154040c1c21021b01600c0030b0382ca0402400103040c02030306c0c0644280c03c25800c0160020340041034900c2c07110b203130001c0c110300c141c0c400106480b4100c0801c007800b603481d060340c0102d42c42a5500040001d903160500082c02c0c0e5541012162201c0303500314075100040504001c90b55080410303141201034100140003a10b4920703c20308240c2107400d00d85080301c01d409212010012080e0164800e980032a0610b00c42c400300501400050000021001340c0c01c00700d00e00d80c40641406003090420405a50320300c00c0c0c54035400c4c08010440030215a1054454090500b20301c0c550f10300f84149680174860f4940c54001041102d2101c1c80400d420161545030080344281d1101c010303030b0713007004080303905409a2074807a06030410040040c1440801005211250f004100c07110001e6480300c94904180c8a02da20140f0700e0038000700484c1c1c1403181a05103a0301800109181410070805180e81d214150f440007220307800300c10745119106451 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 641289550 1250 641288300 641288321
    0x207090e06040f03030f0903030e0c0105121308040b0c0105090705151b030702100c03030e06011206090c0503070b1b0606061903020d020a051b0705060423040f02030402010f03 77
    0x811800100c1c00052442c2200010300c4d219040225290200119080c00c407422410254000780e120a030103d2140000d1004030450042072a0040c98076200141c220100140600b0a60318030511640000502c400c42056502902055003030a94400c580d48049028000c140c032006410b0090900005851030003401803c480340c810600c0904000c2c1603405247d5031034134040d015109000422000c0010395076280386d4000244c968980814500c00c0d424001e00b04c5a202550300d00301d038008001032240203401900d501c0d0031a849800450520f40600e80f08a83d14221341c49a1f07054465404042500303038555010740500c00241e02810344581c0811502c0d42d41c0c01060750348be17801c0301c1c3c100300c48000762520000c0c450100c2a5400c016103488085580c030350880c0e010100f000300040c40800c071000300703024484c984024056540c0c01000802e082034009100c82c42203224900480010a100e0039040728815810080030034010420480324120175001c401030350044030200c0c0090701186d01e2514180c0039100314070320328 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 641290800 1250 641289550 641289553
    0xb210f011a0409080405030a080a090911040510170c1b070506030114031f021b1c0806011106040516061806030504060212180c15160f12050a0207090e 66
    0x1e030710303000520000f084005001e0752814010000820b007914100300d11400c0314400c1c88925600d904d25140240000e405800c1800706d1410030840d295141104401c2c0c400340c0301d080f580e003100052090f406481984d0b00c28021032500502e5810801c06920080203802003030404a05110203401003d0b00c143c5a00c0d960180c140d11501c140010300502d400040e00301490000138046501c0003100504a00c1d90078110f07007182c1d0700a5000902005080c0800c0114024201d92200404560b01c489000c12500c0103505010404c1110100000340b10368413903400300900240c600c0540b011418182000358a030607550046000d4508402c000240c05842001403001580d0403007090408c041c103290302280641f80251090360701680900242085030400711080e400f440b0f81030a010340418800030042e0a22078601e14a5111300b091400758000d45d50000b040340e034000e0300c0041c41e1110070340c03626010012040282018000c2c5002e0880100b016410100900042d1041d8086807001595100c1c0c4038142c403195083c041c0d40c1d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 641292050 1250 641290800 641290841
    0x41d0715050a08181e0616050c0606040509010b040617010e0601080d030e070506180315070c061e090b010e0c1303060c110f0c0109170604030c03030b210f01 69
    0x100c44c0d03541044640c207405010368018160030040f4000d03d864503065480f0b80e07006a428020b40202d0702c403207803a4181450070700e1401c01c0d03000708081d03481d4040100b11a0003251604005101c0150039030190103000c0c4002c004214880c0c440c1c94401100d4141c1d074103561290f107004500e1501074070024049040b200100010030f01c000503000104c1c098442c0105010072803144040c00300d01540d8000190008000c104400341d4140e0032034081614089200c2c088481a22440050203629540b15200b00f00c07103030708940c0c00b14104a41c3d4400c03425104070003800303092852034420300e001040021000b09048070900d801000d010b17129481c0715101032003800340392a899003c0ba00d04000080c0c044d00b043c0c104240a0400000e04591400c1150404944400c140c0058005409a180039030300004108043c060020340d42e02d01c401803030151340d075400c00604081c090142415803401050302c25041068603002c0540000741d40404443e08007044440c000300d4011502440703221655680e0140302e0241c000d1a80c005611303a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 641293300 1250 641292050 641292061
    0x2090f0a12120c06090308063d0905041805101103041203090b070306090c0c0203030a11160f06030b0f030d18030503070b010614070803010b09041d0715050a08 70
    0x5000107402e5901d4240a407003098038011410741d200e0300c49903a0280d21070152600c3c10200300030b00d590007a5104801003019450f0a9240d0251030381e20b0201003200c035030310101d038110080244c80300601944034540c4541032242e24110348102045040501e80300f10304480d4440041c2c0c50410a855020302c0503c0040c0051000501069001c40c04c0e0740c03106a2402d0009114549031101c5030303004070031210f507004281c42c1c2070104031100c00352240712984500c91404461f09581e55002a84070310401d010702d81001245c40b020a0726400034881c4103869808000d021001e0303591141001e048591522035800840e1402c80114040d080903400d2004102008002d0b00440c009048181e440084110190030ad0341007080303000c00003507400c00050483c0e6010f040042c42e031f0341c9089402040710880062134052a003052105400041090050b0390642e290040ca0036100c10b040408038004008a005440e561234203201e10200424001c529001070301e00718035880a15841042c0188d501e4031a8030001000517000800040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 641294550 1250 641293300 641293313
    0x3031207050d021b0d1206030f02040f0b0a08010e010f0614043c1107020109060813080406050a0e040e03120a141e071706010e01090b0d02090f0a12 65
    0x9074070055941c0c0103041c0001100c070a108004150b040e144554440c40200c4036198206d001b50f250040ca85c1003d018190841d030741c40c03142c2c0700181c0b4020b024607140d008000038500103401882d00000b01404c000b01496580b88000d01030701000911704559482c01c556034255200700e000c1c5405031403c5240d04802124500148402003c2c00407080c040c0c1a4208820741280001041030710800c9010704040e141c40c81900860b204485901914030740c2c40008114480050740c001d018001200c00d10308244000b985d4030381116403c0e000d5000c00800d000000103000c035580d5007043c00303000ca110301d9a40700c0300300221600030711040b00c1d40d14440e00b00307550040c8508601c01c0084009990b1019182202180c0300c0051004410040070a4680680c0c583c0c030700780000058034140340b880381d1002c1c840c94405000d12041d5007145160300c0141480341003064080030458182d0090008100500109031ba151707507280c03588039580013900600394451185c2c41c581905040b03868071130190b8054601e00032849804181680d20503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 641295800 1250 641294550 641294557
    0x1b031b0f0e0109030206030c0c06090a0209160c0209040c06030b09040206091e040e0133150c050a0b01050307091112101d01030201120218090a0e060a090606050303120705 75
    0x220b04119610b03001200507250500514050001100015140e941c090000e0b800c0020040c500e1009034040080701c40542d032898000b5400088a11692031034107100c0c0812034100c070404c0f10185d0441400c2c0d05101c00c00008600b0581202c181e690708005400ca00c5003044040d000c240e5010f584100140b294603501c0c030f081d00004241c001d5040481c40303038481a40c04582581c4c0c00d902d1102081e50b44800803041072008011000e004402d160000402003115410f445070001c00e03025075030440403140d00c002041030288248060168001e0222802e19060b8580700903804424042e140c0a07000700f001c00a1441214015004400020041603013042000c072020280c810004103080425000b5076000144c40005000240111459070000380b00d42d815400090080c00e021000901c40c144100242e207103c526400c0d98140c1090100d9410010b03460b03950807000940000215800036020310030074003010202540c040104144680424058030f07940d10205030320381c00381420740391802030000c0014980c5481039004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 641297050 1250 641295800 641295827
    0x509100512101d0c19120804030218070207080c060f031312081b03010e0a0911122b0909230c0307030e01050106050706090609061b031b0f 61
    0x8580d00010a004800d0690725142d0480f00c84080d1008010b89441082c80210346684080c1c0d0f41a24401c0048403001403080c0d5442a0710b001100d0780d9514003041141400c85000f16002018403e9104c00f40c0c07081551204159402000351080074000180c00c040492a01d695030801400c460511000740001c1480d41e200a140ea80407a5102596400180500086801c4844141d962902624141d82a8688400384000080315280c060004200402c2d2003490640c1c410498500441d1310512464881d08950f55100702c10307800041846010b411760700000340b00040e0800800f20b05030407150504c412a5204044018500041f43c1d43c60a0055021a03040514405201d5641079070303005407104109110710003a940940c03200000400d02209907410b005034580c0010b00d0303000300159450800054070a01c90000020a2652203110160a0000765480717074400340e070024000c0c4090341c8c06a1281c4410035000041d0400710f8681840c0c42d0035041412031044c80050a519800c100d150035035004d0301e011042154 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 641298300 1250 641297050 641297053
    0xd0f050f0c16030507061106100306090317090102090109090c050910050c100c08061503011211120604120824042903100e07171509030909010509100512 67
    0x1180c1d610051801d64003c500a60107000c8181c1807000040940001c040140203551045d0f042c00b480b242004110021282d02c0100000c04044520b0156684202080d410510f510010104614060190010490a4400d03aa03620150b80c568100c1011a0318915545001034420300c044c0d0500c0c240207110150300445410a82c1c00d10403001c1105107090000008820056180c3c4030000e1020f41140b4803d4000c03100320703003208048082c0003500351580414491f81d1100b4810240c0f4109102d0940c8005443c00d40141001b95061006081d030350342d80c1815641140c40440d0b6082180c501482a0403480c0100b040e03030303914100e954900080307100010035040d8a5910594401543c01c4480303544ca211002e80030700e001000300305040c1108040c140b046010741d034108541041d86441c07a0400224132101070700c005610032400c80385c40b00c0b20740c1c1ca40704d0100000c11004030342209201c902c100001c0507020008040796401c260340c0e220014002009000e03114960b01500380c01e828051803400d0182400f07100c11090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 641299550 1250 641298300 641298313
    0x40c02031611180c0702010908030304050a061109032505010503040c0501120f0c020715030e03040b03090a150605040609060501170405011b1808011404110a091406030d0f050f0c 78
    0x480f0300c2c15a04295040702c4070701e000061031400c43d40c11400d24402480307040003075403d62034142c45080e1a100b06840007440b20380e441c40084030900030101a150024009030840f108003a024102d0150004427200d14601c0711103030100020706610803000c6030300c40d917801042500258074010041d00d00e0000390181c140e48645800d150982c1030307150f22a6030301810082d8010f15826191069519216460a07800790405040000d158541100001164100c0c1c0c10615032a40d607644441039542032003000c04004001c042c5000461340c5d84c0c400c1c0c3e0020001c6d90300858081001564503003a40003260380501c0360074003284210f100d080751045c085102d9075001c2c5c055400850002420750071010310780d0031801600d000c2489004c3c0e80000e0f81c0e1100710b060141c44ad65008000cee07240140352000120100820003800710f0300c0108400000c6d140c01015030028081424144400380340c00d4040e051001007101c0d031174000e200d403291612803c0d00c5201840d4617600d6980341d0500c1e100064a100070564070400300c0007400c0c415617 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 641300800 1250 641299550 641299579
    0x70306020d060b030903120f270c060a1d01051e0a0320041805040b01050603040f0506131a040209012d060201020a1d0108130302010f05010f05040c02031611 69
    0x1040154411744008018541c0c4803a62a40c1ca0175806028003502d841d01c40344030810900903039020030311a80100810301805003020311450f0518181e44000f00355044403010410000158128416900c480605480f07134090345907a80044070507001c0c142c001c0b125124102071510404103a40020518910146000720304400e421a5000321560342c03008003401488006010003c00310541000480143d4501c1c0c1800242400e45440c00b4010041c09590b00c1142c0000c08101044103102c8501c1c85203030700506a5840d0310340400c40d4551038000d01d6096070503070f600c500d4864034180d64400d490f2086600800c0c0c04560303424440c4812118045520310841104101e04030980440320a0102d4001d0409034000359035907c0c030042c0103160700254105550000444401d142a60b0b070803c00181c3e0101400c40400003074142c604049002d4820f0030402c201641ca00000800c41e00e0826480a00b134070310550742400a00c0759610126580d1040711030310001c5c85001805200060a040300c1030755180001400306094203841c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 641302050 1250 641300800 641300819
    0x41101050d0c0806040f0605030a1415040f022701090e1213170a081206010c02121509280c030b0a02040905070905010c141c1d0d0203070306020d06 65
    0x90082c844080f0b180501082150715140c02252210001148144200d40ca4040829985c00c644a00200010101c02c003501c00c0760410805542400416a201406030515080c40441c1440b5001b00703902444070009225054030440515000181f03000c0582041e581c60200034000401d000e18800013540600c540001420000d90082c003481e01208028a0032580380030382d4464482c408600c80451b03500104e041c1000314001000380c07150340d846680c0004280d50b03142e00485814000c1c40b40258052030b0000059240a03000484803540c02580c082080c8545828030300540e500c12404416a81c8028102d00314613140d02c014212030b80303a10820712403420503160383c3d40e00c1840070110b8090318202c0c0e010504010030307400c9000f0a0340155050601030312590408000a1190075a0080a05032070749a01d24280078010801001002e486030b1307400c11007940319004000b4280e80009007001d6940c10742001059031071400c4900a04280d6009000b44409840c50365404042e4014030b0010b40a10b80d030340c800090301003c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 641303300 1250 641302050 641302061
    0x607080a1d180f06100c110414090c04140907030201050c01020714030a0e060a0522090c020109050c0f06030f07031410080d02060f0a0902030307050313032108041101050d 75
    0x240b4041440c5480c2c0507261440051008100521805500c0e4034586815040704042c0100c0390400388400c04444080c0204000d005003d61400c0c40801410801441c644081169114900129000e000481d401108400c1040d030540c1c0000458014a2042005600800003450900c000300c0001d17052002c151280b08503801501c00482640d04002290841c9130362148844035032203411200170f030a207811100c0003403050040320040b2a000b800034002460201d05508060024000707020207110310b11140100034060883d000044460f40310340310f01c1c441c0a02d803840c880d001010300540b155055503600504190f0700c10703000e0144001d25a03030381d6114003c05055044144900c04411001484920b01280e5030720b014064180a01150400000e00c04000340850702981c000300e0030b00b0040b690384140d0002a00b148581c840040081c8000500c80024030030080195045a0094056200981a0300400750071090742606020002d050500020002442c15030200c00118041c9001403c0c6a01c0d1b10390700c0308031a17 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 641304550 1250 641303300 641303329
    0xf0c09041e020a0f02070605040b0a030e10050a150f031a041b060503010f0e0f06040b060d0603150c1b020d06140403031d0a02060429030a020301090b0607080a1d 71
    0x40c2200c2001d090b04e41c04200b140c0080003036180c034034078083c5004d100d13288a0182550203002c045d110380b0014007242080042010f180960801003101e8201983c054000f8440c0c0802d0050544940c00005058600260707004200c0e6048103166030000071110301a802c101004008641e000e11080110041500904103000684481c0d1910341c1c1d25410480001072900c1158014010801c0f4142006901c5504c07000031038000c00300740d90114a4074010400501623000720508104054034203200001071000c5812504600203c10b001048420500d000849024940158036507007807030341d1f0082d10014201043c085440a02a0000288040a4040484100c101178500b070700000d8480146016560351181c140598001d0b0000608202c4101e81c0402c03514011440303400015804a11102a100154500c5012181c40003078000e40e40e00d02280103c2c001d400030300407044214600520900c0034103240044a0503160460600c1d4100f00b41240102c80f8446084294a03010100c0042e80900340c172031071680903106 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 641305800 1250 641304550 641304557
    0xb0102030d200a0207090506062701021f23010302030a031d0402041d0f090a170c07030f060e0c0a05060c01090204020a03090308090a0b0f130c1d0f0c09041e020a 71
    0x18642510700c0c0036141c01408c02c038030a05d410403e00c81c01d48500703007400c00d88032000d469070440d80f03402d080180d044c5007e03c0000c00c0b404048088402015140ea070103a010700c401020741101042d4000917100e6190b000b400025050750001c0c915502090141d13080c15080c0c0001c00001d8a50f00d252404101681c100b58805d1152035003401d462400ba40000b1220b90b8041c03440195800b00e86030514032039940c0c0f0021071001d00005000001c107460400358904880b0000034200491701603e40d280f8000c0341d01c108501060300c46510340902007840400119040010b01801400c4015260501081010662002c1d050340c3d032039036030340c0c44010040c0c42da80041c102910361a1000142c4101904010384414002800000c003030304102503a10000e00c0080c06036800c440a203145401580d0f070704200e1311004101000140c07040c440143c0001e81000740c2d40c5100e01d1003004a50401103a1921590361503000700566150071072480c10b1090803958109a88802212228849a480307405154960582240d1101d80d50b00c000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 641307050 1250 641305800 641305813
    0x30303020d0f0902030c100201020c0708030903100c05030a0c210f0c02010525020a050312041505070906120207140102071403030f010e041703190606030b0102030d200a02 75
    0x140c4954455000758107102e142c244000340d0142d000a4562440c403004038403035a04070001104040c0300b503041e82c5107618184100d4180d2501c400e9a1681c0e9041820420300c00c1c07058140711305c00c1c9403050045034045521038a91034110344907440c045015203001c000705001c115102d17911558200400d1300c41c6a804011f08800541450b40c03074440d01c00c3d0350844660a0a6a04144c02c1c03240e07d03050049407141c1f04a07009225502c042074031004a0400444c0d032409420351002203541c4040e20b0303518601e03c1c081c80c80b521701c030460440b000b0400e0060340c0c1c0440e078603001b04101d0001080610701408a810404104040c01880d140103079903103014074524032000c40800c0c3e41c0803910f03034100400354a510110000304bc00650039480c01015043c0f220b001402000180031080c40490b0400460745580c1384208000d0880705d440c1d01e00440801080744c00030024404d41c074101100014680d00034455101a940182d02452070300405034458009012441045064841c80b0940d81034051803007c007030301008400d03901070001d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 641308300 1250 641307050 641307067
    0x10518010f0b090a02030a0603080a170a1a13060906061701060305060d14100c0507051606020a0303020c070503030705060702120f03450601081605061305040603030302 74
    0x315000c0c00c09a5004901e002e0001c42207a88960003981d02c080d25500141c2e407580d070311110601402103944000e0914001140b0400d6860304000b0001800d0101000c210440d900c0030000b4059501a0b4102d401090342c140407040c040c1031400c0b50f00140c1d1446c120219045039951981c80c12210b90394044400201c4800314150441740c0b446030b0f180100120318080c44a418450300240649150030001000b5501c00880c04641c103030300b071000240d920b5414034100301c0c0c901042c2024140741d1081008540c0c03809045110300201c1000504e00c070a8469560080540200607078007a002540691002c10080c46900c5000820750b030308200400718a407103100036041c0c0b814004806031800c0102c103e00c0c2034441c03050242c24014064481aa0b81c014038408203c030000114040780e041c03021110500d03005092440d40806044880c190714902d203011a041210700587c1c1c1c4580b01c1da15024503802c802c816110034042001203103042c1c0041c01010201e954440c4181395a003000170115901a4411004260080b44141 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 641309550 1250 641308300 641308303
    0x30905070b04080601330915120b030f28050706170108010204060210050c12180c3f03040e010e091c030f0617010209030d02030c12070212010518 64
    0x1801403861450000601b21090000046159000e29040070b01c0e10824000700e4180c0725501d454020610104681614003c000d4010003a00c0001c43c1c100c1c01c4e500f0500380171011f050019001c1c2c03000c54250090700d0036900340140301c2c032043d001e0b04281031195200645c0381c001c29803e20095009041070b44618075412080c404910103190f05034040e51150b4070611041000680208501003592030020000520707541d10b0f00d104000380140d80000700590108010800c0d810762040c15240c508410f00100d611001c252070805c0044401c945110710750480e81410081d07800401040c00da007021406005624660a0b03410440c0b45802c40d500007104101d00300010803203400c9031150b194004460002074900c402e1443c002994040d101ca181d03004040d40c0d115880581c1c5801d0780120302810010b180307000081d0b03c01c41d03410f010350450203d191083c0125075101001d207000200302d550110840001e403508039504800c0c41c60030340281c041030342c00c030a010b40c8400c2e590400b0322038a8031840c6002d80034004040241046e0307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 641310800 1250 641309550 641309563
    0x1e1206030c01180504050a0e0615030f01060513050901090f08272d04020c010f050601050c0601090902030c12061506042d0e07080f06060708070303020a030905070b0408 74
    0x80c14043d004241c003206003040e050810507076a0942d0b0128041e00c4600f40a00101056400c0398064020701e000d00c20180380c42004121441000c8084450002030080e41c6400c80b82d0912489601465401c0c1280c3c4034040b07a00519800b061f141d0001400441c15200e0740407008091400300c480080000340314592410700d044413048041d450300b20301240d281900c042030099001410725402d4059080681c024404031824200410201420941d20342c1054080c05010b0103c034650840c460b0704140014007954461001e907100640001d0040003142d103041115001446100d20598041c0140f01540549450700c08032003101c00380c000005c01403440d082d565036841c017150030707000b42c89202c082000b040002c500c4141c803000e0205501c500b04502800f60a0807030f118900d68801080c80001d00c0030001700d030b83c108001910810f1414a01c0c05643c0c0d9242c2000000d00c5480300c010321032203041c0010004a41b090b409030411103024180050346188545074540303045500d610400740c0210024050060110a2100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 641312050 1250 641310800 641310823
    0xd0c0b031b03191a0a06020d140703020a140a0b040807150b030d030b030f1606081303050403110609130e0c0402090a030b10030b0f160219081e120603 66
    0x503503085040500c0c040d85591540c4040441c3c058541c030f15481452180b03486044656401400d4440712030303407a0000307074803441c010003c040070400b004140604c0902120031105050f030b055024200c0707034045655003481b03990200d030a410a8400c0201e050005880038500c01d000e5406409145e4882815151030500c1c0140c5e200c844807014200340341c0e50041d440004030100748100605010031350030314600200345083d00d0301003501242d1042c010702c15441d040780703000350041c1c81259460b00760030342d00c42100406100350220b006001900800c07007000401c0c1c0b003c24000f01c40310000c003001d01d045e2030040040c1c500003c0c040c03002802c980e5050b8a401c0718208100e845042d01c001c1e5400d6003003400b9280081c0e1403913400d00c0003408504a440000c1c280403c46c180900c091903100310081c1040c100760300d40710980d45085822403590103400c0c40c09003145000148242c62450b030054500150540341c0e80d0540e064000042414802d20600b60964001803c90064002e0f40c4a100c0300402614105d4209840d1071558800c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 641313300 1250 641312050 641312101
    0x180b1e040305190c170906070f14120a0c080307030e10050601080a140c0304050102070c06031a090108031905090a0e10210308040302150903360d020d0c0b03 69
    0x2c07184009022035018442c8107000200d007680b00d06c18240818154400d90030700900000c1044110750402c2402c0f440c0700c10180c3c02c0c4048800b595036a109c9118184582110300021400d000e001d000082c0c3c511000355403148281c41c010883c98001da02440c0707803000900d003c050107601c80040020701c0d603010070402c2d841814880140001015110301c500707030f400041c2c40d01300e00150000c000b170184002501101d4840b940f015000a00c990744c1d01c001401040c8031a081010802d00c0e984a269600c1c094100d941a202664040d51811510f00e100602d402540611881400414001d560071aa00c2000010040c00210445d840924002c5241d407100c01540d000004a412507000107407581c1914001c4828080d41350030030001d5070b251400c00741d1074451142051010071a41c0d0040010070003003c0302915000d807041d0803801d01c03028620b1030b0294189250b90078414450b442824464a0700e0910555110036002078442c1c85840724548980c42000459000062404400000c3c080f524403020304c243e012000404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 641314550 1250 641313300 641313317
    0x507020f010c050909040f0b090a0c0603090209011412010510050411040303080112060f0213031b080c15120a0506120f06010308210a0e0c04180b1e04030519 69
    0xd0014140780035088413203008184690001d01045800c0313241c000c04581000c0d82101a181c64082c49556005080040350320000485001030780c035000c1c0c001c91000c107a0052147d1426820108039070031031b04041010581c00120ba40d0f800864440c03c0c0306a03030064102c07405203003007075007440180420740f90041440c000d242010042000440e50200341c180c1920302200d00e2018007401c40c104180a440291001d5480078400201c050140c01c1b504030313482c01c582c401c05007203403807403110781a060f80c02d00d01e8803074410b061b003100e5000442c5280c80214004d1460020400c1070810b49106940881140111284500e46075604144601c516101c000e16201c6005e443c0100405610304c054651210b8040c400142041ca01003582e0090090383e03000c08120840442c3c2444003032606107080f001a01080c0580f07a00c6004001c0c2c00d82c0541054000c0d0346006022569007801041c0c190ba86030440d010090104000088918441d548410200c40840c001c4c2c0c025594940c49110b03101c0303056038185100e40303040d05000e8002e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 641315800 1250 641314550 641314571
    0xb15031e01032303040306020a050414040e06010b091908010c0e0603041104091e052d030f031f030308010305070e090607030915020706060e01090608100905011407030507020f01 78
    0x58072400009290200321628028203038011900c2c0d8042d13030b08010b07d0b00b40049a41403032250b11002800c2260340c0c4602c042d043c10560420701084617410040441c407a00710700014000c00300d104004104081014284040c030381c0c104203c1c6096843c0580190203141d4640d003640c0e40d000ea200d074050000c103400310744e002e143d4105540d8207030004944403001030065860b880302d1014031a00d84d03180810740c01003202c0116180a1031a080d07031100d00b030011a406001160021840c0d18100c0400f079001d030811100190300d4421a40041c3d4210340006000406c61b421841c1468075604844c00d5000007103100c9e880e11146941185006402c100c00340d0842540050780b1030400002000024460b60011100c9c10700044500c028240b40341d811850801c09a06ca40c0002815810000c3c40c1e407102040f0b60400e280c0c0c0945036200c21084042d20400e220324400e41d40020061040d50206610030103015200d0400014100001c00032603800300c80444a003000303e5a40e5040100c500d40500464003000d178201c00801852421 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 641317050 1250 641315800 641315813
    0x109050601020a170702040903030e01050a020910080606040b0a051b0c09070c1b12140606060a0513091803030b010e0a0909030912080403121803020f040b15031e0103 73
    0xa12030007406104007160384c3c031003c100000c102ca01c09030300030b4801d00c04c0da1890f080c007501030b02c01c5549254040d860a000255582054802d40d8500e6800034064003000c003224004450002d80500302c160300450070040026000101001404050610344505864070720113440c0d100800818090032003907070001c01e10740540e41d89140c895540718201c4e040403040d1056505001c034801d10350f500001004140180f010900c0720500004404107482103040402120000e0211502c588040c1c8240760050401e2010302c2e4104c5c02400907006400e4042d800340704090343d4441da481039940e000d00c98111003441d40398000a0540c5401808801e0400b801d00e4064011040c010404510191041d41141d40d82c5150020800d8480c2c40c1d000000c1c10540c00c000000005801c0142d4184d029220031140e488400c5d81c0903110900440003d049040c2e4002d02c900e44624503002d018842c00e040028130782c441d540e01044440d9580350b46a10950003c0240225180d160880041c0a10b80300541612044801e0741c0040000404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 641318300 1250 641317050 641317063
    0x1051014060301180b10020715172a12060f19180204120b07030c020f061605040b03150a05010e0904060c020111031e01050a080d110304210506010905060102 69
    0x2806400782c103481142c0301c02c0100720802090b907001c00f10500390301b22030b640043c4603c1034680100d000744001100034070985080310650a0714202e0300c44000004e0740031102840c099040e03401c212031310110600045003154540e21011150307442c0b540d40024000207041c00203070404030000030f80fa25522600002199651880c25200c0c0b14552100011210150402901614000e01110860319041c103810f00d03190544000071501080042d2400c5009108140b0024503550740201d00d6024010503110194006100608a07210200303000040000203042901075001b140710b00c4008119400070942031007004008080c42d03000c1c504008102c4408859543d402410641040d40020006480d10f2011016405032048050f00c1c8540da50100810000010400e007108090784891030a4240e81e0f2140704202c17400041d40a1003103d40c2c0310741b0205508074001c4075003e11440d07a2030201c0b030529070f45009440459440e0009000c030303804145619002c001c0c0803c962805803501e01018060341c501040001d58414 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 641319550 1250 641318300 641318309
    0x7031d060c06040f17070507030501050a090f030e0a1a090f030d14160f050307030215010b09010c0507091109040b0a0b19112b08010521010b030f01051014060301 71
    0xc55000b4941000111417184400d402510002911481e417401e0003501c03088248400c0c2d407594201400a8080c0750b4600c20070646550102da0820821a42c1c2c070100d0354404c41c1800e035a0864020100410125000c0750b80c00e0000200b4411290790789220310070710085035003900610b4003d50101c00c2051100c0d41124581c1e00495914041c16214400c2d0010030648a03414031025200ea0002ea416100b480000301c02400c00c24001c3d001c03518a0004030840003c82c4e2424461810001814001c00703881e0361281d08201703c0076018608483d806502e545452040302d02c00042c0d02254107000802040a0030310b40600303060a50100d8540c000170b07240c090515981d20880d40e00c1814032400808460032903019a10902c16042d004003140c00c0105200108a808240006c009425884071410b000308140b003080381d21305980e0050091803001c086486048100001a80e92204c0f5540342c0203030044d182c804010080401c0d89040000c02e00c0e00f0541214041c04200c0d403ca001c0201c005011503000c0d44904040301d0454 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 641320800 1250 641319550 641319563
    0x30a0302121303080a03060f150f0e030f010e0d0f020606030319090e071809051b0313140709060e0c0906030c04051906030b040902010c1101050f07031d060c0604 71
    0x11030b00320003031004030180b542008000740404186000c1c0d060b4540e001006640040d14410302803038807408078201407a0800c000b40700007040d10003c03c1000c0d114807250301000340007404959180040c1e1400d642503c400401840c4154001010301d1a1a0b6000180007488141130000d030606092400100303869200d10100c000001101a26126806201301d40f190014a03580300b442c02b56040c03c0320020300c1c4e0054503400c8110003482141c04140807096108060281103001400300f40b41c0b02c1250054400e030801840c02c85000d1560b074540d80410201151062040805000fa01e040350800c14468111002e0360460751692080e841040341411828049034144081101c595403a6a85c107080e81156109a800864100750760555a00551901d403803510b080e210725440500c00e0a182d40d080c00b04035918910040d001806480132900031034101d40903080500818544145000860420603126500070b0f031007103000a11000f810250068404110441081e003204c4d40c03842c0c2854031601c42c0d0780c1c210103007000d80714 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 641322050 1250 641320800 641320807
    0xd0203060f07140a08012916050c030f060a1503050607050706110409020901030c0f0e2e0908010606140f13080f0f070f080d23040905060f030a030212 66
    0x140905103010030403181543d81a03030303241041001841c01c5800e00c19040c407a00356800b00718492440000504844413004589418812014464460624503004c01d0f104d901641110400b6a1402c1c4455901c0380c0d070a00051040b4103009002000322403081c080c0214018107290180002000410001d40042081c81c20359142c03121402c06600500321100314904644c0002800202d203030054000d0828208240c07001c104a01802e11709880c01c2d0001501d82d00018915910044249030003c101c5541c056800e01b08140101d8100e01c0300b50103001c0b040e900000c0b61044208208090090103848050705503440e040b0081c12807881d0040017805800c0c41900007550101c2d01145880070350040400400c407240c1152a103800644025458000d00c18044082c1d0085110100e0341d40c0c18190410f04a4012100030a013061a00208031202844008800c5001d49503101d44100d0041c540e0281000e01146000015242841c40070016417440c0003c24a002c1e40240b1100000700f6008201000c94203800450302d0f0380c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 641323300 1250 641322050 641322061
    0x18110a1a0d0204081902331b06100305060c0415030509010b030a0c080f161e03060e010506100305070c320d0e03030f1e0729060d0203060f 61
    0xb901441e04840700034851000041540310100201a100c1d0380283c079020040304502da402007101c0300010f001410001c5490042c80d035040403000520840c004090307250702e05021601c00508041c403d88540700001c0b81d081e810301c00d2002c244100c540081c001409149003500e083c0c4440c20f409009d130044008c0c03590b0303800001c070386175000e40045054403001002d0322410000d40c68990114061402240301511803058100c940341800154088609100300c000446a80b034038515555641620b040301040584081c03000001845501404d5901c4a03903400214151814400f07100c28004c00480c080308040c10902405212508001402182a00210340030008060b00e5859201c0702481201000600700040c880b010410010448510320601c1e652403c406007609800c0603a0b9020b1300b44c8401990004214a58403550b10300c10151061210200950030071046031141c0d04d103280440d55152205696000e0342c0d03080b08075100c20680c010000c50300c1111505c02900429030710100103210302015003101300807070f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 641324550 1250 641323300 641323327
    0x5030402040603320d0503040213061a0a0e0d0308060f01050c031c0c08040b010b0a03060314010e06012702030a02220807050904120513080118110a1a 66
    0x60246811540401c0c40350070700780189103140d100200da65401e0b607440200164680010030b0707001a0b0340b07082c1c6d109070842d1a5078003080401c071f40842c404101140c6d105070014580d1074802c5071b060489030b0400c003c1e49444100b00b02400c0000900105441550825460030020b82c04c000c00c640c01603001c0e180b05241c0443c40b80140c03030074418034501002a01c40400c01191100d01081d01503000c0b034007030200740708094a42e01c040d5052502524020610705460700107101000b500c1c4050540c003122071501003901503a986860b02080303c21148809940d44440103a10034580400c032090042003034519001c02c041c0c40c04131070301c0c64140c040500c0320080d400001142c4030000369010703151a480f503030900a1180346c426801020000c1c062059040340e020350f44000810745080d40d5400d105582000300c6892803000040211156805988a080e05030355013500400c050a0134031600c203422088041d040c1c0c004200d0b050024109080c03030903d905c5000440c0c0d051003200080d428014182d2501c4815075204e4030f00e06c001300d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 641325800 1250 641324550 641324561
    0xe07060903151e0e0c120a03050a031401060507210e01032f130602190f150f020315030309030c09061201020d0b01110d090b0a020102040816030606080f0d0503040204 73
    0x4500052080c3d403400c2200d201ca038820f0804810100480c3e80703440c40385060003100c1080003454005d80e00900e0442d000301e0f008800501c3d40e240c6a2030009610310f500e00361a21941c0003030700b050000540100d000410010381c2030444600c107813444400c00a1400c1441c1c020202490600042c0c1095242d619810302070044112100c05101448c220a00b01c50549150580c01e8104140c10740a0840c0302c440090081d001081e181c0505e0261040074140040c262115242200100c20803600000380e892503207210280c9100d5a41c02208000002d0b81c0e0b400c0031380d01e070624001ca100c0414400e40042200120964000844c468059025100750380d5903a81c5d140001c032443c410030246600da5000040b00708224186a10501c10346800b6200c940b04210148060741d681d40c0030849d26070101d0b202c030105000c181c10807000307861201c0d954400540f03016110f054850800841c814000d50591211400303208005680c000d640c00b8250420044c410840b41c80ca640b640e271281c502c0c1c00c0c020f02030b0000105095403a540c204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 641327050 1250 641325800 641325821
    0x303031d03030a020c15011229090610080d200a1e020103060902030f0f04060b030304030f0507090e032205090405030a030f1b14070c030803010303030e0706090315 72
    0x40d03a490f49080801640654000c8075889002d0280c4200070f454960b40c0c42000303050310030006030070301c0161b4550356183d1058030340c22151003809140c9200c9410750306860480c601c205c00ea40c0103800c0a0800214000c03454009030400d140c1a0020403401030401e40c04002d2001da84100382d4440d100349100701e103c90030a2804940034000c030503118102c6003600303c40707180020098800c0e6001c10000342d85d410075804030f00056425803880545038003c02d117802c1d45640307800c0e0403030300a40300010000b00ca074000900d16841a80212601680d2900150030f010051026500030180480700303001c009141110b0b561a8170580c040741c0d84407090341004061a040d0381444002604025100e0708050609007081d581d070350488024003001a05065002071010094010306203141c0105c00c61200c031594400c801d4a40d9907021580c4441c418003800294041000340361000011030040c1669566541141002415286842c21404245d44035140801c54540d0000fa550112600602030030a20101004500082c264078000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 641328300 1250 641327050 641327053
    0x604050609042022051c0206030a2a03140c071205070203070914060103060819060b15030103150e120906120702010605120f12091804050a02040c03150303031d 70
    0xc0c211424074030180394620344110201c4000c009585d4104100c4804504000e0f0b00c1014401070300d5000500300100a1900440056808208813003040d400380010541c08012034060781e02c040800c0130f00d5406108801d0018125452010903242010a000040c85900c03002042042480040c8000522420070303154890f41c020180c86445039607003603100140800c140e200ca80300300020007242c0190700a101c0d203001c43e64a00050130004078080841144c940070310400341c50300c130348451318005150390b20181c444854082c800b609859504508105441d6400c0300303440030110707141c05003c00c2100c00009150312800480c041541e079070303481500440d9650048464003401c0d400c089d01407001007a0190004026035009842c501d1030341d80d8640009039911a410b07011036640e08160b0303542d04050026802000408009050464111198031a1481804085070f0984081e000195540d0451525003e1880364513060b240505c00c5440480e00c1f5a2142071074400101031513a1906d902020030070001c68692408015030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 641329550 1250 641328300 641328307
    0x91506041e0e2d130f08030103030207050108011a07150e010b0f01030207030509040c0c0503370f0807020c370b0d020d020906072006040506090420 65
    0x200d01055603a29004188140340494009450111141c040d458625038040d03000030060040001458144400f40080c200c00304000903c4c03000c07410783c410300542140f2441c3ca00390b0303940c910b040082c01c00040307803c03141c104080c0704010010415455081c4d8170a4000314081ca580d01e08515280c1d401d894480e0f0303060031582c10f00301d4443c060705065003c8222000c4c2030720121403c00e40d6000440c224460500020041a018042c40006040c00d42c0030f400194402c1c00c25880305510303500c0300703461900206820a030a02c00d804006072080090b0002d13003a6001540410b12144001000c003a2144500f0a906001c022035400009d030220700c01c0052440b03003240a80002080070b54080081030030300c0700450380340785280715840d00c924449240c9d0144d42142c816025a6042c4681c0783d6045020354800c6140341c0c4e404c1d0f024000c410255443e2401030003c42c1c800d8288501c0d00401c00d068001d024100c2001038841c80013070004101540340c0c80c1c1110002d64049800250b001c00f41024001080c5d810a0007984052020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 641330800 1250 641329550 641329589
    0x3060e01180501090201020f011512020303091f030b010c1104051902030a090215040f1a0f040909060b030114070c0f0807030509120d0c0627050d0f050909150604 71
    0x10b41c00030754114001c0e4241c91104e000c400c10308d400d8401419094940f01c3c181c403020401e00111860706002140f0080070740c0c0c9480326160003e8940c00380c003e0300c058000e452800d56503140b501481046000f1500f8200108102c0c81c81e100c3c4045100e90740380b104d000300c1e258070008406913070070851801410286102191642020380b045401011404401c0b0b00035414401c2c07150f0715001e40000e540449140c0a04000c045080c801094a122074001d800c04c4442c0c01030100c0b400c80e0b0003840c00f61001e04038102002507414040d041810a0f541e00409041c0070380d243c50303003244401c8101120700c1d034484102c0c208000c20b0003281c0382280c00701701580c2d0b02501a200106d00e000c10550b00000800e001031007210642c480d00c05408429844010f10040540071603407903001e000c0000c0580e040a5044407480300c410000105d9905c00d010858205402142e0940104804015054020007002e00000051401c1c5003050089404981b1404000d4405040740d244841c40140c2c07542c982d005c40e030103443c1a010f454403c00c000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 641332050 1250 641330800 641330803
    0xf0706090c05040b01030203190e191a07110d0e060d0908031005031906150e130b1005031f1b0305010504050708220204060807170111030c0403060e011805 68
    0x240c05002c1c803d0341480420314441d0b01c01e0081c2e0b40a84190b80ca0300c0c0340000c1e0500303407000426403290a414079000710f503040d0014200f070042c642c0d0507501400d91800020007450300c42a00110003050f01e0f05002a640304d0400c076050019600003e00d9241c1011034400f441900014900d008941034a58000c1c01c01002504201180000d103001b51000c20300da001c4140c40d54109505e86a440c40ea5100c21424a043c0801044960300714518503a80e0100d0920f030719880310072804403031400b103402241040070b02c00c007101080300000340f10380e21103548103c408040b414800065200c104101c500e500c10341c0c60503811001c041c0203500480f50a402d0284c04401d0112442c0041c01410092148070310840c038140024800600035a141da110356400b00f007100b03080b0b1100303a0010013040f050348160f0300305650700e8003c28000b008000e50340c040c008091101e00e18121141c03003142502c00020628050960502c14064000000e500369400d8035406540810348980f4400070b01c1c01407008071468100f01c031040c201201403000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 641333300 1250 641332050 641332073
    0x110d0302070504200f07150608030705060a020406210212090f1006050f040509010e01020a110714030a03050307030e0106090e0f0c0105040b090120061f0b0403080f070609 75
    0x9039014004913280c1c490f02a05011840d003052818107041050003850900440104002031091007802441081e03030b0030725022030f1440e4002c02910307440060182c05020b4100701603980302500030303c1545000c0c203090300180a0000810400035021603295882d00c043d0240e01a103d844140e162088050303d420503000d66550100d4a0250090140b40c0403040780380a0350081d00162400905807030018038a150a010042200a00c0c03039141e95a541c00d80b12841c4828002004584500c0d6100c1440c800501d2045050560a602403206291400c812600649000c1803850040360542495034490b9034085c0c080e000b40484080a4615510b440e030041040102e540c06007119140e4101241c81c503905003440d50381c1ea44034020b4030030301186043c0010840342d02410010220600c045c0f4021503481c0741c00b9403882800040700c04103401c40e005442000303600010703400b031000c00000c140040344182d8035010000005115500020b80700310b9000030003840f003a04000882d203110f9031001c810030a0402a040903d20400d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 641334550 1250 641333300 641333309
    0x120504050a17030106050f0a0203070f03030b0a08011503030804020d0501111315091a09060304080403110102060f0403030207061d070e10180c020c1201020705010506180f04110d030207 81
    0x5042e18111490107086100b56410703200e203a00e5003458824220074510040c1c0000c0d060000314031003002400300045000070381c40480b5100741c5010a0740c1180d101082141d1500350090052680b60a2600e02004240314451048a0f00340c1040341c1180c880d8000701e1610500444068035942c2440d800321401c40202c8024603d02c140358901a42c3c0c66110407460000d100d40454420009203013120030f1194015030031b01061001d8400d40300c18130301a11038020941030341044070159003000c2c0106081041c0f1038642d44403100f01c202440038060500c1e006c030220010040151001d020194042440000c04c0326603403010341c0201c2032041614035100300603042076450a40c1d0054284e264030500100e4190884203490380190f6142601051002d080060300740014240414800c08511421030001600d46402141d80c039060048000035988407500c1c00e0150940d000034091500a0349040081c0e0f1410a0600301c040d04407000312107078402070b1030360300f070004104003000301041e07108105403024810150000b81100440f03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 641335800 1250 641334550 641334563
    0x40b100b121f080c0910090f020301030c0e0403080c0f0405040207080a03060906060f210e070f05060901210603020603070314100f03172505010f0b0303040510120504050a 75
    0x190700210040702c480016200311490380c1d120851a00140c60051001640070000e0170080221941d515240f42c161404c192280134041d50000050040c0038640170800d000d0310644821064508083d40d0041c10140c0080518581d000b004c02c03056554400c0398201e500514004109646400316820903e420b907100c0524030010071300c0c04c3d1000038405010b00030601114581c1c0c888040600010a040d03605412000070108080c008200018007158507214411050709210002c0124506100004000b41d000703400c4213102d21000c1c01102490707031b4081c40e810b012000030f074201d4143c07441c01608000a0310140d00000d5001c0404010062490f526912401c07200c0c0082540028585582c182a2050111400380c4101082c2c40c0c2c1c800d001003640303031034100c1c9095800300e1540c0c5005030a100c8490b481d00c90313500b1905c05100e228072100601209004e94044040c0d0b541c2c0030040440c40b14006a41d030312403445000d0241075020700406085004110303061042c561920b081c1f00301d24240c0340c03450310f0340d00f020300c100d842 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 641337050 1250 641335800 641335831
    0xf1407080904050609040c05010f17091c02070e0604180c1e35120703030204060e030c01090e070201091a090105010e0403020714062206031a09040b100b12 68
    0xb84d02d014005d9034001c1d0340010207a103241d030a201c0119503c40d10ba0355180c0c18004030300d18030500c11042c4265180b0415502c0050820312890741081420f01c2143c3d603c1c0d10440d4031481c0d050008043c400d41c81900044121070018184000f02124070300090742d10400380c607240022000054070b0908107910084500072103402408544c40c1c00d461003103062080c0900c0c802d90041c2e0b440c5414840103503052a8511080001c4030b1000400c408108181d5000f104c0c01c80009801040c104204c07074000150304042d0900310041d008400304513000034101e070294483c03401011441c602003000c05000f0341c000043c80f90030002c81c5000f00c03030b14003001e19a008155819200396281900001d21120300c8000c05015988c540d026001d15403030041005454052000c600b0380c4890100001100c01c441c10101d40b464070070300c20b035440f245454040d010b1308580880190340078252104501c6407042d0343e00440310b81c0c080da100070307001c07082d440c1c207020324400c0c0c08290400d000140303001070080000c148200701c1030b10484020501410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 641338300 1250 641337050 641337061
    0x10f02010e150a020f040602010c02060105180f0c0c030703021606020a030801030b0c1603030b0f01050309251d040606120b0406020a03110d0e0f0106150f140708090405 74
    0x200e400344030031840260005142d004840000c04901604900b0300d102c09421300c054400341402a902541c02040580c0d91102d844841903014801c19006000490795902d11007250b52a29044030402003102007001300d4180040d200713198a106450403a035007201201d440301214a0702039907038243d03501c0082071000580c0c80092010300c00505030600700e0313240d03491072030a03461540c0703050080e04003401a0b104a4401d000c4050007401007100c1c8002c50f0300a0382c012602494207410f0124903140a450b03141003110420800212030303000540342d8540c5913407500e8462010000034210807000401c0e00720007102c94110002c1c0c01c00c034100c884a00c0c0114054841040040d0b40d80e41c80d00d003d064989001011f9810100010700481e0690b800b401080c0c40d9801c01081d440c50441050200d640800c15440145a44100800035941c04011120703c40300f5075802001020700f0034401030040140350020100b041308950038040050310079170001100c0420b071141103441d8025450031010b140c00c4810f404d07004515140c005607 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 641339550 1250 641338300 641338303
    0x2301509030403080714151e0105060f0a110d0302130b0c0d03020a050702040509060106022103040b13052e140a18021804060e07060f0e0a0905090a02010f02 69
    0x901405009009510b070900d1603980021139001441c3c16503074000c880700088072807003003401136041c200c00e88640c80b201850314450105190b295984112040900c810050000b034550f0001c03103915140843c425602d030080b0b0a000c85550048101000003401620a110007064142e006454810030500101107810303100d500c1c2d100c081c019000c41c00304980c41403c20004441c041e074014000c2c21482c0c41d0091410300e080e008201034800079649490558482001000707000d40c140301909004501c0203112041f1074a03181401c0d03d600000e40302030044004134000c51641d07002003040982899001c8282c0340d001064103c03d9807241e00410035030210702d078020f00e084801b0f0110300c2402280b103080d20b090080c68540d43c8030300006044110f26220320181d09400382c0c0c0903991b809103500040000c03141c00042464680f03484801d8034000491207181d0fa1201c48140001500000305950901d014607159280d03074074240006002e00f440f540900c0c0342030f1400c8107105d07008001042a9000f41e000780c0f1035240820048030201e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 641340800 1250 641339550 641339593
    0xe06060909062e090c09170d0504030b130f0506010821030a050a061206020705070b070b04030f0201020f07050c12160e0c0f0f12061f05070230 63
    0x280e016142d900308260b1400f081804182052401d01e016911103502e646520003258034403080302c5d003c20302050f0100301160203050701e905210713450400b40000d0304d414940503100d40140d000050081e144940040c01c0700d0222050441c03400c0d08164014800313102401c016850325028020380f400d43c0030f5150040b110717010340b001d80100b018501544a02c0c41c0d58003211040107040141070a090390751074000005003d55980c0c1d075000c203140140c2e0b005981d038400303141c9113140108507032114503620310502c0b82030013140002502950003074242c10711a24240c1002400c030300a206511440d2514000810520700380400011000300d182c1080e030340f1700c0c2e2a841d2000c2c40703543ca180c4010380582250100006008000303160030010b410200c400450384c18041510303060609608040503036a44a1b0008c58070358001c1a0720b040c1d0a400c00001c4d907503801e001e070380080007043c1c605209480c00c2c20f2003000290b8030704545440c0408101c81208007010011046101001180c0940d4000c1c6181c40703115403165280341280c602d058 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 641342050 1250 641340800 641340811
    0x501050a0b10110a0b0915060d02151303021f02060a110406030b0a051e0306010909020907080c120106030b040f051e04020312030708041a04021509130e0606090906 72
    0x451110040041c2c0441c1c40c074000b41038000071801401a48400101020f0071140222000b00140c4002c08101901030088072004001a2080a120100101507280c5802c03080c041484c043c0c030942e440c409000a219002082d91001303400c015805048240c000c01c00078407106440391a42954540d840703599a0b501521070540200a25000421080245501030b91207406685d00c0505005400c503074a100246110540e1105040c0c50f000b0005080c0c00ea1405100c0070303000d00031b0401c0130030600c012500401d04803c0000d014105000d00b03000803c10010440c42030720851041c200001540c1c1d0713103070b2100030080c1c001d15461501039810404840380c40c0300b00b401028451258010603214401c405008082c41ca02c4c05082070340c150040a00e0206034580000c02988500340d25107442d80681080c0c50a1800e1030811400003000307114540621005a480542800b802141c0541142d102c4000350002441024200c0c2e035401c0d414641190480400b0010502520900d0212442d01c16907542204041e15414200c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 641343300 1250 641342050 641342059
    0x91103060a0b0a02150903190f020d0509040905030a03090302190b15180103050c10050f0d050c0405040612060b0a0302130203070c02041a09070e030a03030e0307050d0504030501050a0b 81
    0x8007405034258070341c09090440c00501c125517280100d0044010030f50000d4544295540000444c0100c0361141c4041071150815441e0103010003902000081d1201c5290501d0010814000b2b800d0701d40384e445411810255030480705580d903400711800050300901c00ea00e0203c0141c0604015079124552040c1c0c4641d9140e00921071011903555481d0541c0801c0d1100c0d00181c1c407100c0d028840d20000020442640650f100d00010100d91006100308160260a0f56502d020814100040800c0b0001e840698154000f801404100d0f030701c40380d41c6800c05020702d400c6213800030314003800022000100c40c0040031070340c00303050200401c0c10080144041d41d4094007020350482c00c1d40180f480b030150560300456019074640f40076220314800d940002c040d101003001807501543e0002d4000f0b942c0c42c2c84502c10380c0040f618105a40b80c1c0400b0b001107500c1d1640e2407400303002d055440e1010413003e01c0500840b40c10301d9008040d52040542c658000d8820707080f60200780c40c190701e030900040c0710075054401c054140500a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 641344550 1250 641343300 641343319
    0xa0303050306130e0304180515040c020c060a1d0a060503060d08040305010c0c060b03010b030601120c03080a02010c02190506181014061002070b0706020a02030f040f09110306 77
    0x880549060744050400b541000700720b82c810100007003a01c103600808015070040c50759940b5103400d00c103000c540001090480c1c3d00e0304050149440c00310102e0103044500f41c602141400708d0314820b9040c0080c5244054109100103000e144444d4400300c030398078036418110100000740103031040c00086030182c0205e1001c13030010808604140340c07020b1215010340c4182c40c081d1500d500e943d0398600f980c20b0040220081520f40380c0a07410414180034905603088103030020410032102d0b03400699620010312420501602c152000701c244101408903101942d0454000e40e03840f00ca0a500900900003c2c0924005000f01c85400720780000441481d40e005402100a02c81c07a1034003a030803401d8480111451303c0e18460b100d8090540542c90082ca015101c3c00500a015441e000e002c1c460803144054094007150000b1500b440700210480a0b0b54031960010801a141c1c01034141c1a0726600c01c2c411040c3e5601804280000c03c4801c0c2c4007007400381d0300c00071414403200c44c241e91340d112280002d0f100617a2001240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 641345800 1250 641344550 641344553
    0x1015080709020f0c030a0c06060b0909010905070203090316030c0501020a150507030f0e01091b0e011202040b03071e0b0c030714120a08011508070c0b04170c010f0b0a050a03 76
    0xb50080c100083c070825107140f901c8644441a451580121001000300d04080001d0082c0700302c61007a0402000f025100c50318010300c0e0000100c4145050095100d0356594001103144a0310070020740782110030180807901000c848800040c01120075100840340912244d1006c5a25407001c14454903655011988110540f25282c040000e441c0003491141003564074141d02021512600820f40b0000c007803000020050700c513040800300c40c09200b0140c1015140c00c2001c1041c2c041142030740741141c000c050704000084542c0b0000d07014001d414001945442289000b180e003e20b0031403440c0a40c040450303003000380c0d6504d11140040380904161104240c006005040100d003d00241040c403d030b40000f55405a0003903001c85815802c0b543c0300714001000d000050000b0b1001ea4001703501a400342c00c20610354030301504010310348400c40c08010061070b00907000c941080802ea04294518112504460b12501e100400303a00074003044002c01e0f0241d0414000c581203007004804082614800303007405050b141075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 641347050 1250 641345800 641345819
    0xf011d060702040207060510090b0609010309141204060f2a050f0d1101060909020901180b030601092a082d0705070b01090c05071202010b1210150807 66
    0x164510941000d8104008001641c1e1840104034180c401e0000107074504044403d00307840b8010b50070181c0b4403464484120904c5c0d8130304098440c0d4540034032300422400c0852910845500340c0710305450040c46031001c103100d5a800d40380500182c0e0325030358441104080d00c0400300d030344810b44c07000034101440441c0e41a01a6500d11030154005000d8412640e048004180c1940381c41c403400b0320040041e8600b641044442c01c203010307240080ca030440090103003564540008035440c8040c23084403a243c810802d0000c1840700380d040000760320001030035501250380da940340b94040d00f13402540b1125030f503075450b0710f030764081c2d492107810000b0103142e42d8404030340d8800600406495580002c117241d9900c044104c2c0200709100e03d4070740b18139082e5131070544a400603d0041028801a00882140b909100c5007414044d0701205607480981c1041303410841041c0d4080030b0780101070000ea80c0350080c580c0003018800080c000707280140c50802480402150640804041c2040181d010304040b0350400c03082003000f8040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 641348300 1250 641347050 641347097
    0x180c0f0c1507090501021501030b130201180303020309090f13081b0a05070815011815081029090406050411060313050111091003111309020c06060f01 66
    0x10034904440800001211440040d4000c40e03101d800500f503c90103203c4c95a052100003445500313040607040c554195035501903000300040c0714400079a12817100001303580c4a0020380c00d91500d150b090740715041c0c4900b4029100d503c00403907107000c0c01c40c590200c0c800c0704008410b18842c088170418014240450360340d000c110b038400e0b0785020055041a406244071300c3d00307100e01061517108a0080c07580034501501d003804c10180f07028060b880c1506a00422020311107010038030080051000010320660406005060746a0540001e140c41c880c241d805c0702c071039010390f21221000e4030a22030b140e48068688101c0d549000320768806504014480f010400144982c1c1155410134445da40b030400034802e6202189d0726410480324584802c0c002c401150a01c0020311908000c2c10342000840d1420345180c0125078244104121801056513501e00c8444010f04401034031240110002d88003489561807010074040d402c42d040c13586103409840c02040f134500e80002c03141c600d038006031110b1141150104c8118150304 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 641349550 1250 641348300 641348317
    0x8090c0604140f012714040b10050d090b0702011e060f0e060607050d020a1202121c0605100905010e0603060d081b191103161802040906090b180c0f 65
    0x21504110030405032442c0284020440743c01c03150006140307446d843c51020085007400d58001c510b840c00c903040b01c0d102c04258040070701c0c46050203940d58080810040062006a20140c0421980d400303000d4030380e50641110085041c60031071542c618804080c41c1007110f099210307240e00e0b816110401c114421a0f00440c40e8002c0008007050308001007519018141404d484440c401030f000301c80c1c00b200700890801102e000396220701c010030394000c01c3c0310158200c0c40341090803c48014540310480c08034460b030300004042c00014001141e29070301c0c0000030748080b6003400f945010600c561600700081c00c0c10380c1620710038030008002512a8942d44c0f944c942da540a00d44400740b100b22102c6c8408c41ca0301c100540c010807094601ca20b10481d005007002c0d07034040414416181b20760846071600341880d020b13044c03800a030794030b1307448112030082c452441320004c4c4a960700c8002d0a034241074001550b01c04aa1107a040040290341451281404d90082e0442c0e10040790215402c4201307000c242c03032652400300500042c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 641350800 1250 641349550 641349557
    0x10e0c0f030703080403061d01110315031603050610240f020f03041d07080f06010503090a020904150501120f0f08071e0c08030906030f090c060301030308090c0604140f01 75
    0x190f100c0d15414125401500151039a40c0c60b010303568020782c20010f0803015003050300020840c01c1120759140314030344000381c0700085403100c0704e0101d9281c0e41c0c1401003228400d4105103124a841d90b0f440e1240c0c07240d50071204081d00d2002c400c000503e01800d5a50503900484072069500d1ba000410310075503611210300124400c5106800400415a900708000c001506c580f0484408401031014410200ca40052420080050030001e1201c2c09400100540d0003e02c2400c195480ea62140700741c1d03144c81300300b41000e035000b031300c4000f40400e1080c0f1081e071044440c0040414007090b81c83d04510960078542100c010b1240400d540e400300444d402c211980101441031000d1441d04c60b030707030b101c007d2100c42944201040021b10421001000006c00c0756400402d0300e14007450805c51000000340309400001c1100040441400010f4142401840034180c03480009040940785c0d42c407401c0c0109142c03012141402544691075064640345448015542141d94001c024000c13200014203100c6000030301414103051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 641352050 1250 641350800 641350813
    0x7080c1002120a03060e0124050a050702090604020d060b090306130209161701150e192601141008030f0703200709020a080c0c061b1c05010512010e0c0f03 68
    0x140046d42449500a007610041905030401281d0785c00310011210304508103000d4100000b140d4203801c9020348d0842c03a0120344075106991100b021801902c03441c1e0201088901d080c0002c1013004584003d801e0000c01581281d4865551200300701c6100034105003c2c0d2300841c1e0030300054000c440610100d0001b02145000303e50302c95030396401c0c585404282c102d001c0240030002030095155000381550748100049807034098405443c41c040890121502458070b0b69140300150b258403d0890b4916034009070384000030042420482a076080445096405a02a01440c00e00203068040081510540110000030615245540e5021707500562494000400420b03d0034416010001c1400340e040108a00700c0e000d6520728a840300100a5100107000d28002e80d400c0c040c02c562980c0009800f5800300d00c0780c071207264080080c1010b440b603010342103280c100e03912580d0340c0032207400322500868100c82c015107580e4004010901d04900703079405001007151541c1700c0d00c500401490000b859128041d0041c082d41c09 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 641353300 1250 641352050 641352059
    0x40b06091e010e09160e0c070c08060a05041505010b090f0120010e0d020a1a190e0109030923010806010c1502040f0b0408190303060b030907080c1002120a0306 70
    0x5072180c260f100c80c00e5410701c942000808003052040c44a800c0c41c0e000d6000310682010b6101012600190511041e024003081c02c10070004002003100c0a00b186000701c400503d854681000580710881b02180c80c85061149211540042e00405042c2e603214141641480720074800d00812010114110341040340b0245600d424400320151900060455400840c8040d03984041518180070300400b00110352010310a100407819040c00b031646d00034a080f00165544420400e05c00b400d0104682c9040d1615020700e0440e0f442c0305501002210f480303600e481c009159988441181c140d40305820700c8034120420100340c240d61080d01601d134030410504096500c12840d403640021404138000b07890755542d0029050042c0c4241e900381e8002410754010700c900e081d08021055031600c0034009820604880c040320201090b00a41015018040d080c032142c1e01d915200000d240c0d140c1d11841900664007503030007040d8441c104100c5c0080001d801c0d800504c3c0d14176003040451450361002d801d403410165074280104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 641354550 1250 641353300 641353351
    0x90e010b0f0d090b0f011208040b13150306050108010e071d030f120405040605100c030e0d060903081f0b0a1b0c120b01050303120a021c05070c0c0905040b0609 70
    0x1046140134120142007454181c000a95148042c2c111188144001ca00d180004c2c04501c11141502c603c8403501c0c1e03c4416800078548655403a0b08100c84000355810081010359059010904444e400d980d040b449907a035540001407040d003600c1850015680100810b2449542500c1100d40c000207001c543c0c252214072000350912203d0850700c0c1a4000c0001c0401c0286018010500988411907071113300f01000d410180042c0d15154004081c009044011203840e69902060f61003a45c01c03000a1220300c100b45030091100d0012070b0402680c400d00d4010031402035403c819001030729a121022844c000602d04242e03030082c4040c01e41c1e61028030083c10303240011700c403540701401842011b200b902d803007040e03180150b80e080c2c050b00064003950050081120021401461301c2d0082c14008006170b40b400755102c001c0d0000fa00040040380d460074981071104c0d60758400e51031a0b41ea4000c0d4141400291108410340503200141c4003d4083c82c440070210b2100c2c6850000340307420040e0701d45044080300c040c10180c0f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 641355800 1250 641354550 641354561
    0x60709050d081338032707030b01060507050d0206011a09060f070b22031b03170106020c030f0a0b0417070c15110a0c030b0c1c0501031101090e010b0f0d 67
    0x460f007041c81440c12420000784c03110826000c0104104a411440d18840c596000d4840450b0101204c0c400308848400c80b0042c0300c0d21000c1c68118003654215038548002030704503484550115600c1c03040b01d096490491001c0b88490588850f2034112000070031568180440f03403c00d0320642d0f8090010040c1c1101041c40c9402070805a104135a200c41a14002d041c41c415000f0348000c4030041c2210f03d80f0000000d5000841a401d00c020904903c1c0d106542d040c22070300950300002c8056481a41400400c0d40d03500000c2520003420210100c40321224209800c40c2c8600961800404011044002c6400a1204c090030003101080386561406c21320030385c4420400604a500c0b05411000622081c14103540c0245044c090714981401013034004915640e103803801c55a03110161002d0101d0022070f00d00005081201c62511410807000380d401e0140c0700c01c1009003401c0c4012a180030151190071807075406034951904071160710240350300680c600103450156500c0803160911484082200040400d07561180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 641357050 1250 641355800 641355839
    0xc0221120907030501060f1d1005040c020708010b0a050306040803090a1a0a0507093501020d05150a08151005090a0504111e040902030307120f02060709050d0813 71
    0xb42152491410280e08445054000e940030708800c84060012010f002c07031518901091030082c5006680d4603a10702ea010411b81c2095606c141060401c0e405e050340000d420b01900d0881c0c000300683e000c40010012101c03414401d45030503400010014000c102c0d42d1019545c0541040244c41c0c88506aa441405680c04501e80310780c00502d81080c0401e00c6030354814103900c04403a0030081c1d2041e007000c641e0f8880300d006c0001904450120261250903c0c0340004000c00750a011000390340320314175008000d020349400c942241051024061443c81803030803041080403100070801a2880c030341e222000d20f0445030010540c0b5940582d90340f000801d6118005072611916003440300041c14200f520303200052400d13035104240b04958030012140c0c965420540001e58090031500000c2c0100c40d480440c1c2180100b80010705140c0d0442444540d880e04111180000d000075400d4070180e5030b4070b40c401d44007104103000c0c20342c029000ca00020005071071038005141c0c01e081005004400c3d40e42d040c00c40d03840d0307020710b54 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 641358300 1250 641357050 641357053
    0x12102130f060507050d081b09040f1109010809010b01091a0705030409060e07020106030302032a0703060605091f0b1b120a020709180f0f0605010b1c0c02211209 71
    0x201300c07007402800e2014280c1a01e8a182004c0c807400e0100a001c403014400e080d5009207800055407c10340d44d40ca40c003290303010304071440a0080152500c450015900121070b490b01140c400030005409010601c03c104c180382c01610b840b20003504003e020704811400034803151203520108100404101e01304040e200170300401c00045116030500802001501c03014110805581c10407406000194000c02603c548010440003401030071801e40040c0d040c543c0b600d164041c540156a030210a220040e048401518029180c1248035150824400c44580c206100441075010200c82400103035420801080d801e4044186804a00840d4400d075092840c112010950102c2c0040c04600050f011711201004210300f10040100452003180400c0c00107200703c00038002c0004480b060308218064410468140c0c00c0a03041156684451005501e0761222a205954002c0d42c0e80d010708035005d50140c001901c0d0745a002d4481402c420358440e40d00204040d010010950501a0302110b0710f2103d0040c3c400c40e207c60 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 641359550 1250 641358300 641358307
    0x81c0902010311090a0911042414070b06041109190807060f05040e04032304030303110403051b0102010f11070c0b190e0102160e06040b012102130f0605 67
    0x80003408640d40390f400007020030002e02c10031103103646040840c022181d1402010a60b40701c0d03928520000d218603042110b41101e840113006404060954001c448055510b071010419205031041c8400e0041074001842c49031030100003a15400d045d00581e541510140101c5c0c1400740d80e000040540e000b0366000d00007803001c0c48080010758800c1051800500711800c109010701c10442c0c00400078492402044042e580030306c089010544650740142c8000c28110203040600c0580c000010a42c1c4144030a0300040e0806004c520394280da20111340032a50b100000348112003038400c1c580030403030350200e03228155540c4004500c424041c5009021032060b541c544a5038a1000345401003180c0304640002c1480a010700030110460207150481d071800d080c070305140000c60080300040703140c080401a00f0966800c02040001c0d10007080003c00d002e100211018482c1d0b500842c0115800c2d500d0800004d40900c0c0e180c5804400c0803e035004003a24020709188894440e1115810245009603610807400540b001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 641360800 1250 641359550 641359553
    0x180e09100b100203220506040b0a020c010518010f2a1703060d0b191424060d0905120301120506010602010608060f072001060614071707081c09 63
    0x10712800901c0d0360225200004244201c4009642c0d0040700e020f980507030b420710b41101019520724500c070010000185a550f899032213924002c503681103044420094400c1c010707403210f298000d0040e00c10501940900b16004c1411200449051000c1c40046051185480d81c0d105c0702940d200082c88046241401d40280201c0f916040d200c081c001d10740320100c44800d02c02e00c40990b40309074442103101c1d04000003043d203443d900c0010722100c20b0790710440202c03032402030745590314054080501c0c450001005641c00d03602c0000300504000001201403580708400700440e01d20303022290310514180b80280c0848151740b14014954140380d10a07000341c0c0da600141e03580c581c2046070030040305014003410f01c003e0140a1070111059030f03c0d40c02520100c40420b0300070009440621845a1951510442030048508403541d44014001c1c9000d00402c1e00044403403042500040526040f0382c241580580c2c0d00c500c00184101c1560960852141120141070800040b00c1443d18603440e2042490711180019500403607 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 641362050 1250 641360800 641360833
    0x1713020d080a0e040509100e0f0114040b07020a0302100e012909010512060a050a022512020c010c0215090a0603060807050904050a1b0b04060513080303010f0303180e09 74
    0x1601d000e0340706500b0042080304070b52020071f00706400d04144201003100d0b820b64000034102503103a01403203000c0d840c2101d15a84621400680c80c000c030300441d070501494a81c031104a0b283d0303c1c40500a0003680c032038001444a00c00720343c400910980803c00000302e044c404440f0f92070100c2d4014032200321980c0079220030220300d010122140100001c03540d0f09441c00000e40f0464480320018400e4000c1a03490340011100000e940440e403001100a800c00c0601d0014610008200003601055901c0210580301000d0a4000940c00314600303416100e15603102aa0b03401c019600340041e07000c802c05a0140403071003442c0c4622486802030500b0352008150542441c00d00d80c603107616640541d1040742c5100c00d0001241c00801c41c0004c41d6006a50502501c20443c0901d0840c8607540c84064901030002c1c000a409030310a01910300051100210841d16a56071201d03507880c0020b016103101105401030410003e80101c0350328060842511810110696440034401e0000c021600d070b448070f8001c0080780906a04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 641363300 1250 641362050 641362067
    0x3010c020102041e030506070f0509060703050a020d08060109030b2e080f060f070509221401052e030e06130209100f051e03030f130b0403031713020d080a 68
    0xb01d044d250b10059186440b06903031888040e01e03680500c20350f03e10100c01c8500c650102c170802c05000d00307016516041c80c40c00034031503407201046c00e0050040c03500703d800c003500c20f0001a020742c90581d0b8410b940c505540b155010880c01801c070b510307540c50f040c0c3c000d441045103903c2d41117564041c00c420038549290141c030a080402c00b800b8150b45821100810258003154500160060818074003244c586180d01d010600c24506501f403450590100b840e01e06850310700d50003680e91224021611000b03666a00184403110119044d940300b00c2554081e2096891a080180090b0a5592134041248504540182d050120035240566194608420682941000030305a0303001040441c0c00c808d468605505000c0d0302c41140900780c494691047c1c1c0300809814000c11041255000301500d40d44c460b00c10b58807109601c031030344100d81c009401b1400034a0b08a060251003c40350580c50751500c4141e00c1d8040c0200a40090179002200d10648142d80540c54014038204098401c5400035518260740c40007904001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 641364550 1250 641363300 641363339
    0x21008071404210204151e0b041206360201090b0c0709020d0207051b03460f12121503060c0309020913030e2b05070503010c02010204 59
    0x70400c01000802046900c9070300304802004000101001031001401034409000e00341e2007540307116404036101e0f1011051a46006400c50410107080c0e0b00d03110341009001d18030408030381c0149040700310046801c0d41c01000b21940b00c840d031068030980040c90b4074801e5005c0e42c00410120b50b11000b8908650300411081e004d40000d104071400e1845001025503210306c0c5004070700b4090740102e180c848208042d010390704000d0340941a20141e44244c610000e0400b041001c6038442e00c01c41d5140040324425414000c02050044c8107200d82c01d1004000311000f00000700c041403807410381c03202d05003c1b4810026000b40a0f104003102148001e110700000d010301c02c00c0080510b22480e200c3c119003902a600b8444048940c0080301160f414080c40f801d1300117140005002c1c1d004100c03942003250069107040000c1c603d9110703460341c09507031001106000943d85144580d0349602d0000410140c00c0c1c2280c80c906890611460440c0c04040e00c0700f012900352a00c4401c82409030b9008174003400700700101010480210f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 641365800 1250 641364550 641364587
    0x4021801030f0311012903010b04150e13020406060309050d0905130e010b04020f1903020f040e180f1b030d141b070608010801051311040c0c02100807 66
    0xa504545800c42c005941c184000e060021182901300320f15800e421419101000f41d03060070b20340d040703440a00c01120001800c0c0d44603518022a25030740d85054403e0083c85250900c0e1002414103001000d0200d030b1011340452400650740180c240180e840d0301905014200135540400d1603007071860210f10340080112404103101c6401014402038980a2400505000c0b00c0008201c020b09000454010300b4000c0f00a41c105000049015170281141c0041094590190007102d60a1000f41c0481c22401071803007064034a0401c21003048903012038030050f030b082a82c5101d41100c180310301e03401030b02e07201901c41d043c2402c1c2c01130684965840300e01e61019060b445c00768040c0c1201307120141c0c0200f00e940741400e44001c2d030304003246c103603099000420720114442c1c4540868a041c0e403112341c0640111024415607070300750300780400518003085201d040440c4640c400001c0c00600141810040074107070300703420081000907408028015903540c103581005141103840b1020141805100280b0955080c20320341443c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 641366906 1106 641365800 641365849
    0x5060702120f0f09030f011a04060524131203080f06030a020f040f0b190602070608070207121106070302100e0d0e1005090a08060402 59
    0x40426408584800211120a18080c8101807401d07405034024021440ca0000000240181c40380003401e5135080b04070611541e00711031100010b4103142d001351003420000c4c101841403074040c00c0150350813140d40002d42c400301e01100c0340003d0380c0507070344000a143c03d8100d03d482c1c110018003203815000002c6150b6042c01000e280e000d5074501691000c071004a140da11300080c1c070355000d56028202403000210002004020b2003070b000080e94030f50301c1d6600d00341d080d554210209945240f141c1c0442d04a824000000d1a004568120b9411b104004090209540d000160001142c004400802203021589442d06103c03460f083e8940e0001c0f4081664420181c000ca640382c0b0213800d0300c004101c14189402620341d9400c005d002d80001c5110518001114204869031040d0440380341003091401580e940858024400d80d40302c0c0c51250014020b11003103207000d002e00544056240c80c0d5008 = true := by decide +kernel

theorem cover : BRFrame.Cov 641187050 641366906 := by
  have h0 := BRFrame.cov_init 641187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 641187050 ≤ n) (h2 : n < 641366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
