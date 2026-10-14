-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1520
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:22:57.447197+00:00
-- url     : https://prove2.me/submissions/b7c8a367-e3ef-4997-bcae-adf3dc4ed368

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 273201438 ≤ n < 273381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 273202688 1250 273201438 273201463
    0xf0a12080405030d0c150b0102241906030c060311070206161a0108150402030c030d12110f0405060c0709050705040e15030a021912060212090c010f0507030c0203 71
    0x1030790707554184001d042c2000c0c514141c0c1014404507011100c001034140c54004003c10b80228001200010940103e091180b6035443d882400c609034024114882e2000c0d480d4041c0d449002340d510002810201030043d21003a01c809400318903802420003210340240c00c8000e1403c50b030106103280c51299400140a80c00c0101100305001c40c0e10110780810025160403072244d5280d4107194215850080c00540d00c00c98800941102c890305030102c0d045403803c1041440301203008007595001c951540d0000d0210202c0c0840741011401c1000d100b4a1100800880d414001000c1c1494a06410002840b0b82a0b02803000c600303041c8640c00c400a0300c1c000e28402c0c02d00030701c05641d42c00d9a0700e1a01101d8681c1d064081e000d59941d11801100012542c1c001590100503603054411908000348005e11080e42c0c441d550041c20000c4542c1c482104100b1240d000700815004021603001c55150412080d65500f00080202d01260750800d40d240030030700840180417034500c00e1814204110b91503011078200040c92018 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 273203938 1250 273202688 273202703
    0x20402040f050103140906180a02030d08190e1b12010507020105190e07030308070c06020a1e020c0306010b09061314010e12030706020d0e03071209090204050604050f0a12 75
    0x40c8265a4135000310325146100c09425085418410b03807450b245c1101a2a8007000809020318500e210024000f1200a0b5001030a407140c0402c5084090082442143c2c0c1c504105501d6408c051500d4051003159010915000103000e2114540e15508002040d07500f09548102c0480c146901240c1c240a0302d4868070460740049158140010b14007032680c40d21580c089800c0c1040e08113070300c5220009101307085039014600210300da21410f0081c4e0b002d090071400a0002070000a03d4141907070410351104a2940401c00d505204402c614200d8407845403045859164000c1c3c001007014a410402400340501e000305203510304030044803289418650340d401000c0204050b00041c07510340e088010043c403480c003518030060410308464000d80340c0c8181c1000901c415408a20582850b00d0340c0c0c4010740102001007102d50313400d0315080601803800401c48144c000765051001107030498050003900e0844a002c0c100906150a100400c00680511100c80d030300a1009800095031680b1624441200e0380504203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 273205188 1250 273203938 273203969
    0x7061202250b070e060d0504020409051b18041505040204020d0608010b1c0b040308150a0803031006020d05040302041d190507050306061f0c050f15090c06070311070302040204 77
    0xd020b454040c0040003c418040c0d140d480300e4441d00c55100711500000c83c09000521640c0d04e100180007404a010040c01d24440d81d41203c004200302c034900400d900040f1450800e08495003009a44c00c80100c400400320000090000007511081d00000e420910046c0050b0810199140301c004132000c0d94401720380e0780c4d110100500c90782400c404007801080413246500c9004610707122403c00307000151005003003007100c4000030300c0042d201200381080000202a904080d6503030600b6641d0b41c10603240610300140701d5100182d564000100c11a0300d01c05512a0303400d05280d0303001c00005159041c8035903e500b4030030742e0b81c01441c2400c1c04200900000c00000502d400010301780140307008099048203000341e100d00d0a02116540c0c01d5a000515205900ca0001c0b20b410000220b4100c030140c00024098882c2149234510703001e01103a10ae0403800783d01e11a00155451502c060b07582c10110b08195003201d020421140820f04c10904500015151011500081c1c0da03540442d08a030b029234801310411035201d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 273206438 1250 273205188 273205193
    0x1205040309350f0a030804060b03060106050405030115031e080d1407020709090206040b25061b0810050118080a0f150213180f0e030705010b01020f0706120225 70
    0x15100403100c040742d40105440060401c0c2503035103c08528000d42030052000001e0f0801c07105070081c01007404064240c80855940e0600a00b840d0040c1c020705103c0d500303044d0300c00b28001c80e034511601200d402800c203040701c20710100300c092165108501920042c03030400044d00c402c803850260145510803a003001c1d84524110074000d00b411201e811075140107050480300805030b0348440540c3c1c252695002c2141d80c400c3c00b241d1400310343e82015504e04001410b102450300348809980502c040c4615040368000c840c001410480e9814411110460320515401c4140312030b5120b00044250310807107a01006185485016862804501541c111450320b81c4404080c03c20044103d0783c0502c051243c02036050881070088020440840d008a11003040d202e6020102d0822607080201e545200301e404229494140c1c9505031680d101c1075060700c13150b00300207540b005540300040b40151880c0c100040c119aa003009812528003809051030200c060f028031007800d2241c144406400380761580104c0340340303e60151 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 273207688 1250 273206438 273206519
    0x2100501080601080601050a06020d030c0c060905060712020406051e0c0718060e0f0412120c0504080c090603030a030b01030902100c0b01050105040b0714070b040e040b0a09031205040309 82
    0x5807c1180540300c040420440c1d5900064844000780032401c1c0460344204c241c00441d1a48001c0b10041c150381e003807000c6901031000200e61207004506a035544041d28510080300c1d0203030302c80c4d03100e1040024410050f0720181c20010b8506120500311300d5030945403542c2504010302d00640e41c4c000c1544440c0c41484080d00c15820f2080000034a50a20b801c0b07190300d41850300d12280040240041d0092400301d081903281e40c401c0c01b21440781070904070300b0450081c03055001480f5801901800d031640c41140c050a181c1c1c80c00715407640c851070000f40198584803d42d44224054040c1f50080750505807603203039000040c5c5da090581c1d0f034595255520001c21491a0900105014040c0d0000c1e05002c0108002c0c0201c034072090481d0059608040c0b1000350a150110040c60156150301c20071076800b01040104144242450060099002e110070441c107464610301c1340112610f00380001c022407000704c6062131800a079080268424002d0511b00701055454502c1c040d86080c801c2c0c0c50b8072401011526078002e641c1d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 273208938 1250 273207688 273207691
    0xf0607030b0a0e06030709020c070611070b1c110d1a0a051c110907200c0906090a090204050708100f0302031002090d1203050402040f020325021005010806010806 71
    0x5240070302601c0141408610503100740d0085103078a80008000540e942c0301000310300024104031400b1550b683c01449495100c10350303409400002044142e118a8044001071450107407090346418500c1c0c0030416440418410000300020200341e111007082c9042500503029003a20030350100e010410001800d031016910151145092243d000c58401b40010b03110b400d000300710759038181c030110340d091600d09002c249540801da003030394019002c500b0400c10551103001007203800c450301c044221030000c110581e502e03118865030480c1c10000f50000038425162581039683c000c403101c1400100351006030085000d4502c1169410089607000c030031f12a11040c0391100c0001400501caa5540050443c0e0000b5210b0301040400a920358004c0346100c000d50f0b400102402856109052100e80716900c00c000e0084c0000325030503403155180c084403000140040c02100d02c40c0d0203289081740e003d4101540d07207210791586c0c61070f2000c52081b05800d10034080281f0034140a0090b801c000c16466151581c0c8510b0a00d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 273210188 1250 273208938 273208951
    0x406090309120c0308161e03090b0c030a0c030908010212090c0105211e1609090c1b0c0f0b0403051213140121020c0c0a1a0904020d0e0f06 61
    0x1212034100114a8001c01d403c26280e10030b5003141d480304020480311500024100241c44c0351210551140c040405c030920b824018801d446041503550380790010201b50144542141258104100c3c42110720700c14403c890520740300342400d03c8015100c9404a00b280c00407100d10303a240c1550401d004140a0800c4404000102403804a1804941c00022000b09102c0c10048905240020101e82007010088965608a03045680061075142104400e0b200394207141b0300301c0100707940c42d00200b1000d15900a101d20741100c1c4e1a8030101540d6141c0c01d05900007070300d4042e05e108054040c0070a02c40b05080003e070051000d00161a10740d415418801c0c24000700040508510b2000c005140c550000d90300c086080301c02c17988824814280c8400181e8414003902d5143d059101c95a100e003511551940c0a850805241811034011321024020711882244a0161643d1003058140041d80558244001c0081c4d060107440541000300c01d4413007005070b0700203844980d8070703401c15803031400791403410048950b000e01c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 273211438 1250 273210188 273210209
    0x110301171b0a09020d021213060c090e0f07090f1e09050f0621120307020615060d0e010e0f06190b0a051c0212010b12161e0e0406090309 60
    0x150101c000408a00840c0720b107a02031500440c010901032032680c159015507240c1200c03003641d481c5c503240c1c1242c07099064800700d07089442c0460000215105165400580c1c440b00700d0010262943c07103590500703201c0200400c003000240a0041126080091340b00b0040500c1071740c1007010311010074003000200d800d40003c1c10a6103014100001410900b079141d8000c2030584800310407200c169480d900d4101181140340c60f03441000c20354042c2c1c2078110011032190b0480e509441c0e164480e9080034215885c48684298801c0003400360380f07270042c003952003070070604c5400c800012400803103030300141448034554190a0a03004001044281880c040703048407401300d02901003041d0403604000403400174080c014140106c04984945403001d9000304000501070700204194251102c880c00d10340a0078071074030840d000d42a5000340055424000076105e01e0701c0d118003640c880305414a8450041016110f81c0003081c2c0f01d041e0f074000765411202e00140d01503802610042514103850034054000a0503501040c03002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 273212688 1250 273211438 273211483
    0x2e051203090904020d080d020f04030c120b07050c15010b070b0105091003080304061e060302100e0108060d02150d020c0601060c081603030605041d0c0105070f08090411030117 77
    0x95850b500c0603a8029812035201e22403007210305102000d401201b0303600103c588005000c500d00010b91000d40708480c898100035580603210010f1026000688000500b43da500f00040380303000d4022006031a90102035401c0b40d042c1904520a510062020b0340182c0f00030703a0028a50003070054011596000d010103031650341080c20a007800712151b181c6c610001e06418000700101c0d040103c0340c0c01502c14100e0800c4582c0c1d83c100340c009020002d144e1840201e108603061104001c46034011038030811100350584810b0040d5031040140104010402c1040b0ba00000780f02d500003008907100c010b01480c0d840914010323180c00440310090700d4580c0607081003051281d030f0002c0d240001c0c41e0b0022100c100c080c441d58a92040104e103801d0b0b0180520742c102c0c83d4850b003000710b1400c0300a416411400004d05503011102544504401507629114006000d08024455000b12002c02d4030300004207110710019100180181c0b0007400c140d2603409c281c01584144006000c3c1c010040ca08104920320b54a01010301c4001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 273213938 1250 273212688 273212707
    0xf0702040b040b01090911041502010c0e01022103100302061303060c1e21021b0c0a0510110f0105070f1205010b030a1104030206040303030c1403040b0703052e051203 73
    0x282c245c9100e1030081c0c2c0d44481e4000801c0090f02c007a10003c00041c3c11443e4100000200680a082c02d001060000f0b9000200003049620018102c4407a6002c03075080305128100e00c9410b1b101c5d0b400100302507200c403242a00000141c6851004080e4151151030b2030b0042c40c21850003209540c4a00100400c010040c01c451006101e40c0100307450203401ca01741200b0b0700d00420500a2b03210003080061004500c0490342b40c1c4848644040c080628006006944081c0d81d100200102a10360340181500b221456108106e070030300402020b54800c408200301c6081c3e07541142101c2c00c0d41c00848040002915102c1490076298018085810700e01004200b4001e035030414070081114003001f0a610b03602d1340c0710301810103240004011140616009044143d4494072410094060040009003000080542000c881ea4607583c1c01501d014540c401e0ba00030307803512112001c40103040041e00200b90014420421306115054030894126492849203005d205440c0404000f890007006480028a40040000b41d07030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 273215188 1250 273213938 273213947
    0x90b0702071409130507030309090c141902120f1213020310050606160c050108061903060b040b030d02100510060219141902030d0c120809030d020f0702040b040b01 72
    0x201035510207944e82e221003031161100141c1c40040c0c12405a82c00106c00c2c181d2007050401901c0343d044c824001000b0f500d40494410025814400c5104003e10900003c43c0c8040000c5102c102c0d148102c030005031103002030003003683c800c040709119180300040400100404100c9541d0010b9a600c0e10302c40b034460394012a443d61541008100425a5240000c0b04c40d17075403005903902d00824101c12102c1003200c0c907094001064601030640420410300c0080c4440c546100201d07861a402c12501c0e41507442c60303403100064815080f03550b604c41c4e102c560302449a1420046081c403000e0550051150002d440302c11011240301815212a5072503203802840550380005041c40302a180b00c8021001014508052075008a07419010f80c0c58001ea40780d80c03003e401820710050280d4000c6065074800352000e903048c3c403610340458000b81308070855114042c03210300582c1d07400d500c0104001641d19119084400390b04903071054207490380404021800d03005505041c49490394014094804200000f0070400207030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 273216438 1250 273215188 273215219
    0x30a0c02040f0c080f22050c030609060c07033f050a0e15090102070b100807050103140112020102010e03160c09020a020a02061606050f09010c02010b0f010e0a05090109090b070207 79
    0x848074016000c075860550100000341301c2c4000c0e010840c030203046850301c0c5884142072808e051080c4211000300b20243e40c0421124000c12100109034a48082d59409541500e011481c4008440008034800c110001c1c46110070300007030704000296546000c0031011000c54001400040b0344038913025000203400d00c002603c172010900d04403440484c3c0d0350041803074068880c0110042c4044050b0b801d00a500038203030910b0013515010003c1c0d80405480c2c6c401141141c00700d2203151044600000104040145a080d00c80324600610011420a40e24030401c0e285074400c8602026145412180d54140000c4903103003000b602d01018150f14010407604000d5462107403a601911030381c0c0000e45d084552041e45915007159a1012091246150012010900c0034086400c800300d0350800001000385441031054011f41c503001008002c4844650004564080f0101d03c407540003103800002045070350340d15515500806050ba40429100c05a16145a103007101910700010355100b01401e0140042c1e006019 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 273217688 1250 273216438 273216451
    0xb09011a0409110a1502070b0a0f0e0303090d050d020c06210c0d060306050a0c022a011112040602070e010609030b130f030f0318020a05040914030a0c02040f0c08 71
    0x2c10301c0202c50808007083c40180d03104940c0424540c07030014910740b0034002c1588400383ca4081e034032103694412100d401442a0300c1c004002036807800c528440b0b0740c0511003241c40288064103c3e41403840040c00b290f944a00800c0a80da1907101000c848002c65040245501d2444250b0b1002d050826400642c1c4075040000011100824640300141d0350078482820340b0494802590f043c0501c59072030500318001c0000760b4400c450f0764201001d440c2010300006140440c0843c003c180140800320760a590403c1601444042c10030080600c0c03c9c2200100300001d0311031418030055541d9507442c2050113440c0019540c083c0b0100c1500b400100322240e0403076261422a6000007800340c59a80300c0e10a0040400c0d10103008143d070002d82140c1d41450703407004206c5100c0c80152010080507600e1240654641101d5000035804115404280300d1418150880000588100030b5908021081d18000342160402c40102c40007901901e0443d0030351500340541e52042c5c581d60000c00c05108050402030191800503c203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 273218938 1250 273217688 273217691
    0x723040602070e070e0607030804020f061602040902120a140706081b0a0201022b060509130809040204120f120f090306020c07030203030f040801060e07020319090e070801030b09011a04 81
    0x150744d05000f101a040c005000500d100d075034a0003440c01500ca40000d03113040e801208040c009084604000c42141c039400d564004512400449600704009004954000c0340c100c041a01d05100c001c108118201e9101e2040da04407103030f1060800d1491034070300c41d0b9007d8010000c03454140001001031180e10000860700c040c076507949110300d04080e0b019219200c00694241a043d000421031001080070040c0c0d000340340800d1180d00d40d980b0800c1030121059501d400301c54030b00d4000307500003014000140b15007034000c0c8c00541419035400c01c0050301d51080700c0c296900691001044100806c17160007803d002954101039061107645080106002c1050000921055000881c0d64154404214140040d60700030112582c4510342985c2c01000c4c0c000e0b00c64a0001d40c2041000300d204908100c00501c1020359600441c02e0645011100810b0090941e2040a01c02c06040c081100620031514501c60b010341c0e29000d0380d0354514135050f0a4032100904640c1030764074041898011081e1400e544c881c03003500701e80 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 273220188 1250 273218938 273218941
    0x306060a0e0c0c1218010201140703091e060c12060608010b07050a0606060e03070f030f020609130f05040b0609090c09090709020301080a050c241c050723040602070e 73
    0x1840c0d0344520891920043e0381c452061209142d10001e0000c007400481c20056400c010351000059080c1d80d001d034600290034003030310000340070790748640c1c8562042c50244841e401c0000001d601c655a1042c00c82c0e0030354286840780110754440d5000481076501c101c1c40072003040701902e04000240500c81c10b00442e0305a000016480f403d10a08101c2d4620f41c2d07800007400c000c66030f50342d1006000a0403562003070703000e401284d4000419038200c00d0400102c0e90065041039403500745034200100c5500949a49900c07422107140182d46900780d12416402c64000341000905007802e042421052000515551103442200c04100424101182c0110300410546424803103440d6141078a0504e8011f0704503440716072000c8000215040c0029043c2403442c000c0c01a41e03007003400c3c1d400740160a40704548041c41094004180c22410840400601e50500351000340700c0d40c2180460180c0548400352080d400054600c800241c1140e000d00d61088009000d0070000c0c44c0a140041c003948a540b02c0c402c14100f01c21120 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 273221438 1250 273220188 273220201
    0x80c0a14070b0f060307060507200109080607050d0510060c03110106050d0f02090703020a05040b090d0b0a020c1b100e03011b0504030b0106210509120d0f0b0306060a0e 74
    0x1415610400d40c00141003002d850400010f914450040b00d41501c284110940011064024012030348099000005a141d140e00c0f00c2304640084800b820742d42c10003030745410008500310f0511180d80203501a07581e050b80c0d50466091031081e40d40242000c079401280711002c2102036000b85402206c3c1d1b6040c2001019038140d001c0c018014079086d80301c1900804400001c9081060320403012554a00c200e40f0800390b500c403240c0840881c0520743c00781c0c002c0303101003106009100822000d0854160010003c41c102c0703002d642c8002c05000151070413011381d5004995020000f0052048030080400301021000000b45107000514000c1007801c010103000955020a00343c0c0ca0a4001c4000d1000680501203005900180148203622130f12043d00d41207464400030a90620415203296004420340c40010750b090625a050010980a0040055032158101c51490001b8080107403110304800740c40001c0c082130040c403142c1915408402e15100340c02001c204005540e07405c409605803080007441c880199101b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 273222688 1250 273221438 273221477
    0x100309050303100513091109100b18010e03010b011b02040902060415020f0604050607030c12050910060b070816140a05030a09050f15091912030f080c0a 67
    0x10802a040d404000100302c0e400d5108540081142c0c8141c0c1d03c1010103c51485240c00c07249010f20040c0b504150710440035035898281141307600031404c0b41d0b806039100d13542c1c45040160340c01182d601900c0417507000ca41e01c0c25038100d181c07060038000c142c000740200500440003c058805408003006200750610644040d91269444581c01790ba01a18281d540d64541e1180c41c0c103c110004004014400c400510101400125965002c0c50b4080000e12450b1101da400340c000d001114032135000c1001a400d002000031480c01594043d81c1c0c000042e14142c0d598248200c155080e6400c440c0100d90200241800a659a42198822240359074207020000003407070045903409071140899294480c0e01e039a0300901070040014070349031089845609210b40e4400a200b0465202140c60707034000d5404100c10b21682c54803000785500320000340b200d5400210244c080a00b0b0280c0c0d00442c007100d03000389002080503000320002d0002052030a03d2800d43c51300c1500030400d032080c0c00d148802c01070141040318282122 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 273223938 1250 273222688 273222701
    0x1030c0212030405010504020415240c0203011802040c050c0a02060a0e09011d0a05070e0d020a050d06050a050702120a030b06120906090c0906030a03030b0307051008091c0801051003 80
    0xc050659903a080c0b40c103004c1d01801d41074600b60721580ca4451041105516040510f0842d00307084601040024017100c44140ca02c42c656064040c09401496000180e03020301c5140c00d141207060048490802a0040c030080b00c00401824003400320400c800200500009100d05000340d04075201031f031301e41007071200701c90320041c43c140140c02042a40000c038001901400c40364880c3c550207000c9034141da810000c50240c840c19100313040400c0c0000c00d0441c2a040100d521318000e8000380c24080c1c1a80e8690103d802e41a10031070a0b10040d0345d48050101c105060300943e03410078601e10041c8903008001701400301c28840c0c103032000e0506030354000318021502d8846c1a1807a007500403003030300000d141168135603450790012100d480450290042034a01407410040240c069031018009002d41c0140f541c0c1500140141c410f03441d0315204a40002172203130f03503600961146440640d20a813450800e84210307843c0ca403094080066100070307451400300c03040c1d100481c1030460780210340c0100d01c1c8031611000e8004005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 273225188 1250 273223938 273223963
    0x30b0f0c2a01020d0e0a1505070503061903020907031e09020603130501060f171005070519030225030807050307050d0216150614060408030d020a1214040c080d080601030c02 76
    0xd00f0000d0011440201c0d01c0b404890080d03400d47c810300c08003508801101d00444040300459800c0c004544542031224015000ba4807010062920a8481e00040c901400450740ca0300000d84401f41aa00d083d151805a000603441c20f60502218003190700142e02400020300000c0d40c40d02a07045107050020940104004002c0c007845800844e442d000110220212001c00e09068031481c08201d1035460b0b00d100c0c16118064a42d1180d0501c008401c40311814900f0f02c00b86010142c0a10901c02e075401038102c20701140100d1106244000324070700d406000309100402d1501400ba00707004100c2c0ca690080100d54100a2003070006039903035488020400f4032030100c140a0b14120904070070400109842d44404181c882c107000464481115034100a014070950044507a1900b0a01140301244000c1d0064010b444ca1421302c501162890458070007141c2d0078031101d4000212070030601c000c0c010700c841c00320b014103140d50103401030030000c030130203402c1940c09040a4105170759801c900410b50310a01011140c540d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 273226438 1250 273225188 273225191
    0x213060605031b28030b03060c041703030f04030e0d0b070c0507081b0409060b0d0b060a05060901052b14090105250f0e0901030b0f0c2a01020d 63
    0x646a40e002070182d0400c54110803030500100b58403012800c68429101411614141c0c0000441d424929044000000039000d0038191a01304400050b601807001e948541000c0d06015156807411004e2031050a0440349030407550000c0052190380d0f404a8422540f10303402d81801117614501102144c030000354611702401d550040d030140090a6800340d20190b04a00400441c0d540ca9298181107494550541305120a40c030700c44c0b000c916505003a00881016030140c400041e040c50254081410f04001034001c4952a00c82e00410480b440c01038600c002800381070741c4e0281021034000001c1c12038801c4240e000e209280800c1d29800c806801404515520401c0c0000c1c00110711110010202140c2a5074511003035080200060f10b4141b5002c0186400e5160009144c91080c1100181e4155841030444010449108041031542d00c03900303000d038002c511071041d0b180689009411488444000b810103251060204004c0b41c00cbd004480d150011741c05014515940200a110300c1c600901c07400a9401030305 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 273227688 1250 273226438 273226451
    0x17191506030308040b0105190e090f010501060f030509070e040206030613020c07090b0907050406200106060909150510030e150a091b0602120c1608030912010902030c04090213 77
    0x558020043c600441c8a590b10158903602d40080256207005044a2900301e40380c01810091101881401c80d000190402600c1c0c10b2045846014250381003600400302240c4403a40b55489150302d4402c499014480d140580003543c201031204158010140010341300f40720100210340103030303202e4141005030700c0340010466450102c420f0480e21540c5512455168a16011540ca003508100340814410100d03660f505141c1801d041082c1ea4004070003c00c01421031042e9035450900400f4403504020f0030f4140c44002d8098a03000350760701516594241000f8101b140641040716895000032070040001131300303012801140d401010345c54040741d1000903081d10021014441d8500070340d031140c04418000d550310711460003080c0084214048038031920300180c1c46051101c0c0d803c1c581101506440d89410161030350444105408502ea0030316070004041e40e00009501001031407da218460140050340003030083d440207400190b25460b01000060049031104000d108640d61f4010001d02c0c90b0500c00104040d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 273228938 1250 273227688 273227693
    0x903050c011a1504350d020a3e22060e1b030103170403021e010f1427030607120b0d050a0f0c0b0a0503101719150603 52
    0x102c40a1408040c040c01c50b55000e074046905403000c880540e400340311819000c1500020208a00560f00c03d1144c89008a81038409445803c0c0704000c151313449a402044440e0441c00c7c4282444002e4404034110001e42409982100303a07009090414904c0500c0300c41031f81202c20104203250300700700608004a45c41d031000e00ba2140303c0e5000714107640111140e074000b03540303100c901400c54035080c0008a19910a100400c001008010b400c0d02c0c0710088405641020b0362a4042240e40780040b4580710008a20309581105592141912147c2ca6282c600342e10b1200902d0760104c05d5228031034000900c10403520721142000b510210704c0750403e00c089e0882704030b4500860001c014074085001e080748181048071445680c507040001d06005078001002d00040d60740d65403604180b2018100c116400d64003850001210081c11018200c1c41d41c20340c41c4d559a03440c03c0440c0201504554011b0143c0c201d0140c0421001e0800151180e40e03030312a1500d0321380180c22402e21000340e828420b82c03400c0c594100300d004400c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 273230188 1250 273228938 273228971
    0x6021f0f1503120206072309060a02030904050c0f0d0e010e120d0f11040501080604090507141804050c06030709090603080703030e010b030606010309032f1b090a0903050c01 76
    0x84a029000424003c440180c00700e84a14040d1188000608451500011107000030000c44c0000101c42c03100c2e01c3c2c00031040c041010390304030071129030151b0000302d128052410f090003810f0b4003000308000e5038984000c4400301c01250183c0759103c400150b94080102c02088251f0241c3c1c40c031081d0074110340c08000081400c5489601c102054480c503170a12148081c1e0706d403a8050007050a81e10b960481c02c2a081200464031804011f10700d6038441c0d00c0d445400b0100e9030512030100a440c0e04465000101840818017681c0d109005030500030030035000c100800f140020409400248007102c046a50391180c02c0c08030340e026244d810043d402031a225000040011003401005094820345040c4003001c0c00118031401c81c0c1000900071b806411400001e60030758420f07072020107054070a0034407182c02c01c7c52442500d854030b840460300351005000c8580304184070040041d440b80501d41c04d04034010b5003101000c0349164034040e190040365603c404d80c440425010b041a99030301401c0b0f00003000108109a407551 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 273231438 1250 273230188 273230231
    0x212040f06020d020601050d060b030c130204090c050304260f031f081507050306150705062211010e0a1d01031514060d0f0210020d0305010f06021f0f 66
    0x7015200340c00c0c0d40c0c500c40e800132032560b0481d0300043c02c4030650105501d40c440074140d2101000da1501801031808000da5400c00440d42c6019011001a1280d0801c040f400844242840c240d007800014010080051000b0700c100200a100c41c0340c103c80c0d081407005c0c9041d58003d08040f840250008001c0160400c48800000c184138041040001e1107036403690415201c81100c011019a000d4580010720003500410045d030700000042d0002410241c2003143c5400394000c041d040342d00350007103000e100c0364408403090030300c0801c0341d00d01c2122510265680e4051403280103483d9414006000907000c0380b41c1c0c560154034002c04a01d0b1128610114048404501400901088503104000584940000c0b070303e1042006040c0c0c65400300e901915040101f20003103841e8181210519020085440180c8602103851030500b0b054009003021604202e002d0300741e6005030004890b00218560402060341d001844480084808200724030032602c221540340036000c848200038401e0306150200d50422500880c80c07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 273232688 1250 273231438 273231449
    0x31302010305130807110f1201020304170f0d0f0b100215070216060c06020408190303050108010513030c0c0e1f170303010b0c07031505150d120f0212040f 68
    0x400069885143c00ca90882c21103070058076186090040c0c400003480d2280355032000e64000e02900040c4584000a01000511221030300180d401005000402800d0b2202c542c1411200c1482ca0a01042070b242480c1805608031403100e0540b1810095018030722030340249151500601048800014204043c3d640e8000041341a00c0404910005003454408607010300d81c2c0040008a18410380761000072103410442c0502a2000c6034208000666420304028204107003404954104008485040c05012164143d000d0a030302e905010802c40035031000f40710180742550504103101c941d0a01c0c00e0201070210647c0000046401803000d11201d01180c00590b41400003204161251645a843e089000040034001a0f0913500a10040c0b00480c40c7d40050080107070004100d0b0700003a6691100d20740c180b080c0021101c84d56071101400b82075128000509000c010a40c4c2520248006035544007d015108210204108082c208400c1c2d05200f801805d240151520f40c154550f40c030760700c041e8030548640c07154 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 273233938 1250 273232688 273232691
    0x3270904061a0f030706030e121909120201020709020f090d060e0d0309020a03020d030203070b16120b0a0501050d0e011e15060e060a030e010509010606020d1404051201020f0313020103 81
    0x2c0c1e035050324004281c040c0f034100150182003170700e20307021007980681000b40740c070215400b03031a520840405a50002d48600c0c414914411031004c400c44024204a29580000c04101c0300e814000c000350b41c0005800f4201d8022000040e40c803800b041000740c070b1740120010160b2088484903490b050209540001e0900b0b03280f8010b94450b02201442a0708491840c0e070000c0d08483c1d10340040016261441000034514080e00543e171911340b40396200d0200d2001141d603c156014020592007500703601803800303200360b1230340081084100180c4000030068030701c5105003070402200040315020b24205e0303080101c0b0780301044020b102085002c2c46034800c1d0001d0f12604c40c845450405080d228542004081c011180c1903140e0104c1c05510406210880d80040d4524040c5a00c402d4003400b0781b4024810103108034101030000504a04200c0006d0400007295125000c12a4002c0c041000400410858040300ca0403201003881c4840300b40d40368003a00824080e902a800e004c01081100d0120f4941d14540034400d0380d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 273235188 1250 273233938 273233981
    0xa0b1201090b0d0506130615060305010602330601021c050322030807050d02070b070807081b1b0109020409030519080f040308090c031014180327090406 67
    0xd01c29590f1200101625950180d4080b80414082c0003245030204e0107600080307000d600110003012000000d40c051070001c1d0b42c071001040182d0341030162014440c1d138a810000c01054501d080d844038200c2c0c8083e8003d0641110110355203070f00800940c40d041c2d0030a6500c3d10b44225442c1c0250150f0000c07500342c01000c0101c03580c5114010000c0144e80e0300d95250310750160584480000301c07010b400034034244c0601982008a4004218a00d03103103441340c01c081c0c2c0d907500b0343e242103040200b400ca0040c107441e1407079080c0d009400d03000e00d001e41a00c50f0600c117203842c1005c00d045000d805025103610b50020b03400501e801555014982d1250042c0024240c81c0f044030380030803201c1e40440d80381204961080302c003003000d404580064414040180c020310076908403000035a92400007824500c41c11200104a5541c07c0c0c0f48104c0004034806660003040032400842540300741c100580c4a12800800c0d00c0000000c00301c2c2000c042c0d08001816110700c015008030480e140a20f000c41c01441031140001c01e820103403a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 273236438 1250 273235188 273235211
    0x10b011404051f03061a04050103291203040308030a060302120604050a02041a1003020c0d02010e1c1407060204180510171504060c0806010503010602060f060a0b120109 74
    0x4045034100c860140c490110758003503443c0d050750b5110f1450044200340e10755100096150581d82254510340400c1203040e911890800090110f0b00f900036001420100d82c2c400f403c29070a4400745e082c0250044c2c4030f4568003200743ca03403541544603981006214440120600c048400c0320791024064a2003034500d100145807140c11555181d0049800a200f81d0101d10b002005046c940c009907044516501000c980006a80001d0400040c804025000a80c0444d0302c01d180102080b041c081da00c0c160000304148000c00c03a071680c4820307000c00c4502c0001d44045420b0a0640b0503c00348c140340d0403150045480d9403140c41d100e4081e50003441800d650311500d841c941205242031081e58080c1c82000070300c000302031500c0c0f01d40018610340204a003090203498400c04c00f214080514600c110b200d910005101034040501800440020f00300504000303080c80140016500000d000d50050400d40c0c01d881d143d0740d22400550307401d100c4d400103850450b0202d9414042d17940e9880300c0d410b90307030801002e0100804c2003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 273237688 1250 273236438 273236477
    0x18170c030303040804090f060504230c040e06040b0d0c03050303010e010603060605191e050702030601060903081b0705060c3004050108270a03020606010f2f010e010b01 74
    0xc3d103025101840810080001c102960b002c5d80c07640c4442d18011130710300e075100c0024046401860724880c400384011141614510300300c140d543c1c8984041d59890400c0d0078030060001e95503004100e60b0040c0d40c2c0380741ca900f03c1ea03201c6102e0100070384d00940618019480746800b940707070f400078400c1b0311041e03001c28000300d51607000c0c0c0514001e98125036101401c005000c1d9005016001603103501052044000c07020702c03680c10310f00c0221030102003074840569914003803050601d0303d081640508200032404400b070001815803402c13103441080101c400406a8084810355003041065440260300010004110b0500030b0081008400c64403640c0091401801c0c2c2c00c078080d40c0d00404c208039500020104030501c000d41c09414481c0c0c205102c3c0b20751000102103c001000040e04003071700840a03902c00c2d003441007010390401105031710802c00c0c41c20051800c2c40361000f41c030a80c020251201c54900c0741d0f0582d40300c5500c4140c80c0044a01c503400078400b03102d00d000b816000301160b0304514005080c44011030005100d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 273238938 1250 273237688 273237691
    0x250503071209061718030310030309090b030d120f09030e040b010305040203030f0c03160305040e090a0b06040e03070b040b15060313031812080406030b0409150b0118170c030303 78
    0x130f448001c04200038030702c003038044440107150401180d290703c07a003e80706204102542c4189004d4803a0307002075045090150845c80c559102d04051800d000da1f140e40c549000c40c0700f08004800741044015442042001320142c0b4a042c80da803400b43c5824106000d149d809a10000b050074107803800c002d400103140044007035a80455000c2c1d0954410001d502c06480f5441c020701a8514250560303080c420714a201c060001c0e40c05d0010b80c00200c002ca800c6c404e098421828641041402c002803200908a6481081c64480280130900caa44d80f088941d41e50341003070003250b0385580d2101041d402403610345031050384000c0c140c9044080c0262a403c009883c1051b0049a010380003080c032000c8078100903038040318242d191b202c3d40b80030130074021400502e4003041c5403110405071140e048641c459061a00040440d04084501c52149042c00382d0b070008104c0c0c40703030f800001304020b440202d04540b030b042c010380300d85d801200301c0c24021050328000030700d0880001002e40c0a6807400d050361480300b008130426559000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 273240188 1250 273238938 273238949
    0x1602180402090c090f0405150307150e01030207030504030f0b0a060501090803120405070513091a01121106130e0a0c03020306131505062a0f03070206250503071209 72
    0x42c41004640c04403401d1020301841c0324010040410b40400300003140c1a2003090f03c80403003240d0041030303090041c0b40601c05600600b054031010341e1a144ad2a100801c41c05001d11702c24145913000411106051260048401954100140b035071804294940145528170443d40d0360442890540c0c0401c4030740c410303100b800c1101c2c2814011410310550206800452802500495107072044000001d02c82e120f05010100c001500d140c00034403005503007400c1401d410348200c48505226004011b0145a0309120304010590704050101101c1c040c51000c0740d030f544204c80703a01304d0080c04006e001800c1c00344441c0d000d10801000205101d956a40c030b0054059000c20303a0460f0b440221460102e801c1c48041d4408514034131030b0080c1d08141941c5101080c240e51081d0307240a0f11000121204600f01c0b402c0030040000d1407404010710b661030110078225101d00030088024454180007071248051000c200c411180e07025402d02d8010340380c1d014905940e41b0b502804c011034849950030721154202d07000e45404402c0700c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 273241438 1250 273240188 273240199
    0x15060c0201051303021507140c13020c0c0a08010e070911040b161502030610020606060a050c07030507060201060e010603050903120a180308180303010b1605121602180402 75
    0x11515801982e094000000025100b0316424002025aa401001142004c441c01e0503607a2801641030a440740d80440d4145001540041d50710b481544541002441b9101500e50050b21500c03204201404e00c000d2300c0051307a12507101c45001c10020019440104076145200c111294039950303000c0c110035904480c250102c2c441c4203010401100ca900d1005051402c00981502c072500750780e6a640681f90700e1a804a1040341c1d0110404c40c1c981045452440e01040c2030008001ca490a5400505a4400c544c05c0d68108a80400d2505044030100305441c06581d0000a6609031500ca0100900800c0c50344200c150302c84502c000091a0381c00f901c1411300410440c4061480c0a44d0428a0100c481c0c0280c40c1c800080c0d954540f00c1407021070888010341e00c507c00d903075aa48904080304004601664641c03d034016400c10401084030364103840456012410703050720b401c45640f50782800e5061a00d024081070440c04c002401000007001882050700e41031080707950b9200a80e140340b4400711b0010840d4025040b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 273242688 1250 273241438 273241457
    0x9030403020103020c0304091514030120090a0503030c0d0318030f0309020d02090a0605150a0929130603180f060b040b030d0309020906030604021e01230a031506 71
    0x42d4030a0b00140030214800f011246099504c28011f0129110b0902ca64030400c60100180100c80d05c82d2011600010700310000d010280346205c490051000c8010112880700000442c4440703074662030a101c00510004082e2038075409801e15294860f202d11198200292805900700034001da00008240c1440e05541c44141c1081c3c03042c800d9008080162007a80d12040500c600b400503615800494840c0000c3c14000c40c001c0c1c03600c0e0601200c85100c1944c0f10210505000c800e00ca075600c9003011049aa80700001e13425040780000300010179042d910941d0310094002002803002540702849412604295000c001d400303c480c080304100381c4000802020002c2c8a031040c408103100750020000c1c1003000b000024105104000203140002d20700091010940320700c012419403402c808011742c803800542c06403043d403070300f5800103600c00e55440c030b25554003001140700459a48030b400b030214200d5184c1300c03181000800070109a0250000c00454000a0a2020000022a40c044084100e0304c075500e4000302c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 273243938 1250 273242688 273242693
    0x81c0f080c0309010f02040306020d0c0203030c07020f130507110c15190e0307060207030b10080d08090c0a0335030606090310140106090f050303070f05101401050109090509030403 79
    0x42c1d40007518246682d92070319000101c0740d255100802c000c601c04c0900581d40c4c2e4403083e81d88151415100f030441075400c14030420400c02c44243c1201c0303117140c1c1200d00107070507071a900006109500e610491a030301498442040095034001101c241c0000100d001c482001701480104a040aa494007444074003402303000710f400c1400c0c0388031400d104040d40c0c00c10744403018003440480e15100c0d10764400f2006030710515040060010410602d5080030b00030004481090030402910740d100d1080c2442e03802c001803580060004e010500141d0500301d0300520000755141d0340d0419284000040700074844012043c1c403140d22a01045d903a071160102d884401604603582c40c800c0209941180104c10303054000d048803500045d1544c403c0d64140041c03800c400d98154149040202082641c0d0000d68024050b12000c1c05556800801d0340c20b02540008001d4410006107801401c00e003110300d84140150a2035500500507660000b5141a60001c1c9d132204003031540c1c2c201040580d281991a203000d508100300500c013 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 273245188 1250 273243938 273243961
    0xe120c16181d0a031206061e261302010f020604030215060a05040204030c0e13030203041a070b0703050103031e0e060705030c0f0a02040f0524040b0307081c0f08 71
    0x1e103801034902c908101911000194188100e5103411000510304005007040c007409442044080c16403880d00311654200740c4035000d5146001683d0381e061004141500340c11040d4040d841c8010003202c4022406070800410480081e803440f00128040f8481081100100f480040c0162103035130981e004010340c0c2c0ba40660301441e007070050880394220403c024082801c2c0c5650001f40000c2d845140c00701c2340c072454105a00b15661015210a241500600341d02010aa000040e20309807118070f010414214003154075401c040c420140000c00c1c90101c0020003013280c0d010703440030303048a00070385584180d1001544214421003410100c0030210700701101581c418181203000d050417500c14001c0780d280c162103103201450300240f031801c804190b00080c018011418540036009040702c4152081c0080d0803c40300c216588454004041a04010a8038002281e5250340103080c1e0644003030281c41c0425260100f89442c0c0d070f9080604031290f184115086416885003c5040000722199110245600d440c10500c9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 273246438 1250 273245188 273245201
    0x7030e010e181009020a080a0e0703120e0316031103010f0b06070308062e0215190b031c0e0114030405120307030f0501060903050d09050108130201030e120c1618 71
    0x401c03003e0003d00800c50f540540b00614100c80d80c0e464951052804c03840500650f00b92030441d007000e8205034070800028480f510b030100c40d41410700f0820720080e5003002081c60309241004564419941c65400000d002850750603201c40325050340240316000c0b006d40403109603180c0c0c055484d00450304222040109218080050700404020421800d2610f18200586041c0c001d04941e8402210321544c0300d04150108041d07003109100c0c840403556840c0082c0e014900b03825107000300c02c41c6512a00031980b180c5d000d000c8182000c0c4448510000404424030080540404088250114108510b140f041903101c1058900c140d5201000304501c3c0343e07004600c0300c44c0d00064a004141030716510141a5400b40d40240d074003900b440e649100740c5600e1410000c1c6419040740d00d1400340900b00e18140070590b408046a50b109203013504001004a40740300490040c0007406020380203001d002000c0e00050280070040c001c40c003642007100c149040c4001e151420003a9880f034041000401c0102c0e4240302826040302 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 273247688 1250 273246438 273246451
    0x309051f060504050f09062203200a0320031c02090d0f0302061509040b0c030705070b0f0915070203070209130515040605102d0b04060507030e010e18 66
    0x4074003255540c000c2000d80d0400c0d6000000030300c44004003c2e55440404c16240d01c410003100303000c004000d503042054803005c2d5001c085c040040414181c0b0104098940f203054003486001140d00c0c0321000d040040c050700a00522151105030090326408918000040d10105020107804181150004540e10025440b10590320340196040e180c0c00c0200380442013040e822030294010b0111403812809023040e812124842070311a40d00e031801d0002284081d003416522108c82042d81341e5035111203a06036004d00881000800246103101086260400c41c400507010700100403c4800140721460025081c210803030b403020069009020b008007501d0811070894220840821901e140300e0342e515034904040e200780c0c1c004007401c01c80c0180810883d040c410540d0041c00f16600c4181e8a042200c04d2660b4806139905a03403000b83d04018001100c06101d0b030000905440007004c0c0c1d9a542c1d04009003558105001c243c000c1020205252541c1d40500218001c3c02401410703030141800b40d007951a803842c0c010700f45 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 273248938 1250 273247688 273247691
    0x27030a090b0c1606020604021302040e280f0b0a06020109151a090c070308090d0906112401080d0203040e19060306021605061803030408210c040305010c0309051f 71
    0x3d80d80510125112101a18007170340541547d04e4140140120414240c1c00c803c1c01c14410001002100410200940c003c80b00e0384107c1074064207000080303001d50301240c21511103443c0c0141700414054952041c0036080c8c0c1521440c500740c0c0c0d070314000e03800c07520f20020150040284100041c0d1a20713260344012100e81000e051501c00038000c20102e0301c4080d04440c0c280c070460000a41d04107064211703000943c01280800101003804400c04003c202c130741c091050304d0502c8403025080543d00c0080c029003425808607440481e07013005031001024598001e100e030941600880c1040040eaa00c040304450950b80f0b41c1c500c004480e203500519185407544440c2042d03006070b45280100004040d40000c00507460051401c03184039409003032060030048064910782c0e55401c1c0040c00b449944001c02640c0c0d20036000049036454425008069800320340204052800585130000c02044e80f81e8203003e0029680903100800180003d08010303400c40310100c801078616440480600704204d415255100180c203100e00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 273250188 1250 273248938 273248953
    0xa03060929030f071a1908071227020a0305010c020102041701090c051201020d0e16090e06040305030c040803070506071b241806060608070203040303121a0927030a090b0c 75
    0x46d0b02c80c0f682050740320f03040010000c10501c0001a4844c0b50707407140c0410600d0070440441d00c4058024061201c440141c030035010008114150f5442003014401150803400038030805107c504001e0003584507002d104212002000b070440107800510421300e94980c032440e0003403042d08000805c92401c030344484c3c6210564007001078030594291401485982d624010050402c4000003600d05818801d80d04606119881c003c010707403035000001802a0499090300344255640c40c1c80001002d5031086812802c668400003c842040180000b891481048513540303401c200c1c3c0d880b401e0707a000303c40c07030036000b030107200e5083c14101948501d09105800300c408000c0c0099181c60018100440d16820a020b44080359a50300030441a9008091280d200e403480c80903600d010700307680d0041c01945020f03c52006280d541c0106403801040ca10824024080003018003945243c0280411180800040c0340050816403440f540e40c0c0c6c00300007042e00c4c1e11140c6074850203a21818080007124075008001440503030f12400c030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 273251438 1250 273250188 273250207
    0x30b071110020d0e031308060a0905071a0c0703050d0305010f03080901080601020705120a0213060506030a0209180408130e061c0c0e040b04030e060a0c080a03060929030f071a 77
    0x1004007020145510f02c02d4201f8a0100e030b290801070010402c85000f801c000304200010408038980055500600c2c00c021104404031040307646010b903250780c10380f07403140030000700601074001140000c484807a0740a224581c0c89891030220b800e69072000904404040c01803180540c01184003c0d403101040c81107460301e6680703000241107042228807400c0360f50408102181541404185a420358598040c00c1c0003480c50840820031611000b495201d04a07808116030000d50b0780c07246c290401140c07182c400c0350a820039040c450f449a20000c2483d05034055000e00040d01e012180301ca038032030207000700443c01501401848504201d0340450886105075005004682d04120f10ba505014900580b207001681c640b526004d00110074a80d07002e407080350240320034120154400c2c0540351107030f40802100d880d0140e161f01900a000b40d80c2000c0a07190a01b0710b0303000014902011180511303520100c4034004000c4c113040c5505d0315080c0d0050340c42500207030414012030480020a2000301c5001080a15014004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 273252688 1250 273251438 273251443
    0xa030c06051e180f091302100201150e06120c0906010302071403040303030509100e060109090809040509031c1107081c020d0203010504050135030c03070b01030b071110020d0e 77
    0x40d42404038444041540f050305090080c40c403002e15030150784d11035030350070181003500d842c611108000b80310b81d4104462080c020720030b4200300001568040c0200659440f20700140f420f60044944078010b6400d42c43e145c2d00b008002502001c5010040c24103241c6440d03500044000e544107820039107624062038171182c21100e080009000035806079900141a041c0354440070f081c540f00400074003101d42012a402810030010850300e04441c20400000760946161038080c00310f008846a50758001c1c0b404040014041c0040000c02050640743e0b84801030303500d090045011141d4a04040c101950107101d00000600200300402c110101004041600d0901e0700e040810303a4441c85202080c95004070040003d42001d004039405018102e507001d0b5140041c51502c604190340005601140d001d1500d40300000d80d0500441d00c080d01c41704190b81e628001424000c544010a20040350302d4400000061400b511400c0000c80022840d40035082254604080602940002c4002141035603101204c0000d042d08 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 273253938 1250 273252688 273252697
    0xa020f06041505090303010f150e04051e0a020f090f041808070605010b0903060a09061e15060203090604060c0c270e03090a12110904031106060a030c06051e 69
    0xd41d410900b880ca061403000d09540d0090600f01c8142d0052005100440d1013403220b00666003100d200582d00940c420b42200d000c00040425500540340c8070501101031050700c2e80c20001007208012602d2911036510540480c425a074020030046800e0140001a10b8a81200009018000d0011500c50000c01340c00c0070240c100407044035040e03400980038042250303e0041d68010046061401d0521802d04082611000300a103111080b13a622035842c2c04116040c0c1c0114204140c0742c0c1d00581c0760000c0c10084005001c1c0c3d081405075040e00c2880000c01c01c0c03001080300c0009902400f00e904081c40c00d0350560784c0e20400d4404440c000d100c0704001c110110f941c00d014521250000349004c00c0e030703881c0c0300745002c840099818500130740041060900d1921412204821582c03e0818100021140c2c14500070070001d800c0e0440d4401035003401e1009240e4003400d544041d6030003405403010358507100100025050136110080c80e12a13070500801c8014007070009400c10202c0550b0745840748580d092418143e922 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 273255188 1250 273253938 273253943
    0x30a0e010e0706091203090501030f060e01120213050903090d0c1a0a031401030201081512030f09030d020703030206011505070c06050c1015210b0717091507050a020f0604 75
    0x10002c208000c5034081c10140c002c3c280000300013450011500e0082881c1c0b0f06020700703814141c5440740540a6503840c0d100d40b00501c102ca81813600c41d40c40d8080c1c2d048440070128268400c00d800c110a102d095218412107001c0d400f000029454060710100740640240c500106590085220100156060130411443c81d0014a4660a541c4465021028007100d00d080b0120401c0c0201e840103000503604071528070b42004c08020100c01c01d14a081c001f641c03007c01401c42c81e91500001c64514a50401c031806000c810804406403251a074698000726500c030000d04c0b0140040c0d12080040004216405060002040e5850201d14141d05a2252400700045a10400003d000059407860307560040c010110348480c200000c0c00342035000e142c9541c00702e0441c020311901130014210804003294088240c12801c0d44000b29140d00e10b01240080d20311031807050301940c1c050060b030000315950300214040001c12074040198503a620761a03c119040e4000007030303000030340c07083c250503041810080000c0c0744030b281b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 273256438 1250 273255188 273255193
    0x30d0c021f170f0610353301080a1407020706110d0c0b090c15030609010e04050a0f030207050a030c1401023d0204090c0f020304060e0105030a0e010e 66
    0xb80040707000582100002c20320240400c0c54002e02100307944542502c0307410030191a144450b82811544020121001c0345000c00100035044410301c8a40c61194151040d4810007001d4040200c075000c03001468410074104460724440c500d5000c9560141c01043d4110102440001d040e800b08850342c00c1880041d80c103040540d009000c2045211740c040c40458000442c0009072114540003840904240b516a60003045940d400c40003d092000c20418120000b0000348036007640b0b80380c0c031684003c6034000d0302c01c40e01581000001050015074003170094029684000240804c955584030321210a0110800b1030841c050180002125642c00d0711440245018200e02d051803494050000402161030710754a040d500708600300c1c24000080004d141081c0d05e40d8800c803500c1e00c4500307450310a40200550080c04184040b07004038506030182d01124001c0596127806811405070602a030341e034080c03440b9036000500703400c040d010b095201e50069030700800c2501001c2a4203407011803c6003500c4c0740429102d1241e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 273257688 1250 273256438 273256457
    0x90503130303020a061b0e09190501030c09140106050712021e07141503160e03100902012303060d0f080d1e05090607030203040f0506010f0512030306030d0c021f 71
    0x4090306c03400b4142030344984c070381010440310000a00301c122848116441080380704001400d42c0b0442928008014001204210707941e1a4a0001405085401261301031850200e07074100300d0704074030650b6060f10210303100c1070301f0822a603440d010b510141d2504441180580d000c00ca9140c903248403040c44014451000e040700c0307801c1030f4200700400031300422144900201d22004152402060450360003440070802c181c0030705c5040e40c0a843e000e0f0b00003030007034061040072004d500f0361a01da840310003aa8401d99480500018000e00320076248018070003038011800c10001b10320701785801c0035129141c51151000c05940c4d0007070744920345550030000c1502e40083d16005334246240d030017042e10340c1c502c0350103400b04010308240c051580d4500c270051100c018135a001002c60103005c08444a0417199a002048421039070b12007105000828043c41514054035503480303540701500011003a031b440784102070f0042c0028900d0380d200f100d00d490041c200340c5c1c01c417284103128266607c00840c0b001c6482020b03221030034103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 273258938 1250 273257688 273257693
    0xa030b01080d0311090f01020a0b0a05040c091a010f12020c06062107030f0f06020a0e0a0902070b040f0f08030a020717040e13080d020d0509010b10080a090503130303020a 75
    0x900a001d120b0408043c94a00f400740020388000c160345924109941c0c004c13003400700c800181c2c40c0403c0c00402038100c440d03200070060200cac1c2540280340718510070900700e40c0090f503840d1980c0c1074400b0703449400d490102c4602c4080c040d5119003183c4008400920341076008850f515485c4089900c05040103455411a208200c4a4140b6440fa40b8045c400400c80b4401107684214582c0c85950500009100c4114180b02d0000e100001403035201050300200210759401303110300d0180c852099072880303501950a01000069000340c1b8070070781e140d150708460030060039515a500e41000031102d890403034900c03200c0b004a01c080b50401c0080c51240c1040e420059940205081001c2c4942100801da400d814040209222001c0c0042c02c60360040000203101c1c0d00b04056240054150190551500e04140f000c140c6940c25603c035000f10703024500540081001c04070140600c030303812001004c000d011904810114143c0211948866000d034016010b59051602c41c82e00700b400c40c65140c0c010b400690014105209 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 273260188 1250 273258938 273258943
    0x1020405131b052106060f030c07061a01140c010f060b040603060b031006080a0b04020d09020f030a080f0f09060a03050f060d051b010903050105040f050f030309031b0a020a030b0108 80
    0x1103201c840d0a05600340b0340400b2101c5005034420340c01030414024100805c0282d111542a0b616649030048840e48030300d400d40c40d25001e03400822043d1089400d220891003100741e02c8085110800301a900c0004c500050b0900584652150118100c0d43d903881c0902c012112103031280c903002d04401c10441e070b901e03860720000505581c0207030400c4450308800c0061040c0e20b010300d2180412200c440c18240c0c65a5140c28840d030080c4240801143c109000040880303100b03905030300c100500c80c821500403103510280302c10b02d95200d2500c90010710546c020404103210543d00e401402c000c404042e559803801c103002c3c0109945401c405002004070340c84906204617030950002036079008609540f5030f1207100c000d031038044e070702c0c94000020313805240d41000841051b4419200c400240d90410020301c00da040c61708d0440c0d048a00618252900d01900d40c00c009039034004011a80a45521401503045c220780d03a620a00101c4450030a1903a0721421480b1401629000440c000650094039030008962504400c00e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 273261438 1250 273260188 273260231
    0x506090703030f090605040905070201090c0b030919020306070e031006091407020c091b070503040b0403030e03070e060108060a240306050a030b010e041716120f0503040b090102040513 81
    0x404d00510020510000e5402000d07901180e0100c0d00c080340c3ca8680120507801000315080c050401c8030004800301c0d4a9001500450080840c20704881603150220100004a105050025819009800402d00182c8104d0200000c039070300400340c81003203c03060540d40440d102680440180c9840d003460400003592601041d034090944e0000d007040c240c1c02000540032000041c43c02c80d000c01c8141c2203c0315500e034402a2010141e005045a0b030f01c9450307400442c030b03642184c48200c000516441c6210014100800e041c8125002020210400d4031200d0054071110030080c6165004003904ca40020010344d050141300e031030402c02da2400400c00c2e54002c010f0946a0715000240034480e1084100001800f0161b40e504450702c1140c3e0f240c51740c6032031030841002c0000c08407841030010301103145403161031311105610500c6d1040080000c0551a25030136100150300301031a0300820300a20005001c40c0d40c0c010550380c8601c080c00014a0035484800148000c54000259100da9584510006d501496881b80e071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 273262688 1250 273261438 273261467
    0x3030b010807050a050a11030f070305030610032c030d0204060e2107090f02090402041d0604090209040b090a02040c0f080c030603030f13050603010b180d030525050609070303 77
    0xf9807400e035650784003404501c240d9015900300070600007443c603000f03403d1042d5001d1501201700140d848540707040c000c1c0316400aa0b48180b05010350302255111034000d02c5200c6840c20801c881a100340407900c240300d40480d10010420840c0820800f42c64140618030090002d04807a40352245103802d80c0050051080c403050f1103400020700031807050498103002580380222030540c1000300e0415081d209060290180402103a0000d002003008208102d68001d038101c0b849118410082c1540d800c02040161911440041d410a607010041400b0490414200381d00440e18030880e1500c43c9aa40030a044071203501c9e200e40054080d096940788160b03c9903c0640066001021a0960401e03800003900d9201d0b03007045000319000000c04801d540e800340c090800410000300b2594030303580d681c0c11100255200f80c0101151901140c00e102e82e51508803844040d95402d80c0d00d460500304001c400322086664003281c0302c0c0e4054610340c8070340062420844141325100b040c010340b44c51481c603d00940120300c541041c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 273263938 1250 273262688 273262697
    0x3040506042309270a0b01090c0816090b09040b031b0f0306041a0711010204060804020f0d0515060d02090103050d08090d0e010c0c05100c02030706020304060516050c0d03030b010807 80
    0x14083c0250f0a5100108442ca00300845011006008031040c41c1c001c170301e00020100055100000340b0038500e5805000c2c42c070400e07101c1c0281c44d52698400e03960810340c60819404140d81140078070820650030007520081038040d000140710000c01c00003a14004030701440000c01446d110800716503041103401c6108101096000b840780b030405030385098140094107000c07007085686c034001640c201d1040d1103911001c16001d0003107607290b480ba0320042490004507010b07409030121604000307a034207103c80040c0e060780d04400907207294007000103024480e0201801c0d4aa100309258034400142e1340341d0b42094000c0d071082c2e00611b0003080300b41c0007a203a0803000b030500c1c5503600711080c18044940c12203459502e0000929040d6654500c0f0b15010724030241ea03411040e00081c040700c02e44042c541140d01d002040e40210111003035142e0301c0200320703542d110764040c010000c0d1050103605280951000314034010b40c030601c280c808100215020401940007d5019000282c69401000d129600040c295400400e40d02d132 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 273265188 1250 273263938 273263941
    0x3120c09040b1c0c09090b010e07031b020c0a0e040b13060605040c0503040c0906080604031101091709130509030912010212190606030911010804050109021017060a030f0209040503040506042309 85
    0x50f4030a001c7c00500c1140c0584800c0310005503140c1c80703030784980f641c02c0002c0b142e844c4444510400a50711404500c0b4076008004104010440d0160a01880d20039681301c0c0c403e801ca5919600600c43c10640c84d00304880c2584c44181c0130800742e89c1c500171040c0c80802d40c2c0e03d1355220b140c0703410310387d080484e03a40c01211007501c0c0c8041444815008035100c2d6120740c06003407040601281c640510700402007008058410040381070710b200c1400039203000302402d150480d43c2000b40119207040004079442903410041030703413040040078117504140c10b01d0310301c24000100040c108032160f440c4c0c03480c54008445612a00c00c00c04d4200d50441420720560000d00494074003002911020303580c1211800881d00c80d0f50621840303400050030001f00350440f5001c5903000c1c090086100e40b040c07014010803407214010901201c0c00c0c00060f07041c1846290034040360380040007031000308410740030b1104503071001e0030a0352540010400400c40d900c6200060004000c208072804000041a0741095104002c07181640300707003103640 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 273266438 1250 273265188 273265193
    0x10504020c120f09100e01110c010818030f1603120b0901030b220308270307082101030524040f0b0703020c120c0d0203120c09040b1c0c0909 62
    0x1600e194080082100103640d00c2c600e0f050001c050003034121581e8000c1c094003030a0140e0342e2102d81540585802c1e200c0c4100b141f1585091074450145140143c005000b0000066415155400b0610b040c051007084d40c3c540220401c0308582540560790700a0319800e005042c0e02093303030080c2c0f003104034110f400003001080b600200142031600107200203041d020305400400d41002043c8405840004100c011000b091054903002d810100100d5030100010f80d00404290314660004501d00301e4a0010055880c107403050f92202d08540004074207220710f03691b04455203590b280c1c41c0c11541c081d6000c0e0f00142130f00341440c02642108045010f1000121500c40180300001c1d90031012090101d5001810555540d01c1c40d204900038010040181014410046250f2481341c3c01d0f001007042d1199041511480c04072000240c4c0d5900c10401a1400c003500040040c49441e000005080d212200030400320b9030035502070014a0500c465009510f542003035107048020000703402000700085c0a030510a008001d00354 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 273267688 1250 273266438 273266443
    0x8070518010804060b0306042004020a09211b23031b04202703030a05070201020c0a06110705030606030d120902040504080705070509220f05010606110105010504020c 73
    0x4a0101d051100c49000304082140c07a030070401400001500310341c0d4520381410b028a06000b0b82a0240c0960601d440450b080d007402c0c000c8583c408a0781c0c035403920340c502d000303001c5d00c40f50001010b5040d0518103103107000004100d200c000d03c40f007000b001901082402c1240640501685a01951020642e0040308189490114600f1000154034031103035074071809040170901915481c5c3d40396010128188140548584940140010b4100c426401c40400000e0006890100440c0b40e12a407540c0148001c05030140310b9001015550300c1072040e651030000d2000415408206904010042900700d954000c0c003040400201006100890040c5640d080941c0400c1e143c11036003403840e0401c0805404012816416000840090b40c09442006140342c5810100b1440c3c006d004111042c4c0103942c00050289800200b080c00b48105d01614a59014212200d42c0c40032441e103421034010b4010b504040c003159017807050100400b0760745c0320781d02c08407000341900d421282d05800c403600c943d20501c00d0590700d2100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 273268938 1250 273267688 273267727
    0x3030601140901090825080105060d170d0f0e0d0206060906040c1404060203190f170a2013120b160c080d02041404050f061017040501050601080705 65
    0xd40c05050342d401c2014012590280d40d50042c40c000e200703401e041c491406400c0049a46602030441d0a2086920b0740b800500b80c4800b1760349991302444100d0343c0d1010502e01c0100401c96002a400d0303601d271010004401c02a51524102d0b03000695503000e01540c20041404905500c1c070240c4042c00e014034000f0001450070002030300c2d46020340c0e600c04c040850140151400c2c14109040f0000b60385950380e03043c009541e03500000d040895071001040d2456041e00446441f20030140c030752903060b00c84414801c000035065000300754140982d22540c1d000a80d94021a00a15800c1c0c9244442ea8411111070700618100303459020a20004078500c1c080045046081c0664200445d021a0541d0000d1503008030b407980c14815020301501000610454803032800c4e8010070459600c1a554490511007808010440303800301c2c0c00201c107003880c81c00501c10386032120340580300e140070781010045592030a072205810f8004680449082e03544c3c01c103028140d86c00104031540f002582c41c09a140c8240c804400405411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 273270188 1250 273268938 273268967
    0xb0901090506030708070b0c070f06020303040f0c09090308090c0f01020c04021809160f0e010f03150f091e0902060703080c1c050a0c030e031c020912030307020f03030601 75
    0x1078038804201e955909000900042021100b126450fa843d8001d2403d103a0203011160801d01c9074482c001500080d6190280494400d6009541165030f142c891100c8210700b280704441c0211071910202c0c501c0101e110f4090b21600075550b2106038540b010700c003131500c000c1500c1288904035003064a0b001d681d0001e43c0018010080d2000358a0713081406801509001c10200d00340e002d8040c04c20403582a200c0407140000c00303c680e0358034881440b0020103a41c0d00e40300052213400914010f0754900464043e40283e5880d051352440d01181c1592404512103018054004002e03064a980d0078401c104d41981140040c1c4180030300400c2049400d0b80002c11611481a00400303001e003d800040c040380e034a80595400f440201c0e60041da10b0740f40ca12400041a0454050703004510304101e90813000c2c03207846400c00080201000318500140042d8141d4a0b100c010503104c0034903001c014040240e00c03108100030388401c0420083d500da0a0003040a07041842d040313488065984180100a216a440750a2544919 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 273271438 1250 273270188 273270191
    0x90705010e0a0902070b0717060d0303022a07080c0a05060712020102040e07081e0f0a0f06080102210f04021503040819081605071703130c0902040f08010b090109 71
    0x40c0020041210038015a02c010320461012450206000070348071b0082c0305006560b100da000075003145001d41c6500094400359080029a07045200103070027a401803e1091003003a039402052030740e800c41ca4441d80755100a00084e0002482000038100c1081101d8012204850342c00d062070401c1c02242c00d500071000040c00e000504c20107200b0701030007903040341d002e0581c400810030903103460800607040382e42c145da41904110929112884c82c3e42842d000c01d00031030410b00c200c407031621041c0c11a00a4001c840d4200d900f103a4400c000600c40500f480200303105013140a100255114400d4041034904000302581c0305020030b4810400141d4600b03981c202041c1c00903101940307a031120b0070403040c18050351003803000c0c1007540305090342960380007181c052042084003030036070f000000d03000120354a01445600500701220701034030700980721401e0059640000b401d0f0700480700c00c820362514000b0364403581c044065aa800641031200440c0c100740c1201401c2c8400003404104003400c003280d2103500510400d003401c0e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 273272688 1250 273271438 273271457
    0x70e0c0313020a03120e0a0902120412110f1006120809040504060902060705010b0f04020f03061c1709010801090e06190b0a0906140405010602072d0605190809070501 73
    0x56840d03d0100700507640003e80e050580c00000c00182c040303800d01c0200351080c01c00312800503165005000312180402000100c16a6480396030f141c54030340071944030320014801d090300360b688900001c10a000103040100000d0040b01078400041c01194041c2e0042c0c045501c60310381480209000c8000c13112600300c151000509941c03039040c54801000b03c590003d43c4141d000610105202d0b054201030b00481d011224030405a94440801040380b18801207021300103801c1c40099114a80020802c015040750300c07902d40e8601455980545003620000c81c14100d40000c106034205513401103047e405402d50703100070000b41002c01400741c0d035140c0003880004142044c103500c4e8440d03d015004121081e0001d44401c5001c0d4492035200003a0009001d43d00107044440c803a028285000d0141d81e04840403600a82005810010305503201000c1440c000016105040720540404080e01c189000b1302450740e490303440d00d0f4807009149071100407121080130004908107111a0710f5001c0b0344102198402d00344850b50 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 273273938 1250 273272688 273272693
    0x50609090715112802091005010905040f0b040e07030c0b070b1f0801111e040f0509360c01020703030206150321090a0915060507050a1b08070e0c0313 66
    0x2418042e10000001c4507024010b455001c40c4c4080040f98544211010034030307903456460609044070188111030000d21a003404001504140d0b03c000410800d03081d0104a1206110100303090b2000720050300100d0703104038820000d000090aa50001c1c10402e04402e00c1e05455440e81d200540c0054101c00c1384440c01c0700300300081c282c04001c02c0c00410f4201c0080c031098100003001e0805030404ea8140c1c0e4488550b640801602c0c41040440703041e80c1c0302c140f980050340e003450700340001d00400418506000c0307484510080c100d907405060342c41c01d030301d1010004889141100c103d070030034800065150641d44450000d10000f0b40100e41103078004d2005120317040c480302881c0041e14083e00804114007020382c42d24400840c500d414028100c0940075601c5603207080c0e40382c2c0b0460403280540d0410039170440512090040d44c0c401ca0003410400e0240040316103004880d01c2d68003402c21010100305200d01a05401c001d620340600148000384910407240d4002d16003200141e8103032000400c1d10b240c4026600c108403c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 273275188 1250 273273938 273273943
    0x91005030307080c0c09090616020a05030d050601140d0902040c030209090105270a0b0415080a0f14060f09010b010323040c081006060e0d030f0809010b06070605060909071511 77
    0x45c251008040c0809400d10301901903c2d4a41030b079018241d0004945040101400001e4441c2420350050080d440d02e1031f260a0b510003070001030801410030007601c03a0035000303214000c0941030341682110000b800060310b10401045441c0715202030145401030155654135502e001c2c005045440603150060340420004501c03120a0340610507142d62049c0a05001c4174810a034002219560103590820482082c0303100c18800c404144070f816543d03801200c401c00040d05081096180078800d90681a90000c0401864203080c01140d005142156580070401900000d00458641580c2820b08021604000c90050040e001d00c0445071900c68000c0d01040800408848607001084200c05a401c8480201003d10107000d5611030078001500e0040e20400a2515902081c10305070701d5203507010032000514050300e05440040c901320300d6560f100840b50050311580004c096483c42098001807134039029042000e6071300060400c0c43e450340a45020302c26240001c04008a072100b904015100c00030f000c20251 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 273276438 1250 273275188 273275203
    0x5090d02060c0111070c060504030803012d03030e01030f02030915041721010905010b1204170a03020417010608031b030c0d0c1406071d012c091005030307080c 70
    0x202c42d03190100c0d505042c0505406080007900c2281c03e18000c0d984c590703044455025074000030780132180402c0100200c42c0c2c0d440982c01001c844913595018400302c000c118850003080c0c0e00607800714a00405242e543d41c2c0c18401c0c601319001e41d90045095051803250561b03540e018079142050004054041824400341c41283c1da01d000f003003500d181d5103851000450020450044c0c0100c00030131090008107604209005d100d0503900c0070084a82010740e50b84105801017800f80050344c14890101c5603c1a80c1c00e1000200700a00113514050fa44500c1c1c5034900c0c50600c804030300c0b100240d1406400340040c01000c8125240311080b50002d2a0801a8003955070a40c4a601c52440e49446072307030034024805400904840186002e001d400608074114980c0c262501c508841d071600181103800c83c0b060402a044041d0b07000764061401001c032102841e03102134144441d0a49443c14680b15040078036608d0702801582d40300c1054003c5521061a0101281d602e0040407002007403041c0200d1000148002000101e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 273277688 1250 273276438 273276457
    0xb070309090e0106060f020c0d02040c0509041a0a0801090c060c0c0902070c0501030c0c030f0503070c0c180b01140a0c061404060c020606030a0515090f030703050c0607090605090d0206 81
    0x41244592406825001300014422240070a400501c0601c00500125440402e004090138402c0b034683d480d800c100041c20813800d0f800c244a000d02964040307846a10501105440202c240041c0400d10b4040042110705a0f01640079a81010720140010398400511400c5a80c03d05282c222812203103050860704940e60030003020640b010500c0c2c018021151107e608554017070301c0800c034041126100300c07104501000c1c0503003c5489200d001c0d18052160006550284042c43c14003241562540e071030045124541c030143c5010305031203648901044a11948032554400d090041c5021070084070762060703015141c0e10506000c1514003017024400740f80c201c0d07074400c031000c0e022081074a0709280080090400c0f95500006126820004009040000e1100016a0018001c00740414105c0318909000b034000c000c1d10090140d000780b04481c203010805040c25134840e4407440c0d00d410000d81b070710b07150441c0101141d04104124104011140c1c000c42201c2c9078040035501d5040808107800400c002d8801c07181c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 273278938 1250 273277688 273277691
    0x10e060f0403030f090b160302010f0f06150302030910110d020a1d0901050d020402070f050f07061103030609190605102c09160c0f0b07020105100f0b07030909 70
    0x1812200e080080100192807194680f242111603042d412101c0700028080d500103008204514007a011840c81480d00c1d0910030301c0080380329040c0e400f00106840040610440c8036440718018841c4072140b1084102954103842c04504501c0c00300007581d9924000391440889581ea00341e2442181c151408542c20505208429903a41003802d00081a034000c044a009113001c0400501c0701a1929a04003812101c0080580d0300841c035a4003040025441a1000c5600c250480031110004c3c0007403024801c1202054060074a030382c90400d004c0d2070040f0050b4000300c2c9410030001c004030360b40c62041e0f0300d401c0070115080c3c0312038440e40b143c0b00c1c2c000c114503003225511854035001001c1c5150705c030001160010042104d51420004040b4942180d110030340030755440180e40002450900000d1190b141070401c5141c454210807058070344100100b2000380540c1c00103100c0007000381c01074090107999004450303c160340040e103207002c4043d02070030001d025248058074000b03540010300d48200c804401600110b0b40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 273280188 1250 273278938 273278947
    0x2012a0b04080a0809011b18030501060902041d040b040f0201030914031e041508100306050a0524010e130b040204081c020d120f060305010e07090b03120f09010e06 72
    0x14521000d400422103c00001d42c4d0f4800070b02d0181040c0501070480040d06454200c40346400b03402c1d038041c00c45511308080d1450088001010903004d0181c3e030003c0c0f001c2c500050380e1303a090a00d0008840c904403018119514140188000210810b4500e680300390800b010110448861004901034400c0d000c0c054a032030590319a03001055004001000030707400850603903000700101e0740700e2070b81c500031440b031420fa9034084140c045c1e07103d000781c8502e94004a8191203082050f140c0c1c2e902401c460003500d07100c58550b0780d41e0402c00c031482075243d0a0180e04d2440d0a510741c40301c0060008104040c24000d26004135074907402542e00044c25081000420300c0140f003075444944541d07041d58ac50390103616060400d81010603034a840750000c501c0c582908615903607071131182c010341c556801134041b8603d00b01d03440380e6403400040441d80a1240329400c943c0d49014005281c42c0c100034009480000f40340901c250030140801c43c40e51210400c070b03082045a10001a01e4405100040c1c3e0072403014801c00341c01039400034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 273281438 1250 273280188 273280193
    0x702010c02180105011209030905040b0312030a06050a0b1206010f1b0b0405120a09060309030e10080609070f020d0804050a1e1b050a090b04110c03040303031802012a0b04 75
    0x101c203d041e00d40c281c3e00d130684001c003085840b0070b4500140d80540400c403500c105000c00d003460f8100c000d000030043d08644441103125242103050381b04a83c1841c0c8183d4600050056140080d03074030009201d4032051900382100020303882181c0802800007414000c8202c00d83d110180107081403e000622009800c00d4880c141c1060104607600719000c031801e02405010703120441c5000d0607140c0c08a4182c0d2403460041c1808020f80081900c08025001e0001121203941c5503580d141d510070035400c4940e80d107881414201c0c00d02000d50760281034078081c0414600c246c05e546600041c3d2140303114803845e0090840e200d44c101030b030403e082501c0180500d0304a008000c400030b076070681410a140b1800662200348041e00c3c140500d07000500a4030f9100304520400c020f588682c3d000f203001e40000402c000340b000782441e11300400791300441c08031815400c003040c20000c1c150144104403181c42001c8102c0d04242d01d0350b00083c6000180c11003900f04800e81e0030745940c070440c200180c4030800c0d48108207003001d08213030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 273282688 1250 273281438 273281479
    0x403030e060705090108062707050c0316060b0103093f031523040e01021611010210050105090f070504031407031103031303080a0516060902030618060601050702010c02 74
    0x908680400d41403400b1402d142072480d050364120148c1403024000312500380800c00601c00103000c202c03c0140c20700070724100043c00c1c00140345108801403a442e2110403413500030160741d42c007a201814540341c2420100480c0c400040d1701d01e9201c5008034030b080700142040c000902441c684c10801c40484c1d00a0307180b140764140d031103190010812420f2400c000d42d14050040034464082c48030020340104d100c0310017281000e030088100b41120100240c284000f6209207908000e401c6010759052000c40302840071540c052002541c0d000106100780140d60602c404540d00352006040d00115107138030700002d40268450400e48000c2c1d81e01003092200002e1824540307540e10440c0c0400d5416413405110504146000021501220f085020441c070032031554545098030b030050503036202889010404886800d101d0211085103505c40ea40001d4880008c1c014035281180041515403980411402c0300700307480d0006220b0f91301c540b0901c0c12507592070040c80100d4407078440900094000d5208503040d404017901 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 273283938 1250 273282688 273282697
    0x501030b1e3907020103050912070615030f2414150a03021302030405010c09081c090807060909050f040c030f06060512010e0d020c0f150c0a05161a0405090403030e060705 75
    0xd1b03a0070700c15611809030241d20b6662403071114030b000d001000034000045c09600200050300d0307140451030742030f51361780c4642d90600f02c001030403907903180740303030038070400c19041414a4000f03260100c020481c09030385094038681008082c200c1103800f8030982c000300c065510039103504007940e4054003034880c00051103d0b0a019403c2610122159424590f401200520030041402200c40b0900101005155180b0102025030014000b2007004140b26001c110700c1301c1007120000410041c0e07100c5200d1807510240c007045610240c6054402d0f41541d080c407010503001020b020030380e03400103241001644982340080041610303500054201e407454003000320402040d4010851090030368251200e01c44207020880e100d20030100c0080d8012242c804143c00c9003090700e9a038040e40c01600f00300b4a040c4510140380d10b4007411000481d41940407108100c408100c45052400403c0701c8080c428000740e00340e243d0080c0d40070301c2c05030074007134031241000030203151180e0400891034030300300251030003170034807100040141d0301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 273285188 1250 273283938 273283943
    0x70804080f010e030a300c05090306062e02010e01050c0c15010f0902070f080c030703021b060a0f020a060608010b19080d030903020a050d030501030b1e3907 69
    0x1c0c200c0d11070203040004c070445581040c0782e61256070030803018020480d48045a800a88085c07402a00c06144410512414aa404041c4ca07410788490a80c0100751500400804650080c2a84807222550b90245a61a8910001c1c0148203048405d030100c100d0040c0424581c901c0380c0d608007814424100101c100801e003c4010b03100f030700c40c509000d8440c1d0100710000e100b88440c104c00d101007000381001c03503409003050900c540305610340214076440b00f1803240c00c2040c0410050308005002070815070100401240701307408128a0101560314400641035000b4104942c0c2801405c521502c0e40510030b01c2803846941c0d10280400100d610b0708085802840d18500d03860180c9000c9104038845804408a01e0845040c0c0c0700800c81104c1c1403004030058001800c0460661095400b40000101c0c14002e2192038500740d07400065a61442c2000403124030b0241920b054141c1a840c400e4101c00c09224003903000d82c0c100f00240350064501200c0f41510146064020400c4640e4505143e562030340d40106038090 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 273286438 1250 273285188 273285191
    0x190303081b03072102090301110405030705100c0305030406060b0d140601020a02031b030304051f0912031209050c180105030105010b090a0306090206040b0304060212150a0614070804080f01 83
    0x22903074001e004148030640b07441010440d140320400024080c080021400e10b03510201504066550300401d0a441c80075101c0c240c40100410240402d007001c0024500074182251a5038541100c1d8001600f40b00d10218060b0030008000001814440b9a030060001060f844403219501e10183c00d516000b000d200c1028141007031980702103085580700058140e01036070024064500b043d032903111814059142110240c060009010000d040d50310090b801034420301445d00e56141c881d84c0200200080e1103500003003400c040007003d03100440e51180c0031041c03002c01e081d00000d42e4003250a0441c5404142821154003002c005c01540890b20151869412a0003e50080c0541d0745c0b541d07044210b5005105c0c13030300e8010103141420404200759802501507070780060051b80c0b03401d07220072034001164001c0ba001c0ea22a07400081c200404e03001d08010030340c041228179900740c4001507140003d02a0941e072080a04110000340c461a4411000f400c84150350f50001d412035407241d0302c086194031900703503110034901c55 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 273287688 1250 273286438 273286471
    0x90507030f060b040608041b0803190203040605040302090618070e180403080c03070507060f050f2a0a02031c0507140a090501050703030f0903050d180f020d0219030308 74
    0x3034405000702c00c169082222410305007070520030200c905440c000c04c1a250b2500d0305511110986900107054060440d4102841d91450110903d8142030155050311085500c104410044964810243c0d03040da54129034000c05600c41d940082e20500c5500284135800c9035503c280111190003509411040c4015120311200a150b18000b4501d0502100c0140200f002070700003a8010001d04003c1d9030003072582c01c003e0b060240035140d002c04c41d64003442d90800c050340c07203040c40304140020180d1340d88650400c0c6007044000e03108000c4110032492184482c0c000d1030215100034041d000713100351800860600d00e0003011403e042c0030380c40070b0041511000e0100b1a680d0941c50401d00312000c0b5622004942c81d0840d1300ca00d00030044030030798070484061701016950f1148224140003030182400f103601990300c3d0ad4413100b0100351101101e8500a00303a105000066603240020040600d289055804907460708420b0028000320715007800c100360380d101c00c5148a201004140c0c2145000e8016440c5107645400b8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 273288938 1250 273287688 273287711
    0xd06050a180c021501030609150e07030204050a0f110a1e0e45090a03020c0904030507080a0f020115230a0f08030912070b070803041b09050703 63
    0xa100d901400106100c220301c2a0380c1e07248150480302074920580704850a10040c41024140380c1001e0308101e901507100c00600040c00503000d03140c1c690401501d402c201c80324401081a940302e8291100a0007140c451340019680d0350b803544500b031002010341d01032007500169011a042548001c0109020684410080d10013601c102c0c81900000000c0c1c860203101c21028040120008221a900843e00700c0000301c05170f03180b19409000050071520040d00002418103101030310850008049130f11a44c0004480f10210742d0004c2c8907616045c050725414615102c5040c01c071440e02c108400540712036800245824280d500c01d481041809150f8002c02c400403c4d0040040827210501c03c40e1b4100c5c091740b0240f0071204c10b101101019440040500c1d010131b0741c8400070040303006581c1c08102950004070340c800150501e08580480702005c000540b050b1410500e1400b518080d118025108600120001b41004180e0214590092016200a0100b40c0d5620410045e144c203c4451001904042c501c004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 273290188 1250 273288938 273288949
    0x60b100302091503131b030204090b0a0b1005040b18100216090207080307111e07061709060c0d0609050112061a010504050d020a170a021e10141309020d0605 69
    0xc0726401030315110800c2e1510b4102c020308100c62800c0d00d01106d81c0d00040141d48034450f0110203889061551468a4600e82100403180000480e90040300300c0300303140c00f03403d0b440340031203080d5000d12002e19200c008100c1d02e011102590526907411220014801d8a01138002419415020070540384000c01c82e1103825840076409066170090861701c05201003209280143c0d0355914100028040340c980c130b40c1d0041c0110100203160150080c03500a5041442113952001c4900d901824009a41a50f410003000f00c0c3c0e903c0c80010034103006110007041c00ca10b00070198201c41f0040601310014002561160055001d4480f610021a0514a00b188003541da41c14010b00c4003280d041610b40340c0c200351428050084003190400e00700ea100222150201e5100c130713010705070111000060010686044203106020000c40d01012540d49924800300103005580c0d503c1241c04034410501d40901c005800c015012142c0c00340404039000310a401c0c20200c1c0319003e40d409880711003890b920034095544ea8106024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 273291438 1250 273290188 273290191
    0x1401020a0e0402090105070c260a0503030403211b08220206030726270c01050a110613020324060f031501031103071a070f060b100302091503 62
    0x4042401c401011207649040d6014003100701040c1001072500e013641d581d030000d0400d00c2d00f04034000c0300084040501ca44000d040303080450103040041144103425110103640c0c1c00020001001c002d905000c0680300d048001008804481c100c405100d00c1181000c089900407001e00003800280da05000104100c90031108104c481480c0740040100c10055000d0114a0740028290028811144c1c900030350202c0d4955182c40e0b00144007041e10359400c100300c64080c80946800500e50108203145008694103020840200c2c03d8802d003080c565030300e0a070b501614400c0c101142a1b603540035102c01c0200d41c101c11413020100d01c0c401c0f403c2d1030008460250100700b001e007089024040d4030700f60b00010480d050520440710303070b00f200600320b41c0840a641a5400141400d0700300b00c1d000349107003c0c0c48009040030071620010f072034160066480c83d0b5040000740d403540103000011b4000c0c44010b42c440b060060980c400002140d01615050714480c038124060040c1d4004680c0500400c030440101945a40c04421349 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 273292688 1250 273291438 273291457
    0x30d0801120308090111041e05091015020c0a1211060f0f07050703082101050616021915020a03080f010e0415020d0203190e01200a030b030304030609140102 69
    0x15903a8015600c08541014004001d80b03141e41d41c0300346d12003021a4100c041c000418281c1ca00d51190900c0c3c0d00301f00040021507011780e003e02e0300341044c01850f2025060352070079160480fa44c500140203d1074124604548106c000740c009100c3c0c0fa0101d416800c64109522460103444507841945c070301000d000d0603205100e07066040000910443c910400c0c000c005181042c00389045030071550300d0b0307101c1d0720307203a03020900300701c0107203005070707000785003e1110300103500520303040394660305100c0100017048403011a02c1000348507e20704a549421010078262000140502c00410480e1007060701020b5074458042109401103208180041c1041a40001e4a0306031110701e040c1850030384490ba107d6040a20502040403d035400340500501394801d8400786116200c506d880d2043d100031b000d240c0c1c080351440d0048404030707410009102e41540302c6043d00c040c880c504096036a510348080c04224000d05070100c1d11541800000340c00414400c55801010169009980c80e8848041c1e01c0c0d070030f078202c1c882c40c03105 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 273293938 1250 273292688 273292709
    0x103110301050f2e15020102031801090201080c1b12030a0e0c0330030c03011a0304051b0301020708120f01060c24020c19060605060403110904020109080a050309030d0801 75
    0x8013501302c11a80000d4085080c6079044d0040c164491000003001c103005100c01005079804030400001105444002841c03c1309040200100680c030340008080700300050040200410005810211481d0060030b0421160f03030f8030503285481c210080c050386035070064078181440c41c20600d03c0d080400f00480c400300040c030000c0c0104101500500540e050100c005503102040307000785a406800c81c00f0b01e0085d441820072025440c0d4030760401400c0a5810740d041c0c68000c8400c418410400042d200090385540c94030070451411398400200c002a0180c032a40200030300100e0301040c10a250400491518081c1c0c469002d1402c043c3e8886404840a4405d80e03005404580842c0c4070041d041203c080f5008002521a005441c0c00c1c2c01c035103141c2c80c00c0001803880381503450718140041400380074070401d07000d00f00481744240380900d15101d0308000c11100316468800c40f031300c40101d0f045a0003044600014520401590901c035414209241c8030341051289a009014000d003030720040d0b11916140e41031340c086164 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 273295188 1250 273293938 273293971
    0x30e01121401050126011518030c080d14090904022407060b060a0207030f02040b100c060f0b030a060b06070609030c150606050304080d150906081002030106140a050405090103110301050f 82
    0x140840b41c0c000441e01c00b170501c40700984143d141d11031808d41402035030060944803503551030721000c146011200003900d4200100c2c2c220820305228080c3c100c1e1100041104c1896183d06e030f600005289070034405903055001d103502c9a500e07050384030340042d000581c003504c41000307880660030030f000862160741c8100700140c200303100034000038200c9000507501c18000781c0000766015446c1d0116600d5040d11003164003051030507200c2c808001050042c2512469521014007541080c0404281d503000b09010081c12140c41d00380e62001038540505035984950060b07c14000d101007420042c00d410910701c010748000406003101c004808503070080385c045907460364030103155079216100d1908540105049902d4503498481c0d41300d510345c144802d1006001d080304000348162804180034075103c410342c82a10700a00520040205d10b80001001701c003164101000350b0342d0300800000f00c1e004d2045400c002c2c0e100e07400340e00200521056501c00c9000c2c0303105030000c004640325441e4058803003d00b1100307210b18019800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 273296438 1250 273295188 273295199
    0xd051e2b02150a0e010c030b04050a140c0f0c030a03230609010e09030c0d0e100815010c0312110d0b33040b030f090601150c030e0112140105012601 65
    0x1500d0383e901038501440042c0c2c0c0b03070003c58030303d0079a403072404180d0000c2d80301ea803061640c1c078003889101d4109070f00c2001041242140b8520302d0180000800c03450b81184003262843c01e00464000b201c842c040305a040c2c81e035900c083d21025005000c48610b500e400441920300c2c5413a0b406003400c03a4010480141407040740da21344484480d858200a0000c5d07141d000902400390040403c105130b103d54141c0742c03a010500152803040c00400710010800c034080101c1c450600c0071842c07003042190b820013028603000c0c0b16a54142015102079280d4043d185c2d0311441c1000300300300c10041c0f40141040a1802409010074a5040c003089030082d1040c501c2129034200303441102014401c840d544c08010102000e690038242d4035000c03071069030021207043d005240c800e800c01c128042c0600142e809014600c5200c070911044180007232641113030300001402c1c805a4015a1426130082900a441030114542030004048018002c5580f00f402c1c411a0f000c120b140ca55003295142c940780d0141e40140182c404e41243e860b00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 273297688 1250 273296438 273296473
    0x5070f031104090c05090a062315090d17070605070e01020319031e06031205040312050d140403120b0418031b0816030909050708060d051e2b02 63
    0x11401107a130070744409000206a1200d4a4442c403403001070741c0c0011454604002003401040981d4510107140013400307800102d556440c01410240307048154103850700e401c80c01045013000103c3e00505600d002c1d40b00a4042e900f00001010254440d0400f441a6283c800c3d0540786c2d91084c0c030845000d41c00c1413084140d000b00186144118410718038011402001d02e00842e410001c500c11104a07072a1030f01418400d0010118640c4107200d03140c50304ca80380a2854881c2400466041c1c001d0341001030008140440c9043c90304180d03035400300740919000508082c40c0283c1841c61440f1400440c904080d400c0c842e9103003074420016070503070203001900024280e030780c02c0b40c500d40c1c44494901c0e0602809032081c04034444101402c00ea00d919408031803202c249060140840106620078000c0710305000800111562005213940c0058040d079156100c10441d07c0d04900f00b0409900030942c1c0000e88444d0003020100044401050500800d50b0640c0352264900410002d11003903a0f1015a024440c1d8900b060b100c1d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 273298938 1250 273297688 273297701
    0x1401050706090b0c1815040b0304050106030215180118050103020a02150103032601120605061c03050d060501020a230a1b030308060f0901060f02030d0e01050405070f031104 76
    0x14040002c1901c81690307000c0d0002000d4035120298180465006010352100250b2945c181c01118031009146440161100600c110b00854264010200104c0c0801500350480c50140d54003d0030558030b41103c440c2205031707400c04d1100c00c0344412805008a050350107044180002c5696038185041c00d410311005401950028615008601c5600c1802c1036003400120090b0113941f00341d941540500c0c244912000c90f15604051001980b054401000f801c02c00409000c0010740c00000440c8554030000015140c1e044042c24100d002060f40c404070030550b0003001001054a1000104241511403004a9650718200002095001090740401c00c510352041900b95001c2440121440c11407160b580040c904401c132000030046074080c005008054012000e140d01a0301542d01c10211118140015808207042c45a0740a00c200c1c1c100c00400303248203000b00c415504801000303100003240c40707032804e00920045805542a003d180000314190700410755040c2100e41201030420111504010000281302 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 273300188 1250 273298938 273298943
    0x418120203040314030a08091f1d06070306050306070201060305100f060308040602070e01050418030c0c050d0b010e13052104030b0f07030b1903061a06030c070501110414010507 78
    0x20301c40000020748084c2c0a81044008101464440002d0040036000320720250507a0b400390480d4038494a40d003c00c8140780c01891000f0f02c00315940384400f1110b840e00d840e00d040b0801d140241420000c506030590420000c40c2c200790102c43c0c86641d890000c80c225070340c50100401580100540c00c02c5c03040c45402988542c510204002419aa60b5589175016482070307000c400541c11440c07040051040c510b55083c01080c0c16902401540360241e01c0340f140d2a00c8000080a0114110b0b000c01840250074a1348c028050142c0b0000303100c2c183d8240111590740274400e80ea04020b00400007802d103088070700f42c500c40a41c80002040060744610f6110110040d209034254003403000e10000001c1409550054068035555100c0e001c24180781100909881071214035600032171038041440c66452140742c0310405c490300302c1c40c001288030103500407244d04024194266401000401405020400c4000903d0300303a10031002084090b00d60510b07a0511300461094100c0308103400b114000550140c40105440c52 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 273301438 1250 273300188 273300193
    0x31a0d02040b0a0303210b06030606031008030309010f110703050f0a1b08030702010b0a0608010b0d11070c15080108030409110c010614010f082205031303081804181202 74
    0x11440843e41005455105500013402c5100c462098480d494201009001130f0209024030200310001c0340712480054600350040f680080050000158244503001408444080e00d03a28148011514043d107aa80300c0c01e8001454611201052800740040f038440ea42c0c182c503194104a1032010300c1565401002c95502888239101400b240310360483c5241d280c1901c600040780d120700340480c0090840d0070185040c0e005800d5090144807035600481c680341118540040640c0c1c4031080855203000e03102000382801c0310300011662000300007a1040d5402610100501154002c01108080718464403e1040c40d1580d0003c01087c4044e000541009402e80c02400d41d072880c0083d0203841c6401c48250303600030700b40c2403201e055403e202e60380201151090380b414a07101045092102042c01407808207840506256460241c120030060180152145450350040800d00281d5038203105190703a2004032000039421600c0e000d06003500e402d215040c58103d06c407200180702051079035031070a1004d20410810a42c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 273302688 1250 273301438 273301451
    0xc0307450917030a020d051810052d0901050903130e070c081c0608030a1b0309030b07120c051c051512010902030f010b100e150307080412031a0d0204 66
    0x20908600540c0500c400f81130050307592000030b4409044610103455244043c2130504035a4010000082c00300030100c075480e0000f03190303c1d085181142003080c04140c4a5010342d07000740c04000c5c5828103410744220b8812009125681e610003680b074480c81401c5030845503501015003805004001261158441e140c0d04207481040c501d40c5503d103640c0c1180404039440c0d8000082843e0920700ca0040200810740d540055042100041002e8440100c040b0f078135a00d0070030b9100740c1083c0b51286404400542d00452844205e040c80040281440090142c11a60074100198205d8503071240045030004039040c0c0c444050100d00ca041000030b04805441d182d105074400c0d0501e250307a40c03034181c03031710300c9a00500002420301851b10605080500060b0390f0303031141c0d1404c058078059441c2c246520320b1551380340c500b00100d16980b90001d10051417502c184010250040100300100781c110007101c1c080c90165510b0358400100790f4085040d5091101000f41034030820318800e805003403003640060220b2000b4004500c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 273303938 1250 273302688 273302723
    0xa0f0510051e0409020912060c070f0501061511070501020d08041b0503010e03070512030c072402031302190609120f1a0f0906040305030402010e030c03074509 70
    0x60341141d0454030a0700c0c5e000444000914001c0f0189541165000207800146401e451150081c012440301405583c84044800c2c2040803c0d4010009001c9455410509120010004043c61156400718415114030f00d0045079644c00015901c140b140140d0307640c00c13641e44950f140180e17951504c1c2c9072a1074040c0b440e004141d035039080c060b03402404a15001581c039025a81032161600403850176014036150100140411050998102d849054002241124081101141148404885464500305840803081c0008801001004039171603001f150315000b00c60910f23580000c24034861040340041500d4840420141d903180b1000c00c03040340110203030024020315840b4081358003082d000d00c84000700440200021304900b0304802d0307007002c103042c01405546002d650140c41c6120140c000303414440c80c0e201a40c0b41c1d070750400042c900d05070050152008036a80d0051300d0307606d000404000303140305e00004002d0f0002814900030b44c5a0802142c0b0b4404010341490140d000f03003900a003c1d01c030041041c04800c907 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 273305188 1250 273303938 273303997
    0x1030c08011415210319031a0f1323161205060a05040501030c0807120503030609060a1206090203120c0a1203150b03070311030f18070f030f020a0f051005 68
    0x104004034024559440c030060000b505c60083e00c4003034081c5803070b000c050101d4584111000b8065041910414401c9c44060f0014001c44da506810b01c100a040a40c01710b1900d4142c5510349a918100c003a80140781c8841d1800061415961000800150b41240f0350741c51084940003190000d402070881040c41e0384620202d0b00ba1882600306944048030210100710b070000822900c80286181e5015129566a40e0f0ba191303285d21010b40000d101d141031034040f4583c0e43d40c031850800102000d01140000908038540300f0040c0c441d525043e84030b030041e09007020158811104440c022140100541110116503807640b200070042d665004c201070360340403a6062400c43c00549009402444615a1289080c030743c0101a11004900081c1c06c034000d2042c00310b00e220210b10280c00490202081c0345089000c00c8072884d003c1c0b65804040c111002c0351000081c00800454050349600076902a42010f0311030700918001d07616441042d8120f2400c420101100d4800c030043c1c08a000103114900da02042c0302035480 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 273306438 1250 273305188 273305239
    0x5030f043206010806010b0d020903010f060603050a111e070f0209070c140a1203020304020d0c090b0112050f01051e0a0303050318010b01080105190b04060801030c08011415 76
    0x804000001c903001055201000042e004003004130040a00350305000f10450540a0750302000100750300480d511016550070b4200b149110501001040080d41e18100240900f0050320101d080c0ae01c2c03c1604c0d20207042d124111540c051030000080c420010b520703c5078200b03030700c000d40507a040c4007402100b07401031780c2d442c2c1914080c4240b036070b62008107022810904c1800340bc15000301c41943c004d95400000030b200e040007419901c91400c006031642e5850010802940c24500010820040d480740450301d0b20385603101210000e000e1f078400c021351010b84048001c40e68181e03400c640d00130310368004201ca8580090051201d030700e400250b020102c04800420000c2e074081d08103d01007400441080850643c0d44461952100240c0082c403c0085010018100b40c03010700a15004420441e050101c210050444034020302c1440c1619564036a540402014920280001c035145d000035000041c0c0144140202000c6802d5a42080c0b07042d200c01d4062030303141210403015034000d001090801030711103402c81d104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 273307688 1250 273306438 273306503
    0x5011e030f060311031203150d0203030714100c05090310240e070e1e010f050c06160207060903050c1309021201150617270a030c031b0305030f04 64
    0x3e8181541d1340101820303c14000e2644071400d4040c0108681e2400b00c1d078002554980545000c2840710650020030308500c524403000d001c00c86407030180054908006050281055060b504001c1481201e0302180d4500c20140555410fa12000c0c107541049241c0c0e2088a4841c84400e1307207092004000b401013146405036201ca039a441d00c00301005801600f000c4d03a5080c100b01241c0460031017100007e40804503c5801351641046000d001f10000c2c00d0141040328101412041107462514240e8190702112030341c4041500103020b000400100107025940500a4030350000150811007548003c0c0144410314425560704c1c0340c0c4030445500542c0340c2c9622021460051000482c019004c0300140e0004800b80d0310003010009005407000303c950015040c0c5410a0701c24600c100c01800042c80410001041c0d906000d80b4084c0755000c200b01601304022600081c469259401007135840a45e0098407102c45001601003a030400018803040e5a580d00e1580c854030800c106c96124402e0a004951101c06040c0d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 273308938 1250 273307688 273307703
    0x5030d0b0406180203220206030415020c0a05070302120d050406030e1507020a0b1f0e06060d0c0504090f020405150a1e030e01051518040f02030607210605011e030f0603 74
    0x14030101220142c81e10314000c601b00c00b01c2140c0501c66012541600c0024009030172210216004058060242c0449945000792012150700900c1401c0c070030f40b11442807004034440c1441400300c4041d203a003c2010000012952034183c140340c03501000b900605a0f02c0303074040884c002c0410442006c106c455100303000e0503913076008000e1140a41746c6551000000313001001c041200d20f02d071780325003401e49001100351000c511120040fa202c80f00802e00502030070340c008000ba400c080074686030b1980f0a001c3d00c112003803c5000e0128404c0780f0300300001c80c8514042c0c6d50f0043c0d800d1200800041031072000b4a220340117071900d00c403410b60401d85040000703910000030300083d85851403c84d4840b401d02503180c1201c40313420007148501401001600d000b44010107000c00b044034400203424804205403900f030194010f4190341c5c032898481030003411082c0310290200603d10502000c040300c1703420300c100003d58406858840d01200c400b040308404800c200410001c06442d103041401c0d55025014820045108540 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 273310188 1250 273308938 273308941
    0x3011406011e020705211b09060121110c0d03020c0703030e03031b0c0f060405090117030c010e0d09080a03080403081906080a0b0906130204050705070212060105030f0a05030d0b0406180203 83
    0x17003941001e4007018031003109001f46102244968507545000e401a109007092440c08a0ba400d2840928819045401d00c2910301050390f800d503510400102141000349003a20700c00303456250103078100d0040c81100b90181c2d10495050000901600a4a0440e1401402c0b2802c01e40e41d10103a42d4903003030b0406a00090b400400d905d0103d801e01c01e0202c00080c2e011143c4a040a06083c0400c004140510441d90b004860718650920188140100c170701104945009010744024034050030b90760404150900001110140000b903548000b04d50540303032030340c142d594820325140d50f00c00320f03520a006040703c2003569400140e1115501c103485840002c000e2070018240314001c500707010301c45400c0205036240170381100c030822204c002c44813070484c40103904840002e4180c0b1203040840399401040c4009406c043d00c0c5915040c1c3c0c00c400509175048410480803201d8000b0150b410710b031a00b5903090014400d510521a290354160503800c00400e928000c0d000269450b91a11302001ca80740310007035540f00550000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 273311438 1250 273310188 273310249
    0x10605030f0109051002250f15090f02040507110114100b03010b070609030215010902030a060f1409060d020603041b06030b100c0204111803011406011e020705 70
    0x204520034081c40c4030007002200019114030341c5640c0b0140c01c550189600090640b0a100401d03803001001c14080418694200603180c040307007200480206403400340e00d56007640c507095071a000300c000c5150300840c1024521103d900303103c003031302000e03180c001482400800c82c02a10024810160181541c01240300942811130b01058100010b0300700700100c1804000511010b21480c2c01c0700c4409a00010010f40180e441c14201d091515941640303040724468000044e0861203078020b1400b50300c0444040052596440180c1420500b07885100000654040078a485160078140d4590100c8050805031000302d483c1c0c00070301640e00860302250205a007103c9c0b83e6044100c10b10b4140038100908080001250b00e60000301c500f500c8200c44003c010346840400c0071511150040b0f1502c051581c041038451038145042e00c04c0000c0032011901a44c40d0900c9103034541c1131042414089d69040c0c40c0e0090541c200d403075019000907160014000d40c03140790000201e80d203030912220310155810506411614491 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 273312688 1250 273311438 273311443
    0x11e050703080c070f1506090203070302180a080c012a0305070317040309030210021609231302190b1306030507020a0512032a0c15010b03010e040809060c01060503 72
    0x290080e40561002d015810015480205640b0420f400643c0c2d0440005140042c8003d0301c01f903000361308841d0003c0b013406801034064020703110824815890700c001c2103a1b0018030241d02ca1078410342400ba4001266401c140d4007444c1d00e00000180a4100c3c40c1444404586591040d501c0303038200c0014000066030020b0650049008191000d0490700c8010341c2030039140203207500c180d404041d208034801501c88404500030048540001c40010310034041b16501d107000d400030a04e0118000d481c03604d03031049480f41140754503410b101d1054901e940e0b1203601d40385c091000401c0b03810050602c0b21486c100210340c210380b0601800035004800075000c80c03e81001c1d001426504e0140c8003078159800298084001040864100701103183d01c0e0280d45c0340c3e07030344118085a841e4081001c4024498000074880b8450449004100040c034038400ca07403040709030100390350808400344510b01c41d0f010180300510501580d04030b0070760410f00a0f13019500380501580050b50030f0f071001c1c020740c10603950b5480810107400c06 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 273313938 1250 273312688 273312691
    0xe01110f07030e100504090218030d09090f020a08130c05060f090301060e0c0a0305100f090501030b070f090303050304030509041a01030605040b0604170f011409010e0a1101050306011e05070308 85
    0x56a113685800f01c2c11101900724011070080d145059008955008103d514011005011400904894000d41000805404d1500500034030b4009406c010713100c2c034500703024000c54108a6142e9186113046d03540340010041425051021103a901002900040d203030b840300003512641e0540d280c1140e88041c03800c00c06084a41c03d901c002d4603140755504101040c055203054035410300703190a0108095454001d21b52580380329400040340c02c0402d041c040340350341d40d541c40581600c0c8600c40900359600c03450b1003506c00600c0c080b000d000050fa40b80c01440068880c401854019220313040c12801c00072903000090948441300280c5c2c40c21309400180441035a8180902c0c07008007415103041203811000c0c4003049846c17180d40500c0745d801c071740b403940f5421b40d1300108880000b45500c00000c10840e9042d881d4460107003019160789d141036081801c4444034200104001500d103912203c13030b51007150054010746540d0401080281417040c9516500742c421108002d4a100c035005585d0b01e0b64560302890040e105800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 273315188 1250 273313938 273313967
    0x108060a230f10030501180302070e060a0621020712030c0806090604022a2a030604060f2307030f0207021318050d030b010807020105090606040e01110f0703 69
    0x2044054000340d501c030321070640000c00e03064020b446a031048480b041248942d48000d045601c1c0201541c06049501400c0054910035401c2d1102c256840010019207082520a154400d140c000100030180c0141e1103400c07011900301d211800354582e8020b1000f2a00015019250403031200801c42c200750745031040d141c2c07024890030078440e6400c213500071a03801000107100b1070103a5400610000300c2421405607552030350303682404102490782c0301d09158581042034800445d14546000f00a0310060002c170380c13a580311002d001480142d0f0f581d2159070250848541d40340bd005e13030b42c03a800102c03180e24581d0046140c0c200024004642003401c40202144d40404042c942c0310f2060001000580d41c1001d00401c1905070100490306440da40f54030211001c1d8007000611501c9164a0584081c0c0c00d5003000070442400d0b294900e0380e5071500001c0e42a140102c2c1d4000c85500002c0000d5002d00c0c156000e40e4104070b41c2000021902d84070b06081d08554007642036141c3c0f046000c170744081050780c08801c1c0d040194 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 273316438 1250 273315188 273315221
    0x1801091101030f1b0e0303070f210f0c020108041a04050a12090b04030204050601020313080a050c010c0503090108040804050a0f08190c120303091a0f07020319081b030108060a 77
    0x2400e410100790700d10700050300701d00f0445c040c16504d41e0b40e40c0400907a6561034000366910f10241c03861800e0b04000d401d4040c81c56098400601e845d0440307000d0312403099494501d0711031300720341c11302d503801150748043c0244121070410380001085c0c8030f40458032501d44107034030860007802018010b00340488840080012001042081d210a01141c0d000b0001d44003140d5040c1d40c04501c60715442d00507803c60054a40090f19114071610029480c00f0008c2c600307148c90b02800a407170360703041c0c000011901c1d100c000c2e1001c1c110f0360081004c811254481c06807541d0090192206030305190b186c0380001c0c4181040d42c480308183e81d04250502030b102e414400c0241030030701034800c80010b982d55915013040c03015601c10386a0b6210310348040c4d018103009400c04850303613602000c94040740c01200380d98108040140c803084081c2d8040000103e5260000088510b0b21003140003144004940040848818000910701a041c812003080d01101354580c00c0994040e004107000307442c080c03520000d500c0032101c040c541034007000d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 273317688 1250 273316438 273316451
    0x207081b0103020708090d3504140f030f0106030b0c120103120201020d09080a08062409031606110d0f0806040b0d050f0102091203041d1801091101030f 67
    0x120166080c0000000c000e0801503102c401a091900c120301a900e00a034100c00000c2a4a0800c90100d1150889035260516a40c4012140c2c007049100b80d001101d20250100400080c404100d803810804240354000304041b11031b00030800031a040903010b450040c91613440c0c41041c0104020002d000d68411104020030b03013840d21a206c0740b40201c1041c40050202c91103001c400c0086803003074045030301e0201c11800030310417035545240c01241a80065000d0380000c00000c0494120701d1700050141c5a50f00000c0c01d1040c001c0e411003160039507842408400c1d13062240c2c01845c072440c070144e90308000811035900d4402c81c0421404810303017050007007604041000700d03013844c080545800c4031540e50412000d40300009c1200c0d607240440c480786020080078165214920303801080d00340c1500180180b0009503421010b140319503100d243c1c1c3c0d000300e0042030411300034400d0020074032209591303066015141820711200c488400f80d080d8210b07181c0368030580d0700300368104685100c2d5806001d02c0820940c69901005070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 273318938 1250 273317688 273317713
    0x18090706080f0612210304110301020a120b130f05060a06171b0f03180c01050412150917040510170402010e010519030204030c05030a020102030d0e07150e01020708 72
    0x1181401000ca920461004c480c480c4800e03404c0140516400803002c61142c00940010522a550030881d000c43c3c1880d0302c2201440681018000d5070004100b03034413060f541c42031301642080030f064504441a04503401c0311600f42080c28a000302c81c0c0300c0101d034800085500b030080602481d4080c54004a050100082803982d20090000c02142e010304030410344e81d826000d00075029128410181c030450030000100c00d2143d000480d911140c5500c4c107100450b50f16205040c01903c1d0f9000d5032040d407850801844062000c68522200440b885990307440020340001140e5a48245109103104809100d41c046000d1085041121034004542e089080c40e10711601055074071688010b0080c0b001741000022102940a0b9003d6429200740c1107034501e1548400001410060003500706201c01d4428071164003000401d818082031518210390107038050b51501c10340c1c2e080030700038082d0791800d08000e2040210004683c0071842a40c0d12284466a5402803800001e000910b0300107660820b50280c0c008000b21000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 273320188 1250 273318938 273318961
    0x22031d19030f0f08070b06010e01140d0b061908010806060a030b0411041104300b0708131a011701060807051002010204030501091a0a0204050a0302040b0402091809070608 75
    0x220380c0d01c218100c0c00110309103440c0c5204060194020303c095008960a002c00c007603450480e00c07e48080c1d89a00e01d5501c9080111588102d41492b901c0b054804c0104501d400d1960704222840040642131900d025412219252035800340d6a0f9500003620041c01400000c405000c030b1500150202d5041c0740141c02c50f15001c25850001c1c00003071611100c080c1003038141d113554100a250750024003085882d0b0799107400300e1018107010804440c40e0594140282c4000303001483e500350303d80e0440a800030b242e648550507500600007408940124031900e40400019201002607a10880d84500c0c06005514115000305110b039111012007660341048424401e1010004040041b128111200420318480b410241d00910450b0000b50055003008040401e0008080c09800b40b806c0101400c40541c0d1690302d460200e018a000d0b1551210a06104202502d041d412000c4031413401040145000d49403400542d200b003100d042d10f1500c0c0c000504101415206211040050a050601452070b1400f00038980 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 273321438 1250 273320188 273320239
    0x2120304020102280b0903040503010e0a0804050103110706020c100507170a0506010c020909010b09072a08120a06050a060c0f08030a060503030a05070b100312030522031d 75
    0x3440c2013a40700841d040d43c218943e40e4415811800144035810000d40d40c80c1c0300e038494000c1602941c00c03d60404002d030800102d8070607980d0000c24050a042c20b240c0110f015040c000c01d62111b1a00070f011000c08910070340700078003412542900403c2c044c8858074601c01960720041c801800d20000c4030500c0c48000d014903040b603100a02c008002440d644640058645441c81c80e00a50030600c0f0108100d00d001c1c056102c1e000341c0301e003161045050780e2102400c80754045c074999502da5600b905024111340e000d140c2c00e4054050310600b8282c0c1420b15400050f046807504554001215403664020043c41c00c2c141000401341c000b070f1034400d803030f04c6241d00e94003210450f030b0b01c000741440000400980284647d6101c00301410b40103007500e5503483e00c410010b000d50130000041c4c849126440c0071030604607038801560101c0c0c4e0b200c3c43d901c00c0c2403800032098004180007071101072510181805218400411044100c51500c6074a0303105156076103494603d40500900145401200390b1011480e6141624441c0c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 273322688 1250 273321438 273321463
    0x1a010804030f12020703020606041d03071401090605090c090105101413030501020f030117010203061503091510030501050a0e060417040504021c05280b01020c0a090c02120304020102 80
    0x41d840c0031098142200c03c801c2c8403d040c191640f01250440c201940403c15502803002120140040e42000c200008103880040d007084907a8020010b5a0002d800051300002100340c0c0c1c00000b80700400d5480d5401542c0e011604902140c0115030076588900d00070300694050a410348180000300c10f80c0e5000740c601105184d05030380581000c0342d01140001a0002038010b10f9201e4002e544580c1c0d07030362403900c00e50402c0c001e128500944000709102d0500501c01c0c0c0e84103c1c401040c0907c190b500e840e44100b5980080c00c2c0002501512450944005a605915000c3c55488440ca80340030f01d18240a42190b901074119241c6d1420b2110980c80400005440d68100f074114070039100d602c54a0700a86070508c5658040c540140c00420b900042d01c0140341461600031450200344117036500d6400250b01414600000465404c41a800c8807240650b40d018031500d450600449100c0b0920a0014014200b41d41c020040f41d500e4520001d10707594144007952240d2048203516003541010390000c0d450b82c0b03508528 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 273323938 1250 273322688 273322697
    0x60906040b12010e01050105030601080d050901120906060f05130e0706111c0306090c0e030d050c03070b040b07020115060801030633030b070c080f030604090506191a01080403 77
    0x1510040d9440129030b520300034040008100d90480107091a010742424414980f11380540c2000094a81000c1004054280c81da502c041ca044240307401554400c4560481c00341c2c0e61741d22080100064030621030103000c1c01c601410304480510b0682003204400101c202545107030b00b80070440d000b006002440d00140c0e0320b00d0402041c00c3ca9462006440d000c002507500303444190a41400c2000e03909544104291204034805220400a20b201601e100c0100c1c2c8140d600b661014503000200c034410300140030680c081200740c1e0301e001d407161581c680d0b031442624141c820003400c00c1400302c0c1d42e40912622a07042d070030742404050145890340c00780006d0300501c4081c1090340c46040010300820403c46034a01c0200c4111741460402100610312040e521030b010071036040f45140041002a07002e03111031108170354403002451803c8010300c0c107540706400103041380d900691101c40b0b61000603018407181c2c1c401d0079201541c04040c0c41c40a120070a44a03841c1f01c082c61002ea0b2040901140d03804108240d000e074141c2030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 273325188 1250 273323938 273323951
    0x20402070503090a270603030537051206030601030209160903060501170f03031306021305030706120528050402150f04030c091802100905060409020a110606090604 72
    0x107100782544102c0d0300300b030760180c90368401150140c1d1710031415200e00c607200d40d12010f4042482c030400440d0520301001d00810000c1c00840c1550080c0e14a1502d030214803014402c0700350b03c03650105040c800c2700e40b403440402d01c040f454501d280040c950a0342e210804030028842540f6503000708101c00270240c4030412041d4402a41140035002e01c2d1088000c6521a404221643e503e80c43c4102040c130741f00e4600c4590064100e40d91343c0c400000103890141024585a0034911040d03600c2c60004c0d44240f50340652100c51440015103a982401900d0007084a034440d50002c3d0800300482089032402044440c860a508040201220825501c0c00c0000d950300000241034885000060076261a204071100a45c00003a5a040d000703018000307842103912a40c000803c10b0303265034062099428148000800001c50b94001c0c02510b4590403220002902d42480c0710140d03119804600c46a010343c015042c0907400280c2428590340c00f982c404012582c8078050318283c1408000030703640d0313000902046c2c4515200c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 273326438 1250 273325188 273325193
    0x906050304060e070f05040513030813030207081c020d02031204020f030a062a0305040215130902040603061d060a090e01020903060f06030106050108090a1b031401090204061a030402040207 83
    0x5101d80c3c1c0d50303800030741119155513581c07040c0f86000782113001c1c0500550600000c900d2017504024403189040c0c0c5a101c0030481c1d5a4025180d0506082c5030f025011071007026070000301c1050a0100d0305c2080d1600600ca080b101c01c00300003030316100401090800310742c010000080041e11540116400590407205100d12440e2040040d20300b666849015002510b0090303503581030703d013181e40b003101001d14156140b52918940416400c554040364043d400030400c064020b038403440003004003c6543c0b00c21551664589034070322081242c0241e00402d0200313946007801e02c503409440035040d4001d00303800c084507c1c0c1c1c90640007003811507407a4443c294540751900300d90902400c003901aa12099000b80071910503252032111243c8401c0d0035a40c0c64041e5203807220100300c5500c14103110344581170740002032001060f0b80d83c3d91410701c0d9044112b9005030a0100e40400042d2500b6040e41c09080d4800001c640000140100012105070381c2c440040c0c0e00303071400380c403c1040618094070ba0054048800688a44050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 273327688 1250 273326438 273326441
    0x50906090f09070801030311070f030807060e070803090910060c03201506040b01050301081e0a24051006020d26090313050103020a05071b09020d060503060a060303090605030406 78
    0x10301d495a0111a4008010140307501840140c100c1c0d0095460007040b02d140c9440b01e8903243c0a001b4444110303080c0e001072000c54402c42c02851090f2140e00002501150140d9190038107100b034020b40515000042c081040d45090001c0c507070000f880c030f10f07045647d40c45d0107006400b80000403401400d0110071080755001d010b240e42558401004203090b01c0d00f0060342d110030300900c0c000700c43c170030b100c0c602c0c11019183d00c3d4450000d8905039134000c00208501081c2108103280614404402c1c0b8082c4502540840003402d961441c402d20004603c0c261403440400703030341c43c0680f08001d2403241e0350548003900304100395000828156000075800d0245440c40e88402c1c2e4441035005110b88508014000c06000c28200300200034036901d19011440c121b110b4039200110264802c074041e032000128107100800c04240303051203444020301d100d10b54080c86591003038404183c2c1c100109401e41190340c0e241c2001071741014800303181c0c4814154400c108043c00c40c0e81c05042002c2900409007005004000030707041100700e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 273328938 1250 273327688 273327709
    0x190e010201060e190f0b090414010f0c050a020c030105040201021905010204080a08040509010e0f0f0a0207051222180e070b160201090902090a0303051e041202010e09010605090609 79
    0x407109412140d00d044c20070354940031050701105a14900d01039039070b483c40c0300900c288640c500c0300030440e80c0343d030b241da0301c88010301c9030414420441c55684100d0350251607110300c1000c500c0103841c0c46250304d40e15030000103070800340b40400b5140264100380c20400181c2e8081403200541810051000d0448201d043c03240c0240500e030000003083c403424026074240004040500100c03070044404540503032325204102807113441520a0780740170107a000461148020544084e500100e03d0800508111080d2680c0d80f41c1900c4045166401c0d00c00180800f07221998825280d4852001d4602d880343ca00d402188010040f0003001c0040c0d065a232100704c1c03880f002c18403624009158079080c041c0c440c13404204c4170160900a4500b24041040c0349030004000200740261109100f0080c01814014907507101902d05601141c64000c401044051034091081c4801c01b804c003818113007404103070780e000301e1001600e16030784451014410741a810040210b10703070190498800c864103554280d16130106002141c0400352 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 273330188 1250 273328938 273328949
    0x40b0a02040f0e1006110a031b201003060501140c0f0d020d200a030c110402180418260d02070308070201061410080c0706110d0b0402190e01020106 65
    0x6030000181c2642c41003030a90050721380e0300410785455510304040c0d5075078000042408564210011460201e8040d004039048003c4d90088104010440c0d554040d01c000e030003105024484469034440094200602500018107960801700706440c14600081c01c034104160380700d2010440020621505407052018038840071103039003203441070005100065160308140c0403042c0058102c0864000900c5001d485a809200340d80160080e80c0158604545012411000f5a01200e0300c171000300c410f8035607200910705802140400d2405180b1481004151000401c04410051006003208003290241480c020350003548000c4a040e00c480381580300742d0380515902403d44030310110b00d480605403c1288903102c1c90140c0d0003001829103602c1800b4010503a4802581c10080e81d010002c0101d0013012813540028145003c2820040c00781d580d4020380b501a0040100ea240205101400c0d000350b000d6442c0703c0c4000c480550030900c500b41009185403644140c41c04015015292000c1c9034001e52050002d017a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 273331438 1250 273330188 273330209
    0x6060706020f07140c01210605120c04050c03010e010b03090f0604030309060b0901180c050d060f0305070906180b0d0501050f090d090f0b0702131407080a090b040b0a0204 75
    0x1803005514180ba400c004410380380d0b81c50200c060130311420045901d020300304050b1544510300c40d801d1501103044d2481104112003a55420021820340e4950b81034005e10402000148041500c0d01b06010a903580a826001128010300040c0880310b0140c05179030646141401c120f45a50b14402c14610b00907501006048a000c0e0100b84030515615401007020140694414001d0010082c10700008400900c0b035520840101c101309095044d80d9040984030448925010782480c1000400400b21882a0f228010000380c602d01082007080600c0303503038000c00403460100001880d1090760f01018208050546040382c0c2c607014803070160303956a06007444079000b40c020040d40c50080800a0081d0f0b0590300780b803091050142d1300803614442c3d0594019202a490310301c080038034040c400e01003900201c4049901003d040c0d04c0040c0c411181c0f05440d4002c0d003a1466241c0760a2900014101d1103014003064019414000c80c240840c0281042319089a0300c40700c1e04000e0f0340c1d80040a0700a004a070010004075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 273332688 1250 273331438 273331447
    0x18060f040312080f06030f0a030509040e0f070f15020715050f121008010e0307020909031903060f0f051806061b01090b0a0522030504032a08030f040b030606070602 72
    0xb282d000788400d108400222444026446520030903a03102c0807120511803a40c404011400041d106d00302510550310042c0001c1902407069003140e0a01c40300340e580781807a900500040200004030b00e4404001c0210844001090101920094841c4680c0c000c0300c1d44050300e440c2c0004090711560403551107600d031135407003034850030390001241d080380c015104c0348581641070b000469080418031508201c6a00c280003103251011980c280031104500030070081080c0000d11001c060210700e9801010240d1055900141b11401c0c0107500700b04600a0700603040d00f44201c0c1c0d0500c001e1300c56200105d02c1c0e44ea0390035440341640c5c80c040090164801d410550001f15002c6501c500038000540120304e0b4148a445100000e50700c2940c0e00003142c00c1100c41d110000c1840a00e291401c222100506846000789045403605880340c40d120310040035180100c001d0b102010703884403210040c140c0e41010788208400f4603e488000d4081c0e80b030703602650185840300c1e0400030224807255221002c4442580d032150095464 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 273333938 1250 273332688 273332723
    0x70e040809100e0a0f0b07240510170a030504090b03100606050c01050a0509030f03042a1509081e010b0a031101080a060e0a02071407030b070f030218060f0403 70
    0x50304a1030820300070385044d0000b140411410a02c0c405031002c01c0d20041c00e181d0750f42c54a105800e00300701010304040520380c101d40c4800c1d0700d004452082107403661002040b4a0912040081c03031004562a43d1900306c80441000613601c44c044804039203a0724000708884695000080c240405c0d000e0140700585082400604541c0080c090119070007920001c10003030f42c031040184159801169800c0040c0c01c200114541c1d52805005103030841c1c042c5011607801040201030a440755610103500c000341d12030b100c3c10040400c01034002200031040d4a02046100c0c50300d1104c035a12101c1e0440b00c2c075070210341c1c643c48a003040c0940c003002030940020410007410381d0720300f400c82d20310540490305400640b24000040c41804140146811101c03401800c0c00f403541d94902000c000c1d01b0440c801c940e4034102c03c13540320045104104040141d4080c110403440f41c10249006000c2c14180c0c00c00b42c06060040c0076640702c068200788000d5000a0075903905a40b8071604030f0703c0445100b0341d08001c001080c0750124151 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 273335188 1250 273333938 273333947
    0xc1201050a0b060c030906031e1e070507050a02041109060f03010609080d020601060c060b130c021902010c080309030f041509060c23100c02031218070e04080910 71
    0x411203004104140d00182c0140400ca118040d131a025580c8100007401860a1403001150302a41e03c0412485d001c010f0501c50401880654042e0000e50802030020341201554884e1900090300b402d00e146003214030307074802e40c803001d0700f51001c0c0c8200d03aa443c1241d2961b4007030007180c149500c010082076980a0b114241c0c0142c3e0030a01610700090080e14010038802d000003501154854140c0040050b03a20780303036003221004a0b03d041128200d444142c1d60317540d85ca5070300d6002201d04100380c02044454090000a01d4080325600702441c04e0294085540582d8201444008254000c0540c584c2d0799a000350462852082000301e030390070b1000003400244c5503200641500100215611701c043c0700d6035000b007201c41c55505940580b0070703100e8044508590528404c80100101c4036000c1e0303420810755800744412100200b0388400543c100040e8100b04945248480b40d01c9007001c0700c5004148401200c55960310700d00c0c0514001d410030031001c00c0038000c40c00140e81911400400c4c106001421040082 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 273336438 1250 273335188 273335191
    0x317150613140108010e01090e030702060a02030715020f07170c061e060427020f0907030f050a2f070f080403020414150112110304031e0816110c120105 67
    0x41d05007400c55000b1800e600c41c0705950704076620740501c0c204036400c1000b5440100320700410304c40c41f44001c104110042c2c4520000c2c15259900e90042c0d500e40781c0742e09000011000000d48000b0b594030410100c840c0c00d07200f0003a50015074125413052100b50b4504213107541481a6410b400c3c2500ca00300c10403142820300000703125803111a41d00010292960410f010035030715903016216000010182082d03a5100a850b01c80b0018002049880054001c40100340c411405541d0600025101e000c100c43d90b04c1c00d40626600a401c55808004041203a0040c1c50100083c0c1441101c45e11030a000040e0010342c0000d860210b900034202e45440103a030302c2d0440c100d0303019200807400b6600b07150f80145084402103170f492180b022080040342411812004454800c0d1000b81242031984da020403010504032600a144203503c29201d50074452048030500d010840c004080f50100103014003000250300c0d00d5a4841c000b20402c0c1041e154050582182c5810041d80b200c46942020703d03a080401c0f602415000385 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 273337688 1250 273336438 273336449
    0x501050702011104090207081c09021f0e01110c1002010b100e0a060302130b0307050a1707020c0f12070e0a110f04140406030b070e0103050108070e01052b0302010207030e0a030317150613 82
    0x1340e981589100716101c030984a01d0383354046941201082429401000c0c0075914032010400d60300d48446410004116481d03150300000142e40d07070315000007141000707164001c104540e07081158564521000165480074140200c1b010140c002c210700c860350030603200c03090242100d0a6455140c1c42c1c001002011600804000710005000c901d081c0c0303400d146e5404031400b8118540c060400c2c1e803032400034000005054040d451b00148002c40d8020f100710f0501660010707100740458141c01d410222884015a8048205134800090822016240c1e00b140c200f103034102c60952103617801d000740c00c20004004103620751000e01003100d0041000b94a950240000186040980b000c002603601c074401c241c0c0e12512030194001c02d00b101401480b55240100080003012801e1042000b0070b6840e9802403040c1d80c1c050800c40160b90045029001c058110100740310743d24080c0e0f00681c64920b1918000c01020880ca50068407022150200d581641d90b01100e1a41c00d0001e010140e580b1444601020085528801c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 273338938 1250 273337688 273337699
    0xa050f0a03020106050901320d0501150503030c15100308030a05100b0a0c03030f0e0a080d11090a030204200417010e010504020d150605100305040501050702011104090207081c0902 79
    0x445d11346400c108050603901e1240c5026030243d0300c61441164820074000c00d400d141200070300506240c0e500c070b15151990b03124500201c1d81d60150b030107100d0b0740030040d00145c0c801d400a2007049020700c00003841405e100350308a22a00e490316003c174030008560f0a50009013481c2d40c0001000b189541c00e40115029890302c515070300f07966551301850b107800c0c0114210900005d0703010f4141c0b80407a2182d04401c2d115102c060001601103210701a29141440700f034021640d94030b01056a001d0725207144a038078001c101c440e0072280341003482000114803010718080240f05a030749000c1d2241d1100c60903400c0d5640004061041e0b074680c0c850f000540c402c0401e4202c84119030800310b000401c10340600840d03004550191400524411a0ba14400ca0064043e4030101301551000001000e54661510180c50645910001800d09050522600351800140744105680c103051160301c0300818070084804841044000603140c81191402c20329a01c10181a04030120b00180c0b254901885e55002c0b01640d4401c075039 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 273340188 1250 273338938 273338951
    0x3030e100207030b0c0706111201031202060f060907020f01060b0405042d021e030c070204060905040b06060c0c0a08010e0c0306102105010c0f0e030304180b01020a050f0a030201 78
    0x8003241e0b10022400b0082c6841640c0010458101c1c200001d442c2c81c03445a80041200d4900034813540f107030b41021440170a0142100c2c010030a201c0014049500031249202600082c5000000d4406000c00a040c4038010a0f0000001e104d5502c280306401c0052014002445402c2c0e0390320035800b080d04a405000c3c452460035104500a500c0c6032055101414296081d4000312281071208009400078000c0140102c4400345061540501400851007228860b203020385a5501d401404220b80e003e80207503041e240f41c80181310100e01e400401076445001120035076030722850030310641c4c00c00a4495886422130445c2e00041508031040d00040038202400f000c580d840072100ac1015940c1c94140ca0301c1007010011241400541003408a4084104500c2c070014003600c07183c0d940c82d0840d1014454070f00010010751030200340c16400000d9a03401041100214209420421114424603400c44071914540d0340d017491001607402400000341a54004003a00c200c01c1c140144992500340d800000c0700107529140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 273341438 1250 273340188 273340219
    0x10c061b08150123070f020a0803031b03040302031804060504090c1802042402011506110c030705010e040f0e0607050c06070f050f03040f02120c01030501080307080a0c110a03030e 79
    0x107004d41c24041310300088000d00c400b03400e0080940d4051801a00c00958501051003d61150000803009014030401180d0320b02e130100a000380301600070807290201074100306000110313a002054500e400b10030100921111540400100100203641c0956082400c1c00524814400c2e00b02c040c8003240d018801103c501040240410304034420b41c00740b1144c141402d0b008040d0402c008500040701c0441d0300001840405d103010000d19900a07900280000e41d50400c50000744a040c011110750000540080101504100c0043c2205074010030040c01a5511101501c5c00440754208002030392101060f1000707810040001081c1d43d200c401c08080ca4824140481e194034820b10781002020056511181003200707665a01f405540064002d40c2e01d415545500809681d4420035104241d003035000a200c03d2820200150544d00140d20054143e0018014080400c803080101d501d00001450302c07107458101d80c6040c080c82101c2c0b040980c1c011810305404000c0603080302c10b186050034201c0d41c4051190900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 273342688 1250 273341438 273341447
    0x140304080a0803040c090f0204080c01031e0b0604032901060f2c040c120b01020105060a05040207030207090504060606030515011d01140c0601061403010e010302010c061b081501 78
    0x244200c084560040000101181c05071002d5500940b09909064510742d55082c100280d4003107442101d5540c0d8005000c0108560400c281142040c0a090901041401510340060703924032880b039140340d03502c0e00c0d0040c0300750341ca49040728041c5600825140250010000d0202c055041c00115190040c03402c1c00490110700450720703030816074040d5465200c02e1410034481011400c111000e080170041203605400640d1700d85c0510414152a9540d9900c001e841e03d19240070b0382c5181d80c066040d64508003d000326521848e0000c07060b69002da9025903603045602c1c08901d49031984d0f000d06a400c0c5403074203000c100040c5070000c508441050341d0502c041d0b198041c003104903141030405640803c10b800424180c04030001c5410b416080141807030f0304500c10205204404c0c1d400440044219049400140f00c100d0b000624920804202c66540b411581010700d00204d02c0301c1800b01034117101e1200c3c0510100092504a94441c40789181840703440b4020f40c1c00901040700030381da100c0140700d00700300500e84c03035104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 273343938 1250 273342688 273342697
    0xd050102360d0c051f3b060403080301031103100608031b070803040305030705070b0307171003020d2010020a060923030a020607090f090c0c05191403 66
    0x381c06074031020001080c01c00c0500d41d44603100711002140180002007990390106039004900030016100b0403245c4081000302190191140302482c15520041c0c0004042e00b40710415017000e14040500e11500c0000010701d140c02070b42e100030a0002c0001c0084200004a508e00c240718400303808446907400d0f8400d03003c0a5410710301a40c3c0d80740c0e100f44007012600d12001c1055150f0480708080d1110f0316110001075085601170b4000f80e45650000038030b04104002000050018142401c040e41541031401c1c000705410318868a0590714000500840c07041020b003850074006640c01000582103c249140001d0714405903403800e0516500c264800d84682481c90b145080070b40d10fa8003803d01c200342507440138001d25403040c1c10340f00c00180304681d00343e03507100000e0509100e030004002c646452074028000d241030341c000d05500070800c201c801089000041c03100700c0191507000760b012842c55595603007211f00500001020385140714400c840d0a81c1c0310a4001400140e0040c800d400701a0045020181e80c0c2c4035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 273345188 1250 273343938 273344017
    0xc06090305010e0a08030703050402121b090603070602060c1b0109110103230109020705010b12011b0507021e22020c070e0405030304030305040201020a0501090c0e060d0b0f070903020d050102 84
    0x101b04006000c40784a903008950043c40144000d00c1242100d040303514100056205480006000616900382c1c58860324042c1d111070200e00511829003400c00081d140c100262501c501e403003012aa548103002208040040c00594500030000b80c0100d081007091a0085000716010a28045c2403205800e03000c040603821600340100c46940d171340b0b0408031200a50012030180d8440d543c5040c202841c1c0c2d50302841c1024101610000b151403000e520095003180c2c811018a02030045c200301c203c00503203034854107150f248400c400f01c045900098021075118441e070300c10310105e100007030308007988460b4175030140115892030300444100d01c0c3c4803101c00584007410b90707000c0c016500600010740060702c00c0c2c10a0754000e1061050310003100e100c0e0745480c25146000d108071540d454a0f4420300c450000fa6840c103522002c00c540c140304e4245d458641340d840c01000780c421107100c00c80000140450b801020480022744d4007405c48000e4020506109000750400e4203904150f0040b15004140c801400805010285 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 273346438 1250 273345188 273345203
    0x3080a0c1a0415020a1e0210020f03060a0605120a02070309030f0c0e1503100c092705060d031b0203121305030106050415060c0201120501170c090907060c0206070c06090305010e0a 79
    0x280f01e1b003003000c118040c9064441184601e1159a140700b0781030019214038641c1c4600c0c5a222f00348241040029007494200c503003004011b001024407100e40c616020b801403002200107070350300c83c0d600341144c030340a441e00003515101040f420b5508100d4880ca81400712400792455405c1500d0315070411aa00828284466055002e002c0082040f15070341d0080114044c07a01340301e03900b1680c1e0012002e60001001d0200c5107821106803181e00389909010b12544190125142300ca404860390f0064010b01d80c45440040e20b4002500d40001c64808000c010400c9800c1c1c526142c803061249400c0c5900003903801388034002d508000001030903003480d014001660059102c00c24400307081c03240890b00c80c041c5034000d0b2304000d02d012000c0a0311034030344940c0340640f0084407191001803d44005134074103040d050760b590082d006a001c201490350301056910aa41300d51910020000c1d5900025107035018410000e030200d08501e40014119400c44201c100301d0344240c009014400d680d900741c0ea25240c0002c0d0240150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 273347688 1250 273346438 273346457
    0x1060f1101020d0c02032805040e06301209030703170412060b030d090b0316030905030309061803040b0909061c050c18060a03080a0c1a0415020a 64
    0x9034000c09010440100340400103091207480d40c1d4a0040d1100400b4030b00158100190b81180030448041050322139030b04c10700e1000719055002c0700614901c114441d02040c41040c5020540c0361345e4041400d41a00002c1000d40d40e150000c2c0600c5449044641c041c450b507105945004174030003e81400d0700c0d92040d004014241c814619100c1c10441c6103260100d5801c0102004013050300030200907240c3e48103000702000114030a400041c0351401c0c49a43e43c1c030003401403a00c41001203034a20412640d205203200080d0b01550029082500a0480700c0d0004006e40404420400e002c00c1c0000c640b0f1160440f101047c40b09125414800d88a203d40d000301001c4400c104022005414149002508040054090842074134007500025690031102c4007201c0a800410b04403407079151a05078104405d25914140c442414040e0003d0182c030f44900c40100b204c200499a5489240506001c4c0303840c43c5c115003079400c5001144408089440c080740d003101c81000421750481c3d10440b520a4032a05260f545860484 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 273348938 1250 273347688 273347717
    0xa060f14060c0f0607020a2a030219030204020712170c040302010e0a12120e03010b090112020d080a0512070e180901021c05040507050301090831060203070510050106 73
    0x741d074001c500901161182407900c0c0a5500308101062103100c65501601411003103250110b0001e4001000159021403c010552549144002982260b82c1103591041c0041110f8810700000410340c0080d60091001c0354540c24803c3c60104a901880c25a80d2028400b05110040900c0f80090f5000c00c003061003484103100650083d02261403a08000b0045660308c0d56550b000e1543c504031400c100ea13200b02c040b40f4488029002890b142243c2c4044000b40141001d20000c642c4141c1d0520440601c40e40c00c00c241c1055440b11a1400f45064100014964800800c00301a1640d403000581d074141c030140200052415111b1062824004002810008007403c2d0390302a801c41040039000e080715550070000404004000100c40c13003992114500400c0c40e14140c1402420301c00c40b5804036000341d0504480400190441046a5160181d2406c618403031203000406481c011504046000b030120b031610214a140d0000b010348035207489601150344c0d8100900040301500d000b841900003042c54000605413 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 273350188 1250 273348938 273348949
    0x10303140c07181505060c150a0b0301020703050a14071703070e041d0709062103020705030327120601060c1e0c060f141c02160b0a060f14 61
    0x1003207000070302140c200680311802c41c040c1505500484003021342d03580da40028102c5410b041e80041400302c1d015810300c001504080e03200c110020950409005120024400380381c0e5500c40418480094002c40d1a00e1440c503010301982d110301000400b040c10800d505020f141000e0840e84882e40c420a0000382035806070500d01f0f1a003000d005030040c0329245002089a807503500c10b046202c14201c9544103040a45180c040c11300103940c000740841c5042503802d10106e0300c0304814000741701215003000404091802e049040a80b01d8010130391500001030802080c006502c000401c040440c05030714a12840b150401c50040741d001c0481d000c2d80c1218004029090250b094400254064ac01410300c1000c1102c4500b011740d03100f5021122800c0d08130303040c00940d600c00d101c0243d048840c103244032001c1c40814a039030103019500c5890b03445580e480c3c06448100194040d1420a141d03500c0e0080481252320300f070b024010080300c000c1e480600e40300d400030341e90103500746032000ca074518072044160b040050305101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 273351438 1250 273350188 273350197
    0x130c0b03041e0804090c031104060810150f030e0109030c02060a03060503070e040b09030310031101030f020d0e0f01020f03061c0203030c0c0f090403080f0406060b0c160602030301030314 82
    0x25542c80303110004241c50300000e0300c00700b20b15100d00c00b0a641c41c0e04000f81d81d001c450701d80c0d0442c401c1514140790400705221160442d020741c0d04506120120fa9150700810f6251050394100c140f01030b04520707843e80100d0f0407041c801c40b406600c0e00c050140b5440d0501035803c98071041405070015048a4414025007030240083c442c01089144c0480c886458801091030312280e5071280390708520700400c11050183c0a0140340d0450580c0340a1840d42c1068505040d407400c8074000178000740111903c5550b40e82c007a52004500050b5507a0664450030902e04000040600c29a0622207001d01090400700306018422038000c0d1174031443c640d085403103040511260104010080c0c0c41d0103084038200000d650100003400450529030001e202e0458040140722076852510222800361072101c2c14000042c3c0c001c0c101980c0301285442103c001c0e40c46044c54070140c00681d000709030615001030780038180f0300c002c00d140003441144040d4a50841e51204200c0e660b20003440007038001140e40200700d201820440041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 273352688 1250 273351438 273351443
    0x1e010807052b020c03040f0f06170408030a0b0904030f080c13170a080c07030c0b1602040e0715020a0629010c0620030a0b03070b1903091b030b130c0b0304 68
    0x11305008692440a180d83d01503000740b151034840280c20040c0c9521032040b00701502551816065044428540a2590710042c4c002810311402100040704070b074140d888212403c0004117003110074141410040c1494cc2049208030000c5c06080009001d0028101200e9929000b01c260110091a042d20710404210071b001400450040b050080c000c1201e010290000001d000302510b0f40c0340c038504d40783e5800240b0307a100000800080c00b130a4080500080400c07840e907010386001c2400c5203240521424040f0642103500b110300442076400c00143d000074ac84200a00ca0780d001c204091820f4800c030f0440000d0003a1040c14500941090015480345040e203548034401d000100f032a00200c00107100284500b0400c0c0c0040402104002400c800c60040c07a5900406402411780a4189000c2d403070b4a10801160100d00e4000c0e00018510a100ea88540051074000d1210603208245896840f04c90f03c483c40251502001e03400800c07081c1a080d0840104558012490011986410391450090304018001d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 273353938 1250 273352688 273352691
    0xc041a0409030507170a0f11060115050910052203020f0d26070c06080402150306060d020c0c1017040b040627021309020f040f09021e010807052b 64
    0x410b0016807100c18600c4a803020b170440fa5220490303688001c11201c171544460040000940d04403902100c0400e11906407480088260b101600625050340c01d8401e07049031a170480c8242031090300e100d500c4009007143e100260300203410941002c0d0403480c058030500000e1362182120925040301e03e0704141080080748241d0561184101030414014081d030031481003d450b10001500d00108115103280ccc401800990a0074105410503030046000b0b040d442e80010030440002001c90043c1e0b40781d4007902d81d410003183d01903580b04424000702d03865100d00444d00780280d4030405c5101e8018042c480000c10072001c46140b2070a81d071079032580812500003400079500280d072016421503a88a0f81200c48144000340117800d0b50314902c1c03051015107902001604003241ca40b062000044e9910309021280c00d40c200c1f000714130517112990507001411580c4000303502049401e8182001c0c0160101040a44002d80b2004943d036241c407000d903413a2042c01900842501144400c00c1e9018404005801d05d000da03000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 273355188 1250 273353938 273353947
    0x40b03060d0c030302010c0807140d09051204060203070614061305040204020909040b090d08070507140f0303072706211b02030d0608010605031c05070818030c041a04090305 76
    0x11284044540ba070015001070b5180c024810395150008040c0307401c00820b02e410303c1c0031172049072000010300a40e89401601e648411003581400800c0104016040f05192042e503920364410001e596a40204400c440712030a00c080d0007003103d01c4c000700e00e10881010702800c04c550780f03c035400d100418005104a900c20340c2445002116119014114400c503c0748606075594101070703014030310344400070020070f040102e02820480c0a07540441aa04a00e50044c0c04d043c1100004203000c1c1414202402944544004002c02100301d40c844001ca1043c5843d0b154030443c0d4129200080d4504410b004070008a2072000c07500d245200482114104492100d00005203910205285011030480c2506100140d1000c88c1c03012092445115240040c081480200801441d10020a4a40082c00501e1800c00b084003076907501107001c6d200700d801c1c1a0b4000085a501c031210a0085a0300b05e10306a90307806881906220140750510340b060444608080940c4980d1303440c4501004003401020b9000c804100b010701 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 273356438 1250 273355188 273355193
    0x3050f040306060303030905160503071202040f020d0506150304020a03030507060b030f061f1520010f021803150c0a021e060403020d0507080301300c08010506010e06040b03060d 78
    0x10803600914402d41d00410403807c58180280340a42d4010f0001d41e58010a80070000c41c1d130009102e104a0700d490f8120881250180006002840101c1e0028005800041c048000c48101d80c4201d10075001111041005401c207201c0001c0f90200301c900030741215000c0402d0001c80c5c068005040180d104990200342c0441d01c04c0400d08082600302150030b10703480142840030186c035103c41211740c000c902c2d209407480c2d4505111640f00554082d0194184000c80340580c00c190b10381050303401d0488403800280b0581ca07152031000000c2d40501070f12094100c680c1410f0b41e0920b004192807858801d00da80401c25500c07580d141003080c0d8480184901540304000e04c00440800e4a1fa030b00303a0040008002d00303c1072604d03050180c104681461810304119080040704c000034007001c180c03410f450502c0c00c42c1d1545503401e80e4210011180d544c040d00946012a0702101704a0110043c0b0103544000000388120380b034074001961000c00000c040b950103241800b003802404505c03c082c650145009240303414800654 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 273357688 1250 273356438 273356441
    0x5030d18061d180a06080c030307020d2a05271f090606030204080f070501120b0d0b13062f0304021309150b090c0d05070c0b09010c020705060c0a03050f040306 70
    0xf030610311441d0440200708882c460080c460303140107090880c05461500e0340c0400285d01c80c825000028071070200898100f080c401c2c0c40d4940b20441d01d200b9840c03116041c1d41ca0b0043c04c403030000e12a0078840c8900546001202c004440c9907201f1151007050215180ca070240f60001d0300c0c0b24209413218000d6510000a4980064010b84004085603140181d03541e0034489198240240300c0e40c01540c6034041e03801046966408003404ca800180c801c00010031855040015509145491025010034114800d201c0c0600c80c08101d001d02d680b1031481004919034252200407180c001000100c506c1842d6000290700d055040025a4820300c000c03ca10800700001d114203080700c4400f030068520fa000360012030800c16042c40b42c2c3d44005000c44a00d915443c5c201480c81180c482d5520246071181c41d00c01140d1220b0080c84500d00d074507400342b451002d070302d80a940c0034002c1841c04041801071060318000909801d081313041b1680c000f0640e0103000090103980301038886521485241074078090412001000c11810b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 273358938 1250 273357688 273357709
    0x30605012012040f1a0a0f180803180316061b0507050415052409040b01020a17030703180203070b1606110a08180615060c01051005030d18061d 63
    0x4007401d013090310b06215100002c50007901e100d195100f81042011035141d0440382d40341c2584803514050045160310340100c4c001103025440403005202c0814501c5000010380c102c069580d100360210b41d104000c40146c40840b441510400011501490600d00c0c0500000c0026203c24080d1084680c030316650760114003105c0202c03940403680c04600200f40280c0c075000140d80c002c18015200b81c109400b0f0180090780c0c83c85601c02e224410703039440b8020b500d283d000340301c11140e4030341001100c034070042c17551b0220800703900403103d00001030319108807144010401130246020940150050030028100307091002c00b548990009542c85054115020000d0014000e1a020040030218240ca451b40140c02402c21100034080448828030b00c2c0c2c207410300060000711580e001c8945030940d1130b04408040441c6152140d8048060b45500b41000c00480150505443c02190070a80c1144c9091407407074402c43c2c0c14000f038641c1c0e80b040005c250701000f00750310a4051440b0790030980004000300b1788400000340101d00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 273360188 1250 273358938 273358949
    0x70506040c030209010803030f0112031106040f0b0105030a0f110f06040609060f080402010e040b0402090a230303131505131806060906050a0813050a050f060703060501201204 77
    0x60101c014030031802c0014040e401000d0b011300560840c1000040e0300641041401043e0401035601c50342c3d0103042c842c0540c0c5a0300b141240907078540c1e003800d04003100c3d100e1410b4420f071100201c0d000001210705001803101d5499030000c00c440e130005200d56030581c40b507070b4001800d54820506050741302a03940e000c001308010110358a65402d080d14000016208244903074032201886408030800000d030b41c0201c802540c4000859002601d500c0e2400020028041c41501e0f503000303404490042000394802e10540d8481a1f00910350380040c0c016001c0690701e1103a204411038005207100c0c108010b844040c1301c102c564a82e402c02a0500c09540111441043c1544c0106030794523000c0c69298400503244a0f0002400b42454840705903070800c0d00250052090902c108100311610002940c2160f0314110084e055a22400391031240c00181130050303407100442c1c0402c03442e001d600d01140c103207401782c4180d0045450607100e4a9444011158031402c01e4034009a01c62540100c918001350400c0d00c0005002500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 273361438 1250 273360188 273360203
    0x31303170d0204060c110d080f031b30070c240f0902040b030a020604061d03010c020f0d08101503021606060f05090c0f03130602040b0403030e04140703050c07050604 73
    0x5030076046c00420700d041c0c440d08601a4030400b80010102e211072080714452001d12120b04d41d641c641c80e041c03114105001001160b003100102d1403035401001c410441d40d40c0c9140252021002000358084049030000f940d180001c030b5082c0c2c10040c00107020003034500d503503000841c003544039050b0b1902890603a09404606a1030550300d16a050440c44c06204141500c0c00035401050303010010750100d0613074416405000b00340306d4a0004030300c044c18030b00c104061020015000340080d03243c001e0003a65449080d4044020340c000c05031042d000303a11a00c1d803e4801d9550380303841ca1010345000408025a80000c004e50f00b01502001462000c40f012001c07080e44071301c41c090000b0040e1a103d120540b40f24960421031054400400b84844aa80401920700c0036611420b010394079200c4c0d9482c8521501d10400c0100000d00210b0f000030074071040400f80080703d000b610350b05883e00341364041104032a004210010030903100d20214280520a900843c1d215245414079454100d590311201d00e46902210b080704c021 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 273362688 1250 273361438 273361457
    0x1a04210210030203060108040201111f05040b0610021f0204030605040f02010206060103090b0103061a030a05060603120a0827011103160f08010e27030c0708031303170d020406 77
    0x1401c00400021010007686000c5085081c603000081a103000608040c3c10031040c0810302c0d070180d406003c4040c2c0641c00b000d10048442031034078080301400c012501a900052884d00040640c2829412810b094076554040c1c44848140d20300e005d015502404640c40d036903406e0001000280d40c5128460007180200700b21150503415100081c03600d000149441d0415080001c02800a945c600390207056035486500440c607180240308020b101c07000c0d125029031500c41c040f81c1c2000c0c00320109400380110429003eaa1a00202d0100d042c51803045d102c1c3d90000039500000030710814201182c4566a52008403041000c0d04407504407801e440d02d0002000ca00b0500105000c01c0030a00c0c1d5100f0410491410422400b00a00d0310180c44418144642070301c51001c44000b40c10f84a0300ea60040100d10348500c0560f40b24004101d46a5940194143e0b240c548500c0c00d01140400000080d04c80d107003115034828540e5030660f039440d940c0d40072000c00050b00c03110070b10031022040918005407002e0086030740e800711070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 273363938 1250 273362688 273362693
    0xe0102090a060314060102070f14151c051b07030e0310020f04050f040603080912010e0a0c080d1d01050901050c060a2f0d020a180f091d071a0421 64
    0x42d038006842c5d2419580801402c200300d9181d1172411003224020344d121095030320018003240700041082c400039014140011028044006040120080704800c03400f002559a450303a06c0d108507100343d0304100c4803842403040000213071243c002c018407000040e0954415151460700c4506a8007c41200c000400340401c0520490920601c3d10300c44800849081c0f05040ca5030307c036861103104d01101940900e00900c01c54407901002d4118201c8070610360b089415040043c148294541654061400c240c01040340700403a0921980003110004c1010f8140029105c0d540c0c01911103912000c09107050000a001840701244280100343c41401e0000000c11035580a212040301d0388400e58011402c3c40c1c4064820440c0c2134010140c5034964100c550069440b80d0201c416605c100100d03494505103415043d010861803001404c44046030590342c000d00510701c207207042c610300400012128509a1204004000c1c0300c0008500a4203540c080c0c01481ca40b40d11011161078030320360a080d000311545e00b5000300c0c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 273365188 1250 273363938 273363971
    0x180a08030921041406130806010f0503150a0e07120b091216060c031e090308090d081b0705070906060f0305060102030702120f030a1e0905030607030e0102090a0603 72
    0x81c00410103842e41000912840001c24900442c0501c2c030130000c00d00200f0840352140012240c000014120f094180b03503842209643d9010709000e844020001c1450002d070b903040c00039016a090300c0140c5a190b0540d00e17141428028110070301c1800080c410300c00300103503030400500038508103402610140e441d45001c581007480c1400780c0200c0d196610080082e40c81703200310010038244460340000b01244800610004501070981014041e15000d40caa1860b02c4000060340081101c3d481398031403106d642e07590310310580c681210200d40b201203580c4900003264400c1103031011003040380c40000ac40c20680e03182c4600b85041c4064202003002966504280b200c65085081241e81d400d5600c0c2c10700003854420300003074490140c040d0090150002e01d003048081c4800b88054000e08104504072921483e0b118001047c20101c0000381000d14180c0c00040c15282c420a140390035510083c0c003c0409403620802100103040c0c3e1030076002e055609101ca800070781c0d9400c1c2d107a80180000d94012900a0b09602001d2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 273366438 1250 273365188 273365203
    0x9020c060a0506101403060303130602100f020306060706111303030f0806030a0312150e240901030b010618030c0b0409050a050f060105180a03060e100507020a020603180a080309 78
    0x244241305100d0b0f45015168814034400d40000d0001c140c0380c40303444041c0071900e103000d0600c0200314803004017008545103500146581210342c2d4410700707002100041c2510000c0348010360301203070040c4040185402048141d00925007240c1c040b94001d1030541c45005008a903580e40d00228001501c02c10300703000c40b503440b0740200d80024044001d0501c1c425036580217440b13114060702c5200c500382c5690381000c5501c640342e0100c00070036280102411501c1c0c04d00b0f002e20040984034441c440384038440885030039402c2000d0359034182c0b40d0209510000b642000d0302514010989001341d180c0d80301130301c40800002d01d410301c004010240c0400194031039040008c40c1058074030080182c216207151504100260301014000c5401c600c0c00e09203265601080f840364441d04a01e00e840540100358220004100b00c1d09a02c0340e852304058106032840d46c01c081422a046c1c44003070345e4250041e17100005000145c90301e003005581010085842c0caa8011000c5000360508600c4102651700c0c81000c4108070446100740400b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 273367688 1250 273366438 273366451
    0x50c0304121b0f050a0b151017010b03100b0a08060f012d020f01051005040b0d030207030809120105130b01050d15021b03040b1e030c0702040504050709020c060a05 72
    0x900100000c1e01246803100b07036000000d402012207940080510030203100030744920307070000a8a002440e04481e55011318844c900018024510041c181c211207208901c00b0007198184141d004a50b4644105080c1c941c00c090180654490080c000141c03c200541c000c28442d2101e031510021450034000300f01c034660702c4c0d65215040c03200640320b0340003107c3c0c042c4c48407441000a202074000301410150892500303821140700340d002d601e1308041c80010066007a4450840d40201c0d001d0108410b0303e800c1c08403001c00c1c1440140541c2c48400d05000281120b4041c0a810038060b190800035043e1003640c6007500e0381a9803400e040030440c0e0941c81800140c1c005c403405004140c0361030806800ca41d41d040c940008c54101581c400f82d000c1703125020301908410301c4040c020303e101141c1c0c031a0b032583c460300441d80c0404130100f81c42d0100041d078440c0c507114805130791141c07021921550a20700141c00b40805408004d104854a0090600220f904c042c1307880601100070781d00d0014080c914090000070708541015004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 273368938 1250 273367688 273367697
    0x6050901050c071112010f0f09050c0307030c151b0b060a050621130b0108160614030414010b0901090f06080a050c13060e010b07030305070c020a050f01050d050c030412 74
    0x1d0000c02e000f06400030311311a0a035880000700001c000c40500520001160552003410b15800c102038034085d40012014600030015624011400c104040e512007841c40001e00d4000150010080c440b0003003044c4105801070b0406000821401900034604059690100d610504240038040e550600300711081c0a03040a5402d185406540646503a41441c0101042007516a9600003100320310317551100c0080350351151503140256180e0800399108e96560000000000145500081070f6104204200e607044040042034515140c0351500e082034510f01044041035921040c909209884811150b802071181e0740d00042c0c4d4075120750992007a03600b90740c0f160302240c0c4003c40e00720101d80301040600036040101c0b00007458801c80c00c244400f81071141d0105841503010400082c0420081004104007846954204100d5603018000c0c2e03044d030040d0703001a400440d140c40c00d020070f06105220001001c03050414906000342c842903001903c80464408590650100500040000072262541400040e040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 273370188 1250 273368938 273368947
    0xd05091204120c03060e030306030f0721030c12050306101103030f091c0f09240f120603110909151605041706220507140a08030706050901050c 63
    0x11508500e008074003410146002c00c00a034003c00040301d10000003140e0202062000544144001740c4981044034128040d000359812106100c1011801105039941c4584da031210100c000905040f480351100d04030148042441c220700462582c642074129840d041e901c280e0341c1c0c0790090a2080c54403852031281d05025180070b80140740c02012041d030307130b210842c043c00c0b085669405040900e4240c80b18001142000c49203440a4001c2e030000c03109100094603100d51482c159078105001d03007d0003c042c190380030035460340c00520300c030320400c0d0088400d8003a2070038007818680c0c0b02011003110110360003194060000286075501d8240390304001da01503019800340a00600d1201e03d0303a1954001080500136013070414030000c45501600c183c5028103440002c800862280d000a296503000507103200300d0b080340c468001602c200304c020301c60140c00e43c88005003043e80e2600161a0041c502060426880015108041000d58041001d854914000c4d00c000c91941440b11600b421a54050700070b0400410400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 273371438 1250 273370188 273370213
    0x1609050409030806090705040e0f010f140d060b03010608010c09050306090706080406020903030418050a05010e0622270309090b01050405010503040c091a030705180106110a080406050d0509 83
    0x310f0841d8010750076528072201d5540c500b0201c2c0c261140350400b03400c1c850342000781706295440350900c5d41602c2c000c407030315a01c0948070030b0900a45c40d284900e00b580a58952a13a2002403000e810a004444010b000421007175100c41c0d60034250751501c00000300140b041241040b0b149000c1103d5900141d850021305006820807900901443d4000c01c094138498000926504544003002114000d04410005503c5180003c00042c050303c0b064503030800c11400c010003c1552200b4104050040000810030359807906840b805505c0311082240c5c8030039280d510580045010100380400c00160b070700c0c44010500300418a40901105060341214017554500100f451150341c1000885068032000d02303125440c0d40e950310b400050114190001e041003820500800500300d854482032140600890030340314040d40b10000c1c000041c4102c1d0018641c0c1640300c00400142d40030f0707411b80100b64112002e40700d80260940308c0d9440d540c01640300c0d4000580004828204a03564414907400c581e81401a00e084140304 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 273372688 1250 273371438 273371447
    0x31409150f0103020a0e0408130b0307020f0601060207060e0406092c0c06030105130213090c0f020102130e040302032b0c170a0f06030512030a0b0109080a0303110f03160905040903 79
    0x180a0042c20110006c041018000c0c5030042e11100242c1e00c07920714940d9251403038040c0b190010b40c1c0400140c418684810007100020400703a0590789030b03030300400741245802d00c21505143c8190540d500b2503902d400c0031800035440d00941c22070261050b00b408081c1b21500100300820410340d0b15039038079008120380c00002e80d541400c0741d04640c003c5881d95a541541c40419000b845042d20090780c02144520011308402d4a410801600440740c440660158140d072081e401d0b032242d0341404240c22000300301805501c070302004c816003107402481141d050105405210a0414081410200071800c00c0304801131400c0c18020810b000c40d4902e410800c0402c0c00c907501041100113401c01ca0b0b822384840098000c008141c0c0540001e5404c40221017459002c405050407650040c0d40015000b810110260300c554051180181221942c00082c40b0004803920200d00a022050010360303007a60070001a00040b014178040c43c010710003042c5a0700c00301c1c1d4a01c0b02500e4121303180d211078000e40c20440e042c0c1c0480d810 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 273373938 1250 273372688 273372709
    0x2c04110c2508030a0e131b120608032521030203010f1502101d160e0a05100603020d090206040b0a030509010b0109090b0a090e06010f050a030804090c031409150f010302 74
    0x1030750804003503421620031401620401c1b40c009001c00e40c1f42c1c00500c00c240c1c880c4600b6001400b659040043c503032100380b040d440f8400d1408000c25111401d9540714a081180c40c1021090b0040c3d0106440010f00c2400c0c512a140700ea1680300000c0d000b200502006220020300001048180c803d00c45112016501030744440c0d03605018101503940b0f03102c400ea0703949070303018458510024106556150074155036402409005000b03508001c05c40301e00292404901b0322a29001e1601e07003091558003458107400320302075400141100705e01e68072940c280c030060321514050006041002150b64680081000082c12114020440e00c4a41c0c100342450f18566006400c0c6015a039913800c0c00300c0c10400700c07404200c80301d6240d80480c910314540b41c00d0316180500812401d06035034211480d5460555201c0410507074109902024144903400c0008110204a651150291001c0c80c2070200d660748005140c1800d05500b1601c2101603040501d00c1c0907848030611000d0340c0134001082c000881c1d419500840c6004a2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 273375188 1250 273373938 273373967
    0x1e041701060320030715021f060602060f041103030703030603051603080f070203010603050d0e0a0609271814010c031b08070c0606060e012c04110c2508030a 69
    0x140760600f80f854406120003005048107280d02d0001405003a0300a654074503c0d4140c04401e151070b844ca01006d03165005400841e10543c0c01011140c660704d10340407145201500441d04080782074a140c0d80d5071010702c060100c050003510000b404604d142011420141101042c0c2c00c2c0034508a0103000140380381040d0790301465204a000d8079910140b020078010303c21a003024143d84208050760f1038160b0f00060a400e50441030312020311659803088c0c1682d40714910301450704440380041d4030311044c000220071aa141740513030700d0100e41050807a03100c2003042001d50044d540300b1b48400f045070140009004101103400d95190401c2400490300d603222042981813007c400f0090340101041505102d03964000949402c0441040300954841025011840302d80e211404950b0901a8020381e0f11800c0145210030707031441400ca0340000d5002040000c040745002680901c0061100f04515281085803155010200020840e8005010048803240360580e0240c0040c0c0d01c204580f10b01c55601041c070166414 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 273376438 1250 273375188 273375233
    0xd030302090301140408071a04030e01080417071506170a02060a0e0a0902030603010b040207050318011427030c060a26070507060b032e021e0417010603 67
    0x1580c1c040068007414000000b402d02903d6242030000303000300710f00100341c42d611404c003c03600c1510000c0c8203c0b4a00f400c95001e400319003040820030095000d00c0c0440e5005128640e2030444204084200055410840c0b043da00c03020540d00005441150b84503203806011003442c40c815a141034404280d6400c020b200c000c1c0104030110f4041c910034001d078004810740c00020a552040c0742c0390541e500081d00111542c038440c2d03080c0407822200781030920880791b02039006405180b901280d06411103ca10511a07a00c0c108400c3c00c4140d8074041c808805050842c0c040c03071500300e903011803940032040729140c204000d10941003112962015030300c2408440000c007880c240f03003401840d04001804842c025026501c0102495000c012810303074000000e18489105000030041c08000300113040c0c5d04d150707804d441c03a5001003d203050f04602c3c000300c48000e05514419400340c035003280740c0040d0109100d07000e1601814a40440c0078407901480100b10b20003540b003035008000341441d41d11a981ea169001c0c0c140750519 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 273377688 1250 273376438 273376447
    0x1a060409110903030301171603030e041e0509010603030815180c040b1801080f0114011b02030709051603021c0f02310803041203110f01060803070b01140d030302 71
    0x5541d86410340b44010b00c01800d403510385d03070750304003401560385c04c404500046c1c0035010f540405010071012210680383c05940e440d8018803403d00b880024050394a0441c208100390135a01182440340c000e0511447d640c00000c0340051a514000e044080c02034015940344804c00c000d0035090310384800d10040001c0c0031461110a8891616100b0745105607042f03003111540004410314200c460075174a4041076020703614071fa007070f0391451040c02110200f801084003402010038080525841829800b91405000c4082104020b990740001d247c601c4581c000465540c40720f0401458401140705c400300d1000b1800c00354540345074006101c1045002d03004128110340d5a03a44604001803590607910740b0320f04042c0341e03d0074140800c244404c00d20702e02a1410010312040001c035040c3c4001c4155000c607101c11b540c00d80b4014560380c0588000340c1f2485010f442c0d00c14803010404150003400351000a00c1c40502540d40c071905801d280100d414140c20004040090300940541c40d01c0b8615400c1c142030f01440c005844 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 273378938 1250 273377688 273377711
    0x12060207020d050a08030123010c080f0d1805070e0f0126030a08090601050d0c050f012309030c040b090f09030c0f07090b04050601020d0305100e04030804061a060409 73
    0x10300b0103440140c40c500c101c0c2d02400411141c0c1c002103042e100c8022010070003101010003159116100d02c5a5030005980001c00380000c0e124070003410100034401c00244c14000924002c03000c5030a0100d0700000104102d881109005090007146c0c0a003044504042081c078040101815501044c441e120f0041d64403c10514040e82c003100d904030310140b881c03d40c0d649842c100c0008240003001d940102480c01080c1c000980c41c40c04884103e00c6561005c04043c14a291500b040407102d92802c0c068180803000078802c16026080c00012124040c40407603603203c0702900240340ca0602c0308064180079030b151111009256540c039903140c0e403005800c0100c819503078441c9440c50940c0940c00164116200c2c140c0084071a131008104001038480100081040d007201500300426035000f9540d1700d0158103d4501120030600c203800403a0300070500421900e0382c954595011660080c11181980050150400d1200f08040c5009001080348014010f401c444443e1002031038034442e601c2151145983c5050700c164 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 273380188 1250 273378938 273378949
    0x30207081206241b070f09020c010b0a030b01080706050f0d0b0d0503030a0b030f070e0f0405120a030b040e01050c0906070f0b0f04021302030c0a11030c010c0e030f01061206020702 79
    0xc110142c40d5006403c44001c1e10340402030b812049820f4468a540d0a08038032003180003031603404544140f0b00004400d8680b000c200004e622500322034916540712108500c444e2681200440103511071640c03800d070344d858084481d0805040b40c00001c10003200b080844544840202503507500c0d4040a00040c00702d0703078040000c0210a080070f00503e10300010080003001c64080d071040021340e0003901626044011020700a45460f00c60248503001c8003500b01181d1994400d180c0564424170607000c0b501394001303901c402c1055401c100003040000785c5400d0110000d06080c001c0301c980f03141040c000d01c4103041000c9120121b0081c0300c07885005100101d1441d05106042181038280c9070489142c00711402c1c02c0408d101111822201a0301410031240101d2139002c05100b1203100300c1401802c5820400082d500325000c407151a41c4011038031042c44007142d414401e00c40d0f8000c1100c103450303d070781411684050604201001003100392507490b04400b00440f0200300c009407681c1e9031000005948850724400170b00d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 273381294 1106 273380188 273380209
    0xf020702030715120e010501150e030a081602040e07030203240c0d09120807030b18040f08070f030503040209060405060f0d06022205090601030207081206 68
    0x181d078203d0000074268032080c44c1c601e100d21541c02400040c2c40500320090380f142d54900041001001003828802c04110600301040e440d030000000030381710102e20b40b010b448550002440445a0100c1510400c0540d009104228210780c0d080100d5a070021070008034001d110711070045034650010305440c000700310100c109601e25034484110b541d1a40220b210381f002142c0351035180e4000381d11045808100c519a5950015034601104003c054a011040c140c1c0103004054490724440a2280d03100d9010382c104158494000322480c00300f0032482145409042101e4050b480e504040c1c0c004c0c02540105e008544a968507200c00d0100400c0320020350320f0300e41c42a09040c5062590501c41185113016000720801400c0c00f01c034105084415003110600a18040031010038006460440b0000750445c03400e10741142041d1071543c0c0da889912440191020300f00782036000907199034a854040 = true := by decide +kernel

theorem cover : BRFrame.Cov 273201438 273381294 := by
  have h0 := BRFrame.cov_init 273201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 273201438 ≤ n) (h2 : n < 273381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
