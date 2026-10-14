-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3705
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:26:24.359182+00:00
-- url     : https://prove2.me/submissions/5d36be70-e270-443c-922f-d7634822fd18

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 666187050 ≤ n < 666366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 666188300 1250 666187050 666187061
    0xd020406090516090e13020105030a0e190b1b0915040f06090806220201030504031e031a01142d040e01050a060c050d1808011a09010f0e0604090f06 65
    0x3c800c41100d00302c1c14030802412690450b030141481031851410444000040c60008540607428240103860b07451703000100f00a0001c805000005203c0c201c41d203158a03101d4000c0c80394045c01140c0d0101030b51a862140041ca2030580040310300e0b20003c002502076414640380e10350804101c406030a00303043c0c541100840c02c003029031090001502d52081800011000d0150541101c5190340c10003080c2c50380120101401489440641030641ea0790000d82494044c400d00d908205c2c403881c0a0206009101015000304905507411480d600640c8010b00154006d4401c00705507840a5092030070b2200110076102c0d0110054200074030350856440b954203d0540d4005030020700526180c4c1c10b0690f042c601070080450f043d61054003002201c56200000c16008526040c001c2c00901e46107450078800c2000c41d44c900d1007030b4020072140d132828040b94050705204120005110b0300719000302182c5d0b0b071442d0001600b0303110300038064104031a07404030700c8901e420b5116020307540c4a900101070a40158072244102c40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 666189550 1250 666188300 666188311
    0x1d090601090b040f06171b070204062c0907030203100905122b05010513090c150201090b07140a0f030b1002010506040c1d010302030606160f050f1b0d0204060905 71
    0x140c1d007075410302c0f2403078003c004940c0c1010f5505034000c8a103407015080e0351005002d60151b0362200b00123040025074583c0e40005003d0110500c446c462100300304c3c0990702c40e0800341128480e001c12000419244040400c0b02d0084a800074010894800358200b494000d003540d0004a03a18480c0c010400110b0007118081c1c060041d0b0180b405941e071803452000c080102ca1005d17448001441e10005104035a2402008050841d00800c0001c88032503904e8905106102900104207680796028520801c07a815000b040e695841107079011115240d02c10183c1b5500c68549a0318403014092280c1c2c140d46105080c00070701c0341518540811103403c1203012606d5540c8610300d420060351610100142d900b00703402403808803002e500c1d0503018040408817144540040091250405800001043d6117584410a50304064001c5021031070f00724040c5000c11096064040884481c000c1c40b58440d4075090209004000880c8443c071030941c1c04d440340811200400c4900201c0c2c3c80703a91140040b0b08003d2621a4501c6078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 666190800 1250 666189550 666189569
    0x50a0b09090624030405070e07120e0f010515031b0d030f0c170a02061f1404090b0c0307020f1203041121060105040b2b0c0902030c0403030f1d090601090b04 69
    0x5c0c206030800702e080400c1c9401c10042c1c0390038401030000456100c03040c401b121110386000110b8802420f0500d040020b5000ca0310019800e100c1413008002d0020505901b4200460854212010050708a041200301512066003e2380005628010078003e404051940407603140142560410355924480910401c40c004581c140104040c40243d40402025030002e4440700549014014030302c0d01d0509200ca405450100c0207d1002d240060310f85410546980ba807200c403407051480d0404c00c90350141c00440301000103101d40c00b00424119404540c3d0214001d0b070f003006e180765580e15150341d007054040c5004079070031a00101c1242112a8004a51006a011480940070700e5140c0801c00c0280c0d034007a0b000078840c826500602e1102040380203e0b2801c40d00e000b120341e084641c40d041c94109c0301c01540c00355404900000070441c11070710010050068900c80d03144e00d40c680300c1d030b2001140c84940b0b48150682e010500d0080003ca4501401d0306035008005140140341c41d0b4442c403441c503040d08554042c242c0e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 666192050 1250 666190800 666190807
    0x16091509200d1d010b210c030a05100b0d110913020927033405031303051204081005061201060602010905062d1506030112060501050a0b09090624 64
    0x4218010703c6680042c203060000741300030b04000300081c070442140c03c0161152101018107030003510050000e00714032100242a503080844900380252652035245404100a20b0600705140e03600c0c0001c8a451040c0c1c00840c0e20340c2119021050080c1d9460181540c00100c400320b03909001aa01c2c032031074038030503009084a440004030b40003100c3c48614603070202003007a8209000001400d007490b204211b220101c211302e0600368240040d0070040f9600000041c0450000041e0083c001d45140090001ca911400440f080c0000d008810322550041d40038102c010b40000d0408102280c4982010b03800c030307200415102400300035400490842d6030640c440d40142c1d440b810b1280501600b444031507403046001c0403007400f41300484040c071440b004064110580700310f5803000c24034002c2090403072402d804001c1d0246075256101c0a041c80314034240701048410b90f08080020076503051048002085421850301d040c00c0c480d00b501044444071000b012140c01c8400d0058102c100620910031003140369020b511140d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 666193300 1250 666192050 666192071
    0x80706060b070204050604020c0d0503060a0329150f10020c300303070903030f1214010806100305030a050a210c02060a021213020118060216091509200d 67
    0x26030345c0c010301c0c40e0303c264810300c122021060b0104040d03104091030b03e445580d0365600c3c40003487c8030085810180c2181104c5000102c40c04035142e0011a410b0b0001da886c405566203c50707001d00078001d00100341c21211f00d81100d185400c001c00000c000c0101d90044d5100700043e040400d100880c1d80d401030000f0b00c02d850f50110540700c0e180c600300650400d030000d58a0742c035241402500d41441e61000400304075111620b614883e22407145250555040700003070001c0241c141c030000c40301a0030701a08186024003008180c19003c8802854100c0743d001001d582400344005c0103952a1304046103c8007031164010280e14040c114041091440d00010b400148143c0725450092030300304010a021089407040104002003141d910300c60384e000e0b14000e9201040d00300fa01c01250001050f459142d214920400d021809580203e17a28240744100150740c0c034090750780c002c182c05848840016101c8103820400a2048131201d8120b62841c0c24680d01030104d181060210482d0360303000030b100d0300d0125610b01c3c0120707 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 666194550 1250 666193300 666193309
    0x1915090b040911121203070201020a080105030d0903030503060312070602030108120c060415110703091a041d2706071d01121e0914010e0d1b080706060b0702 69
    0x22a401601c040102010780e686881080c45820503007403280f00c03010314030a101c5008000202c541000c01c191781d5282e003851386029010f03401016680700854485400031990381400200b20350480040d56603600018a16213007a00c1c95803000d030003d034160191850b40d60040005000424440e8812640180c0e41d62500d80c0050500640c2151502e21100400c5284810700c0d00090340794109401600000464850310707030713003002400c0e003c1c041840c42002080c1c0c242810382200c078038011610140e1810351103c0803203050b040300344a180503e101296500503140269003110307114540c40760040010380701c1410200241e2101032b5650200d00c11641c0100c0c1007224051f03001d60344840250f41244004400c3c1d007400000780c0400c083c401c00c0314900d45e403102c0c0466081c0145030310b030200d50030000003005210001d040c14840c410032544141c41660074103111200c01040001c6c44000c00d1041e40e1007010081c800c0304c10010444010748241c800f5542405400046102ea01c1188001c10200e000c0541e103030081e10500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 666195800 1250 666194550 666194561
    0xf110604060210060512070e1504050a050403080708070c0f0c081f0c0915030b0d120509043902030f0a030606020c010305090c12030403120525020117191509 69
    0x203400761b81c0005000075204800510001a5a0481c0e80c2029070740d1158490944a03c0d01d00703600d51700c2418036043c05604140c9074002030181e8001c0e43c5018540c0d40311102522007000c00d42d40b102c00990039005000200b0500741c03104400714401c07045d9100e03240e030301e1401c2407038500060002826010f102c200c900f600c010300e1040482a468034101084042c0c90304c11a640c02c0d400d4426400c09160f2614901c80301c035940c180c407400c4c0040d44040000c04080a424005049400103e0320601541c6000030860f00611854001403071a1700350301203102d22038451100f0141c0c40d50003800d603c0546c40140005102a00201d000d043d1041d140e81c2d0002d8400d02c0d04400030b2500041d54002410315103020705000300c0f180082a00340a03140706880d110b041fa68004c4120f8510702c2554405403103068040c42c1c6000d05a0310500504444000d00e1a065054030301c0112030b0500300000400a0108007103a000c0c40380c0302141802e01d948400c3c909000903c041c04404500f050315841c628203403c0d028541c034180800c964a110700d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 666197050 1250 666195800 666195809
    0x90201090323151614130b040906050f03061605070c030b1603020a120e07050307080706110f0c0103050c210a0c230c0a30080906040f11060406021006 66
    0x28020b070034400303660b81800001580d201c042001c8000ba0b030117000010f8003102e403000055440b41114580d02d131544212500280a203c1c1c502c0e050100000d841d10740b002403041618801400b074060342d04c625809210700c04115221806002d07040c03203400041640701e90440011030180906040d1031400704509400f1800b0300c540c0380e00703161042c001040401d500c804210700d07140f4642e1000841c4510300d00c03810700e071446a81c0042c2d8584200c04010a9400001c54401e003156026140d0942800030341c015a0740700d0100712403500d0140c0c00001500f219600c00d8000d180c102e0410302403076260501c1c41e80f11540e169009601c0d44154003401e02800720308110340c80f60500d8030010349080945500395858408141c007142e044600300e15000b18030076542c0c900130b0100601513a44508011003841540c01b40014074440d01400c0002c0001700390b100706a543c01a0b083c03a00c1100003002401156070340390385510034040003403800d07940aa00007d40c1009901c43c230780208040c00494001304419070100c2032940544085801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 666198300 1250 666197050 666197083
    0x20105070503040b0a0b150d0b0a0503010c0512071b050a02091015050705100204080604060605010e060304061503050d050d1506091502101b0e01090302090109090201090323 76
    0xc000200d40031301c40c00e50304081c01d11004a00390180c1da002a12080030b440889581050000b42c62090300034992040d50076110a8a011502c0c90343d440400d030803125994440d8021400800c143c1c04400c810303c0d0b00541c08034260a04c1240a0007051006000d8481c10700e003203806521202109007986007205119500c2540c1c1c40000031503600b01031507482a00c0f0f51020117030502c0b00100d04801001000d10007044203195030442151290390b00c59019540e00000e49050f92000d15100e0003250651080c0c41d11003d0740d9010f0061840d680f1907a0321400201200c40600f2a840c45e40754001c40010814000f0700381243c45a42d42d60346a03044003d0040c102c03410300c1d505066071400703500c1c2006015001072080007103a10740c004000e5100d04010040c0e00344409002e0760306809250190203400c1c803c601d08016406485942c1c3c1d609540902001503401904074040a54800c0c50702c00108a03024207900b040d06420b20602d0b00110341c0f5030f82c1c0e50b0509040c0c0d440e8040a0050030140d0b0803d55508208461140c3d07040105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 666199550 1250 666198300 666198307
    0x4050f06060f070303020913050103020907021b10020109020a060e0406090603051c020313080a03171014060c1b0f0a0311040203070c0f050106090e0106030c09090c051207060201050705 81
    0x4000401c41d2041c075a01c00d030028000305182c0c09060007541950240f15014044056581250020304000c2c61300b4001244a81008004100928030001c0c1c1c1c4406040d1004511500381d1004003081501c55211400404540d01d036452a40183c0b943c0414400600094407402e04100d154010842903610035080700e541c00d4074020302007010800c0061172001040d94440141044c00a90070100e0452044017030f0b801c4d074030701000d400040024002544141c464060340c1c84032410003140b480322001003801c0d0b440310b83c6c803040c2010511000d5100f0546240030440200718501d0b10004041c60b60030b042003800c003a026860200f142140382e04200121b8292500116400b5040a05507607460300150019405180070f140c0c08000641054010b0380c10010340f6400041e6000c9004803860050b010308028052036030300038102003001160400501480058070350003070000445508101180f0010001a102034038030042c06040058991078000c603104125000b900904907490800001900355000500190200321040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 666200800 1250 666199550 666199561
    0x40f0b040507020f060a11090303160317011410050d06080303041203090312050a02090406030f03110c010c020d170a09031101020d0c060504111309200904121206030c0504050f 77
    0x1045d141c1d0304c40301c00d800c0060591021010082907020b04002260144030002c0c0c01c4507583d195070021000a44607a881c1c41400740200740b00ca18103803080c80b0702800c0d00403150840c2d25501d40300c41040c440f55040d180040c10441c4c102c0301c15081c4c65160b402000250030010920091203400c82541d19100fa007810180301d403404d141e6004120100c01c0117592030413580c07140404e0b0380c2c680680464403040d200070010301185440c1c4c2801c4003000c0242404501003100c0c041d00d64a400400f08803546801c005031505440403071940c00784510b001800e8421151019800303260405038042c08090016541c069480c02d0400c0e0031751401c0d0585800c090141819584a51440041c60b0303440b40b444050300b43c0c8800f02040301d071900c0c50040c06290700340a000340c0c080c0c10040900a480d50030380c07100c011140142d6864002d00703810300d11074501107150751400d0340100c119400a0302082c0290a0140b92920780e1400590a017203451003c0b0807034505400848103202400070030049440e1500925800100b480203202c000d00740b5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 666202050 1250 666200800 666200803
    0x20c07060c2109051e01050a0507060603120512070302130902090102210319090b041115070f0c0b03070c0b0c0706060305010e01060e070806011d040f0b040507020f 72
    0x2610590302005141c5425008200d05007805404042208004544920300100054503400e541e014540c094006034001c00750301149407040108040c8107858151038500c440008417801c1d0301520742a0342298031140000300081d240301c91404460020340c1c403613403910801030384451070410103020076080500500942a10780300500441d4125031300d2650040e6580341910050781010500c45c040015190482e00462003207548400540c46862210789035071034810200c400c01c04a03035840c20040e0003a1514000100054030205085803c1c1c0002825201104d0384149201f2041c0c0c030900d02200c0069036072015104000d186c1180780044c0c14480e0105042d40b8003208000e1140000820142c010741044000c50740c011104003c0300c00c0c0e20b4212031700b070282d16240e05045020b8001c0441d01c1d6541c0d8a00500019121900b00610b40540002c1c0c4c1c4489094480c1801100d010b41c3c8204400850800c038107846105540ba44500326070184a02004990b0001841c10031084440051851066400c4442119000c950 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 666203300 1250 666202050 666202063
    0xd0e16060f0c050f0f1c080f04020f06042301141e1c1a04020405011d0105040e0708060102010b011b080c030d1d010b2d030a1e15020c 59
    0x12289010038070700030000c0c1d00319161849140040c20394002e200300a620303944041420a030829600c0c040f218000d4054034070704816001b00c642d0800003401c041c04104103412111050750441d0000341140b546511020010354640d0007548610042c9003d6034000e40f00d91a210203211021000342800400c1c40700041c05a4143d100d54142d4552151034003180174040f000d00c1e825030302c0580708210f025000701c8041070380780000d0002c50446c2c00b0881810142c11300d0782c60940202c9080d5501070303440018110b00010b525900c00c0441c00502d041c0103003800b0100302c1e0003001035404e200e20305c141c8d1940540d040c040006821500c1c3c22088904004c0311a01c0314070004043c031fa01e1401c42d035001007915510a1040092425801442900d1079080d00b84550340350010329503503100f40c1c90142c0c1342c000c100c107902d25410060000780c8511041c580513109480c18055040c0c402c165007038a140134050710050016940c5050816048009482840319000c44003414070170384030740c60030b010001c1a5045141032842d1038850b5541d02d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 666204550 1250 666203300 666203309
    0x3011e09060609170a052e06060905060703050c0d03091401090b06060a031b090303080f010302100507080d090804091d060105150c03040b0a0e030109150f0b12030d0e16 74
    0x509800b000813206008009641c03905800c40c0c143d03140d90b00328085d5603c404d01c1003c808400c0008400444140d006184204021200300e84c0310302c1515807410007800029002a00c0c143c051200c10b000c40d00d66064248802c0e11f903040f603640c00160031104c0d1300d00000903041445501c0760703581c50190a100010a248101038011030111411602c804404204601400b0501e00c408000008042400c0c0d045400c0031445c2c040d207100340c840c0c900b541d45103030307030700c1d008260900c006584071143c0c01c403d0074450300400c000c08495005800003407814000640d0803080e44d03168141150702d900300043c10000103805206640103003400321800005030500314800d41c2d40300018080c0511a07010034031020896403928048500000c50f0701e040d41d840340c5d5a00d11241c2d240d000940b5a070082411500c4095551406201c0d156100340d01c40b0450038100354504030300009200102c03050905580d00d425001c1560b58504081c8110440303031000b1540d0324800a0303540180e0b0405d001d6881d05601000801500d004522000e0003501e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 666205800 1250 666204550 666204569
    0x4060b180112060f150807020d05030f07110a21020106060815030307150506010201050601050f030f0c0c0307051b041107062703022103070e01050313050303011e09060609 75
    0x10782c8640040e004041c030b6441503030380d01540140041c5940340c205e010b41c02c0400c3c985908a01c1d55070004240d0711480640300890024000700001400c0c9808041d006070042c000b450034419054204514601d0040a0403098480202d60658140402d81000fa540c03402c0195100034004c0342d260440142480c90042d00c07002c6c92030105803804c40e060310100159090703103800c1107145008100000c0c50318000c280c107580b114015400c000000304194002c504030f806060f00c110310145181d64050f0f2000074500c001d0444d50070b0200c20084222001010005400080d018602506444803064201d801c00085821000c2c011401c00744441040c4080b441a01d003d00d030440800308062050750030f00d561381c82c590a4000c5100e180d11402000349070b0700150b1070760048950000c0ba144090400040d5600380421603480000688070070b008012944180040c40d044010442144014091076a6480c02c40c2c000345c100c4d006c0c030004140c414601d8000c2c8c40c00340700182038240c0c0c200001410014001c20860003800360079203a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 666207050 1250 666205800 666205817
    0x61d0a060501020a14030d1103040606062606010c0209070207170c031507090518040308070c082b020d0c020d050405060f18090a0219170115110f06040204060b1801 72
    0xf48005008403050411000c7c801c00101444d003805800541059a090b519070b0b14249001c5103035402031111111070746109010410245880864054000c0000c2100d4104a50520310b80c005852b0940034030f000d21215005410914107001d6a00f080b40c100440e00c480a038000d00315040d0645000c5407002d0071000080010390a40e8603a02c00303030b4202110740d2007660841c1c240841c0400045040280a018520030741d59540240c0b2a620229081c9100607005803410340d0820800300011982d00406180d040115030300d80041c00e15160f480f040360012429410b00a417281010f05d0b803940e041c40414000c4500b801c08505090915000c199076006800c030344040e40310005064031140c1c2c2813010540746024002c201e1100f91910382040c1019401001c8100401c0d0404110104128041d164283d03e00350040000d14550380381803a03544008400c15102401d002d00c030840202004001c0c0648410540d000b001030413103060920502080742c1c60f40d0f020001e140b00502030400000580c6d0325042c0c1c920070901c2c100c040d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 666208300 1250 666207050 666207083
    0x1911190c020a120812070302091c0b1f0503010f1a191406090301090f11010c021c0f080a0c03080606030115030f1530050303070c0606030204061d0a060501020a 70
    0x103880c45034010504041303070740100f0803009a516800409d02c04000380c0b0b480a50600c440f450702402c260b141001040440400001404884803e424119011240e2a00360703220b40d079480428211440001c4500d40d2a840d40403003000d0740305416005c182c0c882d080c1c0340000345085408040e2101e20441c0070b4040e92102d0084100003950f60703501903c1421324020000c00c01032040c0d10b4150142b014005007250041c103180c043d003031950f0007120100005078016081d81c5020b462a100800d28444c140411100442c58492610101c1e10f070b000a403404460350348446119440904010380500782c0240450301c40c070410070040c80781d05800c40b001c017101c1007036017000303c0e100030150300c1040a07010045520703100c0e280d182d8001503c014040042a503801c400982c6002c440001010007881c04800c010281c01c0360301c10000300302418450140a40100d0065600243c0d4640740d6000078280d4200f0b501a5150745001403030200000d03c03010303003c0e802c009114800c200e8140303043e0020391600b980d0340c00682602c0b1018a03243c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 666209550 1250 666208300 666208313
    0x108070c1416060f2d081009091511030412030911130209041506090b0f120c04050906031b06160803070f110d090e1911190c020a12 58
    0x7480310054a0502c0000b500c0c0c18004040c4401c00c0c008070300140c000c0480e42c142c00702c0f18210200401c41c40e00031428214030200252000c81029054103031203801d50300c0018865070f5074400c0b440504e104040e52411086000b01101c2621445194100702920410901000550710405900c1402c5103050100d010403403402c103110400000480c690300058400304c400d4010f001503004080c855411142003241200800001c00070b80902c1c0151408030b041103c00b80003042505029084151503e03000d54548688030310780701003440b0140c078440c18004021030b0078400d61821000041c0d1205080d00141801c41c00c903c01d028565440c41880e90250000084908140c0d1305104e020440c203400084403581e0381000325000f0601500c007058000041c92901c8070070b0b21141c020030b0301c459a0042e0b54402d46a9410600340004690000e440810100402035580c01745810500520120720030070038185803104001a0f0f141c0590b0b25480c400c1080201003400c980042c0e40c0d40d0801c00684140322802c0318040c03800d1400c01b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 666210800 1250 666209550 666209563
    0x190f09051c0204050f090f031314060d0c0305071b0c06050a030b09160f140a08060d050f010b0a05030f0601031202010b090f090d0509030d0c15060608010905060108070c14 75
    0x2940080c100f070100b10100205d102964000d540301d1040b20303800502910300355128003030801d80b030641c0e02d0041c80801c414189100c3c40d44003040d0040c002481c1100c060b0800045034261040780303020a4440302003000e21908010200404400c8071042c15410b103031a6503030421510700e405110144980880e4040a80788260b200b41c0c007515014100080c2800c1c08800f0281072400c0b010004001101c0b508816494bc1c17003001000801a1040e03a41810907020303036401d8920b690000e0010b81c004c04031041070000310300200b00c0c80c081243c0100c00001c0803640380c07040c01241d00d00740e08514041ea0051010280340d240028040341140e0300b000759440c881030102c1e0120b001d00054040694042d90345000d0081d4000490311980c041c1e8074071400c45401411026081e21507000c1da610155054100007050300890303004d801c5020b103591080241c0301510603039040580807100c594112100043c04540140030002c0c0f584121a08a50242001c80b402e1170300d00700c02880d96000c48801403100d5140c11440050715804c1011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 666212050 1250 666210800 666210803
    0x1030c020304090e0714100f08040213020a0e24040e1b0331030c080a17071110021201050d050102070803161805010806060f1e190f09051c 61
    0x240800484020425170b10909409070116805c0600030310103080c40c041c0c01d68584519291a82e201010180c04155500b0b04024001c3ea001402e0021f510488689840109603502451b110004102e0510061148511240c81c03101070300503401114001071803895013600c04480c00c030394aa002e15602d4402c401182c426100c001140340d9004002e0101c40d4a80d5075111003010f50155803e440c2c040242d00260001c04000381c0500460b01140d4013402040d04040100300c415018200328046595120030000104802c0f00c8502c0002c40124040150381800d1011991000ba50315095040204210600392103c506204661007190024034085c00c00c0001e4041c2c0361455040007140f070b244d1602c0c299098003420032641c044001540d400c01c04c002240400300d00804d446040e0b50307042096030f5003001e00c8903035400022240403000b0b05100c031222035880030f015001101046002d1949441407101d4950401111016120a100c0403000c1d40310207035031000c100c10417202c2c1210b031042c2c00b803440c031110044408004c90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 666213300 1250 666212050 666212069
    0x8061501120c050d1127090a051e0106030b030c0603011a1b0102070f1e0c030201032301080c010237020609090a061a09090c0901031b0804030801121101030c020304 72
    0x9045803400d041ca00504100d4007400c1c001c401440f1b40d282c0b0098400309a44006610040000102d0f10f42c441aa010640c031821a450200003803601d02404240c80c0800d91252001a1312084035181324102885240c1d28180141c405500307650411441d5054081c0201100381150b50114003503284841e01007040c1c013042e2440008554888407402c02c801c1040d4100d405482c0d01680c82c2c0d042002c68011007130390424541007140340503040c0c2994011800382c030b0342034122422700300020324210140341624800d07030090054500410020101e01c00180c1080c031a940000381d92200903007048000190084092500310409003070000d1856513200049184c024084e0741c5400003003240070031495420710361140040c3c90070030036403039086010300c07000d600300384a203041c0641c002129501080740c103042c010282880c01014100071661880002425880340c22006000e00019011403d00c010b25070130682d403d01501400c03c1855620038680c070fa0344091510a50440c0c10145e8031608508424070a009444c0034107402c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 666214550 1250 666213300 666213311
    0x6051e09060a0507090303051e04050a0b1210060206040b090a061404060e060907170a020904050d030f0b01050301121407080d03060506090a0515070f03080108061501120c050d 77
    0xd49035610203003158049540c6150801150a80d4000c1c44407000f186d6140e034800e0f00c1c0000c000d07100751000c01148007410341d0703460610011805903515403403040a070130100020b584840b04285101c0ca1050b001d4030880e81048410300c24000703503602080072030f0b100350069644005034662015403071424040000c09000645132400e5040c1c040020711449025074000c5809000b02c403c1102542e46821080c1c07000002903000d80d00400c02001404080c805a111000c25030f01416810f8020503110201110200c1d042d410840500c042d058040c0b080c071401288081082100c480b4000000e4a20310040c001d0800d070a1f4210b08079000c00401080103030751131101c10181d507045907541016607a59014144d00d080824180440400d0500f4050305079a0045401441145014500000c1c0714144003000141007107010301b040740301c002c0b03a8503e010040551207070380c9000b0990314081038241082c10240059241401c0c0c81034680560707a000091011000c034611001a100040c01c0c4141c82a10500903060701190618 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 666215800 1250 666214550 666214561
    0x7032003040b030903191d03070b09010e0301090c030b10090b0d140c030d090515030603070b13091404020906030604030806270408130b0a020d050a0309020904111f0c06051e 76
    0x19421100600c00e003a200c0e9250107d008264807070906c2d00456842400c20b100c400340c2984200126001504050000100308042c0c1c0c0f601ca911440c1900181c4110703210400380047d40900501d0300000304807030f607010844032105100280403140d000001620a0b12500b03590950100c060200c548101d50040c1190410501c41c0da0240581c0e03072500c646403041c245108500300b642043c0b41120720400b0f00074040c100c0c150411a4160407500a15007044181100c4c1c0d6010030480d88500ca8820800d8001120b48a64a0b09104010182c00001c2c6454002e030001c000380700c0082d41109059422100c204c0305400440c80544036200c080300c03642595240441d0385014402403008442c001d2110404008114010780e80f9004280030340e02c6105031700f40040c1d05c070781e2003522030b203224101401d6040741500d40802d0481742c0f500060000d017010344040e90203000300c1c2c990094503d0031504489807000300c85000303a9140840d180c00380c0b0301d440c0380d5000f51101c1c0e202c00000d03020601120844040340701711040003e05017002c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 666217050 1250 666215800 666215807
    0x120c0c0201080c1602060a11150a180218221a09011401030305031902193b0604090903020a050c0d0f08130b0c0307032003040b03090319 60
    0x1510059001c503031520049007070683e0035411150400c0988401e403440c08559424400303203903c0065003100f0004d040c05110b60300881485101c01c40e94000c0100f22550030101c103220103c0c0c4038604030706402ca00654103400143c0f00c41c0600d00031680c00a40030310b070301e5607550081c542d40384600040070401d0309250703000020040d2400c0d0f910103070f0302c00f01780c45c00d465a6001e6032242201e0504007078541e038006000040000a01c1000115841500a41c550195035041041035059030403a04004008490002e07001d09865480902003456401416030076110910701080f000500c41c2c07507481c1d0401100903a402220b81d4503030004842c024003916404110f44405400c00a445441c448c41c01c07926801411241c200c2443c0c1014010000f51b04901007907484415aa18585240d1040360048442074a80c40c0006412910f500680700c1120103a0240d60760b445289801486c0001684035410007002680d4200000f0000009803000d45050321102c541c0c03078a41c0c02450745036000d0110685000031903032194042507580b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 666218300 1250 666217050 666217067
    0x724030b04062d050609060703020109061404120212030a200a03150b0307080604050405190b090c0613090905160b0405040b0102240705090307030c14010c080a0e01120c 74
    0x4040f0402203580f210b200b00c1c4a000c0314184034441d8017604c01d0090301007507d00180181141482400000764680040d41c0700300179a6012405542c030030410404120038458074140a511014442c4042c1400c000024156011400060000d8208968540c0041600100d2181f8602c804c101c000d619074031100c1c9034600902803c2141c11007529441c0c40c120002c0c400580800b070fa40a010700b0b4840402555402c01032000624000b0000c2d182840780705d18102c0c2030b06214130345d012040c0c0103000385001860108242c918051000c82282c1c024a41004011041c03101c06e40000e007550803560020503454050f0400c81e191000e070014400c088144908001400100a001441250005e58003072050791031500059894400d000d403040720f06140d40542a000e0395111001c1540311000d400c12500741041070010910b0701c1d007a60821151708401400a1140ca00500c3c8800c0c20758909182c1a1b03030141c016680c811241c0164140c0405202c00f210030301240368000d01c552500c41c407001e5001c103c05811403000510f4000e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 666219550 1250 666218300 666218339
    0x1090606140a1e0905220b22081b030c070803120703110306040b0103110f0409241e050d0303090c05010503011a090415030c080f0724030b0406 63
    0x42100c0003c0b445a4640079a40c514540f90b180103220f03203402e06010181100410501c107549002c4000c1810241122403000c85038007420320101a840d1413020700c200c1490000d803101490307440707500e02c40006084108072026281d070407500000c5522106119460340c01000c1c0d2259a902541c00d010600e003c001000c0e01240326007081c4084152640141901128054603016042c0c1c60100001151070130320307403c5408880418540055450a075102044154002005030041a000050100802000e82c0151580c4803406111940001c8001901000c0041d4501c2005d00c80c0b19012040c10520444100301d10040102511034100e0115524004000341800c500884a5455200003c210f070f51060003543d0584801c5c05006160000e415002c0d60981c00c155405640240c6440e24015003144404070344000f5880b91700c00482075420841c1071814018040400d01c000e038001d070000c022a11a92b6940c10020204000880c54007114440c202e0180030154a0250040e0a02100145414040109810749c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 666220800 1250 666219550 666219559
    0xe03160804151e050f090f0109030602041206050907050d12110a06020a1b0312111c020c10050730111b1203011a0d05130b1617090109060614 62
    0x11800d01c1581d250150480c2401e940005010b1b2038007e081c500c0c0c0110203000141440e041e540c3da03c5c1d03510416130303005400a88606074807944150401c100c5c3d0107055001000d205c0038080290400b408900742d040c3c2c001010b804c0c03120400c50350040070f0240c140c0c03211042030132050350349401c1241890340184d03001d503211500041101210400d0600400203002d5031b80c2c0d0541d034405181083c107400718068040764407100c000c0c2004010129030841c04c04510000602210009030303c03400c52104460500d0100c1000003500c038144400c0002203940030301288425901f0030042400c1014422411410742d0381d980355600d1040c5400340e80c5c404000c0c403801501e40e43d04940b45118075406041c074000d40303a1803603141f0007a004c00144018400d1210046c20410f0b025900071855040003d081500710649405444204003540642151b2050010301c4403903550060090284940000070f100c1c00900c200c1c6600c070b1902c00410300c84080340b41f0100070340180c101c3e40e40110051004c6600d900a030f0010010103800288203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 666222050 1250 666220800 666220847
    0x616060c0f020c09011e05040213060e1507020d08270a05030c01080c0a020c03030f0d06060905030a02120f16140102210306010210060602010903030501090e0316080415 74
    0x1c184001a100c2140d00060090840c0d64039000710920103052040125840003501000480c054569102030a482d4503500c2c1446549850000d0140c55a56881c110502402c881801003000c1404c0d48101e4810340c5c0e0544c2c5440211a050078002c03410b008090321041e2207280c58aa50901007000c040c034010700f000403280c0907841030f40c0d0f0b01096a100c041c1040903002c590002c000624a00310b40340948081780f014010380b00080c0882000900310b90048807058110070010a22403023190641c81090302528883c1000c411031800c0c10f0000b0b83d146040e000c028803d129074002651048070600904a9a00b14030007142c1901a0102c08110510404d002e100c0c246000007070203c0711984000303540074050501c00c9408000250403007070b000140c0c1c8005c000506510500c6c60041c02c0790030902c2040b006020075800013422142c2c03460010180c900682c810f2016904000e00510140b502100301c4081e203504441c1410814010302e0860418041c035031080210000d0a45801141c5803c850824289040410070081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 666223300 1250 666222050 666222077
    0x3020301051c05010b180a0501060224070c0c1202180709030b0403050c030304030306090f0b01052b02121602060405060c07020d05010c030f0c020a0b150616060c 71
    0x4a00091050360b03030012081014929058034501000860760040c1c0000c03488162510108028211144180d40c2001c030500030401c2540a510900c0d0140c8950305c06468109042200020001d20101d0307038041135152000030038100c41c01544500801e580c0992007250072961541500c1ca60a8960350030f9010b694090364095041401d801c482e80700c0d841d2030300c400300c0340c40c06c54440b030059440003030007182402400c100821080c401000036520552080d0350200d200c80c00c1060300025503c0300d08c81c4014950400c0d92159036070f1b80280c01d4a000e444031519000e540110404941035101c1414001007074984002005076803031092015191240d081c0c200f010080304407600080380d48107011100604940c20200100b0400d00c0048001c113940c80c0011300a51030030001e91252821103030381c5000d4401007aa200c0c1c4030034041001b0300494040d002c050003e052038580548486401d95001084c0011640705910259210b954080550301e0072404e00012200d040c0c40c0303260280040c5500580800442d000e01c20060 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 666224550 1250 666223300 666223307
    0x11e0602060c19110303130c06111b0102161701050c1305090402130203070806010f020a03120216080a02030706050c0403240b0312030105090903040f1a1303060912 72
    0x10301840d4164802d03840d02405450001218103152003038001c01820b00c3c101145801c0401c040c0d80a01d1780e000305401242a0303842c3c500d15000c043e41c0520b0611010a04112180c400440c02c1c0c00300e003040d0300c1c04817030008035200101c3c00c1151317004610303214050400c40414108544c0e139161090040c142e008004c680c4400c841d06c040f50062840d2907489196012080c0641d0408052650304248098110821b03612901d0451081e03802c1201c4110006400208000f4650f0380314103041c44031001c41c000740c2460b43d40c5413802400c0310700c01c3c40107802c0e9640019040c86003050074503484e407000b40c226100613106c85030603074000d4982e444510243e440302d060101240c004000c5900319800c495000004500d024042c50b80c40d501c00001103100c000c6c00d96544200c603016281840325410503004110320941d658148420041c001e01d028015078443c0d80140014010340b00f6040501069030400040750100781803101c074103007036482603450080c002e11020f80c00200f001100d400c0402d01c01d224007130b001c0700d0004411049 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 666225800 1250 666224550 666224563
    0x1c0506300d180f08210d0203090604051203090c191520030a0804060b040b09131505010509041728020114060907031a0301110a090e06090703020a0e0306011e0602 71
    0xc00041d0401a501c104c50301c509100104a4080c0c17005180c1007100c1408042d00b241c1003140d0110765a001002040200141442181c04440e9440340007811070800f421032503130f0f95034051005400364500c000c1d1200c64100301d200c034000801c0095480c060f20039035050010030031000c2250615002900000186103e8000b00c10b54203580b8647e5210074207591240c858201070100000f20030b0b0404d0303448412071010344807030485610585458803004050810391622281066854820061440c036100040c0001e0303541c0505c07190800c1d00000041c0c20b41000000c64049841a0850b0000c550b00203880c2c1d06100240300464441e560a51300204a01e008008010301c4c6a4401c8505c03552180d0200000344041d402544605605251716298581003011000420b0071907a140ca038145070a40d010070b07a9403859170701c030349000d01900c60200300051506110f40803c42c41c0c000600784406040e008520b074100d06200d04100c500c903102c01001c42d0b641d56550004000000891040d04141c81080754010130070300d0000820 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 666227050 1250 666225800 666225809
    0x3160b0106020d3c110d0c0f02010c0203030d090605010e0603010c1707020115030b060f0d03020606060715092a08031b03040f0b1c0506300d180f 64
    0x21899868540e40d5142105441a5002042404004007515401c402071540c404c10111070b0315801c2544000c08440c52518980485007002c0184600402000034a1041e15101d850340c2800d04143c0030205100007804d5019000407110442e103843c0500c3c00388442600150f04907041400c2000c1642c6415040c1404d03118890500c0020070085134841c1e003420113407082603600104610000030348241b0f05c43c0d50781c0c2e020115802174409980303602c10300c4418a441d4804590041d01103403080708440d51030758040d44400000f4003191061401061101c2440501a007005000291107400c01c07065030345107800c0c20603150703049840701d45011040d00d4004500440d461a07040d00c40b404029402c08121201c18070f543c3d852110300840c80e020a10000840c0c2a031304440c2006081840000c0791100b80c0b08000030503a032001d80c3d00c0340c0100c0c01c00003070104586a000e0f0302124801c11440c40e1910000c82000002e080b0b018942070030092140d80421006e5541c090a540e03662643d90115030031065a54440101d042c0041c0103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 666228300 1250 666227050 666227057
    0x3070b180f15090d02060d060306020909060102070e0403030203040309030206030406051608060d2418030201110703090303030504050c09151f02330429010f05060a050c03160b0106020d 81
    0x402c00c03a494281011101365100420322403412800c0011401564903907441140c00c15004a0048500e10300940c8184d4400402c0c130003050000e24083c052140001d010b803010741815070000100e428103101d04402c00c09550098552a039a0605260000003007004036a9a131b07003044044d03a050400c5101c1c1c100c450040c0002404d101903010705494060310f0a07181d510240d2100150940d07002003d005010b005d403040c42d60745006055210508000e4291090002e034444001020800c400019030800c2d220030543e5014900042c696580e851701c0341c03410b071100c3d080f07030750202000d410415030075502d2030074421590060780c1d8404003d240c07500c083c0400280400c0e02c030141e08110001080e42800b00c45104840c4056a0003040035000c2d400500c61902044d681550941548000820f903042c0842c900c10307800201908444d410b6241020680f0b8232040303030141c244100b42c00a842400030344190140e40903400303a103080e6030340c0300c200c400c039101c0180c4070f0241104e40f014030030000100503001203641166007480340c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 666229550 1250 666228300 666228307
    0x605060910120c180b0a080c07020f0307030803071209081207050409140618060904060b04020d020d020301090b090c0d090c03150905070f08031803070b180f15 70
    0x60411841c565040045010021029603460203640d42d80510040140d154590760409041420707205182c074501c2c0c001030300c05a010412484032940c030103039a6500c2009040429155040e0703100080044e1450700b038040c0c0c5446944000710074407030410011030040310b068480000d15240c410300481a030355921005891054280a0605500c00c080c812990182d0f251a10a01d0141c840f02001c00700c0307511001402021401e0350802c900da050282c0b4044469544241120681c0391600000d5180480184020199901d401d41c210090f10380342c0550710b008103901000d64885420381c1122000350001d100b0000010b0800c6040c40842c105107a00c05d001e0144400c0b00e9140c4500718000340c0c0034003005281224041048800040418281c0044042d40e104000011a21091a041a0b80f400031203401c86c00080003150b008014071003000044807081c0c0601d21603540410031400009043c0341165000e003400e50340026090601c44406903e810a099040325001c110b5040d48044c0550092814823141d4504c1c42007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 666230800 1250 666229550 666229567
    0x20c0414011a0c1e0607030603120f0921020f06040305030f0306030a02060d0207051b130509010635060105010c0f02030a050f01022109030304150228080a060506 71
    0x10b49211028220614001d140c24000c40c81c080c03503c0080b8204510f4041e0404090101100910100e60828568501880f1040c110744070507001e003000000100911420446600c1580d005084040082c0000c01c40a82c0314008101508901030b54007200321721a10b1040040c1c4100e00e4500d0545060300d400034015420408a000720103056071010780f006500d84952400c010041e0b458100038541e007820070a01507241c40d0186030031880d1080401c0315036001c1e42d0f1504140c1c06901c0312081c1c80e21400410704042890340350320361110b00501490b041001002c1040e0200031415540a50030350b400565819400c10b081c08000e696034a560b030a0144c40d0009825004140c0819455440140094001001c3e905c51007c9035607914a414031016000841c3d07500821802c511200140304030240b40d854001c010001d01d4185e200c540c803407000520080c14641c2240555a8115103076041e1003140d142c0c0d00000001d4401039804900941404107040002019040001c0b681c03107003402510222000540b0160400140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 666232050 1250 666230800 666230819
    0x1080615120a0206071119081207020d0606060903030212090a14030c222007060c0c1203050f09012a032405010806121b06071a07020c041401 62
    0x407074000958410301c0891000360381c80c0001080002c0c460b1010464800301401444902e18590036002030303c81d00844200040d41d00440c0241d03070704e40405805075407881c544c40000c0c5400480800980410315005000c00d00c1500083c1403400d482c025002c44030781c2c2c0d24900c503115103803160106d800d411068011040242c1041301d00d940002d02e90050689076856421030128004a00c00d1054114080003441050030303c0b011441034030561005914080c00b00c51750082020181d20503071034020203559031804000380140c070032800341811a41c00300d0400d03010f09140000a001e40b00903684140e1001020b0080345502005105654010101c5942034130355548110050b8001d402000c581014181c0300c071404500c600f424040711002e4030701c403100800b450741000001040c0c0300c40240128000c103844c1e030302444038001c0080c00703111031074484c1c0180410f04510b10104007103014039100100382a650721000625428030310581c622603003481d401ca6080c1b500d44010001660019000e0000c001046001489240326 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 666233300 1250 666232050 666232069
    0x6040b150f0403050a083c07152406030e07260303070509180603101116050313050301050717100308070302060601032d0b060702120303190204050906040216120c030801080615 77
    0x6400c0c0e2030712a815a80450142c800640c04041e920000340e00d00341c0c2b241c1000c000100030b0038252400300141c141c41c410840d502e2019008012600d40c1010842011810b10560303030102001c00030540c1e0326410718500123403098010780c0b01c00b445410641d198000030501c00440c20301c2640014010592168076600d032074000d010010100010b0318003080349000d1070480c401c041d41054410030040d940d07101c4284018000340d0454005a100764140010b110b0410b91048100d010032040a150068a80750801d1160840c0244d510080035110701145100c14550040b440c503200b11020b8078140180c0d08981d004142c0c10194004842081c02ca031820746143c3e01c0140d02c0710041c0d20f00500320600d81603040d000680000c00000007003015500000801684184282c4880b0004440000960420b0b04103c00200d03501001002c203400b40d0380c00304140d0840d68850804400441d0000201d0300007000700000104001e95a580980224015200000d0180c00001d0001d00c150004905003e59505203400c000c040c4d00e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 666234550 1250 666233300 666233303
    0x1e041a0711040b010e0301181b0608070f05041220010206010305060a02070c0e090607020d030203160507022d010e120601050108060303040b0c03090906040b150f0403050a083c07 78
    0x56862001d00141c03400d100300c01134181150440e412088c034901e400105d00c00c901c9844110000b001c502000301907040482550042054148003030340781002d440031112402075900601c403502962280001f4031240c000c0300e079407003544c1003548840c07130301c81000590340e80b1000e110051113a44103400045460b0020350140c64458826030134409a03585d00c05040c0d14554003501d040c1002d40000045c025004c7d010441c0759030816107801c0650031450000c440c0ba050303914800425041c02000280a0115590072007188541c00e01004500020104415017a0000003101ea100740803820580081100d841e04090500582e0004401060181c0c03c20004465040780504940c0d00341c44180000b054110203076000c0c4c01e0280d00c8000030b545034509202040a48103000c0c01045c0254603104070503001e40c545c00c044444178500080c425580b182d166003882c2d4184540d910191190241840e00301c00c0001e80d01c0204034803442449288019560807601da860340701100034140e000003803a134089903600903c001406045 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 666235800 1250 666234550 666234557
    0x105240f130e0105010e070e040914010203160305012112030603021201021e030c0a1404170105010509010e09030703120b0a0e06031218060c031e041a0711040b01 71
    0x1004054040348000c034074001051106501d842018a211500f48280e500601c039880741c4100f00d003010f0078050000d01e40c0c0760100c0d0285032600102420b000d003103804d040e8a9402c5d08000c564901d04207010481c5030315039a81c9480041d0400000207030032042010802c540081140268409914035503c01ea800c60001141d0024140c13500320010241e985c041d510100420050005a544c038510f10440c0c082c5e40791008580d24031581442031047e0354200c01c0544196140324180120300801040880c8001c0c0603552201c4800070034180c00443c0c084d01904000c1c100d0350250ba0000b5a07980315030b80c00c6400e00089481182940c420b2050340e001ca0712a410402e038442010b103000031901c000b0750108880c00301d9904a45015021007007801003500f0200842043d420240d51443c0c14006000e00c01148540410f499070301c202c0c400715050000d80401d10032241a6104104c007010305d000801050034040c2c00c588220448500500c2582c1c44004541003101c4955a000d0010800c24400e1410880100448041e4a040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 666237050 1250 666235800 666235819
    0x918050102131a040b0f1b100e0708030705030a1d0d0b0601020d020d08012303070f050a08030a02100911090108030c0c1c02010806010c06240602010524 67
    0x4210207100600000d03620304101e818143c18405903840d09000f0300300007003510304100420004a20340e01e0944403c99007071a2204e0b035558100f09103e103001700c400b804410b113004808614104070940c0d40a0865080307000241c61000c0d985e01c01700c036268042c217540070b00310750030420150f542d0b5131040c0302010805c0d10021503840c2d407032503c801151420512070b00840d02504110140185503804101d02001c0880a1000b019661160300c0d00030002d04062080c2e10300003050500c4451071601034640019030382005011070709001d98520700c1500020440c82418020620b143c0089440308010003244c0000186030002c218030b00c03040c15580c00030030340b031102071341c030440c952540103500d070b55810902e8001d1650400660312082034228a60070140e803440503520901c001d01113100308100c0c11901509490702401d00008580d00d007030050b0707241c0c2500c5034010a00741c40c0203c03c03801005100245902c110203031040c41000ca44035241030b800c99805592180b00301c0000740075844002c0d4007140c035030200e403006031902c82d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 666238300 1250 666237050 666237053
    0xa03020a170108160e06010c11042405040b0a1a09010c0602130618031109070c1a01140103060e1f050d03021509011803261302011e05040918 62
    0x511083c2c100b10b80d190040d02102d0311000c000703000b1202411000c042d58407507080c40c00028000101500300140203c88030810b848250341e80341d01c0b001490300c883d10b0100091300d81001e00303902d40341d80b4010584181e1900b0011315141c1007203c000c4013070b90071005072042c0840c40040100b03c00e402c0549000d04010f0b00c0c04c403040004ae0580040d1400181e00f05443c162542008000b821954a0001500f452055500200081200c1001d03c0400c45001c5e188100726071500303a41151000340800340580114203440c040090302e036100400b05e04994019060013250382d48100110161003c0c0c1c4201c10241a4900119000152414a40501004071814800aa69600c0c085060054048415000360f0012891907941035040d111a07a407101101008211025030004a8082d01180401c0078040012000d1003071040030200b10340c2c03080940c075170170600f000b40b03000c807a00207004144680490004000c034180e00714a1500340d255408811844d00d42c0b504140c24802c1150041444940a01e082c1c110f20803d0340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 666239550 1250 666238300 666238337
    0x90b1c020d171306020d050904230117101811010e130f050a0e0a030507170304060e0f070e070f18080105061002030a0e130b03060f06010e030703080a03020a 69
    0x1903a10001c0c0c3c1d101c1010022451129901e6888141950010168000b4240e0b003c82252103200046070001030300c0303205a000950710003901c0c44004400320350742e0000c030f181d541e1002c4900300c402508040b00d4100302ca4502e01825654201c2001030b000c2c149400140024185c4030304000c1d844410314000303941c0141c510004103c070101940003a200ca54808542c80e1030040da01030f0950102c0b41c02c0003480311581902284d075990f61a000050104800810120200441484010380d84e40a440c42c550316401c040c2442c5008107140403100768207104084004044a278003103010011103004244101c201d03500d400094401124281510040140a01c02440c80000302500074015110050001500b4a03048090102d445060790400b002c3d5841408042000e81c1d00124082d82e1013411703900c501200507040654005007448040035941405058100015040052000d034880c030001d03661005420940001d150300d0b0a01d0b8000a072901c0010403c4d16008c0b03010f5002000700440c94644041101c2d0980c1c0c03c0c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 666240800 1250 666239550 666239573
    0x1e0304030b0411030f1510060e03061b0c0307210314010501080a0f021b0d0c0c150e2211070201091a04050d030c050709111605010e030f13090b1c020d 66
    0x2002010306e00001d00145000208011016015034140036041502807030000c0e9031a41e004000e00802c03006101403035484071800003581d404148802c102c0e52910300070701c0d02414409600c4215420348410400c503444162107070082c030200c20031805060005909010044401e0007005102444080d00c9401c120f0880c0b15620080103200008501242d104d40c40c007001d10b0401303900344031510410200181d04c402280c20404103078101ea444017004481a000c8080c103580d00800c40010903441407900201c0d90000c4001007440ca518480803030304000d0340a60365142492401101400390000e00311003001d0104403804d4034030006d840700c140c50060915030754200286040444041c1140010f442030342110030818200041d001410915000303020014030b0704078224203030148003544d00011120240b000d0611000b9440a040034040e001665516043c075621840c855000d507030841244807045c0800a64004688a031040703003a0020314599400d452100c1100070160014030903603200d0041501d84d80010b0300741041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 666242050 1250 666240800 666240823
    0xa080405120403060906061e14010905060c0c101b08030415060b0a02100218060a180605091302160308042906010e10020304171903021e0304030b0411030f 68
    0x3140004131841c1460666040e80e110643c81c149421003034040c94014806001507030003080350703030440c1032084004030be502e04982d01081d00b1400006480e07142801c08601c262200c0300541c0d20007811403600074102c81d0103880005501c212001400300b140011a0440115049401042d080d070a11010100d45021901e1a5002c5285d014000682c4440e59405001c5107442e2000800210304050382c005044003400c20b1808820300c903c00014802d0b00c441d004a5459400180d0030603042d402c0f90f290381d4058840d62044060700d1013000c01519082d0b070801c1341d0003250481d41100255030050491694151020000940202d5041c125070700e00c26500c500052180302511b103001540466802e080e400502013000080082e40030304401c100c029a05900082120102d60f00e161490200302d0000d60031a007061803c0150b0b1401040050900c0141940040d42d0401c04642c0ca660041c24400200101d45d40c0c403847c4001002084404c0c0001e000c074034549641800e068010302030b21080444040b001c1c0c00c0c01d240a10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 666243300 1250 666242050 666242063
    0x60f180a140703231504082106120715031817030106091e05100306080111070605010b19050f0904150305011524020a0203030d0f05060105030c0a080405120403 70
    0x8000b07000315641321a0b209490344142d10b041d96095100240c035400711011031000e440855012604020100d02101d0781c8540940b8542c188203000703213180c458504192070f003a1182a034101051100a0007041040032990010746200611403200f03001d601601002c01442d140c5030800c01e0b100d010551083e02c0c3c83e0344151030081c266480d814840040d005404640021481c0c407844428503a104402034885400c0d108125400c070014a4089000c138090015600a84910750a1414400b041040280500f08152180d1001e21190307886404841081c06a480204456100c950302014418081c80040000180c00c001c05403510f4000340c0401e003910051103d0645003003441404005101c000e01c0b404122800c4181c083c01801d10340280041000030300520100303055800e108000d10345008000c0445d1350350340a006d598503210341124003001420145489216903041100090715984a082120b1140401c102030600f0040d540314104d520074070060046526116403254180c10011000140008511405 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 666244550 1250 666243300 666243313
    0x19060206010509070c0515060406120804140102151b040e0108033402010e030c27130c03030804061104090e010e0102070206030f0a24050f03060f180a14 67
    0x105100702c64400801d13140400c6030051a48001400200d02c02c9514407a0380c1c428441034440b400024010805544070900d071049401c10f642c2000300d00f02c060002c8520a800002c2042003901c01640c0790b00c1040044408a488103002600c510081695035aa0300c0111544905094448000f10216602038214a003181c0c004151622480c040e40c41d21020407807200381c0407081c031801800340c505407440250b00a05008481545040c6514200181c12100320700400c03901e40620712410f00446410100008031f00b60499800213507242c807034540003040080c4e1008600c1c102c9451600d0464282001600c04c40d0080e484000180f10f00c4040030142000d880103203000174a15850010b06400c55007640701041d581e90040c00450090303039030842079a6010318440c40510050b96540083c00c000d240d11002200030f09907007200e0b421030714075002510080d100d050b100342400c083d0a000301562000100da0b403d4000a071040002c031059901d44003040314a9140046403d01881035460360303c0405140c58020056200300c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 666245800 1250 666244550 666244559
    0x120902060307090302030c040c091203050c03040b0426031218010e0f010e0f0706030b01021c0302031801021e0a23071b060c0201030c0e090a050103060f0b130504021906020601 77
    0x50240401e07c40f4229410400c00030468000b8200c120140300f1080030105030309008003498040c00440b4030103010042500d40c4c4075220422007105410034011041da080455046090060341c10710b00074500300c800c0c0c0045041401902c00c42d10041700081203200b01d421401101d00000900340146c2c41102c4560300030f04501d01d03401c4021821102944004011a0b000102c110800d032400b0030f00070150b035214600490411000780050b80380c40101d140a14186c48141c0602c03000f01e03416405140107031420451000d1410410314220301340d000707003411001c1c507007404807425902010600081c81c40080d64100540e01d450b040c0d4094085841c01283e8000c0364000142c0c074400c02603183c1e10f500064080824401d00c40d070901c00010400c0e00d115000a060664603d9411a054020b102c126500540202034003240d02d007440c03142014020030f01c8200c5181d41402005c4e41d039025136000d48c0f20000d80281201d81e60301641c000b40d001911015205a03080400900482c01d00404000d0b60005021260014401035142 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 666247050 1250 666245800 666245803
    0x150e070305010510170c130b0a02070305070b03010b12091e0a020a06030e0a120905060d0903030b010311071e050610030b1b0304060b0a08011e0b0406080d12090206030709030203 78
    0x40f180139904100c6040443c0400703400c03801ea5607400441c620003071600c54515140c0100051041c0e04000000000420b0f5548155800207100007a0b9100783c0554020f075503203a041181d180000e01402161000034040144443d105410035a07020b140349080700c40510b11400c03035021a6441108909070741d008260b41c1d030158201f00300d14400074011391804001c8a1919042d19480d10302e0090014a440d41640411308440c0c401c0107114090440101041d560ba040142c8c260028480280c00b00d001c04e04006210030698017030311138050080f401100c1075207030802541e503016a036480043d42040c00ca1b1403503040c00c042481044054410b0381030612105d0207606500340f0189064000307008200e1a8040600c0b129556081c1301600d4105c2d074006004079003022000d001070980c043c0c94000034495031a01401e424040031000c0c6101c0e030011065010441d2034024000d00c8240c99032400f0309001d66122240d42c0e0741c11803041c52420000008a03d0003e0704803c1c90340000c0c441d0740295000c000090b1a0b10040c815480e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 666248300 1250 666247050 666247069
    0x1808030a0e0d053f071506060e04021b10051e0403050702010c061808041e0b180d2a08030a0c0210230c060c0c070306150e0703050105 59
    0x42200c48800c02e02c02660b881c0d0f42c461000084818449640780440f005400040038060031586094801858001c004030001040d008044150342c0f07001440010400c0c1c00d118450f61f4141c4080740c1c0c0d494107004112044c0000b070342c072007000c40181520712080031110b020248212801c0c107070040c8020545050801020040c642250180308851252400b0300002a8022044649442c1c3c282042c601584039400c0200040100b0860031040307101344410041082940710041050b81d01240403d00c00d402036441604500c2028000d04c100d517003003004160ba9100c06100b8241d0030100007000484056002d0340c0301a0408421a1202d5081000040b124081010017081c04090b049647c01581000c100c044001c4c1401d01412000c2c0c040c448500c248141288079410820074140c2e4a1560b081e9401402d20220940d0320034001c0092034055200819041845a01141c20a0b002803004201c0107065413079a00082c40e000c41c079040b072032100e00d00008001040ca0031032807203800ca680b40018150300d800c050001555 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 666249550 1250 666248300 666248327
    0x3905070510081b040314010c090914040605041b030602131a160c081b03070e040c0b180409050619051029070b04030908060f01090207031808030a 64
    0x7840c40108540d1290b106264950200800414810140c0700781d40801c0c26210303540001d01884a460700d400e4100c1415082810f0308400e0781d442d000343c01e64401c0400110fa000c1100307100140c50742d01c045004100f46800942d00140220604131615081c00a15025881140e00403100142c001c42c1c0c0c046082020000000200105448000c40c0d200c15070240f2141d01c40d0708455169140c0303034048001072020118001c0003808004003212600400d240c40804800803001405210340700d111030104131021034a101a0150398002c3c01e09828a0600c40207030448d41146039010700e04403102041a546503594001e00f81500e000c0e40c0641010b082940b008914442c075601284815820302d41440345a800346121082143e024a0007400b020321640c80c1d001603a54002070f00101ca18010845800380700040c000d55002d14841d8958100695480700c0d45611800700700ca088904620000041004e8085a0010407509200e442c00f0040740002a0400000c000c0701c0d0005400c82d8000301781180c0720381e0041030341503e42c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 666250800 1250 666249550 666249559
    0x1d010602010c080621060c09190503030a0f0c02060703080a0b01020d02120901020c060706060609120c1401020309181504110d1e020309150f040c0639050705 69
    0x480082800f5004038009003210740524100c4101c40d034000300c1d104101081c0100c413004c0d00c5540c1032003c4a0101a00320224140c41041200d091105400c1c40541c03034412654050051070138000c00403010746110340d5080c036400620010500ca0001171307a90754000c00d8030768440e40307640c2c0c2c0b64106407510030200c07a5070241c000d0665021340b00c40c0502c0c0342c0016140e0341380c0e00c03040c200d281da9044c6600102c2c241440c080f10f0b41c0d0044000b0610008210454000405407007031039035078810301565012144144902c509010b48242d281c0901400010b480310451940c0e100e041c01281d140c1f52200f00825400c0b01203400400c0c000b5040d2091000e102c031031300a4003291000465050262943d112060b081620441440006030b5036240780b5000300000f409043e1184940c500c0085482c0d107000300c0c15a0701e80303200011140320300e03203008001448002d05402d00d90003103801508145030141008010742e03207500c201c054000c141d03802840d4036035101926800904400300e0101500e500200da480c2c41c900d00300140d00440c0c4107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 666252050 1250 666250800 666250811
    0x507170d0905041820130209030c011d061303020603130b01080309010801091d1002091003050f0f2203021c030504122f01020901080906090a110406050a1d01060201 72
    0x24554645481c0310a581c00c82c4220092a590000910303144d17000e00d02e46a000340d130181c0f0b95041c100559018091440c03099098134032101d013100046503114040c600e007182d0000e0106c40d5281509080b80075000b0a4405e12840303044070b85070307000030305c03980c000300ca15150810154480c1c00806c04192042c500410000c4000d4ac2850701010019060081c14080e060030213507549110191304214410102021804400352040d40c0c4984811034041c7d441207054900074130800da203041c60184a48203040c0300381100504040c60b61500c0c41c807480d040c0c1d005001c0c8080f0040030b0044090362524411007081c80d0303200707800070144008010b204900b00c002c50703580b017002d05103000100008240c0ca00c01c0c07080e0051283c940301e500c042201c02003200110403052000d51145508012002c03020341503004142010b426294480150b031801e021907a04c00c0200e89120755900480700c00b40c00034000a66030211203c00030400305609445401040050354158850500340c542c00300e4000003002451822409080944001d120 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 666253300 1250 666252050 666252071
    0x15020c070f120f0203012d0c090501120c0e061303021e0132030403030606020120041503180f120801050d021c0b0907080c03010b18040507170d090504 66
    0x18802c40900e4040d24468014200d801156003e42c056800032408080310b0290851258044603082c800002402c440c3d80351a88c2070100354003680810080300d8059482002d25a00d900720030000e8203a2100160600014040c540305030b94810000d440c0210f0681d940c962014654010480350300b2030808007112200c0324903061185070340e001500200003000d410000c480075201c0c080d00c010034200460b280b406c2c4030000c07007807100305903164221004070f83c0e030741d0300a00891800ea00c81010700e0718161049405c254081008210381c030b6030040d0b26855070400d0300380040d42030b040c080148041090541700300d0b40480c6003000c14041142150499107941c11900d8008501d605000100349201501e00700070348550b00c0e0428038468019000020580f1a5001041c2d420311b082000f002580c0f680703130740a5412980200c1c060b4120030f00b0148248041e082d0020a41c0300c0c403020310031003482c20400c00341050340d05000c0c0b200046064003030340d010800304083d01c000400303408104420043c050860354000512035400e00c000c210 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 666254550 1250 666253300 666253319
    0x11041523010c06051603050f070914061312120504080c01080a0f150311060c030f0a030b031906060b0a020604030e010201020d0e03030a23041104060315020c070f 71
    0x1940a032225150902115050005841072100064001c2c20365040400300001000350150042078032030a52028490354680403100310240030211903910000d8103019081040c208090410841084040d001c00e01e0503038107416941c030f940815001240000c0010300042e042150841d40d035a5116140e1900c40e040c0380c1850240f84d1540038000d00181000340203800b080030b6070a190700c40b058100c0d007000100a0105c151305142d2900351148001c1c0d580600c58107540c04c050814200301c3e10420b8002e0b025503e0b100e0900212515504501420001c256a8a07041040c648040080c0300601d5102030604560300c80610303203032013a218035070000b02d07a1502c2030107203010441c2c0000f2120f40155050401c0b03240c000c02000101e00900402c8540fa413840d0600341e5058451001100440c001c13804c00c5800e0000307010401c0040c000c200c0e00882080c0200b00400050b0200b804d03112030011303144c40200041116a60f9440e4410b40e10b0880c40018174295000413a403804d98801c01103200241402c02080c59000d16160059 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 666255800 1250 666254550 666254579
    0xe06030604170903032809080f030a031a090709140307031e062009030c030a0b04140a08040f050117010b090402090604050612041b0305120a03021303110415 69
    0x61042c08004650407071a80c1c0c060060f42c1260400f0207910703a40ea80107009111038100c1c00c0c034484012038a0f4901c0407c080740c0c0458000e10f0741c602003004509c0e10703541c40402c40c02444445425440303d044031a409445603903106603640540700c1360361450301c0e070760410740356010300c040c1d080390288258064a0200009000d840001c070111803a072100750034084076800d021020301484401c40311310400c0e5154264023078603408094480700400341e0480700001c1c3c3e1038041c0b59403100070840c0076200009900014000400e580c80548a94200c00242d070302c1d00a0686d10000c098100d600310140c1080c2501c4107004659100f014095040d4242c1001c4c4190b500d0800707003080c035204940c61365009a4000840820a0b1a01c00c2250010310001d040701e9036903100244c1d800764282042d942214045c4903044500074400c815003000007a03d40001c060a409140419143c91380d80c00102e400003490707000c4c4104c0b01b5038903c8016030380046004007900f200d03034141c0d50100030440d0703600d0740c501710002d1451600740708503518010340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 666257050 1250 666255800 666255833
    0x64406010306050c09030a0305040906050604030203060a0e030d05010305072d06080c04080304080106090e030309070b0901030f1409010f0618020705030909040807050616080402040504060e0d090e06030604 90
    0x12540c1307a40c040c03070310302e8814191466058402c440320300d02003540c80001001102c1482800b00b12058982c0c2c104100c0e4825807001a505034404008150982100c8d802021001c023010101c0746440601e0752a1f5059400907442911540c03c0000308001000f42c5440c03810300d4034444e900c18510307580710b0901d0400780030a9015203401c019410300014054040981124040c22512084980780c0790707100e6615000c0c0c021801030a1040e41030400d010741480001050301e018441ca1006400040e003003c2c41c1c0501b503000f80c9032142c101074440c122041c4004240c420382030f07000c3d90410000003d160030425035094900010f400b0440c54070f011400c12681c6040e08140c81c03152002d84025030f0b0f50380d00e81489865806502c106a50200407042803004010b02100207011042c411029176859a40b000178660350a2038094030400494560301c0001c00502e4a07030b00c60395100b403040b240010180f500c4103200b880c0449051400b00491592a41440b10100c4803071015800740044000b440701b071925540c0c0d1803a00d03945400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 666258300 1250 666257050 666257063
    0x50108012027130f0606050702090c13051003020703030c0e0d08070f050d081b030f190905030c0f10050c0906030411030102191206051c060644060103 66
    0x500604048800e840400721030040400e22109840f5102c2c0004001c00040c01c101d1525041c800500c3d180034038142d401c8107030000c2000b020369a0b9000d542c81e0951080713640c54030300e034000d40b8046840d503680700d4400780d6644d0b00e03607005032900120729002e400c68500d002c12201303208500d0a01c6909550f806500a00c030759110000c0d03911171140345042e89803440c61402c000c2103030049089010402d03501c407041c0d45c8203400205221016100d0120401d41d1031200365102d807500400d2400041e0032104280d0076018070195903400140241c90f54580c03d00350340215040b40a11b4100c00c04001e080c0c02d0070040388000100d010410030042c105070f02c00703ca41d882203840050080101000040c18841c251003144d6041c02e02a0003551f4801c4001b940d02c0000810f4081c1a020031500940d804030000c40d841180240d40024215027214107240c4104030715911208000c850301d0341c13240c801003521068140b59101c0705400400c40b10324000c02c04801b003243c20824035411008142c5c01c020605201000400c541100e81000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 666259550 1250 666258300 666258337
    0x6090602150123040209040603050a0213050f071b020a030501051b0c06040609050307060c0e1002010515060d1104030c260d1209140f0c1509040c0c0b0103060501080120 74
    0x404107011b0301907901180d038003602c3d00c04008203000c40494500c200b94070881c0c07001c450f2840001c0c0d80084035002d40d407905501c00745030b000034055406584884110030030701e506003414000d10760001d18a0b840c0c64208680c6c036512071090003203035542e05d100105d003007a020a4642c14007001681155483c1030003000038060075290588201488001c0c0111201d2640100082c04076400c8502c02030004080404200d0040050300c0f409102d480c0b0601c10b160003075100c0b0b482c002c180210b04040082c5608000703100f400e65a501c01c2010000f50251000708021445007510416161038850303085800009080c0c40c00c03d45140021205110001207281d1840f081c03142006041c1c1d110483c01980140884040103040030504410a402a800040e209007464002012503540400803400d0245d15038220310703040c0c0044402d02002c01ea5103001e4000c1c0d170200d4070a1038100c031614440d458850000b0300a9000f52001c903502c50040c01101c000307010350080502c03103805240e80340e108920841814440c0c0b90581d4900003031003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 666260800 1250 666259550 666259619
    0x603150f100507050d050901020a11280f060509060703031107020402180901080715053403020c030105040b0a0504060b0613051903020105120c0d06060906021501 71
    0x50200401400300a0104400c0c246038140150550384641000c0e1101e201d84091481403030711420803903c90b0030041e4040d0041440b5a030301c14101a0b140c180c1035921910700258a465001d94040c00140c1d170044000410390545070030f50104c8c038207010350480030801204120090303541d2142c030121000981e042c50f00013001c1340741c0c00c2640420b005003280298041d00014041103420504a07605071079603c01c0740c1240c4245d036120200350b5070359550f01c00d02100781c1c50a8248082d4502620180c9512880002c0c5081c00884212050b20307a03415840a10400e080c0c1c60001606040d810040f441010400350000c1059040644840c41003000c01494070301030350f4644000804001381500301000c600005001a51500695824403580c20710a014581c001c2c07041c1003030007800503a222022401c40390180c480a2800707980034a8807690385801080211101c2c000c100c54000a0414400c01008100729510209031900b05a0000d003000000701e00c0c2e0383cad0001094010b00ca50444e1010100010060603980101c0c035464 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 666262050 1250 666260800 666260809
    0x5070606051003050a0b0f0112020a091e0f0b280c0f0326061305040c0f030813080a21020a0807080901020105011d070c02060913150f05060315 63
    0x80d03800158100b0306861205410507015040540680704004c2c0510081d52103106002c0b4040d1558a0725000464900d040407a102540d8010321aa11503031420174119030300c485848191240c0d040a218908040820421005140e05c3c202c1010706429640c203032900d00d07155062030320196181c80b1140490031300440086440d000300c01905030035502c603940001ca887c40b8100501080407a01d100b03183c5515030599841d14280c1c4007100c078851840104010410919002c1c04001841300501c00c94070002800c00100d00d00304082040070040d4801c1c12107550301c2c1000d06041c110f085056000b901c0d40d0b440301c0c240c40001010342d0b11082d03181009000b46006010701c580100c2ca400c0e2081d1014000d12030006400e000d2110500c000c1184000c2a0020b000300e03603840c03070751903016113852100301d03480203951000c204042d210300c21030b4a0260000340310034200010040002c024041c503076035078540580d4900300300100f50000213a9000801103600811180303883c00c008242c40c2d100090040304070051001004180707070348 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 666263300 1250 666262050 666262061
    0xa0507050114120a1b020c03100209040b09010b130e070f030e010609020406020a0c0501020a170f19080405010e03030907060e0a1509030b0a090c0603021e21010e01030c06050706 78
    0x1401070f01400a41008074079100280407140e00300600c580407800c1c01080b180005801c00c00d901000c0c0081c89103c544547d01402504102400c45d0f0090721090480c0450391040e28082c040c5c030408003038950381e80d560b1702c0991305d4020a50107040e80d20500400c00000a801410003108a550f1341004901000c542440c0e03801401d40350020744615101040c0032503c9540020003000d0340380b1440b1409103244c0c80d9801a65100c0000d0402040b0000ea9400001081409000f41900c0d80c00500341e1070030310754007180c0d107128580d80100c4900040c1e02c00d410001440424010341e001448900b0145203941051140070751100e00500800040c050810b4454010740c66481c80e4000a01d880a0a0803405100e060300400028141c8002c3e41c0200d80341012401d45000c0740700f80039a1691244003c0c00b06450840182c010b9045880c50140034802d01020315010328922004000c03080c40010841c8001c80042c0c04140c14800603007000e00d9004440006000043d4003070422410f5888600b041615a402c3d0302c4c01101400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 666264550 1250 666263300 666263317
    0x603060509030d050c040b03010512070902031e07111b0a17060405060903031017031303060c0f0216030f080403050a051e011e0c030920010e030a0507050114 69
    0x10318040c108014034074080090f040c0c8034914034051186032210b07413140c80c0601803401103800310001000104401d10b815000012081054015121416650000e10b42240c0040724000704114032038100340d90700540b07000100ea010307406003022004100c2e60308400355280107880000401c40510281e48001d55590039022005120414908070441441340003d41c2b03130070040d83e04654600c10b1b032021882c45400401940c1c8500c0b80200042c1446140c1280780078400c20010160707441c5d020030096070451094080c140d4000c5c41c010000811401c2d6400340c0244940e490300350500864014140342942d68044900d00c404494001940690345000790602c0031080c4595031005102c1e108460800301000800b04255131011850304203507c00a0400329660b080c1c98000404080b03100d005482c51031078004641c0300c120303001d0452400050f009001d03510503a01492558280313403401d50520704000907607404060055440c60940142180d40900d41d00c0c19920301c2c2c0c9000c4c9034180301e0002c014814a09030710303080c3ca805e032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 666265800 1250 666264550 666264563
    0x70305060d140a0317010e040f14010e0a0b060d020d120527010f05030403021507091d04060b011404032a030b1009020a050a12060905040b1021080d0603 67
    0x40080a0800da03407890f9012003100411403032500f09181e922803c90190482d0f0503242c0b100d5840d521039071800042d2003291b2040b21001085046611030100134424002c1202902c4000e02c200020b030305184c032030310000070130302c511443c1420030b54401622000d812110f425445600c0381d020165580090741c95004002c04c0f009407000c2019140d80310843d01151185d100403e07202c001e05161100401c0391070380310480d006400350b0300c80030b040b5500044024000ea40b22059141c0111215140e0310b100d9410015040340030514019242880306100c0144150901e01109081c051a09004140302c85945e00480c407016210040b402e11840314401c400c110340070814210540c030b513099a100e2409552100044c2c2d80d02d04201402c41020603104014401c07240c412540d9100c031410003003686011101f00101d40040305007a42c4402c0c0015550080e4069140168407901410350640b03041b13207103400e101070b456000701041c0417044400d41a0021111f007a8000d142c10100c03d0780d446500b9040007003c0c02443d48000c03c02c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 666267050 1250 666265800 666265823
    0x21110a050907120b01030c270b0d14010f06020d11010f1508010e0a030e1207030c080705100c0b0105090402011e020717031908131506090e0114070305060d 68
    0x10035603c01c40e41c00114003950002c00c1156151801103084440380c035810004940030503a01c900c0c11840080c00142c0818451200d0545911503948003003c0e040600000c0c502d036100e012101241ca649507845000d4070803058550350305031074940000c4d5581280e16403501030019030b5407401e0404001b074205405003480400c051250a5010440c02c04000d003e100d4a49a5440c00c0c1c8400c0c2210004a9103041d60f5816235610484003110004200107074170b91401303449103032040d50301c0040000c070300800c200010040540505910745c5010706200380010350340d03a20403c20610030074090024a101c000d0506450080da0202c034195540c0c4010782b07007101c45100080441d1110165000e00f07a47c002000703001e40d00801160081d01603084909a42c90055842d0364000f01d050021780c602d958820a41141e02c11403440440445089a4627400ca400d000301072039008094541105001c1601d0500854000c811030f44000c10031300790041c0350745400c1f41014040e0341c1050b49800101301199034400c3d81e00d14154004411205 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 666268300 1250 666267050 666267061
    0x312010305150606070b0c031801090501091b0b040306020d09080c0607091403100906091b030314030c0a0c02041b020313150503010905070203040e04140721110a0509 73
    0x5642c180044542042200c0c00001103040c10714105840b00d655010845001c291128401603074142c1000702401e02040d20060b40b200d480a007400741e021214015400020036042c28208140500e05032074190755040e90010301046446680c400316801c9941084d00161180160002017015000c10071002e08407506c0819078012090000c0341c000e006103800d4403001c6007540c0e00d1603190618511410003507415080f0041006100306160064004c0520800001640d0b00150307076041c081c1d100881d0a01c2012517100800d200b0503402100c64030101410307e07407050461a18071415141031190701d0700345003000800082c100445d203641c0c000e00c2d0000c10407028414403030f41084000b550703030700f161b0034407007116280b4100001c03216058008c01c100e140c40c0741c1d03500e45181e0800a00d41c0107010301a10325000c41c07008010000e10803000b00440780c02240700302d1105016460940c90310f442e02c8840e41142c0344441d1340c1e505555131001f0303146210b80400c1e4001d03a03403080c01800000144290701e0170b0b8000c5da001140b0004205 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 666269550 1250 666268300 666268303
    0x81510080a23270c0a09020d020d02040e1501080f04060903170a0f060b0901140f090306070806031b0a180e06010603020c0d0309030507082209050703060608090d03020a020312010305 80
    0x2e80f5034145002d032101c0a8080c031a03035080300c68402c54100b1990384003806250843d8005040c2440b80501c090319100328802c990742281d0090b802420b40c040e114040c0842c0703243c43d1a64101761182460310b925182007810f0008090300c401b038001001603a40d0f15610b41018001d680e901071b40c220004014001d860001d007460b02401041404503d218a480070210f684261101581e0915006030f4465888404003c0d2a18032548505184400c01005104440c6259007c0108920800c01e036520044982011001c4c10310785006400034007008007080f1004046620340c07409041c2150f0000032042818000c0e200208014400c0c0c1c280d507115405000300102d90039030540c0081451810940841e59a40700c900d0044041783c0e103d244c000e001030030801c07154011440400103880d40d0845030041c0202c1c3c0c6210b4401d19032184040d84501000c2d620341c0d04004070031f038162041340010b10041c00e014006143c40141151100044640355080c1039022031582e110b1442002640c181d1409211140d40950b120700b40302e0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 666270800 1250 666269550 666269581
    0x501080f060d020d0302071d04050706140712030234030f12060e0631020715020c01050f01050d03090911041d0907210f021f081510080a23 61
    0x40c3c405c6ca0101040c440c00342841c0c0300b423901c10354000c0c2c040c25946080c00412a0180749010381070340d0056007805800d000c1104004541484017a03510300503610600c610103080e01c807541c00145000641d82c200482071030102080e50480342545494016244031105105a03010b61070f440384c2040350345c900800401d8505480c90781d64011401204c0c09010380e000300c3c02c950103842242040401d01d101c103030382e8603008600740d40103403d12500c01e09484111100c00c6c45268202c3c1c200440c8031019a440d10309205020000b0072a203409000240da03030b15412040b0752000f4090310b40500c550003145a0301c12049811010800503103010b0024000b90704640f8140801c1d01d401004150b403031200e0342c003a6000000e169101035850808220040010343d0b0180344549071441d0200480a003a600403180300361106020510703210000886a4548440c04281004c540d000f03100240064842d01581220180b0907900342c00c403001541c080445a0f010a030540c40f01181040b092005d0142c200340300200050004d42105000712 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 666272050 1250 666270800 666270809
    0x904022202091f09060c1e0803061003020a0c0b0a1103090a0b060a030f0f170307020106090b03060c0301052704080c0d09180e01110a18080105010501080f060d020d030207 75
    0x301c0742c0210740c0408600243c40081d02501081100004204090084840000141c01800780c00290070b0304032081e00c0c00c200c0800c02121043c00010402070700313160101c02d101c41d8407800d140840c01d0821400c0042c200646807400034052101101c0060308000c1281c100b480b80d4900744082540302e04201080c103030b40f10301c0c1d024215410b10326400000c41c0d03403c00040c400304803038114820580001003500c440c03a0802c4800740541c0d07148080118200b8500c0c3c0c50000f103026144650000401500d800070785070403992850340703a0384241c0101c810f0020100c0c0e00c109690640e5412165120300c249800c40310800c03000c1e85441a4120100ca10401083c400740030702418002528005a41401420303c00c2103030644000c1c0650814004640b20504194001c0e40c0140c036007040381800042c00d0b1240c042003468580101c0400d41c009079282c2c1143d04022044031500004090740030003800309506003800a03000c04801002e014214822100060b03269030742020160804d5009000c0000b801d0300c5041c000c0d1a10254082c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 666273300 1250 666272050 666272059
    0xa0e190b1b1201030303020304110a030309140103020c10110c010e07030b06090906042a12021008070e10050405100e090115020c0603180609060f0a0603050309090402220209 76
    0x60424010015012900d20070100d0b451148180e0940d0340a60007900064429107036090091030825031610741c47e500d040036501a88540c850503250020705001d41423100301c1c0030b04247c014082032a00c40782c005890f001c1d01c42d40160104e956011f80d0306080890158800703803c00780d820300c11401d2540401054000549000d03014845140d5a00030607c0510801999410840c1d4070440c00a40402d014501c80b103298010300240e121001c58264080c110001702c1c0c1c00100300c490318004444d08501d80500e90030980312007070816008038541810090103410b103101c5135a008464016031450100d2140c0c0440b0040c1000500e20f5640c00d100303010084c01c8031540169035014100f40700000c00d0b8042642081c80003680b00d40e0061081c40c100006000f210340014020245c1800b009032185144441400f4580c443c201c3c407802414207203019000c804100901801188106141003014008124003000303c8003403c40c00ea40105150700d82d440442c459440c1d401004d040100304660600302000c071703038005290042c01110f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 666274550 1250 666273300 666273331
    0x10306020408011505010c060b2d040b270604380306061e04020d0e030d0b0a05010e010f0e04020a0f093501060801020a0e030d170a0e190b 61
    0xda0050004070b0705d008150104024044110002d480d98120035a040c2c0040c1040c9500410504405224080c00102d07241d0040b812012401d80d003091310460005a0f000ca070f01d105034040001c3c030711140c54914041a1016000e1500040e420b45490b007041c01802c0014100d00140e0a42d01104255000d10b000304403840c01540400700920705d00011445d0140900404200b03261080144460046050410454102d6000d201c00f1070042c546119914800e82500061039803006109400d02c111070324020303843c0c40b40c0002c010030b009690b40884140c03042402801d1003458074610403030a440c0310390040c445a5006000103a02c8500c268001032850001d191a1900841640c40c0c800104c0d103074407016103103103081d0580f5000300d008250420420060304680d400000d882e68071601c84a0a81e805071070520045032400c001610795050030001605e20008070710b000f401840054000e9041b0307210242c0541c40c242e8031840f203003065000510100251110000c02008514420700d0060b071442012507903001012002d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 666275800 1250 666274550 666274571
    0x50a051b030417030a090327120f051914030a09090e0a021504060f0930080f0304020a24120621030207080a12030507090509040b0609060303130512030705030301030602040801 77
    0x10391000c4541504181d425070270211140003805d40745106888000000a0301804a40c0500c1281c441344c4016070341e45007034451420801d54015084c1c10000040d441007008600d485d60140141c01611000c5a0205007045030350045442c111101c400690701403e5450207074918400407006108a44150b1140300d0b20240540d015202c2007010300c2900c00118104626200803080190480c46502902c0c0d04110f14038800d03156a05035410690145444d5400003091105601d0103031101001040750140c224040883c44c9040b520600c198052031091211801c107042c0e0b0b402c0c89810100180c4201404980c20120b00750401985520f920b07002d40260180000c08943c510020440324803a0390840c40c002188484004220000d2500501e4030342008007000c00030903140c1d00d80401c0c80c06030b8080d44016025080070001c001c0c1c03e010151103980b180c1d00402c40c03a017403414120a032000b12071046540d02c1c40750452030401c0c0d00714895184018400c0c080000044200400d590140040c0c0700d04200800400000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 666277050 1250 666275800 666275837
    0x1b0203070f0b06180106050406020c0609030c13060909110a0801200d060e090102070302060a0c0c080313020603040c0801050601090f0e060a03051b0301050a051b030417030a0903 78
    0x180036014004201c0c4148074004690403410700342d0400d070068054541c014000024041582c0282c04c01800184002420024184d041000c10b001040c100c1e09581303002a07480000f039542d41c6258603180240c45507100d000304e940007070b0f01c95001480e03602c030309100303006a515002400810320314071288a03520002c8041404101440b42c600c00aa114562041003405940000c901c2d8000301c0c8080c0183da26110041504007010741494003c544540002d41c03204001d02d006814070000410182902d0b1038103036680a000e50050003204d860303401c00c510650303a4641000c1c01d03030028131568010b500b10328004280030410240e81082400c45941400030046511004011105494180b09004041c03504240601c040c0d094020020f402c044014104119a5600d030b580e1400d0614010b103842c4c41c1c1d5010000c0b240a401c00380504c680c4010a140100203914100c51344a80d40403c0100e01080d1040103c009800c000e0405200d003031104950340e01a40f00d16000c020100a00403004003240015a404106605040d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 666278300 1250 666277050 666277057
    0x60e150112060806130516060c0b070e150a021c08090708011b121e0501060201150305031204080d090c15020f2802040207060b0a0f03170a031b031b0203 67
    0x4640013820060b1101c0c0c142400402e403401054503180030740da1080080d540d2041c3c4810013404c1c19118101d5449060911300308a10008214005201c0341d600c81888175620b815104203820400b0b808192520340690007203103081c5000441041748126407001a40c46504078840d10300c1440c4880031078188036101c000160a0f80e039000401071680c00300f0100c4072545402912189401d00c1100400220021440702d000c4840c5100c000d4038100f01da03100300610401ba820700800345500c0c03942d04d0030031800c0d141d541d138207549204455000c81e040c24000040340400c941c900858401c035040c840d041c080d02016080c001c0d0110700c54450700c0a088200c0000305a45070021603454098007010001e4203041810b884181554088445000e000024410b88000181e80b5440600506c502511000416001c01c000703001d42401e0b075070400c0344400e002e0b1b0070400029030400c084002d481450307082c003910b801101c1c1041d005440c00103120502048240c400b000301e03d81c5a807044203000603541040c0c503042c042a43c02e070380324031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 666279550 1250 666278300 666278309
    0xa0f12020d060b03150604050a0e07051e030609070f05040b130c0201021e09091302030d0f020a080c03030a060b1303020d170a17010e0c0409050703060e15011206 71
    0x900020901015242082145600900501010480340300510010b410207242600a0b01000402014406242071502c208d50b88100007101c02c01c0003028410ba000ea42d10b929101c0d49225905031411069902e0941c140002c1914003d011990103080006d0015107409a03402840400002c18600044030714190148440708007010781401e203030030741e40ca00348000340090b41490401d640d0204031203603461320414101d020058400101d103131503840400030001c3c07581c80545000320304c4c12101440000340c0c2c4d01149040c40b500705418510040c4160a60981c14246d1401003d04820004281c612000202000031842010540f008100c000c0d140c951800c59405400407500080780d80503014001418031541d40840c15004220900d11481c200401984662014510740b0001d0005020401c0b05220450785a0150031a41411122458000b8107001030b40284d2084420160310307000400c00090203a0320900c080c10703c4505108140c64801b4202c0d98030500c1580b803074000380d484e10404841ca0464840c0105a5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 666280800 1250 666279550 666279569
    0x90c0612020316110f0d090314010c0f0c110a03080319050c0f07080d0501081608030702010509040b18010b1804060b0315180403021f0b01200102040816050a0f 70
    0x41c10120743c1180c0e010b0307001c82d26010b240710707a5650b185041010000800b13400103d544102c6401e0646c642141103d1214118041c05e0b810010000c0c06190016100031814101e0725001e8400d0a182c18032000400407184055045000901d0200602c10722030005c520a03c900310520840c003c65401060441d002210b64200c0c01d1414131007102c4041c1004000c0c0005401104101c0c14213141070745500c00c0707550030b03031204039a075204484500440b080c061340c900050041d41c0185040c01026000a0014072801d500648034a54840c41e020182e5210190800d101006001940c640c0da120004140141d001040a40c8105141c4401100034500380c09542c0030350b07001c0c4c1c59403415501c40c8a803040000349205c80d801e500c80e06621203c00050702c070034280c5100301e0082d4028103030403602e0390041c1510546111582c8081f8140003041c44142d800000c1800b01600b61598a08104c4c8180c51490090040c1e800c1807086000358540c4601c1042c0100001c4161602103c84104282d41c4420015008015202d1507149 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 666282050 1250 666280800 666280831
    0x5060904020d1b081c09080303280f020a020a02031605031c0201060b210604180b060f31061d1902040b0d0e070614070503090301090c06120203 63
    0x2881c3c0091018186a05010300c00515444004213400d224207020a543d02da18000130310821a0b0780221000300038580d20b0003451640c10000300f02c00b074860516906019030001d11000451000440c0d0141b40c040300d14180c11500c8003041c02d0001d46404058034103a1191180e01c0c01340d04030030343c290300701422030790000c009008603a0307010201c0c0003400209a265066559401001078090303683c0d4010582c5000715000001d0440b00240b0364035031305070041c06160107030386000280200b840b202000a15055000064480311740d48107070005111940c50510a500242442c1d80ba42600403013030050103084034010520308110683e03460100840d4540d10ac0c2c4c4003000e14007400c1d69405030810b4001178000700090303140300141c0403d4201c2c100740e074001c0e485a10755081c0000e0950145001d4803c1614130441140030f04101403a007a00205000e007e500c0001800800258076800c02101b041191800d2401600a015140e400c0c03c141c00280725030f02c94600455044c0e515600300051603c2200d00c56140700100451 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 666283300 1250 666282050 666282053
    0x1050f0703270518090a0b1806090c100e04090804080a03030e011a0904080f070c17160b0d0b040903052a0d0e270a0b0102010509030301031e0b0106050304030305060904020d 76
    0x44804003602410b024080e0b04030110104090041c42c42c403e034030034a14402c0d12108c1c1a0b00d14a403600003031988980307400c28040701445940d955039603240407074580303001080ca43c2c580d0000780c02003aa00d04020011240081d00203009040450f0340c0b01603a010307450400c01c00076012841400d81d400514a1042450108190444c0349091869540c1060103800c819040c030000740114079069101f850f007030721603400c180c0080084490b603075490008410124094045d07210b06030700c40110310255004d507000955010601c0710780400c056020031030760a80108248016000e0b400c0240290f03101030112030b1710103d0080c0722035040003441c04017401824040c0c001d00500c0c189000c00c89815203000c0c140b82e0720801c5a0f148800a1440804214003c04154080c8101e424080c0d062000c41c1e913041d03c04c3c2d05590511082080300e44010055a0449070402002c541e0011010200150002045002032070903c02c40004108198400061440742d8030a0303d0400c05500c03100708101c4100c0341114009d520000902c04d410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 666284550 1250 666283300 666283339
    0x6130807030c05010507020309121f020a0c08041706011d0c030606090409051b1e0d0819030b0f0f1012021303050f100b011b0201050f07032705 63
    0x814080d10344400c240c001a070303c00d82034070070903175584006034800f060508140c9031140e100c5c11600700040c02400440c21445003c4054160410480b9440d07a0100c0c001c45068014040c00c0d60075640301502c03e59845d02c42c0d048140c1d80ca903444e071802c6507100d8200041020684000c07241d40310403d81402600313655032501c0074203260380020702039a00014107124890081e00c0c0e50051842c00351052010749111008915581801401100314502c00c2d95070b020f07590a018413000c0c00b0326804d00103407002402c1c03d401d820030410611413540d14032800c0100c00d1210030007980c941d0040c85110b81c02c1300e203807443d44402420401c04502c922402540142c034507814084581c000c04961075203208080c40941403801c0e01d40081e0b0141c11582c1700769401d41000c58500c010b003c05005211140f2101c2c5410012118200e000900c9040003210030301c80c10300c00074038a2055a024006035041641d00940441c0c1d101c4982c9030080c404441082c0ba03085a00341c4240041020b041d400c01e00d010740750090b00b28548541d52a03000b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 666285800 1250 666284550 666284557
    0x109080327150703021515040908040806040503040e090a08090603060a05100f020609030a0c231b1c03050f1b06010b0304030908060103032f0a03031a03061308 70
    0x412108500544141542d01c035810700c40d603000840c290b4581c66040354240a8101188191000c0a00800c0c00c20080c504855010910038000c0523640043d5a16040c5440119031089400410161160804200420500000910944d50308074206030844e100c102825030303200c3d50150700030300b01e84007032244c20b0560034000301450b0300c404020a42254103035513002050b181301c103040c20540016940e14583d50225010405a60070101e100000d600d01180c4520003031404c890000e005009020141d540e05007001001c00c2020b04200540c19144400107803071040030460503407040540103a40c01c2100401003c85030342c1030342c1c00d1901515010b14103074403054a12400d62004007002c01c110715210003003500d40000c1046078082c00d20448140d60380d007044e007000341216441d03501c200301680c80b0324014000264022200d5600c0c042c3d00c8070710118907100031803204d280e26030881c92019501c61250400140341d03040c0c11140311303040d40c4125000e2902403c01419101c0c00300311041d42c852041c0310542da00242d5620001e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 666287050 1250 666285800 666285847
    0x16080708071d090c10030e01061d06010c2306010e010b07030e060a11010e16050d03020309041a031c030e010e06011502030c0a1b1502100f0b0d05071401090803 70
    0x4d551001c0e20000c00030b5090f007422007050303000075035075034034055642c000340f00381c01c09417401d00c0d243c40502000c4681f100d000031000b0701a80c10044d800204200b000340c1c980482a5114021006084499800684687c0c820007441044d02001041c2d00008240048500725072117a070701035403000c019400c9241030017125880650044100620110078108026003031007008034100c0c5807006001769001e80b1800e03401080c80c61708440c0c0309003410154480000d4000084a0080c9001e83d808600003220814496410841100d880e425024088422610b000510365038042c0c002152000c00241d01005401c2d800c27180310244030744980d44414010f11100c25440c14004541200c0e00c116841c0c105e1107030125040001200c000c985180d80000050440c40190385400081c0902ca00021103881c2648402503032228808000101169500e00800580d12242c020701240380f00034025862506c000e107800c0742e1390302843c4101d166100e03210300c0321010f541c8600d02400486000780d005500301040c002031540b10000e900d10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 666288300 1250 666287050 666287053
    0xe010e010e031b0f0105131202130e010504030210020a17060402070606060804050d02011107060203042d02040f05040b06012709020712140d020f0c16080708071d09 72
    0x36078a26a507420008202e03180c18050b2041070302c82458080c046094038080e24541030107820b00c011800ea41c0c2000c04501154040b000340f00c4044024008a0096800c807070906500a041542240640308150080e81c02540710380d01301c0b5440d80241c1d58202c120b004a00c0640c0c00200c840010f40c114001d842c40b5150032601c018001850f200b02555400704541980d030111011402c0071b810070003407103400d000c140c94a4101c1d000070320000c4550080c140162203a00d1006094641c080702040902c5000040400080c0f007142c2020843e016105420340350701d01003242240300e039085c003234001085011070061a0040d94840c801c040e107030b22820700564400b03810f00c400d0205564464980c030b000200920b00400145050400140d84414038140205c454840440c49814448068580f41c8590082030031100b503084407840041c0c0f14100a012082e080c03144200c6030302d01d880360480144244025441010031101c401d401c88d49040d44c2c1d00d03025501c43c0d99a2080896443c0b4a0310220800e840b4102003640c810f40050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 666289550 1250 666288300 666288317
    0x51008061f0228030f0804030e13020d140a0e01180f0305280f020c210c0405010b0d060f1206020a03060b071506050f1c02010513140109060e010e010e01 67
    0x7146050800090a1203810880340095003c10301d904205555001950342c0341c19034640ca03058401900f000000200c0c6801001249005040c40300198141c60b807030b00d42d601c1d081c03101a02c102050340944800b80d1381d15014500e0b18201904001d414404d107440c10340c0c40d080350b41000d032042d225103032200c421040940c1446810002c0c0000782e00041c04c0c1d408151081043e0350783c10404004010149280d03445008190340c08940060555619030315403418201c600300011030034540115204c1d0170543c00c02c007299045401d100010900d15402e80160012002c961030030400d16545046001440d82a480b800700585003031750005001c5141070f0004d004140d828100403e80c0c980da2104600941d0107050b05864001520800b4441c50041d8019a4000e040c212400c207005120040014014070210700491100140e950225007164000c6041c0e50072000c803c2401000d09a84001e01440503449078512400160000703404500c00780500701a5244034810384d680c0c10711801410054445c1e100641790141401040c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 666290800 1250 666289550 666289573
    0x60f020f060f0a1e0e100504051b1212070219050109030b1e07030b030615061606150314011401030f0602030403090b130801060e0903030c0307030609090804051008061f02 75
    0x404e400c0307050441001651180c0d15600605140021208958036400d1905000104400141c8100070001441034640c20001280005060301d0010544c0300340c60140d10781c20319048240034003070842d450013541c69400c1d44000005188816004d03000c2c10f27000c02c0d10800c092000c1a240f8030a1580440c48a40400007658001c00b020a2030f242106c6560020380c49a0304c2c1030460805000b12500701480c2c4920100681d10100000c0c82402890b040b0000d1020522000d4140100c0c0d41000c01c14046201c84074903003584900307100030f000c4500d0720003140c1c560800c00d0004114140489203412a500729030310a00302900c1c1c0c3e845070082c1d440500b003901044091500818154a020f0080400c050101d071904103080c40e008000b402e460055201070113164903001006401c80c004401ca030344c45005000b045513a40d8034800107400a110b03d030814003501e85018205030400c1080e40c002c005071142140c02207980c280c1d14004031072494044511a80010341c0310981020350002941c85840310311540181c60303024094 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 666292050 1250 666290800 666290831
    0x16140c070906121a070905010f02030d050c310909080c060a1d06010b030402010c170f0d060b030405100c09051801030b0603033f10060f020f060f0a 65
    0x1250032030030642e03000f01d000d0383c1001030000c3c04114039003071600d200f241c2c0d1505400280460850f4400e00e418407040b034100c910094424000c641202d1032510041040e820324580c5885960030180b2034403410701840c04026112400b60014040f030b13000c5103070000c2049051264040c050101540c045a040c042070110300481d1605005c0b00b4400c0c0c1301d40030b000030100e60034911031106555098035600b054001000510181c01590126944140c0a0030003c0c1120418580f11401d11500e0f161480517030408141e08015140e50f0f00145940010510148402602c2c0c0340005528841076800170560341c021500c84551202036040b0251112032810249840c0d582d501c08504541d1500d0440c08620080c3d40050007040304d50402c050300b103002034006500f0f0010b0040741501c09040401000020f201a40c2c00344014401112901d80000314440c600030703a4100f82100e07817000c14107406508041082c0100d204189480010810002107154000701520346401103075000b1090041e003c0f00320203488040c030b86100500c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 666293300 1250 666292050 666292061
    0x3050601173415021c03140a0b2209120f02030a030e0c04110705060a021c0b0f100f030605011103070611160f05100612081602190e16140c0709 63
    0xf090700684981c5d00281841c00101500e0303401d81e0245860400b40d140310258400d051b5501c100e51100009401322a9000500c1d554107444507854500c2c000840c0302401c1005401030750b9014802c8800412000c0200c0041d1100b0340c0f2640100010380c001c2c070414500522a40000c003d4110450a0f14050b010310310101e400d42c0c00c141e80c0000c0320300c1c001460030100002042606c1d84200212011030900c003e204d2155015040f80c040c20a4080d118240c0c0c50840e602d6502c0c0e54410349008000145c401c114101c05440c2800941185001c280b0b0034400103182e50007180d903a10113682e01d501940c540102075036424001d141c1c801421b00181000c0c40306800c0d40003840010f00d103ca01070464000c1824252808515107018021030307031046410064200407901c0d45110200e55141c0c05141c041e00c0c0c900c4055003907210660740c50b01a5001c1c00803031642c1c5640300b080d00300301c3c03d0703865140e8044055030f9a0082c1c20350001000c40100001040b800e500401003070020003502c06041c0c00c1d420359414a6803039085070203440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 666294550 1250 666293300 666293339
    0x160f15060f0302090a0c270f03030e0f0301050411040e07120602031609060e04021c060308190509060711030a08030a0f05150306060609041104030506011734 69
    0x75107035418410340c540b40006940c01030807942e00f0701c481c518015008000300015a41c5170000d10400082174500c44000c2e2261018080100c2c4400800da03076410002d210038110403800340900c032407090245240c00c06016540c81a6084030790f28039254031480030700008100701c51006040303008040000c611209148908189503008043c09a103038180a1260b80c9150301e03a007000402e0100d001410029036030081e003544003402c030880d00181c039603d0642d0381d1048811084076200c0210301d841808010071281c0405403080c07500b402c245035014440503405680317a124000c507107a80301e80188014400203201d94020b50714604c010302036a540040d01d84d29550650019181043e00c95100c10741c940341c1100a00c11a980080a82700b800c00d9042c40c800840e271500800f0b04114018079000404401d1515280c02100700c0d1002c0c6d051080e0781d0b42c2e1340d06245483d201c00f030049034054050141c0e5284031000000d20448954142c80e244090042a004d21050082c01012a00031130421395030005400da500b481c0020713161 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 666295800 1250 666294550 666294569
    0x60304060c0905011107050910050402071212020a09120303020f0a031b05030f0f0a02091e03070e01030c120627050705120d0e030c0405070512060303160f1506 70
    0x50070600e0028014412940280d03041041031200383c400d0200015661046480591315002d903501c0b440541034500104d070308a190040d00000d54035081040d07405140070039030b07116030300e10714401c108414100a901c6050f1085000805c680030a10036041d01c9076140700306e14031a050044c901162006503a21f29000b210519012903a10400c024081e0355400280061000c0c030f190032840c40c034001a0010b041c41c40604a103020700380d910300250b0b5007411541161101e503402440d00400036901414469004904500113000740100c00d0300140000604040701d06983c3d0010009845d10306200c00120200031883d000e0b15a203481d005005803018961b01a0180c0c0b100d9a8110100001c4504100e0314209041d030241c0c3c066440801005442d44010517003189031201450041403003100900040d01d0452000c920981c0145050140241240c12100030030b89000300b070020056a50301d8004060b1070307000307020b00d8010000e600002c480011308440303400441107105581d280c00f82800d02a07204100c81e10358211031000e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 666297050 1250 666295800 666295811
    0x30b060d230607092d0305060c130b0702130905070f0f081005090a03110309041107031b05030307031a0613081b06030a09032007050310020702030d080402012d030b06091005030a0b06030406 83
    0x4ac030784c1c01c6002c68094140c00e0002da14007041540400da010845c0d5a02020142d034684074041084030a00400c001050501c045a00040e12105020000c04c0e03184140044e51080e0002d00e0420314a5009040c82600180d0142045505a4605a07101800c0c4a03040040340400c1001d010107660301d1280764401071070310300702a485458514010b0400b080f145005040c0304400140b8100280f4000116a8811130900d0046805403011003141000710461009650009012825a40c0002905001001c80d5401d50032510000408000904501002070f80503410600400004550715610740052107a54403900e040f150301c1c0031a11070740702c40c14411001140c1075048104e0402c41480c0030091000201d81c02c100851501c1c5151740001d540c0d403080c200301400d01c03050000060642e03024403001c4881c586040f41415807111500500c043c040c200d8050318001c207151800e01e000307a051050523a205100e010b4007441e04400d044600341d80fa80c0008103030001035900c80305030742c004c1d4481c24040c0d80624810040400d9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 666298300 1250 666297050 666297067
    0x604050a03110f0d1713150b0a171c1407061e090c0305160b0412051f050f010e16030e1c02030405120109020307030b060d230607092d0305060c 63
    0xb08514081e002c14888103400b203601001c1103688400000d041254580010040204004220303002d00607403054145201e03072b14800012072000320307801c65140a2080d0800c03180004060643e401030b50181150440d40c01444240d0000c3c4c0c455004218480c0205025140c3d10b02080c900001e880344450301711081c2001d90300400c00c2090401c03156591848160320310103094107000c8001c14030300407403040e2024003000e50045400d020045c01000144490002001c240038400c144440c00f500054903010300d4000e03460300015455803000e21060048200118541240552010840141c040007c030341d8a64011400c0c1a00440d1203c2034041c42c0031065000340d51624035210400c03502902135092030941d0b9050040c200300503600071a035501071301e1748480a008185c640d50040b40f2404400100100744c1d4019101030381c0d60400d000c0d0310700344000b10002201c85964544001f10b80d2840700c0d00c12010058800815101d110682030b81310005004c9002c036151901d0baa0b174a605290000603500c00405810024091302c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 666299550 1250 666298300 666298337
    0x10605070b0601020303011818080c0610060f320d1401171f06080106060504030b06010c051b042004050a12120c0f0501060b1306020604050a03110f0d 66
    0x141d2002d000d00283d82950b240100d260b075401042030b0703070030346407942c82140c4030742c025202c080303a00015084001c1030780700d0720b40c208896520541600c03030b0b290440c00c9000c00507a40344151f0900160a51659a0745c0841c070100e200580c20420f6030b10b002c2514241d0440d90014554103402a1610030300c040004140e28045007130204002c54181c04c540e0700d0850002500045050000f007840700e1803c1d60201c0300244001c000c2c13500040c0b1241e00107101079400c00000040056011000d841540c3c014507150f84280c94000055401e00041c000003402c03500041181c0d030040c1c0308009080c80414000c2c1001c034112440b024505003d02d01925151003118003c58203001601302462040050140d28200e003a1242e459140c1c0c0380c201240c1100031040004c200040001c11250b2141550441d6018000344403450312903403803007500e401006c04007100c90381d10301d4001081c5100140c158002c6801c00080c118641e0243c0307048407030180c13000705518a4030503403017550741042e41005450760501c0345a0b0b5004a402c104480807 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 666300800 1250 666299550 666299573
    0x160506040b16051f0e070e0c090619020105061c15020f07050a0b0403140705030d0b011b0501050103020f03070f0504020703020102070203070e071202040b09040f1e0207021c2d0b01060507 82
    0x10036a41c000f6505212038000d0000d8240c00c1307112307041c0c016100d0844400055840c81407451440d404408072502180d15901508014006e1034100c81c000c02c04803000094a0004424002c0074005003191601e043c21101b0581c0142400050440c401e458000c842c0c507564500204120200c84450344c0b40d042005140c5e010410300b41010301000e0880c0f0f8500c2e03076100c160b036030701940c41030418141d61201c00e01c0550380500405d400381d0350f010040000010090038818001d00d024401030303000e5104401c0c89800d40c50042444020346112030841148241040103210003500243c400700c007950360800c09000540e5041005a00030403800807040c026117003c0724000c00d24118054840c00c0300f0700601c8203011003400308060362048001540c000990003116003031480606040450406406185086000f541880750010320f0014000d07620006100c8031240f884445070300d40100502004031a002d50085e206440300e8035614041c01e0000751b1100401500e412940f860b0a0380243c1c0804d90000d403130020000d540001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 666302050 1250 666300800 666300821
    0x17040e1503030309030a080601230c0d05090a140a0b0304080424080402010810090614030c0901030305120c07060f05240f060f19090602160506040b16051f 68
    0x9941541400d0051503038900602c1c1c000e2003441401000980140d1040806c020a0100740c5c05007920403503200c00808840e0301400b1480254022421a4cd110718000d100301e48a10384064101c640840c500780d0399414082c1d03009034940d405036800c08002000075889010f140a107009211465845107020016017810442441d440403071007a8803866040315400100c00366001d0780a0900288651b504800150003141030b42215031258a1b145000c1010030150502c0703500c0705000e0b412151b6200d01c0200b009881c007800d01c4010000780d000c020b01e0001d000c4000c1059080422442030b20309000ca03a60b1808260340744031850301d50090b0754004100400c42e1b41208040b6852007800d40102c0480b552011900850070b40c5c451074041c002c0007442040001031201121190540000703181c0500507403032801042c10300d41d0b100392030040c03260303074203454012482c0c41c2c80b401211001004103140c0f078a0015220110780020408001b0302c61407006100100c2d00c00c0c0040105440c601a991803181d50030b074070080c01c03220140c44 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 666303300 1250 666302050 666302053
    0xa030c0906090b120a15080c1525020a1503050f06090f1f03170405010201110307020705210d03060f0807260a140604030311090105070f17040e1503 65
    0x1c00c204481084084503000750b0b1010b00310005955621201d0301900c0000130302560000c6c1070780c0000d02c0d075a0200c2d8421800c00d0448202c3c101c250034034101c207980e0040303680c0c0d07011603a038001c1c0d001a005039003080d103c0c0f907901c0a01034841c4c6176070302c04944031004118804100800d44643c02c0103045a020784040f640060121404500c40c1400003003243e003800b004107003040d5400c03d030540c1005041c008411400440d80700419109507045920b0298150f0454070480e8007540c02c00d0b000054400b105800c1e03070b201301001c0e030042140e54a40810403118400042d50071005520030800f80ca9145418005407040c4c0b4043c0e00e0110b92503242010519194449902c241100d0300246804c0c0400300f400c0085c801480031030720f903d440e03500760750122a0030700200040040c00b8415000d001c00503168007041d110b10440c000d0300d00300f20700c8401d5290411703035105440195002aa0802c1544005403c0c0300c6030702841402101d242d15540d2a102c0c07445882d912a03040002c101c0b1140301000f604070b0050011040c092029030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 666304550 1250 666303300 666303317
    0x602150c0f0a0810050a06051207020a0b130201050706060902030402030d0914130b03011b0e01021506010f030609020f07020a0b180d050f10020a030b01090305031b10020a030c0906 79
    0x100720700c1c1c54080d41202c0e1003005000d0010480400307100000c9005018014010704003207503104405051540a4080d40c641041c806002401c0380b800841d8810880360060100c9541c3e03514000351003001480c80900703c0c1800400c4c8042004102103104080c00307007540601c0180c0d207040a004151074880c9103d0240104008110144140307071540e402110404000d56000c1141101b40440101038142c0b00180c54241d880c00c0560034021a40c0303030261100d0701140d12002c0d40280e0b15401240c07140410318413022103054542c04a0f4403540b00d0501700d599401c15250004000f0303281e512003000d0f82d11030003e002d100c040c049032840551030000310000061071203502c107030b29001144940813200500965503e105011034807166042c400d00340040050850014207480c0415400d1524000039000392000300c002030714094403000340b1b50040310355078141ea810000841c180b01d40c100c00482d201c0503000035444107028451034000803541c5070019105c4180c03a44c402180c09002e564000346034040d194861340c200701022 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 666305800 1250 666304550 666304567
    0x1020313050c0411090105070c18090209010e09030f030c190e010216050f0f1c03170a0b0102060604021303051207110d120503040809091801050a2c160602150c 70
    0x4c0d044401c41d40c000e0a00c241c507550141413041c98403e840d0b100c04860051601e0078a0b82502e5a031000d140c040c8200c58918850342c0740c0c0c1c2484255001103402800340d03402085080038482088000e181d00c655480e44d0030745000c2042a070190841400d1070860040b86150190310f02c1d5607018848008800c4030710310326440a519050000d08080c0d070b030080c1d090058554207030201582c1ca5003080c0700d0503042110200711150540345001880040c440380f002c28004000404039241d244140204800171805030b00600050701c030703081000000c1d44030031000440c004a0340000000510705000c004c602c242c084800548824240c10070080010100d410346201d00d4007494100000b0f074a0040c004c00c0340c0e109141241d1641e48915051120744582c2040c3c65001040070708000003071f590b81c0c1c042181e0740180e100900443d10b8004980707040d01c419060b040f401c10f07281c08450301c102008040094903071a411041b150b0b001651800c40161074015008100144c1101c1d00d0603140d24a0304542942007804098054909a00c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 666307050 1250 666305800 666305831
    0x12060118090b010509250f0207171f150909060b150703050705030f07061a0f0f040509030d0219080705030115050d1b0c030314041e08070501020313050c04 68
    0x50003600d1045c1c0050b4040b0303400e081400102894105007121007804210840800390160459a80e00b500500c5207500c0410310386280001c500e5660001801050942000864200030070791500c040780c0c0240c0c0d1070224410258800c20300d00000c008000c400101e102a034203150041e44c248408207401030070030400000c140000071040350640398062510710b4860030589407041c1140318254560040e000d01080101c24060380713900450070303500000755001651030380509201040d9041180d03503611044644801071281415007200c0d611217800c0c010760785000301d540e2000d8220b0b0484c224810780c41c1025800c08286e550020405900004282803a508542c504000ca480b03d103003070304401c0c00304000031031800464070680d0003d0b4404800200d0643c4e410100b003c00810908182c2130640c00241880c40044948003500c03810ba00440e008a8006035500810425042250020300200e41c006d03010001000420428400b4500405104055028003000360402d2403400842e002a18811450000420446c60300c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 666308300 1250 666307050 666307073
    0x14010e040f06060b121e070e13110903210d0209120a03020d09060507020f060705101a040e1c1103090d050304050109060c080306150403021206011809 66
    0x40008486603a8500e40003148188400740200000c0c1860800302d20642c8040240078942e007480c484446598443c2c0710b241e80b00c10041400c0403141c4910740440d410300d11030032507888036010190040300b180f5001128002111988c0e117034441084008100100c0e10b01c2c05001400002c244402d0540c41194038409119003441180c054246243d0f00141024140d1101540c2c540e10b41c85c3c03a8103850707035800542006501c421486c4d005000041803140e000c140980500251210242c0280180c40d94241d900c05010690b407096005661502c030780c51240300d0b45281c5004180c4241290001d5907150307089113042c401a5107164401c84d94903000214503000d80503964010300711002c91460840d242101c100366003400c61250a18003034100700c2901ea0001400400002403003140c00a030785c0c5010155460100b10bc080501403401058880c0810100780310345003820380e0f1280c1e10302080703155150030341c0e80e800211030f050078039400301c4a81c0260004209024440c4100c07490400241800d0111089550b523010703100c907 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 666309550 1250 666308300 666308309
    0x30c0506030a180b090f0d050702041517030415050304150b0a080d030e061e0a0b0a0506040806072c040e030d0509070f0602280311010f02040e0a1401 66
    0x4012001501c40720080e000150440d409105140c14000c490038040150302007155007030020b21501b00320196200c0300003132050fa200c245944075410603002d9807c01014080c042c44c4441482e000480214101040d83e10340f01c2001c02c0e0784c00650742d55140045040141040182c50800e200e41030041102280760050414142c02ca11400040c0c5806040c00160000c032854001c0032079072150384d01d40e40c1c0c1c05402d5401404070800880444a41d0b6441c44041240c81c0c038a103291048200d1114003142c00b080c2c003600300403142140103114100b2140c4036070200e1440e810661219255074045410b02a49030342141c0c1800c0c9030100c050000d600d1030303a011000c1003020b0718001020f00940d6030b0b02c1010280242402a108a231003401400c0c006810149d00480c0d4400960040d0140722041031400590329000060010f111200180a00404400e450380065801c01e01038081e000e004207151103151142080c4201070300000135180058032103082c060a401070000c011b0030070003102d15210a2000c0c003800340c587e650454 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 666310800 1250 666309550 666309559
    0x206070b192306190f0b07170415080a0b100839090d02090412020d0f02101d0f010515190b07240b040e01020a20071e140901030c05 58
    0x401404404080034403050717010343d000080041021818240050041c60414081d071550120101c51101d0075000e4811442040b54101040c91850503250040c3d4690390300c500540d038000355204224001c21080c4000c8882007001800d00020032900072420320700c221544c000c01c213040002c840d209800c1ca0035001800c64039544590046050318407070340c69642d003e6010743e000e4515a000c0c2090310b44011110001440c2d800540201e07046030a01c3c0e84550528210b0040c254024048101000c3c0c1040c000c0803080401604644c0e000c00524440004109005405400800014080c46d104110004a0300e550b00f00500c40c00f00151107480f1055040b042405890440d5000383c0ea40d00c030383c50304c1c040300446180b4200441c200740246144888465001499441c41510103103e54003401c0c20440c01c0b03104a014503404221008047c44074000349c001060701411144040700e900176220100001c541c2408981c0c84040c1806410070f1099a80700d02452520800544a40e8419415644c91400c1d1a21758004c00e03004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 666312050 1250 666310800 666310819
    0xf020d080903040906030f3c0303021b16140102070308090a0f090207030f08041a0a1d1e0f062e03050a02040b0319020405040206070b192306 62
    0x1d1210601c1180c004142a600801400d940d900e44a040c80802c03400655044000606d40040c0c5142c50400c400d603440f60a44100350101c098001d104000c01d01c1c14142d0401d070782480380d80d1402c640040e0080310f04241b4070040801685410490f00c40c1c24aa401c001000c40e01d2508201090360001f8644041e07a034031040490301d2782004004615440e1039076111100d06041c601000440510a034003c0201600030b135201c010780741650605035105034040d40c0041c140d1140007520604000e900c510560070948030742c2c0104030300346040882100c845200002c18507540101d002e851003030344100711000e4001a00c00141524440e14994242ca8103002048a034480310082e0141e2200790000340310801c800f41044045a090786c41c0d08100d0369801c03038040c0480c0030b6490440b4521682c98005007a00c5042c1d8104141100038245d94280406800040c10480c1c1110f000c0c0b04040008945a030703641e202d8448102c00980e40c403160300804064400114010403103203104100183c680100c5841d10b07511940030345401ca074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 666313300 1250 666312050 666312061
    0x4050607140123090c0603010609180b09010b090306010801091e030504030c0e01080c0d0503030a3803061302010c023001060510170a110f070f030f0f020d08 69
    0xd40340c9881c4005a00c0000781072040b0100c8428140ca00441300e80080750b10700500b1506000349172001303004240c003040954108020f102d0742403450300107500780441e0201c1e03001040300206448410a801c01c50303901c500420848028242040000e0051910000a1014071515200e4510490300141d4281594114845510900d130280c0e0803600210351040d00032707005940d60103441076205820b00a40c10140070744c4801c0d50b210b04c1c0c031401c5249991b0b0000061071458031024070110050800c0801038034540d03405d521461040101c1c0c000011018514180101070658010405041003c0203004181c5100c0c0c00c024580507036032242402c4545a81600d014001c08049042c1d802412100382c44103a010048207040414404190800c80c00c8a9040c0c0d009105041c80e00c13003d0320b40d40240c1c289a0186001b004c0020481c5040b5000603075204110002103103401e05650301424594800402510108029061501050380c00078051610034041c1c5010040030000000c02911031023070800010401403078002080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 666314550 1250 666313300 666313303
    0x606230304080f0c150a05040606080a0c090f09050708060403030b090f0123033705030d0504140604110109090c0507030305040c051804020307150206130305040b030c0304060606050405060714 84
    0x41c0b84c1580301000304040c0c5005406c1202030322046404640c901c0c100800000c0780080001c2019001c2c1d44060350758451420842c001000b041c800b00b406400b551180c03001008160148240006401c04c0400b500f401d1a1500340a0280c640310760155000c0d504560405c00c2055002406d0303415101001a81e6849104050400c41c50030803003410381e545409500c0150101c162240c4c0d81e59034800114506031031860300c003070021000000450025090f23400403c42c820807e1015880207602c0f500c10b0711002550160380302e103149001401c4408469026000031400301960308504188004c025001e014804540d441034020058050801c0003020f240e103c902080030441c10a2071600508809003078280218403e240c08003480806942c2a0f00074014203102064490010130040c0440b0b1094008080945038840808112a0000740079810482c2c20300c00458581c01c00c42c01903010707044140c0d98035202e00785410180b08840707580d40000b060100401080045445040a544409812003081c03050340c0c3c11002d885 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 666315800 1250 666314550 666314563
    0x8130f030819050d05010905040c09050606120405030f0a091806031e0213020307030605120703050706050313080d0219090807090213030b0108010c020d0c080904020f09040606230304080f0c 83
    0x1c0507658284070007c12a0700c01da42c0b16a100c0c5010315001c100c1c06a40f10b009904440c4182c40c0103030407900422044036454000200c494100e486541103c0c503002e07600d0501c10709a00420003000020f0303485c070410440c040001e01e0344201d00540300c80c03c000e00391950f45d0321480c480d902c2c08220314a03403501fa214401e65462801c4001c1d03959200c00255520f24048000030b00800307443c09418440c0580c0041180b5182d0000740c014103803903000e001050640e042c13540a440d44c0d040203180810820070036000100040040c0064401d54280150168460000e00c03080d50307045100320681c401300649e0640400c010f040c0020b904003290844000166907104518601e000c081c01c941000c0c221481240001130803800560007441c6002c015426038071200c007400001c40e82546001c00103026500140103590042c5810345c002c111500c0c900802e585402e2006020906549444e801900450007200700701d112000444082c1809500c03000f07405280d0b00d0075a07a44100c40c0117640c0381009126011841c026000b00c10440c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 666317050 1250 666315800 666315817
    0xf071d040f110405031213060e0310090501051b0c060118150b041a07030503070f030b0d1101031512060905240103050c0a03030806041a0d08130f03081905 68
    0x50000401e88112100c0c0740c1c3c803e2240501038804c03100d81c1d150411400081c1c50840c0440b91703250700c0c12481c200d422102c02011004896042c0190040241c041005104c0c0016061050001052603c0c1403c2001e0108070544044480603c2c10010030b480f003000440d0f00d9040d1810b02c4602184611040162001000381e8250400d004c403080201091060002000d030003110f03100da00040a007408103840c0707840d500900100034089442400491940c6000b5000d070300400a5600e40001c0076030980c0b001940c844600c0700b043c1c45412000b180f04a565070700d8080c0d944100440101c1c21480d40c41c03c1e60151003075604800280c203d940c1c130003030002000018418080ca03058203a0080d0701c0c5442103010010125401c1c4422a10342c85610308942c0e8a0505140c0001101d8040d210f031455940e0740c00a02c00a00184269083e010340b9901313542c0840d541d80c8032407494403030160417155110000351980020989440d004003051412940c820000104000100e0314880c9411303200b00001c849403a020344203030182a40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 666318300 1250 666317050 666317081
    0x27030c030406080906060301060303050a030c0c080d09031e02070611010e032803050f011e0308160b0609090c1023090f101d22140f071d04 61
    0x1400105a50f0045070700e4000c0b410a000d9981545408007058226a807900c0300078085401031040c0d0070070078003035807110102c501142450341f039030701c84c0f5610381c2c1d11540f001d0009184240d030749000200f4554041124010500d4004180c0b140d1250088040c2d42c80500784181020050148240045c10100b034102500088520382100d80390820080c01f031700824242d540506040c1c001c41001e250f0791788a4014103001d50103400d042d421036428003500c850032001c09882d01143c0b450700100040000c80000080460364075414040c581c0c1582c2d40f40c103c141910150000740b04a0103a014402c4001000c1804110f00340200c43e41032840d030403500140e444983c14108140480c0700854002000e041c3d0f40002c2040b42012540500840725485c10030803101c3e005c41c0e40100117031503860301d840c181081d00c12196507484003c00404e101c05404000c0e00a10070042c1c0ca14510f5502c640c04652101d8604041903045009180e1011103031905400040c0300c044a103001c990030040010302d00c005a00c840d800030010780030042 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 666319550 1250 666318300 666318307
    0x60203011415040b0301050907180f26190c080f060f01170d050c03040905360a0813121b06020106031e021908060108010606050327030c03 61
    0x11014820606041d01903800360b1400d995584000400d40115026295200d4015040d0307402d241c14024410300003050181840051034014581004100f0b0750401061412500303101103044c5850074041c4100c001624810501400300709000c0340c1d000ca0300400d108607146010020341810700305002c544405502080c40341c0142904034000040100c1c5062041c41c0c000080100340e42e803031150090200d410101c6401640003140d5024081e0b110710001c0c038480310124100ca08007034079141818201c460a840d01808151000a8905d002c02500c001d1444c09040c1d03c16a03000303140050906481d4410034400529400000940844000c203001c040c00c0030301740c14070110b500d60342d061400f03500d40b500000038056080c8080b0700000d01305105018140507280e00c1969291082660360954103918049841203910006600000300b882d19196500401000c4600090205515005c0194219a40b07a048201003040030010441b0500d049168007089000c48100d000d01c0000d41e00c0024194011003e21840720b00001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 666320800 1250 666319550 666319559
    0x16060b06121602010b09160f021014041a0402031b040f0f050711061306110c0f1f09080f0901090302030d02010c03060503070312080c090301060f1e0e01140d06020301 73
    0x180d000d40282100c58000304802c410140c1040103101b801c5480e0b0314400001d580800c00617125103460301c00c100e6540102d0311035140c0c4080403c00d03150a400c441560410460802c4144261000440e4600010040341c100e40e0400e0f4010a40391290349002c000c054222800a56035174407583d0002c0415a284841001000c0d40000c400c40502021780b080030005034584021080c9100200d45a0700070007c60301d000c005500d16a41c0c1d84041c0c5420403500d051680103020f00c149a0005008405107204ea407009412906075800740501401109005a0f0f81d543c0341290700c10008081008880c680301e42c031400c0544030744889004803030411741508025007501a17495510116501500f080c01c0521181d1001c0c4480c5880d807007459621107040c44094100065049035004403070080c9003441e0000a8041454070b08007074080860309560465110601000c5c404004000805c11080c220004012a0703410441041c50462450020003041c05180c01d1604901c064900310303a5950100662281c2c0043d044d0b45940c2d58 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 666322050 1250 666320800 666320821
    0xf07030509090a06240e0d050c0907080105010f090b0a0c14151b2809030c2405090d02040506011b1103060619060c08220501020d030216060b0612 64
    0xf80300f40c0c0001402410030600640c5a150200d003080d0586c2da880040e05020300803c508512040400e94803070003600603414040e1124007503288200300c0c2c1c0c1c44032000ca514100c0014a0f8040100c101820032604100521a460101007280c002a00600d030940512299080501c40005800500401072060349032003c0c031030364404bc03881c2c414140d00b080d9070703c0d05080c1c016030302d164407400d01f003d0100201c501c1800d0845849500d188102c40e01c500d8a05401901c9030350311150b0180541003c0c400c2500c00902a4010030440c290001c600294030f0107604041c5200d01007034103882d600000a22903929000003517880e0b44903800f4a0321087c03402072451610340c0b060400c500e440102d03c82d600c0c041d004080000f41242001d03403000d03480c40041c4070620482071031b0074030458100b840700f10200e908800800c440101c010002010303d189102d01300c108a841481e141c00a4684034141ca054018503006004003902c032005142c201c5c0c603494000f03034041a4013210b280041c5051060503449007800d01b03400c0a001c1120310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 666323300 1250 666322050 666322061
    0x40f320703031404050102070b18101d0111100c27080c01030501030b0a1104150305090c09130b09030c01060e0109110f1c1104141c080f07030509090a 66
    0x3c1d100d019001c43e035400494414807580c05400e000da03001c800c04001e2088180700822070003078226203004901204000060701d00310b591000e08002100904840c011031a000045030140c0c6090030480c00b2040d051400d0764903103a52410260358541d442e0401d01100e4000c800368107140c190401c660141f00750400c40c50814245600a04803075202d4509011b0495021b03204540c141e07500010002403e07581c0f071580c0e002400e00f540140c1e40007003040c00001611111039170000e078960360548010450385030440490b807130203040011a510456400f002d200552116607612100e040c0c00c040803090650317a1841d2986548103904627800c003586411000506e041c9a0b444081c142c2d40c0044041c440589030868800c0d10b400b0f01c0c021000060801c00007010390300b0040ca07218850303168121020605210000e1950155081070340300072642c01d0071003d5034806141100c00c0d804009003ca40041190f01300c2d444810181c040d8030380c1c0328080d94002130654207241c000c50650750380303070401421000303140b800c607000d01e0143c02d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 666324550 1250 666323300 666323303
    0x120201240f0e0c03130309030209010e0103050d0807140703090b2209060501050a2a0b100803032202031207080a0813020f06030c07150e15040f320703 66
    0x500100490418903003107007103014140d0031810600f140c5940300045c8041100035411400d00c00001030010040e154051543e000307006140a120a66140d41001d034200f00324054110208400305c010010301641000d00030404072000802542c40f4481490305aa10780316503000032103484004100d4500051607a010190321003010b01c4510249030b51648910700341c0700c00b4081c1c0e80c0030400034088494002e01c50b000340052603d0002c0c90f040c218040740fa000c0042500352a055a031103103080200014010140c400500500d1000c00030b518525102a954150390340c908924021000380c105c9500541d541004800c200c0c5880b0700c0c510750350305410b2a011500f0f42c400c3c684100803811210000c4c002c0760380440000045a0060b0180b2010424841004141d078001099102010b0b414072568020401400301103c0e5007510380c83c0040c0e008880da00080c0380400c80000d00118141c0c69082000107030404c0c4a00e015183d0001c646008882e00d041542003010304d881c4c940803440035200050891a400048940459 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 666325800 1250 666324550 666324569
    0x10f0e06060102160b04150306091503061808040b07080c030c030703031103010503061612060b030f0604020c0a061109060d0510052b020307090207150f0506090412020124 75
    0x310340f060111300082400d224003400c401c17003440304101084820750602600c507502c0c907000910f252184015011030b1000003190600024440c42072081152602c9102040050220301c43d00c11509607076803094a1046009501e002000440d00b0401c22801c0c0041c0d800602400082c2c0341c4888000740e003a81d40b5003259109500007420100b1150240c5122400c4905a400c003a002c1e043e40d0b0303109444251101d008078090b00c104000f18900102e00080c6108510180188000d82a540e01304020a401c04010203040c2038032651041004103141c82c2d00152152800758420303c0450300810b80c0d0381e1100a0300956a9040c1c1014001910f003000c212240e10031f0744504000314682120649800c00c0c003011000700002da01055156031840316001081c41d481c100280d1000381250b1100b91203404e038a041e6004000109c0d20b007070155072900d218050900660007440d00b810000c20540c901240081c603055000b60010f41500d0b007605034002824030039001282400c0304c000c01c0b0195170440c01c0c1d505a424000b4850b54101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 666327050 1250 666325800 666325813
    0x315040507050405010b180d05070b0a1805010507142104090509011104050f150a0e0a090b130b04020c010608100b180402011107030b0a152103050c010f0e06060102 72
    0x1443e0920541c1e0595012509482c202020340399a0718590803071815a070740c050810f64410002500c20070020010381401c501907900d41c00c1441d80034001d072018100306a01401454010700150b61b2000c01d48008ca03810403040c0c54848542c080450402c09a1105a440300291400040c5814000d030010800c56941d03410411450f0380ea0b030802e50890350480c80020306003000b00020805481c00d41640342c0f250034020b20000808100866117981c940c0013907491000720340b030300300c4050b04c0340fa043d00e03150b0007050300c00018083d4250700ca0006000c0d414107164214001e550311801c00598072a036040e10742c0050907a00030401c81d0703180c440741903a4603c10b81a4868040c185480301c18a41809200c204006941241403200c0b511940c1c015510314164170545519807150003000000f01d00a100014091580f00400155200403201d00100704981604010120200b003028001f000c0403002a407090340c1c0d01460116141d409070071540c0d0261825211003c12241072460b110a49140411a6401040300b6004c8903078 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 666328300 1250 666327050 666327059
    0xb10020307110906060c0105250221030c0408190c0504110d0509030712090e1008030901120f060f090b090403170601020c040509060f1f120c050315040507 68
    0xe491050010080100c807880c1a505018107040003800d0700844000c0800c1e04006480c500242101c8040f149010000074210107403500c66084601c82040d05090300c050f021052441c000302003903841914401410340f0380003000400242d142400d0318054070320101640c60b015041042000c05840361001602c0d44400c40d1000100d40c9800c0c411002c0c0d50030025119070410341c0441b806802454001d1a48489000030400c00002030b004001102d00810141c56981c1094280400380140d001e0080c0f1031581c845c0219028400340b100042655030740d40003441c1c2011641c024001c0348000d070140c0c0c0740300d200d0700c1d0609001142c3c0e0f61003206072400f500c1c08010104000c00e500c408010703640105480c040e0200d13100c605800984d81d88000c0440d8401c0c0c06004170f0302c1c2c251092000c10104e5108985200c4a03405c02c1c4148401103035076200c40741c0c00c055041100a01030300c411600c1a4810b89620945010070350030360143d0104100c0040d01c00007820b00405440d565850540d0040c0b000c1011101120680210364002c11b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 666329550 1250 666328300 666328303
    0x705030717071416060624020c0a0e1503010c21090201210603020a0e0f070201050403080c0a142d0408120705011d010c0215060f1009090507030b1002 66
    0x3849035082d0350381c400b01441e81d145502900e6000301d084441d0324800c641508082500d0b402040001c0202d0082c869145103000f141d1516010301d0001d01d030031074101c4014820f150b52002c0030081640d4800502d041251240c0c00c10075600b107400d04140e034265003000d00e0083c80c107030009207550244100d40850f43c03803c3d41d840c0804041b01e10004000b03010a0b14003007425590f14040d04a03d00c66504580000780035500c130307000611000d400c0c0d07014a8402a1300010030150824104040e42c008156000a11541c02c190707402420070100203143d121079140c049140401144a9082c01c3c00801849800345d036034003142108d4000e221442a4009103201c00401c0a4607005000b00c1110211060301000e402105080800c80020340d210312800d07100d540d26414a010314100021004803294424000000e11424582001e41801d03162091a6a1400c45504000c19602c84070510307003001d4404c44542c8420f4110704400c0d6600341c483c0d08584a030618203010001841e816a01c500122041100d50460783c00710048220f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 666330800 1250 666329550 666329597
    0x10e07030209150607060f020403020f180c0906091e1212040603050a0207021f12060b0d0b06070f080301260a030311160303050a1d061306110307050307 67
    0xb508608074400040e200900b41500c029440f2009040c24a02001e90b229442a2003152902d9840980d0003e0100304518001007806400901601d2200b40c00b400101080b0304180c00034648600450300003240c40307151340c1e0f4a007241c050031401014090f0300648003242c0340b0494000c0c40341a0050f103102041c5281c1490001e1040c03214840818814502814406c0840141c04090034401c01c5507028071540c401a0b6400a8041c2c40d81e04030081829625028040105801ca4408009400c1c6150000a2140408400840d081c1a01c5902c2c0440c0300314108000c540544625000072340301303801d402c0701e050420108400440c12500e1203424504140466a050102130011031710000490340406d12180002e4000c2e0004904445149041c40c02e000d042c943c070109940000b201200020b50380e00030810402042d2040503001640c4861840c02030611034090344e034610015020308124844000d00004100007504a5805200303011009602c030f0401c2c50014001e41c000340c61500202d11940000510405521100d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 666332050 1250 666330800 666330803
    0x61d01172b0203040909031101050a0b2409060a0207181506080a1103100504060b0906070b04050a0203030403200103090203030d0225080c071d15030a12080702010e0703 74
    0x2001e41614180560740c40d004810050303801540001d1000046401e02ca201d8030900a00030784038481c0c400941c7c035240742100c0d03000b0320110342d5a20b0a10000c2003500d4482202d40428102020703003030300c0e2175201d04461560241c420100d03402240020f80c0503400e039000c50480103c07080740410b950000b4851282c01c1c00d44241030301d204c4101c10000c0040041034072401a0366000a41c07030100150040b0100303a404403e030300490b000780c240d8011007008c0181d4100743c42203000400340c200c0d415003820828000a1024400c88001900c0290781c0004a82400000d00c0a040940e5005040300d03981d50341c80c9800c038001d0300041e480400b4070649420b03000055000b03002c2d5a2209500802071490903c18140c684000d402200034141c03001c82141c984403899200c1c100341ca11880c00b640d212600c802580303604614040c65504500d00071315400310748814901d41600f034243c010800f00f6032542c1c0c001c0900701081c44c0040000026201e0f29024045c0e00b60b413500202442c0c003507400c1e98003c0c4491030000a140f40d441c92248030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 666333300 1250 666332050 666332083
    0x30503070c06031e110706060806061c05060c0c1c0315170a0b070c0507030b0105190e1b09040507230f16020f0d06060e0f01060f0c0501061d0117 64
    0x1c8800100b9613a03480380c074074017030026042030801c805034440c90100c0724141c00c5100e0660000e414072200e031426540700d01b889810980314029510050790b07999124400030304004800b520200b81c0481810b0107110807903070030708e2140300100381242c40c0704010080e005d544220312000d05151800b10f42d0b42c00d10010b42507403516850080010340041d0b968020b042c20010461002c01c0b1082040a0010f60306001c6003000314040c60012003035505120402001c41a01c88000304c2c56400c4040400105410150b038560240445060745d010040203408148a03100e91284241d2051404007044441c030b810005480755080010300b002c58511204403040400d10404000140d144014040942c840080c0c0e4500300c0243d02c05441a13680943c8a0b000c1341e010f03003070044201c803007940784d94051041c1c0010520b442d601070080302d040d06855160810150020b0740f0402d0900130440b07440201401d010302504850000d2013580100d601c07003d200002c2080c1414280130300c3e40d0a803821003240303603800c000040c030031944114201b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 666334550 1250 666333300 666333341
    0xd26041e06210e0f0105010e0c070c03080906071a07021c020703061a090c0304061a0105040509151203090406090c14030a090b0f040b070903030f030e03070c030503070c0603 76
    0xc10002e501e200b604480c0c019500c2c0c01d8074000006051169201d07206200c80041036550621808030143d0400034940244424140702c45c03004a0401c01b010000c0b25003081c4035aa80f01c400d800400d079907214280010b000c0312045000c00b03142014283c00140f14040030340c00d807441100700502c104120302990076120010380c4120000e1001c501180d000070f06075085840d41d014051070b5070001c9441000704a44690400d1404410030040c03081ca80600e165076064084140d0480b690880040d040b40038a00690f8040e60542001a100d96050155000010030041201013428500d9100c103650798090a0302500607810403900052000c203500a00161403202c2e00d6000b26080080e803402c0590300010440010b03a51901145404210702440d61713805004429000265864241045118180042c064004102807a242000404ea1024178680c540000c0d240c0414031016a44415186004d000409043d1245c1e02c100001000000002000042d2051720310f43c000540d5400140c04580000c0410404c00300c110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 666335800 1250 666334550 666334577
    0x1120b13050f06150907080c030c0c0f01060b040e090319110a021f030e010203010e130807080f0d05010e06010818011401080106030b1f03080927010e130503090d26041e06 75
    0x18009012f00100810480f10560f00865805080d503e96030b0107002000c0001806111008407003a42039403189091005500c0c2c040072501c41425216060200e038108240d580c0c280200d54402c1c804900500c1c1c005007205100c85c08642204a800c1c021320081d00400d14240c41741000c4041802501d04841c031001c012009640c855241c407030004c00c8120700300d0b08400304009a6002441e15405031070055410301403039849001091145040b6001a040b10304407180e56810090b140ea80501c80682c4031440540c0e0700c000325900c14403a4003609400d0390342d4240740302c00f03c008204c890055025808480c0985510102500c1380c000112035215620864448010a044c091000c601d40400904e046480030b804000c1501d040c0c10f96010740501810305550b1003480c40300420054200120701c0703422040c040309000c82780103195203e6a891141005290258411115100a028602134070070000140701507040c00c8a074100d401035956038454000c0e9400105080310303082e101d2140141c1c140580c4c01c56207030f41c10f160110303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 666337050 1250 666335800 666335821
    0xf03090e100f140d050316051009050a060905030c0f010506090a050105010507081c060b09010e100c11060405041104150e0105030a02030a0b121501120b13050f06150907080c03 77
    0x1500d1164220001100311000100100002d11f062035a1a4600d540c1842c0f520300300e81070544400c00c00b0204ca05000580c0f000c00c501040c00c040c905c0c3d2140000650031054035002d4254090000104228050818201d00710307503040d0000703441070404480c500c0d815511b4002c1c14084850070300445002030002c0c4000e0001500600092002481032083c00c020606c1280c03040d0150380d11904460203200020441d03000e19608809040015001120402d808124200004010b0b480c1e00c2c01c040d0080742080200803194540301c0c2180c01a03c0d005d0024014044100007400c125030051261540940405008000c082d00c02e0952420108050b9a07061554850381e4606001e50005404608059900c0044031004d9440040d40c010703100c0300e1009090070030b0a220110403050016030000e0074460036115031500040b640540c2540c0124105412240303841281091498001003c008510520401c824020891140c5100d4014404100d80b80310442d03880030f504840080090300c01e141d20480c00c0c07000c1090141c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 666338300 1250 666337050 666337079
    0x6080c0915031912021507030906090602030a06240c0305030702011803030c0e0402030115030e151e071b170d060e0610090305061603090f03090e100f 66
    0x1400d001d0354000204000001c0c20250021601800c045051241100b0881c1000900c41d401d035a5001418400040d001c40320601800204000205030b0345103203102c10010070b54440c0d007601d0b0701300b14219224501101990000c3c11980100c0d000600303100e81504407006040b030b103038080140d1642c454203840c040d84d80c1607955030000340c85078007076549441c200000306c3d40050400c2e940d140681c0c4c011803510300610018100b9500d500403507004500402c0180422078220007000daa5425505d4005101c0540b9144d007410112400304141d0390303118582c14003035040c66001d0712a6407007008030f410500c4c5484580003603030085c009942c00c40c0700305400b640c0c0f03002007041c00342c4480c8070708000401ca51030a06040c45010407a21a500405c5d1036407182c001703000c82802c029141c040041c1c0582800140b641c150344400c0d036240002403010900780c4002210f078103894400d0f00040350b8103501c80b00104e8100c1d12850080c040f200240a40182c0612440020f4018070030306041074102c8115288200820f0f0801050080300350 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 666339550 1250 666338300 666338311
    0xe0a150806041415040605030106081903020f030a05120a0c211e0f060b0405031c020a060c0e01021005011809020411040303020d0206130b15152b06080c09 68
    0x594480e03c500007030000300100303403141d00c03886441107408212404004c1100c0850300314600a0780340c14000d10402d0000540105422a00072509042d8001e6103001c92401c02442c00c0c2204600000c9070708401541c011029044002c800241400300f03a450100131801c4480c0051140d0009541c10880c010f0740d0500e10004000c2c1c03c010750085100110509820112030050140c00071482d550b40c4540c40700c0038203101e401c01a02111011625240c50301d0b0009a40d00350002e28407028a00c0b04a034100c3c008d000b00320980f44183e2194084c402084121801341800352505009809400791000d481c6c00f80016100d40d9041c0e6100c0b4100b421000582509900100300041040341c1043e5201012030700381103580040d000842c030943c0200b0f40b025182e03200034100307035020b0b110070000f840214240d40000d00701803106620144021441d611003000e0000910300ca074400440040094000449521080340c450b01411881c0c0a0580042c0f240c42c0d2107a01c0041f41c0c2c181c420400715401030780403200c4a03d003075050150043c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 666340800 1250 666339550 666339559
    0x12030501061e0e0d080406110601080a0f140c090109060315050c0418020d0204080f120310121b0b0903070b250c091404021e012a0606080705010e0a150806 68
    0xb041c4e171703104940c1d03210b60002c030081402280400742c0c210702007003054090510035002c4c00300301159668003020780c40c0407a802804d8821500c00f910409400b00f00c0c01c968004000d104807810b503990390a500c010030241c00190781010741c40d17004105103490ba0041d640120302e2201000e10b401d2509045556a243d081940c0c50016000c1258112001a900262018108140190036251304030b8072481e11300387c41c804242207407a80034800c1010b103141c6a600d031812201808201c4644284504e0026010382d03511a0200d102149032002013610040304e000750513051025001c403405142c84e858580c140340205a03041e000c003204954415000080201c404103a1071050101c02402515908800c0603200c00d801030b158454041d00810007580b6082441000540c0d4805102c8070001071000000c0000d242804d0740d4041c180b030062403021184082c2805481072381c001c80d01f00050b41d03e07001d20035210001807040600003083e0450111540ca0048481400c6030345081c03015010343c1040ca020741e05060010300d0749a10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 666342050 1250 666340800 666340819
    0x206030a020d050c0a03050f01030309122406050406140a1503290103060b030112030c02120109050a02031c1b02030304171e0601061403091912030501061e0e 69
    0x85484901406000c2c0c1ca504011544504c906217004003168030003000241011001401000407982203008242541d050007d108040d2410b8113140c010980250340c603450741c400d0740008160300c20702d6622550650350101c030148011907440c15a40d100145050040782d00400400040000c075182d0500c80b64080040d040114a00b00e6030040d40782031b2102d04c20410104040c0c140c0c80c1d1080d42e4180704800282c10034079191401c55042013280720030300003510700040c2881190f180c032009540e64083c407020035860b4200203012000c180d1825945601400000324001d1140c5036002d41400740d84840c2064910f1240d540b1005496061100509944504000d030780600007008041420350461108070180e45031100105109000101200700d138a0200603403101540010005211705135002e002c81c800806800501c944030303100c041c0b020782481040811130340d220008041d05410860070a000c1940070041703440c1000ba07683e0765001510141d802c154000c00342e038900b440c03054a0600070010b030241c440c00030300200c05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 666343300 1250 666342050 666342067
    0x5130f0e030703020d080108120f07050c06041409060402090306061903120f0f2a030e1c03080f01031101200624150a0302091504060314090105040308040206030a02 72
    0x3180d00640043c0d0041e00901c00740e15040380c11a0300d1310300420a560090419180301c00844049004080d188030801c20002252024403101f007016480720040107080c184c3d40c607900c06800801d0400d03d845680641c0c00b5400003040b5251078401e071040990090064411a9500c0040003d00414808030a5142d0030341e041c003002040c1104080003c0829544929003143c611102c00b410039070003003c04104000400750101000c0116901d40d070117030885c500224030340a14030b1805032007541106681399040f8000c00034a030030a400780f80301110000d0191302c414078030742c5891902c0d07145843d007400094005100341410341a1940f082500413100140281d00e00c9402035038503a4103007424010388214680403220800e16100c1c1082c030792032003020101218100c6040f18002822074141c00394000000a140c5e02081c040700940340d2146054090440d400c40755500e544404002d001490300d00c07180113940c010180001d02c1444144a44da0049806448030340300c5a81e1035003000f6607036100519000700c4540038402d204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 666344550 1250 666343300 666343303
    0xf020310050c04140f10140c15041a0f0c030618040f05070501050c07050607020a0509010b0d060e0105370e040210020115090b04061214010b01050405130f0e 69
    0x5002d9800b030b080c1e407035440d440c104d280750000680f07000352442900040d02c0c540b00c030303511241080080341083c10104070303407105401d441c0c4007400350200450203406121504440c2426030401107101d10b20030180300c544600d4148035107440c03280449401c0d248944800c0441c100384441e4001d10f5000000405100c1c4d107032243c200c4201140e105480440b900c540449200301009014030104001e000c00f0710b80382e803d14140740f4842e5510070340d41c8201e40c06900b00051510540d11b6054140001d44000360214809503990100031440d54001808600360074506480400c8090b052500c1e64106c0350700a1000d282100c1411020f802c0c8515820301c0d10309120900603510302c109a42c803140c3c000301103480c0c1c14015803410380180095008001041c030216450440100c26194005081701c05540c80880b001600c01983c00104000781010b030098995001d41030405810060441001542d6280384002400203500100065403580642c0c0942a03001c0484036030090342054640c4000f08808400f0404161400a071441d00e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 666345800 1250 666344550 666344561
    0x30c0f060c060506031f09020f06090102151009090804080105010f03201810140303040609292a1501050d11101106090607080f190f0b03010b1504030f020310 69
    0x2006a987c03608108400d5192400043d81400400da030030f02c0c500850400002e40b1480181c49a200149124020a01020411603085c01034074001e0800c00c0002d100d03003000035840d0018031503a121982054004a400f641c2032113003c08982e84510300c000c0030522905d802607501c4040c00d025400800104c3c4087d910000030588600801030652076441590800114190310120562028000c0d4410001048040d0740071100c01d0442d110b0346880701c0d903032411031b500c2000021030300540e0440365004a500c2016203a20701c000b0914401c10082c102101c00b60103040fa840b803044190f21403441d0100b030010005820b0140300f0142d8144111109a89400d030f000c00141d0803201c0c4c0d00035400090b803070042884101020865287c22115000090400d8034183d2030003408080000d104404100c4a14003081d0340e2030041c009200c148100134420f201c2081e1412000c40104a41c00e2264841d6081014000a80c10401d5030180e03c6506050b4081c5010b00b1515124003401040d10126050f204442d900c903140b0f00644070740d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 666347050 1250 666345800 666345853
    0x70b0f1c0c03061d06040c0203280e0301140609060f060c0d14030408180105071e0b07180314150a0504110922031404060504030c0f060c06050603 64
    0x59078a08000001e00300c841c5a080072480058404034121a21a042c00c6941d0000301100c020480c9044620124114054081c00d02c0820119a2094039241e030320b117081401089440e914010401c038648201030907200050018003403900c20348003145140c200840080d91088003c0c140340444c0418a0106003540d01034070f080030450300000102901181d01c800b05072030100022000c5e038150b04054031640014880d903180a80300caa400b0381040c02a0740a5419600c80980081c007810040120380c0c00a069102015001ca41611405c0000b03400c26004e1a1034000ca580310545004001d425580c480d0b4220424524151291007280110744028824400c850707c1080b04800101d40c44c103140c42c200110491031034811703104102c030390b082150300000300b06202b40050b1011820f011901040c101920b1124407003607001c00c503810019020580740c1e00080140200c0340b0504010016554452101c0101e0f8100d000701c500054201c2c6840e004210b8a40040da04000d005081e81e09002c1090b0442d92003003400e692 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 666348300 1250 666347050 666347107
    0x14070f08070f180801140c07020109090506150409050a0c0302041d0a06030501111308120d021e0a02010b1914130209060703090914060f2e0c12020c03070b0f 69
    0x110700c1c4034007006e050642291a034088141032110703981c0040c14914041c000da9a926a84000007100c0c7c1c3d460180b0040c00b001c1c44030300c06545039200c0720f000d4050041111413110481c202132500c2003042c070030b101301c4c0d048581002e001d11015040030703c1c1d44860040649410301c215100c40001c0045038081c03007030080948580359044c1d542e1b201010304000140da560300010070f0341c00140020b003005681c00c048601d1403568010040e46d8140480900ca420500200c0303211040f200800c100b90000d4055020100000084880c800e1900c03800780003030001c02050055501c961013150000e43c0900f0411403414482d0306035100941044134900c003040d076030b401040b0280c00003a20600d040066004502c00c2a1188041c41c4d010099071522002048180302c040b04c580303004150450020300075074081120070403403490444e0030078102118400000c214100c5c1c0101940c00301010400c45101c0c1d0b00004400524000190207805610320709505c1c2c1005400a409501e40700004206c0d03411400201110080810741588 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 666349550 1250 666348300 666348311
    0x307060c150e0a230601090c020307050d0801090e01090503090f0325170303070e100201020c06010e0f0702030a0c0609031b0308040b0603031303020d111314070f08070f180801 77
    0x14550070001e000c3d0103400c043c1c03807204c0282120103004030b1001d0540d0a030200101e5403510f09442240b440c4a20580a0214000c4e50b50016aa5501104040c1240c405800c140440c4820201a900304c828004000700306074400c02542845091070341e0688044070004041e1410303540180d1003901084429411000318031545801445200355882c0c80444248540c00110300b1032038030540c050000f0401e80c0485201d21003000c05860040e10035012108284000c03c1030301c2c45941d4640c00031500c05000c5d50403851200034840000c5105200000f992807810311640e980012040ca5101c000c0103002d0300c60198100401070003402403a25150030483d942c98820b0b41c0e0031f2620315040c100a0b491081c0030340014403940003005060f07003a46044a0131001d0740d80440b8051013903e000d240070030200b0504154542c0010049070b18044c4a15241d0000403041c00e174905450700786c0d44050007142c03400c0c45141400c01103a60340000c910750760312038241007900e5842800c0192a208821251407501152607004a9142c0e44a1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 666350800 1250 666349550 666349553
    0xa030207051005040b15130c0201020c120f1c0609050f060f09090a03050c011401081c0e01210902040509030a03110f0a11030f0d021908060307060c150e0a 68
    0x2000510000310710103400304442c0c2081d80d50b1010959010301541c6e07a54810104801180e6616000015900960b03031080014000003040a8080d401006c0c004841c1e00138007400c0400381244008580d048811309071000d15000c2107062070000942100310380c0c042541c0c1d40401003981007242c421680075080c50300e51040c0c2481c041c010007140d007901c21101d50161880070188041420001040b5a005505041c42d940b9401029400c500404a070600b1014055400c000000c0b00000458490240d00306500030301c80b1201d94260607944001d400d40424009845900700c0c58030704004030300604a0345404007000c9030014080d0000b0b801d542c41a2a080740c103400029000b18615094440c0d071414019028141d8149416414550114042c0305802002e012a5aa105004550510440b07419a0503003280585a4142301094802500316000b0480303650300c80050000428002c6500742c3c82a01c0040040031501e0504008481d00352800c4011204500000740d2045101e109004041c0c2c4442560020320003040d46 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 666352050 1250 666350800 666350803
    0x114070516060f0f15060203180d0209070804200105030402010c0f0c060315050d05101d060a06060e030613141e1b01140706110c0a1401060609050604290a03020705 72
    0x172000d220014601c91004000e216000f2040e540c00f040350081d0181d007000b800e40440d40550351000c0003548103021000b00328146401c2040b20b40154000d02c1099400d140c01c0644071241c03c180c0c20640e000c41c4d024030008005610038450510800d11900300c19810600d030790b8850b4007001407600300340042510f40d02108224a12070800c407004000803509004020b440f62680c544495034010300840494407a41c401002c0002c0600e48400140c110301241c00b5454400c031070340024070903800340c803001600c1214060b900307140004201c0d00075561351881805010890b500d074424045d42d030914800c0c9001d000000000c21401c40e50740f41c08600400c0180100c00d040c250a41c44481c1c410906c1410f1000d9039500c0d00b0242c000b5015143c0d00d603480000000c10780c400c806e40004d04d008d500c183d800d252041c400f42c00100a00f0424a0081046480091006035280c401c16940205140201600004144401c02525850280600e01039408100310301a03030107091409404c46d0b001c18100c0300801d0f0000b07510400c1200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 666353300 1250 666352050 666352061
    0x5090f01111c0b04060503030406030212010501110d080a2409050c12041103030906070305181f030b04021b06091207020f010f031b03060e01080114070516060f0f 71
    0x801c1030080c03a00c21007268a01a03100e40100c40b4600c9540c0c1c3e00141965203460703010364080d04005085a4940350f44550080c00b075172003012110403c0400c00e00018555004410071840b13001e0381000342004a200320030898491100401c658121344d02c1e05d00c0f04420110300c15404540044a5400011443c2050300036401d450000d800c00c0c29152040150120340103980c2143c5400691100707520480f03000110000c2d103580078859a5070f80c0460000b82d03160405070401f00801f285661598030f81080c000344810402e812000a12441d41040b401d02820840b520960140640420052005007040c00c403940300c8105100c81003018190b0f40c801c0c1d05000d4481d1040040c0c848030480c0074562490010b00c0e602041030380d415a88194140039001115610f00d50080c1c02117844500000c0800410800038070b00140906414030032200c1a102010001c00d1101060003601c500c554804007448554584441c1196558400d103213507040d0742810314502c0300040550141c1000c4507142c04010540007020f1134084210340 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 666354550 1250 666353300 666353321
    0xc040e0708060c220b09120d020c0f0409150c110a0c0501050c0a060905160b0304050a030e0126072a03050a0c0512030103110604060e0f0604030605090f01 68
    0x280919010800100000b52442e80b268008580c0c80d111200c100d6582c04001c03441c640405840000480466418500e0003d0a8a00411030703040a81d10201c03040907403907800d60941000142c1101100003501d0402d01080b0100c074101a000003140001d0352604503100500a9202c0031858450480c0d00302e480d4012151020a49541c018217410141951508085483d603c2640e0509c6030210b604441d90b007040c000c03002a29000801413181c51420b2605644460300010340550305140742c1070101d4640c9160b0b0503284141c0e4480024650030b4019101514400c8450542a04001203c0079031844041c803002800007c0c104510007400500340b03400b024200f91140343d4034589510319250f40300201500a040d04444036094240250344100c8088100d07060a0303400c901410b54814559a036049443c180000c40c102d03030080341034942c000f111b81c0400200703101d6849401d0002c1c04818001c1c00e28900746243c480f2445000f0003851620b960b81d40da81e0143c80003102c69002e19040303000103ca0783c990038021071100c1c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 666355800 1250 666354550 666354553
    0xa02030708220605040c05030a120816171503100c020d050a0c0b06030c0415230306010e0705071a06010207050301110a08040609080f03041a0105010c02040203040317090c040e 77
    0x1030200310804030590030085805800b83c0e450324013007828451070841c09400b40002030165041b41e411070904401074011451607400041c0304a00080f0f980c103c0c04901e0900e030005583c0e072080ca10345982c5844012102a107131205c10306403da11076809580800401c084a040c418003c00c0744020008080d04060083c000c107014000104080111940c0c45000500165405440340d407298a4aa021a140111300203849811600d000500c280041d8805441c0d4102c0340c1680088443d03040c2c07050600e80b0210108a800d4050380410b0062100890000313603254401210310300f00c1c0c1040655200d05100c0c081210301d90715802d103590107000440d68144041405481c00380c5c004c2c000029240d110610920400d21a10100304c48000450b04101581e04051000c980003007025071640051a110b090039441980c0494410202d4414071101078800c400443c100d8078161a4910300c08110340034003000c0c0d03000030012010042e2001d00c45084010505000307014044840c0204968004401444200d6800210b283c2e10b9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 666357050 1250 666355800 666355831
    0x6020105060f1003140712050105040603020d1e080f0c0c031609150b1206130b09040609021201140106020d021603020607080d0218100512010611150a02030708 70
    0x560310703103040c0180c66070b109850420305100081411402892082d9440f8071009881050003503c0703170300a84400c91640504d900300800c3c2d991340200402c84480780b000030b401050013016000070800029031205601181c880010300135140c0e0360340c103515034401110303952440000b04035000300d08000c001c1000004402d80041c400e48203485004143c60081d0f105c1c1c4442c00c2c0c3c03120440740b41d26002c1c0001100401040c4200e5480b180307041d4211312a554201d03032850160110310124440c000140c09803032800c0c0c03805442100652207584071200600120b1704143e8201242800c5d49609440034842da0f55071150741107000301c0e25410281c00030b060108000502c011948400a041c0243d0803c0b281c0a0803668111411651140180360140f02409040c0f000300503544041001101000b03010310307a1028141c200c80200801420700b8080d5901c0c0620640448408401d600500c8094040c034647d1040700d240e1400c236861400640e080e00c000c210100d0340b4062150b0080240240541c000c14400d07041003134100010381 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 666358300 1250 666357050 666357061
    0xe0a02070b0f04171c0219021510180605030307151d030f030a1805070503070e0c0a080a061a12010b0405011d0103270309150504033908060106020105 66
    0x11441d10541c043c05132900000300320751800200da600d0480c1011840b020b544070b030807069181c000320b03100c2603030200540104104001c034030070628202442010012244001182800c807a03115400b045100c03044d08070b9540001060320b41d0200042d0035014811003501585d10080382c115026a98480c4040804402c902000ea10b00032000c0301340c48000410400ba0750726980e40c07440c0381c000b40c003d00d803191007000542076400c1c05119002c10345105458081c0c4c1110007050782c0d06036101003810201c2d41030b401c008007400300c40d00c4c56101b800d040e41c2007074946901043d402d44074001000381150807420307001c075500002142e40e001c40700018464010080011050700702440e0800103488a920004640548010200b20f00040c5e1300980c040c0300c0d0181605a807031008030040e5501d1a058000100680204d0780b00100080c000d094503201e5810400950b4403141490321707658648500d40e0019110000e8000d04042c9a00052070940740c003507840f0010781c2e1070b11800b03262500c22424920113030440000c5906100c00c101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 666359550 1250 666358300 666358313
    0xe01080106021e0109020a03050a06060b030403080610210b040f0c020604020d0819050408010e06150d05030d0f0504030f1e1110060e0717040c0e040305040e0a02070b0f04 75
    0x103401c3c1d07030500040006180040c2200d0060203c498000d42c40030000f000030003071100011b80b01c0c0003a48a514200000750300c4e0601c00c02140005c5030300400103520100002c0303d50501c04082c03400386041e42040342c80583c16009801c0c440041c84000300280c1c6d40d0b03941030b803594585801070584c0400c3c101c0040000d4008150000c0d1583c40081c0013031301907040403d000080029020844000205020420901c26040c0c42c004184c1d034820b1081032525800c040c21620003003008a000c5025400d980d031018003201104080c0003108800c4601540d280c0820320514011940c0c41c020f000c96880040c40002c0d0f0b40c40c00307140150140c0304120b001d00030480c40060010030030010311200940f038500d9040c00d96060300c08c7c0080d28075002d80d100610440c0c0b0300b002c50020f440c0c01107070400c40c003845c69511401c0500c28500780300d00310f201040314080c2c0410351009040040c4020540c050360010f010703203000c0d03141c02d449415007015414240d0f41101451303030000f407102c24482c0003105940c11a805140800807824142c4815 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 666360800 1250 666359550 666359563
    0x40803150f1311070804080307030e040b0901090b0117040b01030c0b130605070c05062a030901020304090902060c0a0b010f06031103150a09060605031006020a0f060b0103140c03070e0108010602 85
    0x82ea500d83c0e560140520b01d04030300040d18140d070f82c045003842c1e0369511006505e0700c9030004241140400d5000b1400c0500d07181a00446110100240c40d0424680c81c284480001c1d00c4101021810711084642c00704880e00705514281c4a43e0103031144403407951541c03800901141030b51f0b00c1404012000e0240c05481219503114100b2100146406a280c844904140361a15440d90106611540001c1c004603007804511810718a440c280e012400c0704c0ba080351485442e8130540c03003514010b0708104400d0108220941c040003d00b80094901400e140c01092102d00c4c0c2041c1e48015101c2c005040c0c0100070a061250b40e00c1c01800880c641803001d9000d0308200085400003800e4803a0031040340401091a84529007003100a0032000803c0c4a1646d44601c003500c0d44e0300564460a001c0841080803c03601d000085521500c2d0307010709080c90400b000d40b600f100401c62000003504040c0c0b19403041c030107a10450043e6000c0e01d0307030500d09076403400e083c80c01414402c02802c0c041e051001e900010800280c010455 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 666362050 1250 666360800 666360829
    0x151b07111011070e0403090e090f0d0e0109030305031302040207031e0f081612021b15010303230f07120215070e0d03051b0d17190902060c0105040803150f 68
    0x15003005d894a160944641011390042c420070345400c07040080720304d00044c144100488a806032111410404021207500003803c1d00240402c0c0100300c2080000d00c203038011640407000d0b81c40f46d4010b1186a0000d800d82e406114158009144400c5c4d8a01481c01103244420340f14a074101183c00c508038010107046110004c22088410403042c13089100c0324000c00c0345c1140c400e140e0108558511a4188403512440855503542d0184103406400b06090601c0b140b003816290103489190940d02c82e600016403000c0e4490f0100c1010200b031001e03001040c03082010b40311b0380d0321591591248a69a5000a180c415005c1000b0b9244184009001c1c40c20f0308852041e044440655010310003c03d0340c242502d26105010100102c0c0c0e0540242500d8a074010a0149020b403d95840178400020000c0031013000034103903100e040f107034203441c0014800384007640900515071000d482c09041200c200701503401c4070030455081d5181e0708000100040401d281c3c03080304103d1002c55a0018002c4c1c0180442d5002104921 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 666363300 1250 666362050 666362069
    0xf0402030a0204050613060e0115020a15110c0a0c09051f060806060903070f0830090d020d0f11030109080711042706150305151b0711101107 62
    0x10600940b1b910076010810040c1010a00419942d500b440c043c40c0424440c80782040f00b41d40d040c400745880499a01d04464020382d001d401e11000049806c000c0c034082450200c0340c0300410441d0014103082c00343d0041d25001d1840f190300c0d58504203007e819076500414008001e44100c1c21036001d6201c1c2d14102c01580d0480c5000d5a599840102180040c81100640d07075251050040004191080309460801d551420095039481003100109400344008010048030108150720821691050003020740b003203c5000380b1412104a035900814841c0d00ea1410948603420885500c00600c0320500d10550018400e4008000d514100c3e00d81182c1d82c003907144024064651203050318038541e1690040380c85ca400b900241c40b05840107002002c0d0402900c40f08454550510043c400d00081203a42075003100c0e04034018002807010407080e01000c000042141c03501800e0310400c00540c041351005014500e10401c88807008003602c00030003c4548850380c0290030000e030500c504d1020f580204018049440200307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 666364550 1250 666363300 666363311
    0x6080a0615050d060b04110702030a1203020f1c060602060106120902040605091906050d110111010608060c070b010e070c083402090601020a0302120c0307020301060b040302090f0402030a0204 84
    0x407404080c004290702c0503620190008a49060101e41d5000494900e4100c0d42080101310a107a82e080c1d0340201c03500a9415004410550081204091103000c450800e181c010b1034a40340d40560803094020950b0482e0039084944162410b9982d44075110191046d030000380700d6585002e034010f001000c015840311003036807035601d4401151035582141c0003821004204403414681a40c610041d486d180e120894400d040160000c2e02d4241540210f030b016802c07181da216039400400041d9080c1c144100c840c000d030365945000044424040c0f02003400350140c05500340d6110039500307085110300010382201c80980b410009211000383c0140000340001ea102d80c0480e10359a092002c44001c1d500d0054400b1249003200060b03515240c1000d000e0074103807007145c8002150f1210001241d607035140d03420003009a40203c01c40c610748040140070b402000c074100700312464904140c1c08070f420340d03a403980305030002880801c041c81180b0305290010744c02400241c1a828624241d000640d0300c0d0020300011b40102e560700c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 666365800 1250 666364550 666364571
    0x142517070f09090504080307320304150e06010f1706160c0602031005120c030a1103010b03030c1b030303100509060103060b13030c060e010921051506011206080a06 72
    0x9200b039400800780f0003020040c0c1c1c80c0c00e0030008407035031080302c02d40c00080d1040e002c1c061a407413500741c841e28060001d0b080740480340e0300b4181107402d0740007030015105980e4030300d580c5a01d60158041c0c001192203402c0544034a51404071000c00360b0860390000401c0d8800c102026a10b050001200c40e88156001000d800089841c0425900407803030100181055000200f084070f800050010202100c2041d01e10000c048400548580c41e0088540f1003a45604002000c00c0071540d000181440d482d801000062040c0318800040e00c3c0d540302d00e6940c503054022a5030520280e0580a41204100c0254051840c5150401f40c810412a0b5801424414000440429002c1c2d21a5114201602c0e858444903620310001c00001600011407100300c800c0710401c074000c42e1007407003070700481d00030103042e12054443c0341801c0c02c03e02c4a910900082e241c1c4010304c054080400c2c02000b0b0400c884d0840a9001f010b42480d400040c04003c0c82ca1503c4595420010b040000d00d00c00107130200043c2e04404009119041d8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 666366906 1106 666365800 666365807
    0x50a0f050c1f0204150c02040501290706150b130510090b031902070807060b090c12090a0507170c040e06011206142517070f 55
    0x5212440180c1c2e961203503040b411840310000b40c2065115020174240401c003481400004000710102820342c00c003407290300e01401c203491078110f4003410760078041540341140c2a260000c0c00c0001c0c1403070505c00d19a10000082d80201c0390034042039a50040b5410079001000182400006c0e640c2c0060301b86001c2d07481c80f04400143e150110340c00e01d0000c0c6417550303400c014400341811841607541c45100c0481d02c01845c0d0203215400c41d0381c492400d2308020040300da514220b02d002c0c0c0708803401d10400f00b00300e0068950b20b40348034000010315074400c482075091070a003100c0200f291041140114040c1000200c003000721811a08030f0701c2d011040e00800c0299181c4514503c11500034000501854034440030f0411090701860b0003007000c000a0b0304c1d020503a001129503c0110b080c8100109045041c50400c0d056070009160020041344100c0d0001403400026049500b804521040241020300 = true := by decide +kernel

theorem cover : BRFrame.Cov 666187050 666366906 := by
  have h0 := BRFrame.cov_init 666187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 666187050 ≤ n) (h2 : n < 666366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
