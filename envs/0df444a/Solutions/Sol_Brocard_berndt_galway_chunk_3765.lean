-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3765
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:36:36.669269+00:00
-- url     : https://prove2.me/submissions/2381fdd8-2439-4976-8c38-4274ff16bb00

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 676978417 ≤ n < 677158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 676979667 1250 676978417 676978439
    0xa0c0c080f1c03053313060e090f060f0a0e060a2a0c02060d09021305010f14090f060f03033f0c0d06030c12050f010c021203060a1a130b04 61
    0x209403000782c56920030000c1c5e10f2003a040030200c84026500201000c820b02e130650300c10381c424400c4440c0d000c0341401d2600c40b040e2a0741c40e40d8070000c03942c816070701c0b00300031410440002c0032403034100c0103c81300050200c2c079070010365040460494000c40d030255100c0040641024101e90500404580385080e601844400009081700d0448180a40600804100001419000d03480814002d8004141e0008400120701c4c94001c0e1100340200c0984000d071213000510a259410f6000302c04600800048099955206594005d04014107050340f205603485076003459202030006002c08002503003001d2a01d030800713412087d015020400c0c0c4110000c5070208411440c40750701c8440e040000821032030360711848004003001414880c0c1000d000503030003620004e03112011900c0f51a4051003901914102125904039900b02c40306c400c02040541c01805101008540c2200150303801100103295141503038440c0410002d00f2071901485501d00400151503500e02400c0b010030004182e0403541514290a00a030740c00c0e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 676980917 1250 676979667 676979701
    0x45101407030302070c0509130c06020d09050d2d03090509010b0a1d100809010b0901030c090e010f05090f0f0109031707020a15150503060405030a0c0c080f1c0305 71
    0x10402d81e001c240c1d04108a03411503414000c050092007071041e81081d5901d1aa9a5009034080b1a00103251000003400d6001144060342045a9119200194605814071000c02c401940c00c507032510b401c440100643c64a018048200384038980f01c40346000c044e18002d0040603041d0422032140d42900d0042003a10074000c1110034008041c50040500012402081c160300039419059920031745403900c0c0c150041e1701002c65841220b88a0080c05a0b400380d074144500c0000a000151018001110911441c83c0a402082c0c11040b00c000008403000c0e4903646200704c80050728000803d070131061031000207000401540c1d40d4090f2460003001a070180d075802a04119070301040003105002c040000e02c01c14001e100854415802c03601541c02c9610b0060042c0051186422074581003242c181c004c5014100000c0044c07042d6440702c0154a01320486000b41d4502d040400125014180008041001c40051049500f29403159008119003210300081c110a074050b031407400c0070146810304011040000c40c0c0242 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 676982167 1250 676980917 676980923
    0x13060507053301080d12020a020d1d061204020f100215060d0501021809011208040b090d14030d051501020c0108040203030408150402120102030c45101407 68
    0x2800e1500300c540001c030303489808000800602c1140c0002032100d4012500620507103103a0740d4041210a00d0000208034001c100340c410060b440b140c0d00b82c2e0824020070f5003800c2c00fa08000d035030030600c0b10300000030815401110340444110002043c041103003466291401b1b038950407581241c5d007150300b0300005c1d07807100410400c065441400c004150a13844222005242641201c0290b640b162010b828128902c1e004086a000c0c2010400010350140304403100c0d400554030103d41803078680f50405480e001d81194242652003103c1d51b9090002400d04c02d030082c0501c85803005551034080050085045800c001c000545120765070503140f8660b0ba010680400d100c000b420200259152130020a155000d5500a50b606128011461030220520036007288110301c222100e1902c420807a051909070b0009483d0380c504506c040c403000c003000d0b0212708628605206003401c1014405041c445001f8074007003e205901d500222103480c88281080c0d840324100c3d034010b007000c0c1c00d1001ea440c0d000500f40f06410780a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 676983417 1250 676982167 676982203
    0x5011d100905040609110a2d0b13150302090d02010305090a1514010f0308120c070c03080315040b1309020102011b080601090801050601020601031202100507051306050705 75
    0x25415003030454040d40641003600040015141c2864240001e08000700140e0f05070300103100034265882c3c0141d001c0103580e0034003010400e00158401101044402a0304c0480400c0340c14404a1000242c40c0540044840e0518002c0d03ca440e20b400b1070001c02c5074a43d80c60070540104640c40003501c030b0500179450280d0a203030006044ea5845a031505200c40084000d00504c95400b25000003401b0380c120f0105092082c0d00c010300b99a0f00c92180a0b40450352100500104080c4900d91301c01c2e544807906903022406d000310918006099950548243e041e420454031034201105005403100b01c0d421b468014a0f0903281049000900c60014800780151152203201030744601d01c21003164030039000031101c903500f40e020300c8010205504c0079007204070894015000480b0380e000000e20709014002d20340100d2060f0040c00740e69086032a841a004908151141584550001564140000d2203024442c1007039503912521449103135600480c14080e80e07c0002040400e10a00c004160007080640750040c5140030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 676984667 1250 676983417 676983421
    0x213060c0807020a0f060906020606090a0e1c030c0806010c02240705060a02030f160c0f06060b0c0a0201030b0a08070b07060b120f01142e17100e0105011d 68
    0x1c005407611a8000094100c42d80640004410350419035610981750309440baa01801d8030354404a84e0b410044403095800781c4ac9501081c0440e03210303030111b00343c1d0000d0717002d80d6181d070140da404400c200d1000d051800000d50703441c81c24442c1c80d400458170340c01030700c24071300548010b213150009a0100c1002120107038481d11740d80480c1c05800c1c500115109168003a050b1412841c149501384002c2d0401c48160311041c09410000304500f00c01030060590320f455488080003400c0f40d45801c0030580582c0c0003101e12a5441d01c000c00c42c1031045000e010592003100040c15441400e00c001401d07075039900c0303415008030500402481031141c01306802040e80e980d004450b8554845040450140c00405034841e001215458500103940021400000380f5821200038018918114183c009000c030484204d07001844001000d040e100d410191003108000048040410540720108904900b011102d8402c2c1a480b003025011054290b0240e00080181200200119890019429030900503e4007620a00d485c2e080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 676985917 1250 676984667 676984673
    0x160503041506050d050f120f0304080a0e0603160207060801060e0d06060f0b0a0809151303030b120c040f02040e0601050a03110d020301140d030e1c0f081c0213060c 72
    0x2108500408008060b0700004ca2103007840d0b81c80f01c00764204900c81e03010300300c02804090005000c49800841e04454a031131039a96403180e1805810034002c0074100002e802e41d110b000c0d0381e60401740d80070b8107601d82c10034025903084c503010b8134102c1c4d580c4c071080502216100400c034030b07600300c0a0050f0400b800d50b01c103c2d000401389403060003000703150004410241011400f064042c02c0340c002c0e01a003989a2101040c940799003c51503985c00b8410f908880c02d1090900041c0320200e02890030f41700b58801d04000c181c951506000501c00a050345aa1240b80d10807004c5440c40e203000e01410b10000300b41942103162900f0040d20700502e660040c44281803080c0019080e0007207109500c1011450300c40c0c4070840c1c607846151480c0019600038030490036a1007104524040c6407a1030321040603c03551549404c84018100c0c0180007400e0440c4008002e0349500c4598000840e0310044ca000e0058400c040d0184d442c1040c94404580040c122a1404040e2060048642e01c5d05200c45070b8040c1c400504003922207206501d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 676987167 1250 676985917 676985921
    0x3070c0807020a060504060f050c280f05010f0c0504030203060103020f0a0f0608010603061401021e01091a0727091505060a1707030c050304060b061e09091605030415 73
    0x1c4003e4029240e514000f80b0b16600c0320180045d140241c0d520301d03c0e81c01142003115070340100703420100f041d0002d01e0503007103122012100700c110300100003c5030714104c1982c48100204614070400e54099460304440c880f6100944640c80044d1000d0921605003421900440d5079410140002030007001c000c0040019559001d100034000c007505400200407585581c001002c1c2c00f001e101c1c00c4c010a0a2800101c1d901140340c1d030101007440c0c10785c0180f10003081e402c401004c0a5546008400c81d56070703440510040380960802c2c001d020b0401c0b4203481642080040104080c003210030f43c1c0420310440b1115001c84141420400846d03911840100e0b05140e0144000ca020035142e1100d58405000102c840000d07400c15400b80790386c0100d4001180c0303543c5024081e42074551802c20140000d0f42000045c001843e1a802400d140301c1c0074103080c0c204078008800c8004a080240c400a450402180640c181e1070410f80c0c1a5201102c0c00407440c0b07000c1c1108020b0054007025000503c5529025400301740302e0056 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 676988417 1250 676987167 676987177
    0x1509050405030c030304030c0506010909210519091d010b1206190314010e0f0d2a0807060c02010b0d0209180303100e1003020f010c0f0204021b06060f0603070c08 71
    0x4800744c9a9a060500c0d000d0110241c402040381c060044c2c600010390718030b551180200a60304424283da810701c8021003107865034404440c41c020700406100b0100740240008002e00313600381035150050781e582040d4004001c0c0c0400082d112030303040b920380148070501d96001a1540580503481400c9203484401c0050200440303001c0c0205030740c0e10251300005005121120104241d0f00794002c00c000d8a102e00e48030384810750401441030035802180d00000c8180710b040c83c1c0c1c504103490501002c0234030280e07581c95901070045009807600b11001c10000d01744816441603040c04c07011800204080680100890320b13040980c28040d00c90030000c0c00044841719000d14a0300f01c20000ca098a81d81d25000c050b4206840f0680076038003140760000c00058041a04591300c0007501e40090400e800c584130071004540030300c00d80c6030444580703d03600c40038401605d481c0050701c07202110039048590f64481c00441440c1c40c4004020340d2240c149810901c13000d0710b4007422a600a401403a002510001e00d0070079071058030032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 676989667 1250 676988417 676988437
    0x3140403060903050d0c0f09120510050a2c07051c120f0e010306051c0311060103050a11091b0f0412120f0504080304090c210501030b0a150905040503 66
    0xc0404802c00c040c0e21000500070b00000100030092640300c0714048526410f980300c2400403d50503070b424807030f010b0348150f44042948900b0403038403282d1400301d4076016900c05980c0720f00c01ca40c985001c01000840b9440071030940c10391000c98402200d447c403115589041c14441c841c01400c1003004001c0d001000404001c2e008e401c402c00b6019406181c90003410315800031310300030001704100100051076200380074820807100001c01c8002c91b41444001c6984140d20441c0c2203062083e01c1d591030b10f03516014007513a402140100b002d01400c07500c03401c0054081c2c0c04800ca071485040c814081103100600003100c142000c085044160b100d00e10301c40400810310a40d0040c0d00042180700214007005125041e40d0102a40360b0345889444101705010f4400340a94007581f0704c80d82061005001041d6242c3c0942012462072800020740f40c04a00300d200c8200704040c0780900903403200014024401181d08403038210700280c101300144451070148034034048517400703040a00c50302c41001c60b080c4030b820415200a03e40e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 676990917 1250 676989667 676989671
    0x9021804030206040c05040207030801091d12090901091116151a030c09040f0f06150b18030712110607061d0c1801120312020a1211160314040306 64
    0x345414003075a1818126412110040c22039030126244c02e00f4003d5440140e0b1640311034400d03900f00503c0e040900340000c180b00c444040c2c0d4230049541241013200d02099056001c905030b8560381c03101807014003c016005551b01c64100340c041825221200219500018170300a007031100603552601e0003009102101030ba48060815a2140355290341820305072625070110201c804a580700c000b40984407808980191102440c20000d401003042030503201c0c41c1e644694070004641c40e074500a41c0d00980da981002052a5005c00c1011203187c0c2c000711006c081c081203008059aa280074510503810305103420041031404004080c0c0d101d07442d46000d6a1909030700c920b00340304c136203c01c40340051001180c2c8405d440c1482448041c80060410310203480b880b01808250041a82c20310842c1d0035600030b24001181007090005209003d0001440641148907055980d000c40f0f02d4444500300545001d203404201012080129070b6a41c43d483c0500301e50030750b050502203a202c03900c4180b07039030fa40242c2d84044c00ba54 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 676992167 1250 676990917 676990921
    0x1404140c0706060f18061a03071d060d1a0102011b120209040603051f020901050d052502060702010c21110c01060f151110021c1d0c100909090218 64
    0x50580805c88110f00440020403a1540e2a407460081c14504859880e16100410108600c181f048941ca50202400c1600d028417041d28408908035a208900d509145035864031041a83c105003443c0c51541c0c6000d2000b40a460203c289082c2c1130b40303241d1500700503c9a40303007951043c000f098040e1840701500034020000940e41e404c0c0700fa00c0d1514048204058a0545000c241c81c1d0500d200780d41c0e0002c4103958540c102038154980b01c0c01410080c20085401d640024000625007842c440c1d038440e54400d07405008a810480e40180c00d58116040800500404400e000415000b95071007280380b940320f08000c42c0140303a0070041c40e06da00c21442054039a508040b030100c0c030000080074400440380d00c0f50403099400b079515011541402c00c000110020b400c00450542070200c80c3c0c000d0034140b0f101c2c401e49803410b624141540201c65404581030102d200e1030490b1801355505200719410b012050b00ca24401204032400180035035124001d25090b80d9440000c0c00964403000e4094854802c881d40d410158 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 676993417 1250 676992167 676992179
    0x6010f11030304050c1e010e0f240306040c050a081605071514010602010902010806061305060705150c07050a0b04060f0914070e042118240201020408101805161404140c0706060f 78
    0x42e0f2f000301e03500350145e41407800119107180b00703400f2070f54108840e81c2c0d02010381d1603c29031540b8080c40034000b07008110b4240181030218100c04110a16201e29140025500d11040c0d454809000141d100d03a00756450042c8860150341c100d8072050340901c04980140da50a910b020701486c0440503044140c100700e020484200700500085c900944102c15040d4243e6079031080c1174003166109180c0018925000624000c000a00d911400394100b84200f01c00314012610013106000c482c0d9001c000ea4085070315000c1c0307003111101480010040d040f001c10030f001a143c00e4480141c1210030300c64842c8401200e2005030480c61107480c255038030411407006003045541d1081d905000d4640514441c0301c4d0b2000c00b00d141040c0c0c1c0140301700d40858200e4805840140c0030605900001d180c1d001c250521103803c3c85000c4000740040c031080c180c04c3e12003081c18604904254050844810b05000280202c2c50104803900903c0342c0c46503907500060842855a43d03e85038640300000d482030398000d0000c40311040b0013040ca = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 676994667 1250 676993417 676993489
    0x103050a0303240320030d090f0b090a051504262407030c020a05010e030309100204031e02040b04050f090f1506010f11030304050c1e010e0f 62
    0x11036010355014800c41c0441011000c80700d076501c0c0701d400180301c5403000b040090307800c02d02d0a00c030b2100c2800700040b44c14100301103400e00700c100003504005980c051003408040611041c010191040c01440b904044500d00881e52510007800788501c100d0103080a0841d211080c0111000b402864081c540c051641059058032101030300201c006c0e600a42101100300c1d000c1c10f02c41c0c0100700b031241d031030002c68540d00e0f030903001054419104011802014028000320320309008800124600100550352441c01c54440790504229282c440707a00da0042104001241c0000300b00482d0162800e03100035101b402d403000a0080594141840c0c0050030102000340704044201d1040c840d2003160282c0d2414210048400e44410505890125240148000c2600c45d40f10b010031180e082094207240440e08558050a0304c2c42d007003210110790070740c0441442042e605000c2007500300c40030031005145214090706c0000c3d200d603a10010300ca005000c8480101e8580e81c811004802520222548440440c40c145022070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 676995917 1250 676994667 676994683
    0x611030a060504181e0827030f030d0f09060e01050708070e0a150509090c040602280b0403090f0305010b030d0519080a0f0f0207060609020c0a020d05011103010305 72
    0x604285008000600b0341400d0140014040c00c0d10614464420666940d405804102c218101005913a000c00c0000403041340003401d0a41d05181c00460381c12055a04410303201000d02814002d402242000400c03003000000e843d0b079400c0344140410b08101c2180ea0300f0017801c02100c043c1045003000d09100f4844010341c00b0500484050b9144d00c4913656a58082e80e021840c0301c0b095070030000f140420000c10700000079840c80481c0c240390080c9003000480001d07101c0c4d9025114402d004800107010800e40e601005400e40074840c2905813403500312495034480c29004144001380030070702c2c0e20000500300b5100d020340300003512070f0302600d540d070b1a141e013000d034001c150301d0101c07a001c2e00c01c0a855131100c034007583c2074070300d22640b091020f1421801007208a4849401410360004103855500c049a0700b4014064500301c0c0008200058946106003030460503541151f02252780c003441003150452100002c00d00144079601607503c5480d150451a045004140d0030031040524400840040100900422015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 676997167 1250 676995917 676995931
    0x80910290910050607140d05030f07090303140c0703021002010c031a0901050139030f080f130c0503060709260606010318120207061205060306040f02030307061103 72
    0x1640c1803004050101c0340714103440005904070a40c2c41005645455001090890f22031020014120740010085180008041102012500210420810800c0302074040c0d8030442602d8907a54543c5141c070003500088140801c0048600005010100c0c013600f04081c0b00251f074090201807207074011107c000c0c000d01c2c1d40ca0170000002e0800c0062420041c14481c481c59030b140041c181c420903447d02c1d005441d03103928450501c00d80c400c28201e0241c1890f58000c50700074817454030001100818a884c0c001c1611618000c1f50007840320003010701c40c102840540d40d80c0d020840300c05030101d580090810708080021584015810310540c02081407403607008811400301c44039651041262000a0304101e0045025007180d4240d84c04040040c05030b41c481c4e0000c40c00c01c41c9214174030401480301c1d147e00c1202c0f842c009480000d680301407020422194400004840401018820410341c18040e0029884a070007070009041011381c0e884002c01c0d07550a2080b10520f07540011b08100c004010b03c015038058204440d01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 676998417 1250 676997167 676997231
    0x9151809010f0204230117010b0403060e030a080f0711010501031a01270908041701061502030726040e0112030212040302060d050a0f110c010c0c03020d080910 70
    0x309420702d5000395030907241d40003c482c02241210b4080d00000c1700394020181000b070140040703200e4203042d0840c80c2c0030300320845a169565045041001c10707180c0c0f100d000c02250380104081544903502004043d0460003400aa0300561240c206c111140060b20000080319403030100000308101500703201800e451407514070700c10b05a0303131a00030110300010907801ca0400440000440f2400c0c9056020b1620184140c94007403c00b616403040352001d2010382c007502d1040c1e544400901103010881417034400000741d0310046140c9242c540d00e5000700d0105440050300c80b80c513101020000c107170050a81d00648054210840590f0391454200c29401e0101404e41c058014543c14854070b0703200f10101c0e0b00b544c0d00a01400d1415880e4850003000b00790041c481781d005d07551144400901c071203a02456030f9820080351a40e4503400740c02c51150031a12a00004418040c600484500294020650100d410081d040031411a0340b224100c80c1010100780c3e00141040c0b0b400035100819580c01c81ca2060081050a6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 676999667 1250 676998417 676998431
    0xe0904051c0801031119150203092b081606020c0a0201031113050d291006181809080a0306061107081c030e060c040905070f1202130b042403020702010804020915180901 74
    0x2d201d280188c0bd58100c00c05030300c07126803000465810802420501c0d60000d468405d0300035a180d00d02260803011000807503030060400c642c1590313414040c1550007201c1168591800001140c03001b420801482002d02076a100080c64051080061034550324414841c11070a400c00c450384001025001180c0c00703410b0003189100130581e28032500150b5800b51400d8013034407082e800d2980e5080c040701d00a054040c116250290304c80042c410002a01801d00c0a40b07002c10201d080035005009a14080c00390340d40d039030002c0c0c8100314100c0000f8a8580d0200c050a03142103032008041d0480191500b500e8110300c40c8540824400f100c0b15805c01001124005002084180c0364408119400303100724000780b00040c500c41000b079101c42254004c111040d200700c020309103182c1d500340907010703500143e1180c00f0b10b0100000a0344541321003d64004144103d141c00c5240216541c00a0070910010b030010740141038210018141e50b500074600581030000619910b400c461030064a560060308854510140d428090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 677000917 1250 676999667 676999699
    0x5090112090b18070b0f0304061e060b090f0301090b01150507050a1a150109030803130506010b03011706160806041e0b100f17070e0904051c080103111915020309 71
    0x42606c1e00154000c05651858076903465000181105000740700210030303501c46901200d0b01c4d40c4100002070440f510800e032600320784406c12050100401095010341d04145131440080c5000c0d038824107455141d102c03c94100382c2d00da812a00c41c01031550081003403040a1010092108174140041c6000550b001c0110075640c0b2032a11409080f103d251a011400d482c0040c0000303034044002e154451312404060445000f10703100c00c1d140c0f00081e403081c41e00e00d20010040c09144d01c80e04106d030042596500070159400d05070030102c2c82c1414a154902008004070100303105503140c1d040840400b002001034130800a1540e0510018010b01041a01c02c821a08840d40800d0265004400c01696500d400d03142d40721a60500201c40e800a00304410020417000c215076540c1d03100801801940204011300c0303500c0c0039a40c1c440051000c007040001384182030004000254500d5050307602e0f800d05a81058903604052104200c0e43c801c0c1c0c0010068a1000440c060304560010103407800f0304e000c4644c00e220854440f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 677002167 1250 677000917 677000939
    0xb0a1404170c040b1e120a14070b070c06030c051605100b030c010f050714010e0d08010b0f0a050d09061a09101511070f17010507030c05090112090b1807 67
    0x82880d040790340700150701d0702016900e86102d41d0070000380c110710f86c0d900640c3d141c5040041c180811260a544203c003138000c94400c018034005885900d80051a028880d120200790000c2c80c800d08003010303162460300380454810b42c2a14502091441000001c0d9030710b103001c681321a04101701d21481441d1003072014446c500011481c5100d070041e169400d50040300d5030300f11a01e9104100542c0c4900c5000b808041d00d6400340300c0c003007180e8904409020081d100c080700400d0307406c041e4041c1d6006601804007020f018014402c440564510782000d580d40c82c114812540500035100019103010300d040c1c1e40c410717003442110301c0079250360044640701c81c1c623500c074103204400351500d0041ca088640e0b80c80c04a40705070b028000703c0e600c080360715088030000341c0d84034004410021306821103510042600030b100c0e2885c00901810307801600b141014010590880d00041c403502440c03c0c01410040c03424030045010f05030350f000501298014026070040c3c40c004a441c1004480d90038122054849d040b0002072150ba90 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 677003417 1250 677002167 677002181
    0x251203050603160308030a0f06080d05040819020907050c162c1005010302090a090e100b01170609180f0a0311060f0a0b1c050d03060803130b0a1404170c04 68
    0x15007130360854a96421f004010421080c109400544e40ca40101d5140010820129010010b544144c0d0b00c81c00d004200d41040d8401c030404201c0700201641c000140c1c2c43c401425408801e614250303843d41018801c162074900085d0285000d0350607003074046444640b038184c1e6886020080c21003440c10354808400300c03070610200c882100464000703005002c2503100390014444444000c203024034160311040c5c0c02d0300b11024440910aa0382c05490394140d00e1120b8050030010780e4003402c110b00414289200c0500556000305403034440d0b0310100028000710903034500340b11403010210494500c04c3c0e81c6094250b4501491a0a402144400802c22aa42000580a4400d010b00d09420b96551a14024440a4584050225409000300c05681e202c1941c40400611031070007280100603e1205030400303021107145070071941c0e0036007040042c00d030894a0448401d08a4142c9003407203940d2051a0001c0b0380191448114000c00703680005d00140071806407402c1c031001c0e071091701034a920011170f5003004122240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 677004667 1250 677003417 677003423
    0x6061e02070e0a021b03030a0b040c080f0a0608070303050304141912090902030705090901050108130209040c03140d03050a02071208092d190203032512030506031603 73
    0x41070040c8070620050086a400000300f102c050305004114407400d25980083c1c1d2103140a60011080100b908054081d95048000a507010000081d194000030880580202640360407910314001c100ca400d031591011004228807010303119816183c1c035005140c0c0d4400d0381e0540703215080724440c50317150300046440340d604003480328502d0300c00c21280c1c1c2d51a040c50720044a041489030303200340000c0c07240c8140001d6105110a5071096500e44035041084111031042c0c1001e03040190140800200a02c1c030340410807600d0b01200c8116007595103280030740200354107402c004c0200c8000038a89121002c0002c0780218040c664505001a50310007078a03a040303002c2d103c80070b031001d2011071050842500580e089038002200f45c06982c00c3c0050490b4890f0000407000140c0030b415010b8102c0030744100c00b403250058028405041420480315900000d5590250805064072100910b1043d81004007001c9132003101940700302d04900000b0a0400500200306c112a294064001c036010880c07048001742500c010b4982c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 677005917 1250 677004667 677004673
    0x106090311043b070e04060c210908071203020c0f0a0519030e03070807050a050303181516060b0f18070f0903020a0f1a040e0f19050a06061e02 63
    0x14403100001c6541021810035034600503203d4410310031460900848000e0211180356a00703509091500307004403200b802c0380c0b408014160100403201901c036000f0a509400c0d0240c04213800c0c8850501110301d105500d0300030802107503500c0ea0980a605a005400300c0c000f681c0a8420038290340307200340c1d2100905c400040c00d941044803600320380d1038015501d02c8140c0c040d241405074610b01001103032078168035801c00156540000c008000520303050100f54060001507014504140d20014074480e02c003038040b405482240210a040a850b810100756010100d200648942140690900720005c004801219010b41002d540b411a681490441c0305c00d034815202c00a844c40c3e5814101b21007802e40340000c04100040910000b0144c0d50701c01062001e0500b1a04460010346003034200503c0c0090b00300c040f10303c408140320800c8817854952509501c000384402000d02070741c441103200c1184c4074550343c0c40900d51902050208060b25548060b003510200d071500d00300c450a0848201c6503802c00016a00164 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 677007167 1250 677005917 677005961
    0xe0403030b0d030203071b0e070e03070f0b04050402181504140d02090a151d18010b150f07170a0206010618090b06070204050717073b0405010609031104 67
    0x910141c9000e010301c40c001107c01c00c9181c03500540d0031180c0c0300b0758070400040d0303080003100c2c4a441d084c0581401810891400c654a0749030140c8021103000d14400c00344030349c1d80403c00c54000208185030481c140b100038403a0080c446c8102c1c006c0c4040c1c0090054004100c00056110228285550051401c80e0000d04a1505a03500c2e001000505a075912000d000c0c101900001412140d811011010340300c3c01e40004494a800501d41c20f5951003460030500076810f00e01488036903100c2c500c1035122030444800c401d0399444080c0c01080c0310704c101c043c0244104044214000014080e038003400e40c4400590941d030b4a41daa41070f04448440f04100986031004855200300001012076008060b0740c0b00240c445410000f01d6000601180c50481d4400042400c44c6038000c1004241d40c055a8080f9440c02c003840030030142540408041c852080110003568200a4542c003028503420001c0c400301d0042c4184000e40c0c40f1070b03004006050a102c104c4003c2250130f01182c40b881c06006200345c440741c04005124030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 677008417 1250 677007167 677007173
    0xe0d030b010f0509062d0703030b04050609010e0405031201060e04051b0f0d111207020d090b0318010b3606030c010e060f0406170c03091c12060e0403030b0d03020307 73
    0x9075000f0f006e40c2c0300d007411241c0340400004d0154010100b015000c502c50780c59032114100541039828a0300b12a100b185080100301081d5901010030341928400d81010040d50344511b4160328500c1452564007040d01007070000031719141d0122080c9403071042954180425120070080600701c55514075001800301c0240030703e2007041c0c42c020141100700c25801010403805601e500d01440c560100301410701c103081c05820400c003550100214413070355080d45020100d01d4504905200c2034000a4000940203400004980d0240000d40007451002d00092026040001d03260a0380311103c407041010300c0e8125150361610010100718115841283c01a000d40b0b10000c200740115299098584400d078020340070700404c81145400c00241c00901801e8517140e5940706280c0130f43d142000300400c407074200b000030070030014160800f00b40d004080100008200d50344000c50310075100c81001e000700300140f91400100103904246440c4030ba010354000c0d1000c00c03030103d1003801d00407100741c11180500035a1081100f5400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 677009667 1250 677008417 677008429
    0x120309120f031103120105190504021803060f1902090a030203060f0a110717030a270501050609071205041103120405190302030613080d0e0109050606030d0e120a060e0d030b010f0509 80
    0x105987c00484001550303160309c0003c0c1240c03c2290a80e074800c950311841100d1b420100000c541045600702509110714180504005600c15100e070620352603004100780d4119229065601d0103142e00800740c81280c50074148125109404a5000001a0070111b03502080c82c0e036030042341c07007198000b01d1803000718051a00c1c44d225030b800605030f0030a00399640ba485614155200d4508180003408c503e072849200c0c1c0341016420744802800641c8900580d01c14058907641141d40c1050400202e44040350f01c1d616418542d042c070340518400b41d010300541c98503618254a1400500039103508480841584040c2c3e050702000029a003c000e401d0390010022500100000820417500c500c50503000d860002c03000303205419190301c80160f0280d82e4554181c0c904018040c4604ca138010710650007000c0e045d2005070001c080003200d8040030b001d00c00305620302000c2001444002401900448180301425442d01d80d5665000c0003140039000a2511b6480c030210340c4074148031030700c5024541d1801d040408560411107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 677010917 1250 677009667 677009689
    0x60a0c09083a0f0806010504230109080102030c130803091503090a230c01031a01110a05010516090f0f09020a18091d0102030f01120309120f031103120105 68
    0x10800800c02d0340c0c0111003502c02d0629100811580d1071401070240b5110183c88000043c04031418000c040c0424001001000300b12102da02c20b68942c80f540f4180800180c0b06909a904a0012135000000b0400050500f2009200d003d940352000c0f000b150fa94410284c580c01480100c6502c500621944042400030801450300885400f0549000504540c0e964110020905040401340f8040b041041c0f48907043c0700c4452940002e013001d20496804c20b0f10030341c15564810116041c4589446100701404007000181103240e4040000c12450501202c0306088600f1180390034000307040390501003911408504414210307859440740500150a0100c10b0000e9005a406031007048164601c104162041002e200000d006964001400315850100c182e00000ba40c15404010380c010000d01c01c80754080d82d007980c112080c0402c500d40103480d524049070a20440da20130042e91749811140300600c0610040e18810a1094803401102903407400c005031a401568030398a54503681e100100840d0501d40802d40d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 677012167 1250 677010917 677010973
    0x103080d0903200a0b241507021503060f010f05270603040c05100207030203120d06080601030c060f1b110402040803280c02031f020f0c060a0c0908 65
    0x10120796500f0704400000c605501103a0081d500c90a04101440080949150403d02820750b0343c0038a0f40ba1404902c404c40000075a60207a0070800004080c00e010b40c1c02d030b602c02940107100319404d908410049400360025514140320b0f80f055800740c0e1056014004c001203142c141d40303643e41000c074a4000b4107803200c81103148202c40c11415540c5000c03655004002d500c100d1003901100d980a080406025507103103440d000f14203541c045da07414005a540090307100c583e480f16034042656020240250340103494154085c1d8228460080003200b0041112482410b9900a6460440b05d00c12208104c0b10304140040c40760122410381c0d03c81c0003240c010f410a520740c00010344058545a82c42c8040b600d10303480700220130b1904d10506800894070301d000001c000011103074070304140010801d40010351600d03243e440001c00c9100500c1201d6010946405641c070188100d0301a03902c40756030302d08203511120200c8940a24514190710040385500072024001621911401044070202842c80381404140d204466 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 677013417 1250 677012167 677012177
    0x40b070e09090d350606040305011805010c1412070c0803130b0108030a08010e090a050d0306031509110f03010e01060311120303060f040f0b0d0b1801050103080d0903 73
    0x4040d6078440010490140072034000a10031554500f1000b003040f00500048220102c1c2c0500d1040c0d5190008160f190340700040118204a440310780014810740f241c1d034801490365080440e5841c00c11f01000c40c800005014800900c1490002401201c030240d860000e90100360041c050800781004a04405a200200c0e0601c480b00408645414800d030f0000c40d210001d1440400c280d508202040c545213004008110007107080078402030025110000500400800c0404940010030340071040000741c071041c0c1c10406440765200124001000b401c02800260780d00001503410014400b468460f03104010f4010074590802d41040081004804400c0000c603030640d00e444001c0d45100080c032a0740c0045204065600c02d0111300020700810164124a182c5560030074010001d0588642c18000d680301ca04480005030401100364103001820200300058021030400202c0042200d08500c0c54010140e010707540c0754103442180203900361102404018925541031202c001c140a858210b00940c0d4424100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 677014667 1250 677013417 677013437
    0x1401090b0d06020705460b01030b1314060609010b070c0e070903020301060e0106110304211401021303030905040902010203072315070f0c0305030712020d110c0d02030909040b07 78
    0x1540842e242c4813010b5141b20084640c6072038140c10b4440a070300b200a02c41581c20020410740d201c030307001071a052001801405501c0006100c460343d201c0384603026036210015038840718214641e2950f80f10b0072101a03014003042c0001050070303187d0b40c05803600668802c1081108a0400c0141c0c007040358040c1400003480350740c000c00f1006903000e0061b800075210744680325419625185006181545c02c0c1114107483d041000140103220a00d02c11100750340006135400142095441c01c10340c1729503001d0040440b548007107940c01e5180c851100b40c404484c002c1d95400d00d140d85800401c0111405550700901690041050070001410460380c910a40345090521142c3d0225058041c00d001c090141032045214103030800031480e42090000c41c00048a07c1c240b545001d607585c01408512000e0040020301241a8594071146843d404481c8902078054051140411f5076410750810342148900024600450101c101d209100009440d0a054010315040c01d03a00c90351580c3c2000c000203045038081081c0703007003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 677015917 1250 677014667 677014693
    0x30b01020c060408032212080304020f060a0c0c0602030408070501030509240a0e03040b07060906060302300f120c1203101401030b0f0609030f060403031401090b0d06020705 76
    0x4042c1000f008613002a640e80c61400459806c1410340c4064440310702019142845101d102841080e100c56105011555940300c03800001c415400c4190550742c0302e100040c0260503243d0019031404041c0c0306a00041d1104e80b1100203988078041c2d4000d1400b1680283c100308402d42c426003010fa000544241500c11002c2414400f03281000c03440e0002002c07c0241c02445041c0c01603118181003254498069410642040c000c0703c4c0c940320700c0e900600200d0301c0720350520503c11190300907802142d0041101d0040400060010200c00310f80050140b00c061070b40906c0f003034034408917140d44014181005070100e00c440e40323002d2103d80c100d46584507061158a4032849407110420007140a5091609028042d610700020000d003180014110343c10107003000f9045901307440f140c00c440c041800844001e074440040700040792926605101c100c0d090712a0f481403101b456015405020b0302c4031104103c40e1035a80b540c2da032a0a4030070904250790000740c00c003150380120f82664003400c40188a03500b69089110400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 677017167 1250 677015917 677015929
    0x1a091b0904051f0b0406051e0d05070305090c0a0311060c1002040939030b15120f0112080301120809060a1d01030618020a05091203070b1302090403030b01020c 70
    0x120002840000e800c030344401c81000070f80020040410450301403a041c01c0410007031842c011704903003403445502036010840e805100303001d84105a5503200d040003c0c0ca4000001000740c41d0036201c4281e24014810403412500341052a17a080d02c0c0c0003070489009070800b1060100a910204221019011b41c0e5403620910b0690300081004103861000403541e070b04051100d8080103043c01b03087c030501890094003900c04280154038245003d2a003000980e00c203400012403503001031300c02801e41070f0800040f03256080c05c911000d14081c050307111300d80805a80b61070300e54240e0300800002800584c0c05000403c1602c01c0000d42c601110710954100d4201502c0d5004100240c01241004021070306c400ca60032040d605068086841c03803400d107000d204503441c05158100e1201611041c1c95a6074001412489240c0920101c90740010302030300f506170340e00d82241c5641e204c0c0c01000e01241e603c3e8090010448400400d422034180309c1c2c0081000780035440780d03501a0300a0a8003081d941c1503006980707140700355079645 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 677018417 1250 677017167 677017171
    0x7031d060f0a06060f110106080a060f05011208160c050d15050a050624090d0c031202010c05091917030a03140702030a0f020c090406020d1a091b090405 67
    0x88010205801c190164404034140100a000498a0100e040100360341c0b004c0d00500300c6215091083d19140c0c0c1e0032800b03000d001d69401100880c03003800140c0e810402c0690104403403e00001003004181d80350b5100c0202c0c0410918050070001081c802a40d803115035800400f10f10344a00807035030702141c1e6000410f0856190107000e031f955460319140051050038030300540e82c0c00114140104106c2c03030728000040300381200002c0399a0749450744251000c403607080402ca540346440240b0300c0034424117524124000c002680021102081481c14410509005001b000b4900b00c1c00d4031850304061707001007400810340903001441c0e400a219040002e42c408640d552102e6411103401445d580c80c0300c000043c0c140c0705110306121034061820708101c070140e404029a0185c0208e450040043c00140c0c0089203040d1001c450316070311650039003d0004102455004140b6030007001d00c1881440c2200f0102c1c18000f800299050704440e01c0c030700242c0c0c8111142d00710710527010300740e8402d814440d548020034115001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 677019667 1250 677018417 677018471
    0x303050304050c010e10261503101404060b040b0d05010c2a0f030936020315042310090b2d0d05010e1f06050306040b0703 54
    0x384800d00205000040d00003d0a0a04a500d42c650b50007103280e000101101c4410012400341c07081ba81c1e1100290103550300b1510700144103070309121000c0c034036160b4000381c003610900c00d403105060324043e02e01030224860141421001c41c2e81d03554480b40c01400868120b80c0d8410f80c0c901d145000b90b95500703000c120302c038001e100015528141c000041c014104d00800007a4021004620340c50304882c0c0c0f0340c02210b01707071700400d00380c8450001d141c2514007142070b070801000c0c102c5c42c410b050b6022038181c48060300030000603c50880c00314503421050481c8016201e00c00c00040d0031490014609042d004098100c0380c0841a610041c036040a0f01110102a980304260500e2058104880c80040c014414110000c6803d4440d8111491a003944c1c12500d024030810021660301100f07003a030302ca01040b10010f41020080c800140c441034005c0c1c403144501c0040c4081c0c8121214140001c0141c40341a042d983c0143c0100f8068440340c07601c0755500c4008090104040d21025500989446600e01d142441c803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 677020917 1250 677019667 677019677
    0xd110d150509070f0f05030304050d0804080712150509031815070804090509280f14012009100c08041d040c080a0809040b132c0a030c030f050d060303 66
    0x1082465042c130121071540440068408068144007d5801108607021a00d01f160032402880061500048500807503000e41002d01655400042042c02c0410510b822842200c002903038817079005200080342d400303454189a035401030103440c00a0401c944002c1e9000401015024025280103541e00e413584541c03400c80b1559001700701041010752038058541c000030240060300000141c80300390710b504c58803010000251a2a004568140b2403088981485c86400c80240d9000002d4868454041d007180e04a516050b00062001c043c150703103d80546103c000700411080c40c800c41914121020209401c0681d004a820440001c00c038a484102c080c2e20841c2c1094880607280c1401c1080b10b105407a0b22411f182d404c1403907020000741121013205e07a03000c4222000110101000041035008649951201407149445a019002100003928001c015940c607910481092559541c50f21169244401408100080c81c201e000a019140344013060401d0301c0c0c100c1c00c22212301207207415900c3c40d038004c1e00460 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 677022167 1250 677020917 677020919
    0xa06080f10030c1710050708040803150312070b1005010f050d020f0406031407030b06040302061606090803062809022506020d0b041b08090c091806060d110d15050907 73
    0x40f03000e101c044000170001e2000c001c00d150403007002d81070070401040100745000000c00201110a500d8903803890704030181c2265810613a030301c80382c80d1030351007800d040c0d40c8180704200141c040c004581d075810680e181a991440602174110094a2540161004814154080c03242941d40072010003c3e000034013450341c01060b01d50710300c520140b00d90b81c0600303007404250400c981c004940d20f5900464040343da0550790705603142c2000201007600c0411500092400782018200070a100041e000b440c021641111110464091a01510030303605005004040030603110200700400a0f09a01814100200030941c1c914002641410313040c0740f5008004444566011035401412040b610407501d03440d0081d60204070105a0914100005060b0000142000202e00015815110a01c0398804941e400b81c0140140d080280e5810340740e0302d406150f035540b8460300000880078502400d281400a0300400d80c00025155681404014800e07400e060724414030100c6044d00110a070710a251141d40c00c20050701e106 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 677023417 1250 677022167 677022209
    0x30105190c020706020a020d021c0b090106050a05030c090414030c0105041502030705191209140d080708150102031b06160906020c0d110d050304140a06080f10030c 72
    0x441ca40300d495011988204402c0c000d40e500050b1178000f80b50115842210710b0a00d100281c07128908014040c41c081007191140200030440d11894003a03040c52000b4002642c4500c00d01c00341000501c03a0682c540d1082d07581003d42d050a4000540040c003540f50440302c1e1508400c0d291440d400358503030750500c1e03645d207007000140180c0400c00c8815194960040d40345007130002c0d005201e80503142a00b2030b0040405071500c0c4890003645002c591040690040c03200007001d080003c8803048040c00d00001d409019452842c162241003014804e1b0b0311501d4800407a154102c1c1c0310480344d000c039030050552008011400101c2541c4012842500607a030081c805451b29400444050303103000249814000441d00511489401040101c4880419954a03840f007510742840030b1384207101d0103400d800099102c000c6040c0304d4003100a0081e161030070f0403450b039082003030140140d4040c50b02c2094001210032001c07900414032540d5064001e1660740c811000d141d2a6151444407124a40c424030b466071503841c0c45001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 677024667 1250 677023417 677023421
    0x16030c200102070b0115020709050105010507060c021e070e060604030f120903020612150a2709080c0307021008010b0f030a150602010e0f0708060c09010c0c0905060405010e151203070203010519 85
    0x1809c030341241401075500d06000640315000d8620000c01554641822140492007000343d0380454400c1c00402d402604a103050f640c44121ba400740f44c541e00c00800001d9001e0800c4002c0394112644030b4901104240d00361103100544c64151811020051100c20003c0503980340342c00382110010220311100c550410440d4000290516448a0701410025404101040c01f58003580e40010180da40c2c9191f060580d220700000b4421640020b050150205804581c00000005025114800d940f442070600d40b01e0003e135041442403050220700134080000d6140d02565101a5400004402c030124280d40c003200c643e8180c840c60f030400f00050b952102540c0c105d5204101d0070460300c101c10058244030f03041815131a16800c0040c06404015000a80c1c4485644101c0340d6454140e08080d42c103800782e8a41d44c0c170b0340c060441074070214880c03401c200c008110503c80851107801200030202c11801e040c192024045210b2806d050350000340414002d5402585003802200d1150482c2d0120f400d500d0b1b411000541 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 677025917 1250 677024667 677024669
    0x3030d0c080f090d0c03051e040b0a020607020f1906020405221802010215060a05030a050c09010902090913060608100504020306130c0b131d16030c200102070b01150207 74
    0x300582c8144540c13405940c01000058803203401d45813603035540c03180100c106052801da058240c03030440d0014000500040006c0980905022075003901c4480e01c1d845c80c04c80e624510072030700c088140c0103030310b420164407204015032081b180700d03220150038555200e001461500b03801090341c16070407840c884041c2480a40c800c6c0b541d8601881e01d08502030030f480e00001d540f40e016170800050070031004042036507a44c070100204024540141290002241860882c0d101d24415000a001e00764800004c5401350040c002d903903609502a200904583e5030803503020700a5492030042d15a035a44000206e96201c00340145080d500000001041314201403050503d4030340001c10801d10710710162405000240e1400e14002262020000c0903154a4402b4100407062007d81c80400900b05001c003083c00d841e01c400e41103110340c07503143da206d01c4c0002e401810350543c1c043c0901d000015200301031620000704403400100d211400400018100113442d03641015054003a00f010b4082080e46c015103446a03070405c0898 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 677027167 1250 677025917 677025931
    0x120a0506070216090902030c03060c040303030605090c0d0209010905040c0302040503070e10060c031106040b01030209090a170d020705010204060e091806040b06010e09040c0510140a0302070203030d0c080f 90
    0x1582c43c03003040807031108401400b0300b40700c032912042c100d01559020002c0d0f0714600c4000301a00c05074240940f0390b81241d03029102c1200030904010000955160801a0754410300d030745001e0318a082070202d00a0001d502c0071300403034103114030001c1c080382c5070f02d032032003441c0b07203c2032680b8010307a142e0400040510349206035000c0c0c4110782d0b802c0b007001055007040c0c8508045035000d042c40da1240025107000e07168070055410050740c2c2c0c070030701081106100d43c1c8007056040302c0c000c0e28080a1034649590f042d85074820044060b142803044d02d203002500050790000c006221901030010b04020f1141d580130f00760380c031a82c03005001805d0401003d003a8942040c0d00350f04a90314000a02c45290802031454460350024005401d810016000994903401742c43e01c0042800d0041110701c50785428580240c0c6a030f811300880f4003a94440707410f1440d041c0101c07006858175081104150601c02c071400c0880103075005403000c0741c050205026980c0c10100d01c3c0100070700402c035625400207618060b03c00b2000c04600401b81 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 677028417 1250 677027167 677027173
    0x1e1704033204050114071406161b110307090f0606030507090e04120905180f070504030b04020d140f06011d04150f020903030703120f110a0f020c120a05060702 70
    0x42075800c001e10040360120389003800c00c0807282a00c400000e0103402540b8000e0650a082103001e01b0850307011071090312920a0100140015192081c2116040e0325090040704d00c044491911020039600340040c400103800600310364180d40c590340e100c070079112221000a10b45ea111607041c008180c1600806500030300500d000d6200b1440c05028885400c809080500741440c0c841d102c01c0e9031482408031b4405404041c200142079401d05100c00f180c0a0222a0209444d94000c00304040071701c984103e5044a0300903100c0e024549480d002c100079846210300031146880c03080140380c00e14005210410203903200f0030203802c1940c500851170305600c07504131188055440f05010000040e0460b101444500b01080b00044c00c14645400c480003441030455069141c48041039200403d6401040c0c440c114400d00014440d011489180d030040c0d030b02c1e1413041c0c1c0c070b01d150a0081c0f2041a00c40c00d0201307403c8500d4412a11503124400200d10344100030701c00c01c803003500101030a5040c44420040603410624034401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 677029667 1250 677028417 677028497
    0xb03060c0409180c0608060301060f150302090402130e0f07091a161403070c0e06060418200306030d09061407050c30010203071e170403 60
    0x200815100d14040c180c00165a010040070307043c3c00400384404140d1040a441c10701ea01c40c5070107440c0d401c04072803080c40380d805e018001c150100080c501034200e824240000464106801060f8083d4002e03008a50300980e003480b418048418200102008206d0031703200c10b410b401c2c07444810f0343c0f6820041c121003c0c06107003e020429007d40b8400001c11812184085468081c440e1000e511104100740c0901310200c0309044080000d0b002c030040c5129440b807400c0d02c011710795a02d50a94400000c40340c080e40520306200801c50040f00c1410040d8a80490900081814081117005041d21022003011807400e004010400e0509040100034003241c49802c0100388a45000c0c00240800c98103506000002408a80c42c030401c0000c020154287c0002011007a00c41e0406001c0f100c07414142c2c40000d04526140b002100b07170074041c400c90b8015809643c6203604201c0360341419018054441c001010080c4c1e40c503030380d48801d0408844501851207036492000314460341c0c0712058000c500303440400c80b040310000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 677030917 1250 677029667 677029681
    0x20f010506010219030c0b040605010f05041803140f030c090f06070215090a08010e0f07060801121e050a0f020108091203010905100f09060603150b03060f062a010b0306 74
    0xc0c80282074405800310300072064503840c0c101c41b10300d04443e005111003110400d10040003803640005050342c0711042d0200080795150104020b0760061110392031022513030880b2401203480f40200c141c1c00314880100d04c0c6000a500c150003401d51080342c4544c4481808121500c10303107458284c006254408880c0e06040154940000e07120251a208121380704000064075819922409210740081055070006c205000184403aa5101e001034010310044e4000c6031030108400b0701039100c56050380d0000c0e21900850b4001e40d60701d603000d5030340041e000786e070300a400b00c460000ba4108510303601c140c8624103402c15000340d807002500c02c0c000036009800315000319041c2451004910b06580c1151510329000ca155210742e011180c1e48503c0e60411101541c1c00c002c0400c0030b000c0c54110500b110941c0c6d804003d80c00909424042954541c000c98a1030304081012070701519022452010505004000900e0400c1444032100440c55516400080422030382400c80907603000e1250281c1c6d110150003500440c5480d40d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 677032167 1250 677030917 677030923
    0x1b120f05040503030a1d010e1609050708130312052a19050f1b0304240509130b060318211b0111121f18020f0f0409020a020f0105060102 60
    0x9141ca400c0700c0d510100e07882542c41b01c00004e4190040e45c4003c0012501240f947c645805402e20f41c00303485800800002084c8110744512441010107944061090b12801550070380401814400c0d4100201650341c514022164460540104e009260580c050941d0b034481510032401e00090391592041406910110720105020000c0281c651810310340d12544060a00e04a0145c504500d50040321440320f01041400040103000303075815628020b0f905403400c0210074441c084100c0c4140090409d01c102072141c20801004884000d03001c001065500d1000c02048080c0c00880301310542040106454a050005008100f41890f044242c00400803000744140360600c60a400750f80b4540341e440c0f141600103001c0d0321207110b038040d4540150b9203d910440e46445000d05950f0448004541410603908415514588045810101e06001c0d010010151200250041d850500e0540f100b042441c5c1d20540c0d41c0c0042c400380a0300c200060300c43d203912000a19018481d00c180381240c1c94241800740680e000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 677033417 1250 677032167 677032171
    0x703090b070c0212060a0605032b0e4209060301030b1015020a0b01141315170102040906050603011d0a020909090706030e03040609031202011b120f0504050303 70
    0x780c202015442041e10103d10701e280f05940410090080030240702132aa610303000013003260030480485601c42c0d0640e2810184029a200c07440740d801c81303c0d04c19030a190140199491303015000301b00d19207414003030b081010600d001c602d414483d04e0203201640c0312281d000300c000b084014545880c5042100f081e01040980c0320601018284200080000704080b00031512400035101c12081120b000c1c00040000c0d40e070308112035044465211039000481c5611043c01d8056850400805407491003a040300343c0300080002c40505c03903036040c241401007850a03088000d000c2c01903ca01c00140d803546800c0d00407041f1a03a540000d4840c4900300010030440164020a83d100d0b200e00c40c51604648540800000910031030b1006600010540d0420180e4040800c2c924210707021514180458031103502d91a441c1c5c415801048017040c00c2010a1001c101020101501c80c42d8130300000907465032454080600035500310300d450000d140c810740d148011000f80150700349d0a07440700050025003005d42c2c0d0340d5124080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 677034667 1250 677033417 677033431
    0x308010f0b070503090d230a020109050919111605060108010c050a020d0e130612050106050a060c0f0c0807080f0c0d030f050c1e0109140a0812190614090703090b 71
    0x4080305a406000c041a071100140e101c900c081c021f400c4680c050b0b15121454410300764049098104001800d041890541e2720401c41e242c9032007407800c04001d0f0403005044034800d400442c903044c8103d601000400b1034200321140a1801031441e50302d02308000d801e5808030302651081000c02c0c84129102e40c0c00141d402d0201c401c030f0400140d040e0600c00803c02240041aa0455080c01c2036000105a8007640031640c80a014400900106441c0d8060240340e048922800001842602e04038011607a0741518002d4144241500b490241ea5150300c10b2030425603400c000250317042146001c002d50340400c08161600e40544103d000e24043d9200602080a00031505091110008402003892018007a1004003079803030311a00b12074175003c1c4c0c2180c001d004032502103611444000b0420800b402c001078a1410650156819140190f000c10300821014060943c140c821010740c0d01d031000b4603050040750080c0852012951064407590100250310320090240c101307261400c0085004185003052466101d21 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 677035917 1250 677034667 677034679
    0x3040c1a0c010f0e120706090b0109020c0d020a0b060f060c0d030219021b1512070f030b09041110050705010f1505060c0a140709020c0307111f1b0204090308010f0b07050309 76
    0x150420901a200a03230008042c4078036000007041202595015114017001034040f101010314081080ea51443c80900c090014006c001c002052450400f08807004510040c2c040d80c1401070901015103490300842201c00403e4001c92201407640000280c405c00160b01d1004002980303092546007101588448801c0c010003010307200980381114103044507141140404201c0b194500620010f040c4107202c0543c01c0081d060040480302840c144070341c075025640001404100c04582c4040084082d5070400d44002c0c450180224004034800b0300c122400820950404910044480070b034244c015140c0d0402486000280004c881c10140041d088640c0c86d840791190030200d071212442440d00741194402e169070b5000103450141c9120100107010001e100c0e10682c0008140d610401c41204011002580010b40c404030203814503205500f03900300c10844a814226100d0181c0100c0d0075145a098140d011440d2400100804099046120001d0901d0f080b081e05200c120364032a46c0f03030312981058521440c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 677037167 1250 677035917 677035927
    0x403080c07031209111806031c080a0b0109030b0f011503020c0303040b0402191d0709081b1c0b071d0a050411090307180c05040b04090203040c1a0c010f0e12 69
    0x110424080191720b010090100d0883ca010200c2402035200482c0d001d40a0700424480c0a04940c00031100e84c00302e40d031912400300c03d80d201c4107040010300c43c4030403140c100204100008049540840004c0c001c0000c0c1404144c2c941c180000014544c001c6002c00041610420001035510700100641c0e40181d07203d9808001d544990001030100c810b541c06100d00341c00ba1480008401c024074207012104000707000c001d0101d6032082c1050340c40c258035100c0d160450f00101c0013810b003001d684400422005000380989c1c4040c140c0c0c401c000c550742511004455025154081c8048207401c210004400c005400005000038080c001241d1084d0003407081c02d00035a1131b010300880c52100c2d40e09540b280100a0111a130155555011413022040300d000d18056918205418070fa242c850f00880e02035807201400d840c0b4103813920070100002e5100030015030f102c0000b080c0201d50242d0a420b491411080c22001da515035010400309405c40f43c45907610300d0202d250100b900c0c40340e00f010562a031a0a04c04030b40507252 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 677038417 1250 677037167 677037173
    0x2120f160504032406180f14061c0c08030d09020102100501050105040b090607120f080906090d11011808030702011118150c030304060504140a0c090e0309120102030403080c07031209 80
    0xa0119a000048102e56440c0001641c6900e94000c7d480c44240042c18000ba008900095070181000d03a8850b8104080703440043d00002a01306803828141f18108000d256503581c21480d055800124949001c583c81e40d0f4400195a4100301c00b86030800d41d84400c101c5545400006041d9110700d00c100c202a071401718118109a440c00305075600c0c542c100d060303100a5120010000d026880103074800001c205002c01080590344001034091061803058014a00021415002d5070050000340e8585510745d00c0d446096a24420078083c00c4d4484d00c03410310591039080101c0c019080d25010b6409481d851000c3c07004401c90030b20030f007003100c0510050390b20b201c4080606001c46507034451b030720703119030244400014001003080340d62003503220303d0241c1d541e20007618103143e8481d220b00c5200805085104416400d0010500503030001d2040c40c00c1004403440e1031040008102000003200e9410416540402084203040d001b26842c0e51107103024484e01c0c42d2500d1a40d0150109502d003220341c62990f99003d4020070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 677039667 1250 677038417 677038421
    0x70311060d051e070503070c031209050d210903170a18051c0c150e100c080907061e1803061e0f0e190602120f1605040324 54
    0x1118512540c2801245404150003d0007007032620040101c00b034160008412030b01c2402500c1c002c01142d9205180740116450480700c8404a40d00c800c4e10b1680c40540c000010410880441d086d0f080381c4400740c0702400d50301b8007684220410070307498025003044100c00008c0d6202400343d0310f90108603d54286521380c00c0300c8d4402015142d58541c1e01801c0000b2000034800c00040c4a0f100e04894442d42c25180c000240844080211050042619480440d50207a95407540c201c0030005031b204086540e210a9814440c080d40c81d40f50103100403170461030512110343e5062010314060852820420201c50b5040020510031007000a40b008110680c140303550884180b40011004582100050180310030081400500a001c502c0c01007245141134040100c1e10454042c0010303010203c0040c00b8814182c2c081e800802d040108222021a4208400303500300d28554201070084002c80c3c84508180303860700409060f001940c4092040c88001d0104000040340f880c0b0880b076060320000c5000c1402010164100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 677040917 1250 677039667 677039677
    0x10c080c01141807090603020607060b220b1906092607350706111203040c1502030f090f0409061b12090b040b1e070512010b030907031106 61
    0x1210b5440c4041c014528000144018110050020340e00203680c0c400904048400c0c070b2100942001c400d11503880824102d600c0307800c0d603500c043d15890200889060502c50b140041c0000e4620650ba5070040e84c0e00e003000a00310721442089604410502d0415030003610300704892003590001ea140b04202056040744a642a500306664400c5070f45698450844100301d040d03200710001700d201c0b04ca0080e441c20541c1c5d4072201c0c0812542025084da58101281191180b0242d2040f8402e48245404c0741381c03040c50302005620540c0622400541e5908041c068001c074040c040c41c240c1198420302440e519031182c1e10031a16220000c4466800740040c0001003005445401e0000c5c04891805481e0100744491500c00e8000003c103a5800c100c000008030404212592400040d000e400048006000100c407800b11580003244403031004180540d08038440c8480300d0440c0d504001500104025401d5241001003501409802c603000e4110300d060307980c0d90f56410315440090204040d00440d161241c507100f007210 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 677042167 1250 677040917 677040941
    0x90605090a09020d080423030a031e05070b0c0310270b0f060307020708070510080c031302030d020c09130b061302040b0d050103050f0304050a0902210f0412020c010c080c01 76
    0x54843d80d542481c244c1911f05a141e8012603035070700c20900d0302850003041041d0304070391644603118540c21003004002c0c0406100d807080c00340304040200d44045100304000324800c040605d54141c0d40e103840b00b004411712400e0303805101c81400148007118504c070b400b0f0130a805607908d001c0000d1031031000e41c00650128410701130346070880c5000003401101076021960801703a418180880d1501c90b0780f40b060101d03d5a000c0405400101c2080104499440da00021a00540e400f0701d02c140c520030039000a41410801c0c1c2503840541d0150200040500b0600c440d140d00c03011900080e1503015594071040a207180c02803140d44a4404c0c0220103000010907419140981558100c860700e40212040b007000806080c00183d8091060300b900300d907003410000813a020750b40b010740620000f5282c40d030450701039081a01004c907548181d6103001d2040c404092414031400e0311100280f014200340c28521544224800040c1c1190001c1c0c5a10f116660040f6131f0420305c43e0b012400d669164100b52141d801800c0080f055 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 677043417 1250 677042167 677042183
    0x50c07060c270b07062a080106030c090e010b09030a05100b0f060a0203041e03020303033303030f0705101d07060e1c02030f12030a06090605090a09020d 67
    0x1e00c003034961110790600503104900700e00c054142d10384841c1c00410031038814500b0291080203124005202c68105c00341c0c0c02c1900038002c10b840802d12004502c00349900302c000015160100411005034035015582808010742050f0519074100b081103260417405028038070340c003800003825034110f0f00e08200006226800100741d900b44443d512401000d4540c0c110418896841c10b402846180f1303210301110b0540d120764005603e0203180442d81040f9400803409028a003074940e2000002d42c80c144000c601c2581885900000b0603215080c520201009600c54a51a49003884004a94600004a416400317030b08c4003058803603201c1e00c0e2041c5403402d1300b04120341081c00c10301421aa51054800410040405016a0845520f0b004111080281c071018079500003150541070803110200304144007510b0004e4161004d19a2001c2c503140740405c0304403a02ca20900c001f0812040900d1071060720301501203040188202d40c50800000d8070314401034103142c0c0d125a1401e2081c115521001b8174400d860340300c00d038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 677044667 1250 677043417 677043431
    0x7020d03030e16150f17130203030f032716030201080a0603140a05010c080405190201051b06060111010902030c190f0608040b010504090b0711010f06092405060d050c0706 75
    0x901c010000300c40d284000030545e00d000c0e40c1d0b21240100540c4443c041c0c52821407015039180d122030400103042ca40141d80500080201030700f0300d000c540080d440360100242c0214081101d0864140b1481da0199138900c82d00149510040b6500b403103640c104994092808280d42e8980b154624014502e65200616140c00340041601c902c134007103000d4102d2800b0f14000c001c0700c0c40f01a01607c9556040b100205140c11401160391841e12245407241500d006140c09030506e00c0c0c01c000850600150710034001e1603841101007140e55a8007212100042d42000024071100101e40d0200307603207500082d07105101c2c2540140040d8061001c100140c020244104006801560350300050130f02d05043e50b05031204c1040000108040c18035000b03101c4000e90003481c00c0361650324403004803090160000b100c0541d54a4695a4040300528081d050250100c40400111840d10b8200d50010000103040d1000140d009d070010080c0d5030306c04050360060000c4800c08650740e955003000000d80e104040004181c03500e00300c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 677045917 1250 677044667 677044679
    0x516050315070908150105041401030c030609050c1002010912030e2109151209070f03080a0c020405011e1401090b210103031205091209010e0109030227010b07020d03030e16 76
    0x2141758100c071000c0d50100500b0701c0d40007007541000400d00028000c0075010004100003820fa80c01803424600440941d01c980302000000f030340000242d00c402c1c006070344410046040c0480c214840108440d83d040030000d46213805117a40c0c49182100100c8501e2807507040d03500e40308030008120303018254010039400c0b50a410b41c460342c000d50001c4803124814594a4009000307070030005050420340d02d0500500c4c0307800d440c0da6141e2200c3ea0003c1d02007020840c4801c0c000c070040e2198002c0f80e02a020040e5148a811048403c100381c1601583c003070212240d40c50040e0707036070ba604800d141c03046c5d40c040d1081035034801c42c0c0020440b0101c0c0c0c010440c5521a4654000018158803640318400200580420f2107292103140540c0d43c0c1d00072000a0714a256810410810a90f000740300c10b144000e0103041550710f139603490b0002a20b0a8611000c42022002031000525000c00703009503502400d1040091400c000050f008920078003411100202490b0703031116840d130f080004004080c40e4888100c1c55419003034440d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 677047167 1250 677045917 677045953
    0x5040906090507081e040609060e0d050c0c09131103071503150b1201180e01060b0702030d020a050601030206070809061932031308160516050315070908 67
    0x1905140003962080100e918101d0400f0150903c0c80c410706405615199500c1f140d004000100c02101c20341c0e42c400c0004c4106800344011612003810b502c44a0319646119070700da041002a140701840782c0d088604002000d100400200f003101e80200f50307103020840840c082490f01385190082250303602c490401341c4480d0340c103401c0b014a1144200a02da9500c0d40c0e9403260000b070280061840c2c40781d44140040c010303402c41a9007080721440fa082c003c1410003880c04880d08450980c2c00103240e0503000110501035040030004806c080c045440207001000c02e60b00d8058581106000083c4070f00343c00149030090040030400c0d030b1b0042c000100156501c07a20401e41c00d401d840f060016502061007070420b500c06501000502c03542468a041804418000075081aa0359000818119030901200b10700c50100d444a0060411007041d034106a00744181e6042191174401c4090784940d04000800317050049443c04505541c0e0607080d105200035a032078a00068030000890b8219690341e00c606402081e64506072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 677048417 1250 677047167 677047171
    0xc15010609050109141e060c0114090f0d0c03180b07150b0f040b031002131706161d09070c200f060c1002030f091e06070f050409060905 60
    0x54035140701d501e40d580e0054843c06031511070080e52102c0c8510003002c50501c03485400b102465002c0c10001c0c60395030000544150030040c0c0a003442c0c1e644403512060a0291001c03540c0000300c84005203001040041025038965035031038003200308002e00940c2420140140c8800c254040807511780b40e40d00d91584001c840c1a08a0001078810003031034030065240391500c2c420780310402c002400420041c0728960511010781a81151950140700e0550466258503491018003410b0516021100311071f0310341406041021980388c05045280c12444c140315001c6044081180d07540b03900e00346010341c080d55440c2036490b001c003641c000303400c030541c401000140c03980050f840d03440d944a1028041340240c00c0441ca11622850a030309600903002a502403c03e1034088040d2201e41c40c0c0c03008440c021080482c59900340d070000e0740c0c410303410400d040a20200c0381d018030503603030740558051007002e082407000447d07941e85030041c018500307000074104c821020034420300c2100c0280c2080c040521074966103245160051030700b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 677049667 1250 677048417 677048429
    0xa0503040b06010c02090601140d0e03070c060e090103060b130516030c02010911040e1f0b040605060313060203090106120f11060415080c07051605010207060e130b060c1501 76
    0x1c0c1c107001910540c002c500e95100b485c0c000e03000101507603407400113540412400914400c1c07280c061068075614401c2e4080d4285141d403030303c00b664642c1c1461511045110141c0c001c01c003801300072200030000e51903182e9042d045980200c0d020403120503260106410300380300210a440c950070300c42048802840440d40590b41c11481e502004110800103003207007200c08182006242c414102080d980c1480d29400940b51403848005640c2c13072150f0f2000d0881d0740f000342041180c01c142c5841400c0b42c0c03450140f048200a00c015120b452070340c5010444000c2190245100400d4940c1c08000b2034681c940960200e405000035012035508003d41c1d08110301d008007802c3d02250003d880310b03d240c00c10301303004050718121070081680ca2550303650008141e41010004000c40a200c2c41132120401058040150034104004084c001100c241031138002030a1103a103070024400c4c0800d4100090594a41c951809000a1031200005a245e117010000e8050301c40e403100d1001c50302c10070a1103102d4030314810380b00c4d0403107c0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 677050917 1250 677049667 677049683
    0x501050117071d10120b0601020706141b0316080904060f0503121e0d05070807031802060309070506071b0602011401090c110d0f03110708030112080d020a050304 71
    0x1108201542d450840f40a501c01c41850000303403144031860115001e40010703103000190380813512418942e0366401c041005860702c0014200340400d40d41c05101c1a0302500007403610302460300386901152030521440000340c40d164241804d80d02c110005005443c0301070398124882294202d2420300d4001d80d0010b54065118a02c0c005000401c0600440c21004840b03001c2c0141c095400908a010f04170380040c0c540340e110190024842c030000814000820700145203800c00680f6040040000340001c1d402031a107000c1c10300c0c010500b652000c07144e1410710800d81c121200c1e640c982d42c422034181040515440301d030300140302003503000403c0039038190851682078030806400303203503980c0108a081e9404103070040301c0740d81c4d800014001d924440d081010307915014101180501040e00c00240382242e02e00c0d4040c000307071100718200c070005d40c140285400c4550030740a450408100351a41c020f00e101c10b11440181040140c00c00c404c01040b41c068811449400c45e0031034542c01c030100040c3c4164030449003240c03941 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 677052167 1250 677050917 677050949
    0x1606030903020f1606050c1606051207080910021e1b190c14031509031b0a0c0603020a0212040f03110405090a080a1206030c0311100503060103151205010501 69
    0x280700180041401440500d41d131070b90380c54100140c0c1e50b07910000c1c0c848501c0c0502003018021f10760b0410110014140f5035102076a0706481c0d20011301901001d0101c0c3c04122602c401c5c03000034000041c590f8010005c51170010303945e41d40402200300043c201c1c3c00403030414201103214181440e1840c5151000c40803c425120000025000c24014141c0414001c008d2403d6200510603604008400e90f8407080c05403c4410090024a1381e0281401c110384100c1c4507800002c640b0702e501e40200b03041c0f0b1100c0c165001000d054130155201e1805942c0307802088209a0302182c01140c0e54420400c11030700c00c80301d008455555803118061454203081d400251080d542c140401040c5007094410b031840b44000501910503900035548140d0070741d00c00c001d84030800040881940401c0300a1045034000d51080000e010480d25514244c040c1c111000031240c030400360000d03415070b2260000100c80d4804400d203400544950040c0401e42106035079000784030b001c8084d0b00000200041540410706841040f10012006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 677053417 1250 677052167 677052193
    0x3070b04080d080f0c0a141303210512070e09040501090c140d12021204080105010f0506090a0909050a0b0a14090c0604030308062103041701050720160603090302 71
    0x719905484800a00000c000081c170075010803805403280c4842c43c60b246604d5100d05952400d9078100e0b1300383c1e181c1010607090801c00c000c100d54013060501c121300c0411800307210044000d8074601030510940d508003d108006140580700f10020f2015000042c8480d20314149410224000d080d811021602d10520003008944410800140c0ca60400c4c02804c03801c0d0341015603070300c200c10011070844005522a00b0101400e6042000103040640040000000c007980341086080060005a012900642c4d04121807020340d01c6010702141070312112513002ca88080c81e4130b4074a1030024144005440000c050b000e020030703104142c00000600d81d480e003100c241e81c0c68103000760352a181440b00113a80100200000c000107801104400c4d40702000414245100d481e50402062070b014a40204c8007640001509001040940c80f0f8401035a190100812003450709031000f41c503c003541c841c0d110781402030061000580311308100304449042516040d403800750351005c01902410f440102100580110903400540c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 677054667 1250 677053417 677053427
    0x50d08010e07030207170301080d03150506030606031b071109061225210c21030c0f0203011a150c0606061b011803080a020a2a0203070b04080d 63
    0x140c84a5481d04040c075107031110150002c1d440a001103c0090b800e81c0c60042255401c00a10b0091030300c000074280c20f03010780078024104d078030511140e56400e04126041c04140c881c5016a03500c0581502e00e507942e034440c0d40010b201c800c4512074003c0c032610001074140400202c0d002c01c081644068402d50401d8484200300710039410004d2105800360704c51140020000c410f222550020604a19a45600c0d503d130429060398102c44400344020340c1c0d80c50008810841d178050035500906120088009200c00c62072185000c0030b4150b000740801000f4141c1b075050007a000303ca0042c0766402070080040c0e440218030044918100389420380304401501d442d1090405d5081140c0c48024900003800d0700355074481c100300880e08560040c40d2815152444c00d4500301c0c0900c81c8081d80382200e40350712005642840e008050000041010142c02e00500c40d01d0b07001a00201e881d000c205200744c8803800136015000c0d0412144400b800a940351103600f40004101002a009006075040c1e4019654000500d03081610 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 677055917 1250 677054667 677054669
    0x1b0611131d040303022101090c110a0c060e0a0506030a1406030c01020a0b071b031710030b161202070b18070510120207142506020a0618140a050d0801 66
    0x103100c540d200042c0028400c0c1e0081a450324200c900b42102c0a00340316800811409810500381d281d9584003000629030444400854030b00103400411590b82940e80300d0b40c60301c9013441040288004c17450314060560b18652480080d01000d40065120b01c0c1607440380014000300c080c04028201810081421401c010450049200060300208100005560342c0d800c2003a00804c504108410360510303400c40403d00c052400142d005c1d9580031030007042e1100444480c40c001c0d102410a0303062807000c000043c0c1880d9100c2e0700200c0025014180500954240d501e030b028410f008a01c188005104010040020706060199942d540380e00150008a0b180382d0756540103014142e1301c5404a80da00003890703c102e00500703c40545070320141c1484050f44c0c0300c0352555520340c021007954102a2414040c44116140c04451024481c10034500618142c4043d40b51044160007405060300d8402443c21560f08604a00b680c0d40d000c9070484240e50030050307664503480e1411086074980181185460481c1c4616407144c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 677057167 1250 677055917 677055959
    0x3408010b061c06030b04050f01060b03070f081306020a02031e070b0402061b06040c031109010b09100c020a081e03040b04050d03030b090f0a0c050408030405011b061113 74
    0x14079100481180382016190740c500c07000003c0d00c2d004044005250031581e64042c501c204001c102d1542c2c02d51045095540b0790700161000c0e2014002c2000703007580051610140c58480c2000e0b41e90307486030380d00d0b08640100008040c144c01d00000c0c00140403a40003005020070810003009943c841410540003070a4410344201400c0800300c4c1e0003203000351810358000d00506c160b01809141ca0000c020002d41021300854041c1d8440c60140c404001b480a00e803000c10f0380041c11282d80c0c00c03960500304480704070b00861022a00a28254080d082c4090081c100220340640044c12003108661b500d8100743c3d42c039030940145c01252420b01c05040201000420782d4180d03101c40400e1818217007014140550b00400d01002c1e410140c69548001158882180142c054440008240303014a4030702084025607001100d008104801080200f010382000b00540301907510901e00306035001240c03030300e0701c3c200321500030080c00c883e00d001c802001c0f0242200042521602801d034150f02603a175240382442d040001e400725 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 677058417 1250 677057167 677057179
    0xb0603090c040e030d090501060e0703050f0f060a03020904061a031912090909050c09100602070506070203030f0a0c1109130b0a0e030c0c09011205071203023408010b 73
    0x4450341d40341c15003040c102d40016404036820038940c28481000d803013a55001351581d03591480d0034440000089a5168482d040e41014041c60400c08000c3e03403140c0c8001e204001c0030700c14030301041495a0b42924a00155001458204e49040504242e00105410707441c107103481c005170401040d141800300d00114080d88540c0982030a0030a51a03a01c85014041040f0040007250040407814024510030703101c055000d040200381003802d110030f10840c10341c09403c459413001181030803c0103590014a00054070800e07940303103449003c2480401c0c81c50288a158600c80c035808107040c100540d0081c508032045000340d001140040594003804076920080d902e020002080c0c1c2121400306d9250104141c0100c5100000500104491200e50842c0c0240324103a01c25004812080214608140c2a0b03016041001440c040d15650ba030fa41c9030742d00041d02c0703042061043c001581c400d15000380034801c01050380b401a0410880d80500583e048840981450400705444401080d40a814402c04280341070180c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 677059667 1250 677058417 677058433
    0x8030f060d0b04120302040306230604110f0d09022e080f150312030705040f0509010803120a0605090c0301080d0f0906030b040f02130302090c030403050910111c030b060309 76
    0x80c0894107244c0d090508185034003000b00100003405440b80100c40c100803070240c0c01030382030040d0220030403038084d02c041c1c4128180070b01103824502040c112504188185120f6a03540c05032600c01001d05a1098043c5d40510f240340b002c00d511403001d0161010200900e0580003414500009a0307101005640101c00540d0040008042c0e820b000c0c00c60010003c0101103e00e82042101060b4907a0700807a06000068008141004180f111030700e110007030902101e2010843d8106840103541e4000c0c3c0450a1480c1c0d070782404504d14101543c8403c01606010300421094500796148201c641e00a2051446900c50240301d424901e2084c400514a0b00e440e41d542105d442c60300a0031006400e0983c21194040d981c0c0d041401c01d01c01030f200600310b000301c00444101300d51170750040218004000300481c0311807d040080000083e4400c0c02c88000c0e0b14215290841d8451150f01141c140340700d181c08403d50b00c0749100503186040e01903007040c62142540c1d0140a40303003041d0240040c40c00300f95040240ba9100c810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 677060917 1250 677059667 677059673
    0x20a050a0c051e030a0e0a120f1407080d120209010f140c010212012625080f0610081b12251409010302011b020303041208030f060d0b04 60
    0x40a8000940240112004102d400342a10143c9001d0400740e5450781c000140302c000380c0c3c0c0060f02d00750840c404852040d0864601860000303c1c44100000410300c040040982003080b064903020380d030388840c071000c845445131910710301603032500325448200200f484c001140301300710014021102c80200681d1080c401014034007096400840980c88401c10450070300084980d010248094801880150030703c07a00b5525000c1595140220f03d100c0503810b0250010350740000c003002540a0390b41082c0003030b80d41c3c00290388521f01980595a00808068000c0039010071a1203c00504207008034a44290881c51940e280c5049903150610341102c0c940900c3c040069110340b601c1101000b400380b6542c2607c000781c0188500c038940100240318082d180c18061001c3c4608031011540e10b009041c1a641a146941141c0000e00395449480304c0d503240ca000075009a085440900a035401012104021104400e0314074004400d50421034200301d1880680b80020041d20b0300b58103151001d40c00c000c1e440e0540e1600d407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 677062167 1250 677060917 677060927
    0x31e3903110c101401050306040507170304030215030403030b041802151201032414060609011202161a0127090b010b030a0f0b0604091e0908120901020a050a 69
    0x3842258180140032034050b010050000100f000c84840c1c000440003242444c54505000603040503009a114004001c000b600014011042d508403070090818080703d056514a1403090740c1000b50403e0300191903840d2411510040c6004034401d8034240306401c070034000c1c00104e50a00356200494102490701c1405402d140e0088134800300c0180119242203800602840c0c405c400b0b900c202d4100e100c04400c1107440c1c58a2150002a00c0006c005014140180b61010107519000e01494480c04c4000b403240b21a82c054401c03e000109452019500c034030094042d052030100c40c00e01521200451070590410251121120341a21450050700d04840381d01c0202140080d000590a040b4668901592001c0303050080e1150003086550070036981d9107002080380040d694810303001c9804038200301100005544580c142c034143c80340c40d200001d80c011140f00200c011003215429000040c548289101800310500052800d055402d001e00055101c0c038030104c0c00c034859541d00f0000100184404580b042c410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 677063417 1250 677062167 677062181
    0x31b1b08100e0705041a1e19050d080f1b0304080f15010b130f091a190905100504090f02011e0e040209012d02060c120f07031e3903 58
    0x10b1030021100c007080d030001c1054040b840908040c0b42c00c0c7e06c2102401842c0044001d80f00c00c1896240780d121034605404600801a8514010400d039008200004034002840c20744068400a5010310b00346140310789812303140c1e405400b0320031086c002c2d07010307640d40403030f001a4080002c02c0c07210706c2c0c416981c680100c040303480c0c00124403028050300405001480180a80040e0081e25170380c64001f4a004409403402c40904980028034040e45200d1950100740d040a443c03d003c440c501d20300070a42c0daa1b88440a440342c0d071310381c0009d07a20514009100041c0900c0b00001041503100781c03103854100c1000c4049050807004000600700240e640742044205090940144c0403480042c1030440c500c24009480c4011940039400350003c5801040250385291b034100b000c1608403c0007604145030590030001840c03041c0000b0400d050f80565030010032801442980050b0701d1a6041402c4080189100314990141902100ca002c00000c0c450b8100800d07010a401c10b540d407040400c1c00d1009000c601403d4000d403c40c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 677064667 1250 677063417 677063441
    0x9102d020c0a0317130b06010807120c020c040509030405030604080703090f03061a010509060a050c0f241b0d0e0703020a120b180307031b1b08100e070504 68
    0x9000e4202811000c00968042c54481c0d01c1c0c02828403401440701d08500c00080c41030f03400307942a40824001c01d4058040540042c020b1030303e6400d80e558004e054401071024504041503e1130700c80011803140d40454041d000c01c904450502c9161a09200903641c2c0c01180034060307258200801050010760701e4001402c10b144242000b0b0f01507551690000d410b81ca5503401500e04a4441c161449102d2942005011100d801d00700503080c586504041030709402000300c44400e10400248503403c182c8104004582c032605401150304040b406031404081c03035502c903900c100e00348903075010500ba141641401d41c03025104401070b90030301c0b8a464551002d0900103a926040d4010403c021000d038030350681d0754015148800c07249411079440c2c40c000c1c0d042070b0010603a082c0c54050100c1c403820b900e0040125808550145400d403011450f0b41441c400080e03642e44000c0054514181941d10107040c05080d500300d60218050301e140b500a100200252405054042c0702a0005441885580780c03a5100d406420f030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 677065917 1250 677064667 677064671
    0x2040506122d0d0503090c040504171b0703061407030c0e0103020a051909170a020d020f03190f060b061c0e01090f06140106090e040b06040f0f0509102d 67
    0x21010000c14103000c0503070031043c0041c20001c204030b0100001c20009040352000d8030200801e18080d21901c070316002c48030310790032161000210085407000081108602041180a0f900340d41d03540c0c075000006103150705d00340d0300c410140340015040c0d038001e01c00c02212040c40d0b281d6204004042004400941c03011b101842402024001d41401d0082002e50314401d10301c584030800d006041c100071300d00c0c603842450b001c0945d0b0310803448040182c6590010a8905034140c8581c0d090001c43c100007818000391031108500004c0e90511002070205203540500224006e01003000030500c500288100f501c54460b00d080e40814040b12003518140035805a203600801c81d000103000d2a40f507071400d501c030079441010b8800545818840304084c8840441070b00520350fa04100270803514100850100000040c409003580c02100c0002c0d5082c0c0722a001240b0216004400700556200c01a1150051905440b02040b0381304540a0384c070401018801c5902d804400c0001d444410302460440000780e5101d090400096 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 677067167 1250 677065917 677065993
    0x1603090b0709170c21010e03030c0702100306050303091e0d06021903060f0308090307033008072709060b180301020711040f0e060c070204050612 64
    0x54441040d0901400c000d5035400b02c0303a0b140599181020040d000703100855040541c40b1140b41d55548441c1c9140420800c10101500c0741150b001d006299495011959002c0081000b000c03480c0c940040003c04d108035868000c103000003c3c110100e0340c0c107000d6590568005c0151812502d09152022960031003004020b42240e1f50070041500d0301302d4200d0454089402168019a0b41d5460314003104a8550345010046070349882c0006500c0c606500c00a0f200400018816209860511500c8042c40c0c06c5011007510079040d01c2d4801e0f0b400c0c1c1c0c4c0d240d5488031171026a00000341c54800e04410303000ba07840340d036043d00121151a4040b0000b036015058801e15000e11750000307a0751403a0107403c00078040d202403282c8601560711400410303101b01a810344a40d2041106000040042911052810041d10f001512820304a540300003881d100b10341300d402d807007140300300b15036003940d0300050100ca8401c1c2c4044c022500c072003040c00985030140b4800c410f1a08560500e0166115581c6e20b44c44c0c107111050a14406 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 677068417 1250 677067167 677067173
    0x501051209100e03070b010509040c050d051501030804090c0c0c140a0305010f0902120708031801230a0e01030203090706081306021809013602042102120f06160309 72
    0x50380d0f4580c18510a0300041000401d020070060298010002640c95580d145403655500c84600322074010f0074860300040c00e440f0306010301007010200345500c0380c0d030301691561241004002d58020744524480c0f00d041c40c0710070582e00d1007844d405440c558810200c484031030a1100e0401c110a610003402d411030003011002000c2842405103000c01300c242200041c0c3c11011b40140324601401c134681e05040c1e0301c100800c2241c5c40000044a1215001c0b440d01c0548101d52001200d018000700411414003400044800860350314900501c4440c0039134580c0035107130042c08015400d030300040b00c80303881c241c01511303082044500030400140cac4014100b400030100041035841c40f00300d0304940c007004041c90702c4000c1c1d200756040002d80d00c0c0c050165640052862001d0b0b500c0c0100b0311411034104400064800c058181c00c0d40356806480140000407103a00401c00725011000350200000ca0503841400003c5044000c10404146c0e00c0f4042c1026014185960381d02c0020320095070460155010550354034240408 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 677069667 1250 677068417 677068421
    0x60f02100f090b010506120f0703090f03110106080a150c050f0715061208160503042310030615030513021f020c0f031e151f0f050105120910 62
    0x24503101c00012510850b00303042c410407905800441c001c44040254a040304000401194451011500800d0641c0d601a003280a001d54100040c001c0ca1000c003000700f00742c2c0051014408003c5c0100801c03402d603940862981d80e901851025289000d41c1c0005000c001071074001080141450070311501d41034002e501e25049030b014000aa800c0c95982e40e40705910203042c05083c0042400680500544041e40c85490702c910170100021172030410748444100f0001d0174801d590007000c00000106064140803100c0c01210314102c40c10344110040303501c0648140c000c0c400d0005a4080d050101c0230302c8004041a00109000380810304100d000004281c0140c1d654000b0417100d5484840d050414040100c0180c40d0a888080251080060010b80890ba86002440540401c002072141c03040c00d60106507641070007103401014843c103c810b403c00211020160203000f003290064416400c00361350300d9200d40b0140642c0a400d00207602044001031a4003222a45a080b03e1032409035154100d40d0b00304001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 677070917 1250 677069667 677069681
    0x19050a080d110c060904020715020d09061104030c0e0703060801020a0905011227030e03010f0c0f02070608010b030702190c171501090908251416060f0210 68
    0x8031030381c0800c6a01844992141c614899100c0480007401005600400190785004820b0364034010369020910100303002220503a0442120040c008659401c0468485405840741e0b070400e031410750a1012400e0340d000c0301c1044904807604005a000300328200b01c12050700d400007500501c101500e400012030344a03800c0c4000d0143c2a8940c445903c0c0e14070746000941581601c0f448102c2d454030704070444c00c80c03054209100003030030130100444201052510741940e441c0c80ea02c421903015860580305e40c0302c00100ea40058404840b40c0c0b1000c4510340c0d900b10807a51400903008501c0000e030160300410820508202454004a0701e0054854009501071948482801041e0569007546104401c100410b45201c2d816540310050000d42130000c0c295840707078102007040c428420460766980488080c40303e83c00541d80014090f004811800d040515051480c0a682e04162001d24090b07580261000000070700e005c821007004080c0317415924051040da15840300a402c2400d602400401d08900085407203050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 677072167 1250 677070917 677070929
    0xd050a0204020c1608070e06030105060a0308030a021b03031e040f0201030506060405091006090b0a0e060d0e03030109090b06060301030203210f0a020a05011d060a0e150f070f0206070c0219050a 85
    0x21031061f180c00078240008002070f00c524020303490082072184548942040d0810b030f94104069941c1c0303490b8050712000a01c80d002c028040c2c03807058a021451000b001c8010f602a03400380c900c0e0581c186040b82e140c1c2449009540007020149580ca82c2030055000c1e070446d65100c41d0081c651400c060b9943e01150b440c40088844200c88134036510306021040d0040c6800000c1c202c080c0f481400c16201e040301404240d40c041f41c4e140305000102e101d0b0740800395030700040d040d01d8400c8181c03516940d41e0f0300b1030405415203404c02c5403051404400141941042070a80b412a90002c0c02801c01440f10100c10011080c02d41040011303000c00c008050501e08014000c0075a46c1d21980180809101402c0041c00c44040c0c4180542c6440307007145e844d40e241c0c8009811900000c03a20000140b0340b5405098500e02101b010ba003028082151040064001d0308022043c030840e9203868481640c114110200d0702c0380c6003295000c0c00308000b21420800350030046c01c0011003400c1164000d0442d6201c3c2c2c0025080300d96036001c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 677073417 1250 677072167 677072173
    0x3060902040915020c010e03040b0d0e0c0a03080a03050601230304050109140d12060605030c03090c0a060306170d080c13080f070503120a0807030e0c0a0f050f0d050a0204020c1608 79
    0x40c4881750702403140c0c85000c41e050014508003401c1401034026441000c24810724076440d141058589041800088100c04000f410000842d682c0d14103030f240e03904540103200209180c500010001e50280b0081c044007509418401c1c0010081101c034207042c1c00103803040d0b406650318011132000507a1103410f0303056402020020101c048000e075008040d0300300307400801d890710b0505004203c0b254001069a41003900d0740b9200d80c030303652007084c101d2030035120000c403a0b8001d11503000001c03400d41640c400701c140e9201d41040c1b11410f00442e40a0368483d03003880681c00140b076500c0010f040c0d043c504081c00449070101d0004e10480e986510342440d041c1101860b0003950440e003000c2145c1d00c3c040104020030f41a80382c2041c28010a11005405c820008002505040e15840e00c200005001d200142d0380c840700428030603100d6290f040070541c61100e070203440d000ba10002aa1031451070410040c0380195400401080382103c55424800603400c8009040210721840e110007503400100481440506400001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 677074667 1250 677073417 677073427
    0x140705190b060a091b08040203101406010f0e0d080a140408010203150307140f0604080d0e010905121002070206090d050f0601140303030720160e0603160306090204091502 75
    0x2c00040c4000d55004c40e000d5843c0890281c2c0180860f071411600780f0715070820352840da441c1e001080c00c0811403850a01c0d000d1814080040c9911a103119034000c2200382e035043c0030100c50000517a4000d8049441a0703014a204004000190801001302401015464884845403001025001e41d8001ea0842d10782030b500030003000b03040d0001119110300c1e10003c03001080b50500d410031140040078200c00b603d0181241e00b0404c00941c50f940c0c110340003820494115440e400c03102400420070800150181d00140c424500042d00b8500101200040403d25010341020324040d011038000352b11814089821081c103001206841da55800500341d00c80c05030024003060701e00c0314001818414140c2080021031100c90000700035480000c283d942c40107141c10410500719044500c1020101c900038503902e02e00c1600d003250300c1540c0c840104030483c0c4410314168605d8035182d003010f4550340400f41c0c000c2410304044040005c1040b540120030500d0001e08000341c002c6094450b102da81510800d04e58601e900014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 677075917 1250 677074667 677074669
    0x12f1b10110403151b14131202010f02061e09240406060909110f040b041b1416120309020301050f0906060901081b0a05130501080d020706140705190b06 67
    0x42c00d024040f01c500700400172601c000450202200e20001c5000c10020a03000f007010314071104045030114044a028401c0d460b5a8814984444603a01c90072030016071010003000025000143d95070056407c1c868036540c584c4a803154001c90384d030082400304503114485041ca181c1c15007000f00104807059188189561078582010300503a4030a0303111088040c9000c00d68804214814250403450004484450340c2000b00030015024050020500b9402481c02175101d0340c034480901310b540c1040c007684504849590529518065000703079001c1500746c0f240c80c1c0e880c400003960306040c4280e0080b9400e0005070744101e5000300c1c0c2182d0044520383c21214580060210722031007008019031028048900722519810001495100e202c0242c0c10284a105210480349a564a02c0c000e00031742405040e28103004c034252b594a018003820311982c012401079142c251003661012078000c054858030f803500120f9801d0120b84c000c040d1311040d000e60713141c001c00310217040501c2058007030f40ca203d02034003e9203480d050400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 677077167 1250 677075917 677075933
    0x5090a1814190e2b1e0e04090f06050a1b050414120f010609091109040201020a110d02030a0f03080f010e060d17130302010e19050d050307050f012f1b10110403 70
    0x1e10901012040104090002d65001c030220030b00000c07c0d50081014101071800e145c5d4801390140c0100b05c07c2c18402044007035100c503444800000c0164000444030f040e40b20050310284201c0c0146d181030398913021040c0503820090040740b9a002130f00211081090107030008c1e030031503500c1c0c0c2103208941d4480648009002031031064a90110003218900041d08150380040d55401c1ca21400a141c1141484807503005c3e07898551a0415503005030030303200480c900d49065812004454022804240c0040100303156906042200b41030b190300008030980d80d103030081040305038403201e0320485071080301002c48550300c0d107803602518809204103a040b01c0c8a083d8400176029440b084036950060892241c0d02d10303591144445d003022104241d41d1507c10400501707140e802c612400070f004d81680304030004070703050800541c4071240c4035804000b0801c601002c0b07000c0305800c0171a5650850400c03014049400c92030603010003a04410f034000104c1d04034007108101c100c00e80700403541143d042c0d01c001c90704200f400302c29 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 677078417 1250 677077167 677077187
    0x130902190f1a121602030d06060203091903030c0305070203031608090108010603020306030a06020f070b0f0a0f060b0712020f0f030d0f091a040305090a1814190e2b 72
    0x1207000e04140c901030060380f8407400213100215221003155034041a0b070003070084802e880c1401c8418050300b41c4450b800381d0703a40c0c41040782e40d009448031041d850000c29420654802d07a03078150b880c070100c2116a1011205074010740c0040c0e038980420442415030b8814161184401c920038041380c0d07243c29203403001410b1000140d00890600d401013080152070307980460005007240d8800e0005072105c5484441080500405900030205640103050000320304201100a00c500640d0505100f12081c00b8202d805582c0103204079a82c102007885000e0010300c0380000c00b010001d8510450305649458600790340307080e51039045980039400014002030003441501a405248040c00024456000c103640e0f0700b208460303c020b050342d481d4569400301d01010301c2032040300d00a01000300001c480545500200d0f83c1312001410941a0500c2c0511440c8500c0203244120301c00c18803280208485008080d049001d0224401e40c07808074002c1a0040c00c0c85e0b41901106d644415058104200c091100400500300b1000c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 677079667 1250 677078417 677078459
    0xc0201030e0a03230f030702030304021e010c0809130f0e0d0201050402180c120106090e070c0c0b0a0e09090303160801350f010b0a14130902190f 64
    0x442c41ca4004680c021003016045111011101c1103030b082c43d1060480c5019030150400240760000911180c40c2d07000002c1c50082d80200c916802d403009803864444015940e004d024041024940c02c080410300f80c0003d45142c100c00f906070340c80c280020888074101c400c443c04400000750b80d11400c8480520401c14880400e043c0c0c00200000d08003600000c0e05401c852000c09001098000000c60420101d020384103030b46440d112200003542c6a001c090905000c90140c4000307144070400040c038191052194110940e00811240211410024070b2201c03544112403d500740003000c00480c4d002d440e1080241e108842ea2400342d5140d007084258600c0c00c840d01600c0404200c00301006100403214104094001d020003c51a4000c2c040c1e448521039103c540307080c1d100f4034018030300044503201c8107401038404550101c50f003204da03644032924100a402d0b01580f29400894101034021901040d42c042526640024030110480d2810034408004080a4002e80314038503040d03408011020002000e0103100c21 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 677080917 1250 677079667 677079673
    0x207051f060812030c030603010b03070303080603061b0a12111809092e11040303050a18120807050c060c0a2904060b120f0d0e0307060f050f12070c0201030e 69
    0x42c0340c8118425038000505171661621001000c200c0c6c980e0258001d81d41082c2c042c0580e0032850382c1c0d003000b824190049a40d54040d008540000b40254101011a004600307048412030400800702001c0725183e132240400b5242c560b848a280780d200320803102070440c0440860701110640740a1042c0b001031403001d071050300e00d076014482514031009036070b03107118241129000c913400440c1000105400380280d0524400702c0c0800180200a16074404c00410042200d07460352000b800303210701d02d2a031500301c501c140010b5208006000c07001403014401800340e10701030310484201010803c00105180d1104810052603405422010704220411142d0401c0c8551345240c3c4400c40040700c40203010b01d0f801000208104d0744c0e281c02c40010f41c2da1403461084000080104c990304510300590550f19010b442c142030210f40c882d15184d4142c50300042c1d0405460341c56845d40010074003e08203640c10741229000041080b818400c9000c00da16139581c1c2886044940d590440401c136600015040790f0707480c01800340300d0b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 677082167 1250 677080917 677080933
    0x3040305070e040c050a0e040614010303080115020c040216020112020a0e0609240d0e0a080a03110408010f05040c14182707080607021c030f0207051f0608 68
    0x3240800c0c0081100c20300c2500a1240e80d80d0300e4200c00070135198006650140c001174001c42c020080100ca031344224800c0300204405198246007200710542440000c2c00514a0801888007001c10f49940c080d8013150b0040300d52100100001600340e030851442ca2000840c602d103030b081950f034890a50410b8940d0200110315100c80050018101c2c0310740104035020b0b160020b42010309882e204192000c6090110540c0c490300030300300c0443d10990111846004607820405c10030040b07180410362a201da540724443e903140081810040d006080004400440c5607400d10001444071000c0c001d9017251080d0810000b090700e01840c1141458220303412028130400000150760460301c810541003800342105000c0c1d041c990711340050343c80f1119010610101d4062a0034012681e443c0001c0030025124102c06444540d61080c030300326075400244056991640c1c80000854000d80a80d001c00001c800d4160b02500c1d00b8030315198140b03050070458640c1885400401e0b964100c0c3d11038420500075003001c0740680102 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 677083417 1250 677082167 677082173
    0x11150408030a030c05071a06030607030c08130204060509100f06051c240e090c030d2a0f111519120609050f070212030f04140a240608030403 62
    0x280565030002d424141d03140c0521421501407000c3d2281c10307038070450070035403104600310081d010001a54024001d00c1703008045076070f19009001c3e00007403409580e988007955603011840d1500740c080076000c0c4e070090303a6003101058984854842a04c5092030202c07040105280004000301e95003181c0c440380c1005000c1c070200548140070400e10013407405c1010086004040d400104d40d100480d038100c000f4003000058000f6441c4005000030b4442c404c079009a42e10721308660280340c0c403130b8080541c80001401304c4a0310058414086007007404500c40078400d4403031070810758031046807a08524098680c01100c0c42d031140c1e145000c441c84252240c402c0b840310b04264000a03820b03c00d800c003c0d01d83c1d05005081c008104102d0040d030211005100b1200140840d090444075240f17950000c0d103c240050243c582d180381401e034002d003280d00494007031001100c0c65035161514070325441c0d604907102c05801059920000719135042141d0380d40c801421407403040444806a118100e170003581c045007031904240020404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 677084667 1250 677083417 677083423
    0xc0b01060c12030e2805060108010b060324030d03060e150310020a05070215030f07180e0c09040608011b08011401030e03070602070f060b0612070e06130311150408 72
    0x2640d10a04004c600140e555100074203040c0700d01c240c0034008800340702c04800641107414044071240110240d40c2e65980b244510750988140402c0140c12075410404900b02c034062040c0c400c07103564203140c4100041802400a81009075070140c1d60006602c40c0300c14807030341040b5044a50002e1545840340304250b811000302c0d0320780c040c91825000c5a82e01103410780c05a4000c00403511141d5004003010b8407400440c2c0f0380038071504165100f104c42c41002d000a085076004150f0161002e28980d03102d8803052a00c990060914002000092034200c20711580c802a01c42e8016600036000003800403a02c2811002c2e8005004034000102c400c02c001c070307070040040e07606041d850700c4807507404c1c40e0114003000d5850b41c1034990b00c2440c0009141510003c0e5003030501c070305481c441ca410b5100300f00c02d0060100200411155018050484010210150205514501079031034228010006041c81d030508421415105031501960700070b40e44881b8400781b0860511704a48680e00d882070032822a8146800c007204555 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 677085917 1250 677084667 677084693
    0x50f0412110c0d12020f0f0c040b010302040b0705070503010e0c0f1005040803070827030d032004090902040b010f0f050f130821040b09040506040608010c0c0b01060c 73
    0x306200c16040301802140c000e00000c0ca42800240c0040100b040c00d1514401c0c203140070404000600402ca02080c03071080216100210260742802407034600c1b0044100001440e81c0408941815801c100001c1ca02180001410505000d040a090300500d4481850309562202c0d0201c903a0ba0017030008007031182c0e00c000c0791047c0c4200c00c0e01c0c0c0c042c010307800100c1a2058815500b02c88054030006c1422000c02c004600288404501481007200c102c44d9910030321000304000c003100d41c5c59000010040d030000e200c0ea1269500d140c0d08040c22180400942a1700102e900c642c010f00242a1120512000c1d0b042500032603650050a00e89001070320409200180307100c41540d003210130028000b80c2000c070741c10030b2415142201082007041d03405640c0e0328001d555070b42d603000c400e41990586080d66221080e1103c00e03a4101e6004036026880c020f6208100f1008000050445a000e83d491a010a14210910402661510075211a4070344651401c14200000d0140d001760f0400419034a1000010003c030340c01c40c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 677087167 1250 677085917 677085953
    0x8150d051f05011224020f0301090e0a0b010e070c021c1b050a050d0611121f080d030c0201180503030f01080a02030703020907050d0e0606040c1b0f14031309050f04 72
    0xe14101c5c0d030075202030b4030384003009891850107002085d040407440e103040040d0304035041c4800c200841402840020748400301030700d01034940d100020042088801036160b40d0b5200b000341c40c01d0805090198005103079007042c9400140c0342580c0c12164000c00c4800e42d46800c030880c48200000f0f0003450903002820a403a41e026150003410607200903030420015030811030079214500701d000d4448140d0b05107007009020031208a0351040340c140700030000c2c250401090b000c1d14899405002d00d10040c490940c0a070140e200414115940c1d0b03000d070940c10900c039413280e40c0700f442040030310f6803424500062041254181c2124000c0d40140c0094401039400294400842e90b040d21034881982d11680c040c0e406004d20302c0581003140c18884041804003003c59200e2081100711401c01c20000c4269048a07081c0034410040d0206614202d5100840c03090408100901c0c80786020040c090840f0b00300310f007990020035148012840048041c04120981e0040580c0581d8032004e8078200d24194880f10140005560a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 677088417 1250 677087167 677087183
    0xf1203090d0309030c061103040b0601030e0a0219050a0b0406032d0b0d080c07030623130825050d030912080606090a03030e0a0509090a0308150d051f050112 69
    0x94101401000800d1171143c200b071042200302e41c0b01e10504203d038811142118400c403c0000030b0010760091007003241d402019001851039218a0f401d1240300d14440020000001c10864009915507901300e11001412107850f980d0b880e68a41031014050ba455160201c2510002c501c031400c842c65002040500580700d640702042680988001c12215a1200b002a051120004180da0350150000c0e1410880e8810341c420000800c04600d0290f00c11a8100d030000000460070200c0c400c3d40c84d101c509400d4a024000d00c6280c9929108400f150504243c8030b84070b075089042c0200c05002040c0303d8000d81c2080f5040038411030503260341740019a10382c00d80f178005101008001c50710035143d8002352401e82c00c0203051094410348904000e0302101c194044131303201d210040d10100b098241749030f803180140301a038000c12004040f5074050380c1e03452006007544417621800002420f20354824094014a030700071000707408030000c0706d00d0014156640e0000e00100b48e040000400045624404002141d9001040c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 677089667 1250 677088417 677088431
    0x702100f0e060f0a08070302090a050d020f0d12120204031505040c0506040b04030c0b09060a050703030212010608163f09060203061f0c0201111501080f1203090d03 72
    0x180d8401d44051079968000784085450541c80f80d91a0041158035101c1d104c01e015551070a0084059100e174004c040c1c3c010214441c100603608000c250030344254402880340030604280800300b8600c11241805446008514041c0c0c50903e802c002000c10440c4070b0001540f8050441d255401d0703c00d609072910f00d4555440c80003500380003001402502419004003526a00e2740e0310500301d203650b00580015952003001c000006140507030f402c200e840105010340810708244203500d0a0350b0981007514140c051580800c01280041080364886020b00782c203449012441c01c1441c80500c171810990030300b106200c4030040700441d8865420080d05070701c4901e10009200e4214400c2642c2101b1182d9001d100303181050703204070400440360040d51140300e050744c203500d072041e103c0f08201900c0e1041e412039000c120341141c40790140d44210b080a1500e80b0b54021120500e600c0390180040303031005da100091540020001c81d5081c81d00340a900140044490b1142c250308140030007d40760849021600c0034956102c030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 677090917 1250 677089667 677089697
    0x30201200106080d090803091818010f050f070507260409052502060709120f1a09010c0306050307440715271e0503070b070210 56
    0x282809100005a000788102d5030b68500c0d1503920045081c0741404030b407039500c0104207090000280c130040440180101007040c42a984441040c00c0034145840150040480140034002409a001003c1500c10006480e103489000030200901c00703401c04e820440108240c0b000b040303820f820908a1206290f52a030440e010510709000342c41158410000f00e030501c00ac00c044107038048200e860b403800c007600c00c8481c85040101240c03503400c1118194003046090b841804541d084907055280e40f0310070031200351004130a48580001d42071302e014040c2c0011030401040398080c0207005090b40b036440c0f410300780401c0c0d0909000a4643c000c60090760b4041760200d41e52074680424100c141410080a03000b00203c1c071900d501c94442224210218400c0d2152040c00155129429010032050788560707103480e0820110809807d01030f6002d01102c0301800c141d0030101d00401615114101e000c21044030a90f1507140100381428464607a1040c005204184218000352f00c829140d2040b18120f0310b0314048990707480c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 677092167 1250 677090917 677090957
    0x50a050603061e120a050705090906070c020307030602030f040c08010b0f04020c0102120c04030b0c13140a030803010f050f0312220f1701050a06052214090a030f02030310030201 78
    0x3c0c080ca502001d0b15800d0000c09402040c4249041d0080c02903507100b030f4840080c401041c00030f550494940d88504006600c1da44130308100d0400c0d0380b00800b0349141c1c594a851b810140c0e00240c1e4141515007201007400b0820860383c40e031000034004840244041007040340058000701e0f507602420302550300003900e40740c0741d6029812694449021031f014260303400d0411a80940342c005001c1140c0800035140440c1c1190410001d60b6254503210009800f41800d10283c0b09068204041043d00050400c502100041816000e58040d00d07485002c400201d10f0700042101240004071940d010341c2091048aa85500d0728007242e610440111081c5580410003842c030440824543c840b2440000c20b00c40460600150f42c080d4011125850090080c3e0b22800340c10310441e507491185070307440250300e140c04806204008230102c040450180004640d507044401da03800d1981104d000519801000e0310304101a0000d402103151743d410310003982145048800b6102507142800041c1c1404080741012121088039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 677093417 1250 677092167 677092219
    0x209010c140601081e0a030507141b0307170717070e040f0201030c0e241c02090117010e0606030c091903022115060103090203030c0604030801050a05060306 69
    0x1c1014480c00041c0c0e1140c0070345507403013130051200c00d000c2c0d24081710000952030007582e20a02c0c03501c0a0010381400d81e90941d040d0344004012205407400f0900c2d102c14800500c50f07032169900034050124910b000000b01b5081c6485031300000d05101202c002804060000112038090700c3c1500300745400014041580c0345000181d030701c12100421030004000401c4202803003484554401c0c5c900b0f00081d2440300056031038071550310314030790490780b0309881301928005030700c204403582040c42c072540c907007007101c0c002c2101c5907103610451403403507000141c460683d6841010180c000c002d4504e044101c0d41442044102d802001d0306040c8210404804145139050000490700d242d80300070b01e001002c0707206411070700102d0200c0c03101740d118030000c8000d402144618003401d6078000050020300300c00c20300c1e0030481c550a0300180031035040694031400000141c604000138100607000c003000309142e113028500100005e80503003102d8045e8002c424204030300e4841d2000d4a810110444d05203801c010b915041c60a1301c158 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 677094667 1250 677093417 677093423
    0xa0f090c020f0d0e0103060b16030819140906010f060804060c020c061b0c0108070f2706050c010b040b010c080903161502120f191101050a020406020f0c0a06030209010c 74
    0x120f1080f428440d4101c0c0540d06115400c2c0c0b41480529903503e9001c141b4001e0100c03286616094840074800207100c1c0103a03a074030108262035080643d5107501c90904481c1c00300550030071001c0c003500344140407004008150040c004845200603803400c06600910403680548000c2116445201200b000f500034003480c2c00d1980d0240015454402c207260348038403100344140c0000030b4010490303800015449041460711461890302c44841c0041c080d2411104030110122180c404d00715018144041d03145051208014401950707030546031000f909103542152140ca12003441940340050800700d41c3d0700100312062664001c1161a00d032042400844d090551480e4400c402c01e44224020840081118100c031141c3c040d5070032503031940795951805007940304601d04240d20140078480c0e401e45044081c1c00d10307540800e6180c88036540d05a6050913003500c506440218210f60017090a100740781e070400821a0601071640100004a8214082208040d442c01002c04068002400c45000d9001c0e012114078036034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 677095917 1250 677094667 677094673
    0x3030717180a03081812042402120f0403020603070201020307021005010e01050114090d030518010201020304020a050f0a0e1003121701030b071b1a0c0f090d030c0602070609110a0f090c020f 83
    0xe8070020001071b0381d100e802442000c40d03c0c404445140306060311a005030000ca6002810031400c030f20100c03041600064500710400700c0400011005032142c0011758040d1096400144e02c0782020703c1c01904005111188124042c505001000300c5120320815030b04480c0c0c282481c0c040d90006a42008003072042d082e0782d580242080d21058200b56111009040425800702c4501d0442140380c0128285d200544000e584038a4010702401180307000f407020b806042c002450604030b15030340d000c5840ea041088031104100707026a0700410920031078520514802500345402c040b0308031840c02007844120180405850394500900217200c1c14041c41480c000b0b103105100400f0000340c40e1610700d0000f801d50001912102d40040451648402c2005640340118007115590502c5103d50038092840301492040d030801c05100d804001041081c402002807600401d0045001c1b5a241040421401c26008003809141580810081c161042c0d541406543c1b401c100030883c1102d071641245881e01480f2102c0d00d0780 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 677097167 1250 677095917 677095933
    0xa27120c141c02070b030c0c070f091410030305180118080303011d04021e220e06220215280e0a050a0603090f0503030717180a030818 59
    0xa080019551094401440c40c0d407040e00c200c0800f2a02c60000d03108000f1040800d0000c1014890b00001904600000c1c008031031210342c0c0e80242c07c0002945900c520107080d5600980040401281506584542403080ca60350841c070b0340d64028034501c00d040343c05903540350380c1c9800c0c4246ea1060b006028a80b40114802c071120351541045916a4428071030392181141c0701c0c007901420009801c24511542e0004e21400f00001040c488850b10303c0d0121685603c00d40e0b0b0002042501c2069141400e181c601b13200025552844074030451030108054010000b01c0101c280800c6400c510b064903041c496415600d91040d018101150f0255006801403009600240c0500d0341d002001c45049a05001d0941c0e01c110f1219070718003d00403188d189020313546e08011280f03400d120503402034108001041c80740007405045d445c1511120709541090341c5c0c150008003558a80004d01d800d2030111a042400b891010741b0885103201810360b0383c1e840842c003d0500a8603000980d4509200c21130480e10020074003603034406 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 677098417 1250 677097167 677097203
    0x14090a030b01140307080106031a0403030f020a09080607020a15090206120f100e01050105030f091606030e01060b03010b2a010c03060509070507170313060609050a27120c 75
    0x38803400c0d40340c3d82c020b12550b90001080a01406400112174200030860110030a40f54820313240c0c1002802501450745500d02c1003240502e500c020f0110048030381d50a10303000c0c1040580c40c28884040d0000c002c540c000b4603040c000c22035905080c031040140c6440040c03a046180f020919502401070301403010f00446c02088044050300301500d100702a40400c10032040c1d1100c8061200c581c6c20b004081c0001c1060000403500d440b035058540d00010b000084070446100c0c109207001100c4e0344d80100002070b840f25150582c5000034007502000d40010b81440f0304641c10400b441019000300d04518503c1c2c1102d05500280c4c10041c00400002101c0c0402480000c25001e00a000f40c482031003018010240c085c001070300d00f407140050314141a484142d40f002020510000d02240d0000b40405451541d12901c1c80002074142c072889004210058002c42c05142c00c20313208003122000030f000440da07284a0300e4800d00d40e6201003800c2420b42d01c0140d1546c02c1980d56000c42c0d540181c500300410701d2240e00025140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 677099667 1250 677098417 677098439
    0x60402220b030109060f031716020607061a032e0b062b0e0303070815100206150109030803040b07030b060c0a02130b031e0a0519061b14090a030b01 65
    0x10b80e18600c00c00c1c80080d03501c490040c8050b860348006000740c1c0720480340d88c0c5001208002003042841c2407007034442e00c0c14140c001550700d91000300704a48507035440807002844030440940035005c0700301318003820380802070b002001c2940884841150f5030450303105040304101d5684d4810a541d145c007a101c5a00d50086804482ea46101c4034455460700050302d40b19043c00e039a90203a200e60007070740702c09141107413900d820917a060b40c1c001c0c1000d9052100c220b10064942c03a54000c0300c5903c0d1041d801001a800c2800c44801c020740c0050006040100355502403000c50243c00849401ca81e010307209140c1641d907048118018551110a0341c0d000c040041d0126107910005605003009000f140e40e002d03030107210801502110a910082605908001e09490f2050588113a51601244610544d96119107a83e11030381040c0241c501106502d0904401101340309262081500058005501d0740e4100f40c0070704c024080c41e00d01c51200022003000070b050012911003000c0c0d20010341d80003040c20801e584808160917 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 677100917 1250 677099667 677099669
    0x5150c1009031101110a09140a080303090c0a12030818011e091101080f13020f0a080d0917070b0d0e1c030b19031e1e1202060906060402220b0301 64
    0x103190b40c20303d0961016403a5501c120740c022181600c1c0c0507080c2d898182030408da280d210450f290310000c000b1000a090340d0901c02103100d60b808101a00d60042c0703e90802c500c000c400c3c0c010301420040d28440000003a007162000d0f81040c241748442418441c010210b501401c2042c00e5601120403288408091884070780116000364819035040036548044d4004541e0410120351014000112101050408503014909400c070b50010300b0803002c081c2080e0100e0a1403010b07a1101c16150300c000041c1d40682d9202c14100701410b8680c1207210100c20b400c49840d510032980c013801d5200c030000a4080080800355102141d1070300c19905440140409207c3e210a48860f5034408002c241040415a003900e0607800501c070024400c140304014031b0031900c0b21110017046844c6100e090b00300681820105248a070101522404685807041c206078074038040e5521241c0d082880305540c0680140220740402042460f0b120b801a50700613107034046044181d0141460406810f1440030307448000c0783c502c0c00000114 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 677102167 1250 677100917 677100947
    0xd0806010203091e03160e01030507050d050a0b1e04060509011a0d15021c06140f090402090c130801091209030b07030218040f0e06060a05150c100903 66
    0x1659620001603880b0f21400c0340d9540c2c010b003440344400c00c4101c0204031611111000e4220f88103280810014000e5078210f401c42040030f4840001041000001c220351001b07070000361000c121030226540c4240d900d41031090010418168680051172400e00c1c3c60391000141100502c0c0300300c43c01c20b0b040023401000700303407030884095007462100e420203448060700c40351140307000c0d04821240c0c416031551841010314001400c81d0a070208920100001171020110088030741d40d00c001075491406a9280d0888021001503004841c03122000384a5502c4907a0366501c560152041207107a6640f07a9810190302ca04402c10f404000c110902180c4550154815101284140e4510301041e03950320301038911071a0303031100038241100000000da074184a41c001d0040313072045424079286401c440c000503080d5041c0300308580f074541d541d00d002e654824040024680000e0161540c00c03645080c5400314584d080003100d1000036100c002000d04100000b0403102d500c190102a040001c42101c1c40c006041410021800d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 677103417 1250 677102167 677102177
    0xd1103042f010f080a150315053304090b0a0c080c070b13060b0405190b090709060309050a05060c040501120203010f030f06090c03032c0d0602090d050a03020d 70
    0x9489080038480c04401d0000141c441da0541074a0410803a03260310000c02c0203001d180c84100c0d4410034030000f14980c001d544035041c2078540c090b0016481c0110741c0d00400421180c500ca04055010040345000d488411340342926000c88911080d002c18042c00e56128001c2c03070218244c080028401c2d10307034800206407007244e85191503a110141c801003140075800005d40982030b40c0340410781e4444880c0760302d008a481030350085041150400081c0c00c4600450703500f01022108101040d201d94075104000d22a917046a600c0418100400c3c02820b171000d41c000c080500d6034074060a02400420000c2089403907000046a10f40d00e880801d0089a80243c807800d4045215a0021007480c0050300903241a81c032810100c0c141c2c1481c41e00c40062507200144c4c1524040e9440c0404e0010580e0b4003c11006103000f42c54800e41480b62070410383c0c4202d004440803400e9141e0b1703904420941e8803074400c108000d41000015844040d010002908803070010b900401794030480462501b0140c012603820481000c944030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 677104667 1250 677103417 677103473
    0x16091a0301091e02150f0a030501050d030806040c0c0503040902190207081504080f030f1b07080405090c0f0d0507030501060e1804053f130b0d110304 66
    0x245400c0c0d030b10000000b818402405401c01010700e41d403082d2502240011301361285003956980001c5154400d5281414421b0000385000d00d00742c04d07004260040009580c0c68402e81c4854500405d02c83c006000d2510580d01c0740345a454007031003030b100249015013003070a59036540e0341c1c0d550303400096009404110a204444011074100c500114800d4121220003024080003844c8404400300302c08006c0c001c42d09135030280301d401000e84034000650320605000c0300c2d92682e810321541d480c0c00b40d101507005e010a01c10401010002840c94411342d000c40b441a43c90300200d403546010311006014142500050311404a20040c07211010380101d80100300d030783c138100110790700d403001103403121086850035400010001c807282c820315407241c11581c024050400d644161500c458078110089494a161036083d010a4250000b07218605c01907094603500613401d841c11000511800300310007680302c0c0c0c640c43d1102040c0c40c026000603402c10b442c00544030340f86903940d05d02072078607405120840455804903c50600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 677105917 1250 677104667 677104669
    0x10c030b10110a0f02180106020d0917030d090c050d15050f040206090609040e06070906021507080403050a050c0304170f0c09060f010201060f170d0503010308040902030916091a 78
    0x2d90500d4000303109024080a0005444021003040b001d4422078002030140004004002c800145a02906066000d04150041c205004103400042d40254600000c90703c000c2c5246540042242e46000e10301201044c2c003202d80c20004010207055000c507030406c0050841000304817120003140384828211404204644504000130403800381210000e42051080140c00002e140075006070540301d0004002096541c2071202070b50625000362a507902040f0084400d000070b5405100b1000325941e0130008101e80d20305040d0041c1032000140014003401000103222802a00c40c0c411910072805040850f03681d2541c1d401800d900c580e550a207819240503c491040d548400801c6811502d1001821149643c40e0b80080001c0b840e403601c116030641d0740e90700000401600c001003070802400e0101ca550f01041c0034002e800d0400e00009841344c1005420001400003500030f0313043c0c03002d60350f0640b401612580c0368030340707107281201c00c0c4040d400e410441d9800058100864001101e4900c40115281e08000640 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 677107167 1250 677105917 677105927
    0x307030e060a0c09030206160f030f0e060c250b041401030e0f060403080901061a09210307030c06061e060f0905090f060d0f060c021b1f02010608010c030b10 69
    0x1c0c100f0320004404280800c00b40c9001805480100c0f84c542c0710440b0141c990f582d11a0040013180300301c02143c2d400b003644404a42160b2003040492050f90868900f56413140000d88800703900c0b00c920350001c41e030701001c04203106283c007403805040ca0010256803543c07107c40d200070a1816049050000e8200002122210804160001400141c400514681c0c440343d07020385650300010803190480d1351350800060020208810012103c11500c40d1641d500d800000303108008402d00c004010074080a8203070901d1400000c01c0702e040d160146030038401010355243c804080e040c150702c45030803000010b01d0b0000d84078004134081c00300e0b1800c1d200c042411010301025a02c03c140782c031455074030224440c0040c00c0f918020442c65030002c4001c14a5245801035610341626034040c4405468440d80d51205602b110f0301004409100c11000d030b10f4401d11031260700003d0840103141c00b0740b1403a01c0032140b4030441030f000b50400c0010380b154900a01c0500140c56004005040700c0c80b450f07105212072070141074403e00072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 677108417 1250 677107167 677107181
    0xf09090503120411030706050301170303040503070803130212030c0106140f120f19150b100e01031b170a02071208190603060219030c1d150307030e060a 67
    0x9075040800b4606100b05280004005486140316001c0c102003955050140030064505078031200d4507541441500303540114082440f01c4240d000300144008107000006491095a000180c1c590f0381d07039154107905030b138030746210000d4214588500000c441d000110151407200300080080003056981c544042d81050741c3e501c403a420081052500d281424000090b04c81031042404440703600c00d1002c3e8141c0b421204815004518609a0100b01045006030032043c00c103000b404184a454000300018440c00504c074442000e01c8050318600301d16034000c2d0414416010014a01541c1654024024104544680c40301440c0c0c0d45100000e001140c07035109980304070307421101907405417003105002d80b440b42e000f0340000d41c032800c54202203411030140c0c0a80e40c0694404d0300c02607100d00c0041121035140c0c2804100c1d2040c14245a100e041c0140e008805001c442ca503d040c20700346403c4000400e5481e4042209408010800800c100d003560309500030040301e540040454442d60342d08009202141e01e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 677109667 1250 677108417 677108423
    0xc0e101b1118060910051e01020106240f020d08360d09090e211312060e011a04020a0504050306150906031903051c0f0501030b010b04050f04020f0c160f0909 69
    0x1942c0c040303408a4030040700726019030031f0600000a04584440c007440590384140708901403240789c50403051030f03a94800c2124004003414001092410390002e070103051564002c080e206a03601d4040350b00801d01d2915100c9000b408a00080226a901c0b03455850300c6600c10a40d840100c0c01e981d00000d58035142d44540b1132008500d034040c000c44c844c00c210a40c40c00800101d440e82c190014001d111000c0b107180301c43e0004181000c181041801c0c80e2805070181c0b0b4001000e2091a403400011080081c108001108880e1b0200c07401681d802d14440c0c00c0c1e46034012030700425014030030fa1080103141041280c070b004c3e1140c421510f60819554a10401d0b075100c501c01100c080e421403940207640080c0c000e201424102d01592030340b01c02c03020300c0e1070316404403040317810040f41c0315071a038004009104132120b0403070240003402da842d49001d0400000c14000740326411139078000c541c00643d40600807506400c0e02d400080391000d0358141190b00c41d040a00441501a212840c60418400a44d05031944560a03c60354 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 677110917 1250 677109667 677109679
    0x50d0b0a1d0606091f0806090106060504050d060c1e0c0c05121e01060b2803020c15040f020d0b01090b060a0827030a030c0e101b111806091005 63
    0x10703528050025500c0d010386000175034809104105000b581406200e0094807201008200c02d2800d00041425210741d9440403081c00b4042109100948034544501000e90b0804404215170040f0803040b40d5002c5558840030b0400307034040c00490303640d5021000e10105400f80028484940c2c5a8041241300d003250110011590300c104841c8144085951101208040352800083e41e641c0e1041070752104d6221103100a1941d800310540008004080300782d114030000c1c1c0c541181003d640388816659207291104040b04424a10700080c100814140e21f0f82e400c903070160802004074940d280c0340c04001001e0140c040f0460801c2c001a220b8107064099820545003540c1c1c1d1078072a00c8180c0d1804251306003405299400550750703100030024000300002c144111701c90303600103180c0042e000e0081c94140d030340c01d000d4454a9059100e48203542d0140480710035901c03410081100707881d070b803030a80b404040b0320141c69001452008080360840d141c0c0200d0380300d8002600d410b00c3d581d031a50350781040c6038020b00506030300c80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 677112167 1250 677110917 677110921
    0x7140706050909130512030405061311060f040503010606020c01080a090f06050a0902040e070f051c1e05100603020a0501030519050c16050a021906080c090a050d0b0a1d06 75
    0x300d800184507030050b0b504000344c580700c40c0503110181810216070485456100020600003000b80800142d40e003da12aa40010721a08640c1c4288001c02d402d1010b6100f00004a42c1122220b0850100d074014507008000300441640c07280040d4951b02440c003081d01040d0700d00005201c4480c0341c0100a4141d9101403641070701c5120b070382c1d201c00503e40a8184201030b591005010b0058840303100300302c000b03001d01006184086c5880150208826990070841c050704100b000c2c81041102210884803540d0b00034040c3e60203921242007240c81c0020903201404070720948541021540c5c10b9070000094900aa445501443c0c45000540540d002511100030610743d0355244401c000c001c1d0b200642003c3c0d0045242d240c07805400400c0300302000340100b41d503d50070010b059411072a181d02c09891035105c081215046600d4244044d01e070080040c614008642c000503011840e540c2d8005040141c04000e01480d407641c4941888002100200d030403100b81e83c41c01420a03000001d00d418030310b5607040480100950703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 677113417 1250 677112167 677112169
    0x50c0a03030f020408010504030c02040509071409280e011b0f0c1e140c031504200901061106090115141201110c060601171303110304060302071407060509 68
    0xc00742c00b10031007002c0e07a0900002c18034000a018460245000c0e0742c481c20008401d00400040341c40140244c20994020b80c0100000300800e2240c04420008451141c0300c0d44c2c0b41402030a1400080c0015031300301071800f00035010402c00f540018002d1403002c0082004010419104800301580082503000c40d0040d10404403081c4100a000d81542c818100060308012010210007904195101101d04440b81d0892150a032801c006a40c00e203001100107209030848240e9020401c2c40140c40503206400403d0006422044c1c6440700c851180090210081076960380c0006058849c078000c01c2c0d0007070040750045482818140100c4020031480d00320061558503100b6110760681003c80ca03d40c025a40001e10308038440b080c8140d64154072442c04055982042c5070902c0e0400000801107418401178180707920340015200b1403558403030704441e000d0072040298241510400007800c8490328a00c80014042407941d4150081c1103060f104e254880d00703945458980c140c81d0f038a00c0c02807800046041c010f01d40d00d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 677114667 1250 677113417 677113421
    0xf0a0b0307030b0312090315040b0f13080a08070206071403010b0a031b0801060f090e0a09062a0908010501031a070909230f06010804110103020d1b0f050c0a0303 71
    0x16990400140000780880400d0800c417441d20442c07041350001c690107003241402d00c6828002c400400d091800b529255850078a01803014010301d500b622240000f030300b0424684465001550044005c90301c40c0818040244459012200200180030310000f103514940a800d07003040a019842ca018203580c205001480c864010107044030425844008116102e12440500c0501d00d115680b071861039818114007a00c081c81501030343c000c020840301c04002e00f43ca21170440d50044250540403450075010b09150b0042c025020851803d400d50740352041c8152039481d2001c070031074450780720070502564072170b0a18221034003403101601080240c052421021090303944150f1102060402c0380401e929155810211440500d810025102140218000801005401350320101004d40b02d40300d441d08000090070301038041c00003041c1400800c08407049070f000c1d80540d4122007070384804000d0490f031200d4614540003c0d00c1071030081610f5900540d411032284007112000680d2500401e02064950340441c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 677115917 1250 677114667 677114671
    0x30c10020a020913062f070303060b0c06010302040e0a051b01020f07030c0e0a09121404051314070207062a0b0702030703110616051305090f04110f0a0b03 68
    0xc5016101400c0010703661004a140a030646a030340d8101c0040c1450b1000840d5100f8204d88680c642d041c8081c1405032043c0c520700c0360703206c0c60325840c0e80300c41e41d500d0298041c000d41d07045200090310200d44480034010000b025412203000700c4061200812251a00b80ca508075000c02601c0b6810140400c1418041e5140c00680d440044c4115440c061214400c0c500b00240ba030804c89460007d00801c0203e80b000c40281508248014800c02c845d1021341d550348440802d58898406010b600181c80300d0a0340c0c0207064038010140030304000c183c410001000d030001e10750408010041417000f00450b403060b1000950304240c1303c182d2107a043c054861300d5031030070103240842012a80c160702c1a100e00051002e48006010b100305e80c0080d84c44100500d0094141200e840c542c0383d955000c541000081e00c0c5c61040350300c42c000d40d410103d56410310145a46550350305900060f4100c0f1503c010300c23400d0520395440600c564003a0a4a0066007900010058400741a0703190590056011406100e5024024029a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 677117167 1250 677115917 677115949
    0x609050435070f2303071103070b030a0c09080f0d030f0504020906120f070312110d0503070e0a03020909070302090c030c07230106060509010f0201110f070503040e010311150306030c 80
    0x500e0b040040c01002c2c2288280c0c13144035050781001ca120b070200100080b81c400c44610490103003814504041c05103030039000c0241440c00d443e8980311510101ca000d050184054001003080e1108201e8a00c0c50640e13685200707090b03d000918121110400d28414803406010300d90040011810f5240c2000b082605c00003006074a00034003a25070b18540c0310400b0408680214441c1c58403050700301c650003020704005c0028006880715008469640016a8403e044070b030f0188050404501041801003c10280456500001d4200a811042c00607007000050b426044910846240d600d642d030310020417040e800150b406600c8800207100340d0300001d0b0400c80c41d50114500103040700384500304080c501e00f1341e04035034814004590000303041509568051000a0152a140001d02008000f03810030f410700d100b60200b0a10010012a041007000070a00c02c0b01c0042c204001c10b1003865840e401d01c9198501c070400f150740b1508801c1d000c202d1000700355050b03078070a84000b0040c0c03200e01ca0b0700d018094400e01d074203008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 677118417 1250 677117167 677117183
    0x20a0b030618040c0906060f09050411040302041e0507050a0c0305030721050402130c09030b040f0c0803030a0f0603030f031d0a0807140606060a0c060609050435070f 73
    0x207001201c08864550f00c43c40c010100c0f400700070325110518085480300d4010303004200042040c003100d00d8210784840221030003a20002a180c5115075610000e00842d080207601500b440b104030000385003c01441d03c400c1aa0301c0030026034580b0311007962107104212140000c2000254030201003401580038681c009280d0410140d040c044076a600e070040032100c3c2d051109561a0103000940c10440c03205101c2000302c3d00200207130b0030a650b000d440040719100061880541c1c500260400c07425001260301c0d16407106104070469190300c20191280c0040320b0348ca06c59403400011901a404d80c2c060700080300d40544131100e00035000c44086003d81390300c49210014036800d14022160500800c02940864003490301a51100054035090000c55051052011254800003c0c080143d90b00002c03260007400c6402c204c88000584c0c50450302406403079022002c61840d080c108014007811a40c6039440c0d540c8002303050705204200105130781c0c4060102058007860070500c109000240d455000f494020f00810322 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 677119667 1250 677118417 677118439
    0x10e1b09101a03190612030810080a0212030d06060809060c07080f090a03120309021f020705010f231209061006271202030f2e1b02060106021504020a0b0306 69
    0x1350064581e50350000500d01c0d00ba107480010300d40e0084803503030040c001c0c8a44e20940391400b030640b5038903a41e4620187c4a929560110300e00c0d8ac00400c1117403a061031103001400101d56034000504104001c5403050881e001d80c0c1d001801952a0704110340005620805507810001034001480c0140c10020200e41c0241d0958070100110f00c034040d0551039940305540100702c0070018814000b034203042c0003441016135040c1c0c603d6145643c001c140e1005a402c02e10709140095003071802280d001524294a0190100c98080369048801c903000070204055405464905911401c0041d640c03040d04854810306004010414400a0b115020030035010346001441d14000d0600c40030301200015a03808903c3c030550307005044e011810140010561070342c1641c09400001c0785c94210b507240c00c5000488203501c4441c0b541c0c214403030b405540310100e01c0000751041c00e81d040030080b02960b52603003070044901601c5600310f2903075114030740030702d05204907800b80000101a150886030400e40c7c1026185e507030b0140200c13403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 677120917 1250 677119667 677119711
    0xc0b180a0f05060a0e0a02101419080106170906040b0a0f02030a020a17041203180b040f140106060210050414030d0b0a1202091602010e1b09101a03 65
    0x6202000140a900901500d003000c52200045400000c2d02503140c0d040700701388a0152307031501c201c442c004541d03003043c80c4000f02e0311030008034501c5082e0361020344004200200d4150b6071301c00c030100d060b105030b901c0308050700540701c2c607044100008a480b84100c0d0300801c0060001840c00400f960098170002c8003080c0c00b002c200420041c2d80084a120007550f602281c000b000d2581700003118094580905920b09904040e01c2e143d84020810100c3c00034541c9800d004c188001c580c40f104138106e5001034601c0e0247c1000d2401c120380c00c2c0174401c02c2d07568151080b941d864402c810b00c1444100c1d0205c0c0c005011b46d81c00e02442c01c01602d0001c0044d80c8180e07801d1110000d6403c01c2c0001c03c03d070a0740400c00142e49009104002114505403c0001c0400401000c3e00043c1c0340c010001d500248080c119a01b00c401c00c8100f03d01425606514041e10300030702c010480101400ca03c030104425085690004a036615115130b5001c0400384a0f01440710705030600300c1e0542403864000c51300b11081440758060242164 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 677122167 1250 677120917 677120933
    0xe0a0b04020c1005090606011e0507150203040f02040b0a0501021005041103010e1e01050c1804110409020d0605060906160611070c03051c050a050d0603021206010302100c0b180a 78
    0x300a0ba00f41c5502d036010440c2c3c1c0c1009001e01c80d445002420030383d07000529115202e01d03850b40b82e4518014018005508400d0000300c0d6651211219000c1040d5a646411f14002c5421809450b00302c0c011403d1400240140c03030028210400d54206900420f845502142840090000074000341c400715030f0140364599585080c0107900d0035034007035802801014070a1132540c3d680600e08154042d00d0345850140f14642c8244005c079949400f4490300c00400943d204002001482c59081d2195004000103000841c0b2086401030081030000c800d08200841d603480a100c2140706035a00320750b101d1340800080049142032a2080c60050150f8000224404841c58046080d4051174082e200707540c90300c10800c100074080041c000500400d2011019207002040050458000c0301046818800c01203010440c2d10240d1384507400442c1c008260030882e9440124582e2506800c0c00168002c541e04c03014176801c1c50158644621007540914804520b80c0c6000041413280100e00001280f4000c804500c1c0c0070031840 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 677123417 1250 677122167 677122183
    0x903030304031e0309020a0b0307051c0605150705060103140a0b130c1401080703020a03200a030b0102160311130906060e13080717071e0308010b040e0a0b04020c 71
    0xe0345500710700c03034150210300d80f41c00746014981040600b44020f0b0300c016205c141000003142d080784da04036282d4462400070b89842c05540c1202d2800d101140c1c502901c135815800c01021503005980900c01c80e030011890b14014801c00b40041c050354001001000001c0d411006013500084400948040f0702c402d03541c0b01c01c54081514403212503c00b00c0e00240600c96100303030020003000010441000018041c00180c440000181806c06144d4042142c84a10f03000e9045040304031840b40820320041000790310103050b500710300d484400181c600500c410055000044008007030500d0151018503500d9036039007080180311544045e03000017a64110700c403c044240a04010184140d1000c20081c1c1404006c803d0303c40001c181c80d07140c80b6003801c82c0c40800e101e28200e480807a0484030208807a8500300148a51703115010005186503401c410718105c002c042002002d846200c0c1d0342d81451666078010003410b50081d0f01038603c00e03803110b034080342e213404440e40800407040000e0009418106400d84c100e051081d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 677124667 1250 677123417 677123423
    0xb030303090706080a09150f0f06032102010c050403060b0d150f201215060a120b0406052b14030c01061a072d060605131a0f01050903030304 62
    0xc59a018406550010209544207140c020300b000034180d2078562461304042003420450241e41c45054288d801420303005520001c028080c2400a150b0b40d103806040751208591305585401d100b002d40030a14810300540d1200d030a503545881c1007605613100c440080c4040780785d03d640091450520000a1802e04d410100380700803442c00101c1620b00d41101c01520300701c0c8d41801076180960041003010b1036a005442c0000e21031a60b01200740c0d2040c800d044081100b0302038651240c0045503130803405034840b41414400404c0c09040c0910b40c01801800103440080c06016401000103100c0103e94000103070800c0640500d10703040d4000345658807a074640c040707401c02199041d0070008000b4000b24003400f40800520b10300420600e0040355844910803070048007402004002211541004e003144401e0000e2103480303070858200030100340d1801c080149803a02c41c2e54042c04540300343c030300a17481d10f10600c501081d01c440300200070450001003004900c05030040c0ea0501c1401e001c034140da510f00700701541c81248 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 677125917 1250 677124667 677124673
    0x191e02030601021015060516050f03030601120612080a030f05101d19110c0d0201060501090608070801060e030a060218011b05070e0c071a1801090c0e04060b03030309 73
    0x620704002400c00c0c1400009240b402d06080f00300341e0710002c4080180460b00c6a180040d2030b40c01e1030091825020541c0d60150852140c01c0031074010311800310003140600c0382600c0300c40484014048d003006840444c0302d40d0703070041e805400b00300c0032407280401070152030141e1030006a80e074a14440141204c030191001146151010381c01c0c0030300e03801a04084041c1610080400c450301d881c54441c0101010710000d020003a491f038024980004028095480c002010303026a803080e07441c4000203000344690310a2900107000800300180140c0948a480d002e165280c0d15465a0f0f07081c428107803070240b07000c0003007078140c8100303520140400c1440c03010741445400e040c014400d110481d000100340d24003103400c25008101031140e501c0080c0c8001000c0003211003404203407645a43c0c45200c0c280d0b07402080e20140015480c210b09030b1980d005002032510891410310050503150154080074201e4442c100700400b0049000c500740084681ca40740740e0783c0144281008102085540042030031a0030a070703410001c0ba4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 677127167 1250 677125917 677125921
    0x30a0b030610090e0c0307031b05060301090f050f1306090201090815010815060d11040f02030901020a1403060d0201030b0d170408060105010f050909061f050c0f0a0209191e0203 78
    0x34410701a1504001c41d000c014505c046a80b800241c0351850b611008001c1d05c0f054841511a10f03003405003000603c6e006090725201c0d80d485483c90040d2015403814103980345810b0001d103401000e4a10300c1d0240d2114100c540c1c5462055a4600c003d00d110714059044c004ca00714009083c4030b00b00203680c5400105007c00c0c406514100c4840d03d052015004d40d181d1040310000c008075511085482c0340c00e540c110a043c412400a04042401003a0178034500020900002c1080506401500180a40d00540da1102050102406445031320b00007610704a078045900800d071b03805503210784c0001007440d80041241103034640d15900c0310b802044480b4000342c074500105040110400034046ca1340184802c0c2030804c004040904018604c0c801d42800d240b00b00440310110320a40c65031700038079244c00c0b404400b00d0840d0540640180041e0011441c2c901e1510452400f11018000441c43c00541c40e40507103108a44c1e1107000b1125220110b507442c806100d40d0b40c6003000360507800c0c1006104040020f0400580e28 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 677128417 1250 677127167 677127179
    0x6090a0905010b0c0f0a031e11060126120316020124060f09081c110717010c090305030d050601021504030c02090c031e0c0702030109110901050a08070b030a0b030610 73
    0x8410400401803c40d0424503081011a802071036003503807080008e44c4403a0489420b00700b924150f81c01410000305100741000803c50202d2001c940e440741481e03413820340006813020700003036a507200c08030740704c8088034240042044c02e5001d0000103562842c6000101d12100c15511005a030b200c0c0425002c55072a110008012080d00002003419400c101c0c68030309506410441d4040d034070b2000441c1103006100c03040c2c1c0303051200e1103401e11002041c1c000c4140c038400c594540182c64100c01d00010102c8551074401da1800045c0256030a0f41104d034002e001d9404e02c1070350801c800050030014a4181135000d8498051101003c5800c283e210318403903200d60402d40000e005000a100009140d160070301020003d01903195050307160040f0617003030011013041a0381c030303c0082540f07800391250082d019800d20004004000c140d40d01002420020b0b210380c0203d070790315403c0050b003003147d100c1c940c8143c015010603c8a91095002075620480406002c2855910480840d00c0c0040c212104101d0681000c414409 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 677129667 1250 677128417 677128423
    0x120f0618090a0206091c0f1203181704031b08100b06190504091103090c01090614070303060f080f060a0b0f09060a0b040618060216030206090a0905010b0c 68
    0x202509a00550340c05181100c0c0352a030b90011180040d04c65903000c02c0d9600d403980c0703103588800040c40c810a0341404850318a4803201000c08904210303441259406000300340d901c80d101d091309207035400400c403014008589510720300f40704441200041c104108008804250090341b4503500107018400c940280346042030003401c01140c6211a400642018045030145e55594251020500c3c0c07800e44802c000a1900143d89a100d6640600845818040840c144080205c042c40c41040400c3c00e0700c0411042c1d81c0111070041c80c6000f0704001c104102042c00c0c460700c2200141c050300e44039050000e41140c41d25405000c800d105d92098100345d00c100300c4443c041d40300f40059900006645c1e0244002003c03000050550034000821034004c021207000211559620301c9540002c061a150f03007540c541e121600144150a002a505401000c54a001410ba480000c0c84684a10742c8481c4915140c00c66080044503403200425a0380404048000700398131404c1d10581380202211400155106100c0520f030741 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 677130917 1250 677129667 677129689
    0x20c0a05010b030d08010e180d09090605060906070308070320070203010b0f030d21060314060702030a140d020d140118140103060e0307170901080903161403120f06 72
    0x4043d0f0412950f070020642c010031728606440444440040507614226501c0009107121914210340c81600e0100314408d400c0044902038891403982803000c581c41e80148012842080c0d03810b50004020001000400d103d00d6000750030011a18022450326104141540c036440c54018400c40303200e0014012045180c248548007a1080a4030f03c850b400a946000944480a4690b003100f4170100d01c0040511f00d42d86003402041da51061400c000b07540d01c90a00301480000a0b4031034080e0301c40c0f1000b02d10b0060001041c2d030140c032155a550551541c000842d130313480e5081030041c0950242c0911480c0c06800030350003044030b0072007001d080d80382c00d40c03512480001840d52040340a0500d85002d44e155803081400001505483c2c005401007004615800f0386031841c49848000341c5034690002103941c0800051004056aa0090341c3c0d0240503100c20010b00d4407171050048a641c04190350100d03070300091350501482c091114400650b03080c02e644105015904204851044180301000e0811410b4500400409 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 677132167 1250 677130917 677130919
    0x61f08101e1505042d05030a0c0603090c080318091311042f04031a07081303020709110318030306061c060306020a0c05010b03060903040902030c0d020c0a05010b 71
    0x1101c11100a07a421000001d540150034101d4503141421403214000c10444000b00f0105000f26400e0038004c491540b40032407800d4080212054200000d0395140c0003500050307041d044118012140d103064401e40041910311030032100d0708270f440c000244041d005d1002c2d07e00c0d004032284506024036414100001150018100c891100c0070f0039078200403c0a80030003501c4c0002c01e07103000500d4814514810040780c007081004c000e00b52504088990506424080c1085074440d400102c43c0341051011441c50f041c0c11101080021007400000c1c03c041c00032034007850014001d0054400c990385520ba60420b8686100044520403400030902c16000e10042c4200910301c140f00107507080d400c20300c0c000b44007071080070700110701c0300091401800c1800d00d6130b100a0095510010843d9500d01100014002c2400c616090315554038004591b41e0b6400c022820b284900c481201031481c0a080c001e2640007074201802c2d94184034400d10007008004168401402201c134400010014100289006800d54511107522 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 677133417 1250 677132167 677132189
    0x50c06120609061017190e0d120506100c06090206030a06080c031b01050a02070909030e0906150901200109031110140a020c0a0b070e030d0c0218061f0810 68
    0x54411544941e42100400050140c50100d458a81841e1011b01c81d40c158031804524241e1100c8448000203020510340065444403950010700511100c1110011110103810103d02c1000220b030b548100c102c0810a40304040004100c10b0a0b0081015038104484080900381d0303d000034400441c1c108a00c29482c0400c400518050142e40540481d40c800005100e040c440003280903100f03640248540c4001d8025018200015102810001c204044000409000300122008580181020345074000701c2020502158682250140110342c0e18001c1c0350340c1e25000c181240300c4215440c080c0188044180240c0e2900c04880c00c81d2203403400c181c00d040299190b02d1901c2409000141c040289a42c04000341c0300050705c03141e1086405041c1466020010002603a034000c010f2495000070781440030b00d40030327401c5aa01140e9064144c90260342804040c0d804400481003021000700034060f9a8081c80c00752401504402c1c101c0103a22128005681402044400302040028101d0080c8072004184c21000b03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 677134667 1250 677133417 677133439
    0x111e0c0f0415060804030c05010903030f0b0628050408060f01050909150606070602072f010306060207051512150f0a05010c03030c27031a070813050c0612060906 71
    0x10014110845126000500c800d804c0005c007454000c004181909030410000e00c80f010403071074002c00a004038440100b2a510708140700c1c0b007a0412005076214100c0140003c010020300c016440c01100b01d1284138400c12008010208008100b881442c2c000d00904015003015414081080322820000b49040710701c0c2c0c031034101e000d16222903445c03841e0000030075100146c0e142c2c11803c0440203032291140c084c054503c10310404c4a4107501c9210280f006d6001004c61305041415001102510103c1c0328000040c1c0c03008200380302a18140080031002c510250380d1034a400002510401c0080c0200e5400301e20001d14202043d080c1442000b48640c0380040fa41d001c1034a0400002030140b5182180240c2010307a6a8200c0301c5d46400b8034a00004034803200c00444090359281412800b00d040c0717000071034425000c125581c01d02c0723200d503141030701500300354942c1e40d516a602c007070f032622100003148140d4680c032807120320269640341d8500800403c070701d94801e5102440c004c4248401454082d000e40d0050002e910 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 677135917 1250 677134667 677134691
    0x60d140c0c030f03040510021902150106021f06050d0521040f0611070f080a1a01080d050a05160c15090e06010e0d080d14070c02060901111e0c0f04 65
    0x1c8a01d0741da010225141c403502d85e42005482c054040744007a00c006c1c030020b0804e0844103041c004007031000f665030032070304511807410b4040ca01079002c2c410000541d200000b02203040c1c169904a45100741031540008030305583d030740020388006001c3c4068a041d0040e0038420b181c8c0c05420786803403903400310702015461b051415401d03900301e4a0358441d0038208140d001300341e447d0308414003102c001440c440e10103d001546402603c2e854605401c4116642c040c4070501490700142010700b1412a8114030240101805014042e035143d4030004034181005810009600b8905403c00840c075118029604d150600b420240202c0c81156210388140c248030b450081001a19200c04041e540f0107001e20700580521201c0303000c64103041b00d10000912030030b40441c003080702e41300e9030344000d0703026415a00480c00381d100c4907820756503030700505e001a4128074100f000b441594084c2c0300d01c6a10341400d02c01c48010711100388048a032a01c00307038480d4034590015042d81c462490210f001c40c00c0c1420844041004504c185 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 677137167 1250 677135917 677135923
    0x50d021309083412050c07030c081e07060f0903050d0518013207060e0d0f170604020f041e06080717011802120a0b1c0b0f09010605060d140c0c 63
    0x2140082140c0c200d44e140c18a42e5200c0c10a03030350450810740845107a030340c4a00c0d041e00d0b03454182c050032400e445440340a00b1541d1000c0b10a404011880d00500601410607404641d1104043d00c0c050038407080c2d40703002000540c10090b905284500759502a2a181c020181441559084810710704100310044211031445009520340c0300b01440e20b481c0d000022062400c0e00f454002c07403501801041c035000010b0303d100800301c0d1507000381e240c40d5100c20495040240c00c1c0c1c0c0d8501c03403211500c020054440000d10b85c0c00c003640280140d510b00c48090f410150390700c445c43c0308840c0d0500c05500307903000044104484c0b50840034031500600107040c050030000d400c03120380060110500c90700e14902c403500d014800010255044402c0e2015101203050030f85804c003d084060441d03803800d0307406610012010020b00030541ea480c80c0181e440841c0d01d01b10780701c3d40c180014400b0007030511001c5551b203910001c0c0d1070399450010109142503040102c0c001004210304c4d00ca4420040446a1200041142c400700c80404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 677138417 1250 677137167 677137267
    0x6031101080601021c0507020f060f0706050c0d0606050a0906050a1b060e0a1a0f060d030c11030304090c08010510091503062606090a0c050d02130908 66
    0xe103024505582c8010040703142c94501c044e2510348018000c40c4859080c0c0c458003d000d03c0c1c2c000d40d95a59032a1084050003103600c5800c40e81c1e881400140010300c00594503800494110416000403424184800320030b0048030514ad004c080400e200140c048152500003001074010300d81401d200d802d040a140340603000d02c9092000d9154030b80512144402c01405600c0b4800c81102c50301100c0c00e00c80c0381e14069801185540101c05207407202c1d0001100000200354044c030403503018200703d07600012580c09a0f00142c0c464070454142c404c0d0402d52032551020405040105811640816040c580c3c04000e800e886041c0c020502404000800414043d00802404121108e01946e13508455003031400710000c00160304031505404401001c7c029541c80d419035207242103140001c0c0d0306c1075210a82c05c1f0350380b52140000101007401034801000140380007050400700b10b0000d40340d03105039903107504044d04441c1e12140031a4202e1022640030504008526000ba050340310900845402e240303010081204000c1b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 677139667 1250 677138417 677138419
    0x3010e0a1d3301080303010f0e0108031803011404390b0a050409020309010902153606160c06080f04150b061611010306050916020c1906090603060311 66
    0x40011a480790401c42e104036980c1218450420440303584500ea6291a81e20a00c9800607503240840d02113103140250007c58122010b942c0214070b0a00082c0741c121100300004c022517819541d03541c810941b2a0b00e00c013002d10807441030804446650003d00708100107034030580144001040200b99803d41d1010b0400a415a10280c20b03150f11200401012502c034411500700c0c05030740340040240b010754041500b01048481c4215041554043d102c40703881d0083c0a40b0090111403915600c0503141100a40d00c02c660110844040c0c00c41502c5103030200309154801010381481c1c1880084038402c0c80808007030720780906080d180032042403e2000d10003500500262001d071800ca01d40c881900d51a40650090b4003903100900301603110b0042c1c8041e41c110448004c02616117081d06400c07010250312910801c416250001c10002c040e840d04503501e4481c402c07011307000c0150701c200d519090070f507907410119170100d07074072003200412250800000910301d41c41e6610035018903051907014800901c00c0c5414880c5500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 677140917 1250 677139667 677139703
    0x30506010515070c0e100e13030f0e18090c030106060804080919080a030806040209030a06090f0204020f0a030e0d0507060c140a021501050a0506071b080303010e0a1d 73
    0x5490b528640d00c0707900c0004124031010840001c240255000709071140c1844050304080300e94425070b481e02d80c5070803181c43d503006240403001c400190050517900d0700d41102d03280c0541e501c40c00c240403a1414a46800c07100b03072861a201004403901c003c204291100308107800a000c8a86000c102a00d218000b80c8000c0050102040440d01c0e501c50f00185014142040351403071400c3d40c1e82e009144c80740b0a40c0c0080d8001174611001402509150003250142c0301c0203030090030b0150280d29080000c2c0740c40d05080710f80b00d040d1520785015a890f130001d4080f2202041c0ca0554841c44503001908030361200504d081180c00650b240e4950540000c160303081c4a8100f18080303480700f0005000c4072007214030040300c0a881c1005c119640c10590000d410340c5812461640741d84641d89410030000c3c12040c620403141d2002d801c2240c44000340c1d030442600c0f0005520301c40354032042d4070390101d6410f41e00300340c00c40440c00203507170100814500107008030240303400010085901c041e2400d00c0c3d40e80700c07900b204161801d04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 677142167 1250 677140917 677140939
    0x206040f051002040b0d0b01020109120f0509031209030d1b080702030c19050111030c07030305130b07110901060c020a050405070e0a0f0608071e0c06060b071505010f0305060105 78
    0x150500c034000540503145000c41d0f9490720b45c0150030f2103400070040c500010b0326019203440349500512418130540d80100310a0592941e001c1d04603020021030f21030a00700301c0103001071507072902c003009200c3c902000c01e08200e4440444d842814540740584003020104104015002010010280070344980307a003000d540c540d10003070b50011914000008408a800010411000e03403103007202e1300c5c01420354509980d0a18901c0344001c03e5540c0f03002d00c0041c1c0300340e138209030800c00009000d0002400c1d44031543d00c0e20342c0784075902d42e21903145420501d0165909880448603d90030b141c0b00c000c16024003150300380901010465004185000480d007c3d145c003070307552900441d4546009110071800700e140140030005003a01c400008071402450310441c2c000ca40500081030105025220403a613030f001584d2580014000560304440c41d00c110441522140c0d950303d008140714495078011b082860054081e40625424254400308a400c140d000c201d8840304888148002000828510b0440f04101c034409070f14 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 677143417 1250 677142167 677142173
    0x1209231506100e03030a030501150c032a0f030306180603050c01080a0b040e0a06060b03071205071b060c09050f010f081e10090c090e0619090608071a09010206040f 72
    0x142100f14201d51610020034036019040e416000b0b80d043e60205500d84284600020701030301d26a14020000b4003044408082801080b009090503064840060074046286501d8079004e0350034207805019000280c0700c220602041050941200c0480341c9982d003041810b280da21016242d07554001c6003030420101d0030215a030303642d081d01b28100054008004102080e0030b409402e45d101d2500b101203035058244400000d04940b61401d4a2080c500d42e140c441c1e90b502001c14000061000a005000b84414401c107041e040d203030103031042d154a108010000305060b4800c40a045c04409900051040f02100c02e128003503607004080d4a03a0441c54108001c458517401600c0c044441d00911490040c04444100840410954042c00840324508000c0011081405c402c0390500001d014041c100705c03150011403030034140165140440d142140041030020f4895104900340e818550007008140e0040e54281300c007040c1d611030000e6180340c04107485c0c6401c10040002c1c1d2241002080540b40c0013800d0000818 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 677144667 1250 677143417 677143427
    0x40b03090f030408030a08450105070f1806210f02070507051518090403020c090a0606121e090203030d2405240307120923150610 57
    0x101d00c8024003542d444a032505031055070307a0031611070100045c2014001c81c00951744400381c0803e50031803090200c030f40d0500e550402500143c0031040041d0800181c80311001200030f04c1001d0240c8615603c58010301c00c00b004c002c2c582419134000b00c030398203513001042000d181c002c2a220300703000d00d81c04406010300b030300555003004102445816a0700c0c0c0c0000750030380421001051000903102e0485100c082011060300f206000c0c003c0d03200302030b82c61210000840140c604008605d0303105100c1d2040394004c0e5001004101c45401c00c0d115502c0e1540c4513030040c80a01d8012000c1d50560945070002c00c250f00c20000c58a6418031243c268a0f462030759000081c0c01e646040c41200c8414041c41420720071607521040001c21035018070181090200d080d040420649095104150001e40c0000207041005645018280c01e40c00508200180081d0390000c1c0500e00180c041c00081501801500c02c403100b03011a80c203d402c660800c2004070350085190151288120844180c002c070701580c0440e01c20014180c01d0b50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 677145917 1250 677144667 677144683
    0xd030c03060b0d0203010e07140d0902062a010f090b0105040902030705061803101107030f110f1f0203010602120904020f160c0501031b0809070f030311060106020d05040b0309 77
    0x88214070000b4040341c1010b0f1600114100c0b01202800d0313100f80e450702e00072210340c40710034940c00c144030080145c410b92108603045040018001007055190420401c03680d9501941881c0c0003818403950800500e044c0700a1062a204410b84407040c0150442070707440310012503050040350300c6140e40d0300310541903407030030041e0070040c040180440b555002140495903d01c015251140e10034416070b940c2c1301d030820b140d020321602150300c48051070a020b0584d4042c0c07200f024203203502007000002c4404244e0410f0800109400ba400e00000d002130350602c0010007080e008504440d80f40c9401080100030080e030026000080090b204403c9460700c8003407002401078422200c0391040c410000c56034100100b441842c6250f550b01c01c482c0a041701e41d5a0780150195032441c902d950f20108030b604c41107203103405483c6442d805901d82040d00e0955445121980a23061150016000030f242c2c075481414868040144502408840c001880c142c841200000c2c541d21070303402080352032400480840d603002410400f5034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 677147167 1250 677145917 677145929
    0x51e010f270912110c0d02010c2013020c120702060405060c100212061201060602120a0210020a05030708010e0c070809060d0c0e01021b0604121e1b0e090d030c0306 72
    0x500c40c0540c03808002c4c080504204288498001e04401c403182e85000020003007180d9060b141c0802d5a030007900d642c0c184803a15000403481ea40b8900209040c0d0f590504c1c0b04003500100e040c0140c407040d0b10340f56030349001c525542402d0202c00411070f00002d6941c07402034400f2104225101942c40803010941070805000400b443c17106800400e2040f140c4141c5212644108000d60381182c807032404840b098203940951003001c0160b04049420241207600d100140400200c0d070040760480d24294800408030f0307100f401c0f03c01c0011004402e11035078952050f80e003401008080e10302003050502c403054075424800d80800500d0048000b40111054640078150f03244420603080c20008040e030316a002d400d00c12000700c460700602510441c200e42503c2c030b102d590b21708940503125070308103403c000b00711684c024035260030f032201c1c50410800d80745807000c03c8100d1007041c40f5070302e80c0200c10103403860304a5040307140c0c0020301032a0b241c1c01000008100001c10000c0001702d40b402188844d51600280c2c01001d06400030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 677148417 1250 677147167 677147183
    0x4020c0322030c151202211b040312030506060a02070605030a090b090d030f061409040203030417010b100305090d0c1b091d011401170709051e010f2709 67
    0x50b086120350b60f4040042c5494031a00b40d00310061052404900c0398070454000087c82024243d54403c1030700c5903682c40030521800044017224407030804841d40190b44200c0743c6020300117404c2190b0b94107000e41354021a080e070742d2034100514081c010b92a12400d0103000f00300034011001404152503604151000d9401c124040700900b0407001c03240d2211000e049080210b8204410300701d00f9000c9120b51003c660070103442d65181c00c0c14004109035400b0142081c0d91600c01848003060001c405031075036108042013000011540279010503c43d510111000c01c0e02407600e4903040020460001c03800303c0040c2c00714075080310841000e19182009104540d50058110109900494004800c0c0e0001401361445000b682c03140170104003203030980c0d4a44640ca0020b0351035400401c113410360005038401c1e030b05003102621011606c40ca003580403294200c651840007280c00c0985501c0f022010b0502e4090142c800c14080300707038280710134428102d08071001c0040c42e1071302c00200002c103042544400c510541c001c02c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 677149667 1250 677148417 677148419
    0x51b070803060a050901050310020c1e1606080c0904020a0909020c03040e0a020a090e040609051609050915060d02190b0c0d091503090515010305160504020c0322030c 73
    0x180c809400407108240180078405000c00d407403802840c060304030b41008004001540c0b0206940303001e0740150b04542d20740e114030f0410207100803004a1001f8000f0f1880024042e4080c90b021491545140754401d200340712041c018810181d1b1483c1c116000b0000950300903130750319041c180c05ca44480040d0310103080e1b2840480c1c0ca02d10000f0100040003140c220340700050207034407180800d030704a10400e1203000124140200800c40013200c1e00689030320500500000038004d20b04d840b02401c1861180c4461200200740c01c007480845420320417290080c0901000701920668494944002c038405481c040c80740d44d90041210031075a0359804802221100e80344040b030141c0d00d4101c80d03180d401c01d9401b00c2c0240a11004030300894030920749441103d00c500410108408420b03410750041c600789800b03440034004c0c1c2c400a4034204924184500a521600003405183c0030600400003014083e0440c52081d401000350000103d0008280d515020480d48400d4484010840c2001c0d51407040d44002c060140a0310 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 677150917 1250 677149667 677149673
    0x4050906130504051c050f09010f091208071a0925030512071e03050703080c040305012307182d03050d0201050c032a0f0708040f0e040206040603051b07 67
    0x55803100c2504580c2d9440d0908403170581a1034500888000b00c210b502d041c410b0300c24540c400d0300003085d64016424a81181519207e0bc00c1000d001c0800c03d41d030a00e0002840d400b0810b103030354050b1020400c40f10760403a90500c000040c1e15000e4480324000e846100c919540c0c419041c910400b4021540001243d03000b462035810403006822648098070010311411040140520003800ca4030703455410b030340300f034907045950b50150351650700a804854420018480800010740c240b2802086c40407a100c1c0740540a0140b01c00e8030303e51002424001001b00e0202420400c41c030a01215060312032010302e00c0700e5198a140341c0003c814240860b60700c10b07150800c6c008240301000c181030700620380e250b00911003666080c246070300622007074a144030040810000c08440c2c21035603500c0008003a0412010386004180d914145641d04501d4080c0c8141900150800c10403440341d41c00f40c02801841e03540d00e0300b894160000f03816030013240b0851040c1a15600010203480d03000709800e2011244668940d1501040c0c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 677152167 1250 677150917 677150923
    0xa060e0c0a030c031505040c0b030a06030b010b1b030f0a0305060423040501051509060f010309230f06041e2901081603150209032d0d140405090613050405 68
    0x100c1300303542c540031440c841441940a40503191180d138200e41000c00c02450400440125800200114040d541c7e512001c070002c0c0641d200b0a0003081900247e41e25081610304041d11110b400d1140f90040e413007040802e1070380b00b0010a81e900c0c080142400555a990140400d001d000d408400103040d039452150105407440300382e40c03a801a0b009200800c06603030351513500d038044d20b40a0040c03903100f8441000144580790420000d02e44030818500444c821001e540d600580d03022444440b02c00000344414442241020000850350320a510010071850409440700481c1d42c42c03141c0401144400c581d0703941c0610103092082ca58103a8100950002140d4000e00000b8404080c06010500c0c004c1c1d0340a0360000c070a2030745070383c25a40c0101d14000311500c01c1c51140001d41c442d00301c1c2c40e0540110880c040c401c81c8601c070947c440c0700d54031860420b540b0302c0c0314800c0c1c140310701c00c11070600340503a10280c807104101d8007040c2c80584200307907164103a071b448640014041d140400403803829142840101300c1046404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 677153417 1250 677152167 677152169
    0x3070c050f010209032d0601240207030206070314070503120a050105040b01080105010f0909050c071a01030305030402133b0f1506060c0304082406030a060e0c0a030c 73
    0x32029100d01c0c01405404074240d1150200d081d926a01c202d84400e20014940d00041d4442007041400c40c00c904840d030b055080c00001d90146045801c150710f507184c40d01d40400103003c1d0030030f02e1020f0003120b41160300080460041180150801c04803502103200040e0802c00c0f213101036000f0003180c3d120000c6c031042c5121110300321540c21b0406c0c04e2000004030b81c1050b004048440301d0584400765641c0c24500116028000398800c0340822984060024910016106103805485582007c0da541c0000c1c0c1010203502e04200c0b2a40007070790079400100007282e404800d40c0d8000d40d04035200c560180f40c00407900060f102e0820340b0b09540503250002015070402c2c1f01d0042001c911500400a0411000303151502d8090201104038281c10002d0016001501c180c580c4d80e000b03070000c22250400400700400c0c0e14580198110300c03401c2d40002d00340070114101d110f940280100d0344200fa101c40c90001c000c25203413400707920001c0c00c007615009800000e00040c480d002c000800940040040e48d620b040442d11b480756 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 677154667 1250 677153417 677153423
    0x6010e0103021f1205060a1d010503070f060203030a02090102030d0203010605190801140d050f0d0809150114102706080114010903031803021503180705130c031103070c 74
    0x1a160300a103800c20f030925600a00d101c1916400d4614600d541004003402000b40324035884500c094010130407624010200d294000845400001581004141464480103411040103130001030410402c5550000c00c0b80d130702448014002d80c9403a0316500607861802408900520a8000310012510395842409031100e510340c500002c9101c1e0368a902683e201e1400e028100b85103d0220703503403038a41040c00d0101003081c441d1040b1110054206082c80c24280700c24600b800040c10f04081c07001000d01003103024031240c002480d848055240070920044018820b40003405883c2e02c0240c40081402404406603000002503c4800e560900e070900440b00b04d540202404607a09900100745400c9024810f41d6045044e124107400905589003a00e8040000e50604403c42d00d03006c0210041e103903101c600319644480394400d5241d090440440411042411420300d1590103050200075660320603801542221080c1000115441407200440c0944051600103519410000500a249912003a40309980340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 677155917 1250 677154667 677154679
    0x513080318130b090112111305100617040209091504060f0c05040b040e0414330717090309031606030b151e07050a0615120302150c04050306010e010302 67
    0x654440344085030700403103031982c000380c032034005116502034000310510740b074040c08a001c440460100052310100c0e0b123400d5060481d0b201c50501c4410000d2820903005000780342028003d070a01d5242d440003500008102a10800c805030110326070031814088202d00c0d4200480402051901c0c2c100007015040c0c10800e240b03010710b0440c1800545108070140c0b02034540e21813140e490207180094008a01d1005803003a42c0140324010340c1452450704101d801c1c25049490201c208070400d02d07404142c01444413420020300c003000404c0091440e4003100d5100c4520060b80004101d444220381c1070701d14040c2509a540600c01c100c00020040a4107a03044111002030764203100c0203101c3c03000c0c030605101100c2c0a5010040c14071812010b40031202000d816040000d48407030034240c2a450300da00e4a01662800e035425a644ca01c4003a051a01d01e0009028105c0180441610450390b5002903842c0d90003807010507080c105a0114000c1c0a10204560003031100030b04507280c80d40c54683c40324010100f0b102c1244a41 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 677157167 1250 677155917 677155939
    0xd020409051c0f0e0d0809060d060f061e181a0d0f020406210917180105190e21030c06101d04061427010204150513080318 54
    0x2a21504040b0342c08400c43c1c3e00c0e41424580c090501003600505041280c4081041c001f002c40380d128040a0700500d030300c141022038918602400f005401d18a44c00660130000c030a06042c803400b551070810000c01304986000320039101c0c3c207403400903203030f001c0d8002c1d600d01000358840d284070017900000741c04900303c11001041000c40003182038081388a0740c890000800d5003940581080480384115404039801c0c003601003034410305940d41001e058050600d01d4a0b183c400305280c180c1240300c07031419405103401e003007042c50851411091102840c18803031120070003c01d1000d00c4210740320030a540d03400c05040c002103203081c3c050080b11a00d076000100c03842d10303074842c6600042d1841c80d880c1c015407c868160f440d500c40e000c180800d0b5421590000c01c180c0c0c013540c580c1c10007403240000c52041d512900d034211103180000d100000711480c2c645104e0303020480340e006000074044c00d0f4007042011000d4215080c4181c0e100c0c6c821740441e0b000806640110058040801d1440508600303040100f903079542195060450 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 677158273 1106 677157167 677157223
    0x80c0f0a0c08010f09080d0b22020909160801090506120d050319050f07031d0109240c0801060e01020102120103050d140307020c0607020d02040905 65
    0x2685041030801032440288100d07105183c4013241070015035450f4503591041c0c025101000c0b8080e5070742c241c2d03400035a900c0d001c503210480c203082c0320140e80c2c050719004402504182c0c0e0503402074100c00006820030300c94040704042c3c40090703102c10038140d0a0260400003084010318803500446d0205030f03d00c0003101004000a24107240d618542d5900c0c281d040004c100120010960076581030074240019001c0305a1a2940a1020b1500190703950400e00c0260f2000d908201c403440f694a400340840030b01490280c02003100a5100c020142003504e007042e081110308407010500001c0c000750062044a21401d1481441001480094203125616a010000314000e074821605640302c2e15401160a42200236a014071006102160461400850294840499018040c0b041c000001c0c150115a01c404031741201d65009041001100501e04d40260354005010781e40c0c094511503a440718103 = true := by decide +kernel

theorem cover : BRFrame.Cov 676978417 677158273 := by
  have h0 := BRFrame.cov_init 676978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 676978417 ≤ n) (h2 : n < 677158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
