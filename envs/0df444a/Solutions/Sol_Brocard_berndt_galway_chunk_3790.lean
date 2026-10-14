-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3790
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:40:49.020807+00:00
-- url     : https://prove2.me/submissions/63bb7cad-66c2-4dc8-826d-aea951b194d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 681474820 ≤ n < 681654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 681476070 1250 681474820 681474823
    0xf0c0807031401050918010605030d0302070c050301140c1e03040309090b2e170414060928030c060c03021e04031104021309021204170a020604081e0309 67
    0x148101895181440b403010000800d0b100210709000b1a54055140b00c0420071003001508003100851400300001a01034403000000d24010fa801800c00010703400043d404204942d07e180d03040100010b070300a1101c9100e10b024002058002444c11808000108035141c404400b0110b8802c0c0507401c0020035030300d00301410000d202445501070503481c582000d00854590070100b481c20710100a520075140303002004942074400d511820325003001c01c00c2c0301c01503448485030b003601c5078011071040d107124024400000034681000c0004103070042a8010401007200000980070b00c52651940c541d5083e080403031440c041c0c40402010748003818851030024074031040c5030580d0040032080b6a0020800400e00c0d4580d10011620490100410304c1d00540c8003c1c0031401c00d0b40191401e0682c40004107041915490340000f03c8c1c111030300d03e0391041d44280902c0300f0700c01c2c1800d1055010850001c150702d48400700c280a552060050001440780d013001030175800300060641c9049030070480380942952801c100c00d019 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 681477320 1250 681476070 681476087
    0x803011a19020a06140601020c1002030909090c040c140f070606080105130605090703051506010c0f06061a04081f020f0414090108071a0c0106030c0e070e10140702040f0c 75
    0x1100d1851601c188110080400d07043d8a1041005a000b032400c1c0c0c01027418412301010452444003588804d00084117680d403049440741c411755110000b0601104d15804100507503a010585009008410f2408041d00d00d03071104480e610340030022030540e1642e1070300d0f216000300640d80c0004915464401403158131005001c1200070540904410300103522101d10036134580f201448002c1c0076034000c518900324001450035050b4032807014100b03441c000c01c0320f40303035074881124800d0200c800340c1d941c00c8180240300c0701c400c00c8581d4407080c4158a04103800c1c40741d0140d0b900c40e603043e806244004850821980001c1d501124510460040c05903144c40e44d41c8403e109408040c3e42542c401c140c110004100340c0000a8100201e542003490760080e41041011406150b1085903000c156540b104c9011010400d0420f16000500c50b41103075101500c1c0081c80200946041c140551040d15544200912560700c014000f0701d0424100310f072503642c0000d20024000f41101c0c0d440201c06402c16030500141504001764 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 681478570 1250 681477320 681477323
    0xc12050f01080a0318090f1b0807020a06050402041104080625120b21010f0b0d0c060c03020703050114070f0f0f0509040b130606080c1204080c152403010501030803011a19020a 77
    0x8008d421021680c0594640f03c04036030742030040e48482c0c4040007046143d0007040d007140c0081e00008012180341d502207c01e50107500549160392102c410b0006680c00748540b42065000034407070680824042e4402042a10f06100301c9404944600009000e0303550110398040010031009190190211011407030b01900700712920555040c60003001d0070703881c20044d0311075075403d0b0300000240a29051010650300784940007815400c510641c040400051424440d906551032070b064461050302e0030020040c503a6130080700000400600f0202c80804a40201c4030030f00030102c03410082c0d0ae9403140c4010400030b0240e00c103075950100700c0030b005602000e0583e03c80360503100b42c2d50f03070010203a6031040c1d2121a4410441c0c502080c0c034991780001c012801c0381d4050650701e4060015501d030105080c05d03d00c040300c07080d10702102961582c0003e00c2d114401c010350309240e11090f07000b0700c641d62440c4c90b00943e82c0414800e07c87c1141e21300c0d902400c002d8440046460010440c0c02c00d11602c034000f903009540c0c100702e900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 681479820 1250 681478570 681478601
    0x515040603051c020c060d2a0503010311010e01090303030b040e0102130503061f09110903012310260c060a0305190207150c02030d0c12050f01080a0318090f 69
    0x104960303807003c00d20170018074000c1c04061a000c00c2c00040070017442c05040318081d42e0100c1c01e00300b05d000b03138549101c0461411652015182e5042d8101344254900c25680c050602c00c54040181c110390b00184604101c81d09410b000801c1d00d410340204018004105080d03aaa51001030340d400e0390303011038002d041a40c8007034044544940e94025a500240d26200300c8000d01240d15108009144040e0880e9520078a4112014140075084020038251980e0a050300e8005039a58020721459909401c600c1d804868011442d40a624140c025a8040c41c018541e940f414816900e0400d0120108429007003104041c10503580c1c3c00786040002d00902d015100510600580141042054624003e903282e4680141d0001081c2c12034003c050010424000b018041d03010034005600c1c241603510850800102c140c075040420384401864504507003005140c150100114001400004000a41c4a6099525003400c1c00703c044c1182d050f0150310709aa011070040e90900751003c40a004c26000100b02c01680340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 681481070 1250 681479820 681479863
    0x209100b0a021c080402060f03070c140604050c092a1902060702010c2a150e0f0c0306011409100e0a060302130b060a0c080705010501030807032a06051504060305 71
    0x3c00701c4070b100701580c011398070080a1007002090105940155013091090429030b4500701c46640e01e0307540710714410344a00150025070402092110074004051400411a08060340e45030003000c03c07581035600c420040000303d40c9441d2140480200c4121600600610b00001c000e40d175043c1c0096603000216030000c019402c041882542c07501840058145840c0c0010300b161640c2c408501804440d88000259040034801419003002065880f81618140203440a0072110110200c46d07031a01000b003100500a5000100400c080c990840c6d240010013012201080641c4880401c00054007403a04281d1080c40d8407403d0000020031548101c08591003520107032884600d8006100880e885141c00a03003083c4200030f240c03281441090300c07007400d6108001031410000240ca6050171904260000c5441e40d0b070001d80282850742100c50ba030009200c203070040d14001400b600071810003a200341c00034100c0e034591000c12551582c1010300120517170080c004010f8580e072410120707500c0c104060fa0b2010f000406 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 681482320 1250 681481070 681481123
    0x150301030311060103080a030b01020309040e0c01020d09180b120d021b0904030e010302030c0c03040905010311060f092b0f060e030a0207030f0602070b011404060518040209100b0a02 80
    0xc02c1c444e0403a034028070290304206030a4030682c054118101c1d200c1c11030008204a1003141e03540d1043d000139004107030003080d000c502e400000e45001034a0f01480b003401000d480401c216001d040340d20f0b134041380b90000850541c50410118421006030180000c40b400340d9a41018080e5000450000098132148514009603a51040c442241d1050710b020300000c01e9103010b0b0500d0350003900196007004000070218074020481e050036046801c16041408800e407148010800d2012440804850160859840b442c0000140a001c031510607401058047d0511030030340c4c29800104500d5110202c1119501c0c3e01e003c21600c0c042d00c0702c100340c00d003c4031307120f2503ca01280ca0346d40c000190b922a9825400800c0000e0035610340d80400000c00d841150255000c120240014004c526154001c040045080040d01c1e40201080f0645082d44c100c0c41c000c400241c10001c20044c01c0402c1508150140d4850289840d4841c80f04c9000c0541e4202c18221080003540a030041d41c0003a03284a06003007800c4400750001c08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 681483570 1250 681482320 681482323
    0x19050a090503030f09240f010b090303180a0b040e180c22090501321e04020f0307150908010540032d080a020711150301030311 56
    0x1031810241455105100194140c4074615103103400c101c070802241d64450690400c039034003070b42500380e6042114083c000d200b120300300142d07110702500c03420b02450b04000c0c801021950728059100c0c5805e4614603004c11310040d4803a0000c440141a1074110f442e0385030b40703070548006142740a40307510082d01881c00094044940114180c203070000014610204291410301640b54100020006c039421a038500402000500c244520452145400407124004480c01e55031440c1c0d075040d5001039400c94030070701081580c02e905141c64541918442d105800303900c460012460003489880340ca070f0148142c16001c80c1c0f495040044207400d0b14941d541e18010340c0c0350000d041c2a1041a0cc1040c2801d001c0005082c0c54248540042c0811118010400110003405c1c0c440c81c105606e07480c01d4011900b0340c2211050f2031818035401c0d0b035100300ba1808019003152520014004680205005021503020807200100403404c0403d2102440041015490807540700a00849610a200407004101c030000000082e860 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 681484820 1250 681483570 681483581
    0x9010f030e0c04240305060105090106080f01060c110a18150b040b0a180e0105100302030f22080d23041a070c020d0b0a06230d0f080319050a 62
    0x40ca80c060b02d03048042c002840081c00c2c1070501e01d0503400d815400c2203044902068520011030140c0d0041516515003424841881c0c0e041c0c205e0410480d1013001c006d00c0c0c0030780484180c1110100e11740b403242a0442d04096000b40d05c0c00000d1a4004040f4038002544c0030020142c89016000b1242001034803850b0403032200032040340c481c00207594070500040110b00140005019001c001d414006030941d42c400d404000f0f41c0b0f142d00048880108c050041c045820155558880b0b4000c130f0600b180796041c4040c024601c040002e003192444440f1103951351a005c540c0c0c6004400950040740d080c1c0310002201100044c000b014400002c0c5491042e0f6140d818807024100ba004e56001194280c03620f000e403140c414a004018074840500009000040060b1a4a401c60004034020070b0340d4100c074200807500c80c0960704681d011a2004544c11b0020700c1d118803501c1e00b02d0303900c842142c20b910225018503040740584160540949000004000c214441069002e942d8940703890b02e9007000710f076550604c94011241c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 681486070 1250 681484820 681484841
    0xf1704150515090c070c080a030305040501050703053612030114010e010f120b060a0f0206011a0904050a0b030a031d0301060b030109150305100b09092e020706020d0209010f03 77
    0x41c040001c0752004c14548020643e240c00b0302440c0c00d42e641c4520001d490020b1944003240001e5640040105103c1c084c40380300d0300200c480c9001d0201e03080841034456032604503406010480011410140301002202c405840701d0401016240f284005910100940c0c000340310701c1c140208406c2c0034150035071090726030400d420b00585507803600d0f1160100440b07003240ad40d1401652a540c84d4080105030351380c4806450700120503510522400080800242000c0040e405141112140b449448034105034900307071145071a0680e40003515542d80c41102024021602c00290140070703007a0040f0605600c410349227200314518000034081c03c0408181400c8800c3c5114040905505200601414806400c04641030038a002e0588682e5201e440b0541880120f901d039191455071510980000d040054515900014a02c081d000035139201d500c440c1100f2421010601c0c5407051044044510043c0e0305540b02d03250442011921481c0c0001c0c4070009602603002035002c2110b00148042c018070902404a401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 681487320 1250 681486070 681486079
    0xc02070b0c01020702063103110d05070f0312080709080304090e0f0607080108010f060806070f091502010204030b060609180c160c0303080c0f04060f1704150515 71
    0x1600d82065058190003425000490795000c128030000343c0e0302c0310060461020034100140f0041c4e00403500c1c0038017103d15a5100c0c0c108280c9441000481c002d041c021503101c0041c0c0e85040588800c0c6401070505c051030b00f2100c0c40e030000100100501c00d04d2030041958104075100c12103161101e410a842d03c581070b100e0f0081aa20820081c042c1d03180c0754001006030140308040301e0550200c44c1400d42828030440d07140000030b10000c0100000c0a0034040c58119042040c0104a040d05121a4603205c880090146091000417171050549034440e140c00e400a00180050b002c01d4505044020f0107988140b0003600c5101c141c1d008a4134a140c184115092607100030031119041140034002d40085034020b00c8032321500424841008a601503c0c03414080300c1c442c0784600049070540c075006c0c040003c00740002c0071010060040500c0c0c0000c8500301d6044c0c49850500c03c0c03600d0302408089403000046800c0c40a11590001848108218959030f0b51001c40382403414000d590310381c0d400034484c0020120350f0f98403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 681488570 1250 681487320 681487333
    0x110717181f0c0f0803130203010f0b010518120615130605010c0605090f12130f12061503020d05030307170705040b091507030203180603060603190905190309090c02 72
    0x84074000d0803440000d42c482e01c0842229440e541310b01040743c1003194441c0144040e145140d085140c00c0c81012034881c4008000c00c100c142d208002003041c0210320083c0d000760071146547d06180e4403c44c4c4507002c82c0302d1000300d0303941c0e00d882a2080c9000e1440c003102030246140801840000116024480030395006940d441c00c04042d5845007005000c010b000c00d00c15000701943d034441000f050180e014040c0e4141c55065550800c08401540c2a680341d000b0842405828801d0000350130440c0c00141440e00560086000c0300300ca0300c0100300c2c02540d800203511200070b0101c00100140800a14031a4443c1d0301e4100054800246070b49550404591403000144100018040e260749800038042181019000400f05928048041d62541c40440d0a50159001180d10096620202c1c0c2d0940e60301000d1310841d040d81000c0010542d6800090400b00d00b4084003141c0030f01d0042554450320103d034000f8216912200d2071450f203c001e00c5d16081c250000341202601203800006801004080303c5c4c107900500c0c0f03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 681489820 1250 681488570 681488629
    0x908010b18060f09011205150f180c04020301030f060506030a080d0e010e07030b1006020307050703060e0c0915010908010504080901030903090308040f05010f2111071718 75
    0x18007031401807040340c1c000d90b441e92031403a0b038895101035030103042074444c02c6111515500702541360000181081055a03142d00803c200b44408000080d0000140704c61b9003000c11701d07a060030341010400303a1a20b42151000c40000140110713144001d8602d07020b95801c00c0141c03100350134583c942c0d4451070054520401000495105000c071b0f03100220003258034000081200320004e415040034001d40c0181c89506001040c80810750558500c40c00408582c00194170b41002603031080c0d2100090f200140485a4400001039511407c0c071001440c060028940071240c6402e03282106400b509414050009421503808180c80d9014401d0340d004d1500200618181400040110080c084601040303080251003400080099240c001403c0507252440e600d11006003000700043ca464031000041042003031820075103c1e201c003940001d4204c1c840c0c184001c51058446e01d04040036204402c1d0050041000000c007014101c1d1040c06407a02108400900e80c0198000c81000320128803554025013641c0c20303070240f44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 681491070 1250 681489820 681489859
    0x10b210a0803150d060c0e09091005070504050d051e030405090c0a030209030a2009070507170405031002120f01150c02040b040524120d110a02040c0f0908010b 70
    0x43e48030b040001c88207119080c034404903141c224401400c541150303c1d41b802104190300881c61404c100c6007600c1180207894145200c80d601c0c8480807004440c02c2d5140040f03040c85106004460141002915400e412403184c540340b40d560702003d1380345650f082080f49014070b1540210458044410080100d049915961150b002660011200d0030506900300070b1100e494500b40a104002c80c000c07521041c03180c40c00030108441ea03000c0c207812403040c1d010901300720b4840d030001d060741d00309900191800811503180b4003a080b6845160001503251148440c1c1d41b00d842e800350020031000c01041d001100c19210b841d00c10341200340a0080c211400e501d80d0440c00034074801c00c9a2000140014004100740c640031020408a40c0c0c1501c0b04190b5100800001c2d1075807910410840d540c1005503001480d4a40b8549916107448100da9004104081c0c1d0142c04140c9804005c00c00341c494004104101900e0001000390104150f0b61680c0041584e6450014588906200d50f80c00400003501800040c40d810a500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 681492320 1250 681491070 681491077
    0x19030e0f0d0c080f0109150b210a140c030a020603070201150b19080f360c0a0f060207030f0204020c0609031c020304050a1b0801020c010b210a08 64
    0xc0e00034400002566040d5a81c03180704010a01904900403140d04010f8000d01340801a03600d0740040c2e061600d007500103410801c1130091078040072000510001840300185040d900c02c08030380c00454209040030b98504012030340c111490711840328650250216031519031075181280b0101d81c10b80000ba409000350030f003000155880303c41ca1000284d08012815103544400c0f0320b801030140078102080b1038580e114118812205240c8a0520003450328020701d0f60b20305910000e1002e05a0f04074003898045a210352800035070318122000b01c0812040d10105695691034581c00142d00c200c50050300058004e903002010400d48080e41d002d020785500710b880740c403500e0340f030284100d811645c204543d840b1540280442409242c0040143d607849119036250344104280100c6800041c0c0b04000f404002000000c440c00d445a006802044401c0300c0c200c04005c041d45940402815400000c3c0000c054406500400c285407040303454071134211125030200c0c0310b0b00c0000d126103003d90102ea0b008010883e640c028 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 681493570 1250 681492320 681492347
    0x60102071e03290c070c050105030f01090f02090d0b0709120503030f1b0a08070206060a050a090b1216030c1d06040e160803131d042a081e1903 63
    0x403002480b00700f101000c9041c4044076410007042002c10b4000030024104403440040c002481d0190843c100103d1101b5500410701c100302100d6034030b034080c042d01d10f80d9405550500b40c00502005e0a44443c1c140011200421036080340014100d03080402e02c0c62000e03400e0901d07650800021800d6503a01c541c00130035500c004e001c01490131001c4100481107810000181070455803541c402e02541030961b4003902e00b1074040c228911620b0080030501040d107500c4a00d00031564100707400304654429802045501049141d075003002e015074040107410261201d20700048900c07851085400960303a0400f03c0d120b440341140711a0300c80d2410086205407130903402010000000005803802403440c000d031186130300002c1d400035046400203e0a0b4058120007400300005103100403d101c001240100c0d56222190000d20003090340e044c0004030282c044c4446401a0009504209128241c0d140c107412075481c1140280c80818424250080708400808140712000c4504a20186124569642e040e40c01c184014007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 681494820 1250 681493570 681493613
    0x7080901020a08030a0c03060807082a120303070e010e0a0603053301020f01090f080304260301051c11010c0212070b0a020f010b0a1202130f05060102071e03 69
    0x420070007041d10030f0000c0d400741c1c20002c0005050310032168080c0640720280c1c08003605403c004000c100b14580402d2000f11100d042148a04a501103080304510305820301d4140e80003a160041d03040b540600000450250515444200320309216100440341d1030300c80c0030700c00d070404040401000f415000c0c0c0c014941000c0d010000748200300c003202004143c10100d01c1c01903448801200d00d405656010b02400d41d114180c00000d03c8100b0890321140c9212190751300082003044000005024404000d001d0324201304e254140c110007a0940e282c2007040d0b0070a010313992081584810b101200410200603e51090380001c4c100b020581d900010b64003403005180590300003480060440702e2490a003e40c002410a4600c01920b0b5034034044024038004031688000d10320303890002d40c8842a07507010f0001d8120786203c060b2400702c00003440401ea810b000840c85041c102c0c00d0488601c0483c5550300098491602a400c42d0b0045544e0303440a000700d40c0940b03406002d4201c002d400d10104425003040a0310510000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 681496070 1250 681494820 681494833
    0x607080304061b0305010906061e0f021f05070e04021e18090406051b1201050f040f0513030e0d0206030406050a0209100503010e01061d0d0201020c04060303121508030708090102 78
    0x2407a0810030181c941e030304000295517800620502180b0710070303000901024034164480d820101092031581888007042e00511448000e1510464820480940502c400301d854010100500c266003010b09029110307400851000d40503480b81b41014400d035104000c100824078181c041003203036800707250b00281000050a007105030300345040e100c49018a01132481401d0003d03092805144203030341030b0701303040080090700800c1115103003882122811070305440080301e4805000ca03c0d140040e00400003110001481403e02041281c1031645141400c800c80c0070342c5501100142880812850b00302d0441c0c02988407c0070310214010601540c0201d60000d0b03c100c00500c3c0c11007083c001540c440014400c03500140d40040188a2607001c400e00340c1c010803440c1049600c103258611000008480449640d000e1441400d41c0419684204400e82e0040030141003005a5600ca040c0205001110075a02c0080c908121010703000c00d00c03407100301040710b40038800745040c0384142d5100c0030180d000d007007014118401c8c1d5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 681497320 1250 681496070 681496091
    0xc0901030e0c060c031201140d062c0d0f14070f02040204030c26011a0d0c09020301090e0f0d021906231510140f1204050d11010203010302060708030406 67
    0x3c40007403004500c0e400046485a030b90f903440740a2000144c2004440450b50b12050a0a071620b4201d9041168012000300307201d00c00c94000420298881100700824005412000c1e0030040411165070040d0f0340e680c0c1551821100500351480c85209030504160103081207940007040c00340d40003885440c40188058075140e41c83d00c0b0382100f001c00750480204203801c2c00000c80d200f52400907101c0307140d2082000b03201c280d42c000f0710710081d030350480304641c000c8282880c50000c12401928600187c0200e60045440756107507968903000f4a040d071045847c900c1020b00d001004140007642c821041590380c01000c45003025210f10803262428601200c8951700c07a8103401101d0015080444000300c0c880c205a40381c43d0030b0141c0150310840b40c40090248203a0854401e40e01c2e8030526030204500440341041e1788940102da40303880c501c14880081c036007010300018401001804a0780100d0b0120707543d42c1e6145917a201e00358130300b01d00c420b08c0025400f8100b00303d03510000d90580c01543d0703c0381c0940e0300084c0c1031066 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 681498570 1250 681497320 681497329
    0x10e0307031a01240804031206171015140109080303010902031b09090a0e19050d03060812030402010318080d0615050408060604020c0708030a110d080c0901030e0c 72
    0x341c0003101d118a20000740707442140800e81d042c0c010b100c01404800b030b0402a20210044602d1a4251810001118002400c3c1400340034120050300300c0407001c01c038840e65060100003242c000d1a0810181c01000c0100d065980f50f8011941038400c408600c8402514041050300e071190340e2854141400310055000880d68020301c003941c020150100003580e43d02e001020903000888007203240c003083c0001c0c041c1c01200d03252200440e070701c410300c00d50004640c0c080c00c200500c0c20000d045003451040c505c850340402c100021900000c10b102c2618244041501c81d540c2d96110030564620340340c60720051000401640c0329401c1094040200404080200910748030b461059014044c8003220381c2d204c11341001500340f000d04140c01140c0c149081d90809050000d03440e200c50010b0540d922480d008680c0c1c0204000038000b81c0020280d91003100e50b40c3d24074a001620500903c0b24116070f6018441c030524072030340142e10051103040c014001d1484d00888200544c010480c80c1a440d1051103101140d0465888 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 681499820 1250 681498570 681498583
    0x120b01170a05060106082a03040f021c21050301290d1b020c06030705090f04020f0703120b01020d08010b031905070e2b0b070e0d0804290a0e010e03 65
    0x3181e0318002c5500c4c00c8040d021030150450402c1117505c08181072000b1007c40c50094036082948100040702d805520f0000a1000003030040407100781c00300e41c0a900400039009195000200a600b683c08058504401502c0c270b0300092189204100105030019051202c41c08508409c5001500c414100b400c80e80024044030114070b407403c1440d450f10404020250100084d000344102115081d00e50701c4c01942c020254000d50400340d0091604010700f0b1242d60b10354064035251031032510560303241d45107802e000380b24150594109101600c3d0808558065201190480102c02c180d241c007200d90b447c2440614599200800c10b80700c8050114030307042e16031400d009243c00340759559903401003c030810040060b0004030505510540700070000007030303039941c040b008614195080014215995030307808080d1042e0011106a550000001d0005001c000301180a4416604882013100c107a0305982d0410305a003609100c800600310b014081007401d54843c5221202110040c94a03140780c420303010101c0d00d441e2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 681501070 1250 681499820 681499829
    0xc050f0d030e0610210303060b0a09061206050915010c1b05100503010f1205070806040b1027020c0a020d0c0e060a0b0a0c02220501060207120b01170a050601 69
    0x90325850b0344282450708214940d00b1480051605a40c0d40c9003880780070442c04d48503440400d400310300c8000802c1c103019611020007421850741460703503561184001400032845025400219501600d6101801114810030b4241d82d0090003045541c0c6510000d0110008081c000d14100102080700c032001920640d001854840c0d8682d2685469041408105034010400f2503101008418401001428040c10502c0300b00c88800740c00d00110794941c1809402c00585411425540c811541031004019185608611400605802c4071806031940604a8542d078040100302c00342c040c00100301c5032420035034002c00080a698088481e0320321030741e01140c82050616020707140d0001454003003025203040340c2d08a6100504842009180e41003000d40b29041c041e0107140c40070041c01d44021030454544149410103030b400c904000e00b1010800c40301ca80a401d09008910060250311000900800200c0c16100b0150707211500e0103543e0f080903170141a0390b003005000d10301e40c818041d000000c56824840c4a0280 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 681502320 1250 681501070 681501077
    0x1605010c030516030213051513270e030a080a20070204051e0408070303200901090519090921120e0a0f150e010218010e0f030d0c050f0d 60
    0x918200d4003120104080310a010f091600410003181d0207526181101c1c26034500312102e495032115031031010400c2c040c00411001e070b203070f5400d400b1540d2035140b0000c48800c00e600c0700005851000203008002d4403c1c10400b047d541e4000d000d0024118040e1154962000148000040740b600710003201c20b004040c005d00000e800700c005020b03410f6003001c0c0143c0354031401c41602c0ba40018000e821817655120014006403c03950013007a410101071080d00600000100c2c031110410075001041500c019511100f8058041030359600e0025081c14020420b840600c0000b4500e02c1346440c10030400090103030050700300d82100140713200040c03007241c0c02c69044105a280d5980b4404031004030640b803c40d01320721422001c41e4800a00c42001800030b080c3c409031283d002c61191880000884030304007070800c610501865500204100c498400340413007240c500704090784c0301c04008103000240140320044020164140d00b00d20b203070103030460094a081c1c00c0c0500c0b54084500c01425030b40c21605004140c60f040000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 681503570 1250 681502320 681502331
    0x60504051006021507020109051507300c1b0305130f030b0a02070317070815060712230c0106090b04150314070e0a0608071203020705061605010c03 65
    0x45041a2154550260111007200a00d90078020040d55840c00080407040c181ea072200044c203624400c4d0400d5020550141c202c2d2050802e544800346504000c64800c40003074460442280b16510311038100d024902c1c900c0d507540c9000c0d00c40700084041d040d010280024000e111001c0c010030102650152500d81c001d5072002c4e1902d070701084c4092524015401000f0403501c030b01040c030200d268281d00e50f412180d0138400507902c3c0664901a0340454010a040c4a0f8009200c100010b864008a03220721a003a0540174807501c020100800601d0b0080940c090500c6505072030315140306000e04041e20f403044441e0410340040c050303054800358950241d1400c1c542c0365121076080100409a02440b0002d520464051040100c103811240074203480b48005813403035185400180c6482410303c1490003a05014140c104546043d140b80c2000c0e0550344107800035482a42c00000341640004115041d05d541070b405824942e00c0d0008011640d08030180d40c1441c5244c030f003203600c0091401d20821501302802c0d24007056 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 681504820 1250 681503570 681503579
    0x91212071a070f180308030a05040b011d06090703021c09020a0b070213050a060801090c0302030c030f0307030f0302090d05060403200c09130609261e031e0a06 70
    0x200d403600d41040910141418401c40a41005000d0f080003403038500038200c036003800c02da1101060304c0d40c000b8206607000810300407009125040644140c0c0500032071301c4642d170b0b902c0745407030b04bd00e8010101c07442e440708a000c80c605152491000d03401100b2841d000d0b0400c041019016403410301301c4a40710480744e848510408500b444206034008008a0300b171181850090340205041e01d032040300e914200740da40c03030003d074091500340c0c040341c007070292080204080c0109140140180c10f0601090b4401d2149c000e101402d03280000d9001c0442000c0d0001d14182082c07a41c4c150350401c2020004014107409000304140ca0f29100c2240c2d4400e8042d10007070a20b8105420060001204584d1030610401c0c1c0907451040320b4800107441e000b55400f51080005650f0700e01401c00d0340206854024605410407080310240140420008010320b40c0c0b081c40320186c0107455a02806106ea01001d00d00b14000040c401c450b140c031980a5540282c0c1320244480002d41c0e032201e0b02d08403100b200d1203810141d4900c2c003401f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 681506070 1250 681504820 681504833
    0xa030b09030310080c0a1206090b070513150c0201050d06050303030403030617010501141c06050408090307060f0914180906010612060302060909070c0b010b030703050601020316030509121207 84
    0x8009042c0080a04003080103400458420071b19401100c642c20740e859540c0c410800e030707039201406254000092004505204c3d4008245600081c0ba403011103404880100e00720106840d0045080d030345481d84102001150700544039078000d4442c0e0110965100c20005160b00c0920040d446540b0950303000881c00d0801d100e40c5500300d820265204039a1500c07005000c07000e0700c0450041c11090440d0014820600c1e04208622502280740081440342000280010059003102505840a0407016a40e940e034651404580b03880a1900010000e60244410824144001c0210003050304c080d03e8141031a0740095030442c02203041e10500c10b00d61051004011042d4070043c12a206045c1510510610b0325607000500280034a40d0329510466010010a000c1e82c02080e0440c43c00b07602c001c0b0b9030384569441c8000e9606800c2215110003090030000001c01540c800300444400b402511011211201107840481e11900300d40030150300800801c0c1c40c03c0501004100b91030303c516419140c9640d0f10720070300e4030a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 681507320 1250 681506070 681506101
    0xf040b032e05060c0304180209010806240706090609140111090a0323100f0f060819080903010603061d061902070c0e04050105060405160215060a030b090303 69
    0x2410a25400700a640446003850000011034004503900743d11081c004004904500c1180d100c5000d012004000810345001c54015051b10b03402601c40300710541c1c502062140d501c5084c00420900d083e1000c4440900380f0240c0a40031035402200d001441e1a05951058211900322800343c40a862910455040c1d031024016200c10310302c032146907070500d10040d0100da0050079074000100880307000380c0580300440181c0c070000c80e1651000120742200008803564402400c52900f83d21041d424846090303142d44260103210708580f040c0b030041c2804080e00448402000810302d0803074400400b04014102541c090003010055030151200060b0342c2c0480220002451600703d00190680004007000031020b040c01035030360840107020025076981d0f200d160040d03041c1c0040d040302e15804800030500090100541c8658810581035804120076121280602c0c480b6600569420040c4e00c0425040c40079102424640c0d04006d020307003980d6441e92070f642c401525050413110042154004010080299108074a4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 681508570 1250 681507320 681507361
    0x12102040f064a1516060c0f050f09040b06040906090f05070f08071b061a01090509010501050a030902040c0302190e090c1b060a05070e04020c070501140f040b03 71
    0x1030f1880b6001800c0c020b4000d1011084070750b110111054035a0044e155203c03400d0300384590008144e44e41d5003a0703500002103043c1c900d05442052802c0315030001940603000c0d108100c01e01c0c0c0c0b142420502c00864035180f81c6e201e02c164a03042a2111414402d03030700ea101c0944050f1052000102d00c1c0d07070410101604440c2c40081549445042205000c4100c1c0c11290042a61085213408010b99503001800c1e25005141c041421001300720303107264018800e1691244c8807414844180170300c800303082801119950031900030154000700910041089600403001400c00200701d0030080b40220a0760009011105c031212402d000c20b800160070003c4549105810100d4081d03800d203004008541d07000300701c42c0c440060140c0410070000401d02c1c007071007110301c0c00a0808410000c40f040791405000040151405aa900c4042849200d541e0320700e24203802501d4140013174500a181e00c034a0840110781c204882d8104240351380781046060300b0b100040340103201a0066600d07840c1c0d03c0c00c24803415001300805030358 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 681509820 1250 681508570 681508637
    0xb040e07050d021507050a03080f13050d0302180a0b0415050408150604090206070c150207080c060a1e26010503060f06040b04140a0e0c012102040f06 66
    0x420300c16035031000761030790030160141c5112402c0303003134424150f0311031040080c00b41c8a445208210303410503500c10078040c42207600343ca02da40b454841d1084c0c1a415551980c005045400c019098003c140c03190f40501841c255141c80c2090001c1040d001c2380344000150001440044c1c0010180f141402c115400c498000781450150300d858900041c1549400c60b50b40c45a2a841103000400d001d5030301c940064203030b00d8004041c107941d034506141401d18070703505205030000240c20252082005001241c103404550390840035152128651301003182c1030340888112000d00050102e40c181c241420b00504600719429191031104403004190501d11204412030f50005041d100700600068801144094108403020741c00240d80e151800010041d020b400001c64000f0700d0320600c00030300000011614014071616804124842461141235102e1440114880c0402c06009800040101d50801c401d43c03021842c000508098940261007411b0105902c85400034090710343c1d42d4031a40ba942c03034594002d841765a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 681511070 1250 681509820 681509833
    0xc0d061b0807120f02040b030f0709050126100f0320030c0a0b0d0f022a01050f01050d080409061701180b1f170604050d03060303050301050904050115090b040e 70
    0x300040003103c00c815031190158036010550400015501590050002804555101d1400a40d45400311724211034a0000030a4000300107065401100c1c810074074100c2d0302a00303200e1118807030600c0032000049d1455000f813240e2000003400b0041c0c03034a42c1e0080e61142e16a03d11a18802d0700c694003680000003034a01c00c5c1c001c105446401e83c1d5096a21045402c0c0000031a1142e40d96226030008000c00d20305003814900005031050708090048160300700d00100150030529400b0040c4460807100122030315002c040d80c0500500840c5802408100200d103e14046403500fa02c58030440141c03420359203c000d003107212b2942c0d40c01d0282d080c05011950341020b17840c0070103c0750365114a0080f110140002410f0300f0040070107150344a941c5404400b4200340b0403045003140400b429240e40b07210846007907406000d400e0004149038440e008020840790555a40c900b96400d041c10491140300250040760703190b68402100c3c3c0f0b09610300c81108000d0030156000104500c1030414403003541c0340ea40d00c034003103a000903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 681512320 1250 681511070 681511081
    0x30a030306240215090a0203010c09150908060c160501020705070e0112051b0d0204050c030a0b0916120e0a050718110d020f1201031407050603270c0d061b08 69
    0x102c61500c0244d10702c02c04000c1e2950900e0b02d040044107400039405509200014840c05d8110502100710750a81d000e5102d2030f9031074082104e480025002c0d131000f6800040102d504400d825014110459011030341802412803603644074220b80c4544001c40f011b8010f10f204108031070000c06090300600003102542501c0b41c0f2662101e484044400c00c1c00f02812070402940841e8071564080000590f000d030081189092041d8101d00540080380c42d0082d081c10800101d24a09201700d00d103000e50440041c200d034003c551030054503514204107505660350340d941a0015002010403680c40c0250203030300581491800c0c811f0201e04800c03160750251b2040d0511014085011304d030f20803149506c5450200507140c5102449200444c40f03126603041000f042d843c0040248503018607407080c1885440c1c220b60540f503540c800e0020500007140c004024035521004540340d001006090901ca544100c02e880c04a11080e00003000041c003040c040d00d141b603907050303840d1005802c48a540240b2503d070a03c1002c52804 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 681513570 1250 681512320 681512323
    0xd14030f091e010e0105011509090b15120402090709050d17040f06020610061d01110c0306090c031605150c01060506030a0e150f0c070201050405030a0303062402 71
    0x381030484104808000149000801e1040d0350700b5140d140c805070300c03504081d0a10340c0070b0000700c09501565403800d4000541e03004090400c1c41070200a0b00d46161041c9021211001001012039071a0001050303c8901105104c181c01011108d000d0b0380004000d04003401488042079004004e907051007102503013400a569040c1481000e6940520812a01070901101070007501855208500c100580d2101044194010402d075104100c0b00c00c4039007040382e940300708031b4800170315001c00340700200501c01c1440c09501c9041c9803020001c00038102e0701215401c0700442d2820034100d402d81540d410001c4240384d245400d01c949400040e0940c85008410304060004055181261040030703551400a0400326403207086d0440c20040c0001005103071a840c0908051010384080f68400e0b02034003599041c02c0050340001d600b58092500e60f02100015a00d41c4c65a0107140c1c490403044c0d050100600000580c0e035410404201010f1184d94040b40380c500d400002c0c40310391801c0440700c02207061141c2d890302d09a030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 681514820 1250 681513570 681513577
    0x51509010b090f0d030905031014070e28050a0915091e0501030b04060e2a01020c0a032303120c0703032705070f060c0f0305121302030d14 61
    0x800c03001541e20b289640c00656042104010160064402c10a12003030503008003401d002c8410590a64048603903d0300c802c02210350804031210080c103402c1c045080716100d40d0b81c00f140200c0241010b04030b010031010541e44000b0041c054144400042d800380030382d0074031022000007882031b0b82092150003020910181c0340629030043c00f90302540c4500070707078000c4a0360750040054080003008104a58413814100840c1204407070688101d814440ea100a01c00009041407010401041c40300c6080e640c611030b48000480140031070b04600c5103200496681d0349407002c03080114030425543c5900f50091040f05040c1542c0d03402c42c030703450b00709002c41d003a070945140c95580c1c0308000552079952a03201e498181d0040c801c43c118100c401181160304102c01781c1e1b020003411094007401c125507845540c0d00f0301c0c0c0b103030201d03c1c090310b80003c080304101d2001840c140340d030f400210b209080450804403c0190546000000c0740c10710302240c003034008103043d41020b00203070140c0360030741c038110300141d425107590304d018070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 681516070 1250 681514820 681514829
    0x2120c01120b0109150309020a030f03030b06030f060d06020408010c0c05010c05030c0a05030a0603061a010306140604050d1511040314070303050301050f0d150f0e06060a0b0d0f02190305150901 85
    0x117041401803001c14030a90100c81100d9000303020642042e02c0c2d0400350305c0740d1005030085022a02d8a00120002d1400b80240c901c114407109152002e07030f55100c107000700710010f0081162840d800307004c0440c1c6a6000c1c050040403914603552001086060f0174620300b56460b1106840500201b0024040361040407404c50302e50050302d0801030f43d203803180f4200c0030041c00a5400640f07400d11b0324032540880f5051a0103446c403080245da003400034a440d200e01c41c000150080c8090762048d0301300001c104a0500c80c00d8484414060a41d01381c080039140015801d4441c844451119610000760a2041058685003100f80e122083d0003030101e2070540e80c020744144818020030744900803200e410012581e400481024131035100e0340550014070402c0541016102e10382006541c1802c1c01c000d0200c05800140a502c41c00340106182000361800c43c081c61a5481000604c25064846d0308010900d503070b0380020b21070703008160888840c1884a0b200102140c00140840e00c4a9800303000d006542d41d81c03204120f041d503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 681517320 1250 681516070 681516089
    0x21160b07080909090f0a0b060118060f111c080402120f0a150905010f0518060f040209040318030b0a110304030905060a020309090109150b0a020a110a0302120c01120b0109 75
    0x4e0f101d10010602c1d08544504a1001c1d1003092003030810886a002d40394040c00080c2c85001200c034400c1c3c0062041c18042c001d80d0001486014800c6c0980d00c17848289a0410200003510111080c46c2000d00c504560234035000c1c04181034100f8030085007000c0c00c100e100010a04082c2503508540154562217007c0880041c1047c140640034071503400d81a400003000d1940719008101c9659211a40409070600f103030400312a010070350031107031000030224400b0f10404000300700d41007a590740c0d82080b40c5070002900c140d042050940320341da200c400707407000300021b540560f01d070440e140b030200101d800340c0c0c0d064018a04160800d2042c4400290010101c8040e14411120240c48a01301d0004901d5070040701c6009902c815100c0002440d810315510106461501075000c00c501500c4e103054810a114210341c020040e4494011a00440d10014040b10100710040101262568030b4000640c10113560300070708655080752121075002d40c1c0001450001800c0880284010031b0440000303400b003038085c031928018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 681518570 1250 681517320 681517339
    0xf24080604170408030a1806021618060302030d0c02100c020603190b04020706140a0213270504150b01091805150a060203030915060d0206070221160b070809 69
    0x100e21600143c5000d0622001200e484000050005010300514411040b810564503808210349201090904414140003440f1011514001a00341d0396011402110f40c02d42c1e403039078040f0050350300748441031320700389203580f081400242c0b401004001000701044209100040c40c801c0010b0311010180d0b9480304940c0c0729550061300340c104541c050074090140c507a119200141d903200300b0040c4da10814040c000071000c81032698a91041004038420030705082c12464000dd41000049400c0d0100c102e2121004546a40a040d036044102035070001d490440d469040b1501c8240090500c1c40f0703058424801b46010030500c0c1c580107090442c10017841d2140c80413600d5030001280c902401c0100000600c010f8101c8031415610700009480342c00a544039007060040000400342c50b40980790346401403030700038404541c8901c7c40e0701308140e40c0d02c0b803017040f42c0250140d25a002c114004840d040c2c803401e150405001300d00d5018106102c41c0d15150450480c0080a1108901003084442994014039055030390348107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 681519820 1250 681518570 681518603
    0x30411060901091a1b0d0507081b01051503012901110f0a030513060503090c0d0302101b030c03020309061b0403050d0504060809030c10110405040f24080604 69
    0xd40b540340b03420000791021041507408108540d24024000075601066243c1802217028030141c82da19804010070009209108c2c07a0040f400e0304005140700c400010f2426050a94220510300b952421030f0155041c007605030140e40c1e6401c0c28020011171a440140042c6041000345040150100c41500581084000a465040e480040150040c1140d045c41110100c00f0380346001130003503100c0c00c0d1041102c55180340000300d03580102d003904d0103804a84090606404d1110034081c510300700c1c01040e0b046101e1201c0f050002c1d0202e2280d040301c107008002c8034070607202c00f0710007a0584104650400030140b04000b0032005403800b040c240d400006012085030743d100d0f2141d04491038000c1d030300090b0850140141030b64800340c110005204542403500c885e040b9569682007070b5280e000d10481000c40b500701008154503c59107500026450450260322410940c03500d002c2000c40d41a4030300000c0e001e40c2c585180301d40c00d07040061030f5100b100040d04801441d0510740c3e02500d40102800007024010b01035445034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 681521070 1250 681519820 681519827
    0x11e02030c09150a17160503070e1002010b010e010e0904060b0303071401051006090b071212020a02070807090e030a0f0e0d030e150f041e03020406060801060311030411060901 77
    0x40d8032410081074071240070703080c801c2c654441e071086140070f020074100b42c20343c178010100b481800e01c40d190400c002c1d6480c1c1d85400c82602c203030780010720040422100d022a041540c1d9880c9094407a6003280e80001007045000c40054040e40d0f501d82d1803814080e079254001c84a55810b074034698001d5102c0c00104036503032108042032842c090300c0c8000b88282d90007101d80f2612901548094403510900710701e921400e0741e4040c02e0301c3d01200c50142404c503000400025000c29070141c0c40b02a84c0c01c1131301d02003000303007030b841941d0080781c1001d89500300681060404006c025000c000150240030108001c0240e5085040d15903600d114a8586100b4020200c024008113805400341ca0360700c2c840541440032008030b80c50020a01c12203130001910a000206038903903070454036811b03100c0d96204200202d2400341024403007500c4a4101d0210380400300c00442c04401621030340200d81c0280441c1e11040007550501ca005000e03110946100404070a040c010400440c840302e01034040c0c101d003600c1840e5183c5d09800106d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 681522320 1250 681521070 681521077
    0x90204060902070b0a0f061401030518070f030b010f05031c05090a12020405160f030902030a02210d020118020d02040e0105010f091107020d1101170703050604060503011e02030c 78
    0x80e203205101283c050240803041d106503124401c420400c010380085020058119100342c00b41c402030b031b6841c243c03001c11540658805d41c0c005038141843c0c044941401e18031894041c10350002d030080c20082000700204181840250301424181c00301420060900c801b190382c0d4000805504034883d12507040100380740c090004c1b41d0401001602e08400705840b0501201d00d154040070480c000c0b45443d0000c0d207030060200070f0601510007541d56035141c62507160220040c0205880c242c1c1c0c076001d005518401a0b540c035030610301000703040240340400e000c420300590a121000c05060156410404480f4680800500345d40c5800da04581e000000bd80e01e00210b002004c0000c0240c2070340d03203050b00114800c210007103000c04490300120140a00382a912011500340170326413000b900280034070203c0b0002081d40306001e00718541890402c044c2d000740060000c030080f0942d89080440c0d030750001c3c040d01d800d040c0601c0c8080c0205500902000c1a04003152034118450828028090340c00b2000c110f100324041e044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 681523570 1250 681522320 681522329
    0x140a0503040c091b0f081b03090f03190201050c070317180a0501051b211b070b010303020c0108040b1807080f06010f150207060c0201030213060503040507171009020406 74
    0x80100304015406250010310f1310b01207202003a00c0400c0200024443e0b01014400c0c80c00950a10038217442460000c0c0640010304500034500680c0040a1000c900300068030703600034400683c0d05100f003140000307401c540e0301070400c01420a0800801c000301ea0810310000d100500d03650004c0c110340e100341501d2a49020011444182d004000d21032084c0001500300901030140302c1e12034118102e40600480d400d01c91140842100100480e043c2250080d0b08143c0342c2c0104402840d20120041103441111980520004c8442001200052060650421980750000320a00300242242015111688500c00041401e40419091800b00601e144c1c00c0c0400c1e001400700501f00c2e030034612800c3d61961548000d0090244401da5440c0000d415803071a00c4664011a49801408a0500f4440c08803080540d002c1d060341410b40070450304a801017240c040b0401803c0554950381c5a042501e00300b4140b034100ea10801400000312200c059440c0c0105400441e081c22500000d246407451011801070305440c1e01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 681524820 1250 681523570 681523589
    0x1b050d1e1202030309010509010612020108040f0206040f030b060306070912050c0301050c04090f1b080c040b070606051c0c2106020f030106090e01030c05010c0f0f051606140a0503040c 81
    0x9100c1400e0b900080914060f03107610b4000d00240c0d44003046d680c01c032a8944504402100300001540155020300c15568006d40108010030b04124607070042600c0c0d078801c1e0b00203264608800805c20510540c0841d0f580c100d4001c07006032605082511009181130f1590042c2030706150a0000c0e0b208120040050200014000c0c0003171001d0714001203040f5464200d0711480320b40e03030b00381008502d08111911038140002c8145591030740f29100f0880840324100001c0c558842c40c1400c10021540c030700307504042c2482c0b62203108040b82084c01c10062040c0280c15003803440f4052440e01d10000051400c112003003c0c1d4182031080701c8019603111707036034400700c142e8400905211310004403441100071100055068554a4417000c2d019030340d0300c5481c10017040921000c1e002001d00241070000b0340c4107800d000c8072180950b0141c0030b421095150100703d00d5644100701d459030f02c60080310440d14642d0b51520002c00c2c29044c102822900007800000b24455201c28104010002002a04000007540d0032000b42c032410f00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 681526070 1250 681524820 681524843
    0x4020d060e0328112a0307030f0b150f0d080309011104080a0b09030a0f0c17180a08011a0907020f0d05070204050c030114040c03060b161b050d1e 64
    0xb066908a038001c0303401c3c1c0000a8280200030300036540050502a1058900003000d040340009a900240010366440994503025158002001c0f8800403402c01d4101e0040152801c20705081484005580c084031260380556401c010400301640d4680d4001e201d981c02550700e90796036a800c440d06006204405480a04600226003ca0f600000141e01a88640720b00700500c0e103501c3d400082903890080c1209400040c12894038204131512034900311900c24810790980d06401100303405002c072030704000741c80f5440e120094103001062030488510b000404840703000300002d511010541002002170002a400341701a0070100d4451442001707490200c035100820f80310941200d8000074025800054164891414900868060030b104400c480c102e444c00c85051002c060644140b0019019000d25a01495a20200001e460801c24010900700c10900e0405050401626111240080d1080300061036243c121042c0b12580300c940c24140c8890f0001142d07084111840e00c1145d02c040d04c0d1000a00244500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 681527320 1250 681526070 681526117
    0x1303020319051e0d0606030b061603140d0506092a070f121d1017100e07020102070512040501140715090b0402010e0906010e1003060e0c040302150304020d060e03 71
    0x94080c0c294214801018031485d60780341422006d9450b035406155002d03500300141c0c03502d07010708034044583c41e1180c10704080d0850000c0254403107411450341e0514041c0c442e01040a00d15164080c81e920101c0d1680428a401049181c1e1403111446c1c0c240681c0b00c500007801c1c50500c19955000a150781e8802580c8040c440640c0c40148007000f132841001054009002d0403110b45024155014220019505c0d10010391032a06d403803000010141032000703404450741001c100101e00c111030a102e0100d40e00003503651000c074601585401701000c003000056009001c1404940e0340311100c860b040144005454542c6c00b1400c1c440c103061440d03101c100c403103840c09840c201001180c0342d01e148104c3c001d880781811240e081c0c007802114401243c11034000344607860302c941c092402103039901e8291030914002a10765180d242e000b10b801c60523611042d4054011a08200b1894a603000441c1c00d195020081e08605065000c00d2140b01030141c001d00c56611b0700d843c0002d1304010405d4540200c084000500607001c017 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 681528570 1250 681527320 681527377
    0xf07060b03062d0c070203010e0c030705030106150f020708010606020105040209130f080a02071a0d0c09080a060b060d14190b01050306040b0d17040806130302031905 73
    0x1501040c0c007a00410b00040d426000d460880d002d140d1030516140c0c5106488005840020b1005013281c2e02258240080405078800340700348100c110144000b044055565010075280800c0303944110700c641c1c104041801000046078003003404981341d040c05204070030360940c140c0c2040b0041d0803503c6250720707186000811580c1500018010b9000340c1e4000f40d5520faa801d00c544114060348050b003101010806000098030300f9008000d010810b1040e580e82da504c40d1050b5035140304602ca503412070b010125803003141d40f49074810602c401d07065042084002d450400354684a200000000d03088540e1500ea03a00c5a132034040072598000c102c2c420800103841c00e18150f80b4000429110000f800e0806908603d058a00d07104120003000142c48440c15681c500c410000604040102c0e42e801403001074880000508000200c2c9036284031600d11030311142094411450000d0007080c565089800c08541404290040121031042a18424040c00409484020340749445400c00c3c41030b40020010b11440700202 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 681529820 1250 681528570 681528581
    0x9030f0b0a050709032f1c1103032a0a150218060405030a0209040f020a060507060f06150315080d0207051c020f100306031a0708070819110f0706 64
    0x3410301000a600d82810850b10400c00d0b000c010320a6030301c032a820101e80c8070600801078094085481c1c40c2415244000307c1e80d00c00074000300d1800313804003005100401894040350019110f0130b0b4000e505203402000149549040c0301c1c111460000c0c82000007000240c14811143c4594100030b03e079660005103000c480c004d5221800400c07800c0780b203000703684203864014212011100d00130020290b03451a502000020000940211000102c41480358010b8940344d08079401401103071a8142c441030700c0d052050556840c20044030165240001c14050403a46d00303403424100ca200d103000035140f141000c0074810341006822610492003882d000d040d00c141d0006101e400e0701c5065400c00400407082580075527a045003200250f00003130503041a034103800c0c000b64240c0c24500e00d10700450815034a0726000d40005410294400c00030881042100b009e0300000d08603000015894421883c2c549071031f04071404094454000d128a4841c071800d031115003040d069695081d03c0b221115514402450b000d0000c06 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 681531070 1250 681529820 681529831
    0x91c09050325050609010507050703030302130909020901060f050912030d20040b07051f0203040b0105180a0b010c08030a0c27090f0603060e1f020a1209020109030f0b 73
    0x81080c041000e442d890b2101da5498070844452940910b00381002c2048030b4000c07080850400c07900f0700030b050105808001d100010b501a8400607034a01f00352015002c4840e66401c08900b06040140480c0141ca5880809046501034074140c07401c116403640c222440e102d251441a4004460304052910403008001002c800c5890030f0100200d04885441e45502143d0000c260749446040c001013005032614802840c11358424010b4407150040044c6024005105001c0e140070a64044104003c124084502c6805020f0854840d000f030000c0300b00910003544001d0945603000d071110f401d0030040c1d001d00344003e18107500100140d207034605062060000d1494424178400100000e141010f04500d91500001e00000102c501c0609820000850064807142c801091065680c0b100000800e00700d01c260882400c40101500c0a22003003a4401c1d810454081425081841080424962500300400300314000512a02240300440c2c1e0005940654066001400d0070503000d130044104508045581c1c4501c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 681532320 1250 681531070 681531073
    0x2060f190f05191808030a0212070906020c01050301080a02010c02040213030f1e081b03041205030703030f05070c0f050703061107061a13150b19020132091c090503 72
    0x2280c4210b80042911280384482c500d8654400c0c00c400400c4400c4001e47c0e000ca80800003520303103408456080c0055004030b5000000410015003031001a40c14480307d02c0010003440c11070700315414079500350748440013004000d050100c0c0140f00c10454403540c054542e8003100c4c2800408240d940d0401c8a00c841e1341d29404c5801d44e00000034281e03620040305048039441c0c0c20600345818105829181d0070012000303581520309100a00c40003404500442e40016814400e03070246448071000d04d0040c0640300140350070800d45003400108a20184e100c0b40c00c2c00c07116040a04080048190f0410b1420b002d85500064076460501c3da000b010514090010002c0034881c1004100002d139444a13802d0340f000e114030f075583c088100b00520080c51129041001020301d415003001c10707590703a03003100300180c0e20000c666616a2501180c041803143c082c4141120001101c00c4500305c00c0070140700c0382c102c135440c1c000d02100d41000e2011a00c000c908018003a4049601e400c1d0b05600140908c0291030180a8480d0a00c01d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 681533570 1250 681532320 681532351
    0x106061d04050915040606030c0b0706140c1c020906030c120109020f2a0d0908070609050a0501051c050a1b0e0108181203010e06091602060f190f05 65
    0x40d007010700c5414807940c4060058480403c1d0420356082c000009081543d80e03d4440d0030100209040d518003400412000b01d2141d43c9400c00d10388042500c030904405050606070b5420020018160402c0b0354034100341c1869a10300440041000c0000c2c0500751000360030400101c10841c000b14102c0c02410301c112008125000c9a0740c40c8d0b0108182d10610140001e00601800008403e4000d094000c80c514450380824140c4584010550310380b40910340c0013800181038041c104405801404607201602d900d1805900103400c207130200302405d8143c41014100000090008280402180144030003507401c10b00b03006a052000110000e4105044c040001080004082100034002c6158012031241038450030000d0391740c4260710351402c4c0070414400060148004103064140701400031406002c01410800003424000240107201d0170080c0300049881040b0004044640c00080395a4020001039610302c0c42d540d003540303048048890041940d07156003000c0e4200051003040e0009032040e64454003140302d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 681534820 1250 681533570 681533627
    0x303040f0b0d150602070b09180a050f060d080418060f0801060509060607020d1b09140901060b040308040b090109030204091a071d0402160506131104050411010f020f010606 76
    0x100d030f64041c4541e0b40580d1010404200035403860001c0d200c0700307800400b080c18040030005042c0c4206021150200015903c0003005009445020a250000c20540c0c0c10132000243d640c0740d0026118500034950440968810355078000101d4012034090000b2150500e03069039a101d40302c0c040c0c6214000c49205a040a00045441c20f09406841805800405a00070282c1c60340314001c50103100740c0100500480700a01142040307050107908a800d4076044200018a0601181821507600360481e40c00107a0411042021645c00d030250f405a81a000c902a0394080b40d50041e00d04a4a50380000c0d00141400a6038042c03090350016405043c190074940c078155561100c00712004410300d070710000c0d000c00b2607102c540203061550140030000403007944503070581015128685451800c03200601c0025510255808203d0061012072102c8410703103041c03101e810260385106a8000c000a4207041102c1e051003a100641b0810148404101c3c00000700b002503110000100090001c541c40d40c1d008005941203030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 681536070 1250 681534820 681534851
    0xe19030f050901140a0e0a060903201807020106050901030803090c1020010b040f0b0a1a0315060d1e0608031201030605060105040801230717010e060303040f0b0d 71
    0x114001c00507581d034111021090320130b982d03c0c1c1001c1c42c0102000540041d808030364603021290400b40c2180d844001c3e03072500d5898181d5500300039043c100030740a0140307011003168517038401889814011020300029a5600d000883c010402e6a01c0254803095440000044c0203040e0002c601444585050f82c1460800d00e0a0021b130780e40781540c1030005444404110400500b0310a00200c898202001062803a80240040d0030744843c0c03610541c0e00c0355264445c1165203409034601e0000c0000362240c1004002c00030300406a40001420080c8104a4a00040341950303060211038113018218000c102c8001ca1b1240c850190721040c08030a40344c0d10b80680030034699800020b513111316103c003040d50501d0303003543c0d183c5000d04000b405081c1030001c1484003040068080c080c1c0420340c007034120300200c8104289141d0f80c2145019007100c0034490900003100c05c2031124804241515002c2403c074540c0e4540b0300c042891445950701c820044a030f032003070216007419000d004000d1134044010900c0341002c210401c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 681537320 1250 681536070 681536077
    0xa030e010e0d1101020d0203010312032d0911090411100903080d0f020417010515010305040206122203080f07050c0d0806150d14090c0d080d0e19030f05 67
    0x1c059210400c1000300512032401158440c500c20005403c0640d5580c401040e60420b030012203030861009240c1c42c034281d25100707810311507030711260500b104510040c602d44201c81c910580f04616486280c40b40500100001d590520040506085854540350401d103100c0480301640901c1070291501d040307010382c0300d41c407400c0540b6000703000b092900e8407840d0150020402e5241800d1450303000d02001030b41c4403040300d0040f0403914440004c51649400c0c0140c04a141444c40d515052518180503c0050384500095400350010600e03000c0994450442008084054038808c00c048409010f21004242e4070948640c00340c1290050204161a490720075501406140301896841d4403400c11242902d20600080d038221901405040311004507100300d1901b84c0c03120501d003850603210390300c0c1400d05101031802d55000c0e031030784050000f40380c2100005640004103070025249010100c0c0c11989840741d6484460701d030350729204640304804542c3c0c003c1403a06558100b5004285507284a002c414010400c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 681538570 1250 681537320 681537341
    0xe12040b09011d060406020f060c0f0a050a0c0c090b031009050c010f09080303010902030f13021e1801031212050105010f111011090a12050304091e09080a030e01 71
    0x32070900840100460300000d4844828542c69a020000c1001e9140c500042c00607005503406401d441408980481c85d190014041240050007080140e079010b50b41c1b0103540f8208194a401983c0e0503010500b03c0e4415200d00001d050f680d00844c001500d09003981c800d1144103410382c245c0311185114008202101c1c0074140141035a00034000c1401c0720341c81580010000a0a824030b8981c01c0c0c0c9400c0c035907142d074200b40c0002c00f00c0e941c00401d100e800e0400d03801c1c01e5405518850040c0e41640c003507000c03501046406241344110303001d540200b161552548001c403511200600c280f00e856a60703003001c10640303108010083c0401c1041d1020003c8074240d00845041e40d4060b15180100d40e80444101c801000c9043d000481d8040c0400b900303c0306005004900f17140c0303080e0015644440c034040c200280c1040c0ca41c04111b062090f11800710009001009803400c0301c00d0440d001500c00f4800c00008405001c1001c00c440ca40c0c5807440100802404801514807810a617034100401410081030070f0807902402807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 681539820 1250 681538570 681538589
    0x1b061214011211060f030702071a0901090902031305120d0b0108012315070c0806060321030702010e10021c06120b04020406091406041521050a150e1204 67
    0x2d044010801c5042c41c804000d1015024910b0418020082c0c1c0042e00300f5116000160040003041011381c4e49280040300c548041241907280030001c0300003030020112032080c18110b07600403001a221060758085110550b420406a0700c40f821400d8100d600f99001038075414800d46000c00c169420b5108151582c140c0d1003020803181002000448011107001d0344924035030100c501e40948401c001c1074005481c0070b500c140f810144950410845904201006182500075403001203941d0068811f201000f14403018a9a15030b900d071030303a6008074090111032280c01704500c100014100e21005c1d0b603004202c07100c0d0304407010090542d441c00101c203803406032082086585400020b14081410852b20310b07001440100000303007240e1384034200429200040c82c0451010b4000003001030038107043c021801c41010030320210b0900e070301b08052040401282c0c0b60580e103206400da0b2410421008101c0e14480d030b50002c41004400303c41d568540060401c0c020100f14902550f503202200d44070307100558003664070a41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 681541070 1250 681539820 681539849
    0x5071401020a090902030c040b040803030402010906023903030307050c0c0f010f03020310051909230403050706060b0d380f0a050907020105061002190f1b06121401 72
    0x4c4c4c120000c1c0d040a0000e0b0813035281040001000511075000740010604400955160310301800098804100355000d503055402c03800740250b01d4089140402c4000c41100460250140b4540615041c09035a29015800d80310000901c0400b0780c001021345a65103590084075005031482c0c5c103100c40345604401e07a5020074140a40281c0307081c00380d000b075980200ca40c0010351529640b0000174050703050f01c2e07500b080c1c49844980103101003a002c0c0102d02c003003a01c00f00e400c108051810103440e00c840000700040d08204010401d80208a52a00448010701359129119111aa40c0c6100ca00610178030f0600c820103200355000900b00d054206a5020109000c074419102c0017101003404040d0340380d8400c09500c80301144000c50140e032611003547c060685075000003901e16001091042103001c000c00f800555200b03220340f014800404521144055106056441074609407902180704690a45404100740d8800e00c0418220342c4400180c0700c84208242c24412071b41c1508403060a15000e0260071045c1c25100f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 681542320 1250 681541070 681541079
    0x308010312120c0302310306020334090512060a0f06030512120912030c090103090f030c05070611030d020906043303050f06010c021c0305071401020a09 67
    0x6949880703181c4094100003041000e001c50142c00c80d808072000201103940810a40048456040d0f030020300038620402c1140062041141022076026100003406240c00000042030100f02814151466140c03401c0c4a03848100400000c00c02803412000c00000345080600007110324140e41d100220183d14806400251168054000641455203075020304036200e0780000001081048a100380e0b1812200301a11603600040c2007810b01e00240c95110320780d10404202805000300d80842e6041000c02d071032107546e14900c500580103000114805030540c14154101014160000381d0500300c14460700584640310384444081d5007541d0f900c000600290310500540241d12015401400280001040c4604040d0b84101e00f0300c058900c00890840c004200404a03200d055002081c10100141d04041c00f0600c3c00080065500744004c00c25410440510010019500c50030208079021a00f022021301020042c10050240d5211500c02c8424169200b1410060360040c401e071181c036019070b5644036072280b40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 681543570 1250 681542320 681542333
    0x2010c03140f061507050c0a0b121f031e02040c0203160f05010603080f1b071802090a0806070e090915010605030c0d180501050f042604170601150c03080103 69
    0x3d1007a6004000c42003c1d2290709400400f404031144240c0040803903102c207c00340220061a940302c4045510f040c0b003440544003510140b5075004020312000c4d091051881005010a1541c2d03002401103180d56160f54034121038440484d50550094409118030340300034004994138421280c188100c40b07400c01c0294009400f11603c0d50360640650000700304a51a41c8030701015500004401d01d400400142c0310050034000d03143d001503560f00c2800780070907526014103070b0a84003071801e0842a460340016003c1440d03507003030310030030150100308125095845d00d09400391604041551480c441c007080d50004207910313800a400e14211010190280072079203400310039907039500054141a1202414418042806040c1c800c16071251502503240801384031500b480c44c21a00c002d000030344c0c040c0700d0400304008a1114000c20132805085100039001461078168039038580120381050803a9a000d4004403003d850019403d416217802500c2d032801c41010178000e81e0303052056a4020042000c85c0010404a00e4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 681544820 1250 681543570 681543601
    0x1d0f010309050304142d0f0105190503010f29030705120702070512030a0e150708030a0f05090318010e04090b07120c020307020a0302040b01020c06130602010c0314 72
    0x18100420740340019501d40f030440e00a50000e0b0084040891084610701d400060004454444101802c503a540c225402c403440e0645043c480c002d40d040603002d00c10b03900c1031013103c9000c0fa8040005405070100da0340100254800c0c412800e0151a1920118400300c003504d00031020040b55600119000c05287d02c9921074000508400500a090087c501900c1c2c0c80c40c00c06111b086154054240303242001c2c00c005441d0b041c412280d0302e550041c054205429004030198030041000c42d40002d8a0b040c014540365584129034006041407000700c00e029028485401103400c50b030b51060144030a90f101c1c1c107502d42e00c0c02410303680840f51000101051980d400344002c0405890040c0c008900d011240d10b54404001040d1581800248210450307031841d0402e21940c0744260300307071020b0b518007043da0700022401901030001a100303e80c0c400c17404605a008009802e142d09000d1718045e10740c0c14060281603441001d100303440140d428001000d80052080c416150403103034100d2081d030a40c541e02e040e01c403400b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 681546070 1250 681544820 681544849
    0x4020405040201030b0a140102120703231b031815030103060506040f0614010806040e0705010315080118051903090e07020c040f2004052103070f060e0d1d 68
    0x42c0c1d80c032007043da17540302c0c0781021002e88800210005001e1030740000a240610030342c080e070304001d07042c0820000268408008121451001d01740211140c400784400840d00c10f08461309074400384207038400003074040800030300b0001081e0480044408026018006005038805040011420800050000441c0d039440309421007005040000e1000b00c0086080495520f500820f00e5281c04011124440da480300690b41e014805403424031004039000c609695524940c0121070615440300c0c42e203800c0c41101e0741c2c03001c0117059500003442480c60f4611001001e40d01c0c98815145030141016059000c0d0100c2c252607035140d1f059580c0000e44c5d00d0300d0044006c1540180070324085009981c00100c0c00c2e0f880d801100201240d50a00146546035058801c168a140d114040c0001070300f40800c000507954503010701c0000b0032400c82d0345900d0609120140c29840b0300c05004100440d02100c100c01c2c4052603100c0c010b00000741089030100f06160382c080c0c0f40282d0408511000205000910300c00d800d000d0b41002060 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 681547320 1250 681546070 681546077
    0x20601120606080a0b042a21020d080a080906010819061b18050301090f03050306010216030c09050a0e0a110406121a06090906060d03120509150901060b0304020405040201 75
    0xc0e91110083c41c1458110081601d03418105401d00080c4038860100c040c0000b41440125800306103c0001c1101c81d40c5031040e1150310004821100f154001011070f284800d50003800300c18041d00c18545001150004801000007801201c0042c003001e00015000d8140d840300002031142d120324101e0005840800d076000c864180d1603c60f0848900f41071000803209020a4030f507510110301014081118005503400180302e42c3c1400310107000700d8004809204429010300d0156540d5070307a0300050b4501000066036007504903580d80c0c0041488065014a020364129800c24040f80c1c80d0300502500795614031224528582180e26041c00041d0b884d10980506500988045105a900e010a16030a064584151004000c020004003011000320406071b21040860b8404400d040040705c8540d0360a0092046010300a6a9510003d06010385c001e19684168001c0521643c40c0c10320b040b40c0c864109001c00008080300c8008108129410301500040d11408600282190303260780810000d4140030f48140d050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 681548570 1250 681547320 681547331
    0x1608060907050f131a0f04050f190b030906010603060302031f06080724050708121e07120e0303070c17130308130e0105061603140307020f15070206011206 68
    0x5036107003c0050488003c42c8001244107034175218454624800b9880d1071901c1050400000d0f1454050340c054405584042da100c0c0204032000000c04d154040e00003e0780340800d4400000a40b05a40c907000390b10401d035400540d510b0b43d903204000d401340d0303445000c029890780000c00082ea80000f1685490200812220b010030080d54491425040004c141c214150b517418030400440229080380e000801d82c4890b1400300e00d04841d54882081c98000c58190610a4456001061005c0c4081603096451441d40f2034450290500150160090400305400d00c441410125410103080010007624804d500300d440e204503d61965131f400d294100c104e5030685801c00e040c40b2464030203c06c0b8145001451180341400c0d90781d0500d0300c0344aa9440c40d64000c2819112420040c40f083d100c00b025600b085212840d07801c5e66241a14065545c040701003180c8070640f4000c82041340d61640000c2e0740d90100800c4064030820f80002285030002d41c01218400056400b000c0108040201007801c01d800034024500043c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 681549820 1250 681548570 681548587
    0xa03091e09020a0c061d0f0706050417030d0609140a0c05090105210405032106030a0605130f060f0e0c03030415020a0804030b0f090a0b0c03190501090203010e160806090705 76
    0xc0b40d90400040c1c8100c082018014006c14080052140c019020401807056a00c6e01c0b0006010f4419809030074803a01614449000c250300410540d8160010050244074481c0c981039414020070042502091000c1c1c03c80c08144114454440c184c55445190303200e9207031181200055500f07034000c004020300b0048660120320074002c0080170034051413090300956a00e214804028005010161480c094002080188140b5590000d544450142d100e1804500ca5071080092260500c0110b0701400d61950a020113007040440d500c00c1032032444407042004036403560b0307074407036030b644440f00c86550141c0c8204800e024070311544100c101c260b20745104a588a1200d80d50304642c03038011741c0c411141d44c0f9000c0b043c0109241c24544c01e070340c0a04140010304902c0c8c030310303202d090000c1d402078800310489800002181c00c0c560403107141c950201e54620b061040b56501c4980c480290300911804a48000010106030718035405a000341103030b071803070f0744200481d07c5990400c00c01d10070143c8000240802045080f1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 681551070 1250 681549820 681549833
    0x40515150c100218010207080a030f1215030203010507030908031f230406050f03030d0e160f08060604090503070821040b06030f011e0506040b120a03091e09020a0c 72
    0xb07a0741402100250301d070316458101240e40d4021545181c1950003400303051110101c00a0400b15040d0540703004e000d410343c50702c01034650010100038107040c10306010350400703a500c5840352041101e1017138000700301c999110b85044003100c914202c020410401003010403c6c2b4103607502c90220115080f68840038060b9a0843e07100884003074212089110a0304c0510116407a251240600402050f201c08101d50651000282c0341d02c034000b003624580f0b50762a60300381b115100b0403d10622003881401840042d48642c8407000b03440c01445056030034820303080020002d00b03003800b460720f200d0342c800021402c150b00b5a4404000790030903807500149c1c03494000150318546002c40d43c140294000c10041465080c52001e05003042485150041c0c660706054080c51142c44040e091540c80030200e2001609455850001c1c000d00028010245e01800d000300e018401705c400f08800003e24400d4a9a2240c56500e03000f8031046c8041e00c40c8584e0b91710a50000700003581c1142c00615403c0d04601c0d0181d9440c5140c0c2d60007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 681552320 1250 681551070 681551083
    0x3030e0f060307170a0603030c080d060b0c01061701020708040314150103060c02061b181206040302010605130605030d0309141e150402150f0c121305040515150c 71
    0xd800a140c0240e000e61192000e00d035660030175424403041c44400e0541c0c0703000e00085085400106003442c0041c807182440040d90150028000e0a0402a5200d101d00d020b5400703041c05004100109902e40741280a181d014401c031445940d004d060b5606080c0b641e110680d44007903440d4080103902810014000041c2a0300910303001c1d6108400c00610a0070b5150001c0c546500245021591211900c40f641400c521030240d078866080c002c44c540030600b5400c0454902015880d0100c1240b14072828001050f406400400542d5801e64a41542c1103c00184805403081c034852a90941c0188021103600341c4250400c0c41c400d03000320f003071140000b9049096440d01021032011b441c0410742500003220102c003403001300c244040c1944800103030f04041d00003510306e1007600203e0721118400212610064481d40544180307a41e038a01303666101c03000111401c0e06600040100d040040055030206040c07034580f003090b025040300f05100042c20280b2081c0031070f41e20002005070070703c80300b407228000280080062 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 681553570 1250 681552320 681552331
    0x3030201021305010e0a091805010e0d022806200c060a0606050f030a051503060109050609100e0703090507051002011a0d080d0b04060e040803070906020d02030403030e0f0603 77
    0x16a076482c402607240203403200c2e03002181081179503480d4550503035800d03009006603407100d0b100107801d00c401c00380c5c00705440c00280004d125500307103002000c9038034011904450700201c640070760f84c0b03030860140e86c09074503807892180d05048500320b1802404214643e008500003100b9031390301013004481d10a035403180d800480340102c082d4002810001035160301d004480c02081241071130760510080a0b0b0403080ca0000400060905e0b549900045543c2901040e1400040c03002c2d09071895561074124000152008a0341203004409040c046000e032030740d0004440850f400c150380c0380075940340c12100310b019204103001076070140300e00314000c60300365102e9400941640030f030340001520104541c0b580609500181c0c030944503c005064150118016000315004041e9281b0300003826403034040020001c210b40d0b0005003e010f00e01040004001c0c00c0d20041d800341f1200e403142c0c0e514658550080ba55180c2510708540180c100b80b2080000034081d00e03038011800d4000301000a40380c40000071a0440c1c008481 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 681554820 1250 681553570 681553573
    0x1e07051f0504030917100207151b0206010e04020607060902120f03090103180b0103080703140f070302100b36130311030a02030f0306040209030114060f0a0311010c051204030302 78
    0x240001c0540082031320380288034080c1c800407104503000303d441d1038010100000214a0b000a07400042000d011411031103250020800c219500c2c6150942d0074240c501002480948181000454403201e850204ea01c0f03203030300411541c0b410001c5d658a8000d420028400c030f800c98408220b01c42445030038021244550b101c0c200447d1a11110b000040a50b48031140601c21040030107029800300e02c102c2c030054190b039008071030569980b1a52030215500844c042d044100000042002d809010a2400900c0524040d90071100031501c0103003064201c904840380150302c010780003210340b040301648070482c2546240000c0008620b01c20341244484560840f00e8a03c003403031100d249010590031031b110015010403070b4015030a00301440300196407071103030f8024080e20760000300015100e0340d107a030100d07204490050000d00803901c00ca90010300d41d44003500c2080c442c60000c82c0350800340c01c01e80c1400044a40102260200408401c01075403400d0180c3c1080d19107000d41141c401c00c3c800484010001580702c1c0d0f0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 681556070 1250 681554820 681554831
    0x3010e010f0b0f2202030c0f0403151d0a1410060e07020d0518091503030703020607030f0903090e07030e0f060718080309100318030e151e07051f 64
    0x10100f01c441e0b115004024030074042c004101480e0300b004044004c5030080440010b070f41e0f0300c540400100d43c0c040d85134241000040007502004202410b40d0030303c49008000014003082c42600820012010764008481081c0c0c4400c06076000711b11401510518030341000700369071120a40508584c01d03245650400b440219000b402d001d00154100b0071401d5000741403030154100982d00c481188441c0d500d2a020748103c8804000c122541c240b071000031401c042c0102229030392580c034074011351106400c0702e0b44030202e4a00020001d40c0e02045c0143c0c150075505699003c180c0d03080021030000340d14060700c54002c0554841c1d0450240310108145054142000010201451f2180700145501e00003000e02c8840705003c0402c109a210000540d4440360741190800c4440c0c2d11441c0c03ca0080500000e0034401283c030030070a0f410b05400c0321116505c0c100664820091080b503a0300c0b00c8051103642c0186601001401032226038411140c06049c6c02442013045d00c0d541139400751003203401c00100c0c0b01000c1c6140d440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 681557320 1250 681556070 681556091
    0xa0c08091915081003060903050906030405100b03190f06090804081b0a0311060d11040b0901020f0f12070515010e220b1b04090c020c0306100f1403010e010f 69
    0x41e07466441e6600310310f4030200034505565903904145051000400c202c0d150190b80b400c050040060300d0140c28080d1000b44c4034905410301c10365442c420002c00312228036103110a400d07400d000c14014030461060804070840f41071580e030240a0380b411300041d03440c1039441c03101d900011030885c002c0006155100040440108518880785007081c0c09030018070500354404200001080d10381c5280908404440c0c10383c440203840303071803802ba020720641001522400200450041c5030680500a9030900307900300c0388844001041256a101000c41810481c2e2280217054807c828040c0140b042c288200155050f00a00c001e00c0c4120f40c2e0203800201e0f2900302001040241c0403030785604e40d18103000c600c081c01c00d000c49480381055506d000c0d105410005d00d81c1c42030300e02c1c170f00707041c045400030013810104000020300e03800002c0d104c01410f12451320070b0141c08089285940e40381e0b000300580d500300d000980100d240020101001c0c100f8003502c0d4055480d800c1c15420210284500214204050404590704440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 681558570 1250 681557320 681557339
    0x91f0b040602070302210a060b1c2405150d02061306120515090a0b180c0901090b1c0903110607030e010c09120609030c08070c0806130201050a0c080919 67
    0xd400d0b030044050315580c6c0d0019182d00011300240d0441d04030500080240c003510200706c103000083c0d42200e80c2c0901c07a580d40200074064000361501b80c22042001481640300da504010389005445125809440300398000640c0780c00c07401c01e15040c2c8001c2c840d62424cc94441000014502070f0b000002059401408034408200780c02001d07481444a59155001c7d0384140001740c01c00e4014202110031a564602030701aa120700c0c0c0c040114048102c01e8002e54600210039065946c401d8000d01d0000c0d4146800040140510094070324030000304031890926414403420303d0042080c0c800c00c0d004c001002882e480750540c00d00c0818001c1071180d501041c1118100503040c25118420030000c100199040c0801040c0c4604020340e203844e501440105020110f42000c44083d00c0207031000d00680300000381442006a0201c0e08422210400305440c03a0b40d481c0100f02d001003c00080c00303400305208111200c0d002e445400c110b81c1c0e0a1043da0508e0400740c503100424020084004c0982c00c688172010280459480d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 681559820 1250 681558570 681558589
    0x20102040f050f01051210180b0315060a0e1306051302030c090c04060809030d050c0a0809010c360b0a03060b030411150904020d02030402040b0d02091f0b040602070302 74
    0x900f5508200b0030b040ca180000e085201d0144401c150600d200082040b1704940b00002c001801591042590b4030007450303212005050b9160101c0c42031088500c0000c04800750400103106180050684141601e401e1003640c07014001050b0341c030070424104141001a00304c0c41503502910b4520f202000c0e0030110700c14140303060162a1000d104902c940c04208001d079912080341e00b903500c00c3c90852910b48903100290724501400c444098428142405c00580881450107041113a503144d030341030425103c5440e99070803101c0c20341d021400110860102100d10780661104000d641115022040d21004010301c544a01d0700f58010942c180b0000603130f0b0001c2581030084002034108072281c031345142030942da80d03010b6000804c0e00c50700640880c0181c030791000b80341c0c09440301d14002030402e41d40c070450380d600c0c0c0001790f04c01c40d4101c2c410340c64103296402604020001c90b040650103005a800d60f16075990f0351503c07806a03030b070f4055050340b510808562081c4141c05003000385001d80080c0002c1d815441080b42018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 681561070 1250 681559820 681559829
    0x9061502120d0e010905060114090c030105030705010305191b030614090402010c170f07020a0b120f09190c030521251407030302060a0c081f0f06020102040f 69
    0x14000d280307000100008104a0303410b180a448001156090414003502600f1400009840383c010400009001489070f040000541c06c12076041e03410365262103186241c1d00080c094660980e2120206002035402a400143c111594031141d5a16107418a01481503c807513840c030b00c8086507122841c1d400150540152000750008400c481e1244040001113400f4502c010070290420109080030000e1201c81010703140b804d4040e2031080e507a0384c0049400102944180e000700d01813801500c1c002561201d1209540c556142c01141c400c40340c030346203854201c00f10090700e01c044600984600031044442d0340aa1040a84101d98800701c2900c0d505046081c1102c0c000c002c3c00d14600700b650750200024410403540311301da52002140903841420102a070309400c00c01c005000703d042040b01c68007982d00041c894202c0f4801c1e030807200a50307140c018074025200641c8030000402e6107140841c078100350380d488648d48003410100882c82d0302d6407285030542c040c042d03600003c0541d50010f011300c8100c2d0004a00000341 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 681562320 1250 681561070 681561073
    0x712030f020a081314120c0d0503010303080f04142406030c09010909051005070309110102010b1c170a08070806060922090203071503140903040608090c090109061502 73
    0x200c5424405421010f006100f8400501501080c008001d21201a03419482c02c2d43e0480352208400c5510154550041d41d12004512401c05503001c0644944112416254560341b04101c039140c0c95492003203108042d00464004030034110203149084104104800702800307242c070104226801c42861050440500b04c02d0007500070000510491311049509030440354500c08c001030f440114200142065155101005004d080905120301103606810028a10340101d0701601c94908880040e0308a902e601c0625401903a06407220388192440b8903141207090140c8400d1110410089048800d03038800b101c1c0d08040b980701c00500c100305510800307055011205441492800c81c18000103260041c5050225441841d80a04503041c000301d41c200780c44c03c0b90b014084400e41c80d150400707103050403100010400001c2c500300f280f0801125840788070380154907543c082c61516081107000c881c2c1040080109040d4811658041c602c0d2700ca0700785182c000c0828150006005c5e0401d00201c1100c820a081030085 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 681563570 1250 681562320 681562327
    0x613030e0a060f0518210615030607030c120c110706030b0d02041d0703060515060310050118120c09060603020306030d1107080703062007151508030712030f02 70
    0x42500000d60b03612805940c20300907101d4008289405c1c01c0d0741130100383c84c0c01c1411768098241d00d035101c1100481102505041d14648eaa600c40b841c2007128881644541c90341c0110041031101d4020390010102060034070308003803a00c541804c036200b600c1c408050840090003100d2446202e4005001e11170191100385400c9c001c0c4001ea0f40024050b01071300340068071840d81c50b05580a125048003aa04150801205403940700d80d490500c800208800c8406440710240303000b0344042c915004041b68400c4212810180c110380c280300046510902c0c8044d03811495840b0080440d118030310300c0310100700c01c0c0316200120165060002000680e412680140e09160050041c02040d640102d00704604171003d16000c1440e5401100c0907180c2a040d620002050082000210030300080e80c004c1541c50b40307072010305100b1400f1190307003059520440c20050981c03d400c01510322000d0860300001405010450000e0b00651181e172458110340c02000e04980100f03103c01340e480902d0309401003100480d140d6104608 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 681564820 1250 681563570 681563579
    0x3010b0f0306040e0d0210050618041205040e01030f0204060927081e04090605060915030601030213120b0a1a0607061d06070e0d030504050103090c05030613030e0a 72
    0x146405425a0080c4104011000510507101c6501588800d10180c040f15031000100a019403211408942510071070308220000b81d06007480c00130f15188610580350040103a4817905d581d030501403000c43e48070812000300b00024100c02807802c00750285000d1810703e0350100c4148104000c503001648941801402c01c0d036040036140c41300700300d0040d4007035a5030700200307011051070420311034450705016501d500e0900b1305024030003c02c00060025103001910422200fa11102000380318010240354690055116140310b6000e1012406990041c0042c10050305009081d0035014190351550081160080c150103190305021070101c2c1c03290490302d000340070440c60004007034500510240d0420344c1c2c0914800605901045040c0d4084858012800446545907003500410b40d10754a0648802000407607045c8035125514200442e170341081e40c1b540b40c513444c0500d00b40054016020003502030b1010300050000203850749050000505c43c243c200000c6800c07104900e000b03088440c400c03505a00400c0514010312 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 681566070 1250 681564820 681564839
    0x8070e06030a02090d0b0a1e0209031f1401061e0801060e041e06090c080903090904060914010f32040b04080d020a030219020609070515040f15020d050301 68
    0x98001c400c0b40c00240e40da6540102241804040da500200042c0250302002104c0d100703a440f4212040200103100d6031190941c0300d00e0240d020f0500310340ea15402c20380507000c4e001d0061401b2b140781e140628001c01c030400b11402c1e054404000364403120102e01caa49a180c038429220240c42268031040c00c144070f055040c00d0004044a041c180f07014021541c034294030081c1d101c40c58441d80c4200107003d0611400b03488080c0200501341c07a484a4010642410202e082808040169083c401c0094000e2400782d03210380f100c0c4040d020208003501c42819024100c04e0505084c0030301245202003040c00701d46a114010000e6080d070310843d03040040110740381c041d68114240c42000743c0040e00400000c42c55101c80c10700b603046200320748050900c14030000f00c803490b032605500944080040301d410454080d90100003a80c68000072581c00900f600724620501240c6054030350500140040001141007135214000c3c41d4031401d02c2c0c0c000340c000c0031000c2d40b02104a030303040140c22541001031800c1e9045500d004d5010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 681567320 1250 681566070 681566077
    0x90f060103020f0c0f15060913082a060603060702070524041e030312050412110319020f0601150801060e1f18090e0c0108040204090b0f0708070e06 65
    0x180d0400d500054520300c0c0220020540d03000c0380300031040d41d081e03400145a440e0b0307131640310114020000d24800002c64a00e0210303542071091070107031503000402100c1c0c0c0d42c829495100070302e41c0000081c00094403c40c0c43c500007500065844010080280f801e18100301480c3c2b041c014542c8046500001041c0000c1d00d440e160006140d05a8080c022244e20313500c0d000d10103024580144c881c40701110400314100844008881c02c8034013a0300c07202511031102e16520240c036000c48000c1c0c10210314450b04503a040c41005001d400c01503440560b41040d5400c0304001d114110340600200590000c440b900300c10105001090043c03d40291040800d015140c000d0045a030510a00061000c1f0010000e40c1d41c07500c403001d1408000380808118070a07800344000e49520a031901050341044c180d800442d10104c14401e5a0b00000c254000f054108500740045039840c41c01801207802c10740b07401c0150001381c104907420b4041d01d0012800142c900d402c1000071704049004242004100d0626141d44454550343d084 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 681568570 1250 681567320 681567331
    0x70209150f0105130506030903130b0a0f050702030c0a0915051207051002070b132103020304050d03050c0d0804031107150f022401081204150e2403060a05090f 70
    0xa440b01101c0200e851011381d035034003846d000203001041202d014008001003148810884101c01140e4031500e0310241c42c0601d80c1107002048200c0e80c0e075200c1d140030b03c0140080030b20090803107a03221150400b1429201240c4d00c900322460311421014410091800150090501900c0a051985d0085130b800d90740d00240c0300e024025441e2154074400d07944240140000b03042c140c115541e80f03c83d41081220704030740314841c0c2d101046001002101c08041c40015000d190381541c025400c20b82070104000c89044550821070a1000c100001904424141304440c1c1c0d80440b502c07204194606410007901d81c07421045aa0411f030401503040c400181d40031028a00d0002900c0c01400d03640061200747d1503e4041a08040c0701d42544e910340e101700030b1913005203058a242e10b0070340f08000d000c06d4500b5a9801140540e03d082d030442c40003152458032031020400c42c00001400c0764440301510b030f82040d0f480c20a00c1203804c404800410059107007000e1079284000c0c00242c60b8000d140c90064075000d02004040c1c035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 681569820 1250 681568570 681568577
    0x120d121a060a09150e0114070c0b0307050d0e06010510050c0d03020d020c0a050d0e030d1b020303090a080604030e0607050c012f06010e100e0a150306020f070209150f01 74
    0x142005428410780a100150858100c0e00b030b480040300b900580200c422580c05d40c0060151000b01000c001d611040d1162998420120000d0508090800700c1e26003004005404004080c840b0340c56220300c900600100f002d900000c0c0001d54180001e011546001c01400c00a00400700160903d01c1c60000c0e8010a5002900c0c0c01a268012824044040c4c428800c0e032a00c10302c58411503005015002c1115041e00318aa2120440010704031306064507400101080c0c40801e031901c407620b8111501d10302d01d10400740700506691801c0c01010005c1c014031490f800840c2541d01841c104001c240e00302c240010191011070704141030010703942c0d030b0030b80e80e5180c40d24050400016407000e9404021042007100206502e00c9403e40c59000c1c1640c80307a407500709101c2d003960803080380d02280000c0d8001d031038a0240c482d2011080c1c03080e91501006c4000e030456020314035411010540007c0801d4441c406000c1c0d5060000d045665407581c0e00400039000b41c040d01c2d645000c4100b2102c41c6207540c3c0e0a120f1046147d003801d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 681571070 1250 681569820 681569827
    0xc090203070203090a03060b1216030204050402030f0d11010b010504030c0b07230102070b060604030f080a1404170d02010b09061c02030106030807021e030307021e120d121a06 77
    0xd0704a0450041403101c54104240203000700420182c1c5d000b0350606c040079151240310340c5107903129a0382c4007039001055041c1c061640d030a10240c109030300f1445c2d0050014040f10119140409c03414a4854940345040c0000d020480046510000b80205250842c09107881800c190558031212280d000c07511030806405000103c45007040002c2426005504064240507540040788035414040e600015081300c4429100002802628002c0169021307603030007042c40302d40c034141c6a0300e12540d0382c4111611410710984403c1e110304400e4139002440544845540c00c4410b80143c0c603440d144c08240360940f001e690400344003612544908690b550710000071500300074801d410214066044003450300c081e4040d408e0480200500c0484c400400344c0e944240c0b56000c428030b100002c008108800301d1034a606820070810315000d8500303160144450f17071160030840c103080d1040000488201a500030201c641e00035800c1885e0f425007000d0440c00c030442c240818041404410568050700c0c0d042c0800610958021 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 681572320 1250 681571070 681571081
    0x9060114031f05011802030c0409021e19171b0d06030b0405070f0b0a020c1318141c1202180607060b0405250f021606050d0605030a0c090203 62
    0x10409900080c10800880709941d0140b070055010b460309009100a91041e82c40032080200103100322841030885062060403c0c0c14000c10303d010303500003007402502c1c02100d00c01000d0840c04000900c100354400b41600c00e1000c69007405050010000844038000c503041e010440c82404002a0f804240c190008040e5039030501c816510040610703800240c41103460704208800c010001402900742e9030b15400140007030395103150142d014862401c1890058100e00c0305040f0a0030039282c09d0010a0b0072030750100c0d00b494400010320290364a0392003600d0480e00311450460309003003403051000e404145031a000520013a000c0142038000403114a074102a400586140c0390760304840c0142d03051200a0005988402904100c4080c00641000d54400c62402c8007213100344000c05081c002c01c10152031b800d07042422810081d40e4080910503060254003c2004198a1000d032410001c003800d015100c441d11108159451002c451843e00032601036446038044101042e03400f07800d1230071203104c500d015079a95941d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 681573570 1250 681572320 681572323
    0x11040b06040f0825050102030a0810030f030c060c05030105012a0b0705071b0e0a180b01180f0504020607080d0b0307090902090f01050f1905060f0a02070e0906011403 73
    0x4560008186504429012400c1800414801130100482100b84030503030084091300011040d61080c1400350f401040303002c4d1000d00a8403215030003040c04011020340e0b9500c0d107407800a111041e90480c0051000030484003084038511a2140c500740d20700c1c02c1821981041c001130200340a0744608003070300408080c50f804008540c0d60040c0c0569001d03061021600f42444064420707004424112504114005040d11030000d00c10708108880008815000c15150607101100034051100e0440c0c140b00d00d4081080881ea4000601d8024201c2058151010160441340740403950060700c24900141404288030141e69001c0968240d075400007030709943d0b054802e00e8a4010243d1003d143e0b05070160309400118032142d40d20201c1480d00a9a4030140e550341e0051070104d0308024000c5c00d40c0050050150b564904040c004480c52980c94402440000e07204c10000d01103030000d480d144440e6000140c0c0e07040b5036a040c08a034004041c008542105410040301e42e80d21000140a01403030f107014841518600c1d0340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 681574820 1250 681573570 681573577
    0x501120b060406030b09011e0b03070e040c051e040f06110f01110d110c0a03030b0f04060b0d0608070303080a0510121b06090518090a0213050405060a02030411040b06 73
    0xc005000d01d40da03c1ea00d440140c098940703036480c0703841908100000611020003440d401c040e010740d1841c0c03514013820301c50300c3c042c2a000600f052080001140c440c1d566900c6500ca28159490b40303440c0e85486488004480510041000c00d445c5008020f000403c0800322003c00304007541c0850500d82084c140203c942d500d005421200c1c03908560804004100302c148501c010420440d2011083c84003020380250081d0904c41e99501c1001a440f0402c0c99010900c0380d07200314017011004140e000d061080800140a58005070000c00204800081072400b28041740308010003410ac40d4003401c41c40d803440e20040d04201c0c4c000d01320b0701d00b0380d16030002a21190b45100080040c0c0f11070199543d440d220b504000388140c0d28441d13101d000c1400a6008140540201d288401f110320003000c600e440e0403104009400a080902040128460640c84c0780040e078804461540780401e8010001e264030b800d050061501602402003003541307104005000101c0c0c00c010000644140c141c0c0c1c0428030850803800b1800c0ea10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 681576070 1250 681574820 681574841
    0x4240c1d180a0504060b0a030317040602041e080f0c030303040b06030109060c260c0f1b03220605180d17160209100f0312050f0a091d060a050112 64
    0x907484800c000410380c02c0e501141c000c07401444204841043c0c035040c0012120340e80009000700c3c00030340030000b4000001402d0307a07001c0e100750786c09400c00740d407200742082c40c00d001800305410501c43c020500408500300b00201031401000002d03c045190707180845e45078400900040d1001c0181c40000d6119102504808401648150100a0800368003001802e841b41d01000030785094594001c089d804403141c01c0715010381014070001c3c3c580941400c101070300354001c00c0e003a60300e48040e80c5c1800c1c50910510240c00d5107030305880c83c125602c6501c1010420402103400801c14045c061100b15079548000c89034400880003540d8814540c015070502003a140803549101740408400110401c0372004048200440d40c0f081d159203010b51030b0030301448400783d03003805400c0c820b8040b03440070800f00300000203160034074040742825480e0041c05065980b29602a00c2103d0115248003001c00214911030900c1d00f00c541c4c4107881d00031078203101c40010655a6503200c0c1d503042021200f0340c14090201c6a02411544 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 681577320 1250 681576070 681576109
    0x120c051c140a060302400f090804051921030e092d090307060b01091e17061b0309010f060e0604050903070305190c0b04240c1d 56
    0x1031409202c2c00c006000f1038081207016089031480103085c102c007182c90300105d031a50a01000003528040070060741c0b40c2210341500e81281c8504000d28040901d10034219564051410f00fa901c078208414071485002c8a00300034440001440100501015808840c0524202c03002110b064185428101c44a810031003130240d0101007034060000e800300701d1083d203060089107809044901880751242c00f00b400e00b11801c07403168004100c1d01c00012466400000c0100050524503107164540130300c24884850b8a581070005003c248041c002000c0200074a0510010b140050005103000c80d0310034001081000104654400400450190a030079004407a001d40d50982c100107140d070303a01540b4800c02050700c920f4000c5160001081140038003004503410560540c0760b00b0720b8400382d0180d000f60030071600c0c40502080100700c2c00c07400055a0301200b902a5000b194802c1480580c0c0481c0a8243e007014254800b4526002c030aa40c581e81000710569544025050030208d20311500c04501d2405c0e1107923004580 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 681578570 1250 681577320 681577361
    0x403021903110d020a02040615020a021201020f0c01020c212a01090c090e030f0f03040c1a1e0c1b040b041103070e040b1f110303090c01120c051c 64
    0x90a50000703080c0c0142e4001c450030300072239603103052014181d01d0404c04240140c2141c88889c1c0903050600f910001e440d0300000040c50700d048081d0f40c0a143c0c04c4800c520b98a40d4001940154080e420800a4819555030a0380060030144050001141c4105c86442ea4890015a1140401940810147c03c0c815194009200c180f22500d44600c14804130300408038102c1c81d00010002e4918000203550b03006581c10710f1070b490006030030b07803010060300001d108030341c915030350000400d103413810385010101c401c0078100490703c85415008110b08207a101e01d000d002414180f0012024a500003221b0300e00620042c24044100d4100020902610b2100d85294101b8100341120320300c3e0415034010340c80703440d02d80d0310028500700d407100304000d40394207811076030340221040d282d80b15000300443d119036003000c2800d00e0300348800c14149950454008070346140351070700802c10640a40d60004510200105480420421081840c101810358002c0207201c01c580107c0b80c1c40985240341d1170748907140040080b03904240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 681579820 1250 681578570 681578593
    0x33403171b070f05060c030d11030a0b040b010806010c020f03030c0d09060504030f060f200a03060501030e150c04031a0117030703020c040f14010f0501020d08040302190311 76
    0x915034404940e12040c0310032005145200790000c5280016900801528185903242100f046003e4000c1106441c0d1400100103241581584d4400c102038841800d02154691034004c40c44012221030000041c02281000303185100c5a900041541e8050f42c2424040030742440c50012846400816480c903825200020700e1881041000aa240d9418600d54500d07852644a250444882c001d900c40207000c07a05c0d000038000000c029401802c841491301c4000207a107010628814266a02c22041c0200c462001441d900f14951600845018110030300f01440642480c2c00141d0355140788265001b1030004400c045455040340d00d003110011f54020840f00d040d01c9800303d001c0c103501d0080c41200028002c1d030615120b0084040180d544103a05900504407008103103007480050140505100300c050342d200c00d842419003c441400b8080c011103000043e102e41403900181c5040010941a01031045050170000001e0340028640c0941c4500d2111203010380700c91a090340e201001c1c00c5000400d000c0d00311100f0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 681581070 1250 681579820 681579863
    0x1202070c09090b060a0803090915130f060506041a030403050403050d031401140d12090f030302011b05030c190e0405010e10090606090e09100e060a0506033403 70
    0x10703040e4003c035200070540d1200c030200080b08229108540b865041400740c0c040c9854500200781d0300a07880f200c0301e00e00c150030000080140c800da0380181009070b45c03488031042d080e00e54420700000d03000688100349824101850f048041c1c07600c10b450440660000000f030200351140d000d90700110382c41f00895454805584024000e000d01b488031880303a0802e4000081c0304555580b074858501d401603ca9804c180c0d541d211004e409040c010700d08140300040d91700044031409154000f0040d03000ba8000100e64240103880203014000504040030030209005025081d08000115540700150015179242968484403c0d0303105000b034694580d0052a0000015075808030140c1c55108120b0100030302c0c04030382c4402201c0c0c111903036030041000040103441c0c203100da9682190781c1340d00f1151503030403180fa43d02514442c03030558410903480d41c1a0b4100390140155007200d8000d090300301e502100640400303c548070301c03160b8007500e00751000e0810151501100c900140124003d01660300400320001000100b910300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 681582320 1250 681581070 681581081
    0x807021504060c120305070e040506210106081903090e19050103110301050604090c121509080c10020a050a200a06020c0c0307080c0f150d1505040209030d1202070c09 73
    0x11343c0d03010b0582020421151091041e41d2203158551201d10040703d0140922004043c024081078005052001d0300c580358221281e03050148a0038000403440c5410030711000c2c2040d0b25400b003001000d080740619130011b50441d85400c2555021400310020b5600d1220004c12a02c0c40c41806005920700700010080c0300d002070480320082d00c16402445952152001d01089072281d52003d045207007014014414607000100f8413000c00d000c1c1c0c0c010811400c0f911030002c01c4a084c440304a983c1e160028001c0032000c000e108a80c80b449030440704600304500100c024001c0d2140c20318031020094040c12176800000300b0700381404090251800c4410704052803074500002c1d44504070001c6c01b8401d40410032072610780003801c01c080d2000e540c09411000c2e5608140612a040800d40c0740d0700c14000d6100188490b1182c01400380e1001544000c02d02c003240c00c00c080c1040d0b580317070030150041e4010400e54030507440c005601205a02c4601e8010700d01444010990000e00031003000904a610a80c0f000032440442d4004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 681583570 1250 681582320 681582323
    0x1b0803040510021902090613020c030301030b010e010e04120c141b040902131a03030703020c1005120601120b0307030c052821020a060215010b160807021504060c 71
    0x4107042e14a0782d0400d0b65150740c003010811500180e507003808014244161401e42040029000019045241c0c0e1844285c0c0c0158865a0042d84088010814456951002801040c41107002e5016505000d458842a100140040c003031000303051046102d14031800c40744200c0c0742c03c00280b00320000c11011551720323070b81c05404a072400c44002e120200e651800c2c0c031039074412a500408001d80301c4141c1914002500350324039040c0324080100303040041a18144020300310300d4820f80c041c0110340700540802c0300c402a00301c5814104007041c00992498400c048485401607401d007041c41490080e0036600000d440e10341181c17034240c0583c1a0020400249242d545c0c02e843c021a10740004220926180312a02d00038014400ca401800d01d042000c9440391040c41070039003070b0442d03140500e01e91340c010a4003800150712050050340100ca80e0642a856509030902400c89070031010300d440c6244e1403802c041512860050503800e800601c081c210341d00c2e0352056494100c201d4a441e2500ea564001811b132075140c020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 681584820 1250 681583570 681583579
    0x100c061107080d1a120a11030304080a2901080a0309060c030e0d0203101d01050a020f0708160b0103030e03060907030228090c020a03110f0a11190b0a020c0a051c1b08030405 76
    0x1d6143c1c9180101c162b9041d1f0300d0b183d0050000e010aa11510020881e0b804610080110502410800040030385424083c190f0000280440e50440c5401841c0c0e00445d0721140800c5601c002100c00a9404403440c080f2050032102904101b0003400024100075020301701d0244107280610303a0100d07c04140300034103050b0400008002c55502c4a210345c3c168401c0c0030310300000d16420040e00340000d070310781c0103403400d150302803400c0c2c5480340b41356a4048030300d07400e8100340c0116010001d2480d80c0e140c10804940d0240700400034040951465002c29165181d18044828401c01e01c2c1d00d151005030b441c03004000426403000b092003942040c0002035180c55070071909400207244a50000c40481c000980310501081c0728000b480a03104a480780300c0e0303030341c00414400d6219a84495824010581d4400c0d071020304102d8008607951420007001a2a118403040d805020740c200020402407136644803a2500000110300c0855500d264504d0400103051954440d004800c40008000c2280a070000c040d02c2610310585 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 681586070 1250 681584820 681584843
    0x70f02011e08060315060603012d0e010311060711011d090f06010e03061510030b0d03030b010909090f080c0703021c0c170d0e01020c100c061107080d1a120a 69
    0x901171444400c046426a070094420801001031181650700307190024102d69480c0881860300701c100750700103429070180361100c3d02d040042c402d003d9082040c0c0c604000c100d900c1e82c41e1603d16590000002c606001c0141809440d040000100c031409004182800006200c121f02c1c0c603001c0010a10840151021070005001881350b503014180001c0540c003c10282c40f0031840c0419000030440c04c140402c102d00101030b15013086d07115070340706d10810140444c800d480101d0342c120880001481c1c0c0000ea403040e10741c18141020600415040359945003110f03000300d036240d81c0b1720034080c0b254500122588000d4201400350304558081c810004595001d5101e817030313070062165844116500e102c6500310800c0a0340c000015210225002d076406034080203042c016190845131140005212854101b540c002141107000c0d0303401000850b100c6c8a91509a45260900b001266101d51105015940810658950700e03e070780b58007282050700c4025010401410082c0c0e5040ca40c2529851701d0091604485000c11075 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 681587320 1250 681586070 681586093
    0x1c20070305010b06210910020301060807030e120702090408090a0305070e06010306060f0e18070f030f02070519050304051302071e052109031b030609060c070f02011e080603 76
    0x5004841c842180f03448403110311503255800d05d041d8036010706a00494417400e81c460721440c0260011314002e01c055296403806160440c006420b842a040709668130b508841c051220140c00082614507594064610000950359490320111a00c200070915520800c2c41074000204040060542c080d03c0030307944580d45948541c1c00641c141c03502c60107202c0101b1140448118940d101d081d0010100300b0040c1032582c0003144000c0c10310b1a940580d1501c00241c400401c613007406030107000c1d01d1000508030780110b1401400d0785401b520f4942100048900c010030410807001d122007002914064100140382c40c6071208001c640c10001d611580044402950313080310303800b84030040c026045142d6000700c080e00b018000081d1001144105200030426102c084c0070100c1c00d034030304010000039441700c6502c80507960455020145071000c01004d2103402d903c0001003180c030314482c82c251a0340a501c0f60428028110300d100503211440d54041c003100d00801d1910b42c6100b0f0ba40a00c945002c0e103026003d481190100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 681588570 1250 681587320 681587329
    0x40e0c010f0e060a08060301150f050312070c0608070504031b0311041b03050a181401050c0301060903110111030a17010807080c0d0c1d09070f081c20070305010b 71
    0x795000264072403001c1c0303e60700c4528003e9000703561044004000250800c1009d03651007020340b5a40000f03d40d6560b452040c8080e080400c941c100c0c0300d0703040c203050342005000d50700c00903421064081e0324100b0030200b000c9002c075800b40741518042c6500601381f50343c034491131081c80700d664040d2000b91030080d90740e124051142010700c20060344038a07908110b07078168034002064001d1b00c00545800c4503103549400c800741c101c1482e0000b0054520030700112509100d1104000d09568010380a4011a5010001003100c7d5030840c00303480c00c40754018529940d166a034401070f10700c05c18000764481c95000000e10486000d92102c0b009020019220445040340d0701e0b010404e82d0741c11f403405003e01e60780c810b003074402840c03030700c41c504041080c030030040140b000f81c598449110040c10458110005034004052201c803c1040c81007501404141d40807006107442c4c01d18072942c0c0d55181d00007004108019188805540c82680c400d4907410701c8001715290019440000d5558414510003500d59510345100495503240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 681589820 1250 681588570 681588587
    0xa080d0212040b0a0c022b02090703020325050f0f0a1107150302090a080109050f0d0f0818010f05010f090b0f010c02060307020a050d1709060405030f0a0c02040e0c010f 74
    0x40650484c142850407400340c90b003881ca28803d030790010f10482c503110002d55000d1007100e0080705803a60842d183c1d05206000e010b50001e8002030515005000b00680c0500ba44440700d5000701500901e407039041c0700f00c1d00307690718455508080814000040d102c0100344083c40107107849140f95440d604111854418252102000d00400010344110340045490710302c43d402074070340d03107000a0809441c90b55540d40d00f403c40d1088041120160000c949200107218280038040100015082403465600503801c0284054001400709584002c20050001420400d5000c11454090b0070760400ca42e58451035503c10800c070781d10401c40002e040903030142060400070004842503a043c2c40d44501c036007481c4d003082a0358000501d010110710850b56681d01040d0100300030302425002d030b20352071101c42c1b460030f922101240041c8401110703400001030000040b000801c488502051441058030f443d6403800803279610a08401c017942c02130601e582442d40d45c802103200c18000400762524a41e102da8000240c50402 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 681591070 1250 681589820 681589829
    0x5070f17091b0f0604080d120c090b030408070b0f09120405130207050f06130b010e07020a020f0f06030f010609060f0516030c06020d0b0a0602010e07150c020a080d021204 75
    0x200020b4801ca004401040d220040701c03801803001d0749903000400414130640241d4003414941c0c0c4041000c441040d0000b01401d0a2072404006001200900c1d90160140b142c03841a0032030424000300203000c2c801c502081e206099401507009140b42400d1550740f18055051f03445058900684401d82d00c000e00c54400c560440354090f000c000d5080d1031824141c02034004601c15104d0740280d22a0351801281800803e100f6906070f418030100101e58104100d988074160454064140e454003413048507900041d50400781503044410302109807151000c980c80c42101c040d9943c00000c00300a10040c2c0b0030716640c86050b00c000d95204000d09503920380440b02c4800c2c0104100c0404d0f01000413600e03401a2a8440c441ca9020317080c4440c0541480d82c1e98000c0f40d2141d2004103120f95245a001514039001c1c41c0e2400400c0a84002c0c030800b1041038143d601d0301c480348071381031618095103a08117015000e42040d00c0c5050700140700c0c141c003641d00ca0045440c0c0602c0601c3d0b10050007101500c19150322240305071425917 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 681592320 1250 681591070 681591073
    0x2010f020c1b0105120f0a1b020312090102090604090504061503020a0303050c16120b0609150f0409021008151804060b0a080d030e011d06060d060f05070f1709 70
    0x1501031140306004025600c40040c1082400c000340700003940d034040960300070b941150351244035191080107e0200c6500e4005200c80042602ca0760725100e0380001914154100050207280f241c03152542240244144035100390809004180001c0718200c1da030025102d14000d442c2030100455000342040211554080250f1010f141c1d001030001c244284050a10400c1d6501155090004994200503000c0d043c1d010900e100340c0c510380807040020040280d40c2220098440c0074043c100b10032904440a140c11059014240c00801007111790703619008192040d801a00348006032803d030307400400d881000c0b100c545c1d003003011156515107401c1001d014150b0300e520300000307447c03619150345000180c400c084039140d001920755000305400005000c5885e10944d1030f140001d12400b500e4585095a2191800f61080b00b4501800d03003107164007041c80307540000c1c201d0755014031000b07918001c8018480002c5d00008949000d041100241e045803001c18640410303190b20360380b00508110726004030300440d034040c2d65 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 681593570 1250 681592320 681592333
    0x1303031103010b070f0515130201110708060117070e180d1110090f0506070302130902030402102a05030306040524011d0312040e0603070303050a081b0a0f02010f020c 73
    0x2140305003600c405c071944140161010852071120840a04c0d030700761011042c41e006c0004a50031503030081c00714085039400c000602401071400008a84840c8144540c80101c006614411050300050040102902443ca030386070150400b403034a0804144c1080c00c460315842102100214a400342485ca00000c088800030aa030300c40340b8246801900f0303c3c0c24121242d940000f06d00c000142c05202480c030805003a0f6005840740700c6001c0c01c0303594105907441114030b2032041041c00b0240e103803082442000b6800b81004070200003191006c02c0e1114145100a1450001440c040108940440118001c1d03070100c030107001a49820a0500c148800a0a4840458000340a5407125400f4101c9000a900b80d41007a00a130464100801d003000380d010364501c10f08400180c1070006400d140d81d243d4003c01c0c258001e1600a080d036401820900c47c260341981032009803030000e80381c100444c01c5103082601c0002c0303941e11009d0100e0003030a280801c4180c840954284400891000443d20a2728400400700e00100036 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 681594820 1250 681593570 681593573
    0x1091107050706120f0203150f0a0b0301030f081b0705011701180c0e030115030606081903051812010b240a031e05100e060a031101030b0a0302091303031103010b07 72
    0x804c00d088280d50036140b0f8541d00c2c0c844000345030740b001d14811031103001c11500c1e41c001131080202c5d00d010311405501c030303024912040c0280140b003029a410342e03501a002c19204010f44c1485001ca025030000404600078440107101820707404074a10702290720a0f2143c0200f848102c4400350601024000d80c00d00c070440319020b4000004c3c94000304003803130841c24003030444030407103012030b09403205480c2208101007a0201001041904e00c80c0c10001c1c080c00010b030200c200c006402d50740f182c0000304050108600443c600d020303410a40015805001d00900465504501c0400f00c0d0280100c0c501040c4211a1119028860307100d0000e2400c015404440403403814106040a074002e0a489041008030042986240070030900c900c10b06000303546509400f40c40b940317060030301c0e64809001030195010305400c2100f0400140c20503c0c0030142802401d001c10808101000724070081c03403503030000c0d5002c4401e505000f10450000c0d50001c01d07074000d079000d1069002070340e40007001b03100038401c224035008204921170 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 681596070 1250 681594820 681594827
    0xc061a060723030d0902120a11091509011220150c100203270d020c1c150c0207050a0b0906030711010204030503030a18050606060c010204170601091107050706 70
    0x36440706005241030040300c07002d40251550b0008990a82c503a076540c2c003028150b00d81003401c800b001e21078400070b002800160b41c880c442110940d40c0103005044401c0410140e0405164450038044c0242c0b40c642290fa44101c862240100c2180a44d909920070071414049106c0c2e0a07509142032010300142c1d049603071040c50741f043e40e00c10349d0060a203014003c200302485207503000550040703d400d014420208003241ea03003440c243c6488180e2a00e9800342994040c1c0d135401182010707420f00704584100b820507410b01049400c0851080080413400401099032036030800b94440c1c0715201c465030841e00c03140d40390010312020032140d005404414030103000d1920700b441c121005582c44002ca20300b00200e9050a8201e03826a000ba80007204c143d0404420404041c80500c40d140340900c44080d803041000140c1c43d481d0700c418006e40603500800b030000d07000c1034400702501200c005040c0180c001901900035410243c4400d07080c041c0e011040d0030900e0a0316080f040c48141d403c00e503000409440d4061a1500c02d6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 681597320 1250 681596070 681596093
    0xd12051c05060a23040911030c010c0b060d020d06090f1202150117010603080a090302010e04021207032a0c1208091b041508030703030e240903070209070c061a0607 72
    0x100071905010070113200a44490040605c07440c0310721030302c030421002e4008060420103072401c0103040003444140307080032809480c24960001010b5864200028450012400b188486040503003200d00b4008902d00304144400b00d000e60314052807030060b2490022000b00d80301c8840391401c1018204410041c03003070400c1040040c400d10b80180001414a45c1c9960f07507180e0360003045e881004078034404070400655800c624145c01c582c604a5086150810981942100440280002c01010b40d1066101d0070b007a104400c5484c00001e99401c803412074240e5100400c46c0071030074400c0320711401c6d00400e101d100d030040400034044c2200c10041c027404500e18180d03415201d65104005d610503101e403a5080b50700105600900030300301c1c10016541d1740700301c0e08014003503e10020400c506684056040c0182c2c1403030440315400d58643c22000c2c0b42544580390a28594000c0c101d01a612045010a11140c5d98100c5601d41c003403446410b0901100d020f106000070419a540300d0103420100c00c0004100094186141 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 681598570 1250 681597320 681597359
    0x1810021e180306010303050d060905010506070f05150a0b0f090702070e040309051005030619030210030c050706150e0901060e0f09340909150207020d12051c05060a 72
    0x101c4450210403000a443c04200b030b402038000c80c00000d4060042c01c3d407401044041d000740d40c024062945000080b644620590b40082c0c80854421403140030072034184040d400e104031900d0f50126904010500c03d00902d400841140715440c54003088506081006005203d101680c016010251500c0d1f441541c01e90010b00440c01c12060000c0495182d48424442c862100303e50380c1d041d12450301c0c0060080c0c0648e141c0164100c220000d00410041c0da400b00c6000d42c83c0190b00c0c3c041400742407000140c82600406000030100d03400c0c08e0340b001305014483d51040403070726070414640d5280c8581c0170050888030036001e040208200d0400086000c0f0900400517040b11010b01100e0300c2880c05440208a03e0700c16802100321076003090312802d03000c000c07004a030190100703180800c015850b80d41d40350440150486008140e6801160030340a40d600c1e00080302121b500601da40e400401c0261005140781e111408206640c1d400b0300e207415003a000e03445003510031840a80149111b60915000060000013a83c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 681599820 1250 681598570 681598597
    0x402030606160602032d070f020705060d050a060b030906040816060504060e0d05040b0d0e0304030f03080601031a01080a0b120a080c0f1c0f030204030b1810021e 71
    0x680070320714081481c011642c502440c4010b0304c03410803440c0000d0034141c07090140d03401e80f10140c40c100341c29508403a1503002141d5060000404d1581c020070703400d20791154041e95010303001203441c079820b500e03e800292150816500801205072111003560541c0800d44905005a0100380041c0003e100b5200401098051800d03c12840010b40c0e0380d14255801150100c1ea003984a0320252540841001003407962001c40c107140b42018141388004169000d208042d030420380d198404806090000d02c11a80510f0b0414082c0a1105590074080c001f05410703615140002c0c0350600d0310f5807003611a1401c00c0744400c140d550707100ca0386500d549640034010036420f1030b51002034000c1c403500a840403c03610003858440c0c860303d5168250701a15904211070304103410a140c01c080044000c50303c00e50100f007841c6070a428000500710001c00c04034024081c60300020011803012013401100508500d858481080060440b040f82914210140590151040c4804214018407982c00b412542d08090306603a9071814 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 681601070 1250 681599820 681599827
    0x3060106020a0609062d060b03090d031a181603110406030b0118080c0f040c14030901091209140d3201050414070e0610120b0301092f0f0402030606 65
    0x21810500540e6001c044241586c50210b00e5200c1401aa401051207135041411480d02540c030311303103511032440380070304141e515410f205080110242045c8284c0b070141881d00c204e00c600340700b0f4255003000d80b40c402d203140f014020800c04a109000b01010341d01c12407a21750820b4039100099010300500a42c01d4140940c0d100308415001e0703101c940c60000c003032840040160041c12000d00c11944c10046d840c600a034240b4190310300075a0030081780342c1c1d50b0328469021a600d41e07c4044040c010820320000508145c0707103d080300041b55101d0003603000c0e2402d00d030f8450a4298514100801d0509505000703000f0612414981c031501020260200c0d0015880c501e8a09103c5c00c142e11401c607070084804403640050141c03501d2140c1410000440035000241c550800c0d410090300250604042495040c01c000840b0002d5151201c0398000c0640c0c0f00b009002400040c0d0285000c0500210001322000070b6601c031319850800325000448a111000042c28000c5501d510405000281d40010100e540040f0f041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 681602320 1250 681601070 681601091
    0x80d021c020d060e040f120519021e0604031409010908060901090c1211090406020d0903210218040e0708030708120601140912010e03160c0503060106020a060906 71
    0x4491101041825820042e40c070030300d5407406802c0b12181d030448881200c0c61020000010440070712203015035007000c3c00002460388103200f100c0e07610444540c9640b03c023207040120185900040e010115000d588040d07808002c601134403070b5803040c1c219400380005840c4a83c07902e45c02c201c00003e00f1440740614241100540341c140b528030305001920020340d960365900d01e040520100581c102c0181640080180c01900e850b11056046001411036511484100c000318040001d0707903049400c0308071015024440000709040c05840e9519075007e80d040c1c117070044400cc0c0760640b548212040c00d602c0c040d08002c040480300902c801070064613807034611842038032008501001e01300050f0054501c59815295513080031b12202d812004050810340c1070004050341482c09015640595440b0401500c542000351500c0c0d80150141558401007003407400009230030841c024030b9454105405000c0d01d5101d8000390f941d028195100d50034496100117801c00110170000503580d0304078081c1140184400320b40b83c00103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 681603570 1250 681602320 681602347
    0x14060903031e31061106070305190507020a05102c030c0708070f05060a0c110d060c050c160e1b040f060f0206060a231c0809010207080601030807080d02 67
    0x8240f07074090310340c0a0340320303240f002020955400360032540381101c12000c0c0828160355a0340c0240c10402030544450026200f125042c4840c042209440c1003440385050121010b522600b07901401d4401780a000408010f004490042d00c80c1c0c1c50780301c4100c1441c0d030220b0344040012200c2e060260960b0004020248800008000700009840800301820105250010111120015500280c0900014088194000d801030408048030b03401c00709014620303002c2800640e0502402400074001444c1584550103564071034094400303401c0000407155040411021201d070783c02180314801d12009000000340300f0582e00c0c125a2020b034140441c013401c140e181d04295003002410f40048000403200c1c2c2d2401103040c2d0401c4400d401107410713200800d107207003070418161405a00401d200080501200889195210041207042981741d010034207210301c42510b8050704662001e2489070051191240100b140380c0e000c12224101c0703910640b200c1c030b45520f0f40d0b41c4c0c0140303802035100a0001a403e1041c07442c8001c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 681604820 1250 681603570 681603607
    0x409030507020a031b1d0a230c04090e070b07020d08250201081e0103120210050c0417030c2512030c030201180201090e060418060614060903031e 64
    0x1c80c10b600e02006202d45128004c405c40c59108420350b107075a44030506e011940f18aa04c0e0040755440c0041a04070381680340d214a0b0000c032042424001071401004a156441c40240050754549601401000d17007806117150b80d11210b0080481d060f03001c20660006180a03850920524881c0c1011070400103440058000403204d01c106420980c050401c072400c640c3d00120301d9a00901058260030134560240441c8101a01400002d0000c40d10340d550120359030080101126003001004103000b01c0c40c14181849003604144500c4900c074620700e0000c0003458000c0306445880b2086001016040b214010442944450f4100164000c207024400b107410a00088400882130094071545840007041ca002400c490a602c41500f401071071a0003840141ea00c40410001c49000c0f008482c40b588541c4009401000c8810390708001c12040003540040004982016045802590800042c60300c01c80a001e541c2c400e003030400747e150b017003088036015404c449000524401a03a809003410076080c41c0100c580e450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 681606070 1250 681604820 681604823
    0x15020405011205130f020109180905010f060513050613091103060901051006180f260a1a13020301020307050405030705030f06190b1e040f11090409030507020a03 71
    0x54000805115a503007050000008100d80403003000a441e051044c00c18441d069240180421000c10703044045d03a00c14440c99000d00146d0882c0701f506c1e0701380ca4030400140782d4008101c88a50030040d2101a2000903c200001c0342d501170102c407100c0100d02501d1004180040c8140d600c007a1902d0702030a84452442000703009841a10005401003805041500e082c03030080c00c0d10400c0e8104020425001401c100810450703090b800c00d00303040d250b942440060180250083c200c00180403000140107580701c1508990b18025070204e100b50303201d50059a03207031126102d000d0807401c0c082000d24903040c600d84100c0e6007e00841c42c446500c02407030f80000d080ea4000d031070a200041010806111500e003e001540062000724020080d040c14041031031340b6101c0041080d000e4400401803841240000d40000d890640000c140054824142000c1d10000b246140c10600070340c0740640315110319040748a400703542c41c1144603481c140b010b078100300405880000d40840411500f4044070006841d80c011140146 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 681607320 1250 681606070 681606113
    0x3060c0e010813050c010f02030409050f10060504140d02040902030d031d01090209070503181009060b0d2609091302010e03190f081209010b01080c0a050d05070c 71
    0x2250100d000401e00e00000c0c048118209080300c007000003400004641c0c100c55020308090704c41010811007a400e50056038003803000706082c0301c100f01d03519600a4041d03100b1442010215406902c44c50b003181c00d0300881c01207195000001074500d50a20788203043d006028402000420403640c030341d003c2802c2041300c84104006c651038080590024501c0e0300090b07070300b12a45008124100d240c0c2c00151010301d01a00180500000002085043d182240700302044c8050000320b0349820135910700d03680203041005040d0755031868140048003070b19040100300d500c1508503109a50135500c40403249801d1b12a100c0ba05640d1008020315a1141c0f80d0f644194810f41e043d40e20f240d0105800d0001400c144e0f00300b05100c0c402d030000c015070002e081c0384c101c6103000990400340220244c40645048180f5203d4a25070f6007815800e40c040107581c5030705400200c0104401c1c0e80b500c02c07544400213a020f030b60107965241c1d408108180141c005410b01e07a4001030f4050750030f25080103001c285440d480e050340c1c8141c0489484 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 681608570 1250 681607320 681607337
    0x80f0703020a05040e030904020c010902060301080a0201080f04050a021e100203120610090e0a090b04120216050303071b121202010b010e1302030718171e0c0d0302010603060c 77
    0x1d500c0c1400c040c000503d02a6400d001c0a4442100262a403190341c007503d20955000c640106002c4095100054107a805048242c7da542c40c1c4064980e82e148031002240003598280009444104404480b4000d0754802c00500c501456542040032100c2d0384568100e110030851501c48483d40c401c05007810340c16094000d555a900114810f02c80384200a20340d5008072000300354900c00c1c5038809402012181209440010f0381c0300c1026243c0074140c10000580802410f40c144001d02c503401e60800c99442440d02190094569800c845038050b0083c450141d154005104003804162045881c007021100a25500084c2e901c9480300c10300c611901000f40ca05899030240084083e809202c0d0040d030714002d0034818001c05040b0009050b080110704c42c80c44454010000c1502c0c1400352440110194018841d40805503c0700d880002c940081170729582d031442001407101d10903000000a0151078580e4014200703080b150800d000c514501103804400310740d030350035000020840c0c40c4200701d00d4042503503c9041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 681609820 1250 681608570 681608573
    0x60420120c09030303060111010e2407081605070204063605060604030f05010914030c191a090f030c03030f150102100f060305030408010204080f06091510080f0703 72
    0x250040014441c45020a0400249441e40d800005495000f0424a041c1307010700040180a07015000c4181011b015100708c1d101034001c10b070700c0c00702100013072501c02e2251003d0752028400c407011842034070040301022203c81d2906d030140c840c100504003140040c20100b041507035641500546003c5440c030404200080d00b05c010201c2d034420280c088088400018441d908111001070043e100c0c6200007040050300d11b0480b003c000d003e401401e245030300a0342d0804160381d038900943d01c0364003101c4182203134043c0e8590540802e082080c4546100d80114400301800c0ca02030341d01c005804081c000c0d840750f1061032216005d0902c200014030001000c08080d50712410f243c00c170840c1d0b8410182806c0780b50742040744040582e076400940741540e808490000b049000c80a03015200810868101800c83e0000140124401005400800469146000716254500c081035410386804042d21000c90700e810800380d049002d4690340d036242d04042c0b03018080114960300c0394551b04d005038140004502da04411170400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 681611070 1250 681609820 681609847
    0xf0f05012405040f0e0d12060b07031403090708030a09050301061205100b1210020c071406040b0d110705060f0702060c0904090c05030f0328090e060420 67
    0x3011103807482401d000e407104000340c00607044040c06403500440d07036142d15110b4003525401008002403c4019038225480b0070700f0040511150744024203a45041441c006100c0030794900302d0302c0841d00f6070341c1e21803e0f2500c0300c1c80c5525548003800c0c030180b0784180d11020918a03014001081402d101e5110810220f1814080c907094032000e5115252050001d01220003140c00410340750041c4114090008030f00502800080012000b1030b4640c14921a042807a44009e60a80c02000c01d00601c41c00c40318043d0b601d10700d5808003135543c0d056036080041030100f0402c95003207602400b03544070316000c08149405102c004ac203458020001c01e8a85610a00500c02c0004511401a0300300390144080c09192400550510292086c41c1603140660740d602d107041c040c00415141007024100c000c05883d20340e009211029901d800103944200441c031401b42d000700d2000c40c81510007501c10145ca40b0300201d842c201140000d41d0005000f103400c2904d03800c40d0a50011920310756006100d84010041c0c40c0c10b581d07000308 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 681612320 1250 681611070 681611081
    0x61d010f08012a18080f060a0527100212073b03030f0409060e09030c0c0907050d0504030504090b0a050d0f2402270a030312090f0f0501 60
    0x800c0301e03924200464486105000d4040f070721500c0000c10003240241410220b4416a0100c424030218030504070214280c20007144804068001d00201d442a4540c04108001c4906c20f407807150f4503400d03401700c859100c185070300003140c074005501c1030b2034041c030a440280042c0c1e4001c082c00d0304484d003c0c074100054140c2258021554150040003104d400c15145680d00f52040005101c2c4640409a182000d1590f0104220381d080c0754204256501c2c2e0b5980c0d5008800340442d8080e043c40a5038400001d040b6850000655078a880c0041c000c00302d01c060b00307007071108486015040c1400c11008000e0002078035164081c00c1e0049209940b000c0c2d44030300d030894103c102c0b0300480487d0311032072909408104c0c50380e034901e40d406a140c01400c9040003007140c2c9007000f03840c004803420040e2a2100300003004001c4e0190b0280035003216511110b100d8540002c194180d81d00401022580310300641c80a101082c403d07034000701ca41000c900001881c902580740d002400480031030803030707042107882e5245040050030b0007030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 681613570 1250 681612320 681612329
    0x50424061707410c070f170a06050c0c0d09030c05120c1002010b030d021c0819091704031104060e040b070804020d0209070c060509060105060f0d061d010f 68
    0x4403c1182c80202c0d410720012109004006810542006860904100034090440c01101c43e03180e42c2c1c0b0351004800b03848504900c101442c00300c40a10011700025400341d4540c8001284000d414400500c0d562200201809400349113414814464400000d5040003507000c000d8007622920005480c41c1ba000d03d41d50b805070441c0d400741000209182c000000010711303003208901183c4481540c112900300720f0040a102d9200742d170611801001c44050381c1c0108030700407030104140304204012415441030b02e8140e01070750100b070f040c2ca00340c0c40200a1000e40c0c6c48921401d2290070001d0024241160f01c180903000b80e0403e6901d40000000f00c80f50b458148038040c010706841000281c58a850746402c204020028140c0c42403000e004002070855481e500d085c0e0441f9030092044121781084a802800780400d4401220424070340000726000e83e4000030024121003008100510702020a0a180002d800401900d48007039159400441c2c0d0716540d401d0a140481c01d525031100320342c985240f0580f001d94a600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 681614820 1250 681613570 681613577
    0x602030a021002090f0d0f05100207031e0c150c02060a06050a03150204081c02060609061c0206120f0405070906060c0303020c0f150603071a04050424061707 69
    0x118900380340c011601c220b482d40100310040c0caa2000d02d0101d21603040d01c41003103a0001c40c8105a104204001181d401114054402c403103420b40e0b41100401280b00d40440900403551a01800030040307460302000440c4030007450303c1145040769940d690340302c5107d48080840c080d26241022061a41000381c80e80c0110300e080c0612000b440c103000f103003070072610340000341c542d407010940803440180540445004003058812945a8104d04011020510801142030700501070b02c6d012030640c3c0b60284141340030368402855000c0241d604c064078001549200800c80c0c020a007808101507018a90300640d01c242504001e4410303d07d0185401400d0100f42e401004003280342c2001404031a6107c030380c0481e0942d05040042e42d400d00160064940254034200603182e100340d640c920b090300181031042e80603072802d50840700c0351a00c4070003001e00d2201c42c68110821a41c01e00c8100710070705d0141c1102c062044421140389412100326900c140c503001c10b03003004012801004103181d003000f5030340000c3d0388403c007440d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 681616070 1250 681614820 681614827
    0xe100210090602093c06041203020a110f10030e120403120216031205030403110303040f0212010c020615041d0715080f0612100c08040204051509220c1806060203 71
    0x210f21640c00017460960745500c850400c1c640265100e041c102c0d000b408000c5058800000286802503980780e0200080f100242040700e40116401d01007185034404a0082c880040543d0404085005112024624580344540c9400b882c2081c5094000c1002c0c501414210410b4070301c0e95000ba00d80380b82a01300d00012440d035141000400c010819580394a07a49190060b0b90351641c0c24102c41071080c880c08000e2602000003400100f0818040702050a4420369404918040d01400079089803103240c200e0000d41c11034000260b01d9554104d542c612072400900016400e44403816030800b004d40840d8240c0e25500580052001021a40344000c2d843c4191900001c079103010403000e0010800036100302d004400144101c0000703c0c060100301006414071904200321905080d004013044415641070740100d1408021900ca08512000d0f03283c2c5da400a0302d600c0a607140c0240c80d100341072524160103088440000903500241d94156140300410700401140080800c181e100d408031a490b034090000e42d030080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 681617320 1250 681616070 681616129
    0x1707030b010812030a0908190f08060a08030405132301140418020108070903050303070c03110703020607021306030501020d2903060601120609021b19030e10021009060209 75
    0x30f04036030b0320401540300469000c070b10740f81010b110300070700c0c842c000d005580d40d0410728641d612405241c4080481c4d41c44d41c04a40ba06014828a5041b81c080e0700c540d038000f007000340301c2c0d0f0500604010184a8514000a101d44600e50008c2c610b580d4200b00c2a10b1b00d049001040048041d4064038200d02080305d00700505140006103070300e25800510024148002d000011700f2080c02084420029500001602c1d924901000024070506400030100c01064038403000c850200710000b801015240c0c094211854950b498003004a281700001c010b030380c0310380c48110100000d103080c00900f0b0440f40c50302d000300f0010b520a04000781302416100c1c90f003d030032000034009c42c95580040c020b50403043c2170078256130640c01200040c0c0540b03401e1300410800d84c000155050752400500c505003002d1020002d58031551000003040701e05100307061024002030690b085030941860034900d040d54804c054011106242c6141c22040141e445211003a20300a03404141103000b410454003403000802c000b4565100c0c011407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 681618570 1250 681617320 681617353
    0xc0309060822030507060c09050a0e0c1b12070302010609050603010e060105010e180f090111030705040b0d0b040f0b120c0108161b050102070302120301150c0c1707030b0108 76
    0x20846080b0305906007000c10014180078408644c1c005801c41c405000800c0040405044440b19114003800f583c2d880c5070000c0e9044950350721601684440319202d14203411580220390b03c40030850700103186e00a02e04060a02c13a4400e000f0441c451003900041070941c03902c522003040300c0c0e005000600070b0341172103045214075402240032410b40d002400c0c04242c00e08107101082d1628489442400d00c05054028401071881c01ea514503c181ca814000340409031041c82c8a90319800160780c00030101c0d40c1480203010b2160070350058030075020001e00000e00c1d40b10150026050700d80104c0c01241080e40e40d030403800d0908000085011180846004005114061300000c06094009151314942c3c20b09048005c032252080e024076810034031900800b091440c050405600030f500c034207421000343c81001c41d10b003034850038442541d040300c4500450010781d0210041c203171094201e0603c01c0f50150300500c1c3c049080440c5040d00702c00903620000030701c0b9407800c41c60003c3e80c103401a0404041c5078001d07407880d41c20a10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 681619820 1250 681618570 681618601
    0x108010510080a02090a0b03031b06130314090d12030507230d09170705150f01270f0e0304140904210203070501021b060f040b070318120c03090608 65
    0x1815030b40d28035281c0c1c4520342c02004082d82140c02c8d500d8040000d150a910802506181401c00114241d4103a40ca5021661001c2690700c04000d001c100303108171080482d03020002601000f003005c0c00b07039005071003c2e03034071080e02d4003001d6100800700e0b54400c14861307610f5018a1012460310228941d5603a0019078000c6451801880d05144000d6291000c43d800c001c0341d00c85101400c08442d03010794588400d454130756161486491800c4038040010002032078140d60003c00342c100d40c065006e821202030050501c500c28060641000e07100c2da192404013260300d21070300ca40300f0312814000c091503c407401d050050914040d01030756188a00602ca0601001c942d0900d041000c9a6420340c5035840c8921008052f402c1d4042c40d107016105502c01f0410002c0400c3e8030099004c1c1804441c00e466036030343d0380c1003010600541945c001e82603030900070000e09120b01a03440039082c1c4000d001240f5022056070340304500c0c42035403864034000800f107409800c1019000525a0080c114500780181c00e86841070b00d1404184 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 681621070 1250 681619820 681619823
    0x80f070813140706050a121401030314090901080c10030204050303030c090d0c0e04022e08131b0e091c0c020112020c0109020901060507151a0a0e0108010510080a 71
    0x40e03440712141042030190302d08140021060030390300309035540d1001130203641000c01d0b030501240b0740000c0c68401e030300300d8032511000000103a52000682d00f99101119040d8825000d0220600100415442950b40e8032080e40204070300310040089001c04818400e4845404140000b4540107020610490303030f01000703481d489840c00300002e84a07060600081c8001c520200e000d0185c0810401c00701d642e40e0302180d0a0720843c026120161042c07030345611480001424140115603901d0840b40040e00b5100b00c4006e900500050314800c0c18100c1500c82510286580002c4c10081862000030440603030308034400341e481341c160005025170001d82e00c82c0441c403c04042d0040c08210300b00c1c0402c0700b10781c0581c5003a1242c42120300c046449007801200c89000b40540035040c2c1c8290007400c0005103c0748158100c98405034003608401c04c03818a01d480f180581319200841031103940b9142c001d260340d103035100070000912240003010f2103549002445821100050315a01011205580074440c036400040c0d5a0703c3c09 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 681622320 1250 681621070 681621091
    0x1703180f03064011010302120c03060f0f06070213020903030406050d0c030b03120309030f1c1a010509120c04180c080a03200106090e0d0810030b13050307050d0c03080f0708 76
    0x40135002c004034000d102d030380060b20991100c2e40911031000740040140d44552400c1ea2481e810041c1c103410005040c14420540d980258204a40001820f0260250301010380d05030015083c0724010f4006801c6400c83c5e082000060340204501d03070508034070b000312440649030703080800020325000b000c2501d55010b0b01d4040700b144000404540f0a0700100121b50b800101c401405032511115904492041c030440b07101010207040012480046442e5004400d181e43c1c141c4400c1d01c3c100e400020b1000c0d17910343d5a44121180101e1443d0b85164603580500c03402c10a408170441950815454403141801c115041041e00754050b0f80a40c0000b9045140309020b18410301e401d1112003500b10307a8074090036950300605403083c1008081421010b00149042035a0000e84903560300b13681e0742c0e410540d81e241d9407002418403c410008500171403070341c41010644500401c1500d28001894480f6071400082300e207040c0014034a070003018145a0300402c290b0304081c041200e00407034202414010a9060080d2083c4100c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 681623570 1250 681622320 681622343
    0xd050f09030405221a012c0111070803070f150b010804080313050f03040807050301090503090411041212080c031e07090317131703180f030640 63
    0x101c48140400c9111240141040c001200302038940d00c9400c5c0c0c0d81090b103000c038a18034800502d441900000440000702c2d04007102919002000444402010481d184c1c0140641000400c480d40140000d0042c0c0b40907550180c4000c240d4604400c01c6448521003804032807a148100c43c0c140c1c0d210b044190002c4e0000c00150b00c0c2e444007071590b05210110b00005105110351440c084100d90040301070f02c2100c0d5048150390400740d0f500c0038982640e0003200020616001001a06518a01303980515064100030364610300b004d443d210304091409520310142c3e003142c00c1c010a80c02450384030328800d512400c800300396030840c2406035000c1c8101d80910400101c01ca070341000946502c0c411210303a001540c00c00183d84042a4152070781d4000d51002d8001648144032020100d0358070b107552101ca04000380507004500e45203070000c011111035040c100c010390050381100b005140d6902000300ba4000d002e14240006800c15070804c45001c103003403c0c070380c0b85200707141a0383c4803071046824460345513140c22200c8120f1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 681624820 1250 681623570 681623599
    0x120f24080c2119050c0a12060c03060807060c0b010f0e240411091203030c041e03080d05090c01030b060409020c010216051b01020a0c150e040c0201020d050f09030405 73
    0x4919820b00ba100c002c0c841c0d881000300d42c00d448a490640700f07016000f0355886106280030710403500968020400c18040c1402c04000241d81076211000a5416245c00584e00c2d481e400d07050300b403410130741c00907000407000014481404528580140100070000102c1d0740c0c039207015120584080001c0c00c0c4461005001d400100d09840e0540c0304e00b000d4001001000709480203a001d070400d421101400e401603000780445110504008200c82c003e60721185441d0906207051011440a441e0500302126040254400000903a021024103810a10200041140d250030000c0c0351400c0ea9082e001410181001030840040d101c040854050383d40042c005640c40040003619406442a0711030080020380070304800f010310801042c600107100380050b11182c0b501080d0012a521000c0319005489480846401c000d60600c5c0b01000b40884003608107505c01c0c4440d680050304442541d105000582d40014682e020184640b20701940489072040207082c03401c2c4030b44e0655482c026400703000d014100c091046213 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 681626070 1250 681624820 681624859
    0x60c0307080c09013f060810020c0618240702010b010c2a230324181606081504020f0703030b0a0806160f0e1f120f24080c 54
    0x910f05e0f000801c404224120f514036203401804c2d280b25142090084441c4815080100d000311480395007280c00506680d02d0328000101130440f100d41e100c41501c0f84055188030307401202c48001200c600b10340141c43c1c5192190020303003960b80341c1c9000c6040145981101c400101c1402031a0040702c80c1d1011014141da920f0400c80b1040280c0c0c01849010800c03e414000301205000006800007041c0c050702c84500c0603001d901d4811f49009281c04500341704800043c0030840200c1288001c01401080752141c00340b0030388140041050750054000110307040c04000309020811034050700c06409442c11480c01c00795402e00d041c0c030302600324000c04154903400d09940c623a0712001200060101d42d0143c5c0c46506005542250a8904805010100d410404604021030103203107071072840311015280c2d10b01607514520101140a140040600b0310580b000e20b6603151085100d0042c91750a00400000c004034401d460340c0d18038036607a503c4c40004011440038041034001040207202810700380d5072a40c0380c040074560301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 681627320 1250 681626070 681626147
    0x3030c030b04090804030227010b0d06171606050c07031509080409150b040320062118060c1603090902072a051507060608060c0307080c0901 62
    0x20307502c80c0c281807070340040c415580000e2048038030803210003c540645526504064003900c500c1c084140c0f2003001004444603140081a07500b48c591000242a038444019000755a0f0000c00c5044542c407142c0c0303401c100a980c04500c0060610f6040082c2400301141030035544000318000145000d4915440369001070041d00325000c0b466008515985036911201010010b000c2c01001c40c084040c03412001a40030603d40855054036048450007015450740b041e8101c0c0d200c1c02e55245a001403080140c40600c84104a0306099100d8007a481c519900f4030820201c202007921080361850341002c8107006910009034101c412542c03c1e02035841c0c015540c3c0c2401d403082e40c00c60f17000c4049180006850410400e08031403424130308192400d1819002c403030a590142c005090701409800c6500312032449014442080070782641c41c80340c2c0000c1036a544480c82a42000801c0d200a5102a000310a100856420010081e44000ca120016080c480ea07040024203075445180000103981c00003080d11002c9081c0d2180 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 681628570 1250 681627320 681627341
    0x2010203160e2b050c010e10030203070c0606140109081203240a0b03161d0f0d0c080a0b13050705010e060d110a020f0f0706031d010905011506020606010206010303030c03 75
    0x80070149119039030f14000d6031890fa2012100c80c0a940e089101940c01201e445c40b5500c1c0c081c0c0b0001101c0c0207640141d000350700c042c1c07109d410b102d0000c0e906000207010340560380140c80e04413a00040d0703040c4c100000d40b4252058010141580181d80084071001902007565400504d1b1490b108a0301403c0d00c0b44440b28800001807a080142c1e0a07000c01d20300c503640c00550003012040c4510400c0006088116500d004610403589150960b41c10418245440002ca001d040c0340145445416074490b91003005400c0181c1c0b01c4c0e4000e82000c03080000b40000701c0107443d8890b04824807408010700da503850549074581402400d051045000c08183c0a07214070055500718ad07454a010484c403042e04100b1007017a048501e0840051103070b010070b6442d941c0042641804150518003c11410b810142c05034098070a890360890008007141c4e256209150901030829050300503400003c007800c0d24840c0b9a401215508100203560004c014040c040c0d80c002512030440e034051900203024086903804a025001b200342 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 681629820 1250 681628570 681628609
    0x2a0d0b130b040c0302100507051c0e21252702070f0209010906030c120204140a090c0504060608070e1c03120c11030301031205040e0705130602010203160e 68
    0x200b00400c9003074a428400c0e203000310385000740400c030200200d406100302c2c0c00c01049600014100c4180010030300055800d6181c030300301070001c001f0010100d4542c00030320004522051020b40c0000b20a0414000c0b9001c031160340c5034107141c80341c128100c0a0004c0d1584104925000c030f02d0700c0d6980d2400303002882140e258604a09560703070001070800113000d03421034805a100304144000021459521f11803103003202e03404140ca400315032074421500311403540c040d800c1e6000b54980300709400010307004c1e10040c8503d101000009196a80303085c80300e50360100d0742180d8091032911200b40030302c0360010300781c6500c108545040e003116480b0390013040300340c085c004504c11031407600b00d214810590007900051206400100811a000d40d1120450700f80c00d030307401480e600e500200010320114010060002450080c1d04100380317800d59500241c85080f000b11040c1002410110f540c00b6204140b0124000401540c8000d40c15804e12100d20f40c84180480203c1c824013500701c2d0180510b46038400402c00c3c09102c0f030b6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 681631070 1250 681629820 681629843
    0xa08120901050f2106042708093109020f06090406090501260c0904030c051c03020d2009220203070201020702010f02010c0906050d0f06082a0d0b13 65
    0x44c1c2c028524004030071080c005040b01c50009009060902c02c403003400136140505c800c1c05145c11403c1208103c01d490545a400c030401550b850354560500c40d5a82407403003620700c600c01080e99003d5108043c0c01c0d801019440c10b009031140580d0340e00340303032129040382114581e5403810310320005401401c140c0d008680160401d4000174500f01d50b41c1c030180d02e00030484140262487d4401070680c807003000d0032a1541c4106804007107004244100c280e003184920480032110050031440d5100c440b003580300344042c00070b0b40001d01c12401c1040c41c002e0301600050f20407500e41407a01804106818020760103a1406003503900130040c410525a05402c0704144614070865423410041c48c002e001c0d60000324103901068003410b00b003400901c1440340380c0340e1540c10f07a1138a2036141000012101940501103084030a5101c54805e03403442120320a100c014507030f150090640e0703181d0403013844480c1c2d107914841400c1d40c3c4d480041000394a540d0501210745038000f031084c42965a01c441c003c00081c1000004d0700700d900d040c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 681632320 1250 681631070 681631087
    0x260a09060f0f0f1506050715020d0b0f030a030906080a1d150f0f06061309151e0b040b0f071a191109120c1009140a08120901050f 57
    0x942c4200650141c2c07420600c5545107414421080d16188070341c107450710641040c02c0040c1880f03100034107901c6100b469694000b14400ca00d0307400340c0e00070f070342040c038516a81d41c4000c21601d032940003180200c1c402e40103020b0aa10544020f08034410521440c03051060160000307030001c003260320820b11043d0500015054412042049a580281e00e1381da200702160803012900c01c01c5006581c9106081c000c45400c00340d520041401a207070021030480c10164200781020646030264001c0c00a00040ca54455140034503003d01c6107107526070040309021700e00e0304560500040f2100c408550948102561055881204803004c4201c0c4c07003142d801030820302032490300c038005180721a682402031690460340001e0320380400c004001c5400210b4035409410003004056050305204c181003540f21106800d5078404041d48010610b4803841000e194001070b400340701800604400c0c4102510308806450090f074003802e02103450341e03900728001d074101820300101d1803150b907a01ca01c00310b401504140010f252251440d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 681633570 1250 681632320 681632351
    0x3110313080c0d050c010609060e0a0207030516050303190e070b0c070b0a1e050405060405090a090210200f1f0204050d030905010f02060c04150e12070e0106260a0906 73
    0x105d07507601115400c00c0b60010354400980280c0e02615100103500500e41c541811010081d4030591303045007804002d200c41da2541d1425480142c2060040b4091582ca1410302d058103804607166101c000c103185804a10020f01800248103002d607810032000540d1031412450703240c0741c030b80303c1d6014607050f030400944541c4065002601e41405171091088140c0c0c0d12841c1030960300c2d40528010700e42c00c000d0034403080006207010b900050f0001c00d052800120201d0f5500414600741c5000c00c0000071400080b040504d2a008180c0446c250165070042c080d101c07031407a600c50315002c0400d503200c41c0c480d45030a451100340c81ca60454000300001898011240810329001d00781d0680b0348142070104003901c0a4103045400415064071661100080301d160504000790510342d80e11580780d00c0308000e0f045401480303d454616a842103038510100401c1058648510048213040580221041010780000d407c0c9840501042c0b1602034045e4100140503510000607000505100c1d50140405090030000511101c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 681634820 1250 681633570 681633577
    0xc0305040c1a1c0606020d2607030e10020a1206080a030e01050d05011202041406030718061a0904050c070302030f071106120907090204081009030905130605040b0103110313080c0d05 80
    0x45580070b68041ca00c00c410148c4c1ca0070b941104a0b4920804020407001c0003070441d05d400d6000105050002e042c1504800741c3d4039083c940076640d0080e544c0040d040392108d800040d1500000c0130541c080c0308840c00c0040c5142c442090300401070910080b00290b40300e0307a004009a411901c1c584104004941c0d4030b105029669070344100c1640a01c4c5410485c880d00c5d54907034070b45441a50301400601d180e610308090700d62540c29400d14a0941d9550320008629641c01200c0046443c0020b0000d07a16809450304010803201c011745004681042040140b001a80100a4030030041d1544051915249a07091140c4804101c001550344603c0000d4180040d4003e010303000c1c060200c580c111a0442d480f01c0a0200700d01c120f0040395029409054043e0301e41c8520b8202111480c441d141c08210700f9580e80110307145038209180d806c111600d0701000d01045c1051b00c510824600c09103003d10080401d094400300307512014020b0105204055015001c2c044410104d8102d588084c00b10f428101044100415070340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 681636070 1250 681634820 681634829
    0x15060e091f020702031e010f0f090203010b030708370b0f01080c0d060f151203020f0c060412030903121101050f07090e09100c09050102010c0305040c1a1c06 69
    0xa00221031120790784075100f80c0703800a502500521041020840c04d9281800035000040650340315000c0e91220007030390058030054010314a01103140401c030f104041c00d450401d0604c60095220310410400c4640c0005d00308100c80e2503c103198100c400340c0400c1103003841c00800340c40884040302c00a40400220300610f43c81f9038019015a071299032200240c5440349040081c1035840045007040c0c0d4007003080c0f0f038003d082c0b9070b80c2e83c100060040c0040c088031400c0038803544490301d5240c0d002410024550140700e0000041c580c038001cac0040b804031200050140c0a60b0160407114281c3c801203d080600401e2040003850304250386450010034050014141000c1402d1034000703500f840007080070440e40601440c01402c00c1d8445138007290410841c18801d03800240140f55078800c1c041ca00761031703801c24820345000c9415551803440c21070800d4000b90a607400c400d00c03242014038280030003001c602050604001e88a5540410f0203140c2c00c805402d415020b0818206014845025100c0c4441c000fa0300800840c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 681637320 1250 681636070 681636103
    0x150c0c02130b0603182a0909010605031f0915150605033d08061806091f0914061e0420010c060c0f12021615060e09 51
    0x260004400d0350907210800207464201d41c0c00e0011401c25024000781c5c500341442c040c102c51908950240e00d0800e41c818007042080c0d910b00b290000d5035810209005944060000002c1c03100c24600008207950b84902c0300c20726413480d80a2003111903159507810100900d40c0140d81281c9581551070780400400c003415034010454070048000a010307001d98240e03445820080d110040419230400820030602c00c0002a045010012050b15040d00c1c201d001c01018002060092400c0c2c40c140c244801c408100d20740007542036008404018440b0700005000c2e00b40c901d000c1c142c4550381040182c42020f80300c1118001e08150f02c401070206994800240184201d0754041c1100c0b0001b03d00c202881024005e031405050f201f0406600030200c10000345134600307884103140841480038661508000c450031a0620750000700c00d90501248143d115600c0180d03948018807c42c64070a1007804920503d5003078400819585202400d20302000c5640d210310018559510b1603603451401c454610307110000c0c088040c554 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 681638570 1250 681637320 681637339
    0x20105071b050f0a03080d0e24040b0a091101110f0a0f020a060806011409010509060c0c03070e06180a0e01020f03010e0714030705091906030e0c041401050607150c0c02 74
    0xc0c0e107844184413003201d400881040c40e000c85e446548015200454448000e03100e80d80e05c0082c2030884010380c25060250b41141d6415040c603207800104071002030b00e2500b0b050309024900c80841d00c0c0221003505500242001204d40c10020143c0d03040c41c0c2d140c1c0441035240546201d440910000414440010380700b102c0c40a08680c070f814003540c5041c42a500300e40083c001492100e030844407a0018610208141401400d2080050010b0100d074030400300e00d005500f00c0c1003221558101000000090b1041400c80c1d041c80c9411004986408600c040342c080c2e0700c103c4408540d5100e0580c0c450141c006505000f55959010795010482c1607200b03201c0c0d2b5052000c6d01e00040c3c50706120346401d020101d80e001d12140342d502c0b605c42c00c80303c94104080e15a4071420750304035006840f0b030468248000300181e40300070800e284100441030510400c4002d4600450a05034076220a84004014034103460084400c01c8e2141f8a13800c2c08207010381d000c00601d440717a14040c00d8440c00c5800400d8805510302c01c031071740e80b117 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 681639820 1250 681638570 681638599
    0x9050118110c03030103175809110a12050d030e070501050702010e0414151903060e15010807051f140a03090203010603060518060f01060c020105071b05 67
    0x1191150b100125400d0708207100500008581c6119070441c0341c00c80c0803203424090540d41c8040e410300c0c241484040070700711030f0800c002e02c07012080741240b04015080703000c449464114200442036800c014a12460780d503051840030000d4584034080043d81c090160320380b0350b841c0d6848224076005050260390910800305081403c42c424001c1c3e1420f10411005811041c0c600780c010740d03490700060f00c01ca06101d00702c1d010f0021034075507101e400414540000506003508107000e0310b00000480d041e105000303070080b0b1800c40500c60010420811603512040000d03564400c03c02c0c5a061910950a040060314010000076514900041e1001514001c4501c25a0220103040e8428082d100100d49070200300203440b407540704003814010342020395080c00c000c00d410510781e00003400c451458008a03591903a40041c01000141c1220b81c034083c40444005011074101303040c0b00001c0d00d005101d10340800c038080680f01d045912031401e0701d2915a1040d00040005c070581081c1050018901449020300e040480c0002c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 681641070 1250 681639820 681639851
    0x803040b07020406080a03170c0c010c0c15110f0a0e15040503150108150c040503031c14010e0c071b2409150c05010603080c0312090c0a090b040609050118 68
    0x40c042e415181e502481d10048c0c05a070101c0d00080c040400010284a0751000c0b030402c2c01103000f04011607450992180700341c90b00804401030410142d8803a1700d0840e00505050f0f5000441c1c0e03004102e9000b00351241130001c0101d43c689a0928481e4110103c4042c004c02c840b4268090030542d402141a201c0c2c0e00c290130000410041c0910840542d030340000b10407001d482c000e510503904100c120400342c0c33602c0c0c2c440e0301003403860f0301524010b400c000d0380d00e1080710311034428414079071020700c1240e842049501d401c01d86007045c007024240680d502c0000540004001d890816840d00c2050241900c075140d9603219540355070f121190350903455103081d140903060b0a11450010b015248044001070307820251800884050f00c000004039080d42d640c9102002107040310010b42601c404203001140d0300c8511645500c11458003401c0b1032030542c0701c4401c0710403958a0000720700c00d440c05542c002a0b0010301500103400f030200c59000540541ca40000400c80b13481d80d6035898400344802d01700b4080b600c070303148484 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 681642320 1250 681641070 681641083
    0x3031b07091103180f071206050a0c172e03060e15220501060f1e050a051c06050f06100903122102030c031b03040f08130803040b0702040608 62
    0x7584070450400001c2c41540f070340d00100c0b4511040000715034602069140710b5140c0511600003460075203008a1f480708221090040d11784c005021042070040941900c00601010845580c42184280340c4000454005641610407484802013943c004407903102c1007090500b48490106642080c100621102d040700e0019800d09146203291400821355103100c130004000408002d03c1500e80104121003020480074020701c800740c240c1800b400c0b9110f281080d05420740700c00714000d0780d040c03090700402c00c15960b0304403890301110400e40b8002d180180700710001c80d896581da04028446803800301402182d506c46c0c900c00348100c2c404c1e1540900d900b140784055541e0311562200500440ca0447c007601c036148284007007070800d8000a0980386110740106018181d80080340d07080540c6c00044108484ca010391a10252129845101d8074030b1802e1a0b00d41400b51400708101416031240003c241d100600c0d42c001c100c00400182d17060b203031281d0f15284e40310040d50041109030300c55410110041020080851007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 681643570 1250 681642320 681642341
    0x10509130206090402040b0d0f1b050409050a0b0d1406010506120c09060c06070c120503090316080f0d0204050a0b0a0206071b0c170f03190e0a0503031b0709 69
    0x10498106030640c00c011565001c0c0c0306194100e90284030000d008100000500704403400030101242d550800c0700510100c2d054640100300b6003070102e021041287d0401c04950560f103840c0c40214041d0f85120451026014000c001d41c3c0103542c800d0040c0178003c2c1d80070002e8000300d4070b1060314100c0e40da46003000403038020b00c6d10041005184c034012818120b0304100800303110b64046c003484d00301101000841d040002c21560200415400b0f0941000c000030341001c402c0c1e503c10340c2001802e5040019840380d41c0c0c0120252100441c21080c0310409111004041d0f80c0882c5d0360480e03844e512352583c02e4110194100e4801d107800303112112804208904010242d86226519500402e00350b03881403004c40f102d2040d503c02081180403114000301040c040000580900b4581e602d0740014014000d8152805000440c0c218450308280032849919804c0d601040114009181c904143d4400310002001c0b50120b50143e513051200040c3c840080c103402201d444007aa80c10241c584050ba50001103051b1400c105c00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 681644820 1250 681643570 681643591
    0x1008010203060f09090c06030c03040b011a0403120e060310081b01022104150c030206060109060206190e07081e01021303031209020a08010e0f0703080a031d0313030b010509 76
    0x10703503503d81804411294801150011229031042c08401304042e03500175601d9130040b040000401080c0080b0303030740f01801064041800c5901c041741d0f400e0841240a44d00000b0b022400300d480206e0071310300c1441d0701041d0707400090a0030b03034070300f44895801c9010720144101100c6000303426400090b140498003440241c00c0c1a0090244101168000140340c3c4009124003090300c420b01012440d01d070742c140d00249030099500d810440384c44908000e894200000d00407070400c40e40c01000d0180c0b680c0461519005044001e0000c1c40d940c11403e1040a00001250a40144901c510010354004005134120f080390f01c111400101031100915070707091b4840c0c481c95030841d8a0702c0c0e00400000c1e21440024203d243e40c00b000013072039602540040e8034034200b40d1025032180c0d1a070307104e45100304041c002108040d0300c5200030107502e0310b10766405419000d600f0680c001c0c10787da510890499210035003000c1e440218801a60b40e02c14107914104c43c030796568007081d6000c0004800100b032074101854120b010300d88495 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 681646070 1250 681644820 681644839
    0xf0c1b1806101b050706050a03060902181507291303020c060319091209090614090604090c0329090a060b06040f0b040509070306060f0804050c06070803100801020306 73
    0x30300c00d50700f894020024004091004405a0201d10709221100141c6255640c859654100d0354004080d60425001445058030401061260100146011046900507035405080c284441000e401500030300001a001c645505100468010038003000c9092020700004060507848480c0750806c4618040d43c01070260b4445810200e10340380030b0001c0d55103c4031444850400c2ca8121440ea002d541d40810104c0e4520550f8510360f0945401c030031306e24042c0c01c82400c00c101d002e04d04450950004507201400f4040c908003408240a1344642c0c0040500e00d4101c400b444280d41d503490800d442c1c460101c1d415030701d0740402e10b24440c034140042903c0e014201c2c10005102e003000949400006080c03280720a5401142040001180c000031602680203040d8036004a44031480c00040c0304145000519071401c061a0650a102c2d540d00200884031503505860140410341c5d03a03203841c03482c000109134841d0740203c0124042e801c0098882c011480f0b1582b1103080200250354041180c00d0780401d4880907400001c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 681647320 1250 681646070 681646099
    0x5090d030e0601030f11041b08060f1302090619020708011407080c0d0e0f0706020c040207021011010608100c1e0f050f0f19080c040303080a020f0c1b1806 68
    0x1500c0141720f0601a40e00300b03a5540c4507000041c129019400d1080020285240b020421500030800315481b0200340e4070140245611400507400700d151603540050315034003040c1e08106480e00c1040c0c407602e1410840c40c0f801000c0c03004000e961a0018801c06c2503d60074841c03c5507010955004440c060341c1c90b625030120710f44510083c0340b043c0d0450606101c02c10f82c0c1d25400d001c000000c20024407010096800350840600307141c4005d003050f842e400e1007806240100450303401a00e880741080030f400c1c0a4034000180d444001030080c090308403a840001c8500c20403003413055441e10f0b54001c1d94100c2554442e4413041000410300418220800201c01c0400e102c80c80703824069004200900e04180780615403446c0412114216180d03400080030104100064032007134500d5030f0056520354010314003244181c20030340b8507a0014080d0b0801010058003e40100701804400446000e0b200b09403021030986403039840041700b4109912042c454103100390b8003002d1402c0f00864005249001c0e40c401303420071000c01900c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 681648570 1250 681647320 681647333
    0xf030b0406090305070b15120f1b010c0602030a0b040b0d050a110402130f080f0f100c0314040b0a150b1206030703020d060f06051f030e120c0105090d030e060103 71
    0x701c14007903041c0f003010018640000c0f0540101e87c41140003540c201400741042040c0100b408038120409070503840400d40703ca01a0001403820780780002c04010500d117004900049680e4014080020706080c0040107110403200c0e40e800c55040e4104c182c07410410200d1840400c0030510a50030b01501540210030601c0120b01030079030309040c415002d00003510b480b50124030754841c44003d44c00040052241305c004d00c1030840034031203a2508810703000101080e0f03450400300c03a103d2107041c00850303a5607501d0001030610381c003940103107c8440071030a60202500e07184c1010010507404403141310640e440c00e0100070880c420681e07240140d45c4800d0a06040103409900c2c00518031000d003c20f541441800e400000607038a07042042c4545e403280d040030440880300c4403100306a41407500310a22881400c81c01d454010300280e2001d08462807850301042d00300a6803100f0741010391009003940d50060003c0c004152400541000b401003e6540403140c0b2041006d00880c206d861029002d400c2d03401050040000c03485 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 681649820 1250 681648570 681648581
    0x406021b0907080a0e0a0501091403070c0b0328050406270201050f19050a0e0f010e0d1a011203080c070c05090c12161b0506160203040b0a0306050a0f030b0406 70
    0x61010700041d080070a80d17551440c04140100442e00307a9110314100302044a03180d55441c0c150100c400860411000f50764000c40c81009010314600da40020000604401003940007a00150b02c4000020000d40d10075941c6001e000120f5096610300c0c140010007403048003415170324400b111701d0f103c00b41a54002e82e004642a5018200e1901d01c80414003081c40195000704a03001141c2e0b00e40c031511b03910b201640d4050440b4904a0495204403140e81c00c2c4000c1da40c01ca1441885084115501810280746180c08440110010705240d26140b1901c00071070b8200101e6100070007a03006e921501099507440c0b0001d9031511400d0030081c00c402619104001da8104010400e820213460b0381c00b80c5c01d010610102402c5a04216841c0100b01d034680c000c2c18a060f000306004110400204460800d200b49468040e900c141c050f000d20b120b12003080454015502c03c1c0143c1d40075040c6907040030303a80c1300700c1d110003009401c8a001d810b1080c80c0c0c4480018404c8074480300f1100f00c0790f01c50860f02d1543d40c1c58071070100502 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 681651070 1250 681649820 681649831
    0x8240d03030e0d0c0c0909110f1c0b060a0803032e0e041a0115022a09010909140303040f030309060b04090f0b18030711180406020406021b090708 64
    0x15228400580104810f1215144640569840d5103080342141080400c064899000c030319402e28101c0600c0c0400c5c00000d0701c1040800c240d5001e50000c4541d00822903844040e24000703881d11540414404111120030386c107001d15012100c40602c2512022503036100c0c40262224085a5404123102011403072500c83c0c601c10b014241103494556070354200d4055084000c0b00c0840d4010310103480c512080c0c4004000a014040c41310580caa81c200310302020399100300381d1000b0311004900c0c60344880320080016a540003610b01404964595030758520700000740c211040c0840c2d402d0001640007904040020a40340701c3c0e6007005180c041d00240e52002d80c000c00c01810103468050711070b5074100b420344490086415843c400e180400c900340391030502c1541802d02030480e40780a000c81130b100c0b201c110000280d0303103203503003205500030021840000144041c0a10700a82a040e001300100414020345502500481d41a44c082d514820385028500303903803081d640300c000da000c12000b011844d114406d20035180e020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 681652320 1250 681651070 681651077
    0x2a0705030a15150605130605040b1206030705030d0203030a050a2a030605060c0a020907052b020705010c022a0901090f0b03030c07090f0b0609060c1f050708240d03 72
    0x295080d4121002e100f149420060200b60000303002c1c0c840401811111004001a2800505140c1464440011031148403110403c1075402004515942d07020f100c507800409004081310514003c00101030349940044640031030385c070b1404d0002a00400240100d008021100341c07a0002d8804040300710905100e44070500040660f107000c0401d941e05c8a000070420f00c8101d000034024000f007441000580341006000c4030030054140b00002d07044020764031141c035449100300200f0100b2680110000280514030000d045503003000042404aa00442c4a418011050503a000ca0f035003060b866950194004210070b8000081c2c4c001007040820683c000513040b48000300210394124018000383c9942c0212552a5864100c49010841b1400500c180c034005500d100061020b021014002803541c00360002c0c15018900010b05206600801c0c48003464000c840c0461540345c03900d100084004100458030b10300450401c80c00b0401e003000f03820613a548021080410341444441d4020320400311a240b00c11130a2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 681653570 1250 681652320 681652331
    0x7030c0e0411030a0b0610020706090b0a0c0f241802040f09050d02031908010f1710060f050103110711010318080c030a0e01090803040605090a0b2a0705030a15 70
    0x3107550a2112800c1180911070544440c200380742080301012a5011600c08c1d0b40c020707030341040215040007039901101c10344400540c850209100948020804200040815884911a0040003900e4128110b1071079000816050200c07116219000c440700581d02c60300740711068801070f0043c5400c0d0061100c000c1900404508040b2030f41e40c2390300c0c2c503404d41c03180e07005a0000329040390006054072540c7c8541007142340110142d403414403000c032502042c0c00744010a83c002500800d0324030040106643c49501c994003044030a664421715010040310f40038150009046c0030b24a0075080c10a4103407181c42c1c0c1c0006a24510087c001c006400900314031200303132178100251040c800480ca0341c401400032401c1341070165513101c1403040c3c024a25000400c0c51750500070f034101d05205040c4004291070581d0400c0c01e043c2c3c2e0301c0c0703000350006a079400d85601042106d5000aa0303814152050403c4c1d6000580d4420219411998005002e8440440d8090907070150710404c00400491901d0b404800b0b003003c0842c0000c5c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 681654676 1106 681653570 681653603
    0x21c0513030915032406030615120e0705030d020f01060812030103080a0201060b0406020c010305010b0f071707080408060f0a0c17060310022a07030c0e04 68
    0xc1110f203407a240c1038603002c0d40c0080308220064010b00d107545d20544643d1040c030310754050b501c000380c20280001a03803513584040c4070351000b05407035165030308400748101d80042c000700c20a14100d104003c800900c944050003071044407070256010340800001c40c4240f9007500d04941c42101c0d00da12500c13000b50074010386001d503410b60750b1000c4600d41c2c1b901071900480c00b421480d0411851120001030003e4603e130006144410410213880910039a030760b414103e2554041c200d00108590001c00104000079103001144100010420500341031a219440c1d14503180c1160700013841c50382c440024000c8c6050f140d01400e6004022200500004801e00c0e4000c10345551040107410f01c2d501d40010400a80d802c1c000405d00f5a69200110340340c4406002009a0102c03010301c0405951481074040c0708080c011030310784203036070300019040e1800c0c1c82d000500b08001001030040d070303035414070711208003 = true := by decide +kernel

theorem cover : BRFrame.Cov 681474820 681654676 := by
  have h0 := BRFrame.cov_init 681474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 681474820 ≤ n) (h2 : n < 681654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
