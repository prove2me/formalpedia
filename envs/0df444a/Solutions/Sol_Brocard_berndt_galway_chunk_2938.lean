-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2938
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:11:26.552068+00:00
-- url     : https://prove2.me/submissions/8f559767-7653-4e88-9356-752ae7a20dff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 528237410 ≤ n < 528417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 528238660 1250 528237410 528237439
    0x120901020918040f02040911090403080906070905030a0f050a02060f030a06051008160e030d03091209031a090c0a0b030906062704080c030708220f060e010e 69
    0x35441840c1d900d104001c00c8a4250490038401c50440c80b41d503009403840c90103211503090001908400501f19403d4a80b07100c1c40040d52141100700744140e0084e964205c56041212806040c907001a245004100350b209060016407400a1004c20b165442001102c0b0f44440342003031801e002e40300358002d600c1040001c040301d00d6a031f800c2c0a10b0048250f898100110740d914010000d006a40022603804100c00710002114201c42104c0c011000b592401d241d04800801000603080400c80202302000c241d507020354400340002c402e130414001c0300500b06419001d08580742d0500f01000905065484c102c40070003e02001d10600c1503881510020309040c0b0951340781c5c0200080368004445401c424894080000d101d4604000c03020b4444030043e03880407040d105a00720501346103000388103440d106020424042003100410040141502641c0d8190b121001c42d00c460514022000104144428984051000030138010030581150010304000031200c150b0030041e665049212642c44e4060b80d00c01d015079 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 528239910 1250 528238660 528238663
    0x120c160b03070f0801180e120f0705010f050c0f0304331401030b0a0b0105070212061b1903240303030c0201180507060e0112020403050114090615151209 67
    0x140a003082c2c0e180e04440d0011250f007254003503024410b166440c8000381e40d1002d0395007641d00c00c1030381e074461005540140d20030030707041c00b007a901c0158600d150389030015661007440000e11a0403020504400203210301d003000d0000601a01400c000721a0616000000c2000c000c401400c0312011008038500d594152040261400c401c4201d0480440642c20b21554600320282c01d4a0941a658440042c05103600d42ca904000280b4044103610f052000811068002d81d455040c0460601c0c0b0344402003000e032401005550031000100d0580300802070a003c038040c0b52000c00c9440107994000d1400103407031410200c90088003041c3c0100c009114415000201c10f05a054100f40c141c0c000940003031010320303e41210000c8001041c24003034403507040300800b4000c0612942c040281c00005240566454102c054044100d034025442110359079907584480030304080d085013091b0f10480c5400500b2940c80c0880322014204c2a207050b041c81002100d001245000840d82694a020303065500c04206250610106 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 528241160 1250 528239910 528239917
    0xc27090d09080102090904170d0227030a110405040c03020d05060417070503040509060303040e01090f0b0418030e01090b0c0c040506030a02010203070303050403091d0a150503120c160b 81
    0x40002a0140c000440c050405000310b030690300740031b040e0aa207a9241d4031100313585454083c1007002c1c9981000070110610403030020b06004070380c980c0000b40320090017801d500d480e0144000b07640070ba00118110b0002c5206030710f0800c448007064070301113840e954902d032034a21103030190070003507104c500c413000003061150000d00c461103988251a0303150402d4142c0c1c4415101c3c001e42c0c03001040e950080000f80f0050900022451f00104050110390400341c0300d9004943c00d4009801807845c89503034111041060795140124a000703c0c0c05c1d1000c204038541031000343e50f0035103183c001900303020711085000300a912a4010000401c00c45200603222545488141d4607507540d0701c002441103007030401180340303480c3c04107550452643c140c008615250b015a026805086c2c0180142e0501440e41c000048000c1c8200d40101d4501c60854840c0091078600400390840c0c007800800c888141c1c0400c0184200d0b1400640d0034801c1e03680c0382295868052010040d4070345020b115410703003040d000b0000003a1809104025 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 528242410 1250 528241160 528241183
    0x911040f08010506120705060703030f020f2209060e1314010c02010212010b131809060207062301030816061b02071a121815041203110702030c2709 65
    0x103038000c14001782806660b071165000d8294000c40401200e4000b034041d510042c411074a1140250078030800314800001500070b1540300c1a2160300700d49030f018a01c8100715100280005220400100e8102240414600e07401000c4082e1100e201411700d06001200d86503180d603141d010000d21802d544240001d010b90840b4050040d5641000b0001c00d0f4040c08800340c40e40c000c0c49042c207524083c030340341d08a0308280403140148107090b0386181220102d00a030005241150149801007009544006035081960215101e0704a0504010040c0000762031142101d8500101c507030340d915070300c440d401d00f20024808031161001d030212006034140c0310394002c15a642121000c201400345140c00b0304082140b40718004480c8048894040020000e14418130a11b101201350340c00c80f0541c600300c2083c144020003d480a0f611181c102d035644040b42c0c1e041c021340c1400392031045150308202140d40480da9501050640c1072144a410183d5910800b81c0f50110b6440220a0b00030780480c00c0c041c140b580c0328800005d2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 528243660 1250 528242410 528242419
    0x507030b0f011b02061b03031f060f171506130e01120b0103020108070e1e0909120708090d0b010306050714040e06150d02120118150911040f08010506 66
    0x4103102a03600498002c259003e003420710070300010300eaa08000240d805042c120b0401c2e69041e43e4201146000c0000e540715094881052080c202048110700c003443c09030b840101080007000c803012003a544506240c14400500328440c1503602c4040c02d4502c14801420030903004140401c1c082ca01e4214801c808044664401454407280d8903200030380001d444800b07001e0320030406500100010f5110b0b00006910018070b280c03c520407040c03c8006070420720220308054610303403920400c0d0914608110f186400c80e00d400001d1030b2065a11009664900401d038014104101c007140c18602034a600d1788100266600c070030540d650303603100d1a0030402400e0940e820000222013848541007001c00004aa00342c40001d6902480c1d0390340c0750100007032288040b40d440880401070000000059a81c0041c19842e203c008541d03172158100b00007030a00103507940312001401c0c105509108030800b020022400c0c0c03200e045021401c0b40c000303403841c81c281c03245903c0b5021034988050009010b200642c030040c000d420446 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 528244910 1250 528243660 528243679
    0x1c08091905130b150708120406090201081f031b030c0803040905010b1315020f01050915091501170c0910062003030a02070318030c0609150509040c0c060507030b 71
    0x900c2c00007191000c081c0250400c00f0b414010b0302c02c500c0480030f880354501c05c008603407a010405d560b480c54100107407811036100d611480090110760b004165903178003100d0f07070802c03032540c0207807000700440007602e84400380050041d0420003500d09656403080020715001303c4400102c81d542c165403982c03035029100b081e0800c2e181400206a141030710084031900746c0301c140e07040062818141e4804a000000300350074107506c2008250404040700b070054a10429210026102c3c605008070b0b88a041b0100422104458010501303035013010b12040103a07819940f51750800b80050b140f11458614100900441c50751281c483c90800207042c0148040380141e860641e26000103c811500b8555038644034880110079170170a0002440311000c590152401034040c0c40c0c9080f0421540040100308545600140d0340903400420038044242c1007001100241440c2c8401c42042602c481c000b40309000d07a01d5100d00c0703151142e03035000c0c08500c142e0705801815080700003002070b4100110090010500c0c04011400b80c00c085 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 528246160 1250 528244910 528244939
    0x140607090302010203041419091509050c0307080405120c0c10110c090604111902010c020703050a021311030a1d070609050402160b280b1c08091905 65
    0x150122001c9a5040c0c000b1402d03d07045c011070101d211001c40c0030365000403a01c610601402c140c0704a0340e006190b107603000541020210080008000280c0200c1f0107181820180f03c2104178000450340d0000032403030001c0300d5440351700c1c2060800c0201906401320038004a80c200e003a14001c03442c038160040807210707a0540c201c00ba4080c3d4206900492082064001c813441d0000d900700480c0c10780d80018000c00c00900c005031881180c1c00394020750b00000007140080040e5113000d03024800c04000320301d180005c1194900d0760340e031140d0350241e9104c024054002c0d110342c81038844c65074200b1200040d01c1490b944e01c07881d00e241d2290082440b68242d01000d40b40c00c581101010300070401c4002d80d8841e640b101c0e6803500700010301c03019503c00d02c1d20212401c0b540c1d402801081038078442794040d4a421145888000004a10314101d18941d205409100d180503030014966071343c05180310700058a06070401c0c2441d12400e02802a000b580c50082d0003400e5207140a2400f82010f681000b0b8410440b001c854121a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 528247410 1250 528246160 528246167
    0xd14031204030f031b120b03030d02041413020306030712080d0906150b03010812031b0a08040605060307060806010309020a050a1725211502030402090a0504151a0607140607 76
    0x5d9a01c07070100c3c1041c0755032a0440401c1e0014060110080c0031646001c01c40c1583d40f080760b2259010a0030200c02e10324041ea90f1804852172000d02c92302c040b0960960030712400080c0c58a03403a114507050f41ea0f601c1080b200f048911820341d84100b060860811103d0102d0510b034015101004030404e4140c9040004504680c074401601d0503603851300000c21100c240c3d00303c10701c01c5500c0030300042081c02c905614405002e032008001c10b058903240d903d000c02400c2038940ba006507038000d0b2500c0e2003070708000418812070390722180941d4403c0091a000c0744806050010400e0000d03103400442c7c10490305200071a14002c121806c0404400350001c4449649002528098064502a0810707952031140310402c8100d034003541642e04075a00e4030840102d44916034a01c3d02012441036081d09003600441004194604015229801741c1407042c140a03502e0556120b420582d840d490071200c030b40c4e13941841e03e031540800c04200b482c0c50303028041c20798590b0103090441508254001501d1588180c0e0001802c9510 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 528248660 1250 528247410 528247451
    0xf0803010b0405030c1e011808011d0d020d0e040f020705012c030304020d02010c0302150a061d070806190905040503030402040621031d0409030e010e0a050d14031204030f03 76
    0x14025203065181b0341000044548090660513108040d020303000210350350b5001c0c420001c200c2c1d941da030800301000d940c8966504004400c802d56040d900f0510001e640f030380e0440c10980300c9402c11540000c0c14561039240310024001c00f60003074190741c41c1881414405a800412204180c0c80814100c0450315843c130b216540d05c0304450094000707a42d400034800550041c00a81d007a01d03c41d0040d04c01041440d60700001d0701104650150310141c48243c10411403c0041c92a5a054000e14040c0050300e0600000341000f035010701690f0091940a0b000c0c0e4a4a14108440002d8216024284150b080c5400d003596240c0007030310b09a1240b8a080d0323002038010501440e2150140c113030f208503c0c0b2442191015181000041c04e010b08d1402c241704841000d90b80c502c554880280310b074480d8100240c1ea400010403071a00f1028550040344400c2081c80156103201d512162603034040c4203860048042d500c1c09056019001c96640340d849a401800700301078006605813030345500c44c0d5041004c07915a80443c82840d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 528249910 1250 528248660 528248689
    0x1315020606040b0d080d3621050a080c0f07050109021201091a0a021621030e191407030b0115020c09040b0a110f18030609190f0803010b0405030c 64
    0x58040100c40d50744038854101c0030607102c10a0842d2001c1078440045c50160900700c82d02c1141f038220320300480401444d007012144444114014110491400c60080c160b4400c0100f080180800000068001c2c01240300b16142801c108410b280c0701d5201d0302d041ca000e495910340881c070400c00c1405c0c8100d82041441805440c0780c02c628100c19004101e0134500ea10107000d0034903030046800700447c000352416890080c0c0f00b140f1501906848840c50100c00790041980d94540c2c0825050107100b0b54207640010b1003845101c00002d03045c0f40c403031113440c2194200b01044994103190140960000c01d0104890f07040307040f2113010716000b60030302503a04101e80746c1d80300e00f54480e4019150008a40411480c01e001580803103c0c140024840104e0032520581c0d8106100d640c0c50100b0002e445560380c005000c4482900d1000d074000c0665040c02c525854840407660781a41840d4003400e024000e00640032410071480e41c00103201942c4c1c0d6183c241000c13050380603000d02da01a2103040b070000550705000c8416001c0c0e8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 528251160 1250 528249910 528249923
    0x105030114130602040f14030c01020109032312010b130e04170c030c0106140102150603070b03041a01120605010806060f0f040f0e0a11010918021315020606040b0d 72
    0x15a00c020b0000d0742c10011401c181c0b00c881c0d00780008110300070b090f034804020740001b103c0e1451200701c080406103001e80c2454242d0459041844110000e03030012002c55480300a44408991424a0b404110250290303626001e0310042e8803000060002070280284030040c054011801820b4869072031030001642590014090400040722880d0811a2000391180300381e10800ea0f445e007400168040c2c00d50b41143c2201d046902c00044000c2c2c2982c0401441c0c0003c2c1c5959800045841c01f0300001780c0b10b1510b84100020440004000740410240d0a80304030701501c11200d41d049561190600c03045000c45440441d0603500c0c0000204074810300040251041100405400d8048540011700c040200c44500796a0050344070314402c59281081e010304e030404540c0740014401103c0e64108180300502c2d034110b160510516070014010030001c000221003421680b0b01c0540d49801c0130656021400440e44040c654840c102d210224440c1c1c0802c1190142800f25020710130300d8007180801007005102100100310 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 528252410 1250 528251160 528251201
    0x323012f07082203052e0606230712021c051c0b041826030601020a12020a02060d090309050906100e0402041208030709080102070213050402030c1002010c030501050301 74
    0xc3d480d00800700100445000c0800714a030740c0e00da4400d4030f440b0240c9000414400d481300c001c00120b00c107480f10300b2210300c6500c0038004503141100c060001000d111140120585c1d0251851941d88000111054182c3c441c01c071616264122100a4580c070035813010300c04060050b000b00c03c0440c031410544244501c0c0c1c0132000d0351641100e800c10300400e1000804d5400c40d441c1c2c0d41c281c05a0bc0519a42c4070414000c1140884248040121140820f0400c12002d01000140700740310842e41d0004003044030b168850f0503414030b6840c0c0201a032802c0c0590200941c4180000794814400180c1c0e046204072901ca0b8840b50b0315140c45000300032001e041103071959041002c1600f14106284100040f2403a0703207020b4001498261210303004021800303800003d6404850010511406030f60100c126001010040300850800b25190300265001c0c0d54000011141e90f2110702040c199902031105290b5180d0007040c1d8883c11010f11000b038080c1a0a446001c082480c1c0310000900d07040600600303440410001a0240 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 528253660 1250 528252410 528252427
    0x31c061409100905070201060513020304120804060b0a12020108090f030a1202040f17070e04170a050c010c020106090605010e0d120221130617010323012f0708 70
    0x59807900100707509030380010840c000580102e5481440d000310080d9001084190400040c080507255200141030710a10400400000c0341d01460319182c10340e46460400c10545503828001c010742400c1c03000660002d003203100020001540d0400300c945c0c601c03e0b02e850b00681c0e12141040d80300d4400d001c203088250010865503c1d914400c910415200715002030041c01d181e00c1c0d032400084026942c1007050500e80000f0010300c120401c0000d000141200440e2840c3c6180c242d960503d03450781e04120f240b0441e4003090140005010f0000d6800410800000304039040c09054001c0c0a00180e00c22641d900345000d0002c00d06510540b455a07d02d42c0103402005008580e65034559100301c07880780c0034211300595110161407900c001407648820002c201003034442458100017a01d01c502940010140141c001c2c0010020300d080c80d90034110780c0c1060514407100074502d20a40520140450328a043d442c01046503100c60000c0080a0f1075030a0508424400d40081c0b44400203104220024000d14001d010700003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 528254910 1250 528253660 528253669
    0xf1704050a1103071e0305120c03040605090f03060f1902120f0a110304030c030212090d0b1909061401060f091a0910020d08060303090604090908040b0c031c0614 71
    0x40c5030b1600a01215051907440e0b0100b1245280580c00c09000204020300300140001005a0b94500c030360341c551645850615415035549110314030840b1f05018000c500c0c000b10303913100640c80f189050003409803a000e1030501c0c1011014401165080c00c00ca88200703011402440b40d00c241c421001c074098407455240c480300d8440002030b00050842d2111307034903000100c0103082c051001c0c41c0107a11a8032007403c04081460042e045c50402010b41a00020621030403410759284036003804807540100c10070032a611181040105021044191a9900d0400c003c3c44104121070348000255114500b040e10140d0720340c442201c41061280da910005903550a007403285c9414140102924003005c80501d10740f440700070121700c0d00001c8410700000740c0c00101ca50030520b0740010420350301c41c40c11005035107052100c4002462a004900541040701d94581501007040091001c9a01401c0143d11554444007802c841c19640e40c0840191507400009107440c0c0381e145600d0140720146c9802403241100c8904480902 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 528256160 1250 528254910 528254933
    0x812310f2c01050f121606020609010507020c09160315080a0c050f09061e031f14010501120c110102040807061403010803090409020f100801060e12100506130c0f1704050a 75
    0x1171101c1c0100d4101c55040c005120740c46d0000c0c40c458025000c10b203410030415007182e50080a460940d003160101e40041d03610144041d62183e6a908010b80035441208101c004010300075004408070801031020804101c0040d82c440d401d8400e001c038600464681052181d80381c0d6000d0750740c0e0050300002c0460180e1030500000c1e408001c0bc4ac0944d010030180c1d80009181c20905180c0c001042d024a000e521482c205000f040c00d41983e0044110003549094002031030b14028036105008107503140ca4070b45103103104500d501440b0850800964507107444095680e01d2300200c0c032490b00840c0746440300403000b48810040d81c0c1210700d00c101847c18040c0800601029007851602264031003c030594092403645c8900f42008802242e42c0d0b8190f0540c101000607180030f80c0c0000301ea208140390900242c2c2c240700080c0010000d07003940804035103604ca0801040080c000302c80440401d40c1440d030310781c0c661540013025031102c01c5290794041d42d4220301d6050b00101c40003a40c002e0f000c1d80002050708003080320800345 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 528257410 1250 528256160 528256189
    0x3040911090f0d150c030f050c0c0d0807020f15070206132406030b09010b090a141503120f0c0d0306060c030e06130b03010812310f2c01050f 62
    0x20802c01a00e0680082201e1000340c42d02c1c0401d47c1d0b410b05e05021a20752180a038808440844c041c03038503110307050941d59050000045000c0001d0718001452052003030000440d0140f0035000c1390001c10b01c0314101d200d41c04049a590005124103400104003140c80c20140141030b0f040b104405240404581e41c032090700c0141c4007085d015449060000014a441055604c00c0d00d000d40002410341480007004050040a0070100e1001d007442c02d0040660080001d00d90824a4881c0c2d4285440e0340201081c18400402e0a190465030003140422111042c80020064000c001d001d40b424070780c0c2c80d0010340c100c4a15006101c002001040302c100040d0141e072540c2d116190052000b82041407807113542d02c0ba042550480c0e07903c138801000401102504001507202c1703007414000790303062041068000100752000c6800c510101d2081d00030480466680540c480a440441e10785511541c891000c005880c0c0b1020800341035140407001008802d2141050300d0607107000406030f0651505100801c1496a1040036 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 528258660 1250 528257410 528257423
    0x90e06060a0e070f2c0f06031b1303020306040311070605030c07061d07140420030610030b0306011403060a0614130e0a030801061805010206010501080c0903070803040911090f0d 78
    0x1844558803650140c05d6400d81d83c0120000c0d415601041400740c9180c03984501401004240280320304043e910480644541c5186003c54444186020f100242e0b409548007079003501841d8280014541e0198038014010405012900d100d071740d411003210f16100c00c807030708040c03500140300c0382d00041c0094024070000f80c04a844803071030b4a240007501c0c0c0ae044207941302c142003c40024081896007480c3c001c1d0850210328200c5100400d042000802d41440000c0038a482141c1d66820710003a28000e030712480c001440501250010340e16280c0c1182c0c06070b01141981d100740704450000d82c04441c0340c001d40050384e410f05040c0e039803108000140511240c4484165500c03644500803009110400c0020340c2103075000360b50b01c49981d4503202018001c4030303865408200c0261a0b10301030241703980000754181101e20038604801c0d15596515510701034058420b0f2282d0500411000003000540080500180ca02266082045083c19040002103109049086800a40401c2d10f807800349440401100e8140c053b10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 528259910 1250 528258660 528258677
    0x40f0f050303070f0f1a0711060105030a1103150405010203041703041a1902121005120601150e100e03060901060503060c0304060e03031006030605010305070206150a090204090e06060a0e070f 84
    0x64646d04190107030018900400840c1080154050f4418480e214051002c2c010302a154105000700340c84805c0108081d0000e6442011600c568904001424181c0700700051304146060904d8058045e41c415a820b50703010f01e80c07191b80009d180c40d100440c2e0043d0751140c540c01004810509a004a100c000d19142d10b220a10b81003205103600ea000400ea00c0d00c980c10050003a26192321820348203441a00a140600f00c2010480051100010454103503401501c0020b65030701404000c4510112010426400c1811080c1940d00c035904081210702d00748d81207058841d65981c27140c13450b00b00c4401e4031420354154003c1c40400c0450b550382c8020f503005401403e000c294103a908014030701d50b40c4241d0701142c0c984d030064001c0200540c5840b480f0090030f024681030240e82041340d8020355804001e4441c11301d00c0032500d503403d46960b0b1800032100a1404c5002076443d29038411124000781a07100c2025840c0c003600700011034078070b8125100300a840d0410503242554542c1a022901c41e004000b41805001488 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 528261160 1250 528259910 528259913
    0x1109011b110d05070f0b031018110406030212220803040503120f04150218060d0f05090304030c0519030314070605040f050d03050105010e0f010306090c05040f0f050303070f0f 77
    0x701034030b00090340954010b0a24924107040c00b200c2c6034490303001e005406003e1040c07044824038031091408680940c690814008403682e03104000740022a207500240800040004400e81c040e0060003944600b00b40100c020350300c50b01da542004041d90b030000080b80b0714000000c00180410301641d003150007072080380d0402c00450b810794808001500c05560b2075502008000c2003000e1041c0205146026410650034102a00002245281c0c1ca4030618410500400c110107400141c0c0d00100c07120a21b503d0034851070400c44003851f2668050700003a281c180280c880422207080c00440d00d0961018820014496480c1d07450441e841500ca8003206040c800c20050440410350a01526000301d005282280c264040344c907001d807420034100c900b00c4c2071500f40801040079a8201042c4450f40300c0030b541c0030300e00001d000c0041b03006240d0740e005107400d94600034203c201d00b0380c0302002e4001d403810101c030300d58020b4031600044204490b921500d81c0c1980100030700400500340032840e42c0c1c0203202d01010500d01245 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 528262410 1250 528261160 528261169
    0x30a24021c0225050d0c1406040b0603010b0406050a0e06120703201804030e040207081308070b13092a180909030507020d1713091109011b11 62
    0x11241e03039101c11600441c81000140040358148a400000b114940708040300703a0b03586803606111054402030291000c6030405102e0468070020086840c0c00640e5141c0c80c1c6880e110703642d00fa0a4a289000c0e42c60b00aa0104a040510502e001d40c1d00040200c126689898101c8a02900c0148401e81060300304020070400c01003088607a0145205210034003d4940c0b0588201071009180b004034465034080c0706c00e00c040307280c440c031140d0080c0c0c05140000c0843d40c0364010030003a104880c1c00510711031000800346003c0300b00810050035680b4007004d440b1082c0d510748000e4214000e88481c50a9082e5a2030304200001c01c580c8001d0900300130300c200d0060003000361a42d0002c0880700509001150b004181e150213180c031500f4000241408050403c401c140e00e450041840c000c906000b4007800d45a0070b40070901010301c2c90f40030781864003c0280d944800c002040006405580300d01c0c2e000a00b00004101807041e904d0648002c2101039481410701031524240c0e27054140c881c90241c46c25100b03001d425046844 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 528263660 1250 528262410 528262447
    0x9020a2102090405131203090206130f0f0e041e0c030206041d180705060906040305070f03050708030a080c0a1404061d0603040f0807140303010e0a0506030a2402 71
    0x1000380c010789800681c0144019201c00424005401000516080001e410540c0c0785092044500d000500c820907071022038424440c0400f650300e070440c2f01c103000078150651100102903400c41c17544080c06030390f030703da48010021060390001c14400103d0b03045050151101001e641700ca00841c45000c0344c4d03030360740c010540583c000e800c58000d001c07011402071084584540841d03041000342e43e02040402c00100010703194a06405080d110f1070f800100ca000c2c0e540e44606450213036030080180c1d81d405584400b104900d4149220440d054020500300003200c0e0004410740c0e10702072207a29504460390b01c0ca10004959032000036004c003032000d5104252016081c201c0644040e28080d01d40310a1504243ca500c40d40684e42100a403040d030040082100042150b03402142d40e075031100d040d03512101c1c580744c0114034107201360031030030704c2e10000c0000204204000c85007401744000103810400340d01c03001c2c203064840348840070151003680850a4102c1d0a0400c810400f1040080d0740c005007000d1001501819291 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 528264910 1250 528263660 528263717
    0x3170906120429150a210326040219060801120f0c0e0105040605030601080a06020318010903020c01081f0b18060d1a1e0910030f0c0f0501170109020a 66
    0x3940303c0304001064250740d65568038814201d80091a0318a48059a00c00800745901c104950041003d200d04050043c000c0903010703480e45060303004894004101444a40c000c6900341d00c140e81d42d000048880c80c0440c054003d40745c0ca41d580c400f1913800c1a07140c000d40300407450b0031203a81601c0443e107004502c03515010030242822502211055140100300310550784950400343c800d421007001000210300028500951a9000e5009a120341d68901034403503181302422815125420079918404060340822071004503042621000c005440d9260041d001414071502c0b180120960711b4140003403003500303000d4890b5070341c81b83d400d054402064020800c2c44d00701154a4020075100c880000c0038144c200740900701e044098620404e00392402c50b88601c4003a00460142c000c25010b80444e60072124850040091500030b0048e880765030b203619058200038040e119210701c8690449000c922903104034842964003808450502c0325909150b4008020352220340d001c8140080c20780c030b030180d01001c19040100170 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 528266160 1250 528264910 528264983
    0x13020306090c0f060c031b1606030c0801090504150531020a08010e0601140607020607110a0602060c1819180e0a0807030c0f0813031709061204 63
    0x21502001e01c003404044441032886058140b10172128110300000741c070010381ca0100c041507810a085445410f2000c0d501c8403442140c810340c008602180c140d084003c0d011060390b29411241ea07540762803000c54205450040084800000820744603d858104982002c14079050550005804d400c80310008103d0403501c82c1003100c040031a0a6181000c00d280040501c800280002e90348040708684405e0f050250411042a83e407240e1680d40f90780040d507100f43d5020700440d544038403d0414011203035001c40045c0c41000b01120114542d403003c00d449001d040502c04190400c0c01101d014680800c04510b04d40d000862015a1010b061003500494000c00c180950845808103a900c40402d56059550b030f0078150740507680c0e4800090f113040895401c00c0c1c243ca03100802e4402132400c4d00001c1d01800c8003500464000c0387d501023144200302084102c0f442a540c010a143e818000c4d204640074070324107603030301003010301540c090690300b6419954014800c418181c41e50301d00141c0c42d120022896081e1204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 528267410 1250 528266160 528266173
    0x20408070513090506060d141204230a0605090d0803071107091b08071814270a1d0a1104140f071202160803040620030403081302030609 60
    0x15410950a0401d01010802c028085074075180c072869601d250142900c1e0151101c904040240100310042020101c012802d0301c8214074042c800d00382d00d400c14050041074080c41d5182d10075640d80c0f107049012007240070b026090207501d0320006442c2600040d0104c2e400c2442c080d400c00001c4d030348400440c40346001c3d48a0300d8040700702c180b90500d03011040c0c00c42c00d60581344c00d4a80094100302c0e05a001241d4240c0750107001659000d0085031090036031420250f0000064002044032080701a858001020a540d002904559101803043c10444090f28502d20080c2d000407495044142d08130403919000440b036420720302c9800c00340f10703c0c10f00c9070642a00e900d4014400d01e2540d01e030074061b00c1002114441080b80c50308202140100d418405070062007804000c01400604040c07603016202d140c62034a0610403520114280714101d03134002c1b0342c2151000c0c07400603400921075468450404910014245a0a40d0340e203039426100c0719000f0f0302c00c46028044040140040c3d600b08807007032089940302c000d080b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 528268660 1250 528267410 528267419
    0x5090a02120906010f030b0601030b03060709090e0d1223130510020735040905090c06040303090320210f06070203070f150e0f061f2702040807 63
    0x3000760094034622003030b040900100080c44102c0791007420b4070340102c100902515840d0042c1c0080c6807850f00b0783c0d0140078501c1088000c540001c40704080301d80c9503c00b405111400304800e40c0300c100c1c101e940c00c0810602c000340142c0000ba94032280c0703d1080c808159007501041c016807004100100c0d590094a1818a419010000c0500c04d010a4403124a130a50070000c80ba5650711400c035900302da1003544030101801702020b26900404882d449000509942d42e16254101c07203018201c100d44200c054230801071030490321706140c01204c0449030941d0b294104282943e8604505182d11801c02e912040700d982c8034441581c48080711000a03002d00c0301e0307404140180d6a11400e00d12008004a6650000b10030803696640110884001a07071081d40211b8040d10f40c585104104012200100d4180c980740d1400050500010204181500c00044810503951040c148480317440401e0030358101d0600c11020495241c1000300c3c0c146081e06480c2e040324200750070507128202c1e00554030070320861b44441030400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 528269910 1250 528268660 528268687
    0x8060c0a0906090302010e0d050c06040803071b050303030606180301050a0c030b010c020603130f0b0a02040515030c190c1713050f10050c030f12070f030c080a0b030705090a02 77
    0x8000b00082d00300660030300d1440d000a4601151100d4903809039000303015020030420140050303000d03220018215a05c6907142c8180655070380180c44212030f04010b144100b0402144401c121088480040040d0300d1541c0e00c00c14081d0540110952144400d109240040b20b40d5081c001c44e885840303103d50000d0350401c064130042c113440f56180a54103010051a80c040540c840030201c070303803240d00c20106445800e401e1070f003010341341055600035220401c2c41d01401680a01c64000704110781c41125066100f02e412070122116100c207075480007210004100c003c40f10803010054203000b105134104120794800c50b0300e9101f01c102052600c481034020000311007408032142440d402c0901800d0307604650341d924440106035000c9044448000f4403c000c600408004802c1084440707410400c100c0300d45481469140b0b844111040d5212800300d078a103441154414802e04c03981c0340c4a001642c400c45a80c031010b0218008000180741e2582500800e00c000c04e07e6251801040d02070303036030007100581d12118010300c3c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 528271160 1250 528269910 528269927
    0x160516080c10050901080103020f01050403051005040c0503190b070c05031c0612080706020c12131a0f2a0d1205220b0703060e0a0b040c1107170708060c0a 68
    0x14018803c051040d0141c9903032125130681520350681c0c0d006468803c04005840743e0041380e0008015104541c450140e0015030740007140128459840c401c4040c0e10b030001c0607210614260348488d8611016696000300d80d80380789041d0001c10900b403010201d00152a81c0f41558044112015648445002c0000c1e20403184079440007050001010807040c8401d83e2009410700c00c10700043c05168003c140301c40d10b00c205014404118a2815469903201e413a0240b4803810200f51144003500380400c5100e10038141204111092480040e08192515014482485684010900c0380c0071005c240101d204034818208481403003120585c40b07049aa4040c010301000f614030080590700807040340480811030f00c1c900d8901d0180682d11000d074142d50340d5544003c40051040e1340c440c900c900814800c3c440080429484480045c3c810b079028810f08101c9841513544414018450f0110f505c1607408011540780d41e200b0045094030382e81a01c0460750b031640114508042982e980c4185413002a08030000c58004240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 528272410 1250 528271160 528271189
    0x150e041404051516051c0605031e010e010203010302012001060801020f12060303120408250b1e0c0d0b1f030501051807021b0d060516030b030307020303160516080c 72
    0x203403081c41580c0c20000700380c2c0c01b8544072100001d101c01d04100441405070030610140c14007a00316000c0004081200d044607a0550322681e85528000b00b05400c00c0060086a061741e4040c0c4490341640c10654049102d45242c0b0702c280041d540e108008a040f95082c0000c02a88a04503003190b110403400b20016803030280500314a00c0303075204020145c48083d05030b2050707902541003a1010307240c00768844031140c000b2210410841e004100c02c071038001c1040035502240203108050300d43c0e5800c140c0b01c1c0f81c0c10044030140c849041d040c0c0240200c426030041900100c42e201400b42c204800c115140804400d04074502590340c0c0820344640041c085803d00e210440b4414021544002107820011000713519140c80d060260310340d611040700c0382c101b0307100e9035040009598009410081b51400c26402d5100c01103030300f200c0380041e013058079050382441d0000903074181d90f40080c0590700c1d051201106407452000b0f00408c41c0c0c98018034241e85514042d20045a00818010f80500030309a0741d18100900c1d0103170005c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 528273660 1250 528272410 528272431
    0xf01020304021516080406050406110607120c0c06050406020a0f0516020d0f0506270a080409051b030705040501031521030203130909061104150e0414040515 69
    0x104805030355442900820408103a03035150380d5280c039a5200061303040b0660090180000060002401d9602c01d0080045035842d50b030301078015514060311622a842613a0010014001140300a5000b00a602c0356425110608004881136520303030b2104103440c801c5400ba0351065011604541d103d411548103940d20200b458000d2030400d11846030309101020741d8010340a821a403003001c04201d09441c84860b000c2c2c10008540c414a0080c2200d04500702e02031078010240781520840d039520b03d00241c403901d003a40c01544d1608017410b00c028200240300042c03030380089542040c912021280146c0086015241c603950b1140d449083c180003400361452041c214500c00e03c03000302003041c1081c00c40c0160b06101d410b6410342c001d4078541070491940c007810314201440c0e1404000004c1a5110b070384416042c0c1e20400050100352079401c4c1081090085100b28898001c1c0600505042c5100e01600c030480c0d10001d00c00910480604080e14601d981100c0895183c0c1c81a0098004410141069540700503400d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 528274910 1250 528273660 528273667
    0x1e070b0c1204061a0402030c070c170703030e0a1d040507060e090604090303240e13120c0602040e0c04060810031e110913201507030e03060c0c0f0102 66
    0x480d01d54024a0040c006070400d50744000031031090a81d0500c0c8425003000030420340d124244050b103110f1903070140004550381c520342d100008101d10310104110f1110350300e1000e0300d4801d1071602c064611010165100394080c0405401141d070088551401c2006505800c10300840e1910746130940c0340c40d001c1e411079020700586e140303040c10f66643d0002466012380269000704d039140301031609a02510524401c0418800c2d100381d00b0140c07501c60200030048604030000c8040a0b115280b801c41c111009800142048415041d0035030094003514000e840680f091000520380313580c80070324218844096504081d211000981003210660050026420050001c1d600f003c2c2c42c91680e40e803d00e08110201380c840c0321028046a002c1c8804000828010000541030000c0391403d5801c00c401c81000d460200e0b15940c0d044c50f8441c90b0504e040100200321409023004490200c40252404940c20521080f001c01c60308500343c854903202801840d000321482054907880c1c00d64410302c141400c1d210866003451340e1051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 528276160 1250 528274910 528274927
    0x60711061503100222090f1a2b050a0b01050a0519090b1302071518050706050f0f0a02060105030c15071106091f03141501080702031e070b0c 62
    0x102e00440040603c400060340d07030314820304008048581c1c08206540718000e030703000260703401584c0041c0d599801500c4100448060441d44000381880000265000a0b80000394440b042002c5001c2c0c400311050200f84542100c2c42d5503051030904800400c480f1840081d004200a0500000c8040580400c9a0103048200060080c1e1104c4801d48180340300742e0740742c607200d03c401e44404000c540000714102056640301d5131420b041001101448908480341d103451058108401a040c000400743da0000150540c0e5160440482e1603170854a402d03418080c0410800702c00303040b82401094110b080b134002d400203600d0311040500f00000c03601d5060080c03812280e501d044003850310131604180c0c3d0000302801080294000b040780e501441d400382e504042d070a049500510f1040c0c40f11000c0101c50361341403050407510300b6807401102003915000d501d40101103140c100740d80074814082d80b00c80d0320301c1105c2c1003500d200c0c1041e00b00b00e048400d080090f50700140c0070092101c10090254044003c110072807402040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 528277410 1250 528276160 528276163
    0x40311010b010e220b0d03080412030207020a12170a0f020607050f0d0504050102040801020328061202040b03160b3619150915030e10021b060711061503 67
    0x1c084e00201c03100c03810b40d9000051401342d0310500100b8405405000f1036585458003902084055500340c50101002c0c5404040b00c1c4a8001c81d18260fa01500248c0368524200d03006280e82001003046036800010b01003003010030b030070301c015011150540e0350f001201840541d029080c8040603149004000e0704100003804000d14204840303812090340d40000d030596640c1001da0090007540c002c81c1a40d4000018840b802d03070340401d410301d204810711480740c4820038180200e04448a80c4502d2400c002c1070120300c40545401d5000300080d81e405000c1c0c0b4100c1d80c407048080c0c9544040e40280b82c0c01c6074046280e50340f81350018524601b06640300a40c9017005e1900f00030030400c40280554038450f040c0e80c80070b500c0c1c00b00c1e02c040030303001000405074010310045003840103007c13000e05002e000001101c001d15030354401d106e80500311091242c000039040c091240700091010b50f0200034180c0d1143d140540c00c05290031708002940c4615195524140c4882c400c861950074a2070141c0a40400300325a0000d10142c0d40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 528278660 1250 528277410 528277429
    0x2180c1c230c090d0302030c0709020a120b0102060127050403020d022811030f120301150e1302030604021b010203160c0314180904050c0307060203040f05060304050c0603040311010b010e 82
    0x40491340d0800210251804a20f10302c41c2d40004c02c7c1501072000000307040502500581240980c03504d501059003d00d84807c0c08036010032802c14010790000c001040400c040c200c0a411541505c4150802c0545450b505415550f0544044006a002e40d030450301559040c4440c2541461081c0ea04090755250000b100240240c648e01a04426044090213456036040040c1142001014162407020011882c20300c550f4209204a2512031a600038503000140303e048800f48e0440b005101c4180b980b407540c5414000d4000074507481d08164208588202601421100f6151511120015a907442d0000c412a4070070380000460781880980240980000e0b0840003440c40d4000040e501a00c075201e801503002d907041002407003600840c285e030a05c0301740031001c500848403000603030480e111540e407064101c0c0d4901c40c40c402d44c81c0c0100510420300c02032401000441c1c000e8040e0040301d03151442100041c241c1d0717005680460200c0c0c046280107500090078040d103080322009081013459072162101080c0c90b0310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 528279910 1250 528278660 528278677
    0x30109020903030c06070c0201120c020d0c0c0803180f04110304030c02190b030901050f190e07091517030720030a0b0c0703020c0402040302180c1c230c 67
    0x54000c154200709460400a840c51030080104503691402d014402070201141084240e001544c04120070303005c040f4a0103219920055507005140c0460247c0085030100c070459001c5410103034131040040e04110070409418040240b00d90151504480340030484a00503000005009900303054111510f82050819a80e010703802d41030900c1904280d1000401804031900b041390100001340d00070a5200e00d070400385125030145002001709445600c140d42d0015000c54100c0c58000c003429600c503900d0a0723900040641e110100442d040c00e41c581052505807024030a80342600e00449008020500f16803500040b0000c11502843c58030103251180351001d210700c080d0303003500141041e8050907920700300510301c1c02d1a0072440c1c4d03c040741400c641402d0294840360781070b0010320680a107103800c1c0c903051080750200d03940101b01c0145010643c441c0c1541800041407451084428803807030880d1a403407040e04050301d504403c00519000303140e2903164941c0000440c514100782440400100c60f184008032003102 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 528281160 1250 528279910 528279929
    0x3061e050d0308070c080f0703020c0103140610050408060718090915052a030612060c07032303010902090406091518020405040e0f0d14070b18030c10110f0301 70
    0x9035540c3c4400d5502011110009103807060008030b007200001e0540148c007500c1d04c02d6090700ca84d1483c4400450030b0b00c00383c3c4000618100898045082442c05008000440a807400c0a90410350b4035105942803820890342d00300841c500300b000004000c41804500082c003403c0c00100700140c05a12940d000c440c11801c0c941c051036588001c21a06036040c0801b101d50020084050402c089888142d41207070410740340d00d8001d60005008102e401400b040a500c2000c103440c200d400e101058404481403a0707201006c81c200040030f240c100d10700c1040c50007140030744a10345025a8640d000e5050108840d20f03944180c040a00e010343e8030135090b259400020446906c0503c09141c20041b40305000284140d1348101e178007902c0c054007151188404682407451026050543c0d2000c2140981510046469003145240380f0302004410005804400d94a80015401c16910b079200500502c09107542d100203084002c3c2c3e800072402d103015803c240207050507003050103c41400c0141d1305201c08aa0b01041c024035080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 528282410 1250 528281160 528281177
    0x2a0e040c050415051f1d0a030b0c1c0b06030a09020301180f110103060b0322080301090e0705030106210203030708031f0e0c0316020c04060603061e050d03 68
    0x900841032150030241c01c000700300b04404a44140c04402d5601c551040900681400c0400411044090500300c4044203a45503000c00003181c0b40820f9901100c00e4010368444012800807001c15011000d8920811044a46503562580c1d54001c0107418101c8060b1a002800c2503840c580036120322040d250458003252000ca10489075200190141c0f048008041103064041c102c0030034402c0b10300301d1940d054042c03070000c000350950030011005e41d92207009041c0e68141c2000450003003140e9060346d019858400585854140c529500d01210354403e0384078003146501c90010000603030f014481100189030403002045802c0c5468801c014410b88a00748000000d0710540c100c0039500e080c422070f151180e0040c80603949140c09100120585640483d81603100c0d200d00021a20032088a60140900780900350030b411550380c4400340700084103031803401c003c6000e15940000141c4441c000e038409070980d80c4011517600c0c102801e00802103207258084103005048c0c8001c003d50f1702c0d280b6021406980518000c00c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 528283660 1250 528282410 528282413
    0x1b09031b031b14060301050907081012150e010506031c090807090c021b130b042c010c08040c06030b1f0c06050c0c340e042a0e04 57
    0xc50220035400074100048a00c190102d40e18403500036010f680034410381c6128085000d044c003405000900545410482607004241101e005040e548d600110030052805a030391954001105840d44440455400c0361000f0030443e0a0f1041c014107244441e00c41c005c2001c0d02d08240040d660310341d82d41541d4030018008420604280c818070240002c3c100107003c44150710b60380c2d2401e9004156000e5402c00500442e84400d2081c2a42d140502c1c0d0003500070140d240c1c50f900018034100410300001c10a610076544d4001400c00c4018031806a81000b00385000c0025205a02c0c00d1401d42d40c0ca03000100400040004000000d2110043d40c0262419441d0029204450324045100c02c190b000d80840301100f18240020f0595011248101181c0300f22418800c0b9120f9a0b80f081c03807402000b02070a500e421071455000c0a403400084a000d502c0e50500255428a04d11408110036030703160806004841c9920030442884030440744106a41007a11b400d410401d14510301c07898000c0203001d41a1a060354001050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 528284910 1250 528283660 528283703
    0x308030c0705010e070807062c01030612140c010201140f040c0503150910020715151220010e01020a0314040308030901021b030c0c150408030c0a061b0903 68
    0x1041c850340b0000800981801115007641e411080c4200f00c120320440d10f0200380c0394402d140c1790600c01c1c02900a101382007107400320f041d8965440b00a0b541010340c0c40d41c00062040359601601c843c01e0040a80d40c48140210158a00300340005406034190781c102103000f109004411040c0d507000b1901d40340100c035900c0303e240c00d4012075402c0d801241c0c940301c0c00b84040300b20031801c0d214034013850001c01294044c00d00e0010b40c005034000c4140203044d44000c1100c070b0f003214100303401606000200308011080507840d120008566151100300b9215819610121120401d17000c0895248150900b803100101e1003050000f550380c09406401400c020742140c00c400d2190030310055501941d402032444c0d84a1030a007107500c2c000e410038502c414503e011003e091980120120884041000c02c101404000310075806001000c1b0040c030b05030851540130000082d40081c1403003c0c080304003c4002428841c0300a0800d001512540008010b10028000e011900a07810580c544200c9600c4030325221014100360424 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 528286160 1250 528284910 528284917
    0x1005160609081213020603010608150a080a0302010f11041a04120308090d0c02063a0c021b0f0f0303070b0109051e0c0405120a080a0918020c070308030c 67
    0x4046a003081e000000b0805034101404001c081070424100070707a602074920b0300b101d44019003e9000038042006001c4d00744140045540b00205c80000c101802900c1d0106010705541d6014900c6504040e4802080650a002c0d40800501030341003480030307150b002884911403040e0b204a480103180042c140b0344a07071054080d1802486c140600703a020005c0c40c06d000d07111040449940101c1c0c0640b03400114018060741c0c00d090040c1d00a480d40303041405144c100b956285080ba000d0062460104c0780d0210291512484001d60f1784007040400d810ba040c5901030b182011780240f00d284102080b9070f10405488020044000f000100d80f41d141c05180000800c1c1584100003001c2c00c08240c2c1000401c0002c0c0e580c11003401000c0198400c40340c50342000c102140007005a950b00c2001d481000200814900041e13000d02e940c1c10070041c0d81828080307540e4070071b541c4d02040c19840030641c0d4090410114291a404a4081c003880c001035142007a0806800d4079034020340001401c281011020070170514405059 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 528287410 1250 528286160 528286163
    0x230a0609051501030207141911040c0e04050a0b061b2802040209040f0513030f0f05030f0c040e01060e0102060606070506190b030d050414030f0d080a020d0606080601020f0c100516 79
    0x180c5106032801030901801c5641c0c1082270b03842e542070740c00880c064200307403258000d06a0196101002031030741c0e0b0100310103400e010b845400c101c0c0c0c031805001000c0d65001b0007804000004c11141c805940c044a0550502501040c3c4010b502c003196204411070b484450311030703003c9a0490300142c0c1c81508500003001410381082c10b1003040d250004108586400c0c00e002e400c43e500944400c680c0c004c02c80304c100c403030640070525080024028004240d0491038500c00c650410115504141015121006010b80365001d0340b0540000d05082d616084658040c0320742d5420000035548285001c0aa403583c0741c1d198005030000b4100c840c0021440d604040780c2d400365000680040607280380582c0c05100502903049409230a600e0200f5801d011164036002032403c14840a58001d0000355054034003e03140840c0041c000f038041a0208003c0c03a000c25a440f4020140185c0d031512400382c00c11100083c44e021404401e007985600c5120000b96a0350741007503d44284c0280d1130615501c51f21038104507900740f40e1807030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 528288660 1250 528287410 528287413
    0x14130f08010207060f06060e090a090206030702060a0e0601051509030a0501180203060a150b0a031b2f03041809080301081e01020a0503070e04230a060905150103020714 74
    0x40032400080640041c10220300400040c4240c0c1c03c1c2c50904411900c003440b84401180c400783c0c030340540c1e0600204950344002460030000c0c4811180d0045155540122101da0050300300008100c080300d118400c56401c07034840301c010312080d03040c003010801070b0300c1281e2428100740e0049940d1816507810004550441c0c0e00c500203000507031140c01c00c450b40d00307242c0d1001c0f4443e0186100081400c1c906c2d1241d500c901103030010065071545482001d4a455111395107600400d5211001d0100c1003103421100301140781c1c81d540b02c3c2c0c2c0d008000130012484040e800d10781c001d840a10305903c03517006400025134080e1041c01100d05081e9070302000800050402e0900104000d00220000601d18000700711510780c0120540070505840c1003a00c030781e00700e201e1050b494000c00e4041c400301d802540b143ca184c0035a1440504002211101890a5922000409054484110701200304003116030f080c01994000c10a044e000e0107982080401c504600f181c0180d21410140e000c0307078210078801d0f0821344c03441c43c031803100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 528289910 1250 528288660 528288689
    0x603111b1608102f070203030706110a090b03041a1302031209100504030b041e0b0411040f0209030c06071b0f0302190803070b0c0d18050d09061413 65
    0x50710780c1c9a40030302000381a414a0304c1200750103194000d0b80c26a0800c19070b40c0b50030000c080040c80d44160b400c424400d980502c014849000004c03090320410480764400b06500d52264940b41000340301092075000a001e80e4424414000000d820f80740c0d061805000c3c0b020041565100c41e8015803849001c14080c1d894400d0003207945100d99080014100c0c80c03801e640d40e201c146141c21045e28603201e2072000500c81c0200d20002804611444015640000644400f8000640070b0301c45203e2a601640c00f0381b01681c295042c1140303032410784200f602c00b01001c1025414004000c0000762030328a811030113030142000256000400054403030320040c54032100a201d0170252121841c401c2d111090000b00d01603003025500c03150791001c1c00780042c21030715414000c625010140d600c0003040e2001610b640c00d0100141f180c0100c001450180490401c2c0e04003040b0ba040ca50750a1841c1343c016014000428401510818000c480e804510342c2070b0740b501c08440c2540c444c0d0704981c1010510030703540000030218101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 528291160 1250 528289910 528289919
    0x605090f151c1a03060a020904020904062c01051008040f06050f1b1c1a1e010e100801060503040f0209040c090c021609090c031a09070603111b16 64
    0x1111129440c00702c1c124108000e40600e8907a8a8650284041c44e925034030800001c0d40d46416038004090300ca10240c0b025051204900109041c2c80d60f5810072105080702e4420b0b20101e0040c1800c0d403084100038602c02075254500004902045003603a0b100003000f124034001814800761108140007a03510034010003007480c05d8004281c0c4c510f0151200c2006110405c60381040284090607904840000e8114030701d1070002845082c000d00e0a03030071040d8440c2d01070001c0066980c4004005940d41c40080c044c45d002c00851000600d0001100c1c5814424400404603d4604c0d500074206415140c090a0856131fa40360303414640c04049080364020340c4081e504003040100955024241c0841e40131081c2400307054403441080c0d84440c9601480d119190302c2500402c0414040e42003207014900170121000c22a850380c07600c0c1d008202100000d1003514038501404603c4008003c078400030900d510703041040c0c54004510195610400d8501d00b240030a08034100b5004905009807140c041c21410b140180d9541e4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 528292410 1250 528291160 528291187
    0x3110c0303010e090604030906031a0d141009050c010305060121020a0305070206060f010503060a08030f07020a06090609090207020f06180f0d05070b0708040807030309050a0f0605090f15 82
    0x9000ba8885880b402d408280c0c544000924a40100e071f143d1610404e09041c200100d006044040c505a40c0d40c0c00c8404481064485822100c682801505544241442c4c107180c180b40500404415910602d84011480414404200402e245000f460302040341d841e02070040300d01c1c1205511021a003554001001c6030721401c0d500030b2080c0c082c10b0320180078076a6060b000740e8690208866141d0400c030590407042d1150701c60001180d02610040c102c958047e2108019440c54000c0c40c0c64807120301000a0650551515200e080c006020501e003041c001414072000130140c00381842207031640e5801040d42c1e4115500d4200d009010740c4050045c41e20380000b4040610701101048103107020703181c210364a07422030070240b150941154210703004141c41464400d22540c183e011400a40d00f0480501022901c402c00b80704040c0114001e5890000413806d000401075143c40c7c03a4010207440224143c20400d19401801b0b6038007030881100c64815108442c40881c0c1d0041c4000c290101e000e400103164407200c0803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 528293660 1250 528292410 528292417
    0xa08041a0c030d091716033014010b030405071208090414060f04230a0b03070308072f040209011106010603020c1603080906130308040609030501050916060e0103110c03 74
    0xc0d400016080085160a03d130600c0750b800041d0480e01c5050009022900840340802c145800050001402c0d00480340345c00030780c1051003012311094885c0004040502c8030384005001d8a5400c40340c900c1c0d42401e640b010f13590f0a0034441c0c1c0c113000300d8180c402024003207000243e400380007028000b4854080148400c03040f881d0201e0b022482881e104480d41b003c0c1c1858407600f0700000d2403141a003600c1c00f4266111180001c0240350042440d159190180c1d03644041c800c0740300031031042c0c000369100c2c201c6240c0b18407400c080c6d6000007010380c0f0300c1117055104a209860048010030035100140c5e21840040100c5058072003c6008420b48104000050b00f5030b070507030003003000f0314145003914950b02000245074028011440040d047e00c0003800b42c64181d2070300034000c11641030100d070b0016159940e80c2d58805250082d0b8840030115403403030b00c10401d201c0d003801600c2d401000c032009408000748031503a401d4401014002c4070104164100300b11050b0740240e01020007160f0b09201c940d164505c0c051a070341d9950 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 528294910 1250 528293660 528293663
    0xf010617191e0c0306020c070e0a2007020301230915091b371e062007030615080d1209081204050a020108090a08041a0c030d09 56
    0x89400c0c00003424007560000709000641c06101440d808081d081682c0c0c00340d2051005030380881440200000141491000b040740c3c0e070380c050141ca076a81c60002d41c3c05e05060000d281920150070511710340081c051086070040110083c8140c2c0752680c1c4507002080c01004004084081c2c81c242c00394408441c4a00c0482034800c04104040b6045890420340745c00034408161140f00d07866001c803c0c03c0d0160604508482d14426021300300c1400d03003500044002d4012000a8080704220b014690021081c031031507c00340140c0031170f42e548040b401d0454506446d9a4285c03142c072081000b02a900d06140540b4003107524100140320894a40715104e040c003400400c00740c00350103100c0014110000300c45101003042c00340075503503484e0114003812100500d4060b154031142100c40600c100100041d10030010b0249010b140a100200110007a074400544540001f034861800c43e449034080c1000940c80d5000c613410703a070061005011825184006100900581015890740d000203c0c0010410400b50300c90348850703 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 528296160 1250 528294910 528294913
    0x13060203040f0215070c090507020f07030b07090e0702150604061208090a1410030915020307120507050c030a0c0212030c06090607091206090201140f0903010b04050603070509090f010617 82
    0x40d007180b03041013540c3c441d10320020410800300da07003001045226801698040c9850058601ea42c46152181c2c0c2014600d40084491518400c01d002406038804044406802d5080780e450441c21300c1e0a010b581e079413041144a108100c07041c0019000e84660708903030008c080d00c0341c1c01c0d05111031314640203405d074000803d040d004000b1148006100321710800c50b010880e10150a04490300e0444038114040c16000c0c100762081d0341005100300c101601880114894407040e0f460140d10340315610810103503030700a400401045024454411038110210850b4001885800c0c050022103213071021a1406810100540b894040400d42d80c02c0c01c000400d0540c4284984015900947e40d00c1500b07442c401100d008070000c01030103040c044005030542d400f201142e0300504194030b800d03490303211034a80e9600513101d0360007107500821a200c0b21300f000d00844641e81001c903020301c01d9150020200c0d5480300c0512400388078010000200342c92031418429003001c01d5000c8020300003075848121110b0041890405080035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 528297410 1250 528296160 528296179
    0xf1b0936070e0604050f060907020f10020d15050f12010b030a051501080f0601050103021b0d030606020f1b090601140a0504170d02070e06010504122d1101030513060203040f02 77
    0x9240501c1030a10840701080c110b1b1854440c0c006000403140010404010340c072500c0c40703165586100304940b603051080600c0c0076a456802c0070740703c420b4594681500d101e481407444244451b60381c80416030a401400c0d5849400a10403c15090140907100c0704950140070b041c0005042c4100841c43d000c0c0b01d60b404015174126661030858036516203141c90817010303503003100c001800150300c290000c004d8502100c4460f00c1e00c5014000e1242002c0c041d08280d00030982d030300001c00400d50184040811251000080d08509004240001028030b040703442e030740b140c02d0101c00640180e000d441803412607003131003100980311909800058400d47c40350045808843e103110074005a543c0000341807024a1803903000c1c0420304d142010720002c558000e0720340e50500c2030900c030100e801c0c0c0760340f40445400b500410f404051f031301c06200c0b1441071844250b19030002450b1058101d020440d50103074022081028a03000513070385d0700d0300004d20501c010480e00a1400d4000800d10051004802008a0b443e00071200c6509 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 528298660 1250 528297410 528297421
    0x90d050a0c0503030f0a03231303110d0806100306030c031a01150507150618050406050108010204031a0603030403140d09081902010c1502040303020f1b0936070e 71
    0xa80740100490090b2102c4104a0310342c001e88070b078019000104688003221103c0043c00a00308c2c811008481114034810312031400028554440300f000c400d41011405040248015003000300307000d81c020b1406010748441d4081d803040034403980c4035800840c0c200c200320140700d4a03450507000741c0510300424038815001800110b404c80c0c0e81103400c2c5800b101d81c1c44540c80d11506c0c0c2c1e02d2808085c0035071001c1d80c0650762841d00040401070915051090702c41c4400005540c90549004411600c043e08484031310780c41403005000080c07a20720201d000069500000381c07140d58940001740746108580000b8281c0c10720080460400c08002007290070722031207444104240d80c80703001da290355450b03294840e29407031704603800b260155006d4603407041e4403805090080c0c00c503100e20280600782d901030351040b030040e402610140305409060140d950942110718a0740c018500314800540011b0010f000c0e0411041526240b0b0001d0b03803201c2c2d00307006c00c402110b001e640700300f232a5102035204c1406104061001151100055 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 528299910 1250 528298660 528298663
    0x2120301050604140f130f0e0d140d0608030a050c0d08070909020703120203040b060913030801091805100e1002091503070c0b01140a0801141b090d050a0c0503 70
    0x34140da40160440d82031618041d4034164111841c143c042c0c004550a82203031042c5c80304464140022600030f008038075210303d4508001260b8841107800709030b0300a141181d04c1d4550100400c400209500152621032950b010504000c01c501e0b030055043c0c0c40300180310040d803600200500604c012030015180c2c0c13010100c00c141d40a0358100c510f40d00080403804c050040c0500b41d405001007a0191401012510221080400701d9209907025902032560310200201d44c640a10307441d5018443c680310112008255402070000701e418081c0c1d00031309c0d0311880802220080030048112554000040b0f8172a88448007010004008414000416000d0fa0041b80d103001c54600032202040b0f005002080740305a01e1012004c2c41d04090540c90800c020340c11070f000070641142c0038501800480000c410740003d00020002648070941c8912603e906140618903a4032607a0105a44541c560f000c0d90759600389034010344001c0c4210a1040e50249410032407405005002840c0e5180074815051114241e46540406 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 528301160 1250 528299910 528299917
    0x7030308070e010f031104051c0b130f110d1a04030216061e031425111902030c03010c02010b0301050a15090b1903060507080c0c0a14030d110304030212 67
    0x40f0701107030404c5100d2681501c6036000480c94400e41602e01c0c02c160b160f2002072030007000d454103c22400f09581000c0280403450b404150080211800041e5001c060364880001408000c0c010b0482d5800070403d00d9551640d480315460154400078592245101558080a071300c4140e4059005104108a04040540b411804010f50382540c80d09010b07070b114007040014818100c501c8a0400d82c40e604501404560300700864060210881d5200214a012018541c001641c0c90001d0801410300b00410808a002ca402c1a030310781c5050414901c4440340c00861310b08031009039000e4040d07103031038104805141d0640c44600018401c4000744041d4555809140c291009401c041140c0c0444010420408000358450f48400b0310150100800c001000c1c14082c0c090701d250300a550040d226010041c00131360041190303074007540d6500c02c50f0810102e80a0241c7e9090748040043c05121440d00c030448440e13042081d40c240a000a1040c4400e80c5010358900c601d4105030703000c83c05841400c024021618000050307 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 528302410 1250 528301160 528301187
    0x109020307031d101d0f031e0403020114030411090907030201020f120a050a1b290f0a0903180f0e091c08150904030201020a1103040803090d03170403020703030807 72
    0x900e80c900408290900805040b0305200117401c0d070012400c8100000e0102c0b55401c0d00503c05103854010700a0303c4100302d400f072030742c041011104000500040c0e0308401c2c1014040c2c81980381c2504c83e607982c41c002d0481c041401c205a4018010b0701000f40d1100005040b0040d24401e80c00d66441d07a0034421400d81d90030451100a180c2007003880400c0509124502501c09511585003004c0c05880140c2c0c0304400e418050020b0380c1c0589480d02080c0c00c4034450502c3e90000c021800d8640252038085104440740501510040c4065262aa5a818036104050040d6080b8108184030100d6968481c4211500c5e031502c0390030402441e0340c000450800e000300c0d0b0b410307030b451959003064041340c03c0e0351048644002c010b204007e21444d08200000c00c0d00c8a51545106034401e400069030f508003ca40078040b003903000304072044d960040206000c0136001200340c48035008141c0d41c000c201602441c0a03150f0b65048003c001050100701c080006055001440b502124003030340b00c250403a11489811129081e00c480c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 528303660 1250 528302410 528302413
    0x10f0501050f09131e0f050a0b071803060f020f03100e01080f0a060c05070609200301060f051903150f2711060d020d0b0301110a080106050705010f050109020307031d 73
    0x242d41001c140403604c0005041c00c1c040170714074100c040703070f80d050f0030600c0f900c606990641c45000c4001c200300d42942d80917089501d41c2417101007104e0301030409401d10003c0c04000c000d207480f08010507485009805641e60500302d150381755201e107009100300e100c020040c452076500300c426000004422038007242d131050a0100002420328059151144000703003541804490401c001040290089403551044020641c445c41c10764020f0614201a0120381558003545882645024030800c4258504042d0700111041a580040c1809040d403200d0790848180c1d00141c000355035001d42ca400481140c1c41003005424041f02041080420503010503c210046e0403070090384903090b00203011421003220b12040c032200804951500d80191050426600f02071800d00489440d07003080c09562500b0701402c42c4400980003100d040210107070000b4100c0406120303082c140080041c00c0420301c44203400415a40075505801e000d203581d1030406c07900951085501c600060300d0b06c0d00d06052404541a040d0b803c190040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 528304910 1250 528303660 528303691
    0x5040b0c0c03040e07050703020105090c2407080a090e0106140306090a0e07090902091605040510020c040c0903060b0315060f0409021809071e060f030e010f0501050f09 74
    0xa414040d41c012155030646100a01000840041e10340d4542d10503015540d495882d41c15a140283c29618003820030345c219000b0003091034080e01c034050451201c41500c4445502031030000442009445030a4010304004c2000031a181880c1d001000032048404540020704a030f0303a80d10007100c0c0ca4400e5590035415a4003000410018078002d60540c0d0405042c10000800480342072009107000d40703036440884c0c0d03251125000740541c60140001a480003115010050101100780c009004d8131940c014144544ca222488444080c070030003004d0300d00d240280c410440691500d00190014106201c11200386040c241520b1160601046d0400044064021700b0441e80390a4104003c810703003106500e410603070312004a40580e82e905000080000c0340b21200a0a0030400155420410144c014990300d03040c820f08142c00e80503e50910003120040c1c43d0011127a80348002c110050300300403e08a5096081071310710011000c0d1503001c81d0403280100c81d110552601c4100744240048120307528651080003c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 528306160 1250 528304910 528304921
    0x1202030402031504061503050c030705030309240c060718060f080a0f0f151502060912160503131e0b040504090807051213061b2d14010f05040b 63
    0xa141c8a13400074840d083c0030074049000301c50358002103d654001c2d2100d5100960308100c034201400b01d0805068150003851514605001040a90291480d50104031075080c0c00c0d1200e40d26004252140f0902146c00e0354441c0c107007a03a000b00410641c00300303202490940703c40020b982c0e00600204a00500541707034641d6599070300350040700400144a041c80d80e5502e41030a1003100591f0310400c00c0300c0181000c1d00e44c91500702004907100030300b4482c0450544d0f006400b40000c00c100080d41000c81b08034114013039941c802e100340054401e800c84100400a10020a0340c00008070300340c40c0d110a80f4003000c007810010700780c0940b11040082c0303441500c98150b402c0100f4007050a1980201c0d144030b000d0082c0c80e2901e005542c03554030f48150004030806203100818000041e4151000c51001809280341030344c0c00314014060307044150f18030b00d8010020143c40080b0b01380444403400300c1c1a07608189500b09188a50350400780c400e84442c0184030015480d18007205150400d41c4a02c40c01181c118659050554a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 528307410 1250 528306160 528306193
    0x5010f06080415110c030705070504020705060a090f060f051501050a0e060d020412350d051f06050a17010609050d06060e0106091514090f010318030203030106120203040203 76
    0xc41d43c900480e45816010803e10034050081c4a140450001580c0d03500b15818400c2c00c0041c29000107119900410245010032000148142c000c2d41c6e161b070004049100e490034a82075012558024030840c01c19a00c54204c4040d980114403468481d01a61075130b1040b1001121948545042000404c0c0d110b82140e0751402d12030041c09040e06484801454541c6500e4241c4021031600030898980c01510002c051042c1d00c400310034048040b00700903000e4108400000b00300d40c094000e0ba2112155030b10002110b4540c200e110000d907199001c81c1811041d1200c030010075036405170700c4030301c0410000342c00c2c0c2c3e42e000d074407900c2c242c1211160f59136500074508010821170b080d0b009203819241d450f00c805012441e0000c1a020754020030054642050651804103016039601140e91030406014060502c0e5921600c81d804480c86541e0490704051802c10b00d20041e0020305200c40c01c201041d01c60503250080580020055040e134090b42c0f259250a10240601c100381e1008917002501604501c029a03109540d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 528308660 1250 528307410 528307433
    0xb120a2708041a091003090b19020702090403050c1204050a0311030f0d09090b0103090c06080901020409021603300518100b01030606020706080609060409020d0602030a05010f060804 80
    0x11644115251599944248039001c4103050b0269460a00042d40c0071396103401188514074580c0741c1018000d004440d1645403c3d41030040c03001102e040800709045803006c1550480d00c0c0035500512594160800f42002005504106107040c40c6210b1140e004440c4d154040c20341701200c00c01030078040040e00f15a00c0c0c2c03682002078010301c1e806101c0c4604880310703540c040c0f0401030b800c4091b84c2d0304600c491801070150191043c128072141414544188440030401203034042040d201542001d008503120b684c200d50081c4602d0340009142d034804625042400320003031590903000d009580c7c1d0a0018024290009a80d03500b00607450303028040b16a403155440160070081d0707c9030312501504204890f4000c490f0034040c2000d107100c0e605940d0b1156003599038051140700081c20f02c601c001c0c030400d41000c0c40588015000740495108580010004400d944d5903042080901e50203005960f03c54060b10700710f400b81d0400d036030100c60241407034000700e40c04240701c8000084554994490740a0303116912682c20300c0030f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 528309910 1250 528308660 528308663
    0x30e061305160905100605040b0a0f23070209330a090c180e0c0409090f020d0c030605090a2d0506010b071e050c190504060b120a27 58
    0x3a58088504642c04050703a4004142050300812203240c0700322803551240c11078202d07000341300c0188424021a82004151030401c600e13070901104d803011a02c400e8030800441c4841c00142c4072070022005520012030098180c29200f9140c9800e140c592082d20090440070305007400d5940d440d8401c40b0400702da490302c001c124000c003404d142a065264020700b41680c4100407150045000700c6c41d0b02d20020f80480701e100050801070045409424030010f1841c4500c00c1d4400d840c100e40e1140c10000900c80e0042083d0381c103d50051001000001602c0c00820314210b40c0301c180e4082e890440000c440c4100031402d001c846501c500e100040040e40106040c543d46007200c5600d1103c00d0001e03003000540200034450190203140c0115865082c689014812180c0c0050301c90910380314004088002200026414010340d000c03580843d02d13114403142c010200005500582d4064104100000e55041e640002d01041d44200c600081031390b10002424181c541340280b000101c000304240120180c2d10008000c060b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 528311160 1250 528309910 528309913
    0xe0309220e01060b03060111010c08070509010201060801020a0c030f020604080421050f0c030c03010614010302071703010f0e09010b011e030f0504050601080616050a050904020412050106030b0601030e061305 91
    0x402441d26821034407a90059025600000240b00180da0801010004182944002e101901812070010092100a00700c0400d100020400ca000c80c0c2c004c0d0072a2000d0202d010007103440c1c1060090040000320441e00030340c00303e0700655480c03540c98804070b4020700c01c42d00100799520385803402985115942c41c940214490300e0050b5028000540b0074080e4101120032240107103d080c2565040600340010603805504c00d80c0740900400c13954140e183d444c0d2181d4024200140c46071520306100c240348510414078114068000004100100c1c03603145c0c0010f0f9150000402c0e1103980d900d01c61030894454400036408a100c054220004400202c2802c0c518075030f526003ca50307007486811407819a07005690455131f94000c200103202101c400c00c0150b41c003030700a40c600120403a00c8080075001d03100351507410040040015a86042e500d464045a00034400511601c0800030141081c6000705218001220484c40541c04900076611074042d440e82c3e441c5a4014204a480743c41d0500c1c500e141c0c081040b643c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 528312410 1250 528311160 528311171
    0x70c020103060302060a090e01090603150e010e15040b070503010b370c17091c030e220b010807120b0409020603040f110402030420120d120e030922 65
    0x16203d1030003074a503881d4147c96040b8183d04080b1400e00089050300407110841c9428010404581500c1c04408003100031280051410550701600b40034000100d0100d44521540310000340b0002d60326421882030b4040d4020a1641c1c40f403600849035840203200d0f035510180d05200c001c3c00c4034480f050054000101c25140e8031240031000540c6501200c26000c007000c1041c03010307688c4c2030111111602c0d02010781d0740041444c001d0900300184419200588411070500a40031070001c15014034221246081d0091040780009012014482e403003141c034425800c181c1c1004803418095008920030390141c9601d850b103400c08003200d99a003004022034004143d0160301c4041c080d02689844c002540564001c00c07008440414030b04100440e0180748100c5400385104204000102d0085d002c561101c0c0c410000d0440c8003141000000c80383d441082090010340070b0705855594880e000803429000000350102449001203605500b0f88902071410b155030006100c400e550304190f01009003001c0c040740c02c1800100c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 528313660 1250 528312410 528312413
    0x20061b1308010501120507093309020304060c020d020106050a17190f1403030103030c021302071a0601030b0f06030f1803040b0301031109040203120306061b1c020f06070c0201030603 80
    0x390f6400384d010640304c0e400307001e0a00c203201042c402d400161a84001c03d0062400340f191585120030020f4104403440e11032603002d00c994001380d4485008013407080b002e540b6030506061041c02801807030102000b61203406203021030a03006015810071a00001c25010b152407400c120341e070316010b91660440150141070800d0610703402c080c1d040045580a5409004061150b29000e4040400c4203040c2845070b00034001000001e612000d03182c000341d0f041d0391a4095440c0c84082074041c0c040c1800c0100200c0884810460100008403100c1c8502026070301480b0301e545060a00c44050301c01a004d9802c042d0400001350390180c004001d942110b040050040a8040c00c0e10042c21500150082c00803403070000010401d203d0100d171220100c07401100c40da4640d09042e40040c0c0c1c0c43c03407081c942000101001c00015255500c140903103c2540101c3d81d0104a07141c0c0c000350300e03201c50700c0e1000728444412440c0c10145a510000f0701560040c0c0d1140102200e071203030441034445d500440012810541c0b1001c0100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 528314910 1250 528313660 528313663
    0x5030604080405040e061003031412150f0a030b0402060711150319022701120612120305060d260f0a020c03010b03030a050d0213030320061b1308 64
    0x28030560240e164561103034204010030040c0c9a41305004035095011030300f8044d285440407668030072a6454204542c60320780036010603025000312920385440c1d6890408000648000000d00e840c0c1b00b41c1251100d810210380000c004d402100e500020302402032100000380182000001043c0440c001e082400c041c030104030001e811040c405880300c180c004080300784600042d2003080542c3d1403000c0b84065061011107440050800001c801400c0284e83c069174400459026035024908000070010074044103450700401c03210a8041c40d0111560002e0340e07481c648451007480740c1c0d401900000c00b9240000002c0d159811780c103600c103070501a80b441a0602001035412140140b00144a8100c003c0d02d1303001070709010342806020010b450090341028007030021685c0c0803007121000d503000d041140d1100b6101c000d4100038043c8402112282079400400300c141500441c00c510203040080080c00190f41d00e0030b0f569220b000a4900d0f0035101d030300254100c11106000c015000780c000e40010080341642da505000e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 528316160 1250 528314910 528314923
    0x6040b0403120f030605010e130e060709030308130c1e0504090b15180a0e0f1b031b0901030f0302010e0d0f020d05120c031023090609070210150503 65
    0x2120800c111200c0c2e08402900a036008a011105007405c02140d440c080018103041d000c06281c921690820207a00d5244a070380d4000d8600c0c0d031204003115610b1800400241c030764500740c0030035000b20743c00800241c40c40780c00308580b00003280d122110004082ca0607401c00710071081c11841030b60003100800702007102d4a80d07105259255018409003c02d81c1031004542c290b02e0aa000c4160144034010303412404a403509502e984c001403039040001340b03003880c03840f01c9040c1a10f540c5014843c2c011160007055540055803900c0114104a0035140c0c4000341740c030784542ea140011201a041080d07030b001040403640782c100c2015105e000717000208000507404030329402c240c40303902c4060208910010300100154100302c1035800382d8090512a140c100080f581e030740d0100c0000c001c4103100b000000061340018050340104c0060044504103040d580c501c541041194408a105500680300600013400605c3d000718007030300072030f00358000e4544010549405405803025405aa00a5040c01800204d90301e080181 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 528317410 1250 528316160 528316163
    0x216080703031506020f0d08150303130914041205030a060308030915010918200315190603150c03021e07060c0206090d0c06060b03180c010306060c0b0606040b0403 72
    0x1c2140760f841c035218400249800080840d03201600300243e42c02c1c00564403440d00300b2810419055910382c9522028a558140b2203a058040400c2c80000c0301804c07000e00c0c064454044c410700c104075500041c415501c0c0c080314050040f08401d80d005221034010802180c01400b5084080b404c50703184d4448100b258425200d00100740c0c0845121028411610320840c05440007080a00100011100c80803000880880181141303407281c0100c0740407880c3c1d0111541c0054040c0a44540030100722000701810000c440011139510351146149a19006215a6050303c0e400840b01c600b00442c2c1034154010141103a84c401031580c01c028880010030300d21300803400041401c0d10655903038264a0f0500564190084034010b5500c0385080c070642c4a80405c1c0c0c6031440c1c20910b040c44628100e401c0c00b8000e080a43e200300c407442d00000610030100c140300700001c51004010700302c40d00e1408202c0114111243c070301c50840050300051920001845d22400c040e0000c10040415060070748800c254013155000e40d20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 528318660 1250 528317410 528317417
    0x20c1005011206050105030c0a1418040305030714090a0e181204030204140115080703020d02190e011e0302090102070504050f071209020a0306020d150311240d0216080703 75
    0x1402c0d0104051400f03850b006d40030640141a201401e580800e80d0650035002c1caa006e1105000b14503c0380d2207000540710031443c402d04d901450b080500b001341650f841507541c400010054480d180d040d5005508640c40218064100e0705514500120283e0310217000c1c0600555118400c810f82e00c00c5002c200e0840861140c0348490b81e524514810070003200c0003481028000304084004110b1403401903035101c5040000c0c18440032a0340c4a8404400a02c80c0b61406180c0c1440404d403904071806c15031410340d00c51403035203d2807141032818006640c0d02c4141c9450000f62400c2a05000345d680c401d4001e04030140040c01201d0b00b0f5a1201d00041c203642c3e003144d60f900c1180140c1d00b0486016800224032184c000314040c1005804101d070089101c1c1d003074501000e0f15107600002c080003600ca09a010110b01c9004080e011000e23900d0780341940d40490242c1400e0304c6044007524094140d040650384c04452940b820703001c2d03d0070500d01c0d00b20001e50808030b50fa003190b00b00c811124001c01c0380e01000388200d41c0300ba40c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 528319910 1250 528318660 528318689
    0x180c09091006140f0d0c0b040909021203162004290a29070501150e060303210601050f13050103062418081b030105060306130303020c100501 62
    0x1040501101c10503802000c0110400843c4609138030741690b0482e030482e065030080d803110340904042802000756031014030340b1200018002100e560607440041d16038401c5039404c3e117075660b40c1407040c1d0307a01426030b0000e01200120090000504e81c0680e030504031607552810880001481c001900300e81c00e8224405070b0b44500c490040c00c02c4122280c08003041030807103109000f141841c212014112411040c540404a150b010340d40e0144c00b01d095501d11a4840000d000300213000fa9800c014a01c14800c100f95000310710081543d03403034088240d031034004040107030a4002c015400c8aa000725400340099051210822248040064080c01000c945116040100c03449140070700050444c0ca041d8450100e500c00c0c030074020f0080d0008612f0228000c1c142c50050340d440d4001c0c8a0000d00c04441d8455034884c03182500c00c00c1c200c080c2d04001c02c0004c50880003040740e50756990070b041e103a01c1c2c100d03000d901400803049440d001034040d074050541c4134810f900b29800d030042521800b0032a48280c000600144019 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 528321160 1250 528319910 528319933
    0xc180103020f030d020d0f030207080c0102072d11040e0d0816080c03060111010609020309073803070201140f04140d021f1107030c02190e180c0909 65
    0x1c580c110b1a1009074000c0006608200009495440840500c420007096070307940c2442c184030742c041da0f09482d00440c034995505000140c8034000c5d40542d60480d18039219500c031410100750420480200c86c00f50301034102c00e425a94aa40300ba5161511a07a440780d82c80341c070591014401c0200c2060780f003890712071200d9800d282c0310003605d01c02103100c8030040080303880801800340220802c0d20f0300b219003804c0c40500240ea03018224058401504042c00881c400700820442d0840000c0003c1210403003c6401118104015a511500410701101e4130b078941411462002c08403400c01180e10070303500d01c00044c1c0c0861044005480740019103c4030a0806c4d80e20038041880302c00400701108800010041006401014010f502e6031200a40741d035484401c01020640000306400508201d01440b41d041c0d9905000c7c90060005c0f640740d40d05070702810346109040410300140c0ca09070152000f01d9810344066a03866281c2849811281906800e40904400c405c00d0362195641c4a0080701032502034482c10045 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 528322410 1250 528321160 528321169
    0x160611071b08030c03040302010305190c031d0304030507050603060a0e09010515030a03021e010f1e0b090717040f1a0601080a060609030602180a080c031204030308060906030c18010302 81
    0x1c40d0807107078064108200380102c1c3d610020880e01101c1d030a00300400d82e41c2e211a0b18298401106414011031030038121074900d0641e041e80083d200c1d9005415500381d511501201c0d079500d0103180070052180d4000e00041c41240b074241d0140d540008003c00c0c2455290311800d04100a103010398080455a4450060008000d15050055001c202c00c0e0001c0501d0005518029650380c2110801d814606640e825584440000e4110714001c05110605011540c04111a1145848034001c8450501d242c40c074400d2051402410480c040c580035035400024040301c90201100c20406001111010100780040000494000c010b000c0c00098014684032441c0c41000134291820041c4400c403082d1800c2030034000303260084512000d130b07070b0002001030300ca202810300c1600440304200c2c000d91114001e000080e00001c00a1a409200826801e60b06071968440100c52540103a0000801085584000800307600300b5041c640d070300c2a4010110340e000b003428400300c0c080d0034050700a0035022501d50010700c2503040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 528323660 1250 528322410 528322463
    0x70302010311120a090618031106070519180905160909020306030a11240d0e06010608010501030c02070315090c080307020913030e1903030314060616061107 69
    0x84034403100303251807034a1843c500e9580000748452645035456512806000c0c3c00e50019854082d0100300503010300d51410040d100f00f5401c0d078050420b1080c10005004a445102518080002c5d000d06400f04c0c48888003c0e90500e202c1c400b20f0081c1e0101e0000003070b900f8039500039203000b61400d0340c2d503014480b41000001c0854005030051066680100140301c010b0f02c001900380e000a8026079010740840c202d800003084841c81d4410407244058803c6840c481c1d00b09000284483c080203032040003c8128a011907444150910844021503945801041154000d42081079110090700c1501c807060740725903507234411805284650800f00c1d6a95040343c1044800c1078454098600030004500341281da078009400d825009200030303c1c0e005559181070425000301811404408001c05648a41146464510000c0d09a05c016800a03060409140c2850f6030b010110380100c601a040f646402180000f8400c031050920003180c45940d1052a08031420b2810050103103a40700345c2a94288a4503000e598000303e6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 528324910 1250 528323660 528323681
    0x90905060111250b0f3402120114091c090305030307050f0f030901290f0919061508070f0903200301020706050f010b12040b0c0f0406020703020103 65
    0x1050300c140344488180015006031003c1c00d00096103000c2206030000281c41d1040e03201245484000c20313089000c0700e40101402545407001d10150b40139421641d180b1001d82042440615040710b481043c001d41400d03c500e11440e8140c00c008240c90f48a110b03051502c030300440e015501c54102170110288021445a0f002d03002c5403500e0300c00070b01d600315204c240e202c0c48060040000e0110018002004003440c5c8141c07406515480206a200c1c900100f455010b04065010f0398004142d09580150742c40801e215404020000b81075007001c1004a41405803903000600740f88030307031086091480884240d0b4010480902a26480b4040740842d500e0040d0220002800000501610400702d08020b64010321540441c0c0d0480c601001d8804400c102243d0111141d00081d00342d40005002d405001881c2c0004c1c3c001c0c0e0120503003c400eaa603d4420013614003c0c014040b04040b6a0008079000c603040006072030300026040030880c0780040c059196103003a0312175803245015801c221001c04c20756805128190302c03207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 528326160 1250 528324910 528324917
    0x306010518100e21190501060b0c0a170a05090d0c1a19090b0f0f190512010b03161d1f020c03060705071212060902280f0804030c050703030909050601 66
    0x8011300942c2a48034000061400c56a481c448540010710409401c103000070f080d002c100513074440401c6039183c2c444400c01c00c02d55911f10310b907a640e941342c1c400c0b60844501c0e1085d80d0b500d50908900d0b004002e0b1280c042a800c2e100445400c4012429050809041d410241e002450540d500b1a080d40540c801503142500c07001d0212412040100c00e88540445100d12040751072203540300400000c9010901a00c10310383c40c55108010220b5100341c00c0030081116600c1c400103d465a80d844420850303d03c0f003140c0461443c1c00161442c184130703008100f141d0b030400c0c10001c04000543c119002c40c50201c0b042c0034441d10882c1071911100c005406001a00da41c0c0c1c0c05070b0283c00c131482e05520191640c460000014001071185005100a81c89410400312003c0c55031428003003241d90b80d21040103500201504a5144100440036409401007243d02003c510207407200301c400e0754045010344200f08010070660134040070f001040000f03041032010300091132080e11a00d0401d82803064075400c0320001840d16050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 528327410 1250 528326160 528326209
    0x903140405090412030e120c0f010b060906070c080102181206060102191109010f150813060b030f030f0703030b0909100e030c0307051c080c0306010518100e 69
    0xc40e10b0381c2e900c1d2035115030040b10881c8002c0301036070101c0042c01e81c1800300c542c5005034144d8480004c480c0c0001c02844520000f02d40c140c6c800c060140382214840c040f81584040c007001900c0450030300b0780182c0000c3d40540a1800199a10180f01c0e00703aa000030064401407510311510301c0c1d149000c455041e0002241e100030105403900c00c00207945d82569440c05446404440241410000702d2921154042c0000e00344040a5a403407102c02c84505250040e207800984084c6040039241c41600c6072481040c000c105031040c0001078440c1e000412641c0d00c0c3c150103004441e9040c402900801c010000c0303c451a01003503440e101420010121664045c203244210300c0c050501c0f0f4002c10000b81007452001025000540700c455590482c03079440352421072501c03400089201d200b8403070701281e070381029183c070300208111904180d012107a0b120700301d0384102e0851080c00461002d500c214041c143c601c02940d0010406400940095886141c40041c603000868601e036000c0c10b0308208908203042d50880404610 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 528328660 1250 528327410 528327419
    0x1c0305090a0b0a021c0903020601181116110604031104060501140d0b0118092f120402010c1406090c1507110d020406060519020d08040b130501050a09031404 69
    0x445410103060200f0030b42e004200900355910032010540c54100e00b25040041d0600d51401944501d02403092460451041e10062640105400b5031400340c10715007240d600c2c05a803451b0b240e020201c400b40a90747c8000040c1c0c05605601c032400100051350240603101c0e92095011304010a50319a070300308138100b1140340009401008240180c0344200300b82c44c00801d02808100040310601d9441d021400c4d40b44400303800041c0350100e948441d00031506184119507542c00c0001a1103014410b08180031440d90030003c2444d88040d07820b50940247c414903214129072000d8961500c8420109801802c1d50050707000d0000424080090b04807810003a564425003064500c01080301d40a240e8022301074020131030000c802995035205081009500500402030203489200c000c0c42034000304000100021454080c06001d80002120013030320300341c1d0b45e4608041d03490b680d5aa1300000c3c041c0c085400c0100f2484108002102030081c0c511a5222280000c0d4096040c20024650004046400443c803001c000520 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 528329910 1250 528328660 528328673
    0xf211d03042102090109021b0105010b070b01050a0b071403090d140607210209030307050a08040e0117030715020c0703030203091804120c05190605100803030f0a0c0e031c0305090a 79
    0x1741152034155005843d00c20006603881f120f80c08424400b01780d445c017800440d000c0c030004064560140113400c43c080311f07030701c480500c240c0503141d0198940c000000d01000700041c0c600321141400b68001c00669040110701404a50101030241c01205d502c190507445c0c000c207150030442c1584c0701c1d4052800c0d1024046103000108111000d100b850307116900024040e00a4804100302c1d4130301603028045074140421400e1a40e0507402c00d0191442c00f000c54000080c1600c03400c0d51040700a1502000f641c902241940d410120110452180c1c038225028032011003583d405009100040d400794001d140d6400c40344d010824140c41c842910600360503504240004500056a40d605040682c00d0201d61241a0304081303141c0b00c0c05141114000850401c40c5040280a800003402100f840d8038402c030342a1102903072070f01ca00044a18003218102d0200080300600e494121210540d210308001c41c0f808107110209003008107070300c42c03114080d60340000e4012083d030500c9100d5015140c14007600c0c1e100060354800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 528331160 1250 528329910 528329929
    0xd05040503030f09160b0d29031204081002090d0206070b0403120606050d020c0a1b060e09060d17040b220603020a140d0b1c03020d0f211d03042102 65
    0x60210404a02d01c030301e01f11541d00110800c040d202034807500d08000103400d0f401840c824400c0b806401500000c2807443e1400058405442000c4040d00b08140d0098800317000750001c0d114503a0200b00d1032005000340c0c8400000342222030044900e01d01d540b0340781c1030140c14090106140c035041480c0140c10000c00754010f081d103526600003640582d5408904401a1900b40c04c400007402110018004017031a011601000c01212450313222003080009000400c42c80401c1114200c0c0c0003031001705042c0001d40502c00340030a01c03e0500d603d40c20652154024003a5411118041c0b8200041c000540700503402024900010310243c50154505001c0c914010249100d03200c807004c0b10000400d2080ca0342d0210742008810010151680003c00303d1004c0d03040e14480c0b42c2c113050303000d805400030f040b4081344501c544d250207402a840b141019120000c10603003404ca42c120310080c1c2c3c0c1e80c0b80420204200c850044087c0c00c0100c0f0000c50322181410100610b141540030082c0c1c4000c014000b500058850a514 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 528332410 1250 528331160 528331169
    0x1b020d0e0a1d100b040618091104270c020a020f1203070b090a1203020a08060f06031602011508060933180a03080a0f060f050f060d05040503030f0916 66
    0x1440545903d100341080391201c4e00f180700302c0d2001181c0416030903809601d1401d42c40c403005c190303940141e0b1481c0000c100c0b13919591000180b002040240043d2560048001c04c04051004001d0706007111480c00b402c0348c9031070b03e4100040c1c001030910030951030f100044508600084505820315841c00c03860319900d20074a5030041c1018485400107420b200c080c400445202e4001400b41605443c490303008000750f00605066012505240c00b0a50605140000002c0104082d00c0c96203503403a064200b0391000640d800d96003c56403983d041011811902d0b0200000740080c40041100d810701225090615410b2000c01c2940d006246940c001fa01109880d610300564001d003007007480c0c50702122030509603541003540506201e9143d510040503801040385219582c411001c005031852002010107990003441011440c461444041c02a460721004110910000034000c034a0f006c100314920003654011101514950004401c000d0481240c070790840c1d100003610060049002c10b402001c4098080d03000c1e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 528333660 1250 528332410 528332459
    0x20f03010c1e14090d0f14030a080f06030a021207180e0c061213020127380f16030807020606040209100c020123040504060e1605030a1b020d0e0a 64
    0x7058000d10003604905291150487c0c603250340d002620108030f590780e100308002400601c0400001c1d406102c01034400380038000050241a001c5015020015200440039a680480c01910000580710300085c2c400d48440104070400328085400a8850742000381121607603001e88002c000c400e250034804550150b01180311a0480951009070004840e501010b421440301e2004039401e4a00c90503640c646401100c4046a0640044c1c000099407410741002914401c110800c00420380030240c08040909529001084c01340d082151008000100132104030701076020a00c00d105011359183e060040540c4003c05850551520382c00070041501d24503c1c404039810811071421035021a0321400581d84c0c2002c0340700002c9000900f00c016580d2a901c0781c403178503204034500b400c0060286440c14005104821361926001c441040e4807050303500c0d80c4010f011f62030f429550300c100c0501380f81d43c4c00307148030101044d0f001b064061140d202c00760a40107054807161244e803010800308080c43c002d00e02d407250402e5018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 528334910 1250 528333660 528333679
    0x309090e071214010c0e1809280c051503040f022107170a0309062006010308030105040e0c031002180319120f08060409020f03010c1e1409 61
    0x526907414812181c2260b0031203001c400c0b5942c107120380c000d203650000110307200811640c0e00a46083c0c07801c40240881c2a00502c24020b124203400d001443c0562184240c1e080d5028074071220300b1403140021070040120b00300c00307003106141444998280b20000e440b050300c881e960b03588a50828205404000c00040507007803100320341c0c001c540b00c62441d09516440301001c1030581601941d030715162a00c274000c001015482d82c10001030150002404a0042d8054171260152410507000b01c502100ea001c20040e01c0812201c0d40d00a2202005018003e60103445074546950610040109641d07401a507481c0036441561108015a00481e0f56064010440801650703594a03005440d01d01610402060703240c000e040c8003e1001280c440c80d038000c140329a0500b0b100c025140710589081c0c0d0a003882000107025400015214200360380409140c1d07000074041d45044442c40b0010742920001c1d03005000040c0c035456480042842e13a130b00d101032080c1a09041c1c00100101d00034003002d0081c004d640d842590082c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 528336160 1250 528334910 528334931
    0x30106240e030a0f330c0309020a080106060e060702090406110412080a080c190e120708030a02010b010807080601050d062402010f020403150213030807140705010e061e0c0d032304030909 82
    0x941c03001541c03aa000d0308ac004041e541e503c089000b44018803d0b403011998202030201039241007000c07202441d6005001d20047d480380d80320240244000c000d140841c00041202182420f45a0030b205c04891107826150f44d21a41c0c030b98000c01c1c8503405442c40300105406e0006541e01841078032460801641403500d040048500c000240d0349002e1f180501181e400f4603c000320300c0c0781022000f800a01681d4000b0322a4440134001120b04030800c071041000a1045408582550720800040191460551011403a507840c0c4000850545c0004004454400754810b030001103502805080c0000c00c2c1d4040c110309242c650740703400700300514502c140b40034294000382c030380c80350502d05020390040d6801a986584035141850101c0c0300c1c0d6803941c0389005c18030404d68005078562042003050303071212025041904184100700d00d201144c19400c140c00b418002400440c609240800c160310301c000c0141d4001c034840102c401401c054006820382d481e410b0b031000d003c12010070307000f1141c01d0845892020006116644 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 528337410 1250 528336160 528336167
    0x912031d040213121b08031b01020910080711010614090414160e01140d060207031e021509010e0d14130308030105040b030106240e030a0f330c 63
    0x164412402c2c6200f007084003098001d450303484285003038440c6100740d001000c1031407a10352880303d0f1701c24503c10b98030800c05440219000074680c0714110300b1500140c1800d8010b80000c820540180c04500094048801c00080d10380c004861041608108020401c241c02c011402454048280109000b49003c1012400b00b1007030303204100300390186200f5591900d000011602581032180303e121404ca400c00004100303c24440c60071021520001c1441000d41841d80d039250181d00821410f9060040006038519112415141c6222802c41540a040741c00b411410b51081c4000180020500e07030714040308581c14100c0000d4450304202981400440b840030f040e4104024440c007070403a043c4030140c20000003001070724005075043c0e072030846050000742144400c5c1070880d40300e4842d440755020f0702000d940b0700704540061080700a03618502007041e0700881c3c4c0403a281641c640812540c40c00504130355000d00c080d602d00c4d401601003c01c0c0351042d03041e0300c440b441140c5d107009580040090399041c600507150f02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 528338660 1250 528337410 528337417
    0xc0206070c060216090c0801181b09060f0201020c2509020408011b08040507050910080a0b070e121c0306050405190c02070303050f09030307020910060912031d0402 72
    0x1d0290107034103620380300c04000352079944c680a0403102100809021032820308602820000e42d00b03d40d2254001d84c071300110030071202d005000074181141c1c0c0b07030101c0141041034074812041100c19182c4c040d031503240010092006605402103411648144402c144070700011410305180c1c6101041c40d01444001030f0606100c0301e080e03200d5103200313200150000b00e0301e01c103400ca501e5030500f08a1110300d80034840d1003500c10700c03022980208070340c21121050082e45041c4c0c0e5859000900c00c070004010039101c0f214145041c284080545408103124200300300d0343d50001c243c02d0ba01d181542c800d081100040703007469646149400400008015610411031140f0a500c180c000700070052040c003c03818100600d0820744050169618403030304040300b0740700b40c40c0002041c8040f00d03850f90b92103240a0101c000c1803d65040254a954903000c10030804016030744008405001320204001280401d140090183c011140c80c0d028003000c0c0001c99144c004030341c002803aa03811204010b405a20721100e40000ba00030300c0f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 528339910 1250 528338660 528338663
    0xd0f080a0204030503120132150909130308070801060806010c05010b0d05010b04060b04060f0f0e040c080712020c030405010302090a0f03031d03010c051b0703080a0504060201060504151e0b070f051c0f0c020607 92
    0xbca1305800c1100482d5245e4050301494000e8980c1082501d441031300315581d0f0000d01400700805e1101002c18072070351184500c0b003c01c0b40240c000240100b003840000320303d9107404c0c005071450307034460030058403d1800c0e2007444001c1c503090802d070f481d0515004000d0b14219081103018140000344001c40d020307900a0480c24030440340204104241c2d090204041c010751015512200040d81d20400d0103010f100b64401c4801c01c40c01daa00075030900e4079280044020390300a02015801825100c000200c50a0b108440c1014610a0715201d4519500310715415240001d50040761003030b810441490445e81c1c0000465076620040c0d241d04000c1d9041c01030035490180c0d80d03480203001040005503212035540c048081c105684441d130080c005503980b501000169654850300c0030000030354200400c003c07103034440034411030040e1440b00b0820560341d5210b40a01c0d00500015160682c1182c1d444041040a000786004c400c00f0324046040204a1003004107a1624102100305002d080213280c0300790b540700c10980c0c070003a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 528341160 1250 528339910 528339919
    0x120a061b02011d0c150d110a0e0103050709120f0c080303041202031306110309030d030c1205040b0a020a02070b1c27120314090a0605010501020d0f080a02040305031201321509 77
    0xa4421081f90307000c0b5813060f01382c01c0004501c800140c54a610034055103010704010b5440060351424403251024500031038808545140c000c80490000600303424002005100c20400b0b140c4918246c108050240e41400ca400d0441d0003c0200b00c45501c42540d1041c00d82c2c24910382415a1122a0829803841c49610000c0780d241c13064818903004503074142c219141d0914156180000314603240d5024041d5003056800030316440b228000505a08116400b6200e98040e52040342e41c03c0b50383d0802803602e94001c61080c4101d4004442207090300c1c100380911141c06101900c0055540180c0300b0443c018103004200804180481c0e060020325440303034006941c41814250080250b080c000c0301d030740d52420511405c60300c16080400003e207542c004140045002c0954480c204180103011085800c550010408400f00c1c1d420322010000c40e50030000352101a00040b020110795040216188210310b2021011b904808240802100c203003910741c9040810209a0340c0c002c030f459039800d1819681c060048003e800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 528342410 1250 528341160 528341171
    0x3073311060901060311030a0302061302040603140312070503010e0a090203010b0301061d180303151807030c0e06090a052b0b0117010902010509120a061b02011d0c150d 74
    0xc2c0e2606500c080220380c842c80c0d06255102c0c0b44801d150303c442c421a806000760300702e81c0000d803031842214000090b20748000c1000070600c0c0c907603484403603180342c50403a0720300c5510200303000c840c10340d00940032030b0084001d003851b904562503d00b40f409200001006040c0d10f580300c14400c002c54809402503560403000500910806440e200007120219501815010180301d0002190345140c18024148203584840080c500c1d5551391100f02c480301c8603c4d0850780d00500201464407c440f001881e00b03001c0c81c00381d54080707044d50412100500c11413408400354403403d02040b1007141c03551210b04035000c0b00e100380d500c0f0782200213a01d041e002c181d10076240e14100100d2510401d00300416550114184c0d604540c2c0e441a05800b48a03c41c00c980c04641c1c005c2c0425820480d548251131324400c55072000c1c0503042115000f2006680b40c03c140d80055602120b48408040c24410303058081c081e42e1403510340003059154072805400b425a690018008481c05070a0b40700a90501580300011a0200140407006010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 528343660 1250 528342410 528342421
    0x1529060a0c051b0a140d020d0c0902280e0307090e03162303180f030309030f0d02010b01170403030507020f19020117060d030e19030b060307331106 65
    0x40040b4644040d1094098030808101c0d02c860701758442040501403c003c840c20384545c2803294a0001070340985504000d20300004032010a40001e003800c0303046005c1d41c042140e842c0c3d118141d5480c0d4024003002c1c0007410b203550354140c03000180001201c011000204903c000100c0c414110721a0170a0550104900c43c592000d2001000b40c41c114200c0b1148140c02c0306490700041501d070301506282c00031040020740d12003414500002919910341000382074034580724805000a150592411550482d900009441d0131209d4080c41035110124003070038448403a826289580740750400c0248000c040c16a94000309080e24800c01c1011070014008040318010200b40420350010862004c0032400180c2c0071584564009860400c80d005000c042d0190154103000e54090301c04030f4a2000d1650407a0708401d4090340c10380051845401503005503682c08003810064103060800565811030880c40410303180c20380c480c2d001031410000b00760151038520034008280720210f0f40e40800c3c1400352801d1040f8028400c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 528344910 1250 528343660 528343693
    0x20d080901091706060f040e101505010f0e10090509010f154e0906050609040203100506150301150807020f1203060402040b0301031529060a0c05 64
    0x20034030200362619401d01e81d81e2500c3ca41162208581c41c03500da008100403480d60b0400b41d116100c0d500006001103a02482060384901c2d20b100440b1034062a0740b6800c006000300c84600c00040941801c4c41e0609150a10703010280045c0661b90071140107240080150345803074400d90303840d4013400c4000c01e80d401559481068501601c0c440c080c00803503581c5080c50803003aa00075030840304041c0d1050000000c0c42d031002c54540c0049140d4a01c070200b40c4070140c40010414452031500c450012100380018170323418a003042c0c01114001485d40303000381c50000610015030b80c0021407803d40342c4990320100d1030366900f0f004142405400c1c1000004418084004204c90b01c011019180588003582e0f0741c0b610342d807a040c01f26500e1416040040160b001603066440490f141c030000c41d481080504050304d000d50b40c41003607105a100361702c241c850700d0100800340648107150050b201701510442d00c1c03006d101e81508000c81c19040c0c5070580c030b04c140400141050b000740103101010700d00350808150b80c010009001003a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 528346160 1250 528344910 528344917
    0x20d111503040b0106021906020a200a0b0901153602070210230c011e050108070e01080c0603060d050604110a050405191e020a020706031103091f09020d08 68
    0x45803d0040080040b40c103174800100d144111500195410b0814500c1c1c4522000b0340c080c00500040000b003441d609240c002c26042c16654150b02c1000340000c04283c00d0483c40341401070b050741d5059044c1001c00017644d000f000d00c042030302c032540050a04240c0d07107003102a60b00044180d1481c640c40c3c60608105501d0681e010301091402a200403080f81d08101c1d045401103034000c0061004c82001e0400b0f9813400c848006400441e0603840000b411031a2009102a2441c45810b004000d030380700c000500c43c415040c80f58400400c0c40304c603000c00550502e5802ca840f1088550954001e15002c400191242da8620300d507085150000c3c00e50b041418141070004550030780000b01802509505000226401c1c68440c0d540b00d040c501100340058091441c0c02d20103071103414880c0300000103d885903490b0a44c5440141452009074008001c84c2c1d1414401a090b0b946e0b80d58184110f010520030003500c8040031444900400f590190000e03d01e802801c098018824214007a40200600c1441c800700403004005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 528347410 1250 528346160 528346163
    0x90c0c1f050f06040b090411030a1703090c1005040e0c1c0e010c1d31020405040b0609010f0e0a0f0303090302150c12070323091509010507020d11150304 67
    0x400407550303a400900c41a20401741881d60030400144c00600801d000304c0501c1340c0c021000b410f403030500101d611107080f00b050082c514000d210740001403041c5814200032154144400f550000f21300844082c003c0d080303018600c580340c1348c0d00003003000429410f0211300720392001440d03401644c482252a5003900007080c0307107006001700d98a132584c040e801ea4000c2c0081800c84050700303540e182c180311700d00601003102105d9030740340440c1c0b00c0030764400005848246400001d0211050040e201c51030031040005035500c11080c0b5000e03c40400c14500d0a90303104101ea41c04104504011822010000200b0300d142a542d02106050090143c084201984800780340216030084481d000714949454040850388941800c2d02e18950000c040d05159180c460b004d042c0c80c60190904c0003003041c00d8845078002c101c0d00c02041303041050000300c0048078035050149032003440c0c030b01104a003803403070410010b001841034020186c41000d040304020304100c141004070b241c000307000e05014908a00800c0104407a00203850 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 528348660 1250 528347410 528347431
    0x4050604061d01020619020c0106050402071505130b0c09010c0c090609060b04080a02010f0e09011508100303021b0a0308121b07080a0f021005090c040f0506090c0c1f05 74
    0xd4031900751310003c0d0290281e007405600b01498000450b01800079031080302606025521107400260903590342c070190a41b40d020301c0ca0540003402d00c170300c05401c48500400d00e61900b504c220b41c450200b00c54003d10703940030340405803203986c644078400180c07682020340c4c0e0000d244481c1d00b200401d40d0700c101e4001c481210a00e02080c00007c0c0c607801c1c100705034040d90192190030b500540703071080558845c585520524a050401e103402080c40c40100300742000076002002416039901146035041c1c5c0c40401036a00c107918091000d0038ad070455500940352480b160111604d04034461000c440d640d61021768000442c0d2040e140e5550b0790071b150310000e01600488154051240d501d41441d00d1809d4401140c3c2c0550b800120701d032400c054203000703458145c1d07001511411445020003d015070541c1c0d1081074024074000c8014413010008a00300826140070844114586082205000c1d480c1c86001100b50070040124006803a00750345001740d0301c2c1010345525049102c109211010014406a00503406514217a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 528349910 1250 528348660 528348707
    0x3160f0f0219151d0103090804030c0e0f0c07020f091f090b010e1c02010507060212090f060a151206020c070e06010f030c08040f0c08070305060609060a0b040b0f0405060406 76
    0xc00079a40c0301d038620150f510084d1904a429403542c400d512040c42144191755240c2480d44a46600c4030002280d000320b81d80600707403018404034402d011b52450744490f010401500e092030070b50100d45182c20703d900f540e0142460102042110440380d401910084003207039800c00c1160ba90051171302610203c5600790203c1c0428403030541c00d0624094161300020700099400c0c07001c506034011521540b00c900280d48059080c0100600c2404c031481d0302703001c0c182036401448019000700d811400c1c03035000b80640641914180e81c1da10700303815890070241105d0203580b4030003190700c1c81c1c140300c0081d100d200c00c1c80d589802100004180e40a040e000c082c05141e00703903070b515001d500007032041d0111100e00c0304400c0401c010000250006901c441040c040c0c501c03840407010b80b56a252400391400d11540c0003190980c006a0800c001410b000c0401036214070110740e0580003a18000b00020284224016010402c40008604c0b8407145900201d07030007030102802d010b5445640e26002800d00d508101e4a018058131030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 528351160 1250 528349910 528349949
    0xe0f010207031e09050a03080d11180414060a0e040503070203070e07020c0301061d15060309011a09060d140c030703151a060313030e0303040608041403160f0f0219 72
    0x1005004d05480c070107440640a142580c4800101c0d401450705802542d485501008038a00c40300b002c0e240782c0129016800d840078001e402c11041c0e0b8010701c905165481500b003001581e80d40c01910008481d5442c140c128a500c031414002d04501c920700c8081d406101c0c0103000142c0d40100d4040503c181d10544c01d5480000640041500703a4a142c031442c1c8403100150100c41320f1070740f1076a0369034118401c2d00b0008901060704000c24207a070400c458210869549565480a8002001880c201d40c8012540c2c0d040c00e2a040740083c0300382c803c4040c05001d903d00381a0140350f070300302000796124051009003101d03142c0f9aa840c10b81d2200307103c641055030480c10201d10070070b20400c50107003502201008007000e00b180d641c604200d100e038144000076410001407610090315500c0c10702c02400900120f54402d84646042d05012041018140688010b648204181c0e12038501c00415040e800380d1040782c20316100c040d818101c0c070f503800d0303135601035030203006001e513018151210050142162600c0c5e18441469090 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 528352410 1250 528351160 528351167
    0x30906130b06090711010606030609321801051501122003091e070f0f0303050706090204023114030a06051008030309070302011403190e0f010207031e 66
    0xd10030042040214902060340c0d440e11085266010510340f9001c20750310ba40424030750030340704160300500200303035603032402e1005040b42c0c00381c03200c102c41420b504004803e11380c2c030100f528104102c9802d507042103500480c1c48001c51800b0b040006424000070721a50410f041c002041c42250780f541408503101c01082d001c00c0c4003e0042840c03514504080119110005035205543c1e80b0080c030040f0700d801900d00c40140d0240b1002c044240e02040c500428080341041500c501c0b400b907030741040c6400c1d920303820104002580074003160030355980000003059008076840458040d0180c00c20a8001e040c00301034240013583c103010341c8000c9031100d4842000c42a0395000c0414801c00c0f468105401d0303000721520f080030811a800094011800040700c00c4072650310700100381560025030301860f00b60040c840c100155039101209450806402d004540345003002182081c4007254040c0174422203860314a400b088200c140701801c9484440e2000b90350311050b81c034009040702c1c07020060751404aa070a00041100340b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 528353660 1250 528352410 528352441
    0x2712030b010c1a150a08011d0703330603050d090b040f030b092b080109050f01120507051c021302070b06090a090503120a0e0d020d180306020f030906 66
    0x4214240725040d80d4650484400d810000f0921249500b00d07805030300c89500c0d068100e17001000c40000026804034040050580030398079290088482e400245c007480811402d04013044080b841400d02c544584e40d03202240318a0303403079607100c1400c2031815500109220b008111040050704941d00c4590241e12503403c450a4081c0e0b01a18102d070204000900c001080300c074009070440d810300101e03050060002000f42e2640e0910301c403000310200c5a24a5040305400014003409024446d205100c075140400c0b0310307a03c035201441aa00b0030000c17200c002c01030040500a450103818040c25194501480030300c5c5100282d0319281c00c9002c2c0c80e80b038003060308002d59072080e10718540e4000b0f104080c540b00c0d40100328031004043c1c541107105946850200004d02c080004000095107488505001e107041a094411141c001c0c0c1c0c40503c03504012940c0c00050f42c080355400020340c860038010658601074640c80d141201c0c4e5040145910710000c0c000d440d0b17800c4040918410428801100c10035941d682852a40302d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 528354910 1250 528353660 528353663
    0x6131e06060e091f090c1806080d050c1504240b0310090f0204151211040c02010b0a0603361b03150b040b0d0c03050c060a122712030b010c 61
    0x1c3d02c03012414011071072034010400c414016521881803035207c040d0035900145c02021050703d9962000300308074030101446040c1d404080e0f400e00609200c410703180240c881c65103074107030310030f10410b400020200480507080d5080c010b4120008004101f10251400041020503c84c3d840b9204125040c1da500c1107034002d40040c030380d0001c60b41090701c400d68248030213484001082240800b284101040d000172200d2141034040c0201941d01d00c0100d01c80c03d1004861301c07a02034a01b1a41009001155519403c0900048814a14000030103800c8500c18000c010380c104803038001e01e42c2c00d00e00307115501c1c40203007945d000a0245455a55003660056100d003031a00b14400100400c00c4c400c03140800c1d400301e501c421140040900085040e0403210005143c4003200310044a000820500074002c0c0002000000d01c903000c20750710203150811600780540b40040740021920081c0d1038011246115070350340041d400040e8070741e84410010640386803618121788400c00c0040020b14101e002c08030307584281da040b50891f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 528356160 1250 528354910 528354943
    0x90302120307030b06030a24031e08160c080f1f24180b220b030f030c1005060a05010c080a020a0803090706091202010206131e06060e09 60
    0x14030500ca02510603040203100806040d0354244d44066a280c00d002075100d071452200000701300b49500c28000ca00103800242c0400d90541c10300c184001001c5044400402e10311010081c0c04101c14075081d903643c411000d40943c86080300480e20101705145403540d00341ea550714183e650314203040065540c1c9003034040d00e607103010000d40650007184203181d12020301c84c00031650346c100d2a0b02c519915030f02040f880e80890b42e001d00110802c0000c5801e4800c62241d0340301200d43c2407002b481c1e0310310514500f95802e15000380541e02c00c03e50159660411014130f082c0240001e42c1d0b150a2011019911000b200c5284400316085c0000142146006802c100a49905031a00b10b1185085e03102c009080c0c1248590a080d80304940114010900000103141b1800d8104011310b020303406c0640003004030030554040460901d4590f4200c00503a00898420707070003c11205a46030a81c03150824100c2c03c0c1202c0d4080b0400700c42c800442c401c0c0002c503003100c001e0318100c08a0741e4813034450f204c00640d1400229281d810302c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 528357410 1250 528356160 528356173
    0x90a030903031b0602042601050106020d111903020a1e03050a12140405070f0b1314010504031a04020913051515040609050103110d050a0b04020607050a03080613090302 74
    0x1d000d03c3c0110202404103c1c072800b2640d556407070341c0803a4010303004a5070300002c55002d4420382d01001408103d0080750802484070354980400659210107080c04103003440071040c030b824000391007040390a101242892143d002c00c40707241406034545504a2007681d08249401a201030182c3c49000c2001c200d516a4038980380c011141012106014609000d20300306840300d09200203051002d40650040380500701504c0b5a5180101114100c0e40592048031003400c1401684041c40701d07100780a04440e410400c401e40300c208400100c50511a41c1c200819052140948405814803480035a204030f10950f51860301d40c5a03403844941c01510707240010050b5000d10510ba03841c581d500c11140e000030300043c440c204401c149001500395201ca0f04642c0b42e8a0782c6000400a00c000c100c0300c481c409030240d42c0d082c00580e00c0e40311035485102540002d0316400c22132010404640313402c0e04440b0b6441d000004e403001d0003690303e0014003d580a94a0030b125440401041285140d60312910b80c146a0540040a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 528358660 1250 528357410 528357413
    0x110a050601061b06050708060103061d13030228020a0501030e0a0318081e0706030203091e0c04050a020a030f020903030406030506030312071e0215010303120b040c020f06090a030903 80
    0x20500349044108900c0c16203040f4080005415001c0c41e0f005120b00c0c1c451007003d00d0408001801c503404da034049195466174a07184112503a11040907a00300e0f40640e109400040309050a03854034010301116141850b50141008440400260800341d05101f10340d80020b580d81c86004400b0382e010041042d007950800110b07000002d02800111482d1407081c0c82c04001d440c6d60740b00540c1000c0c4e00c034040e80d132043e070308044100f840311f0140000d2002e0f14890504500310f04000054550301d603100e6141e50071140c003410308107803040803c006103003d8040050003403101d03181051500e000380d00704002400109040060410710020507009407921840054010341c1030030315210048000c0c10f0044d24960309800104001c0c1c52002d9000c5049202e0faa0a03102c81c00c503105480f002400c0d02000700b420702c0440d00301c11410b500302156480300504407600b41c80d01443c044081250440106503105105601c035140000ba100310503000b02e1410001030405060710f0440d550f08405d0b988500d40213000500146201e00d0510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 528359910 1250 528358660 528358667
    0x10501080c0c010605040e010c23070206030405010e06040f02040b100e22020a0203071a0606121909151808090d03020f10140106170a020c0f1c110a05060106 69
    0x6469410342d07001140c03030b980c1d9201103001c940101d0502200b59460b03119214902760462498040105a070b8a060640f510305250a0490301039600028821400007001c141403003070035013103000440c010406940081c2458504101c0010508000300c1c0942e0a01d10307a40340c0c4d032030070540481080202d40c980311820140c0c4420003108604031010306018046e65500014601c590744042c044241e0950005c1d541d64003103043c00649a152500300c85524144203040042d1522001c0503145008155140380744283c86260102c401c1c0504e5524840046180806200c103010141c2007403c130201e020314040254049200321032224055100d0041d01da404100203142440c188040c001080d03d00903c1602c0440803448605030500612081940100792140c1040c28001201d100075401854141818071103000b013203603441c3c81c0c3c0d00024020b0340c045502190007441d403035050044d000600c022000352a1f0031221601c08031a82824040d070140012001e4075505003081002425a4050381c00400030081030b07203010f1084 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 528361160 1250 528359910 528359917
    0x20604020f030a0b2406070f030c061107050a11010c1e020a0f0803040815090613150e03030a0b030102070308010e13080c061509100302120a0c06080108011103010501080c 75
    0x260548901c3c003041012549030300750540113403100601c6003801c503007400c0c03810804000c0001c1948202010002d160000e038880700c1050802e5410704104000c42c0c9141008030003855003860b1102007040021f0418100000404d48052040c403452046c0da10903c8800112111201808004c1c1601e404000c0581221303207010480040e40e20042c40080c409481c0c82c0c1d40c1c4001c4240354010035084e480814280010b000500c02120340d005012a2560945044d0301d600782d45407006070121591840c0315145005001d640611a4018030308a0030a000c04c110340865980c0e6a4401c5418041c8a0314001d04400140f4046c000c03030710101e40580e2000c145034209a24446564000b4160060901080541e5000a00220f0103450402084000707040145080c03003680420503800143c103403140001101300324241e030110a04506494040d1070f0300d0603e01154940a1810b00f04c1b150141010316071450020f0995031020302c541c141c1da07a8030028031890180e80c84916041c0030a01817030b030100704090b0010f51303c8000b85028 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 528362410 1250 528361160 528361189
    0x15080118060207171b280605100e09070f12170c160b090301050703060e0c0a210905070603050c031602010f14010617040510020319112802060402 64
    0x5904080c42c56400c02c8442da4400d1180c00c0e02d03009004c200780c0b143e6809120401015a0350000c0e5010310707000e801c3d50090380701b140c3c0c1c00038a02c030340e2100811594030250f002040940218844503980d810300b5403100c1d80d00c0015108552031a81209008624801c050f0075a440066000034140300c60a420b80540e001c0d9040030f40d091400d1701c240750007151000302108803003008125105005580308451b50505096980040a55040c1814114104603400c0780903002580141c0c072100c241d0319800056000c83e42004001e60300d01100481340742e0b1100020f100d80c41a100701e8400c3d01140c0425640e50001e07800e481e42103e0807910200706100080c000d0344040c039512600a1036100004041180400003421200c4000081c01401d2402c0b0040c0403864020380100c0500c05503002884552504c3e40c1c0e44ca503510042340f8601c2240c3d4011010501040c0c80741d1021011444000c42804068845c1040b540260030150704240c07401d210320006007940e800030042101140e0180c2c0034060b10b44d1648c00303210030707a81d00b03811 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 528363660 1250 528362410 528362423
    0x20c030a0b1803040b03250207061b061401060f1106011203090806040302060a0c0201020c0a1709030a050619060503060f040503210402030c0f21190615080118060207 73
    0x740b10700b00003400100080c0c40ea504a90742c403810407801d040c0c2c803110004006400704903400c459030695034000881000704c40c00c515061030700040914441245111494005240a04020b10518102c007208211816101190b0707880a20520824044881c9100d19500d195540c01000050100300b071649180701c5042c0c080d050000c00281d5030321503186418022182900160071900903c1000a01405840d0601c8000d00c02076050002c081069600c415810302c00600905100c1c01020f524071540082d00e94100d001003d4618052150411945900e002c56440c501fa4800e0001c00c1c54400310391007090b003682d4020740144800d6840000c640d000807005042501d1078130080c0007406070340310690892840b0f6261403e1109581c01d151042c54035042401003414891003a840301c0074082c0e04d5820103850309508148111210301038003407000341000300071040c1c580c500d08803140640c02e014840d040020790660344004040c80c00d50310246113003200c1c000014a032803031414002d600301040700703500a406054044e00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 528364910 1250 528363660 528363691
    0x1090b0a0302041a0d0b0303030115030f0906180b0f0c0906180a0909020a08010905030306150408100923120918041a1b0a1419050c070501020c030a0b 66
    0x1449001306141d6041c480c16608000150009a48000c1c054990001c0040c0e000314219418a40103030030a0680b40941c00c100b603902c1c10255400c59482d000609180c0d007000f410080c50511003140b0006114101058030b1880001d004611840f02040c0060b02c96610f00340300301d080c5850101044030030b9110207a42a140004109280d10641d5141d5980c402002c9044000074072800130320500000d41d51070303404190640d02d429042400301e1000300480e42d104030704a450300d000c01140303030100350f040c0160f802c4202284140031030350005104a62101c002280141e00b84001031b40310344e044441034001c07613140c0392454112080c552a0075030100090000008024501800e00007480041c0490410031a01131b507510009056141c5005050b0400ca0340000c8000402c040b45121031450212a102e402144d00801842e0b404003201840782005450440040400744051000000801881c503005100403030740d030303029055002030300f036000003100b00e4650005005010380303500f04c0e01c0d4291031200c01020003240c1301854 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 528366160 1250 528364910 528364919
    0x607020105070305131e1202130b01120609051009020918070c15020a0e0319120c060203090106060f0203090d111207270c020606090a32070e01090b0a030204 69
    0x21400c005c060511000143e081c0d04c82d0f144080700c01c0040340d00c541c40d5442c101341501d000d81c1312401400030b43c8101800c0450b6032100c080040740c04130100f0301c3c00920b852074040040380700e41c5d00b900058042e0002108010b0455159810381d800c0b845106c0b6030a9008901d2103c40300c164a4140760507500864909100040070072139180c2c01b50601c180c682805d20031703500250345030806401551000304100181c000307001c10104600b030341d04208202c040180034800e01e60309030103030a84201d81d28110180c1c41001952a41060f09600303020704518000c1e40c01081d0030050003500c881c030010030f1f03c2c2207440017041c0c4141c40020341c440c00900c034114070f079503a006104003c0d0f980d14140704020700c20040c80c980812918410080e50071b41c2500114602104286042c8841d44004a500150194200c042100e04a01070388403145110000c000b0010f0344030909403009100861102140030106400f48400540b01890b92407032411220a042842d0702707800316a568000b440090317410409000c0b003080c0790030b006140c80d459 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 528367410 1250 528366160 528366187
    0x2030d0e1c020312070e06070f021522090507020304090902030f070303051e0301030b0c3a05010816150905030106030c05120a120302180a0303050a020d05090607020105070305 77
    0x1c00d1080d4025900004009030020215407a00350b0000d010700e00407000d80743c540000342d090320a05a01401c16000750f40140d0035561140c036005022450195902d603249148032040036411042c0352a402020b20075040003d089101d40505846494180e000d10b11f03080c10b1017a844000c080411042e030b0540f1031001c0f1900711a100b08411000b0318065100c40d81c4402241c07024180c02e180d18a044851b640007800104005071210340300c2600011b03642c0946407951480d580301d80054500710703030824411610840e0f409841d0200b103004806a596918180100d0382c842c003505582d0a148401542c032040600400c000d2a01748130401501d00400385007040485a550000a0075540690800d44446003448410080c52038003400100c0c9103800c6c48043d0445500d65282d0b60440c100144105040c907400043c05034502c0311242c03420030340c08001844040850340728240100507810070002c3c41c0162042102c181f5880d4010710544500600040005140240640c01120141c03c108421000c1c484140520500340c0322 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 528368660 1250 528367410 528367453
    0x90616091a0405030601061b0602091906050306030111040e070509030307050d05091206070e04180c0e0727030f0c090f0e060705040e060d110d05010504020411090102030d0e 76
    0x80c1d0055160b21503050004050070801c069010405011411619102ea12490401100c0b180d801440058507511160b000c22510340c59501407001140c00074802141650b08000994011002900208800c0c0748640c0b410b4000e1255000d11140d40a4400c0098074061150000300030700b03003018040d6410440250784003840c0200d0401c860001c00e40104000100f810b0969406202002e810018902c905010002801c1e6040510b981c0c2c4c065601c1d41d080d51007420450301800141544050408110f50f914004000e00134000c0e41c130000010442e18844201c078407100807140c440a0b150152101c040d103903035280c3d00d0404034940200c513041856440014281c032544503007101091940008503400d0342c418030080c140140105100103002d010304c41403000301703401104158444015643c02140081601300000c1e50000701c02d86582c84164485900c003000301c1900020700503482601c00b4809070200c990700180c6030042c41e507014010b900c1404000c1c000c000c1d540100440074103c0b07003981c0c1e050806c40b80e0b0f00c0c0d0501 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 528369910 1250 528368660 528368699
    0xa15030b0105010f030218090c1b060a060509040b070e010e04050702160902030c070311070302032d06010302060a1b0c09230105030d1211070b07030b0102010509061609 74
    0x6040030010022075801c060002c14030382c1e49140031860908181c40302c4e20001411400280900d0103400005c5400c104441124100d42034010038004007404ad01c2c0c0a03544240480e040102181054000a1281080502540581d03449401542d007aa14504200e4640c240c01400c6410030550a12512068070355108c0c06028821a41c00b03000340040241e4605c0c0780000d030703a0244c40341c10320400c01c20560b81100410744852591520304441c1c5414581501450032480d0b802c00395250181642c08003160070550401c1c0e4428002c400500c048240245d1070303c2e202c00c024840a07402c9039040004400c014421034005000300f041c0c000d03904807141e19072540d8400d81e0750307a0803020f41c580e0313500c203414556203405001401d100b8a62031125260b605020100b51219181000d02e000d20000c034815211121098000000440950000036100c210b0b90502c1504e02c007003503800001017850210701d40f005503c1070143e18401c0d40000c00501c119203809000012200d042007101c000c0003801d480c0407e469031503058019004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 528371160 1250 528369910 528369923
    0x141204081c020c0108190c1d10021e010906020408010501080706020a020a060c0213050a0203060f09010b0a031e050c04050406122004290f0904030c080901030209030a0c080d050403020a05090a1503 86
    0x1170401c41c0d003d40410382048c010511076952640031113120b9a0000f6021245104070328680c000403201140301e40544804134000b0712aa002007408210040154031190480b8103410488005c40e68890090b038441c014030f14080e41044c0c5a00081c000503019100d06100e891028050500d4103401801c01011100241d990045054000050003c20301d801208210034103801c9510134a9545090b0b4140c50f03920400c0001d44c2855103030403071101d0100d44500120005c80d00d0000030302c05850041a00d0215520601400e44158030745900440e02d807040c2c00d003140001e6401990400041c5109405102c404200000c407580b25895551000a4550011042060344a0300c06c11041d800c1c50744c02040742940855500764021401d000411012aa00c0b04030000709030380145400381e4840701c107801200640300e0301c1c24454152017491074540404c41400001001c860999081d12b80174511500200c5042c452072202035402003510105000c01d140a203405a00a88012400504000c4110009079500c4a650094565 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 528372410 1250 528371160 528371177
    0x2a070c0303140c061602190f06150501020c0f0f1804140a0b1504110a0f020f0d0906141b1605090c16141204081c020c0108190c 56
    0x8242e0001141c1107024220310390542460720300b4040c1c60b902d081c000e000c6580003014100500469000b40403006001c2e040d55002144442c45003400700540f04018030031540e5078682520407460400b8120040f043d19016400b074112039048008001400e8034464002d1350003142000c40c0040369032a829000d064840849800d00c02d442c280c2440f0907a40c400013090b261b190404404c07200001c11011420758810b60410480d440d0407600000701c0c006190b5281d64070610000000c00611894101040300d40714a01a0700711136000d102000d005407200c060303244800100b80c00c2c00c401c0c040c040c000d0340428096208110030314107042206e68520204000c815010300b040c4c014800743c00424000c0c5020201800054480c0e942034100300c50705508504c1260391680c8014802c102070b408000500d4000c5907040900811034058600700413259015501512400e98248034407449072040c20550943c41ca5548090703005003540b011a9401514444030051012031030820780500d014908031940300c0c9011540c06580c40021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 528373660 1250 528372410 528372413
    0xe0a090203010e281b060c11010c151a0a12030f0906050304061a1f11070e0703051b160b150901050f030307021201140105182a070c03 59
    0xf110204442d81015070403441d510800301070b61000b0404140069440700c025186503080011305994801e0001e085405090000100e01c2da000f02d0500d043d40c000e10080403002640001074400c0196900002e040007540441140b1041c0194040c11000e2a180c0071940048031150008504200076007100c6882182468041d06260348030030700c0003d120013420410101030502c00081c2060000410003030182d52204d02c0411140300c2058922030748040540b2541e01060700c5e414001d03c03000c82600000014103400b085040742c160001d203050494145080c0a041d6848a00e012000b402000380300c401c0b254801c180160104040f24010b201500c4105c0303010180344442c1c540444000d04c0600901003800005c04040c05c980e40d0100180e0450310f04803140c00c00424290082401c3d402030007006944202c4080e0500756012043d04520702c19100d2414036984c45c4c0e01ca004002c075403148460102e1702030a248000500384480c00b16041c0340b2008032440f9552a51885403031842c154010b680c1120a010311140410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 528374910 1250 528373660 528373663
    0x909050609010c180b0d06030602070b010503060a140a0b03071706100f050f010e010e150c060f040f060504030912060b0907030605060702130f0518060c250c0e0a090203 74
    0x4050f01c1d03850040d004504d015450600280c0d039014416246400003002c030740c1c0002d150700a40003154072110a6490390f005090415891609118060103070140c0400503417145e1092040950607039640301080410f4841100c00c078001c1884603c0b50303801d8418600701245c00100034101e098001120402800350785020118150301c0102a880b01700e251901c92014421744c1d45040004209001c2843e10f480204081001290f4440000c0c000d036400807001d00403005c451000c00d0013000700e004420120750241d112b241c0505d101c13860440c0e01405c032031903c1c59020002106904220b802901a10300401080d03104c50304a280b11231045000c480e403070b070b50300900407490420010440d406101810100901407502c80401c6c0c042c45081c0e0000d01c2450708254040d01d01200c0d5100c0c0d138502c0400310080003a4640401091010300000404031001d106850015140d54524070803103402c00d100000b49400b403c118210a00c9407481814121100e164015010602c82d80c034405c2240308550030007001c1001c080b28018107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 528376160 1250 528374910 528374921
    0x4080a12030506150a09050a0f080c0306060d080d0b1c03021903050a050c1204090b1503010f0504050a09020d050706120603120f0903050d0c060506040203040b1f090905060901 77
    0x6500749420300003008440d5803684091040401100d1000741d684200c480100c4045600346c0100c0e5010003003a4010605502915144007569105000c0ba600c0f00b484004141d5184004c45072180e000744850004000162150043d00d201c4404400104910346001d000a0001400020700b0b04510075600c044002d043d810081c0705100c44100c1005180c01c503080d2002000c81c8640da8000b014461700055120b03006008202c0c1da030016811303110301a1500d03251000c0401411110030528030498580c1070701e601c50310b8884c044a0480d0b00745014188485e140106000c05403400801000b000b80d55603680303001584070044107440072031007030014022281c01c1840c09440040305085a085151800b00c050000610440d420b04542841d82803840500a840108440a0b080c0b908014500d0160223040302081f9007015a40d0314051245074203000958078402400304034003048401401a41480002c200c202c120450f40003210040c0e84044080c00d5150b640700002d8a41c12001201c555011000b0455654820300c600e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 528377410 1250 528376160 528376193
    0x60213060806090f06120609010e0706020d050a031802040e06060a0605070803040615050a08300d09060f0c090801052508090106180207121817030d0204080a 69
    0x240a04282c004907003100c400901007a00010088046a080c2c1d80301c1d901240b40c0302505089444910300130a9240c0a06503501c20342c103507885401e00c007141c8940040382120414030fa5994a03070a210140354210003610703101a02c1e814036031101c01440c016071500c0c0501d004408180d4000c2034541000d00a000c072000282d170024013000402d0200700000b40c000c0d412a604150000703800702e4000a500d42ca031100440700c4c0e1100d41e2050104200045030940403821405030f0480c000c984031046a1080320380e988000080e0749501003130003002a1003052000c2e40c00000c172640941000214244040c10210890795003050801c082201c48008000d004400d00405602114121040110440118004204040306003140081c0241240001c1004e0002d520000042c060708140c0d000b1110203410310380083d405031805440f40c100c004c6505801e180140c910040640d0b00c0150907c03c2443d06036000c032100c515500d040240d010030015884100502e0020f800038003a034101921414101c0c5c42d00c1e60010420159 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 528378660 1250 528377410 528377417
    0x1e03120406140c07080105100911030408040b22081605061801051b030403060c020d0825090e010305010213140a05040911040c0f02071d01030201051e040306021306 72
    0x1840041d52250381d024410490410340d03500c48400c2c0550303070b003011344680007007206629007010419044030103800b4500301c0701089010000c410110300240e51030f110444020302108010002005154500c00c01440c45040204011021000201c4600740c0b0000ca0707404000c090f80501c2c01d500040d8001c4c01004010801169031505c0c02001d03540b00b20042c01c040709e045060050214207100d00d11200c030140c0c0000c60700c103010340c1d0350741c0e4403460280000d101c2207048030010705c128008003414500410140b40104e0440c800c0c400e40000c3d5041460361170624030340010030004048000034501e00ae0240c0c96000e07610950000d43c98042e080c01c00c3da0803842e25407100c40c1c1c803a04185c00160301d07200d115007881650416500801c441800d424000c8403203000350a0721fa0040c0c6030040c52040a903202c40421000722003542941d20b07441c0d07a00c442140c1d0b14a0124420f000003600401040190b00820041c8922003219503d1030000024084540710340d0801d90083c1c80103072b0005400700d0052540c07074002c0054000c03800c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 528379910 1250 528378660 528378667
    0x6020d05160b0705070b040c0617100e0709030b1005030c15030c07020409081306030f02042105250603060e0702060f061302071b09050402011209060b1e0312 69
    0xd100706060342802001601050048011504062041d070481ea005c9800c08014540c505080c601034204588510481c0c0025041c0036840c41ba601004c0061800390a000e03413007010030350170611800c405890140ca403009104504400000040d00c0720b0600f44a03804a035540d8070043c2c030b0402410300f841e100c6504584100703280c6140d821061148ac0540c0d80010b23000c0b8500391501c905201080080104038005001c000000c03c0000303070b400780790507440c0a8131041e83e014440b200799006540181c0c021801000c00d91030140e0710920b40300c0001c2200c5100e1500410032076094103800f410768805020705010105410300b088030148440c9406000e22001482c5100150250317192051001b526038101414000c0c10646c518082040b0b83d40e0003040e400c62015100086540722090701c2d241c16504102200e00d2000218090009030800003803090502c00d03901070311641c002c0708480944000400c2880d508980041d42e174103500b00c03941ca4082106907030300441c03940035079150108400c1600e8000703001c40c40c00d111403041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 528381160 1250 528379910 528379927
    0x5160e0105060a08090a0804080105040309060e0f130b0d03080912030c04090c0c0c08030912070e04030f02010906090f0605100602071712120103172a0a1b06020d05 72
    0xb48111075465843c4d14102142d61694040c0500340400340c58094100500400c1c081a031100642c00b86000c3c510a446000c031b155521501074503100c2d401407102d0f501c8902c00c00c103803100c0e09142c05400f04240120000040034004180010800f81507007400b50300194240c420006c2c07241040189603080031000809038194900b46806902901c036078010603542d00d45806060780f5250184204400041d804100c041e43d00351200500e95076508035011240c4141409104144101008a11142950130121002d100b5650300c0d02e05855403100590038100319941c0d89101e04c0400d1043c0724801c040380c400d00d29001020758034240107061322400350407a032a5902d0200304000307072500010207600306e03164841000e00402c10151502e0034084010400c040405000450402c02604171681c0ca040c0d91240200850f480410180d44045d03001e10800548403051041014001d0500d625044024600380400c81d40f840b4002e0b60f9403a1000f903000b011020305a03800e002800364640600201425052928005080c14281c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 528382410 1250 528381160 528381169
    0x1020304080a0c11040c0e01030c03150506090a0810060e0a0209010c170706020d0203010519060819181101090830040503120403150204120b10090905160e0105 70
    0x90311082c100303201e460000b01c0100504060150384201c03008004020704c00f8060009094100c1c8000041c0c0001e181000c00e80440d40a44260352914050352600359a5500f8030b01409020f03800440550341c80002e5680000709071204000c1d10704c50034003004000c9005450300007143c4d10f003940a00201c40150060000f452142d80c4400062103141d00002e044245501d228507030311f000e22480001030034260002071075003422403c03500114100d8074181c9004444480c14000c68048015034000c0c400040e58100c040343c1c204d404405910742d010380071400010042154081800c8054a4440450702a030903501008038940e00481114010819403001d8068180840714042c0011f401640c000f11030b00d4040e181c0d114803032440c400d88002c0c00c03002d02241c6980007440e800b0380c000c0d0040c1c40102d545803588a990165006940252401c0790b46030f17002c00526145d10b07650704101c440700030103a0b52442c040f440700095501603801003102d894001c202600c80081c1c030007200c5c00d09030321341e41110005a0960004001d15202e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 528383660 1250 528382410 528382417
    0x1020408060f13110f04140612070f120501060e130c0b0c030406030e010219080406110a0801030809030f010f022a121305060a0801090b0d05120901140309010507020f0102030408 78
    0x4e00005419040c2640c2c40001c2d151005110040d80107454460421481826164242d0081c14119100312a48440003001542c45006019048260705101810401000340d0329810100394450b50010a0041d241c81c442019250100e6105e01203141c550901010b01c04152020b02c0030305088200341c0e141c2030800d06001c2e603d1240344100c60070141c3d80d91004445140079819106048071050318004d003061140d4005000100a41c2d007a103201e45800c481c079110715014002c6039850711550315103184d42da00e141c0f0b07800c07843c5c0c01440340346030980165220709800c007100780b2800c006951044001a1103209112481c0b020100f01c2c02200308152003802006100754000076603417801250319683d155200150210021041085c3c1d200507000701c000314034842c950342c03c0280c6c01d042e01c10280041105d07020413030410140110030385c8083c0582c0c22440007030034610008001402d07020018146244a0003080130020000da001b00c0f010350321030b507403201846001c681c1480074250b2600028029821410316449240c03030b622 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 528384910 1250 528383660 528383663
    0xe10140d06090c1416230c10050408060c03040f120f02070f120219030807051b1e01050c07050a12020906010503070e0907091206060302040c140d0f020c030c01020408060f13 76
    0x641c8106000b0032968080410800d01c2c01340300c6e801c901103d0f100c05030395041c104e61b03100d110380e000150401c1001e21030410742d0102c1d490741008164640b6500560f00036540007074401d0780c81ca030100d100c003400300740c0207101c078858905150b843c906025188130009062078203a80050924900c617403020030a01c400104035524880d0100c550306007030b01c003203000d031440a08141c0c0700801070340002c00c40b64141310b0003290801e43c0058240d03100400d544801c0412803c10410b080110609400680d140019441040a8441608150102c40c0869200d01c00102c450b41c0380c2c0e001003803080d60a8600f03002c5060401e4080e4201f1000e08005003507080600000c1d005410001e40070b40105038000005407000c0c0300d08050300c010840f4845200da0a07038541006000380106020a80c0101e00340340d42546100d128104140c80e0440c0600d28904042801d59104003925419024011064081c8403080d1094001d20091400303a119500050b40d40c0d1408103003500704507000f0a41c2021300319400c100441c032180d04d80304a2426 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 528386160 1250 528384910 528384937
    0xa0612080a0c0305160b09331806090106050a15080403080a02130b0301090e03190e01090f06030b03010e0714010507020307052d0d020f0f0301060e0a0b12010c0e10140d06090c14 78
    0x127130340711303100300b40954440a10f0081034425070080c407411007019400313001038480a0300c0c50b850090310b03500c1e4149601c40e40004680001c1d0801c2c00203000c24414501950031504981001d440c00c2081400001da080d05900405540f14002004002c0c105d4240f244900480f4854084c6040401c84011170445c82030700d00900090210b1040c02d000141c0c429800f52003e4182c00c042100a01d88400300100100340d00d0b0086402980b0381020700c0c1070a02c001400038100c8018240d0500c0c140c1401004450740e401c401012a050f128030000071455030384c0c800325000c20355032042504409041c480301242e400e03191948035600031848a401000940c0300c001c0d0a44408000f92456000c030405003001ca8010070940c3d111220702035812040c418901d00981040c40412400c80f2080b240715200300a60b82200c1e40403540c60082001c03107900d44110300306100c54401d50400c44c00c001d0148403510328980d051f90b0094540e20100b0340e90308002d01000c005485445510a5949032400760319114900740ae05910440040100340b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 528387410 1250 528386160 528386263
    0xe0601050a170f0102030a05072003090f060d0c020c03071d01030b0c1605030a020d02010501120605040302030c0d030b01140712110c0604030b0a0612080a0c0305160b09 74
    0x110401000c8003c0394090000c40d92450b0202d11072004003004e0300c0550001d122140350262164881c0c224000b0b03401210301840c6072814100c104209903007410308103038103d1003c0c030030107420507010300c00c00c00403142c5030700a0200d4588501c205802c014072600115043c2c20003020404480340240d10841c1940d42c000044031703040e00e5090003000c942c000c1e001001c0d82a848800e007007041260220140007014529001c030761080410840c1030f42a0f031001d0041a464882440015001c5680740d0003043d0014003c1c0192450071400305104c604000042c1d0003140841d03207407000c1c2501541e11000030341c0921004861a41401d40d02e40d140d80080e244800210100f114071404038941500510035000d504074024086650340c0c0e0b49243c00e0106c0d59040300c00080c900d28009000a1000ca144400700300c4542c0420010300d065420001510311005481c008d504000c01403008420340c0c16501d0b10741201d24001c401d4903e840c6041240795280102c81310030000c8141800c07148a100303104ca09080d0010703009500c0a06075 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 528388660 1250 528387410 528387449
    0x7180c110615040c0f020307060903181e062f07050d031709160b0d02070602042919081312050c010605010c150b0a03081c0e0601050a 59
    0x281920010100d551a0041000744004802401c1c0800e003800800d441c107000c41c030710410090760301400d04900c2c040960410040f0f03000107480340d8003101c02c035403003810001041c0c0d0018100e100c1041c001d0300151480000020007600b0910300359030703290041500749000381c103411410346040c0d404c2005030780302007407034001081c074107501c0030b0600035400903110140c00b00b00c0806050400a0144480c00c4107008107088010100d80049008545624041905d581541c04546040e070a034070b4640c07044111142c180d900740035200014695000030300081141d5442800f40f002d03403401d240407040c01c5980c120403002c420001480608080c58045c550410b06085c40d12203661081c212203036016400784010b01812807010800000c54020020380302d030700c01010007003001d0fa40790001034980407002c200280000640c4458107041d1246038110062404002e40001d101c150340e40d45a0045403c9110b031203103884000e24105074039406510640c080400f910004020551514002c0b40c01c0001364002d441c45164040f0090a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 528389910 1250 528388660 528388667
    0x121020f040e0f030c0a0b010f06090b0307020c1e01030e0a020906060d020c0109030207030c120804140d06060b0a03141014031f060302010e010203120105010f20030301051207180c 79
    0x7840071030303140150ba99030450305d600b140d00c401216000700e4482e00c02100100e03449004000780380a0301c4150710b510820906101c00340b41150001040f070b10441c420050344420a0f100c4c030045840142d071403a8008a07040382c000c009800d03621140900812648480000e00240e036610180c15040b403015503419589840c18000c00010344a098a100c4081d801c02e282d00b0f00300355000500004582c06601c0031101c154890307101e482c4030b800d10070010707011072070034407051164034170315408815060030040c8007035580e680ca50b0f641d500b5102d055001d6a001e030b8012400200e095010b018035405a41c01c8107030700002e8540002c0241c001c14080c0900c45070f07800c0540c4201c0c1603071020092502035042c1e21201500f81c0c0a207101000c06041e09000882c00100019000c8110354000400c1c0c0e03101d80607440301c0d04c070f26138242001180e59044041b0103004000c0d01756282480c0d40c0241c84a414003000e4900615641e43c1040e042c0703e0f035215003190f4205c5990040408001048000021002c4003032090000b0411080c02c03101103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 528391160 1250 528389910 528389923
    0x601080c220c08010f09200c121206211c030b1009060905030c03100b0303160f020103060501031e0e0304050604090218061303110117130210050307021f020409020a080121020f040e 79
    0xc0f450207400049034460152200c00e102d00c10be5084800207002c07190581d0b840d803504110402140b5980c0519550003100e0743c103803618945100c41d0f140c0010b6200d0442e00241290091130820004030300703110310900445a02035104805003600342d00600510300140c0105e6510f6680d0101080d405544010711941a80c081c0200c1e0440c42c840e0b4001034401d000f908044203140c10019080f40405e140880006540d4007d0045056103520000c02c20460640d0461100c050030b20400c08000300d010400c40030031103a541d540504050000c8400040c2c5481c003092022107034411081d4410b201e800184040d031454603d074080c94040e00e40c00140e000e00000f9410040e20185003902d0b113000080c110408001840f2002c0050381c40d0305008440380004410401002e580f5484141e41380c03001a040948120a03004518100c10400210860010b1a147c0d5035151a012078001104501c00a204040100455407030140d00c4604081c1801c02060110180d0b0b00144100080040751401113850344c03081c1e00c010f141841030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 528392410 1250 528391160 528391183
    0x207080d2d0f020601050103180f0203010609020d0e1216170f070b07080f060609060918010303200f0309040923011d0601080c220c08010f09200c 64
    0xc03500c0301d00341d201c000d8a80911880e02500612598000180c01c0d8400c0c01810030302021039140010465103610b1742c80e121804140b090380c066407642400907025446200400301010400c2001800201c600001802d014a40c840e0005405090081103680c540c0300e8a440c10040c0e22400c0d0740c440c0e080c410700c2c0c1c48060298000c0420755410224001d0b0a000071040503a204130910740e5654140e507a0061a00d0041c2e100b0340e111500440280006d54071420b1400007080c22140050080e1000c0c4c44500380c20050035800d03041200062010380d0021950a80d4040c00000001018040c1640c0030b00885129030b070780a0444440d00c15510b85445000748414682860000006104000c80c03506140304801d02030542c1e110804105481040380703448550012070351074180d0724070781c0161401243d0f100400c09581c80c0704451090452101b0104e10b18240d59118117400d201540d1075000070b070741c90704091407000d5605600068165060400e800070f500079003803014900c06120011a83c03215621010645414078007001c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 528393660 1250 528392410 528392477
    0xe070e04030807030e01020327070902070f110303070515043801050a0513050c0912070302040c0c030c12110d0804020319050a0807080d0203150109060207080d 70
    0xd12007031562010740d040c070030f510b142c4080c4482c88584001c0c500300c0c8401ca0300055a450b80c140c46d01801040e082400b401035102d2800c5803525a11180080101c1e80303c0d24007103650480c1c10712403400304010440591200e190480103141002ca039074071600e40303550303850003101d0b401c213100d1000a0801c0f0150501c403c0703001d80503104080251508803000040f0242c0c64444d010700c02c841e0700003c0c0528000c203916041e6680500300c580250800c03440000588006401c000200c1310030f101d000f9503625440700301242c180310140181001451801030200300d40d41a110941001001d0002c00c0105e80c214402c14071a9502c041500207440d4079040840c0c180c08102c804200c43d000f4083c40c2101c655005001c1c1e4080c1d40214252180140540c4404040c0703941000000c0454028035018030100b000038018100c00b43c000c0440c1841c00003c84480c90480c1d0041755603030416210030210121550344180302c2e0380684400e00046c00002e090000c100e035544040080041001048101803595900038541004411031050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 528394910 1250 528393660 528393689
    0x1120e03070f051501170d030203060607021504090b01030b09011502250609090204140d03121107030305060d0c180207021c05122701050913060f14060306040e07 71
    0x40c04503100d134551009000c280c1800c00c000b04094613501c0c0020300346000740000744101880f040080c1d000c0c1d00b000b8480ba900c01340c14071440025880e080d088130315201c3c7c207002c1d85955905003403d8100b110b1190401034105880c2158400c070303907200c0c4900141034030160980c0294540c00048200c0c85e00c041c000c600c2c161070001c4020907080f08160343c01030b42981c6154a400c0c036010f4491031554124061880760701c0c07440b009402040000d0421800219185000f4030304542d03c404c10f40c0c2c0080950710700080121149000140050a05030700d40b1680c1d17000603048a007002c00c80c07060b44412584482d03d01400c6004120781d09030790f18505c0c1c5541100d171203c0e0302400c05d4602840d0041c802c20200c05501040d5103500425002241a03004001252130810f104404d82d40000244850200c601c0001701e00c0b181408801c0000e00c026503030b485009001c40140310300c00304642d4200550406845a03c2c0d001041440030003003d10300740c3d0b8030101547d50111f8150b800060388408503420b0392824603d071b80188048000130 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 528396160 1250 528394910 528394913
    0x40e030c0c0103021c050603070306050f0105101d0405070306080a0825170306010512090601080106060e01140304050a230c12060f0a0608070f170c01120e03070f 71
    0x11028010480100e020398010700e941500540980c400c050310081c03660300300e00b018200e01c2c0580d0305c01c83c2c2218000d81102c802a880e690f504040ba1002c1da115547c4c3c110040c010422840d262480d00c0890f1031f00c1c602404000c503403a001c40301c00303201d021203203220b592501c0004142d1407081d4000002010340da030813603c03038171410308000081d80c2c0070742034840702c405941c4070b411107040089945041003503110010140301c0d00140a02401900007400d01410404200460310705000131015a5000b1202c8001500040d45403011450840d0b810340d12140520007240104106a03030041500101f450520b401c0c41d035a9560f0740360040c00e00008060041000c950b00343c50440f4141c242840341a04008142110304134003520041081c041c60075020718032542d11080005201010800c203058001d20610380c041041515842446d041c50740e55004aa00e030300e00542c00700010160a541000310b509040c014184010162000905280b81130340d01d1200d503074840c0b81780118080200200c0d084550031164044200c00d85 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 528397410 1250 528396160 528396163
    0x43b1c032f0307030b030a0807300509040905030c010203010b041d0112030302070f0b070e0411031003030f091a03010305010e011b0f021504050601031203020307050f0315040e 77
    0x1801124204028951200d00301d00070740c084440d2414054801c1e18219501d8200072000b070007141d456550540100c078451400165502d020b490b060380700743c40040e010340c041010172030741b02002c81d46422812141c0c03e813a50314941000485814007400e58000c58680400e0800c986184254001c0c00c03025840003000042240c40b900c0a00203035018410403020b0b442090b80040132528080c099285114400044000080d010394000c000280c450151580c40f40241d456a214151041b19040013140e1840591000b41c41c0c43c0c400c7d600058000c1074401d00751306090f003034000280410300001702842110440c405085005008000c024480c400d5800081c1c49003514540d1160400e00c000c42d03081d0b090209500400344180245400b030a0884000302906065107800c50b09107480c060001c0550003004600c43c004001c0340d821030300c00c1d03000703100030515945540b4258031030070590380111003090b1062091088a9a1200895013681040001d503500c80d00c03450300c10220313500c4800c0350642c417034070703000a04168010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 528398660 1250 528397410 528397421
    0x150f03010605041a0408102403030503060f0301020c0613020111010e0703030905030309030a1e02030f0102070302060f04080405131d010b01180311120a051902043b1c03 74
    0x106038440c0c0c01441c5241460300145c000e500900b0301c030341c00c81d0401011030f501691007003412000b1402c41d54480c03001102206e00b0307111a60001c0d80040c10000c2004000c1c204512411b403c8042070303008625204260b002e16460b602c4c00b611010355003c02800704c42c03d5a02c00c0004040b640c031080020400c0d007548a035060740d81d6055110880104150040016041c5004416120032140c080d010f0440452107a488030b50b40d8642c290f0072660551555400405a03d040000070410318021000503a91091030601a19140d0000d00c56941c50200030200f2002464190980342194029184804138039603050702100034000d100700490680314000501807050b801508030b507003000700a8032102103800c40b03d4507000d001d00c10340c0006040c005178110300143d582401c40040d1800403003c4207495030300c1c559540b00390030710340f4008409030001e01c3d01c55060198a072030300c621401c0c0311a0304c08080c41058103c183c00401c0e0244002c1c0302c07020300000021040791906000341541c0b81042c2c0c061074140d403020b5001500a2a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 528399910 1250 528398660 528398669
    0x3120e030f0f1009080a0e0301021902010204030c0b19140d140402100810140a0317031005041b0810030c0f0f2306032d0a050a1a150f0301060504 64
    0x114000c050110045107111301d4600a80002c0c080e40340880c40ca4065a03005060100e0719090f650030400e842078860050315804440d1182d5001581c0d072403031820308012440305a0480c1001035410440855180c0441d40000d2181a035810700407102040c02c06d42070b54078002d0072060084c6d2801c0c1403540c06d1801c1d00b00215445644200d844091514400c502119414012545542081892070040c01044100c0900862044006140c0c181280d12a40c4459481000300f00f8614104004800e00104242d0680310030080c04041e5000c10074101c0312492123071710241c0b040c0d200041c0300071080428090071a186c40c10001c0c507000780d020003405581d20403006a2900034400d010710401c0e1040080f40d5181e215141080d0842c600c5c986030520324044042003680da0000d400300c003480341e40b0000c164400200c03d8400401012003034059003649400104101035490041c24608010b140c12028070282040c40000210550b09454040c1443c0d80a0780a20b0720f071017050400c010500010000041c0217a11070300900548 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 528401160 1250 528399910 528399913
    0x204030201020607020d08130501025203050d090b1906050a0b0901050f0c01050903070303060e0f04061a09040c030c0e0106080c0313060c08060a0f03080403120e030f0f 74
    0x184d85102c030403600c480c01a02450002062140030511751504114000b82c240d000d03400052400e4502c1198220010850041c20002022116200340d0704030010325188a01d42030b102c400b205190302e05150000698000c070010203000c00451202c080090b0740d4040300c052a40880401046c0c1000350048085061081e01c1c00801381c1052000b280e41d04100311500212808400f07950b00b0b0001d202c0041da6540c0044481e40f170400002d00004c074840d1130901500d0b028015400246075a5142410018142c82c40c50700620300c119507480a2102074052009170307c1d80103800000005e0b00c41005900000642c245c03030340091384040400184030074040c07041d00d104100e134400d1140c0e210a0790380707404407480d004091007a54045011180021506000c24000b103610428002034000204000c0d514041103074446400744000801c504200886810300400c0329014009580c1e409003d50316555800400344100e000080c14140710081c1407604a0003a18400075207030000382030b0381c160560400f000f42c0e9500340a8024185 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 528402410 1250 528401160 528401173
    0x7230d2a1a0d020c06040b07030c0503090c040c030605041518090308071803080706141503070501050f0405090906150103090c03030c150222091437020403020102 71
    0x910080200c0c1504803140225600803004103030010031000d40114400c6040039408020f0103c4940c0107101d41c9104030f1107400c2c1c4c5000c50808800c014101c943c540d50000c01d108040040c8071403040005106515901c00300c078042400c1186010440c003900f075991040e0b40090400464400200252894000f42c0b0420040740408942950291055804182014011450000100308203d1050a081e202c4072107540d1142d00340365483c1c1d01c80c0030507445214140c405030350301c1c1da500c0184041c0c1014180c0081c00030b0000003011101c1c0c80080d840e0305003446250706000780001d0030162580782c002514010030004060300c1b914a09020000d480708401c80d064045040000c620155660191061111564020302c00c2e4404a0541e03806603985a00709078151a060440c803110000009140020400420345c590000624940c0282c029820141908003291403030a0003000780d40391108051540d401882002c0383c20484c00d8a01d80303884858100e0f46600d411020001c038122000c00d05800900072a8800c1c1e003141c15 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 528403660 1250 528402410 528402473
    0x80a090311030a0809061605070605030702100509070b0706060e0a1e02070b1506070b04031e020f060a05100f1e06030b10141c140903070507230d 64
    0x8444000f841c00812a850501c1000c4460600788058a00d8a0054504075080b504680750079161507515481100011800010003900e1641840f94a852580349d80c824884c50800403440307a04c0e281d06014040c11140041000802d10415400c60340c028040c2481c0c00e02d580c181203406c140a480602c981d080810801b05800403142800d1003180c074030580105104803251a0144800d900d1192804010b80c810030521100c00410380703d04501c0d006070f200352248603000e601804280341e44410303189400b003550001c20461900e42c070f0100703440764030654012001525590791411402d0314000707070304070102460340c03071101041c0c40e003105a030b032841d175100105d142d107040e40e440d2011010b03034030030525203500705105541c9048040d014440101c00641d01d14100e5003400030104031651141034520000c100c694807a060760b40a203604020180d080a8024061450b0101342e0320303042e0340c602c0107104e001c2c01c04141004085c003c0c48000301803521800010003202e2004003904140000d04041c04042282d100b002c6030412 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 528404910 1250 528403660 528403663
    0x905030910110307021908030a030b090901060b0706180b07180e09152a07060c020d0c110f0d03080603060705040f05010e04090206030103030f08090109031403070309080a09031103 79
    0x200010010000f10325103501a0b090210f40314401c544055624015840881d000b00180040d01e00741c0d00c0b071b0341c0c00180068644100b00d284031001c1d00d0111140d00d003000510441d01402c0c00c6035185500301c0c2004c07540c10326815141c3d04002c010100500804003031800d1005090f409214440552800e8aa0760b452607112041012a00c07015610702035035038004140101034040e000d8a00345e02007101a50b00c8918040304111560564514031040e8100c480024005d080091318070800018086134801405000414000a4207200350700101400c800f948404c05100e95586543d004400d4001070248800c11903145405010820155032040c801d01511002603452442602601c048500714650002c1003132034140117484038a10030b964640c20a0b10341d01510b003d84c90b0703200114004d511980d1042002d0544200c02050b212010f00b012072a80d0510448030046031748044800d200e001d25061a035034a81720003405030001c20145000800086000c40c099040a42141041c4100d0f070080d5400050020500c4c1010f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 528406160 1250 528404910 528404927
    0x4081f0b0105070b041703011403070e0c0301211e030f0f02061b0403020d050c030d1407080306190e190204080d0318151505030312040b060102100905030910 69
    0x15400507109103d0300000c1000000d10b250814040d102810a150000441040e654026007101512526041d07501d40c007400d0400000d8010710342000c4510300c900f01502d410303041c7c0c8418814508042d0100c0d51a08010910314108502d01d0792020090000014a040404003840c000704168040f940b2100c0c40e040e42030280c8145c01c400000359001c2d021598981c1d40110740c00c1c0c410b12a400ba0741c0c40c00e010100060f291500c01da441603000d40e00410f16003403200c0405181c410305079015010000c40d440c0c036900d4443c40c0b00c241e40029500c80171654483c1d4413000416243d0480b0071010f04080ba03814800200402d04810290181112442020b111582d01c2c02e07007010b80c42580710320046c0e50712444014a04520940c050403040c5a4444c408020600e540ca1b5808264011101c1d81200c682e00c0034081e2550150807105c00c0204070580285081541401d54074041450060018144010b141d0000c5c101c0c0e84240501010709514030b01c00c100303010032403c0087c9d41c1d80080300034078090080301521514240c0603010300d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 528407410 1250 528406160 528406181
    0x150903031c1a030114040206030703091b03061d07090b0607062c0102070809040506030309060a080603060709030b1929210d0e010504090509010b0f090702030d0b1504081f 75
    0x8001c17281d1a076a0138024180e2000b06a0b41c101907440c449480041c00f44140c0035201021170070400010b6045003011002ca4400c01c120440010400001d8010450081100c5c800c545000b40001b030f0303c000c1c07000400e8017031103004c1000340032620700036058174141c400a55a866101051403180c611015140c2c01d0f500305c0c41120b0026000f1001440a00b40c24a4203030070060f88071001500780d900340030305900460035541103a01c5401c04200901e00b0403070141010010154080540d00e00703104401c1c40e54440d40c029031406050345038407081e51561f200c0c03200040e401200004a6000c5080d800c0d15800c450241c002c3c80c14030740240320303140700d81201ca41106020340c901583d032400c80203000020044001030b140910a002c0700781c180f210a100000b42401103104052182203506e001282402d801e400300460790600c6109140320342124810702c400280e0001c1901c03001104580e0004440802c80c000489801710b40d95184c09251001801080303988001c03d130f80300385102d040c00040740640e4010f42d4000703482c40d0165 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 528408660 1250 528407410 528407441
    0x61a13240e0306010b09040b03030f03180c031207080307020c1909050c13171906050114010827031201090902011704050a060c030b15130e0105150903031c1a0301 71
    0x2081b99031074154062240070200404503460401c0740f1054400030b80040704c4181d2010343c0000c002264032014822940300c40300480180500c4104081c1d52403450140c00005410f007040400041ca000b8000c002071952030340300401940501c201110b81c02e02000e081e000e50f000840c100304c0802d80c507416403030544817141542003076400c10354104442d800800d4660700d110070081c850102c00164040b80056400750070750040001042c1581440980c0c07107509444400241088801c004101140400814001c214800001400030901003402c482d4618055a044240200742210001504907403d510449042d07200382c0341d00510f60081e0f0680c1c80c07508000ca60281c8240c100301942d80000701c051b03100040456050038001303048142040401c00c20b40d10001c00320740084002610070251123002c11400c00514580400c86c00945c1424046074200d201c1d91001004000003148507466942c00344207543c1c0e400264601c0d00003031003d10900c24080e0146143c4800750690420300c0c00b0a9040600030300c4140201d001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 528409910 1250 528408660 528408667
    0x106060806033409021b0c0108011e091e0507090b030a05040204020409090b0103050c030a051e0a0b070e010906110618010b0a080604060609061a13240e0306010b 71
    0x7007240c0a44014040c07244102805601a0b00c0c0c241c02000300c3c1c8010b440c2d041001601c44800c03080081d50b5560105444980f94080c40c5008030071303030f44030280d6415074003180945c24031b50308125411151070301e41da003003418001d003464003000301c285400c95440100380403090180000d40b581c0c0010780302003149009a00d03230140100000742e40180302d600002e070400c1c80a00018903080c0c0e112100d0b42100e8414404481450300c4000400900104010301181c004086024000070115940e48568a280c81c0402c0c0307640c0090880c0400781a0340c1480102402a0412030400281c036100000802e40001707200300394049031000a0116030707103115050700300b4554204002040d442e198400e0041c110b11001d4000e1240b0742d2200d1000740e142c0c550340419402054030f44024807050810349000400c2d10102d0b0000c401d0301c1c1c41d180c0c003000145c80e03421380212100c600c02c5480303a80d00c0404c12a05d0b064000d40e080300569101c103080100704450300c800c3d03502d15503101d0390340c0c44084d107001c40c1010f07180c031001c0c0b28841c075450062 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 528411160 1250 528409910 528409933
    0xf0a0312031119020a0b101409090f0d08010e09030a0e061621080609070c1b03170406030e070e010b0c071a2107050703030b1809030c010606080603 65
    0x35800414a060302042d0b06060190041030350b43c2c9400c0c0f8208000058201e801d00504001480380c20701d40202542c4060983e03607040203d100040c0c10102c681a11074442d80c1c0101e412008107210110031201c4010030340c0d11802e02c0d150042c29640080c070407000106519400a610036074044151089074413641e94031800d0900c4001000580e42110311100c440c2c4050103400000514001c007400d040c00c0300229917440b464141c00024245401c0140070500600c060002c00c01c450380d101c144d0b41c15007548625407841c2e10074003805000070719103540c0004180f2100340148a41043e07081c8090011222a56024400e44c00c85440e003d85070310701846006501010003005010b29050350300035164105132030045441e07443c0e49480350303400100070b0b980442c80414006100710702e9825404c00800c079590006602c1c8070f07c1c1000d24000301f81d4810b046000c1d040585d9603844501d41d9580403c10040c504101d140c0210508082e2101c40d101c1c0d203d183c104249600e060300003c2c1003801803000c0351288000070050040c0001c1d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 528412410 1250 528411160 528411167
    0xc0804030f0e04241707060c030903080c061b090d02090a110310031a0108030412060902061207080121080d0b0910052407121202070f020f0a0312 64
    0x1c4040405200c1c40703803891010741e1254480d0b142244465041074040015566242c810b0301140c1d0040d03161180495030305082041c0c001124021502c16250140c04a2041d082c00c4641c5181c64200829800e40028541c07070341d0200045060085035400207000b5101c0b0140654400351055450b0310b03801400701050034003d840c00e0500c2031751101d0103800104001240e000f001040342e2003111608424038600c4814014400142c007424001004000002c80650421142c07940c5d03801b46100d911600c4510200b858108480c5030420310895078041c149a072a030240d500e04070054a41103510500240780341e0300024018440d5024429881d4140f00050a14409511400c8887d845605880c0c00307191910b80441860325050a4140311f90711143c5050200e6040c107080043e514080034240c0ba40c2040424400e220f40c100004682c503681e8044600340b04030000c403038243c450b40605440520700a10126004051042c1d580d00a550341d4801c0790b198400d61040020001500301c0d038000542440642442c4aa14600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 528413660 1250 528412410 528412427
    0x1d04050c030a0501270812070207030c03030e091f0501080a090c03150606080c03130f020a18110307200a1b0305060711030a0302070201090f0906060807030c080403 72
    0x15000d40d4030300054400840e02e480d1802d1001c44050795503450f801150030128413071440b03c050b44820002d4071038903511650402c1c081e0b9502c03043c11125a001040405008100120003140e200c8040848540d4a0a0181c529901c0240c0c3c42e002e5007602c07000828624110101190355203103080e5690f542800e0900443c0d41a000071f091802e901d075a000030fa80030035004548003005601c10141c45d07801c250350840203416109030351b0081c0300b4010310400b80f1000040c031105903a40260364400c0750707400d041c150400300e0360050441d00182d00203141c0c92000c81c2d003100c1001c0c00790100c100d5002c14001c0008a03814605c00e4070048440c68001102c5411200090050541901000e620b0b001204c0b511060307606c42180001132110113243c0c161a400c01001041400e00c2220fa02c0031850901040e60100c40754200d4591064896000405500081da101168010781c040c0000c0c04038043d21031041c03601e60012600901040c050480402c0e00c04000a6507a8405c0c0141c0c0203806241d030f6000300036200c40c0d505a0f00c0c5003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 528414910 1250 528413660 528413663
    0x10091206020c0114071b030206061003021c1d06040807080c0a050f0d09091803030c051c020a0e06031b090f040504061d030a02031903110705070f06091d04 68
    0x940030010b01d0300c1036109020310200303880340882c0040303c0e040040c000380400070030b0750086003415800319010010070740110301c1d140e0021041d5050030030940400d104030700038810807400d5222691120444640095a5400311112241961f4600114120540203968840c0122802020000104030090014010401408202c980f020171955204509c1e0780b02d5081c140c508800c0d21503036000f4444000060703800f409120080610040400104510f9040c424038041c0003c0080d050540320715170909814441e80484481c1d113000c0004015400103105458003a511807040b040c0080d40105024090f8508038048a00480300218511860b400103d0142541d030403400300164051100c80d095059502c0e68059540305502c40c10000032040345407001d00083c0400b150000002c0d0b4024014404082c0d000000c4444000c0c07024040c44a40440c58021006000800388581c9200c00104001080040000342c01c026290704903015101d00d500d0b540116812402c40c4201c080d149001c01800700c400303080d50042c13138115 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 528416160 1250 528414910 528414923
    0x5090c0c1c1b0503030a140106050d0c021627020a020a03030f020906030408030f010803030c090103020306030f03070804061106100909050c091003021509030c1005070609030905010806100912 84
    0x51040d0303001c120320301440c84040e60f003500000200840303032040b07200307004d616940340c8207007403a80d41040c1004003503001d41c2d102e0b00801941d40c40160000ba000300183c1e088194045603c4403019291601a44240215802501031456081141c1c0d082c141078025190040201d6005001c030b0040360300e00f1000340c1103045490a045508004513092070700c41800642c413540c0241482641c0c0d0030105080300032980168480b100c81e800034020320048941001c06c894403c1000d02c2e0150322a120503002904040c42d5003070840140c40005070792400c0180c0c09010b07204a8466440c0d52500c092921511030321960120303460444e02e59008000d1001d01160380c000903a01e4051800c645c1800c900c4004150800c10590706040e00e0074980c82c0401c1140f8014028100001d00440000c0c01c08188401080d5154003013403c842c802c4403a2100d510155125a003a01e0086401c00004e00c10354000b810003504410790341c007405000900d03100020758a402c1c400d4070b08105c060265601c40001d0f2802140e58400c0841c004101d501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 528417266 1106 528416160 528416177
    0x140702160807090218120c03061501020706110c03120417070b122208130e04020306010306020a120f0c02010605120c0405070302120f0105090c0c1c 65
    0x100c8a24500242c1c560200745d02800f080900381521030b400840c601c9110301403403000034011580c480150250303141602c0c0c4501424400030040401c0e4056844000b04000c031500c246c1c0b007044a075503460291649041e15200290902d4410001905059008601070020003c4003901041c0c6604000081c00d4580c0f4262240c580d070300030010843c102014030400100441c440c21201310214011010503004031442c3c1c030f03110855400c000f200e0039202c0c40c4071101144102504c801c2501403030300180103208030380c61952000065444401c03184200501c0d182c0e20f070f40d001628082e40c1c01003851501e0201c0d40c4645034000908480466000c0e5101da0425a81040e0343c24002c148910440e50944001c0f0f1b00c6d9a6100c003d40c040e200da0b2110074031681044080040c41d100c5003516038141c9000711200b020540320038682c10b4850043d03160410640c0c0050303c46050803260708900f00e00758801420318015 = true := by decide +kernel

theorem cover : BRFrame.Cov 528237410 528417266 := by
  have h0 := BRFrame.cov_init 528237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 528237410 ≤ n) (h2 : n < 528417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
