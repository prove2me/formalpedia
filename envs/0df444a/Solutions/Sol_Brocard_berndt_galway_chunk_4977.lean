-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4977
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:20:42.975242+00:00
-- url     : https://prove2.me/submissions/aef56b79-9a7f-4355-bb25-3f472dc0fb39

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 894964028 ≤ n < 895143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 894965278 1250 894964028 894964043
    0x227190308071e0b070915020d0801090209060c07090c080f0f04030f170f060139030207120303050108060c0a0816020f0a03080f1302061204080706090b0a0605010813020d 75
    0x1030060b990710118040944c4c0010120b41c00c03420501090f0014044140781c0e03401232004200c140d0f0400c001401c2c89074103015200c80542c0024030b440c0203403900030403610101900003c072242244d235414110000c204505111b00059100004100501251410140181d880070000348a64480d5601034440c180d4107940300c003e000c3e11407044100c0d440100007a61060b1040300b2482c22900d0718500041410b84182c00d2014800030002900f9107140c06c600950305203035507607901c480b4200f0441c201030b4901080e41d4041c070022140040b02a08050703064011504a4400104464090729181a02915402041044000102c20600242001069038595480450240150f07112505190b4049041002c0c560f801e8010030141d03411300800c0803000b5800c0c0c1e8003110088005c260300c3c041c1c2c1d0005940c0e224441a00b80301d0200c3c1008603050103002c1e003c880c181d0341d02010400281c400d5140030a0152070441d00b49032010314000b000603c550003a00790380c1c8a540546620041091980d0030458076a1a841c130a80780d16 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 894966528 1250 894965278 894965333
    0x1203100b040b070b07081521030a050d0b030601051302070609120c050c042a090504050a1a01020c0105030a0e0307021201020c0d110a15022719030807 66
    0x3600c09000900140541c04681503884081d42031030f10344c01e00050144420030824204118040c4c000d040d00f14403d04d0201d5803041010b10b20285d40b2550b407480340c41880385010004111049907041b6001700400c0250f080d050000e0041d000c20561903060900c106034018514095002415a00764014107410f03119070320018414240b5220701d0720322540721401d070010817090701301035042c00300030840546a410f00f1142030040c00e451a14402c0d14000000c045070401e0b403c46460500d06010707180f0103015146c040e004201c585450030b9400701804030300c010309007803030402403209081d54800304044101130010f0710703100d20350780b5038064020040032442a03169150006022120061351807600010b40c0e40c01c80d5002688441d180214281092418403e842c14007c1900c40740d02c1c00c00f00860111a4150042d03071043c1c00d0b01c0c4825901004e885040070441395007550040084600301071402205190760280c0d500794030100c840d141a00018440e0101804401c070034441e82c00000d07440d00040c2040c400d188080d03000c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 894967778 1250 894966528 894966539
    0x150804050a060c030204170105241c03020a14010b0f130209043314010f0c1a0106080a0603050c1002010209150909060d020105070f0c08030403060b0918120310 70
    0x3c884030200c821000a40003d4104924051b40b03c0f03240d01e03142d9410003005582048036100c0285540703200800401082c0c0120784519585016440c1c0702880d0640c0e80e031410307220915000391104040001103407180340c640c0c2112000b00051148124101007d045d20100648900070050180140c5400c0d40e0f85540030041850a03842d14041c199401070845400025400c203450150315001083c02c1c465a441002141005541c1100c0d440313001c0440c1c02e00341400c02000b2040100e0b418603a400000c0d050442e2042004100000110303100d04031405035a034012a038880c0c182c80b10039240c0902c8003414990000501c0f074050303d004500c040541c4480e0000603e0010380c04007046202180141d0180042404289103005003080c0c0301c001e6000c14103d40c03021000c002c96001070054000c407070000d868410301c08030300e5040003d040c4400d0040c10251013101d842d03a82d41e14040e0060507021a9540c0070340c2404011a031200003d1420f00e003415107440161a00d01003525812103103820080103130b40049941d000010740d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 894969028 1250 894967778 894967781
    0x40501020d020a050304061a0603010b0f0708032805070203070803101707060f080f010b0a02071e140307051522060f030b010c02101b02130b03070b04150804050a06 72
    0x500662904e40310740702e20b400d0416004491951102d090f0707294619503c0c0515503545001c50307066549104000791030f04258520102d0300d00035140014183c000010600c202c02c02c1559165105411280d500104510404961416514140e86460169006020840008000382d01455110030720041250699640da84244040d502240c036007403440d045030301d061114561204e0850f82c402624140f10319107050160745000c0294052082020722000421106a414400d01145e001040389030198076444040190055803c08248502603440f021b81d640300c140c908000ca07010003181c034014543c0305078040e030440c0c8180c50391100c8410403400c40c01c01d1540d400040c0c04600100074060700e90703c14810540c041d501a0454006071031450510545000010040e661028800081c80c06850724020040b50b284031140001414a4002e51184070a25006201101e940c450400c01038101d0446640660b10b1a162005201d24040d0550a0383c41004504401d400f8010044c2c000303110703404031981d82209484040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 894970278 1250 894969028 894969037
    0x106050d24090b131103060a08071a2101090b03071a070b04030c0b010b13090b030c01030e2802011b05030a0e010e191a04080a1e14061b07020f09040501020d02 70
    0x85e0ba82c0c012060014605040c8a124040e011520080c00d42c2810305100002d507034030307030072042c0d142c880b00051516840c620380c503010b1500b0544405c80062035071182502c802400110700000d001380b06205000400303115100380c0c1c10501004519a5282440b151103000d01a071300200141c09200d12403088600103103589049074001c00304196481c1d1285d0340b00a0001c040070882d0b100a81e84c82c1080c410401e075903004101402800c4090074005207900c04184205e0815080000562180c1410402030034071161100b0b10100640c800d0360340b07040039000300031010b060440310300000e48154814450340c281c0d0390207040710300d02e4010141482a040118000011b8400103d0800003003d90710031b40003000002c0401103840108440310414505250802d6200c540d2600c1c0700c2c00181000d0030340c0c0da603c2684a00b4400701c81041c0d82280340320f0f102841681106640d0a0240c03852412100c4a0244200100c0254161944240d00400051a0341480b00801003e020044c2007a10655400c2022100d08601c920003070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 894971528 1250 894970278 894970301
    0x723030f0309030a09091a100e061b0f07030f1e02040509030901030c0f170613090f0b220201030209030f160f050901140d110301050106050d24090b13 66
    0x3d503030710125840c0003084120a5406100c1042c20150031280108840c80105101d0350190341081170b2200641c0125540a20003000b560805c0c00051a00c00300210071500d9480c1e0552081250000c03418403203003990f00c524a00c0041c00d00200e070518407000400ca00d42460701c00c03841d551407040030034040c0c0000301101c50079108071110354000115a589560036015a96480820381010100800c41e402c02500c60403440603d000d147c4841000603000d6038588590882c2011841e20421044000f8134040c44040d9245000350384c2100000001030710501150740e0f2003c429902d4900c1740b5028156401500a500602070305607160280300010040d11008104642c189954500c41001d85454600280d0007011710340c1201e402441000c00500c50010142d203005141d1200792685611480307030b0704010b41c03803180030103039503605500700b10001070200d51100141041e60000f203810000c0d18602c01c42500c1c0108040c0000b45100708a81c020048d1041d142d03c01c480c03040020700070702c0c114034041415200301d81546502 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 894972778 1250 894971528 894971533
    0xe013006090b0a06150e010f180b0a0503040510020f07080a02030d091101121415010504033003090b0604020d06080102030a05090c030601290c100b0102010e030723030f0309 76
    0x5c011050040c607825040b02d50078100f203407000c95007000090441c1c1c0c815403258248008104000007030007c103480c4800400034050016201c0c03224160003003c9074000d80c1e00355814880d80048001c0c05920744202d8901d20701d80100d8a1910314645d69150281c1c02940d00c05003540014020b01c542250703503010340e820051107002c41d1819001c0140c005001b0036007041c08000810319088861610507564038406811407402000c0d01141050400101c0b42c41c400e0350401414081c0d62030304e118143d074003030391030510f86205404c0d20500f0950300c15045003203c0c10428054041c0c4a80d80201c3c8003800c05031700803c0500e900c0f010100d0002d441c2c9401030b0036a481554544505d55856040050310b40302401100c4110204802a101e554034050402d20010310b15520300e040440d11030240d02841c01d005003150000880b503026168900e5400032110000c1080c01d044074055402c081030071a6a6101101725441d095118070300440c0d010000141da0f0329203d011080c3e0b0440d2104110384a40480e00d2000b0f9403141d8404c400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 894974028 1250 894972778 894972791
    0x106200604030c060f02090a0504020705071a0a08011403031b0709020a1d0604290d1404020f010201110a1d04060f090b03060105060f03090a021203040e013006090b0a 73
    0x70301a040340d1720303510408640d0f4414401522503035200c41c1c601085590855016844641d541030045c01d2161700da00030b592680202c50606000d85816003d0031184083d44c8416820781e03030342c1a81c05030490b8034040d4241d06408c100001d41780112208000304e003011901048400b240c0c0c88410010890744452040408540d603052810f81582000d8204034010500342c0700c0754200f525040b0030605180b06400382146006460544030410140b071030a03141c5407920400103118991001042c0a00b40000f59000d03800b800c85150450700e2540140201d880ba0009000060300d0f20821440480e100da01140c00300b401c040e02407100d088503a9031409041e02420101e81003001c41e42c64604040111128901c0c414041d40000c2c00421080d82c0d10700070303180800c408045140d500d603103074100d490401030030b45402503112007030421420798140000054425117240661800640c0d803200c010052081c500103440f40303142e490791a00c65000040401d80820244519404520880c4075a07560107076000c100ca01c81403c6503a4074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 894975278 1250 894974028 894974033
    0x4090e061303140a022404032304050f010c0606030b060a0f1203050a0c02040606020c0f0117041410021810320706090b040308011d0106200604030c 65
    0x7900110581c40d45103404030641d8010f840d19031040c44803050700301c0105001080c03500900400c04882e404c08072180340d988180144c003a00c0882610301341c00059211490034080100a9401c80d28220401c3c049402c007440c040070043e22100c5105500e0401c400320b12010000703503050240e0005940700d0300e40b0350740a19141c02480200360b07580c0d0103404410304d541400c001c414500c1c03c2c8080c859800d41340c1665601c03401300c02070340c0205081400a4119182020006107141d0205013422440380c101c401d40b4282a001300115904400c034074035174412402d11804a0001880300c9204e800201c41081a01c41d0303c0c00300540803040f43c0100170306441c10f0106a810160903c0d0070b80760306084901c1420045568960400c4050b03031b0120281456616000c40885081e039681044146c0c0c2c0542e40c0f0080c144080c140a01d082d500d8410159800c40124410130004075201088208144c07525060f1040c100c200d80c6403010445100c0c0340030b0721224100d41c01180307129a103a014040c140c4118000e448610101260f071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 894976528 1250 894975278 894975283
    0x5040605010515040b03010b13031b1401050721030b2e110613081303030905130c021002090d0b0414121306050d0605030a0c09061a0f031b04090e 64
    0x405406003900010082442003645c48425a41946d12680050752203035a201c09020100700107800240c00d441201d120401d020320402d4103a41615000426400c400f6444001590580a050030040180c0030040008000c8100c04541011003026803402080448244010980f0710b4000c103023050305094624401c3d81b40c800c1c0d00444026080311844c00301c0b81d1203021807526032185030140c040c072001e000300510b510500c070405094611010b0b140740119011344c1d0781e02d409441104a44240d90203190940680140d0808030300c0b406142c003145401901a203a030f40c0140c0e900035400150032a03401001d50f104403001c603144a0100c1c0c802e510038600c6900d50720005e42030078070344006e08000c501007800800030301890b0300e9002d131258210348050400c1c644500380d0091480107402e0940146405114400c129420b000811015804540c0d800030100201510b400520300d100c2c214000c2e2212910042007030b0811000c0001c000c50303205845c01c0b150240e40104a01902c0075a000d90700142c09952250162141524203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 894977778 1250 894976528 894976549
    0x16050102060402010804060507020709020315030c100c170c07090e0f07061d0307090527010204030201080f1e0103142505040914030a1d0405060906060a0909050406050105 75
    0x9000400d500c1c641540020200d510040008040c9900d88c40481c80d146c2c001c00651014145500e029502e82c9810382100b100b41758600c41051080c8203400c0e481c0b03c1030604207245c45420400740e444038100703101e40d25031100d0141c461644064482041244404a01092201d007000c1c080d02a000b0950320000390b480c9103011100c1740011300c1504241c00401003d50010b80c0d168116182100c801032031210b4000103800c000a86e072080d040c203030400040102040c12056810f0030940d2102d6100804003c005600b8201c0c081c6002c001c0c003151140b030102c1d04003007405509076403200c40354074025012140c4148080040f1002e0b48100d500001c0c0c0103000703101d00700500203240303c0c1c80303182907800810124550703a1411183c0c52080d14016681c0301d5070760007071003401194444995502400c49503101508000100604140320b4038000d2068134042c041031510302401418040d1000501d10159511014104695944804071003010f02008681c001103100c1c0030f00a552045000342c038000b4180d8901400d100b440c808 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 894979028 1250 894977778 894977789
    0x50702160b0a270509062e02070b21060d050f0d0813020a0b0c010225030f08240111070b090f0406030812040501090b360706030f0906050916 62
    0x3441074100c000012901e80740740498404617600201038580b48003180e40c2c041c030b00c50b070170442900d615000400c494038100f44d248103881d190b007210743c800d0f6611081d00c1580940e580d042006414865079070140c64030204420b801503401026100c00c00d40c1d40c2d440c42d203404d5082509801d0790300030004042a05070840704083d0301c040c4d070b108a1f40e40c8000550000f01c05040c00d02949040c0f00000c01c504680031002d605807600d0042c0904032101c035462104003070044181c1d88070110b000038007042c3c1644907207225507000c0340690307a11f218108484c2c00301c20078941070300c2400c82e0a5040101410410942000401050004103048802c140c1da62110100b8400303000d420700449070181d410450204000790705541210614425503280c18003e4403a454407034003421030000064542400c3c4014040010030003e4403511800d000c0400c94862010b46402c2084058200b044407075a40105c0800c200d100c2c040e41115408194050000586082c075a55260441c1e0080d11400d9240c2d12030141003c01801c907401c00805440d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 894980278 1250 894979028 894979067
    0x301090c02070f081e190204090f0c0f090e0d0903021021061809030804260d240f120507080307050a12141c021603020105060a2403050702160b0a 64
    0xa840c1c0d4400806c0000d03110000d0007240d6a25a08040c0325100c54007249507603000018810403907940d03111406c41105405405800303442c100d0b51000b0000c0004045103410101d864207250340e49940c081011561618100364103000070325547d4070501c41081c213403804800040340d0004100e802c1c002c404071a402c0c01e03800202180d10b482c15041c082508184440c0d4403075480410302d0b9001c0c040c00c41e09040050943d040c1c8209a1012510040a03010341d00034034a0510030b900503121320000003840040d120103510820400180000080c410443c03d2001c40b0401801902200c8500341c1e43c581140ca107911400090b5165000ac0090a040010106400c852041e0516043c0395032110034185410b9886458842612036031540c000e00780d008202d4041e26003051001d031014407443c0607400c010b4042c190855085209132408400403981c640030841e203003200c141c0d16034090f0190b0301d010360613001030901030240c03000d501c035030b444030b451090f1850f113041d018003003074044d5a032520001c11010345001c203c0d40c000d28852 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 894981528 1250 894980278 894980293
    0x7081506040b040b0307051e0315091003120e090f091e06060409060e01020307230c0a110d0b0a020a090608151905060c070f090903050301090c02070f081e 68
    0xc22004007034405135092070002ca582c907200c048090340e0380d02c203014400600e05401c1c510070000b5007440000e5031081281607944900c0403286410000342050450713021924086032a070501c049595070b029a440d0102c68180b000c4540c13a9000013558000707044401c00c586903201d4040024081003070100e00c0b81000181f40303207500c940310150250340f2000c00500c068060b41c2c0d0354055005200c0c290f0880142e005010008547c1d074105580300404011048080d0b11200700a0b40b604504d0300030502c01c4400c0c2480c0c44014003204001c540c0c403400101c10070000581d1146151350010701180c1c0c800401400b901544000599600e2030040152040215500143c2070003100c8041041400c180d000403081c500b0100c2c0c01041808660031070f5000495190030480e0480701c08104030300c482d400040c5040070307100c4101038004456512010b40e0192819613000500240f401d000420001610fa00008076002060040d1005641c072010004c01401c5a80c2c003401c042da0200c070310321034003000c4050700c2180f08900d400074101c00c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 894982778 1250 894981528 894981539
    0x90308070e0406030605151e010e09060a082b021902010305090f030406020a0605060a060912030203090316031202061014030705040e0109021e0f011b0b0708150604 72
    0x901002003011090150401c2001c0241d5a03992010018503071010f800c01c040d062140040c1c00c0300c4c82c3c42030914052540054400120f0852452150a04505039182c030032440d212010700449080140a0716044101c0100106510a050044e00740403c084101c2071168865411000000001c0008600554011202086030082c91358840e040c401e0302030034041220340368806210300c0c1004070200840319010119000c07840700d074003240002c000c50054400340082e0b19000c00308410311a0303d110b0781022030b440a10401007031003c520704031385403806030054a051518900100e4109070283c40c140c540d0050800c0c0500030850110440f180c8001644010965440d0001c07040303900070142d02984404100c040c1c8040e045950410000e0080d08019006001d06455108035a0107231842c03071400c0744148002d070460a804003028808401990b00100603494400103c001510805104820b96454100182006005c18060000c00d806100305507655540c0d450030f544444880031980807030602c58102000100700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 894984028 1250 894982778 894982787
    0x1b0a052a0906101205100f06140712050c060c071509050a06200c01020c070b1809040206040b0319061e1e0e010801021207090501050a0f031d0109060c030903 69
    0x148010250f6035116860b40201c000d44000f101401611101d0781441c00300300c1c40b00141c0b824407003140d060750040c000050300c03030310241e85002c8030f95807280707112400307201d03807800f107820151040400152402c180785011000c1d9001820403104680c2244c0c24100080c1c01c2c010401c03041607101010314400000c00c400c6c042699010f450b03208001019000c0754446170b038260350800003030458414481940a280d520500c055a41d8040d400801e451901c901400c2030004100101508a0b0241100f01842e92102d407000380c100131b0460f030064030590f001441400041001c03034100300198044d501031300b00c80c28580c80b80c94039481a103200d40c22905200c2101c18070b4403001c9646084240503504011043c8403503107150020814440901e43c0403643c0f071000c3c0000090701c58010b600404c90074121480f0000c85984a220681d1045528820580054410415243c0d00351051414001c080500d241c081065a0151860a130008a00345900c1aa9550304000b104008031307031144010b03181c0c0d6410140701c401c0d001e450141 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 894985278 1250 894984028 894984031
    0x4090201020c240d05041401060803030403082a1206030c010504090f09050118050c01080601080703021b010c180f080606011b0b1602210f1b0a052a09 66
    0x1405603410030056440e452040ca256040b210014409a4644903001d80c800c01410046da010341d01e05806c04150380701c08030b040c000c0e0340555454100462540c0c54603582111421700042110340180d541e09400601c0a07010034455120900e001c62164076907590040307038404c42c0c10180030302c0d00c0fa5124040040e2a81d030840c043c3c804885407210000754000c3c00d842500050311240c24001e04a510781000761074544c1a0b1310039520024001c000f15410420582c1c019111944190b0399940070584000002c3d0b101c038481e40042940c0b2620445500c10740c0307403252403142500e80c50031071403000c41d9024155502010886a0240050143ea07004504043c5866100c9807552009081d85041111504580602018075509092001d0b4040d03502c05607842c0800e1070544040e0620078650060059555008600c84294a00b1085035001d10110345001c10313070701a40341c903680011481c4a0741c01d680208101f02d01700500003180024016030162107003a01e141c0309008181e01003009054042401c3d481d0320741c0342e2140040789 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 894986528 1250 894985278 894985303
    0x22a10140a0b0307030507060c12020a150b0102010b10081501050708070b10120803010303140304020a17150c030a0605100f08062e0807092405040e13050c0409020102 73
    0x400400d0ba10200b41800c0150304003501030700c45d8482c00909558494a944e03141401090540c20156001008980ba0392040d031000e08080c42808120720f403844158003c8a0307120050000094452000c0c012451103141c48892201242010301013284601d00c201448804601c01d103465450251190348807042c45c007414801400818011000400d050407494889010305001c3c2c11025555409144c80c00d4a94401d000031000291914094000c0d120301034190b9001e180e006043c0c0d11024281022454000b01c94016241d052143c06801340140152100b89030003220000c0e900c55603440c1004000040c0c1e03e1507071116000340c2d24a074175a65050f0388020603645c1c00c00145400c01c12030311902c00049403100501d400300d410001998840440500186064000ca0070684a5501a999503401a10380c4c104c548210580c01c50b400c08580316503000206540c0c42d0000754181a410643c540802080705402182c84500b0f20000351140c7d400d100e81001000d08586d02140c041c0140742039176000035114005806c06 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 894987778 1250 894986528 894986531
    0x140a05060f061e040b1605100501050105030a0c0306170c030606030c13020a031d06041a01080a020111010f2c2b03091203150503010203151201022a10140a 68
    0x814240001c990201c0d402003445c045619110010351071900351864191004599078400c0f00d900200e40f1a09015050490b4816103c0f582140c1da803440040103440250600400c06607188804541040e40c18010442c4038070000080111010101c2818078001000d01541d209900c0082090030990f1040d090016004031050b01586417036042c94150060b060f80c4503400c0d403030f0f4007110140c1d0301c94100182072031042c0c0c01406650b20824241d40c8950741d8800030b0154100942000c400750016501404002c08048000c0c0d00000741d40e24220a401c1c212258607104400344040300b050700a00600c0000302d40300702403e140c050811920404c01c43c44103019107400322101a2003050501000038000d6101c0306010f5040a9207040c80d54220b60001d00606907400b42c1c002d1041c442001054600f0140b0030750b4400d00c05e510380346118120400c10020210a900d00301e006540d02040505150f00007a4845020300d50310400c01e07801c03225840102e50900c090380303038400c2030189032020709115075143d10b00050304049008070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 894989028 1250 894987778 894987817
    0xf01120f050c0d06050a0c0c120518040218010f0f0203030f07021e0c1003060f030b060a171f0203070e0609010c210f0903050a08090d06140a05060f06 66
    0xc115050000480003994440c40c4100840d05004e05070300300314410741004408000040400d9400e8580c28250b08001c1c00124205020382c40c2c0c940114024503030b14030254907074140c003030400c40000c069a00522240350f10380c0c00200b0080c05d65800c4001e1800c0600142440780c85401d9030754000b55240002803228440b031005601042950303000b44400384c240500310f03002082d00b803401d0803480e607070702020380036203018007030200c40b00e07000c10300c80c0c80744c4070658182c009600c1100303141d07803111000d40401502003076100e0382c203010008803540188000e450068505000d40360070103204001d0036000806504036204140104100812746500035581c5005140031100540c0b40c0d5031110040721680301c00c2d800209100c1171400c12418415882c0341d4140110314954030f40ea407038400e002040f1102c1820748802041c0794048244000025110340140c211024050130100f01e1030500d446140540d00b0080140380d1194060084c86004182401100d0b807048041e6452a0200f440c800420540e12590420b0841c1314041c06 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 894990278 1250 894989028 894989033
    0xd0504120f26130503160311070b07080309030c0307060608060708130201080405031c051005040c17041703151f0f20250e010f1e15090e0f01120f 64
    0x103140c1003070f90760414110703038075010044124601d000070804180c1c00300308041031440788144001521070030340f075a0700d0009080074420382d40da1030141c2000e0600c1c8000d000034844028418010805800b08500902c4040307806458050700508094000c1d00711420490401c0c104001e080d00080d1011949a080c070384440c10b03544508026003140101140c0300030595804001c0d0380c01c0d100d19000b8178081c4c4031038075203408199941d408000465100c00001c1010440300440d07200c0c080d50044404d64882c0c001c0304000c40301c0e80c140642e852164401c403103150107800b046000c00214100052401d103d15891101354024903140000503110b1441c404042007008482101603000303e00341000012520190700071a1502038543e08003081103801164411500394080c00300091b41e44d003115405042b241040003591b4030500741498881009088100c0d21035100e40d003100040c0081d81841642e50009150b80d0303034420141005204490441d010703003514401400c1c900144404a003c4490f1043d4980c0910103507074040103803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 894991528 1250 894990278 894990301
    0x301141201112212030e090c13060f110111030a09080f030405060f0907060f050a1809150603020306090106050c070305010f02300414030d0504120f26 66
    0xc0303101804a40e020844030000407007400108101d940c95501c3d030b40502e0f00ea003c005141a10404060006000b1080c01c00360750400c180015000343d4680c007000d00c0d040011810081c85607484e40550001801c076801401015030142c0c50055054000b0000d216005105a0384110f07808060000d107170042c1d80360240801c000c0c40404881c0003030844010107032203180c5800c01c0b688451084070504200c00030703040081d01d42080070404c5019034500e85c03034100b400d8910305000c4855800481040040c4030004a21350142c00c040200c06005003445c0c60049003100280c2c485004000031317503001400b41801030083c40020f503909203805e410b40d115803504589035106504c0c0b1a250500e030f94000380c5254641440800070040703039002000307a980203220410001d0402d0322880d0a401090904c00c402c120182c0200c0c1c00a00f20360f071022403008070401100c4c2040444240c10341150760036501124800940041071130411b0300b086a0b11104072103800c160090082c200d40b0810380d00c010782c4024418865910000354a003d21 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 894992778 1250 894991528 894991541
    0x815094503030f160203090a08070501030605010513060c0311010515010e06070c0e060a030b01030302070e060a030b041202030d1109030d021501270906050405010f0203330d050717030301141201 85
    0x201420260380c1e8271020a52103a03200c1c004d03180001d080c200c012400f94080da04640810300100c0305804904c0c542681180c100440d0181202001010155a1180310f400d00a442c0106104482e10034401c80400c00940341607140e2030454080c1d002070203940d01081c16402038508680c100d840d6403d16645120000720800034540000b1700c1e0b07088001c0088103041c0c2c0020148265088500203c00030344070801044640701c071510008000f40d400d14006000511032000c44118a802401103a04080307440f00c1c040c003581c4260042042c180008592104585402c220310310551a0b5030000d84039817000840c071103006441c140520001c1208010714905c41c4184400f845c440302c811600f080015030080c3c03420402402083d02c0c25507280d800c006000041035590b100b224082c4580d16020080414030280c182c0721118030b00f008004041000380503c2581e100d041c3c42c0400248104003805485052424542c680907684110760740d10360050005100d000c9442513440001c5908581410803240c0f01410350b03015126 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 894994028 1250 894992778 894992797
    0x3190c03054309060e010513050f150c010c081501080c370f0f05180604030611091e01020a0b0a0e010f0c0f0815094503030f160203 58
    0x60b441d001d4039a0b110300304105507141c075039420188051200c011641070103081481c03d50402d54202c20802403070f00300085032500801030000e000007000b04403040300d142c0000b03110481c60394440381030b03140099020442030780c0000ca500e04107a0074403c020000b845441e00034180f01408400040c900810b0703802c0140240d01e8008240041c0c1c0e582d01c1c2c00601415509110305100200b0b4121001e11141da010304000342044d4042d954460030964011150741d025141d60b040c3c070b40c011108000c0480494400e00805040c41103403041140d84440a000303200e10001110700c01007468880102514581c0ea0101d00e014103950008124291602d460b00d000008000107500c09005600e0818065a034040e03580020207001d0b40d41d101d141b828480b611090f21403c8040b00c2400702182e0000b1100094940300c1c0310309400078120400035400901e40c92805561000290b220b11100900e14511055040078014554402c1d9207400558110301303245910706140ca001a0140c0385505410420000c654400c0059902c3cac0413 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 894995278 1250 894994028 894994141
    0x90f0204090206121e01090c27050d051b120c040203066a02030906030c0304020a050d110d170d021902070510030f090803190c0305 58
    0x3c0c03c491241000078100c0c00c0c217660883d80d900001c2c0044181c81a1104155280c4516031400c0850b5440492a11030408500b5010844000441c1035200e014541c072880d8071640042502c0d00225044038030420100c900584180801d0044411551011030300c0000c0780c0040c0e50240c0c40f07403104400182003c484c000025a11451403901c5801c26680c1d607a02d010701c1c039111380321159039091a1040240300d0b074008005048450315202415040c13030111801d110b410440d205403424047d8010014410385d2003990b81c1310505001005010940c074000c81500d0040500300e4540c401025660303114440311000d00c242600c82c80e1120040e0b01400000d00030903108481680c4555521030301d0321706480007500000302c0300d01648080c02305198442d000065400c241e03040184400003207482c0700021030203011249070381424545ca8201d00e0000a001401071406400401284000c42254441107003c44000410807420503003407000740182c000e610040c0c0810708100d56940c000b042c2d146441e055512244501001c243c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 894996528 1250 894995278 894995281
    0x1206180f05060a05060618010c05070801020f04140604030317062e023c070b1602030f0c090a0e071d011d070f0e03190803060310090f020409020612 65
    0x340403031140c0c40f070031150308100400d403111402d0200d103024840c00030a07a1002220640382640c02810480580ba1080089604890307c0c0c41c0d502c0d080e038025552840324064045000d00c204401003007003031000d074000c0c0c2e880c42c20a4503680b401403603c1010040d40c0182c8608201181084c1c440c0c941074000d046440b003101103119914585162820788540c4505e0060145c01a104038540c96486850160036400440013403400c0c840400500e03c420069268445100e903400001c0c0b201d030600050440003409002603428500d140c0107050510ba240c112038040703900501101281943c1d451003450304810003000000b1407000034020607140c02101c0c1c0055a40a480000907500304100301c0d0201c0c140c07401540b000080340b007524260b40d60a1001c3e500140840c0312545041049880303200c2c0741421000049c01c40310307a00303003181403c020500d030520300351803a090000400a1a080800c2028045040b10704200403d110a0315004009041d41c0030080c421500e560b40c210640d5a2001551a060202580c00190307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 894997778 1250 894996528 894996533
    0x60e030309120714042a1211070b071701031202030408060a020d0b09070f050904091e050607020a110603040302031e0d1d0a03031509020d05100f1206180f 68
    0x2683e505205968a90059424100250400d03000d594146100c207400f07849606090104158500703402c9084c441000001e450b0500344514034081c40c0180303528188100e030350780c1e01410000c022040082c6020240180c42c2000c81a00e80c400c0300c4141129041310303904a00c084c01442c22421071240da400141a8803c4109102820034168003d203110308010004100b0b65007414240304c1d800e0002c54000d030105880901c465006405940240130701c6500620000300c02c0002d0743c030500401b980034141400044124851400c1243c200601b07500b00c0c40c140000c10362004030790f841060700c010030b01c0428040d80010001c10704150082050701c528190200304000c50780001d070030300d4143d0b4010071240702c4050b00300030805660302c020100c1c08407480e007650007078103031600c050720164040d11711a5108002d2030388452000800d9081440a4800101c001101040605041c2c80d4542d007800c4a802c441100010000200041c8202284c015480b50303110314045100803600881d5540f0324001100908640324401d0764404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 894999028 1250 894997778 894997783
    0x3080f040c091d010f0b0a060c0804030b0103060e01240314151609141305060d080c070f05100906110a05070e190b090c0d150e16110601060e03030912 66
    0x3070310fa60900007040f214110042010503030b10040c4a01790070101b42001030195503c202908403046000b80081c2c0e01c1c2030f0344e907170385d1034014502603006a80807079031804103241a020a000d481300f50003207105142020700050485940e600b80620009010303200c0080c14201286007404200600000c0440300c0101e0718005805c40c080d14615090313040001c125030800b042940d0880780322600f0400c0600400f0342c18101c182c2c01c40c003d1101600c06a44401450b80900c0010f0320b60f0014a40e40000301d000e0100107103494080f01500e0b00641005100e82040c4000e801400c1e07000305001c00711400e52806400c4440d04a2125040c00d01020018000d40510340c0007260a07440990014010a100c00ca084c80c02c2d50a110540111400e002849501050080100c0d2030306082a010b0311410440081c001003900d90b002c61040030700c5255000311541c00c03048080001c040090030700000c080c41c40b802d12480d20f0300120841919040140038039414001400c910035504c0d103040042d1020940050100480b9070160509240d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 895000278 1250 894999028 894999071
    0x6020313060f120b01050c160504060801200717040e1e0702070303030b0118091d0d12091e0c0801230114060f0d0506011b03080f040c09 60
    0x12a08140e40800074005100300407a204080c42640c03203544502c0310ba0601c10241440c1d40d4043d040080600c4001c2c950301e0300740701031100014540c0140e0000e615040500c4103480e1103a00242d5903900d442d034185070203c0030060724001d10501c1183c1c0c0d03646581910b0076201c850008498058000c001140204582400c071316101c4c0214060031000552150540a992005004949070001030704414000c000103070003504201c032200f105040c001849644001c180b0695402c507400380362078540742d511038180c220841040300e850f07544400141c115107032179050180c0720420030007620500d10395600c084001d02c140b503009106100381d01c550040e0501d0b840d0801105c0e1076124091031400c2e52801441fa5040d4419400d80c440e0290300c103401e1038a17680707000280c0500004115045412100030000c0c540015003600c010038080210301c400050301d040a5000610b295075014680d642d0b03120200d18100801e4012500c0d550005800341c070407141e590740d450700301d8912015a10504540d802c1ca0a800f240d01444840e08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 895001528 1250 895000278 895000297
    0x303071a070306121110030e01110d06080307082b1b1107082d0106030812101215090b012303030f03010509070e030607050307030b040902010e01051b07060203 70
    0x38025251640c4c400001810b00342001003800d01c1c411100d4050b03050050380840720b11140d0800003107084281e0348503400e40711000d1502144807000180e40c804000c07144601c0d0081c2ca04100154105442503662090901ca0400030300610708840b42a001c00700c1c0d0300c44402102c0c00091500b4002014800380d80c0300004000c1105001042c0c6c01c00e010404e01c00000b071440111240d880040c46002c2542403203002c86042442d1412240308141c0c61112010424051880114424501281e6500e10319540ae85035000250602941c123030b20711010080c401900c2c1080e021640c002050040d900ca07500c642400610f45024020b001d880e9500000800f1800302c0d100002e031044540c00300b4041c920400c101030f1a841103c00d00d100f080d83c240010b04c807074104802903540c411542d080520f8861100000207150031400c4910000180c000010040419854021440c00c402d00f41ea003405039143e0740d80082c0c480e01c45004101d04104c03003c00c0d051310703415a0143d40546e480c1c5c19010744000d55103038103009480b0381c4520b644 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 895002778 1250 895001528 895001531
    0x50a0f11030616030e3d02040612050a1409070807060203130311010c201002010926040b0c0604050d171f0b1201060f170f060303071a0703 61
    0xa110840c2008500d45228410358079000f03000705802c900550080003403406020ba588a40f12540302185102c18800c900d85074061400f01d042181c00d41c0400c806080200180700301801070004010807a00054a0300021105900c080b5440c0e403a00b840c0d000030070aa00c124015803002d1414007242800201b144425144100e0907108481d80324181640c1d68810300c8400800044404802c1012074807034119401e07000c105150440750300b4003a403500b45081c1d40d4482c0c07200c98101540c03003038009480c0248420700001e1081c00240305019960311812000070b00d40001c140c45410f00d24070399100d42240001ca8014208440520b5111030302224083d0340e616080300c08494501c16280d5060416000d44044d250203001904001030341d0303a510701000240007203e540c0d00700c01c20044101042d907503200c10281c041d08011182c1c5024542c90004d000f07109804103426907040c04206e0110824001c030104504c0c0d88126402c003007003190340398030010a04d036214082018004c004240480c03807030b4030003880315580611144d540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 895004028 1250 895002778 895002803
    0x60e100b0a140a050d03032301150c0521130603450302030f0a02060709051909150e010308030a0f020405130b040603060612030305090c06030711010603050a0f 70
    0x410101e510b03440400340e0019156508200920344003c42080003403180c81c0108049040c1d0805840d9910348020300f4102c0c1040c0001441307090940110f15450262078034192120396816159581c407a030301c0300c6141e407010b084804c5c0140300c0810401140c4400300d41d890140b1020381e80c3c1c64000c0081c10484462030100c40300100385055400d8900501c0401c008046100c00410704807419a150703030441d414110b05500040c8040100705003624007405e410f02c1e16401420841c60300d98001041e1f2213168116a10440c9081100d020001107000041e042c0d03024242c0005029005403464454518594003007002e40d44070000100c1000074110155010b098240c0d0103101d0440f030140d101e01a03005600405800104c01601031b12031070380c5508064001c41029000146054032512000c0a036101600030324a058040600d030810150300d03105241c3d1100c2c05a0140500c1446100051010b02c4041e01c081c00300b0580c1d40c90b1030f10b0f1402c2903201c0401103601000301c5070014000c0c9040305200c900e15200b034460005012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 895005278 1250 895004028 895004039
    0x16020109290a0b031203100b0304060605100315060f050712050a1407020906090402061603031a030313050d0203120d09120806030a0314040e040b040b0105030a1e060e100b0a 76
    0x700f060304400180a030448182000302d40f034103500010842c803400c10030f0300400188440e07054021402503000310000b103a49800c150900281012031700d114010180303800c0e54000e00018054056050750818a01413503060340c0c009088440380100f01000e4103410051030403074625900603000b032001d5015a11010107103060102800054002d030140a50400c01c154002050341c43d00340d10556000d40f00421a171304001c00102185000c000d6510300303c0203e40c4da120106084600a1903448941c0c0c0e045004520740408441e102180310b1441c801c1c5800381207285490740441d9001d010401c10384286800075515a40d058800c5000741c207810100b66880404800c0d04000f1500ca00316030783c031941d030140c01001c800802d942d0440d030040e2660890038a1682c00e010118007007140611090189000e48c1008010342018200011502c0060340018440e6100c00242c0c000100070302010340020b440b0201000d500911814480e028001501e1214900e004402007050010311503404040c00d40801e0f1507024600c0d4850 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 895006528 1250 895005278 895005281
    0x70b0c12040618050307050705011803150902040b0d050a020a0906140d06060f06020106051309021011010f0509030a020706030605010c06020f07170715020403030816020109290a 78
    0x3488649100c14100003901045294001c0256540f51540710700ba4840261a92400d580114400700d440c2d0700105010402581d04c214000703000d003003100610054900d950f640f000c01e082041d40340303c036094484038820199511507100400c01c0c80c000d040c452a06106181081d140c001c4840d080b48941101c90022600d211380748a201d0030341340000040000490202c040114210201d5800c45115444181c0850200304180c0d00030000e0100381c001181c568103010820485210050007064014540345130342001d81d98903071a007010341030241411a40305500e454140c1c027500c0307500c0450342543e0400c824441c000800100820702c1101581c01d41c0c541d20340380c0c1400c41c180d83d050701c038860012300030120708008505c0d95402080c07200d86910b00e02e46021040d6072030032a010680880b041d0309a00105000040c0309401564074400e507000002189490304541e0090010080900300f070101da2481d1041c20007450003540304144050b000b8804400360102c0745500b50118030310700340d201840d01030180420340800d00c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 895007778 1250 895006528 895006537
    0xf01020306011b0f0512090102100209010207030f08040909030c02030d08151018080a0201110a1a130f06020a030b030a1205030c0d0c03020904140f1f0515070b0c 71
    0x50b554440b4225500c4a80c4980c4070000a0550350f1100141342ca80001e80100b0032140d404a091504c2c68944005900290500300d000b0052502d10780100000c00c4640c1e40424514103403580006201d403d40882d0400182c24007a50b000348035071601c0c2842003020305402c81c0c001c2c01c540384202d04503600380c020488215003200003980c20188540c01da4100d4041c9207440f00c0c03d501300c0f90451410425114030081e20810200b103d91082e52a0781000c1506801e41d42c1c4030402c552141c02e10300042c0750303913030f410b59894501f9001207607a4020b4040c4240400c845054801d50180843d4210400c00090b0b81c1d5801c0101c002e52000e44108042481c01d034642c400b9060100390312068940260b421f00410804410a5500ba031004201c0030302443c04100e000604131030361007045a21405540c006031980d01040601c0301f05c40300c90200e1260900707480200020012106800c0b40c1c8205000c0034880c02c0882c0b2036104540d545240c1009502803880490442c0340c48452000e81407150240400b0189521000e000f01c0c514400e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 895009028 1250 895007778 895007791
    0x1e0e1b0720120d12091e0b090604050d050f0405040219090518041b051804030f031404110303311205150601180306021306020106060c0303090f230f010203 68
    0x11001240c52400e00403011300c0440011000040350034485642d0300800b246941444120362080c01c8041020711010b03180c95a4080001c100801c11400e054035201c0c0e07640001410a0100040001c071f0f62514105501034a0081038083c1040d901c0d0748400c80d264540b10340810307031840050301e90680042c480c68181044c02525800c01c18031341064030383c0d031038000c800340801100401c140d490850000e86921074030b511013000c00c1c000481d0700c0380781020f180040104001d204070004041c02c16404000710035001c1081504103134424440c81183e846a00882d003140107900c1e00701c084040c0700c94181d0540c1c1c0101000082400741c000e6002555444000b030800720014610003404542c01501d141001c8204865030755005401414503880d4a07014142000e07181c501ea401c01c4400c02d4010464108540207030414801800182c0000c2c054a030909900618100800320003808150702e900b03100c001c0c0304034010400b0441c0d8100b8281925103510a4101406203032200841102c0d101d11074885011000c184241c900800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 895010278 1250 895009028 895009033
    0x50a0305071b0b0a1413060f020a140c1f020901180b0901050706020403020915180c1c020f07110a0b210411031509071e0e1b072012 58
    0x50b45840c1c2e98000321004080514041d0396035001c5c805103901080c0d0902c524400100748030b040103a490108142d0b000b00e685500c0b0380d0300500229208130b1700300176028203524076111134980b00c094108515151002049a032074041030219500c61020070241c008003603c030820780700c00002c074403030600c00f0050000c244102d40181409100510301e80d0301c218010083c4901920015041c07a40701d40010b03401c1142a14034240c1004440c1d0402c1320b03424808000710040c0c1d90f00da2400b4891400003101e060a00c9040c2841c0e5000c0344506d604a55002d80d5815100301403052030626803105e482d881d1800558168a8400744a05100580003400c441510222010490001c240d0503c8029444c0c000745d0042026000310780c200990482625191030404c00c1440031014400c5a46041c1017407040b00d0b040c6080780c4c0000c00101c240d4401386680c03e8449403640100e030007806070400943d45640e1a150905c1444c1c000c0e81400d18009805001e000350040390004001410105000d810b091780308109200d40680f40350380464 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 895011528 1250 895010278 895010327
    0x16060e071a041a09060f0a03060905090c01090509061306030c0306110f040501030f0b0310051005030703030e0607030318051501090b130c0216030b04050705010201020c0615130c050a030507 83
    0x64403c40a05500c2c44054141ca04022940d904035045800400201001a07540e0004200c007002c18000c103600240f512016246480e4240c000900440c414000c2038081c0c422074010030100d4460316a400300030000c2020030402c064891610303820007049031105640c0a410f000c0145070038169402115440402c24140c01e185c0383c641001500988580c1c0745100c170761642c40252030200c0d20203100a0800c0406510000356a10303000400d030700800b165800c6940070b58001281480000e0f000401c03050800360449400f83c541007e850110090500c000c80c00c9060345581e00e42004008000600c9680c2c00030790300005800d03a03240e9042d002152a40b1100581c84000300000041194a40c1c0c40510801418415555818000c2d101d403d96031025074400c54603004004c04120921009011003406010f00b440254a0640c06440c1180c1c4c40002401c1848481d0840004400554035200c120511090a04003803003548525400039002d60480580303140171034180303000284018403603901000d11f031207025040c0c21311 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 895012778 1250 895011528 895011569
    0xa050315010f1b02041103090a03030e0c0609010c050c030d020a030e0d0305070602070311071409010e01060903080a09030221010e070608180a15060501021009050d030216060e071a04 80
    0xf21810303001c0c1c0c3c0281d03407001031312030b001d002200961207180365400500d190a07552030002e04461401d1a5440036411041650171150780b4074040b201700f41801d2034400304540150810509048940c2c48055042c0710f650342380660503070041006c890040c0240c664403851446d2001b80401040a80c4006001035810840d00000403030783d60142c03a03114009c4c5050411414146002d40c54400e0740e401c070640c4c080c031440b40c1c290540b0b01302c00b11038050b1400e02e86100300c039450020084c0003040c0c5804020b2441c4004100d04100720b110303042c800c00460b001090b01c0b280e002c00085c05d105540c1e03022100450740d401c020fa00d010f0003400180d24002c6039260358404085070707614030308900d06d00c680c1c02142c0218080d902001c80032420080e903207400301c0d00c2c200b070004049260400180c50121401310051545003404c2c0c2c0380c0041440800c0000c890203d0381409682c8001c054082d820101d8941c0340106000d1504101d8810440c3c00915082a100312002401084801005c5490709000302d2050000b0341d04040c072107448 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 895014028 1250 895012778 895012817
    0x303211401120323031603150501051e0f0322120e03071806080c1005040608041e0605090d0309050703060b011106090105071b1109060f04020a050315010f 68
    0x1543c0649840084001249080000442e43c0d480e6070402c08404030601000e844420600d03503800c3c0c450708041000d65040e015410b0a00e10510555050102c04141c0018111000300d141040110700c4c0c1c1ca0701c1d03441d04041c0c000c009681043c2c40000214002c0b030360400034500129968000150045903011519004c0e02040341d500c01403452054050080d480c000442c00300c40c030030704007003144403041c007062040c00c05209600c2c02c6404600c0034400e00d0280e185c1e6051641080484003940c0491810042c290349a0403c10310308462414900c1c81020078503d02000c2c840070741d005600036000700c81654030503400e100e0220161030b445503000c3c2c440cae0884030040002842c3d0745d0188142c0d41060500a6082c420308280e10f04100040b034071500165101c504019150b54000d955125030418107446142d01441500d9170700c50300320350440d0140103480d207102107052540d960f01060000341e001403080d5a03078205031500401030303001030f20b02c90302c040d6800c4031039240b541c0551604099041103031340c0e8404800c0f00b84607010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 895015278 1250 895014028 895014059
    0x7030c0b0304020306240d0f0204050f0f0a1a060c010f0b19050d061803051e030c2a0f0325050c090a0b060301060f08060915040b03010b04060303211401 67
    0x2606d40304584152500c9440e8500c0c01310b205400f41c2c0743d00111a07418018002500e1000307101c045201210b40030000c199803985507030f0b0382060400e4000142080302d291360031081d1004040310b0b54043c001240b02d5079400415081201c020100e254280305140c400800e000d4064008007540c5c003000e0700001c0034096802c121982c43c0c0550700424010030308082d50301500703083d800186d030705174001200010002c190904c001140c0b07008480d00076055140d85001c142190480c00740c8002600c0040c23000300e000d00611207406990030f01c0001001a648041c0c440040280c3d07a9015035601c0c0450b4541c0440b0a2441d1055202da20b0503903007040c068409140d281040202c1050300402d200e0002d650b44ca48100e2a07161400918060641502d444c410300380201c0003c0c00f0844000e01c958804c01c641001c21443d071000455080c41048140c4001c1201c038203450000340035000400409170403034644400001071603446480d00c0303403403072007041185e4003a102d42612000395485a8046070104c0084001000140e400c1c00005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 895016528 1250 895015278 895015321
    0x4120215060108180a0f031106130206070f03270f050a050f0d080706060b0306011d0315061507080307081e011a040e0702070e2215061707030c0b0304020306 69
    0x200c00b2205d00340e03200200c4900d0400d043d030004800c00ca040f908511704114a42d003107103500c40030b400c211220794005103051044050051000400c030f020a0201401141c5400804075035807402010103070815034141d05166103114040d000554440d00180c5810195415000d650000c0e003010320504500c1c081c0110384940e440100d440040801409012410314454100540040601130781e0301e04040c030004203d2220715010080c612041160300c42c56a9000504c0401d8405058000d03c480da03c0302c00081c0c00c420084003046050700b00003008420060000c00461003100c2d103846e07443c1d00e41c4070707540c4c2c6c18655000f01c4800c00000204070018001650b11040c0c0c804440400c00c20245010745071207031301d41d4100058840d40050303403042005011452501000c0303544001200c0701c00d091580b9824034032040c040400000740c41240c0e5001c0784a2024020741010010702035800d41e0701911041042c0441d40c0380400e10054903016a0390b030021961a110700101c0740625001070040c5100d450b801040f0341d00744400c4c2d022 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 895017778 1250 895016528 895016533
    0x1b060a0506010201062c1510090602010c140d0507021903090302121606080a06030c0815013f0f0308070210050f0a180c0603090605130507030b09070e0412021506010818 74
    0x410007230f0703640011080e00c010f83c0c0c1e43e0b406040c91404070301a0039176000e031062809019661140007407001c00d9909485520103052000310305611800416428012010002c080d0004000b0450b400d041d00402c03980122482030b10010142c0c007003074815680300c40c0ea10b0303800780c1351000d906020400340d40300e00c0d04250450030600c00040c600c0e07940e81d2840d481406a511600c0e03250052041c07038004040c3c0d40b0580e070040c802d011800c0143c12401c0b070010b501510582c95490107005918000c4000c20318908180e01c840d0b40300001049851141c103003d8500300c400c40d410401442040c1b032840f400c130141d0060a018018001c5403100589559481c0000341c1801001030b1004840c205580c1c0108a2840e0100002d03c85620009001d21507400c0040640b48010161098103034240c80180004200094104c11280c002214241c9604c5648605003000e510f640703c410418180030500c424407040042140000060381c08031403002020b0360503034002000c1115107a01007103201d400502e0003840114610350403a140000e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 895019028 1250 895017778 895017811
    0x4181406060603071d130f0f061505070503120a1d0102090d1403090a0f05150c0a020f0a0f23031b010807050c0105090309040b0d0f03051b060a0506010201062c 70
    0x4200344545982080031800d451f2080740c0e06080c118803e8120b8580904401d0041c05e040602541c0303146011481c6104200700000c120051100602c01e44040100c03a0401c48401e0500d4083c540190025a00352241061940c20840116005200310381407080050241211f0140035120383c0e110428036900c4011500007001620440e640382071040380a089208444107081d42000c0038062139000c0d0740c944030400c0340204000304c0c1e03040300003511310390b843c0e07045801d01c115901520211310080c010381d00040010600039400f080608001d00540808070f020800741141d43d034800d0805641752840410b40188031101d500342009548030740c4c0c00a1380991513040091400c07084100781c0d400c4880403200c1c01466000414055503601d014061981c800c5000c4490030003107241d54a402040c08004580141400310000341c49400340d0084100308200801c0c10151415441e10515440c0a424122003040c01075103004e40c0032170114010b82603800703200564116828518002e658100c40c2d030b04003412280e41280d4900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 895020278 1250 895019028 895019087
    0x70b040506010f0b040303020318040e15150913061d03070b0603070e040c06030e100e03030609010906120230030403030f031103150f0418140606060307 67
    0x1010900a9115800030312241d89024907aa448800640190b503419070b04001c10004a54000107a5a00340b03800380c0d000204072048000031740189220351078010240180340306c1401d40700040d05140e1050400007000c0500c0c124400401058002c01c541a00c1d4505582c0c1100000c20001d44c404154500f42201100800c040c403803010307142d40c0201c0002c585480c4184100003940c01c3c1405180c008004403010354616003845e07960121150721038080d1204256940014040d102010054443c1d40c0002030b104100000c0c0c001003441e183c3c0c0c4110b8020380155080400082c0c2e6060038807611017102c540d80d080d5104101c1981c20400400c1a0803000c00713601e41e03c40c1c48008400407a0000366848203008005560780c61071803038080c0490300e07141010000d042ca08140e101c00078442c0c0b0100c991040501181e81000c1c00800d0010700200d1031054110340280c5001040c11a0380c155114684400b400f407405807400741c460b404004e0380c401e01240d0f07a42e0088818004110044d0184483c501d00700b0b50124880b94000303500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 895021528 1250 895020278 895020293
    0x210304150501090b030c060711010809192d0309060e0612010f030302100e07030201050906191d120c0103110408010e1e1902101119121b020907030207 66
    0xa0b00f20701143d560300c1203d030320585000c20001004040940c2c4150514605880f02841c14255410580c180708841000518060040c040c4211044448192010f1214130342801205c810312011744180400e4090440790403080035004224100390f16640e040005810241c1c215640001d21b1101504954140f0803400f41148114002e4003030b100344001c0704041031550400a14110188000f080390a20304400c4a03002c038004203010782034940a0030300c59962000750010480d6442921944691030054000b03403032225034050032840c500300d0b407180c852141d1014032080210149203401d10314016481011000660b50003500f1400940c90b001407010b040c19075a1000c2402e4840340c1e00004c1c419008050b02240702102000801c0e0042804402411860034142c0344002d24003c800b400fa20031089110b54440143c410b101181541c0740101c00d41d07103030f020400301064078103d1614088851600000f80040201c2c03090462a9000351001403000300500c1d03030340901c00854000340c80380c410150200601000300701c88 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 895022778 1250 895021528 895021531
    0x22b021302130605030103080306100c120e211f0207050d0509040f0216060e0325210207092412110906031b0a150504060906022103041505 61
    0x40620160ba541c4012150b190501d400d40c100c40305000c8184014404245c0070000ea95001400b130380c0f030f07400c4100e420704155040e408010005080e0380305003600b202c40c99030069106403490303001c0d148070a980c1c4109c48480b890a1250380c0e44a2541d000211002c00640b0340b400f40c42520000790401846d1220f2034603690304000124401c2800308200180c4402c3d503013002d2103040c0d521180b0141c11814460000031121244c3c80380240900b080b0b840e00852440c0c0c0c1d105004980325910340950031440c0910200da80710b024600440d05480c064841501088400803501300903180100690181c40c4050405c440c3e03800030701c1030030160107942d06900c004005c07080743c42a50b07030040c1120030303941c022808040c0703408a80040105120b900501181042c007581e6140050101000200310342c0c00764011414002080101515900203da100c111200c41c00c0309a030404010429540ca9a6623917120fa9110501a03135582440711a0001006c0540401001140e800b0080c54009218018031195000320010311000c0e00c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 895024028 1250 895022778 895022809
    0x509131115040b1e070c06080a060503011e0e0601050a061b05030a080402120106050108060d11040609050610020a0b0c030a18050708010f0501120b0c21040201110a022b02 75
    0xc00075921024181e400240600c00015084052401c0e94a66400d1170b01c1d0000c7c4038500c14440800d001c20b80a010f11340045000d084041d000300880001d442019a81e004501a0f0786c211901d4854840f00b01000410070a060350000b0b403051000c0b514080c801c403004a00141d00c0c121880414094400150040c001000c0352107080c1c3c0da802c0c10303040900410000740fa1218052440e40e140041c1009280d81124000303610860441d141040c00c41d1a080240e0001198911030354041e01d000e80211310b1140c16803183e8041c2c60203480c944070499081c0d00503a51110321101c050540140c4100080c60001d540004541c000403201d800b00f0900317504a07155030004d00554045400d50005141481091024403840d80760105240b4140880c0d4504407041c00301700e0600601034040824000002c900a00300c0c0111080000d45880f440c4000c1850550340d24146425030b82207000880c0340354507000c80140000d0041903150010030300c0c00040780301d0540e0034411052200b544003903081905c1036801741e0303500d00c850948080c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 895025278 1250 895024028 895024049
    0x20703081006021f050a02090303070b01170307110405270d02010c021603021c0539130f20180a0f150903060203040807050601050913111504 62
    0x41c495415800a5050b401503011035010100e03180807007401c91400c03d410b0b440040001a243c59100c0000060303c03807040c00f107400d44000140c940c100460f05552504075900310307039000411800308140ba82c42c0d2040b01c0c00030f040c003498030040c44c1c1546440da1010750080041c0b15400514501c04558411500c903070610181d19802584421a0140e028001c0c075000800e584058000d02c10019098130481c0a01d0201900a260450040c04c07840802c1b0350408403103400c4011070b80200000003692a0106049207044448011007403012882d010f03408400c100c15100410000a4901c000d40c1000201004010004241d0300d1309820711200120741c0940280c16242c0285513a9603512130440031005942e1164540100c072000406c210783d6012541d200d0030f848001040d410b010454442c1203e034000b281d040074040e04d1002090001300604d240003800c080b8496000e582a50382c0e50010004110360884001410004980802e00064228030644000160041060b80582c0c4881e8550a15030050b400180400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 895026528 1250 895025278 895025281
    0x32d01031a090303160c05030705031314150403020f0f1f090e0f0f04030908070f050405070206010b030c131503060503070e0c0d0f0915051e15010e01020f0102070308 73
    0x1c115504581d900c000680c00551031814444a07010244030280d00c1c00c0c0c00c2101360b0b00caa0042007c00d02c12103404c150480c00300c07a1100d441c60300c917072040002846040300c2815402e0307452020782042034099180702c0d0085440b43c1007500e5074080c003050003d0300c0c50040c0e2002200c2104581507031440e201b87e0100340e0384dc039881404100c03140040c00002c181c0e00007001040154042050205101040070f40c0450804180c0003962110318058400740880e412904260003211004920b0400d4a0300c884100c0304225410b00013074850034811b91710341c8001e004440101e041000007901150035407008042c0b0300710840c001f105550b9900603141641d0f446550800000f51a40400c1046180412464018203007040075040b460600070040344507413040d00c00c00b00300b25850741c00c0340101d440a9842011555000b1042500b119039080c0f4141c001c0c80b00304c6507401104184403203d95520391102c18140728901441d036172100320741e00100540d130f807004640790a0f04500c524000d0486201d028005881c40038030a4a49002c039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 895027778 1250 895026528 895026563
    0x100e01140402270f04060f210c030f06110a022d0106091d0615010e010903050d020114010b250602040b040b0306150a02060a11162303070305032d0103 66
    0x9400510482c81d120b0f030b04110003400082010f00c8030104444001c24103902c01c40da2811021908808c026001d032100c2c50030f131000814800401080407400e8490082040349446841610490f8003510000500503440b07440320500d01c0d072611010401c0940001101c0b4040f02c00c4204203800e41e10309810480307a494840309908940c1d4401000d849003961036101412403840c04801800c800c44400080a04001c4c18464001c01a4001c5620f80c006c0c2d034000090b10f400241d0210042e019045010701070880c0000302d400002c604100d44c080e0f40480d1080f1014000c04100081417002c800907008060750010b90806c0001101442e4100500c000c201008402e6240d207803450401c10751001100c1d0408113804200040d00e41250302081c5907502c181981c000141a440000c1310360380c0c60003996200d4100b0800c03000ca42c1d042c0301c280703101c0440700036010101c8070140c01030407070081d00c9002d81c02000740800c5080c000325645808142d0a5845000c2401c0110304805640e0100c0c9540c02082c2c0c415255000c1e5904101c51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 895029028 1250 895027778 895027789
    0xa0c0219270c0201020f07060b04060e09032109070603020f0d02030103030903053706110c0c030c1801032d0c060e09010302130e03190215100e0114040227 68
    0x145403643c002141054040e1103450b1803031003161402400c1540e9410301000640d5168440000b030b1404c00300c004441e20700f410307c0958a03805200340d00d01d0050340410852803202d50070412440740e1345400c050541546800e00c150080d4000319a4924410300a0221281903049840550f000314000c1e550002d0992441c1000b50901004c1a0720b905600e88135110340c100b8449180048024054010704001601d8290500a00a01502e42c0d107805005000410b82c1c20940002441d500030b00049041c1c0740843d42c0c1c2ca003041864000c00c040e8010042480c00108082214030030003070350610030201c558141030143d8022114026074418110742e8107204040901495901000b04986100f043e07400c2d9a0fa9411500081c0348014440703800d400b401d071203c924540c203800c240150327828282e0180c21a1350a0706020000303034844410040c40541c0100c041c001521301440c3d160114200c0fa000103103180c0c96403c044d00182c85014111125802c103400f00b221040f0050582c640b005840b4030014000c2220b01034404210 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 895030278 1250 895029028 895029041
    0xd15050c09131103162c130209030d051b100c17100915090e0109050d39080705010e0105010602010608070e040303090c06021b060a0c021927 62
    0x365146024400ba2600f40c400301200d400c0829500c440004c510114401c9540c1c40c000402c00401240074003900806010031001c40b125031008079a0703420311640821138041280251044154150f2010100030f134200d0144000301b5004402824041c03a983d8000300c0149810810381807488480d40d50503e11200c41d501985481040c50b0b01003440301c3c14207140c2500704c5107030340c075003d0705192565480c902030701c1a2501300054000c0a0a100c244800c4104040490082c03d84103420340301ca0044100c1101f007039100d00c0c4001d0140190030030803804000c0d41745080300c1c00c0c0141c60110054102900702e03000850020400b520b4940d20403000851a10b03040710029081d02d4060b84400250fa04081c400c6c000d0080104541090390a002005411555182403c801034103441201502d1100000c0340811450b80c00314140707602200b0402070840c1c4c03580c02c5040c0700740381c81015248000904005a02001850009000050701240f240440707801520780704014510f4440d40100b5a1181d41d05410070120ba00502986 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 895031528 1250 895030278 895030309
    0x90f04050309150c1605030d030c1b050102070b1612020a03060315020c010c090807140301060902130806010f030804060503060f210f030708120a18080406110604030e0d15050c09 78
    0x17001d0185003001180c2d8649030003e0400506031964407080c1c88510038201100c10600d0118280400707801400c0140c000c1d40582410f9916041000015007095100c00d501d0711000450382d541810b2001300c000100080d04501e1528003016114000003000c20b0a2012603181c901c440ea0b00141e81d0400c041c4901d08445003007a504050000c000800c0250710004103582d402c4600d91400f0310011444640081d00401180d0042902d407803000c510072214881d04043e4206513900d44044034030903600c1d25226481c01566200017420130070304000500c51948943c024641000000d05101da001c4d05100008402000f000f10002e01040f6070f5181c07a180c51420003040a002e000a40510b1504000d6110601103219943c0c22541034007207200458424003082d40000c0ea85443c5082c504c490030104e10340581d10743d00034030401001810001d440665a600030981038002d0382d0680b600d28034581600c00384602003208038400d4580e0070045140138289000b0380103451080180d84085a40d48401c00104070803a010105503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 895032778 1250 895031528 895031563
    0x30c0914070e06180d0c030c1a0702060702033f03060a03060e100501060206070e1804060b12100605120601031a190c0e030f0c090f04050309150c 64
    0x18002015000b01c840c024018060303600da65500d2a181601c00c40700c6060300b5058110044804403411700c20b42452407000d5034070444c1d8078500c00350f0b100d00e10745400c800c88800c445541804c2051400501c0c050005101c10b510213015034803461460515000c203035004829014282270a00f080007102100c03081300411166580d42d4840c210b003800e0000c515003640300d0000404065031021422998441048101c00e0b550140800340203a68503090700035114401a191600440c5000500d9440c07071518090320691488041c000000580c0c0ea911010041d0140e214200e40200c21040403a2002e42d00340141030800400303c00c04510145408107001458032801005402508000300600c00555444c4800d80e80075001c00145444c2e440d01800d501208085440207030080f40303020240000c503600641100810380c0700303c00341c84611800e060000c2e154010124801e80c030040e0103000031000046500000d8000d8041d07000c403400e007862840070410700c0c00200d20106030140042800041040100000a2401040f105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 895034028 1250 895032778 895032781
    0xd0e011e090512191203200703031d1204052e0f0210050108060411040510121109281505090901141006030f05270a0c030c0914 56
    0x10101c01403800b5451255810314001043c1c55410090440600101d080d0340a441c1600d01d400040d0b100f8410808012a04202e285c88280c02e00b094010f0f280020101d4407850003e90380c2d4228000c1903024081c0e40c0c0389040d1040030050040c1040094000d0800d42151951641850b041117450315404d02950800c42603040c202c1c4242215441031400b2501e9414a01d40000000a080e07083c102c10325076041c125032501c80001214080001c4c25805a03000301400448801c203601800166a000c0b585c1000808100e0020010516500b10100206000d0840c40c40140700c1e80000a0780c88070140c03607405c13000b41000c51f008061000f20075114007040c44907004000b89052184903004c440080c0c0301380d901c12540c010000b144a102904491010072616006010520b072010552251081d02c1c00341000182c43c0001e105d056030264402c0d40c0c090b0f08240d40303003ca003030301134650440d1052102c00c202c40b56000d481580f00020b0402702c0c03268042c6116007000c4207640d05161000301214a18040c1802c400541d10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 895035278 1250 895034028 895034087
    0xc020309010c150203040803190e07060e030a050a06020301230108010506300a152102130c051c05070905010e12030c0c04140903190e030d0e01 63
    0x1200c031040350a007407106001d090750900030044400c401441c114240004200002c01c010740f4000c5d40b007500c94100403000f040410b0052011501c082900c1041c03a44540000c1c1b0030b05003d0080e642420700300a080350980c0805682d424241660881c0440d481d0f5000720041c0442c99080102215190b401203618000e000d800000030808038041c41801d00603900000d0a41102510b00144c8080a400c40e500d10060b032441c4242c1030f0340c05012070b003000c10035140c102e40245a2295507904c10840d6403200030f410300c078469250502c03a800720301038080768058100a6103148100f118010242010510340341d4941f1644590005980c4950041341f0614140c0703000c0800c07800d1500511000e003515000e18001c403880c409040451a0b004c0080840c48c9544008206030300c041000050b0514049000c0c0c9050150108000e00400301700300541d00b640003038000780424050540d20040f04c2010005d14548180300c50160303004241051300c840803480026482d201c0d08805540c001c0c1d1059800d820702296092032107000c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 895036528 1250 895035278 895035283
    0x2030a0f02010906051903021b0d0e01030f140a0b01180f060e01080403120504050f0f0106170d080c0c1005070c06060e0c0f0f0d02040f140402040e0402061b060108030a02010e010c02 80
    0x20300b90401f49035020640744810041d10030319040907504a81207580e440e00314a000fa1450a090302c1040c002404c103801c50401156500440c2d08851950110b81101c0e1500403185010f0080106864100905500c08100c1c000d01000048014810240e01c16205c0b030500074001d20117685981202d061100c41814000003035884661115146d030f00c104005400d450328606241000c2d00c0c3c0c49030340502d2142103001c211039501940140110303140c0350400301e40d2090916050391119140c020030070125020100080811216400501d111383c011001c1e0f0781c021080c0c116070411582c0554944c0c00040c0344031003180c01c102d0b082c82040040d0400d452444428581300d0140b54003480b44000c0284540700c00702d192080300c1d440b20b003642e8951801500541d102c5481304003002c0c00c6103081c803030240341c140564188091820180300311400d0b01c0300851011003d039a25000d010440c0d1107090090088508040c0d50807002c0c609000c0d05018111281c095951812150f100a00791012000039580c2079242105a8181d503800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 895037778 1250 895036528 895036567
    0x50303091c150f0e0c0301090203120a090e0c030a0b0d05060601050901110102030f040c0b03040f1112072408010e040210170c0a0801080c0a03080f0702030a0f0201090605 75
    0x4800c11001d4400e103800700c1ca440e00c0411005855042a0b050009004650011900c03c90340c0411910441c400104040c00d031034283c840a50150450301040d100346c00883d004202d52129401c000003e56501c0c0300314050184101e80c0c281c0020404010310000141500481c0e001440481d00359800e000f460300c40a84801010340101d06020f000518501d82d6405205500007070003481008640342d1400d48854070000ea07080300c041710a004c2d4480c2c0410240b1000301524025500608010b0300d03d54150b6030028010f00e00340281c3d070701030445d0300d000d0341c059010080c00001e02184082a41d0b10f200e4021456a001d41e070016410902c242080144002c0f0880100385038050340466002d41501603e0302e040e11a11051155800c404840604101e004001d01c0d004000010300d0b541c03050502e0b80d86862075900da0010070455544465910000c0011076207410180c580600880a42450034a2a034002440e21400c00c00840344608441004019580c02c540e402c00103203643d05102e86082d40f060100004600b5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 895039028 1250 895037778 895037809
    0x411030f27071d0c040602030306190e041b21170c0f03120f0c0714010204090f141006050703030c3e03090d02090901140103140705030309 61
    0x4100c9441c01240c400340000304031100c5914203440d42d10b41c40b1080e10754080005481e01c1c4042a000b808a8158404402250221440381e406141551245410004d50843d02d40500c00007074400000820404140f194641c0510710600700c01c189480c03c0d0bc0081e5445400744c0c406404110059990710b000d95a042003c0311965001041c01800d0342444104170340d40c0a18020916244242d42c4401c210303140010090039103444542c40140300d41d58651740c50600003070440b1040030000302441460002901740342c41000b070155000001d0b040036150095901215008000d58000136141c0d81710b030408801102c00c0380d8020881345148a20b440c1490b0024200e8880d94000904140d079510401c03145c60301c030f49022104c4030698681300c04190b1610107008005d01c40c5403202010001d01c400c5504071524004221540503002402d54140200d00307408102421500130004c041303079501c800042c00c104c60700251f00c5010318440d042d00200e09040c0c4c510185411082c0d0040d900a90003084005000e40d0b81c111880791052 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 895040278 1250 895039028 895039051
    0x11090f060322080706050f060a0e0901090503270603090d05030a02070204020f0a0e040c02210c01060923060f0409080c0a0b090f151501050f070803060411030f 70
    0x4a0b24142c0402c01e003502074400d8000d800c40d0000604001100c4000d03d8224002d50f07050000c2d8442c5000b44000c0c03401543c0f50350784000310b103800308026010070030010b40c004d0340c6200000f20075204d82c60301ca007542e01c210102c1e1424074801e00c0c01c00040c0800c00d02d54000038400c0e5103081c1940780100e401da9560190f04540818480301000141c1d0660494040b110304580c09003041d91904810324804405800c07141c0000c005c07489242d000701050502d0321900c1800c01c619030082441089102034a0101c0c03a0300c001c44d003140201001a8510544240a01002480386003400640d80347c80812451103414144120030080a8001c1031203801c3c0e60b0b0b1454229061421600000c440c0000d2818001500c500c10015019000d0512460f00348040200311034895600001554000c2c2c0440c2e405507180d03241d00b19800c80c0e00000c0004569069608465180d42e0041070500c03d1509400c00c02a0040c3c0c1c11603081111071075000400c018090401d03000b4040c061a61010382419810410051310031142c0c000c1054182a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 895041528 1250 895040278 895040281
    0xb09060c0a120c03090b03042109030501050f1f0f09020f090907110111070f0602030405070b1606060e13151e0501080f0309100c050a0b070e030111090f0603 69
    0x400c0c05104802060703510507000c0c6648840c10720003410a40a200b0241d000c1203010900091400c0961300b182e101d5a400182c00701ca540f041d00e1200010b054a56010041003403800020001030f400340304140c0148041a0388584c1840e03c0380c401e130f0210082d4402803803442e50540d41000003214004100003030b10000b07000540c940180e06080c141500800b0940c980c012901d000b4401d00c035401003103062400f00c00a0090100386034012141600d4812908010510b44100d01a100451080ea002e942c02611903000c0e1602690f4a110701c054a420084880c600210101a4581044030364460350004020101c0021403520f08503085425820820001030541340002c4210000d002c0d06600c403580c210103072401e80c42e0b0003802a031100300804003401401024800c14042c90703030590b400000d03030f00100c000500e070400d8001c14030b01c00c6031110514042111280300e01d50350b20001583c9007a1041c4584080c0c1d03152640740e0000c400701800d403011340310a0004c0a0040101d00c4598403020041c401c1c000094034031a589 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 895042778 1250 895041528 895041547
    0x1403010606361721040e04020a09060305150a05040803040609050c1002011a030c060304021507120e18010803030a110f070c0e1005060319390201060b0906 68
    0x120240d8911022015604850100f04501e00d04000744070003100c8001c03104001038a0580102944000841c103600b2401408104251407046900581c450301c003900c9100c80955a00070a403d498060f00304592a42042207030f01d04c841b000707100003540092811018000341c103094540f995584005040134000c240c0314a101c0e02400010000360a600c0700c0138000300095a98601d00900030581a48814500884c40010809514001400340c10841c4001d000f240b81d0b4556070708201000001c844048135a020501c0075a01054040d070103805150b115840d140c41e140102410040c1c480c1a15003040755421440700140b00c0c1510010559603c12401d45000030f181c05c00300a00b9003680a0540780d030303a200100091002c1040018101001201c4030724480711005c1c1c40c1d6040341382c04144076004d460b0b000041440011a0001420240a4180250400000c0c4a503141501c80510000c4140c02c02c2000c240641440d82c081e103e0301d213106041035610003045014140964100a8464801524855070f00461101746 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 895044028 1250 895042778 895042847
    0x406170703020c15090d021522080d0609050a1404060c02070b0d09050c030f030702131e09021507031e050c0d0201051b09131d0f071403010606 63
    0x1e2070f04688040742c03031840f04090450110380040702c000181e4090014a48822800010030300102214600203009940c0d50328098581c41040e030034034803298184085094089150b0800401c1081c00c1014041817050600320150290745000d8003025884d89001c0018580d00b84041c41290080e07489280030400e03c449520480c034025241d0880d02d0a0480080c803103803440d40503845003000728414000d460010301c607074007050b4407103034004609880c940041103884014036020651806a2800410020381c80350078002c100e204071004042030700080c1e03441403040150700d04406503c6c100c0300d8500d40c807440d00c03125a1f0002c00c650160b40b40c07248200300f0410400c803080d00031020780b04941c050b01c0464010100c0303001d000780640802d440742d1200c10010104035440784250022140c440b1300c0940a2911108a00d480400030701485a168a000d41901c200800950050015451592650005101190801c44200e400e02c0c420300400e44a81c0c5010410411950000c010181c103c0140c2482d1283c01c44990341c203607 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 895045278 1250 895044028 895044037
    0x11061b16300516140a14010f120f020a0309170406170a0f05070807090605040308030c180a0f0519081e011404061b08010f0527010e011703040617070302 67
    0x1104629084008035248401e0441c0e18a415002c1700c1c1602402d07910b86c6c0d08030120300b1460740c850002d107003813070300c031904c2d500840702a030b4044c0c48000d000601d101e03221902c0702240c000c1c09910001a40b0340b0781400600890814450019000780e40140c501443c101c0043d06c40107500d07203400c5056000d0b80c0064040c1c0400c1e805494940503501d014021481e003000700406400c412a519004503901603404502d81d8410419075050301c2e8000714861035034a0303421104181d6081448211425940340e0f145d20303616143c42c0891030040050710b90707030b1001604080c20480c403a40c05084508000d50140310800c0010300029070382180d00808020103100142940040380903008540c1e0021500071540140b108118069009801951f100d0b002c181240019a80c100c940e01800c1c0b007075103000550800c1c180074910740708580e000c0f0b6100c1c0040d41c040e403400000c011750040100740e004100c0c90304100700401080d000800c0c140214041400610324190918038040c24440b02d4000e6101d20003241400602c5142c001c3e4100c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 895046528 1250 895045278 895045303
    0x11404021002070f1a07050a0b1f0b0706052a0408010609181e0b0c040509070206071224140109050d0803070e0103060803030a320411061b163005 64
    0x5d84040c540d6091000c276001c02070311400c64898421200f06544a00c11401e03005881da201c078510300e00210350312004d014207400740c40300c04501121206802d034080c1d094410412580c203da007564485240110642c00c50f240307540860002424041c488083c510310b403651030006640040542d5103218040c10358011821041ca0003850004450306200000c00750801520803254200e4000e4a195114581282c543d40142d400350040fa100d0b44104ad610300042c1c1005003c802c1c40c00c1215500e0090604c0017201c40030030b0b8803200003407111011210b0320f0b50303204a10b500607060585003e50744220700c1c2c0d11030003603100040440d400c0069081a80220703a11a0308910000c0140c0c00440f0748074101554410000d01c061155100c040d003441c0c0c181041000003410740344040a01071070480e80b039070f00c9848074447c5000380300748168001c2d0204143d806a810b203c080090f00200040103001149620b24180103120712074100704000ca00c03c0168010350724000402e10644200c00814240010241c60003610b80142107007030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 895047778 1250 895046528 895046533
    0xd03021e0c1908060a02070209040b1909060204030606080a3f030b0a1a12130807050708070902070c140a0302060d0f06090e0312090f011404021002070f1a0705 70
    0xb02d01c1040c900d074408100351070b10740b000d8461980321440c0d404124810381d00000d4011600000050214088160300342e0301200b0ba0600c0d08030360030445a400111405900d0450704182d01181c10300600c00e040c402c60014140c80c80040103841720944416295900c6d8079800c811710842000c40944411800c000c207080e550079a01c419001c1075034001c0180140c40e4015085009850b5420002040118443c0c0703c1c1c00c000440008914107024001c00d01c01200c802054103480151120114001440610003001903d00420203045441e0a041c691400d0074182c1d0300000199005000e0f80c408107544254090440b07120380107070080c40da000d00c00302d0349506140d070001c0d46c45030010580e074280301d00d15007141031400714541c070410804d51245c1088040b180c1c0f040106219074824043d85801484c5803a4182c3c00203594021908180040741c0e01d6429a101c0300031250745404407905210860400d80d01d40b0710b41c000240042c00000b4104010348240c0704162003840099030040d26a400f543c58010b088410442e0400203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 895049028 1250 895047778 895047799
    0x50d020907020a0f0f060c0c03090506090109050d0c080f0a031b0f060c0201020904150f0b09011403191406090f07050d02190e01140f0d0b131a0d03021e0c 68
    0x14445c00c1003000610941d0541e0400d80c25030f0b04180710315941d2982560546406003c0746c105410b12405802031081c1070b045c08160b481c007142c1c5554082903070510b188210303111440d007410440c07802d06107116246501903580c4082d010000090300001c1506002602d003020199404903824131900c1c4c0c1d0004000502003510780302240384a594190000c040301101545c2c14081e0072002e078400c03000313440c1c10310420955040c2040f040c000c02440c1c100512400301e051425484006040920814036401560640300c082c0b2001703002d00f00c00c2c420340207941d818103c0c0d800c1c502c40341c90719002080b80d500004004422a15001d03001403800e034081c1081e54003214280318110b4581642900d4080c148480405010105200b001c24084035803040c2502c52021700001920760800d101040c0703410658101d9010403014940f14190b909031500d0301c0c16410307100c0e04900c8000c503115290040f20781299240e0803e460084901079145404260005081c500b900994142949031452440c027081c2824070942000741d20144211 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 895050278 1250 895049028 895049033
    0x200f0415030b1503070e180304060903061802060703030f020c0d11060c1309020c070510080601080624070c15051905040f030809040f052e050d020907020a0f 69
    0xe01109036841698491038076115509003041032950042560381c5a801214248520800441c0d05a0042072604041c5142a89164028111b4115402c52000a528418104107020b022f02455014500c0c0c0344c080e04107111680c010a0b802d200d113a402409060310380032405441c0e81300f9412199065181000e803205034800d0314005040071100500810944140070115000c940382d507040319042400c62801300700417850105600d0107900b05166144c403034002d0090000ba162502c8913240800c1c4d450f80d0724006c031480e02d07400140c5110805459240aa103020103420b1007494151841201c5103840f070283c94440d80c0518050210120300c3d040515015070400d948001c69411402412a104803045a8511a40a844101d1715401a4441c044036030815040400204078183c00418644e1b2020b8800302d00d40d56915403040660300150f500c000ea402031240b00c00881c140200c0015200c0082d031141a03070052034900060500003071543c01a1040e1600c0d0081445240200041a240740e406100c086100c102030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 895051528 1250 895050278 895050311
    0x10050c120c0a03030f05070c2009072a02012c030a0b04150504020a0302060d020c061006030b030c0315090f0607020c010e010f0c060f060506040906060f0903200f04 72
    0x4010443c003180c14803140840d5040d06005840c4124035603a964a510000c0740c90b1441c04d0092031815040180301c08404141a1325007804003840348460340c0722003407400540f01141c80c40ca0404021880b41998060040006030313070011106d1100d8010108000c0309404c02c03024070ba0b03580d45120502e035243c4a030000e0041044a58044d8602c107034019a00074004409483c00c1d00d094030000c0781c00a60040404406000601d0400003414000c0e2807100e0050034400d104504a207094002c1c1c5080081d000a002c00704030f20b990600900040203000c2e405004c00b0451500407a941e1a076200c41d03403645501440001d44241c1041040102c004410b00c100d03249810603080103074840c2c1c0114895030009038100b00303607109e80d401041688884481c5070ba070350029440c10340300c840007404169003005807070380c8a0b030001a86584036400342000d01486035000a0b02c0c0e1400c08081c4c840502c40c1500014046070000c200701180e0b4803100b8043e110641000e41014400084c005180c203009141541d1703003d854080101d2140c0c869 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 895052778 1250 895051528 895051543
    0x172802030720070f05090c0306010c030c020d4403040f0213060915030b060906191404050928150f02091305090c120c0607140c09040210050c120c 64
    0x1c0c24003202c1130360744a070b042c03203903134007080b207485880c54810008a00c45505c80c190b1141381c54041d01d80031110700c480e58001100000021801d82d00944001c1603c5480200000000751203000061b08015941c411440f2035211041e5624504901c100800024103009240c1c05001c11268020200d45901d00a130b41d225008007864040c0d0f154042c0303008000d0010708200c07030f103d800b966040324a01c2c2c00f59560078100000c3c2003005108070340140c4075a08201b11450300f808013102030300b840010301440000c81c3c42480101c9900030700310a400e6104102c0c0c400450036500541d500204421768800e2202490300307004004202948036a16801d242c01521000d48000e0760240c4030000049031a070103030202e400c0750003059031400d881701c0c0d89030381000ba10241e8902e0041e03040d9180208500641d100c40001c6000501d642d003040720151240600d820b40442c0c0c121042c0308040b1904021030fa821260b042c903401085041d4045100e00b000d1040018610362480170030010303807000d1814188125960807403107090503102d504 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 895054028 1250 895052778 895052789
    0x903011e06060315120c1503021e040509010e07050f030c0c010b0301091e02130905010902011b050d0503040312060603061d04020d0803131217280203072007 69
    0x2510701e001c0340142c0b0900560500d0613940500b20301d280e08000c142d000000032450203d800811103040040c2485688103008001199074400603103811003801509041006d01819501000c030410051010b41c0d40c0c0e442d80c40c1541c07410888010259a10401921244900096140e10b2040402044800040c0000400c022003060b0700038402450741c4d80134103082c3c42044030001c01880b061303105410b050030280445181503000a1189508904c00800700e022200240002e96040c2d44807444c010541d40c01002c8000440c5410240c02e041800c1c644030561070b011580c060381c040120000c08203043c10b10645140000e0307002c0070400c00c10950381d40c80c0603000701350070b1003913000100402d0300800c18401050b2041d4812a0040e01300d40c84980790f59100c90312580001c010240c5e0404014007140810740d17103940b52075054170b00d0315100c092907010300418002000c010308032800e203d281143d10340c001d041005458030140003050096200d440b040e00507241d01c3ea01c0030760206580512101040414000501001100d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 895055278 1250 895054028 895054031
    0x7121203020c1018152904020706050112030314070507060c09050405130b090d1209020105041a030906010e060616050705060c15070f02120702060f1b0c0909070e09030903011e 77
    0x440c407a1300015101d540c00c80d1494020240c50001a124440240c100c1d0386c41d00410052915a40350340d02c90403180d003a041415446000c6c8410420560980f003090f01c0d00c07014044419a518001c00c3c0200b403803264210007000b694840440310500b03400392200070050b0100503c248810300c0d0295034641c0da100c90480c10717503c089400c00854013501020903003405840d596569043d2a142d514030749400f0f400080400c0b41041003c02001540c030b00c5040b0410120364944100070f03500e003050320340540f500310181c1041e0139505000003445103564400084580d420701000c101c0c42030302141d00b841c2e4141006079120641044002a6400424801081d00b800040010700391f0741064840c0c02080341c259082000780d074050307403140e0782c41800e00001030054070800f0b00c0140564a011071003140038140350000745605e8260300c1002c0042c2e410340400c0c44940c44a0100b550548100d151141605640d02c00900c940410300c00e0741c10118100380c4041c0121414060040c0c000d211000300b4880160702e0b00300d001c8082031a83d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 895056528 1250 895055278 895055303
    0x902040906051b0412080c1011041e050603070819021606050f01030302191704091d0a0c171002030f04120c082b1a0307121203020c1018 60
    0x104002d0f000d84003a640706140088500d08541c0d5080041da1210b14411010b21615802c40a420f6190044030041c84002e03050070b8440e8034124101200c41d4460b20a84265260010180415110101920741c406510b1504c24095110307440c655044241c01a124400180001200c1e00030f0245c1c501d050010b83d00c1a00c007080140d0b90001b0000401030f081c0801801a0044541c1507100781c03000c1903081c0e078240514250001c46054a01c0307109589d11640c40740700b0085e00d0740c2c0014114488158010441241e8201903c04200a5a580d450b55021402120501514119140d444407010820a50140c400f00300465580c1480c0c1c4901c03202d40c004880131a01000c0c05108045017500c1a0540c418260b8482460b0381808605070141e0401300d4580a0300415034400f00c10500520348074020101120030400142880340040c200b4541411200d0300101c0e0280d072100300500024444440c44988856035250068566a034070380301c00d0504003032158103111581810030341e200750b00f0344007039008200c0d00c079000c81e0010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 895057778 1250 895056528 895056571
    0x206012303070303140d05010e01060305010e0603120a09120b0402091e0c030403030b090420031902040e012405040b010309050303070804020a0801060303020601090c0e03070315090204090605 84
    0x1045036800d40690180c00c10301c01040001c0c004c00e034071003e0010480109041a0a01c4c03448421254241d10904014400200401520ba05482418050305500211050901c0c0a40229945465000c01940e01c44400164103000c60300c03c000031005444031942c800c802400c00e0412842074001601c0a03031045440a005c160019540a0b010070280e0f01c081c1102c0d2255504008000c10380c0008006405040d2075034854031456840c0e038112442184603070f2a0585841038920b068200050360354556000f030f4800683d0300a00031411203c00381c1194110307404a0424200080c00307004d000364505610032090700840c0080c480f16108135130301c2914002d8070b0030400c41142000443c00c0d5080c0540107000d070f40040010458140c40345003c40e5000780040c090741511913680700401d085441561098005030041e900511504841d8003c60180c80b0041c901078040442d00f00000b51035000b9488014180620300417002d006500981041c000035400800800c802185420148058003084840d089110980e00d5550340313 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 895059028 1250 895057778 895057829
    0xe06092823190810020c2103090c010201060b1e04050909030a1803020105040329092d06180109020d1a0f0f150f0a060306170616030f0912020601 64
    0x11649028000d02c4c03400000e1103520000d60081e07407521064040c10b082c3d42580d10b043c0b810743d018603105120b502c2c0d480c5816103202c0c3c00d24485240e401c1c116410113100304070840d0620b0603550600750705d9a100041b201602c4603400d0354415a446641c0000141c030030080450070101c00352403440c140740c889011022545100380c400b1035090000030701096007807100b0f1012403c85012400401c02c0000c1d0a250803c00e02c4044400c25021a4144587c6e48034083c5050b240760302055440c240304500000724040c42d40c2114441e103402c4c00515071229030b1068004900c070414250000a40c0b0758010b002e840b03202030f4a0070041d05851074000010700014600c4007082d05100c9041d001e510548500031722818580382c207410700c0000b0300081d0b9a980e1085c030103040314646940340c400840c0106259100025508c0c5000d40812a1503280c022100e141d400480c10021258200c0b141c2602c41413142c42c001681d44200725603c001400307009405000d030252000601881c1c0c5e00056028180e5503030600c0002101f1a41c0201c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 895060278 1250 895059028 895059079
    0xf04151d06010807110a20030d0509030c091f0902191b0303020a0302070206030f010e16082a0d2a090302100306050306070509010e06092823 62
    0x140003d6400c800501090f110303401d808442051070041c0c0741500c45546030400000c80684806038501081c2140480c00d143c100321500070704c031040c10036504150b8503e00103521040d040240a000b03002600026210f03541e0192001014440c2e40700d651030203511807007400025048292014040d9490005401c03625014003a03031181d1580c44084c0904080195034120b01a40104449005250302400140e0050341c0322342c040c51044955541c1c4500d40d41c9840c8003140c031000094000944982d16101c00e0144c070703510a1220307511000c10b50141480c008161400f0804101c0c030007010001c0b40000c40e840d1800502c681184040c40304030b2100e0b0b80c3c40d0708007180107891791841100081c0800c035901c50030401410300e200c68003030400d4103080001d030007507950303010a040034422030301c0000290001404c050150b03003042448214a50640381c2504140c82000420320b64003403090360101d10051405400107184000c134480014040010001c0004101c80180040c500c5181800383c0c490240d407506041d202c3c80206961 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 895061528 1250 895060278 895060291
    0x901080d030c140a03090b060616170712051206010801151215150f0903120e1f0207030515160f02070902070c090f06060203180f04151d 60
    0x4051a140400c0c003a80100760400c0000d06021081e40414250508000507180340c0320540c5002c281d034075043c0380c10030480b40020102c0344200014080c00108203107000710b50722560b50081c1c040c85074508000800d03109003e102c4000341210303030050581606c01c0d4000054900143e1b0040c407101141c503072a00640d114202401081c030803520000005400610544903014004070717004000030b8403601c100b400050030110360003817141180502d034038004c620342c44807440100b5546850071040076804c40d031f502189500c006520a00700b10035824407015540d100c900640b0852400c0c0c4100381845007580c006500c6039004e2000352030034040c150a00500303803125011944909020070a410390710b441e081d401e8442c106059214002c601c1008008601e010062009004090160030001111403030f112655007607d6041c501030b541141410030801c01c0c244c00105a4001450450300f05414404020105005071408403003540e1003814500c0c009200f4100b451040103541d640f62410880b400c094100d410150015a5507 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 895062778 1250 895061528 895061533
    0x9090614120f0c0f1c0b07120203190504060b0a1401020f0c03060a1104120818010c0b010303030b01050c10060311030f0d1223010618030503030606160203070602010b03010b090108 79
    0xf8580358070b07110b211305512900c0100b041c0500300c03800e4107400300d800c0c03151001c0342c000c0352400920041d10740152146107010030b00340040d45145080401e090040381c42061a1000b103448801003400c2050075001180c1c0e03e038014210080740c0345c0d590b008052110b0100d2180303026001d840168041d090010801560605020300100701e0b68569034500c17001001c84043c040d13070f00c40d42840b000c01d000340e140114040c400d0280c4000c5848030068582e801a00c444e00403054184000664401d00040308040080d04403505820b0000c0c04060540050b0307002d00c24007440c12814014481401420791342d50b80203c0541c0d0060021642d2441144141540c0d0300e02c44041325890b9200329a00d412252169800a01900d280d14010460b0007500100c4c0c408008240b020b80300301820900140609903110210480c1521055581c0b513183e49592913941c0c4921000d4121401050009240d4a40c6070022112003000c0e94098100c1c0c605540d68240240284140d41c09144a5400c101c009810761034440142c80c1603c882102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 895064028 1250 895062778 895062793
    0x30b030115140a03020d1511030609042607030903050115051f0215130201020628090206040e01060c0c0909150203070e1f02060c0f091009090614120f 66
    0x42401c02d00300c00c0601ca541c0200030100100c01a21044c220244181c8584541c5051031170442c450003c1d510405250110381c0401d104106242e5a14041e0980054010b0f40501440c4545c4020720403030301700340c1c44a2141c250009001303c10558450134070421280680020080c4d4000040074011010720f500c81d040e0b21401c0d000c0462058900c10a85880581240c012100c8851080501c01e0020b001103a9140044042d6040f034015560103102c2d03558440004201180f009000d4002400c204464200c1c00c07098907580c0070040215207403081110003130042090710b421990307500d00c0d005200060305401141d02620034200040d03a4244e43c06000300003030b0302003400b0501e40da2803020310000b500001c000c0c2c8100a440351184107261110703114109040403413022007288900459010746007003c0901660a0100c00b080340742c03441c10350303031054410300d120854070302d0303c05c05042d201121a0320b001d800408816182100004a25110384c1c2d0040c08400305442081d1030601050800d0f4442c01e134001010b655410149 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 895065278 1250 895064028 895064039
    0x70b04050118031b0521030d0e1501090b01120e10020904020706060603050a0c110c010806060f04090506210a0605180a05030322030e13020c011b030b030115 69
    0x40940b240d00802400b0107601c1d40e0742c0e445003a440451880d100c1c2021040840c00d000904084c546216408440b03500700682e6600480b58076940d00c0341e289081e00c0d65680d1000400b0021003481059103289484454420b10f50715105c20350010641054541c0c08aa08440341e018075036814007a108100c6910800380c090b650000c2c4d0a100a9400288002c1d80181e0800200c0009280ba00c20361024114590f4005551301e000711000003110501c64000342809000c1c0096441c210001034800603007030742840e010585485103408140c2d0fa0041d000a50341c0f071a40413130085510402030780300794401d0400701e13104c002003094a000340749c5650510181074a103400c0484000d001c502c2d40e81006400609c98601300340300041401f8424245003901c2411903407600000280103450b560540e1031f092903000701000c1c00081e00a543c005d401141d1440016002d00790b120340303c51403145264141d07440c00b01003000034020203401b40ac81c200d100d9807119030742c80484d01e0b08a0500d00c0b41014420700e5040345012200c0c44080d070a05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 895066528 1250 895065278 895065287
    0x706080c03161b060b1e0307090207023d030501060f0f12090f0c0b0412030c030903020a03051f05060604030201110a02040c1d0312070f02010311030c0406080108070b040501 76
    0x10316280207004080e41e450840440f00d010303400d4464024540041c20340c09040400c0691021b0204107480003462008401403564081410b0b000c849826400680c1c80f8a944040307012103500d641800d00c2100324001d4460022010994440c500941c0130031040501c001920960444800707003e40700014450714222035605019141050056445003040403c03807041d04071450541d141800c00312814000241d00c682000300c00c1c030008015158442d411810a401d115039452042303000f03840501040130b5009154103040c0220071203005541c01030850403416891f82041ca0f80c0302d40340907112034516003982c074008602459100b40f502500f0000d080910f020300d075070011151040400c16801c0d1a005080c0c8440040c0e0f244e04c100d01d071042d52616010030503040c00810301000c8030300e5040a030082d000171203081901103d070021242d506510031000083c0e1103150004070020b1865211015081c0c030000b052002c522141c1c00640b0480b4942d98030000075030788454a8540320052841468400da0003484240442d6000c0e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 895067778 1250 895066528 895066561
    0x90e01150f08070b182215080709020a020319111c021005040201021921020d091a0901050d140106082a0301090203180a0809040533030708120c0706080c03 68
    0x28698007000d501486e00f107610440b401d07002e17104414441c3c46001c10004034140f041c0c100400150604608100800340c0194481c0b1940c03d0300710a06039404003a0b900c99000700341c50b00c07141c070342001143ca00c01c0c0445034400000020351000300251080c481c2d6181522028002d843c822903040c0d015050010041505800c0090949401c9458282c002441500340c41003000480c8500401d50051006188100c0c014101c1182a080300e14514044422640f84c00500d004803001038a00b0301c2d241d60742d542204500c00c020306100c0400440c0a40310800050321b29070110000c0d01071110b5480d2a070368801150070406009110440c06070900c00180010007241d651139000d940d110380008034000b00200d8080c580340c00c229000d903080f90600008104021942054815258440c0e071441481d082c11002403007000310b0314079074210204042c1c440c1072604059103051005400810306002111544492001800340607003240603a202c407841001c5c00001c00300d2007841c0703141c0150150200c003450361300c0b43c45106400281 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 895069028 1250 895067778 895067809
    0xe0405150a110d0c080708010b031504060801091209050f13020a020f0712050706081510091208180103060b0715150b07030f08060a090e01150f08070b18 67
    0x685546480c0ca403642c42d001000102c1200400184d4904113600181c03280101420b101c0030403c071100107100004c41c080407aa000380400700021181002040002d0180209801000065082c4079a89007085031400300300e8440006500d43c085026255010f00c982d20803428100e0f0b0b4003064079605600040764650040c000f40041e44180d030140e02c01c40c0422850001180d001191a0159811010511070f0502c8140083c02040c030301082d29060640700c42d89644000017a031803140c49a00d95242105014041c80001080750030f0401040703000f01d00380080e140e00441c2c06540208004800003200b503209100e820203403264991551704104480c0c451900688586001c07020341136980403031041388006c0448440090440c01074155a602c05840c0040030066414000d00a00c91000e0134440e040d50740c560390b641558000000000d100c0c240c2a8528050111002c00c1c40b0800c0c1d8070000880c6640040010100b031b40d0503001282d40da960356981c100040d210b5415040c4001c030150888131001c0c600046104000403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 895070278 1250 895069028 895069031
    0xb13151422170f0a0b151f0507061d1f0e03041502010f1a06071b06050c0d0f0804080723030a0e03060c0304110307080d03020d060e0405150a 62
    0x10160000900581454102e4044a85942000d9a008204201d5488100581400f40540c40416658140c0310706026100b1999520450758048080c1c03502d41e0b0701012040020449240e5410b4a4006030041d801802e0603100030b8207006441818865881040003002040401803401900301500d491840701101a03607a10240c03201d10000080404001502c003920400d1030715810802080000380c00c4807620050300c03035028201115402d11f80e89000c0c0301c1a444100740ca59943d555003502d066040d4141c10301c900700500c9001c20001c201c0c240d02c43c02a01443d0300381c0040740c028a1008506a40d684154014000000e0b0fa0100181c001034400c00589220b40c841d460541d500c0c80c815210410705d005480c1040c0980d40081000314416500400450a41005902800250401140e0411203100052010b004100c580c8804000c5440c200501001009980203980001520040040180d80014115403105007130280100e484800009414015036004004118500c10384083c0811244010040e00259 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 895071528 1250 895070278 895070317
    0x705070b07150c18080a3207030f0611030921190c050d03020406200a021305090d0e0f0114250c090507120b190b131514 53
    0x503214010742c140100180c803a000380108810000280d40c0045d400222107501c41484103003c9440e881061000e5203000b080e04424000f0440c0e0088000362900d00070b42c0170300c9040000010b0228038038039202d1092041d00e05010000d14850750008501094030420700c00c7d007003015030000c110160804091055560303100d090900400c030b2401e0b80004034002c0302c01c010076500c00c0010200b11091101080300d03c1c440c1011810305003002c000820545a80b1701204e10b0750302402101112141c02c00130000c44c150700030f100c0c84003240302101c0c0e200901001d9402c4200792044843c11a45907000300d00b00c02054402921000030200401e0044603081c140800c1c451440c0004c11001c00c241c00700c1c10a4000001401c07060000600342468000c16280040d03102881903031400c014090080c0e40140316a540380344d4100041009442070303001a4200e00081107201c9004008000007481c2c00e48000a05406c6030450b022031304096032080424046100c5254403400a02c2c8090141c0e181075000c000f500c8844031115980056 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 895072778 1250 895071528 895071563
    0x609010b0a03060e09010f110412140f01020304200405011409101e060e0603010e19020415080402041d030d0c020a06240f080703080a1107290705070b07 67
    0x401d1040c0c0e040c205c00d9468a200c007040600134041c002103103d02c501001d184c40c0c41c104a0000781640c1880007054107500304460f02c2c0d1150708104050030200120000c542d45c0c00c0520b03040c88001c00a03102c04880f1030000d5150301d01c9150902c41c040c12200d04036017007169801050200841600010440e80340c100000301c4c0415603101c3d0f010f4981c035a51a410070004010b0400e04080c0003c08200c584034860346040005119010240c04215048440c0d00d03540c600c03065807584040080e00550b0464a142d842171201440156480704210340100d00a60b42042106030002c1082420321850500c082c140d4000c000c03402c01520540d200d201e021480e4810344840038290340d924002d851380886520302d158080e8540410452800c1544001803c0107034a900c3c0c0c003450207400507190381c10342c40050503c80b800b103070b4000401c1c020600301c0041440d00301030701d25181c0c0350301d48a40f18a00750b84038680b010002c07030110740701c0001001c03c40e1f0700c1e150800000d04019140400d01038142d401507908655040c48403403400d02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 895074028 1250 895072778 895072799
    0x40609050f03031b09060d020714030a051213170a02010624030507110c0d230f0c04020f09120a0c0f15030c0e09150a03050a02090a050609010b0a0306 66
    0xa0841400610f40d00d0a24280750b41e06010024403885104100300209112940c41d50116000100b102c072001da118056820400b11000401c540f680303003800005444a02c1551081c000e040c0000c19030342d04500c0751614000900000101c00c4001c0100217600013006c2c08600c01b1000d02060011480081216511829400b07038a50002051801a01e0b030002c03c80c0e0700399014010654000a9803034008410240340440d10f42d18400501c3d075031702800400c4019030511400404505040300400d03503c1e41a0304c03c4188081d40c4400214070610680900c41100c2503d190030b00071116005030f1014214285900981000508041d0f10054000c511a00d1081400078191004110040c442001d811002078500355841c1203a10000078248101403038082d201040740c2d00108007803d0044152022000d603540d2360030342d19000b114492074a41c4402c003490000100710380054542681c510988442800d41c172121540700c00c0c1d5906440381c0d54402071480040c42100210301c0501a98a1a840d010410350398403c1c5484 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 895075278 1250 895074028 895074043
    0xb0f0607030503060f0f0108160509040501080c0a0e01050a050405090a02030a2d0305030c0a020703020301380a06050d0212040b01030b0618010603020d02071205090913020604050904060905 83
    0x10003103880402040545e10741450b00105002013a12600404102600006c000e07040c002c2c46040a8654085d6031010380b03104505030380161901400411103541c51f80c90b415510071101d2a420f2082c07542c0800030860344650b500b05412614090035100c20f4501703200070040a050b0061090381c09100310400b040145c1d40411200040318042c40865150040303001c1e648444801041b0440206d2040d0503039180081d80c84070441e0381c00040c1860300c0d922680300b054101d042040030b500c041c5d413660a028070500035203544100c16188101c41d8082d110403011060441408040642005500040c4400304203c4540100010048001100c10061501c802041c081804282c10390382038506d03d034a00018002c201d00d080b0580e41110f801ca4844082da25517115071040c035481406034804240c2c0114031400a0429901561045540600c2d1805040c0c0e02103001003040c0c00010b4424841e40000b008030347c02d0300c02e4141e94922680c000d80505d1900d4201030a00007120000381040f280f65a0340d800d95400b0590510408 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 895076528 1250 895075278 895075283
    0xc03061b07050a061b02031206010c020f12031305010806180601230706050606070b0117031b031216020709020a0c02031506012615061c09030210020a0f030b0f0607 72
    0x740c1c0b0040e175130708880030758548080002550b00c2000700d4180f236503200c40c50740c3d4000e200340707015034644000d48041405082100501e5410030149500490254004030180c070a1025400040c0500e9a40e080112004001950340307541207400b032462150a040c402001e580c2c000c1040c14058503059002141c2c080c2c0e0802d45040b031018070707000704000302004040d0044c51741181044400d10b00384449510b450600040600c01e840c02051207040c035485049050040d6940780b038808802503441e41c44200c14940f01c0e07108211100c55403500ba0001030440b400c21301d007000c28040990042980c00e050100b00c00081d0b00400b095018044170200160040c2e0301000340048190302c075000c0c9400c03402d203040050800718804840904202c803034000b2003040088032001030703400b012240c011612a130408000c11907a00c81ca1b0b2250080b40d143c0070300110418400d411180100c1e00c00e40c01c039041809401211703000c90040d41700360400100001403003440c8500c2a0010b980d00480200821880c091000000c1d04a52280004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 895077778 1250 895076528 895076531
    0x1505090915040f0209060f090f040606091503051c020303041106070f11040606091d04060e0712261c0b0a1401030b0301050601091205010f050414010507020c03061b07050a06 76
    0x5030300c04c6003002d0781c400d1740100d02900c640b10020003d00014104c00c000070440180d4443c2c0000040900801c0e410440060040110400003121440e01510840c01240001c3d122849040c000b000b4a20001c14108410649076010310300310b4840e5928ac030b05c1d00880c0701c0c045a00000902504020030810403032000214460064185200c1140d0184001d03122507510020500c01d04000400c220010f01e00150700c03520a0086441060b0740303d1402d00014900070300d03a907070584034950f0040340c04850001c0143c0158080c18001c40d04c1500041c5403000655032440024210006008141840045c244011405420000041100014440452401d005a501002c151a10701140078001c1d6050b01c14141101425002840f17070f4544840003814459061081c0516451032800f040c05124084d804250211440001480503040508002d4500c420f02d0660400c69460300c0080b0b0140f5000240c100412200a0080c10f225a03510b031340013801c8034000c198914000700c10050880060342c1440f0f4250058881d8a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 895079028 1250 895077778 895077803
    0x130510050901180309093b1c090e07170a02130902070f110112020a0f0f1d060306030a0c0803220b030604110d09050d080a150509091504 60
    0x32941d0944030003001d03c40303898020310404000309600c50700e6001540c481d060041000070581641e00c01101c04120b0303421106450b845081c1a10940c01800d14182810000301c4100456901c2031a0700d214030f01c40c0c1000440c050710020089203100381500c0340e10000c3c0f410007030005c0c01b01b9081d2601d220390403900711030788550014238038017030701096040c200241c82204400c505005095403140d0f481d0a40700009040c0500b02c03a40801d680e0722074000ea015143d01550195102d992000025212036014106c0c000480c03682d2540301080d078842c1c60f40e41229110718481500300484a4144912a8405088140c04d0b0052004a0700030401c030443c0300c8010701040005684d0b4a080340640e01e280c0041442c01005018082020041c00342039005403600700b402210300090002000c0300010715417207051800c801040c2400480ca040c030030082071403030341c40381c040e298041c16654100248007102c0118212003110b005014062046003400015164840e03000c0c8215107200380500e54141d07114004a50450700320f0381e02d0b02d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 895080278 1250 895079028 895079041
    0x706440402010f05072004060b1306140f09150904060e010e0106051908060a03120e09090613030e031501030f03120b090a02091807180806040b0f13051005 68
    0x501d980c1c1511461500c241012117075924144100c074456a4518045290544002640d596a010708010081c180045e0ba42c0e01614800a980040c9481441c6c0491b28103029004009030040880c0d02072042c1c2040140340050035030411650183c85001d00f02c00711014040034070180c032640f1540014000209042000b9850945101d41c200c6d0140c0010080080a0044000020014000600e600d0103424804115507400c0049650350348598405000c4446941415080d650406000385a6500560b5038422940e101480d495513000c0654a885034040380d0002d0702c0c0880e12450421f01d1300300006042c0c0f0b01284000070100c40c042800c0c0c0096601205081d5084205500074682d8901544100001d00100e40c2d4440010758118004000d641142e800240900085c0d9541000c50035040c850820718040d410144c10040c401507400038480b007410090700020800303140001342d43d4402ca44c0306078140350a541c2c5d40c440780340d8002c002d40101a140030859528001510a0080001500304858006101c5c6011b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 895081528 1250 895080278 895080287
    0x904240b040e181c0c080f04060f02210702010e040c05090922030e1305070305010819080301030f050a060f1b08100306200310050a08070644040201 65
    0x140041c402c40f141d10540000c11440440c00c0403141100c2140c03115a000743d10025903164102c0d8400400340d1800141c0c00c001c020034800903000f42d46907542c0d0030b014071035110800c2c0e03a075204000716240f00480d8031007a4010722000b04010446e013032043c0741421040d0008070104064030724401c0ca10000c201c0108500d4541d00b03200300c10a50041c5e904c88112041e400c920311100844050140150411507410500586070b1100403003a105080080e004008519001e80018010102030040d42001c1c003a455004034551440703920100c80d0380d004071aa030705d180d02e0b5030b46440303200ca40440102c42d640500b200395400308010340b05100e40c080c9024008107403c4c5807d0400c80c200754110304180140544201449101c0c01c00074102c1066030742c006000500080c03c96420302d0b1041d0000060202c00000204102448826240c01c20484506a0340101000e4039106440c1e2105a5405108000790300c40b00da1703000c10480000c40d540c1d05201003510801e8018800d01c0220401c0080c6501c5000c7d221800a020442d680b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 895082778 1250 895081528 895081531
    0x601232b0b0117070c080720090108030703050d050402030c030a03050403170406020607030b03010e010e030c010f18060c0c0c090218030106121b050d14010b060405060904240b040e 79
    0x3483d04900a030009000b0421100b00030700780008002a00c030018003000030180c11112040e4000d94580b2954050018450385522003106071805840301000020f020b040010076075810340e13490b4884604090602c50b4040003840001d1090364103114200304248991000d01c528043d02d4040d0b0344242d0b40d2030860402d40e0400c8281c5105070941c0c10104802c120040d40030628a81120b0341d0f01d0301103841c00c80000024050580914515015480c1c0048110701e080004001c0860100f084000e201c900c03603c0540e20308840a601c20070b540c400201e4040400521581c2c0002c1c1c803410381e07041c00303020207440e41ca411a0030070341c680040d95582da001644035103001c50305007450303000304040300284402c03070801040c1d404040076141c00410300e8840c00f41510705042c1d851942d00c00703480b0180c07400214440d0350030301c44a1002030b0154428294641658008541044002c540a4440c00313051103103070441101c140320041120561035000388000114041c0b48040340880b11006048062416403074600f400c0c450001c1150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 895084028 1250 895082778 895082801
    0x1c0b0105131a070812180c0a09090609051f05090304032105040b16031205010b0d180b07051b01060806010302300c03010606170a110f0705070303170601232b 69
    0x1e0100381c41203a03140490b80043e04c04410000c54100e40c5803602c10042d0034cc0140061041c06903210840c149480c0f002c10030642286030000307000383e03103c86030305946912650001402c1206042488040380c0102d601580ca1440310749022850f00d40d079510a21000d0304403000c031013501d901c810541c10500d031b0310070050262003407c40e100308030a52415942c2100c1e84035a071400c022040d12260942c44a0482c46200702095803c44042c104a00d0040b800a050f81e01c1150000080c0b00c050095100a14051003084165000f0200400859013150204401036021040703080c01c8003011401d00c1542c202e180031320425096010018420329100b201018250b81694011800b0071201c038108988503030544403c203812202240000404c10003000d04000c0501c680b10101114020010340c2c0000c004d40080c0b19400c82e400780d42d681c0303070b0582c2c401450703050003406495282c0002d41280b880103107280e1040407419032080e1042c0c41440c1c25080c20403c0d40c031481c0c020920141880c030742c40c1d4240202c2d0602510301d9801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 895085278 1250 895084028 895084033
    0xc1b140909030c0c091f0b0304170c1203220b010e1602060c1b15011a0f071112161802040b04120c09021c0b0105131a07081218 56
    0x3d001c184a5a030303900914543d91158050070041002d003036080c54030414204901060300c0402d91504030300a100c2e4401d59003182c02c030302600d41c14092050310100b0380d00020055005059080f02c43e0541e0314030384c3c00c09044001403109880110414100038240c51490300e2142d0340900b403961512980c040d4031800103225030321002c1a1005e80e1030084c1d0100c3c440354040100350400c1e8841c1c41880f0707042040d4140c2a56075011707116284140d0482e40c1380b460002c0c121400d403071100e4500e803401000700d01d0300d0181c140c0300e200440050241400040100d6030540c1250006440050310b0321544182d00c0c0303401030307010503544000c1040c001071201000c0b11340300903094a41c0c28810340c85c03c1c0c6002000a1144950b11030120241c409003494420044a8000c03500101581d9205548440d03480d41c5065254040c403070b10031001d83c6000000b00c280d50250054540d04540d0800f00704106150619081032403020307281111003110100180e800203001032014001030941506a0800ba1404030140c442d11001ca0034444110f6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 895086528 1250 895085278 895085287
    0x80a030f0305160c06110c0604120f0e0d02040b03030f09030708070807050d060b030d0e1c32030c01021e04050907050c030c010f0b101704030c1b14090903 68
    0x80f6900c0c41c0d82804111280f4001210114070305101d8000c084003020a984070300006140840c1c40c0300056080e000314020607686201107104101611231310400d8642002160b4a1207002d8410b00c0c04000101d00213001400c045034035a0346400181c11540599440c94807104080f40300e604604013086140d02404a8400a00c0c6040c1803c03906640c443d01d5224040c42400001f00400402c01c46400c0340c035160300040d04840d41d90111080241500c840c0c0c00b4038a001780c0d08010038110b0501c1034030b5142e2020b500f1080f82c0005500d41c0c0003030031500e07250442c0d201039002c086c003003034111600810041102c0b0714004001611480c5180000c0855111401544501d0300240f2003440b20350f50f0115101c0d003107051410525aa81c010301103144c19402a030008003259442c20a0422141c10160064002080210b0321201d403e41c1c520400d98040101c0314060360561407600008000030700072406803c503140546034241c3d20510020681d0341c07401d51038101c9151214083c000c1c1019040c003400c101d030040c120001860a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 895087778 1250 895086528 895086541
    0xc05210105031207020d0f0c170114160212030408071b2421060f12050304031e0c0b07150228050d0f06081002270415080a030f0305 58
    0x110f070006030034141030305000038180003103655980311340c40301c1a4400745032404a6205c0c1042c0d80d2500062044100d08243d801e41e00103200e6042c0310b900400003160128211503103600d5040a80c5416001440003075110b00244885001900c00107144a240b01e90901580c03071956292468008250383d0b41c0c00b40301501d0400c18843c1000700c0c108180000381d28144038042044034002120b225042007448030013034211414039010242540c00c018161981d1042d00e100d555a04d01c2c2c100e00781c050140740541301d03400c144401c0c0009002032144c24071480c010080942210580e880b211204207485d032000c4000390001518108111000003241c00500756094110f041a004c40c912940e4080204d1209402e19400b4050318116400f5409442c00e6142444040000121343c1024070000d00c00b41c0101c1c24a442068001800005c0c14022244918505100156042a4201a082b11041c1c800700765500c1520f542105041d000003030000402405c03048001c020740915401c01810072900d003916902010300303090401c0725 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 895089028 1250 895087778 895087783
    0xb060304031202220e06010e030607020a060908040b0a180b09010507020418051b010e09060a0b03070e0d03082202100c020d06020406020c010f08041a190c0521010503 73
    0x10324101c0307400741e903805401251803022440003050344800344d20300401003010000d10501d98400c071030070380321074908400c2c81c3d080640e00c03d02261013800603804820340000180c1c040d041200b8144c8940c6040741460740391412948143c010b164020000307107904c0d00e40c0ba0301c072020216140c000c104140c41c3c00e181c1203646c0c0c0020440d1003400c078080d0107641ca44c0404485841e4400141c4a055002410348444089646c042040c4007000520140003906145401106123010421070b070007000c000348480416460b014141000d81c0000782a0014020002c00284146d00d80071f030100038142c402d50b541c58552a20500e00e9200195012040380b194130300103070110050f210700c14004050b031440c0c241111591182d2001500d601d8000308000c01250010074001101030f00001d2881001d00309803260b041d075080d04403040350031850880d005040815a601250090016500c01030303046004200001c40100002c51100280c50441c0c5003500041c01c00039040d8403010550305104447c4503884e59032840b03545400b0020b035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 895090278 1250 895089028 895089047
    0xd1a15100507111e03160803030a230f040b150321040b040b0403020f0303160308060f040c080a05070c02130c03090c0306050106020c0603130b1b120a0b06030403 71
    0x500c81d001602800744090140b980394902c000801445113560400b2909107840c03ca160024001d115951314060705804030191070090311269402141156155860103000c1c1c2080c5204a00c100e900310724844213441c0340c1424030f20034401140740c0442414240341450032010000c001420b041d00703142403213007155000b1554502c0d020b02d002e461421075044045503540fa2141da4024425414000380000751452070001400440303008403403119445405106054480c0300b0301e4040071510141d8951784d030010b801255100c2e0004d0002d0051110b040b50140403070b08558982000c03102165610307040180c2203840d4003d1942c4090a072a00130041c07001c950115103021400c0d2080c1852581b544000309509d0f01ca03500c04800c460b04048030201300d40e82c03420110b0080c10700b070041c040140103018035522320b802d21500300d9025450995030480e102880d5281c518420720054180d868501040792500350740e002c841c1c0500490800308555900c41d00f04480d02004550703041041350300800707081c0100f1011a41002009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 895091528 1250 895090278 895090309
    0xc080f0103050a0b370609050f04080d06050d0501050a1b020304180906060b0a1b080304060e0f0303092506140a02011e1a031501150e0d1a15 62
    0x22030898540545000c1144038009044480214007010f1080500c4c40b0314080c14261804c5c80108841a01c50b540f0005540382118465804010200403800040c4084024408514000f00024030b0640301d5002840e0248003110035031301a0344a0040c0180c140052285014903001d5084020103d110b40300f0203501c038020380c0318250b0440030b86140350480d4525a084200156480a800c010094481c160180b0039002030b5440c4002030300d00c8030b078902c00001810034140c0558102415a056503510350352071010302001d44044115000303036040640500000c001450003000142c0151900c0e481c01c0c0b4034014031580580c10002c1c02a0800c030100301c1c55802c4513a50085000382d440d1030350340d14015a805da003d013094100c4002107120b44c0d58207240c2c0020310f07480380d000d002c021b00d03490681010722400c240e44d869007514a010424046001005002c81210504d2404040303802c0000e0281000000200d44054911003541c0c034840b61403448604001c0084416030207030508000c140000c142c200070030394080e95042d0341c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 895092778 1250 895091528 895091543
    0x160905060c030d091104140114280305010c080c04213f03050c070204091a04050106090605180c03070c0f050a05190c1202042405100309260708040303030c080f0103050a 74
    0x9a0006018103008000c0062000303ca442d035642e982c58071378002c210001c5450000340d800008904405130b007404039021030b01000000403080d0a180742032a5038130400801155100d2040040c5c024002c4000fa4100c0084221150001d481a0240c1946000307035540d04001c0800d841e1504002e49907440780d085d5002140c0640300000c12052503d00b032400b10035150050b8001d50101c10800c410004150090710503605418000d00c41c1d103540e0400e108c40042205410000d90700d880c030020b1551501c00c006035a104003030b443d007800d52118035107804070050f0804005441542084c0b07489d0302400400c102910b4503048040042d03401e01810b403504461884180a0041140c05002c241011f40d030312500820315070441c0e4080c1c6280e803c441c41040031001200d1107080c1c01003140101c3e90882500a104090300c1c01c0c0c00170542001c0711078505011002c6d0110b2003103428180c009004400114110ba4007803c00785100380c800082c13915101d81c001c2d29105005100e1a0712001442c014400600d012031401d8440f9405002e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 895094028 1250 895092778 895092799
    0xc090e0702241f030f0308070212300c0301090c0c0206030a0507020c030105071407051513060513030e120f0d0215160905060c030d091104140114 64
    0x7242011210030251501d003101e01c2c10140440b0001c80054082c00c002050682c490b600f0b80e2150803c01101d1101801800b0b144080c400864040e80803c1d0344000070344140d0b1201c1701c144145132003a4120f040398071100500448580580e426400c030700eaa4603440d01180f0f110f513281c142204c5401e84014010b0420240d00ca0300100e01d0b140c080c0b4040035040c4d90080040d03869103082c180d031100910045800e000140700d00d41c048000c030b040c1885010300551895582c040d40c4002c4c070350b8641d02c0d03a1013494111624801c422038000005400500c840c010a162a010b5640540904114007541c030090400a9888101035062000035048200640011000e5070040f00c0180515002c90420090001d0b800c23407805007205034031047c1c1d400700d50070301740f900300d41001c1d40a512345c10702110f560440e2201403008101004401e1200303240c4840a416810750340310071240383c1286400c01c01d0a442a00f10700301c580725410302500d40203141a010b80301904000a1191840c1d61400e001c3c1000c200010407400d0160383d4505 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 895095278 1250 895094028 895094041
    0x90d03020c040501180c0e0f1c08031f0807061d010e030f010501090c050414060f190f0e0d02101b0c0803250b0a020f1902010e070602010c090e 63
    0x344400554000b0700812103580e580c101001600f08010900402500d001c08034010035004060480ba003e1010b0101148215a042400035500380b4029800031928115411000960307000000c41c419040b2826011001c03403014a120508000307500a101903421900e024800075030300c04025414045c0643d0a2082c19999100503540382030380b02070068150103441c00340301002c0015000b80d412543e0300c030010000c4100da03010403100c50169000d00d45505500d044545481c1c901000580014204a41210724200b168100d11070380700f03002400000071a00f6440c11601841d000107940135444015541d0816200b519800034028140d040441014000d100310b5071840c044c1a0020b42441e243c3c024172294105448480e4240e07a0703040b000c10308202900804090050440c1285c4101000340c2c411388003a0b00d038403105c5a880103500040b103003500c0d1343c4040c000040c0a002c444500d00140f1002d4000180340ba070109942410103540380c1000065a04000a21107100e03800180c0500b1103000e21912003040d103940 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 895096528 1250 895095278 895095283
    0x6070f0509061801090b090d0807061d150a11091513030320070305030d02090409060908030f01351624020604080d090f12051c050606090d0302 63
    0x20210319810240200c1da410b660b1161403e80041c2e20401d03210316a280ea0303120b803054140e01c10460138981181e8403801900c00264058090400180300b03180c04141c22610b1078a0014445c01c1e82100c0d00c0c07581c46005a0705042441c148001d401250321602408420111780e00d0002901c00ca01c0384a000b0340b100c280c130f00e03a08941c070400d4860300c2240c00e54402103d984c908005140307580c0701110f40341400e6000d540c900070030000107080d41140d500201450400c1681c028100003908044621a0080d444076060350000c0c10701d102d20b01299100d003d03055100d0501d0b1010125481051b084410004500e102c00c080500d158035051442c20b071046100400c0042566141e420204840507000b00801d8888001c1281810b03810300c90181403002d00d131141d060b00c0000c0103d0780e680c0c09450150250342c00308083d4440070345540021040502400240c0d910003190fa40b8404030001c5407c1406c0003400c04595601d2032007020442c0c8446042040082c041b90412000240030340c414000704511501d49541c170082058000d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 895097778 1250 895096528 895096537
    0x4020a0510020c060c0114011d160c06050703090b070306051e210c032b0e030115030605160e0a060f090b1917042a081c0215010806070f05 61
    0x544016105c915202c5014007910038012010325407101d4500100d4551103c8102d68042000016003e603141c4845040e403034003240305003039001005111203416001c100f0381d015044c0034011555001929030307498182203804000150022041500b495820405542c501c1c558446010b80040d02e4401c40781d104000800000c20000e03402c4156401e174901100c4604040f40c14140e0040690603a800e4108442c081d004411003401c0c04103410202c18810080d00d84185845c0c0302c1580d01400015156401146440c9080750036030003194260344130f40400450240160a460700703803e507400c0040041c810180011100711250241da01005610000b9861651203000c2e0240108100f116081d0307980c0c0c442c2040138405910074034603000300742a07401c00351885040c071b41080d02c00c80c1c00c003100100c2c0e8000340005042d04007820002c00400300d9500d201044194007480129000d6420144480110010141c041c5c20104141c4110b02050400e00040022030000b00e0604e0340803049140140b80c4220f10f9400741c03081e014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 895099028 1250 895097778 895097803
    0x901140402090a090603121103160215130501120e1504030315080a05011b08041b080d0c12080402100c0515010605071704080c13090b16030b030604020a051002 70
    0xf40000000d81c00301250302c00c00a4a000e54080c0514012024041d5280d000303405a000351681708104070005585184410b40a81d1b100911416101074510340c003a5440d0040825a1000c540c2441d04020310740c0c010188100f10746d42d00f5000d104054110103c06d0b260300c000040250b119200a00081c02c040c03296004803100e440410708e502186071240c2d21147e030b80241d0700c4100d41f00d61078001000380c4a003050f038215090380c0b01d9503201c01d40d668495032640e400884440845100301070001011450b031005000d00307a01140f15030303500320300e800e0704d800d101107480203a044403000c0c08000d9042c040076859078000605000c2840c10581d8440300c0c14617100e441d1640400f8400a00c5205000101c2e40607400030040c0030791801491080c5c0d1841c0041540205481070b803240000b954441c400c21a40740c1004401407d004002060004840710103468444603844202c0301c0342d91401d04c1c4400079014642512070f2000303210050703004018910381940880d11000c1d1a00a0703030b2103078404200800fa000e2081107003204e0f250 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 895100278 1250 895099028 895099039
    0x40209041112070f0507110d020310051501030b091308160203010207064805160f02030f0a0b0a18140601060311132601020406022a090114040209 64
    0x90409450410b05001941d00b80c00062540f02000d22162052050324452a00f140300903a900c1d2030714082204019510070100e8040c05000000300c04100207100d514400c0c0c05800741e9250300c2c0780381e10005080340c10302c1b18514824041c03079090042000e600c507200014a81d001d15401d03075032604c2c00031000c04a4001c0d03000942c190700005200003005071715005140d41c0d9407640c09004c0050410f4038000b081d00c041c841c0e1413aa074000c1c68002c0347c00409840d462403000030f241c1080c0b407a043c0c144900c104044030b0f100b010364030110801e0100c021801c04100340d140256001c00035016540c5560b80d07540008801070111100c1e1625940059020301c3d401c1950b041099000c84400b080204d01d000d9941c444209226843c0440c5c90280701e6160060600100c1d05000c0c95810301c4550340e030420300b90161802e00c2c2006502401108400d20010640901c0280003900d00c3c0d800400302070707040c01e4045050324502c0c5c0a442d02c1c040190620700c0d207500e503441040d06580e059a66101191106400b15000f406140b0700158000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 895101528 1250 895100278 895100287
    0x30712050108070f0e06100e0103020405330a0e010e0a0509040b060f0d02030a0204150803040609031b1214032a071703041406090d060209120c0f0402090411 69
    0x900248640c100c0d896040c11800c513a0fa035003d070b5818900100c0e180790300030000c0014411002e120f0302002c500c41105040050400fa150b00100d10292401c40700d480b0a41c103400a11990160054040101409040b010918201f141c1030010400380440d02100d05001c00c01480f42400e5442005041c00351402400100ea18502414805510b01054072041c0c0141c102c5c80494043e0b04203040c18444030764010340144010802e0f036080c0300086c040201c1e0016441e080c10030100389880c06100800c001c048a58075a4861425820060b1030000000c03c0e40107260038a1608121141c0080d20445100b908a07403020b14640e69134100900b10300c41d21603000d801c1a0144641020348a030380d06000c4d00d6030b40200854210b43c2c3c40341880b000c510302c4a0510300599105000030400702e40c040f0050705035540081c20281c00c141103080410480030700c0c0d10048407440d80115040036142480d032591220303240749070001d22103944408041002c003c10884d001c0d00071600011071268507225900a120700381000542607994 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 895102778 1250 895101528 895101539
    0x3080c2802010f0e010e120a0c080f1605100f02150a0c021204050f400b15030115051902030301030317040804091d15090d030203010b09060307120501 66
    0x40200c8040c00301e02040c102d500d0103076014456aa10b580014041c0c645004481c500810400180b0141d50100161310810000000084040d51181c00410390b01008081c0c2104100090703043c0710360070402d901f6250740300b00108000d507125007026480d9025800d1100705503640071402c038100200c07004510038400c0c110040c0312001d692a8407074801500c0b10b50980d07036146960b03e03031001e8901c6a4801d0f00d40c031640754244a4040c2c54001101c0c0c0c1a40088141c881c2c5000602d4000c400d80301d4100c2c1003042c80000b801c4424800d10301c40c001d603800160212000c411703079080c05401450500040c01800314908020000740e02550042c030844000a0400c95101c040e03029082c0001d40d0703603109005c01c40002d100e101d020900748480006c40c074041c540c0040071508007801c08032040018140c8841d02d150906c042403803007007400000e00080420000040c1502e1032441d0090301e040c40c00e07200d01608010944100f00422288406405403401c2510450300c11f44d4030380f92118102e03480c1000304000080d485c075104c00004c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 895104028 1250 895102778 895102843
    0x70e0601030f020301050a0306020a1e03061508040f061a030a061d0703031409130f050a060b0c0a140f100501080d0c0201021f110d0501050310060501020703080c 71
    0x10a01007681d090003019074003440d220036800284505a00022403682c2032001542e50340203003100c0798040c50b1198840104143d0b84020081d110b00302c8003c00d2b90b812003400400c4cc0003a20000307034801030501c1005030030f0940c1c0328803200a40e035601074512a998030a03c0400707091500100035048004080381c0c403000207420220000c1c2a034000c101000100ca404602490310089040c03000c680d0951100e0781d42e038441c4200ea04e00b82e80f0104107698407814102c52200258210711a9010111402d40005460b1500171451000c50302e298100d050011010300418510b8000050b602c0c6d501640000341102c00c400c8200200d150809240900c501402420001290944c01d54000d074102e81001c000c50303444103803100c01a92501c0d001c0318040e00503008040140000920300400d41c03c1000e075110006151030f4045101c1c540f039002045ca0111080c1ca07280100300601c0c0421504c641c048040c0b104004007031070100041d50b680038a1000618401000c0751424160b2414000c140c06880c0c40c40381d004100048007803084 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 895105278 1250 895104028 895104031
    0x405031e040f081506010311030708041e050c090c03013209073203070809070302120109030215090304120f020303040603230f01061227020a1a030117010905070e 71
    0x1400313000b00382d0000303500358480d0003106918542c1451961071910b481c1c1040742c010000400c1501c450310000d681c0d040b00704403001071030091800340001e8445450f107641001002000503006400040040c001031010354801c0c204036448681c00484040c0c7d001241d5101741244209024440c0d008520100b00101150803005092000c402c007011007030403114490b002215100040e45d40b041041061001880a034028070031650020721800c222004555284e0010b40011410106014165100c087e58000c050f01001005000e1024100c904084e01d42840c00a9490240f40700e03955841d072018400600b4030130310040780c92866401409507a603c43d140d041c090050905003c84110a00c100342488421402c203803c81406a050012000b106910b4204121107450b0314804510301150340715481c070702d00d203040f071014081146101c0390721341c50b0041340c0100100c03054180d001104034000d68864170000f44882048134152801280d81c00b010a104c4008180103003041200102184216000403c0345c000005105 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 895106528 1250 895105278 895105303
    0x30f060e0103030804020a0617160c140d090504050411040902130524010f080a050903090a0f0f1505030f1003140c030d030b150f0f1b070e0405031e040f08 68
    0x41c07c0c1940d03205403c4138062042d070340080f080c25554000c100811140c40303001c0842c0440f842c1904c07900301540c60790046013603100440425a17002560b81c00c0500e0f0000340e4403004000480f001c020604d0281c035041e0303031100400303c4940314695801c8201c08542c0c81303003d00c1141d80e41e180710402852400c005102d00c9007021310006031181e0012418884a5881220101c2c1c40040c0f60740c0b4000141c58a03020b4001400d801340a03601c1a00090003605415280c5003c03034001442c00c050f807003c0b45894122401c0d030710f06242c1c2104240007484a90440c6040d0000c0403207811611200c619a001d13990b07452145074000c86c9030001441d881030b030704040d41c4c46900040c50001c0e0500480036900d1051b0307610300640403100f49603415900885070800e40b000c0c0b0a001c1014108405840c11818078006540e1540d41c6c19502078034814405114028007490042801c001490150800c2c001042290510383c690315500c2c0240b100c50060400103044405180c2d44203400d40d402050280030354105c2940b03504683da10303003076400c212 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 895107778 1250 895106528 895106539
    0x7031101050a02161113090c03200a06050309120705012301150c05030c0609061801110906030403090b041404110a080112110a030f031e020d030f060e010303080402 72
    0x4100d500c0390b81d100b00c450854402d1080c0820b000c480d40c41080500c145844294800b4200c0100e4850140ca0b00030101050302c07c8080d50480e9055150807010090800c01d903250a41d48148005d241d070302c0e5103071840140c03580750900548030f9440341110b9280030041842c861302c0703ca02260030010042c05401900e1407061b1034070280c0280713a40e140c280041603424415403682c0c4200d590900c514500824031180914018821380e407610340c410321003c1c60030205854640155001004100c1d0b24a4601c8813944018038080080c4403071070341c8036110700310360085040c950b01c181000070116080600520460380200301c43c0300025140e070366684070040c0da00e0680f1a0140503904005030031075524102000c07207443d04401d40b181c2c4801c0c0d00300f100001100c0c05410007203030703410300c820901b11040d504d20b52660015440794445003d02c05603071600800b420342803442d00186490204025461a8001c24140b0407112030f40340004031118000b070301c18050011a4400c02c1c00543c14400842415070010f14184120f0080d41e8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 895109028 1250 895107778 895107781
    0x170a120b03010e0705060d0f0e06010314060c031602100504060203010f0f031214070501050c030703110a0903140a1401050403030b0d0f02190e1305100e10020318030703110105 77
    0x149403c1e07807100018070302c503034005140c14440d600d0444040e0440614951000405944c0c1c00c45482c112888900300c0d4000b0f034892401042008003a11440240402d40000b806013030030000302640305400007421000442411107204214107100700500d511000354a90144020305050070b0800003503000b80039000c01d1100e0550041260034000c00490101e0341d0000d200100d08000840072280920207100d8a603204000704050300118800b4090313a401031005a05040da42d0400e404094202e403041c5103860400001032210910031034020ba00c004c100e9810040703c0d40e5040708801010b01b0035043c00300084c44280c81c1d64030485112015030100b8400c5100b901d007045452028030411482002940006210303100a55080c00141407005191611a02d40f91103c0d6405891b11091503003980c080390300271003c03c0b070f0615000500c4001c201c040c40c0e400000200304102d09007007294076203900d40810300190482d00040410034607580d0b0b0038075814082d0303030b20705980d04c4051502e4010f000104242d6440403540c01c100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 895110278 1250 895109028 895109051
    0x10030b070f05040b0c01090c0b09030105220b060103020c030c0115170706050a2010050c190e06040806010b0d0501080105160e01020c0402030106050904051b16170a12 73
    0x368106010040e100c0500b06440e213003a401855001108022483d52284018030003e01d4144a03034002d08132084446403200031220a250844100034003164400700c40c28130742c110940380c08440b1009990800910b200ca03680e80b00c01600a442281401b031524400064414290310065018840710f030f042d04d02d00303101140d80e000055074000e91440030300c01c0e54000340b1007005828003440c002c0c4081c01c5103080403c111510568011001208000a82210f40000d41414025000c51150a0b8801d02d4a40c07160308159001e81000701c450312440e1050140100d02d040c959180e42c3e080203440050200c0421212550f03100d031580310039034201041741c1c0c5402d03007410700114078020107000e1188269481c00000454bc20b40301411a180701e8100c044505501640c0401c42c0c1d1a00c0b24001140039141586506684000034803c2c00103e0780000c1c00e5100121518803502c162440d06001c54040c14503081c8000f003102d286040030f904000c10a80b280c9030400000410403401508120b200d06000c00e00c4c4020480d030707424034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 895111528 1250 895110278 895110287
    0x7090b18040e0f0d0810030503040617060409080307140c0616020d08150907051b010b10050309060705031803041508130201090b030a0e100b09060607030509090c0d0510030b07 77
    0xa4640020f60300030011300c0c08141e1041e140c481d80b1132100300010000564a40b521821a40f20b40c0002c2d00055028400e4810380164860040e00400c0580d400c105030019a02c2d80140360001810400c00c20030201c509003a1084442c0940380012041c038103440340360510f4010310451840204552000d402560060f880b2140240e65291190103521200b802861245040010b8810003d00308000d21a0510551862011285450701c0d460b9440000080040351142000400750042e101d00301040000c004000850a0100e02c503a0840d2884c02c28035100d03201c0d2401e07450840c1030750f020704083c1c3c1300c04140003070202040c00c10301140380c185071207440d034584900c115101c400342500e00c06030115010080820103031031030344000d56001c00d40039400180c443c0340d10040380c2049141c5c0000c2c503582c1d8551044200742d1074aa00200e07040300c0e00316856440e1244d50756000d842c41c024212407512603680707000001c840400c1001260940c2d07410500400403031800030302c0050056540d00040d030b4144090030000762003c1c001c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 895112778 1250 895111528 895111543
    0x51c0806060c060f07030e06070f0207080a032003070b0f0618060108060906010e0301090b01091d061306020706110c0f010b01120b04090f1a0c030114060307090b18040e 74
    0x210140c54070f41d941042e007444d41d1001903c000100f40d40c6c1d00408002d40818481180511310564803418040c00000d002880c001d02c4c8d4220740c40c290000c04040001a4001c0282048924140c003d0754180e944940164203500a40d10050200c03260802008a0810340b164580c1c403aa004a0300404c00b1418902d42407080c10046550301d0100d80941c0100c2d805140103c151640200140b42011501e805400402d003980c3c9100720480f2495041da0049c4202c100074010742800d9100144010707603051006980e10341c0e500d00a4080b00d00700d80101c0350b40c4103229440d0101c9039550781040050000b00041481030506611481099026024840503d00c0710360040c02001c102d4101695070b01c030170700c003030004400080501452055105640c0c81c0c1c1e020001d090901c1c000301046c028500e0500082c25031043c404852030042800654450800041c840b090070000c0c1000c12500944010b03860344c2e81c00c44242e0741243c0c140c0091002e4030012a90324602c030840c41c0d50401d80001035809101c0301e00d01006082c2e44008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 895114028 1250 895112778 895112797
    0x40308130f080a3f0306060e06031b0d150b030103020f03070503060703020f1207020109031106071e0e090406150504090b131e0803010e0106082809051c080606 70
    0x1d00740010304100700c07401c941080d0615603900c1c1e18021516240500a100d003204e420f4030100c2d4031141e041003d260020041101e188041d02d00034650301e4200303100e520004240d42c403071480c4a404940c8801d00fa441c0d40c00001a811101002c1c0001074a031b16800342503420900c4100d22030b5000104481d05828007045180803a54081c00422094807501400d038060340011501c090700442c18803400c024a900d048801d801340180703400000e0124044c0c2001411000b08010b40c01403a030110040c050219401007a01d0000000401483d0303c00403a080101d50803c41109880e5000c000041403009100d41544816102440c0900c400040c0d50f9600a03c415940003400203844482c00500040400c00340f690044103080c81440040d400025800503040300c00e00d100c4040c4d846c044088010300a03c100c5100341303030150819040c5680c05161008904201e19040119990180c50346070710070039200c00b01d030007101030103074400f087d950a14201320510b100781940308a02d00c00650b0002c042f840b241002c10480c2c03803644 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 895115278 1250 895114028 895114043
    0xc1908010e010b1c021b060c13080609060708040204090b0411040c17040224070f0b0a02071112070f080a0c2705060d0804030503030702120f0d0b06040308130f080a 72
    0x340d8503c0350100030b4018070629505003101040705aa4007806029242c400e08d2211003081c0c031011807650007034000048d81c00043e50b0360b0001007400490440014515448000340c500fa81c02980e0340d10120b000780424880040840e2401d205110400c0f00300300010403100b5080e02e08010301c0c10350b1001200c01400c181042c0040c0d00c2400e01113405400e080e110302e001030801e0f00c000d100014406540c01c002c2d44c88604190b4545c80c1c2c2e83c4400041082803034030340d500302081d110190304003059034551120b8103001d840c01340c1c410300069140c490f520505100f00802021807240000d0030640d0390f0070242c0c0382c1c6a0a00100e424011000c40414840c812003080041c209800c03600b61110000d0102042c010603000d48010350010103100a9800a0050070090015521a0002e581c80c5c1c1003c00700a85002c022075468031a03084244030a40d03041d49801c0c01e0343c8203181e102001188113007403400801e1861055400203003050500184040c1909090041182100e20312840e10806c09d0751442c0460b210720360560020b0501 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 895116528 1250 895115278 895115317
    0x60906160903151d06100605030f010e0a0b1c210906140f03070e09090a020108150604090f02040e01060509150d0f0f1a0f06040e0c1908010e010b 64
    0xe00910000580620f901400040740c0c80c003076005164140100901d400d03143d001c18100890025010030304d0008102c242021811414400d8044828030700501071221461b0360000000c60280da030741c04c00601581c01034428003a0b4440c6803e4190003001000c41507074005845103100d4503000b0104a020030a204980da0380c0c10207810103408581e0810ba009050301d601c0c41c1402004400040000158012815604c480603e00b42110a00003d80310003801d01119401a03d540d00c0507036040219039034800c1c02c031000c00c0040c43c0a02d00081c514055500920f1105151141006e01074031590300a105a99417170841996aa076a00d004403900e2141d00015174100070910390b103e088481c900c0c0904460020448e010503060400041c040441c1d1f03400740c0c512011501e40140030451244051640c800c0745d02600c4203040c0341203400224050b44280e10414040f14a18400580742070400c000b5902021240ca0b4214440c5540d8400240381e0f410a01802090181d00380001468524940c221006c10519216032180f0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 895117778 1250 895116528 895116533
    0x9070617060607030f051b1e2a03100f060e091f0b041103100e0901060303090b0a020102130305031c05090c040506010e030106300b040b04020d1202060906160903 71
    0x17098980c0e4900050100070b20080341d02000d049000c510008a0a0042a40344015107500d11010304440f06a5040e80055411400d0036120200c40b8080c01d01d2940c507074440841250100b441c2c04a01040d04800500d0004003030303040356441d044603007182c031070b4260354217a5140d240c2941d880b500501c1e150b001000701016603151200c4c03140c03c99122039800501c0043c1d8a4810422400680c0c42195440c110b401e0f500d03010b021365200140c1c21600480320344004c1020900b55900a41840302d14001d030307045414007041c401c0b032440c401d4044801e888840800140e90550300c0c505141d480c3c00c2400004072043e581d510010941030386100c0c1610922030600201960031044003844018100507200030b04002408940c16801d88003401001d000300210811580c0307064100314240a50107040444a98410601c1d89100c0413460f805a020340042e001018030103c1d07240d600c0007503003894550b1001003e00800724640c200d29500804c07124818807920040e13411580d540481c615401b804c10b03000d207004c44c08c0304005202 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 895119028 1250 895117778 895117787
    0x2030a0225030210031b03110405120120131a0d0213270501080606010c15060503010c110d030b03030d0e10062d0f051012050907061706060703 63
    0x84a0801e818100036070740c80360041400480d005004002207030300c85069100c03246009202c0c1c1c01c404010f1408008503500d00d1041e04092082e880350718450303030f03c00034100d248010a41c043d61303581200315002400d05a040705128000d400035080703034000b030122800020b500442d0101c00006000c18a41261400d400c09000f0b600a4100c0c0f1000c05000c04400302c0814135400041120300c0f411049503402e80305070444000b440c16180160050102c6822403000d1000598126103075403042c5601681c04580100e40c54407500013810707158041d82d4150300b0054201c0d140c0d9001848081d50080d11010b0312681c028895042e001d40300306a1071290140d1080090b0803d0050540c00356940756910b805841031807034641c0c10303003055500316081a01101cac0d24142500580074180c41e5116110038080c80010720a141901d2022480058881e29000d00907210190135801c0c403c2d44044083d2941040c01c1041d4240710020315520f07226070184802103070194414810307101050220074898140148950300d03100305d41d5021034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 895120278 1250 895119028 895119073
    0x6190c02030901030e1518010f14130516030b0f0906042a0902070c06110610051009030204020a170601020f030d0209060702030f03030f0604050103030225080d05070c050102030a02 79
    0x110580145405c0044a1b21030201ca94060030403404031f904000c80741c07000d4908551400d00171407500c03480c0010080768040d50180311644054070104801d0090701c141840b5007070240340c0c082c50580d1886088c000c010050504c0200d401190115034014250b81e813a8035aa56441c001d403400340008010043c00341c80418030300300c00e100c2d08982070703c10303483d4668400c80c880c16a0040201202c00e0b07070a191060060a0b4010407001b0340c01c604a009141c141083c240c04800441140100da010310101c0c111168210700400124004640c0039104546d00c1e210200020803001000c90014a44400003011580940c4000744180307420311080061031504a0340b4241e10000c0d480044101c0d00182d0610410300540d805020b294210124040a1949c1e854013045100300200001c013071522651414005001007940018203c508000c0c00c07402c1a180742c0700c016100e03d6120726034003280c054807800c0000103070700da0b102001c1c0003180d11480d5400040c40e143c2e40103984034091401d150005a100109840c1202c7c406080030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 895121528 1250 895120278 895120301
    0x608091b090a0938060312030a020903011d010c03110a0522030203190b060d0c0612110307090302030c1e0910031704140d08090d050f0a030206190c0203090103 70
    0x401404c8020f180140c1c1c0c207941c8800008a80003c0703040c1480c070038244880d4030390012080b8042c20000c01c4840907001c3c61302026100d00e082a07400304d002141350300d0035030043d03482d00344003060031201d0b00040540c580a4101c5c11124030000707040001d0035a003005400240e41c0c0721034180e00c0d12420440501010a1030004245400140d60b070b81070720010250b101405640240405085d07044004103050034405150035010b80303c0c0780170f03206103000c020128008540b0380c3d003941c0541c540000605038000c51000580211191115140e02c00801d211010b038000c05080f04486c420f03003d4551000403102004010f100c4410040184e003540b0b03403c26100c0c035083e01200ea100c0050b0300c121440715100e44800d0308141e04100708800e00c5900050a102c02c042d55074240c001098100c91505814181d5031b101080c500883c1d050034000e95400c9042c0c410090103002103981d150225003280c0b071212642c10004d68448040d11720028180d4480700d5222000c400303001e01280c040e1160029854020924011001020484401e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 895122778 1250 895121528 895121543
    0x207050717070e070f020717011d0105160302030f070309080f04081609290d02033012060108070c120c0311030408070b07080f040608091b090a09 64
    0x700d1122004201c5400c145a5240103003a003604180a40c02ca00308068040414014101a06607486500040070300c19140000c1c18241502003201140e4050101e081d18801069240c0305440b608400550060344121460700d0840d5442500d803c0960480c8006d80704448042e0b15440014140d0340a60010071005202c1c0c190503103801c03200d00001010390090b03003011b030007508100358030f12045021100c144080d1503980c004010800020800c11842c00b44003000540e6030820b80443c1445a681d055040d130495000b80c02d030740b41955250000d040c5c0135155a400c00004502e58004058064540c3c103496800210403850741441c0c030750800666a00d14005c10340c40030001c03c8800d804c002050b003030303c0e41c43e510100c0e141c16100d0400b07460003400d4041d84901c820300da5441031100304540c0e5400500041112003041002d65500c1140c01c003c4180e1182c01260000880009400030314107a2088500e441070300354201799100c0c00080350504890f002555200703036020340c0c040049010819035502c010f0303140c0d02c0b5921 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 895124028 1250 895122778 895122793
    0x409021e18100f0501050f1b10090305040503070605070b01141909090b07020607050f03040f0804080a26030604021803010606120f0b2b1a1e0405060a020705 69
    0x1420400301c0802c64070700c00d0744000b038001003101503140c0403458058002400c0542c1007900703410916010b80510b40e0f006084100500d0141030004060100d048520442034040c002d4040310701380508140d025124603800792041210006200b84600b0a55140561004521b10503134030701883c1d1034291034528001d5510158901400350711001c05400ca400600c5500f138086030010641c1000c008900c0d0041025045d034000c0010403e0705075008044403191048045c4403a140e8440b07050682041c084110010710074200024003050358100003c90005081c17050000158041c031000d40c0300d01603061005000642901480402c0141c40e0680103001c0d41c042240d804441d404440000a00b515856030054002c1008200594500ca0040c0101c0c00c150250000620aa41d01080410304c8945000c2c4140000d1080910103000344482d10301c84802c441d003240d096000c1500c421200400072005581e2007481d05205250111075050904d0810710454002000c2c2095550741010072029500c0b006044071180107440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 895125278 1250 895124028 895124059
    0x6120504050a1202031210030b0f0f01062102030108150115050a03180203010606090501020f0a0506060f130c03021803060f04061a0a0e0402040b011e20010e010e07050409021e 77
    0x69201c0c45813000c0040c8403187d510b1400e02a104200150400c0e406220100810101c18104902d0074112040f616182c245502c4150081454015441c602c42d10708c1d0000000058981d0009100010320f9984038903462241d9031b071030f40107280801649002c004141c040c070100c030b100c2c0d001c0c1e804101c440c800e44010b42c20003501c59000070308650517600071a01051103280300b4415540e04100242011003450b00900d00c9039807030b45a0781c2d52142e000f001c8030b106d07001d0f15040850300e440341d101244103001044400e2007051904400a00030b50030042405204070300405c10800341d07140c009000f90040d00c1c0c0440c188519115916000c0207401802c0141c4148444502051a03d403900f01402c4010103050000c1d201500b045c9c41004141c3c0e0314007036014100002035150f03031100c8200d140c900e6802d4802d8100030040401c10801000c5141c7c12500d54603855103010041048118190031060304081100c0945100c0c1d41c9a004000c11034407048030181d00560a0310003c4443e01109944100c280001800540c2049185 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 895126528 1250 895125278 895125307
    0xa050c19060510050a0b0c151006020c010f0e010e030c0d060f1109031b0310050c07020a080105010b0d091103030403030908120304080a0302130302030d0906120504050a120203 77
    0x300031650140311025014000e010851240a42080140666410461910b000685000541d02580d540c0b0200050130001000040040c2c02d1008101d81b1003590034a400310314181030350540d11824015018054101e0310310362280b40402c402d03006507210207405074041401140e00040d1071703628a4141c0300d0b40b600741c1c3c0e8585d100103400790314038418070340071480786040300351b01050313030901a401d40c01c600d01441816482e95012543c040074165400340e0000d01c030755802c006441e00c3d8400980c160075500d003070140a9900b40240090070058029180030303a480703a40d40c007690b089074030034458003850142c1030140c0780a1107100c1d0811105203015541046104840f000028199882680f046004c1881a4410444402d040c40303403540d9600c00d518058114139064442c0745c081d1050310f0449007015400610321100021071000302028640203011070304500c85000c0040c24583c014000e41004c40c000595001d102d840600030a44a568400b0262034208004d5588000a442c070103028002d50201780030388a482403c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 895127778 1250 895126528 895126543
    0x31b030606090218190e0417120a050601080f13020a03150501050a0e0f010b0702180703050603100504051908040b03150109060512190b041509230a020a050c 69
    0x101d0100503900c1d03074180c0504c1c00c0f001045032528041c40d000500703a210b8203881c4107004100c80748240300301c0550340c0710319003142e240c103c01444189248001c00c00d2117080c26089042403040749000d90400ca2a02e038940155043c210032501c103294208132800040a402e1499042005140301038413071110306440e0380c0c90381c100350300c0130b45041000e65071070300104001e10f03040d070300000144a134101c03c0d04242000814410080c005009d04a82c250000402000719140c100c90071039034050b24600154141064240100a8001a6441e5200f48a18414480000030714031405004035440401030050994004113000308010b081403e4405880501c00010311044103130055111782d128180e251b101c0c2600302c0014200803c02c5d009070040140074801c61864400c3d8140a80d04407104a000ca10109401007255000d4400200782c6504030381841207039a0f18120b1045c6d150292070a14106010420100320000204541402003c81050021000c242c03d072071181c2c0203143c080c40500d40540f80180c81c110785403810b0b81 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 895129028 1250 895127778 895127789
    0xb01030326040206180d11090c0307090605210a0f0e1612110d0c030c0e160309060f021219020f07030e1c030f0e0111030706050a02120c07120203090604031b030606 72
    0x26010300f20b503848c0100405a01c503d100e40114214100950000c094078143e00a62080c05000101821200d0501185004110b50409910b03168035212402da005003048a03484600c6500f4191046230b900c070080380d42858400d1900412028a10307000c02001d0010501400341c4020500f41c2c0ca8881540307622214100310703800342d0017090b000c42c030350b280040c3d14040382d40c00040c4104910061051101e9140a00d4681401c0c504d004a018260b9061090090051206020a503032001030303415103203082c081000d4881c43c1401040c95803ea1480c02843c07d9114200d40c0d8007482908001080010b4092202c03840600e00207082039801042e6413540c000d035603985000580c01724201c0c2c82c2e04690180c0c0720058080c01ca00a10703003c503813111540030b410307602d010f001c600908250302d900006803c0b00d0250f055810300c1c101441d4442c05414500a1410254401001500e60500a1407a52111030001040b074030f0490b030150115150a2944c1c480002c0744004a042a4016680340c0002020602c24001d20b401307482c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 895130278 1250 895129028 895129043
    0xf01080a020d020c0604050d0c0b0606091302031003060e01090308071209050102030f16030e03090d030522080609010911040c0e120106080d0908060f07021204030b01030326040206180d 81
    0x202401d1032884d0203200000c44041001c00480c60740000e81050300c2c143c11400980e41e48dc0c0f503032400710005003040083d1a003111854408000c020701d002c140c814a0045a0040d5030401400f094080440d090351240380303020340030074401c40105800601c10300c1183d180c414038040c002142901c960718142664019246a00b40d421504244590a42910803450300c01c0b2142c02c2c208040d400c2441003684901030621503620034220390f031807201418001c0089035a003c43c2c5182007a840c8a01c07a0801400c04924000c0c103201d441080c1c00292041414403d004d0302c81d4000240100f014545400c2101400b0844007050030000849420111034540310000c0d01039162200000c600c160404501d01e2800c40351100520402041042c200041800400c9503a0441c15001c0c03260011750f20507030240c0c80d0920083c1c0803000444006800030901081c0c14060b07041e81d2203540d03a0507501c440708003043d19001d04c100b40400c21074407000100d0010700e0300500402500035021980d406174407881002605400d00700100b0356541 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 895131528 1250 895130278 895130281
    0x1603060902040e1504080f0c0a3c06111912050a201b150f010b0304110d030219060510051009090522110f0a050f01080a020d020c06 58
    0x500c2e0a001c2c440d18628440024201031001480007182000c01500140804000082610700d120034102101c031244080303c21250468803510b08000d44082c400e4501a0314144148100340c03113800040100520300040030444160b4450f40ca400300105a115a01005e000c000c1000000d4086052490701d5040c0d110b0701c480011260010480c401d586000307190054403450002c413a904460803a40c03102c6900e41045a0342d0f2503100c500f02c42c0408003c282403132891440380010742240298440101845016040603680c000c0c1d91b00c001e101154041660001e145c00c039040c103451381038105005a006030702e00901c1198402e600e545545800d5126544040c3d41c1c0d076071500d0821100c841004244001000140c401c008054100700b0003c107046550f00a0f038889642301d0b0b000c582c04105071540c2c104104503280e195445540c0c40e1030100300340b030642c40a15020b0002c0390740c582510714110342000101c8001612206005020500449540c40020b0028040c140c0c2445500313030070002031014100342c0503910000c0c00c4070b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 895132778 1250 895131528 895131533
    0x50d0b0705130620010e07060e040f0207080a09060e0a0308071a0a090201090b04050901290d0b03211c020d1407021e070b18030a050106050117011a0c16030609 70
    0x2102c1c12611072040581c1040c422412102c07001070030408880d423602e8020070b07184045000401800d84c2c0e050985025002054080c1480703003d40040550840703076120002103079030b1200103a40000719860078a0f44021701100400104003110028100544294440c4455802c21610f501080d03c040d0380e081549542d95014201b10358100803007030003821141d80c005040074540400520b80e0801401503107181c02d0124200101d07401c08540f4071400c0b200050625849840700e080700d81c0181000c0040a02c244a03003001e056042102c2d400c582090780c13071030102510f0900c2c01d040840c10440c0340340c80c0b40c0c0351070381c204940c5000103214480c5144400d0100b02c089020304140d80c000740b8010011008540d039081c0c01c007220703140900014800c01154600500d45840348040740640d5201c0000000c0c141d01801154022000c001041d8850820b80754262151001702c04402c0480a0003842406019546004a00e000161000c4070001c2c1038115500401c42c4c0940202d003000c052503181aa1040b0348464580c8100000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 895134028 1250 895132778 895132817
    0x2070c060f090f08030415050c0304120b06060306011e0908030d020406030b01090f09090602121906080c01020309040b030307080a030b150f07110a09060602070816050d0b07051306 79
    0x2003c291499142c49414003043c0c136103d20a6109101e003d0140400f1079000303600400590f1200800e800599490b50740c0d406c020150701080c80ca040380e400d002c1000280c07941c68030100340c9000740d01c183c5d503140c28000f503544194041a0180c4240040c400a0754001542c2c0034208003e241c03901d5030b580d0142c0c9403484c1403405000d0740c221010341c2e8140100303141d090115255001b002004c45200c4840850b00c5006420014000d1182c2c0524041c14602c2804100c1c8407a1450895114241075a40c1000110355425400703881e90f803105102d0f4016001005103450516060b0401128642c0c0201903a10382649540c88040300d030700088000c404252100d44190091a00c0d144030100c1100c0707402100c1c601554149128201d00c500d04000745580054150903060740c59103180709020304203052082003140d486d5100030755030f00c54911030714040e4490114441d40000450408808440010b8055521240d080d0b030742c9040450001c110408001d014440c5500107100c51494000906894036240460004c550301040d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 895135278 1250 895134028 895134047
    0xa1d01060b07020418080f13050a140907022e1b0f020f1c18030222050c04080c060d020721110703170a0c0206030405010b1c020604090f02070c060f 65
    0x30055058001752001140403102194039008001000340d0790384d00011070407a181c2185400a039081100e0400100e1180901c140807070541e4011a0340b559691748203c0106d079a50110003c407009048400d1a40340c040518141e001700c1426200310104207110a03044404192007400c00920008a58895250722150140310031a5692200c00260200c00180b1040c0480c2c50107030b643c0310f02005030100003010349940404090010b5a8005c00c50400603000300c003480701d108407600340d00b5017007440c20000ca054004031600711411079281802401d14218000c1c00c0148503009000c440011903020080c4000081003100c1155002d408000350785503240c0c4e4a10020020b8540d03201c43d05c116448100240081f54411040701b07204082e900c0ca0a40e04e03035038200100c510540d0b540000b23403c140c0c080180400c01006400500c2c1d810416590401c003e0b00c00410000340040d0348001a4008408000c14021080301c0e0704809085489054007603d810413560703030003034441a66400300303001482400005039107035485229003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 895136528 1250 895135278 895135301
    0x210c060c190f021c02010e0709060602010e0303150402030712230c070f061e05040b0105030c2209110d0506060f0a06140702010c150903030f060303080a1d01060b070204 74
    0x60803186001c400395480d1301051416403008400240b000040f0b200b5040490070244d90b1094032013543c2e0f1518560b000d07010070702826016508000c00d0024480000045e80c1c42a64012103580c46139a540c2e0078003000350300c050620000c000a1035650a84000640280c8046419211011352042100b051980c03080700c02911000d1494000c102301c001088225030401c0182e40c0050000a07002462010071000695080828402500303110070003061040800000d4100d0300b056056540600d007182c200185c081b41404800806e00c1d0b00d464a0100c814181e008004040c850460940c2c2924050002a41000c0d05a01120b503a800242001543d08041c40c0f802c0045400340c500400c41030504e90003901c0c000c800144041d06000201e854001c0d6845040e0b1454541d8000e111016541c0c400118132007d86a60f0358140c0200c0c0c1000d4040340da410791032242d20106c0350159641c200980b0341da1741020241042004006030003001241c580502c090a100b030030024400080696601c50303040c41440b0541d503111812 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 895137778 1250 895136528 895136537
    0x210a120e100c06050c04080d0c0501060e0103080a030216023601050d0b0613060f0608070206040809010507020315090a110303070201020a02130905060709061808210c060c19 76
    0x5000010b800100c40b074142c80c0e0000c004a2682c0c1c0d00c1d607a484c8980101e0b440440343c1e104601c00c20b2549a04814002e5640307008400034041540c0740c00a1840742c100c28400101104800c21844039818030a501a2140c02020b05020050145507000940000c4100d02041d500c4180d03c41446480703132850b00311700c41c540c00d0b0443d521400e600d02000680d0806030072002900b040540700004006680398041c04a402a05c52000c0100c1a00c13000c14074180c014500480011503202d0021565890000030200d209a503c5501a442c106158004480d00e40111808a8041c418802c0c2e02da030000751110031a2082c0b08040007414200b0040c2400c50304140340c0110b560081d0030401406003d45d03404900302500c03d805a0340c100c01008620514001415040380c060954080c003014449950340c41103110041b15038590381c101d06840b06500a003004940ca10502a040c2d1201202c40800c111520492004c8803c0d07441c86070030a0101c152341c2e401d100c401c484146002c0c0c1d0024288145030f0003000c0c180034400c900d150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 895139028 1250 895137778 895137799
    0x91614070c1404150b16060e0f100509060612031315121112180d080f06040b01200a15050105030715020a0209040f050f010b030d030c0905210a120e 65
    0x2000004c0c0c2c1c203800b4640780c2c0b100008a62401070040710028450613440360f8100440d005640c0305a03101d0410b401c0701541c5015030b5074440d03100005400390318090a51540600800c0d2034140800c0307800000d0300801d441e0350006001c941e8035400a0a44200200306400711003513a50401140100300203000e02c0580c50003450406001240766010b030a44c1c41c8641340d0450791406440c0c20034090700c00e20301c0141050f12441503016000071944c0c84403442e40101600e01c000c1e02107855101c2040103451000c0c1d451800100103100d0480c41ca6003100c1800c148001c2c40c416500c143c4ca07203403505607136829103d031800621a280d400401603800c00f084a0001082480704c1e07000c05a43d020f000a444241e170b10700c080d205400000100d028000c4100c4007120496000c4102d502d100010703682e4a0103400c2100242e4400c1c012101d6002483e03010b8064003283c4816603607001402c80c05d00b020050740000841081d60030a400e8540036150104c10041e1031022801040380111204e081c620050030800080c02c00c0b07024040c5480d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 895140278 1250 895139028 895139051
    0x2070b040b03060d02030a050c01020606180f0619030507081507050f0306011806030c030b0f01020c270c03040507080715260a0e070b03010302091614070c1404 70
    0x500340d40580705491245a600d0b116040000d031031092030b0308007a50602801c84a2420880c0c0010380300c880d8102a0287c03403050b91000c3c204400c07071407501240c50280d00b1100010300c0c09a48100c076141c3c0039000801004a00900c140d500e21054217a4000b140c2c150300184042c40b8800d010000c0090010b444485000c0618013840c005100d0300683c1040c04030790740080003003080785e805403141509482e02d0000303480c8803030b54480005024001e4503c2034008240303064000841818084e51003141d950341a002403108402c0c0806106c04484100c1c01c6018190103024554101d01e4154125405904140c05540c0c484c1841c2c200581030040340d40c0041c13600d40c4040c0342000030240a00313021138040380509010007004200c00340c8070303140d200c021107070740700044001c040002407500c6901005c600c5480400311a08961a11001c0707640d84001e00000e90b10008040010b0910700502003110340b0041103280c154a03c03501265040040d1700310003022144107240348001d01c1401c2c40607000740d52400048900b8000300f103920 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 895141528 1250 895140278 895140299
    0x16020f01092a05030d0302120a090b2802070602030103021002031e070f14070f0803091503100b0c0615030105040c0312050c07080109050c102111070309030606060207 73
    0x1d00703442d141940c100d4070001e06454103204080c001c0ca40602940c0c02d40c0c600c1440100254045800003a120200c00080b030043e850510480c05032a070300c9902c0d120207031202050b04400c001c41d19605080b40c80c19400d01800001c41e8009013030327668400d10700903841e9415407040240d10710442505008640c4140002980140300030400140d015803c0a015511002410a2000c00c1016140a0210280e2410030098004001107440c100c035541c940440005844914a64686c4161500d055100d0116030142c041c6450b00001150407a10405950840940d50300d48040c5a4101d0300da070b0701b107a03080582001034680d03009604414203101107000300400d14117607031808000384071400003034014a00c540200540781d01400859610b0b0300b0807411549001d65540d040f9010b0040c0110031601801070130070000f001e0809455062b8a0ba01e5512401003141110017000d124644c01610b141545460f40010342e10700e080b880007081c1d8103000ea50b07010002030075400c00038107032015544080c04540c0108070801c00302018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 895142778 1250 895141528 895141553
    0x250b1809070507020414150d0302060604050705130305150a060b030403081909240605130e01060e070c0209160e090a090503040e150a1a0d110316020f0109 68
    0x480368000240c440c604111080d02440c880250030902d05110141e0b00b000750500c452040060f1000780244800c0c0409011101d110600e000700503a0280010490fa45055000584d20035242c1ca880c50030a18900c00f04004030510b40d006488580056003401031400000340c0155008180402c248a044d1503c130880d1322703a100c018009410882c0e1480850a01d140558810b92002c80c20320051042984905082d0444e07004000c41203003140e003450b41c0050f24080e500a00303084550080042e04003000c1030300780c4000380c80840d207a02903d560380e0700302154403440201c3d928010152aa41c1b03000b5258988180180801c018090940a04e64902c07452102d40e030000c010280fa03441901c010707515444100105002d4401400300820a010104008c2818400d03500540c1c4540b420760440d00500c881c2009110314030f45503004040ca00030074240c11032203031602d15004240300a0306100014030000004600d0005401c1620200c00300c4804000d0f4810290341008801d00310b00c0321a008014074035665403820420304c10f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 895143884 1106 895142778 895142827
    0xf06021b1902030a150608010609021b2a1f0309030f0f0f051b07090606030e06060a0512070803030a1b0806010c081803250b 55
    0x141c031041510355006000392050019030307150130fa003c0d55003072207800c1480e813204000154074009104035001818014401a120017101035007401f1142c003810100c00550000f1202c0d004140e8210f030044580384c40e58154031042c1c0e0701802251814000c540002e280c1d140c502100c00308180c00d5042038002078440c2e40c425040c0c01c46081c1c10f031040c2884803015400540402e5030322004901500082820b16440c0d0929182c15051543c00e40c41d244158005001840d140c1d03404018240d01809104a00040c03c8098007041c68a0004528010082d12406d44110801d8000c07800510701030202e40094031030351003032342c0d42da1400040c0b001c045c0c89144059203501c03108040c08800c0912615501c3e01481c0140d4562502020710344500c02e680c0c000000d108125003480035904126901000219650880007206407801221a881640c1e8661039038888150546c081005a0400400100e12500b450 = true := by decide +kernel

theorem cover : BRFrame.Cov 894964028 895143884 := by
  have h0 := BRFrame.cov_init 894964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 894964028 ≤ n) (h2 : n < 895143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
