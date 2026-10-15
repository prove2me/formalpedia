-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4571
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:03:00.143988+00:00
-- url     : https://prove2.me/submissions/2eca1334-18d6-4c5e-937a-48704faaed13

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 821942446 ≤ n < 822122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 821943696 1250 821942446 821942449
    0x2150a0b0301090b0405010e0c06031636030b07140702100203090a0e01150503090c0405040501060906030b042006070605060a350d0f1d030607180e06010806 69
    0x2040810859039055403604039000114484c80c04003402240144000906003070006910743c940190321903018000d110030f200700080c4000c104030f0468681c0050800307032032840a886510040c0e145070410645a54580b00d19805a030003002800400d4070700c80c0c881ca26041d01c540340c0030340d50350b0851003d003a8003003020400c44005051803200c000f204042801100c1c246050b1000040d01c66100c0c2c3c1000d292159124010020094031981024076100d490030050b155060841413241c84190590b8464051a1603401150800c00e09510210040142a00402803940c8a01d040310b01c20b40c065900791511a512880000da59030200005c103002c11340204060301c2e0195694031800a4540100321660220840b8030010300141c48941100c09420710222802c400c8802030003103811031844900103036640e845001c122480b143c1240c8414080782183c01c0c0245403034050461a00c07008441003140f83c16010311428001c0041d0800c0b00b54210850021326102c6d01030300c503580442205412541c05002502e000c0108509 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 821944946 1250 821943696 821943701
    0x6090b0427230708251e0203041415041e0503060403030e010515011d12030a09050102121c0203090c040504080c0c01020c0a0b0f040e130201090602150a 67
    0x244640c241035200c0c49555210003400b11241125003441c59100150640d440d00c281c82000390707108109040500e25030402456049800e6072074140c1881101000c51040c1005002d072841d0340000d0040c4160a084142c00c40e0025140d03085842409050300380304110030302501e0816070010315030081120a81c02c20b440c01510050b03000305500c0c034040042d072400c00400c46e510300b80030b03042c41640a40c42c045684454840d00d82e007110002054400840b119015003c450380c1d20641c4006130b189402c4920043c040c0407000200c8215410300110014400027560b815200d030000030007070858100b6001e541054544440b10324031442003580181900075150400e00b00290980c0c06141c0100c90401114040010b800201d0104d40e0192010341d42c5220108055003c40c0c0c040282c1080c0d41001e10182c0620140039001c903400040c4c1c0d0003025243c003001b203802900101180162002450b080c00e04000608003080d214980c0513088205a0000f00722000202c0c0c443e0000031100f402403068488194039a03a0380040100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 821946196 1250 821944946 821944979
    0x40c1d1306051f09020702090105181b130905160503013f030c0b011e050f040e121c020c060a0c031b0513080c06070f06090b1f06090b04 60
    0x403500381c05100c0003c0c0ca02c142e0041c90291000d0403006a8456040c010003d0500050340a40d20401c6101c08200c0160a1902011f03040b4481c9081100c60030052421182035000d42038000d40c4808003a40005a0030701c140e00050300515140c10780d400d80c46c0c00e111007164588001d0182e940500600f05c007802c05214000b0b24140c051114000039046800c0a06001c00a011003a0301a00000c02c0d9100d00000e01c4460b251140c01003104000c50b07000b02d01c40c1140d001400086100c0c0324800c2e4640c541d51412510f544c0c001c2c08411061006550280c4040800410503170004050600c80a0803080d004020041d580308840175004a40d0007030503a13a883c050380070050000994585c04040d00c2d081c200c10344500f40603242029640f25110a51031303166241d050108d240c0315500200c038552060382008499241c60381191007968000241c0c0d80c0d0580d132410b1440280203071680080409010404028005545040c0f20060320032204c0001d0196560307020403620700d2124094032078010400c2000304080c0b480c10200c0b80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 821947446 1250 821946196 821946211
    0x30f0f070906111920121f110c03120c030103110d170a09090b040c170408211807030c180b04020d14011a07110103020c06040c1d130605 60
    0x80c0541e1030b9a40c0c0f0344d40304603424412103191040160804165903461403001c800310701074503a11070030160b58600e5991404001074584c000e01000d031130000c2110071034000303010034200916905d80d20341080148594070303403000c020a00045030007000700e000041504112412290040340c1152107201c64410010f1840060100300c409084c4400842c0300c1c40340c400050031041629460f2005c0c0c0f00d150002c9501581c400d101c00c0d03481545003211491105400001105441c084089000040e60b01c0380b801c14101c0c802c200320b21904a0b42402070b450f80d2019004500d20900e000c0c40d50884080d50481116560b14807400002e007003036404801442110403261a00a402c86039200c04107001881e0b201181c200d9110209004032151a4401c4413541c60000010750300400c12007400180e00b90f13100c0380d264201d008038400101910540501030080e688240c05443c80d2014890584902e4102850010300c5100648290000307100604804081d05400030b03000340c072441130303850b181542c210259075400083c803000f441c18 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 821948696 1250 821947446 821947453
    0x90608031b030d05100513060e13021203030a0911030606010915120911032802010302090a0504021b071a0f0706090b1f09050c16170f030f0f07090611 66
    0x320f074908100d001d900c4c042c017480300200840a041074103101c40100c0700b00504c3d00c0941050020020920340a500c40c0d4806054047c14039141e8061001482c0200e03099280b81d420712005c03013800004401ca42c40780914512890408c441c4c2110321040c0f54903010101c0d070b500d0104a6003a0100035240b07602070482510521803030b00e58175401c8072800c3c0208592a004054505001105182051703040c10081040701e0102d0a1900c0d51858030700c1900450301e040610000d0406070041f900301c21540b2018050000b40c40300a105649505130200c50810210114400080c14801c0c101d0005844481e141c402c0c03046d881d80c082c22031401807449551030907540407080071981281e46248143c04541d42201803405110b003489882d010b120340b8080300f00d0081154100c2903982d4a8042406a4034404a0880f0024500d01810215031030440c00d14402000c40486130140807400080c02c00602d11890300251300c11030500594a4040e154a038150078088011203200c0301081601078107001241c080d074004030410790113200720b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 821949946 1250 821948696 821948707
    0x10c021e040e01090f14161701060f0e1504020408030a0503090a080723010b060403020d060e070b120112080f07081c0507031802061912020a0c0c090608031b03 70
    0x7a203084404c00c08090b9140b010181108041100d14017400039552035a07001820103400c90340710041401054030559400e00c00c20b0042c0d104846080d041103000703150f90a20345c05441ea40d04804d2902c030004680420400c0903900700d0241918140c0f0a40c1c0031342d0004401141408007400050f18217a0016007101103070301c00c80281e0400a04040001d004d03940c8288190710078a43e045031101c1040c108001c181000e0390400e000076003c1c0d1662030590702140c0c2c04031070803000c2d81524244240188400000703131846024840c0041004007003030004012084011620705c4050780e032404182544050568003c040480c00c220700b00507880d54401400201e405400301a00d003c400c481c0b0a01c040183c1d8070b508801d291507a042005258040c8078135074050b1a1807206901e8080b45034006003c51040c2d01c440030860100014245040b4440c00e076080044900040c219a07909070f50001030710062134000100c03180d094807880814045080d000d500102c900500c0214101032000903a01900442c2440458591209102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 821951196 1250 821949946 821949971
    0x504020a0c0602130f09020301181a0406141e090c070813180b0301090201120f060f0b18010c121b020d060b090c070206120405030405130b0f010c021e04 67
    0x103090340f103600301310084400d15000519260413040da018005091062004111013170f10b4445020a0800781d040004503030400d0f550b804401c2902c80806604140b41130f402041c094801c68802d040001c0860301040380382d00082d003020010002c0e20046030080381403000b0a012140c01806003001910800b8403a0401030030420a4024403015846180c100300c21400d0341e00604070901c24100350f004180d009001c041555000640740210303e5080d0311031290360b800200034020040c0c0c030600203090480050740420790342d80003034807a9800003160000c45850100d8440030760741c003078006060324561010a40310f0410144130288d0b0500001031061310091100c40c004c1c8c0061b55201c0701403280d18030807400043c52883c0001884590a40203180011600d8208000300c09a545d240a0300d4041d84050305801c0e0340d41d601d10303109043d0300960703008503009915006210342007031241d0020480d4140a0b2141c0c1030000c000001151b80c50100940a90010701148400e90742c00440c08181c4c14408020340081180c4035800e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 821952446 1250 821951196 821951201
    0x1523040f3302030c09010e04020c070306092a060c1a0c0c0d08071b020303040e07020a050f0303130308061203190201050a020327011b360504020a0c06 66
    0x11646400440701c40601000e60040d016030301803001c2840002c40c29880c1c409101c800301d210ba80d182c41e05002e0046074020f110f82c0d40e03804441c03005403220140c80400790382c1d14051000d4a4000e40c1281c11807038400c280f1042c04680340c010320300a1b02041c1888a194a045000d40b14540882001c4c0e0300d031841555074140c140c55102c4514015541c401c04155900c00c80d000c0c060400e1500c080b4102000075000c14072102c20f5010710340b04d4116940d0a62081c901d071051001a00d1849194086107926140313504000031903401140301c142150003002a100c803071006026003510b03444200d401da040c00c40c0c00703801c0d02c2c0800d12611030281c1c80701000d00148151241100110f2850704402070f0314003001d1165840048681c0c0c28051380e0b800001210043d410340c10110361035074215a8402d4800001c0411003680205403400350041884410384800e16a0854100c00b001031440741720f801041081400c0c0403d047d10300c000d440c0b1130408018100040b4000d94186000c11010350710604450f41080303002410000032980c0351 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 821953696 1250 821952446 821952473
    0x9130516030305030403020625030b031c031d0d0c060b1206010b0d060501030e0a02090405161e06050c070e060f031c080702120315041e06031523040f 66
    0x1d88843c1e07100c1ca020f107002440c110005003142c900d1001d844540221414a0803042403260207800c0104e4040c0d09400402c0c90f2604a43d91030b0710046680d181c4500c1c981c2c259228100c590000f40010120702c0303010410994592a2148500004642640f5400800c2d1181d0005417083c10007061000d1075410720320010f2a0074002e0b000055243c80005112011821600c901001405c00303007014000e0500580c0d44513100d1001c424007074040d803409030000c0d040000a100d8852001c8404507048041601d40a2081d8289070025040604480c10440400c0d054040c8056900b2560700358010700d242400e0507440391803010f024000b40d4001c1c9000e035a401d02c668081c050f20f811b22841c2c242621500343c901d60020076076140580703d0415504a05840a250b03000141102c0c2c3c407040840880c4007000d0510007040007400d83c50f404003084501042182c0d80d40b03005030060412070f4049d620071081c44001c500300304211000d02e0b01c140341203003401300021510004134081d2036001d4050707080080c170340006845e11080e21000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 821954946 1250 821953696 821953703
    0x30206180310090b0109050c19050903060f0c090d020103021603020303040c0b0901080406021c0606020a1703060604030201030f020c0118052104140a172a0913051603 73
    0x40c40003919a80c10704000e1142c02c4404180b050010f02c0b41d680780c4682001040c00f804440c42c0d1503a00041108504c5400c84030f000855660490440c0c9110130000e0031904141c40844c030a0080001151305056046216030180461184051408a0301010800c0c0c40c118690101e0516400b0b0000a015400112000c030704280650003a507601d152903c0d0151180c40d06401c40703014842c0034081030700c2030b980c4034003155846a40101b0040c0c1e60002451110318844240300142c0c071b12414094003007007565010881142c40c134800c1c040c40f421610321121111450200b16811030b0810018030040003d0361007034001282d02114000e0051406800c50806030950303120500c03d14003050072855000410800700f001e000800700a480d80d90901c00e104c0c031090b0341c0b81714500c1543c82e240b8400400d20603a50320303500810010b00359501182085290442c00c140c80e26508608011802c0e06200f108900700e1040d0f40c3c4080766200104049440d5990382805040300340700038010b44040c80750302041d200882000384e02902442c007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 821956196 1250 821954946 821954977
    0x501060e0414010b090118080303180c0109080d0e0a0f030b01031406130f050c040e010f0b01050403050304060804031211090f040b03070b03060d0804092a12090c030206 74
    0x2588144001d0b1a9404000e03075940718050010001c0b2490f0405445020809192a01c41d212001c0d8800d40c001c1141c0d000101240400410f010f03681000764510004004010140c912000701c9200642d08483c441c80740d0304042c2c10034081065607e120320703012038000100034900d00300d481d200c0041c0c80d920701d0707160070407a21131f101c1c00d0041c0240184220f442190b0b4180d0801042c080ca0300c0548444004480e1800400340b002400650301000b9060014051150025204100c00d071613002009020b0403500f90b100018919014220301194826401c907400c1d680c01c40000d600e05468034008031801c0390010416001c00201640801c444001e5000785400ca401c18207000380c4030b030a12010016500c1d8400942841755280800807900c03034a020461038101c0b400540516105d80e18dc0f40458500d0340c11101c028407880c8001800310319031507141e01c400e0f5448400c1c504802c00c8000e141c2044140c4000b0040100401c1540d0b840d00d0010300560010000c140c800d2003111074207075999010840540250b81101c00343e81 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 821957446 1250 821956196 821956217
    0x801090c09141504090609080a0c0b1e04140102040f060905030c0405060d03030e0309060d060312140d0507030204030c090209011e09051e0307030305030405100605060d0f0603020301050106 83
    0xc400e000c1c0821000b003071400021a402c0c90070025500f0300001c1c400c6400b4585415041c1c09000382503200540540c0c100304500d6484c0300404005100d40840c800031241000c0190210300f0a600408600d82c0070122648401600d494586032000c607500b404008590942d02000041120342c00340c55420010314664981d41815810b00082508198529503158017030340c6440200205651000074900c4074a400d81000540c0100070641c8034210310562981c0c1ea0481d0000030205000c03030311a8095070171030b402140e08220501724814211070919940c000f01ca580f12040c890050030707c07003d50005800100383d040040c6015540d64440f0041c01d00d40c4c1c4003481103540414014450350b00310385203240b101c08001001202c81c00f0600064541c5000340201c6029200c2c920201440c0d040007203410b9071940d4000c0c1100d40182da00e2030010015070045601700c40a000d40c81c01c240740310701c0d0b60040c20705482d0024000d80c14020394000500c0106003000307200d003415485070b000201586080c42058040c101958541080c030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 821958696 1250 821957446 821957459
    0x80903070f08031b06160c1703010f05040509010212071803020907031d0a240e011401081b010801051203120114041404200a090c0201020307080109051009150801090c 73
    0x1c4c821841143c02c4e00008204040d0380d4124010f542c0e2600181410140340c800b50a084024140309a034141a900d07000002140040b503101d00c03001140c40807a0b0a00050703072030701e1942c1e00343d0140e1206201e5600446020440380c0e03009007068407110402040307003002c040d5260001410030605a40c0038002c82d44d40d0940a0001c0700c003400307050941c0359181c014010f405140d80c030b9451000b00410300b10924035410001e695004140d4014401680c2a50001d2041102c01412015203800038410ac400e1841000c0c807001c43e05034146100000340d1016100d4441aa1804041c801070711280d0852007120700040210482803e20a868207020b00030f14100c1c01511035040092204440b84010f2890149021404000015080c49400c0d0003003044041514801900d0380d010031005105034015564440c10030350038121b259030550185101e0000750f51000610f9903282d0b4140700700d0784241ca0f40e412040035160140032910b8250014030b8030014000c007400016642e840400d00f1500d42c210708464880000e042080344c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 821959946 1250 821958696 821958727
    0x1713060506060a0206010b1b030c010e0c0108100b070f0501090c051309170702040608030309100f0c0c0204090201050405031e0d030b1c02010e1507140f0a080903070f0803 75
    0x31a60a80b01c1c58641021001c0c0a5554501441036840a4500050303011010300c8900302820403102d0101100d4442041d15031690113000700580c011f03903510451011010942c81506420301503085042194040303810441c3c00162540004004c1e075a1510b4000388100180092040101c00d500519148043c281860104514852200c91010030b0908210450001c80d101d0889641d12000700340009030b0301d0a0a102060150000380c1c0441864000481000541040440c0c0030880d000d185004202c20742c884a00032040310b000b44205000203030340c9208040141043da00141310b003401418224200790390790001a1500d201081d0014802e140181c20022907103081001d030800d181d082c101804800c10200104011b52160902071910305c00d0001003009590103010a804504800f400c07040d210b0103000742c80c91807640992402c545000301c0b03c92029000002240c010401c4680c40c018009402290b00d0b25006a006007452075414002d500c0b0028030410941c16a0f801008600040c680b50a40007861121 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 821961196 1250 821959946 821959951
    0x314090d151b020706110a0209012403091109040f120903140d0c020616060f05090f010e030a1202090a08062a040e18070324110301050607020117130605 67
    0x1e007442402d50a010341900880c0786400e441240ca4003010014452a45500d050b5520700c01039008a003400001c14411446441c05500d01010781314a40d00c1080144102c0c210382e4855005422021403900d503490502e0807101301074002c0e000d00f0540030f280d003864507500e0040402d0508031000c01c00c0b248081003000240100101d01c4c2030305102038201c80201c0748021f0304074100d48400138494074000030509116549024a01d8655401110030401520300d441982c0082c58142c1e101c50003403082c00d41c0209240e505002c0c1d41516140040a1801c0070f60b0120240c0b0050251404101d80c19004d00440025444009030701000340380d80c40003009581411000c00c40300035070107070a0800640300c2c81c69659040b0b00e800102c07800c4410404510600b84d6441d440e1a40403224418106211301407540008184a072400141a001054824a00a00692107030000883c0c800c004120707050182840100035901d4480701900781180181400049000203149446c02000c04640c0d0ad44000d62021403042803002134414251f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 821962446 1250 821961196 821961221
    0x50a03060e040c06030513051b011419080604022203061d0c01080402040e011a0406060f0c020d03031e020c06060a1d090c0607050102220f030314090d15 67
    0x10118186038440c5000c11943d80141d5061549a03004180d141040d003210000aa8100f0182c0c2c107017800041c12441704c8160703110700d81d0006664684440c0c6d40403480049540803441c0c00c3c22600b00d450703064019540d1841c01022039030b0096090000340510111100344240005006e000403c4060861404104440303a010345200701024150240c043c8020002e04003503580c00900703101009a07194400103000d40050a00c405080d400c080d10300c24055135a951000590b042140c040c00b503582c40301411118940d645d180d510000c0e222076007030805030510014503440c4501030326002c50000744240034100c14080c1245441c0340f0700d50001e05000c0009080c400349030046000c440b800c0f4914506000002e2029a10356014050310440010030f5040d001040000007580019103007075110791444c02c115000b50030402d100c00c52078204c4000d100c0520310b074603a81016122800e5100d2071450641d01c0c22940c1c0302c0c104110a40b040f500b0405000c1940d951656444024400e1f0346110783ca021039446002a2020b410501c1c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 821963696 1250 821962446 821962469
    0x60209030d0201060e0f060f10020615010822060e1516020303070905130b120f01050105030601030302060f091504120e0109030c1a0d15030314070803280c050a0306 72
    0x1849164500c440c0603030800d03030340c42290740f680e202c040000d00c0c8c00701c8110f00c2c1750b80141480910a429038010402d00c0c4941d0710340e00340d080e01c1c0c0380031001512562400c9950b0012161034041c18102c0030004440010070500030000003c1c00c00030808140e00d0070381c61145083e0001c4a84d0108090728460001109203101d0600c041c50843c00c1c4400080e066441c5401214031803008070f40c81c00500e60440e44611a4054010038111982c4d01d01d021860b203514120b0307030031016942404008501070170006003803412039034142d00411150380e0300d07501325441a001401c0c148040c000c500084100c034250781d481901842c000d8030680d40700c00d800007000e04001e802071100c0e418480146401c202246008003400101c038001c0750808403a40c16440991094440c01c100c1d090f10619110642108240050542017901d101c1d0301c1d590320340c001c0c402c2c1081c0e16010b4500300070f000b84010400210307000030548220007004041c028002400c980380c0507407030603103201a10140005001084d400f4402e5454054080101300401ca0f1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 821964946 1250 821963696 821963699
    0x5060a060b09010f03020904060b040f2102100507060501081005070807020606010e040212040606050a23100306030b0a0c08070c020d0206070302070518150913141009060209030d020106 81
    0x100500b4003865403128180465100300e5032086009404480d896000108104096900c5500c1c1d0303901da40107401071061034009100003048942c003855071840381e40c0302c040c00c15442802d56402c01090181d40000320b4104002030001100281e028001c5501a12040015002103c10086031804a54006044004021481c41804416500455000d80264081c68881c03440c0c0c400c8008503003e4410400c4d440760002441e01040113025203540301500791141140e01c0c0700c406550304042c01741c0c44c80c0c114072030818414000025010f80784c80c0c8034480005030039040100e03485642e51510490307114221460140242c46542c00c01000f584044101c2d886011170400480c1c0c0c07030041c2c000c5402d420051038001d009800c00640030042c14000c225450040900070840e0f0300841c0d160710b03035510003e01510030600002c2e0250030020b00c1c3c946400b007144030b06280c0402c03044042d043d403070750030000c1c1c00c580c1456902c1c0a0700c3c40c0c08501c5d284030701903612641d000c0e000141c3d645a255044c1860110154000000c69140140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 821966196 1250 821964946 821964959
    0x90108010501180c0f0c0c0b0c0115120209070804060f060308120a060b0f0309010b0613140102120d201303030e0604120320010612020f0f15070f0210080405060a06 72
    0x4018910745c00d42ca810811550300d4505104155030f150403c4204490219168980c0c51054101c44032140c500540a000c0954502034803c1d90b420112000354040d4400c80041c150038030a0141d035500500584020566110621035182104e54503042513489c0000022104d2001c6603404c0441e4110349516820014a490800b1101a40c051210041c80700200040890311820302500181e40c00000204030559907003002036070703801500d07840c492045101c480ca0384048043d070000c07a0ac2c910243d80410400e280c01c40f284030700700040c208000d58038083e01000c0c07400f84140c82070a01402e03207400c190788039503411421800d0141450907001da4841c80fa07801044240304081c1ea030030540c0d00560307040c145444c0c640b0315007512100b15004504000030540c030746a400100c020311002c0f8420650b000fa1184201c0f507840703009101c100f08030034420a8008511440c40301281c05480002c1100b240640101070b00940c481e400269034a140c00030340000180b4803024002070040c1030144a03005482c4c5c0f1400c00483d4603180 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 821967446 1250 821966196 821966207
    0x3020f09150d0c030b0c090a1e0b070203011b110118020d110a0308030c0319020721120504080403050705180402150405031c14090d080703030b090108010501180c 71
    0x10703000d034010410800840108422401c0c444065544414900f800d494261075800a5400c0014203510580e850440010301e100d030040c11400050390345c809400d1081c180000480e09500c0018120781540d03a07581641c400320baa0b80e6030b03080340d0296551050740d0700c0181d5007c6c60965a02500c0d102403001015800d10050f03440d11510080540e0000c4605202075282001581c080d455500141c0005000010424082040c90065102d0707e940303103d403c2d0800b29550b042c0c00303e004400d0010030412500b212030301e0403030911016070340100e081e10700040c0e18441d42c0602415540e041c0d804403043c2001240600420006009840c054070042d00d00d400d04044080c0700b5011210040c00190242c10341442a89100c5110401c0b00c024020142c01c0302d211842c4000002d4108400300403407000940000c060121070100d01c821224042c1c00105080702480b4103407110911070b0b11082c001c030149035441d400b80c00c460325074015040c0200000800050303590301d4480c4031510b0559015004183e00d251034500c0c19990f4210 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 821968696 1250 821967446 821967481
    0x207081506090a02071515090c050a0c05030408010204090e0f01020a050d021c05090a060b090105010c0b06031c020a050706090e070e010216140109080708030406050c150a020403020f09 81
    0x226005401a120186820024445d480003d4840c03c3c01860500460490360003450580c17508021000c4400c0c6c0e0340380341e40100c0f21955000400a401080102032803441215200c407103a010f0003d80e03180c94bc1d60550142264065400020f045448500e2180310000520a0506c1f001c1c80400035850070b0b0814134024407500c40c82a010410541c00f02e400102106040d00303051541180e4030081005050010500c0d944040041040320024180b0200c0380e0700f0308042001e24101c810603100c40180074002c1d078a03509190320081075184c0500ca01c0310159007007404440d403494403203000e4001d0201514641400342c14a00e25401400c00d0080c0040c04204003191074400603404021803070006d1000c141d0380c0040341000c810344030b0a074409072500008950800318140e070840095090b02d07802e02d0196200d00710789d2a43c850384550186604240400c11903c1d000308000c00215000070155280409088400d10464005484141207160301090510440c01c1000d5483c1458108a80040c0d0070720781405400030b0385800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 821969946 1250 821968696 821968699
    0x2090f12010e01140a0c020c01080a0b030f0307082505070302040905100501080c10022a030f07060807261603020c0a060219110c0609010504080d030c0207081506 71
    0x110121400310303102940803005030082da000901c03118050300442d100728142503400d030107082e1801c484d100201e800081d603a0920702060f15030f0320181e0b591048a0008104414165416010302443c06034004802d00003000b9041c400c151007900c039541000410507201c030b5030480d0721344001e01d11040404100000349a00450b6070444010900340540d246c01030600d00e174180075007921400e000010440043c0071a0b560100e0b07400344d83e1a00c881801072001c80c0e80b460b40c110b01e0410309800341000300f00111f8654010064070006001c80e10f0701c03500e80442038580700e556031000001038800000e11070115880702460880b404000482c0480c07042180c0100308043d4040c108040e040e154030503014016001e501607904e651006001d9650b000c0c55400c051010398070801c1600102d1b0718489400700703000d00074000481c05980410007000d000f084c1c0028400035034031091003541800818000024210400c0141f4a0405840d035004544483c100401a1500c61950031000c1240c1102070a00642c2403030200c6a44d01820 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 821971196 1250 821969946 821969959
    0x903110607170705010f150f050f0102120304080306010f0503040b150f1e090105060c07090c0e04061509230108040c080703081b01021920011a011202090f 68
    0x182864400041c03a20360b0286581000c000c601e090038490190b0110103800c807514818001e01601d066044603c460340d024402d0400c84001c07007445142081502044400c80c1070044410140c0c01901141941c1c00c100c404403015500001040002e5034414440f41035440303641441030650030150780707403031a20304002c21070040c42d50010908641c540d0b50300c1a011500e80050a44200380321041035880901040c842e070180651019400000c1c541014021203095502d8403000e40319060402c00d80c10098402074138040c1c01c100612550140c0e80c3e070b9078450036000344010201c0c08100880c16030040e0410b02140c1c400d00701e40c0440e05030b0900020491914405400091a042c059a0780e01d14001005c9000c68100202c20b2003007840c08410404248000c02c1484a00c1242122040290707030418240c1c400c85011114012021590981c91805200d4114051219560a6544075040c0d018142151540c40559416014680300c400742941c004c2c1c000703118402500415403828101d08046452885196420b500441 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 821972446 1250 821971196 821971207
    0x1a041a07110f0316080a0b010e0105010e13090813210233130e1303020c010c020d050a150b0405090604020105090a09050702100c030c02060403080c0c01062409031106 73
    0x55090145045216029000f84002d0317072540710081d07450045120131503114501350300200f82843c110903628100c0d00e05a580203070f8682040113011002ca05c0c0080550100d0300c8200d00b01c00039900c42d01505503100207605002c90390340380c4001c0180e01c100b809003280e1256840031100d405a281c8507054040d005c003280d41c1a454401c60b600000003003a003100e950072804404181d898030291010581d00481c1d4002d81071100d26280c0081c00d40f104140c030100180036902040104005500440d024a2410300081201030146e01c55210242010303005001100e8862160038208040d0155108100c817203002990200300702c0c81e005c010695600d038060310180c140100842c481c1d0b504c2ea600000728010f0305a2200074031a40c2001140613644a10342807080000d58107004401d040e240c42442000d048040d1a801002e29407220b84003aa0522006401c0141c01d042c2084038420400003402a000100300c500a500204071b12601d02c96003800040c407905040100d601030800c0441c048480701900440215191075480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 821973696 1250 821972446 821972449
    0x6030b09040b072006060f090f0403030f06180e120909040b091e0c0109050909211e0d05010e06060d020901090f0e040201120c020a110a1a041a07110f 66
    0x2401340c40c00384140d004126410001420005c41d01d240540c1060b10003150a000a40403c0710440044a031001d00391aa5000034011922941250b42c80c03150318034000607034545401100706040141c0490000c2561559855481900c0801007201034180d2001e00034101111240040c2d034215019101520742466034020580804051180340b07900402000d070391324104824103a46840d40d00d0910300d140814034001c400121030404541e000c1c410061072001d41903002d6900c10340d02c1c006000c00d40844900809014000e8101c200c02a100000d2004181007522805440745507000d440c1c0503002944c030400d0010500c21103445d0641a1034500d0000b410150700d5000240048814a5040d0f000340016221913100003003104031800203034084c4d03000381e881c80e035400498a580d009941c000b03a180c400503848840480003081740307100340340340e0f5050052402c1f4032241d47d100b00c11003201c9902c40307029480348009801c10100b07107400f180c1c801180d240f03041a82011034070744580c601c80c42180d00b20760051040102c1d42259 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 821974946 1250 821973696 821973707
    0x1b010c020f06040f0e10120b042303040b091c12140d1a0306070f1e09180b01090e01050312071a010e15041a10021c0f0906030b09040b07 60
    0x140c03151130400d07520256609074082c40c1500995000389125051400882d2200d06000d5514080d604003600c259503449503601c000c0141083d41d1380c44072003c00d090b43e401301c1c81d00600042006100035043c8540743d249180030403103800c3c04a040b205440141d401400c0c006546108500e200541b10708142ca4480c1d24607004145520be0500321102d1245041440301c1c2242e1283c0900324085820390807590075548a010550f41d000062064030301292040d54210040ea69560744500360101d6441c0c00c28141c7c1d40c030300c44880416414041030040580318450840c1c035580c0010198020140480305121651402c408603450b00d02c1c00c480c000307071420b001911000b8044111004040540005210310080da075440d41040155030039140015010204030990b01d19203024051400171502c002d0400b144220200b04001d101400071100c0815400381d055000e249183c0c01160803260b424a4640c102c4880c4030b420001c010180350380100342807600d0001c8800c13240d02d0340306410f507020b54400340c4180ba0341c407a010161070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 821976196 1250 821974946 821974949
    0x2030703140313030605010e0a0e100b03010b030115170721061b0e011e051602030f0a05100518030d1d120421051005150a06050a021b010c020f0604 65
    0x301c0d030000f200c00000300440e5502513030481d0f01e10304128a0303580b59501c0c45401c1e1922040104080d5014121041010070664041a031281c0f00030000101030780f0640100c1d084d1040100c145c20329016520b07040090b00034a1200d80604552600640451814184c21a04490103030310401c2d5812440c200c00020054680d0018280e00c2e2108060741000c5481c8000900b640d90341c0c00c24600248954071881529001001007100e907a081d070302d0341410030400401c0c41c5102000b01100741d92500c144880c0c401a100c040c04020f8002c0d0254000c0c0c90807512000d0504255403028210051030400c1300302001ca020300110544103020070381a0003203200c104848200c00400303a21072103600d00b0f028110700b110341105070800400488000d10344a0703181600c00071148004a10049000d401504000244115660207502c41039101c0c4415880800500c42140800d1482107141c1015021900c00910003488940410121848a0040012000c86450000000d0111034001c03070003400b4143c1c0c40000040e95884505480 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 821977446 1250 821976196 821976217
    0x2120c13271101030f020405030c04090602090406030506010303080f0103350408010e07080c060a08090a0501020d0c1d060912030f180a0605031e360712020307031403 73
    0x1d0071962030308210350415111502280400d14051000c3c140003d14004c2d10200d402c020098918541c07000c05000207050940002c85400c0e0342000003c0069540c0d01c120405140684000e20b807540c11498050281d941c00303030400720306186180040000981c0000c014500c0d0303030701f4841d0360340b100c21481c2c50f1307024180340007101c5188040c04203002c2500101540503d00040f1460f08558105550343c6986031a00c105504203a013001041100101c050b0040c0011500100101d0443d0618105034650608a800c0700000801047e207681e03e41200384c2c0c5c440003030321005c2142018403100c220301d031001a249110f80070304140110440c12414003e20710620590341c041c290208096540c25080a0420340d449070024182d00c5403c0d98030010985c24811002d480c17140314503009120742c08800400c0e190410b48020310030400051100680824922500c00103001212008402d2600e5404030404034203008058015424280c44800000050381d40060440c003141d810520f4040c2524600203410300f54440c021004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 821978696 1250 821977446 821977511
    0x121050c0d050f19080f092106060a0e0f01140a0305060c07060c08240607020402120f01060203070b1303111515010e0609280f0302120c13 61
    0x1a41405008a40403404003d9102503030341040301101030f00c500c400c0b80c01001d49801801e20403d4000f500c01e44c002c115404c002800e100500070312410740170848100c5000102a90809000e01c8854101910a000035084244000d0300c1c40c600302d10b1007038400e04d0510900c2064041e4204160f590b4a51032034000c09581c002e800c1ea46207140c050801015940301d500c08540301841c2907640400c0c9403207000400d0058282c1150301d800304008200c010b6200d81c00610069004c101000403400503a107038401001310700000500d055440c0f4040d50301c4c1901120581c4410150b41041100700d00148444000e1640318140ca07040803c214091300f01205c4c8040b415005134500d101ea40c8844140c20254495940314807141210f050104e0100c80c01107501c2c100e0b110342550080d5060240fa61580750480c0f00145020507030055803440c400240c85400080941d42c0304035541010880d00348250300f0800d00104002d140c1e00c0c001c003420408440414104c08002c2c2040c400a5034801c0c1507640f01e52500b4941030005041d2511 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 821979946 1250 821978696 821978719
    0x41502160c03140312010312120507030507140307020309060705011b0c0506010518040602030a0f02160c080d0c0803090c04020f0405030c100816020a0501090b07080f0121050c 77
    0x21410403440c9001c00d483c5070301541d60782e40da8418000f08585000e0703400e43c5c51561a03442d5640305074102c44030420200c103210078400b00c400c41000d14828075208a5655401141e0381c103041101030070160160750328144c0c0d09420010070510351703000821500591001e07101542c1c3c0d5480760500c180140890951001c40700f5464407a50100365002041104031400341c000da444590741c0e103080208560100b000d0402c00c1c9080c100150225503694003450780b000f1311840100744c640444050008aa010b091091103e100300e90b01c0c14280441c80d841c0001401604005021613002c4400c0a0710358030840800074041500080080e685450078050051543c201800c07d41d100c84907080c1c071a2450300715000303c80c041c0c030401c0c071582007501e071210b084004a507030340e04c510941d40ca03404500d00b0512590404803055110300308082e0000b9000340f0400a00034051140c1030454100000000c040e03440c040e10840b41684801b00510030b6451803036450030840e80a1070031000700c4980c1c0ca08a4100100c000d555544200740c2e422 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 821981196 1250 821979946 821979953
    0x1005100512070903170307080f04142d01050c071106070606090209130b10030e0a1b0609050a060509130b040510031115220509010f1802040e04150216 66
    0x100039080c0da205030780c4071040114a2641d00246d010483d004000189032001151014520070002c0b81c00c81d00601e003016040e0508008240350a0482001818402003895420750f10345031035559001141c003c00c024415410310145c0d41d4041d02441314041c103c030555031138a801a0b901c0c8404c44105961000c000d20900341d4076441e640003504040c1105008150240303104104514500c28003040b03100040140d802115040004c0b130082c9021400f08000c0e100316500a03020550f00381201283c248070000c9090204d06200e0001e100600a0740001c0c0034211a05051180315080800e5406001080d61400008080f1118080c0031740032070304045801a02d0f20f0113208940000311508800d407030286402925141ca000144514800d40031054074000c5810700c2260f5078094078252113012406030b100240001c3d62588002012242c082c0e01c0840a5482c4071000c01c58100b1218100801b042c02030380031070406140280a400d841c81c0288018921b100001090360304000d2503041e03600e038803003c080100c1464410329 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 821982446 1250 821981196 821981207
    0xb090102071a0322030f1409130902190b030a0e010f022208120f0d0603021c12080106271703090a0b39060a1406010206100510051207 59
    0x120b1448590541c105200106400d080842c44085e5160352580ca000341504d82c02c80d1415003010030512421030800000c1140e6440540016128206000008242d1424810480041c039401c00420160514500070805d80036940c00b40ca502900c20710010a40702d02d000c81c118014020090000850392003c5509100402d84181142d80c0150203492440850b444600103503a81e403030011001c40c00d605c200f10380d1800c003101c8405401c05800340700010034070760307280d030300080031811600c0d42e081121030b03030510340014004411241c05c140d03049400c01c00e41a5040841c000e1400a9200c440170941811020744056420071034290001450200310100c900c98020760440c0d125400105000e114421000d80460780c141510200c80d601a0000b2403241d0708109e508400c01740e03446560b8401d240e404081e25a0600e05806d021180c0300764001030001416409042c05d401070391101a04030781c1198495400c004e0f03030340003100d559015980300301c03031080d076a140b03a020840341341c4240d0100c99950481e110500c90050f030040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 821983696 1250 821982446 821982451
    0x1109010f1d01080d260f060a0902120f06010c0c0f090b01030e070302040e160b0901080f04030e09130f0b0f2503051510020a050c06130b090102071a03 66
    0x10403042292628015108080c007002e0141c1107040c0c2020741038038aa140580b03c003070700c040e80e4031105440500a40c8440c1409030401c6800003c0103903160200b19032858201480d40142049600450070101240103420740321a0040c5807003200591030000c20340d00d070300076a507680000740d0254107603030029240ea4141c0707040c01d07961144603040d81c10482200d0483d0b000340191803103c880b09008040b860329680030403010b0482408003144078003c20031140c89114a44507984041d000c04045140e03100c8060000515121004180981c00802c00092000003603220740041c4d5055000c4414114940b2040b80c90748103e500c0c03010040403101c102c1c02036400c01c0240b02581e442400c009942c04200c1e0345040c00d1100c035080005c0342c4804002820b00303a50f41d0b50f01030ba218a0304884e200281150402c064000318000e0500035420f200503a100204d41c00c03c0040411058102d00b5007034500781d007010302d840524400340002d4010604e1450012a520309564420011000100b00340c0b24804100d000e02e030f40000e180e5005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 821984946 1250 821983696 821983709
    0x80604060c0206060a052815090311011d152208190308070f020304230906121209040902041503030809060708150d0501022101080f191109010f 63
    0x1400e000070349610300448072100b150300c0900903440c48040040d801c5061f441038030300a050b282840380c02103008510361484c103a2540310b6444a00510b4110304102000c880c0708020f190411600214010013903000200c1000307114016550a40216980003103180d10b40148807602034640400780c1480c0010800b003011808440e0309405441003011a5503107442c868900341c070040d0100cbc10000201d0407161045529518581d00c44c0b054034102526815118100c60030804111800011210411001c3c5401c90160342c11031021140c00c0c1f1a103800f8002c035130300d451115803c10700e20240801c2d0b100041d15031390000c0106940c018002c01010203d2588140d42c01003502041e40000c0c410030000e0a4105e0006802e40254800d48403c0896920300c0c41d1200d02c00c864110b4281c000804421190001e42c0900141564154028a0700d0601c1c0580c203090315486c0059100c640a60300914050501401c080744401d040d60014802100001d000c2c141302180d0181081c0701c07504198800300000307002058440c1c42d0140d440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 821986196 1250 821984946 821984953
    0x21903020909010c0203030402010f2307031206081213050a030f05060901090807061112090105070e011407030c08070b0106020a0204050f04020102060601110a051f060602280c080604060c02 83
    0xd41c0c0280030700300c4d154403402d280540d1041020030055800ba080701a188080c0d85850101251300d45106000b5440c100003086030340e040171540904040e08000703540c12080810034100000c0707240c90751080d80d40d000300d00400c0d251500001c840c43d1419100d01c04c040030300006042e80c141259070b85081c000044684c0002e4665008031004a0480310040c06030300f02d141c2d00500c50b40e041c5042516640014401c04000f0245008100125000200c40c900064480c40e2030701c00001d0f841c901140040c01e1090a040114100038407038500c01c10286051040d84c0300107401d0325016410040c54501450b1a108115000d0810300d4100c000245041e030008002d903210303109075010301894403219800134011106507030007409a048000014030301c0d4401d40000506c81c2405d012203c0003441615520306051841f500c812100940704000b8001801c60302803600240914401840005002003449856640101b60440000049220b20060200f01c0c2c01c050301800b07810094a60500301482d03c10b00034006403030717803501602 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 821987446 1250 821986196 821986201
    0x2512050c19050f0301090b1c030f0f140301091505031c09050f030606040b010509060409090506012408060310021809060901050109270507051b0325020103090219030209 74
    0x51099040c0c1d072060f030715412240d003507900307010104025190b1380c0e0600d0f800804803080142c8520701c420b0010701c05030081d00c510b0501501650001d003207201c0140003000b881000c100300380740c8c14000030460f81100e100c0500048c00c00300e4101c519090740a907a005503414482c05440000000445800d03212845042d103c0e41c648684c0d40042c00400c8090251095050b000342000419904054100b4440d010052414502d403022020000e01c254209400151545940341c608504008040000341e01518819502c01c0310b4140c0d0840380d071811131482845a0800c00a54003090040c2c43c10444840c1a0203602419520780c15240107154410540811007441345c0c0040700401c2e59800c004003100d0603504103a54078103020341480843c800800c00282c107403c0e400c440000b000000c0160f407049500600f0702d030381d645664a524402104840c2601181d48109800401c0f640e400010b0708805003401c2100c40c03000101d00700903800141c000744508880a5007241d0030240b44a5031680c0101090180c80c400c07030f07131700c40c240c2c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 821988696 1250 821987446 821987497
    0x906090109031d0406050909010c02100228091d0621250f03030c0209160804020906030f0709021308060105031b030f010606180e2512050c 61
    0x1c848561000d8003040303203c010100701c00b68800311a5a400005800802e5441d0786d14081a81110119555841c0740d40d039112841781c43d17905100074203c204210100390f040203908640c0e00b10074900e003140314250780142c0402c244050300514014004060f409146030f014442c41d04080318541c42110047e1291480c29603407000e01030707243c41c03801c180e000390401890040181010401100031000003c3c9600d010004d00262030b0000b0615600658441d680344154005070344103000d09900050f0140f600e5040b1558200c04042e030080e440e0340d2054045849100341d84560002c41d06004009100c003a09003d540320124003600240c00070003034110070450601101d603039808980c0d2220030030300074154550402110b001e6407486000000380c950b100107064840e006020400345007103801c241e110300040756111003e81e80400c00540c050000b00340410801419207080b007401042249070032400314420f601c245010800910a0040042101c1c030507204000500b4041c281f100c0c240c2003500c1c46010120301304641c9041c3c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 821989946 1250 821988696 821988701
    0xc05160906080d1e0201020409110c010b1c0b0c07050a120f090602060f1512070614070206120a18110901060e010f030c0e0607060207060f0b220e1509060901 69
    0x78080e00340e4410180468003510740010744c280d02410707400c564090202141c80020380c480d0501880c4c0d40f02101d40d881c20b0340c000881c00d4031015103240d84a0740410701840c6001044400c1000103a0f4007400c10180d507650b62550302c0060141003000341c0513211302e10510041008804000b61f0001083e25180c0540c800610b088805010500030500141c0000c408210206122000f0702d402100c40d05443c210390720403801256001c00d2030104520190b02c50f840410940b40c102c00c07a21940c2c803207625030740c1c5814280d80219840d40710380d065070417140c0103a030006203a01c4503030ba11614aa0310501c1158108000341c1c1404010381d0f04054429118031035007400020300c0d03070040c00b040e443c0c2c60040c0c440e418551300e0514243e00030411180c4410030700002c100c2030082030740e0349030080440f14401c00700145c54902c141041c50890b1500c0401c4a1b29a180080d101040e5540145540d18130b40da0002d00c0d00c81002100c403e03030203090030a4510030035219a02d90301000d402c131241d0161160140d1001c41e903150351410420750a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 821991196 1250 821989946 821989963
    0xe04150b01020307300206150118210203030f092b08210106030507111518070506030106030203040b16050d020f0913020406030e0307020a14010c0516090608 69
    0xd82d008100321300008000315a0140e1444030307460400d00c1d464000361306030300d82041a40b00c1d10068028000300310032203a03a4003c40c05c04c1042842d00782450104a505000c944a0600072645c502c030a501d0140d2003a0404030512017003960103020782c2c2d101c1c4004d00e500d8086801503414070788218041c41d01810392400306150b0f540055610b07030310f507041800740b5194a02964400f507805844d04c040c40461440c60703c84164458002c1c00f080e600000d4a02e81510700901c04030503400c03046c7c200e8101c01508a01e0006040c03800390440c0d034601c40901510400040c10749450100c1d8807050300a000400002041030700341e8081d6100e18003500c40160b06903a0700d590540619030300c4000341c01081040c0040751400c0402e5026189010001e100c09103804e02e0783c00002c00c5079603440403401050760002018406c0e564180250240d401031b503c0210b04050030b80c1d0000f40111744500130080c04910f1b01e404a0b206c1d0b803041a6892007980c00a06070364400c00c0300240203c070b00701c5d603005889442d800e0520018002900180380c0b80c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 821992446 1250 821991196 821991199
    0x2041409240c030414070e01050907020102070c0509100f090c030b060c0a1b120b0a150b03060409051c0513051f081b13150503010602120f0708040e04150b 68
    0x5069580001500203600054802e50340c040b80c280d0030409500b0200306c2e1102408000302070010301d601d400c082115120000f4104411640103010705070016095000b00e5050350130444d8580020355a4031a441c40506c101d51141101c07000101e00010f5000b050750001d0120005a942070201c210100d0600200d03110b07003c2c0e8410340d540f007041510701007840f040701c203460040242c211a1700183c0c1c03420140b201100078082a41d05048460500001d41c20604c01c0e40c418411201c814549145056004081400001d24a60246440b641541c0c02c0040c18002c10880841e1048042441610044020000d401c01a9042100389074144049034601c0d20311082d41186038200300012405210751000c8805810141110f040000c00c0941c035900100d80d1000b51100c40c10340c6401c00b05071840c048140c5001c140366071490040c0720080005102142e0b000c9021107070744000001050f0f442031251040001071092482c080e109100116000c5160450300d0303040ca005038026400100524400d5940f1400c8400103801c1d80e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 821993696 1250 821992446 821992513
    0x611071e0303031e0515120c010e13020c1c020706020102040f030f110909100b090405060c07080f0f0a020c032d070e1608090a05121602041409 63
    0x8200103442900311002540d54041e0850000c1c013030b402d491080d14801d69800d01c4401021040f42d92604090320040c9450300050b00410460880c4c60020f01010509030000c0c1c000d580c44007100325058110740407990101c110300c0c100d94072540303c0220107144c9a81c10030190010b0240340c00000d03005105000340c5060328540c513204e84625145585a2640f01d0300820100c4052400c040c0065040d030b42c5017211071044007401d014149607070510425804440420720306a201d0620b00d018003001ca1030008619500c5600600d07103a41d1400f017405c2c00c0000e4022a09000c005843c0018900749070044030014060100d420707000c94402c005201c041540300c08104864450f0200c00440588020000301221109400c0340001c0d01d02180c2c86018004050070f08a51019a95071100140440550b0110841da48446c2d0749002e0148a03400e03513a960b4592100c04100d5801e034002150050800e04071880021003158000d00400200b980c40812041409003152410340398080c694001890703205281c81c0403110120300c251f2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 821994946 1250 821993696 821993699
    0x110f06060f0d06060608011a040f03060504260a08091f0b040b03060c18010503070c030507030e060d05010306050901020a0210050406150308030405010606050a171f0611071e 76
    0x5000d00203804405190340005441c00c1d04010843d10311544003e0002607682080c1503061240760366000d0a03004a24501e02c2e4100020064240c61241300b40660f07604c04400300e255103030707410441c2d0366a40301d03904038014400c640031041d83c00d19504020304045140743c45410700ba42da880962621440c92900c01000342e041d000d81d8451006895000d0a01000e000700001218909800030a141a0b400c445061401e007000074201154201070307079141034059003403038103500d18501000d005110490b00300004090205c0440e4050415001c1d54040c928948054901070703c0d00c5440c118000500403e2005455892811000c14a2000180202c503807401c19a001060f8400c208404100140001041a50010755550002c410b0320701420034000103501030740481e03440303040a0a0050850b121a8054414010300b00010000c02d500803403402c81d00b24802140844070b0f55000004840c204504105204006030000007041c816003203541d28000348168422204269203c009844861341c4400300301e5242d00d81b0110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 821996196 1250 821994946 821994949
    0x1404051512070f06030506040b040209060d09050705060c0610140d0803042d0606050405060d0204020d140c1e040e0115020102040b040e010305011503080f0702030a021f110f0606 78
    0x7103441a00010801c60b8072540d0344210106001006400c03140000e6201e20600c030042c0b070319018543c02408100c0303003140352815910005083d4450927000c034580300d4a0303541c1e076000d121080c4624002818040c160507a2821032161140c1c0f24602150842c42e4400010000300b000380140708500d0032904081c004000f80026500c40701c460f07400090089520341907949100220162011075845415210b04107554050313528074207081915000d40006014a00e403030f0412010341c3d191480012400c1c0c06a0f030059880c103c02c01d031a0050070540a098850b60003030f205101c4180003031001409000c1d90f40c044460041d96400c812421380c81184101d03980e0806280c01442110405500d0220880c3d16000040c075041c0e8410050705a600305620030b4800c154180010014400280984112041e103491100510b50a59480c0c4510b0301900355080c0ca111070201d2610115101000440c03100c42d0010005d015200000d40303618100c040a0005100040411412100580700002c00c160602c071544041e141603a203c0c0d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 821997446 1250 821996196 821996209
    0x140f1810090c1505090a0803090307051003090b1f0f140103020a110d03050708070507151104030b0f040210080f0402040911181807030302060c0904060b0f0414040515 73
    0x11420307140202d12000020b15800f1850081a2079041038444d1030320b4034810720030082d8254080c1d0000700aa0400c0200001c0ba58010a01c8016168100d940d889a00c131054011001010191001823005ea001002e020b8200c1c5c6c00c40d00d807282c010010f0325240090381c5131030840d034001d2403e12039640e43c41c013081e991001940c0260054591000e141c41e100301c0a8140d14980c0e13107000b02a502003004a5aa2428851039a82c0b0680030341e4800d031a41050f9181c442c450f555440034003414042c403407505a40354100340c40c0c1426201180e00135900040714078200d0803c0c500c0100f1000f01610100d00c40e8807040701603042c80f40100e01350340c410003c0844508059540d90280006803518460485441d0006c01092080356111903910400c50329400400065190901d400a480200464654000c5d480380c80100002980007a0315070f801010728182ca9110894603001c2070151015030403d0361840808200315041d20365150151040310760740e01e40903401882c42401c0c042115001d070350004c071090071030500c08001d08125 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 821998696 1250 821997446 821997461
    0x6061704060b1203070f0c0f120201120f020d0f0c030c0c1106040e04050a030807021c1407140d080714030f04031106070201090b0c13120c050301140f1810 68
    0x642000c40f2000050005403c40d4801c034000c540b00944442d02da02403140d40014031016041a130302e0000036034203212104c540070800c080002d0401c0020313514444458010742200540d03903030858045d51179040320982000038044a06103440d00524040f81006501d00c280114441c410440e116640b07204072588600001c0303070003a40480c1d000001000005820480255000e216a014201400c00400b50303140003012408050180000c6600c05220761800c201d003034005200c025918241003112112801c44c20100d4014050090501c000016003000b4802d00400d107984d1044580c0e0341c2d4111681c901d4015100c4201c074602c90642c011f014000a0101c08401207416089402410310150340c0c0c1411000b00c4c507150b4120785000060351560500070421101450a5801c09001c212090401e0b4484448042c0041548111102144e042c20090144425200d5040186c40b01400922020100d07910102d40321000760349107110b9000c0c10b00080c41d500b0442901004000d1300c0700140803c04030300d004c0c540242504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 821999946 1250 821998696 821998699
    0x10241e03090804030305191715030a0b010e01180c0e0d0201020109060e01020405030d14121909080a0806030312312603090d1419090906061704060b 65
    0x1200d60040210b40707107101500c000c2d40300e40c0da56075940140703004940d180d800361a4200203014003561050307005199110416840303043d035074242c4032000007480024070784000c02c1d5018005d03505040001c0b5000c071001c2e200c0ca050f12859080c008811649603004801c40700590421030010b0003c20f000101c525100b840c0020301401413002040c158040c5c0c9400c2d0444600c2c079007048041e94005000c20840c02c05019022020741181402d024410041002c88254440e585c6800868100000064002c95203810340b03484558130500100544556481c060441e507009080b06c80201c1e885c2d0000407001e241c008112100f0404040401e0301644908031100100c0981e0f54501c2c9a5426918500f84440c0d42f454010b4039030f9010380d018107540014116000c10304141206044020441081048901500003440480f01c10041c9000441100c2c03030100080c803800b903a04100d45002c0c2c1c4070419580c1a9001e040d00094031440d4800700700860341d60303030140c600c401d41c42c000b031a13485c031070f54002070116070594000002e030b950 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 822001196 1250 821999946 821999951
    0x120b07021b22180c050d0f120203270a05060301120b09031c09151b050d02190e01080c13050f0a030f0b0a05090c0a090e0a02040510241e03 61
    0x101e02d41c0e150159003e00c0d110300d03000102140c000702440b035510300210052034140c413040c030070302040c0c0c40300040c4403040900170305070422355050b04070480e00c20003c0b152165403810703c0e201284804e2400600440e01503242134451030a050010486140410869048070f40c5584045194001a41c481003207690007441040c0900041c00380c2d0b2000000c821264070407042040b00007516030541d01d401c2c03071040441c00112000c1031400c1810301e982e80d019021840915820f05010f0348501802d450000607100300413201d101203510341e105022464115031071500c625801d80f0f60b0180c40e500c28254468038000e03410740c206840c501d08801c0110b07003420001800300e8407004c0c0c0101c0b041c1e5200e8490405c2c0e00280c400c1181d950900c2d004101001c000b900c00d0f150843e640c03401800e680b541e08000113240c6120360180910300c607516007210800310000c000d0750315295805482841240703011003081c04080e5641c420000303c0741062424421421070189608101e1080d034450b055540e40c0c102d03aa00c1c040510142e817109069 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 822002446 1250 822001196 822001249
    0x5150d11031f05160e0d08070f0f0303360305070c08030307080a060302241e0a0e010305010f06080405071a04031406060d03030203060316120b07021b 66
    0x11030900201d20001019442039030a0400000b410040300c0000304400100031030b50b13410410341d03503020b625501e02e01d204035024903c0c0c556500301a1001e103d244002050b40c00300102440422401c00396805a035806500e08100d0301c4084503000300c009114030100c48543d002c950700c03502d030092905800d101d00c0e03000e031425a0804d034099440e00d00105880d0802c10847d8000b008011805a004250310f038061207001c024050b080c0743d035011985403895882040503090740c600311100502c04070001d448003080300120740c00c249504280b03003d0042d4403411510001840c03e00610f9045d500070300078941200e802c0b9100c503402c01e10f070030800c4400000140048681e0b0180c41400210402000300b0541d819509074401551146949003d26420f902000c0810090308008200701e2196100d5000c2e00c80d5503014180580d0700d5a420000a041180094550161107a09903005c00d1a1040381410b4140341d2149112540c40c0c3c60b00002030b0303925400340700c1400d10500c0b0040c2d045002d00f801200c4091140300d401e03c007403102d07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 822003696 1250 822002446 822002449
    0xe010c062309030304060c02120307082508100603060b0f03060301020705061015080c160c1502150a05060a1707051f0216060909020f0c060712060905150d11 69
    0x7041d00b5544071141d6400030043c00700b0301199110b040c00d0b02c25103000814480d800c0303010410160100408071814008404005589400c4502c0340007001c2c6000780b41d0021032000c500002e09083c60568100000740101800851400c0c082d214000a50310058282410040e49840514065000900303641e015502070014400040c81040341c20700400151b034009420307504285508452550030500e28013003000300c20600200510000841d4542c100100004164002c2d5061604101a91758821490000e03103032a00c20080b0307800f182c0150307030b0032071034004108075240c2d03101100546009503840c42c0e00a400407002c00400c4035007201d03e61645c0c0d21005403107416580300300241c000112004000f03056030020905a18640d030500548402100d112054034419040910003407010380305010b05404660b000034000d900c00590408d4401d4080d0050071201d05241001c4000c0c900320727a917202d540400b41810b80100d1441d00c5070203060700c111050000d03400b03e80301100c1003040301c0c886900142e40070b403100b0080c14080d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 822004946 1250 822003696 822003761
    0x4120b0a020f0f03041e0b090c04020913090f051b0a14030c010c0321050f07180506070228050a0905040f150b211509101d1c030506010e010c06 63
    0x6d80c021700c00d1240e24034012a40302d061041000c0700d07611403032041141c10325550701c5911036903c07404d41140c0050900841d2901c0d840103d51100007502512501c4902000600781c4503022400d050142c45005140d41c1d100c81c94200f0240b10494254980c21105c42503a00b5441103c0113410f06020745082003034900900d07180d5040d0214142400011515282003204241003842041d030006010b103007440c00c0d480000b00e0040a03500a0086500c550350010381b602c25507407041085150310748001c105540c103180c0038000d2030713491003903108003401940a41000520260b0910a00c0e201e40c0c1c101181c0646928940d403504580d41c5110f042c1228a5915205000c031500da0f100702015010001030f00c408001c5002031480d01d00f02520700800420741c030304410030814060210310400301c0b0724480c0700414010000c115500041c42e00009483c3d161107034501e6026546403e81c642500415680c9040205484d08001110780503100701000c3c3c04200c01e44841c80000e409640300d00340fa0112906c55021035000c9000f01e90b0f8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 822006196 1250 822004946 822005003
    0x40e2b1e08040606290d240314071a030a0603050613060e0d050702040b04090b0c07032a0f0804091d06010503010e0d08040f020604120b0a020f0f0304 66
    0x1108002048108800ca1203000050704595100038402040c1e0304203000b440f001400035511031000401c6c1031840e40c8441d0044101250340051082c0c00400007162013102207224401a0303007402120850f08648400420030b8030559048115420078000c032004510450751001c0c004200840d5103442c0000405c0c0280a12401403040c9d500c540c400f503005041070404d035820b03414900407542250040542c216080b02c1143c940c1c540c1503c010800803900c1e80002e0051442d0709001c3c3c08400f21004100c1440d041c400241035542c426203880c1030101424051a520034030032083c0550300c0380007620480c0402c1c260102c1d0080948682d2049203403903224510305080d0f6050301c0081d542d0031070100c1418a404e02c1032005501605054000704400c400e04001e0990350386d06402c0240901600e24040307404d00140000c0c1e0000a9006080d2a64590340c03441441d0700c201c0041010740d8a4203c620200750082e0740d50003100c46008050840e94206a9503503124840c40e48040e204407250356060441488000032a21000c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 822007446 1250 822006196 822006257
    0xe0a0b10050d14010c14070215192a20041b02030a09050405040308060607050a0b040f05150601050a030e0f1209010909060b070809031009080306040e2b 67
    0x50b500f002c581906401d540c0d9014902c424081d1410a003004601c800068500803a0101c1d622100e1000d111104115403007015200256860500032885030b064000c0e01184e6001b81d4206605800fa440720b114031103010034881c004041d04480c1c40c2c00e10110600d01010710380002d000300300140c060481d83c0600d0032106101c00c0c000140e000480c40c4500d003600b0405203802010180c9060050380b609980040140f000144401e00c180710110300c10040c0b00d02005041c0c01c1650100301250142031a051000508034504ca04884034800c0c420a8120007030881003482c06140181c403101d0504060000540c0603100303030b1481d04418410340e085607100c100104205c408120302c0810580d40c5080f08000180300c00d980d600704044481c00c10700708101c03c140c81411100425084418aa00d410740d05002038145500c80003515489410000c290041c444440002c41c0142c0086904000a05040102c2522030b83c02014021082010030150240c041e2000c00e0300341020600e1804640840910060700c500500c42c00301035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 822008696 1250 822007446 822007463
    0x3030c10061502210705030f070302010504020f0402120c09030c0411040302040608031c0b01050f070b01140d0b06040c1103031306200702120106180f0606030e0a0b10050d 75
    0x100300c6034007030300c6210201c0c0b40644040d10440c0700110405140b454503400d40c11002d500041ca540c244030080c4141d4010052500700e44e640e918481c10001c1c080c0100f0f41c0c1c140d01c200c90004c124102132501d4400c03281028540b044260983e0b81d00c03888126650440c50000c1c0d014051030084503400c0d82c0e248181b80c81800b200a002e5200d80c1180180300807070f02c607900400e0072688200103045408e541444800290b086c00c20b0040303170f0310b40d80c1c03c012125400b450400009080010a1032000c001804d003005060b00d811024045d6112600c1c0200901c1401d01c06000c0e008508200104003d800c5c142c0007241d44815900741011008902c3c01003600c0c5500898108000d8003210440508200342d50048044080706490a4031030b0364030740356000f100d81c4150940248194801082911110000e420080040c5442c1d501c1415001c050903e480c054000b010020107014901180400d10501030301c03d41c240d6001c05030082c070000100350303188080c042016100e10500540c808001901c0e550325845031b0096881003021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 822009946 1250 822008696 822008699
    0x20d2607061e0228051e03061e1c0507030503210906071209141603110a060504030212101b0806090103032a0f060b03070e090a080903030c1006 63
    0x32060315004030514081c49500400020390b404c0a00c082401c50040141e10f801c1405568139030580d264410100c0d850400079030b4903554020f202480c40514402c00d41a40c026074440c450410700c4440c81c00984445910480e02c519251070300713003104200942c1c1440344084030b17005030b142d44a45141d500420320402603001c8107100d038803424122941941e0403900f1000101084c5c10040400307040c00c2d503101000e1811555a02c1141c2c00e04c8901c0f4030300b0103840c1030002600c21004610409031161042030006995800c2c20440c5d8052038106a01c0070f1007280c001c1e95400e420710303095508110b400301e07150400300142c0c450f61800c482e0240031071003280e04910049050998048843c4000782113040300030125489034a0800041003c25042580c2038004082c88100302000900345030f2000b40285400d00240940700c8108003482007060070b81c04007e030f0140c2207040f039520b29034450940c00300150480d030707407100e80d00704541001c0040c0351a0080c08400030003c05a0b41015850310410303107440240a01080c443d502c8000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 822011196 1250 822009946 822009971
    0x120206160c032d08032a0901031a0d020402130905070825140a0c0515180625030605120c0f0418021513030303020405040f020403020d260706 62
    0x2603900030310700e0030300100009441c07050074410039080100300a013051400100041501c03250f4111a40648422000780e1903000c00002d21079a5034110b00d000f640400c5c5098480c22720200d202440350ba0042c801449085000019824440a0340002e421010041100c03640405e000b50903004051040060796101e2005180c0305441d0090003d20505001c16002c03d40065802d0303d40c050f5400c800c1c0d40070745003410b6451002d203c0c01c95071100d010303002030700c507008441c4040000d125086010340120140c645071880d400802c80c0040d21164140c858a200e0036007280c00741e6008001e400c00340d02e88542c030f05000036202c0c1d031280850881c105503045e044107a04903108080140c44c21410840301200d059600f049180303042c10b5088180902d0710b40192050f80d180b4140c214400c103c200715410303006481d03070414a007903880c030f00a0080e4109000700c80c842c500f890a80700c0040014402d950840f0b40007403440040004035190034100c2c0d0381d4034941c140c44140c41d03e03226143d05280b10081011a10420340010f02804904 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 822012446 1250 822011196 822011213
    0x106110c0f0f01050403231203160c1506060c050c1f0f0519030902040f02030705040509150414100501051c050a1b091406040509220501090303062904120206160c03 72
    0x25a07c0301e0f02300c2c0c14401c0c0054500d100348034190a800030305000c00714441c80e003000d0302440c2140e00d00e002550b0038103901042656000ca6031407100fa01c00c038110740851103100b040140065604440d5211400c200d880b50f040f003841040107960015007410094a0000880c0170100c0c4401b007145602c000c80d4460103c0d804605180c40b5600c580384480b9400c500f107040107840106a48120321a441c0b290240c0000f0840c0701c040070640d0250400c004008001c0d00c2d01c1c1c1d0349080315a030b0b0112128940c1c0d0381c184500140b603500070421681d0345e200c0484890001100f807240c4000410003d4442d4403416601e010900c110240020142e80d0a580d03500e030a41864036105040e00240110706543d03010b40001d100400c0503844401d440d6400c1001c40104a24501c807804019003070b2041c686014007a5824040140141030b050781c4000152062440c0031101c20f203100d0b15900d201c04081000d0340100d502044100452480b0f51482c03815148010020fa00c0c00d41c0104004d0b50440c1142800d541101e54003400b00300b0001d80e0b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 822013696 1250 822012446 822012463
    0x80c0d111210060f0509011418030607051c270501061404151505130e0103021002010c0f030509070518010509011e0302010309060b180106110c0f0f0105040323 70
    0x501410b990302d41058002050308222050b0003040c00808104000140e0165510b8000d40081c00c0d0b4140d2a0401c400b400d0b005150702c40c10541c000d0081310b0218030001c2c841c008039454404034a03000c4006850002c00100204a42c5001d5414181c21050401c0c0302a08a00001811405800003141007401c1940910b1640b1100204911452a01b0749045070f840d0303102c000208840d0300158a50100c0c46008084c0c4092088001c0b509581010b010040342e1101044002030590f030003074441084140c50240242e08892043c090074022442040300304a00c2442500b2140e8400482d8040c0c41000755184081084111480c883c002c24010310700043c0601e050801c00c250040801c00c1c000d403d505205506144c40380100d01020341055241c0342c045040c481950004100d04c80090308007441c601c0f44150907204000b00303015a00c0040d50740c0c7d465241e15000040c0040442100500600b882ca8008042103015264203000d1418041c00303000010110360118001c1a00c017001d0646800d07501404034201e410090352 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 822014946 1250 822013696 822013711
    0x3070302010b030f2b09050d0305190302043203010903050c060c040b1e04050d0303021206010509030c040b120f07080d02072303010b1c0209010506040e07080c0d1112 73
    0x5c0d940801e1051650f031041020313150740140209107103c002011102203103d07421803a04644000c0c1854100f40e0300000824004604080b6003d65106401c4220141e204521907038484045224190200410b0b0003440c0c0c03880b141180074507800719100d8020034203441000301d00f500803540128590140709414006981d01c400e00b0007803c0d140c241440c0d1006410300070740481042118180302e0040707401203440d045030b01030403008001c0c980c1c8814600c0d000b006035100401c02200b5012050100b1402d50199040d284c000c10000c01a00d1081101c01c1803000804007038a0f2664032051031502c80e0700c0140b06001500088030740c10043c2901900348880b0704c0c60316200c103000108550005508000394064142100402554a03841e40700844681c40001c0c058607400c00c0c090317441483c98429000c041e0102c2003040d40039109491040707190f80e0358001c103c2680110710805c030032404a4800110040e111309031a0b5440b01b44c0360903a509090081c01c1d80011211060309440007102c00040c0f24480000c245420341d4440c0a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 822016196 1250 822014946 822014953
    0x130e0a200c030a08100e18190804050409050c0604031a0705032401022b090914060405040f08031303140306030a080c210a110a1716020303070302010b030f 68
    0x10040038042e03a901c28420001c0411040340b000c83c81007600c01102c1c1000700400320000710380381844080003110b042c03010794014207803140e0f4004e10341300380c004521509259004207a0f9030400d0f20306014040030300700740d542c1200c0c14090f840309074110b55141009080a103008103140b07224030303881040790180d0340800b0300000103128041c410004041c0001080348621282d04407180c58602c90300b40140e140c0700160100d900a0b000c060f008041413420b4050070669818030381e40d810000c0f0394880070300085420b22001d003842c050b640d01c0010b0b22410942c00894200e807207010203007003c02c01074840300c80d00c2d002502c0c00c10502d810000fa40003895800043e112034518074845c21840e5003001e6001940ea0315801c0402000b000020490103070b01034081c070101007801305c0c80300c2c0c4d880e001e1540650403156500c002900404151520304001041070001102885203034411541c66085040440c0580140c0025075903c4107217503248200c00041e24140003401c2a17511079000481d01c01e81007810107080a5810008041319403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 822017446 1250 822016196 822016207
    0x1050a2f030a0207020d06020d0b0301051602062e0605030a0518030904090303020f1201150306150c060b0a23040b06071e14070f29130e0a20 62
    0x26052080302e40020304107000595808aa102103041c98003040e00251050b480852113445010031500000c007110400ca008108503501c9490713010360130341c40c0099400117a0248001440c0072503c40c080700c0302c004a0b0303200556160b06042c038061941c01c0b82e400910010303c02109020b07680096000340d03900a500b4140405224401206c0141c3d28012207442c01e00c00c680f5910000141802035044500c0c4140c000c80e4656507043d0941084008802840364025441e000303149540294030038071801c4140e64400d1110713401202481c1003141c03640c1c101030040da5040e5807032602441e503603900c0d0600700003806e0a0320b03404d4580782d0285500e00c0310580c40000c940507904020104110b0ba88000c1100e408030391240c400c0e40c1802030041c0f141013182d020440140032003014070440f555040005442000c848080c0520002540c0341c41e08101c50070754904c598811081e40c00400300000100340c1c0507001c03d003804944181102e40d1541e1107003442400380c4402045c5551103110a000e021484a031044103404480c1d42c40c0b412 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 822018696 1250 822017446 822017531
    0x18120d1802012a14030703080903130302010c05070503150a0e0a05060105041a10020f06071b08070f1b170c100809030d09121704020f0907030e01050a 66
    0x10140380d030000061001d886440c010752103180c1c00098103c1e0300024021040b00c003200c904c0c0d80e40d40c0049015400301d04007000007540c504002003190000c0c66108488800c0386d15590040d60000400e00c4201c0312402070601c0407030300b40c0302003100404030501c5960040a508208450004544810314a402d880e04826203040101d400000d050b03045a1040c1d81c0015040540c01c13084017507140d030400c0a580b001503550301c0c54085070700248155080e480c06003960030985410b4026500c910034604c01c0180002501031200200f0914400381c840c40380a4040307081003000e1aa01c140c0b03942da800307448100c0082c585405010b881050300f00f161311046014020700d04441e41c14001007020b00803007039000400003500c0c0001c900352802d00545007100460710303062100d10414a802d54800c1401c001c40c0c2c1c001407409000201c04031000200500454024068484001c4000284070201d80003c041ea03091549401c03200706e403648d0920590784901110340c4006105090f001030442a0740c810340080c0780800340c080340c0c01d141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 822019946 1250 822018696 822018707
    0xf03041a0f070f0f29041b03060608030c010b0a23060702040903030507020705180a0b030c1003090b061804030e01020106170c09010e0f0109090611072405130201050318120d180201 79
    0x20581125041d08010b11410080807c6440c43e000140180c1c20458005441c0c00d0000141c548100c046000303101e11042e800510035103c3c01403051f09849480c0c02049010000c0e540082000403202600ba0303071515100350046030035580100070450000e42d450003005012607041c0044409008111228484900c1c0c44e118000d130301d04044c0c000c400b0f8560314441b00c0d4881e64100b0817403035882400780030010048007102c0040c0052034000c1042d55036044850000700680303003d01043d41c1c1d01140c8054040786880f00d44048510301b4100c6040350540d0758440313022075144040c150702024100c5000080450a0750702c1c0620100e0b19040e84440361844101d4240910030400c114180c0c1591000c60000803201d00a060a8010b0850f02c40881441d1100042c110b040c4000d420300314201151440d074103008506403020800440b9000c580d95038071220301a9002005611034001990400d0341c01001c00001d81c0c24000c503d040a1417410070b46298800024000103240842c00381350315a0003064000240400180c002810 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 822021196 1250 822019946 822019951
    0x14100507090e1305010507021c0e060a0507061e0b010315120f1a0f33220e0102130611030f0f1207050c0f03041a0f070f0f29 55
    0x2441008001440303106407003d18042c003508a00284490304016002030348807000900c41d00c8410300b29240c1841003d004000014020381b001e030055103000300440d030031103458000344800ca45843d19030800710606040c0c0070a011402110160002c0c00b403d0000c000350450f82141d014051031082080d0400c82c417070120014101d81ca030040e984c42040701c0381c0c0c903242805101720410200414040750500c90303955001030140f84a8040c003100845074071201c514020354020301583e2110685450391500c0403a041045042c0040443c12b0541400794a030034591000390350043c034100c0c81076980403d6102c41542c031511010010601810320a894803203005150f03459214100307070b80400c000002035890071240c6d010b0868403242d44030302100c04241001800109a40c0c0000349013001c611a01c28004c19025020081307a080702c0850308401c3d8514160601042c0c0382d0020421284101c000740806004a02e003000700140151140301c8481d00f90a15260411450b4060350303018403c0c0041e00d60945040941020998 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 822022446 1250 822021196 822021209
    0x8061804080703140f0408070303170f01090b0d0606030b0f010b120105010513170c01020607030c0203190c021309120801030213050a150b030f010504150311031204031410050709 78
    0x1030700450312107215034178441d4a05130400075100207000260030b84040340c400c040d40c2c440c1d034803d100001d030300340031007002070b41640c224075030101d560010808040140d00c001e4000d44064500766240c805608c0d8003080310b245a000390364011049082144a40001c12420301400b8025a550b04041030844000c14980050003114140400041c1c1000740c0500710030703501e009100c1c5000080d04521034000c19034503803901101c914054458003010072500c0d03009000d003041c0c000295005605201082c01004440200f0542440502c10105007440c0175031070380103503400500044400070070300242c02d00c5c01e07054580c07a0b00400f000b000017142c01840140e594485c41c03804440040408190754940200180040201119901d9850503041d4002845082580618816141c41104620a03a611818801501d604020454415080c1c60007440001c9c7c0142105611520140403215411010415944590300c03507002900d103c802165a9a005c403410032014007400917050061060707040c000c00c060b080c03841501408 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 822023696 1250 822022446 822022457
    0x6010207030302062202040504051c0e1c0204090b0f010f0b2a2b030b150304080f0c0a0c081b091302010e090406061d0403020d080601180608061804080703 68
    0x305d42030022072041d01c61103400610402181c1401d01d011942e408003152900c084080802403244001d019510f00c1c14411070140111661034005410300c030305c509000108a9000340d072618000c003c00c84250801d07200781c003802500c00c540d50500c000b01d48821030b44d5100c160404410002e4010f2050300761a142864902c9551000c041d00d014600305081a41000542c7c9541079500d800c6d58508000036000e180480304c58404215003801a014400685030f04031640d000c50034108041400075902100800c0320014405420340ad00340d807541041d080c80d41c0c440b410b031030001c103980e001e210a140a0046900c80d14030404e0402070884200e01003503540f000100a8562101918681015179009183c1210b4207070004003c240c481c54640b074010002c0c421805203101d22280c610b00e9501d05014074200d01c0c0643e070107800030211241004821105000000d00c07060400403071110f40c900290000400d0005005562100052440d01c0c0702440b00885d99111018420003041d828840801c0c004030403180c105401d458403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 822024946 1250 822023696 822023731
    0x20d0c0809070b0a26070305150d050a0308270303040b01320a030f0b10170a080a110607031b03150306020a05040f080109120e010509010c05330601020703030206 71
    0x25900c1812440828411700c0281404002210b90315174071080c802c00603a10310f400100c1d02003003401461002c0020051042c1d00140380c00003c40d00580c20b0f543d108440d02c154a40303908000900c0303d901314001c10001201c1c2d2002c0140000c00150700001400340014880550560381600c24000c0360310805145130740d9610041c01041c01580340c00910501654000194074040300282c900001c0525041700d03800f00440c2d00040110384078844080c04030403010000028440014141c88041081e48140d020384180208003801c0c0c0c43d15102842a10721800c0b05031000507503c040c0c21900102d8140c1512250101498032002c011f500d101c040c00380040c0ca400403c0141c403041e83d280140c0d46031046800a540502c40c45400160310003054000c58941441021a04140c0554070001d6a8411582218a000c11800e0028120700d520a69107135042500038800c07111180e82c0096075059099000d480c0c4c60002000e801c4840f41d41207148001d41c0c10140138801082000c0c0b860702c009440e034001424465120101401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 822026196 1250 822024946 822024977
    0x1e040b040c09060b090415080a030e0310060312020f0d0909020f090406030f140304060822060e0a05071728170c0d0806091b0706020d0c0809070b0a 65
    0x11101c01410000c2000c101c49515248900c9480d0080b00d1114800c0381818034100340e4014a5994004440d04c4000030841c000c031543c0e0940d044415000c1894042c4618540450010904d01a650045018640754240c0003941b11000f070412510003444070b1035a00078680d401400e03900940e003001301c0303000304801a00c80c03103a07200400341449103c07040c41e801070809901205201245060071030042c42010b00c00e03040850f6061a54490080384103060100c0c1c41030001403c3d807112007252454012a107400c0d24400044c07540d44c0400c5614038295000c06034000c2c2c45010400504000e04070240c1200141c50008110002034565100601564032032650140694903d100509203020902150300225100310341c1e2503101c03099242c1d0054103000c4258400c224018640c40d00a41b406400381d9000707007101001da074940c10368002c204443c0300d203401d003601d0030007030301d4046005c40c07018041c45201d00c1804107441070001c0703001300400005000310b0540c0c1c0200c5420030046038107104403142000c15080100d1091000388 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 822027446 1250 822026196 822026213
    0x60b2b050703050a0b0f1602030a110a0c030b0a06090501260a080f2a0d0e030309061306110327060d0c030623010504030809060c0304060f081e040b04 66
    0x18801012480340d20030001c100032a0281d9181b0640c0c501c402c406050795582d81154440c504442c41001603013040014403601840781c0000030010300c240c4101c48480d002c995510300042c0440d40b00b43c03407006d10f14003408080d814a00401000305891700c0240001d5051210008821400c040e039a0259200b9207030309034540200740044c0300c0d9203400c14102d42d1030302a40410711aa650001c280c540e006680e001a44907600d41c111119044c6040c3c8000400c0320780c5d00440c0646102e00d24242070365041c8000d000d914215941e240c018580e01d080030a601980c6440d01030064496440c03a100f00010350001d00219610b0100030f014004180e418942c000340484400c400300d01c1c0343c49901d000d4501e0600f0200780b0a181c0382c00d60030005c1158504c80b800752001d1000c1800076103450081c540c3d140002c1040208102048280e0b010301155800180140e04c1c104107280620b18550059124501047c08601c100440c0c2c1d82210340070741c1c802c40d40c03000b90855403c01c1411070b0840308000e0005110700400c00c0400e0600c22000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 822028696 1250 822027446 822027449
    0x1202060105030f0a08031521032a030a080a1509060e010f061b030905060f030603070f062001020f0403140d0c02090628230a0803040e040611040909060b2b0507 70
    0x29232146585401c01460562030368401040046c080265082038046001080f80c401c0c0421424000f071810b001e05c001c0c1c1102c60600c050180c031100760300c4010b1040e074205003c000e18014540c030000014100d16103032084082c640142d0048010007003181042001c160807030100705d00b140041c4000f011281851030207680003140340e007207543c20107808074010415503404002035010f9030085040b00d0300e20340e94140140c0986094015007000480741c0300c0d022003a0441010400011440100240c1491600c01d101d40054001c0d900c10317101014010001030710404144030b80c601441003490107004500254020a44141016141c0b600402d4000640d009645070403c1404031a400c4040d081e40d03da0781d0354441407601c81c2d0042150010300241910281d00d240070340e80c0a00301c8485001a43c24580b40000708500208000c0080d900c0079105d41d4420500d214041c000c3c4054002c14900180c403d405050580455201010403030103000202c1303030107125800c1a4803410005500303c500b000500030b10303c2c00c0d43c14241a03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 822029946 1250 822028696 822028729
    0x201090b01090906050a0e030d0902040b090408130603050106050702060d0f0e031b030c1519020f040f05030309090a0f021c1b0503040f02100c1202060105030f0a080315 74
    0x480d0001c9284021500200d502e140114814070075602c40a0803401240c1655180c001e8070b9000308051100c582c1d65800c04140e00d40018000104424481c02055046000325005ca8600100065210700407001a0310380001c0c121b14641000b003907062060242c05807040b0113000e0700c910f00103d0305800e0400c1c0703a0003240d0f4092803050244913509020104d103503281c000000120b11240c1201010340c80c0c060000c140c4950f414038000925121507803000c140c0c0408009400020b021300c0f0b0b4003501d4200740c0203000901035100d000c50341903647c5242001da8010418190170291181c0c004100054240d541c4070703040c0f42c11280303000001810140300303078815000f0301c00e81c1c0041d8200c3d5501f003085008003116901103150903c4040d018098103101d0340e01100c4620080310000c1c041e215402080025050003c50f01d0412003440c00d0112050f045030703d4005110044028090050344801700501460800307110340c10095059400414000c003441c1c6d0355240d03030b0000030300700030032844020308192496a03108150f00f0f03880030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 822031196 1250 822029946 822029963
    0x309010b0108070f0e061b030724020a0e060309190312060609081e071e0f1205070603020702150c060915190f1b0203070b0112080307081015021f05010e01060c03020109 74
    0x3850f18017407910000c000034041c43c1c1e014107401c2032b090300d08600803503402074100c1c0e4a0380480c003400703402c2080c107400140c004440e502c117040666076081860f801c01450540240c89858000c070100208000351480d41c2c02a40802603802420841c11500040c18444210300c00c0d8099060f951029401c0c1c82e0514a40c0501541c0401403a80d945221030b16603980c05644805e03820301481c41e29102e203204103041d0000028030540c01340404005003880781e40607040d001e04c000c0c48000707000e060096140280d040050113600580002080c0000715404004000c6041001d0702ca00b18549021300b0410400b169040020041c142c135504075840d103050591040000500d4604000301158070848025626044140d0031038030034480200101d903e0080b103440d07103101680428024071310b03034800d00200e488031006841c40c1c1d100d042c6101d0101e0a542c8550700b00c00340d862240c0c01080e8420054103020f403003114202e400341c1d40320315000c0140f06041c0461300440c10348049003030640e0712100b2481c00700e0040400c9203005d0030360003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 822032446 1250 822031196 822031207
    0x30c020a0b0c0f030a02070605030c120c0309010f0e0d1b0803010f15020c030c040b0103090501050a0203090c0906030a080c070e09030912010b010c2301020309010b0108070f0e061b03 80
    0x2480c4025000c0440c140088501070400c000070783c0c0d628441c0100c1c0c140583c1c041c034001c2103e9031096000b1544191410788103400c14854420b282400002a00d418011504c003000b04000018240306441c0d12642d035240c01c6c4000d0300e8104030386894001d0712500348104081240b40c0c0d02484160f44902d440c10f40e01221040d920342c4e4648011b12014040d01038549002400a4807982092000841000700c100087c0584402044541000020204030403c503052580b05d41916011400c20f204152241c034070b824001d603881c40c1841050b814580c8051741a03101c0d000f00014003c541d200041c55a01007940b1244041c0d44480c180c02c550320382641070b030042181418140c10000c10540c0130000d8071820b83c041d14615226800703080701d282a60040c078022800a195804960b0200e0088411b8480054880384866072074550f0605a5099078000c0303d0b110866034648482c01e2031541e2010303401c1d5200702d1500c0c1082c00510000d10040c11280a40d00b1b2034464040441c04000c0f41040c00310248180c0e500301e045a6580 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 822033696 1250 822032446 822032459
    0x6080f011406100f18120311190c03080d0b0613050a0603050106210b190f05030a020d14031312030201060905010f0513150e010f120f020d030c020a 65
    0x2000d00740a803258042524000c5009400c010a01c10304021441d00d881c05005070300442290f070303000c030034045000366400703182c0000707581614801920711140650b032500d12084400120610705a140da500d0b54829884091000102e16120150402d895000300d406945034540c0141c3c2018045501003664800070005501e100088203400c080d084a40554514010582d910380c141c0840ea801d2041c00301180c8448001055101c3e1580030410341200a0000510308081d00f000c1018480a0010f0003540007820f40c0510030382c0d010003510402008214000e000c41c621581c0440c1034008031880042c80da008441012051480c140242c80041c4503820301c03102d003250365441142d90440002c00c15009540b80c00302c00702d0300740d0781d074024103050314444508184014600340c1032001d000342480f03401d42ca007070340d0741c2008a158200c41c0741034004012500f0980e81550524424201944041c3d02040040d2041c1042200003036511000b40081a0100c55540080300c080c141075491403600f47e802580032042c1600842c20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 822034946 1250 822033696 822033701
    0x60c0f070c0f1d01050102060f1f0e0106030f0e0313060c030c0605070504030605060a0e0601050c15090d110d0207120809130219020f06060405041403210627070306080f01 75
    0x2082100f4460305140c2d03070312001a0303122201683c0441135100c486001500031444200140100c41400b51210300081c0d80c4c400ca5032940400782c111400203a11101c49003048040d60140c6111040c40401452500100e000c0c4042801d503184200b80500000c070f141e050500d0300812482c001039130020824080c2d45049000100b00d40d01c64017084a03450300c0c10000c5074031414416200010ba88400400000b261240c100559680d0005e82c41802c0e284070303601e001c0030030b070184090443c098801c40c4001c004141c81a8000f908084403100368a226500140707200c038403264006410f81c210394060266002c00d90450078501c06600c218012680c010148490900000070160300515075a003c1f0295612101c172901800c0b03888820038400b2100651001c0003003151454581e01081c0c105104190b03140c1645520385003507007190025183c024400c1001800003070745034240b0414541c00081159541803010481c0101a142102d169208901040800000d42564040c1d806000905a458129114100c4110300b0601 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 822036196 1250 822034946 822034979
    0xc251202030430020609030a020a08010606021207030806040f181a06100815041b09290d0c0e3a0206070308100b0304140708060c0f070c0f 61
    0x11001e0034040d1010110b40c400003c000d00c038030041d07401d9068021540070003a00b0b401020f42250b01d03010340703600b090040e6940d4202c0b0740103107505000401e0742458080c0107030030071855281c428945481000100000390384101d510794807942c1104d0000300c0301c0300c2200030401011400340311410031b281038541506100c5d04006490304000000c030318903099558a0180110040e00340220000716903c0f0b000b107034030b15603a40051180108003070030004021821031881d1003551000c280100200b80d2104080c014042c2000710a144c50810b00700c6460742c0074510480c02064400c0d0605a02d240b82c1d034400e66400d040c8640c00410f408900200704140d02081d042500174000484a03400d5202c0301c88000030f070203240b120103d21030142d400600c85400c02c66661019110500c00900340c5000c1000d0713100c04140d503180440554002d9001c0c0784078550219085140d9072400c0724640000c19640c0c0003100304011102b82400725080303255082d000540b150145d150200300d2040c1d5170001c0c2c40300c24031030401007100c44c05d800f403800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 822037446 1250 822036196 822036209
    0x90f02030f0606040b1e0d0612060e030a0c030c170a0e13090203030f03090a05030a03020c061003020a05010507170a02030703021515040b0303070b0a1a03060c2512020304 75
    0x2029610382c035082080c20300c00c038410307421082d40500c040c0420b084448443e60b0503007842208245081c43c004031a8088441540049035202070600400c014810300d44600130840412800a41c0b800b454048090954951070000a04100a40141104214543e1a040c0c03040c00340c22030103500c0781c03441d9102400000c40017031294003c1c0240d84c1017032122921802001c0c0c2864015014501c3c6c00c0a055010f0f8030740d400145003440502c00c0784240d5002076002c100501403018299001030301c1f19217003032003030b420003402529146001c1d10101081c009a80c80d000404201c1d20242886640d8000f9807401c4034581400b260700b24107150740407949004490300403005140b058825800c0d619041107122149030031550643e00190040d10b0410410703041c1c10300c1e070f02c80041c0031000ae0899061131840c0c0d903281491101110b100101c00e032913400c075014a003003461030303503d0000040b00a05000e20301800150f581d40100464100c060070620808a120b540170a458800c59800100e0095400d01c5000003130f60300e41c4184030f2171 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 822038696 1250 822037446 822037471
    0xc0501020f030f03070513030c0303051e0a0905060901090504060308301902070204020714010e07030506160e030f01090c0f06020c120c040608010e0c0d0201081b04090f0203 76
    0x40c581d032030303001c0102c07100f1000c1065100c1c00c0d6154520304507107541009440808440841c400071010840c1c1f504980c00440c46170380e03403ea643d42640d402009252075100000400c86040c49100e80141e000740c41c10060f0b8105441154441440c0d5004807412000c3d5804030760411710300400807007400784100090800400e004041c1c1c000001e4002d5a05052040d49150810313084004045a10b600310000911a42c0560210242c1842c42e1500082d049138441c0404070b44400001592a07507041c400e01881c0220002c0c2d0014008541ca135844503515050004d059100386400404007042c3c290103106624058440a001c44608000c3c5102290090041e4181a980c800c0703070040000341d003880b00001d0010307601c003a03000d0112000c181003444502c0c4032a090181080c0250620000d0548070341c410240100000800890b024002c5d030001404c1a4400d000c85008080d44640e2a01603600005000e80150000c21080c12240205065103054041c5801c42d1b50361a060800312540200181c0183d4022280c48212 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 822039946 1250 822038696 822038713
    0x7122906091c0203010207120809010605010228020607050f0a060b0a0609050603040c0e090706030f0b0a0b210c03180f060c0928150305090c090405190c050102 70
    0x104825400340c01c0030141c2c041c8207a10030a42e03003084001d401050601c042c0c0003605003882e1350748856941d0342ca80100e50000c3c05403810032001d02024054240280000e00113040800d8148134482c403c64107200c49500b007030700c0c0408814115107c8001b01d0301c50382d81000940d4080f214007400c45482e480030260a580a505183c8150681c0c038180c1c9450045884a8881020091600b414881d00d81c01c02001034641540d0100001000041c01e80480d21601c4820068000541401000b0b01212003412240101c2c03840c2080e01c0d403907500e8800a8a090340c590a00442e1104411800040008031038400c5141291200c0248400124400e0280d400f41c0098103450f0701043d440c101e401d40e03600c05441040308035407103640898850101c400c0105000074001c1c0000c0c0b0b171440d0700129025004480861010341c80e102080410880500308000c42142103c2e1505200d1810261400c981d81d2101c02c0030b091260f5540000b00381008020400c80694440c608c3d0000c0c00100542400000241c880c840c0c18098000c103000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 822041196 1250 822039946 822039949
    0xc0803090906040c2705010f02070b0f1608040914060103051608100e1006020d0c08070b0c07150c030501050102160e090c031e010c051809071229 64
    0x39203620400240c8085190b0392468100b1000c1c110f004001c0e82845240c2d24401d4819000754607440d05440708803c81891540780c480014440c0406005140442d00400014001820410201c44003c402400d00c551200390074600640000010503005060020004000448802e10b030810304080b41407040900140c0d039102c1c01034064607011208241c2c00f14040b40441a0705025848868111030600c0a80c1c45454403244000500a410740310103e02d088031a8080000d16810003001f030340304120703107840b00010318180c2e81d100e107034054040c0003458072082c44001034000b1590b400307444d0b9030303038101ca80780b0b0003a19215a5030000780012828100004c2c10000081100d500020701c0512021190f070861502516000c241204031030003030100c090a010340f02806450f55020044070041d0000d4200868025041f02050b5003100ca0710707421034007445828403501c22009641c11202076210000d44035203c050342d803c08201e4140a00d00c10181349545440560821b555180e0061541801408110841c0b00b13031000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 822042446 1250 822041196 822041203
    0x16090b190605070f150e0c09070f1e1e031e06050609040906061215180210050a0c020a140103051b0304080a020f060103060507170106021009080f030901090c08 70
    0xd81e0042002009010002400b101c0d000b5445800f601000c0c8440d030304c641d1008240ea40411403250701d0703484411750503050b00c0e2a0110640044290401c2d071202c1314214409881e60241070400131000110643c2e03110301c1405a03040810b400c84006007050110348904c80035000f4244020080030307001303100ae0303070040021103882000141c400050900342040259000c00010345007880c02100c00d01c1e01c2d4280080d05402d10745407442032910940c01c000c0c1c6591204805001c454603034a00381c0350740f284010b00f00050b0301d0300400c0c0c030b000425078589141e88442410060700c1e18491380000075004a00310100150005d98100ca5824890090741d0a001c40e48944160b0b4060128201c0e00c1200c1010410100c1c000402c4140140811045d038010f41e20100240b200c1c0c2814440264019600b46442d00b04000c0300c2c690217508180e00001c2c0d000ca89001d03506000e130080d611400302c6c1217980c81582d64a044070900654030151250f0243c004c00050b56031a241c41c110b8040d1a01e02003c541d4051000c03c08140f8a1020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 822043696 1250 822042446 822042449
    0x80607110f0d02060a110c010f0509101a040e0a140304090c0908030f0a091a0a030b420d020903060705041212031e06150216030b060316090b19 63
    0x6900402c03090710780e046200700800800d100d2880d81d0004020050501d0004e001c1d89000c0c42a0303100020341c0d0714241ca801810300700b640c0f1450b44841c5c90003103240c400c1e400b10210340e50204014ee4000030070364030030a0003a10b000f25101700641054135002170075115041c000000c0c0141c0e01d003d48140980e001c21281962200300318022070985070006c0c403038841c0102071080981016482d61410303c080ca65203544003680d58000005100d1940000201d80c00f00329090700034501c0290041d1082d001100e210300d2507252281e81c0182c0e0aa00000c09005c09002d07c403840400440982e4001030741d44d4400141416030001c0d4480c411090180c001c05001500840c090b5058400b181c00c032801401c0300c42090780c2d43c0c3e8031104042000505055468403080490503280fa91003520412141c000a02c5508051420b02c00030400080501150300c200102c800c9443c0d402520011203620200c0241035880c0e4000083c200b11003250140701000500703000140c0d00845802089400d001074550f8817040c04c40003c0248810204d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 822044946 1250 822043696 822043723
    0x106030c0513060b1303120503150d030905030d11010c0e132a0e01090902031014030a0506040b100504090c050105130f060e18010303020c0607030306080607110f 71
    0x9103030800541c1446445110b110b60401400916940c4400749104990088651341c112100c01000034405c0141d005100b80940c2c2e4582040ca08500d0041441c4124610034403000f4002c090803010f034001c050041a0120140c0002029a231186c07038103040040001e01c14400c008055170030300c0700900e20a030264541c07820330f41d4041e0025060070049141c20020301100c0107400e401144e5002101d18290b43c50490341d02e008020381c0c0d031001d1400c0c02c00005011540d203400a026544c810000e101032161300302c5189045a06a90300c0c140c04c1c822440000e414641c00070005409402400c040104008a26103d644030302c8a210060200369107500904c4211002094000c0140d16503400c24411580164007400c2507002000c5070080305900c03050070303400d0b1340707210307404440818114101c640d903600e070010441e00052402d00440803d585140c030000e640e1141c121980e800b607075002810105252103a008000502075a40881d40340d802c21080c014030314066900c107443e140c06035244000c044035010034101c1e1042d20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 822046196 1250 822044946 822044963
    0x91e110f0a0c0f08040905070306050a090b0607060203010312081b040e2203030209040b01050715090305040305032a210f04030c0b0a090f030803040609020402091f11010603 76
    0x404500d11154010905031003800304144140b000243d0103645038011604c51a40309840b203107084d040b08140c913000750000c001e150030020180401d490f40c14102c421219200030210b40e0140100209082d8410000c0145c08140000008001e00c10a45084800401140e68805050b07403020820b40e03490600e80740d40d2260301000c21080000707404c4114469048010701c000000301c0165900341c0c441d05000240d084010030340120b00307200685230503c01c02041040c2070a100340381a500350b50715400e030082041e4084115907030302031100506100e4004d40c3e001e5540304003140e540f03c184c9103440100c00c40c0500b10104c540104140046150780100d00d07508072802c10488000621540d04444055821900c9140c01c078810178440080802c0b407000d6102e0040550041840c0c3c2d405281c5c500401201c22a00164240b10794240c0400004008000b229807040d0041d40004029410388000740103441548049030f4011680d80301046105034401120300c0380d8101d510340e8105d440b59526400e080e601c451002504981 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 822047446 1250 822046196 822046207
    0xf0409021b07061b0606091404050c06040305100c02010207050d17100b090d020f0409030305060a05091b0a02070306050a0c111207031d04050c0a03050c131716091e11 73
    0x351341011a01c2c05071180e20007041e8291980fa030344048030984503020301d061f45080240700501006101070341d4081001d41d16680f800d070a6494190782c1e4503c0d400c110904603602d44185148038401c3d4151901260301c90140c0303010300314140c0000c00b552107040001a204081801240000744040206001c80d241842c1d418140000e20b4104000d88481160903a007001034160080220b540340d11400096500c280c070006141d0a055052040814042e00014000c0c1669420f20014a030040c802011a51810000903038420048008034289009503000030441c90400f000e000c52200207400c0b2070210400340d500c911001e041540c16a60350cd441c1c110208503001d040041401080c8121a00e120004400781900c03029041500410308645080751a145001004100b103102342e03a03d030181310f82205034052440c2c20050b10016900340520284501d5203001c82c0810301411100061200c0c6540750004503004049640d5410110b01070034a040707a80341d21080e10040c580c1d180d2010700c144206450b102001a00b0320 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 822048696 1250 822047446 822047477
    0x30309150a170907090609141605070204022b1104050d11030318030d0c051e1e0c1327021c030c03032a12020f0409021b0706 55
    0xd81c4592400810406000301000d07640d459070640a0065601030010301c012850400701c04c0498006030042c441e072a00f810440a4510b018090080d040311070400024509070814406990a11408400940260010640d603c04118003680703121003507618503210050740f00c409415012140035807014112038030140010702280c02d2031034200702c49512507881c1c904035200f10301c0000c1c510707000102c6901d9094a00c4018421905052000c0f0100e034035282040c03c1641010f0381e43d5030700c502150300120100c03102c81c281d014036070004204c07404041d24141d071f03240d6650402c800c0080e110003150020324021000c81c1500d0040d0190740c840c2c40032404480242c06543d030002240a00a03988410b81664007001d0316101c140c0700d125007900c00c005140f00f500c624650141c02d05c0c014042c0c4801c01c14410f8140700150f038600e006080d21248104000047c5040c4070b41400d10001034000703001c1c040e4103a1b10707600c000c6004109450300ba030042c84d045840000c400c00c666000d0301d00c0e66031410705009030800204d03140142c0300c0c02c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 822049946 1250 822048696 822048739
    0x80a03020d0302090102010e0313140d0b0a0b01030209091302030628090204060b03150a0909031d13060303020f01060b0a021c0c1a0a0614061b0c0d0302030706050105030309 76
    0x1307188051001191408a04481c2845c0d9040001101c000c0d9042d88000c0005610021202440302410f55840501340801e882d917241500d001031068640365100e040c0c80070b00380c1c4039604440d91207200500c0c00c80c140c2403440c0040307442c80c0018400ca01a11562000c5054480c0d41890080f080f0204000030240740142d003aa100500841d5004036041900ca10000c0f40c03001da05d0000e144112251001920f5400e400001c1182090813607000000b614a81a8000c0101c2c0d440f034a448450090300340e822061603100b10101d000031030100c501207803461174040003200701980803490030041c1c1503000007803000c0380e21000c800459100d50522403000da840103102c0160030a641074a816100210f0a064076a0041a1101246221520301c12402c2007a0b510400800741300034030030b03c00600f2507141703404101c0c4480008264030740301d030400f00558142c02508003c45080d040100e000005006400752120780107031b02d0040c7d5690071148044030380c542040b0000c00c1e1130030008284d40d64140010b0484071028040382c0d001c1207 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 822051196 1250 822049946 822049957
    0x23012304031b0e0f150a0302011d0a260609030a0e120f0106090207061505011b050a06021207021c0f03020a051216110c0a031716050115080a03020d0302 67
    0x4003140742000000ba0075140c1c0c0c00c003902c948548444d0404031700c1c107a9403001d424852140c0092103610300030410700150740e1100700241c103804401704005068803140001040c000c03036584618001e6040c424500000c0e00e4204500314001040c0c03007141c296840e503001e00c0d51207004034420b94000608050501859113081d03400c4203817440011040c0c40030340500c00e17055070035144117411600071580c0020f01c580402070284946d01201d05240d41580c0c116090030002003009102000200316140302c0740c91032080c0003040c0110704d100c1e41d1100e800c664030103120f004400350b680f04842c064054014201d0320030324079a00d000070040d407030041d5494440d03c0d45c0540e4250025040b403520001008018884141e01100000e003e50217401d8140e506a059481180300a00d081540c030031004180c0c001e072001031102c0d2500c034a0041500da1040710b032170000c80c4000040302c050080760311030b0300600e004a07045c03424008194400d404910f89421041d031441d072168003141c0d40305031800000f00180e020f141008501d520aa02415 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 822052446 1250 822051196 822051233
    0x90f0b0a18091a0906070806091b09010905280f240306031e0b0a020c0c1311130e15180a0b060a02010e070801050603070314072301230403 61
    0xc1405a80d4086420030f4040300c002c42244d0040b01402880da80004070359078070800445041c00f5910303200901d00c000388008264102e0207440420808078980c010300740d9030090701026003100c110101600e1605142c800d840014920f410031090042800d03046100b0003402e032100308550200600e030b13201806c40b8840d030191407041015074500780400080e02c01d0b02c01002054810f2400742031002d041c02d00c203a444101901520382c1038070400130154114008a03801c5010a42121200307140c6a00070410b01c042e241c40c1612107000c0700002603140217104c201000d8000d444510a100c42513903182074119075800800500945d2280c050740252042c44540301d550ba0b8810200324001c1500b1707400780c011800c5500031060f01c03000f503516818681e1954404008102c002c00e440002880340f405e003030011940f1105c031030001505c2d4150081c1e1920a003e000c118140080030022146c01c6003407482d04080e0741d501500d0704070b84d000600310b00000303121181c0c0804031210080580c0d062440c02c1d02d59034415803075495029581 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 822053696 1250 822052446 822052463
    0x60302010914062a01051518180102030709140108070c0f02040f0c111b10230d021b01090b16020a0b15030708192a090f0b0a1809 57
    0x80c00c40c0b00790800381c5941c0141e0407004e00c0e002c091200c8442d0a5441c020049403091070901c507200d0083d580d00940d54604000001e210b04103071140c8007400365a0f5400c0030000025800001030180c400e501186000031140b036182203207000800381c130045640d070300242c0d11a000284190103080100703a50148031084180300600028100c00e001c02c07040300745c42c01040d100020699800000b5205141070141c052401c840c0003040c00c680078203400107010120301c83ca0040410100d00c4140c0c00d4080c078182450390340300e042c4461075205c51500000c1c0f400780d4094216100120060145007041c081d0500903107440340c0d8800340c01e151030740e120202c400106010404201c1144900180389020034020400203018510f4813420322401805101403520b041e0490b40080c000784d000d009581c030500c040d0711145001c41d80c460401140080d4241e010990100025aa4014400d8071a000210194103911140384c03003d80d010107110002c02c40040201003020ba00c80c0300c03c0b10040403411106008158040b608091141c2500c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 822054946 1250 822053696 822053707
    0x30f190c0203070e0105010e030c0a170f1615110703031d090a050a0b060304050607030f0b030624061303080a0315080105040b180a17090411030a0f06030201091406 72
    0x1e00e070a42135400500039140f5000184a41e59101540e292158402d42c010002324500d40c02084005807581704180e01868003900343d0030350403800d0201000728109c3e90101d506080840854040c01d2410b8420b01d00941c1580c2100e44041b07000d0441902c0040b107910240602c42c0c0355440682d4400c90842a68804801500c00441560340e9042d140b130084d0345409001445141c910110000c070740fa0790842900c01c0d2018002c110016800013002c550010f40c0c1e1401140182215071024040c203030003822183d06002d06410803818a500e91241900800f03212020038403030229805201807481401c504040e84c802c0300d40c0c01c1c80410a0a001071000410310328000030741c0c40341c50b4216005d0346c0168011240594481090000780b00b015a003403a0044003002c0707149081e41c0702140311917541c104118001d02c05422000190b201e030040000b070b2200303140090001e1000911201c50390403540e00c111115401c052030400c034040d002030b241c80b403842a00d6060311985000b5007000300a500d6500400c900c0755020100300310 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 822056196 1250 822054946 822054949
    0x1e12060602030415030b101404050a170d0e1809030c060108030417031216030e010509250b04180b060706050f0a0b0901060e0102030c03040f0512030f190c02 69
    0x80000a0403180d014607200e030b04200b0f1030b80b40440080300c0c3c942054208402031885135100305403002c59400500b0710f00e4050185500d43d506500a50740041d500c1114a000080c80b140d0780151100507000c440143c507000481e800c402d0700c000e614280d005410014144000c29110780340380345150032090540440b400c01068080041c81c0c800d00343c20003070240e00040390030040b810009120780320380303206013019604000c0c90601144003084010814101410340f01040b0000e1408be5000c0c039402c9001400038441890a2a060380e42d031101c2209041ca02100340e660b004040d09815000402d955034014005c0c505132420024642081c2085147c0e000540d039440117400c0daa440701d009000a52207404040340f98645442034941a04c4010241000b03281404000205541d031002d00700e0556405040c0a240c0c1c107030000040b40f45000d00c00c2070000038407000601007844402e02c2c41e2041281d6007141c8a01c80e02e62280c4105860340581c3c05142c0e0400300c103015040c40c1c10b0380844040d15415070707458040c8000f05d0980 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 822057446 1250 822056196 822056201
    0x2070e0106020a02090906093d060f050d21020f030304030c11030d0f031a0901030f0203010506011b0201030c05090316150f020a020f0d080417010f0c1e12 68
    0x240518090b034848500c3c0d030110b05048100030b600900101c060009881c08405d05501c6084400d00c000501c20103403034840ca0240d071031407030030b048400d02e0703141107914424048084010304481c050304d2819158140d0010f000e00e0a00d400304c005560044080e00c001c180c50050240104401c1da07000103500030035071000b040101c200003462003180a03640b84840c20080e81041c1c0e40005000c035a40b4065000408001045c581180181c01034441510380000c650b01512400d051400083c2501c030350000c2400000002d104400f0400001a8000c900070816919060015682c5110341401501e00c00786010450f0059806540650f0080d6842d003822443c140a40c00000d01b40030800d95140307641d010019040c451080b9030340f8001c580d0001410b11a40200255001a42d00c51884200038070456207150200d45075210083c00f261034590008505031110f4950030142c000ca07281341400c4010b03600c2c0018003200030240b4083c0720800381180e16000c070f404410042541d0301c000705d0204c203c180140d01c0e03581ca0040f10b462 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 822058696 1250 822057446 822057449
    0xa180224092d0a053f150609061509010207150c05060c0a05041e0915150516021c08180f0a0b0f0a030e01092301050103080d0c02070e01 60
    0x20720001a8880020582d00042c2c01c10002e6010359496002800075031941e00d0016089001c11056009201003151080c0300d41210517031040c407007603503501030804000002840b15013610101d4a90f9610390741d00c0c814010600c40403100c0c1613100740c40d49404842010508001d120440042c8146c07507116803100c16110050459400300c02c0015625a182414840248056500043e4816140b80b4103006444010803900480c02050b480f45444807060101c20303840904400140306202003804000801c1c16201407480f450320441c0c1d000030404807540c42e42c500c10b800f1034003200841a890a1a04829001d1100c1e00290b82d00420f1401c50f5a981080402e64600c0071304203001d200000e41070404040014040854014030070307540100c2c200766017800320307079187c60994900903c00502a5156100408228054080c001584201e5407811107003900307000108650040301c1d8041030070310381806a8114064201e49092001408420701071000200d0108103801c90102c2110910465038000c3c6c0f01c00040307088a00a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 822059946 1250 822058696 822058729
    0x3050d09120e190303050d0b19030506180703021807030902120d09050105030f06010309170309101109150906040308040b030f07090e010e19140a18022409 68
    0x29000250580d24094510743d2492580c00406441a851a82c0c0038025000704038034040080d0716071746001c0c4242c640e00c011003a0004820340300e4030345a03540c0c109a81c4808040e1403802e10000c02821440c2d504000040c60340031658041d142d402d26003414031a5030800324026210f0000c040d1240b0780440940e0700c40d820400c007041c1880140c03241210088024010040580c4500d041c0034042c0200003100e0f0b5000c0e5119070210080c2404284ca941d603181130071000d00001055204005d010041c00b19801d80095480b01e24041c0810400c0311140c0106542c8141c0103c50304183d1003441131222240012511020304840b24000d400b184c2401e8507541e42038140c3d0810f40003000a40004005c20201d49861028a41c01c22860f00b001e242e558102405000038050500405020054250110740c81940348090780150001c56442003181c564440e025150486050790b4000c452800d01030790680d07070f49d1807100c2c03a01415030061200440011020601500000c090700500c584d003006d10502e0f4082c0c47d24240301444000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 822061196 1250 822059946 822059957
    0x30c0d1a0405071409040923012007081c02040f060804020a0501180e071419020c010f021e030f1c050f040c0506090d12020f01050108030c03040303050d0912 69
    0x80300814032044650092440080100280481010b004120215481c402042d50042140c44140c200449407001c14848074500050040807401c2900c4194405a907486031000406410070888480e5006401149006400070f441003040c2122102e442d081100c001d4002d82002d0704255440031400c00d2005c1a03800a008111000104411454590100005850300b4240000c050159160306c1d0318540442c000c00c00341d00f14600105494901601014001c02410000941d0f40c4501d18001810940d0007440d40d009417043e0110011a5070081074900c4d02030700154028148102e4103c0826060144900c181c1c41d41d0004201d001601804840105038a0100001d04100f9154030001c190849400410302e0680702208000d100002d4096403821f41201c40c2151010b13154043d00000031700074580508002c0c030300144403a40b00c5140381c020821000b92511007008101603a603862029031a48244147c50010360402c200500000f40948041c0824501c1014001501c0f001c0c0e0b40d40d50440d000c0410000007150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 822062446 1250 822061196 822061241
    0x6010e1c0501060b0315150f041d070212031b0c0d0906020633040f06150e041b20011404021f0905040209060c0307060e060f10050105030c0d 62
    0x3a0034001d03c8014045140c0c500d2031444c0c81080c144824a9408a951007602c03003070104480302640000303903144891140c0301c80341d5850f602c012800f840b9031050b20103410405600b001604650004c40c1e0301048581c002441451a46c48005100d1380c43e04604500300c40100034010300210701020060035882008940352043d0807400d02c0400b070701d0a00f00a0103400d805141c0303103040c86c028030088078261100c40c0318507003000114032420005011741440031401c8111890041d00260f0703c1d006100c00d4001c00d201e41c50714420350164900303000907070306554951042c46282c079080d00c080610440d40b220b1101d40c068140404003c0e141c0b0400d081d1503075858928851765207203090001350300e8001c14500002d1083c082d00ea00c1c81c070081d00c010b0f085c00aa072007964822036000c1018480794561400700d0350b20701508415030b0ba031001c8138035181c4010204c14850851340e20518002400c200080300025000b04565014542071502c3c141c01140c841d40b00515904c0c40490900c00c1032210a804c0c003544a4614043c0100401030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 822063696 1250 822062446 822062453
    0xe0910050f070212031b0a02100b0a0e010b1809070201150e070e0d030212040e01090e0d020a08160f0b1b16080d060f17060a02120a0506010e1c 63
    0x1514050404018501100d09008185070009002541e1020500c2507940301c0da100e030b0b02e40d42d2280c19600c403600c0c0b1b014001030b1038240311360102c0c0f46520000f00003000c11401510300301780a0280014010700d81c1c03e200da00014003088004a01401d034440c0e080ca12081307070341250710120300c00c031400340c03400000740c0c4d1200600c070f041c02c2407113403403e000c1c2140c0100c10300304d0303e4107000003041c07507d240000ca40500c48210107501850b00c01d011341c1d401d02d07405494195403a81c2ea443e140100d2003003485645c40e411300d4801d405143c4000807500031418280c0754006d100304001500e5040003035104155510205a6400d040340000383c41940c418a030700d000c0c203510101864408008140c0515a080042c2507200402c40c07026401003004030854100d801ca50b45640340c02100441e40024107003a000703402090044079000442c1e08030700040980d107170249003e5a00366101c10b01d40e00d00ba4050351008070009a40c20000400310745896201a80c0414145890041200d0700c9010605200214011011184800d43d0040c01e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 822064946 1250 822063696 822063701
    0x5280f150e07030c081b1905032a0301061203140d0507030606020607020105040215071a0a0e070b04060203040b0c01090609230c1014040e0a0b0f0d030c0209060402040e0910 76
    0x1740343e0240a4440307101310349800c0910074142494a07100391707002c2000100518003190341d08003802c0b019045400c0c0410300c03820b8180500b0361984041c1003a00481c1c000e9050b00301070041c04101d0396601507001e40300c42183d40c2560349900854000580003014010078143c000c07940200f5001d05000c1d00c0000e0f145050800c001c2c104000200b01d4800d581c1080b00f804010f840b00d00302a201682d01003071880c2ca8845034644003a1041d51102c848102d181407030281720030b98440703510105859104030110b4945558030744158a05001d203114040260304280b204000315130080d170041a101c00300400000d41e070000d5640310f00c1100c103032203003d1358a8404641e1180403080c101c2c0c81801c2101841c002461403103042070005e00380305e82c65020381080018442d00e20111424803025a806441030300b1001c56280f400407625001401c108007481d1054042c07841503085802c01d180c0050791543c0650300d41251031116003d01035a01e00103859542c0007a8200000282030760311800260280b12600050128070401840354410b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 822066196 1250 822064946 822064949
    0xc0306030c090509070608070c0f050c091e0712141e01080705030304090f090b040b2505072409030801171212040204060510030905280f150e07030c 65
    0xb003491620013070120080c00060305604070b880c6840c0564040c0c1d255001140c0e10b40300890010316150b00d092200c3c2c10020041041c4205000c03d031803945040d035810140f62100c3d001d0783d10301b080b002821404030308554406d00003400e614501d0300020500d2080060440ca001108a4108498800420300070441d080d002d60010b00510b80f440082c5040350902000039100e01ca54810031082c240ea40529011610507500803c20554004200e09502e10b803900b004003011700c0880e2281e1504041c19000d080c8803090000582d00034035141d842c40c0c1815901d55a03000301c0d101a200e4601d450702e001604119144640c025005114401d5455103503651600390100130520b844030050301d15401001d07072004440d0700c0000795203800c07a21000032030041e241c81c00860010b0815400450308a001286d0031006950160001c1c19140d210340e007100c94039001400101d8211900310200d014070440211408080760000442881d00d50180f8543d080544100c0805811550107075001e010344d4100c941d0400502101030540d40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 822067446 1250 822066196 822066209
    0x221205251503090c0b0c060106021507090302010f0c0b3916150606030506030c0409120c060f020307091e030f080304150f02130503030c0a11060c010c0306030c 70
    0xa203080144107594201c079081820201507a9281c00e8043c4042e00392404000c0c411001c5050351030007929030241d26800d0034000c0001502c00e161000c4880c403911000c883c443c0030b9a580f8a0701c00b0341903500440341001075016240401614821980204007032100d000e0066100034680381c0140d0380b110400c80c0e08856121740c1d4140716140f02e504140c9003a40c0c07044800a2410f040000410341c01442d1000c288843d00c00761741d425918140d0013040740740c0c05602060090700203c04441d042d1891b03900700320945020110043c090340d91031001e03c2880340075402d070300b100512441011440301003045001040380c00c110340040004d441000200690281061110410403224410f03122181c207648444950615000e4000c1c814240080050180009580d5200107004040030510100101b44021000394201300509403020303d003210005800d00d00001241c030344121410113424480d113551078407075211507003d2003150070040070020304180640a101e80d000b030303014641780080d07000d0460034a1404000720360442d5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 822068696 1250 822067446 822067513
    0x71703090f070f140118092309010c3e0102091207090608031806090f090f0412020c01200c0a150e0109261207051507020a0206221205 59
    0xc03075900f21015007103015280d02c800041100c014040b42c41c5103203040e0400c8d1000c00340700c02c1d0503c003800206412200d0848129607503040c2d010600c5801c8903070000c804400d14204207070900d00ba00c2c1c100b4076119021010421078001410440b98002050300400600750655090f0001c1d0300038403008004c3e11961000e812410011800c040c0c0503103684688030110b40c40c2c130748030f04004030301c1e07503100c2d61507406250001c1000340940c10a800c10032101034505400f43c030b0440d0f900040802231280f841c03000540181d0342030142d4070004a0319806c0301248044c4c0302c1d903646d803919000300c019402c07844d1180038029006050040012740c00001582c00105401d10545415041022030b130310802c1004210700710801941311071a40040d445c0307440c0d6101031400f12415400c1c00100c601107100c500380800402d00d02050300345480d01400903620020100c0c2c50740c58028000354002030600c0545442003001c1c03110a810580b008054003040d13141c481c51010300c4040c580031542940310a08a0782014940d1240401c2001c0d203e191 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 822069946 1250 822068696 822068717
    0x17060403020d0c0c170f0106060e06091207080604030f0e030604023d020f150c250516140108060619020c0a0902031605071703090f070f1401 62
    0x80d22003001103541010040801410300910040071034078001130090030318044003c0003e02d841921b440303901c0c503001100c6d4a0110700146c81030040e084d030640048010442860003144034100036003101071880750010ba100d480000309082008102e440d01881c000d841b010181c0550103001000501c215458601a0f0800780c18000180c588030303641c420070b2254809103030004010102a02d6134030b40c0081f00c01003202c0d03040340c00c0344c2658000c200040b42d91055401e0311000d0403e442c0b071130b541c198240c42002e481d03101000340340301e8019a0f03680000c030380d080c070241c240042041392100c81ca4184a010360410303000940c1c0003000303d400070b07504c0c41e038440e075007824124a0340c50410001481c40c000d1805100d507981500703403515101c510a00a001140703d00500c0444003d07142c0c0d0180001b07400c11101007403002d035071400110030140604155043c01d0303440001460b4041d003032101c07104a900302510080c00380c402c1c42a2800c140f6802c2c01a24090800e0340b20420030701340361004040d0200000c6511350b041c899030498 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 822071196 1250 822069946 822069953
    0x41e020906090a0f060e09100e032a01020403062702153a0b090417071a1306111305240c03030601080c0a02191416170604 54
    0xc40c5074003801c202c5191815a0354640c1403400380c400c0d0040c1c80ca0350382c42d0000110b8904565803140d4040d4012a0031a0410511341d251b1070120350704400c083c0301c44c1d40103201c4012044c00348420258400302040990011502d081d00080c2a6005074004490325900c4015044208a0990300010886402d540300d48480440780c002c1290a604103c07038400f06900010038002081140885c60184410082044403441480e04a28150305000101058403400c000c803003011843d01c0740741c0074082d41d00404612003e01d107201c0c503c4440c2e488981c4c1182d0f01000d44640010101c2c1d0074081a200e0305102c450101100140d10384001283c442044c62890740b80d0501544441c1c450400300c09055034400d6400400104030600842213001d40d040909103180f000061480b5081004400f031800340c9802e880c1d103c0781da01e41404042103800b409040e4001030b400641d521404000d44c0815039080342c00358115044400b030000d82141010854040760700d40709429441000801908118206242c103a00090129402e00360f6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 822072446 1250 822071196 822071209
    0x11a010f111e0303090f071a0a031b02010b0f06160602090f0409030906080f0106052203050f030403050c0f060306090406020918010321020c120a0602070b041e02 71
    0x141403904011a0300702007030000c0c2040216454031198030003482c1c00d103010551815a0396108541001c2c1d0f5001c4d060008410000005800c41560480c08401d8080503c0780707806100c0d03030072a000107000c160b15080f43c41c0e0303295980355002c3c1d810000c641c00030941c4800c4ca41031040c4601002282c501070b031020441040f240215841080c0e03c568000c00160350380c03400c2c0b00010001c00d1807038807141e409440d010782281050f8114110000321805915020324994880d0140703407407040e09100c2c09002c00d000b00038400640031000140c8588010446520604540383d442700c604c0e00401d02180c07242039000280920901030704000c540c201b40d40494560700c0c12415400482c8041c00042e0006014030100400305041101640680704440782c007418410980c4007041c880c0340c41800170b2000b65001140070700315072082d141d5040b4284007541c80e900240380c0d40d55102c007030280b200c411042c00500703030061490a400060707842c0028440580030f00c40036505800c090600c81c1c64890000d800e8002400407200403001601c48030b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 822073696 1250 822072446 822072467
    0xc09190f17160e0a0e0c100c111e10030b010509010f0c050d180b030c09010810030b100f05010507050c091f0b0405120d02060109180515010905090c0d02100302120117011a01 76
    0x34900b004944000c1e1501030840e01c1080c900980c0410340c003e80385c0c0c1d4036034a442c0070b1b2b0403102c085408900c0ba03821a1000d60807034802c120010b0000e0300800c2900110f50040340445001c0c5101d16100124480c56280e90703041003000040c0303c000500e508005110103070443c451401800c04c1001c214031354200b0500c00c001d54410f2490702c038140f0003d1400152803401290380c500045820400050340c91070100c14400e00c00e03446000f00d0301c3c95030381810003007000e51281056278015540a0014111004603038104800e8881c0101529180795040c1e0061006401c04000300006242d96100c00303840e24107203000c00981380d0903902403031078a500000182c444c0d91b50005800d4110b40101d0320002e0f620b08280c200403403048080502034044d2003003a00c1282c02e02ca2010086040346c2c400d090030001501c5241c14640c807038aa54452581c0211500307815005807030602d114802ca440941001483c4c400c40031b00c0e425108400364401140345644000e211504c00080c002d000303d0404101d002e0b00d10061800000c1e207003c109 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 822074946 1250 822073696 822073729
    0x6010f02010c021e07240801150c020f0319140606010503060904080a0507020d0b0a051803090f210f0f0a15150302090c09190f17160e0a0e0c 62
    0x1404200201402440900701030b190006e8009181107280d000da8649419121401c000140d210000144400010441d6070b0903030a00d907186981c0c5071140d02004003480300341e1425075050044c201180914507000c1e00c01c0852903c50b0403e0361201d1a01015203003042001022241804002c200300000e41c0c1c4c0d02c140142d4090340c002001d90300e60480490454650180c03001c02904052100500340034801c01212092050034030540500080d91144c209800048080310944c2a6604c188020701d070b94903010701c00489821010b032005801c2e030010164040070031038446c40601250071817420008428801e2002d1144919a60020030347c55070035503508020404044008200560380745140d00008a00780c5503100219002030200001e410a15030080030303076002c0c0341c4251103807012400d0484000f000c1c01401044802d0000480d00c028600a1000301041200306040480d0150032909000c6005a41400b8041c01e121202c3c507010f454054044002c90301141d0302e05d4201e5001203019180b40d41c4440050405120 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 822076196 1250 822074946 822074983
    0xa0f12060816030618120e270915100608060117040b0a1529040305010207110f0103021e090d0b18010c0f05040b0f2106010f02010c02 59
    0x16200454401003031a41c000120a0240184020300c510349080c0c06420780b80511010030454801440f15071044003900320081c49052440301c000d0540d801340d004044503010150450000c100024090242400b00c00e440101b640740ca482480500307502004058850300500d107607121700d82801100b514500d400c42c42003c040000c3d0400060003030340701e4103a17049142c40307000b12266903003818a000042403004a42c1c602d00b03503240c4500d003400c140400707500e64103c4807441c507070360803c90301c050868100d03200b1103c164010312420000000020424401800401c3c0a04071901520340100108800504030041590400d070042c02100e1100c07410070754642548114020340782e61a0656004190301108440c40500b610321403200700321100d002540740c4410041000020003020907001810b46214941c45040d8002a0040c0030074043d219100004243c166001d00000d4181080f06038480e1400811142030800403030280306002d09541c01507195a403c45050000380425010740300300a590700e40d200982101c0c040d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 822077446 1250 822076196 822076217
    0x16030803062209051507050708030a0e211c140601201009110105120714070b07020a0318050312030c0c06100e0106140d091a13060609020a0f 62
    0x10340120a0041c4080400028803d1a030a41030031030b158404120000c4640340890001783c0018442c038112071545070321400440c150349641040c1c40041c400502000f4261258240f050380500399040d40e0340e151a41240b41d150b80380080b0182c0356014142c400700e070031818281400742607220001101c90358040b00c01e1810701500754102c02c1d80c04401c2046060303407450340102d9201c4511485541c00952141d030160030b1900034410f64000442e4144200d0b030529111500490110b802240715666405080582c184101e050940c41e4461445954044d81c2e01400342e4813181c941070406410440d9581100e6a0b01405e203410b0703140001094954801f0206420000400000078007000081c50940c2c0105441c1012204146070060085003500d4003801001d01703101345200000b4106108944061080808510690402d000c01d42c4580c00f60990356400c8440d484000d40045403458541c0f0701900c41c00400784690140c041e181002c0045a078680c00000c6070f0360041200821b190340115030306000c0f414510b000c0d4850b2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 822078696 1250 822077446 822077479
    0x1f15030b06030115050304051f020c0f12120c07060609020319060501050d020703030e0105090f100207051504020105070b1504060b0930060a0203070915090b0a0921051603080306 78
    0x900d4642d106140d00e0326126114001102740e170140940d07004800498540d6010070f4a400c1e950318400711485402c0204001065502e65181c2e0020380002d11602c81506150895a4681c00e5405c2c9070440105550301004012803120b803500e0082d80006a810304024103803c21000900d68481c507410718101c0754001540f0001c041c440d0380a042c41c00c10f070070000c12080c20300782c40158642d00740d5141350a0b58401c15820700c1351050f441c822103240c1d90740a8002d241030b03004201c0c14188800d00900603410302005200d14400b040d1640601486844854800d40315281c0640400084414a80080380c190006000707020b2242c82e80c160140c036a1040040300c0d08120403080d25000800c031060f4400e403240c02004184000441030750080d502614054445c2c0080315110740c00004010120079000c0005401841c0810401c2c000b0001840010391904d0081042070b2251900038401107d241ca078105900034121086c1400800d0055001040040c1c06100c641491600c0d529900e01000d4101e611460103510a43c40c40d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 822079946 1250 822078696 822078703
    0x6020c0c0604030501140718090b0105091f180315020d0204050319020f0f0d02040c120c0503010e1b0406050c1c111e151f15030b0603011505030405 65
    0x111540200600d41d182e449213130190282190300030080c9102d4045020462441c058010b0395100d20754400151041490458440b000d0640c8003140e40c144142080503801640340e440107101c40d500d0116168440c0c8040d401c0c024013000750b1200b10440741032012000d05c00034031120807814805c000d8503009a02c555030310908030024462540015814800c05002c89450408c0f141003c1e4454001c480904142106905000300c201d0201c070025449881c214006006103402e5000e04c081d14a80d1a0404961213416445000c40c7c0494107440301040d00400100280e00e111550700381c1c001c000410904401c04408003448050040d8042c00007401008141481c0d14542006000903042800003984c510300c1c1484805480100e07120140c80140c001c040d462121042866564070850542d00010000c1e82030701000a030181d40c02903e40c90108c00b04075800065616100300030000f4048109040b01c007a585014058207d0300222140d0f801130b002400100031080c01d40000346030302480360803c0d0365255030342d29205e0708 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 822081196 1250 822079946 822079963
    0x10e060d11060d15090e1513060908040825080604021c0503031006030e010603020303030a1805010e0f0706210509150c0d0b011b022e0c200d06020c 65
    0x480313858002d00b8a680c94884103540121101000c003080a20000765904d51107000d20f1615149181c2c003000420b082c0342d0311400214030395018030b1b4000740c098426901d0b07810503070080c1d101f00800da02031140310342c0b90791001c548602c80d030500102141c0801c0c070305411592203d0004002174800e49401c006c510f44e10395100d0750070031324550110a9a0382da28098070300ea000320161f402000300207464503031100c030620341c14814402540e40040c011811513446204407805000d2080c0f08200c43d540114076400003490234010803c50306417110203000032581d0703101414905103a80d800181000f4800b42d10166081408810341c9481c080500041112794800000c2850050032403a0582d40561020400c001c00e0280c0000d0409403103203c0c02801540141c000440d41d40e00c2450300c0da818800314444020052424541040f110303490f88071180005c01180c00d4600b909288982d6031008030700c5804041013040441801a0100b9030f000000780c0c0e5039208580401d58028060384002c003000c0e07000031900f0304d60604014031003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 822082446 1250 822081196 822081217
    0x70c140105070f2003060f0c130518040209060d12121d070305060a0b03030409020705190f060b010302040303080708060a05030a03030e160b1213020a080c09010e060d1106 75
    0xb0014090b5140035500d8012100701d80013030360740345010084240b5012541500070505846500e0883d2580d04079184c2c19413018100c112403244c941000a06601c0b07104e031164102c000100e5800541c40c0c9401800004e48000340607620a01181e203030403000036092000071081019500d400b8440001921100f0020800c050007104840302c4101d2fa2940300f0000035040069a214100f5642c06e07846010900041e00c0c074186105900d030b00244003d01c6905d0b05503020b0700302c140c0100e04840990070040140074686451000503581c1041140e028028003420340035406d60340e0000e113021868503141d40c400401450f1b02074880300811460340042212692021542c101500d0004c00b500c0d51307003d0500e00900248861511844580a00c070810302c9051b4003580d500088418000c0036a240500840441c003074414020036403000718000c03803a640c000d611102e48010182066000030000d0240c05020003074000301c140e002d10040e001810070424580c98591b007054507194404040004900305000040247c0038411055 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 822083696 1250 822082446 822082463
    0x504170109060b06030717062803050705031906021b030d0f05060a03052d240907060e150c010207050325231006060504080c06070c14010507 62
    0x266111a010341c40500c00c28442e2104121a01079981404100d0008885460100340060140d14500d01200d240da43e0040c00144580f400800002d5140400808420090b10361100d0702014410031004225080c00307000d0480041c00b00900344203107101d81d0443d0323070b600034606a008600b42260703400340414100c8500a41058a86922101c48964010035808a400f445613090901183c0c0c40d040040c0030702c00b92500640035200ba882d40502005215a90b081410b1081c1c510b4204902c0c90403090052030305020126240010700c1999916124107400e01403c1e5003000e42000c1401c01401d40c00480b00c1078403200541c2d400e4203200c400416500c1500407a030b200382655000060710010840040010503210111190288400c5003e1310445c01100c0100c400600070036004004400384105502030b00c0f00c4440e01c0f011290000ca42000e04810707034015500c400042540400c0a200150080c00380082403a0f080d5030312801e259a5480714000e590312407099a44103550700150609a0b44214111054a500003400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 822084946 1250 822083696 822083729
    0x1312051c0f030f09150518061f060338150c0d0809060a020313140607030608030703050418020405060417072c090c030f0f101503120504 60
    0xa0500070081800c01c00280c600001500c80b81001e12403001d8040d004140b1600c3e0924003a400c01c003c040c041c00000b21240c400707504000307050041003110310400c0301c400007001c030b445036008501011030950000da06040c1003803030b110b90860494286240c403c00c0780c0e58803c40300440100c01d14003822651001c5170008261940c0b81d0070b00c03103c0001002458614021100e081d103007600100c50009003a02c41d00e11941029011883c840c3c0ca03500510740101c20703004001d115150035620301c49000c48600540e0416040001004141a01807044000618405c0051807605400d50740081a5100300d0040d4031580d0b204543c0030010301a07980c10356003d40005010a80c0c0d682d02ca03205480320720310300c4a85c241c1500c03c2030008200f40e041c5042c0480c54044e070150b210502900c01da6400281c000080862009220350b110801d11030f5410400341481070568409005c0380084040140d08100d040d44407101e015051075002200404104405821a60021706441c000701400908886511995005040c0f1a0000c1d65 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 822086196 1250 822084946 822085003
    0x114040b0406051309142d040f030f0206010609061107050a23010f120506031c0c11030d09061209021003140711060a0e12070521131205 60
    0x1415084c1c121300795500125130300c80c11103050301c201c41580c0c21151424404540035601d168500c40071540000c49840b648040a00c100d04202021102620380c80c0b61070004006140c1c2215070108041c0045c805002558105a8098000c0d041e0344907040400c4642c4c0b5001c0300b114000d021480190400600404000356030328511100702c68001084800400c801d100c00aaa40c042c0351a209440410340360a64000d80303c6044e0401044000c14594050150380950004501e010210501903103581d00c580f14181d4680c02c01542c5005000c107030500a90001a2891240d50400035040880350280b40007040107a80c205124007622801c00020b402c2400c1c00e421001107a0560440c82c9040d1040c40452200c0d62049000c55000d0110441071540d50449800f2404c0c216441d0030250525107000b08451101104643ca85902c0c2d2021005491036000030743d8442170854981c0000346800c622440705410400388900207424101588540c0aa080040c2404400c1060600c0034016003400344100a410122480 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 822087446 1250 822086196 822086207
    0x5150d0c081915091a040504060608010606031e09140321160e10020102070c0b0a14030403270909140d05040810020702010c050307060b0405130b060114040b0406 71
    0x2140103008150707002d074640110115100780404800040141094545080101c4004040304045a1810800c00941c0743c0c06803554000c2c640118412940041d00030b207420003890840d000751b0080da04250030244124185800c2d129081c0d0488480740b400141c0c04a24a009002d1032040c0c100c00702540004205412071050001a102989004c0160246181d441c1420340c4a40822880c08001007401d00c4003e45040c00c01c0d4200c1203550125000041c5000115100c4219200031588000c0e21804001500b041b0154814a903400041e076840f03009086040540d0058600d01a17140c40400301051004109101c400c0501c0c0400102101c40040050b005c9604201039580c070482c0c12118a4031890a1016265100300104c03011500040d000d04401c02107e04c00c82e0107548031800076030420260026141c0070580a000400c9854031075038001030540100418002a2040200b01d0111000300d04003000109124a100942c01102482c14020441003510088001d00858201401c0c00c60701240100e03041d078000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 822088696 1250 822087446 822087451
    0x31005030714040606080f13170c0313150c0809040f0c0302030a0b090108031b0c0424060305063321100609170a02060a0914030a080405150d0c08 64
    0x3e503020300c006500e0b50b07810381c1e481c5d4054401b504a80f0103580060520040030f944649414841c0c81410031007000140441c006800c03000300700d8659000051100703c0020230009000040c0400c02c000000c03d5281c2c9405402e44170060340107001c481c400940407860b80e855912075070003424100001c06c000c10703054000500035002240e10501a81c41c2988500c02454003206213070480e40100001c6140c980940c02200c80e10710f40e80000800e910030854184000d940300e0141c03056441030301c14008078654254101070b5041220b03034040010b1600e42030a008060b125130401604407510b280901e00482172042ca600040c250280d10700840303040c0800c4084902403a00b268515006042c19107010544440c21540c4412549204e107802040000804001181400091686030400003098034403c076a2900812215407110f001040001d0600c001400410071a03607007020071000a07802400040700b90754410703c0511960140300e2280901017003407100b26a8410495410705640701d02409000d500741e0014081000030b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 822089946 1250 822088696 822088699
    0xd03031415041419020c0c060403050f100c0512091f021b06060f04050c0f040303090f0602150a051b070809030d0f0e10050705012a05040515031005030714 68
    0x3c00700000e255500d0040b21502556203c111145a80c42c01c5016000070740c030405c1c01c1015402003406070030a81c0c1c0c5410181005500603400b41c03880d5004408224281504040240041031800b18030722440ca0303212003680d048505514407001ba40e00d80c401e030079107803c521742241c1c41078440c4904440442c944c5900608040c020102d0041c228680500c0101d417600301c21511281c004844e4402c00c40c032450150015908801d0b0b003280e403440d09502c42c0d030840559102e074106034045503a58004102400101102e10700030000b45c809440102d00510725013220b03034405407201c007100d40c54502050f10703c091880e1a80c40c0b60885800390341e85002a152003422608248541c1e846402a88483d000340c03070250007406400307074a655482c12205104070401154882504001f01040401d00001c00010000d01c01c0f4041036100e44200141c0707c2c80000000220024012401c0c200b003c203000403c020748808003c01104c2c0d044c209480c0d180c0d40c030018003c03400040c03540501d505114407100000c11880c1d1b04488040c0040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 822091196 1250 822089946 822089951
    0x506031015050715050402042315010e1e0f03010e010608100b090a09050102250b012405160f0308070908060115030914120c0f0c0a03020d0303141504 66
    0x42081050b40c0794050503401a061130644900c280310954603a00c1194450300c000c0001550001080000c0c2c64440c00703045070100050000e06000501c0e80c444c0141e8090002440d062401031182000319608560700750b03440c0300c655948203116240c2d0b030305d91180f2001c00401900801041082000a40c06010a4030031280180181004108003d400c2e02480c0741307044000d07040d1140c03a01c1d04180c0c1c50040c0030320b14040c0c40c0e5550910020720b480c0d20000e48906c0111031181025600407440c10800b81010041c0d0107640c545144070404002480f0201c44400342c0205410844d440354402d400208482d800500010619400358016400b0941c2040c010303805000307156a0030380c2003519100b00c903a46810a0060415000d448030400c0070562081c1c00c2040303444c0c814120011801c4501071a01e1a0900e003546c44522014045100729050204204c4d03c0f00300700f8044000d040003803e00780030a5006609003c082d00891481704040c041c940a03401c00c0c1c2c0c0580010360311000f10f01d4184548000d020410380b1941c403a60 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 822092446 1250 822091196 822091229
    0x80a03091109131e0f02011206031a0f0708070806011107030b040b0906090a0201090323010c02010c0f0206160807020a080a051e030403080601080612030423010807081f05060310 78
    0x41072640740341c1840d8000c0061703580c852950019601820207461074540103407606000b000040608a03400014031400e0030225807800c01c0c101500b01000024400c0c003c100507101008103c6610906080d0442021700b07056003160707406501c09080544940010b8200240e001c10300c0100451882941e10450400d4142c1e112912000d2486d5100d02040c64003034001805a80f0500208020b003403403003d0000c01c443c7d0401c1b0382e52170b03020300e600b0740c2d107031410b4040980d43d40c05008030601d821011900281c1c00c14409040203140003019103004e10300d410080d4041000031000901c1950003046060841c6800c0b003c079603261440044000d040d940302c0c5c024080e61080c0a040d0240d00005001076900540c0c2c180c503182081d40c0c1c3c2c00d004441d0000000c0100340d02000000b04420503140c140000d001400c04040009002d400444041c1008410006114100303d84103080002c090342c41500607402003014040500380c0740001041d50a40c18039a041554899400020700450341c0d9030105450854010401c01c08030350 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 822093696 1250 822092446 822092483
    0x2090d08041502160b03070302090d1505130804030f110a030b010303020c010512070804020f1c022107180b0406080a06110406050405040f060e010b03180604080a0309110913 76
    0xc000121081811113544681449841c0e0500080c40e40441e50740b40050030030200c0b6000070803040790380d501a00c040b00400c0861211603182d000721540104240040054078150350380b50b43d500d10441c80050400c503031010302c0c00100840c8071110010318a00801848a01e904c0303080010b403000080c802240507205560b070a018950160043c0c484024840104501c13983d0303942029141c400b8014070803030780002400c4107401d03503036105440110f02040c500c2642048480030310600c0940d410011000041c1e1408c0080402d000c14005044002d0340c91000e02100c14401c028030391805825480aa2548142402004180d520b000039840059038080c0500b0700211410001c841e606200383c0c09020b0000e0030400c0300b40300ea030a164010500e03030b4003a9003001594650301d02c4ca0100554003030b001000d181c9000000d2142c036412600c1403520541034400540a42d0030143d890440c54030a554801092544601c82d08040c040e5803414002c2c2c091024100189600c0c3c0a90b03500501c4608820845400410304aa000d18 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 822094946 1250 822093696 822093703
    0x30109020604050d14010f060905060a030506011809050312040510201605030f070312020405060a0327060e010c0201051506071704031110080709031502090d08041502 73
    0x10560040c003007a2401d810724007032161248158900f51245070586070890842c88092060603030001c0044800162203091682000a488020b40554400c85182d5401d03c0071070070100d166811501c0d203000000340c02c0c0069851074060586440050074501005c42d89601400318894842c0c03156100d0015100d403181e00540003000c41d14041c1c007040100000c140c042440c80105030041a00225002d5485030f100b0007031f92054515032205016500c0290003007030740410150040304142540c906100150b00740b40c2000003042260041c001440b08250320740d80b01403070032610341210b00d8400c10010101115464241018006440340c80c1d00d01500350718045c2c20741c0c403151061040c03e0003418241c0b14125441c4524003000419001450f046c0c80209885190170030b000c2e2284004c20040d80300e6895480c80d64441c508010017044c00c0c100c00014455400d0801205a603c9950001075a502c04a95015030002c804800020300070100c03415040320303040ea25102440800006441248c1508d02d00740c445603121802240c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 822096196 1250 822094946 822094961
    0xf06152101061e050a1b05240702030d020f0c01050a06061b030e0603070e09040b1b09220222030606050a1d250c03030c03021603030b030114010e010f050301 69
    0x403d070b0b00c10041c4100c1140300c1d0008241c3e105451038410407040c41c800e441034048001c85001c03034540d442010302c0740c81001503807100c040848107000320041c1441e2004020f034484c401d006100c1a45c550004040d0303403442e0800151942e02a40500803c95072400d440944c0c01001907001c0d440224005c02c200840b03424850380304c080d125a040e1340c0c802001000d03109200d503d800140c20701d800e01802140503030a030784419000c944158001c4415058500b08404409070980c4140c5112229080410444074244c44000844072188402c05a120441d145000144000e0007030380017440161040c9092501a40d8a0b07002c400e05490060104100080c0c6d41d808001c002003a500c50b000f201e90390903480804902e00c03900b480b130303000030181c00121302088148232740030300903400b40b2066012408180041080c598944169000310b860b1342011454510b1b4050080044900c03604000c040540f00d01841500e91801e4104800d401240515455035585410020030341d0502401600103103426000c0c0042d641c5414041d290 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 822097446 1250 822096196 822096227
    0x70c21170c160b04020402040506070323160305091809011d0c090f0a1e0914070e0604091109090d0f02070b1206040212102c0f0615210106 61
    0xc0202d0540d564421006200810990f40a0740c2488009025260131000f04550340c8030342d40b24102081881a1018501c803428102d0081100c2403019220744654501642102c60301400c150352150480c00000e00d420754100e40c003048a810300b40510013a10301c150022040c180040542e6a0740c03c44010442c0d41c0d03000b42a60780c690180820010030040801000b1280d000b02c0090f00104a0089640b060071007000d4034080d000440c2d540d402070400303201503240342100d0b4401e000081c103d51890003807203402b50314001e040c843c4202c0d610340424041010a001d00c184c3c580e00602029818071703108142c203465100300380c203039404903441800c40c044091010400c4801c0e111a2800c00c3d0401100ca540e55041788001030495800075400c0000390100908140341d144503a5403c0b4400080c2c1d410000d5074a28400303040102d011061a044c41001080c40c07420340507601c8881010741c944d9541c0d903240040c0b0481c4c00310b14184051180020415828500c1c0c10512880d04400e00598005999902c000c490304103010f007222 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 822098696 1250 822097446 822097477
    0x1e0708120c0c01050702030f01060e370e0c0306271903030b01030e060a0f0c1403060607020114030a150f08031204111207080c04090b070c21170c 64
    0x400b40f503024401410a07240054115014491182401421108207400ca45c0c110b0f54410100706000c21459800741c4001c410741040001e241c044181d0b42d8100c1c90f00f842010300b41d9141d00b1006c200f48000c000e080d1111000330103e40321030030010300d928101c2d072896001202d402c110580101d85a0707000101e030100c408842044403070003409520100c008002c0d00b2506410151038002d107090401c000c08c541d42c000c007411000010740c0c0750107285400407a01c0c50403d50f414440610707001084c1c91072030810784c1e5206105035100340c0c1d0b9076058801258116452042c0000360540031040c005080b42c180d01400800640603900502c45443c1e41c082c0190074818400c211256100704000000b0b90400d00c0181e8203e0311941a070b42d40b00d1600800176242e40052036040c0d0056001c1e0404105134002004400d1640900361000c000ba1249500ca074041588010400c4c1e05010502003c1020001074140072405080107115151942075401402032040000c81c0c00c0542d1400302c040440d05981440040382d0480c1a40c03032a6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 822099946 1250 822098696 822098713
    0x1f030f17160b100b04091a0109050a090e0703050303040b0f1311010c060e01020a020102090a0914010b03040507080d050307020105060a0b03191b0807090b07231e0708120c 75
    0x8184000c10003c000c5002011061000104030b06810042c00192502c2c0201107140107203a201029242c1c41e403a0300d10704104600000308190f40300c032207603002a9210a5804610400c01c0c650403403400103554401429440300108000038401c411881c1030084942c2881e2060701d448198440782481d0b040000a010300c14580200602980108100c00a80d4030070b1601003210164a02c1da5030882c4c001d2040c0001607500010074895901e0300c91800000b5081c1c0303100800c120030b034082c24100480c105003e041c0c9242c5000021a0a11908100b0800208440011100b254210300b500078881c1d0400d803032010141d0308090118409107800000201600c84c03245140b415645d0300c1d140d4001c1100c0e0411040c003003556411210003142c540060303150130683d00c5d03100c20b002803c00e0500100700c0c1c00360b03500c40701c0546c8047c0400400680078070709881c90600720722590018900600000c60905440c4001c030070b11f4001c0c001020081e10008110321040306c240314155016140c92440c1c0381c50b03030b210b104440c841d190494a003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 822101196 1250 822099946 822099953
    0x30a050309010b0a17010c1110110c0d03090c06050702090f0a0e150106022509150b130501081810090804030f240908121f030f1716 58
    0x51a40000c0d41c00010805000365400f00c0c00428507500304920044400e0170380d40890a0900032094803600601e003965100305039071071840e180c040407850280140d0300e03020760950622840040d544d14030160300c16a83e03c0940c00740080c004080043c01115082801d003000145580504150703110560007904140c801e542d54030401d14140002840040100d60300d090781845804c0412a40392800c0381d0950081c9503505100c1c0c064a80007210344013a29140c00484c4a414502d40310805000704c5140e60004614200340d460300003000e45081c0c1100d50303502c0c03010504030030300851252160220340f000e8950011039245c4165004010442c0158910168088104101c82820755817014000d03d0044591900b001e03141d40d03c1c19074244403e003042e10040c8507084d058201d070702407255448005480100820480101d9660382c01140104054044070340940b800041d000c0200e41c0400c0070060a020900750320b070303449103062854403002d080162192122031440300880d48648045480c0f0848465030f00c09205195039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 822102446 1250 822101196 822101207
    0x402010206181c0210050114150f0d020708070c09050c04050d0c0915030c150914040f020f1c02040b0910020a02040911091006090612020909070305070908030c030a 72
    0x50302c07031025201c1c008084041a201c40342c4000c00c4007a9601500060f140031402909a61040c0c10508140ca00e5004451031036a40600051500800307401054480026044003451030240c0285061064000220101080030300c2000300112807041e4406442c440d01e588480d4103c2d04201c40060403003904100520051a040d2640c0030407610500d01c20b1056074a9015001c1950a034082c2c83c4c20800b0061000c0c4100603540c400c00b07002c2e2040740c56085401064480c020611001c43c0301c0c0310562509100c00107040d48841d00241d184101403501903584245052064201d94024001740340d034042624406208014217000700c504175101c0002d0241440640e1042200488111410b9025442110201001a200c0340107800e40c4600410950249100b00000d1110806004003503506500c06c4c08418000d03550020038580a4503070034500394440345044403405009100700200d031a4020021410403c4165050700420721a83d142d070f541c61440c503620050a5524000c5d01e80b0240c8a410500c45452410310a4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 822103696 1250 822102446 822102481
    0x80a051b09220c080108190f0803092103011805010f03030f200114010605071a06011404080d0906050408071224050906070f02070e07030615030203040512030402010206 74
    0x39060200d100c110189540200e0310041e00301e00104d0f0002004010300e420500c0401d41d94400101007a10300369855172400d1000c641e09900a00035440400441d00384202041004403184801c008000341100c01058803181e034101f4401c05000d11080c4178000310f41c96003030054038125503c105a019540b0705554080d41c00e141c800ca10710702080041062040c00d81c00201150940210020000801c48c9600c0c4000540100581050003482030401101d0005101840c03002c22001c140910003c0c2d50712000c0040340d0348103d844100079a13810108010864240210300040300c1c4c2d007262030329000c0395560901590107018911460506412214041241e040c00f01400f03501d03244646070f80c1c943d9590164802440c01c0300031441d4401c5a0751101040804d0008109640c2c2000480c10441400071026400940d9600540154011082e03004007050740d0038020307000080641141710f103400500c6c1c00d910005000f504103c07003ea170f483c440c00598042c03081400e41100d001d40c1d01a40a00142d540380c004081010690 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 822104946 1250 822103696 822103729
    0x50610080703151b1d0f300d080f01060c08271201090c0609050d030c0203010f0603050607021011091002120f04030b0c03010b0a0809070302040c080a051b09 69
    0x11000c401c0e00350039842003000b0050103141c03035008034005c003000009001350484908a000d00d07003010b041c0565aa454070320a072480c0c403082c00c5900c01c0c120110149000040703c070b40200ba520901040482407504130405034483c42800004019983e40c4110494842502da103007d03060f58020080320f4201c503d00b403039083d42030036001158202a580c2c2c001040c0082100c082045490755180d054100f00b00d5555410002421030349810403403141040c00080d80d14840800060604c807001c1021411521300390084103070030309452002c02c00150307a410020340b80c0c54100c0307a82006004c0d0000951035010706128000500d003842c44082e040141c0c1c0303400cdc001c0309150450090254420340e084002c5c03030040b40c0b0040901c1480c045003e40c5030362030340c541130318180009019204110011b0006000000480055428041440c90010300c2610750880f034a04003006604040c0d00b10742480304607100300390031000d46400380c08014000c124560300c64404141d11030010580c030010080402c9072910307901d460b5983c401085131 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 822106196 1250 822104946 822104951
    0x1e0f06011421010608070e0f010e0621010b040f09020f0322020d0516170c010c150c0816021507142101080c0a0b0306130b040c020a05061008070315 65
    0x202c2607050344010509a0103000040c0c1d4032800c02c03000c103900040109599405480b0181442102c0c000a410070603800141e030b00407140462000d00790001d2400c02c01ca184224580300d01256100c1001d40f4044e800fa01400504102d00503000820360494801c45210003000355050317046460b010300d500802104039205400f014151000341025981d000c14048005100744002c0c6120303048508810b1103180640d10035200c246c100511101d400a0100d100304500009117041c2290f815186002110040c050300c0903c07580b4500541d4900c101d411040f001d00404800e4030440c0c400d6100c80c800c070395502c2c4200d10132a0f084041400f0484081c001d09452580c041d1ba1450581400c0003c2000c46c00404d6840c605100310544500411034000103008090035850266031116041c2e050145d0102030340700140c20315010300100c0040b400d12000d9548000d801c280e0040c024042c1c64804400291b403420622420388142c002e80e004a40c00700c0740f1006070822102950702400d00f00d850740e15a08004c040011070b1111068 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 822107446 1250 822106196 822106237
    0x1a040605040e2706040615180e0a0807030801050901090603150c05271017011503061802090f060406090302040504050114040b090d02010204122006031e0f060114 71
    0x8a40f2103140e101e001000d0051803113103041d041c84415541c2440ca00c1c0340805940605100302c0c80d444980682c0301210010100d07071017213000f562625107008180040d203160b030042401020584d100041c0307412940100c0312800b041e40c90310400320890f241488000d0509020004d400c011503140d03040418660341c541011418070742e007907230080c0840c640d986040746030184641d000800d901d001051175030280352030b00d00030307003400c0d0300b0021904221818028190010841d08500c400603104e038101c00d0140c280580031418904080340d1203006900152951407003014041407a02503400c0a8041c0c2d41218260b0350340d4200180b543c2c091100030100a041a90155207910408244044802426019520580300f4a003145000b811041c01c120700310844d8800c42e40100800c00240b4880c0318441c10250f00560258900d90072a242032021414281000d038003d40c02000b0880c0c02c41408024004540210341c1c40102c3e40e80d2440012079400d404c80b5054049002500903001090314000a03240a4032111211103090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 822108696 1250 822107446 822107491
    0x60b040b1003090303200a1115010303080408040b040906080c03010c0f0f030204120311120a090510110d08010f0b210606160f03120510030201050c011d03041a040605040e 75
    0x342c0b100041d002c10704400030300c400b1f503617502c85280043c01440780080c000c1840c00240f0065203449c10302c80602004a03001c081401d001c211000c43c0c00400c038400c0b07003540d2035584c0e03141e000140040c0c0c401e680c01405082e0707001e1076a003811301540610860694441402107020601500c1c9800581090010143d0038070010490301003c54074001c0c41030007034403104803030010201c086203816040040c0b01036070307102800415261900005000c09951046400c00c030f0b031100c8000b0031078402d0141d004280c6584522204044142c1d000171100d4142c0b4809400644c041c1d890300c0c520350f100d01c1504910a00381190070198492020b1540c0401d03000309009042c1442e1558460440156820450013a40d00c1d22441d0044020941c1140000c811001c1c046007c1c0414a000c544072402c0c080a88406414040e00040c1c4401140007940001e2144c12140d10700b402d840d00004050355030381c1243c0120380001254003240035405403244261400c80320b0b183d4603503117014140044503c60107030141020300c9030440f900414500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 822109946 1250 822108696 822108731
    0x18030602070605040221060121050312091c080a0203070504080d021605041802040f0209041103160e0a0605090607060507050705070e13020111190f060b040b1003090303 74
    0x1054042c0300d002c2058142401000803165021141301c0080f04209508600042c000c501e01d811a0041080c2d100742e158011919001d01c0d0b00450000c1c5280000121155112141d0517000d0040315254102c4110303055441105200e50780c16281400801c801c01d000442426840d0019135100000380f50180c14141d90301300e81c80c5000414141180507030420b459001030300e0300e00b0760f0b000000c0c11300300d90601c01302245405038028140d9880e0007030301483d2035841c040c050f1501601220302402000e4000c202c009a848072129090700700380c540c41c0390300811038440340c4294840d80c02c0b080c2d1000020001c0301105d20380382d003d0f60645e0000d00381070b80103a0103028050110b0b8041c0304452265005c1d4803210b640780c0f42c0f41b41c814203002203030304081e11001c541c1d020310541d80700300300c0d054a407640d080c2014105100c0301c22405161042d02140424052011501c1c803041188100c0c81500329849039005200c48900002040300352022000c0107a0089460a0490003151003038111281c2d840c041d0034005181d080d210a805407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 822111196 1250 822109946 822109957
    0x4170a080705030a0e0a0b121e0112020306060301090215070c09020406030522150e011401060e0915060a03091a0c130b07080d0b031504110108012418030602 69
    0x10b0507000403641e00c002e6908101c40c207109120458083e06180c1c00c10003070701d856006943e040c03c08401150001003400c4000c800103008808508039906083d0796500c595000c1660021040740a030248401054003030505000b1402c9442c0c4c01040d0072000902d102401c1800d4114040c16035244001040019600c00148001e20203440c0669011035246000c10032171003440c421045059468003001030020120300d4800303010440044807240440d080c3d003003013251405000484481c0c952218241c0000601c643c0000c9001540c52098502190940c0c1d8500c401503501411340707115412a6040152101040c400d5005d000030500c00c0749542d9408041c56a2260042c4c0700300d895091400000400d103a010892020000041c502c5000d00303450902c00d552520700074021200807aa440340c0394801604160740c14004001004400c602012103480c00b03080101404003282c0c00b0070f0105002c240080350384c54110341070900c0a00906120000c01e281844201c80740c00ac2400c5ca0586c0c065a501e002c80080c5c00c1380003c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 822112446 1250 822111196 822111203
    0x70c12030510060c050c06030a0908040b040303090e090a03080406020408060711011a1e0423040b0a02190e0a08030406030f180218130b091f02090604170a0807 70
    0x90341d49450006848030021540268040c40901014030000500014104001500984005840392552a03038140500408032008002640100313000c5188002c60001d00200c901a0381c0740041e15603560890306101c0340a41d407914161300000090b1001c04c3c000d401840d0080d02c1041d00603d040d640b8103186080c07050030703181d5400240000c0e0b813846032042c090280c41c40051f050340c010003001c01601c4c00160347e055490100d81010b50300582044140d84c80e42e01ca140a902d24207580c1c1c0703892844c1c2c0302481042c0021101150f40c4032240d800700340324024034801c1d03d0b43d440c1c48030700a00701182110415121800802401c42e0b22001141c4042001d02003800500014400307600c0200300c01c0d2001c8650001e8445411101c0d441240e00c000000c09a92499901d00f031a860600807451541c40742c111039880e100080b0720141ca181503550038404030140c0042d40a603154016140c4071003010302c9103070160983c460150802e6003c242840306102445804003140702180d0940c048070066881c035074900d40580c1051400340c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 822113696 1250 822112446 822112451
    0xc02090a140c0c0c0112091406250801050d0204110a020c180c09010810120804170604020105181c050c1002031315030b03150106020c0402040b04060305070c1203 71
    0x841c0503903407908100d9000b2a85960803401c2101c40e202490ba1603400101d00c1d4104022048214190079640e0700c80039441da01309201152409030500341954448017a292995005d2488441c0041660217031414200d01d203450352248460303440e14040280005440000781e81c42655034a0310000e1401d4a0001d140d582c0e440c1e000b820b1040c0090080182900c141004c2282c0510950f0070000c032800c800c005c545440109003008541c80d183d01c80351094130b0301a50484280c0c00c0d900c0440070103101c45a000341c001c035070800d0304103010094524101620744c1700554000b404203900b4081c10b241c00c3d054070081702c1c0d11080681a00843d099104da0304090a0a0308010340e42030700000c40782c03045820280c182c2408610a80019445e00103408404019800300e840b50a030b5010040d0f49880c40c4074403d40240038220801411a5082c11031111884000c12007032242c50094800c1820140035820705000b41ea08681603a900c86003410b00d040d10036000740c6002415101009100300d6038800240300440011034510a65500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 822114946 1250 822113696 822113711
    0x90b18190203160810140f060d03180605041a0a0903121b0803090c06031902031b0304030f030b03010605010905040e01060f03050f07060311070f1b0b0d0c050702030303040803070c02090a 82
    0x31812100c02e11000201b02d40c50a08011030210b00c428010b410800076640488010342e68102111100c248481c40907195140e4a40000c8480e4014050010350b1004100078080100241e98440c807442000004030120b0f0194200f040031480401c10f11071288500e0900c80001030400ca9646119101903008032501c8501100340884040104130b40c042c00d04082c1d036814990308100b00e04201c56000c0b0100786400320340010008180c2a0140001c0a0000300b440d21261681014900649400003d05092000924080204c0b01c14601400b035001103c01c1a110b80b810385090406000c040d041c01242c00f1419921950002800d01442031070b50000c5000e000500f2035401c94014842c14004943e02000805007000c2c449007140442c0307012100100c1d400203035202d41030741c00e20707000e412183d40c46c60385881000e40807000034200790f4000c002c5c0070741035456108104d05400c1ca201514240607a41c40650544e005000040005085000a54111200781001603504440f540041c1c200502103403081c00310350f2548003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 822116196 1250 822114946 822114973
    0x30d020a09090b010c230c1302070b0a050c0405091015020d030507080f181510091d030a120207080d09021e030c2704030201090b181902031608 63
    0xa48440f002e091902009600c140e840f5090101d07443c8080c41c2e1042c10307000c0c1b03400d400c0c84100004103190700050700300442c6614030081e10b0025080703100c042c1c0d1210742c1c0e0030001d030105509100d030030b200303484c50040941041d0505060003000380004040c99100d64050304089940054a1426080d40c5082d03401081c140e0700d159002015205c0c094040018004084140038038008a03480343d41e4041131025840110b0109042c485207000320806000442004090500c404041004114029208003007801d0080c415403c00c50f000346000c5404800d601c1d00240b1a4a250500c00e1400190b45842c2460140c103049664803120020340c00300080f2480a80d880c0d204d201181040315111907400700f00350004182a51040c0803949481104002c6071080c2100440c0d010f92841e0f5250041320459000cc1c100b00701d184c1454003031700030310250200341c8981003600c000460400c1100035500590304000003401d40207440d19041c2c01815a40d21080b03905004034500b001c644012242c80c04001e001d03d034000e0409100750203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 822117446 1250 822116196 822116201
    0x6030207050a0c0806160825020102130608100f030803040809031c0c060c02010b0102370503070218090d0f0c0f11011b1a07092c10031e05030d020a0909 67
    0x3903001b420310000a00700541d50a4103150001e800102c9400440305e4444400124021302c00e0301c0c4440710f4039a00d90700219040e94801c0d121442062818440280180c440d190106000c4051000412013070041000600040c003800181140a101a0849a0352000003400c62120700610303c0350720001d81606982014030040340229514144140020400d40001c880000d40380c8104802c3c2e45d01c10b009100c401c4481801c2c41e007841d8204442030300e04994000640ca0444c2e260b0f0b100305000c1e072003030381c20382c51708158070b80201d8045000d2104071006009140090409980c907840c40000c590a000c10010b016021415242490840520900c2020f0b8038540e9800090008074030840120101003078450310000196032010600f81070801c450070200c90b80c2d101801151690314640003101070403840030301c070200d04504890b24048040f0480070b0906550300d2505071175004d040343c8006410401048001300305801103c8d24640d0070387c000c0e0140c0b441d0900a2200000382d920050003400003400301c40f010030a070030051 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 822118696 1250 822117446 822117481
    0x21309140f04120305041110030207110a23010203041a0307111906111902060405010c050306060a0309110901060f0207080102070b070f0318200301060f06030207050a0c0806 76
    0x30a00201e05081e114200c0100f01400d40388203250fa2100481c0c148030304034062510b0703201d005180c0c6211050700300f00200a0f411145044503500c00b015103d00309441c120003118155042c400880d03c68600f810b5141401d1030001c017070355042d80420400805c406d810403a11031003110181184030754900307041d40000c00034400758400c03980640150700f2003021000c0d003036070440045811030b00124280e009401d0202d11446600285240c1e4140000a81041c41d004540c043c480c0380541d0080010b804000c8040d501407000f00e4403558495000c01007558940c3c040c1c0c4c0000f030024040c860511114503140042a9070740400e0700800c0104a03115a080201a81000003d0103080f13124025414003a05582e2280a40005031124003441003102400c02d480d4865400610000d01a2404203020b61060034512300e00e034152000c41c1591a80b0f003440303458500b414003c440c100d807040c0c603c550342507260070002ca0082d0000329007150a805250ba042c004034218040340000b500003c000b40c03402c1d0405c1202c4a440002c3c0703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 822119946 1250 822118696 822118711
    0x6020910030e030d021b03030702011d121e07140f0106080312070305070c0b0c0931020a0e0618010e10020606101218021002071a0d02130914 62
    0x1000342d0034681e1080481940c510400341c04000d6100e0000e292261120781c890428101e0921005c420031402603070540002c0351034181959821243c00c04101000d0700c82500c1110f4462003981085541941030030a024030141d00404440c00b400c00c4a40d0344c41180d20812200c1c010800d50000ca6165040304080c8691002005003500a626004002c0080820078000034014400c0c56910310014103010300410010754043d40c4010305103880d1802c02034464081c2c000718502030040845070010400c03002c02c002041d00145c040310481c200580c0c5940c0010280d8000f10000c020001c81504602094480c0380c05081c84404a050036840b0140c91400148500340302d10310981f01d4003c60701e800040c0c0360080b507502d030040300564054400400080b0191003600d604100d08447c07500d0704066245c6041c0740e100030303000036208840000070740c103840300c003282c1d50619070007101025001a022070701d0844c400ca008260710050964003606065000380b81141d0a0496408031950b01e8441059204003141550b029601058 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 822121196 1250 822119946 822119951
    0x109050f012307021002030d1109060d0c1404080718090f141912020607030515300607090e011a1c1a04050a020a0806100306050402070602091003 64
    0x500c5000280542d80324445003611000d21540314038040454000c070b8800341e401070905d030b200300c0500e8402540c9a114031500d0250701e10300283c848880d0b081400302d0b0b6030750300010009414201f035500540e00412002d1a40b6003402075480800c1c1e001d6041c440940000c0c910078002d094068031f4510b1004000b400070480240d51442c184054001402d8140640d02e0150400408086080d4000e825441c000c41e103100c40360041159004241044032400391549031049581c01d0300d22a8982d450107900b40c0c2d5055800700940c0614507807440c07960620503c2c2240c480039214080c8120201d0700c111054170484480320b02140c0d0085000c00c00c1a0707400c01c921b81d004052401e40d40000758940382d000c1c80d9a0340c54122004c100c00c000125883c0d00600c4101040018007070b01405c00c0b00800840203541e640c0021040b05006506210000d006420300384290f4803249200c0d164101c00382c0d540d02c00c0000030246040008141581c0350340c082810345551018040d43c9215001c01641c41e884882040b03071840134080302104250 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 822122302 1106 822121196 822121219
    0x90a1202041d0705300705150a05030703020711040608010c110a0b01050904030909050f0a0f0c122c0c0415060509210105100302010905 60
    0x91003101c0c20010707200415044800741030014004152900141c4080006003018140103c0f0f2407071100400a50052031400902c54100c0b030510000c0c150300010060007942082200c00d4291035442c502642410b081035001052031200030040001c00d42c01088100400607000c2103501c0740f200007001402856200c0d00c005001307200c00081800020080707010071135544000309803d043c145c1c2010401c0456230821040c446070002c090401c070200040b02800203441e5855100300340c003480c1c035100401e00c1410a01280e00a85441c1c40061090f20b1508110f241000d40010f50004c203071108400109110100a00c40d0b02c9420540008207841480700700030701420040402c00c450b00031411507082021001802890b00c042c4890300445010910820140b40d00b4584640541c05c0310104441c2e41030b0f0500c0080300c50303003912401d695a40400080c00310034002c540c0c0001042014090036650100c141 = true := by decide +kernel

theorem cover : BRFrame.Cov 821942446 822122302 := by
  have h0 := BRFrame.cov_init 821942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 821942446 ≤ n) (h2 : n < 822122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
