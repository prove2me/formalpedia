-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0792
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:50:13.905873+00:00
-- url     : https://prove2.me/submissions/7b5bced0-d79e-4904-967a-a1830ef08c64

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 142266187 ≤ n < 142446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 142267437 1250 142266187 142266191
    0x903090f0112050a0f0b010c110d0804080a050d030b0616112202070c05090702100f020d05161d0307031407080a0503040e09010203060f0d061b0f0305010f0b250507120501 75
    0x7801200445800b52400409490203200d0091049caa25008070366144051064100c04c0c04c0981c1c50802906090041209a40c55002034070380c002d00c1e07a45489440c05407c011600141000e688250308022002034000c001c103902c01488035858550340e4a81c8549544007200410700358402c0404540000c1d41040340201c5062816642c04251032400880ca03d2090003141e0040404500400001e4043c0080e5802e100b2407a0b030800104032185100d009192007040b48024040408040d01001490f820015420000c1030401c0d946900143c0c0d004a1160212508412503580b16038030010868100f0380f445d4010300040c8220004041000808400340c002c170342c048456801245e4803840c1c468207030700c400c5944940c0a030810251983c180313404182c1e282414041c250005026802c5d2581da4041d4005d2410b80d0013040c0b00b01d080642c241d40c1406040d0150018503240c80c01030b854005a0002c0c2d000c1d041070121040c003900444a041c84104000c41c0209801c01e00726001e055071140302210441c0c0e09a0300756001c0d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 142268687 1250 142267437 142267451
    0x13020907030c18140603040f0b040f020906041109010f1806021c020f121602040c081f0806040b040201020a050313091103060d08090102070b040e0703140903090f0112050a0f 76
    0x3c0e4000c004281221084013103a025078011104021030780d4001002210510300503e9820003103103181c0c0c041072069100d40a040c40740b441c28010095140310041c401442981070101d0501c48000002c00e0780d1080500303090840da498103140c03099035205100188080301c5504003200142d0320340c4c005801010381c03a49200707461601000c3e2504036192004420074000325400002c0000320307140310744014401c000071b00402206444d0a60300240507203100050304030020f00710310300740712544c002e2460b103095090024500002442c5030008481d2141002000541021000800241564001c4c028034000d950302000341c13070b503072103c84100507460300d443c1c06401b01d1103103051304c5510074030b0211040324010701c401040010280c10390f0399050302a602400607141103015044002640744140000741015185041f8001c403507241107800102203d030142a44e10f9080500801e00c144460040100e681d491410790303c0d103140042c1603006903183c0c2c604590300c501040c50701c3c0800000f00030680c84072180700c040c01c03024401d0f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 142269937 1250 142268687 142268717
    0x1003030f051201060e0a0b0a03061701020a020703080c010b06030a020a091208090904050c04090807020f03060f0130030804110609060f030a06090207030c0312060b030402040513020907030c 83
    0x25016088030402c0e44421000103005843c02102d600e0030014004083c80340c4c658440c950913030700b07405c01841035002c03e8030f403001071003010100003980030012410303402142080440306009590340500e20026115020003d2682c0c445031082d045a000c11300041c01103a46c0f810640301c01c00007984450b01da11b001816001020401c9a04418102100c6800150260405170404100048950f0107401201e05216580300304d040703901d2300e0007030b803c03c20700030341203036407a80c01034018400c100e20545203941c0300360007000410984981201e019811745e414020b03101100c089042c0790300346e0480701c0924508803c803100c20b030707908066101e810075110320300c581c111010401d10303081406207900450085680c010018080550f2a02e0407070302455000510080206400d940c0d00c42107400ca9014034420750004a1400040c1c0a05400c000075420030343c080d01040140a1621000310101d0202410003441284c039030001c24404801866003030452030b001080c1100e2070030080c41c0940141005004000420700e408030798644 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 142271187 1250 142269937 142269947
    0x60203030a110a1e032c0709020301150f182d0303020618010603080705010516080103051b06120a0501210203060109110c0a050c09090102070c09020f040504051003030f 74
    0x380801a446030407424139140c0b8040c590600031001d940c10580d80c1c102c20780c0c00a80800d0031844a4491501541241030031508407824000ca030340085541c0c4c0d0041004120620a44491a501191600d0803048801040404452100e000b4540a2400070000340116103000c10300c0030b801031640d00c00d80300b911510301c0c101e6403404c0302071500c00500541c11000c00030310000080700c40ea04030498032070000120b4986030b559400042d080075006075003e8bd9a6030811800d42a490f4140410700c1403800c1a01c02903155a48080e0b480c0c0380c28817041030558514802541540f40d09056a10a1455048240242c50700041040050009110380c2c810154800c0c81c031001c405146803400c00d1607402502038281c0b03a00700b81c04040070703110102e03c6081c48181005030040012080c00407040782031055018010540301d2100300400c08102409404499104005202c0081e124508010484149420141e00c42015441c00001e074040c551210790401d0400c0304010b020f410300040c0d00240c4c0e21a803140b036480e0a1052044403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 142272437 1250 142271187 142271197
    0x20309010906080f0402010503060d0203060117010c02060103050d2613030f050f120714070c0e011a180a08030c0c092805090a02040204030b0702070611030a050903010b0307060203030a11 82
    0x1084c4500c1d0040340155100b00d00540d403111010780013490000d075540c08a450000240d0102c1c580762240090120030101c00c1c05960742915052004002c10350640e122507803504070030340074101030080c0c0010320311600c2041d01020740c00c520041c0c034440d080e281000450a1050b22000103c001881e000b0200c5100e078024001d40703a45800003240d440c1010a500c10ba11314024018101c50188860682101e46548003d001818090b05c00c1c2100d42e961450080120101541131304246415410001101e4550005805452910001c60100740c40c1003100408554900d0094101001901000425020311b0000281c11076403180203485103c1190b44503501d09000f4680405048c3c64480722030201c08070304000360405900011000181d0b04010311560010b02242d00130382c4100c807401c1d039140400690039010321502c0020042414014200488142c4050716480b800c0d0119052150106a00d0615142544003034000c510240c01c6481c001c1d100e1001a5036508200e07004a07000e828181280c50801c40c080c142d403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 142273687 1250 142272437 142272451
    0x11030609060c040302040b04090f14070603061809020118080a0309050301200c030409050103060603110f03030a030e100203070302130815130809090114041a0a030f2102030901090608 80
    0xb50a150466003000060f0219078150f40c1d1194541d0000740106005042c03146a141c0b10751500800f428a40d60028208080d551140c018140381c41c008115040da0f0b03980d60082000030200001e110140b910060758260416000220004280040070036050400104084e81034041d0300c2c0c8680c116555070401d0300340e404940035107014801d01c011107000703d801203020340018004d400540e424244c41d460306800b119804d07803043e04d05903241d010400500020441d00381801030103551102d8011100d80c0860741d02e1150000309400c00d542c070001c02014031b10601103980e0549034000305660301d0900e0b16009010b50014490300305480202800060703104030004d80e02c0e1414614442150f0161745940c016240354000400990300780504218145107680c40702000340c007034010400c4a05500001406000407a03890450300801c000003040c103188c840c0d4544c01e91508a81c0d22041200c1d035950240f40030f2962840100103100c080040c4c188408190382c000c0040c00240000303907110604183c1e281e104440780c200c01e841c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 142274937 1250 142273687 142273711
    0xc0c100b060a201b040e01290607060e031305100816030b03012d0207080712020c03150103170a05220f0605030a0b0603070206130c0905041103060906 66
    0xba8105004075081c0c00c21410781a12102d01c60f86a41c00d40d0309000012004c940307403400100d02035205140500c1040c0101d403400c00200241034111a95400c8100080000c8158204101403e040707661540c0072981c5095001c01c00303126108420300003540c0c83c8c01c245800003408a0780c050226a9041036501030403043c4c101c0c0d94128807078403600c40070004c0e5003400a9000806032151404039072628240291042684000281c51041c4240507056056094014205982900400c00c91011840303500c2601c0501d900b10ac8145048ac44c0f141c000e0b40f61504606066406000d60400321040c002c10840142c102c80c0a911554500b806615030201244940e0009001003030003406610044175043d000701e85840f07550300824a805441d18081c00c4081c10316800f1000090700001040802c02c118014640701e00c100760303049400e500304000003075114400140400391065819502109019006101c07100800c1c00c0d160400107030420b414544030120306110002d000f4443c2d50041400110005440c03442502d400b518 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 142276187 1250 142274937 142274947
    0x1a04060527060a03020d0f0c05150915040306050903040810053108040f180606050a080c160f12020601030b01050f03030c030c0f1002090d02091e0c0c100b06 69
    0xd00746910003410326504003072a4000880141c4074800940c0c0207a00607285c0c004901c046142c55203086a2a0700258082e2440b204070703e10011340c490540349aa001120340d160021030b0b084c03004c0418000ca0748080e0586040a0500c602110301100074815a2100b0055900a01200e60030000742c07007094803040540c0c0da80302c03294003007513010101c5092035008403c130210040040e500c4d01402c7d9006900001c00c006c0c00e00c501040f82090030714062850002c0a1400d000d800c2c40d00710058418001e03100c55400740310000d400541e004001d8000c503000016003031141c1008641c2d03030810480c0e508074500e048419551200c840b664a0b400001c919040b241e01c0140076142d41e082c20f080c8003018040d0403c054240c4000d004a030369a40e0280054040c403402c1e400100680e03400c1d200c01500e030492040013160050f204214800c12920380640e0041e0719601551211402c0d10380c000c1210640c0075a10a1101800311074003480f5a401600300104000d01031142101d5035009540000c0c0201c42048402640c8800708001c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 142277437 1250 142276187 142276249
    0x40f090b061204080910030b0109060c150209130c030902090a020c0a060e0a14010b0a170d031a030a0320030c0307390305070b09031e030d1a040605 65
    0x20707255030301920400d0340720301780701c2d10740c010920b4038913044200c0b000f04c1c0e1940000755103940d100c0380040c000e0826240c01c00510f900d5072a00091842449002990150002000c00c05c648a00914208607039042504000c0c01d072640c0300050042c00c00e03c10072446581c401c0080303030040c0f0850095614031b80c032030000f5148190280c1e549000804404a8140c06401a0350b8202c0102d4200503128103110718001c000f18550102e0320070003c031401c1c40d411003800c0c2c941d80607a403042c1000004540030450094100019580c40540c0303256140a550890b0030790511441040204040e4800b50310000025081d102030a12800380c81003540360b020341c3c0d82c48030303942d0700c107000c2900030821813040f0340000d08400302005002a000c1401d2002100d031140303070300e8ac4111410020004c0000c00c0011718018011840c806050210b0790300000d4440d65607034060b0a580104900003058650140b040314880015454104030b084c50308500c8020b60b512803002e540c40340d4075001e00051103041c102016084030035418a18066040018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 142278687 1250 142277437 142277467
    0x304030e0919020f0306090a021306230406170106020d0c0618050a0b0103030e090105090c07050115080a02180402030a020d0804091107140c1c17030c040f090b06 71
    0x40c2144008507a0600b4100088160300c000d2203183c58420a0650b245440d40070300686ea00c015001141e0148100051b4180500c00901b00058803614504248030f8800d0003440c1481003c82c245002d8140400100081e011b50080d2035011120001f40012241eaa0780700d80c02c0c0d8407170220400701d0700031444001c50310f00010201d50049480360b1940d030007200d6804154980b04d2800401c40d000f10b60b2001a800140207054100b16134252081d02255091301a41c10440031a10070b03480908048000c3c0004107010b02086800c0d0084090310003060703590500550b03140c415980d10307040103c0c140d010b6441c000b0300b1800104904140791103a078029000308110b031005e50a01503810401c920551300c0b00424040807507401c0e030b540580ca044281e00e2071001c3c1c6a141e1414040b00d01100354080340340641c0080c20220064590060301c80c40c41c084800480000e1489050407500d0805621072504d00041c00020040c02c0302800d4060703c159200d00005402d543d485280c21001c41e0021201c240d4007078824482015460b0b884 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 142279937 1250 142278687 142278691
    0x80c0315012d030b04021e060a050c010906090302060106171005060901090f0305030301140d0b01030602030a090b01260312271902092809050106080303070804060f020304030e09 78
    0x459100c0003001d1208940002c1100c290700121601401c4900f4402580303012100f10b20004800c85000901c26440c1c1c0c0000d0561183c110818248140881d4a824100007035201c40e03801500180284aa0903c501d4000d442e110240a0800441e4840301304103001d1034000d1200d8441c43d4240944141541004208103440d00144034250401c80d02510101d003000200e08640021840380006503200d5040800750018442d0403070801703000701d41c84c11106010401f940c041504403500b0400050380d94a5803c0204041c0228501c05001b80c1090400061501e101e0401d10714016400c1ca00144a541c1c07001c61b071a20b07481865001071011010202040951020341280303908980b04101610516405151603401c00500d028078104140c14424908290300b80499079640c820b81c1c1030000305811081c0900f0018030647c10048000065480201508200c000d501400140c9402d0301100d84070701e0b06040c0100b484804550841720181010b442e0900100d41d402940c0c0140e40c9600da101044400d5401d126940340c0c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 142281187 1250 142279937 142279979
    0x50702032706040b12010e0a02090906010c0606080d020a050d020c0307030b07120608011b020309010c0f060207081c0b0f0603010306020309100612050c0d0812040c150306080c031501 80
    0x820030002501d13441c500c0041c40100410780e895011585000c140c8042d0310f80080209004a004002c809072942d03a0070911580300c0380900b40301c0d0f440907840c06c10400403c50380d0400d080c1d9106052050a200d41c0005880e210948540c00711002d60b4400c00c4100d07204c442005205130503901000042c800103440d540042d601c03415620b000241c0f800c1750040e0f002921900e0740000c4550b5942d00d130351142c2144401e14140500c02e00c0c0000d40c5441c02000000701032101d101400741820100c00d40d0f0b8800c1042e80d0b0116002c0d660080051902c590039214040e404095401840400c1d03450800c002c0c2060500340c880e5000e0140050544d400c0d83c0c0780da1540170203540001c1c0141082c0c06455000c0c06003004c5403046801820100c09034100c0d00400349440c0c0d24040444100c1c038072135481c03554400c001401c1c200444a00ca21600c403168a0707921646804a415105034000000c07511030441000c80599040c0d01820440c3e8000d4102c0c0c4203440d1140034141c541c910b440d1a1058950043e0060000791503005081d00d101d11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 142282437 1250 142281187 142281199
    0x3050703050d060f0305160609060f05070b0708061201090302030405010c02041401060203090310151203050409020724020a0f031d0a050307050d020d1d060405041406040507020327 79
    0xc15a100742c044030360580003001641d0301201c3c2807041c040304011110396002c0000740103510b18100200a484c02c0070358403801c820800c5411030021480c1c031035000e0b554a260f10038550400303410310182c05002107100306e4440d809010411210300801105008081440790903801030b501e024144001100e03040c00c1040280d80040c1c90710302d0050840000750240740281a03e9020315110032203841014100351902d80c09084843c14182951251080d01403076808950359440f00c106901010f1400382c40ca400b4541c0403240180c400325681c0180b0008030307207803981c000d0804842580c00e00242000812402100080d40c000b40c01070455181c003501961000401180700d8812500c0102c070514000d19041c81600d00f00d6860b00085a00010040f00b0000340305403103050300140907652480e41c6c0c02029551080100c0d18804031001e1421500c5d00c4050440d0042c141c0940140540070246d1420003592509071090b5006520700800640070602c04002d0b607004404035051061500100032101980c10001000303254408 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 142283687 1250 142282437 142282447
    0x706020a210e1209010206060d0212030c160b040b120415020406020f0c1507030810090c050c15070e090402031e100b010207030b0a050a091407080c04180305070305 72
    0x2101000801150050004012401c00300411034182044010f03544080414818050300400e40c3e0003194565218134165000e090181c054000140d04c400710100503c40390100040f0002024401b08114024480c101001485603a4580d50b507140c5114503c203009140ea0280710052500781c05186c540d802a00400040c18140b0142ea01901203074450b92003840580e000c1e0320501d001ca4000d20440e03001c000210303a042c00c030070301304503a0b045e072881201c5008042003407100018802080a110000182001c0c1d0700401c520100300320094929400034a40791020b01c00c0d2002c22680064203c0414454101641c03186640701c1c0c14424010301c69006042240d16016100c0602809003090855007100c90030000100b0003200081e002004603005803d08a04540000d0300c03d0011844601c0e0350f54011040c0d180005107666581c2201c00108601c0350000e1a0044c103620b4100007000020350302041d11b003420191a46200c0d043c040100b03c0d050400c0b28500312500b00c6405000c00c3c0502c0246c100c160090605901e03103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 142284937 1250 142283687 142283717
    0x6090b0307080c0c010f020409020405040b0303070309030311100c09091a03030405120106030206030a150f050f0618031c030605040b0d080901020313031203060504020c0715050f0f04050907020307080706020a 91
    0x29070412741003000090b5003c1001c200d10301d4203004141c0c0d8004150b029626005036914010081d1050b0701001e818452080c11160002c0401c11411100d84c140c41d0042040b0090154010070030040c900c00d21710320508024185202d40c0d0410001540100002d006501e818503060611500c1402e143c1424485c0d5a24480000541c84e030100840c42002140400a014050030307d4821038046183c0080c0300d1010904030070721094a40801003001114101c8549232142d60340134510240d045032150381c0707402d4042c650340400c019003550b400c1110000b213500c0c00c0c00b800e0340b240f05100c100e031001c0b0700c032503441002411f1020101d0300c1e800080c4101c91040c0705492900004180722a81c0040030b0303004958841075440c861403010b9152160078040d000c211000d52502e1a54440107581e420070740240500004803204d201c4005014504031141006111800e43c1c0301c14811050b4031264201e40300321401608a03100262040b4800710840f40b03440c1d400a2004e0802c941c1b5101c00c0002c1d004a4000014400080701020340 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 142286187 1250 142284937 142284941
    0x1031101111c02071a0301090207020609120109060c03150510090509010b0a03140f180106080a080706050106020c0303031906050d06020a0212210c0702091006090b0307080c0c010f 79
    0x249000c00c40889600d0090b150000e2420b0307120b40c4103000c10005d20514103620810f11045a0460b0314a040241c0c41d1003550001a8181c882c003407040d40e00c01c1c02c2040c0c02d000304030103410007410710740110b01c2000405140c2c00309509849484100c001045c030040701c00e1010b85404440351540710400c5c0342a0600644400c007164030004280c20403807002601048078480076505000302c204043d040032030300416007040a00c0b80c41d01c400c0980352695001c860701f11040d0000e001d502038001410300da41101c1c14a01d4504002c01179610105054030340a00b004008122140000f4a904400c04050025861a85c0da0a00b80002c5800d420340010000d44a290009040c2c0d59622031701c4180303004100060f540c804019000c3e240c000500c5182041000504c5106032a0010700210722038415400440d01440d518071a0716071040c841c0901c020342c420740170014450700000014011080d40c12684a01d00d880e81c441d00c04202e180400c81e00100051881c90000c0c0c1d56a003100064400030400100101d400300004005100f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 142287437 1250 142286187 142286203
    0x7170a0e011d06010b04060f0e010e04020d091a1510030b06030c040e100b0405010c170c0307020102070b27060c0a0501270b010522020a12050601170103110111 70
    0x2d402d105912070405000d02404224010003941001924141ca094006045144d0712400b22090285c0e02211035407907405044440d607480300042045584002d5400500010819482c0c152940130f1425000900501100ca51500480380301c826038a103c161a81040f209005802400e8205921414090300603110319001d0b50040b076460505544481c03e000040d25804401032104070030302d4103000c040118004881c02c84054030000e01c1c201c5100c60315401d042c07401d0007061030860320003000000c141c10304c10400302c00361071020300c02d074259202c46a0b511705030761a5004401000ea8a41e546c0c0d9041c008001c0d0b885003184170914042e01144c04c2007002010503080c000250000e95107651500c900c03800001c07040075002c01c944006102410f6105c660f4480b0210f480050092901a044032070480011526012030b607400941500340c103568403046441d00030030841c81c95002400460814004c07505030743c05100d843c80c004284e91408207440c1e1958a6008454180420042c140440d50800c2c0038911030500500e0b03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 142288687 1250 142287437 142287461
    0x301051c051203060f0301090210080703020c1f062715030209070804110d03021027030f09050d0f1502090d0302070e07090f0b090102011409010507140307170a0e01 72
    0x561640b4000d814811902d07145c0c0c031400d01c03d925100748040103a03503140c0d17200b0002400d450108500ea035a500194000d11071040400c519202d00c1d0721550350603102c91200345201c0036111052000340e40c0c4200021080d01b540280748182c0100210820192010340d10404401a022800086c06640e030b4011840c2c03e001610500c00041800040106000b02d500a42d411103c081c1e0714000d902d070050310020b40f41d02548035405201511280145100a412a10741e00015900c8c10001d0840c81070b450017a0021841c801d031000442d0326104005407602e059100744d040a41c03c100c140054403210380d1034800401d0b16801d038009181c1d00f4042500b244c2c4408036a0468580300780c0040c1406414912070749150f640041902c003c01115081c180001d50a6145403021608200811a100c442d1000142d0140480384002034001250600304020f06a05400a84c007401c10340d10384841d012a071130700c4c00c8103521040b5000400b0403046411400c1c0c1000300c003102540300307040d0350001590304020180b040c252444450740c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 142289937 1250 142288687 142288723
    0xc05030415030506030c01140d0b1528140a03050603071a09030105253b100903020108010b0d11030103030c021e0306040b040206130b0d0c050304080301051c05 70
    0x813429040c1000304070390300c12007420710400e007080f0b4400036601031107500c4d19042c030551245003071410350b1a404019251101450908c40c0c807002076920001d004240850a40240c1d1414030000f11428000c500c596074050340c00400c02d1425207665025000303880058000e541511410500242103903100194520a404884089545100c000100350039034401600b2031407e5610070b0740c800074000c502001d0f5a441d00c3c107401c11245c94141c1e0b5200600040d11300c10704665a0914a0000403840c08029109440c0b00c8200c49020300040c02081c201e0b4210400c0c00b0007070115206400500c00c1006070b4000d0420140c001d00d0102e14100c0403160034216801c2a07000314041006900002c0461501c0001d1101181600c1501c004646200c40081d655200161001c0c1500381481d001c1001e548401080b20200300e00c1800400e420380d84c681d89441140e21145440716031614003114101c2c3d0f13501c85c501f101d0090b0380260340e80382943d00300010005e501c8140c0b0110030149420000410000c0c50074404a0f001107080d041c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 142291187 1250 142289937 142289941
    0xd090e010b03070509121f14060d15020a030203040606060c02010c0b19020c0c010206010608241f020d020f150c0c0102090d12080c03010303020d0f0207080f030309120301050108070c050304150305 86
    0x182021100d40d1101d107c03071250030645c0034699044c194004a43c0300d00204c8075045c0e1160b05061144008001c4a074003508240005802903c054040e0025409648140300402c241035850208613800c4003031160080c00101130000304e1010501802c4100c1c0c0142103441c52000c120302100c4040100c0e441182110400d41200700000c0c031303035a0180140c034010100b90070000c5161404030003400d094090112900c100c400800050f02080d140c00ca845244040040d51090142c3e008000295446c0c040c0d84001005100f40b1411884400b40401c907001d20480340140c492458488900c100102c1d048406181e000e0340d404c0c049034119543d40c51450700e038540901b94404103a4140c0c0c1004001500060a504800e01e0030001040060380c009618420007140b498100780d4000c040303408034101607465005840354810150520b421000201c010b6001c2e44840e011a11103031001e4803407400c540824031550380801e03982c000062096000d006800c1480c0c7c0701d0410759180035200c2d031074204500c160b6012440002d80d0307041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 142292437 1250 142291187 142291213
    0x906091b04090f060911040e100b16060b1507112701090c020d140a0e120114060d38070804020f0109031203020c01090b0702030c0d090e010b0307050912 67
    0x10404c006000b0482c010301c2031030f40380c40e9849185c1c0300341d126040d2800c1c842000901c4086c1c094401c040039020300c15525503a03803005003004441030401503050b01d202e4545600c01465140803000900f01a140210305400c0507556103813a031070070811007001074000031840405212401b400611a1118800c48201030803541002d011000b11182184124190350002500140c40394014143c10400003022000c1a45c0d01e207400401c0f20a0f0742d000b450940c21a00c00d01004400c9841900280c6c84001c0c54901c095907650741c1c1c01000311034041600068540c01c3c2c420f41c11b03002d0a202104040c4008074030802d5007150162580804070140080b201900055810790511003149001500e0b80102002403800114060031a200c5017105081c0d04510400d01d0303400104080c103888290407000d0801e400641e440c10910340820088d46070782c03182c2068a00b81c040c0d08000c0103030302d005d41c02c032406440d03410021200c560708110503092644d00c046c0410051050a100e0801ca41e9243c4460407d090345003009031111b070031402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 142293687 1250 142292437 142292441
    0x25110f10300f060314060f0a0b030a020a0806070e1806060a0c0f24150605180604030602041a0304050a0204090c0905150a091107020d0314070602071a01050906091b04090f 75
    0x719031720205400001c244820740c0042e002c0d007500f02480c0300b800a06800000006403401150300c600139000411040e0000c8d1120000c039903584100c055441b01c00c1f10701d1601e42001a42c41c95465030510f41c55580b0b010840509202d40035041050342d074104200c80d400c1c503445202c680300b00c0e000b04841400c0d0742400076440f030a6006134655600d9910700c2c144001503100700940b100004500401c8208200880c80440303402c4a44043d501130a40505065a41c68503810507201a40c003070702480304001e9603910396611403c58201100d00c540c2c2c0101c00342102603003680c03c10002d03206d250003e0b1414043d540c408544045140f290758090a03041c100544007403180340500000726055403000c041c00d480d0041c2d40c4007145100301102c00042e41210b01e24a410854a01a80e1300b0181c2d0f00680300d14000440c0c2d200401c00140e0040500901031004107032031007040e04035650318210074010503400c101d000002c50b40e141802100b00e60011481a14003200c05009403981e80290001c0e03100c18131440e102c80c800d0910030424 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 142294937 1250 142293687 142293713
    0x1804080705120319050c130f080c0d051f02090402041d06040204060903030e03010e160303090e0103020109231c0209060a030c060525110f10300f0603 66
    0x42d9002d94214607162140c0000044000e103914440c1da101c0c40040c0241101300c08a448007080000044416510b44d004414000b0f260b0084011510458030308079440d150042c14000d140742d1002c0101041203408082c1401c8000410099200d540c090000c00403a0395140040c0000d031442d050004070404075010040006280900001e0056104200510410380d009940c4c40980f6050f0030314403400c445010100e0b00510307050144150f14043c4900c0001000345818000f001c49010340d848000b440c4d00c034100c0c111444002e100084c00310f0842d0030104038a40404120765410565401440341c8030000e6001300359402e0803c0c0100302c4948942000b07800318035180d04540e801030419a03010b515181160b0300c0303111480c440d001d5081481804540094501d034500186608440c0100b07654402d0041403074070511a00b07140a038a0702c01c100b001820001820803c0c1e00e580c2d00620f07551030070b01c440301024400500c0c0141c02d0300484da0b01c054803000c06141c011030013441020205c040b00022407500c2c50804002e8040c00c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 142296187 1250 142294937 142294963
    0x6120a14090303060f060d020a08010825150e030703051f1802040b03030c01060f061d0f040b010212041701060b21060d120c0c1703040e04021804080705 67
    0x25050a0001245002054991000095170210400d401d030a001551a005900306800c00030300000380d400e5042da110410904035040340d81290108402c0d8035071a0003540380b400c02c00264070442c040400117280d101c4160381072000b440c108021980c0d100d4010a082004680054503544d0040340c908590303004040f000b04448843e00000c11030134102c0c40c1d0009008081c0000684125200d0840300d815940074000ca512030540d40d0000c000c031540d01d2400b11542c420703d1054501007528580042c900c0307900d0302c000c4000c0d024001c14020003240b88101300001004100802811846400601140301c2c130740c04010b00140c40c03040c8044024882c060112829a40d02da040420161000c0c4841c2e43c01e861010014080341f01d040540560303640c0c1d0000400c41c950210300028016055090100460503041407101e4021030244c0d41e400511911082890019a45407c1d1070100344d108010802020403810146500700b13200500c5540030b08085a00c2c10040c3c2c2059a041e00d006200140800410200f08101900100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 142297437 1250 142296187 142296221
    0x50115050f040905060604050402060405180609160f12020d0c0203030402030705030a03080403030519050705070b07030c0f110f030c0709060e1302040f0b130b12070302062706120a 79
    0xc2c651395800c1c0c0b15000902101d01543d1600046021583c559013a039015010140032000c8041100540320440b01c0b00b91070850080b80d054020071a0b528407410b0043d03040206071100c0c01040d110780c0d000c032025042d00d100b1824a990a21140701100028000d800440d5110360003180c407410140105820584594061032090740702000b25400a60090001a0301503094200014696640c0d00712415060942800d105c1c1e0398541000c0055041d008000f40c10040d0041240305201d40e90444158100c0d2600d59038a0082100301180901c40c5115801d04030100b074400d016240d00004000d02d540c51030b009044080071581182c0000c0c40501940d119400c000c4c8900208000581891401165090b0781c1840c00f1b40504d40780c00c99a283c51842d038015201441c0c0161444000c0761613440450000c1c006a98458410788100f5403280e0f00d848001003e005480d001807a2625202c6100340a002c1c0075103100035001011002e0860340d01c20380e81c03880a4100900450203100444c6441c06a17102118030124503950041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 142298687 1250 142297437 142297451
    0xc030609070b0a02100906020a0305090c1311120f070f030219030911030709050a11030103080a0f0908070306060f080a1208070e0603040606050103050906070507020405040f050115050f04 82
    0x500041e00000c40744440c0c4000d83d02c880201c401c0b0b04054800000c008400d043c006010108101a401020f10b840c241c2e50400071601c2d01c200040e12810030f180354130740c803200480304094070f01003943c4040c0640340500c0e44c1d00c0c605440d0340c4240c3e807041d0301112102000030720a004c11130032503002411401010314078a0212b180600d00c0700000c20f0b80040c03054a00415076146071010400c111012071911040000707085680f210380e18004d402c09001d0403203070080040d0608a4040c800341c680415a41680d620058403810040c09200495101c40e43e0301f00c85041049107400059120401e2002c400910b01540b80480c0c014144464950111940e9004009690052a4a0012880048102043e01220b2a054281c1d84941000300c43c1040719828250744000004184410001f142d40606d04403002030300d090141e940e0320300200f0707164441210201d0202d1000c00001e001450203910041e0b102e80711780300ea103100c54403548a40d030171103502440f803c0f84042007080030f01580c44c02c81140d0481c0102124148400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 142299937 1250 142298687 142298701
    0x5060603060c03131203060305011404060606030b03030702130603020604090f0b0a03021c03020304051c0b010501050909040b0702150c03150919020904060506120406050c090d0f05010e16080c0306 86
    0x320300d80303641c090400c0c0c942074611217103144250800c2d0000c0d50840300900c100485868440b00508044d10122038042c54100b000822a0290040014000c8001c2c055818208641c0034001c03e1403c200000740c4c016610400480141c4c1c86002500c0a854180000a1901c2c00d0f45200c1040310040140c4910488400c0c40c06c00c010707a185141880b18000c4d0400c40c040b21101442c05a103035000b20342185910403c0d4201c070b8440a0131084401c0e500d42e0040340003d4950340c1e20401501d04c0e1050105283d0800039800025002c00e851801c62500814188111108400e47c0f03007800b045c1a10680e14030011400000600c00e031050580c417843d802d0710080310f41050038200b000c192100e10200310707020001160045908065940d5580c003d030001c020143c00241da82644402102d4481412101114220300d8200400c0520f424241600c540200140c4001c480762105e4803880d0344040c1c3c81100321500d40d224511558082c006100d09860000c8a8084040312400c00740c1107400e10003402d031104d01030f1340310200700403078 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 142301187 1250 142299937 142299961
    0x7180302060d090609051e070e01060804031d0405070915080c090f030a171b07030f02090a15090507020d0e03030304060902060f0c0c040f181b05090405060603060c03 73
    0x503229020740300143c1c403400c515014002c0d08032900c01030954080c1c4a40c1540a028404001d04c11840102c1514102502d42d403c200d1000428068200011803150000d800a801104010303842440e04411140d103840b0440080c1c15500d0072100c2c42c0006d641030300108000000c1c00b64510001d2200e0400d000207240000440e8020f0180d064654851400744a629102c0c1e1002d00074045415000701490b00c420450303519a903c02d90044020110660718501ca60701c1501012a001c0d0580f940005803100f0750899408000380d100015022070112951340000e5141c140103110144010581d0010126407403410000103818100d00c0540d090604c00044007054641d07a010044a601076840a40055880c010340003003041c07400f0f00084007010440005081242010004007001941811a0140001c5059010040595546100035044c03103005481890005040d150308640d0042c0b000001c641080d95580003400ea80825181a034003034002900740203290500740403447d071201494962510790b05080b1b1000384 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 142302437 1250 142301187 142301197
    0x20c1b01032d020c0a060b120a122001050702070302090a0c0c380105040612150507140703050418020304120804030e04020711090115020712060b040509060718030206 73
    0x24081001c02d03203a0350101c40c0e07054800c1007072140c088034600358092810f44020b02c03262042622890507102010094a0002400d100341940401e040482046407a8161116044100404c0d58201643d0110707200388002d10401388110503507401010450301d180140650310710007030f1a02c10114242150304000541241040170010390150b540d0900520b05850444146144000000c3c0300c5204881851001800c0c0402c82c107955044404110081c0c0d80c24040311145480b2000402d40420003410f254801da580e8080c1d81e001405081c000340700d41341c2100701c14040d07104000803004298049024401e16415004c0c01d071019071010000c42c91424207889030130311102c85807034400400ca400400a010503100711041540d0b40009442552640780c035250560b070884000c1041070103403044400026080190400c90410000c41d5005410700340d04007020046242e80d520403d032111b40e1039441841044d2170b00d00c18588500e50701d0b8041c1c803040c01c0071000103290380c0c82120050520540680c0038005030b554001218 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 142303687 1250 142302437 142302491
    0xb07141b0313060908010e06040b0c030907050a08010c02060c07020d120c020a03060902040b0306160c030207050303030408120109060302060f07150e1b04020403230f01020c1b0103 79
    0x1444030a019444586184581082d2501d034030000000012002e0b04240c40c4e20039950762500901440e404042503035941d0b41c00301c030054040440324002c20550a5104002c603017110740e184c140c850407030302c40c404118104903a42c80340709669503805502400c42d40c10702c80c95030020440c480c0140740208603000103201c4001650064011a21401d5103c2a98001c20f00b45212541c050065146140d90b8100403000300803151041c0c1c0240e0511032400d00e40d140c0807680c24442e1036254a0546144080b030800c6880404900045003588a2440302046075941000694030540c4160758281d074a980c0440c1c00b580450301a07028030000f50820300b0a00044e694081030b103014203030303409842742c89080c1c500f44006181107040e0700c0225940303081d07107507c0e80c0000801c4508600d030040301c0c01d001c6000014103000c200c1c410b80c44040c0c06071000320300315141c1c0c0700c4e544040c088a8007220101c544400c0d00011880c2241d00c14140c2c0503503070384203058148030041012551680d00d0b8090801b0017104404103410894007021003181 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 142304937 1250 142303687 142303717
    0x3080c160f032a06050702011403060904110f060f03041416150c1505010924031106070b0106080619080309090705040f080106170a05030f0a0302070f08070b0714 71
    0x3c112955025107545414003078411004446550707510002d04184d010b100140c0c00a01088954003101460100f101c0c010311016010701c0d00f030f5a42e5110440440c01801c3e0031a4481701d2484000e02c5039982d0b130003520360500c02c10002c075548e00701480d103242e00142805c50005140c0281c1ba40d0001d000300d00c1415000c8a65040b82c1e91404214000101d81c60305030300100038581d80181048007404c407120b0303005034180e0790031003010003520002502c041c1000a0f246104d034a5903421450900000d10009120700c00d0442c007504480c1030200640d15190300d514241c00c203400258032034080000304c2c54115848403481000b032448040260620802d50745a116103000b0700e0184842c100400c13052840350080783c0041607140030049401d915403220b18064400c521031203296140e0400c40d8510301c603010602c48000d0382c1c454000c2d407520020040c1d0440d40c0d04040c03c85014194280242008a424541000107661240013420303524141480c00d0684100060100010840040c9011501c000c00c002100c940e5565003007a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 142306187 1250 142304937 142304963
    0xb0f01051821030c0708061314102a0309020f0f010e04051504050c0a0503070f091805010303030e0a0b1801020c072606070507030e03030d0603080c160f03 68
    0x10a030380b5098850b8480d6500140007070640e2602c404000707800740e0980501502c982960f6007103810b50368103040ea81c010304490091002c5001426800c02000b0801d180415a00c3d4a0782004106c1e048500801401a11500c00185801801d21140200010312620705040000030001d4000c601040d0040364124012034082c140e10040360300940c000000450700030421b00c02441d107d040803450711000070140c0d0095080001081c24401d1240a0751545c95031075442604560721004201c4500e21501440410320440c41c90100c1c41c600348001c0e603604e120342e01c000441d05514514000702201c108140081e42a001014290001000700d88083e801503075200380d12114035400c80c08140248640704801000d0b200d008400240c1160004545409402d2809520b03002d0341640c4c0403a03144c000c111010000a0401c0010000190056010803000e17840541100d0401d4450601e030000c4406130b410986110002240488640204006440d4040440f40004184500d815800024038201c0e01004214640e6802 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 142307437 1250 142306187 142306189
    0xc020a0203010f020c120403080706020a090f060332060603061219030906080408250f0521070201050d020f130f0501080a0507020c1009050d080301090b0f010518 71
    0x10405945540080081060700006071190000303500548442c82203020f6510090000c039414400c1e9012a90401c4540b0f15044080e41c3d00c1c8002e6001d8540e050a010040c00e021525400020f20b40d0007400a41c1c400240b40e110017244500030790014070315820091030100105010707611480340369800040a0b1001c0d034882d102d040c00034200d07a07225002150a8455100d0748100304060265049030580203446070a40315413504e100301c8c0e0040c02260042c000010402240350304040c0c0041c624220384801080391001b1000c1d82c1c4401045034111000e81c1e00398025014040c0c1c810300603224108550003030454901d481d14039030000e403082c001c001003c54000c2d40410360b071101c1c40200c011039003081110804082c0e0380361a12403107241d0399075030300815001030034038000070340c0c0c101c26807003102d0103141d040d00100003c080c0c041c10080d03410711000a580410104000008254948506500c3c21030b1040000c02d0b01ca6040000d150211a03650f04494400d004001c51450581d8000040360419002c01001000e0340301404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 142308687 1250 142307437 142307443
    0x60d050603010b040e010b1002030a0804290109050702060903090d02150d020412140142080708160b04122111010b030705010e1002010e010204080a05210405040c02 72
    0x1200c030f590094100094018200d8040d446802d50b50f00c1240c0301e40c0c000000f004220b03500c1c081c0d44c1d101d030082220940824003103a01200c0b900700d90b42c01100f08602040c01c0c1802c406420400303030301c40d015094640090145071078050280a0380700d10307444000c5040042203000a00c0d002c0d00d1400281c02000c418140165265502e0100e035660703aa40c40c019075881d565032000340b00d422103041040d5114a0002086104010180221b00101c0c0c841d8440e1011100000c0440c4844103090b1113903541e4052449003641140d82c1d1044400091500e60301914805240490b158181a00000420103645c9005024000749040c80d007924180c8032106010b109961007403405000d81c0940c4464440c80c5081c0a10708a101c40e4842140c42c6020030400003802000191014160b441155014a03030100300d04201001560900d0045680002498400070a03104c0c681c100f090f003264080c1c0c05c001025048a20110b090040402000200082e0310300050501c050420707945186010794000c0303600ca2915110400402c5100b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 142309937 1250 142308687 142308701
    0x30a03022d0702090a0203060306040632100f03051908040b03040605060a08011a22050c0a26011e03051603050c010e0105120a180606091406060d05060301 68
    0x26030300824800e010780c400702010340150310103e2003031100e0000904890f0880c001d032030203114043e000300565142c59852101801d002c1b0407802c000004110740c26a0700200f103603031a000300802c1d069041c1d40e0030b20840d078070717414540354000f540039040200c41040010800039903151281d00c281910510507146203003003000c500c22640b101680030804007d000903c0380f02e0340002c0c0030f44400c58041d4000b9a581506d24240d41140303a205031483c441c1c080e54959420040500240114811420007060701e603140306800b183c2090350b203000064004074a40b00c110b42c10a0a075000d1415501942d0219001c0e09203010030850140504503007101101007030800b80740d80c1c19210010b95031000942d4401c0c030356030310009124200d0744010b035621700c80c1e1002c5100950003100e200840301c4069465900c0c020b4101400c800070f40700501501c14003583c401c001024565039440741d0580620a800114001d86009820070565106c1929440d035500c8504c103010f950750706c036804c0360040c0000e210301103034960783c4000190040200c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 142311187 1250 142309937 142309987
    0x1603021c08030c03070f030c020607080414011505100c170a0933030b01090e100b0f0c2404061a0406060f1e051e090303130e0f0405030a0302 62
    0x441806920b50601002c4c520904180e070710981c011080d000201e00340c0c3c4540c60703a1005600030f400400d076098480c101c501e6010713000e41c1e5810a2014280a0f03030b42103030504d0441c500c1045201d84184001e140c0201c1d800d40b0049030b0b06d41200e42d01101d0b00c2c0c40791846a01c20320b20203031100004900148138020000d400c010030700d800c004074030420f0081e55070039400e03181c8105240000303500040303481490280c800c0d00b5000710103941e047c40b19804c0c40004031482d0b002400c1021409400c0350005030a40c0120005c140600700500c0181d16002c03d40c400d80c1c0303098110410800c0d0034480411904860320f0094101d513100390480004500450b10207444004200506401a003040c01d00c000402c1050300941c001c0b0119007030b9034424907580122800444142c0310f852440000450030014019010401c100c110090000c0d03c49040c41c01108500003441c0d13501000e141941c804040c0010009500105240f40e4010521034407a4101c0c40c00d6a10140c41344210b20144090541c041117506816603182c80c05c0202c1c100d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 142312437 1250 142311187 142311203
    0xa09080307080402030f0120070302120408070e090c03060a09060209100207061202131205071805040209010501020a120807170f040b070507080403170d1d07081603021c 74
    0xc0c07610340201042d0080781c042e8001d10441c0300c20400c0354014402c2000d82c110100140300c401c524015414900e41c0641e80560441c807802201c5a18180040000c1004040c80f80080503464601540003c11000c01085070750740307405c0b651801c40c2e240c4000c9542507014809500c00613903600c82c0e2400c40b000f806052041c542100c03c400300401400d4002810000741c409503141c40840c61a07032008101644039902c0c901c04001034503081040328202c10308804000ca44184143c528060311130301280f0000e074079101c541e08443d44a005103c113501700350958501400c0203202401c8020701c0b43d140c800b8030800007010401000000000100381130f114003034041c03c00120307a10103045810700c0440c5080816068405859840341d100200c0c040310302440444400302c1c1d01409030344c101403547e214400d060910002c0341691f000200a5008403140c03601c500b071455002442c2040401000045462900f03c0a8209030741650103c0e440c8007887d48907404060440707904a41c1d03408a40100e240708040700f9100003000740100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 142313687 1250 142312437 142312441
    0x2012f1b030c0c0405100501020c19030503031504060b040302100c020f1507050105060301061203080a0605040c020f0f0c06040e090f0a0c081b060406030b21010b0a090504020f090a090803 82
    0x7040b0741c0403c2c1d00840d418082078461044400743c808440c8030781405640b0280c4c42c2c4601e81480500380c002d80a0400150401ea652903c8150469000725000d02c07406c107107021510300a1400e03118950181c8041240c5500b014290b6002c5040240c03240c000c3d074140059590480d0456444802d05d940521340500400300c4c2825141500c42da036002403d0840d895401e00c4006027060130144903c10460b00720841c4160101e42944081e50903003000341c00905044e4840c1004030303c0e92540d00a0307515920007a401080c10710f4040c6c0c00d1600b442d00c00c2582080c2500882d41e100c8285e03503110142d0b0240d402e01c0598440175112000028070b0b0032070600020180d801061500e00500840b800a031040725007031010f96085800321840c04140818005e80b0550240d8240014042c45c7d119030b100c06c8000d0700141086080101580480d08441140e180041d0035170f4440300c502505003080140240145100b80c2e090140381000d60014686a02030440c8a0017080ea00001035002c403c00c1e005141079981007285140e07a4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 142314937 1250 142313687 142313707
    0xb03010603060e010204030c0510050304021903060606050306030d09140f01230301080d030203070f031d060a0c020d030504080703051606090609020405130b0105190915050102012f1b03 81
    0x170350003e200607a11030034030714000620303801d0140d201d036000c4d007041d920180345a6482e4208100401c10242d1411b5a6042140210009100d8401c00c00548110344695840e864120109441c005803008810304209810300c0030088080410190303180b0000441e22504450343c4440103c078000d101000c44000034907408550b03201568880000e6060b240c1c400151108404000800d43c142c3c8001c1d145e820005414a40307a9500354481c0d400304141c4100b0213010203007009201110b500d040426107140003040e646500300c201054040003150801c030041c0c24180300c035207003548034126203000702c41014081c00f10001e021010203e1402c1c4405605501600802c50300245e414620000c0c800030100b28002e60cd01404a04800303105142404580e40c8a68000b4940c1c0c01e1005124004803800b06210203010074840205454405000340d94400c0541040c0e100454600740c0020300303440d0114071002024894181a4400a1081c01400c182601283c0c2003692020580c005e021254000c0d0030032040c0d8000800d1300002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 142316187 1250 142314937 142314941
    0x1415010f051807020a060b0f10080f07030c020a14030408030403050f01060f140f040e0109050f120a2307061404060507050315010e030307060c0c120f120b03010603060e01 75
    0x15240203031001c41442e010340644080c5560103031084005a480882208000f44c01c0350011a891074000d003540c0444040034012076000701a010500f0082041c007400c0002d104500b10030150b004400c1d1405000d0841c01c040060b4031103102c440054915680000c40b010019410811603008080000407250f40350b43d40d041c8240c507140d20943d240ca855082080002d00032144c0f5500005640e141048040500e09000030001e400848080c0c5c5e03500203840790008280c455081c0702d100141c13030040c4003601d5611980b000c02c5040280050705900d543c0f4003440aa0b4403140e02c00d001c0b260584560915846041420395011140d015003a801080c080c100b004244a8452030381c00300780500c0c0710f030006100c151540c1d0002d903081e00080304e5250780400d60500040302c035842008959910358024044e41d01c1c150450315a0010346183c9040b02022070511600c51080115181c820004e40c2d40f80c0c40d001c411107050340c1c0010b100c01700141042c8051520b502d10080d03265002e40c0700c040195444141041002d510f0b50340180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 142317437 1250 142316187 142316189
    0x601080d090b2710051206030a0b131403030a020703110f030d110915070311010507050403060c050c010e070f05030f0a0b041a0705180102010e0a1415010f 68
    0x1894050032010110840c02005040c050768442c070039a609164041c92a0551440303400f0352240091010301a601890b1504c020701400ca12580d80c07082c0d522000c80101e40003c801c040d10b130328002c0c0d003c610300d0720201d081e031940260003071450f444141040e503650a0034459000080e020740000c0c000081401580c1480b98020081030b41700e900c0d80300d080b0b20180d09207620f500304110342c0c10081d0010170a6002c490890790155070b00d0682280703032a040411410102c0e51020413a0b601c4641b02d80700250040c207241d04400c80700000380030b1074024452494247d10040540c0918071005000703030b0b200c80d510030f0914000c030141e03299505803400800c82603403400c03c520354500040c13107000c2c24181480c20200e5039040c007081c281400301c1e03410020800d0809036900c685032040010425a8090380c0400316210800081502070700454041e0745840d200c5440e031f500b043c510207842c403066055a240003240701745e91034003282080d400f035000540d400c03d203c1086810f80c18a2207000d2507400701d024500011800c1c1c208109818 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 142318687 1250 142317437 142317449
    0x10e06010809010504020f040510090609020d060b160b0601090305060f010f14010206010b03150d0b100f0e15030309060705060f0117190c030c0909060e0106051804061401080601 78
    0xc0381c1e442c0c1c04111400c82e101641e010750003080d401855811420306400068006201da040010202d41d00d44d2064101d80c0306800641c682500080e122407040003038024a0050296514a41d14001f2100c07011080800e0850b402003481d071891001907a40e070301540c00d0000558016094a00c2443e01c60f031024244142400340c2130515130700031004103400b017a01c92614100139041c0c004041a0b400c1103856841c94000400e0f0800c98441104610041c3d1111031940000c60711440f9000400d0800b03080511004200740c03c40601c41e0920202040141000d488054110b6041141c24902118110100b0b00b544208050203412034070000346407081050010b4807a00c40d2001d00c00b4900300f80d803a8043e1039000981c0544c12502c99100006440d5043c10b00f00c510f2004a101d4900910758a90f6550342031541300a81c1d02280700941e45040000a2280344c0c002c110320a10100001c0100c81c1c10070b000601c80d42400c021071500441d1503800181001802e5025020000840d501030303a4940e95800074070350700d6400340949 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 142319937 1250 142318687 142318697
    0x7060201020f0715060f0303020a05060601050901050906130b031006030e06040201020a02191802300a0207020f150405030f210a021e100c0c050d08060a0e010e0601 72
    0x11064418400d40703004034100a8640c0c42c000c07941d01c528212030b09030074050206590712400014611174050f40e130401503100390082d041500071402c04034200b540051015052080821840c1010b0380d21201700c5011500c21180700f501c0f16040300e00152841e00d642c10080c1c010070000300f4859440d603038140482c22255a564140303e41c8091444030342d10341c20241c40c0240941e020004a500624107094888800900d102010040c5030703030340140c8200380c107900c401f207012a94001510b03880050b440081070082003829040c00d1254004007200400d104004002c005107907408130f01441195100c0003017803400000240035200c0400003e8040c0015400341c403c0758030074030030401e80c95019035000c101e0250896002c0f04401141d07070004031170703151644200a0036045002c1c0180c014806202201011440c0d040c5030009d0802800000d400011124141842410310003451010030000d00000b45c200e0242d601460226102c0d110580072070036855054000089803456040080b41c2006006219446414243d0707070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 142321187 1250 142319937 142319939
    0xb0109030803010b03041e20060a09061d03070f0e0f0103051504030509030f0d090f0308030105100302070b07050a090b121b1b030403020a1a0d0c02010f1d07 69
    0x5450910880c40010644102840100511520340c805168442c1c0120346400c891182000ba160185000000c1260207000c80707481500800c1002c46841c100640640f82d40e1314050a81d400a00003655600c136500410045911046c03001e001c00c40c2e007482d100f001404452805032140300c0c0043c0d01c01c150003071060100c40900001d40c022174180311b090490f40c01001800c0a58030b190b2405010200c01481901400004c0040e1002c0fa2420056400d07003d4140018007515a001080103043c000340354083c1d08200c081240c01d002103403c0008990450304105c1d00403c071451a040107a01a0190081c05841c1c0c0d0041000c012000350054001d0102c0c030070595400c1401c2d41c03248600903181c0195684e40c0555500c80c030000d90070201c2848141c0703115440702d10885c00e00113121455805030030010703030a6919820200342001181840902c45010b0114244108134180c03524400000900035448020704241c1c581000800080c003e60281c10520940c21050060f15143c401d0035200004c12a0408240d10130514 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 142322437 1250 142321187 142321189
    0x301080f16090e03040e13060c110709050405070b040e07030f1103010b091207140108061f0807090807060c02030d0c0b0711120c010506100e0a0501050703030e0a03020c040b 76
    0x114a00ca1036841c540504849040c280b002004020741d020b5203182d4070040002150f0100100a024071522400300091894001c0c0d20740030b0195086c100300e6005010480350f00100b001d04c0803c40d0300581e07040324400191070740c5a003030035840c0007c5c1c1e900444842c400000e01042d04160154114481c4030141c40500842e81001e181404032008520401803c00080c0018010b00b485000140b80c1000020240c0900642d8000701e81c0c00c1c09445c0d030100300c1c0c690b0300c0900c00c021035800c81440e5a10180484002c05240300c06406580c1003a00240d14504001c0c12800242030f0500500d200301c081c0a0300c40072104240d8403000041e01686450704240d100384560310914050a205d480e9003000281d10020110454455410540b02500d8000c0740710741c28029a2000380d01010200040d1000e00d4429002045504200c014030407500d03440004002080301400200405840380e042074002c0351820300c5c056640e950036040031070007064441d8010580380107800e0407038203051b8009601040110700b1070f400c03c41658020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 142323687 1250 142322437 142322443
    0x60806090f03070b0c0c0106090b031501050603180f0a0f0308010510020c010e1c0606050411031003020607021c1101080106111009030c0503040b03040b0a05060609040b01021207080301080f 83
    0x1810340c0078503500070080b00c40050360400099801483c461150317414a8140c50802d4251071ba5034004010b038503501c038001ca8640c5020041e5002005c04c00e5252400e03941024045172a51000810074a03d2075003010240c038040c1010001100503510010550709501700c1c034580060040e1103010300342e00248000300042068a001001901d402005800038098610b03844015100b00010700c103066800303400d5101c40c6280703150b040e1200310164400e010005400d801c1404000460340051009a142181402000408541301c2000c0041c2c940403514140c441c40c06100040000444c1540f4900412681c5c1d284000c100694070100d051030b0003620b4624550380c0383c030012600384049041041d82540070801c4540c601c4110b50060b0f90f507600074a84000c50780800d0b1200c3e8a503600c01d038820344050701d00104010500c00506c0c807036900258558818012400e0400000d00140212031800384126956500d41301240c1c0204140c4070709031110585a901d0700528100420b450b0002d10440610380101380b18002000404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 142324937 1250 142323687 142323703
    0x8210906030402010e0f0301110c0d02030901020a0609060b1f17061008131202030309010f0902060a0e040f0f021305040e0307030c0c1e03150606051801090902030a06080609 76
    0x580441d0940d9620340045440d13240603264207411500e0b8440090460300c0a004041c881c41004800302c0c0d558910b540706601e0207034851802c0b000c5410038403400026a07030200d4004001e542164000c43d0340507140c00c00e4002403191454455001d008455849035002800722031040da62480d49034600140c00b014040d010514003155142d5111030420340000c2801e00a00103c3e40118591003482e80004540e40c842c50b0604c070002d5901c0c09603001008224403041e0034007682c9400c5140c0b80051200030925804540c0754060b000c1403d0900141c4140c502d0030f41c44a42c46190030080307501c000c0c03042c0d09804030850005c1d480a102820300ca9003151011455051500950800800d030317174011407428415480465810780310000c100d03199428a2000128440c20701100b4078098031440001014525500d081031030003140409449255003000010040c054010044d1b4140300303038442c8074000c0e0880d10401264070420036005590200d10220901044c145140d1080c0c0a4030180d40464800e501d03001e030a80d0740e41c0d40e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 142326187 1250 142324937 142324939
    0x6040f1e0308031303050d06030506010e010b1207030903020c0301060b030105040b0303070503032e03051507020d0e2407060204050f0d150207060b180907090603020109141801082109 80
    0x10030408201441004180395a005011b49011400c020110941c1419144254410748035a4805401400120382c5400c0b194010054526120300e8000b140c0c0c0c20402c141d0f0010064028560380b1030000051600030700c41c0060b0351000600801501e5100c00c100b401d00e40003805143c1c00380386001e0710014a4100041161803940d0414000d608513904d5203219130000d40ca13044480380440fa44c00c0104a03024500b4850000380d84600084c2c41c06002d400c00b00100500b0040440086620084031083c036030741c1280d405201d803041a140e000d03604518072009006060403014840000d4000121001408a0b0b680680140c0c0e4086642c0301440c085002040241000d982000d4520a140b40c100d1019400c0b039801030040c10b10a810115a48411900080c8403c0851400150640741c00d82082420a42408501d01611419008100700350031500000d01507110360140f054000440300d8a07a02c04c0c1d0b00d85c40e40009600369071501c50b03d2076840703c51a90700c0e010112000c80702960075600d8451114120300a6480d1254 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 142327437 1250 142326187 142326203
    0x30f0204140d0204060510091e14090403020f030a0507110301050c04090b1f020d0201060e0c0d09080c01020423090106051603120c20030a09060807030b06040f1e03 72
    0x3070003040085108201c1d904a034045d9440c400010b03151907005400030402825190b4807842494621208002c1c40006805042112400d800340140746044118400c903030420f403608001a5524035050f0700e020010b00b07240305148004500300b00490f0b8014020106188a2a2011841014803043c5030a8035800d5030050f80c0300800b404113014160030b0354440400c04600800780c64610301100302c00a01c0006421071500160024140034092980902801000b80000c005050803898081ca42001d14002c4030401401107444d51541c0d414000c244055440b0106d0320002150f84542c3d4040e4000081c85242c5412804020b12000c02014501031001c103048a4140d22000d1400d030b40942c041d105030100c00021028040007501031546041288203c0504444a0b110115000064008051560556000f070603269204220031601c151b8042d48001c1180e040b811714002c181c65401c01a0060118042940d42080e00443d00041c1003e0b903800360804c4603445c822024856040d026006440343e99400060070741a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 142328687 1250 142327437 142327469
    0x8060111030d020415170c041203020c0918071e05061605060a0b040e0619020309070b030c28020d080910050408120601020d0207051507060e0607030f0204 68
    0x54051061942509100c00559241411000d0b0400403600700743c015412842980c04819a0036802c2083c0410504601c900e02c1460314110008403110720460007010103203484141d40c882054000c1058081101d401070250301c8034034091131880040c00c5141111180f030f11480000241d480c00d0290000450241030b00d060f03080384c1c1007000f4844945d000707034074580803d414107144d0004100c0c1400054082c59410002282d0b4038016810001641c02d040002d03516600103a040c4034883d6240307030b5915083c2c4006c003805070322540ca1100c42414103100703910541e00058000708005440403064010b00510003811902e0b0490004041c500a1240080e82d501c8003507441480f504074a54011840d083c2d02607a05000c85481540c0c2c0e0700d0002c195401503e0840b41e0103004a000ca0201c0001d213a003540c4044284002d10211000002c02540e612040c400c031402080e03480d13010728824007018110350b0300d40e800200601074100080300650341c80008942d102d000a01d403214400300c0c440980200c4040707480101407d00c0d00307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 142329937 1250 142328687 142328689
    0x240e130201140c0a060605041a090c09030304060e0103060f181a1c0b0a090c12110418020102070b040510030b0a030f030c0302070608040c090509010e070f031505070806 74
    0x284144000590510419420603088100d9400081099042c842e0103020710206a2520b80151a003075004944580d0502e0030495107140340c8a038101c01400101d425080b00c1c1c4590089407014400d2034003150b0540000140414516003103038052900c7c18007030380c1c10044070303544082c80003000e02c090280000d4203412544885070404150040b07d8412012507405d5002021080042c41c8101c0c1303031440510010780700d0020002d20080410b415030100a4440c248440f0610340c2d00c2d208085641e000c0c010400c211681d68400740041c181e10040d408d040908200240404e091f0003032583d0740080d1007280103110301080030070032850000c1540c040b10005400022903200c45001580585941280c035031308804000d40001c0442d07801b030002ca414900903100da10950506045c001c0c1080910340005050000f07403418800001d40c80e030200d8040360503494001035030f0f44444108070701403c80c2010b24500c1c0c0c861010701154411244148104480c07284580b1a4907135003900d609400d88a089402c070300071420542c001102 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 142331187 1250 142329937 142329961
    0x30408030a0207053f040b030105120f060a0902040b040605030d0507031806050406021203060114030403020102090a180609050609040b040c1208090f030a0f1709030a06240e 76
    0x800d4460700079100845852050b4204210040b02c01020300c40e916444071049403010140417400010402d02c5500d0a810003480f001684018070070b6901841d910805072a0b8042c0902000340484460340540d4641d0422807802030141407501c030180d1040340b41003010328191030648115002c40c2c01c050080c0c030781c80310070710410f48080c1c00907001502841015544034540031b040084040103050396844081c1c035581000002440c081d00c1c60045400c0100c10401e1102903070304421003522201221000c66aa907841d0b1400300e0182c042c46070520707006090824081003c21218482840507100171008001d50356851004506440e0150b0300c00ba002000f000c04100810201e0301299441801005000081584e80307100c284070001010064402403070126148a640c98070b41d42c59442c154040703006040f05019078480c0c2c1c0d041c0342a100010302e0195494110a44d045110094542119004081e06e00303244150425074040e202008288881c04039008140488510100c280700644040d1102c1c0344583d03441c4808640 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 142332437 1250 142331187 142331197
    0x905030a020a0902160803090a1b080309040c030b130c020f150c0a0905100203030a05060604061e0912030207030c060c120503090a0b090a1406091203060d0206040b120606030408030a02 81
    0x640c12400c4100c400b261b5984010b50140681100900d541e00890070700400d900081010130507110300e84d240c10481c2503030003c21f03501c0e918000c4a0000d0040104002500200303545851540c0113120761124581004496001b40301d401560740a03108814014000591104084100c010344145001c02180c03907640717140d0242c0340b107004905217410090b03151000a4016000d40300b10a00590002080221041540c002c40b5048401039500c0390403c0e041c03450191075500140da0451407440b007501640386c104d12035503d044c000c0039521520346041e1542c1c20b000303444070b815000c1691050b604000000d220742c40b5400c6101c6142d0400d0710700c0070014100c07600311290f510103480c14605202d80400203002c204e1036450716004185000c0108215015803078001521003090701c1c80103180d00440108030b150b180101d00c1e441514810005240c2ea81d40b841d0005000a4040e01e01a400c075002040104194840100406e10030700c10b600120740558942c010410300780700440b001030242c2001d102052245140d0380140c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 142333687 1250 142332437 142332457
    0x1116351b040b03060f01030501151202060d0b120312010f06050909070302071a0708060d0309061103040905040303060602190305070807060b220b0103141b0d05070f0905030a020a0902 80
    0x30444005540009140801c19181c000c2c0d0b5405c848010000c0103002d01ca05504180c0c0102d003501c0147c45d009200b10921060f07a0b02a000320000107890210b00c1c600c0c0c1c80110701c0c00005107907640d02a00c108000355070f0b802460388000001503000012076804038540219044461641d5800d1030b000d0003005001c420103015100806041c1c081c49500c00003a010314031401455402c41c82c3d44403d1402c80070081c0700d202c001d00054040c5404410302c0c00465400300d2114196109070410000448007804060328611655012000302c500d40014402050380c560800b0040340c50390750803100d50103c25681070140f071584000040125a0801207103000814440c0a41700d0749004890000c4d01182c0030340400c06141113840c000c40300000d0840c44811180d814803030120380071002c0c038040003504001d40b89081002c0e00a406810340c1c2c80c40000600d080c0110404848841610040901140c1488800a0401811004450b01060032488042107034240042d01014040d0010200d03000540b500d5440c80003503102102071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 142334937 1250 142333687 142333691
    0x7021605030a080c10110706050c18060a09030b090304030b0c0c0703060f02040909030f02011503020d0f0602130f14040e0d030504020a0f060c0b090606101116351b04 73
    0x41c000d920717441c4948244031405409940e45d903003d918191089840040c0025500c03001031186c50174418000070011078640301664503650702c064510040d14140c0711680020300122185040046170640803002e44201ca20071081807402e45c45500400074140900503805803650b0011001f00003150b42500281844220310340c0042c5015100d0070360505490442c9419004214042054681c03a582403141d000c008582c00c0844613410b003581d0005000f50040140508140804500d4a050003860350460b142240f42c5d035064101c280d5220500a0080c085202d526204503205421002a0505001c0d50402c0c0038070300041c150440b00c0c64000e800615025209980019070040041001d211070050716001c0c00036611088402082d520300301c010903400408075281c2d90400018041540c66800c142c0c42c00701c0050410440c212100610145004030401c881c100031041d0341c00000d021a810101d991503010841c04180f405040702945041d1041005240401d5901c00104888151001c1d201c01c0d0581c4001800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 142336187 1250 142334937 142334953
    0x3080618071d0307060e0603100512060912030f0105190902030106030b030601080309010903080a170406090308070207030308060d06020c011d0d0f050a21050c0307021605030a080c 79
    0x401600c14400719000c01c045040d592156100142d0346203900489802100200015402c3c03d100400034035070020100e009820204c0440c98550301c841d4210007030303e00030f4058460050121990f9564080558088056001e20388180400040840480384a1044e42410009a920745424803120840140c2207014035248070340c01084404003800110f0080845503404100790390420f041504000060340280f01540c4108500101640c20008903000c590308000d8164592890341d00689404c201110100c400309001c3c0104000c101c650f0344205100380c020380d00e6000c1903685c44000ea13500e2040d0b010180104002100290031480c1c031040c1d5454240c4140000340c108803402041900b5140742d5582e200241080080001082070300300b00c0c25000301142c0c42c1c4810031180d01c2a0107801485490074070420841540d1290030104100480500300700780c6810300b00011b2502c9016684584c1050f1000c10042c0980c0c4282c2010101504d516001d541c03009010388040d26880d52820380c40c1d0b10002060b6084e000e90700c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 142337437 1250 142336187 142336219
    0x8030901020c100c0905010e0a17100e010c08070e090406110702040f0509160f051e1f08010807030503122203050a17090303061e1315051c030806 64
    0x80c5400c002c00a4000b003680504c44801401900f25030700050704002201c040400c0360b5807142c00c13074421224091403c078219001170081d5800d0640b0007030141400d6043c540030013040350301544203910070701c2e9566910160f5107441e102107454a441d4030030168030a80d100042400b240c041d501202c0e03180c40c00c80c80d00b440c2400c0303540401c1c180c0d807520901c060071941d15401c00461030020b102a103295043c08010380100c9080a080c2030480245010b51409099401080e00c1d16010081e00040c045a0003440b4450f034210560302c090304030002c1840140054003035000098184400101c80d810303254414007031420145003010000c81c1840081016010390207020f08140b50412000716200c40724005c0c0d0301c03a56944110000a01080c005803a500341500e5290300300a0101c6022080d25048034048880c0c521001900a00ca1001c0c806105944d600201c0c00301140e51501142c1d00c10310001254803460740300243e480080052407940a8034180488290760f5000c00002e104004182d440030004082e12080c44005d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 142338687 1250 142337437 142337443
    0x121060f0f03020a0602150a0c02031b0c1e0f130f060609030303051006080f04020109150504090e0601050d14010f06060309050105180706050a09050d030e1003090f08030901020c 78
    0x1600c841d0600c00010301c20b100750704000c103401014203080c4c0020700c1c031102c10f201c1210070303818001c015182e16641ea082c0b000b03200d4802d2003100c1201109054249c55800944801a00c614240c0c212501c100311429510340c00c080000c1e0350050f05040182260401c0390980c0030300480c076014100c00d910b15a0740d050a05444034a034440c0c100a0070150307507a00d10050461501504441020344034404100304610200881603204403a19403008200e81c100e4507a4940c2e10043c0c4841442da049500040c101407090061356034000054000c13224174050a001d03021055846507102e10003070140640040035443c500d000704010800c0c550042650000000c1c403034511101e174030103c4030507401c00000240c4030318200c0c09000d024022140c2000c098000f04019441e2000e100307a54240c988a00401e005000c100202031500810040b4000c02c17000e010110664102c0c54000c00903a2411000c500c00e41d06108403000c0341e40b29101d10320441e90b200e90448031002c0191106a459000180081c00c10364003004141d010000034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 142339937 1250 142338687 142338689
    0x3150302061902060117060c0c0a0c060e18090706030203060307090203040302060402091f0509060102030714030d0e0607140d0902060a0806030f011406040c0c05031204051501050121060f 82
    0x140218049205103940b0082c1805030690000d00c4e1030b44082e1031045112808144903401404200c80c907559038013012207281c1840c0504001500e0031401e14000182d0380d420542c484074010046600c4c0745507603182d00c90301d42d03001e400b9611302011303030300c02c80060000c503000360300450708240c0040840b03180310f948214400070b03a481250304a00580009041c00304500301454403a4105168a983d02010305804444030503881c050b106a511415480000c83d5459000740220b510302504010440344100c041464250f40e5400400881d1100d403030101503003103a0b1004121039010703180076038031080050307120700c43c01c12140c010b400003488580c0d50b00440c00060b9504402000a400c2a840711900762405204060030040c500550460390790401c55501805021551003c0d88007200316800514503a80a40c1110412007581d001070940c400060070408091982406a111fa40700d07808807000641541c082000c0315200b072080c80d01240342c05a19800c0c05d9250652880b00e64141507001452542c1d13119801050107103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 142341187 1250 142339937 142339957
    0x16050c0a0303030f051b030406051911090906010503061008040203150a0b0f031b090c091020010606050304030c03021213062316080d0f020307020c0d02030303070315030206 76
    0x5261505044580300d805202e9011586805001c0a06e010030317540001840700a00c024031840d80d4000141e00c034010404174241092181d0410051041c025010740c05c3c60340401d090910510341540018080c0d0f2054040764400d46001d03009003221150341c41c00b070307881c1c0c800036208a80c94000c83c24082e0403480c02d16855882018502004501815804140007205107902000c3d8003c0e0025400229507405034803600c1c00f20390040e9003200080d6501c022540540c0160b0180300d5001080d0003000f02c40c070754840544c80000d80300c0d0300c141d448001c1004c9294201c800310b100d01c2c1c02240c0244000b6000c64000e6904102190080c0151582e8041c0b041c0c2010b241d0303026501303c001b40280b0b440c0503c03240e075003d6000c0b0020000c2c01c1c00700d002041c580c66420980d0060a50313100720819241031010030441c418084d10754888240506120a40c48841c5040194100f200c441c1f0051280d0b1924403407523740302d000000700e6a00600a5455a2103d80b070072009890403c06014151119440020068461000510f5078600c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 142342437 1250 142341187 142341191
    0x40528080a2106080705060c010f092904020915060702191a0408061303120c170606070b0f0a2019050403050d12091509060e1216050c0a030303 63
    0xb256281042600c03039032103001c440340d500c1d0200621890500045000950b136045508540310001103d91b5400f6041e00c442c0542d240742003010708020480d1402d440e100003e000391030000c94235a8401034625400046901039842846440071038042048412044e0211744c004d400c85180034941d1b004101408080d5049421030f484030007040040b000d000f0b4200ca4140d001d41c0c806881c082c82c00c1441580c3e0400034000714403a08900414504040c014401c5044688a130030050040d510b40880151561000b0956425060b40340c5000409915103081280d050660214040080d034440c603180e0422110010720201c28580e03162140c0b0071520b02e135685d000402e000c81d10103c0c0d45180c003920307172961411803191090034800140808e0000840218000c80c07080358903d004034a1481c480c4c4244040d20348901d01604040c45181d4801007180b0a8100c6500940170b01d800340448607070703404001c2e0f4514005400707148110060000440d500110104d01c00214000c00840b00740619020001e100e03881103900c01c0340400c1e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 142343687 1250 142342437 142342457
    0x7020f1c02040506030102070c0308130e15040b0f010c032a06091208130602070312090302010e0d0503060f041806110d1b0c031101060306060612050609040528080a 72
    0x80b4160140c15071110041c0d000398200002955002d9a05016000041690074080351805024500b00c0516005003114040b5036010304000d1190900d143c0d404120b140590b05051011116040940e0f500f2407886040e501c042e201081a1001c0391083c081c0103030102c2011a00011500d00011002600704036801000005201402e0f443c100080070070f10010801404a146e081041104042603c03a503a103410500c09a65030605180481d51160340701110584c103407a03d024042410360541c09040141d14030401c9900703241030700d40180c40c507020481c0c441e50f018114005102103414a50800d0f049030b00d102c034a2121741038059403030b50241ca07620711405d1051040440d00500003070550045400c03800000311546956450410001d049010464000d001e20031186402240382d03009500280065070860800c000c0c154954000905150000c110a01883d0134031002c03c10a01d040001b05008540c060000d140030800410403040c5156019080400d60142d00d101d100070840034001082404c4a0703035a8100e4031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 142344937 1250 142343687 142343689
    0x6070201060509090d0503180c030a030e010206070201111c02090306010b12010b0f0708071a0f0117030301050a050f031f0b040501092c070b040b09010306061103030c07020f1c02 78
    0x660700100201442c0c2d001c800c0c421070b071a1b000002c03680c201c2419002030700c0440041d001c40e45000004000d15425200b407aa1007000e056000c1c081c020212826820749119450740f000890a0b0349c2940154030181400304030849600106800c1c40660700b12040c009410110f15030002420300b00e0036400740c07081d5000064444030050a4100050151034515006401c140488600e00518014102d0041c003a82c4002036203401d10680104080540701401c0080c41c103441d00d800c1c0c0141c0c07054280304050350402c0c0d038182400e41c01400b000b42c03410b981c0c0107000300075800d04e020100240c0100c9045000d8050003441e0643c000707100c00c000b500601150703e03040850440804803c0c4400c8820581c402148249464281002d40925883c000464456511440c003500341e120b138880c0c10906558041c040071580000c000960886000c09810442801d8a04000040da10401544c6a10400c080c0300015041040054405030244024250441c005040d184481c1d03080c0c1f000c90f80200402a07a0188051269198411 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 142346187 1250 142344937 142344949
    0x60a0b010e01090f1e0305030c0a020a09090519060b03030406050703021b09040f0201090506210f0105090415021b0303040c06111509010207021c0308071706010309020307030203060702010605 84
    0x14280f900c414401e14040703500d807002015002e103500c1a10420000a03c0c04100103001018642050640342d803400e400c0b405c15130740c0a000f40308130701a80980c400080c0c019114072410311b500b50480702618440f286401e4200306411074541c00c0f03078181e0f942d144500745070320200060005800540c031400d0b03481c011420f000e86484000c0c0f42a580a00c51543c40d14040e48400c051503030026445212454003584c9440182c452031920f0304660381295020443c0007004419036501484944000800e2145071580080920708882c24000c4c660010b01c004007040000303002c0307a403e4510f5002001c0041c10181c8a00e034210b0541d0480107038094a40c8040309100c01c0c4125114200000d00b0f560908a00540c6442e9441e40c03180421404100c041c40404000703841c0b110300b0740460f10040e038014074481e00f00038403802c0800c2010881c40280c0001f5030031400610001c1c01904800c04a00181c1c49070010340e0385900046001c0c1c901040c0490301070041d44400030041c6c8041142c140a00859000030915030305041c14004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 142347437 1250 142346187 142346207
    0x20c07080a26040b0703201911090903030402090a180f060c0e0102073804061b02030c040903021005010303021b15070605061906090515030603070509090708060a0b01 73
    0x1070440b0b0410040001c0004141210b0209a2509291102000943c4038801c52840360380c20359503a0061513102007010050405151320f16110300c03200201c10002c1810700003030b8041110342c0030059104001107800b43c030300b05000c103500141840c1d000c03607078a2900c18010000e0509200480d03280c20039048880c20030006001d944009546460121180701c0a50b00003561180c45104401c040002c80c002e8989000c2103001000416a50520101e000121035014100c240d0080c4118000600101940110541e445249061103500203000b40510701c80b920803c001040204801c505510800c81c8504404490380075150086001e6005403001e000e620b07191810614030240c40c00d02c034910260212510301c0c0700d542500d00440e00f110002a196681c05c0205208016030074541c80005852140001ca141d80802c0d0f180c103446c2c055a0042545410385180f8442d4001902c2c01a811b802c03c3c001440142889011680d00c0000d17602226901d6a990022505100c0e0903650140c002d521201c61900a507003080d03081d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 142348687 1250 142347437 142347503
    0x5010b0109090912030c0e03060c04030201030605190b0d022503020c030a0c0b030a060b0f0a0306060903020d14160905060a080703030f0f02011d0c0a08010b0a09020c07080a 76
    0x1101d8410580d4a00c1480c0e81c064101e01c050555540000300018030803101f0b2005800301408440d0242031250207684c0d2500301d0700c01240080c1c1441c0d00810941440c6460420f058144079079103500504140da4035030590003c28029480c40c0d82403000914802d86603955560071103000b4149070301000141402420944400550350107540a240d44800052041314024201d1744841d02641d05d1742c50b030000000c094081544443c60311003010030380d8a00149500002e06000701c0507141048200d0ba03a00c0b0a0342d2007070b513910002c0d51052001711100f003c905040261305039104058180c4d45d9201c030101080c05070f99019007042000c290f50308100705542c1041754024000e8240700d40107203126072543d64000c01261695589600700072100d486840e00c10f000750019002c06448071700d1901d0f4030441190b12580e80309603d5030144214018840000c40640611944640420203464000041c3c1484082400b0350701050107400c203441540700000e44c02409204038509075200b25182c006189624504058081000c401d40c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 142349937 1250 142348687 142348691
    0x70b030c071118071107080a03050f1809010801060501020106120206031b070203010203160201050601031407050703090e0f192f0d0c0801081207050d111905010b010909 74
    0x400030900050080c0c6103055881046810302e03000a00c00b0032400060100070002016415040c0003202e608003084086001041040f0341590766a07065140d0b682e044d603640500032900800019901c00c914000a00486428588522500c644103004c1401070300240e00031122070b555070700d081c08503603420300802c0c0c02030980f00508104882c081c2c001a040384800b0b0003d0000744080580054000c0042d02629105900200210f48078a484070112a8030f184024800006510301800650590f00a1282c116117242d1180d480405985412080c0c0d41588010010b47c14404030410001d585c04025911130701c40c0604110034141414041112000502c4008031f14550398242651034600654020fa40004282d192013004181134140402041a10801352101641c0c0d003060310750040107130040d0f041812501520704603403000d08451580300d414001c00781e008243e50420082500721600c01c1c0300000c26500c2c0c10f000e585020070804060100300710042c004480694440342049203642c1c02003000401130145000c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 142351187 1250 142349937 142349941
    0x609140d02061b10021207030b01080915060102071208070203120316081e090703020a080d0509040e0106080304140906100c060e161205060a14040807020d0605010b0309070b03 77
    0x40003030081101d20303e40ca9403034241d070302c1c504182048101c50071301011500b1035840041340448400090100c031b90802090400301c95640f41c0d4400d00505106c0e28121026007134400240032484e08600c0042c198170b0462252000200f01048000444418a849094000d9550941e8414541008001119040305080034010046010420003000f8284041840c0111003603980c400000044091b451070b2b4003215028908000d41d000c0006010750a41340220707088619142e4406040307aa488030756a001c03000800c140642582820940c00c0042d40007810000840d002c1c1d1155042840d60300729910040002d0307500c1c62003102700c1c02c040b40840e42115040e583d43d540c00000c450080c103000900b51000f03203a282c1d9038400581c580d0040c404002c41c4041c0907080e815040e035a4244d959040d5040005481600540020901c1c062242c45000541000441c0082c0240d4582e1280001600000820b13600a005a03105000291035031051902a10103504116201d0a09903401840d0040b6904107a881ca402001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 142352437 1250 142351187 142351189
    0x2010e0304030303050405030f0d0c12021c0e030f0f281e030b0909010b030c030a03020a0b0405030f120a0b090108101e0501060c050607020a030f081509010609140d02 73
    0x881d01901d0700341c00d011400b511140ba0062861041c241105081c020210b01141c04444030f4005100e0108a40e44041307076100d42540003422441640c0d40c210640140400416042c50544c00034120340d04608280d81c01c0641c0100e010040782d00110030b0600341d080008100089407405c490701100403a600c1e0100130f05114044025040c061010281c008900d021000710749002d2003034105406a8801070910411410040e041c507010384200c0b040039209028540103800039090000b82c0840150f0146c1c000c1c146094645c840190002001d8400d0b60b050100f001240b16001d8100010310304c469800c0080002c0d40b40201c070350301c00c891480f00e080344038401a100401c60440300044106803900c40100001da0038101c0d001300c503400b03444418400c2615040000020f5a160080980014207014405a6909554a4400b26242c03074a8420040100b0115424030079030901c10301c0500e0b480b0b440d442030250340d001402d000031000d000980c030120005a5916092003010b02d04140303c510400c0944104600c4581c0768 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 142353687 1250 142352437 142352443
    0x70203060c030a0e0a05060a180c050906010212031e07032306010c06060305010f0b0312040e180a0c06020d09050303070f020303132c01140f010e1c060c02010e 70
    0xd810700c111103001102261020381c040d80030050fa01c12410031241e248600b8642552506000c1740c000e0b80c4589841040318444225908c1013545560180e552a92a41050308000010401901285c11481001d034410240700180c40214068149800d1004030500880031000140ca03004040f0f00406082c1001d010215010311001c0f0b0202004815aa05d00d03035640d030040311140c06148010f0889401d01c13900000b800740650100407624500401485500c10020070306a40e00203030b001201c3d441104020130000601c0d000940c41c1c01001ca100b580c803080d44140001c030324260101005540c072016003441080403507010882c5062204660825a062a06c0c05001a480c0c0c080c641c070140400c9480f240c0102150303420b00c2100c07010005580300b03110040e16038940d0945c40f01410031010b034030001440e0340250841100c0145049561030b440000d00c00b0054003c4c0180c40042e220b0881c181f2524640303145642d5162348501124010070b81000150400c5803d2810503030f29101c2c070400659241c080340303000009001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 142354937 1250 142353687 142353691
    0xe180103111f0309050c130209030c0414010303030207060615050306040b040c020a080f04170706110303131e020a14010306050420031801050703060311030d0504050f0102030409020706090c0b07020306 88
    0x290500083c3c00d21541049414041441b8182e9841840c841040e10180a50f034050214880250201c48075071010748180000c4424114a08800b081d042c401000024400d40007843c0c0d0300e00c01c5c0700205039a641c0340e00e0000c0110011550340d02040001c0100a01400c0c64402c004101004403400d001d03024981c0b001946510b840b00300940318007030024000c02c0d40c140c000115001469000c092541d120f048401143c0ca4809038003c20001410656107504041c000009036070040942c40c1c18035a040c010f0390b0b201300d442c80080411410300c09a00340010096900c400a4500801c5907001000504e140f100006049454941005224914000b100740d5682403403541840b842001e4040c2c1035407922451500541d4080550b40004158245420001034035410b0f0041422644100701101c15005075034109070302c0300c1c1c0140e20000082c03006d110411507840d201400107180341041c01502d180645a00b0b0717607000d0340d104402c00e0715604d0329108041c04000a100d5034034018108029824108600d81e40000e0b151140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 142356187 1250 142354937 142354999
    0x804020a14030a0c061e0804080901030504150f0b0f03060c0304020d0302030d0513140303070c080a0c0c0306061412060a0504140610060305070e011407030e18010311 73
    0x3246100480c1c80c1c074200306100e00301d6008981c03150a143d4805009040f2100d1407198a54130341041650182c1034050240700b40074a900803461401c01440d01c00440040c83c00600507070710398100c081d0380f000e107100e14444c102d000819014041044074005042c009000301e004501c0e802a0320410030081061689010399400c80d504840032070381001c40d03003001c9256009240e8895206890038050181700541c1508031001a0701c2180803a5140341c80300031894890104982c010085211103116800250203070f0010100710f0304a003043e01c00111640c5540314518400d400403660323103a44d0f480600c0581519034100c40080e1088810503034003150740c1c01e07050700c1d443d000c3c00794005140c40f0404501044840a0001440b000b488100e40051409610144c0c2c0002c2d41e105184c0800d15207008a0495031180c8001c0c00c1046e0180c441141d170410072101c169817076118803000d40822441018456883c0d40e00800c44500c0407114140c00c481e54154103100380200d80b44c1c0845031040100010300a02000225500800e29807 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 142357437 1250 142356187 142356209
    0x601080613050606090703091b08010b0d2109090c02010f0609060b0406110a15050609160c080f09030313060f020303040308010e07020f0d091a0307080408030c13030f0b070804020a 79
    0x111564190064207802100800b60220410701d0000d0449d0326004004607039021000340490b111120074000c0c804120b003006080444100e501c4844070810700880303071210149203001c0036403d540f424240c0c21030f132035203064034010703516584001180d8069005200207020b40310800c00085142041c428210f100300e10500041c00ba0101e030340d001681d010710454124a800c2a648007180c810404c00900424080351602c0c031992030701e0b0102e29041c4010b1220707942d0200d0740c1c071418060072240d1190b0740f040d080280d85c2d4071a040c0070044404241c03030510190490100392800c440d540360510070080c007041a1034a402c4210752007402084007081e404440d05044801818030117040d0348500d00c0882c00c00c08400c0340c0c00c80c14810401500e0045510004000850b990100407281145060b0b4924066200645200c130000b00d41101040c00704e5080700c000c5800c0010388003014a00045581c0d184201e010b10762059461403441c515500c14064041c070720680c03204007450505451b24040d40080c1005004c1d00682c3c0c1000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 142358687 1250 142357437 142357441
    0xc04050709060c2108060108100305100905030705070b040602070806060a09020c01090516090b06030412052101030c06030b040b0d06020906090901030b0702010c0507080301050108070c06090302060108061305060609 94
    0x101039a00964201200b4001e515601d0f500c01000e03141d100c040e19054001591400002c142c8041d12780c00303009070780d40070000e0041820b03c001d00320080d250000003554140030411001c4002001000951300a2410112980d240e526201d00070742442602d90000c2d02c07076003200e81000f03100c0c2c0d80c00c1101700c2900c1c3d40d441c005880b0030745803000c0d60041010b00ba00801510031944101c0000b080400740004450810900b44802d0502c8007d000c46400190340082c40101c04d40482140180900c014180c124142c02c19450640310807104511024000e9205940303c00701c8442c1404900c0d40360045640d94141030700c00f070121041c140081002d03d66800e1014060720307070114440046941d48412104208001821500c16584038102460999130a5864002641c030700718100d598140100d041c0c40070b07581c0007404c8505603071030f200040da10101c00900703060800c40645d040380b0005040d8454184058026070052070b00350b04102156103480b20140c100b4000ca03c09810340b80000b0000160103030f001d41e0660755036420b5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 142359937 1250 142358687 142358693
    0x1080a03120207151509060f1a0c030a08040b06040b03100c141803150f0c25060f0b0906031002090a12140c2e11031303050c04050709060c 61
    0x80c080c11900030324402c2e002111310141e0080d5005070942070703912072049442980d42c04900049400c10300c40c000442c0703003040c02040120023443c540c1140c80d0b52081c0f081d14005001407a141103501249800303012400840900043c0148040c00550065083c0e801708080b802400019a4030044d440640d183c07580c480082e003460522503c4400503000d9070131685a1901e542c1d030810200d0013030f001040d5009104003400c100c0f0725890215418040c8090600d0041e040e112155100d2544e8440c0c02c0f80413503540c03032882607a03d02032618080d04c0351500442c4005a840481c148410945205c041c40d9841960b40c641802420f80d404501018950a0305500503540d100c0b00300810201255039010700a540c00345480749050105141d10b030900c2c10f501d981950f1003140c08008001a1580300f81091544104544140070f901c410010905800481824840c0b0380711061154689194020728181412103d105410400c20070200440d00e95480211414015440c01c24001048154070740310710000c000c0d12324520018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 142361187 1250 142359937 142359941
    0x4090209040e01050c0c060f0106050715090203030304060218040c0f03150503060901150603020a090e040330060803070206070b0705070f081306210507030b06040f030605090601080a0312 82
    0x15007010b0b14002e004914240c1c400c082950800010904680612400224800901400351341a0340860700e40c6400c002007501d0304076485424010a01e0783e25a42c00406001d6038041015510071841980003607926441c0e01d41e00705c0e03e40440e1301000d0045042040302e0713920540024903d407040640d458001004001003103600086051a40450f4241c01844240454204103401035421080388540da420b40c05d6450354100e00301d224060741200010b12408091100c500c101c503600c1d80040c0a0b141034811414400888403003103002d5502090141101d41810024840c9402141c00404402c0c018606203615600071401c140f00d40200148020040e02c0002c0d240ea00903030507100210381101d940580c003611403a08542d542d00100d001e40203a20504000108079204646a102d400b0745600205400280b80710940003904000e070000041c0b60316800300c86107544802c0042c0004084011040c00c0c8a85181408412141c000d0002103041d04440c1c0148003100d4009040000d072585450718420f201c0b034031004440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 142362437 1250 142361187 142361201
    0x60906040b040b130518070f060507030908030a0906030501080a0b040803040215030a05010f151d01031d010f0b0d0807080a1b120f03020309150405010f09050604030908010603080409020904 83
    0x1c1c0c800e0003603084c4110707a445a8070851040104414100c034209890b021641d0340e0342d16100311400751901c01410f1000b01d2090020701141881f03810620300264903180c0903030464005144e03000c006002218108070179641750003a54014075010010740f001d0b11558441c0004030b0310080001d070510800002140c110b4a81c081802e4502c130003541e24a071a801c1c45002e50000d0710f420302c210451038404030008600c2d50100924903110580e02e46510b01940c4c0032000300ca03201c0303101360012814035517034019030140c0514002204054000c40000010b04c00c880484480440301c203102210302030421300c00c210000500c000d0882e8202c6400c101f2032615070b455280102ca076070030003c50304d03020040700301003000804c01c220024147c1c4007016120081000c00d506801c41c124001110308044030790240c001440480c07500c0c400c1035001401a000030808208102e4010141c2e03412031800c8500b179002c01d00304400e0560200e9406c0c09841240000d0040500d56240c110481c0558000c01151300d5000411400030381e101c0e80924 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 142363687 1250 142362437 142362439
    0x3090c010513080d09030605010f05010507150b0604080d14070201140706020f0409060311030606010f0309020a090507080907080102180105090d05010f0b2b080304050322060e0108060906040b040b 86
    0x60308481303880c5402003251030300d072200f100d400d41448000300b01d1242c0014400f042d9401030f9942c82c20042c00d600d680c01030b000035203280742000d0795400004104e80c80301c5004101501400004040c600301c68036000f07203050304038070500112900610601c1c1c0181e0307206210f02a0041c0c103d11080c0c8420250a020009104103060500d40c8100090b000030145026003003d01201e0143e0b26814480c0700341c07000d0580398a41120f505001940c103114440703c050096000344030300c0e0b002078501290f02e512007420008480b01500d5040c04684c1d020f0800c00080410084c003405407852000039400c0c50401d01c400701402c403a0082803070511101086003481340d11260126235205410200a03c004078440c02144020801e5103103540c02004500415040c1d00b18201c1200c00807101c1e10707001c59583d04680c641644640010f8410ac40034001002092641c0c060010840e0030004018171482c103180c80e00f0b80151404010a4606041c030502e4001c00c41503580d2414070a44c030a4042c1c40200b401003000b00028000d0509401725 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 142364937 1250 142363687 142363693
    0x30d020705010b010f030b090a1508030d0218030a0c03110d060f0b0406061d091503030406110d11061603060801110d0608060112081602100c0309060503090c01051308 73
    0x200309100e415044882402d400781c0b18010503020780d88080b0251101d500300c1607040700207503003c035102884681c000e4158030041030381494156251100340b402e503400400054180c940100701590141c00011401d0b1050004030700401c81c0c0001d559400a5446061101070103808021114541030f07180d0310020849241e012400f0080556400c00c0c2c2002040180c94440c017492031300d01d000c1001c0c1d001d4540305061425100000100e4801c40c4104250018000c10040138110708a5103254070b9101080900041c1000f0b484140320032000c101d9032882c150229402408014607107103400d9100c00041906e0b90421035a218860298400e684150081c02040e03022580070340c600f845280311040b0000203804113440581c418001c550355500019503529086c0190890044820001400100003000070b111884030030105403e071000540000700c4a01d1140c11031001b16006050f91000c0507404045500136000c00d080060441c00c2c0b803030345540d8485142c201d41c0d05204001510760b07004d85445944170020001c070303821 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 142366187 1250 142364937 142364947
    0x80f0d12110301150801080d120203090712080c12070c170705060a0504170a0c120311030d0c020609150c070609060608030a11070e06090c0c07030b06030d031517030d02 74
    0x200340105844c2c00300b4000034500c0700007140000010956004002d01380d82d4000c46c40c080b0b42c00001c025407010b4404400c6203d240400500c0a4814048031459401a110035881e42c041d0340405080c9100c018035160540800c104c010001110b5202107802d41d18021021403990780000c44140c034098040c4c03c9a50311040100d20207000721b9000c13004005441c41030310700703442110302f0b043c019681d51104080200041c1e1784640502068840d0f5024248040c00f83c54440440c2e8003c4401c0d90459115070a10310160f030b201c1c0080b813203141c1c04005e0b85420407002c2000301600c5c1080f5000c240d070000003614440303005000060307140c2440758070b411007805260031400030400c003940c2c0c44404d1740e00c4d40802d41d4900810740c004603205107101c2c082142c3c01100d4118802200301d80d2000c08000010800514691030141d0522440100301401c010a5000e0743c42415420010b00f031003000c05141c03100c0301000600b0541004441d000d00114040c4140403110340034078240348400500304803415805813017a040e410741c0c80425 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 142367437 1250 142366187 142366199
    0x30c041802070b0a0b1e0603010e0c0f0a020307031b0209040b0703020c010f1a03060906150d15061802070c050405180604030903020108010603020c0a020f010306050a030c0906080f0d12110301 84
    0xc02801182000c580b030401c01b2140b0b003280c000c040c4a51784140e5020506000403c035001035400388561100030840014030700030b03042c0101101900072a14810041e80042600020150800101c0351921528908858075000603400a80301c51b50082006020140b41404128028040e405903104404514000d02000b4600303600c000041110510440c00d000c0c4a003500b14040c100803d843e80200890806800303599100c0611180c46043c2180098004e5800c592500202d113a02c240207000f5500c3c071102281d0f480c90319170030f109102c030742d10400e601e0903104100744800910400700e40340884000740d0300804c00c0e50f50f070510104840b491034104003050185104002c01c02d944010300700c050724804d0700c40d842141d80700d4a04030228081e611348034440d40d102c03c5d0180058031703010307880b40c50403d0145404100c12351104041000d190040e4003c860010f40032009001c406900c0c0100c0010b401d0010040c0942c4250b0a08030b48d0307900000d42c90006101000d805811280040c0d00700e00866210b81000302c1c0d407565220 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 142368687 1250 142367437 142367441
    0x8040909060b0306060904230a060e0607080c090f042403050d18030209010315110c03040311040c0c08030910050c0a110706350103030507020a0902030c041802070b0a 73
    0x442c214400d010384000101d0074901100b8081c0200d40203910841c14440e003800c2130380344503a2010810f003244560442c500c001185805112400c00c07604010f40302606000c2005051410040d00c1310b401c3d50b6042c0301490058451420031071704c2039012100440c1980d03120288031450f008005400d00d60f00480c2c1d0010080c010009400381c4070448607a902000e50030084483c1580c80c840c1d010082d8064070b004010004680000c04e10103c800c8840300c00200900d501d044080ca41c1d224010040054002180810034400e101014041e4110140d405000da9801c81200816800944200511003140440460601e00c000c0003a84003200c88180c0030801400c100c10480082d800101c0b2420010304058050304200c203010606908a03080b54403052810700303500540c0c0c400341c1d25220324204101c0c19024410728100020f8950ac0c02180607840355551601e40c1d006101001c42940c128200b142c4c0100300744001c08480c1000c80d000c0f01c00140c1054a0b008070f0b54105c00184c4240b481c042e02c0d607148a0f040c0301c108107444d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 142369937 1250 142368687 142368701
    0x15051e0c0f1b0322050307030f110a0e01081e280602030406050415020a0f03050601050c070e0402010f020f0d030b0d0b0403081009060e1303020a0f050610060504140103090804090906 80
    0x100d104c004d0207001c5180050849000791034154126800410018108520341c420042c450714400d1040c80c17110010980708201c690000c05582e8040c0d00400641d5014010707400411140b40040d40201480c089881c0d98940406060000101714140c0005a0301c46901045000341d000d081503590b41024200880903001c140d4090380c812006a040b49045810f900c202d404220b1252a44071400b21680c0e01034008141c0103060505200c01000f0400344a0810b0020030050500c1e6542d00c8070508003400010302d6240c14030845c000b95805601c00e0a2840000114014140b117a071070007058440b0108042140708488c00401007450645c00d00b030204064020800d20f208411880d0303c8009030303590340060f4007603511a100e14603090480101084507001301c01c00310f10a00b03019004903014000d03141d4030380410164516090303a0035084403007800b1b10300642070540e0004040500c0d200342082d061040b00c0451200703058001c0c0c107042d80c89464000b00144502950000c0030079410800035075242d030800c40050929 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 142371187 1250 142369937 142369957
    0x8030405010218060a0e0d031e02060103060b0f0312030406090b0c0d0f0615030f0905071d0603071a071113060e0f04030c12020309040915051e0c0f1b03 67
    0x5114001049810301304c00b502c1d1079403019560ba200d401540c40c284006140500c80a5042250f00a110029070a160140c003009003144d9005103043c3d032540c03c0c1601121a5108900e2007900103140c0507045035000550200b0801e0002c40083ea0b80c0c0381c61401200400000e4030080030014a130007009810702500018001c2c070080d100c814400c2d03d40718940c140880d8041c1c012210342d902000c0c0f1100102c1d2180d80203621110090300005449070164031440c1c908451a4030440c50488c260081101c4980c54004160300007209400030525907040609001035490480c180591001c4045800c005108208004002da031401030b0071401d1104c00201d440000c2d1289000701da680c80c02c40c80210305004402d00059202d41c1d010355602e0160035040e51400d20913801c9000460844c4028040e046503541d45200702e40d0541e00c070f69600c0480884a83c1041d0594900804d103050400710b00958040010b1420361255002e44e18604c2c580e600c074200c2116003070034000c5141e1001070328003a002100d204a400401001e01141c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 142372437 1250 142371187 142371217
    0xc02040906091e2f1203091305040c05060c0a0204050106080a060f1404020915121602010504050d0f180902130506030108070902130b070c0e090c1e030703080304050102 74
    0x168500b401c425500c0120001040e2003480002048640070942403403511390000c8a042c000c2001110014052103550181d80500c2c0d0800105800189424101c081d1800d2000905000a29003600e404260304407a00c075050003010009800c2190b51000d01030300500c3c0764000d004000c0b03961105c0740140031481c202c0e03003041c0180c03030b19030003003000403003480300d08100d880186115061108100500010350050b443c074a422a50400b800350510440d00060f250926005070f003040c5914007034510071184200c0085503c19640b401c401c1c440843d00220b08205108514104560100081d5900701c1d6200c1c1c004048920003010f031000801c1d2074089070001c24159982200d040e030060344400405c0030340e03c828480d5400c1940410400c01021209402031300d007040c050002404001d41d6035a90104642c0b0600c41203508165520007804181e4100c0c940c140c10090400041102d00b03605408650021041074260410140e4a0114041c2c0c0da0100604000785030300004658413802e051800320b012f500300c45070a4281c05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 142373687 1250 142372437 142372463
    0x6070f08090c0a0506091f020307020a0e19090c0f090518010e100f0612150609020301050a230d05030307020f03131701091e0302070e010f030308070c0204090609 71
    0x420300040d20744110400420000c03042c0e00d01340400c51243d000a02c8a904044803c030b600c0c40c210706a2070014a0040c0b95000b8594940640c41085110703000c9400050b81c0048240900ca0004200c400c20540340703c1c0701000264a01d030b20f09040c01c080382e6039404200c80310260b40c0c0200710001c01e070300400e0044402c0c0b07484603460b0100b205514241c800401300d107140d03a4080c150700da00c0e14034143c109a49580a81c17a0001c5c000380c480806000c150705200b01580c8480c02d000c1040009040c1e40f10340f90040818150460440d4140000030b80a400740d0f01c41c90704031001449034260410183c442e0010004401492005000384500e04a030300d80c3c000300e030544050301410194560b02c00b00841220601d48000c002407160904101b1a042034240fa400c00ca5031030b41da120441ca001821045032681e43d01f00b2150b243e2801c1e0168030303009182040c1504003e180440200041066151000c10042030700c0e45801d01380e62030381e103a450495241a0f1104040e50260500c50701c1c205001141e448070a0a43c09003440c21014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 142374937 1250 142373687 142373701
    0x24090e090c01050307030605032e060501050306130204080a030e030f03090108390309010c020a050c040b06072907080403020a1b030b160305011203090303030c0e0306070f08 76
    0x104004403022000c541003501d071000c480d8880c1000350b030300211504002400a0729100401d160003511400300071000d00251001c0f4500b07002c034803034074900d4108020510a01c1d0800340003c1c4207010141880d405900c040d142e410000790190141d40c058054141120009445401c00138040038031403403100e001303020f000f61000c40000040b08490240006845044841d1203000d0700302030400884c6d04040c0b1283e9403a0b0001340074680f250829042080b04119580c90f0b0400001c01402c64042480d00000d65008594072000120041f0701e11f4a4018102c800040002030040451040e00c58014008c20600800713600074522404050600c0c0000185d04083d03256aa407020306071000401510040c01591213035000d400006c180f048410001c05104000a4809641c0c0d914911060016540b80310704c4020407200109455042c03040720f0051000c80c990211a03a01030314050b100400500009d82015281c40301414002d000703220140303001f000507089510501c1d184c04001d218100100840c00040c000d0004182d00c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 142376187 1250 142374937 142374959
    0x30301030b01031707080a0c060506011d0402071b060306030506070f0507021207051002010501090b0102030a0c0b0703090f03030b010e1e011b0803010602070806100b0409020904062409 81
    0x40e254469500300c4140d003180c5804040c0c005261212040e54820000d54000032404406040305c4c1d42e0540740e4011001541c601081585c900400e228100901c0800c0c5044540e820681c3c0003180c4419034005035203800e070b4200300c10031121003688000d0a00c0c5100001618582c0341d4420001c0307a0107039082d40c405898a0004545001c4410034460000b002030001501510301300070301c020680b035804200c0321707203030f40e02c0000c9125507040f5184040507135035500042140310411300502182140c24400386180c03081040010b44403285002c40a03006170050000240c07450700a5000c02c02c1729421103202141e900cbc00b071030010042c02142031520b000a0030218190042d0a00c0d90070321402d0072044020041a0700e407a0300440300c0a81541ca2446003151040700440402c028800460103044590f020b880300703d0070043c0003447d142c1c0c054030040c001c4071806010030020380600e054030199803004401503558103207000014040c0848d0b401c0120810008007284100b00d4515000c020700e4250f0f5112104242c0c0c4c1d40e2000c9403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 142377437 1250 142376187 142376189
    0xc080405160b0304021306180209040506042304050106050a180b010201110a0302180603130210080717040212060106090807060e060a0c0206120a0203041103060402030c10020a15150503030301 84
    0xe070020b8180041801842e1641c030480100f28100400a029a034402c0b9005144114501c0345108690010b9511003074100b901500c2e911001c1602c007440304920701d08401008040400c041942c1070710250200f400c02100b03401c076030000c0c08000c082c401c0880c1c0f00c1207100e02a031004141903504600e4110b21000c6940180200e074445441c1042700f80c107000e100703075064002c1d500c1040480d081081490030130b4016035640000c2d60003401503680c0542d03229000e03c1807001d40b0050407215007d0200342030802c100e60b5403080800080904140907a000c0b501c4a20104818655042001440b40241000803812b9540075440c0802c41c0c648004031503103d43d4031031058542100d00c556198100d04100400380401d40664410a0300030300c0035043c1440d00001029100082d2415241011403980010074442441000c440c14106907508130098070384c03400c0c00e41c0007955a140002c8a14080d0b604850742200c0ea600a1102d0070300300760401071401500c80017502440003400e2803110f099945a203680041050305000040d64 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 142378687 1250 142377437 142377449
    0x2060c0a050d210e0601180f020705100e1b1009030515090c060c060a020f091005090f040b060a1103090612011a040b160224070c080d021b060705010c08040516 70
    0x1500d03420f00e4514401c50700070301c02c283d1f0602e440c0c0205505514042c401001d00300e00a001404000850700810410b591000c00204c0e81030780700344094001d100491952107020741c000c03500d900004200340c005640040c07466001038014041e450400e40030a0001340300511131100c0205881d11003101d94204107aa02411f6408400c41e4043c0d070000e03101961941c020311880c107150040718146600f40307000a1000421000c580c0005001084003034035400e010020031620901220300340904c0740c1020200b041405459810300c00c1000950021400701000c1c41241c1c490f460243c019070b995000b110b0f011000d02d80a1152988180c1000701d0780c0e81955240044c5c40c02d44403c0341c0220b1034100208280c40580002000999000310940b50136105101c000ca000f494a100700d60b401b03611040d440c28160382c80f074242d61028000750801480d15008030750100380c02c400c0035139110b184000c13100c020300441c281e8090040b00520541c40c0040308d039041504440c00b1807003039205104a612030286401d2440c00d4220b14441e032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 142379937 1250 142378687 142378693
    0x30916060c020d2a030b0108010c0c080304030e04110711030f0a020907090e0703060602060a0603020102030a120902060c01050f09030406090522050a0204050112050105030a02060c0a050d210e 84
    0x50401854207001040f1524000c1c040034202d00504201240c50840c0d8070303900303845030328040d10800c20808941101401094208000c0209034030140001d84501c94114000705200c1c2c00200082c00c06008840c8000500005001040100e80f65082462650300061094030100407100115a0900d00001d0812001d9610750281440c03a106038244916002c0107840c803000c1c800840c402050210100880b60701c20001075034007040355850f095010b410441e0160000c04018140201800507076000000c40315482101d150821450030350005d40802030003c1840250701500008900d0361980054100078041c055910603660b03103880e40802d0030364034800e80c440c440104284c42d1040201d403400c11140d2010700712070700100300302c040e1084403501183e02c00c0f6003000b40c450340460244159603020803124200701d8518401c100550410001980d901c0d10900c0091240100040302d4020310b0060200c10403035035000e42107840700c9501002c0a0310140f034884034081c1c90b2001c0101c0c608a0a0306005000b1006445006 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 142381187 1250 142379937 142379957
    0x705150f0f070c090e0105040303060608060108070f0207090f0504030801120c0b0304020f030d0c03180e010e15120105010e150616111908010606020f1e0709060b03091606 75
    0xc41107290704030100944083c00d0040b070018020246000c1c400317004100c0400000c0d1850030f4900681250b0301a001180ac02030766004000c96070f6000718441d900300b040342c10041f100c000d0480e0304a07d03004303983d00417110303103420a004404401030a0b04510300441c86911050826030304c420b035540030740e0443c1c0f40103006480103207800c21042901000454109002402007070b0041c40346c4002ca490b001c9001141c00005401c40600401d05911140d0504400c01c0700a8159041d450071218010700c0d1818010601007103841d8000c80d40086040c241c2c11103004001c2d0a2111315022620200d0080c0800d20403260140441c0c00001c1590000390650404914001e00040c00d106403402c0c03d61614041c2602141d00700000410520a50b0f1249042007000c20b0034032030070140038103140030a07080d100c8540c480e03c1950700c407100003400300d0000b050020b8010002400002c0c4002003a28041c50b115041c2d001c081d80030310300030000c10650708a80046104081c00c20454900e0040c8030000c40150800c1c0c429840080c0c03210032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 142382437 1250 142381187 142381207
    0x40f0609050a020628030b0307030201110a0501052509030209070f09030c09231003170d060603020702030f0c060a050d02040b0a0c030f03050601020a12020f07080705150f 75
    0x1100c4044540100c04440c0111456408901d40b640045d80600c000b504100c1c0c0030843c1c401130480111010b000b40703800c2c03104031101c0c2c01182d038900c240d02000703050148032641c1103426582005091301041e0084020302a601b400c2902481420800050000d42e0a50701110700101d0700558550040700d901400c0241240d0b01c1280c111178001c4103018007820070604c0174000010801405180d0007412a03004001039000c0305805c141e0340400400e0b4007000001802d010030004420001e2042c04694004008003801d0032070219005e101c0c070445424049640c030709240400c046605038007a1408034404c1c2d0031244031082801c4910343d5008890000c560041d020424010203a200340c01501c0e036500034050141c101a10303001c0041c0e460b0004490000000c02000180c0241548050414100c903940c0c1401c01c8941031400c0000e4a4088400002d040c58510f00350442186201300009d010302e60304101a50308540d11a00300907103511903817044510030f10f01100c04010485040c412220000902c0e4003892070112801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 142383687 1250 142382437 142382441
    0x1030c0e060310060308031e150108070c06050103111810060e04020d060806040605061804061515080a0c050406020304090e0705060f040e07090503060a051f030506090601050405040f06 81
    0x3011541c142c003ca0342c1d0010b001c0c1040c001c0030042c1d4400c1038010349925090100f403116100e4a00100012141e140c20302540b17811309000e070344484d002843c00c880305695952090311007800c107100050495240000000c2030000141d00b050401d0720460706009826445c4021648200c0c1c152024840c081c6034000401a050051251021039480640094200f03007030f01080b0400c54000764001002900b1210801041000511500c0c0c0d01104c00c854050659011f034406401c000d5008100500d00750b540d810140825071284d941d00010109006403070100108000c00030140001a248080c0136800c1206000b40e85009805607000c2d507046500840c1481c0c070300441d0402620f02c41c11305019034042d5480101c2d240d21020000d1001e50442c00100f69100e18245089040320b41c014200001c0000585050100b50340200b1802d4220540d10000701d81d45d00c0701c2001200e50300400b031420900c00d0803407400008020004c291944515220420b0304c800c1d0f80e07500140310584200300d4005145900d0044440300044aa03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 142384937 1250 142383687 142383691
    0x170408120702120403051e01060608040816080408030d15290c030c060103030909060308030601030e0c09091b030c0d0803100f0f08010b01030b0108130302030702060a18060801030c0e 80
    0xc1d2040303483c41460743e525101c0c5541300d80c20070384480d00310000d903140c80b01c0c481c600e600380c0c404490020021503183c84002460140090401040ca0200040014820002d03040761400250080c00c120f544591311820f0315039030307031049429103203031800d000030f0400d42c0c01c0c000300b0b400865169103000341b121300d09031650b10340c40c1da0408403509480c10103004d24188150100003921720070b806040142050350440c10080c102400c241d00c10451242811800d000040f05e40c01503a0300040700b0308010270f05a188001050500000b6091260403040c200c08000c41c403500055404504842c11001c0d140321844142410385550b504400103411903080080c200002d548503004643c05000c60180d002480e440d400b0500190b2044c0d03016460180c030b40702c0203100049081c81109080b4500742420000c01024500292602000404600500520048260030f050003401159810741d4020501030707907101e2805015103c4100303038a1441070f07094407040c081a0307075004103203080c162034001c10103804151401070002c1c44d040c80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 142386187 1250 142384937 142384951
    0x330030b030c180105060d0e06010608040218070210050415051014190303050702011e0e01141315030605040203191103040f08070c12060c0315062001061d040317040812 74
    0x103150792340b00c5a440d05000c2e050291503c1d03683c081c00c60800b401041502c1d140400d042001c52000f205110000d9000214141e48003103440c0c0128243e90385041c2a070001131a2299004054100010402d0020100c1d285030141d90384840d054014400000501290751001c00401c0200c6001c0541403011902500142842501c1450403d01d84070b5414000c2480c80b48905003900441e04c850b280c503055680000000d0600084242082e080030b205602905030310920b40309042c0344401800b15145410300c203401100180c0f0000c8c00540d41ca040150488045500348100c0040303003031a20388000c041caa1150b080b68044c41e08800c0c2081d15402c282c0341c8801c2584018022112410040c0000540000c680c81201d141070141400003401c20300800c02600b0750f16000c680d00c45001d12070a060151540107441000d1003180401c003400b0001340005402d00422254101c18204840c0300080c0103100000000c9504c11482640c41c011030400342c400580307802d14140c4004004000c14008c0080c00b6000701c45217a80201 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 142387437 1250 142386187 142386191
    0x213050f0a080a0b090607030203041211010608070b03011e050307060503220803060307051005040b07060b0607050a05010c030203040c03080a020a0b180111070506010330030b030c180105060d 84
    0x703500c04600f450031001d0354040310140903c108200c1d0b00d81003800000e40c0150fa0b800d00394603600e417603520300c5200d03086800d490013030025211071459042c03000d40c0064041e01e03052003200c0206859040203a41a0024450071607503d00c480342962a18441c802c20904441002e0005d1221900300742080c0c0380364200030001007503503903020051046412619140c49410f40141c2c0c5403596030601e5402e06003045100d400bc103000b00700c82e21101034640d0f880f00c1260200c070200c0e0501c5d40c41e8007880ca810000b500341c0200e21541f000780400c90006200000c03542ca00890304c01c9000304019649910268141d01044401402c01125044d041012403400c034000c0020240b51310648484a86c1980c41c00c05200007510315a410040c08442c03106481400d115844414006500d200e040200541d00e2580d100e81c1404000c100306c22034126040d0401600196819140380d01c00683d100366205100180100313034146801d4824070801154507054148500c40c903404d01020802d440031603080409004072640600c0c0092040e82e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 142388687 1250 142387437 142387439
    0x130f08040f0303120c1b0201020f0703051e01052503020910080109060f050906040b270708070e030c0108060a0e01090f0b0102030a050703181203030e100213050f0a 72
    0xa041800800103000d03203100c0c5a0a007030443c00c005100c1400319801c8402107281c00003014410b41c0009008002c0c9607042040a184009440100d0801030100344075003a0b880380300000307c00c00c200815002c1c400042c6500c10a05200c001000d80c0c282c40b0241c0d035004c4c50021001d03050080908c107004511003c00181000f61500d040760780800d80c10400326100600144030300d001444444402e000c3c0900074040750104c18241c034180800151810300241c001c91142c7e948109401c1d682e00c40a20320a600101d402c800d0422031440140708a003400d04540000004800340001075603a07000c0d80340d00280303100240c010100d20b040e150040d120558083c000030b501c10304003a0005112203403160100d0180c540d030107010986d0f068880c0104280c0f400c1041d6070f810b5400602a01e03e0450f031100c16075005c6501464400082d101040380344030011010b8103c9003940b902c804c601c8040c182c0640040251480b007004540c140d80000340484c00700d0040d030742c980a043d0030a100030009032501404035010388900400750780317080d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 142389937 1250 142388687 142388693
    0xc090e0c070206190c05012f250305030f1605090409060b060d0905060f0106120b0609090a02121501021f0612150606090317071703011e0906030506130f 67
    0x313031031070401c0382d00158401d500e00c01040400e0003007001000809070480c05c1801d1900761180d0030410301f00b11100000d80890b00c000000e42458031201320590046214600b0240e500b00204107900465054407410403080c0855000254040d0740c5040080641d1050704140302801004083c1c50b064102b60ba039207454020b401115034400b802010701038240e01d800141d4007800d141081c105080181241010200b5500404c0902d0300202c0e07611110852502c0011803d10040c0052075074001c4580c2c15801c0400e4008018044c071581e13005112030085900c0d0703030718603070f07102c4481511a20301c50080701c2c01070f00040c080018107242c102c03007100810b01300e403030215541d0385504840410320452401650406021200d003050807070039108400c003412007860700e100c249096172182c1210619074800d0341c219200004403201407000c86200604640260f034440d03a13481d48d603450041a5907c4a00010440d81d83c1ca0100003110030040c802c0d4003c076584000944119921441503039040140d0150a5070503140b45a0100c1c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 142391187 1250 142389937 142389967
    0x30b040507083c0304060f02011104030c05030f010507020d0e01031b1e05031509040f0b0103111201090209130201050c010c03050f01051008010506030c070605040b09010c090e0c070206 81
    0x4207a440340c2c0b00c4900002c05902e00031040c4464641d0b0011466400742d00c00c481c01012041700c00b9540142440d0000003003070a0201d005104841143c580114040350110800c0b51401c070040441d0741c124100d82180c0815283c1a080320416039500000d40d00551020f500ca81c041d401440c01d00e00b050600161746005c041c400e44562005640680010382c10301100c1081c1c0d05181102e1050f807120740f03401c5041d481e01c040c40c00010300c130500030310b44901c81c2c1c140040c08208088178002c40280c1c0c0011a0040c9584d00d14021030034485443c0b8041c03188130510419001060144105120035030010800d0b0003d4650070042c2008200441c0103a0400c50b08000744805001d00b4050171a21011554000419103846040300d10b0500060704090300ca80c8000e030001e40b504e07a10240441c10f440c0c0454100790741c1c0d00d0f40ba180442921132984014030309030070319003044144000036060314030a00f44407000340010f40c8566801c50b2100bea50203032424080003a40030404594aa0001d0290701e0b02c060b00035440c06070f4408400b91 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 142392437 1250 142391187 142391203
    0x70210051e01030803100f14090c0c0f0a0b0106230a03020714030a030612020102031c020d0c0210060506030907030308070c390f06051812100e07050a030b04050708 72
    0x52184e03000024003030240f8984095400900610440f000d0342804e05019000461080003814420b407840d001148000238a60110307a15100b211040f6240c1844118555440d43c1901d00241d608002120000034013034020401d200100a83da6074940c01d0300094007941865801041028041540c00d00c440303400503580101e01600c400b00840150b84490600c80010280ca402e0f0708200382e081d42051401d030050341c0000c00d5500c40d40d0a01d0300803041002c6580000002e008805c5000d80d540d003440340201d030031a0089144084400b0205007803010b15124011b121440c03205448000ca150f0125000b0400300303101d0a5074540009032880e10010041540d00d41907805141500301e50b204034a00701c0003002c1c0c00d0300790705107401c0303040c1c50303803402140c54502034511440420300e225003410701c45d0001703c203030102050781e20380c10280308014144101e50034003a00482d500d1606a403511452403074201002084600010b19100301d850052100703402d1130030342c2d03900f00007500c01400845440c0704070100441d0040c02444048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 142393687 1250 142392437 142392443
    0x30f07051623010c030c0201120b0a060302040f290d0f020d0b09070c02030303061504050409050c09100b0906091207030503030610110703020f18070c02040605030303070210051e0103 80
    0x21194a440b1001454140c44030510381400301002c0c8003c002074000b42e45800b8250242405c607000003204007000084d000d80e01c14150301c88044c084c0032a21a80650242003070b111115840303512181c40321441200c584a00e04014104a40b0340381c102d289891a1005081c410380403d8046a00c02d01c2c040c40c482130703801c01c0702c00b0401302d0344414010b04581031440340c690f4401e0180c0707010030700102c4a40100340c403840040d10b00c17402982c20721591456912a003048900901014004000081c414100310f0b803125001d000e25442559002c0101d10b56041d03150590b0140d51602c40c20388e01c0d085d600010400c01c1c0e8080b881d03032500a500004108240d2800784900002140200040d5980f03280c072800700301052020000c41000d00c241020905074211001800205495042e00c0c0100740117203503800101ca82024506c0304c007000c00107004005980f0b60224078501001e200795014002d160300c91081503100c0c00112112001a4852240cc0d0081c1410ba0072440d0070040003400c4140c0740c1e12040e240c8400fa1002d800035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 142394937 1250 142393687 142393709
    0x7080303070923010930060509120c030301060f03290a0605132d140102060c07120f0318030306140d0b011e050d051e060108030f070516 60
    0x400c14990f07500c042240868442c050071480396603600002c2d003d52058025541201d15083e400b6a540e080c0c0d0b401c0c6103010b004603503140070304029072031301402030541154042010b015042c400ca6061200005642030080306c040514116828030701c2c202c980b603010110070f00c201034898a640c41070320032140c600c486000c01d6165030199007644000740041c01e08070780d0040040203420484920b2814282810794166050725a8000400c810640c03800280b041c1c40840120102c60090009040342c07800555200d028420b800f903581564444a00c200c0c03501036010701800c00c0c0d040451a1131083c0c820720a1514820349030400081c01d80d8a0141001000e03010941100800c3e85d811051040324241c46003081c0004085800c05c2141d80d0a6440000c06041840380a6061404c2109042c604e40c3c0c0640c0040600f0001e4644104014141052552484000d000640300020074100d034041c090007045041c16102c00c04021450845000782d03d402d10352100c0c00c04d031000c0c01200300c0c041e2020044080c2030001c00b01c100389 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 142396187 1250 142394937 142394939
    0x90c030406060e060d1e080f030405071d0a0507170106120f020f0f070c0506030a1b0915050f07080a02010c110a0b01030b04080918070e010c1e05070803030709 70
    0x1100c111401d81e00808024803000707003085a0781d80c2e85004160360300c6e4401c4510440d05040440e40055058249000b48500d0011544083c060030b00740c09544524000d80403201103903034402d1810942007903000d449081c00c00541c00501c0d141003e80009400416502e024001455021388014520b01c080c0c03c0303071000030803001d48040c884140d4011100000982c400440c07501c0c1c4c0304886810b42d80326040c98400c0c038003000305000c0103219a14518074001d00000d41080e64074600320040d84001e22160247c1d14544c680003400c010814461107035402554502c40c010000c4112207507094800350400d070030840020104020040005048001416148034990000315900c00800000751501000c1000002641c0c4207449000114885403d45070443e504400000e6070398640c0e050400c0c25110b0340041d02e40114014414002c014141d00310940729016650f24000743d0501140112280c8404407000360098070702c503449076a94440d540500300f4040c45182151032035941c1d01d010f181150011510744011441081b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 142397437 1250 142396187 142396193
    0x501050406080601260304081209011412190207061a150708040e0c04030602030702070609080111030105090a090b0c0c0d0305160f020102090402180a080c150d060302090c0304 77
    0x144102810700070b00500300c1517041440410004407620340d0541d594044040c1d09034090018001c6901603c5401c01b42c8004051300f40040c0c0c0b0990201940c0390004000041c0035031b10f10b1025094507000300d01ea01961f0901e84a0341c2800c2d0b0b0540c60343c07a41c0180584d0030005100000c0c00340c42011100c0c452000d19801041c0310000b080321810b147c4503032401c0300c0e42c10021a40002d11580880e003d994820f1403851658451150b903844d00d01583e080100454400028000e246030005641070881c0c1e03c0340c6e100451141ca96500c0ca00340c40e42d5480380791201c4001e00050006150a82c404c6610040900001500380034a0b1946104070200b40d42303508401c000010068409001480b40c0c030f01e888040d00702404035007801d031000d08080001240e03440400051074044915580b00b0b40440e610528020400c1d9200d11000f07402444280440301b0140c07145402c4e000005808802084603418a000100110b40c540c000c0c507000c0070964000d0840140e22940d5400110043c0d44404c4d00d14041c1c40104030b26501c03031409107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 142398687 1250 142397437 142397441
    0x91e011b080415050c070602030117010606020d1409060c030a08010929010e010c080414040f0501030503070803040804080a08180a24180b0a080c030f0a020f070f0605010504 76
    0x4014000c000c0d07079504020200c0c0c030a4900d0b415040e1200400a41907036100502941c0c2c1c0100f40c00286000e0000000142801e1518800340d00385001d0350003004401d91302c8600b40e90300c102c1842e440e404030740390100014204c1b076a10f01812409002902e400d241090080e5481d085034481000040400c901c80010311038903109118201030700001c0100d101e098429464201010480c00345068104501c0b890b03200511703440340109601142e40014415151502c4030302400d890342440c5110740c007a07031800808030061a1079015850480360000c0145142a2140c3c645c154150300042041d50108010000000c40a8040104900d428044d000d459200c24510b0001422061582c0e1268403550b0244018083e21794449600a109954848080e80400d0224415180010385c5080566580180000011148810002030002070501c1d03a5a46a40e500c0303003520025404156141203c4807820400130340c40c0c8825038002c202c000c4a4022250a11403503664030b80d44023600300030480d21070391150010892400c041c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 142399937 1250 142398687 142398731
    0x100606090608070903020f090402030c0d21032310080a0302160803031504020307090e01030c030218010608070e01030e06040c030605060a050f041505030f01020c07090b0d0b091e01 79
    0x54500401320074910380000c1c502e03a142002180c401c42201d00840c04566082000030340041001d4a41e6096801c1401c1050000c200702072002208a2a5246600c0c5548030741b03d084001d001035440c501292964030542e00c44400300416900146c4180f54000c501d00c3c408022198545110b6401042800d610f101000b41c100e0451b070081c0980e5005005200123102d055280404041c010360b1300585a81c2c40304e80c101e903039030700aa1000301114a0b8200110500c80918038510540303000380d940b040e607103041c00c49081702500e091162000141408000c514054850a42c070141054149004a0b44800d044982801e0040c1540c1c221805240400e041080001710302440c4e911440460744000c0107460300004c0b41d45c01c002c02d0a258030841d6189105050007a010000001a00021f02259030745044508418000d500c911180c01040c03041c4403001400d01c5c068015004c0ae2023001c4c0c100c03c905501642d03007c001c0c46019148120034010524881584a0130340329003080c3d01c01c20030010449a10b00c40d0350303818103880 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 142401187 1250 142399937 142399951
    0x120711150a0e010e04020d0603030503060306070903031b0c0e071e020d05040306180609030f03062304050a1b210504080906070f02030a08030103050c0d05060c0c100606090608 77
    0x40c400c460026402a1400c20820000c1c02c01c000c3c40c240c800d002071700911034905401c03010380c6040408402e066021000c1c51140784260f084841e0341c2c56050050702ca1651520000380080d56088503180306200c0f0901d026030442c42032491120581d1903546070f1200c0c20048034040000380d51500c0c0c03000006c4500f07408800c0b00c0c0f9a070001e0200400c10b240001d046204030301002d001c2c1c54480040d8050030300c10f118203440032a00180100306a0b0b000d40340083c07520210351074120000b03003001d01c0821440744c0b128014403108510b80e1840000b0703648e00305000c05001d00410401d00182c0d10903001444008542030b4150b41c0d440c99440d4442406034a0050002d4100c0c0408041058900806c01c4001010381c4111904020304031092916200300c3e142040c0984020305000f5007600450031641c0402c06803401843c1624800c0c0d0a039541007500c00c0621a200347d1a82000c0e02c0c5030301004c0420003203810300d001400c6d10031204095400c0c0d86001c0d8030100990341c1ea40c0c0094001a92450104000c82c0c1c007a08554211072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 142402437 1250 142401187 142401229
    0x804052401050d1401020d050601180509010905090f0a0c15020102040b03010b07051f05180c0306160306080a0b1e0c0702061c0905010902091501080414120711 70
    0x2600600c0540a0205010316802610303030003007403020b1040b451303050081822004000c4d0b598402c04240007010b0316042d240280402d20380042542c0c50b141d003d4801b42a101e019140c06400d03840e10f5a608003402c4080c0c0745640301d01809200c1480e0400920030b502c220341c0500040120507190211b20030040e540741c0781030301c11a4410712003485014041c5044074119048407600c55140c0e001414440e042010310284001281a00f801d40e040ca0f0300150130445c42045820108411943c03c504020344964540fa10b41d585500113100140203e10082e07a02c0102c2c54061800040041c0c442c94101e24040d05e44000340c404462000401c442c40f941078a40400340c51609012111a0515024808440c01002c42c020300c241c90228220310390b03c5015510720310ba4415200140b2030f80d041428290b008040d599016801003c0d8040015400c1c0000038141001c900c0c181c3d030300c4e000c55655440c0d00041064040142195018850200c0d100c2403c1401414400740907a0001c00c0c010a071800308140282c0a44040036809 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 142403687 1250 142402437 142402483
    0x90e10031110090e1803040f05030d050a020d08090c0418020f0d0506010b030a0f050a0f0605010504050f0d0501020904090b01060905010e0607030807031e09020103050a090c030f080c0607080405 85
    0x154000300710022503041290f01c001944841c1d0840b8034410315014945d038144000f10700001e4420f011000700d400c85c2c501b6801d54511481008040700d40740f080c210002c016901000440024038450a00d140d4011042002e69086100740c40014080e106200c0e0015040301e1044125015440c00e80d240d04404c00007290464007138a800e07038816490742d10520400458010110000f065052682c00240701444511420816881c000c04114020008840500402e41c074000b004269540514201d40c1510700082c078511150b0450300030040502d81004003251555001d1114000c55101d42c061041c0141c170079607450030258180440184290704a40c8110f040140c00304220629465100445048031380501c0d00e9002603858240076006401b0082e007540841242480f01945440c0a5100d244082d00c00d036018007132500c5000e424070030b80d083c518000c0c0c00c20150000410001e10200c01c9204c1442c0300302c2e156410000114241801d1900480d862804260103408000401c0401e004d80c400c003005480070f0b4140c0d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 142404937 1250 142403687 142403719
    0x4030c1202010b0405010e07111218030307020402160b0703050c07030e190807090b0405010b0a0804050a0c1508010815070f0203130914010501020703030203030f07090e100311 77
    0x10001000090001403140038602440c0e8801c1d0040800c407030010b0310074131403943e4030f80d2204250041100c1c06030001c3c0305803a00d4030500b8008110505500201c07100e05003002102051030f08561540c2d04056894801000450300584840c0040c00800d090072140c1545654581840196886c00405460825140004104506600c403098680380d41c0c05250004141e5943c0002c0b0790103c032601d281101002c044400098010030004412098070b81c0d1101c10f01c1400340703403410b00003529000e024069000a0501c941e50324244a040c003d0f901c507000e001250341c030307020503121b450144000e0f41000f164081c40c0000280350a030800c400394018100c440040c4a640c0d03000c0c00c0000340b40710242100c0700300241a0004e181041c400c00a130b910340b03201110901c400980d03074085403000307054450101113482a50300001515600100f0b581c01200d03015000303107281d42c0d03c1c40300080382c2540c0100f004090121800010590100c506046445a6014000c010004d030940c01e0440d051884e90900d54031407100c0310810140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 142406187 1250 142404937 142404947
    0xe100606020a0314091519030c0c150504031709010b0405060f09060d02060c010c09032603010e070311071203050a020306030a1103010f390f0e030f0f01020a03060e0403 74
    0xc4001070413140c4a1000030001b03014840104542c07000e090011440c5401e200101c03d1103160303440340da142004400c01240059808298000010344902840c19009c0d9200480d1f03000158842d101e460034071001a5078000003444040280c0b404100390795200c02d401250b042510400b03410000072640150415503a000095440d280100102d0145018020382c5046445803001d40b151015018000e200d4000d01ea0300040001c0081c0c0b0064441b030900c4a41c07281300741e210200310654443c01c4030030140796038281190528600c10141610003010740e03400500b80880a0207000d8140305120b18040814000d03c0403008050354400340c558505030b0f1040052001d20f82d00015903503c90b961290048941d0b610b5240080c1c0101240390b0500900743c18192408400a01d1440706071011200c80c40c4103c90b0340f000c2041b40b0b0400c0d1b02600c42c5000ca28004403004805000b8132811185440c02012260038a400e83d4007141412001c200a9000b690042084003103550075010b00d03006098064412506880c1c07c3d140145 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 142407437 1250 142406187 142406207
    0x150c09010e0301060305071202040b040204061b051207030801060237051002070503030714270d0f050105010602190203060c0a2c130b0d12030e010e100606020a03 71
    0x2040c00300d04100d102850b00d003900f00d00011900a029640c0311a5283d10b6982d607070070f000e0001c84c899860401000c080346041d109640036200300e99601c8881c6203c000c0245403d00b00500c3c1661240729003802c40c030144124500a0a8040c0b00e43d0350304005501d0143c0c068030b80b48080e0081d204964450380061003d100442e40c00350304840f03100e5070340d81d110650b04220782030241806940000c40d000041c10303000d220000000710b0040000365580341208065401804844c0111200e0b441c980720300702407007480510f25402208114100a01038180701e69a0350324a41400d1206400b203a259450b040100845a01403120104104011289110041050380001c2d261440140700800000c030110321001141c0c8036009440038074908144040c5540c0903070f0034156405002c00e80c6184140407154110030b0400340360080070050300740609450458119035980700311107481d16005604040c1c2d03801e07070084001004d000b1802450100342c040c15407450301000c04801e8411a0308100c0c25540142e00003400241e100c58000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 142408687 1250 142407437 142407439
    0x806090613050c0409020d150506120f18010203090d08060f0901150e060f03010510030e0312090313170f06010b030c030a090c030b18070f030b0606040e0103050708150c09 75
    0x102c40d5200b51003920309010316042600c000d03102003040c02c000051544889181c0440c030414009240d920307800c000c020f106a503c841180100350001c204050700b04c1e00c0c916001b006500251903201040d02d209404c80e002140d43d180c2135800452031402a42d0413621054220600340c80004401c04085c1c0480d031010418840c0c0b800110042c6078003c4854421304020b10140c01c01010399955100000303403d8983d4200380141449414a103110002c00da010f0f1264075500000c880c040d60401003540450f02d61001c00800c41061808100118941d0354a5054010003402035a4148101e0403503e2190501d8460342c50940440c6510100040c4802030854054139444041108096920340d1450740c0300e00a003d201c240181040940b24010003003200615929100b459914440002d1158145007c3e5a94181c0d21804d10341400da0710341800444c40c0078061643c02a0b000d801146416034500c8040d480003400d03401502c00350001101800058030511004000e4420800040800e00b0020000c1d501c0d4400c01e4811 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 142409937 1250 142408687 142408691
    0x20a0f260a053408070309121707031809020c071208040e041103010203040305030610020a080405010509010507020d060b010807111b0103091401150801050c090d050a05030a050a0806090613 83
    0x3241e0f000410b080c0c50801945143d64610001851900550540000c3c1003240442d81d4100080707032064011206100044d0050900f00d140020303903504010907801490243c0801110131481c140307031181b038940b000081008000040e514455001082e0a200c0c90750840500d00b00c3d40c03800c40740403680500c15242910140000e11003661164502441d482c900108125019400441040185600400a14402c400a550141d200001d00204a850b5164184001c116840a02050000d075100c1c00141c020484181000c91802d140d40e00022483c81032600c0c1200c2d4103480b000390441c2964824015a00f200399824202c40d4652606c4106440b0491000300e0707617248000c01c11104e41680300341c000f08140ca070040d0000c40292500300009020309030910301343c4030b0541071000004040b1014442c2c3d070310030f10340141e005041c81c0128003042104c403141c202c140d036144503041440740801c006100a1540c00c80d43e45405c1d40d40c540000307015100c400000c0256108007441401c11816880390104004054110440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 142411187 1250 142409937 142409977
    0x12020405060a120303060f06020604030c06050901061701020405040b0604080a150f020309012f1b0a0c0e060f060c0604020f010516150e01050106021c020a0f260a05 72
    0x4228864503980c4210003804202d00f4881c20305070107034040b40c1030742d1600040d0741c0340540f1800301f6a80c80c00c084d507000340000d440c024100041080e40c2e000c0d5410003c030100119013140d0303841d1113401c160303e4020840d40c41d075400070b01001185014896074003d40d4054404908003440c0508847d251440c0c0040030b45407200d0446800d21042c4182d10031441c481020b4011503e070300b0700c102294000c0500d4041055260401045a85203000c540d601c82c403c40d002d0640140f1b41083c0344004c9c1e0382a103402e4200006480b8102541c400140803018460280c90b1220b0603416030324189003007044151072811890f003c1d0008000f1a2400280425466441034041d19100300c900446401259148583c42c06c40c0090141c054003c01008481100c0b10b0b240c1007100c0d801e0102d00c0590807400e00f00e410030701c56200540d010b40410101c018400d08a01c070312010074019946d1a82c1c2e5a02d41c400001a068022258005800c08994070083c103580120810b10070014140d04102d03100704d01414511802070441d005807100e02c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 142412437 1250 142411187 142411189
    0x90503120604020f16060506150a03110c03210c21060f03030c0d0305060a150c0503130902030702192303091509030d0809030f030c0d06061e091202040506 68
    0x112542c410b11398145540c0c43c1345001d100e04e0702c600c0030f0304200c40f80303800c10b4003003941d07460941c0040211101c504440340ca070155103c0c0603001070500440c0d90100300000e000c05040742d0720070320107024095600c06000c45c04030760301c0a40958200008004c0000b4100074440e1108406503810341040c47c48810b203107034100d902c6007400a0300144801c036141d6407610000402c20444100400c086204e005680c4045c00551545c40800c800c4403406d0080302c410003201101c009602e845120008441030044041c0d91605076548000411203402d60019076142d5000006c1c8403450f9410408002d420142c400a042c10030040d41d1046035a03900c940b03e031140040303078648110101400740100e41042000600c01301034001d50b80726060507070b003101e10714601c28083c1c03000450800740140721151140d20050051403600d02c980407001c05036000a0300004039040c0500074400c0d001e43e40c2c400c03440035210685641d07102c541c1a140034165008003410100c104102e03e07078100105000c0f4108500850780c1140d01103000c1e0360b02d41c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 142413687 1250 142412437 142412441
    0x60215010b0d020f3703090503070602091801120c0b03040302060c130801063305031f120308040501051e0114180705070c0e0613050414070621090503120604 69
    0x1441c40d25103440c45071440c901c000d0404c814001c5d5a1507404025804103004407058040700c280e0400a46036800401c20f20000509540c02018041801088540c0145681080036045002604400c0c1c007605000c0514050020b0202c02c0402003108000d00341c914070f8280d030f000b07403a00c0c07004d40090f030f100d480070071500c0b955104040302c100609071440003044002d88d03921841d80e031500c0c08107100c0e400c4228841d40884000060114440300010b50f04e61900d5502e0702042e6501911240b0300990741c901146001003500c5641d0000d810b4050300036580d800b41820942400e500319500542501046080300e10075003001a0b54141c058111100c00222500301032440f4041440746e00d00e0f12007101c3c0c0482c108104202c0a0300640a0321080740500200161b850b02c0d040440a400c0094030040da001d012411a007040e01083c0e00b01c4c0394480d100e0340851694040307200c5154580f0100b5040240840c1200008443c2050800250b81600e51038080903c00c0b00b001d6225940c0300d104410907038105103880c10005a0742d4880d6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 142414937 1250 142413687 142413697
    0x8061c0303050c16050105010f5f3a06060e0108031305090c27061b060906060108040212070e130210170a23070504060215010b0d020f 59
    0x2886140c0c6882c001c40c1780c0745000300741c03d0092181500c890400030440c400000002c44640d00d15040c1035907969a41601c0300d25603101000d1501031100002d6002c0c428030784000ba07601d000340110407406c45842984003042150b91000810030404100d96110842818080100c003564207121540360320f16550703d060440c0503000a401c42030a04160308c0000400e040c00000502c1001410b03003c03800601c0d15003040203062a03003924860074000043c00102c0600b805a50729680028803502e03da034898620001242458015401a5500c7c858110505a90a80500489610040c0c04020340600d03d0f04100180aa180281019005004070305000505600400500006d01506442c006241c03401007010f030030003442140124040d80103801842c4030f40f40241401a1400c056000000305a40c40011007401003400803c0d4600e8000c110303804080e450205103005e80202002d83d82c044d626070038013001a1803c50010054012103403554010811881003a0a445503c0840c42026039642c40036100b0029a00075 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 142416187 1250 142414937 142414957
    0xb061c020c0a03020f0d03110301090506010c0501050a0f14010b0f070201090f180e030307090b0f07060f0906060e040f0303021612090e0a06060203070b0702150109090308061c0303050c 81
    0x10300c2d9241d1040c1500010b11020107868101102d9142e0030f00d4030304130309131810302e400ca240c005001d0005211407035003508141c4d031014040c0340c600d824200c907403685400c1d60b10a0707860807241c0c0e80e1a801c100742d100c410700800d8420504100200c070654034202520704140b003800c5200c4900710010540008684c4110641d02c01031681c40c2031001d401342c903486410300c0984d42d840321800c0140751442440102402005aa20032440d035100c8901d10307490101c0e40e001580c0248140110124100090000144180b0481404503d40d24000800403031602c0c2c104206c0d18142c1081c0c0ca84101007040100107005d84440d0000203070700d40b40160301c9803410720f4101405600c20308010100b0117803102d88403119074800a001e00300d40c405050007010380c50306007001c2c0840361380f8000c1100580041001002040185282c84d420613014412210350140c100050300304c0c0582070304860241d40e2107052090501d40c4c405003083e04036204680100861089601100044400c0c090003001e1503114000112510b00ca04259220641 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 142417437 1250 142416187 142416193
    0x6020a02030703060b120f010b130603030e090a0f020c03090f010201060302031905010b0a0b0901030b0108010f0504020708090a061106010f2106140901020726250c0f060806040b061c020c 82
    0x4200002c42e000c0d202704601c05006220301d071010800038106004960840ba0151a2107c1400281c0180100010002d0000c40540c1d110b05404070704002d5031005250000e8404050b40e1184004810021000901400c150441e070400c0820301c0035a070041051114400c50548405d5054140d11784140500146000d0581c44040d240d800140300e0340180060172040400d03a0100700340c0a14500644911000303006681e0607a010802c144018141540180209401203d2751814500800c001034010740c1c442c2c000d6000a002e00d80a0280f04c0010000785015292010340d6150450414485110302281091fa60042000c3c00188605011159018124005d84961010324525000c0308586c041d60200b00f0849604000d21500e021030b100f004200040c0c2c0b045e002c0000d2514084005905240004074009900108207030f101e6000214541031000003442d407682910300302490200b01614104008281c54040d505090035003103d0b070f03590300c201e610701407030b02440302004030f000c0582038000e011741700820100d88 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 142418687 1250 142417437 142417453
    0xf0f09091401050103180b06281212032906071a06030c0a0810020a090e0708010f12150c0507020d0501050612120405010c030e0d11030706020a02030703060b12 70
    0x103000456402c2c1a81c500b070b2810301c140002030124044000c6292000b030700707000f1420040343c41407801d04011103200413518800e036050b07094202c481480e80200e60043d1880500c00070300b43d00300303e40c5031803407035440c1000e00f0b0412031000c10800c0940c003824000018000744401d504218955912101943c0503e07402030030a001404000f0f8010b81c1d01a01601c6582c071034800d80c1c503030000c82d02d002d0b050303074040c0c0d1600c0028004240035150150060b410200004007070145a000100d0585c51100c40a44203030b449035500601549064664442c54640750070525400030700702610710208501c46509004602c2620340040c0c1804c0c2c01c0b108851342d020321140298460403031030300c0b2800d0100540145000f141c08940072440321050f40d502c0d5990304500003034900f409001348010443c42d0b0141d403591030744a00904210b0441040f0200086140444050481c0d0849178105141b4060030104455000741c400c0c0d0004084003989500082d60f501c6c0e161100038511364461091807401e0300d0b801b000c108403a0400c1d084074045 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 142419937 1250 142418687 142418711
    0x40b040212010c023714010b090403021f05040503031b0903120702090619031403040509070c05060f060102120309010e031303170f0301090f0e0f0106050a080d0f0f0909 74
    0x841c2509003d42d000e04521100396174a09000d120381c1c001c03d03a110082102900e01d40d66161420404c40130070710155580d100031031196240c0f0707000c01c1c0c4624421340c00741c8240c1e813050150000405403182d0307041c14140380500700000038000004481e00070055003070f45800c0325581c644030b41b030b0b47c403550410a0b01800303800d00c052800b0340e0110240c420b80c1d108554802c401d80c1c860051145414040d40000c8110215000c1000482c000c010210000707040304d8196450300f0340325000b241d81c1c0c020994450b00042d0000d1324000920400340b1016030816412142c030140c1c0d08050307000035581c9810082d600b0400d900000400d003101c00035888103150413850303805c3d00d8507156001d03603c01108002e84070588000d0b20041e100203500c0700a01c1110441c1d5100000b6605690134025140000d00100f0f854040b82e642d1200c05045560742048884903200d004000070540c18100f005004c00741400d03511071b51295000010303031941c05070405552480b80e401403508e07081d2910045000c4415583c50740c000c5030306904d0b2041c2d00d911 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 142421187 1250 142419937 142419943
    0x90405010b1c0c080f1f0f050c0306040b040c0f030e01060f260d120b0f0d05010c0906050c030904090521040f080a0209041e2306060306010e040b040212010c02 70
    0x545014090070444155a02c9100b41ca580d1781300d00e5002660000c080c203041c0032200008091606032540740c00101c946180c40200c00720b50b01039500680c0058007204000ca50b20309400303240380350361003603c0c18070600c0e01d0108040d00d800ca407080e0345018552503800d1065038803000d43c0a80c00601e00d480c9046240c540e1061080d698000148141c20303100c003440d000021960740041d1054100c150350b5500711001b8040b08889009080d51412942e00000311046580e0301d95619101d40f100c140114000201031500b541c020b000c8070a183e10410078440c080c0a03041c0989030220968018650070394011407010380307a00e4400d00301180250240e07007451000c8004007042c581940070304140c03800e018500002644808120750351b491001030095000600000003400100040d40601180500072000d082404280c0c0c0c03200001d0b0b00010500641400c407011700210840100401c5d6003115003036000d0003440d4103100e5504035410703004201410400500d0040340445d10382c004400000c04105000700025600721038020f403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 142422437 1250 142421187 142421239
    0x3190219030605030a08040902030c0409090c0810060612150b070b090106050d020d060c0908010f020310050909070306020c10020c0c030c01030203071725080a06090b0906090405010b 80
    0x2002030328041c008030f644d060015890701c1403500829014100f40c0340c82c00820207917100610001c02c2c80c0c81803000068064403405500740a5214003800c10340705042140d010710380086404c960000c541003040411005800c41c2c00b1000306045000c3c081101c0502d801da40b070b0000c0082d4441c210340000003980000384901b40703410354011045540240801940e82d81040015070386a2000b0354400c1c4001c110900080307403603100c040a40020300741191403c0c5d640e034945003121014521050384980010403c44101000c10f18680940f03404c60321003142d8140003420395a00d07007140c08020042035002840180c241c9081080f0306904d2103120342503603284c082450366a2184008080280680320f04060f0403190760203402640e00c030302c08940d651000a40d0b0750455224043c806030401284031480400c0302080304416440031078202c135a40381c005240c1410b9086008031040b50340f0100b4010f01e49441c101d40d80d601d648909410150032518242d01e502d4038100140100500c180072640031080d6400e42c249200d200c40c8041d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 142423687 1250 142422437 142422487
    0x2040b061e1309090b0609070e060c070305010615050f0d09021c12030e06060d1401020a030203180a110f0f040504031d09270f030a182702031902 64
    0xc102c16540c0e1403400f042d500f120200418a100000c009101170800a00c03040c0e00c03021070300d44003d0a500c0d000c08500c0c281e0201c030052255803c07512050042c0002405500e006004c0e40104102c1480140401800307401034041a150071000019003038440425a00111a03071900100781040d1602203245a045000c150720342181e00758002c0a44c462218001c0c4541c0c60551002c40c050042c5586041c2040b103078460450003203945443d0700f80c2618680c0000d01c05080c2c07410725a2030040e524180716031112202444a401e1554a6000710364a2000600f8072540e07041d0000242c6446940300441000100c60210351801380ba0824600400c000501d81c0c8807112040c0e03ca50246001004ca40b0f202c144803075100100c8040480064000c2c44e544500092a0f240496416440c2580c1100b40c1300c1c84034904586c0304071101400164180070034400040b251f480000101010061101d00c034000107105002c01d80c07440c03100e610f866400b1001500e162031145c0400b03c81c0c0d402038004c6654101c9500c0040d80c00340040c1ca40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 142424937 1250 142423687 142423717
    0xe01020a11010203130b06011205040f02090f0c2203050307050706090b07050309101407030206040201080a020a022505030709051509061f02010b101707080105010c02040b061e 77
    0x302490744418030849000d01340f40d003512006001c45071284880b40030050141410402803405184481120703200d0140940c0c410a0704103001e04450042001034070003c1c0c42d0b2420000380e802480880040c2d10304440320f819050010300f06019850311140600320301544098400d0000007007120030014046914010740345161079051196886040141950141900040a40e441080f848407680f400303a10440791500c0920f0601700805001070340e00915001010b080f40907a02c05800e03c01150b800805190740300e4400d000071414140483e0000390b4407590341180d24082c0d141d141d4550804600510032002400c1e000c0d0444107410358882081c0c0041008542d02d0081c042a494a00300c02e14000d03007440d010301c10040410131207030041800c41198403014040310b01959039410b40003000ea107610352102102200ca449820700e180c02503000c030300005030007860b00041040c1030006020a13a040013248440315015a400140d507a041030100b10f1a106060803000380d44001c1c0360301c180d0002008014098680d2071102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 142426187 1250 142424937 142424957
    0x317010905070e09100308070b040302010b091608100504110901020606030c0f131401030b0114120d05161403090a0602011e02031909110f011817100e01020a 69
    0x20003100c1054690300001800f4038200645031070481031580d00400039040b02c021050340da507a1194941d104100456002e244c0e138041000b859020b00c0f03600c0c280390041d03426440502e0500364000c03200b10072000c01e50500c10b030480402c0302c628030340101c0800f42001420411800e440b95440c1c0d603c81d00b03d0505c150051083c1c2000840d90708012800d1440068041e001c00e00341900102007248a01c0402107200d80550340d001a1643ca03001d480b80c00e0f0003180580c0300b66280354189500b00005415001447d4040e0b1400b0030b09850b800400101c28040c500185004c54440780740c5000c0d007040e214000c0c009000440c0b001c034030480303a4070302000030450304204443e01282039548400607803d8910400c44610541c0c0c840d0001160280d142d002141d03c00015075800e1340c01a0021824030480e840054150f0f0568403014045070b25042034020048244802d00303107022580e440c3c03425203146107018010340b50703001240300690503400c0e801c1188161070700d14148240700c080107041ca807034000c0d00b107107040500156001d44 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 142427437 1250 142426187 142426199
    0x7080d0912021605270928021302030402030c060c010f02030412020601060f0504090213030b0a0b0a050612060f0a0509070f09060302180f010203190816020304060c0f0618031701 78
    0x550174180c050300601e1071541882d120815208210024000300460003401c41c10700100d904c582c14012040c1581e8061510158640107006440c14109031800b0181d10410a020160380c0c001032038086105d0446c1d41c0d995440ca411001800b40401ea0481740e0001d0001c8103100400c062003ea00d1991400c6a00321516a03a03510b02c101d40003900c901d03c560200e01c0803c01449800f110b42c0003890710700e88107140c402056a481d40c8016100008403840503200303a50302503a0304a4a04082ca600082008070340a0b81002c100341614403003100050170051040744085040c100c00d13200c90640340c0c005c041c000c1080c842844c010380081d005c0d56240b064200010700040c00480c500b8020310030f0707525410f4100800041c0705070310028440380c031b289040442d041d44010b00070030409490b1600343d40c0039200d02d9542e03d2640d09100746070f01d64040c140322900055400c1030101703110789580000107650312600545e00c5c8485442a05040d0000c0c10080883c80c0542c1e0400c084134149504480040c02c0c101584010920b141e030788030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 142428687 1250 142427437 142427449
    0x102040302031b010807030b03031605010f0e0d0518040e06070507030314010e040b040303090b01120614040b1b070606060f020c04051b0c0102090d050d18060507080d0912021605 78
    0x10100c5010174105008203040600c6075020403035090001d8100ca103040910805040c041c42c6500d022602691140d03020600b0029a01035010461280402030400000300c0d10302070880e004400007200e08000651155001d503a0b940c00c2103e06030000d8060700c9460420813001000d96024142c00d40c0401d040020b101040c20b0000000c604a8820220f241010f40f580d03954080407203400f4109804040c0c90b20002030106403001980c6000b440f41254200388030b0100c1c03501c1c2c804da994008032502003406034400c010108210350a80340d8030060303800802e20240401800b0304401d00640c07070003400181ca00781021502c160440d80c1101100740c10740844001d840c2c10020002030f41c0d0308840e44102d81e40c0c0320080c0944010407034081d08000e1a548000340c140f1a898011441481100e4000d580300c5d40311719041e100032038000d00e403903590b04e1542a0030703c142810400d0141a40c452250014981034000404000d0944113601082c0c003a40d01020040c40c55901c0a0001e540ea0301480d10864012002200000e143c6802 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 142429937 1250 142428687 142428733
    0x1080c04030218060609090906090f1c030c020f1002030103021309030f051303051204051f02030405010c0c0527010b1c0c020106030c030f110108041a06010201021308010204030203 79
    0x24a400c41044042c50140d03250302018010300c5d000030003485068030560f940500144240340c4080100034030b18045000502d02040303042c407130040d60050004103a400700191604d02401d195420081150f40d014581280341586d04250502e15000c0c50080c5141030505800a6040313900860348254040340000301c1d8003c40307016140c0100402c0c0300049200b200c5003d40d020b08203c11007040005200b41d0342c0e4480c81e04200481c505a044a040080c041c0542c1c82c00032001c203a0321a403007034099101d5138002c5000e5920312a034007402d4144211117042d03070100f0100e6501200079020150502c1034500b005802041164101f100c08281c0e08141070022a600c032481041c1c4100420340c02041c00d15803550000c81008000441d9400700719504d614000c4046004440d030340e0b0080d0300c035840111000e07000d41400c0b2030296404045504000c503000c18000800d201d201501c0c0800803203060000c1544401c40180d00a11442103005100b0901e4900021190010b5018008481c001c3e8140c81e0340c60b014181030002d5182c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 142431187 1250 142429937 142429939
    0x120601121107060b01030f02130e09060702190c031403030a0b0111030d050901060801050711060a05010e0a0c091e0602011a06030c16060f0606020f0a020a06030c0210090c030201080c040302 83
    0x34800c000c00309083d908502910001030400040c0410403c4040040e6480000b000690300000352080156800d89501541d011903603801030039040c14444002519112910f4000d04000c448104070018803200740c820360002d41c0d01141828007610320700300d640d1f03d03504112010116613182030a00051540210b80795041c403618040514604800090883d00410001c1d00d0781c2500c4d0340c4c0341d1002c952100300740b09841c0207600036181c01c00d84081c03041c4541c2c40c1a00080c00c2c0c04500c2c0c01d06004010260808100a400c40c0d10440c0109400708544000c8546804d90307401104030211544100c885d414050020905542c1c00d0f034000d1042c03000602400360556010300340c4540002081001400e04035529000d082448041d0001408015041e1a00029a000903e035048040d9903040100501d41d01049440c2001b415600500200e10b0035800003505404a8841c0c2002d040d01c130700064010310b10a00010f0a24007480b4001c0100c07880c03d041403481d9002600007240400e4542020600c4090700c441a07901320f9078 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 142432437 1250 142431187 142431221
    0x14191e03051510050c0d0e0915010c020d050c1f110303090706050c33010801201806030903071707051f02040504090f0b0606090f09060303070812060112 67
    0x2100000b403211003c03010700c5940801c203042c01040040c103020b200010749500c03a43c1da44900240845d0420003892005001000604121140f000659800c2000002401e4046551100032011410030038106a080019241d0180000d02d119209031600c070305071050b01420f90340b4070700401c41c0444090340e44e21042e0390800460380010000c2104a206000034800d62001e003013a614100041c4a02501c038501c2900e5282e5a0317010210000b0346030b5007452060340140b14000007030082c0d007441e800b444100901560b0762290424001801c08084003030f084820b8031018068001e540d01d2503c2c016040d101d40200004440c018001c07031014002030620010348040a07001f00c09800420380250040310440c245800a0703c407580c003404001015601c61040c1c1201e1801504600da101d01c2a03d402c1c0005030b030042a040c41610148060a04c98413100c0c0001e0f81110705542c1c224041d00c07501b0029145028481c0010a412400640500400308420031103000c0c0500780c9030492500c10408000b4103481000300c003410000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 142433687 1250 142432437 142432471
    0x6070b0711011a0d0c170d02120304020d0201121509090b0a06180e0705040920010504140904150507110606010f0c0305130504020408030c10060e0714191e0305 70
    0x11400d0f07030f002815031707200e12814102969581d140515000c080340313200c0115005030b40080002a018403030403039040040241c3d1491440c041c2c1c0000d800b41c04520f03020f0f0401000030315841c0c800509500c800182c00030700c51000307402555032076144040d020006049038140b050201195410b13485000c1e110558401000b6003550a4409044800910042c189040903205900d400502d640b0780b4443c1007c400d0142c440c4540160b05132042c00c2e101c641010f0b20a04201080208021425041190f0400d60700200c0d15081c141c0c480703003440b070302c40d940e00d0303070401d03180751800003400a4103802203a0310b00359101c040c8c241d0394146e4504006454843c55070940d072001c02d03040940d10700001e100300c004100c1b00c225034130720011094a40010900b242c0040d00602c00c65072000503036110b1f4038010808034103134240c0c03810203200d07013420034404024645000e04a4414045110408030b141c44107601522905101c6400f5400c1c100141c0030010a04092141c111890001043c0807a28036480790007450f1041d42c507064801400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 142434937 1250 142433687 142433689
    0x240108120c03070605340f030207060f02030c071205120601030902030a050f0607020721061e020706060501030e0303070c170c061e090316080a090506070b0711011a 72
    0xd0340c44140481418002085000c00090301d51043c2401440c281c810440302c54640090b0240d80c032043c0031104003000030383e481450566481240007030b0000041c600541c69200a144c108043c040f2039a42403292400441040840d03000400500700f1035000d40a8038440303400c0d0b1002074034940f19a07110a40c2c00070401000812550103900a2680d840c0301604070351901c0d0071900c031641055080140314506812010502c0085641004858050300103040d980800881c44541403420950034a0000c0126444034044182c45081103400d210303049104109544d24136240ca016070091410f40a005c1c0840d181c1014043c0008001064a120740c585407900c0c0100c42e00b6072036203440d400c2400605850990300308900390103004203010041c0960101ca000090381e40c4281488401b5840044c29048076501c14000e85400100240490440e240c1104c0305641d242d0120104548a00b095003080b50404030000e4048101318000704018815800e941c0c0f404126117001c200c840c01c2e90054401072181705a080491815 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 142436187 1250 142434937 142434973
    0x41106040303082715040308060307050609090711160504051605030a05090309040c020106090e0613080a0c12121a0f1309020909060103110607030503010e0711060108240108 76
    0x15142e00c0f00300b43c581801340744107035481c11072401c402d8a040003a08043c0020190071401c3d142d00140102c0203402c3e05411301002c00c507103014415842e4031034490000403a03041c03030040c03c01d00e40c030030a000c06070b0380011420680b0420b01b8256104082c015498040012100c6251025248001e0600d690316451611a003500000ad8030014200c0d035044e000401060186a1380d6209514030b005090b0000310700c0034645803d0328103e608002449441d60007203001c00c00b1154800008050486d032007000da0b9210ac1c1c0091f402c07601f5542132800245228803840111221170b0304156121528141d0307139403c2c000b19404005100405031043d850980003e2080700840c0f003450700e6000e61b14001c900110015040b08290001004442e0545200d100d40e08508010300600444146403c0465410303200e4600e4070030f040d54010a00d00c014802c4050501d0305d0710216012078400c290603015500c1890440d030841d615144010b4580f440c1c1c0c04100410300b0282c608c0b1007080d0607401424102e41783d09007d0056100c0017480124 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 142437437 1250 142436187 142436221
    0x801090c05270604120221030f0703030e0303040c082e0c030b040908091507020a030f030c0203010624030603120302030c1b070e0903070f1502120f04110604030308 72
    0xc082c1e500340c0360300700741c0b038507110301602c010703c0100c03000700c1e0f100c8207401403040350390b1403001c801e444840250180904060000c102c407842d22031110070554032251802c04600030416580d009030389000c004188418044c6080d503030410b60342d0f80029500c48009000c026001d140790f010310701d80322100c103400485104540d03900080404240342004520340c080000000d0807200c0d190400c680c25035001c01c0f00a802d081030b00200400d030420329411407504440340c001a01586d61440020011303524400d0b2501014890360702c0700300d055405002840b540740c899a0744d2182041c0d48000418080c280748807084081e00c640602e8044036001003035400c0a1813813460440103540000c0401042400402400d80d04642c1a4a8800140d10b92000341c095541030035201c1c9800381c0c010701780714000c0d40140180800710b440300c09010101075100d048250310302c0141c070703010010b801111030071111030780f46c4410025510001440d117445144140180716903a13003003030704000407401980070160000f604200002c007a64040f000b056 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 142438687 1250 142437437 142437487
    0xd08061009050607080a030507090303080a1d0312011406040b03010b0a0e1801080c0604050f01030504020102010e150f0106021612050a0803010303030c0305010b090102100f02130608070801090c05 86
    0x304010784910218040360f0004e00201c42c2007000103100c500407541407080c16004401843c2084080d4a940c400900141c0090000c4021680d90702001c0c02e038070040308803044140d071841c1c15a9210740c0e10701044414101d0902c0384100c0420904c2c0d4500d20ba150410461342980c14045009040d6400c20400000076004040070000307006410040206a964400c107494494051851403070b11503050180310f03410403001d880c0c0309000b40802d00c0b041c82265074800101e0b150701020310f8001015951400100d016003400c0c45100802e0182d1509408fc085149442501c2400c002c4000c580301c0e661075000300e03603170040e0003441055081d0401d400d101059005c680c3c060318030b0083c000c950b41a07240340c81701c2ea210761080e8000c8000c243d4801c51554501e4050003198010240c0200c0c080c28a0754010002c7d40b54400c031401e40b40702c02e40d6101c2c0310341003000d298159808416039001d03200c0099110b580140646406555200c0402e40000002070f40403c140600380d0055103603504d030760800c84a01d155a002d400594411 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 142439937 1250 142438687 142438697
    0x50903070f02031e03030103060605040b01050f090a0e0a0e060123120304050405190507031e0f0603050a060506150702030d0c03120c050a180308040b070c090c0e0a06020d080610 78
    0x509075141c0030120300e00c44c10120301d0107145e0702d514510340740c4215103a65010380d00641c18120040d40170780e0030070141c6800703080080e1010b54507078044000030b54011507030700850f003d00001002d210031801a980308603006415117044513103d9894110301541c10f202040f99040440c5804910310713903030400b50f100c0107131840e20000b1281002d489000150580b10100c408004205041220003203007030040c01011b0b000a82d6040420003050400c0080c02149150300d43c00580b02d844075040c4a40007419030050b401190804203031075592815107401005000159069449a000002c0c01405140510215407070240d0042c01000c08818001c0150751a180303081c01601442044d05d48840c8a180c98065810152801d0351403580d1111200800b41200c2d05090700c818440409100a1000031140c800711000da6000200c11504c81c00b130f070f2a01c4d09140a89030405111581410b020551554210007440788074101200c2d41194a034403004200c1e91a8450124200010403000100708141031101002c1c51040c502d29007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 142441187 1250 142439937 142439953
    0xc090117070305061f2c090304180e0c011d010c031103280908061b1306050406081b03240d0f02150f031605070c060e13050903070f0203 60
    0x4040c04d0120840b810f260701000d6004460182da03c0d41d400c000900000c4042000d03e0000d4a01500e4050f050707000d41003945c8a500110755001d9080090741e000b8113600c0d0380d04000d285180b407110080c00c0e108214102500c9100d01c191901e600403151282c3c20b02d10f03119203132008403900004480c40d21000006505101400c0444400d44400748000e09615415100c09001407049a00800340e203444945042d0412400140c280003000c1c3c0070035a250003040a6816104403250415102c000f841003c1e900a8165012000002c0c180d0f08400544203c440e2600c45040c195102034420101501d04070590b01e2807801080054140500c4035000b40c2035000c0580042c40d004c0d01c3d80003203020700490744c8054490b04107a000728001c41c80d0100d2030130025009040807508045a0100c40300c480d0001600c003141540860b070a200100b40b2500641d40c0041d0803180c00d1415a503500d2011b441038201080e0325005214006120f904400e19000d000d00906011000710b01c0c114190700ea0642c00c40300c81800b20703894081d041c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 142442437 1250 142441187 142441193
    0x2708030f09150f091005210c09031606020607091202091503190611090307062610170105010e130c05030307050f1b0f01050a12050703020a020706020c0901170703 71
    0x1a20f00c2c1d8543d03c50341513403006200100301203022030954080801504001100515070500150103c00c61400262801c541f0303200f00203481d034010b41e0074580c1c240c455200704008282c0301d40100f10488103e0380988640d5210b10f0022652110349000c0d19402400105143e4018107115040c3da0f44510a100d04c403c00501d4071000905108810b00d6159048110400240a100a6100311080703083c001c0c951900e49400c88000c42c0d201c1011740310720406e01c812604c180c0ca42c0703d03010b544400042c0390150f4001d01072800030b0108250700c12a00961a03250442807070302005500500c60141a103030101007110b940d0b034500d0415559592841c0003100c0c0d0032481e4900080a403010005020f01902c14400341c0561451800d2030b510385461640700c0700406030340a02440c01070322513942c03d10402c03c0a280080e5200740c4180d0a403000644c1c2d0114200341403902c0100084a9403507806410190895400d1710586039035044120b075101143c0f24559402000d02c001001200c83c2164140300c0684110b09550340560b81e51 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 142443687 1250 142442437 142442479
    0x90708070818031303061b05070b062209030207171605040b010201090c1d10030c060302030a022a121e0903070807032103141602011107032708030f09 66
    0x5e401220103e4544980080f00030396440c4a811740d8503189085414030074641ca0740f9044031005084180140c0e0b04070308625901c0d0f0094002241d5420110701070140d880c462800943c0e403491441000c0c070403120018180341240000c50b803c1036000240c600c20b180c1ca4205010000100301a810f0641550b41c0c5081c40400a03201400b200000c103000316811511440c010258440c0e600700a0800c41001c400810078000a81c400718448161030492400603108da4a403943c4000030311601c1400016000000d07401c0a60440000040711440c2d44101561002c0c4414001000700d8041c000c40c0d0b2011002c03030717041520340c074490501810030f000e070041c11680304a40c5c501d40070382059015041951100000d543d911441c08640c3d42c00c0c2c44140c0f189c9001c00511400302501104803d000d042d82503900d80e8a500204494400d40015406010080805507188030b9450050000c45400b43c0b40c034441c1d044d8080b040300103001900c04408039490500910724040d0150600d8045610054000b988000100c01c5000340002e40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 142444937 1250 142443687 142443689
    0x120902100e032a0306010501020706080103110d1a090c040203070e33070c05010905060d0b031006080c010e120a030f03020c0a11090f1005041a18060907080708180313 73
    0x1d0700a0f15000c401038001d16081601c1600014107551080104000207944508031030b04680d0040c50302000140e80c440080c914400c19031000e4480c0c001c20141c41103000b0014206402655004100c076030544a100a01040c0d010446021001c035010b022907650900b48081400d07441018141e0b80542c0c2d40341c2d80b20700c4190210380102d1a601500100e002004c1007500420500a0182420072402051800f40000c0c43d80c801c96540080c0c4a46548101d105034608200c20800391807040d000f031165903203901c0340c03a0f034a580000b001d600040210a4544e45410300c41c1080882c94000005412034010f43c3c0c1301034407a44461003109040550030494501035030300501661242d58440c2441001480c0d40c4c03420071560400190200480042807000e010a54000d0b80ca4041112001d07280424080c40201c04002651000c083d0960000002c0120b081d03c26000d40c030291091400b00c0e4201c51540f14100c003240c14000454410021542c014041800001c0e4928140e442e6005102200d10b4580d88550186044d109 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 142446043 1106 142444937 142444993
    0x1020705101a0d0809010909090b18030c010501060c0213020c0c130b06070c152102130b0d09051207020f040b01200d120902100e03 58
    0x254100d022402c08001d183e000c1c4050305040c182e0440e408000f0090000e10000320100380846944901c65039107400c2410310b10b899440d40010031004802808405051100b400308001d405c3c030901803a800f0b011a56100c000f01441c4d44140081d0f0402e03001900d445600500103000d0940001071032400340e40d41140c1d5085084c03003003d1100c0091401800050b008800080c60780140032840d890700e02103076060004031410920303601d0215858250640050030340400601070a0b27621507150080d26422880340c41407200142d42d105403e4540e48206070101e5603a4031400c0c2c03c0c00b4005c0c1070285940400000702810b18003035483d8002a5541c0d40d0a025510441d03417142032a8140e445007082442c1c0c50300080101d60f07603101405074165180c0ca03000200e00000c584540084034403080740280d414203540608100e000965080094803a00c00c1e109440b909445114a01e04100c01c0904000d070360b0340c00c = true := by decide +kernel

theorem cover : BRFrame.Cov 142266187 142446043 := by
  have h0 := BRFrame.cov_init 142266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 142266187 ≤ n) (h2 : n < 142446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
