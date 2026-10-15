-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5301
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:24:54.071384+00:00
-- url     : https://prove2.me/submissions/fb4dc33e-45f8-460e-93c5-6f2e8b480450

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 953237410 ≤ n < 953417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 953238660 1250 953237410 953237449
    0xd061502030a1b060903020105092e05250207091401050108180703050f1e01140c0c10020712080a05010305120a020c0909030408060c0403021507030e03060a0c020c 72
    0xa40b02100d40165098884040c0010350010f2884076690740c0829601c40f404c007240141d45410034010000c404100d01c0071030381101000d540d80318101c0e011640040d14a60414113056071103c0121744c0025109030340545c04511103009803030b00e81d01070130080e507500098402e00110a1800c600c803404038049450090503184140c1d141314982c0c80303110300000c40b24011800c84003940100500040010740810820b10a440300c2c0000d00701c180040100c400246010503040c81c00383e41806002c1d100c0e4012810300c680e0117199845510b46940d4a0948540391054413440c640c004d901c00200b50060100c3e16440c000070107103a41d5010a1030b610b5089540c1070716000e2000a00350392101c0b204002c0120341601611b1100d00610488000152403000a10b9030181614103411035000000d040c003240f41d040c05071550141060100320700e0301c0e165a0109a113600c0402040d40a40800f0170601d00301445030321800c940410003011a1b9850034901103407402490f0b00011600584a900d035003510b036050100e14020210b0b00d442c0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 953239910 1250 953238660 953238667
    0x30203100515010f030b1009150c12050a020703060c02010218190312030e120904060f06020d140f0a1d010e0105070b0a11040b070b060111030702150904060b0d06150203 74
    0x2e0054541c03502d0455244240341d26803160b980c11382c540c58003180d500e0406540d40c005591410b41516103d4251012440801c508001902c001c603140900085082155140c802d50311018100b003281400115040100742e281041d003401009503054010b0517000095889031143c55030b07180d00b0003d252415040c04480100b4101d03007000403d84458000788046414100410700e100d404ca1a64140720006e003c1e00d0507110082800402814076104010141c008040000049800d180001e5070f101120074082040008001030385464a4898003078a90341e0149100741901c034003041c90040e09550700642032402401e42d84c100103030340750301c2201e00e00d003005010b0712001e02c1e000e0a91110540c40c080140800c04140d280c100c0a0304903400a00240000d20b031800c50581c0314402d07480c00b010800740190403e0f0420440038860f2070000000302c1101c040365411280c1c036201140404e03140c2040c5c000d43c41140c1c1d015140c060001001c1c03607180e0040800555401e41000311a031903480c40c052801807034103000d005a0050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 953241160 1250 953239910 953239951
    0x3030705041a070506040b2706040b150916020106090e0d030b0616200306090d0e04050601080105041e020301090e0c0d03050417010e102403030807140c0d090302031005 74
    0x5620242c000701c03006950523107561025409840c05040e0703001d800d1190f02c20b20810082c00003085503617403c10219a2240680c0340114001031203020090120843e001702103401610440c004d42c01180240b2420354148a840103541010b910b642c1c540750404c0129003000c100d1031480c81d00108940b2455140000d44807208100e49aa40000d1886074800c507191240d000001c2040d41d007040518480e85088000303119404a00c180101082c418040c400d00490400003444096a003220960b419680309850000f050041442800d250600d8001e10a4880f803002001040502c020307000f8803003103549103007220f8481c80c00e8002c0c008076242060000d000514140010321101001080764481e030040e0700300202d801010480e080b0304180c051044900019540c0c1016000c440a09000c03e401c0003e01510800e0300c4d1458074003506803d002030800e001c001d50741012042c805541410380b010300e0340860803500c04000a90b03014201c00740b40d00042e8842d2050043c0c15000a095001e418850045111070740300341c0481c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 953242410 1250 953241160 953241173
    0x190b0604090512091503100617042105190e01032304030c0503190e0f03010b1005090d0804080729070807020103060504090b04030311160215090303030705041a07050604 74
    0xb070031481d40008094604000d0380c0c4010040c0d4020b52403803920040092800c1000b924040c4c800581c09c00c07010701c1204020100b070b140d208100d400500f240200c5181440c004080300c842c800e040300c4407800b50b5110391403030b04190312440c11502ca0500780c8081040b160900c071410050700400e01c001680c82d201c070740000c1c002480385c0c2c81325661a22030b03c1120304007607512510f200002130048030360b40040d40020b502c03802c5290840d41030209038019802004032000d481c1c0807070b0560360071483d101c1c240580001c04002544900d41c800702c861390000c2e002c0f07032170355100c01d002070b00c0b00314521170242000d0001201c8222000c20740f03c13180000000c2940d181c9810041d9440103425000820300384d0601d42e503011f00064546035405201c0b02a84554150b8520b40b4041c40c01404803091008000720b0940d00340540c40100700c1001215910755012142c0940016840704e000484d0300c282c48905806d8080071082c4442a07405ca03020740195040307002c1e0349084e0349070920310340e209008000015029a1110000c280401c0d030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 953243660 1250 953242410 953242417
    0x8281b08070503120c09040b06120f04080409020a03140145050403030f27110d120c060b060724090501060f03050c040516050a030905190b0604090512 66
    0xc5042030b01e00340315001d007601d0091041250343d4600310308000703080031b8585064412502c5610088031200c4c02d01c00088012510b00b08001c05801c20311003000081383c00c0c01811400d4800400001500703550303440c070703400f40280900003100c107045486a1810022030551101d0702c10004008082080d0090010307407100310703a103860502c181c18044252050b401c121100c0140a04e40c0b041d4020b0301c0100d210001400e0410440305120459150704448913203040381803043c9848005040d03000040e110000340300c0d8000070a58212690001c2035001108084800980c2000c0d080440a01448040014420440500c0900e214003040280301d000c4850049112503010300070440d211082c8031000900051640d5010b00b180e400d9000912950b088200800410008200c05449000103681c240a542071031130310030203000040c542c0c103018400040b0795045928800d9101070901c64001040784c0084006144501032620844d4080e5008881c0500190b02410940104071403160f018004004294400414403101d40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 953244910 1250 953243660 953243663
    0x90c02120d0e0106030b04030f08010e01050d110301020d0e1516030f09050d020708014b090b071706090601031104031b0e010f030b0712020708281b0807 67
    0x142c0e5400e221000000c00d04c074501c0910b1142108604900b0103041c00362910580664010810820a006000f17003803004030032504460b400d5400031404440c42c681120340c80030300313400303a0341640c40030966004250994000610f042804070998065200399224902e85d07210459000c2e2425455140741c1c1e010b60710990156120034103148001400844660b100c1c0c0c240b4440d90b04000050384a0141403200c1c20007845400000c0a41c0c00702040040990301e480c65080d0140115284100354043d0965140c94540c1400c6014407420303c0304001481e064501003045500030f8400b0400150031035948806200c68140d0680250402442074510742d039107400445c0603101280040e0b082c0380041c07100100042441d0305c00c10340c240c8002d5540c0c0140c1d082050100c064001648400100200c0c440c08001141004058980051007445c01d003109074804450b03a006481091001020b0610000d2010f00b07080080d912042810f000f0803850b283e001440c0d2045403000c0b460540403104c4075100b121140060f10305001400c030300c2e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 953246160 1250 953244910 953244937
    0xf050313060b030a050105100f03020906040f020f040b12060f1305060f030a030e030f03040e15150a020f0111030c040b1b030309070f06020d0e040b010c02062101090c0212 75
    0x400450202c1c2c280f84e103100d002c440603034480c42800111008000315a000e07005c11200c00c1700321407070f540000b038101c1c1c0007400f542c0c0101e03910000c3c0710b1a4000c0350103d5060702d00e4055020358496640410410680c800c1a000f040d14140c1c8002c11094a001030b0b4034006858000c2410501c40750015494000b000c01805943e40102c400a4045817038509000c002085402070310703605081e01c2207a0505040c410140012007032034100700001d02009004011040d0443c0b400380c0076200141c0c000d004696528110002c1c02d22808010400010aa44c00110b802c91290240021b10004128082c10009800280c8405000410502040c4150710589000e4200d003405c01484055840b0078442d5203003154029210104103030030862041c441d5020310f160040c0280030034401070150100104009141a640c0030100c0d201d0764607001c0f1003206a01c102071303c185c9140c00808090342c50b0126500700751180340c0180a490791400c41d01c00050580c0c0c5a1007071031581c084d107402806172100308511000c41c83c7c0c04082c5040c01d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 953247410 1250 953246160 953246171
    0x10b0c010905190b0a111c09081611100917070b0403050607091d070c150608010506010e01030605061813020309010b1503070e100507050610060306060f05031306 71
    0x100d0ba00300042c9401c1648051030054005260409500d4503000400c40302c9850f0070701004005001c4408111112103180d000080001080d419030300000d0481d4100140080d90302096404910488103e07840d11180300340041007c3c0b107540010701c000440c603d903401010a0101c1020042c600700032541c2404202008140d403981038aa200b1481c41c8d07002904244c03440e5001c0c404102c19540c0116038280600891607040745406694001381c0c42c07083d0010300d2401000314401214040141101c80300450b50100e8905004440c0c50351183d9000b010221090b5000803044101642c0c50350003803040c0c40982c4d0000d0503a500d0706211160b0445060002c58036103403c000d200c0d540602940c410b00c09540a542d142c400031038551130701c000700818901c0b10441c59011610410a001019401c4001d0752000f0409541e112180301200c4d03011340e85801406000f4100e4055001048404218000800143c83d0070b52020041592074403800c032040300601c00410301040f805c0001c00c03808031030b402d54a4402881050046070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 953248660 1250 953247410 953247413
    0x9060a0b0307030f020d0c1103040b090f06040b0d0c090f0815150a03030903020a090203150108092a1003060e0f0622020901080604110a1101091707030f17010b0c0109 73
    0x80303030304c0200301c010026500c5142507d05903000003600d200f20b800380300550800d810b04661036428441c9400c540e120b00d802841a1703103e6121001600d00808440c540a6111510b0700e0070003015162108001000541604020409501211001c0103072140035000f020404800d880ca09104800a040c90840c00200c480b1000d4961b034500c1507030081c1d8481e41c0c50441841c914410300201405681001d401ca0340184108450101d4290410f06014024600b030200342e201c90202500b407100c036840b042c40c8010707400b45a650600c00241050080041a9142c1d010004680c0e002c03002c580c0135020780c603e881c44400c0031500e400001138415401140042001092003c1803a521064680c07400549000c1d0380c000c01c0130b41c0c0d10341c0c10188042d4044000d450622503203030225180c1010744241c1c7d81640a20442c10344a000b910400d510010007507a0250740803143c0c00e03032005400e1140e0001d9000701c001441c03500541115512815111002078554010004541d00b00006500c03030780c2106524a03100d40d0380b05900740 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 953249910 1250 953248660 953248691
    0xc15100f030f1505010b0f0319110a1b0804050d050c210c100e150c0f0127020d1101121b03150f090b0a0806070f080609060a0b030703 59
    0x30020340c403034805054580c0062401c1844801e03202c40a014140c80c10004000c00d070201000c0382c80d03450300120072a5480d81d4480c40e00f41c2000300a00024107a51510003503842c0d015481004201c8044039031520081080350415000000b040714000911030001401b080005041044030240f20318071620684050142400110300c040e8a2204021180b00102c80b100160030030501c49480503840907681d441c25643e8050026080d81c984090603405440030007640d00340b49004809440c0948803103800d0301d68078040e6034900f0340a407440c0400c1401c03941c00200c1040c138241142c202c01018644c0076007844d01200030750f2205a0005002160a41844014490003c001180344195041c12212200b80c1c030080410603002021039040155480243d4003e00040c002c1c0800200100d04983c45102c010802c0d000300000301d42e14100310f80c050010362040d84103002800d60003c0590030300c22510b03554600c4903540c00007080b96004054590a0300302c00424410b0005940080003950301017030a0030701040c42840e9902c442d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 953251160 1250 953249910 953249939
    0x2040e031210090c0216030b070201020c07030c031211060103020607140f1b0613090e0a080f040911090d020f01110a0302060a0c11190201030b0402040e090c060c1510 73
    0x88207112402d4005100b46042482005440d1001d1710040403a48084008176030182d00324040030340700c4509040002c400303a100350100c448007070589060f1000d030780d5245443c4444503030301d010494044003032480e5004140d1040316284848900700c00208401c2c1d1070340e0240000d5078003040c825142079156000191800c0010002076a81c400320350001d0104200000e02950590240075649110b014100805150490401103080c283c48103008002512081001c2c19840c050040000500c4c080010940c03243c00018500600225290b0b0349051001c46402e9503110203620403507085a0384010028070007805801d00c85500f04026a060400c0d410b82c01e01c0d510030600e011a8040c0440059005004008004060380600e83ca140709900303084ca00c51501341e48407605c8001c6d11840602c00e2582ca03481e5030640e07101c0c4c0c00100c4030f00c4000d8011541d9980b92804404079480407110340c03005104900011400e41002c0c0116100c0c0c510000191a45260544c0b400400707030000703019190304080d840e0003c41c484881c4c2c00702 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 953252410 1250 953251160 953251171
    0xb0604021b1f150905180d121104050607151e09060b0306090706050a021f0e0f0705060d0209130c0503040c0e09070e07021f0b18011202040e0312 64
    0x4010800e461514181c81c012030b240c00c0d0442d41e0500d804032000030380c021850019103a40c04e601080d40e5a405043c04d100c00c05c201c00c90310b650b00c90308020040e0b9079004a0000309a018010081c4030003165910f48460510491141d603800040030095072020640b42500380d4200c112401d00030800c0c039254444001403540031500c6020655a40c102c0e4810401e01d44903907102800c0c00ea014100c2454024175598840c0a0351040d0001c1c800001006500740307209021615101d80c0707004070540410940907000004000d00e480c0d5800354490004245e07044017000400c50121100100a6803620f0882512325000e500318500d0140c012202601858102c50107000303001c0140510343e925600d07840d0030704140380000c84680c84503d50314502c034140001010003003284001c2d02c13035a40250000381c980c2c0c013080340b03445441850415601e104000c00c0c00944110f801101c3c1c0100101c940e2104c0d000e0103d090500c0003030a12800c0118000c0590640c014102600201c01145908040d01e00b400d225030400c24111004450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 953253660 1250 953252410 953252413
    0x91a030d08091e0d2a03020a020f0103052e030b010b07030305010b03070f1b140604030810051c030c020d0807062007030c02030f071e140d0b0604021b 66
    0x10450100070411210b1481280907100e040b00d2441c403c0d03500d490b14490340710242000703585051020f0603865000ca16007544000e8080c03990440740382c1002921064182400c80c410459900413540d107600c40d0295500412540d40c0a50280c8214001000f002000086210249030a00000400f003921408038500030045580441e40d10100f13807600a0464405801420b6204403d2051020803031340b0282c0c222080d030342030405400c5c0000c0000d140380c80a0881000604446200340c42d1104900080f810f10701543c0b20360bd0341e40041d00c40c00c03a4200e07107805a004554210001e4001004441040c40e080f584c614060708101c4030903103a90700440e0b00c0c509411820740d0108000100001042030034440c080c1404e0030359410005406044051040c01d111300c0c01d000c0d0230000c15500400c19550705106401c03002c10b034002124055569500700d41c8000384070a041d15840f002e040e1f40014041d9852000031601e1100816408001c3e142d6610425588000ba0245801903070a01640319589050341c55804491420b10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 953254910 1250 953253660 953253677
    0xa05061906050309011b050706050606070b0a0b030c01050405010c1104060815250c030c05070e01081b10080606071506030309150201060303090b1e0f030906011203020304091a030d 79
    0x190703014203482244030840c9410000c0e00e031081401f9484004c6c0c801c8907510150110303580d2221000140c070b80c02140b40150620a8001c103102100d10a54003100c1d02440a03010b03951543e0800740103441c0c40c083e0707114050125012101c0180043d241e45909080104004c100168250300c07000b0344c62078101604d145042c48001c02060121000d88a2840c03209500f003007401182407550304400801808042c403008040c8181199481e04004090082002501f80340e81448415030396250340d030341c0d100c0d500c04000c6510404400c0c0c000c00da0030324425484510405840300d030b880b6198001406000c1c0c2c0040400d8030140c00365508540200042d001d4107008500a9480d0355400e420301c42c6007072691048000134000d5a00d000740c2000080e8011400c41c0844101c000d8407a1100d14170105400049802c3d88041d0901e0f03000540042e180d11464040e6000c0e00a0741c0c2120719a81e01d4070310354001903000300800f6001d644240001c200041c0b464211400040003403030607686401100e0003191038220f008958002103a1a40c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 953256160 1250 953254910 953254921
    0x9010c0f05012d0e1e03160605100e100b03100305070e01051008070e040f0b040f02070b10030b0c07030c080d0518010606051b030715050406180b0a050619060503 71
    0x200c038440385040c400821409130890701c0582d640000c182004c92018844000780000902032040e51440078551020b00031102d11b07840d02400509045860420201c0090341c00301e0000d00ca84c14480c41140000c0384551203600300141e00c08642c000400400c1c540038042070200000300f060000070010000701c00500003c3d4109010080b205d10140301c0c1404004900e010032403d5580700ca60280090015900020005209003600d009014010000c0350080c0c05d180300c181c0340707903082d44c01000c03102c3c09003610341e07403540360398100300b8000e070343c41c07102500c155661008100c10345000302c020311040b0700c00e05145032440034a548051003038000c007107403203d85a501c0d0200b001455080d050b100c1e910b20198003c00800b403d10501401900403040b20380c070a83d0100d60b0030078036180700b00100d03503059400902510081d0154101040649000c4070102c0c0c900e03081c1302c01003040343c4070240314076241035118004107031946e242e42414006200041c040d0394480c808109100c031030b502501103d006030400780e036503070b039a032424 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 953257410 1250 953256160 953256221
    0x604090e0c0103180b04170f090a090c0f050d06030609080304030809071802070c050d080d141003060e07031415090d050406080c040b1603030b04060b09010c0f0501 72
    0x144205034141030400190794580e4150303403040c4c184940d101824080325280c50400c9400034940d0401c003e60b600d40081c90b28100000500031b00310514080b1402c440803030b01d9444010940305a6140d10300801c0b603401c0010101ba0050303002d4040107807900c03000241156a5181d0307074240d5220500696821000005110a2640c4242e1065000303a4480c0200b00007490003a1001201c40c0c40601c120901d42d0200d00c460400002820190003000010b0400030041c1a41c2000d561983c81008040d044034034100d02c0d005c0380e040c1d207954148221b0400d0310781d1500b20320319210640a030107210606003040c0201e10012001070010020210388240c4440180802018042c450112040141c10429603511541c0410b40e8564090221800c0e14001d141c80300481c1c940c0ca80240560140b070b000304034142c0300401c440e41c05105401e8040e15a500980e41880071207115000e00c400c990550240d0240144100051113042d401644802c030128841da20300782d1840c4c819120b01d0308480500050000c5411490020803040700f5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 953258660 1250 953257410 953257423
    0x8070f0c0543050111070801052e080d03020702030316080d060506040b03150a0b07060c1707120203060315041b0614070f14060f06150f270604090e 65
    0x210024400c406032840502c015041010384a19810040e42c03407204801010140300d924000c20601d002030100c0e0030b001c0d0080003440d10000030320703003d403407816a521100c101d89080780c0e0859181401909440c0343c041b00880296210000070398040c4000c0084100000c45e002c2080e02141c02030181c19115003901c1c0700c4e001600d18a80c40940b003a1700c14072061082841c02e0003181c0c0c200000c00341c0208004590808600000a250b00c00300c110715020519406110030741d0080c06c07070035006960f0425000c4d0708103c0c43c400312070159040400a140244001d40014083d4021078025a00070100c5484801500040c00d42030011101111040c2020143c10a1915100b68a1000c0c05003810a681420105a4100d2581c05078000241c0040b0803142103500340500403404101c4042c9501c00d03648946000d52000425180039240c880c0140314031a0454494840e40c001d40d130b103507020140e02e43e00c0d15601d0b91510955045400840c205d0900d40c0e1901c10080e0b46100c0100020560103e004c00c590040c03a00d058100007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 953259910 1250 953258660 953258743
    0x140c071404021804020d15080a11010306060c15022a060703050705120c0f0a17070f0906030b030102091002070602010c1d040e010e0d0c0b090a0308070f0c05 69
    0x20b005110002858041c0030000794407000075140181c40d40303050001c000103410300d10070109060b0054500070a44405c04a1400c1106005da0411039000c10b19000450031105c007803042400003140749a040001400025000c4c0b914444454094280110044d0001502c072154203524600d12900070035140d22001030111991181c66800e0420031413503d0315000e00584503100303103d244000d54000054016100d03005940500caa45030380141c8072142c5000c0609100c14109004944014100028480710320903048044001c1480d41e0702a03040c0e113050303400d4024040e03859469070316540070b0280308203a44a24450b0780c0000e407598001c103e150710b440d00180c215088544c00d041000b02c4421251000c004002c0242003808050b00c000424008000403a4010101c4240c2000140203c0300ea2a003500d0340030f0b040040321806228003001ca900c03030b40501581c1d4281004020701003402e1030001141203004400003810781049040031140c0a504e03568140c10300064414a0100143c0c03e40c2c840901c0100e031407028a00e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 953261160 1250 953259910 953259919
    0x606120e0309061603090b030117010e0c1f0c0b13031215150c021e0a0602010b031b030f03040306020a0e01050c0a230f03030f0c07030816140c0714 65
    0x542d20381c001c2a41840b8440944030b5809014084030201441110180010710643c52903689950712213402d11405138841e040d0280c02c3d820492055046800490402030410000b0481c607000d9400c0190200c481440405440c284a5495100000300b504412010301c12001c0c1010f40644004525003e8000c0994545080c42140791405400310f0615000101d425500e5005407070030840f804071011074507070f00c420000030340051300403000a41d800703c414844055407104940c10903600d070311240100c1c221010003030080d46c10351001c00c03801d4007040e4001c40303000c08110203410f07100711b09c13080fa540e980707140d00590040f60f6143d40003401e0b4680075070010300c0b0711030441d013403a14034640203107071030166640c062143c0040c000d19001e12481e00848e54403074100e1423040800094450031120905915100d80003110344081c0003030ce1b40001440119038404540c51282d050301e400a0540718554003441d5807103521944c4c001d0241d0105005d42090782d0b480505224254940107014040c10024583c00380d070051014103005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 953262410 1250 953261160 953261167
    0x1e060e010f120c150f020c0d030e0d03021903020d181203030e07150e0a050d0203121c02030103060c020f0129210604060612170313060606120e03 64
    0x7114004610141155441c2c060303940c0700540c0342440d8181c0161a4441d24030580402107007660903420000050400f6003179000c0c1c40c8888422401d00c44946200b800040c0083c203210400f815510344800d600348a140203204644102c0038990f080d00e50b042c0341040541c0542c0c070421042840ea41d20107100c840750604480d141c0902450468105054410808024181500d070080c2455410f0100900c900800d40d09501100074580200042d2540110a01c4103004800c0004045858180a69040c039002c0e0f002e001400d115103070300c00b102c000c0e41005044c0041401001c201d00b500c01841d0001d91301850140d4000152039021220181ca00040301c034440c0c5150b41400c107030b45440010b0711024a0121200003942e0423051034040010105030b0384dea01c9120072880d4030f80c0070488900000700a84030f41c0c411039081002d561610103141206440801c018144c4500060b01d80343e00041002071500000c900fa00b03000d040745030380c0d01c01043e11000c3e00201d0004510b811955500d903183e01801903031552081c0958503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 953263660 1250 953262410 953262419
    0x315030d051c0b210709180b04050111070804050f0924030c12010e0607030209030604020d0807051002180a0f0605070305040905070216050105090d02040b040b03011e060e01 76
    0x215004500000900c0307030b8000c030b2440d1100388640100c045a1402090a60803001d5025440c43e41c03481006810118440c00c2408a04c03400d1b944564a08021031800380009219107543e40c1040200050046456540302c0d46180301410f5880045e0400c542304080c2c0340e0303e481c2003000303208540d880360780f040348180b06080c180401050130219041c540c81080c0401d0b4a020405d401092409803100c0c551508400514840400148190f002a04002e4010295941a01c540e14110164020702c13056561607001000401c00510388841c40407982c0d8403880c0c2160800ba5a034540c10300341001c0555158a46030005403807002e5246504551001c40c501326011040c2c1c40c02c245071080800444d00561040c0000080e005050600520540300180b034015010b111600c1d1080300252134104600140020079080400070410b50702500c151506e6030700c05001703070122109a4082001415951010682296803801140030300d0701c00303016030b2000f04480e07607095a00050803041e100403100c069107c0c06420b400c9000511 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 953264910 1250 953263660 953263667
    0x80d050c0d0b0d031d1206040b07080c04060801180f0f0917070506060402030c120103260307051914070b040b0108060105220b0a030b0402040c0216090f14010b0315030d 74
    0x403171a040c00051400ea0411074011030030101084606203c14425035003040700304a40080003501c240701c659900365a5850305140c0b03108601440c040e00f00030504c1580184031107002200103640c41301010300040b0350900f01c1402442102c0409480c0ea06031910360090300248108040180310740402034041904e4034141c1e4440c15168400a00130b64030690b00000803410940481c81501c0001803000705851040d69680760801e0030300b10f40911280d400c54050035031003680b01e40d2820340c0e2003000e680d1a01850210300a9030300700d002814001e44410701c0071540b02240d000c00d00c0000303000554800c50301840700d4141401c0c9071034015016400b0780721940c000c1c401031240d512000b1440d0a02100d032540304002010101e00080540200301c4d8458110210080000902036a0400d0900a500036182004459078450080341c651542911290100c54454810440c0403059409074000c50001c0100290640010b00c410551000170b031b100d0600301e9404803d02401d04a1000404042c441c11401400704840c0c0f001c015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 953266160 1250 953264910 953264927
    0x1050c03100e06062101060212030613090510020f0c1e210409090b011e0812070501060e010602030c0d0c020906132019110316080d050c0d0b0d03 64
    0x1000342c0c060b050007043e91500e03550281c1c0c02c41e668140c440540300c0c80104d9000d800002c00d00c81c880040c412500001010048041164050a005400c003a020305c45154048003519203150200d030188905400c8203045081c500c0905a00001c12542503076a040280e5001e24154205078600384641c203040c1401110f400000d0b0720200308480140c10520010b019050780c3c0d040c0030b82d0b440b04003014106000c0340c0030080d4030351041d4162006030030507003900d202082801c00a040e0a02170300f16164800610410b16044550150140f00d02c200f002042c602d4481b440004400740130382c842005a031000c43c164508290a200354440381c4075604e05110312280903000500001800341059000f030031004034902412200341c00420b061988503920381c221460746041f1a040b03038082210f0720b04010914586068152207500d500e0034440741300000754284407a14800c000305c00582d81048550b103108010201545180b4050144240312964445481d251100400c00640e003ca07000340d8400c0000241450011f80c001c2e0a1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 953267410 1250 953266160 953266169
    0xa022a0703030e060708040605040e013f0f060504110303031504050415050405071a0406020a06110702030d0801060f0f020607030c090b12040c1502122101030f030201050c0310 77
    0x100c210f001d065000b00d0014800e0070030141034080300140c040386040d0132000800484540b044d003c1016039945003880c8004411003600b41c05045c40050050f00c01c8003050202560003061040c9070b82c244982d5481c601020541c0302d04031130040c0c840c1d00304400e00c01c80c02d030032264005041d0701552a503d00041d40310203110312101c0442c031035642d83c1c000c98140884107458101c0c0000c46070b0104801d0800703060a9aa9400620484132403004807107030550424503610030b031401c0311500d400512200100395203e102401c18003407040c03005442072041d0000740e6000c00030115420300d9a00e501c045035041c0302d0300420104000c21400b09210b5500e149052080d80003031800e03400b03151840e0020760003981941c11070f400d400580c003c55051501255140700700f816088018000c0c0d1041c1d25424407695503400c2802042c0c0303107284402c09600604940a48a8003260040101908154119840b1404002d449025100c02c2e001501c1016020f03055400b0950241300311a080071000c00308505515040041e0140f01089015 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 953268660 1250 953267410 953267417
    0x20108010314150c0319020a0912080c0303070f11070f5a03020901051c0b0c071e02030606010f090e18160b1204080904050a022a070303 60
    0x2202e488004003403184114407000003040c2200d0703003007101c141c100ca60420703a9100c2d090200407400780501c48035482180c0443c47c0d551600c0c0c0103240b601d401400e06402940081c0c440311000c100c01102c3d1142030000f184211569103920650400b0810010101c01941c19034414661040c0010b01103070103078a120400711809000450510101003401c50500940070f0b03d86411326030b1641c0701505881f0100515100c024000302e90504101c6240d03281c2600e004540303c00782d04070803040b00611031f9080140624132028040701d5100c0780213034a0703076032484c5412007110780740601342d000b2503c10b082090085040b24a0f0340a072040702c4400000e41c0019449a00282c4218103110f00304440c0c600c4580615140c9006000c440c020956505d80160a81282d000120409001d8003e20220422000748032001200b501d40701800342d41440c0b08080e85210303000c8060010b83e0203038010b0154176880d50b0303540a401d1151007501000358440825503134000d003900d1603002050202c84a011514007d007000203c0c0d000312a003625 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 953269910 1250 953268660 953268683
    0x20a050d020612010608011a0316050c03070c08060a0b18010b0a0e0a0305030d0e0607082409100e07090315050a2012132a0f0815130201080103 63
    0x1002800b90b02ca500c0c1c5040c1e000590340000a51107411443e080e0480d08409060a01c401c208800000c46110886d0b00b502c040c0c1025480b0201a48280090001c03035003000b04807440d0402039118006241d001c0c1c1c2c4921170f103034042c2c810440c050f14a8000c035260783d1402c1d2101a462071543c1640b00000105005a0140700e40120345d01c01d5441c07041e205d1007201ca07005001c44404545034140140c0f1b0b988180e00407004941401000c00c0104000104140705000c0d41c0d4a40f920f90319040340a0709804080c4400070500d104041e40d110030742d9100d03005540035844500000a0892400040400301c0400030401401d001010303401300080341207040060b05060303803204000303000d07982c0d10450f00050002c01804030540307070b021009015548144000b0440100d0403c402c020558402e0708203500c5000d444001440020002c4d400469030420707005c030030100d0395101c04171242c590f1184040040c2511a91003403000368092203482e0032040d40518155000300c02980c0002180401e0340010702400d10600c80101500c1c3c1c3e54 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 953271160 1250 953269910 953269913
    0x6150c0c09060411040825121403040e0106081e0105010906030506061605160911040e0403110d020109150c080f04050307080a0809010b0102060f01090f0603051005100b0304020a050d 80
    0x41d4011128000781d190129100ca45507421547d40d400c2c0d4001d400c1402c0d5005d803001d1540254481e91100715910000c084400d80ca01c0c0d41d641100000f01009241140310502011682404001c03959001c0d1040e0b9403490014540040b0308889110041594843c60390494010311299034025061015503089042c0451162112000300710503208003600002404460403074801004000702e0040c105680305c002c098080d64a40300e1010840ea00e4500c101c590a90030001003154085161919901c18041e06000d840b48902161980c1085042004000140d6554038060304005c0482e0b0440c2d1620090742081041540d8201c2c0a080d8810280070440c51002440000d002c0020400480c0c0013240d0080361907403141100e4402810120066445c8099035082a480000c1948006a01171080c4105140309120364a064039150007043e102d80d0160400e61100d8000c00418400c000144c01d0485400700003426250681c103000100b9a0741c0c015001041c0c082050001503501c0c2c000c10000ea50003100c41012042c4103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 953272410 1250 953271160 953271169
    0x721110408010f020901110609070504050718080601180b0a030f17070303020301051203070b060f010e120604030e010801060c06150504050a0e0706050f270a0e06150c0c0906 76
    0x320350001d00a5801e01d40d0001c003005180c2c01400c904c21080e01ca40100e9640c8665047c0c861004407141c0b08191f2190408010742c1c501900600e8000f1101e003012040d04001c01022281000d260b00419015485030b401003081120305c5400241a49850004020700350840d00010b19141e607612000d41307c000c4032500310b0203001200e89002c0c2502020320f1140d5851b1110302c0c000d4041d400074030543d4403c0241c40590214294048100c03400e05510001000c0c055480404210702d00f110407001c00c1c10007091522509660702c60328841d40c254840640144000d180900d0001c04c2ca00005107002d04200c07048004102d103641091680c0900d650190000c05c1c200742e4000c610a03481034941c0b0850b8030900300014450b80249903408101c001071150242d42501c1c2e12000195690f1003050000814003204028030000b42031101c100000741c9043e413901c810018550390024844a0310784d00003e010f00f1381c140c180b1a0500e04142040100c3d10450191400d1001d4860314075110411981d9a60095244400285040c3c0c0d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 953273660 1250 953272410 953272417
    0xc02071502121303030e0d020310090512040e090d020d1407080d0908070b0a1503060e0f0a050f0c0102160603020c0a0204060902210c0f0f09060409090b072111 70
    0x110428841d0f00c8249611140f24003800500c800d80108003500c0300300d1650b00784402e50b0a910780c2c014000301048402c0034503c0d4010b1030701700d50a8a0300d0140c03004c0b40540100c0030001f0b05c0208070401076182d003810206005814140c94880d44401e560050a2940c038003500540c06101c03441c3c1010401c4d40b105907904001d6403501c00c101008401c58540802d000400003407030060480d4500401007203085603a0842140215010104c1e04030703000c0c400080c1000020016007100304280510815607500000e2941494a0240c1e030000840d40d64010581008182004000084043c0b0b405d10081091075841000d94030b504a0a0184004150f00040d0030003581c0c404100d55000540c0c06402045030582e25441c0b00003d4021440000107000703088010a0360481c0403d025000fa15858401341c5022100e00451205600200b060520f04000340030b441c44566810000e000203158640d408030703540906181281000c01c00410042c28000c120f00301c05808091401200007152104400095031050102820014003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 953274910 1250 953273660 953273683
    0x12160b0307020f1509060f010b030a02070f02191a0a0f050a0c050607080709060c1a0415090b0105010905011b02090702030702030a05030904050c0418050a0b0904061e0c02071502 78
    0x2149011110321070480d00c503454420000c1174180c0d6115140e40e013140032034090a00c688502803d0038004030b00101219401080418030403001540980c25543c08a0761080d0325a424100b20003a0f0f030002c00108030407058250f00b40c540d5091240c40c22a00d2a0044c00032408021000f0130002d0114000095a001d0302403402c5540d003113802c0322451f1078030500041c228101107800000140c0d0baa007001a0540c06100c9241c0c100364064120140ca080903008c041c15040000c0c019150441011100c282c14100c9200e06030a0b00c1c05032041035020b40c104400035000b0581c55020504000118550002a1100645a410f0644d0440d0300001c1e60700c038144128914007a5000180d0716018800e010001c0000002c024181031105030340074040d581c0c0e0151044050b00441c40740c1681c1c00c0d044c100908204070a540803076407100282e0400558201c40700b0105520342402c071801c8070b4140e9030b40128410f0368410720040c001c0000003030040c400d000f500b2100035150b0001c3c0c89840b00e401c821410400d882d600030b009035407148 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 953276160 1250 953274910 953274913
    0x515060d0807050a020a0501230c1f0b03070501140904050702010f020d14010e0f040803070c1212060f1a0304110d030215070c0c0509071106090c12160b0307020f 71
    0x70202e070705005441d0769400d1000c038420511882e000a1a501072400c207144d01400030360348400303900d200b541400154046905085d9030701650f84038803129603046940c0d4980d01c00b004400100f200451044c14600401030b0003160502074144048180215103404803100d0100a840200d0142c0314944107a002d0301502c6507401c1218000f266024914907294041000f05008170400f065690365040b035240200d20950f803004101409600203000308410600440c0c000b20709140c45e9010014546603816589010401c003070024030340c041035090700d0041d0301401002e8084120154801340c9081c0e411004520405898001d007440800054180030211000100712480a131a150040403a464000d41310034000030114551458030000c124814402c5d510800301d50342c420200f03407400d41030801f04026408000c000508205080f000c900d10302c00280102c038010006a001000012011020000100501146c01c3d0f440c3c0c0c0700101e9580c00c1d400c401d061100700d036600a092607030f91701e4841e812410004038140b0111207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 953277410 1250 953276160 953276167
    0x30d09170c0607290a1e05061c0f0803040b251e140f09120c0a06110a0204060b13090908030708190204081c08130308180712020f010c0515060d08 64
    0x401001b40c000f00903070711200c0c401d03250666200240104850050f03030400d42240300345450385003c0c128004002052402000d1001144071242d94124043d441160100d91030344c001424400e420407180c08102c3c0c0c6003540126100320103540308d4010031024544090102022030903d117502c1f018040e4651a9401c0304000d140d51b030b1540031000071141940000403443c02103c602104900503140459400c500e120010030103408a8680501141c152405c44144041402100c2c81d020059580340f0030300300102403144e2050344400d02c0e044074808030403055004c003042034200925400010224400c680c1d0082d4a42040d00141e110303184520b600540404000c14500d00c0010085490380000603826002c0200307600350045041035002c11126004256500100749034180d950000213405224030603482200c5891070180710b0f003c00e0055113040b12590186018001031100c10040d402c1c461a5901d40346001c0c05c0c600c112040b907544150b40c850394a003200b0760103200d41c000f14000ba0340d031002e401c1c10160001d00e01500d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 953278660 1250 953277410 953277421
    0x40c0302130b041406120636010504051303080c0307051e040e0711061302031c180519140103090b040b0601120506031209060702030d09170c060729 65
    0x56035405401640030340039000744c803c90030b441c0035030444c2e100e840400001030007515950240000d6108140101d442400424141c4103165112142000d8803441051020019403510043c08220341010b4070301000c05100180b0356011070341020ba40c5401c141103450f110790700c0d550504201c030140104020240c440c1640c0c442e0040c0c4145e102e021b0301c01d480303d81e0014030007038841c1c9a041d05c0180da495454080ca40120000582d5040ea020300340541900180a6030784200c4001d003843d041042c4090500301003929042100301100041d20000050142034951001150a02c040f492401406100701001c13002c0c46200390b08a070340b0980291191070b40c007612502c0c0a003058508900c01c0300382100c0e003d0010f229840840401c00329401220301440b0080c001e010402880704420740580d004d0750265403c060b081251500680b01003210b03295540301a40d4083c58103052882ca40c1d2440c05001c400120b540c040071043c6055503881040741d4580768031080d005000c414a50b00104801d0074101c45506107000340c810401d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 953279910 1250 953278660 953278679
    0x20613030210020a110d1124160308130206071b0b13080c030a110d080415090305060a0209010f11150106030b010f110a02010e031207080a110c030c040c030213 70
    0x4131300d480780c000f0f0313201825a00c05003c0d0302984400c01800492020541c0c280c2e078184500f0440d442c46480303030346550a8041c015042c070650301081c5402c04081d020300c5c00c2d0050551120300d11303820000c0381e07604000c85e032503a80004a01d4043d0010103070000d035445602000100c010748039400200481ea1801d510b0300d414640c215541c0d401d92251009034052104000c629107408101a520654040c59040c6031000081c20b011000308180310880d1211070800010800100a02d480381302d0b01c400b0381c0d038034241c58107500d49242010405444000b009005001c0418103130b0300000e20742c40000c000e1030000c4242c0c102c001500d20382485041c24180400070000045812541604402c03031034102a26407000908441e0402c4400700000407100c09690031010b42c0c1801580702c0c0600c0310290500604076442d403010f444da00d06055100c550100c0e2940c6c00001d004820b87c1c0c010000c095103024400161180e040d0708404661284d01940c6141c0c41503598000801c5640c3c00f940c1950301e800b030f200807042c10854580720303640c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 953281160 1250 953279910 953279923
    0x60c03060608010e0f0c090303070206040f08011d1f0212040b061002032a150106080402010e1020031303080706110301270216110a09060602030702061303021002 71
    0x3a0005a0000004c40d070321841524203806540c008000e101560341345010203805401c043c003903581c580400c000890240c1c2e2024054005043d618240e0103086140490843c01c641c1884958801c64143c0f01c0c18109510010400011403891030030384040c081c1000c007642009119612078030240140003018003060200302e50005120f618150740b840c80d03a03070107110107a03541d000e81340c85440d4034545181c03541c500c02e102d54140c40c0b10351011012601d01b0003032044c2102072648241c0050002030040700401007550390101c03201800075400d1b82c00034070004107454010004d0310000e0300c1010000f110000b1080e000b40410440d40c1a0500c6603290420303076182c3c542024242c0c402e14058510300c1c10302d000110030080c64001c0364102d4031000c50021054003240d02c0440d180d0505261203a9140e400e00075030358090b2000c4d10b4200320500c44c220403801503034071204000b014290741e004502080c4c0340850502c000c07500042190240ba4045403216200c030b81c00c500202c11008183c100035000b2481d02e42264100e500003409 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 953282410 1250 953281160 953281169
    0x4b0e070c140f06060f0325080319140909010905071101110d050c03130f0c08010f02070312050c03070518100201022703030a030914010515030f03092b060c0306 70
    0x81e1070f81503c0c4c0701e0030013802c40d10000c1126456008416507170012810960103009103250222000c026aa403181800c1c2542c10a04070b24840358944090002201c1c0e0184201c1e01d009140c0da9a141824029030204580c40ca050260020180e680c001040a40340107400d01d401c0448504024404180c0100c015800c0d500804818072200b810040840c08803204903054071312031007004481650108040d203500b0f42e0040390f00002c0d01d6007800e46101140c55603007800303030420303403c0010005a03441c02146001004241c0454000c1c407514505018031040c24140d030700300c907084007041c604652110a040e41d4600f48000c40041c031a07021f031006803080320054064000d0034041c40750070344100349014550413840840504e01c045940c0f507007007007092032640d5029600c03510a660040c00c80a4025291110103030031200180c4100d00f41c2403007842c212039540750401440300c00c0c3d89048007860070304847c00086500b00990340700d0011080e510740490781003c243c030f918100e0015000402448080084039015005000314041c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 953283660 1250 953282410 953282413
    0x30601020f16060f08010b07031413090606080606070b0c0d14040b10050607050d08181525050405040f0b210115080d0809074b0e070c140f 61
    0x136840c24a0301034180981201c8100759054a401c1c0b41c0c1e54101c41003218010785914407142071003052074802003a00c1100240100120004041d81808000f0309801e400806442c0300d5607040015100252401003059004900d024440f92a41049031481021f00781c1d05420403031100740c1008200500c0700201c0158091117848142103441600d134414005284142c80c000713400e5030b12000c4030f0124140308540d416400740350443c2040c14030311507111044c1400d0709075960b8862801c180c4148581e021a654003800545020008c0c5000ca1001d080003500303c1c002c034401c3d103101e41d41c1da000c100080707034550b0820540f00d0300003071a0315081d0a000781441505404a004403145600e402c0d402c030104078407103507084103944140000340121290048102d585c1c54005005a0650150380000182e072000a0060060740544040d10140040104d42822603800608012454155914840303840c501c0050b214005481c4500c520101035607450209890007540d0f000c004107002601c041d012203801d03000c2800c2c1110f011550 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 953284910 1250 953283660 953283677
    0x1e110301050a0602010e031602010e10020309090f1014210703030e0303071509170a05070201032405102102040e0f060112091a0f0601080f041205030601020f1606 71
    0x40040317080361010058944503910811003a0304010f078090040915038414500031001210000c003046085a14000c0030025034808034050181e881c06c10605607111450541d07400306c52800400040011510740b040a0004c02b200640300c049448040159442d184c000740c4828610003520f013000c1c1d031103210344020340020308119200c4505103800701c01c4a0b80903030041085803011020802140090008080444510019558ad809003041e1000600000c4401d81c07500c60f19900706000140985424000c4c400d0241c06004400d04100245c0080b0001d82e501503d01c4146030402c0c00e02518080b0b42c07074103c4141b030303c06030481070145034007a0000c00070340d003000c401c000742604c0f01026034494460989802c0d022030300d0a0300a90000c6030540c80f10f042c1600904501898203c1185201d065900540d507192505c51041c08101d155604040c21031341003008429400010300e0f180e162015800701100000b003c03c1000000b00d2001d0b8400c11032154070104100c1590045100340d0103005021040d4841c2d07801054135030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 953286160 1250 953284910 953284919
    0x5030a18080d0207050f01030e07080c0411271c1104110c1c05220302030c0604120f0606080321060f0f1005120a0c120c121e110301050a 60
    0x40340c0b4503070b05022074008000c0300c1c1c01e000030403400e001410801410190b0314111000c04020402111004081b118080d0546d003a01c2c40c10b100070340b580c045c048403502204010101449902440301032199540c0d59a9a9603280354000040074085880c1a0343d5030381620a07030307130b20074040b100b40e0404564000312010070a00311100c41340700f0540602c200f6007007180c1000320300541f000507904422140d8507140c0380140c42e00500d50040900e49000110a0f9200000e01006008608080010214540d8102c5686052a10707140201c00600d01c1d4110092a42e904420464104656a04642c028003400001c1d680c4030200ea006100821184c2c0b440c000c8105050808200729061400586080c500c0280012101400300c1043c006502518010311040283c100300002e100321000e807225000e0900c2c01c1011030131100910b8003e04905518410603400d9151081503010140c100780389244100040c00c3c00b04002c19130910611036614000b955081c140e003001e814001446000300210306841c42118901405034a6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 953287410 1250 953286160 953286163
    0x2c09040503040509061813062315030a0807080f070c030303050601030c0e010c080711190f050f010801090e01112a0c0105071401200702030d080411040c0201020705030a1808 76
    0x2e12042070040d1b00e000220390102d0040b0066440c140c000c031401b1884070260903602e0a481100350111010707040c03003070a20508801c044c041200070141100140f079058013031340b03c41520f4882c1d07143c02802c1e01d40c001500000f402d841e02c2510901a0800018000303540c0d2828080c002d0f04084170300c140024505040c003091207008208607100a44181c0d1008100c0c55540d4800764190b01c40310051b1350300c040700160305086640d40c2c0064016400031032050711311103140c800706a0f4444256000a403289001c2207540845903480619076044421003c0d000c01c9c0d0090b6500309a00411445440443c2190005418140d410b030b0822081d080a401060106135010b41500403510717400c0454680f4000f0750208801c2c8049a11040d000c000618800d000203940c001c01b01d0b1f003440b000d90a03a82017550410201d04101540b609100c034481c01010346c200180c85203030954030041144064101244240c0c1c0e0385c0d02d004c000c240301354156404030f030b0302c00c003120394071411220060203094142041d891110005140821501e10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 953288660 1250 953287410 953287429
    0x60a050403180e07030e010e010c05090102070f0b03271204080d05040e040f0318030b0a0501061d04020c1f0501030203060c07050304330e0906010f2c0904050304050906 74
    0x1401d02c1819080d03281e0b0311003117001d040c03e09651480ca64035243c41c00e00e190002e01c11010603181e107840d22a030311685000060309020003580b0200610758083c0b020880c2c840f921044950184120a425942c10303022888242c1c2e002038455151140c3c8915003030020304400b00030040080da00f0280455486030030000f0211801d102d03030700400060211a10101e400144465034115243d80709080c40016481071fa80d03c00c00100081c1d1069603040c10232030601100403a688143e50241c121481d0690a000c802c8016407401c488001701a40107a0340014003040401043c4102c80801140315819171481100320710081c0038003400e000582c03183c040c0102140c13a400d020300807190841e901030041c50815281004d00001100020803101c2c1c91808407400c01d030080103400d40c007034484500b515442400c00b0600305120071541c00402c4503060040312404c05400741d0700062080c02d025401e4000a05805070b2414045014001c0c02c003698000307184005003c20003001002910a50380309032098a450782d1084e0403ca41c808 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 953289910 1250 953288660 953288669
    0x40e3004030507090207020a050d0303051e070522050d0807060b040504170a0519051e0309150a0f0c2a020f01030c030b310903020309010f0908060a05040318 69
    0x50101d0f0041050444075006404800e000a00130045955614080346240500c00c8007140001d0755a400c119848403003440a0f01c00c520b000410600030714242c0000f605c58440c4042e500001445d1030f003554000b1a001d4440e101800010388591b4803070b805032400525942101d5000c840a40c1000310300401030400c0e1044038803440e001000704021204036010a409944881224010010204221581c40441c00720261034110380f076442c95500d40d0010450381c40c0d09003113241200e041004105000600c0c0001a207215002c00c40110202d00f5200d00d1458001462a2401031440714284460702060035004000d6241101c80e1050082d10900b0070508502c400900c0c04000b5031000003c0c0703d0000651182d44014068401c1d0b00340042c104410b40c00081605010440480c2d001c0780d000124144a5020341d4600356952525005219592159401a40303c0c0506001c4030304109000260311221032160300c0c1100203140001c04c2d59414281544044080d002c1141d0550203d034a034102800c1e0120383c0d548400840c2d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 953291160 1250 953289910 953289913
    0xf06080a1419021309061d0606040615030f0e0d08070f0503010303020a0305090f0d081c14011e1d01060915020a110d0506150f09091902040e30040305 66
    0x12581d4204404d00c00d904111034101c0e0b654010340c1c030016840b4860342541c89170380f10790b81d0046000b2080341e51405000404084c01107003454000c008000b070344641000c9813442401c011403e0304070400504021b03d011100711106120b05d5951310001500003100c9801081580e6951070300d003608004c169020321081c0710080059000106580220348928040c1448280062555402548610000f8014400c100003601c0e00a000501110142040b0762480000c000409040c0038020000b07807045138110f814841c5a0010400300c50204d10305040b2100e0002a1150043c1c4000c00640f03c4c1410003a02002d000d440007003050314002064030b52807000c02041521490340201071042242d6903625004850a950743d070810514071075000040c0d018411a072045640d003607001c5400300302c8801c1149042000f52031301d0240e850312040c0080c80601203900003051240020108441000780301242c0204080b00c601443c1c2d000b002c1848100d03a410040346a074042e11040028864096031064820500c25880020902d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 953292410 1250 953291160 953291203
    0x20d051e07092d0503010c031e0b0d0210051605030a0305010f0b03071101020f18030705010503090d1b0804060806102a0804030f0b0a1103010b09130f06080a14 70
    0x110051840ca407003501003401c0030000e0b803513600c1c1c0200c0c0c21348480d85220b002081d1a5113207491180803800302e8141d40d41000c10148400080b02001c21100020a40d02074040c41c601000020484e004408542002003054030a07050b07200b01d0b040071500c0713402180448000038204000044c1022192080c0030640b07030000380e0326281d6101c4803026101200c0c2100c5400b2955002d121541c80364804001402801c01c981e000145d102c0030586c00c00d0700304130041c0c02c6681884024008e000c50799030300240d11002c0c451541412107043c001210303851514040c1143c000d00c1c5140005002c5a40790b0321400d44c9008800594040d21640814101960034460581d03413141c0045080300f400c016110b04841c1c0210050103615014502503c03a261081c01503c0321000390341003c1c0d10024000d280c2ca8074801c80c0c2d0b52012809000f030665041801c000c100780320f40b00100b48a02c903000011843d90f11198044490b501c0d40703d0040181d02c1c0d45010305519800c0b02d00007543e0104148203c16180c03207001c900c0d21218081c5010703681b00e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 953293660 1250 953292410 953292449
    0xa0302070c08060108070906170a02060a05040906090f0e010b09160c020a03110a0b12040206030a0f0f0c0f020102090901050d030915020c12030909150301020d051e0709 74
    0x29001108203440030184040e0006004400703200d018080d18581011b8103c1c03509001c844820b4850f03592100c0d0f6101011084642c040c800410141da003036034101c0e40c41d5a541c01c5032004640501654015a590701d107030180004000140340c0c4440c0b11507096103024840000c0349040c25088500c030702c200130f400c01d451030005030b00f04e24050745c03013a0412480d081420700622260003042400445d50030440341a04040356131452071414600303910003444444081807401c0c0d90603500e0009071401500c0280200c80210210b04102c88503001070030f88200b201020010030b101c03040080c0c05130a800c0d001c8004180c20404510f00c003803041c001c0310704030140941400315591a102c01d22181e4064054242e08200d5002c4012450810342200e4a40001130769000b00f5140040004001c1e00300c42508121b9803d82c010055a51161a0b1441036a808001082241a0148140c0c04207029100303d0701142d0406241c1420003003441c1010b0b120f80c4481d800f1a00300d0f42c05545884096626103024007071800341003044000c094 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 953294910 1250 953293660 953293667
    0xa050f18040c1d042c01140f1e07120c0320040b030c03040501110a09081504200a120503030a05090a03120510050406152a02040e12030408040314010b060a 68
    0xa0148140394104400040c3d01e105210f400045c0c0b140d842d075151b4581c860480c0800c548542c0080c06400f814100c1d00b408000c902d4101c0c051422605503010460000d42c00c0360040c1d5004202c0c40300d1240070701815262001c020002e00000392030901d489200c2d001503102124410a443c1030f030310008405460742d103c1a035031110b1600700400c1120310399200c03440504ca242504e13002d0621481e0a4a60340070640c240300a290610901850103444031960780c04003c003054480c190110b0a5000840d2109000c1d01d0001107842c84840c0d40081151180c1c1c450b414041220010095101d10f034417183c2000907445001d03046072a1510070742c0141c001041001600d614600c40c0c2e00007034000a0740d6034407185581c0d6800200f03080c2e50503940450000341041002039089a0400d0003a40d10110340d201000c528040128404120441c6070301c040e02465841c03440b255008400c0260720101501c00040e585c8a00c0e003450030130155070003400121442e007810b026042140e41c050080d0041c00000901c424100880110103c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 953296160 1250 953294910 953294921
    0x140d210f020d06151418192d05030307020a032301140106120b1509040212132a0608060612040b160c0c06050a050f18040c1d04 56
    0xc01440d030801c60509082d8051280100400c00b011480e0b441c40d00412010301150700c3d2182d4128203030380401407030202440d0b00d64041c0c0383e000e08451401200b80f03403d440e0160701100c2e0308400000003403a00200529a070364000007141141c00b507078800d9501d4070791081c0b60310b900513880000d40203c8102001d10000d001d00c00c4034092840c2000705025030444c0007003001d081d12984050041c1204010005010207641305c500c0f500b48817291017003442801211000300310103107154403141192030070110304060241d0b95901114104241001808001d0402d0b541c144c588001d10f0740308480440031550988a0100c2c034045003100c809958444410f00c0b4601002520001c2c00144011f80c0841d00300302e240403001301028040d001d03034011401805589004040c4000c1003950014078800d100024081c1740c0085c12000880050302ca140ca80a07445000410b01a01d00380601c0c40d070021188404981a05a901c5485040114003001c80b01440144038014050b9116074500303c40300c040746508021115203041c00c2d00007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 953297410 1250 953296160 953296181
    0x105240712050c030703031415030a0303020306060705010f27241805011d3702030604150c030203060f0f0109051302040302031c2109080304140d21 65
    0x49440c0c510042e160700d040d58411703a003ca01081c0e231481004424904c2003907040d4400d9803000c2e004401c44114001030ba450480020003020190000002240b40e00e4841c103503180c859102000f030001c07401c000b05202c040d2010750041da02d080c404084118000c3d03c82005c14002642140c260080c1c0c1043d040d20140d005480351480c00403a886042026040040305503103042140503900010b1800342d0107500f030407443d2810a51620607840030701c50341c0018014098208410081c0c56034003009501200d4402c110100c8810081c3d0306014800812050040545402480e014810420440c07030486100a5080340020b4907025044880404c942101d4200380304000a001014100940050364a200154464801030032560040760007040400031418100a0078070440300103941c50380c008408000c014100712681c0d1802c450301380d10b010100014800c0da880f041100c3d400040c11940e925003030909419651010419044e10321030403002081c4980319a580c0d01080100903e5107a05100500c10003001d064038a21 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 953298660 1250 953297410 953297417
    0x100801060c020f0a0e06010e150f03190c0903061107120503040516080a06060b040506090d0c030510050610030c1e120504030f0f0c0206032212080105240712 69
    0x15118140e984a1418000a040100d1000200c1c508400018101c006c140304850003000042d15600a4000394801d031511a4004004291290341d00700712600c10410cc034100d081504d03d01613800c004554007148103820360340554410701c1000c48001911090348600d10010300061143c1d859440c00701c3c0b1a000541d0060b02901c225910710100d4610f030f0864400d60344c420309141e40700c01c003d5800c00c207407405483c004040054415040c10300e05404a0400e00c141070b10580314403e907046607410800c15100341c502542d0098211b40411880c400401c00401e000e480c604d1081c1d458079500040035119000b00445201c04d40c1d103000c0030382d80120301014000c101403502c1090041c008010a66a4200c1c03203410301c10350090384d4070002e070307514054094038100075010008200403a11141c5405615040200d171303080342e02820052410001300303401102e003400e0004000d180785034070309881100650010245060b180104c44142880320300340c0380d00603c1ca0851203180903151040c0040004143c120350042d013000c0080c01c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 953299910 1250 953298660 953298679
    0x60a0e06181e101a12061c06150e010905061003020d090212060708250c08090d1b0b27010e130c030c0305071704020f0a0e090c100801060c02 62
    0xa42a4400822150071142c3d407003004003004507681c40002011422074a4001074606a040980b8517800079006055502072a1030100300d5214540d50101e503048950020810400300806545000d580d49261045181c1d0110200001c50041d0081c82043c0c016000284200501020280154080d401c8101d080520542e03802003d40541c41d00303d0f10455002c441c00141910703141801000c0c1200341d0141c0391122180200100a021000114003035201c0001410406400c400b507284c1440c03148900582c0a4002d02c030400b00d0320820102d01202400c4400d54090210000e03202c1d54640d890b03010b440d00c599585441c9103501d06941442c880842010401850000204051440071402c1070f50382000e1144040e550b44e420410490b0300d0b1081900c1e21006103004e10480c141100010444414626245800d120400105003159240c0c60080c6556002812038180d0756a550b811546592003203032070703544a000300c02c039a140e5850010360060182c0c40544602c440c81c1d0074031404507420000060300701c2e088881203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 953301160 1250 953299910 953299951
    0x4020a0f121107050a150207020d08030c1e07030909110f070804050a0b0d0f0501120602130510090e090a020114070f0f0f120c052a0a0806060a0e0618 66
    0xb4010210540510000c1c50321542901e05085010780c1c501c0b0034000e81d84107002c0034006a46841e26482c0c0d40760005500d68480d11141151182c500c2501c0341d000c0300c8100e00c4401c80c0e91204003805403580301e0283d1283c1c21900d565001010580d611200e10314000702080010450f09025000903003101c6024202d03840c10652900d01051521032a60081070003104045100440388006005d4034483c14100351090056525092602901c000305680c01010141c001c2164503400e818440c41600405d8020010700307050902190250054016000e180242d9000c003002a41e8034400048214030780354182c0d035180c0865010210030420340c01074441200d0b84a0850b41c5074001c00d001e0003111404034015030b10080c0c58081440c2c290180041c0103600418070000100790030102d480468401504071130003440700003013980c800e1001304a109103444550700c03000c4c80002081ea141c000601901c2047d0540307131141c480b910380191800003602107c081d5031111941c02c0c405030385141104040d400035241c10b052138079600e94 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 953302410 1250 953301160 953301191
    0x902030d080105090114090a0c0507050d090503100b0f4b01020d0f0509030f071205070803160303020f04180905010605060a050d150e090c0f04020a0f12 67
    0x2448900c00080c00c8100180000e15148984900404060350070700c03917455071100800c8200c00d0042445804566400041c180c0741e015000b191a000c1d40207051f200c048040340c80140121034580201030083c4114404001130204910407a091120024641120050750b81e04000092140704004040e51458860704082e004010a80c642030b0a820052030f151095030219030040690720000c0581154043d02c18030301c1c10764011100c54200c81c85441c5c0b05a8904811012a1400201543e2030f0801d1294400000c1c88400004500002e948110107803165546e42c0d400031580d0303004050703a0750800d0740c05002910000e80207034010300c0c583c55a0030841e41040d40e1084007100664000140070782d11a1100b11080800c00e080c82864003034501200d20342c1c02c10210240003060fa005152030004469910300c0c0291903d081d440581c0c000b4445411341854516280c040c444d04c07040c5400303030940140f280441c07482141c0b5050007030b203481c107509545129011142d20800c030340200440416201c2d807944c3d005601100780d071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 953303660 1250 953302410 953302423
    0x210030603050d11240604051005060c0303250f2604051e070b0d020c0111131706010531020c070608181504050309040504110f032d01090203 62
    0x8036481d1800c0341c4812141c40381c10320b084842500030380d684200c210202c11749a02d44440d0005030691703000a0342d544071080840245480e421040c0d1050f408504564031843c004001c6105421a1a40c50408244802c21242814100411001203501070941038482c521604400b94485000d460620302400c1e80d800c0041d08400543d01912117401034024190002d0324080c1c2d00749840315440040401602d084815020f40c0249554070128940000e41e42c5140e00003500048400c5e4220000b8995a545403481d00350050128820405900102a800399810340d020075aa0f040314405080d100141545040c22968980d00e001354404002d030014030025004c1da2403000d001c510103841c00400a850400c1c20240c52010005c0000b203094024131000200c00e40d0100d4412044c2005a0000c00d03da220b62031b00346d007103000c1c0c00c4100d03802c540783c0020481840441c40191404a02c2513074240c003a0041c0b8024580c40b400081e415031143c1e080105490130180c4021500215288114000995165142d001a0500c107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 953304910 1250 953303660 953303683
    0x5010810092c0c0306011a09040f0203100602150c0a1b0311160f03030c0f0609080904060501030b01020c0108130501060308030a0510030f0807142b051303021003060305 74
    0xd200d10002c00b040c030607500c0e41c0810081e440003c1500d50815000207603114014010720f01e00c107881609203030a94484000782d98034490018000d102c10710712207103071600a4104440710100c40300740301c0b000503130780d40080b80caa8009140f501c0301c00925a217a000041c21f40d40800c542d0010007200003007044001e20300c4042e28030954481d5482d0a102807202072411310b0b19003000500e00716503043c05020040d21040c07801c040100c070740c107007004450021241030200c42c1b81c0c500c10300901300f10308103000a0100500b0340028403002404542c2000603070703180c01c0110229481055111f0150344150985401e07580a16040741d40824804011215141a07568160a4424a034011100010080140242c241d0640109030b030003068428101ca01c1071541c2c4590244102d0b020b030282a60300009a44414445060380c074040c0085181c04030b0388103840c04014040203414412401da5a00165101848180e200c0e0040700c50303017a44907204901c85810340e003c00c00b00304859004201416a260030000020700107101400001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 953306160 1250 953304910 953304941
    0xb03040f2d0b060a0b191107140306010b12270a03030501050a14012304050d05030304020102010b060c120c030903160f0b120c031005040f090c120c0501081009 70
    0x121000e01d080c10481038040d043d01d01c81d455200042c407600500905440300503582030780307050002c0344580041e42c00d0481c0741c0c80708041307000c0c4403400301b0244041c2c1014441d5203c144e00302c40541ea65203000a03018000d014041500c004400d021903940b060140240e03080080c07240f88185081c04652031035203040300d80751003140803989031030041000345800d0f0400c000801c50480c250150f0b10508000034074107844051a4802c2e1500101096000d9011005a41c050709002d060300d26503103200e040c45079480c1c10459080340150300346081e036081400c0071010f480ca001d04682c0200140095602c03808540e4000461404940c8014840e1158550b0704000b0014041c0c0c43c100382e600c5090600e001c41d42c8400c010340000b05a000100104004000c040c202d00e80c0c400340c0311140d01c2c1c43c3d0321406403003540d650803980300a138007509141d1000c2c54140194803c07030300f0501c6034064800850b540d034001000700380c1c02107028120342c11350b000800040d4054800c03254040004284210003c0d203070001d03c01214900c0e034080044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 953307410 1250 953306160 953306243
    0x60603060d062c15070c08031302030303040606080f0a02010f03020f280f031404020405090f0708060106030b0a0305060423030f0304060c050c1f0f05090a0215040b03040f 75
    0xc0050602940c481d030141013002c20020b00e4840702c060040e01c48000c00030200180000050703450700100303d041241d0355005054135a281421300700f13038014048a003c0c1c800540280e500c2d80c080e441e40007814105280d410385455904040a0070103800a40145d000c44007030a604010320080700100c0c2d12280d94807480c041841070419451140200032402010001c0203040c81c0c07001515aa10800e030b485944668111400308440d40c410243c98103100da41c4805040c103200e0f9101c046400704011a07094180ea4041c0d50400102500c0c4d010002c0c1d446040c407010b0b06541144020801040d042c83e40e540394400800e0600c1080700c0c402c3c0050749140c1c070114914000e0f803000310600003082181e0180f103480340041d02d03105050126650600b42c4900c0807061468070f03c1c03010110490036041540003001c40c4500542e04110318500080c0442d124026400200c0c032a610560f0030240a0a0403400d480941d60031100c05e605540d100d0381c1e07803080c400e01c00c48141c0f600804e101d4031358588a1140440448004800c41e071209 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 953308660 1250 953307410 953307491
    0x10f0f050c0a1b120b0a0c12090f03020c0f180a0b0d0302070f0605090609090603011503030801030b0708090607052208101512021521090601080105060603060d06 71
    0x8800005400c104506040300c1c8940020410840d917403900b20340350b44c000240074140044107642c40383c009680b984582e0304104090044c01001c919022989002c1d4090301c4602440b0010011081d0f010748107141e22200800a441c1d08809164045d0b41c04840d1920010f00e298400c40001d00001d05480100c0040c1d2003100203200100c1e00c41c80c010003c100c1800d0a50409025000003641c6001344d0145502a000c20000140c640e5000d4100100484e047c603503c0c0105616410b008040e41402d00041e94401d00b078102003141c0303e108500310307440b40d0101c1014104540754031100b19420f03030003014030044400090740c40c03407a920310806c0714000604460000382182c80b4040720703401c10b89509160502c076001c0e103c001000898010085074095682c12640d09012801da01c00090b0b1354010a03001c2c4d00da8211154407111800300d07a4090a005101003021616140e0381c0d0300802d800d17910204d4429030000f50074030100e061410803120b4140c9840c428000410b1001c801d0b1403100320b100b13210500851062804d8680c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 953309910 1250 953308660 953308703
    0x1e060801050105221d01060905030a0f02040504060906020d0603030e030609070e04050304080706080105030c030c010f0e190b03091b0d020928050610050c07060e031207151a010f0f050c0a 82
    0x1809c099014052829848e00d074001c0c0711103038a038042e00840d09c40e400201080b281d44d00c1040140d91015085440d400c031203028600030f19160008030b0120340c1d950105081854006180e5229946020090103000d041140328403c65a001e00111082d20042c0000b2030003240074071400010384020783c2c81c070540303600d00030030980780602c54010180242c0103040c5004560342d1000d40700c0c61801c1d190410050120801000c1080c10b1098421a40050202c0402040c05c1c030f1030100079400b903100d403021100c5d0110f681a0341d6840c581e100c40303015070140301c040007c001070030a0540182c2c03102c40d00345808410b50110380c14071019521000342214130382d074803401c1010324079003009002041034a602d00075007000d00003020309075109141c0c014582800b141075122151590100281030484001c440081d80303800360303072a0010041e0320300f2102c1c01c2d00908111101350002d80550859a200005a48190f20076112a10035640456028408030800c601000b40c030403144410006110b102e4810103183d0040c201c2941c890 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 953311160 1250 953309910 953309927
    0x1209080910180b0c121c1b020706051b030c0c090f0f160302070b27030c071205030f0705060a1b0f030911120c0907050a080118060f1e060801050105221d0106 69
    0xf03915030b4800d007d0701000c40c0d000810005481c15070420542d6046141e60020301c0d051000094070303407840001900d100c070a0f00802c000315042e10656070300f01c0940320b04024140c1c84004903110741d91154040e0000e01d603401180103002072090903040044c074042c00c40d00c1e106001b240403644c0603500d44880810040c0840716205002010082c08040c40c1044210a15031703483d42c9071445042d180405e0703034022405110b002c1c000c5448001662071480d0391290710b4a407454071800210f41c00c40d0114070703100e2200e082c4414005840c860082030b50700c11003c00f250f10000d40c02004440001e580107070200320061460340b103c814010301d4404800040100c4400c22082102081c002003a04d0304224007406024440d54010002c01d0655008482c600003040918450600070410b551001c54145a42c500c00150116044420106440060003000075592200340a8407019428402d280c002103040110444c840103040344202104108007044035001c0da140070102c400254040400b001c28002d00040140c0c50b04107104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 953312410 1250 953311160 953311181
    0x50d140a0b181006030e071509060f090e010e15040f1e020c0a020603130c380405130204090c0807090f0602030f0a1209080910180b0c121c 61
    0x50030b00c070716015950031003060b690310410050644556840050f0b140c2448131001401d81000003d0f02014040310040812580b8419400401c01d00f02c1c086080314415100c8405a580a1701803824991030650701d04141000107051100c01480084d51001e16603c5000320a001480110301250442d080403889001000c480d03036880c205071041200d206110400301d4980d00715a01229a5612961105241c1c2003d060300c40000301403100f0a640850001c0d400b1100c882c204444841303056040744038824450f000c190482d5036103c1000c080c8810415482c003800c100300c840118001c0076003415a2449134001351020703002c0110201e00d100040114482c0d011103448000d00c511840e0054241c83c003000a91284101900040601350016140c1d52060042c00100c994809070001041110041c0c20100102d41103824442d01c121803202800400c0c51240c502c111692200c1d000200003070346040000c3c80641c1c07060401c01460f010301441103110114000190280015080041228506a1000310300726020300f90ba = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 953313660 1250 953312410 953312449
    0x1006091b050412030e031903081815011502070801150501110d0807030b061207091827030c021c020a05040207050c0118150201091101050910050d140a0b 67
    0x10030010142050140c5554a402d420070003002114400481e041c69903141400000c080c03114071f0b580070154000051413040b00c440d040600d1180c80100740940700c041d1191140041c105480060000c0886000c0c614840281801102d04d5a6540c05c451030030360b40040c0d640c041d04031354080300300500c4d60012022143d4496072006009124020344000e001a0005071880040580d0303100d0303a0156891310822650583c0e58070304620442c1ca0800310091080300580500041c004a00b6400e0015040e140599140c60003e24480030409a00742c5480240501d9800c055041040a12560001d43c032020586035064040000b100b0f40c25001e0300500c81e00c044035522803030107544104030a0000c100007240c1070100d0102440c040c0a01403868089007600c601640001c0e01c5101030310180e20401e60154040c5042d1841102900d0710080c18000549981c003c1d2255250040c011041c051007682c0700700000d0420142007000007840002800703140340944001c841d84448aaa162420002841d1849810995061101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 953314910 1250 953313660 953313667
    0x1f090305030106030902040204051f030c110d0e040621030f0f141b33010501050405061b03070f060506150d020901020a050111031b03040b04141006091b05 68
    0x6800824901c414402c0404060382c1d0714002e011540c070754040300c00401000f40700c4145034000c0d400210841e10b00c01070f00408240f80003101a08180247c907101e0864100c02c003d4494400c1c0902c054130203200c0c81508d42c1c1c0c084c0c1c1d40d0b00701055500d0802e020a0b6084201c089a003000300c02450040c1514030005041d00034014010445000643c0c840344840032000c0300c0300e01c6515408002c0c0104500c4c1c40c060510a0140a84000da1030042c11000c1500c05840d17058500d0f010801c505840c0c8080300d170081c007546001501c1004144400c0c14114001d040c0c0c107102240d1089542d000707068150440e04249001c8070002d0703204000c90b05100040c0226508240102c0780c0c9070b0392075529010385401d0310421034802142500455049000d078000c1c84a802082d400130002d0248030541c010214250b0300480e0010462021b64020003001400d60040d01d120b29480440407480b51181c2e00c45003918492985103200340d10941503100302c1c5c40920f0140000501c0004400f043c3c0c03400d0450500754500045500340104841031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 953316160 1250 953314910 953314913
    0x903120507050c0f0102190b0601170c0706020c07081c030c0206101a0c070f08010c08010b0d0207020f1c03081f1712040b03040c090e0a030e211f09 65
    0x4224040103002c200e07413074450a0b003201c0041c2d007007150420600180c0e80e003810100c0309100f21a11400d2141c0c2e001d9030340707286002e03207418214440f0b00281e0f42100d61840601504001446590003000d0b81c01c2c010080b40c1c03071140d0710103010749840a403445c400200c200a180c000807542c2c0600441d103e42605002405c40f900c0c00c980700407181c1080e445410580986405402c43c000d03007803800c4883c0c0351038140036104200e0311a0020341b500003040c400c01c0c0c1c0962030681e94402c030610510030281a2980c0d08442485d002c1c2c08090803001e50040107003a03074071040c4801c0904150b51124447d58a42c0518071012803181d01e0741c10b018180d140001c003030004a1400540c0595080d11112580040d102c44520005110760002c0c003107445c0a000710b2125030307580300019010510305c8500b005503100310f101c1c02040e02d500e03440b488140d094401d208204134650b4044010a00000e0150050540c0c00c0b00c0500740640802105100c1c100303c01a441131302d44c0e160011049100445405040cac5442c10660301c105001c103040b035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 953317410 1250 953316160 953316163
    0x80c13020306100e2b05070b07020105120402040605090a0b03010e061501120b0d0c080105070e09181c0c050f0a080f0307090506070b060f220f1803090312050705 71
    0x390161841081100360200788a079030b90070308405a49011000400c0e0519444000e1500c41e0b0317030010f00b643d151003140d0300000c03048451001c5880729039040c2e48441c02e0072248001c02e01c0684002e0000c03a07109403141004107064592008031480784003001b85c04180c010140c414582110380900d4140d001d9005241013214a6061506241d80000286480059100c076040610000c024411005900c5414a8070200c01c0c0700f484051002036600d00d20081040d51145801a01ca11004440c0150095140400a0020340140c81d40d000440c00b03580603030341b1250507418480b284148810408007c03454480056090220800c161603001003c4001456038008948441d026400360501c004888000000020010742c07040314071078001c09020300480d480b44403074034000301101c4d002c4a4090081490303110700401480d0802a00c1c01002d07004d0f5048510640d5445103901405542034440f0780d0346c0e20341301c3c4001c02c0038000f00c0f848251406a5607043c0c1030f40c01c501d0010320311035140d004002048428881e81d00881d40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 953318660 1250 953317410 953317429
    0xf0906060a140301020d05070801180c090501030e10050f09010f09020607141501030f030e0303070c0e060a170c0117070e0d030c08071a0a02070f2a080c13020306 71
    0x1030000c02c20359a240c00030300180c003a20540324000c0402e41404240440c031508201c005060b20702c3c0140fa80041307c0400c00a0007200d401000f6a4000368011408024550080e0b002e07030444031060003500d03013042002c00403d040e140b06440c902d0035105041e04121a00200307114118030b891704d45800b44403081c5035400041c114080c00402604ca0000300701400c1c503028040106102002c01c03894411030540c1e403070800c43c9841001c1e910540100300c0c2e40280540350720300401107440580c2d10003801c034a203900305006c03500c03180c200800b200d810000900d00845c01006140702c1c5c0403544000002051500d448200052402181d0f9496804400c0141c091008144c8c220310b104520a1060707070b561703182d01c285080460300124400005400d81000084440030700480c100c0c0014001301c0c21050000c240c8501c0c8000089104102000c0c1c0305a03115070510000550300c0c40c0c0c0c4071040d032030b41c89100b03669401c20010400b15075469001c008998072055180555050401d50846810f040103021402c616018004c5030003a034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 953319910 1250 953318660 953318669
    0x1506050d17090319020102010c1b03030c2a1506061706040209040e0109060510080a030e06040911120a090c030809130e07080606030a05031c0e0d080f0906060a 70
    0x1201002191011000782060711040c01000307040760340c0c0c0003083c841c02d14014013402059005500700003030299164003400c00389102c0248194000c01a6142e91001c800410b9040009030400108074030401c15004507004c203e401280b00ca41c2d03510720400314a4414104400307034100ca43c28030f0a002d4200200398003c0281007100c1e041002d06480b55a43c40000303070092140102c030b141c0c0305113840071300f409056055210144951003500c0801558990581c0000000e00a11031b40320384e544058544800079100d40380700804c9149c00303001641010740f200e489401341ca803244400142101e0200301e8510380343c20f051903590002c1d8103050800c804055030b181c3d091249200c0c000940341950010700c5c661142c844105c0203400031150042000402d801ca1241622410701e44685400c51040c100402e00524021601500055006009502d400c0e44e01c000710114400e0784e04000070301540c40c0032031000c076001446000d50801a5503038040c0c05250800394600503c03070241071100c2690100c41046199101d404200c2e007030701c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 953321160 1250 953319910 953319923
    0x203040e01231e0a030807021206010b0306010f020c0913030801170c04090f1401020c010b01030203060d060908070605090d27091a1215070c0b070813060c0c1506050d 73
    0x103110b61103d01c0025074010410316000900064000284141c01d0080c040284c42100c1307a14003c89040c81d903680c0d40b80300b8011030890040802c0420705da580a045615a0111613006a0b1071004007000018201c10701280c4502282100221827410180d02c04010781c054540080800d680515241c070345560342c400c080c0b106014035642d165a8040c450741801030034219034007504032001086420009070207504000740c44c8481d0745c00d2000c603079030a42c041c1c020341e8070030280640004c00300810307503c41d100a000403950a03681c002080001ca8040f541e10b000305c602c0341c0d012000501c00d2000980d001444207040e1070240c00c08000090910311100220002d0908075000c03400f0110701c01e080c680ba841011694a440176a0019450300074001d0028007103019658118054020341c00b0faa01c504050f606500f0361200101641004c200003405240200d06494000c40300801102c8000400e035205021038410005002c0460a4000b0b444100000300a010000103080041408054a0600440c0d20300c400c002004040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 953322410 1250 953321160 953321179
    0x9030f020f0705010f090803031e01060903020d02040510122d02030a060506120307150c030e0a030f02010b06030708060f01110304090506061603050a031503020901060c030e030d0203040e0123 84
    0x188101d00003001f902c08401a280d490030710300034030407010700081d40c2e44d50281d05010002603024007805c2c0d54011682c001d8200c400881e61a401c000041c500100885207292003e603001c0368001400b00c83c2d1180700c0c82039800700a00d0304c0c4000e10b541c0100c10360064108140c21045420016140481c5603040240d00c01d00100703290700c5d20800107032280c100c80d690701c0d454440807400e4004c2c13110303c114203820703481c0392081007000250025045087c0d03003844011040690003629040c00080c0305210004d03644000d4800000c2c060b8026000503200e031f20944010000501031001d10010b8500380d5030300d240580c03090910003c0c0d404100790480c1c5a0046109103d03401d5505e01c00580c1a888804c00c90728400d2010426505c0c1c0d06071894054001d800403000800028508070f038808402242402c0001940e4005052035070036803821a0494842c0c070900012000c1100082c51841c0c50784040001042510042c0c02450300d070360801040050020381607202031560300002c3c0c84400c0c50300c400101d04208807400c0e1469200b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 953323660 1250 953322410 953322437
    0x804060608030d021c0c050702010f2304080c030a052802060a091703130510120e011a0a0f03021903050610060f020303161110060909030f020f070501 66
    0x10600d0303500c101040e000c0003ea4031142182e0750300800072030420800d01c3d0025070183d900c800481d241d840c12078011aa00b0001c0001640c0503890341850f000301468000455445c0c5807030752180c10102400303400c00010200303082c09185403d000c21003440710250010000d5101c15180e1607661000d00d6003004848050b054041410001800001a05178000d00036070340d2440d94000080452080d403146002c1e16494076001d400800d0040100c91030744e555410300f50300d000d040504110700d04521044d40818070080c8007910034000400c0c003411840c8080d007400040e50a1128584413114180c01311614030415140c0402d0000400c1c111062042d42c0d01516802580100c40110740c1d5484a103400141040c80b56004100301c001000d6214410b880c1a80d4501c050281c0c3d015080e41d03240410343d00403001c1503207812100e00441c46070100720000d8490401710b41b88040e42c8038141c2c04681c0150000b625a540b02c1c0d0185081c1500322100491000d060f1006001c0c3c9101c05025a0301c0d0405402001c0c1003005845c00e400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 953324910 1250 953323660 953323673
    0x5032104170310050324010f0e070818100b130228020f030c070f0e090606130b0409060614180708090129100306060c06020d020408030307080a110304020d030804 71
    0x3c06808060201e03000803200e8081e40900c1c402c6c0e02c41c2401485102c4d000402c080c01c0d001350030000c4a002c900c0039205619001b40966506000620f0100340400c880c0d00d05201c040b003004032850700b6001d68800035078101c95105106203081000981e528032030040020f240790508951143c1900801e0b644220f00d1072103041d004070f040015003007849805100201c0d5042c2d40c0354021940c071088540451290a100382d641c0d802c114101c1c0300b141c0100b0309401980015602d814004400d01040c0c3c0115400a10401188006001c640b02c0107401c0c2c50302070b40d800341401840c40c080482003010b10308035000394100103100415403400600a1840c01041030754400708010f07050075080b4510001001c0d80038103240540340886466840d80304036103441a079408a407000d403580203200f903809a030590341d500480c40c41161144070281d44090000c9030680d60800000035000f9041c80690f000f50703015910503840e802d000300b40c41c0a03603c00c0a583c0750312400401c00e21005a580d20540316840741e040c281401ca594a60402c00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 953326160 1250 953324910 953324941
    0x60d032304080607020c01030c120c1202191101091e030e04090303230f070e01020a0b091e030a0813051c030524060904020714010207050321041703 65
    0x8403a05008500424001d202141d0148200200e501300c0d000c031400000118203070349079012080301140d01000800d2800c036003a00941d0a40506043c00650098240c4515080341e02040810418801d5200b45188040d4480000c0403c0d601e02c00080c050f400083e01e948505100c80b00f01c0008078002080c05a0805020b404881d420050003402000490000d080203405400c18120720b0040c9010a0b910780c800205146503240500302683c2000e249076a40307042501ca444100f00c0e078505501c1519000000514070741002d5209455000141445120490346c552003070010095403d00ba800070300c840c4801c540e00041d2581d0183c030780750300020800c100e41001070a12020002103036207200c0c0d0004800100c1e403d50803a83c0200c00c00c4081c01c42035180d001881840f20006003055500c240c0401c01000d6a281a07006004c108bc0074013101d044d08405c440320b132400c81e4001c1c00200e40700c0d0404503000620101c00340c030b0750401041c01e400c0294149456075070140c0031804965101c14821020010038203050008482 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 953327410 1250 953326160 953326217
    0x8060c130314011e0911010509040207150e06010602120d020306010306051c020f1801090906180312110901080628030b040c050111030304110d151e05060d03 69
    0x180940b96036044806029286200e0901d420100401d2068000c190303a00c28802c100350000088824800d444004480690140301401d9104c1d80a02103000401c1e10101231181d00314480760b001860750020030308a4240b0130160f0081081d07410250b03400342d550f81000c00300c2d0014220319070016582c4c0d50306d40050340108541d4010359000700813074985243e41407015004501c224000c031045c0d541a2040c008006508451010916110003034900410000e03400303420103420144150008100d03480d903903031000141102c00700242c0000b002000414a0341c001c510420300380108154070b40d0301e03095500c00042c1c030100d4040d1000c0c0c011850303c0d084519000300c0315501002d50b0700075508003100c0d80d80c07400d040320500c02c2030b2002d0300c0b0310050260026040d8000c0f050001800c003160080c60460f9656207841581080d04e00c95107030400140d2034032000081030324401903104207140c1340020b1200d80304106c1c00c484400703100e00291007078509400c1c400103955080100c00c41513414500008c003490600204450b071103240c0c05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 953328660 1250 953327410 953327423
    0xc0102190c0e1611030f0405060f04120804210f0f050a05010203010909030e041a12011e09140d051e040b03040302152d04060219030c0207050a08060c1303 68
    0x61000000e80c02490701e030003a03004c1c2d40c0c00c2c04a030100d041c2c15859104040f4000340201c4200820441030418001a0110040065007541000c0d51001d02d86000b8007090f4040301c02c00c4000501f40602603100c2d0100021030300c0d000907030b00741d850b09a440d00740c401c10028003c0c05010b14510180708000003009443c0a03154441c0c02503407203503035580050024080d04802207022507401c4121840c0d5060501c079145819440800d400d07180c0c4040c5082c4881d80c07121620000d40c654a81c100c08091404803007403051081c000c160000351a003000d06044074040d0400d01810303250b41081c03901400899110303044c1c0b01c0034100311220130050384100c0b10084c0b145c82190301602244c1f201004000600d0340108110000b88000031041015545501694041c840c1514000c80781034659440c0c104e00c0e00f4180001d540c41032041000525003400e05040c2c4490b07030030724180c0300c000036142d03618420020b41c18007440340284030540f100b8202501303195689403900401030003401a00c002140c0c035204000300001c0031000b5508460b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 953329910 1250 953328660 953328689
    0xf07080714070608011805100e0c04031208060a120f110102034605040311120303100f0b0703140a03150602030d1847060306090c0102190c 61
    0x40001c0c1c00d11400b41300f0074000d00f0b1b0071401003441550f14001c0c984101c40000390030303141ea4103011440b80c090310040c1000300304071024800813000403480c40e085628600162591280c03464104200300c0d04000c1500000c1980c515102204001a86c80c480000303580c0d031003000c1c3e01205186000407859400717011840e820001910844590000101113001da614014175059880d8040110000469000d03c4540c100020070030001007001c1000c030740780d0291421004000000e01d03080104000d155070001e440420041244030020458141080c09000080804213586070419000780c40180540c2444c03103000340660030014466030311610aa020f155801030390200c0c50410390700c0d0100295240c0003410100b00061505904254469000d1b8548940607032105d10b01151003034404955001144158841d007108108001d504510300d010441b0f9406005064114016813a01e0810103103800d00c090000c6810b9000a4401e490690340440c0b01c9404200b80c40e510919808580744c407206801495202100b140500c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 953331160 1250 953329910 953329919
    0x1e08012a14130f031101090f030305031b040602010b03010b1e0103020318010204120b0106180501111c1d090f01030807110607080406023c0120030f0c0f0708071407 72
    0x1003643d40107490103a1000e0b1801d4540ca001540c0da04018040c80d911414010030400009105000466102901422181642401d0545019035401541001c00507075103404101d225420240309880b60b540342240c940c5070709104507a006400e19600c42541d070416400000151807410082c0e40d207000841240021940d590342c0f0300131013410982c400e20484109600000002e0828072800c014400f801ca059048078a0518040040d5221560810080c0e4240a0440314000c01000c6506000705038400c0e0700c2d031150090344010030054403032101d03a000348644010303000e100c4203030728a1200c5070541ea4004481c039500d003918202440340403020b07400d00c0e90000d000940340040124000103403045400b6502160001600d60713510340310100c456018039084030341c0a07440000c0245045140c09a044800d00002514044846070003103802050b050210102400403e01040100ca5030105c0e5003e500019068108984032000207072034030642a024040107000701d030031003d00c0224400390061807412421204155585d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 953332410 1250 953331160 953331179
    0x7051602090423030a050d3b0d0305150d050f03040f1a070b06040c140706061d010f1401050d140907080d02060a05101e08012a1413 58
    0x11203042c544500300c43c0c01c0007840d40d40c000042d1010360b42940c56203410400301f25a14001130802c220740d0300300703c2000d03241050003084d850364a80c0303014100012085402c80307803072820741303040b652034144401c140c9480200500408400f4210720f0401e021210302c00441084c0c1405450a803182c03049030918000080d00144500300129800112040e02081c4909126038501a040c00d00403040082c10b40c0001100160b0149002d5101402c58509814511007440d00101c0c1906560050142110565a41c0106020500c2084400c0b44200c1c522403000ca441e60601c0140d402c2c007100e51184840140c082700480390242c1c0a0800c3e50300340402e40c00104003620040694901c2c02606490119003400340200201c1c80c2c1801081d156020b04454000f801a80c4036100784100518008104048000050f04046103891491114080800001100020082c200380b03106085461004080c0204a13003001041c1c2d01056410807041420310500b042040c040da04208846144200c4a085204400354400414820300303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 953333660 1250 953332410 953332433
    0x2102210a09090504050d030b0a18050a1503080a030e0102160305090a1a04211b23090a020d270501230c03040809031507021c08070516020904 62
    0xa0507654401040d50300c4029000700c42c0c043e140504190004907001c40414000d42194030b004401900c000c852581d1150351030003500680c484480d01e16200c90030b100b00c1a01e1401505c04030100380100a0410b442c60f42d4125280c448c00f1400c4c0c00717068070303166000e480d54030a5054030014681d0013200ca041e84d541d0b15006000340d0140c1c001a20901c2d40303d0000c1840e0044c07050309107102ca00088079078038150810030108000f00155038000e81885516030b0001c001071010181c90f581460f5258030940d080c0c00d2140080001c0c58812240700e400814801c81d245a07658250f1454120120100c011f0390340300040f202e40064a40007071002c01008041190180306400c102c4000891401030303008204101c05021b000c02c00450300000a80b140d10074001040191140100550b00f2602c00c03418075151100400c0800e0030110111488411000c10004100c9a1034041c03224805503440c1d80c5a40c1030030640e526024001c014043c0c42d0804006000c150141d520581104600e811500208114503514051a1949210a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 953334910 1250 953333660 953333677
    0x62d080a03201c0e0f060a050c0f1c0f0e090103050f120306060a0f0c17120f040f060e030c030f0c0c10020a0f021c060b01030b030a210221 61
    0x80110781807a00744400482c000600f203040442210b00300594890856094190105040c1c0c4100002c0c0c0b050180d54a8000420804007152985601c4503080c85c07440d410050700b080202c402c1c5c0c005084508203040030056001400d01c0360f007004c0c01d003441c500c0070441702c60242c6422a5000300340b400010090000020b2001d003030320083d20850b01010201080f08509002c1074415503004007044c0302140b8440d01a0680300102100e528000c99901590b803184468240300c0c900d50302070150300040c01c0d035100c0040d008680d031041d25001441881d05042d0b942403c022001c00001c1c09080d6125800802c034141802103681901008040720344509803a03804001951040c0d015811a12030740c0c640c000c19040944000b103170b0b814160082c0c64101c90b95120300c02512080ba100301d9205445000807200283c4692454090500403000080c540030010005400c50702c01c2224a4441e034450842a80011600c17801031380854040907d000d10305240c100c023640340070036000d8045880288140001c1481030000040e21180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 953336160 1250 953334910 953334947
    0x30105060d1b0329030a021e0603071205010f0e0f04030311070605090d090e0a0507090302120c040c11030901210501030b15010c110d03020c0411040315062d080a03 72
    0x204061310b1035112650001e0a0300b6055088005030f64054a00019005a40e0742140030301120400240001940c50b402212034501003885015810408115849002e000d04500f00c0c1c0f04a4040c284902c100710700348002c1003185e0301c0d044c0c1c0b030025042600c02d410242c05603403401682501c910b100d00d04203001d451308032201d078107500c03482100d20082071160301c20004480c244500342c445031b12a0a00c007009003400070039080512075000030000040e2561100e030ba2040410303901400d40350410101304015504c0c0030041f04204440d518440c08920000b1048030b40c5043c003401c2500070461010580840302c201c480125015502c2d0400010601a15100c007510410041c0182c900800c480c1c40152988800c500c0068000c1c100381d158450941010300c88456a41e001e401103542c5580c040c1e002406454244035964400721011804100b0094912800604030032100e10a01a540c205500c0455904130701c40c3c110f214510070307003002c41520200102c24000c0d094078010b8600b8680d403400c000d800d009100c03c510812 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 953337410 1250 953336160 953336201
    0x3010914090a0b06011818090605070305070f1b06060306061a0a0507171605031801030603110f0a03060501060201092d030f031e060312080408030105060d1b03 70
    0xc400c070105201000c50750203014500b0580342d1600454103212100c0004c01020411000400c60050389407001001e10020000410000254680030f4107444018010380240360908050084894000b0340e0480d0f81c08261500c070f03070f26203002c1a0302c42682d0069900500450b01c0e0200100c1400f040742c11050554202455910244018007401c0143c0e11901c0d02c40300001c2d0050100d0703000260b00420740742c40d08903843c00d8079003040b08031102094002c110b4181162164800201132859540190600100a101742800c1195514644072012400504801c40f88170700f0b030000001e80c8907035801450402540d01b1450030030866860b400040e0007014040e409403885400b00507080c0c054814000f0800da000a20042c01070380300e907269403e9544080a00621092545840c1061802c02c2800c6030044c1d403028040c8081141d40c99400d00c00c0e00c01100e4030501e810040d08078204408034800d00c0403030781150010740d511542e03103c221100320014104542c01c0070a24429410b01445182d054000e49031400740c00350000074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 953338660 1250 953337410 953337421
    0x2032214060708031914270c06040b0901111209090a0527010e250504090812040c030c1e0b0a0c0f0c050409080a02070b12150111010203010914 63
    0x8075401035490080c03000780100001a402c0b1a40e1040f1040c60404c00c0c00400c04280c800c4049400880c112801101d40c103145d82c0090020290420030412481c00324040c080c9418840f0104010f03200b24040d4600b0389070300081c0340d20164070a0309482c0d0301c0c002e45000e03228131b0b400d002c5410036142c0c0480c03d82072080f1103030000728100121600c0703079034080c4000440b034816a41100c1140c100030000c001c1c4940d519581d41c011586c0c860418042d031030444100407145650b034044161540480b90343c07500060300032403400c0317000c0002a01c8241150316032107141508410550300d40c40c160b000039441da00002d06440c0401400100091060160072200c41902407051030b075030312864030044a004140c0b1050010ba40640b40c0000310700310303864003035009005007100350b122a00c0b403010a080d00d00c01c0c2411074076658005a8a0256035042c4031050280088003106807400b4007402248912481c040c10f200c044809102980c0c16903802a90241c0300b20038010f000b503483e9a524450300c00101070303184c60315a890180030000345 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 953339910 1250 953338660 953338669
    0xb0d050303091b1012200c030a08130f0f050c03070e2205100b06070204090308061801030b060909010e0607090f060806030a060e07030804031101270b0a02032214 71
    0x104c00d2102603481000034070140100700d0107003203110102a4841c640e02c01d01d6001d200352030020a80412a10001d540d0380040402c01403999400070a42d0360008042006e0000289164900d001030380d80004010a0035502400c0040c102200e50800f1030b4148901c90f4000364000841399918824603e41c030700500f5080d01c03500f000910300010302c40200280c008074150402541160b000c0302032000c01805050812000d98042400c0344d0b841001540411138030b03c00c000452400d04421855070400f108102d00551440d59101211000948414440e1401c0d44c00240b00c2c0310f09601207030403102c0f02c2040340c10070304124001800000e818001c00c0401d800366800843d03403c2c062a002c500844018004107416101501e5940090580707030761810150186900c0080401d154034060006507000714589020102000d001505800503100e1510060444d050b00308050110748003140102e607034030118a5510722401000b28110b02c201c410340341040c070801c600c0d107481c02030303503098081594005e0441224944480c810030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 953341160 1250 953339910 953339929
    0x901080a020d17130b03010f0b041d150616050609120d0504020f0d030f0e0a0b07030305060f04090f15020f0d0f0912031505040c020a060b0d050303091b 67
    0x79402c500140b00700d000041040b9000c0741d078058040302180c14950015034041c8414219070204450450100040c000d0b1040780541030024440d000703905103094036282d14010050b5a0203616250000240000f450314402030145041541000700381d00d5407015644c014a0010200d07100c141e03482d2140d04001506aa0001a00c3c000003070480b45643c14001c40c1036401024100051080f41c0061100100e111603880780d03c103655103148079841e8510b2480400e43e0050444c03c950108901c102c1740c400d020040c07400144101d0310025058900030070582d07516408100c1089800003015002441d190100c000c1c002190441000940308103144d6807007261840d1550140d02030440140d900c154108120301c1d0000c09584004840b030304000300441c0410441e01d581c4144500700d402038000c29110790800a0842807981070030040e200840341004880c0c491003000f940d41d64201e4000740041d5a40c0b4040007280e4592845282c01039010007140d55a10300202e0498544405002d401d01040100708007120131300e80340c18034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 953342410 1250 953341160 953341163
    0x51606020c010e040b0f1f140708070308060d080a020f0111040e130c0312050a030e060f0a022113021305040213020f0c0a03032003010f0302191806050901080a 70
    0x10620180f4041007004014041100e0595100d00d41000c110140e40301c0021402180c1170507120981d0320007100b840942001340c9074030550b01d090390800080000401c181c040d0b880300c03601403415203040d0b554000802c2c003040b2203060192450001085800000f5030004200144840440007442008a04e25025402d4011405980c2042054900150400703600030038801c503450041d82e04190391075403034440b0b03040b84654030f501d01300081c00040c1003100a509402a1303440440c01c14010003903468110302646100201074400319000c0e03000506c0001e0180200112031980000d01c94034480340c1071400011100302c1c1c26850880c0110005800108442018420948280d801621030000300025041c07042c029404007003d0b00b20030b0f0302400405064041001103c1c00d15100f84c600203130344101c003240c41380561594102c5001c4280100010b001c02c002c03890809045035419039850f020749180030400c90290031581c01041001e507000102d030b03181c123040d50030000851701d003075410140590721503068585407152034a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 953343660 1250 953342410 953342417
    0x80103050705010503040318060201091e03021b04061a030106030e070e04030804060603060c080f011424071b0306110a210b0a1d09030a0c0f050a0f051606020c01 71
    0x7030070000355001c0d40c011a1311501c6860441405c0d1a405004207420400360031102c0183c0d0b490302c04008120554404003095405003c400401d00e04e00e603002565031000e161049501d174082032072441c4c2601c4076080500031700b84440030710300703002d61244610045070401d2280c1c400090404818140d1403078040b4403081a100601018035040d81d40e51400e4460300d5014208a503060358911002010880074442d480308a2041e80c0c40784e0303541c200b039501c4116084040c0c01540c1d180328020030400c1540d0366055034546868032440702280d40410075610f24014028080043d10380021b984041d0080c015141c04402920701c00c8a04200c0c0c1d0822851940880c02142514000b04001c82880c810507070360403419464106c0201c40101d802e00400c8080391407280280d005103d0010a200c0158500c00c03140765651384041604020760504048800042003082ca03010041c001c044005201007d110042c4030103150ba6030403016000b440101c03890030316514a41080c9920a2210071000800c040c0e20101c0e0507240c00c10141d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 953344910 1250 953343660 953343673
    0xc0c10090c0e04051b0f3607080a0e060709031103070f080a0302060f0c07021e0a12050c0103090c090f0209130204061416121803060e0d08010305 64
    0x5110003840d20550544440e141e07844000354407a07148500a12071803190002e4900c0300c1420075503501c580790a50000b44180c80e00040036800f6101e0841480d0084825550a1242e6060040000010510400c4003500064240801c00b030039801100c254007603501120100055007442001584600c0282d03031150005a0001c0208041030f40942242c82481000302134804942d0b44482c4030903c44502c0d485100150003038940780c404c0c55012f0003010b600070f14030840c040d02490f09280007003240c130504800030320940780044403612030f0b0401400e00035018006040e004c0540d4407003210040c14881d44404888601c5100c0c0303003099a5110340500612540c1c482d06421142c1e090105070b001030f01c5e40700103c2004660030b004d2615682e50b9070520400c91000d19030010f980324100b4074021701c0801603000c4c2c6c0f100c00b441000019a00c410003110700090980103501d002185040003030440356a8001c4108449451400c4008801c4c00290351107241e1141e011422149540400c0348290340408091001a08540114 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 953346160 1250 953344910 953344933
    0x804150606140304031232010503030706090f060e0717010e210c03120402090906010e040308041a07090608010801060b18010513090e06010603020708070201320d050c0c 74
    0x1c05036801510034209901114845490801145c5158100e000d2007036200074011f001417884807600c1a140a0800c01102d1507050001182d503070320980c100100ba030342e40ca60f29041844455400d581185a000a06008070308404100c3c0303035501114000c2e00140c50301c400c1040942901441111040540b48010781150b00e00b4180c11505a41d24004a15416000300020380020b0001e0006200c2641103190300f000c40c0c00c19006200c00150024511259584401d0041c8440080354510700c2e0300961525004440d5130782c0d4905506d10485540c44221134444d400c00f03000301da541080b42030080d94016a21506603a030f039501140c0c00d903410751142c41848242000000c4034881e01d6200705050001c10b04280b450072024000e00b03e0008529400900360b50742c0d0b010155801c50f000d014003070062a5a15007035007440a40d4898004c14401c20b50001c0c1802581104407281100780c0440d1140e04e80304488481142e40950120b0716641d05c8011001d14040c40e040001d5190705803802650840c460074001444225481b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 953347410 1250 953346160 953346197
    0x15031b0e0102030d060807030c09060b04170304050907170709060e010311040510022a090c0903120a03090302010608070e0c1605010204060e044a0303070804150606 72
    0x104060340e0441c0010404960841a180030ba50000c0c15444000d050451450411000f883c1494200310140f070f0401400b08806c070205001d41d1b0544081c200005581103510100c80d266104a500a540201d424801c001038039800c000048000b0906e0200404a686e425600715041052401104081510401027884551203948034907862080c0400e49860291254009171822020f403103d00d0061380442d81408034520031800242c032030800500404640c4031040700240780a8002170820656010101d803e10284da01044500c7c890000000416680d41c11606e004015001d110825800341d0300300030340012481c0000036180219144004140300984039503c0307000c0203501980d100005c01314480c0910001c40c10038802071004103100c0c0c41e010041c0d00c0210a00c07055815000843c64141560034040c12194a504000f50b821031000150840c694200f40005841c00202014001c251002200b0002060303002070016008500413070700b01c2c170884040b40e04402610321901801c1d000aa0340003208001812 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 953348660 1250 953347410 953347427
    0x8060f0307090b060d090f0302100606050a0509130c030203090f0a0f0b1b0409021201090510090b210c010305061e010305040f020909010f23010308090d0209090715031b 74
    0x20300404092070038405401c4001590121b0a0036115a10031204500415404006109807a0a00581401418608807014046d0701070802000144480005c01f071006e0780d038001d0441c04401c130b40f4404000842e0404030040c02074104640b000300710b21480f000e140c1007800010350400b14a81c0018158030142003640c07111101c1402900200000c00b0140303812640c01c920401500203002d004000580790310060340c0030b550307410741030f44586215440c2c5014420f40a007a80511020345040c00340200e0070240580100d100400700c428400c0c1000701181d040c042d413071000300711645140000d0b0303024000d079110701c41008802031049404a119849210742c81140794000e420a81e1301602480300321865003d2900420302440007103e400003240d54440100300b142c0442e20546191907102070700d502c00b07080d41603014007403002c042c00f000c1d21800c8040740c82070f8030ba0344601103120311507406400f00280341030000030329940346254000d603a4084d0310f03562404415407103445543c03c0c1e100c408030b00310300701e14105030306950406 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 953349910 1250 953348660 953348681
    0xc0e122113030f140105010905010305150c160f0b1f23040e060703050f271c0203070501200403020d170307180911041703040302031c08060f030709 65
    0x107281c034002000c90315844604a1582c00b07006040a4040300008003421150140c000c0c0c1200b07441d000c014801700b180020b0408890000403850b624a4031401552007103405080420318030807502c2030103001003026445d21822103501c240c0d07461a590312005900c2d500c1070030081c0150f521400c07810040154103490b61000d82c021030b04440b514000305000c0007040c141d40540c1700f801e41961208040c0048a6410320841d41c2c0300c1141d111881e154200144401c0f01b0346199400b5400c02c46000e02d04028881c0280f11000305200103c0d8140c468070441140039403603401003001640d0b0b0354600100c41443c048410180f00688200d00c103541d03e002d0840c2d00b00b003a80450000180c6680e44050880702200000f0300045014044603180c22440303141c0501201a0555035402600c520342c1064102c920b43c451820640307082d91703105a14102e01c0071a07059210715502540e030000c1c1d03261054441005820b003071151900000c2c4a6039817178038044d51341d920a025854000d609026019400b4400420225541d644000c1070f11 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 953351160 1250 953349910 953349937
    0x10e0c0d080f070605061002071a300106080a0515100201150e0a060b07020604050114070501020712140c060c03060a030f060b010806010c0506280c0e1221 68
    0x1c61078400745042c94000300300850b5180e0703039003045c8580b62404840c1244a40c029100512107d818841c9940c1c0000042c46004011000418920351000c5500c0003490405461100840c000b06580b41801c44a030080c40303142d0103c0c24420205e000c012030f501034580319507856400440c0781c0d2024010711070150b10541182d02107541c1c600c0c1e9928240d8003650188000c108124101802d414401d2503030045a0142c1d020303c400c1c0c0707010400040161559419602240e009091240c006203070b03510403008074880c1d080000d049510010f4960104040cdc41d40a100200582e541c1203005020420420106e118080460415602520000d03040740700300ea000b182c0c040300180c1660480c0741d9981ea0032030603403025001103c0e030584540c6c1801d0b0342c0d40e0102441d45d0114091074980400041b81e11803c0e241c150282000340000a0360f4603555402d0b464942419007005a12000c00c40c0c41c05650b40200f18021a420b1148121402ca01171507500d8000074845641441500c0014060030503010352101c5d5070b002c0300c07072640311 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 953352410 1250 953351160 953351167
    0x2407050c0a110f0121090203030723150942060f0d020a06081510030914060c1215030106080304031b060509040b0a0905070509040e010e0c0d08 63
    0x180e401841042500d034800d00540b01e0900945003000a01042400f246042000c010042480e6000321249003100003031942000074100070600101e8110300c03911102034a200741400301203c2082d02450b8006003490340e88283c4040b120000b034007040214041e1070360a02a4030911401600c001140c11300c42d4030b00c100b580085084911000a041c510000024843d40540e519042010314142000e00715400e00301100c012035400c8150b40040d1401840740a0101080111b8001071000c2100100403c1d51000c002c0200102d0390350701c04018040d000c10702c5c04503030102c0d0145440782c51800000c0c405014001e4400d8141c10070740000d10040c00728100400106486044ca92401441c0c1c4003031044002425003480610750301d5040d810807503d2000c11903806901244510801c114403540301054500150045038040342e11540140040c0c004000750300403405203440c041c20301c01003c0c0c0100003002009000da90511201312401a4942295120152441903030006100050030740707040201c4160580c8511106402c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 953353660 1250 953352410 953352427
    0x9090a02160b010609080f0606060415020c190302041d03090d08090d121b0f02013005180102040510110307060f062d09022d1803240705 60
    0xe079400ba4040c5010170115541440100014408200c2c101c0707004005121034104031010407031902c1984501d0b01854803e9a1424041d4420f0180520010006100c20072001c8000d800c501c034000e0511049100307514104640c4c114498000f443c420503c0442e002c0d42c18000c60324240208241819400c4074591030803c0401500da55187d01d0a91a03130140201e4001e035030140c240134140030b2018030300c0340c001c40da43c20403580002e41d40100414015820f00c0c103003e00303060000280f10640b0030901200050702048600150415041d130203130b40714044c0916203644508070100c0c070600f00e218034084c590308412100d001c080c0340b0340110024811000752604407454070040d0303120003080710585d23181100031070f840e03020800a1214100904001801c0a8011000d0a0015002c1a0100c42500c50880455004105d405000320b451080380c00d441e0b10310360a00c800c203014440808607a03000400040c170101c10191101c901d4100042c04000200c40c10080c010000d090641e010910071009000c401040000c000204 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 953354910 1250 953353660 953353673
    0xe0c070506090706080f0c0a030f1e0f0b0d02090f0606130305060106092c070908100915020f040902090321120f0c04120f170315030309090a0216 64
    0x602c5048000042e00c01907040c40383c011310503903029002c02c05c0f600356a0144854030041a08541d02c80780340b0b050002e490303c0e08008900107002c06142162420103029010440054240c00c004040071500400f0000e440c109001c102041010308800780d0040518400501d50060321290b841d000000100100e090842950000c010a621600210342c030b500400010002d468014400c0d0020704044596146112100c0c0d4401520074850b00300c19103000311400200d208107005018101c0a440c0640c01d03600c0b041e12005806c40680011038040b0341440803c4141c00c80603185200341c41a4048601e040b918140c54088584003039000f006000d60b16008410300001c1e600030403600100100e437200c0c000b540351030245103005c0d000c0d0001805550380c0819042003007104070300241160140c40001c5110070400d031a0303003040a02c50101c40c50040c00114280044801d44099030041c0d44035000701000d500e001607240c0706068032409484c1b40366401c000e0050114205481c950082c2081d9411102c0510211100d41c60f4107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 953356160 1250 953354910 953354923
    0x10f06080f060604110d09021206150108160c0305030a11120403020d030e0c062209051f050904020904050a2117040b040201140d0e011b0f090e0c0705 66
    0x31055001c0009000d10a0781400307090f80c40103040300c041006005400741c44800e0303ca4921040d0010340d41d031540780115a42d07030800c000e500d00310b0800c440040c50072051344038022046d02c150741e010400100014250204040e1000341404040e6a19080f001050b582a6155000600b841c02c4141e2141d440400301d42002d0042c1803101200502d400a6080c0390902905290764800000704150500d41c40100c440c900003a484020b040a075a100e075560b181120880300015400c15200324448404000900d4001c0d03900818080e40500781c0c1400514206000000100e6840c422950400a5003000802601e0a4080740b680140aa4103648840556030746e0014400045001491b04c003a11841c0107007040e81c070201c00c0302031020786900888641041e4331104000200200000e0410070f00e005000b50044841e41610107404903840140001c488244165001c0d201059000b072100710303000502e4601500c52081c000048112b41c881c90782660614803503404003000149840d4002c2c108002c6c02c4000744003041034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 953357410 1250 953356160 953356169
    0x2e290c030a0801091404151401030605060a0501020f06070c0f02040509160b120c0c070503060405031903060e2e060c0506010603050105091501090302060a02030307120203010810090203010f06 84
    0x15554aa4402070054080041030300054022480c200190641d580584100e0350072a4000003856602c202400040000e02a03442203541030881900002082011513000140582001c86001482c1034460004a0b90b03000c01c200030703000f5070380450085550117005040201040e4080c1a00f00f42e00600e80d00400c007621001d94090009034130228940d200740410254100c080c0200c0401c551a0190006410303140c0700c00900139803004503000030b003440100810000d2200904010307055684d07615090421f107031286c114149141e070307071482d050390003141d54400d00c119002c2d1002007018081548400880d00c0580c58a6070030383c050314082071401184a003844000000500d065581c10a10940ca4a03002d030501c0010782c011400c0c1410140148000d42d50896103990001141404103031079440c0c0c1004071000c0c0c1d455400a500a580006d108000344c1d0b01000841c460800c40d202c10b815201c00040903c124803003407050204035040441400d100f0401c40d0803058007103000800101d070b007100e0f074500103040b07680c81c2e0700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 953358660 1250 953357410 953357413
    0x13050a020d14010501050a06051e070f030203071119030b0a110c0304030213061203051c021602030d020706120e010605130209091608060f180703052e290c 68
    0x307642c200c0a07013401032901400040d42c00d040e449141030340181403400341c0c0c200c03201483e007841c1062440303e5006003581c81c020703040360103154001410f05011352a544201d40944256842420140d03c1e8109a0300ca2f200c034102140011203171364a15182d10000c00d0b8007070140c80f42503845822089444c04400040c01c8502d01003005103a45601c2c6104004c41c01d04048140f8003120305064081001e032031509003900490703815040841e034a8289030304580c00c0182d00311000000170300c04100200c0b81c03144c82001d4460740d48242c2c1260400000344d04140d07503842031b81c03040b200050401000c03107c03c0605a041710511440740c01c00411015105c1000903c0d445007209500d080640c0451383c580c092420040598115800b0452880c561203a110000e154410082042e400744980d0040074a0540310788001e1102a202509032803810b0500c1c88005015020a0300c2c00d01106401c491944050300c494001001884c0e08030350070b032030324038681038520b00030075610381000c0204a5013140c0a40088810402070111f090000c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 953359910 1250 953358660 953358683
    0x706050c100b030c120c0f01080f0f040302070305100b01030b191a04270c170a1a22050106030c05180f060c01020d1a1e030111040306050103060f02070b13050a020d 72
    0x1c00d000200b0240404c0c28100080389e0248000000c05455064000d03100c09807240340350340c5608007a4941081980300802c54483c408140041b8440c542c051130441c002641c003400a191a00204020501c440d602005401c280f00300c104282010441e0314442049000412410140d0794499008140c00020080380780762004441160310016a100352402805c090134814480d008603003501c1030b000e500400e00310049a80f0b0207000070703100040642e181284801032251003001d900312821024201440250300d10b4a061400105000303000740a42405840507546040c201030484c42c418141480120314180c000340c0c0c20340c1488043d00c2c0c1038010415150b00100143e80c40081c1c4c001071084a60140390400d03069101c04e014106c40c1d5510070b007400c071404003101811402c00004006030041415603052409084001000002c000581d04607134100e074010b860822001d241100b00b40e080c0e10440f1801018109840005040356042c0440ca003001e40c010403c542d11150b060340070030070707803000000c096840c06240b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 953361160 1250 953359910 953359933
    0x40e06010503010c110d0507170c0a0c08071d04020d02062b09021f0905090106110f0a1e0303022203140718020f0910030204080706050c100b030c12 65
    0x24010300d034134020300d80341090858142002c2d030758a0315104505070040090008010041c40740241d02074149580100c14aa662000081c0003a62448254011540120305a2000801c00030204004040341c440704c124601110075000007800c800b50052040b40e102d40280340450140e105c0c40041c024074464280d4800b000042c01c580c101c402034400305200c0440f404c00c840000140c035065100400d8054070001c1581c5182c06000551788215643c002507009007140c000000c480381e00c1a54550412408000c0d111007130520700201da29400da036032014041c01003441c0140204980a1b01000503603020b8900103050820401e0f4010070100c088001c0703600203044035814800c0c0440c0149000224003040000e140309445c01400c60b44ea851074040009480740c3c00324240c551640030300205e4010312070007030009990100302d0201030002c0d041401240b10b01d03c11442d01103182c41c002c0045600c0d04030868010070946441c011200040c00c85240300d903400d0302400032a0320300c54564803684c0c4403141040b0054007401600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 953362410 1250 953361160 953361163
    0x10e0703031812020906030f1213060302161b0e04150507020a030e121204031a010501020a0507030204110d09301b030207080706090801050c09031c0e040e06010503 72
    0x55404000b01500b10800000180590110300640d0641c0c031206141d5404c80040e003055002008086d407406540364501000f021007000700b52000d40007040c05241c0f9200c00d0100c0490140e005002201900d0400d1200400d40f004660184080345000380f1501503111030b0851711004080c1c500b2240307440644002ca40e04540f900400b44e100d001c2c0c2c0700900c01c4141c1510300a121016a00005d80200302540c2c42c40c2c0c0801040c0988100f100c0380c442c0240d52180d9a1074001c50400c90101c0701040e1416280012a40d5880440c41d114a0b0b82c00c076005000c51801c640800c0014030017005140c2d12800d007004a01d03101b40a03130040729006070151070072540c0e407440c0400c10407003c007d24940c10300240c00b4241600c141a0021304000141d240625400c0340d5000c00e140584c50000e03d50050600752049131000a0720503441041c2c0001c1e180c9981c0240700c1c58030b90b12042c1e01c0500908820683c5074120f80f103c54030510341540001c601180c41e1070504d400041c8080400c080780c03080d42c98907a041e04140014005400d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 953363660 1250 953362410 953362427
    0x8130f05010827010609020a1808010b0d1202010b0d0503090102010c020d0c0b0a14101a03070507030522060c050115082d061e0f091b0d05010e070303 66
    0x80c02d02d41403629000007440e0076208403140c0001c4002c024441c01220880942c0030740c000d09102c03007007150381c1c070202100a000c82c202c00385078021961070307010045589203060040b800314020103010301966554550701c08070300b40442c520000456507078250b2900700d40d8822218622484c001c0020716516110a0002400c0d151045140d030103640c08075005c0da804035480648251681d401c030000d80195240c03188003001034040e0b4107141d07030306280d000148282d010288a04004031484501000008240a40c094140e40021594000070a1040c01140c0c08203008800038002c46601c1810500d80224a00844440822a07080540007500140c0c1070b10800909104100080501880c0d0240b010301e003150340c6071b45103400c00004044205101d65503031002509407035201804560820b580c40d501d80018900b103507809075515000e081e0549404945214401c02106009100e9070002d05000325114403d610080d01049165030004500c440305400f240e404c2c4034940004171000d010741b4104e0f00e142401030070000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 953364910 1250 953363660 953363669
    0xc080d021c030b03071226031602030913151406030c0306031f0e0f031305100c0f0b0402010f05030601020c0909030d050c0a0816050d052805040213090c0b0705030708130f 75
    0x300d015645140394400787e0969038005140224400c2080007010124190b0044141c42d40d00710351000c460b40c00c05c115541000180c0b25440f44003c208079554203421700c035082072601490304620100040380213910803c0c001c640c80340014003280c082c10400844126004940503212111558032903515001c00c0b410300c450081d000050000b07506001501000d03415100f11482850701c10007542002060342401742c10f03140c096a4100017022007100050602c43d0345800c08440481c001040380141846060055060f607014501c10b13401000e41040900500c201c03144064075802440c03006000d1003440c8800c0b4001c0d0b40c803a80e809804072351501c9007500098071408014119980c680c02d48109208000c0c3d2010585e9031076682510302044a80700c546c96032407203102c030701d1084032000803034101140350072800e03001940a02d02c02d6030182c440d0a600d614030000c0744e0000000030210380c2d0a11081060300340030006800d013a40910160303850a046665081d445a1050b01c1800f000e003c07080c420030101ca0030303008210090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 953366160 1250 953364910 953364953
    0x3060403032c07050909010e031305011403010b07060902120a0c0510050a0f1404150c05060721020304050c060301030c06120908030a02280c0c080d021c030b030712 72
    0x10750100803143d100d15484c02918010a079560008030400800d41003030030120015401d50742c0e1180d42d0b07144a2245940c501580d4045403641d6981ea42541202c02242d0488981681083c10510f10b991040b001e00051301d410ba9101c040852002c840749418052000903e1107000c100300914030344001d00c800303050f00501d6101030200078815030040c0364001c0c012108c0c0d55143c1c41c180008940e801c601d4903076805946c0040f20211114541a00f1050304103640142079030241d000c0b100b483c0c0d50b00504172000d441c06100060020056000318030b9410154000d5070700b051007034003641e0340c2c80701080201d07005070000d03841680e0540c0d40c1d00b4204085a002210300c140801000c2d014000421142c0740c2010314840940000105039001a0807500a40e1103c40000c2c0a1316414540b00c01c0300c02200010304150015000340e88841d0b00b9200018012070000301c16852815607000b905940b2000300e44000b0341100c04200105240e20f80402c10b03500e907424480c1d10003526189624000ca000700e81003007541000b0816072040039 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 953367410 1250 953366160 953366231
    0xe090c0909010815061903080d0603060513050c010c061103100e0c09031b0102030c0a05070603110421020a0f1508060906091501030e1c180f230306040303 68
    0x96110500e0b1394881c1040e911b21103c0706c941c07441001d81c5400c45c0e00c09050030501061100c0c0c0000b03d50001411240918000d0129403244050000700500d0000002c1c50b81e4007100700303080b81d07502414a0b49541400303400001140a040d0380f1219042d442100d940b42c5950121600f4880e40c01e0601040e504461080682e90030803030070002199562105c0c00c00100583c03000101c60500380c0c4204100d40c80c10300e40c042641e08900c00751414980e520182c5c0112804641400840c0c130101da0124259001c81e0005030241054440941d030800d542040712109a8208807050008241e21840c00708200041031071f00c0e03203a80810080c0d08002d1079101c0140015100350f1420b0203200f40b5595040e84941c000032126240f003001600c54005a0040580d0703942512540210200394254084a04400040500d940c2381c50041006861407008000868010b05410420903682880f0b403081d400d4410800b1109100c0c50445c0c0032071240080d01d0400100c0d011000651a4a4140090362810031038482c2e4125440d0403041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 953368660 1250 953367410 953367433
    0x80405030d09060e04110403060c02010f051302130c09030218010e0f04020609120f01091112010e0304150e0d11010e06040b090d060207020d05150114100e010e090c09090108 76
    0x1013110700c150b02c621454454022007100745001c812180196400036040001d161140400b0340a0010400b031111028680000124002001040c4029013030380200b44901200030103078040018900341c100e1030100100c0d68400300050325a0100c4561070a080989407495614101c1d006002d0300b4020500442954188140710058492200782c400c41e400031103150700c03c455030045052410913500801c040c40d41c01c09003801c040c0b10028113000c400b00c9064841a288000c0310b40d8003800c1c0e498a0f4401d00441d44108810048180c002940f01d4459190307140000c000b154100005561200c1c2c44030940c0c21440b000721903500740d130300711030354000c41c200035a0f15900381841d2031700c82c407600e0040000e01f90180580b00c4024081210640c111000c1c40d9000b1310f55920740c585420b00d15529107200340e01c1c040b400340c003100100d189100e0481880d4107000c01004103240c021102d0b4102c59030400f0110781414050304409204041c2d841c9ea5003984030300103146180e03403509840001c101041c141a4480715064001c4040340a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 953369910 1250 953368660 953368667
    0x50303070f0602071506090f11090f010f05070c0e150301150902090a03080a0806090a0501030b01141207060503090c0405090714060d020c03070b15030a1b080703080405030d0906 78
    0x1c0d88582c01000040c0c94502d0b078103060445c0c0c03107200c03032418141d0b04d01071001c0350440d61503008210110051500300000c040c611a80c0c0b04500c02c44a02a510004911001d01c041d8801c00000355124071924101e410708070f00d650b800604404a4008503050a05102040070003464103034001c1643c0b8040f0300a001141010320b140e260781e2500e00601003140c0d0001002c4000340c441d818403100440d0b1000c0320755910303007105400800307410081e43c1251203100d80e0008928402c01c00d01420707060303d820100000482c0d1810029081900107640155048010030a1144000205011140052400f81c0350541c1d0b0b0f191010701d40341040403524600b071195140c002800000d4a0010b1784205a0721400403541420051800003032007402012020501b050000850f64903070540840038104480c4030350010b032916118400c40c002901d5007408500c2e0942d12904071140404d007900d485030603085450416940c0c0946a050300ea0401c3c291360030a40300301400260030800350504000345110a0400c2c900200700a040c040000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 953371160 1250 953369910 953369933
    0x507020a2d03230f0310051e100c0501050a05150105040305031e0f0309030a140c031e040906080c100e100c1703071205060103050c0702121504031805030307 69
    0x1804101c1c0303100f2102043c1d4400c104070512841c03265071003500c81e400d003003004200d0740c003c480f040f40d2000302c0c0341c0008980c00c00c0003450701030740c1e08040904031554001081c822043c4017503007800f003003003603011001002c2402881914080d055101010641c0d1405840000514099008160403c2800c1008001080c2c001c41610001912146240c482c02580f0024212501032041c0d00c001e009000014001d070508008000c02c8100d4180d1614480000c1014000d85140540e12943c42250002c100250106007102145501c1c01880c1c0e000506164803040800c0803241e20390023600c00e60303008140d403111034a08100c01d80900d8040303107040c43c0031a4800c40402c0303070301c0d00400c5007401348940080142d08000c00521060710411012610641324608140c0c010301e0b0346981d509802050f8a02808905194480c3c01130303500ca8004911041d2515000b6424440404801120781066002d4180c02c481500d061418441c080c0e4000d0307a980a0342d40f851004000540368035440144242c0c030400484000844501d0300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 953372410 1250 953371160 953371163
    0x305150117060a08060f070f0201060518130506070c020f040b0f010f140d06170a03050930010902120f06010b030a1b030f060f030b0f190507020a2d 65
    0x110215100c00b8003180110000e80c000704018000d1600704611180a09000d501c00e0350700366100c4190740c039180700607422107059008071034104040d84c41007541c16018800d9190040710501c54501d0111440c1c03035a50508030192001d600052501c5080400d502d800303c0d03201d0400307404840803c0249201800154054640c9042505201c004040040c0715405521a903454444240d4440d50b640b60381032900c0020000e03401010062402803c10010b4000001030455072944e140d15030900c1d0001c06000c12100321407840410481c06094144452519020b0400c15802e010000022840c4001481002100c03242d090120045600c40ca030020300101000602c281101c403108003ca507240c89140011000d489410804400c0301082314034114000d60580c410000511500002c100c0d0075202c140b4580490b030240300240c080074011000c580000044048a50404503400310041c219280c9840d1900796041103542d4005038004404040034045c0360900701e82608108108201c041c940c0c0d0000c0361109a00b44030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 953373660 1250 953372410 953372447
    0x1206010c031101050f04020a060f120e0c03030f03010314030c0d05181c0201480f111503070f0c0302160305061501020705220902130203060103051501 66
    0xc89418103010b5541401c038481c4500092166107880c0c2c101c2c41000310162002c90203114843c4000030050300c03420035108045044d94554441c440e0014004000e403400c22140d5600d8040c042188009981c2000108041c0d8500003c0300e07101d40c5141400b141010010340000d8441e003080146489420002c1020780504502d03041031a10f032024050488240201d010411b82c0000d24a000103030340c03814140c000000e0038804d80c1c1d0304e00c1815503030b030301c0400d449940883c1e00c076500e07128000c0040304130041402c1c100380014208400c0a0708426152803101404848054440e0140542d0510071814071154021070442014651482e5090a000060150b00100c020f9401c00c58001072060802d442440600402602280110305440d10703820030940f154029907803940d882c48001007200031540003168000072102c000342450311000e96a440c1450b21400c00c1080f1404560b5800c078840107a80b010132000603078460140042c1c0b01c0c54200d001400700c46010700f1240b505601d50940c4000390303034000406a0802d00251 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 953374910 1250 953373660 953373677
    0xa08070504030c0608090f0d140913020f030103120503040b0a0e1c03021b0c0105032a0f0a020d03140604090804150507030f110604080f07140615010302120601 70
    0x8011a1903004a8100606042940b840041c035503511804150007030b0a03071000e8401801104680356660f00c404044803003c0707488009054070b004268005005201c6018142c0c51040400fa00c0c01c00c200e03801041a414000e1001c40140117001c28007904503403440007414072601e14101602c80c6807807100018030504100e03072103d1454246e82c0f010301007820406c0c040e0492104080c00c014003d00079401808641446440040303040d40c0c1260b00040c0b08041d01c1060315250300d10f454021070030b01c4001d44181110107603400c0f00007240c0c41c0740e03140005110080c05100380549070b20110400034103106030400c41d2800c05007012241101a400b40d06500c0d0002d40843c2c0c0043c443c00b1902c0c1c103414a005561240c032582480103a0320110310340060003400100d10135680c11184510049003a100000403021b0b1420940c01800002c0008540d10000c11f003003041d008009041008540e41c3d040b01c3c0c8540b0181c0c041a0f0800010300801d84018030200d44a85001d007015070074911500c82103203121000034040340c10464940d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 953376160 1250 953374910 953374921
    0xe030912390d11210703080304150b091f05090c040f0e04080703050901031103070926150a060b040314060703182012101a060a08 57
    0x2001032004500010240c0d03001003024078681903403909440c00c1445200701d014041c0c2060300c1d2040d1100d1000e5400308880d685651440305000350762500c038108580c809070400e82c0c080603100c100301c2c0318003c52061556035a60b241a280003410843ca51801c52689402c0422141e000d6031000002580b000c07103110901070701c4100010917440c44804c0d41c000354020382c2c614180144802c00500a1040e030781180c00a9010325a00d5010b00c01185d03003110f02400341c00c8103100d0b5070006480384000b80880c130703414076020805101d01d500190007640180c42e84008500740c4031041003412584500742603110456070011002000040c10192142003c800c1d00080e0b04403100041e4003002950310007000750018064540e140c989074a0090001e038920010450b052081000142103584640100d14802c40e001c400700c2004841551041c1c491558141060141e071810302c00002c150f100c0106881c0e00f1124100281165a143c102f50300c11508152106264a4a22100c0c1c42e103580350340080310900340c51890240040c1c4d565 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 953377410 1250 953376160 953376163
    0x40f0203061c0203240a110f07031101110f0901031b02151b1603091e120201030e030310030c0510090612020903070311100305040c141c030c05060a0e030912 69
    0x15103035040e40b045001950b08248581e043c4103902c604540d90007000f87c0100c103100e0001c5800381074034001c1e1a1804000ba840043d2081c0c40000c03540302490008500d4407800605e20700b00350017a0700643c4404d4804a6030781300c20769041c00341508020404602c1c51400600d540002e440745070b045038a0103c0060301c0c000c40c010040700404a65204000394151382c8610001d44895810390040906400148255801007004c12603940f9448150003e06030500030350f807500001c85403400f00841d09a042c540c1e0b40c1c005903440801400118400d03600402d03592034031415031511400902460308002c4c003078201e008120340050b070440441030581d9400d040000f0a003203110b40781b4020b480380000c10303505809013840c00002c11403980160a000d001c101d41444904000240480840304110380191024114442c104145e5160a104100f50100508941c400c0f0203c00601904000000340442c00516150140c0d02840818002c031501b01031080d10601042c50583c0c642c981d01d00402030b41c544225200c0d5001f00882c1e60 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 953378660 1250 953377410 953377423
    0x180a180506100e06090f0306010806041406010503060a0c02100504030e03010c091214071706010f090e0a11060d0501260604200a0521070b0909011e1211040f0203061c0203 75
    0x46c028105d500541c1c4415281d0389a00e070950f001c484c40c0869008004075a480800c0380c906a58000d8010407666a8a45140c03010f001ca00c58008254082c0c10391582c080c48160180390310a0b8040d480d5140081061400d040c00c449032480c0c490b0401030f09107410f11916422642828032517821510302d4004141d40404030703062a00907401b40c1400c1054400701c5000c42c0c00840e50380c5c126985c624240040755511503506040d0341c20110b03640180e401040a00c03000401188c1c040050b4040131301f800f410000d040c47c0c210120751081c0c11442d104c0c0184c1410b8130075011341544800701c07110b12601a1505041641d2041907410700800b00e0340006841c01d5039521662105200400180b034010b081c02401d400120445592031540028032022b4000e6600125091864000310340301c3d00e1010300349092581c43c001c03140c8800d5001101c0000240b031802000101d08102407100e00c9001c3c081c03800110b40c203c040c1b08000850742100d250a55850040c010005643c1d51a000d110100c01d000c2041441d000340c510010f41000f2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 953379910 1250 953378660 953378689
    0x50717031b01091a060d03121512110a03020603010b16060f05060a0e010b07080c010f0c0206100e010e01030b070c0b0a0b090a021e180a180506100e0609 67
    0x1010290a1071a100054214604040c00307241111400e186041c505084030304205c0b40305411030701002811001074807a03020989a0500302c0c20006a00c1c56440c410f2158000e207502005480b00010f8881044c4140c940c0d000300307203203030403a4039150440c950f90104440740014031851541d041c02180c805c1964003188544c0303031150360000301001400700703401c1c0b5180140010f80e60700703014101021010a242032004841c81c140d444041c211410036100d6510849141c1c403110000340750f5500e4031485100d83c11107004070700100000b03401a0001d80307005000d40c0a0380440394040010400101d00401c2104010900a81503a4101c3c000607a82d6403444000da41c2504503050051900e02c41c0e10400c442140c0e0340d80300001420003200e880709281c03a82c11081081c1c0c040d4420b10400380129001d2079610102110041681c15031406000412451410009060ba80c055024606410301201031255a90301c07031088030341c0404100d49884c15620074560090000014501300c03806224000f03208070306507a03029151040b84 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 953381160 1250 953379910 953379937
    0x5011103090402070812180319110d080117060c1629070207170309010f20030a080c0a080105060a110f0a0201020f070303212c120705071703 62
    0x9010515004800c6d0784441c1e104243c101a10020460200c91520b1030342c24032001c00015414100802e84010050910881903010f101d104042244d1102080c8031100140300c058554103e250b1418400312845c12052840800642080782046803100200c42030320f00045030600681503025840c6044000d242c0f961340710b03106038580c103414024040c560040c2e0602c28000d070b23829210080d540e801030340c0c1d1940e500010503441b500244041413083d40b08450091100c451823074004000361000b050003200301d02c425803848154000146104107207420064140c3c104200c60340079441c1c1294150020030281042c0545c40c4110b00004ea524111480780e200b1003684460300d0155000700036003840c96991408602800c9003d8000c0e0903129007003400100700082242c1e0103407901c040000504180142000f1140900c2034000e03a2620710540c01c444a03c0000c1e017811240c000440103001d2102042d00c0d02076855550801c251080000d1000550041030600c02c07101c1300f00e14458401990074000b400d6004114412164 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 953382410 1250 953381160 953381167
    0x708070c05120a1203140a0506010e0904080307030c140a210c020709150320190306200a200c10050406090b0a0c0308270c011206080705011103090402 66
    0x2450104400f600305100710701c0c500303422102002c1501a24003a0720103440746580880001d0940c04503070465a41701c80145014802c2140322000641092001c0c2c400f5140c041020040108598245c480c020801d6014200070300c3ca195014580c004510401070300d002004962500c0522000020310150a04511081c0600411030303e80030081d40e50170f80784911003c0b03604121a550100d07034001e442100392600b00682d400c44d40e010708000e07201007460f184455000101c210040c04003040e003048400c05944500400701d0f4081b004031606019145000b19080c40440c200040203100743c002d4420f080701c5049003d0414662500141142458140e0740c0c100c0d0041070304c092411310940d001004000f5621a43c90780441c1640312003031101c0d54007804012001140c150000780002c40d025600040e40181c90b00007640703414040c0841c000c2000d8014403039040756400080c080c455503801a03c0422021114034081024500d4400c0e03c035503c000c14890581407001c1d0081802c00040b06100716801c08102030400c5d542c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 953383660 1250 953382410 953382439
    0x30309060f1b030d141f0e0c09090f0a0b0f01022e0501030305130f03030e060306060c0109030905030d080915070215010f14010e0a0b0c0a06330b0708070c05 69
    0x1030481d41d8a0004440c0c0c1c1d202c009807481816103d0780080e01d1b1581c01c14004241442076078844848007904c02c10030391b80c080c001c0c03100581e0b84100591007400b003158146074030700f0f0590512003a940948203a0741320b0b82001ea2060140c0e640083e2200c00307950b9000f140034440702100c5402d500d25200326840c0104500f014004030034036030403038020702640d0b19031850a01040c1d6600d100c0f2a282206010080004c2c0c031242a00d5403910b0300c50080d40c1c01c804000e000502d02000d07012501c0c2182c0b081c1c042103000c25609601080140b400344031003050070701c0c14104020140740c50314045454143c4440350341003120100c8045604140300300109500c89802041e51925540c4a10080c07203a002c007441612084a0b4003066069507501c02c0f120320300c04040c00342441056505055080400d5082220851014810398901340080360344c1d405169801e6880c0340382e200c2d01c480c00414903600c1400014031410500070440b0304101101c2c4000844400a41060645840b5440c62803e00e01d503120300d52202c6d41c0400c3c032030b20456 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 953384910 1250 953383660 953383687
    0x30b090a020109060816182103090b120a050705073c0b0a1a0414100e04020105070f020f09090d110c03070314030d150311030309060f1b03 61
    0x500c58000d80b1401c10341c650310001240d00c00c100f01d600714038164554074000902c0e0700502c01b119842ca003003001e680e0020380f80c618442942041d008001e00400b1414002014150044520b0740a410a000194038006140d8003405240401610001400341c1d51070004580c5440350003036440d807035840075110038510100221000750007441112a61030650240d2140225800440050140e640c810a11880390b80c98110540c01481140302c120001e0b804040c840c240f83e500d910a41e80100486484c92106081203544091140039a820032140c0c40a044107000150703030840107442d10250704c084801c1802d40c2c0c0c1d00c041002d40d1003110a868000c4210421310212034404070b0f030380e5440b0859980c1c80540c2e50b071000b5110b645503004e142094068000702014000b09405054002d0214044000c0b6490945409458130071558680e4114042c00b240c880e0030310800c081c451034045010800c800540c2450491800101d2a10800000b540920000200d401039200c10310078514580034108181c0c0d8a44550039440c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 953386160 1250 953384910 953384923
    0x41a0408040f1418040201020f010c022503050703080307030906020d020c010b03061005100309050706050301080f0604030813050a061e06080114010b0703050c0d02030a0f020a02010e1504030b09 85
    0xc2c40703a1110550081600c40400c003481c10b0301200200901424541921002c51100303002e0f20690460150074601d00c42d24000b40107000754180c00740c0c0240b00c408580c841c0c1030050448250360304074603045003004102003800010b030300381a02e8124203043c2c1d403074403004801d034000c19850030020070a0b400454002d10101c010381c094105001c07014001d100d0a0001c1d006c046d00d51800704c1d803401091406003001e110509101c0b203050034401480c1000509401c980d1030b11840d08484d64002400110004018081c0354170a100c0c1c09503458504000300420f0402c0e5a0103003a0200c005e1034030881c154044440c5041c402c041004e40e001c82d800502c10880d104000100c04211100f00c0ca03400c2d189400e01c1000145c2810501c1444060494601203d002c0d90814400341c1480d4410311301501041818000e00c4040c08040c000c9410544158008694840341c201001c6d00407a014a5000e0641d0044851080941d0b00060350b00c2c801c0c4000c0318144407d4102c1001c50308540101d40015001500100c20888003190004c3d04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 953387410 1250 953386160 953386169
    0x30b01120c090501032708030a1805010507090b04060905061809040302010605041a1e04060f080d021209010f12060b040308041e030314030405070b0705010207150203011409041a040804 81
    0x788103140501c018403541d150b0014000d1328000038600014003150901000d183c0149c500c0300042240c1e01260000d1a07aa080144c0a50b241c0e5076a070248038500c0d4114000350000d203041c010180c00c0900e40040900300341c4061080500030f0700700007024030380b01030345000020841400801c81c00342d0f401c160a000303009085500031180200e14001290303141c2600035241c40485880103086c5c484481c100382c25042d102040320009600700703485007404128144140000e00c06040c1a43c020096000ca90100a1030000985044502c0310340c2004029600e0364002452840710728503081c80c2a00c203150b04060002002c00d9803041c1030380000410040304000b000c1d40200f0440d0f02c04030b50407115030004142502c509a003440000e0100d9800c011206185003010059544980648283c03084c50b503461000740915809104219030301c0e540003031f241c0c0802c49040d104440e0161021811410366052512007101050040b8140744510742c000c0000b01001140328010a40d41c03240c04218203142020b00d406c66040d00310703029 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 953388660 1250 953387410 953387417
    0x52109010b120706212307090e04020f010c05030309070519050108041707122a052a040f0c1707050f280206150102030712030b01120c090501 62
    0x307405107074079101444a001d520b4080142c0001e6103044d0050350200034100e240c1c00c0c43c840c030701082d52100c0f13850312454900c510000410b180341e6020000007010300b400108100b0a00004403001c1c8900242a034915034856030580d4946044580c200c0142c03029104903800500500c00007040107001c02000c070b0280c040356010359103030501c070001041808000750070340105e03800103010f07400203004594110302e030303150740d030802d103545450800c06840e00c0500d80c40d00c0d0085004200c241404000025a4144840794070252070260750171a04a0f43d1940d0319281040a0034038038080302103500c043c01d03a00b0204041200ca000700200155400800032a0103401d00c092045c0110b41b185601a004146400c203451160015903207440c030b0003a400e8140007042e0040380c250941c1c1e052901440d42c2c2075800d10b50080f000d41940d00100510700d802041d8291504108101038119001448550000b0700320402000700c00c1d040b8100824a0740194004070b441501c200300c403070f403440e051000716000c5c08d42200d90314041e1502a41d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 953389910 1250 953388660 953388671
    0x4240f0b030c09060313140c0120060103031805041a0a17250b0315030c030a0830040c031502030402030a02190f1d0108010e0303040f0305210901 64
    0x1484100c1c0c002242e585044100801c042c00306481e20701d0086600500b40c640048141005803200d00c3c424030601d12058142e0b00c81581c58101c0d680106003689810003c03207400d0904d0031201c2e14a503e51906200050508c244545004000c10b685004803026000151080010312555090184900c44e910110b501416290350080703448000010381d0031111010200822140380146003c83d202d40a070160104080c61250b00410520310b4a0021030080701185501400c0c003451004041c180501420198401c5e480f0442e076a002a03d4403040d104902c070368400c9100d41540061b2142403d030006901c2c81094880481044100000e0450500c2902e000300f051030050b404a94000007240300948010758140c1c80744a8640c0186804403000070704501c44440b40c4000c60b903071600007800c98080c0c0c1040c2030717819112849001d822a8080c00c1401041400024800f405024090940301d11001d0b10243c8821085080030701814020011a1003000c100184000220b079400320341944444d003503c03804515420326 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 953391160 1250 953389910 953389919
    0xf02400c050412030f02030d11311e030804060c05060a110d020a0207080d030c0311030f04021915110d020c0619030608100b09180303070e04240f 64
    0x8000703640503629560880348007242c10b52005d942c116008407450085200030800307101c5100b0b0600803129000c07812075080741c0f11210717403113060042181d105107812010540040380750300b60a104003407022a800404100f10b001c402ea01d0321103005449800c09010310400140003e40c1541c08002001d450b03001e0415500d464440b0300d00e00d030aa441481003002c10340810303c100c0e803650000364028015024203004450700c265458a8071400c00782414281b0b00401e40e110b08540c51260980a404400301c0c203d5051407540c0762502d4080011080036002130b000b216804869600040d001d0112005818102c1d01d101c603181054600820f040b815100d80d00c41406500420110340f80000b0b001444a81c004003070f1810600c030b10350094039108041c0341c100b04240c0c40d07180c0040c0c41c440a104a0314840b580003004034041c076120044c00381d405805404031859200d0a8919003100f6408401d0300c0d00b101552500c08031110f070002c0007801420070300401035008042c10031103814004170380b07409804a0b0b1010f8110031041d9030782c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 953392410 1250 953391160 953391167
    0x21201020a080601030e0c040606021e01020309030301031b21060c300b12160f060909090305040e09011d010e0a0f050f03030718120f02400c 62
    0x700d50040e8081901500070480344e41c000d0b0401c1c50758408920480303683c0280080003d003618407503808a00960071000800c0d00d642c00003140034035003070701c6000250305d035003000301195540380f00501c4003904000880c2d40c41d280440c00c254042001700f4003030364401224580d0513445401018001d070304a819a140c000c61155142c001c0d0b0407404203134114a000c1604003613190345a1500c405070805800080d565020380c00c110350310350341840060000440201a012780d060f010295108040d04680740144e06900100701807079100401d0801e95690600110341c1d9401c03880c1c00d561a004035080440d141607100c08001680c601540310101100845115100001010031130508039002860000ca0a8101002400118a501c9070089015118000300e4107220305002046055800076a0740d5000030b1201d00b03d403a10030080b0310302100500750210301c0d0340725403a961f5a180c400c0c00c0d0010700240268a08144226105048802c10f80031041c2d80302180b1031380c01403145500d0700129480000d44001e1a043c1d005030807610 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 953393660 1250 953392410 953392417
    0x1c211d0715030b010e090402030f1b0405010501031806020a140307030e3913020c0303090c030327130c0203271c0f201c08031302010504050411030402120102 69
    0x6071550303119100542c081c842006801802a40c1610034000e400c03a0340e54ac2000000d00012090010000050658003008191141a40320301e040509210740024402e003228000001c0550000300162b0b0380b11505025201020b6040c803000700000d000c0108104507030160441d503000441311050300d40440403c2510140602d8900c0c00c00962141d5100e401000c801480841000060040040c580030f5005600301e0300f030364407003048103120350808002d000700e00074208030035909400218051410807100d0030300581200c94602c02000c0820070300a0016090b2222884800c030031510310300a10032240765502c082d42c1c070303840004034185174080c0741c0001c030a8840043c1e0089050100400c0034440030307200020a0190300184c081038402d0804200d444001520344c0d07503001214011404680c50f490303685020030800850007802c03507025040700c40880c0d00140009003200c0c2d001c0e40c80511080d04801c10300048940340a039070415038002e8a0846404540c4040e42c01451165208580c0c1025444c40b03d0641402c0c0c0c003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 953394910 1250 953393660 953393681
    0x903060a0e030d0f0b040624050702010c020d02010e03060f100f0b040506090a1e0f06030c0806120a0f060b0f0d0b070804022d01021c211d071503 64
    0x402c00d010307424589801d9040003a55040d040d502140103190800010301300c03001584040c0f1100c0013210803005102e581031000b4901512410098103000301d0360006010000d40c4c24000b44607440488801045a00540380d102d88500054105c4a251401c0c104203800c180080c1c0d50380c4d4074400c42070380014200440020380e20648240b21082e40c201341c54441801104e4002058650b841240711801282c0b80074a1040d680440c0070b403501d006852482e00100800c034813415008541014100f02d01c00b01d007507070013410760b41c1c10143c161400c0003040c107616550350400342450801805900041c0d8500240300154002d03040e4030304200e8181710706c141441c0c03c000d0840701c0080024807030402d1800141416009590b250790190010b402d18281c0c1403076509010305c5c80b4886070800720b0a2a00130100001d542c0c104a8140c09040e110207000c8121304035400030703003c0d4498054800c0044180d081800c141c80c400d030800c071110f034020b8040300d00003070301612001c0c0c440946015004000b00d8010800c90a90301c079002e000e400c10f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 953396160 1250 953394910 953394913
    0x50606041a12010b0d08040608010905060906300a0618050a330e0709020c0a080717190206060102011413020316090614030f070e0a1b050903060a0e 65
    0xc02480d080c081296810005540b4955131000503e8013503c0d0f001c0544540c500c43d8100c140e5640c00c0c0880904032070410380040c014a49410300f086056243e400c0500e402c180121881010955807100408400700c400d00c240180c982c0b09805d80c10703801400550714180d40d01c195020f0207580b00c1008240c00c4c8240c204000b074100d03400803100c82c0c041a002c0344140700400a002d40d420100c825954030341413608070f030420b800c80030b0b40d40c8600200d0b90b402400440701a241542d030542c9021021207400b5a9003004003805040420001600c40412004804107180110441107664981c0009040580400d4851070070001501071000044c08541c03041c440c202c00c03444060004441c0340c8482c42d03a23414141580e082240c0510500080c036158506002e40c40c0010144080049281c0c3c1c01c01e03d480e00c40003501400503000e540000491002c9a80205042040d81c0c451204980d0702e0b96030450f954081c2040c02912040001641185812550301c00000d140c0700d6030540131aa02c9441c0c1300180400c43d40c0c0c1101c8060039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 953397410 1250 953396160 953396201
    0xc0f0105070b1e0403050408190206090103021c14040203070e0c190e120105010f120203060c1c110d050610080c091215040302010b0105030c09130617060405060604 72
    0x1030340c0540c00c50f40242402068042c0c66a48090400c0d900c0c505481c1035010030808201003040040070002000c080e00c101003c07940985066000c10124083c1d080d91505064021500440e1050000300045618551a60500c0500b12a03440c00c100c0b600107a506900a024801001c215007600550342401001a01b10040c60070f210919582d0004000396000c0c001c000301900c20a1143e40c80c9c82586581c03c41c1d001c00001e81d035240050782c1410400340d6002d04000c000703185000307000d0780d404a0050307402072617038035829503035003501c1000b00301c01c00d50b5080301440d140381a10a07001d0042c84d0700500740d0040c502c0c01c00c100c103494100802c0341d14002c001c4a54006214800010107080c40d0b0380c05014013100c090984047c81d01203000040c2001c140103075440d8602d8055080005040e42401440c4a0031828205a803035401c2c648200d1140740702c1c4500241c0a41d0b400c00381c051a402c85a030200c0e000b0402d14a144c091441c0c2c000b8002c3e12903006680c151041e11072000494a546420320801e40301c02088003540b00b5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 953398660 1250 953397410 953397413
    0xd0f030e060f1608070813090501060c202101090606051c060c0e03010f0e0601090908040b0c10020703020a060605062a03190206090609010219050c010603060c110c0f010507 76
    0x3003085007510304490345907041c005c007000500d07900c0142004200030181081d055041110030360480c1c4d016400300f400c005c1091070180c0450040102805036402c00490122520301640109041111346814510406440c8d090940d16020642c0003a2006124100510a86984a00f0006034441a48245030380c0c503544013105d00050700710b510850240425080407101c61220b48002801c6a030300d50704e080c07040d07601ea81419200b91410b000c41409800d2110301000184100d07117803114680503601582141c0380c80043d04002d0f00104001441c110250b0304029981c2d503907140303802500d4211404084030080d040c001c0200e09450f0803420382d400c65042100c0106400c1c0c3e10310000c0c4045004070340060039070100b00f1161608820f4002010301c094402c4d0001e1210b0305210b0003030f615000d0010908003a46e44140301042d500e841515261407914114039159407038030303903c20200c1c0c010016a0b000421491418850b2b569150700f00a81c0b10759600600140c0340004070540a02105000720021140011002c011000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 953399910 1250 953398660 953398687
    0x705010e010203042d0606080703020406050618010c030c3e090604020a0c080f190e241207030506010e0603040b0408030408040f08030702130e2a0d0f030e060f 70
    0x5510101d0545c080d44170f4404d844010448520b60006505900608402e10650030280544401401c041d10594540040c0c0b0b08448042182130a00c0c40c104030740c080d228401e1510640c16280c80541018070050241c0480c4020722000d04400c07850601a1901049004515207004107500469005002085d0f2507540c04100002903004103410b0f018020b441d455a00420103501c0540f068445104455555000350b03100000c0c4a203003a85e900040240c0f0880c00380322525050260040c40c01c01d11030880b0542c402c20054605802a59000e4a28081200401896030b030303d0342100340915002e0704c031004030b00504030520038144001c45010340100e92120104000652520081d54801d024071981c90605884512200c03001d04541d0080c40c40e40c0c8045140000d62820074203800444111440800001000198841d00c0701000d40220f8610981c0a40001441070609100d1094110050074201112000d03d80380301d02c0102414241c000a031112030340080c609209080700c1c51500c0740c0503460300b0f06500f0707071303030b05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 953401160 1250 953399910 953399963
    0xd1a010801420801050613030201140d050a1d070f050d05030f040306090209150f04050405160b190e0a0b180603010902070203060c04050f270702030705010e01020304 73
    0x2c0c1240c0c605200c0700845500c0400d1010a1615000c0c2e031448903007804400602e041c8040c0c20991260b142000000d455020841c5500c08603030382030800070002081d041c8442d409025031402d0000c5a4181000c019001905034080c4410010f68000d00a0446400441c0ca47e10081d034050010102c000642c24032851900c1c880c4041c0c9036108800b10381ca4030009031640f4800f900168000c449e0980c850118104514118880030b070701403c0c1c0b441c50341000581200103401039070301802d8240925a04d00c080740502030103100c0d0829070300200d4042d0382001da48130312514180d841901d000c0e2203a0f910580101c00b003482051034a0030900010004224030341401c190482c00d6001c1001c03802111200000c01c420b6844000c0514020b003120800140c4425182c010b040c00c00e04014031086900c08104810300507680c44006c00c22008005640940b07081074a9006541d40031440003425116001010410560365030000060040510450003400700a00703000b841400d0b400103070780050080c03c041c44290081c41154685 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 953402410 1250 953401160 953401199
    0x4030b04020f030307141b010e09100312050c01050c090d0206031e010b0406030c020a051f09080c0606031b0a0b0f131823041b0305120d1a010801 64
    0x35190182e4000000c0d10b16400303500d045801444d943c0b0300d1007080300701340966849507441c0c41051809500690000b0208400d10101c0e070f115101e04400b154000740b8214820011f5503101851b540d600c01007090180098100900854456003844005204209410161903000001400c58503041c0343c80d6082119680000f804603000d102c040d11050702840724403a2460090540d000b00540d51401c1100003010780304022000c1c02903510598071100060000940c0c503080b040100403400d000040e03e0401800b4108040b00540403038004148040b5505001c201980152011030844d02c110300308129140108107144e003a503a120301e10010411001c00d01c000103040f0110078050f0685803954180d0394006e00e80c80c41c0c1100d041304c41d8141d0500b100c001e0901c01c50358a9688040c0c5500703181c0d1001044500d03010000d10041008841b203035801c0400e1411281c0101455006040e1342c5180b030180b059500d039800800b2181045400c00320005480e01c1c01c040b030040410010b94a5290f030f0707800c16000000c05c0121482 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 953403660 1250 953402410 953402419
    0x1b14030921031917070c021002011505010f03110310060905090f1504020417070e221b0e010611060f01032a08030a09090e0610030f020a0e162304030b0402 68
    0x524401e004d11040344a1180d4165101c0c0360714103a0341c1c0148600d0b204100c042509580c541a5600ea0f000150503644080790300074a000104028110307011030103009000b0340e003a081c140c04801d120180b201c00206506a42d002c0d0345804050b0f540704104225032100f5501429920140d4004c13403404120410074440b11000a007002d032416982d6550741ca040486842c4485158020841c14030107401c07801c3d2240d0b0481d9101c01103c0e2041c0c0c101085422807040150001d109840144000d01e5480380c00380170a00518804c1c80341c242560707545c6005001da00024880d210280210400201c0360340c01003030003034140c1c0e40140300c8803503012100004141c40b030482c02010100004001d0300080d250340410040040130b4043ea1040f6005140c500380c0001e540307141304400602c0e003051040000d24002c25030030300112508650f10040001150021034180d15042d0440c010128ac640304100107040409402c100303400140c0c0d562b40f02c2d815000c0c0c1e8aa040300140444440d416420407041011807990003403660083d00081c07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 953404910 1250 953403660 953403677
    0x601020a030c1b03020a0602010203070f081509040c0905091c09030c0b03060307170c0a080a0803060915060703030623060315040f0f06060206010b040b030103031b140309210319 78
    0x100081c180305810f81c1f1010042c0c0d0000100140c49501c41c40c1c40940700001e003090105030505403100305001c2d60800702c1c2405180700c0700001e001d12418100450060041030010020340c1001c040464454045851820307510f90b4a803420b034111032140029404498109403050b00140c20f020321007100d584040c002070b6052059110104440e01ca4004002070b04407944000d051219044041c40001c014640c4031030707190b1b04200846000f00d5101d10460f944180b003100c96003000d98641c0018a0800c1c520fa064581008000c1031400406401d070b44014260380c008d010b416582051030010090005401948580014062011400451110035400c240b03010042c00400c0d0305000e03c9240e0b00b01c0340c8450000e02d030941c40c9e207410042141c043c04858003614640c1459864203090030b420903800d00c0180300050401c0003205110061008201203910b9459000c10700d860042013052a0390360700e81010b801030303100b62401d0391b0000c1004504103006050b922050702541c100703501c6090006d0813640e005800810301c000309 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 953406160 1250 953404910 953404913
    0x5040203190f02040501031d030307030b0a150c03171005060c1002270109060e0d0201031b0801080105010f081b0d02090f04060b0409030e0f0f0a0602010e060601020a030c1b03 77
    0x1401882c00c0c49581a40c0141c0700d0345401d00040030740b0b1139501e0705070452448210380004680080200d036842842810b0204200354054082241036106603c07007030040c0c2000740524249540180c0c40c4c0551030081d45d40501144405961100e902c1c0c0c1650264103a4080d10400c0180b4180b1001802400301c9460035038019400704c3c08040244d901c41110302400d1201840840c05065404428289482003841d1032010302e420204040c10006403880801c1c49100e44041c240300b10b82c0329401a03100500c180b40c1c4412801185200544094001c0c010304a141d402c2400220307a00620641506c2101c5d445401441e070481c2040c0d21400c2070807403890503600b00c0f040c0070300740025889800c0224010558142a00b1031494a810124100c42c5d03048207191059007070056443c0803e41c40a901350103a00c0c21070340c079094881c1650000c2e0551640040060b00a0003070f030000a00300d50198401110508520f0990701c180e070394007004a8403030303850360390040100d940a204100860410342243c40351001b06180f18040585a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 953407410 1250 953406160 953406211
    0x1090803040e090f01060b0d051b0406050d14160c06020d051008010b010912021c0b0910050f012904031506031a04020f040f0b04050f091e0705040203 66
    0xe0300809a80c41200c010f01203520001c02200500c4551400200013140c200b50f05042d5a1250054a266903620345010031402110302c80000c282e0803262030714581d25542c4004c0036100303801c1351620340c100528052a41c0744100d903d0003100d100303030b115040300c2d58a0513001d0350566909124400541b82d0503428000042c8880440c45179500500c80c0c008540003162609400a0070b403219044102d0400c0360340c80c0100071024080460760206a4102d41c500c0317a02c11f01110ac8030584801c05000384c0740e5020b1005104000d4800300d015100300702214070070300c010b0b0350714405054850420b1003003160800c0e100b92100560465001c92482011515610034507040e6641c440030301c2040d840301e8140310560b68140410400408102002d810700703601030103a0680c030701500020001800900b1141c003d5484124510700112654000c0642c0e80004104000508158420074040c10044800c1441ca10900c1c0300115402d00703031181100000402001052103504110030300c006504090321301d40c40c06820000000182a6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 953408660 1250 953407410 953407417
    0x90607050a0501091b09020a0f03021b0a2009060d0b04172b0e07061416060902030613050601090c0521240303040504090c05060310150509090402010e01090803 70
    0x30345903019684003080042968010710341c0c000140030744100404280072743c02c513002400c6103c1a00380140c42d0901e04180e046c82c442015046009401440c0f0800100b1031090b9902403001e204501007240510f501051201e0b580c8141c0e102e41c4e00c04844007240c030005040b20995076002d8440c10517100d000910710030008039500103450358140d80301516040c1ca60000c856000004c004d40400051040d00d00c010746050f1500b950340541c800f040b07000ca451003405104c4000321021403003a4903284041c4040c90815100521484500704d00c20700030300000c03820380c449101c0c0095000f81c0101c043c5c02c11764a130200400c0103104050080f0280038061000c2e0b03540c20500b0b00a81080c861342e000340044e500c2d0812502c40ca01c3c000c01c41c01c00040343c11071450505a1000400d860aa94065400041045190400a085000f030f940682c3e0700110000c10018500f40b10450b4004807429041c03900030304861144155017078090f107070225801403050ba00040140d8812098070550f10010b0400801103030715450041e05552 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 953409910 1250 953408660 953408663
    0x60f02040312050c16180507021608071701230618041101030b1002150606131806091107110f0406080f0f0f071a0f0304030909051605090607050a050109 67
    0x410105400301c0701381e020f01c131441501034855034100417035080070003a40030710a5000e411180b40c6d03503510008400310b0007049000103d4481d0b210f0407070b62039621030003160b513410f59010314400110b40122076161001c0c1401400010b04081e05000304164070341d1500641444020105070344042c07006004202d410700203403854001d5005460381d0042003540000901680e0601161902900040c0350f9900302d1640410642c0c4003135811105056252110800544039014102c0201da17001117800c0d00081032200002c0304803200610400078840e4070750315009001244c001c4401c2c0c9682000c10000344000135085111344043d104001c04034452040c0000c081b90032610950021504c0e54032600d100032030713000c04014003148c1401c000d0040003401047c18078903807140100c0c404c1031075014603044901030202c0d440055400c408011200c0d1600c3c0d15003814010040c2c150b910800707403010300d0500807030386044050a41d20031504041d201c05103040c0000381400120b500c5510241d0396030040034003420001c0c3d400e004414196 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 953411160 1250 953409910 953409917
    0x20a0209070825051605010b0a1217070312050c0d090606052409190b2106060a1d010507060207081809010e01060c23010f1a0d060f02040312 62
    0x2483d2054500c008030080d203100c450721042030340c1409203c0f5030000845844260031124812102000d103011800b6180306981c899100d911624040b8000b4041d184041c0402d000d00f040e50342c8030400c41021203140c41801400340001d10800600c642c403100035000306802454038145d00d841c1c60407182c9a0b608981090701d0440d280c60311500100b0031403901c4194115651342e00c510700900012081e05881c2c03580305079001c540c0030f4401c1c03282100000c10324014a00c01417110007604e9542c0c0030382c1c19490f1542c50704804088075042d0302201007000d0b410030009640c8803543d1900d9078003103041120050620a00c500300e00b141040410040030300012800c0c0040e2a50a2291051544854401d44001000080180c40074000c0f46180d004001c0b2110b00c0715a41c1c1158002d060800e42140181000c079516151031044001180d5120300d100f01e524415800f03240c100803992410041412042d110210303551080003101d078817880c250708410208101d584100c02c0300d9610341006103861380d80e507110b1042c1a454404800032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 953412410 1250 953411160 953411177
    0x60806061c0f09030e2e09080d03090309060c15110405030d0509090a020306035205100210020d14090a0308010f0e0109020a03060e0108070807090c0e10020a020907 72
    0x4140c2c20140c100c1700b0300411074046ca400c80c0c1c00d001c0001c004142c042214240b03a01c10040203c5107014200e505c0103403002006544200902010160141124450440000f08902400074880340b180f40d480502c10f510003030031f01320240040b4100002e40410b01c404403001c441000002010359007009151200071483c0c4800f42c0340d91010042120404005101c0300f80f039401001045160355010603900ca4a04c0d40341800c1d2a040f10307900c41404102400e0310300391003070a0b4501c01c1c0c011007449040101c10103594042c0a021454990f0103001034003030781030070040c00350f408000724400d83d14241d0041d000269490700d00181550360610a01d8032520203036400003058100803040001c1c181d2040903640540140407503424000d2030581104a100014818500890360100d1652040740c480d4100000818810090f40000d585441260ba03c601c06449410300c00d11031060001207100c201c1c046d154010070242c540458401d9540c1c18030200008100703515045009901320503005030f90381d0025030301804041d5142c103030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 953413660 1250 953412410 953412413
    0x708010c020615030a02090907180209031014220c15080109060806010308090105091e210a0b1806010603020702040c0309050a14010209030613060c09060806061c0f09 73
    0x2d00c800a80804044681000c0b00740254900043c810500c0d0341c10348038081c2d941e0385c201c0001d003440301607081030b900341c00510924241260560040c04441e0300c200d060b240c1c807450340f01e641001c070f40d481d000301c490041001c4001500002d030100e0039070f002c0060404802c000031040c0c2d42c00c2480d925a8014844102054021542c4191301a900b540075040d840c904008003418074040c55a540c40500c0020510000041d0b0000d6030b0340300c5c00aa81c40c07100007409008010706003108090070100610300c0c2c9030251750b901c50014135040d05c4030750002400f412500500583d16442c3c80301c0120403401843e602ca11192030b441c80c10100420402c0302d001340040c0c1d0b0010b07102c40d0684100b0090f12956000305040600b070004a001140380415421900d65105100030041d5100c3c000c91400380c002c2e0f41d1682d5141c050a0104414011003082d0000600c1c4610020442000328990a440e042194015440051b25000000d5514288080145120041400601c03011302d00c54200f1000c0d036101c2c000d0030858640f41d200280 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 953414910 1250 953413660 953413663
    0xd03080f06010311030c0c0c10021f0e0d0201060504181110020a02030703030c050606010503010b120714040906090e03030c16030e04180c0902090d02060d090507031b0803042409080708010c02 84
    0x1e210004440300272020f00c09541c000c3d95900803401040380107034500350302c00c9025515030280c0ca00300032807006d541040c40310301006402884203104981c000d9051100354250081c000c0c1200d0406c95100710322205224101c07050069252b520807000f002c2d44180c5c02031002580d13040000d04001c601c40d644462950340540391950401c2c1c405840c0d03a040c0706081c00140300200e00481500d590741500c0b01c0305c3c0c3c100d548107503044a083c04000610b95510347c0c002004940b6000c3d6812650a90300c1954007848031070070170380c40250340384003c81c2c0314141d1708000c2c080d82d20308038003001106030b52034005d03e0490b0742108004002030455102600d0782090100d8072a0f180204610400e80304010082120118144109400801e00b00890b8490080c81030b0800219001d0824203644003e5143c1c0c0c0040848041a440b442c20070314082c0d40c0702d4070502900040c8000030301d82c0c00000890302590449000d42c03c8c20644604019501000c4e600644244a035905010503030362010400480289025000464640302249019 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 953416160 1250 953414910 953414923
    0x40807150f0912020d0804140306010f030803131b091a040903020c0d0812090a021c050a03030e011407050a030f231f0308090f0d03080f06010311030c0c 67
    0x4400740114a4040c030303040c64005501c0e500b00c60212040340c020701401d00c00941c50000d1200000d1907444007150114040052040c4810420810b03400c48805903200c21650000c07030000d20004000c00f60400000c1d10016403e01d01d00c0c14503100d0314210b0703112145c0002c4448010110380140c4105a9a4810070754128400c12080c0310f1280c01383c4081052400c41d480c020b48814a10820720701031a50102007034200141c11040f41c2c01000760224490b07103418030716512078030b407011b420007644101201c401c1540c01d0701e0400d01c3c4074561940b040080102c4843d80d502500540702c460300f4141103544e1a0100c0541c2e56a00b90080c0c0b041e11142e0324180d445047d030001508903a094204035062030301d40b44c0e0018150080c1902d0710b01d0000c0f900346c0300500b5651100075a00c6006010000c59611481007000030400c0345e140302a000d400740444001182c6031401c014011148044500640011042d00200c1c00b080b40101c0345170b80042040c500400c8000f440d07158151181e0090715410203181c00043d03500c0c00801e007413122 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 953417266 1106 953416160 953416199
    0x9040204121112060a0c0e04090f021302180f19080a020a0e070c140f03070b090606100f050a2619021c0f11040807 51
    0x10208860164007102c42191511012a09203080d2031102c994010003801403000d961607011300d00c00740034141101401e01c00300d040140815203039070049120150081c0e05041c0c00308040d20501c000001d00c04c00c0304c54110710601492100004511026860020032219140500e004d0400074800500d02e4107003089403a0041c0c0000703159400450740c61030180c021a81700501981e551007025111008494081c001446210b1507030000b42d02c1010000800140742c1254403540407544580d26645c4982029500140e040c1c1c00c20221000c01c0100641c055015202c00100d54860031001c0c0200c00c1c000071000a1100100303000307800383e2040c908144100103039210510302019503078800105042c161400120340700d020441e1004039446008039012950703200103100380c00c4181c48420006120b0042d100710303040d0701d038810700b021100408054000f0305044070141504900c0c0c211000c0303140000307245 = true := by decide +kernel

theorem cover : BRFrame.Cov 953237410 953417266 := by
  have h0 := BRFrame.cov_init 953237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 953237410 ≤ n) (h2 : n < 953417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
