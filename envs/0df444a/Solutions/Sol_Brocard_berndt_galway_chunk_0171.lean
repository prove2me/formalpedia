-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0171
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:14:46.264985+00:00
-- url     : https://prove2.me/submissions/794b14e0-31dc-4896-9949-9229d6184e30

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 30575545 ≤ n < 30755401 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 30576795 1250 30575545 30575549
    0x11240408030d23042315040c080a080706020d020c030c03041809020f1509060a0206040213050702030f070201020a150b011707020712022106041505101806032f040501 73
    0x83c500305000040d0000d03455410704a9481c0201d025080c4101c0381140705402c0000d506110081e1040f02000c020074882c40d141410000d04040d40030380650170548d160b0144500c078110010706015000100c441c0b21100070341c102c03030744510458156500c0d6180071000540300d178006e1046140c43e02347d0748040c212130811032080c07407001d40d8002c0008000100d058281302c0c01d0b8041c400b000702040c2007480310640c1e680301c510042040c2c902e1903014203140c1c900b61041101c81519050640f8116191030308000240381c00004139076044132070140690b141d001a10040749040000000105003116054034001d4103465508001a03415003600c0e40a0400d03851140000031070400c40b10400143d200ca034080024a10ba9a0484580c1d4000351084901e203c1958210921030b00c088000341c4a503112a040000b8000140f219071408142c2d43d409002c9030403c0d1418425083d814020403194421401d801c00b035102072a480bc0b00210b5024036031501d10004111a000001180031100c0107501c02e102100c8400c2c50188142c0741 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 30578045 1250 30576795 30576851
    0x1060504050d0203010b040608010f05130503040608040c120303020405011b02030706140409180203060a090302060c0a120501080309010f09050d1106040806010b19030911240408030d 80
    0x418545801c042201d103007070b082c5003640c05550798840c0c0559511140180405841c10340000316203c0e000704491400c0b01e6000f003a00340001041c0640e14005039001c07049030b00712000c601c2c002c6000d850b070381402e4108150940c404008904040422001c01da0150040d02c1216426200c42000c440070480c0c0510840711020000d6050300965001e2146900540000180040c02c00c0c00d00c2c1003c2d00c5184e00c40c01c0701d0940c02590270101e0303644460301c114039080005507805100c50105102204060340c0280d6103032000740404913821008100844032902c950034a10032403207000c40c28003041d6502c0ca035150b180d9000205250000310100d01c00014540a11810411210058200030034080aa00c6004a03aa0442c5c805a07210804100005a80c141080118007034005540c0711940e8250303008406000e400c911f0100000c3c1402c2401c4200030641d200684040048199050001441142c816000c00305040d00b54448290700810701188000000010f84648000d140d01088030b40e403c040c0c0131140b0041e282d500710b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 30579295 1250 30578045 30578047
    0x90c08100603140c0d12050705010f1a06040b03010605090d050109060c090504230901090803041b090b06030a050703180b010f0801050610050a030b040504030e0a0b0316030911030d09140603010605 86
    0x41c0043c0a0904842c541e120b203242150600c0f0681c0c2d09c0301d09550540000f141a0307611221035041e0300c00d0000c1040a010030403548103140528000d414000c80c001441144280000806c0d0300a164803a9201640f0b001d9101000b088103251500c2c05800030301c0c03c16154000030700103402c01308175402d113441041c01300703c6940764490000410000480c400700303004000f8100c55407181904030000e03914201540c080e51292076400d180c4500c07004104030700941d640c4003c0702941000a02c006c0790300e481c4112500110340420100706a40d410071f041d005414814018001c80202c18024000e0004145010b0705840244c50b1a00e400c0303644541144c00d0390801d44a242d8061200003682c40f001e4040c6000380081c03045414007080031400c1400003811580c00721419408140803074000304440c546400b001c0060140c0003050350071030800500d5019000390388000d1100341641d0301d41400501080d11803410030001e004044414108040078000c1c6010003501c00c00100c01400d08400c9a00d29100040c0c1c0c1c181d69407581e8032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 30580545 1250 30579295 30579319
    0x7080903070204051f180507090e040803070c050601080312090a030806090406060e010e04060c0c050303180a050d11070f03020d020103051e090c011206030803010306090c08100603140c 81
    0x4090282c80f1010349103101c2c01120081e41001c140b680204051031006c2d10030140c1448902c00d4407402040c034410451888401c2c04420344a026141d00540c100f8150354403503842d04419900c840c00302c1000780103071040310000a20b42c0c40010081a880ca074014580300e079a264842415038440b5915401800700c0c400f04c00050440c209011aa94498012200030450507500c0c020070603d01d10a03040490b98054040401c014010a80106c0c204102286407005189175a602e03003a40f24000580303801c203898042200303000102020001c00039460342040584082003a035400c00f4103c011410450b05860049001c000f40305a08c0448030000c890700a80400e90031f800e035500450007410300070300401100074180514684000e000d8541031003220b03004c000700902e00b641000580720310302c0a00c891200b0f40c104502807001400366403c0d02c0c11240d10a8021952400e68034100140c414650032010151081c41141942e400d0700f074201d40c048038011101408003504511525440c0d0000011103070b009502000c074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 30581795 1250 30580545 30580549
    0x30c0503191106030c0f03090105010f0e19050703060305070801060509010b0a0e041d010513151503060905011e05060f010f0e0108092508060906010510030e010b2205070809030702 79
    0x156880510543ea05c0d25085517640816060707082500c10f41c0b0540c0d521001400301080c640e0500b40500b140c501d400004d880c00d44503100c005800341148801654032070000c503c00600a4101d00051903000d0141d4124a850702a4503001b403005100b02842400e6240000404e08800e40448607004041d69030022000900c0381840090000580000150200b028409070100d00c03c2c8103040c000c4020540701c0b110b85c41c2d141801c4600900b4901c2605203185000011041803c10308001003c0b65841000890507041d6810700500502c99008400003e1058003003c000c041c5041d84524444d42c0100c0e04600302c1c850000044030105c40001c110800700f2040c0785040000d43c001d0032000e5000010004035215102c410540d0590411461440d01c01c00c1145030040c06482c100340521384d40219160000c200c50340c949000580740001e44100c10041c182d80f01d09049108000390014481c3c04000b81081c850a45c10481c942103884102d158090391a2500c000316040c180300f940320034021114000110700f8014142c007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 30583045 1250 30581795 30581797
    0x1090b090d060f0207050105180705010806030708030c1c090b030402060310090204060e0901090e0706050c030906070f02040c030b090a0c0c05010903050a02120301030201120b0f030106030c0503191106 88
    0x2a5a50018008000d00d000420030302404005083c100300240e1500240d1400c2425110043d0206a090141107000e031109080000c00d801202c00074a0800b5081e03c0f003001003820607089810050a40c00000380d40002d2181c009450447c810002c2c8048103d04c40014003169112a5809403418601c3d0410104000d86040005507801560107407140c6202c69440c81e003001241c0c025400000032907007900c50f094583c035054811500401d0311120900c0780060794001c00391624220300403181805808034014101d12000c06c146c650051018202c140d8601c141e007410382c1b4940284100b2032046007802e20429040c6d2080c002e03403d919002071b00c00c004039142c90002c0304c0074145252943c020462200d00c0b03400820401d0084090035402512129540d4182c1e64009041034520007a00708240e1082004000503613004415462601c0542c90004142c030040000a1800d82414501e43d0305608000c800320070302c59241498000c071030084044419090214041c84020540d0b0340d4041c20282080e450000d0608000f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 30584295 1250 30583045 30583057
    0x14010507050c1323061005030903070b01080c0a060201020c060106050a0212030f09070e010602031213080706061412120a0306030c0806010303030518060414030c031c0f060501090b 79
    0x60150351480180300c012034460700e40001c1910415441384094004907503040c0e08040c2d0000481c200991030702d0b0032404100f604903144c0d29501008800400141d0040c030500981c0e09282d40005006046c3d41d40c1c0380c00d01e50300c100001c0518440d50503010000380340d074014401c4403408103945002d007006a1806da02074566070801c3d6864402c1d8020000071a0445800c1c034001c510035072000f55126101d0410b50102c51800d200342d00050883c1c0d94403401440101d40020584107104442c802c116201d50301c00d05e41d03043c14036424400901044001c68058100708d0741e07421007000d490f07140440490b000d40e04020002508801d01c0c0d90243c40d0889804c43c1c001c901510010400c513500d5003404604e40e541d82d43c030501e0b00515070784140c01d81c1e00130000507c1019854040c0b1600045041d0300035020803030100f0f20588901011380000e241d800c0c140c441042099051056408008d245410340b511904400d800b0445400309105040030700b4600b00e0016542c0010f44241801c0c0d580603500c00070840d0509440d180a40c0c011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 30585545 1250 30584295 30584303
    0x102100e0708070510090b07080d0c0c03020609160314120406051809010e062e02011a03030307050a12020f040312031503050d050d18050105010303020709050114010507 74
    0x58104012406460065441006045009101081c90710034141d08051981d04540d1041980068090800d60720501d420b05a034401002d1941d24400c03460040010302c00d00f40e17000c84003810004103014040d040351810030003901070b400341d803090754850b80c50301d4548004180c000140a51485c0a1010603030000082c541802c0b1082100d8081c062614010b595070400d502a60008d48009206e0320b03c0308201000d0302c046181541c06845550400c130f9042c144240042415008420008540c2d03040f40800201c00300f004503d9188050584460500a010f03000001c2c800307902101a4000700b14504002086922030080c990f562400c1c1404c0e4403084914115201c0b4000881d0f40a21107400400d0500009000543c864034034004103202c0040003400744e600e41d420850942100383d50403c0885c00106440d640d91945203042651203d1700c820b150000c01d090804904061100401c0c1c404018055110034181d07406a0212504141c1c1c41e0341c84400e4810034000c408611080c4500d03188254050005020030a1103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 30586795 1250 30585545 30585553
    0x90204090c06080f06010f03090c08070b03190b03060c0a031b09080127030804032a0303060608040c03060b01050409060b0405040605101209170c010b01090803070b04080702040212070903060c05090f09060102 91
    0x384d1220bc074905a41e80d0004000f400c000014403032003100f100645012305040000512910320700c034000a4030740c035001304448060701d400610000d03428400d6000c4500803160321902486074003003403030040038881140140c80d01c961071f1000c20700d070744001d0a00d010090414004040c2000074a650704542041d000780088050101d101d41202c04030b6400403013803080003d40017000c200c20381f15042c002c003900d040340d100b2400e20444006100100d140d6200080076240c01101c00324070070070402c0040b0b0f5184615400000388924000b804600103079407500400031104c08072024031505469a080124101204054802041c3c001051140082c0550003034401d05000720070300d404a03884e090200c54a41d00c9441190f0303843e55201e00c0921f01e507030040c5c6000c0c042c1450000460420a5079640e0101928014001401111000c110395007159129011104445031490b50032060341454107003c0d2071800340c0d003c103c4145040401c0004460320035000d4424252000f00448020340840c401e00c091030601400007411401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 30588045 1250 30586795 30586799
    0x14061504030b010608060108010e010e0708040311010609020d11040501051b0a0609030201140c03070f0806040f09030203070606120803010302040b010309380709060f0201090204090c06080f06010f03090c 89
    0xc11030000b50090074280c50320b18003403070044001030a00c0d10503000801c85600b110010302240707018000c4158030600c14240652181c64508043d039040d841d00742d51010b00e600303092000c118440181c0290040140760f84052143c000086401d54043c01940a000d0020300c0500c480d141075894102c0b2848032000840560700c0304901da450307201c15554210300036030150f07460341400c0c0d031000b215080c0c95600c480c0b894800c50a40c2084c841c000c2941a920b445c89003001440703408594542e45035401301c90f038840c509108001075001440e000c0d40b250400402070740c41074602280000d03240e908000e1400340d143d100c6075141c51682154204002000040752807070400d50784100c0c0000003000120441784004042508101742115400108154183c2038444845980248248045203030400d03a03480507518541001585400e07084130480c018845540040c0d0f0107410440130783c042c8050741541c2c00985440340d40c2c2e4a83d81c0d443e02410000003000f03860980c00102c08042c0454414469480121070501c00c00c44104480d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 30589295 1250 30588045 30588053
    0x2090405010303080f070e150919030516060c030906050c1f0f0b031f090206070602070602040e0612060109021803070b090328020d080706150503010b041406150403 72
    0x24030980080340071400800070b1102480a04a0040e4030550a01d003030308400b28844041864002203150070200c0346170100351a42c10356210035040344082e12455080768480d42d281402c9a541a40884958420b41c060a000c58503500c9100d0484003150991110700d03a4a160480417100c039400514405518022032840c030100f0030f0141e070411084d8030003c101082140220001c4411105003102d01352003903202011600b10a1a2400300040000032810000303103184079800810714a00c00e94200408140c40090020308000d8164003502c143c03031351205c1503550381d51000d00b401801c10481342600c0c1c4951002c2d004005075030b1560000c103180582c680344420065004008645040c0040c3c200044c03400c0045800c542074102001800104601e804205d03000e0040f03680001e400c00781e481070207800342080c0005441071120400441d509154805410801442c55560a8030070b02c0480c01144d10135400d10b00320051714901401480c0b2600c40500380c500850701c0301001c01c81720040b1407400020034801400000046 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 30590545 1250 30589295 30589301
    0x6010e070318030207050a060e0d0f050c03100203010303030b10020604060b06040f0b22050d06090611071b0e0c0d0b0a0b0403030c1401060b0403060f091e02130b030606010f03020904 80
    0x11500c240c00170100d49040074200009054190400702c100105041600e0745513440d0803d4106003a005050207004185900740b19042a00310400b9036010b01c01d03a680066103400b56401503040340e0180e5401c214000d181c1003001600c42c008203001005074060300110300440c81b103074001c407051400205102c0c82e103580c0e900c1007010800c05a1001500c00c00118811030901201a601246d1010710181d2454807818140051800c020303590010303051ba03a6035203503e005c004490713000000d0b440f1615055500d0f06034521300076058243c18181c0380c00c40c031268080001c001003002c0039075000c0c1e10816449402c2000d03400710b00e002040a00a01988640706d000c0000d4042c1000b0001c00180d806541c03103040c40c904509103030b44650495415030446a250090410610442d03000b84c8040d45d80c880c1d00410803030f40506200001e0f10208001030200341c81e030f0111202c02007055060f5521540300761812044071900110000488071482c400301c2e01500450005007540d84182890035213100f050a005062000b08400f007421 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 30591795 1250 30590545 30590591
    0x1d0103080729071701050604030305190c06090b090f010c0207090c050409050403020322060c03120209040c02030301060f090f0303050702030708030a0203130905090c06031b120a0c020703030206010e0703 89
    0x804d000004440708140140340032400341106030b0300145030500d950b400801700d21580c40146003c400d100a40c02074688540e0398105000e8000009104000d414105071004a4040e40c00111520540000c10810725060082c0221704403981c024103c03a03450076114101602d800148001000010000410000c0f020322880f40154040e500031902e4801c069140c0e0240f20720111a040c0002848004020566016464060302d96040c5442d08103450160f0085010b4001c6030303202d981c06810850b5080300325900001860403210b455907981286405e003070302520420050b0190444040d4039107410320129000c0d03402809510310181c1203820890755048001d0854004074001e0b00107070000668901c4500000451002805444404000904205000e543d5407000c84003100d01500c004400140e5240010444100d98a00d0100103917407000310702c00e06420104d04541e00074942e0700d0800c0d80701085200082c20b005490781038006201607401c0801401e104900109205c0c205510f40d004078513051012000515 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 30593045 1250 30591795 30591797
    0x9030c150402010f021906150503010f0e0c01050403110f01050c030a0306030c050109080d0c140a0f020a08030301030b040807060605040c02030d06080f0a06020705150c041d010308072907 82
    0x825007880e100060180050401034411940700146003500321940c041c00c4405580d00900004007001e82d50518600c601507035021960652070040c451a0401007600980030641000065407944c0640d60b0041d5000d020324000944403848500b101d001d2810620b44400d014141410814245000c4072542d5165602c40284640001c0d103400c0108104450504900040e1009080000e0b6a6041459499607401d51080340d20820020048030000d01103881002a00c0300311041c282c0703440900ca824610007049a400c0c1c120f02619481000040c00c21006c07007680d050302d602c040c823682252603d0700d0300842a04142419121265200400501340d030300d6108248200059401544d103466400c01e45104903a4980d002480d80d0308440050040c00d2404a1a840120340c495001a154241810858600301d42c90b030800c407440c604002072040c4210644040e100303c0d60310307148038503030804000a04d40740d8207400e01c0018140201030106200084140700c500521009000e0515050310715100a03040101083c4c81d507034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 30594295 1250 30593045 30593083
    0x15030803011205070503031c150e0702030c100605030309060703030204050616031704050606060a14030109020301080f0a0b040f0501020d11090301060501090302030303061002030409060311010e01031503060509030c 94
    0xb010018140801801418210007450901401c02c54107400c500d0300c2c0c00c810320142d5642c10018404801030034030b44081c02070300256919070300e00300702d010350790b5444416600b607244950180c1d16500e051900482c0161032010f8003a500b008898402c1c0080c0d80c100b04421002c4c10380034000800d15484140140c1000e008200050300c2101990074003420034000180402c02c0303223442c0400c000c003049000a40c2608031405030f4000c1c1e560003861030708494458007029610a40b400020000914140c02d8000e14180c0344103800761840e00402c00c2541760f880c3c4428800401100d80c6400080110b00c00354084003000e80604005442c00e4160b24900b01202c0004000204815020070b007541d45040910030344014190030b08040c0c06007821500000d0384c0c0d000042503107100c0c09905d00041e00d10783c030030310503200180000d11050055588030301e0722400d2400ca000017280021420640c2d00d8071903100780140f240c03a0707400264680c442c0e0700315201c07403000d0a8020000981032008000303910500c5010000c42c03c05400544881c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 30595545 1250 30594295 30594329
    0x18010903020c090601051801050c030906030103061409070303021018080a02060106120e060103020409030309240f050114040905031329040303080f07031806020c0c011803061503080301 81
    0x110b80010300354034104001408400d01f005007400940788400c4090034142c0d1140700c000c0600385035108942e146a0444004030000041094039040307008412108ca4505010f035582c450840e55a400c0c521014005910031400754207503074800d40c00301c070b6540c0d4480844407070b80e0810384401140340d0003ca40d110040e841000108080c80c0d00121a0b83c000e0040d0030180005403008102c039503030390810300003c0e1049668424050405000360f115055080e40800700603030907100c03280340701ea061080e6200c2440c03142c14070f81800000c44c02881124169a8aa80c41d40c00c4160b041302030000500402c5012501c1d440100300420034921000003440c014a485c1d480c1c02100d010304641c5a103040460501340598030028401400001e4004103000d9200c40b003074009040603550030a0890143c4942c000074041030352040c5e100c80038080f550b002005c00702c00c904101c40c80246a00f0046070040021410104d282250b0641030000a507036411454004400740e84440312662681c5030100941d0080e40721102400014140c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 30596795 1250 30595545 30595549
    0x308041409070306060504061b1a010306050604021603050d090503030c04090605090103050a0308190515030c030715030e0c0405010902090a0e04080306060a0210090804050a080a0c0b0318010903020c 87
    0x4110b50184481c6010300c02107140003c0501180140d001e00418000030030112150b241801d0f102c090480d40120a84044002c4803441c00c602c0b00080c08141d0351242400e000540a09003030085035051145100d40090b590044e032000ca40caa0810181c00721500e07100c2c2c540b000032a400f00302450050764040104c903680d501d4006103d04480d40742d4041030160aa00004002082000c03c0300b010607505801d0003403003581c402c240d091150f8541008032034054a01001c1c0991100c81c0c03075130300500d188207500b1282c0091706281010754480161243d500c2c01107016000c0103143d0700c40d400508a85041c0740490707005505400c0041c0030303100240c000807441940070070996040e16000c0c0a80e8020000307425001d610b07040030f4540800601c001490300b03019000002d002280544200f1689a000c103824a0401c0601864030704a030059120b44540b034454407161002141c8a40c000c07640c4a400355100b410201c0c1c191400e02e203600c0540006101045543d40c110412102c00d070b0a0042e20304507403090b4082c00714642c513542 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 30598045 1250 30596795 30596809
    0x203010606030c1205010b0405060f0c010e0a03030b030307210e030601080313060f0806040213120b0a050a270302010b0a06030c0f031a010e04060902070f0507050d0209010608040c03080414 83
    0x13100b0070700f05080c5001048035481d44404c0760282e80c01076031920340e51102c003482180780b403149030b09103a81c0d5860004441c0503414081029190710b482a90140081d24640c0105581d90260800c0503128100c4180f004103144600c2031803c04140641c14211580800c50001070b040003426406241c45410014042a0381001a08070201070805414000f1070b44280c2c05001f08460341c01000e046c0180e50004805215507003a10818006080300d483c902c0092240b49000b8a00030400d13144501528281004150360902c28000c4d101422407540d908468602550700412002130711000a0301503560342c0384070802a80381d001c1588041c0c1065180810400301d0018000d00f00c0b08020700e030000705442e02c121440d42d50240c0c0700450740703c80c09281c070110364038110b4000b500a04256001800c45803000070800100000c980e0400300550140007070b601a981d498041c08503040e0120b4000398001886801400f080e0f000b001d550350001e000c0c19070118155140d036114044d95000d074002d6064511480055401c17450140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 30599295 1250 30598045 30598067
    0x4020c1506010f0f050705030403060f0c120501080a0803190203040b0403020d03090308061002250e0109050c04030206030403020709020d02030f060d0308010612090c0905060306070923010c0203010606030c 90
    0x880d0040420250070b43c0182001d02e03042464040100001d90381d0107205e4204151f40245800c44410400c500109039104010a080dc80f8079020519001d0380110080c030620a9078101d80b070000207070014143d944c1c1d4030003280e0701c002e0641551880740300e90400e00e8002c9101551099105640c406098106424041d1a220fa259101c000309814400c0c1100026841400701390005c50a4804001412107610305909200102d280c4944682c0d40c64140e0507100d581c01c0854040740d03001e0080e10790b16602c40113040c00342c5104803039420f0031100804c020401402c2c90f500a41e40035010344191001142c0754802c00d005c3c1c3c0c0c0a00e411720840d51300842440403142c598038449820801c21520f0f814225140e641c050040700c2c0520420090106082c40b10010380400c2d00a02c42d060b0380040b82d050055115881e5100400c0107941650003440382e075000507005c40c024400c2d0300c1580c03101005141d000012104000d2080d0304032b0b20340f50411014000180040c1c03024000c0308050050394030003140400c0416001003103d182c40d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 30600545 1250 30599295 30599297
    0xc041706150103020c2506030f06050d1101180609050405130201080612070e0c0c0c06070c03110f21010b100c020918030a171510120b04020c150601 65
    0x6001031000300030380d41c0340d4510428028200503860300380c00003405041005c1404010803042075280901c110004044061003a9801d0f52030402211046a0301c920459569004050704201d0448036100402c016030310161459505140600e11151100100d2041c840503a01c4030012030010070041c4070398541400788507880b1009140c0045080d2a90f00001d01d0500041d10310340c065880d01d410301c02d45810a1080f2009404403160348841d03810702101c000890380c0840d50340101e1340103580748c80708a07150075400c6450300f0f80c021400502d2607041d40c68013a10000400c0101c1d60140030440d1000c055120020860311544c0a40ca1121008100c6140c07642034802c079140485c03003403401040011920b0f8008040c48030640d0161111806541c540e000c41e20000d082050f03908651001040301184d1030390224182020111480301030a4648178440300049840403040040e40c0030b22548183c40c2e070705128280d6211a03010240020905641c04002701e01264090004a80c2a401100300103041e40c03c02900b0315080070003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 30601795 1250 30600545 30600553
    0x305090d05030c0304020906040e01140a0f0c050f03072d030c02010b061c02040905090303041b030b0a0c0e060c0705010e0607020d02010c11030105100312030903050a0e030102070501050c0417 84
    0x30f00d042c400144002007001740309180c4100071071880e0b141ca0784402d4140704810000c0244013031800307000c40040310403a0030060070b42c107000382005103511a01655040101c03680741d190034000400c1c0c100080350802030501c41045504200c484c0324282200849856032130003140303000000340020004041e03943d007030580820340e8101400b2400c01d4580703404075005a8013010081c51810f031001c03682d1000e4440c1d42e00802d103079030070481401100b95000c0001d501a03485040b1400100d404014280d800c00c4040c407010700f0014a4500155000310075402c0340a00c000c0c28908403006002501c0000d1050b0406000d0140c241e00c0684140003550b0480d61414103824100c0314076003005501d41c005409817651500085c1002041800881000b010218080100900500030b000501d0424076000603a03d05102c1940c00003036100c82c050085e4000c1c40f600d1181505551b03013900d8421813080035112542503a25968043d90f08100f4200815021b03c916030146000398a003d40d03807032800ca0082c808602ca865100c0003504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 30603045 1250 30601795 30601801
    0x30f0606060307030b120d09080601090c0203251b1a030903040902070f0c090b04050106050c0a0605070207030f0602030601260f04210e0415050a031407150305090d0503 74
    0x1075a4810303250300108502e40414003241d12000325440052207010210b4034811a041846455080700003071043d07030303002d608480903607a0362039044055403049041ca2001d40c0041110220b901c5076545015104107288283d40081c4241da92440c005001848420400e242043d00502c204041e422201202d0869080098211304200030029200d220324841c50b108154001110310400c58643e0700900440c1c0c01c68406401c482d52550900003400344501e070184100e19140c00481d200cbe00a809a44042040c00d00503d89030106680b01e1000b01000b0300070b8025440382d044000001f135a40084002e240388581341c00360700e0b81070100001d80103140c100c2d1202c0b417072141701c011448a95450418980d0100344070034150f0203034070b6504060a070030300c90761130380c140c8039040d18400900300341c100d00c800781090070030f4504102d9038594110189001c0c11602030a640036003000c00c10000300c1e600040c0e204480c11100306980c000703642c507860095000414102131010035115810090380d20000c0c811f2407190507850078001c2c603500d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 30604295 1250 30603045 30603049
    0x1809240a141306080d0f181d0a020f07050102040305060c030c0a1d10080907050405060d03050d0e010920030a1a150301020a1d030319080901020c010c0509030f0606 72
    0x40200c07003119001c0c4600054001141d141900320301c000b0400013050b03c812240749400202603800c0c840400000ca40d100340642240800d500101040f1100398902098040c0c04e4841420303800c1c0042c0070511203070b4080c0611609907007094001c01c8103e10030303000160b0303640c9107280a0f030505c1c00c01001c140748690244100405c80750358104440281245240c0f031170001214005510b00e041e10406c0036600000051154120b207900442d800740a80400400c03211916500c0c030400084c1d0f00100c5116030006290b611042c0002d0051b0301422848030001004078040340410080d60171500c01902c10748050303840c0344980c4040714400500d10300301c0e43e05802030442c0440940310303102480d1081c103082208844d6640013a010850710000d014800380002d000759520220418020201c1c1c01500b044e0309100c40c003103480304a5240000c01c48115010111540d102d02c0400c0800f91413080000388160b0301e55400304940d504c041d80a02c5017500b00003442d181c19486207440000e140c90030003422a890b1140d80b03c03100b8007a00d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 30605545 1250 30604295 30604319
    0xe01050102150406060b03010f170109031b0201030f0e030702120613111f030b0a05030c030d050f070c0602070315050f04140f01020f09040b060307080601051809240a 73
    0x80803090350b4401545840c07522100038650390380701032034180c0c0100021031281c14804c42c0c03c08880d445420000c620510460741c80c2207074042c00c1c0c0200401c0e01c420003600780ca25043c1003042c007180141000681d90110080c110182c4150365843c40c416000081e40c4411483c00340c101484104410005007050300e00b40e0071401e8940c0d03140b003001d850005824130000d500c0d075032446007a00380c02c0a0031400d20010f0103410003401030544901e040384140c90110020603903041c006440d02020342d00500074204111001001d03605130b40400b1070324031449010048040820f0f1480020f40c000c00d00396008081461540c1040b00046509596403a00c071824130040c419456610f05100382c02c9604040501031400008900c035241c02260384004d1035a5002180c0b80b017517403845a01814040800769402c1c001103a8030010050144011141d001c04500f200010902d1544600080c184060f00d5144101c0000802e070001060240215952900300c400c075503104030075040d204031885a4140a407048100e0500b04020403c039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 30606795 1250 30605545 30605563
    0x607090f050409020d06020a0c2105180d02030a15050105040501080a060b030c0409030c1101050a02100504020607020604151206060909020f04090e070f0608070509210105070302070209010e01050102 87
    0x40b56856401040a41d0b036102c5103c14030b241c2c44101155100080813000d480301a94079010b49905d0b09400959034480c4000c0859490b48406540780ea1804200d2402804035170030045c042c9401810390007003000181c904001c041a9203001e014205101c0c41403000070400c1e140305800981c061400c0000401115000086060400354040c1021410159020200e850600e03400c42e119400303400d03d0001014160019040600307075010310f03025031901049034015646d0b445a10107040c01030340030000c07819000d205a480550482e100500851034080280c0000f40c107030304203030840b619900760a901c0c2c40d06d05400c4002400b8102032803c3c103000003841c10401405c485160b12800c10001d80003e0a0b030b6000300980c013114041c2c410081c0030071441c2080d0040c55614080790084400701c10141c4c00210f4041d0040e003030ba500c211250354400f85040490001e0002c110f4001003100c566006828003400700000078040da0740714404603540141c0702c0040c3c0c010880001c0c010380c00703234007240820340040c0000e1340d000c40c003001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 30608045 1250 30606795 30606799
    0xc0201090210030207051615020105010b03040308010509040503040b1201091d030d0b0a0803032509050a0b070501090c06080907060e0603010302040504050708070b180405060a05040515030102070501020a020607090f05 95
    0x82c540b401d80c10080d0401f0703a6a2900c98269181c136030302040c002030721100d01c0f2264100e035000704400e83e29088045118031040d02d020b004541a540100003524018002950141c4284107803400d195035000c1c1800c05030014114102c0b481c41c07020040c8015a01c6110b0301d0301d603425020324130b0700199a00d040c071900c9206941491000c80d4444d0304980c000d840c2d0342c5c0c07490000c005c4e040841e6034034941304e5000c408900350355081c503101d8030046101c840082c0c419100c90054900041880007032500d48281036036564480002200d080d501c8110110100d9113a07240c41c401003060340c849400711310749401c0c510305105290700202e041c046d11021076545900c9210580741507a034191000101a00e860900710b16080541c0e00c400030702d02c1240c2e00410801d00020142401400c001c00e01900c4c1c000103001c00054480403a01c0301d8203c4000f207810091032515030803040e0403400080409040c0c4a010300801e0136139200440540d5240c4d00061014501941080b405620421070b28042c042d5904200c42c1d080012020b1007800c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 30609295 1250 30608045 30608047
    0x60f1003050601050c151b040b0901120e010509010606080c04030804050f040603020d050a0c0b0708070b041e050319020f0d1206150c0b0c090f01180512100c02010902100302 76
    0xa005900030310031100c0100c0e85c0300480c0c3c003065880401861300705040310007100345a1003108400d884650001558140c0d240125080d090801640c0116a81611080348012850b128100a48400404e1050300d000390003001c004a810340c20260050294600a003510a5405040100f000030070103100903507041e51300441b24040031024450002d00588410303080a0346c003801c0c84c241c940401c41c5c0022601c0e0070521401140c4005961a08642401e000c2c4000162600f0400c00015000440281040d44c2c010310458900707260346010164040e8818200c00d04135600d5100062801003000d54402d603001016003440103241500c1d07040107058039804241b02c01024031007030014a0301c40480a070000c4024200f1400d2400005c1007c51008118901906c2d0580781d1108038400f00307900c42c001000b290080c000150446600034951401168110703071a0015281020902401040c02d40d80c43d0421501140c0c502c00030004826003078000f8040390001000c00043da85059100c80050729003100341d1206c861103007001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 30610545 1250 30609295 30609301
    0x60c12040503040503161a0406081611030307030c02010b0a05150a020a05030d09150c020606010e06090901030f0201020d02010b0a12080d060f0f09110301090507090e0c12060f100305 80
    0x190b145001e5500070036854021031288124515004119004544058000f140c8452080c83c81d04254840d074040c0c400052500700000358070546a400076949090240b42103145080c061146504540083e601c000009450b580d0044010758240103804980034100c070a400b245280c0707800110001c4039854140c00c820808a10503400d07a0007800075020154212003540d03951410300d001100140919031b0b040750307032855840204008010750b01c600e040b80381080d00144942d4803524019120942020501540000200603c06150703c0b030182c55402184111840c94801d140c1c0d10000e414000480e2408085a141c4031a416080c0c0e80e010764502203454120049102400318140309106110740183d04101070700b0201c00050080c0c0360014a0200c1c4c0301c0742000b0311002c1c0c8074101034054038909640c01450800030310042c0b100d007100758800d5070003507800c0c1410900d5a40d1402780b601c0500c01228503240c600c0d000b0031414054001090020740c401c40c112506980b24900f0790010b02103a900b010b00c07000301a691000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 30611795 1250 30610545 30610553
    0xb06060d0204030b010302090901020c0c0111010f0204120b28050712050f040b100f031104060509040f05070501050301080a0f05070512160501080402060d0c1418040c02060c1204 78
    0x44580d5039822030030542d5125102c1c2810b43c0c078603400317200480c0140d80d01c400017110321406100303456400c1c2e6000083d005564031500111500c6400e025040625542c0700488074503c0010b100520080c13091020500c0d03d00d505003030240c3d13180740091405003101c0314034404525800000004c0e03202401106000540c0703845650b800c0b9401c12240c3c1c2e80006075454282804113813620144c01c41d104a10806c043e012075030b180168a0308490091149580460445d0424030000f481d10b25049440030300a000024440d1740c9600182c40144144c0d401d4130040300601c650414030000b0301c019400341c5000e003000e910310b51401041640d60811110081c2502014640c4181003000030700c2594014400140000e03d000000c45182c2c0e114043c032000b48c03a800068113000511035009180651056400401d183e0812160507014030103031441c04c081c00d081100b0f4190640720b90102101500201c01c076007402c0052101c031031040c0000c0f185501100400d540c00f91041000f882d00709401c071000f0001f034014023142c07511a450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 30613045 1250 30611795 30611797
    0x10b0f0403150b130b0f0603060402070b180705040b0609010e0f030f030d14060a0b0304030207080601030f15060308030a0209010c05030a030507180b0a05030c16030806010f1b0b0606 80
    0x4000d14a05148070841c82c15401ea40110000100407200c042d80340d80100c030341a045820008503550004200300c03078042c1a03e8a20061940410054000740c80c001c416941e01c41106401c50300700303014650740030081030300400401494015000a81e010000145017134000b410070f000e000340090400c20f69540451150b1141c02c6640c0c060f80c0d0160440c0d48100440d070040341c803500195101000310780303422241e94840300305200d02030040d036000c0d00e8680d5503170034060300207290307840203000b6001d500c2421800030b980700c001c1100500a42c01182071100c000ca80e0310f01148884a488040011507007007000500108140100310303134100e0038a8100583d034070740c590016654443e10300c00160460001007580242c50b6015000944200c00a541d42500c95143c440985001c2e0454060743c00da42100b841004100e9002e075005642015881010340d0802d94090090424881202011000034900b0001d01125580000f1681502001ca0420b082ea10703c107041440c0c8030300e024840c00350203035401c0710108400b030315030f60 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 30614295 1250 30613045 30613049
    0x30207091805070902180a1203050702010215040b04020103050f09060c090310021803060105180601080402010309080c0a03030c0306061707090509040501050115030e0303150f2d010e09010b0f04 85
    0x300070381d0f542d6a034440d07480e8001d4008041191a00030100c075100d50394a4220110b4064030300609007510003201549003158183c0014900702c0c1940b0824a1241c202450542c0c03652049224101001c0e179442c1920004064a5010741491500c0b610041400919000425010ba201d80000c011544501918000902c0d040c00003241c66489440000c644807403221307080024502500550464585998800c20302484488032042d00180031200f802094166200e400c2c0306402c0307401458045085000f0b501c50041541c040300c43e0000301e0340311400c01801c054241c02aa01051828142000400d24025018182954440300550503030485000205241d01413440c40000e0280a000300307510b403905240c01c43c02480b0a01604040540c1c1c101c401e250240b1a01074100001c100d2000366040d901c9060041909408860030141d00190410000b105502c0350308101101e070015000c0a02424280d14034142c40190362200241000000c0c04010700c19100e8038600c50444100c0e0040c560341e13032216012110180601c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 30615545 1250 30614295 30614303
    0x2070201171b12060411030705180402070605090604061b0909021e130303030b0a0605090913020402030702010f110301080703080c03040306091406070908120a020309100f12090302070918 82
    0x204031419000c0e04a8a0b43d0b20840d425602084608210805080c0a00080741c6070380002c0c50400180b00b007158007000f03200b0501806400541068481d0b512071050303a0003220995030641c0502c0411041c095140503101d4a091407a0526812038420032000305101c005021720500c80703400140141184220151441691f1070000105442d01c0e60342302820026032241c4010f80c006414a1019070b01e0b468040d541070120b4025481d03280c60168110305000748918018042074034003001402d8071016032200d0000354801c903c10f50000803082044a249001c5592030486038000d00000e10041c0804040016120305680d0800c4083d501c45040308401440c511640c1c2005020720305180d10407040005000d101000136089105959240e915101c0841c3c2c0445135204060044d80701d40009031030390705c1c00700080050f0f030748a105481c47d0030742030320114180400c005042c03000034104103150406168055815178241d00b4800c42880501d0702c1da28025502c034811700481c1082a074500e00c0c11128010803d01c10045584 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 30616795 1250 30615545 30615547
    0x3020d05030403022b14010e07030305190c0503030a02130f0803070b0105061e090d06110d0501060807020d08060a150806030d020304061e0509060304080301090f02070201171b 77
    0x16840d200d5169003062104a01406400380340c0310001d00420071111506000c86a804241255519802070741c4044104c002c0095507550529444842d0a200282c0614041d0300c0e5aa5200300402c182c3c183c04010701160801c021380503203800c000500210469070041c028035409a10f820300c41c041001c108001e40d01028407040344181c0001d100001101408209001e2081e201c45070b80d80740e080c0040c910651003156a9481511303146044281488080c01c030060000c0c00070a07148019070380310720032258441d44420440d85c000c200900c3d8820709003d800e01611180c40d2401d900c0c00c2401000c2d40c1d407101a06a0340c02d0207152800180c040c1c5030075590070002d2030303403a11b5091184180c01d80907088402c01c0c1c440c24024000c84821142c03da00010440e412a1015a1000726a0040404040a44034001707842c5080010400c08900255903141c003440c0224055004180e0300d5141c02c12250458074142d5100012a005020007070250f80c12040000720b0f46107610001181c1e5070f41e1149480c03c2c90820304101c1030054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 30618045 1250 30616795 30616819
    0x21b060910050f0402010c02010c0303180311120a05070b0a0b040221010605041a0c0307020607080406020106140f01030b0102010b030d0e031002030f01050d11130504020f040603030807050c070302 86
    0x100c00500724418904214003042562500420406220012280070340429000c04105005511680403c00c540d03000e80380025040b00307414000180041e45c00002d40c00a0f116206c0b07080892000c3c0181e8902e0104611580c1c03504035a8980030305140124007019210b0102007000544500042c0c20044044800400440d500d540403401203002a0201c10550003042c001c0f000441c1c0c86004da4101c1d03017607500b210000d1846002000000c101603004400503043c5000922007000181c860001409450380b00b84c121a44a904201000b0b007118203c0e8407400000105400345003082d125203520201c080001c1c40c0110b8108070500050380507054413001d95806100794814954403940c8400780350303200d21081701950306550110340050280d01060b204814200310520042204d881e2560b89418450b00c43d0890f03440034151100010300c000304851680226540b070318200800c524012010780e42911003101c04008007411500c0003010214001c041d1000e216000078000c0144204001c908002c55000705040c0c5090 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 30619295 1250 30618045 30618061
    0x601031e0b07200d050d0911030601080703050d0e061204060b0d150605010c080412020a08070e0a05090d0804060f0609150815040b0705090a030b070c1104020a0210021b06 75
    0x41d0f90241c00d03450701c54402c40e200911034004100310203003181c195521420b03e080030359450014903905e42c080b62811030403040314216031030501626000300b040001910342e007491824041c0c2410882212641004212039044d245a83c5a1090300d0701160b14081c2d0081c15a00d6140000061464140296100c03810124150411640d03c0c7c030006d092091002c24000141e48100640380d5030b0004100030400b03081404144184c001e07019060b000c0900040207602c01c03e0b0b848a0701400c1400030342000d00000014030400140b0a014003030181c0103921240203129502c888000200a0000034000070411a241c07a001d55075400b0a8101b140540803a0904105040c0b034264180ca07403400c3e51044070b805016004111031081850b2445501ca1034024421031001d40d943c2000b207a0340d82c018032455070701c024104400b00104010080d403503c1103c80782c40380007091f906030a0204c00040e02c402964452801002110400369001c181d820500c01d0340741000da100c0b01d10705c207858000c040c40503101d142d80c401c501c1000600 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 30620545 1250 30619295 30619307
    0x40303091a0420030a170c0a0f08030709050609100e0102030408070f05030c0d08030a050405010914060f180312040606031b2d0e070306050301061202120c01020601031e0b07 76
    0x6842c403d1011145038080281a2580b02451000d0075000c0000006e03452254403d008040244c3c080c819200d018440c0d0f550707508107001d070351015914488084104030819400c500e1603070240c14100da02d10706000170a00050540b041c0c504404081101382005034082e40d00030801e0301d024099400a46060f2078960000c02608181c500c03c0324440e108400e02107040d400e11f0080e080345160880c1510380f031941c9280c8a8005040c02900072126507607034404c030070089002c10340f120400381820720250000782408a4a14042a07025011804100303500c00e2044044400000300d503a00548205400188ea4a43c140039006006591000c3c112803001c00b140d094a0450b40842029928030000c015401581c1c0e10000018101a0b030890000401c0000300744100e2001c0f500003035000501e0728022440c031751240c01013801e4640700c0e84030009004104003900110302d4100d1042070409181c038010b240301c01c04030380001c1d5215010700c400342000c0c105060700d0907111301d01e100d042150b41d00b02110f8946800c001c0801005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 30621795 1250 30620545 30620573
    0x15080d021501140105070f0804031505010e09060708060d0203031c06080d05070201021203041401060603050703180f0b06010c0606060503010501120902090612160306090c080604050303040303091a04 87
    0x80840041c008220001d440040c001d10840c180d43e13080c2808802c0d82c0b02003181c0503000c0143e0f2900b41c18000000010f141e00c1000410f01c2c9040e5010403d5450205401d110700070203000d007001600400c1c200715041d548200c03050344c00304c3d0844103020a510140080b0313046200741c4000710003c0c40c80c100c1d0800c550f1500e0700108103e400c98400c95001e03480c56402202c4a0044c0380b002401a008006004120380482c0c002d0b64000c0d01030000d064410311114126400c45000c1d5100d00040b0703441e2030130000996014440c2030712821525111090f00c030419907a007034455150001c01071405618101140880c0d2003100c400c4001076010f441080002e0b114107020300705420034030941d40018101400c1c0c55111401d809402c41155002d4050402a121f820400007070b58a45074581c05d1500c00c11055000001a07140e0f060300841c024500050001034900700900c0865240e0401c2100794840014480000c0001040300d5009415103000640411145041c460425061403000301250141060005010208a00b642 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 30623045 1250 30621795 30621823
    0xd060207050f070618150905040903021011040e0606070303110a020c030706050a0206130602090301140f060402030402030a031103090907051216091403190308041401050f0402010315080d02 83
    0x1460a030358600840d1424030b503824881c92080017803800c0046004000806040951030700b00700380900c0d15440810100c50300650140d006038801c1c0e21807205010140300e031945140705090418901400d1900341c03c4807800203049207009040008140c2d0502d0700c42e90101ca4100240500036a80381d1000703400a59075034800e40c505119019000d000940ca6000d1021521940069005001d8955940c14540213401801d0425144035408000d0aa001d903401c1c801c0448000a02c41000300c01d0401e02c0c042806420005c0c1401e00440c0b041040c040545d400041040b940c03907040c58041c0300b4810001d14103056004004086410101241c02d01a61681040180040c046440c610f50340b42da464080462403249000c0f9070f440826855070b800c3c0945441d03160300d04c240c2000541207034450a9902c0c50300c180c40301d5100f07094000a8100050004010360140302e10000c131301071002405641040ba000300040c41d0040d0000381499901d410b009021803040c0d141500904108048c0c890030141c0b50000382d15113512061800f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 30624295 1250 30623045 30623053
    0x8090321181b040b0307030203060702010c020105060301060305030304020d0620040503162318070503010302030706020a03050405040b030a0203060a0516090b07121403070512090307031d0d060207050f 88
    0x1895800001c2c562042c8520440e42d0101006020600c40144900d02c06039426018100c00070001d6281080081d01405079a800003800d41b520f00c00003400c43e04050036041c031990500c0000c001040e0300009494120f07030100d07940c40e0700400c1803910f600203090031140002000138208070104c152403194040e10480e802941070309c620000716070b80c640ca8075145000b6a02c449500846182c080603102aa0300c0b0322620250a00305880784404090359140d808840311000030340f002005208500f0240f00b0726000780203e00040012050756030b40a0814091401203601032913031580e51151a030340c104869601a50081c00340c81c40c9042c64008003014041c21200c40b42c2d290081200c040e8a18840c10020342158003004420703042042c0c03036854803140211010703d00700300000a1200c43c1d10072441c0d8001d500841160300d5055031045c030f410600484080081c1404034070b8100740f20b03a0000c680c01407100802e045803c52002c841044590004140034140400901858400300300700081000c00110300007241d039020111 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 30625545 1250 30624295 30624331
    0x305071e030203070f0318060b01271401050f0a03020304020a150201050a0509150f060402091906120e030d11130b090301050603030405030d0809150405030304060f0204060e0108090321 81
    0x1a82a90247c0d1250700380720011424400124040b07a0040c8055a4145401c45050710044440c0d60004040b000030101400c864404000c3e5540b110703881880440282840d60030300c0120140001d240c000d054201c01415000030003d0b08544d906280e1801820012410022940000c41c00034020441280d856030b00702e141001003000c4130000a8121004100c9800314249541c504003d007203000c00181c40c2c00c4c0c0140e001d006030700055642c0000501041c0000842c181c0c264500200140011559040c10150b0352505014004444020046410501052902040003920952044c000c0c1c0300700021000ca20308900c1d80402c03004500f000821409504400900041d1076080c20152a4803680c400e135030381584031524041e00d8501920001d0792000c6e401044e60307000a442611088083c07011a001c035403907000041048100441d81c0b0992031601520002142400d00b0800c1c0540500075240030701e4140201a40095502d01e810811202181448485e600c1107990309034401b0a844029038a0701d07040c042270150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 30626795 1250 30625545 30625547
    0x30307020105070504050d020f0a0306020c0318060403021c03110d021f050f1f090603081b0a0503030c0c190516090c0c0f030302090909061608090703030305071e030203070f 76
    0x103480980b9001802003646040c0d513230801c107030005c010b280f0075004041e05e1000004240144040d12407000044090340e920401a5802c624428401c51403610802c1c0a120a2025854a00140c0d06c14808003020a07401809410243d4143c220b0342e01d0840b8920481c00c00c01496580414041c080300d21030305c030301c144106003101300074281d85080320713807201c5264090b0000f10b5440360082c04001c1d9086440b10b9091003500d07101d082c000d031603072600300752980c410010352071106050719404022080900c5000d451001402d5456546a20020701240058000480e4a550181041c00032408110040c4500101042540b52060b03c801f1242180d07420b41c1010100000c08144034007852030a8403c40c0c1d078401a40d14203a4680e410407540c1f00040d03013010750031711411585449803140240110760000003090701d031404840c2001c0c2940c06090381d10030403a044050014202001442c40305032545800d010504d5031320715078110703203800c03180440c025265124206a0041c2350907a006502810150303403400c4916103400340c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 30628045 1250 30626795 30626797
    0xd0e0406031109040c090212040b0a05070801030308190e071518031709060d061406070f060c020a0b0412180605070213060b0c06060a05011106180a0204020307020303070201050705 79
    0x710141c22400ca0389a000307500c0c50400d240d90384c0136121725018074003152601141e1003243c02c1103c01c541031009440c180800c1c01070030005194170240c085400e00c100d28201030020150b14062100505005808010a403000102111404c170709070485020016203da0f4412a90b8414031032044113001c080c490703814480c4920a22041c5180804100c868403070902c0e6584030701ca184420010386031204004d000034581991060001c00511420081c041202070810740c2c0201e01c011600903442c81880200003c500240b90001d0f284820764101000040d420700c0b103041607052401e459002400c42d03103407104100c1000003a42c601d0703841903030301d0740c03007d465100c03c0342810300600040c0035a8010520500503130b80103182200001c8500b0000080c04074000340c0c6d600c000186500074185070000c1c1d4000408010355420b1011100000302400d29003c407045c102140724988440d40900511400d403514151002081c40800010024903800b8008566a1800040c02926a002a1f0702800103500380008100424403900c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 30629295 1250 30628045 30628049
    0x9092d06051e0a180b040f021c091103030307020d081501051204050115172119020109050d09030218060102100e0c030d03060815010806010b0f07020405090d0e0406 72
    0x1401000b42400d290342d055038040340c00c1d41002d501484808000c540f007040d00e1010410701c68407581c007040c509a04400c00c010303208110440c61105105005201078803000720200c094100e518000010241e003181804010852210b03e00c5070544000024410f0700c65000070000c0039000c0d160b441c0c17202d9841d51a02c020312181c0b50950765000075801e01c95182c1c40c42d214249560058030400000455010400345926211002c0d030051b00b6403041c0845640d03018000380300352100450800e0b030b41e510165072003201207160301513304403800c407281e401411820035000b540551001074000301191b6040c40c1952000b0304280880c04100e0143d026100c0d100c100500781041c42d80500c50513009042e000c0100140f50b00108001114648240302e041007100031520144a0500c000b0700e40d0313401140444c10f0202c00391070000d2007a106042c60017104010800d0807404601d041c19102d528501607941c1400e5421144d0324041c40d10040d61117490903080c000094070004010310010125200d02c45220210310400c0101c031018 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 30630545 1250 30629295 30629299
    0x105040504020a0c02030109030503100e1b0a0908101b030c12051f03050106081908162a03020306060303070b0f070504030c03080a03050a020708180109092d0605 71
    0x91009000034a042d80190008030320b1440c10744444140358001909484000760294045480001846564140d604081c0c1c054151115040785600f88001c00840506807003103c0207078140e000c14904012403180807504018094030045618441d442a48540200304011030181c0250346ca105500105010340590140d4880c01c1d12881190810300d400500038140040c17410010121803036401c0032100010896001460003180006851800c0c01ca50a02c0e046c030040c2c40c1c40803694680031440000d10f0060440342a100f031410485510a054034059800181d01018102c0c601c90401803401c4509840400c0802c0344d0080b012219507417902c400f8151a8880c1e0100503180c8440d01c3e00003802095501078154109a062402c07074609603030b0362a040e9036105c46030401c40d4034038800a014980c40350b01d40203035a000a00e50078218a08880c03a0703101c03486031140700e110305e1501312048880006a801080e0341c0f030040c01c0c008800d2201c030f06910709607404000c8144015a50790130845c19100006d01d42d1181070262080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 30631795 1250 30630545 30630547
    0x20124060c0314090303070602030402090109050103170a0302090a030302010911090112020409080403020d0305040e07080c0d0b04090602130302040f14010611010906020d0506031005040b0711100e03030103020a140105 95
    0x980b01102d0a00381000c00140030a410048009107071010802000002d000300c100680b41d050510402c041c105061380400300107401c00006001040302c02000c25080d8503c5040566076001c0c1800580190141600456011844940010503d6019041181150f01c580e02500c0140e520400b005400070080c000d000101909a8a003001400d01e035002c0c240742030048080500381580c03540000d891100c000012000540b01040810028008181039038100c0380508102c0d43c0361600c99079070395490080c4611a92026180c20100703d1a48a60b03100091151700654155540c40ca09030800421511902c8105d000d146400054a1140060303c58051090050380843d10356918044040300e41d24420788080295550792030100c0009140c0c1c1c40201028054182c000c10585480002c05040001446142c01c0103400c081c204030020700040840d95100001c0d00b0180740c001c0140c1c2e1000d12300078080e0110240c1516150b020f285d03c1000001440c100c80c4222446580140c4030000d002c03100e880201000e000c560 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 30633045 1250 30631795 30631817
    0x15140c030c070302011e020415080f04020f0d02031c020c010203070c05010804081309060303030509060702070303140702090a0b031e0606040504140d0c0212010b030a0b040203160602012406 83
    0x2854400401d80c2c24080c1c4004250510041c1ca200c07900d4000740c0141000b281d00040c10030400001074400040c001590924a0b028546003004468440c4c0081c002840f07020f0744500d51980360344130089039840790380190403520020b642c04c07409650039065540340e00152042e51203c214940c030000403122040d5026503041c0080d480c000c01503404600c040d00403103040c0410311a000080f1088507503039000382044400480c1951031400d01804079400036000c0341442c0c02c8401040382c00c40e000038140c01100c0d8507181c00036003040c6115214599001e82c003030080d80117000c0350a100d4801119080b400b0304800443c199101c106a00b0851030400a540c003080c40e45800650000d0140d15103513000641c0107008081040500d1001130300e00c2c0c1440b030008001008100c003074003940c0035803c00a010305012030302c1c0d0000b0400c060311240080d035204003464000305240c00d50b01c0000d00315242407109803505a00c1d200c652128503111400603010702217142403041d0072503201012226403d6460480340c01c032002a100d03034600e12 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 30634295 1250 30633045 30633061
    0x1c0905100e06030702030c1006030b0a0c270b07050105180319110106090609051005010503060a090b210f0d05120106030f060b13031106071101050a1b15140c03 70
    0x500004c108a05601007800902c44800040c0300c03060440e01942c0d4000361003419440c0c99007840c40301804007003030649055181c10900b50410604e80c0d600c82d03140707007606454105540c48048480f007600042d4140c100410010f0800c0415000340d80220610b08000700c03018080c0940c0d954a002d0f4541e0030302c030351110204800d207490084059002015800c00082075858803150002d0994a56500100360180d581c4d04015071b1580303540726400540801d103030191a5080c040001068584640211203080f952411420400d9481000c2d43d10001100c0c40342101c034036092181d1a4507210f1a001841311402213010f03c1e00b0040c8100300700c1390900c0341e0480c40c400c02c2e42090412801000100c001a111a03540e15000c0f50f000c0c024000740c48090b1614145404c43d034214640700d07403601680002c5c980200b109200f0000024240038003030100305e03404e01e03140780c680d1207a00701142d5051100245204102c04610007506100b00075602182a0f018200184080351910210b440e80d48812140d4422003c82440030030844 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 30635545 1250 30634295 30634297
    0x9020a170a0b0303070309140906010f030b130e0102071a0705070b040f1a01060e01090e070e0a030b09010204091b021203090102070b010e100501050c1203060d051c0905100e06 77
    0x10680d548400100c80c02c402c00420b1540e4845502680410a03042081043c19010320245802000640d0442500d0a10320006001c10707542034a0b0800303244e00d0707214407142ca894204010f41e250004000500c01c142d1f0b403d005074006d6005160a07944402c55a000d81030540d03c01120600880707440d0b8501d40b0307207a0203449045108401910440340101d44481803001301e003810340d07085200112240c3d03000700c551500c1c0c009000c403025546000c3c14468110350800555108036034080c2e01080c03504003010b03a10000800214a405203400081c200d411200070f01c50650015400740c4151264101c0401085908103503407008545000300301401680081341809202c00c4200140d80c20900c0f503c0050308148090f51003d400d08401d806c1406c035020000c0c1000480c0b014191520010b010070708003039140900443d48240c803443d0701240e50840c4e060020100f803040d1980307071600740340c1c94101098800c0360001c8420040e520203601404e20025001c000046600d10308502c00c0f195000150700d4045664451030240116 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 30636795 1250 30635545 30635551
    0xa030c020d150509070608130807060b031608160501030902062a0f0105040c06110d0503060a05040e010b12011803030509030403020d050a1406070507020d0c08010617060109020a17 79
    0x5024480d1040240d500c0141c0140c3e405486010098813400703050032001411014000d25400044036004204004202c401342183c209580081010858403003c10100b481c1890003024214103180c0220f0008550001145c4105e4044940307000c40e441940d42c00045080e1f0b450070502951000c001c0120094014441d5040e0400b414250b881c860521810a01303542440300e005094007440e5127600c00c00003000380800201d80500b6150910107185030522650750b40d24040030ac18113050280000224400d03035610402480108001403081c040e802003804021b000c1c0119289581c01030302d190700c1e09004404103000310007001000c0c940c80c510f849034548003140a080050103151881c0410000480941c0f03505202a01c0c42c1c0c0500000e10840742d80d49041200544002c1409080380c0080080c091801d501804076058290101c440d024a2960360034912010011540b140304550710f4401c0005071701403100381801c040c0302e82209890860f82ea40c0490b006910403a0b004800244c55a00701c000c52016020311103030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 30638045 1250 30636795 30636803
    0xf050a020a06060f1404090302210d020a05040503010c140901031a0607050102120903030402030703020f04140a0e0d020a05030301090216050a1b06170117010f0203040c060206090a030c020d 83
    0x220300c40e0700d486080c1110724130b8100c52001d104195040c40301ca0325000401c1000d5a0076203003002071142c9510025115245801c00ba00c454400350941d017014032404003655020007072074000b10b40d9410001c0018003036a0040c81190300a5003821244412a40034501d101840c6414060b0f0f10726000d0b89a004400401c088010309030a4450082004415240c04d8090942c4031722480c00107075108150458041c010400411403005039204004100068a022610100f1603505407914400c071000c060021303010703000b4040c4464810510b002080304900603030308540307070540c3c00d80c0a4600c040b00381c1904903100c2c05100700140131684200010405039003940d009020281354072100c0e601406066540768201000c2e1601030303601c0440d0314001c102000c00c0c044441c2c010025400c107410008040c41e5100d020380c6051084000303c040e441c1c071141e6590020341281520300000c490440d982d141520304054200c5c201e010b288010320031040003444903080041d0068000d5058ac07940c0d03900a980c2d9080102fa042c2d0724508032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 30639295 1250 30638045 30638053
    0x3060f09071d040303050c030103050703020907050c0d020d090602030408060c03250503040b01050409020904021003200d050106080108030712050d1409010f020306010c0209090a0f0305040f150f050a02 88
    0x190315102c82d0642c1c0d02c40c1920000038a82802c06080040c2070703c5e0003415082003180c040004000159001414408881d415150750f00241d590590590307040c001c3d40c000852600908840b803008a5021824124402c02a111b110526844500032079a034060741c081e12070f050307002001044400740d5283c046c6d540704490b1b590a51901c5040781d24100900005c040c4040800c2d404803e00c41040401105607000d41400c0d2020010f4580030740000e01948000750010b405580c3c0b40005015407807090700b1164441c3c0744000ba601e60b4100745400d15250f68400c2c182821910700d44000450220b100300611412541c0641c000d6041c0b03e4643c03520120910100e40d500c06110f801c000240e0351304460301034110820401404551f5a244c0780e0062825200010951050030b4810020000c50b6a004440000450380650305010143e0341c1e500300c0e9181010300303480074205041d80300720740040642c0103001b0010b881c4120101440c907a035812401c1410289102d110001c03503005206000594890405041d0407040d41c4111 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 30640545 1250 30639295 30639299
    0xc050a0e04110f07051006081209010f0908071409060906150a03140c2221080915030907060207080307030c1104050907080c03060c0f0306010507050609060708130203060f0907 77
    0x7003480351300c240341c200d070503411a5203082c000504511880e0010140c04003c2d00e245078a10308403144a10842101e1814410300030101c1c0c650701d110302010009040301c5d204490300d45460780056200f0407001e0720054807841e00e01000800e076040c81d000f1980a6513000c0c0c0030601101c140c20528807160400d02e4503004241d901c10030a00044050100345010760022070500d50b1300c105101c40740303068500300411800d245198075070400c003c2e84103500020094100d907201074245501494000c0082c441c69003055404100c0d071b41a5214008050001c5006469001c21603000341c1d0f842e1011781c1c072902c080c451401c480d0414848140864000c105180180744038404c2180300081f0000090b044503800d0311070b100c4c00d6100361800e01c02c000041020458540c030487c000c01d81b520b48484c00c541d01c6d109480d1008408030004c40480d020341d0144c3c065512055118050320304601e8489084c85d502c410442e0f0440c000344d1104041a140070404c00c804446a801902601460b170b10040d200c400c821002c0e000c04880d00c03c070100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 30641795 1250 30640545 30640567
    0x20403080d0e12040f05090109090c05090601051b160e0106050304020103020f0d0e0a050d1107120501060f06050d05070f05070209060109050303040801090b0109060807031502070204060801020a030c050a0e0411 92
    0x104085d10b10001e500301e072203040c00140302c0d8a0b04160040d40d40d00d440c0c00250700100301c09080320760071190204c07542406655404012503aa024000b52049003118120500941c0c483c0030030601243c1c4069090b02d80395680d0386281d1003806c4000c1c4078600100300e08001080155110741c00500f50b10052a01180c42c01210028035000c88080e04461a980d401c000c1150f81040824041c190701018640340c00b0514890521605031103490030310580180507400202c4504016083d00104002c1942100350b8480640d6002c1c068020f51000c4166241c0ca460301000a032854051040ca0a006c00981c1d80c850801e5056424401b801c0e00107052281070192050300011141d504100900144c212070300041072032101480c010078070f2841030f001000700030300b000002d2100c1000000c089c4122a004481c100106c0b02700c20003030000784100d00e03001e0341040c200308000c105602c054005007140201a5010040200003000031a51801508104e00005004884100346490550483c1c01e00f504041c0c0d8003807070702040c202 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 30643045 1250 30641795 30641797
    0xf040b0a082e1e0b0a0809010f0c0c02010309050708010501080a03020705120606060307030b0406031202061e0a0207080408010c0c0203060106050301030302060417090409050c0310020403080d0e12 86
    0x310060001d8404410000b10320000c00c0ba500092035069440c40e611203159000c02c4100405001d0440c03054403041c11201c42c2120100d4600c02040403408456851501d2a40100001c0085400250544c24112056410360f418410a50071201c26070717031607410580c03e074011005069611000d482c10310842c000402c1c03410b07007071007841c1c000c200040c0140f40e015190701d03020381841d0306039100b14400e80600f00e50f240080000b140850740914104e4a0582e43d07074a01109900070560b003a1260b401c24036088000c41040060100c150003100150201c55a41e0b44500f9100512043d40c0017009034648548007182440ba030b9074010340340f01d502c5000041d0609031540c060600311805940c5000016411070814000d609040c850342e4094252803400c1c0b8607541c11902c01030341c1e9180280004061595103064076100095241c01d40e0340690b0010b105100c04d0006040071969180941d940610901405149100360b03000c0c0e2003100c1c21260701c140703070b541012401e805107401020300c0700c0c815000780200d8031111880d00c1450 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 30644295 1250 30643045 30643057
    0x313060e0f070f0b030906010b0a05040f08030304021f0f0e010909050a14010609030506060f01110d030f0b0102010b030703110a030b040f0519021c0203030d0204090e1c050d020f040b 80
    0x2100915096103007046082150f00306500280808004105220003840d0105440381510505c401460f80c03031520410071546845150702600010345d08000120344c104002c00190b0140d8001c4480002c01c91500c00030b40700f243c84003000040410001c070405200c160258042d45c0507850141800080e0315940d202e52002e58504440380c41e40c0580d11309100c60042004000c0d140036149501d00f01c0c0d12682544e8404e9039902c8040e110354441c140d982460301c0b4a03807207145100411214842560811510510050058124076144110113400c1c1401c84016500c144036032a1f804600400410311107185031500d101d10a51b1a480f02d0304800e000c0c00210200b4100100355000d5403080540807030200840c100300d03003800b40ea000010314010121011101581d1544200c0391391a2424450030381c0110300c1d10003c0c1c558070401096110081c000700c3c0000e120b050b150302c100e140c540b00a050f6003140302c6281d40d070301c10005945c8030f40b40070401c24010289040b0fa654050403c900d1420340303440c503142c0c0300c07a02c81002d50481 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 30645545 1250 30644295 30644323
    0xc02070302191505030a02040302041d011a03070b030c0d050106180503010501030804180b090703090209010b041a03221101020d03050603030412050a0b01090507090806010b0313060e 80
    0x154404004505003810b05648106511030480c050070b0810f0395041c424110603080c00200714000c4046040507034103504580045034010b204202220341c2c00360311001c91504110301003a952801202420a03149a02d0345c1e0f010440050141408500b001c08060850b0406804104c08040c24020fa11083c0d18900c5010b0191440d92a00c060342840510b1440c0c5009443c1c100c1c900030390500d4010000142c40e00180e43c01d44040c50b12816118401c8074903800103100840001d548100d00d041400051030309684407205850080d1400503107a80c962160b036455119501c92503450800341d80c0480040380c8141c0186030400d0000d110001c141c1121250070106c1c1c43c4810301030f5000e032550001740c0550760b0100130300052900c41e8181848036107080000640c03030303000300d200b40c02e008140c3c1400c40040190034440c09419540c045103402595071144240d000501e030403a406008100c85013070101e1042c0c000101181211029480070b49995100c1c0800400010540e10031613540f0780b5500c4510a032502840f12105051030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 30646795 1250 30645545 30645553
    0xa0516170910170a0207080c06070e0a14090406020703180b040e13110603070509040f02040302010e060309060703091a1e06060f0304020f010519050304120503090c220c02 75
    0x148410001d0020704803820b07105100001d11040a10f0401d00c40030343d4819641200141c6481c56414201308510428207081e41d076000b50300030044a95008059100c0d4a6802d4468205180c0c0324aa10300340c0c0041220350b60340c480314440004002030016001002500d12038a000d03c01d010880c10b80c4102d1580303039041480141d1000c0b4003031160303070751203075074140e03c04091034400e0072801e1291604031101c07002c01e9a05001c0c00d800000520060b014100311440750710058400c0004517290b1070901d0083d0003e0208030300150040d1741000441c681035050f280111f5a590107003c181c1c554400c181c0c020304159800302c545001071840f034002c2c06008604c052054001c44840c8a00c1c680d80380d14141410402880544038100500038920907020b440c00380e9501641c1592450501780b40e100c01680c050103a049036070400074280504800071a4400c0142d80036902c5161009600c000001c0259907a01003120140309543c006a0040325524042000d05640111545918852031300411510199401c1c004550003580c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 30648045 1250 30646795 30646807
    0x90c030402180402180714070606050a09150b07290402090603030a0c060b0d02030f1005060406120303020a03090203030a0201060e09030a021c030f09030801050f03120a051617 77
    0x10040c0e15522650302c501e00945581c50941c1c001901034a03c2c3c981d00c00402e00072000a10300f00d0082003034003140e8103d4807601c0d460361510320b05034000d0305c00c9000740d07402400380c01b5000910142034020300803083c4c1b5119211801c2800c0122040403900446000c0d540c21124100020b1841c103542840b510542205c60018903618050050007205032014240f9030080d442000725201007039100030581c1100b41e102e100400c000d50030354002070782320103681d10180d41402401040e00c0b4400c00001d01c958200c4011000b070003103030b540c0010031049a05500c2403400300651284100006842680180380280540c1400510a803280d000b00e881c40c1c10855070200940c0d5a054288a8000445c081c2a801007002d001146000d400c440002e40312142540c4154003411144d20001d080d60094001074442d0650380d108101c000741c01c2c10000c000d22070038030815000b000200a81c500794200416600d00107084039034190b103003a003d000100c415a006803500406001440b0425001544990aa162076940643d040c0d8a0b00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 30649295 1250 30648045 30648049
    0x10503010b0d030212070c0312050a080c03040f0303020706020d051005010212070503070605060303040806040302031213020f09180a050307060b060c061303050408100509010606030e2a090c030402 86
    0x342868103690712451401c0b0304040060360000340c07074060a1020035002c0d11280e1504c0d10ba144194580c000600c00d011102451054580c040301502074074034185c0d6640400d1700c40c80300d00d030503600c01990081c1081464410303c2020034004d400502109106400c01840c10365516944421070304191488803900c400d101c0208130940e41080308105070900b181525140400d15a02d4a95038803d02c030008010036103c0000440c40d507424001c0d980204203800503a079a034036182c90300a40341d920610213a8168440e0b44045401c0020203204c0382c070195030207040041508040c4040142c090001400089840f44407940b40c0c54001003405400c0440344110001c1d62103d5103442c000c001c1d03a90381300500e40684403c0c0b03ca111039010000d40150070184180440c401c00301e150404903081d10071b83d000241d041c460900000982c920b91b074800c40c800d00410000300700780354441c581102610141050480c0e00da21500383d051515000074002c20b4000c12582035107260941c0280480c6003000c04551041d55080d002c000c1000754 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 30650545 1250 30649295 30649301
    0x309050108010b0405090609060a0b0a030e12040501080a15050a06080103060b01030203040c060e0105070b040308040302060901060f180212100905160c03081801060b07150203060901050607030315090501050301 92
    0x5450145080f600705400d001c08165010001007120344078515403404030f01141c468182040240901c140c0e00c40d40d6180c500406000303803030b09554401d000e11540c0e80c1801d005520a0641e020f0b135005941d44492501e6400e1120007504211150511241d1130f0580041c00e0340c4c5400c0d5090041140c0d45500c506907146051040458840401e5030b814180100100000222481d861070152081800c100c82e051855000485680c052a0f00041048480c00240000e05400c08a01e5118500c80e50840320582ea505500768242ca0040c401e8110f0084508000c0c84805200e03101d03d00c2d1a07128580050414442e140541361032101980c61804080781d841f01886105058040c041d4451031036040c8080c2240e0a00c0004d11180892501504005503040400d65003107000101840c0501d100d4001c3c0855501c408080c05151302010b0102c07020000241c140324900c00301d00070f8130300c900c0004103440c030b20703a181c5000d010300366000510490801d980c5150010900c480040c070780010b0801c2070400205581001b040c90700b1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 30651795 1250 30650545 30650549
    0x70506220801020a050a050304050109061e0c1419140301090e160302100815030105010807140d02090609060102100f020304060606051903020c010b03030c06040308070f09030b04080c0a030905010801 87
    0x3070759004120b5054030941000856807080e9040c034001780d0303d035a18200b15005110240c80104130390305040280100005480005100029507a010800000c501e8020750f900413a005140541800611100040c0d100d45441012100c0080c28222045800c3c40f4001c112684240c00001c0c81694824180d20020000c10840c00c5180b80130245c1100c2c030341144c001820b604107901e01c40c01080f103800e0000d205103008414800b03090501800034007803561030b1002142c5990941c0141035400320306410700d01c00ba140941c00000003d801800c001c00303546904c804c1c01081031008001c2d90652007400b0316021189028410003046d4030440c200103850307083c079151a0040c0c510b542d001100b007104c1881201010410340261580780310160400507a11003d035601c8501500065032031039418040455880f111100201b94148241d10030380d22038905a44204040d61600c0c10040389030300150f01c0040c1400090360008049070007a025500da2401c145680103000c0c5400404581100040d4100350108103558029003000c2c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 30653045 1250 30651795 30651809
    0x13080303040b0a020d0207060c0806011b08041a0702030a0501090201020607030606050a031e0c020703060e0708061902190f08010f0b0a12020405041118010f080a0506010207050622 79
    0x32031400c1c03603126210100780140c03030303410016400144444141c03590750403100866846482481190744402000d4082e0700308a0300030380031071111103000c184031941803202840180c2c840502400c1504103c012500940c00e44c1d00360591007030800c12503015950412110228505c0707140081052800c500c002820084003401400500d03041c80d5050103100d80000070380780c00c1c4c011890002417400b11404103240c46203240300b000445c0c074501a0f80500585d800f1400c2d0b01a83e0050f40300740301188800c2803880e43d500c001c6c85101c50941181c40810b0400a000300607480340000441e0150400000c004046e2a110395109071001058a000c0c000c1519608080b12a00600780070130800040d515110007080c8078801d11076040c00300a0441c1107030149041d50b40c1514094100903204100e000460741c00c22409620462040c018281d132007090168035032081c03407040c2140c010740d91001455101e03d1207040142c240600f000e4198000c1e48404101038640300003610000034003a07240002144102c40d44048d041031504440307 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 30654295 1250 30653045 30653047
    0x6090d030b0d060b030709110a09080703080301060804030504030203030310060201050a050708070c0303060b0406030b1206090c0d02040207050a2a0b0405060309150a020405010e030a0b060f03030702031002130803 93
    0x1401c41d03907a68a041c1e0416800900100341c0c0d0000400080c181199908a1919140b0f424000010155005c0103000c2184682d1520a0496110340006941e040c45100c0102940020001485010710035014241c010b8440d052185c10241c0360780c0005d0658204865170700d514050540100440c0f070b42400703526001560b0100030000c41c18149001451444003c0466062000c80060041010b209500050041c0000070069840d1070325808024040c1520400c0329100b803548000201d94020b0108030a8094402d0500421010032102d090000d002c3c40301d1001d9030700641c28005107011500034000944081d01c40e01c40d0000034061202d00709010041c1d0140b00080c40c140d400c0502106440780700300c5065034012940e03a526565640221460301d01c1d2000404102e40310361051103404551030300503000f42e03403098903004c0d450202c10301410764510308074034058403100066000c1183e90030100201e83c10090040c00785d80c0f910761241c001c00e00d840107040440d41000d82c0000e04840704007003030700428040c00441c000342d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 30655545 1250 30654295 30654311
    0x20d14060a0509090c040e0606150c1f0e0105041505160e0409060b0a0b0a120b030d0c050f16030c0b190e0414240a05010212090409060e06090d03 64
    0x2048a81e69103000c0c4a0203901030f030002c940c00a5080081e1040c0650040080c01100f40c1c4105507500c4000607640345018448586501c845240317100d0a540c0d5074080500101014003169040b0120090728400c0d41c2043c0f5076504405203146d03001c3c06102d20890003210740c07042c0554100c42c00001c0f01c400505012442c9006000c1c44040d5a1100c0c80d030410520440d00810000c1c0603052100051001c0340f070b801ea00c4010400e00080c03255550b800b420489040c0d0b00c41440c400711a0700c04005881210312080e070305801103019030b0f00003030040340e8a1010038044c10480b00d845107031180c803038602561404000d20400082c0401c000b0085140c01c0c0402414003004580e050140c2d0301500e070030440a800e007040038040d10f62045a5142c603584e01894400400c2c00e849102401c0c05091141d010f00e015100c41000c000b9903502c8405801c00c3c048070021180180d0051005030031008000007280c2007001d10551150311040d115010402c240650030034106000007030b041034103000310340f02e02c1c0007098a030f80c47c1494106180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 30656795 1250 30655545 30655549
    0x60a0b1303020402090f0402070c03050c0301020703091203030f0c030b040e070e04140f0601090507030b0405010312050c010209040c021c0309020f090601020102160503030601090e04200d06090303020d1406 90
    0xa250440b58140d80150301e54071544006400c05940e40c48140d086480070440b00d00388184240c4003411a40204182c440541146082c1030a030301c582c1300068046031203514100860104012603100541c041e10340084c2c7e50500e80d1201c000d582c40040c0020020341c403481c1319200c1d49003a20034602c0200d42e910052604a182c00142408400020b102600001021424806260b814482003c490b00d5101c00d031807039580c503004541c004140903222400001d2902c2c0c3d811401707060031300c1494180e9402c0a5074030340b15040801c00702c3d0160310010310b80c25195002e1003401041d03100c2d0b0280b201e6498041c1c0180221030150103811005030182d0342128100f500b400f99079409038a651040840e6803806950880503589e13080010b074060300c100742e81c0d00030100c08049618248040030020b940107001c02d0343e41901c2181e0318101c1b640711328000e0343e014140914032841c4112021944101050440d0f0140880000034480e8441c0c200310390f401503003900840d0300044c40c203c2c00c1c0c0092141181d000c89003411203d4038289080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 30658045 1250 30656795 30656827
    0x90506030907270c050304060b06072a0503010e060403230301030201140405090711010c050c060a02160b0108010c030b040e0c040504050c04060902070204050108030a120b0118030308060a0b 83
    0x1090601018102106121200502c2e51621407450101c1003031004c1c6480400007415079000311029503180b454121a003259141c03c8040340d080300e400c0849181c8182410403902e0010001040710640c54941d003074001040d440078060b03200c14800000c05800285071505010300360341a1101d034a0700a9400150b80c0c0041109581500d06490302032902e106220780a0f034020461b440380342c10496002440004112035590300084031181280c240e002401802188075042d40c09009036110b8010340e812000004041f00200c0c3d001c0c101002104903102c1d18002c05440340072800c4001e801a984503516072035200c900300e0305030084004100701a82c0c10045c200c10038015640341c1010500c1c04e446a5281c10105050150401c032030504000002d0081007581d68980360700000390b009040881c00340341442d000145901c4040b050320340f14421500c40c0e0000d8a8484002401409040300d6581849010360b07815200320048200700300558840e4489001508050042001901655010101c200d400308166406100541 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 30659295 1250 30658045 30658049
    0x6080f16060206011403100f09060c080903040b03040507030c060807030635010f020d0905060105061305190905070801030201020f0a080415030f020a0206061e0306130602070b0a0b01090506030907 86
    0x1224801c5c07031440643c00a0306200113404209050f034288014031b400c40300b20740c0c06181ca0758400d0004102c1c402c2040001c0d2803003a01100e139030b5500d4009000c00c00c5031801440082d9030041c0f051013520f40c259100d964414152140340c100b0000149010f04010341690140b05041c054452581c000c0034412108807107d1081078120300c01032051840c0d16038807201320000d400c410071090079600d0070f5449410808960004094074071050714284510030001845042075800c540c04100b0b07800117100c4031400e09003804500c015039200c020010312410380c00981c00305144900c0d405800c181d0341d80c4605525500009140036403c01c140c0e45103801c01c100500008010004403001c60f201c255124122140c14002500107094009a54890311b000103041c401c0694045181481840219034998200078292100c140403207942c1c032410b8240d404600402c0c001d03944200e0103110030b80f15690142c9000800e590f001c9e5016410799110f411300c0d07143c51000c010f660f040666040546015036850781545400c02843d42d569020b8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 30660545 1250 30659295 30659309
    0x70c2c010b07061a0a0e07030c0801050f01110313030308010512031206040c020a02060c010606030c02060106051215120106050111030a05070f0516060203030a0f060311010305061306080f1606020601 87
    0x1240300010031000612801130400d4010205c14076255200361600b002c0100300d540030002803900800300070450160310414141d6202400550028289200643d100e42c0c01c5140e07031503d84400e000100e41c01400308e014101441c1709540d03036100c80d4944000c1c80020b00400d020480b41e82c100b80416035004101c804800e40c030100403140031608101d10541642003003c41c5401075000040001c651686c1041508040200c41455504010351010810100e848047c280251070018030100400c030140104c8464145c1c12504d5841381c0c0d42d9031700030709000401c801e05481480602d40d440e840200b04540e04008402215072141e07001c2c600e4020101c90003400ca00c80c1140007800c40c200201020103103c82009041d00500d400c0020358070003a00d03440060360b6078108456a4a080707007410201d0200c8203c5004804c112584800a00d5140300e5443c01900680707401031100e81c000440403e0007140002c1030144c03500408040019000c4090700741c5840342030820032041c100d01d40207900403c00c4069800941ca5044900c0307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 30661795 1250 30660545 30660551
    0xc0509010b0703030f0f02040320040902010203030a09031206081501061b14010b03030705070305070605190302090103150605070302060a02160b0a0b0a06031418030d020906070c2c010b0706 83
    0x20017070400041c02d08460b9180400d10208001c41009444100c00c0b9004011507041005101100104420750b4080d020090040e0424000b26200880365081100140d22a00b01501ca400700250700c401115800e50022240b43d100244240180c4848110389016044a02c2d0144002c540360102011000182c440280a0840742e081d00c403822400794422849280001d007aa030ba110841d0400c40d588400301d001c00e8031140034041c00040c102d8098012038000245d100c0c00c0d1105c0d0b06c105003081e4000e411041215060545512104c944075100700811409025551202ca449000e40e040007803609400400c490039980c03040003071201c010401d020601c03030198070401c5070b111a600c400d1004042e0030f070641d28513003183c2205400701e40c0c10703019000b0002050484d60005003a507140c481a110030082c0420704446600304002d82041d011580d0001c1c030f004003010b0510f0b85042c0307043d82c2d408070180e56a8072441041503003d000c560f420307214000f80022400b0483c91302c00300d54182240c2c1542c034410340c0c0b001000740b03503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 30663045 1250 30661795 30661811
    0x605070e0306180a05010c0903051501060806040203041410050115050c100509070e090d2a020910050d06050601020c0a06120506010e04020304060e0c01020a0c1205030408030f070c0509010b070303 86
    0xd04004c0300d0306040c4c1c4a4001e00c2510003564002c0c00c03078085800120b130035000c0d059608a40071100c00140d4100d40955a4406407a00c4080900009610141094940060006c50190b07000410040406621160000040d243d854203130030b00100d4080129480c20040c0c10004003440e480d002400c111145e0070910001010340f901481d02e0725180ca107034468041c20400c001081414140420101545041c0313840710030300908003083d43c1b001c13500001c010071100d207013130903000026081101001b980000303800c507004e640d0b0b915140040e201020004c0d00300c55041e01c075800c101c9a540d0601a4030309103103051751901c0301039081c25005400ba4a10441d90789445660f200000c940b40e200d0304003504803050103032013155a070501c0e06001c00505012500d500c6584940c0202e840d00703500c0001c13040342d03c81d00094807142c5c2c5418000d50f480e0351088050f003560705210034440030039150814070042c1048410050b5491751088285401c0b001d88400b135020b54810340c040c42c0100440da40701c00c116002c041e414600020000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 30664295 1250 30663045 30663091
    0x80118060509160b0901020105060a0506120709081e010e0d0c06050601050d02070b07090f0f050d050a02060412050601050d12050c3f0708040b0706060302040c0503040605070e0306 79
    0x2d0350b01da00e05038100004400004e00c01a07440020041e0300d100380c0c02845aa0784c3e040a10040b401c1174403616401c0b0900b0001a01d040c0c0300542110b0b0070845c0c030b14024024541e20031b422031603c07034a0740300540304201416414800321824070950416980f8036020704103d950608019141c100301d040d020300002d0301c0e0300c0041c14580c0f0034000c903054100011030841d12020141043d510480048500402040f10305c00041404910b8032003450403140340070441e6404074100f41c1030195100e04c1c1e020480e458810080da00c001a52640d0240014140e0047c0c84d0380d001a860425515140e0180d006900038060180681c000c5201d500c200c118500440c14841d507514106c000d40f91500343c0c00d44e8240320b00070440010380e9000300400103045060100c1e00807840a6100c0b244d0700c1a86100b00c0500034500c000400041007510700b507074050140d0340d018a0b00020156039907008034056698482a080000710000200401c100191045035044001458040328480080020940d01c00b00604525204010710f4001e907484 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 30665545 1250 30664295 30664303
    0x62001091110031103070807020d021b010302090d0b0c031b070c060c0302031e0309010f0209060304020405040201051e09090703050603120310080f01020a0e030607050403061a1f0801080118060509 86
    0x841c48203144c036a40c0d1800b03440040207002c0542c2e04600602407040050502480040e4441540b544a51781b041e0a4490300c0040d402940031407840740d0000d080e90f1504000c24000c0c0d6409200d241e030103110540d01d1914000107000e80d441e4040040d51000148554000324240c4141141031707500d5400c02d4a200b0f0000c4c00c040c0d00c0d500036520315900c0a1381080907001500c05c042d000d540a1a031071030090181c14100030042c07082e0b01805911035040201800040d000d86410b4014a8000e030040c140145030204c071b9902802101650b22200b0317021301002402c1600c40c200200c01c1075006c0b955280070049030814000080d1200c0401001c000c0c05400427010a001c80005049900140200d904451800c5c44010980c4d000c0e40021103008041484035030915018280410320b148034000c541d903403900d014199aa020010547e407040341d4080d201e007440c4207086407900c00303072403001041c1c40c50401641114208018030f800c0e07050700802d0190341070490301c204030480191249920341c1d00010202d0165104100761b0f2074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 30666795 1250 30665545 30665561
    0x60402090d02040216021905010518010c0c06020303010e010e01030f061109061b1c080106030c05070c0306020915090a030b041406010b0a02010e0102040e0c070201030b0a06200109111003 82
    0x480f51000915088000c44e002d025800b0a1007079884222440e50500008251842da1151601141c010000001440326010708907401c1c017014100748940c2c103525240c40c1c0e0b280005070400b4015034000001841a24105c0002c0380c01040900d1a4041e40d40c199541d140c032031642040c00518107900c0311040c400d650404d4050396000000a001541c40c0c49410329a42c030407401c0b40a04000c98026030801200d10240001d40c5401c1d07401ca41c642c7d054a03440e04c0c60403001059014204000c000040c0b000000080007480c0400055014000250315007142e0010824010400c3e043c050000c182000b07807002c661141400d280c01c803900300032449603a0340d603401c09164070942020301032007034040c2e07100118a080d6007601070170a000c0554002c0043c013070041106d6080744110301500405503000e20009005000c04001041c01d54410b24001c40c003080e60310701090328040650844400304680c0440d038591000c500c2d84000c10a0b00344030080c07080001c0c0c5d071280729841400100d9103009200c004c00c100b40b03040c040d41007414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 30668045 1250 30666795 30666799
    0x6050706091e020103060e06101107090203040305030604050a060303022a0a030305040819030905100519030507030e01021201030206030417041517070e090712050a09120503010e060402090d02 84
    0x182202e507540078260705001c040c12030200345040f4010800103c005c010030702c101400b8180706040f07595480d080d40c00055801220f60320344160320000c54102032600266000300e00c01e031103143d203a0030320b2000c000a98400918064103985002d2040020030350010300700008030301071300000a82c80341c1001c04643c01108210b00b1908203450300000020542c2c0f04000300102c50054081d03070204c80c030350400308004540088011b0f00080b03030074106105070f00c0c040341705240244441c10b0184c50070b01050103400390300f0307107850240000c203982e0020001d050390180521144030001d10000c514102200800b12840344d81808042d009500100025080204041e0400d0098400c0314219889a07134980c29010311007610040100062036111680c440c41001c0c031081c500803c0162158070780d5441217002d1050b050340041103803040151007403040741c40341818820a802030320028000b007600c001070705085018402090101042000c10001004896000c2014a0b00480c0442e070150f55800d81c000010a2250110701c040c0d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 30669295 1250 30668045 30668063
    0x9050604031202010c1103030703050a09021c0302070609061d0d080711010e0402030103050a0609080409180b090c0618010509060f0702040506010e0d030503131e0c050301050c040605070609 83
    0x402400603800d00c0141d0080070743d0083c4802c20701942d04445281d10507a0040940d401440490419030198201690028007244c000400d40181d4000440304034a5503861001480072420742800d0650600c00540985598200120044e140141c02800314a502010010441840b034004405a480b480c00096407074000f124161144004d0600c06c3d80b01400b542140e0100e11640303900d10b00c60070305000b075034104c81d0048050001161180c941c04003512804a044840c2401044041842c04d030034490801401e41c4e0f69881c040040751817034520f03940400640007840d2980001c4002e01e030f40d5540c804450212070710007507100c0f03006500b100695260160035100c03a404003000c0f40c0301c0e0307181c80540301804089008603000d0006c0c1d00e07418010341b40d1182004510390030021883c0c455020078002c100841e04020741d054208000c404a442d0400e05283e4218241d0019911100110611251000789005080220020082810002d18000c3c2c1441a4442c01c4180407001c5482000e002c05540490000d9400034116 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 30670545 1250 30669295 30669299
    0x1305010602061815040f110a0f0801050606040e071101060e070804020f0406030c0b07020d140a0b0f06010801060c24020405010201060602030702091f030f0503030a140603060a05060109050604 84
    0x29458500c2100c21000f100314030401d0000501002802465200e8071440d000c2c41070720b813a1100c6405019080341951203044a0b1807002517611442c82c100010701c20440c04240ca1820b20076031609589020b00140e1180364180010721444568406541d001001428400c8942800c1c28005016009540c08082c62004035402c00801540142540c4c4c41030b0b02c00c84406508403038890401c021a0000d000103070000401060900c14106c82200421035180001c2203800202c0c403507901c0c215070840015000e07600d0b800006c41102007002c1c10001a03042448a08200c0e01440c0c140c0009107880c005102c1c903410031038021850302c284800d00001c1d0240403800e0901308554405050714802a610038880c580c015840c00c400003030783e58800700540d42d121364002e19982007a215041c0c0f031440c1e40030548000f0303184050f184001000440840b2071244043c132500c0510780b2071400501c44001c441c0a00040148008201d0030000240d40c0070038541e503c0341e42c41d04006040d0b00da00c401222200200d810a9400074400500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 30671795 1250 30670545 30670547
    0x5060d08040914011d150301090203070311040501050618060d02040504090b1f08071205150106110d08010501080406050403030b0604080a050f0102040b04060309021309122a1113050106 81
    0x10f40e5051441c0b1003a0165666902c0402d10381815006030291080d102e003000c21120704280525080e444002400801c0c5003030a60002400d0040c1548102d40b81a00300c0d200c44150f0406004a0340180002c4804608242e200001d0009181c20f54504078400d06000801c3c08190500342d040d80c0107000e01400c100100100c51502c24070205c8141e50b0500c0e1001055012614144104045002d071801a005040c0300342c038041301b191a24901c0e001c00c4801e80544000702820f804074a54241c0286180d0380c54083c90000640d90a0400307042d2202e6504014889005110301c2c0d07000366000d9041640900001282e940354201100204421702100303500c000c0025000400d40c0340050391440d094081e60650303502022180718a401c0b0720880c4511100400d0500c000c1002501075401000001e00160440c0c80e6841050a91012200750780c0d0211004d05c05d450281803880c2e401131810721800da000c5d1001106d940702000d20302008080c060010310142a900703000701d0741d894560400c904154064028810f41d6190a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 30673045 1250 30671795 30671801
    0x614010806090c03070f0e1314061f0302101209050f0f010608010506030607110f03070602040311010906140705010204050310020a02061308030a0c02030c0d05211905060d080409 78
    0x640c0001c680310340745080c82e040c40c0206111048643c01038240c0400b0741f50502c03901c444031008003400601c800e01d1445e500441e50321215a40040f40da200075052602d021082c5207600061319096061014401c7c4081c40185c4070001c0c031903008031041c10300c0d08480550400000107050700034001005409004440c5211441c0042c0643c50b1121080003031003610340320440a400c0300c800711090307a49a030159022501d9980103072004034007010854103880104401000c114035540c428002280c2443e0b00003020401c0c0040c0c40091000b28409103403240c5013600e490310081c5030082c410307800d4503e03420010b0f041c3c3c2000302c00d50460b00140b001605494820303010301c000c58001c0d00b01c08100b0000d0b008960004e40c10354a111441424a98006509800c545611400d10001c3c10340c1c200b0703041548003c000000b0344850030030030840c000000d40d49a0fa41daa4426080d0500041d012607030841c0700216034188050741c80d40080c6019074801c0000001401d5546000180e104513414001400800740003402203407552032a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 30674295 1250 30673045 30673051
    0x30f0304050f040e0c060a0203121009050703020c1b0a090603060506090108030705032d0d05101205030d090804030803090c15090d03030504020f220f06030506010608040614010806 79
    0x1208001c901525005000a83c0c0d03c45000013031a422520000c3c4103880c060010f89902100c074030441b418042081e81c01e401d00c241c00d03078800200f01134a000030045040310340603140e4005c00a180c00e604008840304100d80e5003481034108051a5640108180c103a110035035001c1c0106030314442804110750368140400144025600c0600550555001041404000084603141680003000f1403030700c1a40d10601410300e0001c0315460b8801501059141101140400b80c10700c28981b4100007010306000090305c0001c140ca602c48414460b0806900f0301043c404025112090700711b44002c1542d54070762070844024482e941008010403c08801d1040c91034001072459040c00e001c0d2900c3d480d5682da079030000b809002d08810300e0703405216488603030f0000e486a00005e801c00c3c40074284481411251001a0301c2c941381000b022a04000f8603940d8200010500402016040d8030b00204070160a50700c880342c030340105009034000d000041000c14200f01c0036500c0224440f4144588141a503180d840c3e140c0c8502082d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 30675545 1250 30674295 30674299
    0x20405040b01030203240301020403080d0f0e0708030409150b0a0c0309270c0c0501050a0e01060e0c0f0310080102070b0105030c011805040902060c0102041401080a05070905040b0d02030f030405 85
    0x10078040d00c65000e071003140d0249000c04101c100021002c03103038a1060f00c0f03c0c0500f80d0907540a000000000e00000c02030884520109400f00d904180c58061508440003800c042e14590b2058004102a810200c1100e007511102103000c2102c1c08810880041200b907035104401071000050f000766659404142070035068425642e1a01165032000e8851b007203c0402000300c0ca400c00c01c0700c0a001c41e00c866000f40c95043c22070400c80b612021079102c99084440071109409c1d0252901d65114000d00288a00005021400f07802400c1d800c02031500000d074022042803208200c00040032569941e82c40301ca5034001c1220780f00070355a030700c03070b070b10301612100320a01ca5540a0300c00c0e003c483c24a0b40c000d94500020305603603c07680305032074680403c1102070f10303903614281c1c3c00c032000300305c2e000340c5000030300084c03014280c02c020b890324180c1c842c00018401a4002e00c0d1a9016141c10140128541d01003c504120b8004031804202c0c605048009120070418201c002d40c54810b214100706008000f00280080ba441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 30676795 1250 30675545 30675551
    0x170c0405090a0204080303011202040f0f0e010e060903030406090f1713050f150a03110c060108070b0c1b010e0402190e01020c1f030615051903090506070c08190302040504 75
    0x162500b001c041c0c2c000e601416007184c00034001408080030f42929102c1013400144041303045d09030120342c4011030740305421010845803160b20b0015820000d000710001c0c618000d00512191401d035031219100e010243c4020059503c2e15000070501c80f100c4100842d85402234001d100a01c0707058041c000a610401c034981c0c81c20400c0d00c0000342d501e440040000f490070080c3c0203540604410407252aa039000415807024550740c2c00340c084c0700311855800b40c42c0c1540c0d000d00400207941028121450310707a41da405401303260000c00c001c0815481c081180e0790f880c0142d81c140f5411805000c0180d031404c4484a035903810510104560100076603003100d0700b40c000d10a031240000b50b501c2d0401280c4600e0ba00300c0568102e0f5101003445078207c00d0316134a1214607114500003d101c1e8541c0300d40c0b042c032081c50b904440051390100307698000c0780c485c403d0704040c15140c0c10100680b000b1507680f5611032000a03d800f0601850130004000d200c0003000726886007000c3c600d042e440848102014009403c00d0080501540c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 30678045 1250 30676795 30676801
    0x905040209150105030f0c160f060506060301061407050c090703090201030b151815040f032a03080313060501090606020c03120f0c011407051809040b0c0703170c040509 74
    0x8811801d0b040c105106039221031565030f407013091025058000c0d00b0614092020402c4000c540020002c0518052050340d07001101c0e400c078201642580c03009810103215080400041140d9a0400c0d042040c003060300c1011500c404d890b00f080c50808441c4031005820041c00e4041003189a815407000460341d00c02d0b02c080000000d103900b4807a01c0c14400e103068600b14010030590740341c1c06004404820700d0900801c809941c078031090804480350003a502100d0460f20900c0d0900400c101203031600c0703101381860003d11442100c0c8005420701519480b0280850328000082441c001354060503004040d0009018002945e40d2001103008081610500e0010300075404441014600820050103001c658518a41040380000344580543c0c00900541c040799601c0a0710350030803409004e910f10a5100382c482d2178484010244010794000d050f41100d00c103a074030100300030010710f500710034582003505081c102c0c0e214401882c05440b4102d455550811014000e010444610039100040086d20015a900000e80d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 30679295 1250 30678045 30678061
    0x1170114010e0a1d150403111606050d0b09010308040501030b15030412020f0a060507090b130e100e010308030117070f030807020406091508010608070612020c0c03070905040209 78
    0x15402e0040c420982610004551907109640020307903603802d00100c0c0c1d001101c41080851826603000044801005807404100905810000c40c4903036540a501a02e49900c0781c0200740b4004810b802a0018044046030060341d50200380d00080e03d0400140c03480c417695843c0d0501501c590030602c5180e000074140b5951a680741042410500c8450402c5060360641d1034694031000c0318080c0c09101011031054020024181e04100803000409010b44c10010b11810042c034005e1848849404c01c0c00154400c01c42101e0340000b02425004841611440b80c6442e01c0c0e4034690309109445501c0b01c0340c030115032000032090062481c002c5040f528144868803040141040242c0c0318146031040d600502445034082010401070001040740c944010800503d03642c84d040d0700000c0356400d00001104114101040c010303034100f44609000341c0350010007402c1c036a1404600030a03c14501c282d00c2c110310b402003406006024200310489040c0001010b4540c51a214603ca03001000121000d0b413080905c0d4021501003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 30680545 1250 30679295 30679331
    0x5090703060501050d05060102011b0504150c02010c0b090106080d030b09010608010506030c0f0d0c0c021002060c0901050c030405040903050d14151917031201080d0c12090e011701 79
    0x5a4042c2c6a84d824a101d0001c01001131100402c414155501c1d83d07000f1500c441a10400200c60542d5250a034480e0300b031411398048070304985060418000465000c070b0144c1c5e00440d18407405c41e4880c80c5240c150361480e240038050304855000d1a0035110b1407030840c80c426010f0b0040c82c0c00f00782c280c0c5c480903c2e0b07903518011108174200b0b108180e005941040401d610048044c0103182460f600f0f1040d607d41006d0215503400c4980000d113040c000f0710300a018004500d00031100c0e0305800da0758401000f1034182445040324510036503541c581401000900418100e909100f6140200001481001100c1860401801e540d115807030860076903140002c0010f40d000311116113402181001d81c0f410303000c6068003e0181c10082203c81083d44034a0100000e007200c1c410030312400c01e141c81400b03181c031080c000c41180780e00541a0440006504034013040c070b548590108d00420025080700980c00d400c01030360400d070fa17035601b144c010310140440e030800880c505440600fa103070070101200080006e408031040c0c100e48 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 30681795 1250 30680545 30680549
    0xc0b1b0c0d1107120305180901031a06040c12090c05031507091a03010902090607060608030d0e0703050c06210718080c01120b03010e0102040306090507080601060509012609070509070306 82
    0xc1300801c003442501091040002e48809a80340344031040c0850803400142e00c5003c00d030310407641c8040c0d52030440e075060481911076800c21419103090141d8125000042c12200090506000040d82c0d02c1d000c50030f1041000792100200400340a031442d40400f450392104506084500c2e00124207400000601c1c0e18100598242000160340c56a045908040c900c0c0c01943c0850f4082d40e0000c0d0601801010604e540704d0080205101401940d4a4480d1054181030700c07019107090a02d40c0103410104082400424100da00d920225141b5654008014500d005e060001c5107000390543d03000c04001000d41c0103c150a00c0e181c01855100d00da50390b845500740c0d10303824544d071580046c0c000c24030720076210000e4114500898004001183c0c62002004a03400ca8100da4405c1c1c410f030b5210303032000c0c060250900c0000041c100038cc0c09058550b040220123401407081114090410000590840e41e68201d01010a4024600030718200e00e824041d80207075030350015014207842030300791a0100f40564064452202 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 30683045 1250 30681795 30681809
    0x80a050601090f0f14070f110303010311011106040302061f0b2208120d060803030108120711120c01020106060216050d0f020405130605070509010c0b1b0c0d1107 71
    0x16aa03801c102410019008450b03144003401e032a14050051542c490090100414508040305806e180c100001000d6140380c92014007840030600380552010f20200441e815240c102d9803110a01d554940100d9400b00072130143c1c101401204c081c401050340c040b455074018601c0b02c459030035480071000ca00c4881091403080d0b4140c51002c00c0542000700c500321013030404018410588115075610fa03095420103100c100b8546809000149030749020007548148800707000d00728000c606640c1400742d00c990701e40000c560500344540219114040060040c070807e03000d04043c15030140c04000581e1070baa42c021138817096015508103407002c2051072000420000045245161601c114a001b051241c40d13411041d0a440d40ba207032102c82d00141e01d031800794a0045d5145107501a032010303a8200300007150006070080003000410400c001c100d80e0b1040004400035042001c0c0c9a003920f41d0240c042014642880c915400040407420302c1107100f020440c41c1d10749007240ca500229441288210740c8071841402400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 30684295 1250 30683045 30683053
    0x31706010c0201180b0418050c0906070305030415020a050301090c08061c0f06050f06180903090f0607140f01060905010312030c02030c1b0f0103050601080a0507020c061909080a05 79
    0x30025600c80d5000f11502c5204d42107000c0362036110280c942c05544141c0000c000d8202135980d00820610030b21a030350303010703840000135418101204000340350b512070007034098108036010000c2400c3c003020020005d071180003480115600e085d03491000c1d01d5a0024416000d03001c0c03a040b03000700e00134011009980b044000070328004120158016068040004c00380680e00c0c5103140340c04000041813442914041c03074201e11b000c0c0d1140b8284040092002d8103500090030707008088113011102c071000080d9442d070182200e00070404a030182c04101c06000d602406000c005541e5940d006181010603500715010302d8000900540d9140d042034010785000303100080046201450002c030841c4660b00c01c07600c90619105580c904401c804800745404444804000710b1204011848114980b0305042c16048000303083c140814179000001170407120006020001460b120b8000902030b40c800d00810745030f400b008000545510000f481d25214440b40c80c070743d40c046122840085020301c00010b2180000b5072041c020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 30685545 1250 30684295 30684317
    0x1205070303031d0f060603070b070302060c0a030b06071203050127020c0304030f0803091501230109050310020405030d080402030a06090c030b010603020c070b04053102041203170601 80
    0x86009102c0c0c0801ca002c40e2050741c000c403045803c14400314500101490080c150b60a05c0d41c00c2600b044560f07884214003141c00c2040744d000980101d100365024189960039904c80c0e2808c0300c01e07000380681002c0b041d40700c1e500149c00d2080104038152090952280e81d020000d6a890ba102c00030042c10848000300c40001c00c00c86c1c209020210740080084080541c00d070303400d1580d6551001000742000004681c00030002c001c0048803441003000141001c98800d0303005003945000d03583d8500402d8902258850800001e041c501a4003a030f008200420307010b01220300d54442c14400300000c1d001801894420300a9511720070007184925480c03030203550000d001e840340c100c1d140d964800070a0104412101c0043c900c000101044042640707500130718a0341c030056a1805200c070b02d00e08050360b58105001a1005010510407074031140701c0c10107101e42030000b24400e00790304110034400002507407043c00c03007a00004010030110310341684031003228441d03100c69010781d655803400c1d6282031089030403900055940c0d42c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 30686795 1250 30685545 30685547
    0x30a0f020d1407020a09110304110103020301060906050912070807090b0f0f190810020307030c111f0209030303041406010801050106080c0315030a050106080705090408070303020f040f06080a061205070303 90
    0x30200548000c09032500c0c0b1b0358880b00f000580e5002c1c2d0340401a481c0110404c0305125000c07410048000d401d2900314078660510602410714070181c001c41c402c105000c101c401a40d1100310341403040c2c400b013004465074240da03000c14556561003400340b0b21115003085042d0320b0310b05001d01a0158400003e21500880d100340c02800390580d011418030107030400c01d20703001580c0c940a1282d14640d031034054000d652480d00403406000e6800a031011400c0116110502030020001b1581d48440e210514004000358800074a99020b4091980c0e640c0e41130000100340020480100d4900d9006c0d42c107030041d0381d440e1ba661000c0f642200e100344102d4020994003030028501107000002554421541c0d040030181c03011801c04030745000030640c2e0407609695210300c207000c001c0c010801c10008010807512501649000c0da1075000034020007100034180350f0041090f1064061220641d07000d8000b48034124200c5070398180003481c00800b500d00700e6a140c60143d0109170582411a48181c40d40c00000821a09140d9a4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 30688045 1250 30686795 30686797
    0x8011506050a090b0a0206060108090a0209061512132a050609011403041115040302031b0301060302030a03020a03080f01030f12050d06090203040c060806090109050705040e0108030a0f020d14 84
    0xb4081040031620000c0b44c40450b0070054038200c004d03a0700400701c41c600076002409004c0c0240c980c1c1c0c01c5600a01c40d600040c4d0760140f0341540400b0076500d00403080c0c552440c04035540035452004030790780425400c00025025801c050540d00340030303c0d58500c0d40c400044c0c981003144414040a690511000414001811300c1002070444880624200c501500d100f002d200c025003040d1011550741071b50701e040303414a151040c1200001402d018003079180c00c1c555400a565124400b01e104158808001c0540c05941e00303511482c021030700079042e150300d5281450000c3d2140390403e01180410300520206110f150311500c840d050b203600c14014210f0200d03940b545003100f089080404100403080001c10a0301c0f2240c0034a0000304041400941c0300e042074a49030394950a5600300504100c01402005116900e108049044503240070000807152a801c4003103c0611843e04014020103040c4000681000000700038082400e803940c5083c0d0100e0035010480e00e5807840500d1100244100b4021604228904 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 30689295 1250 30688045 30688057
    0x10e040203160b0c010c030c0e130e0f0a030f09060c060207060b03070b0903060603060c072004110405030105060d03081b07050a060903120e0709020c01090c15090801150605 76
    0x2000c48041c100502e44403080314015800200000350301280078590038500b4040c0060225090800781f00150654500500380100010010310070307411022550072004881d031100340b4100000096030f4591045004555441702c1c000c41c210009008004034801441c0700d06a50320544802da680c1d421003202980700c50002e908180c03010340e0015580d9030f89d113815075030400000004100c1c020041d500c07000c4043c20103041040013048039009410071810028016540f00c2265012640610301581c1035018400013540c140e9a03984054004e840c20346041c00242c0302038060b00403104201c1c000e1045658990501c81400c203c0708004000c6214400030a400c0003080c64001078950030f000c0e100e410841143c131110b181c00341c040015582961f07035007440c1c010305a100e01032030045c0c01494010311604c003910a5003503070390889100d0710719207a9010412002c4075a080d0041454160000c00c1400c58903200d4104107100202c0c101c0b805c010030f40c02034000071080d1060150414075100701000580d85860708400f81c0d0310354055 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 30690545 1250 30689295 30689299
    0x20405011704151a030706080f0402040e0f010204030b01170c100e0f0303130801060b03070f0309110402030a050106200a0f03180602030408060109020c100908041805090d0c0b010e0402 81
    0x11121032450254103204d5404010720420084561030311010a140c2000c400e40c201d4420840d8038400c10030709481118901ea04180d05880024031006030050560070710a500038410b0265000007000400e101d01e01003030504be50074000e09608020382001c2481c3d907504c0150a01e030740000d081c070030318211540100e100460f40e0801400f030030b03000f5588000003400c541c0310110420322191801414000d12100f446440017400091034080c0c5541040d0038040c1c0180354012644042644680401d0100000c840c03040c1c0b0203000c05003045d91a0b040610306000641404d000b003a0000d0b50011200d600915032200d030104017181da0028042c038a8050b128041c801041940540c240940c40c0a288684401101008028040b50380611b440b1410a1216414400d041e13029107a614014014908509008550b0550901d0742d0700f00002d04880c54039081080d402180e00c07105009100c00f804180c0c0001a4100c0b82c400e0040741d0a0b1500c040065806a42c3c4104080300034000b801c540005104034504500103135001400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 30691795 1250 30690545 30690563
    0x903020c0f030604030e0f0402070503071401060e010e091207050f0606011409060c010b03061008010b0109030804140d050d2307110607051005041101020f01060803091003090602030a0204060909020405011704 91
    0x40031f030100e0241e9005ca0802c549076440002c00742306001c4c08080c00000d9040d00c1d0003c2c049245806207003072442c030060141070900c140b0b1001040490004021a190301c80d45500e01c903451b010642401615890780250150403130081800040c410340c45003080100c80c21005c840c450402d00c1311003e01c4060b40103c2e000d505c9942da5200725884603681002071620409030103042c2140b003401e001e03140382500d0030040d8982c14415901001d0001805900a84043c0c0700c1d01c41a00301d0803804d92000444841c0c0042d40907015001d581b00081c4400e40c04440c502c541c0342b03170b6810322803100b2050540e403e25115404000c0c0003201d541210300442d04e003102c0100142405041160403a02c0022001003c4a405450848090703010a55211030340d601400a1140070500900800081e403815261070348910440c02581d05c0b0300106110540c4c01800f944c0250021900940115200c3c58000010b10081d4018080d81010074051032000a290106008071402e0702c1c01a590130f128a0300c59500c91500f24030141003280c0ba286 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 30693045 1250 30691795 30691819
    0x9010909020a120609260304020d050c130e0d0806060f070c0902040906090c0c05060402100507050304090b010809070b120408041517060a0e010e070203070c090903020c0f030604030e 80
    0x70401e82c0f1400f2039026900c0001d0390651883c10310103c000501d02d94100d030b180e1035a0004002e18190580358071580649407400d10203141d203840380c10310411840f040d6010250b0f05c01030303c0c4424241d0081c040030810000715424a030810400360341141c022262641c0c4140100700c442d48240b95100034015aa05c20902d007250702c3e03201c161650aa80040d0041d450b100d641d00c80809c201110350041c0c8510f10010305000d141c0182584980e80c84500040c4064001c44501d840c0c4105036108208480401e0b03000801d903a00d072500d460800c1c000c1d018410103170f40042c0d944400f00324130f00000b2480740d048036842480ca519040c0b4924060501c0c6500400a6034811030920002400240320411000d5521480d40c8503a03d90780108a10307405c52070050314081c0207200200d0300f444220350b1890540d0566894081c008156034076410304a140d0b109582006042090a40c1e0000382150f50750481d01001c0c1c8240c080e030700003007107403030510640083c40002154941c1c840d00201d004a070280b02c0c0c0e940301c1d032002382518000d10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 30694295 1250 30693045 30693059
    0x7050d0c15031e020a081f150806030105010501140a080c09040603050c04060e01050307050105072118050102010212071808030c0c1528020703020913021e09010909020a 74
    0x2902403100794000c2a140d501c0b02c1112020703000400d0340000040e00841c2011060140102400d80007012010250300750a05402c103800140c00a50041400c80c0002c1d00200002e00010310100c02541d01034001d60030100085102d41c0280c4202402144000b42d141c240036208008488082001c0c2090764a04020000103209031030314007404024501030303002032010b28010024041100e48640c80000408800e82c0180301e0b42d0350110b0032100302c8100f440d2440d00d995043c18042131148261406081080030f00c05070720301c011b4220359000d201c2502940300481c000d9403800160700b83d10a440b400c1c80c2e81e1986c0000900680d0042e041d06c09900440f00200400603103441e4a2455548804c03035850b226805018000003519051201210613422000300508110340d02c4400900100740c503007044001d580c071035041d040561080040e41c0003160010101c1c40d440c10441d40020300c45003010700c26809241c211a400d1001d81c00001802c43c084030242c0121f1103a0318180c5a60020250008102e0b8407060b228070010f004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 30695545 1250 30694295 30694319
    0x20d0c05101106060301050417250f030f02030705060105090910050705130f03120e1906090302130e0d0e03010e061008010c1103030106050702040e0105070e010e040e07050d0c 77
    0x14a07090712a4000031509110003490280003c050604c2030381003008010000b60312604006807032101c00000c90f2a10341c00c110303030b2004d414a0a0f202c4031142101161405000c040031101c0c0d083c078002d48410307d10074040e60040340c5034406c982018003107500c9600100010f04110305542d0307001d1103800a0742c8140c1d01740142e100640d4815110f01d00000d4010035003404645015051400a01c400c801018101d0714596400230217000329048213060202c1c42d6804100d80e1514004502c1d0150720f0704050318080d0b01c5031030160411201d07000c1603004600d540781c0303141810200d216148501c2450310040c40050201c0500722000c880d5520902d802d9501d45c0c010751480031041203802d000d858107101743d140d11070602582d80d0031241c1c0d0990007010468100c450300c007000008021681501c80300c0c68042e03a90445400402d0240060141580c103541c40c00301048092584840720f00d8441500760f0f62200740311582c408020075540c0101320704015800403602044140760043d9035003109442119000300e2556100540030304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 30696795 1250 30695545 30695569
    0x6041a06010903060515010806180a020d0e0708101103040f020909010e0a061b050406170703060b0f030403031a03070504020319061706090601060f0302071104020d02070204050105030a030c020d0c05 87
    0xb02c0710046c00030032215a0803000141e405174040d1100f1410400f0b4100349501114058220003030990b0015085408440c0c0750400c11540c859503040342e0b03016644210703440c0c1c4c4100200c108080546030020084000b28080100c0b0300039604454040701e508590f0302001055200507102c0c40701396503540d5400a4501060000101e00b078041c040000700c204012109085d1800b04001c06000c000c0c041109000040c0c100b0101d1f000a001c5003031582081c0c1e00c56074150000d282c075401000042c3c0300400ca6250304004800114031651003590300303014040c524490341c1040421400300c0369042c0c000702030a201e141419406141d00c942504600c0e102500d00f29103080803980107070044142c1d0755401040c0f060050301007001c15002059a4001d01d007941c90035500802031801c044d140002c041c0c00140c610180701c41a80c004000c0540280700b195282c3e0500404c400940c050201280900d08000c00000d0301d00d004604100b0954064540c10301d0b65000ea420450f078410b4404c41100c540199400c041490340382c284400d00703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 30698045 1250 30696795 30696811
    0x15090509011509050402120103170c010203041101020c030703110607030e09010e0105100c051c20011506110304170a170a110a1a0a0b090a020d0501050306041a060109030605 76
    0x5420741c1e41004051400a130080c60096004000089590701100f42035070441e900044420766a0743d102c07440c04028400e0891390a00d5600210910041c000b4050b20510410405d03000c894041c0c40407020315442c2c01092102074600100343ca095a02410300300c0003040c180c1d1084c9031a0450542e18030000310166001c1e0041c0441d02280340050000381040c4984048010050034585041d41d40d6035200781e618001c0e900d4071103c1400b421a80842030340900290702184418070a81001940010f004500078020100c180002c900c4812002030203500802959000a200030041c2d460079040001003080001080443d111511410484901140c84484180c1308549411a480c1c1e4802100d1002040300c9004074080e2610380140b0b980a00003011041d034107041c055845094585541c510980c48007e14009152a800c01c01c58810070070031045a90003840b41c1c1403081c0c0204036698a0f081815070783d81c03048400811303403e0401c00455158481e60b142603408a8145010125203842e9a114000d82d102594801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 30699295 1250 30698045 30698069
    0x2070b0609060603090303010b07081603020d02061806010902030919060204140609030c1009170708150f04080702030703120816030e0a02060705070305030a02060f0108161509050901 80
    0x315600d0072100d03458010703400300c0315a41582401c00440740c60348010b01c203101810a00080c40300401101ca130940702108581840c0080b01c40ca03e090294403000d0760800c1c18014003840001a4102c00f00424262013812288001c0c0b00036820720212070025440a020340c84240300301c0044c0d100e0a10020024540d20303204110240e12140341440480c2c1c0444803001c41746c0308a10610041009880001d00c64041c030034100d507907030090358203204283e6407040e10760410424044002122481d00500290120850300342c84c003140e000101806606014031743c2603c00e03000a016640c0810041818400686140341c001400c0c0d510603590381d40d07a8042101038114000219000b681040f050801c01c2d0003138681408513060600c41001c42e400c1141c1c0f0b6000c80389009219000115100c0c003841001c101150295a001c000c8940e11503054401a41d9041e040302c07080220007804001064030302d03001c590000b18820045429440e5820200d0b503040c2c145401d4580030801081d41c1e8001f0fa03035a5038000450082c2a84480c0b4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 30700545 1250 30699295 30699301
    0x2071a09040c051305010c0f0204050402040b0301020406030b01080a020306180702150709140108090601050114040902160b180a020d05030910030f240b07030c0501020304030314150a0605030c040902070b 89
    0x440c4d00d1500d43d80003d041c403000645040c0410486410720030059411900003410380d4a0f48000340080a4158005416610100d008200d00f60141c3c4501c91481e4241c030751407515074540e0704c940140d100496507280c00c0381810801910031500045581d8200f90580152542800318210181407980211000b000003450700030704000d00d120b24000644220800e284c6007100d45007000d015507480c00107110b824100503c0c0214941c0004d4090140c81c0a040003800039955013883d17600c030200d00311140c074040d84d01c0f103207440101c1c0900c5101c95503150a0a0504083d003500700c2a902080325000c07032054141c60b0b50004015030b5010356160581c0180078502a18002402c1d0009081c540c00c6581200004034480035901d0100100703090b002a0401300c0c1c0b603031a4403d07590310f101d03d02150709141144009155600200500080641582010300d14040d10341c80025540d940c1201c00c80148100c0050b150000c2d074081c401d114640c4150000c0d41d0040b0345005892034aa910740d1684204d0f440742405650100301d400034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 30701795 1250 30700545 30700567
    0xc0c0604110a12030e0f0f04050a090303050f130209060f0909070305010606090e18010608071805071716033b0307020a06030b0109090509010518030a02071a09040c05 73
    0x3800c0c00307822981500c40e50f0b2149560050b007104101100148900c000e0b192540c1250703070300e0150a05546000c0d0081c042402c140e44142d01601400404801190030300c000174482c46019442584074040c038900c1400c0b260b06036000c0c84042e00c2d001e0030481c0c00c044184103052054640ca61014040c92120303008000e40c9255081090866906801030b0003044840e41040008641c001c2e072503500f1040d080c5144010049030b0340203a00401507a0710012040c02031440c00900c8001201c40c0c1460301c05112824000b43c1c0c1c0e030000440d40480d44514118442d2a1076000c0f80145040d621648202540c500f4000754550442c52990714408013444545130740080025885540040c8400707400c03480d10020000d42c00c0100590000b0004400d034001d140030140d032200046080d038401c500d01e8000389400c80c0c0411040c00c1007400d0314064407045410090440c003000c00388429030700000072501c8403034041e406015040c0c00c114400038241482070108549030381c00e0240d2140d0ba6a01d1194a0072605a0b03281d4079514401524 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 30703045 1250 30701795 30701809
    0x12090302030a110c0d030e0406030512040f0602060f070809070302040e0a02190303020706050304051c0c03020c0a03020618030109080a030605010207120201020a060b01020a120329030a03080c0c060411 88
    0x2c0301ca5a40003000b1180c913540b1900d044800301e642c03609140e8819421040840d0040c900340d44080d0451040c0706c13264888224050052040d01c440c850110340241d1510403d9a4440003562008000008a00000c8040c0d2158a1094004010070180c0d00c11903501d800040c1a207030f03503a0000700c3c550441c0790075404526003d01130900710740010306078180342ea02d1510302940300d4030030b44240010320100000240400100b032140c100e0344000110003c2010044010092030100c042c14100c02511400c0c0710501d46242c401054011643d004150a150065481c0f00d940c1031240c5201954056499036004c0c800201c0d804040c1c07104906039a4001190707031910b0300083c900a2160300486020038400c0700c140240c2d070302185000310603401c520042040200c400040b4503105207010040c5c0100580c0040c111036a6168000045101c030440408480c0a1361100c911080d83d8405101071345a40500180e100081c040c5003115442801d1b68201802c0c01d602010450800a049604a486501140c04603e040c50400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 30704295 1250 30703045 30703067
    0x30709050f030c0103051e09031b0c0d12021609091208070f030209010905090915070f05041e03080301030b010e16050702010e06040b040608060306060d0506041212090302030a 77
    0x2601d00101c1d80005011980ba18065990281019103030000610004140103101c08408081c010a441c21300d015410580ca0b81c100c41010110070340d0000c0801c240203000181c0c1703202d6090007821b4004c03a1109545441040c144800000701354050100c003580c0b02c0101c1d56201000704240c00002c68020068680074040980c0c51224105001d15101030004441e8843c00e590ba08505504005964640305401a10740d8282c9620850b8042c95032010040e40b000f020030200160301c0c1605c015015510749240c00d603a041a5480c0100c0021000c4c001008820741c6914240d82006d000c6443c0d036000340e1a074403406890384c001d800c15184100b00c01c0040000365420404941e000d088507050340d40d1100540341c0101944500c01d006410403e6504088489581d50f508a400815401070502d6441c1e0392100050100c10086420f0b620a000b10000280d603403c1002000038080e40c007102518955803507540701c03050300510b01d050748100f0104240040003000980701341d04a05009070015600c4403080f1000400d000494 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 30705545 1250 30704295 30704299
    0xd020d0b0103140a021c0203011404050106020c010c08071406180706020106061205060f030f0a110d030f0f0c0203030f0304050d0e10120b0d1a010803250f0204050106030203070905 79
    0x4102c854100c43c0440d0b0b410798115070000400b5070764090344107013842d40c0c15000c004403a94501c0000000b504100c1c030040581d108030151010b01c82683d88501c1a0b03140c200040682e40801e0142151705c0010301301d14010007144d84100110704200f442c0030981803805504580a0b6170003203900140f0348800c9c074100090b1004200504c0280826400c0002c000c148185248140d10300c03503160008076031140d80303255400c0c903e5070001c0c040301d12202c0324004007a9101656541502e04d154101e0460415013000103000f50820307099100d101002d9484101114103a5100482e58104070710201e4072401640e06200908024440029460f00c170b05160815509100c60020184140500d801c5894050340b1200c1e42803019041508065010000002041000e040203011641d80301001001d900c04010451034402c074010781d5030140d005140e886030182542ca10419000c80e6130302901103c1e0341c2d000ea01c840040c0c00e070284101802140001554041800d855084c3c001c440803c1c0c02008002c0007641c8410010001c001c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 30706795 1250 30705545 30705551
    0x3070b0301080d030e0c150d1a1e120f0a0c06022103070e120601170f0601051909020a1e0c020603010902090a03080d05040308060a03030f0f11030d020d0b0103 70
    0x2502c00001d65460302218210140745d121001c420404109201c030001156014102c000c030440d80f08084c0c50f07039500100e00d07045814602080f40e034035140100310b4014440800761a9001440181000c0c2a042850135101d95004000c41405c00d1001c009202000840720a030004100389a407a103088900248260040340171507018048100300300042d040064a25010001da060b0b803512408402c4500700110701e0076a03040b10b41c20b00355101860300000d00c64100c480c44a4003c10003416130016944900130408aa002036120307000501151a01c0c903600341d1040010444241c181d0f076200440e9060780c001a401c1004a9800112703070301c640011904134081c440d651b10300803a005c0b035980d0004000e400180520102c080e400703c1c031a41c40303880380307003a910246030031500d896201d030071400183c40602b03411501140000d82c00400300c0c80741d007800348529044e40e905458500541001d4002251204042c5c0d80b82010043e495907011507100042c4018250100190f0740580d0715485e5500803415070b00c0340207080d41014a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 30708045 1250 30706795 30706799
    0x70609080c010b0f18040311010b04020c150a050720031e07020102010b011b03050c010207020301021c0f0b0d060b0102011d0a020306090313050112020403020a15031410090906060801050103050c03070b0301 90
    0x603024080e1540103900d41808d910a102da44d028074014848080c08607007180c80019610030102c0d00044082008000d20011001952241881e205680003511800d0219020300210038036060440301c001c1003d03030a00200c83c20070f404400495088900484822b0f0b18010000b00c01c002c0d03517828021500c0b5000203007044034030f040a500d85030940c400000d001804102e40854440b10b610700a40403602201d030014000d644450300902071841d20300e2040d0408010f10f281c4010000041414056081180300081101610034804d4648170040c08a42042030b045541e90312421144402160fa00c070208c4c1480c1c0001c2909544520502d4945500a4407003403155000380700030802e40c0541c182e600f041e0b502c28a0007203a042020103a000190240341c0009512403400903000c40e61468041103078002503400d40c2c01b4807040c1190901c00d12550f0082c0c580021454903450f06000488507500440f030b209202e4180040ca140d0345810890840303034203070001c8411760040c0444201c136140802500d07019080540010f17203154 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 30709295 1250 30708045 30708079
    0x30f07031b030c02070e040813090605030d0e0301150b1c0510030f02031905010209090c070c14060c0102070507030303240513020c0114010314150c070609080c010b0f 73
    0x110001c4420081680712180b69014603c2070003018010b1840101418890400e46400c0015400c45801c8180e02186d1600c00540890302d40601c100311000500a0701c1720300c9c0c61000032076000c500702c10b443d5010340d01c9069240442c2e000ca140d180050100151850701c603082d0302d103902041811240b10b001030074140410700c0900149003c01104903a4800000989a2110702c040303801e101101c4c0c400e004e40c0c81c40e51503c1040c0101034009261014044500c400907981701c58850f81c0a0141e080040c284c0d4000c490203006000501030710705e5000740014800c9081c18001740e002c5080ea8010701007100c02d80c00011b030400800da0540a11070260401d040c0340b403000c040004100c115000c803485030350f2007174203080c042070b0714a07055504680702c01800c00000c2c09015004030798035001410071312084642c58026503a42e41d51060107d01407004680641d8881480c0d01ca4008101c044c0c0c100090544c0d219649640c42d5001075803120007407421002c034500100b200100c1804218040540222031406140400c819407403507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 30710545 1250 30709295 30709331
    0xc0f050a09140a120b09060f010621020d0c0201020c010513120f0302070804030308040507052b05031303050a0303051e01031506050901060c15020c03030403050f0c060a02030f0703 79
    0x2e284056412140180c0000014030503803400d0740326a500f80100d07400e18050001303468030b45204d0105107007158030a85a04a40c240300c80424481c4400190504002c410880c80084440014000722000542020400d01480e0120395a036014200540c1d4001011011203d0178068568016500900c20703035001c03019114032038032825000301e00c402c00800c2c55a0307413a02c034020313410780b0042900b000c50b06444036100d180140003030304192001c2d5018421088005900e1030660540c060b03022052900441c3c148010079141c5002c10200402c4985000a0004030b1a0384001c540150003580200b00070140b03000142400303412280050401400c2642291b01e120400e0900310300541169805a03906401c1101581b85200501072600103541c0315007140000914254008144003110307014480700c140c00e03461118410100e215000720050190402d10000700842d00500280c01000d16940700245020b0314884280c0c24000200d40706103105078040180121240344287c41070307201c40d41d400c0402581440502020030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 30711795 1250 30710545 30710549
    0x606040603050c010503100e010308030618160f21140109090203030403020906010c050a05011a03030903060105010c020604080709020a030c0503061806060405030307060f0b0321030a0b0904060c0f050a09 89
    0x5100f4000045481541f2a40c0c500008102480c00e64002e9610b91a00040c10760050b18100e200d1040d08403000f6068160520641c040d47c01c1c0600ca2001803250300c01500c2c0203074855910300900081200c410054007000c1601a05810040710008020307511502012030071506030800038000b03281015050041e1000030444094a4044031541c103540c5d18800105e6500140c1c00c801030050041d8800ea1040002c150444504030783c00d40e0b06040211400028140da03800b560742545c1e890741c00600100308039405440c00c444994000ba02c184d01d0709445803d03c1389000d100e54007103070b00c060703002034890100d0340c1c0361062445141803450514558241400001c14641204071942c000f0700210022800f16516681201d00800024090340d407518072134200440107002d8440700c804014103100701001645400303c0c08001d000004c00350036038260380c4003914180329000100400c451598580d030742c040300d41e1b80310000e51045100d94004119240041c4000f000d9a502c404100b0a105c402c3c01101c00d6103400040340c0f41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 30713045 1250 30711795 30711797
    0x603060c1306080604021b010c020d0c0b0406020307050c03030403020c1003050103080306040f0204050406060909050901140412020a060e0a031812060908040308040b0309070b0306090708100b16050606040603050c01 94
    0xf083d84803000060000e100c1d4004441e120220822414a4141c041d0020060129150255600c40c211244299140100c4440c0106044c030f103d400200007c00c1c0303a0103943c001e403180c070b040c40c140309200109030b03d1540b0944040c2d0150b070001030406807a02d01840d50311180400c0e1b10b42071110f5490b640e10b080c072901020305458170613a11052901d13216002d541c103031001820000e0080c00903981c0d600d0060442e9240740500c101d000e091030005400c5100500800301010130040108425a0321600c03102e8034211130f80358140450254403802c02c041200c40c001c0c48600c04106000c0c15400815203802341c401c0d21141000d10f10301d100c11038200445203030180703500b10164000380e0104840d0b644d442c01210300e02c0749803c000d01114002c6004101c8000f2030014501c2030b1042001c841842d626000c0d0150f0501044809039402240c21000800e0a8405d01e0282c0d00500c4102a10458985400c821170300ca801c1f007000e88502c61005c0e42c545051010400c605504540b0030341e82045280c0c01c513284d03207482d2142400254 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 30714295 1250 30713045 30713057
    0x60702091306110901090803130e1009141e1006050912010e0a02030708060402300d110709051620011104051f091406160b0603060c1306 60
    0x1408480d9040d101d1121158408000c0000d410941d030030386120b403c40d10030503002039840310011421400010846000c1144240c5050807640b416801c004119002881010141c100640025800e4054003038108401c40140210100d840c10040d181004e00010120358a1142d9040511500c0380107185a402500c01d01d1400655070041080400c6500e400c004c0c00d5200c940c40d160040040041c04541002d08509c2101500c511a0f6180501940c622042c1c60103035006d1280000d662110703090318007500c01c00b507810880321621302d1507006040c10b02800d001c546020070003c596000d501d0100388210409403141400800141c1091040104092454a014400d020301b00803502c507041c41a0301c0368405064000002d100f884a03d0034214400d8009210b40ca005015014508114541059210001848035541c0c00c000d10700c4d0901c40800d031505202036075001542005242d4a91130340001c02103546024040198141c20a0014186803040061003103a0b200414010054098403111514044803150b207004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 30715545 1250 30714295 30714301
    0x504060e061812240414030403080a0302090109090f060314031303020d0201050c0d170705030601120b060d0f090c0b0408030a0e0f1c06050a0b01020a03080406060f0e010f1406070209 80
    0x190b107020401c1d0000044d82e1803035500f000d100b6a0012146100e1841116076500000030158201c0d5240503901004003034210034080001c403588650301900000105151200d209960b50580034202c4892040d2045220703100d41003801441407403650070382100e410900862800d4003020541070038035440e000c02480703145034090101c05d6a01ca00281c07090806a00196400045510381c0a00b460000b140c02e8210503164000240c0080c0c02403040d00e00c03d01041c3c40f030800d00440d080307614000b00b042152565103c0c1050122200703244c050300c20954400c000b043e000070710001c1410704248107a00e90744114800c08040106200c5544c0c003106442016409083c10a08414440c00080b0a4080d40c036070650000c450310792451103a1102610720310f540e40210380811007600c4504200c01039a120240300c901590144400e50f00192066044543c858040da10000b9419103400040c0c00380e04070760f8040c1d80045041e000500882c40c03412403100003130402c100f2140005400a0115965024602c0003a201d10150800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 30716795 1250 30715545 30715579
    0x4030b1302090f01151715030f010e0109030e030601290c1002090907080714070c050a080309100207050d08030a0e0d05030703060e13080306061303030504060e0618 72
    0x1010031254014103802c032a25020a940721419424400d042030f81d004042c90301c164034086d41400b001400c001e00d0007841542e840660382450880c120000750180301d0546a0000700e039003031159070320070080071002191000560a000b4031441e541c19406209800040040000380c0311501000650080c900b00644c0c1060042c46540c2c0c60300540381d1203042d500942400c038a404105500400407202c1c11a1642c05988415004640c1244202d0340c1c5400b14007002d040085440349030011708046c038801c0220044076a20398010603a03030181940201120740c008a0551098500b03440525610751040c401000d509141c01d0005030070b45203034400545180c0000010801c12803403030704105c00f1a04840100c6100d41c901c1000240700d40c2c01100c4480002c2d00d0064049100c01c0200f482500421204410322550002c54450b850258806040d182d841a420000d02c40503646209040e40258025280d65842e02d1a00d00041c00c0740b5070186c0458400d944c10401e002080488002500440e08282c46459000c048900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 30718045 1250 30716795 30716821
    0x501150e0118060804140a02030a080c03070203011109041d0705010f09080303041505010501050c0c130e0601060c06111903090507120506010510030912180e070302030609060f0604030b 81
    0x82e10100802412070041800c035000b000c0c0601451090342900050000b44409544400d0341d008000d5143d00300d2510035020500d88005000c41d0790f602000d1302c0c6401120344c0028212404080325041c040b101044042c11458203107c1c100001c1254031100600f241c2801155842c1d030101e009881c1440300504100c50481d1280140b00003805006007240d65904143c20f100001d0700040c0b4003404124200000403600e54030610907910a14414030080101c1c2000c0410070059400416034410700950350404001051010092240201620f8841498042490900d01d05844052203003440049007040010440c4004000c001c0f0504014540040c0606640c98150705003501c9503c1542c0c1014481c52990074032a02282250490381c041f10602c6003041e0b00030081c0d05984041c18003030030302d10303040c11240079040c09044140d08480c1800031020045480741140703440d1400603501c15000070b82c084100a494109420315a80224040301d1460001c182403000801c903110346c1c08010300c461050307004990003001180c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 30719295 1250 30718045 30718067
    0x504031202010b150a05040612090602070b0a050106080705070b0703060503030d0209040e1501050d03020109080a0f0305070908030318030d020c030c0d050301030f0f050a020307030c06020d030501150e01 89
    0x12419080c5850040d00c000d018002800c852480303a0140c0382c5440b80c11300b0820460355403541540b40d1504142c030b4000f0580340320221008030705c006512254404006003643c402000700314071881543c0c2d0310b810150120070865070305810040c2400a0041800310803038100040c1c0f1242980659150410b80e10ba0304128050801540b01980620022a61030745031210360300904040b080549042003001d0810200c56540c0e080340c001c800d10700c0c80b0000107000504054075005403003406030001051031201070fa140305950b4440c4070b1a000040701004051904c40e818040c29800480d10700c1c08440042c01c2078410740d02c07480081c0c0514007080b20142c50410480703042c070548120184c084403c646448184107100d450741c1c0200c507140d0003405810303241d00405000f101524142d0382c2014610f0a090084da5038010038403800301080c0c906102c0c02c41d003207005a90401c200005548183c1203000118034121000e0703d0450701401000c10b041c01d10005010000b280920fa003140101c0380f408584880d00c0702c0041e00c802d400382e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 30720545 1250 30719295 30719303
    0x809030106060207090c030212010603230c04140618090a0908040b0403050c090405030a0804020103060506030a0911010e1804020613030303060510030c0c0209180d0806130501030f080a050403 84
    0x41100042c1c0250040380310400c030b681c511410311021030100c204034101d2154001c980d000030104001031103249c1c0300c1c0d401140381342032580c0c0300c0c0b0070b501450410384104102240c83d14058a00003c090000e65142c40503803000785015a40ea50501003401c0402c110f62022800c03140c05500704000160041955411a0036004d0300700083c0c541e21900c503407800e50294043d000a840600c6000001c00c11407c2020b40039200b20707013181c06541071883c8054211610900500103034105500c03900007040980d00c050086000d1012100000307144155858960500e002c1c180880d0b041c00403e143c03014082c1c40744004042c1e9020030005901d800d075501d100017400e50103407281c021520401001c01100301500b40c0d1104082c2c1b4001c8900b8a042d1503010741c21015110140b0401c03001520b0221b0740001410b10640b91508030708195031000c07030010020300980c41c002000160030005011001440342038140f802091f61030384449002071001e58110b4890400501c0c1e4a00000c1020b1400039500901a00c0789058802031644 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 30721795 1250 30720545 30720551
    0x20c220b03070f061106090706050a050a09170a0b07031802040209060d02030c0406021c0c0b09070504150302091317030a09020901030f0b0f04031b03021608070e0108030a090e0408090301 82
    0x1142002005d0b1001d403c001c01c800e01c1800c0c045040030000007540c40441d44e07659542c1c0e01c0c01400070700448154020545090a201a84801058a49030381d42e0340c001209407200240100c00281c1004203181c80068078030018036107459014240382c9aa0245590f039075405407070140c1d944070344102040407849110700d8810708610100074460510580c100504c1202e6169088403400c055020f000d0804030b0050400d04003240343c48503c2800213401d000000d60221305441520107040d0740f000414190341400030a40c080844d51b00003403045103401031009820202d0146a8cc0040c02107a40340b01c0110b82c60b03900020301880200004240314400d4101100d1070b81c0c040e101011a580d81e01d00580c100c0203940342107913075003070399070000b00a580841e42c0c0c40c0c4030340c0d09603440c072080306203003000c12102c00f00080c426804c5000b0315118945d6003c10784d0583c4024005040100501d038601210742084080680007402590401c01c894611a54031084620680b0a92030b801c01c0d55846515120401d07200740810240c065003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 30723045 1250 30721795 30721799
    0x30a05010603031710060e0d1a04030807030c020105090c091308070c090605011706010806010215010e010f06020f03030604020a030204051002100f0204060c1203200901020c220b03070f 81
    0x54441459046401c40901c501420307100c1e21060a1004998025100000e00200c1c80b09820303d03040c0b1a05110b01c2c0182700358421003107802e101750b0301035a0484041d004241c009050000712941032103102041c0c0700c1c0d44000c00440c10b1a0741c26035103940d40240b095101c0c18901010807008140800c218500340da1108009640d12024a0904903000c2c031841007503000742c680400000c00c3d501034018628034003200801d10f00e641d0fa83e1001510407010191030307103045128030203c5016900082d070469018021450010780355605d01038a000c1d401c3e85a400a0085411030034071048840d2000058940002c1d044a02503104e400981046000740a40d9101a501c0340326049a582c0c40b54002c52a4078046130102e1080c0080240c013100c1e0003e074448c521a0200059225203e480172882c00f0b0343c45c0980940e0343c500480e4000840d800701038180e000e03000103000c581002411018568042010300c1d1004070503181500241c89907070422001d412000a11006ca07605c0d02d0780101c1a60f024803404000c3d0102d404942e18241d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 30724295 1250 30723045 30723047
    0xb01051e031606080a0212060409081606050906060111030a0305090309040f0506040501050f0607060e10230604090809060705070e0a1401050411041715010e060414061509030a0501060303 82
    0xc0c051183c01c01284030344012072861041c40c0200c0301240031240110403262120010b10005100d443d1090302c4160007448201c025580c54808140e40502442c1e0100da40d04010282c00d080920182c03079603050024203d010030301d90f40003000f0340d02e600c0c00750b003400205640c0d14541a8198030500780e041c1ea01c035160100084c011401680854003428040e1002c02c2180c1e00c50052103407003501a20b580e54004400d000c000005400f5402500c10b85402e1001e454640d000004541d09541070b000c1409a400500c48506104c2640a60519800782040302e040c0b1503d03001d0b4848110511500e000c0d9800348c1000140182032010410051000302480080c074041450140d14080081510490700c8220004000c00000e46281601602010103900d4012a02c5c00e40f800d420030000d2012000b440c421402030a0b05a041121004c91080c001c00403110301840034509071040008581042d0f0614103007401100602c0140d884100e00442c0c00309903001456503849030b100c0028508412400010010741c24003074040101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 30725545 1250 30724295 30724333
    0x1140d1a0a050411010c08040b0702040908040306020403150212010306050c0c0a1506050102030708190908060f06040b0108100302090702070e0901060f060906140706090803040311190b01051e03 85
    0x43e034002c2c1040720003040f41a00450b0001c07114000070b0403401043c0801d01001803100c0082c49141c0c401000010b22512598920f074050b0041c2e40203a8125070302180c20028400c03030700700d4004402d075039510841ca0720303420710031100c0c9068040c017026000c0b641daa030008882040200407070304140301e0700003241c040c40c0040c40c1038000004c8040304e00340315030304204000559500000c140c9010562040e80a13003411b404000960b4078852000c0810108041258005038002c020b010403801004d111000780590300c0c0c5041070105032141c1100981c10840d0306420010700220040500c2c00742d9074120b502000c0781d215207004914255a0b40c00c5030300103e80100a2140c800360562080301181c0d2100c610140c240c0d40c0d03050549110711103100325408940904040002c0504c0c0f4402000c8042c030411000031504503c0d01c440c800c07604210f904801090a0a003c0303580c00d84200300307018a91041e815100f0341194681d032040c0ca071031410310440d40241c80c3d1000501403215400d581528041c000b40031204100020302041103070b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 30726795 1250 30725545 30725551
    0x10605040e0304050303070b060a030f08030702060606090906040b040f02040609030507050a181e1e0f0e0a080d060e0f0103030801060206060a0b090111010c0c06060503010501140d1a0a05 82
    0x4114070304101005044000b10550f411104000c015504103407450322000c90320000100642c0c3d00960780c01c000b10014800c803d00c601c0250040c0c45007174492800190180c64030b500a8110b80c40b411050050000c5655007d078155445a4182d0380803c00e0300d0f0407008940504842c0c8004441540003190100b01c259000d240c0c14201d0b03001c0d001300c840c6265103070203010070100d071806040c00c0780420008042d40c801e11038200340e40c0032156a110450000004e0400c400700c80c4190a6650b003581224040005401c1c60b002c0c3d1607441c0c44001042020a160101c03550f610184414020020319011407405500d100b541c0c80030009000c22295042c091402a00810a110003400118081002c00c0000300c2d02c1c91001a80ca4482d601c06030006503001e05003a400c6105802108800703040080d040440503680002b80103603e40d0840980311000e01d03102c0b03407800d001903e500d03070031141c0030360715190040103510b00d5030410749030302641540c1c6000c00300940d05010003010400100c100c105c4401600f845905c060315400144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 30728045 1250 30726795 30726799
    0x6190206010b0f071709190905090f06060f060403020d050c0102160303080606031314060603010b010c05030403230a03020c100206060a03080a1704060204031b030b0c0a050c0a05010605 81
    0xd060303030326110000e02c2400350301c5035601011014070140d00029464000c207072012110740400e5091001440024030070300c2180145004098013943d04010310f8002d4003c290700700d115100a444844480c60649680b00720042240344600002d41c0c8103201d0ba2200c108903000340d500078280f903010b1061402c001742e864101c0c03a0b0540c0144036001102540001e8400b40710266641075030b41c002c0f603859460800281b80c03c09480c042c005143c25a07140001400b81c011024440c0300c1c0d00207468546850002c01d402c44107031044c2c20781803080142103903000440100481d030a40ba80502c0040020b0700004024416400c0506440150311440f608801403580014103aa00e02c28101c610407850301051008a80b01d160a90b082c41d08901c9043e814800198060090500101d42e40b40c9034480000c1c0410900041c04284c4095680e40e90016060003030003503010115070050300024541003200e140d07076122404000010700c101646c01001c10580d80d01c0e84036804841c0011218000c9541d600c0341c0b410704900800d6540f007194 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 30729295 1250 30728045 30728053
    0x20912010e032a030a030b01030e0a1b05030f0c04050709050a060c060f02040605031902090d0c0f0e060319020a0b030c12060108070f032c060106090602030414041802061902 76
    0x2424105400943c40c00024a041c080c60500d000810254041c05007130003024140364550310f02491440d010800c440300103001c1c4041602c5503101d112600d10f50b44840c2c001500980042e08016180100001c0070b03158a24103403030000362560b6002d011143d680068000d036510004202e000104980d00c1119612010b010f44420071524044103103000403449a84a144040b43d81400021194800d1080410b90010002805403034406a44002192110303c04402c4400829403441031110006a0081c08090600380003440d14508120002950b80d0885281c03600d82900b0320040c00003107450700325810f8024218a402c0e01c1d1030341414160351006810600e802c0840a40020020360f0361362084000d07030f025501640301c02006030413802003240900313545a10003203419a840c001100728061f20520a00c0c400300d54000d001254144000146204034a0f404001154414070085c84600400e866800d0034940c1250000303007180f40701c4200303d02041c0d1034001950142d00421060788205c0904569101c4000b994261 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 30730545 1250 30729295 30729337
    0xa0f08120709031106030a1103010f060216050d0f0609050106150e0a051318150203041b030201080a020319050c0c070905010b0d1d1609060b0306090406020912010e03 73
    0x84400b0106480040c1265160400d00c0610381020001950003141d44c030070109102d20a0380303581103668801c3e404100003c028040800c41c00703505014444841d2601e48802800707504c4c200c00030700b84612044001e018030250381c62110401c0780c0380e07100b00c482551102c000e0080d01c0d07950b81c0d418540c3c41601d0342d1038085803c41880b1211480c12103c0718055410007005902500c10141d012401070400b00c89000040c11440e5400303001c00c0d403604c011100031003103074030250341c9107854640740304144a4102c000c05929080402400180e03040806154440d032008401a00d07a0703030b90b40b03415040307404203603000014514010034004032a649a000f007e07a0080704c0104ca214035511104101180c41c07d114442009106101c00f01d00c01d54982c101c10740d094490300d0030b04541c05180034411305000e03c401c06014404400781e001c201c010114087c06005108500d00c1c581103142c902c1c08916551802030008100c1ca5000454503407943d21030308a500d040b8040c00c0200440c01c0c0101e101c0d51381c2d9100c560100c1807034000d8254 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 30731795 1250 30730545 30730547
    0x50f1b070509070f020d031107020a080304050a050a0b03010509040618140f031314031f0506090703021602010e03120a03050108010b0307030807060c02030f0c0d09151d030a0f081207 80
    0x3003021885444d03005106d00d46205e2011801400c002500f00900101081514096591129140c010308402c0010719a501e240c03c0c1005168507140d031020b800340c0c07015001004a150f945060700d0446100313581030520340d520b503d010350040c00e0704010144c852036034080c00340c10f2251000040312a42100001c4400c078081044200c2d6a0340a038207a01c9020040c030400030b001c02c0c0c40480e0140085400601111000f44185c1c0d202c0421f00500b03c405601e650391441000002e28011641d984c000d0356505007145007a5144544465034048600c1c0641800b1140401210036282004800071525490b61441d845850700314005000c0e00e82842030414031f40c284580400f0741e00d004181c2030101c80d40007009601d4000e055030b4800150804200c1d02055001c1400f8884c01705190500410044e080c8602500c0c9512210030007a0038812076800254a044200b100703254142e4000000213100c044040621160141d043c00103403400d0000320005251480381081c0404221203080a4000080c6048031b41205541d080c1e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 30733045 1250 30731795 30731807
    0x3100f1202130e0c0d050f011b02010605090106090909020d05030a050703020606030105010503060123030313150e06030a0906020f0a020106031a040503070803090109021801060e0406050d0201050f1b07050907 91
    0x120200d80303030413a0700d66031503900e005166845c1092040041c0c03442c0102d009141404c540c0040300b0b00320f9050740c10364000c1c4071305e90a22030035001d44402c48071001c4550410710010700c0600036001e40725220b503a0f20703580000e41d902c6c0b60000c0c0000e5840001c41e66180b0380e001d0010b01e9074000503800c8000d80b24100124100d0b180c18010903043e0366020740284a41c2c0e20305982c0b51980d118102c8854524000325480e582c1c0381e2802e00040100d00d15054090740c001c4e04d8040502d810342c0f0f00850010401c080d1251805141d81d40004494000308a000c0c049440e01c202d080c0f0b40001c1c4100c400d004901c907000a40c04501503019013098040368000c41048000f2001c0c208451030412003150010160f410402141e000100d40034090760700030912400004484120f0360204500c0c980d010300300c0e42800c07071040040100b1070b440081c030600150142c400303211062811005c0341c08100c12260082c144500824004041d040700015600e008103145400b004c00203d071003d0310348402135030142e540507995142c000f4600a014817 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 30734295 1250 30733045 30733061
    0x1060f06111b06030c0705010603030e0901090b090c0c01020405030106030614010b040614031314010906050c07031b020609090408040f1401022d03040305030301051306060c0803100f120213 83
    0x6504440e10710000800c000091340300800200648000340402000f044092150001851080c5c44002c14050701a080210541c0d0507800081190f040c100200c4a6440c1c040b0441d0700000380c1c21000b5140d0705103860580c06030050750410341c0c03d586001000028420550049034585006006200b05031340ca46064012500c150301445000c24960b0b810034001800040003154401c008012401c5901c4c510742c0e0b410b0040d0480143c0040300c2e0344402d2186d007030202503c24141c0000c4281d2a8502c0d11019540281c2907003001030b04000708003140400c060540d25030b1021900c030711030004c0012100c0d140c2850084a41d4206000300c4000c500028000314690a60000f801c0c407aa80580040201c00449540100100f400d210b09801030110304501d01442c04003040640050351042010319141d605141c10302c1301010a00e488401102c2c00d0590400205400c204501505600440f02d56a00c2e500c0c9a03002d4240c00c0b1980c0001510038030207000040540c0302c1101074004600c22100560b03a00d014500c40815640c0c12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 30735545 1250 30734295 30734323
    0x103060b070b0a0204050901091410060e0105031e0405100b090f040209040201020a080c0106060e090103030903141903030902040b0108011401110a02060310081e03031b0c01060f0611 80
    0x820054011034810051154040c2c03c5440241c03406841d01c4c04101d1080003a0302941d06640c844881e4100c0e5a861802130b54004070110f11054120f1074804e004150815401025050180c004040342c5070181d201c03928452001d880358402400d041c03514103e640e58001400642402d407414560500514100c45043d005411600018049407926000c1008034240940124198031480400c1c00c000381180c800b910241701c28100000f01e03d0f02d0620094406801b178403011f44104944001800081d80140d043c80036aa0400605075202c7d03200d070885e41c03038600c1d441080d008882811154800305036243e040808407610945041c000e1705030b01001035620040a00900c000501d807010100c1d010f52040b15911200710a402c1111030016158000c210381d0340c0280c1e10340000c0c00b21103500380b0130200c003080300010028800050760b6030074464806180d00c81c0030203002084034070001d03e092601c1244c54016241c1d41607105008022680d03480c2c2c2d0b1000ca00f556881803801041c40b450307081c0d00c1281c0202d229440b420342 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 30736795 1250 30735545 30735547
    0x20901060504050d081602040501030602040f0522090f0b16110a05070612020d020309030a0305070c0c030b180d0e031002040e0f04030c08030a0e0105062704022704020a050103060b 79
    0x1340c1c3d603041050b810072400701030840707071a201c90005a500d60003154000c600a020050b560b50424100287c00c03502c5811017030060a030140741840c00e0750b0000b20042011414807000521400515114208810003140038082070046070600100390310b00c005071601c80f44a516074040d2001082211a11072280c0b02003e06a42c0100000f0000d06015001c4034400203044200103150401c1c1100400c2280c2055030f0000050740042340194080e40c00d403007490342020b110b04090103102020707a80c03038001c101d4030b000041c10703c010b000c041540130f41c55608030000c020410007600c810481d110700082002c40040011482489640b240892402507407080b01c00359035002207042c4040c1d0b9030f80c0e40501c46e80d0001d070046080011040e044c43c0401c0002028500603d5a040c01003280c1d0004141300342540d00c0036082a12420b50035544020207200d00341d1030144020fa00d040e80c00a952180002503580c1502d4403480301c03c03055410003100300000c0c1902c581c403480c401c03102c10200070340711740044089620328000c40d0405d0308 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 30738045 1250 30736795 30736819
    0xf05090402040c03020f0d0e0607020c060301150504170a020f0604181d07030305030702070b090d0b04031103041403060a0203100b1303020d0b070e120601150201060503150402090106050405 83
    0x502d5040b0545454090401503e0034540300d14110b20b0354000543c030312005560700c05158440e0804e00c1140e0300b15251b8402060040c035103034001005844188101d9444c0c0e40c00018000403980141700b030324010600c43d280c0d903906507004140d19071120b2801004a00c900b40a0141190900d0218140c401351a21241448080301c20713950942c004013100d2900070112244583c0d050b0f07404100b0011100070718480c1d555103450b810000406803610344190041980140c05100154158840e40c00d00326649402a0303124106443c0ca06044c1e4000e803400f108008a4000010045249200801c5944202d41e00750100d804a9560085201c200d00040c1c80114400440c01c504100a10642c030207040b0001203489070074840c956a40c00600107100d44031013265400c07500c1080202c05a0002c00a46030250f06a620080341031007107a003d134442805000b25110a0a918031002d2040e100350b010401601d0301900700d401c02200000a9070702d1000071141244192142400490b10034820800c1d601155000f4050700d007400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 30739295 1250 30738045 30738049
    0x603010f14041b0509041503060e0607030506010203180609040504050f0708150a0b01140a020705040b030d0906030507030605060c01090b10030302060c0a111603050f010603050a08030606090a06030b0301060f05090402 95
    0x15005c00510b581c869120308518951451541c8200002d5201e00e50010381584c3c0300c04121304042c00203258100349442d2000f04045030340c02208964ac21406280000103c13400c0c2400203c0902400e041e154000d45001c0821040103400030f14120409041412684060f0b03940302d901d0760721220380d80891000903201001c200c034140c158000c41c00c0c0e02c40504000c0c4080c10300e007000c284181c102d0300b01c610060303010800402050606100300d00700c20400b0f034090100b0300d084100181071508140b10300ca04041d501c2000900d66071190303210101402008100d90b41e01e02015800501810f4103034402e880d40c9a082c0c01007000000120064011a0f03815000b0f07180c90307551720810014079006200d080080c05080f010304a9080400c1c418043c819400700c081400280c11402c02ca440d201180a840d1584c1e80760101c144041600010514103c1d50b100c2c5605581356114000f14081d4011501403e800c01401c4c0004180c03260150881501d206096008000242d62209081803101c241e03c0f03480c1c0c101e040100410054 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 30740545 1250 30739295 30739297
    0xc03220b0a05040512010b030a05030405091324020c010e031314100f21090b01050910050f13050702030304061404080d0b0414090703020103150b0406110106050603010f14041b05 78
    0x403013010400001c3c0941c000e00801c2c1400703102c9d80111403682000505006520f8010403480c0c02108881034484415240c0d55020303400e50784e4600045044a045072034949000307984d011155a00d51400003407007059040c4c0c5c0d5180d981d4104821043d030788014040c000c120035072400f181c2700750080014854007440300c0c600c1041c3e81c44850b010070a402c100441c3e2150103101c5d01000d01d04030076003900300005101300480c28800d180105c10b8001b5882079100500740206503144080c88407c0e15011602503041c2910200000e007802d005c00d840803030180c2000d0422150170303004000f84d4440c5001d010144020b815096007000c0c10a021100101411024001e03440b0114260340161005c1c00058800a080c600e003085100c2300b88811182c185441e404610148115645401400310003501211444c0340c0c9414800c007800980168003821041121310104141840e400b508400c009182c00703000690350307503102c040502c001802409039802d1981e80045911060600c3e102e0f0202d00900e42445901001111208442c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 30741795 1250 30740545 30740569
    0xe0102130b070c1d0702100b0901060f1b05010c0f02010902030d0c06090501090804080d03050609060f01020322051c030e0108150a140906030703030504090504080c03220b0a050405 79
    0x2c42041810124004d401c11141c1c0340d41000d0040302c0303016440c10400003403400210003100b40042c1e0411070454840d480707000f2441d0640d2407600785241211785180d01114190308c103110711001e1142c8034280341e0034800190300c03203440121580c1e02c40d01b5081c00d89006a0a031101e002e0000d41540c000c85204003c02d203c3d1801080b0944214170104000280362600c0d42035606101083d00c1d203210004080008035401c000740e50700d80c7e4a608090045140240000e0709003100208074074011581b050341c0c200141e02c02c0c005c4030482c0380600502007030100d45442c240e40c03e04c028040d80f4001c055040b4154800a804510704211542c19a03030b07100c27520564001110b004170301420300b2540e0004914910903c1c0c0d80d01c00c1d913001500c4412080e1189034400710402c400c0001c05049103000e6086804188040782e480400c0380c2c03e440c04410045040d403102c1c50214454840c01c03070041c505c1c0c000442c0079090300000e0403250f090340c0c111721a401c5c0c0c06c60300d5080d661124410350120700045002040304000d00e05099191f081 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 30743045 1250 30741795 30741803
    0xb03070b0403151d060a1a0303090904240b1008091905010e010f050406050606040e0703020703020a0b010303051b160515040302040212090f01050f0a0203181c02010e0102130b07 78
    0x155451000d45134500c0c00c2d40e2858100d107a0704144100030b40c40c8241d02c41c02544164000300310608403c0c10300402c0c0ca9102d040006030042c1541070010341444210808481402040700d2480400441d01200400500084001c03d103e1540c151000c1002403160000b0350040071020080d0107040702420a8a9140326602d50440c0c183d52294140e5003110000c4c810310074080c2441e50041428501407420000b02c881c001c10141c0b05180134031090204a0f103403408154070400b5800c005030307180441c2c1004e80c94080000d9009041d0310681c0000700405500c18007401400450360040919125440a0152035440c403400840e0b0300112542d0411592901c201100c0710950044a414035003900c1c0d0b004502030b0381c0664070f000a1181507405200c008001000b00b403030700310365001c001c204a080c9807004075030000000d0716220800b60007002240031100040307510803024008500316031030340010703041c1c540c1c0090b0600b84420140d4030b03081c00380c8800e010600894449002074081202100d0a2459040e06600807401c152 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 30744295 1250 30743045 30743051
    0x303100e0411060c0705010306090608070b1608040b040503060a09020907050702060d0608030406110d02030a030f0b0907120605120304060c0c09050718061d13020702041a01030b03070b040315 84
    0x1200355210380005080440c4c0301c0e070151a445007014005401d6484581c80400501e1030710604111010020403080d066851001d6925a507a1030312040303558450350040094071003500018002509188035006000701c840a40541d03140340c2d9080c0e1048202e0700c245001a420034181c1000420a82c403640080101034030050106040c4543d001440040f5192a00b2044143d800001c050000540025250080116200013001c0081c11040c000303449000f800c08900615413920388040310002c0940100c2090a0090f0200c0750a1070403600091010000d601201304181c0381c07100c00700302e0b802e003c0d40001d0300b40700c420000c5161503c2c000084440c80404001994201181c5030b01083c510f406008050140300786903108680902e4644028140a100364404c44c00d100c9410f0f0008098a1455000b00c0400402c584ca10484104528410040e21440d08020342c0f1a02c0d02c19400101c602d09444c21103883c2c0c0a90b010010102c0381000d265403580705005424800c003080c84200b0009950401e0b614550410b92408 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 30745545 1250 30744295 30744323
    0x4050c0f120a0b012103050904050a0f02130302011112070b0a02160b040203100b010806010c02040b03010f0912030b090a0c09030c03030206071e0507031d0d050a050607020303100e04 80
    0x1da0a01144600032a451880d103030041080c2d00783c42c1203000300300c2e260750003248a2182698014107103100e0750030940d00464441d00040c06c5000c00741c2c0006a82c200385d04c4250340d58030061716604100300c503d0200b05e0108200007802d505d06e4600244040c039040c5804141031604403d80c54855802000800b0321240b01e40802404c428910541a07009980b072007078120020508062040508108455101680f10b926040229440342e9101551030b03080002804c0c0035a88100038004240035259883c52b940c1c04d0760a1145170b5151141320751114030740da801852107214480c01c8940031000d45503800388096100782050041000158a58446881d2140ca410704210076941c0365124160809258400c1d4050703080f6104004203241c000310420045a601c1140165150450360045d00d203000f00c90018040008032903003248022610b850460b0100c8004000306a504524586183c4c0c070369400f182250340b4043c0001145505000009890159041040c030744941403d0070a5034103883d00007002a14a41036103949 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 30746795 1250 30745545 30745579
    0x120a0612030507120302090901151403070c17030708041502040f0308030a050a050103032712080c1603020d11010309060c0905010306290a11011e0b060304050c0f 71
    0x900319000d4441d032100364071a596410010a002084030f880800c0c18010000c0c600180d0304d41c0c100750f055070085603103002801d030002001c540c1d42201000f6510082c000006021360f881e0026a4074002510603890104200e135055144011408140c5500021941f03000204d800900c04600d950401d00d40780d800103003407558030841e110205025034425100c90381d00000f404080059405010b0380020303c050240001d52450b58014604d00c3d411a42ca05c410000c020030300840001026454014100c01d0002d0055080a0502c589158003100c6412124465406011503d4604a84540486e0303001000301e00c80546940300d035403040f42c2e1800c1c03040c109540c403c0d00c000007516601c60100810040d1340c800c1c1945081c10b0026003100c0c202d40045400c60303013812400002040347c0c0e03080400620025101516040d96a0341a11035500000c91100994204042e0407521903058940c4081d80030300b00f20070b2044801c0b060a0040314170065402901d240c1011484030b8040c2030a040440c0b40c141d0141012499001c2420 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 30748045 1250 30746795 30746819
    0x51e120703030504020109080610030602030612070b09010f091a07060f2306010507081804060f09050426070201031109130504111215100510030e060c040506120a06 72
    0x421800300703950f941800103559000e20000003901e0650018017041c100402100e20070410f602c4020642030300000054490b0300c1d449a1000b80d2051081241e54032900d458601c10b2075001168014001103845048108440c03161a802c000c50301040205043c01c1e03400741608409a00c82c00081e506191a0012068010211312950310410300b180009024400c24010055074008054034180c100078040c098a000704a07004120b0700b0b03140c4168294a4068428004200648500d0780400e40b010811540000d185103190006031050748101c0141070f228903220741908400030041541806610240144001540280d0002c168403101152850504071214002441c4042d40c030880c0500d940ca80d0103000400010b40705030413004d1022a50300000c0c40c030b10b80c1050381d0b0310b01a50700700315843c946a02155181c0c0d032540d11080940405040c100031a0322004004c0c0c01313450640908025840307040c0c0011030300441c0070700b61000d03550010811864041039400c008a8140003620100c860341d910000014100390700300d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 30749295 1250 30748045 30748057
    0x30507020402190c020102101104170703060501080f0d0c03090618090e011413020f150712030504050f0705090705090303090a03030c05060109060803041505070506070306051903051e12 81
    0x350b200c1010344ea50b84002410400b506070500e01c942d003031401082003481c0726815281541e42000121509008829900c1d2503c0072a0344080c10702e504c2c3c50004640143c0c00300b60170188641100443c0e8180d00d41031070498041c80c40c40c1001d40002d102c0441801713460f1040030880341c1142030105885e0250b0b00d603494502280c0000c0151001a99105c064440a60310030b440720703510941ca4031100344201303c3c0d6004a03842995200480744185030001c601c5240711504010341e460107421221141d000007003820080c0081005640940300c40c4550607480e1000d201c0001c1c5a0709a4002a0011260740ca6641d000d51740b5421141d12154140401d1020420305d032a0f000010000b903001ea514004005400c0c14424101241a00301c020030509100091105401c000101e50845000c5005c52400b20310340c00d0300b100d8601a0310001411800707042c0074440c649905821040a45008580d15200d101c401a00a20601580e100060182d0004450000c1c0807031034025088025510f9429101d038030407611130218066100c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 30750545 1250 30749295 30749297
    0x80603010f150f0b0c07030303090804080d0509040f0b210f0f0d08090a110904020105071e030905010f0903060902011106011701060f21031202040608220c0303050702040219 76
    0x5182080341080601043c0024200c807041c0a00e840c031158006511108907010207010705031a000f400082000d00012600100307000c40c182c452001d14144014815404010050700c43d6081c500b881c1404486403090607201580181800701d2500144003003d003440c050403400c1090b000b4401002402c0e9810301440507242601d401910000140e2040544041405081e240e91580442a8800010512482900d900b40111402ea0306640c4510040b0790318030032030360000e24400703000c4a0b410507000700c14400f50b0114030035147c901c0f00a0711a40111940d00002d0100000245a076400b040456a076501407540c050040c940700004100f14800645440801c3e84013050980300325074410100b640c288030761030260221b01003800003a450032200304400b00c8090045110034900103807d00405006091090f0b00d00b0f004801035482c2c66a83d100a06042c1007200ca001d08082e180404600f01e0200740b045000d1168003c0c1200d003400d0035624202e5660f01b2140c0100c2e0041c1e03007005840804242100380d06210159 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 30751795 1250 30750545 30750581
    0x60f06050904060806010b03071206050607061d03030c120a020405040e071a07021011010f06060e03010b06030603031e0c01060e1e0f010603020a020c06030a091a0105010f080603010f 80
    0x79502404216509030380800080e41200300188421280801102e1f0019807500d4000c1840d81340da5034840c02848203074025540070600081a804000550700145486507402d02e01384005c0c215012440c0d2240b100712015050840104400e12070703001e040030000c0d00040c481400504054a650101d8102c40c49000301003e19404101c0030010318000301da07422104203002c000c3d642031029030750100750002082c540c85420b001941c41c40c403203d6202580510300f90880b1420038041e580d034600d0043c0002030b031a040c6034000c0d420406220300c1400c24008890007004058011840c0032060803595180281c50341c010710a201c0104003c501540090146101600d0482d11200144c1800e0403000310f407851994a090340c2c0c50300c02c000c0103200018058000e04403585418050303919026240104d090000e07084e041c45c0c0c071410100500091607050741c0104009403003164030b4180d410f04100b0948890f20244140c900241340c0003451180c003071145003144d0304841d001e0000f1030078004000440c4280d5018000408102603 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 30753045 1250 30751795 30751807
    0xd060504051b13020a0c050a03030203100605030c04031205070605040b150315040308100b220b130302041107120201140a0902090408030702031b0c03120301050f040b04060f0605 78
    0x5800d01021401008141c200b5039181854004038600030f803803d40700a140ca9000c114012000c0c09102c5011103142d104081e038000c14a02c1c42c0c098001e420503603001c1600c943e030301c1d8003217143c134001c0084902604012404906191a42e80c1c0c2c590b074035000c0901c01d4108002402414009041805581d014601c2172240740142e1818804450514200c90000761003640a9810303004040e0000c02c0007504140c0500e8a0349444d40c603402c26009416141c0d1200484c0c420000d80f01d00c07240e100410400140300341d040780010941d40c80030040464005d800150603480d010041c204010f2406078012482810106544ca0030a40307592164807094200414042c09030351a190fa5040d41c1d140e0410055008240400800100e51550007080701c1c00d41c020002000c406c03000000c20003082c0204140c07501414440704a090400c0c0001010707845008901e02240a441a03000b6244070003040340641e8142c03100501440d201c00d0840702044082c00514554a0f00517039204030214101c40d04401c45000b40056403201c1c0d03980e01d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 30754295 1250 30753045 30753053
    0xf080307060506040209090a1116080306040b03060405060a02090a090c030c140309030a080c07020a0f061e050919090507030204060905030607050a0c0303060806040c03060507110c040e0c0d060504 86
    0xb5000401c40d41c031543c410403070f0b5949541c800c04440d800148040700099005014858180d03035100303c3d16103280c80f003420b41110041051b1000254419041030714184029440c03001415030310348040c0d07401803c41d085040040e419020303644c00b405050360010105580c3c2d5603605003d2084401090540b00000c3c0c441e0f09003188144c00c0008903a405459044040c90361a080e6aa0741e142d00441da0480304000302c06000c103006800320300c1a42e040030740003401c1341201a51030788401348094041c82445e002c01e446160f020189185403040720350103d002e84955181510001c00c2018400c2c500700181340c107240310030012401e820b051141920a0030079840c010b984074100322014094016650010348070341e20035000c00481552000c2654042c1015080416200445150560250000b50420348540c401d40303080100b4001d1240c8444102c078040c040400032600c030b0500488400c09441c00240c03199020700c4024441d0700301603200d50221101c2c0d106031025028444002180d541580b5001c1d948251100d085c00284 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 30755401 1106 30754295 30754301
    0x2406180512010605030d0305070507021c0c0e070219050a02060a090905190b060310050603070201060806010b030a150e0705070f08030f040c05011b02190f08030706 72
    0x60781844a40354000e2416110380340c4648110348000386414000d1240c540680d01c0e41d510246484156001d01041221004458010b240c40c0c0c1050800b152054200501800c040d181e1030b006410403510007443c0c0108801c03001029585400680001400041e60401031a0b0590741282c035152401020f40d42c15145038020455107062908000030020300f9480b1207070b1036400310307000c1116001c0417061006a000451307a1812072603003003c00f48845c0c030f0709101840e07004c1028400810b04a449000302c1d03080c4182a880f01364034100100c1070040144488c01000401e40c01c0c070141c4910145130008414122001411070800d1000c006000070a01114004802442d5005a82e80d5584d042a6034080c107038030011181a16082d510160101e05581300c2c200d0042c0749400042c0d80300100d40c03503408102001c418003105101d507940300c4100051035182c3d500040024072940020315182c80141c1004000d03 = true := by decide +kernel

theorem cover : BRFrame.Cov 30575545 30755401 := by
  have h0 := BRFrame.cov_init 30575545
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30575545 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 30575545 ≤ n) (h2 : n < 30755401) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
