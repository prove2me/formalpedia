-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0595
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:38:42.459066+00:00
-- url     : https://prove2.me/submissions/73340d55-8cea-4ad1-9b12-d986b04b7119

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 106834532 ≤ n < 107014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 106835782 1250 106834532 106834537
    0x324010504090f021908071d0a0506090c0705010f020d1b022803090e01060315090207030203310f080c04091e02010504090218010801050103150504020f0c01020c030403050d05 77
    0xa8010001c03c11680303403035003008919007044001185400c034a920200b40c00a0030806039005e00451155120412000448400701010040450b42003c2c10041003001940b90b44415940080001075044c0e02d604080c0b9050340035098410078000708610108043c5459813040d00a0004000f80c1000346044034001c40c400c0b600c94141030580352000300c0b07403a840070091010f090400e041e0303400380c90640100e580710252411049000e070300090000342c55040494400d10310b481500000c103079811b8110310f08903480e68040c1d1240a07030145c5018050a403008440c0c1c030030898100c42d81001d401e0403107018454541c522225a1103881c01013101d80d100d803008481403801c1500c90b507000d2640041140300f0191804258424282159400301c0c100402408001204106400904001030504c201220880e100c9000181907450580c01141054145070b080c101c405005543c5400f82c4a040d103001d0380c6d40c40c00402c009600c0c8101c010b900308030344c40000c0030308588001002038420b4910901c02e861021090302d404442c0c60 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 106837032 1250 106835782 106835801
    0x109060e160509060d020d0207020f0d030e130b03030a0215090703030509150c0613050615130b03011806050a062c13060212060f010801061b0609020324010504 70
    0x128079005015420901840150040c108010643c40ca0442c4000c005411303a0013600c901c1000030780200d051000c601e01003800091000050780c01785500d54903503c2c000d180507003680c41540a03104440c0c0c02101c07036546800040c1c8020340501180c2e82d80036a034400940d2421410002d00c0d04404d10b01c0442e1008a0201d00001100e41603540c0130306000c3d42c0710400c90803510700400034190750010000700d0741c819010700072030784135024603076600089c5541170810909000700209000d0030a805159403884c1765490680703204c01403848060000c0c40d00d0041020900400b0180c0c1e0b44642444d144500a0800116070006441400111000d1111075070301e101484019140d0b266000c1d200e41c400940e01d03c003120f94101d55521640800e015401b41000e0380300c004c00c80e032001c440300300c0b01000314080040c503060840440c0500711007880c10180e1985440001031000f0002c01e003003d0603070742036800b140a101140d00050302054000f401d560310300c555001500c1d0b05101c941c4050226444503000044c0d05d00e054032402905 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 106838282 1250 106837032 106837051
    0x1403030f01150509190302180405060a0207120c03030e0f010606090806060d0308090c130b212a0603070816050a08060108130f031214090a020111030c0f03030109060e 73
    0x1005130b220b04005070b801072004910114442c0c04000805603584424a100320355540d01e00044604007418290b0070080e00512070314106004011010024203030b1404400030a0710b504e810b00d41d0408030300d0300724080c1c0700110040a0501c64007440380002d0700c040d8000000c842590700c590554030b581e20b43c02c6813104d1003125956845030b42c0700136040101c0d00070a1400d0f0b010400350259120b914010000440c20f510001c941000f00c1d94038421034038030f400d001c17014030611050089076001918002d2011139940b200c40c0c0842e04a00c2c4404d1450540d00341d003904d850b1208500401c002d40300c0ca01404010b22420f002c61702d1900103c0f0b81d40a010b20345000d10102ca10b0032240707560f01c0e52107603030760401940c00d094040c02d000c41170000d40f0303009408160084411a41103100b60f6440f144003141074a0f000c04d5480341554a0340300e0307810401340701100e400002c4030050f240d428204082c89074820354900703045009102200046004030b100e80744248002000950503a0310a1004002454807034031202206542104c084c0d29 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 106839532 1250 106838282 106838287
    0xa1206050f0d031407111e0a03080d0e0102070605060405330d02040e160506040807050d03030e15040201140703020607030515040608030904050906061f030204031403030f011505 78
    0x4941418010342c144140241018a42d5880031151107031242d20015003624411072030349030403803146171041d101040128000d442c50b55a0b44404000355014580e84401041902d00040e850000800754111201c0451100f00071900c80e9840d0070a00301038201100c4282c41a031030100010300900c3d00707401c4501251410304160004900ca50111030410039122030f4194810311040100d80160303214011003d4030025100a000d0b080e40140b14014080c245070000c900c02c1c1d01c144010710501b0360000703940c6c0488108596902c419200c03400c085e40200315203043c0f45c0c02030250270a102d80103005110701ca40134174804c3e640c10f0007000b440640007506005113040100140c01c001c01107943e40344a40c015a030032001443d52103460803500c500080c00c840a542c4102c0301c0d9000410025440c1c5090701c20745511071002405014035140400004500b260070704c4c40c48050340c103071352803802d4000c1c17182c4d0686010b503511055041c1940d140c0152203950ba0003c4591507411001d8400110303582e03010048100f440d4405440d490b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 106840782 1250 106839532 106839559
    0x2030d03050c120702190302030d05060f010e0105090d082710050702010c050c300a0803040f0c080607080910060f0506210a02071b03030207170115030302030a120605 73
    0x7218000041e08504c110f2140320041d4103600d2060802240907071080d00110743d80c1942010075802e030b0748003d00003480381080c802d05501590304080d130006220310900c1c2c0755075180a2140080e0802c0202c0c1c0340078000700408903104200700710301011a525410161404c0307042e50b49010821611481c0441500001072081c00014019406a691404050b208106640c0d50380a40808540298107289000407050008010802040d0035080803001c0050340740054121607120340c071b0341e42c400d10028000401c060341924500c0284154160303045e024200002c281c60090401620042850320b040c1e503e00f049010701a801d0b400135450313101e40422140301000c0886244d103030400701301e5071b50804a0310102074014001400d4607602d0380f089483c03141c0c0c03000c00010f03140e00940c10800380a8400031203404071006914004d03c086500001d08404031440e0604800360104841c1203203002d0810310b04504c1180c111041c02008050300400036241500e495034a28005070b80e4500480e042c1c94451045640210405100c40d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 106842032 1250 106840782 106840807
    0x50d08090d120c12090507140306100605090312040b19050702030604110f06120f010e0c03270f0a06050901110d1a0a080a0302070e0702100b041506090302030d03050c 73
    0xb07030100010713007411161032200c20b4080701034455410040380c0c19048040180900c11452220309141d01c002c3d07000309050300d0511144000b00303a89004680510802048a203000d9504105000315581d4940d0059111a03a80b45800c440b50803000030318015420444010380f00c01d101e041a00c0180790000c00918041c2c45580b280078102c0741100380f082e085004500c080301c0d01d454002c0242a415048a03031000b01d03103001c0c105691044dc06030041c82d0f05800e0034083c00b52005039042035036003064007041001a401031039641510b80d00141c401c50941c5010720010720300005c00c040340c0f4814250203207006004954984d4030340740c00c940c0349030700291036544d041c0801001c4c21900d034040d40f1003000e250043d5a40c405401d0004e020318207940c0c07240140e5484003200e00c3c2059814016000200b00e0100d07580c07007600b07103500044d4607103900d032301c3c5804100d65078441c1044e55034a917003201401e11101c50036454010b4541c0c0b0010407035003050009074080d1140740d840d82000c038031911680e8481c480b41d11215040c0a5110401c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 106843282 1250 106842032 106842041
    0x60c0d030e01060b12010510080403020a030e0a030209150307050a08070303050d020d0509030408190b13020a0b0406050a1d0a03081608030a0203180f0c0103020d020d0504050d08090d12 81
    0x41e080a50750700c1502080c1d000081e0014000c0550040044079030350301d00000c01210204c0002c800e0100724000090000083d00001c503c82c030745601d030070a2134155440d00c010035440c80250b4000f82d4405616024000c00d42010740c0442041c20098090b41c0125440d1428010032400c0c5119140d0700e54004601040407900c9100508a41d5008940140c03906002c8442c0b20306a0b60152425006500001001c00401408016000c0d1b0b000c00c9010802a80072592201e08083c0c0c0010681c1d1074a07601c1c6003903242103644111102d4040c01d10404c1c150348898071050010b0043e0416881c031000f24030044d0074105250040c103980c40d600c0c08014081200c0c5c030f00319039a91449410411105a900391038032012000104a20061480b61500394070044e00c3e4601000344100400e80402e00c04001c3d0050028111040c40110b01c03c0c14064007802c025036208181c00a200c0280311b90503100e9082e40c0b030320301808100600820035401076040c658a9000c00c2d201c5204094483c440e0920610110b920b0508485122010742c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 106844532 1250 106843282 106843301
    0x709020a0519080115090308040302040203150d0308010f050306040c06030c050f0a0201020a0311030601080a022d040603150b030a110d0c0804150e150a1104170c060c0d03 75
    0x1c005040041c402111a9104003524480c004030b6104801481503680c0120180410307002440c06501c0c0c18516201d00c082ca102e0b602000c0e000300d03000000503801d40f8004d81040e40c102006004446181036500f4014900d920a0140030400500004001914940080d0184c000e0342c2042d8421880c618100060f0700400903510250700340300e400c0c0181c040324040c8001505c4c80d040c0507000542d8884080320020b044514a450100304c0e40d10038411310075280d07403040e66103070f02c10140800145c0c1c07464600c042294840c0303181c0448140c41211703455101c21310319407030241003103da041d01d0074010220042c480e41d04824184c01020140802400005c403c00f40301c0c0c12030f01c80c1e8480130515500d009000014003050b03886101098000c95503c50900003080181030f0f841c40e5081201000304151040303602c81c0d0761107054010385e03483c10214542c003041c0300380c44a41c1f02c802415451564950b8896444644c0c072031440c0081580141c0740904015071000742040d00485080081c00c1014064078a180603041d0001d00e80d412 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 106845782 1250 106844532 106844537
    0x405040911030304030302030a0801090603050c0405150a27020301080a030f03150603091202191704080f0604060501050306010e19060f060e04050109141308190c0203010b0f01020709020a 82
    0x4210704548080c4020005940030303502a41ea26007400101030f01c0741d5010f030300008126180c01301c03c10200b0004107040710458030448001c192030702c5089410740c0d06602d11010687c0610801c00029100b101e03c0c400c4100340d141d05480f59034403084542e040701240424400c07000b0a402c600900300010b481506c400c0d46401d00e0303041c005031a0610303610725107001e4690707045031000c84d5480054a0601011100d00b010407201d41c030040040e00d212030380078884800018401041c029405d03040e20a81d02c004802e6901034104542120a0051451046c543e1818161016500381d031900c40049054240410700906940f0030a0b2840f42076181d082220f05100d441115070010569100000b16008006064150040032682c0d244000c0b444075108220444206074000940149810810f1420030076107e90b06901181145102c0e52581c42d0b4200541c0d103200b2021000b0030700440004504a1980000c1c02c81c03040c80c0290000c10040051400b8080318001011055016030b204000400c41100241c005008155461 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 106847032 1250 106845782 106845803
    0xa0b041502030f150a030804050103020a031d030301031511030103121101090b0613050610050a142109010b011e03060518070f0206070c0605070537030b010504050409 73
    0x600048080ba041916903014059080c01800440781e0048110015075004a556403849071469031801100d21640c0f01d203070b042c543c01052a90403580240c0c410040720000c40d1115406c5204000300039142d40c000d00084a070024264111300044806100f1455122004041d0390715590031030700c0341d00d480030724070b05aa0200810100410f610040a01480301064410303966400d89040020401c41c5190030403d0b01e000c0c8501d0705e0b081104580e116814481e2270620f508003d0798481400078210f070491940384005104803400076000048400c5903051040001a0030388840c180e4680c0044182a1b499001200d80005c1c0c0c04418030075403030030000d41800f071a1a5810f002580d184d8071404180d80c80a540d0055181001c1c0300300b008003050300030f00c400d0700c2d40c6940c2c80988554508640080c05006071000d010389195a6200040c2020b4061011600510b17511045281d244182c0420300c40c005241c03196001c03014020550030354855009000d01c0910040503118141454103007420701000304003001c0c098807151201c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 106848282 1250 106847032 106847063
    0x1031511070302010501081209150901050403080a05040504060501030605010e0405220602030a0501060f090303050304051e030741030417060702070b03071d010c020a140913050a0b04 80
    0xe0300284901486500080b80f00d40c502007425040121021000070304920421039000d103680c0c0c104440745601c400364005d50320380c107103540100c40e0303409a81c1008014400000b0004003254200000c0c00855504840134446c8a407560011400d4498a02c1402c2c0400e40f0f0640340c00c5580740507000306a110290071180d004504802e0326400c19085040c0042c0c55103540003092040070386040c09000d02502281c2003109030741c91940c00c020070b031407007034807021b070402101001040c100305040c01440b25038272622000342c40c02c40045860f41d8403a40081d408440c503000800103002d880ca510307030310f070010700d156540102c44880003041c00302042c1c1c92800304406140070810000c101c2105612000c40d020441c40c00030030861905000180c60581d1641124000e040c090080000e0700350b1128154507551804500582440803240060702d40c42c0303180700000e6010040d00c0c000b040c56080e0162020780381c20110381c4602c55490f00c00403c0b585114000300540b00c1e07001084a203010a01c1100a56081803040103400e559204 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 106849532 1250 106848282 106848311
    0x40c05030112150f06050f0607020604050105030a060f030c0501112805031e070b01140603040807030e0a150f0c080a080603031213060c030b0a0504110403050106261203010315 77
    0x20410f44c18031440d50742d0340510517800c2000703401c4c00550b401d554552074005942c00244a5024911405040080000009800c80c3d0315400c400010180940b8808080e0b4891034488100c810502485000801d0100c2d6000c0196002405916200c0c08440c3c0c007011200340840c101c00780b40030388401c1d101803004000c042d4440c0b400c00744480a14104851143e101c19461418640c80c100c1a400320000d8625500028203a5561404590b0081d41c040040c558030302a130714041e071f418038980204981c019403442d000a80102410540c440f401d80d5640e85490780d2451a4043c1c500191150010740000010700c22624031a000d81e0a041c3c100000600312410715014066030406840103d8405201510340c000d4002049043c0c0a0300d0340c0d5103412705040c880d1031085004600f9184191052601c1107072103800c26041d0848500440740a150404024040030344c0b07689585501c402030000c0c45da03103038124132083c09002c200411b402e20441540c60aa030b19503442e686034166032600d046000304200785d40c2c06007580d0b40702c1e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 106850782 1250 106849532 106849541
    0x705121b010f051b0307060b0111060a0f09140c030706030c0c08030c0c0304030501021215010816050d09080c070b0a090b0a0201111207090e011a0c160314060105040c0503011215 78
    0xc0d1038004641e51b0480b4a041000d03a2440160175041c48070f0504180030580c40498081d500404a0900041c182d05080c2072001038803d4a00c00760151000d07206000700d43c40e020540c11041c91040e000c8854085d521803044040350b01d96610320001549000c10b01c0e0028052100031600464840710690406052090f060300350741c0244c2c0700300c0f000d07075000403d524114002419a0392280751401c10011034201c0c41c00103010710070014100054072204104042c7c20501600a07248a042005420080310800d4585046540d2200c04800018030440c1742c00a9441021b20032290310964a40d241101d0a02d00706606c0c02c2c942040d4040410b5548030000449007401c03641c0a4880340c81208105000c605000c1800792510180350865884e00c0340d03240052117400282d0080750004071103001020340e102c0d82251040c0c1410900c0d1900d00c440e82480703400005014118034409010164901900c141da60f940d010402111107600080340892800e000400c120808010002401c0780101c518100c01080180030b05e0454 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 106852032 1250 106850782 106850827
    0xa0501051303030606030506150c1203070c0611070201020a03081317073c050c060d050f07020c010903060e0309040c030501170a08040306050403120606020705121b010f05 75
    0x1050301e10101d50502d54180143c90040100c1d003010019030918002240d14490a41c141340c4800310700048094051000300a9400d042c005800034a4032400c0070040240400f2162505071582400c002e842c0540f400741101312407045505800a0042400503035042e25550307801000246854103481a0801149102125901c01504170007085d50b0345607246444081350742220103488054442d010000904203440200f5000c010040030080c0190340d0300c0c5031081c50045003603e030b00d4016002250407070302c5011503002580a1041d480400606644d0b50900301d98910903041400e00045142c041003000c038400b0b074004410340000005680c41c201d1600701040c180d0700c0f06c0c50b64400281e5628010412100070041a050204160300508258013103615046298000c80c04041c1005a40701c01040030580601000c6204400542d4240312031030341d0f91030203922400302e40300c0e060203116032107002c001c92000032507a52003003181c2201d09841c403111900115850040074194100b885410011581000d80701030780a0f008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 106853282 1250 106852032 106852051
    0x120103260c0c040e0f0606060310091b32130b1303060b032b020a020307030c0f05062a010b0307090504050d02070b030a0c090b0d090b010e10090209030a050105 70
    0x40c2d03107010007840200d4298611081c82900440228069a800400c80d0f503000392044030915140d40311800f802c09150310350342c8030700100303407400d000450500e181d07910f4545040d1040d2240342c1c070380c0344030100b45400008490300b5201c0c10b240080c20320303064032402001e0102c040c04154440c04803600d401100c40150b002c41d10390307070b41511210801c008101041c000c044094105401504440001d494507841482d00c64030000d10310a48101c401c64094802c009100c441d90700182180e030f03101e40d02c0c1449100002203004110204039004004540d40c02d081c01260b07003920902c0000280d00186a0303680040c807680241c0800d8554a4000200b42d40d9810030100015204c4240000b60505003440c1052804c442e85c00000c007503410030102000b014100801703a0b640821400000f242420351444200c0e60181c0c1a007001d8006400420781203114841940694503441c0300e000c08014503600d520349184901303812030360720042d95443c0f041804804010f40291203a110041d04803445d4000c50780d00c50f401e489041752121034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 106854532 1250 106853282 106853293
    0x609061a030d1e1119080301091a060414030109020a15020601080c01050306090c0c0303040303060e07090f050d080412030c021804020108070c05031306030c110102120103260c 77
    0x1400d1405124400d1401e1540c100480221074003a404a0000058404107090110307200d5400d2003c07400340803030101c080c3d85c0040900c5117103135450240000e4101f8050784550301d10700500d103c0d0341104210780c61000d100040610b42400d01d0412103048125000303540e1038065403110000001a00c402e1301c400050402c00300b06524119122800902c0d04c1c40590003c021603201c6088040c0c540d030450110381c0c02400c181e80104460750360b0840c1014621801c01050745900c80041000305141c0c1c07581c40402640c88980d007030f0405440d4008219a08011401182c900c0002c5d80c600304000c0c0703030248145080da4483d050460800340e44050812044816800075400300e00300160744011440c0003150b401601a07000d01406482c24107400081000f070b402042c800c280320101c0e0604041c000b04005840050306a002110201d42c0c0341c0000030064080d80d501d00300403130000445007603c4603043c02640c07110703a50300d1111a2160718507110324140c20000450b460410340c8070f40380075511031103144c020700b40c0c141c0c060002c24 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 106855782 1250 106854532 106854581
    0x3022a010e01090f0e0912030c071a091c02070b0403060b03060601051309020a030227030f0d02030f030709050d030201091707020d1202030c0d0804020a0806060a12060906 75
    0x10281c00d40d84103294104400c01038180a21404200e140b0f0640301d100342c0001c1380341d0703034140f1240c54085a62210000914044100000c50701c824005000203031042040380080c0e074110341c2d06022948152400c1000d07400003024106a036108101502c0140803510446066564440030172905034420b40043d613090b503d48040c50b1290508000d103a070020f00170718007586040205040340c0300340c02240c025103184c690005070481d103051190701502d45280c0301c89210100c50020b100ba04c2d407480c412031281c601070b0086003506a101180030950804421042e000f844c50300d64072001d094540d070f2008250400303200c40c096021406481d024031100c801842034000103080f030706c9402c14401c0e503051099034002d0340d04208102801612408001030110b46d100080f822030016802c0268110b01034031000341400d00c5040c0f9500780559010040c07a005500a8906d0348400c0d0316071f10302c9500d90380112a815017041e00c8610401ca07503110310044090460003600d00141d510b80c180da071903040d2501c280321505281c1407000f080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 106857032 1250 106855782 106855787
    0x1704090221040818010c060609020c12031e0c0d0e030d0e1b1003060308131706090d050c0709060f150c05060117070302030303090319180302040903022a01 68
    0x5103100c0e070104400700581c0c81c040d91440d4081c85443d290050180f82804040400d9010307a4a41c0300c1c65500c22028080d07a40c1358140303100250041c03c905402c2d441200c0c00c07030000401c20300849000e000465813452500c415004c400501c4040a00f2110a03440100000d4800098600c54800d03084005006140da45840d1040301081e41da54001440b550342109140c1c0100f0920320040c01090f000503030304440441c0701030743c0c1031300100841d130300c09098140b0015000c041c0d520107641e18000d41e010aa00000c06084010404e940c51200700ca0707007a49688040c6681c10f001e401000a4070032200c1071400c50303c0d001d46808074441514003649c00690074040c1247d00b070201084c500078010380d0381240d2401d40b910002a850b05556002c0621448516a01440c0ca18901c01f00a02040001c0c580280c1141d80c1c9003841c4140c581c0e6580b000d2402807140d824075085c1c501192050080800200e40c80035124401070460f02000300400502170700b00d0540c800c22079220725030607030425006917006c04e201030b0000c42c00031500007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 106858282 1250 106857032 106857067
    0x5010504082808071b06091202151504020714070e040209060103050403170903040f080a0b1e01060e041805060105011d09011214100e0115030f030c17040902 69
    0x400c1001d207200c01402c0056a0180345242d0040b4149088800040310300c90101c15290301ca500a044070b8140040c0780c0c01e2101510400e1542d1815600b156158001c000842011f10020794004c4130341000301e4100c10041ca040d40240512601941070382c4010320507910080d01d441d60356481889580441010807055281005405a001200b030038240b00901e8681da004162404a050304000d04001c203011820102c001c00c20349002d00709200581c0c1e1095261094195a0200d44004503400c1c00044006a4400c03241c80c1c40600e0388000c1410400c59900b0301c5030641c0e0708a09059801e03000344da1902c0101403203180c02c503686101c500504c041c052a50402e400140046040480d112014000035240030f5191520a0a00d044542981041d4039210f41c516000e28061a92100e1400c04e2040031800c503a9030000d41c0c000440907001e0350007007128828115030302c3e0858581c0d11001d0002548003e80101080c01600aa0380719441580c00c03201c100c00708003800c4401c0d0015084201500c1d0b002c0349601e10b58001040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 106859532 1250 106858282 106858327
    0x50f1818100c050306150d09050c13021204060b010329040b01050406020703030c020a0b04060207182d06090c110606041b210525080103110411070501050408 69
    0x148841c1c0d04401003d40f2601c0060142d50007440002c40e40d40c0d4044501d02a5220071040400c10304c0b0758080780c100103a40302c00b011000e0b44a59a00004285000340300d10864001c1100060344088956854980c14000c105074040d43c0d052640701d001f0000030180e0310103404030681420031007580d01c8c060071040c80201c1e002c1d01071300c605011080109000098000481000b125130614101804407250300c04260360019960004141c18404540810320540103d1a10180d40302440100035808407540320070103883c0400340c07070684803a100c0c100e80301e0f09441880001c40b5201e810000b040c903130748c1c8000b0380b0111207407661140b0026002c2c0807500a40c0070140700c62034211000302ca050160f03041c0e5080d003005812000c000807061010380380c41c82107410012300d460880a40e81c01010081440e151411541c0034211100d20941d400c01c0381210840240140c003a40e040e01d80010700340c00e52411400c2800001c05a03104481500c0e5414002140058001d000d900e11a0344240c02d0030780c64407503100042c41e000750001c0c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 106860782 1250 106859532 106859563
    0x918060b0108220303020d0e01050105090c030115110f06040308071106010315020313060501030503040f06230a020102070203031602180108030d0203061c060501031203060f050f1818 80
    0x107104248882d40040354448403101c025100d403025131310b8140c0081c4030b40c0d595980102c0c20540860714140e010b50259040b1070059581070007959410311404003d20090007100303045066420075200c014498800c04809039660001c540598942030005440e10301e04803403c600054003042003007503855000c0c60b1030714090368410090540754110b945070341c11101d0000b21311428560220024658944005400380800e8210208210710358480c10051b480358068019028612815100012790314400c0b00507042200c0d900303020701105040c802c0c0880b4aa0f0186045504540d000d204403005664280010041d0610030302c0e011881101d14814480c01603020803000c0341020803030004010180d00401140d5000d41d4003800166242c3d21b0000203034005803007141e0f141840b01d03488031840030801660300c00c0d41605c2c0a8481c0081c0480c0d0a42c0450546001b170007004c43d64100340300100194100b0311030f00303030b080c01d40104108041035868150100902003250071402c01180b005411340c4d220300c00d001140c00c004c40c90317 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 106862032 1250 106860782 106860797
    0x503100509070b0a080c03061c141501060c110a150203040302030f01091203090f17031510050d110f070302030d05100e0103080d0603120c030810030b041205040918060b01 75
    0x12100a410030340e0041c5050607486e00000001e04c50740d01c80e140710282402500101c0241d00240c186a1803003502c1b440d0581c100e00c103115070021162504c3c581c550403519030396606910300d50b00fa92070800c064158461141c010018001c0410b0b1a8444920000c4011407035000f5600d641c0366004152138200c010809040c1c07649050744800100d09107640c0600009160300303003c02c03842c06900c0d1040500741e660401a0021000604c165035669007040154000c4a1038080711440641640070401c246040d03100e881c0c0464020800d490855130607402403408001d6483d415402c003c01004a0010380d4445041180181c000042d0903034081800e01c0b40507049012155500d9600d4104100310701019010300002d401d01c07001261141c00c01c800b6800c110301640e44014001c4000084000103441c0b0318150340101c011558420004004080303020008003140d8014a4a44160300c1c1c80e1a6802d800890900340346c20000e08000c003080d050030034040d10006c0c4011070409024101c043c10140222601c4459050411041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 106863282 1250 106862032 106862047
    0x8010b0a05100e10020a08030c0a03050907060906110c04050c09011812080c0f070b0d0b0f060304110d05160303030608010c09090f020409060b04050a080d021011040503100509070b 79
    0x1002003e8960b034140d600e07649480300c82c80142d1405000340001445900008100070741410940040c6c101500e8a032020b21554464004aa40b034250034004e62002484181c410131106214080c80103000c1d02020a40700401e01c1c10000c10300742d46080780e450085c00c2000461802c0e40d6030044100b8608101071250780070150601d01c1c1b0841c1e26000d064050b1480340d0200d000001c41c0402e0000204c10030b008001c5402440c0c0c0d95920b020584c000781c7c00c0d94615403400740956a03034108100c03100c1c40c0281c001c16071072455681e556404101c145600e840c81c4c00c43d82c2503421100144040080010b405a14842c20b40c4040c84d502d40141038601d2500030070380e943d04003000c8000c860b40040b00c1c0c509445000c2408190503a10201c100001d00031030380007100040c02c01c8000103d041c1071400901c103850302643d42c0c1c4101500c40a1441e07076018129001801070f8404c10414545041941c46007001882c03442070580b4280e500c000081c9070030a00d14044424555600503c10008420400c40340104440389a603030500b0078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 106864532 1250 106863282 106863287
    0x1090305070302090705121320010c08030405070506030a020c0d11030a211107142107030e0402070302030c0c1005121015020304030c1a07020d060b030708010b0a0510 73
    0x2840002d0244c03014501207601307580514161146140b0341000d90200d40703000340401c079000100550131703183c150080c9001880c235101c6807408210160103840c0c000c0c1208051f6250303401c40d8802002a61a40035a040c04146680c0307100c020741c040c034204400580c9a0203101052414005101c0c00c031018000d0300c00d24852002c0c00802600c8041c0d05608291410410303142c030361540042590543c020051400f02e1139412140100d0140411a0107070311015540e56030518015541c00f900c0c10101a00445d56050280c003080704401030110511078a000d00d60b202c07014010800340c0c1c121040440260300042142d000c4000100078030708803107808035a0810500308428000c0c0c1180b20f000d101a100503c4400020a0080e55850300c50081280c40c501c0c048000384c3e81c030025200d80103070104503680031070318100056220308608030015811004803020300d045015403c0005140103036030110349081d00c85580c800d0726581442181c1c014429140041460105202004088812600030502c101240210041d0300d99 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 106865782 1250 106864532 106864543
    0x8090607170a0605030d0504030506150916020a08031e060414061201090c030b010e07050705030423090a0c030b030a05030306150f070804090b0d030c0b0c071509050c01090305 77
    0x907680c441c28090764076041c000350007510369500b0058040c0b040714140300b1000d03804802032084a0044c0d090342c100f512030320924504035181049480c1d01ca00a540800c29010084010909104c0c560040351010420750703031071030074942040f105840d41c0301100c0002d9503880c402e8032005500805c100c0d000c00003800380c3c0008060707469014100c0d42c014110602c1c10b0350b600300c00754404020190440c18850200750b4070319040d41000824080c5452202040c40403d100c5030095080d190390341c0e8000c001d1804c142c200005104800b140030500143d64140c2591080ea03a12100007030381c0546490300c00801d05164850010b0191420030300301030300a92203002500081a404000d580e00210110b0b400800c3d001d01d0381c171082040c0100c41240b644550001000010450042e00401c1160325440d81400b010812500b000200b0f414250040e010a080c582a02c0000b481070301e8442c1c0c0300102e0303038840e42000c006844080c04001e103d00802d40d61a80d9841106c14001d0402040000040900c0c019041c00d055549494841 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 106867032 1250 106865782 106865807
    0x90308070320041202120a0503220b03070906030501140a0909030e100903020301140c1c02041707030b060a1503020a02031209061b030c0f130b040b03040308090607 72
    0x1580e980c2190300320750008109590050031209600d0f80f02c9072501d410840022509034100e120390001540404020008241500c299411001a5080242c106540408500e012111612000c0e60102c01303e040ca0b0100d02660046960760f543c075460030304003400078003281c0c410381013a8003201c0c0d880d0003d200c43d55101910000e0700c61034000800d910300c0900c1c0544681070304040042e03010518402e240d000550081031001200c0c006c4000f80009030310200e420360785420981cac0009003201e0400140e00303603d00021051200140c0c120006291650354003201c0310031403408100242c0b81e0007005040080c00070341044103410500c2207413030381c1c440c500e80024480a01c45c550100018543c01103003249501c3d000340261051000d09480c80b1510340b44c83c3e2111030300c80001316031607619441c00e0f02402641c00582001d80344a4544801c0c128600000400388007116001008080b20b44034a0360303c00700b46804100041d000802041c010790b6200e050a26014001513801042c02010380d001004001e0702c20f900c10b1450886 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 106868282 1250 106867032 106867037
    0x405030703060b040207050105040f0c060c0f020402030402191e0e0606040e07020109060207060209040c0e0603011e0b04030b0609130203030421020a0602061603020c1c0c1718030109030807 83
    0x3041195004c1406801401c40c080d00c41e504e45001c22042c00104040140c03013500c14003010b44119103940c01618580341d801e40142c201c00d4a16154401820315600954000340000e115a1300f9240c4054002850b014941051220981e0740780803428036800a51190302501072a00c40d0040d51604001142e031a014030b206407044400c4010103e0030060003940490151604080150354030403203820010065030150407403034003480c030b01b00380c410f001031182d031030603955540043c846450759285c01007070107240d1801030a00c20300400304134001483c5500100140001c5100700300c0b2255621703002e420031110300f82c01414000c08110700b00070f402c016a4007004403801c1c0c801d800c034444007040c180030b901c100c4101802d01c025040220380300d002c21419000038080d4420b10214928040c1c940900320102e041e80540300d02142c641d4407284020102c00d41c845804003000d0854a00780e190b11140e0341b9104a1a400c141400300748540001e103408140640714820124a0310a500912003480b56550040001400401200c00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 106869532 1250 106868282 106868291
    0x31b05030a051009031413050a0b1c0e0c130c1403040f030f0e030d09180603170708091804020a0609030515100503070602072402070e0a090b150102010e03040503070306 74
    0x4050152502032034040c941c851b00c907142c01450310b12800032415402901d200b13244407500014645e081608071400710003203c40e035001790250f40b81504082c14420700440311500030002c00200c0d5460b0b070074000740b145a14141c017088040f00944041d0040345017107140c4510050810400002c0303002902c83c0254031341d161510102803411408100c03051001e01003101c1d0305000d10b0401c1411564882e500b0b6040da11a60249910140890310480c100d0700720b4400204100b030b00001d4a00c00510800240c40540e0207007194520304000600000d003c840c01d095242c40c00284041444254140308011101500380da040c0600d070103040d03403511651404407074030a2200f95902c00000b800a101c050101c40144005401c94003501e40700c0e0800780d10761030345004015000107005000c00f8142d82003242100c01d400741e034000d440803e003005442c1040080050034015032030f8031000c500c800030300714502d81c270710400401c0042505500000b000a01356020319164909517401840184000c0e500824100e0072250310900024 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 106870782 1250 106869532 106869551
    0x501140c070f1d0603030316030906091403071202031201290c0d020f07030309050d1a0406020306040c08040209061009030606090b030f0f0703031b0c031b05030a0510 73
    0x80c54440c050300002e200749085000041d12100d54440d070341d503010510180d86201da6802d405e00d541c0340030484031450303207010350203521320000d002e6408a8030290240c480490703089034a41798075080084038110003480380c1c070000e00b03a01404151900805a14981d1003e14648000001119020f0304107000c6e11341040c0d241d685004904165004582c20410b40c41021600c0e11800c0701015154840a4400e00150080e007190030320108000ca48981075a40c10348420141604000600c1005030040304110391201444142c60824100e10200c18412807103460050fa0b40d144c404103010541d0500c01c200d00034818000f040c03100580c0c1e1154165880308003580c160001e041c09500c200c5000f0070960010b081d00342380410124121425400504d59440b0950442d810020080c4005649000300900d00549800c450024400240304480c0741d900b42c0d08200500c0301d03501c0c1640350b808105030203034402c4030000103000311001135940310380000c40106811405071501c0c003410f4882e151280c5040340060613a96a85141c03c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 106872032 1250 106870782 106870807
    0x130b09060910020303060f060c060703020310091514010e0307140402070b011d0c0c0c0f040207080a080a051305060c03090a0f0b2512110d02070303020711030601050114 74
    0xc03070300128010004918546001c4000c2c1d1207600c00c0c1d43c00c03801116460700c014040c0c244402180c0781c88815034010140381e5200c00c1d00310020340002d0326000080c944500d0008004500d40905102e14003024034500c01c4a103821b14003030a81f036224009506110b1002c90425203594049181e00486154004820411b1a43e0000400030312403480001e095940d00000131601c07032501c0302e50600901540040207000c0d2544140307585180184468040d0550243c5541105400d107030700d034074420071005000981483c0c415903503e0005d403c06040c000020b07248000300980c01c2124010340e9084070b68115865070042d402c1d1500740e1507610042012207180c000002290088004100e4001481e4100000c001c006109103440d840319032056880c0f0400c045650404141e88100c502c0d0400000c0141d15230401070042c804020014000f40380d502c0355581001d0005003d188680d0005000d50345c425039005030344100902e08403040240e101d0364075010347d0000005000c143d030418110398000554900f8540c448240c2c0c41c12 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 106873282 1250 106872032 106872037
    0x140706050c130806060a0b070f03030b0102030d1a0301060f121113090302060f090d080112140105150411090f0112020904062402150c07030e0d1214130b0906 69
    0x40c415641c0c2c601c040054205400b00e0841e002d24802c642c801c00c10742e0b0f01c3c8034842c190700038008040c107180c0d0501d903000b001034080e5103d88800d41040c0141c03402d01c1100c000e44000c54041c17a1500720395038088804803d4038176086c0b2503031020301403a0009140751401c00c2c212a80256110304001c14211090604d079519541d002449e85407008801010b00c400040382c41c00944400042d1240c1c8400380a10010078510380010400e4400c2c81810390710219542c0c030f40040045810418101a241e05007523002c0107041000030702660744038400401181240075901d1040c0401c44007031010503a4420014041024a40d44103100340c02030402c04d10745890302201e101c1c7c0c04030091180252466000f45031210000307170801d20030040030400d015400b6010301000d00e04016130f1900c0e032581c0100700c81c8101e4400105d108a80300c000e0898203010f443d10149060040d0041071080c0c4103d04140c400f10600107811440e039601c1101420000b4400345881d0902d0f0000a92810b0325460b80500d0840c041e000c1005901a03c0300003d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 106874532 1250 106873282 106873297
    0x20f0403050a1410050408030c0a0c0615140102030f030703050402120f0a0303050105040c080121060e030c160819140303190c0306030809120c030a1a0106140706050c 73
    0xb928002c41c01480c10700c0d100c0148001146841c01980c00c1040110340b2440b07a24407558003c0c02e4103195994103540c4e5203960f0702120101c400d0018074800750380400c1c51445401c00c4000500700440d46c40742081001c94642c0120042d0303a046520401454041800c1a400e0341c0c0c1100c2c95003804100b41d1280d20000b07101c0008508030141d07134801c0c002c82400202000459a03091800b949040103540d0302c40e014001038411104102d408134604400420603d0103043d0790081616140084260b1840c0542d2071801340c4024152a0240e6071010402c2c0320076100611030201d0307416a0906402c0300b50300d0301001d180c13589011804011411820303d854024085400141c410701540c2c017080c0e80c0d0300d01e480c005128070301d40c40064040e16185484200c50035036011f4480e0809072500800e120303040200000800081c0b031100f4107100003a00810070040c40750740b400c214100c455482501c0c0d15204c1c0f600200c180d000c40405030301030300400144042e04500c40304580116110b0070342001c800b04007503844480d80415481070a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 106875782 1250 106874532 106874543
    0x405040203070810020307202119020a02040c020d020703080a02070b040b03090705030106061205090109050703080c0d090b030403180e090f060108010c080c2107050703030e120d020f0403 82
    0x1294110101c13405d5001b10311840550325010341804001541c03070b0359450f6400c103505180d80048a00e03c4400b81c9c82a060f48401a1001260310308100a09102d1440c1c0807080010096804102c2c118210b1030540148030b00700101340300419210f0a83c400c025555469440f010f02005400502c03110094802e2000c400078000c0c000c20140c0d91503842400300382c0755104817001c031550700421101041519060181c80c080720926952a83c4440402c0c1d01c1c10002c1c0005000c003051503684080100c00180107001c03c01c000d5014425032034039456080007131420200000e568a0422030080070521001c07200c131b02500e41290301032400060340c0301c003f140e04603da51242c10602c60400c20b54100701c0c044800040c4604000c6a050036121240d9840d0700030b43c00e8603074810000c80410300c00c10002e89a05074940c0604210010700301448082c00820094810203502a40c04400040c40062924149605805280d09615207840109425403041d0700307109040c000d03407564000440d00065403180c42071810701510b010790b4114 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 106877032 1250 106875782 106875793
    0x1602120a0903110306011802090d0c030606030b01120305070b0603010e0105040c0f0609140126010306060302090c0306090406020a0324060e0603011406091507110a090e0c04050402030708 82
    0x3a0390180881c0958442150120071000f2040e12604000c99600c2c100c4202c160066140c81071075411401130341040c12003c1e00184030680075008206d5200805e0700850044200103549421800d05c0440c51005800c8203448003401405040021340c85400c4841998000b168500d0b41d44a40c0000380c09840c41ca40300791115800d100601c81840600d800a800b215a054454414982da07450b05807209642c6105212030198400b15401d4036501986c184001c4089020305481040301c0c41031f55580d01e840c282c0044c1d0300380e07035954002e0085040031003400742c008001080282c214941071001402407000184000c054580126003808254000d412101e00011581c0f01c0000b00c5940d442119400055031050000241d001d0348500380d5401d0034800c89040e54119584140141e00440a0005607030224142039040307044004245d0190304c11202804019104201a451039105041000840040381d00f20400c2c440c80c11001312209400069000004c200030349020403075645900020f030801e4880c0e8402812070140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 106878282 1250 106877032 106877047
    0x51c0e060d050a050702070608130606180e0709050606031807050301020720010f080a09080d0f021905031003020f0f0402120f070503010f21080c03070309091103160212 74
    0x10381c1c0001d0b210301c40303c480800099441034000c07030b647c501910074540450810004100f01a00c2070140e801d0f818020070021400c10341e5140001015040e58821540302d1341c3e920300305d0004401c10f0010030300604ca0340c1d030b007031080f410a10001852440060068950840e120840c400611403d0014500400000b4021074031807a540c2400c244291003c14620103410551600c1e0b005076000b02e1600020212542d9544001c0c2c1d100e00d0442e006200f2503e06450b003880c203102c011402c40315030190034070a40d024180903807a108500348820340086503078514414400140100100d015060a0810440b80c040342d5071401c0400b10008201034107262421710f5040b50001a580080303440d101d601c40d01070101420184002d80e910340c0c00311003e000c203005044076803518100400c00701e0001705100394020100c11464042403915a00c6088a9019801204254002003003623801c0c19046241d0300700401c5203030300070701080e840c589a41026104c000d1001c000d0951f248880d1003510301c20825000b80346030304e03550207599280 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 106879532 1250 106878282 106878307
    0x301090c020a0c0815090106080703140309211b09060f060f0f090307060302040503030f03091f05091e070303050a02071703030609150f1011100213080a051c0e06 71
    0x41808441411345c070003000c640041c405101301012104203001030007141c0d0035507443c0d00c119400001c0b440c04a220901c0450010f9403040e15180c8809041405000c410b02c6010303865080c0441c4c503401d18030f072100b01405401903880c5d140301140d000360100c480c2e181c41d00c50f0341c002685600452100c10310004c0c01054060a80c02c404004200c130000c210110b80b81140c0d1800100c00364492b0f07000d8140c1507082800b140d800500300310040c41c1c0106140091740c400812000340c0c84003801c41c6d80c00400d03100340c461041c80901d41c005d1000150300003108240e41a64402074200c240d503069148002020014000707881c000551090114001600151441d03012900800c0916642d82d003082d03c10910441c1ca050100e900d43c00c0030728210b1a03c0710007501e503045d2900803000700465094180d000300c06120382500c3c4990060b07810700102c0c0020008920068440040c1224888148007980159000f036020900240c0401c000144403050504010012034820180c1e07039007140c5542d070300440d09820600c0030070300e406806c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 106880782 1250 106879532 106879543
    0x311040e060f0c120c030a0b03070f140402091017070f170a1103040303290d02040b01120c0909050709050612060303040f06080a2405060304140f0d08010b0406050301090c020a0c08 79
    0x287c0e8031410300280740808101522010184102e0100300e41c4400e04020368007041c11111700080e401000103082c400c03d20007241d0010601c0d420741d030002d88503580404c407003858084044e400100a24015a0700c400324a03010304040c0003075101d094034040700c10000d1414401a089200d4070040c1c10b00d510313241c1c02d151030080c0161001041041d82140c0c03208160070a801c41d2500b100241c40024440782e124029502032000034000b040c240e070b04001410450151032046801512030410041d916610030030328200010341282c1014019004010042c3c1c0200119039a0500f500c8043d5092010f030723400b648450340000c0c03951107154040c2c0c001061440740003800a4101c206d0070300c0b842ca81581800300181032050310216448195544004240e10401807095040c41e01c060356029101c0d0484462131038942c8040e5143c407910300f080007100d40c005a00300c041a82d210400c9401045007280c11420942410009031243c04140116819156258a54014944200f20140507140c0201c90b499002d5102c6608a40b245c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 106882032 1250 106880782 106880791
    0x40506250609140706081003020d030201150b07020906090103050c130b09010303050d0b09070207180b0909030304030f020a0f0201030e0a02090c041a0c070b07030513060302040311040e060f0c120c03 87
    0x74004c4040c001000c50264605600c1480c1d40c4015001d9241190308014101850000c20340c119941d0318180c0303107454101c031a000701903d049003070541c0720549481000003980300140510b015044000041002540002c2c1d840e81e000300c1100d0004d0341d10035003241c041c002c203105800580d102c96040e00020515800c0402000c4181c00e88005018000000080c042008010b49842c40144c1c40307024100116194070b0b400204000d0030250101c0c000f140200040d400d01e80541e0b41200d1034100000f484101a0000400c08080d180c074000740502c03541c41e0301c0311001c01481c5800a0305040e291002c80b4039840041c024000107550041c500600e03401d19843c0d5031500e41081c0180b0b41907180c1da12003003203401030250555900d00c100300014040d640c20031000320400c0d0010b4a0480c1400030501c440c1a034035041b000818050704290b42d0060f21a4610309002240720500200c50b409a45003d00c94502d032240071424075440404440c0c41c180301d459421440c50148554560f00025115030400c0c01609000f010045004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 106883282 1250 106882032 106882073
    0x4090c1209020108010504051009020f090406061407060203070905030618010509151503160602011e0218090c1303050a120201060815040519050102120a02040506250609 74
    0x112048010003008803440004007a0110305500010042032070942c2085501c807401071401603400307a80b44590801e81e000b144020006400119900f41241443d10846006151034030704201c04080b10070b240030451080300c03030190140c0e80002c00907001d02e0085c2d80007401840007500319199490a54224403080c800402901015428140403c01d940310010301c0304030840821401504603111850b0b203542216803000c0704c41d0540a05050000703504404080c42008041640001c184034440f0806441d1840320314003051481032044c860140f40d0500744c1188a86040c06503885209502c40b244144254001c6014a0451040e450340c040104640803a4859100344242d6803081c0d045400b400507400d81c0e07894081d40009034002403024403440e08507031280342c0050160081c0c0300410641e11041100e00c86500060710140e4000800c8800340d20032a0305030790b020301c41400442c1070506107000103805c2d02c40c40c03d0000c03402101410340304039810f01406840071346502c600204a18015403400705214038004243e400f9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 106884532 1250 106883282 106883297
    0x3110a0507050c0a23041a0909010b101d060f070305030a06180606030b06031608040c0e04060e2406010c03090518071b12080a14070206010f050d0218130804090c 71
    0x10702d0304060084a401082d81f06400c1d03501040041801040c0100911039100b640d03c900d10186075458810043c5031501140da80c68850414012420680c038051000850141d00204600440c0303002a40a865010368103290082d540c0e2030380702c00702006d01002d030045c0152206a082561002d98241e0008040b1107550b03c09208010031141004841d000031121028040c01c038843d50034290b442040b02907805482a250f8a154680342c021041c4400c40850b0100c4249550703404918590b4800c2213961901d251190311202045101c1c2c648011880e00900310a0510180d41c01d1a41014001c40d0600060b0001600c0c11684412018640020000c15138008011400f0442c0d000d1006040d940403054451300048102c6d50300c441010b01b120000001003030a1000c0799209006680c90b00c081c1c0b44680601340550080440b941800c0c00070442041d0795009501c0303400010494030068542610744884d02c03d80d948801c50710754407071343e400ca03081080440003071544100080200e400c204580c09480f03139002540c0d43e100d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 106885782 1250 106884532 106884599
    0xe01060810020405090c0c1e01020a081312200109080d110403050606060a0e033c060a180b01060504060e0a060507020f01021009081903110a0507050c0a 67
    0x1049106a000791074100d10340c07100040b202c2000e00300034840e0a035a0412a24190105200890716030f4008e800c0c902540d4002401c490359a5000e008103402000240d50955406400c0ea1000900035818400106002c3c2c100c0c0c040c8441c07805044030107425a0304400034802d0300503c0c90222030550200d440300a86514140c0ca0b0301e1080d0545055070181ca40c413000904407901c0700c00400590f60005403810040060550101e4050b8a00b400ba52108120784c0400c40c1900c43c10000118241c00184080b00010f000106142d15503180055226006a0700580004400305540c44010301c1c0350120402410b085c240c1c900010b40154481d006000702c841c1560307002d525810000800c04254800e21800d00094030030b00844000d0701c0d004400660b90003050045400c042480509d010036100030007402d640024020840044541c0c01500010020300315240401140c645488c0140c403501070842740c0c4080210100b034140402401b04188042420001c110302489903031250044641c0408800c2c8015403411441d249 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 106887032 1250 106885782 106885813
    0xd080405120403021c0f02060c0102070201030f021c09021314010906120f0201030506010e10091e050307030f0503040f0e070e030a1709220b09010e0f06040e0f010e010608 75
    0x142e003036a034003c2c010340c0c10b030480014001e480d00c1ca0410545031000e201c5c590100603550300c0c008080840b441d40002d6200c2501e4000501107035020240400c0c0c1d640100200c0001000c094100c03078091426800018500d50341c0c0c0085250603d14040515007680b621502c0030500c40004000740c12111810004c1c0240c980303483d4002c5000c1d80390400244601042c0e820310f40107601a41206038071070313030602d441a5100c20407000100341e10020400c00c004a10800e00030320407540d6201c80e02080c0d845848200181901c3c20001c00d0b81c0d903010b8407028201380c218804150070009c081c01120002c0c84011820400340d905d0782d000c0300340c0d1a0150740c04c1e001304551085484160030040b58001c0090f411090080e02e54035642003038500c40d44a1280c1560142e41c0fa03c9c0d85005044941c000100050305600012b15480100144070f4002e1040c0c0120008200201c01c1000c50101c000100c0d0380407000303450101d260044403403e1450260481205580d55007007a00c0079466020552000040761840d1003103442102c10038188 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 106888282 1250 106887032 106887037
    0x203040b03070516060f06150507020609100c08031510081501051614030d0b0925032901020d0509090a021b03130503060a05071d0406080d08040512 65
    0x41441144007440003031641801100074000040c0b41e05480d840000300f544c0d03090100d8816001030400940d607880240300f215550130f807030b00b00075142e4140903141040720340010304c041c050112810720410310300c43c0522040d8450b6403c195040e520201407078036402d2007607411843c0d50702508003501481c10b5148501070188149a1b0340c0c00b03044c602c40b110780544404c0b0011141030b401110480d1101c2c1c00740380c4c4240002c02d0303400a00c00541112001d0f64649002400f0602a1500a80075510465201050020101c61001310340d4801c00c2d00d803c520104407800341d082d005040303a00281c18102001d50806108144400383c2668410800d07402d4581515420f2010b54080c050a02000e40010b00740c1c00103008244954014901c0c00e41202d280048418211402803039540520604042148862002c0126050801c6503035008107145505201914202000402e0b5402071000d158024400d0210481c0c0c3d900c070355000d880540f20010659100b03000100c0c000d0304208007a94116460b01c500040311000d04030742c00a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 106889532 1250 106888282 106888289
    0x10f030c0507020d020102160806010e0604060b030f130c060302030f10080a08030a0f0203090307050d0201050f040209061801060203090f0904170d0225021201060302011e110604050c0907020304 85
    0x1c8031428110150207201c5080129031089055111362024480c5025158a03000024a481001800a98102400b400165002502e070500880c14482c05008a41075901038079441b104240100c02c481c1c0d1074103001d4441418180c0d01038019107201e980030600a40c140c00440c45000c13048080140c0351580b500c0607050325160311038000b454002400f40c00002c0d032200001c1d03401032140500800c41c104100c844100700c0c1d0007176030883e035a580005424420030000307010790241000c0324002000b1625201305c2e05122550700500081c03042e2061300000341240d4840c01000c81420410480740745940c0c540001a60701d90005c143c00348103031541549020103140c40c00d143c6100b10f5100c040c1d901140d01040301388800781c122020502032540c090180c1d04554451101e250600e83c03401c6a08840b54a440c0180801003611f5140d056003039051040900251b47c00142540903420955100700b203908a51b6001c4800700800e00f0113000d01d0080d0002c0c441884000116284010822152450503407640181030345e40c2d110740d11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 106890782 1250 106889532 106889537
    0xd030e04050609010f0605090f0a06090e09061b0f07050a0501051009090f060e030714030d0507020f0d050c0304080105010306020903010b030a201f090807060207081b0a03080f0702010f030c 83
    0x140c086c0704151040d4080c084000c1c0c0500884186090103000805078462a081540003400c0d03450104000103462040940003500c41b4054109810401810758040b0303174100c400e10040c3c60014443e904480d0b280d0444030580d4003e02551074450302890040c1c06131400760784910341400d4030507001c500001c60748151816294807034860f49443c410b9555160192203031201544003800b09005841c08a19a50002984400b24030f0185669040c08800203044410203480d107002c5601a5013040403281001811500c401e82c5820100e4071044203028035880c40c803c2e40c20400d034a5003800c0000040007820f4002d4042080224001c0c40440c2c0e80400381340e6502200c1320003500c4454485046c041720103241141810b596806411001910007890108840104070000400060208031007008040401d000b2031026010920250202c10728040b0110380e02c00c0018481c0340905050800c0c00e1a5641e0740003103000560b80180031580b101c1e2041d41c1c020f282c0d041144280e0100302c250010700f0140303220b07100d110003e48068 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 106892032 1250 106890782 106890809
    0x41e0c051c0c050405060304060b01120501060f0e040e1203090d0c0b0a050a140f0403080a06050f2e050a02010c02010506011d220603200307170c0d030e0405060901 72
    0x42244a01074008800c0b00824450304020100b0152189001148142d0240704d012808000f5030000500007640c00b55611181450400180b0070164403507030042101440745041c11210101c200094001e0030907102e0a0310314419002480c1c101400079002e1131284410700d00362052806001010340f40c600004d00b00501d004d0f4101d00168070790085e9407002d500851001c2001480c0c0101d451100c44140040d5540c18004000e10100420542d20000480d402a00440c0031b2181d0b501d0680421074014403030701440d100e40c1189580720122407460881c80000ca8441c110400c143d510b082e0040e00e192f0014140b4001135090018a42203540140221030043d001a0b44080c0d051510820905007261750026041d0700130501610990011000b00e44104c0d510004800003500520318a07000c10200b00240e0094043c0407145c4030740c6010740c4e000ca003d0045912071001c04140e0a03900c25507500b0600910b0307103207a0107008029200107040c1c0c00800d00d2142d4005450400c001c2d1114010040300103002d1082c441002000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 106893282 1250 106892032 106892077
    0xa0303090b030c0c060408040e090a0c061b020306010b030906160507060b0d0f0615080f03070b0912030a051602010203060a140a0b040305060601020c12071a040302041e0c05 76
    0x1404010b680c0542e20306122400d1030800c024450030880151130584c1e420300081414000034580910a0b03401a420f4401012103012580c1d84400f0f01400c0d22404051282401480122109052840c3e500c10ba00406440e520b6868414004154000743e601f20780c2c512a0200042680122807010001003543d511620304054060740c032031000d01203030708201ea0040410b50422000a005034030300030580e4455480441c10288407419040c200d21154403042c21940704030b5044840010110862702025004060b40d40d055844a1846183c074612001442c9c030350f1800810485481010381c02580250072000074940f07080040c00c0b080f400e0f03000c160781d0658084076101c020001c80301d14003080b60081401038100d40030242d03103502d030106507080340e4002c0d280b6401880070402c5541e8103112208046a0489185410a51002d44c8a98407107407800362041e0070510200307400449110b50180c034000c560041c4240316103254031140305d400304004e444000c08582800130b540316042c0034000307441040001561100c0754441 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 106894532 1250 106893282 106893299
    0x506070c033c06020c150412090b04170f12090306070e01020d0815040606020c0a0e01030305030408030403020118050c150f0d050606040519080c0603160c060b040f09110a030309 78
    0x340c1000702c3e40c3c02c0e400c03c0100d1070000180070b450403601c9006841021480c00e4180000c4201c0141e410078200301c590740703041c0f220150b808103407010385001c512240c800050b4101034030300d4005824004000361041c880c502154000d140f004054000007501960483d4458181c26615504440c0c10580035070405521480c2e41440341701215031100d07084c02100c0c500c981407808902283e066400100040c0c110075403490607418555040d10090800c182403030860341c503589000f4520301002d031000b01110300000c041001d040c400d41010301129001c00040303074222140d141056640c601500407038041d103504824404800110001d8407030349811207100c0e500d01420a0038a200070480184500da000c0418040400c0315120246040e4980c140e40c078620700c80c181080704e00c610308800b1041c158402c09003001000320b8046406400f1100305414100080c0018861a1640203803030340e100032640152401c3c651003104440e542241000d03c0c05038a000300b51020310011721402a0b000c1c0009404600342d40010046600d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 106895782 1250 106894532 106894643
    0x140109020a0905041803080f01080a120512240406050102030d0e0703080c07080f010204060e040902011b0b0105011103070503160203031309021c1401090b04060506070c03 75
    0x810752808001498503100060119060b03544400700250100c05480700301900040040d421000382c10384010290700d4003c8050799054503410052412041403050802070b03000b00180c5220210a0000d078800c0d1410100d091032038810044e10122580b002032401109003842c3c4600e00a070b03a0180c0c051860a021861118042c200e11883c507000c0c4d01c00c904001021521910103058580840c2014007811440c01c140146000031075000c0c440c55910422082141941010004021807001d41d4042000320707084c00185c5144180d10306a0740402200c01d0810100700c1000d1400e8143c1e00262980140648010381250792806140f070000d01991080043e400c0086001d5040000180700400312440c1800c20440020402d50581c014070b0200d4021503400c0d80301448500303031101440101c1d81000184543c20041e184030106214882c000d0f0354600324000c0c0c1e07494980101003e848080c00301642c5a889141140160069120580341c2d8000d190f4520080500817980481d0352010150f00c0540001154141d100c15 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 106897032 1250 106895782 106895797
    0xf02120403180b0301080a0308090708030d051915050a0801060e0c0f160602040e0105011b0321060f05030105070804050d08090a0606060206040c15120207020d0f0803010306060914010902 82
    0x1c00b003141000604141c4580114082c2074039901410009059160181075500301801075402034203d080180501a8000b00307980e0445200a000305850321021920300080450300c4030340965030b08014081034103043c1c081581040310402e55a18691958440b45d1500f215440c2c06260480d43d4001c2c04210010000e03406000f101c81c10100f014030b45040c819543d40c038900075140843e011500401e040246c00d480c00c03100c0b80103080a08082600200b03c150fa503207000c00195008061044180d003c42d2203510045401d40c0300f42d00104c080090903110340c0e03505456101c610032a4402d609000c0000c44036803182d01d125004541c0040209080300c8050301c1601c00c0c2d44010100d060900c41e80c80754001166050240070000c0860360081e00483c24941080c2000c0700d4180c002200202c2401c80c69101254410100205000d690b030005894001510000301040c0035180d000d003080422158079003c0c8141840114101c91240c43c0c200180c503940c480392030a4035100f52400e203282c1c8214004005031100344d001403052 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 106898282 1250 106897032 106897067
    0x60a1103210115020c090f0405010e0d11010b0d03050405010807050915030f070c0506010909020d06020307050c06131e0201050706060905060f0a120807140d0804060f02120403 77
    0x280700703480001c0700400480350102901840d01e54010011003142030308501c1c0400039407019101c40c05096012a45280780074105100c05e10403440000c003800320a612855400e00500c00740c1300b40e000c01c100028400c01008100365030035440c01800300035903d0001c10490141c1d515840c0d45082611340b030015190032074001c00030007d100003000440e60030303a10781141000320300d5004070ba6510790800041641031107000500180501500c01c80340f1022a0300000e5141c115280c101e00419130321000e101048a03c90b23040c2000706074030b00201c140300035560010040e03c41200314504440c030990340c01145040ba154244005040c0d40007100c0b8034015500c01c43c1180e115a801810308615108030381c1e440708200d58061384040e030803c0e994814400c1758a0420801e08012400b00ca440c0300141c141008c80154801e030f030800030031614000810200300300d100d400314a164221642a90b90070300c022040685103c00480b802c440399440e107241190622014804d59a1000604480544503520703075500359010040150f03101c070b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 106899532 1250 106898282 106898287
    0xa0513031209140906060313171209060f071202040518100914160e060a030c12020c100906020409020d060f0801140a1802090412090b09060a1103 64
    0x222462101418402507114045442510006100040501d03100350800200d140c0300c62400c02d000d40d5603406454101e81d0460b0035603035030303201c4070501c600e600034040006145800d142030100d807200036100504084109000048001e80e00c0b035400984880088070185048540c01c808039204130320441c1c4c81120801030207070041c07901f40c568000407280400380301c0030320b55a1440360401c20b8000d4152902c07030040240c4042405210400b01500541c20001002030401300e01c200110802c407481008400809071000d8051541d441014100a0290a4104442001c10a0001400c1c0d8042c1c0314400c0759148191000074090f50300001e14901e0150184020640740f20381c003404080340581e01c0340300030100c00c000c410002642c60300d0701d813008d20100015841100e6030703450002401070f48690307000a154006020400007586900b040780c450310004007540080d4000442c0010001041821244001c2441c0240c891400c1c07540e903404031903414802c54119a0b005541801540140c0f8050703620076000b2804041601d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 106900782 1250 106899532 106899547
    0x50c1204020d02090c0d0c03020c03070209090705060301030b01170a080403030320042d03020607022206030f05060f06100c1502030916060201020a0203070816060e0f1605030705060a05 81
    0x841c074034015901a05e002c00c0020324a241e00d03440f84030300c1e00d007102c05080035400e2001030740e9010313120b01947c0f0001c3d001d2810713a0000385807220280001130103010003c000607243d5031031303040c20740d0480343c240181c8a003004400a66010000001030041c019036006101c00c1c074041c15036804a01412410100c030810001038003088503c1d910080c0500081d200b0212351801c2d001407442d12021540809003c280c20302c20f00ca00900258580d403084450868058601040203907001e041c3d1001c003080c980700710346143d1505c0404410042c860b8026807845000b501140c00d240c85510188100780410f542042c0d01c030803c078801d4110075019162210405d40903919000500000717984000c143d81c000c642010b400c1d0400e0010a0950494125400181500c0e20007181003140b9a00c0c0a5038134442c084026113080da0100e003040080d821851141c1e12958400340600207001c0b03290b26656280310300c48448038a40180744c1d40d203000030414140841180e600070014002036240400388030896206081401c1000810400300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 106902032 1250 106900782 106900789
    0x81605040b0616110a0509100306020a02071203020d0f08090a150b0607060c021203040804090b12010e07060311070b0c07050109050604050303040b010e0610120209040f02070b0604050c1204020d02 86
    0x151140d02801144100c11302c0d110130802c0c10340c401e40180f4800c29221003480301039400c10300100d0646e58001001643e8041141040c7d103812115485404c90901409000c42010360109001002d55032540f510062101408002d59002d00e045442e1501c40d0302201c00c0e840030600c0c4080466a005001b200025542c991f040418007990001000f40c4845032560b210030310403a410071141c0403112074091154114100b9903a605080c1c4103a00c18010b00549071205c0c06030f02c1e40d5110481400300080c0c002000b03101c1c203a802ca2a22212184142c0002c03e2514009025005c1882c08880c01e1903404825000c40f0f070f507103180d6070f9178942040300295200d41d0303294000800114108201070145000c2d0000719200d251038a030450701c5110581009000711340400c04c0c8207994541c803c514010314900c0c105405141090918080240503610b0803d03880744c14000b2a1040b0882c51340102052401100c1c004c02ca0b96400e030503c025a4003d507000e200313101b8104141c50400002c849040d802034801004002d0034030040c0c001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 106903282 1250 106902032 106902067
    0x20d02101412090c040c1b02010e04050103210f0f03110408030307020703050c03010c081515040b0d06150522030203060106080f1006050318010608100204050307081605040b06 77
    0xc012980000000f03001c250f60b400c2000d08044c55080340c0510240c440902c0c001c00c807038000c20085810300801d840c1d48045a0280a141401c414054400c02556a403410300e20054140c4013a0310388800068070a41804501c140060540c1c0d8410f52501411000310305022001881d40751488690301106201c04103800700f05100a60260841c0d600511400741142406030500754a10925482685001003203041c00e60040c2c03c80303602c14024894039408150507004038460f40f05040044c00b14010001e004500c01d6031702c601420134524115010095076444200c0c4104141d900700070710300461014821210045810b503100341404c0600b62808955a81e05d60120749800820b812140110b036524081061040a00100c580e00c03000c030030741902149240160182c0680f10140ca0700c113501c415a428041002400d420130170040c03c0c0d450495030100104804040250044d00400d0320a00444500041c24000019040d41c041d41c5035400751680351401c01000005c0075040c010542041044c81540146d422b503c95 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 106904532 1250 106903282 106903297
    0x309030a1a0106110703030f0203070b0f090d0c170f0403060c020105040605060f0d020603070306030f12090f0e0105010e0a080105070306080607170c0304050708071e09020304020d021014 82
    0x59500d80381d22600400e1041200c140c0062040010242061002c8900002c1445c201e0b5058284440b00021040302241580b04045010740f40c50401410302180c00f01d45d0100c20710618080055480c841c100c0e003411140321a08000150800c11420102401001144000c144110100403e1440c240d52503170f800e42509d80254846015035500c1c010031092103441d0064661161007120f040e074644500100062040d242940c020b402800040300260401d4000d5004801454200491041c02c00c46890101913800f44848400c1c0010250f400c0014106130141c1d1034000c3d1218111000d00503800c1900444a410390480841d9104d4034001000903a103000380308650040c1075664021910780e05000c0100d2520401078066803c006811810a07158000b01d4070560700080704c00c0c2c0e0035540e80c070340e42481c4cc5006040e411400060103500320008000c28240001e00c1c2000d5030214042c141035480341014100d010032203001e9040a1000c200c41c2c01490a01205025200c15041600d22400603003010062a04480b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 106905782 1250 106904532 106904543
    0x10c0213021309020702030d0e0f121b010302040609030f0f14010f0e0f0304030f14070e0f0a06030f06020309010e06090d030b09070e090403051e0703030b0315180309030a 75
    0x2403040310b4400464041016100a460a6140400a40c003007a43c98007804042000c00920a0910281741d680d195a075001001c0245204a403150400100380c451902c01e0030a0700031340e03078042c9800055000c2e0007610304480c01611020061807441d00d443c140214100740480d1441d1040d86881c00141c8a02c904410345c1c00d24070000203031807040904640440e1410f45088120f41e20005070396400600010841d030036664851030903a80e00c00301c0d2078154610500d009440d902c60090302404210301e0450103a8922825040b500c844007521058010310483e411400060030350f00d001c0c05100301141943d0011500300c2d030014000107110710111003e070b0900d031080c1d0f201480b60b00b1040b0f82d051480e52501403810440012299140751381407080018108601c1200061300404d5940700080c28140203100395400000740b00150750240b8809410452130780c0c0042003c502203031410780b21100c1400c1c00a1008000c803400d00908c6aa41c0b56035160519070048901822030b1880104441002034a0601c218080700d40f01c1c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 106907032 1250 106905782 106905787
    0xb030102070c05011112161a040503070219030305160212060c04091109030d0f050c0a0305030105041b0c0201030203060d0f0f12110715050714060906090d1d010c021302 74
    0x40010424040c1750b00c00a03541e40050301c0140700c020301034116403503407518559035641c0da0b0395803805000180ca1059002c800342104d03c07c1009001000c0000c0c807805100300ca014607100e0a081401003e5030050001500141042c030034100441030f0074800120300d87c0020104110200d9001c90145001030481c0d030301c1744820b40800d04004010701c5024801584020341c010754104648040466543c4200d0340d00e100402c01c0e08000340c54614000c00442e10055091419200c54410a08028180c0e034000e2040d14042c5d80303454131040c4901c90380041b03030350b040c00241c6d00d141584000b500118060341024019a50282d80b400c01040001c442401200b4450b218204130200700466040611891424114400500c500044c203c00b4003240801e28900740d8804c80c209100c01c0314608000c032158005c00314001c0c150600c138800380081e00d00002c0c410b48a81c1100c0c044455950b42c61140c0c0d030301c03101d46007141c1d404951075626000b1100e80e04000f0107003600040c50310454440e6a500001c241a01d0f210800903202e600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 106908282 1250 106907032 106907039
    0x110105070903210c08090103060312020604031806020604060b21062a030a020c010b060d0e0709020a090b1606020313030207050a060804081c0609150e0609070c060b030102070c 77
    0x103540b24a8540c0909010541070f214111030094510300300000024102400000c40090f181c4c001c2d40840069900a401d9052608807168065902d50081c0c030b061b00802e04442c82c400d03594502101031000d4941c071b54040c0803503840e1503a0701000f41c82c8810311aa440b89440d42c580e4803a0001e50305501d84000030100510031414640d41c086007142a0081d84146141000303411a50040004112500510318040040c0e8030b03e030300400e690050030f842e00031b690b100c03a000820405924081d0030980000c4442c009582000b581c0b880321408910501c4810070200f0306030310041000da0083c002800701405018803103d03102c6165070310030049a1088032402062099800c00c04103041e41003000d50081c01054038883c540720704003940500341560003403004092074400540c181c004080001d03181389203041610140f00d51030300d40c1d00c44405000850202105119000000101d410091b0742c0140035090207005881907803a203107411190a8503080042d0340e0030b03440c3d05041800b62001d2008008040c0a02c4580159504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 106909532 1250 106908282 106908293
    0x20a0c0b090102040f050d0f1e060f06080606010f0201110d02071203020301120f1b091e050610050a09030c0e0415020c07140f06070803060a170d0e01110105070903 72
    0x4040c0101c1a16072040c80300b44481c40004107800155442228160164040342c030b01444002d2400100811001c0030030b00440111040303400000702d41d40729107010f101c003c50411004089030264802c0031520340c0080f012907059400340c25030b186c2c850034610010844002107030090002e81d00114141c440e003580010084188030b841110683c0c03281c1305150647c40c5500d0800c00440481c50302c10094110b1107040c1c0850204050b6884c10b52081410080c8014520380c2c4050560040c00c00024003040d00c15028808200316020b8890540b040600800081c40102900000c03100c0350882050a810310140e05004804034040c6001d2100428551054502d03518103032a0110207000000041d190042c010b021144000101003040030a888000303402e022000030580000780d03003000b2545440d0b0030070b00010320242440f070300400a520844003501c1800c65195030b125070000e59a1003503035550403a0003414007803120920540b20503000e1a8149031000d41014110802030840b0016031f4032402140107440d08004011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 106910782 1250 106909532 106909553
    0x30f0105130c15020706050f0405090f07030515060f130f0b0a0f0512060409110d0510110406120e0115080a02010305011a090103020304170c0d0e060703090605071401020a0c 76
    0x10f07160f4081404401c050707001030b60b1030748140184014008042400f45200c20482e0513a0020030000700f081c445e90600d05101109034000b96054000a801c0400080709215025418440000054440d902e4250701e0808403556410441d415210690351010000342e2408030b0344030f000035144040c0350b075a584604020140c04440040c6940c024003409104c05070a803a90803004643c031840035100411a0b40c82ca14080051003118017456a00c10042200d00d4148a00001c3c2c00421030480002042602117884141c0300c81c2c0980e102d210005440814100302c0d005044e00200da8071001c80c4000303c1c125041d00350480260a03246c1050a091388181801b00942d81d050240038014034101003000c1d0125840c07000b001040c484c4980003414940c000010408004500401c815040251b4030b11640f5519000705040c0c0302d480303140103000002c0400349100713100d20b03100c8122403299a141e02c5080c11f451a204003a2640e422018082d151101241c001103034098080c0000c000b480829901c03241c0080306407400f21110b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 106912032 1250 106910782 106910789
    0x50a0f0509061008060f16020c03010f0e15010506030705160f080a0e010819090f0c1202120114040b06061e040f0803040320120a0b0f0604090c0b09030f0105130c 71
    0x3903200c00180020011a00607858100600307c401c20081002c918040c1c0c03401002c4070324181c042d0b10b0140c4004041e940e0b80e010102281001e0300b92008910415500c101c1035100b030154580c80601000800da029010740000c080680b1000510450150a921085600f074841d15055482050000c0d2400800e80e00210b40c1e403c6450908151240c1c0c1003040344560000d5801289100841d40c9408020501034640d0402d07202c02d600c06070405101d40c41d00d00807070104c10404000c81c020038403860b400080d8101070195000030b408038130b0010b50301d968548800c10244000392050303030000e00420444400d00a24080540c02100d41c00003140e9803481c055004000050660160615810070301061000a500802d400e022010460050708010103034400160003100c882c14040b100d1091500d107070200728100e00c0251090000c9410601950b41c3d002c144403d448440000515403070040300140107090005010300319521029049074400d020380781d5040e0071201d056503171105d0504951313000c3e4100000d540c03591016 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 106913282 1250 106912032 106912049
    0x5030a2f06040c1203020d030c0302040f12120822031103030928080d0c050f04060c020301060b0301080303043216060f120509010902041a09150303070303050a0f05090610 75
    0x84c0146840080d19181d02d80d4003075003050349400008810174032903019140900b010218441c801680c84100d4aa11781000908403004000781c05000d83d1f043c0104201845010b404400700c03601d6170700710040c44090803680002c40034000415501c11300c07890100042c0d0311a000e541300a100300f081042d081c81a03000b00f4042c41c003a040a62080c0c4001980042c06c0c0c1300b8190b8890004500b000440724255810b02a1401c0000d5116012400090031903003c400f2001c228001d900030032440e900c1e240181c10a120034051100c9544c005c1020074001202824207001040c1400203508000c040800511040c0710f0f040faa650490b44145415862600701e441500c00510040c10b0890f6200c0d020320b0080d011403100f070001d501a541e124000360031001c013034000c0d5003203e50042041040901710340403c01c0202d01809558003170344d03401c030000300c2103280c441039290b036044020029810020965005c5000c1c01c00203142042e82502e4126880003060a405218000d50513000603200c50720300390700208200130306540210007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 106914532 1250 106913282 106913309
    0x11404080c3013080d12110a21090219080124150c05011b081005060f09010e0402030109060303021b010e061614030408010b010201050405030a2f06040c 67
    0xa030b00c25548102891000411a503032580002c0300200c0c0d4070a4513600c4250640a1101060000c9a00100c00c1814150f071810070407120205a006060741d01071911294041181d41c0504176101c403001012504c2c15000c00004100c0c1c003002d502107440c80001c0c034068455a000070301c0c00d002c03912003030045013074008040074150b0045418007203c40c5242d00c4c070f00c40d40d21003004119456007403511410100e05081d8010000740042c03801c1c694030f1503001c1002480c004c00a00008041100342300c1800e400710840750010103d4ac1441c03108049a0043d52040764054140300b18030074604010303103580c006503000b0f0450580010701e0902d0760802a00384400d11410341d07040070100a40510070ba80080c2200d13092407017aa01d0315142d00c890b1890402c0401220405008503400744050000e402d8004002c4c0280e6120000074403812583d50010380c00e8480a8a0040a94100f8404a03aa0920441050f0300ea600078040d40415542c48102040c2848650040d004064010400700801d100c281401e071402400c1d2030302c0382c10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 106915782 1250 106914532 106914583
    0x150e042f092b23010c180b0702090f190e06010501090e011a0a0c0f0b0105031023220606210515060a1a03040606140d060b03011404080c 60
    0x8042040c2110080002c034003c3c0c0290072038030300c0580303460208124100800078203003520b00192400d109070b00300718200c0340400e40215504580b0000c0c1d4040c0b80d400381030170401e078544980720150307008020300040c07079801040140582007100e40649000c0c244c080b0058007042d41804001010064550001962035641100421511101008440751100c80d11a0fa0361030b000b00500c12598682c24203170190449613441c554a09019040c41d1090480c0c604604541442607610720b454150f8111b030640106200841c0c1244000c00202541c196120580f200d41c410446450035044100c070301080e030192026507451070140301072410403030855583e0000f8107468581c800f0540d00c290769400c0b00c2210408c0c03010300c0030214001740c451700c50800140c4850750b04984440d102c00c803080206d800842d000d9450a0421400203448448a856080303016030280c1480c56148080e154003019105030103049030150340c1c9080c0d00c1d0401314994403060055118130103e540d50410180e100c0d10b03080000d80b515610703424450514 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 106917032 1250 106915782 106915849
    0x10203090a0303050a06091a040c02060601020307112e080907030b01061805060a05070b101203110703061a030d030506030303070e030c060a03090507150e042f09 71
    0x88903069414500411340d559048444806032160741d00a815076414400304d1007000c1d200241c20842540c05035000c01c4410503080c0e080f40e5503441500e0407400360700b040001c2008180d06101c401502c51002e030205051046006440e030000c0350300000e201d00900440b20303a4441c1c40d0701c914a550050000303402001c4035411a20b9003204208107103d60000d006019042c00b9070b1140e92681b91001b00b50040819880380c0500d007001d40075030320120045405a90980005454078400170000046e04c0c0449005049442e00d581c0030303140003100c06090340c2207104500000001070380b0341c0540020414030000c2141c501c0414014035182c0003410220500340341c20304003001100e8400005903a842102840c3c200c01c1e03141e03031a000c68244a000d5800c90340144000407642440d44d01074111a406601c10412901c03040da80322060000c1700c0b8002c504d0f10004811100304c4482c5d00d02a00100100f0440c5030b482c440380030300d18011480008100085020307401011038980302030700d4031f40710316200d070340130460b90110115841010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 106918282 1250 106917032 106917043
    0x40302030607051c0f1a0103060b12090f1b0f100e010302090d021201060e0108030c060c0702041b120614010905130e0d03050a0f06050319060e0703030809070801020309 74
    0x42c404118011800d02400030051144011002500504001003520190808040d05542e01d0068413081c44021488255200344580000c507650140100d0a0451846940b05400009800c03010144101034001544007001d101c0c24019444001c40e440001200c0c0c01401041e03c1075400c0c0134460000d2a480c020040d07008102e4414418003480c006a03550400030014169003140c0030080d400c00302400d8448002d800550040d81500d150a40748001c4d81c0c0d030380454560320b00c00c07400720448a40114010502141c800782c0900320b5244010008520701481100505038811203501d0f85000071840d101c040240401ea01c5003030b01504240c208084110062000a80042075505c19140941c1080042c014020360603801403200347e1030b00040d03503007030118040007e0140106a4aa0f1050381c5000360901d40410140700d00c10407503c0c040c002c0c14045145128983e400070750368009540030b90312081d891442050038001903002c2d52194a4035152030400c418a1440c000355500b1910b45a032040042c811100000502c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 106919532 1250 106918282 106918291
    0x405040302100e070b180405090705030304031212020f0a080c091005090d0c0f0303030e010203010e040602070c1503140604060b07020d08090a03030e040b010c030e040f060312020102030601080c0403020306 90
    0x40103d504806841490300c3c00344150f0241c0c02490000c1150588156900c2900e082c101045505100c41d4a425107129181c140304e2054a80c168400c120800024404140c40d4800c1061410b000341d005034040c9295042e81c2c04030044582d41800042c40315001a04142580d4004a07070403010340c20019100c1c0414484202aa51442070110200b41001107940b14004014501d61080120682560300c81407680e0740d001500085021a080100040f140001442074a0490391003056a10351a1035580b1080c000703502071380c0d05880366a030300480842c540e505c0031110210380c41d00d03550003e50000302a414076458480641240c2c81142440420400c0d4220001610340c03590701241d01e030b038201081e0b151079040b510035558900d030407003d4500700009064000c68112910301080e141480300654400044500e00341000f0010086245803507051202d081980c030481000710110000035201c0d0b22500c4081c41c1d901b00f41e0740c1e000181c1d00003080110559214140c01d40002811418500385815980000c1c1c803140000e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 106920782 1250 106919532 106919563
    0x3030c0305150103111306180605031b03060f19090b0301051605210129030601020604060c03060503120c010c09030f02010c0c1e1e1a0306010c1e060501050405040302 73
    0x300380c01842c07034605e0104c0d89107195a80001011903030350a0083e0400103000c0840c031030384039250000110a40100f003240e204020110342d04408804c0708802c10000c1c1c0015065130740141c0744900d102e0040e02d030516a0328000c24590007084020b03103441c0a400a80d45001a124040d90402c400e01140100582c40c800149040303003412511040d040d01400c080303030360325000324410b04c40030000012010400c150147c188445113680320440520089042c5580c4416a1800d005034884800500442c0c00d0394803407462444d552070b020644660b0b400009242c003156038030b41ca1240000182403801c03100709100d940120031440c1094400b0515648030600610f0820b80064180031700c0400312420800d01c040000c015081c00240401d400d844c0c018601c0880c03940380100354001004600040607010100e100004179169000c10b80554a00b50020700210742002c1c1040781401102031507100042e0200300c4000c1100d603800301002804503e41400b60a03918180e000c02c1c05689040240310200f540031403140182c59490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 106922032 1250 106920782 106920791
    0x90c0418020f0f041407030212060f180702070b180a050d03080a02070c0e070302130614070f1103011e0510030837030207111507121e0c03030c0305150103 68
    0x410050314017a004d15084000d800200701583d909640505141c0710301c4001c1410b00c0d41c1e914240181400703248000c035030006420070b51840c821000940c203980a801361064070580341d40c0b1004044640c00103400ba0701c424100040d65203580c2008200d00004250031a813150916100b52400b8000e42805850b0500954000400300c080c0001620300c48002c0a51444c3c40e40d261410f010700400a402c407840300507980303001050000300e46100d04102d5680c4c4240300e4441d0328120441c2c0c0e03240740469802c5070456903404401242d071155607080c03296a40080302802040c00d014400c0700204200d0b100284169400b03862002c00313202160380e15043d11818104507002e207141d070312090212500340c64500c402c40c000e819500c40071f0a8075680350700500340c02c0384141003002090000004008022205100e24191407900f03024001c080340201c0c4c1000d141d03042a0502c012002d901d0321400850350242c03034104001c61501d184031410154984610408a480d0380707810081c40c10190311488120101d6250903040503280d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 106923282 1250 106922032 106922059
    0xf0b0c03041d0a0f050603070605090a0e070c03090f0b0d020a1e120605030a020306041214030c03071202072a0b04030b0103050d020a0803040204091a090c0418020f 72
    0x1041107a0140c030328200340c9200101000c1001034081c10031141d1496680c107245040d20b8401142c003e460280038000c1c0a0100503050030002ca0f11a0810701301c803a032244c0710040000d00c4400880241e80107040729581d61076580c04509014103000e41d80d6000e040082c02c1844204464070782c4605031140c42119900250f5950344215085800c048100d954a2840342c048033090a450f0301f080319410030100c005010300040da03a50f030402d40c0799200c0102c0a5059040040050002031041030715902184032810a5400c0f16070302100d03824550400c03104840070080000500c00306903001002e204030b17000190420741c581409a81d600407800000f100340300310462003841140b02c8156000c0d2940c090840c107034003180c0701c0d0340c0e130300305007101c08400e10003607841e80542e007130b52035140f4801b04402e0340340c0b40c01602c0c0030701d10f440780d03800d01c0004d14800400350341d80000b40440744555a001070403d40101c009000038a180c0101804100442e0160000b40500d091007004c44801038480d03101c5401503000803207000703000d94035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 106924532 1250 106923282 106923307
    0x10b01050304031e141201030516080c131104182909070e1201020d0606171b1e0c0d05090307170124031109060603040209040f0501021902160f0b 64
    0x42182400a007000800c200400040859110341281d01403411102b040d0030080d00d500e00050030b405074850300d070002814401039090003542d4280d400c40950000030442c00800341c103480768205410140e4450031080041e00801070070f005a2104170460020141b8a00000e01880490380140c1c840382c0c0540081c00c0010902802050301c0000540c0140c4038045c204007001d1058001d521444090000c40c1c501540428040c2c401c1c00c400c21400c03102d0065107855110203040125014000340b1144002108005080ca11040451032004420317192412584402454a50707078102505800f44c541001418421880d107035074000f401030100e540c00c0c1014240c5d01032801e0413074050200d83c0003140d0614002e038191829480751504a00882e0700881c083c0c40000200e80402118500c2a00c002e58091010710114000d4a03102010a80141c40340c0c0d220f1102007560303560f00c1d09a8000503d900e07003100807859040c2840d901400000600550324801215181c100341c0c860703032840b07894003402c0d01c540004603c03500c4404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 106925782 1250 106924532 106924547
    0x150e01020f1606080a020405030c01111c03020723030d0c110303010b07030f0804020f0603090c0a03060f0612050a03030924020306010f261317030603010b01050304031e 74
    0x92818003541c0d01c5040c0c0034904650b84506124001c0001c242e130300000c0d0b40b140d0a10a44042c0c803002000360080c5565007004640060228404a0302d1b4020a01070550720382d041c0d9901035402881c0d840c0980c80f840e0030b08080d482429003461003641520a07110481c441d040200403908982c0c0081d070001251412160100d480c2007203101e00e0401c41c48004004501d075180e04019010240c4240d031880e049840700d500813aa0800c041c0c03030013900410908040700c0c4030b00d4004060355221665030200c0301074800d40c1000071644030940d032050721555601d00140e003004c0128050f11019080110700384060280d10380d541941c652500201404040d03a41003150300b0020841072440c2c14186440410a500425206502c000d6005071051170114000340380c9103242c03902400744080741014400e1411860718203402c610558030401091450222545c0e4a448004ac0c2c905044a180641040e8501c0e181d1030030405050031a94161003081c18400c06004010009501040d00300c0058595a503401c0048400b04003901c404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 106927032 1250 106925782 106925803
    0x915120109021e0a050118061409060a0e03060a09170705010209030607030c020705010806062a0304030609050105010f1a070303020d060e040c150504050f03030903010e1b0a150e0102 80
    0xd034443d9441c804410766014000c1460b0040322100460360340c440042d01c0750040880b0b0204d4803006101c00704081400356004046000100182500d046000000a04554055854000403038003000f0458882c2c1002c00c40305900040d110030800a003001034a50280d0603e62750b0103070414070f030001400c0c0c0801c00c00390143d4000803c080d045810743c0c10100000340150040039080c60051040d001c000071190700c14203805003d141d01038080751420406070024221411408108005110b091100c6191101d0070002000114003415001542d40c005140c15425a071042e0f1000c8140b001040d8103001c441600d21581220300b9041d50040e030b9405281c03405030042d019050154800a142c848000740307100c5145030b007900c5903101d504080300680d296a484061805502800c800180060005101900704054600d04c054402000c41c0d08043d0104002429180300c80b01c0c41c42150040d2443e811008804d43c101c090140003140c942d07142ca400d104003c0802d94002d80e90004100c00309100030340990080c1b01c100420f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 106928282 1250 106927032 106927039
    0xc010f05010303120b060702090a15030c150914010905060c0c1908010b01080c091c050a11091006080c1b0607020f100231090e0c0a05091512010902 65
    0x1d41c0e403401c020380700410005054800b03504003c0c00360071505d8580d0840d024a07a000f40800003030344400350301d2001800317920084522040070b050040007244880314003000031b0804610b00134205080c014000e00101c8541d100ba0000303294210b1a501c1680c2000d0361609031034082d1200358445405c2c96101c0d00e0583e02d54492074101e90f0a1403803d5150030140403400548038560000d004071480341004458400301111005903050083c4a00d0050340350030203102c5e1551110507000601c0c0030b080c0c1c46440c244a07580c0000c5031040a01c540103080c80c01c2140c9030680c8401d0b003494694090380340190192031043d0040501c0c0e2868000100900c00c100c81c82c840c0b41e0768080c02c03000c0380c01503e03000d08080d640320000c00044078a40326103410024042d4480c004c584213040c10550406404424980c840311140b60405520382d5403e40c2072020070548218841d00c2c4540a01d10300034030001c50044140889a16540c0105000e25160340401208600d001c00422604005881042c0152501c28040b4010301c28604025403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 106929532 1250 106928282 106928291
    0x204050c0f071101030e0a030815030f060a0b040b010903080403031211070f020102010f090c03080a0c050d0207031a0405030a21180c0b04032406091d0f01060602120c010f 75
    0x43c4020001d1100f800b05003a20b0400c986110140720558600462100078009a5101c0004400c0700c980141e4100416001c0c0403104a04110103a032420300c80d084030610901c40d41c82c4a481c10510b098058401c3d101e200307003040f000c2c280c29500c0e52411071080e40400303814040144650303500c41c0016480440200e655540301d45c0c0f0340140c2d02d40069110f4810381c0580c01582484046541c0755418454a0260f551200f0245445807540e5140c40c5d180d008090005c081c880e0000001011800600c02c480000816501408102c0e0451408100c0c24a11403417408142e001e5404000001e00004200c890704405401c0450380c68030704902d1072101c00541c880e240101418860359074410054440c031202182e1054040741d4130280c890356580824000c0b0311010f4144200404c00086030403512030018603d281c00c10001c185143c41b96461001c4d99000d01c4641111074542070b0109100006000170201240e81400030b00029291550080d911504031180f1113800c9000640720109500c01d40c00481d020340f803c0340900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 106930782 1250 106929532 106929547
    0xa0b03120a020f0705040506030a060b031612060c0e1305040c03080c0c091317160c0b0301060e0a03020a05120313090209010f080118020708090a09050702070906050a030204050c0f 79
    0x94a0340d107680103181c9181304080c8040341a140a000701351050b24060000c103481d038a103031205406022210081c0d40c050003030040303c4481107003103851000a0240c2903500b20340360a4519090341110080301c0b0301403c001e000404c00e4240c1c0c0e0745128007085080b100001068546840c20318126a4481c1e9100034449400026400c82c8001d01040c0500e030594102c2d0000860750319003440c00051104054000c042000c45104003d40b80c00300c002519000602c0301c0140750b0078440d41e035800c07083d5010f038200500c9580c1c0030004222440d4030041c520300c1074a09541c1c00b211a465640480c556038018000e051155548c04403c0000c80c40070410346000403000204501c102d56180c4501000794003d014242c001b900c10041840c1140c000d43c490340c1243c46130101c5003060070084030074500940100004480a8030104a0906181d0315102d824003d0000d18400180e24101888080c0c6041a80d512506410307090080400c00c9a40f543c0c6508100c0c1d40503035002c00c070703590355240f05149885070400e810100340f000318441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 106932032 1250 106930782 106930787
    0x50702010507090f0b040b030709090204180f020c15130f0605100e0f0105132315040606080406051305070b091503060904020103110409020d0e07050402030403080a0b03120a 76
    0x7a000c0c0c03410f038850034403040d100c0030442000b040368014030305040340402041100c4050302c0700460340900c1510b0000506500c43d21000c00740e0713003e9840310611240f45c8440004403045172048009400c4040000c510b041e19030140d032910742017400358142440e481c081c0095000c0c0d4044440300b1110b980074007161007510191402c880200001d942401440807142e40200780d1440b2400c0c81401400d100c2c1c203403819a8070b000204016001021400d4602d141c50340007444a8124001c0b80c0c0790001503804104041d8075241d0102d52445d101e000285205505000c010030019420002a9401c26080180480e40c1d035554080181c1b00700c9a40e600600c24440c900c4000743c0368001d80302a00940c4011148542002d80d0070290f1a124041a2151a40a8a1070001c079006600a42c080c2091192b00404181425a00c2071f250b8102e8000d92500340000b91100305042c0c0d1a2010f020080142401711011070440c01c1c15100200517a60052144c0251551500c0680031a0741c01c1010007008511403c03515030310380410800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 106933282 1250 106932032 106932041
    0x212120f1804090b0109090809150315040612030309020a0819060e0c090c0310030c06050703090b0f0406110a06020a1106160210020a0509060c0a17030106051b010f05070201 76
    0x2644203490440246141440c050281040d00f40d00045461166400c103003000c00149184c00c800c40b0b81c4c02040081c4925604d5000d080907500d4a1207820070380380c1c503001b1880240941c025001e2840382c0e01c0d124051001f00c0c00100c0000070303503826290008911030584003050b80186c407908240320601c540c420409440d0410b109080300e0034070500c41800042000305c1201d9803407204003002d0b6400503060300003407001c01d00c40001c2c4d54007080344d0714544004c0340e807502e0b080318030f801c540c000c140000d41c000b44060903d5042000040204402c02003546005d070070781d401e2090f60049000da40c0c20000c0054104110380010030100c5495070f00b01008650344c22000300c4c00781c620651710a01c6284bc0c010b9500081000c119580500f01400307658004d0305000e240071800000070b41c0a112510300b030060074001001aa1940000b610b8501501001007a494200341070011040000e1004107103460801c05c014840c0945c0101511a4040000201d038110b881051801e805014082510001c81d071401042046841e4150007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 106934532 1250 106933282 106933297
    0x906062712030a1b08040320091f06110d050901050403050f0c04050603010c0816020327180c22030506070305010e070e010c0b2701090501050709080a0212120f 70
    0x110380841d8005090144d84420004101510740d600c2840100049140500200e07090964441c01300048011b0310002004200240c803c003070500a284a01c40399040d0260344000a40201d080c0080201c04a001c156070f103088803103854080250106200c01c19900420030380f00a9079115084e90030700c03c0d100e0f02c00c03a40c0d6250000024800c80c10a008a00213003010311a09028000b250380f20882991100301d641503408554004c4821413104015920104e000800102140164071606848240a400c10403050004510440d481810000c061200071081242100d450080d0b4080e04c034040c415100c0c0c8000c45544c0c0e03a00240c5507019210400242c1ea51550040c0c0c107030f84002c0d0050f000c2c0c0d00d030704500b15445401d0300d01c0d141c041400400260003080e41091190b82c03000349204410b841390617141900d040080807203a1010540e4440c1c1d04075041010a0241c06d030300072514908038602e2440c0c00360440d030380c040c2180040c0c002c0710340c50500c0281041c00e022500c800d003050002c5ca69500e034856410b6030164030890 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 106935782 1250 106934532 106934537
    0x5030a060617040308060a0b0f03010518061e0307150816141c020403061d0f06070807050c15070f08090d140f070b041a060906062712030a 61
    0x6021900a00400300b5600c01c00942e0007481580c0e9035070360103454807003001d041941d21034245100000d02c100020020b0030000c500d58034880d16549001e040c001400502c455215810070f51804000881d114500c1c51742d00d180c6941e054070b00c05408280440c3c240b03451a001008040c02c8150312151141e004008907006280c0d80007844046c807641e802c210389a4102584000880100300141010011341d20490a034041c24a4801031030245c1d00c0e9169021106089082d40700310b10002c40c2800000020310601c25101e407503c028221500d0508801010321030020121380c107002c004585000441010041c580686800c3d040050441c02c1c2418003900c080342c28816080020b030074100080707603c100484d810b900030f19961030741c2e6801207003a1034001880e000035060f4030704c0590500540300816100742010b4000e60180e81c520380d000c55030546080d682030000700070300c0c0103010f0320302805201e0b100c034000c5481c0200a07024038203017041840e0080b03445050250440791300036141d0503c140006400700080c81483ca198 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 106937032 1250 106935782 106935791
    0x60f010302030606031c11010b040e150a0605150a021914010c02030f0301030f0f0c0902070b07020303070e090a1d0601140307030305090f1318050d020c09011505071205030a 76
    0x1141016600c0a55072041d82e040f506d00003503902140d0003148210b9540d006000042440e04040c0c0101d400c80da003a00b00d401d030f941c0c09020701003000c82c1807a00e00c41c0c01c0740c05800c041c03101504000c0412140c2450760350a10040c00c001800c22400392090201d03000c1201200b03030582c0000c040342052984e2040200c0007004075460074002c012280d0002045840c000f2045914030700b0350f0b195481e40207115014440940d6540c100c90fa08100103009000204080c013150180140c64981f02c2c2030401c95964010440019980104280640d283e041860804842401c075207004456442c0c402c04400b6019a00300d000c1b050002100002c991040800c1d054140d40030880d1090401003648101a66180d2500c0301a010980030012211181411103181c80344107006400c40d480c039000c3d51450700c2100d5a18188604180040101701d04000060140a0340c0101c50f00c0100150307000140091492361341841128550343c030402480010320f0161095400340354000c2c0c08078000080103040a01194402c0328600b0348036260 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 106938282 1250 106937032 106937041
    0x180210030207051e1e0d0e0103020705030d0b03070504090302030304110f0612040c12060c08010923090c0306040c0305060112030503010e0a0b0a0f05040f0501030f02060f0903060f0103020306 84
    0xd01c00d40c0d080a4014000b04510045038600015240c0c0e800301c0c1c3d8015004880d1005440d05c00080c00103c9040c900c0b000703040c0c6032944800203141d900c50ba0b0b440d9040500400070407010401c0042074400e42d1340489000180580e1150000e03140045541c02140c0081c10018500300303258000c030103540301d1030041c801c00e2500a26802007101800c2145a01540a041800381d1800078035000c03441d5510510412041800c55180d170311f05250a004d1001c200c60207038407004a5800350b60321524541c014180150203001500201c4482d0425607241c5500d110084003240000b40440c00c100000b60030620007900750741d95400d2034101901105200c0c0001c1d40c940c0318000001448903034020980001680654030321381164200700c1c0d0a6030000d0060004a8010348500740c1d981696140341c03011004000000802030020310788818081a80c1312510030740c642610302801080030912162958415642c1210420394807048565545800e002d0610240c0e0117100340d00c100403c0100d040c40c0d03503060301d00032012150070750f44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 106939532 1250 106938282 106938287
    0x906051005010e1002121b060c0910080c16020a2c07020d17090c13051b042102060f030406020706060803090a1a0405040e0601060305090d081506040306180210 70
    0x4c20b540400141d00281800ea03406040c82d020b05084000188010403c04407280c40c40e01d010429100101e4200c400640308217103140143c80c0100461081c101a54980703880030f1401880d0040500c50040c140f42c0c45440403c5664158a00014240f0024400d481151101e0103c42d0b042c2c10119400c121480d00300420388180c00040c0d6040c3c0c44031180e844d86041d010841c511814003401411007202881044041d1481d82c0c0c49014115150894030f81c0050706141c480b003086c90f68240070415182c12441000144075903407039204444080c0817a80f0f03002c1004043d0744040b400134032403960b2001920002001740300800449400038030000d40500410701c4466220044c4684900c03c0d03400c0c06512080c280010003800003042010240b0310200c41110381004e95072400718003070f13460503d00303103460744c011030700520130550144286074010500c1d100400304001111406080020701618403420b060201d4800551a51448101e901641c1d2210b028050b01c1d060010307240c03200d0318008080b031182c202e8200320313140f861 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 106940782 1250 106939532 106939549
    0x306060e040f0609380105100905090417030103031d1c02040e070801020a02060901181211030706060b120c0c0c06031b030103050a0302070b0a0e040b03010906051005010e 75
    0x150040e4100400c6410750341c43c0801010000f10885402180074160316501503809450044201c250543c000c01c0001d000900482000503040644a02c0c0c074542e044100f69401030034003042e0f0318141c900e2069a1603608240106100300d2301e21071103050001001100f0943e0110000d08480c101d49112a2600000410170503049161b10000b541900418002d00151a0a07000090200310782c800342c40380c1e1900c0d80000f902fa17174451108200541d12050034001d0500c000d21900010902c108040d0380704070340311ba81e01c3e2074442b074114041007081250606150426014000c40700c100d07a200404000450342c030b05844049402c10b000d50656600400d00041c500c1c00d84004442d100354a52018200510b1b107901080b01c581c0014269801c613001c03401194122198020045020350b0090005100010051900900d800107e4004491031031082c41801e0384650806000c1e00311050444020035030070300440c00320340140303460100900140d0805042c003185051160000301660005ea03039803148011401c0920100c0c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 106942032 1250 106940782 106940791
    0x10605040b0910090302030106090902090f010e0c0711030303130317060102030a0c06020403060504061506051201060c0203031c06140a080604030804080f0a02010b09060103050907030b0910060b040306060e 90
    0x181d9003045070500a240440400d0441d00fa141028901e09440380c02003401c450701c54100085403607450301343e11b041d0700d00320729841c2e403210381c00b40d8030345056050958560301c649018042ca8020a4042100b00c00c00c020301c040c20341c84040240440342c9a140481b000800c000700312101354007141024045030080c1c0d05900001d4424074042c0c005601d0110114021a421038070301d042a64801d07400e120220000e4481d0055034091030081e1004030f500310071540c200000085940c0040180170041010300c4c070001c402840b0300d04490460500d807a81c80c40c180042411485812803031441da0303455400444c101c08180d4003240c29190641540782041003050244071040f00e46000d1501c0d254040b50000f00024481d20175030358020700c038080984c24010f48001004a64100604403400760b51179108080d070504268107520f600005c2460b044c082d0381055a100b540791aa1804080d0450084500040301c00c40c00300441c000104d1500c0d010030282d0781c1e9058680442d00280403c980903400c22130001407501240121034000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 106943282 1250 106942032 106942049
    0x21602041a090f091e031b060f0402091305010903030e07050609010212090d05070608070311040308070f02041503140d0201050c0d02031302060d0c030e0105100b07110a0807080601060504 82
    0x9500c5007203090fa4442c0f0700a00c2c65045101e085460440c0c2e9940360004454403103900001c0d0b884805200305440b06401501c2144074a5010208000208000c1741c10650400d4054810101d6070300c80180681c0d00d030101740750207061036090026403010180d056200c00300c605c082c007050b1030500e601c1d08200000c0d0b11889014078010b920180480007144e6051009084801c0020b02d188040350960782d805042008651008010900c100d0801000541600508031800c01c020755140c0340c40d0546e5030b81a03a50054940c00b074001c0151480090441d111540601c4030030407008408040b180d564601000d40f001607074504422401050311300b030380541c014095940a100b0301e6403828100707810400340e9070082d00014212080c91580c4440310f400368032410010001c2c4140f07031101040b6900c005001030180c074140801c0f4503041e8503120800480540c0041d410b82035807112003e082d618811403c050301e0340409000c00da940000d11460000304c60000040c0c11040b500500180d03540340c0c0e40d411003030300c03107010302d00c214280d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 106944532 1250 106943282 106943299
    0x60c060b03030c1b030c0a0b18060304020a0b090310050a0f110723030f040b04061806080601030b0a080304060801180e060105091312020606280302010e13021602041a 73
    0xe40c6080c10b1a885650040035040302d074154070a0f000100c003007c1d140c0c4a8a01d02d0800070b0305943c003400101403110300f40008e940d128a1400c090740496006e180038820b08007880c80200b8400116a0140100045985810000c0c081411700440319001068000c01c19518030703180c07500141c2c00c5000c20055540c00c0da040302c600720500a4940c2903010940b02c5040c2c070990350008201807040410002c000d0006019851400c9468505102001d03080c0407961207488000b2452083c2040400d904c0b80781107620801c00e1a0100d4a11200d8001c01c0290030280c0144149010201e00454407070350020a050494407000760318590a0288002c60040b1f4418140d07005a03500500d006100e00d09100040e180c1000d140144101038002c4c80e164501509100000600140c020409112a41c5021070301c00803040c181007902d0b588660540900958010b20748402418454040b5402d0400e698490445d010800c1e01c20b0309554a500785640f05174000395101e01244102d1030a0110700b0a00078014a4000b2031102900c00e00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 106945782 1250 106944532 106944553
    0x60c091c0605040f110111100f060807080307060c0801080a29090a030807020f0304090e0f030c030a0311040503191407080304030204050a0c0804030e040207020604060c060b03030c 79
    0x89008a8162244008008124040051074510489115a000710a10070403400b05140408200b0440c0683d24100300a258075050ba40700089041c400e04d48510300006003200d2000300c075101030200d5610007141402103920000b00600c003c0000d1816900c01d000c100012600791809541680c0b084c05082460382c4141c0c003040000d5885c015070030580383d4040c8a025845500f9210070380c0b452044440e01816089205003504154115035290380103841d500140140d90100001107075240518460211143d845800c0400145000c2c0018045800b090090366518603010320303011f5803a4405c17180d00c030000c1d2410311200d00a140980659041d620300030081c0c140344200c580042c8110384019400d130307601d01c0780f4000480d10f0a01080382d03100a00c80500034544540c82c5004100880e43d0003000c5409240c2004220951320b0740c0441c81e50b62195050034400c114a060f900400c0090060500094103c540000c01103800c503040000761024510a1000f484000d05081c107141c1c0302d0084c4455010781d98812030049 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 106947032 1250 106945782 106945789
    0x512070203010216080d111603140c070303020609070911030610030b130b040f0902030706051e04090e0d020f06010621050a05100801060605030c0d020c0105071d0102060c09 76
    0x1418414001000942005158034196a610380528000c5801e10b00004444000c2c9041c0d00514091084103907080c0c1c01c044480802101904210744001c0800816003c001d0801c1d8600050f11007000010701282c2d244c5490380380c0a5550354094901030054400c80c00c000513400c085014811641d00f058245900311384540e028800c0701940d81802c0c40a15071162800e40c6e031600c0f0b21001c00e10b066000000454150743e1502404201c804207030016528905264015006d41c60001e165002c852607460502d544002501107041c00c600e0000b0034902d02d040010300000d248e4581d030132480007100d10000f66003020070030942c181c3e81c1b901c004800014540100d0b00400900740158107a4500580300036210504030a649000320840d081100d51020180da00d8081c056204010603e41000e016000000c1185504100340985180070050070018180c00001d80b14458000e980c050391402020f06c4000d0295003001c0d0300107008078880d07501c4003035800b0084031221415880021640d00a04178111140e140c00c07407907000e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 106948282 1250 106947032 106947037
    0x5070308071e0306061b17210a06060e010807021002090a090509060103170c0601030b040f0212060108060a0c0504090b0d050a0c0f050d11040c020c0d0303140c070512 73
    0x14401400504980c2000c030700c0103240101d070400d1855400144c1142881c501402040301503a10220050010000c40000340c4805040110707051801c0c03a054960140c02c0700b03c0c0e8505882142d0078207003c2c4050078850054510340202003546c0e41503d52040000d12103004440c1c401c0125034003030044c1e1000c9a00400103500e90300400c4040b43c05072100c0070b50354070380391031000340d41050b10411074551050004000b8004a02d413105a002ca10314000c501d420425009140e58003010b0001921040480700850104989851010381480d80680f000f200b07003400000d1191141c1d02485420310600402c0001b4640c101740c0d200c1d460654006484203802c0901b000e60b072200034400e003c112078100c6601643d81f0085441000b850040c40e00c9400700100341070900c0e01d00e121000003503002602a030f9001502c4000519950380301d100040c010b85000544050102040340717040412a885900400d011030540c4c185a4107410541a010031066000381d9a250701d0410791040c17150102c040d00c59004440352034007400780c4000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 106949532 1250 106948282 106948291
    0x12080c0d05060f0d0c05121203161205090303040312050610200f031e04030c03060b0d020603070518100f11210c06060306010f1401090b0c0106030209011505070308 72
    0x1001c5183c07030004089550500601400d40e00c50603120820000ca00e059640ba040d42010b0b400a0005241000c006038211f02002c0c0c440014200300c6405182c41c588580c0100c2840e5122403414801400c00062840d2282d00c00d80d42940020b281c0e504032800103005000d50f070f00480019020f118006003941c0308581032008140300400b0501c202010802c184003c000f44640c903903250002c0d40c0e507805580310b0900034840000203103c0701074080c0b10400128100c500c108044036008040480c12480c6040041c44012040c0d038000d600c0324020050211403584000580711460440c030821f00d201000f038041142500611800740006208400807421661050142241101914085950340040e01c021604943c44500400c00a6a00481c00c041c2303100040040c40c0d0040000d0b4090308107541003070304240c0705450901440c80e19030912003c00d1966446107120800425201506a40f100b0070607001e18080c002d144820b83c03081c0040c0002040d0301d4040a20400516026141c1030f10b84202541c0c25a0034400050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 106950782 1250 106949532 106949539
    0x17090601090b12070312021603150207260d0b1c060b01051603080f010e06030d050a0905030a080405040501061706090a060302030f060f01060f09170a0f0602030412080c0d0506 77
    0xa00c00450f082e000c1101c40301440c4250b100840035000d41100914100c969801c20180b810301c182c1c10000b00700384010a45100040c0880542e8580b220b04111030000c1402c0c140c00c0003001d14200e125a02c15036803025110390300d103d02c000d102c1380464804020824460001d40c00da6065000c2c20130b400a015a400010500c80c10b04007141803900f140302ca558115148401900460624010402c1c01c48188400e035026108902010400b410a140401c0c1d03a8421072040c0000c1c801c3c0090010100d43c01120180e000309001401c480c0900b295160010f5560401e2140038060390424002244441c001c6031000714840e074481140021350341d9401084070032031001d0b108103030090b656000840562401d11001165040d071000400240c02c04209403070194405910200c2008080e20b890412154050784030b07012a0905080000010b0798080000e042c0904218028110100c4520780c4040110507000303548124004c00c0540c0b0307501c10105c4143c07a8803a048440c0c00d48105c0c10041e0f41c2041400750b00c501d0f08404040d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 106952032 1250 106950782 106950799
    0xd030e03042607031a060901120b07030e03270306130b13080304030c030f03050106050d110f1614060103111c1b0801060519061112040306020a17090601090b 69
    0x6905203800d018140c4c1040d00d241d50310080040180b1120b80708150403c40c107a03424400d035850704081100000d24003000510403a181d00100b51620310a40156008507044020360f41e45255220601d40311030000301d011004401c10b100c41901600e00451528403d2600020340d0040032070355965002c0c00d01004104d04a0703510302100203000b080708031015602c170b02d1217616000000c00c40e5045c050039070301c003642c0781c9002c141c02c00d401401200c0e8020241c074200d485038080072403211600c481c41119030080d2490316500810216100d543c096600c00741700407179409030b41a04502e498810840e500c4000901028242040a03083c00080341044c8204102d02e55074249540341c10b1384159161458240410b8031107124001600b000d04c4a60003e2107030b0801030008640040109182144d10108201030384902014065807400c81c101d000c006200b08400c0e04044c8020071307925a220718100c0d00035002640d4400020b02aa45240c040581542d2140e011300c0b030000041c4111382c0f0341001c1070080d05030483c0490300312480d0b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 106953282 1250 106952032 106952099
    0xf040f05030711011803050c100512091c030b090601050a03090204060f050301060504090b0a02071e0503030a0f09110f03010f02030a02070b0c0a05070b0601270501020d030e0304 78
    0x340050311507244121035038083e1442003000100000170302c030300310f03007940714803c0040002680c00100f05001a50540301c405050108503c151614040c0d521600850310a001c10401d5940d40400c1d1000075441080d5100d44640f00340c0d804804685110f18242d403c2601000442c141c0c3d0300880103400d82018506e00400d00405582c0490242c80f45503000080c5100082014840b0303103401e002d0b00c1c01400061b14100440643c60b110403e160a000e410303003011683c00186c2005006a01c0c0e407503004801525600341210f216490003950703c0d8012107188041c0f501c0c101c1c0d051b4404506000d1548002e40203901111407103000c0d000c04c00b90a050b0f40500341d146d9640d255150b43c442c0139001461203070812800061b111400c41c04d118600c010000c0c1004502601041000c6c071140e004001e490034142c100780b140035680e65110040c2d640c111454084240e500c0d881108032404030074040c4100c16108280d090303402141401905400381c800300c145030750858005020a012000c2401080000e03c45010b51020b824200b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 106954532 1250 106953282 106953293
    0x20c01020a02070302010327110f090405030702090a0b030309090a020d06090e0d090b0301090b04060e040f020f0f010c110310090305041d0c07020d11091f0905010b030f040f 76
    0x20307071021800358100c0300f0200255038240c0b04903082d807032114003407140d91240c80083d4100700300e00680060507202c100e214590756480c0d0483d801000c0310301910000040c1810300701182d6030382104404900c41c043d410005042c000907030040181340c150103001141808030840c204590060000c1900311415030070b02c00c42015100d1401041e0040c201c0d04000030391051100c1500d0304003504101d800007809a0f5181c00c2110400400c1103e0440b440000b00203010f0760f035a00001c000c1c00280c0d12100c0c100304084140404d00545c604000d0845100b21141c900d1210040c051240540c0d1074013003907010030002c1c800744d00401e0f070441c2d0044030400001c0030b440e4228044801e000c00c03542c4802094000500203e0140400391511828218440d0b130711500500c2450403401d60381c40c80c454190002e015880400b006420000e428810b12070721030f001404a8000e02d81040409021a03200141d0722000405800c00200320f1050700c119410384485c44141ca1456690660301c1e805041c005d00101c48501c50303244504007051 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 106955782 1250 106954532 106954537
    0x4050a05060c04060908010212010506070f06090809031e060a0c02070e01080601030b07080c070f151a0f0108060f010f02070e0a0203070f1707030b0f0603090c030f0d080712020c0102 80
    0xa984a450750302d5504001c4000e0403205c00307401071412684100080740705a40a80843d50458500315452950381442c1e26020280a4240c140103000030b041194034810004030340702034040394405a00f140c60b01d8a03651310b610a812042c640380140c41d080100400d03100b28244d00304110345503003401180c480790f03a00c0d02c0e084191542640034a0380c0350440340c010701c1001850031807182c1012892402c5003107810140e44c03120152041010041228101003030640410245140c4000054042c4600300580c0c588038171036040034040050003520894000c002d0290641c098810b090090390082c0002005030070100c01580c001600544040640c801d2030030016042d110000940e115200d43c00300580c483c206541c02a04070902201230006021524150240d88000461708551020321842d020844810303035070200b01132500108000e40c004d1400002c0001c44000002c00605440c0140c08882000d6905c82400f034490000041d050006030498010640f80ba1142581848040394200010300d40440c0400031760072039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 106957032 1250 106955782 106955791
    0x130305010f0c1404060c03090b0a0e0103060501031a090a0b1c03091a0a0807090f240302040312030e01020d0509060f060108090309011d03060129040303120504050a0506 74
    0x40e03440350300c4216079600a00544031415420306000784074142da00c12071a514043d0b4040c800c100000310074240d01341440364901000a140c1c040314242e8420a00e0303002040d0803680580980803e0030304400050030352192003003407281003d40c0344055180c1c030880100070850300702501d03a0743c4c1151a0044194161b580d40d44211100520b0110344040703260500d0080c100101b641c2c094a00c1d401e035505d515000d400290202c48184007180303001603959496000076100380c0a940c21110400d82e411070045500410342241022500541c039824402c004200c0c000c600340e00c180d00005041c40c1401603a036070038030f010350011420020240001340c02c00c1c2c080c5d00070303604461040360f6000156100b402031040400d00b001000303030050313400c1c0382100072490180e1219980b031241007061030410840000007201c01101c40403000080c0300c010140d0b01d807569207812042c0c031030343c1184801c0203107213044091008985c0700310210f80440350300d61246070000b00c80420300c2e0001c060040c400d540c5400780b1202603000580a00010340304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 106958282 1250 106957032 106957043
    0xc012d090801050903040e040b09070b040b0406030e030f040b07050312041101120912110307020d210201060501020703020402032802180d0b1302120d02030910080f0105090c1303 78
    0x914200005095400140c131092003900104424050710b1400058180d100360011500401521030420031440e102941c0d01000c6000d00108001c1402d00080c2c000380125011650203120440d1034075000d5407a0b10510014041c02d010400041001c1a82034010304100c03030144050380d0902510440300c80801707004940440d8a08502c0c80003d11031340e08009000c0d0014404002000094a03640d1440b00c600a45211039050154524110b48106010811688100d074050120050780441c0d141c2071707411120001d2002c5e101c1403180c940300c0c0700d14414400d441c00c65405034024000c0350b10f0b5400384070007540081c00d81104c040704441c81045110034040c454001303001c0403c00603500e032034a4164015100003181d42602c00e2801440c10700110300720b10b08039500b0404c1080d4204002405100041ca0089007144803880380c05400035018240d40c000c40907140b1440d05032140c070103414a005040703945a50444508010f40a144014015410445202a8131000645902c1d18040311150712800d28421039008482 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 106959532 1250 106958282 106958297
    0x10c031e02010609061202010e090604020c01021305010e18010e0a090f111e0d08160b0a05010f0902070302030313021306030813050a03020303070f0201170403050d1406030c012d 78
    0x3507401603100d40001810030001c1505184011f600080a45481540301c1d881003560f10041042650707640d04a40050180300000c40d90b400104041c1c1c21112050701c100c90114081d0404454036081c0b03009601c80032074025807050300d140e003000c006070b408880140030a80d0b410398841c0744600017030003080e1a2224500441118071600001010014950f51034401d00c80d0b500015829403401d51030f0150f0011403141c0c030410341078a603034000700c1c01d40408420410103002c503000b600c144481d1401c0c0d0703440309041c1c07049105940c04098030380d003040050744617144c00140140d01c1000016030104159620a50840c8002c113114010001f104400c0c0544841d40c105541480000030740d03405d2044462407900041906540003c030852035500040e481e40148000540080744401900c42103a10038a14519200000c030f140d02c0407400e083c28020240e410150301c0400c3d051400640d441ea0741140724074903201d00c900070300600d0400c00d4000110394940500d150b0710f01001c0e05002c110904c41011103500c40818a0307644200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 106960782 1250 106959532 106959539
    0x3090703020901081501150f03050c0d0203010e0115031104060e011701170c0a270207020d03080105010e011d0d06060b0c06040c0f030b0a050c070f05060a060504050c09010c031e020106 81
    0x2d45c0841030340141c0e0034400c92002d8805568102c205000c034400d503410000f039103582d050341844c660703c200c00302c400903144004000b141060103140755070306807000161482c0c9410000c01040c1c048640302c0207122184042404104030329440760a0140c041d52044c5426a40e0741d8810030404540d00c02070700f050b080200d0300d070082d08a400040150302c107080c4044038000400c51030141c0d050340d80c0e011181c1e01c00b10692a070b89040c0506901d0780490780c40590150140c00242d41c0b03401c00a01030b607070a0048500040c1944104503030380d0712400d0141c102c0c644d041449103400c1040c0d42081440903e0f204100c800030345603540040da054250001d856402d01d5607015103080c0c5403034030300994000101d40012000c1803c080f07050020420702d88030b650b807254a041001500d5211141c64030002d001c0c00300000c000c2118000b502041090110742d45006850032072003440007a84801c200025140203e41e4a02404824000706007a0f622900c0d200d09114064241040d084009054007501602144136620242c0c1d12102e041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 106962032 1250 106960782 106960813
    0x30405151512070323031312020a14150d090804080601060215070509040506180403020c0906030a020915190b0a230904150b1317060f0703020309070302090108 70
    0x82c1c04150000340908885400c1d942d8000542106100d50402441c0d2051840c07161401001241e02082c0a01321340d40b802c965079106141601da035070b44200d001e81240100062120401503140c002508001d147c0300900b241101520060f07080200c000034400e469080c55804204114010005009100041e00c140e40c10090042e1408440015140040001f042000101980041902c10b050011507000c40c1c551281e00000f02e02c51070060a801c040140c10081c07004040e00004d020700001419140c1005c1a0344843c1016115002d00c10065040f03494500040d001800c010100a134543c070081089021100e1400f1b2001184880d400c0f03804407905c00907100900070b400c854016103075280c40e0b5444d4051004016050014028400300d00d00598481c45203600c620040150b00000c1c1c14080740382519a05e641c100c01c84441d804d4403580c4031140c0390551213416100d0102d800d074400c0d5003c0703415800c0c0361545807007140254002040004940603501c0080b005a69800c00e9900a0903450010001010448180c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 106963282 1250 106962032 106962049
    0xf030609060d0c170c04020a0201200c0705011b05150a0b0a0320010c0b10030c051f050d06180c08060904020a05010f12110a02060f0c0904020304051515 67
    0x40500c102203a0224000007042c80100b0400d803003128806244d041503a528062030a40c0d6081c405901500100b0860030f0107905500c02c119112049601c10f82c01d60401820205030312910240c1c52075074001d10320500c0a940501600e031500701d0040160700008006413552402d088400c0350281c0c0b441d039203200780b09040d0a24002c0301e042003c105c80e88250b45180d56500118000505100400361090320941900c0307a000e040190307801c981200e40c0c0d11451501c11040000901d440c0021039585e0780500c408146030410390f40070508049044e070070500051024409413501e030030a42e080344403e47c5511000c11181121300d84074000a1000d80040b610079070b4103101a110307030001040140030b08400e0040001503036960500e40f08954007070906940c04411850101c0c0d0056402c03840c0800700c0e0a00701d0411100200300001c004544283d030955200e0b842e042030b001200002951400c000c030a09000044451400c0c0e4021030700a4452003c8642d0744a00c085407003114a01121003044440d000103080d501420321026 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 106964532 1250 106963282 106963291
    0x3111b01020408250509040809032b18090b030709020c0c0103140601020a021e0307030b09010509030412060c030b0d0303050603011a031203040f17070c0e13060f02040b0f030609 78
    0x11540c150081c0c1501c9181c240c4e564411107214800101c041000d020008040f240e10b41c1c4040c00b50303441069019819640c0174142030010300b419070440b07040c642d46840703290034801000980704040406481c09010320040c040c6d400341154503018020000440856a01c01024510030741c0f40034100424401002400703d03884032295445007070b50301c420004d491307901203484400954112012142c9400a0348115004d80b113400d04190140305011010042c0014030004038417621910f0000c4c0b059603942e4401ca130702c1b80500d118801946106c1000c4070009007054001070005030b17651900090315182c050005528440c00d07030342980865941c0c070901103142404c0c0a9405030b81090b2400e80f2040001e180881e0345c0f0500003034400c0340281c020000c501009030307005040303011503000040050b540002c030303010264a501260086400e4040ba05000560030443c0f1120b40c407406000903010300e500850b4540002030804038040c10307580b035801c04c4003060350740c00000a071080080402005132030349030039000d101c2c000b0740250 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 106965782 1250 106964532 106964563
    0x40b01030207020d02150f0a0509030c01050412030509030109080a030905010f0b0a05011d0a030b070e09040c1211030d090503010e070f050d050a06020a030e0105060a030b0703111b01020408 83
    0x2d440143e2180034284603400d5050351201180c0c016000111003501510821480d00d60f000500b12040301e5000c000340501c01400c0b001e803250f80c031030b0034010341e002d2040b441001e401e01c03a04100800801e0040340030b42001107018002064083c801d5483d0440c9500118040001c00e0b41c50400100341b141c00d12030701200c0b2404030390401c20701c59030f0000207003081094490750f03040146a1010008072240005281e40750100600640d0398280c980c5840340c1e40400440390400090b01c0141e401c03000746050721302c1034000e58201000036801810421070b1000052a10f00c25182902184024502d60710100071100c0c0540da240d64001800c0d003440100350a681d07880b042140268085203007030020050011a2404403102150340500c6050701740781060400f00c1803580980003903c0410024030064054102c0745024942c0f5000700f100e03940310070402003040401c0c0000fa0030400c541c00001c821a00030341c811402d101140012900303103244403e0102d20121100010400d07130350003080401ca0b0301c80400081c0d00540c601e4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 106967032 1250 106965782 106965787
    0x3120807090806190e010f0203040b100b0406030902030309152a0705010f020f01020a0c0606080a0b060415050a09020a080106050325140c0106060801080d080a090201050909010303030b040b010302 86
    0x1101d00340c0e01c200107045a580200e401c0b40c14a06030509a0106031174500e010002e114841a65514000940041f9030949000780c020340040c030a000948548026a209035900e541042c0c209101100103110004049070036110030081c00d4034a546190001030300201d003a40c0d20790340d81048400d03040041e41d11101510140314895a803d0740c4403000c1480001d9810a290542826204110492030007100300b8240010703502c001800c841d0158090800c0844a00503c41440030030b03030b01d6a81d05d683c0c814041016068103400c3d00891428a840d4208030b00e01c2c4906104407075040c3d141c8000030441e9205d0341c003441c40a0b034005020400304c1e400c10400307401007849003082420f500d0185401000c103c3e44007882e002e00038002d01e01c070310301d10700070b032540031081d80c88500c015182c07520440f5441c003c0055004010100e03070a2000011a0030380080c0d40419506240daa05103651900e051400140c03803800812814480c06110640c8140c0780c0404980c0214000c0d034001c80c6c1160540103000855103070b040711b981010b004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 106968282 1250 106967032 106967039
    0x190e0106090e0a0218070504180c1d09060409050f0102040608041101080c070f080d0e0c01090801061d04060b030a0305031005090708160c12020309010306140307050913020a0312080709 81
    0x4907034000c84007000d030000186691b03503000c0c411240d5101d2900b060440c12980001070050b625560301c07a18168000340c03201390540340d1040341c0c440001e505082d115444001d0310000707166030410307800140f0000d00c600d041b1281c0070300050300f41e03007a40c00c80d400c1040041c3c9008200010703c0143d1400000f0000d081c00d203071015041000030640c06104004029001c0103030075014104003c102d0303048520f0340c511a9130422071803001c0c1e40c02c1510f036403c1500da540080c0196402080c0d00e40d06129040807102000c1e40100c9a58504507103035414a0020810340d0b00595580ca0502c0f1514240001103a545c421f555403076483c070b404451700c68100345940202c0e00400003642004481a08010529000341035065203414403104e054080700d0020140c10014420f09d501901c0210058000001c1c02d08040262414804243c4401c02a030320007014110300c551551080504000d00d0814103003103034100c9440345004800d03a4243e000b00d00650441e6100300c0300e21f094840c000365425030042a55800002502c1c040305001d15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 106969532 1250 106968282 106968289
    0x9020109090e120c03121810060b16020301020c01050403051b06060d02040f0e0709020c1b13150f1203090603050f0402090903040e0c03070206090703030206010b03190e0106090e0a02 80
    0x408143c203803100c000960f00300c1000b040064809070580018001c0c02c1d07241c800b001d06640d00d615044500144140000740c194038007580101815901402489405c000041046070280004c00200b0380c0c06550030804080200420b018141c4164001d4603a90343d111100e0494811518801c1c2c08503c1030741041c010f02a00c0d6440c458108000c40e0100d8000c1070308112145408005c1c1100c0041610b00d12503c040064400420340280030b04070001c005540d0810425240c00309155850714600d54090f4143d00043c04910003588004c80086200c1300305031445484001070031984207941c01902c9841d005100c26420554481041d00190130f50346414001402c19012320311000070081c01c0203216180c800c002800a1800b082603900130402c20a241031241086000661980d10a031681e03c010702070800061a0024001030000459605600a0926a10345413001c02103400c0a00070174419103500c0c0c610412407a40f4002c20010300d0410780000340c03080c540801e5070708603211882c43c148150004940e400250b0b4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 106970782 1250 106969532 106969543
    0x6160906050a171005060a080a0501050409030503040615050a09021206010509130b013014070206160207090f050a0b040e030a050f0c07080a12090f0b0702040902031009020109090e 79
    0x303a440f141c2c5540c035142c1c2d42d05000056026000750760061404102c41001c0340d44580f1081c0110b80c204810030650740c81d1024802601c1100c1e0010300800c400300f003c9800610954480307444240a4000125066180d40000c3c0304007556134080e0520a03000b0807115070744500b043d14990400d2090824034a0a0054404140c00010b544503809015a60f0040f0100590080004650310782032042d00c002542d48030441c100c44201c00050807002545400c40043d00d0800807000d080c003403007264005000603955051ba100c00445c050302c0c940110300808100050180b15030140043d403200d40380d4041018602588060100c8081c2131101d40b00c1da041c0902e8010390200401211429840740c60300030b503a1950034010a00341c0c82151a1191703203108503140000e81035004175024502ca0710892190420306100881194000241e0050000070304c010b8004008004281c8000e00c1c2d03041c406803000c42d580880d0b8001904040b4584041002140c8414480003103681c4100e00301d000e80000354042144c18045460b8a5850 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 106972032 1250 106970782 106970807
    0xf04050316090f020a08040f150501091a0303162303030c0304050c010f09060309061103040507080d0302070816030210090308010503010c0306030507270f0209100503040b041704030506160906050a 86
    0x2c41e80d605034040c0a102114181e00702a00801440300c2d5948200308030041000074400141001071010282651602100301d0741d03000c11400000b141382c0343601d40300c500c000c4156400720104991384140c07200510f602400914841c40000e031080741c403840c2c24102281400e8800604604000d03210840d183d2040c0c000d411082902c0c12840e0000d0b6202c52842c203a80209081c843d030401c490404010007007000400100c4005031103a841c1518409003406005406074000c001005100f1a4184040b40c5003003c0c10111203c1240a4030440c1c400302d40c1090400d04990820105400207410000144480d007000d000c1c14040144030f1a04001d0396103142c40d05901e480d807602440d88216865980c0c1034a40c15654480c034858006050100207040144008200950000c00854010307862581000c00d42c40c00b400a403071195410051b030b8a1240d42d43c0e50341078410000c5070030720030785180305000103c04102c04100f402d00c10042003428a04544804001403e8810b0f66488101000410004802c046600c0b41d0081443c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 106973282 1250 106972032 106972043
    0x605130e10090c1407061b08040305030103020d060b06120105030606030a0c0b090307150201050103050c18040b0702030f0705070302090109151a041518081606050f04050316090f020a0804 82
    0x51141003040b80d00020751100c0c9483e1204c081985014840983e00900208483c210304910101c0c1081c02910038140440307018001c80c1040c00100054100781220702607491150301d0000c0d50000e100000b5116400c24a4691742c2c41ca1600014840c038142000b030a60440d900728000c204a00f503682e240c1c1c07502440750050298001010070b0000013070b00d00700440e90150041070501c440c5041c401000a000304401d03c07055419201f0090226901c0c1007007000308440c4050101400441c2c2d5030390300d50081c1c07140c019001000310321042001640c3d003503c0c0800380040030300c43c101800310140382d03004200e428181038102907801840c0c00300e0594031901e0100b00030112a8084641c5101d8022869280294052680008121012030080a040b42d5001c03c1000c914000e0503400c400d4070f602d60010380d40d2800303401185009204100b105100d1b01d4003d00c080c0c04c0b41100301141c103107020344030004281005a806008455162230345014801004180a0f00030007000f004401c40c10400d101070b00a0410074003038409000b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 106974532 1250 106973282 106973291
    0x151302040218060304200d02060a050307200a051005060102030313030504030c090b0916050405040b040e01111209030702010801050904060f1a0a05030f070e060a09060605130e1009 79
    0x2c2c038010585481c00c1d030310001c0501e512840c2500341848009000700c0e00c940c21400701c5080c41c41c10300d84520569131b965005004603013040300c0d9003c01d0b20706520140c190414003500000d440c03003041402241d001c4601c140c1015009110342858681c1c03400400d50310000040382050200b1400d83d80c0082603d0b0b1000070707807540d8050303030f50f0500f41511a40f040340c0014000c40007091010030f8180c020b80085042840503182c0e00751940d100c04420705000740725402040000e00c1000304001e2032526410002c121b1000400c000750030903218403000c4c00c4031041084032009160101e5004070051007141001c2c1e00a405a02843c40c06940d540001d01c204814000c852040f0000300215003803192070f9005040c207403190401004401c45900d20080c40454440c5070a200701401d0b60081480d050214503800c0085030040240340701d50520901c040c0503500103126941101c642c031400500070549001b40c40091600e0786519990b00d0b0f0008069412130079603041281c20031006c400344103075218400d00c42801c6400707101c00003a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 106975782 1250 106974532 106974547
    0x2303060f0d05060702011a0102030c0a0311121c0b01090b03010605030a090501090308101a0415020a050d05120604060501080402040f060f0605030105030d09080304140a090903111513020402 83
    0x110380301c01840700600342c0d200e000c1c01c1000f000e405601c0140380f9070714054004851140d030780049960b88a0b448860076503402c0344641d4000a03005d40031003106a040503042c0c03005038211904d407010540104403100301404082c101403800c400b2317a01c85d02c0803100e82031803c45680d9007802e903c00310750311061168008000d0300000080011025038852440d443d4403000031700a40310b642c2002000c640b0255058482c64884040020703e08540d01c000011340c91300760500f181083e00c0c05d0b8018509402004842065001c0c079060380000913428040614110042d0300c03a180c44004c24055102100c2d07008210a0041d45000c201740107603a040741c0303400c0c1d01541c101c402190042c0351412a1f4041c00060340000c1d5440e0603003c000ca60650081c010b0f5050b25000d41c00c584001a11000803142e600081c4180c0c04c8a400401c8280495480e00e00300799110714024061510160b61042d10b00101d40645800ba00082e40000310002050002c1c0002d41070803600c5104070009040c000030300c1c01c6180c640003000307100d25030028450 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 106977032 1250 106975782 106975789
    0xf030c090d050a02040c020309030d1d030d09080705040c080a0c0c0215040503100603030e090903041a03091516050c0c03100c1b1115090d03050a2303060f 68
    0x4460048014007841d980007070918046640b405188001c03886542400c2081941a100005a41041800400510002070821405c0e0b4070074861071441c00030a0712070baa50000940b000c001444c00c00740c0302da8880c072a20346420011030030001a82c00403032240342055011b10b03020354080381090b0007a0381c081000810845010061315450b6012000942200b403030031200c1c1420301500098400c8440030340a4601c1411030340c0e8684100c603514040200400c1442c5542c10240c204840c400380c1c0043d8a034226460a81c680b842c182100d460240c25880f903100000c00c000c101032051010f05080c289020420805003842c8055481e0002c0060405003000404510000510030800c6221402c441c05420364400401010012024101e06030100001c5540a0340000c1c580c0741c1c2d09030854030079410039001e0041d141c4800400c4802c0781050114081d90b04140003030341c0d481e95906c3e5428103191081d1101a41c40c40000c0c0c010740580303000f04848040c440c0104a00682240920490f907000804903552140f00e401d40703001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 106978282 1250 106977032 106977037
    0x806040f0903051e0f070b280c11010e0d0516020d0b0604060509040305030703110403051b01080c09091306060b0a0309060b04050915040302010b030a0c03260f030c 72
    0x1a55a10381000040c070141600000100580b40c4807004101c00000081800001c5105100c00c800d02001d003080044042084120a50303003000302c1d0401903603201c00d00441e03050400c18085c4215440c41d0358404880a554000907403410340244000240000842000065259002d000341c60080c007400141c502d900c1814840c001000e59401004040b00f00c089003440403800e802250303000e01683c0b90403804a50361402c210614412640359988502d1a40d8034201140a8034085445410760341d414000400092000d000781617140c600800c070000101d0118000600291001c0c10703018000c0801c20502c11184c40f11144142d00210003602c1140c0f2008510709000100281d81c42410000c4c1d021406000071035164000004440c0682d1040c0304031039080e010002100c038182e0755844503a10294000444c1d9011501e440d5000f8024000001c5010501d008207080058442e001c45404410f80d4041c0200200388000c440e4900c6007020f410801070701c0c079611a030144580e03045000c1104000c80042d4140c0040d0b0704 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 106979532 1250 106978282 106978301
    0x1804111503010e010b0408280b0106020307020405060a08150903040306020c100606020d1d040905011a011b0210050c10060b040302040b0904020a090209040615050910020c060307080604 81
    0x2000c000034800400020064000b030003020032580c807100000408414560569043c0c480b41005002e00102c08034820b90b00d0740e0701302c24a4050312000000c802c041081010394034002c1c4140e4024594851840c41003000b121001842d151141003500001d21100e1000507083e00f0110355200d1560468403110300f060f00d103008a600003000a0300015440f0400f80300800c0d00b000c9001d08020621155860301c1d0160385591541029600140884030a00b881032903208a0014158024100117032209094a5103070039118100c0b88038804405981d203082036540c5c080d29520a800d43c1d00380401000d5026400030f100790382c030128032908000003c40c1080c8102418801848044030b000000c101503030351070184c0e519035041440182d22442c50001c450f822804e0001146115590040080a4480c01e00c41d1100c02500b25040c215000b0f83e94400104450b4512164a8512032098807820384401c501d8081120240e41c5804900842d00415102c041540321032003a25004a46030424030301603036591000c10002d004212 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 106980782 1250 106979532 106979539
    0x1030e0102091c03170f19150b04050f060324011107062d02100c0306050d0c080606010203041a07020f0306160813050c060c031204050d02010614180411 67
    0x52141d007004111020b2503c2144680c03102c65562448806902e03410100f100c80c0307000070820800240d242108100e81c40b1115800c0a400501040f90f100c0000c00c5042a8002c03080c1c0050005040c0490718084c440481a580d0480311540785240203060440154110308240792041d200104112003a80500810300440304010100c642d0390795610002080440742c144252003150000c40d0381c51080b1140702644040c0341050b00202802c0100c164248024270b4401150810107a03240008141e0b03903141920f01e42000c2c010002d141c401418a501a421b080340078001e40e041d03500400040100340060203a0f01074074000f40540588541150010698000314102802d0f41401440d0402c44650100340488a80480755540c4151980d0382c0c5034441007644400360040c000c3e034030007001041c1c207140c0440202000805001902d0030006d09090b030034040e2206540864140c2c01403c401c40300c803582485404010303c40310402d0000c141b60f00000c42c40610080c0c200600c0030030601c0001e410b105000158072205180034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 106982032 1250 106980782 106980799
    0x20402070f06020d0c090302030607180807060305060a0501080f0f0c19020d090e010f091e060b18040903321303020109080a0c0b0a1103270405040c0501030e010209 72
    0x2807030400d00079880704190901e603030700c3c101c5d1141300c0328820103078032060383ea0103001400d00307403507046082d100000300448145901111302e8020618000070b000f06801044507440c041850b0400404014101c10035420650400400e5000c01c010742c540048040d8005601c0185684a07403208030400c03003207104500541c2c0c8a000c50481c40c0204d541d0011344d61302c04450559403501d00584618032115241c4080c450046140040c82e810b01c1000e2080e0300410540c220f601446201e50305405011058508503406021451408220180c411109000ca800c060b041120200b040c50300d66070780940883c10b610140025000c40b502409510740c0312182c064034000d8201000d43d100e904010002d50b40710820700007280003c0d85c2d500005140c2100054003100342b82e2010343c1d1110356003084400100e80c4c1216400c4401c11406003c95414a03030284002c2c05010b0800d42140c0781d42034510f00c4543d03244040ca40f80f9019a1401d410000441d203c0304075407041e66000d10b0041484088564880c1c06405190704495001084 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 106983282 1250 106982032 106982063
    0xf0c03030e090f06062a150609010f1212051210090e010501150c170307050403030305151e01051c0504030206090d090608060105070501050a060e0a180f02040207 71
    0xc800c101e06602801c0324040c485580f55041c45102d004152807030b981024083c0240c101c18801624105c0e15209001050b8002e22429185103207820606880700380603007110401d101e154203002c1441405045040300700d0b00068a08540c2c4081001c40740740282059802d2009005564420801c0b00c100d40705000c010880c508100c1600e080741d12082c8190714203c0e01e004440c2c0d110040c10301940341280c80011400c4607100b911a41039445120103807080b100410b01102c060124444000a0360056096070344143d1a68210320b8040c04680c0c0280000909003410251444141e460010b496080d0b0901040c2c4d90300c0700070b00c100585072070140301103c26002c803002a4407401159036a02c050b00c5603000e07908654054a410ba481070301e40d00182110300002c6e0302032909111282c05020f9558025406241440c42c1c0881c6450b02c50840700291070b0b081d11241c032000c0800440241e102e00e0346e0012080c070810045c0d41c2c22612011805040c0700401408100014900c0080d0b43e220303419030314070b16001130314207140015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 106984532 1250 106983282 106983287
    0xf070c020424090c09030804181b0c021c050a1203020c01020c150a1e0b01050412050a060b0102030906180604030206220905060d03050304051c030b09131703040f0c0303 74
    0xc00b80141034005103068513946109101c0c82c2e141040b40d400140c002d00d0281496841c4c88942418200243c0013501d0b00e818001051001180340b0600180f0368078010b601c205441001030b00d00c0013801ea04071041380d031400180414004180781005552001031a5068a010030003074000e80540200b404103944081002c40420102240c40c3e800d094003480110101d0f034030703105504101c4603a40246244071103a8110100620001d81c00f07411030000c141009030a0590301d02010040400e001c20846136604518507120401140d4000c0c29900d40003400a1420700c1031140c0860b1583c0540101c42e14110400c1001d50566210602198081d41d00a4070b20380c1c3e41d910b441c0c4c1c0e182d001d0410f0810303685034000050000039401c070b82d4407400c1d006840c01002e01000001350b440c212401d8101070010b452034080c24440d0b426400c0101c01240174480750b600c1c04140b00302e0a0041003c800f5004028801105001e018000040c1c006540403010007030b0307400341d1a00d94840d4280000d4004500900614084105601005164 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 106985782 1250 106984532 106984601
    0x10f110c1002030c0301120305300a1a010c14030304050a03090b03040302150705120a0b0f190510020304031a06090a090b07260c0a030e060f070c0204 66
    0x40803401c640015092041c03810891204581d03481e0703070050a10051084502c401c0c032841c100341c040d25090381400900d40e035032001c010300120074003812071040d031044844499881c2551b80c410b098000800030f104802071101c06d032a1003450050f04010741c3d201c03500c082009103640108628240c0003201c0d00c0c0c0c0341501c1c00b190340350590b001c03e41c04030fa07020381300050260003030084034455945036024014040c1e15202d4000c00da00090001420b00c0002e000c400000c05e20301001d28401d1040d16004100c500740941400082c070100c1e40c440d4091000720541c144400709c400c2c094000c58406450ba25000e20401804034110f02482c1c20041603000e003218562084240d001600d801413104036803101e20b94881e44112030454241c40310080158203420300013107510380180340c00702c04010801d000d0703100d80844103048807210504460400d44544041890091aa45445076032030780807500c80146085e0824803180b0f0300308600245603004100340c9510714011501c0f15003040f00e0110320036148419202c1e485045400c1c11 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 106987032 1250 106985782 106985797
    0x601020105061f03020706020f0a030c110c01050717090d050105091203011203200d020a0512090a03060b0d120201051803040b0904051b03130b0a0c0905040b03010f11 73
    0x640c203020101c1c0d0246041c40003080e81c20708900f920366140348208015006500b0001d010b0710320a03805e0104100c088a14002801000e016076400200c44410803405041901c0d4040040c047da07002500958660740c0140c2141d90b23039038002d00311a4050584500c400e01e42d10902c1c0c0300c41d4101501440b0b100810005411250007040303400c05031f8011001c02e298450380d500091060542c0039489016903c0828002c500711036017040c50400c024802010010018601010b0680e9000164407030816802405418018400e0303070380d44401c00ca131a200d006e00000c3d4211506010142c4140c0e61110b00b035200303584205001420b01d41c84001d010362050229006070080034115201d510101d0b0b04012410100c9002c41240e042c1c4000b207400704e08080c008418000180780007442e10b0205080100d80e40c040100582c0503501c51103000d0110200f100d2686481580420b000d001d4140c0b5900f0551400079440d0000340140c10383d101501c0014403c404140003078050204285480d00d014580343c0c05400400100d0b0040604 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 106988282 1250 106987032 106987037
    0x6080c270d08120a0902060f090a0510270506040e07050405090f01060e011e030e070e040c05010210020a09122f011d030706050c070806010e0103061802011d061b03030601 75
    0x4a0395505503144c1905c4129100a42c0240308000c071400005421011788007030781010304400707070654407000815002d5200c40d0202c00450700c84800780c9900440f02c0c90b00c0c141741d4901c1c1e403901c041b9440c00000c00c032940264040c100d403071488800041c4040d44a1815a001400c000302900c0e05070a00e5044046254400e0051000142a035856600554003d01c0c12065080c220350700d040180e17450001c224014080422826020301a1007000078001c00711240c924051402440d004032254a480006450002c10b10f0115200d80d00611116550980145070001150300800c446803450440e03103032500884100086250380946900c03c41c404464800040403d04142a2151a10000f206070050b15910325600b507164943e10107442440071600c680054414441400110780c02e403600e81449034207105007600007044804280c0010020320507540291850b030681e0038450003001c207050f0002014083d2074801c629000642242c80d040d00d4988200700e607038440340001941c0700010b000702d05980702c0d0f00903500c4600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 106989532 1250 106988282 106988317
    0x70516060c0e01020628020f070c0f05011107090b04021c0c080c09031207050a050d02010b09060103020c0c1005040b040905150f090a0c050712080601080106080c270d08 74
    0x59400085c140303014002c10100d04588145000812040c00e0400041b801000d80134412032200031311840c0a010f030944501d000c0042c02c0c0c100410860280180c1e8002c50422801a0b45991002c1001c00c4130015070b000240d0205825540001080103071240e0f2a0005038401030981100d1103441d80d0303000c500385542c195200c10503512141c0e0401043e0141490307041c0c0c10380082e4207004848039088011b00140e40b0501c2514031446003925624105a540d00488002d0307515402410b10524146072a194040001d003001c5081c141c03000222540d605110b0100c03800f40d40410300c2101001e02403001c0d640145070071280070390f4541d200d190f100d0203400140c075205036881e0284440c09592800c11118101c6090240901107280e03a0001e044015111480006041c060108507000c0440d54100000d190f42c44280c86a04950404000050840340142c1c049000c000c1d40c0401c0c0004490004201c99400440e8000c4030380e50700c1c1d030048042c81011a40880c0b54810324003d80a0100310340400541290b0702d0300c40c1642c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 106990782 1250 106989532 106989557
    0xf0c1e050102160e100504050118050c07110f0f06030114040501080a080703080705090a06031e05010311060703050d0e07051309030905060c011404050c040c030b06040302010503070516060c 83
    0x90f501c4644400740b000c0310141200c00e211400760098135a91020380148121501c0d5560004102168020307040042034070440e000003034500540d8061140c0299003281698a80340d1940ca0302241066522a914030543d80e0007591401da5640442002200c04018207070782c2d413075948041054104212211560055003000c00025613800f002c10188080383e000040545045140d5904031541c001c018501c0d020301c04148100748242d21003280d862b01420051f00d00080b100840b440c102500c210041c140352039181010300600015640c241c0140c406d02044c4c0d8607a888200601d410b8802d0f00800002204d100d00c0e1901501544800140c0501110320945100112800d00620001515111039010f0b000c1503941c502040b26080100c02081d0b00500e02c0000900713415007012001000900b40c4081e00c01354030056280f2407501d0700d841020800c00c190300741008140c04180c0401c50170f0245100c042e041c0100413000030a61030181702101c460024a0840001054691130150000c1c01d1041400b40001d4900440c2c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 106992032 1250 106990782 106990787
    0x51006020111090d141204090204060306170c06090103020903031314010f08070c020a15020c0405061c08030717130b0c030138040e180105060d06090f0c1e0501 70
    0x9443c5a00041d14502da03d11440d00e4442d00e01c4201d010304040783c4900700395030700c9821a40d070181014003020b250250342d8030f00d481e4008050300d800e0b401680080501d40c52500007801c0c0060320011280d0b0560f00395440c1d85480c80141c00a019040741c068141c0400100324405401fa071110302c0075507000d400c1512a240200c40115030303540c054488580800c2022010561543c002c0740d03e2075030b05100030200500f058032000350081d42c034034505522000d0b07801f00e26650300500c0c0601440b5480182900d074411a4200800440d07056420844003400806000012900c800e200740c142d000c0511400350703820424140388080864072003480c80e0554203c6922001704540d5103200e412030b41212140b5180d00d501c0b00c11300070030314540c000715400b1100c40800741c0801e40c19a83d400c409400145101001407940e8501200c04034200180000304034003070f0340f40400304429581d403041341c400055040310001454801910304140d00a4500d0b9000d000c10b071100c000002e04042c041c0c1c0c803510f070010007408422000c0d5285e005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 106993282 1250 106992032 106992037
    0x60d1124040e092d10020a080708010911040905100503030c060405010f1503020118030501050a0b0102100c1b05070509130201030c02010504030203031f05041a03070e011d07030906051006020111 85
    0x40451003400b144503e6103109131003484c01e07001e00303003e401d071100c030342500700c0d00f204907805440480d001c60030341410850010f400c024806e0040910010903c400200f070914420184203d00603c0b001b1550303103002c200444544001e0502a00313002d0122980da0f0042c41200303681346011034044455600b042200c5501c0845406084442015a42200406400d550041d140f1842c10706028902082c00100000401c04c01d0081ca8014000303004001a0000302d98002420244906052002a0b007400110b00300c044e405440607540c02e59410390100012100c5c5007003414001c0c10b51110750300500020a0000d0a15103041c6050110700c01d1f2800c101001340408140e00341c8101315009405a001400024616950113030080b5901140c1c8402a42c419120400503086039810401234503042854125005107090070801c0c1d0000e412000c12007442d941c07401120769105680c004a030200c0410401c0400c0b10140607400031030000d0b40c002d40901035480c0000f2803400b2140030f0301c1100d006600780500c0b01d03c4980382108 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 106994532 1250 106993282 106993303
    0x7030806031e03030703090204140109060810230403050c1c0305010806071d01020a02030601031520030a18120c0215070b0c03060d0f0807030215060d1124040e09 71
    0x83d6040da41c80c01c00c00d5000b40240042680c2140d03c440503150440d000f02c00310b50203418080c500055241c1007400803490180c000c0390000703465250144a0720a007039100b01e900b943c06400400403049aa0700e1070304a8283c011001000d6203441800e140c0003100401e4101c1c0300e101c4501d40d80800a607a81c5580f416640c500540d0707a007002c83d084960450800103410300441c100d050600403158240c02c103601092810009a105a43c02e81c41c551440b03202c4201400f8214030f032032640595402102075503000c603034144005840403a5065031540d504c00c14841e507040c090252900000c0754042e20144610113030283c2e00c40e00040b4890100103030f03001d8140c10500255441d00350401205403440c0e90708404926035500c05031500343d21a4612203008009015005961202446a000c0395222025458064500000c000e400a141c0d41004104001c0c0c0e1149920207240e41d4000704043c0d481e030460b4020a0b41c4082c0200721407031508801c0d941c0d440c107044e0355000304200c0e41d0506038403000303503281c1c400c036030720b8a48214 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 106995782 1250 106994532 106994593
    0x103320f370804050d0302061504141810020c06060414070e01050f040e09030a09060309020f090a06091d061f0506030403021906061707050102032203080703080603 72
    0x380381400021404403030720303288501d0304540b50503100e000143d81059000002c80040c1c2c0312008000c41c8211300c1480c149012070550303052181c9c0401300301c60149858028025a64185000f84022180070100000c00c02d03070b0909071045695285c85070b074850307e544045950601803428051081c400f00c000c101540c1c0314078001c0d5545010b4645000c01102c2c260f101051000400c4001d000114610b0000c0e15007a00840d00310004544e10764030001c0c040d004078040d034408018545806030f4180035859040d18003240d2981214900c0c0301da540c6a420f0ba00400341c54000c00c2c002860010a291043e05080b5001300401104003158025514840d10600845044403080f0301030040d000100804d0400601942d0041e10038010f88d001803050307044400360081a402c0c241e034540e0b11510100710940741c18908042451000015040392428800041d54a1241c400382c0340b11826162a841c5035808140108805541d210a00c3c55580100c0d080042062000380d850302c0c404d0040e054401d504050080400d0806000003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 106997032 1250 106995782 106995853
    0x903050709020c0102070210031d010b03030403020103050a090506070f09140d11060d02070807171204030e010903020306090106080105070807090b0307030603060e0a050d03140103320f 81
    0x641c02a01075048481d1200266400303000800045e613401a218206807840e0350001083e44c1d0044501c00700b84006448241a0b0b45003200303020540e18084211001c1d2a020308021801d5100d03806104003d1030010400350172402284180184503911910240068600e69141c2052580b036000381458a10704005060b841140c45801900182811682c6090804020503442c24080700074101016603100c00000c4500d6000002c03006e04205280540c1300000040001351030420400c02c0c0b4000ca142d80207040a01480700e01000a26541c0c0f094603840041c3d540079007590700078100380d60b0040c042d19843c040c106083d400c0000280809100702c0c42d0503c00c5100e031703484540817403502078069880d500c046c008a041544550010000c01c00e503002d0016204030090050201c000b03907080040c02c1000400b44042014100281c220426443c010440d0540380c00c0104240c04035900003590b00c0c1900b074240040d4045003c101d6581c0c08501c0070070114404400b400c20b80300a49040c00703403410000e881d081101c2c1010b03a070703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 106998282 1250 106997032 106997039
    0xc020d02190b10080f101803020c01120e010906151205150c0904110c07050306061e0d060e030301060905220513060e010e010f1416020a020901091b09030507 69
    0x3044181074103d4110f0441086558640c1364840c01c00c5c0c20301811010540c00005012003002140c8200d40c010004260340607801c901c00c3c0d80080d01e030b000c208080f0b0f041011070400c64002503550740c801554116408001c01070b42c01545040b5010b0190480441c82310407160300700080c1d840c0a49800d030b58056111014050b51000c10740f40042c0c421003d000503202c81d4003840f00e500c0f1a01d903440b541e106810041c1d040c9440d0320106107800d00e000803e4000b11300a40000c13040c88419200e4000c4400e02c06820748800c54640c002001117481011000e2002c1c2005003000340031803c40e4408002907040c0c1d5082c0c0e94507010b05840304188020340e00e6540c002641d100461015141c1d80603140d02c440d400c1078190001c4400c2680c1030701d8000c2a05c1d40325000c040070340d55440d1300990b044401d10604071440300e0000c040c0803401c0000c0c0c0c0382e240304c04000c2c03458000110802103800080e10038000803c6c49540240301c5d44880d42c55040d4580104050050048840507102c080b020b07841c003900c6071350102c0e82c6c0400100700b618203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 106999532 1250 106998282 106998293
    0xc14030309130906050c031609050f040e190323040302060d0209041e060f0806040c03080f0d060905010906090209100f020a0f0501020a0206011205030a0c1502030a0c020d0219 77
    0x1503201d02559030550f076154500000b801406090300820740c603102c0b01d4907410301c0e004810302003915040c880b051100003d010002e944508090022501d070071540025466a800041400c264020091080f01101070286000f0160405500f25090446070410003412031800340c824030710310442c003010354024002e1100210111054004001400016001144806480004420800c0e151281000707081c3c940405008180742200c1c200010007011009000380d09107034441c61a03403481408043c2a1280024800da20901868229500721140d5070040003a5607071280202c0040c4002e018102e00c960810100040b007000c1030081d500c1d019002004d21070400040f88050354040391910000c800c1d8043d40c00c05a000c21403c03c1c030344e15410300503800981d9031403860f00000d0400744144c0200d2010050031501401054000081d990368000601701800d0001d801d080511800c24145a114080340c00001000300804980d04070008105081d0210303008645030907400c1c0e031214002ca0b4901160200a24072002140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 107000782 1250 106999532 106999549
    0x708060a0510030b0a0516020705060904111303060606030510031109060418060203010f05030601080a060b030a30050301080307080d0b040615080c0304030807051c020c01090c14030309 81
    0x3000b9400c0380c054a5480c0e60303a42644604a582e02c052079642c1d0100003114100441d8050518010310113489280d062030001180e501603045494025685d44160030202401101128138040d0f42a0b0310b5210079640380b504a000d020140103035000030382420007044880c1c15911241d0705807548880980e0040c40e00c0000d0112400c002401c46a0040c0c440c0003d5080c50b10014441c00001d0043c2d002590360340c10811a8001e0700100c4c1e02c841e02070341c04100108210314011503102051079000d00b01003070500340040040e00c3d2004c40c01010744400b0300303681c07100614511840044a000424a004c410003007200c04140e502703010034460640d43d41c00c10000c1d00c0020790070340c0040c01c001895550001e0400d45000205d4100c882c0c40c1c000a0001010111440340140c00680365a40b18400401083c07540c5800d40c1c00600d03001018000c0c20900001142c407900d480400c02c02520308081102e030464407440020801d80c00381002030b1094070b40b1406040c01041001510705a41c5010304043c008610744080c0200303106020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 107002032 1250 107000782 107000791
    0x901120303150906050f0f0303031303020a0c090e010c03090809040c05040308040b0901090b030c04030f2102030a03110403051b01110703050c040506030303040f170c1501030c080708060a05 83
    0x1640c96805002c0d0903142d40c0414081c000943c0d00060541c100000d0104284600442900c10350810650f10015640001180c1c1d200786074218000d21911316140036480e103055031400429400d00e840001c07034036106507807002110080e80c02c001c3c01040e00c440d4050b0110b410454001c0d00da1603041000d6540c82c2003a8200350051701c0b003850094a800d56039106c01600350803941001c2203005002442c20f18a40e0b12080703420180c42d0301c800843c82c500b840301200c01d1910841c44020a150030104440303080c40241c840d0b0070b084901c0d01c0498511488140402034503039111001d9100440d01e04241c09043d08001d00c00d8400780c942c0a03004249220900450b4007029460022040c100030130000a14040f000621280000354400c030020300b0b203000c0c600700304001da5000620070360180d4414401c201c007040d8003001000c0e00503041106092407054034041d00b21144141007035400300384a08149000c11900560b0524100d9002d01610f400050711142121340703420491017217049d90762207440800c3c014189607000b140c10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 107003282 1250 107002032 107002037
    0xc030e0c12100501150305010f061704060b060c010c020111040305060a0e010e1c0f08060d030804030e030307051501050d032c100302120a020a0f0c08040e040f060e01020909011203 79
    0x910500520000e0f03407026004060146107018072049500c1e058080d95001d004040591048c903801c0c1400108090a066504001c0c180303418045410702019038412460b19401902c169a038100d01c91056004e81b864612410040d072915122100f004058400d580650b60f0103006000540c0340c0141c6240904191502c0c0b5440d95070703a031004407050708200018072400031300040019605980c1140a49010354044207081803101100c1000a6680c4280d04900d4059041c01d000402ea1a14101220341c68000e10500f9094400029400240300c4c000900005071120080c1500740382e80c8400c1444020740211000070b01194844c0014540c1c0403091040d61424091050042c03051170080c0000b036130b9030074502041004207900003205940041081c10301c0e0340c06542c25005500d401d1808071300a004801040c4840c040107041d444000400120004980c0100400c1c0c2030888a4102810000050700d00b0110441d0140d250200c00840e540f030600075074401003002400c50301560f05c6c1040080d0342e1200c12108404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 107004532 1250 107003282 107003293
    0x70303150b0a0215060108010f05061317101a0109051e190e07020c0307090c03150b030702160302010c1101031b020610060503060609062d0306040c030e0c12 69
    0x4419103048007070072140d480355004013210700c910004002002000f42c40c40381001182001440300e002c0044103281240e40689000d541c1d85148245940542100e802c144600e8810071243c0030305030f400281e40c04141d680c6190400581c8107000c0c40c00d05460b00d4929040c089040c0c848104201d01c0e00b1840341c41d0030810903000b60304403000c5100240021000000c03c002d0703183d040d00c040c4403030070400342d00d5903000569000a150144c0c685c0c00103a070f02c5005110781101e00e80c40b1080ca940d56882600500200703c0c0d00c01d0905140c1ea180c0c007100344540c0017250000014070904441004500000020800300c0c0d4060f1103200c0700e04603075102c3d04000c8002c1c0781424107142d01c0c0e401c4141c80c0c00f0824032050a85c50035a0142c0300e181001290030580038600d500540805c0000c0c014010706d07584013400c5070342072101110419900c0c40d40c0400e07000401d8000d514900881524182512040b921200561064000b00c60401c0a00441f01e4280c0440d03901c115600c0c03160f48072868031000d80c2440f0585000c000d60940481c2c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 107005782 1250 107004532 107004539
    0x130f03020f100504081507080f04211b06020c0c0117040308040206070506091b04091a07030b030a03050d0b06030103030c02040518070305030403020a061716050d0c080f06030c0607030315 82
    0x10714001488116201e010040c2c000c200c000365024502c15084009c9151840c03240c140340c0c451058003c504c2031921159911408940d4003140952454010300078090b04c100022091070824000a401202c0080d03d54016600069410744c490080f29030740c40080c042543c1d89403105d1b01d003103461a01c0108201d8010348100010800700e41c0801030240300c3c070300030002482d0701411440c5011072408020503880c02182041c0c1b84000040703503d41c4042c14503995847d084040d80d48e65000305e0150540a2178107805d070040500c0748052641c00350003440c51b2114003400707100200350071040c42010303c4248009400207031116481c00040c90180c0020ba0003440250401c0289440d22040c00d040410381c0c0c0c41122542d00001c0d0800450038900e882c0030040c001820101e00320b50520f50840d0500100624190907440403603c0681220f000c0c20999000201e298000c00c0b14684548024007056410b80d0030344500032046000841a03d000a0706c4d1240f1100a00524103252107650150050b141100c0b5070800700d2038144020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 107007032 1250 107005782 107005799
    0x206220902040311010306090b0a032904030807110c1309020d050106090606020f0105090d0f090b0f1c0b011b0215030f0711010e0d052d130f03020f100504 68
    0x2c0c00a90f0007400c080b0440180300f400513040b114039500102055040091003409907458481c01c1d1308694102c9602d40f011304400340d581c039040c00104050079010000302c1c01d00c018103030b010308030500c40d030740645410800c1c0d4515401265580056083c480c3d2066003044446c22070f00d441d40140c2003140c40544403204840c86540c0361403e503821a0000d80905907182e40402840c0c1d030402a090798446000300800960034031000d079580358901f82002c1e800b4040c1041803000307654030070f0001e400203105081c1f043d91140420301810702c45a10030740a030103000365403680d040503100e032170302c41d00041c800c0503100c01030600c2952039406e080480321030b8140d92014051340117070b1a490080006512038951400b1010051070100d0f0050321128140000044680c90400d84100f40200081c85e59003007040d6081a40d11650f0a41346604845203414803d4805182080d0300c0c20305010b000050a400000501c0701c442c10f5446424800300d0405034400a9844103001800001da03042a103d1074030343d4105480c02a24181e2128002c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 107008282 1250 107007032 107007037
    0x81c02030d092a050d0303050612030409090b06030f0615010509040501090f0e0a0803060402070609020d030e01140a02030405060c0a0503030c13060c0807062a0203030108010c03090206220902 84
    0x1594411640d400400500090580105859800f95103c0c0316690808010801d403030564900107003856514401310301c03190f5400c0702111000c03142600300c0390360f00c0e110001200545500d9004490708a250f6000c00d02c180b402040f5202036022050040c141c554510320034000c10b0f1044041c150500104028026158031580030380c50280081d040049400c05509898904a80344c1c4000100c29400420800c030006000c0300c1240e0308401c0c22900582c841180c2c4c1480c80042070f22400082d840003651102c1400c0541107180194110406d0300d0320782e00362510510724a0b1601c03e2410032780058208000c207101902e0104040c0007680e080000b180c490008035640d461031503000b03542800130810041900c402c26401e03084400050011442c0170540c00107a5902ca03148d60044d254003c101545a4035012890720032032170755a80088103584a10a800100c041c06501da034002c0c05591115401c18605d165038034007034046c44000030390141401e440d0a01440d000c64400d0300041d0001c00d18a0005400a40305466001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 107009532 1250 107008282 107008301
    0xc14010212220803040b0417031501020606030106080705011b08030c04031704050a0b070f050d0e031b030706080c19030209120705011e031404110907050301081c02030d 74
    0x9060090b041c001d1045254003070709200b03103152119400c6407000294030302d000c0e40c1d04030f0351001a010361030700c0d80d1514a0a5024010290218260100c20091061006a89070402803130a8081da80c5c540c84506c01d00d400d07511240100c403841d41c407802d0200316551141611151002c0071340031354250300d07800b9a90764000c0e50050312000f92804c00030409100f80003128806064107002210407d1605191202180605500340708451016401140400a015054200002c1c460b40241030301d00d5009140005808090b04100c0c890191086002001c01c03030b540b4603c201480700000b0020300e4098a000d200300c45900c07004088050200040c400c422111000360310b400300f074010680b005622000c0c040305200c45c1a03580e503800c995175440b1171010405641c01092050b01c900081c0e40c042400c0c921148198054a0000741d40343c6004c00881c04c12040c07184031010241004811511240d02e515400301c2102c0500080c0120500b941058046001d114500301c2040403460090040d0703401c100d1000d08610841d00c9900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 107010782 1250 107009532 107009557
    0x60f090306040b061305040c06030b0111070e07120603020604030f0201020f0a05030703080919060f020903060414070806010b09191707030b0109060b0d02030a0902091302040b1c02010c140102 84
    0x904c506883d100308912030aa8034650100322518250700e4084480741d85110703ca003417503550361110301c2992040680760b008101c1c0c0d108484520360b840d40c268050590849560002940341c001d15540d440b2103004a1013101d0b00103142c142803505545410305c1c2c040244030103d040d842030008000901800788001e441c0e0502501c050360f110506410050160307038000780194015000440041c007145109900b258a50381c0040c8009503440c44414490020301c104440303103a1501c903801c01c020030802205075a41007103864006541c032242d42c8414942e5115002e01030184601d405121524070350074903690402001e403002281d818042d030794a4070185002c1c2c081050311181e03006010240180950440042e0040c89a81410804c007031402d0800f4440380070300b98040307041030340000c00314064001d0758100c0f0009071b030001c10801860800030030001d110314009400b00c0c00b40d4100058810b6a1a041c0d1448003250180021818069105c0e070044914940210b002c4404058040c0f18003490341092001e0321a00d074150 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 107012032 1250 107010782 107010803
    0x8090a0503060f041b081906020d020c01050108070e10060c02030309060d020901030e060106020c090405152d070518131104030506101a0c010f1a1008090606060f09030604 75
    0x41c00d18410745c1e03840c110042001c0d1960701080180b40e10028016104004c00208044101c81c02d00e0b052000e40b19403505009400c1c0041000780318140194031460481d100d0104031000300d40e80c1c04c29032414220231203805e01d492300044800c000c00d40c040d092420711144000c0c00d5a181040803000200395800c415034807071809034045898015075805104520600d058000100015032510400039a1000301e0078070f150082e43c04030042807c008040210320700c10401c410f200348443c50310041c0c81381807425407402041c8209101949002041240784500d018128595415203801c06c0050403c00146c02c2104480e080001c42241044550b07444c4200c2e400900c170010460b50707a40ca90b00740141b6085024040140d03403801c0420400c5074404503151110103a17030801c03110743c941501850860040404a001400c5d5504003441054032943c500d48840c0d081c50211041c5014078080c081c2160110401c8034401c0e81c0360b01c100003040c928035081c03020b4810002c0c9a035600c0e28104011010038104181560211100700e00c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 107013282 1250 107012032 107012041
    0xc0405040501180e010b030c040b0d0606060807090603020c0715020a1203021806040803030f0907030c0605070308070206270a080d05071106100303140c03070309090e0703020d08090a0503060f 84
    0x86004503451380030003034001d0240d0800c0d80000380d01c4030350344101d4922840d078035269120769884091182c10399541068081219580d00d5802426030881101c90360300184c41e9007000700d402030003072094610702c10050000304003890411b20700b848485014840b0000b94400c01e01c0110010b0048240401d0303024484d0390150700e8102c030003020004640c05600b22889004180010700030000000192030384007405c007c4500703046e11100b6902d400c0c443c2c2ea4101400c0705291200208410360007030001c00c15144642c0e40c80030681d0722041c2c2240c0725142552080428501740c0c03002c03506440d282d0440c0d00a1500b58041c2c03800c907841c1d651904510340c0b01010300445561544200322010f50002101c1c020003c03440041c01092500c1a905100013036140130007024401c0a550302e841000640040c2da101d8540d08080ba540c41d0203e0401400a94452085038607860400d03410307080d92000400c03002c2c12a94043d141d500c0c00720071941c0b407041c5038000780300d641e4001e503405d540020035a038104006405190600c41c01e844c42d040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 107014388 1106 107013282 107013329
    0x20604080a08091806061905040f06030e010606020105011d07020a0215031611120d20030a0b09011505181e01081006050f030c0405040501 61
    0x90007448010480314200400c221030b0100d80801e6000f50b00018805003c1040310f80b03507044001440900d0403130b54015a01e00300c40b840c6060480c206616045503802c903203008c4c2d00c1072000a44440100322500e03400e208171030203002d0505c024099036051485401c165080800f080592402541c0010781444c400c0c8200841164010710304810841c441c1c0e880d0303a03d0381050303c0d450030903905845d0740c42c685ca014910007582e0107a034174080c01002406e4503410300a600034104000459403501d9140c10003c40c0316003840307514214044000e45034184005014115080512420b000d40303c0c1e0360040c031820146604c01050346802c0e02d07041d0391700c1c1c64a8010016000a202c0c0c8981c1100c9803a443c403040705038074507010103803103000c1e602c14100781d546168010045c00c00c0c0c814400882d8042000711080c40e916402035a100201040c190316045d0390300301007421580300760b110003404910101c00e14090035 = true := by decide +kernel

theorem cover : BRFrame.Cov 106834532 107014388 := by
  have h0 := BRFrame.cov_init 106834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 106834532 ≤ n) (h2 : n < 107014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
