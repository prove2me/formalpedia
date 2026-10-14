-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3560
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:01:04.099027+00:00
-- url     : https://prove2.me/submissions/fb38acef-b1c2-4540-9af8-f3cae96f890c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 640107913 ≤ n < 640287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 640109163 1250 640107913 640107931
    0x1309050411030a2603161d0d11090609040c0e0c0909090d0f08240a030602130303030b030d0f0e030106030605011d0115020c060d0f02040e041209080c040e0a1514 71
    0x5e0352414203001c44078a02c50781d2181d0140110f26240e0040070866160342e1058080141c6852030342101405c0c07d8890020054820344103d02100004189040c1002601d0043c0ea220103001b118605100c0080340e24030004208103081d88080c040c00e400307030383d4441c400b50191411001505014608000050010240380d43d000c0c240f04032038003401000032031480310211701e1000c040c1440304200f6000012700b2014840d40041c16080c00440d03200600503006c030004040342c1c402c0d18104201103030041071548400c280f98a40011500134001200c5080c0210400400000002c0000030f110361a95200130031600207800501c4550b0861000300400340c101007043e13025080c6222444400030341c0d404001d555003070340c40342c8a00850700030403038240094094001c00c0700200c01c59419501c1d0760715000715003135107502160181c0395a07040d030092130740190090784c4000954044202600c0285080420701016000b1220f0301100c0f44607030705040b0003081c5801c0603400250030b0f0300c5011400d03400c0c403101c0c41e00c920000b802c0440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 640110413 1250 640109163 640109167
    0xa2607080a140109110418020c0609010b0d1101031401060f0f1704080a092d06050a020615030f12070b07080112032d0c0209010b1309050411030a26 65
    0x2c01c204000ca88281141caa0081c04104411201030b4030405000700c3e481861000d03d0550710038541d00554015204030460740c4226251350343c4180585003641c4041020750340110680e40030394040760385188214041c64041c180401d40701001c1c02c07084a000401d90101000a041800007400150b0100b4940801282c9240041e400240e49041c2d41d020b14010740010f2481c540040da141c02c880c05074554400a0a07800c8002c1e903142c00e00d0307020a41c1d01d050840c1c1c3d54010030490340b012654074015800d46032143e4490b40104100d5031504030103e00d0107004401c0d1a0b16201c3c00c01070482d001420071003440040c00d595803d9854021502d40704c185490050201000d01440c035006011407030b12403c1a125240d0145041c040c40d01d00c4040340720002c060003000300012540386290190558010146070041882030721260500d81c4d0f01d02c1c002109005601180400020190081140708080d80085070000e01418a8064012031000002d150840720078045420464014206400c00e00f5043c01041d001e0388407042d98 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 640111663 1250 640110413 640110431
    0x150302251b030c0e06030a020306090d020d03140609100b0d090b01050a03020d080708040f0b07050d03020901051b072c0105030d0806010302070f02301c050a2607080a 73
    0x50034143e40c0184940580c01d9000107616a900f040140c2131190050162022410700d4071516885181d02d603042c00241c482c3c007081c030000342c0c440d00c106900882400d100c021136803075041c01c02000c00070107012074036100840e050101300404288010401c008014000180c00307803d600e4003038072140b8140c1c001441606180c50410150310f0307003002c02899a07840380c8196a200b41501c2c003101c0900582c2c002c0700158075510340c08035817440e13000004d01006006100301c0e0004081c0400071003d03449103400c07046c000744050001020000d84048600014000142a2034015455100f8014080ea001001046541c5020000600740151142180c0500f605601810301d0440714807016120350009040303241010350010300041413000c0038496041c12035000b41a0448100c950080324400801082015040d04c1d203440168040e00001031883c14030000c4039940350701e020032b0703200c141c8090304003c0c0101d040c0220031210100c8a659080f030074031100c0040601030017908080c00c00500c03034400281440c1450303280540c10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 640112913 1250 640111663 640111673
    0x40e0304030519060908031006020f071415071401020406090909030507030804050a1a16080114060310120c030618020a09020903030706090c03050d0c0c150302251b03 73
    0x160509001c0d525449002c0c243e03510740880103003242c00000c3c0170503c010003840744080381c0c10107140032580c46900f100c40540300006802c0d1110420302c00d100f4490050346e2088428145800a11284010000c0403410998661940b030008410070180b90b000d03950024090041540180c101006000950420401d001a5544c050302d248500c20010341403201c000006010440300f0069562806d5200c80d00c81490010781c42d005c204510161039014000355008000b01c8513912506070b0b14129170302d15840d4150051003038240170495101a05003000101c0c240c00c082055503044001550881c40340c800a1284c520f1814250101c8a20360740a800343c80e100d101090150382e641108006581d000700d00140d03982034080c00240f451065500007000d442c140140e560074080d08606100440303004805862440542c10402c42d01d0413200c10004003007600f6a001441042645101504003441782d05005203000d0068600039044000140c443c0c00c0341800e025248100061703690403880c3c0d84001400a9040c0e0b041d6903070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 640114163 1250 640112913 640112923
    0x9080a050c012102120a0e010c02030d090809030a08031605090603070e031f090204050108030301150e1912050f010209030a020f0418150b01050a05040603051506031005040e03040305 80
    0x1a030b04120600182c80c6441c07410900c0030100c20703403541046654030b2000030940b100c80e10458a8010f1649010f0403104520b4045c0180051030006601031481d0034040d114040050400340c40a446240f402d00104c5440d8500700720850b14180100c2d0065160315280112041c44d54410202c0c07010024288805112612044103403a009606400c00725603100d0070720b011074680a441d404820b0b0103014410400b2101d543c43e0b020401082c000e60b8184030340e03030700c4200041d070301d03c004c0c07080d14024001c0703d50b6420f00b00e1281c2c00d011707106000240b150f80460a0302420061841e619004251540440303c2484108003080280c0c0c60304855050081d41803030003141c00240c54a1181030040e004024080142205075901e90100b09500f480074041851500e00b414002a042e28500007021110302d00041d00116600507000d9030005056a030301c803840c00d81000c80c220064030780501003450300c00001401025603502c840246109402c2e826800c10218900002c00041d02c0780e03031440d882c454000b0441400410702c00b00b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 640115413 1250 640114163 640114183
    0xb2808040803040203010e01050a091104050708040b0a0204231809030318120c010b09070c150f0207060507081501080c0a030c05070507080606040605040b0d020127080106030309080a05 81
    0xc507203c3c1d0796400400d0240500480c80c034280c1d483c0c8001c0080000c100c0c0d200e504910700645c0c000909403034907010711084540c15200c0b2004034100500080004403250340c0d16500c044060805401c5c40d54421104841110781e940301085d00d400c2c9410002107040c1849109a40d0038021180d5105c1c0c18020b8560740c0360312020b0441100031030480000c54010078100308918817121705840144da605d5490900c14002c0139540382c00d905ca000045e010503203240c4075400b0429003682010380700c49104101c514a80003841c1018121300900e800340a00c0700490faa5110381441400c40b9121141c40b072400c840451503c4600c002c1d020705001040c4203000c2e00d020440241c030554103a40c00d00050100310404266010302807058000c102d44200880031642040106406002d400192001d202d402e44a108000503902d0821040c1e13000441d4013042c0d80551710500c0103d4091641c22008208000d105802c1416003420313400c54503590303445140400070540d000008100411040016100640c000c3d5a025102c0e2100d0b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 640116663 1250 640115413 640115423
    0x130b0a17190509160806070216060f030f0902100e0f2b020d080a020f0705011b060b0a0906080a021201021c0902030309060a032f0a2001060b280804 65
    0x280008480d50003c209038a490240720300381529443d61790254554840d070450b850300045c001c00c21048103a0010807110002c2d40c2143d200e8142461203504110000e1200d138a4820509444442404c056145c1406000e03441e8040e03a201c0005d00300035024016030f910750160b0b5500130b01e400d03002c3d5005d450f0a01c4200001060000740d008000009000080f1300002070a00501150703030009181d580c054002440c1c2020329560015200c0c241c0c0d80e8001590b204840c82c0c0080444c0188400501c00620f007540011a4204000d02101d5043e45400645003112480d40003006140e1182040000703615200000f800b0a0012000951600002d280c440d41d240c0000e00054005c0d40c1c17680341031070441d54140309460318868050203a6444818580d0018040d11124800810888818000303000882c80d016003a0401c980f2030140ba842e00380881d200b00c40f1070b01c0f2601c001e03034502c11210000941c200203020307001c018041c00510640f11350310b844144283e03001503110344103c0620040c3c0b40c81250307000710130207500c9070f004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 640117913 1250 640116663 640116671
    0x5090d170702030708060a1a280924080607051e1213021905031f020c0703050c010917100509010b1002010501150302032703130b0a1719 60
    0x1400642414060300074000d40c9406100d001141074640003518071302c15481c641c424000d11600c0d0117000800e902c0b140f85140c1020b041859454010f110a103522001c648106280c40480e81e81c0440100300c400c40c0c1ea01500034410810080d16003103949810b4000f90102c00e01420660601e404007401c82d1082c0794501d6100e0740700c0c850350744a4091140680f1039a00e00140501c2162405155a440044003c84100e00c526841060071031340004d140c0b84c00095407000f03401041c0c0b64854548185580440021525a2030780811040302c0f58001406110011403184005210001e07115002401e071803125005444107103000f805500198000052a20911410010028042e15146600ca01524031210381d035400480702d4218a07402a415807089048a07450302000c00f01d155030752070032001c0c6c2c0300c1602c05030220800741241c201c0300490100004403050411040300e203081c01c076241c0180305204690221031180ea0201e01071070340980000380c84055100341d0044d0301d0340b86000e0720750a41c1c0031055803039042d0309507079 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 640119163 1250 640117913 640117943
    0x1113090b0102071a071401200d0608030705030408010b0108150103051b1306031a0a031b030524010b04030305030a150f0305010504060e0d14070602040f0602060402030d05090d 77
    0x288400006000c4e040a031001007000d02090791034640c0540380c110340c1601c3d004e030a14500c582c18492500b6840041d101e0540d19400740c065403d490700f0400c0c01da180c1b40e9031454001b9a010b407c10081c0201c51082010b940c0340c40c030382942142160a4400142d061140d130b0410400035144140700c0c1e43c00b102003400d000419446042c90f124a40e85a809132407464180015070002a0708080f03181e600311281543c0034400b0440e200304240100c940d40a1090b01b2240502041c40001e4890050591182c87e403507005000da992078072001d142401c010020803911560041400349030800e4a0000c0c050100e18011030724140c42d685e40103200781b0004182100403991150341c0310b95042c1d00c00d1508024045028400c1803e84c407804c0040c001c1906a40494502e45461103492240501150714003111403070781c54440e4010f0301e081d08080680d116590880d0001e50070000440c3c135410204140010300a10f07030041c03e00e841e01e0b10505103880d07070000c880c100f800010b200c11841503441c540380458143d8056000d0110b020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 640120413 1250 640119163 640119167
    0xf0302010209040c030b330715090b040b0906010302010f0f0e0a140405060d1707060b0a150f020f283807050d2309030c011113090b01 59
    0x2440d180b41d0f600a04054041c4141c6a050304082041c000c1122451100d001c51480c0344d20f5441c00c0e41c0e82c400c1c1c501004200c40c0704018400d024040590040303045840320742d0301d544804111111864111121040c030402e020038084490180307580017000d80c0081600d035040d80c0002e09070b0900f01c98114200302d1030b0100000e54501c5421b5a642c030f54000b811708240035455958130011205042c6079240601d20303020000c0d0242c034002d11503180c0c06811410031143c050b05003040354a02c1e401405e00361900d940b2015806541e450341002e0900a250804051079a920340440042078803240750f42c90011540094420700481c1d0303004c2010b1b0b12042c201125081c0c211404100b078503a254620320080d20860607000000070101014107004c07415040400d50000085020904003401d00e01910140b000a00500021581110310b07400146815000710303081507c0c01c101881c0fa4080c81040ba0305442a80012480384a031100034040c0480c0f4102c01062075050101d1036520300401c80c481d2060040554441c441004d00b64 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 640121663 1250 640120413 640120417
    0x20a020a0b180c010e10030903051210030b010803090109060e0a0f08280305030403080703020c0a030e01030b012d14030a1b05040b0304110a0b0c0c040f05040506040f03020102 77
    0x554071086412942c90805410a40e815503001c50031000e01602940300721031362207210181000346000f46242c1d009403c0c034004600400c0070a00072003d000041041c808103032000d130900d034030a20003d94034081c290704502c1c004080200681c401c06d420380c01808042c1150ba00030205006644541c90207907030664299000504142c4d859000c0000a101e0703e00100d4006030108400d02000110003030ae4000600c0d0b981200b40c0e401907020003400081040c004600080e100c3c401658104107280780150030103000040799410082428400c134089a8074003a2003103556090f0207030048503a42420000540700d0540043c01d40780070641c420f91540c95601e00701d18071a40c00395580300d01c00c02c030007010703240c83e407030500b003100c00070011982c2c02c24081c0700401c007070031a0611031001c490a58982041c05819a1501c1d501c3c0010740c0195141036901c442040c00101d640c1c5c0e2440e0140c0101882200100310540034202800100c4210409060300e4034140070030040031403000510250031983c400401c01007041a824124028 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 640122913 1250 640121663 640121683
    0x160e060904020301180602030109050117071502120d0c080106110304090b060d060f0e0105060307200c09090106240503010e13120c02100f0e04020703030204030b012402120d020a02 79
    0x805c800c4102d092050070f50255040e5503405004000c00c4e40c2700d2515102c80c0303440e1062010540d100403810f1146280c3c0d051000c070003400900480e407001f83d031105444074940040c40c201c41800c1d0349075001070340300c0da010a5650040807a0308021f240c12041a001e617880f44101d01650000c0c60f00e452206945480304011103003001c182d00700c104038a1f0344510788900c4001c500e101300c2450740c40da41c00100e030a203080f6045034061012516480c0c0d24230000d480391001c0c6004450f50703038818014100180300d161100d110035842040d01500000c0c089060580c101c00840d002409542c00030b02d4110540c80b015040350480341910708404128840d9035510036050452030811900900d0914a280300605640d000390b8862aa64401c48000c43e40c1c04051b0701c1110300c070101021500005e41000c00310b0301e4906081e40106042030117460b01603c0e2545a07280e8401d040401c0c1d0040d00610681c50a07401716608000640c07105882d244050702c00b001c0303484d00c2240300f0b006010000b005950300103040c451140c0200816003071307 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 640124163 1250 640122913 640122941
    0x41104060f1803061d01051005151303030e0102100b06070f02060d0f0614010206090604020108090a140d0315120308061c060b0406210605102105160e060904020301 72
    0x71140e240d01c0c20760007404880140020b44241c00c1c0c5c0702c6860f4001801164032650070600350700c420a2400d001c10220f40c0b040303c04188000c000f0404110002c2010401c4400355000e510b07564034214104000a1030312a02c5141d0114491a00002070b4655442c102215129074100c0381c0460303403201c0c500000b401c604c24454100c201601d002100719541245030001d0701150700e2402c803c0c0d48091014010ba86a01c0100c500090523005900040c00543c0a07812040c0c0040880080310382d61a85985c4000829055020b04241c6900c001d001e200000c0c0e060040c020054400f004294283e890300b032a5118920f103400340201400010400200c60b07403100154880f4800031003196011030600ea0801d07500401207560424000c50030031001084070203580c42c5051704440003482e10000300d10f413520703100004c01010f07001c124450309400000800302e840c0c5221030551101c02e544185581040e02d0654600b01d48903c82080e0792042c0001000402501140560f00040c1901c05a1003030381e4500c0044e005155200502030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 640125413 1250 640124163 640124207
    0xa0608030c070503070506030108300c0718061d04081e0a08010510020a02061b1507030c090e07030b040603081809010504060e07120b150711041104060f 67
    0x41c1d52a00103114400c031603080e82074a040948032028040071744400d000d1070f8019800f107090900280210a50b83d08854016000038044450b001c01d80384180d4081c0c0d01a19140e4803294052014903404c1001c2c4102107400790007001910f190400c00e10b1180700e074010541308046544009828000a04201c0b0900c00709070b1900d9210404540c00032516411614200d40050002d0001141e5810030810307601c10050141c008144040c2c0c240d003000101d602c000d2612008840321148501ca500c0108805011641c2440c051902480c0c041d80c01001c440d0b0441e0f45c1e004018144904010482000d12425088a01d0f440c1c0412808229004030307000e0800d41c0e000400c4c91000241c10305000d4820b01c020a088181111041d029076a190100000e4030b03c7c13170240640000185002c100000e0103603010300b0f08241007a80105282014000040ca0a0200c15801d00059400190b2740104200030602200c2c0c000b080f01c00300402c441300c241c211000d0150703009803000d00c0444609080050b01941603050205c00e4145011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 640126663 1250 640125413 640125427
    0x4030c03121d0303182103091203090d02060d1b020303090d0c0c06030203220602030a050a09050601030201030f02090d05100e070e062b200102030a05040b030a060803 73
    0x55040340000c0040700050b0340d084207844106140002c4064116004000707505124400040c61220407201d9242a80010002c2003041c0c0b551794007020740c8110f0107030340155407031700c80000601c9981d0b209181c0d50010758208004646196841c0c010882c9003940658203141c6071040c80300c452008241c1094100042e00d04942e00e4040305500100941c400d028560603500410340e801d006486980e0b04400c0100140101c0d01c041c0310480c40317940590360140041c40301c032000c00540981c0c03910030010000140d82e015000001c1100820701801019048403030340c40f0400c44000d1035100c0719198041800001d0406031100030a0050000940540b00905001444460014401d20f8217a540b8409d01d031860031102c2c200a540703c0204000700e42c09045401c00203447d01590313610001c10407918101c180200710344082102c20030400d41c41e1904c183c1018071400200d40060300c404003c095005c10402402e04540c41003102005d0942e2041c240d408441c03004019039141d460b0210145d01034481030301310f92007510020841c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 640127913 1250 640126663 640126673
    0xc0a1212021305120d02070b0a03020702060304261c0c0203130b0d1d1009021302120f060603070c140a050a03020304321e060c011505040e0604031404030c03 69
    0x700031580102c0308002820f01c1340070020b807917040440c0c0744030168115000070020150000300920b400314403881d005207020b0465000524581050b90140d40810342e1840d13019103c40181c80c205c0307018510280b0b0f1802c1140714540b9204002248008540c200d8884084025150080090754518106142c00e014010b403544050300164101c0003010260a04040040300d1400e5024120342803d81c195020740b507020300705c000c550098241d07032074200c1e088821848201c23a540414130141c40d074482c01c24501d00350360401e115280b2803c0c0000e0038240c803031041001480003082e002002c081060b9842800c4d11300a502d044115401d00c14012000342450181c551410200b550120090066400c2c41c088040c4181e4030030111072000500040c0161500561031080b034a900e0219014a0101b80390f6100b0010b00321890007180d07140d0030013510030702a43c0d110f112403000c007d810020a00506426241005680c4524540d999038000150001d0103000410104042c2c82c101c0404850240d500008500300060b03880ca40703 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 640129163 1250 640127913 640127947
    0x4050d0c0e090d020c04050609040210050f03011418071b0614011202030d0c020f0622080705180606071113050915010b190f0e040f02070506010501050c0a121202 71
    0x3d4034014000c0c00441c000a182900c00da0340100c8000d410500d040c0d40b00d6090001f28101c0f000b941d005d0240500c0380c00c0b071042c0310394015070181c03024050044c20f48200006200c07a480c86c20458995022200341003000184d0310104000d011300805078030415107000341c10010018134400e03800700c21a23403403c400421400d02045000034581e01c01c0d000c96408812450301119808100b0030020743c014200200d4030524138180300a003041c001a80c508120440111050540990495009018940014200b0440c500d03040c3d00741d00308604187d8450301e20b41317071400c001003042c419800003d0084160601c60001500c86210307255006048000400060074a0440c251765005610201c1c041d82d03114000224103800418145c0342c10600f04c010348094007070b600360309580020fa0300780240b0422250405480d01641d440c01940700c5c1c00022070b0016070341c41481c10814105003058200f80d0500c541003150107000c40001411415094101e4509070f501103040744204d900c1c002e0107040e924a14000f01c0e51240300019421 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 640130413 1250 640129163 640129183
    0x213050117061006050f090d050705210a0f1a010b04091b0e0906012a0506010807030302030406050d06090e0f06010e130b060f090f0106022104050d0c0e09 68
    0xc050540c065101d0041582c070319003160007150800c510030040107080d000700007905504003020b51841c14030b075040e004122040302c043c800351010b5115010421590600036031942c0328412500101000d148c0751540039681304030315640202811410082c0009100c080e0508260701e890104148240d960f4402c0302040c15000f13401010016490200e103c5409807007001070584440c1c2c60740700c0d10f09604000b020010140c0000300034906110b41154183c0c1007040ca80340d14603010386610240c0c4200b0b517450400c2468404160000411584003250600101c0d8001051310100c803618982039070b9982d20314405002528003030b4420b8400c6400c1180500d240700000c120300140c1c59142c03040b506646e07640d011550f0141c005403900d10303c000e15444204045056400496484200540080e04c2e803d400710100350001c1c0211400030720711011a0050114603030600100d40100d2500300f8421104043c0c407203054031842144102845951400c0582c800c101d0300c0c0794400e005060441c01040b1034a405400a0f0301c03102010f0f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 640131663 1250 640130413 640130429
    0xc0f0f0304030e0f0a0306051b0313051b06070b07031803030e06060d08090607020612070e1908030f180a060203030717040b0c1e0d0603020a090c0f05031302130501 72
    0xf03c01803a908001c40724201044004102e080344501c0c5032910700003040007906101c901c01c61155000c49990645004500501308503c0e140b0348036200742081c0b82040100c0800c7c030f00031400e0303001504c120790350380c0b050302c081682180400300a0f0311814015001000f81480030569000b07181209418103826078400091400d004041d01c0c4141d845000308212001e0207480204103c0d400c2c800f00000f410841d015003401840030300710903e008030600c622040da0400702d0340980041e125000c0c0c3e03203540c100b800c4581344480c03920080503065814070241c0d80c0c0307a0003640e00b01c110f0031001207a040440700c0c01003040b02200c08040c044881080d1500c2000751664011100c42c03000c105140d00102c10707a600d114680344107070b400c82d956155645031600103007540c2d400080c040e96503940c80313200301050742d00043c000d010a00701240c000441c18a144180038034000b203a07000c02c03c80c0b882c200c0502217440e001084801401341038645180c3d242d0765904100d5072002c100c54082d40050200441402c01540d95120f103040e50841c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 640132913 1250 640131663 640131677
    0x1020a061b030c0314190603020d1b1a2508030f07020706090803160f0c1d0105010516020108040201051e0d0f060807060e04020d020a02150c0910080c0f0f030403 71
    0x40f4816002c1d1851807111007202d1103d000003c160322110344060300a120000c0020a40650fa40c0000d083c0e25482c1c1d0080e0340a0340480e51120300410010448401010070b040041105006514284c029000303a400101c4003a07005c0d01c44030300c81c0801100360501150b00c0410b00c0d48a050440320100405400c88003031000d84604100450418002e601c04001c5460100c01545001c004103408404a504000b00310790368154030b140b150018000c180ca010140020b121400c0c4d1010740507260306841342040c0d10880c1488010820240c001d407000d0709008d14141c0a0908540640f6541f0040380d240c4145c803201c0c914003044d0740464048a25150040c01000c001c0c07034043c8144034003d614002169000d10400d10a540100401c006450280340a00c190150040c00107051203610b00002c400d82e44250b038078500580100441d46503584030090041c0e0841c2c8035034049402c0041250200e010421400c03120800d1101c818002511401440100c5154404003000161200450042c0142c3e230380003694210081201 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 640134163 1250 640132913 640132931
    0x908090a031113110405130e07170601120804050409020f030f030417030c3a1110140a20120609090d02120309030d05040c090b1903030e01020a061b03 66
    0x82ca000704100304a0021001d4030b400e107440c0400c0f101c0c1c6804610349107c103131502003010481000340312500003801b18085012618203408207080c28488140c1100c030200520018030301c0408c0c91001958142e42d016100055014118000520b118480c125a258540b061205200001c071000c000384c4201da0f40b4000302e0220344814000c0715200d00502068113040d40c041c0860031820310201c100c45502c401085100401d02c2d04101c100b182c041007203a426000310704000306940c940d6004129141d1441005401081020002140c960b201d040190071b1008480e210307900042c09240c0b0900b601b030110843c08165a503640010440340c0004011100c02d8481c0040c0700002c1c0e00f6010210b01c84002c6c3c0116400b4160b500280c01842d04190009001041240b005004022000e82280b140038040c60103a001319840b14a0300c8024020b45450f1030415001d41003208000d240e0546604104054035410304003e680c07010841c004070700d001000340c0c0c054451810300c5543c0596a00080500c0030100da0341ea8103100201d070b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 640135413 1250 640134163 640134199
    0x30b1504141806090612100212010e0402100e060f0417071d040f08160309080105010b090a050d061e0204030201030f02030103021008040c0902040f08011a030a060908090a0311 77
    0x215500001d07042c401d4000520305241450305590704c410700a1401d40d81c1c4001d002034038540705d4410b00b000d401c40c0c0c0c0002c90903403014030807900c0c0f401815880c41100c513924003039020031a010451039450040c4401940c0c010301d5036072000184c90746000c52201c0b80d41c5031aa00c40c04094111a05105010203000c0e0410120b000c00d80c02e214100310080030f01c041001601e4551729016030001c2a001510103070014003d40310b4801c445110000420302075910199044d0a1001c26400c4500c10b030b12020685404001e13015003529881011800c848048401030050030305070610001070b101003003140c034400c5481546500c040c071017079000d0000d890003030381c0801614228400c090102c2c4001c0c080030354800c644002000700540306240c4145e0043c4501c5880820b15500c04005042c1d03085500301801d4114486021b0065038000d20900311051340070840c00c0780e0041c0c10710219807035203a0942c014294903101c030408410704c960442111a160400b40516400964070304045040302c620694491040c1c00602d0720080d012 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 640136663 1250 640135413 640135429
    0x21302040b031504060b0c01020306011706031209130608030c060f040b150d0804080f0c1e01200604030f08090f03251a0103140706050a050a030b150414 67
    0x80500d401d2502e9510380b501c207000b4007815420401e80c4540c0340d280c080341504588010700250f5001c07800168a0f0f060000000d0821740054107142d03c0100300d01c040144503034000903481c2564160305041a074a25010000c2000c08512240e51b40110303080040005201900000620341101142d0130340e6010b880c0d40c041442256015540a0802c0c0c07105000300d080f1006000e000c803280d0b40c004120700d0903610f482c2e0b5080f18a404c164406041c1ea08614840c4600a0041c80114030b55141100d04683d6040c166051031039528860070954100f043c40f201e1300e44c42100c1c484110301c1103219142100c84500c1d10f403400400e20174440d001180000d0084020696081d400141c9854160440780139504002c680720a4818548a4180c0381200d2030308501d00c0340c003045d40d41010207103040070412400907960540c1840800c41d0003030b415007680740d40804020070080c0d511000741d621a02451605550b40c4216960450141100301102035002042040300031810307401038014001ca6019120340c005c44c01e00c400c01c2000b41 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 640137913 1250 640136663 640136669
    0xc08030315100203070204061401110a150e210a0f1e030b0604031502040602060f0106020706050d1d100b030111031518130b0a0912080a020405031902130204 69
    0x104a100300c100c070b00e44407440380ca80034501e00c126424085260005425500654450b49104c070039102140e000b5603000450700115a507250041141c07017910341c2c3d000024184600700207005a6a040c220030080c401b8003502c121044141c1c0391800503240c01d005a5800c8e80090b0102011502e031050106601e8090740d107503842c881c403182401d0681e489034982075010f40040345405600c040200008400254400000d40d02d0f000d0075000143c40c0d40c00c1400191410b400540340c043c00c07106440c010030038547d000400c0001d80d5441c2c607040380c40320b102408903070103000c0e0604050301405580500781d100901c00a452400c0360300d600da0a00107600464245401c803000b08a124901000400014608450803401042e5440c0b0140c8054928029803991030b034581e01c10b40320300c0000500401d41a080c00403044940340c00c0800351904000d000c0c0e00d40d81d0103902503020402e600c103119070500042c03440241541914010180a001e44584c0301d144030a18298a207041c0c03089100349111508450000c445100b80c6040e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 640139163 1250 640137913 640137931
    0x270612030304031110110403050c0f090406090305070210020610060503090d0809030d05041b09140117070527010b12190b1c11041b030b011701030f0c080303 69
    0x1c0d58450340c90440f400c095540f4040101e100d0031400301c0c952a1070348211480c15030240d101503103a07411840c0007802c00701c0500115220755603039103c03e0711550720160000d4000380e0044000031508181c3c039082d1690301800c60041c0d840f000104241b00e00c1c1d5008202984181003003070000d405142c070f83c84143d0b070b280016a0300b551164041c1001104680c0101c0840e5040b00c01c00342140e061039821031040040d244111411507500f01c501c07036546190921008504054100702c9000e0205036171104c40035222200500c2038030002c0e0300c0203010305581d520134841030340684000390800d00d041e00780307101078258110512040090800a20f0001500044140c261a041800d610121710306445440d0113001f60510400c600459641e260604d8032696036160040944000c44180702e139140713566042169403030301602c00303541c026402c0c0700c454400741001c80c200810504040c100001d10780f00900040ba5600d000c8518000c44615010020060058170442500302c284507040da00e1055441f5110301c4e0703c0c0c4c00161942c0c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 640140413 1250 640139163 640139167
    0xc050309010f020a02040c0905211203060d05010f05190213350c01030c0201020703020601051509030703060f15060504090903111906110a0c080a0c0227061203 70
    0x1040c1d40c414002c1c100c021616104407072419003e500000d045403040d021039400310b801c0785420030107818944076100394038580151270354040c001c40c0c1d00151144500c0c079105160010000c0014a10707500e10081c0842d140d0403100070882107818010240060406682810a01c000c00344100318405450080700e40c01c060079650a020540761007140100c0e841122a1480705441078101150341e0005021150042c00f00c8000034006050181c00142c110345002c410042103900400824000c01d0700000d5036030464409885003d1001e81c450000240341c055090920b43c5030107012000028003d403a08031034105001410100803800c03d400442c2900e0b03c2c1445110007065046c44104645083c6030b120511017800f13820705403c40c0c01c0368801c560408034440c0d140e4800d0402c941d5410300340310345849480c030442a0055072034a01614450041c1c4844691403006103d21800200601242d00c6001c16078180c0340d0282c040113031441925401e5003075007075120a4900a40b2007034001400e502d03000442c0d000c4038502401440c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 640141663 1250 640140413 640140427
    0x504030e2b02061207020d08010b04030b160201020d15030b010e06010c0305070203030424080108070b1615050c0304110102030910031a19080105010801110a231801020606010c0503 79
    0x1060101c0c8014180c1e800340c800d000c242200400160414854207480d8007915844440610241c80b104040c0c0003154080c00c14401400003803c84501e4940080c138488200c0140d824182049000e07204125030300c4401420002c0000d00039040241d180203481c81102c2280c034907a06c5002251090b40102d40d21800034800f45d20500109015038028165203001405aa1170503440710341514240a12a50500c0000c507900715010740d0303a5000440f240542104409000c18500e040740201c55400f4458281001c070000301d0a00c020020ba00942041070390b41000107100c1c034584413000110982045806548542103c4802c1556600c08070845920a000070141e1141e9841c030341d0214020040d0103500056440032442c0001c031a03440e018070810340840301050700511828140001d09460040e031100c0c501e40c2c140003d2441c800680d10559140114515001c8908860350303101c000744036042040d51500700000100342c440b0f03440d003841c08019141c083e0211089501e5039001100c0300f180f18100035210b6007040c0001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 640142913 1250 640141663 640141729
    0x4020c030306061b151509011410030906050c130e0f181009050d020c0405010e010b0708160503040510080f01030602030601050f1207030c020d0c03120e010f0504030e 73
    0x15244144d000ca010360b20020000125510708081c407a5250b101d03103402020009440704420f6040c5a035002954484020b51401c000e19950f280c09403801c603c26808518042e1415201e13a00c0034000680000b405e07c020308101c0408002035202c0300f190782041f0307942400072511031780700c207901c0d80584c076021003000d1582c5e03c9850848404807401d584d070300c50380102122000c0117602c600440511901400142c100c8410085000e13107052140d20010b40294181001040345020b8914020304507003154440e55aa038140d4a000146032048185403149120714500300014450004094815140c0076030b203400c0c200b40d88401c16250000121003500301101c0c100018000070f6a581c0166400c80e0044c10b0481c00e042000300303c004180c00803031261892894940400081d03c0d81030262003503411036400a000b0050801d41c005099400b800006024803100d100740d0512003180d94441170101d10241e008021a0110b4100d05000c0c0c00d0588080e40081c5900184801500d880740007441c018115038020889051210b01c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 640144163 1250 640142913 640142917
    0x909050609030a090b030a110a030b0a1403030d05180d112404060e030c101b09050d0807020a0330020c010905091005090c0c010f091e050f12090103060504020c03030606 74
    0x8104000341d2501011a00071400d0006030400c00d09c20340b00401c0b8402c05a09003d121030f003a503c184940400206e101c0f00da81c5020080ba5820a94803001083c141e0710340d032060342d06003c410b20001e680d102c0d02c00c0e210451396004000300040c402c45002d81d10301041c120001e000d000300c01b940d1200300001c1000414002001d03580064440340c48402901d0030309035a240403500389480c50030f003040f90300d40350a003082e04510000700513640c44405007800310245003008040346c41c8c000c004400030901040018214255603940d40d82030011603104006140170a8100c0e42403d405e200344c40c44184a43c813411903169118000b21346c0d0991210f06a60360049989003104004942001400d5852006550b40010500e40c507901009841003403180c160700d5441c4002c108880c01c46030f4943c1d860004a20344410b0100080018082050000f50b4200c2d00151111301c0c1405814400c40001c5142e862040060402107924800007400f0015004d803001c11406640e80e0601007070b841031000c8051142c1040000903014502600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 640145413 1250 640144163 640144171
    0x61006050307030e1b01110105161115161d010f14300108060103080319380118090c020f010606090302040507110a0204050604090c0909050609030a090b03 68
    0x303408242d202c81907044c582405109024a94045858815502e42e540c11022241180381c402c0c0007049203160207440d44045400325044101005107203020b18009540801c41001300d001040710340160707800d100707030082c0c600d840d4203039190b010940d60090401d0385044850040e0709200d040c0c59418030581c034240200e85403012620110145d0303c044c01441d680410780d44000c607000304d00c0440e00242d2580c40045005c00340e4168004090b9a1180c00140005050f040c10340b600051000440070028402a0308280078114418011444004404025600d04480c10522880d040c90798002201881080e00450b0400b440000d074000300c1f680008200440000d50b806170b1a2013283d441542c50114040b00080c0c00e43d5101c0d0301c043d00241d910f80e030034000d614051140a400c00214100180900100c050340c0f915280c100001a2003290ba0300300044080d2140e0300b10780d480d00d510150101440761990465401060240800c1d20144500d0002500c0782d200001124407840907900e5540d1000c0c030340801074456500c010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 640146663 1250 640145413 640145417
    0xf030d03050709081204051f020307080a050c150105120a030c08130b0a02070f0909020d060522060207060e0c0306012304091103060a061a070807020a17010e061006050307 75
    0x1c400002d0300e56085c010922002240700744160382d00c3c500420080c40382c14507101312003002007107010f45490b140c0000031202290341c0030094507101e2510703c03820307107190003038841041c0301d8042c102000501108003840300713040e00d004031500c2da0340151404000da901c2064100060101d000840da280c042841000603040000a000680b5951500e0f10003500d02a040b1044580160740144000d02c9032040220401026046031003003007150400c190000b61078101e0034103001d00301a0341e034400701301ca0344203140c1c0c024038271592102561005007040c0760040081d80045000c0e01d0092030304451545601d000b1a0a55609800038020541030342410100c2c0110301501004070410030701c204040000c0d440c1d0340203904030640290820001d01e406507040c1418071400405200b0340f14503100c0140074204096002035064501d800400d80c48003081c1c40c010025104000c406235001d20365030400510308050b1130b000130600e6a90002400001914480c0c590b6881c001d03100d003d00000c0d440000d10146120364091948000b0354 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 640147913 1250 640146663 640146677
    0x21020c100203150a12110f0d0213111303110d0c05091008100b182809050f16060305010e0f041a0420060f0f0901110f0105060a050f030d030507 63
    0x185000541e5904c550b03002a07844846901e40d181800020685400744080540f2100f00e60300706c000000780b41c04c4000d00006d109240c01081340c4c40d688003da11810110f16107031043c80d500e444043d14032562043c1840f01320341e211260382c4075643ca82420b00d4050358040d0b0222001c852142001c8c204107404c07070010000e61b0b0f42c0004280000c0c0b409010085113068018611000a4401d0000d050000050901800024086440041c894a00d00c070f81e200101d02861a01c0c01c002c0032070748050500c0a0f100d203410150061041e0250184440300c0806c9921908040e000544030540e502c6400340c090b03450074491500c10910640003d155440ea150b0100d502510a41c00340d8079292a406c002640d0600685003602c424031814201d0500804c0700c2d4105d0402d40f011142c0d18282840240760030214031482800c14040b80000c01e14003100c1c0d0107030440455080310382094800e240803001ca030a0082c40200c58503881890085000036031801c058141d118540000382c0601002d81c0d10030070030b5000d440c018011004000207 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 640149163 1250 640147913 640147951
    0x204050a0902040c09171c050f121e010509060d020f03010e0a2d08040b0f1c060302030706050c0c040e03120109020307030f060303080a050c0f070b010905060402030112110d0c0621020c100203 84
    0x2b00d02280d10801d0551210b1740c030707910b5229031040405416000b01d40616071a809006181d0780b48260002442c0d8100c442d800c0d02ca10660129016000c2902e2015003441400c83d90000c00600304e070488440f243c468050202e400c440014a0100045400c020780390900c200401e00202086034010b101c9035403000002c0e440d114841c05c0552030513001460b40c03000641d03200014030071864140141c10040030035140050030034404200b0301e61900d000d0342c03041d48180d6660316000120302c3c2c14020382e498449158005141340d0313503404042c0040e600c2203441100003481c004105040c541c640c45075405803a0541c0d2031101584e90384021a0081c40d0281081c040100c0c18010f00324407104070401840300700d10a1100c81c401d075142440078016101d015191500c242d00600040c804008030b6004410324540002c4041d000844800203c0c600d41144070014001d66448000881c00c2c079003100440402c031080d058489550400124800c080f8002c0c03d400405d0758000319014131035103071650007540d00000c50820105030310301 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 640150413 1250 640149163 640149187
    0x4090308010e100510030903020708030405010918110a0804060606022406011814010801120209161103040e011509080322211a130204050a0902040c09171c050f 70
    0xc1d00341810f000190703c41f1120010194144090f10007825006d000b14185400e182c0080c00d0964030340200400040c0d96035010000745007071380081d90a11104800d05958011400001300110390071142a07d6040c02c024001074054070000c1d03080a800400300703103c260420000050710100701301801c00c07810043c1c4000e07005168030707085960000500310300c40104000d15a1000250881d24141d0000c000d01c1c0207224081c001d138442c0383e8001e5000b50031003407003400041101c40566100000230600906440040360101c0e2911b40c4401d00c034162001283c40007220b4400000403038081445008120241d0802c0c8041d1941c00200c0381d9201004d1800c02c1242e0056840d00c0b0419101d080c10060003041071841c11008042c4004c54201008038076481d07d10400718a070003c8a401e00002c80c84000303009907034403c0000c0828071558000302d84241d00a0003882525000c0000804da661107000f04041840b012014094400d0001601c003010418801c0402c6020324202c019100ba030070540311050f07080c0c010002403981d90 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 640151663 1250 640150413 640150429
    0x72c07020a0f11011e03020a1404080d08040206070c030507090b2e12023912070c0803070c152604020a26011404050a0b0405010b0a0303081504090308010e1005 70
    0x4600c0740d9006860723035400203008010690844060907820710400c02880081d4001c11070020808180c2051802c58856101081b5903120b2030f00c3c050b080c010016004800c0000121f044000c07260250300500080740c82204011685074846005601c5004d101c903203228410a10510380c079840a44d0800200c0c008484035040140d0b40010340b044204407149010101301031b03071784501ca0042118030300706003003540c0490030713580d6103500d2000741c2e07030000101199240c10407a0351000c0001805800050342e455200900e00038404220301e000c4c2034954403020055030760062052071500800900803d00404448940306001807951014000360f8000c002d1101c040303120321062801220413170f2100309604920101c81e410f24211008000da0010b21044013003030001060b130018422036440d8000001d020a502c3d075151440c01429034641607900b00784500070000615812131002c0d0311a016010340c002c15080c00008100449458050090101da00b210051003c00400b1003450350000310700140058951721507001034000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 640152913 1250 640151663 640151717
    0x1020c06160c0f0e0c160c0603050412080903040302130f1805060f040818031c021014071b111e03100606050d0e072c07020a0f1101 58
    0x358151030800810019004204401844981840d510b43c5060034049065070b940a44025010480858411000580e686003c07541030750010b4000c004a0b51102c2c0900504421074060312245284950806800d0003000c1d1288a2500400030318501806c69080018040c034441c04d2031a055520121413581e5030302841140c001501380c039030030b8030101500c0c039015280c0a002020b00040d0108001480006074031001550880c00c40300311302ca05010440000f091518110f6401441c0b50b0417012107030000346802050011905041174003d210410b480344504220080a840102c001900011400c1082c84a4a0000100ba108036420003250035124000fa0701103222503401540700c1455126600c080c54100134020b410007452406010300f0345045000b0703046000c0c40b030300d100c01c103500c03002500c410100c10310444015000741201003100141300740800d012103a00400200d00b0b0400a00412101030000840e4003d4650041c464804184580d4450001008000100f81481392400c2552400c0401c07030b096581d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 640154163 1250 640152913 640152937
    0x315050a1a060c0123193b010c05190203040305060615041e05100201090b16030e07150f0206040818060708030a050f2206050c0903060a090605010e060d0b040201020c06 74
    0x2070900e11251046401c041d0350005807586001c07c0042016000b42d4040101c4204d00c0c041110465284044403a08240006e115841c3d441c020300303103a58039040340107080c04502c02c1901205024900381d06a0f540e1080d408003420f640d101500290f000d02c1c1c1445214605029400e07814205030b0b481414404401d0070314582c00020300c01c2c01042c401e40c00c00340b10400c03e4104910003031240c540e00c4e0302c0b281c1500c04003514603032601300d480c07120011b05400381d001079686020050465200341e550300e068860005440350701c1c80025141000c480c00107840050903a000d6500f03da00b407403402e91064902030b102d03e21003003420b40100c020301880c400304200a000c0d51181d9800b02000c1101c4c074105014483c070250007480948200c48003080b095140340240a801c01c0300c0c1e03016200085030f4442460446241c025090305d1507041c071881c41000108140b680214005e2403161405202c10b03602d80c0e807a00c0c0e040d10101c5106402c60181c1a843c0b011583c20070006801c00d0040c01543d1500c03002c90302264195000c0021491 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 640155413 1250 640154163 640154231
    0x920070302011b080c0a0c480e0a0b04060b040b0909061012180f0c0609060305130f02040f0c03090b0c09030d05031b03010315050a1a060c01 62
    0xc43c80d1a100d2600b01c06290b49440380c95498a030b91203044502a205a203402c2040507a011400c00c1558015034200703420a4004071b80300c0b0488040b842003000484081a42034445102c5c1c0705005412012100c240c855008260b20a40e841401c2c100003049031a808903031107515041d0011b5000c1c000f00042003e000720103421036540108006200300e505000d071802d030041c1ca035445c4008406038040da42c4402c0122a040229034840c004010400180051101802880e41284408208800c00728980c013203c0e1651110b041150765400e068045071402c6550000f06048002c2030b030000364041555000051000744002158280801d0303820884441c40f41e9030b008241c3d50b0000d0b03402d0004400845600280201ca600c0c5011500b001180c0c88020b4441c650040c401c0110100e0020794a440440802c045c800786515165a50380c200396404c0c058124010701060314042c049003144081c0e000d02000e540700c210700e000510a000d810702080e5803040d210106036541c0c840c550f9100700b22841e9200882e40318072103088 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 640156663 1250 640155413 640155431
    0xc030507021009211106070c0e1302030d030c0c030f021501080f010b0312070305070c09020a0323090c131404060b150315060a0302071208090610050604092007030201 73
    0x26100507522200c040c4011450361000901c010351841c00400e015140f07203407194200d191003024028540c22040c440e65080c002c0001c180200c0540e5442b03030303000b1022251107404a29050b03080310001c81d0004001108a4012000f103402403440003035556951048a40ca0f451002410030000401c3e0850055034000010a2181030000d018001d50344808070003030528801300c070302c1001c1c941c401c00e81c0003028003002298100034403182070240002448060003d640c2c4e007034003203402402410340d030301c03032041100d140c1d00c40c035030112216128240f00303842002c02003071801c00d14010020818940e908045e00d0503120020000c4007032003a00d81a01591040341c001c100c0c81c0c04c02c800c00c0703000f503403c3d08907e5200b9802d000f00140f0741040c1d03032007210041d004d890190340e03a020800100c000c1e02c01c41002620014005040c1924107074810303060740c400e8100501b41c5243d03807984590388516041030300c9210382c03060050006019072103030f0b64005c41c0001c1d2050011844a04841c03100103864103e9581900581d640780184 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 640157913 1250 640156663 640156679
    0x203060702151621090804090f1820060c1f0e0312011a0d1409070e15040203180a0f0606060807091403010b0a23040504080a0c030507021009 62
    0x220f60405075000070940c004030400c500910800c82d00210300e00070071008504840b0140203a1203041d104e504001503654594035001c42c8000783c040003030300050103031410113000c0340d02550641420505a02030807888402c0d40e51140020114450400a6400346040003010400c0c0020400300c00e034a0742103072002064400841003141200c0c1101d20700d811540080240d001850040c1212506585140e844100311402c1144602054084d15151844080c46c0600e080c201d0f61845040034841c0790281c088444094482d298002107000075200006401d101440d001e2540c94a500a19441920b4140d07a0040f0001c5482d12803525507041300c250381004103c04180c003803000e0b501600019203047e0914079107600700444020090002445040b0b40c03590300018010301540c0a400402c081c02006100808080d1221843d04001c42d04546c080c019141d5110500c659003854007a881c800e60304480c0741c07400c1203101c0d0015204282d00200480400108200c0c2100503a501d070b101210302d103c5a5151861a8100454 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 640159163 1250 640157913 640157953
    0x304060b0909210a1e0302040305010c0c060c0f1d4509060708091504140c04200f0f0309060726040809130207050a06050615030105010f0c0203060702 66
    0x1107500f1003045090012500000a03503041d119045806088801440703045000340142c3e00002c150394200366845004550120301441030324040c080070030142100000a84480003010520303804916082981224407100d007034420382c1c001c4003234038028401021b0b0f0011000c0700c121004c0c00d80d10003040c108080c0d080c86042e810500414005000d07905505104140070741c0ea00300242000c0070080e1107000180105005c1c4601e01045404201080307103410706250080e2400340110588003244210aa0040c15142034000c0416080c9616030260758100d05944021b00e1380d01c80d44108540c141e04110100304c04084000642c800c48511001d869642003072000200620700031080c040d800c0100c420151760307966119103820340180d0b200e000140d69a41d00d60100c2c0450f4051440765403640d01c042005400d0040102c0d00015452003071104120329074400c0d04100121010340034003421a0341c144018020303940225442505c5941c03030f0030041010309180e40080c0c41c048007250f0507001030b00100b40209420000543c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 640160413 1250 640159163 640159213
    0x30103061407020a020d0f021009060201200714030408060403120b06030105010519030b03071d06041104030b07090e0a140c03070e19080708070f061b02060304060b0909 74
    0x20a9102d040c2248029078644d110303000a8810f195400d12041000f81c00c900b80ca02d45c540c007400b49000c1c0b28074400c0203005400644a9030b0055428600c40118884680d00b00800d00d000d0100c1e000d08020301901d807c41c1d040041041c420061008010210b400c00041080d0b501c128420b035074040d4085258801c41003074452000c40d00740240424001030005170780140c25241501036a074182096040080001c8020304400381e1000d0b094040d45402013200411905809a402048441542c0c00d4440209110031501d1074000005110401d00040c40012070582003550031200920b0306920958480c050f510302440309640252010b6a40e10a890021347d00d5110035900585c81c415150552810b00b070b010707109080000710300d80704448041003c003110b1010000e001c0501103400881d50b20750b840d50001070303440340b8900492001081c01c20000038454810130000c107215214041c400c800b00d00950a00c06180c1002c0c0040710701035280c54201029489400c107540c802d80f002d000522818101c01004071204e14041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 640161663 1250 640160413 640160441
    0x9010c030b0105040b22080322060806060d1116020f10140f0d110a0212092d100203040501092922030506040c12210201020c010204080303010306 64
    0x51000003240c0c3c01200381e40c11107081c1c0d07280030780c1c0d60b140f013540d86280b45800c50380c0101c00f45d550a02180300e450001c0a04540c8040903080d0408507400450b6401590103449100c0000780741000180b002d0030010054a51802030300408907a15640080c04c081c150042007021010701c0c3c00308056015441c10780519050b0050a5404001e0082041d00050032001603a06068101c0d00001e44103103100c2c0a07004407040306121540c1000169030030000c42a080d400020744000600c41c442c07000790b401449004035581c0d01da005182d60603100c8200c10845018900c210580001200400c0b17002a175214548029a00f4800398007440c0c0e980e05080c005002090796802c0895400d07840b02c1c142941c024070f810041c444141002285864501d00e094004d01d1007204034001c5148908107200100700000011814041c51103650a04000c1e500c0b040540340707402020802a203202c9511044c0c00c12004c0388041180da08042c0c0c400580781c0081610382c2802da030702c0b83e44070700481e900000041080c05001d104100d1907101007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 640162913 1250 640161663 640161671
    0xd1a1b0f09010c0827092a1c140619180b01030612030309060f02131a040315020309060c0304030c030c0215220503032106010306030f12020d03060f030f06020c030c0609010c03 77
    0x4a604500722071942e81c2c0c02c47e80c0c603800500391181030141c0e525280d44805891040c4000c0085600f010312000d4241d400a00072074138101f10900f807007038485004054a010100079401c00ca00c491001c1c0140400355001814543d503808081001e04105188450f07803800f80d20049016106032920404486240480d444a1841408604907200b200031003441180d021981441d080c83c01801d920a45208a032320040990b29034441e00c49081c04240c0141d4880c1040c01c0c103a0301242e0710040e4502591104a900074001a401d11a04001034005c2c406c2c030001c540041d092000c2d181700310300400c8407a8800801c0c1c16102148a4520707a0301d090750010381700900410340c003450500700162243c00b500c080b01d0491101040007800020035591007684848010358121240091001d0217042c40280d5550000130301c40103000350780c01c07410024001e001303040032107004558492041e803445e00c80c0000c818806604462070f0b03408100c0f040341544108041c181044552002d00801d040068400d030840710740c04507103001d050030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 640164163 1250 640162913 640162951
    0xc0102120703060f06182715140423151513061d030703060e010b0901081e030910020105160f1403060d1a1b0f09010c082709 55
    0x944d039040c1c00321985818240c0d010204403101a2184006c0d80100c10b840c0d0800407000380e5122804101c0c08003c050007010803094070b50b6064044803a84601400d0303102808689030003900d09095001751418a0b03941d5000035811003002c04126008415130305e8005800900c0c400d082c891620990424003000144071980c602013280a402c070345001584101c405104495035541601c2540e044445030a580042c1501c40c440d86038030381398008096810a01c01d0a40c83d125040001b42440c4940d64180d1b50400c0c014076580c18040641505101700701e01214240c081444080602d07150064191189503458001066130314000648038481803034400c55008203e100c001d000c0c54a600911412401c40009084a640703a40714008603020740004500140b10103148500202c02500040390503004000d10a90079003040325906078440c841c006c03203c42d2a01240d0401110320650b00a807078001d003052041e500c580c01d290400610f81c00d1508030760117070f40b075803510307640c0d1000f852034243c0c030759a441600c403e191a4920307a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 640165413 1250 640164163 640164179
    0x14090d030915020c1204030303140106050c0a141f0209041b0f0e010e060309060f01060c020114030711030a080619080c010c0c0f1707080a080a0e060f0c010212070306 73
    0x5000e040850b10a81c3c001034520065105114441018051821807a0b45680e00d01c2c0c01802400c88016031a2a130701040000f0800a100d04101d901d0702d020840140542c10141d19403605000d00d00410003118400c1e00500540340c43d40d42c0078a80c010b02d0410340141c03a101d503003080c84159104204510f01c40c25810b0b5800d184035800c40600c0c100380d806440c114000e524540300585034814002007481c3d106901004200f2610400220f00d44a0041c44c401c08100d070b607a030401500d000c4031800d002030115445294000c0489410070196038000e0340c40c0380071580b41d5441804039055900c00d07512100020704541c2040440c0c04c0074404041e484502d1500b040030349240c103525584500d0003d12043c10083d46450120501941c09015409440400083c001141e034804002c080401d0250450140780940e00c000a021100466800c01c42904000c03450716200e1141d4089810410f9142080c0e40440280312034083c040400010703268415010703000503914010340c0442c4141c00d2000748960b04041c2012024041d0344 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 640166663 1250 640165413 640165433
    0xd0905191211030106050d080910110d050f0f04080312100b040302010e03120409060303080921030408070506010b0d140603030a0e0307030b1e070302120c0a030f14090d0309 76
    0x81e80101c0180b01e0018aa00000e014240d29800594444080701008060058100050034103ca045030b5155100081142c2950074042180005240c0e410403c3c05403d018001c50013003082c2003200611900c0c1ca554005808050740144d00710003103c0d130010814100c0c1050042c045030704200058691080f0034905003080581e4404c40c0002030400160b00f8000316591810000c3d480d0103940d4034005900e46423103981440c001e066620080e0005600000440c00c1181c0100f19440c61007002400101e01c1403103c9054101644007610480e100c9070100010004102c06010701400381441d420015900c2080c40c151001380c460f80c0d049803520144210078080030b40c0e400001c032160070380d007070074204060980c00300020300700000c0d6400a41032807461420440c0307041010201c0301f0304184140101503e5102e1880850481c02102c40014001603040d000c10140001000036040905040c6000b09503145904c200200765440b128140b40030100311801c0c42400d035420300403041c800213a0300d0b0402855000341c90b402c40007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 640167913 1250 640166663 640166699
    0xe06100e1014040e0a0b0f070f080633030c030a06080c0f041d030c0a060c08090c06031003051e0c0f01091701090c031103190201021f020c0d090519 65
    0x343c4e42d0b4501c1d007109000520180b00d01d40d410080c80310b81c5180222208003011422540b07080041c0400c2034a491150003144042e003d8200507102c0c410401c0755410a4001c003000c442c2803109119903007030050342c00e441d8900951117403c02e0310b0b655449041822404098030501c1c1c104a2003034010159014651b1113070b081440305d002d802c03a070115151003a0003100910304503c51030650507000014200000060000d80c81551034460b40c0100304448441030b0440d9900c10a40f940080c6801004103100c103841c1003000381d40c02032480000007022595075541c0303c0c6402c1c0100381040a0300c2c0e8416410714400c00502c107442201c10140e030503106881d81100020882442c602600340150440401290042e00960000c10b03011740c0102180c0c90070b500d0f410100b805030307c000390140c40ba109825906000c445081001d00c1a1503040c1c0040028103203c5408501404600030a00c85082d401d12090148540422140300d0810998030b0704d40c2c580307090106000050441c100601c50000d40f62204028501c40c1c88281d82d20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 640169163 1250 640167913 640167919
    0x90d060e0c0a061d0a180207110415121b29030709090504261c1104050d1406011202010206090c091324020d0c090b090d03030e06100e1014 61
    0x801242030015030000300c2a080a610040d5000b21b440b4000c105500620b05580110701880d1142084001c200a903040c4009a80500390200420814515140800a045880303006041c080b00084014805581c40551040064041c000c0f140120380445401c0302283c0d110704500d05140d0f28101c11b0180c01141240719003110705903260006000d00c000158101401492504008000c22449445945942140340b080b0321004501005036242c40d19885140040444070b02900d007018903040410001503820b15081e202801203101c44c1c00c012400f84500c5010384008035404100c3c980a000092500c64020104031003580b04228404c0e0f503030b83d043c120319403118282526040341d4005140010303409a55159481404801a06041c0b003d5080d0b000f41000c980c4039541002400154003048450420380e101d211009001040010014188510409120f5009060200d660003a41542e40e240037011680c0070030640da4440240104c0321400c401c5500300026517010240c042c103042d84a1903054102031380c148 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 640170413 1250 640169163 640169207
    0x90d0f140702030106150206010b0a090303210c0f0e0904020f0f060f1206120604021513080a0818180c250311010c020d05030103060908090d060e0c0a06 67
    0x5000d0380c1640450301c02a0b8058000e010300f0b591002c001c1d4114000f12605809402034000100700e218000043c1c1e42821215598000c110703181d601c0c103640d081e420111200042e00b2403445d48500d03c260f4020b0008181071030351500001020204010721b0301742c206081070b1007620003c060102696809990105641c000c5130896142500000011064401c41408128448020030a80c1c800f480300e0f01600c3c4600000d58241c071280c20030110075a00c403081258000d50040802c480d46000501c00000b505283c6840080c3c4003455031144040c620f003443e40740040700c202800240020b00120328034103d00c1000340603291036000d0b910444005204c0f04008003c6c10700d204002c074004100310b0a54070b042198001042020442c0801810020600104420602450360030417035a00d08040c80001c4100840080f43d0f240360a507401d40e03a804000d84860413090b14000418804000b095540e9124401c4591054000092008003101d425013065003000c21070344a0461000704000942d04400085c030078840071a1550307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 640171663 1250 640170413 640170437
    0x3060609071d042c0d1818091e120809030d0b04060807090614040204050307060509010309021215071407150906110301080d0c02130504050f300c070b03090312130308090d0f 76
    0x1c00515140c3c4020b800300745001e203c22100701d01c8030f409c908103c0c05030a01c0c492840e000750068405000c26642e151080d4070401040091103074075440348116107801800130800d0fa40e5107488034601100c1d908030083d01555103030100035904035105000c1100c881a03500354206898100003030384821292060380140a80041d620080e80c0c0700c0d0384400d107402e41c01001e40c8140d4211080d039560380c1d05580508509014650080342c0b01ca4040e4a41d685000d1591a02902d844a15a139510f095920f4aa0503098107407030310308100008075913010b806508000341145580320361408014034500f1800740000c80c14072901d04040c0e409a11095022a404003940b400401c01e0348851400c00e14001100d01c800c441801802256200c030340e4803a588032184184030244106070316068403144128442c0c42080c441c0c50340700000070070840c54043c1c055988241c000c3d00f03030b80c01c002076010100b908400c00c80307004100c80c0c500001d0004241c1c03c005001e03003210510006290310607076410080c0c641d0280c02404024420341c02891 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 640172913 1250 640171663 640171709
    0x1009081e07020603240102010905120a020106080d2109050c060721050315040b1f021203012402010212041e0f080903060609071d042c0d18 61
    0x44030701940c090815a0ba91408054080d605020802c04092421684160000540c07050244020392604003004e00401610500800c103580d0186061109654948000148c501420321095055920301c1e11194402d81c085410448081c90076481e1080c07203440c10390030101196001800751002a8143c8425a44850504081e4842501801e004900e42445204126900e52020145020321032100600758103400c1d400411080d2000b408550343c02100400b04540038104040f00a041407000f0300545495030644122200c041d8000d07009032a0030340d81580e440040c0c200500b1808400c030702c03a10007141070141c0a407520203003200240004e0a80318130101081440b0b05080c0061014650003205820600080d00d002c00c96030b082448098428001d52000981a050a503002032140001b5540e4110142c41e19400c0c0b92410030741179825030040e5032040c2007218241501d401d03501060440926152411007100c0003841c10900302042e40400c400885200f040040000c07540040d10000b48411100418500003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 640174163 1250 640172913 640172917
    0x6010b07060212150108060f090c0304020d02090711210a0e01050405030114040506280c0c0c08030310091104230a0b0c070b0703080a0513020a090605031009081e 71
    0x43d018001c1d003410300908102d00a161a0210030a0321503005a6640c1010800c0240031461007a40200c1680d00154400c0115030045070302510041c14034102d1041500400c15103101214200085055150300c4210403000304656188203a886408540029100f424074400c1e000d140c0b241c1c000d02021001c0c0e01d2040e1b01400940c2c018200140007000740b03050f0142c0b100b10403141a41e09a620703018050120b840783c0d9003400700e0441a207910640551484255011000900036004004200001c1ca600c5400007450621f41c000200b90b0000215103a08100d2660310640500c0c0c1e100d0034038903140022148010103008140c40489a000b00002c4094140c3d030030420404070046810b5901c01e0000002040d04d02d9840b0242c13011000d240110740c455a250102d00d84e40c0d100300903020380440c29405c0060038802d0541c00c4940e1085007141c05e583c101c00141d003c29825440c503000b0241c3c0c0340c1c58038818080ca080130000f0202419407401d080c004035090f6216560a8466030a90088050741d00005c140c1d04550102 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 640175413 1250 640174163 640174177
    0x90111010c020a060617070b0c010603020405240409050c060d06080328090b090f010309060f0c0e030a0f0b070908030a03090308070c15020c0a050a0f0b160206010b070602 75
    0x10080c044940700410094a6444110341150800d2400802080f42203c9564208003030000d400140b511505140f468841c035042a05074000f5992680030200068030349014541c0581000c0d6188c5a0072404d1100007152691000215806a491b28841c0c44c0401c074000b505030071255055506940d62004406590f003c0c01e0f003500008130038400010390b0200d0a00c0c40b07140c03284004a0324000040ca011004049038140054170600074000710902001107140751503c0c00744a500300c1410005880e1500d6650742040d80c10301350b683d015071a6070b608001c030100d400c14490907c40c24110080d00c41c0076076a07510036000400c0b1501c090821500c1c0030002c1c0700c89015001c640b011706800001c072502c03501422001005070403040c008500259901d00821040b60041e00d001c614580d10420f48040d80001690503002174100c2c035080c2509200341050513010450a1099540b03250080c1d100d00440e900034107240d080c41d10080c03e2120200a03030450300b11929804034586040d11004501e40b40c0e541410f00304040a4080d000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 640176663 1250 640175413 640175447
    0x40317090313080c041113050f06070b070c0b10050d110118031b050a2d1205010609060e16030b0f0604062706020a08030604090b04050303040302010b0306060a03080901 74
    0xb0501103806400061180c00c1075070100d40900081a10314440c1c1c0650040120b81e01102c60041000e102c149400c045801c0643d101519041c140b60060b21220501903065a43e000490b01b9040264184601e00003600d038000fa00909440e0341c24a03100100340c481605600207401c82c988051b030315805a21880b00c2103400400d95a65064507134403802c1243ca09d90170088441c9000d074a9a00005142c10003a480d40f0444000b502c2c800c00d440303003103400103411000c030340031102401c8600c480108000e02d20014941c007050017000001000c80c107200c203030401c4450a40003c003007441040c08100c90486000c100400520041c900400e000b80828046001800c1002d031031079104c000400d02240c003543c4524000344039034a0b40c204940d1817020603241005c22019016442c0140c1080c0e1010002c2502d200c01160002c030044c000168914881d168075404100c03e46003201d0b690400010312092590902400300b0040c41140034003200d080ca000010010907451000405248000c0303007841c0a80c0c000d445240d5003903081 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 640177913 1250 640176663 640176697
    0x30f040204060b0f2a0a050d081024090b0d09031b0b1603021e0304061b14090609060a0801060215100e06030a020a0306060611150105040b19030308040605010803030403170903 77
    0x6481d0198903064400364500019846a00042b4a540130081c100c0c11600c203c000814038075540224034103190315104c030140034000c0c003150002d45002070b1002002109105070001036000103030716000f041d0510914144540160440036a800304414007144e5400c816580000c070045000c000042d000303400385c602c581c01840340c1802a082d110742e88d40c0c000c510861044c4030400414851800c1003800b2800305c00e003103000460001500941c214808001d120b07070707240100b049040c4100c1800140c035079405a10401c0c00508103100403c002d0b6010001c0302c66880140754003107800e25200400c0f8074000200d00c5014449645100031521a132014072100c140540c01400042c019501c0c1c0c01c20707101a002922030407000810f541994940c04402045c681e649901c40880d0024991800042001902281c000b90f0b030f1282c0740200700020361200c0d02e5840015071003911050380b2460030341080e000700d0f0016403141a044e0402c00030403000a0344000c04000d13120407000c80407107a884001c0318510351f01034148521298000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 640179163 1250 640177913 640177933
    0x613020c1b131e14091015031b15081b130306020c070e15011205040302070f0905071d01051e0c0d02010608011104030308070c03050f030f040204060b0f2a 68
    0x200030500d001d900402c07034040c018071000920031351125804071a1609150002d0466107541c00c2e154212969602c045070112020301d171251101c1140108280d2400b0140c82c8001041014400c0100c5a40003009141400f40c807030300c0c01d01601a1904456442c0c0c40d85e40c071001607400d4104080c61480c001464115400b1034039800c1700d801d40f50f900c0d41a401045070542e4404000b4200c00310050856a504038182d54400300e89111544040252070080c0c070481c158001d580e0042201900c100b030510040c52198070120782410326410181c4851130321030724580002ca80480101069802c042110b040c01150a140c40045506511103440d5029240706243c09005400b2810005641500404141d07084803008000a403040c01b0000c2907803041d4440240802d43e6400000d4030720740901c0d240400c0394000c4c1815031130245905011502030344201d500e040e424034040b0904c42941081c2c071807000504400003031240b8080e03140e501280d03a40111441c01c9180c0e440407200850045138000c0c28200005654111224400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 640180413 1250 640179163 640179191
    0x80f031009020f13090507172d010e09061e0603070f06020a02131803140706020a0903051033030c030c0e131203230705030613020c1b13 60
    0xc414500f41300c00e40c0c0800700108494015100307645c01840c0c151036500e02080500c0c07a10070340c3d490041103045240f001491400d5541140000c821080043c07410352081581860411100000b001e08502c4c099484442000305c160f14a0010400c0e02e200c406200c461961118000f0340780584940110101038208400040c960340c0014110400034800c40b00200c500c00b2440d443c908489044140c1c44513601c00c0c1d800800480d0003062016055001441024940312868440030140e90043d00e981c400910030507070401c10301205000305903022060790801d21140c64941c0046217541c0308040d0240913080c6010f1490030418a142400c0c0c01507a0040c0c0107580700d9541d05004514044c280f09800c104881f07000011040710385c00c03118886036980031000c0d0f0340038850000118010320f1b4403034031880b49844100c0a00d661016603d5450722858850365915070341d1034a00244403006006c5990900658018800b2803507200c4c01282c01d0841c1c5c00b600d0150036400c0030040000d0110200c1c041a046558684905400102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 640181663 1250 640180413 640180417
    0x90215030117030903030906070f0c120c050108071e0203040509090607020d021c080a0e100b010210021318110d02070201140406020a020d061e1512080f031009020f 72
    0x42002100b1428242e03007060041e168820b05048541c03582040000b40c8041c07910701c000d4100540a25034500c00c1003220ba8076066154495000403c2c1e803580d002e000800c004500080401900c1c017880c1002c002d043c0042d0251005800c540000300589500e804007600900c01c1040d81e008103002006084103042004a954607080255485001400b03680e22a0200fa40005401c4c110b50308818280d03a80720800100c1240d5461010345410b948a4480403503940250041050b69001003003a603001035807068220029182452440c590340e117660041c4014404101c81103a817904a52000d4010394450000c2241c020040600e130b0328402d0400300100f0840ca031060954054000c00313200782c84058411904450245c0540100d100b5000143e1002401400504001e0341c103040651007060f000c66400341c00c00403045504074030040600e08541c0ea0311809090100c020610000703111400d9140b1814003a52100c1c02140700d02c40307620107810710010100300c0e4504c1c085040402401c80340c0045458440324540d140301a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 640182913 1250 640181663 640181669
    0x10121104050f0409050f2b0203030c1209100f020c06060109120611070f0320011401150c06060602030904060b0a08270a0804260601060e0a0b03070504081218090a0902150301 76
    0x341c3e000b50071f03e8036910300000c1160300131115203a0103805c141450860905240008052000318040c0c4000c2d004011210b01600029100000c00076881d0301a20740058030b0044018241d504201e1042c004101d003201d60078101710b81941051011076019081585010241b10744030300182000000160502030661002404090042c810000801d01d440c800e44a0b00f81c45010006104da401000010001c0c02d40e0300c4080652501a4285003820015986600c2c01311140d46d4410000b58000180280503483e0604c903103009003c5002185050858403080105850001821400755811031001191180f00c04d201660403024250100c0708101c9142c609081c89070000d00c2203040b98425080206219040e50500d40c018035a08002804103a1030101e08803165850002c40c0c80d004604c0d8076004c65003401010045100d1180340e140d0720f07555840d00302c80c030b031600b14824441580b000c010f2003054003e00c50b258081c0003002c4200d4548034991100c11600b0300a10091100941c41a6030f48403900740040180081d5040b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 640184163 1250 640182913 640182973
    0x2090a031112031810020c03010c0305100602071505090a081915050412080c040e0f180a080a0302090a150e030c03070609090f0b10121104050f0409050f 67
    0x24030b40040090795520702808035039810316500504980036500b4101c105920500c403505c1166440380381d2502117400c45000b0019000001d445100b0800309641c5600e8840041c1114401810510315003c5580008000b1040010070814001041540f40e07032a42d5005016084910969544a94013074809502e100404400c58421201505d4003c00c85401d214542c0f04580160303101004102c4003a0442d00300000504903c102c110070701000c6110454400490311a9081001e040c2545c200b505e00c030848104c1c180c003810340c10742c0030100b90000240a5400d881841546050260b142c5030301c4000900c101000e9080340111205082c2002852540304180d01090385082d425260b0455542060607140c450900440000c0f5401c0c0303004010000f4035500c500136020700690009650700c407010008490618072110360340042c00070900040000e105226044000c0f110b5495580362a14140205107111041000c042c07240e6599560701d01800001d0044000d20701500054403898500a105110106202080c640d8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 640185413 1250 640184163 640184179
    0x3050601031406090a02190c0c05090c1c021902010209040509030406090e0c0c0708061021031214180601080a020d0b1008060109020d18020114090402090a0311 70
    0x2080d4080c1c462280b00401101d026040c640d1114140591504050600c0070901e40c20009200341100b5100340a41c0707407410783d075070407402c00140c00d06c0c18086145401403407080c009a01402525030441f000c480b5451580811004d0420000a02c07034001e0240d48001606180035100c00e56616a065004081c04d600c100c0f0108130a494019040c0d80e139002c0c40c040c00340071550981080c090350080c00300040d800300018020614219a94060720b080156551000c1d1541c1d00000c01c1c400140b90542da01006000a00e074a6001c041200c0401d00581c0c440b8640903081c0040a0020404030380103800840c3c0c1440406c0302e140a6041c41039240841401807040d105c1c0d40c2c0643c10000c03c5c440310100d056402141c0041502c98082078586420301d420002a001e4800c503840d1403170008858605202c6103000342a4444016141d090f07920a00054512002810010407c400760183c010703a00902d28406010b01845160b494000392804200248aa201c4045c2c0c00051001e000040140108920b102404151040c0b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 640186663 1250 640185413 640185421
    0x3030406031b11060105010c0c0f0b04170604020108010e13060606050d14060303181201050a020702040b040b03100531020102070602070b09042d060303030c02030403051b06090315070305 82
    0x40f40030744407012010b11908840010031280d84260760300c40d504c40c0150301c01d119440e44e4080b000da0307150030b030340c44000782d11030103c1c080010b180000c00d12420441c1060190906142030b0f40000c0c032007041401640354034000c0708041103892140e480c196140031350044c42041400d032958005409508200d070b80460407410500144080ca0001d50781034001ca90280c011414a030040c400982041c00000540b80c00440200941c1e4034144c00f400f1715070041180e00c800617034401017030040c0810745012441050066003411808200c0f0f0b200000c4209103000c40c5140003446031160f1880d10500a03641c14941071251410b40b03d20f5204010000e042c1405100b6022034a8040d42c0c0c0c18242c1c0c441b4490721031114155410f000b80c28036824150410b031401d45045990402c10854200e01000d000b10701c1c6d641c2e09070159100c009104142c0c140c42001d80c00c0b000c45c0000c504180c0385503141982d5041d182281d24100c13544624015640d2110703c162004440003c00741c50b58050000083c01da401400c4134a4000241010041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 640187913 1250 640186663 640186667
    0x603070501090311040c03090209040b22030f0c03020712031806170103110a09140a0b0609030c01110106121a06010903020a0e190204081e0d050405100e03030406031b 73
    0x200c02103039404003807130f80c1c0740b180001004020010012120300345615080c2d10001661a246420301c00c511808a078000c034145480380c47c6000f40c000c00304030070b03100c141c16213900860b4014074030321a0100d2038645000303521501d250072802c103881a44220510f81c4030541c050700f0144c011507500380100300048030501c0103980d46001c03285002514031800c2500d07540d000610128070f2441031403841d0880909070b4000582d5a4070400300b1607540041c1440700802000c1488000c081c1070107464241e00302101d0007824a00230400103504d0382c44450219042c0110300d0000c0c2304481c800c6d0000c078000c0c512001d15110310680c4d82025000a071907a005620034607601400213180f5070040c902101500c0c2c0240490022a0811204400d082405080c001c2c404200180c151541d9200380014405091848080c04041c011248009041781200034404078503000320a0317202946610800b50ba04a42d02224191b0760501c04003015203040c0ba420451070f4250200150109482e0b070507420081c8040c00c088000303503010310303030441c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 640189163 1250 640187913 640187927
    0xb0a09110603310b0c0c0c01030c02060105010c021302030a0c0906080c030609040303140106050408160509040602160506070314060d050a080f040f17060c030108070e0a0f140603070501 81
    0x7003200c0c6420f00783d80c2e54010354001000e0380100d0854504014a8180e40d80f0740d403101c101c00719501358820900043d050485101481205140c1400b0b0800307110005011601940700c02050244604000d100c00000c0155514141508803080781c1c3c3c60708650300d003404810300024000c007280a03404611100720000304035220f8880c0a1060300e82800c810f0464a9410401881c503901078420b0b003c02d034031144194414454284902d0080005172103482c1c0d40c41c5800c4c1540d0401d840d0800c8080003a41802d0b041215807207a0107450303807050388400b0040c2e640080740024010610031601c003070a144198802c01c020f030b6405a11210003449200c0d8040040d5641104206c004260410700070300540181c0d501100050581d4050540741c4900c0d1100303420651940706105c1520125403000000d00c0c413810076072030b000c8000c0c0400303900a00c20036041340c40c6604105581e0b41d110820b01c602c100c00c00c1644001500d00300705600c041c40880100c102403041410032031703401c0d00034070040e02c46d280302c1e010315100016a9030003210 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 640190413 1250 640189163 640189171
    0x40e0a02031f181d19050615060301151407060204230f010e0406050d060f0c0309080423060706090204060611151003050106180b0402040605030411010c0b0a09110603 73
    0x1004102ea441c4403220f240501402000c0c803030b18000c1440b00201c0e1400602015088403141220302d1411406170906624094018002540d0504d420070221210f45846003100d0560702c0300703041c801e200f64170382504881c0000c0746013980712400c501207607103030822009400501c2140e019902e2a00120a944622180c19100f000007a5107c0c4002e54010119401060314003000c2100400c00240b03103030303503802064000300d0480e0110780c0e10356116410300420080744039100110f065440c080040c0b8505036030b02c100b5440707a4090044500d0008095071510244a05c5800d940d170000303058a1707200c1c034481c40e090018090120381240300e40e080c01c0b0040707582c074801c034980034016001800038484400040a6006a0807001c0e00380c00c12501c030400c0110100b1424004d200040040a0580e4000004200d200d0304480c00c2d43c0d00c0610550041004101c0e942e40001942e8010740c011141031172001050005031505c1c1710a01e8001c2c50503045070b082094200d850381c080e5030014010000d0b000c12010000811001e48403c50b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 640191663 1250 640190413 640190429
    0x412030e09010b0d0905070902211005011b08190509040e010507120c02011d0601031a100b0f0c070605030a0f06052103070f2303070b0c0f040e0a02031f 67
    0x200104454810039089405e150703005030192500e0035140c0e140c01007a07074004c240034800e540080070880381180e0346032007295001c034140314003840650030040001d140000049070b000e1110740014012052029240454980c21a0748076610713085614004c003d025600a02a058440c0e0718000c128240d4060600400f03214070500c0d9190303440d100302d00081034001c12103844550210765842c4400201b0b401010010303180b00918400820040d0315601e40f034030550420b0140c58561121910503c4541480500200c09468141031180d44400c11030f94020194010860440040e2041d6072000420b550824011070040880c0c00d4280000385000f4151310542d0418415a604080403181c0c2109004e2690400c0c00580d10a009480c0f4120f4240c807a0106a2008072042d2038440c005c400e003034104158035000091010200e000f0318102030f069255407803c03010083c514042c01600181c00325a404d20307401110050003040e25100c14909000b042c40000390000c894011800140b0790741145c032201c0d80070703041003103c0c004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 640192913 1250 640191663 640191667
    0x61b070510231515120615090d0b0402100915030c11030a080403080703090203030712170a1401050906060711190834120201140a02010f05061e01050f0705030412030e09010b 76
    0x500080003507c241000300741d00c0a2080c02c5042c0d40340200c248449014107151821410700f030041101d158040b40300e00d030920009000070444401c10f2454900c883e100c0782000202c81c182e031142a50700048580066115000c0046c07912411504a0b002d04e0046000c0e68400486a407500c0d4190112132a03500e01a41c0343c1c0c0f050200034006010301400d4801d04280c0d1030400d1082c200150342000105083d138504000944031008809210795400d40d042c0103150484045030b45007804404580307144601e100280c49507424100305070303c03515015262034000b080f041550400a5031030520607100c110001142e4072008504100a05801d0304d109640000c0070151410300340c040c50315061109459500c00102c0c1404003400320210306d0989000509004071003178001113549880680260100d6000402c00c40c40350301c2001d00443d4580c00d80c0c844900043c400c0c07c00c60b0f5256100c1c071400546028a003001001403000080209118101c402c010180314825151994044106420441f009009000e018101c2d001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 640194163 1250 640192913 640192921
    0x10608030f0c0f011506170c0301210503031306060e0105030319030b0301090b0a0f0608120a1809090209010806150d060e0d02061b07051023151512 65
    0x300c0c0d40148802d08658084a481d19a00600c260a5500125403007100c8106064100511508840c00c00070908070203d05451074034107141818504c0c041070081d0a102c03111078100c140507102d200070801029404c10116901c03440c0081403a800d40a9500c01111002d040c404000b51180c07000d21100d040c0c8100078041e6041c6500c00e00da06492102d00b80ca840d0800d40c9800b9103204649083c0304a00d42c241c054031803003489140292840c2c040e1851440380415072440c01342c0c00c0080e80030118200000b4110014120307641e209444040300c2c030400140160039148651000090790302c085a00c08140c66100ba6002d5030b6980e6118442e035102e0b0001c9420407102800002210414500005017009d00341c4162000186001031924852526002059450140e80860180414584002c00003d01e00c42d2052429190246035070728103466449105014078455260b0742504146640e004020950399104180356407140f400020302004900390044140c014110f004544d058078042c5011200c010764403280d00b42d42919 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 640195413 1250 640194163 640194187
    0x1202030a020d1707320d030c0e040203090c090105063c0316080c04051f0e1504061206060807080403020f07090203090c010e031009020d02060c0105150301060803 71
    0xb20518003215500090300700c0c0074910f200d04024044140c01240d42610000185c3c04000300480c0c0c181c400b000104500924401e150000100701c105c144261a011410304c0541209482c6080140c0d4120740c003500100801108600005582c4001041122600c480343d0b6600180a05481000e0360b0610354080c41e03da448020f24880c0c044008203988140e480b22076002031006406c1c2c0d410540c2c4c038a01c00c8134181c190041007a480000c90341c0081c08002003070718052a240028042d2441050f20181c05441415864880b600070400c4408001d006010503954120917440e9402e036610030300440c40403d04012503054046d0b1288299006e507880c6071a42c20ba03680380e28201352904407008108074110301c219502c0b4200000305100d17500041c80e01c1c0d8400358a03410032111090810030504001da04002060942407100e0b90002042c0190444580000945c0f1450340003080b000070b03010310040d4200e000041c0c0940051415400b503803207201403900b40c1c4a03003225a0100341c26910b00e0720a03c4c445902c18414525425 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 640196663 1250 640195413 640195429
    0x19060b031207120e15341109130308060a1a03040c0f030f020103090f060e0a03020f010221070e040203101d010510030b030102040906080f1501060f03020708090d06151202030a02 78
    0x151908402049044600c8031848141b441d031140400001c0c0034141c40c100200782004080c0c1400880300f00380549040410310b1000010240c0c040d040081e00c1010400d5030702c42e14134060240004c0958004000500304040c5805d034800e48044035465009400012900301003156902642d9011819102c0005513070011405003090b50000c0e44d40005003041c42002403070911840441c2605c0e1005070440588905019052081121035036406900410107542480544450f080303602c180421401d00548448c101118203444c8000d04a4110384000240940c0c07071f075414540c000715007003818141880701010034210460f80c3c0a1003115044141d46100314222402900402c103280d00c0035000605141d6550505000c2c0d44c150351107009107402038400b80c1c0c415041844034a80307442d01d01094001551425000a0840f003003501c81d4010580d010803d5810881d00c01c08540310000000c0c4002c0505900e414280000d10160105010700c10325010002040e40c1142080580c01e9001009001440c0c455001d0003109 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 640197913 1250 640196663 640196677
    0xa02040902041d0c1212041e03060f060e0106020a150b18132d030e040e0d0807020d0903240608031902070501030b0319060b031207120e15 61
    0x2007034850750180f003055074900d202526040b02c40020120007500c6400c1c042c0000c5c041c5440300c01608040346025402c0841c02c101c2d011030341c160080243d044015050240c8204441c0c000500715404c2ca0400300100d043d90f0000d1007540d1808480400b5079030381c5e074810399a800c080800208041c4900301e003500b41403855403050703144c080c02418100c111259504c1041c0c003c08101c1c0d42c03501098042028906104068408000032400c4c0401141d07821494102d000181010450080401c180b03080e40f09400e0f02c4542004034184000011100d40500320b0711302800d030100455074040184201c224000c0d00a01c120001c00c04c0300e8000d0990080d076609800c01301d00d82c0c121240b40038042034540b20000f4000d241003004003d013a8003962051152800840024101038240d4059030425007000341006040e540850200f80100c03503030021000c41115841d0180281999001c26503160144003441b90885040b0401070802ea4402c0179100c40201c01001c00783c0c1d2003a481182a07400c100d2450030002605405402003010b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 640199163 1250 640197913 640197919
    0x405030604060f0e0d021b06071a040f061a010e100e0405062e1b0c1202030a050d0903060e12040b07140a0c0302040b091909020118030503070302060901050601020a02040902 76
    0x420701101d00c2151a040c0c444c0d4917540103030b010b0804101c07162940100000607a000701c56161a080315515400c1002c0d1009041c0180307028560b01103001c201c0c406003005159584600e0500c83c410200c91400e485a103101c1c1c8890100740c10100c9015246020321031403188420355200d0310b1703000c0310b0942070000400c030040099821804440a81048600e030212200721640030040c10014074074520001403030700c80b12800381c2203c220704256074000240d06003145010740d105e841300190102c0c3c06000091a1401800000c0c019000e92110812841c1c0d1104000d01980c0c0034039030a108141d046485960f95041202c906122030006010500000c0d801c00014040903001e640e12611940c0484801c0e800c0031001503084442605540c01082141014000c5038007600d406c945886407031400048502801140302140700d1483da9400c440c8046a0068517511b4526075642c0e0300c80342550310703441c041781d40fa80043c1c030550151042500040e0320480501a681c41009e040c0d0207005090803c0d82400007403c0e220408a078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 640200413 1250 640199163 640199171
    0x1a04030b010e011e050303031914040507050102161401051e0f0706060e060a0b0d021b061509040c030201230c070e06062d0417070503070b0405030604060f 68
    0x1180e0125915406011181c803910300ca075261080e0100c2c050b042c0d60300005200b110f10700822241e600481030b240c0c0901e80542d46208510040500070007400d024a0a00d003404031041030200f07000001038000155070342a0200e8840c0d131102140c008000344584900c01813035011401c1d00d8160b51145003d01803141045080c8280032104002512003500328894507002c1c4030020420a00384a0700d07000b40c80080840301e03840b07021400e040c1c01149900c2c480f4001c07212510b03800505c1880a140d46c1d4112900300c41e440010160303003907258003003e0300c0710703410380d2501003034000001103503500c1c0350010456000381e510555060002d0315660054424403040a50f040c910f94442d80e401d03054640300c400620800da03400020744903040c200b40340f0000700000038212038003c0c2d0781800f040340110420404461a285540102c510b000b058940441c210b10860300310240c07030280390003130200341000002e0300c0e0251a01201a40e528984401c400b5210340640e00c03901c0d52550208000c540400c48942c400c0b083c0c502d404401207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 640201663 1250 640200413 640200419
    0x3041101022407020610141210090f0209100608010608061807020c0a0f060507020103090c1e090b091302010f0215091e0a05030f0c070e010b03060112050c041a04 71
    0x1e40d607a0b0709582a0411050b08030400030a1941400102c1c0c0c031007800806050720504080c1d014030a1840c2007546070040410a405042030345d8200b11801e00320105907401e010801c40c40c03904208120070707480100c0c050404000403900d1a43d0756220001500d0300c5541d00e002c20780c03805101300e5200c00090500340d000254040105500c244880c5054800d035200d03001020b0521050080c085586407a902810001c010044107104156100e03085994280e02403901242d544c0c810f05010310360750103039481050503c01c91104005800303140186d44084640042082005456034000c7c40b020034002c4506060b0310801428441c010b41c00b0340221340c1c00d1026441100c0024015a0b245800110300382e403400900d0b40001c1c8403034080a0080506035100880c0d502400c52300300d4540e03031640d90b8040c0189074503003094045080840c10004105003030007000c4501e404940f03540e541c85051240d0b481540c00c180001c05400700d41c0c0d54404d85015075402451201d5281e440c0904e0488400061103a04400800c0c844d0700b00000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 640202913 1250 640201663 640201693
    0x120c120d02040f030f0506090f120f0c0322080f0a061a1305090106050a03081914040308090f031603060b01020c040e0705010201051303050403080904110d060305010f0603080304110102 81
    0x280f8042c6101c0c41841800300024102107180240040c1044516400301c6411402680042020344201507000c05844d102e1407e101104d20b1401880145043c610021581d072013441e0342080c0340701161029607454407646803100805612400300005150581d03206150300300c00900c0e668040c2444404030521000101d01c150002100d50b02407002c40300d42c981c0c9440c00c2c8582103c0a00c02c42e0000d003c119404071700141b40d45c1c0e491413240035400b1203503d40748103078038200d99842c00b0b030040c80c0c0d00548258140380d95640748c1c41e0988003500001036403402440350484008142c2030001d00780c03102500b0f00c5960380c09149103654a030041d00145481a04502403404400c81d5900c0d0b5010f10880b0314400001b81c200c00e8105800282161002402c0c2e40c4034203003903640344000c250054220740a03680c00c000c040350f43d900032901040140928240d42803081170000340460450045501c83c03810340e4403c1000342319412181d52204103684090001414000302000490b0000d0a2104840070300f15041c01034030141d44210702303d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 640204163 1250 640202913 640202939
    0x30020402070f031115010506030604061a03011508071220070c0302040b030102190f02070f030818010203030c0a180308030f01030302070501051602010f1101110c120c120d0204 77
    0x402c0312156809228030080541003201440310306002801842c08030085881d900710900188542c038040c00380040800c945032256000000544919180c10003035403c0d00c40303804070a81c024881c03c5143d02d8843d03c010406440340c190b80e80900f0040c0c1d82d810443c80301016160003024054003111840e01d181800d440c04a040c07101400166001d40c002140c0c0b0362450041c0010344258200c540e06ca03910400c03081c052400e4442c452200d00100345490314071081d245a0991400702142c20002030066440f0000080105160091140d000010308901a03800c0250040e40d59000640c0c911070842c40902c607044801c1d20410300d56409072103041d003100d0700302d60300e07110410203500c01d5406540c0303a0349031801030042c0b54041000c000101402c1c078115241000d0383c000c11401d000d041000034104111840d007481201c0c1b040d080c03d421441064002c0101ca80c0801c01108160f000102c00900c070b028a90500711841c4070002540c3c61fa00b9000003a04008104881103001507110410b07010101e90309010103d404408220 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 640205413 1250 640204163 640204177
    0x9070531110d0e030a050a110304030203010513140a08040b0c01060f08031b0a0807121707030c0f02062e080a06290a050603060102030d0f14070930020402 68
    0x40d031a6a5803941d8289101519003140f01d5180ba948100060b04255038008115034482c1d009180410048003208151401d612841e03001030352542c00c0005008060409045650490f4802c8004203612814100a0780c0c0310100b008001d88019010302c010002148035100038241c081200000041c0306485599082c00104240c0080986600105036161940a8a41d03103900c80101103005250840c800c0d0b50701081e40c820080010f20000d820002d9407107560042c06599a03200c20044006810b2801400c0100200703840756681c03000079045465405000d00214210f4010724204050382c06003251101c050743c1c595500504881c0b02d1400d210001a44601401280304003171150401040c121a8100d0800301114000501c0200300400608800b140d541c51450034111201680c03130307070f07100e9940c680142d00714056813104078815420080c0000503600c15501c5441c410481d1100f5800d40e0302e409804a0301444180186060540c1a8480c85d0505a1121001c000c1c10030700c100702c0c007503036001d40e002c0b5090341c120340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 640206663 1250 640205413 640205441
    0x30703140708060c120a02070c0b03070c0c05040b0d1b030209010305060a050a11070f0606091e061505070f022e08011e05090c120405030a020609070531 67
    0x10001d01c10440b061010f20740020010103802d040c9482c01110a5441801405602915a00044003410092246001c5d001071140b1130347c807a10381c680100060074071b508049084588940d0804041900e142c54030a10f4126800278210107104d640c00e94070b41c04000708040c070716200d00c441a140040140d95804055000c0c5218801410150600c104040d050b100c004d010000c4550920400841c02c0c0b00c84016111855080301391080c0521143c1040d10080c00603420540d1410b04102004000120301150000780019901d030404c030f1281d4440d0b4080404a02c80c281000040d0100155408902840152014103000409100300c1201200d001510921040c48030301140f001800d0340450150414000360042c40200e60100070b40e08040010b482d030301c07140d0081a20600407100452103003ca1070050f2824058032091038903503070419040282e500c2d000a00e0840c010310405001407610300011842d40300304d071405040c5a002c04500c10070b2504104045003040c0d54107105d075020201c10716440c0500300180c1018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 640207913 1250 640206663 640206673
    0x503030f120f011202060a0e0a09090314040e04260304030801090b010f0207091a0d140d050f03190f1b0912050601060c0203031210090f0b0102150603070314 69
    0x90030707a01940c1e02004144040d120345942c01048201c01000030050060350442d00c4560310418440150303002d4000484445c0c01004119001c0341c00c003074650211400300c2c080e445900324400302e801d5001091241d409041001c484c0a4081000101d00c0c41c2aa0400d046400c285a000051094020020340089030150f0010322044010400030b0468411002d1000b42841d007503070501d060000c040e43d03c0e41c043c404c0c04d4030030350b81310082422414440c03049424030300000c1000613041100e0401c0e6040c0f202011003010035004181c81403139100c2c042e44c11110362641e01310f001410f554039003c282c1e6400b102c2c1c000c0c00d01140d880e41501141070b107407445a0000321009501002410f90700320070060030801c464000795500d80c099a036090102da0006030007811584ca41ca060440002c541c408030b030031405005150140c0d201c411003440003003401c1261000a484c0803060420448503542032190507140301c11013840c01341c0c01070b82e00d00c00360f82c40b00700d400c540c0710344054200d500d500d6403a80d8100c3c10b40c140c00380303e080c0758101c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 640209163 1250 640207913 640207927
    0x4090503160f0b010920090d21020705030a050703030e013507050a1709030424020c0406030f0b0619080f0d0e090c0309070f090f0c140f03100503030f 66
    0x38524000e400340c44002406c019a41420031401c0c900c2624810b41020301502040480d52582d0329000070700001c3e4000f0783e0400c182d00e807914485c802900d181540c40980900940402c25003000210084c1d0f158100006018051075900c0640d40d08406c20328441c1000440541d03101842e51540c0000149040081c049140b4a411108042c1207400070703100360200001000003818141e0710605074500031040c1c002807031450f160440c0c2e052440c4207a5110883d245000740c00c18003508001c9410341092800342d002d4400c600d00d0318041200316901800b005103600c100300721781004544008855a0f110a0141c0780b480c0c13102160300564440e4007141d01010742a440311041000f040f4041c0040000040380741010041514408001200c107000105540200380700807001600c0d0283c00c009100080100115440c2988c1c1c6030140385014041c185014100036040c05240203085101361010300500312169201400c050301110f00003540e600151500400b5000d0703090100d410364007400181a1900302c0001c955680c40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 640210413 1250 640209163 640209173
    0x5040f0b0d0c08060d0b09070306050709061107030f030f020f03040b0a0e0402031b0304060b102016050f2b0b090c01050f07050f1506010212130504090503160f 70
    0x20402020003c1240741c00c00d100030ba407a903041080f0743c1940f0880e04079181c0c0d0b924220700d140c81e65a41c005041d45003040c1c10f02003c01c0c1c02518080656079160380e40b20160b80005001a6514540d10000b003244a0203001c00300400c1c030980c0c0352090702c1110f02c15140c010841c0c60549244d0f40054105202c0c00700002400d5010580010400b030001c04152420350a42c038105800c0010007014200c12030b0807000010002d000c01647d644034019030b0200802c00c1d22006240d020080c1840744d043d09028100045050f2900030200001b21304228908000e50460980c0c140030601c6000148000900e81149468100c1c270050001a940103041003035084004c0040e074a2350030036201d200790143c5100c108ad080700303001002c02d9074044112010101c0311040155121500d150080c5080c41400a0b1406805001c024580d55030300c002400e03001d001d00b40e007265201c003ca0f000e04e0300700303128122100407209608170040002d800d140d04032149682c010019241003500402914000035060582114000840403800741040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 640211663 1250 640210413 640210421
    0x71410080a1d100f090f080a14071b06050304050601420f1d09060a05030a240c021504050a170901030f09150e01021303051b01020606091605040f0b0d 66
    0x181818420300000005c2d48070388000100c0100050a00000058240c401c18011b20310440b081c01c1002c6003660b110000d040500402440c0c0326401180d1807040342c0051814855015a40036607040070140c191a4030741242c2204804400c0303009071b00c40b400a00d040406038150000d88106910441f0742250090101360018000383c1e0351400340c010b104c02c98400d0a09484401d44a502140c026225051562102c200003203c101c035035441981e0500c83e09030440104240c1036030212141300480a090540700800281c5400d071555104540d0059000390b1404000c5680001500c0d0400d01030416220900e0301e60b1a403408802410150920b01c0d0300010300100c655274907100350a294003081c01c0030420b040c942e07503854030a9a0707098142c240542c0c4548242980d41001c2d0b04858013030b04002d1034540c0699891610079140c1040681c10143c260000c0890b40280d400498401c0c800d001c0104040313003d6840d0740d40480ca1000c0c81e9108400c10000b4000810f0a820f060280130260401a040540740d8100b54800d400391 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 640212913 1250 640211663 640211681
    0xa0f0c02070e1e070e030102090d050a06140622090f0308041e15150e01060f1707050304030c0c050910080d030c09061119030809071410080a1d10 64
    0x5050b00040008207400781c8540113401c203920703140c40340340d00c0314240c006400ba0060303094403a030004e09420741b202005800030311401c40903c02c0b1002d0114450078400308604000890307034544c10107040c012508400011441e241c2a92118100008050250b6210b610100200c24803c9010813510b805210501c4101104800c011200031243d00d40e5002c3ca0340e032105440f11702c41c030365400c0e2600c6801c6009850300c40c2d5086000340541c0c100c000f02c01d69440d0001450644e00d280c018011030300c0584204000a03441c8038403480b070605030b11064034541343c90b40c0444010350482c070143ca1300610b0000100d40c541c0e41d24882c9010b144103040e1000580d0074044603500301200d1280100c1454608441303580e88ad5004030180c000c5801900f040c50081038000001400d011300411403100350407407003020100701070308032418074000c4281d04116407505403180309014101801c81e840d16401400059010591445422441d40c424078018002c600740200110000c0320b140d407450802c20540012401407041000341c8603e07026 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 640214163 1250 640212913 640212931
    0x20a08090c010f0e13050705040f0506090f19030f0803040303050a021204020603071809020415050c07120606080d0c0b0615030c0d060e010f0509070309020609090a0f0c02070e 77
    0x1da00300c0200081c0c0344241909410341481400440c10a00b44d0310141d8211117001940f40c140030b280f800c0303400185940e00c03038000c5a240d047e03242008103d0b8100311095034070401e0003400609280c51176078204859030038a0700c00c403001c009a500001c000100300341002e0900500c40c030009034a9007058900502603030802440320f0b4100e441806031024030b82c0f8000300580c001c0d4040e2511a80c9454400c1c0458051020311440b08840b07440c0240058240d1659005200701c9000b40c0210180b1703c4024400c442d18480c29002c240103a2100c141030080c02c0403000c801c0741551182000181490fa00e0600c41e0602e03c00040309008545c4801d4810184030700d0180781940088204c61100c0c026a042035074201d28040500b4283c0000c8020815510700002c03940280e014102400c01c501c007e6075104020410641c85004180c041e02d1580c000c1808140079025000c03e05500804d000d081209000510110990061003c0d0381e03152211038442001e41d0500c0b504200c3c0c05030394040c01c2c005041031410048614080c00d0056 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 640215413 1250 640214163 640214173
    0x1f050403050c0919090503090a030c050a06030c050f03060a05040e03030f10050303070b090703050a05031308060105060702130b061803010e0705090601081e0705030106170402060d110f0409020a0809 87
    0xd0b52410801308000f00003481d41c00042a80c2c1c281841407840c001c3c0980b0541000d0b410308040140210b90400d2801c44c0e01c01c45840c258030752955000c4040d116042001c030302290040c4484000a41d408001d0b540c002c0e806090001c2c440d580300b001078240c1d0020800345c841038000105000ca030750070500c10399600981c21280c0c41311052070f00010030390301d109980c0301500e211a54001b080c0700d90f8060005e0001103030000c0403192062074501f4415107960281c503441344030261509002460003000310740a412a40002c14050600401da000c1c05910745180a004011070341e91040360049584200103001c101c44550810915819200103040c21901401003000141d48811405c201d256a00044607034841030038070300383d1455195845860340300e41207408054000000e00c02003160582c4c0c4100a18100c4005540760100c1c00b05408010196807401d4802030340200f000c00c81c0d03207003a030015008034110400d07450401c1e00d40740d03260070148100e030000e4108131045500003a0301c48556500c042041d4000005102400d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 640216663 1250 640215413 640215421
    0x2d091c1d0316050d0303020c0609032104021c0201120e0105070e0d0f0609050703170721090501051c060b09030115060504051e0d03020a03081b181f050403050c09 71
    0x81c2ea50852481039a114070460440740e002c140c403e80503070b01c64080202c1210f1481c2050700001f83c59170068000781e0800e22540041e16001606024864011900a800030f41081745462108d607101d0600d00c001c1c0d0501000c1c0d00e000e07504a40311b1080405104070340000090a051040c1b0007405a005c40030454494003060401c0d0300401c0c0102000b80e000d551060001803000b500e460418104081c0d9030020b8607240c80c154a9000c00e9011500522000340304813107c001081407903410031800c5442c40c00810010380c00c10f00a002550242d00104003407000c07880b2403410f4501c0e030084001a034503a5040701003022000b103090890360400740244034401c40510b00150150b414a1001030140c004c40c41780602c00e01c0300c0c01a140e5000074200c100d681000d0064941c03558180c8a042c040d55584020400300c0c00501f00301d00003690b05180400950103107200c065880d15001c481c03960440c070b1351032040e00c096200c2c1d134408460754262804802c51004130100d443c0c43c1d03107491030350070220304200d100b884c614010180d160400c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 640217913 1250 640216663 640216693
    0xe0d08061c081204020d15150f030807120201061a0d0e010212220f0b0f060a05130905010b0a0f23060a11121605062d091c1d03 56
    0x70311018011988103e8165540780000303042c0754904c0303002070304040c03440c000320504580c01d40040300c0101c2c080da5000d801643e18548070007800d0143c40003800c405001d0040000140e40f084034916921020701c004035450382c65120002110840810004140c030300000d03889048191030140203e071a010714000c50500070350b03030707400c10102900030300d0060151000d0b0312040c0e012200c5170b44c40d90345980280349805580c1a0386458039104105035907810f8250340c0040010307100d01e04000c41000fa40d4000e03094101c4848000a20740281c50052400c4406540f52260204291038030306c05600100040300d580f002c1c1d64640790b2444440c01d5010840c1a52004243d0944ca80d61254000c440651415150401c0c0c0f08545d5480e9a061020705042040034220000300d0041c20f400003a141085107000340242c2d076040c0ca50b40398001200416240c0320755107203460006850203503011a0300c143d2142000d829511011840b000d00c1c5640300072540c03414080341550f1001c000c0412140803000720400f05400902c0f94960342084 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 640219163 1250 640217913 640217917
    0x2030f0c01020d050c0f010f09050c0d11150705060f06130c0801230d08090a08030405210a081c0506010807080a0203070908011503020301230a0903030e0d08061c08 72
    0x300e8040c03100001d214600b0170401c2118400d80d8111350003c00180012100000141c1414503003a5401c1c4558090b820143c40d003507580d59241da5009200c51306007005030051050f0041d25070001c04101e4414043c00c40442c2e010300c10300744242440f00e010b203038500c0e200c02040003c3d0941c42051080501d803108064909400022241c150781e10540d854400383c0340050859443d40002180603080300705802e04000704081c1c440074149010084900000e0140c44a07103450707480c0100d103c0d00d42e0080c0803140300000050981d0301007060700c00010644034412540e494400d05030f4001802c2c0c4000081c2c1c81d0032403040e401103200300d40d0800400d00e403850300b50400550040081501614540c3c1c00c17a400000700742c40c1809000360f0402045010001d01c4030400d8500740d8a20b00a50b440164040d50910802c8652030b041240d1084d040142c0c085101025283d8041c194001c000c004822401c0c55900c3c010350202c1c441c10408441d07901200e43c0e40c00418500b0030f080c8003549102d035070880c00c4c0d0380211588800103079654003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 640220413 1250 640219163 640219183
    0x806130602090d02041e0507030c12020708090a0e0105152106030f19170307090b030a0b04090f021f02071a07020a0602100b0d0b06013902030f0c0102 66
    0x100035864007140710000d4010f208981d0001d511500e4084c00e00403071002140c141c8000c03c1260303c108896950102c0a90a0f9800700841d04001201244c070700124580c680c0c050b14030507001d00d511034102050680852131844c180e41104102d0b4500000400862608400c03200420300040e000078200303220b01035101030000103031001e489503036010350004060f510b081040c50000408041190881c0444001c1d0b5040c03184440410f0b1410302104007030f118040485401c6038050213540d0b0303500720114503285815105800c040e00000b0a16210300740e410142d074550003120503886c001c034401044070b061031042000c26010411110816600c009400d2103483c4c0120b141e104490304070300c084004114245e6403050910800900952221410b1008035450f54002040042c205858804000112030f0b241040341d0054650401040341000c240098110f5104050114040c17800c0204d60129500f10380198021002c5440c0f11102183d00da0070030010f501d001c010108000c001c040c05800c0600c0d003000001d4944000304 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 640221663 1250 640220413 640220423
    0x80601051b01110a08090c0f1314150f0405010501120b0103060b0a050307020f060c04170c10050c070905060f090c0f04060906080c0c0d18030b041b080613 68
    0x3045441d00c1d04a02800341e04907041c0403008201d10044400c03103100719005a40120009902d91001900c8400c0004e05c40c00f460200504840100e031481d01008090078022000b440d00319112030880c0d44820000740098011001c0003844481012070740c0c1400011600d1100c668031850a21004100d00d07600401c070b040c1c648282c07001c08185548030a0058020b0700196004940c14840010803004641c4e005005d140200d40c25400e171100707a00d002c071486540720016035101010100c01c002c1008000d12402d10102d48d28103840c151035007403c1107800195a02840041c0d41e004c070b10005001884168144603890113049000c00800250520704049424080e069090b0b80c0a8150034010601c0389000001b43c540e01040310481c0343e5119103c0400030000f00d010321410340403900a9011504103109030040c0d4043c1001c50004014801a080c030072103c1d1220781c4010202038040180200c04908640036451040d0b008140d103458040d80b000725039112150542c8181c2d6203410180600204038900141000515001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 640222913 1250 640221663 640221667
    0x33909040c181e12150b0621180a0c081e070e04030504050901120b0109090b070e150f03060901090b06030c092b05010e2e0e030c030d0c0f08060105 65
    0x1041c61102c0d0f0103640c1214000304100b04443d0200302d641c01c00b0301680000c5044c244851208403061040034010075890703001d2422101c1c4131240c900c10000b01c1a40c0703e09040301c86d08802200004003030a01441e40700030b840c0c07010720410030302a04108001d40f400c508070582d08100c80c03042c0c4c01c01729038890300540150105050300301c001c81d0034184610243e8011700002000000e4550359804144100b20300c0d07220440b950b189400000400f0b040ca0b2155140c20380c0c000004018694641c88115004807070032140c01d1b40300c030059422000440c56a800380122040701c0c1c1c0f40b00e640382031603410082e10b44416409507030300b14104130081129403a0b1800b0740c1d40003810024810b17118104100010240c460b00d80b401c038100d040d0000c2e00c8001c88030307000c0e601243c2c9000b20020403400c40041e07000c5485003518801a1800075004400c00740402c1040511405a0224000040c95007403403000d540c20350b40900b140550f1541301049000d0b0045130391182d03402044250074a12034859015001404036140102294180440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 640224163 1250 640222913 640222949
    0x120a1a01080d05030c04052d060310150909050c09090108070305120c100f05151915020109020306090a03140a080a05041104090606090b03030f033909040c18 69
    0xd1001a03c0140000509010888d05c0c0c1c00c0c08030140403204c10102c620009030514000450030320404982c0100c80544502d0740c047e0400341500458180241d0036020001c11130310009002141c0e103d00e80c01120641c1c0b1035030795106100c0c100141100c042e00803d600f44c220440c108000b0701c00007401a092504030540c2a2520f039000082410321000d251202c05003820000b00c07076540d044560219100f0307500e141464101848803028400345640d0007004010014080205111201c400102e4818000305840045159250741d40840d04145092710302a000342e01103981c01d01007540001680700e0f030040700a08242445181c0c180240760000141c03154211558580202e000d100d100c2c403084800040180c018050300c0311516001c0c0003440c0521600c0050341c94451100b00c01d241c04012100710400e05000941140c4800d080b1400b4603589442030320300c0042500c40b010070111904c08040e2462a08000640c8a01c1c901c818042682c408480340001c0019480182d000382208155000540740340f00c0c4101603c4030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 640225413 1250 640224163 640224181
    0xe0c03030414040b18010602030a1b03121a040213050a050303030c0a0c0f050a1109060d050a1205070b0709030b0c032206061d010f090905070b0c01020405120a1a01080d0503 76
    0x1c4001d46071701c02042ca0010a503d60004002c28144409944911310314244e488450344680b1100740c0240050503400c1e0061614a140d0049140341003551800340f50301c2460300004080f03074454000050741c1c0f400000100018034021003208002d000540207580b8502c0c1695400c1c4083c4100d46032981840f01c0405a482400030007512000b401c0e5102003190111281410030310941d80c40318000c144540345100005001d81881f15032000340da6408801055913105698480c604a000c01340003800f040750500003100803a40012010340105c100d0703181d1280c414194140b807c206100106107000c0e4400401c18008083c1808900324440520a80f801529008900e00b904c05820150310070100b0003a40110440d24510a03030f08281200c84805040101c0d99958030700509440c14020041d2040e04070034010003800d020b42009003004580ca00005241076101c1c4001030000141100b1103009038402805002000031141d048207691164003d1503a0741c0d8500720000d035aa44404000408100001c00480c800310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 640226663 1250 640225413 640225429
    0x130609030224090f070f03060b06210106080109090803010303110f01050a0b0f030f0303180f0304090f0b0d05070902070c0302030105040305270a1202030f0601090e0c03030414040b 79
    0x1c100b0120000740310141403100090010541d030a0304a0b02481d00400101d00d4006245402c41d1120402c040c0c0103850354075020010118603901c41d0704040c0803c0325403200007989101c010721911001d401515541042401443d0020581003050f150b860700940d140890350510540741141d03894940400002d46543e002c509041d1101896502036003000241b218268098100b0325500070140d91101070f0042d88801c065499000344c03182140f54004002040305500f04106107803148000c2d000b00c9440040c00c85149295a110364051b100d40c03039440d43c80640041084c041d0f00480030084841c500700b181c090319807944410852149601d00c42d4000b4031341003040b00c07440d0b05100454005000300b04916080c1405002c5610030181102c0c50500e9003901004880320350151241c45070701030401528107090202c00300100c44000c106a0303252160310403001600d14204010750203040c500b900852201c01c1041843e182580c078402813071181d0070500c41400105600c640c06a405030b811980400c1c000348810128140b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 640227913 1250 640226663 640226683
    0x6030402030c04050a0209030f0c1023030403020106060e0414010e060a0503010213030501051f03030c02130e01090c050109180f0e060a0203040b0609010510030c090b0c0a0b0901051306090302 84
    0x15013058100f01d40101c2d1907002e480003890039016134441c114900c800e42e86400c03024400750341c0078551107180c4540502c1041c2e20a401d5084000d04a241c0d4040d03000d007611354000319070850060391204018085158002c03030316088030400351010302c0039020b19420343c000101c050244030480454540007c1d050366403886610010900600215501c2e00046015040c814441c0403c2c0c0d540d40c02d1034007003003450550446404030340035140c12488940d030456400f210081000360341030380c3c00910212443d446084c5442401071824401c1e00000d4941614036010040f8401c640c8007a050000f420b0040140012030745040307140e140c00890005090031800a110010029507802484600c5580200203461805078010350156005032003008265840d4420014511002d000d5a03401c085007040110351a8083c2d0448001d0003010305088101d44c3e10303101c070341c00e403a040341001c040b06a000004001c00d0020300c0014641050060009003d50710789002d046c4414120010000d10703456480d000e4005041c070170b00c04485d01c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 640229163 1250 640227913 640227919
    0x506162d090504140f060f06030c09130507020a0c0806150d0825060b100e010309030c0203190605090105060a06050d02070b0705030f0604050708060d05070e0403020a0b070c050c06030402030c 84
    0x110121132000d00b480c01908030740320031071240004082005440c002090b80101d0070014195031460f41c0b00400c2c10681c0e000140c0c0d5035004103112411748590307501400741d141704158981c002c003400c0c2d8147c1400f0a946d1401ea1210009400c40400e0248845480c460a085c1940c1501c02d540c8100c980c0c40e149a140c81960f0304a8421072818121a0405148030919514a4061982400180078450070000c001b0280070710701e00402d01e8086a4070301075000e50410408107000341062003902c005130700468142201460f1000b120401e484810381088410700c2055002a001030003004245840ea001c540302082c14020f880a03c14041215400440a50125207a40d0390000742000340d0308086501400603002a640300f00014441d5000801d00c7c1414440d1034800c03180b5603500310b40c68a07810144003c00203690402d4844c1e000d81c02c408585540310052190269210b40e0003005400780606107500201806041c450800c60024079100114070001101190303501c044030740326503a866501c0040e2034000c0d45148650 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 640230413 1250 640229163 640229171
    0x1e0207090f0e100c0516030c020a09060515090d0206400b0c0d0315080714030d09030507030201030225060b0301050c04030803010b070201050c0a0506162d090504 71
    0x4030160940d000480281c480108850001c0e00003c400f9064800f081e070f80b8000120140210134905200541110f9694003e04081a50040c990045600c804c1550000408075407104020080341c10b1080c090100182100e40182c104060700c40000c50310349400c04040e10600c800310780300300d100d05850340c000340083c203200c800c400702900c1e80c58161301c40300d01010000c01460070190000d401c09600040b10705507601c41010307011254217907806034000d0260b4415a10048440000818440d00412040000e0540300c800040c007003c10300101440e110300711074104100135503203208100007040044c100c400e40c0e9090a025071642840d03048080c1004000200001c052100113501051040607403114200078002c0c0c1c001c1c091641c856021501d40d2040e4880106aa103003000104021b209040241c03a10300c0c070514080d0300d00644074900c41c0c0f5040071004191544d030004000e20114442031030051015007410708068840b02000380343c0c02032108010003400b031040c0d5001d030460002441032104901071300c4004c000704 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 640231663 1250 640230413 640230431
    0x16050403021311220302030d0815040c021c0c0606170706050c010b090103120212090a0504020c07080d090f05011d010c03032d050108210c10020d020901030b0d031e020709 75
    0x81d5044d0501d01c410380c041d004404840c00a28407550b120342c4600a9a1040c01d48240b04200b0f10005003203034000b2101714001c01e02c41c80e081844a41020303113840550380d2100b0101102c0d00306501150030661090945140d21000c0d00c01440c008180c46081381c260303080c501d8036103400541d0035015000914a69a008401d84008002c1142ca0246100f24254541c01c03038006480140c1000084c0c4503140c0d030284c4c4031003000020001484e054004100c2d0b03235107000540c0c01499481191030f251103c00c100342e03070100341000002c0c0b009030503400c2880300038902441e1000801070b00721020074810303040312001e6040045142c10002454001e401461055002140c24010b0005603903014411100b247d8800014600300000001d4400c4001030481600d80c2c075042125454036040c0f034040e034a6118100001d42c50154807210600540c1c1d0748041c2c41da0308131225026030758100d0040010101c440c1c07126068400c00c0301c113035120f02080c1d0112010100d80e458a11014101e82c20a0f800e80c901901c0d030340401c0b03100c3e042c240c00c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 640232913 1250 640231663 640231717
    0x418140708041b15170f1317040602010207031805090402041d060103110a081606050a110d02070612050403120c0201020d0f0b040b0a0b0f0a09051816050403021311 72
    0x480c2c2c4e14140c0e90740d03c04900700352002d80446084140c4681440b0903051010644c01c80e0002c1211550030302c107005030704245032a0007510500e500035510010150350f020400f00141900500d035103100700304920590403001d05040c00901484c034003410181c0030f19030791600b00d24610740c0c451458000c003c1180480da17581d079503883c144005900304040301d030003840500c4001a10003400603c003800f00c04000c40e1030340c0c001e09040048589400c61a0345100b0084441d4451021010910107104003c040c1d81c050480541000f00260084044881e1140510303e030404000c0441d9000004105103021b02d82d001c1440d40c002030003203000e801800515101c0c1ea141c0302140c1848403541c0e01003e5140c030240c9045c442c000e091410080203070440d1084841c84801000000c0340d0b03603420002403218803031605110142903114404220003643d4100c8412071860030f00306114101d040c1d120400101e000310b140c03003490035003154042254581020080500d0740d455540840c00c01092009868501d844d500c900740b601840020350b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 640234163 1250 640232913 640232939
    0x1e021305040b04060605030a020a05130b030105010915021c120f0e0f0d080a090f0b0c03070201050c130603020c030d0e0610090b0904022707050418140708041b 70
    0x12a8030582c6840c402c07002500b000e00460041314000d0701c815003190b948500c000c010b5802082c08808101d02001300c000c00302403618503500034000c804580d544070740c1800005401007a4541241e4004a80440300a0310142e0000c0c4400300f5441d003403140040c070121510240d4401d200e65030080d00359820201500e098210035841800da090440e4102c6000010031445552140d01d24121600050030900000d072007041f10340c00c0340d1800d501c20003a2540801450316403c841132410b48100d81c9070b100000500409990900030307150424040a5100d2400c801c00d85541d07050003c51107140189034005c5103076404201c00b030040c1c6501388403050782806071110209045481e80c8003124550007940004201058007a41d43c407418203c0e5002425510942d102d036002c0160451101d03a004202000e04e440c411701108080c41d905d4015001c546890f0f8686040040e0b44048400341550700113014a0a101001600d4103000c4a5400150b603082540058403103007096044a40c96810940012100340d05c0010b51401040b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 640235413 1250 640234163 640234169
    0x1140c07060614060301171906050a150f050d0c0b1603080c030f04080304060e1506010e09040f06020306010207080a0b070314040f02040b041416090501021c031e0213 73
    0x420040d9121080f0301d5098541c0368a02d03410400034001408500c0c07035020700c100c2d03100507001200d041c8425519614040c00c41e2541c01c4071003d4850090283c01c1100b4024110360303106900f40c101005003030420610340f01040d031048921440401000c4001d000c208078041000d0b2440318151a592041c205040700d882c1d00792801140010b100303000088820400030156030261060f099090a1078513140c95401e0550030241090f00d600769a0180e510380c1c46000c0110641c2d080034a038104825140181c0003611844050000c0d9004022000030400004c00c441014038606600c01c02c016140d0302c0c0d01c0700403490003003940c00800700b91080c1444081444034085544c6c2c817405043c2e50501140c0000302e4010301055099074020100c48555841800500e01500181c95504c400f41c0001a408072a038409071003075030140d40ea1040070120b000c0190300c056110802d0380c007038070782170004040220311000201e515890900851040658501c8070381000902d030a8101c91844075828250f40301c1d080c00a59410f0004984 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 640236663 1250 640235413 640235423
    0x308130b09061605040f060c030302041d010510110a02060a1e0c050d030e1c230c010c080f1f030c06051308070503030f031f030b070f020c0a150201140c07 68
    0x1400f00b444003031090781200c0603a07041001c99460207140c4002030310203100c0180c086051640078070010070300214501300b140c80c03448411401181945400300b400152a8540c0b40c1a041021130080d140c44041d0020f0ba07078200c0359054800c40d540341d000110460b04410715083c5814401842c1824010482e8468052099180207005480795880c0b01c0c0400e0b8100e0702458040c500540140503191a02d40415502442000150a0041c201c05280d51010304211014068207000c4101180c80c1140c90307400d201c0c1100a109a040560703050038907038001560600014038560744c00024203155540c46403d407010340c008643c41011480001d071a54030185c8942c0048011450421103000c000802c288006550300846002401552034541d100c141080780f9030000300015601d100a1040e05e444907510040e032230096010703c103000098181888000c25030350b04103519500715404500301851a40d0b07080004000c130b0343c8400356051440407000069000d003007286043c0d0b0b0903400f0305c003c02c11024002c50080c1a1113201e2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 640237913 1250 640236663 640236691
    0x52206121101020d090504201b0601091427010f14090d0909020903032505161a03250206150a0b030615040306050a0b09060904030206040308130b0906 66
    0x4980c3d078075400d001d44c0700003040b041c003c22040c1019071111280100607440088880c0311204080721070f910200c00c2c64460340610722a080030030310034440e04c0e014000402d41030008407103820403001218405011030022100951407d003400000301501c5039030742c840c440248110002e45400b10010038101c2c0402c054401340c40002290403501103456440c404030381d100c0d0142e176400c001c0140c000b504090706003505480204a10180104100c3c0c0c1141d0787c1c0d18081c1d07480500c09440c900301e810190070004264400d1502d00c000d03c06250304840307801400d52449402c5444c2e65800c0403a0312590b046004080100d0840f90300c5110071503001c03841c01d1041180061914440e8034100c00c0c032088040130b00c1180c00c540d005001062861511001c022070307a0b0403480c1032a0078561643c50b030304220b0b202aa802c004050b40d0300492512410078540c0030303070b1045080300c0b1400c2625064a003c1e49400009100900708001580001c40d0000d41c000040c0d201504810215901d01d070460701c0656403002a6042d0403400c0b00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 640239163 1250 640237913 640237943
    0x106030c09060918080d0608120a27090504020a0b0c0a02090915010905040215040906180612030f050c0a031101050c0a09061b061e0b0402031005220612 67
    0x303d80079800b410041c01044403800035594588401540160714032900301622810f0010f03c01b041002603140f10040301d00280d81c0c40712400c0c00501101001d5500e07075501d15414901c1940031861a410b03c045841201c0c011840755541d00c0024090315050b0000c4170070389004500c20740c0c0640300048800440f4030a440b000501d03120000010307036134a80a00381d414214044001030003090195049950031520160480100314032424407284250841c0e080690110344c1c4413401c1107003055080c2801400042c0000c208602403c1c207845200e100800031014003400800b0110b210032500c078808492071210803200f82c481400e0940380003045030440d01d40c40d020b1982490042103562503e041101c0382e00059849400c122481c01009607030640504400e440c3c1400000c4207000882c400c0d00540b54005040b90118201406012061007141d003440242405070f80f051080018060f661a07070380342900d000300c4401d0340e00200c8107a0f03a81034040d000e490701041802e101c1e0000c3c1c440b070104001800684103c0019042d850 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 640240413 1250 640239163 640239179
    0x180a2a020a140c0f0607050c041d06070e1e03120a05130911041517130210020d210209060a080402180702060c0f0d090302100c0509030a02060901020a050106030c0906 73
    0x81c0648003c1d806202d20105a440f0f240c9580101206d52003802601c40c02054040003600315503d10801d07180ca00c2e169495684c0e02e0a05101065004c911b80c20046400510b8401251a0b40303641d84455266182220101d00c203580d0402980c4034001000c504140c0c0c03510003820041003600003440800162444000115140c030300750095910341c240e500c4032141040c1c0741ca40c100300c14080641c1190284581495110341c15520b03001014866003c500c00118044400d01c18004e10141910601c002c6400001c441c82115600c1a410094010040001d03480c85140c0e000c900f00922540d5075035075000300001a44002290008100344c480c0b4021202c078000c0e800c0c40305400c1e644620071540440180c102d0b90004200c0d699140103031400c40480240307581450308c01603000080718400d060a401507480125030003800403007401130003c018007900d04142030040d1403020030750310040032000a00c07401c008941c22446034400c10188208a401000a0062540c3d9080039a1041c00c1e500a4807002c41c00d005004c14104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 640241663 1250 640240413 640240423
    0x16020307240932010b030c0402031b040905010f0501050c0709050712060905070905030a03080606070c08030d05192003040203031207050712080c0a0804050102090d05060f06180a2a020a14 82
    0x300018029000304018801008020b51000340303504850900d000700e00b1241d012f0300700504060704002d40c1c0010b9550405400d11070399000c41d44100d0400000b042940c1c080440419020101c400814011802d034442d020240c42c03401203003803030188443c0750220018000300c0b15040702e0b01485040d107401c030802e40ca0b18280b5884608040d00500491f280801148490400600400e1282d0181c0440c58038207490f000d00750b095500010b07424001c00c0d1503500744400b0902844840d09407030548071040000036905e10042e00d0308101000005403503980800080e0a40d1000d000712070901500020540242c680980c020380300c0d41003000c1c252131518840360900c03089805402d0480c01040c03030031900c90401c8031410040329074030030003042219255020306c590342035502d50f016100c05033740c4180d010700154030f0401a00130305208001c01c140d100b00004440c1187d41c0640d8910f10b40c109030121008941121101c002400300c031000000b141d2090031071901105d180ba808110768003d54420764145200b9422484156510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 640242913 1250 640241663 640241681
    0x30b1509150301020f0715050a02180409080903030a0914010906080f1503060a060306050906011a0310052116051c0507080d081602030724093201 64
    0x1049103400460404007030380c5a03030421031000800151400345020342c0b00c45142c1104100300e8030080443d894176a1710388540034403035004800400443c14000c0035090813402200c0c04101c1401240d0342e9020006105503101251810703c00038040701d94807408103800400b5100790f0706c9665015003100041300800d42c819100700d8201d44e125680c408040e2101d400301c80e481c4101030001c1d6804c040140d011886501c0a1202070304c5541100340014980b403842c202827050b030300014140c4500750090001409480e4030b00d80300800c071400c00500380b074883da07a01500c02c29039425508041c0d80035400d01c40d43d00200c3d0b210038080760403412540035074081c155412080c41908006014043d40500422034941c40703d01c8480d2001940c0b8020f104072041c190b602c500d1141041422a101c00001381500104104518401411030060100744011032a141550325441101081c1e08000e400034201c0a0310001c2d112a940c0001c44c0042e0424041a4807071806035090742c007064011000000c40301160441410707141d041c8030710b2900d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 640244163 1250 640242913 640242919
    0x2180a0b03010e13050a020f0319031805030703120e010c1b090b01081e06010203041805010503120a0203041412010c110c01090f0e270a05010f020f1204030306080313030b15 76
    0x921040d1f0030021130807404081507130035100d020a8448c0c40307030b9011300d03400c03000c1c1c00780e01c910b041c0105040303070342c1602d10240d00000d010340d002c800100000b80143d24540601352051820702c220110072030040300c40000c3c000001d04003a00b0340101c40020726a06000c10111196003404000682c07041c401525040750445080c40c1c5219000d500180e140c0b003a078412584480c051056900e0207403114400003240501c1701e5a0100700344c0d01c000601490804000d0103441000c003040d84c5040010f8010000e503644103600a00411010f091080502c903241e10986d4412000500028000b100b1120002010640000c00700c13a000c0c801c1460b5504c103540100d07102004d03070311084d20b040c1d203540c20200c0920540740d01078000c1140c90140c001e05404088960002c1035001811400ba0030005000e04109003514103c07150f000c41c2610402c0255031501c0101c00315401048a0311000c0555920b40c14140c00408a95002100d54040007520f10041900305d40c40314281c07403080031000c07019181d0b42c0c02040800105d80000750 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 640245413 1250 640244163 640244173
    0x80c0307140706230a08060f0414160206190207020307091404200a061b05010e0d27090e010905011802131a010507050f0706080406051f05010302180a0b03010e1305 72
    0x50340c1b44112250b80d0b02c1003024204000c58502907000c035044610426111507000903807400c0c000d032940a029000c501015600c02400c50b82441c00c00d5054108408000300960307070b40000c2d00411074800340041d07002005418420031a241c40340d515450702560488003181d542260b10704451002d00010b2402d440f040e00585292a21802c21105075480c404410311032500b04081420782001907000d0140b04040391562001e0120350448000180400400040415401c4c40d0a4070300406d400080b01014110303400090b01280d540881c034520b80c018250320b0710181895007403040d144440d131003803141044441e02c00d44208800c48581c00d000b0088403800c0d0390048942e414100c0342491036210708040c00d4030394041c0069441c01d80d02403c6140c0790440940c06840882d103c9da041005000080c811558006054201411404034044a04200c0f1815009850502d17601281e401752142c2e5501d02141c3c4030002a240c100d980b80c035400c0001050300709210703952514030305c400041c40c2ca4003c500c401203130075403243c0140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 640246663 1250 640245413 640245427
    0xe03010c0905100c0206040b190305160e0d0624050603010503120705100f09030909050720010e1603021017060904080d1515050c0a080c030714070623 66
    0x4520314031843c554008000495a4030000759036000000c0001b010905d1049954081001c503600301e1410482a44c0f003030501e40300c100b11500c10818108244000799241c2011500c0d0b10000040120300315010140c100c82c909100620380190811548806182074041c0e0f101c0303181e449040103002d21003401101e80680200250440100c0c5050140039450321600681c1c00d03184007040503e00722130000c02119070181e12944c005080c19040300cac05002078a00100e091001d49044d22000e80100c5455100505000350520f203101510341c207501000c5041d0514080c2c65040c2d01ea1200c920b8410340d0f50109170303c5000412801150706008134020801c0d6007034402e00b900300b0b9455008203c420540244141d0343d500081160b0200d110441c81103021a8905c80c0003811140c3c14500103401185003c2e5421061040400c040c013a403100c001004265141c0c01725a0760f07a15a100200c0900750b0184200040201720001604214041c003c21440169282503031862086160038480f4010741c03d4200e01c0c102103410800ca08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 640247913 1250 640246663 640246669
    0x203041202030109020d08070606150e0f12011401030b18100b060409020a050706060b1e07020a0b04030b1603200703030b060c030903010516020312100b030709060e03010c0905 77
    0x4035158001400007848010b03a8000c1400c0781e0b5621400c844c903402c0000e0030740c10441d080c854903001e031421042d034010400403a00090000c064050445125208821107502c5541e201e6611105a8220f030000307205070a41c3d18844032506ca020300085030842189000a629102c1c40c4040100a66160f0010320700c508504d44001c0042c92003050044d08542e04202c00b08170910799000400005441b03980781c503940c0b00d0305e0400300211207440d006070410940030061800380135803158503003c003041000f14203540c420540c4006600c5446a60019680310360200d00001070001c1807241c0391140c010302e1114190745512803801c408480c9c01189620303802d82d08510300e00d600c02980d00030704100742c400d040000d078030350422000500369000400200c2c610b130b000055650345820280205500309584800041c100209000083c5d2640205a0751400081548000880407e100020003008000003043d03103503a414900e030014088000d6019510102c5c3c003226000d0954101441000c9a416179559110003137800c180070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 640249163 1250 640247913 640247939
    0x225030b04171305010e0d05060a0b04060909060e07060306050310050c09040f1d06010e01030204411f0608060303040306060b190c0b3c04021201020a020304 69
    0x82076075020000c00900c030b03203058180001c1402020f40310400c203000c3d19040c0014500321248903214010a03800c0c000c000000e00014101e07400c8901480c011512604032000b11700100b0103580f100d044c1c1d90031700b0341075000d0080e00d62090301c42700b44042c180d84a0585a820a4080d10042d110741a0180e000e01014031078140203520045d04040080515480d2500c0740f00041c06983c2c070b600c4c0101580b903641e01d820382c1e02d01e94501541d00c40c819000103818103615100c024021440140b002a001d40d440d005851404000d01d440043d80803007004072000ca85045941c2850341802d00702240605144c1c05001c51040003402c40400303021481000e4680310380d802d02e01c00700c40c100d4001c0c104a80621042c8004800189540903010150440c200712580b0b80c00032503151900680c1c80a0300c132051008058801020031040100e482d071007040e42429484503504200d64001f916002d40d4140044505280d091072106511403169001d1b6002310351621128100b00c1c0070500300d200d403030403141c00b50307200300000c001031000200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 640250413 1250 640249163 640249171
    0x81504030519080603100c090b070c0f060e03060f0f06040c0908070b031611030a0323090105070807020313030204090215070c0e010605070b0a1805010c020d0225030b 73
    0x180c0103042c0100d9001440318001480480030200707000780704002c6079060411080808084c043d0741480803412500015085000c4d41c042d00385034400001c1d441080c010040400c400030040b40980011095460000502e181520a05248240103110203d000e202d241070f604c602a001a141c5800140c503142d003000000d202c034007040014032015107400608030702c0070300000d0300602090200079a00d2400204008005002c8540ca20071b1240a81c0c503e00512030000982d500e9160a050004200340c1c0410105a070004144c010b05000c00c44e141045110070040d0040ca000341c40645950400e51160003050344c5a00560400442e040b22080007040540b03881c0d001409040c0c00900748047e50510805401e603a603001c44010740d5910b00d00902007080000292580c0e00400c10361514508208060352551308001004e8102002c4c203880ea0307007100d0b582c45141440c2c0320381d44d402002088608003160300a506c44500035404000b60007040c0e80d400c1c3c06442c80081441c81e0400d8081840c10505590f507411014034003070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 640251663 1250 640250413 640250417
    0x50406140918060712050a0903140d150303090303030b01090b03150a15090609140a031103011e150603021806030705070606030b100605130e2d06040e0708150403 71
    0x382c8106034820034840710b80070307007400c0d40e42c001030381260b1200c0300c1a500003600741c000c1d8038505840c103004298401d2108001c0100c000d60b030b9694074412040342c0042c00540084101084152034000105a0040940d404591194500340903c408170401941c080c0518400e4200900c0e04100089140f9a81401140310303030001003441c0c1c9019222800c0540c115100d0403910f0108451307003410300020780c12180b00340042c6074401e00c000d4200d10801c04140101c0c0d141c4030050410f030f43c0c001c2c1d108055600f9000200104583c10307c190000f8440d400c500c1c06841100022000e04042e040c004c690180b1a0080300c48100c07a001c07141200781440410301c181c90303100800c400200007007441502c0000301e49000f01c0700154043c44a881d05401c00b40400070120b02158408410b0003000c10480a0380040090034508880c42c21420607080c0d0380d106000e04c1c025a454a5000060790030000d219080c1001d042283c0c01500192002c01010001c4058103540c0c81742402810706075403200d41c99400405a821010307601c070f4464 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 640252913 1250 640251663 640251691
    0x204030f081b0601120f0201110a05010507030c11420f0606071e02120124120f11010c06060312020606041802240c03130504061409 58
    0x261a04810000c002008441c85100020480358078103848010750306025803400503040c1d030351400c40d07600c4010320300100007002071108090700025603008500d0582c880d90a2010350301c42140d075141c0580204421924100468070b460400c114840c4501145031052020300010311030591001030b20800c1d192407903503550020a0b1000c1d0001c0e80d204070441c15411000f017609840150400300c0300c4c481c40010040016004020a00006000c644039121615410b1030710100c4207000c0c10309001280316500120402000e07503080000c496003803002c2030804051910100c1e080a402902c0e0144c10860302588200038026208020100b004940140f5130000c250b83c050502000c090b90310340e00d401c1514802da00954003913086c0040800301ca601400019071100c01200c0403c071144442150039005404000041d021300c003080b0030400f0301c02004654042c215a00c8032030310b44403107280040aa9a610490141c4000640100c1c00a02800d1a019001c2607468041d010017400c141e08041c00714401e402040300e110134240d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 640254163 1250 640252913 640252919
    0x180706090f060c05101e050105040504080d0f0b04020a020a030201231603061d0a0c090e0a090206090603011413060e010510020102070b071d0a120210120e03071203020910120204 78
    0x21442444111b000041d030070031800e11180e41a900b03c0720141c0c001802035040008120000e200c600440c1c03034641005200164103a50000500000c00c000241d594005d440000d80d00fa10607000a04203099038802d83c001d001d08400180e898001102990342d00c0c000d01c90f1200804c80c084411005220410814540090202d42d81da2042d080ea090b07406214110420a40a0110300304190003515502d002ca4107180364603070700c0c04c058103408110040180100d0303030b6503086030b00c115074403582107072244040100304903101d5071034104602204002941d40c4c1d2180c1e4890842c1483e1001d40e005020488421107586c8405038607000c24044540c1d0f00b00d850504655003003010300001170300710804a004181d1a40c0b15884216400003888900700b0856270740c2d110314440368080240c0d50032010448010b5030f0640780c56518908071001510510b40c0340d07400e4030030a4101341800b40810800806031600342d000e100c0018620300d8800307065040f03200342c1e108642c00203002da01d0001c241e400765002c404101e507001001841c00d99 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 640255413 1250 640254163 640254193
    0x6070306090f1407050c1906060303090506180f0a03020a0b030106020c030f0a0609020a121a011e0306110c0609030316090302030604110111030c060901110c0601030311030f03180706090f060c05 85
    0x104071f500440d030450b9502801d005042c0d003c0c0030034024100a680840ca012100340300f04007a462001c050340c0c803030b59184034480d40c180c0b11410140011640a848100699191100300085030800d0151000511641d20415041e1a00242030540007012102906030402107031108800f410801070140c1e080b110b084400202d501829240c204402d000b004020044803400981c0c100880042c2c1c04100241c00140503000451121070050040740d5024200040c00c64400850741c0c024002c1441c41500c2d4002d00003000040e1201200540c0b08544110856000706008030b003d03105a4480e000c080d4244d032003000041c000503001299180307413000504001442440c0c4181880c0b9561020340030424541001040c030180000901402c2c04002282944504051034221a15562001448080d003000712030045070702e030341400748100c0d500f000d14801740c95917924001121403800003030001080311500c00e040000800034450001203096500000c40024654a070040449186040c1c050690b141d0107481551860a8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 640256663 1250 640255413 640255453
    0x3071e0305090621070509030d08090c060708041503110708030403111c09050909062a0f07020909011a0105301006050405030c2106070306090f1407050c 67
    0x10542d80c0150544c02140403c00c2e00404020b0b0a900074081c040c410321440d55000701d0150343d030300b4840c07610800d155281010707141381c01c42c08280b494010000003424418410208010300c2035a90009000d03482c090849822411104000e401001c0c41031706001c0751001840680066400602030706d40030100c59032801c1146d00700100341a0510b18451042400d103406a004061038006100454083c112444c02e0701034541c48400003400002180203182c402a0500d404561a2040c1c010940300340b078036024028a609003a5100190691080a40c0000201c088030140501546001c5c141610403032804010010344054001c0e00030318860a0300041d40082c1200c46680410f41c0340e01415001d080384c18550112002d0b0100b0b5008102001008c200c10320150303e0004001e400364005640c041c200d100b284a61a0142080c0340c00841e540c00380509100c28654103030032000030313103180b803c00b00451000040c1c2d000c1111071495483c0300341d603005030004007454040c4c40980a040e0b117860603100401030160036a03040c2c0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 640257913 1250 640256663 640256677
    0x11d0112150503010f0203040c0509130b040501020a14180915121e0a03230408011e0e0c0906091b0706090b100506091306050a1805070203071e03050906 67
    0x8081c1a40c41002540b03003d0183c124001c10f40d18086145041640303681e0b440c48000d00803030380143c0640f40032607226850014490402c41c1c00249041042c142480d019010b50f000c1ca00c101c00040d050240540d050040d04100c40e000300c0e0140210f03c51007890300901c002402d00400e00742d44840384811207134043d194142d410952030000c1024107001019806404402d000c03c9440d4030302ea9000703009100c0081d801c10910200c1d0102c903480c040704040540e100720828402c0d5080a146542401160000f4004810340c5910780301d40d90340103102c4a061036400320394603020705842987c85a01030340410081e0400d2440aa0030229400819001c40d180000d0102e03e036100503c01c076005581c1e07950300000d12201f04854de800101030304112081074a00030004120b8043c4101203881000c0319040c0c615500c1c000c2d4484001032001900b11030b00302c0e50b14000c0705150b0ac01a00b0041a1504010001d401103101200300c0d0701c0726070321074441c05103248164000d21848003c1e070812018414100701c64034048e51100c01074561 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 640259163 1250 640257913 640257941
    0xe0f010506151e0309100f0b012007060c05070e070206071701030206040302061810051b0c030607350103020f030d02030f0a170c04080615011d0112 65
    0x349040003018814400c0900240d03050114041c07007000103400c00001541c030310341079141050f41c0741d441e80714003a4200244200340c001000e1516542022480d1580c0104602c407100b601c4441d0304035a200c40d9156014118101018282c1010b10117029090098400180d564050000c8881c0e0b00d44440c0701b0300b400c04007a103408001d64452820031000f1913201405020044801d000441d40e9490359011030010302403400f00900c1030302d011403150b030416080a00740320100c50003081024121004180602254000300e81030143c00364448044564500c0000c0c003d0410001900406503651282021250a80c201c02c0800c1a0f0641e10020244070044601d6420062804d2402514652461040000180d070b4410014008d07000a800031000c25008000e0b1204c0340c01c0c2154450350f83e02e1402d402c55411400d084029111000c14082c844034207c014040c03c207640800d0120743d1113488145a40240380b01400e4114006903458428043d4103102152882100c90103042005100700803e5500f0143d8100351501c400b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 640260413 1250 640259163 640259171
    0x605030108160305030a120915020d1a030a081c05010b0a110f0a14030f041202091b1911010207030309110402041a0a02071e060215070816030e0f01 65
    0x7240341000d114041e01182c075490a100e0b114916500c05440b40030392400c6070b0a01c85a91f40443c0301120b150407a0740c0c400e90045070a41880d21044e8a0002500a2002201c100e454880300da410501a08508820000b000b030051015188503651600c8075480040c28040113038082040780b03250245030051502812268a88580340c015a0400070115140b0051410151784900c03c15441403101150384440c10790006010b40203a5008100706186200d001d0401c040702e031f00000c0c005092a001aa41c2e402c0c944210f03220415503c504803850710191106044020060081244ca602c40c00d1183c4080151072282c1880c450b0280260090703422038029000039400300340c0b45d03080481044200707a50480010800c850031070a040c1400e070030380502000c4d0490481101800102c0d1416113000300300c0704c0010030010050a41d240212060605503402900c2088013501c0340c0c4044411550304503100710320518043d5540c08040c2d640c080c141401200017200384c02419a60003001820745400d204444003041190000302e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 640261663 1250 640260413 640260419
    0xd0b070905090705070305120403030b0307140a080a0507060815041d060a060b1804090525050102010c14070c171f020301050609011d0d060f2405010c1a0106050301 72
    0x301c1d030b400d002000e010410600f0800d2400185c4c225054548515002c40c080c5040e035143d02d0154001c201c0f0002d416803601c82c24070001003040d1000c108481031501610617160880e81c80110030b644401c40e41000340250005034080c01850b1040112546c03180a01c4064109040b111000c54102c61022000308605080300d116501c5400040110750b810011150303040086a190090fa04103a0041440910f440e900300103510a00d581c0e06c0c1c203c5d0b80e001782c0150980c0c401203880710106d803500030520300c2e841d20301800042c00141d9600610030300c407400c00680c4881070101a040b110740c200c0e5005c80011242419000000b0902074070350154401d1414010000b00f00c01c0b01403025009420f4002c140c50b1101c81d0041005100341e40324038050b100380c08000c0c20f101e24010200c0007540c074070360b042040c1c01e0303002064040f110040c040182c2191000d003041140803c84145a0400007444400200344100c6455000705d041000303512564845480d00e0141c030314400940c5c82961555100c0d1402c7c0d01c81000035030084014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 640262913 1250 640261663 640261669
    0x3070e04090c060f0804020901121703090604020a0909030e06030a0e070303081806010f172e0c02031201230d0c0306050112120e060c2413020a0e060d0b070905 70
    0x900108240b400c104175145060390000310300020500611841161102c0c1040410000803180800c0f01500004070b82c030b070319100d442c241d85d44004550aa1140c00365000000725680c007403003100800f0340c0540c1d0301111403105000780400c1e50b101508980415a4448407801100c0b41803041c0300c00f4601c00d58070040b890130f04464407640f22010044241c00350300801d004000800c07a0090030000c4038105403002088445d00d518440c01c04808100b5800d203040744550046203201c64000c1da001c10b92000d001000025000a8100c0e542d000744107110800854000042c46003100410851219008540c1009141408100440e96208950004031140038482030f0a10410949014150140a540c580e03001d600c00a5140c603510f00402c40307559414081100c1d039401070750301d40d10100c41421102c4030840c5d61154801403425014904950030309001e03209072011841120344443c4106084d03800a062421041c2000500e000c8410050a100e500080f40b5000000117403030121084d1044440d5107610302034a29103418 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 640264163 1250 640262913 640262927
    0xd2f01060303030e0f0c040b04090c080a0c150f21020d06090f020304020303070605070201090c0815060301021606050603011401030b01031e03120b010207082a04060b0f03070e04090c06 81
    0x240b0f1343c0e00120203020785084000b0300d0391200c4074200c0340411214002d4012a004060801000d03028010480012414080000b612010a4070504c440c101d11540c5100c1845220240740c04100002d07060803a41307402e6841010310050083c0e60b40c014868484a80196200326031004581004044e26010100030341501d900c80c0f46880800e07018194a149020344c002074482c800c049001305401e45e103d002c1821640300354000d80b0442d9000c0e00c0421801d8903800c040390f60309141501511080101800900d803824180262441082032071060070034148183d03169006420001c14582d0559a5041401c0c000c440807580d10303000794062000c808007035040d802c02c844a01c5059041d0040340590f10000c0c00042da01418502d68240c45640004107200d0b0300e00102d04111203641705610311721441901c29016001016190142d400d0f10302a442140100e1003440f0942e03002e072141440b004000d0103101850805c03d4002c65002419141c8010600365a10005040b25224034096030010b4101005102203034100c44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 640265413 1250 640264163 640264181
    0x412020a05040e0d2a030c02030607090303050f0d0e0a1101090e0f010308070519060c110c06030a20040f050a0509280207140606210d2f0106030303 65
    0x60280240d003078000f6140c1e500d1018401d04002c20194103020070306213031140100140c0d10001c0d0000d44401c00300d8200180030b6050640164803034041c80d004076104070301450b055011643e054540f2400e0807880a4005d5181c3c02c0320000749652602c1d50020280380d801070004140c0c90b445070b1404142000c0c10400180058003a8001d560a2429541803060719070401c14880d0440c0e5000311156520f08241c0790440c105082e41018110754908000f28004104050300300e90f2440c860382d0344404500004100096480800003821500700104102103043d4141c56000b0b4440e8400c0b110154004000d08400c403201070f8400c1d40f005030001c00c981818403040c0780031502440145400c45030440c1c82d003084640b401c10040113090101c0c00c01c641400740440c414890b0161003040d500107941d040300c143c0082046850740c0d0120307225481080c0b034030340078000e118011045000c040c0303220000b0400e80c055800b090711000348040341c044141c48040b0428039010302e8120705d070001c425110f0011034120700d14079028099401201d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 640266663 1250 640265413 640265419
    0x30f0b0c03071e03020d020a03051f1a030717010608100b040b0a111e101d0a03030b0609120d0e1c0303020f040e04030c050f030a1718030412020a05 65
    0x9200d541c641c002460a40060040c3d641402445809401d030002c0c0704020b681e080c601d00220b105c0d00c6130b0703415038000b034460080c1c02d83c1c884444000b02c885000000d141e00620812840903c081a420824100959030145a071704002e00c14800c0000c1c1d001142c2c0d0240e0003030303000504550400060b2000701a9071802401c00590180c1007608101070002940142454402080282c00c0d0108000000700000f007102c1e00c0c902c52040c0c415102c008643d844100c2d0414000b030150030000d80540082c0c00d8541700d5200b0301c110740900b4910182e59401c0300a0400c60f0209a070107201403040628607035075070300e000d903034400e51000038a6801d00c0040050304199a08040324425490282c4421052898048051155034103150050356101c40804444184c00f032074100040081d2941c082104054119034400c504e11700443c100c0e4445500e4000041d681e219a130203010009030001c09600045078a452429040002c40ca160b6078006100440580f66400590045a540350218071040641c01d02922202c040e05041e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 640267913 1250 640266663 640266667
    0x50109062c0a0f081c0608010902120a030e3f01050609040302280501020a020114010b0f0403060203090f010f0c0909061d060102070b030f01060e060910030e0115030f0b0c 75
    0x150b161940c83c07002c5101d01910aa41c00108500d0140032134244100040541c1403c01800b074550785868001c03c04440304030b00403481040c0404810301d000072805003660345691444886035002e000d1011000d84107032100042a8100422a58060b0885540019132051400c00d500440c1c1d110060b400e441001d88070030b0140104205003c0400e0340864500c104d40751400301422081901c07400c909801d00800d00c06415944042a50240d00d0b80c1908900c00c1c0d10040c906850030b41e40c035841841d0262080c03100d40340c02d00c4000c00c010400520107401869103c04981c066501c0f00624548241c01d40b01e4170500d45008a0355400e555550a0b00a00140701802da459002c11009040511010038002000001a52203100c1000030340c04e42c0c401c11010001d0900b505840d904d0b401c00c00c001c040d5464080c00740d107000c24014400b04c000ba00305401500d0044e240144010700035100b001d406e500801c00350182c500155215500400818880c20015000350703c1140200d880342c1090078405171400025000b882c4e81801 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 640269163 1250 640267913 640267933
    0xc070c09090b0601030c0c140f06010f0807031104180c080601090c02070e0c0c0334031707030b10050d0b03070f03080f0d240f060219050109062c 64
    0x80d850741c0340d021030f081c240001d004090307000554540c07070010030007030100c00c046200b1a408500800c1041c0070b0a5008122203e40e41c9a07085007040000e0b034018514154400310041000c0f87d40200c00100d86e28000e080080c400d0781c405151540d500c6903440c10b5031006c036203413010800710604004090051400010400c020700381800007e46511032841541007051082001c20142460780045030620441c1c0d6040ba42e64105030400d036a0b50b201b10441e041160040b03241c100c0800d103c41541c0d007980300d83c503996010700304c01e000d02d0040f0914405802c4008040da98440b011076911000c01c0010311860130381b600c5445100d0a021002500d8640c10b01074040c1d040004e0800a9046800c1042c0540340d118685a840e042a42c04c3e0822500071030612201007802c08442e58500035400342d03044840f900c004002000170f5264050305000c1c2c5918400c620060f8442203906018202d030141e690b858038443d80000c02e07200c0442d107581007903881055100305030082c800365104200d817481001081c031181e81401340030071400d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 640270413 1250 640269163 640269173
    0x210020315190b03040f1a130b09070b0412021504030c0521030703090314010911060a030b040c090e100b09010507110409050304050102010e030408060703090510050c070c0909 77
    0xc08444882d004000220090701c00100d1000414083c1c0b08024203c0d071a490541490648070b0586142030364040401107003003481e40300c1d503c40f0300d108030281880c00380440d00b40c0e541d01021220050900c40540102d00c4086400c1c0c51503c003c10040c42101c0c0901c2c3c8043c182d004000202d240712034030b241203540c20081040040c8d41c0410007030403030b0811074501d0400d003120810040c2d0603d004a82605ca030000085060030980c01410316000e40f40079405082018500c40301c2907003265004400134040c0c40104032001a01c0ca0441c0080120b009645404500981800c0c04581620282483c80c0081042c1040c240b1a0810b0700100641c80881c03211204081c0d4517085107070440c0e200d160440e070304110000603000180301007076401a066410151003040040340f030303061190b00c9800034040c5030b006500300600c4c0d121504001042d6403d8600c0903000d0110754139442c0d416801030000b0542202c0c03c0c0078510354407115800311b00c9450305c180405114030f6a15001850110800007075904107a141300d15003200703580401c07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 640271663 1250 640270413 640270441
    0xb01080c032b0c0b04050a060507031404020907050f03091b06040f05040209060c0d031a010f02060f040314030c03041101030501180b03010213060c0606050405062413090c02100203 79
    0x280c1d80700c00b106000a079003508482034406200060407001003001840204100043e54021203030244104106a8a548004030107442640c401222459540e80108000d40381900702c130f40e04603005040c00c61401c45840003211103600308031175000c1e080e00518003600c2e044020102ea42a4103400312007191400f81032245640d101071542c0030301805a80d0129520029407100740c02c072100c2c0e8640508642c0390620078034000f4064800100d00801481070000340340c070107501880d040c41c001d03440b03600517100781d0740d48201400c03201074014001c2d82000902c49044070460074480082d8020082c0c00c000569a10381800e0510000b01c40202650400d49002d00400042064000c0d440c00e04021040100301484090700080c060b0040050140304002d403074000080d140c2e00101000307889885105c041c00116aa80300b0881100d03c01c4680c25004007440842c1c0c0d0702203150741203842c650180e000c030290a0604032011200304091982062801c1555000500d032210f40401460f0003608903203506514520b0f101003c3d000c04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 640272913 1250 640271663 640271713
    0xf1c0909020c0307020d060e100209030312091005010e040b06011805040c03090503030703140f2502010204080d20011a1e090a2301081203060d0f0b01080c03 69
    0x11507408640d2650761501403044039441500240b0040c405041401c00000411440000042a102d50b910340c0504001d0f034001c2e41c1d414000100554188011011541c0000400404a002c1805520041c20181c4030305d04c1010702030b18100b003400b40d113481c3c0303842c06404c01500500710074140150002907610580445902005460081d0343c00310b22888045000e84c040c000004004101e80030100400c190b560745944150b25184029250908a44a4a603c070000e40002c0d0b46081ca50402000c0c1c22800303030400740803800603000d2440010310b8640c0c2d130300a1750305204100003081c000842400ca400740034200582016950076021008120b8547c1c013100c813206c016401c85030180241042d6440c03030b015843d6010100e040b16406080b206441c9007203106980140f0303810701e01c1000300320201c40c0c08400509400046042c4e0b09941e00401e07140500c86100e040700e0b0002404a540407540140c1d07103000400700101c2001440c07107140310315241d5052554060404520580450003a800311280c5180558005070840345 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 640274163 1250 640272913 640272929
    0x3141e0714010509030d020609070b19030b1306061706030d23040e0108010605010306060f02060a0f0b280504140f04030504050307031202010b01030204180b030f0a050f1c09 76
    0x10500030140143d0350380c020001c000e5410b000e40001c1c55009900800c3c0705205401020940e4100f039106c3c010200c05005400c40b441414811892036290b6038000d03803000302c54601c020041074187d041c40848100f40e4a03107420160000742c0051062507000540909142c2001044010380700001c2c0c0484e000300144040315001d00d40c030b000c040c613004080c0c0c0385a08403006006030380c030b85001543e1070304803607406445103101d100c1c0007038544500042d03203c1c8580152408a40c030ba0f07000d0700107a03c529480c000600904100b42803c0760303451a400d0140d94900d04001d0740f061002d11030701001d035111031050717a80020660040c0d01442c00c0141c02c41500103480391290b40101c490b8414441da482e40e0a04441d14003031a00200d8144c45561000300c01d10500e010b451401140b158000d001c4000d00308011010b9000e1032181c2203541045a080b03035480310381c941283d444c40c40060125210000700d000031520301494520251012b4111002485858000b0b100a4000c0c00c00c9281c80505c50014000c0104200828418004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 640275413 1250 640274163 640274189
    0x50303040828050606090604112d07120305090115030f020117010b0a0810090509100c0519030f1b05070606050a051f0219080406110f0c0105070606030204020403141e07 74
    0x87c01d50744580c41003000d000091601030701c03900f05403030400190b80310b0030071803016406110585075440942000c44641d1070f4040301ca058030401a040c29005024082c20031030103552039400e40c0194050b00c407074520045000d5100744090103d180001f41400e52136070060502210280e00501540d4048400c4614030113503460207400c20340d5104007038103481d2020380040038030a040005006110380000b6101c01020140307501080a02c0c10010150f030765104001e0030308007041722541e4194107030f40654018480d041802102149501c0801d401e0800c0200310910780022890103d40441030000c5c07485204003400050302c60321549400d002c0050000782c440d400415200150446a0f48114800e20140042006c00350b5246010055441e00020541103030107800300250040040788112800020501130103100400903003080d0012400450300c07948110010380e44540c55440c00001030b281c1d403000340011409054205003603075424660b03500300b50700c8200110110300b2510340703480d07001404500c1c4000c540400349684c3c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 640276663 1250 640275413 640275421
    0x11a09130c140d020d03020a0308070c020a0513090c18110c06010506090a031a15010c15051b03040c0e0f0f0115030f141b160803060a05030304082805060609 69
    0x100d2400081e00c0080d002140075217450300301034000030403688071071003174030b402040c2c0e65a02001c9465807640c404c081d60014a80314104a0340c02c1c107010482200303104840c082440352042e240c5c1c00499400303602500b2400304881c80301501d00d000384500c4401c10a041d81c414038010700b001c429513940806009241c89020005410001a0f844d20021002150312103107900915020740d4007040005411100354109204002000c40c8561141400d4100a64013044145443d8011543c0d43d005100040030703101c0b4007920110500c0001035843c0518809d41c407800010400c241404a82200320030301038050302c0c480b0707540c10038040d0004280140e681075407007500e4820304002c1e00b814100c0140a42c0c40307080880c3c6250218044400031907840d054070420041c000460b0402c610403820100d0f2281d21114824558050f50b02000190184019900103500420344071030a03890b100000e09581c010340c408cd07801e9220b841643d15818025080302c925009607a80c01f1441c14a0b80c40d102e440d107900904040c0f0402d00340c0006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 640277913 1250 640276663 640276669
    0x3120e0309060f04120c050a0902030f151914030d030203070c030309020402070209040807110a06051209010b0a0608040b1612021617090f0301020f121305011a09130c14 74
    0x50380082c03c89802c940040412401c26052001c6c03140159409a8060000403070480641d008030307802440341c2c5507034075056501d40d107140c0950046003860980c050200232441504002480940025105051420724420460000c05181c045800010307028940107004000311075030040b00d529a165014100401c0c0c500c40f03031001a009214100c03000394045058400d1105104465004d0019244541c03882c91130041d542c01002303441a010310a04001910800690f0120381034803224035046080c4030008034841e51544001049000260083d0000408142c204821b1013400c0c0e00c01a0000015503c0302500c903030f40780d401881061004e02d140d90080d00001c840d20910940103d00440b541c21021488080c20135410480382507200300c41c1a0b105442c0000240c100f40350620894215618500100e0300d015002119070003480801410100641800d00201340400d00038061000400d0b0010380310155280d42000b00440d01c80013400f400001e0014403403210000e203000d040c01c0c0a840c9903882c00060703840c043c400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 640279163 1250 640277913 640277917
    0x1808150414061503010e060c1614011a10080c030117150403020d03150b03040f140109050d031a0a0311030708100f050c2106010c06050405070303120e0309060f 70
    0x65010140b1408041040700b400540d000b40300860700303c00a0092500c03480c07000b5aa03000c00e540c40191504200b011482c02e02d4820106c1282c82d104028000c07070480392183c11401c441e80003450780006841c5900301c036583c1c980b40501510001c3c0c241048226404c10001d2442d05000c14090240007021950720700442050400058810901200c09500c1500e040c1c138009448140100111020a040181e0040c124004ca407003d0190749070905040d0840d07030389071203902d828059800c05640185c0500403440d41d40d08280200f01120f8050002070249101c2c0400050480d04030b482910a0784941074403502c0c040c1c0d948100e040840e03030085034070200e01550b10002400c0040a9010700075501c1400500b00507009590091048120003140801c400d542c0c00c9800f000901c5207552520340f0021901c0c07031655042c100140e5a821041c18900f0030b0030138180f5a83c0100711001560143c03000ea00000040041640c080c100c2c50005030140b60074071400101300915a52406503002c010b214402c0801c61071100f01c01c01742 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 640280413 1250 640279163 640279193
    0x10b070816030e03010c170c071118150901050306070e031c030603170a020a170d06270c020c1e0402120a0b040603030507061a040c0f18081504 63
    0x40d604601c140c64600034040d0101c1c204841c0c02542843c880804c030501441100e9460000000d108490b0341c1c81c600502502c0e8814601110201e0300e030741c0181000d0300d880462211003d0b504850520f0360400840e001007217000030152511a404510061105480200e03072103070415040d0415502c4840c0c80c000082c00d180c60000c807001020151030a21040725031680000c0203c9014000c0d48504122942c9400c0842c400d140808015a2100b5076140001d40d41c2074018a042c00d03084026420f100041e544a02519001d900c50100303850800842c0c1d150710b0004040c1a101c5441c2c2004002d50320404030081d441f40007020215114941641583e40f040007052690000200003c10031503960b1402562080030705005c0e60000c400c05d1400e1452802400e0500c03a0701d0580c0d8050b1110f905007a070540d141c0002d007200c12002c41071140441c40c40140e1b41c95602403441100450f032110030210721501401010640801c05a44100c0398000b030802001e02e010038201c80c905040b02c040c0740d540e561800d0000398268115 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 640281663 1250 640280413 640280437
    0x504020d02060309012301031e080f030a0219090e0c0702040e060f07091e03080306030c0315060f0103022502120a030c02011e0e01030c020c090c03010317030f010b0708 74
    0x4004d407414040d44404d1900207400c0b203121140310030050360b40155200b40402055414410f0107172075070100300912100b0349449444003924000c0c5103114900c203900103807035070711440c2c1e004112140c031b80740d203400c8c030380c0365403000b8600078618603d0710000c152100409881c044080500003042429500c0b550410200e01c9241c0d0111040c0d402c00c0d43c601c401c103540460300d01c000594403440c041a5a2144409900c1b644a4625113040c100d09507144d0310000e5001404540e818071512070f0f800720704c1c0c40c140f000356690055100c50320594a003001c28048a041880d850a040620402c007400c480c40709031201c0c0c0c140811034142c04002100d0381c40400c2a0b2145041c0e003640710320908030800109544000e521505500c01e81c0d03400d442c26010b032640002c00d4150050000810881c2c07800d40101d51090b405481d1030340ca288115204003907440003090703100a058441550f200c00010060060000301751000e05110700e150315461a40c0b42c101d1200500090600030601c90010018003801406006020703a0114484c2c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 640282913 1250 640281663 640281667
    0x306020c0f1608010c0503010e072a150b01030c09090209040603080408101406031011040b1206090112030807050315060c010911040506100e12010626010209130504020d0206 76
    0x4021090b40103000e124580040d824280600c6406100d50203030380c1200c100305444a415218018252915898007160322a5000030300c1c070b0000807411603090042554050f00c620b00c0100350b00e09140003a2410901914181400c05a6a46841d680110580102da01000c0c0040e10345081ca000039001d040c4507440035002172008a4045040800812502c45100c2039100401640c60502040485190115500c940c1908010b49000c085085500254240a403440c5860b10303003501c44034101d03040e800c50101d0b040e03896070840030040b890500c10089030262401d05109010701910b581d0052407854020849010041c010000c6444600d071400c24045182006040507141d42010208900a000404041d503860242207404e00d090f0130031307106203405050060107500081c4440e00095901659140350f0715001054071128000400081c800c210280a601400c0103626180d07040352030080580302900c100603441040b4400099461a003810b1030b0b0800349001081507074440c000201501d030b001002940003480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 640284163 1250 640282913 640282933
    0x30303110c010e0f07090506011407170a09030209010e0903190c0c140306100b0a050f090910080f0f030d0e010905060408130e010305031b030712050403060f02130306020c0f 76
    0x224412100103913801c111501145c0d034403c03920a849040d2156808078110f0a61800040c20440080c800903005940e0030f000c1418843c031a00540e40301640100000d00c0108041c0110300e42074103101d00500d000803002c1070745e091807205641c82c0d1080e00c0948c0002a4030103a45510179001d00c22900203d50400920010681d0fa01d10315004150503007800c0d44240500b00005d04102c074071290341c0050701d003428526818501199130030f44140e480b8a501e80c410300802c6c00914015a140d41c0309e80d20400302d00c07503625212407900c0f0030307685000a81107a03080e190b0002c40c18100f840f0000000c0e944c945a90f201d01052a40741030296a00410410343c0141550042008200c2803103c8072000b00512188002c1c00504955140400b0030144c60a00008015400401544a070342c861074050705400801c910a0703d1030701c14035640d45425a0040c03001803000c00d05c041401c1060000c984119000d550410344113516011120b103411039a40801d010090542c0d5000c15181404c43d41044071640e5040614103c40407000c3c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 640285413 1250 640284163 640284191
    0x50f120d06050402071101030e030904050c071a19050c0403021e09100815040c170c27070c031e03090c080109020a030f080f03160315050a030303110c01 67
    0x88403190490055060000c001000c0c00c00e882118802608005204c00340035200b80110301038410382070103580501c800c1c803444250b6035030f130300c40c1c5405400c00c0d8002c5541c403900c1e0b10781040706202000240001c050b2140400564100c00d882d480d00140e09030800140036aa060302c17801c0c550140740c2000e90800c84100b112080d0340000802e01c03010a40c1107610300c4065a8042c1d131a1500c0d001c0d8011020540c10269160950405040b4216042403083c400c0c041d070380c3d44845201410300304140c0550301c2588249241c15003070070113082001080b81220340c01d2000d03602c0c031081c5a20650026000c203040100c2d0110350411f0501c41c41100c6003c034070700d42040481c4207181100801414000d1000c5c2c40383c0d00d1a18001841000500c18140025800380c051400c0500d0341c3c5410750a880300380010745031000d003081042e00b2900e16400440c031407249050a000206428030008003141c0100c0040983c041c2c4800c020300c0250f841401d80d00460354145008a4500041b248141e424041d002307082020350b08000f69909104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 640286663 1250 640285413 640285417
    0x140d230c031e13080d0902030a03080a06060504140d031107140f040c090e0c0c120d140103051009030e150703020d1704080904090525080f0303070c050f12 68
    0x150035101080e1020a9070201800b406015075880301030340a0001000d0000e4052030103000f040702007000010b203440c0c042e000f1904100541c0d41c01c40010300c48004002d040c030074030301c2160301910300c0349829810315040000400078035065080340d500c940079060440b41014881c01c007038800d1860a2040d1444190385030442010b211103200c40900c5050500c45116090400784210352055140f40c1c0c810f00303400d14040d903042c002200a450002e005504202d070404040007005103160300008143c00d9039036000c00445910031100203d8041a20307010604c01007012440000314907141a011200c0020a591185803c0c2c0b05102104641500120318508202003081c1000152014034004e80946c0c20344e00d01e5400444586407150528152100818041400709041001629504a02038400142da102e80d499151800300c4480056421421031a0306403038500454452800030607c400040c003551480d80308050726404003d055000b00704104410308280242000300403e07100051084c0c510503041c1440800c615 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 640287769 1106 640286663 640286671
    0x70c020d0c060e1e0d030e0a090614010e0102060708071b3203040e0a020c0c12010209030d0e0603040308190e011b140d230c03 56
    0x80007100e042000c2e0940ea1580c40c4a901200c0800c60307240c41d4405611888021000d4500c41620744042d84441d5030741c5401e18810450918010540d6049698020440301341800f00c00120101c5c011082c0800c04820b9070307a8540c2030710950059175203040c107540032000103c8013800106024856404e00c0741114020b00c1107480015607803030303000e03201d00030104031944603c044103002c024012000342c08004090750350241d800d0a15004422121440007081c120720240c000581c2c1415072014019001d103000000d1150141c12003548041e4000d41041c0060b038028400d4000b0b45a4482c0254501044554002c1115145a50315a81110301d2400680b181e014043c01c5401e0008c08038a43c0100580340b81c0031400002d40c1700400285210581034440c5007420701040c1644a410783c0202c808a0f040030f401c0e0000400c0811600211a101c81c00340034003a6a0038422074140f101d1540460011401 = true := by decide +kernel

theorem cover : BRFrame.Cov 640107913 640287769 := by
  have h0 := BRFrame.cov_init 640107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 640107913 ≤ n) (h2 : n < 640287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
