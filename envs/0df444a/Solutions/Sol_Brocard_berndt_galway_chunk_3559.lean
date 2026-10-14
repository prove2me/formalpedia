-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3559
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:00:44.184229+00:00
-- url     : https://prove2.me/submissions/1ca4d333-1409-49b2-a9f9-d66be24ce5c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 639928057 ≤ n < 640107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 639929307 1250 639928057 639928063
    0x5070201200d020a060501050d020a050d020a03051c03180b16031122060503010e0c031902030108011e0528090b0f1e0c07020415030212071e050906010c05 68
    0x90901960241d50010b040100029102c1201e40000e60741942413000106103450b014400c1c09010354024100040c0c28509002d220035144840f4041c0d03444400a0000004a0414803100b2105040da00703981c48804c80e10744001d4100c030307010341c0c0c9400c03400300c1010b00000050b0300118003a0010b48014030000649011203041700030300303642890341c4004900401c01c501001c07004010145410103e034944c1c1c41c0b894840a0469880c002489400401400c25010601130b10151000f5500300c0c1001071465040340c10b0480003000d81c0d100703900103249070f9176075007844050040d004440c49841d070303444c0c20500240c00d00c08030840e004400400e00c4061102c0c0c1c00800980542154400042c0c960f201e9000f00081c5040302c0421016041180c140c0c44009038400214420003c00bc92144a49d000e90707800e90401d10345400380700082c45041c640d1103904803070f082c0220140e6600781e0940d40c0860044002e1402d0343c2050911426001901c80400381907001d0f01e002d2080d40c0c1c901c1c089036403048003841c000041c012682040341c0303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 639930557 1250 639929307 639929357
    0x14090603040c09290f1f0f08091c05070503070b0408090f030f0304060e03031209010b10020a0201080f0c160b01061205040203070b1e0f090414090d0806040e0106180c0f05070201 78
    0x310b0f00c1b00c410750b03000000d4028a5240d0103180d1070f20f90701030701ea803000c64003500c1e0b04a0852007084034400f00c040f801c000e4029005850400e00400840b8106403040d65160007000c0150741c1070b038040c00d000c91680c11070300d014032030550b00a800b079014003a0803003607115042c2eaa01a900843c010f0000045013002c09440c10801d4560030500000c62003040d06002620a00070100003d00c81e0045080c3c42c800c6c40c05500000d08e0004a56042e0745000300b0381c0ea0116140700b500f4001e0070f0f0301d10364002002803a05503003a40c1a106c40d0715001c0d800c1d03020310307504d40750380a4416120a08024200e030704000070000541c2e00840c0c1c00b4104c41c1202c403283c0d591031f420f0100c2c0c44441d8416109620a807000300d00003c0440050b000b0b440304440c1558104030310541080b001d004400225815111b5034040102c0c030382c1c014070036401d090b044200604041059020301d5102402e45001c0d07000415030304c1c00040480c8144900b406030b95002511801c000c5000300c04e520008101784078003203000e410b02c40b003194030081040000400c05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 639931807 1250 639930557 639930589
    0x110f1f0e1911010e04090f0605010e0108061501091e0e10050312070302031303060501050a091a0f04020405030307080d0b06190c020a0f031112030a09030314090603040c09290f 77
    0x21407003441c0b038047e88216103580152140c51804c00041202c0d8110500306040c0c90000c40189820755901071200c4000140b080c0950400c0038510340010002803c0c40300810300e00c1031a902c0c0c1c0c0e03800c0c202502564550001801c2c0704c1ca052601d00d003009503403008251500e01f24661403115541c0c00f81424140c3c614801c4c6180108040fa104000105008180d404207059603001c4803038a4200d41d807419a00207581030900329110750411100c1a000f18600240303070006c580d130040e20150806036118000703425900030341d00c255140ca00024040145020922901c6a01001103d529040c4085c0300751010643d400c1c002c10702c0601007111031034001e560300c445004e402060f0100b10105025102e141c00d41c00c49210220742e90180c0c02902c0a01c050410120903100c404e1016038030b01b501e040c95528112000310244d400103030704040c00c01247d400c81e10b411000f1880303140150b21243c1d034685007494102c200c81c5101d840c0080035101d4100d212088021031600da800740b104640860700c043c0f60100150960507601c40304 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 639933057 1250 639931807 639931811
    0x3030b030a1b0f090c0806010f021f0b0406150206010b0304062903010c020c01021216080301062c010f031d100507230a110f1f0e1911010e04 62
    0xb407100000302456482030703503044070000101d80c2d940c081010940380c9074078000010902c00c030f002a40703c0d40700b40007011030000d4500c1110403980070501c5201c00075a107540c0c480001307a285da100d80c0c1f103403d280c05044000e24072180000060030720030100946850060003005143d090010110303040c404540c2200184042000c044000c0b0105440c01044260107810918000e508061984c8034190011031144a04072068018241024028241358596030044400700703d6210114158408650040061400307410b07140c8440201c0b000e843c00c074451030300001080104440845500c2d20050340e0040c18002070340c0310742c200030a889128140c81302070030507118500d0308148a09005030043c2255500301d140a4016501e0700074951800c42d14021040c100c800c90310b446004c0c01c010940020344a48080500d642d003075000d55041c100d90820791414011051a0400c600b050703079111506141c03c2c2e101c0e070044030b880c5a00401c940000b0b032066100b10490706102400b1801071200005099024160340c0103800802001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 639934307 1250 639933057 639933083
    0x203150c0708040e19090b06040c2a051603080406030b01120c03051f0501020a020603270c041b0818190b0411090c030f0403030612150c05040b0703030b030a 69
    0x280d00d26500c402c61709660002c071a0344c074860300c0200c18444c0381c001c550402003860880c0d4501c41400041c0c04c0c0842100c081013805ca2166582c20032080300c00302081c65958100c42e520746107091152501801c2c1040c0c0803130f64800d910420015110303030300b22804c44800b801c000c1680040580180c5154203284e08103414142440d400e00c540c141d265003c548160980b03401c4815030400e401200301120164001e66015903ca48403280c05840e008001e1580001c2581803102d00e52441024459034510038a40b0800c0384d4440ca082140c10300d058091011180d50b01000c0d09400000850000c203591300241c003a40580758043c49900740700106200300c82a00032003071003d0700c403a810f500c1c00c5580c802c170072101550040f8800030f40c41c4103442c2c4030260f40d020701c6e08107846a08580700d11640460122001c0c000b2130505a40d54400940c52140c2898410614001e840c0841c00541d01d52810b820b803a5006900020040200000e109072003003402038504450305032074005101003c0d400400c3c03030040d40380400b0b4804c850441d5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 639935557 1250 639934307 639934319
    0x1902120301080d020d0315090b0f181e0f2811070203010b090c030123030601121505090d030e010b1e01020f01111e2718040203150c070804 61
    0xf24a560504181d003150920a0004070440861389040601200c401603042e04000e11480303a001110050b60040c95000e04c629040d0024101070410280e0b030340c82011010401025444120900740c02100004115034145420044400c0c03541d0014000c007481d41103000388412241c0a01d4018076420002d0f0701c20040705d182c03c030290a1641068030100d00c250f0034080c0381865402d00060442c0115400c910150459007440b44032003543c0c889905517908411141d101c01c40f6a0307020400c0030300806002071403082403101402d00c0c0c0c117140180483d08000c0d40c240818031001440018541c5000c1910380760010f281c01d4901c52041c05015105110350388144442d407030508000c016001d070a0080700076000c5549880c3d42c0e4140a080e2070072100c80100303586061081106221481010382c003801d0504681b5464071466800741c0a4221240403510b001c0000800407044c1030030201c00d44850b1500403e910f5007545019400a80c0da0324259050a05a2804101007072290322030105840780c00e40d01180503034030360745c81350 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 639936807 1250 639935557 639935563
    0x90e0402010807122a0914090403180f051302091809101d010c1b0f0f0501051312090b0912071502060403030b040c0516150924050c190212030108 64
    0x818410b0380c5110401c105e241440c02a80391400721020040390041a0000b4001c011116800500c2079043c0000142c416046101c2440410040d09800d4041c1542d1414502030103088841c01d006008101c0c410056603c1a0fa250001e1500409009072041c9079a0b4404070780c1410600c0c0b030303066009407134106918058050342e14149200046d030b114008103d08003841c04121101c11180c52450f03920000032640c54003113080c0c0314000b030506004c0c00c18120380c060f43d903660a08440d8215061104500c81584038810000300010400d240880c51410b02e40301400d0001d0144a0b11403165110701c1074910071000c6003c0c1c44207000090091020f01409800d0000d100300113901c40c03400b1142100040c0c0780c400425602d151522034500403111a503102070600d45c560702c0f10074403011100c40580d112200c086464089113400c0c0101920240720b039820203044100325140b40d107a42c821281403040c1504204c01c0004001c43c4c10151110041c0360451060004c1d43c0400c00d9003061182002001d0b4081c00100210f0300355000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 639938057 1250 639936807 639936851
    0x612051503101a0102070f03080304020105070804060206090f0d091205010f0207080d0b090f010e071116170a080702090c070206190e0f09010603020915040608060a06090e040201080712 81
    0x3c90042040f2601d840126110703e080d000f03080880c1c12489044c03010070800720107940c0c0300748103051007880d190b120b803551902a04640e10400c0160b00c00410003074003100900c07114110841c2c240042010b1000d00102600f291018060701e44840305034214241404400d400103040e5260803074046645039120b0030074211540c4030100d4510790908013130704003204d4204101007038031807109030078400c100380d00b400c581e000410700c0600040c0c200004060b030a0344200c81405000d075016900d01e00f02c0e82551400c07403090f00e81c0000d408856107a410070505500460742d248121804640e0494800076503989400d0006164083c186029400190110302000d802c0c809082031850f214803500c0d40d04c2d0002e401c4c4d081008241d41c0c6803800340c220014100400c5840e0080c3c000e00038000e402051160b04030040c1000078100d03005940960001600281403200070f05202c42200060811441c0401407542480400001c0d8200540020704100c41c140015030081d204444029010510080c140002c05101c16001268560 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 639939307 1250 639938057 639938081
    0xc0102040e010e01060c02040b060705060106080a0c0e0d060908070f1b0e1302101110020703110325030e060d052710150f0314011104061205150310 65
    0x180700201d400346800c07080e94103c4580e0f07a030b41d0a10320790b240d080c08080e29805018175040002407100e840020000d1209074060303c0190b4900c0614980004e442094070030400150003401b000304925582c0b51039541c5610136107508500c0c0440e800800d031901422074800c41070007500e403803009200001041405407507070300d030200c01500c006411030310f440d00101100c809895811a03140e0800d650700041c2460070980c1200d41c00c0c2e0500a591441c2800d0260500e074651504007000c0d640060440c003016007004256030015900700043d4202007103c440107800d03102084107581c50401c011104001c1521801035003180341d801800c0c2c29164800351a0395406020203440c0500d00c1c1c114002188030b0500314003005402c103817a9500800022a00240d0316000700701041c5490403003032008a02040d840c44550b0301c640114811031020390050ba03078540b440e084528a00c1e10381d0009000b040104a49079100308107042c8100403250005490711744d82845006403030180d001d2501401004212403039030b01507500c09095460 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 639940557 1250 639939307 639939329
    0x7030203011d160315050d1a16270b0705010c020715140c0c0607030c120f0801031506180209040f02030c0406110f0105040c0302030d02060405100b010210020c010204 73
    0x118110342c140422084808140c0c00c0050180d0b05050b41c40f0b030f0806114071002c101c1c0c884120383c8840200760040350049040d12089130800c0d0720200c180f801c15107a03620003944030740791082801c010b500800c180c0541e44141403014440d807403002d620181ca80d0b640c0c01480c40043c031556540403454024041d2000240d80000350107103540000c3c07588420003d080c072030f041c5d503524085100480c4000ca034094000c0c9240704e406208510b001e400a4407071000410f00c06d800303512440e550301020702c0c0c182d2140054046180801c9500c00c2d59102c00e41d00a11110305503a84401e044080075031180e03891004011031383c04080075403040c001c03038601d001050f8028140d10300305442c140564481440360b0016884140e4081500400401080100c58403400103100441d00c0130b0240d507071000030b14040c0342c2920415074040d903040440e8001002141350401013019101d11500280082e85441d1716055101d0134280608000e81e03890b60442c0381c070350303109115401620001200840d2103030100c140c045d000390018012100c8100c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 639941807 1250 639940557 639940589
    0x212180615060406051323030d0e030a110301090b040c090e0a11010804260306270105011103120c04080c150d0b040212040b04031b05062a030703020301 67
    0x100304404021040c0c1e0192801c0d142529292003107485510007510084840680400400d150740a021002c0c04d04440140e01078601c5000c004060415031014003441c1071200540c0102001e403400310340e424a4a4024810790503000344100440c5c090102410001d2014811600300002c20420400c207000fa503448007410481c001c40c02c408580e1b115610350b03014160000800040312598030039000903234070900c10810318101000030f6000080d41740904106000c41c0b90007200b0005103041000c06004001d808c8640060001100d40c00808100b4040c020117040005071060700213940f80c10411104080c000300707080d40031031502809648854000e80200c2e030f2540a1040811410300d85901d10740300480d543c1819078640f26941641c2c0c401000b2000d1201c4e0069024003000d00781c0d40c52106114070072400344c100005189090f2600408003000030f906a400c0d290100c0c0d12034042480048d10607407125500b0700004484040f907810580780201101074100300c04000080050360b031b6054003d503040383d00c40f016400101c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 639943057 1250 639941807 639941821
    0x9130605070309031e021f0f0b06042106061505041d09070e0601030b12030c0d0504150309020d02040513030e0a0b030c360901050d0812090102121806 66
    0x2031001da0f803014001842c07800d00e2407042980e000040c2c11440650041f00c1400280300381428114464001c00c011056644d01c000410340040c0c0a01c240202d000c8a0207884c290800380c41440703040c0141042c884605024110300e0400400358404005001c070500d5080040e40c01540c020900ea216024103800d915894400c5030344d0007002d0b00480e01aa1480c405030060908081d1080c1b044000200203a04140d100c5480c450b46864070028032205003009400344d43c1d1408640361041ca03050720305e81200304103e8104400c004a004101c0600300c4402c0d42c1c640405d1a0070140001016034200d0580070758414030f06402c0c01040008014483d0f41c0c948a034a4481d182204902000142c80d4144960400b00a0400005105201c0131004005607102000d04000c80480306000e40c4d0308800a0034450080c946c1915180d50340e1034000d045a00401c4c0032501110404540e40d62052140036450186800c0c000c500b000c500815029019110005103041c2c3d800b106107031481d035144081031541e990310083e000d004c0c00f00e189 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 639944307 1250 639943057 639943061
    0xb130b15030a2004050114030a06031b210c090e010f14061305060315071b0c06021605030c0105070c031208070f0201051e0a020d060b280e091005091306050703 70
    0x4880d03050311001d07c0c0c034640b40300803845940010b02201889941e0780e40840000c440c0380c5100d050700140403045000d242002220300702c1c01e1055180d022049061490a00000c040518901c04e031208410040b49000e0000345031070142288502020b00c1c14240f8802c4110007803076864251185408903821008110003071a01c2045403801d8508a802d81c00401001c40307020003030603940b038200c545807400560460382081c00c5600800300030000c48030321034500e10410026a040008103c00d240c11000f07506d42510f0440000c0d61a8403501a580c1444030104040d001e210800386600000d41c1c00007070150111051010081c0440012250a804140380c2e1060143c014814400d15100b02c035102400c1070003517001c490102c0c2c094001801c14589035005c00402c1740590403802400002c10300d011055456201034840070420110008000700c00c1d1020034802442154040303002140100300741c0301d100d03854880b00d0034403095444036001150030068640c01d000040d031108071070100080c00b03041c08100f41c0d1520042102 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 639945557 1250 639944307 639944309
    0x8150a02340b07050a080411010e180103020a05060424051e0702180118241d010e19020d330f0b0403020613030b0c0301180b130b15030a2004 62
    0x10000f400075002800066000c8d800900c0600c050504141c0500030ae000201d400c00c02d076102c03c6002c0705503801081141043c0c0c0c02040074040440f04d050800c5e082540c622940e46012a001039500c1d6003601565a00e13018408a990b191500842c90341846900300805695500c0310608034003400359550400030150729000818103a400c42c0742c0320300c800c804120510000c3c0802100300d041d507407003890160030002e000034400c10003400c05001059031061206021070088030143e121040d850540d2080040024407100c40400b00356450900580340c0c40c0c440c611500412410000030782071020312a0480f03d040103203078203200f8071050240380c18069454841040d480b07451845013003d0f902041c0301c240014a404e00c007030306400d44041100a01c00381e582d1141c0e4095001907070007401c0e80d00d001005201041c00c500740452400c10110f001d1000d0f24040000c1074a1139507401100c4401907852507102410ba81304180a00e12081c012825600c81c1003100101d40244000c41580c1c2e40c100e00c0d009100340c01380550003560 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 639946807 1250 639945557 639945577
    0x534020312040305074a09150109090f030c0c0f0306050f1e010605210a0606080901020c070501080403030f0f0b130902130e030705010f0903080108150a02340b0705 72
    0xc4031201c1d001403e0386d009100c14258100500c04044440c000102040308030703105854020042040c140625060403074020306800007840710f400c00910f2008a24281d03011007040750b1524040700016018180140700000c540c02111400c00c00300000006d00085d03403c01402000d140c070000860b034565115034400c52490120704041d0b00c500742c0c01080300720300540143c01000c5804440d86c0204906036005025000101e8070040a5507460320f090240e9a03002d488103a0203840300c1c00031403031314281081c0b0a544a82c14401e15042094600c001b03400c05100c1d400100540c140c5190904c100254103801380c02034009015103038040e00300f1664140c40c05e034090003110b4900303401402c0d078228800300d00c5414000c0c05820030f100405110400c200c0000900921640d2002c09070403000040030200351500a08030b4606074030000c0740e03a0003201c49008240c0d1079010b15030064105100141c0d6105c0d0000c03811012125480341405024040c0268405024045507035104144038004101255580800a44050184480301c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 639948057 1250 639946807 639946859
    0x110a0f0803090c06190207050a080c040203180607090503101e090f050609030418020301180e07050a06020705031216030e040b090a020d050601053402031204030507 72
    0x6801140249005640018445054804500801010500c03907403080d00d00b1950036800b4400041010303810b02c000f802500c0e049500c0141c0301d240841c1580e80320050b040440c800c076400008554210b0b03507558529100d043c0e403000d50b80345140c8040d01420400da1442514002d00600182024003259440b817403501c003d03040243c500b0882c810395901c001301a8090700f03c4031640000305c601d010903010030000c1e00c2140031000465446040c00268184107919880c80400c00b030041c0014401402c551581c041c540d03102000000e644a02e5005040c030b0400c03154450350300315043d51008980503a010540605940b410780446000c2e42029801403602d10900500b040504488955a4006803041a082c041000003d01c08601107950b0707170001d21b80340b500780e401c014400e5000807400101d00c0030340906603102200342031460a018400c0c402d001440d48641450703441d01c2d00c201c46045450f00d5010020000750f0040c04540036440201030740707219035110f03000980c2d4034494094005000c803403410030a88004098542 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 639949307 1250 639948057 639948083
    0x319030509030c15070e01230304030c06050a09020f0904051c09180b03250b07021201020301090207140105040f080d0b0409060b0f151207200a03110a 66
    0x8500400c00500312001600003040500343c1220200102c684020b00300308401c0d075034240840301924607480c204074603050000c0e0701c1d07180705d419003441b2005080e80b00611040e550baa450340b5081340e0390502500b0041c0490325100034400c2c51401c50f0b205103005403003540d1404003003940d03008010060208880040290f800001c2055010616080c400030070416030402019040d120401e840c007500388410710440c12541d9800a19043c90304002d00c80840c1c000c661160a00b091011f005910b04131a030044044040c1300103008000c540701d59080c4001c00d0a54402152a561903014000c0a54800141600e02480710202d2002e024010701c2010b024a0b4020b4640c0e0b20b000566440c3d00746500250911000144c1c3c0b0328251502c3d8a1b10b003c0c031005288250000a80699094204060601c4140101e805518004000c0c4460300300c0300210740300742c1e58201100c0c0381541c8000003144c501502e081440b000a0200c101c4040318880095034071841d911a403104c081103c80c080c0ac4542d1000c003104013404c10141a42 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 639950557 1250 639949307 639949357
    0x3060a0b01110f1f0504030807030510080111130f1401140909040b04021219020d05120406080f0c180d0c1502070905060904020a06141b01140903 64
    0x40280c06420040c1007620441624440c0c2504014440030300c070050b03030020741e40e90103008003a11499030f41841c03241c000c00a5080c25180102801d9008029a040c144e131600810301c58000c5508180041c40303414001d0120b0140c1e1070b14244d0981010707840d003000181e039040120700800700782c2c2d030721054843c2c54118200c110041c00044400700c1c0300444802c0d04800c1042181125201c40d0002841280642280380050030b0601c1031260099003403901120a401203603d034401d03030303c0c072540700c2408580490300800c0004850a201d410100a0751f81001d80d80000200043c045400c207418600c035801c20004816542c0c0d4995145000b48207002503000782400802100c000c134502000200d94807030040f01c1c984915034564a910302c0084041d600c440140c0e00c80703901000304030054003a80d94414026034000c4110b042c10790125001c40854000d440a2050140782c0b40110041901a01c45c00e04203400b140703040c2c0401003104c0380200f01c0d211f40d4a805010740400504404000011100a10161080340391009200d207 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 639951807 1250 639950557 639950561
    0x307081c03110307180513090317010602070302010e15030112120302180402030907080318192108121005180c0d09050c1306050102070e01030b15040b04061701180203060a 75
    0x1522803403131117810b01c00302d22034440a0801503985850350000400005070300303000c0e241c6c2000d24245d1580411b1500103000550340801c0c0d00701245e50a00b0441703904541200019500c481c0c1c0c4000d03a1405001000000e4084582d410a0441501810741c0e00009410254111f09903c500341c0302e5001000c01140c44241d0381015801542e02c25111800d4074581615030840d2401e580c014032100700d4505041c10701142c1c614000741c07000c0e09901c3d5084c00c0c1e00450300c1c21110302594901d1814540070405060984001e20002070100c9224808501d142c103072030300e0036034a0f441840400f4024139000300c4c4501c501c603551240c00359816000f400c409880c541414104107802014040c0c141c0c0440716400b600c0c02805058032a0000f00d00d52000d05040420100d05017000245000b407507603c01043c203425440100041100410520741184101c00d0b03100712005104081006080082e0360755800520300750000824100e1a00580100038241000344502c0400e410140e54108120078083c4d455080303240807501005080d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 639953057 1250 639951807 639951827
    0x10b09090612012909010510080c300a0c0c02120309030604110f030615040209010e03061003031107050f0409031403040c03060b060720010e0307081c03110307 70
    0x508401c0044007400382e040c00d642064a68010004000741452081c003449107078481086029214100c03250f24090001c4c4508030b20260603030910840b82c0100368002d001e041110700703400320100107503495071000820b0b40a0f004c0e1100d902503c0c13010b01000ca40e20a040b40070b00c01e04005950f5401030413100395020800c542c1aa1009100c00d03120403c950100c98409125040c4594090303800700c2c1c20101c05030240310303158403140740c000d2003030f0810400c21200f41900d51089031302d1401980c3c0142c42e41881401a52031103a400c40b110341c1445940b0030003c420012101c020184c038401d42c1e030200c0311010807024550310410350140641c04142c4c00703144116030030300381d0080c0b0a05010b8030708044c11500e40b00f04800c482e842694141e80c42c19061205000b44070860060581141d400d0300c415107002e806841d40c000000f0046882d5041000040e06158503a120f2000d662100c003004095481c4d8582d01c0140955502046403400402e941c0b01e91104a61030183c802e107804074000314070540c5035035110381c000c584410711 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 639954307 1250 639953057 639953059
    0x1120605031e1e101b020709021614010203040c0807141207050405160206060105030408070f050708010f0c1404080a17210f101410110a030201050106080a05010b090906 74
    0x40e003c4070a00045030300c070102c1071484000040d240c0b0940d00000032043c3d60316214200d416030580800020a03560005404e822640c44100041c2c840e1903001000d00f045801e200f020303280b203d80c01181e4505820650095025a104895200c501b5035100d240607140d40701c9209070003d01784a0500c3d44014184151803100d100910b10540e060507840302c2c0050220f03241503521032008250851030241454040240b41e40040090030082c0c1075240030303500e1034040e01c03555034002d003034500d604610700c204902040034801521114000788200308119032504024280f4241c6400000c410100d900500b002c100216800e481050001d80001d8041da2146c81143d040501d5210303070ac100030010950100840088034110810610001000c1d040c0403607842c01110020740b141540a26800b000c10040d045040741c80c910381d00542d405654000c1e80d450a0301c60f2108624061110b00514608000b00b69041d840300b4103039403d50300c40500c0c9071a03600c82001260024081c1c690714400070400c4000758982800304070390001d8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 639955557 1250 639954307 639954313
    0x3080a020901180e09060a0e0604020616050703030e040c0908120c160e040c081f0c12020301080313080d0516140a03020106050328063801120605031e 66
    0x24042606031040e920f070313102914070040c00090101c003410621a1940068405005200114010034190f880e45030103400248031740000a000c80400303a84043c500d1109401001703890310203550b4200a8007581c80070706001d00c0382d403620b003404c00d8460044107814141d80303a000c01070000c2180c90301440400d40c403000180c80035224841288804540300d0703800034041d086e4801d204426003081d20303110190b040310380c0014a00703030000c00c0924100e01c448a68418040c81d100e40102e20f0740410141924002c0070104a0000c0600000000c04c50000010080c0403070402a03403001c4400740d45800181c0c9400014941500207401040341d007203403a035107910700a087c50040f034002680e441c01104ca6454104121400c07400f6035100c88080195140a101c5005807040d2003044d51005800c03049018164000e40b00c004113880c1c1d5032102910914204666690113081041c5c81c400b6401d000c800c006018001120880d0000300320b541c0400301071040c0d000358130031210007400400003c4175490300c1d6640404880c603280a588 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 639956807 1250 639955557 639955577
    0xf01061112090d1703130510090f260408010e0c0405011a030a0612060e010c020309010210021308070e01031b0f061110150f24080712110301050414010303080a020901 73
    0xd00e071340011801810b0428062804411910304203081c5aa2403418030b80f02894141c105000c500d400508820780c940c0140201c0c800051507052807003040100a81d10040b00c004140880c440030f056000d00310b0b90400303004482d03844000d1401c00007500e50074060400c0d0310341c10700b80002d000813800c8050350b0084611900860718545694801350080c0701810b041d00c50b240c94881d1404610828450154050441d101461401e070203c000030f5910118001c1800c8129400500c00c056000c041c80480050014982903401e82541c0c2c451400202c6400c1c0400c1c5d9944003003a03041040c1c40a1004400200c6800b01c442903452850b010003520f03840c811008c195903a001300c2c004115101c03c00e00c9180c0c249181c428200302c000e4100500d5051181058200005001c20485001e1010040280880c038807070f400d00e0149410796801030225003100c10a8044c0420500f0040501d01c04040301000d117040c1d950a9070204010b460741c12103140001020310000d004502c0c10400302d80100002d0700100000780041c1042c01180f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 639958057 1250 639956807 639956843
    0x307031d160810021905250b06120d1e1704080310060804050c0409061d0106091d070e0702240106030f020901080a1d19030f05030f07051b060f01061112090d 69
    0x4900d0098212000b0f000d0360104155842e10310382b071510044040d0002c1c40107120382100501505546d01c0c0c2d9418403016903407808007840c0303c0e030407130b003100d61030459030008904080c03400b11410b8005a0386000c3c0450f41a101007440c03032048403414851608503000300320031340e0036509000003081940e84c01d4a144d52113505014081444a0350780440b51405000065028038195140301121a00b480c503d17091030001950040d26840002c610043e01c485a0510f2042e0310340f44c10981c0703825111416840318a1200c1c0d1095858070b0171119250403100a0344062084425013851b0074101d2244400c0c00d40865090004a40c08140340d41c42055103080514554001c0e44c0540c400707e150407101003c00091902c1c11304000105544110611901c0000781441c0d825420807441011080800a0400b81040404070340400d41041114111050104450a03582c16041076007201c12011024061000420724000f003030100d0b82c0000888a071003000060400f800c114498007000f80c0c080040e10107130f40b01c8550444003004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 639959307 1250 639958057 639958117
    0x40b1e0c2503090602070807030201140a05070f03090501020c091e1801110c010f09020307060c080d0c080402090603030a090918050f031309110307031d160810021905 73
    0x2001d000c3d446002406151000080c80c200c0960001e45131b6070840082040140d8104000075103001e00d0f4201e080e11185138450403100c80c010108043c04e010301400700b48040c5504500c43c0029584280d081d1740c0d40041034024440f8002090b81c112504001d145921203d121701d4030305940d0000411000c1401081035118140d00355040316600c2d000003030ac001104c20a0210911a00102402d142c40500c9000d0300758000a4954102d840780303405200c102120401000650700449d184100010030400002440b828000c0440070119422400b904413800442c0d0300b45000010390b420b0341c8040d0755a010b01803e241e88000504483c00c0400790103114401c01d00001041840a0b1843c510310400868030396141c2c85003ea011101030703208414a502d4060000a407024000c202e991146c1c26050104e100500c440d540c100d4140c1d10030051480e0300912600c0341961860207503180031a079645040310500c480301d2008100301c0c03083c04001162441506c035000240c60150f000f034510081000a1840b03800c1c002000c06031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 639960557 1250 639959307 639959377
    0x3011401080f060f010f051203071e110411091c020301020f190e13020a110604051b01020c1c0201021c0e01121a0103050c0f040e040b1e0c 61
    0x540c40c0c108502c076101165003008000d42c048145010040c09501d0210218150f0407035006450140c034012041c003054240400441e12a250f0010100b400501180c1c00f1840544801c0c204031844501c9416207c03203440d107801098101449004051b00e051400e004210500700c1e9480703007a060703d8255107000007582e4284050084940e0700d03460959144104d2010803c6845110883c000340f01041c05032410507103d402c425a621800390000580e01d420700b98058030214100c8030300b0350300c03403180508003c02c1150115560841c1c0511410b088005a4008016a01e40c0141c010142e0030081d00758588181c00c0030000300c90703066401030064400c0c03406104a14103c494000b52010080b8411010b0000139580c08550700c00c0521002c80701b0004c5101d064049104108503402d87e50416031134101041e0041d0450f030482d0601d0501d4070002e907032075580700b00d400d110030b1080394240c0b0500d51200005a440501c0c0a00c00001c11a1104043c1580c0d103110381c40300103030441517241d00d10105226000c01301810401c103483c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 639961807 1250 639960557 639960569
    0xd09050f010e070b03010e0a05130203030a020f010c091d06040b0a080a020a0b07031e05040b04090518010506150c1e03030a0614010c020105070503120c12060307150c0203011401 78
    0x1180992500b069286404060b84c40507036052000c00041040c1d146070700700e49400102e91100810117844112940150400d6240040d505010015040f90750940001d8003944a000f454020b0100f4031040c2d4003942c00d842140300e28012a003503038518400900801c0c00c92507008000a1002905080c07810200b0a91002a040351201b03510100c1c45506500e401d114400040c1044c080c02803400b0181d59000300840d0300514003030300260100d91410f000d2401101541d002d404550100c42e11240c0e12020312014102c1034903201c070301d05040079540420100601079544109400342844400a203e4601809994001c619940d217030301802c4048a006001041003402e00d00301c200c01191070342070001102c001c40f48183e006019131050b105140841da6000000c203030f5000c0d024203007142ca0703013107030b05115046101c2c41c01c0c40080c0a02d40e004100c0d08841c40805092001da1090402e42c20303568032014541d41d4080d41c02034000f42844410f042103040d12610355124102c3c400780010501c0c0e400e00c86001c01e403c5080c1c003c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 639963057 1250 639961807 639961811
    0x106031e090c0e0c07031407032f10060e010902070f030507061b11060703090c1214060c0304171213020f04050a0f0c170130060c08091f020d09050f01 66
    0x2105042d41f05080c2006440c680d004280386c01d00a83d000391141d014185075000c40c0c4452203500c0205820007080441c0c503d82a001d48140c1e0700000c00860003852035000e43e070601415000082244c40292080d1540c090384001c03000501d2039540c6081c4d07041d0300001c1e02140c01d6a03c40304072000f85500c090b03034144400c1064941c00c03044080d840030941048001041102054030300003821000ca061081c401080742e107070511903804001a81090f0396064040b9000c038103244907040901142d100b20800a521560051100030011392140d4003a444a1086100300c2d02080c54113004a103004020201e0900150720003001c1242c145e0f12003004c40d0075140d08560540100b07aa4414000c030302c01d4507000d042000315503407518812030030010006400751181070103580303041540c0b214401c02c0b2000e0109065482c006e02c0c3c190500382c0840349413000280c4201050036001858a40208118201c005915515906101c030300c000ca242036600050001d411100c03440c1030103134850121801184040c4442c01c0c11503501000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 639964307 1250 639963057 639963067
    0x1270803180a0c06030f1401031101020a0602190818060a0b0d0b150f0f150702040e123415110a11010516081303020c0a18050106031e090c0e0c 63
    0xc06400c84a40580c0901114141151481640705031f044c0181902d0780302000703015800b041d10040745001034048001308024030002d90b0b0030300d41e80c06403980c2600315100c0c0c0e50200c160761f9440ca1180004208100052140d001401196901085401074924004050814401c2d400c05481f1416640001d44a80c030150b020401e00c910641040d041e103000300302040e12030740030f20702090010070089080c001684034940c4c07000c50703004115500c541040804d203c01070300b207034900d04403c0101085540124040e82c0030342c06c403e07282c0c00140e06082d42c45c045000800010034051006032a281c60602c40c00401c0c450390350b0350b0300421420b0802200a041202103595906103800980c440241c00c48102409110516000340c2490107103a034004c122030790050b1a10841202c8407014a0264582104580550b50112520f4800f0030308036000250f89154510091090050b6607035040242c0c2103aa504100101c0950300d14103003054403941d90040782580d40305aa003040aa0740e1f030046000c48100586244240041c0090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 639965557 1250 639964307 639964319
    0x60d050c0a09140f0f130905060f06090402010c0b28020d060b04030503221a0307020606040605240d0f06030203070b211e04110301270803180a0c 64
    0xb400301510b6042481078940c000781c80020b010406250000340304814000c402ca0380b6031151800c2804465040d4010700039070b0520f10f0a41e4541004440b00d04a250804001621500c3c0c50304903140035a07010307102ca170401c02094036039240c9814014405a000c0e41c1481a030040d0f244407100c1c0e0201481e60324001270303c6002e070304111005e8440d41d0f030000741201c506000c01c1c00440c4020003210715905035200c1c14003594010903200c0924005540c000b140705807440a060403840703440e0340254842c02503a03013a24041e603680320800046584030301405030414071023030300418494452100440c1c4400b00382c10090038407aaa06007130096440030140c6030840e90b1185010400c42c1001c00018026090036101c031810010600d5800d02245c054640c81d14900f4440400b20300c5c0e40707007054002d81c42c10711038500c3e210301450507003880820301c50760b490038502030740c40c202415044074000300309500310310309041d41000d100300759480d080716039080a01115601c10f80501da0190030382c2d0400080b10050300c501c0e5000e617160300d415 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 639966807 1250 639965557 639965567
    0x605150a0f082a0d021306090504020a150c030f05160804030201320f0405060d1406060708180f10020607080f040206070219050a0b0304020f10020703060b060d050c0a 73
    0x250110800d54000e66220f606aa03000d4121040030006580c40c400400031400003400c2c18500a00e80c045041c603140340410000581e030012803081d402aa0305500a6645100948180481184900016940d03200d190b000a2040741400324022051802a06104483c200d00c81c0040165008a8000c0f100040401c215604403129080b44030b000b0302d00d4003600340c0c085054188002c011418045100d400500003207180541c2050303c000e0300f000340410344c4411400b12a0801001034440401040c000301c4001905440d05408480401c0e512039411403d21010a04c80c029005000481e16844200c50f0742201440e00d50082c151451003c55008014508141802611481c8040d0001e044031040a00304030160700d03444c04071901950b05640100d20140041d008001ea0340d00d0350410f551046807000000341d100450300146000b03034001c403100c2852000800400504000e1880104013503005220200080b40450340141d45e01540034141d01e03d0900041290000c446084501503450440403409100c040e41c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 639968057 1250 639966807 639966823
    0xb040801050903190c030302040e01090c030e0607050a05071401020c03190e061605010f020a09052b0f030516060c020c010806091605130603050906220605150a0f08 72
    0x18801941c03400012400c401411403907144c0d0b04083c420020302c2c40040602c81c1c0d0445008007081c492008280d40c64070110009051403040a4001904148200c00c038008007161030b90003511641c95543c030300012840d0a4400d0340082c2d00a83e07000d2080381c42031800510030b0009054160400000d55075a2100506607010f103036a4903502e00070000e4a45011586031101001c0740e4003181d10059410081606240c1a8054500740c003550303101500205194103032a03041221007056501c100e410850140603010800c50030424241d012403460000c0a007000440e5681444e5070b81d41d8000e241c654030780541c00c504140e001c0c0c68410116401031395400c041902c44d0703050240307020301030742441c16078150300b4150002524003901401e0700c40499041d0080b103585901860441d07a03c0b012840b4061102075561a001d00144400c4803a04c3c100e0050400081d0420328502039151100c0c0c0b40f9600700c19281e803941791701009000003000d1342c0200180d48134114155071203c60080080150070981d00c8800d0918200c0c0d4109520303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 639969307 1250 639968057 639968071
    0x611010204030b0a052d06010f0809030f0a090f0b030a0f1806050a090f080d050f011a070c030209040501050a06050d030c0209070507020d03121508210f040b04080105 73
    0x30500082c030010309068402504080000008150b680358880362069000080c01e50321003881d501b9031644c5ca03146e03800300002c0c45490309880c2c480301100c03252015502c4027001c9401e0000c40d04200040c003400703581c00015040400312483c0000c203454940166401c0078190790040003062a012041100d800d41600800000b0601044180400c2d120901d0800c1c0802105e44010702c103036210300c00204259042d910010b03d094009074003c01d64800340c2080c0c0d01c60303402490980c0013c5c2c100b4000500c09001c0d5a80c81d41202c0110564440d50356880a500350550042c2804a0302c400703c1140000c096510742160070f0080c0d0044000103036a0404040302006c451066200c140141c00260720000401e0b0030503040d2407950303019100000283c0d42c0450469091203103002c000e600070000c02e44501071650000200700d5130807001c1004c00a44100d0a01d56210240c14447c0a030f031503124040c0070050840d9618401203100c00b51560782d040150000c0040c48035001504421144a00450708204142090180703d0308200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 639970557 1250 639969307 639969311
    0xc0603020c0a0f060e030a110d03050c070611130312030e0d120209120607171f0303050a030e010608010207020f190b03091507030903020c0a0f050f0d08040807061101 73
    0xe020a1650b0701c0e00b15500000c0c10703160003540200700b0b10441d0f4005c0089403030741605596480404110140c81d082108508080758441c0e0f130107000c1030701d000380b0510340524001d0040c5030502034030307a0f514000707030042015401100100340300411404034040c0000f00514880c0000846446003820001c089500c8004443e200c1d0b403044a4000b6016045104500f0322400c54a01698600901340490b07640c1d024031042c0704107489080100000e2907402400c0420902090304040d0540d100c14070402002a000e07114102c0c1b40c2180c03101000020701806c001c080c4011079003008100703e104002e0301403c658a40e0b0140340180d40000b80c00045180089040488400484000c4002100e4002c1c41250803504d010b00c0c480d10200002007031071800104410164200280a0314245161541008001d002404000ca0140c4030b0003490340b00c5442c01a00d00811b807503500780e034040f41514000c20040d69940000ba041d4005681d40064070104412130020702c05028080002c08456241a900911241c003d541010680e4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 639971807 1250 639970557 639970567
    0xb0a0e0d08222d38040810050a090b012606010f0510021e01020d060b07120e1512010503122d0909101a130b0f0408030d090c060302 58
    0x412409400000c180116280080010108140e04039000107600214503251141c5045151510a90355948140c001c150640c00701c098103200d104c8441c092801003514a4100b15881d00141056034080365128003500b03c04280d100241d254541c84810070b8101000342d03205000011100042d03c8200c208180402d801000345615008055412088a0040e288242c041351540690307144208113510600d6028000110702204000c60705000358400302c03079410b42604054000846805010941d0b165580207003542e441d0741840281103a0a43e0130429113079008007814003480c50703540008050410b000728994641c1440d41001708140c90315014076980081d00d50b04001e48405500200e9658401d42070010181c2c0b0110214401e00c42e0b40e004244c2840d800c130300c0a0042015170071201000600f141c04003401c29143c078100d0070490400d0301c50b038407403488038600c4402c040206075126001040c0440e2212145400c00740c8400030182154011800c0701c03049a2901d5100080c000d664038404000c01940c10214900 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 639973057 1250 639971807 639971819
    0xb1503060c0c0312070522060e0f0604150c02030705030703080a0e04020702060a05030a0c0e101b05070f06080f10060503100305010c050d06080c0a0b0a0e0d0822 71
    0x4240c020040595000041201030302e1450800c1503c801840250701d401c1d00b031408401c020401c1d0081c02d903c02d040c0d8901c122186510401411401c1500c01030340d42c0d88281003080c0240000c8004442c110394101c90200b000050b4208030307040b01101000940c0e41c004840d40700d8010585400e02c40d4000718829000031000b0800104281d08880031001c29003014517031480c213400061f00030f004600303010f074001c1c0000900303940c801d5001d0f00a511516407403808110b5401250b9089074840c1d40742a8098000c4001d4004101d4240541e08001040380c4003000e031014503c85d943d0740c90424269500014801e000c100c40dc2c0000d81d0808202903001504004030841e5140044490a8000c03481c80380c4414044000041040100018916000383d500710000384500c04116000600c903034001c2030701c0000079146c40b00204440c41c0218004c0026940201030035105403c1c803880959641c40349951000703104482c00d002a50780c403088510300c5003034001c5d0507081d01c07030340c0d202010f035000d85140700e2507400500e8050080c891 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 639974307 1250 639973057 639973063
    0x7031e0f06050a3f230d03110d0e010b04140601020d05030402061b031b030a0e010908060615070b0115030b030a020117070c1a07090f0303020a061515020a0b1503 71
    0x3c0000fa10b841d001c440182130712410461012680050b04d80780c241d01c0e0388000015800403004200a6842c111041c241907a070045040340c500d940c00c0d10b140385003040303110902901c2c0d4100c0b416881080000040052402c800203040f900c84808001d400c034106c1c800c00920b581c040c00620100c1003e400e0103851460980c0c0080d24510504004d4807416400001240c8809010000c5e01d28450740d0806003041208110380c0c03980d489e0854140840090804145040154846c9000c002103514880c003d0a076500c908081051100540894106204041c0001001310f11001040e80c02404003e16001c80d1242101000301915084080341c0d01a078020b46201c00181d038008030707540e070103c882c40004c00b090b186e040e0126481c4064440140420b840c011f0140304245a028405010b460642c845502c03440c7c0c0c0d11118003a00030180700280158001c09880e10108403103030020700c0c803402c05241d000d41d03194480744442003800a510040340140c2c0440c420301300f001400340c20190000c080040004c40c0541c22b40000359 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 639975557 1250 639974307 639974369
    0x5010f1205130b0403020f120403080d02030702010207050a0b0a0606080103020d0b0403111605130e0d0e0102070b04060201020a09090b031b060903010507020a062307031e0f06050a 79
    0x280141d610000504101111204030448a501c100c40a1240c182414025600d50601c03680b98180d00514195003050441e40301107804803548102c3c03ca08080011541e04002c1d000240b118066540030004030740010400e2204000709481400d9030786490a16400100c101c5060750412001e11000f60f00510169864001c8100c034940d1100c4404402d40c0e0700d20701250031b4070941d13051907080e1040280014450850034283d00c10b8903000e88006d840150325102d440d01341c404400201c0b02c2600001c07180c1c09000c0c4030700901400502d060048880550351210508410380c090781c01000183d41c08503c0003041c603406034624000f0403142c10180008608000081d8480742069900d0314402c1c1007600c3c0004540f20142034450080700100204810315080a000c0d440303405000048a82914110300c03036440d603500c0c2542e0070441e982c0990f00702d42c0307039102ca006030010991801030200e10b141009074024128400d003d1104050b2030000042150351034082408041102d942243c40f8203c80f0345c69000c441484403146034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 639976807 1250 639975557 639975587
    0x9060806010305190911130e2103070c0809130218040e0304050418061a01020d020f0c060306010c051e0705240f0c010e1e16050613050603090c01080105010f 69
    0x1c0d1190b482e10781b032006d401504d40d089400c05040400d4900040e001e80c44081d80c2c80e42481039a50914a50185041d012440d044901050b4001d00126100700d00c20350002c1401da01c540300c80b41c038000d0300d400043d01c4030030301482c01488240c000a00c148111016415484c4044007900c06100075000c0b640580e1f1240600d0166a0281e992202c00d921044a0b110036040c525070072110402007900d80005840d04550540000344c00740c41a0102c0201c0148002030307000d103040c1c80300c0113040301c66019010000c5546c0007900c001d04001320101c03240e000c0b4078140440400003003e002560390516805520f030b414190b080d40320a00c202d140150344414804040820858064032080c015501e43d10341008403000c2c041d1004d604410740c40c01517510000301d40090005071010200c107440141e4807a210381030f0340d00d40740c1440342c07004810344d50350801050030002d000e0700301c46500144803030009445002288181d0821658520b850780100e40b00ca482d940c00000c0c56001d45028039001d41000301007a8080c1002c0d03401c0c1451 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 639978057 1250 639976807 639976811
    0x110706050901030612050d021203160e180f010510030207050c0d0503120a0c0306050609030c041a04090305090405090303091c0e060d360201030e0f07060906080601030519 75
    0x25008980c480d40c81320707002e490750902102c42c154240c14601e40e9500c8914403080507200380c80002d0314880501054034030413201441c0869040002440803030310500d403d0383d183d4010780400c10f528000c010140400344590841c02e0308018544c03502041014040741c0003200c1c82403520401c400404180e020a10383c2c2111825640440249107600d4468503520844105c120410841d50900070450403980210f40703034003025503042c00200d07111000c11240d8421905400d6150f4402c280740b002e03600b05a0012905121078104d02100c074041d11022a050ba444440203e000600000d6080d81d0791416118850300105003000075400e40c5000e9100320754a5824a80c44200b0b80d14020441ca1003d10941c81050031481c0a040c0645508030035480b040980074040c500e6801c81c1d2138030003c1c3c50766080340d5107014181e030030100c10742e20490740d41d0010750040045480703040c1c1078002c030790340035425080030070001004140d10340e140c0c2410b0b40381103030044c6580d4024041e00d04060808e42400401440c000c41d24513600c03228800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 639979307 1250 639978057 639978067
    0x6090a05060f09190204030b07090801020406090323060a020d452f0f0312090406080f0312180d031e060b0a090906180b060d050a1b11070605 62
    0x1080c43c12081c11507444c200070b800003402104200302240802c3c042c440a0310381c1a070706138131a04038500741d01a5028880010f41d8180c01003000c030300d45070400c140180c4241d51110a0200d010b02003814280121404115a03130000b41c0d84800f000759129101038060a510b20802108068800c1c009000b80c100c80501c0030300034001e55411405009094400c0580d2007055403801c3c0700c9400c0c02c1c0e131071307000f0b941c1000302310f481c02800407001070030300ca9140351100701c00070003414070480060307054095600400421500255161404144203901f045079401d10031041c0001d45d150440c4100b102042c8100510400390240c14501d840d124030b000050540e000445810003003044960b03810381030203071039000015000107410080005140d20503000189100c0902c1d07500c06600c19224460340059038000c1c40b481c02280401c8100007000301c00c83d808825007000c010070756490034203003080e40b0050324820b40f108806155201ca00d0440d40a03824107480c4611502d046c05050f04803401c480945800392441a2824010300241e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 639980557 1250 639979307 639979321
    0x51c0c05010e03100e0604140109030e01050f0715060306110f03060637080c0a02030706020904060b04060519030612030f020705030f0105010305210a0c1e0b06090a05060f09 76
    0xc00f540c4c500e0810822469003a203180c55900c88064509540500400e2621032581c0410700070301100c43d80503140d038140a43d2140044a00c1e80c0100304a5161120034854800000c2c850032034140740c00410070b0081941419824010300b15a40208002d1140c0800c201100601c82c01809882d0b0125049a125407100901c5c000b0b00404840095600360070440d510024901c4000d0a88078039400909680d003407819503400c0040940742c410b542a69016034000c2c0300e2040060340c6a0003c143c0040c0c0038001181c500d99400f060080c031341054010f01c000c40d0012031404c503410054694511441a585001e21100e0b00e0255404243c0305015405802c02040e08003424080380200600b600504020301107488003046064041d0087c4404e000c101c4960041000207203008501801541c070314881d203019240340c05180e04d001c1e00d02d42c850b13600481c0c0c29803408031b20064400071107414002c000d00420729000710b0b03e092410422904802864000800c1c41c000c240041c42d201c101c031408841805407080c11071a00c0743c0c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 639981807 1250 639980557 639980563
    0x1008150a0c0504240f0203340605250206190b0d1202150115050405010c0303060b0d0b011701030c12050c03060c0903191505060d060f06051c0c05010e03 67
    0xd000000d05132544c0b4a2005102000d151164000d155996000094440303e4822030310b91280b444448170001158003c81d8020000c14204030001580c00c2d00440d018030790355100404d80d04200c4101020494268070141b6500d11003180040c204581d10103003a051034401e80e800024400004040ea2a0b96148200c1e500303030301ca62a1540c0015000003400449030303c0c3d448000c1d50b42c094003140384610601d08000041d8403103101c2c241c81c1341d0a05a103a140c2024200401111076140200041d000c054451f0000521703681c01341c00601e05a50f005030b01280307400317100700050044803a40384c055402c2d40346500104003280c807010031038003030341d5a0800200c0b048009041080c503040305030740c075180e05d40110814042c080c007041c4000c043c07117901034040e9940c45000c1000e00f207075610814000f40951188800c9142c030740c00c1541c41103500c10320007003283e5184030303e41c0c5a4104941083c2441d0070103c2c1d4410f801c4c4040d20346089003040c1030780701c80800a021401507a030301130381c8625440340c241400400081c0002079031b414 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 639983057 1250 639981807 639981809
    0x60b100c0b16020f07090606110303131b0e040803040309080f0a020609040b06280807020607050304030c051609050c04050607020d06180809090c0703020c1905030706081008150a0c0504 81
    0x6500301c8030015206d41d401d04c0209450300c074503030105a2140c3c0c0f040c07d6513000300589100303085070b100902420500d611054490400c1504101c035840841101080840341d0954040c00b80c0e00408006440346880e140251030301302c0d41e400c018000d40c44510f60040c010300000d42d403981c0560589055031180116404038016107124120f030341d808007002c81c4101c220110000240c00f1248080795018031442801001d8400c82c00940305200160040000101014058002160032074400c2c903003d965000d083c1c6442c1c1c00c1480c60b2200c412000108002048aa85075000e90b580061030f40400610781447e01000541500c00d2a8000b40100c004c03103d003105203c02a400710386c80f125050001c00300340410f807412003440d42c00006014420401c002c040b0700794030b0300a01031310075055154005196820f0982e042103d079200f00c2181c0009203100300c02c00b140b070f030b102880004010419078507480c0f00c609041401640e02407140d04086020390050035240446001801079a4100060000c009958001d1840841d414455 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 639984307 1250 639983057 639983083
    0x240102011506020609010b041b0507020d0807030201090605063c1f030c08010608010902031504020d0906050c0a0c0803070c120801060f03140c1c09060b100c0b1602 72
    0x800000001e01e640c021420b2841015010007c1100d07040c0703103040004444100c15007a40c80031025a0114070716000f900100703507290005204001ca142c141c1e45844583c4c1c044035040340142d44031469201046658000d59400c1a400c80704001300d00d51043d8000d500004030305031030800350305804a400068200e82034950103010301800e5030008094a50311400d07028028078100d00001d180c03114906400f40b0800c2da2074140e900356a0760418503464082c22002030742000e0301c495103070f0031110200c1d031203503a0b6840101a608203000c0d001c9404841c60070007404075103004201d415400c034208000300700f681c1e02208003002a6806544984c0782d441c0c1041c101c0e07900100d003400078855001c000c040b00c00315800140c2c5034120780c0f01d40c2e50070b058848941e804a058401c8002c012088140381d00100c0d000300e50b14809441c3c16528002c2d15820012010100c60969441410a84d6401e03983d07980c045803428000b8007030700c111a046c101200e1240c0c003541c0d600c0300984010942c40298500220000b081071081c0720188040903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 639985557 1250 639984307 639984341
    0xd05090a0915060f050307051903020c150105180114010503042103060311030f0a060f11030117010c1407020103150b030f0609070f020705130221041a24010201 70
    0xa006082d9100400d5074015600403880813002a03454a1084049a00c654181d0b0740b06410540350b50301502c000400080c400c0305254007030101c502409020410610031582007400300d24954504401e014081c0281c0740741950070818107005100341070390010107002005082c41c0071a038998450900b0038581700c1010a03070b03141c034880e00ba03030b460340a40c0341e005003050ba0300800c1c298054003150302c2090782e150083c1003107604ad03400080d092404a6103640c40300e01e031403c00c400081152003890451810581c40dd0b0040b14400d400d20f0f21450421009224040ca42001820070742c604110380884c1034601c2c0600302d0001c1c10141c4500324046c0d8015403403034140040000c0080e203622814925140d0120003c00c4602d81d00030303800c810018415601c078001842ca800510303009404032a00703042c203002002d00010b200c1d010390b035003c1100c00c150780d4400e08400c40c2420080f04811090406203081458000c80c0d05507110aaa245800d1040d980c0365281181c0e09030380c080106a108110340e0300145c0c050201d01910040e203035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 639986807 1250 639985557 639985571
    0x602010e2104081f0b09190e01020d09051005090102070b150d0210020609060903030c0f0d061d013201030c02011b0f0905030106030b0613020906030406020721020d05090a09 76
    0x21001a488400703a41e001d01c802d101c07105c55034051000c1030384100c0b11b0303142e20680481114140c0c0303d15400041080010310025240c0f078111078210040d159843d10498056000b505194030104d907030710481e5003155080d802940740842540741c0320150600500842c0480c002d490105440ea03450f2180c00c1c0089a025016a101d4041c074200a5190003045400d001103010350380c0002c0c419840401100d1181c100d03505120308140991001070701c145c00c0140494000740c1d90b100041001034070301d11300e0541d0342e1000d000000340e907040007070409104810000440d21584100f03014003400d141103150080046082c1f8001030304c03408400c42240503142030006550a0f00503400301e000c80661042c048280540f007600c5d07404a031070303668040c10f00720b500c00c1c0b0000c2c000c01c104c0004a00180342c400426a8295459180503081c490500300240b49503100307990880740c040d400a9a81e0410074017514001d64680300714206042c0d060b03003000294541e03038071310f100348108900012141c80c0c030f64030725140340007030065000208102 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 639988057 1250 639986807 639986833
    0xc0d0602030a1401080d05160c290f040302060901031d0304061407080a0c020102160b0406030e0118020f15040308040e18070b030c0d0f150602010e210408 68
    0x25801550107064041c00c1141460084001c3e00380c1604071407400008000204c000f060450701d0360400e0300303014034034540d052480c03000c10a109100000341c841ca0000d2036542e002034842c1d822800c00c1d140c0d101ca03007100c248184050200d160040d14200c0f41c05849007507542c001640101c000345602d050300c01c009900d0440c1c0c820b00c07907400005801581c40c01d807508181600700d0100c3c805103020b14074009000745000c00003a8001d40c4105001008284180111580390070590b002e0648240960021508100041020060140d042c00359810b0419064000c20a0700c1807200d000944140d0030302d0182c060103140c084c940041d21440c804400d24480300c00c5042d1202d03183d00d01601540d01ca172040a4030400c408012070300d100e1004a030703003080d41c95140082950614102c0301e1581030304024065400c0d428140203164103805940503088142581002c001101d80004010001c0000f091300b041d011685080d180003044c42e0001401229448100104080300f255200c00d1b8210f0b2041e60015031070390240c0300d41440a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 639989307 1250 639988057 639988061
    0xf1e1003060b031f180821010b041508191a09012c0a02120106030e07080304061b0602070c03030207031403130b0309150709090e03030105060a110c0d06 67
    0x240c03441420700348503903440303401015910108a840000560252030209601c09619480021080885110b212040100b07444404013508220b41484240380b0302010140e120805100d01ea01429500750894182403c004580301e241144250382d10501c1180300201d01d20500b94405581c040201610500441c440034800d040c1070080e410302d542c040c822800001c10003050040034146403100d9004440420705596500c08c11024020301703000d0910740d0800409080380f910b0405c281c0079024944001c110304000360044d62410000754003c50054200380300074044036502c491807904190000310074441d840c0c140c1c00c02310000d206089d002003c0f401408000001c041c1c001c030780d21086a00501c2a603e40c04a01c000d490307160301c901d0a00c500c0c1014000d0741030240c121940b0180d90800c0040703040305c030034603849015600d640d00d0680c1d840000c07c070b484a00f00301c00c15560080310040c040350005103080d54905004140c05009001000003840000a50700c00700300810000542c13189401026800c007c6114146200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 639990557 1250 639989307 639989309
    0x1090207232d071517150a0f031505040804120201090e041b080c18130506180c0103060f1203113a080c0309030c0604050f0c0312030f1e10 61
    0x1d990080075000940f035455034030103d203d454a0346555144100841030801030340e10080000000741420041b06c0341540b9030740325135405800404100d0f0700842c1503080c10140142d410801100560620080100050b18103094030100c81c81c445c40e50814044510044c0e07840d9040b80c12111042d034182c82048140103070707404101050305c500020b403000240c440c110141c9656800a1483c6c0000010166100349010200400d03800000100d01c0f603115000e91f076526051034401e444445c15840f5121085000400a01120035002d000342030401c80b1605e02584984090366600c42e0090381199a0442410b0500442034000280c01c440107607a00e0303040b9420640c001d46001c030310000031201042da21a42c1c1000404d05c0cd1184940c644481c0001d6881517900c05d03840d48010074181907070200780562841d10200304a03181c022803194000c2c000d0b210000910500d4510002041c900c03c1d482003030b45408040711a403c581c2c1107a101c0089410315650710612401c18ac03c000d080b084800300321820040a0808607120700 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 639991807 1250 639990557 639990643
    0x50606161104020403080315040b0603071d010912060b040c110a0803070c05060f0f0a02031509040203070801020a081b0301030f03030c0c0c1511010b030304121a041a0109020723 78
    0x2b10301120300d01030000b180802c07503070070012949551041000c070b9004241003440c080145090300840f40c80301d021142c0b800c4040f500700c5400b5110306114001e81350601a044082440e440c1c440442e010001e88113568003008800501000000800b080445228110803003449400c00c084031028100031205008610b01241e000411100140205030142c004d0300071603005400001980005c60f140e442041840100a8412039062046140c0002e00366402c1c0068040e040c0c440d1940e010f0707440e104068041ca070900724150310390120100010700c0000d4042c41c681c3c100c01c0d0149400548040281c03420f40b0318030040c81000d40116000c880004000b06e4032004003080842c942e6481c1c201c500c03000d2400d803e07954150221541a0401d11043c0f040b0f0b484040e52101c1c9500400c110b80002d5000c481c0c014009500f502d003a240c0c0503150109640341c800c41840c582c01091409011480c00c1c03021344514100110030084007034007000c160350800d412101000030050108001101d42a1034082c001d07a0000f442e0388072141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 639993057 1250 639991807 639991811
    0xf070b091506040b061b0c040f0213050a06080412030603020603101509081b010c060e0105060a08060c0403032d030b030d0201051b0717070f030305060616110402040308031504 77
    0xd0b06800d1500450304440d001810f0703d8100203101c41c6092486001500010303140c0304c0c14070b181599694034041c09180c8541000d00503502c008500c0c00c076921001580000340590542c08003081815403060360700c2d5101d80c1040d900024410031403c00ca026002590002e588503001000703103e0506c0e011281e500440b080f000c004070b0b10081d2030b4401c2c0c40004043c45038056a400500810750103003904401d0341c060a005140c00c4090080031781d21441107a0407154048890703950382c01004110704000641c0b034041c040039001040207160a0b9041c2c20395204a0100500700101e90154105900b041e0301c060028001070350034907040b15444080100140100d9894030320030700c50b80158541050041c41064001c1c0a4203c1411220504122030000c0b580305071000c03107908904101c0c01c0c4212801b480900b03540362003000c2c8074002d10598140141520300240a89125850401c629085404081e02c2100081d81c400321401c031000400c40094001d0080c3e9101070021100042000212241103031046070300300085800b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 639994307 1250 639993057 639993061
    0xa03080c0c0a1422020705070e0f01081606030902010e030f010906050a090f11010e0d05031909050108040f0c12150f050403050d0b04180803100902090102030d020f070b0915 76
    0x70440c0d4540ca80c8880350001040c1000420701584d406078220007079600c40c000340c90315030180e444600d402d02e0350303001c000c4000c0c2090601c0402c0c0c0c1d103d41d0b5107004100c0c0000501e04496002c00c10302007000644201c138107040c2c1d2010780a04590040003070b0014048003d040e07a43c040b007803410050181098200444006240200062142103144168413142e600601c0100340305040c0d035035840c1505004c103807044c188008040312844a548401010000301d00ca0030107942c40e0140766800f0b512904a0801640074095031920900c0566803000340140c4c00b07500411145100c2c200c0b03003028031660b804d68005040c0303071001c0c042d140103205924400c01030103888982e08018420000303108400703c910558000380082e03401c0040c0d4400102a402407032041c04000c0c80000c4511002101c01d182d5a0382500480343c0660110402142060250711800209685902949404401c100007500c9202d1803c070222003c2c0d0105402c661103c1c0c03501a1504158000c60391a201e0030000ca40341d682d0000314001e45800940c01d80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 639995557 1250 639994307 639994319
    0x30f0906070f0f120e030a09060206150d1214041e0806041e05010209060301090c0219020907180503031b1903050403022b112103040b090a03080c0c0a 66
    0xc0e80c4035142042d55540b0944021000112505502e101c2c0c500c041c2d42d1039205d003040c4003005000a10400c40107454a4020601e80000a400e25070001c1040c010403101c2d4550341e02e20744990b00c040b8403942d4842d0b1161a1441704280075240c50004042c1e0b102c3c00705000c10f01090040028000701d801051900043c0c5016030f840d01c1d00e5940f070390212030051200385200301880c152901c0d481603e171190701c00c2d000541040210003b01e946034000740d00c10380080361102040080f964041c8105044400e91050110800307034140c01013007002101820782c508005602c4501c2a0020307102c036404010304001010380c0e81d07c6040203500809102520007807102d034003c010303060306480a106225810194503882d8581080c0c55a0200b1621074402c0c901c034524500301150814102c50864081200e00e0b1060082c10340703001140301800a80b461144039070800810310340350000d2010002050f01c040301d008183c4103a42c2c1c680c0341c0109082c509a81e000500e60080411101c18281d00403130002c0740351070261078018410769105 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 639996807 1250 639995557 639995567
    0x10b3f1f03080d230903070311010203280906060305102702060d110a09090b030a051b01091d01080d080103110409030509130e010c0503060a06081506030f090607 71
    0x3210080090508101c07690f80c04890b030b080300c00c03e01c8074150782c9008408a1405a040004101c4a11070a504002460410182c1141c081c0d1940c20b41c141c002c500b1850312202007403a511100902c404500620f80340000c5805042e0840400154081e0042c0600c41d40d91034400e6503441301d001c550703400f01e007000340711401c0c4001048110f4002e0017004031504241015028040a07900c242003409005484003000401c6818000c0180300860300c1d551180c075011f14000300c40080700d1038443e80f140310340c101000c00310201e4400208031880e0018401414585802203006a401a20f0b0398020340600f107500004901d08108221494100d8820009481401c5165001100d0390304007400010250300c02e000d002074107400c2644c42000090306c01d0421625040942000500c030100c0ca595101d521900c440da0100c83c1d580c28060014a611603003000e90035401e1080000b00020014050346080002a000140311203106508050700200c0c040c100d03690701e050a9800b4142d415080720758610900c10800842c801c00d00c95 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 639998057 1250 639996807 639996809
    0x20906060c0607051c050711010606030c0e06030c0c19110306060a1e0f0b04030203010b100504030f05010b090a0506010315051012150e0f0f010b3f1f 66
    0x81d80644030742d56441c041940c80e078100091804000d103124810801982e920311460f80a00629280e0a448801c0c0a40780c0d420344d0440d401401c20075003400429610290020428940c1311000c0b50026200d9603007050015841c014410809028030520007040322800b22010600c983e1401100302480c502292400d042d9074400c1a11400d40013182303018200540980300c0040b40385022140c144105e1141d49007000c41500c05c180c0c00a0480c2d40b000282002117140c00d22a114100c003080d0740c03550b06690b14900c09131907030040344000b404804224412004018080d0b110b1881c10800a1061105080100942c40241011514140403a20f4541c5820b180c0c62080ca00104841d40103022440300178248001300c440000c009400c1c04040d880c1e4005400001c084c825100103003c84d0138202c0f101d890013181d030f50001d545c041c1001d03d010102c80c0050004031104000c540b0b40c41c0011440021001004084000d0280300110610104880e1009201d00391140321075980900c000d00d80c4548040440c102a00803140a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 639999307 1250 639998057 639998077
    0x117060102061302010c0f030809280204021605010f06050f04020c0a081b0f010903020c1002070b09180405070602121312031b1202010f18020405190f0902090606 71
    0x2c0640007500c030700d41c2e60401d004024810315003c07913100e00a9a40d204006070000c02100864920381c00c100d1000400c00c00c110740e4450a51104004014041c1e41c1e11180c4049440a030080d5000500010856140d551400c0005e0388036008200b03184003045414000c01c010700501c0e10541c2d5403109054103180038025200007402410181c42040003903955030b052603000c141241c0c80013802100b0b041d08030205100e0700782900340d40310010078070051601c0e0003800c186060110f607215002c032a0003003042030390004804080c0e07094550707000d0341d4400c0080040c40c0c0300070142c11880c0165518081000f0480d0216540301140e81980803142140e418005000041c0202e903440b62040dd554041040030380000f229a01886009061180d5190704420420024003805101600c2c2c441d01c8032000d0300302550900c154005034499440802010417240c0034965150394600021b8412510303400812591080662014410a00101c0c04c0003d4080700130941d0181441c10016882060307504001245810480e08030b82d15408 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 640000557 1250 639999307 639999313
    0x6100503041a04060605030708010509010b0a03080d02033102030f06150f060f0c03041a040513021b010c090f0506040f0608070c021c02090619050f0d0c060903020117060102 76
    0x51040c20650742c0c92030003401a90a60303142c2d4030004080d1024000e91000d0480340c1c0010465243c00285182036461b501340150160080040800204010b142611407405600c00c01607565103c80b0090401d50710240107104034491140382c03040c9074440c08a50080164825410b403188005c90340304803501c400c0304072070540b014140038007050301624100510690000004052604040c5902d00030181c60f000584410015440010140185000b041c629080620810409171401b410030b80881c58100516031181902034012414840b04c1d141c00c4034040444004200070807032030108100c020030000c401d00c40d034101e80e00c03100344c0441c017800c1c008110740544045444100119183c4030303048030104ca000700b132401000103051440c401a40c512880c04940c0c04030300d0402c8410507242c01040041c0e0805000d69104a1101d45220134800801c0300d80310440308101c88110022400324042040d42842c900010400c001125010034080d80064040003528000c1c0e07542c1c8004d103140050445150030945046016034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 640001807 1250 640000557 640000583
    0x72105030426040603021b01110c06090102040303120207241d0313140d0b1e01210201140702220c090b0904020a0e1206071b0f1509080d050610050304 66
    0x130b40240c004202010081110120452076100c1c408d003141c4111704070030b00400b400140355080400c1040f03080c1c0c201840700021490b02e840c41d500904146401d481c4140155000316200b41400014221100f06001d42c42001c2d506882a0906ca401004905a400402244059507441c400b100105490724000074401c00040341c2c0c18500c200c20400040d0410300d52161001c1001000210700440680c0940900405001c60004150081084d50016001413980c40c18852071245074403001261614143e03020300308015500725403100e00c04244104c0700080c2d0000341100000b18041d038074550103011883c0c1d400c3d0030081d401d0a6002254241141e1285150588050043c0180d9260560003016081444e04101d408280340401151744020640802401c1d600510200150190070480e000c003201c05d002d80b41524003206680e840c07000c6023030480203441d02041d04003640751030080d03074004c4030300d1b075002624246c5803410000300271f018010441d802801008586c810311845070180c029203015562003010a0911 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 640003057 1250 640001807 640001819
    0x180705060f040503030d0f0b0f06070609050717070e09030309070b130f03120206060913032003040e0702150114040c0201091b03111806010507210503042604 69
    0x103800c01440000c071120308000014141d5010801400b020700d82080100d00320703081e0b484003070486501281e028000e000304428884555121000c8421a55126800040f03507042414528640702494110700d2040d20411291000a20009218070032124403103000202c41d510746002c00d48901043c4d54030130f195803164109000c0350910b100a0402852441d0303c03440c1c21030303455850403113000a40d40290381607100030520003451a41403003a241d101d5070a6a0140da42d003048202140b0480041d1805401c01440e10540e135520381c08407000300b41d19803030f8000304e0391165144c400c1850078000654510026205665002c1980c00805001604032206500d540f500030340c0000c1400082d10040091a046540c0d40c030a180c0050754241c00e0f0701034002c00c161443d25140c00c42c5003003542c90400300e8881e8840e000841500c40c041d01c1c08016a03a1164003881c1c0030b03031111580c0c40c4c4448646008603d0346600c44c0141c50300c40c10250f014000c0c5202d14040c0301b0203007002d810480c510002d189802810030031800c1c10403040c004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 640004307 1250 640003057 640003069
    0x31606052d0d050f0709050102101113080325110409080705060103030504170c0d020609012001020307080609060904080901020f0729031e0a0b04091505180705 70
    0x1040c0400006a59030514000d00d0800e0791294000c0c680d51079403a818480e1300100701d0702669012801d07080c207401080c01c0c50f00107542e5040c1c0303200d028119902d8446030403401d6042d400390380480030f0704070000300a00c0e15002015104d800030302c06c86860040b030000954101a404502e42001c58108601e0000c0808580601001d000d136904165000714042001000242c4100b100900860082d070368140c4942c00d0400c2d03403a18282c100c0300c440046d400103d8148490741c2d080c40903070069904580c0700d943e070074080340161441c3d041c44413030181a10780eaa0004c0441c50040d00290b00c18070917075440c0303017140d598101005902c1c2001d840c09a00035043d1b81c00580043c114a0003004201814011103624510b000768551070320380b4680000030f140140d00ea100c40030400101c01c40306662000400035055140130f400c110804108034002c00e088081d140041607000b6040d80c80030b405840080c0092040e034040b030500440c0200c580d0140070b01585003100180e00040910b00c0e140c11003040c20040d0450500d0302040110b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 640005557 1250 640004307 640004347
    0x1a060a08150609132406021e0f070f0e0a02030c0a0809120c070810022b060b0406030525020a0b0903040f0305070f0b1602010c031206090b03160605 65
    0x80c0020040000c03c00c240d4500296603084a03400101082c42e6660245801c00c03203450302c82943d002000c0250501c9000d0700403e281061640a030329034452041400c094a01d800e095452008080c01003002c0030401c842c500840509580841c10100c0660720f4102604040344021515040c03098018840302c40018460300c02180c01001c800100c5401c0c05032032900302c03a203501400140c0d02035440100c08008590080c803a554610341d80000450801082000d149086d03103407400241c410902c00383d200d104070042c0c0c2c0e100d02d000e499070200072a11075480d40c2c00940240025118003514101e0041201611103030710f42c0703428104540303602911010800d03a5802d10040c0740070f426140503020609c00403980c24215107020307000b54010401003507900e2070050a480c280305250454031740a141000a40b05e21081e020080704001d0303080c600a1010300c024202200c020614004480405040c054002021802c5800c00d924070300040313090310001c0c404041140030035040b82c0b2a10010820601508800000c2d49480311 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 640006807 1250 640005557 640005559
    0xf0328020a0204023f1618090b042f1806070501060315020c070b0702030a050106090f0b0f030c0402031e0108030a1d011e0e040608011a060a0815 64
    0x10714a41416400a001d0fa007012102c05c0f0f901030b6010301c0ea881900171442c07a9400b811425030501d4a0281c124105100d02c3c070007007803440144040c6190302c442c14480c00800280014094190683e19254000003000d03000b503495080c8628140000b40c40c1d902e000141194500c80c40b03e400c0040c45c51508490b201030741204100c41080c0100c82c81c2c40c1d155803180700c01846118410000041c0c5241075140109012840310411803800b0f1041c403441c180707000002503000c2a21401215180c981909200107407400108900c0101903509000000800078559000a01c00340041030042c01245810810b000c512446010300d564140e000140801003824242d0045030041c00e000050301140c40c0b032940302084c0082c00e03840007600382d20015000c0045039110081030f16000020400784425060680024000381d6401800e902e04065000700603d068041c0c0d07103102060901401c18003a49590760500d60081c0314601091150540301e48408104e80b80860484100d2203c035150840c3e55101c00140d0126250001d8600b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 640008057 1250 640006807 640006813
    0x25081005040908130e0405030306012a060c20250812040f0b070b0703050712090b04050f0d05030c0a02010b06041410020127020307050a170f032802 65
    0x49040d031182d01914a000340100b800c41e03a1050341c060702c00c0603403100703601c221020303194101800001400130046a0304914240307040740b020f1903004048808a441008d813102000b0400a02038100103c41c0c0022908080903190031141d000c051010300048114084ea85002e600100c12041462106c2c58a043e9041c11000381d0401254a0b00403041c640903608640721001e83c0c01186c2000315607901d50420019044a003141410585a6a01e4182400c0301074040c0d07080c1600c41c0300081846110f010030810491506000344000c070300ca420305001088080da8140c1e001c1c000c89032840f1241c0400128045400455078030103207955690f841910658000d21071117800c6540b181c006149640d40c400141c4003a2003403268001000940a041000802c00c00705900d0559051962017079000305480c00301400b41140e01c0240074801080e03c0000c1c100040794019580c000340e00c1d20041141581c001c100ca0100c40311604848840b20348289440e0789000d070b1030441001031440002c000506403081062001c6007518012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 640009307 1250 640008057 640008059
    0x60f060a0e19063002010f0302450303040e04020d050f0627060f07050711060c03030907060c05070501140c0607180603060f0306020901021002070b0609250810 70
    0x60002d4840a90280c13120704a1018000c0b02840fa07411000c100e85160120072081d881c1650005c0c0142041c000043d05140d07001c00c840024258000302c20720f8603510325030721018401c140380050300062042081d105d02031510304c00076010f42c14004102d40955412005c0c900f0b0a5449030b003004501070071003a00300c0d00c90152031003102115504020300c42c0601424041001600040a14024402100e0004020650003081402100c04028000d16002540f0785015a65072000d030400030460070800542e11342200300015428034000000c4041d5005103074400a907800d103036880008961072018a000544550000381080000e90702030120899079060350300f0010300b04194090200c0c2000d60031035022010032078000030341a20400d00b0b0b1049004e400142810058107003410106400c4c5080c40c000100760b5980000c082e407040e0b000f0856550392040c0c030a01999100c0325407038552902e0006846007401110700305d01244e07040007a0380300607019124130b2150520303045a40000329803212015003054010094164 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 640010557 1250 640009307 640009351
    0x1e020307090311010f0801090c1704080a030e1216020f040e0d02010f1103010915030506010306140114180a0e030a050301150f1b060b06031602060f060a0e 68
    0x25600c104840d4440c881481e286007440d009584005001d14104100f0034a0020a15048003c050540d05809000a80b41001e00c000b80c804000b60820345481200410421080020103401811088065a030a002c1d00400f4954030b44c2c0c86100e0700c06001840700601445541001050070040803500088c4100031012703400021400320350b000810303413480d81c00c00b2102c030080175024045e0f07400300b62404008100701401444403040c10b02060044003101500c0f03d01c0c0017214100203010310050b541210a94800b96503e2900300010446030032952035850440c0c0000034000c040506100b40c10a010b420680c000000d2500260700201c010100310569648515404080d0307000c10141c010300c00ea0780ca03150b41d80e50400c8607003800007078070107420410092131540d000c1c0801da0100400013003000c1c10b42e208a02121504d0000702802044200c1508600c0c003008109501c04d1481c200760804080780c09030746454840c004a11071407501100c1258010201d0b420402c8103e008602c00f0f0751101c1d048811146102c0011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 640011807 1250 640010557 640010561
    0x20105120703020d14070c0f061d030406021903050a0c0f0606140103150605090904030519030605040b0d03090b0708040503241003050a0b06011211041809050309041e 73
    0x140741c000c002603000c01c1c2c0581c1c400c40ca05c070703000100d90003a14090961420060080850300207950040031410314003000340c200403c64000409881c030410114039000c40c140c40150b52604140704040040c81481c0f82e040300d45054114420031547c26507109440c3c4540c42030305842c00c00c0280c00465207140084202808038545105100c0a4174040780221034459070840010142d9601c00c0c149011490b1404082001581004c00c1f1886c518003036a108006940e941015500380c007403885440c0c944003410400841099161348131400f503450032a4204070360401e100c10b004170b070f181c5200001c0200e0700c041c0c81448440400750140001314494900caa02d0541c03250042824503000481607088103005e04810450003004c04c2d10075510600240c0664600383c0b81d600e1302690b51092880190034401d0700004100d0907485410400e42d488006641400101d031101c4424507558031920405040040c0034184070510358450185681c1035412a00940c208400e502c10000101569400031400c0c46d0125000600300400e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 640013057 1250 640011807 640011811
    0x11406180a09290306130f0501060816090c0806040f060902040b04030b06060c0d0507030e190e070201060305070b0306180108100f020a1d120a0503180a0308040b0702010512 76
    0x450b00801c802110240d03154600388284403840328020880c500340c405840004030290f00c008003c40c04040801c15081480c01200c1400d03002e0819406c01802040b103400000c0d01a41300300d4011031044455035078020201c2120b141c1c0714040300280300c031004030315286419008050350726090070f4000346080c1e4403035442040741c1c816070100d0140f540100d000c00501074641174a691103101522010b14003030032402c140d80c403020200c3c20803084c45008200c490602d44a01d0ba040e8a200000c0c0081c4403400103072038200380301e8090b4860b40c611702002c1130028040f280b060203900212540308005020741411320440d0f01c6150401460701d42c02898001c81e43c00c0100b07070566028001c00d0f19501a00c1c0c42c281040c450400ea4a0848001c078002c3c1c01003000744686d50303111501e25980b40c1c00b4a07103048c8030b00840b00014602c040440711003c0038464059035006015011000b001c2031203241c940074a000301d00c441405842422440081c03c0e201c014001005880c02401c001c11280d0b1051501e10300d421030381c0c844522101c0c02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 640014307 1250 640013057 640013069
    0x20712081b040f0504150e01170102070204060b03180d0e04050c0903011812031a041a030f0c090603060723090307090b030d080c09041d01020d050f010e011406180a 72
    0x3c0b1410810260410b440380c0d40c40a0341c0c00911000c19828502000c800c0207061141c8d0303040340c00400108801460070f41c140d07103c056009005119159072500e00d083d40c0d80058072900c281600703007400b6240c01e5200180c50411040a5210740060700f5000003003000811000b0035101d25110f0421081c0c12039034003842008040151000d140030300f412142820300078042000e0a0b942807600e0a8140804e011414610f0f41c4194030071180454107000010591660f0f500c800b102a80520500c40390400e808404034580340342c400140c1c4d503040d03180e5803101003503075800007900c1000c0412554201c110300b64125071070788801c110340341e0354580c03400c4001804241361620540c802c0054030303a641480100e17881c080c0841480340d0107614000000307040406a00c1401c2c421201c0a070701c40c070740c0d810001d42d011046072090b5171103203000310086480b410503040f0390000d84800c4802030980b1250000100d000000700010f04d050340c050825841048000f282880314940c0400302e081240321100c0917252441d40c0b822f41c031002502c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 640015557 1250 640014307 640014329
    0xc0207120c0815010f0b071401060f090f111207090f0603021b16181503060b010905060a0210050612030a030606020f030c060c0a0e06070302070315020712081b04 71
    0x450010114105a0070448410181d000b42004005102951401c142910200d1b10001e6a80c0c5251500c1b903408058041841101d500b40100020100b41d00071002040f46c0400400707111480c170290703000c0e08480d1000d80748a4880814810108141018000303250700214500b01250180d40320310103030b100c8482591101000a4000903018202103044800603144d9840800a0000b0b100b071000201e071545d081d0254050000da800c442c3c0501c5000c5411448841d100010000c04160310703401d014001d0301c402600f1501040d20030074001703003c0c01d25400311004040c0039409810301800656030a00540070240c50550f210b07105100e240b00b00c000c28001882e109040b03803000900585004800b0b800d00001440c04000c5030004d00c824410720401080007a44080c1036640a42d888501c0c14050b6245d1560300100d60f04483d02054030000c242c0c00064960a4130302503424010101010180c01c02688650f0500802d000003c01c10700c603250740100c1d0225044100d14484141c0506841202401038103e9842112415 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 640016807 1250 640015557 640015559
    0x10905060a06030908120a020904020d0b0306010602031204110301140a0209150412140109060c021b0405253e030a090b031902070803060f030d0f030c0207120c 70
    0x8944100d40310020302c054241032190380c00e180ca6140060003090384601b60b10701c40000150076a2542d604587e1805030091086446800c0c0c0742c903010040c00031900a038001e10803040007040c0da42c00003007500c84100c00e40c007000c030362503865950742c0390071600380e046030381d0550748806090a242c000200040e214060303000c001a2210309400800c190000384154034034050000f000107010250307208041e1119030b0781101500038001001d48945004118000001d01464a424001e0112a80c0415034036820a101c13410404000142020082240e000703592000300003044040344040c100301c010f028050070900b03041000354000000c56104007126440071200c54101d2200c85002c00003403503941d502d01034141d1001141401c2290b4030191910105025103ca07240000c4000358114484902c0d030013010709800744c255102c010303502e0482d486800985009100d10780e503840114031824005000d4142d4141c9984043d01c80031110b20a40007020368140d010218050303003070046400302d80821503c0400b03114820b680032003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 640018057 1250 640016807 640016809
    0x5100203130b0703060605090d020a050d12080a0506010509010c020d0c091d1501030b0903040801020c0304050a0501022406010309060203040804050f090106080c0a0306170a02030d020c061b01060302060301090506 93
    0x1050009101c8804d051419506000059000e010303140711260960b2582900c2c1c7c42400010007804099000e80da1001c41e589800d81040089072540200c0701480d22820b11581f1414225019200d0440d00740780021410300410b03000358415600c40c0842400940380c591103002a803603c044009182c0c11240ca059101c000c1440c0c80c4811004440005004401809510b14103d242c0d04030380c003043c800039000e1400da10109050050031301c210f5006003041c0008540d00c1e0000c0c00a0707a02d0f40c0041c030842c0e110701c50304d0600041130350000c1860f9180c6600d460390071001c02d110301c21040d070340d032005090b0758101951441e044000030340703510040d8000d6008070fa00380e40380c0340b405081041d10021203880d240518804401006400d401c030450340e802099036a00b0544031003812100300c0007080356a014000f00d4454010040c019134000ca005904140280c3c25a44545000135050740c0e00e45404204d55004501041144a07164a008807889000b041200100c0c03550340c0d036000500c542d0402c5e044000c0d255030341c0040c0106 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 640019307 1250 640018057 640018073
    0xf08040e15130b0d02060307110a0303050105030c0913060c0e0a1d07050715050402030c0a090b150c031b010f02030f19110906030402040617030a2012070510020313 72
    0x95a400c400d403d0101c40b80070008a0346900d8003840090140d08040089200c6034024a00b0784510046002100e81d401d1481c14001c1c0509428442d41d40a400b90b112041201e060080d90284035a0b000707842400c011000d03a0f01c01e001803203120030207010000411032001c0030395941156080106041d4100542e0020500d800f9070140034007a0070801842810494800042c1c0c4070440f091420380b410000081503907440c00401e041c03980c1c0082d600d51100c0b038101c02291100960f8040c00729440d0548012110740000c60380821144030305d55000e0000e0740184141c886820850000a07035a81d41c0301c001080d2042c031001e144c01660400d8072492442d00012042000000000c2c44121414428180034828039904a0481d020340c8140000d10307000b014000000b4040d9200d0340c0240c00103018414120060070080c540d85501d1b0740080c8a0320000030440e01920302e402d0308402d4200c00040628001d04100398440c980c01006a100050488036405917060810300c2c0c00342480694400c007080c286400320803149160842d8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 640020557 1250 640019307 640019329
    0x207180609060504020c07170a0611252307080633010804060c111507033206030a05030f031e1e090708101a01080708040f08040e15 58
    0x10144d4818410380403c3d01c0001100c5d011107643c00d08a207106203090041904200f4aa81c000e00b0541c142001d42d0004241000100034400c16001b440c00011141082c420003005521809007801d120490130422040305182c2c034a440c03d5244017240c001c1540c6810302414900e046415001049801c58151842c10340f4046502001004d11812100040c12000190030528007410180010b5600c256544141e4080d00c1c002da003a600007030445080e0102c10400d001c031a4030881e28500040d0a00070052010404030f840c036000c0e01031104201543c149481481c1e4011600140b0041c0d140c417a190869010070010300c0140b0b20080000d001541c3ca25045102403840c05d08081052120210b030b40c108407a42100003072140c0008100070080e009912400d42d102c1c50000c00303411082c468024040020b9194080f40c3c88451182104818000300c03103400401511524011103c0d47c010030070b110700080001c4c03040c20881518074440d005090800351225004048544211032440c5038041c0c84e09421120300d08040864 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 640021807 1250 640020557 640020559
    0xf06020318030307050301061b0816050c1212160209130b0601090602061512030406030218061c09051e100509060c04090f02040306020a090311092502071806090605 72
    0xb51640c10104c000030241d1005110309401c020480a02c612040b100d603264a04854001644035240c0ca0070700070303100050b950607000722402d200d4100c1400b41c1e1308007075060b20706602e81348000c2c1880b83c00c4c50303258030b4860f03205c5c0846840014206410000503900c2c094131500845500000324074400892521200385400600b00b0b505100d420242001000c0c4e001952070f07400400d0302240007100c2c038081c0200d0003030380751250035946500004c9404901c103903259010707049403c00311500e650003224103814006e0343d106000c6140100900450398040440300740d0043c48040303101da412181e03841c01c03002079000d58001e040215812504005203060b00213034580101a00314030810003901c41b50070401c0083e0010310481c403030703414081d0701c60304070301c0b0245480d505450086811503415540d0380403c030002010f102d028007080300c08001e0079121b030000c3d00304400c00c1c6200300c524844507601440e19801d108046480210007900f18802d01c240801d20000212440180708205180400c5032410070503528182c074180c1d02f1203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 640023057 1250 640021807 640021813
    0xd021207020a03110d08040b0c01150302241207090509090c0306060f01030f0204060c0c0902120601030f020d0e0606040c0305090a1b0e1609080102070308010b160f06020318 76
    0x180090b079a400c0380342e01229440069030301d00700140c2000c215008440da101a00c03040b0085000101120040300615080303000c078008000b0801c1410026004030000d000c041d40246118618070700078607407488135081c00b4910150150030540521900c11600104485240c00581c804d00300300404d080c419041e40d00200200d000e000000b4401c4013103907850070020131091040002103500b070030030703400b90384045100a00c01c4002c1d5650340e2942c00282c81215002e4040f112421b0700300c00000d091819100707458540103080c1d501c1c00b05440702c2e001100980f0030a092615080c3e4208001d176050301641c804d0101d00c0031100c0143c41c1c1482d0810402c4121210540d00340b052500b42403c0002000e0701113000c0c00d403942e00040e014032240c034000411110440c01e8000400740c80b443c50a0014084065400a8440207503541d021040350b00e503c00a800e078003032002c00501240c583c500501ca0b20024401801b124903048072041160905911525003200b03030700c107064484940c0007040c802d41445a204049480707000c1001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 640024307 1250 640023057 640023067
    0x170d020c0c0f011b03120e0601120b0708040302070603020a090e040f0c120804090c090e010821120a09110312040e0a060b0d0e011b0206090d090b040504050c07140d0212 74
    0x14401c510001004c000b803c0241c0001c109094002031741c01001c0c0c0e440c0705411a803903903855840c14528041a0750040c1d4680009100041a0a01c42d001c4244581d61542c00b81240c00d107410b0065000c0d400200c800010b00000c940c02103a07841c184071246100328015803815001d00c1c0c40e4101482c02030f0ba10f0b00100380071200b82e040b060214000307030125011101c2c3d10b0400141050301c0d85085910380900d400150300ca80d491400010a00b400040342d01e101d0b4038598040c100302c80c00b029030b01402e03c9444103148040d0320090011391181115403000c085d0b81d0180242c07100e4080a040024148842c24070b40c030006500200e01440b4401030f04040c40c0d484082c00d501045031500700340a91656000c1d0307000f0031003000d449000200782c0354070a422919a40c602040ea1003c21003000c00060b4031900c044600c0c2410740316254440c4e800a100b828a44101c56040c111030b8039150a000c107000141c9401070104114001c00c0220b50002807540d8020380b00b14064401401c1640380c1004c00a0421400003200300b07196009004c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 640025557 1250 640024307 640024337
    0xc050a1208060a1a1c060302060c1f020a08280203161106040b040f0c030512180102010605090105011d0603070201090c060207060525020d05030c010606090f03170d020c0c0f01 77
    0x48401c5c29948151000e64080d6585858016160a4000a400c410046400b0121382000903051a07110510304c0c034502e209500300c03428401c034061012100001500e01001c280074841c400e40d110040c283c40180401081c00018003038007664000e803602ca002940c144454840243e201860f0001151940054103203424a40c03224185524090800b9001c18030b100c90440030403200d050b031a00199404004c1c0c40040076010108131445e000005d03100c0040e242d900102046603c18851402901c2c0010002c01599090500440d0344011000030308094581030703c030306a110798030140039500c43c40e4582d002003541c801070724042002c400a60700c03510a660025100f805a80c2d003000c01d9840c040c40340b030410341e00e160702c103000c0070301c0030421004c043d410141e440004028070001000030b1050f035031800300074040300b40e513118200c0c0d10316200c3c1700e03031a0701c40303d000002d10014240f0503048540c40417070a80b141c03c2c841a01c605a0880c0d0181c0f80c4c030241940048000e003c1c80c14036050140707540409007041c28085100c10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 640026807 1250 640025557 640025609
    0x30b09071a1b0f1c1101090201020d030e030d1e0c050f0403020121050a060807060903020d0803090f190c0b0c150601030f1a15090607030c050a1208060a 67
    0xa4000042258031400944142810000c00751007030382c90700031a1181d04c0034a03492418071005050705400640603001d003030701400c014044d484401740d040e801002c22076540c01003100140b246001c030313203c5070004000c0c100d121051402480d400c040b44003c0040c150308290324003011940302d1580c60301405030600c464428103001c2c0066030201d90302030800d0340e1407481c005582150442000e80349071001d441c0c001070101c0703a10f0a511a505842c10042141d01c11600c61000ba07400b8a07262100a610404810b2524005104a4082d58014200200701c680a84d0ba1031007003410100c0b806045408803010414850900074405043c000a01c08509010329000c0006150394a5508400d80d012800c41c80001150003079119074030031140060090300402c40701c0c402d010200300c24207024400f40e00c1001030220300b880461104c1c0883c0d62803c0e0042480e8903028550740e0a485c60b40c00e8102c00e40f60750050b8814031020551100780d92124080c00e0391090442d240120030041003407542c0d002505555070700e400b00f0811018034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 640028057 1250 640026807 640026817
    0x601030524010c06020c031305060c0d0c08091c110118050105280518090105061b030f0a05091e090109021606091b0e0609180c0406030b09071a 63
    0x140040341c02030300d900801a03690354140302c0d0090580748002502182c000e03010001d402083c42e1140881c00e03607507403401009841e004040c4003902d240c0150007090003a03400b5a0b06502801c0c4101703415801d1501c20000074010f0001e48403c4000451784002890801c6154201701740c0231071090800f0270010529142c84e142c80c1c10203014550600c1000191841c1c00c0f40e90041d900995016504a80f45180c003d90005016400c6a140c48410010341c442070103040c9007002d8001d0507150054a0303981840c0f4940c4c01000038220f0f13000e0b14103641c0020010031101102034402002900b8250b1241941e0b48084000e1003648030010b0250012100e000041d800c60381e5400001070304540c4046005629035240703070040e000422032607500910240c0340080703030410400310407130900500c024245203220042e07503100c941c2c41e03140c0111611f40d4003000c5100041c3c02018601200b00507488082c040344d80f000c1c2c410010074111013407a04145c8940408104012900508122540c00f078a248a169925150a004034480078014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 640029307 1250 640028057 640028101
    0x10903020c0906130911011205091903090b0301090519020306090a0507020f030c0706020d08070c06020310050d150b1c1205300606090d02010e0a052706010305 70
    0x1140001c51059504c03ea0058010f40e00013008209050b110710703090058591010455000c00c007281c008000c1030555102e164480c1d402500501460324207294820250308031040118148990070070702260401055001c3d43c0130305a40c0d6000921428a80d0080c3c2c652140e00002c0c1c400340c0e0041040055503241c8851007070b08a4400303040429036445022381607040007144031213280c2a00c408940303000300745d10024a01c1c0844440d0303000c2d568185000707002140c10100448221000c80c140c1004100000c00729801140c1c0049101692907145844600040241050000548200c4c0043c0c8815401f03682c11b1060701d83c0d54104984491161002506290607031007122409484502c961647c12489070241007103e943c2042c0740e410601641da001607a01130f0304c01c3d50100c4003a02c403074180010346c241030030811110407203c014445030407400543e0046510050380e000c850740000c5645070000d02900d03201544850074054101c0c0c1c46510040d40d0700c502d010040140103904260415040c485040c0b4180e03108061010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 640030557 1250 640029307 640029319
    0x20313121101030b0a05130525050304080a1b1103061023040605090c03040c060924030603151a090103080f0d020909040b0f1003200409120917010903020c 68
    0x4584c000901e020542e03804281c10521400904107840c900341d0003107215003d1011001c43c000c2c0c0207001402c4450305d00111102040c0c040001c00c0104030300c01e001d0300204409240c4441400e80ca00704410300e4000020782182d41600220b240700003450140112548521a60305904243c1e2801c0640560f03e0540400203001d0804178825401c1c1c2c0c0c5a5400c00409031102815140d10740c18080c90000c070681c0b00f00c40c141c400345141c4002154151180f0b2804c012128056681e803030210508a06030704440352480454207140c1e60780700001c005104140d03420240070034100005840e95907020000c3d0800c2c0061541440390444200600c0082c6018058903004080080d14907280c0640361602e50091088075110399001440d0b074100410130001d8070b101c0e4414130110802c640c954407a0003415184e469180001841d40f1481c803008180c81390010001318003502d0080000c140300c031709500e43c42403010740300100e40c000031505401405072140482c10b40e9205961240204441081600e00035240c010142e00c0314460780f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 640031807 1250 640030557 640030571
    0x915080628270b01180501050d0303020c0c03162d0b030601140723011e0b0a09020f0a02010b011d06090406051009031b03030801030b0417030702031312110103 70
    0x110407005600004400c2c1c9a01921800c00c480c11250901c01d804a400044142c0c40c40d501c194014107040310302c050845031850455540550107500f260f81142800d21451b110414035035420442d044ea81d8940c00440d4003403e04003000301268010001711200c01c03d80560300540140c0c0d01403018001c5404520f0b5981d101d8036007000480380c014042d0511000303003501140090030b000302c12462505100140600801207482011214240c40a2961a110165003607045444480c890f8000e0603009600074003602c0015200e50031641240c02c1704441109c11440072454450a40d0244990325000c402424001c4d1440850780c404250220f13405001d50240001240300c036000e072555048440a000003c0081c4070307460040c2d9001302044902d10090780c0c0c200b50071807a100290132500c0620240e9400d40c0d00c0b030703400d0703803c68481d4804914040d02c112030740250070644541204540b0003650181d41258061a0340f0700300d03020b15003000c0380c00d0b4200071280c4a0300000c540004590b8120086050340c00c2c200030840d6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 640033057 1250 640031807 640031831
    0xd021c1a040305040806070813020d2108040b07020633061602040605040e030a0804050c030304030b0114150a0807020c190315060b0307050c070915080628 68
    0x403204402a4a620100000c0c03004060b04400900140d4a401044580682d503015044405503c10742d80c840c4002c50001a540160400c4c4118194182c0030b2840030b2007681286100d41021246141e03401d00080118050000b000000281190003801900c02442d00d42485030402d840e00086140380140001c4625030141c9110a0300381c4021850801000c8035180d02861042401e10700508904038440c520b0854081402d03d05481240c189491f024001c500f480f00106c01170b10030242c068000d4030301d441080f1182d10160380800007040510b205114801043d458184010030300c100d110340740343c49413600d81c58101e43c1480c4c00d02566400d410520f005511622078000590030120700e001196007144e00021802491354100b00004200c030710a0038a08521480d150500045840c0e0707000d154450705080001c02c44051003000604660513160003640c1040b6500c91100c0700721614044a0103115580010030002020203200c1c0e15070080780601c00ca40d090502c19800440d00c405011150a51030361403000e4162 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 640034307 1250 640033057 640033073
    0x20915090708150604060c03022518060306020d021308031c0b0609041a010e011d062109010b0108070e0a0612090510020910090602030403020405040609080a0c0209060d021c 76
    0x2080f0707020304a103685685078800104500c280803410f4026105481c0310f46010349007000030080082010280b078101e00d003025005034040040c0003083d074000b91200c8002c0b022036000e20043c041c100303070340e400107954040740e0700c0c081d10889180d80a0f04941e0014001c2540d144401c0c203000c04840c040b1040000c0c2016464005034072400360801503500180b81400c1000314020035010f00c0a10310303090321441c8403419540700444492900802044042c90b0b80781030405103051040140242c45070600080382d0304c1014031240d00307103150122107642e00c607910f50740803a50742c0d6008004581c01103080e15244210780104008a00501607500ca418100310030032044e42e66004141e80080c00050b807240545840d42c5c060300200001c1c0d004040380f50310544014240f5100c0c00c1c041c8500104940040e0051030515145408100c02003400074801e40d11552648001c10024041c10020044c10003143c0354002c60200e140188000e661008003211f00036900948014050780e170700b500311190402d8481d07210701400880e04c0c010306 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 640035557 1250 640034307 640034341
    0x16051903050d2c06071b120c14010905060712021c020106170102031b030408090a0e0f0a050c04090b0315010e0928060b03210403020915090708 63
    0xc0940203150750b00360000c2d8000c9003c1145040982090490900c4625142040020300340702a400741d0204408400030341513540b000990300c40d141241c4e20003503071905011840c1c00994000c90365200c1840043c031080c0003110a03150140420302e00145410305000c082800c9200f500409080070040c84940890644200284540c0b40e16000701d105000c208044081e0103003070240614250310303034000d0b030441d04814144241c82c031540d80708010496645848482100c683c3c000b5105903642c21042003051004e03100d00c5002070043c142007004040900d010b054100e0410400b80000380780c141080c084c072403041d1381701b01580c00781c44400500040103080c120010740303001da070007903501c06078405080001442018801c2d203501c5541d600099440f044240e4841044079540c5903007140c842e00c06483e46a008c20110791000c82c0340c8c18045c0c11900c6400d10a02416023240c00b00c0c1a810862074005005e0007107043c0400102c2d041000d01c0f12040c017051003e40051a4450024103003402c104a010001e010819040e40001d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 640036807 1250 640035557 640035563
    0x50a08040801020706060914060d0312060e0106080a0603030228020a060c14030a0c11190906061805090105040519020a050a030e150a0c020f01050903090406050316051903 75
    0x50355641e5038401c0038040d4102940a4460510b403010006980e01d46000c3e01e082c240c0714510031413642e50345034202300a0f030916500a4040040c21041d0030010141c2e842480050310300c0c028103520f21f614114006060030402850030a900307042800410000744c000401a1410601c1003070b24862052514500c0300c4100245806980310101c150001412600080c540522030b0150f43c1503507400d22414801e940e00e20805c0345020000b8050000c40010810103c60744605c9070005001d04500258120070411143c10303500a40700d11542c40000b0808a030300312031a006030200c44420807005602e418005000c02c03005125050040e42c40751f00145e0707c6000f803411004800c2d84400c04640700c050944009286401010107103003c80e00d4244020103481e0f0028034900c0d0400240e1004900340c0d91405400c001d0440c041c1388600707600c075a2111160700c0000b80202032161180c00000c5844001d802e04000544407582c4c0b09a00a0b0003400304424800741504050b0b0035240d059921040c800042c2d03c101c00313203000b158005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 640038057 1250 640036807 640036823
    0x303021803100203060405250c060f0c0e0a0f061b0804030507090603021306030b1803090409030c151104090b06070c0b090f03190201030e01060b04120b0f01030c03030507050a 77
    0x1c00c1d03003244583e000d0b42c0112003d407410001a900c1d003c048082d1250700d0f600824003c4208420100680724a5003c0c0c50030b80715010100c0d010300c1c3c000700c0205071920082d8200100e4130741e104180072428040e86010040c0122a803240c2264600000035080c446249100040911b2100d0300d0020b22440c0310458004ad50702c80304451620b40d650030558000c0205000407403040d1000000c4d8040c0201501810090720782044642d40c0d82d484000511980151482003155503000602500505668a00c203009400d03000e074030383c0b00c0546064600000c18400303010360750003051700d449002070f40d04c1800001e032803e0f240e0521000864091030070000d00a805025001060495600e10204400150400ac0c00700d0322015901c61000c1e048000802d511060b003101c9107540ba02250581d4409513100c0d80120001c10344442c000110562030f02c25502130341e40a038100d01c0152405882c5502044040cad045641c0c800750b240f82e86440c650450f40c2d05401d50003548005810000301141290500609004404100f5481984 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 640039307 1250 640038057 640038073
    0x9012f0708160906140402090f0a0803041a0c0d0f0309150905010c03050f0a020f07080c0f100606210b120d0e06030609040210140a03051008190303021803 68
    0x4515900c8180102c050800a04404001003140e030314050b0806407038458440021116521052200030b41041042c03a40c4a01e91350541d56803a207075450b0764006000080051036899040080300c0c00ba540e040c8000107240c540400c450f00e500c03038000c550342228224030310744441e882c6007640044000c1d240c004406840104007041c038050340d454030b510440319141701c1c400038000b8003003400007507080741c038102c1e03002440c200300c4c8001402502c034560003045081028201141420860384819003960862080703406140c0c40b09007640350a010801102d07859217151501840502c1c20494001d1182e103910661852009074a100c89542003003d80281c3e103000c0010300041662098061140c1d40e40110381100d00108031070b04039264a606207070701100e21416000e042100700d82c65660038802248801c0c5800b4003003060002540c200207030200d00803e501e00700766034086014246114410807052080d480415207900150030610505080020100203c0c0c050400503250301380c400c241940d2040203046180d16004a8a13 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 640040557 1250 640039307 640039319
    0x12303130309061d0909070e011805010b030c090411042301080c040501140706090506040b090c09240109051203210601090e07020a08070809040506040209012f07 71
    0x34054411802070303a4080710701d5070380c4505842900e40c04c143c034000300c011100d000f54541800700045410200c48001c4a0f146503840c0c4c85003107180d20070f80200c0c003044441024080810b0241c00f90602410000c802c0c54035604041c8406c0c1030310f104030b8608900660307e884d9041443c0c0d00c0c1034191001410f00c000c0503111509000c14005003884854005400709400c81c0110380300c600b0000598003510010f8444401c948850412108150417040c41150802e85030038200001070310a1007014012881000c00800a01b48640300a0400d260303900c040d03000d0801d044c10800d111a42d0a5803040c440c4201c2e4490016002a0740101c1e00362003544c029640024050000402c0071100000074201400c00c1d03011134080d0005810300301c0b8003290990300703180024018181032002c2c250348804950400d040d401264481e012a42d0f80c074003141c001070780540c4c20007000f04c4c40d943c01d420a070143c240e2000d8100c404500e841003210000e80342c51f500e0701c0c200580d0340590001720740c3ca07402c41008290704403d0030115039000395117072 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 640041807 1250 640040557 640040581
    0x80c0403020a1d0f01051e0406080f06090c06070c090203041104020c0a0624150318080a030b22020a0e03060c090102120702030303450705120606012303 67
    0x1940c1069410f0800700000c5000f070402000074140c40008009040c845604041500c505003411091307548160b030f9450014034198200800001c1140d000041c04162a05e14049800d01c2404c80c0000e004d00410000305c000110b00314018000d5800c90301c00141c494481e41800000c643c0d0f40301d412a001032000503034207410000000c03185c9201d8486d01c01441081103509074034124282c00741e81455410100c030006d001c42586c152011071034028a190007c0d031541000201310074541d403444183c4441400080c0c100046a150003100d204d42c0c019149842600c407281d103200c04101c0314014010b4100d074045034103a140c84c1b00c2d0003540519440242211140d00b041081441c0c01d40c030850100380903214081c42600b0705504401501c4005030018061406e41d0344040740811b01171800102c240c0004000119506001025019044609001305003144500c0307040c0360084c036028a030381000340b0401010b0214150300d600000c1c03280c0c2c4400286080701c0040c99400c2c00034485081d001402560301d0b4080b0030068080d09071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 640043057 1250 640041807 640041839
    0x1e07060311091011012f0c0d080717010b040f06050309100e10110c1603030507290711070b1813021303150c05030c0a080c09030f01060504050105031606080c0403020a 73
    0x48190342c00700881303803446c0d25841d10078158400f5036034021200e8000010300071003001d6481a035030306009180310003904e0120041e00090b0000b40d010340307000c01d05100307090403561008007800c1c243c2000c2d031440c20a801242d0b501c500c1510300c1d6501c02e88404040740383d07200612658000c254000303000d204510f40c0000058090b00900c4144010384a170451032402c00841100d03c504070390b01521641d00d041d606441f000040c0044098a9000c00d0f0f60300c00441082d12840015481161255070f4a445074100340301003803c1180961010b002c40400380b0289007801120304003510341d440b04684138500804541c2d07008010307000304202480f0501c81d100001040c00b040b40324696110102c90317010003011101c20010b561500042c0c0d1034401c4e02e80c0c03e000011740303240204403c503007240150844c0380c200309804000a00d84910340905501994440204202034103040c000d00e4094070f0210301900c20a0340c0458022046503191080c5001c00c0f4010005c55001d0304048100c401454010303082550103a2515411800c500300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 640044307 1250 640043057 640043111
    0x300219030f0b0301092301020403120f0f0f02030418110c0312010609030c05040905120d020c010608030f0316030e0a0b0603100b1e121e0706031109101101 68
    0x80100300300b9149810b02c40c403540c00c0c0c5e10124040341041640e00e207048030b600741d180d8003400b1b40d820400803022501c1c0c1c41c2100d011311034641d189107284d060210300502409400c240c02e030900582d92000440190048190707016640200e107411b080882c1141040d0140100300f41025029500040042c0c1a120101c000c0995101d200100c2d00b803640e0725441110704c7c0c030091002802c0e0304800e16043c845031a1607004104100c2c0070344121201e807440074082d442c035580101d01152050b513000074144000e86081c0a040c004282e41070141d400c01c140c3c041c500701103110040503003007582080d07030881c415a8000d0344001c1103091058211a244000c9141003600000f042e65514403d00c503180110300d029409000b4010210405030128410071000441c0300d043d81d404c0d5403202da00c10140c03508a01001000c01003407140d000380001a6011000c5001100e041c1802c941244003010b08280d0752541450b20701048840310030b4180e070b0720340c0805042e01c011201c07402c4401001c0055420480c1c03581071703480140b18146110207 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 640045557 1250 640044307 640044311
    0x302071b1a0901140714010f0e2109040504050f0d05041a07030c140102090d0614010e040b010302090711010e0c01020610180c0504030b0702060106080601300219030f 73
    0xe5010070070700050240061450010b500003035145500300540020b018940e10800940d120300c03480407200c1d42507440349450300022a5541c0c0b0340021a22081140c0503c020b91503140301c0044440c210210b03000d10444070024021510794010408000040041c145403071420001c2d5107441421480040c6554024400c0450351408500071540a1b104502100c45141e03254544080410306a40ca1b9466440d03000f00056155500340032141c0c1c5a100d05d115850307554804d000c002499485400300f80c2c5c9200701071300040301c0f600c682802c100000da24841d4181c1540d4044075545010740c5c922a0441d540410050360034019400c00c1e030100d40d42000003454900e9001700740c0a4592942e1403402c03081e504281c91107203a40c0128800d40103043d00031113a0040e885e41d100c42c6481442c003526500c9240040783c040d181800140d001000400c4410381c402201c5401503c01d03c0d110303419140e00a6103201100410b81546000041e0902d801b00c515002d504640401d2440d0024500c3c800b001d5401600402c180c62030381d101d244c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 640046807 1250 640045557 640045589
    0x803010b0919080d08040503190905030f07061b0510020d050601030501050f060403060f0603050f0a0c060302030606030103110f09090705010809070f0b0705210d0f0c0504060f0302071b 81
    0x30b100b12800700c1a00d84401c010102400302041c00c075003034000070f0402d5500d4002000700d10036081c1000e050455039111030300e07001c2c03e0902d001e090510b41007013038080980d1038003c0c0d02c051005540c48a140c2c0c89000000d040c1c007940f403100d800c01500f003180488100d000c4920002d0760200e10a0150003503131003024241c030100000d0ba660303000d1044880c02c1421f115400407040200f8000600700343c0c0810500841c1101c0000c410341c580d1340301c500d44800c1c507200e100603621070781c3c0e841c0420882d03500ea84064011b501d401e500314140f40000c21094041800010b0500b10340030020201500c5600c10b40c120718030004c1a07078905080c420001030b100c41081c0611400030782100000390030f1450001c1c004007107a62042041340c11301d00c0c001d854601c42c1c000f10703c2100d842c003852481c90a00790031315060742d20301614204030759600d00440c87c1c1d031030454541c1403d40c44010f0910000d104103c0d04403055a084540d281054618661070200440007031140c2d050040402d00c0d24030b064601003009410f500181c4541c114622210 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 640048057 1250 640046807 640046839
    0x120a0b040b0a1a0717030901061a090d0305160f06290a031b3609030e0112020d02040308030610080930120912070203071a04030803010b09 61
    0x201d510b90154015881c454051010441d0f0381c480201101d45c000c0c0d50348100700c07007800d40200069100399403002e0540e442d070200b072160b4060705070150b48111180518503e400003a0b40403558034a01c0c124003805000c800b08555000030390703035900300500b20b03800b80024500b00d145141410081c14030b01c03400c8281c000500d10300203100000d00703000b000e5814005c0000d04030a03d10313540c00084e04048003070320441c5c0003010030000740c443e001150450822080154400442035034407400c00c0038118210301300c1c0002e080c4418403000c01e8206040c0203e500702031800003600301c0d580300c5000107807003205505541c1d688000740010500c01220040e60140c4c0080740e1a696403401d10800319407101040d65059051b4001c040b003e0400d0080ca00c00c2140704144d09401694280c08482c290100e400c022080799001d50b41c4010070850302428402500c5181c1d801d00070601380080e50700841d5541d640d07801034541141140303007a2081c5503084005e65008652100c4220396940c0c40e085900e10070f400c008a0b02d03000d5400740c2c0ba24204 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 640049307 1250 640048057 640048069
    0x605120d02071517060f030307150506010c03320a170711100905011d0a0308061f05030603010f02070302150a050408070f0f02030f0a0213060f0302060f120a0b040b 72
    0x140f000c03556a40220700c40c81802e00712024401416041d408611108a81368503101400644000c5d8052150003840001091441050b6440100041c0c10000840e10390341c0026003103c00450340008061314124005e030180030400c682d0320300d210f00c0182d0500204400040302e03480700803201d2080c4a010400181d884401003564103406006841040f900f010948000e48100c6034444003525000d10000b19148901c2d009684d980403a040b0501030f10b8100708800820f040d0010503080d0428030507141d00c84039110400000b50358614600f205000c03c00000080b03562a903003500591840d410040046544984916010b95110042e0356080b000c03080060014007580c0d010b12134a44602c1e00700d1480c0b841c1012580e981c0310303810304412044986200e000208005614200314420521000f18001c3c25030021a00410081d0005024011300950a00200f4060825102c11400c21660f060b507000351203050a0b000303848980a1407400303240c05010700c420422050f0726a000350b6003e600940d000c200e0221a2018440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 640050557 1250 640049307 640049339
    0x3110703051e1303060e0d0215060103090c0503060c09210c0108040312050406020a14070c060c08040e09100e060f0103021e0402030c0309070602060f010501080a0605120d0207 77
    0x11890a00804101841d060501c2c034a038108225058508080640c0c1581841c40581094070b100350788040104d080082005a049207482d203000403c220480303003000c07840729030000702003504050300d802c0c4003c1003002c080382000c0130340401000d0320f03103501d424401c50301c2c45e80208070494480c80f0165000c00060a01c11038a01d402041d64001d414442c0b1301c00015240984090021000c10582400101c4c02460a22174a4040c0c3d2040601599464507510003c1c61a803210a84d4585860301304482c03400100b00c00707844021107031039040080000440c1d0500800c203024991042c1c0313000f0380c02002c025002f1000b14007601401c950640400c00b41c000e1404895075290200ca402001304003507001413002d86810344110060991280c0a1800c01364660f000c00c042c3e03003050310b001e03040401c08001e00007429014000b001c040d02082c80146914a4a00d01d1000e0080c8103110f0103041c4017000000c05c184042071703000312016040140001e5060700001c58041d644036150071000300140220f42e03000c030b011040714200c52 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 640051807 1250 640050557 640050563
    0xb090c1c0314091206040318050d15090b0702060702060c0c0d030b03070f0303080f0105040902031002070204180b0f0106050301080a060b06090d141908250819031107 73
    0x200d41428503540075601600042c698460982051106680f90b81d00c80401c8034012100354003402450070645000350441c0e204006207110001c44c084144074641398a841002d90720740080040d0803000b03000c3e0340000240f01640018142110306010416200d07000202c0034009ca0803513084411582c4d035000c2c64903090261480884964215142c240c22992282d0814004150020250341a1030340c1c1c0c11166444d203030f169008802181505007002402c2400050290040c00c00f034400b8400601d065000035154980c00d56040c82c095404180c210554446034024081801c210007101d0340070740c03d070400004200003140c3c01c038040b145000c0045925480b8034107a034120740040004283d81042582c800c6c01400d0340d4003000e030b0071120912146685940301844003000900a80d001103011083e0100b00741401144081c0d540548554552040061042c0080382c4564500d08641d10f20310303242c903c41048901502c140a0441328010580078030188020010790a01c0d40692020024251508007440d418000c1c40d4001d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 640053057 1250 640051807 640051849
    0xb120d0f0c020906120f1b1e0a06080a0605030304090902030f0a05280602030708040213060609302f0d1202030d0204030302010614040203060d1202030409090b090c 72
    0x309a20717040400d01e2124481801050b2503200503021704003860141c00313034400010307100309100d0350025003406640c06c1019454134030748080300300c0c4000216210b40c400340300740c508208800d0002072040d281680408098080241600d580d00c3d47c603a44a40030303004800c800c2e8403a00071101a100340800014041003903a6010010f0b000940304030b068103250000c1000c070340300c80c1234803024413400094aa1000314410541500c800800e400c0a00604c000b80342560680002903280c208144411600200124112081b505041d4041802010342155a008229034900440701010950b000c210900f00007854007003008240c032a40d40c200d0741c50001c140c0001c41c64960000f52504019002c034481d203c4c008110220380c0126442c00740000400001c1380d100d82e109500603591603000b4888040d0004903501035517400c407019811420070500042d4080301000d0018407440303e0700c086405250081c4240d6004218001d02001142010304290481c204100c4024545000d1812012489d181c90b00f03140409440d4240c00d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 640054307 1250 640053057 640053061
    0x80c0315061e040306050403080903070314030403030207020909010b01180e010b070303020c0f06060102010f021c0b0f042d020304080319091502070b010e060f01030f0b120d0f0c0209 80
    0x2070107501e601c014401002d819000001e06590a10140208000c41c8110b400051616090900030040a03001d40b0300c0f03035190402c018202c04280c2c000d078031090f025420f0300140d80c0c0b0f8a070707860190000e03c03d500c402074104000e0400c00a0002c01913000404008080c0c80740b89241602c00c40a5101030102d005144181055100503c290800d0340f0103440b115100c0e050041c5003c5d505122285040e41480664103150f214204201c1c2550f421f00070440d00a0170709100303505103004803440768140da001d0131102546507500c1c003466803a40e4032910350383c1460601900c00c1115100c60914000d030380e00a15081104040070b03440028140503d807003168840c0350804003090540d280d00c044504100702130100d1440075a100c1020b0380109201c00c80380b106045082d000142e032500145824080e11005034030000c129080383e010043c10307481e00030714022803090920b030001e03030b40111000b00002810741101c25900100d810300c0040642e030000810484801964886604445240ca001c0b50354156904000f034100303c802c40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 640055557 1250 640054307 640054309
    0x702100c052d0f071203180f05161202040b10021e0705210f010c0f050a090f09140a1503080304030c120504050a050a0821040909050607080c0315 64
    0x4644030242078028020030140da1000050b8494000c80e60301d4a0341074000604000304400c4075100c4080201070706040c4100003001d1401070308a05050009400c84140d07072103100c2081424001c2184074403e04421100d01c6490300325403600b00315001d030228003e03851f100303044500b031070441c03070320110403807694000e1140d2846003603003010507002401c03001460b218504020a4594400010306200b1803000303560f42802040c002c01610341058180d001d94164074001e001c4031030355407190121603020500e0070115a28448417000311441040340e407000816242c0c0c1500440c041e1095000513038400fa0020801d8000c3d100c0304200c030111a0a510342c0300807201040307c108001032899001e5603000b802424824800c1203241c58455003040b001d160f003800208000b40901040c60700c22900c802070b103000d0b03c0700500c4e1401c0443d41d5039076540003210390300c40c030400031642c030350640c0303000200e9020300381c07000081c00510421f181181d900c50080c2d5950707001c6207000c40040e038a8904481a80d1240c400070380d802c8104403030380c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 640056807 1250 640055557 640055587
    0x2070515031302011e18050904020906190e100306060b16030c020d0f060501080607020f0a0b1b1204050d0305060d110301020d060e0a0e0a0c090c1709060702100c05 72
    0x481c0c00c0f41030006051402100384201841d9800e0403003251107580c228403034074101c06c0c0d10358031a41045204228050501004d42c072000380c2c4541c03002003520728440302d182900710b01000158076408452142c210340308000010728450b0449040f00d201e003a081c0315060301c1300111030040c020200081101a034160681c1c000c40e01c50030703484806c94000f80441d05841038649030801220702c01c21b0b0070383d94035440301c00400c005201080381561086140c03001d00402d00844e601c0540300c0c0391194010704072501c00c1e801300d00d01e54500c030821040d0010541041da9229062042502c80d024115001d0790280210400c18002c5406070144a00c1000010810100010559121440c05052582c060b1f0159800d020f90980c83c120741c4109406051080040f440d03601e031000941041d2404a04490b02c180c2080740b00100240442c0c61f131009441d0030740004650840300200885408441010003003c403807210041c050b1910020810600840c1c2c180c0c2610182d00302030aa40080d210341140080000e2001c000c4100c1e000090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 640058057 1250 640056807 640056841
    0x31407080706020c06090d231b0d120e01050628170708100b0a050d051207031e0c151e11120a05060a05010f020c1009060207051503 58
    0x5410024180181ca440c2d03842260020b00d004c0115500c90801d00c04070140070005151142140c0c6444240103c1d2003290014201150b0301900410380049803010089004d400210380c0510510300b1240c010107010002800f206403211481c0e1071a2506844454581041c003560b07100d1080540258040401100b40c29a1401c400d20340d070044d0b0700b40040108000e00c06140a1444141d144024507a4900f401c29240c1401c40b640c041c03581c82490100096040c1d11024040000c5840c111440071581109041c603038140500000c610101c010700003803d00030140c0004402d8052a0040d0800c16200366240040e074200e1140200504598002000b031420078001e5041403400c04c000355210180901c8845140d001d0b102604001d041651001c20a0300c00480000641980500003d00a0040c0e0a145c40820b034510343d5806076a0400901d00c8401d09414000c001c80d032500500641080784004002c6c8004200320650f003c0ca1005001d220000070705850502c8080b0204062130b4007503451600c03121010210390b914 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 640059307 1250 640058057 640058063
    0x90f08060628140301060e10031704080a03050d050a0212041b03050604200306073207260f0d0b03070e0103062a02100b04060f0f03021c031407 63
    0x5030301072032960210b0040880040004a4907010280700070010103080d1460740c1c0288111206120070840ca0348d070342c40b4051302102d4100ca41c034032031074414082d1a403c502c5103404c907550900c1040080030415030b00c40010301e02d05122742010401501d40c104c1744001e030310401140e0207400c0000c101140c00b00340c1c4083e01010203c400c41008041c00d959640349030030f003c01210144c1d081e00c011080b40301000c80075030a1030303c500b030100c1c0644aa440c081a001c1c1c6070059002120340f0b081c02a00701c0c0000c15a03030150740c0c12402c0b40c5114041d01c9900c140380c06001c88581800c4d0300c6400c002c0c600056040024041624101d69160340b120b81403600030040b402c020520031031482e42c9489101c0c8000f0740216100740c0035010354044c90011400c01c8220050010000b9580103480d400b440c1000300c80f1019501294401c881841440302044146c0c1e030000140103030405801c00440c0e070442c3d440000700c4401d98074192017141d1090b150b80351a030032071406204601e580c1c41801703800301b4607004507007603000c00c031800504503144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 640060557 1250 640059307 640059349
    0x1120b040f0c02030d0c02070303090e0a021b03090a050f0a171009030908150f070e1219200307060503070507050106030b060f0406231309080307090f080606 69
    0x4481c0d902881690b0b086208400036800018142e0741421490148010b44001030008100181c85c46e80c005216289620849032400c0071100410851006901244d08020784c0e0485420041000c82d10152640c0c0100040c610915024000150a0901c00700e0003030382d150014118995903150402c080c822000400b00001603025000c0030a02000841c42000821030003966100f031410300b8290b0080c034000410000c6d4a0350040e401c10081062901091a548010146442c80d4103a0186000c94000280c958150140e40280112541034409201320f09850b14042e07a6615540c0420b42e822580c5101c10040183e050740106800340240d42c02000103603042000c0380342451078140b583c2c03501e82c21a0304a810032240171020105000c5145005081003c1c0d41d40b04039010000c2500c1d20800c280351450380a603410f1240d6016a084249a507087e86072002c140a54600f44000442440c11041942c0100c50300300c0414030b10007002c03c2c81141c0c0513105040c0c9003190000c19003030301c5010801001d0100c0c42040c0280b61 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 640061807 1250 640060557 640060571
    0x3080c2a150d0c0c02090c04051507030e1206160504080a030e0a03060e010b0907020303060307030b07050903030309070f081209010c0c1706010512010e06060906010311130501180501120b04 83
    0x445074800e03100f20700341c2a680c1024502241c8104550f02d64040c0c100e910401c014081844030b035486102c4e510801e00080c510540e00c044074501075415a107810002d0742d002004080c8005503440c007142c124814004085044500346140d0301c140d856004501031804540d2185040400190207a09024400c08005080c59401640da60b1030b042907900c84003100c4441d0751102902600340c14092081600101e01d40003640c21032030a00046540d88042e0b104c05450b00240f01d010076400d901130000ca8000c48400b4086c0c81d5a49041d01041d0b646194600c203840309004400d2001610100102e000094080d484048a1424503080c00454101d110b400c01507550f10204d10000681c508101d040054807900e10300600310540c134002c20002400e1100032008900d03410091040c2c0c41805c00f041c01c3d80d000d00c0880361000903444120048004001c0101d04051043d00004c0c9200740c04581c2004c0400c0301c409036550241c1440f007440c0a07200d50000c5c860315000c1040c17841c142c0c803441d42c1c91700050440a0081e0000401c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 640063057 1250 640061807 640061827
    0x100207080427060f060c06051b07080315060403150b0a050a060f0e0603150409150501030b15030111090d0609020405100501140405011e03090c03080c2a15 68
    0x550300310508189050400c10038042e80c541140038690042c11032040a1001c1460148042c20211380c040000306195564000070302d007100ea1000445d494103036100f0845d1168914506960300c0c0d03001f50b0f041048001c01c0c403134007070051400e503040341c05581e440700c01c0140302189000c1d0000680180b0123103aa1001d01807801241544401034888001c00103030340c078030001c0c24203c0005000417092041140c040c1c441001084074007144c1c0e0308100003414040d03600043c42481810120490100050091005410007000106100c00b503c9014040d42450810040c10600e64041500308c1309110008000508103005c184c540b0325007543c448448078090200403a10003895030020741190412075410304501c80c28030b400d104951f4055652480f8141d213903c0c0c54641424080080c1044500146285040ca00c8000340551240300c1d03040b4003000c6074081c50700000b15489280c001d0310780d0480718044082e0320444c2d0440c40949821480c01d05540e56503c0803800e01502401440402c0c1c035a07406d40840305100308410008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 640064307 1250 640063057 640063079
    0x1202070e0c04090506030c01020c0609030a021804030f1b0609050f06090303010906051e060f0c0102030a0219030506012a080c0a0204110708090d0c031e02090105030a051002070804 79
    0x440e000c200340d8140d4440c10203000c24100c81d030190417075000303074000c0301e20003074990b0001110711800c101240d070144c8440c85ca0300042d141c4001000029000030001c04419401e0020481c4680654800d40718a2a884849003007100c4001d0142854812160007922100108100358003150003d401041664400c59505a00c1d52a0000503203211281da4000401007044401610412002e00812182c0394030a0701c2c040e600b10f80000c1081c151500c074000000d1884004448041140c40ca0600c0800942d10b030311305800214003e420141032910724010004556203441d2003032140c42d105030b5058560070a07000400d07121000682c0b42140d120312030803008040c00301217585040540140100c1d176009014401551040c001030b60082d02c8403040c9083c0c18440b1000040c0004240c40d02003c058544481440075810039045c50401a40060480001c0c800540441a2400358030480c00d402600d1103181d43e40c0e207405142d55a803880d43c026021b0740180160068045d42d540090200034080d000c0281000d80319181e90318 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 640065557 1250 640064307 640064311
    0x160504030b1306091a0105150d020c03070f0503070b01060903081911070816060504030503190c08161709060d02030c0c0d0504030302070e0c031906090c110c120a1202070e 75
    0x5440d49020011785105120b40043c0c9004d040152a0585000c080c0031600400e8040e0464018103160041110200602c080054901c0c407038001510340c01180c0c2c40e042a46e10b07584020015107100d10800004583c030b5001d03011030000c4962142c0368501d441e82640b4805010188400e0752801c02c030a8490024280c2c00402c0648080c1540d140500b031103081d00c0c44040440d1019034401d106101091008201003003010064034a042400000b10b0608c0130900d004488601403000700a04800c80071402008a1b8860b4452240b4a0310800c03011260080c0200c00c030303089014292202e5440101044410106400d60300550b4021141800b50b03030508039510003050401540100440c005180854204241039042102c180240604520441c1609055044400da880000c0185102082c1c420110000196550101b001000c0c0c0366000c00c050302c42800000c04c9072008a101030150300c649002d1818501e40800c1d128102080c18004180b0112070796070b810028540080d01400354042c0805c0000c1403114903000da8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 640066807 1250 640065557 640065563
    0x30a0f0b09121c0506090907060c0305040f03141603122012031b130b030403200601090e0105010e1b041d070f020c0f01030203090c041a010206160504030b130609 71
    0x4000310840f401c03001c01c40c3e03001004640b14a5460042c0040c0c5d44001c50b00300141d03003603840d1906034000c0701d0406440901c11355002c20064a1811000028006071020342c00c030700358149055907888101c42d04203004800d0b00d8040030b800c0c14662612102640c1c0660540c4503201e560020300032880007030100041c20714542d460100420180041000342c0021304142003500c1c0d96018010502708030100a004c502c24a00b802414052400080030805150145104600104440310350845221402460580342c0500f131050b11307805420403000340c10300130040c0a41030685112842c07500b019a928200981800070004039440c42c1d0390104000300e51403110300b0940c0c4c400c1a50b40c0084101d8104000014004060411076004540149140451036a40c0c550300c0001270009180c09610398841c005d080741003122a4030440c0d84289811a207421000311000d1102075814240c00f83d480c1607032280031820100080380007841c001182040284009900c2070042c9401c403058039071380c1d13032604043c1c0c1e20f04046500e600c4080d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 640068057 1250 640066807 640066837
    0x1809010e0703051c1e0e011101090606060e0d0809040f150602071d06010519020727060e09120a050f0a0e090a1806050414071e05030a0f0b0912 63
    0x8100c00d4002c1080e600400503036203848141324141e144094440c941700d100788001c02040c0f54020441e80c2c0308600d440c14010341940204880819031400c50010b084c4c500c201008034020049885a91600c00a00b524582d006046c161030912102c0070800140780034880c3c0d0040e01c0d901c8200e08a007071401c0a050b4007074503013034004100190618030351600c024804100c0794000b5190303d0801c42c0b2641c7c001c0540b1450017030103001c00b9290345003410030703410308801d0b07042160070403140c5005003860306107156850001021130344100f00985c4c68000703241401c0c00480c1d001d500d692100c1c407076241070303418000281804a018038001d810900461550020f9500a1034080300145001c00441e07210f103002207040360440f100e000304110541d9540d4100c650f455201002811907030307664000606000304c45401109121100094964054550140c5641c02002480d0626126210307035001c5282d007400110061007680003121030586402580c2d03100080e480040950030382e809801c03201921484100043e1408000f1080c507 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 640069307 1250 640068057 640068073
    0x606020f010f022118010c02070302180f1f0b040e0a0c030605150d0b0303030106110d0e150d1b2102030c30040501150e061809010e070305 61
    0x4001d0944914040b40d14400c0d10402a04050003400d021000400002c0c00d680c0c51300d60740c0d42543c00000c01d07070186450b4842d400c012556028a601103100b0065902c211007613039081d12800d0004c1080001140c044014400c001c011500c0c603c034031003005014144241c0a48801030301c46030015100d801c81e501c00c20904802c00c00b032020884260058000305000f07881d0404c1014a03100004603092050301c4039a80004000030f665048140c00d41005010030030107800c60342e90356950b440c010000d034202c940204540c00fa0000c0745602e14810102010514801488526440581e19156085501205116251699600c0030001031030780411151030f0051103031204044041c40d42e0303034444441c51449a0ba01d100f4030400402c80b400102c41e0903101c100504051600b0346444030154004a5031318241d103901440211800c201c20003605401426032402c0c06458080000d41c3c40ca032480b403081041d01e103507521002030200c0c11004002000100d6116845200100d048004082014103181c00b540043d600c5801c00b0071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 640070557 1250 640069307 640069333
    0xa02010b0f100807030b03150f06012a030311040806150306010f051522030f06110a200c210106320609090f07020f01020310051c06060602 61
    0x924000300340240c1d11041c020b41d414600800e540310041c203040a05036501c41c21806518100900b00030709000501d80e525a0070300f41c110300b420490840d11f0900040c0c0001055080110307a001000480c244030300200c100d01d02c2654241c01074580c04500d0516030000b88000a00b04208200240c01041d04520000051001800b45818900b050300855502c0708010010080c603100c1ca4144a807100c0b080c0c002c40e403201e0700091784070b4152240040c034451016a01750080244002c441c070802d0f43c0c4e8841e400810424040204e46202030040008210208101c540e0480e00c43c041000c00b0f070f940762036a03019104800007200c0000e1101a03180c013141046c200c14204510502000d06c0b0340b03006410070000c41d45103048080d080d0044d0030480191006440035080071100706807101c06c02d558480000034107200f4075207492208400d03040c07422940c1500511403880115035203601842128080c0c0c0000c0c000070300e081d01300801c0c09907002c2003480c5160b09851a03111303c4040f03007040c0706000c050729040e4060200c103204070b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 640071807 1250 640070557 640070569
    0x190c030e031b0913060c09061d0d02012f01090b011a03010303050a090e131509080412020607060e03090a0b03010f090b0f0409110123030a020705030f0a02010b 70
    0x2020140240c1c00002c0303a03064200c00d0640820b05010495025030141d03113494594a04812405005101c41d0904a01c00e00c1c1a070005c01c00c105944055440c8840031200e644200002075084841c1904104102c91130b8002d9403061801c1c1581d5031000001440700d82e03410a4004d018091012210044d035501d0001c1e01c20454103140d46401071030400b030800d540310b1801605405520040c840102030040c00102050040d0041071b0000040054100d41d070002e180c5400202c210b40384240c4119040002141e0a20054410303201d00c1c00030613003210304a4205401c00d803181c0b04103040c14000340c1c1c2c0302c08240902c84c00902c45005000c519040c60b40030710348a5444906225001100b0b40140c01d4040007480188040c1001507040c400701c9010300c03404103031000321001044040c000c0d001c0e03141d041824800820103101c544104540d9148081c6e0740c0c555500041d5910086001c80c1c0b100c44101841d0810219094442940150507160b015406503858141000c2105040b940195801d5015075183c03000301525280c05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 640073057 1250 640071807 640071827
    0x1090c030f0b0f04050916030309090c1806050c010e070924150c02010c1406041704060203120a0222091b052a0f0c040b01050405010c0f08190c03 64
    0x41c880074030501d1094000594280034900d45180075641e540001024100c08001244001000202802c4000e80b641801803000300e01d80298800d070350402e0b1300310164910404081451a8805209000b0a030810a00325116800300116a24664840c0c120380c07056482070003907100070840c50100144030909013075522464400c0b00156a0500c81402080060840c2d80d0034a804c03502180c070f000d5050400e40d10050710180c00307108015141034183d44101c2490f0780006081341c02180160311210404800713201d00e2585108502588e001600113001c040800d104502100f500101a4100981004268408031001d683c03800e8002000c414610b404010103403051050714459400c90f920004020301c0700602031710070301c56411940d000045804444030701d100c82c121300100c620080070aa50000c8100746440e42d5428000c081035101d249000541c0006601a0b81220116070041e140d01200c2e01c42c68640d8081c2050412059480c10810002030440c143d80f8916410740940031b80707840c80b0500700c038200180b0309519 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 640074307 1250 640073057 640073081
    0x170f0d020118030309241d061303180b030c1201060e06190306080d0309020906060a090608090a06020714241504090804060c0b0a09080a03051e01090c03 67
    0x24000031048489200c02c1070380d04407505401c0110740c255103468094503414040307503980a4802d610001c85605081034002c2c0500301036072000d69074603a440a114030340b00c2800360742d1009400b0041c030b01d9000080c0103c1d005041038030400c000601550303a60a51031a17940c022102d84602c0a400548040d407a404490440e001d40035034030f8901520b1141c1c00200f1001c0c49011440c0b04000701e1814074402a43c0b0039040f94000d821003505446444151210117000303003034203610491081d4000386c0090f00f03070f04200301034038012400c40e80c0302e284880c503102003501c820341d0160051080b40070f820500004161680001e0036035070f1040c1031040d100d42c802c1c882142440501000d0320000d03669840d000f4070307400c0702d0b07410f45800c204001030641042d141c40000070010300900000902020010400040c442c1d00208803040d502c3c040c04000900d540c899031b0070004c45d1400200103050f04400d1040d114514401c0c0d004036800b00c01c0007401030f00703141e0281940100c180245d01a8103007a1b12130f0b00401c403496042c0560008055 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 640075557 1250 640074307 640074311
    0x11040606081b0f0304020d02120a0602091c11010c170c0304180207030c150204090608061006050331320c0105070b0417070506040219150f09170f0d0201 67
    0xd80603543e550610026001920850344000401e0940d919008488610003401d0102c41c8940144d00d09240a5080412098800d101c4100150448802c0703620341408a58041c4100240110307420054588505902c01a10101700400c04002c103040701400030841e4040c804001c54803a860941400094030300e036803111000301d00510403900001d401084030040150302c0500304982000310803042009006a074002c0c441c0b079050080018030080c002c00c0c1d19000c3d04418000c40702d143c0e1650810381d410b00c420744818031030364101a900448655460400310042c403c81130b07241000c8001d91124487c03214804000f542e1510f142c10b08080c1c0481d00360741c0c0c04688a030000584400030780400003074140d000c0c480303000d8605031350070001808000e10f07503d071a0300d110300f2917450b151586024281560f561070100d40c202e000301c07408807461001c0c0e0350b601140700854801d030341c00b10744540b0a200300303e405403840d290000c00d01c410340c070b004900c042804298440082c010402000f00d0f000301700440d440d20004443c11010343e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 640076807 1250 640075557 640075567
    0xb09010918061127040c090e0c0c010f0f0c0315080703150f020a0513140a091d03041409130302070b031008010507092903060d11040606081b 62
    0xc2807924403034500c640c00030750000e4003031006900c0f80040e108a2403812407144980c0c00c10742010a4610441e181c81c0e4099600300000c2c1000c040940310314034940640c100d00e02c80321000400e9012070078002c00c0f0b18405400040342a80005480d241070703400c40f144004002d9200c980c0c00362141e5052061040b1660854100382a00d0300c0c01404649405890102a020307041c4401a504000c4850f040501c0c01d9200000c06c41d07403114080c1e001012600109910340861401c4040015030400201d0102e541e8503004044400b030910b041da8800c020310306107015400c1080551000750704231f041400a80000c01000c41d24803c0d6011040800546080007410035030288a41c0c0f501102103640022041c0c20784080c0c1c000250349844031001e00103541c1076940802d0b05982010108028142d00190300340c100c442034542c88a80314018001c0d87c18042c0071001b200b01c1804148002129440c1150080440034003503072031500c40d905c0c5980400c0c2501ea00390400004075041005010342419030742d46000f04030900c041014204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 640078057 1250 640076807 640076831
    0x5091504020609010c050a08280f05041403010b0a0312110307080405010c05030f0d1a040c0c0308061c0f030e011b0f02270103030e03031c021b100b090109 68
    0x35002e0b1000f154104420026000f003001410014038104503000711850307485801401c00d0f05070342298074000340d856a00b01c2c4140224580550329641c03200030981c43d0b260a1508105242c84200d104c004ca40b40d2541d240c030005034440c1c591098940c003540c003a20f0716248070b00d16041d01901d001038905041145030710421000020505110039036094480174030b0001c01030b911606120745940182c158440c0c1c0303683c1c006429625010643e0007000e140380000280c00d20791030007404000440d01500e54403004a888001c020300024410104a940010b0090010b081005d641c400741303c1ca0b0000100440e002451608841c06141d00070610340d41c2c0380804d1138100c0c20794070f2506612800105509008040c030700e18000340e4046540d2102d040650750400032a2444120500341e4100090000707110680100d42e000c400084113041c080102d0346a140c50120000c0c03000b5003120600b000b5404000c0e003112140c0740c140c408050080074000700c0714400d4803c07004200002c14000301304000f8410707030081850034a40b008810103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 640079307 1250 640078057 640078069
    0x70c23060319241d060f030f0618070b030f0a0b04020f1b011109100302030a020d052706070f0e0d020d05070906050603010302090403051803010c050a1709030405131803030509150402 80
    0x1c0f000046c0c90240080380107501081c50710002c1c0c212607540f03001d580b081015038118140c600b032080040a04840b1190341d900703c00d044901c4192041d40d10030030140b0005484100e2a040300d40044005400103140500601c26080240c010b0a41300742204075207142c01113111401d00400312213880101c1d41034075046001c03000922540a030100c07401810b80100000f84080c0d46541a51102e145070001400b07036280c446441003c40b150301a5074514808100c004140510000820501c01c0d07200340c460110140d444841518021103110919030307c00074801070303403005854170074130031011500c1a00141b110905041e1028156041303a048140186418801000907170790704042643c005402d420030a6840700020303440031030a800341c81c0194142d82040611020580d00c000101143c00465440003129030445645c0079802c2cdd01078400c59050750045c40180072610303040711031343c01d01140d02c0d0b00055800580170114181c0c81c044941500400da0b00d40801602c100140706010000c40c80300d0f04810729290507800180 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 640080557 1250 640079307 640079311
    0x90105010c0f0804093e0406140c070803040509070c0302070509060402130303020609120408120912010c050403030e0f010906051606050a02070c23060319241d 70
    0x8004540599524180030b400300495001e00700d101400e00c038171100415565820100c00b061700710041c2d5403000c078031b481065145280002800080a01d8600b510f000030803206026040ca02c1c410402040150014400c01000760b800140f070302001940d11503141804003c8207841c0140100c0512581e180c014000907030200300c45056500840314107415490300c001040090041444443c1e43c110001d6020061580006110f0321a1851504a61040e4032009001d0698011407068002940c421088440449141406490b01040c09441c503c40c40036100003281c00d58440b045014045107000505005159028885140750340303003076881c83d4200024030002803071314980d07110302c5041003008101c0042001e003046400d1032032a0040818052420303c800704034000d40c0448002c880394098840c001407003009600488c002c408c56a00c41030240400d03201030103003991000b010b0071103264104008039010700b00740c07003000287c000c900d0305c22888802541c03400070103c0700344e0081400d035252100c00181110701c0c003100503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 640081807 1250 640080557 640080563
    0x5010e0c2826090c0f0d12020a0c240306062124050f0904050601090f1b0c140f0a081e043b15010c02060406050a0e090105010c 56
    0x4000380c0318004881154150b01c1da00d1030b841000d54600e5400c0004880d481c00b0718012800d9903030003005070302040811010881d00c06d070000c10400a0002040c10b41620f007025103014010b460f803007001c9903034961200d000ba030007841041405000c44496000da81071105444052800d00708441030400c80d0150906080058280741c0380c4c40c0302083c51725441aa00110f2180f58008001440210319620200b0702440c2d034080c0e40c0c050f020760340007030f411443c1201115000d90b030043c01400c9281d0a20302064060301100c0c0544820f151140e00740c40c0100b000f4038501e5801c2c9856596a0801007ca00d800416100182d015505541c0820000d0004917030100e4462456541300c0d6080c0e43c0c9180070030300c10113202d115221800c1d00e200040f800040c05617001c080c00e0007802c0c84500900203844521540b0b8050b140306507044540001c10800603000100d00c4541c09604081410140e06d1400e0720303800184541d0158000400040002c245002c186070421191001400b007100e503e40c031981080c00080464455260207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 640083057 1250 640081807 640081867
    0x9031002042301030207020a14010e04110a08100f0e0403030908031905060103050601081609030c0f18050c09060f12010308130602011806020703090b03040f2108011403030c1005010e0c 81
    0x7a000340e0300400410bc5210b0001e40180903e4090b5003022013240c12500003400412a40340004107800c889401c0c8c00300b078801e10b03142040c2d01c506258540d90310800c024006c07800d0546d80d80008000c101e040001e58450070865071014940c400300c5140c04241da00290410307046c5402c1a050182ca687c0013401954021040648501083c0f02550200c4504400b40e1002d041150b606a0200d00360840d030301d405040d51076101d0b80080e105070b40c0c03000c50308880e801c07281100e0011050015401030b141400040032084002d048490500107030744000803007d502a80200d44c0c4950001c2d0030405030f0010036448000340441d0008020f441114894404140c604502c001c1200707600080001c101070265850002605407010700c50345a251500c2c18000100c908d03072060712090aa85460941c000300c1c03048036611110181c0d01e00005905c5d04900c41e070303012000d918880d07150100703004c00c0e44d2210301040756a030007500303419020441f9490108080f04034000070300101c1d1130303110401c2110602141103501c2d1000c940c4901c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 640084307 1250 640083057 640083089
    0x6080912031b070b01050a05060a0e1e06161523091606080f1005060d0f06050d110406060e1e220c12060f090209031002042301030207020a 61
    0x40c2c040c4141504031000e00000007003254018401040b41d44c078180c60702640e1307000250751a101088281d0140302c0d006000074510700070040c0f45080801c506003804030351300c1c01c081d201c41b00e00300010800e400031070040d5074600c4013920701000e00010f43c0841e000300031b0b985010466043d4060309402c0c03d030f56108034404074190b4540455990305081011803840b009000700103d84a444100060120034241c1d1071608400d2201e02040c84450303810414005c07128018902da1a02d001282d0203005409501c5008a40e00d588010000e800e45a0001e040da2041c03042d010300042070418004c00c001c945d02904248204200001094083e4580141c0402c1800c1001d2105000e11582c900044a00100303000845480318150341c0c01c10480e40320b400c0710060b0081a100c290f41418419110821030b042403158810098119408020700c0001c0c0c2e00608100c0000390941d41c2040d0402d040005992096001e1504003848220a000d44184203c005180c0502481c007507140c12990303000515404c0e65400f40ca0b07007180c55000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 640085557 1250 640084307 640084321
    0xe06070215040e07050c100204230409061505030f03070827030d120b03060f0112030e03060403090e01080c06040e060103091b0f050d0f030807090b0408060601090608091203 76
    0x2064600070b1091400c40d443d980341070b041c02041c5070000e07100c1d199584210303825000d10310454002c0c0c40030b031544941203504810610103620101e00341d520989800a5440004102280c51780c0528071108900304001d40071545040300b41481e00ca6900c4806440b80c10501601e4002002003003221040e001e10b408602030b43c880c0034120f80304d5488913514550325115000269a107640c02c003424101c1243c014804006201d05034091584400c0112690b0700b007541c1d001c00502c08161174008004490740a40750141801c5403d03008a4541001503d099000c218150f01c10408138034144215400351894102030120340d6040d4011808a008501649952000134400038602e80d00c40c2c2d02c01100d007500124410180702000945104100c081c1c055959a1240100c0114890801074840c84950b50720402c0400f00350304644046501e440040c1c0368000b0418100b1000603510000d9021340040c20340b940241010b4180000050a446002c1d07201e001885844002c010f58142c01090040c1d8100381c208a103640c07075541d90 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 640086807 1250 640085557 640085599
    0x1a04050313031109060d0b0103121101051509100f0510030b1c020307090e1507030b09010305060a1505180910090b180309030d18030f0605160e060702 66
    0x10780041c142440900000090111044600088000503641d408071070b10303008113121a003601028050800341c069001000014010545400c101c202032a240144403418140e450a481c415103040092110841c040c80040c94291511a0805102041c07502640c1c07410a2440c41e00d469071203058860203440c08800030715401390b00001e085240c01042ca00c0520300c0e80c031101e41c074902070300803da0180c441d2100100f084905031140064449109008210540e81100c0d420200b260003050b00f41016215003085143c2d40740d0351401400b031481400a000e1074a0701c01e1b030400844405146211803c0c009803810405070f149e8090001c07500039580900c20540d80d40c480104e107407540350001458220328001c2e000007884003c4111901030100c00c1c0b000040b06e204d07102c9940d940c0c041c0141e0307194150008110481c115000b01203a07402d0300a030400000c0410342c0c83e01c03004c8100c520300000b0384000340c5800c100204841e0f03445c0325011204040c107250980381030241c0410014010514028000d05519102d416400d21032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 640088057 1250 640086807 640086817
    0x204050a0b0a06052b331a090301050c031e06010c020103090302011104180b0a0609120c050d0f060c1103030a021c090302030a09060c02030c220e010e15041a040503 72
    0x50100030000c5c400d2010800003d020808040400c0c40401101c0d50b1400468070710491a15004404c2154403400c10b42001514000c41d101413200c4002080110700549003070245c10b12410501d0b000540341c4c03510304242d094908038a43c40791105051a01044001da070001c5c402a40d280e02803800080405151406a004081c1d451301245030340804100014081d12034a400c04403800c3e4004180001441c0c5824070200c07a50750700480020600c040010300107200760b420030364a07a41c01144003003000c036602c03008501d40080f9a10141c0d11030702000800001e0190900580054602500d8605c2d12200070080981c0c49020141c1001c1200b500003c4031302140402c100c0503021f14200d81410403001d086451301075580e501c82900c52010884981c1c001494a002e24003005a10b0380180142c25241c052500308607403c07084007100ca9800e45100200c2c01001d403030348200b080d026212000062886801020589042c0701030901815020b4080d0401c00083c90b42048528500d0050160840c0d6843c4c034a003003401d500034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 640089307 1250 640088057 640088107
    0x1020903160f091401030224030708010f1203020c1212030a020d0b011103042c1303030e011107060509070e0f0106090909030c02010e1c030c0204050a0b0a0605 70
    0x340c107032480c81403050081031500302c55200c0b49400703800e81d4803820030064401c45000b41c0001c842910040000d82018806560407c40c51411044c8090943c03c017000160400d40701d0310005140c000c018004003286010300c034081c0401d41c030886e80302d271041d0b03800030354514000d80824065a01c41c4410307480140c08002208100707562002c3d5030b41f24074003244800000e4204201d009520b60074a0101142d55000300b08011014402c0300203140b501d420244510604000c45185c8807102000c1804451a5540e1440307240c0036400c4401408104c20084c200281075a002803144022645002d0441100c1c1005004072a09140e0105021682ea5603121590303003400303a6984101140a02c1c0410407a079041d0310002141030381c6c100c0cbc072000001600c80c0d41041c02c4800c003040040104001c00540405517010f80c0b8015440300005142d07070100b06603629104c1c0400d00c40c480490100d01b50503058800c52402c0d008a03a841418810100100045840002c4000301705100741c01c28440000760a501c5500c00540405412103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 640090557 1250 640089307 640089313
    0x3150a09020a2f0a12090515130506031005041a060a12180807350c0111180d15050103140c09070f050d0e06010308030720030f0c01020903 61
    0x14103a0020744407903040c0326042c2070f00386003601d00000280d509401d0b19080b4034100081c0754140c1c00380d0f03030307180300c90401d08aa00c24420800c80000d016900d012074a58080040b400b131380e0701c6c0c0740034491840380d400701d07500640d100b01418810080c0005448107080121801250007003410b100b031040c40d0101541d1003044ea80c1020b030000e038021032550030044200c4400460380007040654001000d40b034105080c190000d003405c1c002c211500c013090458011450b0750f181c129021a40112008000e00c01c001c1009641d0200c0001042600408000303104002100b800201010b2800e04003503025074070080c040c01070900c28007030300d06a00c040c44600441035403021001402000556140c4c240361010365418082104640300303140c441c0d2400d0074a2a1024000c8003940c40755040102400c07000d46040c0c0003070440c0c606165884806124484d004c00600d4000c6002c0c2640c6640c80c1400240108049209012014050240c044280307070420004112400039007115899926103a040350340d507002e84503a0519590501c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 640091807 1250 640090557 640090567
    0xc0d0e010f0203090d05040518071707030608010b03070f051002121303060b0f01090e13050106151103070f0f02270a05070e24191206120803150a0902 66
    0xa0050780c021800b80d04210111060519100703001c480504c154040c0796008043e90980c080346140c2715101c0b03604a101400d00c140305003002c21078030303942c084c0440e08000061340324401004406004c2c8604d0055000540152801c5802c150030300703109150b80c0c8102c5000c0c1840c03544c001c49803032017800402d40e484145075610b075481e4074450342c1d1003506040c2d003c01e0344c1031352401004241500c1c098207141000c0c1e5040e154815000d02d00146a500c010000301200e4080d403000510382c0000300d00780324038005840040c80f04401540e40880062a260f46105500400d0b4410051000410f0141a00320704580d80124015050480380c4040345010b0100d5010f06204403800c0404c0e0100922404501d1090740705003810412503a465608480b0500c0002d12186c1020001804104000e900c2c04448841404022501e203030403070800300310f00303011000b2a03d540010104130000341603910a010b408014010017901440c030003004e480c0c0348018807000c0c0400c1070616500c600d12009496079038400000b0b00030180c0442d164 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 640093057 1250 640091807 640091831
    0x130b1002070e01090606080a0509010b0d2303070213180804060c030e0108010513090203010b210607020a1703090705100201021206030303090307080309030c190201170603060c0d0e01 80
    0x307001540140011603000800119101d0041e1160078115980c69881c0c00300d03511424510700041c20044c0020001d95251464803009480c0c02242c903c0700351007401c0700d961031000101044042450020703051010340040101401598924040541000d068000020382c0c4d4104116800800000c000040550201040c009203150b0070680a81503107000741c135021840c0410030b00445200c5024080c0c3c41e0302650803404034004100f954040944180701800000d0980034600002d506009018559006040f40c1d558409501d03800f480b4a5070014100c1c0001d18180f00703281d503840c0c0c0c084034004040c4180c081c04400120210030401000006000140c002c909051907502c0c028040d40c020801520051980408903104d82000821248100b0351000510f0814010745c0d10b4031050751029280d03006610045c0318508812800703001c2004458114070b484061000b40f0f00c00584045400300180c10349030180b20801a041d02c0200d070096006510034040c3e507466440030381e060000e04d00000300c144150700e010109221 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 640094307 1250 640093057 640093063
    0xb0d06050720030a030f1806060807060305060f0108190f27110415080111120703051501050a0201060305010203090307031407050a020405040602090603190c1706130b1002 75
    0x1601003a968070074a002d410185040d03507010b80e030402c103850380104005104640b00340e04c0700980c07418400b40801c158211800e086514594003000ba904695560000c01268808020082c01403643e03050502ca02e242c0800000c10810000603058180505d601c0010b9041c424a018074114804021080000c00640d01102000300620b040310104842030240208a2403e480c0c82d030003519500407516004400700e8424030018011440800d0242003810f40003152010083c02200f40b106e0b113860303815480b03050f00601c0464500000c0d1224007458a80410302002c40340c051440726200034203003050380d60707210002001c0b40140155400a022944007205200306100c01000500b0300d240039544081c18030f0080031035030f8414421084014001e0b40074600e840014145504101c0d4003e000b200010300700000d034008240d459108a6003144444004002800b0511940c03042d041c0103140d0345458100d6800030300e4031260740480545020711401d04040718034028480398010303034801c00e80034281e280b0300030300c412000c3c0d5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 640095557 1250 640094307 640094311
    0x603080c2a0d380a050a0b0f210304031a0708010e0109110d020a23210903090301091a1609060f020f12121620010b0d0605 54
    0x411801c000e1001d0415110915411804003001481d9040110780340c0e41d20079110008000404084805034400390518142e0940340d000b0302e8902c0c1c8003212902c3d00010304e50803950004c02840441d80740c988101410740340c2070b04508c40440b0582c0c45038011082c40c0c0e201c0721078160261301540e16102c002404820060a8820b44000c560340920320141500c2d6110305907000340e400d006403000016584010458948541c009500480140025501d40110003030810280da1205001c100800c0840d500c0d40345101d10000a00e01c940d078040c580a06010003020480c503540002940d440384e90480b100402c01401c000d100321009844018002c03c08000706262008900d1103145807c0e50000f00b070400580b01d1164044440300010041e0741d64102a0309210044c1c4864108940079030440c41048a96001c080e400c21034043c2c80f80640305a43c0d210388a0107080341c24004010081903044040038441c0a9841d000440e42035a40174180550300665000c081050043c80324102481c0d00020718117564091014641c4818 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 640096807 1250 640095557 640095583
    0x3040305070e04120f05091806090603011407050d0f020304060c17010305071802120702100b060c070e0c0d09060f0b030105090705040c020304050901080f010b10050f0d0603080c 78
    0x80101c0d686100e880300040d82160b001d00703a0105a0034580308540b2401d2070288400c580d09215041291903004510380c4485001c0c2c84050810b420203112503840c0903400c40d80d02032012030007805400d10b44c0340382c5410b80c00080c124100f070001c0420b4003070012341c1c25040101d480c48004001c43d140c5c030700b500307200e005030031b01d1940480403803481000742010481d080500740c1680d811800410f5818908420101d0084c40e0800f40841b10782d090102d81d01c075180a4810a0049400d94000d0100c40c0c0180d009104448290754014880c1ca000c0100440b0700c81c010601a08441e400c0101011a50b201c070354980051003040300032280e11703140001c084100711031a440748055410b02d050400c4803c41c03280516007200c1040e40e84584035170144004002500e0240c00c003010031111881500e04142d076420209110810030303000005140c210350a500b4041c07500f40b04d0440c02d001c0450326040ea0034200c035009003061040c2c81082c0c00c41030000030300c0d8406400540010004583c859081d6070390702c400c0c040c05900d58010303001c40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 640098057 1250 640096807 640096813
    0x30215101e15140a05090d061406010906091404020306120f030304150501030809120f0d0e1f0909020702060f0403060b09090705100c0501090f0f110405100308220803040305 76
    0x102c2440c81160908805408464440d190180614080c0c130f280d0822000d8541c0208840010780004a50b40201c0146c1d07045000c010300c0c2801d0000025101c8a51a0081c50412004013410009140e100c145c110070700c2c00c1518016940d07200d20021500a03e0134000d1464a0700c110504180d040c4030010045104074090b01d0b10074410702c510741d47c080681e8000c0c800a0000042030200c071076146001a10840c2d041700c100c046844501020243c40e04028504e04404045078685400115a04102040b0020100d640c1c42c4883c0e000d03010600549800c13030900800110740c8e8082908011920f440080703c0300d00c01c00c0d041c101c0e121681c030301e080c1001c0c4c035202c0c038220f010390140008551103030740028205040e0303100103201b034202051a49044900001a00c41580d40b59290076044012502c2c1c0e485803c80079004844422400f95241041c0314804602171503540200e2900040200c4031030500030000940e58031044403581c0790408238414071011068500c201401c0205440044c841c0300c00802441200d100302c00f6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 640099307 1250 640098057 640098089
    0x3020f0f030a1a0a0b011215080633090412020307061a010314010f140301150b09010206010f03031e11010509011e060b041703040b0a020a031b030215101e 68
    0x280d078041c0c0b10550f905d503010610004601400c0b90160304400721010108485a484c15075030582249055402c6d01c4c0d0221a03242c50700e1041904030056000c050082c1054119980c00191202007510140c0041010b004502c01c40072013074801e4424411510781e250484070910425004140030039020f102c44914134040ba11b801404019220301d0052181280c5440445807900c42c502806080d40440011140344c0c90355031150940413040d40d40d16204041c103c0c2c00301890301c4a00c05000a458064180c12400c01280c8042d010000030740c0c08611108010041d4400380300c40000345200ba5550a2850179145d060350a213030401c40000701c158050120507925101d10544014481154021600c49004451140c0004c110030b2110300200c52a0250300c405000441e8641503890f40d05000a8021840d480010703040b0b8402c8005055000c0800d8014817050007901066550039507000e59111001d454040c003102c91140056500d020b01406c0301700501015502c00001480d42400d0202c411403801032109007001082 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 640100557 1250 640099307 640099321
    0x1404050607030c031107091e090b0f0a0209120109030e0303040e010515070f030e090a0b1f0e090109050105040f0e030324130501080106060c051902040b04020711040609021303020f0f030a1a 83
    0x1460000d10f410ac4003217405512940c003907105654000302200641502080382d040d1035281c0d0503041007100c590300c00001e4403e00e00d03e0010508003007003800c42c1c03003641b007407000b4810f0202050605044402c01c40e5046500300c0c00c002035170341c1030040c40406429507001c0a01d480034180c101a44058490044440d0300e440e42e03c5c4c2010350100e5042c40045a082203400c032503181c480d22a10030300e00703c485503402c0045803402c0303d40004245150907000100b241e92100c0c010000307800c04d8080c0070744800041509100350703e85a01c0d0560340e400000c103110801090701119588020800300b40c00d40400020304180b00c0d040300b06c807000c005050288034a169640c81c0c814001080c0f445120f905240c1940200904141884060610221246a44107a03403042c0c0d5180d0424541d40c0d544020406144a580b09000203074480c010842282c109034412000c040c010000c490340da61b00c03c9010003d60b40d0440340c0307681c0f8034008000720750981100c0001c86e40501c04c40708424144440800c803d01a0b00c1c0d0201c40c00c030030b950703841 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 640101807 1250 640100557 640100561
    0xb0318010e0d0503181c030b0d1104050a06090f020c0c0d02060702012a0f050c040501030308011701110a082406040b030a020c0a0809011404050607030c031107091e 72
    0x100000070785400c1122100716407441000250341100901c03690b00b842d02c54080140c0c0c00c11950580481a02004030703101c0c901e0b91380600844850034404c07600b52601d00c134252103031a045081c4070708451084c0c0c1c3e501d0000341186041d0b40513201070000d03100c0800c621042c2c004100000d6000030174215007031280144501440c40d1003041d402405501421081c280b0f8800c3d4015502c0301c000b02071494507208102440b118201483c0c0400c2c02d01806030003c00800f11003414202d0819020035642c80c0107506050040c800302e03800050203811160700842c211180c180014160b401881c1a8415800c654000100312000d00e0b842100c05004200600c170000c00d000802000300401c40c01444420341212092200704400d094940c091a03200c035204c1c4003d0301d0031150078030880c202504603408071801100030608010950780070b907015150000c101d5500c1d1034581041c00141d868003540800400f00030b0081196410503104240d0192448040c5040b00d4509440700c500c82e000e0035500a00d1208844000c13088c1101c0b080c98 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 640103057 1250 640101807 640101821
    0x3090f051203040306090c1212030f0c1d0f13050f010e07020d08180607030507030e0d1d0f060c0a120503070e012f0303010e15150706090602040b031801 67
    0xa01d008500d020b01e56642c260140040c240156054003190b84000703210b1801408500041d8030030a20500021075a0300060115410044d000001c28545080c540c14250402c4045249000000d10100042c0d01d0100040740d010640c80310981010345455100060000d54212030702840c100c08202e074403070b030b250103151807100d80444401d00141e01c12411020307014058458203800101654907020501c02543c200d624000c8140c9000002070780e038100300002150b1501c100d040e0012980080c0ec4000050701d802444980310440e250051003460034800c4140c0c0e240b8040034518000a06466180d0307060040451301c8001420b030907984107800030010310019106d1422a0300c43c1285448401c4090fa40000440d521840103452122844144006981e260340b201a46401d83d2000c0c001107070380798184000000041c401030040720112288001c01c1280d40c1c2d400b4103c4001180455280e502c40420303040c20409000c0c0b800c40601040c1c40084c0c00f1500c0c2c110310b0002c1d4802c0d0b041c003104001861040b0003403408c903014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 640104307 1250 640103057 640103089
    0x41a13060f08010e09160b191b02190e070207060e09010e011809020405090f0f03030412080c041d010302010e1228060e1c080408030105010e060d050403090f05 70
    0x150b20050254102256506410400483c02c58401100804840ea42e1030f60a4000c2c0300c1c1d2960200301c04120310161402e60461070fa0501d000344c007103541c0d0400400819041e1038004e00c103204200700d41060200040c0c85000520308441310040505204d08003a4840d0b406000c0d1900061650601d400d00e4280000480d0494446440a040c070f686010082e400040103200011042911076000c640581d0300d80c017560703001e5030760540a0203030791101307008452505050344450304003a0028420400459006006102500c03500d050840d12592403040340030b481d2007075800505402c14408518034020440041c0349050301e20070f0700c0384030614145c4e4041095940d0100707014411030340425690b1192880340703a000301e0560000e004d1401d46038295503030340064420f07070a01d02c082507102c0383d000802480007d01c0c03c412a082c0e0308054001d400c180e100c407000c51005004a03070502c41c605441c0c02027900d4020460386860900b1100b0812030409140007407201c81c07644034135209540c5c02a070100d494036002c849440c580341 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 640105557 1250 640104307 640104317
    0xb030f0c030c0304030e010c05070303051b06150418120306090e0c1003180803090a111005030105100c0506070914011b0623090105041a06010e011103041a13060f 71
    0x24550b17908441c0b0103411191141005808488000041c0c410441d280c003070340c42626540c0d111090003805c8180d007080c01c4500c0c00e1951100c400e0011113a00d02044e20104841601d010440c80b00010f9100c0c0303840846003000b8400650341880300c0348258154131800c1510030b40c20007402000701d035402d426079440c490000b1517030104078110351000d214000e0340040480000c9962000301c0e420f41d41c0f00c040140e0000c681c0c04915820980001003085004a02d00d202c511044410f40b01010303030b0380c000600c0d5000c1405440d00601101c01d003000075500071a136040c0c01d41d622030112a43c614103203e005040d241c40d807054016000d54034001c034040d0741c0030300c5a4141501c2c540755918011600341c3c1311407010b0614500c0c0140310b0400c5000095800b100d1122141c81089080000304032410240362082c7d2410b001030080400b4407010040c480c0076a44103201d4031040d8424a082407002000180803800e5103e1603000f55050b04d10b4000c0400c12035901e00c0582a4011f001c030111300d40c1e0355910030580d0252611010351000030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 640106807 1250 640105557 640105561
    0x90d0c020f10021903030e0c0406030c09020a0e060d1409061b25050715180905070e06030106180801091e050705030102030f04020f1e060d0b0a0b030f0c030c03 70
    0x1040c601c1158036885490710403108280182060012134803c90760041d000603486d201e45c03800c400c104000f42d02c000d81003074904001040c65a00c6d442e0790b2459034000e10080940015400c0070300e512600c08011860f00c01015140c0d54000005a240140054812640308062060001c0c2441001103000d51050503021045c1001003054000b85005a001d8011010300104070243c03e41c4080303622000703081c0c240c0319000401c0a00d052065062010201da100d160800c400c80da44030003c2906800058102c5803001c4011425480710101030720319415903004a42c12101c040000122103501058210903100000c807083c0f182e507196411942a81c91000e4058a46003503c94504c5c1044001000140c00f2401740c42966a020303124000242680c0c415102861501d1400301440709615000d141118021021500800d0b441c03201d1580070b4184154040e164400c01300401c109219030400d4002c818010702c000e001c0380c00140c48050034002e5402c152021000c0901c2030000444c90800c010440740541131405a5904507 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 640107913 1106 640106807 640106809
    0x80c040e0a1514090604020607020d020d06050c030a0c110a170f030426090a2102060f07061803020a0f030c06020c0c040f150b1608040e090d0c020f 65
    0x29410081c00c6c000143e80340d800300e417460ba60503900707580315056500000d00410011800030380024249000c200d4a4000c5200840c8100e52028080188034501802110554040b0403d0240c5a03c02c48d52400450518015418006040041035240845000c1068400d8100fa141220f260080b88160700c07903030481c01c40905516400c00103103824000ca080000b0143d031080d01c0703440440c10802804803003c0c1c0080c2e01c100d00c065005000c8565480425521204960104005030b900514010b141340109003803080d002e5025402d58024440000300741c8034011107205181c3d0840500000da01d1840000741345001411964108002501d03410710403000b8401501d01c1502da504095141400c05180b43e540c01d20210151850042196203814076152201480c502c1035034064482140800d0005181e010082200d00c1891050242c0d402c0c81d91400c0d0541d403405820303e00961200840101ca001 = true := by decide +kernel

theorem cover : BRFrame.Cov 639928057 640107913 := by
  have h0 := BRFrame.cov_init 639928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 639928057 ≤ n) (h2 : n < 640107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
