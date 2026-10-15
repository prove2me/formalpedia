-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5269
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:18:23.331694+00:00
-- url     : https://prove2.me/submissions/49e9af2b-95ef-46a7-8fc8-24ca6cbf5c31

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 947482014 ≤ n < 947661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 947483264 1250 947482014 947482021
    0x43032105100602060412180b0f0306011b050c06030910020315030c0904110d06090b041b0807051810080708010507090b120f0c2115040e060c0903010209060a0305 71
    0x46281c00258400002c0d03503c28418031000810b20360540140442a15014120309a1350030490310030342040d031208441200029121501e05c0c1440c0c010761280b182030b02c408845030560ba0324003210f600e03031303042c0504690484002c0c01c801e498280000d40d04100135101320307000c005101e9034a900300d80c02664046c01c44050343e0813102c1141028030220b16142800c440708402e501d01350300c5102030a001c943c4d14510944510141f082002026840120040c1c0c1040ca18403444c5094a408282001c800b0304440d000e400941c03001602040004122054940282c130310000502c0143c400c0038100005002c0780d40e40000c100020070604802c0280b00018460880086442d041c4008058245a4250466420200200b1a40c9003484910149642114150354100c0b0141d0b00d40d0050443c0d4011501040003400310a8074900d80d07441035600081c09196282c5c4003403c001c5441007040100ea9846c0340e120401c0c0c01450000305004400400b1b020200c0c0d000d40094074000715400059016884601980c000c00d50740d5050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 947484514 1250 947483264 947483281
    0xd02041508160b09090106050d090b010b07260a1d061303030305010819030507020102011409010c1b020901030b10050411030906090708061303031d010243032105 71
    0x44100404a5400c0c3c1480c003846000402c001e440c0500030076050000009510311105956403002c0003003600209482015610380351002680d81c00207005880c000c84508082011341c040e01e00c4043c041a8150b401490300c960108151031100f085400104c100b031020f10010510f485420080c40116090700c0b00b41d00d0310f03041d460041c046980c180c00034243e607405001340c2804803035202411300c1c89503050b09015442d00707282e1004130b000d01000002c803c9803164071014408880e02c15008545c04041c1d5440d42500f150390360140c48a2050300c0f079000f0b540310280f000100302180c00499101c0c2c1004a00e01c04441c19a00d510100e02a900366150050b5201c2000003040301c00d04090184941240792000907021036440e040301203540c3c01c3c016110f4a5886144200f45040500030360000121603500002c5085d8406200603c41c001c0d084200696581c880e050381c03e070950350b000601101113485038226581c0a04103d200d0b40701c5440c0d902d60840501a140f00c0c0b4420000f50714040e1814103840c2c02e404a49032524440f03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 947485764 1250 947484514 947484553
    0x141f1d0906150d06050903090a031103240103060b031507020a120c020d0b060105040305010f06030c240804030e06220b0c031903062d050907020c0d02041508 69
    0x9080c0d81d00d0300c54440e0502c41c0d4444075030105050300140702080588400505a06522424803620307442407200e01c0c00010400ca0320269014210210107840700a80b030f200140380c0e0800000b101070b104691420060002840950055800041c040d040711100c0c112198001e504000c180d9000000d81d0101c1440810840140c29030012a500d6151101030950598082110311b42c43e020002e014100203400039880381d12070000e9400864001000b0300030401180d03024001850326001c26a81d04031216808215140328024051040d811102c0d02c01e407102d034070002219815005003089040000307032080c1c20300c10344d20300c00940812040d0039842140d0311260321806080c0d80d0254401d0885070000d004161094601006417408460002440c606070380b260710085004140b16081302c1c00d12010054031000da287c074045942e80509104401d644c4a175100d0080002c10501150044010b91100241040d54100b210398401138500c0500f01090417001d210b1280e0380d140b6180c2100d41960300002c4054213000d41c800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 947487014 1250 947485764 947485771
    0xc12010501031803030e0f030403030c051b030d2a0b0601080105030c010507021e10050c0712020a03110d140a1a01031a041b0608040312141f1d0906 65
    0x804000074103061080c00e2104200f10000340178155554504070a124040c809a61004880030940c0da03910384914000d0064402441e0664051059016170500703d040d50600031242c10000b001841018104441101d80d400790f140024290001d642c082c6490304000c6490844580c0314080401e00c61038400001441110140d021500c00d511414103240341d42d8104c1c08841e08283c0644603011070381480d480d9440500000000780e80c11a15110b80024a1540240070f450442c0e9100103565006544004607818504503a10196008015560400020712520785140504401511324a4492019100c0b151a006a041d82c460380b50000000541008805c0468100000030307200d11410755411501d51012102c07105680f81402c1000d00e0124003030003500e45c961540748484c0e40000c02615100c0703100074241c0c002035401314041401701190102c00c1d0180d004002c0700c0c07500114007000d03594950320f004d1f080882d000c0101c2405500c07040c0101c2c3c1072400013450151400c200c0c40d0070410b414016529894840001e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 947488264 1250 947487014 947487017
    0x614090414195a0c05031207120f120903050d060b1806030402120703061b0503090d030209040204030605010b070b0619090b01030609050415060f0e13080f030c12010501 74
    0x1101c2a8070243c41641d10341d41c40340301106000841803850200a00810440f50b0201000f00f6446074510410111030b04203c00d48070254152411224800702c8107400780118080100001c14401c510030300184640e81d242100e4a82d407406c42d49a03056600c284086942061007034001030310000700401d090450b4000d80005101420303c0368642054541034602004100d01d803144215000800300d000d66aa88103418052620603003994002030381ea28110004040400c202c102240c544212580d280d0702030000d480c8245000340c00307401c1c0b002c10124110001e41c0a100501c0d8096070901001c00822910310805010300041c8031843e46c1c0da607250425802d214002000c0d24420b11400e40b01180829110071980308450481c00c010610301450300040e40900150341125a03a41c0c58103007080b0500c042028010540c00060000b000720320748545100b000303d5018001c089100004c0c030302051141c1c4001c480300d0300580c00391407600d04041035080400c685078001e035083c0003105004248084039842880d12103005207001d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 947489514 1250 947488264 947488313
    0x3030e060a02070b0c2407030b010e010c020108040816080310090606050a032003090a03181d1003060e0f0706051e030a060f1701050109061409041419 66
    0x103800d00942d0f0b420180261500c900d4041901c0280340d40421084020900090510404101010ba84400714108886600000b400c145060203030b9402203202000440781a03407150076a501c0d40d0010340f0a03000c040c9c012a41038604104072600544140320041d00c4d24812114039580b4106044850b035800859000000528548841081820f41280480301a0560340c14046024903c400302800d01e0144a40c1030034965100000f00f00d002c1e9408244000f006203c0d403184000301c400201000b010301e442d0b001c1c0c0110509201c0341c00200e00c1c4102141039021051001c0c2401540c1c43c1c0c3e1ba2481034a00c4c41c0540c14642d48519410388002000340114005051149031081c02c10032852801c11000155001d464003055000000c20300321001600944068041186c6100b5481d07981d07414003039140b01c017500a9005510b090000f19249a250081c0001c88032070500346881c60b0351080c10400c50a8010b00b04407442100041200c5101100b40256410030a00181400120001d0706019006c10008121048807408 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 947490764 1250 947489514 947489527
    0x9060509090a031d030307060b090f0105060f07110a091d0a110618090f010f2c0c19050406030e15190b030118140607050f0a03090f050703030e06 64
    0x80e442c4401a00361500301c0c11041d5584880360f031044803018581d0580000121502805001e400c000220361080d5907843c81a5600414590211820300840b94405410461254501041005040014000c0049006010a11000490cc0c42580c0d01a40d0303100d44540040022483c1208032440081e408400380c1140001c0b0390300d03034a8103020b040c0740510484011428480c0f00082040d1000000405407007614903040000c1003458000c0240b1902c001e288d41c0880224000e400605000d91945407041c45075445001c0a0746084803c00c014510b042000c800d0103540c9a0002c502c1c0f0200c0c480031240c5036681e949040400007070584501d1480101680d202614442800c906003c981d42c0c00300c04a400b0700d03e8020134174035040140c5140114940c0c55802c01514104101190040b00050b6120341038081854201c008240c0d110070046a07000302091041c40700581e449101030040402e80550b00d40080c1d02c00f00e40e503e05284a503900b500756074640c0200303010700406400003690740c541035007116030307604110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 947492014 1250 947490764 947490781
    0x70609080d0e1e1806030c040e151305121903051618090218120c150304050114090619061a0f0f0f180108040b0105221509060509 57
    0x201d02c41142802184190442c400d500e950740300c69450f441000300b0790f076202a040700c02c00040308000e0314418401d00a4000540c070705d144c24452034604452810103080c0a020041c4a1079840000410600d00d00300f1041007540000e40034000c2c51903241347d002590751100c20009402e02c1d41001002c150040c185404140404044c1c1500201141d82c0301e441c040854500c0104200b1483c4903070750200880d1070010508002900744500701720701440c801d0350a00480002940e81d00d9035102c82078030194011514100c81100060004d00a6520034040c000100b20070302c4885004811940885149442d500038006001c030202805101c1586100081d40034440d140c100000c035100118881c03400071b0102000a0b0002c24803103004181c40014000a0304140c8072011040b07145004c0e4484085003603c44010ba40c1080ec41d801901d501c0d0040f0340009070300d0156820681070001001910b0540c1c40030780740d1001d0030511101103010b02110501c6107403c1c00ca19514200c0d0190548819800c05445074401104200c800c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 947493264 1250 947492014 947492027
    0x81b21030a020306010c051911040203100501110705150a18030302030301120c120b04020a09020c06190f0903091701050103020d111203070b040b010902090a0e0603030912070609080d 80
    0x4041010059503a103940d001a03418075590980140340d40101c2801007549988c2c0110080003a0040001c2c0f09007014407801c010880c1300c102c800e0110050104000e202551080d001c400d070600f00d40044820303641d11750740007a000400c80e08103424107080c00030b51085541d80c045030301e00c40c010344511031a01c0c140c19964041d444e4041400b4190707580fa0710b941d511003440101d181042c020400c0c2c1c0c020052618035820892120581110182d010751040900083c802c1150720071900d840e95640c0162035a07407207080c41d140115038000308221005403034010400d50001c284c8649000b0303d2007034036400c020303500d40010b6000c0704100780d0410003540d151100410150720b070700e01c104000307039809240c1d41049045103000641100c42220503a49038800071030114100107004260b50b0149005949007038880c0c1c0d80d0f8200700c090340301d1030341d0458100040f0501001250560741d03c1c1c0c0d410030001015242010320100c0480c851104004055071241d0080e40200085c9402100c04405000000301070607109485810141c4407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 947494514 1250 947493264 947493271
    0xd05160f050703170a0603020909010506011404080a030c06060801020c0a05071a030c0306031203011203020105010905042102011b09231e0105090414090f06070906080c07081b2103 79
    0x2130380140020585100d550066019541c010100310752030a101030882e00910048480e50302258540143c0700d080c41c0b08600307950840703117140000c0840e03d9866030111450035200d00c040341c1a45d19507a0105500100f070014280d842c0415000741500b541c2170a00f9807800c2d030141c1c4502c1410368a500c14000841042c02103035400b025440c036482d502e460346c00200c0d26201002444412030f820100000c50b0580c0051050199030307000f40d009214698a590002003120b109031001881500c0c4640042c1710740020788182c60f00482c1900002900581d20b84404101c0d0a1307404d02d00300004c2c0001c400b80300a00d44004004602a042005005442090307404180c82c40165818803501800740d1114002c140e2261b0102d400c80b41000c2c2050001103802084401054010380d140c2d1a203024441c4075801201000a0182c8600007a940e241c80680c23400070141d0300c0d4003015100c080b004604100d50000302c2d403510010715a840c3c040c0d41100075122078804860811441c1d1404881e00d94404030388001d81881c0710143d0b40c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 947495764 1250 947494514 947494547
    0x10e1005150a03052d180303060a0e0601031d150108030901090b070f050d0c050c010309080d150b04080a0b0703020a0234181a03060a0c02030d05160f050703 69
    0x11a520f8500641c18011611328010300d170f051800204904140e84050094051403003203c0703070800f440d00044115200e0004940d86a00300481c8182041410806141c1a4001c030040c10f0010704912038100122110300450342d40413a41e070001c207546c5040215146460300614404020b5814505440c0000f400f05200c2d2180c4000c03800302080600078020400d0402a40c50340c080120b44216100a0000d80a20f540c50420788082c040c042142c0c1f202e500074040ca4510302d51000c900341c58030308003a4a080041081041c21142c041c050788001ca0745008950080002c3d1044200410311610140f80080c6400401006c0404044c010b2050318210382e00000d40b800d041c6800c045c003458044403480000f0000c00c2e0254805400038014500241d030100d540c6144050b545a218280110b80c80c040c3c0b400b2085900c1c1d4642c5070568011400115407000c90740c4004803600356481030f6031030201480603040030b0380d10941d1810224001c12000b110271503045400c8010150190902c0750900c4480d07180600405400701c030010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 947497014 1250 947495764 947495771
    0x60615031b07150e07092307030f0f0e061008070e040b1504150510052b110d0b0307060903030c0b0c22031505010b1b03090405010e1005150a03 63
    0x2041042d488402c20b204440b84404000034030413a00c2d40e940e5200305100d602c00342da00e004508084510f140305142200306d0340306600c042607120365204034018280740c0b90000d090341da22101c40301408104d0042c1e101014a000c01400107003030070013200e980d00011341d1040720300b0360044504118054030000d80039402074121a00b46421740d41d801c0c52140c0458410ba01e958810b05d03010054907802401da00c4007003904c0301551400a2840300201c1034604d03103d0410580c002807001c6005512003655804000004004108013140b441d000c1d001a400380e80040c07106207602900c1d81c0107082c081c2002c10000c3c0080c1b14034030b0910442851500e01400341030400801900300041180001c621504440441e41e143c900720480700908910b540074040c1c9007802d40000c0354010700041c2c0d408035085140c02481e068624200c442c902d0803002003c0c4034a1800111104031180c04280618425565107100f000e0085c59410811074181c81c28003250002500b580d08018410480304a1040100700e42005071020140c0608000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 947498264 1250 947497014 947497027
    0x6030a1101031401060503090706030606120b0a090524011b0b06041104080f011a030d1101180c080f0a21050f0f04061803020102030d05041e0302060615031b 69
    0x120081d00c0c00258103c50030700701e00300014000390303c50015440b907408502540c00309511014110b00b925010b1260000190345221540c100710b1180d0b105144a22008286442d03860392030041070160f4104076400310310a1000725003102c15400e101c040d0380108909203404e10145030071001d8000e6100e0390200240900d20304500003041d03a2201d61164064212881801d0307140c9903a0004107940e68020702204081d5401c011502d000529291501c101281c2c005000e400009800c40d021035040e0324101e5404265900c0740151607200306024030b400b1142c2d00841c0c0040780242000303201d9160600b55411582141e0056845c1e00100b68201c42852200b80c8080c1d59005500610b001200c5030f000c1c20185240440c400510307210043c180e034005001301c0c0c450b9182c90743c81610380c1003020b14408003071001a0158104000311a05518154001e0750b10130300c030310910380d0908900e2113000200c10308118114050b90049084c03105c40e20303105202a000c03400554843d40743d03282001a0140448260710040c02a45010030704 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 947499514 1250 947498264 947498267
    0x50f03060d061d010b040605030607050f19020309090c0703080103080c01110c010209030c0315191b020705131a0d08090d050d0e09010602192904150506030a1101 71
    0x2001e100e81d008001445508442000d5030703240c4070000c3e100501c642c6040b0260050b0300b031034003416040714070043c09000c0d1540ca50f0030664046c3d01511466a81240402811040d21b00f50003005c0255400359004580301c0107a001881190040a4000c46491000340404000698030070107aa0540781e10081d62074a450040c0e40150140c54514215040d07403402250019640c00158050200c1036021012607402ca0030503010b02d0b45483c1c1035000c0800034000140010350b03641000001500b103c0c4582400501e007500851849100440c070b4032360600580011100b0800b41c580b000011040e880080810840f031804200c00000c1e01c0440460b40c0e028583e50368150f01440040810380e4061200541074544124040c0b80403901c80c20025924408181c14048000c3c00d8102080c2d1035050314000d800421aa00300c8402d80d00755a46c882900300c0c0c201e200f402b441000c0f251032011401039403c010b54040898101407900e02c0966040c3d0705e01d41b0308207140404000d0f446d500000e15200454110201c29411a0007000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 947500764 1250 947499514 947499529
    0x3060c111e120703080f010509010302090a0c140c100e0d0f1b02060f0406120504120e030708070906090b0418081c110307020f1b011202040306050702030307020d0f050f0306 76
    0x50520407004a0703200c06168200780186d200b81d0013a095124141c2c0c0b1f590410000d1002800040d4104140354001a140941f40e440f4800c280198103110a20300b1024101c07209590100300712a80c0b0303802072401c110000e0f030203000c1d4401c03409100024012000500000902000e0300040ca1400c000d0540102403000d0104205425910b4015010a6071200c181c4541c00f80390348544648030014066001014200410307105040c059035100205022000801c8000c9a00d10f801c80416941802001c00c00198000200641001000c50007404100d85180002c41c0044400a112180c0264188820141c400000143c6c1948059010440d01c0c0c4401411703c9070b0403540440c2c1408810145042d07540d0303845258a10207507215003041d0f03003103440c0584044841511f0355612903840c80982c0d034103512090198020401640d1224221900504241e62505c0314001d561382607030074001580002007800120399051205510009a0742442d6501480c0d4041c0141103128034400c82c40ba842d07000c000320f5440d43d503030b03103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 947502014 1250 947500764 947500783
    0x6010f080c071e0602040f1d060f040e0607120605060c07090c1b0b0609150a06030b01141b071e120c0308191e0518030703170403060c111e 61
    0x60f80c03042d400041d8580440203600a0190b201e46062803880010702e44e50f0514401406000901c040c00342d80c4070141484240c05422050552003034441080c1141c0c40301c204009445104241d40d251030000100180b60f08407a9a070300301c3c0740100ea08114110003110002942000c44080846c006040011008122050b640e804960509114100c402e2014400ca8036001d5010322011a250402d80d00c80c80e403042024200110b01540010050a04103d080d000f0381c06044d0110040c14003441000c01200c2d1000c09071301c1030701d010072540c482003213820b00610200011070281880c0100c001845800700060581078100c1e106615881201d84501010000c04150146c01580d10100241e01e4030700340b44203450900c1c0c00a0a0b2000560380300c155000310902d039044ca968880041c1c84452400440c5420b5a540488144020740c041c45000d800000107001901300c11b1080610300005500c4900318545901500d10380e5100b6002c0000049111028040115040c1c19a810b080c0c0c9500008022904046c01c080040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 947503264 1250 947502014 947502053
    0xb040c09030809121501060c200f0d080d090f150207020310051b0301140301150b07030c060e1207060b0102060f012c010b0c12040b03060108130519030806010f080c07 73
    0x5c00000903025042003c40a1540c400c0d07654100e40750f21400c029449030245803000b0340c030005880c6000150b040044444054500981c86c140c640b0002c0d500200039500c000d9012a00d000c1c070900f0010a004d030840c60302100c400908419444d00043c2d0300040d039244e036590b41f1240c003140d840d000f00b241004524403c50000446c10785041d16983d440100a5210000000c00ca000c0c7d400c020f076640e5008102d0400354240c030790050f5070a0400205c0c4e18104c90750301c2c10b03d00859009683d8403d404060f241005440d4006840c0d42105964180910b4003400b602c8003048a030b4150b501401c00d110b03040e8003105061341900c0e20f0400041c280c0c01020803020b400c0c00d0113064281a03864030400403c90100d12030040c40c6211b4181c088544000e01110540c440d8460752058a2a8203402e102144442d841a40380e5030b08200c811880d5042051183c43c1c06007401004801c40342036007c0900c0080c2010741100401307034071140900b407004011550399005801400000c02580e488000000c8035010400300c1d1002e0310b030700082e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 947504514 1250 947503264 947503303
    0x302040c05041d24060c030409150e04150b0d0c060332070c03180b040509060d0f3503060118060c02040b06070f060b040c0903080912 59
    0x500e4001d407240e0720038000c03126154000090545404105030b1140d0145a07107114002c1c3d0006821000c5070070094004005a00c24000c00480300703400c03c00c00251000d0443d115000841905a201ca00c82282d010390003031031180e250204000c081640382e82914094982110040b85021040303000a41142d1108c2c80200450708115002c1074a036031607030010032110071507070342422090041035003000107029154034104650660400925101d224481280d040d510070705066140c0755544807001402003180c0c0100c4502000481c2c200700514280c01140e0b0806c0054640240440454403103004100e81110003401d620420302642444840c15158068410415581c01c10003c004500d1581c6652050700d8030f07070000c1c2074500301040e00c3d5440b2401a080303c2190301d610f0901c1406a09000c003414015404d0b070740c410824030840c4c020491006545c3d8619205240024180c4020f00400c41102d450035a24030402c012031a06100080f5000c0403110480000c668030170b29001c0880d446031a00d101c80c07075000300c00d122 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 947505764 1250 947504514 947504531
    0x71a0a1b0c031e020622180506091b07060c05040503120403060e070e0711010f1109120115050d02040e011b020601090506010c0f1703072003030f0402130204030204 72
    0x401d46240e82501d01c14400115074100b203040240440802d4280607500007400c11498981d58140700c5002100c44440c0b0039803d9603075480300c81c01034050030106c001d03010341c0d107540402c040c628004264a074040340a04640000b5001d15010b101e2501420a00400305076507130031051b8441d4010826140105801011110504241e900f42001a0040c0c070003150054202000c4c6401c824010402c00141c03118429815050b40d10f9180c101c400b042d0b01100701c11595602c040469412209006d015849400140c60554615040050100398a007001428205924211b9040f24180c50701e1240340403114100c648401400281c0002402403c000441d01c0680d0302c4c01c00c400b9251000c0829200c110b00080d000d48080341e07a107110301c6054030011101c150009828510440003d210100c114107840d01078864401002c4100128400c290310540780d44000c40c0344d1035031340c043c101d40821450900303641d980044d50450030249954000a00d000d0f2000303115100c402121079107541194191002141c004005111f9000e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 947507014 1250 947505764 947505773
    0xf39040303180b2d18090702070315200705150a060305100c03020c060405160906050d0221100209040b0f180a0612060617071a0a1b 58
    0x1802844100c1c00305110312016038252500b600703148100d840c00540c141c6042d0440c00c141c900a82d00103400d0041010302040c00221000140141003401180c0c18800b032a41125010009644002051402154881c1c0c00c14000100c8583c80c80c64003440c803850220340d034038030b011280c04000a500c4c1040c21445011904505000b400110349103180c01c41c0180b19000c0e2903e007a40f8081c0d0300540405080e592222111300d03020301fa0f5900c5003648c887d05180043c00c5c4586843e032141002026102070784c4551007601140040881d90386074200510f8109400c00211f443c1070085425084d4903003000e0300c5164002500011110a804104c07107865855007900c112034003017440c00303000707402c41d547c01801645000c4061046040c032402080c54201c0061041c4602c0d8240610740e140c0a10052100d8000c549903036002540b00c03081c40107c146d80c7d100b401d02040b01414100c0c025030040020207e50f040c1d034818001080700098440d00360864184c8042c450350795007550380d416a001022034a0842a000d100d01c804414030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 947508264 1250 947507014 947507017
    0x60a0e0c070506191d07120c03120f0216050a0b071b120c120218061f030b190b120c09150c0d0311040504020c0a02100804050609060f39 60
    0x1d14180780701300b20b45c45142c00760025130800984080a0355000100c107125030400d0300510070710a03200d200400d910f1516903860001030046100300c1c40203e80f00307412601802c2d405120000e0450640c0e025600d203d807030100002d0616030b45220310204408000381d14000c0c4000c1c0410380034090140607103124001d980700b8240700da5450301c03039040c0c0d13041c0603407040032816108d8000010a1650010840c90100701c042f41c14002c8130902a18995201005a0307600402813406c640f544a160425117000031a8003c080601040b6401c4100c4410380c60640c1c24103008840d0714200b51460588400d82c00b00680c0d4603040b90100c3e03845008a41980819070915800c030000c9580010003407407421400741c03910314814400030780944807020100c01c42480140002e20031803d0503409001d103c1101d13000c07211f83c0031081d0049009202d001c07400c01b002604a80400040c851f0802c142d0b41c0040f1104024030540c5482200e822004101600079440000c114021805103a00c46000d4607005203440341d081541e45c10314601801c0c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 947509514 1250 947508264 947508301
    0x60f100506030c0c0f0d0f030606090611010b0405070c0303050907260709090b0a0c1701050609040f0f06081e0c0909012004170303010f03060507140408031c0203060a0e0c070506 78
    0x103807080d0f0f5444287da10a014041c100e030120344400400d141010001d4034040e280f581840b8040d0340e00c0c50410307916a940c0c01880e004051a4544030050035190034010141c9400904070581d03a03010940801403242d518048070681d042a21134110f010010ba441141001d07010b502001015017000c0c2e0a00600144a41a41c002c01d8403107020418181840008e80316862251030600f041c24200e0010805800e0810080014080080c400600e469510f000c2c04110341160440c542e40580da81018000b00f4420440b040d0181008101d61110000700da61a580d24802050554007484500021030242c500c09d40100c60b000d0b100d01002e403c091061550307004c00f03405c1481140390440086038058440d001c044201e80c183c0c0c90042004515904503182c12000d800d014241d00101f003192010746600c070300385102500c05411084091940c444410b40451045238020f204600b019104009203e1a643c40360784440845501070112002651110081200d6010b101800b41481c05031600704200c2d003845d241c03001d52 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 947510764 1250 947509514 947509517
    0x12020709052d1b1c110c030304020415080609280b06040c050f0f13050a050d0f020f0d0b060306010803030f040b0907091d060f100506030c0c0f0d 64
    0x6550b10b075000c403440040000a02081c203504200003400002200c0200d0340075204900c43e90720803408100500c0c6552280c15048004000d504115002040702d0048800411070907000f10300b81994aa001364591002a00c028800d80c1c0c3c0b4420bc12909045e140c00d00028483c0c4015500b103481d0098030243c031803880c101e0a00f84070110004c0e101c28007800c20544c01d036a9030000b5004100c1d680d03101c00e00c801061075564200074400c09029403c04d88078507000a1100303816020b882901c0301e0748150301c0c054030292500101c0c400d404a800501c22500c90403941d940554011000c444100f4083c00444c9581034401c0c03080d9008910368550308140301d641100a40540c000b54116541a82c6e600ba07102d88901080e100c106011103084041008101c20009580e048220305045c1d13202255a03800070343c11211240402c000d04a0310001c40410b034502030048680c021000c0896850314584000b003035880114502610303201c1c40c4084041a85128021b003175540300f28141341121403074030942440e030f56034a0400c00b9590 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 947512014 1250 947510764 947510771
    0xb01091e0e120c1e07030512030730060603141015180f230109050a0512030d050405031b01110d05040f02150c07080a080906090a0312020709 62
    0xc00c10510340c40340c03803008400000602004044405402043e921645168699105101c0c0d90249101100001800b003101d540044c9480780c03071454224140340105d1000305166106004000025070804603284901030103e01014401c600648404400018002507181c05803170120041a000d4041d8403041d074a8014000c0e0310760325900c0c24040d2a80300c6007409241d400e101c00d1030003200b081d802810040d901c0e40140030015a1141c0394140c1030502150b982c00203410110318024681e003d80c01c5000341b8881c000a280ca104aa81040003080c140d020307a01c641401002c88560011181c5002d00603100101d10307028040c40242043c2c20181c0e982e0b0000e120300e8921403080751b60321080701014030905011490028000382003809144045009081c000c205031401c01c000a001c50050791100ca114aa0f81c8200c400280c85802401072645480166041a50030391301c90543c180200d6002020307510f00b00d008644460756050000c2c0070640c65000c0d50b0006101c171140200b0400040d80109611055a281e62000c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 947513264 1250 947512014 947512061
    0x10602060717041a060a0b0a020303150f0a050919110918040f020d1401052a1e0a0306080d08091207020904030804111e091e15030a0b0109 61
    0x810050400d940042606a00b0100d00000c0449201c4c803542c41340c4018000d811103a5a40207441035544000c034450300603003000041200d00001441451030180003a5508403c684440020a0302e0124a000303881c840c094440021b00815142c1280c00301488036030742c0500280003000e0800c1c1c0560050000584501c81030752411617082d40d00070340c442c4500c0d003110002d01d001c40550240300003200b1602c0155a50200746134040c049003024011203010740c0311307042c1d000084000e5007a21030b80000f2801031403082100401202d01c071b6982d112450304c1984061070355160b850300134500590040580d0b6100680e18014907144158458001c814507105081000030703241000e2540b40040040d1144c0c010003540b02e1a40800724010911030580e15030f0043c40758404046e600400400a0081e60800c490081038000d8032407111840d04000f510706801408803007803440c2c408101c100200020300010051200303084c20000c010703030a43e010090400800c0e0461041103680d610740000c60068805c03011b2000401400f0041c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 947514514 1250 947513264 947513297
    0x4061d072402030d111218010c0503010b070201270b03010305010501050a031227080f07050301090b0106081509070509030d0e150d0e0607020607020f070303090308030406140106020607 81
    0x11902201c90036805545041043c1c0740102c000d004003a90f2101550003070001c0610040e1003c50700d8000c0e410f9100000d03003100c2152010342035544044811081100034401002180d845000380c814441e82401d1400781c81c0c66011b9260307402044800400b144058007040051461503440c025410f880c00740c00207004503070300e90b0f09200d102c12a6100052844103e01102e031900e900c5940ca41c0d0440019091420700503110761009400800c07680c000559a4100610004000e00100300140040c00f0a8000780891051a15000c01540d0140309140522214074006000101d00801541c0300700402081d00325103007000b800050184e00305851a5009200e030442801e00e89000f4104070690b0702d0001c20903861088130b500250056003100d800c2541e815291040106a442d0900bc003500c02da101c1c0d40201618546482c00a140081202d010740c3e0640103404240080f952004516041d6500310b0380e4190781c1d07100c1d8a4081e00070600741d240103251000c50030020442d1680072a1083c019012551361241c01841501c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 947515764 1250 947514514 947514569
    0x6030607170601050315191d06060f092701090515030601060513080a0b040b13320607030b01140a0905040f0b0303030a091506060509040504061d07 65
    0x289458540140c0c00010b01c603600c104c00444d4450140104c2404100710580418600d52245980c245090400344060003500c2d403404440500c2c61440702c210009050180202d04684142c110858541900040200d055111085000e91411040e5042140410b105414044030302003800380c003059a05203c08201e0303030910b44c2084540040c00a014045503440e0150544255000142000183d800003900081e050000d101030400203024442c1e000c105d2510707103852810418010114080346e40b02c4000b1034003160301005241015030391001e0380b40c420030400300107171841600800d200419108030400c0000c5198590040c0d5440c0c402a22a03400da141e5280d8050101e004496002d0700003007d41c8002c00041c81c094100801c200180c0400103803140848001c00e0842d4011103403007981944a400400c200800e00180c08501080540204006820300030000c005202e115240352190303449402141c1403214983c01420f00620051901d0740600206010a859001520488842e0400800380010340300c0d0008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 947517014 1250 947515764 947515787
    0xc03070c030830270a05030d06050603010f0e0402060f0f0901230d090813170c1c02210106120b0901020a020a12020a0c180f09020604181b0806030607 66
    0x41c20081a5030707003020113041c0340f003c4443c4ca07003150002c24040c80340d44c2c3c0c02c0c402030314424040c03000b0b95074540020b6160b805580950b40101e0045d80200b004210601003a5102d07000c0d1040700300301e11995265400010458000c50b40c82e480304000c0000c9418600a10000510240c0400e1701c421601c518951800040400c00503a01428441c1c10480d11480c80004d50001c40780c2e0344205441d86c20036081d2900c40701a505141c004c588040e400414601c403004080103a05540c0300111a01c6c070303068894206195040390744950003400b41c0c0c081e94421240081095020b544044504000c006040d07480034241180104c444c0d0546166601c40c0109004003010b000b1550817806540043c4001d1581d5503c6006150101c0b04035803c40c007614252100050100f0502e20051100c4500000100c034000700c0c400464104650003543c20380307040c08010058450101341c42c1200d410b03595682c240010444c209020f0180e040c3d08140000c40c11100e02082500b19914900a80007078003140d00c1036465850940e510029032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 947518264 1250 947517014 947517097
    0x101d040524040204080d03020714120a1407120e0420070201050f070609030315080d1202160506400f020a080a05060a230a020c03070c0308 61
    0xc5500c0c04060349041c0340d41c05121010380018505542c8102d003904000b40c440700080065000100c6006011541c0d140b00d801c050704c2405000d02a00164485040b8811030030703010f080c0b080d0a15081d0034900b951007503d54150b0071000386408100250b200510700109e80c403001b845580f070031000c80b415045680c80640f0b049190343c403c0780b0740507541e001075446420420b0420700c107034402c100c1c541c00200345005d48440248a510041400e0700d03035100c0c150700c1c404241c0044c5420360008480e1042550302616030410083c40540069440f42d100703034814200a142c0c04040c00070711601c41408800f903512064540d07003581d0207402050027403403401d80782c0307400129419900c10b44100031080008514a244030418841c4000d24901c00a561040414101441001c06485d00e81004c0c00b00002c400c21030048109800482a01a650854110f2480c02d00e038009003c003c44190b02165083c4241c0d010007c03180d42c1e0360400c81c41c0f41101d6491034038541660000c9981a02072480300c040da040c907011303400b003200c50340b006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 947519514 1250 947518264 947518291
    0x3021b0307030215071a040507061106060f0109091a13150608070c0b04030201050f2203050304050111160c1a09040e0c09090c0405180712050309101d0405 68
    0x85808002495040c0d04126500100c100300c8140080c6c0c40c0d00c140301d90311001c08080209491702d030a01d5410f002255000509124030039608881c543c4c404100540d02003021220781d00000095401251064940e030080c00300d581c50000e800555105c1c00280c01460030044811640c01182001c0e03034820303035a00740703000a820440c1010070301409000e080c0c0c2a42c0500540b818812440f030985511883d00003d50703050700980d65600034041200d18100c4c442d039218000150302c520a842d080c20784c508908060b8006010030401102140c00c00800b9000702c105d94104001007a21100d0121081a804050010407207a03003c0c2130300b001404c41c448020468010010400d0903080030710400c00d00014050500fa0307000c0c18050043d184540795a0101224000c4425800401c1041000001d10046500190110201e0000b800e0318103500440041e0100540c0c1e11500345170000516494842d00c0d501480b404150700c1740301820039041039544201c0d021034401d102041c02c900d0760000f01c14032044403426200f00920510 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 947520764 1250 947519514 947519519
    0x1060b0f0f0a0c0c0605090102010c0908030316031d0c090108151902190f030f050906012105070b030406050a0c0c1b0503060c0405041112060d0201270303021b0307 72
    0x11401c001d86203052036802c1031410041156103103010742899821043c080394002c1400310700b550b03091041004d040c0490030008000d0303080c03203115a601d020043c071101403807032a4102214042d2094100c281d0303148102d105a24001c031110182c031340300e01c803030180700d409001c3d184000030f00d0100000d4040f107007180c122102d481c10b81300c0c0242c02141e0882c0200c441d40040d000c01020040c03075403180000c1c552a6080c0e680155009850100034140d901252203020360f075081c44248a01000701060850450b407042140b10701072100d0703804c08203a02c840580c0141260144010008030040018001e61055214410401213981c4418400d411070358541000000120a094004001400c400c4038000305000039160f000c0c55030f0399000003131901070704480608060078041400c0040d410b10f40a030014806200601600f02030805001900030741c1c1c0285490300c1051550340080559000700e141c044618000d104c3c1031070200807000030b0b44009a4900c0304030014496181e20005040310480d04000085000b00038002161 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 947522014 1250 947520764 947520787
    0x423041217090708060105030a0b0c031302060d0605130204080a1101110d02101a13020706060b1204110a0605121b0721020c012f010c1101060b0f 64
    0x15404024000d0008622a8140501190416910801c0c0b14002086994248000c117170400c80180c6c40140070358030060079500040c480401a40d0300c205c803c00c01070303101d94840980d012215155400a0742005d0002018503060243d80c00460a0303030320903200020241902540d98003207118a209e20074080c1c03c06016a400100311620b44486644140350a000e0440c41c1600300d802c1420480c038110150340404d00541d03500240c0d0154800700203000c1401d0800c0001c180c0070481d400e0032030030322500c03655000590208110b21603020201401660303c031561201c1c0c928840c4020300b14161001e42c3c60600580140036180303058890041941c2055450604210003030113103105e0484080e0609480c8a0042410514403119001278007c2c07600800101401a0318400048240c40000c4204000c54124444c03102c0c4c5a6044040060800d401100c0101450800c220503400342c90003215000b140d5080a8041051a5000f110518440c1c0a8002000700701d5032094640124460305554901110051001d440c020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 947523264 1250 947522014 947522033
    0x70212060a24060c02030f010f0c0206092d01180b01032a090b0d0501090f1709010c0f020102010b0310061a0702030c01050a090b0304060c0e1210050c04170c042304 72
    0x1d201400310b070f04a0812103030707c6080d1000c86801e040002d56680d08031240b6a410803402d508541c0100150842c092402c0f0907034014208540c00c00c0c0201f940d131140010460003503000c1409651001d030340d03007102d0700645492084004284410307518920808040c092044240710180a994010001c508000b450302c013025014142003403190f64480c06030001d000c0810420302a8240c030602c0307904c0c0d14411022918024400e0b0001c14900403509070144030307100e0543d8014000b810180d4000c034042e4070583c59440100e000d0800c028203150140210001a84610380c5504518166000102c41c00e14040008800401a02414402075855400581d54544d9035000c1c800929580b40340e440c04105e40740d11103c0e4031070b2075070050f2003c848030b40e03076003c8440000f80d201c10aa2001101110040c1c1030031030b002035a43d5680007c0522103a0356955034003148010b00b81c002202c00400340049040c40e0101d54080194075200c40c0c242450080d81840071200b005d0b04e2810009008a4029161801e191266252038040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 947524514 1250 947523264 947523287
    0x91516020604061a04090c08120a0206060607080c1c091706010e09070b19021b22061203020106030c0e040312020d180809150a02030a050906070212060a2406 69
    0x906541c5a80e00107813a81d024000e103480c09450b41e151f1051909550526041c44808048140e071414040240800c0d070201c8c80e00c3d04450b04030383c0240c58512900b0f2040b228840c043c00d0281e14403e0f0610040141c1c100c00e5248020030041e1030b0446543d9a400c01203000842020101c1c04075045000140f19228680140580110414088500581d242c8060405a5200307108601921107409501803125504025140203004081c004100c40891480401d028200340c8001c00803010200781000e00c0c4020316400200103003581b4480b4500c106e01c508002e4000c00142c081600c98200801c0c011605500c035104981c00399a245c0e40f0f00040c0c2e00003105c603030300a4026400d00b42e1125160041004040444590600305074000d204680d07540c17035048100705818030b142490b03c04a40092162082e0541c02001750f9600c454181427245d0768204c400c0020303625101c4c000000f913000c400d6094108142c003000603114821440e050080120300c250344a031404030042180c1d80758046c55656070030701100c4c0c4141c0d083c045 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 947525764 1250 947524514 947524541
    0x3150d060f090c0306111602130e07120204050a0527010b0d030504081e100903020f0d02030a0f0305150103020702031e06072616050d0509151602060406 67
    0xc1c1c00800300030110540300601c0c001d40340419190018018840390b07100300640c001e01c0c100807916181c0040c4540c245620414806032140c00d01140441c0c0100c0103401c041c81100c40d40e001c0e5846aa10350005500540e13801c0303c16401039141000040108410380b0842e40906030003640308803400710b40500b0448001b8840320342542552208400640740c0c41d200c0c3c040c0d10080c40780e03d070543c640e07041c003c6591415082c11a02c60780c000e034088200762810000b2171a42d2000038510b0300071620320f08504080c1d2800c2c810038014285031040c192f0441c1060b030b011024082c04082a0780c1e90b4444400c034135046068034001d40302c0341d0500f84042d60f0040158000e80c000d0042d144098203851040b41406440c2515684103494510950000400c10115542c000d02810002c91500040c64003000c100d0302800c40e50900034401081580b1084903895280d018405850741c40034040000d00c59490901712081c1c851103040100d024402070702c40826900743c00d0f01665030320041c2d40d40c010940d5a886461f20800780c1122062040e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 947527014 1250 947525764 947525771
    0xb03071211190f14012f0a2a0e07050a0f141c050703021309090501021e0a0f080c07060507091706010f0e060607110f060a11100203150d06 61
    0x102c51620b814101c02494001d4100d201203107490032000300410404250341c100030300703802c01501a039440031450543c0d0003100803600310115050441072030442030840182c41c0c1149a15819100e02d079070400380c800388240071010700300f240d981c0c414000402c00a4450340e02240042c0038602c3c0c1d0500ca4682104a442c00d0f1506410495200340304850960243c441149201c40c04102035002c03504c603024036a001043c9203000c510300002c8215001c2103413118090209401e071034022070030a00c002501500c0c0d041050880a11030b144485250b4202940110b461101103010071030001411784c002d000d024402d60510407003e25120640d80d440000304030084c445030a0080100c00071620300700b88808a010103903800000d000c15414500c101c0b8040419078486051051010100001d50700c900080d10301b01640300c0146a901c145940000781c0c001080c00e403031a001140414000040307036100a24041d40c0c140001642d0001641e40113007000d80c8822039081c4c21010721410f280c4440c1c00c00d6840800b08a02404000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 947528264 1250 947527014 947527039
    0x304030b040b090f0c01021b0d050303100f05090f0a02070204111c0513050a0201051c090807060e0f1b0f040f020c07060509030606040c0e1809010b03071211 69
    0x108000d80d819035054072010000001c0006202c802c0040c0c0c0800341d03811000341024042900004c1d580e10380d089000c1c208109038250304046444070b05420b90040d81c4102134a4803407510b40b20100f4244114030903201898407103100000c86007401c51100d03000d0742c80f01c0150840350f80c1e00d0301c045001c3c0d0b200d040c04980250792078a58503200840c24019020389a80e05204000c0140200c6501c0b054480150825047e00b0030001c186000900004074004800e41c207081490315200f580100c54080c000d00d910604d40b06081c075111904000485004141141c422401048a02e0800f0a415a6914074500c1070f40309500c0040440340c03044200300c00d0165580020104098886420041400e503080048050070064000c41d4018081038144101400340c03d1900e043d03400c0c0245240001e03582c0c14041c04a601440d501d5102d0098144100611a03502e50081c1410121085440c01d05034038103000c4440003215407070000413204a20b0b0101e0240201d0361802c0307003420150001e8491809420400401a1784030800715201d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 947529514 1250 947528264 947528273
    0x4080a08220308090d02011e150810020d05070e0a050f030a1b031a1b0a0e06070506090c0414011a13030c080c040c0203030a0b0402090d0c05040e1504080c030403 71
    0x302441c6031082c0e58a0b003140c1401019107140000c4d044840c000d59041c641c02c59000c452502c9160321106102d9400320345d81810151515401e0065001000d0b0381c01079220030300c030194443d002000c803008400810400c6540e1400304481d4640d41d140510761103002d40d4010005482d06000d0410101d5009040e00c441608aa40c2c1c5840504010040650050115420030034400c922443c0c5050384003510480c0003a140010504005c0d503000560100d06980110301922a13512400e00500d680d80084c000701c3e5900d080f0f00b030495550804491441c480d1040e001032080606250290001714846122009030340e9080803031041080c81292207490f0f100300c05104d1680d00e1b25043c00c800c40118001e440303054206041403000d40c14540844001030186061403140310445900008999104200c1000040c10504a43c0045d0180c864800000d50140e2a41111401c1c030151042e040119002210100099402590201c0c8c88181a40c040c140b4a6a90000039000c1756040780141244420001039a00e0140c89036074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 947530764 1250 947529514 947529571
    0x7090b0f1216180c02010603120807021501180b0102160b0c160e070207050303090a0603050414100e061308121308030c0c0c0910180608032803020304080a08 69
    0x11440343e4440030f0075481d11a08092244191920306880203121365070440d11101c43e03035400e503020881040f00013000107000314801c2c89034010b8a030300c0c0c1c0404050ba50703456864051032001c1081d0504500e00e0080e46211a6000058103041c42102122001005240c4882c6004580001d03400b0b110502582c02c42c43d2006248040301c1001d005010303a00c1c200e60402e40002443c0054030f4210f98025401002140720301d66070420400c04480d001e10380803d041d512468507414441089070003030b01c80e209594190700c80800a8001d00c1c040105142128116690304880c5903141c600c080e800341060304104903c07041d1031036441529a0004070490700c82230008903540c8a900e5580304980162000c100821056100d40003800700d04000001143c4a50841c10b295820780481c03642d034030850f458003003101c1c901c9030515803680202c0f004040035416640c40e0a50301c0010140000c0445400008016a050000350030b40281b0940f40265041000e0398141400700b00140c48501c4041c01780d41c0c99800e41082c100504c8070080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 947532014 1250 947530764 947530769
    0x801090e0c04060f080f01060f17030d0c0305090c0306040f0b220303060f0e090601140f0909010c0801080a08092101090501090201080606040b12060d120e010207090b0f1216 76
    0x42d00e00c8040351070084d05034101a006c03ca5403560b039050000402c00c18199154034000c1e25542c3d2108110007025194441ca10710074172003d11034580c02c2c1800140402c1c0c050380080d00c2454000242c690442001c002c05440b4901200d000b0000f40280d80c2c894049400008000d5006a51107002c00b641c0c12070b5650302080050012040300025116082401800e540280c031000030002142c0a92060030101c001070f0700c551050080d0103071204c14074030306889590384202c08904800080c00c0c45085042070704003a8040d280c0c90503081c01050100000040d404400500c05094035040f500441c02d081c0302808001b400e400200f4103414400200749051031403c0c00703214030111584200000503412840380300150014a00800d524461035080c0020172041140c81d0844403c00b45811511886641e6040025201c190840e4040d00180414280310ba05641003450061032110036021109110b03a224404400d403030003180c03221f8000d507a004404485050212000412188280030b03640b1514025042e0b000800d184d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 947533264 1250 947532014 947532029
    0x2303030a050a0b090919020a180501080d08070c0b07020709020307020105150105041d040206071b141c08030403120c02010632010507140d05030a0b03010c0801090e0c0406 75
    0x8a091101c07040d42c501c40c008083d001a200391529103803a0010548a032141070307100d6030460050f46107804640c0c440d0207000c0946844281500f0030300c001c8008400400e004d000380300c158800e00034242111400303000c2b454800c079400d0f540d21665010a6032070030700002c0701500e80800e602c0b6440000c01c0310002070002c0c4d40300d820168000a501d141603400122008981544181482000c01c814885004e0741e2801461044485640c1132050300d0b85d1000c10414451090060040c0d451198440d1180710503000d0304048030b05540c0c0699410007840c08200390a40c0c416800000b40202001d044001803e90010707550190007810141c60906038180c2407015a0017035105480141d6583c0801d01c0000c4c640b41c5070041e1034081c0300003031100d81c0c050780303032442d01c5d42000d25141d050200c007081100c00c014030520b200c90841040826100c42802003040645140c0017030380c0002c89282855041c080c241014440c86210344c01564803107103680d20700441c8000a001c44009001203008219202c1581d403950b0250781e0050654 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 947534514 1250 947533264 947533271
    0x501090c140726120403260609070f050708040f0503060109021603031806050f010f0f0b0d09150f020403060501170703020f03031215040e030c032a0d0903020310060e042303030a 78
    0x8000710340e03001e00303401f2004009070220282445100e8803005d0149901002500f0b1034502c0300399000082d1032500603040e0080499a00060105050b120545200111074040e0200e0340940d803600715250a078005e100246001030405601400801d100390082490b4101249424070060354588648080d16070444200b01c07900070b00001001001c0c1b42d00c1ea02801003030144020b0070010b0504c05003c5440c4245501b034540c1c00e031180c4007a401c1c130030642d0740355601a00d2034404015000c403404200010f5045440107a85141c0340c540001020300c6050b2101c2e51a010300f0b00a041e04906617070800035000e00901d0300a401d84801e01890b071501a4100c5d80a00941642e503800d0001c0814034200015101c40c400d090800e904184101000c1d66000002d0303d404036000300d402c6680000109030281143c45050150049119641e181024960072148500a40703000750180e0781303051a01d12b400300c281c804a203c1c254041c00e0101c001000703c1e5180e03288990420b448031040907045070180000d0314540003903408064642e035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 947535764 1250 947534514 947534537
    0x2a0b04020907020c0f1504120605010f0902071101141c09050c01030b03061303051306030203061005090a0302010305060a0504020c30040302120f010501090c140726120403 75
    0x910341075080e4000e1092004018101c0040c011502ea10301c0607540a0081000b128031504030141c00b0103840103040e1607101c18034461f00c00e0800c800071302028407031010920f00126022421001d1402200c4882c1d030420003c0c2d580c03021030b80044480748200403690030401030a11600c5200040400020401003032440301186416890811a0030103000210f0705050525201041d403941e140800c400740e1009020b0a4400800701d2801c0640b441e10402c0c01441c44180500804105075403d940614050641602c90f180690b818142c240ca1912440c590a030b802009a101040103601c00e0300003031360182000d06450b4045540300d001c902680c004901c2040e8a40000b102d84c1454107501c2c54000084d04001624a42c4549134250b010161241d400080d0140603008043d62032100d0421024010f81041c0000308581d694030540308004107054002d1b040000c040d80b4003595600008010b039100796801100b0311000315400c844e00810400f000200d0803a011080c400e450601d450039030490301c142e0003a2a400701802 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 947537014 1250 947535764 947535769
    0x102070f1403070512120c0a02131406010f080a0e10060e0415050c0414061905030123212a09220803060325030c08061302012a0b0402 59
    0x80710303400c510701828403811710a004040005040d814018206030742c0d555040c1140c2950305186108202a400c541980e14504000321103a020340015200c026815642e92110401141c100d9004207068000070031080220f040c01d50700e03602200580b0411000c9074440c0f0030750384284c0c00390f0b8825401441400ca0450401080c8031502254148844080c0005c20451410030314081aa002d00e001d1943d07500c10358512400d090b00e40d0070494507040c4000040c40011200c40e040240300e41e1007402240c10722345024120641201c0700025584100000420740020501d04500c40c0c410340f10384016108292003604910609240343e103900301d01d030804104102403650042c9050003940c0c80090030b8001802a00300015810b488522640002d031a440000103030786e43c8803d030000e807401050020049507440d0041443d491b0035050084001141d20a003010304440e40ea610119440703443c101c8800c0d102ca41d854441900540c42003036003220521a0315503603c540c0c18621a00c0c50b48004c5400204c910a18800c180004d51 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 947538264 1250 947537014 947537023
    0x501020a080108030c061f05040e07080c012d030207080f0403030f170403080603011d0a02090603060714130b0309010c12020301140d06020d18030e0609100e0102070f1403 75
    0x422440000790302c0c0205c10074101ea502d0b00000e052102400046000140910040105200400f002803040c805001e03a682260f40304c2c110b071b20444080740f1500e80c0e0003990b075010303440e00030000c071520b084002002c41c00700c0c05120000124000c20109a800c0080c1400503442c40e01030f003141c2c0460f1341c4403500c86055280103032048541a030704000303201223900803130201d080120145602c80c9d410f01e00020640c030360344086030141981003820304070900101044000b00c000001c0d1440f403d802200d03104041c2e11114181a102c0b40281c81410000d008a40f11440d80c42038900100390802c0c01c00e01004d1141c2d03070340104410942003034994181c2a51991300d00c082c4254080d000d8040c1e0108428210310319490500c010307040c42500303008c9a004145040411041c480c107981590f4019520840c03d103c05e80300c5003098030803c0c9905004170b010442110440400b0f00345041503401d03940020340035101134900000259403441c0d000b290241144103801e0003140e1072406404810081211300d0a541a038050003003050f040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 947539514 1250 947538264 947538269
    0xa0912020d110a080307030207020102070504050108010c0e0d02060f0c030d0c0c061b1e03060305070605070c0f031a06190602030d0b271317030f010b0c06060910050a030501020a0801 80
    0x943c0b164242c100400d0300301003100d8003c40c803401c0040e0744003002d10050382808001d40c802a13020385000d000051006064000c0700e07580303030b4a03691b104880d0a03140410032219801000030390007100c00c1c461450810403000041944151000403207050072822000e582c213880c400d180100001d66140011000c2000070700901c0070100610380d1401d038403001c80c0d100400b960f0000a0b1010f01a1400c3d410140b03041c0030383d001001954021042d80c1c1c4068664201400c164041401100c1c2e540c0d19500004521304c040c811001580d03808000360070442e0209240f02c0b0f1402000d403015501c180c1c110000d00042c1034401a000c020900c94019545a000001840048440700d10040c1d015198400c8100301c89801d1030005107480101040225054903141c5071844a01002c54000300b001d0300400e0400545441c1d0805580300c3c1700b0b80e1030110416030f00c40c50701401d00e01170401d50015a0340300c2c1c40492210b103460282c10b54000c00c4038524034600c0d41d9660016278094010381c021346c0e40b03942c000745201c0b0803540940150301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 947540764 1250 947539514 947539547
    0x18010f09080f2d0c06030a090c0f15080c030c030406022a06060d0519140a0311070b0906072d060501030519031d040216050d020c040b0a0e0a0912020d 66
    0xa00c4603580c40d1184d164807080011a01c180c1c0300000141480700141c7c4283c0245d504806514600c3ea2107102441e40b00245d070054041d241c10100304040b1652055030001c0c403a2800040d81815612049401d02c0c1039040a442180c1c695000d00c0700360032624001e1002000c00c40c1d80b00c080c141c03030000110640d040c004040d04080c01400d8400e40e1348007140300016244441c60070344404084081e03150034910620071049003440c1207801400201c40505500c036000302039003641042640c1c8030700c1e03491b11081c04502c50398003400d800190a01168002c116140550100182070310404d402c0000307050b002c182c030540c602c030044403180d5580005205210042200c140c249030203c600120f83d100c182c0340580a21052501300c42481d003801e00c40ca4154595405994841801618849004c1d80c2c0d4500147c54034030362602c680040c80b8421001000345810b00484018201c090b001820460400c185008040c0c801007050507010703103d848030f4001071544151600f04259580c06028250fa2488001b42420103100507840e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 947542014 1250 947540764 947540833
    0x18050403031d0105250f050310050d0b0f161407020a0305070f03170f090909012c010b01030519020a05070803040f03080f06010801090b210f010c0518010f09080f 71
    0x798800e801206c01203401c0650304015880c1d54444840992005090700190341001054001108202403140d405008840c001811401c540c0d8903401c5a020610b1118050002003860000c2c0851103d490000c5c801c09001500480d11640c1700d403121454000c2c0307680103c070740c0148000108148980440d4008014007003485491808049002ca00f0032400361071b0251344608070311000b06520002c00d40c40b0303030114a20440c1c9442849008182d9081e0b064a104013200c0d6542007030030003000c46d03100384030350751186e240c44580f4105509140d0390440203410015008080c004104008000300300c5043c040e41c030641c855601c807200445145401040e24601811890244800d0400c1c4091aa00700710382c0e81c19104508c0001802d0b9680800280300d120300e80c0c00040c2816200d6901c550440c1011400b10321202c5020024044041d24031002c07076044c4600540360003e15845034210210758400e90000c40d0102443c940444841d803600348560510100c2510000703d0351280d4164160b0014001601c04c04895920148 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 947543264 1250 947542014 947542081
    0x40609091524030b060f100c060c110f07170304030f0b04020a030803161803051507020f1504021008010e0f220f05060a020418050403031d0105 63
    0x400a440c0d148003241c1d5041e03101c400b501c07031400102c081031a0800b10041d0340e5816582d03074200345080183c10b903402c901030204001c2c201818107054100c10542c94070743d601c5e50f451003036a4079058014900c028a480822102c004000441c9200300701115100300c00001420030540b90110241a0131928210810540c1080c0000c002042e41e00241070b60f250317041140e0401ca95224400144220f0403a0002002c9900c0401404802026103000c00d42d04030b050303180c00c2050b028082c481d11003035000c0d00c8010441c1c3d100030402c00048001038420b58101090b4011103122030034881d07849040c011424140002e9246040c20041546000c440c0020b1400740c87c14444119410310b02080d130403000c010714820004c400e01000c180c0813440203800c0f00c3c6c4c151680204080302805403608510385c840041c001c0e0b403240309100105060034094421a003c0f20130160711812004400d0368808042e1200820960030b05513560440c1d10714040640a99862211500000a0384e10701810182c4034a1955880c40c2c002a29200c00c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 947544514 1250 947543264 947543273
    0x1060305070903120302072312040503100e210c060a110406050c0717010906110a05030112051006150336020a091109011704020306061302070c0b03010504060909 71
    0x2054143e030340000403410255190581170300607200b281c6005120580c2001c10f140d8134600f1041d081600c85021050780c80d585049040c8000d28020b40c080e1941c10341080100c42a00c0c0b030030790721240e91880c00c0410345400c01020fa4202d805c403260795805241605000072405440d00c0107210040d8809200801005110072900c2e07004403d0056000c1c1405005d130004441900702810401c0c40010103248034000001410601e045020f88410b01d001c40b000d070b040819003140440f0b481d042e102c139900e26988183c150303032070240c526244003803440007910f45000320800000e07800940d00400303001e000400904011814072100090482d160400b18404102c0200c0050101000004800740c0890300110f07403010441540c00000c410f0350443d44001e1484c3c0c80d191207200f030880200050000000c0136201c0d0507182c2041000b0ba407400ea8222340003585030b044840002c205103010350000f020682c260100504000103596140f41400c910303008000350000100040240e403420f0701800002c3c2c13403000801e00c8040c119566 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 947545764 1250 947544514 947544527
    0x2150f0f06100509152203020d1101140307030b18071d06090d0b040c06110c1327022103030c0c0c060706022107081501020f240106030507 61
    0x19591056200d44400c2d02801e204100391100400c0c002c00581c45010015607080055004030b18400c4981840c140c00c4003555100341c040c0c1d044076000fa00241da040446d13510355580300310100005041c80141c00e5809920f0380050b015522540c4030f92000550030350034004010a240150316207803042d000c2c05040003602c81e40b081e9921001e075503003505800b00d05221070028516000303401c079203a04581003201c9841071040c48880d0a00403405050300865445c3c5070001254011030400c0b07480f0290303109030304080c200e080824003140150b00c103031400210100c0d01e0148036089192144040c0d02e91107207071419019450301d4210860301504003205c076000342c640a02200d4603400000e0030440b80c868041034030001e4040500a00c0300381580102401d6a80c0306614040000b134114940314503111291041a504102107481124024140b548402c00070340e4910b9003c0400050040e4200d0450040d07840c8500d0700d4030100324102e040390403000030b061031003403444664207800c030141e01403400c250500085c0700c01140c100c803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 947547014 1250 947545764 947545771
    0x9010614100c0302010b0d03090e060607080a05030619031202070e070c0609051603240204030c030b0411060f0c0c0a0f03080307030e0601090903020f01090210030f060504060602150f0f 81
    0x3840d0001a000f410240d004258480d0401d03005180081200c04056100c8055029200c11a40c0100c164482005110f40c900941c44000c0808a00308540b21285001d5000340d07901010003080c038103810800400902d1241c1d0164012035480c4a00075020449507014460240a402040381500292400700002004441091409081c3c5075a903415a01406814000030103075803103103542c2c0c3c2e00459592030420f1030000500101d005269080051b08000d050074000c4808694104d10883c05844c21030b11081417005000d4400c84400a081900d0700c0079031507600c040d140420810300000e4a400c3c1c0e050460303003030041c4454417038401c4540300e105001101c12103031031005580d08034113940e8480c0e5038110103400406011501b0507280c80b81c40f000283c1880d40d6088030218034030235429603082240c41480c0509903460480d000354428203000320000740038400d40c011103074002d10003000304980350303998041011150680c000c00c0c01031304031403190039495810f1040d4076005104140072803414680034080445043d0b018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 947548264 1250 947547014 947547017
    0x123070e0a09021827090c0310052a04060e0603010308042606040f03090e100b030619090605090f10051005071a01060809031305130e06040b0901061410 67
    0x200711000c2003014404401c000030005440c6001610740c1c4200013403101518181040740340d01301030005080100107e03003c2441c0300d002d0002e01400e54060018405408000c15402c0710402c0ca00042c091245140e0001c116140c05010b8070f44e07500c4c2020401000300d00e1040c00c00d401202d04100410014100c9000c55086800d01c0c0742540d9072100d4030040781005148200848010300c46c0c5400d01083c0440f21a003000c070148a62580c074030031540c07585160340d20780c0100e40007003c03490001d008001c5403501a0080d075100c41c009014030201d8650030042200d1080d030b80c0040079142c0d5541030034011f5041ca8803c81d40c104102501390b034024507024408505500e218012603002d07429004814842d540614280c0700c5550307004d2540d000007000c5844030701c0394240901c04c2000040303800e004540e4000b80807044a081c890b00c0c15041e010f00c0d08102c02d1002c4050303182e540818032603030382d100000c00403000d000c1c25000320300c110341c0400ba60501c0007107982556519006a02801c015054010040d41d0341104108808041d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 947549514 1250 947548264 947548267
    0x717310f060c03142508060906040e100e010e060106050705030703270806070f08010503070b1b011d010606030506090a0f110a0c0b09240c0c0123070e0a0902 69
    0x1504200c02500c0d0316040b13441d0351443c81c070038040d95202d2030603d4200c00724000005103002d40c04502c21209004142ca180d504a03071002e000c11802d080ca504407030803601d038100850b0b981d8504840235904607402c09024594a03596800422108102071040600404851500e5030030b02c00182c9405481e071268440040502810002182c03464030821001003101c01c0741c0c1100344092355551a160344809048070003d0028114101134001e15001d01a5203040c0c0f0806401000700d5070410b00494881c0d401542e03c0b49001411114001018209001e4940841c0c030f4440002003055840c1201401c0d11842e400090505080c24104282500c444d07405a40c0080c0d030301c00102e281c0d9845855680200341c280007100c08030000003442034005070041065003180e44150b0302c5d442c07207941d0790088985030400303000b46030269101101c2410030381d01d00c0d405c02a0440c1d2200e400c240b4102c00c0e8003ca80c01c5840614601641845511884001e20032504038940d000c0d0086c00c100311444030b51000500c0243d60b900802550036030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 947550764 1250 947549514 947549531
    0x1050315090f160e071107090f0207020303160c0f03170a0c0c060f0e0a030b01120309150c060e010b0d20090f150a1a030717310f06 58
    0x241000302040224940703050760160740f00700243c442001a03601814180c8030640e004140f18501c11304003250b80e00d5030000917054050070408070300f02a0003400c240c1d40303410382c0900203e80965070a01c010080c0c0002141b03007400c1c1139402d151040c1c0020303d9920102e0a036a04030401c00201c0c512581d5528441d0021425a94650385110156040301c0e02c000b01804814030b010001c103810f6002100b829081d2030f980c4071006e0780b801000400c252683d03940401002450800010050808200c00070342482d8440d08154481c55220382c44100100303002042d00002072041c1d807541c0140b00c0f203441040011a002c030300034840b1040ca5008a052207100d40401021045125241d0b05510186200c220000f51b004107800143d0400c80b080110724501654100c0c4004003040d200002464100ca03101d04584200444501c0741e00f100e05400b0482d000104007000380170341b41002240d003104803a182841407552100e0124038009100b2901c0c0a005024000c400d007014070350100d004208400b40c0c4040c01075129501150515 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 947552014 1250 947550764 947550781
    0x30e1203041209080a1209050f060715020f0d02040e0a050708060f13021201030203250e06130908070b0106030608031b1c0c0b06061804020702010c0510060302010e0901050315 77
    0x43c1541c0504098000c2c4510001000600a4a826504595600c0c074100c0c07610fa2080016207643c0c41a4a80d011000308102400102c407502c0c076a01c1303440412001414070741d654006e50099441000000f007100da000405000d400c903902219600150304000400c400c1c905148081d00050028149501c41c1554a00340805a56003002d1060020458501592221407810401001210a0000300e00c240106000600e10704409540c0203100040e542070b054210b441d00140a0042d08050541c0d90440707000c04203564034000c03a0050121440c8121030a139980c9040341481505842c06801901c201401d1620401c046075000041e0b82a01ca8003035500701340c1e01d104494036841d000503500450700d030606d8001203e40664011440b01c000030b02803118040c82c2c0e501c0004200452050191000b2101400e03100c0840303030b042aa010f0684144107042511154032962500b5141c600b40e441c040303041d80c1d00c8081c14421541d100000d45900141550400115418440000e03110200c0c0c1010744180b01d001c000090690 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 947553264 1250 947552014 947552027
    0x7020f0108090f0d0f020712030818010b0a180b04051603020a020703020405040b060108070908060c0a022a03010e030340030315060e0a0e09030405150a030e12030412 73
    0xa5079403408644a05070440740140185c429208842c01601800f82e0000d0814882e4141043c191781c1a0380b12480c030b540c0c000701c0c42425500ea1484401c2d640d130320b1100c0003c0e038480d0035600019001c03038500c00062880c0c50800006540300c1c082c80394055810201800038024403044440e58005076400e0140e21040080ca08900d0050142d01c0650b11500341030510003488039012070680107200a0303842d5038050340c071003c0a83e100704640c8a03080040d4003150000d01181c0080c40a802304045030320607a92400740704040b1985900003554603a1450801510204480c58244102c601095079000030790708614062101c0c0203100c0380d100c040000184001c088411002e554034000c4591141c0d8200d041da1080603050040040c101003944200c44080039030013042d014024400441600001000d812900d42480310400d2414006082004280b0040c04086080e6a40500f412203410074450000d03203402c0d4404000f000c0d07a449002c1029160803003410414840c4007041244d80c41500200d0112020703546000485a1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 947554514 1250 947553264 947553283
    0x1030b1b03010e010e0c030709030b1008060f0115111209030c09010e07090509010e130c050a080102070b06040606140304020112050f040605060609103507030c030207020f010809 78
    0x640d4008004185507080c0b511043c169464201c0312005a91082c0402c00140700035584c00c004a01d184800f040010303000d01580c0e0748030b00c903c91130200f0305544812a5190800a0310141c1ca010b041c0c03401401746000c41c0d01030300310001051a00c10030f109000c010082d15a1000c2640100000e00010f610040e80c50811130075900820290181c2e80c2980c0d9104d59004242080e200c1c0c5e0005003c0e0b500019080c90540791a605840d451034140040b900c50614405074140654412906c1880c00040020107641e43c1c98030701e000b0039616001582e1406603140078a20003400400c80e61003246850b005001d8241c0c08010340300c3c940100300f5603a540f07480b035000581e48a0a40c00050080034201020804581d103001a4580036a110750702c240103a4031101c081040b2401200d81b410b801c2801e00c502016128070034042042281f0032901e400300301211404501220821803203040143d440900b0501c000301f5070601c140207000b041c5240c1107080840c0ca80c00280c3c880009060f0504003d442d00200c1c01000090003102d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 947555764 1250 947554514 947554561
    0xa0e01181706070905150a030c0e041b080a0e0a021203251e020906040902010c020d0b04120201020414060304020616060617011e0e160f090507051201030b 68
    0xd15a102084542c1c4020480e0154005039240c68005080d0400c40c40d0704540300b141001c2c0606191414804400601805000c80c04020045100101581302d071300c91050409084014440d00525420700a03001c006e01070000444e444c030741508595141004240b80fa502c1c0e60440f010b038040c01060401c0703495800303142811010007402d0141031441925120642030030318850f03094212603106010f01c1102d418060310010390410346c40b42c0022540d25060384481500ca00c14103164102408540110783c0d15010004225802000001440148045029900e00700c59461009501e024103180c05031030800d40a00180d4007410003c00410210341e1598284c9110022030703042c1e18150b0595003016005010281305403200701c00c0300001452100030600660010001604840d0f0800800c90128070090074000b02c0440340d4050603e0300d00f0900ba0303992031100188100c080132a111810000d40d00b04940004e400d10041c840200400011580429070b800d0440f500002d0300c1805540d80b110f04035226110b01e1420f00b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 947557014 1250 947555764 947555789
    0x6010e0d060509030d06090e0a0b10030f11090f040f0303150e2415070b040305480a0b070207080d031a0603040f0816060c11120a0e0118 60
    0x41c41d100000030705038076a04107205110942d5100e0361f00c0221402e0ba048003815170429501e40d00402c01001001e43c000280c456a690303155a00d8588000d26500d4410840e80f080c4d03001000c03005450850443c5802203d601486622402c041d034911084c0101554014145602c87c0420403640070700c0203003200100742e61301a401442c81e0444000000301f0ba1220305c140c1c03610540c194041d0900b0b004001cac801100c5140c40c2d0300c1c07130b144003a140c800b101640208200c0c10400304010280c1011500c14070440c02e0740d080300460802a410034000f992100b04103881d4000d003000b0000010906900040b48824075070032003514140ca86907400e04a00b008215040103204c0d1040c0700c64500f0040d4950300c0100610804084848203030400810400c1ea44019034000e03003c0002e049070f480104040380300070420902d6140010100340341e070f030b5115070598004001d07000201c1c2d2409410310100382d0500c800c403200b4140c07100c1b10380b81c600e180e02c02520f0610180c55039810051303500780c01080c1c00844480321024025800000c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 947558264 1250 947557014 947557021
    0x6050d0b040c080c030d03020d020c0d050304060e0a0213020306010e0a330f081302090c031806060604090b010c060905010b100c030203070b04030e040507021014090606010e0d0605 79
    0x58560290a4804651082140382c0014082e000443c42c40c522400c000c0140000b4181c40808038003075005031289015403035003006003003500300701040020091080c984905440f0b01d0a810a042140d4401031210302e10307002144411300590702c0c00c8044040e03c42d042c40058507134880500480c1c4c400310790300345540c00843d040f40115004202004500045030405c42c50038403030201c103001c1d10038600c2004801e400304e11400d03d1800c50b940100d2984d0fa1200c198104060789200b1900001da000005a0f03d1001d40c03400001804003820051048803030444810008108509103940858480d00c158414582826561030511b05142c0c070170503400f0300b9282c11031405d0003c1e8440e42400c900030300351150240c1c030400b040d006060a040c00b8560300b840c000d8142c0c02071418282d15840300518a41c0003401181003001205501e1000e6a0ba840341d0f501840c0e041e401440c1d02100b40e07031100101c03000f0400c1c2c035512000300401c1002c0d44c0800161590300200a20703062564842c5840461131444a42e54024103c0c0c0c100f0040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 947559514 1250 947558264 947558273
    0x6060d0e01090b06121c0309050f03031e0a0b01080a0c020102040504050c0d0c020a0305030106051c020a0f14040302060313080c061602151504240603061a0a12050a06050d 75
    0x40b0b074010138080b541c54a040160100c0d4696901141440501111050b030441906034000e50003400200d00170803d44117000003031898581580e2048600c15480140000744001100c1c800b186940d0060080804102044481c000a17224810007071000b1645900d522070980c10902c01c0d01624002c0902070428000b600b480f205130b05298004854643c145454000b01c04001c0e80300180c054104c40d050b407501803641c4d0804108543c40d80c81403045041280c0011030400010b400c510040081100983d82d8004e81005903034000c00b00000c80d0b42c00040f00b1402e001c1440543c0e2580d080ba0b0300800c1901d02140050703454541201203014040d44540e207030040d00104800343e1800903400403180000c2c1e095411144000305640e88030001038a0050b80c00c403050b00350024600b02580041048414044103a0010107520543c00200401d07400200c0000d4542c482003001030742a40100603010b4010007024106860004000c0400031440c9130303012099241d20100d8110b5280713600c010094140500a008024220b050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 947560764 1250 947559514 947559533
    0x80316140109060f0b1020011d030a1805130b0a03080f03010e060316060305060f130212010f0602030f0304170a081e040203070506090411040e06120309030606060d0e0109 75
    0x807080590900b170f042041882c103180f0800d8400d9494990743d040383c8401d44c0b201500e00c0076203000c812566a4200068a80502d50700500c00805c9000003540d4504003417000800f030394105420b0200c0c44918032070500042d90b41c00e840b0500004044000562616020002440d0030540e610281414000041c480c141c10101c10045050b903801140c48a446c1d00c031041410742d02c2083d4041010000d0b0008010700003580f080c2c00842d0404401003410010103903510001d0700001c441c0b80b0346404903a0010352100b02001d910f922030700600e500d078200e2003800c3c90500c000c1d41340d110701d040b031550041000000808129441048460f8403000040d80ea45075852a10003803c080810303a02c0d44c80940311a0a00e004000c030b0341520911070b0340d000c0d000e44051486d1800b48031980e0441d101c80b5038040e4940030903071106000c20000d0300040c00d101d1011101418103805008000320b00a0640206810801040c00c55441c0001c0c0503400c51380540e00142c0c0c482070310b080700004020a9007041c01035400c1101c4142880394020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 947562014 1250 947560764 947560781
    0x30d1e032a0e0a1508181e010605040e0307080717070f060501091a0a0e0612030304051b0102151302011e0f030e1f050c041e090f0608031614010906 65
    0x483c50042681c6481c1d0602c0d80300b503100c51603030000e0b10000000f82c200a50b0700d0400021203100d403c40d0301d5000440744a0140420000c00341c2d0136695a10010805403030a80100054851050040c2d442d0a2136600c41c0c9025100d600d0028107138910120030700c0440c03e803480803603440300e03040103a032034041d56540f5190025100030301ca03640d412070502d100b05911507180b10200c450120000c0c58070300030a10349000c514100c40020b01032a4014158501030900300020700041d0302c21441040a0710443e0226000100d910244101050455000841040c41e222200c0056a00041003071010500c0d036195100482c0c00c00900b00c1c24808481c03294401080300c130f0b01300b100c1500d20700464606028032001c4c1d001c055a6010503960282e00d410041c00e4464100f41e440c0e0206070481c84800000e880d00fa02d442080a004034418041c09032818070410402052056100d2401e204980000c00d01c0050714240407155680106001c030030b04101f03c1c00004003000342c03440e00c0c2451062510001d0002c0c0007a0b00b001c1c0014808503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 947563264 1250 947562014 947562019
    0x2030702010506011416060f110705150606120c0403021002030a0207091107060b04180c03170306011d0d050f071701271103060c09030d1e032a0e 64
    0x240464442d6001703850424002d0010300d549030410142030070341481900d0301d2106658250383c809250789507411901130014a00191002266920b40904c0c1130b524100c00006070541b200c5a800600c400340d515141200d464003008030302c4190a84032055202c0940c400c9a00080d800340e41e41d00061071454010024200d5452076800781c5034020b903148596401d80d03510341010782520104104100001c0c445a005000e28003014000042c44d400709a8041225039010005071441c00303105208000b0403c031254220b440d0740d010001542542040400608454051444044034030002166607545460300209407076126081400c4900310410f0041c55078480d030450040c21135141142101d4030011005016001080e01d0750300c04001e002c0c020014100d0110311041e811124420606094a070940d402c0055a001308605446141da07042c3d8a0201858410f4045000b028040100180903960380d1807240c4c0c02c0c01e060300382030101e5520607000b005462104460001e881180201030207421080d4052031603004100c05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 947564514 1250 947563264 947563271
    0x409020a170f0f160c02040e0c0306150f0f300d03112a0a0804050a05121c090f12020901170a060207060b030321011d061216090203070201 61
    0x110062040040c01c203d070300100350751002c000300c0c04142d5000d015141900080c6803600c00c0c2c4070281e0008080d2081c06c1c0f89010583d004040404a0b40740c02c1c00b0b060382100d00c00942d2100341b0212804a8015040745c0d10ba68800d2402e040c0002d00d1791a85444c00504401c0003105018020a60840000c011070202ea03261281c030844607079042481c0248965444040115138a40c140714180c204031403520382000d10360560384e0000840340700e40d003410880341148a208040ba96240c0341008140721803507a4a0744003601c14144020321a003100b00118603c07082104407100c0c0c000ca1146074105445000003688441c40c103070110300e4006150800c4001d140c0007144201c90215050b42e071441d920804102607911203001c3d4010b03483d04400a6010350092648a00c03580000c07070705800b8040000e0964010301099250300145840c0e54144c00070000300e03680502202000d03e09580c807049000d0032016001000c95000302d800c48039030600c820342017041c0c024811010200e1400e41d03459114050181d0400c0e64203501540c00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 947565764 1250 947564514 947564521
    0x605040c060512061c0c0603020c010c0f0f03050c0f07030c0210181716090207212c04050405030c070602190b0712020d02040503060c03010f1a0409020a17 68
    0xb1030780440d00c01080840d011001a12807000f042188900e1581041c001840f5185140000303d541c403251300148000d46006071a628074092031425542410051030400541000c5650169000038068010552a00c0d001a159032200b95000040c420f041c00441c40000100d023450401d580880b003d0440c42c400d0702c5064680c041e000f41980c00800400044d840c940001c00d040c0005c1c0c0401000100b6010b0310300c03c0700c5040c100b4042c88411082c40f0740024110580003c0c21030184076021011144100343d143d00454602100c8000900115480c240300c007104141d500080382000e804c00e2401e01041006004124505051905542c2c1354407401500100b40144000080c02c24008292041d040001025006030842143d4400040f50f0b0b00078109400c0c001c890399a048551070610160442c1e0859003001a500c50814041501e0284024080100c6403401c00050102c1001e510300030b411940c840d90354120340e40e0000100242400f503608a89690b91000c100401a03e500004458110700359144030341f0283c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 947567014 1250 947565764 947565767
    0x4060503063001110301210618120e03070602031608040b0406050714010209060d1806060f0906172104030b0c03160c0221010b12030307020c0306160e18040605040c06 73
    0x91103442090714000c0540091f203d01d9950305060a4401d110016045104200360110041010410350b11014041c3d089d02c211900000c1c01410ba0718118001e108052401400954a11840c920a55042200c160200c100f204e244140d40140903071096290b213407500c940c4e0092407604094010b072244100c152041c869640180300703d40c11844d014183c1840e150710340c051000540046410030328030007080e00c0e0060102d030141c8183e801408001d50100400c1c1c0c5003544201c140c07216030700014000100c03041d084030400d40000d0300c45052489080f80400c215210f40d508a054081c640c0003410b4103c0900030040f00c01038941c021485800c0030203682c507507840301000132569902c20102c0207400822003040000b98444509030f05501540da800003043c035500c0075011690b840d150703541240f107903403001c4140161160144074104003000b00754010030051a00c0c00c90030503242444404042841a0522a190180c5a010070b00030180e04000000d12181003074940310009003400c44064132030500541003c035569 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 947568264 1250 947567014 947567017
    0xc080d0c090b070b04080a0e041a090702030c15040507030c120213060b0a11100e031b0d0f080a0f0207031835070e04050a060c090b0406050306300111 66
    0x840d00300070038000700d079946c0d1b0f229412507000d0701402d4284500c0038004207885e9554015400503035890070340c800c1e02140706010310403c0d91018102005640040c80340040840c1300280400c2c2c0c2401c0c14110a00b00d03281da042240c01d0140d04d81001d440c0d1074603d50b000c0360301c1d12801c272100b80320352090714000301480001000008035481c078041c0f8060982c0800011161900c50040d03220010095800d490031850320454003822038190700c5803a038140e00041800c421004e41054110b0803012200060702c002401c1203402807034200c0a803040e0042c0002080401d1410040c1c1e4000100001c40500443d51014207040103841c0c0400110f00c4c40040d484040085480202d1900101d00c000500e20b481c41c00b0104890300d003004035000c1001e000300c1c1c0310f04a00062140fa012084a000300d00910261075208403d04041040d9074456442609000d450a82044902c2017401107808481880c0f0b04213843e500c400000802042906010400740c60060300c02000c031240c5010340c6806c00440d00d00030082ca034110390902100303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 947569514 1250 947568264 947568277
    0x300718051005010e0307181a040501050901060f120507052701020d0f03090c0e0105031203070503040b220303230603030f070512070503090f06030411040c0c080d0c090b 74
    0x141c240118080140d035000300000d91192000070103441440384c0f181040b81088000c044035810080d01c698600480c0000c501c40000c0b05003083d5014452076045c00d000c10022075040c0300c0d420421050078003402105114010508200c0480d031424092030070043c400134002e07000140710080d0b81c3c6c105030380400c40da03101449510013034406030040d245400b00240182d407180c0b40001428181a00e0f03182683c001001a13183c00b02400203103140f40da0300e5060400f41442c0c101e0590010a0400041050004090704503003980d5002e58044c02c8030032a5503c1280040703644042c140308100d00c00f440100e403400c0542507009071808213158281031a400d40f09001100303800c0010380b0540d415800c20429100d081041c02c000303149550050003107540e0400811109407803075000800990f02c0780c00214001c0c1c0e0510b84104210907448040360542d0450416842d03501800c24a4185184101c0d82c922030f03412200c1c0500345d0b0041d0340b9000143d20341c403a04011142e030301402e0030f5845100021890304011414540c54415143c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 947570764 1250 947569514 947569531
    0x215070506150a08071e120b012102060c0c10020705090a091103031315030207081218160503011503080307080702010906020f07020108010b0c03070230071805 70
    0x940b9100c000220100011400c0301c03542100005101280d43d00b020030406004100c02045040100001d00300005040040c2c0c0000c812104050304400c0810481d0b00610f05440480b291304441007003001c883c042c09503807244004d40100700440c4d5145041070114450010000560341500460709014040f40c40e41124010320b0360006450780458056541d560100c40740501c6100c200da000840c24002a2568206020380c010302070380ca40c4117200e900303a50300c0c48000607034250505608000040d90744180a00440c8051180d07508100000b0720035201001d0595204101e000c143c40e250012030303a4109000b950740c000c41c0e009600302000d1050710303000c0c0b00300c04080302d030881c0c1e205080d52a0f040d012034100c10301900f01c44c01c56489180c0800410550302c01840000c0312000020303a2080d03244005807103804140d001300d0721400144004901c151010007128460343e811501c1c1c1207400303541c4000081c1024034010492101080c1e2640d82400c0000103007000643d052080160000302c6011483d20950302c003210341e80c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 947572014 1250 947570764 947570773
    0x5090601051e06070506090f1209010903060c1404060e12340302031f18081e12010326090a05010e1324120206091909020c01060302150705 61
    0x480d500032034604a020b220004041620305800c41d100c0038603200055513441401e401680203182887d00800480b601200341d0004c0c5e41c140001980045d100843c60710014082e20b0306c480151007a544102000c10002d10000403040c5c40d036131241c2c070040c01ca5030200c584034040d4541d00c1d14070440c0680050590142110324640e1f801412002d40d036070040800c040c1c0400e030441c144401c04001a9001e000164400d40000000744200700b00d010500180e412480c0c2c0601d400c00390827000f201158800007115024190004100800c1007004000b9010340304590b1a88012600a0008010480399689009410341150101103420250941c0c0303094612440003126807001c80c0400c01c000170f50144c0388607142c219004041c5594030305542d4050094a1784200001104580e50500f00010241d00300d21350b01030b20015400d00d012007815404150035202d600703c0c0c1031007101c140480c1944000c540400034080d219050040d5210079469900b2406030607107010880c4122044003001e2005007400058600d0590042d0041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 947573264 1250 947572014 947572039
    0xa2a03170a051318200307211806060e042a09021309060f0f15090302030a141b1e041d0a1a04080306120c030d08061903150b040605150703030509060105 67
    0x7510510b81000d40042c6a0f07a181040c002c20f00d00034451034010400300071004001240c5460003030200c03402c5800910301c0b07413382000d00c804102500c0e23030300c50303040c090055404e4203010f807400303504e1400c4c2668042504580001800001c04418613441c0080311041041403280c9511200e10320b0441300c0c6030044168040c440c0c0c00410403012002c2429003261034504042c10220b49035008242440385949050380c0400c00d0b81d0290380081c1c02000074009400c81003600e6651141080009010b008200321f0316000002c80e0102d0520654480d4041d2a2104000004210404200b240c0c580c0310700a1400030303141c121050105040f0f0200c030040c0d6a01c00e9520025007031440d92084c0c10094007071401701d0903a1f11403107501018000d41d01c0c1002500d049420540300c040391450321104102e11170610482c904004c0322203440c20000a0307030181c4280d00c0500ca02402041c0d034400140032038001d1416a204903803100b20000c11501907030b02c1c0d800501f20b003406a54140300315940e071200e01e42d541c0c00a00c00d10742c0250048289 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 947574514 1250 947573264 947573267
    0x7031416050d090f0c14030a020108040501151502120711100207090501140307170a17091e010f0f05030106120902030a2a03170a051318200307 63
    0x380340a9041030400d10b082119076107058044414401e412030f88500760b41d19290a00c0700d0303601200001c000303242c10100303801d40d20800700380c548034038110003414004410003003000c100b000c0d08030310f800709201041c5158041e03a07421212200450340000102600866201c40a6010783d0412641000e410442000551170745006000450903081d42c1c42c2d045008101000c00c440425008141c02460340d09800340c92802860105400e14400d94401259180701c1645113405050105002c0f5a03240c1003c0030b4246d041c1120900784040c8140c09006600034080201c3c00d068241007005880d92107001c0e65030480940d5811800d59044151501c2000403038410f10040080c01d10071003d501200c513108101090340305003540445c1c500b540505c41290440041d950092001c03295174030364500d101d00030201c0c0d6030003451074940b03d9102c49102609120b181c0c0010300170805c00d00800848041d44803022030304001c0b550341c50b0a2441040018040c100c2d15080440c40d41e44540021903c42e1b0554500414030b15607260b1460 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 947575764 1250 947574514 947574541
    0x80406050705010f1a1203030f0402101205070c03140307090306110c03040b07030201150f0902090609120a0b0603071a030604061503060f090608100b04020412050312070314 76
    0x41c226680e42d2100b400e00b000140d503028080b0a00800607a41c0f02008000c81008400c5081540361603a80c0d009004100504244604a64100360195540010903000700c41c203c80380b240114082d4005800c00050012250384000c200c900d5a0003030751000301010540c0c100254500c0300b40c1c0d2000010b0f0b140b51051001c11034560280e150741400c1c0c403e007441c100c0d007105044c4c11508550b1240c4ca0b68407001c284c05090640a002c0d02c00d482e40c0200341e01c3c0f046814010751070951821406600065940454007500c141c0b21441141d15000c0000c1090340210500bc0d9120b5481004803c1120001d99040c00f05005040005141c015111000c08800f45040700c040c10362584d400c0100700652041d00d13410000781003443c2032031401e421107031550042192800e294200c100790b00213501800b5000c0c5001c0c420032240700007095404618404a001043c3c02c4903c0b00080c010740180d40010100c450230504800400c0000002440107000b801c030708009599900c602a000c58403013131642d001d58151000010040c4101e080d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 947577014 1250 947575764 947575777
    0x607020f12071d041202010b060a032c0318100e04050603032814131509090f0b03010f06061707090b1602040e0d02070902070f05060c131208040605 65
    0x31903040702d6032200443c80c02d5080701e0a10741c80c82900d01c244814004159000ea014071014002804080101c00128146110304810b003400c2568442034092070030a40c1c0810216440041c14200d9540b403481c000c00d881794001d01001d410116401c0884003079040c200100e49c039030351040d181c0d070000d400c2c40003e2101918004180d103070b041c04100f0846070020315482c03a003580344040346a091a050b0082401400f5017081124142118006014004c120310b40081120243d44540800b004080810001a50034210780c0e04203421250070540000f909085036400a040c58208400900c800000000613800305c0380e01d400baa800142ca914400b4039800e41030002e2030740004142c9007011a0a69408100c032103500b1120403059803076401c100392401c0d441c0078016224803801610107880b0048104501a54441c114400d041e051900481c44800780504440b0504070150400c0a45819203040740318142240d00055424070911004c01c00801c0440c80e8000324000598000e40d1700b403425080030f00584881e00300c403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 947578264 1250 947577014 947577049
    0x9042f09010927050105071d03030d0e1011030919020303030c0c0319170c0a0e1002010e06130224090402130510080108121c150815010905060607020f 66
    0x30b60429120303c844070035500070a002c0c1d0000a40c07400e254400410100b91940428060602d542c002e400ca59408000c4941c05070b1030590014280034000603480c00d111034107210114a40c0b81c15600c180c00006103000f584504000804da0382ca070240780d200c031750141d4010200a034151b4414030005243c4e240785001040804462000c40e400c044094002003c80385021100708001058040e1510400418445154014610180c902d0912a40040080040350091881841004010250076426000f0351141d4804032119003615418a0305201302c0d22180a8141c080b8091074003078100c1161b0f01101c044084a03003801070405441c0401c290100000794010350132110900d4284072001a89036104088900400c80a0311800300941c5888000f6041200b45040c1c011a0042000043c007103100c008010808201c49400010703209516603d25511b490243c0c00a070881d10410f801021000c40741f02490b4120350307180c101408540e032903c00f80040390007105002900301c0002c1060310070600d040d250010085404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 947579514 1250 947578264 947578301
    0x906041707030e1311031e070302090d0f031214100602030405090a020702191203080c04050109050d0507030503040605071202011505091503010507030e06060409020303070312020909042f090109 85
    0x403205e10340581c01503814212030000700700266590a200701030b00d0345c408660b0a0440c10031885101091018007c1500101190b50760328407541018020030034603000d41000306041148a420311100c0f02d00c5e8905941d9030380201000c8400040682c400000c607019a0005003884043c4d40740c0d0300d01d0901a412540c0200d034040042d45030340d001500400840f000410b940d0031103080c10602400c002e0202000600440c00003d0101300610550f6004102c10048a00644410b00c1c9010b007420100d05055072500024802e0000050014141e5800000750560f0303402103c042d411840c09800c26800c84425611141f00404080000c1109240c00d01013251300544041c2006105001a0002030856800300c03105008682d462076071001c800820004a984400159402c00280703609070000790392405801c1c801803c1000d169007141000d081501a1180544050520728070790910385400103001782c202c04058204040c041d0102c4940c51007007000966202c0140c010b104603420200382001400c40071000c07205ea60311 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 947580764 1250 947579514 947579531
    0xb13020a0b042414120f0604140714070503181201020403031b030c020a090c030b0a050a030b0402060403120917060f010b1308060a1a03030a021209010e090906041707030e13 76
    0x10701002810442040d0794500590302c2c0c60f01c54240c403501b02402e841d01a502e4225018030ba00c2c0c000b1f6001c1c2c2c0100b82e604000c0e034480e070071508203142882001001841d9010100f48840d241d0101892207a80b407070121001d4004a480a00d00d034201c0c0034506c03020b40051040040d56002007940903100740c885019140042107165542c0101d40030358403981c80340b9031096844a201c50348503498410851002c1e02203c0d058a4103140c50005030800da1503000140c24030000c400403508560b0f582041b5001598071107040f00d4070b45212070010701006068480c0141100c00320701c80300d2070742e040403849900c548920040c06034507909141c0720601c550805451414100d0399940040340741541008007030b01c10b60061b403020071014135a5882c01c201d142c112000d24003d80c81401501a0301e03030041262100c00b00d051050302c1c1c551403841c00482c0c40800c0f04007120307088422034041c00b0310490045140e92049010301111a41018100d00f5550706201d5810040e000484120302e0310f05515201c0075103591a16150008200d084 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 947582014 1250 947580764 947580797
    0x615070f111009090c0207080312060d1403032719150204080303090705040e100e010b060a030b030d02061b1308010c0c03030e0303040803040f0f0b13020a0b0424 71
    0x2030b241100c1c80114000d0501005480d4881c016518044c54034400b0b400314070724041d5010798a005441400350007019130030000c2c0e240d0b2034100384c0d403040c00d400400948214108056850702c980c401e40b80540035002d400e40b460004817a01030154840002c1e207006244040e141c2c12855213039030405c00101e80c82c1550040030524000d070360003d80050500d074405540e0320309250000b1880c01800398003171030040d410300c030910880c42c2c0c0204118041c0c41c00d112001c101c41c140350714403e00400203118402d6001c10081445200c039540b66002c01080d501c00d8040b10780c9103210031001c1c0e0b41c0e0f000031150100313010a45e0442b14044040b84c0090b01d81d550000c98082a410785400d0102e00b950040141000055818030085060592502540e9641080003018600e1814140c90b200c0151200401c06054100040c20740741c1001122159a610590800e031036948904104000d502d52110301481644610100b82000c01c107162214119030846aa80c2103c07400050850705ea062644088042c00040c00700c8403620344d0452 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 947583264 1250 947582014 947582029
    0x1506030c03110d0e0f0a0302031608090d080307172e120317150108070e0607050a0c090f050f04031112040f0e25030203220c0306050615070f11 63
    0x1c2400f200c0030407503621031411035142c41c500c2210411203034020f021080101c0c0d00032040b13a09451346074489882006050074103000500c500080d0326004140300545005114026001e03600500030382c2da4521000e6940b64001d10b078840c082d2800710340c160107a80040c813000c07915115008002e100300f1020000c0c696070448030340c8001503200f00381c0c00700342d000150000c92000d01a0003a0b0000e4120180440350f40013900080800800503c94014810b8820000201e41e03546002e407030341070b0342c0481161105025890109816440d5108a8400390b00341050311160038028001e591150503220251409030352140c80c11180b0000312444254103000f208000c5815060350402800070f05580d10a01e45018540901010349500081400c0545020701850786001b00c07540810700d107644541d20b40980c4135100c8a450703400b0710000000c01410440d8000c400c100b00450388180030116402008100120740d01c600c00c0c06020740015103401c860703000030007031781c000198480c01e151031043c0284039a036820060440400c081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 947584514 1250 947583264 947583277
    0x510090b12010504140f06060d110c070602121c15050315070e0f01051603050d0c09030c21120e04020f0903010515240d0c0519031506030c0311 63
    0x1d55000360040c4500c1c282406140304408035024582d6052414403030524203e40050559880384100003003001c040089508200ca5040181d90710a0344d41c0789034112540d44002c144107010260045100f0000c2c92050035041d5643c1c14041f042003a00c01450201c41d10061080702a001c601c0e082412003c14903032010800d2150450b840340044895003400030018010940890019210b4402d4540103002c0c0c0e40e014054601c120030b1400d500038244154034040c1d0b007034040c00b40030f0400103140800c4a460740ba0721510700c80c103c0c1d000740d080050031600c64545180100c20501c01c080e202d002c1c1032965000807140c0f98014080c45061900d90b43e080800344c002010390b8440b58604450110100d19141c00745020710645e60405500360480c48070300007600c00f15070708006054001c3c0c14400c1e581d405c800a80b08040440d1012054400104110755000c100904039800501c2c81da0351151002c03059085a42c000c0c070640c1d2915120340184001d5a00d0060124050007410322140c042545800d030041d402e14607000075122 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 947585764 1250 947584514 947584537
    0x3070e040308070e032404060b040c05040315110a110a060603140c030109051b12060a0e1e1504020303120c1903150e0403140f030f13020108010510090b 67
    0x425040c0303104024041c03c0d140c0300d04c520070380080350304040e04060264212498500000710007801da4032420608000d0042451240c2c00a00701003072890707241d601800900c107580c4200d503510360300307624074007a0001c50b1580341150706506000c00001d9803441c0a04600001d00780261704440e1020b466541e0358060362403da008071a10400b0000b10007100e01c0074402c030390f480e500580081102c1007071522401da6905282c0b00144882c80c1245103913070b981d298100103011030003612049a03600d042c05084c0600410301c09984480e2070048450f581240d0b0a0f0800c1c5e0380100c1d12075002013184007d602c54204041c4005001264035110030481c0385108250400c090b446400018211038a5030391250f070104507400c3c6201c1700c0040500c2c1440501031010050242415101f50740c10501e890b966a213815108006688140003030fa00c1c0104004250010f0300300103522071500c071410484a6124204502600102860000c3c00314100000501c014105962089211103a078581041c030340c0e9136040c0318950381c4d2107030403040f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 947587014 1250 947585764 947585777
    0xf0306082d0723030312010303031109030f161502060106031d0604030e0307080a240b09040c09060605071a220b010317090603070309030201021308061503011b0e03070e0403 76
    0x41c00003040303d000000c107402c0c0e0246140111a404541202078140001018103a449090704141050f5805803603442d00043c0440b0000c1c40c51040e65965100c46000708000d000078145e01290079500c2010407544020b2580080046900f0b200e4154082d00300a20004840d0080d50120701e00c0c1901040150b0140e8000e45409501c84071180506082080981280c00154803060f203180000d0303000c02848001006001d402e22a940800e002c800107410405c0c2e20682c020910350500042c070480041c031804891004600300001aa01c1e4400d8420b8051220040c0c00c0303c4c1490b202c13004008900920b5588010b10000c07440580c1da981040c0d01c681c03039070130000307407660301c04140107004110030008521f904242e0712680b141403245120020310340b484010300b0201007549a080010405000b50107a88800c1c01401101e8078982d1101c0ca060ba5558013250b08014030000c604401200e42010b224100d10b60406800a80054002f06801e503401d480c1681580c0c3c051082e01c10009200301101c16260045100750f8550 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 947588264 1250 947587014 947587049
    0x6040b060d170d06080613020d021314011d040305190e06030c072f06130b0409020307030c030506060a14070c06110607020102090f220f0c0f0306082d07 67
    0x1c40403a0000d400c5018150703c0102070004d91140c51f6401c0c00201c0d030444420f0308000107440440c2c9250b160381c2030140d9480c1005008480b1800410040341038860401c0318403c0708180d0030803803e2104041d540034001c680304100c50f00d01c2ca2428200038545141c14104807005825000200721203500844600200060100b1070a0801c60141c400207114003031001066201d01c440800825000c03094507806104850000e03040030744e14441c0310b0b10700003010700240e000c0c0c03a1907440f0a024040c2d4400c40700350700020315001307014a500e802440b039140aa10064150382c11701c8910030095540c501c0010300690380c88c02c1845035000040005421402910103513070b0302e0152582c0302d0001490100058254000d69005101115041c0c59000350010000000c4070340304500c5001345046a50300c84807607460a505c43c10034a4038100390707a04e60031007010703804180e0b105c03045071510090480445001e40280d1400d50448504040c2544a070f50022800c1591100e503949591840c0341c0003031030105c6662103903170002c035800c00d007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 947589514 1250 947588264 947588287
    0x50c12010522080405060c07090c090e0601022a061e07060c020a03230d0f0b0f040612080901110604050a0c090911041d12030a06080f06040b060d17 65
    0x9000c0810b45285400c03881d803055680440e14080c500445001d0600451070003a6183d081080700001c03c0b82c00750801078540508401000c500d2180500604008401c000c5402c41d440041c295103015075002c40004100d00c800c0085541408960825a011030f06006000d42d88105c0e01300381002c6224545103d40c0e407403607442e04100742c62001001c0010b540000c810344010a81040e5188004910307001104500c0980808424160084901c1040c03d01d161a040350f8a81c402035010344418001101c50b0100741c1080000c100540324a801900050f002e02d0304841c0001da8101c002d00a8840141092020150f544240c1441d0680440d0255150352002d420001404022408500030b0070000703605014901d82501c0b2100020051808140920f030790f103141106400030300c1c44041c1300102d880306950402e0404002001207800684907200c00a19041c0d00007001800010b000303030b00c5079101000d0229690703251902d904501e03000301202d0308900d20058002c0003828000e005540c08082d001c0c2a6116100c1c50304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 947590764 1250 947589514 947589541
    0x1529190c02030f06011a0c0a0c080102071b0602030a0305060d0b041b0618050918070b090901050402070c06180b0a0306060e0307060219150c0206011d0f040f050c120105 74
    0xd81d6200d0350004c0f00140180700c4101412100c0c54040b202c655961125455600c1ca0038449400241c0280d07000000440c80c05010b40043c0740d0980504255801c0348038249007010980c01510031100580d004000350000c0c00d001f60031082d481200104400d0f421045520751140301442150200ca1080d80e8030603000c0412503500e14440940518030300700e500302000380035558080c201c07402081c0c440c1c960384001810140450f04403034400b5000720191101565140c0407004650056140c0ca407081d0400000442c6604061003a200040e81040c00f2444092400400340d0308024114210485204018400708002c000103000b0880c155455400103940d919002d0014010b451700d1030300e280300390000c0100f0404aa400500344900c03005080e141d02e003c12136840c28414201c803021040701c0c01401c3c82401c411540d00841d1160403608100c0e8440e60041070030035500901d45089a26000070300350280840c020070455035625004a1090044410801d0501c00081ca1f280760f50040620a80d150420480100071820 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 947592014 1250 947590764 947590783
    0x106051f0909020a052718060102190206031f09020f0a1d03060c160b18060903030f0a050c04030609061a040b030606060702061b0a061529190c0203 65
    0x103500310301304075135110014a28880d58036900d0580d01040384403a50100d481c4250001c18400a1281d03c00d107100855100710400c044800501500070401d41d030904a400301d000c4114190f00902003440c542c2e038100e0007444411003001c0314546000045000c203204500344020104034100300d410030345075400c01c6030040c13118a0405482d000c036104040d000300d094600080d003e8020780100407140d141c02c0b078010f88028180f0603e0018000d03c51140500207803170305956440140c02501429030310160f6607010803540d030f80700c19220300042005500001c0c0300425147d11081e00000d811b002c5502d8140c3c2d0b41c54200698070b0350041a20381c0d986d00c5124411848000030311180f1000d05a400780f00140c0700740b00007925540c0c000c2440c1d00445001461404646d04c2d40c04851554215006c00c1000056a850482ea59444180c003190024070302451440c13001c1c2d140400008443c680c0d2030314290070f0760189840c80001280c900152180c602400780c40340d0541c000b1004010404159200c2c1103000e0940101860020705a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 947593264 1250 947592014 947592029
    0x603061104061e1b0b0406050112030207030f02060403020406090b240a030207020d0f050a15020720010207210302210306120c180901050708010e180106051f09 70
    0x70002000100c1d004910a515044207400301c01c48100c20b000103481c0c200c0144540b0a000102101c0c040400664800d0540168020942008260f80b80c00f4a001304207184e04000c0c015034858041000000d10b05e5200b079645a2000c2c102a0516560381c3c0498181c84c03098110005544d2104010700e07181c1411f078a0f4006450301114001c140d1aa01c2d9600d60740382c4103410303202c82059000241c0005544400c03404c020600d0b031105461185603031504003181c4034240002c0803500711070450a01c4040c02214000e4071440368114880215078901c030600e404001c0c140c007040744c2c1075019454000403000041544000445441d041000d2040310300c0c0340081c1846469032048070001803040404415401c1101038a500500079a508035a0b480e0041003103290402002426034440a8400ca505842c8a0311075000d0180c00720300024001500c0b91442900c540b90240200b811072105200000d1000d542d0f8000c400105800e40000100d4a4542020590050790f000800404a0a4000021029520040f044001c0100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 947594514 1250 947593264 947593267
    0xa030b030c06031504180c05090a142e030c06110f030a0e0102030f040914014511030103050607050a0e0618030d0314060307081203090a020a080106030611 68
    0xc0707500040150101801a04a00b5410f00c4448519140c607030000101c00042c0100b2103d8280c0b0f0320304401c1c01552130040c64090b5145034045608614940206041c11011051200403075681703181784818800c00b00740a51a0094030110f461010094a85001c05540120b11041c060781c101140a480052001d025118503407005154a040031004810344000402e0b80c40d060442c200c07480e004138035601030190301e0700a1400c0040c00192945203a4016440703081c1824423552a030f13980e10007403400b0500300d06800c0c1841c041c030755420b140101da11401c10f404900140780d1808030099481c01c4022919240c4030b00140101c000011b00a0000c100080bd6100c1e260745805890422100f1004218844901f081801100702080d4140c40000b9400c540500c0080039040b25011460700d00020007074006906552240e90240010408a040200d00c0c882552040c00043c1411404031000700b1042d4001442070009000c6c54401d070307006958560300100180034500c00491064110300b410b1007104d4242940c2540d2080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 947595764 1250 947594514 947594533
    0xf0402040b121c0905122b0f120e1506150702180a020d180c050a0b04060804060e010e060f0709061b0606050a0f170303070504051e0301020a03020a030b03 68
    0x3e00400c0542c0065603254004800c0d001c00d8483d013115400441d0300c05018526044a0301d000508010884004408250408104800002943c2c50520102d00150040700500401030088803102920100c24400045002080b183c2d9030424074400b5a00d260408000180300d61071910071286c03800f190380e2040e81c914086e410f17400545007118940b0350000e03c04040c40003821080242e4141c4600b4400e14205101130040d00510700c810780e14171107044555205041000c112800c05038011020380308036051a81c40c0c075042010650345a00c006000711405912164005007845003030003444a4076854130024801da00340415420140c5000505040800103940320401c120742d0300800028950411169102d5801544e0501c03401502c140e8001e06e40001d640c1800090050711503110310210340c40d00ca40102669141c4110316101c0c4016140356001038401d000903c6103181462001b0201c00c0c0d1044001803801300340001c44d00360f030442c403c07100c040390f4042261070007243c16010707044104a040340940707039421 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 947597014 1250 947595764 947595799
    0x8010903031d1509030f0301030303240e0a151503020306010813030804060902030f01050f091e120f0d0f1d010207050607030b150409050718080d0813020402030f0402040b 75
    0x80802125143d01011400414a044000d02c120b54100480311506980c0e03684074100030b0050040c0000c2c1003e6030040c001c00390300507414844103000b81e03081d04c120341e40c1c00d071a81d031149000f90030181d00030402c4241480c030008000c0482812904450000c1d14090b0702c920f8150009020700400900341c0460103454540c840001c0e601821003580306a0000c8001020000b6001180c07400e0080144a8803661925041c031003040252292070388501b61040850300c401e0204030024001942c4400369860a030721802c09280303502e251001802204501002c0142070008520103c1c013a0344d26440480301259076600402d1a054900518042180c603004c020351414989503103c603600c3d10010501c00400d44d803101c40350f4070b0399a60102840d10b885144002ea89407500d410700d000042400b90740310000700d101d4005012000382200710050460b91260040c210749001c3c1c8000b80c49182c07000300324600e050250f060480045c0e5451000d94094420075070b00d00b4051500d803042c04121a05000030b944981c45450b0316a4855 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 947598264 1250 947597014 947597023
    0x180606090e06040f0b180f0c0909040b0a330504180f11041e1506051b03190c023c06040e0723090d060c11010608010903031d 55
    0x88410f80780050301e140c070303c01e02400500307640d03030b8166010451140c0041440c0b0f42c514a14000c11013040d41c40da40341c8400c1c540c210184200d0344c4180d00702d1f501c180001d006c00c555004203580050420781c08521002e485902490001c25a030100f2a119840d60b00c154107901e0f11380040740034010070b6800f04101c0c0010f59a030300c0101c01da01001001e81141074811410002018680138080314082d1043c400401d044401304043e901c4003418012003440c00546081e1200c10848482c1211040e40381d8070300e4124007540d6008440b024603007100c003521007000091100503030461490380480260b556010404540e2041208038002145180481180c0c841400070030b0351448829450b1001e90007506420b440a603000ca4854083c651044a012604a0402142d1030f0410a442440c0e0409d09410103840e1010a0700d822a0081009040d08824880034640000e5002e80c440040128642840c032094001e001e070081c25141c058001c102d03a80d464401e2401010b415014406c3c05540c1500206805220b00c00120742d074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 947599514 1250 947598264 947598271
    0x821100806131505070e030d0c02130c09150c0c03080a0206360c0d140d0507150207020d210f0801210c0f030c03030908030307022a040501180606090e 66
    0x580c1d80b08042400ba50141d91b10600c081d4001c0c2c00d50301201e400340d6015140008142d0140c6c007a582d000f100e5403207410107215124241c101c07501d0b858800760170301c0016214141000c1c45a000d1045203010000454922106000110f1168240c2d50341c5612000d0f009040c802c014041550110703243c8410546000d100c010464250840483e4101100c403100d41c0d14507141d60947e13a0360b0032000f03900b40081840710300c6c04da00080e202c0c180c00700c0310a8840c07200c0480c0e0600c40c900019244000c0151a2502c88116400170700344031340003d1401c3d00c1c40101d501d468007682c0400e941d0802024028406540c41c0d60000918a640c030170138200075034039624102001500c060000103030900100500008410080d92220307120242c00400a913010a5403030749000319400c1070601059000c2900c3c100b0000d42385c60300104580c41401543c0c06408590070102d04c00016019034203281c00d820984482840e0031b62241d204d071500074040002c000039135141c1041118110780355034000200b00710280c00b0601c854848590030540 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 947600764 1250 947599514 947599553
    0xa020a080904110d020316050301030309030303092102160f060e040c0311040308040602013204020a1e0504140c041707170109030e060412082110080613 67
    0x380c4102001c0007800034030341c2d107040e83c010740000b080119016105901840c415503442c201e001d2114103410303054411303020900c0300900203a0720b108140001b84c0b0035041040c040c2e200e00c2001901e540c21405000300c803500502510010b0380043d03006403d228010a1690042231000f145104060500200405c6550070805050050780c58488080402d0b12a0307000074880342d0104110764a403500c91a20038540da0251040744010740c20441074040410b00e54400400311207081021621a015440c01070081c3e250007402641e02079032401c00010b68681008110302178626501281c8121400c0c1410442214100d050702010044460704000c05440f0000032141550100f40c01e802403124000401c51074468940c105244c01400241d02121811b41500607400f168440d8580b502400000e00911000d409184207401c0764081801101011a2a4400a00c441124454070800d4119410010240701600b074900161151a000d41000009010f110140c0c0207200c0c1001c030703400420f00381c65012004280480441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 947602014 1250 947600764 947600767
    0x4020c0a020909070306150b070204090327090501081b1c120504360e0703020a1215050915250807020c18070e1302040312140a020a08 59
    0x5488100206544264010103202c01d500d07182c0b0700542c03100020320045821504003401819142c001d40c4800d1701340c54070800c16a05210a980821018101101c4107405000b0550013081c116a503814242c14480e101002442e00c0a2401c81e1040031120145e101c100150800c50541e4162101c0f050b43d210006021035000c0d0710b040403130700c07440e00d90300d00e80500502062550120072065078000d03020b0403c80343d1114203c00c100e90100c01800e0310f00a80441c4092442007002e5196140810394800c175446ea480c901244d69898070b07580403801042003a0803440c0540b200821450400c4520510b00014070080700d01800302d13017850210103942c2c141800016030101c6414000031a2004400300c1070051b090480022000a000c2890283c01c10b601510b4480050081000203409414542c2c0302104800e01e501074003131256181329003224108100103056920000c0560344030052800b138005440030b103000c1c0400d440d0f51282290050079030b501c3c3c0550715644a005100c000350f501c0d00412200503d51700440d00a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 947603264 1250 947602014 947602027
    0x60f0506090a0902121501030e07050103020c01062606070c0c05150c060f0711150c09041d0d030f09021e01140a030603120c080406110304150e130203090c0402 70
    0x418041c1660448010a072010401e403001005403001140544103030428081b094070391200440551b000c1d0880645254442c40007080039500c207034010012204950f00004565840d40d1843c0c81c1d6a810559006050b03803002005200b030034003402416008907139820501404842e40d03a440c0d07000b074140e00c6040d03c030324a00c6112104461a2400b12000107041c81c0c01ea07484d510300341d107410408000070359448000581d0581c0040c905a0001220922416106100303c01c1d50340d404241209903200c150b0440d0440d440c0c030948030407046c40d00c1c0c40608181e0100702800340101c901400404880b180303240340344103d0030900104050784a00c2886000d20300c0d50814401601542070050310314211381424102e105c58005011703120698598400743c2643e01c11500c4120200c440d120480311489900b0703015121810030802048814014141004544110410390f420a075541c12800300c880d169100c07250214151600359036891400d60417821411210060442c290704280c2c910640c0c984410307500c3c6000d641d000495 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 947604514 1250 947603264 947603269
    0x109061e120c0306110c0105010602030f07082d03070e03160509060316180614011718010f0501050108160f0309080c06010b0408060a0e120d090c08030307020f01060f050609 76
    0x100700c043c5400c04802c3c40a01d03080a802d141c50380c0309241d031740c4075946810300105210340f0200403160b07a050440441800c040700c0703480e42a0b9560290019507008090031600d0480c100d80c3c00980203100c201031400507281d1508000145c441051480020322a0b0015440c0d09070400c8401301804c02e03602c096620071003a648080c0440e142c40524104112500d49415000034140801c030000b182c503040d1114180100c0c2d0396240d5500302c040003130b0030b030750b001c1488150b994000c01a00d4110039404030380c11501409040030f0012030ba084070720040c6500030040e00d80340144140e5070071220550300001143c0304900300740c40030301006001c510742c041c94008054640d41107109200d62102641d02c0710544a05039116540d445d00d05441130742c080c1c03140010602a9000040d114500ba10030558041d0400002c1d00303246040390203000c0507900683d40300b07004580c0c1c4c0c01c0440100340085005405050508c006581d2030902c00070107480c1c690306c0d4210121503030419405105800d820480d54040740c00a03151030303480c0e4200100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 947605764 1250 947604514 947604533
    0x6191716060e150715060b0c0c0a0e06090606120a0203010f080a0f080a03060816060e0a0b0301120201110d02060f090304180b0616050c04150803031f080d02060109061e12 75
    0x81105c290424402144c200c010400a0407520a007608407161241001c0910101844034410400328603000800a59079041425007640e000000420191030b04040c8414651000001e8440041980d8040014041d403065882c840d40a000c5440007002a54120b03940c0c1321031036500b5080103240c04404503451450501a8201c0c00141c00180b00381c9020300b0007035005602c6090725104140000c0d103202c0d20060075050040703247e000da03900a80d0703040c0707140c0c20110301118401054408904100882c0300c410b44103c001e00148802c40516800b41810303081017410f0402c05200a0f003090380070b4100b007004108000c501c5000704141c50425002182c1c0b100b820000034828004c1180c9164480e5110100000300075020070594000702085504111485480340100c1c080d4946000b0846141d00030400b00e00c000300002d41c1c070079580018040012400e511050350505000c00f100c0d0344409680248010b2100c46520f010300401f424100c14804c2250b105918078030500c100501c40c0510840da040340d05c5007400b00989 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 947607014 1250 947605764 947605793
    0x60411090d02310f0606050d05072a030807030b100804050c041d0615010905091803040b0a030e06070f080403020109050303010b07020315090606191716060e1507 71
    0x2914200b00490f1200c0c0c425802d0f00e4900c42d820020314001e081c0070440000d1042509039809581c5150500c641d2454000042602030f140c0024490301d00303000d00e40b62440042c40190003101d603175214200c03042458040e02050b030140001c1c081c9400d11002c42080c0e21581c907900c54000c0c2900c2e01e484182c03200e08040d401c0c4042d0310304141d0046c9c104a25052002c00300c511040c03c94103d401146c0d00c5a4510748000e540000040e8100e000030807040f41041a840c291220b96049181d00000c0c41c41c00c00206115803950f4440e41c02a04840c4005c24006000b0750503204500441d1207aa014007464030b00300d00b0085c00035501766800010300640078041814180b007548407107a13082e408003c0307a030b9950315250b94261603000b0070022440ba00c1031040b46031079122820001801070745a04c0c000c00e02070300c07410200088c44489a0b5007181030000301c00001030071500c0e15401842fa181500150840b0740c02483d0413600e0100d1508550240120142004900d455841a50305a19008540c06407202424546a0030380f52410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 947608264 1250 947607014 947607049
    0x71103120d020a050c0d26090607030c120c110c1f08040311030d090b0105190605090f0306161b030e011b02030a0506010e0709060509040e0712060501030209060411090d02 75
    0x1080403103c080d04030621710002c3d02840400030403050120701040340c87e98102e4210a0703030703048130000c0340c0f40310b000750464005003140d400c000c4200e080081125049964958401c00001d41112228865070400e20540700c6c2c1c0c3d40103440f201e001d04c005a01100ca6420850181b404101c0010001f800b410301c1164103041d80003007001070b6940c51081c1146034020380f6461030203aa224001000014903032900d220540c41c0c41162201c0c8107401483c0c040c068a258000440640e0004180311440400780d8051106621441000304000c41048406400801d034003020320400744801525086900403d0b0442c58400814a007480c000c03c0403116441c8609075001d40301002500f41c42001c061408116021840794160b0705030914a90442c3d541c141c089860007614880c88003c2031007008041c0c2682815040095a00018000c8501242d40d55042e0314003c00c0282c020f030341d6030b03076100d0040c421898140c44042d0021030407181801004148580c810003031140424140c81081013007040c0046440d03110208021a411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 947609514 1250 947608264 947608273
    0x60c0c051c091a03010801060b0339040303200106031a0a06050d050604200d1707082206140d09050a02040f020c0705191a0d020708071103120d020a050c 67
    0x40103c00c0515003003030041d42c106509160b00031034880e01102c280e0744503c1c0c08820402010306610559410045c019580405040b0095210b81d20503031401c0081004500c41d9a41c0301c0f82107043e080715981c41d4090b1000c1c3e499a41048020000b2502c159845000640040708500caa0f0b1100070500c80200b141d64800354101d68001440001c1c05408286140f0941c0550394075880e40c5040a81c0c01c000038842d000440d803040207200c0303071004030742e01414a03400d902d40c2107107091a04a0a807500303001c0d904201c580d0144030004901b0711280b880c040c54030000034066410450b00c0700b01007482559081c0035846945c545d0641d82c1100a0601801700541c0640a4000e030003004401c00c600e4084001e03500001805a01340b18648000440342003034410740031902d81580c2010035081c180640304401c1d141c0e031004044245400e04c89a42e10440070320003003a80300c0c8a045140e580d80740030320b00310318501c409c022014800c0c1c021600c14001a0304c64011108190410840142d80e40b0340c220090ba594021507540401d03c2c4034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 947610764 1250 947609514 947609549
    0x5040b0a0504050d0c0302091b18040207060203090a020111031804050c12010303350606220b0702042301060e010207090218120f0c3a060c0c051c09 65
    0x305002c000702624008d440007213a903900c202c4501d5003071a05149010010b134040281520203003143c50b400342c100100500262914006454100031381c4c00c00c1c0e80c0c0388c00540184414000315a01300d40e050403086501d40103075042041d0400c5041502701004442401641c540c00000c88030b22403081142c1826104840d001280e50716820001c0c80d00240000510142a16288507850a4241000350b0480240403640c0001c1c1e581c0c2c2401c0c000c03280c21101d0408541c43d050406141060700c4a9102d401602001c40041c4d240e0b8443e0041005840e05100880781d1403190078102005c0007139201c40a4103580c40b03401c00840c1142d460004034035080303699102042c0c0740d1001c50020311400e2040720310f54a8000c2103a014981403200c002980c0c8400c06a2051009684082d41c2d61840d0304203a14481220010361076040c83c03c10046104900e5082402c07513542c2d20710700c2100000700b0010740d445191315252103850005070300007141d9581075503108009200c03240707072a004860300c0060f842412148003400316070440030126203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 947612014 1250 947610764 947610773
    0x1030c0c0b1e150a1406070209010909030201051509130213141506090604030308060a0f0b0d1a01020a08031504060b040608060d150504030309170a140a05040b0a0504050d 75
    0x146202d014103109002c6501040c1c400c140700c0c4003180a20001005603071100d2420204101d11010660f44a030800804e2041d0b50140e51240c0c946802800e030524003003001c000c145402401c48a0003848140180b40031106400341f61501090503912031010302c42500c02c0700003800040c00034034842000f01910303410040500d100b810845d41a40c00f42d5448107800410140d0322040044c0b5004841c24190802c80500080000c607100300240c50b08104050f101c265090340381d825141680c443e40d00302c00001c00c0f0008600c07604100500c10f0081c0c19142250308145005003d000039111624401c0c080c1c60382c100030020a404080845095064020040c410000c0f161344040d0f4420720b42142c420394020030b20940c009105406c10030312200781c81c3e0348550195000c0c030384040c5a0000707200180c419002c0607660100000003905040c4096205078840d59143c2e216090108000d00071003045041540e030b0b180604c001507003290001305990940710078020482d110411400c048825000350703130107140c0c00102c1028000622 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 947613264 1250 947612014 947612041
    0xf0210020f012f0f121005132901051b0f1606090b0306060d0231150306031110020a1a07110f0a061a0d0503090306071d01030c0c0b 58
    0x840c0460076541c002c1c802c032900c40b80f00c0e00a0601c200d581020410050010200300100c90f035001d00040c90448000b52a0f1000c502d0040c4005110108036580d001d01640e002e102540b042c0c0b8480348400c492022050850000701240030b200410b5800001882c5543c4a00740d041c043e600320a4169011210b003203104000201c1c60055910488000c90071054010440381c0a1008991083c0d00c00b50800e440c00741c5040100c2c000350700944000000014810348903010b603410490114250203405e907032540d0b0300d00f0810b060070710070b6541d07140d84185490503108000040303480f002e20045240840b09550030440409090741080e55140c4028100b00c0d5100041038002c014400103409006555a00b103030890400d07031000d65403425400320401c9035201401c0341000840940003901103e0001d80c40460320070003030b4041900b0000c954400c6560f0742000c11120600d00f0104a0168002400d18085503101c560811038402740c0b000f207140e0ba040503111140e00038031a009903148450903a224000380e002d850841d0005803075 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 947614514 1250 947613264 947613311
    0x3130203011514010206091c12180204110403151a0604060507050c0d050606120319020109120e0108161407030c1a07210603020a06080108010c0302070f0210020f01 72
    0xf20072100000f182551000405c64420406440141640c080c9034005011103542e42c1402c0d0108464450a011048018005c81204400a0501c030300001240e00c1044191481e03c1c030383ea41d400b1070500003000800d8110071880902500040b00007000c0c50402d410510b0600041c95007500820f00041c0010020fa20000502d405400f07041a0755082c0b18242c00c0080d034440026000d442540050b0102d5510f00d07021240003410015041101d181c03291021800304d002094100c4400580d56807a40c3c8018003030181005142c038855403418007002c40310100044d00da4400617280243c0c40541e180c0c116802402503114600c98404826181e884041c9490010580183d0450459036035514608111360300045a0099000b0406921010410350311804212900b00441e054842d960b0b48400340040075803074406044024040300d0340c070320003198103000c1010f00351034003c1400006c01d44104844004940707504484200194102d404403400014450101c2c9440701500e12000c1a500e407008020a00c40241c102c0c2c0e50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 947615764 1250 947614514 947614529
    0x402060f130611070f032319021806030601031b082e0e030a0507022202042301091a36010503040f02040e0a06150e1f0b031302030115 59
    0x7100701c1801d608a413220344602c502c1c41c01c0108940c050000905100d800c2c440c024101100c4160802030300b41c10f40c0341c030f010b0051003040d14020500703210560070103180400364800c40c491640c460303040c50b50110b941c500052001806d41514482002880300c440b0500d08002d0540000b201e07590000401c1240344039000c800041d10091042181a100c82014050440e21010a8001e0350500e00600c2064170554800b200482e4003152011040504401019000c41840c410301c0d0010f071560b007000d0031001e102c0460f040c0d525500303403824143c03029682c0c00140c0328141c1d150109103290941482088040328000d0002154003540141a008441d40c0105003035020f411900176214010002c20005441c588801c0c1c0c1d0207041c244003210700c8005420150404050f064160701200c491403141e8036004101e440c0c160044d2424a289002001100d140342886600f180285400c44440d141c520045100c8003003600c183e0015800c04400500401103841d441c06007150040c00a10014580080019110800740282907 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 947617014 1250 947615764 947615777
    0x3110d05010c0f030623010e040605040e0f010b09010e1911030411280e09070e070206060109050f01020303190f020705030316050705063c070807020609150402060f1306 74
    0x60001b642c210004591080e059081101c1ea0030b000046a00201c207842e000e401685850000966864501c21240c84c02c10701c80c0508201000304205509440000c0c20080c895040000144078a01000742c4c0039400c50f03940e403c110703c6c0011590b81d0602034211440b441c01c181001008020500c041140c0c18201320104941702800c5d40b410f030304a215144015107051003070b2404043c0c280b041d070580b14401178100c950b58081715052640c888850708060421980b11005030040001e1003041d580000d210f17805800111070000003424100e0001350340e404000d0034510f541c60041c8100058403c1d03a0b0140b0410303c0009425517032500d40d410059641d620a548031346140d805010011031480c414401d6845880d4404083c2c1702c03e440c1e1001403031088021103e003011003611050344500b15050080400781e2100d13070902000c4030f840d01290262a0110041c424410f5401c50010000008404601940850403ca010a1454640d400491424041c018a410030124002031090f151291604d4100403600c2c150307510f0703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 947618264 1250 947617014 947617019
    0xf06070809241e0112020402130503070b040306060f0b0306040b180106050c0606030d1418090109050405100c0203030115050c0d030b0901090b150319090606090b010c05060103110d05010c0f0306 85
    0x601210f00910451458100c003456000043c45c064000300b0202e44010701c1880803130348510000b41003002c40d43c020410f440700000c04100304100d0380201c0300280208050310000702d19100500d911844000c0072903202d695128041d40c00e55550505000b0040d4981043d01322540e140c1d04050210350104484448501c600c800048462900180c0c100c42d402841d034607190101d40082601c0941d0b04140c000c0380c40d07562449241c120986410810500070f00d110480820182014140541010000040c8004060900e07252201c0640c0010850341103a4030611101640300c0c2c4144100c582d4001c0c22020506402a4000d0126269140c0c00c0006465000c8039600066643c0f65a000c046601043d40d40c0d0f0801120b0009078105030208000e141d100c5090562014400e600b502040c0484489481c2240c200ea80d4817030038405101c0c80e21442000c0d06003820401c00714030744c0c2d850f49590f88205101c02007100b1008035800c606070301d44160000d03046d90b002c8001c1c0010000000060301807000c9d8a800d0700040e01c0c00200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 947619514 1250 947618264 947618311
    0xf0c01050c0d0605190911040b0c030403020a0803070b150a03050609030405011103040e0f0a02160f03141204020d0303150e0f0a02181e06070501060f080f0607080924 73
    0x510340c00c0881d2843d00c8442519100740040500847e10641c21b80000c14440020031410700b40081002c0204040950b940d0f500318810014100040d802400c140d40c000d200410010380d007010341036000082e2810002c44640c111000450a01681d0402420343c0034450510614050000190080d10401d8841d03c2c600c11030b441641d55a40241c0c41240000000d104c081924080101e17246500004064070240c941030001da603000a0502c010001c49448024603544014982d021030300c0301c003030b0762115401403070501b1070b401f002041d03075010700f01920551401c1c0da01c0c0c040600990007103000312604413048103a40ea8950b50102001e80480d0004050000e020000e900d0301082d10859003215180c038038058000e01d6400502050305600d81d102405240c03030345c64101d42996010040d00406101d0400444e10034281406011f05101c00c0c0d100200369400b592815501e000007007000b507848040c624001e030072584d810854900d06200d40009494a9a9040e02604040701c1c00820601c5400c199000728400c000242a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 947620764 1250 947619514 947619529
    0x60e0f0703060605030c240a03141e160f0521040f05010e16032303180a1509061b0807030c031b0201080c0f0f0f091203041a0f0c01050c0d0605 63
    0x611b0112001083c00440d078580b6607c01504010030785260004045401c8502c5e491940c00c00ea6400700303160310380c0002c08040c00141c5503131907201074410a0410510000403015180240c00c20080080c0040400c050603242c2d4408644064485e0300d0800054900b05400c20341464040750034192569420b00f00a01010304002900078100c4100391060802c080c69502c2c0c2803078101e8144d8003100e110048041080b275903401000030b010802c01101d80703224154412801c0000c24201c0b2760008440b400e0455501140d035030032061180c1100c1072414440707541c0401240584818a182100070310090010520406060788042c184180b50b10980342d01c1d1003421064031510011030600802400109410f00080e10800d204003d08080642c1540d898106100c103031000c41d00750880c8901520080b004120315140c1e141c02c115401c02050490059894a0304081201826500e108401045810000f0b411110b61300b80340c0072176040c2c540b0000200b10906040c504150154041102c01440a0905201040a140000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 947622014 1250 947620764 947620789
    0xc0409052a01170f061c1209080c0a1d0c07060f0903030b061e09030c0414040b0610020709022a060609100503060a050709030f050d090e01050904060e0f0703060605030c 74
    0x380c40260b035a258004c200d45512252080c2d8040c205503460500010300e8143d4141c8458580c2d00c88c2035806042c00c2e5050b24181e401201e0310303c600000fa00402c0740c5c000407a94100000207640e108801603480054512291003001b6004000d81c0c5010b00003030510145a011041080c1710350f609102c0c80c0100340401c03d01d8000c0142d141e01c54003025948a80340070001c00184907040e0045c080d209143d0709a4000b03021102c07010020410207500c0c1041204115178443e419620000845200015404400000750360b20447d00032000401da000038005402e84042c114040608078014810b201180808031050f12410280e4401f4001c81161022442e07074154184204165a13000d0002c1a1030360341d13521000b01070000513000c101480000d51000c17001c034102c030114048e0540914000d007140001e104004100e901c85900841e1081440001400960b481e00c1c20140c0081d000400824510007030072155040c694001c0d000394540c0f003140070000c10403100e42c00c0681200c2048090b943c400c0c4000060040105144 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 947623264 1250 947622014 947622031
    0x6080603031603020c2d060c031b030405040f0e0d050f092202030403091701052205010e030c0d02010f1413080903010501060e100c03020c0409052a0117 67
    0x2405922466085108110300d80c034024811640d003641d940c40410680291900040c4040b07a000c0031b2139160911411000c50f40803015141e1a03d070400840b425600c90295010340a4a0b0440f20203001030b00310700b0070564002c0c14004204001030012903407948014102120b0b901c4590058141e00c8003604d014a05403600114000f4203035150007059802c10200c0415075440b01c48100003c041c2007030012043c400343d4491486900c800c54001d06103040c0c0d007a642c2000000442e180e040100700701012062030110500c055001c0b103c50003528117890038501401140d44008030302d200204003124150000280c465103a2881d8008110b56031410040d1000c0c3c5002464040102c09007a010500c85004031440d04440d50258029900b0700d5a01000a800d50707200781e10440c00078507041c520000310303e0800300781d421491041c01c01110741241e075503002e5110f04d0740700049841141d0700c02e02c040600100740314180748400d404034245103040c850005070340004420b0a030180001d05202d4411201a0280112801102d54 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 947624514 1250 947623264 947623267
    0x60f04030f0f02030c0a031809020304240207060f0501050a090603120503061912020117070804200a08030d14191104090212061f210605030a050d0305010608060303 72
    0x20034282c2e036058054141100714402001907801d585001d20100d004184241e450741d4000d80c408161880b00422a001031000910400a000001c0d000c5030300504114055606424524442000080207004a80c8003400e00b60170000d40c41c1d0340e5603a96005a0503110115240704031951030301620011030b400e038040248802801d40180c402c280c040c501459120100600c510600705180050504105150380800d04852016039407100310741e00006070102d0960601d20138480f82c601150001c09208010f0070181c4488030729500c2031b43c019482c000c5441c80c035101031300314552103644d88a100c1d62030348042c44200130a0720781001400400c034020f10aa00401c2e6807200500441c440815100080440c1420159407910421001070030643c0c0b8000740c05a4030b002c1916000601c1c10f001803000318411020f15105c0425a0005000c01c80e4105d41c641e840e4440e00745c0c1c901642116611000020136858100c1903051049030504c408100b000240b2910040d40d640c9c06004d2640e88100c20f40d100002569000c3d4503800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 947625764 1250 947624514 947624537
    0x2041a0d06150b0a111e0c0d14030403080c0f01090f0b07022a0102010c050c10050907051507030e030601050f090a1b090623030c0a03090b0a050405060f0403 69
    0x10758102241c5a5600084110400c0d07843e104900298080304082010550305d03441071840740814031032000302d141c0705001181000703200088280c0740d000c0c62451620604011505009009401c400852a0243c00080700d9550751281040050b6801c0080b54801d41c0c450681c0c0780358600b4041c021500004d50041c0356030303640001640c43d60304038000100180214460b56035404910001940002800d02d044411401c064001c00002403d4030ad0300740764803041c050704102418800400003103030b680441c900080041d40d901c3d0380750646d0404110354003059101501d622051660022400100703c1140b04e80c480c01c2e4096241010300d500ca117000d1164651050700e0804e8801c0b0390620542d0310ba400694042c0008090314085401c1c10a10742c4942a07000040718038405000c1e454200c4040109005039194440862203d00e034680c110b0300c40289903410820001c150f40164078065002a410300b03601082060381c0c0c1c40c22a07118002403c04440c01e507010312490000c01ca00220040100707006582540c1c84440c12407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 947627014 1250 947625764 947625773
    0x105270303041e2408090c0307091d01060f0b0d02040b12100918030e040e0f1c030209030613030210020403031707031847010605031302010305130b0a0902041a0d 71
    0x11001b46604c1513805200c40c0c1c07800079a02840010f01a1108660004848000c69001d205207013030b0302d41060580c0e01d407100511a00310081c400000f200c2c205a01c5560b0b80040c5113050b00039000e00c1c1e01c20342c030f10700c070120796210714501d00ca100d2842418902140c124956642e804041610102d0f0311400041c3c42c90b0441c1c1d00071a1042e1040d11001c94090000b0403038101d40d20f03080c0d00c0c0c4442030510400540010030039420103110003034201250300c0740f8035041d8202074240700003c1e103444015002c55036a445500d424401c0600031f200c440342582c020034045460707a54034140a80f1900481c10310040402c1a1000203500d10f01911480044130300d8458181844040c1c0d40d9101d84e600c0241014881150740910101c0124683c070661003000140244030f60480c507890354a201c03040506030810428807000b0b00400c2100b03040e10f142e852409409203000314003521b440450088042c4444406000800104200070042c1515080760041901c2a9010408011118140c07200000c0b2032420a40c00b8103045088000709 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 947628264 1250 947627014 947627027
    0x60e060d061e0501020d0c0b0c03060a0e07030218010503010b03040f0206130303020c090f0601080c0a030b1f021b0105091e09040b100e060105270303041e24 69
    0x4105400c00000e80c5910744441603422000c0d510302c01c45050b0807140600c09940e0511100804407540d08011411a00d1680e504070121001030502407800b201100294450307445400d400010000c4104001d104c0c00c00590060280d803040c01c01e40c0e18500103002908843d4828011641240d11814150303045441d1581c442040340041034041c1d81c854014001c150040704084150700096200c0c0d0001c3c80303a500d1107070a028508800802844090381100100312144c0d8000c5091588800700d060042da6840035900158003e00c4040e0400d0f800c1002c1d003400c200c04012402da00c41110392aa000c80d820709803d1104c6242501c5e00d01e8a02c0d00080c000d00c0145100d06019610703128a4190764000d500c41c080c04404a040d400c411a01078600300980404d004004c200410040081c0800f03e445900c0c1d844c101c00042d00d21f215845e01d100594024a900c0d030740c07104000005a4180200505683d9105e56510207503e50b641c6045c044403a46864032400134060000726440122028101e03555603070b044007028103030f458 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 947629514 1250 947628264 947628277
    0xe0c120403030b0a0f0512010204060f18090c080106020f0d090603020702030c06030708010e010f050f010e1c0b1603050114010503090a1505041a04260f030c0901030510060e06 77
    0x40c03684071858441943c0d1559212005031503440c5c284d4050034a41000c010b0041d060005030020703a413040105002c0141d1050007442d01c1003050030881c004600005418580070400e60148013078629008181c81d4a070b0340700000c24104ca46903803c480d400340401001030740b528010214803000c503102403020000700d40241c014102050000b420703241146400b0b400304080d80e20450307c840000e1404030051005414204100c1d016100301d18441550074108008036101c0e055045030b95050056515000c00c542d034035019029400c40300300040c000000010b00d4195800700301520141100300b1031081004a942c403a01c0f03802c1c100c030008003450103840ca110006440c00d070b1000d84012500d00540c2c8418011500e0240a040001c020400000d020720b05400e024049000b12101c075103c0d9050101400f004c84c7e9030500d101d1818008012903a110100101198207034400c03c034800030004004000c0001108141c0060080d084003030300d0600690307460710b07142000c0c00014004c410104100c05104034081c1000c1015255 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 947630764 1250 947629514 947629517
    0x403060906021b0c0901051903050102030f1602060103122001020c01090605060d110d03020f160603050a0504210e12030c0c12031215041107020120150a0b1906090e0c120403 76
    0x800d2510ad8454a09a0340225005428001c40605004910807041c440c0b6200c58012f2000c0c0c0700b40d506540d01c40d965050300c00640b408110385524142c03001e0348061904d02014190344000c542c0d442240e40d05e00e000c0d0a100e03000351503070392521000a900d13050000380300703180300c0d0310290310070340300340c01204001e400c04200038103600714070680c81d46000200c400c20203100c03090005588010850b10340900181a940000c1c40c1c4421f40e270405c418800080d43d241a000d80c204120310550301d09050000e003c40d801d89005141c664800140440c04003903860100040041d0b540000c01e60305149060710a20105080400061079103030700420143c1c10100000200035009100d031009007200302d080c400010300b41e4020b1070040e804410b0014400d403c642e0414001103280400c60f400342000301c07401403040d0b11f0302584514040c007088180e0000b0b4042c80c155000422440009050b0f401030b01c0d01da910450064158012040440c4003164041601c49010000502c504408100c0c1da02e0500041d1542d405100040c00490 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 947632014 1250 947630764 947630809
    0x80a06030c060c0b070f0f030b0d08130503102c12040303091401210b010513030b0f0c27120615030c0103060311040902060403060906021b0c090105 65
    0x10001d0101800c1a00400ca25030394614140c50a0526008428001d4504000e000d40c908280308401c1e040405264171080d54200041c980284901091618143c002d00500c0e65000082c6521301c09420f03e5000140ca9040d412141d607845410300920458040c40e125002210760b2024050785100c0b020384003140986050103682d00c01c2084030000c2025000741d04101d002c90080007040c000700d000480c28580c850800d01c0e201900c00400140880c0410403204040744c8980c0710102072485074040c0c0b00700c680c0182c1d8031500c81c20703480e33481c103080142074001d403182140e80e80080041021140400c05440c42e00003c6400010345c0a4400070100d01a00481c1c5280e0308260991103914010b5418044144540d490170802d003540c0c81400209410a200000520f05041c07a102040c40032840c40c801041d4840c200340d07070000b034800345130000032041d00966100402d03541c01c00403480100000303500607040c2034808031086102c002c54250f020351565060300c0203940090009004004901d00b4401d164940c0b242c00c2c1500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 947633264 1250 947632014 947632019
    0x18031203040f0210020c010e010809010222170a08040b030417070b0103030f0f020601090231051e1012020c0a0b01050a0605030106080f04031e231306080a06 69
    0x40868004603800d81d400010400001c00707504101c000300401da1000c1c80a0006d030840c040000c1c04101c4c0d804401070402661000207480424254110b41d42c111403000204c220414070f03520038185a4690055405031100e0074030103a0318500018050204a912140160504d03040c801c0016064000a10076110035003000c5054001c180740d04020300b4134038000c80b031016403903040d410003030001d41141462a040041c0e00b21a81c2d0425404580207056030344108001d81d0301e0b282c820072035a80307030121940d880c09882118044117250000c441d4403004c0718803d43d00b021200f0303101c17000c510b401d071600314007950000115181c00c0d201c140b068030003034440c2c4100440141000224840b0502d030800c2500300b01c030058030210040c4446d1500c0c003d20402420b962420510310b605090b001840b84d500581051841c2808070f02045c1054015040c0c0b40d460b101c0c4050b280f08500c2140310060100c0354002c3e441401250481c4130000750603a45040701c03499641072043c54503031450003108441e4804010940d0503010342d81d4102 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 947634514 1250 947633264 947633293
    0xb1c0f0f06140307060f172a0d060509010302060904092a050414092d16170106080d0f03140c041d1015181707080c061803 54
    0x1480060b10110740448072009811051501e4122241c02180c01d00c076501c80100042c6a0202144070307101d8001d4946c0d48242c60b032a4003140303810001000e200030103100c2c042c10180d51220402800c40012040014050385079260103010b2101c4081c00f010f9000b982c104004030702800e0a410540c000c48c8035640490840f00001c03010400005808590041308000d540208a68a010300402d8400400d1844550a0b82003444000741e440c12500c54a40328409000012039403261152065400f2603071003400d440800f0300c160050110510607000f050b840b0fa09050300d1410038001442640180c85402000700302c2c204039611300744d03501031031902c3e80300c20551104503403034110503020080340c0910034031103c194032981404a00303202d00e94a520740c100d40490210810a01c62001350002080760b0203100b060b4500c500501c41103445454150850342d0702a030155000440140541001030181182401d5a0100e03446455060301c80c4001d0340c0155204609008034a0000741d28900900c00010040803280c0a8984840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 947635764 1250 947634514 947634521
    0xc080f0c0a0522090f11031003110a1505030a06080c0d08340317040f032a2d03050f0a05070f05011401140d0308150307080f070b1c0f0f 60
    0x1211342c13507607120010804281600d001d021900c00010041c40d00310b1811101c80000001d1030301c4007800520840030138040c5515842ea0442c05071043d4080c1c0c9200000f40300c0d016044e0740c02034806c04071036031500e4070000d00324001140d0001d03504402864000d81c8100d58640391401d411141c07042c0d0b41490660317014801c003c100c0180303100803400300d121900752428600340500300400d02c0507a98104034060082100081000001c0410030307501d1b00341442c06403880c01030403140c1d10b44d001c10304c4203803c00790350108240805010601d0905542484c254420418010547c07119404000003c01003103092010000720001400a0486107e0b64074000d420810591944032040180c8002964940d5513520340002d400d001d840994058102c01c0016101c0441e1000030494649502e88050104031400e00410750b500b40700d000028501d04005c0846243e20b440d4801d07544c40746139040d83c9800c14480c42d040042c603c5081c800781c852200c0412980158040354060900180c0010384550702c550303a80d0b1031402e4640c0c42034030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 947637014 1250 947635764 947635769
    0x3050d081f0915060f050a26090606031c0507030309050a06050c0325050901030507030f0c110115080c12101b1803020f040e07050d060c080f0c0a0522 66
    0x1400071400050340f46030a01200c030680c00c03003130410014112108a2940140840c0c0d50041c01d440d04100d80584890301d0a110016030206540034202e030414804212000a1458010f01c0c0c1102510702c51010301115201401f80b00799401c0210ba01808083c021074000d620843d044c0d4060703400d4520418080e0b5800c1d04940381110201039000c0c0101c1480100742e100d000d0000b00101400e407944950240340000382c480d004200100d8105a203036000180e85900c2500180c8400b4203094003404000309840003e007140f8030303a0074204255860900154215008440340904a034001c50140041c0c440580030b101d20409560754a404a1117520020f0b052016188031f024200407400100c42c5512942000060000e6841e414030710f40105015002d10269541c003d078404000801c6400050484076100002d00b0007030a030f8070a507403080100d09040300380030f03858201203001c400507690031103903550b501a1904205000d4910942c02c98051001c1c5443c86c1c001c40c018800705070103800c8010b4428080d014100951403c1c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 947638264 1250 947637014 947637029
    0x100e0909030a09060c032f0a030306060e0906060d0c050f03010e0f06220e010b090412110a0c05060f07061e20190e1008010302090a020403050d081f 65
    0x90807a1690743c1c404060f2000d0b141c6440c00404461480d1002865500c01c030200341d0040c1c0000c0107100b0303040890b281c28415500e001e81a42d0080c00b450901400134040340c4584004102c0032500b4008a2901003942e80c4107490040205003840a000002002080c1c5401683e05110040107032066200318400a10b0080c0300c9080c1103515072525401c140c04000b030240078180105d1403e4000c00b120114140d420f10b000400007400280718070b118120744d0140c034119901d50b412a40703072010302050140c1c078900002e45c96815100c0c400703905442c880040d2b0716003039808003034188140e0140920003442c0c998014030000d109491024180980ca480724030448a10520007201149103008128a540d62800b0b64803241c1d400b568a07005180e4240c0007131303e09206131803240750105421103842c1178031405440c0103805088068446135609071034800140c010042800309030b20032854840080c01400c0d031802141d00740e0b80c0c020050a1464143e140581d12001c000e0204231000c2d041c031990f1007101c4140032002c8020b0845 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 947639514 1250 947638264 947638267
    0x7170d09060b040c08150604050a0801020409050903040e041502130e090d1e050c011d0d0219030c03051317011509060303081803040902031006030f09030806100e090903 74
    0x35140030360803034544001550165050913241c103411508030841c940d101c080280c01304410101100001c0c4984215040140e2005818001141d4180c0550182c01130b600c1507802000a03480b610540d81d80c9010300c0c440c0c80440351a40c4002000a185032079107820b03108210707c0c098209406043c24002148050b04001c01e80c6a01d2801c02c84490000c1018450390741031400c086103c40105220503c0300311444030048180000010014a025030075070080209014010001c80c000000d042c2040d00d414158004000520400045064100344190f5407000154036446403114000365641c141d984d5000f0264081c1d0407041c1540000314150310b102c2c6152908079034800040c0304c0c941e010f142100d030a09a0480c1442500d0864140002500400b443e0380010401000705440014001140d1840c41355400c003010003070000c01842140202d00c8242e80c1aa1096101031100411100300d490803030781c169078050000350140010411504040c1c044044a0b611440c050095000c49400300302450010388103101ca92b0300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 947640764 1250 947639514 947639531
    0x3181206091203050603100c0c0203030304142b0e060c0703030f0314060307050402070f21080108010c02070b0a020304090501030c08070e0910020a0e03060403080106030b061c0207170d 81
    0x81d114000c00d41c0c19030f0804020318106040803a507210a500c06504900382d65114001b441801011020010b550003400c681d40d920b4940b4011000510512390058544504014a204c103643e04245440c1000d00421401d441107202e03000703d40d920f040000d2690010000c000c2030781c03040070030f20091010354040d880d00140d04110000c01401c60704801400081781c0e0848090241c80d58010692801300c4100700c4016031141134604110000220b2204001c1c04013444d0f03190000110b04030340c5881c5641c00303241c0f180d0740b43c2ea076508415403e0710394107082c500058110806c1800004131105c060f01503440b1a1040f68202502ca103003807412100c0a03041903409008100c0704000400341041018042c04500110002c941002c1a4459541c14070440c150071300c41e0082a00d000003841502f010309000002412640c00c1d09290501400340c41003070240c140043e0408030600d4845c00d28004503030040354407074001c00e079460030104684000d410020003122504808030401e94a1f100000c046c03c00f01590800c00600401d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 947642014 1250 947640764 947640773
    0x601030c0c0b0403021f02070c1202010e03030a0309111219080d0c111204061b11040c11151b0309070503070f2421140c0408120f070318120609 63
    0x10384482d03980d00c1b014010010040081c8244003444110b9882042c0b0103005142440161040c0c25142c1a07a50980300100d103218440f94035401c410311150040480e0030b40c200c40b000038015811007010407442c4940c002494007908544101070104131a000da100a41844599155102034400d043d41d81d10028640d2190814022410301011200c8890002940d1401c4c3c81d161024118012242801d040d070748200000d003003031025688903100e601c3c0005100304407010100e28007411000001d20b86544502c01c0c01111480e00d421403118500503082810a41207041d6551100724840e8001083c3d12014051940300041640302084054090400042d48122090425074802181a1122031900701104444030740d11540d038224564601d00b5024601089042e896041140040d00d0028401c201403442281002103000070700010308107a50f000c20070b4a440340b8581200f00e4503070007400c0c1e1003008407400f0004140000c2c044e1210750b000000f003003020050303517544500e080c1000c81381c00310079035008d901d5110352003c02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 947643264 1250 947642014 947642053
    0x108060f120f070e0115080403020f1002030403030f0618150305061806090706080703020705160e100b0f0d180813030308010909030f030b030a0803090709230601030c0c0b040302 78
    0x410034000d803070904d9803404a21160708540780300500240f11081020406040c8203108801024850b20102c1c2e01c4481200400c00c02940205c40c140d001070b203403010007841c22040740118000c6070040000900d03c0d01e0056440001000308051901061100c5140080014402d0011038411401128030172410400125807905001000781500b015170400d940a000c03182d000b01403a600000703a0b1800589501040c81c0c01803500042148003044484010000a612400c24001c40d1141c9001c20907a40c0051b90b403034410009008099000c1d030203500611030940000f420341c2c810580e4400030340d510440039031192507112080d0320000c80042d564100060510070b05410150a41c010100c001c000c014005003174a0040840740718040c01d90400d5110030040c5501e540410894504640294503d681c07428904030151303580885202d4005403905104802e1140000701d84514048070840c04221416900c1d140110b004009071010311060011039164003010070961210548078034403039001840020024004019030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 947644514 1250 947643264 947643269
    0x5010507080906070e060d050f04060b1512060f0d050f1b1309030509030712021c030815031c0c020a0819141905030d2304020108060f120f07 62
    0x6005160341800b5041100184940d484403092401001000007280010781603c19920441c2d42c050822061200c0c0311242c40101d800b40d0b11401c0200a0149030f0403d000500d0300408001d081c600090054107204401c0c1080c0950001008080340316007040d1800103425082c26030401e95903540300101000d403485042183c17000c03840c0702c901d40d0f999141e0100d0001e0404000140c0038405241c0340d80203d000c00d40141e055884228004003910450354440c1d001c82250f0001d0321069205284109581040c603a5101525480c5070701581d40524540e508102031010790394025901e03405129408686224205c0503201103420091669881044116401000502c48450300401c0483e0821080400000c40780300180e1485944801251110018504501c0c1404031030758800c0c0c11100144605401c200780400141680d40300700384108425921100e4000350502c120403100f00d00b001b9180031401640c010800254048401030498071003140c50000301e40c52100039500b1800b0380d44000405032601e0418041d8401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 947645764 1250 947644514 947644517
    0x905070801110d180f020d020103140c090109090e070605070f08120f071409131805010e1c0f03091b0308040f0501020c060304030c0c080102120105011e021b0d0b090a05010507 77
    0x4e040040d803600f02d2840c5020318000c4c820510075400c3c4007164000d800a814800e500064000315280201100722141e110981c1c0301d000410402021801e81c0c5903216485020018034000c0c02c10a04004c420350381548040402d441c40401203040500040801004202c101c10351807041500c0d003401442c000303a0710303030290156090012040821a002d801072090b2580035204a6070784840000c01c848101c000c007000301c1c5407182050b0a140c00d500384503054105030307128031044040b504054110007a501510407000d0748600003c1010500d0203c0c642b00c3e8000001860103605111161091a103903007403500050b0703004840c1d20001280400020106044090042400307001a207180c204081c0002c61a2000420013414005203801945c140040b1224060151050b2002195966081244403405103006d00c1400d00080d1000b02c00d422210040005039080c0b00e0b0b940050143c0c0104910308200c802035941016000350f91151a1400b180c019200d130703801609858050400c00e0800e0900e5800d59000404510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 947647014 1250 947645764 947645801
    0x81e0c121501030c0c02221805010203040209010e040c060f0e030a060c0e010f090b03150d0c05031204080a1103100f050604051003080d0c020312041415010f05040905070801110d 78
    0x1005a21100c07001c5503000c241c601e519a41917201c51501c4022300f0000d1441c0608400c1006204c20484154003c0d4043c900898045089a036100c47d40d81d0043e40c1250300078140140c0350000c00a85009e0200301c001d6011605210380c00000700c001080c40e1074100b41090b12101c2d180c6209005240d08050760b154203807000c1c41d0001d40d0b810f0700301c8080e0644005e4400d0a180080000010705400c0c1a51429010104c00070600fa440c89100e041c100d10092041c05058401d01420b0507051100f040300701201c5c01c545160700078001594003034444d01c40300540021120740601407a802c103181c9503aa823141c01214000c500e00060035080c01da0522080304e00040c4211a5410030a10a00c08242c0300801e8408414161001141404000718202e045000d84001c000104a6840501003007014039000480028960f43c11180307081051585100c10003402e202d12030044096580910a50174503070803110308280208111851f050b9030303495131402c48041403a070181501d030218210200030303c14060a44207840641c14030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 947648264 1250 947647014 947647037
    0x80a020f040302061b120d06090207031707030902100909050603071a0a02190c060806040b09011502070803071209080a0c0506090409051615081e0c121501030c 70
    0x500c8a214070700002c1c1c403407003001c01c080000050408440750028040000c0d9181380048811400c841e810110600c200c1c181480707000315441c1d607140700761a401ca401d42d44400507641d55201e0703041c640c0030240084040586980017000582ca58841d4125a05c0555845100c0c95240182039812941c0c080d100c58842c4c0c004134401c02036422031164100d03211103010112903845900440a0b03203400580f0420316100a4100004c02c2404030b0008810119800d079119101030766681c2c420041118410228140d100b441c080042c000b4140c00601030011440341d004840070540c032280b01510b150000e580484d03603da0703821000c81d1869440344446000300024402003260442c190340740c101e403034494000c96000303103408590b20440d0360b5142c0049030350b5038100003501d024044051180f1a400c10724050507450030201080340318002c0c442e541540c4909544c01000000c4c0410f607810901c04040a4400c0c1c08000e001c0c01030724000c1c8403c80c4401c0c02501c05000c4000c84800000c000340aa070b0303051a08078240011708011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 947649514 1250 947648264 947648287
    0x20d0501240c08070b07020f060c04090c03180b070201020702180718080a03050306010c2901050d050304050f01030e030a090f091e1515021612080d0209011b050d080a02 74
    0x9607140713a90b00580c03001e03040d40c8542040703141c00100104080780c0d2081c0021b001c0303001d0480d40144151801000103001c04041a01c1c00d0b015035038030302045943c824a24100c8004100000741c501d030014020b00c005440c0050640024119080d0442c031030080d0380030142800780342504084860f1072824409040e08200349000131054071110031b80c42c0501844400030000c0c05036803290070120141e960007110403a6003401e609013a0b01c043c030354403010040e5040842c0041590310b000d0404070001b0b94400011490300f400d1400f40240d001391515218107041c0c0700d0a018203054014405000031000c1039940d401c40d649091034903091181258062002c0528040e00c02195400a00b0b820469083e0a40007003060181d90401100740c084960042c0000b6a40d0501200480c2c0d001c140100300d1625a840060b030715031102000b02500c031a01c80c0041c881781040020503d0703180b094000e003180f5807050608513a68140301065000000300414203c80316081000c03141c07055034000c44a6074100e8880001181403000f503268 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 947650764 1250 947649514 947649517
    0x1060c031b060b0a06020a030206060105161e14030a0305010902090a0e13150b01120204150c0c0305060709060305070e0901120c0b0a0804260a050904020d0501240c08 73
    0x84580c80e5219601160701400015045241000f00c094414012603682d1000207480e4900070034128014021300b004201203600c2101070752072a0740b01c010585000421507540340301700b003450588030644078a81e24030480880d1005100800340d41c82c1c01c0166070340b101c0c200d4005007203450503088282000e01c14008071507030b03444285040c0e003910745022000b8002e45030407501da0144081590014403480c0742204a0910300d103e0307040302404410a0700e402e95413640441010060f40901e0290906005031030813030f440c03946d208001c04030340e81d4000c0101d840540e407681c0340c039030130032404540c51408100c200b541040295031500c140740d0700c001c1038949102e2401d000c00000c0c0034410180300d0040d090f030400e03a8400500c071070315015400425007400455a01c00c041c200c0a410300408079400d55640312450408014801c040c0651104411050b07649450600c407040b09071303415000024842c4e00171342d09002e001040d442d01c1c4a0035010304800380041c900c441c1d40d48420321210350340100c58070800101242c010300040c0c00c0c50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 947652014 1250 947650764 947650787
    0xf11040e070305010623090d1121030d0b1207090203010f090509060115020309190510021b130e0a05010906050c040503030f0309161205060c1804090204020c100b0901060c03 76
    0x100915145d0058a4801164010700c00b007036a2040c21015034404000762441c05404078542561524242034503e1071011908501c0c10ac052603940041040d0222010594489011100020055400b900e0340e07100151400302e0a8200c1900c2c10750010040c451800c42c025041d0080080b040d041c4564079003880000c1d201e00040c0306a030407000489a05032100341c02403054452010f4041c048040d0000725101541e5145c22520846000d54081d101480000d0b101240b140031001c030b40c0804102c0d5051030001d100183c04e4280341c11090075038511011a005005014035020140074400202d015003c0f81032082c21078002921640c1195405c00041029880c040242d03154220740540703e6403280c0d12000b410382881401d091000080c4603030007011507007a000101c00c94009024404603241c0307960303030502000e081c410010f01c0035171903000c107141000328a082e801c98440d09102400140c01c00c0750794988507103001145c452030300f142c41c0c840418051600300840a240101081d203080701c0d2030400f640380500b41d2030945 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 947653264 1250 947652014 947652047
    0x21070311012301030b060111070e0702030409020403060509011104060c020402030606040b0307021e0c092a0309010e0c04020307050301120c08120702010f03050108120a02010f11040e0703050106 85
    0xc1060900c520300c29400142d00000d0789803000511401d030a40e5041c0e4100c01d000c01c58868200c200401c201c0e510440000a02240c07600083c406141004000c0010250091919045100411020406100c2070000e4401107200b00c00200319410012440381c00d5880440110b4076006041c8410031241d039001004200640c0c060700c0040e036070345480001c01c91500c20340d04149075805001080c0040c10703a0015031881c44181920310b034003060111a001c1610b4113100125598060300601c0800d6010520640221300d482c41150051450600c505c2400455041280d030518035035990700440381c501c1300a114100c65094101c50440c40c510b401180581580018001e0b14200c0817400c00c001c08214a10503564058130241d0200c0d0440b02d48801170111680c80340c0700403800070340d07594100000b0a0090082a06070b41c810005000c034081204c0d2001b049801140280c021907489210005000031948184005616544000c0b9a07441c1032600002c60554041c10000c205840c150042020036403264268580030b44a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 947654514 1250 947653264 947653277
    0xa241412060c0c01020c160f060801080c040b01050c2a0108160f0c05070801091e1703090307140705040e060f04020105090a1e0801110c03070b0a060b030708010305210703 75
    0x80f500900900948540c003102c2e200300e54480c0000402000305400b154501000801d9060701d035541214400028421402a603008414034200c504c0c26800c00001d001c03040c034206080c0103020160a2609140c140518650202800790060f507a20380e40e1101d88050080c03c1150440c00c00d51000119081107040c070b030040080c002b0300341018a110750204264280c0020403212003540b142205402401140c03001c6500c0d028000741d01c41281400010740b1003460f000300e2902001c1c1e01030070315542242d10082c840043d901041004100242140b050802c00401c3c1d00000c26410381000280012900015914613080d0300040402500c4451190026031255081c6032080d10f84c0e0399a00402d91109054101c0c0b0b10319400d507003003921200499040c801c1102c0604000b0312800d0640d800303c2003135200d00a00341099400400ca00c00104106420706600110481f84c00201644c0c1d5040c40e0609403c19906134001400c49030041060102c01c1002c580007040090980a524442d82c10500e47d80c4160f0b030005092020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 947655764 1250 947654514 947654527
    0x60e090a09050c03070b1c0c0509010c061e0207111c030507170a03050703110a050d0e070902031f1a0301060f02011b0e040e01051308030a241412060c 66
    0x10501401c4645200070f0100c85c480c0d91102284e907516001a2054640c09580014895990b00e65009000301c002e01c644481c4c3ca0090428011104411020030a86140d07889140360340782c820701098104220b980c0e03504016100c009038038240480100004145200d000702d90500e001624101c0c10b440b62455160030020b9403025145080d015900c01908440709650300411408040368050b04441c0c461481581c08001e00815460001e10074041c040342c98002940511003070713107a10ba059001c180c981c100d40c0200c801960f9100c0c1d080c010390740104c4000080d91610000e4185040004803104041e09000e880070103a4485032544892074001440782d9002c01181d4000c100e0090700179170202d4100c403a5080b86191000b00f11101400002e503c110103070140303160403c541d042c08010322605e4090040800340b0f0001945949039262107400240c5280c0c046a518005a101071a00700326400c00c60314001d554241e941d20f00202e880c000d0b03041034003550141110800c000201400030903081c1c0e200340030160f00c913120340 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 947657014 1250 947655764 947655773
    0x7110a0204050103060e160326074106070302031306051f06050f0a0e01020709020304030905040c08090a080a03090f050115060219021e04021b07060e090a09 69
    0x19054680650400e00d420300100c01d00c841d13504182c04010084041f641040c2805052603001c00a5100140450001d10341e1140d1b039148440c7d030200944030003100c2c24181041c41d2144014030398060000f02e4003030000a051109041c100002000040700402e030b03100d60a20390214261074034002458542010b0340000041c6103070f520828040d590315040321040105191044499030586012035690070100c040d0302e0005031303d611650440d070001d91404007081c01c01002c800240c5414002240190640c000c00d2008130304980c1510146101c2c030b000381e4626600601e03100038807003250941e0480c1e40400c0304100c104103410500040300c0140f150710041584c0d41c0e03001c4c1c6030200e0007031060400041405a49108050130f000341500081003a1520300701001015684030301c160380c0c580c0c0300604d5001c07180302c0c2e000da4005072900c0c58a40c0314032050007909010181c580c0d000642280e01c40321103044408101ca005040e42c0347c04204007070150020342025600e071a41000041c0c5041300040008001c0b03512040f03142c0801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 947658264 1250 947657014 947657023
    0x8030d0902060c100b041109010e2e03020301090c05070f030c11150309011b140a0e0a0621150b0705070305161502030a1727010c17060303030711 64
    0xd410803001e071690000c6031030813440544080c0c00280e1140f400c000941001e50700d100c0c1203d9007240141c503030701300070030000c4d05000d58143c41c141d0312072542c0701308048240d8011084282a010040643d401aa42c0d810100c20800300d442d0120f00e12b08200e018062003002418050f1100402901414088404035040ca0b041d09004d1030100c290340c01820703489080070620795030b10256000d214200001e0281c00c03000c9241101c000403032004117000800d031980c41d140ca9070108004202c141d141785000c6035080e0303000c408180400d80c07942c008070000307840610510300810650303d40f1601f03074a005001d0201d55104460040c800740320b400f0307c4e1000400005d0341810000c3c10081a00210b6200d8103682c032003108200440b0327221322240702d5900802d40304850f442c1802c0c40482248c507104056152407014402c840d00e4101100d20080c40e642c100400c04d4101c1c0ca6000e00300030103080041007140041220003402c64010300441c1e0b4400c2c040051208102403058964010003600d030300c10307030130702d840c0c010294178010862a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 947659514 1250 947658264 947658277
    0x310b2a010e01060f1205031909030b0c09121b011d0414041203020a0807030e0a02120f1603020a030b190e0303010e060108150411120a020406110708030d090206 70
    0x25840e00002948001e010342042d0b0803109441e410780d0f80150340300300006a000c10488000d080350010010714030002640201c802203440546040407540343c40756501801860140c96000561001060382b01d4542740591003014050fa426024248040454290007550000c9080b151f050028440d410031000d9a044090405904010010700800b555a1150442c044081d00c0035540c9034440c04201d40c0c0700303009008070740d501685690341d4a4595180b1a0031002000b10345068006130160400090140c0d441095500c0316002e020080d0008080315003c3d245000d00303440701141c4459581501f0005684e45036201c400f1280c1041c81450650740307942190741c5c014036207000c0541e540d1528090b19803c40700000511b043c0c0701c9d041a0600075494000065030500740860302e09090010f266040c0f546070400360003851095084403205410445550007091105408468a1008a0303001c50204a026800060600360b4407000c405000388608100038161039110391350404070410b0300d0f54800402c46d100c04049916 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 947660764 1250 947659514 947659597
    0x7020d090e06010c171b0d020615040b120c1c021807110a050a050c0108060d022101020a02250e01091e1406010f0e031b030a08310b 58
    0xc40203560701510941080c00200110b1460106070141c040b40068020100c7c420b580040005690318420801485484409a500540c40e66042d4500d52101c080c107000e2126042c0242084080040c00d02140f104a100c40b40c01e8a100181100d026848144a0944c9621648408040d43d501d4050554000702c0c4044007140c2441914540c01c2880000b01d80ca5240c2d601c03c806039408010f642c0c0044404541c1541c4084c0c1c4140000002070062500c0c094041c1400000881c0140c0c10100001084c22078001c0c0c0420300141c0c0bc03000341d02000c080049003060508084196850140d4100105114024014002c25101030780d21800503041c2c1080b0325159245c40f040d00c006010110000c44003c8a5000c20b50341d080c085000d41281ca180c00e40100360076440008060b009181403062102415031400655402541501030b540d400340124041000401c4c403440c844105921f0382d9440e10000481017007901c0250740383d2441500034084400090b00f1a01c0d40300e040e811413880c040c1079140101000250031400d20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 947661870 1106 947660764 947660783
    0x1f120501050a14032d010608060919060b06070606150306031709040f0f0506030f16261b0123220b070c0e07020d090e06010c 55
    0x61002c3c50041c2250300001e0103031181d20340d02c0b010440c0c3c01d480400c2c0e80e491445c4040c0901440c00180070400081150f446c0982c803807902e48864035020b00464800c130803c40140040c50300060000701d001050f242e6144814901140281014840e07264040d01c2600d032200913500038843c0000b2650400421101207002070101c0303009078442c1d1801c0d0b600542e00e07032505100302c10500c20382c1c1c0c1c1316600c45400075071820108201440c01d40c0c080e05a44e0b4035848107003400b2101c108122076a080f1028002124140340c403801e008060110b80e24021507071031044045100e12140c5050340b010080d2400e0300c03000b078640c00380c10b10ba8030026405601840c508030200b00308035140c520020304c000404c45002d400003641b521449000c171180d005d2034007519103d234100014091962425a200e40290300c0c0c0c0010701040c60400c0003d007280c8200e12908103524601c23000224641d001c0c111000710254005000b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 947482014 947661870 := by
  have h0 := BRFrame.cov_init 947482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 947482014 ≤ n) (h2 : n < 947661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
