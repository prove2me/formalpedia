-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2181
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:54:14.295672+00:00
-- url     : https://prove2.me/submissions/5d501bae-3b3d-4356-845b-bccd952aad6a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 392086330 ≤ n < 392266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 392087580 1250 392086330 392086333
    0x1050906070f02070e0a02270f1504050411030402120307030c0b040201050c060a1409030405011b08040f060507060b010903050a14101e0b03060f04140309120606030c0f03 75
    0x10000d5004241c0c2c1007000c0030900c101c4000d142da500340254a610107642c0340c0105a000141400904004007000121b14810301c000700d81d0360001030000f045910340844007801041d502c000c0700304d0390f0700701e0064600502e0080c005028282c1c82c807a043d8229030044408030701c1a400a508801601000800c4d500825410340364072550044d81d17107a0146005c00200200c1c104501000f5a0140c09070a00c41c0b64042d0209503c04a0b004032038403148021680c1c007d05240582d4402d0004014036a8008030340d10300342c0c41c1c4819030b18101006052500e000d20807900510840180340c01c0001c1c01550140050000d03a002d030100300090910300004446104907440080c0c5153b11003400380011543c001c040880b0300810b4011202d00021545c50241510702e0b801c03001410f43e03810051290f102501d8043d9101c00c0a0440140c000340c41c100c0c0304200219030141010b80031016401d100280b142040048600100009200c0c90030600742c4170201d581d45104070351032802030140300718611513420088805188200e0080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 392088830 1250 392087580 392087593
    0x201020702241b0a0f0302030a020f060c0f130902040b030f01091406060a0c12030c11070e010e180a080901030f0b031f0f0e0307020108010602030a080114040e1501090e010509 77
    0x2120300d00c88401c5000e06009000b0340c0d03040400140c041040141709403087d0091030b00c1c0ca07881030780a806d01c2c50300903228285400c41d00070002040d40105c1102c4081900d2014641c41d0450001c4024043e1520f410089000f4400100819410304001c05184108103190241c01c840ea29080300d501511a1380c41160412412100891001d2510381d020f00035241681c03a00090200c0c0310748a030300c0c4a80d545503540000c04d5a45202020465208241c072428074503210007841032600e0084950003031041407280c18407003813010000c90314000d5800ca41c1d034200098001119101d403514145500c01ea1321050a0f1808240703490141c2c50340101d24010b8110030301004019102a114001c002d060170034080b0300003403600340c2e561480040d5403520300c05e45236406041c1000b50b0303ea03001440054014201a000380e820b55005110464020781e010803198151070000961909800c0d180d00843c0250200781c0c601c6245001d58144104008410318140d812a19003000620190302c0d0544510700700d0b60240c0303410295401c00c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 392090080 1250 392088830 392088847
    0x60503010816050f09150d0b07030b010c110f0d08040602070e090f0d030c0302070f05010603020306100e13081b010c0306150522050a12061b020c13060510020102070224 74
    0x520401e92002400150b5050003180c1c400080347c449800c1011500c108441c820f100d81c0710342c90300c65900c81031403e0802c440752071050f40341d100050580e540c0301c078072507940f01e400244507840e145e141c0c0081c994080d654589032611440040d4070740401d40900f024481d101000181d150b400002c11070204c1442038054600c801075000214050241e5960030810305408028620000c0c00070300702107c060780540000140d640c190310401d410b0a10180070306003c095514018007010303e08034842e81c1c112a02c03101051101c09545003c8420707020300300d201141d51800401c18140110306420501500d1015a010130516469070000a0702801800c0568005601440000614030154810140910840e141000490341da240050040512500100d1020340c00d40003c80420140b4000c02e8041448080c25144c10060200001c2d0b4036508a45d10b02d1055210f166485a00f21071588000003400c40944a041c1180b01c68101034043d603c4094100c2c002c00c6288403a28132101d190f8071a1400c810840d12042c50034614 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 392091330 1250 392090080 392090089
    0x5010e0d0f080a1a030703150b180106050717040303030902010906050415050c01060504020715060806040b04060c1806020703020a09050f16140406120b1503060616020307060503010816050f 83
    0x507007903401c02c241d600d09001481c0da41c1007151b50019481101c006403c50100001c11080d0fa141c5031510b801005902640d000f0511402c005606685551400c29256407082c10109408503405800800135080028080140741d410742010040074001c1c1c8900240907910a400c81d21482544030b80b1803600c0454828481d410300c101c005182ca0640600042100b03078035000041d0481c3d0005108840b0780c90318102091601040b402454001e0520700c001d40142e143c151211009043d000300024401c42d03940002030b00c00d43c01408803091036a1509040d040b090348481d80a035465109020680c0308000c0e100d40054100000e000e664455031500714a000582c441101501c2c00740c5800f4070440600011003a1701e105140c0070000341004007040d0790f480039004140d026840c01c48801812150142485100d4007c0d46a18001241e4201c501502c1656645c1c00004000c407410102c42030080d0305001782c201c0051001c1d0b01001450503120694152608210204018065103409110340c13a000064480b560707000e841c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 392092580 1250 392091330 392091341
    0xb15240315130e0607021605010905091905010b0301080f030309120705030706020d021e0c06041103010e070801090b060916140c0303041208090106050f0f0102030c0a05010e0d0f080a 80
    0x1400307080081419120440395003500c160200d03080f000e0780802c0800800703a504000b810526079100c0d1444407140c0c1000002013240445008650180c4840030100e1201c0b83c0102401018400241007002556128403140300e8580c0284144c010303d10429804141e0013074040201ca0285005400410407040d4a41c095001a00701d4007003030311640400c0c0b141e5004a00140004c000f000c603580d400580e281e140c010070141c0002d143e6481510624280104106820006690307500700e50406298000d0311800e20009025010803840b0340214000d241d80000c400405401a010749071250400100d607607a103409004280104840c1d8100e9906c450303e0121125010703001c40241c41040c06041c614000305409060301c1c41d4070039101210390f0340c1c1410b6024840c0fa403113101250056000310090003201d28150000b4202042e9000303c51040448a0701d24989a008008480d0824604002d507500d408550505038000c1031b54410400d8140510b031070044005d84109842c001c0b440c0b40751a24100c40e150000030000814 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 392093830 1250 392092580 392092621
    0x120318010e090f04022e080a0f0c0e040b18010902091311190906050403060213091e0b0f151602060d020a120501120b10030b152403 58
    0x101c2004400000e03122000124401d0008078043c50807420103106008400800da03007900003025000c540703040158401641410303078040d18900780940713403030303205e02c1400400c0c0111500072800d2900755050324860b084500700000d160200d078208120540c036403e00c0015182e10700d86680c0080031000610113905664041c0040c02800307071031204010b800c040759504913040102c1c0ea808500000c190300f0310042c0036a0300c1d04001d00c05464a0003583c1c0c600380002d0054007a6000c0101125000705440c04c203094402128402401c00080502400c0003400c7d005c07074508841c580340790100d41008407445080c1030481011034928005003101c1031500706132025480036000364000c6001c016801c4090005a502d90700541031200c82ca020069445003880d00c0645200c0d0124a896941418a00104601c0000090802d2584c0c1c001110703622a83d43c2c00000681085542c20007052801b100b03003400083c0c282804c5a040316003003a9810404010740c4408040701d542d5880942c96980000c0001418a4810b90244003611 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 392095080 1250 392093830 392093837
    0x90c1205131718032b0e010f05090d0c1502070b070302060114030f0601090f06050312040504151809030e030c0a051507020312070b060d08071212090b0708010512031801 74
    0x10f6500c100103801c0003c100c00b0000d240d212101c40042a9402d031588400062079800e00c0d01080040e0700001e44a040c02c5010b01e002c0c0030011500b414241c48012207940140d0f4000d100108083d12151503408400100703020500510455102166102e00c050859030a00e4064000b402c840e8a4191261061200072000c95014062080e00c0780c80c140c42082118007814140001284152210399030a048800031342c01148650b000d2406800c00104090444042e240c09807004152482e844018000282d8140d00a210700410a000154028640d40c01b0307101041c46680c2d00b00c036078200300c8101a511034240e0501d076072014410303004104a290800401003851600d0040070f00302b0031070f5000641030100460090001c1800011418100902c0d076420740e41c0114100d0f01d4500d0f8843d20b444504690040420051091200312074203040240901c560345012150032100744409007151034030720b00d000d106440321400f08110100100e064500f05030407003500c0148030021403c05c40481c1c3c3c0034001944400031641032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 392096330 1250 392095080 392095117
    0x7083f0a030905011404110a050901030602091c081e0f0318010e0304120b0702030c0a030f0306030b090d090605040513090c03060e0319020309010801050910090c12051317 75
    0x10405e0041c80c20348003000c000c0e62a64545030500d00b1106144812040c82203840071000c2c01039548000d02c0300d0550750048001030725043d0b00703000701303803055141d88400e80f41100710f94100b020840910010300506034644080305014203111801d05c114050304214a01300d20007840040c400540d03180c841103040d51814000310b0056640c1400c503086074001c1d08400071202e0701340440e1062100050710700340c000703c0d03d03c025032410203044020b41e15030400030402401c101d006000c0320384144c46074000d840615000003080d681818544012940d030440440b06c8030204071404400107495015606072021a0005000d0000110450624500410080300d0454034020514001b102103000e42c8103c1d050742c9482e80045d55280540003550925018000800c4110741c820441481c941c3d0b400b0103010704541040d5003003456a2030f00d91800c500000760f074000c0d5500c10b00e00000c001166500000128969105030070400560703c42e10200000c031542800060004d400342d0f00a003a00f18105402031010858060f141d08c00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 392097580 1250 392096330 392096333
    0x1c0b06160201083111030712020114040305060712050603060c03010b0d060b0406031e06063f1b08100324060f030c06080f060418020307083f0a0309 65
    0x100070841001210280c4a42e0340104c100300b50006078900781582200146203261030f04164006414072444001c3c10031a03580307a5003420300381a50941d001346a01c4800e4800a2500b0b51008018450481100c4401c508150104449040105405000c1c032601030780f5a14581c280030203244594040c0b05e4440c00c0765552000080d140c1400301c040c00290100d0340e4042030ba51a07529118003044032804080c607132145031403410410307560009055241d520098104a40c840f4400300c1251402030b4080302d15040b0311200c0328040c6078405903400501c19610307080448020014010b0220380b0500101d4072a030400103056020b20110346900000018680074210840c5030461324002c801c1038032003580c070405c14003458510078401c10082c01840c0c006003c1d540303441d400c5480c100b4103040c080c1c18040c0020b0b0040380d440c40383c50003254242c4498000182c0180c03c8400300341c0c0d03880078240d4402041001c00340d1f009050002d6101a41603080f60420b4240500c0e513408242081104041c0d194000e080b100700b85540c82c15a00d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 392098830 1250 392097580 392097631
    0x8060906090106030e2803180f05010e04113903030408181903110405130f02030705060f0301210f060e03130311030c10140f0c031c0b0616020108 64
    0x480410a01b820500e0140e040d14018001290580064041505210702881b621119011800c1201c4092801d000366441d901702081c000c000d904195940e6010010303080c0c01c0c0264224036800002400e004503c4000303804c2110305081020411420f0b22900100041008a850200034080d44503268071241d01304110f14000a40410f80403001c840c202c07508284c1041030204a80070400750100a48080c00a480c10110184a01d030075a00006d10946106800c4010340d10b0401000014004c007501c1e26560b070f41509580034564000b44902c4c007120000d21445441044107041400101d40d00c84100e80c0c00030910741da0a070150078032204111141c8400d01c000682c1c6103441c42c1c044c0095006880402c26501504140340c180200040e11a003d0f0074281c000c1c0c020305a0044100070000190a6015200c3c2100040748489100304420f41c4014400840c144290301d150150701400d02009010801040d10280d040c8aa1070140d643c494440d66000d10301c0001550007015243d46c03000304100800107095020b042c02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 392100080 1250 392098830 392098873
    0x507050f0d0f03050f07080402130608060a0e06060d0b0420030d03061d060108070302131a0319060b090d080c010f0c09080105040b07050901051c020a08060906090106030e 75
    0x4000082d07141c511502010f816100c1c403600305000c0d0804c001d032458442c001400c0010041d100074000d0f00e100100030a84241c83d0701c07410140603484103803255410242d1041000d071040281d24511030040c900440ca5901d001c9030410340190788251a11081d944903100d211120401c2d0254070984260143c40968681e0140507000199100340c6000481e1401e010442001ca094900b02d407554a4101091108503a00300200701e0340020507241c00760342c170b040424229402550300d510407208410b00302607400c0c0e4040020040c40c40303501600000d00e041c4002c041d0f440c0070707500e00d0320030885004000c00114000d8140f4a0a50101e14003a424241c43d210702d40115500316074030842140d00d8542c0e1000c40e1168a40c1c02100303031000342070182c0248401e00385500c900f0b00d0744401070120400c0c850006441e0b10242d0003082504c014130805903900107c404001251b1000e07522500c0c00e00f000500140c0082c01d42d14014441c0c5005440c003030b080e0b0b540303070307084c0341d4294014240610003042502c82c141d055225042c8901c0030307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 392101330 1250 392100080 392100103
    0x21903060609060b16060b010201060b13030501110f0d0504030e12010e0613050705090402180f090601170615010302040f0b12100501080f04261306030b0d030507050f 73
    0x1e07080c0c541039aa500300e50468100140d03540007000300300c244582c3e0802c0180c0d0540c1000300040d0304440240140c5c0186003c1e4044e415140e40840c001001d01154000002141e0041c0024490112100304103070303651181401004007014203005103d80685603520456010b84281440b411030303103c81c0c4c0015042c0078002201c8646070344076800c40303e02d000705014503a0413600420b2201c0b90075245944c0d854481d68503014281c010303848000010150755480540203481941046890190304100900c8c941250040b1407080c0188528000001c8060000c000c13100f14052030303400f8000545501281f10440305441c030586040540902000c1a45491016400010540b001c88240e440949048504960b000103003094a20501800100079070398000ca0150b92000700c19541d0403032a50b0340d10300740350058581c000c00802a16004900e010b02000f090040051847d03060f00f8034045035840300b040382903411201d2200d4001035020b0303240300081d0042c4c000c3c20065108400b511094010f09603102e181c000c4d007460 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 392102580 1250 392101330 392101343
    0x2105090a1205030c04050d06020f13090b030703080307030e1606030623060304080a180608010617160f03090203010504030503060a0b0412020112020d051501020f1b010c021903 77
    0x114800c10050742146640c5407001c0c1032040c10340c5400000d5640701d001d6813003100c0c00340d002050110708002c0107604545001c03204034070b00c80d116002d050010b15110308a0040c01409440c00b01d03009c1e118500014400b0480780d101c00075520710b999000d011400740a0011a50b5014490080c60401440d820103003600500016a0001661b615050201414500120708842d01000c2031070000466254001141d901540140c04180c0d2200043c20885060551a40a0041c1c0100d2440403c00315880f441c1d160407a00c0954401000c007030b0360243c901034140f054888488407180c03074050b4003002c0d000b00307601d6a1079980c03400c00281030030090300400e0039141e0858080700000e20010401c00c49203401c0e04800017400030640c4a41c1401d042030a200f040c5100304002038103000c81c0344c0507080d951020f601103a4506101000070300080c02c0080002418620b000351241c00741c00340c078240160b450800903181815004900c040308880101d907006562000385290141d800095107042c00005081c040c1c0303081e006502c1000d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 392103830 1250 392102580 392102593
    0x607030f0c0c0807060c050d09050c130e0c09101703030a15062f0d0210180201091203022b090504090809130b040911040b0102010605090106210509 65
    0xc89090440700784400790014822054161404a4201c0f01030f10001903002d080010000850007082d07a80d0300070300461441d86810b0640c881c0800c039012424644402c015644c84d00403500e840d2188041d9080f02c1c401c481e05500007440780d541442c0050010342c00c040c04644600c415500d45003000c52001c20000c490300075500000c24070034040158400c9044050320014440c4074503007404c0c130080031418552004001103000940d40488202c6c500691980c03620960219820002d1000019460f00016440c00c2c600510303210b0b0510b61061009060030340c40d94140d589103403550428041150a04602005500b184100300c1c20250a0440c0c0b21030354184007036259891005102014000d040c5003031030708a58050350503c4103060000d1602410385400704421034091044003101600c2c00300070320312120b510b90301c90b0600300840c06100898502c03410041080e01d0501042030f01000682c2603079114420310341c211204000402519201c2d000c83d40022102141c2003610300c48000e84a0b00703441095940d24107980120 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 392105080 1250 392103830 392103851
    0x504170f070806010f1520011406040b0d0201140705030a021b03011a0607050c19050414090601031e120906081005091f0b0304060b12071202010e12060703 68
    0x104034200091100e040208042c4d81004e2080d100c190306841000e601c5ca44900e40028814000c0d8601035003525218502050200c40344003150180450f40d440311035884154001c2951400c0074051840800b00c06043c5009800107540119a03282c0c801c1c07035400c0782150901101000170001d000804402d81e00ea8000c200748518961100c180f81542c82840f4843c1c0c1c5803030701c50103045c03d0900c10b40d83c4150b012a92503450f03403183d041060614810410700350780417980c180310b00d04172f00700300c0728070010344100780c4042100e00e0742c00580c8038605006444c810115031184004000141c940a0b0001913080308056600182d1002d603a40001d0107042d04801000c43c070340f01028892664406100e5500081e01c2502c440000e240c100458900350b800340800d8072140007080030742d14140321082103d0007010b606444651703c2c0f80030b040ca0802001d0b0800f00da8442c070005000e8842030400002e00c6010349007520340300c55000e61264019140c655500c80100d4004200c0c038a00401042e0038000305129001d84e03100444c507500c44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 392106330 1250 392105080 392105083
    0x1103090d0f0216140d060f020c071a0d0b01140307030207031205040f08031b0409020414030d0f0e0d150504050d2a050f060a090b0c030112120504170f 66
    0x403040c814046601030111041d20300001200f4004075038030100c0c400f007034010342d001149915081c0304000e028113040518a2016811030343c010a42d50600c0400c0c0c3d9100c42d2078555003041e049081d4203400354600701780141c1e8440307040e90303000c0100420f05061031400c84807004030440d4581c00c201c0316140401d5011030000b00307045d00503015407140694002d04100a103010743d43d402c1600c82c52000903103500340c0400050b00c0c103a1042c807112104555604442d442d16614549000603500902440d142d0071603190070300e016410002690101d01c0c445031a046408030340a0360440d44403511500c1180c1c45004441ea0307102040d075908007203503400404407000c9224581810725910302200b1050020820290314119002c01d00e081218414440d6140403455a82100307041840c40c101781c0c1c146101d4075020300404d028000541e5400340f030400d4032590801d5266901c0040242250009110b5000ea001c9541381c001e00050124171090310070501c81c146203081503220703121448060000780c8000c510758003000d004680241c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 392107580 1250 392106330 392106347
    0x3050a021e180a0b0a080a020a09060e01120302031603080a14100308030901060e130c0b0a080a0b04140c0c10020a020c090403021507170906040809131103090d 70
    0x1a2854a102090355803008a001d4200c210b00007032001521802007511001a6003042c0e8081c480101011212030b200e441d0f254a845140d50704034810300004000040090f0280141d4048950544900d5216031030f0003903d0f0204a0841821030850108101d100f60109116040068442c0a981c82040c40e10700b120004080307401c4680100c01050204081010903003821610601780c1b50f100900346d0303c0e9200d030715800707001d4040c81c0c0000003000d4804d001c0118190180d009012600d01440e14403100c156114080c840742d1180e07049a038009a42040010a40c55480d00103134110040038200141c503800948560301b0342002941e000420050004d0300304401807041001c1c06200c00d25070011481c0184510019544581c6418414012580d14000034241030080c0526050084c00d14180845460404401045800b1401c5000b001866417030124254100c0042c0091050354001d40d8107140410314801c0011142c04000305400240d21036011081000c468409503001d00a510f005010100394904003914800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 392108830 1250 392107580 392107609
    0x3030304061a0f130903090807120516061706130f0606170f0f09100f0b010306090e0a03052203110f03030703080103060b040b100206010f080a032106030c03050a02 72
    0x10f40055007603006581d44a0942904400d5140001d075080d818039040c0c0701d03c0c13000c0e8001c3c0b44074001c8d01800a1086540c400a0038650700c101c0985828034072400308c03c002034250b03014440015007580c50014070145a040380039040707900102050401508000e645060781e40b20416001880e450318010404150040d038001d080c4502111507001c503203000f4013103541a0600070608101d440c8142c0c00302d200c603007050051010721020004240000540100307840c010709070601e03509000900d03042c0d0000e41003050b07110741618109110058010300450303403002c69194000f140034011700030300e1110031007520b0000c141c20b0000398401e14824070342e94440e43c20000314070403e5a07258001c2e001044441c00007075029585038103582d07000d500010b00c2510880441c008290601c00c1d00d070820079507040d1030465500015030358101c500c0e1381001a0150345544032540c4a5065a800070003180d030380115802d40141810300c1000d5000510800640d041d0349880c0c1900c061181e610076076454101d40b0448040d414079240b80c1d141d00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 392110080 1250 392108830 392108839
    0xa0c0c1b08060702150a0203060114040e150901061b08040f0609030c0f0b0d0c0903021c060c09080307080702030c03030403080403170306130f0b06030109060609090506030316030e03030304061a 85
    0x110144260040402d8020100546d4950010000307040d60b000e6041040c0115843c00943c4d16151141000b0001e00c1094428118018903c21510358929000d0b240d103060769540d549048418a01010303500f00403145000c1164060b0081c40041030f45526030342d901d8020039103503488010280c075500b0040c1d411101904440d6049040b400300344482d07540003040725102c0c40750890024440d829607030120740302d031000c0d000207501ca0120940c90300e4940c0e141400c0c4500030702809041111041400341520818068443c201c650f070828480754005c42c0c0040090401940040d0541b0444140d010000b804c41d841070304100c421500125052040c0a00c10440c00c2d03103a40c00041850bd141400300010b100304400a0b00154a15110007042114103103e4100e8860100003808050b181d50711960000b011380541d0040c580011300a0000040141c0c4a0180c0d500500340a805145440c407804d40030200001c100e00240d050000203403003044140c0b42007000b9072085014000001b00500342c41c15000c505900180302d140306 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 392111330 1250 392110080 392110093
    0xb13090209060316061103211602070e01090f0b040507080405190c030204050421030b10030603020f0d0203150c030402280b03132a0e0903030a0c0c1b08060702 70
    0x8130040e441c02d080686809040641a902c1d003245d200d442c52013444240c5d900c243e11b00c902c4101d40420708550342e00030140b15100000e1401000f504030f07502c0003584242031120814a00400801c40280d01c500040200d070704001c20703a00d1b51100891f05480040d81c00c1070010f00d089080005001003401410790020082c40742d54596803064480b903a4075816030001901c10bd40e644041420411079031030740c03031440c40c0c2901d2055031707c450b080300a001000c01d0340c1c50038001c0f115a140418071611034030800080e07a038003c20070440d800034941030120410809608982500c51290a868520303080f00009100d4466003140c0c84e92850988117000401205c03085640e1040748031082020750004191611040c1d03a400b040c3c050b101d42d03901064250704a034030303100604a01101d07180c94000a0b8103142d0007800300c505001e807010155480301c01d080e2505c0d00700d8165001d500140003103541868550015030356010b080c640300418800329143c04000c452000d81c0d1582c40380790303c0c04c1000b80c3d040902107184d01001c24009002c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 392112580 1250 392111330 392111353
    0x10f0501030b2706010509040912031a011b03170109051e04030c030f0e12030309060f06010c110609130b0301050c031003030c08040e09070612110901030209040b130902090603 77
    0x81c0c0355288080c1d040000243c000140c003030f4440c00541c1c40501c0000d0080c860002203007480001c4032201d203103a00000342005100665003000d003288800d059010395581c05080d481030603941440d03540704400c60401154520400300914807000e00c80c040e00308144000341c1420b092100000e240c50907101003c0040a240811000c01d030810408080c00790141004074a0042c8040708803500400c0c0300c11281c2c414104500c002c1408000400307184141c101c0000ca48103901c800d500e14102000c111461400244d64001c0403000512140c801000001c001d0952400c100d821400a9408000d02900c0b1b1f92640d910300c5010f4080c94240910b6402140341c00b1414592b0038101c1c0007103036000c10b40c00003506200011404004005800c01142d00805c1c1d44000700c9083d00b00b4001c4240c071901c10748182800103042d101e020240d00c80314070952030450000c1ca51036142803c01801540a5048060b4059001da5243c1084045880b4184480740e5420440c000041c03003150740c8100011010003034001e5010394041c9400a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 392113830 1250 392112580 392112619
    0xe150c1b0607090909081b12030c0c011401081e0c060409141f050409080714030309120f030a05071e080703230105060c0f010c0e090f0f01061103070b010f0501030b 72
    0x407c9a41d60b08085058400d0700f50925180c001000d50001c0c0307816000041040d44100f00c805040c000340c60500030300c5550011864898035200030b0096a2a58010503100614030800c0394049041c0704413203003900d03481010540003a038a90020360084200940301c010307078003c00c169400c2140c7d000b4080c08000c0b580c3c0741c0480c0c04c101014018050030380603558a140c00d400380000c4006071030307103a94402c40f14600c0d203003890b80d5140ca03504140d80341e6101d880f0b212620004501c041041e11138035030f003005405046569020294001e800043c0a900a000e15a03882040c0300807040280010303a0b100717440c1c1c0030307140c104500000c0440320203045105001104a50030207180b103403880300a045135803c8480c0d03602c1d946129200e5003804c0c2660362041c0558039204a20280b0703174021280860703000084505a17410f98506c500d03642c890004958284d002d01c12140113024141c01402c841041c2046c0c541201c0c1810620b81c2c5441c0c10500030703000713000f022110310810005587d1500601c100c8010a40703c1e40124070350510081c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 392115080 1250 392113830 392113837
    0x403180e04290406180807060207020906010f0f0e0d050d021501050f0607060c17040506190504020108040b15030f060108011107051504030c020a06080702010b040e150c1b060709090908 81
    0x824150b202c0c1c2c401701e0400a4980c89800442e04404401d80d074100d10b107007281c029801080c0403402800d110700052800e60040d002400850240e0301c828020080920040302c008003002c3c3d1007030703000300c4035400c90703011038001c10503070b4440c0c1c4e1203800804140564809202c428801603024620070050340c440000c0a465071402c0c0c8054913840f040200d910303510500151508486110400500c4502c50200814007000191480c0a24051803004101009061044040c0c0381c040320040e02091b10240410001240074130300c0c0ba440300c02141721038027a80c04c107800a81440d6040c2101d42c201c0d031010006000c0c02c2c0c020311440d400c040d20704484034a48080750361101d40711004011001e002c004914002410305001c0d060104401c0d500400c155130b919154140904620b4041e54400015842d245800480f400d25224580041079040c1c0188681158001106440301d0000d02c24070f254502440b0a07240c64046055502c00d000480c1c010f0540340c6400940208040d05503071114003203030300f04038a4001060000049 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 392116330 1250 392115080 392115083
    0x6020d0b090a051b0325090603060605121f08010515011706031e0f0d050307020105150307140409020307030b0711030a080a050606091f1103130603050403180e042904 73
    0x2e41c80756562a04089044110300541c450341b260038892043c03486e444415a415504103490401100d52601002c4516004a840c1c500c3d1700e036440000302d1071000100040018000c51141040903154a503c132450940c2d000b42c501e5000e031021110390034065030708030300307206142d080340c40c00340b11f079440c08400081d52501144901c00c5148011701c5d100c0680350052000a86500c002c008607902c0041d6988010700980c400c654560040d4680700100760805501241c21384100c1000b0010207000341004281c0700d1040a0740001580079a40d0899040140c40501070b540c01540202000521854481d902500c20661404c2018483d0070400402070510342241584d608510210300014607a562100413070518460003c4807a84070074419150130ba000d650100d0200364006a40d9242c100140c400302240ea03034011802001040480303000140481131199100076480340c000d16010074501c8202401d0290041207400c44403503810403204200c148030000c0d07400c1001000c804021700d002e0312012008460304401600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 392117580 1250 392116330 392116381
    0x50a151e0e250f030b19021812010209190306050c07050d0f0c06050421030b0603041101031d03070308060618010e21030c070608010f030f020a0306020d0b090a05 71
    0x40500d4094202010b0350050903144400000940d120b040850038a8000c03240c038500070780d014000d00c581060a00944202c0c0841030074224468425100308007000800c0c05001031740799424424016a81da401241c0e02c9034120f22486548001d040d400c0c010140c1320300411030400110100060400070340c0008604981e109240303007040c112810400c0c03c03101c0c0d00030307000081c080c903050606000034020044421045240c0ea600380683c2d604034440706a0954103d0070880382c2c002014000240801d035080f004019240052600140c2680040e00c4034a00e0400038050400c2c81d403000c0341410805801040d07041d04070204495403414071254070351545070040d00008141c1080f5500c0e001045603162040c19100700d4800d2010044140c2030b28840315683d4110f04011201440b4100c0c0000b03005020341a201d041c0c1d076982d19084010b9046841c1c0400808001a0803a0040060000040824043d10141048120700100401d40842400c00c00c6031005d0b003d402c5d0b5810741c1c503103030920079800d21100e0055100c404028 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 392118830 1250 392117580 392117623
    0x19050c240f040c33050a02010e0f1f090804060c11010302040e0103080a020f0607020c03100501080c0d0f152c03160f0c03030206010e0108011116050a151e0e 69
    0x511888001d5a20704800034120080c683c940300b9285c103d030207843c0154480d4000c0200030380c000a5030359034500380012001a40c20804d03503034403403100f00c044100000b20390f841c01055045465603190342c150f100d42c1c846400100794074005010004140e10400d00300340c0c01d207000c0d8107103410080130b051300c00d10602c4024040c54002851240c550b0080c03010010682100095640034600884040d41380c5150702cbc0410321a001d18680c0c440071000910a05050301c001100500100c1525014403143c94041c00003a90038242240101001903640d44003480401034000d4042005441540840716680020034034007510720f81010500300480780001030707812182000104140c0303031541c0d003007600603d031783e03140060611030780000003000b415000130b006412100100390101c8140e03600d0700d50900701c40c0790801c1d0141391072041000352414106280103543d02c50150341601c0b40c1000e25590986208950511102d007140c40d8100c6d00e042d811810201c2002c2d00b6440c2090020b401c06200454840200307945003100381c03d042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 392120080 1250 392118830 392118869
    0x1150c150b01021501030c051203033d0311040c031a190801020d0203061c170703121d010b010c0c09020c0a051f0b0f010519050c240f040c 61
    0x204a0002e025804c6903031000b95503120304050203144158010350340074814412000808074000011030344501040c09251440354240c4041b882c050400030104016031040c034804401901e0340a04020045100380d900384400a41c4105000958030b802401c0d1042c90f01e4010600125281070300150070000c0111a00c003c00900b041b802d00c080211500178000079803011689103442c0d141c41d801140a40070407138100046100c41c0300c520704911440100107100034143c81150100d2007810b8040c00250340320707050116160380008920000c90f076001070800208004103c2c00076420900780715140b111030083ca00841d0012264951980e400e10038032507203000c00c3e030004040e003032180144201c4034445e500c40309607001d64a0911506c104811074144e4540c0305403a00151158a00d400c0800e0340c2d02802c10784804d4213080840c4160b4107c00076030882c10040c440300700a0035408003000c0c8620020340ca1b07420040c0c01ca643c0d50038401c101620008107601c008040107814440412541c40f81842100c1540080c1d2000c6200b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 392121330 1250 392120080 392120083
    0x7080711010908030f0c07240209121606110d080a06120c06030516362d0803030402060f040902040f0905070c02010e010e01230301150c150b0102 64
    0x400050901651822100b807040145490080d4011000300500c3c88254a0300180440d9520842d0300c02001d40641901e01c000818018400900d00903804600600f0210900003044412544410b40109501b01c0c40541621829184a05014150b02d1a10400001c8442102c0350741e594026006420f020340180050a0b10600e074200c000900440d9179203a84141c0c841c501161300c0d0b01c803801a0350200b8106000250300e109182c0f85420344c0400350b0b94a42c2d104800003851200340c00c089280c0c0c00d07507000289084c1021190301071804020200e900c0350680904500f201c110706107090f0f000218101094a0041000c10f0001007a80c0e00150115200c3d03079509580b41780da12282c42039034007840d038081c0040740c0001c036190707445400c000b1600e50000c1170000c0e99070b01404440c6207101285c02070100e40400c412614079485440302450041e07042c14060041342c118240c040c40c942000d141c0812048000005021083c1c19007910406023803181041c43c0b6008081d40c441000841c1c454011554690380c0d00d03883c009030310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 392122580 1250 392121330 392121347
    0x3010909141006060909020c0309100c0b010b0318010e0703080f1201060e100e0d08090d0f1b060c08040e0a1107030207030c0b090d0206030c072003010c0801060206070807 75
    0x28240807100445a03105410010f00b005202d444041680710030001440021802200d41391081c02001d503181540030000c0240780384078500720300c003000071080840c2c00040d14000030f540a481c00000045e02c1c1e1418004c0c2e40419412228602c009904147d920244160300040880c1913035800001c40307484041c00d120040c464000e0321140c00c4038103206400015001d82020205c45a00c0742034030290030562220905882040500340c0040c2c0015820804201251001c0090054640028507514000e209a01ea00c1c1d2400318021041c0c3c0c4005120a4107042d1a0b00356818000900c0d9908044003c1c40050b210700e13015024611941ca4078103000c2002a400002941c402440280c4080d0072035150354980c18000d40d80e41a90004944e40b0b42002400300d50307400344d02d040c1c1d008044010f050810f030f0380d455400d01500d41c00203016190b0000046c403880c00040d01e00c0c0ca10840e00c80c5503100040c46110210101400c1d151182c000006100c01d0200601900323602140b203543c025010b0070b2102107501c1d40c103000c580074903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 392123830 1250 392122580 392122613
    0xb030112080f070605041e081e1611040516090303080a02130311040606180603090c03060c18090501050f12070e130c081605090c16080a020105150603010909 69
    0x1c6001414104200c419070026001b14040e06284004071801c0412040c82003101c6009010904180314115145103204440f80c400b02181884a0030854210803550160010324012510410210010304107414184030b0303207a00000071001107006840448005d4002550780c04064200191640007494511031501202e03841e029000032003240f0b0385e680c01c04080c104101a00346128500f41034001a01c01d2283e020502c0b081e01c1b0110020340c50b440d0100940c02400f0340b40086850302c20110000000c02c543e031154000e480d10f1900d403030056a0221600f05002e0986400041c00d85280000600268480c00001c080c0c201007540c1d0b2075003100301145410710b0302c81c1c41ea102403062402e9408000b0b09240000c0e00c1c980c110310403400c0200f51034072140c80ca515500079501c12019072400c0e0404004a02e040c91070181c0140d0000681c515010032590860240c289524040e9030300440041d160013030503424440c40c1d6018002060300401c018564000481c03610040c4503000b503494031401407106000600000c00d8004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 392125080 1250 392123830 392123857
    0xf0f0c0e0109020405040c08010e010510020a060507181d0114042a09050109080c090718060504060e040507080c090414040b040c05240f0f0c061f0b03011208 69
    0x7980d48102480c0070f580980100781c0607604101c8a03900031400b425205050391150218000b05e070703003085c0c140f003600c8810b03003030090440c41113805d510040b8110707124a5000da000ca6840d02106c80302015020440c10441c2d000340c0c500004d00800741d01c3c9001e2548018150f44424513201d060000c004005400f401c07078019004425656440c0202c15581d0484d8000a00d804035250744c00c05030744c1d40e001580d10070060700c00c1c0d40d500d41011951500b9850034000c4942d014006040c50040d00b92000c035208090455604482c000c00c00000d000d00c0000e03040305034242071074000c44050100786803101c401403071600702a084600466000c41c140780d80780d0303c5820100d04801280c280211501e01030600018012080d10152042098080c1c003040e03600f41494102980040503410043d03880b0f0440041106501038694560007a00a00041d11031590000061402202882c000c00913401c1101c80f00031010340f9140440043c0a135203000b00700f4880090103980c1181e075642d65184011302c160410080601c64050041c10b031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 392126330 1250 392125080 392125109
    0x15130203062701090b0609070c1e0b0f07050d090c0911030406050906040b0403051315021b030c0a030201031104120f0302100506010905120705040509280f0f0c 70
    0x1100402c0c22100b003560701c2c0c00b82540c41d02440400301ca0803200640780151510425000045a508103003441a8000e00da61a044141c8000c5440350b040500c02c2110703484004003400440002d000300c0400c13964005603200719415035802d04181c090114402e81030400d2076961a24001ca0a100c10104004002c1c0441c03038083c0010301c1c01c280003041d95441114200c454600c1d10300459541d0384000754082c4500e90120401c51a5190351300d0980d03c03a0090241410440100b50740480c0e200c8000f40041c5120000390000d0961184005140c2e40054440200500941c084403038954a59200034180040380d4080c00c7c00120804032441d000b1443c0701c2c03a00304180d002c82c0701528004011601a00d1041a4001c0d800e07900c10800c1c0c094071100303031a01554228000b800e042002c0c009844d01c07640a408040d6480704842c000303583d41000c1020381c0e4048400c1c00e4240c01120760400c4400c251403650305100c03e050381d20890010940c0c4d40c0c0300c80c00e8421101400080851145030108428141d800300035040e14582c0005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 392127580 1250 392126330 392126341
    0x1505010b28021e01060b0706020304060e1c0507030509030601060c0302070b16060203150d030801050a05010e03032a0304030606030303060506070c0303030f0f06140906030307051513020306 83
    0xa00d0744508410060611404107040d00e00303035038041c0315680c20310650281c1400381a4429030059000c1103e140081c65507038800004004001000600100f0320884001d0380b603240506180d011114440b0780718595030004030b030400c070b400d1201100031011303a03440c10702c6502e60040e0b04017200d540c010a4030598151080c3c1b4004102d15400850b0403003030740d101c0da00321501c0940b079140d00702c060300400720200440e0720442152400a00d4079009980e0290003070140c034404800c1203000649aa14200c02603010411f00c0c0c00502c15814000c00e15001380000b801d01e165024034400c0841d95030710855500391b00111000c0c20410f032014100309000b00c1c000c3c0c80300499840307a8803418100c2c014002884210080391400000164a00705071003aa61681c0d0400c0004000f0ba02c0c607241034026180b800c0d200ba121036035031044404042028460803010740400c002250000313101c401800356898001d00442e109610a0080200092000510480307a43d1901208112030303c0d41d00d900950760401810007075050081208005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 392128830 1250 392127580 392127599
    0x906060305180c031f0e15010f0611031e070f0308012303030f0304030c0f051b01030506130c05090a09271509170a080a1b0c0f0813030804060f0203120103030c150501 73
    0x38180e4010450b0410300c0c0b58ad4070f006035641c00313070080000300036041170015240141c0d00781c0107420114002e20665140107107070358801c40392010111044000c41c0c43e0744011b1010101d880b010485100c1c0398040b02c0c00002c8481d00081d03690041508003040300400000150406105001c1c18800d00c0c1e1000303944071601c19a16141f616032142107551454074101c124000b941d980f00e4001da50240c0c0019001224244200e0320144c040d041e900d03404030034410f04000a0880d0785403021762200610344c2000014041c0e400e002c003444070140030703d81d18452501031101c807408503020700f5140c608501707d07040005500c1003070b283c003420095203040704160130100840d01c0c55030150445040c0e0b200301c0c0d01c00750800c51114040b986074480004000402c00081c61250800e0004080c1680d9248003402780c1d88050402c0320070350303920002d601d1a800490f100d40340420208038194000c01041c60010103130010318149452200441032180341480050b042019040303110051121a020980000324122410702c03496031242500c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 392130080 1250 392128830 392128873
    0x209030307110f04020325020a020120120f090a050409030519030f0f0e0c0a080d0f1806030e1b150d0b0406032604030b060f0102070906060305180c031f0e 68
    0x7610f440310602c40707d4082440412005d000300e505855110f0b0000400301180b00040b04c0c10391103101761081d503038540301c201d1039607024141441b44461581da4464110051292501c01c03035104034010703414601d201d00000d030401c0960b0200a80c050081c40740075903845044015000c803840070b145992504010701c002c0c0388a900104805080760f2f0498240387d64810901a14010a206011054201211400c4210310494282c030b00402075141c0070313661035800309040c0880d5009600000119555680c020110b000070300c002c000055081113164910000b101c0859080340403107801c0c00a80400041c00094280c941c2e1081c0101c0d400908104042c54592404455049403502c18201c041242110b6a00302c947c14411901540e40c40718400006841e0344040c03006400c50340700300c1c82c15030042c114041410086882420003d0140782d4010529040041074490031141e512100d8003d40c000d44020b50050701e00141021038403588506100503410000100c0c40184104480c441840c02104000c3c2601448507100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 392131330 1250 392130080 392130121
    0x180501030b0c1206060d0935030103080405010c0606090e0f0624041d0f0705090a06050102030a0e061c0f0e0f1504060212070305040c090209030307110f040203 70
    0x1e544281e20b405090398103e010724800ea01c0c2e0841c80100080590803d01d0240c0210b10002d40b0100e000e445503580c2d0f005000c400181e0000392a426040160405040b0300e101342c503941801c0189186504548444c1183e00c41c6000e907605200075042d103201080505ea00c02001048490000c01c803c0c60411050303a2503010030009411144641c0020524a44580c0141a4141c058003884a102a100703030501c4040d146401480080500d0701828455881c014024920b620251002914a41d414030701044140040942820303182441c00300180b1059800000301ca46076152400c0032100e45001030001416442203d28401e40c00c0f40a440302c1001c44040d130070484083c0e0344880f0a12280340142d05103a41c450f0311200d696401e50101501d20805c0141d00b071025002400382c14050b2415007a03171066012040c00341c030003500182d030719410071080c07060707254540010f0645c040d01903142020300c0b00001d5a03400f4240010b0580c0c00303801d840048994032850040c90554001d00195100e05e001d6800078050340c4003d40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 392132580 1250 392131330 392131343
    0xb07030c0b0906060d14010b121005070c0b0f06031c03330e1b030f07020f0706020705210105010602070f0b03060102120706020c0f0601150302030603030702010c02010918050103 78
    0x100b0030348000440c2051103200e02800d483d10111294a800600701c44102c40c510940d585e42c2d2600c84541c0313444c540c548407117101c840203010b9808008031813412a00001d00440400c0b25040b8164001480714900b15005988070392450f0311a22440f00290600001c0002c80549808404c1080d25443c0c154020800542544200e004030010340a02c42c2c9140e210246210015020a082071103c1c003d050101500601c00c49817103442c1046120000e50540d10a4811584080d9410104094503030b042201d0b406903c40d030000381981038508a0040d58032000d03805414811b401003072811200c1c2d001504421441c91059000381302e6075941c2d0328082d480301c0a5014100c0f03500d0707544101045842612003241d010b014184c0c02401039210340490895203400402d0700b02d0340140c003040f07051049241040717041d810034444005410705501d4150007062700d43d2015203003000e00d030040c0b00308015982c0200659240a80a08240880076035610049074990b030b80c0d40114a6030070103101c851380720b601c080c4c0c080ca069910828 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 392133830 1250 392132580 392132603
    0x1171609090608070b210c070c0503030a120c02190b0108010509031305191d090d0908070b0a020a12050a0f090e07031a040e011a1c03080c040b07030c 66
    0x7050002610410300804000e5401070408000c1e141224000704494441e103080c402c0003540c00e040e603040e814010391340f04a0740c0b0743c0400c040060100c485980402004100c00442c070341121030b00050b0410040d0703a00c0c481031681e201c4001503014001e122100d01c04c103550102458491041c680006109001e001d01411586800009021140000304032042c440241c2e1540e030307c5525150420102d81b089001061001000700400644126441d4001d45850b42c10211f18032075203000a40307030740741a00b4210309000304820841c00308103a64000c00e80b4070903203041d5600c060b40c13580d080c14168030300f03941d03020028a102d41082c19022896400300c0070b81800035030340d60b50511110035030030101c0d443d80642c094122020300e4031010032105402540060010310040785500c801c08441c000080c221a91a403030549140d464115000d190b000c0440c15000f000303011101008820002140d8510104c1c4521000703040c014a90003150b4411b140300c007994001d01e00a1002d6940d54601c0c42d00510f9480d0a1308102c03410344d10070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 392135080 1250 392133830 392133839
    0x5091009050f07060207061d01021908090f0105040f0902070218070f020601050307240309060e010c0e03030c12180d0c0501183002090a09050616020c0108040201171609 74
    0x128046c400c0340e8440d618042003000510300f00b009541882011410b42c0304180c8002001c0301411200d01440c1c3c00b4507020f51b02c0d540c4603000e0120780c034201080e190402034100000d0101c0ca500c01121010303107044800c0143c54034050710100d01c01c54280c40c6500c10b50070f450010450787e02c3d031180450201c1e40d60341e400d80b80144d90340c2d000d2554684a500031000818031441106145200e09415801001003600e0049000b081076101c03c012100c0c08851205165199450208000d0304242c142c2c05461050b4011441c180030760746074649035801104c09480304c20b00040c007010500d200606c00544444000c02e0b0480051a5240c0304943c4503ca124041c082480070008507807104c00554560100c0d541908081d03801460b607400e503180d018a0040d101144400b81c2c030204003680303c0055032849014025070016659100c2e0902500d4204020711903070803072016844c1640e5250b400700e040540c940c002e0030400c6450300d0f2880182c8070300b5200031081031140000c1c0200711000440c080c807074001050540700c01381250303100d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 392136330 1250 392135080 392135083
    0x60602071d0403081e01140a050109030b011a12070e040b0d120e040222052d190504020703020607090f08070302091803070807023105091009050f070602 67
    0x144903031440c1c080300c000003000703c0e0081c03100a501c1000c100c41505050b44603101105070ba642030b08001c0d21311b13425070480101e600b4071101001c040d00090030006091480c1d50307559104240b050040c405411460b00d50122440001d605031002510300070440301051811f0072005040915201003540f003981080182d17003c9040400400046c940c024092840103800c116056815400c064042034100741d003008840b0403001c070301c0ea012502c0c0381c44124240c8554544020402403543c2d4000e0042519070f4440e03071094034400012540c0107407206803507941e0344414108a0201458440d8066a00140005006020150f020031807502c80d049940f03400004a86968034805251207500840003198009903050001d891320462159000b41d203042da004904841428090450b001204121740310038000c03d17904214605210881c42c00000e40b00c849030120480380000604011613225800030340d540702c3c08180340b01c10910040b0600300e83c0302002d0004403d40e103802a5038007161025004603000324080450380510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 392137580 1250 392136330 392136359
    0x13031406060f1f120f05010e1609060f021f02071403130501080a1d06012d0302240a0e03071205030a0807021606090305100603020102031806040306090606060207 71
    0x180500f00c41d606880700d05494003151102c0c07140c902440304a900540a0a409010307200c00c0c031850300c20100d415458804040402480940f80c9945c6d501a0701c400c50010ba401508070307080703441d945081144000402c1059042c04012110b09958400031008240d04003802e4004201c4030f44901100104102100c41e02c3e07440307000e940341d45103503403040e568104403d42c031400259801481079240001c0780d0f5080f0452441c8100080400030301600040d0041041c3e2401041c10710040c40e40c00110301c4018142c50341d50520000901000f1303c50349141141c4c8a8a054044025510890364a0300503911004040042c2112040c4d1710801d2103881003201c04220510002d0702c000b909540a401182020b02c2c0b00800c4e6280701c8020045411403185014120592142c01c0c0f01d0701c0240f201d070303ca14640a065082881c00e09001d01010f406840c1092410401070368000110381c3c010300c41001c3c584000c8410381c0024801d1203130354400b070a02410005900144076460340501c046840c5a007c44000365079a4230250400803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 392138830 1250 392137580 392137609
    0x1503060602120d0b0402070f0308070207030308071412010b0405120a0b07110a17180108060f01030e0c040e0102130e0118020d020f0d06060e06040e0c0a051303140606 73
    0xc00403900034074190501c201903d50f07652200c9011503151000e402040480e0025070701a07440c4968903e503801499084002d998101c2c1c1e0754800b419089055483c05000c0c00d0028201314100112086000301b8000d804056840c005007010344403942d03507540c02c1c020820345c0017405568465100003441210b00140004d01d80c880c00d51004482c025582c8901e001d0710610100740c0380c28014041d1002090025044101c22030300089050083e40d191003401d404403121030003803901c40b414480210700340242c65644184140780e10400b480c0200307501407074004083c103003030040c54241d8105050041403150102e0640140c030003008011810180c4554a130001d6070808000c0c4240c5411b81c0c8290401c0e030200da400e800408250b000a40c5c007501d4180302c0460510581d2224501e0128681d80e04814440e441d4408054450030604450075030038581003840c08200d2000280c8610b0261000140c200040c80c0500141c03401c0c2d20a04c50148030550b0740342070240c01c5100500c0b0703c114030701445001030b006e403501021078001700c0e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 392140080 1250 392138830 392138833
    0x100f021905060f090309060c010510090902061c06090c0503041203110d0f090b010612060608091911030a0c0806100303140706060504110702041112040f110303040b041503060602 78
    0x10380710742ea0007499110f800340c409092400100941520364031400010410251510000070f4035107040400440c2c9005a46c0043d01c5042c200304c40203000d6900c92042e81c8299040101001c8034250310185200100382a0740090096401e00342c401c4c8205130080d020307600c20f50003040840154030040030100c2c115080d10b010b81914200911100490b840145e0100044d02c1c8460710020307445011b5201c92644072806d9001e6400680c0c0c2c0e90254403407020324001c40006144030300346a503550404014540e00c84040c2d200404a0041c03220300c09091040d028082c008600002d01591039144c1d840c1058541800705000d25000ca01c9030b440481d0a40810003046005c8036016512900d80070002980f03401a50301c807180c20789000c1e44814000c107665480c0d102d24100703090042c1348107030b81da5440c1c418403055541d6072003c60340e00f60041c400d83c1107030709a840056601942c07091800034402504d00d80004c0c441c500c604c03c3c54041c032000c100030501d1100c0500810584002a240a000039225a411410740743c0500510300103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 392141330 1250 392140080 392140093
    0x105010207030b04050a0c12060c020c010206011403030f0d24050604030204020c150c090f061204120c05060405060402010822110604030206071104050708090703110609100f021905 79
    0x49000d200703501c4e4000d403048003a51040760b800c0d200d0f6404c40c1443d81000e1a0700034004501c00404c859485130300401006030020b8200d11012400103515190140724001e0480d8058641d04825642441110740318581410803980398901c010100300146500a9103140240340720740c24910700940424484110361008044901d424195030900010f50018007903404d95210b4007504010811030000c0711403103400b94041103601ea9108204000702203100840c032074040d04040005100c0841d94121060b4460341020702041d54020001c001c070344100b00000f000d07000b40690418041040004998079004078000da90b041c0850703e8500850712003c4100c0428402d09007003645c1c1100060711245404102c02001301803d0a140d80d90300030a4a0781d00c0450200c401c0c43c100f06140c41c0314134244c881c0c0c41c0c020301d07285000c0d03880d031400100c444da40f130440f0301014141403000e128086007a41e80600b15031100201a0503660501d0118801408a940c0303611848094080e03103200201c0d4440c000d01050f00c040e0484020701c1c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 392142580 1250 392141330 392141333
    0xb120c0720010c050f0c0415061b030c05030a090906050a050603040303050601020c060c03041d160309020f060c0109050d0503071d0607020612090d0203070c0e0a0b091311030303010501020703 84
    0x700c591a80d010354140003000c602c44010030410f2143e14540c0070090701600b4541003490810086407603501c03400411010030f100034403040e5403060301c4102c0700c2c2d0f0400b001b242104c1c3d1404c0603102c0c510508801002c0b0b10000859100c2103900c9000ba1080f2000c901e01030140c540c6907820802d03404158028940c20040038000500803a1003508a01d40044c01801625000b807074120205500e42e000d118840f01c1d13039000280130030245100701c0c10030000e103c0e10304400303080703041c11140f180c1c207041101e110504164448401a09540d43d0b42e852103a106001004960707a40805c44180d03010f002e0840c030a580328043e500b00220154010000c507480303003c0b43e640d505184903009181458036403800d60810342008081c000d000c0142c880324002c200155202111407168501113545074942801c1c1c0d1a134500b150030602400000990b000c0c02c9001340c03074600c5c590044903a202e0300300d80010301d000c0c003450358042102c00a0050308400c80c60a02c2c401130103503c100140740c0b0302c01c0c24542c1c1ca120030b104050059000100800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 392143830 1250 392142580 392142623
    0x3040305070c090c03020a1101050f0424020a0306090c020a151814012703020d050306130c030b030c01030612030305061315051008070905011107030b010b120c07 71
    0x1d4a4032400010781480d032100480c804031003800e1500b03408a5030010b80c04000a8024000b151920761a000900640c07512009140001401420081c89035042607840c419480d51414a189101301810045441d808a010004c01500c0703035120b4260420b00c0c000d4070404151000c00c060101c1a08004210740411714808600b008002030500609043c00320070380140001e02000024460030300071000410400f84a07940409680e204146144694259081d0800000d4000c50300c101100403900b001501c135a2032401050408040700d0756510345510f0f0070303004c5140780d40503813050b01a8141901150510340e22540150201d83d6107004182c1008860342418000034401e4102c903074000c001070031400d02d92401283c1241601e424080030760b085c03155014184454240700c0c1403640c41c682c803450007101d01c1c140414050324015150191504100c62440f8021019108100400065900100c1004c0c02c1da980c0303006141a0701310410006c075000e0300c00c011070a01c03040003040c0c032980342d0089002d007054481c0c5c00e90748 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 392145080 1250 392143830 392143837
    0x80a0203070501050a0e0705031c050310031505010603110708070204020c010920090a110702040c0e0a08061005030a02130203040611040323012702030f0102130f0509070503040305 79
    0x1148810403650300020800e004140c0103480151012030b042c618084103a01f03000168000c5806940215103c2521030314240003034134000c40c2402c01595a4550200003280e52034075800141220350448240080c40446a00540c1203810313554040180220300c001403c001c0c49500800350040906004903000743c40d0942c0140041012030f80002004000da9076605c003030300c40c000c00005080b500707400c1c8045a42405440c0c960700c4450000104183c0e1509014a1003074051420041d0082d55108003c0011600800c090b10359070740000e002555840d521042103540f0201101c0d004a001032181001406080000b03124240c0d6134001c09043c5100061047e4034000d4200038000e032160380c2c0350400c0b00a5285144024800395010301c5100340d540c245006400300142d000d100c8520305a146c07211700785000e0008444410030300a41000e016005449000092401d0400c0c190301005501c00074090706c00324518030b0340008a40c0901d812213000c0d0341d203408114501e64102c2d400b40206600301b00040003c2d1040004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 392146330 1250 392145080 392145097
    0x70612060503070b19030506090a0504030311030a060302041802010f08090304150903121e0c1502030f040b0106110718150807060e0a05030a030305040201110f070f0b1608 75
    0x15103580c1d00d1000074940950f079802040c004900182040520105c0c20071030301c5000c0503050038045820700c1c401040441d040242586002a9107002050402d4440e4016102040201140d26100d061404284009210340d00c800ca110310700d048000d85007030088507001c2e80700c0c1d0b4050311842e072034190004043d1a0040000c000c11721900007000086014891603110b110561a540d81d06282c0604600d400d40c8946a580e21030b00c00c3c003400e51200040c980d4803050f21100b4468528116152040f285400301c0c2081c00041529447e0340044108420f0448080000d4400c5014662400883e6039440b01580d001c0300c0074403a903d040d04142000c0c00284100000300108020140000625a01e41059014008200d40080381150010481002465444501d00c074960750300311014180d680c07928001070342e034120007a001401d040e210f2000800350ba00a0b41100140e4102c603007620148141000d0141d03c60707038580944109036103525408200c6503400b009844800d14008000b801c019000d85400f0555041200c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 392147580 1250 392146330 392146367
    0x70810120302010f05090f0c060a05040302090903030601031b301e050a060f051504081605010813110909010e010f06050f0111071208090907020d120506030706 70
    0x144400c01510034440d038500960000404c484030790400c03026074601030002d026540c452000c9003007200001c41e080c261680226901640c5282d10041649c5a0150342d2000e5840103142d0200301d05114003000852068800340e81c01c004401c0070000c0380d00b207003294034180800128001c0740e58942140112840c00754458003030110136051810920001940c0d681e080c0c01841001c40305983c408400c03d800352681110322a20705004045c200417990134101c40c2c42c4201480703429403009000078624250104e9000e40400c0d01a9a8230030061214200529118819940007907022400588041c0b110350b00d40b0f060700c0d40500342c649500c000b4020000b400c803001c0c2400607a55665200e502d103c03030007445514101491600301041192404080000100a0301c85150503c4070201c03441c45904d00208003002900d440804080758031040d8188035409002d640f50880d00407a804090024440e00060040051004c607039070b0401e21034030b40344010706945080d10f545425074854041480350500034160a122508642c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 392148830 1250 392147580 392147611
    0x160602010624031b0f020c010e03030a030b1201110a09050a0f0905070e10030e060f07020d0f02010204080604030c0204181707020315011d010803041a07060216060e070911030708 78
    0x144400105807880813000e0210b405001010702c5c00d030f010301c00c555150809085c9050700300c1c07201010a490388a032196030010140d40e1040b043c0169258060101c1408402c0300800120214158043c450390244495101107000140001070510b80400c0e10803d84040720302044030305140c81851409050042d111009219211810034080d40700d038441541c3c0030600b030b41c011035480f400d00c50407402c103800544014203100590041001e0250000f41c1c11402c8412407822143d41040c90703004900a018a0300b1030750160003910244024142d0110380308050740d001b12001c0001c0f03002d01f00d405841f480380a0b4000c3c584054a03100a12018151000c1d2401a0003e420343d040c00f02c140351800b034820003d81000e01c0741440d0007005030280300108180b90240114100071407815050000c01e642000720b1400c262034010000808604000d000c0c0c041c0d81068200d51007030300040b00e0514144026040e180c074403d080e84140c11001134141d8080c0038080c80207200340d011901e9900d8184080b02e080a004041d26200840d09 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 392150080 1250 392148830 392148851
    0x50307060c050c090901060f0828051903020d12090b012714221713091805011b050306152b14010503060612120c16060201062403 57
    0x241d1a0a10411782e51000040050800500a40305a0f15800080e40c945c0035248107810410149030341140c11a00d02e540c0c80104509140c11440d10203015140c20003901d5a5004030101074000401c00c01d01e107115115008448011124401100c02e503007406041544108010002d41809603844041d5143c0d20070700b590307901e49003c1002c041c2e905a5a0070350b29600c4000030004035a8010004011100081841c03000200f11501c944880700d4088640071110600001d003801810308402080c40200400c0303074203204000949007013150120354840240e800707508111000040100189088821900c0ca071619400d6031564414001248800c80c410701e20000100300c9010120241d070f004804204400000c0203440350030032101c1060300c56044180104505000041c411682e012400c02d90000060311001c00e4403c10b00e00c82441c0410000020861480000c0e881c2041d080100c3d0306990780c0d0b01c128111524980e5a83c040f402c0316114480c0d075540040100310003c0a85030100c0600702058189800705644100c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 392151330 1250 392150080 392150089
    0x2150702030c03040e10050a0e160c0f030c2114031f0803040618030803070e0301060302040c0c02031e03071e0506010e0612060f070f020f100203040b0a0501050307060c050c 76
    0x20740200a0344003545d010082000200720180307002d000c050321800110b51515099082c80301010b0181507440403000707101d0ba0340f030f803050600728030a0703411042c0340007045018100a0803010406400380c030940c8402c002d01c04565107145503a021002d00307030750f10607400b02c1035140001c0c0c58001901070308801803125943c84022100118181c003034401140a10b990b685041c0b405004003101504d144200c0a9040c0100045000c04041d2584990103040c0790005031905c000180c01801d03e40c0000703600600d40201040c0007076000c040940c0c854420780845500e8118100c441c1001150303943d20f003503240e004104140008801c200341c1e489074a1100c659445d104910307510103040400980141c0c1d00d405822040019034604081c02ca41d035050140068403560400300000c000140004241006001808880d404290b01c00c000062803546d1040540d000d4001c105050b0019600c00e8800781d40072914000401c80c038204070701c500d904899004009000040c54114262919005030308141c0d841d004001d2220340c240c48 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 392152580 1250 392151330 392151337
    0x409020303040b1b19020105070b06010509040906051504181103030708040b0a030c03020306090103330e010516050a0c11130603030912030e1504150905040c080702150702030c03 78
    0xa1541d50200f000302082c1c070b41441d002c0e81d1560009170308480c0c011000540d0b0440216003141d0b030001031000d07d41e40c540d80181d880d80b2600d005140c0003460800701c0c10622005600590107008503c00d0040c080081c5010407080d03945039000c2943c240b48001114001580e4103d055051043c05402da0b4213007101c070749030091550401e5100b46075400e400070f040600c5c01c0d45440f41d0194620141021401e50400c1e6012480a240500009125251180451040e08004c41c02c40720310100d0054040c010100240b50a0043c000c44c000c010f80c59030a00004c602ca07101c09018080800302695901400c010300301c03008842d502003103d000d48110000c1c590904503a280d0711900d001402d152240451120b14600d401041f11440c1e80c400d0340c4142900c0c40500001c1c1d4006c501c130a849004480e1100c3e542a0150035480030b22580c2d015000c08020442a1401d20740c00a6140c2c08a0b90f0440d4100800340710242c00b0313180014103c4e01d20700140c01c0010309071141c0c10f02001c0160000300c03c1c4112800c082413810620b14603072 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 392153830 1250 392152580 392152597
    0x3060103090f05070509060409111002010b03121e0a14180a1409100609032405070c0c050f0f010c03090b030711010b03010b15070302011107060501060f080606090409020303040b 78
    0x1c0048038117020900304441d455800403800ea604105100e010b403605240c1d1841401500d104809210480807004c2c400d401c4031500120080540c3d16681c024000c03d0301550100101030745804206585400020350002654208a032075190f83ea8031890b40709100c1419400468004013402d03900200c60328545030ba1101c08040c180d0000481542c070200b03410441c001030024081482451644424044546e000100d007045981c801d18105250380400304440c1c21018060001201e2483c202c03c100c50309030322584049170180a04030000029803904c0a0101d144080c000c61a00801c100d08030310f98551090300203020107406450017005032a01c800c2e1250141e8025508000000d0010b0460107401c40b00303100d03240490004800800c000e0410301c007c901c04030036412400d1081c0002003680803d042c000c0d0454084207810509071961a140c62512200030030083c081c5100040380680340006040c090450742e07000b40030040c2024240104d10081101070494920101c1e09800140070001b0a021003101030680503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 392155080 1250 392153830 392153833
    0x19030903030b0306151003021c0203042010080a0e0709020901091e030b091609060611060f010302060d09080310030302010e031c020d060b1206010e0a03020f0603060103090f05 77
    0x86080050948814054891094000005016040380c1001c9664a207940a403103002ca202da800c1030a6000b0301404d0609000110007005600007031a9030b038002c603c101d119035070007008400745521007184014400141e503003000b66900034920441c002c80f2450380c840311081c001304000101c0d80c0014100046903210410054000c10890100d40c0c1141110000c0e022581e00d00b104e010903070004050b60105884041c24000001001ca03040041c2030122300101c86e180b03a07944d0403040d92030403400c008010510501c000181100d1100615201c081034240c09006540d001c080740341d0a5800f0410194030102d10340c0ca4550359a40720200003010340c40954030880b810030104103a40e10310309019095440352401c4800e81c0c2c1042101c0c1c41308645d0008001e01e050b41060005846801c90080da00003004990061000054003003803034103c00b5000d1104510035402a40d44550031003407030b424400104500d00000398030210701d01d4a06a5810207001540d4040c105140105100c40b040e100c4242e10001c2004c251100d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 392156330 1250 392155080 392155091
    0x313020d0213140a151505041d0703060b030106020318010e10090f080f0a030c05070512030d0c18030803040c0e0f09190803040b04030e060415020705060901090612021903 75
    0x15140303e0020340e9000741c10b10003d00024502446002040786a4026040e07100601c043c8009610b20550070381e000340128000c41e40a8100e00c08210001c00c0045622200207420315001160000030072003928100c5034590010740c00c1101000141d00b44801440344981006260b480f80b58413940c0d0036001c0c01021030380f520703004c2c0841c1c101546503041110030f03000885036a01900c411120080002000042207400d454011640c3c8198544103080c1051760344060790240e139071034040c08401030120041520070f4039201e0402040d070141d5030a5039a45a106003d044002d0700c5c0c1000c00c045012280190b501910603d90800d91940360710070030f541081c09462030f00300c0d90f100c8020480410f0301000045002550070744800041241551192102e2100400040c00710748004046010503009141d00205050010f1a0031713151501c511128030007850b0044080300500c00da1100282c00e0800c401142e91154040e0354110066080c100309130766078840350320852441c42d0701b0400102100c3d58207002d01400251540c01146 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 392157580 1250 392156330 392156351
    0x10e0d05090a08010c090e1003051506030115080c010c0507120302030a09080c090402060a0c050a06020a03060b04051509010c080a18050108090c040e120c060f1003080313020d0213 79
    0x1035100343c0e002090345a1601c00034218091308a03940a007240d0650300c0903860b0750340e40c1c100c428514040f17900041251096840140140880101c40ca200f84030036030007000420310303814008400c0ca03028418411183c0200c3c081801a5200f010700307000281c05042120036580d5204038a1100150149041d0016040804c0d011051644141c0c808010324245005018540b246000115608005000207210304400070300c02c0da40a005400742c10035241c0010aa9403246a14108000690310180000c2c1c002450301c0d601090180c0d00c02d00303990070365001908800704c20340c0407113544e40154000484181408505002c0070006900f00000f8880c44000c0d80d81c07410081031911003c02e030401182c1105042c44030780c0c01004500d003400035401505200403a8082400700c50020030b203051416028000450b99800600c80c04075000000d0958000c06041001c2200c0782da41601d01c400c00e000340d0000500070070081000c5040c150090001d440c820340000c0c0106030f040c15a90000c1d80920b00c01195010503911644a00d5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 392158830 1250 392157580 392157589
    0x4020c010917071b06050f1b0a0614100339090f1404081204030e0604080105040b07030519051906060f020105090f0c130902100804050c0616080c010e0d0509 69
    0x3030042c03880140c00c0c10350074141785000c2c02e82d01030780580940040300420a82c407088035500d840b40780d2003010802da038680071a41c00e1500c058006c0c198400e00c11005203001c6010f4005503503d14040300e4018142c000040401364180c01701e910242d080307522898104002d441e100341001035040080030381c0d8000113440c40031003a50000380d814030b54401d03400c101c2500400001c0b0f00c01c2c200701d5031860555640100940d9503842d003900d8002d5410805900074a010070701084424055020601641c000d0f5030038569540c032020b086007603900c2102c1c2046d42c0304089104074030091090700321076002110381d84c824182a2080001a0850346542d100d08001000c8070845110300f5020311425421003440f1014008070000201080c0d070390812400154003072003100c0004d600c040200e52002514a500404000c040e0714116030040c4403000a84096506d4042c8110818541c58220222555008600c014001800c0e02d5101c903001508046211035087d500c0d81c0880c0c40c1d0160078068004500c4607511280d860394070a50a21 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 392160080 1250 392158830 392158853
    0x1311041203031404020108040f05150c21060a031b09050708041101020d0f0e01050d0e01020307020706110606060903011401030501150b0c1e0a0506190b100e04020c01091707 76
    0x40d049560f40c101408050b07644034511076030043c0c2101c0c07c0345944203e031802078505007a252011207040c0780c80b4280040f4800e5203004000c24142460030105034a0b003802c440901940a41e040c642c001070741c07a41040000c41003822138a1114203110358428582c0e84a40c900e080c2d51b0103d8500340021015000c010410660740c4038680a6082031005011a81d003200e000b6112801d04010300003440100c204100d40f90388140c040302d0024210a5091101e28503000e100c80c081c1d00141c403102c001d801019404640c8034460840c103140c40030520028299a00c81c1e8042c44040da0001d284c0d2501035480344070303031412017001c44245030085100d1000080c040c582051424000c45040e080012440320070410f00e10703d180c000840720f0101e20812100500480088180c5152501c0d00300000c280f4081d038020000f2004070000c000001e144003400501448441c00100058102448486000315035030043d0200d5608182d400703031008220360000007815035182d468070300304a00c3c3e01d540a0002000011520100610f0b888003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 392161330 1250 392160080 392160101
    0xc12030d0525030e060a0b030f0a0c031e03020c190915050a09020c060a0b0111060702061906080d081f030506061504060206040f0804090e060a1415131104120303 71
    0x40210054201e403098031780701c0183c0403806084d221010148503540501c580c0d03c80042110490302203168030702e05081c2e43d16083c4001e43d16151203070342030004041010524424141c0c19805024a00700c5c2808010b505100c103464001c0280c60007101086022161044008280801c142a40b00b940340204111038100907030480590b003030040c88520103490000824940003c3c80000203d44165004012580718900c01e081d0002c9128580034402110707000704074a030156007403c092445480030303007001505903101c43c400c01d03040e680201804140c0512401d212034000141c0b04115204030071200f00582d40341e103150019146e940003242440b141c0d251078070b64054a044a00541800d00740307072074406500c40000500150540e0360246141c070030070000000302c030040c00300d007042000041003081845d581c48000b261206641071404440c0d006c02a20880e078103200b080029202d5241c2c403c540b0500c0488000d045200c441d66850340c084030000d03203003034016002134460f40010301e07014009820010141d03031401c8807 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 392162580 1250 392161330 392161337
    0x30414120a021b060a0c2009041a160906230a0201020a0314130312020d0213213306060806150403030503060f06071407090e06090c12030d0525 63
    0x1050000941294206010503000207c1070304803800404d035401d1020010004591100180c802c02c410410b541c0311040f9540d0b0300303821120050b600c01606001c0c000d544909500803907440f1204000091040c4903201941e208820a007101e00c420b8020207405400004281001d42d402203480c200e860b5040c812a80f400c0559807100c651410310308544021a50208000f03001c010a130002c07001f814001d030b0100c4484103004507046680b074001e660b0005543d6031600601c019844409020064019038001000d9001e4010307079106031006500b8007100723a00507540480400407000390aa0100340c0c0c0b051245400074000747e10707004841d141c01030030080419840d440181c11244184810302c0841d80c0304041da644800181c42e0260300c0140c400010b40680203550300100a0800c811001c0a841c1000c520b0340120b500072130b0203000580102d408207032500421a030406103584166021700365480d103407100071034044050060b40c0c0f03080b07440305818050321812100e050658115006070a8090380040035690122128030b03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 392163830 1250 392162580 392162587
    0x140a030f110a0c09020a09121a09010903020d0f1101061518030b061c05030c07030b0606121f180203090d031b0305060609030d0c0b011505030414120a021b06 69
    0x1603c1e44856800d50007500a0103902241c014005030040042c0c1000c0d048244500700080c2081c548000a0402c2c00c0044081e0b400c031001142180505000380e618580d07041e006000000d034402c4048550700000044241082100004c0c490918001e201c0c64002e0300c103841c1442010101540023500c1c02d01c90456a41c0076585215007080412941454190400001ca4603414041c1c080c240a40e848204080d01803c58000000e0340d10208500003080000c4a200c1c49600130a80d481600300641800b4100031092090700d4000001c0c0150001c4806400501da203541a60f40346882c0e400c4c1c030704c0c1480144001100c0075400003d02801c4241041401c1340b07641c180c6401d0103408014950401110350003038154042c140c5031008034503203540300b1007a10300030300001e000c0b5601c06810f900020f0400110130025644541080c0010032142c100d512404420001a100c2c2e510b0740e141c1d55109428081031091038030584c001c030501c2c50580c00c0104010401e01e082940102808210303094048411440300711210710841080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 392165080 1250 392163830 392163833
    0x3020105030406020f0d02160203070501051608090d050303090a0b10031101051309110d0b0409030c0803040507031a0a0c0305010602060601110a02040906140f011a0304140a030f110a 80
    0x140490b640290b228802517111848600c04403100d004940d0503000c0540080f840c1c16121045403200e0f040113008400b244c4035283c1c3c640040d9014416980042c40140119001802290b4000e00914190001038071000380710a10b602d81d50f0650704155121210f64011383da002040c4009181c4086c0c011080c2025200c0300b5241d41d6580640e01c0d20b141540e41840307804030b4615410281c0b03008074030003040c8064081c00715401c000c16501044e070003014188a541d25000c41003003035042502c915a4481d40c540c903941c5440b0071a0311454000c0d080200100c41e82c0c49000303004000201d0007200b50030301000b4031f40032141c941404950f200c00e07108400011810145031900400c046a800108960002c50030b00b804030071090006041d40c141110b0f036401035001070804a46030104111580418031400c8215880c000945840d0350030107202c6021f1051600c000059050030028040c20402140c00901c1240303207903403462180c03a1361344c20400e0800085c1c1c08a0303580103401c1007564025411030050310000703002d4603100c6c015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 392166330 1250 392165080 392165087
    0x9100531080d08010608090309100f1d0f0f06040911090405060f150c100216111c030806061c05101e1a090310090201020d08010e0f070926011401030201 67
    0x144990001c06c000400801d6032000e05204540540e4409003602421a0340720718050124010741d0701c001e0014040a1110b240c10a520131038901106000b081d0032100108281080f0560901201682d8031580400000480c50f200340701d0b41000d024481503035611101c4400c100070444d80700800543c021700100800c1c004660b40d29000d0785841c10395041c6280c6410030b41c2c07203041c40c0041a100407803002d880000c5403000311701803103600c603030300351155040851600a02003401503aa8118840c01442c10301c0c600c1c560006030040061660140d805801d850074000c2c00c102160102d201c06034800040e584e2002070000c030242440f8148042c1240112181c000407a220144c000004940b203001004001448084040300c2004102c41408a00070b046603980034445c07282a001f0060305800324094030803030007010140d078001c0c509107049410101c0782031180c0d56030403010b1002110040641040003031005012035621a481f40300030400d25820101d0040600e01640c1a003158080c05149540c4a91705004000603a070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 392167580 1250 392166330 392166347
    0x106060819051f0906031202030406020601170a0609110a090b01050a080405030702030a080d0c0816050a0c0209010b13092c0118061b030506030309100531080d 70
    0x41e44040002e00b0b5540c0f90511400c000c10421241c8801000800010207044981000094a0040388890014141d640061f650780c46148600e4015030032003001000380030b61283e00d40e0742064603401036807441d02240c0c4c0d0356000c40302c513070108071200b43c0d43c100c960b01c0c2c50070f005aa40300176000e9220108905001d19001030001d014100c854010040580002402c004082c000d50303200719406400c5038004c0880f441c00400581014600c1c811b0740786800d00d07100401d8403c542d2503008203111104d5044800c141e8504640c584d00204c0c038502808150019100141c82e540241070003047c10100341ca4640d10741c520b4412110205600c400e46d518200720341400d1050b4400d1801c00c0c10f40fa205012681c803030403c01824058000310110b01241400261070340c0a0100580258031460000d600e41c105004180c00c003a4111501502c036190164024005281c40f0f0800c80215060745009050160601c01075111070951809880d440051440d00d9112a0b612142c0d0001441d000e40f41800c00791059280a84005002c2c54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 392168830 1250 392167580 392167621
    0x3062a030c120c0905040903030c17010e01060c1b0e010801060f030206090402031909051b030105070e1003110f07060b0a06050f03270c1c0b04080d0605060408060901060608 76
    0x20b83c0d90282d0350392a03000d090312600602000d001803100a240303081c0503006100c598680c3d80031503020111440b814540c07285140c141d40c425501021240d08000d0202c80c005001d4504480e90b00d031160405200d00740c108109002454050079404640d0b042049290946985a00c400e42c020f0b5010360a00c01a074450701038404002065500586035038941c0610080181e40c20008143c09142864443c24410045803a00003500000b07402030034104d2490502d422a0030840740710300001c10f0301c403400e0120301c0d208103d210265020310f00401c1e40244446480200d0740040c8040780c54210004050041004600074001c00d0360003210010313842e038038041000c1c0462059030703031840a0107400400a403100d0a61401c0b607900000c43c10761740c0f032018442d030381a42e0f480305540804c1d8403030b5848152008411852102d4200c100340e00c860390102685441c2c0d10000307560021401d1801c85501c1c0d400102d107588994010340f00030014030f4014a410300b0011540d5003100c0711500007404103c0ca08040103081046081c00101c0301c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 392170080 1250 392168830 392168867
    0xc030d0902150f0a09171009020103061e03170c061801061a03040b061f030f0b060304030c030e0a0302010c032102030a0903020705030604260403062a030c 68
    0xc062510018101c07080700400120b018602143e04002e024405011301040c0071a902e0354400d8544a070b90006403180d00740f4000046500c000c50100381000c842d080380400900c107040c00700b0302c01d46404244400c071841c1000da44401302010010001c0c4002c0d181007010019480c04180c0c50000510f402603240c110040039200001c0300d6041402d0200e60950145004080015800022500700e854102d21a0f00641c0c0c2580c01c3e0745001302280301761500c280c1460403c1c0000881c42124903901805402400b01c1060000900ea40d40300000d07840d86808005501c030307070712980d01c44840c80194a0083d1010010b2443c2e607000b40710709402400140d811405034107009400d070800c03c2c1e01c1070200d50341c0480c1401030b41d10100d21500100a00c05000c01d19000012650701c00d400756441252908249a40c4410460b8040c20722a95129406645410031034030501d00d4244401c6507203001c0d00c0783c036000c05031900d0f07401289029050044100c45045968407803040300030b484c60240708200318071000030945802c10002c482072 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 392171330 1250 392170080 392170091
    0x21902030d080414030d0b040e01270807050a230714061c0603210507081219050405070f081c0f02010b0a0f0f0509010f030f11060d0b030d02030c030d 66
    0xd20581c3c60f0240303400811a8212540c0d111054840001f03802d070380071040d0140d03040107444d401d00030040c06851602652555000810409484e07800b004100d000c100340d60204c420000d65001c11014044008014017580010102d540040740e11712100844491030070b442c3d08120428058094030b00317582c40d0170380c4003216066101c4190605500c1400300d000c149031022031030310714004104101051203106401050608083c080c0c91080107848501c078181c801842e000080060800302080240c8035a004501070f40950144030a00e00644115541910143d5407944000e0040040728418580c100107054220040c1510002600140c0b00c0040070700078502c1841909036410101078401d40c00b1a005140003402c00e01841d58400300b010300c4d000395008004404500840100311424506151030494083c481010a02d03851521024400e24940d00203d800a40b49020f8a89650b10203014180003410084001041c06c4030304c080501c0c1c03024410505007076420510865995035404025209029042940800e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 392172580 1250 392171330 392171333
    0x408030a02040909030e0a08030c0712110a030b09100209031f110406050d060503070b04090c090f030b060f030105090d03090c0504020708030a060501052b090503030c0a021902030d0804 81
    0x790080340c208640141c600794010007030580c420030351400060103403035841046446413541e5407a03100301e070000c2c80075500071001040780ca403007210100e214900459103070310310303c580e04000b6512030610703842580c0c502503210170320078800d0382030043c540d000305228400c602d40480703800840e403a1180210300c244201e28084003540580d99507008001010744054446c1e81ea41d072103401c00b904540208030a42e034414075050000c50076040000303a000507100600c40550801e0725095090b001740100c1030440301007000650002131003c01d8040620080d6100e6030604405140c103d090140d1031000c80310061213030f810320091103070700013000c643c400411080c7c1c030380801c0000302c6060160110f5240e80c0202c0d0070520000300f000c20f00100a000c1c50048076400002d02c80155103e004445074024540700c401c07000540c1041d4640701d122041c0e40700b481c0050180125800d2402d841d86400c6400440c2c0110750701e4000540328400c1541840110302d010b40400b1940c50031111500440e0342c07841a43c00d14001e02c41c12402140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 392173830 1250 392172580 392172601
    0x10804020d0203070b03190e0610050d030e040f06050321180409080307030c08150108240310020406030c1d10170112020a0509091f0b040203090d1e08040803 69
    0x40c00380c405c034001241c1e82e0070010443c42c203070000c80800412903460849500055500851500d01803400700e500408000d081404005161f40c0b5440100d0500249980b80c1503182c0701c81c003403101840a586400211145040d00b454285003e040d01041c1502070b130b08259002e8000340f42a540c0703106c00b026540034001d91510100e030080150b0b1030042d1070328102000300300c2041e50540080c071810f82c1e1596881c1160322290f0700b182c8583d003008845804600100001a0007400808612540040000e0ba1003200c06a10003c40d04113040000c00c00d00c0280c0000f4144861034042c095a685004145030a0300086261150160b4000381041c2c3d8520842607d0070641d10381744903030241040650640c80840955070b55822054180111140480c0102007540c0005550706e0318595080c46903160102515484104503194481d4000750a00c138240683d0341d0f0404420390f00c8610103184103004d03000c002d1941d40d42064010700707015040705015860811410803050034543c04809039421960010f04140c0302e843d00c51a50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 392175080 1250 392173830 392173843
    0x4030c0807091d340e06040e070e06010e0109120308070905010507031706040b060c0d0f0507030e0d050f030a1205100326071a1e011a0d060902040b190c02010804020d0203 75
    0x44c031000480c18010400e0051412420b0107048112401c010f089040e0354001d0b05c2c0e050911648640b94405000240254001c10b80342140f503805241c04c1040c1503c0741c40001d07041241c14010b40000d08600204080650010a800050242420501d05100c01135800030940250120701014040d01c01c40451702c1130320303145c02a40c80e400006180c04e403603454901c04550b071214500c10940004000c840ca4802c224041c0c01100d00564041d5036280701a21480c00384051080200b00440b001d00c80c069a52900c0c0f501070019010080c125601c0d003640c900a0113000c3c0c10f56001409801c24100c40c0481000040d090020212221002d01d184000d602c9000c00e005555008698001d44040302c882c0504810002810040d03120b42c00ca03940c03000c044407185800c1c8020300c80034020b0410103011454602410700b82603000d00110400101c2c04900c1c5a2200854002d07a001070380040c26094020880117600c403080c44006040703030003d18100070842c200d900000d0a1640241000c0c1c001c2080741c002030255103052004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 392176330 1250 392175080 392175163
    0x20d0e0a0311100c080a050402030f030d02070c0b0307050421061103041e02100e04020f0a090608010b070b0c0d09050d021e0105040c06030b01020304030c0807091d 72
    0x203694240c091418054030004503809184500e001e41070350998074210300d03c40e2015454869861000581d141da000c00c000b81409070003603902d44918540702056060400042065141c1c0341c0c0b000d078545056260090316030b44990031010301c0e0a000d00400034802e620900352801ca030340e80c0c4080801541c0f1b01c50158100300b200c20000e800542400e6561005418110007180500d00c60f0b0b405d1189100d01d402441f0001d100c28800943c013003100500410b0061282007103001c0340200400041ca04003546880f004154401c54034207009c03d1480b142045400e40000c0d4941c01002c202c0801403525142d039a03401051039005207140060314011541e00f120910540c07090002035171010032500c4a0000b000c0107951000031204421507948007480c1d452200c04103008550145910180000c0d01c203040c02c000b6809040c41c103c0c0281144800c6c040040411141d0203030358000c12800000d02401401c2c00540f00c1518002030751000452040702c080c0c9060540043e0b02031034843d801e000044000c201c020b0307501c424903c1044 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 392177580 1250 392176330 392176333
    0x1704030c02010c14010219020d0c060e10051006031404110d140303100f06020c0109090504030c080a0c05010b040515101214010f050108041205030a060b18012709020d0e 74
    0x340001c0004c0543c01400d109800402007103541030144800c0342d540c211010b103203002850f0350900c0d00010b005500011a040b21000954a03500350203011503088600c00c03100d801d204112041d0070044103406215080440000f4031400310545416190100c412207400c203900d02072521600c5550500c070400c1c80401d41a0728980a884e900d00f84618005091000e5004034400300405c800300140213800010009001ca1040c0c4036040c500d4600f5034440020140200154107010f14410141d0001300c0c020010f00c16504240c5500000781d2440c2086070848a42d064058011460b00051184c21181031107403d0f0f68400440d821503c0703100ca00070444102c3c105c0c0c51954030003400c5c5451488000082d03020141a1080000e02c030a00560340c400469220f070003690302514441c0c900000e903150911440044d036100c0080c010110341c140d03844035001c0c02c3c0d03802142c824000e0700420501c00322079070780944442da01d80581c84d80700040e035190204625a940031803243ea5086d9a0005180300d07d07102c650000000d4045410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 392178830 1250 392177580 392177603
    0x4020a0b07021302070b09070b0301080a03030203180a143706090c14150307090b0f090d03080402011b02100507030207080706050318070e0a2f191704030c02010c 71
    0x703000d20042d01b058410020500603080040b88841c403500907079040301c442000801400c40140c406800a41c0040d1503410940071041c50712000a80030030070445190310500040909408000c103180c04c010f81911096110a2309015203903200c24690b030140c80c8900000500d60810798140b1b0804028603007810002c001ea8000380000504142c40900240840360644100c41c2c80120b0740d054109501c000c0312140003050101c50240261681c1c90064001d000304200100c0c9400314000c001a0842000c030011400105854104003c40d40e104060441c10700030000c8540e110450b030340c0024100103400d40500b00b08003003c0303000d40a0510801020b001040c8001c02e86020944403040280940d100303c51445c40d81c1000d0740242401c6500044100468059806010103925652030042c0a03000c03000050140031812001c110200340d01ea1551002c42100106581c0d46000300078407440d107540341050003014020324031024034452194541c003a5125505107417507003080740d25200695428030f0185010f408a004070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 392180080 1250 392178830 392178833
    0x50603100603150b010e030703030c1b0806010906050418031d040e01230906010b03060105120702010c180f030b09150406020702090115020d030c0519031a03010504020a0b0702130207 80
    0x18809110f1020201814001240c2207001595a0000c0031001a0580c5c0503201c104046881a0704d25134006104000c07031152400f40203006469030b0411b13040350020750001c1c03004008a1215100b20401414150f03002d00c02c2280d01e0010514111031000041c081c00800400c002a1010b48080f00a014030018000c0141c1d2003074949850007440380400c214003485c00c0101030715524030303428000e13440391343e07200010702e4240c1c02c2100408054201038242414000f007804010392840080031001d1140030039500008104200000003020903007007036400011188150018480400c4c040344641c1940d412400c940d0654030fa118009140130400a110b031440001c40f0180010031070030f50014040d40b4004c0350711503502d98075540000f40505070076498002680c0710301850b0300175078040d0f00a0060601c2c2400c04504141c07404983c0c6410001000078880040e40e18a550844e07040301150140c1302440c1075000f08418545076020403203005844c066a07078440408141340003155541c000074044034030001015034461065 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 392181330 1250 392180080 392180093
    0x1030e030c0714041107030c05010b1003050f1b180609040c08070e150306272e06050417030c07062c1c060b030307230304051003050603100603 63
    0x50142c0000204450000c50f0745181034019240c48081009060303141c07030b100d80d40543e24040042012603140d500c40c50a1842c0d0754580c4510310030310860751800315140ca060511100c1c14040105800702c42140942850345807004601568451101c00d1401200d058010300010010b004100c1c1c4107500030304121300e41070100d501002c668054500d41e107032010280400030820461484e42c488528506000348001681485c00c84002d45a4003480380c40002035049000c0400300e54001100c010301b20a0213003000381182c803040300e442c031940403801403602c079600c0c2005002010303032246101b0028600303050170944480103070070300407642990280400c80d05082d44c0c450000e00480c1d10381d1051010907482d48441c254801000d030b0204242c00d0024510014070340750f01c4d42000e610b00e0b5030505075501aa00c040300202c9403010001400c07214054891041c5071940d840303206e107017009100c040700c0c0280c000740010403ca8803044400c451044450402041c40d41d2010003003442c0c1403108905010080c14841c000060004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 392182580 1250 392181330 392181343
    0x103030f09150206041121071508040b0610020f0601060801092304031b02062206020a05120a0e060304120201111810020304030b040804090b090112060b01030e030c 72
    0x40c50300c454000c0c6550301c00000c01850301441180150300b1400000300015000300e83d02c881620014a03818444a02c0c03584800146c4410b15003224607800a00f060111945070310a11280c02c40500d00342e001490a9511607502d150b02030705150203038220000560201d40280300c40020808054110b0794590f81d1004002d207450001c1c4990760080d81342148a00404d10300d01224000d401106296560300d849580d4101c401780c44039010703109600c43c2840428016a501801822100308400030716103405050072848006000913070200d42550300c40340395280040c0f0049400b120548101003080c1e22110803401c2950140120840e440d404100003003000104036101e01c0060044c08954000c008040c81003c0311000d0748548407044004200d042d1003000e207071030402c142d20103030340713543c812349090555a94a43c0e69000b01502c0890b080700e0089814048070780035100b0091912400c6032149265450f064454000c1070201c80003400c8c1580328071756030b03445034042e8010300d14540700704044954a990100300c4a88629 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 392183830 1250 392182580 392182607
    0x90b1210092c0307020d30020318010201060504020406020303010e22060b0105090a0308130b090d15090602040e091002040e07052109010f0e0714060c010b04020304062c0c15040b03010303 82
    0x429903001f1030501303500e040d4480c054200c150000c3d8038080031800c0350f041c0d00400402460440d0740f2803e000c10113807154009800104078540003107032a5410407071b40e04800340b00100b8284080c101d12810350410b07005441c1d4080d020f600544009013140c1d000740100c2c1c040c404d02800c00e401c035002400c000f003040703080b40c02029070340b104400c1720710160f884410700704040c0300e41c28501d9441000680c980300440c1100d05c034940d00110b02e800005651120359955000e03a00b040d4004600600c8040400010340000d00c00000d1103900080210314050403c0c26142000e0b002503d01410000e012554400e4180001c126600c059100d03080c4104a260100e03405010304903052842001c141400703946d450b1418001403c9058803410306140703043c0790240c0144052500310020303160040d900c034a01110b503522184015070080d40507180c0401d54a0301c2e0303e01200340308421041c41c40c680b02016102c0104000c0840e500c2c3c00020102c0340010005a003079880b00640c011904104c03544c4000100010030150045080345440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 392185080 1250 392183830 392183873
    0x110a030b0f090d023f09150306030706030b130e030309010b010806060d090812091005010506070b041401060302060f13060516080a090b1210092c0307020d 68
    0x40c1c1d509402c00b80c944040c46000d0015070701140c1281c900c440c01040b8107080c4c0038483e68565202c1c0c00d0105600c490521032030540a0190000f07280800d07414003500300080d5014001c14a45141002004256503144a01c60b0204241d0f8492103001180d0720350b600c9501010780309400384000c40c54501101e443c0d51043e100c004003580f034035601c82c1c00d0b5402004400d00c522001000c0c903003072000500255019060302002281c55030001c22580d410100c0b140c0d00b850055510200400c1d50b00800f4030920212107040e003003a4402d41051100340700089440d004142e101d0f51182c0c03415039003018200703524050f0031030b40c1000394810310120f005400060004040c1c610352036404075002104d50341d203130103450501c202c0118444007501d9000101c0400c0b0404028010f20131a860450b01315527039249100000d0300040c15000c1400452404e001d071001580303030b541005d020144010007501c5c50311400080d40b010703408603c140703006d8401011110070f0f205006441085030054408024510b9514068400c00400314020088 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 392186330 1250 392185080 392185111
    0x2150a02011416020606040f06030506090703050d0e03060402130b0a06031a0901030b0705031e0109020c100608070e1f0803070506130809040b0d05011b1b05070e04110a030b 76
    0xd071001d0005900043c0c0d8a4003e40707040e0320f9002c18070025004400306001c0da00e44441d40040001e008000742c902c1204000c000d01281415031802134148800d031000d5100300882094040300b19500803541580050f070454010140036402c10141d0301610502a07071703503400301041c000081d40c0381e00354011919040c50400c041b41a00d49030802c200317079494280400f8104c3e62071000041d41590140c070055400039503c004040800701d80220245c0044002d800c80d00c400340e001310390140c9200c801c108a08807480c21420920002d801d2030f1240d81d540c0824410010380445210100d004000b01400c10b80d200881c66001c25040d5407a0500c0741d0356584211412250780c461600050006205e00034a0704060750700841580c900711000e42000040e29825072070990018515002d4000034100344200b03400741c541000d01c80003030341b00e090014102c041105090b4540c001c1d50440d440000381c01181030029500c0716015000691540c0c180711031101c058200458100804c00b40200501188110030380c421030752107030124003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 392187580 1250 392186330 392186341
    0x3e041517010e12120a0207020d03120f0c140a0504090510030318030c0e0402040e1b010905060f030a02030702030d020403063309050c0c070f060e03061005090402150a020114 76
    0x182d904120030b0f882c0c80c041090140c0000c1c1c0d580207800d950011481100507041c500c00e038000950b0000d98020440105691500091208200b801812508242030404100018103010302908141d058403010485d154001092a1300f075000724290f0300686a000d5041007140380c00700401d80c5000e5507010a07400326048803019410300c007000069034103880e40948031403036075854801c0d0980b1541380a40101e900585951685d0700315801000f2048041c61075003904000c9012210014040b0005500024000c1101704140d416503c0c0320812a40c0061000c040141e680c1e42e00c0008900710301850300d1131315103580001400000e00510b40c0003030b0380a800d891200310142402140040c00c07032805485038500d000d600c0d0f0f406c0140080e517501c05680300400d101030500d040c6004510b1340c10042241c02c4587d102c1e0344803109004c00c80e031190300300f003401c401a0000c140314285180a00c41602240c8501803041c40d0050001d030464441d0501c0ca1061804140318944030391205a011340a0450903100007812103890300001e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 392188830 1250 392187580 392187583
    0x40812090a17030a0c2109031209030f0b060301090b0c0a090504020703211508100501090e0613020607060203040305180604051c0f02120a3e041517010e 67
    0x3a4001c800c0c50095207440501c201c2912050070001c020340e1180006e50110401d500300e180000030180213a51901c02690031803500125100c084229007040000d201e01c00d0002030f102d0804c800f000b541108040a465a401d4006809040f00396802001211101c092281a00c244005080d120313000307803208201d482d10b6000740002c0b40181040680001e21072810140c1d4148414404501c20f03201103400305442c04420b2048052090a51009915610201c05402c421b030b03043c0705182c05071645e0700c4c2c02d1164031003011405503200005065503000400091006045650704401c507501d40d60b02c0340c01991240303001d00f400380154002d1070920700c40441e41c81c0f8448841c42d2500846054820040c0107071800c1700500c00b010040e80c4e4901d812510a114840d40300c0145e92010860109000e00c40020815180a841d001001740c3e501800c15a254611942d0010f6441c0040c1c2c01114482040c0c1c8110854100d210001c0c014001c0c200141d2545c0b008500b003c15203144a074400d0080d01c034400000d00010350b640440c40d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 392190080 1250 392188830 392188859
    0x20304050309121c0e0604350c09090703113c0f10091401110a0c18020f04030210021507030501051008010b031303120203070c03080603030c0a02090606040812090a 72
    0x141c1c000e03002c00c024007000040c4a10014110405023140c420050400411a4402005100b04001f980a890b40e000c0034a000000c150b8000101d07406010540c0c650b56501044186050a192052404e9502c0c1c401c00c503041e800d050780f43c2400c4c42603803901484808400340700392450b4640d98015031400942e4100c0d03003808249914042c0e502d81e587d044451038800072400499005858504104003001c9a034001002004940b914031f0141102070400ca01d84001003520010782d1000c1c40081d030050060340c101409610982e41100d405444c0340e100c0c1e082c0844101e061038085003000c0700258881c2c0a1007040c2d54140d00282c10b0704e40c02c4e070381e904108854180c05c1d6014142403140010345102000040c03050039000144000c410321904045031452401141103007a0780040b2248800103a5030b21600d401d00d680590885e030003003000d8001e1407810206401c05503c03400300350f2029001d40300140200b0880c0e11204105e070014219141900c072100c3d8602c040140c1c55000480c40d46c4140c00107500801c11aa03d080c0c031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 392191330 1250 392190080 392190107
    0x2090c0903060a020a031e0515031c03020702010e210628230a0c0f09050d03140c07060e090f1303080403051306030203070f020f03070204020304050309121c 69
    0x82440b695243c556601951200b582d46040540315042c0486c0e85886030b00c000581c42040301c02280da440e003450250525404844124480d6100d4000e00c090840c802100282d90300443c0780160f1380350301500045c1d40708040040055007014640c000d00d0252400e08240d40c2c1110402010f4406603212a0681d002090720000000e80360840700b00c104800000680c490001c12070303070180e10100038400c1081c0306510b8004503030b0340ca426038841c00541e11031907016488400b0312916040c034440c01401d0034081940082c1070701c030003004d218809000000119000058880d809440000c942c12030b5140e400040540d042003512a01546101d00030450704043d90410510075150759103e18121070254900310b0344131034050001d50034807401700315152040282144110142401c1e480250b5282049900144011485001c3c1400c540040540c03000ca001c0200482c0c40c1a0340480e000368881d1581c3c107200c5d06500c145181d203980a84e40039900c4520a4020940b0303210382600329000c00000e82c00307801c29260310700c00601 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 392192580 1250 392191330 392191333
    0x10504050604090b0a1a0a031b120e0a0c0803040905010f050904031d040f060315060b160201020f10052208040303030e0f0a0804081209030307060207080d0c03060302090c0903 77
    0x20620012001d40d01c00309026034010301d000005566915050101d86c40b408040324032210010311800d6590f09030046040c00d0103405024181c80d6114840205000e50007a25286615101c1ca82021581005c02c002072440e50060200f42403075607a4001c0a40c1d0343e2051040c90441400c1000004411540050010484e0409400c0c03c50a64076a85e0488441c110742403101d00d414452008040107448030b20446002c00c00354040050100d0440c2040c01c00785004003104200241000320034420402e0380d1f800d840a1039007241050fa04e808181c40140c1c20300655101110042c45230414100e10441141c000c1401540d0540c1c00b2101c801d0312075040101c90100400c0500700d0b000c10003003003000034800e0b40202d0240b00340100b550180180c00d86518100b4441e400d01f55a00343c0046024403000f0024860382c400f1500211415117030061010101340c40340222400540000d90101e103d030140803000b000c03990b040047c1d80c02001480c44e07006000c0c000340580d0000b0380c0a09010000102064100001c40d201401d0040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 392193830 1250 392192580 392192587
    0x150114060a050403060609023103022b150b0102030a14030a090609061b0309050619110a030504050c01080411091506181305100e09190602090109050105040506 70
    0x8003442200d40c00007440c207080003010040000422403500c540000b034921810003681c0d0364042014190101d60314581801c130f0405a8001d40f0750010f0344141c4000300c86c0d05036100500700e41405c0b56501c8858040c08091001c400142d400c81c20801d401910700d8445031140c00030001c1d03031069001241d89020351140d03080420650414072500520200195038004900c000204840c0055582c0c1d00030395040c020304841080d00d5440074107400c0a440c800f03200d01d04403840d0800001c051519a41e944e44c00c0501248080f581d0101c46015805080c1c0110041c01425141c09030b80720b1810900a00422040303409031414090000140c0d0190f11540743d00340540d4206d15081d01c40b481d02000c2060714200030b480740400d80c40c41c0b0641c03d01ca4031a000a80400d400e4400c40c22030b18280c16040c00340140b845121980e40b14138003020801185503611031441960144096900d5950301d0b90701240c50101c0d200c0000c8942c4209084250170008140c0084c01c0c0403800fa641c2c022550754510040d6154020390017615403040050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 392195080 1250 392193830 392193869
    0x70902090a05040608030703031413030c02030c0910150503040c06030b0d0506010617060603040c060f0e030712120206190e2404020a0b0712030e0f120c1501 69
    0x680180c000080000d141c40e000d907598000003001c985141c0e000140e11340000c2883c406064040c4265039020b2a01006180315282005081d42031000780c0c40c0080c140f065224240e0150346003004104031078400500402600d0601000e080201c090714450b04400062002550001034400c4c816030b030045a00201d03040c0c0c8241018025005802e1003103445802c80c103103503080e0010076410003849000301125100d0250900450000071081c08000f0169401038408005010008250021300d03011150585440720554070740c580100d49510074100f050390f040c420307441d0100c1c012101d60300441b1030620035000d05c500510b0018081c4d88a032004c03282c01c3d41000b1901030a4030007513082e8210701d9081c15103400381d0306591001421200c204801820540d45503c21000300011400c0c208000c2d005000640c504030b003024059643c1401c7c00700510b07101400c1503101c1580703040001c001c100d031040c0c1058100684030003075100001c0c01c10706d130000812036006118502180f9903107802105454141c84107900755481341c1e000c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 392196330 1250 392195080 392195099
    0x3061e060313050c040606030b0109140d0807020109081b0f01020a02150a12050f1e0108060402190e13020405071b0206132412050601051c020c011406190807 69
    0x1000c005a880d4018004a00c2d1540e03117030300c20000500615100003508031450030004040107466007041a5003407400034a01d0681d641d214501d1002a80490240d907640820f1004842e000c00c1c076440703100180b10785c0b400366130030f0f840c3c01c0041141e10304141d8503a02e4000148004a917518107042d40650403010b0710001c00c1020b500c640040550311310a003000d42c1c40c080400107001c22201c04880052216050300d00340320820052660442071800034050504565040400164450b6800350000b4840e00f4640c40c20501e0003005923400008021032444408a464040c04c1c3c101400703d58402248251300c2c00c40001e80d0540a0b140c880010341e1150701c03d00c00000300d40d0030f201c440d5214040b14260000c540600003113100360600f11040c0203442c022401102001100003510141a000c00886050b00f4007017001090b9030301c81300740d42060307503045c2c0103e4600c450a00032100030300c941502c400742942051816501b5400400c807030f5008a10980e5510020b0300e1080d82c0ba48042c0c0d007030103050500d4000c00d1040007008603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 392197580 1250 392196330 392196361
    0x30320030708060f100e09101a0315090405010f1104060c06151a0a030e0c0105030c09040e060a09050f0705010e090702010e0604031d010906020706050708040b0301030803061e0603 79
    0x10b861130701610000000501e03070400840d4550002107070308442900b5424002c2c0040d40140c1c50b0204500840c1c00c0200e942c28144024588084800010001036110004044500c44070480641019100c1c01c01d03003404d0340a04480c144010300b0a040000740a0994000003c035002c803070036551380600c0d510007561218090409072000d10f002c040118030101d941096200c1a000c1d54009401d01503680714001c2c0d01405440c181201071456800c403401208160760458212076106d0044c2e0003030359840e1800c60008005001880b08450b15200e54810050030001b9a401119641c1c0a13008950b21044c000510981c0d4100500074280084c3c210143c0f800d0034241801415004001e074000414480900958a8a0054103c9098001039202e91020006c0d0b00800c0f000501d852081c07904800f02030421038060365502e098824802000700005600043c09074185c140c0c2d024200f007104480d0b595a49040c285400c1d001603411901c10020080207040c0f10074003800072403d000018000605681c0d50708a00c0c8106170 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 392198830 1250 392197580 392197591
    0x11071401180509130b0901060f050904060219030b010905040e030a0305181c0306050d051c171314061504020702060418091101020c031011071e030320030708 69
    0x8220003070104a40ea1003240280c403481c450211300705040c0700c17800d151068000241105405914162043c4000d541c0d043c1c40c401516810b40707410400e034946280c500d0092158080d08884010300100d50007170035a02d40c020a2038034109994a0032a0b03030310348041004031000c0702d0007003490380c1c400c00c07602010324080d07000030b54044032010519078049c60806116041c44085207031011007003024942000c0e0305401d881200050001a00e586002240703603900e180e99a101c218812400c0401b440c035042040b031191400c2140116041c9804e91033342044840500c4486024904560351034403174808071202e25001a80c2031042c0003040003e01518502011f000081d170181d201aa0080410403004c22400c40030020070480105ea00000940f001c2c0505040d291050581f02040c115080514001b01da55070008140c52000340350f4900065946042c40091650712984400410305041004008005002c1c0301e54219894000e8400340030204110064000310ba00b10b458400d810b07001030021911041c031030300003191f114 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 392200080 1250 392198830 392198867
    0x909020d170909010902040b1b282a09020a030b0607081803011b1815090e090a150504030314090c010e0609100f021f0c11071401 57
    0x500d007034450850008072100340d08624980020440e4160424620b4035005144880b4118249820400040000d1185002000c120504000107000c2c0f0308043c45200030794440210300030314a80445880146001d559035098480080d003002c05401100c40003091450090105a04500941400d00d40c000a4029a449604242d40c6100c20000f03502e0340e9004180403400781c103219482c0d101da034107185145a940c20303015000c2d0341008400d2082c010300801c0c40d007001c0414206407045260411038002000d1103984200c082410f00215082c156400ca00d17401c00352548c2e51417118036503441d00c484580c0c45807200340c005c103d09131483d078000c0e48804550000c0d81161280c0f5002c070f0b40200308032210110450a0302d02100355044600484119038012926080d00003050318164208a050ba00240d250703a00a003d0b8028400c0c40c1c3c030082c0300c2601c01d108210750049410f80001c034282c0190020001084513041c0c100c0403030358980c0078411030700c400900c00040754414041903199806003001143e0500c5103020310345c0314 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 392201330 1250 392200080 392200099
    0x2a0a06050c25080c0d0c090f02070804030308090f070e061e0d0804060e09130605100b1204030e010513090b012003070302070501080405060105061b0f072409090902 72
    0xb100c00d040074020709000a81c040441c41c03814540641d003060440310009104190b00c641d048001819880220120380c12080700013000c0003554146800381c4100b900040100000060100426403c882281e000f00060000c8035900c650301c1031129514011402100010414107000030307082c0c27600d044c1c100c1d4003844490f083c898000c603034000324921090b00d40e0112812100880c0038064194030042070369001508565401050600d00030318001800c4d484809441c031511a00000c10941205004200402c2911002c030ba603100000800c000c02c07441070703c1c102c000800003c49070801d90320500030350320104812801c0041c640c0c541048503000301441c01c012418000a41020a460600003a400418040c80c0001e19500c544030b02d8003d04100c00360304168140000c0c40184402b00b20009101c50644100b03980c603c3e605c040003180f00d80d001801d450b5031401c612032100b03048040e9030041010400c40303041c1c41c051070700c440e0a440c240c0740e0703a85110310380c0740003c8840c602046050340d036410002e007090001d80980744 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 392202580 1250 392201330 392201353
    0x408031f03241113170316030e09010e0603030306040e070f1721040b07080702120a05060a11160206190807020f01020f041203030e0607022a0a06050c 66
    0x1c00c04215444010380b890346492111841c20300e014610100790b58254840c90704440081d91001c2d00560300480c0940b800d40c0d407145405107000c10803244980c001c1c4460403205821860300504056000c1078850054a210340000703090f03407003190114082d140090255045948003c01e00008020440200c00c00344035083c400a04000034041402c0504502c2e42003041000113940c24914080081c8010800348600d00c2e031140380103c0580a550030f440c448082141e4030790150410351070901807000080c0d8002201000d80324000400285004281c0c800c0301958150740d82d001600044501e20019881b41c40d2040040740080c601000d841d41201744000d207a01d0a141e00c002c017020311416441140d4011540480601480d1601081150901e00416000f940b03040507a1000c0c8405004900c10000112185d80c20881014081c0e0800344541c6141d604580c5a85000c1c54029503504910201880c801304540c030f00040c01d50180624003d00f6000f41a82110314900081142e1075440442d8030003c1d80180c2d0509030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 392203830 1250 392202580 392202593
    0x7050d0b0c1e0414090105150910120f0c030507080606090616050d08060a1512050a0f0e01020a031d030f0f0705010905060402010e061812010908030f01030314030408031f03 76
    0x8013808003031100321800360b803030303002d2243d80c00041c0c11a601c980d00740b0308022800d038440421100340135020b91741382480c403540da84151500303a20040000c0d000c1c2d081c500d124550141d0381d8440c4a182d00141d4061202c2e4503822425200490292146078205104010400081c01c101c00200826141500141c0120384141c48550500c03000529000c002003941d8240189460312030042005098215640b031204404030101901040645076030800040d10342c400181d4a0040ba84092054101980c2c144244801e40300b1007030003940121085000302e4a04055509441e900c3c0744048003613a422001580392407503070f900b8003441c0e070000c01c4c1902011900701300140c0040c00a014409255101750001c1100d4101071002410030b07000c50800d18001c038410310a4001c010404018210340c1d2405550100d500000350320740602420f030080000c2d002e20300000602c0010750004580a040b42c0c000c0e071352a04e01c802c80d40c400e9035075403000b5580680510300a00c045500c0340c0400360007032990810302c9001310200380c1d81c1e036a41 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 392205080 1250 392203830 392203837
    0x9020f0c06010902030906010b032514030a0504061a0d0204090203010b0d0b07020106050105160b0702190c080c0303072a090609020c060703061d090a051e07050d0b0c1e 74
    0xc500c1540105c10301c484c040d01080301034017400300c1403022400c0d403520440e10307550302080920801001d10310302d1842c00c1148c01400f4014085c2e92a120096a9162a80c1070902610342583c00f00c481e90b180103103140448400f40b4a90343c2e0340c140145180c40b02103e54003044080c240c00d0760182e0340f41d540c03210340c0c0f40c496443c0d96108582a01c2101c244905d840c007004041d0841e00316074810750602804000011300b83d4108000c03507a98079400903c01c1500d885d0b0f040304900e0a4090000b01107480440d403440b0091040380c140e104212102d200031500211100410f043c0c50b8001c912005080300c013010342038003200d041c0000d5080c9a2114035400c0041c5507036007003410196851580840300580d800520091407800a20103542e22403407905041c482c140c502411414881011030128800e00059008168017020500030070340d01d203070884203c03505000092030708a4202c100880090700c500c0f6a0000160310b08000c081031090383d4000d0281c0615507501c0003841e020741d0182c40068105940c1e91030352010420b151003c2c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 392206330 1250 392205080 392205089
    0x1b020d15180c050306150d05070506130806060613170a020316060f080105060a050c0102070605011e090c050315011b05161202030a03030c021501060c121809020f0c0601 74
    0x5969207090740c10451103040c0389400141c042e80002082104164007103510010312107095440e02c8a040d40c0b400c000d802d000841c2c00481d0321140000b83d030100c40c404855802e007901e00020a64016450391404c0008510444880c0301c1c0b0112000403c0110002c032201c0340e002c500e0000c096030800b031708541c0000c0c200340600c1d5443e82d5000004101303002d400d41c40090340c02084500e05040341d00794108400a9401d00490700450308200c2d001400042c00c10003034064803213141d803020080c0000c0d41c40b00d51800301540c0078240d4400007000e50600044d04d1080d805402006030f201d8441519586451844901b0449100721060501c05202c040c042c20303070820305a402c480d41c040c40240c184030718841034031480305003681d10500401c10081150750159034089005c64410b681401c00140c031a6100c48142d0400303180300540390004400310000910150000405400300b4420b46564072000310721a4255030107412030311048424125034a0a010300ca0741c6600402a219100960504203280205054900f2509801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 392207580 1250 392206330 392206361
    0x207150315080610030b13020901031104110304030f080402060405030a11030601060903080f030402180103080319090f0b18010e0c030f01111e1201030f121b020d15 72
    0x40070825581025068405044810301500d4141813401c80904541d40364000030f003110116101180c50040b010481c08803003030340607106205642e03503402c03e058542081d100ca02d0081d41800d049485540c40001101e10466054584507404085d05030110380510b8000d004a0300003008000118a40d80d0402691302c015210741c25400b02e82000c03005150800c0c0042c3d0085081c041c40c03030814400500d156054480407910551281e88030307503450000401c02d6404017900b004641c034060000c0f0500003000000c610036070140c2009003030210401400c80456014000c00f41115030b41c401e05000251100881c0398001c03a000720320030030442c200403d041c00c4480840c05a07406a01004088400b0300302408080c8500c218400200810040300c06c10b440c1303c0c460581070030303640302900c01c003200d0000d4040203031203503e14241e8a40700c00d51703144e01e04140210b1001c0d0050340c84082c0340e00400c0c6001c0c800d074086203401c00010f0311413817140456400e0014020880d002281d040225000380d008402e140c1c841c1d50717190718001c0c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 392208830 1250 392207580 392207591
    0x3041403092107061b08280c05160e34020a0b0109060303170a0905030409050a05180706050f0403050a0c0302120609030f0c0c0a0f050a080307050604021002071503 72
    0x1034519140c40c889a100f0300074040303070507483c25001701d5403441c5d01142a00805030aa0f02c403605e020100b041c0308685e441140c1c041440b401c4040c51a440490708401074800d40854258401c50f00c00410140350612801501c52030020016480704440c442c1d1034881d4003903400480644010074001841c10111000c1840113030301c400c80704420300000c022024018004d0420400c080c0d81941c80007001580241014180c0c0d00c05030020030f44094803076100d41c0c41640c2200c140c984642c0c403190040040c4c041500d254040300d040002013520b2652a010300118030580f14020107483c2d14041c0c0954a0fa0445031001000d42014040000810000e111800c3e4261096000d00001800d62040002403803469051000c80c2e030088003081745d0040004126a2481d82a20003140c0303507542b092034585055801c04006030000310f110390000e0a50b040c02104820b40740100c0e40740e48000c1d207070024aaa64001c150000d03105e03078082c10115000d030074140380504c130380c1116106071032050391544400f1540305d10301500040040e513160f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 392210080 1250 392208830 392208889
    0x1080c0109090902031b0315190608010c0c031b06051801050705030108061b041d090106080111041404060e01031208150904140c1c05120702060304140309 68
    0x40c04590180000034401c20141c03900b900032940e204c60100080c1c0c0004100c01c09802195001c1001490b0708c428200f081049203804603280105203400c01d4600320f01c6045c12404103540302d040c050700c2003040696480e2810b440d010784040b6017411014540c459296980241c41001c035503903001303007407045540820412410355080800b600711240180050104402480144003002010440c10340105410b1004016001c51700c1840c1c071244215480340c040b105441241100b20310f62154454824070000008115050741c1e282c015081c1e414101140c0284442000140024910a030080304450b1000d400001c80703549a5001d654840380030381082d43d10361808a51501c0d0540c1c0318800a600c045000703501c0c403243c101500032988554019000504900c8004280002c6480c100721804104400030011108685010680c0440241014040d40c09002c0e00c0442000c4880c042d040300c0140303a01030f000914540c2c807600e8400142c404400c010259010400681043d5901e5241045946c0d242c4080d000001030f05 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 392211330 1250 392210080 392210087
    0x703021606031509020f0d020d0e061b0f030a020d0e1b1813060b1e0112110307120b041a032e270305070c080102030c040b0c0c0901080c01 61
    0x41e500281c1010308010080b54003c20044800045031280300d405070f200c0840002c0000f560042425a80e080e5101007840400c0050b150411016424150295143c035254000120020680c003c4c08140b910740803c08030074003907040c000a603800303d1039850041c01c24007103204c0e04d0180c42c07102c00d903040c09600078902c0d4441190030004090700100210f071946c1050b480e00140030b000c000c0040c0703204031800440310100c00f80002500a040164802800c081c0c8411f852018100905481011240020390141428922500610803084000c9100328001d041d0b0b0b81c4c10104640d0002d580d0003d500050700c07041a008152200d002c2d22650b9507094045846000ca20b82c14036140c250068107121906052010002c10800e04e00e244035002003004002041ca5003284032040105005000c0c4161454458035401060507800000360601d94440c0700030b503010301c0d82c03260344500341c0c082514881c030070b0360f4100401c1041e039500b1001803220200080607070b0082c8000400046d07507100242d102010680200400e1800c07580e1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 392212580 1250 392211330 392211373
    0x4061808030d2909010306020a0c051c0e01081510140f030106030c08060d03050c010e0a06090605130c151e020124060e0f01170c0702041b050d050604060902070302 72
    0xd03030783c981d090182501c10015801a00600c8040d00a5500048160741e80d440b48140c8c48101f80c1000072620009064100030130303d080d182030b0000c0001d080d80c80340900c56214074047c500651a80d01c014543c00c40100c1040960280d2407103079800d00950040c00700410094001401800c00c0030148076490390b00d4610090141c504140c10001007091881c100b1015545602404900c42d8051810799100d90710408c000380107003c00c0003008014440c42041c03404000c0b0329003080c01c070301d0310880b42484182c0301e4000468180203101d2000300750700710907003092000c03640e0042805412042407034250001d90f0750b40c14030001d00000a00b1700e40180d44503146429515500118014852000059654414a4450000d160303006826155201c0c540c854000406a807080324100e0300d041c2180411000d90a0601d99580c0702d6022440490280e802c1012503202c51003c8100810075802c17940302ca070b1400303004c80714003401048010989944039a40b008081110342c02440940902c610130b130001c00c0a86244243d000b010701 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 392213830 1250 392212580 392212631
    0x601120c122621011a0c1c03020909040b041b0807090f06080102280c0f0605040203070e0a0207060605120c06030a02040306090c050f040b030304061808030d 69
    0x4400440400024800d01509203100c0c02c0c54901c981501014410101500c11030041940c40c5200d0516662000c901c4a80281202c643d85030102e505100140f00002c81c2c01218010b0540340c00003088491281b01c000901e02c0701101074940180f40c09110800594041c5090b0780a480c2011294200403c0006204c1407004494440e4410907485140c0b031115507a50426005400781d098490448032a405269040180904101c400a43d10b0360303014040103188143d2400d140303403070304030111140e80203a014203424002c00f500719240700e00302502034452002404019000300e0f05845010030000704014181515401080c02580250b40c5a0fa1410302000765076031508000c0c0702e6035805102c11012840058218440c980a07105c254480d940c90f40798500a00881e031020740554241400c500409c803540041200b982c60407685010040d641b8018001100c8901c07020703e07019031003000240b0246000e8040e005040811031242450191200000d50558112100c08501e4a444200d849803a09071000e8112045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 392215080 1250 392213830 392213849
    0x130606030b011e11150702160f0e01061b0c03030e0f01020c090403210c05072a0302040506040e031908011a0a1b0503070b0a061e09020f0702030601120c 67
    0x159482d50000005070f2441943c040c401000111407900c0340500446040410400041100703140c500c2020703442d2942d850404020807000342c00455030981044105d0240c500384007060303015a08044054071288121900000c151a00b0f00c05040010340c42c20300c01026612969504210880f28400e10450410103041c0a040d5040300c81112890380383c04d01069440741c1c051400e01100020344440e02c081c0802d07003040d0002d0a0a0a0606080a410074014540317144560180310002c60910302c440c5825441260703088415079412010030140c501900f002c1c1c2c00007802400000c11503ca403280034a5580b04010702058011400c80305402aa081054039006082c0c0c4000342002650690b035601c600d00c80c503601c4034280080c900381024800d22981c030765040c882d03200046070780c1c5501d82c3c1048404840100c80c4a0f01c0d5908100000c6549040340c0f5030a500e0b01c42000c14941c190342406104070180d00100700c414100d00040c454a00907a60800845000345100b41088038803210500b8288100101900003d000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 392216330 1250 392215080 392215097
    0xb010302070f050c040605030304121b080d09050a1d0402010c080c0a031805040507050a0c050c1201021b16091a0411041a072a24081605030601050a0905130606030b01 73
    0xbc1503451854840201d900900000603a604200e20510380c1182c1d0700b08000c14802c6607608d542468000907144142c6030112548000542c4e681e092480b044008003441141c0c0c4480004a0015406921360f0a1600c0c852244903040030010000e1618003461942c06500084098503075041c0030f81d202d113110010300002c0e00d041c4000d20b800303540900b5a105698803481048140149041030020600c1481c0c08080000c0000c0e10108440e89868040c0d004407008211110b826101344641200010f1084184101d1481a00604e45070054190040a80c0c000c00c0b007050340b1003e45038145694034458882c040a66282440d1075600344030088504400d600d00104400c01c081002101040003548422503122040303802404015001c5e4200880698550001210300c00c0290588000e01a010020030450b24540d2429031381d903100c0188950a0102202100209904101107000f80d4031500041400410b903081c03003903149a80ea00410385024181107008100355842c881885030541c51300552414000901c2d00d01e20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 392217580 1250 392216330 392216339
    0xa110303040309031b0f030b091006050109051201020d2f1e0f091206070f050301030b040813081603112d0f03030d060e060a08030a030b010302070f050c040605030304 73
    0x81d4609800090303e00d00ea201c09105c1324845a464080181004c084c410a80a41d24982102c182034244c850b00c2c0700340a603c00080f45084c6030312a100480d83c0594482d5040c1e8a0401809404085404c2c40c0b000d0f0354007080348910105540c050320302c034807505000f628007052400d00e08a584070441c03a001d16401c02c04000d5121140058800e40d010b6003204071140b070340c802c2d41c0d012244c2030b88a0b0054441e0009008260846582004102980701f64419119400e2000c1c414808440500c000d0100030289210300d40420086140724028020480d115501c3c01d01c800d4403501e200c0d20384a5055601c0c400e43c00e50803c213004000c501c40a0303800c11301e400d0b00c0301d000200300c60320010300c5503031504041e0702c02c11800340010096035540886189480000740580c0d03510300807249454087c10482c010047c4480755000880d0490a0000910b42102c5100001c0d604110025804802402000014504254080c0300110101f41c0c03800c07038983d80341c0c0b0840061220b11021030620082d6007a43d804280720790010b000400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 392218830 1250 392217580 392217587
    0x70e010e0a0c09360207030206150d0221010c05090d0b090316051c0c02060403060e070b030f09060117030405040f02040e0702070e090a1a04030201090602030c0a1103030403 76
    0x1034101c003000e103000c601400300c001c08403500310751680450401c12404c500540c2e001590f445000d480d00c0101110440580340060090076032003440c40041c01a80702c500051007008445038003030084a0010005140e02400c2d0300044c50b141801d14400360344501e44209284118001d109050791365141c1d0405508108020001401c001882c0c14003802000c07400c400100c40000c00c0c01192507094503090501100d0009040c1700d5a40d066540030020030440036a401ca15690040a0b410b80c0b082e4010003407031034181140e032840d02400b8403040a60041c400c241e0301107607000b00d04000e0b500c140c586c544604034601d0002035035490058180d1222015150100c1504450840841180c013550810307030700880d00c141d204d10b0440c020310566011b104038007108010f01c1082ca0380842e60b04212000041400b40549404d100c042c1c40c0d00e1071100060060f80c0d208600003030030380103004403a4002e0103400005020542504d5401c02c2e80d00889403902c20500000344110055000101556042b0b4030310020b5085203803990f000b9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 392220080 1250 392218830 392218859
    0x80315010e0d02121011040305010b03341d0f1602030d110903010216150e0715030b04060e07090806160507170711012606040e030702120f070e01 64
    0x19000304003903c80d540c13240340100241d0100020a00f02040941030b0040195065001030004483d070303500b08001d8080a180024022183d81342c08d145262182c041005820084008620700303c0c2802c4150000140c41e031409a50070210140a040e038020910b0003910040d02c0c0d0a0007803000e001044c0f0740c0a90b03100c0542c0007064940d0b102c13403847e00042240c85810302c00b5042c000c0010080e455800040c140003c06d00a40e20304600f28440c3c0014035550f0204c0c590310003901c020484810680d0301c961800c10100c0e07610103c5200c6c4007100d0600188403034800010400790348894114550112200080c028415804030205004180b244041c0c802d5081059010144206007003c000400c0b00c08502c1409211900f40140e03581324911000e44e40d1040a03141509908011240d41404607001e0402c0e1005003030382c0c00d02e106404801200e0350440380d80c0c9a0170040204080703c182c01c003e101c140460030068607000132118455080f00000c1c11102920a1010f24107400b07074114464032001c04004000c02540d82000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 392221330 1250 392220080 392220083
    0xa0f05090d05130b0c01091202030301030f06020f090402281d0922050601050307051c12350a060303020a110114030c1902030f1b01020c0109080315010e0d 68
    0x1283e40c4001c202e4400c403d40a940d00070b92803201001610715402c40c8154400c8648502c6a00400c0c4420781041c002d0303889000910001d0314501e524504503000502c07650003810343d44208022581400d144002140403030300f10321031084070380416980c1c1081d18040e4007154040401d1618080142d41e680c2c190321070030000c030300c070b07041d40641919400305a4486d8000e03001a03c82c0c00d1001052003017282c0b4100590380311428070415009006000001ca00e9007410110407002440b48101e48251650b00d41d251004e0344100e980700300030405016801e00301d10f0170030408184d0115085e8004100e40e004841c204080040182c040040c09140c03c204200098010805c81c410702e070060041d001da10405001078801c2c07810750106401202001042116145598014084103540020031051701600000305036564480c480016540060a00010080710300746038003c010089040005810504003481d00341c2500e44210013204c019001004200f0340345808015200b95080034a085094460008040344489080440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 392222580 1250 392221330 392221337
    0x90402070204060302061c0506030304030308070809160801090b0604090c0e0901240305061b0d0f020c0105090601030219060503040f0305090d050619050f1305070806040b0a0f05090d 80
    0x480d0015075a45a000d9001583c0180682e56550322503048003006a1100c101c00c5600c52030a0040381c42400c0c000161000c0c1e0f54591140b06542d100c84805a81202c03004250074001d00c9000c840c0703044809031044a40003080b000c4000314103400b9614040c008198020080390007245016402408030340700168100031038000c00303003001490311a208a05c0c00b50400c4500c034442204078280900100382da0654800c110782c00340050300c005031a58480c01015403410040f00d4482c900900034200070492030340c0000b8812290754401490181800306960954030100c2d41c451580c1c00040c01001541060512109507010303c2403d4144941810406080f5000203080074042d80d40c480200020580541c0403242010b4004192588002d02850065514101103456a100020307004484481d2071aa020b030500031070302104002981e40e542045a022854400c1c0c090300e403407250200010780942c040c0714144c0182d000b24000402403400001c1e0b07900343c0c0c24a80d4003040c05803400080180505022419550103503e914 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 392223830 1250 392222580 392222587
    0x908160302210307030b040e102c0d0f050a080403030b15070b01060f0302090a0b0703140f030603010c09050f010309050709061e1409071218060b090f010506090402 72
    0x14201d14024210300c22112a60207440300c100d0b41c80004000c0d40c480c101c0350390184124144081840140e03102e02600c0f4a00354816a61800b1000c3c5940243c5445014210392480c041c507d21f22044082031418070f031300b6007508419201c2600c6503001445504c0d410050a240d486c0840f9020300500091004001500b01a42c1c1e0340c000c1007507944c41c00701e011185030040c032842c1c440400c0c1c10014000f5000784162030100b44506800000c0b60300038020b0f120030103c0217045028070741c50803c2c0c2131169480358100b01d04100910010306272015002c000340101e80403e04565440b0710f00b8505250844409202040a01001c10002c01031541d601096014150382844d011441d00b070145480e07881c182a40c0c101e541c001d810b004002c0b4170368110b0700c12071500340100c0309150f07042907a815041580304100b4041e96048107043e000a01c5945c001c01001f070034101302c00400128080711556943c00c850414108859080d101e1070070314514581f03032404c581c1001c0604501f403195494400014418408c10800314065038020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 392225080 1250 392223830 392223833
    0x405070e060d0f0302010e1b0f0603060d050d110c24130504020a0203090f0d23150f010e07032d020f070b010e010803090f0111160f080709090816 64
    0x4100c103810340d03021583da54000303094507010b0f0282c07590b00c45201080c81a000812010120303982c5600303d288010b0100120301c1c800f0810310009a000030180c541043c020b05599001030b03410410001d41c2c001e83d0341e9103606400d0103400785050840d401440b43c894094240d03032054500c42c0c0d1940082d802030304c01d02696034405110320710180704d1441d0700c00d9a21510202c1c0401c82541c011004002900d422100c8419012f0000204501440581009807001907100e0322038a00c41140003070f40002001c030004952929412410390601c164045458030100e10321000108990400f80d030b2999000901ca040a00420b52940c010003000e00129007110024130300a601080001a141d0440300c0703250080f1612035a5440600303086002603428400c02021030104000040c2101c0c0c0030040c2c5501311402000300b03a40d40c40340d0004445844040184000c54015180d41c0c15005e0410342d0100010009290b04d03041c00f902d000f1209080c4007899020160090401e0440300c0041d941c030040b110011000c28600004d00001d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 392226330 1250 392225080 392225089
    0x2030a120e0f011401091104030c03120c0507030303021206121b180f011514090402030a02040b0c010c110f070b0d0e0706090f12082a0a0f1a0405070e06 67
    0x120b02c8000d0b203e51074400620005626546480d041c1c41407210706200107141c42c0c0b00d0400a00c034610024143e002d00071000d00000b0310011341700c0c0c0c136241c1074a8a085104050f4561901b01207135540100c0101c2d60019058008402c44040140d00003c1116400054031801101039214058030344400b84021200a5100e07069480a5941f100311280102189084c0f40c03841000c0c484517003e0007034400b80440e1080c500119440360b0300b0702201c07a00c1101c046040c60800750610010f500081d00c3c44c0d0f1520b80901c030114001d030740107000c2c080202d090b00020496180c07122003c2c00700c500080c00b0078242e4120030706a079022800001d088080304d00c0491036940e54418403012400510440c1c04004050144500005406d070340302c40c1c014146d86c241d0840c419841da40e000007580c030703211840000f805210184041c00043d0b040d080307480002c41001040f8201d20030780c000c2c4541071282d02c1e601201d204d03109800b42d000384410710308800d03045008003014800701d00709501c800382e07035001510400d80ca400326000041c0440c1c40f0b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 392227580 1250 392226330 392226343
    0x605010b0405060d1d012d2310050909010b0a0801050c09091905010f090f0615120b0901060c060b0402091c0f02060f0301180605011b170c03070203060702030a120e 72
    0x811700030031090f076041811050490200c40901441c696441540584541c940703d403800d81b41041011003035032080298650381d081d8000340b4150616a21500c0094607443c2c42e25a144680c10b60000041eaa00794070041000c00003150f040417080e07070f24240400014400c94803c4072101c2e0340845100c04250780765814944d6100e040d19060400600705000010841000015174060701e40450080c4520204180d00c0c404640d5107110340240b45071000480c00b44e460043c0d0110503c0c01070034602081080c81e41e4040ba0956000781d1104001600100000b0113101c55481030740b111040c210307415403074a405400000c10201c4c800004241c0d4604200428080002403076100304e06c5940074103030946035244d82b007201499420901c030714041200c98205012041c401446444250342050312170307038028806181c48050700350215204458000c0c075000103955465003100076190010060008543d244c00b41e20500d8100400a011071095610500030040800c0c0c2007a5080c041c40c0b115040001c0d02c01c0550001c900c1d243c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 392228830 1250 392227580 392227631
    0x41a0a03080316050a09060e010c060509030903070909050309011b060c0203070303050603010b010c06020f090a030503041d150d061404030f08060f01021c050c07080106030605010b0405060d 83
    0x5105010010400420101651040803c5079248914000e07114090760f2a01c150f20545c40040c05a450902c0701e14042c20200141c01418501310b101c0365210360701c071821140c1c140c940086960003c00c070f0011074034040040390302402c0204001d010b0050301d41d94282da02d0003248030320381c10310000c622004c9030108001c9101d405030750090f800f40a42c82c100b44002e91603500002c03090300024140b0002071070381c1c207050103000b00080701030703643d0007030f20a0030b0300c03400300070340041d0400c064010080000801c20740d94814000003030b500a0024541c0e03246404045191000c40b44403d020400c0310000300495454000029017209000751204084100f052608000400c1d4007034400d00980781007018042410f0784400404c8010070243c40d5490786440394404c0000380003000362660300507407041c2000c00144040c0c4205203000c1c121820617030308080b00c003401d647c10801160001581695261300400c1440064043e01d0f0042440c800c0c41c910381402c0c240803941d684924555004c0c015201c04401e00b05c0700d092640034002a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 392230080 1250 392228830 392228839
    0x5060d0b03070f050f0a05130f0e010c081009050c070327090b030607140702010c020d0c030503031b0306100806030c1215090f03030403081801020a0302040816080c041a 74
    0x580c842c90300c0024014240a51400384031201559516410200641c0701a03a400616408c0040c80c100e02d0710010f085900c03020400e0b5612580750f122251401d0042d07103081d101030b031522150341c940a101c107070148059903c00b054681c00c00051048a803080f1040740c44264151070714980442c0c00408010300e90340e261034511401384175900002004c9160750300c010000f00d411000e480c0079460f100750488100f03280e90711269858104000a200560041f106c00350714510142c195407400106031075906a10f05564020b44003904004100301c0c040310001000e4052812000c1d00c01c1c114240540400c40e115024201d01060100301c1c07000c204155003c00c10308402c00001000350342070110880c6c5142e140e031030741c0c0ba011400c1e02e20180401c0d560b0743c01107603400500c50480001c45c1140c0d640e0300d0440c0e031030001402ca0100510016903004202c0c0302070000b864400340c80d48016a450741351042c07061610b0201e680204035603485441c1804a120041180041164103d901151f0010103208880d0b0b0031401e184040e901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 392231330 1250 392230080 392230093
    0xe01050318120304200f040207060b03010e0f06070903080412030509150a020f0102031506070f080304060b010e0f0d17091914090f010303080a0f0513120507030905060d0b03 76
    0x2601901801148203030301c2001c40a1110390912520560030171001c10b101e83c414041404403074141003d41c003800030180141004681076100c0001b207800c40d0311400b0808600c3d04003408146a5102c2000066003056440c40c01181d4245180c6272541140964022241507640310b150001c2458412030990b61140c1c1c0c001e09001e008034028200814503882880740d0300240c0244000401d803100180300741d034481c811072501e02d5005800352040083c0c40e44070380801c4894814184000010500800180d84038070310034003000883c4900e030380c0090101c0310061440380c400c1051030340c010a140c465500c21464194050b01e40f5444420310a4a850326016030032007903400c1601d400b500b0300040601c0d040d0000f140d0590505e038003080c544030240300498004886074030743c0c8084040100006480780c4001c4c2d602c45403040c400111030150b081d00a007640c4041e41c44203602441070b803200091158035600c5010104950130003528060307079554064011006841081d100340c0000c60300d004860314070342080c2080c500040550700e4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 392232580 1250 392231330 392231353
    0x5060307261906050303040506091807091802090d022b0819030207050a080901031401031a0916091e06151d2d03030408030c0c0409030e01050318 64
    0x44020200c80041d0000d0b0809107000c11a00780e8030511050701c801030051031505040106000c41c070b5100045480d00302c1040803040c01000d4001d00f805014041c50b980d9189090f01d0312000b4043c10521354a5000a180304000300c2c255580c03803003800c014550341a550ba0074610090020145e825030502c4403a101801c044007a02c041045a0004000309049040000409a1140d50460403400f4801004045074000c00c1c1c000045075882c0d01401c103d00051401140216101c0100c5030455401c0e0700407209243c50a00000106050440c483d600844010040100c42c0b044442c0e040c2c184080c1c858003010503901d07146000c614406c0d4402c90f000003600c0800b805101d60b121000647c40004d1a003000c0003500e50380d0101004480218a4200391030000c0a070404600c0345400b0080308101c20034200341a41c0d00c1c071144481c80d1001e2002d04014407140c0301031500d400350f46040c1410030f50304044580c031451421480100080e0090065243c918003840d00640f69650b07330040c14080350848000c17031454440c0d980f8400307 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 392233830 1250 392232580 392232647
    0xa1806110a0201180f030c051009080421031407020409061104031406100905060402070204090b150103020f04030305091c120e0d17030c090405010b040f0b0c0705060307 74
    0x10074000c1030390080106182072240c8910461103144001c010250448600022900c00c11007050610b004500b91170400c64041c0707176801110000a02105c80e14408602041000b0080c1480e82443e8100c06402c5001c030032070741d40101131159042ca8076003e02c80104100b0199140c030360010903000c1d8080030401244542d8805801c040d0801d10045911140040c40c0504c0b9041c0490741030b000e1074030b860100d40704c0303403c213098400a80401424513422503030034007030040940c3e11802040b0f2514003540d500d0721a428402103401d03840e01c14902c0705040c5401045000c081100c04002c4408036501072403e00d032100072843c00244808074007941b45014414100030501840400030a0411450342a250012840b4106003800351240900743e0160414001381030000300369a01c0703030095034404041840580f9101a001c0060b0489400380c00c8648445070101e01840302c49a001d14141c007516104c944581132603440104955164440c0c054540506400300c08503140500508460102d0040c13a240d480040340b5003451117 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 392235080 1250 392233830 392233837
    0xf07031e29060705030d0902010c21030506100e0d020f0621070f080f06060f0d0b0316080303010627060203070213050907030f050f0607020d020c0114030a180611 71
    0x82820751400558001c0e24200c0d048070f5000350321501960501c24058014401000140012380c10f01402c60b60003800600340c4100c000f001100040b00407400e05400c030000301215001480d5a0165210110205c242c40d0440403080c0380740310448290007000840e10110b04210701014100d0f40040340031480c50300c070850b018011004541401c0d503107143c40d43d560b07100301c801814042d140400b00c1c3c2c01c0404980340103901d01001e584100d016044030314110f50403484000a41c030005250102da50344244004d103038a000c4c019030444038034a044004800f0b0400921703a440f0b10062042e14207000d50452252004500d180ba42c059400b8040a45001c00b0380d290000380d01d0f03920842080b44240c18105840042a0007071281502a04c001c03002040c01905540c4c030000c4500c01c600055640e403058041d8511078aa00b0062a8850221a0b000e02602a4000006440c1803802c4102da810300280b45000000c0e500d040c81175991001c0790420204038201c00076046108800754907c05081c1509203401c40d00745103c0103004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 392236330 1250 392235080 392235131
    0x1b1c0504080105060406050105180d0510020c0625110c03030406050301050301140c1602030a06020301031109010905070f050703031d0303181f05100f030c0f0e0f07031e 74
    0xf40419500c09007004102c44003802040d01156043c05012070400c03003a604002100000b402d07090100c074003525030a1904201094042009400003801040c0d8941405456007020306440c000f00c00701071600c0d0105401906400c0c4c88200410b555507407030312581c10071041030741c00700242c15240d8840c0c6841000340107600074080d240c040d60810324010822081c101c00c0b07510034910748012a0603c0201c46d030084078101824400d0303070705214040c60039010500501c0114000c5201c0c65a01003c10040400c2c0059440c0580c400070b1b05514200402c2a10f41d00701e81c084030154240d2a109641c2e106030301d0168010420ba481460a42c1041c4082d41085980000114024030400341c0c009070204841d501702e50350303582c855810403011108188100b094803140c1c10054001c0a0b030228141d803a40c0b20840302c4041e0056901c1030302ca01c4c2c844c0408110708460316490002a00104d4803410091921100c1d01726900c2015242901701545e4010f0807400c8010b2043c10f41c0306d500d406009001c0300e60901c1c40c004031050355094 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 392237580 1250 392236330 392236333
    0x20132706050306040c0e0c2203140313141503070f020105060a03030e090402040b100201061409040f0201180b04060201090203010f14010b03040f0b130b0a0b03031b1c050408 76
    0x2804075451500003245885203511020220049090010340c0701d41c60f00c00b8020003944141444070046201034012090b0126010202d01c0d0522483c41c101000c075010303000034005a6800c01c10260781304590000c0c17504281d80040d203006001110140200e0020003900f02c1c43e060404020042c400419840001020b03080e506e940240031980b6410104a00c5c501d003032000074040f640c03100c82c882050501100303565225000420000e8181d04440120302c50000501034580140d654a2040c8268441501d500154103400c1e114042d080c601a80c50f26240d11120001074140f000108155459400041101c1c001e41445119241c54664a9030302174040c00c9185001c03440384d402c0000e1a01c1d0340106125910741c05120103285000c1b6442c0110000c0c40d0b80c00900240c1e061800c0d50003c4020407005003a040c029440813581c240d01c981d242c144200c00d1b102c09003030603c40500700410000c4607034002080d13980e55001c00c150354254213524802c040c0307050742e40d0b03040d8000d140340c0b00b00d003550346a0007501038401ca512600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 392238830 1250 392237580 392237591
    0x90504060b040e030319110f160506070e100806121015050d0308070c08090a1d0a0b06041a04150c02190e0406090302031e04090e01201327 61
    0x8680c030b0340001c0790340352622640e44171b100c2186151a00500c0c0043e001040f000d25188400000103010b07444034100304c203900702c6008000d00304681080040e920084034508201110303200c200140080034003860813802c11610401081807a5030300d0024403030958400d4102d94840704101102c001505c21104644030036524040001024148244402181a450340c2c55002e241e8603120141c0e01441d802d0f4065490840a100109441d20360319002009807182d4442010a40c014065015498130024802c801c0c090500b00509103a4480380140e5007a100703070316051400307000704601d03160841c0519840381800c00c007006503450200c1e80103140c242c0340781d009540e98a080321b040f00303049480701814403821781c041c5e40c150300160202e5180e501c07480ea054420701c1542d140c0740c000c5101007805003c814101035050740004003004540c4843c458100c186150800a002c8400055602c0c1e0024002a8210820880009981210a9500000602030800e0000301c1c01c442076400b1442040031120204411801c0c1b400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 392240080 1250 392238830 392238851
    0x50f01050918040f1a0118021207031d1002031806010f0b1b060a0621030c0209060a030b0a050a06090501080303180c0607060b09010b071e0309090504060b04 69
    0x140c08891480002901031041ca4415440c1841d031260002d20690f05850208800700002d0007044480d210081d850848940030b5041c1854032000c291008450702c1440d204000c68184502c1c0700540a90207501c0e41070020300f1b60300341c0c882201a0380d200603030188a4081d0400342c4c0316a0f46a07901460140015075192020351544142c559600c103000e0080043d900001c030b0040045680b86801003505940600c03180304010b071001503d83c0b800001380c411141c010703220b6030244820285041c030792840301040081259203038180c0c1c074041e00600c2100d4010f0f00a03001c11300086c1e0f0540b180ca2040000b03613846508800c80d850312030303600d200801055808000807802c000002a06414901549060b59046c4007e54a5a12055408254200700411965644c0a1070705081c81c00e0b03642070064101d05004203c041030b0102d10104004881e17605800c03401001400344401404a14042c056008a0707100c00040d40c0c1b01c128030308041d1b82100f05648101300080c240f00c20081000100d800081030b0310416034060150b450034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 392241330 1250 392240080 392240087
    0xd06060305060607060c020111041217030c09010c02030a0807150501051905090402040f0c26091e0109020418110409110f010c05070303110d051303110118080106050f01 74
    0x359510355000c072050000760017168056000c201030801a0000060380c007129880102c8603042940513144041012040405001c94525510050255544500d1952900b0741c80003801c1d01030103058904200580c1240c1086440401511441640251505031110a01d107000340000c2c0d0054040e18040d8202000021366080200300c4a80b905c0d2400e405182d8a0b043c05d0a0040b0410300034400c0e607006440390120030030800380703100742c108ad411141e070b59203001c4100e4803a03a1520481002c10801c1c502a000c00c100c0b10388404240d2004c154004816182103c03568501d0501402c141c4e44042d510500e4244205001011000c020050b05e1040e02ea00d9000c80d1400e04100441e90102005040108058010940351901e020905140d07141410b004090014948603940303002031580080700840e9945444840203982002119051405441e2841c60f10b6076a819956a00d0818030006104100e40c0206a01c00d81c02100210125100000b04c400c0b40390ba40c20186010300014403845005526070580d41500307511 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 392242580 1250 392241330 392241341
    0x30316120b0102120f0d0c110c0604031112030d0e031b01020a08040206030a060305030c0a0c08070f150e1f0e0102010605061204170f040801060e04120f11120d060603 73
    0x705801800381d03001500c03000540c0307510141c505c0382d90110410284445405520461800c6199981c0d00d0100f4180601c070245000ba0f64629584122414481080064580403002d4030391502a10201c00c40310080258070300e50702442d0f00012446092240c0a0803e4100002070600f40c4581d044200e0310b1080f1061107800c034440e01c21100700140c0c107140000c0150800d08021a0000484040060a2584ca4a8207801e40e003003001c802c0c07220707000900e01400740265400c0d41c030003a04428014283c0c1c1490420f4424801405111780c6034400482d481108480d405680c803c03c0c0581d000d0075030141504c1500c6400a401003603c0e980780403808841c01e104403540705100b80e0b425950042d00700d9160910f4096040e40c0030000800469032840304c00103101d0340c4482c040180c04140d403103483d07040d240c40c1015041400c1d00c10540100c06820a11410040861250305401c1415911800c0c51030780124006400c9601005000d01a15a44176521443c2d04980d0074200401e0303940d03410f41042010300d4449504034207442 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 392243830 1250 392242580 392242601
    0x4090c08060103052203020c0a090f1b091202030115060804020916020c150706110715051603020a17010b040810020702100f050717120906060109230303031612 70
    0x809889800b1017890440f0400c0701e01e04d00900450b451000840e0010304040450340041401e55102c02d4080102204ea0040c00ca900034101c220b540301e0076035103c0080c01c042c92031041d500340b518072040c4003041d0f49081d4024a202e45070720300045a10f640714100038141020a83d0200d0207040710000007516034044070060350b405100c40c1e0191040154240030000b05100c0300603844182e0300208604800a0000d1207100004800c1c2c20700704d41c5540007820401070514090051410844c20b1000b0000c148004140f85419a002800e00503200c070400c88084030352400d0b91038070794400b03602c6100200750200414054800c442c2c904c001c40b5408071000c03200d83c090380a030050007500f08501c140401511402980d0301420510b1500d8030310304049258444e0303036000440a80e40c07848140c00107a03022040048445269000000310000c1c6124240800020a50419441500c80f6141000d1915140c0e102411100802e07040003400c582d22420710310710702c240f4510407010039004104007100700207640307a0f140a100c00c1038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 392245080 1250 392243830 392243851
    0x5060a0b0a12061506020706020706050903061311120c041d060403080702150a020406030f05190507120213080613150f09080703080601030b180105040c0309020604090c0806010305 79
    0x5140c4990003501e102e14242c111403294495500051001080402070300815450740107013441450494003030706015840d0001d070f041103410030401f451a1800504540c01c41c1806040224810490801404000d142c03525240d200904ca1800c110390310001445603a101c3c0c04a80411500a0750f180c40d03a500500d1081c4004640c2000340010f011902074640e80d80e0141d47c03070060b182d000e00b140d03d0007603400c10100ca0405403650b01043c180500c9500d4410b4419103040030000300000d0410f48030a49a400018041045440d119070004500c28840c180140355455001c0c815500c990b09029a08107080302d038003a541c1a8411540001c202e4011982e1a000550300068002c0d090805104200003511070401002034180e1941c03084400900204005d040b9176000381d0b9480308600b0450001820780d91080b42d2603106220751028411301d204464211030460350103c85c001182c40b06500c0c00c0c0e0240c044410065032200b0081000076002500740c0100860320b007555182c0b901c40d5120001901102c40595034040407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 392246330 1250 392245080 392245099
    0x1608090102160b0a091403120c04050d060c030e0703080315030a1502030709030b0c030f070201051b090a0504140103030e09040b04020d0311060703060801110703051c0b04140405060a0b 81
    0x31a442c41d02003a0080c1e0303441310104a80341e0684170400d494071241103903482c0303138400a403004101c2d41801c0c0264111442040061500e413a110000d26003016145001d01002e80c0d801c01d21071224026407048268605203801d0380d0303e86607203007420b001c1ca400031502030030140e22540e18203c680c80c0100d1200c070016845a14038a003080e10b081000c0c0290001810f800912601d10004800700c2d42a090b40c6102d8901c5a200c00e80ea454807182c00003071004050118825a07040005106806c120703003440415150000d80000d07103410384d0800181008000c0e61003207400a10b0042050110304284034a01d050300d011342c80300031a1100c401c0c01c0c054000821a0083c0100300c2c03c5005c540107243ca0309131a000c0c14020700d05602c1c04125500c1d00f50502400743e5400c00840c0e03640d00100890341c0203000b1140882a04d911003030801d040c64502a14602ca02d4008011240c2d6048030302c50700070016840721b080103501030405c1007c1d500400001000d084c09440940e1688240350016003008018029400c2c442009080c603640b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 392247580 1250 392246330 392246333
    0x20304030c0f061e0c020d03050f011211150a02160303090b09032505121203071404090c081905040f030f1413031a1e0408070605160809010216 63
    0x21464481e0b000c0f0380b565224403000c081c1082903480300035402506180003a03d0040d40c04041d00d00030032112540245400c0404105000901c4903026044034001c1d20348400d5901d040c600100280000c0280b00d500416202c1807102001c0400e000e0600c81a840d0200c2e0385001020080d4815041c6c540f10090002c0c1c0880414001f44500d200a001120400750413030b808040c8040040b032205071805003440412107504c4042110340340084040842d1a007090251410407005000351440707100003003d03c13041c402605512841c0b10309000c2228010f04c0303104000c00410714001001480080e06946c00510309030701c04622840e1078980d10490b03002c0d0354042d44c0400f100e511a0f400b40ca9400b05200b0000501039004103a500c0715110300020844500402c84900130705040d0b01e0320031405440c250403d400e003a44c00040110200400424250003101124030303ca590742c403440c204006108503c0010101405c5ca410300c0706456542e181c05c43c80c170b00c1d80e40314554540d440300301e590300b01c0c0142603a0b504a401c07c40c00090 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 392248830 1250 392247580 392247593
    0x3011b030e0708060403030b0604090c0804051608030d0216150603050c040204260102040b0c07031403030702060f1005040906050603060a020901021b060f070b220f0b18160801060801020304030c 85
    0x1801e451020b00020b0502d03642f801c00c08120b902d0f16890030041201d400400c01048010700034030007411518501c144004e41440007407966401235030b2031011410780c000707071204442181074540c1001c2548031100d40c005a080000100141c80c0f03a03c403c0f26180310707100f0041d5461a0a000f5074080e00c080a5601a0742e4150f440d41c1c00c0d00c0880140d00c12580d55003000f002c0f401e101060010440e0b03020300c000400c1018a1844c1080200342e6500001d8074941090080c000d010794007040a6803c0401c81940c40c1e030b161a604c2c1d16086a00b002e0b4080e03640645041c0c101801c204198212a102c2c0c0e13822000c2c1d503825681c400d0f80d42c040c3d00c0744815460068210f4501c8031503810701e0701c0c141400318002804280c10115041c5615005074081c40c406d4605331a10310400600c8070b06844900141203030245180e2440e90a5610703494083e850603002042400c50324001810525030800040c0741086c0c410880c1c40703d010b0180700b1621403195004400540d400d140d0040b89c1c0389414000c0324081c50b071659a103c1b01800340d49805 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 392250080 1250 392248830 392248841
    0x1113060906050a080a1401060215150d0b09070e072a05030f0a180f0f0906210503120103031806090311190801020301030c170f0a02010f0c0203011b030e070806040303 73
    0x11200317070340d43d030000e0f80d212400504414060300f1107400a201d50429081c0b00e502002d00200300015580c41c80c4030060003a01c03030f0345a0b0003403a54018100c1005441d07860000e030810703001d40c05c14030980011404101e0101e90009000040707200d9681a1401451491403c0741401c1403508040c08a40c401c0113030b040e40608d840010300d1951403074a880c01180c074000f000340d0f10301d00e107560210044400c0700c00d09014805411036400000c0080c0383e001c225040c0f401010a4420799011404600702c20f6140c640800d0041c180102c3d507452019003058007a5686920707000c1c0c15828030650462410803805408a40c0c603020720100010380f50010100000c0074071840030424007403000240ca12001e8030007030001900800c00d00146001c2d610801c0c3e824255030400851900c0030070b125040c4a019803100b0745e048014980414503a59284d020301c2c02f2610100031321002e0b80c130317544028002509507103442c109461a641d40d080c840c52400b0195030501c0840300d0700800c1c07596a0014003a5641580103440400c0000b400780c0d105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 392251330 1250 392250080 392250091
    0xe0108070e06070602030406111603030f061d040507050118090b01020307170c0d050f0702150f0c01091202031e0c0703060c0f0e0103150504050c0d1113060906050a08 73
    0x211940401c000085aa5500030078000c0f1215a004400c1c00100181c902440f100400001001d5040030b82101000d440b03a198110007409242e55081d030300b1100c2e4410f4009101820326803c20300c0000b203002c1d80a006d80c40040b80c05031207500950401150b03540c4161500e010641c161104144000d0a140c00c1d03800901c40c1150310384c10740c8030400c00a0001195180c03000d01c20114404c0f195162000c158516050131510806d500c01c02c04c08005134000b11405006544806406880b03992440740354541940452180d4000060305010120303024910301015040040110302c15400422a9002844140c0c0d032409851240c2c41800c0c2058030a520010f400c0002d0700d0710004074000c940203265251924412141c80a00c1d040018807000703092101c0c0c0f60800d40220400c90b00f031804014441c2c019410003585401801034520494440006c22503c60f0f404081d10120303072541e8020024090826420036155006662260600d2000c40b0700054940c000d54000301240c03801c1d1100d500d041c154010031242c40100404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 392252580 1250 392251330 392251337
    0x606010c140a02030607090911031e060409051608070b0403020a030f080f0426150109020a020703020303030a0c1b030f0e010c1221020415140f07060f050106020c010e010807 76
    0x30b80015940c100b10b194003400040c3c6071889418208150324065a0301d024400c0c850010400501c6809044039941c150076280421221405032203010021700600101d40014009104924021a50756040e50b80e0000700c07003048040b116100c1c3e444015200f1400fa911010354002c61486080002c1550410b6144d0041d11901c181842c1c082080803500e00d58000b5048484804402d1203200514084080035045818100380140000c1c801d980b03c4480c40501400743c1021306402040c18405076000304500700c050350b0700501f92a03e80c034180c10b00c1c0c0000d2141046040000364201000252423410f803829601c045c0d0140d8800c01e041c80340c2e00d000d1740e031204c0e03002445040010500722000407a04094484103940c42a0359807501c0001c03620300022500c8030b0001d410980d144100810000559280b50f110665601800d0030f03440000c40900e041800d0141144890003603000140786000c0011581c4181d0381d0000307210041101e070b40c0300c180803640c0380c031061402c5000c81c1c006803001201d507004405082e4041d03180d18 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 392253830 1250 392252580 392252593
    0x1030506150703090306060b130e0610030b012c0102011b08010e1005181506090d151506030f110a02032a0708060a06080619050405070b16060e0606010c14 68
    0x40c6c82a040b221b0950080f03881148c0480c0c00c0702001411601d002c002c00700c039075200e2118100140002c00f1203030b500d44103c1c103065940c464941a640030780381b180c03014075030b100c4080e4000745c800008c3c00303400115460060040d440c0480b5407060001a0031400036510590341e4640441c0e00340040b0384a40e802c06046c1c1c010070140c450000406940c1ea00510740440500e1038850014184020300200d51549403140c00e110790020700c45e4034a640c48942590306210380240e00c204a942005515200030000600091032242450001169080c0c01d5080805180030b524420880d40c03440b401040c1d450300407481000011b81040040c090400501440c1109008502412104003000b5000441c03800c43c40354480800e90300f000301081403000061040c1c0c00240300d190091b012501d03004007149004000416000481c80d52032021906002003040000c001e44030842c0c450b90b956600e00e500800314a00f01c0742c2190064204a2030420001c80819054020101030b110722541c41c01c1c40c3e403101c01c081d0f002c2401c0c240c284502c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 392255080 1250 392253830 392253833
    0x90d0f0518120a02010306050f030c15120103050d090905070909020d0b040f15080102030405060402120a02041e0c1106070c1109010906030b070504030b0a2409020315010305061507030903 82
    0x15201d0401110700e50003c00312210107100150695200703a206070b120f1210310151110b542c4000c141c0c84c001100c00c444d07081e9030040c2c420034681d040c003a1002806202c410a0004070400c900002e10103038501c030070b450f040e407556910400c04061701d004844010000d4501d02c0108447d04854018100001d040d01c40412411400310118040301c100c000e05180c071a8031180b405401c01d85091040002d000035500a51940c60240c0f5059544c00d006000240a0600388802c280b40341c0c024064001c02c075074000e0060094000d441c07003242501a0102e0301002480c54003902c03170032860017480e20b0109024000302418459403601010380304845802c4098034400082d440103105070342c64901c1d4501800c100000029550b042d8100388889200c010840c0080c008100014400714036114001680300c8440d00d0045414000121012444507042404441488207800041741c8040c0c243c0142d071103a10310aa100d81e8000c400e80044098a80a807903041e0809485650000d01d102d000d00140741c0e080c02820181200d5580e03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 392256330 1250 392255080 392255089
    0x10090212010935040b0a1110020418022802010204090f05010618121b030b1e090c09010308070c050a0f0504060b030f0a0c1b08090306090d0f0518 64
    0x40070708a446110155080481401c1e0a650304101e100c2c0800d40c002c01c0301c030b0090003c61403042e0301442d401c0f00c0703001c206200d00d14801c050b01001141003c080c0c80307013039a5884080d80603400c180140741184d0440d524048000c8668401d480200c3d66018205401149000710141141c0700300501c4070465408200c00315010140717006840710340c40039200c005081c0d0b1610100a0092480800460101076408020010001061360079a000d0750802d024a064841616400d80ca51043d540000d01c0c0380ca0131400c0001510b402c801d42000c022180003039100c290f407141045615080c68848403a801048803006001040001c009015003c0c80740c2c5103141070790780705d80000d9a0101e160340304030384181001030706102c41c0c00e043c018034004005020000703056040c101c001c0303004594024120003840c2d40d1a2412041280706000d503501100301400403050603021428181c2c1e40e54440121103003c0d11517040462140140020600318541603592864240d49502034101c03203540c086c045003940c107141e1094005883e0b99 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 392257580 1250 392256330 392256341
    0xf0f10121b0215060102060106080c0c01020d060e04061505130e010b0316170c061902010603080d092f060304030c1b03060c021c0c03020a0b161706031009021201 71
    0x1602d030000c00c103d540155001d5003000b402046030b03045401020040003a9508050041d03040b0001401142e10382140d0b00c0d40c40d00a008041c0810407450902c2c00001e100b5015018403070240f40075403014400c0c101c8143c0c0107103060b001803091076040074a1040c0003842416030761000c1600d1003d40001b041032402e00d400280b8101072a081010344202801041110309003180065a8130b0780c45501605411000c10000b6929010700760740107000707080c03100651000d00e20079403040010719440300a171500c6a8403030440134002c0c5440c8408a850780142501d002000b400a80858510703603400c25443c10030040402445215040604101c0501c02900203410014005020041c02654481c5800304214510309048066400c480010350541d0411010010744c01155092040020818100700e2803070090780c50200d1410040b07400103400f000c10807061000f0f040c24011027640c00250350741c6020402c040c05000000414041e205668581d204000000d81040603802004141380001c02c4000c100c0c0074151700342e003501c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 392258830 1250 392257580 392257631
    0x11040315020901080906040215221e0e0103120c02061b0a02011218061a0d0807020103230f0709080a11040c020304080a080f0f0f0304020f0f1012 64
    0x2078011600d110301d560b01c810080d43c040f01c1e0400a140508264001c80e03080d22410346580109180091124400425040c1c01c400280032024110a515510541c0e00d03c02d84940000301c40b0341065600000d5240380b04140c0c40d05032600092020000c80c4907000681d510208040d04030f8000800b0300c2600302e00202c10941c0342d10980340c02c01400310380c0e480e480014103511251303140e07001c560310b46031441c21110100118441714a038000400210042501c2c1c41192070131580a045902c0707ca011a480304000d410005803030b59034401c1e00c3c03d0081c1391032801201038071140c80710100036289049001440c594281741106401c0340e524140b41c07014a4540c051541085c41c5a801560301c5084482d4003506400c20703125070021040c10340f01071420942085180c1d9207861200b4070281c0312510200e1038051107010007080707602400d244610039a5448000d2030280740b03500100c1e016403141c06466100c41c4503042036508840c0c0000700422042190241c4002656488a01d0b590340500c142e650021040319801710781c0d0240c120 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 392260080 1250 392258830 392258873
    0xc1003060b0a02032107080a0f270615080d0e1306060507050f07080c040f0e1603030f05070f021e060f0909011406071202121206130c02030d110403 65
    0x78080b00b12940b920341103034080c2d069001700040070888900e5200055641009400d00041003144c82240e54002078041902e136442c042e00242a00c23106882058000c1d58070b80d109400030301030b0040d00d06c07400740e005855200d81d40d00c58100f452004107541c800c2108002d8080d005010007200c282c0d0b1464001101c003540c007c070011550004040051203420071155010a80502c010800706040a03001c13a211000105a54000da449500380b100b520984d4102c2074000304808103c41c2d60760301d604ac0594142d40c061009801203005c1c0030144080328030580890705800d410040c07418071109141e09009140c4200407100c0c225507180003c0c040240d0390071000380781400540c1d10360340d29282c1c1c070010840c5c80312040e8007440000441c02c0e0116240e89458081c1e485042c0c2149200ac00e0f142c1204c001c0e030500d004401210028440040c1a4405a003084003003401641e040d07800c030a64880ba490140220b031451080e20b00507034030521040c0f001030020341180f00300384110b00e50181003d58a070340343c1c80d10f42046140d10f140d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 392261330 1250 392260080 392260087
    0x605010e150f030309041d03180108090705090430020f0d0e0a12030203040b0c100c050c1213050d050105040b06010c1106030a110310050a06050c0c1003060b0a0203 72
    0x140510020000207201215038085842c0c00c400003d0f540c0c407a0390307032aa000303a86604008408940300c1c00e44140c41c164200a50380d917101c12507a150f4111003403003d141d002c540e0000c0031a0946d000040d1400a44801412075181a15180c485070391400f21085100c04503c1041d842c2d06440b5101c9035000814013454009041c8001031344500c034100f20043d0240c0b010064041110f110540c1d440c41110200c41c046445051480e503141012400c510a42d0071800d140d00303000400f6000f6800000b107852401429040030061080c15000403a07042c4689500d11050364019030555101c030001d0388c0101180c402601004020b5690303803010449020b600b0318295456596002000700340041d50018035445042440d220f1100c0841d580d510b01c0740d440008034107001d15000310006000c4020707903000115080210311030584a2800c1340c1d035809100500d0040e107008070004040003400d41d0103001642d07000c08541d0007402c0d030240c2041c284022019401d1300d2108042e00c40f64005104024000100744000310b0340d000e1640d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 392262580 1250 392261330 392261341
    0x402060c0d0e100203090306011809120e15090609280306020d0c0804021c0f0b0405030306130b130b0316080607030501060f0c0803040f02120a020f061306080c070605010e 75
    0x60704042c0f5058a07041d900704010044180d500070424074190b84c11801e5040d24099149211001850909070091518400300f0280b24180e41005000c1030158085800c1e5401c0c250135140308601e40500e1a10fa50482030900500b0940c0c0b03015904580a080742e0b40d404c0d00a45400104440300f000542e00039501c0b258001118015845103005000383c84516041259050525901140714031448404600e542e226a00007802084100c400241c02550040c40c2c6030500d0400303080042e283e0b40305603211032045004040340180700b2480e01510203143e20080000702c0b00980f0314010405011900f204950601840c2404118000b4444040c0d001c0d203074620040c5410310b88414041c0c01c650f01a00030300d05000d07025584440885c0e120300e203c04400d51102c2d682d920390300c2e0b919040c80c1140c080c1c0c2d0002d6000c107900b0b24503805204001100044240200d6240925020600610581d0322992000806d07a114520b4180074490090400da90048040c04881f841c010250319107400701c03007003078020030030b4420f10300140003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 392263830 1250 392262580 392262589
    0x402150a0e040e0106050303030f0c040801051503011401060e060c01022203120c080706020f0903070905071b050a02090402210c0109050301020c07050108090102120a0c08090d0c06050402060c0d0e 86
    0x40c8080c0f10f030340081140c2802e0800180e6a408002c00c20720100c1101d0340019640d04406058074014074001d8001c0c4041e0518030714129580e201c0b100a1800b030761a01c1c8500101c81c0d6144c01690403181d15440300001d4081240a00030700b58054110080030390740800981d4100c01c086a0015400890380c00349145540c154541030910186159225040280700d007088408103043c030b41150300d940d0340502e00683e149400300c072584160040c0c501c11545802030010008901c1d00035000288103800d02e99a40d01d071403240c0c0071a814100c8210001921540c00214000c2c01030800c88886504540000c0c03401d0040e03100650100e03101c42c0b411408031a183c003c0d440c1c0e0055541c128482c07101809085000754203010003c54203d41c0c2e0200342c45640e04000350a03001c1001400207604642d002690040e40402c5c0345803021803000640402c41c41200000c0326a07001492410011502508c003544680d152071645215403200c0c0094032000c2c01c01d03a0b000c00c0c1000781044240c0308003c280c03a030121640307602e41e41144050401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 392265080 1250 392263830 392263841
    0x317270d023d02030f031018060602061012060c031509020903100e0c010f091e081006030206030a050a0204242015040609120206100609060e06030402150a0e04 70
    0x4900030002c020300e00e0519402005a484038081000944d445e076803544184c800001c0755a000c51031000c00500d00340c2000c8100d421400c00d84007550201c40041d02c0300660440524024402c0d007103814507148107840018096002580038880a1401103006a0365000380144a206548041181d035400503081000e42424009845103000180d01000300d80840c0d42d0383c0303886c3ca0005000e40e04024904120340c00260058800d400a04031141041c44080180070840e260203d003409a05110320520a42000b0081c03507000b40230549501500c1c00b42541c5402d81c800c40640409000904031540900c80445c2420f4043c66100603e0b4001d8128003410100710b601500040090566071500000d044045655a1000880c40300c0300b46d02c01340740d400c02c1d0394904040c0000e0070840c400902a400b40701810107000c1c0c0c0022154040e9051002d1a20082e56070b1304245c820705c03000c0c4541004142c84213910301440c83e00201443c1d111b400500203580d65824402200500d0b440441d892002c42d40e405032240941c1498801e5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 392266187 1107 392265080 392265169
    0xb04091506030b06060a05070312020408031207080a060803041412030a08040203060f15100201150b03011d040c051c050d08010317270d02 61
    0x1403001424181c4401d40f850300c800800b2818a16008040b95841e4141d41c13201460880a5a81946c030180030240c8200459030a000001d0151350a20080441089c090313050006468021400340040703a000d049101203a10b0040c0c103008500001003181c055811000c080a041d900000020b40c495a407094580700310300000c10a10141c5401045050203a0300c00c60564589a48404400307910060032030b08804011003240d003405171400e12030308112a1007110b100104000170407803210b201c85003075944101302030300d4000010420400e1140c4100c02c5008802d0004240c0e06094460728108582c5008242c414100790308083c034100f018840d000400d540c040180c82000d80240800b40c40402d007448141c50f2014517154000074100c100d030440700903c5040200703103003488041200e0101a040c1a04c0b46810240903c04c6d1000750781d801d02c244580000048203d60a4001854103150700d0030300a00 = true := by decide +kernel

theorem cover : BRFrame.Cov 392086330 392266187 := by
  have h0 := BRFrame.cov_init 392086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 392086330 ≤ n) (h2 : n < 392266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
