-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0847
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:08:27.602754+00:00
-- url     : https://prove2.me/submissions/ec7c5881-0afc-44c6-a355-14ffc916cae4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 152158273 ≤ n < 152338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 152159523 1250 152158273 152158291
    0xa03020903030d05250914010309030c0c09060303030e0f0618030d0908030417030108030a360503010506010201060b03181504030c12050f0a08060a0513050108010b01020c010c0b0403020c0603 84
    0x29410040d845a40350b0800c940c02c0810844c011b1004c108a50900748408440306080c46c02041d01041d0b81425507500041100003003950200100004505082d03510000076280f1a58052003c21804030200d0340e5650b502401002031317003000c0c010801d0381d4665001117075921079100940c1d01b0084040400720840300302d140e00ba900c0040000c1040104440500180032017401c408140d800d550410102c642d40c0d0040700180d03030900507052290058498080c0c0c02410100c0080d110301c04024414190821041c11480340600071360808004ca030880d801802104d05035024071002505640d00c404458009a8030392064606a0007000d4500b00c42c28048610035100301c0c001c0d02d907006140301d5480c00f40c10003601007440c1c000308a010f1007901042c00045e821103d1100751031a20711140e455040000d05203000036800a6800b041a0f54500c2d074000d01500040d048800000007045001c0304640103a0702d4002c02c158140c00501103905c16800549a080c0241e04a8000d00c1158690b0100e5004903070540d200b0b40e98015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 152160773 1250 152159523 152159551
    0x30203090907142a0109120e03030d050108011a04022d1629060120070503060114040b0901050d020d0f02030a151a030d050d0209030703110a0f0305030a03020903030d05 74
    0x22101c0d502c812282a084c518200810240c810b540f21a0361401d0400e100b5803c0009910380d00c20706543c2041610952080840c082240d56540c0d04803130f000348001501b04210165000c91500c45242901c00d58028609503001d00c910318503200120f500c030240c3c103404c26001d9402405914105c28030705001080f21481440300b0b503c220840010749001001b020042c05160307851004100c05641d000c4500310b03c000d4050340e81d603102c00d045044a070818816400450705031148000009a8048501d00111440c1c4d003900c0400c05100007a080c85109034090041981052518000c400141070500d40c0c0c00120b40680f05020300002c2c071b68002410580c1006059402a196882c02d0520900d5849985d030301708030402d40790440e089003002290300e520300600329009011011401c404030aa080c3c0481d41c6403440201943c0c0c0003926032a120f841e481150320b40f60300407030440b0808106a4854080301d8140c0381c005009600f003500031102100a58401c020164260005002a01c07039252203000b894001c1081d418009 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 152162023 1250 152160773 152160817
    0x40b15032103010320030304030f02120d0503060a0b0414010c0f06110d060e161107120f0308060d03090302040225050609011109060405090619090203070906090303020309090714 78
    0x648101141c40e4041e60011700c0241401742990000110340071281d0012261341402079900000300a8062041980c0044c0101010b07001200d502c01c004500c01c6400325001b0b004591103a03048401c600441c054150f0030000e4620256207980221030310300403584940c0b11429282210780e144015200617482c450207a58004c1800b2070400c000b40a001c0152606030100311482c54586080d4941034015607030202480306206040180980900c0715402400e03425089080746017107450001400d030302e140d03c01d0700007804542c0481d01c0c502d410392040c05520b40580e41c00e00703080c0c1941c081100a5101180480c03110121201c4540704401410340000c8031801140070f0030207460801c0300a82900c12002401082045c20000201150349110a850580d04151811400c55a8510204401c02d8006280c0c0d1540b1a54100025184a41d03070011132180c40c6540c2d0f11051a9903c2c002583c83d904580402400340e0824403040d00385007000041c55600841c186050340800b24119010003540d848021101d40001c4546190 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 152163273 1250 152162023 152162033
    0x50a0804080d090b030c180a050d050a020906010201050c07150b0a06021f15091a0612090d0512180109170a091d010e13080a03060e0708040b150321030103 68
    0x44401448000c04c014954502099042010b100d021884081c402d505003807031200d03803075069084028100181a03040d2051003414416900c080d400412442207a00d040003520031752040c0200790190389215841c0c1c0c1040030702e640d00c202120142a0002817542da07005c6041040d540c4030314000041045401500310410305010021a004005c0701c10311040e414016032003000700c44428040216a0000000900c1640b11400015414085002c1541c000c81c00324501c080071040802c41ea000d4000002240c0d8440114a4140c0f11400380f04c0001c100301001500040391805250f18040c500b1742c0b000c000080d00255652070b01c0b00c94410042030034403040d01060080c041c90700440040042c000400742e040368610340030300c0540c864105005040143d4203082c0818484490074159241041d80b08048903150625554010010240351140307251008468001c20340040c01142e1042c0580d03000075510400c4c1c3d690310140403c03210840020340c0c05218011b0300c0184081d2948440444d00d090340d16040d5254554206 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 152164523 1250 152163273 152163287
    0x3030507170a020906070b0403050310060305040f0609061b020f0c010503060a030f1a01030602030a110c15090f0709020d1d0606040506060f0a08010303030f0e0613050a0804080d 78
    0x5200c28025800e04400552007032009480d03201d00b4107107000d41d0350a0710b00c0c0450041d0040c00b070002c002e000ea00040c00105600310740503500c100c101200d010146130345c80c1003c5056800a42d005840c0860151500010a426070014000c1c20301400c804210700c1c0c074005000c1e04d8020940388580058000f02042c0c03034403280a002e0800308000909e071007421802d0010000f6541d00641c80002c00c21001c0007442820002070075201100c0403941940c0005070760b503a081c014003960040341e503440d055144c50584da1000c804441650303000c0510a0043c0358080b15806580c0d0110b4010f000c0c20300c0b600c038040860f00b031030904000c40e0014000705034025032107203030341c09410301030b903005042c20560988040c6842c0b03411000001c0540e40318030f04031000301740e070b0322940702160003403003118801061000d000940d148460b4009081074102c034030a680c10000b09038021168002c0301e0342d80ca40c01c1c080340c00600121765120208424480401e005a00f643c00010240e920061291f02076484407032290000d00d2203403001600080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 152165773 1250 152164523 152164531
    0xc010507080112030813050111030408040503150c070609020604090f0e0f07080a111c050307110f0a290a020f060106031b0c151a0f04090302120313060603030507030305 74
    0x4403500c02d0300d01c9684e0150107140010101b07003492504892110a0120035040240d01c41500e0b000d0700c0d524106801e2500d482d9002c0e0042da4080d02c107242001051441031100c0601c41c295041c0d040c2e0500791240e0360400900440d0a042ea8000e105005c007087c90111441000102107104000040d0500403200389070802e00c40401c0d500860300500d208209410b00414421390f45644904c0f5244121000000100c2005400c40c070420900c0d501c160b80800c0250000040448500600000015001100800502c103200c032115a0b00510281c00401000f411004452110b181402c0d0344160707040e5035064038245d030304a100e00400590121400401010003489024050b000c185014402c46490034050884038070f205603400100402003d000c401c1c0541c800d03403580d55001900081c0300320400030f2681c0800b003422080d00c6114030110001f413440c914041c4101c00c81c85600d6009021010403400c14110140c00c000d100d0b000280440d00500300040852040360051442511070640300c1d00030307060081c101c5400034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 152167023 1250 152165773 152165789
    0x60e0601060522031e0614091b010302120a15080f0307140f16080c0604080a03080402011704030906030b040209090411060f0315030f031606200c0105070801 69
    0x1804541e500c60700300c3e0756204070b551054400040c0c04a10780c428554079800509000d06000c1d00c140120f101480c000e0809001301418010583c00d803501400400003a41c0400e11035101c10050300b00006018241c4009000504005051030300c00174039109000350498244140c82e60380c811a55001811015860141400030002d103141c0040c840030590300e10503d42d0281c0310300308500100c00404020000b8107031003048801901c03c0142c07a0f6a1052001042d8015500c0724015250300a070303035003400c0c815181141c10300ca00030f08441b07030a603e044e508440064001c0c3c0c100300c080d0781000905d180c40399043d030255100759034000c0c001d458401c0c010b08031150811900e00c1540108240c040c26030707412202d642c00603045201103241e80d1608000403410f11909180e0b0480850200410202707401540200540c1142601034803610070045191a4580c800c4c81500504003c801061a0114000c2ea000300c0c0c0104400540c420301032246146560f254100c1411110140c0d164410865969448495180140069 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 152168273 1250 152167023 152167033
    0x209092803082a09041107050708060c090604210f0c05011d061b010209030f070302240a030b010210050c03180705010c150603021521220303060906060309060e 70
    0x303080580b41e03040d00b81c0720000300b098010443c10f0060f80c9641c010034403031041b003030040c1e03444060340303030954881b03496104203801801510000340c00410f120702143c0001c0001800d031440d203801c192940821003184019180000003c8450708005410746d90303050002401a50085e16081c50301000500840a00c0300c4000841840d21901010791142e805940e4003a0b40c003010801d0083c0c111402900a016074203807240d0510400300f1480218201107600c0c01624002c0e2600150006e8640e84011520401454000c009404105018601d446a17004000301c070414415903449a00e003030a10805d4070310070340d40750a000c44004148801603107107205000703c07140201e010300241440d040010705045c09455015040010940e0500c0da910865404000616801000707d0031034541200403403895009000c164040d282403160000d13441300d818071b54611680410580d040c180862903c501f0002d040d18034128145611200c0201d8038071040e000c1c502c0604181d035070001d060221b900706041665100f4040740103980003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 152169523 1250 152168273 152168311
    0x1303050601120b09030a051605121b010e031801180e010e070305090c01020c0613080f01021908040209070e12061618050a090203040804030c0902070b1e04020909280308 74
    0x301041d580390300c1c48c0b003c40c601085918240ba0303040480003400d8072031a00c2c00080514610041c1510582d4000d4900e0013000348102d51070045175070b0b10865810031203850040d0500036040d8401d901050701503210400f91030a040e90f4403941c1c404d4003801e8202000d07804510041256483e454803843e684241107000030300d000c4180c5c1c4000307903d44804031a42c40c061a40014809410304480c500781d0001d01140c01180c026982404806000707401c4003020195201c3c242200c008180d214405603400340342c0040ca2002103880724070b01a1664000002d106812846e401b920180c91241131050390310800880c49802e05140d151880105040000d40c1510344055098005110076107510340c511040c0c0345001c00059594542e410a40210b0140f944000c2c0040090500442c01c0c04442d000b070041b0034420803582e18251a102a2140c0680200e41580040542400042c000d494000030941d0807010380b80c103960014a0205c0c480443d1260701c2160045d50f421031604000300b60b4441d041d030380c1c0b0107042c10441c111106 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 152170773 1250 152169523 152169527
    0x90c040509150c0a09080f0a03091706071b0f0b0106020d0302040b160f150207020f09011203031104091503120305190b03010b1e0907020105060d081303050601120b09030a 75
    0x580030384400c4801d840844c8125080d401002e524001d840040210340403841140ca40c00c1d07950081c21802c40c0000c61b400c4000414a1044040880040da80800707409540d40302c0b4000c562007800c05030540481c44e210f12800002c50074117099545424002e0010300940e6040180213850160f03200d06c424201841008100882d00500c401c1d0782c89407407050b501e040610074504284880906460004e000e9880b80031011400182c0c0754000d042c014420703a500045400c82c0c00c108800c0350030900c940d9031150101c40401d00080e11070f80c0b02d08c2410104000407030a00782c4800848085440c040c850080c0040080414028850f241031101150030803440c040c40180f0f0052420307664040e003007a01c400d12540710250100359a50a420035080c00c807025000308030300c20071090181d5020b0b9003050018090311005010480991041c019103200d070002501201500341c581d40d407010390360b1105520015281d0051030100000d4401c1c04024020007580e01c50b01071512050400409104000d018015250300c02c00180920300d07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 152172023 1250 152170773 152170813
    0xc1b120828021e031b0717030a0801030f0614100302041a0d02011b1209140904050303070c0218011706011d0610180b0c01110f0417070806090c040509 66
    0x11410500800c004000507031503803650195800082c500c5004100e1741011070720005500046400d180c0310220030100310310609882e0320402c110b041c001100c40d401840818154801103040510400c800112603100c28008801c0b00303810381c0c2c290b281c03a103980800c0003517140c240600c0d000701c0040c049903071016209800203500900f4092009040c040e85224540600d007409900501c05504807047d440f000b1070000380100110010700031070321400503065000c5814200903409a22895014004515540b0740203c02d40d540601010300b07d9000d440c0400400c1480f0740150307003500030034003405140a104d1800d41401d04014050f084244502c407000e603241c04040506400e1a0406016104000306440d800e104541c11643c044986d41c43c0345480c140016901134140080c0b21b04141d40000700141201c141d00c1c107401d445505480da00003642480244224400c041400c01009250303030450ba92540d4940180341454403c0f18109255082004055a241002d000c0c040c3e1100381c44010f0700301d0321080c103040c85c511 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 152173273 1250 152172023 152172043
    0x108030301030321020316091d0703020f0c0a0b0f0916030605070c2103060b0a0905060901180603020c0c01080103020913021210020319020a0c1b12082802 68
    0x105034040401e04c4c481e2060303400b00d2910040a642d42c1c604955015000101e50880b10f0015603041800103001000b03000018000c4090041c00a0036140d00c002103000e50003010307000c1030480040100d805044402c202400c4018401c02c1d910013913151248070742013091001400e03404a501721681c07900f1180c2001042200352648210700041c5500c82d030744100e6403d41c1d0404002e20800d0001c95104c0041d514080b010440032450741d080c0b00e150b454002c40e04003405a44061004510380c0c100920040c0350400181c1050541031418410f0030054030488140c01c07060390b01150109a000804088a40301401401d01180081c2000c00140d45158040303031564600402da4101300c54495002411527a0b10592130700200c1d80101240c030b1840824600b01c00a40c82920b550b402400c0080c119030320341103d8000e4401c45a000c1c0c40e03d41903450030741c0b41c2c050b90020226001c5070840524002141c03001f11105840c0800d400b40714100d8544c9400b85d07840319903802c44915102814020710018000c141d002441d071013a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 152174523 1250 152173273 152173277
    0x20f0604030f0e18061002070614091305070c030e0103050115030513050318030c040b010507080a050d1506320901050f031617010e010303030c0e0d050303091501080303010303 77
    0xc03078503001d0b008403200c03480441195403042001140040c0c040d1500025406240e0441b00d0544140071880c2c00e994030480c03441a240460b140140ca401d40e008024040c04440318007a0005040c048502909001c0301c90445100021072140c111503c01d041d882640501409828203040000b94100803680389a25140c4280104040d101d10024031a0f0300385440420b90b50f81c1c0103003182c6e1910040040c54160600c00d00e01ca600a103d40ca010003101e00c1c140c02410300a200c1a19070070303e810b40e241c0741c030101a0301c07251008050042c10004504140220300c0b4038041019407030141000c0a0400c00010181c000f294444003105003a59000001003034020440300410640ca40080e036151505001071319203008903040742048540100400c900c0c045103810394058404150380b600d11091521001d018500e4081c012500c2c041503802c018000a8040d91001504810300e041800e0401d82c0600001c3c040450950102e0316600f0100034081c0d10307207080012640680c241000030080398107204445990703001c14070000d02 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 152175773 1250 152174523 152174537
    0x606030a0b030714011107030b040b041406010e010501032a030e0c06031317070308040312090b0a1a0102010915050601030213030c03020310090b060904020a050307030b010e07020f060403 82
    0x504003905610150310000e014003603441d160f55440a030101c442c601c1801074041341c80700284524040002c6900300030b49500460b9104991100e031117401c40c0860050089a82e03041c0b00d46005018402000120300800d0040842c00d584d6040000060544e1099034804104074460384c1800010680d0900402400d1050700e000a04a092410a13900d0142100301c1240c00c400e00000f80302a2450f140b62101c916401345501c14154511080540524411078a0140001d0110300105000910407895070380c555220000124406200f034a40b07202c01141a9840341403180c0e541c0b0603c600020300034121500346024002084424426200c028140048031b01009007a9070320000600070707a019905452003642000002944203840780b90007000219140011fa1081c801c00d1a5100b80e1340c003e00804040030780c070072160021500c0307080901070849805070080740d001c0024100401e25460030170041d001103008440c071003143d500d030041000c46044042c03d440119005002c108101140c00a002034110f0380c5858021 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 152177023 1250 152175773 152175781
    0x2010f03060918050d020304050303040b0c150109021207030608122812060902031005060706090b0703021812031215190305190210030b0112020c0a1401090b060603 72
    0x100100200d401485105107440c21207041540b1281c80210811320440481380b21540d03c1d181a6502d009500c20f41d036050f40300b04000e1140c684184050f03d1070020301d00458002c10154402c503251940241c01510713580d42c1c0464014050010440c0310f54010000381410494141400101900ca0241d034401d0840140000381c0600e0f40402014803103504074a4082680c1c03070b620420002003100584d0700700f014606041c04c0e0041651540d901c03c50740181c20101d00d6549040c90310060107072503040800d0a48170550740d50510800700d11103200c50361084055690050b82c0d14242c1000700c8000c0741c907000842c01407940d0341064a580c0e100004962040c80c03a034503003022a03a00d0b1005050031351030a40d00300d50030020f071941c0200307048440401c550580340700e10300760707015070040324803604419401c1d0344040e620034241d40952500c00e00a922403c02c4800c1858481126112081e05005a80c40f012640c0c1d0254400403220040c8a004000c2440e5400e4940c02448041650b0304c0c0c070081c1e000d010b00b20311710942c0004049 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 152178273 1250 152177023 152177027
    0x118090c03060507050c120405010801060c050f07030b160207083f0a0e0f030705010503220f0302010605030607020d0e0105070f15050a020405030718140906011404050f0402010f 78
    0xc04019a8040700034030043c945140b00030916003064092101510411101003c0f1007102004d82e001d031384069680c000c1903032130030204403422103103840284d034107000d480740c410384c00c8030b0038000c0402541c0191803000381400c180c854a945050b0425410045403c144400d0091010119800916005520314400b00040705441c24030b1030054078191040d040000d544107001161030602404e030300b0131700f174440d401544084002d001d0310510507000d16906401c1b540c4140a00c2d8007407000b96400c081651800c8400c80f203c0d80305068203001c049030585403046c241c818030040646c24002e12000d404140d02420103030602141c042d5030380c01e544031405d0a01c006101c1440d11a4442c2e420b40d50450b82200320b031002c5500d64100004225802c042c081c851509140006141e52034034000c0304d0461b2070181c004c080301840c044000c840d00090006c06401036489410352359000f098103900600902044003d01a1545020340c184444006404c490740100d08100070425000c00390401c00d0307406078081c01d10034071a091100d82 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 152179523 1250 152178273 152178293
    0x60c02031b150d050601091401050d0504110402040f0305240f07020316062406090603021305041d0606010e0a151205090a0b01053001020c0a0f060f05011809 69
    0x203074000b1480110101858004034000d002c2078a41a0765207403134823141081091006101400f1a400300901203004000c2d0303100c550f0182c00380c0600c8143c0440c00d800501680d02c00d91080c040b41d500b40400307106001c01400144034084115010403407054a480c50a035034200700804221109040c440081c0c05903000b030048984a61640502d007c86040c646001d40c01448103201e0f81e0400c00485080800e82c5001980001c10342d6107d0300d842c0405860131000304c001c1e51051040d050095106c12000407a626580230394400700988075840301074110400d4169203043c00041c001c504004804a58906980720504450250b80038078040d0403080904000c02d50b4000d84031580c80300c41c41e180c0b030100041d10794042003146605102e008044910790340d4a08004540305030481e61441d10119070440d1a100c25061903460954190b50000f40c10042601b07020b41c14501d4250043c0c0b0b06644004140080010f00d01c590705c00500360b40300c1009594103000d00700419130001c0e2100414541d139103890f4424803107440c003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 152180773 1250 152179523 152179549
    0xe01050d0602040819050607020a02031b04060e090a0b0a050618040218011e05030c090a15030c0305010b011e0903170d2322080307031b080103030207060c02031b 71
    0x108075560810b001702c5a0400c060022410341c0e4600509000ca1582440425500d9480303030021b00400c1c50016902c1c02c03030b00c5440d4540030107500c00d548410000740041962146071103203c0540103000c115090f03046c41001d540c801005201d410345050b003000070696130803e40c5c204080d140b001e00034060380c540c4040b03000c80c607081c0c403400c032500014400051802920490035042d81c469091015003540d450051698900810114a44c000c80200000351a0b21035a4489078039081003072210a1955030300d444200d0801303000d80064400380d448404096207543c000c83d0040c0d254020283c003201c2c1060701030008026444c47c0c04000d00b120340c100d809802c0200030780c05407850114000300802c01c403008551004114544040030140410703502c40020f410000c440030000c4c0030301106c1a031300c040103266a1980c1c002e52000b030410050540d141803180144481400d8220101e881d41c80c2c030344c070035411810080e190904603400b407010050a0030100c1d0060b200442d0440740044074a02080002130248009403000c6000c01c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 152182023 1250 152180773 152180789
    0x6020a031415040b0f0a03061104120302060a0507050406081810020a0327050304270e1e0607050d09050709050906011d160c020f15090114040e01050d060204 69
    0x200a000310071420600c080102c1c80212010001d6501c95401e1002e0716000a49071540320881000803c0490201c1c4c10401c2016200071003580343c0307920b45603c452000c0c0344400550060303120800f0080c5248007440340c0f507040280740c101141003901d04100103009050042c620028003480b4804480c0703204081209081c00006480190b40399200201e008004100345070320420050f400305d4505c0d2541c07154006400001c0d8100b000380d40b92a00300109204070b01407071a540d0050300f10340301d164108820b03180b24407440c00d108880a8408005852912203501c200c1a400e5101a08407109201d022900401201c0030390203548004180d40c0705a0a100e0f040400507400051114181030400c0000000462014103032078034013030221044058500c190b9100c840231107402d94109044007144180f0f60050a0030340f20707070340300612444401d016440898548c100d010708d00900f19002143c280304560304140b0085c80000ca175014241024a402150200400103101d02d80c01aa10203403c6410b0245d260100c1d00036120381c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 152183273 1250 152182023 152182061
    0x20409051e0d02010605091e0c1201090209281403030706060311090a0e0307030503150a0906090e0309090f0907030c240f02060609060409060509030901080601090f0306020a03 77
    0x1c960200d032208001880d01d401546450300202d080d00c3c18509850040c4011130607140c6094107103806a0b003411010b08040c058403000d0106950748155040024043c2c00801d0001d0785030780d0340303005200c0c0b92140c4e0b0a803440708490740040d000946103030744408030454441c1e90003043e100c0d007000003081c118843d19101034069820603202105000451100401b904030950700390b84503644040d014800c41f405c40e80c400c0d030701d500100034040109120300301941d00180294403c960041200e00003449614055100082194881c02c00300014140361240f516002d60754005503140c040000300203a80c1c0c95009180300b0303020768110041010782200300910380c080c0d54804840c2c426107455106425190b040342c0800202200c000c082690f0444c8141817000c146c0d90300350010f00c0b5503100c2108001000310002c154540142c1c2e18840c020105616004240c0600035000145507a000701d40300040420000a00e40c41c1840011281001002c201d580800101d0760030800c0141c0300d0b200c9080c00c80262080054070001d242c08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 152184523 1250 152183273 152183323
    0xa0318050307021206071409150a02070602060c0c0717030c0313050a1a09010c0302210702041103100603050403031b0806010809120a12020f16060b090c0702040905 72
    0x902c41d2500880b64030358001d040405460340c60004407a0400007428901f17039450741d1216031015165481c0010006064200d030500901456001001200300580c091842000b45a4040c03082540003901c0480651801c140304603441c0d030301c4801d88180c0b010314503589802c03000e10f082070082d103900c11024826640d6032600f41c0020300740280c9034007645200e10600c0200150480c541444141840503d010725810036000000542d05040d1001e400c4e02503004118042102c480b01c181c500500c0740007003911584440b0180140070440d19822503c15402104000f07110f1090f026460040841d521882d0100d0669114923044018081c0b40380e211042c500041c0580240c1504031004c140b10380400e0782c92030602e544400200d03039503c207099422220000d08008000c0f826101d04504001903c182d2070242ca00307500b0030a00c000d29400b0f42045003140751201d4100c010406140070302c0b146c200040ba0b05046078248050030f0006031140d4200240700c1d0341c2e66075515013000024000d40c1100012a0441200256 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 152185773 1250 152184523 152184533
    0x80303180a15050709090f06081204050a0e07110102070602090909060708010b0714030a03020910050309070504020d0b040f0509010e0f0c010c050f03031006032f0a0318 74
    0x15240d42410291100d08a501050006901440c01d600305089048502840300c0007001000b01425001c10401c40c03030408500d0410500407160b801c1125500055505c0c034082c5114241001000c41d042e00d0308041004001c07984d00c106660080d60720b01318103174000b034842441c11380f4121f0703180714000401e500108111081c4901640604110401901d002c86c03140d980950071a10b50000f1504007021411800c01070000c000d103a0050024648526090700c050713a00d00c80e10508e15003001104e08000380d00062a1507540c10301c01005a003055035414080d04609007803560700c1d1294285d0040c1c41c001ca50129802d07680290b5078020000390803014000304a5100781c16110000381008880d04921517080840180140034000f807881c0750180004041e01c280c90400c801110005440c0341d06403118031900d22084508141803000718054600c03c862040d1003854a20058141c40c13000078005101d0145503641030403001c00c10b8546908000320139a55598118246045d00101454040302c282c058813002d0900c1005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 152187023 1250 152185773 152185777
    0x90703080906041505120a020304020a0e07140c06090d020a0308010608060f06030405010c030501050604240e1e0a0f06020a030c020a08150103020f09070f030b0301111207081605040b03100902040803 87
    0x400e40441c6d803641da1a0196082e0320003038034002e400484e1024100301e040504543e143e003044031460494181503c050101049030017101f5041e00c50782081041c4902403504008807130300c01800780054449840703140c5001e40300326014403c034000d2147d9a4001160703680e03034000c4007000d050300804890712820b00c5d08203140209507100300c0c0004245041d00100f521b103040815501220307040c01069250a0900307840541030b00070281000203000c0e81485406003a900d49580e80c2c0c881408402469228032190200841202c082e8400b150780e2089540c00e014040d40826950708454040c1000d03407003040c0d03620205001c9292a03000724100d000e80401480074407450b86940f13048034004c48203078110320720401c2080b580d64019204000401c0700e0307010100506020740c1100306036038401000001c2010408003500e54640c080c042481c0e2000340d80c420011007641200000d5048002d0141440c0d415106a02c0079110f48214080d011442c0700100000351400901c04c00030000d0043d400040d900c4a598100030303640c036 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 152188273 1250 152187023 152187037
    0x3080a0809011815020405040203090307110406030c06111509011d0303070822050d0503090613020306130501020c39220b09040309050f0603090703080906041505 71
    0x669000c010600001c0140220101c100c600203100c07150324107540c0c070300032000b064200c510b82094092200140707503604e9101440c41501d0031005503a44418130b20b401414000340c04285d503c00e61418600f4400b1501043c004000d0360032a05240c582204c0e440c0b001407800040791102d001c2c000c0200c040044800341074100c4422410075108501000e140b0010706505c03030104445900009101d4400655000c5482182e60011201803135104d000c6251901c13058109489450302c40040340b000020b2080200d42000700650040f19000c2c906510515030f400a51501c2e400b518070058500048070724001d1000c2941210054681f1004030b07882820080e1300c450384070840400a26030381001c00c1034101001c0b86510003200101d8002c0101d107a0f07a1070030b0214040161140f00401c40e85680e1a5000301984420b8403032406580645c0710a13800743c1ca00410006804003003407080c5d008032414424025210000a108001d0742c0e4458540c0d0b4851160902040b150700139984100100900c9031030009809422800a01d10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 152189523 1250 152188273 152188277
    0x10e0916060e1212030c16051b1e100e0117040b0f07050a0c170405060d0e010507020a08090d0f05060f07020d0c2a091a03070602120409150506030103080a 68
    0x100f00401e01026480d001045400144440104000b44a180380c03034004207036041d080341340d54541e4a90368503464580064810081030549000011103114680a41c5020f50701000f046120717401d205013804900c81c0e049400b520400d00520300300340c0429a0140c2800708900d03165251980051505041980340c010041d1801040314402ca0082071000388940308850002c0d00d82d448011640c00d15541d02031443c482401030035100041400701003096500c0030010112401c410702e000c03a10000150040e801c4400140c0f000301594001400c01c4001014403081d40c00c3d041003150246200022030174142a418003d24004100f17000b1b80c1c0070070041040100340349020b140141c0c2200d00010350750500f070314007040e030f004081c4c05060502001c40c1e409032000907103000300c0e5030090b260010556801e1084203886e00506050030b100900342e04242d443c2010008070004200a2005042456604d040d022b030314841c0380500500f2586840b80016402007000f580c4004020242c8203980ea50b94905144800d81c00010703161700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 152190773 1250 152189523 152189539
    0xf0f0e030a2102010c02061503010f0c0c060606080105010c0b0a02040e09160e131203110a021f052205010207080a0c02030d021227100f08070314010e0916060e 70
    0x342e982e205110f10501140913030001c0a5988030185851891241c850070f80d40c2c19901d81d21003030301640c00c1d4062181b00175102e4903082c50355245468808252501900301d00100899140104446ea1703000c807001003c644c000504200da84c84000c1d014010303210395006a02d51f03024407018050780c401300107030b00c025607081d070030000c4142234440e110324201d550140c40500ea0501131107260f03004070b17001035042c01c10344505003800110792040165a46c0150080900040541c001d0707100d08190091040c10080340002729001009107181800414440204151741a0100c401e8241c1a0003004000d60440715110f17080480303d030f01c420b50520000c01c80ca00c02d4801b24040c2c0030741c890301603015000144414544100349100750410303000310b00e1038905141d0705207180700a02001503100401c5e192484440f240b2107003640d407160030050030500a44078150190102c0105407a02c1000302400d10b60404044c1517508916041500351110781c03000d45840701100c040b60001e2000c0300001b60213034012140c0304001c1c1083d942c0300c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 152192023 1250 152190773 152190833
    0x6090b0d020d0f0537080d0b04330f06020607030c0e0424090203010503030a03110435010e1218120703030e030f0d030b0612090c03070501030207051b030a1b0f0b04060f0f0e030a 78
    0x42c5801c0700310722074003001d63b11010100b484c1502a4200e51809030782880c101e023100300d19200043c00c0e910000110491045001c186035201003070801102c014040030754080d49194500030200741c0c1d074071031544001c04140c0c3d10000c0b03c441910780c6080f5070040c56203210b044104180c0d24090000020104801d0076082c02013514200e040c00103004613003010005034080c180300d98024511843c650f1203038250841c28050604481120b556040c682d10850000100030240c2c1419480d0240c640c1800c10384851103544280d800070304940d000034900c0d90242c040d01d808507040e0001e4000c14060b00880c1460001060b10400704044c0e00c000007218002400200c0031591580d42d55001503040b8425108085d0003504010344440d09041e035041c10310810031015007210b01060041d102c0c1d50b000303024440c00420003103c00d03038200061114080950042d00708000424902480c3c51400341c1042101580c08003404484403250300400d009050030211618054142d0f1200b943c5d41c6002100d14600341d0703a40c8854000380c0000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 152193273 1250 152192023 152192039
    0x209031018030309111810050117010605130f031a1006050403081c050408040306060605190e0102010603020406090b0406090b0d020d0f0537080d0b0433 67
    0x14030322819a81d80a00242400358070304801920203800151002e08052000110319100c0c4442d408801c0c0c0311048101c8141403c101c1d107107c4408640c042410804a074800c0c000c554243c002d00c41c1110194100155682800b141d6050144000ea021030000ea1100c0350000510125600d51044054001d0b406011a91401604010300c0ea043c0034800000d003081c0001e0002519210090208250000003511030302a401c400c801542c90840c0d003141c401c000400e080040003d00d00591001d440b035400c1460420100000b221501400c01200400300304401c0e0101a42d079000303502403005190042e1040c001c0c1d5403100d5600003d070940030003250040303142c0074001501d0101e501c07804018881c01400110844015001c0029030000a01c0540e04a00650075010002c0c10820090900380d480c2c07803007248100c140c031314801003032584004910901c032214409040014042d608440b07507038404800004085c0340100110b070040042124071801d2010312007140d2003240f41582442e252070300b100d20f0581456101e0001d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 152194523 1250 152193273 152193281
    0xc160303051b16060309020a03050304030606170102030912090d0b07030204080d0c23030f0301030b01030605010b030702100e0a06060e0108160f21050a0303090b0603010c09030f0804080d020102090310 88
    0x26691140328041083c000d1038446e03003280811600003802c01c0007041c0c50351143d500703545c0310794812601c4507542c1c541001581c5542d143c0d000001e4120f00214107520309650000c1e02c0e880d0780d1000e6981c044c00010b401203659600320340d48000c1070b00f0030401089403401c540094025840390080350a54421401d40a04007486441047d050039401480001805001300340302404d041071030b000310345500040c000007221000c80380103103000714090708500c0300551540c203080c07080b100183c12252414400300108000c1d207400243e00754142c8440d0000044140320b2261060500b600f0040041416080490001e18442e005105038141c41d01d00301031b0340440d0f441c4c5505083c0610703c1e2282080320407503810108540d010b4201d0054008001440c00321030030040e6a5184d0521040c0641180841d0307442010300c090140c2001c0072980032805500130042d5411b026405440c0041c2d5210041500c0c00c035043c20b0040040e1002542d0080a40c0790845100c8064188040d010b07401070540700303009128034200d469210050303000f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 152195773 1250 152194523 152194543
    0x60605030a050a020607081b0115121a04050f1504061a0904030f2006161404050607080706060e160810050f030c06031006030e060603120c160303051b 66
    0x1008083d690584d03400c1c01a660803504091312008401d00811000c009501d0308851043c58001c000500700090741c40d00003002da055042040e581c0c089107074a40004480303c00c15100b0f05c510703603500002c941e180d140c40c502d008500c91120b05075000d907290000140080420103400355102c1c04050020203005a0301284d48881501e00f25070100c098004100070a0190340b40da445003041d440c000420b40490600c551101c0c00e402070140d820f501103001c2100d11501c00404440c40782c11440d0030303910300091082d02c010500490080602c141070000d04082000710715405c41e640541e000c10240941a5500d10b00b0700444011221080060341c02040028841d2166070601c0c80343c1140c0e0300070800e180c14481070013008814049003c0c2c040c800c0e03c5206400d562000003452054002d10100c00c101428a14010141c48161492905a9001e40c0920041c0d54002c103440c47c81949003c1e41d9920740400ca1030140c644039141c00c2203003c0b08140c002c08001d0590000051043c0c5400c0790100200395405100c19a8031507103a4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 152197023 1250 152195773 152195783
    0x307020d05071b2d030312020f0412080901090801111206010c0b090d0905040902060403060b011707021c05030f010302090606040305011b020706090807050d02040f05040b04060605030a 81
    0x106414211501480c0a001e6250188480c0c05120a400c0c040303083c01c00c620f810024007000c0300151000c2e601514441c54406200142101c08910310b565001780082c0b0703902402c0303002c454011851406804000c1c0c1540d0040030008113543c0b00c1c201d142441c01c41c80c2c0c481f9810600003013a0500105891038140100c2e0010089600c0407498440c4603680b010b034000d0f000e4409070400250403105404540450001401010014040d00c85420f91681c05008584154890350040b401c05140c5005642d4000540342204c0d08100d0220300782001c00f0040302e0000311100c1c415800c40880c01401081070380040e05c0c0c01a040d1a0442003c09044440140e9103400211214050072000310018001803e00d00261030308600e02030302c401e05260300d0ba510582555480d03410b01c4501849948030408640c0d0410803400100b0761410301009481c00c00c92880d0300c0300f80e24081c5500591103414402c046498550243c4111040c42c10100450b09007407601e002d003008195811741d1118180040400ea514002c5482140c03503904c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 152198273 1250 152197023 152197033
    0xc14180f031b04021312060b0109140303040b0309190506010810020c1b040e1b0916020717070902030a020310080303060a030308090c0d030c05010f05070c02013605120102030702 78
    0x1000402010754400c03454182c00e417000a1001800284620031100c116100e0744000ca00d0300c621000042c0f03044038a52066900482c00706004420392804801c44c2c090750442c08010b0713600e0396000c403a54035010f4814415020000291000d000740300300428a41d05a80c800c034262014102c207401c116040c0e000300548088503400030140b8965013400754004880c0803402030400309104c814060b40c04c0c100328142c400041554100d100c2c02c0c40d07a107084c40b003c5512024410b084000030100840095842065020b44c0131442c6451a41c8032002e00200041801002034000075541d82c5400307021600079400681d2040d500c02200310002c2000ca0303010007560300c1420003034420040c00d0300e5910110380554000c0c24100e424014220110482d0300e60b100780a1a45000761070325641c1c41c84030314156085034880d0907940726140c6003d091003031160340000d40c1041550246098aa07d0040300703800102c123145000d40307036900d560760503050900d035021895075022038208464060b6103055480125003070344030881c0d100005800c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 152199523 1250 152198273 152198323
    0xa0504080910020a021c030305090109030c02100e060a051810021c0309020414091c0e0f03031b0d181514120901020315031504060c14180f03 62
    0xb41200401e40303001d510440b880c200c125000300d81040c00c2d031100070024103101c0b01040d082c907400d8000c031504084918000c0011407040e440c01405900030308c100074403504d844100f00b40380c03c0c4541040841d101c07000b08015901c1c10310603000b50280d4007000481c070801e059445480000d2412504900348010b0780d030080e02c80d40c8031045401e104c2c0140350700654245652542e100f40580c0312407041301551510030300f0134012401d115210a24244000d24030395403030400344241c9000503078403000b004600501038a810707080c9907841000a0650141010b040c841180d0b0f0745c00b00488400000305203418001c1520748812038070601440001803060f038050a1500241e81c1c0c2000500e9205d2242000c60311040d4071091709000100310310350618101a0b40c507408503074000c02401442c10210411440400085000301861a50b4964154040d6001800901480c0da070301034460504d0300443c400d00900c01010910350741c4091860000c81085030f208182c50140c00d0b0b178501381d001420009801042405c4907801100d001071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 152200773 1250 152199523 152199529
    0x40201120c05040812180a0b09060f0904050a09030810140d081c0506091005010f0305250c0b010603060b1c09020901090516030501061b050a0c0b040602060a05040809 73
    0x20041c19100c1041001c02000600e100c05210f042400c0c070360112280d56070071481c4100440d00354540d510b2482981c41c0c190411808442078112040034000b07580582c0c80c0e1080d50107004c1175002d0008500c0e04142001d003000307074164150703001358241842a01d0300301440e10f50040c05c68648500f4050f607008031800c3c109103125440c01d82411080c861064411900d8031002454850a41218454420303080303031a40c01b070202a2030130178111544501104004440c03141740200007000038601040c0d4809056071480071917400c014000c1c0602c00d82c600e20707000301044c0e900000020001d002c600d205a503c074040700c0011401c0351090190200301d48000c40c3d52400d002503c40d03001c42c90984051010030140d0340d6111100140c686c45540c1e070080100040014961409405030000d00e4030414610041500c1c040052154580010401d201000001040070040015203407440c178020758020081e0003503500080019850b01208010401d0300e40e95400da075065107440f113070082500e2055070b004258640034406025182 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 152202023 1250 152200773 152200781
    0x2160c0b0901090e06151201060e0f06031306150f05090c210c120f06040c0c050d03090f0512091f0906030e0c130605040b01020313050630070306080604020112 70
    0x240300820b1030000b0910400142d059500c0741103c1c6000540d180010400c09e03402c008001e44942c3c050310185800d84c480381c0054118840100b04c1f281d0540f080a010082c00400d90140c400b03141184508041903813105440020070a20340303c0d5134403030318041c0300140010381e02c82c05413004005003800400e101c1c038007000c080d91543c100814050340d0680503c40c1980c0105900c1c070150041020440010240c1407480a00090b1030180b5215010b00070280a2903001400c0003c00701c280580a2034005100d100c5403500494400560f01d001e0301794407651300b0040da4000c100e0010400c5110850302c43d10754141d90141c104040d07011481041c0403c45a140820803503020741c2162007294405002c0d11030243c00307800020100ca048002c51035505641f4601844241882e106508580707901340002c50404043c058801000b2669000b014010312012030341c031400031103a9030b452000301d921110290318060540303030191500c0411510040000d08101d4001204400420703894001c0b070301a0b4404115840800106003d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 152203273 1250 152202023 152202031
    0x1803080415050f0f0108060403020c21060103051006080a08070204020307030f050f07120b030c1003090507031a0c0301210203070f0b0d0c0503070c120e0402160c0b0901090e 76
    0x1801c44006161284a0382c0300d00c40c4641d9080c500c032403543c00c1c40b11001e207070180141c01c00321781e03035001c01c003400b010075000142103802000442ea0142c801030812507151015884061000040c82414004410008003154403400c200b22400100843c3d60b483e112181c1d180c448200c0902484030421881004d0f0400344c00450b80000c283c107001c01c88510101e8050104d8000f21041000100ea5170300b4419910ba0050743c4029240d5001c400303104506c03007040000e0704c40002d91162031142e4010004c0c800c00783e02a8000a000303c0d08001901c0c00729a690070b007908100c100920070920b00f404000004e0540120740d094134142c500c0d007621070b0000750543c03541120b1800c1410050b0b03858480c103100021000d8821900b01e002c0e10a104000340c803034150401c54019075080c103102c00e0078040300380200410b00f0f07070001c003a80d02a5045082116450b102690988a0300d81480700f95410500000d101d095444a900010001901c205141e5103035071f588400c0b00c07899002e4009480d0000780c40920030440c3d4440c1100713072904 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 152204523 1250 152203273 152203283
    0x7030c0e090c0304020102060a0515012114010315150608060a081b030c04050c0304020d080d06090212090a0b0105060c07080a03030621050a060c0507060c2118030804 73
    0x8540d500081c002240844414165050000400c01156810b2240c1074004000702d4050216042c801e0aa5400c041109801410025105004685d444c80340000040140c603400302048400b200c2040c0444c0342d1402d0106032a10301c41800000c105600b244500300e030b9212569540c070032503130510908440e0120043d2020f50b0245030704802040070001803220701501c00e000152554603101130340c14142804007445109101c0d51078038081211049054040b690301550440c1c208a8407080761400a01360f000b0401007204852a10001040e0383d4201ea005000045031a01c00c000c0568078801c1169550310402c3e401400740300700c20010132603820010040c2400001d200251009640c8401810346000d990072002d40001c0c2e05c404040203241c0c41e075030021085140000c0020110409606c4880e81e55001a0f030040000750f444403000c09291090050350b44850b40440c09018000140c10020201d07030300f280c041504c00d1029840e421250f1010310803c0c035122294113140b06244034a880640e5607510040061720 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 152205773 1250 152204523 152204537
    0x6010f090f0902030708060a0e010e0a0f05070909080d141003060b060706090f0606050a0b071101090b03091b0105070215090d080304080703120e0a021009121a060a030b07030c 77
    0x44e50148070b48809000b10b4801802d1914083e4441000d8404c20f48d4450040d901d0031030200c0b00000301003140480c6540000e04c1c0150001d85103441454408294002c07085c05182000010030400300c1002451482c3c00140e043c4040c0d40403108000080900b50b03402400c03091401d00400002c0e03025001440c6039080240803c1c20b1030381039100e6605032403200c1c500711010100c40e00307804200842d81c07003160b0282000f03840b001ea145007481c488094034803c005000e480c0c0301038441400305c3c980c8109072490282c110005496100c6c102901030541c0c03114410741000300b030218080d4880581d4428400d0b2080176030024800019400400c600c0e060a5000255450308a8032041504001c9130264000b18000c61142046030f40e60741d118100108041c0c031361a85040814144903960810703000010303120030000e8040354000f000138000d03142600d5094040c0c0c411030100809860740002d000700d4042c6680e094210680c4107101d6550981004003140050000400720011203010480481c42035001160301c013800e05140c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 152207023 1250 152205773 152205791
    0xe0f131112160503070e0108030f13120308060112110901120e01020304030c122c010e0910032901060807020109082808040b06040e1510031406010f090f 67
    0x98109042d052068440036101c03402088241001c00c0160f00600d03514401007140e50501074019124490040a0020048081144810754040d00041801401c50741d013082c0d10034505213000341000d4001c980303050108041002a0313200d1341c5070b401160481c40f5440195841c110002c001034841ca00c20081e50105540e0b180f480000d1440244021405203000c2c0d12079a000c0d0f4054600408014600d010700000c1009101609180ca00d06036401c00c40f0000d500050140781c802940121480082c160005903c16044800c0c000f18141100c1d5030001d5070301a40010710604888203d001c00600065050000c4120000042050320f118090140d00f2003200d10010408950030744547c03120780c001e00d03018180086510f0701c1000c810060190b4100c21666410320200d145826110025420402004d43c3d009640351000030004240070300c501c041244040303201c0030190405c011008464040c80c081100c0c03005240030600d00304400050594101d92141d58102c1001d070401108402070007560006580d92902c40540d6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 152208273 1250 152207023 152207059
    0xa03060801050403080117030405030a061a0406090e01150b090904030c0f1a0702012c0a0c03050d030b0105070b071d040203090d0f0c0b0619030b070305010e0f1311 72
    0x115000d00e02a555600b05541005003d50742041001f112134103644c400c00003041a0745001c91001b002c02c1d000394000402c1d89038200507030b41903901d907003134158080e01d0300c180441c5e90744803a03001c003581c09014002005400d124100420b504c00380c0340624500224180551403d5181c01c440b0603920034030900e00b403000c250701c95076040802903c0c80c0d022643c1b40102415100c0c010703000c00c90130780c0c402c0052000740800c45825424000b60306001c01190f040c0b07101c071402c160064508109000c0401d5002102c46c840f071703689003010f940700d880610303000340081d04118103009650303c40c2e02501c1d08582c012240d80c0498480000a0362115000ca100b8502c107416149411440e9a661000d0351280b1003040290280a10305040181502005400c0c1420f020a581c0950f0214554402d036903403102c4180c450408200758040b1044a8624a0b40010690700c00e40c02040001e03a4107400c4581221080d94505400380c507615601c80303004208031420381c0c0c2c1c6450005110f003c0345418101a03400c0c08080d080c034496071003003000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 152209523 1250 152208273 152208281
    0xa090203070306051e070f0f020c1c060f06030201120f180f0201080c0f2a07031209060302041a0a1404080a020901051f080a0605031b1804080f0a03060801 68
    0x20548106903142c0070041c0e1041c66501840102250418100c0c082ca081070007d400a14450040e9003040038001c50138850318020025951180c01c010420344da035041223907010318105100002164820f041200c165004200390050005403a4140c4401c01802c1d0710009800040802c0500007080a403541002c10004c0b00290b903000005001386850184103aa41c0009032a044003c0d0030340e50405c0e0100282501d102104055034007251581c0c10412601043c0745850107124040d251071b40160041c01382c00420032141c24600d048981141c0c17507042140b5a581802d5040f0300551240006d02200c0b0098040310f030181340010800c1014608010000040502040341c039034216401408141d07100c010700038158a0100002401031204072054039910f040b04850345460b20040f05c5420030701c4421404600e26080c1508210081c01002d421141914440c0c20042c4000c0920120640101020b40841e02900c81c0351200307a1069810145185ca06480031810b00061350001191a04040c0c7c0c409011544081c2806 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 152210773 1250 152209523 152209529
    0x703030b030c010c02010e0d030e03101b0e060405010e1809010213090b1804170d02120105060702030703170f040e0103060b03030408060c0a2d0f0509090f0a09020307 73
    0x50005411a444414145410b192001c5141445829040e01c0010b1b07030700007900e0381c0444c1d09542000f40300b20103213010b41c3c00d0300c0c000c804c2c6176144c002c110203040c0b000902e52141c040c607500c084e0b8508d081c035000d09055402e16a070042d0a600400104014071095008044144440c80040e0100d0303101c00800c559811903803826503980ca240d075000181d0042d00e80d01482400080d104088c003c00603112a00009080040c1400311030000ca6040c00010341030100350710000406140251540355940346810041009500c2202c02102501c1070300b00104250070010709880100e94054001c0c0100e5066807254000f04601c42d849640e0307038030100000100c90404030007600c000c0c140441e2409007541540740050680f48170300c4803903000b03900c244001c00003c400000c1ca20b4111210204890352140100812500e00c0030075610b4101c2c41c40c8080c42d03c4040c21400f81c45a01030219a0707208124850742c21000c41c0c55102c0d6240c07055100c11140c000c248008980c40307000e90001c4800200040340003407540841c0c100b4103da4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 152212023 1250 152210773 152210777
    0xd03090507051512040204021b150f0435070303020705070e100b0d0b0a12020907030c021e0a061e1407090b030604141305120c0a081e0703 61
    0x20001004025042111002801c402c40d10010402081a4911524043d01d18245400c92160001ca8155100e5904861246200c49403407010191005a615550b00f1220545441110b0b008000b40100e00240c8000703025982c0316039642001140c0d110246070b001e88032070141222040310400841d9006041c5c00811540e8440e8401503160b1440f800c01e07030305003c0c855020544400300c1b401004054041000068143c0300f034082041d481c2c41c1840000d0001f0036030000da240d0021015a0013103840e0b10340c0309a051901d44222505078069a40314421019250709510600250703002402da4001110605e04603500b041c05c92017112405c1072980c0f032307840548900d01d40450304c40b2083c5400d00750346209401a0800e4140d644c018815600744101c005100c102640300d80141c00101002054050b0fa540d00040d00c01031601907071001a0800303190f0700c071403800100310884480c81800c0e01d2524440c10f035130548c1c4040c1a800003419290b52141c0b40d802d02944410380e440e902d241c100b512042c8016600d0080e110306800380e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 152213273 1250 152212023 152212031
    0x141018171509010501080c06130914060f0301090506060d14010c030212071403040b06121e0f0115060503040c08010f0209100216180b0a03061b0c030c1b080d03 70
    0x107560340c1d48079a002426841c403a9042c00014052040c0005005070307042420b45210b84d6980e07259001240780f1160b600403407543e506106030303c00c5031041041850300036202102c915000046502c00c1500b00d0702c61403801007e5811040000c0c07110b142000040c5506400703017200c80715480c4a600c03060b0844088a4040010a41c04a002514034080c03c44265000c9000c5c10000b041e512050000302c0c0c14080103000402440c800c070005220382e110003c070845a03062200c100d442409520104c0f0b01000c0300c80800e51541d2040101d48040307545d050084101c0c0c803d0f0318003035480860070400100c410740d00c0240240c65440743d804001402c800d09210780c00100703000c0440140c42d00007001c00c010040d00c04584040440d8000c400c842d01e200141640d503011504170113014102d22040c00c15920140c000c505015903c000b44040000500000f42c0100003041010003a100c91504c0010060f00e25006040b0042c000500d68000200040c403401c0368000d200e0011103950740340320354803c04e032498480081140c0d000a912 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 152214523 1250 152213273 152213293
    0x12180105060105040e010905060a2102010e0a050f10021e0f0d0302070503090909010f020406050306090a0221090a0c0303120c0801081011040812031014101817 70
    0x30311509030001000d1802c145440d00d8102c014076020030600074104201c2d541c00c04140341da9108210302c0000d00d04000c2113500b501948449010b280680607003680480c00d1540100410f181070308050090707541c001c051103401044501032069081d1501165015881070036518808040b1085e10110b0f1040d0003001170020b101040021401c00d041c0749a005c080c14014050500014001300c141c0d1100407003030301d5031040f40c2d940000300c50250410b51303070100204e8030000c0d0210301141d10400a611900d8180e071946a5a102c000e41c18041348a400c0c070b140c4a600c00d103111080c030301c0c6050710000d400c40034090848110203d691100203801ca03071640100c0106d00b031454044801c0c102d502031264410803d007480c401940c0742030040c585900a03030f045c000c07400d0307507910386152104000001c1d6006051042c003116400c3c121800e2105450784142c604411906d000303140043ca1400302c2d4215201c1641c040c0141055070400007050b01c24056916003000400c1ea4410003040740ba90101e901481903520320010881412 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 152215773 1250 152214523 152214571
    0x30c060310090e0d08010e070c0206030c0c071a1204060f11040504050906061e060d0213080f1204030b1330020a0f0201050f0c0a050d03050f0601121112 67
    0x10f000c00038603d4a40040c0d481e100000d03004200a81102d07100550f060f0340d50385440c41280c0d4540080002507200b2404414000c0d0601c001c0054404260340c40c04842e01140c0f034002c04000404880d25801070700700104010780a582104880e640c00034810500441c40c0c00c1030001407416680500b000d0030210303c000c6010080e5141a015694000345190090704031350520380c0100f1405145409031110f808400d2841c2802c5031181c1c0300700ca0540c0211b081c00c5480e034540300c800308181003e900c1004d02a03c1180303914400301c440880d00000b5510201c010520382851aa07516035a01070040c4075401c40e458452a100210f07410242c14500c81c01c1c0a8441184842003001c02ca040600d0961141c00310751280444d800003070ba0500d400c940c0160242006902d424103150010007600c100403a032041801021420700801c9000109030078004295201400140c1d10758000d1000d540c0d048480c0c0d80080d840c92400350383c106c00ea41c0484c0404800301c0000e0b2902d900800f010000d0700c400d90384150501111420121411 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 152217023 1250 152215773 152215781
    0x4060501110d0311070b090708060f15040c03090503031618050f0609040e1905071d0403030f020405030a030c050d0309050d03050a060513020a0f0201020c0307060b030c06031009 78
    0x420242041e52000340311492460780c8100d4407020303006040d55046201d2520012100f41d4820b217601c501e844580389011170006d03440d00d09910642159214407400b04100d5005000c0e814420950b80c440300398600d15000800c000b409504420b001416541c1c40004027140c4240002c500c07607604c4260040307603401203088c000d0045001c581ca00c1c0303181950010174030142e520f204c0c0c07002081e601250a60b03120103103003000900801d0940c01c1c00a6610802041e45002e4030010001c094850086054030b030001e80c2c030140c00760b2505000c0d40c00d96004002c18001000a40640c1c01965003844200d00182419200c001103440c050355100242d0118400000c405c041240c2004003910007e46803a040c85134002c5617030390307680d0b40e011020b050080c140c4440018064410b154420801450014800c5c42c1152002944800039408040c8000020391059641e40c1450300500072110080215002586801c174143c440d180107000d01c0a250380c0c0342c01203143e03089103070f6075210142d8098554031014444c01072038010464119 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 152218273 1250 152217023 152217029
    0x1b030210051c020a02070605070c05060304032106030c0e0a06090c11070504090c0506070f02040f0203090d0f0207060f02030903010507050405180403170414010905030307030b0d081801140412020406 87
    0x303030f4010009a03580b26130114800341150102d082c0503031515228a40568a80e88582150b900600040100400e0651002c20300c8511603400510b0700742c06903001c503481d0035030b1017600000d010a041460100414010040d9a5620401f960b00004d8280d0300d84c0d842c0c000b030b10f640704045000070351807103d40980903205000d4000208402c071802c01240086030780360b8040c20518405d07203114000100e460810b00c0000801d5080c40d43c3c0c010801c12034903908983c140c00940056960300d2030713480303500460a0341c2402014248818080f94004101711803a05d042200c3c46055146011704501040c4107101403900d00340242405a80715895540c0c84a09203c02c0c00080804298112281d00d0320300c090101094101800c844c01d041c018080242569440c02c100d4402d4905425a025640c0b13005071000c01e00c0b00c0400a54041c002550b01801110011410020307a4113102d50042c21034002003110b001e8a016103006041400810b06140070a00441101244a608a80c0c0010f4514a2024602c011868240f10358005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 152219523 1250 152218273 152218327
    0x703120906210c14030106020a031220030c0403020a0b030603010e0d0507020d0201110d030506033c010e0709060821120a060506040306090c05090708041b03021005 72
    0xb00304400c040729091110700108090380035034812a2400c194881e01040f4112680d00c04690b40d2540c0d0340400950310f1000c65020f60006503c5200511041c141d8000c4131900d602c1104e24240e901c0b28243c0d200d9041e800134041d49000c140c00c020000040c2c8614040800502e420604070b40c4070300d422801d15003035610009281149411a920110a9075000015521015016145410306030118401680c0f02d0309003034100c1e000392007210074040010380d150b0050340c42500203030252501c000013a8000003107036078a2019100b00c40e49d065844006180c0503003012a00c2d21400001003010500314038490300340b07411500200310703e60702d51400703211025080102d03084043c00b91880c0e02c5d03803031b8041090003203900840205500c0d007848a008108070a525401c0500034090040c03460f607075140d40b8605400240192101110403500400d40010300e80b900c400e0440c8598225100c0041070b556035903035030008010b1001d180600c210303241c0740032002d40caa80c08103002c480003d440d8141d0300d4480d80240e80243e0b82c0f184414034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 152220773 1250 152219523 152219537
    0x909030301050d08090a0306110a020709150b03040602160b10081b1002070506030a09140102070b010b07050307080d14280e030715020304030f08090d080c09030703120906 75
    0x49141c948090f0b004500780c0001c41285c56000080025031403400a52000c0c1247c3d040c14004541d0450481c020402ca1125408039480c2513601e1448009640007220510713003900403d07008110704000c00000f564028441c100040c03800c2c10501c076801800b08000d50541c1e400e01c1c1d0b401000400142c4d0000500075001880c01416409014076804075542074204e04070380960701003414800007500030031110f070140c180102020348915002c01c0446c01404901030944500d51200c2500e042d205062080b80c407080c0d01b1200003082a800d01800007282d84c485031084807036100802c000004501d90310041c0400040c448404203004100e054030040400004d000d2031808403455110030b400148ca1140344801507107081e008100711402040c0c050039130050311800380100040d01d4020200d000c80da40294442c40c444c0d250326904a8070001c00f00d07a008002c8440d041c2e682e20041d86076242038022034007503a0040340c80030103503d00140b00e0042820640030f0340c000c035a0640c80400d81d003460740c1c004491201500301d51074982 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 152222023 1250 152220773 152220779
    0xa0201080a02030f150102100e031e270303070c06081b190e010c17030106020f0a0507120222061a070201020604170c0a0b0708011208030610031503030507020909030301 74
    0x100c03003104c0241101e46508840b00c000c00c5540d0090041c2007090545c001c042208000405400352654000c144005024038400c200d08440003100f400c0d0b60301d07085040c9910010b91003001551b05000b03811241241d0601c070521041002640b403c0503540603000a5441b030740b103410003920200712544030100c2d0f400e10380320502251500c003040708510306502065190005801e20320b400140c40003880648050140014100c030141c01c100030070000c50480c0c45a500701c0f8071400c03400c1c500b943c423809400300c010941d0300025420060410110740400d038003400106000115440b551291919860714441410441d488a03001c00a00341515a0310345402000184e50f89440e03642e0b40000c2d120107000300020100d2291740114811070070303050151070440b070988003113500c0c0c01414209841498070440d070f80000942107400204561310418545101107038000c1c1c24038150b445210070450551140c14103201010b549908540c4210360360300b599001140207444282d0740741e041d40144200b5000040c50300307030305510400c010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 152223273 1250 152222023 152222041
    0x62d05090402061215040906020c0f0f06070c03021203040609050706050a0e1c061503050d020705011205060f0402160501060b1317030906120106020c0315011403010902040903020a0201080a0203 85
    0x4a42e14801000150851782e03803260710307502d4405107015a50700b042c42d020f00d940800c2160741c000c014000203d401c46003070714500d1303031031665514a034030385000c1c0c43e04124003050748140030300c8c140049248203005a42141189000000701608200c6080c0c4241e500c40080c00309004090141c0d00c0a480203103012403901880920140c811300400d2803260042a04410340c5402d00c4400f440d200c0d81c00c0e400070050120f020b1480700781903400414041900d00380644209004114000540b9204803601030715515100302001c00c901d4000c00e0020002604003902d000340100b9a1b60300e2000700b0542c611281c284148514504206086506c9078000c02601c010402400c0340587d40c0e0750201040392454461160f11810f0344510301c3c00c6025802c1c034035821850101d68203039042d1708071040d43e050782c4440d421161081c8425041668035000b0452100740d8400842c014400751410107140940e60802a00110b11804154041011298144400d40044e04400c0d000021980d00000481e0441c09108056042d41000100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 152224523 1250 152223273 152223277
    0x4050c091006082a2508070c060302090d0f260a020c030304051305091204030c050103050a020712030b0f03060f011401051e071403120f0c041d0901062d0509040206 72
    0x22104140d4400b003500720395406400c3d00442c101d1154107145d921109580703805c20064010705421140300300b10403000700c0e083d4402e01c240d8100c004010145c9081c0005a00d0700341d41404000c50a840307003000010079604045088044803555903820164a0b5a8910018000d041c18944503040703110f41c108200412181c0d40d041d00c00401c03000300c40710014550301e44001892500c8844e00c040c4405080108002090009040403071007294030a80303080c0102c3da20040c00c0012845024002000c080d603079155400e02d648660301a000700507026080d0740880d40c050001900d00351040f04d69a201c40722800040c0320030810440f14440d024801c0c01c140e401d04074050001000120080c1c1400d90034034020400d6814800194009508803030070302c0550f030b96141804540030700e045048400100c0070240002040c8000e480340d00301c80445160000c605203255100302400c01d8124007415131501c640d2950030100f107023010000b840e400c0c000100d0560903400301c203603a0000c621415501c4144207400c1c84042002584070101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 152225773 1250 152224523 152224591
    0xe0408030a020c0d12060f060c0b090c03100902040b030d02150907050406060c050705120a32060403020d081519031202030d1104061704050c09100608 66
    0x620a8a99442480800081c0070b626200b20051140700800d505007030300900d182007590741c2e000c2c0a201a944949854040c20458850503001884d0314403080b02090340c548120383c020742c0304000d580c0810b0084000a01d03284584140074041603540c1c0ca02e20451400b40700b40900700f00c003500541070b100c000e484003a4850500da40d100690b001d04000081c400d000170f1060300050400140100003003921004000d20703c002c4d9000841e02d502c6004000b08180c68418882481c1c42403900003040d405c0150f54490460151091240c46a50018295101000141d4042141c035440500041c00180391a0071b0080c41c0c185c99001440c1444112002d0080c51a0b00c200da10301c0c81c0000f40c4041e800850701c40c020344605911688045e160641c0e016049080c654007100a200c0c1070075145083c012106103124401041c456441000c3c0402c1d9500c0340c080c03440c60910b200903403180c0503a080d50703011440038020070544c4030211061001c0c031104400c03e0080d50341180e8034a8201100c2d400c0341c01100700d440030011505074469 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 152227023 1250 152225773 152225783
    0xa0e0f010903081f030803040b0108060603160b090303070f050f0d030b03030301030f0317071d031501030f0206040306050115140a0905010e2b020319050604060525020a02090603070e04 81
    0x521329041041400401005540c0407004a503240707401d04001451074028040c0b140079014270300208100b41790001c0c0402d21045a01000219989489500e483c1ca901900c0c07038075054002480010701058842c5400000107002e800a0301c0d5100e00b02d50702c81d08100003500900180751a100c4829525100001924196580310098111110080c10306881802c2801d81c9086e5454904082001d05544064004d15861807011009010500002016118211440f1960024004030300401c0070407046090000802d001400e03070f626298a940700d160a40b5000d8001c403811014900c0402c03c0c1c50b0f032010080300c1d050803588905040800c0d803035004142d0304503407142c00d040180c00415441740c0d60380c04c0441c5d086c044589500c2101c1446048000b0904529202c06030300c03e00600c8440c2101c3d21300201c01c01d90003544440500180e559994800002b440090110592041042c1c0c40b20501c803401c980c50300020180b41c004040e00714a605c10441c05003030080031940130780c1003050200020300d11403081e075801039842 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 152228273 1250 152227023 152227051
    0x60c0309090b010e0301021b06090d0203072a1203140405131d0124090e0d0c0c050a0b070605010f08030702010305040204090525080c010806010c0c0e0a0e0f01090308 73
    0xc02c0040364000300311042c50358107501c0012820078001000910502203241001a85d400d5628520300b01d032600d6840c0c085401682003003140600280400d003c03d1861004c8403002c40800c02d400041c0c5100c0803454101ca10782c103850314110402c0c550081041548035200255051400d420a00400c0b81e43c5520340c04400d00301d4840d01005100003043d600303e060b01d4580310003009202009103e0f802c110300c1d2044004070940c1c07840c4002c81e1035803c9004000742c0c080010000c182c1d084a002c42101c044150325001e80c2c410008080101d200ea40d0701b07403044c0c0104494058152a0b90341410300b0b50480320f060380704201030f6603d001c4c03c0258450200c1624101502400c00050541d45c0b4008070700074042e01040180580907000003901d402c0310f0201c602480d0040d59001040140e2544512641c0721907941c90240858803060010f540356100d01c0300c0040c0d0500c5031034071001165640d6501c0c081000140c910030b038040d450314000020342c0010800000480c5c0041c009002c0050300ea02e01405071030002e0b0000d200740081c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 152229523 1250 152228273 152228291
    0x2010302070201120f090b0a09082205100f120614040b180103051513022b0c080609100603020603150a0308030109021b0a020916170903090a060c030909 67
    0x4d4910642c2c8000f18641440f03429525618640240b451846c2220250054008150010341c103100f00000d29a2250701d02c0d28112104810440d4110407034034800d10001c00c0c40e4045001c1c4c50301000700064460076110005003918440d0040e004c41e00d124408020149028001c101c0140c804136101c0c03641c070b819180000c4101c0c8a2020a5113150130300449a402d075802c0c000001000720028a84020700303418818161640c461200a200300e07280e0603006075010000480c840e400c3c0f01012101c00c441c4903070000d003c08041c0130b5600c990a04143e80d2140400340c110004000c90200103201c00c040c0c1c50b80c5118100071050660f80042c034140405040b02c000b1f43c5540070702d07040f19100d940052001d11780005040f920703580d440c0c1c4079001940c001244100380c0c40320140c07500c210407000107900700050740c014212085955035039003200c5240501c040840c03c207c2e25840807540c91725000b003020301400720340e0081c41d0340e801201c00303010b0a050142d001ca810031082c0cbd00001c0c04a58440c000300140c1d031110340c011440c041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 152230773 1250 152229523 152229527
    0x8042409060e0616090f06080604021908180304030b0a02070606170304090b040209031c26040203070b030606040b0903070b031509010b0a200f030406020303070e0a1202010302070201 80
    0x3050340144003919246690310b40322000a0020311803581800e40c60684c520300c1c00119090340f082c0c8640c10580b070780300038244003040c041c003080340d071159020380014100100c140110640515410800c03020445030303414802541c90180b04071000c042c00d18010351400e49943da44500004009007940700b000e40c045a03910030000d840e0000300060051101eaa0584600e60b101941c5a46c880d00ca40c0002d1845e0102001090805000b5100300380401801ba181c810003602c417000c940d9200294010070070142c0b034090385400c0304110401c01e00159190380d640c0c80f07140c2881814589216a00450505601801040f800c0e50703480007102d06aa91080f0350b20b0329429800e000c249040c6107074105c81502500803007000808240c1c004a01c40800e0119a005071513640c85101c80d9440c42000400300c002018240415090383c0944180742e074051000d8212116458010709283c1503400c6034009100580001062002151f4451200400c0c0c140489400c140030f440c1c031050040c1c012141200038141900400c041e01568 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 152232023 1250 152230773 152230781
    0x1c0c05040203100e0a09020a031509021e1c0506040f03030e060a050702010c08010e01140f1c050f01060b030a051e040507051201051b1e0d060e07080424 67
    0x5000d4015510303400e149003500c1012040b409a00c075119a03c0e000221540413a010340c2842c242c000e00307103042d1142140c8548405400e503c0101070100e880703040c03000050b16084c002d048400c001c5544268000600401c02c095804070030786032007400e14884001c030040760000c21078a801c25405042c1e80c80044140c9400e03409400d0b112800d44060254404201c444412504500e202e000030358002c00c165640080103844020b000e001f81510140c0c03440c01405020120442002200001446030004000c400c00050b002d482c1009418091104080e0f003074200a030400401c2e4070900624001e2006906005107129180002090a00c940e500e5502240840c540d91241043d01c1004088460151625090480ea6201188546801820b00c40140d080d10081845254055810b0301d004215250302034100069a410028400c529602c8005002d90350000b42c00003408110009800440c0d21864521408259103005110600741700740f0700c04100004606014204110a5103903031000b0001903518020028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 152233273 1250 152232023 152232029
    0x203010b0406082716080307050714010509030303040606060905061204030f120c020d020d0f05030c090109120b0a0c05070503090904050c0a090509010c1b0305091c06020703110c1c0c 80
    0x40b5121303080c985a02c030400b08095450f601a00305202c40d09540b0345003941eaa10402c0c03405429900000e40512000b1010024140300003414035102e170810b40342070000b0341035a0042ea411109181c1c0d44808020203078000402800070001201c00b0350900c00200010004410020030040c2040031410508001c240590700d0700030142c8501604114103000103002075590914062080090320907502d4140050b0f1003120501c1408602e982c415056807642d42c80300035103821454525041c061500c0010521007a59092420214003076240400c442c01e14080500443e12100c1c04c51040000c10000da1001c501c1c008100d40400109650240703559a407414001d003441038040c40c560b404a00e010b000901d107003041d00000e0085110f08000c00c07050481c24004d50722403d443e00302d207603504200005400802c1c000d1002e03040c07240024000c0601d103034039481c08002d150449482292003650200350ba60526500c002c041d5407215001c1c00419400c00010001290790300a110100f0b941568845d0840412107984074030001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 152234523 1250 152233273 152233321
    0x90203060a0203100923160212090d120206070f0806090f0a060503010e1b0f030a02060d140408040e0703050f01170717010b030f031c0513050a0c060306090203010b040608 75
    0xc030405c1090760055006032017022015400034001c00c815400010407074a1f08519038008002c4801c155030b4031030360b80d0000f00350a0790085002050f0340125004081d0400c010310564094030a51501d100d000e45222000c40c100d0b02000400d01c10450f06807520b110551b008950700507500e01c9a601c07007401c540600700c550401754044d400c000b10741c0f45500000503030051070015002200034082d000c5050080e9030000080342540341e88141e5a1201500309103004010044c144000412102e0091010b8200e8510030b4070b04a07804500028100001082151060b42080203850188004e081c070441e2040001018065080324031114041076108480c1002070f0300050480030f0281502104148046008224040e1303058001d0040c00d0013101c42c010084102c1e403101e03898942d080030346060402440003d060062480008069070000080071920800c980181c030380c0700d807403503041d494205030300201903545d10781c0030001f00c50061005104040340da100b51000d840e024a010a071640d11001000300d12250760104500c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 152235773 1250 152234523 152234531
    0xc050316030c0e0a020c1c200304030308040f1703100b270f03062e0308030403050d181b09020406020318150304080310140619090b041403060a090203060a02031009 72
    0x44406d01c211003580c0e241510b6162070044002502e09022070301c8c2104c0200300345800c00c010034000a40601c0708540c025002e17262030340d07940c0b096a56028500301202a04280d5030380c04020012003800ea20f84801c0034004840149040058511400c0e6030020110400c5e40708071300e4803d40045603110203c002d110440014100c50700d0b8205020b030060f00c0f9040c1c2440c1c0c54115141804800300426550588040b2640400c0c1c19185541d103031400c440c1070f0030806410004903160001032b01080002d80b2400a181d01030009004c0c02e101040c40504001c00341d03448128040c1c0140010030500f40c002c401d4805010b80c2c050b000c071000100c0d8001414a1444183d400e1540001000f80401d00c641074001e948602d1000c02400701241d00c8125a510165410b1090f590005007006901941141108084424103550600e4444a40c903841c40d52425001230708564600c041340154014285820000e06402c101c41034800c02244002c7c0e000301e40c444c840140100142038000010074051042c40c100305004101d030700c038108 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 152237023 1250 152235773 152235793
    0x313060509040b04020f04030803041707030806010f2a060e0f0304030605090a0b06040e0708011107050606100816090503121804051611190c050316030c0e0a020c 71
    0x103482504041e8945008614040c060766030350401c0c0c400c80b4140c2195910076030a00d460742e074a00e440e66000403c210340d102211008039030f0400b9480080c000003403082d181d240c41d0b403410000040442c070f2003203096810032200031182408846507180ea030002a00d15048212801c001e810004054950381508040d1840380888120301d42c0f50100c041e00c19a8801c800074801a210703048007568800c032440b4058030508612000c10b072a4a0581e20a0402e601001c00b40d0300c85591b2095002c0c01c40786002d0001141d9800040d621007040070500c40035038006021241c20170841801c1a00600d003000017402e103e91130032214a0018410300619900004000003000c071150700d0527029071400d040d0082c00c01d0203a04200012110200c2c5081e0003650300c104c444800381d0000c1024071000f160130340005809881140142c1f0920183e804000380300c0340321240a1140650040e1400c020b042c6084414090b04030902e904076014400182c60003000412601101041c0c0090340315051148005d02c40d02c2d1719548644a098150 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 152238273 1250 152237023 152237027
    0xd090b090c010f0806060a0507051906050109141b0702010c120f030b040b0d06110403021e01110f07050d02180403030617070e0c1308030a08040b060612130302031306 73
    0x203a214000a0341d0f0940204030141c0c00742c94048068449507030000c010f01c44500028464030150401c04d000d40100c425401c03c0030a1402e942000102c00e9a010741c503080107204c620701c00d01406041014420178650546001541d00c60000080001c044180c000041c14809580c800e02c410b0780500d800040030300e1249810107018048203000d6462901003801c02c00c12010602e024450b000070340038080e002c4119a00c2503a10301008004245008490345005c0c40040091b8075540c0450204240c0c1c81e0030700344a10b00c09030015180d031134450071054440d802200d065100303420103c2c0c3d1200315442038034031a50f200820310005a1100401210001c019505006c02051590680042d021107948840c4049001158003005480c1c2c20613004801c10001c1c0480424044481100103103803514104221503040b0ba155422942594400c03007000c0c0006964509000c1885659030f00c20f0f41110044800d14a0119695034082e04c14600a0021001001c80c10b040014980240200c07800c0c110f114140e0040f4540711480 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 152239523 1250 152238273 152238283
    0x905130b0a0903030501061103031609180b1305070c0f020a05130b0a0509131704080d05270a0303050d09080d1d07030b1308090301050103031d030606060306060d090b09 74
    0x9038001307803c0c01c0000482c103004540d20f81c884404c010141d851a0380300f03400d42c040740320b0b00b8850408102d10000006210b5810744122641c0c1e0415840c04110310001004101d1000c0030194800312051a2205005056030080e01600050f58449284e0036980a2400012459005607003e96000f43c0c110340010744030407041d03020b180d040404440b00e450440e2a003091018070f40c0b0444045080c1300701d0071071345030110304031800b90807403000581002c500e03194451035124281228141448041840071501c10000034824030242d41d104091001042d009000700300088240c40c0c030340703c081c0501000060308004210b150704610b140130340050300d0503a60b20170390380700800034200038a0681c2280b191035a030044400c03001c00c200c01100e1300002c0c07221007501c4503006c4c8088090303490030807905a50208240490790b102801038a001f98000e4a405400c202002c14407400509841e11841c4641c010004018072641ea0006598204006490741600c1d070b8140b4103050000c210791540034040783c030460b003044001040010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 152240773 1250 152239523 152239541
    0xd210e10050105030f010e06071107050a0b071707030516020105130b0a0e1903020405130f0b060a1e03030e040b0a08100c0f1707121401060f02030705070905130b0a 72
    0x1044900c5c18000c00300340e03070880e5801140038010385c0049004c600703020300c104d088407a4004280152860165218009503581d02240c0c000c0c1e40c00358020480d00d017804034428030071a082e90003981d43c51605409507030050051080c840300c820080d0001400e0020f592040b0117880d07861b524107000c0e0000e291201070b004100d4000c2400d03174000032091884a0140e0400c5855801c02b03e01013400d071081141175034200406003400504180641120801840110700f08900d89440f4070302580741140d00c0d0130074001340100100c25403c000b01342030341119906011620f010500040740c0c0c2500c3c148a110103003070b0005024048180160b039004456200110b105030700403d160716207012104040118520b11a0251254090000781d04040b6034400680444012a002617982c050341d5447c042c10310240000e14542201c18410b41a1248032400005001d000d400c000c1e14600c8030350500040d81032208079907a15981f5107103405507500a54803000410118071841301e042c1240e55009a00352001c0c9041001e800080600603 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 152242023 1250 152240773 152240779
    0xb09040c080c0a03110402070503120709030c051005030f0901020418021c050f01150c0605011e0506030108100905030702040207030c06060902040b030126070602070806090d210e10050105 82
    0x401429070b62801c145107400301da500100c0e000e03c08a030981000000e4100031816580d90208110b45221303541d185103c0c92207100c60381c0b194213032541142017200c81e0740130a41045004992003146100d01c1c3c3d4000c801d803a84984480e030f0304140781d42c400f854035000e402590b000d269841601d22260f02018041d4000e0010881a80110856200c544a0320410351740140e5810144010071401803140072100c950100400171241000200c441c502c1d600e03d41158400d034072220214110030600360b1600c000118039401080704039101c0d030840d4103207848952603c5410440300003c565a10f103002c03c11200307009407a2060307002403045440d074201c0e050240c940040e655044540b207150100229890000c4c1c070035502a01c7c40517a441d821030b0f003050000040814a10503c1141149a414080612901704903040c040c25555000e010100d292a2242c0d25050014008c408203410030441d204205902c40c01d0b001d0500341c60a00034811001d04003c1c100245107401028625000c4d28841c1d0010a1180d000325040f68019 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 152243273 1250 152242023 152242033
    0x21801060302041806060c1e080d050601080a0c020304060e0a03050105040302070807081903030b1f031a0402070203060417040305010606030204150e09150a0b1c060806070206060d060b09040c08 85
    0x803c002d4111001d9000e02e101047c1c50002d0076022400c0d0201175441840d80c4510881d06082549402c54a41c22401030041840e480388100603035542d02102071900044040000e1040c403246010180d16070241d80154020008031002200d03490b520015540000c0d90060003c01050426023002510303141075000e968168401d504000070600000108401414626520004259034030764049002c0d0040c0554160b019640d958895a0441d20340d42800b1440010b407400a0150781c0d200341c0991090801d507189202d10300c10f0100c1405070714003280480d405035000c4480f010f00d24407164149014010783e0405461503180100105003540c141d0700900680714010050300c41c40c040110110b401c00e8030070700481e400055000c08100c00f10100c5078035101070701d80100300d0420992190072404868000004400d0400310b072503801d680c6d21440e0310411010380541c1c409008c1c103242c25200a5a00c40c80038103102d018800094403c0c090080c10780c040109441c000700210418182030400b0708104c0d115000d010918054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 152244523 1250 152243273 152243309
    0xc090106090614030a021c0e06060f0d06020d020708030f01063b0f0607030215130c03030c03030f0507020a1401020310060c050c0a03080d0c020a080d020702180106030204 75
    0x1250400c04a034101d81c0c425014000f502216000303034001400851209030284041c440b0440c0b0600c2264001c0d0a0210008100c2d840861407440c02401901d12400f036600d0ba04041007c0d102d02c010b06030820303000440940d40d00c0d4502a0100244190180504548004001e10108040c802007650485400f541d5480d20086007520808c6084040d48ac05d131040040702d001c9a0207006070300070100c48503d004100c005041c0504020540e141d200c0e48049005030405141021040394031a260f0303401c048600b0304401704030242d564680f849142400050180001801c140301010b1194010246000c040074050250b410a03210203540d83c890300301c00b103134044403102800a4401051095a10170742c1d4244001752901c2c600403090701da12041cbc09041e2001e0107269101c0c05d4607110320402030000d600c507079041c40d80d40c0400d41140040310216460710381150000b8030a000030036a040c00360340d05000c0c4148010307618222403000849483c040300720742ca9200c010000000300240c05a014100b1282c8a0212950701d000e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 152245773 1250 152244523 152244527
    0x30605040b06030105041805030c0d02070f030b071805040606080702060f06030d0f14030903030117070e0103240c02030a0f021c0807140c160602010207020d11010203070803090c090106 81
    0x919104002d8118500b44010070071490150002c7c011044100343c10909444d054a42364295404800010000d6005007595890746904000d4003000b0a40b070b0b0350002e4030b1421a0307036150300303100c0141c14001040080d0304034105511038903003040b00400d4001e20812185584105c0074241442c211900b40142c0664030002d40c030030903041c0d8100e1041c0300c0180500764404007074400b0303509609010142410003800140b103100400302c8800a50080243c000115100d6250121440e40071503040300102d4150000503040104000c25a5140e0640c2da1058149510102d4590b1070781048907400e4203064100d05200f0841149a000b10050000f0466551b0f42c0407103002d4220183d84c0e40c5e011174007007404406100d4601e280301c1d214100f2150020114a802c03524004010640f18942c0c002c03c0810529400c03400312a400180b20309403010081542d4002507082c14203540000c3d011b1004c0500252a80880290180f9160310a0089925140d8003031487c1d80c0724100b055030030355103400c81401940a02c3e014400881c40b24 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 152247023 1250 152245773 152245781
    0x1a13051003021005090a03050601030506070903350d05071b0206070809120a030908160503030a0e01031104091a0909030d0b0f0904081210062709110a03060504 70
    0x4140100304540c903501d1030303091004402e040c0240380c3c2004400d01c10409107a070f48002500045018100820b49541941021820034001070514000d00a1907001000011030050910068043c141c80c0200c1d04800d0713005e0100000440c01d07034010300380000100b85080e101036030b1116000340c0507565070a803c10040303c04031459210300940654014814000c501c00101038000800c9581805442e034005c446d0341800c40c4d4034122402078102d020540b4400c0c2802412010800d80a10f000e200f091a5003103440c2c0002701e5240d1207080c60b10f0b010840711900d0f280031a406038008a18202000d000c2c5562550349000703840050051800560b0742002c0003d0340307a40c500d03003030101c98000e01110014620784440d074003d03100140700e06440c140e0040d100100c88505a41c4241d80c042c8154010303214590341e602d000c048020001c82c000c20070045040300440600030309602000c40041012050300040c102d8250a0b541035901c04958032041000c0e0920b01c1203102201920f000e030000d2042500c09008403903c1d042040103407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 152248273 1250 152247023 152247031
    0x5040516060e2d0a06050403030f02010c1b050111031003060b270405010b0303030a0f050f100510050f0403030903030f02060114060a0302070515060f03070e04241a1305 74
    0xc2c85040614400741007600350240b030b5840c0a000640c02e4401030108424411303903030048000c034202090801c245904044e00200c46000c1d0304c002c010b03800c0318520103000000030140c025820444800741c0000c020003580a0380c060020b01c4c021a840385042c5201c1c1407e00c040f40012a4580c0c1800c03034084590030075100801c03662600800c030310a84540c0c48402e14203000003c00036120340d901c488150300a51010f02c0214064026001d0105000203240381050540390b0182003607241d0030105c0c0410210b00210b80404040e80d204681c5001013406c1014100d410340030742000b0080707643c1c00290000405800480c030408680c800d0700c0343c0b0320f1074101c10340691302c1d800248924000c2c00489c02c0e540c0028500700000b0031603803516040040c03c0c400c0e95202c1ca4540881d902501000742000b506203d03039440c03c905003c4d400d260440041000c40e0400703468056200000e4401401c0c07003810801888040307181c54090466450540081020000581501c45491441c0840c0d41c0900400040760003120a5401180c0c86 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 152249523 1250 152248273 152248279
    0x4020d02030a060605030d0203210417030c0d1b12020306061314030111032806120b0108100c021507110a05060406060b0306060a0e0301020d0e010501091803021908090405040516060e 80
    0x70f41c03042b0b270a07070f1202240081080794a16003d014010744c0408040245000d101c002000648611101000b00f0807a400742c10b9080101c001050700a103241d501039614400710441000141c0c490300e070040032804a00807004c0d10454130780480004140102222200744079004103c00038441e031300c0400c0004c00d40d071000752a541040c3d003081a01440b41c1006034000c1d842c42c0101c040000e1400d546005000940000040c221155209040100031b091020003d110940340a000f040240b050084001713503549401003400800a62402d00080d90240206da064828001880554821040d90714083e038441200700c8003200c08034a00380b800708100e002d200030350744105000390400d407600701090003e841e4902c000720003550541d002c102a49200340c460168501405440700042107a50402407105c0a032050044100b0001003800301c0789003c240e0000f01500f40903003120b549070b840e2030a0f0401c00001d1040f0324000c0e8010f400c0c1003d010030404005068042110341d840024000c03038543e03030b0403211401c0383c2c642954 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 152250773 1250 152249523 152249557
    0xa0f0b03070c060c0206040201020c040203071704021c050307050f060402060703180504020a03020c071401080f07091a072102060a0209120708060103170c060c0304020d02030a060605030d0203 84
    0x90549900441d044110790605042c125501d960342400d550082180c0d0005810100a020441d601007040f0240110b0443d415030540c40c24a600501d081c41c0796100d0790038078402c40007081c15510780145044500740000c6c50340c41c010405050280d82d82c0d0008500315401c0c0706503519040181c2e00802c04901a41d4002c3c002487c2503c1034508842002007407002a40f07c2109020011707459031540300134091050360351805a00c84825060003420700784151304c0003441400d41800032500380c0c2c0c00851640d01c844882e000b100240c580600803200c02c5800d030465020301508100302d003149442007020745842c0f03204010603c0d8541e080b161251812418280c03079009a80700601107041242c0a4020303003210700001d0407401c41b1481c0b1a003035610340030255000108036000500144280141c03148030314165022191503500e091140d180003903840c407005040c008448404004942159a910075440340b003a0010b00f10341402d1070740c0c209640103004d10300c650b620134424039943c202203d0020060f10f0068049900c0d80d8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 152252023 1250 152250773 152250779
    0x10602030a110c120c01090801020313060c0c060207061506050a0f03020a0c0c15020c090c09040f06031b06030f0902011d01020c15090118210201110f03180a0f 70
    0x1982a0802e4556070308240241c6594140503180c480c045040603240700002d0451340c95440000d803002e482500406032590040041068038249045c80c001410b611860005012101c0d1904450101c03d0700b074014145030000544d0414800180c015a042c4040716100a1640f0fa5561007980c2603c249418840807400e0282c120a07101d010343c1c043d041020740c3d070030034035000d49095444400720b001c1c1d6080140d012a080a85800090f0704000080091005441c21021400e100c0190301107405948041c910960710303a400809055069000100110707442500c0304800052045901ca10079224050213000900c0c240384902c0540107801030820090701a120203411100c2402c00103141c1203001402ca065105600403d4225156803030980110b01c0c083340580e40b242d028500040100b80d0b512441c0010b0101c05a051004e00340c0841801010000451000e1000c00c140c40141e4114051f442e0304000e5000301c81e8104280c0001000522003e4410700344c50710703508005010490f800c0da06005003644000810024 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 152253273 1250 152252023 152252027
    0x10c0f020a0609111003240e0420060301030f0302010c0509130209041b20030301051302031801060f03023604031101050103290c03130c05030102040b070b0906010602030a 75
    0xb51122401541c1130089040c20300042001c0000076006800026520403c490610519100d914203014400305028009481c00d960342a400c400a80301400c0f501c01d003540c0d055400743c1156500d00f0120040c01032910b075a9281880294000b003124150059403c0c43c140c3c40d1480d22a60850b04181c03001890040d00c034154244503c000d40046030001e4101d5503603101103c1d40791f811001e02d041c40401e070361345c0d150100d5a01d02c440c19400b03281c2a611074560082c00180070944d54892060700211091800580741d030b4804090390102c1803040d081c0c41055107000302c0420015085005d50302070700e0082c1e031200b41c00c05442c940c801c07207545000c00341d410a0403a0b811101c8081d900c80d020a4000780a490705180c221401c0b081142100d03402e900883d58044e52150780030251600701141d800c82822110707452803174a000540481e8600c0002c000e19204214100c4410070030040807407c80107051702400854072152030390014160343d8880c010a440030815000050b503110000101d09050b031b00140d001e1810100e51140c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 152254523 1250 152253273 152253281
    0xf09020c030705030d0617030a0c02010f033305031c0503070c06110406140a020703030305090307061103010603051f0b130305030c07060e10021b150d0203010503010c0f020a06 77
    0x301040074081001188081070b01040680294038004c44005812840c0040603581e410064407090003640040c00740100d02ea402100010380b058084c00e00000c0001401c200300e004144151901d8185030400d4640b0351029541005400c030803242e004c13290120754544003003540d54a0800c4146501928540d10760031003034840c40165400c0009400e1800355030489560310401d54001d1000007191030004071b02041aa9403224000c214a0b1001080c18a0050380d504020340310340307079070102505060b03c0e04085050030a00308115004280c00c50000c200610400403240c2d201d501c01c4c807079800000e09060100d00c16094010000140c040413503200003d046c0b80c80c004003456080400141030300e146400c800800f0500520081117921020310290a896090040c050519512920000e003e02402850110400c1d000a400c3c00c00300c20a194a2908094080c00569040010040002c46000204d441480c4900d90740295058030b4084000348850b80d910f14085411201011100c00180e004048180c08200d42d980 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 152255773 1250 152254523 152254537
    0x1a01030b0315180c13020703030507030603030c02120708160509181b150408030a081b1c0b061902070806160c17030c12010e040804030201110705030106030b06040e070f0902 76
    0x815100b00d801c07004c002580c88078802021008450b00015200b040541c144a680d0b440a07a80c00c04000141c15074500600e08282c04900a015102c41d602c00d4400d10820050390000b000410221509942040c0e0714040d5400f881c0b252600445807400072880a03558006089524603440000f40504006c01c454818001320840f410707a0802d2540e4102c2011414030b800400150010000079581d441d00004001d0100f04024035446000703800368203148000401004590017180e01ea81c402c2c0c005c40e01c454103040103103070401034281c1c0718000040031082da201100c449151a8100e800f510360880d80e4052107031720340608440c02601c2c00b4101c81010903880c001e90b01604400c0c00769442c200c042a10610b6200c0c145d1055400c40044000810455a0b2041000c1b0840c0075004480e204200b90038907a4604840c3e00644c0402818000c1c400d01034285d41104200c55002094020000c1c45141c5e503074207141c1c04801095400030b000b5401d294501b00c0138103000035a40210342846001e000c8503843e000350b00c802500084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 152257023 1250 152255773 152255821
    0x140d0203062a161101030b030309150405040f0509060108030c0a32010b030d05121b0c010c0807120203070905060c07240219030203070303020f04091a01030b0315 71
    0x20b102c0762201c0c1012005401e03944003001a03210203140c2400c20590480603140840e0405091145184240d01c000c8190340307004005881a0002030340500017a15a40519007040da002445d04010a04054450300090f000760540304c00e0b035000d0390304c405160342c40348a00b43c600340300765000780f0041c0000790100080b2940e144105008409d0355010803400211403e5400108a09a440701151303505450b00384802c6045d0000b508042d8a0800c186403c0b0b0f5100c00c1c000e011825049200030b81c29014030101c81280c901079103010081099a0801d00007801c801c03c15602c00c000170303070199610104020144202c0380240480d44803d4582c2e4500420404030364024035054905000c2d0343c0c000108089030040043d840b006210307445003000130031b410091070040c01071413407a80300360144000c0380401e402000316030b00d06401d0301d00503035a00040c0c030807101c0d07521441c0e00c90001c09241c0404400b4038255248540303020b0409a80902480c0111801c05a4a000c2d4041d00c01e1401549000700b200302c80c003041032603148134000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 152258273 1250 152257023 152257081
    0xb062704020f0405040b0402150a0c11150c030309071d0610110a0c1a040b0d020a020c0a030b15030105010501020c090a06050a06050d05010b0a050a050c0a060213140d020306 76
    0x40d000310f0b040d0f81c400d030b404a60003164401031104600d000100300e0440790441c08000d0400592583c010045403101c41c001d0b09030017181c00401215214204003404141c03503480034039603580544001540d21f60007250362a180303020f81c1d00c01086019401c0000100a5042145040b4945480d810415003901c1481e4450a0010b03140710000744540501200120901602650301d01c03500d0f0030700e01d1800403040501c86145100c2084244610584041501d0b50302e06800360041c1c6500700c4c144203a2420284104c101d42c04502800c0000c00c003c03007101480e1265581c800000300000d80e44060600341c8030203014090240c0c01c0001241d02c3c0c0c1c201038100da58071012110b8041034041d521004100141e180d07820040010300001101003461600f4020f20f8010420148024900f00e8801001040da029181c101e0082250000e01001c280c0020001e070064150050021580c4035035446041910312079504c20312003264078481140307055242815000d540c1540240c06460140d03a2003416905101c13910029440c10104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 152259523 1250 152258273 152258299
    0x60801020a0f0f0c0b0c090a0b0f0301150210150602210901030b0604120b04030f0c0b04030c020103020c011e0606080c040905100305031204020f0306060112150504180b06270402 78
    0x1e1703288020301810550060940d5440c0b913000b8030607111950f030016050503900304044c0350420305c1c8004403070440d240034000941d00c0220090403030030480100300b0105207074180038400b1007100d50002c600b0708546490b02141e0482d400001e20021001c0200480100c00c0b000780002a10340d40250480c03201c60707400070686032800c0d444050000c040031300b0a40568001b04242c04100c201600b06200e80d120441c10b0030702c031000c04050740d030f000041d280041c002020464165107a070216402501a50072400342a4003d1040d40e00310b081080300000d4101c452105107080240000d800c1d400f030601ca50180b41d51100d048c1c581f904180021010308400780400000301ea0004002000c00c0d000c2c4040c01026100300c20112450a143c010041412000c200c0130740b0030703009403041c00b8443c0e030040b030041f0035015909008511020b441004540c0341c03185a0050b84c001e410040c14140300e400d90080d185419100d01308071112901c6500a009034a042e0780d103076402c860005070a50101480c091052544030384000c01c0350303c041c11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 152260773 1250 152259523 152259533
    0x5150f0307060822060507230a050711120606130c08130507031202100f020405090f0a0b03011109090705040e1308090d03030905100c0e040f0e1f060801020a0f0f0c 72
    0x4c0180040c2d0711103541c1e100b8004003d9016002524110020340c903d45000f68452140b06e452180062010a10074002400070800000343c54403500c4440c001d2090101200850390a1346070081204d000344911104103c04104485030300c135116400c2c4442c0e64011403541c0303e440f209078402c80701605031428403903460f0000020f0147c009203d040b041c00c0d4042e0021818801440741a1f554402400f619680107010511050b09c030408807070340c0b0a1640c0d80b102c1482c2c40e5021944001d040076480242c05508060020b10364415410081504020030f0b07540044a5845100880f424041c40c040d03416000601c50100386604515400701012a004404462030140c5407400640c101c4000001140401d845e4003000c0c0c14481c0501403401d5460510409110111112900070148034805104520841c0e480100c01e44205003039110034030b035000200490701c00003042145e86c0002c0f1981c10101e0380032800d049000c10a000103000340d5442c844035803560950805030f560151007003d01c81c3d01e5003040003015420f0401050f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 152262023 1250 152260773 152260831
    0x907080109080d150302010c0813080303010b0703080906060f09070302190f030f0506010905040f090c0603022206050706020309031614161a0702031207030305150f03070608 76
    0x40c840e1034210f81da03400449070001996294801c213142143c4840080026076003100009a1071940190001d68818816500d40007403501c40d000000c492202000108464185400402c03070301c0d000703845200300c80c3d40b0429a01d60f2690210740050308806a6a500481070400e134445582080340c3c0d04003d030501d0781104c2440401c81111440300002408000712110f900d8143c41003088580e03446005000c82d1070240c0001c1c0c4000010b204440c059a501c0498007100d09055110790300d80c9900116802d0b00300d541c0e02c801400783d00030b10550096201ca07101c1402d14800703400480e41c2280c40310340b1481e003000d07400d8846000940004098030403a0204111305250308280d40d01c807080c03443c400e918940400da034000241c4c0c504011040c8502e030041035264203203c0c40c12803100b160a0308581c11866640c8001c1840400d081500d048200b0031025004640d0768101030b0107030499407141054042451282ca450400c000c96101050300850301074005034024490140300c0c02207103500c00c000c01005241d02019809044031a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 152263273 1250 152262023 152262041
    0xc05060f0f0a09030e01051317060703060f0303020601060c080c0d0c050d0311090f010504031a010504110f070210030e0a05070305010606050a021c210911060a02100509070801 77
    0x320081404101016248000719508002e94440400407003110f941e002d090000b824184505215001c40ea080c030640700b4001920281110343d46545014111208a95940200741e0f48800403908100002c01d50708000e8801104494069004050760703481e0030015a12098070681c2540c40460401c042420a10b003085000c001c17a88a039100e000d8244981080c90414420a80c1c2504042c00c1c030448003407940b442030564580c1c0d8012513411a0620070315005883d1880380d9440100800361440541c00b9510190f000c642c12207000361401d000303042e00300d4501c107041c3c401d14410300e1140700f06000580250900741c0e0300503040d4a4508000074070001c99000c0900d0001c0c00f0000f101c20b640001d000788100700c428040c1c0ba00400f034509001e41081110b04000e5142c001c000384030850341440c0e441d1011940d01c00e030700c410f030300c0d80039489001d0814040d1012000a460751071030070340720044240b541d000c0b241010701c00c40d1901c001e41d03400b41000e00d89499400c00500b40181040d1890b1040d00001704040d8000c3c440c20300b403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 152264523 1250 152263273 152263291
    0xf0904080703020d1e11071d150406030b070c050a021c0203160f0b0c0c0a090f1505060315130c0503040c120209010918050a0b0a060504051006030c0c0506 68
    0x2114071502d8002d1502c00d9451610041120645802c490407402001e82da0380d400707403800d0020300c0d94500300800e0700e8050300d0b034010810045010b2403003980c600c3c05590180141000c15581c101d0900813414081a103d0394480240076803158000150303894810100d1541c1180300302d0075140340e60340607000a1040c8455405602d100c0c140c0c2b408004c2140380c20800030800104002e105958585403c079503545032501c40c41281c2e5255400210f90450000501103191400c41c02040345132220b45a15143c8000c00d40d070308550140618000c80c480307406100078034107000c0380e80080c1107070b14550f5000180846000e508180d16003010001c90320f032001c1c01907405541000c1000b5a10a6241c1c80d0034100700d1002d0303040350b1000480c000204990380140c7c6418210301c0c1565280742020514035080c2c01e40341c00404007044041d00501a5009003001c02000d00c407468000c003403080b01031002944610400c4101c1d00140c40d0700d051720361203060070002d060194124440e9202c89c0d003403002140c100d503180d290502d07100702d0328416 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 152265773 1250 152264523 152264527
    0xb030a140405061e130204020c03040906030c06030c0206091b061e180105030403080403050315281e17010b061803010f0203070215060a05030a060e06070e0d0807020f090408 76
    0x140c0480340600f03114100316410022a907017080c00400203032000c0e804011f8050f80e000159119184000c20454004000110040000540d01e04103491000b6082c00360308006400c1000107410383c3c3c0f00064a078020a00c3d07074054003640300d22040c1510100c501a18003500060288603601200e04454a5001401cad804103109036501d021100030b20146008500441c18401e0130f1092201083d884200300d903015070305080c019030300e40f40e088140f481e480483c2500755000078095009001c0a0809a070200c0c41e07414040a0b0700240e884510030000c0c5200709805102601d205241003016490308101141c00c5000c034000000d03240c04582c08100c0c00c1c3d1280c42d00d260955114031031000f9a003024410300268503a00781e400c50942c20001d40081d00c603c02c080c0c40c804008103020200b0116a1030a20080090400500f10b40c0c85c0205403400c10003524001c0b003182020f028410000c2c0c5000c0c011010700351482c0c002482040140816500c14005401151091b0380040c48052800aa9260b4200950140380204c4400d5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 152267023 1250 152265773 152265781
    0x1003110a02010902120304030c06050f09040203070e04050105030706052a0304081e030901081306140a0f05100501170a0b040911041a06030105010f140703110709020408070b030a14040506 82
    0xb440c5d20031600b003040c0c0c01000100041418042ca102c240d801a26144c1e5a903122000c60000c240100c18ad8294818400400c1c0508150481c400e503030340700c1080e070701800660307a50030406403561500d20031800451003c2100150082d030004124070359140840026840503c0307410600e1440e005900180051b9212a0400001c00c1d0300081809400541000452400f080a80000c00a48001c1d10b0011031180001c0c1120810a640d0400070b02c900020048e02c066240c420000c1c000761420310024200c1c00e142030089046272103401300d2442a901c0607100d858460b21913082800c0407143c0185080040c1d80d642040701480e95440c00703610754440c010200c01d9a00c18400c410002180e408404202450000441101d190740700c603c07c0da81115400d0a0900030080140c2c4203a07442d4861025070030710144000b5020040681004d92801041c0b0044215a0495202d610100481c8514000c04903140c0c0302c0c9030f0421403118010b00541d8806082040407806070448207400302c000c07809840c00c4585400c900100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 152268273 1250 152267023 152267029
    0xc050409051e0901110a0c08070f0c050a05030106080c0603090f071d090105131113060f1d0c03160e060a020601051219080a18060309050105060406141003110a02010902 74
    0x1260410b080f40f00030080c0b21002511150140304180c0520144800c900c641010300c80082d007642d220a81080a01d107103000c462400e4040d80e40c45008082c4200210600440d150405115400540d10044010040802c07910204480c40d003009000100500c03c0e1280c1810500003881b441c80200012010b1107080300441c1800d0001a00050003c05e00707a240508020b582040340900e04405a040b034040c5054030044008221488100800c903580700341000030000700084544000c00440d11300700e00042c00617100e400e00e94a01c42050741c0d6500ba480052011409001c1e9010300d8648111027030a04008003601813011910380c0c0c00c40c1840f200582c020400400650130a10313004540d0040c810044e1031500c40e441c0015401c0000c03d80050600c3c5d0021503c8010640200c01c034114100040d07200d294015940e040044c080d00c00c5c008111590750919011030105e040a0180c241982c00464248680c00722540902801941c070005442c1007548138020440d038511500c0c018446402503900200340d4141c68014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 152269523 1250 152268273 152268331
    0x9010e06150c0328080f15191404020901090e060607060f0b010e03060c071103010204050301060f150c02100c0201030b09130201080f1b030406021309051503070b04090c05040905 78
    0x649001c1840c1102200c1031380d40013015542c0442c04a206071040c0c0c80360803156000a40c1804e14640105004035030403007003182052104105d03200b45908103003441d19803043c88281e004a10649021814040d000d20840c454010354650086014009134100402c580342e040a640c1c4000b0b02d0a0310780da860040b1201540e1000000c0b4010000340c1c021300342c41c2003e07611000c0300e00c10702e103000d0440c0d626600600340603030f8207404507401064018003c0c800141c4500150300e19a03240d12584e518810161005101c0d00d00800f00580c4490f00285035030b1008500100c1a107403c61006022410160382d814000c060340e440c1280305025032400c100c07150400d206440058030682018144044080e481410880390304006414070b108100400481c0713440c0d131201d1130442d000e4000d011074801441b0380d0403404034207600a5400380c1d00c07a1400b481d45000f0454a803041c56158034060041860800082206000d0820140c01406c5400124580369142598904040c82260000c1d00c00a01da000e0980000c0100c080e2441 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 152270773 1250 152269523 152269567
    0x2030a0b0d110622080f0d110c06030403020a0f0804080106170a0f0507090e010b0f010302090904030318080f04060e10091202040f0c09060212040509010e06150c03 72
    0x546403210340030740d210240c5029000e40304038400da5001910080000c11035800e20101045034010610603a01c8154076519848014400380451051041020b1400d100d40c00601d4090310031009410201001002c0c041c0c0760348000c1c015015071003600c9001c00001e102e0450070b40307070031300070b01586881d981404945030956656910010b0300f01e480d105c01103003048020130f85001159000c080d0456017445031800382c1c1400000c0d030156100b5440c00102100c074180c1900000b41d090402c075043c094420044005404a000382d0103041d030450050f40000e00020f00942c1301610340031072143c11121030440c55a070400700c0c0e480034280190f9110040f030100703c480c0d00320301c5015020030104e6541040c03a011000040c1a5502441042804201156800b0a64a0b5a441b00d00e05105444040c405070980b020051700c12503079440380c40f0040c0708044202044407000001d0340c0c1a10001498031450341d20b0a50500080e1138041d1032980c3c440c034140408406042c60030010240c0f491250003031621807110416222442c03603845 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 152272023 1250 152270773 152270779
    0x80f1006030510180e0d18090b0a12030309050111070506070e03010f020d150504060b072a060206060a06031104090504021203161a07080a0923031209010c1e1404060302030a0b 77
    0xb801f0030a50f82031010203a040c2c2e48484000075076061010300080244031143e004405049541328682c0a156040c1c020f020014081c000a120740048500031080c0c80c80b8106005d0850b40240010820043c03043d014078032850b00080001c111074025240042c0ac80c0c0c45051050002d070380e01c2091002c000044403040c03008000485041101c2072910070801714a04c541e000080c00090710720880e0243d03a420910500205d140b0719401d028864030780c000a992420150b0b229032044208420015440b07200e03000f0110f809407410110313070405250048860190030042e00c1280d0001c416203412a8200e4108064100a54208907d8550a8881c2440328681480f001c0b00220290f4100030031564503008811143c12000141b40000c8450541c14103101d8171009810503080e4800c076010721004140c002000c0c0112640b07542d5121059200c03c10368500300c680005403070000c00d02850024505415103034845e0f0f41c0c1e07081c5042c060b80301a4000c1804c09541d00c250032031004264084140024403c1c1c6201303c0348d14810603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 152273273 1250 152272023 152272037
    0x221a0405041e0807170403020915060d0e0319031512020f10030b0907031b03091205071401020d060f06050c0606060d090f050d080f1006030510180e0d 66
    0x391201042c1d041c0c0081000002c48036030842c0c0d0100505081203d951070703002080c1c058944071795040b0441e207a000e8441a0b129002c40d2002c03401030030100402c0301940380000c020703a16001840c00c246019061810880c281c0e4003043c08900c90f0700395032511451610286907000507101d40c0703a600c41100d243e01600011070004050340700b6001038803014200c0d02c06200841d106c5201d880c8003207049010301080494960061000300c00d2040c1203030940c221044040a80c078010014200c0303c2002c401312100d0701c20240c1003030094031050b00c07031502642c0100503481c000c09080001c0204200000e082e46d000d03010854650341c1d039078020010340300707140002009041245005440c06041052117540c07240040c003c01d100302c10004020520001c00c0d84010305d0a50305c2000210442c601d410982e440c1e40c0c1c02c101c0b4001041200e00016200002042024440c42040d00300c0072515040070400c500402000b031485807010500807010411015000317004280404500c0c1c04600d162030018001e0405215420b820280610 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 152274523 1250 152273273 152273281
    0x10c050a020a081b010e0115050d02060d0506040b06040821040e1f050301240905060105030c030c070c030f03090e0903040924170105090c0d03080402221a0405 70
    0x80496034190980d0000d0005480381507454540d5441c202c9508030f50b04e1580ba20200341c46000041d004040b05114152201c00007503611428000d6000ca5518000c1d03009a00f00100c4100340303402e900c4140c0200300a0000103c0c0c2d480c0fa40030580f15802508000c01075400840059000401d0a80100c00050901c81d01c90406140c4011800c0017040501003640341c034041c1031200c1c1103803036140c10340e80100710080080c00f10368090b0606100d6403010a01d1fa24500c401c00e040440c249841c1d01030f240c001c0c0380603500e40d440d550b1500c401500d19080036007102c1d8900010420000403550008049001d540150300240d8032003505d01e005400000c0d0341d802440030554140402a0f090f4010007a5002c80707004e82c201003040c417a110380f900340d20140c4d00346140d0ba24818217030111305c0e40c00701030b080b003800d1107101d000700110b031100e07403000755149000103038545d004000a81d07800001c0d211f00d14440d00144080c203950348045c614800c0310981c900c042a103400460b542c00200d00e0400c0c10314042c003a140380c203035801c20040c28 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 152275773 1250 152274523 152274527
    0x3051f0f1a0a0914010e0301020414120a050601030b1008070303030212090a0c140411030705040302030d0201090b060f1c0501230103080909071407050c0907081510050f030a0608010c050a 82
    0x240f0344140302c3d8205000050010f142d01035500c54201010043c0219501ca40328034000010b00f41d81200d450152281e000d041810300000034011808640040007018542e05e96610b100800c0c00c0105009030200e000071000861440c1044008040c51103905c0143c1c8544c2c14040c804a02d0358001c241c00c1559022803501404210031540187c1941d03400602c041e401020700c030100300948600c0c1d20910848200008001202c0d50000241007a203208805880c0d00022070340d01203090300c403440d501610151201000c41e425140604840280440c0a03080481e0024840e112500396025488282c07007a035150300e15000c41c1b0b5040280000c0c1c40c1949401200294155100c2c2e1405000303400b100c0f40074564500114440238011700c00510110480100c803547c604c05403a1071602c07800c480b11241c0c09003484901040c1411f014210f1144195641f50b40c0e0305414030700804001e016080c0d00700030070501004001040c12444080010743c46810301003808901030346007002d207500b142c00c401d010b03a0401c0030911000c01955 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 152277023 1250 152275773 152275787
    0x6090d02100201110d061a131206142e260106030b10051003020a020c0d08091008090606041b03020a0e0607121106070e0103051f0f1a0a 60
    0x2a01500d050410740c0e0460016801080e0084103c00d40b2a0041034050f585046504010143d51500482801101400d8100300550042c55240f58810f00d28110622100e42c0080c5e0f15103105000f91408120316523040c0c50103a040000760740489072811b00800b44c071004080484803c502c075034000d0202c40094138010802d49a504e1508108600100152a031010443c09410002c080c40e08842004400d04140a01000c05c203000c0c82418060a800115900d006020f0b10a9030484029a00034024146a40e810814000c0101d03504036501d8100f0b11914900d0b4131030301d201918950480e12a00c030340d4101700700e0142c90028014001c0d8451418224400070000c4e603210b40107104130342400c0240c1c8814070b104040e00d40b11034007000310b0380210011403040c0c00d00001d541c1002c3c8410f12a203501070b07a4820b190b240c980b94001165058046240d20b40f594080e1b52091f444140e004c51503108a000442c1107112020210800740c0c49007070a9441260184101e404104101400c555820081d81c0b40040c86c0b04060030079 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 152278273 1250 152277023 152277049
    0x50105040515040801050c03070f05030f011502100e01020a09050d08120c040308070305090f010e0a150221040e13030e040b040b03160f0b0c21220e060609 68
    0x1d51050742070003080d10505070690b40680604c0009010a15100500140c50380003290800001030b540581d0590040c0107100716030042c10740031490fa50301d80c200b90356441c00e00f0b50107104004601c603422a1008100c520f10420408161880015984500303210b40100328a41c02c2e0480c0d44034000c2e4144840010b0541c508862840e0519008003800703a540144e850180d018551000d4003030000050300104140d030107002058661401c44130654038078561801151241c070b00031015500300c90100004d10152007250031172001c0d460684100d42e807294903070b90101d500000c03500e81000ca0040104090142c80d42e0000071550080c1c0c044001d032020001ca0714028421201007180b030707003e99642d055400c856201d41e0401d1107083e0029081311007480754854070074603007010f0b80f0070a007424000c0000030401d983d4071421a62950000f00041031620f144000304000300074424025541048108040c6040016002c3c40e0030383d42c01c0c100b1240e509036260000c0b0b41010310700100f280e849100100100101603542c3e0049000f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 152279523 1250 152278273 152278279
    0x60320010908070e0c120106090e0a2906090a0e0f01080d0503130c0e04030905090912030606030a060509010806040c0605090d060b0102070b070b01080c0f1c0516061112040501050405 80
    0x3407500d4072101d04c2c0f00d034031034a0025040c0b13601ea06d0000c5007144d0230902e64011110300b21101c0d002070303541076844803c0340c45140c001482c0030820200700030808940780e407134030b058040149014a8451141c00041203181254002c0055250540810804981c171014540c01040c003c1d000d000401400040101709210080c0325448141c1e1062480091020303032050034024004450099800e800c140c00c0103011030800c0d110302485510194001000b511000c6410081000303040010350031919503800b044690381008051070340081d9034140c0003c0c2c95a03890036290082010304080e00721803c19040c524041d01d901e810035002d00004000e0359940e61078042c42200465006800000c121240f440100d041030100d900607110344101003907450510460f015058100c520700300c2110444504101070128545404500340e910194100c84880580c0e042d1200003502e61151041d250131000091490043c1006034005c040004d000740c5070191214410422900c0c0b5058045000b401c10f071420700020b149100e10302034280 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 152280773 1250 152279523 152279549
    0xc080f16050706020406021c020c011b02040b09041a010503011b03051801050106020d03050a05010e160c08070c030b0f09030d0b0d060207080a02070e0105030c0409031206032001090807 81
    0x400e00c40d07000e503450b10f64051001d542e0b0701da41d4040255900003980c1c00740810495110f40600c1540001103000f640340040c0c490b0015800810080c00858180310400c1e6006074503003034404002c1d43d422100754401ca04c502030036001500d1400d0901301001050b004140a03a160043c805c0000c0708208000c060116685004035850b41c9854400c481c042250480c061251b080c08001b007403d43d004501111101c08a40c0e0811013030b62000041c1094880030f110b8810100d1201c00440e4207108071010341200302502e400c3c82e105100803a038580c0c1c1194000301064840e5040040d0a00c100802080c0b1f080e008910740e00d030800c40742020b040301030b00c910a03810981c0c14266100e011041944030348809101058011108549070030107800c0c4201c0f164071100d1004010300a441c0301060b0010302c00b061905a8002034010b00c1d5402c4694180070040000710401e4042c80001003840c80400010301400014600c50990140324038002e0318011101c0680280407414070a000e9010300000000060800071920340000e006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 152282023 1250 152280773 152280811
    0x140d1b020d02210111120103030c0c08030a050d05010909051c21050906010b07050a02100c02190302030c04020703081b19090609050f100f05160c090c080f 68
    0x1407100010040c025001110503012007a00c0100041210501002c20024032245091002c4c42d81940b0421244140302207000c401400406c0c412103031914918840c030110f04110383c030b901201c1e1443d000300400800003840010300150020706400f546004003242c0e20207002c41c0b02a5543c0c40d4039410301002c44c03482d40030f27000c0004203002c1c80b4079071010414000c1042030720103406045012010b801d0032541140d640c800c0000004803188480210740c0c49980110180c142e00509070708120480e4006da450108103d00c011182c030259139400a03070420b00c81e2801c0e00000329460752040c1420003000c2c05041d4455032061000b100801e81085031507500c1880001c0034010f41ca40c6520090b51805400e210008440c4082c08034502180c01c0b111801c2640d0b455140e44207010355800802c648117a03002d00241d001081d003041d0a46c0280155884c0070300b003015007041400c1c24421801c00e440c09200e03480c1918400e0180c00c040040703050a01c07d144110403140b40907001c80c60f00c1d1181840c0031070003030504080b070784040c0604 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 152283273 1250 152282023 152282029
    0x6040f0207051e0705040c0302090307270e101a01090b160f050a060903020304090b03120403030e120f151b040605030c090604090501080c01090609060e010201021c0207140d1b02 78
    0x7410285c44002d000300880c6e01c2c810300081c02500822405402445480c00c040345000102074600c91000c02e6007482411907651405510183c81c01c1c240305112031003150800c10101103036018802802e8580c01e00d180c2c0006035640010326191482d03000d100c0303698042140c2140c0b8408580500b02d0700350000010740c0360705103e207001850100654000351465240ca0710080400d43d0100040040350781c841d209019204030041010f454500000ba01420804108002c20000340208007003555644001c1c050810301c0d0504096600703080000c0114011078200c108104095809100410b820003500300d648100c080455600c0e080d10b10441c010282404008000035500c4003201d0210340c400c1d0f42c040c1c119500d49980d001180c01510082c06000204e004000e480c0002d0b5100b03000175401c4414540d9400001450000c1c25510034131010744280c1195000c0141c407001c0c40d00254044641c1400300001680da9203a81030400d00304001004400003500004541d484403071780401c0e404a01c2e04004424800c82000d4400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 152284523 1250 152283273 152283283
    0x607200111070209010b040506030a0902040b12100e0303060618030a150c08010602060618100806100504061703030a05061c0501060303120c0c080d02070506010e06040f0207051e 78
    0x1809055800c24456a030000400006000040d100b80c072074210990700d803c00c4440a00a5007e102c0d0410801e20000c1d22012003a006414101d001600000d0b1025811020910452078a58a030703001d81d20614840c042c11040340305514180b11100003840c19424102c0c00030780d0b00e1003040d0030841c0e0740c40c2c6034403202220303542031181c1c10b516548980390a0424441e17071041c002900c00f420103000440c001100000d142030011461501c610001082607000c4da51140c580c901d0500c01800404007180901d0380800c240e0300402409008010039140806843d02c2e0104201c00e45100350040d00c00b0240d8001c80035400c00c0300000f0382e07402456030b2030042266590400425020644d480e5032000c410f1049400100748001980b01100f80d9000b40d035000400c4040291410079540200850000646100350020204284001400c2407544181000d4503020a40c0c0b56507240902c03c4e004101c0c400390351b40901200f0f140510564040600400d029410301040b5142c1d10b4585240d1800648610898035044021b0340e03041c40707 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 152285773 1250 152284523 152284577
    0x601090b03100e07081603020306060406060509130605030109030e09060f15090f0a0603140708060319050f15071701060509060901030b04050a02040302010e061e07060b0a0303050304031205090607 86
    0x300b2140006c0c140320103e202c6854500c400c0c6d00038000c02001c40c0840c1040d00412007aa180b80d00d40030b161492803024082d480f28005003d600c115a190000300d40766030f0a0184866a6001c0e035103200e0b04802450812440c64000390241d4030503048403100410320340b245e003108120300421b200d2132903d5419400c042099220100b407241c0e442030341c060001c03c11a8042e4000450b40d20340b90149030041e0b0340ea010640e40101d05841c42e0740d0607840007001c1044490a881c0000750140f00b00c0982d40c654559205661a01c2c00201380b582c00411284208000b07150f100c1070203511040070200d20503403540340840150091007161801d0f8018440001c0340400c40e406034202034400c001c090400c0200e894040351500094001d400103d001407080c0d00d0304c90291802e402502c80b2410b00106a07416940c41e00040102c550140b9422110315403a52514016540e80b9010800111300a482d40c594920303040c90002c104801001d0201e00b00d925001c10700540c2071001610355408640c42c100f112a400b04e420b608909004460 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 152287023 1250 152285773 152285789
    0xb091203011d0703150512010b04021602030f0318010f0c05100c0e0604030b010e1b0f1b030307090b03090a05060a0e0d0f0c1b120f02030601090b03100e07 68
    0x1002604160700c2009902c44100465060f1030b003580c210305131a05d80040506141d0820000c1c4400d203000044c0f41d07100d40b000c0340009800500003000c03a00342c0c4c201011441d0007811100100701542402d100d07404010f1303c1d20001d986401007141c1120000c4000b05542410002d40706010f41100b0f0144d180c2d000d04e07a40000840310142c10300190345019111141e00480010003600c000c0000c0d04220042c0c074240c035405100405240e00f00341400d100f1500c010300d40c0011440da00c0c05801e10302102401080e00c0d440c1e908049503a00f248214804041c10f1401611040794020000c02017641d40c003003964416503034441c803055665101c0c1843c4500c2e026106030081e003140110300911070092059801825a190100150784c42e00c035a0100a44585e80b10340744030008a0101003440d00010f03034070801c4000c9050494542c56000c1e0302c1300040c95100484075400c42e02c0720041d01e012005c0d441c040241c1801060025400c3c01101d00000c042925210480d01420b8466152040d000e01b103001400507030080e12000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 152288273 1250 152287023 152287027
    0x1808030c0304060b0429011704080f040315020403020f0f0f010c140102162102060a050403230307030b0306100603020c0a0203161502030405060f1e03070306030515130b0912 76
    0x68241910ba101004099040c15000c0e403110006e035406181c411030000682003c001140e961529a05150341c4000400c80c5030799820440440010140c13020400309a240310740050b243c0d03045205210341100c101c4500351240480340c2e440080c0380d560342260100c0400a10344044003c061386040900902100c0f6140c4942d4008036404c582d41c1c036200400c85911b806201c86c1e00c40b0f4007203101d021302d42e81c03c0403111070016080480016628041034000b80d81140c0b03c0d01d400240346c0017801030601c4050781500300d0402d0b81c5000060002c04c43d498054140d080f28203e0141c200e50400d03109850480c005480b0700e209040d00800c00c0820301c0d505010203e4016005030a4449070110764410300c0c5080c21070701070002c4001c9510000702d04a4800010340301a60f5028020504e00190500711542c190800d0011100c071401c11440b480072100d0711800f5600840c03860310f01041c2541036141180c2440614002c7d500c20800000420a84500382480c964015801c0300c1d01c4903158a803860f0381d904001092990344840240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 152289523 1250 152288273 152288291
    0x18050a050f030147010905101e050a0f020c01050a0c0c051203030f10060903030c05010f0606030509010c1e0503060a030606060e090f040b0406050c04080105010b0702041808030c0304060b04 83
    0x4d98400d001021914400055024441600b1241111130704880d690004d114400c0034046410070403c48004480981040400700c2e106200b80350030307503242800b144001200490201148c0da00300c10911401a00380c0080c145803d84200000c0050140407280d00800c81a104400c1c144204042000302030030703018189808035000310704419907e07030058444200000d648000504078078803000c401401d50b91306590710601d0a00d5514210303000c64060405481c155a2106600a4001184280c0c0001c20054502052910b03000d01120b0849601646200078001c440b5640d00102c0006100300031008401d04000c1d4aa0300c451010825613005500001d02803850304201007002900070008981c996000c4072150310791364030310f40b4400b0f44084c00e41c0c00800b1894080c0c0414001440354000301d0f40800c90311641070505c0c0c0d4511915003034400a90003da042a80060300c02c09608085c040d610403184110000d0084907016582c40c040341c440100135064011000c0003240030812217404c110300c0240001c009000c0448 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 152290773 1250 152289523 152289581
    0x6032a0f0903020d0b1e19050c090409140d030c0905061b070305010203011a0c1c11151905010b0304030c03020c150903060a05010605070303091a070c0318050a050f0301 74
    0x70702515134170b06d0794060754076a40d5400a5100b169109040c001103c0d4884c5020340d490744080c20000c0d00c0c1d20311030f52003480100d85644452064010040c09040301c8441c10204201003403c05d50007410a900f0141812844200c5079003001c0554226102a1413a940d08c0c58000b8444078a025241d090900500030b910f800014410150041c6060754096540d40c260350f41c0304d094401d201d12480460f00b61039000911085801548601d61282200c0d4a003443d03100d21303104440386401c0900803080b00003580e14100510014401d02d0180703680340c5240000800c1154181100c0700141e0000500003410450351a80031003c05100380060180303400080c00b10200306c0008050744080360840d481103030091290301d0000c1e4049401e0301400703048441e1500c4213031400e44035403000c401900c0041e005461001d49a030526407013407070079030b0850b10038403541c0c0d100c030000021490003c002202c00d25481000a03505082440161360700e40e26001201e038216401c11282400f100401d000d48402c61628002050184048182d10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 152292023 1250 152290773 152290793
    0x1b0406021c020309011b0f020a060c0b060306090a020d0302120d02030a140c0d1104030c060302070309060201090507172b03150308180102120d0606032a0f0903020d 72
    0x25401c801003002003150100301d0f0b8900401c2c02d201c5c001404454001490600004905880c5000303000c6c0800e0264550007042c0415110b038011000240303884803500510002032017940e00a0b8084015080300d0820b210107503520660420041e1183c00044070003400c150082001410350552840c006031075000311480c40000350012039422244500740721518400780034000036a88501c3c440a0356909042c2d010169100a0207105201355a0840c03c0001201040780045020000e141035034002d44e0300e04807860001c00c4200f1940c00903042d6070500310f454000030004940070054036035401c1008000c00a03d08442e15150701825001e01000c4401581d038404c441d4156610325002c8143c03020300100250380040c1ca00644248000780c0042424003551008601780b14651644540520440701c200302e90384c0400f843d940c0315103014100e41e42d44178001c20031140c15010756450024203102d5060601c81442c40034040c02080c6850404000a101600800600800081014540141801c1c0184c0380701d00d081000c003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 152293273 1250 152292023 152292043
    0x1c0501121703040c0b090a0504020c01020301090b120d14190e03070611031c060b1602091305030304020d0c1d18030403020a0e040c0e0f0403030501050301020901171b040602 76
    0x1ca07072442040494858003141c0c012540441d503504c09a00d40f128126054214004090f4092100d03074000510355141c0c000703060135580c5c020005036a54940500003081300c10f1a4201402020f03100180840b1900118081030300c0d641900b001d10085030b0842044025101c0c040911020003800a0750021032035101c41c030100c42007000d804441c40b040d29034070252101c0e03c5030441c108042e44100b0106801c1417240481119508600f200070605648846040c0c00b80d402004054003001d0040600c081036152403107803140c024544815402c1c03001c14948680d5100d10000740060700600704981d9013130070452101080c10007415142141c0d10111507055103680a060159041200c0414415a2410420000c400c80b002c90398010032014036140340a100c0c108a1000400668182c407094000148035103d035130050344100408410342c0c80e240303020718000d8201d546c10b8101d10300aa1041c4180700c03d60345c102c66000051102c40b0145449907542d106d05101d007403400d0605c91009040408c00140d426000a0000da603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 152294523 1250 152293273 152293283
    0x7050d1a100f1d0c190e0d2a0506070b0106180509130203011407090501080a0b09070c1a190216050a0506010f080a0b150103090609051006090e070b1c050112 69
    0x4d13111080070425901a8040140361101d03060b072864016800340700d2401d40c040000e4520108040140c98030703091107a980d8480601d80701c00c080e111a1036480d0100320800f070001182e459003031074025101e01c04c40f03c4050180301c0900c1429104800c0b5900c06404150003400014001103651810045d880c5034900b21a400b00e0280d803c0c4500c840703425a9041e4024032808195940d01c0305586401c00443d40300502800712a03503242e4503900400340c0d4aa5003041d601c910380940729142200d0040c50044000000b502c1d8038500790114006004c44041100c051000c942c01c504009038035520901c0121070324240341c0070001d0143c0308090105c4100180415401d040b50303d80c55680c081e240da41d55009465029000006012415180026004680c2d424034492545018500001c410000f44c3e2001c084900360b030750a45880d40045e0494a0400300c50254401811146800f8407070321030403103c0c10340c1d140781c58090b498894001090003660780d14824015010a111841c0a01c001d50352805a00408181c05c20b003a41d07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 152295773 1250 152294523 152294579
    0x10b0405090c0f090c070b04080d0516140309061b040506030112110a0305031c09080d06090b0109030f11010e0603010b04210317040206090312090307050d1a100f 71
    0x7413441d2603000e507489016456a0366203041700da03581b050989a4001e00171140110f0034000502620042d108641c410b400000011640b0311a800c2c014002d14001400005410f03400c10400075582070204a8580020841010441400c0741c030040307140324000ca0304040c1d000100400001156a59440c051000b64001c1015030100e081c001c0a1010681c003034000580607074410040030400c04090241e006180e1210400050603560035138a1561a50005d03175003401c0300e9200d03030b4140304070499841844030400d42428090103c6166503140021286000b101600b0044031480000c502e90140c88020401c05005141d1592503031202c03a0215079403c0780c01400000013052380b01c40300c84d442d900540c100b09070300340c0c45122446c1207108ea545010706000b08201e801400c28451144103890400560001051800555403502058000c0c1072811a40380d00140c4242100ca1402000c00d180d00d07503245903031014003003c440c2c507030794030a600c14144050342c884c0a01041921001800c803d2800c2918405141400301007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 152297023 1250 152295773 152295799
    0x12021210050312042309040b04050f010c0c03120204091104030c060e15030702010e01051311030703080a110a120503060913080307050d090203070e01050909030a05090d05010b0405090c 81
    0x141d41d80303803d12030588103030001c0009100402481c4484500313110348410f007400700c02050022034200c0605032000c071440842102800100320303081c41085a91401c1d000201300d418140d404c02820f203031042d900038040c010400b442e0752022000341c044501810300d10310144203200382e100c441605079005220a0f14050071550010807035a208840030820201c0c01002005451441d181310809a84081c001c1010340d075903940c2c8952161828003078030b481400c000030b8170b20542c829820900c2140c002404864032039041000107000146240d0191411104580342620b0050940c1c4039991801c1030940c0040c0185a064100c40507580d403280056224039400e8600444075100e0800d4840614812170300200031141c20320004d40407070320500c060441405101800b2401c0302c2244c02090800e403058002c1c07a6031180f458010700090504446240e044950000194940140ca074001030a17030141c001301c9446030300c3c00b818000502030250031100e9105401002000582071800710103030349024504010740070f0700240c0104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 152298273 1250 152297023 152297029
    0x816020a1b230901051c060c090519080a1202070e09011a010809100f090609110406081207230d020106090b1002071406070506161b02100806011202121005 68
    0x144004080c05810307042c3c980d0800c0c08004040f00c03030702000110400c1d1038100c407000c01e081c2d002d44084a0035540741c9481e200c3c01e120500c41703080307269401e5400011480340d0405c18501c0c000354181c02c3d03582101c0500d06e001d222090481c10b2014a80c403a0700c88450361000c6c8511a24107603c50b40401d500d042e1180050341d1444010364040c1c030f08a41e900d005410079407082c0b2400756180c0110200c2c034a203d200107429582556a007044030303140321040c0c0e00850103007400503c07030501d0310a12014012440c020f200d882070058180c0c8040c80340c0c440051203c10300881d8503401760030a0002040d90035a140544409810221000340209100d20a420565003414003107031203130070410400315800d035180c0c0c0a17141c100e080221445c115120412004d400035020000c01001c10403e03c0114020050503d45207c042005032005008070f09560004125981082c0302c01d0040e40c6904000310f8404803401c10003041c0da1800c0043c0c0d003400101007810ba807140001030480c0c0c90001c088456106003c40001002500e40740e03024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 152299523 1250 152298273 152298329
    0x30501050108060d03110a051e211804020c01050901140c0d020c16030b01060f08011401080a0902031b0a08070303052a03270f010816020a1b 62
    0x2024089100b95020401ca41058403121940340c0c02424901444200803940301d1a0003150f030400d40d0960400d403994684100e01314013508200001c18020b000c514540f91000c0b0701c500000721a034101e20400100303840c0754050354442c2100840000d0045464617401c40c03101d8060407003160b40034043d51a002d84040342c80302c00100c4134010841c020205007801d940f080c0d2400203503c5120011078900c1450019000808102c00e64000f4611500e8071005070f51408a01901c00c0b48040034001c01e1040340d0006100391446070125684150f000d1800780102d45540c0c180000900383e042c1c019415000d19800d102c02c101e6210600c111940044e44e90313542050b5a2100c0c951200310a000050001d5000c110400100d8070f40f0340340188403003040d05030100040070490f1091035135109481c00114860b8244d5101c002c00c400c250074040021065a40c030000c03844440008200507001001070499500160008151500c20002401220f0b80710030719150303812802904038132041c401d01c071342c00015294450650750050130700f00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 152300773 1250 152299523 152299529
    0x1503060f030d080a0c0c0c090204080607020d0c06111209010e101401090e07150201050612031e0d020f040b180307080607050915030a06080106050f0306040f060b10031b030501 77
    0x5101d00b0f01d07882d0001c804001e4802c2541d50f00c00c04c42c801e4201c1010440c544050740003420ba580c0c0059840e441d001449060210080c00c030300664103c0a103c1c90080c0d00700c00c20464040d488000003444809078106030f115405620528510756030f0034801c00c404241c0550242d0b51002610b0101d902c012647c00c0d0680980e03e24003007a060454900340100900c1c0710940091681003002c0040d07844540e100c01c80c903100340c9050003140006030346500a00c409402e200304c200100c01b16043c0a1450300200440c2d4036080d1b0100f40c006941e503600000c42e80b0401020703038117440d205810208070030341d5665223024040c1c0e5900711012400c1101034410002805280000c0c48008641498010700307010b596000c0280c4041d0030205540f6000b00c440009a220910f50720019889402c240d480002e403d810480c14500b141d13843d030001d5000d601075245910306540c000940e40d5003c3d6002414626907074203840c0000c0a405210003c41c0c104000804103078030302c1d0b01608544060039001c0a1843d04241c026030407030650724284 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 152302023 1250 152300773 152300777
    0x80d090602121809091c0810210308060a0b0c0a050607080105090a0f0216061a01050a0905040905070902070f0b060402030103020a0e0405160f0801060e0601140a0e1503060f030d 78
    0x140f0b0071401e820a0b2455940c00881001501d64001020400300081c03400800d003035000887d100c0030003101180d4840444081c1c058580b5980101100c403032030030034100910314042c007440f1740d280002c1ca055441241c440c015111464000742c8442d960035440340d0702c80c10004116030500500000413125449959414101c980042100e4401e45801407039000610703ea0240404541c4c0030420351544601550800000c203206480000b00031607207032140184051805409410001c3c100080c0380419401003555080c0d94040310700041e1a03100b450310601d000d10381e40c400b0b05031034000300364a8144410701030305880c80ba020f005541d0081e0b99040400003284024040250300c40080e1405100b0b403542c05141940c402d12a03000c9845a1a21076998000180b856008110ba203801010078440c030602070058400412000c50140b03400d0401c00000303840021344000f04c512480d008550303410100e01c208014204484050494101c5100380d00c03890503280e008552290103418044ca00a14074213000440d511040025 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 152303273 1250 152302023 152302057
    0x5060f09010c0c030602030f0106031b0f0e0117090105060306090d021c0c02040e1f0501030507050105031306020424020307021e04020c061e13030e010315080d09060212 74
    0x480c0040d91007844403501a10701c2011214080009002c070f20081d406100024080000b42d8540341006017902c4201c41070082034084501c1e40921320b40c0010072a4412400c5040480e860361350380f40104c0300000700601500c0c40312a10001e01c01d8050065014502811b425010380b10981e40e074072491960392203400d80c3d40c1c1c0142e11500f88071148240b4000510f0090000e440c1941c1c0314182600000c003619003103003901980b50010070500341c1d0621200c40201d405410082e040c1700642c0b4644500f0b8036000f880c422039052260003c00108150000300f006600e031a4044130464559880700341c09541600d4954031001d662501c841840e0040d4000000d0700ca010780e0003800042048120800c1c184a03440d0201080e800907024003503072140134024000d4034850300307601441304200b68003460030100300d0320080c00c22043d020181d40808082540b05248445c2e60000382004281c131104441d08035050047c5034006e24403401840402c7c0c5680d0340c094541e05c2107559690848541703000c070300b028242521420764104c1d488000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 152304523 1250 152303273 152303287
    0x20706030513061e06050a1a09190303032f0d0c02070801060909021509060403060203060a0f12020a1a0a03181b170a0213150503030c01060f05060f 65
    0x219821240d4412076101c510081c030032680d641c9030f0a40300c645004a50100c8140301d005000e03446841564020142161403464003032401024024004074241070188176540010b8000507901d5000c0e41c40041c0c26522208010306560b4200100100032031550384105400c041e030484032005071945036207000c1d08100b003d40d00e84000c2e01e80c1403001b444030b8540407080d406100130010300403100784911070044c400391001140310f007224030400000741c604a03c1c0d142d21220501c80c002007071b03c441c401c1d070302075a0348100c006a40e52254000a20f034001e25522099200d071a400010501884c1180c410040e21b1003034a889440c1034a038030b081101c1001d003426070104207000340a42800c0030301c69000541503481180581c25142c900340c4604890070940c540421035070300011404c0084100c1c40003030381154170710030022b456080104d5000661048007a81c88541c0d031034848040a131946810201440141402012a80e881101c03052090203000349100310b8203018500d41c1c3c005a5400d04200b16664004803400d100d10f040b403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 152305773 1250 152304523 152304527
    0x92a050108070f0c050f0303180709020f040e0403030b19050102010b0f031b0103020d05010f1502011103040f0503090d14100506030606012607030f0c020a0f12052106030d02030307020706 82
    0x500d2035003505d040c0309840d4200c903101d00038030086000c2c5d80b407050301c080c100c00b07450101c904c0c090030340e400000c681e441040070350040c0c540c0000b0b032000e807008035010b202c1980b12800d0481c050b12140c807100d03034004ea5064868040e82e1190b640300c4203da0302030f0020b0103441c0019042003014640b0040e4103030190404843c020301051041d500c0d204a0a0505005007045001c0e0848400ca42c400d801190a4004528060108180d03850286d66904e1031413000740078070b80904440c0c0d11b0500014100604400041d01841c1c03c1140138800d90314185005088980004058182402c1001c0c4170310030742c0c0c030501540b15000303102c840780d0080500c680d10160003031459444103030044a18007801030000e80c1500700c5900c0500721600d81c03550107026903615a004902d0304120000c8c1400c540d075101811081d507004011040005441454181e001a0845108205204040c00943e8a03110345c102201e10541d500c03900100a034600b42e10580580c0080e402c80f19441d40115080c0d030307280f00550b00440941d00c40c0b1020070041d8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 152307023 1250 152305773 152305787
    0xc01080a020f040e04021f1d061207090f0f0303020a0213141620210903010606030e0705030a0201050d0203040c050d0f1a010518040204092a050108070f 67
    0x24080345801480c1c41000d9000b1406900a9086034006500401c1444254900b4550025503100107030401d80340c4d00100d0754054114018981c44030740104c0c1c030303940340403041e56280155181014000c494503494a01180001c103013014502031100d42d00b20344a4007082e40301044c62400f0680e54544c0041c129120300760200b0440c940740110800c2c00e1600c1e00c03000400fa0034010211070084041c000d1383d4044480820000d40094180514003250105081038581450030020b9407006003503032110b2407804044007125580d49446504141d0303415600b010800507255605a001c10000c2d816982541c00701502e45e002c02d9100e43c0408006030010382d003031140c00981c104590017190828454441c8061740c60340c81d80807495540303a4400940b10045900361207418001c015404e8070356203081c901008030300d40c1480000303003000c90409451960401b040d00041c04544881e4800500e140d0082c46d1140d180e10910b581c000e102022200c50f800c041b0340b01400281e254020f004090040e81c4586603c1194003100000311440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 152308273 1250 152307023 152307031
    0x405010e0d0809040606081501080412080912040b07150504030e01050c07050310090615061b0317010801090210020303060901050913020d0302030306010207080712030e0a03060c0e09060f030c0108 86
    0x180d00304003e07021065440d071085c0b4005041544580106150500603d6170851660507090f052003c04410400014002c89010400b40f2140c00d00700c2c2c4035200d200d805481c00d140c044004285039030014021840340004005006807900c900301025080351030380c80a109507003040c0c500801181c0f040c1050511903001380c01600300118540c00315984660f032030300000e24110701d504e0303061503581c0c1d01c0368003038103021441c0107200f060001708014950507450b16600504001d0a000701282d42c034902c100c001c0415204a09011500c0e0307412a0302441940c440f14014002d003510134040740706031420f5843c21030140c0084181c034440c0000038240c081c82e81c81c5c201480030107080105000207100e801c401400040c0c0d24414003902040c040e0780256101d00c4c1920019291420381d0308104080ea01088040000c0401e075030a50150075418606003803000540b2001c0303a203034001504000c04142c00c10464898041e40b060714810060400c0b203150f030203503c640d800d101c002007034040300e240c05807c0b400380300034194055810640c01c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 152309523 1250 152308273 152308283
    0xc1c08062106150d2f040203100501050a09052e110307110a050301090605010504050a200a1e050a020706080702031210171608010c02060a050603031c020307020d03020405010e0d 78
    0x54011545c0700395071500b00300c1c9400c0001120600b07220101d034601a8411001d40c2c00d0710f00310304d9814581d00c0002e552203544502c03030403c00700007a40390b411407140140000801002e04214514082800190305884040908209d00e8500180c10702c905403250458201240f0203001a525010090712014039040d0b0300c01501f50007070324420000405850902c51400f60754020000001d595040c441008203581019041d1480e0b507080c15071200c044030342090b40e080280003010f0490369400d0700f08400c1c3d9000070b0b2486c00360500d0403032105003104203800100400d001d540325400d8400283e250901628980ca00381c4121380141c0c01401410105495402c48903004410400494840c941d5074000c0902038001c0901040c86070031412002c0044909049002c0c042c0c48010300901c030740c0e480703c00001e540f100e0042410440c652514041040354506001701c0d0100c209054900105071034107440f00c400303580292030400040c4612424210940e200380b09903000c2c3d410507503507003624440f40020850701905401064503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 152310773 1250 152309523 152309539
    0x6050c0d2d0513060201090c060f090b09030709020406080f0a050408070b040303061a041a0f16151103150901082a0d0b01030c06080103050606060c1c0806210615 71
    0x2030040300b001c403e401048594000328524400e45440040c0040c0740c5e01c505d0511942c4a813001d03003150000e81c0c810540321944411030b101c0c40d89a00007846c0c10750aa00401e669440010013003082035104144900c114480c13101c00c2481d0b00c0d0308a640c401c550b41200c001e0051070302032002c1c1c8005003450743d0407604240289000301e030381920746000f9012040034140c1d4281150000600300b00e503882410310b4003010b0003e4007141e424540180c1c1060040e12808010390303020180c2d2080d00381040a0307044d0a04040e01d03640d1081181c40d05001e040c01542c0d0007510b010895070307030410f0021194070302600450b0580d61800c0103010f2100f01010802c980b06401d15161002051800d404441c94498607102c204203402050b00d071a03194510300344507440d19015088181000000300050000c100001072140d08248156080c0f40e80307849001d076413801d01425140c400300c4884a10360122a20354000c0d1028090030701200c91080c00c1c032a010910600c84030140d0201034641180340003850384520380c000d900c2d26100c040c04100d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 152312023 1250 152310773 152310787
    0xc03070203061f090e0a2402030a020d1a0d02040515090f04060e06042402090d050a030305090a0f142d0d11060f04110a06050c0d2d05 59
    0x82d0a10400300c6000e00d00328110444203005801030403080c030040c20014001c10840b42000b540a4880f0090513000d410f036450b84410a50340c955011440d5824429401c2c21500c074144003040d900a90711915952036803509024100b1040f14801d000b10044c0c01004010824a801c15070030b201c042c103030060540d511003503c44581d88603034a404074410b2280c400e10035480c80c1d62900345081c1d02101c41e880047c0009600c40420000003540c6080c4002d00d804176002c0d85107084002003d030f0b070003030f110703030090250081c003100c00340c00810100241106495104c0c3e00d040c410b60759007080d0303c0c0ea82c1c04181d0001c2e00d050480d0844070007007402031a254002d190a1825501c1a082889650307800c0c41c0741e01c2c5128802c4514000984040c40248840b99443c011403402d015141c01c0c02041681d645409048907005072040c102041c01c000d4036010720b46150402910b2807610980d151005800398204001e03046503400340d40e03c1d030314202d8450103c1c0c06645610002100303103180051904152403040030340b01820701c13504001c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 152313273 1250 152312023 152312029
    0xd081008031b060112150e0709060b1b0607091701022a010b010206040206121812070302011404020a0e09010b03010510140103060b0307030c180905061e010c06020c030702 75
    0x4250b4408200c44500084019442e510b2600038160311410f08006101105030000c2c50b00c01419000001440000c9204903040c4c507281d04054440e40000d03a00c0345003000c00a80ca04045019110900303858880e0322070345100c062420388a0701c049400d1000038582480512802078a51041d40b00b1449540c0014140070f002c0205030300c0b06080d080149030345002000c40c902120400d0189150103403084c0301600c6c560a16a000c18040d008181e40f4440103101103000450002903032030f5012034641401e0845441404d0703140040c100790310072181a401942010180ca421210b24070304180200d0b03000c0c000030350b070fa458041c000540074006092907116540364440641c060b07130f00b40a298050005089000d0147c0d01c0e0460f0030400b0081441313031605060a00c541002161024030680e0f81c0682c0c43d00b001300b41c50132500c8080740c464210350300303034009600088000b09243c0c03016402140300d0310701a50850b10925810300c215a05c61002c4844a00203003c41c812000045c04a8020300707421669441120f00740040c41d800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 152314523 1250 152313273 152313277
    0x3050120041e031e02150702090601080604090b040309080706020601050a0302040507170123011706040c0905032401060c0807021011060f061504080a0b04020105070503190e0108090d08100803 84
    0x44c0d2150104078940040c10341ca4549404030001c07a0b025203c0d45484080d03800300d1440080100f00a052007400c400141c5c10b6202c070380024800c3c903071007800c0c035515161514024100760464051600c1622441002081850000884034180c40c130040075404d60918580c00c0101804e4014080410401c4042040048120303c12000d4060840c1d074008150500da8040c0010800503145885410408140503281560094038271482d0003500940f40460110440340042c1c81e04602644095010320880c180d0103091440e100d201011f400001e030710790606982e142d00442d503c4c0c44c207181c0944440000c1044400600d13160302e000405c0d402c01c5c00c0400000110514550502000300c5511032801c042900300040c528000a20741c1d040040203440d0b604040c1400e45141d52078526400003000a500c1e0300116055a000c2d505541d80c0d9948901281e6444030b00c031046c0301d1a80107101004001c42d0848a04449a40c06982c180e4441e55001c0010151a4001c89044410010162400200c0701c40d40e540400c20f19030500c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 152315773 1250 152314523 152314553
    0xf0c0405060d090308160e040905010e0a080306040b0901050109060302180d030305040308012129090f07050a1a0d061a0723030708030403052203050120041e03 70
    0x10014003030186043c040d001450040c41b10503003410b09040c003528150000d032144039611080d98000307804900c1c0d00d8030341d0050818040c092040e100d075480d48020829110000d62041e4829101031080c014004248a150344080c050306010030380918043c8500e070700c29809003011002c2c80141c9542100b136000415514503100105030002500c5804100a0503003001099005080c01e245001414003808605020505007260080c820b0005084c1240d0f204801d0203191410407490b42e1804d09030800360a016580e40c1c6440242d240d60250040c0081d441c41c05201180444038003c008038458091645ca004142d4885607030000d50355554140410703200c13502d400041100003220200c595a40c56800c003204440002450f03030004e140403801502480c1404019517503416401412251243c989142c296807600680703602c10f040d40c002c0c2d0080c8002c2c4c1150f0b0000d0046034080d02c000c02104038421000700420101c1ca6624a403050100802c10981885890304804030741d03000c020b2106991645c0e10302d01d072210090 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 152317023 1250 152315773 152315797
    0x316140d09060b0307030203120a0512090601030b0a050f22050105010306020a030f06050a21060e030414060a0206061309060e0c0111030313020103020d020708030702010c02060a140f0c040506 84
    0x100610200b082c60310411591650840c010011903180d94002075480c154949505401c140109003200c40901030710955180d104000050100d40c03404403c42540c07560f0034402a94401301000115618a00b103101e614000ca042059001032540c2c0d40100c4011041035085030300c104580030b00703003c010174402c0c42558003a40c424603025980d030703403160b10043c10b9802c0c00c100b21600d0391500c00f04124070307070b1003140040864144030302001ca03064009070103030032500e607224000d0481401e005c51f407441d407007002c8001c00946800c07403440391080d81040700703004080c0203010720940540d1208012a00305d107400c518540e800070b00c105010907132409039614041901c04204c214495688442d94070b100940c0c204000c91607900da000000c1d070440c0341920741c0508804000d0406414142d00007141a038452050701150754840c0c00c14600c0c0d5480c1001203000b8002d0020003503c400500443d004a080042140103da0282c00f0958031851070784c65110300c4600d46400501a0351401e4007c000004043cac48060107030008171640 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 152318273 1250 152317023 152317031
    0x30a030207030303051006090918020a03030e010210112a01020a090311190911070c031b0f051e03010b12060108010507030b0a170c030601090b0a0e010602030316140d 73
    0x540340184c29114042e02d184404170100c84140041030307207c04040c04961807000003240c640048914031483c0406c00c0000b80d00048041c4000c4241600907100c141c8800c0282c0c207c07800030040d004030f642254564860000825020000c0c041d401a400c0500c000305034840003854030b01062120241c0c02ca920000003040407645825040041c8503090307004ca409114241d6944540d8a0650b207244420407250040c00c1d0416590410100c2c40c8034034400341c401c0b0700c2e0300841c0c03440302940301d040c92165104202e20f14804101034590125400746581c07030400c202e403130207000c12a08410074802d0444031003130003110680541d03a481030304a0705ea840b44d807914969841b03c0c005e801c982d4180190982954801040101803500f08180030107580c80b411840000c580401043c203800c00d05018601e4180407007100a2036043c0300c0c3c1c000118116100d60300c654000ca40c00c85002000ea40e584045281802c2e00340704000c05a04148000341c804603049000790186c5080b4580803260400740300190f4015040400c440d40666a5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 152319523 1250 152318273 152318279
    0x604090c14130e0c0c0d08130b1905060d0c050402180301020406030207120c0f02060703030f110307090e01082d01020c011a0906130f0e19020102060f011202060f09030a030207 77
    0x801203603d5000201500305616101004144a66400500d01d400040012880c0024026040c8440c4003683c2d40d80522075041504002e01c10030303032042e0046003d5000707502d400042001c40c94001741d5806425804025140d019107400104002508041300003038504514a500c080703103a88c2880180090f08190301e0040c0c40ea81c440c100f0b44241c6180c0d80340d15051200441c00c200100c0e40f26191000ca03a9030464825660380309a01d0101c018080301c3c4007038421036082c41c1502d0340c00f00c080c90103944903140c00d41e1182e480d50b03038505e02c01800420070722330003100f07800801356480010520075030000b40d6511255680c0001002404441c01c80e4084541840580d55600c2d441d030300c24085d490080054102101c03543e129040c10700008010101c44000c000031159a113492034401c0110360042072240032108281c5502e010103c01500480101c0c1c60220300500804001624aa41d104140b5060700c04044485410850707650a0000aa01042c140403108405204010312030361b0070000e0360030300d0b4442d074007800441d4a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 152320773 1250 152319523 152319539
    0x30d0f03110f030906060d080304060b0411030403020717010603150510030b010b0a09170303071d15090a06090b0a050c01020d0f0e06010602073b070203040602100204050604090c1413 80
    0x5c0944260310480c90307421000003060a420540f50041d40154000070000e02c03090004004003070000743e481220b0004020001490b402194403022104190781401885c01a441c149080391300c64003006240340c802c010201380307410040d44065408440d040310010303070507102e4480440c0d81c1000d0f40700c180451800140030b2081ca51111821000b00030001203441410b0038030210320388900000340f00c8400c11142c488030703207007801894040e102c1c1e4500107070900100a6151300750180d2680030070902801004107460000b0124440d06c2003000300d0b15058182e034202007101908407040e030b12003031401d10299002d02c00114609218400d2800800c007026000403e03150840c0030509116050344031006540040d03000300402d52031401240400c40d40c414842d800303030b4001c141c4020080001004034140030b1140003084400c3c1d03000401082510455000c460940030851003800c280e04c610b0040390340040041c8400c1150528582000072640c02600302201003600c0004249040e400c0700c0051a40305c400341c1401c002c458 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 152322023 1250 152320773 152320783
    0xa05030301060f0207152f010b150a02060c0309100510080d02010606080c0f0f04080c03151302060a030e061f06030501050a14060d0908130b09030d0f03110f0309 71
    0x6001130020344009880c0041007840c10b000d100074801840030104404010301c205007010080704004880d005421903030010051b009002c0040d03101d0145014022070327038512070540140c940034901075004050560302c1401031591600081c1c0628103606c22424220725900d100e010711841800d120340010a094540f4800e140b07482c0386011039105591410b002440305a40c0084003591003101d05100c19070301c0302501820103440c403035002c45003503240010030041401c00c0d020505000b900e40481c129503c1c8104103a0403188484150351801d0822060705000300141001c4001d026034030454100000c031411007101032800c018080300d080340e08000c80100440e0f101d82c940d403d4805460313145410005581081d0218024150313701402ca850980741607001c46ca96290030880311011000701c2c06004940381d41c640740c034054002030801e0210038003034000454203910313450076a5284074004000f005001c80c010403e4902d0400301d2054010142c131500b9262403581c40d070009110003070000c2030300c5a40b03107800d00d0360030300782 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 152323273 1250 152322023 152322047
    0x3190806010503040b011707030b090d0e15070b0601030b0d0f03030608010c080c070f0f0303140c030c0d05090708030a0c05010e0c221805010207140d050d0e0a050a0503030106 77
    0x4460b0610501010852100701c1c035066131190b80345401541160100c29141580310390000b400391400d4810080c1d01c61010410004060f0591955803515009504000180025810210016400744088400b1030306d503440540d04007070103042c00180f0859080100c2c05094030448280c0b0a050120440c0c410103030301d0b20440c0018000d06008102c10b11600b07030010f12902c0060030310302c1d50590114a48042c88084000700c1c0b2a10781c05000303851041e52501d0081e01400c3c0c0026103159050600300050450084442241d2050b002c8030b10207881d00c02d204108000a05000c2d01b5120a4803a042010901c414104020941e072001a25140c282d10410300e0401d0179101d00e01c0d496800392f00451150300c00780e01c602154409001c203404000d545030074030b88140b8008014a80880b0000c1c07a4490243e001e2240c194010b140f0346024405500944048069159480c111810311000080040248890459499104c0f812201d0903105603030403c609501c03028076013000d040040c7c4080e003000004100290300000404a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 152324523 1250 152323273 152323277
    0x10020307210e07120314040b030c16050d03150f030b13030e04050411030c01080705160501020702130b120c061803030910080118060b041203050c0319080601 69
    0x5903103012a0010a240e03200d1096510110664a03040008075294114480007038000040300c0282d956407030a03055483c5511002e03401318040f07200111045840d8000c0394103803400f850502c1d00d151100c44d50440194044246029000c424030041000241b050014040c641d100341d40200d0068051140441d032180a9841400c10f01c00385c0c3ca0400009010140d461390202c043c003070aa07420f40a0f402c0030303192100d0302c400183d481403a100c10401080901050b51400e60800d604036815140c02c01c00540d482c80040d5644004582c0522946145400204030701082c1032103040090700b4641207074041000d407002040d0340c10219440702c42031140c0781045002541c0c0554402d005200d640e00d0a40450018428418008160366401549440c2034a04104650b20514094a100b105d02c507541002412410207005648a0300c810800e0201910024007840c010f40d40902c113814605450810f4903030000c0803c0c0320807030501c8030620048020050500140034000d0710466412400364581c80e000b45010300080c60181 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 152325773 1250 152324523 152324527
    0x170a050a240509060607050106030b07170702070506090102101109040506270a060506160b010801060303090e1b0f0909060907020604020d05030d02070302030915190302070c030b0a05091002 83
    0x100318811410303120704940007541c1018081d00c800f400700e2498410140098951360070200000f00304a83d41050610600346a5141c80744c8035980091015040c0d4207551040059015480511030307840c1080c01050350290500489681e4100081c2d0102925409442052030020100d45024203041c2802031703036400340741102c0403207940c07aa84180707100c4d5662040c0302c81c1007100100000380c882d61556129001401d0014a0151641c030001c0e9188114009150300304c0d0796240f040c00001d04080140034030815a641912028046803d09198100c4190000c01070051181c10320f044816800090f00201411400102482d550b400003c041c4202120045c10036400b403600c61302001011075000c10100d8001d43d04445410452256003811880c602a071990a0084c51001400308200354001008200811054400c240c609160610030303001d50003001840c646142d00034418109091090b8014094a441034154004d100d03120340b02e010b0743e402c0072103c00c01d0296030b0304248104801d08012110104851031400e41c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 152327023 1250 152325773 152325821
    0x6060e0607030c0611030c070302010e060c04170316030216050604051e011106070306050f0303070305040e070908030a0f08360c0301020c010501060906050406140a170a050a 76
    0x26a00d01ca6040d016041140740c452900402c001c0340c020750909400b480c205a100e0134016402d0503242c0c4003400840256180400200640d240803031b440b84149081e842d9030703081c02d103030040c070b841a0308000500c400c00f4042042044501213458120603185402680100720070818206094004503191b007266100390383c20300c010822940c0300c541c2109417400070306480c412000180c005885000102d00c10750300b140900c504011030140d166000310129201292007000d12071251b0181030b02d0b80305110000d03002443c1000184501c4044034032003604143d440c43c2041049503514a041c4c00e45e00310b10303580000101040b607400c0206902068185c0c1010b20382d940b641500303905507a041c030340c0e01003510507461240419002e501c0580003030002102c00c250150095550f225a42c0e92180204005d0151201003071529501040f05072180d8240e80c01d681d281d8484501c1c80d10130717804800141e00840041c20401611071450400c10b03009049250284090800c00308690401000d2030058801d0803400c41d81000c5014101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 152328273 1250 152327023 152327029
    0x130b060a030b040e0a21081509100b0a032a0e0f0a090207061b0507050327040c120b030102070203120f04030206040305060402090f061e06041509030606060e 69
    0x140c00e00d40300c905000902c165003501060181c0b0054240307034018007030340103000c041c400300340108012000306038002c04075107002407030a07514154140c0700018030010b400d40e0050705003051407150380c1003694240398041c813a0313a441040319140c0c0541d0031800000d45500500b49101c140c0c1e00c0c0e00032544000c1e866880e0001042c48000c00540521101c03900c14010742150304400c2d01c03950540005004401415955030f001802c10201516052001100c00c604405035111035910030740660702c43e1036100340075500d000c03142046000d01e07220420720608500ba000d00c51102c55600c0c0c0c81850a2101c041e01c1d8010301200b5840500e00f11007407880b4080c041c1c0d0040103c1c40c01603401150762010721194103e2991110160b071044078560065410003500300b00005808810b210b0000782651140784200c581c20b40e01d5840d40440ca0355040c058541c260004000349034000c044c512469070003885140a040306090551340c1900e04074040d045514100030449140c001d105008250080c40040e010506010038051085c0b004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 152329523 1250 152328273 152328277
    0x13020d02040903050c03040602010209030c03010207020913030e0d06090209010b161e0c0305030304060b041404032d030b1518100c050601090b0111010e030405040b0a0e09060105130b06 81
    0x780301d00d90318200c84081600130015038010302160303800c4a8449031640c1000e4000c2d8070120f00035210f81f02c1c4504202291405000700d5050a501400c201e080342c589001c101011b02c1400c0c01101400013404441045884001c42200350314000c1c14003084164050062100e5888180c00c2422259000c0041030030089114580404955100e41c502082e03281c5580c4540e1442c1c1500002000d00c40c0210000040c07080000c05540941e00410007080850b020740c040100f16002c1103080d02482050000080103c1c2c000c50303c04414030340000250020f10110b10f10041410a4070703403184040b03551a04510703030f40d081207800400540b0390360318407900c0c0c150b240e40a2400d100c1350100c1607108422841c010490035129018440e01c0702d074000100c46040d40c440d480034002c0c0c811901890b000801a25074404107190500030070b003041d01400c0c09145801c0c00c10040c0001b030000510801c1d08001143c1c4002900b1042d001d00078420686c0740c01500701c5504010820100413928500000250300b000d02d104026510941 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 152330773 1250 152329523 152329549
    0xd050a1d06010e0c0a1707030501080d02030c0a020103050727140301050f04061509050703021b030a080a0f090506100303140a020d080612150103260708031b0c0c0301051302 76
    0x75542c44840c0c0369012034a0094404c0146c036030f00600c0d8240018140c041e0407460580d2103480513103840d0a5641d404aa4900031000745003070b290b00409500e0090b5001c0e1340100d4100c0c07018600b06070034a5a031500e102c10ba00044040008490518a00b004200210000380404200440080c040c0341030400010465850141025280f1551110321001a081030324940005080200082c00240361851010b0000e410a41103012000142c408451a2450100440f02407040d81e440d03a03103181d1521050340d00100450070b03441603410f075038800300000700b0420070046102c1c0302800c00001c065415407230700400303101080300c00d10030100f010700c008948541c010460b40951489454280000d54500b80007560f0a03d28001c0e4403654040c40e4070f160038841d94421650305a9000e09005280038803d0383d2510040394501021f2400d4582c188010700000301c0f05002550086103400085e25004020400d400007507008001100d0341d40d102401c0c44600b03003828041d45e075200c45010ac0b0207641e618181c0100c0c001d07060700c207 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 152332023 1250 152330773 152330791
    0x8030a020901090806090610060f0203070b090f0a0501060515040b03040308090a1208040b06030f1911282309040f12020a020a090b0609010c06020d050a1d06010e 71
    0x8a4a40703800e91061200200400c2c1c4a401c691301420010f1320035450b11810740764206000900131003c241d690040c1d0206400020507402940380480549602e5002c000143c01c6400c4c40c05003c800b407880d880c080045041d17040c005c6000142071450201004400301c40d1041554401d40c00b4801000042281f07000c0c1ca0340980c05041c01c2d40296600c803019030610140c184004c10076000800140c024691122042780301303620440e50700c00552902d0080654522000e5480030880d40134040d03410100c2d20021031340d040103114010602d900c41111000942503000e03425000d585c5c0003180701d0481c1c84408a800c07040240310905101ca222411104032401c1c41d100c1519003400b805000c00401d00b082010944c590703190303802c10103540c00c16140e218025250001030704140e00c202d0704403501050070801d44c812445881d1004051074075003168040103540c0c40c42000c0c0181c0d0b019609100a009108a1b401081e01c40e00e0b0102000400d211036000d4880c2902d207400300b5403926070042006110320002880481e411400e01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 152333273 1250 152332023 152332027
    0x509040503090d080c01051302210c040903020313090605010e040b010e1009060f02011404020d0f05010c0c060c080f0106031a0619020625080a0e01092d08030a02 71
    0x3420800e186110703822000e900444950308040c180080070010b04100640c0e200244556100e180030218034500380324010f940000b604a004c2c00c950713045156030800d0003409042e41c1c2c1403602c840c0020101c1d580b100c001e6015800008074080700a0036031680360040d1181c00c4c0200003503820540020a8601c2c48158a402150348070800e5106a0040304182ea400b400140940c10240c0308140040002e01d1910500d00412207c002d0f0f150b0090040c06001074800d1441900d801d20790310b940070480005520081a62400d00000702d980c0816000c2c02050051900740d260400c0c50001d600e044002c940b41d0821642c00c00042c00c051101100b005416507045075107074600414400425200040390b520380d0f8800640c00080040d2034400010340b0015200106810740136034015544810002c4080c4070395000c40840ca82000514104141c022003007950050f4861400248100407600440e00b11141c0303107800d449842c10b104000f46542d004510144c008a00800395413101c03034460b56042c05500005e0207100742d00e070300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 152334523 1250 152333273 152333281
    0xf100f0209030f01091209081908071a041a0705090f0111031c0b04020c1203100302040504110a0f0f06030b0301090b040b04150902010804110406030c06180806100509 73
    0x264040c0d8801035001401d40e0340e18983d21000500a0250340412250101c3c1021503640b003c0c0910000c030202d0302c2ca0006000001c000c60078014080482e1002260004d400307200140c0800c250b9a4915608521203a5041c0f10f81064100b1600c2c0305d165400003486425080100f0080320717408400e0303506144080d070308883c0b80c00158006940401202030014010711001c0391000c554500380b40038010111035803104000c10503201c41404203034400c0300b80c4584558810f42d00759410480c00e8006503030285071070720050f000c00d07103950001e0b003568002d407001d580055814802d02d500b8171708800e01e00e00500c0c180c03098410300362074116a000c3c642080e11846c0203041d56040000c2c0765440a4020710b00007640045288800e10341483c007004810815a400d80b02080c2d0b080403005040310a10401c00310321380517140c003031080d6281c1e96242c094101008131580c01ca51280c0d00000001c843d604410080c22040d201c83c1d801c41d615151700300f03d840c020343c80b603152079001400f441603031440d05070200c1c1079480690b00600d1030b5503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 152335773 1250 152334523 152334551
    0xe0d030512090a06020f340308040f0b0703060905183a110709020f03040233090f150702040c090e040f0201090608100b13080604140c030f10 62
    0x1040b07000d881640000742d45502c00c0c5140d80100b81d200361000c5007e092989403011600d4410310242c1c50460300801c0c4000c103010034000d41104e50b04ca84a00e541a0041e0000d981e101141ca10a541803404641c6520007400300060034080c0c0d0340c0c00506107410400c418000c032041ea988c0c500d02032010350000e04448001c01c02008100b00000c803900d04210b0034a454031120070050911039002d1450007980280d035000300307090140e4000c90314080344101099085484580800108240420b01c91185044200c6881108440a000324407a2400b1114458880410b0410b00601180b015186031288100341c41c44a00301c2c04c0c03a415904019010384c1d0008012131006001d03106203072560000c48000c5000e208000c2000b10074a502000e183c800ea996040c00c6a0b1200d0a413142c2c14291101d211108013a10180030003030b0503d01801e0502d00c20003400c0303513180e038584005003050b800b03139401e031045100e40800080b144402c10007040011000d074010000154040c69540d00c0385510004c4041d12034480c8101c00c5810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 152337023 1250 152335773 152335783
    0xc030705090904140f0703110114090916030e0a0b0c030a0207020a1401021216063b07050607120c0201020a1a07020c0102011a010c02041503050a030e0d03051209 71
    0x10000d08402c9a03401c0500341207100804184800c140b82c8078901c2100d209480126a880850b03500c0015000c03984d46150040d03890003803158114000d55400d01c000400c41e5952581c01d40200d0071281c800caa49848000e0050a07540c0c07030b02c8600c3d0355034000a0200001050b070400340e83e100f203c21030629101e4a66440703441c040c2c4a1358070040d50041200cdd80c00b20b0000b21100c850800c40200741c084810050f200c1c545146140210340c1101200001c0115010110b54140c05c500d0308500c010700b0342d003400c003c548c0740618074500c240a90700c142010040b2a102800040080d0f00180408480c0036080038526910107000038540030064041040300001e44085900070000e40305040d07400244050040982040041c4030007080b240d4800510542401401550040c403590300d80201c16145c460303400c4aa10010340c3d1012500c0d03030032a0010755401d1030001410007050100042d43c8240d01504c0c0d403038468100100180150302d00d5a100325012021200002e40103402c4854101d0841c0c2200c40c20342d03d60700380ca0700700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 152338129 1106 152337023 152337037
    0x50f04030f0e032104030212061b07150c2a0203030a0c0320031b0615042c01020c0f03030f01090e030c03040f0311010e090c030705 58
    0x401d2140070035842c4040040d00710b80c9000c900d0318603204202e411081500490101040c28011844c1501090320843d080100815040c03d01503000000c86601c02000c050b6440c0014805007003106005841741080c1c0025000c100e03a00680d080038003014a0407042c848156001002c3d51403c0044040f217618040d0041c00560030304142110607101c0d42c20520f03007642440410100801e03000b0b0710508024180c056030b0060b43d101c50314070405504200404080311026000b1800708a07204108800c2d01010b007008840129070090b400041103c442a413000620740010340211707008544105400500b10074031070710212038401d098802c2482d12400181d4551444280a000401c01500303540c01010044031003c2c01d403031611850818051469125501c800318481e200e000820030f024140c003613440803800a0801d15441103030382c00003039141a00245103108901010021660191203042030f1115 = true := by decide +kernel

theorem cover : BRFrame.Cov 152158273 152338129 := by
  have h0 := BRFrame.cov_init 152158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 152158273 ≤ n) (h2 : n < 152338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
