-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0252
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:44:45.170492+00:00
-- url     : https://prove2.me/submissions/b43061de-5ddc-45d5-a81b-889733469f5a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 45143889 ≤ n < 45323745 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 45145139 1250 45143889 45143893
    0x1080d09080c0102030405010c0c080102040b19050a0801050405150405160201050c04030c030b1306050c0a0e01030501080618011e0b130509070501080c0904091101090f0f1a120702070303030b03 85
    0x82c500c110ba07408012601102e40920700301000b402d0360704041c0204409580102c51940c400a40024614100d4015015091105c010302026255880d002c4d909446034441000c0003403403c4005103d107151a62289411282a0015003552090070012030202ea206603010322501c9011240318190680c24051641d00c003403112a524142403031a90f900721006a40e000c010700b0b4129850004040d5001d0400700c4500380d4021409004030b0518031989400c0f603000005210001c0c80b00b01a1840950003800340c141201c0316200200103950720f04090702040091400300c04129501c80194203016805584168000d002a00d03000845008400400c1007100ea40406000303440c6c00d0100700701102d0004101003007103910a080c0078078980e4555000402d64030601601070340c400e01d0410403c0501140d03505220102c50700f80c070382c0d050040c0c1303400c0745c20700051281c890222101c4000409001741a1920400444181c200c40341c641041d100049902082404852110050740245000c1090591500560680742400d41c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 45146389 1250 45145139 45145153
    0x2031309090c030602074209030905130908070506060a15020a0209041a0f04020103050106050c1209010e0907051e0702061603020c1504031101021f1505060301080d0908 74
    0x551588a20b40510020300703070a5000c00e084040c02484041d030020281d2102c0314540b003154026014121010707a02da01d1003a40202201200711484a01c0f49041264060712880c02551815040000141401030b807248451b8503001680700080010000e07150f15031044020b4100d40c503180d4140681c0c0d4400c0c1c1d000103452a004950f40d00042e0700450400300141e011340f20305003240d9642c04c10321484940e171003400390031003038030310402040401502025005510076a01400070341d0340d075602140c4e140109210010a60408000312041120600c02409651818100720303c500b16200b0001e03208940c1200d48202103403001941c00c0200c05c1402e1059201c600240c8118105500703900802c06038080c00c01500e00140c4403da0000602d0300030848079140400040202020304403240000b16a5000740c8801c40c0d0400000e51078146540c00454240f9051810034100d03902c00442204800181c6040a084611201704a4011807680c49987c01980171300841c1d0014807100c00c0902000300800d0299000b10001d0700561 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 45147639 1250 45146389 45146393
    0x306080d230a090e010b0901020c091b090d06020c0601031703040305040303081b0a11010f050106051204031209080a11060402060f090f040906060501090f0602030406030c0318030203130909 83
    0x6018240c2a28049041d0b11200c0d9000c06440c000d07040d412503d8040202000001c15842160040c6400300f003e0b0b0a441030466254240312110f07006407130180f450000300b20340308140c5881d0005001e986c03200030100c200d411081e44400c41240e2101148000310b801c0310f00148184041d800040750070280c491011b502d036281c5910000e220340144e010003010081d9031000314820240c00c091300c801c20314a0881e0240c2d00e28480da000fa00b0384585484440300b55003846202c107103181c0c45104e03130341c100e032603548400d481c008004400d034004080080003182448041484100d958086101e06c0b59220b22502c0d4195456065413400340451000307a5049841e0750000c01000016160842941d1070780c550040215222040040042d2810000072200364120b07103424240014401c0716000001110007c0e25501a125250400c05112104a00505003d40e004101c1080f15502c00e0703000440065141c03a0005600d0b00c4003002c2c58010203016800d9006902c046006624261580c4850008250b0302c00c040003498100c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 45148889 1250 45147639 45147677
    0x50f0f03030601050a030e0609101514040c09030b070206010e090606030703030e130f090b0f010b12040204090b041b15090b071b120c050f03060a0c020709020a0306080d 74
    0x400040c10844d0200d1400c1d15240240c01503911003103040252030140c944050100c0e9103040b8a190840042e090450003a10303200c0c051a04c038103403801d02d02e1044a13110248180070141130307000c0e038100403c0003039980000450002450035026032a6a400b4081075450203c0400f1000f4014206550720741145040c403840f5074000903500c0490342c0c50f007001c0641594140000354110a104072981c40d09040440c00c45800820f540188040c61040038044410b44580c02c5c0030b03420304024052802c421500708030100e10045404840d50b400b520042000c80c0c1480d42e661240c5240e0f206403804c4451259414050f14181e10060000010b00840b4900440019600000801286061056810407880010b4510034000b02000bc08072212410b4032140205564910300060425490025200f1451304000400c81d40742c640e54a48828a004008041c50384901c03000d440145181c549040070345c850303000001440c0060f8005041aa4410744000442900e414480707401c1440070754410f400c1241c0f442c000000d12901c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 45150139 1250 45148889 45148891
    0x60d0b100e10140f24030115020703020d06110706230601030b010203120c040b040303050d061e031101030e0607050d3e0705030f03060310050105100c08090604030b0103050f0f0303 79
    0x3c22920044c0100101e000700d0b400070110b40014401c000b103d00760b0440380d08600002c5040307d030143c11103c1003264112040307031a01c0c650301000754080c2c1c10000350030100d260741d00a68152009101b0643c80c000712961784604079240c1030404042e90710070b6149041c4280c82d0740301069000c80d080c20b081c00700c43d1181000075101d101d16070a40441c0d83d40d00c00890490385100c07080d100076191824425641c0c3c3d4503030401400c01d03004130601361003090608a02144003180d44581a208424440440c6d02d1981141e41b108c4101204001540c10941e403581e29060060080001a001e05265114280e590000c04521419259401c00d24280f4071211100240c4000c81c01c4c61001d01e8189080b40c50610b180801a07804140c803442c50003806a2101062946050703800f54000c50041c80c0880441c1e1429090024000641b4800d110345944000140401c00c803046c0240034480b22248980001e91400f800710000802ca904282c00959003000f8807c01401001700070060109002140401448149290401e1950701c2c88 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 45151389 1250 45150139 45150179
    0x405070504170c0409030e03100204060903031101020c0a060b041107020d0204020c120301030c0906051903020402090303071401020706111207031a10021c0c03020c040203060d0b100e10 81
    0x2c400c4507106101024410201d1015000304240103039003c0e410010001e1158040c098030a0188002641d0040720318401c5400b1580107440703c1200034515101681c41407a12404d01103a0354081200c07010010041c40510b170050700ca0b550004446c0401000e210441e080466003043c44e0104010304005a80d48044145003140d0441d00580da650700300b240182000286540f81401d09004400031041003201c041c1310043e00c407103c13030412560f44d0f200c08022203003080c0180e0a20855164900f4005810190001c0111640c00380840e4035100483e620242511007000005000781d602190720001c1002c01d000c0e0502000e85108580c1c00d110312a6022114950050300c203205240c0d441520006404900b5021901030000030805507610080c0c0ba07019449070844648100c0300040c070151034500501034155248607542660081003550000018030000f54000b4094652148581d1400c0001600700c90445200305200c140700107000e840c0403004440408060319206003820500e41c02d01c92801c2c001a610840d20f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 45152639 1250 45151389 45151409
    0x109020a05041d0d02030c0c0406120b0408090a03080405090105010c0305033402030a0f05030108250302030a12080a02030412050d0b130608060907080303070c0528060b0405070504 79
    0x41640030003108000c200c1d2400071140113551601078101e4000c00a4500c0480c810140c82c82140d01d40108400c5400c240174001060300303941c001c800031410122007030364030901c104911460030801c035001600150080d401100c41c10030000e001e0000c1d080c06a0b08a00604003800c100350442e00b5664046c015010080590829942c0c51800801c44d0001004800001c02d84102440120301d120f000252284c3c0101c0e40b001c00b10300600400040c103403161048a040700d8042001c2d000b4070041c9403200c0e10a2200365852400b40210310300200250740c003030200c1903003680328002d96034003880180d6001d801e00400038010309049105204000100750800d003141c40018a900d44541e0380c0300714860100003090b94401c0c194200e2081c0c010100e440b006540320030203940c2190708071001c40c3d40b0200c4040d03075040280200705081d0000c1c000325846134020f40544560a01c07943c1640c10400405160070038051408600e41c69012180d0200c4060101c0c0d4824a43d20308420b450612561030038080240c118800ca201c0c4208075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 45153889 1250 45152639 45152651
    0x807061107060c0312090218010e151f0908030c01020301081501050312090402120a201c0c050408010c0203090907030c020604240204090905010507050a0e0613031202060405010b030109020a0504 85
    0x35a450307030300c600000382c2e00a181204c60110100001e104000901501c082e0103104c5004c030305030381d14440e12000d04010082c1a81114880405e400c2e10031400040507006200303c1000113b420030061010f01207131080e450005840358035203500c0f50b14224904411010b0000c081d001405183c03004a034440500300344141840d5140340c008041002032050141644800c907851080c04801081c4e6001074040d90494420100641c80002405040384112401104501030400100c100e1000729003080315000803a00340241056901c0741104c1c25503c4080403100180c10009084515141030031300a50429281d280c1004800c0700c02c940130350342e050b01400242840c45481465604209540341e29085492800c10542d250341e9129280d81c05800c02100803075241d42807134001100c483c400c400355114800d03582d48562518000c3e0b0140000c3d544003114101c19290102c10100200f040250280324180d4954010b241c5031505007801405c542003504505e210f03034103180c2880c01680d40c000c00c05c801d07200304540c00908 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 45155139 1250 45153889 45153917
    0xf0c0f091e0c0c030a020709050a021602100e1005030a05160f0e040f111e130e06010212030f070905040213060302090d060908040e0108030703090b03041b0807061107060c03 76
    0x24002c412103d030f80c911000a038450366503800b05010048880303480b002d0100b500e8106280059006450905e003034800c0c04038079a00517141c0f00e90308124404035070038004117220000d00410b020400307800d5190040394000080c084a0301d6075202e9aa0b110600400040305003100502c02480451503801d0042003080c0310108040581e2340780d1124508102d0002e041103000301d000114080d5420580081c40c1f400000108040c00c18141d03000c031202c60700701d9108903d5160821240a2240c0d00291000d8110700c907070148220324a400c6002140a074188094a940714a4410b0004102103840e410260055006102281000154040324030a8074128200540c4030b0f0001c00100e0001800404040c2c0750314280100c5106004070000240306030396030b800c1203001c9a038880729503950f28031501030024005102c40b0320820091050f440a50f8001e841149441440c2303050b949100c000c090950401c1001d40c114140800025130006405140d58643c0d0713014008042c5008000b03400e44139200c0d009410305c00c00b501805a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 45156389 1250 45155139 45155161
    0x10c02040222231f0c0f200906010212030a0e0c18010608010f030203190213110d0b1e010c051c050301030606050d050a020f030a02030f0c0f091e 64
    0xd80420045020403020790b12604280c29a0292039004018142415030500711304045107803141008505018603c0104400001c0354400d600303007030503180c0e02c1e9032002c80c20001e51030004030614a0300e9160421590b5260100f0000004005081181558414000101c0c0c280c1500c0950b580302080c407030000380080109265030708014101041c164468444c10400700da540070030240754146c400701d41d110798a6a8840380f12424803c1c2c1400043e605610195010190301d08441c0c250007100d1000d00032905441000700800d0a0340c441d9500c02d95811404550b01003410780911606540354001c45500304140c0c81d556001c44120300b940d52060400600180610a0020400c080915102c4045103003110300e0522000038103d03002800126140f5060040018803450402c1859200c00d0300003010b0000030920707600f080a081081305000b0b8040c0501001c5a003d030388c040c4543d035094107091010744485080c0e1408c10458844d20040b0a124007131200c1407002200039590111015215180c2120141d1121a01300c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 45157639 1250 45156389 45156427
    0xb0c09040e0601060e120a0611091201050402010e040207021806190f0f0f06020607030504020102241009140112030c170a140306060901120b0a03030c05060c0306010c020402 76
    0x54009040030200241d0322000160181281d00c907588960441024004205900d0411003107982154480e05000c00440c0090303200144450424002520b4110b00c030001ca425180c075103210802c240d6444041105558000c944985190000c0f50110724112140e0b0002d0606581a0f6010340c003040c0303250000310320743c99900ca8a10302000040c910150b4640e941d8480d10700c00b0050140025692011324000b41501050720141e09031052900078000d9079480e14812002000001c1060b811446040070880c6076642410020f007201c03454410044aa181c010350b0061032501d03941c01504090301c2c0045042000910100b401e066420784010940d240403141801ca81c045103182000d070407891860b03d0503e810a501004060480701925156989104040e18182c140401c82c3c015410a200700400e010039803058180390700d04401c1c0c4500068406207100030407860041a001100030600200096050100c1040240c0d400b10b90703266060b195107401c0000034121180d40100a000740c0d0085000000e40f00310503101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 45158889 1250 45157639 45157657
    0x721020d09060e03070c08150f130c080723010c0b280209041406010e1201020c030a0e0118030201020a020f0301090501092a030b01120804090c0e040b0612040b0c 71
    0x34404821103000c0181c1341d0b070003d83c0c22640407441000008100c0d001040301507401c98200910303105552403030500000114001c10501c0c011241c403908070005200b940ea8000a04040c10040004a0070045a80c400d41816645a00e5a0b04428402e03031403680e210720001c100541c440084541c40e283c2403c5d442842c852099100d1665900c1d0f0820308440a55601501403900c0888081c4070400501514800303006095540d240001e070413401480003800e2040c1c1c0c0050002200c4001480c0c4a0300e130701041d0a503002210004001071601d8503a841c3c41da4002286d16034200301810328080da0b407940d40041c4d501c04440750000e0003407296120304c0d40a80c0d001e500c00101250854020b1040341218036008603d1103c090611a107400d00345410040000151510025a03501091011040e401c04c0d40e540c54151107031404840c80c8000300000f150b104080c0c01402415407650b01d51101c0d40c92107108000a440c64419254001c030b405000e16254289003410b55030308150841032140b0300792034003080e48074180314103461 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 45160139 1250 45158889 45158891
    0xf070801090309061b021005090604030609030f3b030d080402011b0302060c0906040f08100606030203090604020d0201090902040e04050601060f2a02100f02060721020d0906 76
    0x100040405041d00304810240c880d59600300810349909050710f42c1c0f4006071500c04c214017451440001824500c2d4034030070301000790501d9070501402e400000d40640c481e0b0002c541998442036001c0405410450b408500300c15800c0100324109412a00c1010312611141900903040600d1a1200e0718040380900c1d40b03652016094441910b560b1801030301c0124141ca08a0000703000a94415514200c2c041039000c00d40e05501901c140c0d2104c060a100c1a0040b1404961080d01000001a802207483d0190700420f11500600043d01130b0b0807004040301d0320b13035004000b80360040040040505011851307541c482e504880e0704641520310f00040b05e000416400ca1062540300090128582030b1f800c0d0000e1165201c2e20481e8483e0b0b032500401c80341c0c03c11107960000400c0307260340031100010f4914401c000d00002100d00c032a02c2c10068000489072071111400e007010881d02d035141150107506200565100c4c0c030608000100d0440c00709101c91010300c2244070401c940d8003058a002a00c41c58015211850f00800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 45161389 1250 45160139 45160153
    0x209011d010912240c0207030305030c0909010608010303020f01020901090512120f0c01060506040303020d1110090609020108060906010807030c020f030f19030c210f0504050c03071a07140f 83
    0x5403404e000a0790508003070100041301c2c20742d43d49080318000c440f0744014560203414134901e5668141c9240c2c0000d484240303807c00c144030100340c1c3e0316140546402800c0f01e559503451549141800390800c0c101c987c11983c264010000d1800c4c2d66044000c590444901795003055451804a5001d130500e5084e10f208580c48200080f403800c00110340d0050000d0003442d0000300145940c410030041e0501c103e100c010090b822903c010207020b4082c04071061490f1240099504807030307400b6480ea00f1921100012582c1c0c0340d0325505882956800300400d580808143c843d04402d0802c00001b030302e28100104011f0400d521001e414407001c0c800c3c007800c80700c03001b81012261030748860b0100411b19000ba4071010790140300507078640100ca10038003861300500625180c4032040c60320301420850420300040040c0030b4540b20050410780100d01d10401d80310b0f07800b03200a0a5400c00042c2010304002c0c80e640704400040703150b068124440080c4044030503da600010310424400c2000c111424a010b0140c4401203001b110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 45162639 1250 45161389 45161393
    0x8040204090b16020d0206160507020a0314010606030b0f18060a030b0415140c09190b070303050108010b100212030414030318010b010c1509171c0b040209011d010912 73
    0x9400e51203443c9280c1c0035910b40d4850b8201c12a65080704450382105220403000d81942540200d0052491900160221035502e80b2901d500d40c2d4040c1c0c0740346520407a9543d000810000c0e50511a055010408a4501080c4503032500081d034130b000d60140d803101c1c0c20004008a0850707560044c0a80040d0741c41707205400c003403a050030001c11008031645452140e81c2091091910080c0c035201c0148107003c50b00c6040c0c101540fa0701441014070002c440310000c911001004902c002255000c1c10004d07120b5500800e403981811201c03400e4a2407090024040c040003e114602207402040ca0ba040136070041207103451f541c403400c10030400c5411581c0b0400314000001801007110110301c81c42064140301000b40020704942e801112881d41603507020b001440344405070601c0a030386402205078140030b240040c02810990b0850441a0720107086da0b80c2e040c6007460b803469529858061401c2c003000441c3c0450920702c1d000000f81100c801d41c0385081080034410303540b115580c051124040540703548614522003190714 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 45163889 1250 45162639 45162661
    0x201050a0c020c030607050c1524010207080a060b04060506040303020f0f070317070501060e0c0c0c040b060f0a110303191401080304090c022104030308011707030308040204090b 78
    0x9440440c66581000101d14420303000103000422440c01074020059a070703a0480c101ea140d0070512240c46103018190704c0310030750140c001d020350103014001c00318189541c4181541100703035484c0c010742e070540d00140810801104081900c00ca00381d0899408201c080701280044d004250b1900310a6004030003240120a044c0d0000e144001c1c04001c03800c481543c05920003a6540fa1210310000340f00300c3c4035420b003051008a000181043c0341c4120008146185c80c0c40c0005d0440b10b08444d0003665071000700d100d4a40135802c204041c0f03075000c2a14200010b01c0d1b1000440c10074418001d455441c0c41002615400b060311a8808000c03121001054a81303a0400703078000c205181070741c100401e0160800c041307020390a120011050403281004010741c503180c0b80200600c00b07004058040802e5000300310a071229a45144ad03405091400b180185659505601e0301034001101038010800c15140721102c8040b00c640040c5010640360981400503031550b83c0d02c0007a018210000c0010505100341c424000e11040e2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 45165139 1250 45163889 45163891
    0x9061b011401080613060207050a061103060a060504080c0d08040305011802120114070305100515040602120f0906030a0204030609230a030c140a0b010f090c1707121803020105 77
    0x800c501c0007a6603c0c212581d850b003003a6080c1000809100803940060040e5004002d807903c104191081030400743c84901c11a28001c000d450100380c00420005546440300f00000504010305156003418200b483d01c503030300d80300241468001c01c000c1c2585001d00c10041c050310000c40d0300400a101c88a000140680b0240740200100d00415034600a0400500b040c0038907004042821a01c035159a100e20049014020185c48200d615580d0340c004a12a2100401c000d85c00400c0440c00d076071a49480070087c80e02c1640d50345064901c1007403029421a003410021185402001c4404546079203410101000900c1140d01c02807906c2c1c030f089900f20400200618403c406603011014400d403528280000c0c0d1140c040440c01000110005d014000140041d5941981a4451021603513214131315611300d007840000f80c111002981d03034190204410451806540e0080b0185c1c0713000c064070103001c0301c0000302c0c00014000d85c3c20701001000c20100c0e01d9565000780c2d030600140003000320401c0c0c3c50502900801e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 45166389 1250 45165139 45165161
    0xd1506080d030b060d0908040b0a0e030607030501120807030315090b040b01030501180531050d0c03050304060b0f060d020706060b0316050c1f0c020613030906030209061b01 76
    0x1440740602070180c080d1050511a0101521283ca0b1503100e41464008012107201126198010b100100b0f0314a6844054024201107844034030722031020700101860007000410b0032007018105001403003001540b000800c042380d802551191610300038034040d00904004103200c40740c000a8800000c1d883d189801c00e04070b8507401e5808001146000f0011008d542d024003a402e80f0442c00550f100095120341e0225502030000c078101d01000510141c4618824080c2d10004440c8608900d52014040140440d400104882c14400c070300c01055a0040c040d8000184040d00d8a50f0300d00001007292074104240303a49001c000c041039502c941c0c030348040000750401081643c9040c508140802c60042c14400c69024801070080300f01410452402200c0301c1c0e02c09a9002070b42d00800c0240340c50007051791503044107000d480002149008100307200a14002001b041340c9a401c5110640d0707004039030030400c0d0342c06580c0145400b59036078030000045440d622400340740302d80c8542d594050040000065100b80d160300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 45167639 1250 45166389 45166393
    0x70b06030c061b010207023c030d0c0303180b060a0b0406021903020a140102130501050f040522060e06010e01020105070e040e0705030a05032214091302192c04110d150608 75
    0x34179841d03090034003120408c41d103415070701110b0070884444c02602c000040c14400d02d00851001c100502821540301941e0045401e46040d8041c0b10b010319102d404007010b0610392074413900386464554000e41d56138141c0181c10020140840403000d040c0300340824001150000ca5241003100050300581c001c0d4811400c0f130040790201a400319466204100721020542c030303510003a040030b0422003003080b0b12a540a10390701410216130103001c101701d070b40207840007810f100f90480c80d6850b050b4009400c0005290185046900d0a420030003103680100141411800c00d071000201c51481600e0741c1d00c2d06609030070541d414409c0060640805c04000001e1a10540000b6901321080017001e0301c0002d20707554081c95400c600c0c1a405010513007803400380c09510000c01c2c8440c4200204a40104842ca038059000715490900203200b40f11007102003081e071404400a050b03514880310344050781050460090402003000303e4000e185185903449a002c042d003c2c1e041b0440d0204e2240b044500c0005001ea881061094 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 45168889 1250 45167639 45167719
    0x31803060601020705011403151507050c0405060607060b03030408030c0c030c03070608040b090703120c021e030c01030506040908040609060806010539030f070b06030c061b01020702 80
    0x20b52020504030212201078448500800065003110f1580c1c000400002e07011030b91243c0d40b8440d40d20403607505102c1b4440e05220f6a9101107061046c2001c0242c0c000034050790401061041c640c40e00012100c040340c00c81c800050301c05403d000070341144990740c481611840301183d41e18170044049000400070908030100d48003100e00d030090588591442c86000c0220b0400e0001401150050461541c8003800e001511501d50300c9688514009035203521510005941c0007080007103041a42c80c2c1840e032401003007084941165580004d83da0185e40d07412070304040e29480800c1207130322643c2000c0c0744180e008030f039540c0383c50301e0f1007004140703080f9842500c0001d00030601242031540120101c8252075141c880038000e0781c1c800700013050545400c00241d6110245031107080904641407010f07214081c100100b60f5a00c0c0c1140c10140550000503210030b1090700990303d8044e040d074500c0300300c03002c0345404684110201071040043d802409020f2001e500310346a03030b1008140e04a842aa201e54170f681c0903208201c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 45170139 1250 45168889 45168901
    0x3010f090f0902090610030605181603060f05010c03030b0405040803190e191b030602130512030d0b01051201030507051519200316020102070e0415020d02040803180306 74
    0x58411246000e5000804a1302140c064101290525488000340c1000724155a840c0041490100c0514284090030000002e00c08001e03010f0145400c1c01c0100c3c501440300604061003500300c038840340300709818000760309031500c00c06000790031101002100620070052481e01d400c04003460780c012501441c400c642c0c1006084100d2040c425500c1002c0030f84002c12000e0301c24120702c0034400c4039100030f940200384110304042c0302d1541405480518490740c2c01607255064030881c02d20081a42d000107104015000c0d03e01c00c030320710000c15a06035043c03004c2e010907100b403072000684040c46180100e4038002140800801072080000f480411554151083c11113915901a08400360007a031001c01401080c1d08041c1041078400d05586401d02e000c03d403090120300020038018a154800d042581c40800c00020300c005641e01807141070000d1402643e500f8951600c0c0ea03400750142010809038000039408070340301000400341d074103039405001c0d0f000031659606000c6c00781130840b91201296502c28071610000a41c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 45171389 1250 45170139 45170141
    0x30806090705040b070204020c01050403020f300a0507050d030b09341b050114010503070b03010b0304030e04020301030501050a0b0307050a09020304110d030918020909070c020a090203010f090f 85
    0x21041001d680d032181440e05040404c42c5680c0010070a81c0c1c02a000c1c08085041700e403c0c81a039005a10070740041251440305161282030440703400e086100341c500240b42e00c41d1840040880c14004400c01c0301c05e03640b07070280b00060740c050283c030002078507910421a030700c00c000c0d4040e4405218900100e820b2451030b601c3e00e200410300e20307801400011114801c20881604885c2501c941a049031904189090900b821484d082e078080c03814098905079124510f20500350640b0f0026400f500040c2c010700701507418048143ca8600c018880d100224a000002a041c035100341401d10312124001c006550340d5a480c102039000e00000e4640c0403c0b945000042e00d450315002440b10101c2c1d001400940c1d030203203018101c0c0002c4d080208203035041156a040035040d980c03083d0340521035030312a40790042c900b0b04190140743c5103050490210281c501c1040468001c0e070b07806d14400da00c01c1c0b451401c440f200d5500d202040d400440c5620031110316001100208000160603010015510b100508022044440c06100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 45172639 1250 45171389 45171391
    0x6030303010302061903060e0c070b090c030606010c110d0309080f1b010c03030b0a060f1206030f02061605100518070b0405010809160b190f021203070210060f0303080609 75
    0xa5020300104143c1740d212094140c140c07041c6a0500380040c10582d070740000d0108000840312450782c2d120003e0f40408202554111940200005c0014000c1c03075221000303e60b41d010302410003410b2001c030054481c10070020710304640c00f00c00060300c0101c25220790f00c3e01901d01001401071100314002c40c2c9410762412800100d41c001c0000d44035a50219480c03100041d60503405140040d010140c80361812409a12000b148000420842c2c0d241301ca40c0000c1d030401018400b10803e0750708060300304903040003c0740000ba141450f19804590140d40c030346829002e1a944804914024124003a036154070164000310741c080d91061a40344c040300004540d400040c0e455800707901481d80c540c1d8042c00700340280c2d4494000e466000c1c00320012117090440b0b100340803030b40140c42d5116880e2000001a290700001a45e100500046503500340302c00d0101750364101a40310000c0c2442211030354400310015a082d0310801c080070740b001c0008002c101c100c0d140d141800c1040450302068000c82d0100c0081010360602d00019 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 45173889 1250 45172639 45172643
    0xf250f080c03040210050a03090602070b040303050105010918110c0d1d0d08031302060408100f0b06090d02221d0609030306060f0706150909050d030e1009020315010608040308060303030103 83
    0xc0034120040178003583c8640190004400b095138401860000400c6403004111081c040c21607000c440c0380a141c01070503200145c210301e0411900d148100418400004103141c0c04c880c0050119013100f9890446907103001d142d00d411000e104aa140400650300000888001e2607010382001c100d280c010144070140e281003c0042c83d0620810004100d06282c1a151b5048d500c0106818a81542c2d030420310300e0115100b1a004c8e0041e541d90401c45140040e114160781d0300800c0d2015403c02004000080001000f90300107805404c000203140c2200c40c00701200703408a00c03010380402507240e646c0e1800d94650443c030851036039442120045600140c0c000282c07449894001e0030289801c148000040b0b55401c02c0c1d200f03c0c3c203641c48904140582110500c00c60103448081e1001900707030040c0c2002480d00303036442660030500d440c2c0702c0e16030b00d13561010410b0480c1c03108440e03000c50b05040e1840800d14100c6000385100404000070b002050340740d400380341c650040c0c1c0680d8503800c2da611140c04154507440b0038880 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 45175139 1250 45173889 45173899
    0x30f02030c040204271e0e03070803010e15030d090603050a060503010501060c050c090928050106090f0f050f06060c070506070303090c0f0b03040b041e051e01050402090f250f080c030402 82
    0x3ca006e410fa421a500e1021000103490501101d5942c0c03040941080c3c02c04020344070504100601442c90211090039948120010005d1041c403190160100c003040c000c00d010152500c00040001410f60401c00082801600030049983d40c2e050007041d400d14008211401d000e00b50401607540b400400850003290241c0191044c42005828040500700b0401400d200a14103a001404039800380b1454000f4406500c001c15142e00c01c0d00540201c44404000c070314030034502000d110340300040c0c0c1e000c030340e2285064603880d588010aa11603858001c3c141c0c04941d100f400010145c08040e8160454088070b44034103255031045d80c90710480342440819005501a9036024400540030031040440f1641050007604450b000719080e00114001c500c0803070094599510040e00740801203841003103443e040c0c1d020402000305040c140e001034049400074252110819510001c038070001600702849c0b08a1692803a440c000d0040ca42020f000000511940c1010030403810019000f81000e074212446aa80105 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 45176389 1250 45175139 45175181
    0x905030306041d0102042303030304050d120f060b04030308010b0304050c0d1110090501091d0a02090307050604090902031c050304030809160803070506070302040f030f02030c04020427 81
    0x1c1480000c001c45807070b04031146010004110000c1082c4000c0c030107015802c501048801c400d00e03c051084009142945c021781c0100108408140c020a040d800e80000d0300c1d02c0c00c00040a2400f0340082d283c2280300c02d0f07000e4509480011030408050003042140d10903103880d41282e0744e4030b030404814041110060302940041c4d54480c4a0300c1e060f0000a4103500c60760214120002400200da4007407030100e45c41c0701140d408030081c002580c000e5201b00c002c1292114007001110f041d403c0001c050000b500c1d184600e80c020845100341d65007844500040c02002d00b08980f1540c0d0b800b81c0300d000d0030a82e5400c0e402402044030500d0500c000030001e030580340c9181c0b0748d6403540d20342d960202c2e98803100401d0388100303000780b014041d03040562a44440042201500960b100c1026007400c500380b03540a40310405040c81040100255110494014200ca401c0081d07516106d10320b0010030b0404a40d0041a9840741c80001d01048206d6405100310322030695002898120724030903090400c5440382c1e00585008400d1003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 45177639 1250 45176389 45176401
    0xa03080313080403060e0303090c040605010c080f0c120d2a050d090203060a020a0201051005030706080406020903061608060307050a090b030a051b190608070813050f0105060a0909050303 82
    0x814030489041c0b107150400d1070560b8a07112101100c500341d030140b50300e0700b0001c14080003034070411415480f4502285c0801c60756241c41300103032940d881650300030140d190100d20744c0c4480c00e001065454800d00700f0165110040264405076860380715001c400c01e440d00d0054003030b424a214805512905148200741468102e409006503503940102c0c0340d400c42e40d5280d019080c01038609118050040c4807242003da2540f11420b0040c1c2507903001410700c002c00d80744142c2081503950000c0c294040321a0b40c10a04800e454605001000e8800c1100041c1c05100f881c0c00e1103040400c0d4100350306d5000c403d1ba0f9020264a41008040e1240580c0c400d140e03001241d11000d00c11040103900001010600608807003e400c4660707551030a100c2542480b1210103400380c60000d0030b0070b0000c03207101c42683c0301440000c41c0b42441c1d400b400824011704540b040041d55400a21a01480703403000074241d8000003224004041010003034003a0004031410342c051556001c001a078a15240107000500d0780c014060350441c0c2d182 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 45178889 1250 45177639 45177661
    0xc15020a080306010c2a230901060e0105120907050a080105060a05040c021f020310050a06020d0509120a12020d0309020102030f070215181f081302010e0402040915050a030803 77
    0x240c0c0055400285131800020709486c0c03001d100441b8a00005101012441c0030030840000f1960355112850b50740e00e0f035041034650707540f4070300c541914401d0070408008550440126828050b01d00707045015900c0070144a54110001006c01c00c40d8021100311540c80e440c0c02d26030b404d031041500c001780c00c8134180006104910303094102c10000d50b034510440d28664505035031b00c0c0000380322480d10100544c0c000144020b6611007580070002d06001c0d5400c00b005032400400940d107512200540040146c0810606040d51321400d030900c6099060084451000a6003020040c9482c1c8014660141c402c8040e002c18840c003a00030f103010a9016000b4609103900701071100300e66401810101c0c1d02c402581e11200b240500d20703001d00a0102005020441003d80c00305010300d0341960105141610f4007803a400380200c0c0d02c902d803d940070006405070002000300e4801030b070304640188029640325001040100e0746100c90741c081005c1344098070000385e80680d54018401524107900016000072130410001d0110101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 45180139 1250 45178889 45178907
    0x4080d0e030102130e0109110a09060309080f030103030302091306120b10050a061206060905150c100c02010917030c0307110304080109080903010b120309010f18030c15020a08030601 80
    0x50000740c43e03c0d000810207811484681c0201c50085d09810050102003501d2050202204003030088030301e0002e050030050100d07d140d12800e800c168071840c0c001d04008060041d5800c1070640d182c202c0d00e070b50b1a0700d0098060340110749680d005036450300300245290300c03500822003100e055103182401e94840e03031600d4402d058000d001880352008000c0010711901d5038802000103011aa440181c03200401060006841d080c0d84170108201d03075240140b1040c0c1d2048602c0f2061000c010210b40e541c91031090180c2080d620020850307450740781c0481c202510360190060221030340712b03a010f60100905600d0f04080350005a03a110b0440c8014030010b11054040e082503185401100100ca06196403520302e1401d6071801d0000312040e030004281c0b0080d03030909000d031001d0010120356144c8540d0720300d04001c1d5030340645501c0b5410461050840603107203014103010b805030b419030020800400d85a040000e00e41074903105030003000c1c003426440c1038030a2002c2121604641d20000d05855511803000440754421 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 45181389 1250 45180139 45180167
    0x50112020a11060403080106110f060c0a1214010513050c03060103020306030f030705030406300c0c060608030c0616080403030c0e060a0801060e06070807021306080d030207021504080d 81
    0x44015402c40940740104001c500c658400d0752280c200f07604182004041000030700421410341c3c02460300300c2052402141842d440504a2455030b250403c414044403000000286a0707025464100d0b80c166884d80921304074103079002500d134002100501030340f01044410440380cdd2003840d01c1c01e0000c074400f98402c1d00259007080000b011281c10407000700303c2500310343c00010125560742c0001010000f0a4004410761342c081c07441c81c030307680702030041d103510b02c54600f40c0ca450a048250350741e140e082214055500300c0e80d25174005804004980c8c43d940b1159503640556110001c0e842142e0009078540b04010308144540c0103903646030322507100d90382d0980c05131440041e40c4c0e0601a00c0200100715031074200c05803449a9080d6034407011549080c40207403c440150382070301e02581c410070400300820300345022030700307907a5061b01c00d0500c860502c140c81e802019030f078101510501811194215403a4560054a003c0d030086880b0314400503004031200c1144a184502d1b14a40c0010003045000c5024a4044d01801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 45182639 1250 45181389 45181397
    0x2030c091807020c09010501050306010c060f0e010b0a1401140d09080313110102121c060302040204062a0c0b0702030a06050a2406090b0703020705040203190e07050112020a 76
    0xd610354002034005050300100780038074010104008810f54100a00c04019009a422010715414440001d00031712004110754103001ca120424410402e26502c04466180c0a410400040e28402841406043e28030840707407285280c4100410364608030940c02c0c2c3c1c5644141c5aa250490300c04680003801e0b08004882000c0996450b8020081a00139000394843c1045e00600086a545072504440b0404a80901030443d40b200e154401803c1080301214161808c00407182101c040c841407810140c840d81d0402500030b40007250001da05038106815265284040c0803410f2402070080c401742c0c841d2144000a40807441c194801c0095031900130040506d0790014040e50310144058540d101a030328190b850110103070355424000003480708102006244044120746400c40ca207481c03001003115099006880c02c05400050741e000301402041204000c2c82d01410070340d281d260103890b0309402c980003100001800c0c1000030008080401260b03074029244140c44030500c01035448000d00080d00300b00c07400000c2c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 45183889 1250 45182639 45182647
    0x6071407080319050a200d060314070e0f04050c040f02280e010503090a0b06010909050702010f0c0c0c0e1302041505150406080c03060d080a030c020106050307081002030c 75
    0x4604401c0c01548140c081107a00d0803101c414002030300445500419600304107190940c1c2010350f0706101c5c001880c07007180b081c42580b10380306244848010400c3d40c1c0000c20004603860180b505110105e21710f0200c40c50340c0a1307520a1399031295011a103c0b000c6900400c42d401003440c0c01c40790b1825038045004992050401401c0810203081c0b809020031481c49403804130810700c500500d8561151580c45810000c0c644181182084d0221545d0380120b100c008008a41030710010301d03540d01c260050310041c10b01c414248040d0078010f40203070003090809a8425001d0810316032529280c09048a524126440450742c400646800d420400e4600090503190b1042c0c205103008025994a0240070441c10044039a09002450182080034004612845841210741400100945c80e0131602c0a6805136003d01c802d903503a030704c020000b034400e0203002e40100780e0940850580541c81c0c1c550300c091030050098008100203078481007050382d5400c0c6445014175a6108910200340b25030b99401a6811050601d003032810 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 45185139 1250 45183889 45183893
    0x7020a0305160618050115060201020a0c02091803030a0c1b02090f1005030a050f010609050606120405030f0d0902010f02010510050f060903010c020d0311030408030402041d16030212060906071407 86
    0x200004102082e11503070b4580007c80c5402642000e100010100c034002107290040c0c0d0100580527044034540a03205274080c0001a40300300c54107102c10707862030308003080d60765034604804410001d10030900c003840081c0d0300032075418101c0c4ca64801114450380042040403190380701ca0300c451150400906141040800400001b80d41d2000c02041c604640b1030707005000200d000c00d0415084495a501104080c2c1c10501449000e03201c071000c403990351150113410100ca0350741d0300b485880c40c810b00c40001412240090131082071203860784000a680d00c02d030b94480c0d030901622012800d0700c1064440c40042d403521541041030f880d2a2030706950ac40c1014194a05012003000045e08407810f9040d02c2025800043d02484055458840c1d0002036150060305070039801d0685901c040707800000c0000b40282d69a49044400d010000e9901400d5681f2104640207501d20031034040b08404a44230072405078061343d100c092000c4011455038496201c80c40248070b15910b0540840e0b11882550300510008010003c001c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 45186389 1250 45185139 45185171
    0x3010603120c03080606190507031b0c0602060603060402060306041a0d050d09120c150507060c05040618030f0b04020105070c09150509040c0513060506040e0a0507020a03051606 78
    0x1000941944a0240c0b0301e0071814050400032005251510a00c402c000d20402a008820291265500c3c2d18100381c48030064a0203035000d200c0300d99420140040d00f40c0c52410086410300042c252480f95080e00c070183ca0f548285507036900150b0740251703c11002d200140c513a0406074480c126170012981113417040380400700882d4102e44000d03800c0e18141c2105c180d180006404c0f040000061140b48041c40610446840c2c44203411400d014034000e28a1601842544601c61000d8a0215070004400c0189075014000540300340c6c040d104d00fa010030b2205000303409a080b061040d1301202d400c80001c03016032886541341014100e00030400c0703060020604c46c14010961182c05030010302500340d000542d0181659900341140c889511507031040c0c02c68020400001c800d8000401125015201c16101884851801028141d50303000a42c128401080028801c8a04001940a440511030400007900c42031000c98607408000c83c082c02007181082481541c01203d120424168000e040020f03100341c0d5049540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 45187639 1250 45186389 45186413
    0xc030603060f02070507060206010b0a050f040315090501110f070b0c07140105010503060a020f0904151509140d03020d0e010207051c0b010e0106021209060903030a081005060a12050603010603 84
    0x600300b558003180203400c0150800c00c0c0c1000d8041400100300e650714000c422640c501c9412801c004200021400980c1901e2100540380034560040900107a03440741d40c0850f000744260141526550700745406a43d01000c140112851140d140c2196071a01c81544c8942c0d942e00409044000a4181088071102040c150012034201c0e68100700085515490581058078210020740903601d0b0350700c100281e600c40b900794800c4030020f150a68002c00c4021841c190160035103180d80c4501c200c0c2c0011080507032038a602c80031341c90545904600d82c4101c090f184c41840000001c440c0000c01507445031555101c6580071b8078071100e601c1414411900902d48032030100d0502d61a040f43c03000c2070b100d6021400200032001d040385003d00784108818000b5172601d28020f41e14030a518540e03809038000100488162a00c01c100c650424019040700c0d0303a600e070080000c05100089440f040c0a020f05180480c1503e0414221114246295518099007000c1d405500060801402c003d51643da0740307000000180464940b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 45188889 1250 45187639 45187661
    0x40905040c080601060311030121150209040f0b010e090a0209040c0306050f01020c10140f030c0c0706030603020603040308090a0231050103080a030c110303090307030306080c0d02040c03060306 85
    0x309040c0c0c500b0305424903100040c0c01c8441810b04101c4104c2c80d8015117829241111119040c482243e121001000c0d03100140c01d0b00038100c0e00360003620240d490a603400034012040b09680c200721690203030705540100c6203030b002c51074001242d201d00c2d51034078600b1007200c54010f0190a8014641a0b810b8000350881e0406e110b40800710b071300c40a08001034507060103890521802800130f80f445401d04000200f4020806003908140f2a07940500b6103548100d0054942642079500c005540703041071124a0700c035411540d00e1a0840c4113248010415600c00c0c094035084a50103465181503403103658044c2d80240d0001d103038200c0381c8100d03082a80503a6803004100d40c1c0400c07221380c11003aa001c10b0400c0501885860114104504000c010400201880304844074860306240001c0c2580341c0480442e00d056011003100700503c03011007481110071020004000007480390b02c0410920f0364906001d034481580416141d481a09110400d015042035084889800c02e145400a0340c0c07600c9076940704c03c40c2c0b03110582c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 45190139 1250 45188889 45188903
    0x3070210090b06090619030204050705091315060507050c01030b010c0b13031101090f0605060d0b010609060816050a0f092c0901050f0703150302100c0605011a0703110304090504 78
    0x81c04003909048030036a802517025034643d05500030303903001c807a140c1500d0311000703025640c0c030000199854410030680340d480c1001800c0c1d200c01004c105408020b440b021f5070354014a0350050700029a140541c00b01c0707600350b90100c080d00e40c151840005400418500751514188070303200c0e038941b001405088041d44616640c80600d140f00307000d13040c0100010a03040034070040340c0c1341041007400324581003150400c00f617204c040414070b03581d071401007405c2076a480300080c4402410360000c00c00c02c1e0403d0311801a115203640c0c0d511b881c0c0da0740e60140440100c1d0305100002c513208102d190092446500038600c0c043c41410a0352000e5601c680207490040390032200600110600c8860034006c0741a41c1154011243c10024403080c103081c80040300c5881d01400110626a540002000103008070050390700450f0010802d40c032440c4031040243c0090f0034214100d80340fa14100000c940c01c540310140208015180c0140340c1400226901915440c40500310501c11344000d000014126a090150f01e10503407240341 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 45191389 1250 45190139 45190141
    0x20c060f0c0d0f05070b060d120504032018060315070e18010509180123090618060105011809020d0615020102042111040e060601021b0904030503070210090b 69
    0x10000d82000002e000c1982000541403c940d201ea520034141c450032a004000c000e042d4813031310000740c03644603800e5004100307102d0341040300340c41500503018108403070042182051156030343c0e140200094040c18000da000202c40ca070f504e21000c000c0c41c1580d02ca80701a04031908402003401ca050720795002c5901c140050042d990020303a90811901280c1020001c401068003541042c00148464034010b040700c040e0342615807404481c0c0b50035048041110030501450761180040340030f461070400112207a00031445442c0104104c1d243c203404610b541d41c0c0120240016908000044502c3e0060070f1128000c01044000424900424401000c0c089840c0c800020854a490f1249002c080407503800701c00d59205000801101940c07150072a030441c00e05400540c114501c0c54244110305003620f012350400e1400b1100d0a04a1000030464004c850036000c0320f184140324980e6903481c6402c402e2850304441802e0220300000d0250000d590080d01d203005075515105041030800131900000310950b41605110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 45192639 1250 45191389 45191407
    0x30903120405010b0a091b050319020301090204050a150818011d0a02010305070f0504120201110114040c050f031009110909060a050c0906070f060b0604080601140f130b01020c060f 79
    0x1003485c00040694035000d0201001b503030300c82000ba031454070640f02400f100100182d4201040d0341c1a5030000114002152a96124a40240290420300649000707114104001c03440d68894503e5020b4691a80c0c0c036802565120282900b40700d150501b844002c3d900c0d11341d4441c0480c88603e0f82410ba0780300310002c101c021900d00004080d681c1c09008007052089102c612000590700600720380a1712003150300d500c0340103c5440101d50f000554248911a07500c1c01e034070080074902c0d81a6560040d070088070100007035900d03a001c0044000c681c3c0e43d807560542c081040d15884901503004140e030180030b40c001d100600d050402207010020105c1d2101c10580111300ac21000300c00131710401c1c0d0001514507000b4200600c1c071000c1045480f490f14003504085011307644d20100709040d040380520b040080d00305901c450340c03017805550b00c40b0280502c035803140c4054554036050414034915400844020030f121010107a5441ca20000c00241c0c0c1200d0440c000c0041c00900da8407180003c10035103d85e081441d55a00c00700d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 45193889 1250 45192639 45192649
    0x314070305030f0c040e280f0e070e1608060d0606030f1a2707150c060506041406060d02040902130e0702070609170a0c0305030403030909060b03010b030903120405010b 74
    0x20090002103a0502c0140f1040c2c28480285500000d81c92070b891402c0030407c084a0300c1c0707540071040c0104a080c40d96948480620340c00c500c148191480031508070a0300d0b1b0100100802048417040e410000c14001203240d01e1061171000d42100c0040c0c50b0050900c4c05442d00703001e031491074100b81d4007411906070250030011448002410031200056500d40743c24180c55600401051001801c1d40d0120b820030100300394810300c2010018035100f581c14101190b40f0201600c03800700244241c4280e460040020f9442c00d00d03010f5280c0c5141c40207643d501682d211401c20510f0f4000405412801d94240004607607000207200403d915100000000b04030b5140906041c00c3d090018800300441d000284c3c00c02405800801040c03d1307941c8080b040014803444d010b85840c0102004000e004014103010000c01e015000c00284140d901031f83d200c50b0016142c400c1841521528403468058030b1081004121111b1300002440c0c00074a00ca0a691801401005222003240c0c03d941c1510980d6548050b82d081d4600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 45195139 1250 45193889 45193891
    0x90c03060b12300c011e0c020f0303070c1401240503150601080702250303020c01020d090b031302060711010e040905030912030c070303050a0e120a020d0314070305030f 74
    0x2000b0042c400110010300f100d000d054603041d8000c00002010026420a0046064413040700c0c115008112403268240f403104000140803042280c10314100b1010401480440d03002c01d0800c0701e130004e610f143c40750032013120b08501240301901c00400b00c10004400b01400c1c050103c0c40124580110402a1000c2d10801c0e104502d80c851f0380720ba403080c8011000e07410f08480c010703400704003401d080c04c4954a00009a082450440380d00d41031300500e90302c008824851182c501d003a64007950885412340072001c01a0390b03a910034a444030104200000800c0300f89548002554059a024450403084100c2e6011031020303089600101d9100c80c00c1c41d200300103540d110851038040c00b0304460a005850583d210241ca901c2510881401904462a801d00406042088600001207001154881980ea0900410340d8000c01d609030300040c1e51420b4032010b882c2c0130251248010032040503101c041ca5681c20072012801540084007840740c00000307041010710050103400121b009448040e42c03482c0c440003607d0f41d220 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 45196389 1250 45195139 45195169
    0x2010219030b0a210219050a0314070f060503040b041b0305030910031a0904110603090d080105010804020a091d070b04050307050a0815070512012c010602060c090103090c03060b 78
    0x56140f05064120136054480f00b0b10f4059440c8208074054030841032400400b50419908442c00c10340010400c5451031814000b5102182902c5440d0784924088000032964841c030800900c00b84049030109a5000640381c006e0f21a59004507610385040f0003040f0200954802e40c0c5a4001281e041b100341002c400d02580c00d45145800c000100e204d0340343d001404c4400d00c1160050384d03200006801c1028a036010a40c03076100528a0361031380341400a00e61b460728200300d1000054944400094254014031046000316801010840c0035401c021305000140300100d854011200403080084400c1c00c1030000c10301510b400d80000b42d449003000c090526040c8207a000d50b014001088080086039004200c126a010b100f0000100584615404903880c4c005d4007a20040d1080c1c0c1800016030755142c005501141410752200b8080000082d001c54058109214000250b000040018010400c5c1401010200414140007410b0b010540302c140702d0900c681c004440381baa4a0000c00300d18a003000054032086 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 45197639 1250 45196389 45196409
    0x30103060e0606060d0209060d0204120c0b0304051b030114010306050901061e03110d1406041a10090507090f1d100605090607110d110906040204050108040209060102010219030b0a 79
    0x108010020031214401d28031942c10155000c107c8000b503544a0b011240400c10600d01552540e03190f0281000c2c02440c480b04807004401d5010000b01041014140ca10032364110b00604071420011011250400c620365459505559860f8142030b40500e030b80c02c0710b010394094440001e4a00c1d000a981e421141150080ea05800c0021501d00d40500320b90b80440960703038440f080c0c407c13980024000c98480f642d1848001c0c0507520400242c0004000081c0740d034803c90207030f41c405540800d240340316160481d0a036100d00303a003100c12500348013400c55900041d420103070300d107400e00ea0256501c0e401c907a80165a0481c91008500000b0010200f51038031010380c0001c0510700041e40f02e440d0001c00740c0300d803040d80000d6015031408101034041c810700e50011804020050702c000300500c51031403d40801c0341c58404491241d00a480460100d0402b0701c2510166803068580381e059403216001c100072154010416411590200300040a590341c10b903a044d14042c5644000c100680c1410801240d541280c0010300c02c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 45198889 1250 45197639 45197641
    0x506090c090a0b0919060e090d03050601050723070b0a0206100e01060203040e0712090b06040c031104030204240303090f060f1b030c0804060f03050a02030403140d0603020a0308030103060e06 84
    0x540d6035001241c0c00018105c254071004c90b5020120000c1d003055803000940c4c8a1500400190500106400d95030011a507020001c0c0c2d1f130780d400159901d0041900141c0319020100c02e0300c040e40940c1201401004020044416560342d450b000e010035400302c0d55100058020006000c0b01c80080f0b4810006400309c0883d824039503050445c0250b51340a41d2040003c1d20b4604400b1500071f50081804094040c030340f1401303201009041c01d241540c00000c2e40c807903000310f19110b6450f44441c801d100303080e441c1d5444c4a02c24a003510310f400304405408c41015109c9404185203402c40700062030b5100c500114800e4507200003192508100c0980c0a046034408418072881c488a0401c603a8007480d1743e030710000600c4000842ca006414110782d031001000c001840310f40009408904550440100d4080e00c0255609001640c0c0c0d00742c0e01c20aa010030307540180815241c11046541d00c0100000e8018184049000036000c2d949400003018903c460740250b1321508004010300034007007140a419400dc0a0380024031403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 45200139 1250 45198889 45198911
    0x606060a050702240a0c1211030901030f02040512011b0509061b030c010f05090d031a09130c03030c03080a0c080c160501060e0105040b01020a080a050d02070506090c090a 75
    0x200d0b11505000900c921001c4c0c41e28081c9056a000303185100d441c0c04616a16644440c3c800303024501a09030580390301484c000c0d416401480340200f40e10300200e810196042844900054004e0b1070000c00b144c031400d80034400814591030b89500c01011503035160000c030f800741d03080032040c4420307160342d040c40c003008002c1004401588071380040300d80842403007100030100301c160701e4400c0c15070081c080310206650070100c0d4604c1e04080384d000640280d680c48155050704106010940c129002919410000c2800c00c0c2c2401e66898003200e1180d03c2146561626910000c0d5600c964080103541c00490100b481c100d00b18091507449507006501010501d02080030450b0070788090b1051100400b4003c1801000030105044042400d40c5807516501c40005c6c8116502c17040d02082e17862003406628019442d110600401e0340c40001c0807001da58010040034a42030900d1022282c80d401803404600080d020040c00c0c0002d00100314040c49048004054510381c20024108030109101401409842e400d01c1e0022070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 45201389 1250 45200139 45200147
    0x310060f3c0b0a030e0106080a02010c260703050a080f011d0601020c030f0604020f100f030513020d050c01030b09010b0a08060a0302040501031a0c1606090c051009080606060a 77
    0x21515003140810400d001007540041c0340280c5800c89842c0c0d810202c0c14050168140d04040d1158104c20028400c01c2d0703c6902099840c10301d4a0040e00045440040b040442c079103003144000b05841c40385028000e120700002140c25402a0021000908000750070428a030b40247c107a90085a8454600d000b54541400c0c400014400606240711440d01c40100b03450f40c0c001c00100c0c402000c041c003645d03040700303c8185594540d40200d806a00408424014a0a61602c405407a1072401c6c00c3d1030b40b00d0b02c050000400c900901001b0b004c64002c00040e9401c0c000f5951305100040007900c500c1c01414506404c0000400765145280058020010040103226004143c810385894542c6d9242c07100b400d9a5040c00100340384200d62010303403c54039010000c4103000b80c3c40c1840100780c142c2c0042e101d4503110481e100f070380752243d600f0b15082003215401c0314002502540000c0f4149004001028045842e10300145100c441c40c0780010200310b895004224403003080c00b019601800440f5494141106048090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 45202639 1250 45201389 45201449
    0x1050a030c030f0e0307020103060512030307081009020304121805060301050103020a030f0c050705150f04020906041d030405010f020105040c05040b03031905131e031407050310060f 80
    0x1051540307a501040d6900d120343d01440460b20304101c10b119402e8103000c5642c030781e4814070040c1d001900b800d00100d0b060501c02003500701a40c90900031461961201d6080701c50ba00c020303141c103400310407a540000c2d58a50900144d80250b0064400c10600c0e00303080c6020b000c6000040c11a5581100740008010303658800094904603042030801680d200c2d29000110010611800b007691070910306200460050340c0b1a01810000b4800c0d0112504022003903402204140121220001c1e09a5a00003030f005080613110645c0040c4054004501c65026808010074511341d04513802590b400401c080000e5a44481d400e1411b000d90300081119040c1500d50740303444442070091902498444c42c00f440c00d62010421240c0c0301e201101c81c940321401c4241c005295030301128066014200340d0402160704030b060342e03400c105006d86498461600346180d6480c00c0c2d82142c8501120a40243c0f140000c007074905124030072100416031000109a402d240c01d03480d103000c503600031f0b01c0b1076240c240725149400350f84440c3e9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 45203889 1250 45202639 45202657
    0xa20010c0203070b0d021b070f05061603030c0c14010b1003091106030408040f0f09050109020301120201080406020c1209090109020a0f1206050a030f0b09010c14031b0c030a0f05090105 81
    0x50717840d0000880c0b1700181c492042c81148114924105038454440440c00c0300a540303450482100f03456599080201c68080d551100c0c0088106100c0600006c0c02030384843c0e83c2d0040e134142803141d1b80803a01c42821103645048101c4a43e51140043c602520b480030414030815490300f020001c5c03402c0c94490218800c05501c0040c022400000484c081c080e150069600501c3c2c1400d803a010701d5201c030202410a580c611580c900e040c10400040791440c1c090082e00c5c160f4229200f140c0e1500c101e5001101c0c001c4010b4019960541e00f0070080c800c1c21030501c0301c0d02e408600e240c40a50307105000014480980c405074016003290b481807100090295001e9403480c400720083c42d1000d002c01c12401541c0040c8065800507078840c21814000040005a501e4110010300034a0540f040b582c40030390640c02d950296240c180094504040c14440e10314980286800021020060f041e00d0460072008503542e0007903101501d10751001c00c0e10794605901a240401c05842450030301e080940400021300540150028 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 45205139 1250 45203889 45203909
    0x603040809040b03030a171f0618081f020a0903080f121302031f060e010e04140606100c080705030307020604020306220303020d0b040606050d0c0503011818050a20010c020307 77
    0x4101201fa040c0303440d040482003420325078521aa09c45014000a00502c0380c28200b681d0b040c800a004000407480300e01801440314091311621541c07684000075032120f02180107010f103400020011880c840302a11420146001d0340f0f5882c01501c0458600031801026080c9010b4540704410040e140860900800c0c40d10b000391115028034a09020042d00302e0360044400c8280da00000034140d10005501d0740114007840c50004600c0b444c003da00e0302c1c0c040031600d90343c0251001c0d8440c0f2550707204014100e40c2034001c040482c2042c00c1507071501d0541c0d00aa86c29401a1312400c1804150b25040c0000e43d0491181c4030061050401c1039400d02d90301c002181c001c0d01345a8089001d070621743d00c5405ca8075565800400800165843d0b0401900a401c10950508800d190a803140d1074540030f801121306032409503401d407000c011500e902c40c0c040c01031041440d04114010107a400082c8040007095015031040d40400146102010780d45941071226403c0d0b81000003041c072403000750310082600c030281c1d404495 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 45206389 1250 45205139 45205141
    0x20309100c0c05030a0309020f1806010f1218060b060c0604020409020a051f080a060e010302100507020307090915020403020603040b040201200a060624050a09050603040809040b03030a17 82
    0x2800e5420341403000b805805030000040c424a40c81d03141e0701c01c040e414401c66041d445c8a00c6003040c0030042d06022120b981d07150040c00812515030161040315022606840c299640b1902440c00c502035507907a45801108030100c040e09020062603008074481000c0a894650509000d0200d0607a903a5018001034001c6641c0e201d2042503407100f1030810040c02020305100459004040c04e22200c000800002e800541c88402192036001c050081008840507844d48544507408c6800300140c07002402050710501604108450040c1c605200040c002c01411100003481d10312410b01d0340701d00c07641e2007181182c244100428001a41c43e01c042d6070300700c0d0300808a511203945520040c2c41000040c030805000d07000d80140c8944d052800640d10712124424802880980d076034403c041821848800701740c00e4180c1c4002a15002407084000d001c04c0c83d11451700c1809580d480b0b000c00c0f9240d1003914191b8000d17400050303489403818a4003602c604e55105500841c0f0b0800d0b01400104104281c508521030a12854 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 45207639 1250 45206389 45206411
    0x60503040807060c0c0203100606020a02060d06031e0302010609230915091f0b03070b030a0b10110c0a05010e130209040507020601080601060f02030703050904091406090c0402030910 80
    0x58452543d0b1201007001110072428014104000145080344280f0520320112301801a81c006d0008a03a20f0f0380090a092080d6400c004c03158000080c1040d04540c0c1d0900000405c03a410b2103a82c007000080e0f144030b21800340d070a00a0940e03200d50080041c036400c1003016890315100c00680300100018030f6104250b078549400305414000c4108240d6004080301c018031041d0140030809131341d00b084400c80b0641c04c41c80c1d071090000740c5010707000c40b81d4107412a1004025042c00322008550095040c000001c40c0c2801d07078009003000300d1542000c00080c21200204801400c00c1081d1100500202e400b0f0443c545007800013031003604100e40440c000c1d80c0b10803e001410300b03d030b010340702441c0d402003083c80b180c03170941402541c98500744640c0010784610000011280d02424403c800d245440c2d0282d40742c0200740d20103440a90103200c0250704590380700590008100c140304201c800d26480f2020341409c0c10001c100f40d280210841050384514070410a0284040c40085c11000d01929044007096106003c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 45208889 1250 45207639 45207653
    0x602061e06030f060c0406091e140a03050d0f0801140906010509030c0901030b06030705120c04020702150d09110102071805071404080105010504050114060d1116080405040c021606050304 82
    0x40d402603c0c501c102414403031780c1c03e2040c0241064603c00e9598082309a501c1214001d5814014801d00040304003400134441c1e0220b10222106500340540100203055403656454a48202c1101c00c02c0000d010410b000340d00c50340030180500601c6805612020b02c0c04110000300d40c40703006030542d8140030740003d00c0141510103021391200c68100a0032a0308a69584c01e00d00e400c031004443c0039209005402c030108540c80e2007000c0750342079205200100b0300d4031004800d100080d03000c0801642e014900c00c0d02c09400810340001800703460100340e804113407004149440a4807a0084c1e451314150b4010fa1014005a58080388070415190fa06101107096202c4040c15240d03588c21080d112803410f80003402041c10401500101e0495405440c1048175a0782d420f200e00c0c40000303507106681c0c044801c100040d45002d258100d9011301c060b0b50729061a0076118105850a2054850202d5000801103030802c800d107028402d02c00810384a00290503c0c0407401c900c0070b050703061401608181700300800800e06200c18 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 45210139 1250 45208889 45208903
    0xa060b040806060f0105160b0604090c060519021b04020f0d0501030804080d02010b33030a09140604030915020708030a110c01031413080c030d0c08010602061e0603 72
    0x1400511580e9107071126840da84410003202c03a50300582010340c503950254802c00480f600807e401d10300b606034071002d135502580440b02901c1c642e4030545811a070000b05400310f41c820000d00c815143d6a0341c0c1c43e60a001500d280340300c650030f40c0c00c2d5080132902102041d8082c0301ca1003032107401c6500503501c240600e2080d10500a03041480031461034180040700b0082d01c28002d205407607003101150041c0c0c9203001c0c101d00340c1c0c841d450f107a03070040141548820f80420031a180c10b80d15281c1034507080071900880c46521613801c11100d421100b43c41750750300001e20032a60070010080e111341025014510f020348025001400c503220b0f00c1001200003030078100040c42400508040e10190040e42c7c2e548003600001010f498100f10710080c14098226210740030f40c001e1092150403200c070035850200b90340b0b07401d2070100b400c6001d10a0303075104420042104035020520080407014903100c00000c56861030000280071640503005036045d54400018802e031103010305840496000b428941c1041a81c448000c203041682d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 45211389 1250 45210139 45210149
    0x5100c02041b080108120f0901111528060305030f16080a0f0e040b0307030b060303070605040506040506011e0e0415050403030b040c140306040207031b05060105130203010302180a06 80
    0xb850104100309900034900c904843c440b400321a0711b41003241c510f600742c2c400c00e010440d4280003007200c0c440b954011405924a82c2140080ea100e500082c8141c09208a040701c40c01107175107003c40000f1126a1807a420f070080040d0328000c201050940d1303610380d5a44900042d0b0140d20301d005c10604c1d01480c217243c1e10240c0aa11002098895200c0c40d006030100c00070940341ca001c5030401c018215503050901c107001c0d41c3c3e20001e00030700c07103a45951241040d0042c00b804580d0540030030010040072400d0f034019240283c4c4100020400c0741f81c24188107041c000d06070006901300280230b900c03d2442c240942083c054504201503030160381ca5605e00403000e600c02d800c52202c8182070800300710925826501c420b00801b801d442c24056035400a908072160f0840e039056070031001d010b001192450030030f60301520402e44130b0300f41012681c40d04514803580c100c038080d04440c030340d0000c4c0043c007140c20304490b0f41c4040c0c42c20740800c1d4110350560340002ca00c400380fa440500051482d900207501d040090704450024a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 45212639 1250 45211389 45211421
    0x40203031608030a0c1403040b090709060f141008010b0c19060b010f020c010c1104090f2004020708090402280903050c030303100e090102130902090f030705100c0204 73
    0x1c990386411442600700702c4201000a1401720502007440c014110203010700e6910000c9843c582e074659400280b044007030502e04680c800c1d1031000c542c00b031247c40b0f0701002d00b2072482c0e40040540f0706041c660b151f00700410035901131204820294105034110740990b040d035401c5100c60341c4540c0d8500a40346411840000c190700103c03450008014840d050b40811200a420390790003030342e0031100310161307500c5100d00d00d070724001210b400c4684049074202400007000103004001144c4031a982c0c68070380304d10300100380c2510180392020814401c500c421401111545054609600742520780e103030982c00d40500300030039019513000503620b038035911640c284148030300011002e01d10b11001180c0007440d17400a400116210311680050101034a07000060741c2c4500801d09009040038201440f41c18007000c003500300c4509640901542c01c4c10a10214004040e1482c11001071f1078101c0070382000103c01c130586043c0c0c000d8000520034051601d070366180420311610703401c0049400c881e07440420010001507034040c2c012 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 45213889 1250 45212639 45212677
    0x5062202100c05031b0d09080d0509040e071d01080c03070902032701020307110609030a030903120203040803070e0103090210030203060a0306090c05040c0503130f02040e01051609151704020303 85
    0x10080c445e24440001001e904131101c40c186034000352455400ca00030103080b984540403850106200304003d00404070042c1c4082080041c07105070a00c0d10070150481801c00341d070461240803528000340c00ba40100340e8800103060741c04070500420780710240c1c3d0080d54401074000001940404160307109440c441440401155481c4030104098000d4006503140c0c00010700050700c0442e40040054864010403521000e145032140aa2090b001808040000c405200b405a04440740454500c091403241f8001e543d640c1c4c0d42c0c689400c009100c0007070240198181882e02403004007580f1a4000d0040040c980c0c2001a0b9075155980082e0030282c440d400113000c079080c010ba02e010400300b8040102111401d17503061200442096040c0c810740011500144000311894000c40070440107140b112640d400030b403000490044040250b03003502d1f012a04506d4801003058600861a40580008001e0143d003070080240070502900800300056138a505480c40401801b207419561305108540c00c0d510700740d261001d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 45215139 1250 45213889 45213907
    0x170a05090603150301050135010e0a0f020102060708090d0f020708010e010f050c03090a080915030f040302070f15030b0424030b0609040809060a02070305010c0c05062202100c0503 79
    0xc488401c44105004c4d5092100005500c0500c1a22000b01c02c1100820451807940a0741c05201d83d2680d800760030399640304d12888003050010b1113807401280c000d14000441c0022400060300e4003402404000401114900f080162900810b018420032914582020404c503c140128585078554100c0543d5501e450002e604148055102d48806180040b0900c0103503610f180250390760100b114910080d82041040b032000440f03070710050480c0c110090800c1403604215440e60324035001220741d900030105035002d100c1859010400c0400400d00b244200c1c0c3e40a081582d0489a030700a249000306141e10341070074003078566440d0010386680c58850003400c1c2c0690070300c1c040750740c084080c8001c0c2c500082035000305219060100c1e030144a9604002518034140400c01404015404520418114041c106010001510a002d0507241d58010340e01d02c00d60102030306010b820401e01800e00001d000b0692403102000c0b43c01c0c0d21100083d81c0454560034140c1c41c1307400c1980c80892030500102a40000520301003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 45216389 1250 45215139 45215161
    0x503060f01141306020f0c030706080901020d0203130204050a050405030a0f0e0312041802040501090b031807030b0a0c02150609040203070b030a06090c0206060102100f061701020a020d0c170a05090603 88
    0x4441d040d5084035004032a06c01100d4540c00092802078058001a105000309401009955000701100000510b013803043c407400412038000f0340d00000c2d003003100341d9041d007035207810700400d03400c55950034007000241001e5840790b682c0d200d500845c00500900d040804400780c041c00d40c241103102d0107801d0310440b20940804000c1507000f40944251000c42c1301019039110810320964043c0e88043e11400005d030704002c103c0006400080200d55058000d4070b0708500742e8001d01c180e20003076200d40611072007403c0c0007803000143c403906a45101113510002a103c900510b46808036008581900c2d4820181c0700c41c00800d04240c4690080c003240d5800006110700c000d9a07a02180465403004003c201844496204a071150320a4520500580c4418400c855408481d4018080f034191410300007040780e59203403d0340c031030900c2d1551520640d6010030510001d40d018030a03104095200c0c50101003030000c039981c4608044009802200000010070003100013402441112440b0400404090312843c09003125a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 45217639 1250 45216389 45216427
    0x60c0102030a020c060c030903040b090f04230c070807120e060403030810090507020616031508010501032003030409020c07031e050f01020405030c010c0507120f11060304030503060f0114 82
    0x214850040000c45041c0c00d1b5040c0ca0052038500051860113180c0740000116403c4924a2648000e0091084125503541d101d001111215140c080301150326a11501140c000020704445410100300301c6000000e618134203c40040d94000b10004010204c4030301151000034000030aa00711200050120605401c024014401e4a407502400c030721544070000941512016074454025901000200380452440c400d0050404042d00e0000f0702200202082c0e0001d0b94a584051044e0355641e0041c000e00100e4103038081c482078143c4114140111190200340e4900c01c42c8514a990341d808500c0c40d0001030148a0340c4015074212000101d042d001c800c0307400c90300700034080880d503605c104070710070154000c10f0080c5c0e02140c90003400b40410b00001c81c01500c400c4d141580894403809225004112803030307910040c0100700d028032400031482444c3d10704036494600300c0111034400c0805208000000750301004032a03000b0130546000c10b28003e5400141c400134050300c50103030a604042a640c480d54a1142d0314 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 45218889 1250 45217639 45217657
    0x203150a030c2d0509040f080406051e0f09090c090307030c0510170105010507020d06110304021306030c0506090303070b070e030d030b06030406150f062c010c060b060c0102030a02 79
    0x2243d02101080625480c86640741c0703403c030b0308102207007041001d480d050424a078000c1c02840207803040f00d070351394510f03260f41e000360030101c04a10003140303120b00f62000d0164240007003001c0112529258032502c0d44403d5010300400144a028541c0000304d220300c40034155100318002a0881d2443c1d500c0741351040707450002c2d0080e1400340f00401d41008000d0310505400060500c000303503a12040c0d0030040112555803100394160381180c106c81119001804900c070f400b03c20a400001c9945030308051040241da22110f440700c070022401c154060012408a1299900b292000c540c000d0355402d8101c00b01323045008095002d000351101008200b900ea400c50324036081c0c0c41c8100c0651f20740c044140029030440e01d4a050640c0c00c0481400000c000403001c0c0c1c00032480b00d500346021010f4aa0b01d496954441e03034141c00020004040c0500350300d400101d2110111031240c028420003e12a18200007851404195030103000d0035200e520105081e2184000c4440a0740007034001c0d50340e8a030100303600020350b220181c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 45220139 1250 45218889 45218909
    0x604030501111e1314010203070203030316080105030304030c090c0c02100207050f040905070902130509161706010503190219170106020a0302060415110d05041101020303090c040203150a030c 84
    0x41c140e4030701c3c6000486014046500c40c8250b40c50816a8928150441084070b9040d07100800585026a40400242d881640084000f106004618400070918101a40321502030741c000d02041c400070f24070b01042010f41e0443c1070000b400c0700940504448425800b90069004028810031604d0168080b03190015038800352422602d41c42d68806200403101c8004018110360046e100c00c3c000120300381c008000d0100c0c2c074080385800c035881e400040ca032014203680c030303c5044d40d062010303945181c0c0000d0a81d0501084c0380a001d1545008130000e0510300c07004000e0a840000d05001c1c00c004003c0340d0580300c980c0440314400d403599820103809041d900340b018541a11140d20400083c05c2803000038205000740d450b902805558489940305244010b1491700c0c1c1200760340315100900310000d40400703414901032180740450141050300701030074a410002c0d010f9045400400401c80c0034100000c2c4011010015100141d070b80c2d9a8016508086021045031588400300e91800001d11140d800b81d4005d40d002d50301 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 45221389 1250 45220139 45220177
    0x3020115051518040608030f07060c0806100c1505090115090c1704060e01021206040c09030b06060a120905030901020f06010302130504060902150301081608060a0b060403050111 78
    0x41000301c51100340340d80500401c0200f20016608030020b24036505103c000e400032034407686800200c1d0450700300348010150311a01148100501a89018066002c4501e0800c01c2e1182809008518520020301810050110303680c480720421000c0b0400e00114010385000b00f00f00d0825010b070074040c00c41c09c2426105400940008038081c074103840344824034500e81c2c8070351a1400d410800741d4003544008000741c40135960b920100c000307a0403e0000340075200188920307440c180760100c104401c4070420303040101007000d007200a0000910304a54103801c0041142c81903194101100129400c0380e845076104160ba061644040400400001508a0740801d0b025141c914480880841c0d40b02000d10000e5070051b824440b0b41c904803260703800107420038000c040100b05102141c0100d94080300001c0015440c6000100402003210144480811000d036042c071141e1042c60400d0003541e615001d0000181140c1e602072402c0311395910300c21a402560711900a0104014402c019030464100e6500f056507110828 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 45222639 1250 45221389 45221399
    0x307020322080f030c030d09020a0b040807050a080303070207060806030a05011803091a030109020a0519090e0603010204080634020d0201141303030e01020405060403060b040b010c050706030c02070e0403020115 92
    0x2001762150010850b00450800d400600c24201400006400341c3e0030103500c00b004180e0788207840c010805010075200a1401d94940018070060700e030380343c3c4051002d1300103200340000964082402ca084800320700d4003003455180e0100180c100051240010825803815120084a088481d05e0610320381c0030341c41d80180181e0700d401482c21006101042405035404000620501110ba80500107542580c9445030502c40f08201030201d0341d0120b010316012850844c5c0402012600030080c075400030040e0000c0d410a41342c02d0806545080c0a81100600440821002e101070707900f40481e4405000000361001c889a410000703074481020a5000005508100c0000701e01030302c0740c241d68082c18441301e61240c1451991000c80c02030a00400c031001d255001c0000240c03a58409002c1e00103140102c80002e5035116000411045502080708141848490040c12022410120f02c09080311510304020406130082c24040f803c002c800d40140d030803c038044080c03109150741540000c04e40d001e00c0103007074561340c3c8034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 45223889 1250 45222639 45222643
    0x90c020a0f12050f0f03040c0902040f0b0c030d05070c2f040c140c07050405060301090b040206030403050405060d060e06030c0a090b03120408010c0f05090303040b0307020322080f 79
    0x491809014034910401110006000300d14000210b185860110306014600c0c0540d0005c0d0301c030a5961101c200b020090005100c01c14440b00c004090ba010214541403602100000619442c800d8842440d00819a041c000d8001d004a40744495410002c100d549449600640f200e14420000e9804502007903602220040c4040c07100080f0340381d52006a0707021a241c0800c8050040810030204001d02c0c852040c0e012a5014042c0c1100b68015018007686c40c1404282300844400070502d034400c5c1c0c184411381020a1070a9040b640164041da12181c0d20342e224201039880344141e921007600403500003801040740c2440c1c6e001500b5601c0380200c8005541320b440801d0f99480d0100710302507001009510030031019060b640302d00000140a000e4800c9160400e00c1c944464125500082003651900c01c0220301c141e002041000010302c40c2003c6081403103580219a40b80500e02030804441c00c0000801c072a28004c0081e41c48000100c6120040c2c444d51942511a110311840b030918644903c0d04911f100c0180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 45225139 1250 45223889 45223903
    0xc1101020c070306020904090c060237020d03090f030f110d0203060c0310030c03050102030906090d05070f0303060909111014070b041406040503041e060203090103050c0c0313090c02 80
    0x1501c00602d4024250b444800080d440142201d03071259580c402a40000d0400380f00e44003d080c00c2d00a40500b8540602c03220410a030036139407480144290003c103101252010003a15402c0d015104800319148900e410b6501e0300142e04588107a65480300c001007000701c200c9495a10364410300020888a0201060120880c0c012800035410f030081d20029222410041c06141d02115010041c1c0d64503a603511402d80203080c60700196a541d400100704042003108200c030f103410040b0000185030518060b4001412802920401020b0294034114001418829045100a070415035001c003c040d8403450030341d003007054120f041401070030f190aa540320940103104001940b006e1801c0c035464142c0c581d50350190882d000b80304035820003203030700c00400e00f00c802c1000a10440c440ea000307564480c142030100302900d10350341c03007842c44a000a405024140d07010047c3c0b0b582580030b01780030405483e210304005040c013840c2e800700406d01c000b00c0c3c4240c0424019520104481503a6820130113156100d00072a01d9401d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 45226389 1250 45225139 45225157
    0x5090c10020303070c02032802090709050a0b031e090c0405060307051507050a120203040e0609061807030608010f060e10030803010e04050f071502060a05070e120102040e0a0c110102 80
    0x403c1c0000790030303107019280c8120a1072004060b2007550740202e004880c880d000c06420101104510705400850401d800101c2c1c0004180c10318103401ca2603d00080c0c0c540e091800f0b5030f1103100c03010000c00c88501ca005600401d080c0c1041c1f20100610302242d00b903070f5514510060318440c17410310020600c42e08004c240e00040d00c402421040d100804881c0c4070701281c0c04000c00b2a034034407400c1603000100b103120b6900318822510b40d0107941d40d1450103901601c448400791046110302400b4091144503078a642d400f111144044244101d0740c7e84602d0207400400041d4002c01455003861004100c0f0851588554165001c04580109030b0300d668202005a25003400000c001040410042c030a481401c4103c982c0039116204a5510410b44a5064284481903010140042300106c92a040e01c1c0c0501a550388404d01480c100300324a0f105034010561004840740a01582020140100415082d0102c401a004003402c26040781000764bc101c0c018018a030309800094071100d520400c1c1da1040c021598011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 45227639 1250 45226389 45226393
    0x200301150b0316020a120507050d140a08060d0c0305071508010b1b03040b0409051014030a02010e2107050f03070e040b0709080607020a03030e0705091605070c080105090c1002 77
    0x80e40d080b100507405640f0110450661064140b004000350104d122591441c80e260b4407181c5440d41c0349015407810410180840610194610b03003c7c1100c3c40310306448000c070082c500701e101901e4002c00700340d80c07074a4000b01414188814502200384180000c224085a44290031018001d03010001150b0350b0b102801111103a010400a0300d00c07400e090840b107141d06103080d099900d000d07a600d014100c84e5101e0346c02000455100c001b008298520301c103c4c513000b44003400003040402078050000c1e44072582c40c10000e0511400306207482b0a03848040040145241c003030008541041071078669036481c1c291744a89440754144680ca6865410701140410444410503911032564680396134161020340c00510403002c01c02e84403c0007410403410451240500e0b856005042410b1044c20010151140039004c52a10313441810100410b441300080154400380ca200001d01c0e55131090b03002c985511038940f0180005061520100c1e410764190310550050b040102110100400042445043c100d4006244056 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 45228889 1250 45227639 45227641
    0x1305060604050c040e0103060603030306060512060415080a03020604020307050a0501140a0c02040c0503040506070302031003030507050a0b0718060f0504050108070e030105011202130209151303200301150b03 91
    0x80d003055041035810441d0380300c0f16410207031152401594504241d00581d006a101c0c0410014140c140c81008041c1c441131400510f8a000405444010303403000c5d040c240510340c1d440e64030f01c5508030035100e80c0c064140c0310140c42811400d801c000756280c0040c5e40c00d030320074001c0050010351440c110102400f01c54068440c1c1c0f03180e03c0d00c0010103000b0b80140d4065400d002c0c200360000d005a6451040007052003140e11010745904282c201980343c100300030300000c04e241c030400c144000d0350302480746001140d60500d001a502c4c0388a24100381009d14860f001841040141d00340002c05421828540c0d030b40441c40300249900e03607540c500321484148011140007191003013200380540d510070740d00c20740c0c03210050a040c0c3c0a0400315011900b10b400980c002d42c0006240501c490452902041c0203541000b0040c065003400c080d0030004250682100c2014000311000440304600c1011188600046030428140d80030b651030f80c3c00d103804004000c0e981d42d219500e0418000d00c51100c1d20070040503079141c0c550030b40c15 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 45230139 1250 45228889 45228901
    0x9021323010501022515210b03031c110d05060108070203090a12031e0305090c0d0515271509061003020112060f09060501090e07020d030908090d1a130506 68
    0x10b00c103e0440c3e030302a9481d5491020030440041c6c0800c440700c036032594a000705c0c0305401c00ca0070f440c4034503d03031400b0046080004460081e0350020944144440703c04407001c10020500662000300088107040c14480b00102e03040f82d4400140d0b20080c490300007170321610250368624008a0b01c03842205000c540c07112040009000c082c2c00501100302d03043c0b05e07080420003071aa02a00481504112a85000103912041001030500c014803400071074800541d0550040c080684d50143c8540841c030040c4203150780c01c00003490005031b15051280c010b03a4107264101c006154006252a00d065403441c0f10b84d0070000c0c0101d4444d40c4000f41c2244601e00401074805070904640c0112604200c10301ca000b25552152808a0f4598900544000070008150000349292410b400500603081d240d0282450349040400c0215003600455101d000815500d80003035284020718014071280100e86495400c1050f403030103001007001141c00a544158190480a12a40c0b8900f96000034525508000c10070382085001c1f0300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 45231389 1250 45230139 45230173
    0x90c090e040f0f0312021303060b03030403050303010b03070306030f030e0f0a08030a0806060904020c0601050f010203030405071206141603050f0c040509040f020904150c03060b030403050901030902132301050102 93
    0x3e90385102c0e180140c8208810003552007680c02c446010910301209100030001c01030284140464990240d001e107042500c1c0d9150b142c1c880c04140b00b0400147c80000000b108a8403a92000c4003440c0d011501101038046410001c01222591107050300a4212820206003403400d54242001c980e00c0000661510021a4089030084005851300340c00201c140910312a503034460014021002030240103003140d600d0003080004400c1800c560380d042d9001001808080f03880410501e0a413a009a80c40c059801c442c50580000c1550701d408074560b0706840103000c80109400191040c0030345965007400715031141410600c030f121b025a02c811304400104001c100d1410100c002c142d0040c0100b04220b49005a500400c1444031704540071a04c481075955006611070309882080540e40c040d19081006500344102451184006070028050140114011481c1c0e8804c0d000500800d6000d040d5202e168045803807800507280202d101d6001c2d00b100d90350b84402c0316980712140d040f60f40582c001c020075016100d1501d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 45232639 1250 45231389 45231413
    0x5010c0201020a140f10020a1b2105030f15031f020d0207050304060807030c080402010804020627040b06070b0403050f120f0601121803080a0b0307090c090e040f 71
    0x2410b40c0162901c0d040414040151804094042c8028104072000880c4140c01e001030000d004030041d106204c18105030740e014445101d8000241c0b5010100c8280d41444c51f114190b60041c0312095503c100308910a43d03001002c0d6000301290748840b1040d031500c403944902c080e50b4550641d0181c0c00048c0040719002902c1465440c0f0190742e900528000e1441980d4040c0c1e40f10322070a68442e8030000c0d041180715806244075502017050302c3c0402090300c40702001030a001000d04041e04101d01d0001144c01d664413042140d8101e0041a0605600d42451103040889049030701c8041c4114603000c09043d05003050400c503966203600442004042d0b980b5079050360560801c0d03020013000075007486200e000c9000c18040f5401000b0001c07a949440c0390100004082c00802c805040703255040019241d13203840990074181800d07501d4141f100d2a03039641c0c10508001e000e0b0300305503589032103404800602c807005640154540b50300ca950390034281d900c808081e4002001654010480c0303480d0600880400c8042d015a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 45233889 1250 45232639 45232643
    0x30604120c050a05010204050f061303110f031c020601060212030c07030207080303010f05041a030c0d060f06060503010503060108061605090103110f090a08010605060a0302090a03021504060806150405010c 90
    0xa07010166103078850394a8030700107802c100c0749603500003800e02191500c14083c80e40301400725942864407411000740d00306c0e5030403448002c01044141c850441c5079034403101000038658003e0115038105180e140e20a070355500a00800b03001d4050a800403507036910110740014a00107441d034083c80e680341c880a0840c1e5074054030098045005190020601000920045000380104010b103d00141090b0400007155081e10b420031007041c0d02c101142c107035140810103500700c010031200041800030900b41345c0080d02c0341d0500040c0903440c02e60081802500403010790305961042d811901c250781c0301d0341d005a1320076045d24a40304c01152600000882440340e030051055080614020540b5816080b1940280c3c001d01305070b031110300011070070f5a00ca041100c0950010918031000b4800c1c0381c6030901080f89031181001003030070143c001421003490348500b40e070003008690140001451107011808101c50740c00c1070040fa000079692102190103450042d2035840200911108a0310b400d24100065074001782141c02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 45235139 1250 45233889 45233897
    0x3020f03070e090303090c01050406090b0a03090506010f1a070b011e090c08040302011812030b0a030b0c031906050907050d0b03100c02010609050c09040b060409020c0a0c06050903060412 82
    0x2000c55502c801c08016401103c603c00215140c0c10708020107406c00f140c442d40c581c10000280b004101c030310761000710352007100d100e80305840c0d94015942045014203a8208050a54441c0303500004182d15880b0707140f021586000c00c44a0b81c8400c4d1542d400d413031320407407001401c0e0380c41420060124651404005900d000f114900501c01c903941c500303550688240119610219030900100703c141502801107071006544404948450080b83e565178000d0703414664900105070b81c8665022040d1103403440140071f56044450300c41a0714221034080707010780c011220016207569081100c2d030b4a42517400340c501502d40c010000c4003147d940c11012200ca801920801084648030061a04152414030005404901c02c550100c0d0b0032540180103070035122a1340c030015119240c81d0400c1418400101aa085d092b1300321800b045140030b02c0c00048083c0900d410501c100e620000c2e0402c088940054180c441a118801d42401a0303540e02c02503a550041c42c8ca41505078001d000024005000f00000c00035014403410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 45236389 1250 45235139 45235153
    0xd0b06060c0a05100501051201021e03060f030109060c17070c1727010908070f0306020c01020c070905040b0f06030c040b0a0b0a0503010305160302180403021f0209010f02031303020f03 81
    0x56107072901c049413100c0142960b6483c0140100d0034480c1d4170251211020780294034284071082481d9103080c1108202c0d40c0a800400850103035568055540021a0010024404140c082c03d010380107040340340c8140c0104140c10311035421490b40e0491b01c0d1044241c3d4550769021002501c5044960039840b42c040080f4508000c106c01142170700400c400d60381c04225400c044e2081071400134100f220107411040c42c0340e10407117041103e82290311014042d20b500800c05178442e03800c0703416180a4040d00c1d80b024200c1c0115000801c1d020380342d07480a4403903030050244e0010340d140c4420395404a4000c0c0e8920781c040c1c20011102105040c103070030641d081003000d02100742d030640c0d0b68030030705107900301685c0c1da000280000010018400100300c0e2030120301204503c00003407440c5500203952030044400040090600a00040a00d0f00a000c030b90440300d11041e01144405850901c0002075100780780c0540418404200d10085500c0002503a02d42e80b6a80304e0842c105007980c080101c410012401786502d807141030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 45237639 1250 45236389 45236393
    0x204030b041401050a0e120f0d1d100506010801090b030c030706030c0210050606072a120302060703050c0d0e030c0109080304030914090a020c0102090a0308030a0b0d0b06060c0a 78
    0xd010144030780c1c090580621024140d40ca142d0a440c4042c0100464505006032044052000710301030341c50041f8034030b500e0341c1c4180744146e039520b80c00782210704400240b1300079145090020990783c0d84076114502044e10405040c41000c1030403035005071000c50019141e4001844451441d078001e002c42d0000504a03003442c80340700000780c0b800c07840c0e420550010351105000d17101a034040002c0b07106200803d400b84002e150450108030140030b03005000c1c080b42081c0a064512880d00100e100e8261403452901400030385034281c416025201c404102c006214000009014a211348a0340b4082c0d80c0d0f204000e813503d00320404c02c0015180707000f00402140410044031031103040910805604902c15801503890785028100a0814040e661180305199552044102581e44403180c246e171004a082c1c0c01038441034146e4146009005a641150308011112404418441040051442003154070020b000315500d07901485159241514000c15400120002c078480d450124080d0072100c003100110342c4107110f02c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 45238889 1250 45237639 45237653
    0x6060504051003091202010c11070803030f0612060f100e1317040b1206040c08090316140307030207080613150e1524040c0516080f04091a040c21020403 67
    0x3c852045c0c0940c3d50b42c05000a03564000c940c1c41002c030b41d004c0142903038034a4102c071143c032480001c001b00c8030201d40f20001103d076620500392a003d2000c401c00c855036460440e068840078070b0207840c0c2c0c0a4006400100055040381410301c684150001a00e40041c001c85558040c0c00f07145000c2e41390380d10b40d0244004200020bc0d44085c050207950901d404c5c25030304000b01800704030340d42811301c00700701f1140108201c0342d07410000c01c4400289000ba070149400c041070038040315202c6140d2101500c1d010000c0ca0340181903000840c002503a0740002541c0c0c131a114024010440124000018095000e4005002802c00301e0340c00a4202400d0005580841c3d06041c0e04098440e800c803119004c2c0c8901100030381c00c140c0c2401c0207040050b02942c0801001200b0328020303002d40505c0f2502c0c001a03158400302010400c00d1400d803442d0f150b0303402c6120340300d41c0c6581910000c2e00307080c0021401030800da910700d44a46003c0c0100c0c1e00b118a143c035100e4901403130240d01c4a50346408200c0008094007004000005010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 45240139 1250 45238889 45238913
    0x6060a0302180c190905120d05030f0903070204060e10060f0e0904050309031911010306050901050409060917090306090a0b18031303060203061008010f060e0f0d03020601030c090606050405100309 86
    0x6641d541d6411071b03082c0402c0108088000400040e9584451240b0000c3d40d04030040b0703500300c800c1d292100740700d6541101041ca14880d005000b504281461400681644400406400744034401c0a002c82c0c56196902210007521150030840054040d05203018035040000901c0e03006401507090b00e2800c400840800d1130b20341152054104045514171b04414842001a42540741000b481c06101c02071600002a084542c180105840745540310181402c00a903544041c1e6041c2c2e00c10401c1c1d0255a01d51001111a0444281d09000e0701801002411440e03010408540440d8852000480340e240e0381680e14043c4181d00440b8020302c0104060301003608501791020040d84104009a50307450308005000d980904920080c0512100710014460030007101c3c2c04105580c9240740031200000034070b0000f191400c1d021100e98211211700214000d06a01003003d42c141c90107052003c00c0e40381d035101e20a0440d0018440d50000440912041c8064903200303030090700d50300d505c1c0350220f07240115403908011100c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 45241389 1250 45240139 45240187
    0xc02030f030406080114060304020f04180303060503010e0616030903110a060f0e030901140a090302090108100b0612070c020105040305060f0906060a0f09020304080c06040308010806060a0302180c 86
    0xc400b003400c0080350303401030f203184c05040b100c080b4100a0290802151a500018000902c1400541072504054555034444400d41d0200c501d155601102418003400900039402003078025400c2c412a203131605000242c942c040c25945041d5103000ba0400710460040035032420450801ca10340c44080c0b030040c02008483d103401d01410b0005406400842900100c9201c0d2803a603d076038105200c0101180c0c0c000c03001030741d46280d020360355640d000030303080c01c480020190704002e5011844800109200c2c1000500000080c20800d00f0400340341c50300200400ca004600d018050115110001407500348994041c20a50388181041e60070591241c0d626401e0080807103405982c2c0d12840c0c200201c1240810550b40c0040d010f0324800d0030a410900e81d0010511a07014042103e80c0000118040280002c200d898150007101030720803a0601c0d16000b80300b0350b001c3c0300d807219a115030360100703100740360022000c811a9030080400d621100c07610003190510341d00801d51220ba8000b40080450100e0560014403516 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 45242639 1250 45241389 45241393
    0x501020c030a021b010c0203100c0203090303040b0c0106080102090607080c070e0c0919081002091c0b0a1514120a0606140306090307030e090901020d020d0c080a0c050301060f0c02030f 81
    0x215120218092130741d6001034a410003556021440c0540c4020916014030b50300c2401c003055240d41e54009a255114201c004c81d0903200004c8c0004181c1da11001400013802100020701c80e4603942c010707480c00c2c2c0c02000d44869000804015400000748404010f209407041d01050703400040c0c3d1060942e058a004942c2c00383e041400191a403194501084861048900900480202800c0241040d60b4491454040040b2980003c040304255a649000300e05600c2c40e5405500b2a00c542c680010a150181c4105070501c0c03c0138500c0c0300080d40e0030f408100740d51503244105c0c0c20443c20403c02403e840221207101d124019280ca0b500030942038004ca101034014105011005045901810f00e0a14028644803071500107000c1400000c1c1d1007401d04031803241c200c07445405a100c40540500a204540054800c00d01c00201100150000d4003c0c07542244030351030358081595072004250503180d401415900140b0b00b00018010140203800c100c5940c0c11601c0c0c803d40850403940400d1400d07012210008143d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 45243889 1250 45242639 45242653
    0x3030c03010e0f040b16020a0804030c08060108010612020103020a0309060f0203090706020a1a09190b01150c030c02150f030103060f0e0f0703081605060f150406030302030f03040501020c030a02 85
    0x10020001c00541202e0201e920705191300d02901c5070640614054529000c00c0c40303e11400d8419032080103a040c03500c0d08003081c50359482d0382c0d19040c1c180d0b080318400c16030785003d508000681100103124000071a02003130f5101e5010503036a8011070081d40700803003180c113050766800c10f40040350341841840001c20f200c5100503030ba411310701400d600d0100c0710fa2181c411540b00424032400102003081c95a0304100300d031100689a21400000da0030140802c10200c030806500c665007003480f20406030107048070150603142070410006603048840700f00302c240c040c3c081030840c0120b6005003044d0f420030501034008001039082c24402d12011016031b1080c9d2040e540d881d1070b0120006c038103416114048410020100501e42000054a41901d03058103104c0602001004208104c207146003081c56103029a10106650161a00d1000100301c1c0400b903510050703e0348400750744d404070309051003214141d1703815400640c00d19001d00c0105002e42c0c4000c10460740c0303540a100301c8a039508100041c1240780015000f510038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 45245139 1250 45243889 45243899
    0x30522091a04050a110f0904090213020d0c05030408120702010e01090f050c061207050304060b040501080a1203110d0e01110a0c14060c2517090312040f12060b0303030c0301 76
    0x25200080c0940112501d40f0742a170b40a0004807080340c0050301c594160307907110410840002c0040000080107034025848884034031030340b541c560081074802c0504400300580003440b60212941c1c002110014845007042103411414a4200e4107554894113600c004107c2210202000d401c0d101c028a00303e520014a495440c01c12006201140400c101501e03104d0502095929400e40300a000e0b00120a0020000101d030501641c1d802120345003102a00600595030340d16001c1d41d60b9400c412069415528950b10071101e07a1080c02091010030210320f0181c141900716800c48000e100310002c1101540d03030340c0d60500c3c1c40e00c1d111020f401907264644421005007004c0c103003203480c00413404c118005d0b900b00da010008200c1051013500c00c140a104c0c0d840710f0340c1c1985401c000140c100044007800300c040e00c000d04a988038105004000b0700d9810b40942d20201622404031049005500550800b4100c0a005025a60300c4142ea40003180c05000041201c90010000ca806c3d03604c00d841c0311100981c00401800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 45246389 1250 45245139 45245141
    0x9060207051002031912090b0114040506010806120708010903090807080c010203070b061309061e09020f0904020d0803010f0f080303040b0a021305180a05090604030522091a04 77
    0x3000e082d2104561802c601500035283d04c982102c10190070345440c1c5a0418a215400d81e040c008165003040100164130306000340441c4003441840c0508407002c2e6062414100707405454011401030f1141c0e01c10f1344a41c0200100c60003003040c058090b10888400054481c0309001e541c0144e800303134645514131070400d69801c0c2407a540ea085080f83d0f5024189103035460f42e000003100c0d492900640c101c05245c444400150030300411040d00f000a5041c422010240023140c0e0141e002d80403020b24610f94801000c12040c15281c030003202a6100400c42010b00550034161200e43c0e101748010025510124243d45040054100381c00c01d000030903082c0004e11020000c3da03040009801c105005505525241c1e0320000d0b00c040c001c0192000395004100c80c00540012038907640030b040010404503100b8211900841203201c1113074511503a0381414042409e85030702190f024080c64040d81c83e1460043c140050083c0010100c0b0007101d4150f00410014141d0400d10039015405880c030100448803a0800c01c005c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 45247639 1250 45246389 45246403
    0x91302090a0b0f09010b04090c03020417060105010e01090302030a0f02150408010b0f040204031e020a1a0d060506130306020a0203040e13030210060f03030e0f0901030f05071401080601030506040912090602 90
    0x680203000345030040c441b4180342d1040d141103810441000c114419401c02c100c019000356440f092a80e0384852441003409004206181a9402170341c0c1c2c81c2a01d000203004443d1001d591101a405400914021002c0741040b2003048200740007a20305221641c204068802d990301543c00b1110a940d9a42a0703080d9141a142081620034122010350802e4115103810900400701a0410050031010499030219110b82010342d00402010a101c0d0408000d14080e40041d8400389250b070320f082c90003c0128803403902e40706a4891410750f90340e8001c2d035400c582d1801d0096215072080410340c401800000345503201c50140521418506c000904961001d24004c2d141043c0f8030455600141040b100b0b1003a0403407520840100c89e0146888047d04e05c000c404925a4464183c00d40d4000100c10004014000c0b101c01c8602d216118a0444180558407a1403042d6110006e0380e1034005010340003ca4821b6201e50000b680105000f040005c401c02266200400b11940c0c40c0c81a0104550303503404c015446d014441a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 45248889 1250 45247639 45247669
    0x50a0b0a080906071e0c020310020d050a0207080906180306070f020606041a010e060c0d030e071403191a010602010b18060603270703030207170102090f091302090a0b 73
    0x901c0c240c148990b004d41000307440c1241c1417050025104200f100d5108800d101c02d031640140c00c1d40c80c1c00140c0f05101e0046c4d40302482448500c0d080c580403c03601c1103140b08076441c06ea0400841402c00700c101c020440c10740e1102d102d203002c0002e060405511660700f88100382c01850a616800741020004030064204000144000d229910702061610b1982c0c1300c0071940b81040007443c00c111000d01c0e04001814a0180d400040014400d41c6003070200f264041c2c1c00740f02910700d040704842c20655507c5114070108060b0381d82030b8140e00003611103d070300058020100c0001e0b200c2c991840903000c006107a8036000700300743c0c400e400507074494503405240d0508000516811083e801e03201c034507207401800310700365100c060554088003441c65001b00c0c00f0f9801c85070510540e070450080da40e00c20303a80e040c000e6964515001d01040145610064036a44074148211000e41c1e801501c0800b00a20140400c07040c5c400040010326081c008154890040e52044038161240400c1d51000500203016424416108001c2d0344d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 45250139 1250 45248889 45248893
    0xa0905010c020d0204020a050c0102131403060108070b030604020c030c0c1302130b13031205040f0b0408250f12060609090b0c07020a1205030c01290d0606050a0b0a0809 74
    0x404405610380c6440e0318100c0d0b030160380c05070387e803040c01408071b856102d65a007100c110352001c50981d110701440071599040b59074000881103000201020951644c0c0d080c8224420b42c0c0c0030f00f000708001d621141c061035028000920050030003400310149030655100c000000f640f50459443c207942c500c0c007640f03143c414200000c421414801d110061420206d80e900400c1c0300350700040340002c6541d080c0007604000d5980940c0d103140502001c4400f0f0210303009801995462100e0180110306940d1650640d000c48456500402c0c0682c0300d070a04804101e4514500380c0c06403030b0313110b0106410815061040060103807104920fa0380b0b050742010b43c00caa65607001500c1c06820400c800d008a4541d1078550740007900c040c1d20302e556140f00d100050304240303103a1003140002d40b201217400c10300c0800310191020f0b001c040000c1c070400e280940d090070030b00254020b0700080382c0720905010f103500b41180d20806580c4503600c00603030301c0e494000103082000f2a50004290610028480340c515034409a042e40007403a80340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 45251389 1250 45250139 45250157
    0x717010e0106090c05180402070609080d0506040510030f020312131403030306010c02130f060e06030c0301050c04090e011104080106080f030301030f0f1104050405030a030c080603030a210e01020a090501 89
    0x84c018a0381c0300da643e0b801c5c60800b0307442184410b551180d0444260700d070300403c100301c60342c980c2c078002c01550024054a0911413900d4001403040c24140a200d100c3c1e500b80b4401c070340950460740c52003120814070341c05980500c0344510340e0440e25007030b030020040c6018001c1c4005016240c2050310f80798812140103039009030018410300071240d0b040070307032100655412a2400c00107449290030380c00410941f11400745240c14080000b07280200c510304180168401e03003d03201c444030000300381401e85000381c610045c8148204070400c40ea50003a4001d10100c1954400460079043c100c05035070464000f40c1021038540d40d00c803010042d0340b000f00b20110851002e4400755040d989162240900d80c82c0720b29014101060000d52442007011031020f00380780500c014070800550800b2308009980390840703071029011030300d0014400b844038010f4028911400f00100198581000030404039a8000a419100c13403040344415889400c2656004494402d125100010f84074000443c00030401090740c0d004505102c6061 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 45252639 1250 45251389 45251411
    0x1109010f050a1a0417030706090b1806060d0209151509100206011206020706140a0906050601030605030a0213090f06050412080105061b07050a12060e030309070311030717010e010609 80
    0x144c0c3d044418500d042000300803549070050862062440040855141c401e408080155140307005002e00d074001e02e021388000b003242c0c4035692a1070545420b42c1c0f01114540c03a5006103011154154030500594014200045082c045003954514403008144940040346e5071040382402c101142190000744014210355160585288848041c11f2016001ca070300003804030240700f03c0c0d070000400010110403100580c5800c0725034030000c0803004000c8400070709040104076650310030f01a07201640c0005020f02600d03445035080100c29260703c1c2442000b03540302c01c0801c0102d02d408901186990207511301158524003031500786c118968405825003840319540042c02691203075015910b00d4240b803180c045140d420400d801d8648000c69110075400840200b012600184511400c414288208800d100c100c094003249522800200c81044095000d03480803c007140301d88844540c20a07003c1c06885425817112405942500003e0105805a455a0070725558403401d1107031000401414104005a00441e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 45253889 1250 45252639 45252689
    0xb06070c030b090a0c0603020d0e0f0d030518030a0503070e0117010902031b0406090e0105040203040803062b080903060f06090712180506091212060d1109010f050a 72
    0x141c080074096192070000a0402902007100726040b03500822101c880584d500300041c00b07940308800704060f15040076468040c00710f000441081d4846213002a002000d403a510450040c20014080781c2c0920044130814940d0304240028940280183d0f541580c91031301c00005845074844044450400c40800c0024036982090103290741901d000b100056a20f4591003440c25404d07c01ea08180c160b00d0000800183d13242d08a8414003c5903662409014560303a0f0340204070480c00105c901408522041001410742c0c03610051801c605902e0456621034074406900d803110364812130b48100c511060000c2d2000681c902009019444044401d820041c3e24201c0081001c0400c003903c0002807005800c0c51380c2c07403580150042648020040c2d400c141c11125402c2a9594007400e50f180300c03042c01401c5290044031140b4088516125410700c1c0f443c00d540328001070181e460030406040e01c001070307560324540040e51a004110700030903001c0d0184d03540d1400e1200300071503101c20707078045248201c0030480e8081c0c00301e803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 45255139 1250 45253889 45253913
    0x81e010308030406021207020705030106091a01030b0a0f270c020d050c0f060a0204090c050a090608150603040b04060f140103020f1519030605060a020303040f03050d1103010305010b0607 82
    0x8049546078076903c0b1460322070041e000340000c0407452070001c810030805540c0003458804a80301140240400c6030b48880400072203441124030f03400ca42061851051550280d0040d0b19901405066022015521080034111410036040003400f85003842d410341c0c076443d4100010403407900c40c180800041f0708041c1301079900d04000c1c055a051000100e40032100300024400000080680029101c8520349003c0c80b90082d403003409807040051402d10120320551081c005c0d294908842d854440070340f4186242521244801010b1389140030007100300c0502502c034040510702071441403e11036940d0605281c00400d42d07501007114081c483c501103110f0803012848a51604403601980d141803012006408105070013404010100398500010b1181c4070301e041040302e00301c4902030b950200002610703202080110b03c02c616401c40140c0c001d002180100d02104000c800700ba1103414a50f2503c00c1486e03956040d1036284600d0140011702000410a0003000e00408000d0300c4220740c0c1c02c0c6040d1182d6500c03418040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 45256389 1250 45255139 45255143
    0x50c0706050a1d190b0702130e0303010e0a02090a03030c0606151b02031e0706030b0108040c060339021207080304030c030203070203030d050601020c0a1a13030204050406020703081e0103 82
    0x20a0482480580302d035400c0310f000c4148062541c0c425905c40030042e0030b690115070103d015901c14001d044001500f40b00c2d410b070043c1c0b004042c40c1b8591800c18210284000039048000c05682085840c5a650f51683c10400031417082d02c401510b4681c0741014400c4451552148101071584d44d03070404229401000d00310b00340804c58110b40642142c0c000f00e4500000d403c000203002d030b005850303040c40d01c0b400900c110803201c26079401e10101c0c51b500011a403034503059030020044004000c003806602e009070041500c0c03480e203c0003000050031b04020004801d6405801032400c51940043d4541c01c2e90501410b038415001034040c602e4401e09039194441c600c0010006020004642d000108141c800d10460380900c0d00207007203c3c0c0351000180e200700140f1066401a000d84108489100242808040c034030443d00d4848070650796200c140a1844213601036014450001d0441d200400180c0d181d216040c06140101d200585440e028503010703210b4400a070404c1034103042201c013501c040700e00314802410340f5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 45257639 1250 45256389 45256427
    0x50a050118020f1606020c0d020307030503040f02031603062c0304060f02160806011401020a051011040e090303010801180503160242070507170f060106050c0706050a 73
    0x10720b0f4001844410700904a50003102040500008103005840e0094030840d90b2800585610829110090b0b0f81e03841103410050100c0c0d0244000b401103440d01841e12086800030303080d83d02d004800d0130740001071049a0403c03510707103955000e000d10012408030b006008091343d00d5012400d12403000020f41c2c038000d070320072070b41001800c4c1542c82c035840c820b0100c0c1042c40d01d60300800f480291a80c0880741c07244801d0090381c0143c4a4890020741d25031000030840d054540010281081c1100c04214101404040755a101c1c0007c00b0000001e0754401080401d21552243c000341d030b00ea504161600d400e40700700c801e02c841800d60525007140820070110481e200e0711190107026800c0b0a0754400300398001c0c0d0324190410340000700e1038480725031034a600007202505442800d07000ca85850003800b04071802244405041588220b8040c80300005200c0b8519030a60a88110762002a8400e1b65a143c00340903080b4600050011a114544200400684000c0d140783d00b8447d081101c50b05004001007500c0c034540d2a10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 45258889 1250 45257639 45257647
    0xe010e100507021c021f0209090f040302010b1003090b0106080402060a030b0324060f060301080a0807110904030207061707120b150a05070c050603040f020607030201150e010603050a05011802 84
    0x207039008002000401a60413a0426a04100f4401070744070031041a000440b14403c0c200f80010070058802c07142a103000402207407407a2980c26450b180c0141c002c10803003d641d6500c03074030307046a40c84043c1c0010491207580c000c1003400390b40c50b10303043e82d0506902840920400209100040e628602500c400b84034601c0c000842080500010349803058540c01d0110490100e416415840380902c0700c0d0b13100700d00030341c2d2103902ca649060500c070252009224042036600300b005c1d004005031021000301605030051030001e02540305100010a29101904d08a0140e4440300c402c000647d000fa502031b004400d5804035024510b401e2601074451407542445480c032903a9254032074019610300048882000e10301d0040f944550180720003429903405524152140c444e603410004541ca000c20407a44a964480c07540344100704181d00b809000d4101e21011000e55403900988440101e00810580c018200458200515458504041c0171118040d0401420904040050084040d44034210615040c100320050359 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 45260139 1250 45258889 45258901
    0x70803040507050a0b07050c010e0102071202010c06050a0207020109081c0309030512010305030d0608010b032d060a05040201030c020f1b040f0e01090c060f0801052101020d0e010e010e1005 83
    0x340550b503041240c4c04061543d001c0703442c0032004083c0001c540f103038040301c15000b2118015500d00301c5d84054280183d1201400740214085010303070005891040c101101c01000c03940e581003c0d40c1003100c0c0c0902082c0d000c22a0000d560b402840f110040c1a020003504a00402512100c144040034155100307040e15052694101441003040302e6441000c48220321031943c43e46003907a100e50107880030552140c24010042814501031281800c0303468010000c0c00da40084500100f56051403a41690035844003290000b00c0c0c001c1485500d104903001c00000640389400c0c8005000c4034400b02c280f4003154025031001a9000000800d210b40c40181d0843d201c0c22260100094044c000b501e40d80c6142c1400c01c4000c00c260384054200d42c40300d62017040e00740c0034151070745411035804518204103030010b14200010842424180c0710ba12513400c45a410b44d400f00f401d0404a402d83c1d1010341c41c1b0400c165608030092517280300384034900e8140c1c40351000340020010348040555070581c80074070703020702a900c001280c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 45261389 1250 45260139 45260143
    0xf0803070e04020703020f060c1315091203050306090703020906030601030b0f0d06050f1e0703050c070f0b04021e010509040203090304030506042609010503010b130305060a0e0f0f030708030405 85
    0x50407690091080d55507040318580251540c0304540e16030060310507080402e05032800c60060f12002d005803510051581d18120141c0c01c013103100310816007400640381012806241d602d003010072080c040d40300d02d40c0d241004070501c130190354014001820144140082103240d5155004c6a800800074078000c0307a081422400210780c00403086203240c0c400c0001103401c0401c5503d410070380c410040c2d414100d84942c3ca040c15202e804420000f00d100340c0b0500000500250b000342d01050b0480c0509138568100700e420b42e160360701c000c110070f01941d214564908201c1140340030210303500310380454040c0701400f080f25800a403071405071081441c451900440040d400308001c10035240210b8014040703071900d040508250424611a0082c1c17070301440140300c82c4040c00c18050480e850030006a41c3e5900d181e01c0c2c45104400c0d500300003406259500912400008128100001406501340c041d0020f420700c45032114911341803071418943c8158205121071100040040240c4104079002580d00d80d5a51303592420f14 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 45262639 1250 45261389 45261407
    0x20d032a031d01060e01080f0a03180e250311030106030c11030712120504050d050d1b0801050f0306060d020d140a1104141003140c0d060f180f080307 66
    0xd80b0007030042158041d03920541000e411105804144001c03a42c0740c0f03c0c155102e01100d40443c006500440030980000e105141c80e020034101d590308240c003c0d8030ba500d0351000140540f05120f124004145058200e1781154510100c43e51905080002e4084196010054081445040e0526664171040c454440c0126001c20503280c0c08001e0325501d00311880e058045140e844102d100103650079402c0e0109102c18420b9074051500f00004003001c82049404507400d074014031081d0103c60316440e00e4400d81242281440001000340c2f1601441c0d0705090900c0310000b01040103501c241c4c09001400029103075950305890711364041e1000b103030300585030400500d58031074544404591302c00c07000500c090000130004d0071301a000441c0c081c0003603082d42c04c40601240c0709039000303101101c0501c800c0001440a41520214031150000da881d11145840001c0304e814a0703030300585166423103c0700000c6002c09482501b0440e010350040790380303181c000c0c3c585580340f040000c0e00030103000001000c1111680107584503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 45263889 1250 45262639 45262661
    0x3030506040209130c09060c1a0711060403020606030c0105040b0f0d24050406050f062b0c050c0618120c03070c0b09040b010207060c0305090406080303010e07020d032a03 75
    0x4413a0368424503140c0d001010349036600c20000768204804038405101d00320002c0c01c02e0704aa13551783c5450385080c0707204500300054000824804040d01481220800340007241c4290b009401032b0030b540c80c2c84401e15003400746190010381009030402050040151407002c1e02d100e14bc410f04038686403031001002100500c1c01c19103101c05942404520300e100d004c883c21020130f544055030305209041d910014411405008107090303074400001d04c01d2030350b28414015407062050414130b907140864000c4044508075141000588002440064146502c0b20f003000302613007208070002c81c41c0354032a0031f1041d5900c802d083c1c20f490301c40103000203034a0717152103080055504c000e40098801024076903a05ca220910360020141c5805641800740d0b10040e507001042030784c215112916070020320010360354211081e44c40300340e07065401176542c40c000c81c040c142000590301810700301551004a01300000041d10744401c2550050130541001844020b0901c592074040c4201d2313134100f042c0c48107014400250050020307480c036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 45265139 1250 45263889 45263899
    0x50906010f1d0a1701060803090a03030e131e050f01030b040803041a0117010b01020706020c060c0312130219062f01052701090c1208040905090a0209060105090a0303030506040209 79
    0x100d4084c100303086561070f42c031160000308a11981c80080546038000c8980f410b40c492003044040002ca40075082d040c980300d100810070070030044410200011582d0b0307410b80390700c0d407140c00b040216842602d101d56a00600f80303850498903580f641c5c3c3d48500d0b981c4002c000811040c404004203040048402018600300c0200107007212960b11400b515000d480181c10985480d802c002000207a940042082d200b910703541c4e4041e00008482405000055006590382a128402009084115013668400ca8025241d0000c4244102682c0c010441d4510a084400904d690205400c21a20ba080044015148440c5c00040d000d02100482c4c4082c2c80e0550312180020b50034481044604016012a580f2780006080c2d884000012407200f80c1c00ca550603a00107090500c2e0340341c14000b402c00c513000c04011502c03a070141403405864004603425a030082e500884940c0c010700c009011881c0048400354080c00a107091418041240006910410680b001605041e42c0701e0100e0700c3d030f85841e01142c0d02c0c0c03200940 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 45266389 1250 45265139 45265159
    0xf01170a060e01050415021305040b03070308030a0603060b0a0b0715090501050907050a090e061b0c030a1701060302160201030e1c05040e090109020102070b0a090e0906040c050906010f1d 82
    0x10340ca43c00f90200711000c03035418082d151402c0304210340340301383c0b2600040140c01c4058107007004207100080240c00a21a81803040001c00800202541c1c0113500c210020300d0045040340c9540382100540c0e0511110502c10055050207010501d44ca905070b800494000100303082a000e0100e03103000412201502402c03e500704020810f035000001079400c2154010382e00c032603030b540d40c98002104403900c0d102c02c0c0d0815041080803d00590f0a000d08107100704a0076802071038880d41e48452851a4040401c500214498101c62010443c208040324010003035410290316000b010100007500b640b00c80002810b05540d80300607a4200b200300085030000c42c2001c3c504551121410b006403450304140f06051010001c00000744900006010350841c155060b0018400507040650240782e50b08800f818400700312240d9000102d104225800341c2c052505035001c0d00329410715080000304110117030013171130084020000380035050b42c1c010b600707a44c03480d440d150104003803000140e4813202c50b082203410f50740240800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 45267639 1250 45266389 45266411
    0x20f0c0105040b0a02090f06030c040e19060603060e0f0411090c0c070f270e01050403031a010201090309150201060b030403021e0f060408160611040911030f01170a06 73
    0x5807040c2d015600404040c60035581e04a028800d0380700340419582c205d90f031512465020306050b0099608504000511070505456180b54030711443c0460702494002042030b106201c24a09100f08400380c0071904d402d1082d03600740070a038400100090000705c40704240ba40090207000d400d202102c1005002005d00c170303041c10902e001d2180d603000071031003480f40c0c01840e400091180c01c3c02003900c12100c45804a880b0940c0280b01024004004900145a162a00401005410300b81306581c856442174600003a154441118032070b0305000700d541c40381968501114240860b4201d82004110f450380d68480e05d0800f500c4408030702505860b401000944030120138003042603000729000060710207044054840407506198180e032101251600c11054001d0300100d0081111600181829050500881c1070080b20fa1f5640c0200c034040e01c40c1c03124111b800325090201c92818015a01ca0038520b807145415401c14a0039a01d01d05010702c59040603042c80d01110b10848010721075048019000381007040307005812 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 45268889 1250 45267639 45267641
    0x609040e010501170601080601050d030513030c06080c09010914031009060506040b06030417160506130b06030a03050f2a0d03060504021606111b010b12010902030607050d020f0c01 79
    0x84c01510910030b042c1c5201c1a1071280002c1842c1220703992401012681d00c0d01c030a2290b48614a101a000c00000708006815a26038101d20341c0210710500482c90100d140c03120040c00704802400742c6080c6a41004000103580e4031001d08400d803912480c0d40c60300c1001003c0068505010500070b81807081c14600075406000340790b4403e500c42c200640e014011051044204007643c8000c9038000d140f96400071402d4000300c0110050011004c2041d1413841c06180d035203615191410032500d41d07000040014891040101e00f1800c250405010f60060041607030f41d540261250181c2000d11062000100f04104244007096501d40125800342c080080b1040e0710340110744400141300d6020100c2d0500390001010305051003164500a12180003014040c0560f4500c8040d000340a410042e800d01805610108040040c081624901d81c000014040c1207000901064a14200010300203924000700710000d604d0201c2c03410b911005502e046940d80755112580002030140701e82007025040c010603d0745a003201 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 45270139 1250 45268889 45268891
    0xe0123031906030209040602070206040e010e0a06080d0504091116050f010e0307110f03010902041505150c1e070807030f03170910020a030e10060f06080c0405010507020609040e0105 80
    0x8045210540003040301d40380070546550f84402034004160f034000a000c2440d039805801282c0c802440c541c81c09544802003aa482301c01c0c3c010501c04c0c0090070501c05180e030306115000042a800000c0d1140414620020b4124080c030310075060300903284c6168480200407001240d8200004000c01ca0300807040742081985d5195008588225610340001798060040002c19a0241940100b246230669440382c00e0104650010020540644d00e43c09484010b82c1d0700e000301c21903910b1075086010350514050400401c01a100081140391004003c81030041001140128040203044034500c040f030607800a4a10300400c035405040c0714082d00c0c401204014543ea0310380b11b001c1c001d9450303811021206c0303a00300c00700e03000b03561402c400e40c01540707110a1801d880d000740c0200c1001d414000307150761142c3c0751541050b240c078500700e1b503482e560f18050024004085106010308414030700440207140101c4040030321b204901a80b0b052107404a03d4008550b82e2004a51180700098010303c12480c2c0c818a080c06008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 45271389 1250 45270139 45270151
    0x5090303010617160e01050d1109040f020403050a0f0f0803010305060f0c03060f1207030b01090c020f031305040b0f130c02120f030a050a060f06050a020c010801080a030e012303 78
    0x280e0603505a0f030140394140d80d5014400c4040024021842d110303080da80c007150b401069051090520841d1800e40c418460030010301e4102c00002c1c0e580512034200412581260300066a0a1040c4010b201207500041d5107000740b680068042d60f120413500b000e800745403002400500c99240040080204140816000c3c040c250424030313182e050301c4103c4400c0d511b00040358a2074005011842a420070318204401441400141042e40c07240f507241d03180e900c15090f090304801c41c6182c5440141501c140d041110138144a03000b00070f1400c00404d202022074a12180c428140320f103440300403458856a0340700103c0760300c81b4010142c0c030041030f000780e226014103980303042c0034054000d00b003a1300d0000e1022011241c0046c440300f00c41d8a0340c0e50b03c0c66010010709001c0c0000030660303a911070201c2d0403107906207500c02070441515403031b44800304400c00924200c88401c1d03560412003c20300400c03401c3c0f4000b0322182c000340d03d424003801562600004a030407000f16113062460390401500c030701d1002c0c061001540150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 45272639 1250 45271389 45271397
    0xf061204060c0906031e0c051306020313050108010513090204020f070605071805060d020d0605030111071e08121e0106030603151103010b0d060e01030305120604060308090f0a09050903030106 84
    0x71356480b8240c04441172040c1d4811402e142443d02643c101069108408110380703410102d0070007446a90700001550a900400056031000403004141c021004141000f01824a0301c3e07185907052902240f01003020003020500a1303241c0024008558031601600d11200100202c0b035240c20450034804084c1000345c03010804598640040c0d00c25120743d50003082640d03000342c9200c0c035001e9600c0d1450300960080c41c605040560b59880840c0941c6c0a0050709003925481c18141c0e01c80c48542421040007004441410324160032400c02800640c10f60281c030340482c4c0306042c888080c0d8a801e0900d044080c035802400d041421745002098281d056403004d000e4a00440c2c0c20b1361541440400c80084801c0103528452041051004202c4692250024407a00b40c6808000c030302265909400d24080c102a0003c8010840209240610401d66005a079110344126002d0051914640b1071045500c528070030b00340180001c4c2c01010032a203482040d40010125814204040d2904200e031030344a41081c003441d0001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 45273889 1250 45272639 45272657
    0x804031a0103020603130507050303070b010608010b030103021c0206091801060207060201020304020306010e090f0d020d1202070c060e0f030f0f0f030a0207140406030b0906040204060603090f020f061204060c 91
    0x103421142003641030340d501400c25480c5031124002d4008070032a8040c22216031080c1900170405843c1403020b0201c492042180200301d505014000e4201e40050704030440750368080c001040587d8900f40d460151040081c0003492140480c0081000c070b11942041c15080b1056241e04030700a00d40b50480c80c1280c5507a030035078200d9511900b04034246d101c1560f020b54107030b01040041c03001d404440a26500060000e048409080e12000c0c0207040c072a000f10810051380140c2109003459400c500c0340c5a0003540c90108500d0114907555042803520716000310803c0000000400709543c88142c00d00308a010020101c0c0c140315040244e20b65a0308007050b40e0710031400b030b1341100d0b40c006a0010994280c1034007070300580001414000201c3c1d1106444800c9035025488560000c0414449e80500c0c1c01b80803901c001e0862441c203030051000307132034044e8410401c0520700113008010a000000c2064103aa044075481c00b10090a40050700c036009038144c02104001500078801084555809000d02185984900c044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 45275139 1250 45273889 45273923
    0x60304060615120b03160b0901030207120509090708060d0b0c0f041205010c0903020612270d08180d08040c0803120703060f0b12060d050f030c0106090510060f0201090609080403 78
    0x6900303146d1100308982824502c244645988a00a0012002c3c107140c01814800036440e000c0c920b0f10396106042c040b582c0018074401078200808071a900101c1401c000308503007400b4000c10001c1504441c090006001580454040e58224048410700554043c0154641c0d4a810f6102e0061b04030f684101c3c0ca545c60a1104040980a1164a0200ca4006003c1410042000c4000003244001440351445117110a13102d80d105440144002c103607156000200440c0360b0244001d490340344080c0c605074030f92981c07481d500c00c144e10024001c801081949098606900c546c50811510300301e98000354110b00010501040e442c61100301e2a215141d6a5418000c0f90f5031b40c04070b500f0f43c0d40750380114841418100211203540211034411a040741e40a050f80b0801950b64580350b013401a090881c500c00d401c00943ca1096000034020000030f400d580c1010401404c020005011142e03a502c03d460074000d02000040016000313506c014851500620184400d80007464041d420b0350150008907044071640f618126 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 45276389 1250 45275139 45275143
    0x20c030604021c0c0515070201020613110d020303090301020c010c0912030206040b150306040b0601030e0105010e0f040c03050313300201030515040f0b120a030e060304060615120b03 80
    0x100440e000740c0b08822161509207540d4070303100f00c09029070380440c210400007090380362440c101c9000b001c2e0840389926181140b000a00303000340600b65042c1d40c0c01c3c0d1804e250200703421410103440f81d2070850303107607030304191510109007580660084560702d54404032f620400d1103410f40044d64402c0260b5201c807541c42d181c2050515541c00600e000e001a485030000074009940600d007240c005403216005401c517180c20000070326040f0115411a6203001c40b501380300c0b007035802d4001ca03d08690203034024811036045c4560051350510080c0f103845c101100e03001050602035205c900d10042c640000035030381d99030350450300c03281c0c10586841100ea0b28410508009911045801b00102c807d608401c4e10303c0c070804070b030011005045c028084003420004408400000d0b5194030602c40d03407900c07460010401e99064000c104090001158014040d000039558000081e8010040c0d11160811140c41da26500c0b00d0030a03100814017500108401c3c2000100000903d8106050824099407580207200c25008041416 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 45277639 1250 45276389 45276391
    0xa0b0a030302062202030a030f02060604270f0506100501080a0501030b070c050705060a0224070206010303030c0c0209090f0d0914060c0a0b01121b05060d0c18060f020c0306 76
    0x20380140c00c10343c00708040f030028881d5410014104140000d000c541900081c5c18500c800a040300494007604980d03102c1501402003940c0300320216020000404e00380135000000c503100040130950a4080340303e00401c200e10f211001a03580120171250750345445510885104581e00070540481d0444c00010290103946c09454166076000b449a010b0707881e080802d48241d4420f040441c2c4a020380d040c089807646400300500940c9100e81d0003000c40d03102080085481002c079000035500320500104015180d9000944c080c1165814940001c07190603441d4211207864160030000d40c1300241d0303803d0280d001000500c146090150600341d582a0050240640e103000c2c4900c1030b51041703881c3e2981d014280c50300d43c003d1f00803c003100d0185c1c6d9204003d0b0b40d0b503c06441090b04400440e040b41009203050241c80c1021030754400000c4101009103081038001010382c016608040032581d26881006000c5101d040034401105002c1607100d40c0b9525840e028040140b04c48010005215241141d859403070700054107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 45278889 1250 45277639 45277643
    0x3080403050f031620100f12020a0e06030703060810020a08090705010801050d05100609051e0c090909010e0604030f030c0305010e0105061312082104020a0b0d0b060c03030a0b0a03 79
    0x5000320340c0c00d0382c3d2140c82030b2540071445d00c030000e16080303a00d009881b540424070065010307990340e10050001c601e010748290785002655000901c188103040d8010f030052080c1090800c00ca0341c581d101d9460300c80440c007512094012506a01a11130640300c1201c25801030718502e0b102e41c41e80001c030358500c2c0140d503480c0c07400c0c80756900207044140104003904102c101d81d811a40684191462280f000c1103680543c2c18603888000116500d40410003440c400c000c481079840d5000d12400003608116000682d01d0240d0301c0402d00c00c049000201e40d0000d002d501003030a03443c1d5601501e220f1702d01030802034a202400e89024011a0600551120003071280c4203590595091550110300c40c0d0803c8140a4182c20603222480c110000f400c0c0400c125600c40c890010892058a0240d511401e06038941a0000800501c2580024000920006070344486200c0156050102d032180c0f140b10500d10358014101c0c011000d5003002001440851403c1e01000440c4160403070407003800803101d4031050001001c103500c40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 45280139 1250 45278889 45278917
    0xe01081303030b040e06090a050d020a030203030a0507120504030305150301181203141602120c1c12020a050d0e0c060a050901140a0201020304030908010c05040e060604030c03080403050f03 83
    0x1820009000f644003006540000d44000f8180e40c0000801d880c2034801c1d42c0a007020340c044003a03d4208541080b01a280c1c0969101504000d005560060340e02d02000d0000e0749002e0307c680c00103600c0d610038070403642c07940852042404241003034103015004020680c0c540220500c0302c9000450317404d0500489500c0100d840d20064500c600d5250326600c03d40c440214800c068884400c21603010303070301d02d030603015203007503000d1651440d5100e401a140c000c0d0070f0120349000805100d00c3c00d01240c0840c00d195001003001d030950908200d548201c030300d00c03855407060b1245480410545121948080078100d1446105000c00c14200801c2d0410382d200004149554044410041c0020f00b500c2000174012801c810704100e4041c0c403422aa048154008400c03020040c0e5000c4104018168000d501800030f000301c1e0002c2294001641c4010100d1066019844003885100040b548036154941110019500100d090000c60b40740e1600035190340c401c1c130050300d00d40303c0c0c0c1d02c03144250b22003c070807136002e0070a041d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 45281389 1250 45280139 45280171
    0x50105070605040c0305030309030c2b050a0908060c0702030f030702030c01050f09030102030c070b18030d110d050108031903230705190f020f060c0a1808100204060e0108 75
    0x7807580003400004104507a5200307003030700c00800108100061406604004080c58a0788a0441c0c01ca19010710144a406000003403142580720100071400024250220b2501680d210b00d201825141d41c541c9a00c00c00c030510a8004010000d601c44001c0d01c0110f108805407030300c00d4090324205580e0f00490002a515410482113003a0560240c001405d8040e02c0c458924280580b0500007030072600202c94038900403100081d4042000190000c02d54844900300d01120b01f1540034062540e40c0c051407510030046541c850300562040c0311070040da4030382c0300c1d050414491981c40754800c0f5180d0704040e103d00f41550012034001a1140640100c42c483c1001520380d0020702d04400c5100c1c480300c0b002d4488003c0c0003080001a90049050b4039080049990752603038803110300550402441c0000b400c00e804010b0300302d8000c6c8801074605e44222580e8022502e4284003116415501a80a81141d800305401d0b108040103440459056000b03481114240c0d210003500f600d00c4001540c030110211100e0700d090100c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 45282639 1250 45281389 45281393
    0x9120306120105101d090703060e07050901080705100504060c1b03200910050112020307020f06010303020a050705060403020d060507090b0c0c031b0108040f1505010312030b010905010507 82
    0x195034820002410a4600e031004607800c1d00b100c50960392200c441c940644c080c40500051050824a41501d144c40c0030145030012080751500703803501004050540354201140d80007420007464000d440000c0c1060701c5540d47d22441a0f84101e01c1c40741c0c50040c4222041322994900860980d001c8880c941c40d407400454007540c076114031001c40c0c0d4100a00c0141c1003404804500103002c45121100720021102e2080c0c0c070801044000740f00207046d01d101d00420b030b1040c0b11a91380140410000000c01c400907840b0b4990b610207904203640104100c0883c4141800003040c15070000f0022405c0d0301540039540c2868841090103024030a5000103500701101c00e418000040d501d60145034043e0310742c588040c1d41078844440316800e90000b51034a1841e400300c2c4803800640750500c202c1c400d503000c4044424148d03101f200017070001c0400500107004003103500466403d00042070100010b1032000e0300104415a183e2030804107450030524404002460011090300d1540260b50354800c0e150141c58450078406030b9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 45283889 1250 45282639 45282673
    0x60522140402030601030f05030d0507030c030e030f0409050a060b071a1f030201050705070803040902040504050109050402010c0b0c0f0a09091b0206220204060605030108191a130203070303020708120309 89
    0x9084200c500e80309c10007a1955200007481224094103559a003c00d02c03480380a4014240c94883c50041200e4208025409510845c40100c81c101d50420b4800710f4a40e403400090001040254440002154006000c03c05c018035401790042996141031040d2a40d1901200403052003c0c2c21400780003103071144401d00140d8003801c054000648541c0c12641000e484001407400e540003944980e046540101d001d01052600d4001c00340540b061020402c00d40c90907030002001c2d49401c06c806000c014242c03002c01c464180304000c8450300502940c1c100d42d91280f80b100140760409500c070303c2d807496103001c882540d00183d54481094000e0558001c01c1c0c580c541e4144800e500450050901e8111440008900103031030314010040200101d456554032985004403203803d0156648c000003031408000c1c115000200250030048009403241801d8005030f8541108942d0b100440d0006985840380101c000704269000402401303403124103094802c02410780c207894800d4041540c0e040f840c0e8210403000004042c20b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 45285139 1250 45283889 45283913
    0xf03080c010b12060907090b0307051903120503010f06020a02180a062705070906050d0903030902120604111507060b0307050621160c02040b0406052214040203060103 73
    0x80c40000500002610010b100051030b241142d01d141c02800030055195418088880207101c000070601034541c81800013515050240a602d02c18982604900f00039000b41c1c03880005144d10007801c003144465150b0140c15500244a12000900d0b44000030580d141301141c88801c5c158090080c180004801103100341c00e0070000c00404410355100c50001e0081d6240442702e103c00c03609140d07030340a0035080c155a020740f8402400300c814070880031400c0204542c0601101c10b29403500200040b10182441c0032000741c80544406507100c1c11a19802442c21004100c0a004910a00c0c1c4510310458820074400d1030560001d400741994814880540450303107941004035004001026a481c0d240c80d040055180e07041000070440521408846111a102101c03449030414024200a404034554a000410700d40000400030700030781e25412920074980b42c0c1d80086010305402000d4110004458007840b03c07055a5050041d0302c1d504000b03035428a91503000009018a4002e0007510403a82181c58800d20084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 45286389 1250 45285139 45285157
    0xf060303160b0a0c030c0504030f1104110c01150b070b0604020712020a0302070609050901031407090e030a081005030c21060a0e1006180b0109080307050303100b040f0308 75
    0x104000d003115000c00281c00c0125207110301d801111508040405000703c44552080406040c0342401c0c10900f1600302c13080d60201e903031050301c4281071030140c9002040801568032281d00715040c58991300d50f070b1000f1009070028900b588002c1000d1126050019000c4015100f0225004006c200c8a030108031600c000c00c3e84010003500162030804655201e5507a403140301120001030b007100a950040507414003464ac0141142d2410600b4a800c200025060300010b100003042c03026542c80d40040e2343c00a0200341c0c01032000d0721042003203ca41d034206544035407181b80018001400b0340001001c0f10004964030064600c0940105880c0854405212080c0c40007410b014055090030002c00c21000200f0034144141401070011038501f1500e001c09240c91502aa2100590b080c940301340a080c0d204245040d900481c0071021640d4950300300141c030743c9131243d00804864080010700c0000d02c440080114041e075081490385941c03641c0d803241410b950146028001c0466460402003000c81c03801c801030703c4219 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 45287639 1250 45286389 45286393
    0x301150807090519050d0305030103020a08030c0c010c0f05070906080d0201060810050603070b030109060609050301021815070c03060e060601020708070618050409030903140304060801030803070519030207060b06090105030f0603 100
    0x341d03e031300000310f04001b41c80c000c40000d07a00200520440c00c05030307440001051a20003e500300b00c043c00c1c2054441001040035410001804081410300c62104201d80d20103810500381c0d0f103049d8407600030001a0500b40504051071144107034031182c0500c14800c80045031101c0001e40b0780540c0c00f026481c0900340c007420241c0e051280403008907211000400440c000c0103254800500d00d8504103014140680503803000d071003030b40b050103011201749007036007180b501c11802c0b142030366194600c400c403007118010303800701070080b41c0b81200100400810342d100c03c0201802404a0390303190340b0b450049a40321003600404c0f1494104031070410005004801811812088034a10180107442c8d0020504513010b0b0a42a400034407071038030410500088040b016611201c03040603519103401c1010146c00081c2c180b1000703120410010000c0c1d00c40b0711070b1050300c6081d031204440f000c040115a20085c0a03420cc204240c440518040300c550581c64082c00700d41d000c10341a110242560765440f0320055060300200382a0f00340c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 45288889 1250 45287639 45287689
    0x302040f06051210060b0307050306090613090803040c270f020702040c0201051f140112020708040e070212030f07031d0619050109060305060117010f1103011508070905 74
    0xb43c0c2e03060080c1800a5070540105100381104051a0948601d9486814800000c10502600983c0202140d42c00b030800e8441d5201500c800e4081014884800e00b07480c1014684070007501000500801540128012440380480a849035500b03401c40c1900003032450000c8182018483e4a41250032020078022109401820440342d50003003000c0d02c005285090050f5501e8041000100b0391401d5040b803040e20200241c7d03403505100101c2c000b9040485075905022001002a0040c504d5804031180300340d00c02c0119444558880307504060600984841c409802070281c100b940e6241041520b00c1541c414082ca0101d89440b18107600a042d00d40d1a079003103c603504d8140d15844d40c1044414001c4880128462800b200880c0b4034007101c0068019408640c1000410030108500140705410358540c0c035404c04402c42ca4182c000c0c014100f545048145a080c1032600c001d03e40c0c210003440c122035035410740350800711204108841e0301804895100100b00700349002c4c17049060103c09001d1113007680301d0000003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 45290139 1250 45288889 45288899
    0xb09061f03090b10061719090206160503120c070308010e04050f1b03010c0513061b0b01030809010e010203160b19060f08070e0c04050f04020f030702100507180302040f06 75
    0x101c40480701d0000c3c404c0e03030b10700c100081070317102d880c031403c2d001c1201e51003d00d400c214a08203d01c4013140301d80601c1d2501c810240c030070b550314001201c2045a448030000c0c98a40d040c03810f55266001000c420500841400c001110724078510111101d0aa260303840c543c1c0c0da801c00c00e80344070401e0090300990311842401110142940e04005281c844410310401c84601c07224003082601f5290504214801c00606010706107807641114400d4043c0e030700900300000d46010020801c07007403901820016040c1000e0340c00010502c0740440040c0f074210701c20b070b8074000208210401a03940c1c0c0708a0421400c00c070750740300b640800301e10340c000819000800d40c06140140d0883c03139003100070b070744891300800c015400e0503008001403801001004010907801c107480319549042d540d03425860280344a55409803c8812204100e60303203940c12151290601c1028940f28101070130700035501d140004c2d0f195651454480420155070041c2c01d40d11529075113000c0701c03ea660840d402d210240081c44488410325450381c401280d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 45291389 1250 45290139 45290153
    0x30306090c17060f130b030c060a0e03010b0a152a030e120f030d0506010201021612030f020313020607060603020901031a07050901050403030c0312050703020705010b09061f0309 78
    0x40c2100307895640c0003030b0031500d08014030030b09000b0b090144a4642c0c140003108940311122031188441101100050a04005001c6410141d413107980b20340c0300000050140000307400110210020307030141c008118800d9048144000e02c0201d02854800c02c5582105e200d0840c4941c4001c000b2640c00c50703081410004c44d81e03121400d40824002207000c213442c200d0104031401e0220124a0500c0e08800401d50015550200c5850744909d01d40c5418060b00c440c00160164000d404603107100100802c1d079490101c05041405000d01548041ca00280c1008217500121009000380c80c0038421246007021611047d03402c114056202080441c1d626803204d00000240c0d0b5440041c074001e5001d2400c3c1014994010003c00300c0c074100030000390920a06000c5907070581d03403040c241c03815294581070000c3c80d91045d0400b942e4600c0c0c60100202e029007001c0c204101203902d03401030107540e0700c101c00a0044800507000c003d5a10811148a50450042184103440190b450b240c106850a24100029401c0e01c540301c400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 45292639 1250 45291389 45291401
    0x5040507090f080703020f0613170f06040303020a110a08040b07020d0605040321060303080402090a020d0f061a040803120c0f0a050304030806040e0a0303020d0b030f0a020405061903080703030609 86
    0xc0f6a9000043d08000307500f84142910441501240e981d403034441ca21000101880721405160039400d443e071a44c19001d0000c0144d2403181a200044404604c2c1601c0d0003006035000c001d1920010f41c0b91543d5181c020740006030841a541c0c004101e0f03003400d01f840b85051068121010503680528203195a0303001c62860311a50f40034501950720500c80b2100c8070005152501c01860105100c1e191540410100340e1200d038980e00180c4c11a13880800d900c034072070140c1c043d008062980035001e00c1c00000a2002c4019030141044034aa11355107580501001c00f10318082c0034500c506000c941080162507540d40350081c0c0c00d50301c4000248518100b0081d000100400c0d08003d1058000c03c000005001c21f0640080146a2011040b18280701c05a15140e44a0720380080900041c00d142c2c010405511404581c0c0000161010160440c1c00b5042d00b00712503692510b828405a00440c544400301d0010305100707078036007084071001400c00e54091641e80c03412059808030000782d040581c2c0300c0c80480c0094841c0150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 45293889 1250 45292639 45292649
    0x20a0b0901090605220e06041107050c04020d1b020610120c0b070c08070e010306050a06030807030806010504150801170601060206181009030c0c15020c011b1403120108010506010905040507090f 85
    0x805031407e803040c48200ca0002c40500b015aa0512611001410005030641a040c040e00d01585070020003c12030042c2c503420b525280c9240c555056202069800103c09204c0e060300280421000c0d41c480030703110503840002000c0c04400c8406010301094085d0001031080e2841110710171050740d65007031094144006034210403900911000100140811400381d550022440d000c00c000851540d50b610543c0d00c41c03003070300405100d03240000035250380c0182d050300d00420307003001c02c1d5044501e01c4a000b856601e09000b18210088a13091a207a80e0100180f403d0684a198009100c0c588810300c4040c40400c540c04c8002c44d40c4240340050084081c24022600214460389500c0803003881351602d400c41d01055041070081d407101034003c02c038141d03002403c0081400c0078207050540340002100307650000201c0401820508500000720000e480000041040c0c0b003401084403103990b21460213600341c400c03e0382e400e400030310300c51005e00c250b2419601c0305030001031a040c00e00000e9595484160030507800c2d401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 45295139 1250 45293889 45293909
    0x4050c0d0507090b030115090509090114090303040f0b0c041d1e090309010315080102030103030f020607090b030c0a0203090901090b01023304050708061003020a0b090109060522 78
    0x45100545060054681040b52418001059810041c010990f40014450100d0f84d8140d8814501c90038001d108200c003400303029001d0011483c1c01c000942c0030b403130301d0324018041031216400554502e01c08030981e0f0040343d124071342c00c011800b01d0f1661050104080e221007040f0b001004009509032403500c465a01150455070000301d442c10310740d09001e001d0203200c141740215030201005034080d070100031038001074401d00740051646038040ba400101e4405400801c0c440d0b01c000004010300d900300c18011101d203015800c0742c1e07043e40c40e041c1c01c0740c4c482440d01c6030b0211001e080c00030408100d000b001407c2024424030449051044602c0052124402a030114841c0d9546920070050741d42d0500024440e00912400003030308034280c90b011448580c2110314181c00c0300c9100081000c000040c8401030051045108480d414204080240c0301c0d00c8292001b28844c40c14503d00142c4540c4103c02e81c1c6400030161903280c8800d103407500903251544403014004404030081c3d08002c24206020454003d0315034816 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 45296389 1250 45295139 45295147
    0x605040c05030a0b06060f040f1e0b070302060c07020409051b010201050108070503030301050d0201170c09040b0409020616060b0d05070914092505061b010f0b06090d05070504050c 79
    0x82003100c40d40d1075000107000350001d1400708082800503244039000a02600d45590303402c6481000781c0b280c080d6802080e4a0414880d0010360002500311b620903207034140c9042c400503a0b035541010703c64071903028014003581201000503074a40c0084040c040c00d50003e132002c10709030017030395a55090a0001c803030449201c1c00d2800341c0c1440d5074240b0a0501401e180c5005100c0d0b10b003840300096172404140b04282c802d0007003511001c11a44100070300400c1c0f8400c012081401e041020007101c4a401c000e01d40b9016a00c0c005658000d46428000c010b0404d402801c05c52a006c4503021000c038007001d031103042c0d4086498030b1006000b034031038a1035107aa5034050b50143c9007045c140000035060f01c3d030860f1003042041440003804400f0303101203140703d0304503c0d8209003598070707900d1306001c0800b480e2607110790741c81013004c1643c43c142ca0700845c80744500b8150000802410104019210888070740003503150700b0510a00542d400303400d20a1108801600480c111002e15540c0e0000805a641c2103941280301c2c48081 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 45297639 1250 45296389 45296393
    0xb0a210c06050c06160905121c0818030a0c031d061603020123011211131a1005041511060c070210080906040602090d0f11010e01030207051209120109060504 69
    0x80b11311600a031403440d8640004080d0600203001c1c400600a041c85a1401072101090100400641c10056007103074403005d00d56500c90002e0181101100c43c91068030701c400c259455290080300700c4900a10a44800643c3c6a04c0c0d1030844401c03001a000f20300300384407000303c041d43c0e9540b0000703005441c03a10541031410340e98074580203094403418001482000c030f024811040000d00c0245142c1580d10ba065504c05030321280c20800b0002ca401404203400c111600c6418070702d61465000f000484c2d811403031481c4104405418440e03998212074254000540a21040c0310b00d030210b202d00b4170102400d01c0d190014880110f000c504010302541e15004680340092601d0443c1010388400c0c10341c3c044c90401d00083d2a1400c00b181d00c501c4020801045070344d0000b101c02c423507501d0a00c0202d0041c5c101340780c0c16000346107243c0040601ea1110086000c031b4804501500103601c28004c90301b190350302201402c00c030380c1d05112208150300000350840d80b00640c03d0700140100402d215009200d40100000b0136242480c2c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 45298889 1250 45297639 45297643
    0x3010f05041a040506060d1a09160c110609040212100f03030c06050403030e0a05060907080309060711040612110f0f03060f060102250503060108010b0a210c06050c 72
    0x1552220740200e080511200d01658030760800a8418015580070400790764410010700c40b4421610001c0e40c051038190741700200391386001c003c11145030a860b401c640381c0b64201d450143c8a1102801c10015a4038201080000c03402e441c01c045d9000f005d4203003410030070050300190a80e042034880c140308483c0c071070411080c1b00306001500011702c101c44130003d816003152801440007238400006042e00303032101c000c80c0415210350311854040b2280c1060340c800f4029803034159100e0605940b0801c6a208645020507101c201000321000400003c20080c941903d507030340c0d440c1d909500381c0100e512590f107041c0014086044400100c00385c3c840d010071040c07081a44201300d039111700120036030b0061641213a6010503440c0005d049e500302c4554004444541c3d036802c0101d292500d004500d83e0b912074140050800c940d2106220020b42d6822012303606203a80b100101800c8a00e01c24240f80e002103200e5040281307c004190b410305031743c00c000044ca4410201e03181d424601000d6404800040c40005401044601c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 45300139 1250 45298889 45298919
    0x150606030209130e100b060f0a021605010201150611011404030c060c0503010501080a020d0902030d0201020408060c13031218060c11090c090609130c03090210090e0c030403050c060c0301 82
    0xda43c010403ea44585154980e640014001071003200e1381c48450001ca6078455055956021041c1003166840e000082c000703464140c000d11007201c0e8001000003044035030060241c4d0354125541c4100d41c585a00d01442122a072150f8404c0700e00a5594517400c9103040002d180e600d00c00c5000381c4400c05100c20618010040f120960503032000c010307003400144216070340426a1034000745050790168940d1103500700c0c0c400500000500035494450682c0c81c0d54515010b401800481d00c401065908541e40c031100001607210301d400d03c0d225000b2071841030000846d45060506084810300d04503d290000140f180c270200c80303940004010503c0c0d183c03c1c1c2e0802c892041d101046400075030395090ba03810b10078130100c524021a140b4900c03072034012650032000c1d2600700c20f02034054411081801011620034003d001010541010780c001c207541e03c405101c1500030305040041740c0c040c0a0062280d03850513908102504050001c03400c1200802c443c031103421f802c20059000c5d504040115960754504145595000c81d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 45301389 1250 45300139 45300169
    0x1b1215030b101707090e101d010e0105010b09040e07080609100614010c02060d0f05040602090301050f10060e01051c05010503160e0f04110904080903060a02070b13150606030209 78
    0x240f0005100d00c80d820101c1e410003203602043d4045203030403844030300d0343c10305a60307501c0300f0390507450a51444403c0c0328a62004400e00203460082104200940a590070f035002401180051801000038a40c0c40c02c142d48028401030441054030921a1110101170611505035009142544899900303003110308e5138481c610042003c0012071010300107020020b044901e500b04043d10801d008507840035070022540160f5810740344500100154901490302c0c400a4000c170010034003035803070400080d441480c0780700c8650099401c0c0503002006480c01e601240c02601091100b0704200c01031203c0400400d00700d058012027401114042003541c10101418034102c43c140840740c030780515000400c80b8801142c40c0f160440c645e550f0400d170300c2d40d80341400910641002c0360681c10000203020001480081400f42690711340450903550700d030300c4500303070a0240e0040c1040580794100340004180d001895550f01c0c20350030b104203145503501c90310700c0c003440888216510150200303400260880d0703075161401401e0003400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 45302639 1250 45301389 45301409
    0x7030b150d11150d15030b060108010e0a0b040209150304060b09070507080903010902060c07030303050c03040210030b03010905030c0706142a010902030109081b011b1215030b10 78
    0x800c00b42c4603800e60242e1025001d00803001d802e400b5054040e0003046a40c0280d4600090141d84042114802021090b00c0140d0b214845400480d142e50302c05c2c8035040c101c4814040c850380b1034441e101d5802c02030005405850340aa0b003001426003a45420101001e405078050031151217150a0030908291000500900d1061345003204005081d0381000541d02c4840c1c124001948901002c1d001c81e0040c0043c0c40701030352007038021504d0b410042c400030760801a41c1c8030380e0b0103009a807511402c000c0e142c00b003910000d5010b100c0c00c0f801fa02c0d2612950003004400741c0200081501c002ca40c681500715030004401c1847c40d0070181d41440910b80064500c12400f4803503182c02e10f0488030800c00c1d05c1e90080d1a4804e0342100d2592000c040c080001d40011401580042c02000350f0780451034601019400013541d1180460644005120741c0410b00c2600032040850326503400c20000c0300ca0485003400320f40070340c010b45981da120001088000b205601c003c2e40c440c40b10990705040082600f502c120290340015842 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 45303889 1250 45302639 45302659
    0x4050906090105100c0512070606060906050406020a08030901150b0c07170606010c080d050f0a18030c02010302090105040308040b0901140309070e060d05190611040f0b0d02040807030b15 82
    0x2585442c1c0080300d84d0002440c1c070000c0e0005520b00641010080d00010b00d1003d40802e00b101401802d40c84141100e08940307410403039031342d101429a450b0040744107040150700320001c0300300401d030004021503002c003000000041c103c0d6841c0e4401c120680720703041141607074400304400c40003444c2044400c028008103401844001d030398200c01c81c1c2e1220000d01c40c0b0304020421203148104140c000135a5107101401006210340d01d888c8055800e185021a21081e200d030504540c0d1400a01a04904107125010350707403000c076026603800540295000351903450410408100000100d41c20030090030145c54412056035507040b500e40010a8880803980340300002100704284041680700090302c40480c0c610081d0351a10307968002c00120f6101030400041c6c0310303028020410003591482d200c28007045120f0403082002100070754403a0079500540c0180300c2c40101c0f0031000d02c40703d842000074050501441d071f4050300c2d21340c171641c0050408070740360b200321806c20b503980a01c405003c64410703050554105698041e0a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 45305139 1250 45303889 45303899
    0x7030b01030b191205010605030a05010c02120903030304060b0f0d03030204030501140105060703030b06130e07080c0c0c0d212006070801030807020d02040c020c011701082109040c05040509060901 86
    0xf840c00c4910480201d9039848980c81c003040001e400440050038002c050b10000c4810381041c0d8041e05001003100018000c2402101d2500541e8040e1481c03010003400860556075150781380c0f80100114002e056100a00201f011300954503855030080151190360090f840d82d10310b180c07003400d480340001c4581c80070038003000501060312490259a4203179018500818403009000200b4118807030500c0075448081c100c1004581d880c14040402d0084031907956400107a0b4549007054200d000c0e20308520480c1d00480c201e1600780c034111401c50b8285000e416a0740320180300740350480302c03400942c1050011900c00254103c50140b403990f45c8904041c14005402c1343d140a0340b0052425a0500005108013000305041065480d074001f0310a020764040c0040140018070000a541c558a0480450008600340c1c07844592410014a8504032a00c41c00204140001d90034a20f0004180c0c0c05140c50b01c43c801d008a0089070f44600400986a0607603c500e9691420070307090010300080141180d000700104001004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 45306389 1250 45305139 45305179
    0x70302030a02060d290f0102060702060a0915090b0105130c0804060504030c060614101d0f13020d0f0e0a050601061103071a06040509120f0304031707030b01030b 71
    0x40503070704441c05aa44c9803030303051613001080040341013584810a1380c031140218002240c171030f120b010111040b0703950000d5a401240d4901c011100c140060b000100420010011a000300701054441e400c1d2011400e00307401078008517001c0020940d800141040108200d003004040104040001641840048607621010b00400e4014000420107661100028107040c8207500001e9100d900120502000c3c0e03039194240aa03401492030244240c0c1e46800c400480d6004441081ea0b0306c4030000a9003040a410b4104010146c42c900110b8000d80340c2480c2114501c094401041000c64000c800904c010380380324410111414494650100d40c405024038020a5000510b50304542042c54034900003010114041e0440c0144040104040680f41006030704403443c5001c603201380002e59081001e95101c84001e0b03a222050241084641c1c02000041e40910b41c441c0250b41c8030740241403004200d00094103002c018802142e40c00000390341d402d000740440d81c0c940101980d100c011150314403803401c0400040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 45307639 1250 45306389 45306403
    0x601050a0206010608070912030e03010c0314040206031308041203020705040603230102040b040e0f1e070f0306030b010e04061109010504050f0f0907080f0901091205030a150b0d0e07030203 83
    0x1e0511179100e00240d05288690f0580011b008003803881e0700403510601d070160000c007000c0303aa14825400c0c091040045131003031144031182c1c410030020501e00e45840c1c091107090760019103220401c00b19600e8035404600c2100044c0004d18079a01b0345043e181141c14002e00305585500500e01c540e00f8030800704042182707120b0442314040301d02a0340d0402c86004210303500920407984003800e031650110f00041e100c01c0704030813280b01b2524a05045001e40c3d94500241022040282101303075410807034041200e5900c00c1c00484c24800c2103003000140321b40ca82c0c45c2c0300c04c003d00076030200c83c002100310700f0030040040d240207070020300d4100780d5400d040c404490000703403003030145c0e000320350090100320401c05550b6950008401e40c004007400488003414a40b10003458100202e8601030f500301e0380b40c013003400110305201da072181903000b04d007540405000e0341c82180c0c99807014000c12901c035194008080203040d901c15101c028074650403020b50392100b900c4030f03105440245104040301d400c288030400168502150302 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 45308889 1250 45307639 45307649
    0x60c1707080601110f0c040f022b0b060d090203010b010201090201090b090a180506120703080f0304060f05010b090f01090302031504170a021b040203071e050903010e0606090601050a020601 83
    0x1500070340c2d4400040380e02c603048942141d000d1140b42d814039040c100205a22010040580d0b06221102003081c180e4203900ca202d482480510281400c403c0d84103860044c0241282c86003408101c0c15207580029490703802070340b000c880310350361a501d140841c81d0900c213a154000c4280000d00840404d038002a001c0105841142e00c1c80c00c000800034211b50b6449102c0014000c210b4009140b511000d07140030080c801101c00341e0182e0483c3c0003110f1504000110441101d41c03210445142041c1074800c1e2034a500003a1044a40300d0f140c605180345074000b4040c032406010000b2200380c9400c0007804201443d0402c4210505000520708188050f80300469809444040c505400001d41c03600e02d00822442c12600d40c0b0701000501040a840143c0e0100301030407480d0000100000e2445910208000c03803005035088030128903d84003090844181024840c100051410441d0070400817801103030948a08004040d02c40c1c1001081100c00e00e0104080350f0420000e11701a802c194460310040d40e1900706010f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 45310139 1250 45308889 45308897
    0x130c03150905091e0109080d0509070b0f041a1b0d2319020307021509150a0c0201030b0310091b0801020307020303040f0f0804090906050604020307021902060f0708030103060c1707 79
    0x11131504580c09401a400c001d0b80070800c40d5541c0c520b43d200000410041ea04c1003100c5c000c2603030000e2094121020744d0740c0341c0400c844a134946458505d0a00300b0802524a03240500d10a01544105202c000d940824406161018210700f00090714000d16005a0500ca145091481d1141c946c8020501e8260713078052a484e4403c900034900c1e0344040e8598050004000d40c0b001d01d28030164200a181400b030f110302403055510f840240c4003242c2050b0503004441071100000c02200f420400f540c4284c01c8100b01140242c103460300390400624803c10740b4136a200c1600c1c0310241180f68038105081d640910b00502c800300085007035081500c8002c4d164440604050700d040504240c2c01d00b800703e404481c070405a8030185141d5500d6880309a8005008140c01c180c941515040000f030180c00c040c02100d210b804203501500d48c004401c10102051184a1001e0760484024001c264900d801e4000509243d07000b00c90041d1290f1551400405460341040c0b80402c001d144c45490780c4c4914000e00c0180c102c101814 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 45311389 1250 45310139 45310183
    0x160602030c0c070b0403060b01020105150f0a0f0b0901020c030303040b010b030c09130504051c0f0f020f0a11030d0905060702040902011101050403030501150c0b0a0b130c0315090509 80
    0x1c0d5070241409440702c0c44400e4043c1910006511044a0050080b40d01c40c03407050100d030342150f0059080342c1040711400507458400f10462500d2a080e280e541c001200105880340c4580c403040c090365812000d41143d914034000040411540d80c0420403950b10040847c011840c500c3c003540c07404018481845513070028940480031510101808081d184502005800000500840d81e902d20240c40260740669640c051540002240c84a5009100c0c20306486d4490740006000c170f01c2d04a0306450486000c0085010301c01042d020101c2c18030421f0b0000740910156116102814100f40c18100c07106000c5040c481d8200b0104056100e100036a0f48041e0112000500f016107070005949001c0040c018411035481d1400b000105031301030b808030341616604417480007194154001500d00280d070a101600b103041310720000b0205096600505210762002d05090398031000034a101051301d1a840492002c40d1701d5030b403400f2001403503403d82c00080000b64024811418046a6a519448811050200000651 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 45312639 1250 45311389 45311401
    0x16030c15170408030a111305100201020904050903090a080304180207060b061303050714010206040602070c0509010611010c0e0105070605090c0d060b0901061107120f080406020303060a080316060203 87
    0x301d1650310310040300046800900e0140b83c032189070381c821180700c507195103016918051815a80140c9541220f00c1c1c90318100c86041c0400c10a8a03240c107031030041159000c02800003207495a01449018203030b81e1004548681b0f4040c10070a01000c01d07000283d1070b030700a01c01004196100b540c40030404c04410360040e90f45d2140c0c00e03c00058000e8020380f50b0010000140c041070f0f1101d1401c1c000031030340212300360f4144544541ea07141c4d04610602c4c007980140d00c107001150200f61143d0041c031134584900d42109126607034070086803203100709078003076000300b003156280464007e420301401c05149502c1c601000b6640302d250001c0c0040c0664000a004240c0d200d0000d01e00300000c00880d040c20300018410080207041d8500b110260038000617140c0200c20140001845500030304140c180040c080b0042c012450402910403480c0e4214130064818182c41305448011401c0035004001505240c2d000d95540d1400c4424024810760a130700860341d59004101c40c030b500380d481c90302241c1615030084015942e45c942e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 45313889 1250 45312639 45312647
    0x40f05010f020c061b0306010207050f0a03020a0605120a050103030c0b1504050a0204030302010b040903080f07020a020607080301050915010519020f070e01030308070c11040c030905010c030e16030c15 88
    0x12001d05200c0500c0001c05141408000945500c00d070880d81001070101c1080c8000071280c00140c90303c40c050303400030801313110500d40006010380d00b07039000c4c0440c40990756030703000107520103419440310000c11f030000340301e910800b00d40960f07076400720201100344060352640d41c005041c5050f100e4060502040c40001c00c0c403c0f103002c50701240034000140140500e00f0501c0c14035000f50b1152004074059881c0152800d25400c01e4040d507414903415440d0802241d4900007581c0b0342000040a50341107008990034a00140c1e1890b01507c516030142c3c0d28907032a581444180010381d03102a029107c5c0c0526082160141c4ea03101c02165137592540c003005442c070b5a400000c0c3e00e411a003010308801800303210301c04600400c0c40e80c00302d4101c900130b0360780d1880b948035a1001d48542c0d052400190a010741c07004c10b00c00e5401c180d0891080c0002ca8500058801d540c1e886450841c2c1500c6031407400070351075000507a0303058030400c5032009083c07103260b81c1d51000d440c556440d048044240f240a84e101440d080c0382640700d010b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 45315139 1250 45313889 45313901
    0x105070c0303080901061a0f0901091e0504050a0e0c190513050718080c0105030c04030b040f03030e160302040b030708030424090b0a0309020f061308010c0302070506040f0501 77
    0x100c8248600e1858032858050015801200d07030030001c3d843c114000450207035800c0400c03014117000191a00c0c1c2030150040c865164000c103102c4d418410184400549002c0c115040780510001241d03840c8400e0910041009030313640903150f005131505101c1c103942951404542c00381c00003022510080080080c203084204c104055220651040300200030006034206034000900c180c0c1655140d8130031001041e80800700480f1030040d020b03c1e910490782c1040d43d5024400541d0001d540002440c206645c0b5034030890b02040803070741142d405000036000c20401d50940500840307405540050302d10b250100c2000c8000203041d00c4040c2c8280c0d283e204880013600c0038040403014080c08400e0b01e030703540e46070106030300d00c1f0440b9080d0030303501300307010303a41d100841d104419030f2046da40e1540c082880d0800301803086003d071643c2c407070580c0c0c40300580034188615925100105500021000c0c4000700c2e81c40e05c2c03c1c1c1070854a08652a0091500400c1401c0004e034010642c103500c6588048080c6c15842c0d03c6c10304e00c0c01855 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 45316389 1250 45315139 45315143
    0x3021f0608010f1a03191415040f02010f0212071b0905100303090e060108040b07110708010b13020702030304031502070209010303080103110a0311101412010303080f0702150402010507 81
    0x4a02480030840f00301640220303541e5150110074280211008060680d98001d156140c1c2c00f0019440001300013546130301200160200705421a0145e4218894905c0c8142065030300b1203002c00d01036043c80441d60480c1c200c200b41115800a0700d840868400c0c900c8580c4281034004081d00c46c41541c02c1d903441890000c1078054020344c90200060300c1c10120110140e10240000d40214158040000d85082c040390224801d07241a17484c200a52516580c0313510400000e00000180a00013885c4207400204004043c02013a240740041154080c540c188070001005100150a8500400511003d610000308480440387d108500c90207045001c80280000d01a180c0f0080d0300c2080c410001003810350004180707042c1c9009145a4411195a00c100201004039100003800f50070151100045868084100c480303403003d030301f8043c0362203a55032140c4c0ba066000d20340100341c401c1d960006000303141e48503030310950080da00c1a1990450410341c1c40a91341e25038241c80704000082d41c1d0005030469124000703842d0195 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 45317639 1250 45316389 45316391
    0x9010309060c2102030603100902043903060506120402030a060f0902040506030303090a020f060c01050f07090503030705100c030605030d0207051903030e060d090803090102030610030903021f060801 87
    0xc066801c000c10914048122040e04110100d1003440e058003482117a019800050040080c800b20072038800c0600000c2109a9101d0b40e100105800c1c03081d1211000d41d520380344001140003000c1e904010503250682d0310f2980405181c200244580e84921084440c07200360045070300101da40c1e0342700180c81c00d404600012f0000b130a2880c8800f101c005074002810491080b03905021030765500d03003030558a000841e400b0103a43d000004060143c240000081c181c60f1000d06205d10740f9440407901402c2d2042aa98032031414100d004001141c1d42c800d042d5005040200c014525080b81600c4060355142d80e00c1880000c2036940c000f04002c2e5000e503114800900c4003401fa00c4001c1c0c03510001039191200713441000c1c05541c0c2c0e0201d0584e2001454021000c0c2d035455180c0c2c1e90341c90308840900c51650040402c524616680d1104100815030440165110f003406400140e81c0303141c103505010b50641410014005c0c1400c101c80d0100081e00469002c56540414001540e031100350303404031002d413040354001c0c500740d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 45318889 1250 45317639 45317651
    0x804051201020909060f0f0906040b03011a030609030f040e1f060c0506100f030305220f1701060e0105040509120307030603111206070f0309230d021209060901030906 73
    0x40c0819000307409040f804495401195031081d051000d4038000c54621603101c10000411049481c02488903500210040c1002500610800100782120009505170b00b4002307980802e41c40310314040003070b070b40d014811401650a092610801007190700541c01042c80c0c01c0302c228001444e105c1c441c09050b2a880b006c0e00880c1d440740d59100c0141030b0f299412016074407405003e00059005181c80e01c00c100711010714501400301403568500710349640101244003010076244081074040f80f141c0040a01a00b200c1900c41005898040c5981018a80201c50f10043e41815020404854030418990458800340c0340070a5580d0b03160100341c14800e044a9001c10048048107124446d585070340040103483c070030201034201041c07107c100100d810300c1c99484c0c142ca174880c6001520080c4102d0141035210407a05020904400744da43d0304a08440f18441180c81610800310f41c2d80d050000c001e81987c034007240c005800c0301d04520480c07803014401d5940d4140100c60008120445911035444252029040760b0100302c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 45320139 1250 45318889 45318919
    0x50a02090c07030f0806030c0d0204021e0415030b0f0d0f050d021b06040503071e03051f0c051908060303120a0c110d08040b040204090204050a0b130603110d080405 72
    0x241e0b041a007090f00013900300554400c0040c002d0610038011040240100702170b410840030480d2400c58400c040744c00c00e03001d014000130710794441560783d054408140e105480b542051165100070003c0c41c01d8008050501c074003101e99032502d401d15810017200761703460320a40103141040091004200e0004145100303d070303554000e456001c503488146914950407010015810000c00009002e940502c583c19044600d04202c00c002e001c1c5000390347c3e020a40e10b41e00f495500d0b10740038109103845204031441c1540104440780c101c01845450510112400c0190400b82c0e04d0584500303c28010038000180482c15001c10f00581d810401e0b0707007169040803190142403a101021401509000c054100032a0448114203105080803940c106060aaa80c1c0c41e1581d9035907131601e0313454481c0030b4001e03608580d072804000003680300c9005951044400140104543d41400c0178401521014114a002186008010310000703517500c0304006103850072648200b8000103800c1c0340c90144120340c041c42d4803040394005c08038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 45321389 1250 45320139 45320161
    0x30510050601020609160905100f09021305040501080604030e01050c0304031406090109031b03180e061801050f040207230607031506050a110703050106120605060a030206030f04050a0209 82
    0x710400d02079080e01c0443d140e543c0c0844da00c42e00c002110b04622183c18043c44600d190340e221717540c481620b03510003881a64624007450366116541000038081c0e0002490524484091b82041c000d08042d2030402c030703039850900c08544464000d00010100203650ac14694240e1250307051700c0d004103046080d0384e41c5e031b540c2e803034900004c0400034072040300c0c0d0003000009454428180300316154140c0640350f404460080c0d80a01c00718019580301142417200388071444800d9100d4085c2403015050a0900282c2410040c0c00c0000180d1038480742201c91800b0300052006032540c1000103110482920b01584034151441c2403801e0144440300980f40782243c110162001c2c0b00041c4082c000e000700e440403c04800b00d4440307001c03404001d018100100d07a04002d08076895104214800981082c0010344140d1522960f620303003903403569407000c1d144191010f01e14050169074810650810030031902180403502c0d40e40403071140e00000300050810300c00d40000405101c001e11440001c107030f0082c0244001d1800d001541 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 45322639 1250 45321389 45321391
    0x2060310140402030403050909091501060906022505011b0807030203030118060e040305161704050f06071104090819080403030c0c050a02060309010b04020f04060305070215010e0601050403051005 86
    0x4240c4980100740301c802402c2c14402c40f800380d03415680349440c0422030703002e1080b0888084c140c45414030552030500642d4141040e194081c000682d919400c0c00c5c0b410400918146441c100914110343c0700120920036501da62001c41222800e00b4280c01b0200f40c40300210510262640143c41c9840000700310341056404402141a503030101c0c1107507030700341000481d0000c644844c0503001d05043c101c004100880d020700d0240c611701d402c10b0100c484201d10707540c03001c4440c03190a640c800000c902207014090362800203c0320400010644d200c03802d200090300c914900b544820449401181e80b1064030b0180800c24086441c002d864540145005000510040041500310713000d8000900d8a40c01c514098468101200100d07005001800b14680c1d47c0c0130030400d0351014094544d0b56507100c40c0d040d07040c9c036140050090003842c0c0d500b60707071120b15058018003640c40c020002011500100300720101070040030040c038155040701000090903941c802c0140d0f1305110b190405013a0340b1451f81740002c8100b0540000d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 45323745 1106 45322639 45322649
    0x60c050a030c0f1406010311011706060c0a02060309030a030506041a090a0b030d020303010e100810150902040b180a12030810050a030b010812090f060a020a02060310 73
    0x10742c0c0c0e44c81034041340b140c880d0480c00040007405454881515508800e0070503030a03180840562605500c8000c009030300c904070104005005a500300580512150301505280d540d0600c042c2c000d41d02e030080301e82030001078202070002c1d149092600510204410f51440303100c41c003284404002da118001450b1210480d80c1d4420300130180d4040000408d000f480345c001c0d540c3c0c0d5050000000310242c001b0028901e010b40d80c1c00c1044200c00005a0340d01d90b402c0048000389020418401001c0d05d4130301e910a0355002c3c00030902282c144c009d00f005104860400701e026050200b41400e11101860074843c600501c4001844140868040c007005030703221201080d103104c01901c603400a0b080b05800c0d007040e211115a50010b00c05400100304010303008002c06103041c10300e0020000034807405d2141085601a00000c24a4501135008100341c0f485958001d04d207a45a142070060044000014890 = true := by decide +kernel

theorem cover : BRFrame.Cov 45143889 45323745 := by
  have h0 := BRFrame.cov_init 45143889
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45143889 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 45143889 ≤ n) (h2 : n < 45323745) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
