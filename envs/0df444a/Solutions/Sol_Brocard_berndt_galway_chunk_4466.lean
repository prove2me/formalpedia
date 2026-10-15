-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4466
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:42:30.369708+00:00
-- url     : https://prove2.me/submissions/2ee6cb62-0367-4c68-b55d-bdb12af8c0cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 803057553 ≤ n < 803237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 803058803 1250 803057553 803057569
    0x4020607030e24030402040b0301020708071101050904060303020105101e060c06091703011701090f030f181205010e0312040807290a0c020a030f2304060c150209060405 74
    0x10250440500800800481d0502c000081d01c0f44001c40920b0b2030345020f10402095404071403140380264010f101c00310005044a017030360101d84d88550300112015645004807054040c4031049984142061000001d050301940540e010f00c402c00c155444046e110301440304c1c80c803060380c01c1d610322031000d00003003003035511aa0300d030228584a941c010a50040300d0311605c81d12454a102411403d0000004000742c8001d04407242d1040c0d041d50084c45400b903075440302d14440040f00c102809214500101e96802e41c460789010301203441880c81c40071001e4440f00d1162036001c00c41c408503000d605e02800100c01480020035502c0440b103030540a9035544d183c0e030701c4003e06d40142c80c0464400c000c41704101e20340b1319480e4034020003003581801d182c0349140c5803940c4400d50310032241020642d0444190880829440b800c001582181420104108019440c02d00b95145000b115540943e002080100f44130b82d1103075803e401e06000742c076040c004001645c202c10403031107001c0c9416800041040100030f58100441 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 803060053 1250 803058803 803058827
    0xa0e040b010230040911130e01120f03210b0a090504120f020f0d0f201b0d0f0b070818100b0a080d030902120c0d080d1d160e0402060703 60
    0x290301030404d6600c5010205507400f400000010140110f102c0d903061121072503042c001c180300c0829800303551405400030341d107410072000a8002c004003101001418012012030b030340a40c400529880c1c60051001d43e1008140e5000b10b50b1007400380c0000084d8011590041600954010907500007130401d5a000f40c0b004040d0314440d0040d80200e00480c4400c03101808150315030050b603141c4080c0c500703100764000c060640c0c09a03224805d44d41d0305000341c500344000a9517800041c543d4001d00d208544400040d86602a0344001003e8411501a181c10004106000c5015030455169003105841e58031040e018200d12692000085d0321aa8040c2c90a51160f041090144c4004d091044144e495070411800c1c00ca01361034003800301351642001c00450901a42c1500903e0941000d01980000710340003a038204941e030006003200c6030201d14070469090a5004242030b82200c52540780b4108100c91441c1c40d803449a100c940303d14020b00000908281044107a44102d5005102d1480c00445c1ea400b42c4010840f12 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 803061303 1250 803060053 803060143
    0x80604090203160801270f1b090207050a050c0a12030e06130b0c0706030501080304090506031516090e06010903020108041722080102120f18030a0e040b0102 69
    0x3628801d8903072654143c01c070250581d5000441c4130414103204c804900c2e42c840e08015012441701c80c0a0104800325281648147c0c42041300b0401035203440b0300b2aa210349904502e800d6440042c802c820070500164280c007079480365017601c040c07101d248200000440c0a03c034803000d2070a01e1035a500000e00c5800e003182d82400c020819801c000e428030cd840c0202103a0b0300019008100010108005081000140300402d1103160a001960400089680764002e500c10301424640341c0010491030303542072024000c1c0004000009080e0b00d001444a9029580f5004030004110217540101e0816108909144207580684550b00060700d1a401107514910085c4243da0702e40f420008180424014001808821205d078007900e4200c03410b40c1025100144c1d58048000b50703104004903001e81c0c800d035007596804501200840c007240e4500190000130381c00490a082c6602002454848207a000a244071b003400701078408002640c401c00059956898400103401c00003e03030500c1850302803a01100182c0c0c40146 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 803062553 1250 803061303 803061313
    0x1051c0f0515150405190e01091502030103030909020307050f0c0309090c130f080c2202040f0f0b161b03020604031208160507110105040e04061a010e01080604090203 73
    0x25100e081c01c0205070304552240c02c0c030803424019844803401000342400c50440c0c0400590406400091520044511480794a0340b00e0428290b460420350111100c607801183d6076000120040c4003400a42c02400106c02050b0303002d4020490300741910946e4840d48081d103d2070300d090303043c90802071039421240c5a042688400c0040c944940c55900903d40100e110800d150380f20028401c401c05030404640000c40d040304400c904109a40300080e29141580043c0e84030051500303000000d94088000041c509101c1740001000110016402c000f201210340008040803c40e440350914035451060840300c04500f86c500080c02d01142003c2010407102407102c02c9492615a658045001c3d600264020f58010210700b0b144144a40c00c500801e034018042810406039407600f48014000d801110307006421030f00d84c00e2400e5000c0e4091401c40300a402801d1241d4414a032519204029040703100c000c00c03641c04c00140c40241c55000d1442044032810507121241c00d0f50340d100c20311000b8040f00b070040c2d91501c10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 803063803 1250 803062553 803062583
    0xf0e0606090d080d0605040c0c02150a110d0815010807050304060506040f330e070c0c0b2a01052205070902030907030b07080f01031101180803120a0501051c 69
    0x19403005041360070b104034000c150549454100402c40c0c80c4180704070240f084050280005a5813020090540710048451507154081304d03908481000041c19021807034402c07a41d00141d03180e00310381210702c0303900f445462403100040349004440706141034510002180061010500082071a04840d078040d50140002401c4101340e507210f0181c1d148115182c81300c19040e20b1205034490b000b801842030b2901200750034140e82c6017440c01c16081c80007d048030100050441d0b280c0c200030705080d4003c028452002c3c0d0030384880030b54408510300e01c86403071100780c141c450b44e4804078200c0041c0185440b5107031145240341001c0f60300d50f03d00c228000f600c0048030507000b41580800e08200a10196019000d05401810b41c10304514120a002c0005400e0400b0301907000108514241c4110f100360540c2c2e80039083e1101c08070070343c006950000180402e20030a0b40307000c0020903103640000240070b4003400c8c1181f0401984030641480b0844000b030261607000307020703003000304002c0154613448200580704002c00280740d41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 803065053 1250 803063803 803063813
    0x10902071a010f050f030102040302030d14121006200d0e030f0307061d010527150901021338070615090f1a0f010c0213020a03060f0e0606090d 63
    0x4400d8101ca111014803d8082c411414519060301642c0d01c181c0c004c500e41815500001d99a1100d5105076007000b00003035801102c055900151984054580300300001c44c281202c007040803003594003441300000c1c0a01840003220004216480100c048500540b085510a000032102e1240c100c441c0303901442404000b02c2411420002401414007901d030003d0b0108060706000070100f0841d03228502a1b0606007485080401054401d100440c040512051803143c4586282050b10a280b4100c0f0000c01500b007203010b00040d00103002c213940c011003034807045031101e4406542000f008504401d038260007600c1c0c050082d00c042d01d0300c040c410011101c1c0c100b0105a44000a840400004c1d0041d41d03003c02d8200250710311401201c2d10071580710403d200c00700b007100c820501ca41d86908101c0c4100d001d8501024a0f074040d015280b15103801030980c000031044000c481c40a584107129840c0028540040040d46030610b149140a40e05040c45028040d2604d01c00c10100d03801c1185081d620000f42603015000030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 803066303 1250 803065053 803065103
    0x1503010f0306110a02031611030f0105040b090a03080a0c11030313021f050d05280209090c16150225170405060f0304080c0d17130b01090207 62
    0x114080c1200c454a00310302c2c00c2c2c0140d80c0b00c150440c125441c24401141e000e03070084142c0c0d5070381c1000400d102e02004c150130450a00944207840d01e8160080402580b2105810b40226102d0341c05024030284c6a142d841c141036690158000103000140790601140105040e9045910307004110700e041100800100240340c00c5500c15194000015030300d941d0072045003003017504420800d100489009500c0410381d0003429900ca14042000305c0c2c0d0741c1c1c0001810b60058200c51840200c07811207824824880b4121213402035010300901440b58010300001100080c210080320141c440501205005c1c080c2507640c042c0042840050705146034091140d40290303090115402d04040c61840140c1c1d00301021300308240301040c1c0310410007100320100002e0265444040448034000d0786801c01e240c0d82e03941ea083c505030360b01640003c00c0e942d0080100601c0f203075030b11104c2400c02034041c184480c001e440f80c003100070000410800003009100a080100029180e0b58094681e8038016a0f0b0141801030b80c0910680c18 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 803067553 1250 803066303 803066309
    0x903041e0806090f12040b18040e03040b071a04050c10020a02030a03050a3b01140c01050103020a090504120f17180d0e0a0302040b060706020f0a1403040b0f06150301 73
    0x59110040c0d482800384100701d0301c107a5101090407181b400c2e040041e6025107210b880900c210300703c1c1020071040541c6407079001207a24050701050701d840f507071205010ba046600c01c1d417041c0d41c1c0b04005081d100e00b0ba50101c9056026030b50210052900c00080001e100d95020440404c60650140000341c102684003131000d001c0181c0300c0d656059544140d0030025042c1e0305a250010001c1c15001064210441700016202440140d81d0507040280f1a01d40100c50f02d029003502e826403038502159180703020303405410140c1a01c2c4200c84140425880c3c083d0380040340c00444001d0540818443c081980714001e000007455034003989060603241c00014040390051100355000301d90000c4d5032440040500e024885420035070381c41c2c035102e016545d8403c0000d00e80610342c00081d03c10781d80c941c1403045036690b0400b203480c4a070380800c2c1551180c0c075112003264180c000018140120350004c01105005000340300300c2c1e20940d13110350800725a840380e844d0440c40c01c1000340999009000c4444c40070050f01c200c1301071402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 803068803 1250 803067553 803067571
    0xa0f050a02010305011d010303141c020417030304080306040f02190c050c01140418090c06020102090a0617070e010e06070506160c1205130e04060f060e0903041e0806 73
    0x18500e00344001012140c0c164421000c41d20501e620000c610a00c01001b811250146898000e0076140601c03400e842c03103207900c049080d4006100450225059030060400c03181c05030702c504030303081c54150000d45034801110014040c001c20800511a0f103016885a00a640981c8006080c00c03446801c91300c3c08802142901c02180e624000e45081080070841007071082820310309010103c40c40c00141489010364066215035900c80c00310345403401455444000480e41000c18100300580e02d80001c1d0003580801c401030700074003a0040110f282c5018042c2301e0358019800034111400d540e0404205c036640302c4940d0341e50400880c2e000c20184c03643e411020700350003030044001c1c2001c1e080c140707000000000000e14a605009070000b4000108101000500d01c4000354207085039941c81c5140b001840032029005801d080c0c800509200600c00540d110300da610400070801c1203242d8540f0307860312110303500700c4514a182d030081105110414403c0b07650f5000380100781c51100d6003512200b40e1820034800b00c81041d6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 803070053 1250 803068803 803068813
    0x2030603010b0301060b0d0207050f060c0711010203030613151e050a080d05031602070e48180901030528030903081c0606030c0215010e180a0f05 64
    0xe14080c0708000108100710002c0003420b140c071a1200040c01041c020341d15180c0e000c180c000511405001c0a8035038a28034040c0d0360769240c03101840940343c00041b070a65800c040d46507142c855500010880b4007404d0b0042c044030540245411f0792001d4600290729012004901000050b06541c0480003c8e031007811304001c404090515007480702006141e404030140e80d0100e07017003140158010044035007010701061030344a54090007500b40c1c50301d0705681c000c00a8034001020058015802d20610f1180844100c3c1c00001050b00340e20076860310a0440e25001410320070a036180d502c0c7d2090007c001003058428205d04104114000920045003684190303240d03040041045010801c1007106002d03801c3c0000c03070443d012403913100149400701c03d01005054501c00600788064006a407100b050303882a8400c1440304035282c00004000d04100040a4098800c042c0440d100400c2800fa10341038480080158105075940360304804040d480d039031890414003d200490f00450341da42d10300365025005400401c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 803071303 1250 803070053 803070061
    0xa0b010206060622151421091903021605063c1210051e13020f03090d141e0306150f031f0509040201030c02030405101e0207060f1103070f060203 64
    0x1501c001a640e44c2d280c1158004c01c01008021091f0f100810016082104110142d4400354120300d0014107515203030090301c500c0c0380c4608050780041d01040b5a40581c0341840066030322014003120340a420003a0916070b40751325000301000c1104080070b0001080b4086180c0c0300548a82c0c503101c0754030611b4100300c04002501005000d000480e483c100800c01950f10f9944019150203144032282d50004480c4500100710108808090b160152182030b400540c4540e0b40e8244140a6507860706141c91101c04036064075540c80f40040c014082c5c90316400518504103440c0c42481c0200483e0303000800d5030754410141d522080c410705885c005049100c00c21100356a803070070044000706a4171380c255440700d15442c91400500241c0c481101190708541d0a0070003050304002c1d11426419030045800c0340d60015040003a40c07030910f6000f03640e20300440740701030080000c3c0701c007500c101c1c4c031100c060140030042038900780700a954900c03031b01c0101412180d04c410749060000c1d5640d1700c185001081020f94800341c000c8140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 803072553 1250 803071303 803071307
    0x52701021315051209011118040c02030f04050d0203150106090905130807031b06021306031104030308190f06270e0c0118051201140a0b01020606062215 67
    0x550007820650b482440c1d086000140205503105622040c0809199100411100202508140090989007008944505680151505980748480349905c9682025414469180088100c80415500321400e034a45810b000c2800710115034900c00f240c05110f600140c125102d0721401403030107040e060713403200c5955140116035000d46a01800002600d041c807548800054410320844901c6039142c01d010759144601c0d00250400b5903941d0026281c00d00001d4104520350b5503491540139109951420400911100c54920b00da0285000060204c0c00310404241c1070748003000d500e4034080d03034a0790200d156541e40d540003080e03501982c0104142040c4e0b490201d515100600102040f030b483e80c404100c502e81143d0788698400407840d1403410300100c21403206140014131078610140201500102280809002440c02412070302c40d80c03808031307415201041d00f00c0b0050203032610a4905074003e2159490704400c008495004c480c2103e000c8200a55500142d101115800f00600700c111100082132030300180 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 803073803 1250 803072553 803072587
    0x3012301060e030304180b040c11070902090d0303090212241f1502070e1f0e0417030a060305011a0a060e030a150e06010f030c05101205270102 63
    0x100700184100e0590005030764030000f096404070f4141080318508450704114010042c04541c5000f03030080d007071400c0c0f507444a801050320301003020007204803481c248d51560b01100300e000e598060f503440000e20080b81d02003403003a0011401a40000c0c640441140d0660181703241c0080301d9401c40211020914603440491b94684041c0c2c061a04450f140c1070008500c6210b0005074240189058980040d101e4034640d8400c2054502070450b0800b51001401c1000f52a4440003c0d0040003d110144e4940451400240000d0500456214003031145910503404605843e400003440078212694130f41c00000881e10034001c2001070058040014800440304007030024200fa030b0f40280d400d12040000d1101a074078000b414a100321b40085880c0315045c1c0701c0c03448001a200a0032466114410100003040030f40c40a060300c1c00312440740015416456555003800b89122fa0054110013240d04e00e1951303046210300d60040e6900018109a0908814620030340b1000c0311240c070782003429a9404200203440c2c0044c010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 803075053 1250 803073803 803073809
    0x90501290a0911070210021c05090915010f0822230105061516061b03060618050402280507032d23040b07020112050426040503012301 59
    0x8050006079565050503d503489503110090140c0c0c03006144a1829100b4001500c660091035401c1080818425000382680c000b90707000da03c01c00ba9840420144801e07030003080c0e00042e041e16100b60400700d119080c0c6015500500200d44842e51024600d94900c10740f07c40303030810744200e858105a901c40a9840211070101c04020300716031501e42400aa40c0d641c0011030202ea0703e0350300c1e03555104108030800c00007803e201c034024010b03410003004800d0321214012088400300107a60800115503240d1080311500501036804a4004c4502807d02c102c0c20f0036002011041c14081c9140d041441038400c0b0140e4002c0c0542c2c2500040020407038104055003d41d413803646071084107624a0b03080361122121081d201106c102c4060119000f40721071039100c420281c090880410840300e44480d60303101d0030000f61b03002000c100d00040e020100b08060024030303c10280a40d401580000b00e00c042907002c8001d80100d00c68980403060300b44030018069909008045940410071075840b0b02603d0f800038450ba491040e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 803076303 1250 803075053 803075069
    0x19180b0f030906180c0f01020a060c0809061b0a05030601030b0a0905010609051509060306011106040b0103061415040213091d010b030f0a06020901140d050421050d090501290a 77
    0x1c134000c441000018040030040801ca41ca0b000160080d40144e140200c040da00424017030038481c06c0031103c2d800001052040d01d14000340c4095548031036050340b04071240c10074410010350501c080c00e10688134030302440c3d1144042c107000a00d221148000343d49071720142e0140c406980c89900500c40264010501c0005150560f02103000c0340c00110481e20a00926407050700961011000544a0388a5002035011154080c02d0305c9507420541841014110240030684e030040c03c6c80c1c02c0034200320300d508886104985581d200b0b40036686103000c1202a503c001d000e0414222410004940300e039084c890541845410780d002501e0100001030a4291000086000d100350041d006040c012030740401c000704625403144006039034092001c01030350120704004c000d403c0c801021607000b69600580e4042801a030044820300c1609020012113900b0042e0030724507500280c02072006c1070701c41c80700741c02c500f1005201b40300200e4509140014680c07903150b00e41d583d00d031160110341a13003900d040455289025044034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 803077553 1250 803076303 803076331
    0x506100e030601120606180501060816020613141f060602010902060a030b03120705030c07080606030d0c1e031e080f060904060b1009051519180b0f030906 68
    0x2030000a07031284814400c0c0c48000c2c0b4080104d600704a11a80000c01420200e80b880010500340d00380d090050509005005c082266400464170710300e201c818034200742245034001e0100d0347e29151101c0c8648092403044131030444001308808243c0051158078898121000070f0018100c0c156490001e4544c144c2c4a90700b503914100c02c54015854040c201c0d400f043c82ea0401041c001031900100340b80141c0d24408880844020400204000000c0003c010f00540325003120710541c1c903901c00c41d403501800e4603903c1e49607000c0528001e50602402c5060406401080894400c002d0b81401c1e4106140c0c94100320006a50b54420515007110a10440b88240b01860120060b240000740c10b06c00060240c0f0051103809100001800c104413a0003031404000d014104030a80c01c203800d0003410700c1005001b842e00c141564499200310010500c1030300c1c140a94041d650405020000d41500c1c4064160044060310041d0000850b00da03203010014034105071024252992481c0c60300c9194203081300030303080e4038a02d42c0c4c0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 803078803 1250 803077553 803077577
    0x30b13050703090b0a0c0504050910030501060e0402042004051e1906020f0c03120d0b030106061d04020f03040b060a1703030a06090203090c060d200901020d170a0b060405090a050610 80
    0x801000d860a0356416500e2b40c0b10b9495400b40c0100b2041590b0004002d5820901d01040721285104401d00a9100b0340e03051040c001c80440303080c480641002c02d10044c401c1408204803d2920300b1040305c084540f5500401c10300680e03c0890508200c203c00c031142c00f42203070381c200841581007207040c0c40f04805ca005441d010495400185d12400001c05410100e500420301000b9240c040d8440c040014004008002059465102400c501404000d031003842c001105208081d050500850380c4001e841420545981d031203a441c0c4c9514036024120301d4000411001c045020000c492040000c2080304004582700d2600c1c04c0141c0a45009400401c1040d0041c014000d46c400000386914503400211001510342c0302111544008000080810f1402c0c2c0c03200c4e00741c1c1e040c40c60500c02421541e600703900f41e951074508400300303507520041480103001e942d0030a400140541d200381d214059050005106a14081c0c1d508001782282e40103544809856070707a00d0510107246030010211806601c203007032225203012 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 803080053 1250 803078803 803078807
    0x2061312050307120c0f110708150a0e030c01090c0f12030822150e060f0f0709050d0308070f0f05040b090d21140405060307030b13050703090b0a0c 65
    0x1450a4856007401408404145140c0c0640720184400c00410360800050340d010350018400e4110b02c0030800841c40c0301840c10000300010614038151380f072405c028135800d80800000c200900005107800e035016074a05208440d0700c0e00340b0007441700c60501c1001080e0860075081c1a08540f84991140301c0303a00481000b001000d558031032025413690503040c404925510000e20491113080440c0742c14400c000ca1140c2c07420000c11464108862601c1c00d400c02540d56085001075413031038103440c18454045150700103075041d03a402c1c04c010fa0000c80d81c5000d4410b03a9036200803814030b007800e0404a0114200c3e40402c03051076400380d04c0020103084ca00d0103005038144108080c20b6403151b401420f00c2c104000400b4034150300e49180d41032085174407041000e110250303090b0314001c200c420207614001954150f446149880910f066070b098410041c240c529644171020305600810781d1b03102d025081466040450345070030080c490720f03109000d02c1d180858034201920b042003009000071f2078400f40ea49441612201c941d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 803081303 1250 803080053 803080073
    0x40c0311040b012c031212011d04021908100219140a0c050f0a06060f0602070b0901080402040902041109040c050c07031b03050303072a110103020a090915030201020613 74
    0x2803501c510700701c000c4141ca20241070f04c00070b0811580c15104d00d8200c8481c090f80040201442003c11104070856601c42d0300d00400b0300018000e0026100300704003c600545003429000c1d448012007802c900307000e96503401a5003030030070307605a14005d980d020503201d50300d510325101c00801d80d1b40380c644030a903c001d15610b2411800343c0450841009031407603000c82001000c0081228016034a01211a4803040c5c4c504417024100701d000300980e006982900040060001448200b640d19041e805030510142c64011100d0034001041a0780c0551290328600140c0c655105112100a080e90300a03a1551010180400d503034503185500108070080240c9a0b1064001c24820142d17503010444120f11954001102c1e08900941c00c068000e010000502c640e43d508034034060800c000e451040403107407600120b030700c2d4441d002000203080c14840a104c4409980300b81d00070680a455070920241c00f40e00c07001d091040b0f030586000030001c140b01038418019580c041114903481420300c0d180c0c428070380c201c0c1e0b40c401e084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 803082553 1250 803081303 803081327
    0x3061c02031e070b0711010e010f0f0f05191d0a0b04030f050a02060f030901061203021e100207060510090203190906090b09061e0106090e0a0b0405040c0311040b01 72
    0x9110508915003160350140f08002c020110880c880c0d44401003418a9515060308141850100307a04050746c100035400f4402440304451242c480c1d04442c0d01001094a0300344550242c1c104000c1c00b08101e20103140034070340980d444080c603906e10031184000711041e0ac035000000345641c0308010b50b0784100401822002100c0940707038801000c120324842ea2030007528000c0b06c000025400f90340440e0403901041424091032084011354002c1c4091940d50864041c4082ca82c800500181c11002c403210b440304601c40c6880c02d000580085070705107908000c1070400c0341c10103031040301c20a840ea4140442c80e644050500007500b000f680452841c100303400700d0b5110010050b0f180885a445145000922009a0140b58540c4d0008581440c52500781c3c00c150700d6400c11030380c0e221050074416400701d020207210241030507100c80d13450706000035040c4010b0f000e03007242c014403192409441d21105403180c0c9031401640e0280c0d2242070100310303003400c3d49031515041070f00c4402940111301d031100c00c4038036a038842505444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 803083803 1250 803082553 803082583
    0x20010e1b1207030b04051203010302131a09070306062015071404090501170610140d06110a0908030c06010e070c020d050c10091406090a170303061c0203 67
    0x2841448008522072128061001c01c2a0040480020612600e5100719109511030700a640003020850012400c034042800080d4101c00c903480d0b0041d0b0003000c0d9000180007000b40500e87c0040211078001803040342e00b20b42100c0025128001041076070341007a00c1c1605480201d100a842d598035800d9203544040b1505440e15021040f408100460b0150b00308403500540c03081042c3c0d8a6840740c40c4000641401c1c41402148906520b07840040c440218045000d00348007040c83e5420f51a03e64508400303c01012895407001c4a640b1144c0000c0351441160502c100340d41a0b251501920300c005030481c50180c1c00840250070400400e4459200801c5103810764103224030000858640d454115502c11100328001e4021031001d90000501c040081c070115651021604c0080401c3c01501c2107680c0d298600c03c02054a45080d6544030502c0c001001d0203000300b010b003403010030340e40d209442003504408403201141508000300740151410040c03c4c10103a030511902c1c200e207000ba15400f0a076908003c0c0c140d004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 803085053 1250 803083803 803083843
    0x100206010e06061b0a12121e050603010f090c06080609070207061b080d0621050307120507020d0c08070f0e06010c02010504152d08040807060b0a0620010e 68
    0x6030144c0450300b00160400c03502111980001c80c83c104d00c01c120b082c0c0d20700000c01c06c44200f14410083c1405030901c1f400b80c8944045440c10300810260280101520443e032554030355400380c0d240a103504c908803031107000c0c0402e001d03024038246c8081e1504101900240c00b41c08180d00b00280c854000500030b0071180c9030b140c80420b4080801d61820a00304208008101c0600081c00f0503c03120070b6000b4100307a5080d4241b8541a0340c600d80c0398020010b8030700005186401c00d100ca04c000c2441c1880c0c3d8a002c20950400f680342081e1a4001040c001980d202280c5034001a10b0500c89000100314000281c610752141124150030500d820ba50110000d040c9810001c0c29040c7c41c04592040c4240c1d0010705906504114181c1002000340480c00500c0c564544c41e0100b008407180d1141003054044000c0d0780c2e8540d4045600e403600c50040a0740039000c00c2d0303009a02d031582118a41c69001d080f50040a05503200120b20000c5601420000190503075400b07641e04007001144074100c0800c40310003154484421340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 803086303 1250 803085053 803085067
    0x2070b1306150b1c060810020f0f0c0303040b0603011e0e120f0d0b0f061606091205040e090c0f1908010516020f12090402030a09020301060b09100206010e0606 70
    0x34040c01c0e4540b080307024910082000601c0a0300c0c0d0028107134803451904030b542180c500c200e001c41118424401c3c11101e9010b000070801c00203081e0b0003031480c10700c0482524500084060030000645c0301c2c4064400e203520010800050161305004650020811002440400307003a031528248440095158100203940d50404412100d08000f020118070010320015203c150a00780d2188a410140740e4494250511801c0350851414500c58042d0b0100242228201001901c0490741100106011112140d844034020302203000541405004101ea40c1c91307590319820320400c600400c030003030201181644102e800c0c21080c0c2c1c41c00a00d40c0200c20550303802d40403022070100c6804012155003c0300305946880b050080308a50381c08049030340001902102c15001e000c07000c05035900300258800170080024040c1165170324040e0021a00130080e01c0b07000ca0342e502c0c04c0c0c00203801c40315103500021581e400050300c0391150030003e080305455481400504011f61418800c0e5048610080c0720070300c100400a150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 803087553 1250 803086303 803086313
    0xc0203130803091f020c030f07170f15070909090f0309270b06090a090b1807020c060904140f010303120b0a0b0703050c07080a0b180307060905030d14011802070b13 72
    0x386458030001012540388230030148032161aa050382c02200c040010341c00c9040034240000642c01d201030140704c01002e146c9440c0009500448001e00443e0803c4020107000550420324000c86d039030030b8003883c4125081c41061501600a07181c5a021060759020346c005000c1c107521f40440031440e1383e191040402c2da010b804000494610a201c01c3c0d5a00c51408603010075036106540c449600c43c0020f4a4040c0c1d0103004d0702d400c1c11086c808540040059020000502c26810a08040d0500c02e50140c404216031403101002c20a10724200c400e50812841000100700381039000c1580543c4100c80d00c000c000010101010a1060b4000d00561400c6000050f420007054400c07412a0b0440010340700340c4000a0711842241e07150b60b0110b0381a5244240f51021488030901c522461408840c82e000840c0750144135508c0c440a40b00b1003a050b5090b000a00581e00800c020380504014105404c502007559810011420034218032103600c0f4601501c18454a00018134200045401030f640800720000d54006180c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 803088803 1250 803087553 803087563
    0x1205061c150906060906080c0604120302100e1b040e0c1e0a0b1207030b100c02030109080313060e07050306060d05031903020a0f0c05032208010c0203130803091f02 72
    0x281c1051511004405200c10b9070b1000095620b4050107000e003030b507070f4404203549000804615500440c1000308104145010040c07000c03841c0b00c1e0040d16840c080f403284a00071903140842c1d90703829400916501e045441e10500e81c0c800408126420081ca500c0b40e400c0e00d0751090041c101ea0301540b000e800007405000005000c04007050000c05206499031200d45243c1c090b04100b266640c0c8074101000b08801034041c1c05012900032000e02942e40d000749040c000c4070008104501613826540c1c8150510200d582140113520503201094a07104e00c04e000c2c5030000407030701008202c5c407840d007001d5014000c1d554045641504494101c5020328800b00301e0416a040d0b20840516155054058043d500841d8040c0c001d0000386455448a20340a00118030075139803a441c440c80103009400407c540003010749000c1d060108074140c8501e0004150b00d4001442c00c44240380038aa02691000c00c400c07100f4000307560f0365130240241c80095410015944041145107919583c0032401c90050b2840303401051007001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 803090053 1250 803088803 803088833
    0x60c03280603060c021207050a02270114031e070b090109080609010c1d09041e02090903030603070b120a09030302070506070809011104230d150c1205061c 68
    0x100a126602e1400100030901804d221001d80600340745907004122034000d4508907500800030300361010300c0d41d0030419180d00140b2100400740d11900e1640310724203103000381c41c043d00c00380b01c04d1404540a070040500d40b03550130360100e000607090403241c60a560301061400071110224103940e2584910b43c0141c5001503a41c02520385886086c00700544580705400078104070645444600c450142000074641c10301d4540f100030780089400e00031400140340300480705080340c411560a1207801c0140e00203800d800007654000a45e500101c244807140c40d080c4602002051841c100c6c5151007040e400754454450010101070344541d442e43d801c0c09140c00381d01210a6264030005442840c0340080011b0010340e0195810b6941e50700c1d11141c0000380b01250f04580c02d0324004440600e0380340c039421040c0800c080c8040005e07046040310086100052810038400c440c40d80c41180480e141420500080003948180300c0307078000b02d0901051002c10f072507030224a01180741030480305820364014207242c442140150 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 803091303 1250 803090053 803090131
    0x150f0907050f07060f110903030703121d0c10020c030736020319020406020a060f11040b0307030c08012418141203040f2616090509060c03 61
    0xf41c41d808010003540640940c005080d402c200c014650703044424a80608a44a50168010000c04000c80d001e64407900959841c19008100050807080209030415000324401d0164001054089a0f2401241641c07907031450b407006107070302059040020313940c1c0003911403480402c607600310071070010b90554a4bc46c04c5070b80174144504090b01303000d001c500071342c41120491080c404103030788510700d030000d0300856086940c103a004240c0c04040d512100000e0410003040d1003059941d0003400022400480900002d102200505e500e80c5041300700502a1800d04001204114480c40140403440240840d500c40903080c5100c4145900110703010f503003414805101855000c100746d4006000011098020003000301644c0280c0c00e5003034221f504d690b90040c3d01030500d04a9100005001c4140b040c5029044142000070001080480c03008403402c02440c1c11001900c0d00c0c1030181400142c00d10b00460390031000c05c0f0014502450070f1407a110720b03070002610310440c2500e100c0c0e5088a00c460314149003640c48080c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 803092553 1250 803091303 803091307
    0x906040f150c080618040b06100507020d050d17060a1205010902031501090e010b03060601031e05010906050a0e04030e0f0d0c0e01030b070503010f211a0103030206150f0907050f 78
    0xa0b01c010740918070440f9400c1c4509500c405545002241c03901590141e40c0c0411403250548403103040107802d0000c0d81a00042000030702503000965104d04051071840d01601c0501090114205c00a015022840c0844000403000f82400200d031904030950003210113410b00364003000002d1a0283c00f60841150181d458816200c08800d4841030000b42412034070000f070100580c100001c040e900365035000342c4003075054104c0400203420794065048240d1002c0c0d004c0d002026900362001400440d00300703030401035050340c1c3ca4906000c4c03414820082c001400403125010050300d003d590040401000100f09030007100e0761003003001e664669018558095601ca400c10140c00c3e03d038401070b0350b08442480b05031108190200402e051901403411281038030109544040268280560510700191004140a41e50000081400811401510b01011982c0c01750092010f5265041c020b141500240400a804903039a0707008005547e1008041882542515549d5443c0e46a40c408c0d940d5024403100040314000c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 803093803 1250 803092553 803092571
    0xa090909030306090e010507080a14041e050d0201020306130605030c012a14010513050d142709060301180204091a0f041b03121b080406090905010e0906040f15 70
    0x2040d00701f9881aa65a41c03400300700da6620000c8010f850142615145a0704200003160114540c0c42c1e249100b01c100360524500320700a0b0b900d9a00d080032140c3c0c03800040c1d501000f44006403500c00801c041d040420340c410302060742414002500c8801480d42030b4180500c05101645401031411300c8414101a81124545a840c0707062a4803a0382402d100e4003115407802c80021900740703081c880c140c170b6540c00c14000c08900359080000d075030707074030b000001d190031000140850100d2076681d0003005104c25035500104500c401c52000c0c0100020083d2419109904061a0b00702d41d0200d050804c000340d804460104040d0700740e052400c91002500094150201daa03020040702544000460f8002d52017554625002d120740001000341c80305c1c0d80802031925041440c4c000300c0d40d124a80b1410b07405030000c24806032200035690410194070591024000c40c0c05003004214110803842040c0c010407502c1da5808051806c0c1d1072003910b811005100600369403c0214020504c860206d10050391518880c00b0082121 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 803095053 1250 803093803 803093831
    0x308061c02091006090902030c091003090605040f05300706090503030f1902031504020a02011530051203041502040909060606021617030c0a080c060c0a09090903030609 74
    0xc0140a40c4c00400c450802c0010990141c3c07003140c1c82854070120050900d06503004000d46003840401e118205a25000c00c3c40209280c4d10440d80120310400000078804824682141031501c954140d07808803030340c80c01c44185015110f4840c68141900c5144568940a52408000625543c0c81c040d00034030000c0308010504060249090046101e104070a2150004414583c283d1104803080e900c2d11110182d4152542400e80203000b4540050001207080364903400f8000204150380d1003a0740da030513000d80884102600342c2a0004000758200b0b100a100c02c40d440302c541e950082c4040c220f85c0c6400000240070f00c031482c00411950741c46003d0079941e440c0c0d5400440040c0c4104142515458548031002a80034000682c040c0c68001503060762039114a40f1030003000003154007845c652203010422080c962042d0500c41c000e04c0510481c1c0050725803668400b89450014000c01000440074100200001640c1220f1110121402460041003e10080c54100c020f0180c80d4005001c4608050010b03044003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 803096303 1250 803095053 803095081
    0x1603110d02040f0b040f140f10021e0c06091302041a0901141810090b12041130030423040510051003023702070e01030308061c0209 58
    0x68019a00c0456031030f1a140c4034803851240e8806c501614214000030091209a282c10756a5400001c18582105180c940810190ba402d00300d1140181c0120300380780110802040d816022180c03041c0200300e00070100c0702255040c401c00c800d00b441034611040109203008160111030140080340142066811a42070005550708000511400310f07103009500c003840383d01c2105503000904081101403c09940f47c080c49007040365440e0f004204802d43d440810683c44032402082c019540380c210041901c0d05042c6041049446000c1030701c5404075184220b10300c05403445410800726400c1d00c1140b07082604454038170718811a4040c802070500d19200f0320b03820070035041c01e4000d10010b49082c07015a607580e456110b45003c50280720b920004821004403c10320075400385c40c078400d0b803c1e6002240040c3c0040d018280d2400d10452160500401810311165414006070b0010304d5806000c074000c0d411950083c002900042c8494011024901ea40c0c211240601031300b5200d617001f405403201401d020030941710301c1d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 803097553 1250 803096303 803096309
    0x40809101107090213150201060b160c09020f0a0f020705031c0215010f120204020d18050706030212070e0d12020309030c0102300c030f0301090f0e061603110d0204 72
    0xd00484400183c100c015001301c801ca520042c0c4c0340040c545c100b07111200c503004d0710396640045650701c0c2408518105030320002c0048501c0042c0031034500a40c2c0c584140c03608655004000468014465486a0389003903056034083d010f2801c4c581034103403e8242c200c0c5401d00541c851581031140440031501c0c805003a901500d03a80003907081c0e80303181c0800400f2801d151420700c10705030075030b40280c0200802c641d80e10610940030b100030070141c588040d183c0c00505031443d5424034406d1484516640f0b0801c0340c100706400040c60b0030308080d03050407511440e815007454000c2408007444100c041d0115142d5452039413500041c0d00031a4040f0314224088020360b00c0e01301d002014040e11500206a10560000031417504020908001074008002c0415201a400008040103a4031000340588964084288003402e10b021040d0466603c1e58904460b07082960440c041e0544c01618214020f81907034400704505600ca40c0d405608040462103281c00c8000b044040390840f01d43d0b0000c2182c1c0c1885900e44c00600803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 803098803 1250 803097553 803097587
    0x10905062d030c180409020a1a0d020f0a020118151a0d0c0501031d07181812080f061020070e040b0108010606050a0309020102010b0409030507020405160e01030504080910 75
    0x101800d440c00c0c0806c58060440c040e43c4103002103400c0041d14848441c00b107408203103242003800c0952021102c0103030b0300490305018040b10003080701e550b526030900c109969541d99101c5115042125140d0001c001003103604d8000ca00d48070300d02c1044d04880b4840e186072901d800b41070801d00203a1418040c214112034000d8500090500046c0e0104002249005440d94012009006214501034a02c004000c1c40c8505c481029241d045114084900040703040e125801004200c0411000b0341004090800007005880304078030901c00c1c014580c9600c3c00509800009051150703040600303840384c0b4a0b0303d000110003800c1c1d1288160200e140d17102804058000c6119041440c041e9884907e0701d42a111180108000070f031081c4071b4094602d00c81d0700180c0d00f040c0103000006120690f90081410b0700c64141060f0042000000e40108600341403040f1603100c1e00302e0b40d040380102400e01c4010286841542a01d04043d1118042000d01c108081102c1401f5030080c0760310f81d00e80e074001001e0000788404081c12a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 803100053 1250 803098803 803098837
    0x181203020306100305060312130f06050301170601061b03030f18060506040c0c121103030703051603110d09172d1602090a1d1605010905062d030c 64
    0x142c042e0017030150707030300982008001c1c181c0c2140300341c060300d80c03900700424000a00b007001000003100440100f0540141507583e45290341c0b0342c140028000c0e01d014110840042e503000000402a41d07901811410700da036106903c260040c0c01c40d040403005403000c01c1c0640302a529010340031b040c40c030160301300745041c0303218810500240c0d44010400007203490b42150b00703000c16601c0120600094802c40740401140c083d050601c0c0c141d20048540785103170003c9690f0000b280d6a1818001e032401420b100c1d05020b401e40c6018800001070310075524882c000d1301207410941da01ca06410341000342da806608110441d0300c0031b0a444c2e140b0340480d1490001102841e0b80f00240011a5000d488050011103110780c030340b6402904910a25400d010b80c1400040140b481c407580c0d9034814080b4010522000c212000001c01000107066414500f50002c1081d849207043c012507030010403042d00d84400362400141d036050380d455458019446e46110100c03c565400c8a080700008000d40070b00c1e0700b400342a98403043c0740c41e21 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 803101303 1250 803100053 803100079
    0x108480a0803090a0504050c0712030b0a0b0306100e010c1401021206060408060f1905100e07020a031b02040b06030408130504020703270807030302070512150a181203020306 76
    0x160300c1e031007100e03c15a044010b05a080c0060b0809030003041d0040d00e0842c54500d0b01880ba01c558074200310501240b0300103600d030000b81a5501e4550f0040c80a08107c0a00518600b800d400055017000c3d042c0300311050180c559110b514aa001d50030540c0c4081e00a45541302e41c82c91141c03e14004d6001042c1a01d015481e000800c2d16820403001b51401e444552009210380c2e103032610311421100f4003c02c28101e0a010100c091f0350034405010b140c0c02160b503100116580c0c1c1c2000e030041c49904d4024014411503021800e1301011030350180b501c030700c0c40c511156041580c13003081c0042000340942e2580340b40c0000b000418401000114002001c424000c0282d01700c40700d0300d403030401051b4410103001500240d040306c00d21403050b448182450f02c5100c25019000340366911605503040c0400d83c1c2c01540541c0180d4020462400c1072002211607807840005000c1c18080c1d000c0b8102a4400542503082544ea542135401f98030600540c01e610080c1c210302400c680c60600e82c0d00401035802103484a0040c0382000c100703 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 803102553 1250 803101303 803101319
    0xa060609050705040b0d110409150b0a0906081915060305070905280302090a0b010e030118081b07180e0d021f02040f0b03100602060108480a 62
    0x15001da940c0f40e545a10b0b043c600b010075041a00a025070100d0310790364451403060050000004c00040c1000c500120309203108698440000410b50300981541000b00228000c1c1a4080b01d0081a60300c40d0410354030a44a010010540b0900a0b0300d030b012540c03900c15a10b04850905280030b08544e920354062295940d1800c044400522900c1196013280038848110f0394100c40e03ca60070303400c6075064041c800b019034a4000504611007601c1208110350b851504101550b400b102c07072600d8140c294028015016201d11000f1240200b020240c80250040750400c801d00b210000d02003000301c0d15045a078960785810340390311f0301c1d121540c0c030260551030031400c0d19503040c012a801080d4311258000c1c200011400702c4104540c0705210f1004e200b80c1d800c010108031840c000813030b5406041030f0700c0075640303130300e042200d10b402c00301c0329000030041d58007175070041000c00800200040c503825048900011121420f1090015414507590000100145107000005034280e0600b04000742080342d1540a02d582c1d0048 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 803103803 1250 803102553 803102561
    0xc02031c060807120b040b151503151c02010536010f020a2003010605030a06090b090f0316020109030210020610290705150712060b0309030a0e01031d0a060609 70
    0x4000d05a85c1142c00042c0800c034074000d19503110f03020405900d01c03002500009100301c1164411800000ca0100c2440001008c2900d440c00303642d4140c806240b101990002038280c07000c804002410031000040c44180300110461000034203080b40c0c0d04c080082c442a95001080001c0121540003078018240d00040a00c0040c120362016041386018041840d200400f0140d080000003040d01592100030001d46500c00300b03c44602140107600020700d61405141c2250600f401401c1614294000024504042000702c11122061001541c2000107400c0e0710040e20290310300c2d030010b540505a0b0002c100c54076008500540704001c88000030100382d45814110480007625049410400c940d0417003103400300ea41c0b1004250352800b444c00c440d0700c86055010182d0110307048501300c0c00599980340d040100207e50148502900031001201d05514001c1d112554034001c0c2c2400c01c0400c00842c03950001d59000341c1c040000ca41840c03900c603802000c9181640d0b40c03502c1810049410500d0b10790000792021682c0301d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 803105053 1250 803103803 803103839
    0x306070e0f0405090708100b030615011209020f090103030203120a06290c030406122007020103090c180e0f010b06030414030d02030a0608010c02070b0d0c02031c060807 74
    0x11400c9101d42a4005110081500a055190340c1c4603643c1c0108200038200440c00341e1a45902010a0000e12001814200000500020880d040541c444841c50381c104d485100221801d20780060135465070700004000100319011755801a180400200905902000401c10f900a42c0240403080d107030030403034104484070344c850041d0403040041030b55510003a0f80e92540420310b072002440d01713200a2802d5681140d209502680200380500100003d0a0780741c0a1440c0a500c08a502664180180c2d904401e510448400074101a44c2c1c0c14100704215445c200c5002030007143d42400f4200a440103180020a100ca00b0000588289042c40c80c02400500034001e9690006d4501825521941e90301d071500c0c1622030416509000900c096000d5420070700c0590721134409020003080b641c0c50b088500f03084503c1d81003440115080352070700b80100300e003081c101d51458010500000300d804407001c08078114001c440344d40c138103d0301001d001038803201c070f581142e0103481c02c41d0107980d503069860761711080b03041a1350 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 803106303 1250 803105053 803105059
    0x20d2901031e050c09011d07080403020304140303070501050a0c0306050609030d030c0921060c0513060509010c020a030c03050f0607170a180b042303040e04050a02090c090306070e 79
    0x40002140c660709800c00340c4020310900850713116010800004040380380c2600300c2204600d4085104c038207596514545a0030401e241458140750a103510f00a44912441c0200c494a41c4c00d150603694a8604008440c1d0130354100e00200700905004280d00c002e0540425403000203070911002007060b15102c01140c0c00c1c42c1d0003c00401030310002210503006440b1071800c8204bc09000c42000031400c004800c401301c43c07e64445180e03592403c51402804894070004c840d001c2003c1130090300c0d00d4070446880541500c200717007030458541000382c0040700d1003e0f210600a4100d41c8030000002009174a90303030384050303d219009a0340b2900d80c521000d83e072103504a031414001401040c00707808000013100d100380c0080c40540d02280315080d03403824150559600e102150480d5a06003000184080c100c0351101000c801e500021441c41801c0e102552802503000d03401201c4560340110301040001c0000b240255070141c64a076141c03810da6a04005038002d1400c246c042c0c040c2c1c000007003030076104d4090004038039001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 803107553 1250 803106303 803106323
    0x6010b0c100b061c0e0d0906020a030e210a05011d06040f0203070306050702030a09091803120605041e060501230706200a0311090102031e07020d290103 67
    0xc0c40200090926070442c160421010400c55164242c2d50000400090100c0c4000c03494540103000c05151a840218020411240c3d103010700c061540481c40f035400c59014606001c008441000081c0c800c400e0303445403d40d89183e048034060300c02002ca02c0c0c4928a000b54000c002001d080c0764903480c400c03c2c0720f000e907095821a100140010b1340c0442e40d00d035121f0000e4201c43c40c2c181c0f665121821207105444400141e84042241c0107299402108a0050f059044080c40746031071000f480f1b00340d00070700c032002001e01140c05040c2400005651001006000051080c40014000100301c213419000485240302d103400e15501240c25402054502c0c4d0032050400d070b41c45101d83d8690000a144c000030412140302d41c841090a440700c10b90880643c01140031101d40f41d940c15680d81c007604a904404c1d131541c50400c10b22219070307981c2e00441621401c41221080b80d189412404c505855445480b9009520024083d140c00510180101501000c810080c7e082c0142405d40c0700501070000c00d110082030fa60072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 803108803 1250 803107553 803107573
    0xb0a052b0b01090b34020a090b041b050412030e0a0605070b01060207210f0c1710090206070602030426030115031a040b0a0f080a02090c030c0a18030204090506010806010b0c 76
    0x5415040c41503c144500780603900c405d00d900013040c800d40c641c08a0785036921140401081d1800344075140c1081d1405499026008020030081c0c02c0d8003692180e0001c003210b1085007410705000e05644032603508001d04050849d501c541020f01980c0000300300744c40110040d000820300d1400015a641a1070a02100d28100201c5640003128882030304030480710055a009400d00042200d04d440d000340000c0303a002c0c5a0a8511a040e91a03e540403d88042260a26803054003584035a0202c030300298000e080541d40790b80e1801c02c800908140c40c0e081c06070302034800c032155082e40890090350603a000ea10150100c208020340441c142e49018596240c2ca02030000d12001c10f1801e80d10004003104043d00d0715403140d1781c6510704202c1079020303400b08400d604040380e00300440c60035156541c1d105034046103440c2903080101c106900c0d80541d86210040c440c00805080340803500c40230380c800856000b002031121903000d180060710b82c0c6007032051104910585001040300f0030030400380c0f02d9205100c0010590402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 803110053 1250 803108803 803108857
    0xa091a0c012f0304030c05010c020a02040b0a06051605030405150306010e2b062705060a02070c090504080906030a02090109051f0302090d020d03020a0c0b040b0a052b0b01090b 77
    0xf02c05402202445211400100080ea082c0580b503281c14441d00506000e52036030040c803060f10302c4009220310034000d10000b80641e80e085001e030780a455049280311240300c0035140c814a5407145400285c1d1203000c210004603185283c10003144180d1081c0d0b030b00ba00403a1034a061150b0030000307000340000c000203000341005031110350415201c0030f8010300b008981088102c0c100310074482414003482100950b90040b8040c483c0070003001c6c1e00702c3e4800c4011860710080d5160040325445500445501c95107801c041803e00852030305440402100400300360b0b81c1d00b06481c401c0000c0d40b00e26130107030205004040010b501d10b040b28032442480d03a1500c289000701000402100254070203201c0580c4550721005003400b60f10b50201d0b51340c00c41d10903002418580d039113003814502c0303d03090f40c09952951304c10031061110702825410381c0c503c83c40710b08015072181c0a450420402e902010514980f811916140d88900d85460300081c07254102a211501107944a2450054900c0344680026050380c0344080030407414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 803111303 1250 803110053 803110057
    0x4060e0303011d040f0b010f0929060d06030b15121506060a0207150903051009020312030901020d050c0306100806031504051f02030703060b070f080a091a0c012f 71
    0x603200da089507041710019034030070180300300070f030401d600306540f14405100b4001c00348114012450002400c41d1818401d01440845d44101821a4050f51000c14a40400d2a0382d4002202071640003a07100028600030201c1055104282005441a2080401694800c101103070f10381b00a04400884051b9558000a01000d0703130009812104506c1030b0103002840381151045007401400e81d0b9100c044051650070410300d0710180c000d4075000c040c503000304880165000180280100c0b44100850b440303a440301100c600901481a600404071f0815080114400b0840002c0d8843c20044540304030f6041cac4900125201030088400580550004001d4a0600844052640d00904c5034003290103000401c010080c2c85580310b005407113119004003d10050342c0d0580284006003540441c202e04000c1c2071b072030b4a207580b02036140c017504c40400003800e201428454003003c4080c1412003007010801e0b002c80ba0b80d00d6103520440110103203500c1c11010034107500c88a8440e207840201c0d11034485e20440481d400042c55 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 803112553 1250 803111303 803111311
    0xa15060f020709051b070f0311060f07032307030902030607055701060617040b091e030904050a0219050c011506020105040209010e09030a11071d04060e0303011d 71
    0x86014030180f17a900c1c501000305413185c81f03240000e4414a00e498007500c01c0c910b80003003459503040308041084009482e244580e1103e04c030320b00812904100010608030964000b41c4413000b50120040246140d059004440181d109500300d0300d049c0d82e0408100d901e0300030a007802a4409550424010b81c0090600c49161042c86000c09002d10f580c1d68030200940b06001d40c41c2280034018070b80355040102c00c0c070902000300b8031406c10000050800040300c3c00c522006100403d54044400800c0c03500e0700820981c208054100e00c1503182c010795801e19030750781d000f00b5902d502c26800d100014581c460700c3c0c000e54180d0345411011000303c0c4241181a02d068020b0703424604c5035940e42c240c540b50700e12507480070030080000b50000200c42c01d280c0180148800c058101800b5040ca480600111600000844615103101d00d4480c4032505091829414000654000416082c000c40d4070703501840d00e1020613018074464074080000c04080044d03644c480c0001d00c075040e540b204030208051140c02440c409988 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 803113803 1250 803112553 803112571
    0x3050607110601230f2e02010207021003090311030a02070801060f03020f09040314040905040204050a0e1b030304050405090d0216050a0e0403050c010c031a0904111c0b0a15060f02070905 82
    0x120301c40804c1404000440302e991003481c10141d500c900d00b601002c03010002c1c16200944c80c0404ac0d40201d0380010200d00e404c030030596100325203c00d01d07102c1d5011107100c4411806aa035a040030740c1d4000c1d581c4003103004814081d403815400007480300c000300c1001c080341c1c0c0c003805194101c0551410080e10600081c400c4d024884074000c00c104945903180140043e029043c1d000550342054014030046980040c0f0245030b0500c1c0c10000c00300c4d850700161007d001c4616451440c1c1c0c02a152000c2030644c000c9500103500641000203000c00d40f480490148400c8041d94215a02c40e02c460443c0e004500a610620b600003402c44000e225224908010b04e500c07501a052542c0742038001200c0c682140c00310706400c00000d94600024000540380b1808001c112003ca91035a414101621500d44d41b01002180d41d00c5503c01c12504031100024464050080e81c0181680c055464403802c078601908003481e41c481c107541c0300d0201088140c00703150340365030050042e40207005803820030000500901380940030b918 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 803115053 1250 803113803 803113819
    0x908120c0f0706020a03030c0221130905040f02040506010f0c110109150f1b021c1e050705190608130c05190e090c030d05160204060305060711060123 66
    0x4512000b000a0300040031194024654802c0c2414000c0850303c00410800454001c0044d07038940d1224039061503082c001c0aa8816643c5420201c2201425403988c01840f06a092808000900442040928500d80280e0f0144406d0343d59000442c0d1190025000101103039203020704101017825001c0c4000d04444c1818441500c0380c6405031035008140b0072409100003030000a000320030981c0701e842c5130720300f9201005200c149142c0754005002984010159005160380c007107404240903c24001504584c140c05e8107110343c041d0340c10083c0c0c0300c80c0c1500855001d4030300a05842c0c280050700000c00c040312543d80c0e416038a91141c14031b203003180d021894182e0380c904c9a8035000c00e03150f403076803150032482c1d8003400c0121459180240d80000108024850140c6030407296000e0001d13200400d80341005481481e0003a505c5030102c00f2125410050540a0341041c90503a0100400800183c41e134010350041d15151182c035242c0400603a44e40c0b0901501c826500740e44004082184142d019000034000200091 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 803116303 1250 803115053 803115073
    0x40b090a02060c01020a020705060f1804090206043b0402040902010c120f1e050909040623180d0f0e150a02010c110c0a0e15030106060206070f0908120c 67
    0x1811a0f00b00b0340b000d01c100d03580040c546504580400c894802000190381e00c41c24408003201d249030f075006441c0d0320200b40c1d643c0800c040e12583c903680301030f42c2550300800329516035031a6140341c00d009a00300e60402c0e00958100030740c0b828190011081032050b4800f1b0701e0405560707075035013800080c10080303504a040c082551019800100e01c10071144007803075550354600510b0108140208050900c41302007000c0d94401ca0070f541d8441c0c0c4007040b2881c280050301e900e82540c64901d020070040c24080b414190902004070800c0c102035103c2c4c1a24020119900241c5017031403002c0005448030542800a0b001c545443d45a2114a000ba500342a4000005181103d16004880140070b240e0004042070300603590b9401101c00c854019011161101c1c5003001840c090400e000410310f888100c0c000e09851095440c0081d00b060f1311002443d00c0100003400034013203540d131804007960f10b41061328044040b03007481c002c01c4004d80c801d4808000b00d4076400e0041000d00c10154040d0040d5000c41c0c040a01c6000e001044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 803117553 1250 803116303 803116309
    0x20a1121100c090e010e0109051902072001031a1003140f070206091b060d06031b14030f0601090e030c160f0e011215020c0a08070618020306040b090a02 67
    0xa110301d2103110004188282c44080090040403d6048205009104030050100306c1840f81040d05540d8184400110341d200d00601503c4031080e07202e544411400001c4000821160342c84000016820741400c407408c01e420401134056560039500740900c0c502c60500e507184c030b00d04409040d26101e194200000c1c2803032424240751040d807049840b1441c0b207030814140400a5410811280d111120102500e094054585c600070700b000c24171817540c841e200205401c203035007405910080007075074054500e9100660541580030340e10640d100c3d0303014030300c400e1041c81164140410030004078034100300907208a07820a03080b040240070100b986c085920050140b0030543d84100070034040e10520440d440603580c41c01c0150001e40c1025045030510300d4507000100084001603000302c0702c00354440424809000f281c4c80d440000e000302c0302a01002c0c1700e90b840d48803e01ca08080203141c0706001d10024409441011000c408414000b080250542d010705e00080118145440309900a202c070400d0b07403003d24983e000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 803118803 1250 803117553 803117563
    0x90513060b0a170c130216030f170f070e040b131e02120a0b0a0317090d1205041404050c0f0c0f242a070302030f040602010204050a06020a1121 63
    0x203010b4030740c02038807010050b140c100034485c4091610541075240444042114880d4107010710001c051000303400b164240c2c41d0080d07420140b103010720364000340540b502000308a200c03481500e800700030403550b0f410074595052901419411042c0036050005030042103408000402e12220140a0561f2040382c0104002c01400180410601150401e03141d04000382031400300c0d101940224071510851008000040445c0d140c0c84c00b4025481005881d21090004112050305586006003100480c143d10018250400054825591454640703542c0c82c1b440001e0104442e0140c4006100140511224080100b1740004204541c0d280c0d06543c0c80b00f2008403803619000729100031380511601d8002124100f149015000d0388070440020640c101c21003007060000040c031003803100f25400d000040304010b040c0204203c0f02d11914050680350303110350350403000f8000d401502802c0c0c4607201411000031001d00c00640c000c03041341c100c1506007840f14400f04000c41421041d40304820340800f1000710b0501d042c1440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 803120053 1250 803118803 803118839
    0xe060d0c020a0302071403060c030402010516140705030609032d0313061103060a030201110a23010518030415030f0504150c05070f020409170f13090513060b0a 70
    0x10451400d0341e150282c01e01e405038114840b40c5d80406031b120f802d070390000740301030300030401041d042e40da5101e07400100c80501c0382c1d42040b214040d05500810401503228100090554840140d0f1440c9850740109a02c2d6101500e41034450b50090185640003140781c2c620000b0300c090164008416542c4844071010341d0003c0b5008803003481c0403050401030103501d0249924502d2100e40036032035881e04030001780c07001d002404060704014600c3c1d4240700c02481084003d40c119040000700c013911100010780c1c1c040b0111078140d00307980d50929010070409030003a80b29a9840d0f4507071000d03504250420801c484071800f01400b41c01090b80301c040406540c0c0341480b403140a2801510390060304907840e0140030a44014156040401ca0b08104200200340424910301481d64102c5002c209803549041c68601604400d4101c8045400000c042e103c0b940640c00401c007454070060130014496840c6028800c449041b200c405010b48200094000070311030b82d21a00c1c11450090040d8102510764a84421540b5121 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 803121303 1250 803120053 803120057
    0x70f0e070201051005010503160e0a29070317040602041802180907122c0a03080603011802240409020a080a051302191a03071107150e060d0c 62
    0x80500040560a0055a038041200a620700345203150000007489072000038040b030718450740f100200c0100d6215111205034071100070043d560750354980f42c4148001001c800784002d010f41060401600302088410790341d407a070309900c031020b20100610500450141c0100100e0728194204404116460070319441c0602c03030103680700140c8800f140e000007070b0b00078030108000b446070240758104403000e170740000e92982e440000040440c8100d80014104110120302c801c04408101c1480031080d400700008a4284190082d660b845040d00d508090500300c441c044401c80502c40920340c0301016040080085005449101607070319241c4d0b81801d4020140c01540013a040c01d0b4001401001141d0710029168210764408001c2010b82880b003a4681e142901d00402406010001c503080b80419105d00f1000040c10100300c520040c1c4030b08801c500c803680c03003203035440c01040c3c11000110740d84400003840342c1540c002d050602e0001c00c41c15016207010301c0d001c0c84a54403c02c01c100c4038401c40f100d409400c8a00080e0303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 803122553 1250 803121303 803121329
    0x151b03070c03020c03070f050f010c0c1e12050a0204020a02030c0a0c06030c090b040911130b071e0f11120708030309070611030a05030703270b0703141602070f 70
    0x40c07034001d0410400d44c0b2160312a5000304024464041441c1c541c408403032046a4007800c6900410043e242a01e000760094410308022100080c452420064160840d071340da18282d00013605d401d550007580031817900140c0076900c21148a001030805034000c003004205801100d04003a01c0c8440a0314012040004450300424044100901509801184080c0d40c6500705000a070b8101090380c40c0e680640c0c030441501646070b1f40d03000454070100e1704849580000e89010031035541c8502d240c2c0c040d0f500600b000c40e40b001d4890403851021609020010030240e00410796200003110340c0390446141000318416510560303084200b0b901c214200180c4005040d40c001a54403032408100c1c4a081074120f90010302441001c600c500075075000407084070805422030901c181c0f0380d03c1e00796045008007003414101058000010903002d00c1080450400c0080c0d1044080c4c00c0c01da074030503100324142d0303c10103d0000740711801408078118040c03030814540030010510450b2640b80d50381001603a180707070b5944000801b40c04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 803123803 1250 803122553 803122577
    0x409061e1b08040f021807081005042c010213080a0b09070501050d0c090f030f0b010b090d0204020c0c041b090f1503050a2d1409151b0307 61
    0x12a00604018005800c1e1480300e26000d410003030318610000704028600c1d20300a0314001107503120600071901c8841800c00c00524a008580a80702030030030f40d030030003030300c4100103001401d89010b01138403080c2c4410350101e08a5412403400ca4480c8a07882c440307120700d5502070207944040c61a141100300200501401090b52070706509003642448000762850460342c10018090000780d0300981103d40d0250030507000035480f42d551b041116170101a07080403c6d0b0300b003550000401d10a1505035071140c140601c2880b10282d0760f85444100078418a441c0507003016100002c5005481c1aa02a143c00d407a14030941c1c40c0c10091400240868502ca5070004070582c2515040d86926031005244001d4180c1004507180c6a060001442c0002c400f92005000c058881c800502150120b400c92410f000c1404e0300d40003011034442c0e6070b6103801243c0150100300c0b4580312010900100c8144001d0241e802d0401420b511460700c0e5203480e031820010010146003603940046500750b20841c0040d40f0030400c6d07a8034000c0c4404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 803125053 1250 803123803 803123861
    0x8041a13170301050a0501180509010e09100608330c0712020a0b0f150306070f1103071e0c170d1403061011070503010e0d1b050a020d02040906 63
    0xa601d49001000300c01400103000c15110b220408068410900b03000094203d42c00c0d80c1c6680a845421054000d00024000281e43c041d03a035103c4d0007030110000ba00d0001c60300c0b140f0390048a980d8401c00034035610140303507405200842d800c010001c4000d0198016604c013001961109a51305480001844200050205c00c0c4085407911110781100c5101404441c0700a841b010b201c598007a00d9615818429404600c0c1d40d0f0303070038949416410b40502076805924080718017600351624425140c0100d1a80e4641203e17450010080302c4499030302c65a403400301c548940c1c80c05200c8049081c00c40d80711420346c030b0204030801c0050070800500301910007880c030649071a000800b100b04103030400708030300014402c0c003c2c07941d6040c0d40864001510f14000b880c0714125498140b51001a0348455015464100000003c0f140842c847c284140c15484a20300c0c2103080109040035611268041c1c1160064140710005243ca0980c015030399000030004908103034507441d0350044820f42d45d2145260003c0d2209501014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 803126303 1250 803125053 803125073
    0x60812040807060c0f0b06060c1c26010b0f091203040807090c0516031b030914010503040305040e060402090402041d070e0d0b0919140705031c08041a13 67
    0x4400c529002101c008113584040078030500c0c0c28028041b10010000840c0c1c0e03182d00040c1c0300d141401e503045411030441f4500d0607450300b41e00710424000564680f40c030303102168228040058180c1e443e0011000741e11b060354180700e0342c2003903100c0d002c140000c104038816940e80c0d2031030203400709404015550f26494101600e02c0d1401c95031042d00818244014500425009000c0c0e074201c040c410741f00c8e03002c0d020034a4125211000010310f08d00700524031218900341680942c01809860401044000d01b051400064405000031607000b8001001000b040c844803101c0042283c0001003d0405030800c00544000b0382682c00c26082100c00300e0020400020507074403c0754194100070f90741051440d01d801500070480310300e02124040c2103403c090b80445c001c850100f004000342e0070030144240c858031081c034128104203411200c5034064801d9000103e203d180100710651303140c042c0c0380ca1501e0341c459060242d070a40b40040041d64100440c0c00c910345a40d084803081d510800c1a603030905284000e6203420803e0b6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 803127553 1250 803126303 803126309
    0x912060108030319060612020c07030c0f08010e0303060906010f02010e0a0308150d020303040b131208190807020a110d120801060f050c1b060c1f0c030e0a02090a060812040807 77
    0x5a0030300d28100900d5400500e40c81e47d550010602594961403d1800c502c0d1000c243e100401721000c1d074000003070180302c0542d808256141c0c4d07002444201250540b41c1d65030b002c107a40d440d5000b020304000c10015070052110700c0c00d0030b20500001c503028903082d405900f00403540005401144c06c5604100103c0341d80c2007180c181400031074050095590980102e40d81b40614024002c1c270b48400a034250305440c806011000030b0010340140d07030010b00189031007070701c1350024041508904000108102864060b00925101e80d0140d0300130545180d254581d02d40f641303402d1445030b4000c87c889180001280c00c8225040c002074290300c50300e106501d4101300820740400303030303100340304010003444031203056100801d52a40840701900145070945000000500301e2142c1c103400c21681c46032110841c1c001d40d40101511516030030100401c403401d1841c00903401d580c405c1404c2c1740650494851200146400e2129640042c0300c4240002c1c4907498904013454500c01c0e40302d580320200e01013410404060104061805 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 803128803 1250 803127553 803127601
    0x90c091e0216032a030302030901020d05010b0d06060c0803150f0405040b070914030a0b10050a180b010809031c231504060b0a0311070803040b060405010f150509120601080303 77
    0x42c3d03844440c2c3d40c0e10403104c07202c0020101a000004a20805002d4041c0e44a803540c00800704260750703484000d00c1940c2e000c00c00030708100303040c080001040303401004883c0181d41c010740686c2c510b61b14421040c0f4444101101103500621100c40809951100d1250368071962045503004034030308160001800400b1194000c20f41d030342242c04040c0e4a9180400d21641103588490003c2c103e49840c1024120b8402e241c1103aa081610740400003680d61715524174024054900034100b0900040700011205000d0864200e507440c0c0c0100141d0143c0c2411400c541c03400034003480c00041009280c0261144080c00c01d01181010254038180080c0d10030707112138079055071030840d0b01300b203082d1030b14003c204176002c0c1d1a000001e15a5610320245420398950481d4450344d4800c015070744d24038191078540200705050f074001c1c0c055451301c400400c09040e180745602c2039815155840c03103004046130044400d9440108825040b20b400184075488203405c010540c06810000081c0d1f4a83c5018409a20402a00d100d031482c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 803130053 1250 803128803 803128847
    0x7180e07030209150406120905070512060411031638070c09020a081b070807060e19080d020a05040302030a0f02030d052a0a0b091609090c091e021603 66
    0x440d1f40c21144d42c0d0080d1001c0203010034034001c1c0c1e04290b8148a00ca9100741c2d004449a100801902800b20307040b88518458039a9071203c2062009040d9a0540b50001c40c1c141c9271101402c2c040840104d5806545442202c1010701c00040740e81c0152001140c0000fa402ea001c0c0442e00000300079041e10490007801000c4400c504101a0840c000d0082c84080c202d40e0194400165043c0801120713000c9901140d00f210300d203aa074003042d1411030024804e00d00303100300500444001e8510f03030011403082d0103056002512941061015007080000354000410782044c01410080000144c50500511a80034010034034a014287e10380140b6080028402807002080f50402100c1c40086a034180341050304041000f0141000fa2400e0440c640800120081c00761030021003001214900050151411401c42c24000d00b020b581d000b180007500c429000080680115400a0111259a0b4420040100e00c12481c64010800720140303403c03030b1302000084203182d5501036903d0134550010415071440107140e21a82c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 803131303 1250 803130053 803130059
    0xd082205070501120b0f0927030301030611070f140102130b0a090b130306052206052208030a050402010207030c06090306202a16170d0807180e070302091504 69
    0x1840040c103890322144104510f001081c1c100d941c2c82c1d03c8240b400c146c40b5402481900011942795030307410901c0304440141c00c0410700342c80c0c901c3ca03005442680c2d42c010541c101010190b60340b84400415200d0b030304225942449011180b003611044c440042c520f2848003541c0c0c0e08001c0004054174419048910402000c00404100d01201100382d400c4a41083e00041c25850b01e800030b407520345054800c0c4e103015842203108001e024040e806103004951131501c22801200c03016408605008040c1d000d08200d400340002034188041b904441d500503c1403042e43e0102d6140da4031164001c12070b82050000800f1040c0074400c00030940310f0000002170f4544031008100c0c20020000700c1d4031a0385d500ca880300b210710742c407401c2040d901026003c2202140054421460002c100308115190901c160302c03000d42010811008028046041c200051596948070059610b1b0070083d40d41c80d079480340c0038600540712500024522098400a03001c1d650540d0050fa460410b003003000300041c00625180a9030308200310030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 803132553 1250 803131303 803131309
    0xf08011b0512270303060a1e06031503020d51060509150414070806060a1202030a050603010b090705031f0b1209071203020d082205070501120b 63
    0x1031200c4a0007208580b0719540d0310300c1c80048120000908268003102c842c4003856250001c03014500c00c1301c0c16220380491507500c06500558030314140011b000e6480f004401e00c0128030a4000360080829035031100f01c203a036298082899508400ca00b40c40220050050003d0010030344403082c030f0001d44a01c0f640b240c202142c0703801003c420410f801d0802903c00b91480c5010840c030b4102a005140003440324050780b61480c6000c2e032580030003501600c0303680b8011030144188000c224080c02030415584911440d55403a0030310040e540306070751150a00404c02036840c42d00c1154002103100b007240b5200030406040480c00d050a4030b83c00d108071840b80502e042084a800d0f4001c0981c4d40c00165601600da0203180302c41207140130319031a0840401d0740750006103280c2c620b0058003c1c5020707840c510221401c265465640218050503c100100180c001101c0b04078460f01c981c400c00d03009a00b08030244018540a96407902045800104403140d80218204100544c0c01105144584c0f02001c0305000c95180c403400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 803133803 1250 803132553 803132557
    0x1203030906162708070b0316050304031e090e0f04170a0c0503030906010f0f03080301050f12010c0e09070212190918090b060a060804020108060411040f08011b05 71
    0x2595050340c6a881820608500c141c18000c40e442c032012440140fa0390290340c4509076206401000e48511403a01c0001c2c003080b8410469108800049581c0101800c46404641e250700c00b0b40183c0401075030440860415184c03001800a00c0f0050b140d004190b850064190501c800043c940d0780075200384020000841d006d191580d0740c44128101896441c49030200c155280d130500c04020381030b84404800c00002002c000b5006041e80d41c0300040c803620a0743c0e05403007074014403a800000d060100901c010005428481c00590382c2040c02031a1561442c01d0f040000c1c01c52301071400200000e1040c05e0403e030b96040c901040d0740c2041c902c0c405000d145082d0842e20182d44180701139880000400c0300e805070054840d031040d10160003000c45541150340340311101c10251040c6403090380d0411004d404217180b880c0008910f41215a00d40360036000343d445800541d0305000040219030001e03100d00894400d0000d140c028405002e109691601d12414124a2801c55503075100901d150005440c4050a298010003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 803135053 1250 803133803 803133811
    0x30e010f0e0103050c04081e0c040b15090109030b0901090605060a0602120c030706060605070510050609041b05040e030a180806041416030f050d0206190207031704050c1203030906 79
    0x30f000c180380d203c3c00c5440010b0f100e2940690801d0003018a01c0100034070640d00700d221424203c0c11900c4002d100c0c0c08200c1240c24a116403640a40540b43c00460b020010300170f0030600f001410312049940d601e840344480900308075802003241e55600041400c2008074031034181c10400a44000c4100d608180001c0e40d240d88000c502c0c1c10261010691210f18072040048801003580030f4002d01c4550396502000d0078075003041d08111454004c2442860440896214907442210018184502034482c0e07120304455100c81408012803015038800031445403240c0c0641d4501a10f508d000319074508805000038a640c100002040c580d403490041044400c0c0c000940541040e004128401e20000006005241041500c9100c000f00001c55000090003644100c00801900030f1041e40c40110b21701038100d0f2104412a6241c000c0c03440e924600c000c1035804da025022092003070414845082000914001d4204100e50807242c60b8000b81b45200c15052201c0c0c4d880555200b1030095013035080c100303000384e01c40300020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 803136303 1250 803135053 803135057
    0xe270c1e030126030d1a19030311031912021e27031209010207030c03050a0c0b1e0f0c030f0310080304150e0d1a090f0a0507030f020a03170403030e010f0e01 69
    0x40046d141071865464030302c01001d00402c030440c59034001d4610100c040702c83c802030703001c50325840c5041c5541501000f241e0340351520707022142805d0341d0200d054801ca881401c0d92411280c0c03d00c204075002c0700320980c0e00540940b0704c8109458000078401e452100c54004003024041c3d00300c0e0592000b0351000030b819195845004141626821200c0c0100d15005860340054040f0107003c1000090080128890040d10f02640c0800d102c1ca4583c01045500d10407101d450351761020143c0341c007200d440300501420f0b0700c6186413800b03490038402410317051646d00b1110582c03810a10002c2400580b005041c6100000c0c201080510704261402061055a0300a4241c01d003c0c03200d10080c20513107540e00d004c2c0c2800b50b03911080044581c2e080c03d440012261084940a50768822010401405080085c140c0c2040c1d510800400d81641103644211610107004801c0ba0040f244010110026040c585454030718081703600c0d103644131484c0d414004c0c41000170004e20b0341800042120307004c0300d662101d00707020340030400c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 803137553 1250 803136303 803136311
    0x10b030309011d010c08040e1e09061305031c24030507140f040c080411031b0105070813082503030e0418080a030209010e270c1e030126030d 62
    0x203e0010303030380c801c40304900410034107000501154102050003035900881403000380c00c00c5402890511200404c003a00c4001d05540100009024400c1d8560788180461041064074240300d602c95440e0b03020030700d8410204040e40c80f0001c1c1415031303101c000309000c40c1c3c0c503101d04103460501c1e58590645800c1c181c003d1320300c068200210319240e5207491000f46441d150151041224840c030303840040c0202d6003500c0490f0b54a05042c07480d000341c58002030510002104801f018114186070006451991221500b11040001400600c1066041e03607810001802800081c2030700440807121054003100c41d64582002160890f41400802e5000003080101007064030001002c00f8021103080498040610080042a001070601c0200b58150058130380d000b800c1c0c031204001c00c40c0004010590320070318031342d0819104005505200e84a550161604001200c203d03a18101e2704030f0403012020703030100044610b280000010400a88084030540003c5800140d0302c032041d0000402d43c2d1a07222f101d400c0345287d615 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 803138803 1250 803137553 803137607
    0xc1502040e0c0d0b10030b04180b010510021005090a0c0b0f03061005070501060306200903120a0903080a1d0d0302071e1809110303031341010b03030901 67
    0x140c1d21000080e800117011240c280c5a001d8018094803801240600941c188100c61015030440b84036210ba0301d50188441650381e0820007030240000c0080341100c2144a02090030240c4219841054010f4400402811025029007494419400f1540c41b40703030042020050060092400342c1501d40007041100e502c030902140c2c15045a4a002c1c0ca54082c155500c0c0403400020010103521201d4810f00903040c0d081003c1010803240c28070301500040c90780581026940398526141880200542c4903a0300300b051001d500c980314100250402c5072004041520b060076500d8441c40383c2e004640d42001194502e50600c003a07038009480e01e04c0751090448041101d04000f01030380030010500f018040c0c5142e69a6015405030110002e4a0307161403d0301c0062544910113414100401101e01c102c0401d021083d0381e10f942d6032030f494138030112031103000207800c200c0b00340515884003a40e58030f44a44101d202c41110585021090850700103024080c03080e4010042d944842e40c00c41d100d0792403c0c9000c0140c18080355 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 803140053 1250 803138803 803138827
    0x192318031315050d1812020a050c04020d110d050603060135010e030a170a0b062704020c010f380301060306020a1713080306120c100c1502040e0c 64
    0x5090340fa015840c144000343d1081e00580c0c5260817840d0041c1d02c4074241c605800c1050741c5500d00254003070665080507030005141d040036001480051070155002507810482c0203290200c3d00800801d054180d01c1c0c00500c04c0038941040711501409400c0035906240c61207000400d8250095031050f95a00c8140e108c4002d0141c0a5114040d0341d0400425659030b603a0302c0c54020b00703010300f400d00e800c05241098085014840746100780451900c010300711a00e09610082010f28005200a000d6807592215540c2402d54440d40064541c00041800124690f161400308a040c1c400d062040c048010014240a50002c12940802e21912640410844815100f004039001d4030403504007400c11030000684c040042da0069158100f818420414000c40d12141c8480b0800700780c01102401c64170742440880d410317240802d40c4040e4859002c0488000504500108245c044228601c4011a032a022184140310141030000086031071280c0840c03800b0308144c0c01c22445407015010300206440441c0c1e440c0346035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 803141303 1250 803140053 803140057
    0x4050f0307051203040503010f0e0d120209180406180213020705120a11060906070c14010209040e011d0a0b0406050601050f0c01020405120c0919231803131505 70
    0x80300280482d000990f2400003542d0360741c854407900340a9803800c40d0000104031144984524041850003502515017412011107005800c1288990220f5003002551480d585244d03218880b920008105400741c40c050400000b02c90a441c01e8451441c8605201c400603030721f80600e401c14030300e003000050301c07081d003410301500e0418402c02c140900324000945040454000350581c074204041422030794030740d441d04003807501ca000540f211008108803d0303135600054103013804411202caa90b4001410580e400001400b50f030f00304048072081e07035500c010039001400c0241c081c010111440008040c0c0100650f0303401441e00e001030010300700c0b0f541d880c0271400680c420411aa074840c500a101601c3d07000e680e807c98000d5115104141c881c500005203030100550201e402d11b55114010414045542d40341c41902e0608822100d100100d40e03299450656200480300483c100c508540419034107292450010802120303070440484258410312000c0040d100c1c1680241c2a154008506140c1d2020700c0025100c80c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 803142553 1250 803141303 803141309
    0xa020c130f02030c030405010e0d080a090303020903011a031209180702070b0f0c16080a06150807030b0f0c0909010b2a0105150405151e0405040305030a051b04050f0307 74
    0x1c0c0c0000107200046132680003460046010300020041200c2010794259507442d611a01d4001c101c0650003d1151251503010055007070007401d0142c0390401040000342100d00c541d8540089407690302021420f03003010003240785150740e03120300702341f400c0311071000036050400390350b40805154242d4000904080c0700f401200300515103080306a4036070644000710f107015000000001260b1040c055103141800c821488142101c03d01e002500b02105961036a1014210303941c0201100700802c20700041c03018007000701d0f20045002d0a1109841d041c40d241d501040000944542c8142c2c0050180ba455917850000c6141115680e4000035510301182024810307102000d0a03116030300400b102d1828000c141900000c2c4150800c0300d5081c461116401000100d5100742d0306200481c08007141c403042410040100b0741c1124a5241242011440c00002030507a40110b90840001c3e40100900c05074181a00510307402c032070710303070714402026611042ea403000d07026502c105403040b1155821b142c00382c0c50502c40030001d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 803143803 1250 803142553 803142581
    0x918192d0906061509150c030806010e0a1707090b030106030203030f0d090f060c0206160206010522050117061e04020904081e18010e0d0f031e030b13020a020c13 71
    0x10b289134041c0040c1058101c1c0c407485140c0c0c25200d50403540c1d58811821006140d90540303c0300810340b40c2c0001180c0079800c0070f41030368000f420900e0200c0c031900c90002c11403800000d00001c0260354200b6640805490788803051502a0707041041c00d000580e0088280da114903110700009468082c2920080040d201c40c610203011500300c00c245a0034018540c0088007014030301d0b0210b034040d8507a41041c00c091481c1d50001e5005070800e41c01449917181c003000c1c0902000341032100b0100d402013408240229031007070f4403c407c071081d0758920840859041c05136541c440d4800d20143d02c0d880d080100043c14000043c402071256810900041c200a400000d41d206601c1d14402c1d04020964180f04d400558030503044900499041b180c01000c07584100908100e2040103401c03c1e14170b418550310743c82c1d400341c6640102d080c003a911b00c40314144000c00316610040c1500d0344d004907150710900e040c4034084503120002422240100642030342660001940401c00009450005581c903000107400001c0c400910801c2c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 803145053 1250 803143803 803143829
    0x914060103051018020901030501080c0d0b0604110d1a030f030403320d022a0906181e0f091c022109120307170918192d090606 56
    0x24112541741d0140c888580c003a2010003050b40ca03241059540c100202d28660300118507603401c40000c400c8888280c1180d405440030500b04007080c00e180058208910184406640701000640c51088441a2030903100a401411003005044079881c1c4130300c214000608007000001c00c0c2c1898464070342e407051282e0100b2410440b0100802c20850311030020b500070b000148660f1086440c100751003100c03000c003002030980300c1c8480b000d441c040c04040203000300829440710b801c100c903182204401c598940b0801d0032101848856840100d4501d02400140003001c4000c400820401c0141c0006600c00440207038035842c030b64022011030b0480c03910170300b0307440e541601e40c604c010070400000c0c00c0c0140c840444210790150044800d94409562800340c81800f8010745d11044001d400784001200400c10880007070040b144038680503128003403100003070700c02d0002181c403400d814140d0b14441c8200f03141200076a415508032410788030700c5d25500982c42418102103a4594078041002242d9011038014803001010130 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 803146303 1250 803145053 803145089
    0xc02060a03020c06070306120f020a09050f0a0e03090603151f030b040b04091101120b060a0c1208040b061c0b0a0501051c03050315060c1e010609140601030510 70
    0x70040c0d00111203070041445054089484580280200d00580710b414040007142203036521458011109024203a230040000d040200d80010a4041c01341b08408400c0140030354208004480c08407072a96009013200d4009001001c0d255030f9500c2125005601c280705440c00c0030322080015031810140328002020012080700710412501604294541350701181e0030050402d0f00000d100580300720000003486401d140704089215130064040000b00481c4500014400c2500008a903080e480400684085221404c080040103500440103410b40032504d44559241843e541d203860f80b01001d0316280c0300382861071104240c135203000c101610140c1c11015018007420b04006101c01080203018050049184083ca0703a02c03102e83e000b810b1446641541c2c3c49240d07981d05801e000f00c50100907d5940e0100c801c102040c641003080002c158100003000682000c0d108401140d0300319115a400698032a090401302c112032806424019030280b000c1c200030900d661465212640d01c02c098029500c024184c1d03103c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 803147553 1250 803146303 803146307
    0x71d0f09040c051509060f0c0a080a03060302040b0d050c041a04141509070503070302070c031202011d01180602340201080a0501080c0d06060f0324020301030302060f06010c02060a 79
    0x2503401c655040d200a402c0810b110310641c218417900d4840c542000c030802c00e00c1ca891480d000181690b401c0c15003500c05c50b02440d0b440048030303401440154002600c5040c00c0c401d43c60544119405d46c05c08036841c1002c00c8440c0d4480780c03110102c0307031528415503803014041400002200c203a861170704020010060400440364081c004201654001c03420303140314107526020b0500188a234043c64542d140d09003503030384500080b4081c0d8000c9000311007040c8040000000500020103468080030349030004a94038406a400c5000e103d0418401c0b8060f038104111200e6102000c601302044035089000540e0741c1040d10b9018031040da030030141d108020708000f9038040c040380c0011600c1c60a417003603030380012030340b07480c0071520590b0f03000c1c0180340385500540030701401c1d450207600801030684183d0002c0303542942c0d9402180d43e840750f5482a41d01c0c000c4a50008150480801d120940b80e01b1480114115410b5450003540d944004000d001c240399001d01240b03030b6a000390300e43c0b8222540100780076504c000003800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 803148803 1250 803147553 803147573
    0x20a120207150911190e151c0c0306020a050d0f1e18020a030305070311071a0c01060e1503070801111e0c030a03091a040305090d1a1005010f08071d0f0904 68
    0x40303540000000f00400c0b8101c0c0c020305150b560120007848441c0c04441c03230301000400c3d000315104070340c0340c00c0342980080000d540c1e001070085e4405a444003500c40340856000001da500c2c0c00c40301d1820b5840d00400350211100e04030641141105501d00052a240c112000c0c1c1390b000707071303d03030040d6005100711400410141e211004191399882641d40a1540607135240c02e50b91103040b8010400c5185d014040d0915840c1c10a000c4c241c102c0c034050000c66160f0b40c0b07039201000100c056640c0f00c0b00740c54400400c40300e814100041c80c010030002000700148160490048114000e80e075540750b40b003055200d05490300900d24250386440201c50203813555045c03444000750060164903022550171407a01c141d242c9174007070455514400c541548405117804803000401901e2440518125401c5900c94428a11401000b041e98443c5001e400c02c000001e06001c0050481d140c40e100358000c106144080091040d81b0007811440c440b03880e500fa200000c10800080c01ea034403000c40c1d451308480c0c104208020321200da50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 803150053 1250 803148803 803148809
    0x4050414010513050910051f03030906170c041512020316031406090a020d18111207180c09121a0a020a02120306030109020a09020a12020715091119 65
    0xf401e101c04101c007005007030a50302e04030351344070300ca030081d0941c03000c45040d5070003d550008400000321004401d41560280c040c200d40c00581c00151014024011182c10102c0e80b42e0710015a0440c0c40c003031410808441040c400c42c040d0030784943c03500500d01083c5001da000306d5415403240e03c1c250b482e460304801490300c3d00800748a800010341008031411101c12511a1507000d800054502c0303080381c0e1001c2401001e540804051840c0540d200f11500100300700050381141a4818540ba8034402e40141c10000f2900c0c0511301d00c0c1454100900c204203018400c100940111003880000c12024802003058400030030381c1d84403001802e6400000e404201351800c2e40354402002d5400920207031603055800c0100d000318041d010250f482207245031241301c0d50402969000710020300116081c1c0303150780840e00d2501c660380101c04594000c14061101d075008002a1400003240300d00314285903458540443d04603103030540000340e560716120758080c0071004880c1400c00c040940448035211580185100200040c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 803151303 1250 803150053 803150059
    0x40504150f0e0f07111b12070602030c01141303080703021e19050406020c0108090a0f0807110d02150d06090e030408011b080c030a1b0305011e06120f02040504140105 73
    0xc0084c64060041d985101c000078120001d0001462903449866007030740c0003407842d61120464416180319002040708034054003040c0e000e540c0324191f00c0e42442c00c0d507080d80384900300000d8810400c411007003c8164424069018540244252110041a0024031030f410343e440075413060a400c101060464030040c854807014100e050500745502c0011100d0f80103034010117005801c0b42c80454120741c41081d81541000103101610094451030f03030b61000c66103800c0b038115401d441c0801c1c1c440601c01140c500d0043c8000c141d4001030076000030f60000b00070ad180b01991034850500802d098507100520b5003c4005403115000402018400d044c42580e690040c2c0b240816640c02c2504030280c05001a0210a030344000e40c641c00c4047d07c8180b10781d00717907820042042c400340b940c0f8181035194603181c0700c900c80c10f10301c5900e00260342d504200d2500c1c05800010781d14603011440300f0301044000e500c00c254400b00a280000040c082c9605001800648038a520250740306080c88002c56041c100c981c2c4a80c102c507411 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 803152553 1250 803151303 803151331
    0x3103020111070b03060f01050f0a080709080111040302040e150c090a060e0609010e0102100203010b0d4212150e0f0703020f0103061d060f0102030f040504150f0e 71
    0x1c00380d460382d980c6640644950034030180702013100340c113008210502d4241c050410a04041e074081c503c8800360841070301c43d800204070100740042e040e00002c440c405000607600902c250241c6030b4000503144968032009006d15590311501040e04da050140b032420b8000301001c42003e060a201d586041c0c0c01c501156449042e400302c0004100b0b0241614200d80003000d000c1c6400c00e0f01c040b0040d1141000b92207014154010b6140120b807140301403000354003820314072400d0354448504010302422600c240c04107240c0982c41aa09000700b800c80c045200150340c16030142a1001e008043d1504c0c0c0300704662100b5a4a03074222403000400000d01140c16240c40004002c01c1b149540d141c0300e640e50108910207440b45e0b080074400780051304107400440f081c0e9406040200c0c0060b138a1a81d801d0824021051840c0da80001003841364031301c0d0400e84c8a4112109200444c101000f81d40d406515100b9403045500c62562980121030041c1d00c0684c030401481980241d200056523a1003503010900200c403003400f05408 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 803153803 1250 803152553 803152577
    0x60301060501020601170f070b041a030c070f140106180e01061a0a140304050f01062903061804140f0a0803071b02040612030216030b0c31030201 64
    0x52003100222107050740180010391070a4403082e207148060b804880c5c140110303800340c0000c10341000130000400c2640700085d074440c80c09501d982c011105900001904104100b0f020b0415190b10a58140c00e4018a9240d40080b042c90010100c0340480640d50865007001000122074400c03021095001c2d40100042c4000508402410300321b40c003c3c0150380d14000780c045040d02a4041e500a421404020b0612901d003410624418800d83c0046808941c02d902040e00c00c6ca048200b80520b800401e6404842c114114803500c00000742810542e00b02601e400c0400040c1503550b031014003d1008030882112540c0e41828200408603040c0b4000d00405803044440c0d52444000000c0c61000a039007101c015030075500c603030004554620081034005401400c545451015039554440c07c0014044101d94402400c0707035242c064205071412001440350030030440100040b40150020039408100403501070350368103a04401645900e070701c0d9556049080440417408011905c0e82032001600e0003600c41e07140c5010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 803155053 1250 803153803 803153809
    0x110d060e09120309150f06100906020606040c0201091b1d1302121606020d1b0c030209060a24080a15030615030218070e0117041e05030304060b0906 65
    0xc41918841c40550000744490900c000007000303142c1142415040d6071414401080301248400151001280660103005001c0689842c40410b4511821400e00d01d05a51800001030f443d00b4000b081240180c0c0c403420032024041c070039440130f5019548a13500090092504e0940b03041c420a500603140d15501969a104a006554280a119075506c07000383c0900350160b0300f842108a0056a00f0002e40f2034000040318440710401710b03101a102070f034000c00000d11420001000105003900340e0011164103152400400c2c0e211a815017941d4050b034000c2c1c1c96466490124107018426071001c01c001d1844a240406164440b11842e00b15070b0f0340c1d680c0d03441900d4001e40d00c0221401214500d000c415904e10400c00200141c10082840700312405015005aaa801103103020689078441307600040000c041000c0b050308100020f40c080b60a02e013800c4402a01271041000060280002d0005100012000c1c2500b140d0341024640369400000d0ba9103d041a2802d4005000d004d02d0051103880d1500c0011760b141 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 803156303 1250 803155053 803155079
    0x140c16150804120c0c03021e0f0a050d0f03090b0c010c090f0518040203010b060a090510111e031605031206010509060403110f030303010312080714040b0d0f110d06 72
    0x3500400724100e030b548100015113040c2c00040f03046034940700b880e1000001d03a40d40c01551341c0b21500205200000030507641082154140700d0031540c0b00714074002d42804262500c9129003030550b4880e140848981e55810203030359001d0107034004950783e0000140c101c007034041900084100d030015160100784a45510014040d00744074008c59030851442d043d01241d15507005800740d0840c0c00030300000b440c1c0c1003403c00318200d980080d0189000c0380c92034070100028240102c440089110304e00c1c3c0100c01e2801c0300d0b41941c03102d407421803044440715400101214a08140301306c4241f00002c4412041c1490246801c50f00c03034015086c00342c11340030b070000000c00950003142205e446040041081e8502401c507a10100309007000340d42c003504400403410742c04168070304200440c0a14006c103030300905510f003614001c110000043c9410100705901340704030300f03002c519800d5a058a2040c840f085c1c49041e8840c012004110301e0f407078078a541741081045101d64100b0401004160304468040c080e030743d1201031600c004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 803157553 1250 803156303 803156311
    0xc0e16020d05090607260a090e0f0108030a05181801030501150303020304050114120c090907050702060711010e100315090908030402190b0703200d0906140c161508 72
    0x102e40308100309800128000d04081c81301126034014540706ea91014a0149a0040d2549030003280203000144a1040f08508569203c0817044c1580869810410708644030301940d19040148080480c00e00c42d060850704941c03080000107898501034a54641034581c00d00420312044c3ca255181c0b171008014007015400080582782c15400541c5031a1030107004485c1a00c3c00000c00f1207518091000900f10704409811601030581410f107952030301c00420401c05546006840c01c401d01c101006248016120503041d160700e01e4010200785511100c220050380c5d402154400030364403016500e40815131681507485000300100002e050343c0e04644640d0f40308211080e44402820a0701d0510020780180740100380c031400179000d020303840c007910381d20100348000d5000300008501181911911001100040c0510744500e22414002c2c5002c546285010317060251a01541c8100080001880c20740c031030304011120702940300307000c0701e10302110101e19000b000310078007a080c00020007420340003929110707141441c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 803158803 1250 803157553 803157559
    0x25081602060915150d0c031208040f17040b0703090f06020703020109181e020c15040f020409061b080f010e010b0f03042d060f020a09120c0e16020d0509 67
    0x6030100012900f006100c00408100c540026290041181c3d180e0281d85601c80b072141c070744500d40c1411454145081950360302c0c3e40d02000032100c00c01c40400c0b641c43c5810ba003180c0144aa400c140c045619100243c442d60b0803102c1c080200084940415034844148002c8614080c0342c1c00d00755449800072a03e82134144000790006401181c14080d69150714450f1b0701c0d10005410004420300610401000170700e80c480d00c8040190b012a40140c440c1c002d11910000041031000c211603813800383d4a0349400d01c08083d0183c0960b650300f8454082010a80c4020000072005079400d00d02412101c000384000b90440e607030401c440500000007107030034101c508a410f0700c000f0000d050a02012074000807160b0801442690413500801c0c21040202049907030304020700d40c14007140341c0f0290b80d0030084c0640c1d0701507032503035040c1c0d2040000c01caa2550000312581901e0403040e21303028121b0541070102d8404000d0308101780514006d01031210340c030999440d11811003416020b56100502049007a5080d0007030983c01a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 803160053 1250 803158803 803158813
    0x804060e0f150f1602030f1005010f061b1502031003060b03060408160c0e01090203010806061905040c0c1202250302100c230304090b060301080304030b250816020609 73
    0x283e0040740b4064141c41400c41c0e01030342c0c0321529400181c46c22282280301005508a1a10755007104094003540d80540403e40514400d145004001090307642501004030120001015400801250726040840c414004a0542d140d003060340c44002c240825120498000345042c2071201c070f6050100c0e1682c41290059480c500b0702e0303200c001c1c0010080411408035100260100c000c0b8140f40c000301d206020b000030f030f800144c60f90b0501282904c2c086004c2c02282c070172034104015101302d1909a81c00e0f02601c0040e5400f051046030308906036540c41600000500d5540c4804000840690000d0010f807132420b910060900c9a40607503469484650b40e000203074020703442a00c0082c07000e0203035403401c00c10b0744100c87e070005551400070440500ca910784001e070307141e4000040030010404140100c001040c800c40d00315186525141101366244540c0c17200400306600702002626039079180030400384020002014061486142900038204501154102c40080c20401c44841c40c0780b000880b144245142c400500c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 803161303 1250 803160053 803160067
    0x1a0609060306030a060509010204052e030213081005042f041805060703090c06111e030c06190515010f110c03010c0e120f0604080a0c0804060e0f15 65
    0xd05a1006100075054401e000c075003800a516881520720032060a800141c03034509090401584694020001040741d505040d00001034a01c0c07a070085400c03842e400d0040c0d850321a11010541e2250ba03501031001c501800f00c200007000781d142c01c0244981c1c030800c40d0030f61480c0240004c210010701c06031484810b420080078950541819400a1034007922210144800b07006076a5051a0041c104e40000c00aa00c43e03215004105140c41508054006804d0000c2c07040780b52604165030f80300402c014100685600201041c500b42030003210308404038542510003c0c40c0001900000c00200d00c0400d425a00d060001100c1c4922044a1840164165030307000080d071303500c0c00c00c40314017650071101e0360035005040305114039540c24071a038411550f9923214400740d0b00d40501000450045180080055040081201c03000c100101320242d10903400724100351174a40f07d07002152a070303146503001040c40c41b00140214a01780c210340040304c1e21404580d440c18401010050011118107640c502507160402c0c0605 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 803162553 1250 803161303 803161309
    0x302120a060b1603020304030b04050f0609010506062224020f0703170304031e0e030f0f07060507030c060c0503010320060f0c0f190b0702060c030105040203190f0c031a0609 76
    0x42c081c624000c0c812a82008d413661680c0e0301c0c40405681c1224550710002c4108d0503641c0070f00c9855070005d040002000076140500101380311384940d00c0d45843c003101305c5454000d8401c4036900c110180440100c2c1e2040f600b100d1090381c05030718000b101e0502501c41c170284408204000614030003941d50100e410010416500d020500a4001800c1201440f0f00c0e40100030403444c0101160650034036039540c05240d42c0881301032504245043d80c803518150006450b20300c0304580062640c04031a04c518200e0b0303442c802420101d03840b016075040200807a0070148a121002d0340b113005541640c2c010701c81628014401709010092035140714030349401032018402501042c2c00305028001c11204842a10401402550307040d003016801401200b0401c0089902d0040c09034181c1c05035030104040c0014595414041d41c83d0340c0e5408148075461040f0380010004400c121100d1000840040c988030a105074441d01d510100500304003c150400240740c02c5007001501d204140b40400000090502d601d0050040e0034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 803163803 1250 803162553 803162587
    0x80a11010e10050a0f05070b0601050f130816060c032a0615140604080c040b040902033a0c0f060e10050a0b0a081b040b030d0302120a060b 61
    0x126505204000d65010115102c2c000100d00e2440b45948580d03442c060f61101910404050921741308004003844201e00050410140a170000c9090a2150310341038201060241880707030b00d0400c215022003207800a10040e002441c2d81c4805488100c038084a901e41c0c800301c4e40c01a100c0c1e009000603900b07050728005e005100071020300114801400840c04041c03130310380c03805440340c80c540c1100a500c80706040104d00380840100300e2071102162002e02d0b1500d130118880e6900d81d010800e40c881d5035140042201956664020380400341c0c05415205009500f0840d1140240404000324a07529802072034406524091813921020300c0548a803000000f0a0711042d030281c000000850300981d4598100410480800c010510800c601002203001d160114101054441e02211a4001c0302c10003011f00103540c000c00e0400301c1c2402080300411070108040020301034000328071059018024040075201c080d506030000d00d0501c071082e1031441c058607821088000c4801c140310b006810312084c418840f600900c42c038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 803165053 1250 803163803 803163833
    0xa021c050901140412140c01020102040b0d0b04090b0703020711040c0c0b0901060f240e010509040906140a2c0307080708090307060f020f07030803060f04060801021207020610080a 79
    0x4843d508068a80303031210b0400350040000e8400d402c10101e10501e8407020400e441c00040d00380b00070b6090030b10306066403080780101e0510940151711510140c040740c94540c01240c81c1604204192103504001e030014009502001081e900201921140c015070705050056046080e016541c50b00000c00c161510848070401800300f90465407181c00000d5120300d80548503000d00000a0034840221407581c01c6495040303030301d10080500c034011140031090b0381c108080d030700ea40d0019900070030003200501d0074030000c05081d42000b03080c2104009000214000d54400300f41c2c40c0242080402c40c02c1c0307101501051000800e4503000c1d0341d00802848000440786806032010b144030b03c9169003406072600c0080c0c1414402e800c44000140d000032500c0d5200d81c10802004080381110103070564030304540702c594041c40000c0c00c050041480070310a0301e003515181d10042c01486c07494002c40d12505000e42020244006075580c0c0c0051188502180c103200384203414404540400c4020319a626070366541541c0c9061801c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 803166303 1250 803165053 803165087
    0x3060115140a09061709060708220b0114030307080318161e140a05010e030c090408120c0a020c01031a0619091a09060904060302060c030a021c050901 66
    0x1001c03154401c6064009060301c415152200c91145080c0308005081c1c2d08000401d04d4a41c3c2414103020b182c1a0100320300b40c01c0490f0340b502140c1030343c0d40307905041d040001d0400c105030050041815000d1011071b041302030580b044080302c1803143ea1900b0405950340950140500f0360300007040032428000b940c1a00c01075507407000050b20281003940c0d069001303e60681c0c1c4820074a4144e20302c2c003404800c4641c07820700504800b0005078400002100812801c90396402028140800c1800c601007554040110f001d51105c01070480c41d00e45002d2510f281290021003288c001e100401003c0780d180302c0e1010a907824001e283d402000c940040e440110040d20000c041c00802c0706c803010043d0701e5610b4081c010950f0445c960b0044043d02c24880c0020304110990303002142c85040c2241405041d4181412a090158210f5120b03840d62001400940104001d6100070352003d00050040141c28000c400f41c0180400d03a02a5040c106c0e80c11094001d83e846441301d0800100304104040c000d600a42c5452404940a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 803167553 1250 803166303 803166317
    0x9050603040609140a12050703020a1104020c07080703060b0d030f080c04050a120b06100c06022101030c1811070602130510020a05011d030a120e01020a090e0a0b03060115 75
    0x1038030340d12145640c010541c60781d0b402c140c001e20140180c40c600c481070280103241c154985031b0949c034000d4485225600040000100044081141d500c0e41c064982c064048015500c1240c0d82c1c0da116565408a032008032811400c11101d1a42440c2c025081500706401d41c40c3c1080400c039021302101c403644020260000903000b8440400c958540e00641c40180c90a0038400180d03605608041407006130040a0701e00c01c102d1014841c80403030b4420745c070400d5036a1000000d40c5519040345a49a144000d400a00040080c907000005221824100c1c000b00c0c0c00a408020010600c7c0b01c16005644503603005402020040001c1d900058040d0b0081022084680c64011840d894400080c00320041c8070f840001030340b15018100611000303104e861105001e00b008000d68070645010b407070710790044040d40c105100001010408950303803900040c5d64400264000c540e100c184d024060183c00003406009824403c1100140d04104a0311034a1103d071002802411030382c0c60300302060407175550301d04c0c020100162 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 803168803 1250 803167553 803167571
    0xa05030f040f0f03050711030f100e0304030b2703040806040f1104050406060f050a05090f070207030b09010510090504051203070513090b180f04031d090405070602071203090506030406 81
    0x340c0618664854485da480564940703180c03e0100d400b00382c40d044540f00360041200907402e09000165410034401d990f1b00401d500380f01885582c00c0d07000703075803000c1c002040e40410000c4800c80d0300b50120208021204410f40810b500144641d6401540074800d1706501ca800810042101e2080d0040d095100d51141c4507051112000b06003641c1054078221001d588820081c098800d00f2001803000e0314003601d940801c40d203400001894101e014003840c451031511404a0030162081c80303104061030308030308bc1788414241509014000c0804a41c3c95015909183c000b08a000c42802458081c68002c00144081070540f040c0c0c2215910241806092245c20000583c400d035004005000801400354000b4107240003000340701094006110406648010b030003040b000481c1c0c001300c19000758251500303940c000340364559244080000d00c6c1040e8015200000c20080040c0080e078142a10b40c19401c0d500015941d141c50b2040c0204000e006020032981a424411400c0c00c002950b40640590b40124214030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 803170053 1250 803168803 803168813
    0x5090a09060c030603030f170103060b0319290f160203040510020f060601030c050d050c040506121609053a080a0216030b010501080414011a01140a05030f040f 70
    0xd003103807a0b50082078032480100b05241c0c0040c40301660030842c0c01c04642c041d603036800002c07500d00140001006a995968100b08588081005c0142034208110119041d00603007010b01200506641418505015224610b10119016206802103203240b001e401d050b101e400c44107400116940c2400118031041c480001c095643c4242e406818007980c0142c01c13b0a06003107800d00b4a00001c203100d0505080501c1d001b14964040d080310291000b0090001e410340750f18921148038030945d0302c401d07440200840c0c1e032007104090740650303401004d0300d0500788483e0104140903501c845040c42255844101603c010b2240b0906102a50408070b0201485988074008070304e094200401e2007080c3d4021a02042c401182601086480c10310015003e41c801c0c928a195035034400c1400500a00d410000c0c568089810001d800c4003407140d408d1100300a10480c0d02500c016002021030104c4e490024500044007a00f40c40c83c0c1f81122520006692440d15540d101c244240b070440000d00201d81e00d1b0740b0031403200040b40f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 803171303 1250 803170053 803170061
    0x603120806310e0c010806010f0903050307060e06070e031f0e0a0606080d0315052205240616020409051207050309040501080d092601060905010e090607020705090a0906 74
    0x1e002da8150300698000ca2150030071100c0d00300c040b01040c0d004280039401c0303a801000d0300780c0c0510309103082000d5004854080301c902181d9031008015110210301d400820000d9003041c40b24196010860301d06680e412070464000284803000c60700b40c6c100700504030a0710440c9014205118180d0408601c99111003c0c452810200c3d03402170300c4207990382000f40155030041c03040540d0181146000d100507000001100141c880740d05c5000d1041c1303401804070104090200c40c208012500e41420451480d0111860460301e04580716012000da0000c6000301501d03040041c1e41401480030020300104030f5a50a0000a000c4480142c0300c030b1065880300081034042e88001d0400a12610107561101d450106020607500f0603000820b09400c0304040b43c0303246034007101d102c0880f00c1d05445184040c0008242c00494404400740002c02d509051021681c40859040141220030500c1100040c0da1014041c2c0c0c0c6418007641c1c0840160000d420401c00c610b0000b40c056003003001c00100103242c101030384c0c503d401c81e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 803172553 1250 803171303 803171359
    0x603010305010b2404120311030d090303180c091a0907050a0305072c0f0a0603060e0112050d050d1404030c03020c0118060c0804080102040305060103150603120806 72
    0x9a4640064018601340b654440480091498000b0005071801319110810b008a0003641030410340903012a05040c0300d1600002c41050640c11340380e403a44048111009002551000d03004030381480e003211540720700c1804016007150000c61080010313050121580c007415100d050303106640780a062102c43c039690fa00c18103006a800b81c0b1056038961000c0009000d13510000d04540600080341c10b40c4207041c21000810001e4080d0100c07a1480c0100c900005120f06008100c1a07041090010007150b52905948040280c8000c85040d00c0d0356030707903040300b0f1030403080070300004003547c102a0141d803a4030301030b10140140d01e00c0c0c064049441c80b038284c981d400e04102101c05400107104080780e1020f040c2c060110141a90080c601009140ba00110301000f0701141c0c410541041011090351042c0010041920050440c85000750343c0d465507800e181da91160280001d50319280541e06200038034400d8401e040440c1d40c410607048403084c116000b50381c0003c0050100d1b80001808400840c020805001d6140c0303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 803173803 1250 803172553 803172563
    0x30309050307050111070506010503030702060d09020307210303180c120305040b070f3c0201020307050307060605010f03021e03041401050412030c03060f0b0f040f090c11060411061806030103 84
    0x300e9506c2c2c14554541001a4065030180d042001280096112501182c1c0100400310002c1a06011840440c1c6071001c4da501203000e43d00e03800c0d41c0c0c03480142c070407040c5840741d8040e0703500b8000d070743c801d41c01c980354840791440040501c0014602000300583c8031a44e002800e000341415400e255580c5030064459000035400c4a030b4050260030340b0204102010500e011034810000c0c035a6203450781181c0c14000000011400c840418140c64404588c400c00840d07140c10b034003005a030340340c410070716040020f0181c0c1d000c3d050104004850401e0424070a109440c0042404100500001d8005005115070b500c094025600400c7d4a8007a04000009002c1c04c0e0150b032103454440001c0c440060010304490380703c28860100f50803c1e00401031080024000410388106d20f17241030f90742c103200e06401c10920482d03003c240f07440713111071000486003107035031002101007040d4071445442100c0c0c0420701c2c0c84207011100241510301c808003040b00e50400d00c1c05025030091050307614541c010013900181407074000341c0c0105c070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 803175053 1250 803173803 803173807
    0xf07080709090c1e0911270402070602191e0f05280206090106050d020a091d1e0c06030106201e0606040605030105091b0303070b0103080901030c081003030309050307050111 76
    0x8030700101407140040c1840b48040080c2045147d13460052041c1201a030a004001030130350f044410707074940c1e04403194039078840000c40d0b0b19a00300144200200c40e89070b4420220304509080002201094080e829180d020b544103d0360070307210703401900e80e6044464021400b0340164900d048680768050341804030031007500100348901d0b0a4480609403844c41c1c06c11360194180301602401030b26000741d0242699103008002c15614008810626591001c0c101440310b4480c00030f107484100c8040d021001c40d89200c60030740b24024804002d0101a100c01e00c502c03c006840c1100f2564084070f11a00c550b110141b180c00e80b01c2042032104060b040c1c001040c030315407042e04000213024083c907107841143d005020a030024012454024681521142100303030740500c00c880e81d80030200c03940d41401210748840c0d00c1039210013196140e0900c06019007010548074086894012280c10450148240602ca1038540c10380d00345071401d50381c003180a0148450121030038402400010000f070000c2c0210109100290300c011303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 803176303 1250 803175053 803175059
    0x2131703161518150e071a0f0906120103051018061a15090306061f0f050403060507030b0414040c05060d23040c1505040501050f070c0303020d020f07080709090c1e 72
    0x100889102003035904c6175510822041050a83c00300d6441140c81108413000c1d1500350b40507241002c0d00c0b0384110264080c100058805007000301102550581e8002c00881c3c0258201168042c101c4000c000c0300c0000000b074401c0480004c0311b07030b01301300707942c80307500c0c080305481000000400c50b10404003206040c0c101d4003150605883c2010003402e076001100700c445021944441c0322407550b60102070080400c0156020245200c1405441124003c41e1f11100c100035601d44010010024041000d01920950620a4a904481d540d201c410f00036030300540c0f00c0c1c01181c80c01080140a0380003401d4800701c1521100030b501102c460040701c12a42200c1e01660750b541c81c00f45801a40100d50742c1103a0711000315102c540303910b10f900105a400361a400e007040c5a480404100d0080da902402c8002488100e0348075003c0201070b4013152403410b86440781c00700d561041350009110b441d1900740c09104102e034805a020025004179801583d010b502440a410720f00307449071140710030201d000304003e5000034040010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 803177553 1250 803176303 803176343
    0x30516080915070b040318150503010f0603050f0a0507030906051f050a18051021021525030c14060105090717060f04020c0102131703161518 62
    0xd0501d407881c000b140d01c0c024165449002002000d00064104443c441c2045080c0700045001800750002190100107901820b03002009a4002d000e880400300c0003560020b00c0074000d008480c06002c1c04c00c91142a40c1d1070900d0003006007001010b0300201501d031010000410742c50310072540525485c4001ea40c100001d00b42c1150104210350209000c2d1001c2d80e4200203840c190f600d810010b6410403400b0a60713842c0c00d4402d080d038040f40e401c0203031100ca89400c060f0045030b51a8810341c0b02403003510b8820141191400380b0666000d68076510751840070300041d9449005a80e20078070303001e0b48a4140340740e6021954407000384494813407248901d241d01000041c490b81c5052030085510078181c5c41c080c0007180040c00341900714003000c2c1c4000c1c0144691800c19929a40c1c82d0180c4003a9140b20008640b5101240042007600410348611040800307940c03042001014041f085800072901001441e04881d02a5105e02c461410080c8000e4902d45d10300350382ca5211540081c205035507024043c1441303440500030039 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 803178803 1250 803177553 803177569
    0x601120908190212270603180d1b0b1f03050343050109080c0d180608010509040f050601060518090402011e0203040b040312080915130305160809 64
    0x1101c001d561150700000c41d40c102d11001c991741c05a449542d000c0400c010182e043e0300d20100c8221503032004003c010460000220301c9104800c40100044500800302c5a2043e038581c000c442c04981c1040300c0c0050000850f211120664020000000280008820044c80c42100c520707900100d4207900000782c0a075440016001c980c5540e1120b1f01c0c0e10f030325101542c10108000044103191941001400c0e006070500c68207500c080d070b850790000d080700d5403039038041d013419100d00d082a404800f203021134a4440c84004900a2a42174a415842d130041503401d100070880080d0000700100c035500c0d840f640400020340b00b03000302030003080b05449031910785c0c400c1100d80f003000006946003030041d0701207010000540e07440310310001009900c600d060020070080004904512a94001c5403088030009000000c00854014030fa1101900d96580a0191900300105844400c94030394085035240c0c0102050301081e41514120103144241086442d01041446046070720b0f8106505980b00400451002428204041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 803180053 1250 803178803 803178847
    0x2010206010e10030f0524060a0f080c010c020619020d110109030e09060103020403020d0c0f0602030a09030305090f040903080105030c060427090803011707060504050d06050601120908 81
    0x1907185980d10745071104100f105810311014003210202030707040c03043c03100c10301c02c0c01240002c0704480325120020302c020040d180d1054611078004c00c034009000500050f000c0450040d6401c10380034044485c6002c0c011180c0844041003aa48107104000004450340d2014174604910308071740240c10301c0c240c4150302900b072000b65080d4100c0369040003c042c00090b8420780316180818225a00e80064444400407402401a60070007900552007181170400d000700b000c16202100d8428208480750754a0395412612800b070503101401065481a00f840041d0040016042c0818003810075000364611134006401d40f0380c40c0c4401d401041e0204014051414240000969024180c61180c070380752804c00f4003400131020120a901152503c4c03501200301d50107030400b04001340c1144400b500e07035854403007581001c6403008080e0402c1c4944200050081c0c002d40a0314111500240f8655076000541c8031100580300c02807c2038100101c04003141c0f0205c80601c80c8860003809100e440d915054155002941009409 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 803181303 1250 803180053 803180069
    0x60507080d050415060b030420490507240c060914061608010506030a1a030303070c110f09161403070c0201030b0117011a041503090201020601 63
    0x2959010448050440e58003041c0008001441e40d030b1401c2c070b44055902a8004091181800c400180007044500914002c0e40241d500c0c811904003034041c0782805444d0040c4a42045201d180e1005c4c80884900c0420113507107620418858450300c2d402da902e4016111022000030250b0358060081c0241086403001908080300c0c1c410100c1c00c0c3c5480043c00d00c82d041c5040c0100542c0e94081400c000068110701150b030303813020703000101c0300c0302c0e10000741c840d20304131400104040030001c603c418900c5841482d04903a00944514a1038a07403003024400b40480c1109059a600250043e01207502d040002f10300c00d00c047d540c2d85a00c035805160590088040d08503151055a9556107082c003680e44809d1282c000d1a07160150081d02e075008816034203641c898a40b480344290210811a0541e00f02859601c03151007640c04015145e4405c2c0103440b207442e11152401540301000041c0079512a00005041c2072254140f82781c141a9078048003d170300c800c00c9940d0790001e5100c50401086580400205014080d18 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 803182553 1250 803181303 803181307
    0x80d06061215050f06040b120106080f040c050402030402120a080903150108060612070306020d0f0e0f1209030a050a06090b1303120207030306090f060f051203031308090303040602160605 82
    0x12884070144010b1402a98421641600c1c1103900d40d6424003180c008100e4081e407941c80e03441c844801411082c0034454040172030340c0e66000032580b001c0040320034895540111758a403403600304010310000f900020070480c0c0010f100100c805045a00700840301203640300304900c5640d180d049003411f05002c2e039040b06400b8291440010701032030030701065240d0f1052042c1c4e83c060000e5a2400e40c54a0315081d43e20240505200080324154150a43c000c114440303041c07481400540c003c6022181d445024020012882cac04c00c3d140c034611350002c0d40041c401103800800701e445184450b15600d0030030341d401c4070880700190350300900010801c400034a01d5000c21540701003c084515918040c0c9035001c0c804047c5102a0b001441d0010035009500000160100f481d00b00a60720052a4840c010001401121030b112500d10b030008161901c0384a641d03500242002035420360300d40c2920103000611001e4212451b201c2070040c500c598404001910041c400340d8018595409516a080c60007001c0e90401c0d0200441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 803183803 1250 803182553 803182571
    0xb030f061f1706310b060c03070b04020f04020a020f1b10051c090302010c3203090703020d050a06061d041e02030f01020715180b040f080d060612 64
    0x41a03200100700c00741c1e10341150703d0b620b01c1c0009120041000c0b403000304544800443c1c4100000c0000f40c0e803030158150342040302c1001c0c2400c00800e805140507910f01c46e4420855400010400b03842d00ba0003070301c00390007400c0108014002400b80c0c0c100d0081200142d1005191a2a880007000304a104424850100500c002c1120100300c0381102d0740c48100078810001600d0901000e10000481c014404082c00c20041e00b00e450020b000e015040e40c8000001c1c59000f403480c644501c81d000c0340800024408542c5e0b8045503d6034044c0d103410007098134184d80515140000542c07030303c40c4003c6009200700b02a141c02949850301404440c0c1541000b45c0d96910a007111002c444080b200700d4000b42c000400a0702014001c1c20300d070440800c0c00c1c000323401d03008100e41c900007a201500030b00002c500c188031103805603210082010858026201308a08000f00c0c006101c0800d40d03400040b0341060260340040c0b89100a41c0b07480610380d1100741e44d900103d40d1402c081184a0b80510f101040c8506a1030034060f883d9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 803185053 1250 803183803 803183807
    0x1203030a1e0c05161a010e06032b0e0406050a0f1d04081b011b0302041502010e0a0308090a080f04140303130e15090103050705040c021f020a03060b030f061f 69
    0x82c2c05101284c0a40c810100e1051101041141110700001070a94038550b0311400862000101540d001d4041e2244820118010095411021069800b01d00b04049440e41d00b85c222114000307481002e030820b42d01c0b48c0c01305450b11290190760103408070352001b482c40c6140144c007881d06e0030b000e0b002d1403100b00a20203204c00600500e0481344c4c01d00310081c42403003c8080324203503030040001c41c074030034440401984144402d03509900903208440d104414042030030038800059003a25070000311501c681c1c11900e11400000e00507036800350440141300031031b4520300300caa580580a901400c007141103104007240c200311080e085403061140082c140c0140d81010000c0b0707901d49401040f4010700503101d840700300086103841c5080310f01440c150000c08840c4c079540e403801d1254031041240182400b6500304151503507401c0c00010030191580515940c1c0744202c140c03039030420080d0040400d60080548550300021045400da01131402071030000314040f0142041c004110800082195112400e0403140f50a11504c2d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 803186303 1250 803185053 803185057
    0x30c0a080303010e04060f0e0c03070801060305100f061203270b03161e1715010804060f0209040c032310031e051e06010b030121021203030a1e0c05 65
    0x165135004002c0558542d85050400360070030340d1846524520301b000303220120000107441c1c100ca040a0741502c8003943c0364001c4a00780c0d041c5000c050980d80c0038200102d80300c540c66015800d003541c2c1d03030703400100d0a4440c039400d0705411941c0010348c0021090f42075441604004c426030360030b0410f06007820340309600d0007180c403c503030100400e1413020100541c80a2800d0303014401e00c0d068081c07010306150002ca40188060328000041c0c080303100c800d14400005000300405601c1440701c0b00161100141e607a91503813040081e145d9100d400700d01c940c00344100c2d05036443c1c50240b0350300194580c40205102c0380c60034070a2089d080d41e40d000050048402c09000c0380100103014001030302d8000440c0700804030420342040c402c0d0110741004181f8445c00581c0f9a91500c0e04086610300c3c400c00c01a1020750340d95800000f00d5020a02800340000700019000ca1f08049101c5503115091019105147c8200404800d07401c540007103a6070405191140409420348895044040f1088000e440800200e000084010054 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 803187553 1250 803186303 803186309
    0xd02010507021612050a080301062307050c060d15031a0901050105010f0c110a030b07020708061905061807030e010b030115060e131a0f041a0f06210402030c0a08030301 74
    0x3006407221061002c14041501c0721500b10740c0c595032341d50391100d0040031142224408c401801071015516400500c0c0c008445000d178200e40101a1107002504014440d44150100b0308465070b114500450502c00030b41c07440045000303420452400300c2c0d03019130b40002e00d0024000142a490040140700030780c0c000d10801030b5001c8910b824107081c0d0380d0f071801400b107000350380340245c1c800c0442c0e06c0082005080901d03035200746081d03400d40c1c081c9551081c40c0d41c0c5c0c0764004c0c1d0b00304c80c0005121104119a0103254001a44404020a400740103001c042c00101043e60940d50305000a86401c490391a0a40034050300d002002d094008004040189a02369040822030160104229015007640c01c15a180300c601340c084003000c40100840c158000388101242c81115005000e400c5030f62410741e43e450a8880d903040c8095010300e018100e0a008100906101c009030001d03403103607061001d034814801c5000084065446500010300c2d034101401054030b824420030306188142c503c03110621079101c01005403411 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 803188803 1250 803187553 803187569
    0x4030903230601080102090a0e01030b0105060706020f1903060501210c020a05030c0307030e01030501261c03050f100f0e0403020c06030a0f0f200c1e0d020105070216 73
    0x141210010951900c0c12201d029050748140400820104c20641c0200b0403c50100c9440307072450380d200880003402c03009100160403032078007100400c11800d105004041c054030690300107141510000c17814503990019243e8002c1c2c1d1a080310f400340e150360544030b071001601090809600d148800501c111104907801e403001700842e22400742c507188900820602040b2036211050faa19002104040c0b0303520380052205500040012a40b00210350091255a0586801d8241080084103c240d02d2904164009240d90340780300350701210420700c007655000035501c071346558041340d0342c10544006c0c640601e000d40716038101071201e08100880714107507144500302d0341119610b0a83d95243d08040c0d0801c02d00034004e68000f0000020442e41c62110341c0904c00414601104214204244100030110b034080d16064128000800039000b009622101610520350420201c1c3c00d05580b4001003540e000d60455450220342c401e041507040f464082c00b920354000c4940c070003040001c110052840e2131400358450103203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 803190053 1250 803188803 803188823
    0x102010e0a0f021824010513091a040608070504050c16020123041508090a0b010902090415030308160f0e060705010f05190c090509010e190c050a0f0804030903 70
    0xc540f03619182410a50f80305811040724034040d075a24190a00b01541c04002680c0305d40e280c010703580030380181c4110f05400c0030445861410101d180c001000c051129228010f81c2e9291f4164554131030254401402c104409054032510f07000500054903c00742859600c0141801550440f040c041003190b0000d4092034140c0c0b292610310030041c601400c441d2a1b6043c0180002d0100e00c10411013a0040000c103140d4030a1107551b64a46800d44440103160000c22010070900100071a403079640180007030322030080c0002a50ba0360584007803071014660380110082115041004500309904001100c52903c50404244204907140010891051042c078941700300c00105070750082c06425400150108a01c401c10031080c1030061b06000401c0344c1e20700300e00f419070500300a810312038410200e00080381c0002c0c159050a0b401c0040010144900134141000300c219048081390036401da000f500244400c5e5107030560fa80c2c010080081071141404407060500005405200010b40e11200300c80446e600400008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 803191303 1250 803190053 803190083
    0x20304081e07050a030c0b0f0f070503153321071e1e0315180b060a0302180a06020c010e030f0d1107080d1202070602090406030318050102010e0a 64
    0x78845014155019100d8803858514404140d0000d5207400550301070803d0040c035648510f0346425000d02100c0d400351051024011912403030141010715002040c0d0340c2070220751702c0414041007000d02022043ca00343c09010340e107030400c00840300400042c446d04001c3c0d5032405140e034009042d06500d40d40029031404203007002403000d906c2200c0c022043c040c1c004ea044807001c2c0d9500010704200c000c818110041c086140d59150300c50180c40b81d1100300c942180840022840c1c484c801d0303905a00d0040c0720210a481e485110f0180d5039000061801185584005840c0c80d80b0040324400e100d0207440c241c0c082c1028030340a019017600015814680982483c182c441c503104030000c00c0c00e15290b000c180902e4401d030644400d000b604410500070b01c4c05100100c411003030f45d603108107a4401034000800c002c2040b944140c00ca9103000d40050100a000f800301518094074800441c04a403900c1e402540055041008410080031480c5460003c1030248000c2c440c010b03003d0500c44d140d45001d10028204280b1725160 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 803192553 1250 803191303 803191357
    0xc02040f051503070e070c0f02060d020c0607030f0908030a050709050907021e0a021f02010e06010902030403110a03020c040b03121908010e0403050403200306041407080102030408 79
    0xc0440103049081806603003001e004445a0303150a80c1001d20a000d012004141045a004090b1240c0c0041ea60755040c40c0c82601d40e4071058460020582e0492420450405a200d2f07a0000b08480c40f240310041c040f40c07900d9400142124a4045c0000c01207040c0344142010800560907640c0250240700c0000300c5417030701d000c10b0b1290344050b844207420080c0d0b40c04000d040d60700440c00e235404100030b0445003215039684400070780b11620000002d51010b10340c0612003004401500003202c00780a80000034034400001c5000385000b8099010704803850700082008101540106c4c0d040c480c0503030320000e260b6001d0710341c0c01a440b102d00b405001e00407540d4202c1d20701d6030368081001c00c0d03c16950080980c1c0ea50460b11450400119041103c80030235940d030000070380c0843c82d00703800d4852501603a03142d04007410b5948100c4030f610501200f982d80604003401040c035075014001203004a10816030746081e880307004140ea0501a03d68031001140c0d205008010115021b01c007110192100300481c020760074030000d44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 803193803 1250 803192553 803192561
    0x30f07020f120307120e030304030507080d0504060b0f030f0705010e04020405132703050d0c030e1905060109060e0c0c0304030b041407090b1806150c1e010b030a030c0204 75
    0x8821640c400e1507842c0300c103a1000301c0114002c00b101e03a90350003403501c14034005041d100c4081241314a540200001808248503502410000c5d106443d400c1c985058108003205460041c2d03425141aa5900800405d618000e01c406459440035000f4003030b200360210b0042e0725003800d403042034144110b1410801990b0b5075541140d01a050051560b180001c2d4070301d0520007000c00500d021024082c442490440b5140c0c0c0f00e4031400326902d41c0d00c203031500b45210202c8024008ca031314030100741500c9008451180c10300303109040d00d015508445a8002d811400c00e0303840d180069004006151601100340b00ca41c11504080390700984a0042d00d54070301088001c81d00d5442164800740141e5410414001044800d514030100c540010040311101c80c0c9514070802181d541200155004a44808031040744440c41581c0c0d03401003004201c0b41b50030012209000850b880040b400409400c06040f07600c88812107a0809421458800200484034031000031076511000010050240010514250704548e16900 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 803195053 1250 803193803 803193823
    0x220f080d1d0d0c050d0b011505092d1323010f060e1f020607121107060f09081801081f380a2c0d060f05040f17040b030f0702 55
    0x817075210070312494203200745040c00070700602c9188003a01c202d451955200308140e44403c44000c0083c000e510a0454240a0800b0740c040100c0000421011010755582d4512002c2d100c2c0d0041408280ca0794070045420152a4211043c01075181c2c050040c042041414101810b440c002d0a08200a440440014210a140351380706025220b031070080e0749207594046015800741110b5140c000c02d00d94500d03500e40603503110405100a840080c13190b080811150f820140345041000400101c941040d114a02e490b4010b10055000d96440c0903511040c6d6481920b1720f900c050040c1c0c4603a1104200061582485000d1280c1142c188024203c2c400c500e2000c50740443c03d408040c3c5045041401280ca040a82c100322000f4002c40c111203058a000502000d0b6042d49001d004200c484c03429414040040c2d5000803003040d80c886540d40d2104204840501c1400d0061340902d0080704103092038508a55502c820038800c1220207010300007000300e025507100b629081650390890a842c0d5540000072454648203070b07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 803196303 1250 803195053 803195059
    0x2090402070303140a0c0e060d180506071701080606060a090e10030309090e2808130e010f0b030403050318030d091b1a220f080d1d0d0c05 61
    0x480c0020950035910812041d46480680c242c4c540da00c0403801c04440301e282180c80401d0f440a01e940b098a003000062014000200000070307101c1980090311111003501c0000c640030b501800c10300841c0c6405c160300c41c0303e115444242c155030390b0511083e6a01d40a001e400d007405100302080c25903010740100d26a4015140e0f99440c4040c52070220942c04510b0070510096021070242807002c10584110b011702818511107070024500758603410180f09040075000d001150b10005002c2c400001540100200b10401500e00c80940050030030040740348640c0c3c1a070026680c1f0b040342004102c04c11044099990250309401c041e500c0e9910742501c0c10743c01c80c500c0d104a40c5400009198a91040c0582c40708071403500a80002c40110b070b10007240ca207000c10a0042410004144095440c8021140700078682130b00780394000801980802c2c1304507904142c680029403030120b881c5e82840002010022071400b40614078014150305161f0940400c0500c00306201409280341144a40500c1311602004d07005140203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 803197553 1250 803196303 803196307
    0x812041218033212031902161b09020d1506081b03061809061603060f05040f02120403050c0c010903030504090c17071d1009061107050307090204090b09041110020102090402 76
    0x130001c00e1040e58000c90b080c500c10344089000110110b401d10903102c017130070034414031045800a5107503440c503c1c00b00402e12070445000c95012034185402e00141050b0000b42ea400f080c0c45110030001c5c0c10030010340e0031103c200b019020030080e20308903450f0702103c040e0704e1325010740d0740e41c95420204103000c07003076140d180580c900303042403141400000032014402c43e800c0003032081948404504500303030758241c41944856083c54000303000618069001700361501c00003500524001820313138040305d4070b502180c0030383c00b251010980e1100340005006251258009103401442c0c40e04599000d1f019016500034001071a903140380c1c2d4131f12503004120f44c9200c91000f21004000e0301c1c05460041028104041000c801000c41c4151070003820b01111031303000c501c119225009201d082010841d004661007420f00b0f01840340c8240050b45480c18031007030303020300840d110140c2e07a00c1c144001101a200e51a180501424a0070100300209424a50000c100c0303004545c03958007007240c10f004a000e0701404d000a6401440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 803198803 1250 803197553 803197573
    0x19051302070501020f0703170c0a030b0f090907150504080307030c0501090b011e0603060b0304061821030506091003062f12060607030504030f08120412180332 70
    0x203038170003400340d84c3d12030340da031412100ba0212111010082900c1100074140d050000e4000303227020b40c1011144000c040c1c02d07507203002d0024000804070388060301c280c0d4841c1c01510060004041085003104075803900d04020385070074a00100207a9910a4010113001c101c0350a14070b6041150a40005001e40c6e0001e1400740c40e541c40e08001409100b04019203807035a1520030002032060b0090051130121459880b081e8216901c0d43c0b43d4601070418501a00340032240807180000040b91510144031032980480e840301c09025000c800f0701101c6c0003912044c82031124004100d43c00762030030b10341001c1d682d00000100e11030052a103e8455040030103951202c807210f00006002d4100d00e90050201d12101013180403141e160007040c0010b6205a15001d80054001c100900129034807240300d92155204079080d926109203412031404c0c860f015507040b292101c0c0c4410a82140d5030050080c04c505103503072840102c491443e956461018001ca80e90035a9002c1401111040c01000034490580b02214040d0b034070076a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 803200053 1250 803198803 803198827
    0xf030b0f1b160b090654030409050603010c030509061303020c060a0203092403041e0215180306070504210c03030c0303110f0f162108061905130207050102 68
    0x10101c0f106e820b80507020640c502c0039480c03002a10900001e4005e203413560701c200000221000d0480c5000d400d05c4514860100f0301310300c20001400208100d00c40000d6900b440703c101402e454110b4018001c05080609208403044085165a08035400c102c200d00130803241e140690074410054051a0300600c04a0711403086034000c0014001c03410100c55070f8568080c000040e0303400f55210684084c1441c4c2c28400100051000302c2c0711000b94800e41d02a000764815540020b49480220019038038810002c00c198011b00201d0008040d0b07008218045d100c44d1500010040032400717584119480006900300c51020b10b2000c10013101402e0304121450080c64072401e01a0400890b00700490000745002c043c8042c000c650002d0b180c01c1051a9402450841e601003210407039080707508400f818003a0198040002a5000e0702c085c140e140d001d015a402a0340c1c080041c204103401403140340182844072009900f02000c5424405491f021580c20142c0b0004240b0280280240360b8000c0c059840042d140d25441 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 803201303 1250 803200053 803200063
    0x30905090115081e070c1104230a091509060902030f0a05072403050c22060e040212040201081308130f05032e0905070f030b0f1b160b09 60
    0x9219254602c03151141d5041c00786013000c0301d0740325a031010074801040d9a20b1180107149070303440c041d0401c1002d150300080010b00315840011140c8100e5540072140601d440c04501403581325084081c101b051003150303242c422241c07a450109800703040d61102c40204010751944903040d155000740c03c4484802990780640d0742ca107002c03e81518140b195041c000303070500c0d8240344c2021900c0c01003d82c603036110403c0030a9014010107441c0c0580c01905004581500c141e01c0695450346c602412074200399840c00d036000d0302c0c200c0c00c2e400e4503000e00d004015118901e4541010540c00c5035080c603140142d42e0724801c0364180c0b01d4034014014030282d00002c004180301307036420001c4240c81007a000c1c501c105940f041007503503502640860f42c1c24440e2001ca8103980402180b100e04444546090219100c0176550b0380e42d092039415000714038980340ca108113005022001c0c204d258051103040c0020b8090800329508602038224220400ca00d010001c1c510038000c0000f0413030151994080701361501400d04504140d261 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 803202553 1250 803201303 803201339
    0x1002070b0406060e0c0415050c0303070207060905101b060204170c1c05060403030f02042c100b030a05130c060f0210020307090b18060304230c010f03090309050901 72
    0x1c2c2e00b060004550b040c1d0402681d03024805900c10345141c50701e060b80b140d0710f1484c010030720780500c00f05001340300c40154140010751182c802c40d4080c00c1c40034203191b800b500c10065a00101c0c0904a808000440d1640007844168450041e002d290000c111510b03103503000e44030700e80000e92181c10041c420110a40700050b02c0a100390122498850703134500300841d2811380c0103a0006000c030390100003c1000310740a0780c0a0743c0101400310b00540b800d03494a00268640500303c20514920341340040e01d1300740d6080205503d40000c0144040d031400c501d4040d05800900020300040c09066541002c52120140a103904881540c0b140140350601ea5409001e0040c4140e4402d0301c1c0580912040054107038410300c2141c1c030440c40d0fa1034203000d05050103204800d94200b08104954822000304248155864101461040b88200c2d010700701e00448240c40c07001000079001c5007010741e10142c10107038281e802070508030884246290008007503120341801c0340c580c900b5500450300b114040340040f4403000c6c010810014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 803203803 1250 803202553 803202563
    0xd0602130e06091b070516060c0b0c0406090312020316060b0424140a050406081c03020c03040504110d0f06080c1f11030c0303090610080309010806040b031002070b04 73
    0x30541d502c50610030911401c88000e15410740e4036030100c0c404014a0040c00a0f0b41c0a4402c0ba504052082c400104006a6812410100d114040e04c14104228440c03900c1e4040d4000740400d090500c0c114014080036072030701000f0882940f103590500442e00c05c00549100b2400c0502e0a81411058104000101f1803105401e0003207007441c18104c0c1151121000003044207a03030011102c864585520440f24803010b1400c103610004017400000d880e0f882d8081d00300544499405803000d26000241c0da01c92040e007a403401c00341401880035051411020050781c2c11038000343c8001c5001d08107208003030101d205504c02e280b84245084010284407500340d01c820140d0340c04000b01d50503c40a24104000d007940d0403000c00410400119501f4881c1c4506020314074081040c086a0070165110702d0f660a64008403144280c0740c0c0300108001c513139915044c0000040082d43d014501d41180ba900003425424010b100602543d1101014071481d10100409200349000304030071503d5480a1070b0000c0644402d890070740d8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 803205053 1250 803203803 803203829
    0x1031101300506011209060203160804031d0105070501021303021c020604120203010213030614130809091f1202090a05010e040327081c0504180b0d060213 68
    0x10101e500c01d8500c0c900042281d540c0840c11000c8140803015000003003c0604110f40725244424040881c001d50301481d2040750051303180e180c10544038034008100f0001c40c0c1004010f000b40804207410456007211400c0c0105110181c0c2c0358400140e40a108a003c0106158800101803201c400302c2c80841e000c4d6482203c41c8500d90151040c40060003c4010010b50b1140d400c010801003000700c0c42910360601d20181c0090f05009120b100300c0e03101e1540d80d1065801503100c0012800c1b007034091800b00e0384072081010041804205850f009154004d01c142903004100d82d001040c1c000f40010482640d09641c1081c0031b07445d85d204c9034248c0160442e0710089000d809883d01003071144d0001d0140034180c803c800d4400f6036540d81e58804071200100d60365a0101001c203101502e0481004012090241c21078a0040800c000b080c82401201c001c80943c000030440c0901050218852100400052440800c40810898003140004659069104c4010880c0344000383d41ca900c444041b401004803014440845 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 803206303 1250 803205053 803205077
    0x13020a2a051e030d050603010609020408070906091b0c02030c03100c0306080a0503030708041505070c020f1f0f050d1b1e050d0908070507090e0106090b0a06050a02100501031101 78
    0x4030122200702c0301d5210f500103020383d030441c511590005a000c0e000030300205115030b03107480e000203e83c800d820241d42d5801040040c000c030000350040b00000c0101c0d050400100c12281100843c45d00500615003c2100c80701c0c0344410341d0f07810003041c0920300c030003002c6d00e901070560b5500384024039103e1071120100f410443e00003542c3c0c0020034202c6006070007002443ca56550640c0c102c90f00c2400410858440400c1d040c2c10070700ea4081c4c401e45102c1c81054803403d40102c000d00400c4040c0d1410120b551182d00140f01540858011072450200b88406040020f00303c50b03285401c2d2041e002c0c45002da04c01c54505a00c007203886c1c810407000140107029444440d0564080044c000030792aa2041c14004644100320b854401c107c203a2080744032500071000c4509004169036028107102080d484442c20356150080c2405105081c891400200031450041245000031400b280c0700001c42d00c03800701440008206140b90900034004c4142000900308100709560f16482c285002030309034180380d0300013000380100e1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 803207553 1250 803206303 803206333
    0x9090f160c0f0b100305031201212303300601090f14010e0d06060e0c0901090e06270403090605030105010804060f0e030d02030405011a13020a2a05 65
    0x5202115007000e90300802101d070f901c0751800c82d0300190090800d401924030000103d402032000d4a2002485514803806515280003031900c41303274024070650403980c41401200011452029030031a445070402e8a25002c441c04a668194023461200c803044d0101031079461000380c180b400f14200c000020f244400c89441b100700465a13040385000e000d48004401d00244202e45040880945c0c07014149000e40348101c00c48089071201c1030742d26040b01d42d90303211b030307004d1000861030948164010031000d8201e0030444078500080509000d40305000c0036016040c08580103403140c0324544840303005080c0008c20070510181e90500240b003204d0a4001854120011072028440c1089a040303030f00c165201c05442d2a580c075140028070342c80300c2d4001c4184e5142303203810300c0c14810700203403101070b00f01c1600503140c0c40c1504049096031400c851a11005940070f54000303070f564411424003000d0542d50300040e2155900b000c10740341071448191040200c580c408024032500415820200b21900c16030603101212008030503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 803208803 1250 803207553 803207567
    0x40303061215050705120a050c040902041403060a021905131a040e0c03150f130516030b18130602070519050d031a040c0e090705070b1e06040f0209090f16 68
    0x80894104c6c146404101c980380e00d508030030303040845032682c07a02e0b265645458200b20781c07195202013407262038204106042e14050000b258080000c107000d514254440d03440f0141c0f062490003020034401e0200780f050710401c005048101409040d10340c07038400f5040c0c110341c103181c2c1c1191040300c0310400003900081c01014980d00340c03801032212003602614003071400d04101342013810b04025030f08404120503501c000030907401102e000e081005030381300c580200032200030156010002d506014008040c81f260001c50403900080e40100400d0104039000003520b4007a01030300c44d28401178064880c09000f415440381154150340f006200c0c0c811a560b4007604d100c1a4252030004c12002240e180700b920400320307414650000306241c2c40341d10f850401800d54200240305864261150030015001042680400c4000c00c0c05a8002c01610302d081078044c0d540c01c0b403014001c002800c5a004613102e102009a14109406031808042c0061000415240c600c00c082d10302c03041114030078042d5038044240c0007950b0241c04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 803210053 1250 803208803 803208817
    0x603060e071b0b070905031002070510020a090b070803060a3c0806010e0106110303090a110414040312050a0b0d1202160906080601171005040303061215050705 70
    0xe0082441d6607042015a40100100c0c0c0300811201d003580280005000590428407071591a20b9181c00c10781460141880c0001202d45095801d1042080501054000810b81c5500705069030250340c031044000205e59944255104445800b0702041c60b03c00c014109028500c0341c8426a210301640f0350359014032940109038000b0600303140c07101c44400c3d00c4e05a4a040003001802e9031020100310f958480300d003490f0007426840000d4407400c4030014800c1c0c0345d00550041c526415903009602398205600c1840d02c520030880001c04920f0010000d900c140c8880d003258001d225040b030040d40a14060602070b04405000e00081d8016180c030002802c0d546082c4100c0407024000342c41c101841e81141e5400301495901108101544120800103c1d03000c005040700025010b9000045140d03031070104000d14000c4107801c85102071096518820071102c0008403005880420080461070313860390300b01500208a540c0050081c54500201001405800030754070510b5010715004006580c0d030307528200c0701130003001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 803211303 1250 803210053 803210069
    0xa030915110750040612050601140f0a06180b0c030c07081c0507110d14011b050708030411150408070906120206070302070e15010314070824100315060306 68
    0x94910016520b40002d00d420a203401340002031a10b4880d00d004a0000700710400312156440040140a803012410101c0b2411101b581c1780102003120707a002a942003940c0c010342082181620100f4030f0344001da140d40c0010710074208400c0d81d48002480356501c0f5402a500303a01103100e00c0d6000601e540000031101440a88145409003440d103d58003240d9030740c445101a030700d03a0042180ca0700181c0d500c0720105c01d00c6102e0101a003110601c0d040103402c0d242c81444c00350a11400381130100c4000d4000b000c440a403584080350556960369407402c141007000f050500394000e45078000400f0303154080e0008205071040e00c002c03548225038a5075010181c8500d40542d0a5802d0701001c030f0320050508801070b1030000d10a00503904070a446420340700150303908480003032a180300849040c4203960180705482082c0074208041d41e8501c0c0510380a000040f0140202c82c10740000580095070490380c07610342010401c0204480801c4558150045c003400081d610b01101100d2042c000403450700a00c10b4101f103680103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 803212553 1250 803211303 803211419
    0x804050c103f181407050901211101180605040512031603140c0d09050406170604080307020a080d09060b030a030c021c061506110a0309151107 63
    0x5850420b0203052035003600011503001d15807040000d0b0380303040540f01c0c44413098014207800d840c02c030400c584100f041e813000a03d40300007038032070302da03800034041c0c01c0c181d641c20904a490158080004076000801141da28a01161401d80400d60035480002001124001c0b1050401340c400d209102d03443e071041c50348400f400000b25444c840000c1c01041c041c011440c01c4e04106003401f0030212043e003041070100030000000c1d01010705100304e10300b920802c0f000d000700001c2020080b14000106954240152001e88401c602000203080940b0030046c41c02229404902c2030340b1007a09206580280c0401c40003141d400741001c010284034240007400040050f01561540040c003126003d0000c040b0700040c031004aa0440010303038001c10080e004098100c251106ca503507103d8a0890b0042c010404038000c425281c00840c0e0701c00c04254402c007642c0a50340034020000951100c5a000d030303404112000146104d019a00c0d00107400e15504400340803018541c801e90b882d44a41c4043c1041141014406596020342 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 803213803 1250 803212553 803212667
    0x604020a02210408030313032006061905030a0818030c010c0b190e21090a0b0c030405030114040b0c0a0915120f09110409120804050c10 60
    0x2205529503014401400e00b03034900b5898880c29815030788211140d801d5851045040001c140e8803c0c03041214404952500c2da081006c01d00e0300c1d89a00010b81414400c50207a0342e86580840d1460060004250040403520f10385580d00c1d00b03d2503a00030120100158011b42d10403440307820003048660101d08142e6401195021540c0c95504d0780303030007402401d54041d442030a0a20301001d071042e003440490403401010189640c02207040404910310b1940303610101800007070250346668039213400f91200324109079201c52112024034514083c41e40881c0c0d0642c00c041d050351650700302034083c6000b28001c4c00109032540d03410b0920741e6144604016000010000e10080003030581d882013a680269041c501b583d031000b03a000e000002e65210484d04a86640d40c0c400c51005c010b055480d111381e40800303035403d1100d1121502c55810080c40d0045c1001031201304c41c00a001c0000074070011417890340080450911000400008240c0c0c010f10542c030072215408050712001176080151704041d049003010359864544 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 803215053 1250 803213803 803213833
    0x507030c0305091923090105010509030c0a03060e1b2b050a050619050412030e0a0c030b1006031505040c020307020315090105011706070f12020304060e01050604020a02 74
    0x2100c801d80402000307012a8a2a039998280703802e0a00c50140000d40c0f442c108282030a4444429003110b0ba0b0200c41c2030f50303030026250b14042504458007401c1c131584030154030000c281050741c800300d0150702a000c0f004c08420441c20b43d00c0354144035844800c80f0800c101c40100410700101d000b0300c25501460f0083c2c1501c101061030f2500103009401d0001c500305001641e02d0301e1603301a000d0482d0950000c204011400d10000740d6210324a000920512443c2410340701c030035512500c298100201a110710103954903010070815000300c10361018500400c81d507607041102401700700b6121200041d19119002880601c02d005030816035078444600d5000380c1c0f62200700030080c400c12084100750301044c0813281c050f0340c0501903400d1401c0740503d00130042c9080c0c6800c60131944141c0100b000c56407000c203070806a00f800100340b1307030120f07003400d088003d44542642a02c41e000140705043c205400001004100050340c2c00000908070000c00a2003a522030004000c180d0084035040130050748003592244502c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 803216303 1250 803215053 803215067
    0x204090602070f0f060c02070b0d0906110a0e09010e0c16020321040e0702060c0711040618021321150b04020406021b031f020a0e130c110706050703 65
    0x1a104038001441c0850a82e210600e0080c080010380750a042c201e00ba40074400c0d10b003e854020307030551024010243c14420904006d01942c44c0540a07903584242e10810071400342d02140d1010340040700652507214400e0010444c40100020034005e49090740000748404007203004900500d0703000d60fa2401c20303200c1c440d45c0d402582c0003e07040c0d83c1031003800200300801c0c0c25155041c81c1178a441019690760341c1051407041c021080600340004540c020b508000c0c40d240400291110982d006805100c400075040014028180e00d400c40340309010400890300c0c0943c0580e0040022903a01c0c5201d004a55a458282a00030ba04c0010a6600403c480741c07440026036400700200199010742c0009000c06848000ca0101e07040381d04000050303404689000084601c85030402c9080200714018003001030551401c1c40800818050074401580108811000c540102c02e4107651020180411040400014440b0301522419400380c001c1503291a1801c0e25010220b0740c0700540300315445043c904881940e0403034204d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 803217553 1250 803216303 803216321
    0x10e0f040605150c070806071403100315020415080903041203090b1b1b0102030901080402030a06050a0b0f060f07030e1801060207030308060102030c1513080f18090c070204 76
    0x260703484601041c6030b51115210540781038012100358941c402c07000118a030510681200f0000c0d40100708100a059000e050f03080f030b0074170f4260b01d1030300c94446c007a20a07807040440d040100000300300ea1000307204600c02d6019204036600d2131a207000e004d484c51030989850405503851002c90300100018880c0c4243c01d40090034480c468549410003036a95001c0300b00b940c0140090020b80c1030306482d40c01180f0810807a00561044100381059458a6140042e54a108502185051250782c40c0001c0646d0780a121812000c6d41005c800d10491915007114030042c280925507a201e0b6800700c40045c3c0d2801e108041d5480e080c00300b1011f13441c018654800b9035004210311410b40d80106861411025607042101213402090303d81c00400841e03045140180031180028580390440d0301c01d12080240160019000d4280c02204000402036100d644402041303004444000c0d0520380c0000300500044800743c010034285e40300c0316050080035598020045c000c1e40907103040e03900031420b200d040701619160b404100c00e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 803218803 1250 803217553 803217559
    0x30506100c080a090512030901020d051606091a0f0603160806010b0f220503121614010f061d06041b030b0f090a0f0b040203090a03110a02180106031a010e0f 69
    0xb0240d0b64000290407161b9180e5078010a0f000403484012658041011181100d03143c10110f040c10904c1e1104601e078095450040c1c491600c540500080c4511f80000d44042800c8200d40502483d06020b851407507002555098040e10403580110788918400c250031080da0058000351803541d10701101940d158100079141e0f11105010000f640212a1241c0c99445100003159400c0d1803518100415040103041600044058820000104e08078008500034203450ba01c04000362120080a5103180184418201803c81a2801a001c95034107906016801c0e000000840034849545070b8090009171554460f2107000078080e1001040301c140203030414120f081010782500360210a880008469080035a84510f100350b403031180e00445400c9004500311480159401d500c0c40c01d04001c4c10355036a081c2103014003041540c3e07107241642e050a008204601d41c00a01d0b4003500502103071500c040c10320a214400100785002d030f030300c01445034a0020090b1000705071281718030741c40c1d504148060b02441103541030b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 803220053 1250 803218803 803218817
    0x71e030e010b1906170c0d0c0201090b131523090a0c1502061605160201050d0507080108100b0a0b03061801080601091a10050c1c03020307030506100c080a 68
    0x10745611550152510318940000c3c62031294a0400090003807412060a0040174162404020840d8203ca0450b0824a01d5a800189031800c00d1300481c01402c50a10080410519409006c030948032095101d01860141c3d1100202c02c00d11002041124003512400c0c80320240d402c0b0000821031a900803aa0000103201903411250180d83d0f061001ca9158100ca190190500340e0b50f840c80390304210445e8403482003a5040702a5040d100041c0150080c403c10b0707091036441c607210300216481403054130310070b098005050000e400c05031409007070300409004404c6036105001c41e1040210b414010204811000340003031418500b0088009002c1d400100f0064200f16145031610b140400c1c500c4240c02402c00c000a00380550500c2c0001040e134200c013030704400440b0b05105100080e500c03026810200b00d16800d0841e40c3e003131201d81d803e0801001c01e140d03200782d1100310440302d40d480c0c064000b90b104141550301041507a85c0c0e501000f5021402d0421000015403c0c00f170b0100041c81e1100800b110449800c1c884 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 803221303 1250 803220053 803220071
    0x19050d4b050c030a06120308010b03180709090b06060f040b030604020921120703080606070c0e0c090901091109010c020f190e010e190b190608040b071e030e01 70
    0x1209a50058070b001280c81400020010780081d203210b100c000c2c003200740701c0080d001c60a4500500001043c001d071740c0340e0f480010109020f0075110000828181a260070b4503c1696202c1c411001403d0a106c103640c402138a000041070740c41d101040740d080d0070340198040c0c00e240c10107441d80040d0304000c18690f0095800c00100748141d94007000100c0c2000d50548200c40d80b10106061411f10b22410448280102d0038400c90340002e4114980582c00030060750700c0c07a1500d07214104145c0c000d8641e0b02c00740b102d9100c2801c1c4501c45040400620045109840742502e9990343c03d60601100e440b150703070106800f02441041c250398030480e141040c1c180010110f241130402d04000459000b0b18184000180a80314420082512a0300070180148114a210201d42c40d2a41801448011610b0180703c942e0b55a96103000700d59408148100042c0c88010800482c0c3d1180c0c0301608003c0242d03810f440d0340500c1000510030710305c245907c40035160f0704080701410f455296000e0303006d03000c1d00301460141d54881e0b40b10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 803222553 1250 803221303 803221451
    0xa02040504050607030b0f060d0b0303072108090a08030609150a06020304060318020109050d0804090612060e0a020105040b09030304030b130201090801060b030612010219050d 77
    0x540c06180a1409080f090801540103000c65040850342c5000300e000031010405641d5410641c2c1714422800004240741494100181c1148104035000309a44540c0f002c47c1c0c58032403101400060054a521030351242d8541c240043c0d0f444a0a400050030040e0401c001981401c00c150301d1b0760400312003902c011034545140000f07490301c1502c1e00084010b074000700d0100403046d0306002c0c0580000448116464600c0300f034000070012180c1c0d001e010300511a5401c610700304800c08080310000c00d44044100055074442208845072921310324261000d81c18512a440c2a0501080c16203806070705850300c5142920f0520390510a40013202c500754180020b21000001c41c0104113000c0c402c11072142944003c0d0018030000d01a030324071340c0024055a1402a080c050103910f1070031039411200171030f480601030f1010085640a40b1a99a2000024208000007691250004054821803401c00014841c006402c00600795100c007a00072541044102c803a402002d0801c0080303013194021200700100080c0c02c150714 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 803223803 1250 803222553 803222561
    0x906110a170d0618150b030714070b07020a020906030f07140f0402030a02090a17030711040209100c021e01080109090201050705030406180f0803090108220c0801060501020708070303110a0204 84
    0x848044c075080d08103200c1d02a00140b04204909210b14100d00b0301608140399910745000007012081403001d032800c4045624050000c0d14a4140d0140071020685048c2100a454941c09203080380200000300114000349070200310841580000750007852341502d44084900c26040c1b4140c115006952803949500035240d034002980300324034982c40036035100d24003414080b5044840e80090001110000030010b07103000030040b100b4090300004254403210301c07440050004c3c4940f0304055440f00009800d00440f94109441c0c81c501c6008a60003221581078038160300d807203910340c83c4050000e80410010b0003102d581d0307441904498018541507082050703c0e0344051544e40207401c083c0100382d508208116441d1020111006010803042854803149800d4407141d4901a81c3d403e0382c14420710300300055580d220041c3c0c080a054003075524829003145400c0600c0c2021007409100708950030440085200d500000e502030807a1118002402d00e00c2c50f68404070740e90003081b84010380e140503100959001d40d403103000d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 803225053 1250 803223803 803223809
    0x1d0a05011a0406080303010605090a0909030e010201050c030121050a080313050c0303040b03040609020d0602030a1e0911010f12021c4a0f0c010906110a170d06 70
    0x880e0080c0c0c00308900c0407210700c10070910950500005010800001c011380341111400d007003203502d0317003140400220480d960b90004000c8a15103034440092542c40f050400036200280c008000c0e9456601c1181c540f407109029402c16205240d402c58089080b0b2010025420301410584e1620003482d44c40344016032040c0d8403000c102031803e18141c140041848980c100080c11001585040e00d0203c02200c00d02000384080c0c43d00350b58140380070540d200d1b52084030390380707030b1018045649250a0540700000c0c041c0c034404c01031182517182c902c1d12a00b11403003249402600507400c040c1803030310ba600445401c0f000300ca48504000a2a180c00350024031030001c2c044100228180302040002451100102e03114442ca800f9442800c1c50701c0920041c51a4410520044e0b90b0080c0b848082148004c2403443e1651402003450b00c102c001d6000c0321072003c0f80703146100000740c2e1081b00c0345070754000488107080310003100b90030354004296110000c0c00050084248061038644641848403040710f410403262198 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 803226303 1250 803225053 803225063
    0x50702180f010312170c16020406080618030412060209240702010f2f070515031b072a17070e01060c0807171e0405011b0809041d0a 58
    0x70018010442240c024403041141854400c2c54000c0405041500c0c4401520358840490009481020500b41c105a8801a03402030b1052204940e20840e8075510f49040b10042c2d04103065003803909010380044100d40c121460410645404401038584500940c001400d003603100302521054140c100000a0080d4484294102e640e140c4410340009421380308440c1d402010007211059041207280340703011050850300d04009a0120800c40a10a407400400390842640300c1c0415082a114591040080d03105400b84c19003290106075030142d0a089000d881c070001c0900c0e00c4a500150ba0307000516040032820741301071014480c4d65039000c007405101c10490002489400402d01400044010a040c0c2e00514203844c0c203601005440e03c42140c80c0c01200c2c80201045e541d082c2e44a110f000c010107a0386041018500410300b000c0c1824a109107520070312516000c075031407070b0094190b003020400c40f08045401480851405040e6000c010080003403900040100040e106003a228410400004c58258814 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 803227553 1250 803226303 803226331
    0x40c030210110a030e011404080f0d020a03020d23030f15012a06020408030f0a02060c0f0f070303141006020c091003030f020a0609030905011d03070605070218 70
    0x540140701080241020040c2441081100c0c06649507000907200201d58141c64101e00a410000c0101c440800e100400b07940c1c148041000306070030078007290744800e82c0c4104e030031146c0c8103d00340c3c4203030f0702d6011404019002d0b8001c2c441007900076004140c260340b155040900d500c080e0144407400c500c0c1c6c2c1c1042e82e200681d01c1e114000c1021203c065220998007082c01d0030915503480110034190071001040103c0340c2c161070031340c20217020072030a0380549019205205c00d403912000410512000c980129204e20010303c2404041a420610307002190b01c4000030a0b2480d103070190301002e102c4a54015202101010381c0d5050b0001c0790010011a1400342c0e80c2214140060340c50100e000346800800a08648962400e805115000c0c0040c00540210395260030000100c9920340800c3c2d01701595810b016040c03504115045c8105940211124207464090320b0340c04a0b10116043d40c10303c51540f840d26501a807100c041441203a001c0c0018003101417004109200e03880c0700c81c0c0a01415001602c203240d488800f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 803228803 1250 803227553 803227559
    0x91127040b040218010b0426060103050307051b030a0206091815040c090b160f0506010603141501091a0702060409050411031203221212050603010b030a0611070b040c 73
    0x44500c4600040003240041d844e41c3d418500c9100c0d040c40341d88070300320904070620f5034a10406070010010058680c2d64003560002d41e50b0342032198817980914800c807502c3c050490f8070b5120709506048210b001c0c1000d0001d04400d011079081c0300040e4440c90740c7d5584070200b1060846442580182d40d88140149164400c04145150512083c5c4005103410003d00c00350320f5003484041080c5090702c1d261042ca040301d41c4c4100540c188105080100f040180807402403600108100c6e8060300320a0030408a940c440700207554600c60b0703450460440c101c0307600140d101c20b010010055080100e5800c000604040c40c9001d4040c0c4c0024026849a44180401620b4108200a00c0201800e00d20303203185c07d5010b000615a80303048052544002402c001072140041851005960314001c0c0c1401ca960100914482d0703440100c002d0210708200815040702d604010015001e41010b0003450107030900034009182c542107590729030000d844111480c3c0383c5000d05201802c00b10b02d18484a40c0114002c1c00d4140301541 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 803230053 1250 803228803 803228809
    0x2190201120213171902090a0e06010914070e0d12110a0f0501051608130c0902072006210c1e0301150302030c0711040b091f0801091127040b0402 64
    0x1000d18410351250441c0030340d9a0801410480c01700340700d60407120304200d50b96141281e4018144844005007502c2400d002103040c0103140d0107010f200034906900001030b502e41d1401c54070401004e0b031258100c9546407100e40004c08940c8449141c00322420120f40050b40801054900800c2000a4174413802041c450380c2809003c1c400c40c1d810044007c0550307030f0304400120141c04400c0c003910008900c0800c2641d8010300102e02000400740045c0c4400790340c0c6c0d01c5241001a060b250415030107060310102e038103803513051800f0001c5a08401c500071051003c220b044007a8403685900900030303454035000b0054803030940354401e001e041d0342040003c0796842c8e5041080700b03072201c552030070007005051040040c031500356441801e84100d00c0c0d1082c80444c0107290783d0040b03005000207501c01d54101410360f00f07020380f2140e4142002901a010390940c000c81e56030307990303140c2a604a00c40191440481140c80b03100750502c900007a80340c1c1c00344c221a0320500342100148009080454040d83c00d02c0e000c80034070007149 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 803231303 1250 803230053 803230079
    0x509070513061202120c0409111822060908040608100b0304150c0c060905060105010311121503071814012702030a06030506010f06030c08040302190201120213 70
    0x11080c440c00300030480c00e00f6001100320800c2c402c007074402c24694009945c0844100880148204083c1c0140102005490700c50b00c008034160f0094880c0396450382c924268a99200c400b486040c0203040407101e0f10180310502c5079092400c1060710600d40781d900c183e0103c0c100f2001040105155a1103036180d141803003441d40040d03910f4100d1a13070f8030b804000340400f091119900300941c0040040015507130030038103004c1e152840070010040900f800c050400052000110301e840c100d0380f0a0304c05000d00c0032050000c41e49072080080b2031940c2d080c298080342842c0c01c280075401d120200601159180c540700d0040140389260000348200c90b0380c980c3e8005101d02e20a00700f5500502c480503061542c2c0b40f50003000d66070542017441c484583c550120010f0002d000c66005400110740260683d1404d58546100c40d030841014000d20002c64100340000040e188500340e154030540c0c042e8068407030087c3c0800302402c1018296400ea04006a40030515030251041c070050000d040100003c2ca410361a203030400c4500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 803232553 1250 803231303 803231329
    0x2030f3112180807030206132105061506270d06060317161209050d05030c0613050616030b060a0833040f24031103121b070905090705 59
    0x3414203440104520307880001c095050700d50444503a5119540e4a08c50f51041d030b480c0e401405040108588240c500814241e0b445480303000300c007542c0241d510280c000b500074a00f50300894012004000b80c54060b007035220f404083c00d200d0350b49600c614006a0000300520034003041941c030703d42e450804008000b821150a01e07600d0b0215911801e160003030740310046d8102288030282c5403c03c0d03446a02086403045076a0005000c00810303104501d2400e041c070030343d2a007001c04006100c0c070441012440005a4549a5084585c0b14000300401c0d0754070b0a41000b5211203000180a00d0341362560420203641e000080d02088031740390785040003441e04000b00c540d10700079202011817000800712040e007103860700d000d0081e183c0340580300803841c1d80c1800b441d00000d0083d1500d49058021025952007851001482042101d0050001a40c0c10a0003002c060702d030300748558142c5507004108444048240c0010500740344868000580d48100e60319803141c81560b0b01210a030950b03811502c000c0c000ca01c1c240014001c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 803233803 1250 803232553 803232587
    0x20c0303010f0e25081b0a03020d0b060f04030210020106050a0b12060d0309121a0406060e09070b0702041109030a080c010c090f210507081b0402030f3112 68
    0xc8070210a03080071000749050000710400000d02d00289141c0b801404018071000306ca035180f40d84502030040100250090b480d251401801c080f030408171850000103403070701444031704049403a00e4036682c01c006040c02d03c01032410565403200340015903540e8018598004107000480c0075604c04124140100400c0010711151080740d541d6401ca0200758401c11580039108140c0525501c501ca03428030307010413544005080c3d0155428020001040f000b43c11031000c503a080342c0c1c003c0f200d844803820680c0302d40030b03406401c50b2554181301c0503001d4580394006900c40964403554602c0c3c08110000319040c400c62483c00d030f602400c00030b8103403e11502441041c218501c2807902580b4207050503404060324209100f103240d1a0307041110136800c0100d100c4c94038440342e409021101416951003943e070f15143c003846491b40348682080303c121142454001c80e403150080030703003803180360b0f03035003002c070891805951603072510549081c0b4441007260280380501c0110f070003402a01b200c0c0c02144401009203440c0c600d2001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 803235053 1250 803233803 803233831
    0x91009020d1e36080c0a030e010809100f060503190201090f050d02132c0c010f021921050d1104030b180c0d14010f0c14070501020c0303010f0e 63
    0x65100c0c600c504020010210f0044910710060000902c1e1580b161824054241d8400040c45008000002844000c1920a4403024228080d120056413060400c44903040306420844040e0740742c0c1015404103880300000d24000030342d2910b400c0070038039022012030b074000012000d41015040d5030301310007210014501c02e01d120641c24140070100306c0600a03480000d0142c4000d502c03041481c1000d4200302022403901d407480f80d074001401c009140e0381c0c2c0c4810f0021464002c040c0c0e21205948541502001150285c006044400c8250006c055800200100b51341c0742904070712079040da800c103c15961488003241d544c91f460f881084408411901280b03c0c1021441c400c200410000d50700070360150340400520300300700588100c901031508140b61104882d0344240400480d10800150a0090f02038880d103400800107450305d420600e0480e640501c03044045030b524000d40c1c44110105000b414210722a000240c100308c3d004101a01d550400e0701303c008070b03120b9217000344074a41d240c40d0006e0340008104142c0ba = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 803236303 1250 803235053 803235071
    0x32011415010e0f04141014031501030308070207150203090a08150606070f0615081501210501110a08061302070c0e090c09070e100305060f091009020d1e 67
    0x180446042c5001240034018002e10000c0983d6241d01004000409060f54440e51400103026000403603540104c5910200c43c0c60100c0391b6080000d601a45080e01600742030080e421038506485006c0c1c010a444c08602c00c001d80450700b590588c0fa07900d00f920841d00115240c4218108010b4292810f801086480d405411442d440350461700120f0f411207800c0d0f5a256031021507050800e69500c2c2e00300003402c80f50070048400403900e44070800c0720445d4029010b5170450300c005078030480118401c0c840e0750080111f6400354015950155078030004d50740308500000309001c013641c0d4942c4c503402811480011801e41010841a400c1854403d0400d003e0070b481180352111640d24440004200d00480081040c2c1c00d0020709510001c0202e980301e0a00141910038510301440001d0210f00c40d07584150040b0460343c2c41d0072610303009014690043d03c006000c0d4142c00c000318203210b05164000c0c8020901113005400003210301861000b0304800035182c2000c11102a03c1c0c03e401d2045440e8107100c8242890b001c644 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 803237410 1107 803236303 803236307
    0x5090114210a1b36031b0b1603090503030d0606030b0607231e06060108150913031101141608090a3201141501 49
    0x8620250340d403440801d099650958074602d91611820350348400c01d01865850440d92008844260b02200c999140308a01340d405104d4007982c8004103040c0107104c2800c0d0110315060051016007001c9240c051031180b20310844884441c08a002c0644008040c400d139105401024001c0480751144021902c59008054074402d03100031078900700d41c2e02d40074285074060341c10f401e070040b50504e0995074003a49918100e060800e0301c282e5000d01c01240c5101c01c40c80c84490003940d1800010810f5280100000d4842c8801411b1300d030460001c0d40c3c014080d540c550118951002c1006002c044110892605035900318000580c0c059039420102d03035508010aa00e0131610840001188039084151604143e40d001e20035207220603c1c1c3c0126030b48402058130110a030105049411804102804c2e004081d410710340c0f80040c44406035107524007220640300360702941ea0021031075048420b40d0b0b1008000 = true := by decide +kernel

theorem cover : BRFrame.Cov 803057553 803237410 := by
  have h0 := BRFrame.cov_init 803057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 803057553 ≤ n) (h2 : n < 803237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
