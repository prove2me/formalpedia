-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2701
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:29:23.882437+00:00
-- url     : https://prove2.me/submissions/bb351f03-82a7-4bc5-9357-47841a6cee9d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 485611510 ≤ n < 485791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 485612760 1250 485611510 485611517
    0x60308130b27030a060501032105071e02030a05010e10050c0a021c0e030115171f0230040c05060c100f06031b060e0f03100e0705040f0608060c0a 64
    0x24a01e640000120b41c181611454142c000c0800c4180410707100d22039140214060404841c084100d0030b043c64142186070111418404180400780c0890200710101c4d43c024074800e01822412a0350000a280c84480000206250700304440c00902c000045070300700b004c0040303083c10300c901d4980140400e554010341050b4401070740420a0001008410100c4240f46111800c00706400701061000c24292a03000914120710b03841c0000c00c0195141032024803007581c82c10b102034900801240e14050020200c040039080d041c0c0c0102c2ca805060070030440406640c84015000250340011140542e046081100c0580c0d8001008100094a08184041703070000b50003a0090510400748607640c4006041c80d940f54004156924404000900c0c0340080c1b0100103180d0514a00092800704c0062a5070b40204003140521030400741c02e6046d8030b00141c18503001d540480c010a0a00440b0010b40c64074841c0c0e4052b55100341070a15030340c0420000e9001e0f1007940e1020303090314030f0366444488070b40161085041c41c0001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 485614010 1250 485612760 485612797
    0x90501090e060906040b1305040218012115020d05180d0e01031a0a1206050a09120819150611011406061c020f040806060a050102070b090f04060308130b 67
    0x183c900152025801580107000003417211008000c42d6005a00c5020000155514001c2c041585001264100b003d42220a4034a4943c1003c243c1074100d4443c040c3d406000c61900304402c100038040c180d9540741910744600f15111200c5110400143ca410749240d04064038994249001140100d2460011282a200e4544201200700110001c00808101820420000f0304114559981040800081180c0c0c2801c100b464002e00345031003129400351000000c81d1030000b41b140003545240900150100d10b0406240319641c48424402034144030300f91600c0f042c9802080040040c0700321242c4180c840d2680d50060300e02804040c0c038222200d00c08290041141c19002440600c1c02c40014020110b44d1500c1c014619020f401a205030303042600480801c00f0041010b00c511101003101d1644842c04075031500c100c516000002c0d40700c070380d580108010000002184041612903a501401070342003c0c4c402c2000030307501d0800142a0300418803026418507078000029104800d0000d03a5400c030604a1000c40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 485615260 1250 485614010 485614021
    0x6050f0904051f0609050106020d0810050a050103091110020708011103060a0b0c0304030816140607080403030203100e041b05120c0402131e03110301020a0203090f150d02040501090501090e 83
    0x180600015601035801362507010110303404055019260003424150002c01902c003100d0009400c004004040b610081002e070000c11895681303800c52011a0400e08000544c1a070301e00341610740f00c540e0f0340031a40040b007080301400c2d4035074000741c0c2c0c00c1140d0700e44000700042c0043c25004c1000e03100130b54007143d00440d151818031010710004010150740d68038408480c03030b05540383e8407020550000f450301c1207031400c10200c01e01444402101140144000703c098001454203040c0a040c1c1103018001078105a0b007c0006804450614100f601418190400c488245098a00300c3e4004401c2a01248206010030000843c1d0030302c0140301100c0c92140010301200b10f5400b052000940004540d0040e0103951200091034220260131040c5080b032241c42581c0c96401c609001c41c06100c0c281c80c440c0241e20402940c0044d680c007000765652603900f102d54400b20701c4c030744001601031a1480c422604081e80004c44540d252000e50050044038801c1c1c071809225a0303641d0065400c88464801d507100e14911390001755 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 485616510 1250 485615260 485615293
    0x303090e090102120a060321080a050c0c01020f0306040c0e030a2a0b0a03052d04170a021b091b0a1202160308060a0305030702010507170d06050f090405 67
    0x41c1d126500030001402c142c2e480d48443c042d00c00c16142c481a1583d211803d00074820403950150044880c004100e5541b17040341c40040031084000e102400e0a40c4d100081110300118204030b403a841c030840002d5487e980c0d283c4410f0140d620070340740e980c4207902c3d1081e0003502c41e00031000f039440310400a01130f027424500c9449008000100045a042c80d0880362a03410485150121840140038440700e01e0790be50390603190180440310b026060351544080000070718014220303549088003445040b0750610700e607162481c2150004101100200312260089074188425030700055440d005984c44620306242117250080c881000001d9038650340e81c0072403081c0706104190900c000e00701c03c001e5141004007095038141500c12a04a1491a4000c22103184e9841c01e16030710440c015005001211201c021074903554505650b44142c2c1e0b0000e05000e404203001d800c2c0a10035802c05600301c00240125584c0100d0070840000f401c290080f24803a0b07030354080d801d0301d074102510058807d40e8400d000744510700100700001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 485617760 1250 485616510 485616539
    0x27060c190e041a01021b090601050f0918060a0b070308070c141024080c120724030c02010905060105041107020d15050624030a02040b03070f0e0a030309 67
    0x400500210741c51080541d141d41c4241c060412903448110511490080024280644148400a1001c00415904090351070014460301316a090919a80d5084182d0400c0c419001d5103000c0c2c2e50184818601ca06c401444d030002c00e218000860b0285005130312080001107074003441d1307006030000d2109800100c041c0c2c080c5c2412400d01d4000e01c11444070340d8540f4403451074000d81400da4209991540b01179000b942506114030800d0301c1c001406d82009003400c2009584510000341f6a02c04c05010100b0095070314180301c0080540352610f0740d0304001c1e0121440260110311810f9100000c1d1411581741800b51040c49a901c8041e405000740400c1d9181904110161a07080003203070104108000c40c00040c0c0e01c03001c034180b8003445070402000400300c0c00f1003e011102d00520490082d48010b2000f010301c1e6001c507040007030b98000e03503009440b52610003e0000a0250b90088036021000100b4001d0564110414055103040c5a846048080c41b07241400110000c5202c02000f060010340c1c188820f20004080c0e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 485619010 1250 485617760 485617807
    0x330c07020d060f0e010c030c020a030503061504081e070905070c12031e050f0f0105100503070c08072604120f0516030b01080606040219030f0605040527060c 69
    0x129140b80c1d82043d20307048034043ca082e00401da6680108101d51038041c001d500f41c0c2107440c00078212200d40b44c0c4000d441c41c44010003035880740298003420059078480b0401e5030301905e5080110342d42c1c080a62030102200c142101c402d0320070320620f180003410040340d00555215040c542c0d11040c041807140d0b28212035074203801d210410306441d03214442c0400c100310301c0714a003460720a50110341800d000303500c2010070a02a00940c900558100140015220054081d00303102d840d24010b80c1c0c0340d55100089a11310f0000000800c90400001c80f8014080005a40411540790000d45c2c1500d1241d1940100c440c81140f0400101004011444010400d10764a0a404500400a440320036401040308040c00c00310307420454400c08400e0061100c0107041183c160300c0402950114600861541d22140d4005500500c508041d02d071b1906e006880b10700d0300900300808001c0c1c01030125051103c1540080e85045d2005290313134210041407072660100146443c081e001a12115151515200b41c1d1603c035007880a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 485620260 1250 485619010 485619023
    0x13061209080a0309110405010302090f07020c100915111f0209090a0c0207090c050315031e01051f14090612060705030a0f1518060305330c07020d 64
    0x12404542070000400d0071189594002451031094a041c14403200c802c820079018500d01801840140c603080d40307654010002188910740c03689c80581c1280742c1000a50116000f81e04910b131590029040f580c180c060320801e501000504003000021240d001403104000c032154440c2020815500b004a4040c411880e0610094501040348001c90031044c8252921856142d860021a900da5418000c400141c40101c1040c0300e4202911802082400301400002c100b0420031030340803180e541000b0101c0702e002c2100070b4200800390700100c13a008200848030f510b603d00082d110358031880c0d000007010050702c000c0c40345c0341994400003041c0506904024001d64101d91807016a50149408103d00ca01c261250303541c6c0c80d6640f510100b41e500782e4541144002449040a001d4044c60b10908140e8080e1010740c503103000d80350784640d02d00029282e03550010300940200307014424800141c1d41c80461a00d481403400a00003071007010100b810504460010b480781050241c4c50040c9800505080c140307000b4907 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 485621510 1250 485620260 485620271
    0x80610050412080a090b0304080403110f090f04020102061e0a1a0604080d0e2d01020c120604120c0b1503100612031202040f0501080a021603050d050c130612 69
    0x76006818141030718103407803d10f4013042c0200d00e00c0d4001c0b01000502040ca011904504207a40da154003401140001440ca0743d1030005520552143c05007a4100c2400510001030350425001c06a2001c000fa60143c5c014001c0c200010840e400d50300f4509802a111a4a01c01c2c5550301241d5500803c1000c61340919409001c0a0380c101e942c0e514042c2c0061309021029140700140428098100d11038444807074000c41201c10b03142c400d40c4110114100e02c059101201c80c0c0044a0750040b4204102d03082c0c01c2d40d000301d1490182652100014a052103284100d41a403151444208103445000031034500804601c8424000b85151203000760f40c1791340110244c1243d580519000e01e4100392a03140e00b0000300c0c078600581c840c0a05900c400115204150305070304501e494100580b01040c0b98180c0a45414041c600300412050000e5604641d40914003030b11015900c096031800a046a009068440c501c41c28400429020020102200c581032501410500114a0680c081d6145d584800103400a20b9840 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 485622760 1250 485621510 485621519
    0x50406200f0f0616031b0804020102010f180b011706070c15050c030f0a0b010516081b07150318110409060f020913050c0d0203060604030c080a030815010806100504 72
    0x2c000303440c1d01d580340d03201070300c49840c1005201d060581d4002d640f0041504101320310401c50154030030300400c1d2900703160010b9103a80b28001030303015194807405181c59500e0444034a040c0c0ca040b550002c4001c0c070032149640a40d0340e4080e0f24110705a07100f00d6110769000341c1c0106500c0b9002b01d1610103100d06c1100000300f8607102c4d07040c000444008444601d00c07180000704100d1413602000c8090360000c6412000c01c044200c110001f419030054129090800c51403901c10b40a000740901030f11110001c600d414420001d9040c411078030b906c4103104606000c07640c24100e01c002c034041d0098080040492100155078405500c3d0800070706c200801e031680250b521000038011a0b06030061a10038005008090f90300c6031408140000300480c00480e0103c0c626000070b0282c40908201192000f50b9142409622600c6400020b0024842d40d4030003049a41d030990000350140c008038245c2d01140c00b0303803039440321940d604020b0b4000003442500c2c2170000d042c440c00140e007407400c1c103088006218140381050030a500e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 485624010 1250 485622760 485622763
    0x11042d03081305091807142404050307050a03081207050d050906060a06032007020303210a1413120201062c18060412030b040c11010c050406200f 64
    0x2e040c07000084054403070520550811070420340c0c0204845014011070501e02d08a203807551b000d4040c0202c0c1c281070760b40740b40b51580e5034219003078006600c41554021600d03650011003240e0161140500034040c0d0000018185026918001181d401101c418507045034a070600c0b408400040c141c3c414048180320560014500307120300c42c4104078010060025040020401030132412680c403280c1054200789048900c18074002c0242e0b6508804c5503400d4a8203a00d100082c21801060702c051001e204000e0074550300c0c005414018001c4400715420881010022102c00071a0400c481c440c501403001854000001c820291402040c2401d100004d42c0907240e0701041c0a00540e20040341010307015a9004a2814000030f0560b048072481c96080721122400003540c2d2542d43c000c2c409401c03800e00480da83e9801d07009400401940f0360040c03080109c60300d600400b5114052070380050000750f00c4c04648000b1680124121000d550103034031420190604a50f00911120320410116000d0140c0407114115000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 485625260 1250 485624010 485624017
    0x90c03060506010210150909110d1a06010203040b16150c0c0204050c03040f02090703021326010c050f0c010e070303050c0d08150405042307050411042d0308 69
    0xc2a1004281c81c1402400245454198246246041d160540500800c8419091039003199030345440441e440030141000c83e42501c103080c6054020508503890002c2090b84003003403010740450a40d41506480318401242d50b03020702d00076080e034524200700f620203401d5501800b90b038207449010041c4950700100400c01c140c40010080c0000300701303a0f060510840c60140a4160b102d080000700c4e07801c524003919607400d80b2105032006400f03424450041040c083c8030360111880c00340f4982100390301d1640c4042502c81940c0210a0b15501c0c1c0d400c40048101d884113000d0301001107916038400d800c09541ca81d4010155100f03e004404a660b202d68020f040d0303005121300b2009500a0310b6a5446030b44104100341403484102c40c21040240c4002005400e8200c0408042c3e040d200343c0380002c0e02c2da0b90307180200804070520300c0c0b040f01c1841c0f00d40040404800080402c02d07102d00b51002c2c0f010409140d00c4014601681c0540e030130100101d0707410348401c20324564544812110105003440280e90b622840490352 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 485626510 1250 485625260 485625263
    0x90902090d06240914060907020a140c0a05030f1225050c0406081f090804030506131b0501081803120f0406050f0402030c010e0111030a0518060c030f090103090c03 72
    0x11a114080c00c0f07008a440a600500741c0550900ca508080382050703500d0300d40200b10911810f18500880ca9492007000002c40b00d540c00342d104020203030403c803401c1e0303a00001a5218410501c1e5840480c2c90b01300030801c4000710100500500380500640d00f90b050607040360342e104014180d100400c41c0c440345603200404070747c0d000d0005804008024018041034030010741041049034080780b92030000c01d18039a41d4041c5440076203000500540381d4900b0401601c07481c1d00140182c8642020301031010b404680280c00181b00d44801880c4074214400b90100c280389100701c60107c0c41c9800010009404007006949421407501901d15240744404000c100c600191a400a400b0003441004100031a80c402c05410541000c40301700c107864540d000075034074883c201360513040002d12100c07908180d0080c07a00301190714110007580d45845019500800e55001200b0011042400765031020442c140303d8101e515074442e080c040d500c0c000c0219020316156000903642810942c5c2c81e00040080341c21060bc034801b45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 485627760 1250 485626510 485626541
    0xc02011206060e0f030c060706020d090c03230106060905120708010c09030c06020714040b030f03041205060f220c081e240612010e03120405070b0a090902090d06 71
    0x8603c0c920911980600300c8800c907000f0750000c19840c00681d1840161941c09a01000c0076984650f1a060380c00600812180106829a44c000210400c82035410348090150070380360210300d4400d030f103500600741e56041c400d244c08070744501414806030410024101c08011001e04480155940e103400c242140c0c42d40e80c0100000342c400c40188108101180c000008196920052036100c1c01c0c0401d030347c459055034a24502c11550740c418044030f80c40601001d2000c40004055030b8985503a1006c18008661050084901c2d01600340044e00040c989840b4a00a130315100d480842641c00c0e00b006011640d840324141c0f50740c5001040051056000c01c06596000900741c00c41d48844190000c0a150404d00d12846000300309040c143c0c5800344a420041303070720100c00c40300259900d040701000c4c0e0041c03800200300003503404000381e50071041c000603000c1802144120200c8800c565260200707622806886001c44c00a01c001c001040b41c41155009004101e4000b4040055240c940d560003049800401185594 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 485629010 1250 485627760 485627777
    0x9011413090c02210d0515130f0e1c0305040206070507060c0b09011a0103150504060f03140a15050406180c140312091315080102091302190c0201120606 67
    0x28150705101509121407042d00c080d9085504498130446801303212400c010301a690000194040a840c4e504515800003030070b00648034004e08080c9016011030b400d12400c140c1090035844a60350002410089440c1201e0f545841c0e10540310101c1c0031b4907018006903030201c0c0510500001c030308144103050060080b07807900601d04190340380800124000611041981c0d1502e200c410320114226020f6a1141d13007440d00150703001c000340c48000181503d41106030000e00d015004180109400041030a4074014240d0110148019000680c0c4508141c3c00034411803041c0b12415229a550700010b4110388164804500040e64694050408400310401d662601d03106c3c00c01c0103082c0303181012081840713007075001c0c0080005074448412103114001080f40903c11102c900141034000c0d6000442c800238841c1460341c0d441c0c1d00d6100a0107508185c4d1118800d02a07008045a035802c54400c96010703c90000c000f0065408040381940e0410450ba000d81c1440541d0184042c1244c40c0d206510160000351260000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 485630260 1250 485629010 485629031
    0x90b030a140c3f0709090c02030309070801050108120325120b030609030a0507143702010e210105180708030307020a0b07090b070311060f0c0901141309 67
    0x4140c100d0314488256825000b0303584040d0300c0c081c82502c00340c1c1c200c0e41401446031550304d0200c42e0400c10794420f2a0b09840e003019844035a50110095002d1075010089501d0940c895402c18200c0b0400e104145030355000910241684480034003640e0320101d820590941c0700f800a80d0154910b0340c039000607000401610f40494403d44520071020240b4042d0300030103041c41c0c0700040950ba40300304d06100702800f90100e032034001c0100d1100e150801c170b000130042d61600c03001c028440e00c6540c0e141d0384030703645001c051146d130505590500c48200310301d40507984c180350700000c42d051148582d2403010880c1401c3d00d60038800e00008090003024001c07409003001d18407144010000c0717802c0101c1500241d50507002081444182c0d50300141170172041d50808400c072107a403140030b03060301d1a221a900000d00e0600219080d014103800140c108902494281594041e039502014030003050030440d80740010307c00070300c0348a00c20351050703810032070041d035188640385000d4440040740700e030200a0b03100e0351042e0b071244003548 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 485631510 1250 485630260 485630287
    0xe1f09020708042d121b030c031412040902091c2d0f0803060a0315060e060d150f0908041814093d0b030d050a090b030a140c 55
    0x5030131440041950001001648103d410f070582031203441c07400390700b06081000388a10540d192680304410036080e5461036881c500720514a00c40c0c4420380d03103030190868003a201800840c10034028884400203d00e8581056440341c000e40182c0b110a4006210315076045100411412801c001c1c3d005101a001c208051541c10340c0010b0f95901c5a0032030380c42840c5e060000b031366030602031200551103031021f61a5a06d03403010520307090007a0b0018210190301031403441e98030000e500203c141d40340c09125000544d02d0703405104106010786030040040185100b80101c4803205d900c80407440c12503203400304510000d52520346068010ba0002c0440c0f002600841d00c80c500e8a20403c281c4a05082104d03001d0303d0051394a40c0c40d85075106010210003c01c051405a0703d0554400443d80e000028200036004480520030000f007401403480c601a100f0400003c00c1140200141c820a400c81e42c1c44c8800c183c00c100c26808280c00180000c0c0c03038540c6680102200a5650b518a4400c1d4405c01245071201d2070b508650 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 485632760 1250 485631510 485631539
    0x7051e07050a0509131a0106031401060f050a120605100e1806010507150f0504150e0c0a17011d0303070212031302010e030c0405010807060908070e1f0902070804 71
    0x218070880c502c0c90700f00844d880381d100ca03552040355500211840318403070501a000000461300c10f2036069031800040342039901030340702d0240741052138500001c0ba82c0300c03031b82900c10074801442030020990074041000074038803c1034150b01362902c40038085080c56690f0013140480010b200010042004a42d2510560130080e19100e01c0c003075143e01a4040f0300300350b40080d10307603c80c0c020003900c041a80026080c01c0b1907142c00405641c0703000c6c1000c101c54a0141051002c0c00d2601e210228150b0600001d041340840004007428415001459080320300d03d030130002c81079055540e0748003005540716420750700303851081070303d400001d060500995039074900300200a040071103048450001420a01c28001c48201d804020184580e080c24840301406030f0400191500100c0a101c9601c0350904001160b43c00001c02c0c2002103505607125032072050b881e44005521003c00b8004c440e50162844000380015080201c44030040e09a502c46603009600c510001d0706036400520103441e00c440c00a01005941c685211303d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 485634010 1250 485632760 485632769
    0x3060c0908100c0c0f0c08061503010b0306010e13020a0503030d05010314073c031419080315010c050a08030609091915020c01020c0a031e02060f070507051e07 70
    0x1000003a10707083c0050601107040c1c101a0a210304100c901080102190402c8080c1408508540407441c2111814203080c62050040d4069401d000303c2480608000074124103940180d511805213580d070000d1201e91038030104060764400c0d081c03400000c441d03c092000f08908091a4008182d542c15800c10080d10801d505811255070302c2030504018100b0305817503c1c9003110255030b09400c0d038028120450110a03805d1546003074244110000002c00102d45403500d144852001600c928030b144904485164040320000b9106290800001d0100e10204103900401d020504194001c0040c03901c42c00e147c8104503c04460390710703000003441402d00d08028040e51011550b0700405000d402204034208001c11407a009100f07012140d0b80481918498041ea41c2c6601001d000719162a0b520612640e281034444042d00490701c03000701d0022480c0e9103100d5841c0c4007016001441182c551850746c03103403090000d2410080040a204050008805100c1800e03406111000d80307842d2410449040e081402d00d920 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 485635260 1250 485634010 485634043
    0x40b041109030105010e011404020a200106080610030f0f0201110a030201020a0e0d0210120204170a020f0f061207210c120c12020c01060902030408040e01151e0903060c0908 76
    0x400441841d007015142208007a40e000d82c494440035000c1c1e81156481ccd18030107807000001c012000a490561022081300c00c044c0c129662074540c1c8000e00d0f0701012a000c00b40101400d00094800f0a20140300c040015106161608180100f02c4c126400e041c488074040300140d400150b20403c1540c014581107040070115400310a110590340002c030504d410041410602560a40000303080c3c00c40d074161002004074940c40e444040c0140300e850f44400d880c5200724071031103100004404904017003801244e40d200250410785400c070240b0040e10b50038001011041040700071500c240300c00010001c0c01c0807807021103002090b403180810010b01840340e070401d04032619207018032000145030301074810031210070340e00320040c0d031080301c80c00c0180500055001044280e000106010421184400030022260b20b841401c0c01642c95040c5814100c001c480c0c0c280005419500c010740c00341011161000c015264101b080d240341da00e07070300e4a003507078201c0307601d10301103200401c4c01c1104420510000c2146520f100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 485636510 1250 485635260 485635289
    0x3070b13060311030f0a060302091e0a020c070e1902070606030209090d09210203060f0f0a0902100f0c020310020307020c041803080903040b0c011d030c0a11040b04110903010501 78
    0x315450750f11301009180e40112448500070601881c40c0d503015002454016015000d01d10340204045002580b040306210340c0072030400040c00141451081c1e5585440c04c0000e000c0c85440d1443d0b9442602028000702c0840602d10145a00001188028000284103000200e02145940101700c2a003900510162094200e001c5e18251039501041d0342e0b0503901054481c5140d15070070b00aa43d803000ea1080000d4051103210148201b803020b00e00d250344110074210f0420b01d540d40b13001201060743d1003180000d421151603080c102206d4019040000800c05501d009460018290006071605000c0c029509045500000b40010240c2c14002c401000c1001c0d00d0900045003400c0101c8900440c008002c4c1c20001118080703180c00000340100c50007070160440e910b4a4a0200007002e000b0f06000c40324001401c100c0300c01001c00000801501c29a000b00070251103161001c0e140c102c2ca582140414651050b81e9400c000c1c0305903503c0c0b02d040e82c54020034007120381300d00ba50018942140c20603040940400c4904 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 485637760 1250 485636510 485636531
    0x11070201080f0709052101180804031104182105130b071118060a0e0411090901180b150a24090302042f090a0314030903070b130603 58
    0x10394800e8100016481040c1c0e2940e50b054101c0340c0c2201604a2035010346003a4400c2c81b69881094000c1680500710007c00021150708409050150302c041d00520310502488200701242c54036080b9180cac008080c1003c0b500c180d80d0310307114441e5445201c007154042a0581c90048030078034850740300808142d07420840c2c9400461540e410000003140b2a08950200c006503038820440301650500c01204003900450303c1c150341c1200a030701c0440c203e0360345026507004078001404014500103940100d80100c0e01404840100003488558980100303602020b64840004d07003141742e0710111f80741d202400740b8184140f90800819180301c0400f0302c0e50041c413445c4405418840c0c070b0341855001c15003c500000455200390301e42c60170303030300f43c48181c0c4043d40c081d03d08070584909148a5a0141403402411139a0000c030002d44050121406040074641e00845450000d00009610041d8201c140c44090212400c2c0390205001900d07000043d00044054400840d4200c09822500801405401207007010f10403050390 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 485639010 1250 485637760 485637767
    0x8010501090b0906071b031e080406030c0207270e0d05040b1b0a08040302010206060406141201090804120210020a0201020c04270b061206040c15110703060f11070201 73
    0x7180074090340d0750400101e420310360340c4140444800603030000002039100407880e058034103041d0720b01c42601d4080755030020260008880200c1c8616651220105017031508121080300200000ba4400c0e0a5120360000480c140403c000000c1c800111100c484d400780c01100400c0007562010260002e09034010f100000a454015041c0c0b0250349031801d1749500e91f1400301c1c0300c1842d5010200d00c4055801400390410a00440d080180103480c004e8089440700d40341c42e41032008031821392041c2941c001c2499509621440e101104400801c040b0f40007003991a01c980310680c42e0ba120784d000d647c1000150745600d085091500102c00501620f0000d00409111b40d00040e403a08a1078071020f1240b99a04050038a2000040203100014440c49007184640c60b10310781000900c07000d9620b14400d070303008402c1c9609010001880d510640d4042001514230b443e0000701e10560550344060014400c3c160702c22442c50b5410400040250301030035001c913051091080c0d43c030460f0740340010214410001c01202e400b5036003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 485640260 1250 485639010 485639027
    0x606080c032e08071409090d030e0a082808090c0d0c180b01080108010e0a080f0712020709060e0c180111030d090212010905120918040501050f0708010501 68
    0x100031002c000b01400b508504194a6402107080b0010441200301040d00f1000107460b20584d480c10080e0412550100204441250121001050740e8012100c00c601a84a0f80004440c1610401214951551030b543d00e030154103e418529182c3c52040c900003104403140c140c03000380e00f003541446211800e0945040303403203412800070f41d0b01455000410320b040194916004000340300c0d803016010090240c6400ba00501100d80d40ea900040c5680c1c000b09842c41c0600c144560801c0c0900101103082090f582c500c4960850300c84840000d80600c0785402007459804940c10301c4500768082e083e00c0341441c40c50000c41d181074010704c0b829482e05040243e1040c0c601c04840300304c903c190b00c92900d40210801226000d03201c0341108844d0001281180c80010705400c884c0c400d61080329500490940419007500b01ea40b03400c1c01074455170080c0e1107110703010707007070801407141050150121014904c1a40082000c4c08107640448060f07644800b007006070072034005020b03000700c907514040180d5450500020701545 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 485641510 1250 485640260 485640271
    0xc0212210619060c020a0b0a020c0a0605181e040203190e0c010c02120a060f020904060b0c071802070b070e0f0d0803061e091015020303060630100501030606080c03 72
    0x2000350b5944c1590380f10790650000700646100035556681c0c00c0002503c0e100881d202d40d00a010401d00407941a000d44183d075501c0c080a100c5821254120042060000140c0d080c4414910044a800300030b44803400110310a0b00215000558240d80c103070b0b884215038860303800200d15000301c00c42505580c1c2c489540442d450301103441c1c0d90b5002c0110340040c01c2c0010b241c0010449490030381201e07410001c940203030032050021202048180c0e6500803404a038414403800032816017040e04184142c40c00180501881c0c0c1101c20014184841c564603000d44000c240e460b18081012280074611905e0302c1d0440c0c81c0901070680b0110b00d641c4e0181d403403954500000c4c02480c4641c0698a0145102240544100716200000c04401241c200b0f44881c1c20b12845d14010749505a6011880818841c000001c981c081c0c00d01800d0640781c610740026001000c0c2c00f002c0c1c1040040ca20b44e0300d4990740001d00e01a28040c1c00400460103409140000240445900368084400e200588003007141204e1810142c0e503102 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 485642760 1250 485641510 485641517
    0x1d090705090603010e06041407080304080d032a0e1e10050a0327140d08010902090d051b090a0e06040609060b0d080c01060f180c021221061906 63
    0x3511900d000030702605c0444030200b25031050608100c2884480050310415100c00000d641c402038071010000d40724803403801000090f502011301d510311940300c2c0c1e00c80501303040d085400280514804148050b0300c0c010146103000070b56051104405490f011040b40c6581c104106213281c0d40741c0c2c59000c070f4580304581c240300081c4840410001500c074060741040350340741e051071a0440c019107110500c0f0301d0041c1c520420344140610341c0c0c1203c520300f00050f2605040c000ca03201c03020036a18000c1840d000e0340c0014801034000c02d24038481c2c2c0c0010000c10550304c003c031416801903a00c440410071301449090042582c114113082920f0518242c101003000c982080e08078001250302600c6003072000250014118640d0445030b01c1e9514014401c100000c0d0080f9410b0b60000d0011039507800990003c2c009500804282071460b001c600030003e80c940c444d0300e19440e94011340300b15005140c40030708a41c03c16114400000078468044e02e2681249190b2544660102d480a28220782c3c034002500c403036080c1c058442032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 485644010 1250 485642760 485642779
    0x618130c080703051005070207082e05010b0304060e07050f12010b0d0b070e04060e0705070c0510120e07060c1b0806040c050418030f0e01030b04020d061d090705 71
    0x240100111000007a0110708100e41d411990703841d1580c0e841c107144000303d064915100224002520100e00e003012103400c0b000808650302c91120800316a050001403524820b2103200003440e41040303000d264021b02081c070010b41c41e403400e0f00301001910700301c0300c242d840e50300000401d21850341c9940c060a0204c4051b42d00c1c4400c40b8000784190700502c40044426400b0401608281c200807018055921070803640c1d50341c0c142102420203000603114127018840d8450f81c910002490540300e000070b8844180511956a0b00c1c0da502c0005c1040c04029020000c0080e10700344141d000002c0a0090200b0000b000004001040c40c10700010400c2c058010010300c04080144041040d00f2020341080280c0940d00031b0380c0042c103003843c04400074a4a481680c0c0101d0400c0085e81440c0d022584d0743e103049070035842d061126100342108654090517141814185a564000c4140d02e440398800340c8031103441484001461800c00112300c2107001c000c030045130009a55000c000381901e012a8107411250203440700d802 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 485645260 1250 485644010 485644013
    0x1502010c120f0e0318011706030a0b070507060905060a060f14100c060f0f0c02060f061009030506040807030801050306041703060402040902030a060311012a1b080312061813 76
    0x107040c41c0f078888a098032002c11010601c20164a00c0d021251098854141400d030640501085810131a00c11350b00d50894440940483c504103039880d170180143c5401da24040d242c0c1d455100702c82e01c190f400d43c0c0faa4814010422190498484c01e0080c14155490070282803901c807a6030115085100031a0060345002000c0160600440030421801e0f841803081c0b10004103070066000426104222211260400c03c40044942c008103405002e12540803002e001d40d91070009200703001d10601194810000d000c4070001c0404c1e030510000e4044d034406c0c0507860780e4010754200144200c0060708510304c250002000e0100080c007400b10a90180c800d44c2d0010346075512400002c001b80110b5004c0c4010318000030812a034084141c1c03059055a1140080007028200c1c400112140b511407802d09989000210108410100031178010064a205110b00c2c0f0324265481050103902150380d1111400b6840855207c0d418050040015840300c8199240341020058012441483c0005844010320f03151b1000001d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 485646510 1250 485645260 485645291
    0x711062802190f141b030705010509011b05120f030a0b091012170a020c01020105091614040603021906080106050f0d1503060612150203060609061c0903091502010c12 73
    0x14a4a5034083e21079400b481c100000e0170303004010760148a40190f050100701580504251002c0341010381d03612442c11102c485100d8040f08803c0b00b603c00740b24040802101070b00780c0c2c0c010300f803040d0524983c685030305011503403800340c2e50002d201c28400c052100030418014000308841c4d00b1160070300d002c9442e150907424540d04c0031283c5607400b0b500c0031000647c00c0d881a000140d030350340d849007a8000c110070f0381c0f610f0b1030603207600e20820250321100803048108020811090700c8444e0000040000682556a60004e24581682001c10b8071112615000b00000c540146500c0d004007401d082042c944056030144a003144109a00301e2040359882c50640807181d0358246910107198406010081c5586540701002e83d82c40d0114101c2c2e00d5080408008990481c6000f82da0040c1d6019104504111109041284981141d0517500040c002d2480b0540c8940c464007901c00e000f40039854900c14241001c4108a016890306041019a8113024402864542c803600c9004042e0944ca030009500c03010070340c00c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 485647760 1250 485646510 485646533
    0x30a0503070c200117010b0316050906030a061706040807080703020a1401020c0c0406030c060332060108090a0f03030b0604050306092506080c0711062802190f 70
    0x681490048460380f82c035040b00d02e0a18a490300e0980f1843c0ca108640c0710b040c01000d600340190901c0840c14808102007015208680c424042c1e40d041a906003901e42021030f100350821583c5614907500d8900421100724102e5a50540200b0b0b600540580d18058484441074822500d004260001c0000c100003414424006040429801b80220003401760b600300d02030213074020210556260190306040c02c0e2a181c47d02c1140f040b030794442c208c0071407146055425402041c3d2091440313551100c03165542501808504d29000480441c40f001c0a281015030004062010081c110790f00750703010810074008100a01c41445103158075242c0416045d201e140419241d010b5036000320340520400060041c00113000c50301901048100c0c03965541c060f21003590341c01083c05c5100d540045842e04020905210030301c030003004d07407a001e000850405803090b80420745903840440520601c544032288641c40000360b0000c1902c00005100a110444400001c1515102058802011408000c800e1810080c144080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 485649010 1250 485647760 485647763
    0x209100c0f0206030402062502010e010e0307050424170c0906090a0c021f05010302031501030209010603021e040602010c021006051813020603040317010905150405040c051f0e04020705030a0503070c 87
    0xa4828401d81c04c0c008d828011042c9100300e0219440c10021042540701d010f070745804800090080103250f25000c00e0000600c00d42507260303514185558042091302580080000030040c81443d02180c4130071158250030860051a1140b0803020300b0140700e400d903101220240c0045400c1000900c1c0040007100303924002d0703040032140c0203000c0d20040c4600e020a41d8081c504890003501522240c0b05000c4070100020403d000080d4001c4031000103110241c803c3d409411a00700b41034050720350220f20058003480390000c1c0e014600507911500083c620903814080052003010880080c8441410440020094485c08181403841d0000c4c0002440a40200003601d0f0303140d801401c256942d0400342070080030010345405243c001c0a0000002403030034002d11440f44100018118900c4403015082000040c040140003611800d99465020400e541c8844441c030715200c0b00c0300d400101c0e0000d282d0203080e04100c071010b07903c207a1052001e0301c01310f100072088a004504a144c04d030398943d14032030305a81c0c07038216540 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 485650260 1250 485649010 485649037
    0x12020a050610030c0b032e18020a18080d0f050904090c05100203071a15030f0601080f0703021f1b05010c080903070f0201080709180209100c0f020603040206 69
    0xb4800044200d406150959004040d200103091302c90703c03403170001e10094a0340005980210016105501c4031410760041d00600103c2c0409583e88207038411410b10b641c6031440d090b641c00516036002070340015004244004202d2801946464510081c3d118100b142000003030244101c084000c0d544540e040380c0c1c403520000c000b003180f40200e05242103002d526018503070280d0000c1c008002214000001d403400030382d00290740986014800800f0101c0000a095005690f003045541110b9a07010710550307845088a0009110540c9805209444c00d4464540b580e95608152810700268541b014001c041701c0c15400e1081550350a200100c071020300c1e484601c0460b04030003100e5810084c064000104145080d07441c111151102110161684a2448014525404041c0c8003005501554a2a42c00f80c5c00742881000d6680d41d605442c2c608116020160584e680060525260710300200100300c040036514100c82803c0d210355542c92244d000c2803004e4400c20f00440000c046640c1c0c0d00440d40c501030b4842c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 485651510 1250 485650260 485650273
    0x4030215070e06162f060d0e01090302060603070b0a1202090307030f0b070e0406081b04020c030a020609190302030a2109050618030c0c010302181009090c05041212020a05 75
    0x1214590b81110009003202c401e09910191201d000350008044200c2c1485c01c42001c180181c00c0400445502c00d5104400050f159140b42c0d080c10828410340c030002e40079801408207440c04500309070811001ea005106990310a1108449281e8412400c5006003481c00c0c0050340c4600400000b4a0007225038401486951041594020400c90100c428000e2190b5202c100842c4810010041a22443c1c050400194848240c580e0b44e4056903d918010f0f400c0600014070304500024080d0070750744445030482c0507034092000e0050f8503504005820000c881d42c0003400c8017142c10b0b0b03402074032441142c040c80c0400420406103602898200071510400140140420210040d444c04c43c1e1135106c129803415141010ce4403014880308080200c50708000c03600c01803c890b4490070019002500030104078040300241a40c040e0346610b41900c0700c0f0010030b0741c1e20b49502040c9007030a14000d82d442000004104442800100201341d02d150188510950001480c0d02c02d60b5000c804901c3e040343d01c80301514512468 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 485652760 1250 485651510 485651527
    0x9031903050c10090312022208070602070503030a020606120304080105043e0103200301142701030f062301060f0207050a030318030605070807030e010504030215070e06 74
    0x800103103801d01210040d1906100e8082603c02110541c8902401103045141c91801d00665540181020203080069504031420000d0002d880324041e000040d1981c8506402e11103d0740421400c0b0050500710011403800c141c0307403c000d48131100944654005c0ca40d445200740c02c0c2c0c40034007c1e100a4402c02c0001c001501e0300341018074284c06186119055035604119000c410b034801d004c030111044180e602c80e1320000f80c0c0001100104102d640c10700d9198196a12381203840e521a008600a10440c0e00041c41074107090100444400c10002c0c0b0240b14004d00030f070303040381c1d825000b0704e0741100e4000c0541c0307400559600300b00f40640046c00b210150210b0558406000903c140c00d403e040c0c0786c0079076813010440800e0000343c1c0c3e40c0c0d0f01401950360140e041002040040d01c201e000001203107196105581566480d07581500340c1d4426250b20012401c00380c1001415a03241c4210444040c3d140c009000c24201524080d4450100042030701c0381818603000170321058001c4505007000e240140200da0b0b242c440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 485654010 1250 485652760 485652767
    0x10c06020d06230102060f10030206040f031106030906012c04030f020708070b040b070c0503030313111008040605180708060f010b0421150204030605090705040608030f09031903 78
    0x14014400f000e410700e140b1103030300c66101d2110031440b481030300101030689500341400c0d00d000009180f103152290100001c0b0058071105d0181c4020221240a4031000d402c62803c3c0c1600d03458040940e002d40303020300402840c810006803c504641c6980d485c200c01900e01c0042103040300c0340c500b030218030030b4603d0240020164032514407005070f183d50342660403172902d9552094403039513544110b6100301002d22092241c50800c10040400a1040c103102c02e40c103aa400210341150401c44803085100318524995080c41800f951001546100320f07040c1141000d001c001904045003c0c101030550f544c2c2c0c0c000984c84401032914102c8004845049980069076001d0040d52207004a40d45060f40403c080005508080081500d082da4200c3d0886118000516482445005184000c0c3c0729605078001c010010703083c510050001d5170081c0c0000c1410318001400c0d174608000360780b0080c05189401400c00501e031010040c0c0350440600c0302226660b0482e100000d1070320303203400f01a24200707244801c100109600f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 485655260 1250 485654010 485654021
    0xb040218030d0503090304030209060a0e090d0f0c020109060503150307080706020c06090904080f130906061d01052712250b0706110c1c030f110d0902010c06020d 71
    0xa04034202c030400b100e002011a21400181d88401c07841c1d206110510040c54510300b465401107024110000c107036500d0006d51008103094032069140e801a500100c6003d42c171980d00b0860101c1803d00c05110340880c2e0000384001d219105010401c030010020680418121f1503081c03c118009085070743c00d17900c40c01c3d484d880d02020b1107400c02510488840c4180c0c6d052140072ba5941c00c00083c15601c032942c8a480b02419135000c030200420000b2308200309211182d071044c012015000103500050914140000a030a6000022803001c0060000381c1000b10750ba405002c07030703204810b00e0407030598001c40c50300914000d0040d071000b164050300c1c0011100c2042070000f0b0603192050903a400d041d510743c00f540c000d4501e000b6801410210300c003c103c40e02c041079035500402c01004400b201700f440c00f100c0707142d018100403c0403c2d8126404403032114a11403a49805070089005027940f080001d50b03200c18020701180704000e0b00c083e841d07032079aa08400b5a8081c000c25101c0c00d030490415583c0e003d0031a1034100410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 485656510 1250 485655260 485655307
    0xb040e0d0e42070b01080d0e0d0c21020433060905150c0f07080d031401090b0105041a09041b0503040f0501180318080313180b0402 58
    0x420030040324040240c1c1982d254000600940080321980b14402c19610b400c00d601030560031800c000b181e000502e5104050300a03c5a41c0151440c4010260000e01c0104460320051181440d1140c881c080354100c0403800c01c956000c505d080580311843c60782ea00d501403199010b54820b01d01690f00001e046035418000c6140d10600c1c5002d2800d100da5645840800781d406140000b40c084ac1040c003540c10411040118160f0482006081c0403c0c1c07c2614940302a021114115800c04030007080001010040070b8801a5642000c0c02510291103868031012014030a9000707164a81401e032015034092400c50303001d8901098102401100719017081c403a60b000e414454061403420f2030b40d0298502e00b2130041d0300d0480e280d854620750340b90b640703440c1c0d0107611840d4141c5180d580d82001c891088030310b05c200c0c1a0544a900d40c46030b025807254164004030416031264420307070000c11451440300fa007522a071090b144802c00034510040b40384a01c100174007052601e6900a8800200c1300030002ca9907060f50040c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 485657760 1250 485656510 485656519
    0xf06031005061f080f070c200d081602011409030a080d14010e070e01050a0807121104180515010e090907050406090e0c030705210a1a0403180e0a0b040e0d0e 69
    0x143c1b07170300104440ba54103607400038102c40c107401c100c01c98510800e800d83c4620780d001052110610090384945c0c070641c0c407640d282041030010321302120840d41c02c40f03224144000c00951450801c9210004a0f86450112030002d0400704000b50418401c0040c0d4800301c100d00c0040e03a0b500c482e6031949524100d031351040d9410000b182d85596010510b42c131800403078070b200c0d00965440b56551600171007900c0360165081d24602e0103458030058010303500c4a10283c130041031160135400309030030750000d45012100040c190b5501d81d0106181c44110707036000000542d4203201502d50406030b40d00c00c81140d00b019640c5c1c0006a0241c285800010440401e40103d9510400c403000d50380000310103030070175965002ca441919005507004c4541c1c00250001200c507059a450030b4140c50f01e0400f242d031800c0f5100200030140c00c010700040140428140d0092561190340805658414010700786503030500d070b616004064200703080e10344c0303070a42c99078a031034000d584070a1300c08003198540605460003420010641c0c0429009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 485659010 1250 485657760 485657791
    0x311060c03090304050904030c0b0412030e15010509040206040f08060103060606050c0c040f060812040305010c05071109061206040c030b060316030f0f080f0d050f06031005061f08 79
    0x5902000210303801660400b0056192501e000241701c0d0b42c4000030002d40034032222054a03004180390b4610180b2451080b4050a04c101c25440094111009034400c0c62440d4020f5840c00c1c150395800300c0450548030119440440f0399920310001c5c800c1c1c0305580000c00c0900e5102c100190340a030000c1c4060503a84584c60600c800b903100c01080702c0c240074240c820303090355100c8880d1521504090744250b00314042d002c404035004d40c980c101c90340b0341240c4422004040000007410018800280f140d0b2601c0140391800502d002e0b20342d150540281900c0b210700b40b0810401c004140766942e2440300121811501095590502c0c0504050f030300e1a1040c40b0136195940013400045a5180100b071401400c0c9420040b44041400c503200d5458013030300803600310344401c0d4501108010076100e101425810a000e240705a0700c0c90043d41000955102401c2e0403913052121050006590380840c818102c3c801d450b500103815500c000000b951810981e00740c4468803400c55158822a501044c07051060070001000c846 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 485660260 1250 485659010 485659021
    0x415030804050f10080402090402030f030a0e0a050d03091a1b0c030c030c0d03080405160f17151807180605010e0d080433030902130e031e1303031106 66
    0x41070414004c3c0703000081d03103040050f00600d400200a50014006021074034640c070300510b403d18580c0990324440108264140907206131030b051211802506068490200a405540d80070b0111041d41c0100c11400703690141151810281c2c100743c50744410381c90100c0c01d9501409031095118680485282e010303028440c02030207a4280021102e4041602030447e001c100b410303403400c41d01444068411510f038000c8801d452404a688040000544018038480188070300c0d010300780c0c103101c0302c220040b030142c1c004803d12500821111141903010301c0302c1d41c4000e00d03001068070085c140090360700441c014064071480d1520f096002e42c06502034070750030b886000058004030100a8404014940101950001c100a11948808071160308011804c00d042045441c86801d0100c9220315082e80040060f9a4480c000c05515000e106e502035032404140420142003540d26940d01d0b4402c01d091003003d410402c00d04000101c101044446803070030f400714a84002d444c0d140041c2024900803131884207200d80000f103803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 485661510 1250 485660260 485660269
    0x1060806090402010f0f02010e0a0506060901091802011b230d140a0e030a05300702030d0810090f0203040c0e0705070f1a04030f09170601030f020415030804050f 71
    0x60180f90142c407507101c4c988880c00d04840305c0d0b040d156048215520754008451416042101c401000d2144018101e140360060038801c040c0c0c0164040100d1900f80b1084400484074007000c2c20750590286005040c860b004480c666403642da40c0002000170308000e4211890b80e40100213000013001e02d0058800d07280920000316074100b503d82441c02c044400708803076451640075001800c0c01c05805400c0e01e80c3c640003611394500340032171001d007000d502c419000440e01000c2e03100d40008820380842100c0e801c1030410b07004a80d950141110240c24004904045000302c62000582c2000b84039006091091b50b080c9205035000e504256001c840c6002d601038085003031055010024400d2009994060414049407a80f4a00b040030f548169a080502c0c042c001d0064500f000c4d0b01d100e503010b0389403222240052180182050541d178808024101030704e050701410140859000c1c116900010030041c00c42160000500070801e00e1000c401d4041c141c0400400c024000c0007800131180211108207000000c1010300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 485662760 1250 485661510 485661529
    0x918070305040606061412100b030415150b030609040302070b0703020334060504062c150601120e010f06030308090d031b0809390402071e031e0801060806 68
    0x110001500340450420101f201c0100d6074000012912019060754805c1e445461758825038040d681d441f400200c400c60207596016060201102e681c0b40c0707a19130701d003815008840c0005003001303202e10610760200e401d15108000c00c0c8060407070704408955274482c600c0c020703640340d006003a0038642541d00752441500043d4012006d10004000c030361640f071420079540d040000d10008004039201d580e2030600c0000440c81108807c1c02e0344d00024000ca4500400c040c41d4078041c8107101e800d984100302d9040150b07a9a0100d08400300c40103100b00450003200740c07560b2901410412503880321807840d105001040c154070000c040e0080318020192444103c5142003241a01c000c2d10744221840d000380d81000c000c070b00c2590b03d1680126154241c540b00301c580148e100041c2c1001c41400b8400f00610400c5103404021058003138140d40c02c40c0e0440c600003d036981c03880305000381e12000300c128a160421000349409010401030083d02c1794524900c008052902030144074081c0202350005818000150660030316002e40d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 485664010 1250 485662760 485662787
    0x40e06100506160c0608040b3304090203100c08090607050f0a051303050106060f020102071214070602280516081b070806161d0105091807030504060606 67
    0x10300c4954208010b000b001c1d44a89203540c0e1443c02510080085418000040d001d4495a61541040e041c00c1c105070980c07680240c49690f0710300d894020312030800c2d9818401d644420001030180341c014000c00c0060020640f60002a40500401c500e8900c1360b1465403022603801926100c2207a952242e40410395204002c480350408604100140b07043c0c04a030710b000d0281d064030762a2641c07402c004030a4901c04d01d40c2c40e0780101c949a4459000340005070700f00708494060142403008500b01200740d01d0350010005100346035014060f0b50409180c1451040782141d0196421240555440c1c50450600840703005480c0520114524038003440e01c2d4512400803581070000340680050801d904c1d0b250a125503201d9109030562000303208c01440c0c0c081043c000b1900070000c82025041c00d240c0300c1c41c40c070380e0700c5152104030042101c207000b0104105400c0b51618803000f020b10b00183c40b914458041085003528076070b2040c10418010030801c040760705803c007900c03c503c2030302e040c040c8541d1000d05036000601c2e10003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 485665260 1250 485664010 485664031
    0x90a050a0201210c090f1a0909060d0b040c14060c063105011e02040f0612090b0405061e070527280f031505090c12030405040e06 57
    0x10304805580b103a04580ba4000c600541625042d44110085040311000c0c3c051002080c11a14100200c007030346c100500080000d10384005005401d14644250381c0720342141c491140103490007290a40d2194800b00b40340c60350041c850749c3d1a08203400c01034194107052144a0302c2d44092408400c00d82814030550f040403201c18010300b03a41d02d89803c15100d8a01121241074003284801c0080004c5403034048480025024000000b214410511143c0e00003c0c03528808419a0040004100d44c00c01205042c0898045203000c3c1c1080e1030008407003002e0501c2c15030240c40e401c0e101c4180404e208006c68928042e041f01c00c140c01a0b84200541e00304480c40407121500407600034440b5030003861310800840c800c50001c01401409184030700c005452070407104d070b00808500c07280d0b00d101000014030040f03d0140c071900140014040c074507aa03540c00d40b80b42c0c460040711141c030380010a0001000300f080300c00640008003000445e1660811440c0eaa4000340f0030707075102c1d60801400344c501003408140b2078000c804c20359 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 485666510 1250 485665260 485665273
    0xa050310080d140d09080d0e0c040c09030b0c04090923060f060f030c030307061509020c060103020f01052106030c04140c030403021e0d090e090d030f020417010c0305090a05 76
    0xc3d41512541c1110134034400e4591034021610028240900401c0304034002c1d0303c0012451130391304000b460300e0030902c06c00707020310b01e800c207201d0b02c69410107043c9040300c0c2d00420031300103640c424001d400c0318000e540c4580c41240c10300701518104001f1b800202e00035000c0311075254010f907a00224603038503c01a00e020301c80d540400046403990511200c07041c03800401804503001c078088803010a00c3d542c04840242c54184d5101c001c055070300810b50800e4002c1246090a5043c00e0f02904201e84844040c0f01c024840d580d4481c0400559005905032012200b8180c0e040c00302c6484154113032880c0307004651103131082c000c0c404015140c2c0380c24231403200e480005007031180c0c85580340310000e441c1d90b20180c4241c00f588108414042002580341e00707254100000c0b0301400d41c40c0142c0c14040c011417900c2e00001041505001000407004000070001104c801c00d20f004100300101d0502d16000f07106c0c0d6006141407004901349600300380b00542015808800981e010003403036580400003902c0d560b43ca60010302507000007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 485667760 1250 485666510 485666537
    0x105060f09060a240201060f1a1608070b10120809090603010b03070f08070504020a050a1d03010603060902090a090b1305010b04050403020610140a03031b05030a050310080d 76
    0x110000799000303002600f001c140300d4035196803140007003648096000d030800c0640d8081c0ca06a082c00b80b80c0040452079044a00d05090580c00a1006d210003215a0204404103540e941c2c010a180c81e20845508034204640e0340106060000d0001c008980c3c91032103030400000000c0403c00d8020300c045258001d100e4038100b03070a2108101201c040508142c0c0c0c107640340d0344000481e6a051107010700500d00c409071012042e1900b04440e00b090220750082e03115620510181c5480b58102049800c03a00e580d00c0d00a0341c0d02d0b900280e010103a92100c500540541c60140040f00704500e950116080d207000325401903081c0d0721001000141c5804140c0205100c0703013240807075121a000d150070049144a44000f05071070640c04003080446d80101c4044d00164410424808240c50260400010b081300441004820034410080b42a40b40c80d03100080401020030b00c44181c92142c01011504248c0c0501031b20b50ba030b800480010106d0704199483c9400c8648080002001c600c00100116078251907110030920310135a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 485669010 1250 485667760 485667769
    0xf03020d060b0408060f070e0609041e050a0212090a2a0306090303021801090302300601090b130b03060109111c051e0c1204171c050601020105060f 65
    0x5a5400c1000341c0c031900301140b08002e100191018125144c0203040c44e2400c001400a840800740104050060840c8100500d407520400c4818030f40068801250048c884214950080f03075900503da810b074641400c1c030051120f40d0f00101045106c4101e441c0e529124014620f4940072103c0d401000b103030400703200d21030881400741c00e04280c0c40d40c2103078603008130713a2134031008195000d011089000960000300070400b411417a03031100080b2002c2c42d1405510303007036034042100b04495400c944a1510303080200004100c4403140120351500110540b40f0f256540c0034080c0244c01a103281c0c600c590782070a14000f0819892042c0201c00500800801030b0780d10b0061500010028400901d00e00c0070100141881c03d0742500c0041604c1d810a680000c0a04d451504052499881c880c0c1c4021500070700141303c4800c4085066500f048100f080981007511030b80b5200912900c00b1202c0300a841009c140b00f800b50002c0d9030f28510041c0c01750300920003940c8843c0128200c3e2400c4510a601002180130811182807 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 485670260 1250 485669010 485669017
    0x6031512030e06041a03010e0a05040b010b09030309030304090e3003040303230a2304200d08030601090906080a350301050406050402071703070c14030c010606050301060f0302 77
    0xb600e160f04e019180c01811180308091001c8580c2804000010009103101510301c036030068007264204400d051a075030340020b07c8018070642482e45000710380303500d0079607051040b0740364041c0040441c0d82d00c03603582c0030309000361844060404642c05111020748141c484000b0000c0d4103c02d43c22610351a42e104c0402ca526508050010303020503560f211407200c6c6450b6480c1c010036030a20200c54001900e070007041d500036280320a9803550b81950f030004040804800524154006500010020300103440b03010105100d00d080101c00d80c41841e628005003480402002113005503800e81e54031051a8071500d1030400d5801c5442212003d0b402000b1443c0800c483c0c1140c0c031340d40005551074a4221584550880f403880100147c01040d40c40000108080e180a1040400610041d2400e5080c410180c0f0341d1282c0301c40e111a6501c2c100d03000000160b8051140d04010000395220105070b01561400480c1c603a43d80120160f8160b9605e070000220f04140541e0969040704c10680c0c510242e025840c008801a42 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 485671510 1250 485670260 485670287
    0x50f07020d0c0804090606081602010606050702090a0e060103210e010c02121006061d10091a0d020d050405060f1b070305040807090209181905090a06090605010603151203 75
    0x1001480041750401440c081e1100520065403583c80350304122585104c510203c032101401d5a1602c1420040c940d00041501d0b030940d0101c40788111680c0e403502c100050040402d100300240188070002c02080140006a19001e041840681d00b001070100180e07440202040440e011a80da8030040c001450302890340758000003e2020396000c11b261700070180aaa189420620124081d810807100ca030000c1040041c40090449030742e49044408100941030103c240600168a64042c203a1841d14000d602140e030b00000d1690115595401c0c2915000200400c5c0e4040f1024010040400c9036000ea200041e80140980e0b10301c80d480c043c0e400e480103020b074000300007201845014440052901d0b0140140d030b00812a481025944503a0b031020002c02610036031104065400c41c4060100711108a07403035028110301c04d03030b0000d040d4590020703180c40e003580300800900840c00c0007503801c2005400c0c0c104034101c4010341c4051029440340e0300c1c4040c42012502884581c18030640103030021038841e0a0552442 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 485672760 1250 485671510 485671523
    0x12090b071e03110f24010e0f060d0b010f0e01090b010e0112091407030302120a1d010c06020a0e0901080c0d201003060e010e060612100b04080a06050f07020d0c 70
    0x758100905400c084130301100b20706641100f09043c140380000d1448140d00c0080650100444d0304120b102505440060080c1d2000c3e103910380001c86903101c00c1481c5448a4000703035160090760391030030700d20748110050080034480484c034000004c00840500896206c6071f4141c481e289100d10007001125002c3c45619501001c980700c00b22140030510401042da10400d244020b01074a03070442c03d010749055580070071b68079402810021b00761401c0d400621401c982c004c0244940043c0c02810040703c07448481e000107802035100160703c0c0010340d007019034101d000741c1c252a40407880c4c0e602c040b40d9482d044855912074022051b0000600018000440c202d01e0703841540e40c2c100999400f0021404135202291040c0110780ea0700c0c014400040c0d0400e185004045ca1400c2d0002d915210000c104e10740035400110440b0703400c04000c624240c800755412030144c0700150300316449503910300c0d605590f00811081a01d6151510011031024925456110b11400150300104540c00c1052400c03aa107011501d401d490a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 485674010 1250 485672760 485672777
    0x304060906110408030d0e0a05120a120606030911030c0102030d020903150c03040b1303090501030e1e0102090111060403050f16020d08090301050f0105091603020405040912090b071e03 81
    0x10b540500d0190001c0e00198009607140e074010b0048808650f02d81007503180980c8141c02d2140064400074407544050005146145c440b07030000819960408116a880001814008041a0f865150f801045e10078003490411095611000030b0584a80000c0c0382140160401c0010702c0d00c48109800078540340001030304031400c100204c01c601038141820352305c804542a00000f40824840301c00000350300100726440c400380d816503a9034090901596445103074141622144a00b0035040c05000f80c0d58080f40904422410b100b18176100d41c001d500c441da58034041510031001640c11074000803c01c0c03140394162103c40c500403444501c10615040301e01000002c2c0300c00c580240050b110480d4001d02544610700103521080c1500400d820354400602c0b043c000881035004020550301e030442d42ea00000c108003460322030090814120007900c100d0b000380d0713007043c241110306081000180308004c080c100c544e10761000c90f031a450041002d1003200c40181c13400300300456090807483c0c12001d08800340d110707007050b549 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 485675260 1250 485674010 485674031
    0x80c04170a02090a090b010b090105040e0903130e090d0509030c011404090c03051b090d0b07020c120f0c10050703030b0a051c060c03090812060a0f03111906050304060906 75
    0x140c046044030344c40103094440000c2c00c20003801008a41c098150b03c1501c1341840f0800000070140c1c0543c0c802d0101d040d40d03000105004490500444030742c24013041103a4506500c84850446986003900c0714034041c0724428191030b400e40300f81c1c1a905100d40c01805003d00a1880f001151041480c0d8600341003420108400900c003401d038414408022523649000c02c3c0c81c688403400c5100202000000c203802001000350030155075804504040d0554003441080c001e840304113080b403400080c0806136401c03954801643d00306103000074504801c6280a0101e0310a6213000d4140415220038080a00100300c05002c40c000007030094011030180361000d080010341c240c0e1080000c0041c6080445c000005c8400c445030f9042c4032240c0031329010501c040c00c00780300300000f0b59a240c8041c8504601850320010000100d8003c0d81c42621440080c4244540c50b01540c0c0c0303e0034001d000c80e160907030f07861041c0f041c7d8400169160740301c08020111403103501c60034190343e03480c0ca99034050400c101007200e900c0c0d5170b58084003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 485676510 1250 485675260 485675269
    0x4031e03110d110c0901030305090d0611041d15031905011401120b0c041412070308030c040608060d080304030e04090501020d090209060d120c05010b040612030e01080c04170a02 78
    0x4024829600c030f0403800890703c1114100362007000d00d94002d00c400401800400e42040446079408015100102038024500701308008080650080341311203030000d800254002c410618031811842d060044005840b08900c2c07117401d0050389040d81d0550005040c000c8810603d0403042c00d054000c20010941c40c5c4000360444090038241c11800d135100040d05010705001049040ca1303171100d02c7c20240c1380740c0390501745038010581c0c500e41c07068801c110201881002120034040d0000035a0700c07407229034070703828485d000c00c94a800ca4065040040c0400c40040c00928001c0d80510a054215044503c0c40c0c407251002c1310718102016801d6001a221910140000c80c00d100030f00b0210003501000850303080034410080c00f6080540b040c3d22510312204490b002c2606508214030841540c00c03c0ea16275849440c2407409495482c4505034054513060002a20039000302003c01c0d01c9100c0c0c2c0d99005008503000041d0380c6200300344d581d00d080384802e01041c0100c80d1035844044007864002d04844424840c2d0b030010b03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 485677760 1250 485676510 485676523
    0x12080c0c0d050c0d0809100905030f160b0903040e070e031e160e0405071401140301091e090f020f12060103110102011d0d0f030608150708070504031e0311 68
    0x1c000030310001c0e904001c5802440141c140c024039240c50318140c1000e5a205585505000e0240051079031900d400c0d0400c0010421030301c00c041200e44540d207601054910b1a8804c01908080c0ca040d07440c0c1001981e015404002c450544510300d03c030000c5174403945d038220b41900001c81800e42510500210040094a5509000300761042ca0001e03c1119a41000703943c0d400115400180540c0140050200080c0301203450010f403600e8030650b810700c070074860040f9220341c562862589011000000410081603680042a000b840e0240c0d001c41803469070000012100040e0b405071030402c424880d0300051038401000020740f40c0041c08068149582074071681098400c0e842280c0b080c88181d1089100d58080c052110441c6106040112204084c152551900e0075200c0c20004c000002c40040c00c0b0b40d00075030150000d020400c1c22039058102c00228442981d505890900101c1c981070005982c0511910803a402d40ba44081030f40e922408402100050501c0c04200b1014001504001d0020301c1d400c1110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 485679010 1250 485677760 485677783
    0x10b0a0e060909090d0f03230403090f170106050d0201052205101e0509030a033b0a0e091e100e06011823040c0302060c030909060a0312080c0c 63
    0x707801040c2d018080500f1486082c1c1b0580c0606003045000500d0031000001c40d09445581d140702105a42c03140f800b220454001e070000325440311000c10207c0c0140040da402c08000030340c5002041619264010405600d038010300c000d001a1041084480d8400c0001d07002006d20840710a60381c10316110000601c2036044561204000b03044da030024a0740c002051181200000642401440d0818080101e511800c000001609009030103c040b6a140b604204020b00c0441a00d22000e246088020049080041441451144d005450042021011860032038041c40b11180144903550010100041825201e03809007000e000e413840706a0349410600401451400d10b002401c90f540c1008545107100b42d0005050b414203140c00c1c50054100e40120031034140e524104014a2560358602d04440b0301003480d00000d41040c4003094604402c0d60010140c90b600c60110b803150742503902c900601104115610001d4031900c0c1c44c01c62904007a0007208401d40110001c4400c034a054440400e15240c00c0034070b580b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 485680260 1250 485679010 485679013
    0xb060307052a0c100c0206070b04110405060a120c0f4109060d05010e01050a230a0915020309060f09060f01030b28020d060e010b0a0e06090909 63
    0x50700e6102e40244407005000d903920320000c070b035840c1d021404140e40700c101e82415400f40741001910310040f4003e00050300e56981c0180526a594031a1a112117201000c0e0b5080b41c02c00009500c00004e0700d010b000b404d00c41c010180402c05c1891600704216041450024203866076540850081200140e00f007100f005010002c11440c0802a40c0105941168000c6640c40c1a0700f001d40645018420f905202483c20f07204549290494481070006040114188001400e035864201404141001074101c2446001c00010402510207042226088061003100940382020010005081900b040e48080280c80c0078032102c05603518981409001c0740d01c1550762076002e50104042025581d82c48007603e50045200c0050031903814407104208c901541804002c2001c2c4810b00028050000ac0c003070240a203012443d400341065552210300000c0d4400100e02800c1c0e42001c00210388241c802d1300c032070304a80c078035492140b03481c01916044494110840c1c840c6e600450030000e02e14031f0343c1c801c104540207444260 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 485681510 1250 485680260 485680267
    0x5090a030f0311160503120c16022106070f0206091f020d0209120102121e04061e0216110d0c0911091003021c1a010c05070e04050d02150114130b06030705 68
    0x8007c02130304030008140c405145020403c0a20300c1400c0001032a43e99070640b0120012070440d812380e1000308040100702c000b8424030003004015a40301e104c81c013910354a6000c0d07401c503403184c0410315214089500c0d060846543c1c1c100084142c00994000e0070328200340c00b070040c2007c0c0300c600045c180c0c9602c14410900eaa402060340c1000c02103a807003041e0000101c80fa03200c5444030303042400c00290401807025011542ea0780c0c1d103a501240200007030707031100380e43c5004550f100e003206140349941140c1b1750183e6440202019508a03030802e103030b01d800e00c1078100c420b001d402c518040b03139800a0074100c0c03440c0c2400b95051201c3c41040e2a080d8121502c7e41c0103807405a20388500300020300b101400020728102042c14060080f850112a035003401c803488084c80c040344030310f1440c00c106280a03196032106e24207161401c10072040c03190100700808402199400d0fa0030403201000d04c505c1d40c480030b00a60884001035a5001c44600d40701c0c1e140c114411500b400401e8000d4100c0004829400071283c0b580801c2001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 485682760 1250 485681510 485681527
    0x90705090f04110303130b0304020a0e0a020403150c020604200315070806220207020607050703080702011b030e0603091006061e020f0a0212120403031205090a030f0311160503 77
    0x144840070703003c030140c3c0214180525a03440b0405030944e032058030b1040000102007015500c425101c44050040000d14a00c1800c2607000d0800944c054071040d224221100c124000c460b00600a400480981e6070080080740c0304c81c1c441102155401e6038003c0003180c1c4101c82c402036102440001c13480a6400f085101074584500301134010000240b901744580b45941c03419400c41c0c01003803c00b4184404500050700c0308503074808035000340700d9000003800d240303da07190000802141400600d04075100382d80d20380580500200880d40c08000e40c0d0001c020803180b8491030703c1402c1401c05194807a908508884801a0386441c1204440164000d040019100640c403034406800c00000005401d562006100da01c200300303400b640310005500000d200c2c2000000d00d1040e1041001a210340c094440460341c0d8890792480d003e0160300000c1d618501d000d041000045101001140c0d400e4019056150030380541440103007140201b107480340019100d5010700036450740c114913010619425104100542e0381d03c290 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 485684010 1250 485682760 485682773
    0x22715011106060907050a03090507080109030224040605071202030906221505151f1407030804030c020a09110717090a140315190b09060117090705090f04 68
    0x51101e5511694408024032200fa11035100c100c0e1302c02c0c0c040c9000e0342c4403000940f0881c0603000b44080070f009880781c0b80010507139050661010000d1fa11075000c4550050166183c60300c00381d44655550101003600c1c0c0001c0c04580e050300500e900c508946801d40f82802c2000460040340c200b40d5084d01c01e607111000300440510312000494608420058060040764181e0314442c035513085803603034280c0a0319480826801e8018056030709171854000c04000342e1840316401403401b00d1240041c0b07400a005041050720b08845202201d8105425582c1d10105582c0d40d28140d54040d8189412600858500c40c0090811030034815042922802000c0607540e401d1424013008525140450b455100410040c21a443d500c6004107806c07101d16400c02001a4501c00c00070741440f28024404445a035810104000f100b00c2810b41c42d8a460b0503d070411a83c0c120b082030042143c400c031481804a00b03e4000d810074058010f4003140d20001c0641180c4030240c80380045403204105132090a0300d903280074140002c1004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 485685260 1250 485684010 485684027
    0x3060b040b0f0d06240305030d050705070b010e1009050114030606040c090e0a140c030a0f0908091c050d1107080a0b040b1e070e10091202271501 64
    0x3121451060420030b0005003411007195001024655550317500c80c69000d10184c05004640c016000c0b03181c00f0780ea81041d07501c80d4030451065404603c1c0c2000a10014041c90a03034101c960080d510b0300791603003020040740c800d07100a86555070990a100c030007d0840400c0c02110301030281d401503842c0070b08030a0207040c0b512001410652046003081c6440383c207941c0c04400030f002c5030220300b1080440d480e8017910100511a904074141160b503180c040100b0741e4100c40003140a0344038148100226107428500e04129016000018074402c002c2107104007524041e00c02c008502a007140110310350802d9524a494075000d400c54070041003a51001a120541c240710200060030b00c2070261440800d15641c0340b0890000403c02049044103c5c0881c4101511070003401c1005030301c880888450a1185c13029141000021415100d01d90420800a00902c2140c44100303c0300010300317010035981c8036800c005485402000003582440401c1d4483c140d80683ca8100d40100030440304401020300c8070b400100f5844 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 485686510 1250 485685260 485685281
    0x21f12020301080a020f011e0c12081009050601021e07030209090d02030409020a0e0d052a0306010504230711010c03020f1b120d0e010b1906050a0e090103060b04 71
    0x3441030004011600700400c00002055044841120b06007041e03006945500c04005070402da4800402d0b8a00a580c02000e000c015a0140c0c104065845507048212604c40c021030b01c42503000340c02281000400000e0700103075000101401175030700c0420050041e91980c4005e08807003030310f4ad00c0a801003065084c0302d82041e07085644c0761b0180003001e02c0803002940e68895885075003040d590006454428a1058440d00c491640052429100c0f0060742040ea9035900c1d003c0b00d0019100b00d4001c15080102c2e8070301c06004448001e0040c064513803030502040020050709102c2202c852280000078040c01041c05128440d080e43e07202d07400100c1001d1442c1d030868000c0c02500007450301c10030034a41c1c5900e104054490398114000c42007806281e04100c1424010800075511400c203010444865a17545604807580240b1020000c200100400c0200b001340517002e1061200100022030a01845100314001c0c0b008460900340054001d8071440860f4140f5003d90040c2d800582d070b0060b0304003d103824050501d41c40f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 485687760 1250 485686510 485686547
    0x90601030905060103030c150c11063321030a02071d0c180a080a05011401050f060f161101030b030718090309090906050f070203120a0f09021f 63
    0x21000ba525540e03590010b00000c4c06124594031a03008010807403c200380000d104250030710003440c561401400081c0202d221005600900000807030005111076035003138428428008110105154052101b0000c040a111b40c02143c1050342121002c040f0074039012403000c0e00c00440d075569101700000d05006140c0c0003c44a03a41c0782d8501040b00758990030380d0784c115901481256541003200c1c000c02066200d45082c60b041b2503061000107a810b004079184a40c0ca02074070003030140b84400d140b2250403640074090107a10040b06e60b40700e0f03900d091200140040860140c030b07170340c40d100c034403a0005d04100d0404030844610941c1140e4405650303150040d40f00b541401c0d4018054241071590b40d10a1030b5044841c01e9803030395200e003d1800e051040010030700402c80c40a0070031140d041030503e40b015100c200c3d1041c0e02c424080012504452000040301c0f05692441c000c400980c40d5400b1401c080d1411071488001d0070786840788a80940e4441e07400301c0040c0c460001c4848508400a8003901c200030000420802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 485689010 1250 485687760 485687771
    0x305060106090f090b010507211d0a0b130f120c091a1c0209040602070b1b07020f0a15030f0c020705031e1e0607120b0609240a02010b09060103 63
    0x6100781406654280c0d0403040012078444170000040312a8003992030081c10000c0b003140c0e044140c460240b202c4070784090980c1d40c10007148003a00241030b0018101c84058104c046450b00304079820145012700010480812403020306580c071084101e141803180c011a00c1c00c01075030007a4080142c0300a0001c002c000d284800e01c03544c810504512600c1c000303003844030700171030744004100b0078600c62145500200b64001d00c6040729003040d007003800080d00103000480d0b01a1803000450341030200c089001c018400225580d61401ca029800d001c0780c45182003115400110758400454826408001800f488072603079000200307450920451419a080204281c0075034011a0081c0000e4501081020030401c3c14542007100c0284c1020b0540350409405c4030504a0b0100001c4441e29900402d4017800751246a95a1190144014580d811503404854480d030000701004851200c2c10610340120032041c0304500b080e0700341000030034125581d000a0040005035502c1d5030183ea146131031103030590000c0c403c0c6000c119 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 485690260 1250 485689010 485689019
    0x9030b0a0b100e0325090e030d060b040305061b070f03030b1e0d03031a030109150b0102011104030f020d050d032007050d1808070e01030204050a090206090d080c0f0601030506010609 80
    0x8031442c4c40c0c0305c0440054240d120105c02d44003400555401006101020071603410f0000c01c864603030300a41c0d607000b58581084400110300140c00165010b03203030001d0141015807190980d48400094084003203104520034807540380032920300640742c5811030007524045041481d0000b0001618115030216488001d22104850b80c0e80b151520b02004c03542c5404e001a608000c45402d802c9101c0d0044000d5040d0f092094882c1001400c5100c0031803000144810b00c52030000328016421790f150011a030110780700034001040800c018603000c0752000d0019259a0301c1400e00c3c2c4802e4140fa904100090110341c864a502c0800421307213034034000140c07801d00d1260078100c0c0c4d80c3c1c0d40d5450302003540380c02c1c04000280d14911121108042c00030001d10541046275081307035a8a00c1100500300074801070740705a1070500003402501160242c903407050f5004014528000c860002c100705c885070f100061702c00010500c4908128202081061203821089008000e692b16500e0080c0c640301c0160055003c00c500c0400c00c20 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 485691510 1250 485690260 485690263
    0x6030a15020c0102070b090a0b070801060c120315030804080d080c0a081806070c0303050f280906090803011502031c050712090c05040b01050408031909030b0a0b100e03 74
    0xc003020985a00941d0302c82100c040180603004000d80a8040c485010500c10001c00000d032400c4001e00c82c4510135540c0d0340c2c152094441da8024418400441c02c2120a88009880e0bd02c80403804503550500040502280c1c04401590307040d900100d40c000c10018050012070002c21249864060303a10f0002124036014403541640d00031000c1c0c0740188120f001c0443c80ba408480b140c2c0d400c541803402111568507040000501460506d0801e07004a0716040205000a4015800a02c070310000d40d00301c081e403000d080c40182c00d105043c0113510f0041d41d6455000008500303020751400300b800340300469103075410191607048a025144081043d50300401c042405402180000240c00d248850005426a40c1801c10340e01c1502080e0241c94551802414000700030341c0442e81003d886007660100250291440117440610490041c036409603c00d001c4981080010403003d402e5110a2074103035403203541c030b5980d030049100030b5500420a94680440310480d042201480100c6099840c0144d1080e0380080420b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 485692760 1250 485691510 485691533
    0x6091a0411030a022d1e3d051603020f0c040204030c0e0c1b0a050105010812040e06130c08010e10050f01050705011d0f0c04020c0303060907032007030806030a 70
    0xf0040d45c042c0140c208500d40c52078050754501c1005081151711a0000300501d00d6414000d21b81e5114450018050a600300490701040c01180c0001c2c060310a5507114548104032541d0400c6074080040401c1354841c00c0d01101c0c1c11a401521070740041c03a0031441e06540601303085154070b085028074418401080440c02c0c11540c481100c03c0b46081f60400d41390055000c10314890110804007031440c1450407210310100007110300780766008800802160762036103034098840b090300c625002090707403e100034440000c20740040f54101d200103102141d503000044502c01600e580c4040f5030040b458000041042108000c03041c4e034801030400100c00c0f12800e03c00094030a8a0b4403182a04000b8040360100401409501c000c008071505d0a0b100e2810910b0035290340d807004070040080240c001e034030010745203080138000e44d60241c50840195055507070b814180482e01000800c003c0c10992100700469210039030f80350007400f054010301010781d03c1c11035080181140c80c000c2c1455000354800e58440700411640100e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 485694010 1250 485692760 485692789
    0x60e0a090c02031b01060b13090b1e0402160b0705040602060f0903070b0613110301061b0b060111120703051b19110d080c0604140d020601030b0406091a0411030a02 72
    0x210307061070001c01003003401081c240c3c10201d20040300192042c00e002c0140c8d8040c08aa12a0750244400d2216605029420100001c07804410f40099600200e41c582600a45401c00c031143c441c2900300b0300e40d102e000140b80301366100c9001c503100007000d10140b6418407095500410240c1c0410396410101012075813441900d8014021001200118410360790f1444009564001a503060140d900c2d5409200404e61083c4500000b207a01201006034960894105d8464241c101880c94940d80c0da03100190b03860480c801c44800e96004080b162074905000c0401382203410f000c0c0c0c0d101c584030440507025941c0050f0120103d5510b5008802608503807100f801c20620f07555000354409006411400491110004901c00401504010644540e6200002038851003180207018541c2000501c40f000b90300c0b480d48032402d20058214000510224071310012094200c0d2084c9400201d14603551105c407182000c1440c1d003010301911500340710034001400d900e4103401c40100d025103003500d0264001250b21080114 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 485695260 1250 485694010 485694037
    0x8030403150f0510140307050105091e0603100905060a0b190e030706180e0f0106050c15040b06010f020d020c0d020406080303070f030f09021315080106060e0a090c0203 74
    0x7800040000075812000d40089042424440c50401e900d85060420b60707401010031045506241100074030300020218201e51041c0c4a0b5864803414405000c5d041700d003060980964030502007459250b880e020000e51140c50032142c414400e07400d0201c0803056070401707803ca0340b260401d148140444280c00301105c60344130707030050111595055410290b40b8401c00004155240c021030301c001031950703001008802c00c1850b80221040c4c690b01d590360705404050540b64000160680c000501446e4081c900a01080c410b401c01c03070701da15005001c0d1010310740c0107c50484182c6a8241800a1560007881d00c4400c40e0160001d040f080b20b245034000e640f440c14800c400c3c82410104030800954a41d64480c101800810307054903580d00e40648040c0c10412014500c100191804040580080d050303c502e001c000d03401080b080303070082d401d000c41010381803542c4a02130103440314000091040c800d104480040c00317252140e40c00740c03206070100640c4e0000c0c2e611200b01e9900700051a000c070344e4003100310f9004a41d81034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 485696510 1250 485695260 485695283
    0x9020906060a031410031a10060503150619300c0c02030609010203010e0a1107030311090d05010b010e0301090b010308070c23040c022a0d0c090203061908030403 71
    0x41c412000b8040718074285030a0142e21003407101054003541711078292802099002c0303000050110000e002201124064001c6c00500300078800355100c0c90007540c1103030010800c14080810100001e01d07035070000048840585104514080081d003220b1a24180885034208890030200c440c06a0300e074106034102c0f60340329541c41c0030012075a40580b100e00102d68002d401c403029407504044060007580213020f0465003035030140000e0500603041c090017620441e4850854280030040d07605034090900401204140302c4140a0801c80d074032610484061140105c00200b0800f013104c0000d0400100302800b1400713641803440040c0410b4611640b241100e0780b19444a07a00d0205090140d0f004866400c21644044842030306580796518031100d641d8000103c03800c00c216928120705036a100200c2d81903d140e804145060184c50000f004070140207040074100b064012000d940325201750046810040e4401e43c040184200703428803075030030148000301204a8034141e0501c0c0486959008038403004240d0252007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 485697760 1250 485696510 485696527
    0xc040f230903041a070b010b040b180607080c070603060f032006091002010c0207050108071209081c0501030b0a050907090e19080a030e010606050d0f020c0604030c0c0503010902090606 81
    0x1007084600404d1a4000c6a0181003803c80104a580c844241651b034450b40ca400420b001c0041401c8078116840b581d00c0c2403400c4442c4071391100d81030101111030303402641071000c0710100706074a00810043c8894406444164108000035048403481e4212001302141d01006000180c03070142c58001c030b18082e0343c21140001c0c00600040040c841e8448558010441007a540540c40d015081240c0c0001c858080d0760402d500d80f8011a002d2500300c0f4684005a50740d440c4c80386044e41a804801c62034003030480e40b40740490070100341c3c3e260b0b45810702c5244c04a98a034010014410f449200e0394100c60071010501580c1080c08040e5540e100d1401142c100541c2e41140600c50041082048a000d5820807030003d1603d01d03003041c5006800c680319040120f810000308210340c8606210f16000c0e10030300d444803401c240050000b600107142e03079200410155030800501405000070007106d03202e2403003a0b4030150f13400d001d0716180354400d045910450180c1c1c100f1500b03400603681c60301450380c01f04060700c0440e11074092 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 485699010 1250 485697760 485697763
    0x1e04050a0513061d010e0a091110110303090f0f1204030b1f03060204090f0608120a0306170102040f06050c06061c0f050c21060c0f040b0406020c040f2309 68
    0x543c004511800d42c0ca071149409013020f040380b0304840c814081d1800e181c1d12003d080040d502580002440c0304208a100f15030751400440c0310328902694a0701d07042c2e00f81400e00035455076205480c9075040e5408280f0340708000307208100b8480340740920000ba0012040320004400c440c01140801844259288001800b1080c1010824007800a14038100204c40c0e684c00c000e030096110380200c08050781010319403001030301140a0039088075440c40062041d031030030081031303c07040d00500d6102c020141c6607580041c514003648420740204001c41e00040e903940c42d0004031404107169038458820f001c1c0900050b40a101e010612550005090701c03401c100050190a4404080c1480402880c048a418005042c4400050758540b42d040a60300c61389601e84003403000519001c1c05c46c800805600c02400211301101e072101410500703021501c61404e058031184a0051a04179400800060f480b00441101d2703841c0c82c1c0110290f158181c5010880c520202c1d87d0602c802d403041c0c488904034200c00c1c0229410100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 485700260 1250 485699010 485699021
    0x11223011b0905060f0f2709070315260714010905010918020d110703020c0a0b0405031b06070c1203032a0311090d0605011d070518180901021e04050a0513 68
    0x1c48640e0084c0e24941c1d103c2e528040c600347c905260040400c240000d0325503000f072284e50f480c80468642c14a94a01e0078800007004440c5030002080c61032141c3c4488600c0c001040140b01030000c03c2201c100c00c541d01d00004110040c00d0703100a0422980d00000c1000c4ca06c291050061116242000369a031042943c0807409000340c913000d00c643d2440000c40905055020032102c0c10320710100c5141d0040d039915403030b0603424007450245c01e5060f00315405900c02c0c040c204010380390240c1d001d0007071400d0210715203400051142d07039488803402d01070004e450010542c1c18450003000302000c0c110b403600c110a0002d401d1143d44021b08039400d16568180c00c2d0040c00c500400d0f0b45c2e203010b000f4081e100424075440e00b000603207020311441522a2030700c0b80708403405400b101c0c507612800c03041e41d409040080c1401c600c04030f0f28071141d00300d8215404040f146020505001190720403a0300500143c0d8490701c2291654461300c0c2a0b041c005207450a101c14030840d6984801d01c3d0841d0b1013245c0c001003071298455444d00810 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 485701510 1250 485700260 485700277
    0xb1503010902130504021c090c091407032f2b1d01090215070804030602310807060f11060702160602060c03011223011b0905060f0f 58
    0x4102000001c1d40c0340168006044500c4200f408030121603540c41803000340e0190001c840082c0358a003500300740c02d03a11684505a1a07000740f8110703d000342c0d6851072504840c2404c103c14002140c402c10450312b9500f50003030b1040e04581040489440d607244103a418012007940f8900728620000800610540400d12420044000030799200c0502d184007086200501c0042d46c42d40c9040c49507107182d209240188200103c0075000760400101140750f8011300480d605ca2802150900b07014000030022980620292640142c03014130000c1d0400040072a0403900780b10442c041441d03030340e0744050100c002d010450200f21006410304e00a00c001d103034026030b40c481d00d06082c455203210303000c1013207401c541c006445c0c0010408014590491a00c4000c22600c41108846031000603108000412004c55036142c00d002c8180900394000e070084140708005403101140c00c2140d030fa03a440ba06403070100c80345800442c4c501680d60800324109071502001c6184d50180d42012407443e00d0103d00841c1a4003920f04448800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 485702760 1250 485701510 485701549
    0x3011203030207080c161409010e070302032502010501050a05060a0e010530310201050f070506070c050c0a120210020c03030f0d050c071a0a0618020c06090a0804090b 73
    0x1400400b58203006e00d010341c400c440c0004402c64070040207041c0320790390b41e05032403222090240c42c0d0303507000007a0003940c0701a1480c0a174980a241c004445140c6d04242c00304d494855001007019458038080006044464124601c111020007030080ca49070000952900f181007800c0c11525134031210078808440d143c101901030885030181e152220061a1007100303105402100700d0300040000c00c14200140c5400d41d0b030300c0000ca50f10b0071045015602980c00303060703d0002030400d286803030200d644060401d14144c441401080c0c3c500e44103020818180000040054150707041581945010400360f0700d207245610290007000f6107800703182e8462003408081368902000d02101d80e19200b8042d2092240e201c071200361962868880803900340049842221302c02900210a034083c0d95901c580b19980003400b030001901c0c507655400004088400b00103660303a071060100010b0304d8004032142103080000003410b06000e90050000c1c403000800000c152015244030010010b03c800140f004035004080149421001c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 485704010 1250 485702760 485702773
    0x90d030f05160f0b0a1b271502010605091003020105030408070b070507030908070b0712030b0a0602030706151208070f020316090b0a0f0b0d18030206160503011203030207080c 77
    0x307001e920341109500ba44944110130155070f0320300340740c02140c48900b072125428000864101c5424811160094140722020103070351100c905007036100e003080c1d80750f004d400e00300001005021b5880d0203106d250010f2506030384a02c1c0d82d140003c0400c100d840c460000078103211011002c02c1c1844440800d03240d206600407010032031804c1415014000703420460040b000140400008071380c81101080b000101d8000362440360030300d405592072880d2010206001c1e030030141d6403000842c080d9188000c0074000c0c21260050b41d5289080c3c00e101013030b920040402d1901800b007a5003004060118070407041c100c0c8e004455151143e5861800c03003121440c1d00c0000e9414460301d288140c1c1c0c208281c0c00c0d003081f1606920308100c5896680d0074409010901e2080d0384041c100740c10b0800c940004480202a01103030410001f41c0003001d60b003810248182001d0030b80c016440142009032441d01076500c10004140340c20501d043d50f26000f4541d0308180e0900f1b000b000c068000c01d864080061040a590703510b806241501e55 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 485705260 1250 485704010 485704013
    0x603020306210604020d060e0a0803010f0f2402070e0c0310140906010503060a240311070f020d080405121b010f020615150c0102090301060b090d030f0516 68
    0x294005503000c40c071034540301942c00002c0c42200d00201c2840020405080c043e5500d408100b600c4070300c1c25056405549403600100c80f0401031021009071031050240c2c0c3d0700d035418a4080b82002c2c406811807030040c80d0017002807001500b0094586180030102180781e4000700411070490400304107900c184003051081060081741c4010034040c1d8840e001e460083c1900982c0ca024160085070702d01c0555420140311408140d1a5101300700941c3d03c170303802a1070960910744c0d1340385080050384d140c086480840008000d03950815414014003c041382296220360401c10b140d00c44000450154000038480c5c50100341c8003040003001000c0d90300814004200302c6240480c041d40c503031280040d045001101c81c0d8950222903640c0903c02500820b00f503130303008104a9482411440403004040515a800175444d2102c43d800303981140200030b0340559000150320380610313074203040c01e49195401c203001504080c030022002d600e0340d28050381c0058052034010501e01d080c48064800d8030401d00d8a00841d100c901c031000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 485706510 1250 485705260 485705267
    0x60f08010603032d030b0a080d080a050a0b03100f110c030c0f070f170118080c1917090103090606090608120304082a030304240606051b0c0a06 63
    0x2100d029032203203e007a10030441428131a00c26620900440d08141e00e80904541c401d5100d444a800040c0403605100e84665509140c2554074100d07100186109040014509050140745c0d0419968a001e0150f1504200000c0d00c07200114960352210742d0320b1b0108058101550442c030401c402a24180b6a20220310000a440f68000035401d5024800c01d0900c00901100089030021500350f00d1494900504000340035140380d840024041c0c0075900c8807000810385082060301001c0c5c4c0d104607605c5a40320500c1c800e01e400c0c101c07291040003070115021001000701d9200c50041070070b100104c1000d5641c02d4440c00580080c804280040c1c04c0340e142200204425509601503410340300315204403404585030018048041c44200c4005105440920003d0311000c10744001025018008141c2201d0302210038041c0c5c0345801c2110162010a403880300b050504444900d4124550242e00d0140442810510041d0151044905a10244a2000184003006400d000d20806c10000a0200064999802004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 485707760 1250 485706510 485706521
    0x70506070815090411010216050307050f13050c0909072a301202030c090d03090e0a0f050603010b031510090501090e061311100e031504030305090a0b0c0904060f0801 73
    0x21b40075100390901c0c25098a860704001044903c000c0041080c60b00b84010701401089011185401c14100280c610600da000e0290500c1a9080d204141d290002142000403500000c3d15a07410302a440445058107002c0d403454401c00e2545070218200b0079207900c3e141d01c8090640c034850b801a0000d141980001b003c1020302608082d6503520240000c1c042e521030000c0b8442a520861a11002c00000701a400c00c4422200180d01a0404050203940d03428543d0a526044030160710081d0740f0b04420000300c01502c07a080c0c204070140c000300000310220b0080303a5500d201d900c00e5600c12921400145040c000640094050300059905006d203595500328203001e056403503070341c40d403500840c1c0018a0180300328a41d2452180c01c20a0394010b0030b030f08818481100c6410061004010300c860038100580c80402680703800c5254480f04000340d01c0c1c503040040c2182c50150402007d03410070324003007002c00c46590655400507550070344607646104a40008000b004160702c405066002c1702400036410341c040d80310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 485709010 1250 485707760 485707793
    0x3030304110a060e010c0f03030b1e10050a2102090d050c030d05090a060516020402070b09061506070314070b1003110108010e13031101110a140705060708150904 71
    0x2c81001a01d50301c0c2070316228002c06005002030300e4032901c0d1005c9001c048041d03403014040d00307000980c560500040390700c50000314000f040854034845456140e08000009000000762031074801d007814060107000f4001c14001982488140d0301e20b80000000c100c80d0304403000c4080080507080500040e14059032140c2d50851400d10900441d0703007007250a40248110386108030b004007494031450920b0303000e6400b50000300204101034600c5030b0140050700e40744010007025000d005d240c400c2d46819102c07149426170040a448500c4e000443d0720300540c0302c0c4025110940d43c1070801d903050180ca0044040c2d180150078000c0d08441400c0c040c00403080d000c00010041c0e9010b84100c0288001ca5070054984107402e01c200541d0201480c00102035151040f0005a2640304c1d1411000e0b94829401840c00e40361aa012003501d9400025070300c0915400000b120301c0c5841d6200c140b0304100c1c1580302d1a444010050042e010711003641d0008501c2c0c2554460040c0070300c0010401c0c0c04600746403d0041826070a03541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 485710260 1250 485709010 485709019
    0xc09131b060507080705011104060503190905100b010c0c090b100215040204050c090901030309090608010902030604030f050706050108061e150f040e2a12100203040804050303030411 80
    0x2400aa01a08050300c9040e110300b03450702c520300880b40c1c0d42c02240b640582c905a074255601c500c40d05440c0c3c2c640004000500c0966201a2a0f00b42030b03c0ea140d0106440346c401c0d12492800e04072100003030001c90141070380c10041000192104003800140c404070015540101300e008800b401003440306682d44441c00a0400395042400683c0300c1c2c0d4180c0e5117004501490f1224506040040d0051506410051f44002e0b08008181031000d98004189800d8080e0412404240d0b04440ad100000c2c051040c08000c00c0031500a201003041e07a00440e86485000c0c20160803c0249040040d00d94041d00c12900a594050760802c440d40e941c80d03e050315104d0607075a00d00c4400c50130b0039041220010064030303409174010a01c0c002c003484030001040201820358051039005515114400f502d203400307001088641e090900c10f00340245141c0c4010030515042404c1d980704000c02c0a00304c030746410000d1254100e4090035001650b0b915241020895402180d00203645440f002040000300400030481000c2c3c20410394 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 485711510 1250 485710260 485710283
    0xc03060124080403170601140a020106140a0b03010e22050307110609061801030e030403060b030609010c050d05100e0106030f0e060c0a030b04020c0109050604050f06070801050d0201020c0913 84
    0x81c04846280c81a600600000e25a4000c0820f0301003805116400c200141400d001c0055828120306164010301f023980c0140c1d54858040141c50020514203c0034981114514022828416140903e01040c001c03101e800b2403184c006000b080c0008060080c860040080c4007411500d0714140f940d81c1d00c071b000d007103072503100740d10405241d81005001c0d0b45540c82c00422446c100f010703c200c0341c2805080001c01d01d04050310740d26640700100040c001000994000d00b808243d00d0000000d151130118040c01c00705160707142c00700d040c0c011036010701910700580d0201c40104a0351248410113061000d20f40000c40c101010fa000062455003582c0404102d91208400344411842c0350030031929000226422000010104940080c1d035100380c3c0302c0394860324001c100500782403e612585084410742d000480301588003901744400d00c1400c00004c801180c00500a0440b80341031a0020480340061194034000d03091484040e003161300a010082c000d5101a080301594a0100414104411420341c20350791920401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 485712760 1250 485711510 485711579
    0xf041704050a050f131a0a081c08040f0c06030212070201140c07060f0c0306051c03020705120114090721020d020d05030c0307050d030b0904170c0c030601 68
    0x1406450032940d0003402220918541000c0c407610030350b07070704099500c50303d5017880401c10900c901c81c07802e001d481030a200d207082c2d1002c010310002c401c05401c104140e030f000c1c50300740e8460420b41c032204030b46456500e00f08901d5205c501d048909440748000c010034a00b00000089115640b5601510303e86e4203d071b442c0c500603100c235075050303007200c20359034501c101100c1c0e400004003409451401003044074440e00001a00440c400d60100444100898000c002615103801b0401841c041c00d80c15416500300e0a891511000c1c0e642c080d41c2d980043c41203078002e640001c050f411000003940540b40c00d61120000010b01d24240002c10f40b00d403402d0141030b0244d00c4a40d0304051907050b080d0946840d035030240c640700705042c0307076000c0101d004200c11080354035100c200b000028400381440640f40c0035200707000170b001c0e0b010900009001c0c3c84c803d048103405043e0031002c00010501c00307101a1203d01c00c0004160f0703141c40c074030039003824100791405440d014414600006072240c502c201003440d8022401700f040c0e212035007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 485714010 1250 485712760 485712803
    0x409021c030507330203072102030603161d04020f0301020a030608060703090c0e04020a170102070b0f190902060d060b03160e0d1509060507050702030d03060617100e0f04 75
    0x40c04000589084c00007000c1190b900f03650045400c080b0038184503031210181141c04200c08038a0410441030b54001c024048035040402c2040c0d10402015200c0810310f0905000b81200000c50350001c50300d19a0300d0210b410f548803d40d80303400c528805802595078800b07914014000c1d080900ca000003c5c8280000510f030075100340b01300050f407648248091106441d1110a03041c041001e84280c1c4d01003213004001840e1a841000c2030b03403481c01c050001d61599040d003840c00b11504020800b0842c0c031480c0007007016400c0e078081c503020010181ca20001d180c800e14000320722540200044104054a40580441e11401d10005103102d0300e149440d15802d2040310900300c0d40c8031186010302c0e400040750410a00000c10003010140e050090907800542a540d80d01d075401603034010354401c03020035000078510040d424107022007140080c090506100d0107140010050120084001d800c0c0c0913000700011a4407030040746a003034000c1203800040142805d1038402c0700d0b50300101380c5044400a0b100c1c900800c2c0e007100b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 485715260 1250 485714010 485714063
    0x13021c05071b1704080f060105030106030f1506080d020c03010f06080604080c0f0d090303020f060105060f130f24081009050a0f0c0504080c060403020a050409021c030507 75
    0x56640c1002e84621003620700080400c0389040718241c00040309040300c0803a583c0a4002450306070010942020480810b906040060b00728a0203030341001428000f107102c03040a403011035484000841403c610904040c001c1c4191307004610103000e02c03108070071034a500298820f04180100d000708000d40c2000f045800b00e98880c455411140c00001c002404030702410041c1c58080030020a448011418006082c1894595400384003c41d541a2050040c990704024803025200744030010720306035042c40005206c50158a10034a80010300080d651941c0101441c038a0040a00498600030760380c869031105100607400f0800c3c00355000d00108891442c1c40707401c0d81402010b00a41503124a81041c40003405080e0003003052020301e4072005140c3c600b0f1020b105407040403905d9958191103c0c20480158201a600c0c402e451041005110900151303452080040480c0c90445000400091600c00304040381604006801124054201e030340038560440020109144506ca00c3c0c0174501040140906090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 485716510 1250 485715260 485715271
    0x8030c0d18090b120106091b170a0e030412080909090303150d2d02040501080d05040506070f0f0c090c0c080921120c0c03060712020304030e13021c05 66
    0x1003904070704002c10031040d4005030703070603101401c40d1041032400c80c4c41500f51401d541c0300c0302425030794001c0608010700d103145215103580c951a040783d80039014000c600080c00d02030500030240b59112502c51000d20108200d40003441c049501c510100341c60300340003d035a0450920035014030504000030351910b81c080100c034481c620034200d440107a018901840800751980c2c608881c51058000f8082204403500e00900b20808881c030802610500391050006464041c1d00c1a0003540c0120303000800d198010040d0380981d4400d5480b83e8031100b440c20070b0401111003060181001380d06203c00010f10002e290303214140e4040110030b100c1c60912610840d01001120340180520308144000d841c035140c00201d142d0400380000c1c1c070010110100d000c1d84d00782003815180c0141c0c0400059504c000c100240244480d2000890283c206454690300c06801c52480c401203011041d400400502054000d50703000c1d00d10100600f0081c00d02c1c043e4440140290320040e1303401c41c901110501080306d801070340034941c41038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 485717760 1250 485716510 485716547
    0x2001020703140a050904110a030c050a0c0f0807081b160e0103030c02120304140f03011404170d05010f050306240d02060f1201050109290f07060608030c0d 68
    0x14442c848890a0300039003c101c041020030002807200359124060b070311009022489260341c4841e441406021125610280350078441c040c4802090140c000b2600d000050300401103004031380703061500080c240f0450000400000b000706240f94903104285424403400811001c031140c140900c90101c1c1090b4040c86882ca400300380c8030060002078890003900d6840b51001d02404245082382c0201130440d0445e400921070326420020140062514a100d040707010307010f8000b0441e80801045034245514014805065800b10202e030440040081044844c082059030040006503160003205100180c00d2003018802c0c450440461810800b5a590082400da0381c884552a03641c640144054901390b40d0043e82e00510030b110501821018200034610aa1007000c80089907040c00000b42c00c00d4001d811800111280e864103054101d0124010021b1091001c5400c2e105c17032070300c00382c40c0e118410f0000050210f418120005100c0c00e000002e0960480e4080c10340700250150b0000f00e5014203005510243e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 485719010 1250 485717760 485717777
    0xf02060c15180d1202130e2a07020d1b060507060e030901020d030b0409050102030c0705012009040911120106090b04021c111303050c10031406120c030d2001020703 72
    0x70b180140301c0b04004c5108040d000d42001440b44100105800c81d0b400441c030f8241c8502000050001c6002402103003120882d03000031558402451103080c050000700034021010481d01005000b0341b29640e01c0c1201140a400300302e9500d40701c00400c5604441011503801d400c01c1008000c0200110542d802c0c0f0906900808549040c100b04030b010f4290000d034150410799810041c1d01080080c002180b2845000007015a10301b550700e0881d00310356007040040500100e11640345502c1d0200f1041703c0e50440c0482c1d0100f09103255042111506850030780385540507414120500340404190040e07005c4420034001044151210411b010991007030011511407400ea143c2c01c0d044112041c0d20403a140700b01900d1f40d608121080d140d111500c030f6035400c161083e9000e14048035003450190440c541400552800b13000002c1110511a64020007070225885202803000c0f40000d48801c0280440c825001000c58100070316540000c3c0c8480c038001c04103207829103100d12401e8071500500803035a040c2d515a40703013901c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 485720260 1250 485719010 485719033
    0xc0406060f0e1f050919080a030c020f09090a2a03061a090c0c012306061e030c0a3c09030c0308030a0b010815010c0f02060c1518 57
    0x108040764a680c1540319400c5807018a500f0a04142280e4012850710366903501d0620302c007080207a10039052041200610ba10307051040503008111034800c40d9150410b100ca0021a00c0080e81040503400c4103a04158401c0420442240014102c0f1200f80111443c1810b0f00310824443d0305030241d00d0001c242041680403c000040c11513005044441035103140d000910964000940400c00c185c070185c0e007542000c1f80303014024400b0f100b0303981082e0b0b041d0070341c5048420300810040805c1006015503c10030000c01c45004005a80503010b01070500d6032012036580c070b40300c007098070342d90044011a8000f03010700700303510404c81c209100400c500d02400003c1d40f0040034078034400305021810826804100d0042c000000081c4035588540185100d82d19035510391501003a800d00f16001211400c0c100300300002484442541c800f04070b07080c10801c9c030b8025508445420102e4810000f020002e400040018075020701c3c0c200417403c1a035404019010f451680c0b1031181891412017048440415500020745144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 485721510 1250 485720260 485720267
    0x160f060518060c0a0e030703110310150614160b0109060605070218270706110102070c180902060d060303020c03030f0a0804020d12080f060301021804150b0705010e0c0406060f 77
    0x20f44c0107052502c1e0f05807045000110342807106640c030403507001114861916485c9800d1003400c105030a031034410404070100410084545203148903410900513991000e000e05207907102225000c1e0424403080c0b004020500e002d550700002440340d0841d0030f140c0000400d8051040c411030718040e40050690049010300642c541061101524180300060b810b5804040307400c2c2c0c2844112443d03801ca01618001e481c214014102d0740f101044041070345d00c10003141c2c002410400d040416192901400d4400c02d00e24000c0c40300600ca03c6d400650b01040c0445c01c49a8442e29810801c20360340f11707070b013528408200b0f6004c1c16981e0189030644001003030f0500c08410254825840070340c0c41070000304040c800e030003151280d00640c8400c0480600003407058040001101c4940c401a81115080c0d008524101c0c05440c10801821021203e5105a4485030743d902c55041e42803040003d0005198019a0f418045c90194001c1c0400300394000300703005180c404101450544940411070380c0035220044103103120786048 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 485722760 1250 485721510 485721517
    0x1d06160306050a0905090a120206070306061707030e0c060403110a060206130f0f1205031b03090307060509030712021b0405100302130e072c2208160f060518060c 71
    0x1400358487c101c6408081100b01e001d40c1c2d580c140c1c41e006030002c1d09009400a059486e950482014004c160540d49204003180400b10703880002ca00c3c3c00501003650500e040e00300460100c09036800800820080b080c010214501411100d08a4040c6865682d034002640c44d00421030f01e440140c1c44212080380480c683d0f14507000c0091203069100f80c1581c20341da505003042d8654154000041e400720401c60300f000030104004100c02c050f080300c1c0c01c40c13802245041d503038425074100800058031840440d0040384c08006691086600031034511000c411000d00940d0b40001304111143c0e429505070a0070642032a01c645802180d5410702071848a082d03801384082e6080561182580c81c1e03666190401000d0f007408105c019040c51000c880c04007981c1e02101e505081440c11100f40300102c0c0c401c0c00031980408204c805070a80d0141050340c18461030a00c03c6440c0901007020503014a801c20700410000729007448500244a0a030401c06070701e41510300b4902422002034048240c1c049008681d020030b01d90040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 485724010 1250 485722760 485722771
    0x80414010f02030a050a152709080d020309070e0c0904090809040e03090f04110a1413090209120d140306040e0f10050f04030915031d06160306050a0905 67
    0x81146610428140c00b00d034002c03030300a00352664450501186d14070500600604558212100b59002c0c1441a0f2032041c8040c9080c04007440180402d03854101040d80041c07168039040f0200e107443d007180092610280d8000c840e008003601a0403004200b014914030350034040c9207000045030034110710300c0034000148581c8400b540c0380b810512107100340d5076a03030050710038100c030368000743d0744441c3e0744418403503034143c81e02c00e2512032400c11144521040c080c00c242c82000600345090703c51340c0070300b0514030520b00c0361007e681d030f102a80c07890205082040d03030001d1800580641c0c000b80340c0050034034030a8403003a0850850b00002e810603510121526500040c5820500080c400541ea0b0b60340300c14545043d8903001d200c020ba80042c00040c0d040c1444c0e10411341d001440035a010082d286c20395005110b90028000d0642071924250207044803407107540324948002040b10310158840c9500d08095568804598a018104401040c040400d1280c01f5920495038043d1a1281990402800d0805807500a10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 485725260 1250 485724010 485724013
    0x40f1a090307060228030608010606031a041503020607060b01091202010c14010b04020412020a1d1b070f030206040c0510092702040e01210f030c11030f0309090a0b01080414 76
    0x3000e17490742c0480001004810b0703654400040317940c1f41511250035141c40368845803d140c41d00c410300d101550001400000c2080423500050001c21106100440001c03540001c0c0d0440004030f03480040100540c000c0f039515200342c03500308090b5901c0e0000500d14188003402400544080e1034038001075041140030890b204418008181c0ca2114004541260490381c400003000e540f821055041d400c0c20311010307000d0400c03030900c141e112441c081034100307800018003241015403004920064042c0c03403400382c03441c4961008a0700c145890f1401c00960b14003041d14140d40c11250508005031515010950700302e40c0b010707500c94500b0396141195422003100546034203629640302c2c0000c54641d440c1480140007800309070007905c2555041c001b08411040a80ca00c451500c43c41c1100030010940d040001e0725400da0500d420103401e102464030041540d11890515058803d144001c0301c1e001000c4040c16482c9425610b040c110740d1610440c400b550246800c0f04e000c260b1a8011401060708118500d000055800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 485726510 1250 485725260 485725297
    0x6060f030a0b190303090e010b0a231c1803080601030c05040b0c060115030b030c210d03020a11060609011a070506070819021207032003040f1a0903070602 68
    0x100801c00e2001400f00b095016000c3d01014000c1641040e00306000e4030b80d11941d49029030502d61000814070030b0030b44c040140905900386040c0b40100d08030414131020f8580c08580c46040600d0101002020011000d00007820140d80c10408241c078502a0085605590f45501c5516198010340c020141c02081d8810004200b0002c9409a5040300071301c42e00710440000d0007990326042c0c05994510190380c1d0901010f007810420781c8569030014201c258410100e500b1100c1030306880350b01c000d66602c07a47e455094000c0d01c41d0603040369055806080204084d0311085e442d01c4802058030b4a43c88111615a48401600014060440e001120a0505286050031840c040d01901d51503e07100c021191180003a80010801400b5000702140fa8541d01c000b480540c00e112402c69040622800100801d04150342c8001210601c68030003c0c0300200398084800d40e9407070401e400e00c01e192241203001a158980c00c3c1700180481880c18590620a080b04030140d41040c200380d4506029601c03c034211041d102400c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 485727760 1250 485726510 485726531
    0x1f0903081b0f0307060b090108060705130504140106092c090312010905060315010312111c09240f030510050907210b01020d180f0b0304050c0906060f030a 68
    0x1c000c65030045403450001c68640783c452174035405070344001100034014001c0c0e400400c2081d07000a0800d03003221160406030b490355035090004020040d01e52010743d1042c1024a4501c03441c2c151031506059030344581e02c0000c1a42c031951002c0b00c0070400d03c01c04100c020204240389500030171001c80e0b0341210500064074074240150101d07420720701081e00500c007019521424006c85280030400c4440e42030a0320006440c540c1345d5112079420700001450f6a003442503880c1550480c00051100003e40804c5d001c01c0d1980403680280144509c1c01406031581c08030300c8401d28501c0c001d80d814154003440980d03031007041c011110314040f0043d09010301110b40030012141c006c202c50741d500017820b100e0403460b56000b082604c6103040904003981103508400042c036041e0078148a0340d002c21400c0c003186541c103110044c1040c070001d20810350983d601a00c00304646143c08903103c0b0480005501032400b40003105d010300403c2c800c122030b201040c1d5845a011008000a01a940c07101e00956072000c0500030002d214a10b2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 485729010 1250 485727760 485727763
    0x906070803040c0b2206080708040605060307030c090b04050901020705030a050d0b040f0506091006090501140c0609010e0f1605040504061d030c070e04020901050111030c030403030507021f0903081b 87
    0x218585000240100111403070b0100310b0317483c1001030040303280a480c2407d0401c00541480000761024041d1a1240300007552602d00300b2000c1c00455101c82003403101680d0324030b1a80241080881141f080741050b000c44c500341d5050080c4c0e5020798020014512700101c110040c2c0700c5034007401c450118140c03561501d84083e551880f580035500c02c20070021549140402c10041030b000001e19000d0148800d0380c040c0891580300c110542501c10a082112000c3c049101d0f140117402502c04070141031151008004485106403c060f40d41d60403030b0100d0b194031541e51300060f01c070748062081c11540c20858000304246e02d400c0d001207400c0b5001e0080090000318120104070052008060503060f42d10015410206880c00c0203420002c11042e840c40c00c090900d9070008141e903a06106480c10010103241c0064403007003e10403a61201810070440b030ba1565649805045d582105074141e10030b00111060301e007002c42d0401a50641c20f001c0c0c2e101186c4070f007581d507881015000201d040c8074005048a410040c00740 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 485730260 1250 485729010 485729017
    0x1d100909150b1801051c05012a11060a0f0603080a27030f06020d15030b0f0109020301052d13060f0b0406210b060d1d030906070803040c0b 61
    0x1510340c041e1500100c2501d206071102403000303601840e407650f1182003e4080c07020207415100b08a452901d808010414803901c1c50340c1550141040d480c00002508a096507460100c0c0745c19105030b080040107000c041601e024208a0344001260000c00003d000b0190a0f44081d41040103000d00280040d285e4950020980055041c000400d0703620000f800000c00c0741d0f02d0f6050030301e02800000d106e5821a524001601c0d510301c1c00400c1d0940108004455031229001503040c4030110350780d010025501e04102c9010141550b580310365a80c0c490010981001d58001c9a05840014050881f44040010000052407401000a0448038a0400344205070b403000c081c40628540368030f000c00d202e0b013041c91480c1c50f1800da40c05140301d030300200410002c540d0406c0001e10010304507410101014280c04000d4054183c1d403240c6a8403c0c0c002401c003c40e01c90b0303940114000c8140c1003012255039a20034609aa0f482a0fa5195034481000c0c07012500007172545000f5a40300d4820032006840c207070760390314803141c0b6003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 485731510 1250 485730260 485730263
    0x8120307180b0c0d030b040c0210270524070801060c1b0b09150405030c0909072112030903051902070b0729060d0f030302091203040812041d100909 65
    0x3c01c1013107030b02d030200c5d0700d13009403182c08004032410010a0600c040181d82c8078181f00380c0000a50b01c9441380b02c2c19010120b484011007a010101c0c4032a0b0004e4509207484000004c8450302c0300c0e0400b2541104641032407043c503c40d000580f560340003a42482000d0310080d00001048800c0c0001c180986d41e02442a9a2840200b00100603a5110b11211080080d1645812122040760b0000c2c00100b00c3c42d600000d80708404d02090381c401d18035484400d000b0b82400c5154110a400fa9190115801d60807584d0700c00e001c24078000e900e081100d482152045044d9001c03184003800042c1d081c01489440004400032078101328240c01112503a0380e4403c1f80341416005580c0a6031901203040e0f20300800c4240706a460b4040e00340381b8175540c0714a0004002001c809485501401e2840302220f03400425009504840f8591002007a001a100f4180f041c103039030703511a0103100303850b000d0042c0200c40401420203460030f80d241e42d4032581e01070440e007410609200b0f000b8841c0250304103505002850100700c2c480d44551a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 485732760 1250 485731510 485731513
    0x6030c0d0c0501230301061107030f03020a15020a0816020a021f022404030c02150304060905070b1804091a010e010608150117072102070b0108120307180b0c 69
    0x124a03020015004446203040307040050841005940c6030b801c44c0382100e040d1512405c1c0380c0f00e941360f103a411614000c0907400080000322407090747d005241c2c001480f4240c01c2e100341c0e281000b0340d1140e01c000050b8001c015001011403506d0740444c03008071182e8100b01007217200d88110740743c510346900003071401d0300240036101e4803a02c207005002559506001c0e04080c1108550822598a460348900750410001800036017006500c2d10712204540d02d20781407280003249607100b107440341040c0c10701780024550840110f90307900c0384001c0002d05880241c25580d44803820038000021088420503c070140502410441e42d2854110240c0380e80618051498003802c1f440d0914029581032101c0603040035005802080b461155880b0000260f03400b0002106075060300c00d036042d15031076403042920711107075060001c0c150161200c44140040321a40c050100d807070143d1900081a6601c000280c1c039289038104000f15000c1c2040010007031070280ea150500d203041284550304a65403a600005940c00400e40401e0340d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 485734010 1250 485732760 485732783
    0x10e010c083009030c12030403030f06060806030714030a0204020d06030f12030e120a0309050c0901060f140f160312050c0d0e0d050d0c0c05030406020105070f0c081206030c0d 77
    0x80301551410b0703034410b072440000c518107100c0305542035441b00402c500c503200c1040007000800b014070a410a0840300d4031004244802d5444800c00f6141400c101c0d4054043c1c401e50300c001a4524103840401501007001d80540b0050f030a580a01c0060f501020210011075120b40002000a6210524a0016005202c3c44440821031000242036840401003401250300c80e10b90f0700c51211601c400c84034011203a04001a403041c135031425504020700416425845544600001075103034105503102d034443c034142d5901485e81c0e010706040280f8022014441c82d214418460488040003030620281050b02a05203000c1c8d02c0c0b40c00214030309940c0c045503003403410031000c0f81006000d07003070f4080c00c2503251843c006403180e0f1300009002852400b580b0115492191662541c07024a40600d41480d0903a41140c1aa0355698403108081d02030003003519000c001590103018081d00c14819204d1050382c5030300464580c90b007040d80142804110b0040e00360780e414020b62a503240c240d910624142e07105441900f250780c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 485735260 1250 485734010 485734087
    0x61b11060d0617011116110a060809010c03020c101d01060f1a070f020f040b18010f050a06020d05030a110304060501180c1e0908030c0606041802010e010c08 69
    0x15032000f94400c6095038100301c801c0d088808500c003a2007410000716500640302c0b0752403c02d2105007034011842d80c4c01210204012406640c41700e0311510440600b002840181c0041130110120301c2104a020159000407400f100484100d800081502c420701d051010001c40c550442800c4a995503c0028610b62030201002117244040010459030a0080303540d0500985468000403665000c100a10078000d08131600c07182c0d035840e0710103c9403680241032032079403c411a41c00c0c0c1701c18200303008183e44014009800919460f0440040041e124658007074034801038a00310035103907504080c001500540c3c4a00a003004ca40080b0b014520542c016200461a545810080c01d402980d41c0d00d521051401c02451804180d080b40c45420944d010741034000040c02c0140d4100d400b580d42d5004001075000000d001040441d000515038001c0000300c404005146048801c94000902d14600a01145040c28921295070161984100c1503005491a07450074041d0031250a0500c0c06205941c65030109000341d88 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 485736510 1250 485735260 485735279
    0x40825060912030e04180f050c09010f0920160c0602240a18030c060507081308030a0603081c06050904020a0e0a020906030f0601020c010207061b11060d06 68
    0x100a1030182400500c1d14101941408603104074107001c0d0034002c004030784441c1c0f5103c0350b00078554588540001d054a5019161a01403410740300400d44040c0300b0301801410b113242c1035094604a0341000c40b100301c060703d441c01a2001e85040703810b002400125003520040c2042030b900501c0c1d42e20301c0b02405d810306a0907180c2125a07079040d400c250300310740c4909206100315124900c4a60000d115402c43d004555401c00c1402c0684074402d03030a5016661480400e08040d040028840440d200c0e440034030155a07038880c122555031007111300c295082c0264003080e012030500303c02144c01a0120401091080d101c0e01d80300810ba1141900c00340704402130044074030000312031050320b001e1300b402c83e0304041a003000d40015107141281e01610640c1840000031684150703007a0b04031a90000c010384000e4603490266079041c070041c011a0000d000d1300440342c00008a40c40860204241ca00c644c881d030f400700030b294910300840a441801200c17022110000350724199661f90150040c4024202c0106546040c0a070a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 485737760 1250 485736510 485736583
    0x1e01051912030504120c241b0804180b0913080703200d0f020f06010305070302040b210a0c0503060f1f050316050102070602030712050a200a02091305210408 69
    0x5030315100c00d11410300561607115014480b81103c423100900d001c0b51504000c040d80c85250b03c200062941c0012800d84105aa00007203c2d180c0112158561a51601c100480054601c81c0080040004100c020002400351b60030454003456640e0700580549103892440c40c003803d181100002c944202c4440c921716904005415079865240003500c25541346589803641c0b59000d003c028403540c0c40e0b017040750701500c42040b003e078200c400d03402c01500131240380031090721b0b400b800c01e013034a50680c000004a680c0c200000e1231402441030a1000500e0313600e49065001c41d111800510291884024000485580821010501d500c1410120b40121b29040000e441d0160a034050380664100707000343d01c0400ea000d000c4540c0740140d82465079880c000301c0d40c1100e400114101114049034241e403640001c42000400c543e03000c0c400e90b550410b680744d00048907420250701e14003e06030360102040c052860080c0c8005c100c120720f489251402c1c44d444110440c24201c01d43c1c40801c05201c00203d9019452240056 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 485739010 1250 485737760 485737799
    0x60b040903020a0204061203020a0b070311030412080c09130504050f10050f010f0b0a0e0d0609030305090c010e0307030206090d0b040b04050c01030c05180a0e1e01051912030504120c 80
    0xc0f40c4c7c080000d650180d181c2c90101e602030160f802a0000800c514020b0b0880d180f94841255500da403881c1a142280020072422a401d000070900340c00101801802d400321042150001c007180c2d404213a004060003d0400244100d0300b80c000c01e20980c0d81d0309400c0000f40d01d074001e0000c1c0070400e440c3c0b4403810000200164003642c480d80c089201086414a00703070440e10346032010b2404420154505011500d992004240140071526058540040c1036056101a004078000002c0d5245c801d01e54004540e500c2e50900e80c240e068201a2003000145002401401c96410150020000c00c4036a00c4840094004076415100035044400300300c1001800d005820021000b424100410391841e040107215028290441301c07850a96809042c00755200c046c04030044c443c490b4500390780d14002048100c0001c0000803d82040c18807000401c1c0ca01e440421004401d0081c884101003d290010718a05080b07403c4090307051240c100000718425621030030a00409014810380d910b0385281505c400c081d600c08004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 485740260 1250 485739010 485739029
    0xc03151d0c0901053001060306170106030c090e190506040b010812090103050c1c0b0301150b030f04021f020c0f0306040210110325060c080403090e04060b040903020a020406 76
    0x20070513a0800240c8150100300010400489103110341001d2003080115040400e603202d5000288055054001c0019190303080c00e0f070b5145580c0127a030709083c0c035200c0c040181590384018090103402d010303501444a03c80007004585142d44104003031030403c0f501c1c05007030b0382e141c005504000070b01005865150040c0103100092254150341c0c04100c5403401034090782810152600d011030150f030061000d071011400e00840e4201c02c241c003c0784a03070080604c803810a00a5092418400d13150141503420300c1100c1c0c21503c010b00c1c5a951103180c00f46194001c1040341e00543d0b041000144007018460500e88080703980041c041c011021081041041070001c0c00791080d030243d0100320040c0c4450b40d50000c1c80500e800e00b01d1030518600c60407800c5001e5244000d82c2d00d8407011140f8403030b04041c83c005803428003c680c01c000c0c4d45500d4508035040071045901501191140004000081d9040d2881d58000d004000002d28603e46c400014103959030307180309400590011040d2410340c54603101343e20040c0130004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 485741510 1250 485740260 485740267
    0x60601090b16030c05013602090103060b120715120236030f1e03040305060112021c06020a110c0a050622080633040c03151d0c 56
    0x41c000c58191003030400b00c030074001d1141035000815009510903000a644100240302c2d01c541012030b0000e0031000070340340c03862408155121141140600052003415000707030040c0e40c40d0382151500b1010305040051107410002c40403c3e2103141e081030055030f01801401a010b00e10924200c00181403041c1c0e0140d80180c20f10403c003441d01341c203405441d03801d4200c208105501c1c6200c007003040702c0e000b2844048942c16006001d00740c8020000070601000100807400031103214202611901d903a0300403400020265840328006000d0311a0f04100314280e0b0788005d200480c40781552018003080071000e05d04030383c42e68010034441d00f09a046514807800641d124010160401341100181440301da500c15180941d40003e00e050004151300d4115405c0002039170694401940c525034560380391021103890444034007001000028440c0d5a0341d680d801c10440194000251a1004100c0141804a5440706259a503200f5900c480d0045454030000e0030402c0300707500c02c516607007074481d058980102031200980c03080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 485742760 1250 485741510 485741519
    0x804060b030303070507110114040b0d060806090c0111030c160501120b0105220911120f01240c051605010e040519020c10361110021501030c0806060109 67
    0x1c046d154010b03007200d1118100300c000c10050303c0e80400311010340e48800000402107181c0b03000500414211808240821101d40d95070051a202c010942c3c500f903281d04801036076829903100e00702500002658000b900e00d00b03a1180083c3d40b41c1311481100d5811240000804c00c001d6800417130103d6480603a040074003428074250002042032090000c45a00b88914148019803240e0f800b20300c0010b814280810448001c40140065080e0411482c0300d00d0200070000040e880718204a81504881a40b60711161403185640034500c05609840c6c60002c04c00d40072409800301e8820082c104840f03800c50f52000b50030381031034001890020010501806a410103040c4144a21442820902a036481c000144c686805250aa082c002c0100f0400842400e20318010a400071500180d0714581c020320010921201351034884580f0540c00c3d0000d400340c17903c00801c20650400c0500c010840a0701c2c415030b441d81e5a03550180c540c481080e0010394904131002c00603c000f240800117184c0040342400c0108895250 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 485744010 1250 485742760 485742767
    0x40f060501062607050f0d05060906011805012003030711060c0f2d1201053d0201063503030c0a26011e05040c050a0305250804060b03030307 62
    0xf0f4282054202010350004400d03d100f1825140448080411340c1d80d1180c03c001004040e150589995201c2c141040c00700d20198007406d0403110600d0f551441c8240645424019158202444040003140914448004480d081400114810074058a0750302019884e50401e51403c40c0040c45d015050904201e0300c0d0030f005105d804e5036515540b40b0061041484000c02c0d813080d1580070b400c000301c41c001c00314103030a008d54508000e0781600c01c15250105c048081170880440c41b82404058520782d0030351005a0426000036103842c028202c0ca0002080f000d907204024284010800c0d9040c0c1503441040d1510204500b8441014410003014020741c103508044c00740c0c090f00e202d6a01c00d0300501281c44d601c104500c0c5d50a548404ea206110f074140c420350b0350b5001603850401e25040a5a40b0108840b0104151500d8420400c0202e0700d076a5184c208444083e003a402000c02400e8248660403500100d8540715041c0c82c0054200000e64501c4d400f03007050311748101900c0e142900c1c54400c6d001881041201a0b2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 485745260 1250 485744010 485744057
    0x91202011127060d02031e1509060607171809150a0608130602030109020306030d03090c0b09120604030302190e010e040f0b030723010c1a0c0c0105040f06050106 71
    0x110300c1d00000404019400928a0320a5004d1345031194004004c01900e81111041e660110307000c038030070864503a80d020405200c4d1180400440d070003203c038000304495040003000391080610405121f504032880000340850f5070020444d08042c400e11500c4612a404c00d0f6042e10380020006200a001d0701400000404042c0e15024807000c20402d1000111101c50780d124028013180c00041c119540d58640c26003034041d500844500f40a03200d4945018a010b01c240f264068440d00310070940390490909646c1102e075442091110740c00076203039003082a81c12040c0102802130340b180d10016a81c585140d0180010031101c01b04405000020f0342c40801070340c110072080c0c01000c088a00003060004001558010141c0519280d01031180d0500414200f1a03206644880502c41c0c06007200080541700459101480380c000401c09140c040c0d007291401500e82110340c000601150f158105807030f4054203400c40b001114280c80c1540035208403402e1103004d100b90707405000c00d441e003981040d4040f5049850440b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 485746510 1250 485745260 485745307
    0x4050a0809031507031b11070509060103270c050a031205071a150301050a020405060d02090109080307110f101d19090501081b010c080c0307060912020111 68
    0x100c00054040d2150341c00e10081c0c9800301504050051414000300040c000e011103084070500c40b511030785105506004000500308503640c0c40040c4080307070a1209001c5201d4018050905050302c1c1c1c1e80040d048140036075812190003010000444c2c008c400e01300070b8400c2e125544042d0103080c00d0b410a00c0818881807000804200b581002c03540d541d12440e043c4000100c00c01030600480080c1d05108509031380c14401142c0c5d22007100284440e488000d1800c0c100e03c0b540c030800d50303c035604012049405041d41c0103440d0092050404021503991032107240c1c00c1d5880040122400360094601d40b049203081000d017400d420b4282c81c03001d5004502c11018005c40302c0741829030746030703036144291540f41da48a040700c0300100d00001070f800f00559960720080141c00d080c060700c1c0b030714003560070513507014050282888613040f8169903050f20074090f074484c84100d0340601c10100300d0340410403040000c21150300405820034410030004c5036101140350001c2c01c4501c40c1e92030f180003110030401c000c0b1000349280305c801c1d0360 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 485747760 1250 485746510 485746523
    0x7080a080403180303051206061911030403050f0d12060e04060e0c060c01020a11151b04051009030b060306010302061b010902040c0f0809030a02060411120723060304050a 75
    0x54680d42020740f82018841c4000f00c0401000c2804001c040c0d20034090010418240c844a046441d100100319046c0600c101240d8400c01103004030005911a89003000d002090380292880c00e0f0b1641c5640303040c08000ca0071449950301014000c5262540004060409040050108110f5082c855900d02c40305010b44054031030740e100c1d191000000c000344614074080c00024501541d07032082d0900d45020303400c140c40c90300c00314026520f144042030022445d52074900030000c1d0903406507542900c59415044aa140c0700d02000c051102140c540c591003a814554562604c603a001146503241c000450320340148030a0103504040b00410045e201d1b1000e0b552503a0640e107401c104600004a007d00500116001030341c840d00f0710b4254100a41c0004c081440c2415075603071601103580314880c13940c0d2442000c4c1490010b900c6240000d0200e040250760204d00d05005000018028444207480e28141264105045100c6900340c0440d4030601c4c0200610310700d4041c1c80942c114030382502d0b13840d1904000e41c4081d10b007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 485749010 1250 485747760 485747777
    0xb0d2c011d03131404020d050907170316080c03070b0108072d090c05310e070f0e010c050d080f0711070506180a0b0903100207020f0d15020f0d0b010507080a 69
    0x4e9036450f010344000310545030301004680740410700c465035208144101c008100c0c43d540000b10303600011040b1f407404604140000200d038445d655425540d405211121001e000500c001000510700716001402014594000c100650030304400300610300b80885805d1a00740c02031880060028103c9000044440d4190f00041c001c860303190594682c03103180c410b070811041408140c0e01d450540e0a41151440c1400071550301152682d60341000800280da2080106d00a440c01021551040e8121114124180f40481342617180b6a15030f0f141480d40c92101c8045946942042441e40500d240c841d8001c10341d10f4600614901a51003945407031481c0030302030081c18000703011014000010a0701c81a4070014001e81b038620f999514ac1c012940019910900c0790250360418108402140242d4050355001414882c21841e081c04100200c03844002c116181900004414031502c1180b014040c618842040c5a6446004441b403400b101c03401401581801810b001c0702001c658150306440100095007004c0a4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 485750260 1250 485749010 485749049
    0x10e0111192d0507050f0d06050a06030b150301050a051b03090f0a0804170606010e0603040201030905121b0a03050301170304032103150b0d2c011d0313 67
    0x340341e0701110b901c0303181003116402c0e01d00707122029440c00950350007581a24800350300c2e081001482d41d250b20000c1d911400c00721007103000c5803141c0e0000341c2003407124138002a680d42e039580303070580700100f152480c00040300b40310780309001e0500780034144d4030a18441c820040351409062603016081c40c00c0c0b80c0b00391410007000246044174100700510000c1d00c41c204603600c68483c2d01d0028215406801030580114164542c1410aa00002c8042c01804161618102d42d100071007800301c3c1782c00003001a8101030700e9180001c003082e000d0100d8040c6403440d80c1d6659803546c0c12209100070300d45600310200d041d8402c0d102360000c01c0d44001031364155844041401250389076120840c0c61405950005000a8150071810708520b05180c031406190039240c078140619500081040100a0382c0d100b01e20740704104001c684081c000a038852100b0034070468112046400241480205520181904406a542d45034030202100034106405461201d4002586401100c0080c050390101a124411004200c0c4400c6e05 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 485751510 1250 485750260 485750273
    0x90114010504210c0f151d22060e09060c0c071d0f0109051303050a05040e10170a0f0f080403050604050d03050601090803030402062203050705010e011119 68
    0x5004103030038022001000e100311000003004003c500c1c104c502241c100c600007030302582e0103003610031191840c07088500c603108200c05403821520a90f00704080d0034484100901a074840041050344a44010a918600740b000908011900c00d0341144c0700300c0700700c4010040e0031080094915440941c07071504175120002310f6403961070700413150800811240d5400798010b01c0c5031144000f9200d403564a0002e601c50f43d1720200c203811501e05403041104409609114804039014130000d040e41c400310301d0034518096541e0399403440308205482c0f05480d45040b910801c003400b030107105600303145824030142051134202e540f281c181101d0f41200a00c0c22413800032000a0110800035240250b420905440052800303180c81e41d200e04400d00c5c02d1000c01e14001c0032039029481114000e0503510418003c500d180ca4030b808204054100d0140000344800c980d008454101c040c040c0d04000b07510610003020018103103000501a04000d1a02c2da04000360015a103501c10303000103030381c0c20703141503201c0b0321004040c0d6083c02c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 485752760 1250 485751510 485751517
    0x60b040305120c0f060c070605071403070c05070f08010905060901021201031e080705010b100908070902033610140402010309020414100e010b1216021623030106050901140105 77
    0x13a480d020300410046200d625200800307410741b00e490704011f07558071440709030703240400301e0b00b80f1200400030700c00500c405003d0601655454001c90441e42c0940e9101c0d4441804101c90b040305289035151300001042050030031007207403c103103031000035030a1609962040000000512015214500c01d02c554003884c08540740d052001d07900721120541c1d03243c007070400074080c1060b500e1580c05201c20079030440d10b25100714000400e484680000c0c0c80502d00d020440d03006500040c0c6a4004c5404001802200703014170700000b07040d25280c0d42c40b000c800c142e603d03c0c241441020104205401d04020300c1d00085401c1c074007200d502940c24200000c4681c228004100100000f420a4040002c80d8050040d4101241e44d81000c40f00141c42c080890b80c1c883c0c00050342e60080d824045007a02550001c1444580e030741034444c0c50414248101c82020340388001c2d035484030205901020480d08012910011500c0f981d80010003110160000e020381403402c03011900e420414810004051605404000a6889075044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 485754010 1250 485752760 485752783
    0x616050409180b0702070605180102190606060908060403090905090a06060b13080f0a11060d0f1a0303120103020103020d0f15050f031606120914010906060b040305120c 74
    0x30030490052002ca54075400d400002910740d16164000201e80e184001140c00a440366035458a052003048506048040e1042036414158000d580010b00000740802d210034100340030700c802180243c5032003000b4041c140180c010615a4001008201c0401e8102e000701c2d04542c421040040e0035039445030418200b01d03165030000c0600d4180320001443c16120310103071100540d01e21141ca9580d640d9681c0b1030b5200140d449862440d0060420007000c2403800042c8080e12001600c258900400462440700f266044113254890390342e1544483d04004101040c4211410254011841c0c5810340c03145d041c2c400d0b0140310090405030006298880070301030340c014a1000380440014058030019805d80700000031680a45406021070210342070051800041e8081c1c58104c0b11602228541000c10440c2c1d101c80c215042094280c071901107600091702d083e204540042d8042c000202440300780f8005c1c0903604580d00c10f400c110f40038442400414000304100c031000c0308000740c2c3d40c2e030758078580b103000e06001241c040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 485755260 1250 485754010 485754029
    0x702121c0e0109030e06071a040804080f0a0c05060f1b010e011a0306100302090c07050c06121618050d0c030b0f0403260604180203061905150306160504 67
    0x91240001d5015007203c0b4120780700c2e8a40da07100440e068144182c81c091480c02800c50400e03100000c400801d0502d4141e0000e00039400289030584030f00e4820710300400c05250455581c400c202102c1031002082d641c5000c1c0c142140d2440c90703d030340340c100c00c00780e8003070075082540301c080f10342d01c0d01b01c9004e0940c00040302022280092004001100c1e90201080c41e080c1c04034041d024480c00245884d00c0a02c6c04000c1d643e008044002988403800b16038a16000300200311002d00c80c070198504107039644005031070016100000d42c00c0914041c029480c032402d12985d08010300c04102c3c440503007094504206130980b0429100e03040000490b081c90070406003a98405842e4030003503802d015100c840c042e091481540a40c40d1030741150400d0b4030081390084910351520404861401142c07003442c190300440c410301e006542d2007003140740c10b40009040070000d40d404070500d080300c10101d8490309503020340c9a000e0149030760986140c09181c04a0307200c41e802001d1200943d11150200316a0b4011b0065402810010a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 485756510 1250 485755260 485755271
    0xc0e01031d0706050a020f01052a0706320402010801120c090504050f070f06090303030c050c2a03070f12050f030406020102090a140a03140f060a140f0702121c 70
    0x64013a2407a4403014000006000d00807130310740c0e1142c05006041c0204200c0749898100c1c10500d0504198880480b404d80c54050100300040104440340a0495401d03138464020300815942e500c070400150031001608400003c0c6001c100242c0e0300b0598640c11110030b1041c568850307140c1e103007010200f411600304001851621043c401402400142c0b9021030f50000103c45c512500d460b46114001418401e2100291100006000103813090b0442480c240a9040050406500348055414034401190742c000a01c1d040034140e809001844014038041310a0f070180c10610708020850303540c2c40c0700d401140318020100c0f00c1101008020030055144100140640391a141c0f546c0d170090107584101c15062145240c0c000124204240e0001c68600e030b0781c0104000c8a4900e90b554420000503003a00642940c0030f006030300c0c800c14a0a20515215412410300001d11400f407140c600040040980342803044103403038040000d07072034002070321403800c030540140140c0300e132000842c03a2406150680102e810a0400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 485757760 1250 485756510 485756519
    0x816031d010209090903031311010905060a030e0714150307050f07120e06030c0a0c020310020403240203060a030b04110409050604020909030c0a0f02040e0a08070b06040c0e01031d07 80
    0x19400f6102040084032414000d4407161a500d64a000580d451622840c41c0904440090310806990764801c4042c1008030f02c2c1d03039803180000c0b2540c10240d0040040307a1249030400b003400c0e0500001c4054403001045001e44680c0e000031644960600d542401c0c1c1c00c0000011400c054060401c0d5601d0715141140321303a655110741740001000c1036618503000807964a0207120203901d002c030180d91260030a0100d860508041c244100c5d00310903009426030701801040d14071482e4400500060002e540580c907524a01c40c55002d160156400491540c80304074414014068181d80300c0307455001301ca40060f0b00049903201d81c2848180007804501d1940d10519040d1540700300700780802c1042c03199000303c5540e115580c1d1020502d4881c805e00c0c0f21882a0340000101e40c3c0016184009040d185001400015040702c40a092903d407074054841070756198000b047c4001000b8003109460f902c2003003501c0074490f030704120740042d005200142509042c50780318400008801e0306c81c030789448078100a03011070303070170a90b0ba = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 485759010 1250 485757760 485757763
    0x10b0d0503130602030a0f08060d0204020a020c0f030a0f080703030b060d0c170405060c0a02100c090512010b1309050c030a06021305040b0a0909210f0e0906010816031d 74
    0x407803802c2074030450354207000071128004403d484441c0040d840d00843d4203100c3c5021607030341c0b0b401085180d1160305c1c0c00c82d01d800350300c4500c0900480e05440d0002c002c070745854420170552030607419001d8440e50240e1480d10014030f0402c24150b0099000c4a01a00c0d071001e480c090f0090720440291941104000c0b5a000d0101c0141c2c0080712043d21940310180031901a030203640d20303140b045a01500c40d600060100700c1105801005241ca61a188182d5211285102e000c07400e540c800d864400000c2ca1106090100c2e1074500100307120301044600800c0a0f894903c041a0407614042c042e00410790f4a01280d001d010381442207141c203900040c1900c440c1c010070300c0e00c00000c0d00014070b001075540c0c400f00d012802d400c04e48900c01280000415003180c1c2407800c16084060a08400111483e80800c1e01e00c07044441d0303000540c8820030080d00e5a10036546040c81c020610050705e0f0406200341e8414041c820984d0704a03100b2600301140c800400e942080000e800c1d8060326514482d009558110420f00000c003c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 485760260 1250 485759010 485759017
    0x711010c02060609061f110c0a0306060f0b1201060c02011205040308070e0f090c0313200411180f010201021e071103060712022208010e0d03050c040303050309010b0d0503 75
    0x4040380c4039105605c80d5030501c116444020308143e0084000c0746550750b03482c011a20200c1a410080880d2180200280401d00341c070111b90044130130301d80765001805558452003011024060100d065800d146206044000031130040c800c9c881130080140160701513921604800c00c000900b40d5040c44142480d00d8000c214280803501e0000003114101ca010381d618004402012400005004101507114801e64070039941c0050592040740c1aa8003052001070502c0807200c4015400b52640c00704451104c05020548000c6100214611001c2042076040c000100030b003000c414041c0c030b0755000c0607200c000503402072240c114200c18003100e452811102c00d498500501c00e43e4443c00d6080e000030b00c103c06240d503800d0103a900b000825480d00492816030341940c00351040c090584101c681041440302c0410981042d500025050303519604d4101c03440b203081100c5600c643d207500e002c218515021b0041291801940001400c001c000004202c0d4403009400061240c280103002c40051001c0c0d01e8155525407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 485761510 1250 485760260 485760271
    0x9091609060e0303041e0302180108060906011a07031403100801060803090d200d0f030f08151005090307120510090c0504110c0109060507030b061c02030711010c0206 73
    0x104403103808509079115981c040c2404401800440c01c3c58100610341b611804c15886401d00780640c0040007016a0700c45a043c45140d01903030040c81e071541000d042e2130800000410101c2c1c203901c484010454001c2c44080749507645d0034080044e403180000e00e411581d50801510b803081c42d0300003100380f0240c0d449032942c0d041105e00b100020019940c0c0e8000c010f03224001e0304c1d0040d5001c0003e1030820003203126542d0b000c40300c0d408010700d014032140d030800050b58030b1003a00c41230358440d580d00a050109900080e43c00703c580b140e03092204441c030301403100c100302003144100360f809042044e840034140ca00030800ea605c541801000d03961242d844032000380c01c00d00a01d00c03d0f00d03180305100c030041c440368051203080302a81c1c0003a030265101d4100800c1c0005130030880c1600039101d0040180d2404110700707100c0c1001281c801d41010800d41884c21000742038032010311500d441048204542a0841c0340a503203d074440020860140c0c50b96a501c2054035030140018040010b542400f088051041d40450a2803244 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 485762760 1250 485761510 485761517
    0x60d0c06080610110304061b0b0106050a03060b1204030e010c05060408071a070203070206070f0818270f1b0c03070b0a02160b0a020412080904050f04030207030611090916 75
    0x240d83c01c80c412100c4c10004601c1100d281c00411041c08601d00ca070503c0c4100d0000885403260018042c0e4400250300001d0307108400154012030400841503240c010200107240c003140090a00f845100f0b201005003004c3c0005080c0408140c5c4a680c903405801780070801074001e400d440301d0b45032500300b840e141d9015480c2103503203003034a014031000400070ba00c110703001d40304d07581c005e5040c186c9507400e06c0f405502004c1c0030b5502612480d1804002404000100703104911032254805181228040c01802c607181d040c02c10050000306650390914400c980c480764843c0c0f51055880c1c01d42c49403400c0d03400ca00c400811300b00c0e0080e8006401c11003440000002c1c4804c5205042c2c10300c00d680e4800201f0102e00800802140440c2564100b0000c101050f88030707a081103c804005281c10390300c51a592402d5040c0a0880b10350310302041140e00d901c1d01c2e214a0ba0b12441d500c2c1001858a81a50004e4444805010090186560380c0c034045070941c401050394405440030382612254186a101c0901d40d031062440340000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 485764010 1250 485762760 485762779
    0x40f0605030f0a052803080a14091f06060c020913051c0f08010b0909090f060a0605040b03010b0f06030c0d0213080c1504150c080a03141003020604030605060d0c060806 74
    0x71040300303000c1a404180f413140b241e11985c83d04d9800b11140c00300942201c0c1c1403900c4020044040c049580014020b041d141c00811481e0b079055048110150750404407640740f898507030200802c81c1c200301c6e580c4200d44d04071215003a035611403620f1007a992107050068803034420350402d0a40540a8002e58201c0881a200c001070b032040d211044405036024016041e102c5000c2c07014030041c0c00c00c404060b400043c1c2e41c1c191100c491030708609a02d4050102c0b0044000303512035204001d14201442901c1c5000400c1d402804402d8914010446549121502d140101c07800000102c020f0307404800d4541c42c00e000c1c44150354800e91144400a26090f0340583c0c041c50181e00081a11840d00c410743e131001c1606024150305040c07030021421780c1800d060b440708090000180003600000e80f180d0081281100039140011903c0380c4000700a60b040c0c004140c1001041410414400350b03980009503070480303a02c0f010108080d40d50360042801c408144800420748644428040350941d0004010b034072034207054660000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 485765260 1250 485764010 485764033
    0x90309080601050d03260f0a1103060f01140f030708061809102f0a0908030a120506041404051c05090108060d0f050a0b0907060302070809040f0605030f0a05 69
    0x44541d001e2003a00e03406002c8102120009004604032800880340300328034240900c00640303ca1210303100b00ca0840f80241454100500314051f0301c20425014840301800f81145814000725445105032580917041c48440070030402c40e050280101c4a48403150992562071b400c1030ba2001c0c1103a40282d4115200e5501e004461066804403111544280043c1d001000b0030f0801c05404c4009011440400880d08030401e8620741040075101d032040340c1c54403090919541d070002c8400810100d110307004104960020026901e410b5448207891840b0a40044000b5094658100103070042c42c0c1d14403800038060b05001040b061040101c0e51590043c4a01c04a80c4900030a1000b00d440e8425546400d01180d003010203e40d9505101e41c0300c040013842036074541d012460740e8458601c2c01800300c3c41124501e03200e004004010340144916030080425007019030500c41a46e41c0c9241500980131b80c0c90145603241d0305003d02c210b05030890001000d01500350380c1c2d04514902299240c03841200b06a2321442000720400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 485766510 1250 485765260 485765263
    0x1020703021506030303150a0f030809180903030703020c010b041b1707092106020c0d020c030604030503160309170c16081e0c040c202a03190609030908 67
    0xa200f880002e01840c59596015400103148640c114000e81200050801040b043c2444a14074060350042c0f10141d155030100003004001c100c0d04041e050b0341c004080510002d10000029613821290360b0070b02503150070941000d1401010f0780e43d681c0e9401402c02c0c034400c0c07204c0410003141749c024070309035140000d4040501c420801240e05940880c00505280c80400041c5030503082c03c0054008000341001410701c2e03031903000c260703003225505c42ea0301d0b0000e03844a101c03207030100a8511140b00642c0980b11a02e01902c016095001c001c200004c02d014071610141090300ca5071001c10f02c10782c802060842c5503503032143d4206941044030107230200c1c030030b45491010001030035504004880628008141c101c00c0581c51142c0c21400c1031440c81288154580c3c0f90059903180100c0c22a0700169594281c9181000d480da500e08001c25202c0010f0b401c60105201da80c400d407030300d00a4030f4440c0a01201c42002c031a001c68a060381800c002e1100203410b43d5580200841d0b43c20811000340281c0d50075615036250000d05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 485767760 1250 485766510 485766553
    0x103021f02030a05070303060e01030305340605041a0903040602070801050103080a03090519050604020901152f0f15180706030522110310020405240403140102070302 73
    0x10300503a01c1440b41d601402c1c0705100034000036110307180104170260303038a1441c03468038805e0304103c01040020610300b804000380c0f80d48019801c060844050244520116030081120880019221640b01e0000505200c4807000b60340e40007141503150016850305580c80b540f00d4016010320401030080d0100041c86460500406050701e4000070362a14007901100c09034024140d481c400c41e001c1c058a224100b400c0c070f8003420642030794001e2004d00010715244c030420a041c2016005880e4400083c4100d40320254000f00441035819010044000800012007c8403102c18402c0070403130a20900c188114000f0b00030440540c158a05828880c1c1500c07516420300180d50a114150055804400f0030045c0b40e00c03d800c80c030780001d02d060420205c5042d10072103407243d0b04241400c6c4c41030b81041100348201d040401124007600390200b4218281803c240003c1c0078400c6680031501100c05c0c0d410140d61400380c1d00101c0c1d00940e40150034030444050032000354080d40000382c01350054000d80c2c03155484242c0c9000711 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 485769010 1250 485767760 485767819
    0x90c03100507090515071509210201020d0e070f0b04181107060903030507171902070501140115080c040f0b0c010605031617010c05090108070302130b03010302 70
    0x50410010000203450041070020007000c1000120200082d20b40c48100f4080039000444100079920b07400c80c1080c000c04400314141098080c50082c110000c900c44e920f031600c505001c03e543c0c807131904042c10300720f000e80078103400d1401d0a8581182402c2c2020009010401c8500c030150b0b199083d0303074940104601c0e003d1b81c0f0408004241505010b003a072051503000001301100343d48228100045602c900f001c455580b041100801d03030725030a003e22640c2000c00c0315134000b11038174a0046890860f44d1089901d40c8050049031081c1c000c40d00c03030204070086d000f03424070307d400101490030f43da9141c80712024103400607000e05c04148114040b80321190b046003101c042d200328421034190ac915007007422426170310400044d000c0e55680e030404226590b080c043e8101408843c60441121030405070803042d21352525049113031503803400c1d5031030542e5504103042e500340f06030909000c04690b440401c02d80c00b074840c00341001c84201081c1e4000ca01206070101460580f802510410740404d1441c45d04251210f0355440c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 485770260 1250 485769010 485769013
    0x15030b040e030c150a091a091903050a210203091c030e1902060d1d07301401090b15060307090e060a170a02040e031e0f0c030c0c0405090c03 62
    0x810b02203401030507135422502050700019400314540303400d541c07445c001984903a00030342c000510104520400c8140b241c02828001c1611036030301540c015015210310206030092000e43e00c4030b20010403041603030380100e403541102507641c0e1400136000f64880008030456208440804000303007207140300740f0403103024807400b07001402c1c00304030b020f52000d800681c07000c00c030303070003002000039080c6007000b13000385500780b05001c10307030034208840c03200090624202e60000784e500c0d0801c1019100a8801c00704031100402c600703000550081c980c2c103104841d60000c8400500540c02c084142c01001240d4220510640302e440011441c909410200100f500c402d60b80b440002d00c02c29001c0c8001509154020f801010040181045a0f50381a07128081d043d440e8a4403801c1c0c1042001006600380760013042c100300080030246140c40425030203200d15000096040003095000300354040d41028074002c82d555810140100e07070b1a01ea480d02050365900d00d031011207000c0c0341004042140f0b44070001c0c400300e00010060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 485771510 1250 485770260 485770273
    0x3060b01030623060306061c0501050a050f010c0b1b040b0304050601240f120903110c040606090b0306010c020a081b0301110d0b0f33040f050d060615030b040e030c 72
    0x820131485070030103415181c0c484820080d070498441598414030000744d0396071001c01ca540c5407030200b00300d0b140960300080c080d440030724406640d60f030b00c4000078641c1c2c0da01080c0440181c58001c0140030207480442094038200001902141001c00400507620840c8a542194250b82e2124115040840380e2224940d821909000d201006801415035142850071842c008545000145000c010f64030301d20820740100380088580c6095680621001d030b5041010fa0b41800040c0c6410002051410103104001d20340740c0120100d40d883e84100502c1c1d01c01500208091110381d103401e0030989035034080e254020200724216003c1058141030040f0501f088807520103074101440441e508010f4044000c1c025030215104403088902da948101481800790b4070030740303810101443e001c80d1000213000f8100c0c00b90090240400c2000c2131110342480207490007a644012501e6003031400c07501034000d54100c1503e074000300d0103071850780343d041d031092102480c2140c040c003000c140e507814031ba10b03482401c8209ca000c1d040785 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 485772760 1250 485771510 485771579
    0xf0f0b0a031a220605060c0606090c07050105040602031f03020609010f0c0203010204090606080f010e04031110110c0d031e110705010e16060e1f09080703060b010306 73
    0x2540701d01c0850714180c150b0103616070318a00150080103d441c3c1001d005607056080409081c56108035030203801c0c00e807412450b00300800b508641d05d00d40107106c00c1c80b94a002002820402501081ea10801d90010003070100707042c54a807501c00b81d08102da200d0b1020044003041d10340242d800d451442106d4001d4100391034080c440c4011140a082e40c42035105100310005100c0c0140c4003480104000c0400d80070001c0c15504140c0018583d0f0005030081f0706421103100140b026060680d4016005541421301e08100c0070b01c1c0414605140790480400212868100f41581c074a171920024160201400c05441c640c8021030416411580e0100c080e03403010030f0300203068464a0441c0d20140d0080c412800c894100b540359600c050a6130920700e490081d5801103040c2040403980c031040d043c0585003d003408030208110102240d110400c071240c0e4080702519458110495008003411000b4111250690b0f02154490903c100945100e4083c42d00091604500003010100c602445e081040ca80d1039402050740e00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 485774010 1250 485772760 485772767
    0x231030611040b0c0604030e180f060d05030d050708100806130203070e040606050a050f130b06090a030305120a020a0813060609020403060e010b03280f05030708040f0f0b0a 76
    0x164181c0344440c010403010900da03500a0151140b8482c0100403c0303286020300d0020100003230821001d02030b4404990014455045c211480e501500b042c07031400c0c0c3c50b0b0b60300d8001003501640300c1c0d01034410f02002903d26007510305904194442c0ca060380703030150f50791902d15580c0540c20303182c0300744105500040f01081d03c14a2102d80c508109000408a4800da6210b40b124100c5440c19901195241d543d50000c004908003c1d60303400c005c08088482145041459000c1910400009620011a40c4e290240c06032603a602c015120500c10241c403604c81647c4030307d0b020340f503a406030038851b5400481d94000340c020031440c002c0300d0316400300342d4944030b454032034001042068404503400c542c001c0d2201404508030550744050001180070b010089540d1840310004da085503280c03400f0134060340107101c0e0701521200c044102503210070f201030404103400c15410102034003e01218000c14034040006c200c41800340741000b50060351140007054250980c0d0324883c21007071a8070310031440380341740a0040000c040d02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 485775260 1250 485774010 485774021
    0xf15021b100815100f02010e010c08060105090103110d0f050c0a17090f03030a05010302190537030b240a030204090303020c0a03020d0f1403010b071e0602310306 71
    0x5a03800f0380940440a00c0001c0e99a020740480031000030301c0803003210030f020350900600d24000318000003000241ea010354010308042006090b84d0600072700080018051744a541706081a258a4000b244c45843c481c0741c040c0500b60042d0040032003420040443d2012039281c0469400200365101c518a90400c0c0340c0b520041c400c02400e0402d02e01622481c414600418801140b042040a40003d1349604610400c00030b4112280e000301d0342a0000c0c41030250380c807142444241802c41d001204a00340303403140c520190512000d4220708112078200c0c0082040701c240c02040c0600d011883c0310002c16080222841480d03400c1d000d40d82e00440050b01000035040c180d00142003503020785005443e00c0e40407402c4500d444c03030200d4110010b9011072261039003103601090b0000c2c107046d1481c5c907000103822000c03103040d940418000c601d526040012085c08207c00c0302c074481d080c5500e10070084102c541d90b0038108001d4000001807100c4c80a216650b0500c400c00004410404c1021488400603c0c25911284e000f0003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 485776510 1250 485775260 485775271
    0xa090b1e0d0f0302160b070b0f1302040612210210090c0302090405070612020c1c020a1707060c08040201081311030a2402091c06060f15021b1008 64
    0x280480103031000b107402c80c1e14940e140c5001c0e4008000d640e244107903000458015500c8512039041c1070004200054401c1e0041c0d0b04114500c2c13921506031220040080c00e05402c490003544036161840c00611058800d05000005006040082442590700d031852010601101e0031070041e0400d003940c6030b0804480c1c0c00000c64070b010710000880d281d02d80d40032a030b02d0403080c1e5054a842c0e2009104000d041d50081070b41100ca602d000701507080013004ec3c0450380c0d5100c10300990750710044802050440502c02c200095035180c1149903516030380340380d81b409030f1594045407050301c00d1030030142007549040c069103000c0c4c043c075410383d02c0c2401c1d40d0340c606115100f210709600840f000c1300c554040f607001744d41c100300c60040e080c0940c14014520410b81c02c1c0400c0d1840054803071113840d00600c80c0704456a5036180420180d40745400c8010f40300d50514020740103003803680146d90480529200410700d0500c3d0440d01c20107048a4084410200074014004111081000541c4d400b205101030340404034802c401454010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 485777760 1250 485776510 485776519
    0x1203010308032205011a1009060819060b07120207030b07110f070801151a0f0708091011010c0c170a030204081b03070e07200c15090a090b1e 62
    0x80110680a2003c610407000c01d039010380d19820511040c200e80e0050901e441360850b46030351803140d410b030090880100c1e0320032070043c4411080000c0c03000d402c1c0103001854011301c18040140e280c41d0005842660441343c0b0556551404030712400741d0300d000168000a0301c1d0042403150b11581e0307a9500b1110408203a5a0103c41e010700006601c0412082101784003602c01c1c4070010815103030560300d01f1030b0f103e525400b0101c0d40c01c0c45d04c011209200c6803c101d950030b02240c3e4030580d44183c00d0078103c0c03192041d40d03850380d0002881d24540d0412944022211740700000400244801d200d100c02c00c4810310600356000e05103000d03140400c50a03492086c000c0c0214200f0f0b08016042640d0303020414106802c00d4242240023070810100f40040c0340c00e103c0e6402412084080082c42d0401204c01040e40d242e020411030032029450b440e5030304035001c00c42c41e000c40e50020039102000c09040d12800664001c41602c40c010344a07140082a044414010000358000c050712118a07446541c48050314060b202c1c5031103412 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 485779010 1250 485777760 485777791
    0x33090304141507061a041401180b0118060f0305090c100f110102030a150608041203050601090e090d020f0c130b0f09090d020c0d02011b0c0914060a08120301030803 72
    0x9004d405031826034a50071400c4c8440441d00410300c02650b20940040c4540155030380140807225182ca000049070304400e01c002503c500860040e1007002002c1003423111002d1070b40000030090741c400800c040c4145180d8050003151541c2d00b0183d9504a0034101d907510071603c88085101900c212401100210310741f41c1a0b810596840c0d090b403c992091390540241ca4841d40c890b00b40c44440f2906100400c000e1070300701311500e001e8a40b1080c0030182542e0300708242d202d1021416a138440c5a681010300400350319100700b4113102c0b041036a608002c42003440503000756010300e40b44a02c041000c5001d01405010081d130b12005082c110010080104402d521041080391105582c44411500d4170820814004103070301810210b01a1821041140c0c040c4542000e000c00c2d40140d0340840c10709103010f100c404200d260f2034145448035441906070000a6803514111020142c0d01d54500124081c480a0b1180c4030781c01d8690601d03d40310032100b02080c00310070007040100300080d054401107500038030b40888101d6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 485780260 1250 485779010 485779013
    0x50a0f0203150904023f0a0f0b04021302040b0a030605010f020c0d060e060c07060e030a051b0f120a090806040203030a050a050c120301060e010804210233090304141507 74
    0x540f200c0f40f0040c6c028805000280c0c1000c0345110360b0780d182076400003400410460781d1400d50040000c9001040440448081011525503144101c0e4200940b8002e5484030b44484960085030040310400001904194001030254000c020b546a1030035164040c0161100c6601844944801500d08841c0a540d425180c0c124400502c200c5018010300d80c1c401c0d035101d1143c20b014096480c8607103403442c160400c115444101350044100c903940803040d041d026914a00c1da00e00b03810400f400541a046004850341010f060760b100004082001e05a00c0782c21040d40c8a056040c1d03542011500250164010000310f80340ae40100302a00d2038021a18000e407070720101d403038407505181c60852002d20340340c00400144071040c0c20407400102d69801707113000300a9140548070190303101c88440400c242c8003400d480c0c0c2d02d000d40c400d01c01c012031030000b11443e664407a03a00440882080c50301e80b42d200e140d5004030114181c58404400c407400c544108440505051402080004080a85405903100401084070f1030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 485781510 1250 485780260 485780299
    0x170703061a15040f0314030702040903230313112101050a18050c042408060103020117072703050a0b0a0b0409081204030c050709050a0f020315090402 66
    0xe00d00766200141034060700005060040c10344881c8100c00801c5818031080c010700c0041245070b4210b03500486d071079503201d03d00e015a50443c4100138000c0d40080c109072400d4181904031803003031440d1800700001210400d0a00c080c004501003552070f00064034800800701c0c01304d0f803101c01600c00032800400000b05500d4808012281d213040c2d04024031a40d445108001c0700700701c40c2c4601d070406648281d42000030b0406030345182c1c50380443c0210038801e590300d4000c2ca4601c103400c0d074040c01003044405503010250320b41c00101e64540017440300702d001070220015402c0e5010703030443d9103005604d01d48034801014107006800c6020300b1280d5845201d01060034002010480030000741800c1030003005051101d003402e01c4400706840c404001c2c0c5009504001c106000900d51908030b0380d00224180003e0407544451500700c03209546508060001c1c86510b0020442c42015800b0318090700c114030003044059501809071082c4d00044407200000c01d6019080310550400c0e80d80aa8070a100900d803024404000401c075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 485782760 1250 485781510 485781521
    0x30405240c010b010e01030902030604060c02030d0c030f050601090e0103060216080a0305240303040b0306040605060f0d05060406050a06030e28050c030a110d03020a020619031b0917070306 83
    0x5030403582d103611480f85196040380c3c2880d034140d000e10f01803010041d583c0109607601d90280008103110350ba50a2014443d1003801656490f00092209100180c020302c0c0040c0a0b103140868011400e01d0500403544030b41c052008001190407186d5407210340e82c41c68454000a4104503031140350040002008030010300804002d094030461514009081c1c2481c0000c11075460360200150b19901340182c5510709641c001082d20304943c54130712029035030354400000c9005010701c0c0e40320541046001c180144008080380250420700c40400c1c0c200001ea45001c104025940070b4850150440c0c1078407400d0018034400c2e00001290b624500c01c9a500540070211545030401c0c403043c49494074049506502044801d0046d860300c218110000c0450704035a4644140101281c05514403c1154441010030140280003802540e0380080200e5265441c01c51040c0c03035070706690b214200080c40d16400004441c01c20032140c4242290369181100b0328184070410214100c10742982000f840785500000c005009070158 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 485784010 1250 485782760 485782777
    0x405150d02090d081c060501020606121c230315151b070f3c0b0f0406030c0c0f06021c02030103060b091e19020d0f0615020f03040524 59
    0x220390b45c510044030120291880c15408592282c1410401c00850383d000a1658012100b1100c0036080600b50101a18103e501c040e4041310012080d245035a094010f204a2185013041148000c1c3d2036112801400901c0100c0380340c561504845c0070440241030284186001240c9a40440e24090080070840004d04000744840d145500400090088450b03d031a0343c4010b060884114040b11200e0020107011203d24018079030040010100079070842018580c40e0042000e10072256031400d0500f036001880d80540600c101080c200002410100c0c4650f800c602e003690030800c1e42c4031400e42ca41c2c03500c011b54462160024031852101018041d00e04910056001b03501c03039040002c15a60000074001c40a0004101c048000d13017041070628289499081a42d20129915840d2460b6107000c5049000380221a141c054140c503000303d000d005072140d07000c0c1c800d8a071071042490800500810403603886d4180b40320a68079402c04d1204100e20b00b400c11038000088001269900d426052001310300d06500300c400b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 485785260 1250 485784010 485784023
    0x9061b0f031e0216060b0d020109120c0b0a0f0e15030406051008070611100509030406030203062d0307051e040f091208100e060a06080915010b040302150405150d02090d 74
    0x21030404004680c03241a4106e007050310051a080c0d00e40e000a4140c4c1090b202d4409018008240e21041013611021100582440100300e030f01c0c0e00310010000c18900c032618840c03000c20300810686010b8500600e0040f0014a00c01e415495503645503140d001138000070b082c100e1100802d020101c1d070501e040c00240094000c95840c1c0110031540042c03103203813140803401c0802191401090200045d408012541511a075040250b52915208007003500c3c001980004417041c0e04040a4108082070a106044610001c500702d078151034580c1c003040844501d040341c1c0b81c04038850f03281c40405810141c1084041c00d621200c001549a4191200d5001849201f11140062840f80c01c010380700201c85108805041d688500da005890a40080b92120074039005079400e200a01c030004101d01020400303841c040b42080d0710301e45196501c0d55500d420b50800c1c00220321031503100f0040e0010200c10400d8074229440140000302e41401242ca0f043c40c0d60103e1000c3c030394184c01300883d20080d00c490805090080c070480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 485786510 1250 485785260 485785297
    0xc091801080d1806090e07090506030a060510110d03150b0d020a020d03060b030415150f230d17040801060b0306150702131a030601030609061b0f031e02 67
    0x750b00030024403054008000c07004901c0000d0042542c012002c0b025220780154500c040e49840d08151000d482a0f4800350740000700204000b0000c030141c000d41d00300c400540306142103000540050b144140c2d125082c8a00d0f60015505845482c82a0024180d490084140008175a00c4440a120030b074405001021243d400003901c3c0011941000040e65114030f616081200340d080102d100c246210250000d412542040380101c071503082580079440c10b008001040585950b00c6d070040d00e032900d0500c5142540c04008800c81080e82d00c4200c04122802c0080c03e02e00d01a6080d03440d60b4000e4040504083c00380401d20022840110912504010f40f60154040c0d48901e804410055150704140c0d0540111405001000050b202c0640c6d0b0700b003091201130042110380e61aa80100e0f2540e81d02c03101a0703d4403a81d80000180403260f4440b0700d42c030340201c2c0c0901c850741c0d81c184801c0b070700643c154228001030315141011140c14400d070301025020620791b1b0180caa90b03550000b03100c185d0f00122406c07a09001d903007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 485787760 1250 485786510 485786533
    0x2424030c170303040314160507090612050a0b1305030a020114130b061003020d14060a24120204050a0b0d0501060201050903070206090307050307032102010b090c09180108 75
    0x200da00c020706010040800140700d03007040a4890101800042c180260744030800350750010042620782960201c124111880401d05007a03503285a42d2141c410b01d01e20b01000420305881496440c0409070308180180700d23100c0300c0d645680015400905a2030301c000301070310110006400340002c10344500703a9400400d0041d85148048501d100180900d440346540302072600c00540b442c0400b50f8050801c5542e00c802c20b80d0610242c029228200000c1921442c3c0f5880d5050001030054007406140300340c4115001e02e0f120f202e50700c1c6490b010348244400c0b5075507100d40d8900354821211482c10700d80561015041564450114681c004a900200700a45010480c04a001802d00ca4503005060510090016003440300c0102d881340704104000c0c0c010b560005107808951810040d40c0014039002d011281425564105980f00420340301c450711542a0481e500c10b0800c1c0b050142840140c0c0003007001c0e00ba61150b20348210558403402c00b440d00000d2020110344420507a0040360700801c44e40d005405036900b81d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 485789010 1250 485787760 485787773
    0x4050c03090c030307020d1217070302040825030f03030b04060b09010806030115060e1809010e1504080f07061401090e070503070b040603021c0e0102130909242403 72
    0x2012190003136100384851070241c0d40c1c0c403180070040c40e0041c00b29542e0310b80c1c0740c2c4100c5038200c0754240b07407942c0c484017801d0041c0540e0680c004c0c400c07500b4090548075105400c10b00042c02d2502026918010b01114a06101050050319401c2030b09109060001e581441b040c003290030350340f465200005060f00820b0980c010b58000240642c004400c03002000303002800c0d000c0c0c60b400c072024014003040100c5800306494503150001070000c01c890304c00408105d442c0c0201900d0103003d1343c40309908117020306003929040424000f5600d0040380c0c0419254206406100d900415030040d4000785c030020f4907400c02c807102e0302d0301644050103000d41d5540400c0030322880201c1c80c50f001d50350340440c0c040d84c00030200700203082500040d201a18000d140169407415001c0d80300002d42e5002c04c2450f0303c5480d01d4031550302e4280c1503005040a080200d0b42d40d00003a902d08012003198002100038108202e0071281c1441001d1101190000ca4030302a40040c40d4401007240088003140558950252036240d034082c801d104c031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 485790260 1250 485789010 485789023
    0x2808150402010909140c160b0f010618150305060105040b03040c030204050c0408031b0c120c0a0e01241e0804020405090a350304061d01110414040b04050c0309 70
    0x420318030500a03002000783c1180310b010010807840e82482c0101f850302d0b454460f4030329420560340020b042c00090414840b9000382207428401d82c0003103802c0c070442c5040e94403280042c004640c480e40d01ca1420703440603a015006444001c1c010390400c0310400c408141c054803080614000ea0040c102f40c520241188140801c403100900300806030f40c0180002c22150700000112a1201c4044601009034410121a5490400d6002041c0e5004002d0445020205000590755100c02022101001ca06940d98a20142041d0030b0145e0640c881e9109940c00340c0200081540786030581c90324146150a81503a428408184521840c900098a00e42400190f1400c0d0243d03540040045001d8422031285503910748a20710300022080001c400308088400b1802e04504200544840542440d5285850328090005050780e44003060200002900c40300603140c14030a007003009002e5080c56160606050103c1141b0303604a115603801754a40c98601155243c9014450144950b900344a4480c20045003a604006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 485791366 1106 485790260 485790269
    0x9010605070519031d0d0c080726060414070807030605090607020106050a0902183307230a0b04050d0e0f28081504020109 54
    0x15040001490381d14410b50036550640090641c0d500c900e5406140500041d0041c2c0c28041880140f40300c03020100710040c19400d44181994503440200201e07040042150000c0c1d1080042c44c0d43c0a0359003901c445221108a201c2c0076040e42a6960003000b40043c0a400c60081030400c88401441000b0203020008107841001c0e4903414660701a04042d07500d00b915105140000d203095206100394401e036000204452401880c102c01700000e500020103105000c0041c0d940e00b5429541c8104d60794080c410092607030440c0072104002c03180c028600c1c0c44e00200440401582e00060001440d10700c03450b9040e00000c1002c020b010507145403280e1641c005180303c0c034000038401440303400210278074004855503480740c02d0201c070310070f00601e84092200f1039048525940c01c80341010118500c45108040c03807903500003166841c80e10b280b40c08036651220308a910b9180601c070035540c0c05002d040180 = true := by decide +kernel

theorem cover : BRFrame.Cov 485611510 485791366 := by
  have h0 := BRFrame.cov_init 485611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 485611510 ≤ n) (h2 : n < 485791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
