-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3031
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:27:48.42531+00:00
-- url     : https://prove2.me/submissions/b5f752cf-5c73-4c9c-b31d-b395d39688be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 544964028 ≤ n < 545143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 544965278 1250 544964028 544964033
    0x6141903030c0602181009032d0f02121006031a01030816031107030c0e1503030d020d090209040b10061d040513061409060601030c0e06030a0b0a06030b09060409 71
    0x2c940205055100c0c0000d0f03519808440590302c0c2c01c54584030140d00064170350400104e2170b04890101c044034031614061103014010140003000443e00301401685215079804e0b030000400340b40e14012884c2c4003e100c0e00083e0400d5048914200891034040102661050244203014001852800c200c0d02c0e4901c01800350f05583d1000c41500031640044502a440d40d031000400d4043d03200200800700307050480d40425501d0034060501c1c800c921541070f511100070b001c18040060b8042118040f60042d005501d4500c030b0103100002035000c0d40300400344642d07680c290001a603030a60358a0180e40684002c60356810600d41c503c20112803988001d0521561221034100280860801102070504440c001a1691010442c3d880348404050081940303161001c68030401542400b200d0052000d1001c44001d40d03100001503040303c0c51002e00c24040342c1041c181e117415141800003507600012680001c40c031070710304e000071035003031001a00300e10042520740c1e030017038014103144202d01d41c885001c840a101071441074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 544966528 1250 544965278 544965287
    0x612020a0b0903010b060a020a150b03030306010f120c120509150a0902030a05010f0903090e06010203040b0a03180b19150603090f200a05010804170c100614190303 72
    0x5204500c0c40e26000319038422580c3d029070140d9240c103000351206035900c1030b904000303440e0583d20a044542c00d580006524444086119170a0000f4004d0001c500e95101d0a0040d40da405090319000100a50746c502610303d00500c0c00744210305001030300c0305240c1c1d00c002c905100640300c000305502541c2d4058001d00b0b09039802c810b040d03a0000304855001441d0b40d20382c004281459075022700500f0940c2085072244200001d54040103505002c4e54030b4034842d80e20380c0181806d0b5981910060300580c4144001d01c03060429000424501410342000141c021040c0007000c81c182c07110034207030380007600c2c0c0b01080380c2484110003140f40d4183c05242005a10042041400148298018842007541e9140c3c007004102071800035200b02500044900b4420f40f0440c0462008219405090302880400d6070006180d4080c00b0481e000310350201c4c050911001c150084450f0340c0240782c8910140c803a090041e0b50000140c85900040e103c1010625030724000101844444030381031810501e0240550f40810100368032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 544967778 1250 544966528 544966549
    0x3020a0b1f091d011805060c0301030308041e150f060b090612100e01090e071a0306041505060f090f01091d0408040306110a140a1b02060408060903030406061202 71
    0x100c2c080020400044045060700007102d030701c82e180d50761a00c1c8016092100d0784c101d4402c10f0b4841d0046811030b980341716903004140400c0c031008002c078250030080303800a5100d900030134500c14200f1f0000442c26954072600c0c0c2194010590059081e0784503801d04146450f405043e024240c0040c03814a020b80e08008a60306120f0700081948110882000c10483c00030f07100c1d1080203040c1108059502d50310381305080000c2400302c031444420310883d640001c04104100e072904000842120850455035002e05000140c010320f040e60100e10507000012540f5640d460290000a84280b21103171200311003424800c00801c0d02032842d0612280110800401c41c0e10040011075003003549144855413214601900b0f54011a00b00800c60750038081180b81c600d510201a0260540355510004000155444032025204086030580091450b42e01c030341c0806908038415004c0740c4046c1c245807138142d42e000c40e81e05010b4181e905002d150000800d02092101c00d00622000c0c100610b41d10380d501850354000742c51003a9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 544969028 1250 544967778 544967789
    0x1020703140309030715020127080703030e100b030105090a080f0a0903080a030c030f050415020c030d090606150518090901090209010e0703061d0402040b0d0f03020a0b1f 75
    0x603503161240e107414090040e075403460350190882d0501a150b090300c0b001d41d076202801710010740c070344680405580d6503402e51910356011041c0f8180b81c0480740c1c1b9500016400110160b0a0503140d03c4c4405800804001d0150803100c502e0001031181e52040030103003918400f0305140c4041d84100022004034108800702c1d60103142d200e034601c1e41e5404100003178802d410b03d5807000e04a000c4c04102000800c1c0c26030003414100220b42d80030072100641c0c114100444100f6180540700c0d04c083e80000001581560090002c0d044142c100c81c181404050504181c5005c1c80080342c0c11900c44004121500c1c1800304402007505a080060901d0201c03803210502c5004800034030b120380c25007000306402200030340c4440030264014040c3c203200c1d0303101c00e010220381005540e11400030b881c0000015100801f10280040207102210380803807601c480c0c08210142900c1c82809034480e4902ca1000000b41a4500380c00c0180e11a030042c010325542d500f8150b680e4039004140b41210201038176404198414001c2d86801d844 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 544970278 1250 544969028 544969043
    0x105010812070302071e09060602030c071710020313030215070509041a0301230c070206070b040303021204031115090a0b1026012f030603011506080405070806010501020703 76
    0x1001c0e0504a1905071103511003846154011b2008050a06451b4401c080d26001071090010a03918034042b42d51307118480c80e01e03040b03400001d800e01004a20218400c0171540d0502155490741401c010007089034000c3d12048078400b1400d42500070940c0600200c3c0111824180008140c601039070050078610403104402c3c819551107131a051a00b110121039580c400000e0020000414140c0b11881f600d80040c0080071044240b00010b043c844400c2b0403200d865902400d8a41030145c180d4130010503000c090401c4080c50340a021400302011044034051207240203a4460510180c540d9005c0c0c14684154580c07000d50311200100000b160b0002054011683d0160090f00580d41d184248800f5051580000003607148030610f107051610240c11409624012100800880d4202210790360000c601015840180e505100542070b2a032214000c0c5900240c00780021800c2d03085404a0803003030645070030010115107030f01d0070301061107410000c2c00042d100d002d004200365418040040d65491140c0300041c5401c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 544971528 1250 544970278 544970287
    0x406170c310f020c0114011e0605030907080a0803011401080103020d030e01030f060f080708010e151504060b0307030509010606052502041503120f050d0218031e0d020105010812 78
    0x30720059020300340c240e00340b0300119200e07202500d4060103820382100d00c0100c40d10200020810800c4049404104515602132146091600c2400e8980d504020980700c2d09014151000421150502c0794105280c841c0d448213a4a60401c00c0b2404100020300c0e2080c104000302006000580300c182c43c102d0300c142c26041103502c00345184012030141c03078041400d19619081c040c001504544c00c00c02a000d80f1060010790310182d0b15620070508940d0680884041c681c814078003a0074240304040c8440e0002c005009130500b1402d414042030070f841e07860f4081c44203a840001085a800c2e450311a090b00004000002e1020510b410402041030080324400692000200d000461124200c840e1000e41ea9003d007045c031003526640c1c44221403410911007074030fa9010300c88818000c280b18840c11106518035403a10750038406400030301c400a41140520b14551000d4040c00102984c00300030b50b6a0640050306d000b0801000403603880d00304180c5140d082d0540e81800d0061041c1e00300880c001040e02480c943d11501e5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 544972778 1250 544971528 544971619
    0x8090307170d0b0a0b0c1203040210031509091208070c020f130b0406030c41041e0b0f19030b060a0e04030201052502150903090406170c 60
    0x90000f541e040b43d104200300c90003e000c0034a20041c10084812006595179001400c0311640c107440304850003907011003a0b00c9a02503c0d40254824644a801d0091034807030b440e19114001c0031966000c0082e40c01c0d544108591101c243c0c80001c0d207621542c0d9103407143d0995035941c0803941b0301c1a1031000c10700c5440001c4c510794404082e070380054520a0024000e00800340e40303007400c030031700c074658022220481049800c0e0100d445e83c3c1e210380c1603c0b440440c00440080f40c0407059100704811070003015445034950583c0c00c0c0500b0283c268180f807d2425200084071075200d01000244d00542050901640055540300441041034454100f01da42200300c8084550310b400015091b50344640101007443c2c03848080c00207045d8158026845100d84010340c4504504030303202c40345082d0103c7c1070040180d00c031f001200501e418000741c40b50008681c1c81202d00300443c4400017015603019400030050303030b803140c8000145607000b040720a010030425a241003c003071071a20a0b00721007107610300b02c2070f14906102c0c06420 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 544974028 1250 544972778 544972781
    0x21809240d080a11010b04090c030512031b1812060601090614040611030705030415090b040308030402040b01090321030f06080d1b05030711180106020d03090201180e0708090307170d 80
    0x6141c6c0008004011440d582d2510100112080c0404da07842e200c0c10100380c0124503800200d038080c0030300b1070400c0d0b241c1303851500000403039025409540200303d056402c44034035111440030800020040002c0d0546c2d19105000500d501415440303141082900041080c802d0300ca40d00701c4003070715400c4c070340090b103095200811380c518801c802d40184144400180029218512250790b0031032140d0382c2d50514007642d2104019224016404050f00c803400410104006103455402100d6040c010b040604001759a5241c1006038515110003d8003058511602040b0aa00d8483d10f6080c000d4024104940c0f0700b0a078509944414000c038501c240700c000060403542c145800c0d00c1110a5a00c441221742d42d40d40b52074801505101c1180e81400f401c0000160030504890041d4a41030740e075254020b2001c0b41001008501a01000c01c0c03c2e030610071464281c1c1441040d0f145902c3c040c1c83c070346440c501107060581d40201000001007003000d00b0b410600020b40025024505c1c0000171403088121602c031500c4045030030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 544975278 1250 544974028 544974041
    0x301120521120a1422060f021c0621020643030c08030c09030a0b0f0709141e0d0302010f0e010c050904021809240d080a1101 55
    0x407246650310795040c2860141c0c00061407141a0750020882903110442c0c00025260681c6044190310f41c218002002c3e6064a0650903810150503000b079050001e41c1c5455080700c100300e1030607101c0754000681603480107508241901001030000f04000d01460941104a0b500b0b900940c1030034802260000300940d546c41041d0340c0c1c2000d803001c00322030244149245091007600400304440e0300841d03103140c0a05022264031003040c2c5400d41c444540d00802d541e01d40d515030344000c0580c0303004002403100c0000740d2010007500c010244980044040f50034040401600104010b04d00030801c0042e1000380000c582d640d0480b002d2100940b042484501ca802181d01588071098896402210a039690028168150002c5103030a00c102d0781004102245510b4500380c0c0d12074407040b40407400c104070811840c102076006285210403a071404c88030701c10300e40c0041c80c08901610182210f01001e00d003904804440c4564124400007110042c0d0a9010b42d036841c031981c0541a06141401940514900035490a40080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 544976528 1250 544975278 544975303
    0xa022b23030c06060312182206320a0e040503160305130b030126030c030f13050409030f0305091f0903031b020715021908090f030a030503011205 64
    0x594070b401003000d50903900d52003101d103a44284550301400c030a41132058201c94040c03046000c40e0400344451414800680900807010b020480205251081203032184150402b030019070168a2400081103215107107410316207150301d00c50302c0803100c600940e81d4400722981200c800052041681e552820072034154012032000b10480b01042c05205c00f01607000c4028100301c401c0c14541c1c00215102c030b4407403a480c0002d0042d074024401c404407841035502c000c159443c0044400c000c40e490480d40030441410354002c24884840c840d008141a000c040300d40503d40f01030b15007600c04100d11003094900a1034140222401c000b41551903000c1207c9900c18440c1440604000c0034140141c003500c80840010041100290002444c10400500240c009244280140100d034010324410382081140e103d0545c221080d0380651040c2c410003005c081d0406001e10f219401a4820380c0c85d01892350500c00b009142e03600c1d282c42600300120242c0040d0300401907034152006451fa0480840712441e1151a000c000000d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 544977778 1250 544976528 544976533
    0x7090e01202a100209040c08010302010e060f0f0a050c10020304030c0f0204151511010b0a26060a02040e09010203060901091808191404030807061116050a022b23 71
    0xf404000d44503800401c1d0b052070075181000401265903007111286428003009001861000c00d11030b4a00d0036001810030004420345d41071801c00c008003e240c10f40d10101d414808100e02040070b00c03020a040c0508000009124001d6156241c20f5034020604200080003c15100504071000c09540701e903031103902c00200440e060381e40b0f030b5160f0350060010070502d44001c00081020690307068070001030091000c443c01c0a825034690300d0904108414038200c0000341e00c10300c0d01120b60202c920f407007004410b010742e601c814016611824400d41403800400100040740d02da0042041c0f00c001d490b00c041490440b201502d001a1101c89441c8190355000601c20107851680045031403010b200508081e1000d10500c1c1d1200e9040c03440d1010007590300d000d80d02c800382c09081d00703000100200b0f001c0d82080000080b850782c1c3d9407501040e4848a0342c90340381030200b514240c2c4a9040003045042c01070400250003446003018080305465009040e41000d03003c0b008289074607003c0316a120142d8000c1408401d01d11005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 544979028 1250 544977778 544977793
    0x80d2309011a0409021e181302030706030c020a110310060b1305090112031d0d060e060709080703061503020424060512040f050a0507090e01202a 64
    0x40c0c26000e850700c00e402141e807548035a41981c0300c1c60b1610607a0030721513010304002100c6003207040d0034100b80065250765421403404800c15200d1516502010b100380b50703c0d40d44003060059801414501009608a0002e05150580c0c4c04c0a283e00041c0c0240340d940d0180720001044648404281410601d02d008100c6c40d0601c0c1d00440c20503650300142060340d0507080c0344410030780d9030010000350000c00e228040d03040458403d4100440d220b9440b88403442d01c05020012800f620030046100f00100c0703501070b52003580e20b0b8003014100030305220094003c2c01d0361030403031241030500c803480d925a8000d1200600d013030344d9002c4400d140d8924040f69002036400500c100b051140c501e42040310030200320307070501000c070055070701080f114080c0040d0780c9000078422405089a03241d03030f40c4020911460300d00b69924417400a100d000603104022140113402c84140c0454111440128135081d10304c2c0c20300e0f025449080ca19508543d01009094a8010032250f1000a03802040301070b0304a11280c50511000c64040c181 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 544980278 1250 544979028 544979041
    0x1090e010b0d0f1517010e06010e160215070c05101104030c0b040b0403080711130225150507051306050306010e090f04060e0f070806070f0c080d23 65
    0x401400100040e020b042c01400c1c0c21404840840700521001010451840c200b40890481d040100500c1e403000c80c00014103120000302c06151000c260320400700d0000c208d042000341c000700044420b0307010040c001040036446550640341c10000040100c010403040004840c24000c1c01c0191030304104160100300420100e00d1540c40c04c6a110780000d8030310407120540001d000600070b08550440d8181040142414119a01c2001540c05403406551b142a50102e411185d95016200c0c80644c089450040c1d45440c402c00908038a02d15103501110760000511500200703441c580c00c040640c4142d00b002130a5039403c0e2044c0d4250140101c200e01c40f07030241c0400f05d40b054200b0029030140000740c903040b07503c0900c0d0041040800c801c8403c44801034104c404100090304c180c010014400009042e03600780026091607514040c5980c0c071144050b03002c4828010b11a402424104012180c0d14282020303140c0707a00d62150503c111815569210f566400e4510030002c0f045207003525003f01c0c1c48181040c10b050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 544981528 1250 544980278 544980299
    0x60b03040308070203040b070210050c0d1e0e09220b0408031e0103030c03030c09120b0f0a0c0815010203120f0708090d0f08041502120a11070b010b070201090e01 71
    0x44804074003140c44080825440c0c2d000200b40e45c22691001d03e0340b440e04169070f003807001a044084400302030110030701280081c03c0003480002c211400707982d0307022003100a0304c1841e080c40c2c01400509080c00300c21700c000d01694640c100703501e600c8142040c80e459007502101a03000f0f00214100c01a04031844c4000b40001c1002d948015030040c100c81d101d8111020200501800343d01d82880014089802d105c0f03020002030294000720910509400c00340f200c00c0c0d0322056130200e030f10030072411140001c402080001d14005042000d8001c84040010807801c6d034004801341c0094400791008400005e2182c5c030b00001e03072003041117400c44c3c4607014403682e542c1003403078054940714000e850385404505203c000907203503503000803011100c61250ba260440191190b03025100341c100a401600c05441d523004083d0304a1280c00200540b005513140d8031400d00c1c181488008548103810b14a00910f41005690b01050f840701000e0306560300d01121035034800030b92005880d8082664130031101031040000008541165 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 544982778 1250 544981528 544981531
    0x90402130e0607020c012f0c09072006010605070b0a090807060504050f0f1c03060b07030804051501080705120a020a0e16050f0406080712020706050106120515120a06060b03 76
    0x3036001c440b1780545003001954151402e030012203051040180c0c821190040e54100c01c040c89807001903860741e0041601145c0308078401c44415000c1000c0514815581803a210030080e007203542800790141d541041c400070136603c40c1e044050200f03e6148042600b80c106c0e039115916050703200e95016a113400b42c2ca01140608400c031350036111406501e040c035008460114581c1c01100c80c500103803503030501c11020030481e038442d03400000c1050b035154000b00b1011400b60051117041e000c0c0d00c5004261515252451410800c2c83d410311840c2440310041007151000204913003522401c894040451150150355450328140320f401a5101c5003c0c40c000600070055810715000b40c01c0055034211921407290107038ac032071080c001e0048480204000c10801c40c0d00c00c05c407142d0814481e2812420800600d901c400c180d0304294001d85a555540c001001407541284a03a21081c4400781c0621083c0342071078a40e80e80b05c0307841c0c0384207000302c103800041074445c002031180900095210b00100409a1603006912040c1c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 544984028 1250 544982778 544982791
    0x504150c170304210e060d140603031603030504021503040c090c0e0f09090c091e0a0e0c10090f060914061603050c01090b070f021006060509090402130e06 68
    0x1e4511401088009010490b4401c940203d240b20b2030707581900340f514800000d004241c042126680c002c140d6503039014000e00c0302003079010011861900041ea02e80c81d0f0741c2d001d0b01e480c2c840e40c410803048060355410841a03000c2038141c1400510b581d55400450380b4400322418080280c4c41c00410041046220307034101003039512402007002001e6030b05001b503407034142c05507103140e010010b100c0521080c60600c08056106170907900741c64032400c224021494840041d203610420b001d0300d211b1182d000000304140d561005100d5010f0041c48c503100c030b003203031a444480c1d220303401440d0904a0800140c06403a840b00200346401e102000c1950b02c0e0001400c840f03150240d40020801e10841024528001c401d0f0707034003540b0b410904540420300c0c1d5000d43d40e581c4010303408419552100b040202103040684590300c00d0b03849403550065040701c254002e08108600e01c1110000e860444148025640403045e40c004000640705521507807030300d00004a82c0841e60a04000c0141065681c640c003d4011038503e02451 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 544985278 1250 544984028 544984043
    0x5040b192a0206070201061409060406030203120a0806060915090a03021e0310052217130305150f07050a120e0d1202040602030304020d021908030309071d070c030504150c 75
    0x1104c0600490907a130461084444c045d10341902d00801e85130a012540c1c00090007080000c0080e52640445d0400005600a0b904a0004900088100c1d044041190b00c00c008445813450900d004000900000d10f500032600201d001144a0701c1540760040c1ca00b000d190010030247c541807000e050381050100c04902c0b14028082c090801c0304c10b006074025103004040c0e20f42c86510607816544280c803450001c072020303100600d0404d141910001203c006081c81e01d0001007404940342982049450250602e2000c89002211010030a10710801d1844603000b03e178501e4000d60301c0e000705200b00d0300400c0030700200460303528024a038403000d0300c002401c14480c0001d884103a03a091603c50001c0490041e8480d8001503007041000500518144441410361480146040170202c8420603022141000b42c001c80c08580c0000309214004400700920300c01040d800d210301100441c001c1a1718040d030344c082c0c820424404a100c3e200d0030103004505507000341c0f040948101084001000091a0f200d804000b0342d4051b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 544986528 1250 544985278 544985281
    0x30c0106050402090f0907090315060501030e150a0b120105010825060906080606070b130314090a03150603080c0d12050609070e210303041505040b192a0206 69
    0x1e04090003603540020004100c0c45e10720503c0010b000703020100a041e04c0801c0b244890202c009042050a8a0001c1400400003805401c08002404442c0410000655a44480b00e810740f2504942c00b101c1d482134820201181c040c5250010031a6022020145082542000700100d500d0b480050400c0e0340d1100b007401070603c9089100035210b40000c13401040c3c0050b40d0750030f05001c40d5008002042c0c02c041e01074812460591141c40c2d15a07004400d65005408003500c00100052507446010303e902c0f541e2007000740c4d18282c4040d0001c1e04000c0325100003000c0e50201c0e50524400440d030751148005581200100b030303417000c6090100e510f80703074404001c4021840e00c1c560403030b1102c003510402e84140406081c02c1140e0b216024161071403c9420040c940c4080c2540580c0582184080b1002c501c03d1100021501e90a09141492648888501103202c8601d0001004045400010350b2500300120320724820b9840440c02840025062010b20011408191400159082d00ba0351170000c031032080c0c1c0d091301e415 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 544987778 1250 544986528 544986539
    0xf01050603070210111e09040501050f06040e0903120403020d110d1407060b300a050a17040e0708010501020d0306060e0111071206020405210d080a1d030c0106 70
    0x502040c0c4296005904c045000360890040c4da020f500c0360b030668603616007041c1ea01312002d20b05014031825101800004522540c450500d13003c2c0c40d004d000c0448503041d0351405000403680710b020b513109500b40034154070040b400740c000a0044903c00c481180041280d4642810301a6640c4420401080001c242e00c484a0342e0080100b40201d500c07249655101a40c034403680d16030040d801c8031340c0035134034960b807642d070a08141e503480d140500d4135003400350081d10032401015907990b250140c4691502c90f0000160440018000324100d02c6541d4025011035100712405040300250090390802c241e410184401c1c883c206400543c038034100c4200764212003085826040c210241d8049120359004250a404207180a60050400181200e608001c50381d040b0369460202a82820900050700c1442d4000b0307081c4102d0a2590b180d204280072400c86011280412000700d580d890000788503401c1201e000d002c140304041503000304c20003140c0300f94004070416002141e00c0d242c0d40300b00c101c10071941c81d00c0c070005070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 544989028 1250 544987778 544987789
    0x9010603020705060403110c0d050c01092108131d061e010c12120f02030106020f0f060708100302031c0306090b061c14010801090b060d0f02040c12140f0105 69
    0x29950050150441c2d4541b9a400e070b4400811090209150194902611844e03e420011780c84542c000c4008010175003d440014000702c0480d000107045400410490b25405510300340003111a81c0f0000280c0c1d03500503a00034414407650303500322040c81e01d10101c1202d000b03d034401d03295000300b508403441c00d400306440302c60f146592402a100303404540d04030240c0707020078001e00c2081031080241c107112605900300c2c4554800c507004044080000b55001c40180400d0703504116a550030000b5200400c403035070340c1c05030140d42c41200800c400e08000c00800082c03150100c00c541034004550144c11140042c0300c140c5000c980172200b504260009103032000002c0c038030109005c0da002e140300160a040c03501019241c88400350542c101c06265450302c4140c040044041d00c030401d4001c0081d2000060110414504400c0d0150040c008600c114698100000440d541c0340366101401c1c1c2c115400100010000c1058880181080070314401601c1e0440340d400700704a80300840d10550b14031031401d481d07a0700d4208105 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 544990278 1250 544989028 544989037
    0x1216291818091c050903010c0305040c050a0f090b01020715120e010c1407050a0f0f0b0f0615131509030209060406030b450c0a061209110604090b0901060302 69
    0x140c0c000c244643c48800d0182541c0210152481d02d03e1801100001180c2034448180321040083da45004101c24800d2140154015110882d80e100002e850108541c103000030500139402c21603039404000c400c9038001c1183e440108401c24200760200c9400781d01030850a001c00d00b0b00e05907400d22000c84404641840707001d002c0907044d22000d40348200e070340c401c000710740041d081254540f08140e40d0308085400340e5050b000941c461104c0884644807494440fa8400f800f4004071110104c4005024103603407182012603251101100468540e8009201d00004104a034040c080c02806070400d100415401082e10055074000e8400030480d07100d0006100c1282e00354840070300000201c60200d125042040c0c000040e006003281041914110401802c1301d40592801d4458080c0308800440340305801440102c051010803500c2c031468514002003e40350182055100303808a40e40c249980800c80c10302e00903007031000d014190b03644403070301c90881800030092a07a0640c0f003820f42c4030000030030a101e0300894 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 544991528 1250 544990278 544990291
    0x3011a041a1c060905010e030a0f0806030a0326070f110303060a0506160605090c0901080f0a080f040b03010306060302090f04111504090c0e1216291818 67
    0x228800084014180207460900c100f1189161144ca010b0301191003400b4100304050894095941d0f40301906005d04500101201c91061009010400c02d01d6030b008a020780700603406051189031003000c4107586e1280300d68080201d1a800c1400107124060b5400203451904031510b8441c01034000314a13450076500d0108940c580d0348240c03078183c180f0040c1020006001240100410540036100c01d80d500300581e0070445188400d0752008035680a0707450301305122070050500038003410010449050a940703c201400000d004441c000640380121a0403000710390051441d041001d0716561a0f1a110024002c1e51105034401e400c80000f2420b0780b01e100117114040e5034085200e8110030354040600035880c074220741e8070742c40002c01c2c0400580501c96000d6078802c5150b513626207199028100800580314181180d03915103500c488001000240440c20707840541324040e02a055404408810f260810355201c07548003821804900604010354001289a40c4002218980320311100320036101c148000c2110700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 544992778 1250 544991528 544991539
    0x503070e01090b0307080706030506090f0c0a0315090923030f0a0e010201061a030901050c0a1b0606080a030c17031501050703090e10060e030a0803071d03011a041a 72
    0x40100c442070754402003d80c0000741c2a100e440c0e50380e204160038100c5d03541c804804283c44104100c41c40c5020180c940d400458042c20401c1810244d0102d82a401000301c01c105140c5c0d00c081d10426001c0413006c1e2002050681401c2c40030400501e854030b40900490040c4124048a0030010381c564400b006035000d1604000c2000d0500c3c1c83c00c4000c80c3c81c1c4d60f0925109066550310035001c0390b004e6450340b0311950954654406c56032420800006804c4941c000c000004824040c403186000d40e07402080c0e0303144014442241c2d01a0a46400c1c80c200610040d031240016200d0356840d101056003000c04900c0080c01010807400100c104020a0708600c411188405410340002c085c2486600400140080c40d0007071500180b03190700c40034440504c400503a002c0321010001001001891383c0300b03055150010f02940600510019a95902000d000180c4030505118072031400380f4401d11540d40f50030620310700030028801130004500d41c9082105080105000741d0038400c0c10503401602071003045120b64043c11 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 544994028 1250 544992778 544992781
    0x150206061e010c06020c07090207210905060903150a05061903020a12051c05090a08010204180e1c1d030d0207060305100f0308131a07081b0a050c09010503070e 70
    0x44038800c070f0010381107411a80c01e000402c02c48404001c1e560251030300d9000180e0799442410a950701c0034103808843d0513290320081c15030300f1035400200c900440d4020380b030301502c0d0203454000a0904090401d9003503d0f0310703602c2c2000302e64001d5030003941c02488103603408400c490010381004d8024a00f07001c065044207004104210a040141068030640d010b9015661150781c0076950054042603c040c03400001e1001c60841841c1ca8240352007001040c10304001c600d4145481d8080b07080002c60400341c141c45650b1200c224070104140040d000e0000600c2c445c2102c100b8452002e00260115007103035081600c1d8541c01d0ae400d0a0003d14504180c07100d80041266924091044010300402003040100c8160401d0004035008078034401c5018512910071b0b291905030441565002c0c02280d400305414058003800001c050700c08004035108160001e082c165210108603500f1044034031085240c0603841028034400c00c0c0039020a0142c07a038a400c44860309140d0343c0f0400c05a884003113016513038104c5803100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 544995278 1250 544994028 544994089
    0x9041b080c07060e06090c190515070206071e120306050105030402040b03120a02150703061d060604030804031a0108121b070e040c0806070203070b06040903090f15020606 75
    0x100942803052243c0c0c40400c40c501c950002c1c9081c0102520a0b803915845010a003a0600d01414034480c400c00780258148003620300000149400403d035003601c0090000600c2806540b25001210202d030f130001c40030000710181d00344a400c5040e103000d06803121202c0c030604a04240c4030340601411242c5c169107142c01c64403140c0811004014481415506101d03010a506040c1c03800320203898641903607006402c505801d101001c41004c0000c1103c41050b203010030074840d140011045d09550080b20070341d807095584080c082039183c812904040c0c00030300045400020000550b44035082c0c2c40980203c441580d0744c030800796a60b201881d22810b0000b0003404a01c5c945504251200c00c801540002c96950a517a00c21401c06004161000c1d101101071300010f000c0c20300c01300300194101480e0b100a616002c0300c1c2d224908500000340200e4030440d02c03140804281072186080e0340141ca00f2140105039196035441e412500b00c0d8452444015000c1c2d50000b0b1030528040c2d818000400d84441040305843c50070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 544996528 1250 544995278 544995301
    0x209100315030605010602010b190506030c0d060506040308090f0a030c090207030306051002010b01021504030503040816020301110a020c060c21161209092d0e010203040809041b08 79
    0x2092501c400050680004041585030003298020280394000069010891040c880310456070300d204030110700e100c00108682d496907411a603029008051464403003002400d000003800c050b5020340d5000c240801d0110074041f00c00020400d180301159810505000b4205002e80a030091201a2044100c100100015030b034035002000581d00c00d26000990989a000242c0c00c1d0340ea00d01d1b5400182c0d5903a040f8041c40d60100804084c003180c1d0040b02d40305140c680e44c02442d6110091008008480202c0c0f100c0003045110443c0703401542c024000d200315881020310400680010412a0042c4550700800b02e05003400740480d1a00000403000c0d0511049840c40c0d00d509070b1407452003036a800001c0102650b220225841e41e42e000e803081600c441040d100b070000a082c0c0500d03030400c8a100d854192004421521028906a205800c02c0c6030318062000428075001420094440c0e403483d40004100400c03c00104010036409008903410080700701c0c44095948040380c11100700c004242d00001180c1c0e0320504 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 544997778 1250 544996528 544996541
    0x61017060c0c0f01021803070501051804020a03110319060609030507030204270501051005060909130201050c1204170703050331080309010206092802130c050a0e010302091003 77
    0x302c101c0f032482c041c401e50542260f200741c0c03007459001c1407014901400d19041c0004c0d8024203092070f15504010200400b40d986200700611544540d81c0040c10481c40c42c0030741c0100384401c01d020115030f20780c9840b03c04203030346001d5040d00c6c010702450181d003c0742c460301654028007620b030000c0050400504640c01d11004045024a40420540504101a40c2e0314140000e00b1024454000400c1d2400c00d040d0700c85c80c251154004c42d214410610482d00c05858070128240c1c003164640c010380c85030b801c078001a81d540c0314003074460143e405904012a4005001c500610444680144480702c5080c01000592a138606020040c03290300204101c8407003040460720000100c03140d0005c081d00d48884182090078541d82e078000c81c401e4001007244c0407035603018020346500002110140074109000f40c0d1034000a10080e440245031000503116005646034103045001000c0061401c01100ca282e04014280303400c105d8055000814011a0090b40d502c00d009950b43c948018085090301203644000390098040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 544999028 1250 544997778 544997797
    0x312050c0c2403090c2d010c080f160204110702010801152304090c21110406030c0e060d061a0403050d1b0f03050406140c0a1e0f05061017060c 63
    0x95540c045c0001e50790a078113030800c1e501402400f881c0e48091151060b0780c000b05000c0505010390181c7c810041135040c003c48204100c603044a6944000700028090542044480a5041464101405400701c07807034005004540c002d0f03c524066a91307501c0d01c101011800c4041e00d0001e101400500300700509640d00415010381d034250300741000e03181c1d8401000c0f210300942140020304000c445d00d8001c0c0c0b074020452804070108000740b2660b00000311040072481503200f25000c0540e2202c0b01781300d8502c50f01200040c4d240040c07086030364240520801c005003026000d510030b886109840f4100c04402e22085074102d9034888041c00c0b000020305800e0360440c1c03414000841c843c40260121002410451510340d050b40710b9100c55072035a0800c0c0c0700402002c603d924100354880100200d21205500007251001d070365000061440000340440503c1229043d904014504c5091000410803ca008256640304405052040001ca6540c0e13076890840450f108070080a0340228003c0f83d81211540001c080d1a0b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 545000278 1250 544999028 544999033
    0x206090307031a070e03010e15070306030c1409010e040f17040315240b03010918080a0908010c030c0c030f1103040902091503010812130312050c0c240309 68
    0x40d5661074650782512898181c4040b243c48000704880d8a400ca02402001035054000704508421800d150360780c0d4206000009100b54018001200c05203c0e40095000c6d50b4000c541000380c65440a08112009001c811103205210389000490f4884804d222144290741040114105100c99110807800c1100d40c0086800ca650411010010071004403180001c01c403c3c0c0c0001840300098649014900c050207045019030300014010800180fa400c00e690565090101c00184101400011203915a00040c01010184082200b00c03280341c0007501c000850b84502e00031300481034150422001c451500325444089071021045c08040703032244580c0701402c41581000345d00303224008085403840e001580000c02072600080c8000f56802c1c0b005000c8424120804194155410072142644030195041c1d0400c5030750020030502e0f100380750040280d0081d60047c00205000070701c4200180030f94400d104041061040e86616089428001108403406d0840c00803030b80e0003039190f1483c54490340003814500051 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 545001528 1250 545000278 545000293
    0x306011d0409140a020a050303090102120c031612080601081006030e0f1905070e0f1803070c031101030b0a060813060f060b2a030d020a05070605010315150302030a02060903 76
    0x3141c80c43d90039140c10b5140011301120341c2910401100048503040303640030b40c10901030700c076071a600058590812040c0344e03030b4030351103a2030700e1841d43c80e42c01490240100c00c02551040c0c828000420811581007081e03a59203201c0f039440c44c0054600d014150741e4210440700b1340004020050ac40d0f4001443d41c0081c1e01a0b5481c901c000c19a0b40c81c0c000c0325030030300e450346201c1d010120402404100c8800200700065188981d89080080316100c1c040052242e0760000b465098215512428800c40e888a0b038000c0136825080c4d201d00300108109112450380f804649880c81c00d0b1918500641480c0417a0b229a59196003607480c0c8480d40c0b410800c5510444035551240039402c0541d840d0f0081402610101d6071568032941d5a203514100100c0d4542c0314030350b6820901c040c4400b00004811581400407843c005039131040a03a00031a41da12a05501600c1c03d0702e400008810090b161104845400b08000c00388040210f030b08100d0803040c11884003e500d584000307520b90050070724402902c401c170070042c00d8076101d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 545002778 1250 545001528 545001533
    0x909060f041e0b0d0c120f05011406090108030c0a03050a050d0608010f1401060804020f0a09050906011502070b0409200316030609060e0708090c130608010605060306011d0409 77
    0x650340b071a095075942c40580c1c0c9200322119a90b2240242d20082240c411074000c010307489200c0000c0103070044841480b1041c29030000e00405004402c036072076208008121100d042a5404402c0d42d0946072a031207070808000004449800000b035501c0c0d00f0740e107000380200a101e52780641d00c603442200400180031303080c0454403241c0460f100c0e103001081c002e400412a0702d0401420400c0b242075110000c0e03221034490042c0160350340841a50f0388554141d540440c9091309c000069090500c0b517100c205461700301420082c0e9201d010071010b041710b080d0300041c5441c024880d0140d0300d401007400717882c0c90707408148010442c09009412030036008100040c06012806410304c80c40080e4400c481403140040f920608945540e4140b00d10300003880c4625041140c1d9042943e440d0101102910100800c140312012406450041c410b042002320000e210000f445050303402d001c083d1020303208404881d441c000000900b41040003c50707209001c141d4440b6903403520280c0d04900070a5901455410550300d0140000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 545004028 1250 545002778 545002781
    0x20d0e011e03020304060b010c0f2a060c020306180c01080a06090e1b030706050702090405151518070c080c0a0206030103080c0129060d0b0310021c110909060f04 71
    0x1401003030342d40544c0d00d1805042480076034a402c4483c9041200c40d1103440089040c2003e28003d41c0e9100e000200c0d001c8440580d2241443c0400b910b08500700024800940141c000500403031b004d1081e416900b250765103401e2000100901c02e211074141d080302c140d01c20290f1261007900c1e44246488070015055441e0103c100450f440c0c01202c03c004d40c0200180b04a0549598a000c5035002c124000c2c480e250401c6002000d5004505000b07010b843c1c488041010040144050508190b00e80324170300462400c10500025190364000141c000e1444a400d0444c00b8110300719144280019118002282040d07516241198400070405007640111071590006a542c0c01c020b500850264031800d0326880074909103070864648500d0250300d00034104000240b82d805181006800804641d01074403038a608030040043d05498408070341c140140d80318190030003103d9000d4902c80d0900101e02c60312001902c40c140869400c4284c0e02643d10040c0b200810902e400b540340c41c0d0114001d0141d07080b0741c0018002c80d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 545005278 1250 545004028 545004077
    0x804030302070e01080106050d03030218030d030c171314030f040923070905061308072301080f060d031101020a09241d030106033c03020d0e01 63
    0x40058000440803c00f15040c2c0300c40d44c0c00b402c404002003040c240740400091213000400d0b4000c041c1034010404410a101d804003450a02c880507040d00c0281606000090041c2044e5140902252107010584045c0e60405100740c40f44000d180b00c0f100c11412034503180f80300095601d007040e40788000c00c22510400b40c00005040100129000884e0100382c034200d00d06040c18054072a0426a00f170707010842619841076070102240e0055945654076078074426400351241c0250094035040c460048000340380700740c40007080d00100302241d24040b444048801100e1064090b036005030440c40000101c4c51038603004402c074407441d2003803e0080c86076503070b415100d0990700203101b5600806c518220030444442c070745200c0010741035038034007101080040d00406011100e502c046900002109140ca0605840940c031035806507400003440300c40d00c0034a0554203144605907145503044204c05401c0c030b000c04103a03100d07600c8a030303815000b50100721100401110a000441c04041c10894605880d0305203000000c0f026 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 545006528 1250 545005278 545005283
    0x20a09051501030504030e09150303071119051503070302040f080a0611040501050d091505040807060c030507051c060b0a05041a0306030d0f02070b030f0114030c0a050d0c03080403 79
    0x41824609000c841d03080d151011046810305043c00200310010740d0101004000307000031200c00c0c000c0d440e8080d003000c0f1a12442081901403000052403011b21840d020045107045045945030040000000001141080b603c1480d400c00c5004403410311041106010390303405401da207030050425603030b0301801c0e005100390f50204101c0c0d00429041002d0140602410aa0030406801103251a2400e80028054400c0c041c85c003035529544e600310030402500c400c0038007171b800c0041c4040c0090309090904a10f0f0307034002c06086415034913005d0050401030290033424803c81c2592240c0b402c0110821840072014000900c0b908030b55902d01010816031925405014002e5896a65603201e5007018059400260140c1c107a2960040030710410605550018440d1540c00f03140c9446060000352000c282d03c0c2000542090301d68540c08820410b9194003c4100d81c100c60002d804a20752150810a058580310f01e500301503040100010188103d04182c2510f01072030303108a541c6c500a60781c036200d4030700300c4d0400c0d0400c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 545007778 1250 545006528 545006531
    0x10b030c1c06050918060628060f1b0803040b0915070e0f0d080901050a050c0d02010221060f0609061b010e01061d0708190f0609111e03040f020a09 65
    0x901840c1009402c05900c5449901710741a00007041c1001d5039201d100509141c030511400024119903c4105103186150708000704c010320941d100c00c0054510884500840b00181262141c1448404400400c5894a80003142c2d249513071a1610382a0940300002c00440c0c0c58400c400380180032040c080100381c0f2410117a03685031814280c0b80100002140b0000c0b0b001d00c945032003c42c10000c1030300c0f038041300c04840003400c0299651a940c1010b88550141100300202c42c0100744003c6480e903019001010700700c440e075101507072180307070b81d00c801c081d580b02902d010f600b20500b09101031a40c14698001c00303407058000d03c068200762140c104110ba040040003004034994455801d20900c5070f0074003d01c00500b159070541000302141142f0000d8604000b07144004200515001c90040c499030700c5500c0040340d09500900264900307407003500103800248a628134141c901540e03102108040801d1311504c0b00c0c2c0380c607a50030100400304402c17683d030030142c41966080300c000310840c01641c81744420300007022200d40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 545009028 1250 545007778 545007791
    0xe030a12080c04030b01090b030703120203070b0f010b07060c020115032909030703050d0908030c1c021303030e04060f0f2103120507171503010e15010b030c1c 70
    0x80109054009000301851582c02d000074400500c1c50905181519005030001400c10070300d10000b441c0c98030b240c1c4040d00c00b400280f04100c01c02da01200800f5000e00030810881c454880e8403102800030b50034450440d0180d821300110340045c505400c05112404248004034071940040c846000ca096658002c40340d41120a040c1c0d9201140700003240e02e0b03248410391003901ca00d451030301c5035244d21418200a00f0445c0000d00400b01681c260701c45d11110b900050225220314110070750031220391080300d002e00c0e90f120300011141880840d0080f20180040e12105840051446d03400343da000300c2c001ca001d9480742d10341c135020130708111041c0301d90010002d15034a400c2580ca00901c0c0c001c8000c522480c01801c03001034101c40080303034100310032541418280344002551b07910054115400c86050001090f0341c0303092400d00016114000000030a80411002080401c1e00d240b04c85e96a114054401c160705440d5500401100d4605400786a1101c1c040c0c09561415540d094400c802c90350300d107034044d02c50780c2e24134 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 545010278 1250 545009028 545009063
    0x9100b0903010e0729090a1809050102070305071b0303020709110409150303110304051c0f06090c050a0e0609040b13050106080d08010605031b0a0507020303040f1517160e030a 77
    0x441c5e0100011203181c0070f107401008800301d0694500b601130a04a4104502104083ca00c607520064406030848002c544840e035a2034010423a0344003d03030075507040b0f610340720300d8101d10b903640081d0040307039410740081480a140103850005031070b4203080c015000d001400002104122405296522080001c030941100d0035885e0203088200c0710b0300d4111041c0d0080c48203100f1600c0740c04044012013000300880f00112680d03e40b1918504480c8801001c01e4200030b0390307508112100b400c10f01902c9046908003000c9440c2e1101c0026802d045070440d074480300d0207012602264210031080e400515030f1180b0294440300343c84240c00d42d006035001c0e06050780881c00002c50703240e00c2181907014108510308107255050020560362001e8440f4000e1904810000395030000034090720407508115405400c1d00d4855503a580070201c03ca100d48504e103c181040d1815110151090604607510122543c000141c0c1d12160201108401a203036580b090020007482d50b84aa5070800000700c88d107200c0d4031040212010300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 545011528 1250 545010278 545010329
    0x60f09050f07061416061109061611100e1903020d05070303180b071b17070306050601030c0828020304050c010906020f0a0f1a0705071109100b0903010e07 68
    0x8800003c0e100511451a00c402005d403018211074101c58041145450000503540d01d00c04c2e1a001c50380803800103041d1200074104851064124011008400e0582019082c41903401c0c0c1c00440740000740c000b03151030505241000040caa1040c0c0310300044c590540b0781c2d002c69482422032500f07a8007640000c00820030550701c0f80350f4030f8030303100d1100c1e4200b01310b40741003410801400341000042c24011040c001c2d401c41e5010513080001800701c03a402c1c01c1c120b10441d403901e8a4203228002941c1135410130700041d090f54080d018128060249550351902961102c40300d10441c182405024440001c030300002600741d582e40095800340b40110080c1018100010000d000030a46621060554004442c880300103400807031070b5105290007110350070801e10b081c507003820564150f00040480300c0519003400200c503440000b0707160a61003000502c8000301071404100080c2401c82c0c0c0d07042121003407503080c40803050711805049401c13006800441c1c000c03c0d9155150601901d43c1040da201d50348080d1740481c10282 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 545012778 1250 545011528 545011547
    0x4030210171e060d03032007060e0303150d06140a0c02010c0906091502120706050f01270e16060f090509010b1b070b211f03060f09050f0706 62
    0xc0001c0b41582103100002c100381d041c0c02800b50f4828098111490203050098010100100c1c801c00d01c4095611050800d0b84550403055040d11060b00e040005901000c000044a0240c1c00e061550242c0c16803100c2040f0f030b01b0184c64005c0b140f198403101a00c800111030030406020750783c40540032680e100e90711402030865000c000e54108104076242c0401000d9040003010b81a541d01072511a608100014180d00e0424119150341c100341000941e10103000d0319510407401920300351650203250740d0718012a4002c1441e9501883d452820101442031004d26038803454044c40d10409075111140420403c85100320b459126201044075214590ba81541c4035030110040c0900304c45469455041c80c0d1071031018045d02224882010a4191082000d0400c22079100203003d904070442d601c0a24052540c14810b02d444107000000101002c10158001405800c401e07000c80c00001b06c03900d146485100207005280701945109640d030807030138003240c403e200b03c2940440d2000201205032518000601038800d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 545014028 1250 545012778 545012791
    0x20307080430120302030709030506190e210d060909050c0405182104080303190b06070201020c040f0e15060f01030203090a2915041b0c03140403021017 67
    0x40c00c0e80c40800203103510392104542003c40ca001a100d40d9007040c16518903490360000f8185101d0b02c0108020422001071815025003056400d1108078038280300a552002421940c042c41d03112890602d10071a007183c050440b507100110301040c40c540d90030b4004101c40403900140c820b500002191510350501d40605504820300b09803140681c0205422a9211024102e840981000c0c48422102c0140034030261005840c0040c00e40b60b41e420b10f045507e82d40c0c0d445040880020f41009400f4005103811003e550000ea0103802401e40240c80d0010040200410101c050000d5030314410070201c0c070010410a820480014075024180c204201040007580c102041c1604040c0100100142804040748060f921940880500c801c401003030b4015400508044105c01c0b24034140c010060144444d440321044c0a83c03e450800400d16060140703080d40e1504580700002c501c1c0b0304050380009106400400c00b414210304080d00b020b8581d40040c0c4114860450040002e01010100d4502a03251003d0780d000f46 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 545015278 1250 545014028 545014109
    0x1020a1403010522110a05030703140f07080709080712230309010c240c1106040c0b0c03040308070507030b010f03030e0f060d060e0108150609160203070804 69
    0x600d0f100000b100c0c1d4400860605040400e000c52002150340d83d04448442c010035450305494074401038008080783c00840300b040009007010070b20414903442c800c00d603001e8890100f081c507031551012000c0c0c92000700944040100321101c18001842c0303401f84007440150070042101070700490f60f4144540220842c2440c61480001c4070324031111000c0000c00c50b42c80142c01c0c01d0a60360908076040c1041a41c1d140c18a280e0303d03401c00c0c00136808048180c1d2181c0c3d41e011894507103007000320510030344a030b844000712030042c08820012400e220845a4a014000030000e03041102c0c9004e440340c2d510500741c1c20a120031a5550700110040c07080000780030341d6901410b542d9580a03c010710b1500c0003005180e40c904c810b4041c40800c50101a692103110459201010040c001e003c100c1d5104203155041909200b03c50b41d5004150300c6a108030242c28003107000f0f47c1e0090606180d61030b0383da80028541c503501104401e5210800c020000503190801400040c80005031102425554182c043e40d0b8081d44408401e40f403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 545016528 1250 545015278 545015281
    0x70b041a030910090c0b03010b04150302090a030303180f05010f060501021c03020306011205090a05120915030a2301050f01080403080a050405010e0709091b050105041a090d0501020a1403 82
    0x8000650302d800c2c00e05043c010801103401d08008098444940090340e0303403240000041042e214840c010320495440d8004a16001510300c011422402114181c9901c5030050800b040407030b00c2504030705c0301d051501c0031140c100c80f402e90742c030004400a03110485159464200c0703180c0c604414451840286070a00180402c024044070b005a035801c00c068600a0560110126001e0b910909240720701d640c480c0e00c00c00550824840d0607a4540040c40225445c3c850303d00d01790401b016003400e4943d085005805102d11070500200c242c116000140b0304840039559100300e98102d45030006c20011003050201103071840d41004107001001200d081007078140070b01401440002a4480351450380000c5420f400a55521186030903800b4141c8840031701e1152003400c1010030b41c0c81d9a940100071062041c0c1c44040000741c200c41c000c00c040224460a0302060040c0b208022030403e5100ba0b0000c2d850194005140c4400040042d103c4c119203441510349a50201c0c0b2081c6c402d800998800d40403803840c11980c1107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 545017778 1250 545016528 545016541
    0x506090708071a031911030f0a0e030403030e270702060f0705090f012114150102150a0608071203030e0606030304090c110706180b0a0e010e12070b041a03 68
    0xb889062580c0901100080045c0ba1116041020303a080c11250f0300c01d000d0702d02e041060205640003954808420100c51001c0b035014261841140f25424000c000fa50500745076071029a81c0b0600c2c40f00031030300614603003044140e00c0341c0364202100d2080301c03c1683c03d050401c1c2b20024a8054020840c90131564881c0c14040541d80107030950302c0c4941e044401841110012b001290f110700c54130440d107400c0f80e035880c4581c40710700f154001c04070720f40900c0c1c507a001c1c0750384880135010700c0c10800d101140540c000000680c91a83ea0030003455010742c00e54800b24100d41d948401714a0400c0e2980070007408d1000c45001010142c0c036004210208550303400500f000d01380400025103c3c0310b140f10318008181d4801c0c0d508405405100350f05038020000c07054418103581d0342c2c000f6100c4910115880e402c01d000410124891109405495007619150b50f103441130040003005403481910126129485900f02e1003c034182602044010050303c1041d500c1620755162128007420760500141c1c0b902044024400c001e007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 545019028 1250 545017778 545017799
    0x90d060504031407051e0c09090607020129010f050f07060b01170f07080601021204080102071403040b0d0216021e030d0c020603130c120c061e170a0e0a050609070807 73
    0x1036081c15140504400400f80002440c0034400b003407143c0c000e1001810002c500d4000b04ac106d01c00c1c03c5c02d030000c0c080001180da8101500e034211088020b0a07205642015255114081c0c041c2d4060450400500d044a8442201c0d466004402c00315a00b80d00c4003c0f4000e82c0d42d100500035040f403008200c000082c185850030704950b04004161404002da81000200c0f0382e8130030410001407145800320243d03106d4607048400d002c3d5111100a44074001100541c1c0e102c0440042260101c82c1c40c06400d038208003202c00e40d07074065403001514604150000040e1405642c41a040700355214040c10101d03402c4c05030000385402c140c4101c1d031440501c9840303194880076890b00e804880d8090003100f030300c21100115152510304803109800c07401e10130900108103000c22000601c000180c4826031550b100e0306111003420005090040381c105c0002d00c0d400303a0313080f10402c502c5030650850751100c4007007000346015540d5031410103551760a030b5842d4810f1040c050000003c4c40484081c00130748000d80f02003400c0000010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 545020278 1250 545019028 545019043
    0x1b060f08130b0903130f21080a051c050118050606030105010f03150801050906040b09120f0c070306020a20010606051204031e0f03140405070911090d06050403140705 73
    0x1c1800b114203000a4040c1000c0c01140e140b045200514100c442d03c4201900b035081c424014100048a0359400c0300903580a04043d04c0d00e030346d01c0040c4074a0314501040803125504001c02c42d04600901890031215003181740600c50180c6101c02c030f0005029407002d01d1401b0781d0350180441b40502c9007040140000d9a110081180b10203d505001c0b03007800d8071142d140205039580e8003264880d4a040280b203243c1001244c3c50b80034134000c00160740c40380c03a4000002e49070800c414046118500c104110121404244043c0c07540b06110410742c1e12542d44c0341c41d14400c0e07074003480a48c1c002410b40144084003200c089400800004030900801c007941c184000a03141e0b1241c80c00c4101112164000101058403500c440c0f0030594500e034017000118000000985034061000d0100301003400d08207854005020809101e04c140d030814000e01c105480c000000000b0480e003013548055410400c01400c0c1c42c0c444003031f02048184104000619844c05003001042d0b42940000002e044070f007006140080307000040e619 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 545021528 1250 545020278 545020283
    0x2303061c080711092503110f16120206102d080708071d01050402070227160e0a0e10080a0f0b01080304030b0114280f050105120a0f06031b060f0813 65
    0x7c0800e0801c00090b0140182c1c00c000309000c7c40044e600300040401c60032401203d102d4142018004466041a42c80702011500641042c00d200001c02c542400030b001441d40c00d44d2500003410007006401216101070350f94204200a520410040054400c1004140300402e0074518640c5903900c44600d00300101e0040c461030340b01e6500071411000f50340e01c3c240140d80d460b42030b100c01d84081f1111406595800800c85544000703807210703032241c1c007500e014100c0e0a20010004012515076402c04005040b2414068404114188412000300d000b030001c00c08117003900d0046500e1412640f0a20342b00d00840b00581110005800500080000820001c44241075410210307400c0b07082401000030415100e90b4200d203043c0e07040240c199036880c84101c40404141c441d16803801c0344c0c090302c5c3c1005462034420a1045914140c2d24030019010320f0241d032000e07500e90202c0401141050f600d441d112049403d0150120110280f07010411180d44c02c80c0810003180c400381010703032091805c0e03c04c02c0b08070710101401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 545022778 1250 545021528 545021531
    0x50a052202071b030609032d0f0302040503010603050a060c05040501120c170a090b0606180f0f0307060f030c020d1b0201020a06110a2303061c080711092503 69
    0x2d00402c2021524507068071080302c446010306030340b400c0003800303004441070035004500f00c401e90807118400e1310034a1140307110007d8106102e0f000410b046440d8540d148083c01095421721021502d135900380035100042d401140209081c40c2a81403800848076250803110501404100c204038598000000d18403200700e00c0f00014a40b168000c0a4500d004102d0100490001040412100614640c8030b280703c10b0041145142940e10342040c0039141c46803000101c0c107240070001b2079566203030081403400302c0c48018001030a20700030000072a10f02400c80d0407000c041947c1d000d48405503985442044040c400d01c0c8003c200010340342c02c02800c44640b031030000f104907984509507070030f5900030003d4402c40780e0b1080c41040003444441010b403294005502c0180003031802001c00c281c3d40f07400200d02c42c41054140c0d1807481d503140d00c003c11600c600c00d01070890030b0b0f01c02c030300760b130b5002c1a12807001d03041c3e41c1d020b0501d079400d440d000c1c0104004c0610041c500c80400500320103000c090302e4008080403500c00c070307402c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 545024028 1250 545022778 545022787
    0x403020f270a0f060e09010c030b090a0905010b060304231b010c06021b010c020708070308090d03021c03060f060c0c0e0c07020319020102242202090a0501050a052202 73
    0x9090000d403003c5140c0510803418441c00241c01d610220886216018610003001045900e4100703c06941480c040d03d81d000341c18602054a0180f183d014428032845400001443c4101c0c0001c100c80345c204540c19100244413054084081c9900d40282c0d0241031000094000e07a0000d01154041c09203d41c892030400c51407011035010070007140c4c1110f459141d03180150340122441000c0d68060494030446000500400e034000410f07800000741c034816139502a149a06250144040c4098109001d01c141c045200d00d000e0103190849441f0094900c082654010501c04c0c100802c0b030314400e03141c0d0f000c0c10401c2580303176485c40480c0c0c1c01c8a07082300f60f41d0710302c0c00100242c507410f01d89511401040e0f400380d03160040074541258003461350310180020703200707809851505034010f45081e045901c2155810102c000c28000440c641c0d0600781c1e0742901421255800703508400f540110b03020b42c00c00c81340422041e58400041c001881c01650300e1009000c1100d45100c6c147c4903911031011049102d680304052600801c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 545025278 1250 545024028 545024041
    0x31103013f050d0315050f06090114030a02040806011221020c06040603021201090b010f03020f0d050a0f0509010c09050f0a0801022d04030f0803100902040b0403020f27 74
    0x40c0852007009081000c5501107942c1009a11103020642200100349046490b0019104510851044620040c051011011144140222541300c0a841030410030800401d150442c41c0350f0145002e84c820344001600c45043c01e02d100c2c50046d06070015a800320810b10804005466004405401d480079556a40e174205903d60a030b00d0094030014840d40b0860204000c0360040c0c1c035034050b14114008009408203641e036000344034120741071241103500041c44220000231860080c1c000340388135007964003190328203030b070701280c4200316082540d5043c0d1040d1100c07030b04044001c140c021160801c220700020003e2404094001d0802c480611921b8003408007001e0b080025603541403110018440d140095558140b007841e00041007850b80d107070501464171803101903010b0f07032440152410f5aa100000414400c219141d209864200800c94018401654000324446829001410042200d90a100d0f02c80c0d041d40b04005610703404040b10703401403d030b4690b100f004903444a020021007403c02d01c880515210907 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 545026528 1250 545025278 545025359
    0x310030f050c0a120c09150b0a05090301050a140901050c160302030903010504060c1b020d060203060f0a03030302090109210f14012910080601030507091e030303110301 74
    0x41c2d09580310010882c00030b2805100d20418000364401d10283d490107031078580100032211401c2200c1c0761039003c0d1105010001c2400020101403010b4102507003820800d400003802c2d14000c66201301c02075291b582c000e245400489556130000790342402400189041152007101c2d00882c1d07045120502d2032071515050600074000c882c6e101e840600240400d1605051034400b0344080f140100004800002c481e0090591030312005200c2e900400d40016101d45840305000381d00082c0c19207a0014880d58140c0c60740d41e4103c0d50200451080d100540c964205400140c20580140e0201c40500c200c8401d50400b207079021000305600381e01c000410000c4c001030601203180c13070542543c0d0603035600e8010b40301c0d0039000c04004900c40c018403003d5071764188131140c14803c0300317410003191402007000800410907a40c002d4000c2c90788100146000000c1580d9039000e15a0f0780c0f8181242200301924003000d00030b0642c180244000790032120450751465141558681426218552005850300700015401816202 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 545027778 1250 545026528 545026543
    0x2a150a02090d11370f1503020304061805071802040501050702090c0f040305011a0d051c05090a18050a0605030d030903030b060d0c030c0806030a0803091c020a060e030310030f05 78
    0x221003040300000c049079580e203481c0d00d04540c00d0310030028600c4d001405010340c1ca03c4000f075650409102c426a00440c0054010750006402100c5031501d440e22181c1c050421030b681c03844240500c00030f03c040b40c90800c105070703000b0700b00042144190041000740403a90b0050102e03a52964113030b030811901da984c0034043d2903178040c5d401505107080c800503000013401015041605411024800007803403440701e00410084542050006100c1c7c2c200f010800411081800d40c00609146403c2851600b6060b400080114883e6000106030070f1411141e0380103500c0c00d1023242e502032141d0000b005034a0602002aa50780c200c7c3d0380b500100364988921908240c0310307410a014078a4094a59915013820a200101500c43d81c3c0041c4000380c541381c41c02c00f800d44680300c1d2502a80e0040c000d0940075180751a0206c041e40003c040c00300c2407181c0c002811001115810750041c141b0f1035030262400e0421440c14105441040c0c0d01d0400d00d50040c400e2240c0c0c0d101a1040c1d20480f688051a81004499071419604101c030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 545029028 1250 545027778 545027809
    0x9070e090c0306010b041a07020109030f021503090a060501140a17010612031106060117061003090f0c0e0c030106021c1704080d0f0608030f2a150a02090d11 69
    0x6040f000040c032000e80c1c40940207495100704a424400f1208100300038038001d030480a800a26070035010000706075500010000c450005d054083c0045d120991404d0942c0240c80b038041d15440107040a06205080c401c060140825600d001c80272003850000070020001d0b07000780196645c0441c20b205240c2002d40c003c100602003220712500140042c140038004003000700240846000d04400200c0f19840b9444422105410b5004901c454860b0414846007020070080c030401e2658403c0c1c85008108251100942c1c2e0b0b114280f640b085030300341403441149000140024481e52014001400b4481e004242c008950040301423181c0c043d009042c3c11542d2108854000241800c81e44c2030005021802c4c4c010400e01c14010300911010b03000c40c91003411995140b0448811350014420340310301000351401400380c8090680d5a05100307044070f5104401058034001e1415591001d000c41901c4041300c040035502045858085051407142004203610440803c2d00610f00500d8900d81503940c0d8550200c1c100000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 545030278 1250 545029028 545029033
    0x7080a062304030f030522080f0f031003060b0102030a020705090c0706050a050a0b0f0d290c04050f0a2304110a0e0a08010b0d060e030d14071709070e090c03 69
    0x40c01e08010f4503a0354010240b8000905040000c0d510f10640c0300038403408125003c4d0041407c000d500c469016802003204140740f21800c0001d50b0a1800e442c010314014416080c1c61403200d032551500c501110800c03c4c2c07140c195081802040d985a07000300b07003c070480d001a00c03800d000e83d0710380048170806e11442000512961400003800b801c000c4580c05640300d03040d2800100020001d4008001441010b401c4865009540ba40c11070002242c0001e55000359144208982c2c2c002038480c803000080e0301c00c035011741101b28003180030070440c47c2001c0388a200c80002d480c4400414145140250042c0c8640b40e011041400403003800314607283d40d40080310021040042c10b8a0300d003404401030602090303403410b034442d01b54a04089807101d8107114900950304000d1101d06106560350f07441002e04500d07120708440307001c02e200300b5002200a00400a5640744061010302901e001140900280060450400445080c0c0100200e00f4800034404003950443d6950006958038000003904d0528000c080d80e4150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 545031528 1250 545030278 545030281
    0x20414190f120f021302190207230d050327010504030b072d020c090108060108150c040806010e0402090f010312030e0a0618210903150e060c04080c0307080a0623 71
    0x201843d4040d001e0403032000140c0c95450311f0300c0d000b00d80d100ea090003010303015008400103010212600f0001c150240c000b62039044a1149610351751f003036130040343c4031840004d0b480d030031455508403078590402d904400342030403802c01d81551100c2402c118010050014001c10070890349031030030400c80032150400c034600c01d56094040036100945841d0480080342c05a03800c0000450800008906a41a1402c102c01004c01a076031070014010100044c0011125501c1088045071000051116a01914400c04051540d0600c1c0c0b041c040c080000400e4421003103038050040c00080d21418011061000703502e03012610b000c40ca0b03c4181880c0420100030251407a15264806002c40749104140c41c0740906c0015074401032625444401711040034122001030300c50b45041c4006000a8100c00c40400151800260010700c80c0889140020580719140380307440104040000c02020051070710a646c00f43c02401807a0320b13103043e440c0d44403d500c00c01001c154031802a254216002c0360400603800350300c40c0400d003d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 545032778 1250 545031528 545031559
    0x807030305041b0b04330c14010c0914040209010f0e060f0d060302030d020a0302061b0c06180c0111060a050a15030308100e072c0301020414190f120f02 67
    0x440d0311510aa9610b103128003107083c0050030003011306d44401040312a030081c440314500c0840f000c2140704011100c505002100800d98442403180102000c1d0503100d842c050750810000c0198a130074078940c13174400c0380100310641c1d613664071212980400150341004c40d8404072880000300240a4000c0d80290b5000101d8542c1a21502d5040300003160300950a403032200314044402c0b6190b0311440805000340e4060008941201d208030380c10341e0840b915245035130600019158441c02c20109640040d8008444100c031010400c09000b04e90607001c00742044c040a13070b21b218610751250802400d4000083d030360b400050103c1055044503410304080001600f5542c0c8070b241c05408520140c03850304489030300c030f01d020804031034903001280106040c0e128001c00310301a61030240b1000d042c0c0c80d00c1112411080b04160300391401d0002e4006840010130900c580002c280c203019003104e01d00501000c510380501d04000d4005c01001000070f541d40105104550901c1d03040c9240107055141c0c0083d0080c0782d8880c0d0300071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 545034028 1250 545032778 545032799
    0x20d0906050105060f070b040501020f0406031a01020106061d0307053610050d1a010b090102011a150c1f0b0405090a03080a1d0303042a030807030305041b 68
    0x915841103004012690b00c070800d0000c00e000e04100c0c2040407100f003060801240c02c0440c01c5c1da00c01d20400c0058508590b402d2004229042980460301284d100c00122810003035248a9180c030384070030700c000c000781440c0c400000d0642d0459004402001104012180640c4060050708003400001c0d01802001c0d50418080d01e0030b640b86001d100c4030a0100031502181c114494140740119505459900198140402c11508003244801251099103805101113854140102c0c10300900d1200d04498a82d1450350003e4255518080d0440724228411890a0035581e000c103407048041101c450580c64035000a0198a09024001c180c01600c15507010502c034000950049101d1503402e075014800d03600d0341d4503070980d03461031003a005020131080c1e000204075864550101c0a03d044400ca209800e054038181d940c2141d00503074043d2003541018851401c1500e240482c108012800b50720311400740d18685034045c041c0503c400080c01c15031158041001d100440020462002c4150840001c0a59a180080c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 545035278 1250 545034028 545034041
    0x240f03041b06020109032a0f0b070e03010207211103040e010512060601020c010513030b1806070c05120a031d100b0303090109260d0c0308100602150604020d020d 71
    0xc6805800788808202244180030350400e190b8581c50700304c1103034407103400300500700c00c0b03511000200384a601d12000030030b0702d24003507100f081e0140080300107230300380428010000d00e141c0031400d01031380c010842072001445250074490101c0d82c06d82070880c034a00d0352000301c0d40718a902c0701b2140c107480041008520611240103480c103e8204803810f5a0569110b02030340e4944004561242c0582c1010201146c1075014900600182804101c1503094548a9a46580c0400c0940702140d000350903001301c0d4440081042504c1d0405960f05185a000c400c666420750340f00000c1000c212846000715983c01c080d802901704d10302c8400d0b40c00000c0c2d04440d1403074001c1c2e03650b021031001004003400d01ea8600114140842100d046000c1a59008030107410810044102e0b10b04550590061400c076030004040841030100d800058029584d841a070b42880c280100b40c103034054413580451074103900800019030002164500c03404455100012652218000f400a0040340d410200d2240001031041560000340d01c01c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 545036528 1250 545035278 545035313
    0x13020c030403060c022b0e0105160c090e031c020a26040b0a0c0e01030e030405040603080304050d02011e0f24030c0801060503031b01150929240f0304 66
    0x106c00c1d003001040700d00c0c48001c03090044405122814491300c185482090507845440060424518010004808003080d001200b8103840038000d01c141408508803d0050300c007140403500045040292072015007084a000350114212590300149104405000b002080da0203e03a0030500070300d115404140070850941110100c528000060006030071110b14440d02d20720b0310716550340140e001d0381c400c0198001c0408143c5a00a40b0041c040000c0c9941c8038041c0c4c201039440307821419103e080c40e1070058506408003034100156410800c0ca2210f460504810190544481d000410452020075040d4010003042148505400302800610034000504441c47c040300d03c20800340e8511561002440e080765240d00a065041e00b00300200800000c402c565964407000e81000041d101204c402c590f000450540d12034030380e46d0f0300c600d401c10004010380c030011030545014800c0300c035020703403c40012080c500e007001b80141500e250340550808408041074450007420005000e6580c1003d0501c1140e00c801000320 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 545037778 1250 545036528 545036533
    0x109021903050709061107030b090a0302070e130308061906020f0d180e04051e010c08130c170703060f0e06010501020718020306011407120e0d0b040213020c030403060c02 75
    0x1048200c0c42441054820f10059440d91007a07402c00e00e040b00c0544000403419214481c4a4003c004104051001c500500580c001000210150700e00a400c0002ea03600c60300c00b0009000400c19000344480d1012251030341445c2c42d440c42c2c0c0c1d820000441c400f403141c0303422410700c01c41140841d543c0c0e0002032624540c41c403801180c00d10b000005c400c541e030141154440c143c0380c00c4018104561000d0048840e0001e00ca2415600451701d507080c841e04441e9480303182c03107040e91912110540079400032201c5030484180454201c4404485d02d88202d00301051203001180c008030b80341d0313200000041c070404c03025590040c820701584110081c420041c107009951420540200000001d1030340c0009420011501054040700c0b030300d1034502141000b50401044a410301a04030040c9541c200c0b0078006100ba82d2081c510221640402070f401020030440d02c08e507a018103210b007102070101b00c0380c4a070198820f5040311240e843d83d420029a50190060507400c4401740300118002c8100203c40d0031041c0f494865508 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 545039028 1250 545037778 545037817
    0xc18090b06061e0906041d0f1b03070e0f061206100504120f111003020c010b01020111040902130905180c06120a1a0a0f140d02010f12090506010902 65
    0x4200e510f02c00c448500d0b0b140c500e242c400241070341050700034081c60318004003002c0c01c040d030314040d02e14822480700756403008100da07200b081016000c050040e5000106010304a40420782c06040804510001e0b10040910883d00c05120700c035a0b8100884803d141d000e0404da40381c8106d060040c4580c402a5940340c858061810b070390720103600c04d00035541100d480300703480c070300001c01c41d141c4404801010707106580315480000c3c0d040c51034480d046d044001180a6400507501d4141c40c000030300312402100824116410540c00c0303101c21290000340d509031102d04c01d00680e034030682c19080042014941c80200381ea0f00b0035042000d440306175114500e002e40c4007010f4130a01c081c104100112341c810f0702d00780381206186601146103416154048060400408220741a144500700001c80306840b0341c1c08003d00c180c00b50f1040c402404422140070310010151050140b2485640c0042c11a03047c0300c51150402010b129815078a0119803c92218150010107483c40ca51315002d1100181d406041c803003810745907801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 545040278 1250 545039028 545039041
    0x501020111070302060711010f050f090c031501060f0203190e03070605030f0a091505310b041106040f061805010509180901020d021602190e130c18090b 67
    0x20110380e22983c1c50380c00780c9660b40c0c41520555000302a007043c06010342da180983c04807000d10348625806070000c49904034443c507020091a1130115400c1d0300d42e020380c020ba0f44081c4140320384401241503d080b400e00d03034094146c2c140206d246000d604000f101900c0d0603080f00007071503000000e00c000130400360b00b5984070350f4881105071014407081d5062102252141d001601200090b840808a18414880201340c0c07500e140071001912810f803001c0e0310804121800b0314940390403600c60051302a008200308030045560b21042a50b003c000d00c00341800740d941d07902c045d65031340e810300322009081c0c00740c4241d403e01d0700d078980101610344a8044044a01c4444000714066010300c00340c40c80b00700002c01c6041300b80180b0891a80c6024041c01440d0190f40030310500d0b428050a00103080081d034080ca003c0601c0b101401040458610342c922043c050240a80074406540310b64021540140c503040307410100707041441c1160298806030f0001640c200c2014100c0c0074030b2280d800c12030096004041220b0b26031900c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 545041528 1250 545040278 545040311
    0xa0b0f0a0c1b0215210916030b0a0c230d1404121404050409060f0b040213120c26010506040c1d0f03030301030f061b0c08030a0e0f030405010201 64
    0x2c52041c181e0300000c0b60038001032800c5144c1c500011590300280781048807002c0b01d00340c8040111607101c1000320714810031a803e030040104072501c0d0400d150740c80e886860b41c0c0b030386141030102030420283c26490703d088152084c01480040350380300c0c182004800703c0d43c0f000300d100b216800481c0010741e00e40c104411805e001c0030070030f026405150841d40340c550a000300344003a074407034520b415150b0561905000004d01c0d0303a40e40c4a00042c40d0300401000c00d02e6034074240d0843c1214291107840d0f10452051110105140088030508286c40d03003154507003400d08403030030050041c5c48607034031500c05c03110240181c3d91581c0d58000c1c070b10f10500d000c0e00207006c5622403000700400d4030200c4003000d0001d01074a541e6112101c01540d02d0b00308400180031084442e14020200c0e0071507109070020344904008440e0507041141c24400c0f88500c0d1100002242d003004180001801052044005400240048003084140250f03912654040c0c560718110b4000c803200e45443e98580e04a0300c6880d02551030b0100d948102c07881c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 545042778 1250 545041528 545041547
    0x506090a0b0604020a12020c0703050105010f0b070210090305120405040e06070203190c081b060c031306050a0f0501082103040c0506030405070911092b0602030601020a0b0f0a0c 78
    0x801514041d035154024000250001c017030030810081000003280108246100030070303451a2141c0600a22400c6003031060035248103a000400c0e10700754001c10000da07400b000a8408a40d81190104007030b10b006134040b80d030041d940e04090054025054620300d9807200d10010720444200b5182804680306218000391128000c03104171025810410201c100351868800f90f87c01541c5a05010b0411040c1c5d44500b040798116807200c40d4a81a140d00102e030903a02001180e90046000c003400e03181d46001e07400900711948095005020315224400304080d08980d40010021040d0510200415070395000c03415a2441040041d200c2c00046007250785018907044d0880340f040e03400100d003181e85841c000034070049a00c01807060395a03010340701c0040fa601c480f9014a5a005c09000240740c1c1301e0a90302c0401c160751955001000d02e0184d020301e003940c015002c9940b011415000f0000680300d070f44981c0182e05080d00300030b000748011041c0040000440c03418828a01075800300c0c2c2c00300881c101512041d5000c200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 545044028 1250 545042778 545042783
    0x1f110702130b0102150a050702060c03070c03050f1606151a0919050607110a0605120402011d0d0507090f0504051e01060e011413150513060b0a0503040506090a 70
    0x911030302080744441c007a0020001c0c26010b104641c8461603240d0000d600c11402d940d0b48001d41e40b110b0500514503410030050381c00852030340c0d40307516500700008064421103800b40001c05111020410340c03074030450380007583c0a0040f05514031440d2840c51905c00f00400c1c0c1c806e04030100d40515000411582c0415950b2281e03d0309a54501c1c1c6030042c0744003000050030240044a1450110a80100d8a51a104050300700d45124984204d0300d04021410071441070031503000390080140c03e100569401400060340790308260203007030802003005140304001c96100d0801c40c90740c00411308000d0004000e00013869004445a201e010403800300b009458005440082e0380280182d4040f40300d80c640088103041e904e2081c1c484c103000061241d5582480700303042c10242d0000800003241035512400e420482e0071004084203c00c01001403001ca041c3c150580c00190059070302591808401c00c03550041b540c084005040c44402d280d440320440480204640d100b01c82c103c071680030b000701090301800001008009640e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 545045278 1250 545044028 545044039
    0x8070c080304020d080c06011a09130b0d0c06051e131a09090a090219032003030909010305010c120513150b100818030f03070c0309081f110702 63
    0x440603152162a07030005081030381d00c411454507180020b10500f0007403051480400c0585070941c940103080b05040000e070092000002c0810401480c1d41e0740e8082040d0038482c2000000341c101081d000b080308030507095802000b00842c224042040364200029140038210b054072186d800c18441c140d01e0744c030f0180003074615200941500a10084145030b81c1c120300d0284482d4a40c0c2002c80440006014100135142c1300c8480d07554240e17002c19410501540205400d5490820080354036560b02e03028004210b1095501c2c0084407025400f19503002e200312b0740003590050403080c0710f503180c0c14414001d180303150001e80400c6041d80c40514215541c0a400d03c240da102c3c032241054040b41e05c808034100030300740c403c0c0001565445403082c41da031450344810080e100799030b4444140c40c0180101524500039500421035078401c0c49119192204913044030340c08100361030040900b82d0302c1c2c0340644042e02d4640114085006aa018684803000d187e1450010742e440780c2d0900010f101c09c1141d100c1e40c890300c80d0203508032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 545046528 1250 545045278 545045297
    0x8030403030e190f0e01080a1110020304050306010e01080616020c0405100302091602060c070209060d03180801051e0105130b0a170a05010c030b06040603050c040b0403050d020d0807 80
    0x41c2c0620091080920040c04091900f40c0000802c001c80c10190400d0f080c042c0c4040d03090021000c1c032000c0e0f0340074152501c01051a10302c0c80e154001e2404160f1a80f501c84c00b03c18042801300352090003a2401004c000e0119600c55860f10355000840000f40507440c060720508000600c861401a181c8092a80d01c6d0042c1150a42d40d00511007d070400410401c010098210000010382f03c0082d2544960b5140342c210b401000c00e084020700303105010709071100418090103140007580d6003004458011300c04840386004000341d0b03d000e5891120003506c011152516250024a459064001a204500002441030924021252110000400e00903a40c04c414a1090b049104000b41c0c8078440081780103009101071645c80e5000170200404006540c1a500024596000c01030240101d0443d17035640d0070207000c208440e2010540381d000d184119003c160f21503012071808501c050480d030160104441c941c0d42c494803400c20715a640a541d01c070400500c6070f1021004024131440502d4040c2030955030b1803092 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 545047778 1250 545046528 545046533
    0xa120c020721110910030b1302060d0b0901090e0709020309010b04020c0a0b090303100603090615090218030d0c0201050f13060818011a0409020307080706090503060a0c0e010804050a14030d06080708030403 90
    0x5554000b442c5c031051340041682369002d80e90702e00c06007458074640180444e8a05c100402e101d0241010707400710700d07c0350030041c0903c2d0044010a2240036208415001620395881640e124054440f00642c02e80103440044e0500070194089814041c090142c2c07010f0701c943d00c1c1c95646c03981d648011039a196551405e008203100c0c0a00c81d0300f103825a035004810114807240c10042211042d242640002d510603400140000c007940c00035107070210002c0813405801c45000340d1802174071700d8010b428001c0c10400d0009841d04c45000c41c0099074084c0c0c05603011030b20169101c4c40040e00e10310007610003100c122029049203000210500840200a01c1d20b01d180800352251400d010140c6406041240d02d80134080380414882806c106090041039155281c001c0349180409050501101078003070359005083c2000310100b1504107072640c0011100380b80c0500c041da1242026820320400000083c00302c50f04061035400c9040003c06040c06c004041c030b00b080700c259221a9195902c40324410107902d9041400208003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 545049028 1250 545047778 545047793
    0x2030c10050405030c1b010e01140a0f050c0105090102030601080a0507022e020d0c03061517060d05010504050105070315080a06020706180c08010c050a120c02072111091003 76
    0x300a4841c0f02240e081440120030a0300384550f101030550488400c400031181d540c0d00c42d5154400240a080000c4111032a901c820340c06d104041440092003a8801c00002c828444c104803030140500c140200800e0038081041e5020398025550640080c0203200171824407410303441854050021500109414448024010321083c080c19002c8113040c49a407003072880f252540005c01003524000c0b800100c000c1c1c0107101504480b4183c210450408501d41d480c068590040c1c0940310301020014248441e5071502d00140f048016890010029420310040c4000c014054201e07a000f03070015101442038626114810440b04504e20400100d6801902e41c032000c50341c59070040007400d0240381d0109560490302060802c8402c048011a42240446010008082c080c407a070003490006d40751252508103040703401050442a000014041030355242003100307079402040744400500401c2c0c808903903445c1c50480105446a078460035584c00c1050a4001014504103500f107110f01c4c0d092411094043c00d5407200740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 545050278 1250 545049028 545049031
    0xb0a120b061c1416080601062703030807090e070504030807111507150c080105040e15070e0a0b0a05160507030c03150b030c03070b3106020d02030c1005 67
    0x98201094120790040c0b003001904003107100b400b41034080c92403400a030382c29103450340480342e991141c0060641405940404180641110040d180281c0c441028003c030f00c1e43c000100e045068056990b00d000010980c0058425200d000d0546404e034101e079651881e4040b43c10308941e0140040c1b402c00c4280f001a8000016002c0301c1d0044011910603001d060100d68030b00314000001030242e4021a6910410241000c03280480c200201c0c2400910006070015080017418010f5610507521080840c0c08004100320800b1941940d40c88858203051800000d00000050b40002d402405d6610004c80c241e8100021192091015560180340940110111300b81e0200808200d940d40541d080c004003040b8200d00502c041c50243c203482200c0320464140304201c90b03017a0f81082c041d801800c80380d05607550100c2d0701d5040b24030a040072580d0341c2001d10707203511745101c400304d49010809100e44440c003481001464025200c480d0200e481ca800a548180c0e900c1c000c0881c1c84c101d942c090340040902c80221380205 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 545051528 1250 545050278 545050291
    0x1180b0a1d06070c03050f0c090103030804060e060106081b07050706030203091203040516050915011d0301050a0207020117150f01030216031e050c06040b06220e010b0a120b 76
    0x4006544401d0000e00d299011502c1502c0442d0030310014018040280584c0442c22100c1c80201503860100010612000c0c1c14800502802081c00006040c0501c40d00107501038001d10303060314a02c0da140c00b8003500c1048255203d8244403158183c0186148149080f1140b07a5009001003042d103240c0142200a0340c0000d107240340e903007e044c003001c800300014800307180a1407040001d80395040e8903009202070000c0702e600c024800d4a214050002c50807070080c003410180028a04820503140e1000340d4903004241c180910f030035619080070043d607035010303502030449241300341d95001d1100070608000d0a25102581d160129080845400d040c600d0240000005060181800b5042c070003d03a006c030550700e00c03c04040d000300f8140381401801400304203c1c1c4c40c0103c0341e41445410909082022680e81800a20013805114101c020641c540c1c0c503102c2082d001e40103c2c2c10901c0001c1c1da540c20030060304002040103451340c2424905100c03807074119461400d40306040040b07015890740d03440386840000c0c0a01760 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 545052778 1250 545051528 545051567
    0x2307020a03021002010207031202040b0d1a0d030203030406050912032208160b0a0507121a1c030806030102041518030209160801080a0f030f050408060406060501180b0a 74
    0x10050300c640c0490f021401c403507000141c640c00d50b07080c05480d42200c0c80305c44a085204010a11140e4440e005641070303244c1011000a00007448414020f200e10b2612940d5407210018200c2d204044d400001144110f1080000b88081d0b00c1c1c4171240c982d11658180000a480c1c000d00000d41c42c00a00e4024000014a00c46218005011901c1c1c14442e81d020546507028214029402d101b07110b0f1803450b541d0428a800d104000c10702e403c2030000c04450f11204440850703900c5044800355944010f40d1040b00c030400603c3d08004612546800480c040d07903038030490100c0d01360b400180d5185010301c00e6a00302e441051040000440300c0004442c00281c60031030740100c1d200c150012002d82c4402103201c5c410804408112000885900080c0c25083d05074041c00107540a040100000790b004d1442c040c2079941030802c0030040d0030007035054480380200c3d00300749480d1141c523003044140305650701300c3c0e000c03540e0a881d4912740301d003400c80803e024174150007005a002020090003560b50302c0b407181449100d40c0c4520 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 545054028 1250 545052778 545052799
    0x112805070e010905070f0e0625020901060c02011206080a08031e0a0c090f0b0d0b060d0c020601050a050909211303080d1103130803060414040b04050706230702 70
    0x40a1803039142070b080f2052075680d0f9001c0000031500104050703810b0030181094091500c0d00c0d40001c4052203040030000b4003640d21240796511155a110503001c059005090001560712a90010141000010280d00040040381c88103800d0245200c4c0000740c4207090003a20407280c19803140c42c015803025201507400c2c4100c11480994003030703001a0501230561079202041a0050f000b00500702004c42d080b1528006221f1000c0000b10043e0048424110302c2d50408646140280c00065140c06030f03540e0500305600b42502e40407110703408103959059441c121400d2404035210028440300c80c0c0101c030030000650241045850540c511a150044150b250740b8107032400c08800410000a405a8422110040c001c650b00131407600c680031f013501144131490182c0c2140340c41c4c3ccc010004600c0e6034502403c42d000002c0814290b403140d4002810000409c41f528800307003032500e4100d48840007240c0907102c50050040102e1807600c114416004040c15420441218545c00c107002c1d81c40c0d00c0503004a9105032501c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 545055278 1250 545054028 545054039
    0x203011b0306060e0306010911070203030403030309050d05090d020d11030d1205070e15070305040f030f1109310c0b0d0b040b0604061b140d11280507 66
    0x38040300080302951a0361180304510000e8196030481c0c21250034862028583c14058800280c05070458040702400f1030349845c0340c408070700188282e840282d014000007501106040e059048860024429011100159944031045450740210483d0780d5010080441d07642c0985006c0c1d983c4030805014084806a80d041c0c18000307407408154a0300600800c4e05418001c204407410300c1010740c402d80908100b1805d00c949400200b941c104180381003403030700020490109041c45001640c010740050441c03110040c1c1c40e400e01000c0681c1d060412034500309090a19900d6040914030203008010b000d500008919281287c103002108010310250509449500f00c0d01040320205120010000c2980140e0745030020f940340f005035a1031245d01e81c080c0341000540607450315807008450450f8038034600403200c03078034110411181e08c0d03019602402e088094410403000c0400842d1291122690f5183c55107118031007030080b515003100c0c882e150f02c80d80c0c03106611980015800c0070361108030300c07034010b030340140e901d03407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 545056528 1250 545055278 545055281
    0x10c2405011203030b19120309152a03141b1204080607050712030e010e0f0616081003030f050d0608060f060d0b1f180c0305061207050904030507020301 67
    0x240e1007403040804104288040c5505803080700d0707195105641c4111074401c84903038258a403000c0d07c80d900d4401c10b50b450440506204080d40c0002c0c04454a2002c1c000f40d20540040c580702c00b08803115943c01041d40c050320f82402d107146000e09241d250301e841049041070341c02503040e40c020141c02c000e04d41c0746030b008a0030310348240600640125082c0400f505d550031300040da427401200418903800c1c06401c000010103e0080c0344000c00c0400f02c0c2c500842c01c0001d42d241107000d4020160070120b20300c650b03191907428030340c00b041f030710f00c602080c00b0904280c940312881111001b2054400d40c0d5101c44141c1c1c1400400c0c440c5540b48100d440f0350800d50726213950600d140044074101d44c00110301c0d4110300184268244440c1e0780d190400d80803140e1102e805901c2d00c1d01070140d84058200d4203003a4441006803030548000ca08000200220200e028144119062540c05044010810000030b49010001025403a281d0f8515400703e500d1030042222078144014020703002000381003681801001e00070100165400d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 545057778 1250 545056528 545056531
    0x906040c020f010f050108010b060307021b28080d03020406050d02070f1a06090601050a050d0b1f05091201060806040f0611030a090611031b0304140d210b010c2405 72
    0x1104c00040c1c0f46d850320407624210780c0c12400c40340c0710b94400c00074401542c2e80007072803840b03c900076038158640b0005c07c80018100744005200c404540c000c842c011a400c2c030141c2c023050880d05241b0950b00c00000f01c1382d040f0308922580c042c032030100d64180b00001c0500015070240844034464001e103201000d0340d4231002203160301c0d8044841c0382840c1c02d08122080c00d0101e08650846402c3c200541414550b0700040c0040c010390a4107001140d07281910048c03660f903581040b2480c0d101e107003100d820003c1c2103c02003065100d0b10f02540641d048800505000c441449003800b200c000300003911280e1034640e201388441c00d62001c140c5117140c540d04104046c04c401d6005601803511004006011051031034104103a40c040450724103021001e0042040541c5518009511045115003107581d0b80d8941c505940e150081c420422901c0c4501e40710711640c140c1240450141d0040142c000299100d1180810240c4034a801c0d0b05002901080526001583e20a1200c010040c042d00818400580802a600f110300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 545059028 1250 545057778 545057801
    0x120a060e07270b0402040506030c030601140c070e011401021507050403081305010f080f0612150f06130501030c060e01031b0e010e0303030f040b0613150603050903090906040c020f01 80
    0x2141032041c140c0840320b114600d0300007011355056042c01c1c50300b80042c40c980401064a41c40c40000000509143e10800c0b03121406042044481d84170b07904001131990314003003409400740080d024400410b1045045210140c0145c05a00810440344055490410264090150018440c0c140310100000d81510090110240d00b910441c00c428600300c00104242551451101403010701414000b070300564540c1c1e298829015624500c902d220061308624007402d004202c2242c008100620050a9071500e203980161401c50700d464070540039442c12003c540c028400288580081c02080000a0055910450a00050400040c038641c040784041000800341c403103000140261041d0740c0a5a000b58140446e640164020360942c03038800b02113000860090006072000c18440001885655480c0c0b80c0042e400b08004103001c0c3d4501e2030583c0c24612407600621000c0f80c04c000014008180c00810346400c07260007800900d080d20b411040c88000d00a80c9402800c601400f0542000d4090900420244c2807 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 545060278 1250 545059028 545059079
    0xe010902031608071409150408030723070521100b12150a05101e0e0a0e06060f040e0313090c08040c03061109120a11120a060e07 57
    0x40c2c0548820036450a0760b5510051142e05418081ca00d540068000c04038010103854554400702d0f000010654032000318442ea0f400c60001d4085800c2c800400a030103d07922825000e141000c1004404484c40300c0400701c0300813075000281c1040245001520b036807038540c2e110f40c071103c140d0202030711904143c0c901c5001c800d01e5845490402c0c450030071218107486000000060000c907002c0c04061000f070a0003900c1c440c00e03181c544020581e40341c2d00ba84e01400500c1d20020302544540410381d0380ea0340c443e040c420b034000203c01320002034802801c2c0c0601895100301c10058007030340c1c0d240303000c01c00905103001001e50401c1c1d66010340d001e0410200000c00064800e41500d079505440d090700c1805a51704444140704008500c402e200019107111441401d80c0c1c0c2c02007000c511802e0001c421141130040c00c49080c0d105440c400f5030017180307801080c031244050140d0b20505003101c9010a001c4110241c140354a540d600c034204003001708030568031942c0c03d03a4010301540c0b1002c0d40d80400d01e403d0242409906050b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 545061528 1250 545060278 545060281
    0x803150d0501140f0105060d0e010f06030b010923040807031e0e0909010212060d0f0204020d090209060a470405011d06040302060a0210090602030603070518040602130e01090203 78
    0x25100e045603803001d040f44818a030382d8101b02c0400c8103801030f110042071003911200c04008202c3c0c05c0d0400c0b85100003203d810000f0503501c0c28007003500d1800b071080e02c5040749400140c0440440c0140c54082100c00c0700760102158640b030340e50b1002580054800c6c2c0c00c201003c40040c02002c58550000042051590741c0340c92108181c0400c51403100190410180ba80304000712450704440c000700c150300c100104c5002c44409400e0802e2001103c0c0000b00a500620003c0d4170303003156409601981c5400e0080d580009240d5410040c405010902d01500300240c0404456250f04081c4201750845845030741c011954401c0e5400c11101c600101c1102c402d0602d001140c1440356582c481135810690440c0c9940ca40c40070702d2207011030a0f900c00c0e070101030300a9200160800b4542d008200381f102584117402e0070416403082c0d081500094205071803080c030038000c560002480d8a0300703800350809895122103250302e60701d41ea90382070000d51080c5120781c074400100c00c2c00101103640700d00548c020300b001c2c2d8004d6a40d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 545062778 1250 545061528 545061551
    0x1080d03060602010e0c09070519051804090507030b06040e01090606030515241f0207230102030d0b03010b0607061505010c21030b1e1215040803150d0501 68
    0x1601c420750409800c580c0b6204404000d07135800101603466141c00d603103c031029212403004072030364800c021104800b400c0f0a81301c0c0b8011684040244146050740506112600483c01000241c0d002401c4c00f400e550b022050a00203c0c00000180d50003c000820028100714004203503400e60703401c1311040c0e40341e0759590010001d001052001000000001414034028030306200c110303c00020a182600c06091f00c440d1503c2c031500c4070500e009451001d0b038020040030580d12402583e03089203000700c0c1e031404c04103402d05d4201440c5c010f0305111920144c002d1410001400c010300700900441d816168190748400000c410364a0301d030001c00304035009985c0418031003145200b84005560b694860340c100030940d040d01020030a0f564001311005d4035420f01a80c0c041c449407049020380095460b0039804650180c0c00c400f4240744801e1120400c0c42912081c1c1003070346c9014195162801e4a440044050400c40020000703445540255405140307030b0507000c15840b11201180720700c0c0d42540d003255680c1d0741c1c1c100c0009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 545064028 1250 545062778 545062781
    0xf1504090c081011030a0507120608010e15010f1e09020f180a0b0d151505480f01060e150d081b01061d1905040f031d0901080d03 57
    0x48200341c10030140100c41c0d213003051a0a40c84010a0809400c0d919404600d05901c511000304444254a5040c481e40c2d440b211100d0090801c01c61a081c2031207025104e01d00c210002c000f05040b12110f0a1445219141c0350380030b0142c0c0041a4502448003561001103000340d03d81c4041c00e0300b407101c142169118913052072034102e8800c40c1c80401e4416050014100800002902242c11191694002085420f1035540b440415204c41d0441c11380042c1c0d076641480c00ca540319019000318076410504140030040804180041e01d1590310700c0402081e0301c2c402010016400c5600c0030001840303c00c50f10000c401c41c102c01e003101c5641d004080841003a0b02804044440910904081c80301200d071600001042e40e500c04107807144001d250342c0101d0303504181c80740c90001e500c880018016505601c608102c040c0c00c030308992038110313507200254520301c0e007048052400c0d1188900c141d134406c0c07009100789010f48003503d80380c1c00b600303d02d0b1031032008405480d03094580241c014000d102c110021f1550f48407103030000c0d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 545065278 1250 545064028 545064043
    0xa0c1b0605030619080a06020d0b10021f090b07140403080a1806020610030615030f050a0203190512070804240905031204051c08030c03010305060f0f0f1504090c08 72
    0x3d101204c140302c01d1113030358000b08078070080740d5010300c1c0180d481103000030000140031803051030f5611465a0405032411a000304545000c4640c2208000005041c0da03c0c00003229000c25000c0d00d40c1011100284080340580c0301140da4030041c40b03409081075074a43e11016568002c60f101d000040749104040354400d0701d1100e4001402150018008919118070036400e0504d00788405410b2645514007944012003110000e8040e40e000705402100c20081d00b011036686210283c01c070300920078000e16015840c00740104803d10b540c4000a080351900d08507560300c41d6006008155503001c805c020001d0701e030903410200151940071400421810051541c080e00b070044640c0603d00a81041c800b86565500d0a070450701580d0f0210b50860079408290702e200340705a02420010b000210001c180034100c2030160103141244d01c14012511581c9e141c8040e00e03031165003600c0c036050010400010500c0b20311200f00465000f60760111010b40030059000041c244c5800050a94415405d45821b0112480620410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 545066528 1250 545065278 545065309
    0x10801060e060a0b1e0f0a09180207020112050901020912100f0615050c0c1c0b1006050304030e0315010f030c0503030f04120f0f11030d03050702030a0c1b06050306 72
    0xa00f40341d103800004522441002a50f000d1540107518460f440c01d10f000584e03da00d207071020440e031038040136a805041d201c2d80d4062558541000c3d1a03800c0325015074000c44201340c0d810380d508058480b4929204c4040d081c05020409595000c1c0300300d002d10f48901c00e00d80320360191600102514100903803035030102e44030f104100254508000b000c2c0040c0034500e61a5802c03481900c0d001e039036105d0702c0003075a0a203040c0b138090903405410800d56600c48840403040811884c001e03140c0f02e070380e500c62115080c110402c2c0c0c031503400400c00600000380030034010407a8198040c809000d440e2396404100070360751500740c00d80217900744150600051060011115601c800750000b078000398682814070980c2c55540c0518850105204447c1c525001042803a0401c0280e00c3e9104003c80705034a00b0f031800c0b2114110038000280a4415410070715001c510074050340d80501d10a4014501d840f4440b40f00700d07044110100e068640141e00c1d40344004460110580301c2c010145961040d88900f403007010400031054001e0301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 545067778 1250 545066528 545066539
    0xf0c08070e10080105060d020f04092009030a061a130f0c080408030f07121a040e0a030909180f05030a17090607030c140a0e010f090321021203010801060e06 69
    0x82c000c0e85821100035410340c3c400300c8042e9250303200700001c800a44540280108102400306002170f600b019078010100706c0c8140c400b5284052403c0842c11341500030003140d10340c19409541c03200081411503000c06060040e04402140000881003c81c0012442c04149030f240c0d0340d10541c00500c141c99200b1400c068603540f5159840741401c3e2240e00c498000945007907007858550001c142258098070040c034801507135807018000300c45d1955040c080883c890202d503000b90308014400300d8400c40480c1c20003038290f154880b40212400d01e00c0a0000348462584625048114030a01002c10030860320301c0030f510710480c010340d521000c0b4000286030420006111009012010a00078440d9000c2071036030380300380c86107000100c01c040c00c0002c868100f10710f0071010071503034000b5010303002032f9018048200310403007038a801d4020000d01c1011a0650380510000c1d0103216404014052500c1001012201d40b19500c1110300c02100140742440591003a48112005d030340d02c07a01000840c0200d0a100e0f4001000c844 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 545069028 1250 545067778 545067799
    0x80c15100f031a07030222090c0806031908160c0302040f050421141903050f092814030a08090c010801061b20011b21030f0c08070e 58
    0x12003c840304000d10310f0705450301110b00026540382c40380c0d0646840d0f05010356511580b0005034400035a4081600074030b40c0c141c0c100140c40c102240151001406001c01078020700c9151031290000141002c2140200c0b00c140080107006800001000000701d418080c003c03a03010f0524520400c812100e04082c804100e900703100c10880803c2c00403016000308051002018040945018100c41c0c00c01000a0070400a00c0421980390320301304030b548002c5e211030303030380301040541c5504040741444802210346100d030f070b40400020030004808030102106511010841d1101c0d003526039078651203450355510041c003503001096400e0f0f0a035000340c005400900ca5400f03080c0650141e00000d2051a050243d003042c02180c02d01300c01c202d16079818003594180c000300c413581640d558401140100b000c0c425202d0000d101d17050010603074400d1281740c600a940c40b401507001400212945040c05500920f2a414140c3d11981200e10f000130f030103403100072403940e030310006c4034a400310010701325140307410080d4000c079602503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 545070278 1250 545069028 545069033
    0x11070906050d14010609021912060302060319020405091614071109061f03020408010b01110703110a0305010c030b0a17060c0306060705070f0e010b0c03040e04080c15100f03 76
    0xb4811001c9800844640b0040150160319001d00396960240c605c480c4001019110315149408201e0345600b59503420010015100409040c0e64581c000030754448020070205949000300c8840c80c4640143c014003608180e6100005024010100d071114143c2c1c03050010940c2c0d1640c000d1100d01c0480580e443c29081501549450f01ca880c102d031003140c001d03109100400c51580d2080c4000555807140184500040300d4402e00030080e400901c1642840d41c00c1034513002440d802841c0b1304454804000091061920303540b0b0b81204990000c2005800088510011001c91028011100940700c241c9020407040b2490051103070000b0f030b070b9100c040742040507a0780510705407011604542040400c0103994980d00c0b19400649035100d55031000f400e510551200017100ca0140080c40700f103c200b040c2c080601d0f03984545110b007a10a050020400343c00403c0f0510915000e810300b50f4000f03004003900390500d117101054500e042030300b07040920b4010900c410030007440c60002000002e0184036420000c1d80b40740d40d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 545071528 1250 545070278 545070289
    0x9030f040302010e0d2f100c122601180506010507020405040602130905010e09010e070e090a080f031015051e0d02030705030702100501140120010204061107090605 72
    0x50000070304200030804c0900b01d0350340d105914900d854000c0126003c2400d100f0708801241c42c403420009441d418204100150310b0101e00b031144509003515920302c8180955150800c0d0b00450307903110309011021002c0e8440c090540f00e0f4100b5411442c040c005154100601401c9409a9844a00d540c5080c1010400c850b6841001e0715413403603054601140303688862400070b001e03000d01030b807002c000800e8040004c0c5011140d0412812200800800e002c162201e004c510b0980750f00103d00541944140b03000c214231601411420b60043e181c4c0c3c1500c90500c09650f8410300d6900440420591074004410b0000b034000b141405002480511604600c00c00d4040780501140141d038000c054002c604048005100002000c8031101c6450380310440d56842c0c44d4601410581040d5a802c1c0144200325400c507440440c4e100d51416100310318400080b0308080001140c0c60307210b15800100c82e010304d10300880d03900e1090010b400a81100d886100c0c0c0c601c0000183c070314140c95030b881611110304000c001c20054480 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 545072778 1250 545071528 545071537
    0x50715080a0b060f03040309090203100f080c0f120c040c030501030209070e0102070b090607050a060509150c03040602030612071412070b0f0903031201090c030f05060a061101230601020609030f 85
    0x4c0d954150307103a42d280d090a4883c80200d9004586080c000407c0244100041c82c4010a8030141d50140600030344031341d0400d1f0780b40445055150000b013040d0301500945804000324101504c640308650201031a8000b00b003c2c1e03903007071107004082134490300144218508201e00d03a6110a00f4588600541c9003080003d40e136440d40d100b0660504c070f00141c0101c9a86030582207401464100341154240012032600c900140811030b8082094020403281c0700c0a0700c40712030368038000c0c4100a101030071a192030b26850000d510251940da0302c085842208080700ca41400300310000d0104c00407025294120605010591030146c0600c1c2160300a04d4050110409000507115a00d5070030850984900d410404a4030b9440ba032800c80d02180081000000e64003c907402c030040d550743c2130390184906500c034450305c011740301c05840240c0c0c05001c0c4c0c282442242d01c216540c1c41c41401050001c501140500c004041152042b0081071009602d0402c00030a56010061141c0061540c00114a4000f003101154464041c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 545074028 1250 545072778 545072797
    0x501180b0a0b1812150613090c0e04050f0a050a0b06040204030212010c09092c0c13052706061311070f0b1008120708040306020a02010c0e010f0f110307050715080a0b06 74
    0x90240d208000e00d00030390050b6442c582c40342501384800e0300c0b880c84520a2b0001c44040b2031500c1546032403640c0301303000b03d20f5500c121341c02801080c90921640d101c1601040c006c0a0f070f90095402d0000201590f0345814013200c11008100000c0c201041c1140145414000d0300019155800c100502c1e1500045003004c801451100054192840d900b100c4103042881c42020181e0103d0140c003041e40380b032603d070700040c060b8450000007841c22401e01d19440ba184003507004144990007690002d011410034446c06000e0b069035090016000c60300241b1307000c6503001944140c4003820290009010025002030039a0060004221840c00c81e10304a41c85036640e01d4011001030042c00455410104200700c403d03603010f194450303c10340d100c0018400c000d0003048018000c0c00060a0000c2140013940a00e0640401c006156200121041440000c1d40c0c04000c2d00a0350755244010005840072500a10040001d0325011081d042c2454041c0b80003403030390002030041c15019107032030880981a52054202e510720744 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 545075278 1250 545074028 545074039
    0x705030106170a0b09191b0c030f021e030a020c040605030d0c110301050a090b24010521040302010203010e0f010e130302010b0307030b100602010501180b0a0b18121506 74
    0x1035801800f08098032a00b44d441e5008020481070028464400062a40c01e050040d010402d6031851101d62540e958542c2d20b0001003200b60961a000c80d210300c1a41c4c201510318011100c1c8200028450307000c000d00c0c0300f503000c0141c0000c1803c2001a50500880c00d07006801c89040c020700c0e00b004001798031100501c0390301c01440341c044499410003c03c01100070700e810008008001324030b0309894010113444000411584001403800262601d02c0070003440c034000b0300201c9a002c144104000643d0140d110400c641550f092440003600c0e440c0e81d82c8030041c0b140f8400d6001603225454500c0740e1480d05009041d990320b06c3d04001c01403002034155810503510403076881e00e2520203811414280d00500b01c08a90a0f0180982a400b100307008081203003c0c020079910101a044c56507030a022401c81e00d00307029081c3c00c4c0c02d007081080e014071403a030004030700450000d100d60102642e90b06050f00d1a80200c48201540121501c200b080d407809000c03041002408601034640202c00d102c80d000342c0c9000410a034880c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 545076528 1250 545075278 545075281
    0x60f11032205120d0b28140d06022d0a050a0e0f03011406031204050a0b0306031e2118040509160909050d17130813060c050105070503010617 62
    0x7000c00c000a02d020f51440390300c0703540c49564602060103001c2c4508854000c81d10702c0c000440c001e070510b203442c80e020f032104c0d0402c48640c00c19400380d0449034600316855100090a031940302052241c070087c6040d6206150b001036180c00c40310341d503103d05150001011545000d10008082540103130486035491024a041c003881c4070310b080040d90341903883c0d500c903402d586000c1603040c4008400c620b0710b000d0f038003c8044808081100341c525034184500c2c06655040000c0c1402044448a214081c0d5009140101500c0c40ea10b619448558030514514440c015030740311b041d4000480012482000250100c51841440c01e598450540408801a02694069562200052200881030100007400803500c203007611260b5550b1003a0002e4080e4480507207a0307025034000040700ca801820386101c0102d1074446800c80c0c0d996031039000c20b10700d000e080941c1d9840c01000400200070003810848007501c42501d44242d03001003424038608480f001800001480401c10042c000c858103ea01240d032461300e2105102107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 545077778 1250 545076528 545076533
    0x101814070806010b091f0804030201060905090c040218030f0d0f05030115080612060c04050109140102120f040515120702010e0705040f0905120714010207020904030c050f0a060f110322 81
    0x500100c54030f400500c0c1e004106c1d14061362228109005502a03402808050780380c810341d400f10758080e104400107070b10800744a117481c00c00e50050320390b0303088150442a01d05000c40129003425514000040545c00012041640d150000d0260242004c2407402c80c0c2150f06003c0840b0380360a4070134034501446880800504a80d483d6840c48208240c0b1005907580d03810842c02d0640300f50024021940030a407158408a400e4514942c1002c41c00e0050740200351038504800c01c030b9456400012040d0350702404010204580e12401d41149030004080c924940d030780910300380c1d40d21048000d403a00c01164180015450304410014031201034807012180020700d183c1c007044800003040c050b40d000307250303004244001d000c0d00d0915020f8030030325000c0c480b40144054028a041c0c06c03846120002075220160501240201e03200f00f03120101607211794202c588018448541e2841e00c180c00c02c04031805a154688a02180c0b103e00400640000301c0c66050300318100000d80c6120040304112090798100c0d120703000000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 545079028 1250 545077778 545077789
    0x1d0c07080d1d150601030b010c050c0906060409050108030301150e010f0f090f0b03090c0307032006040918120905150c07230411030402010804020d0203101814070806010b09 76
    0x20024000421104404582c2016008040c42213660b1804280f415052092650041b54882e8079140c1c000054500c004d05401005501d00c40a051150051014031010440988521810703010f05450030040d80c4a6242c400c540e02d03600b4155403d101041014010b0356401e0340c2104041c3d112848500f042c001e42d5420f102d046034001226400140c201d02c0b461400541c61038040c0045014a1403e0103503902c0840320303010300d960751300d884c4002000c08058104241507416800d01c0307003410500050000c0c0c609a03469a1540c02e51f0101c09070b1940c0c08240d08854410405010402022840c6904041c0740c01850000010f500aa200c01300e07040700500080c032201c02007030034400100030708150804119034400140d0900d507110001d0401c140160325281c4071100b2003114105580c426941603407845c1c220340e900e6090000c0d09804c08001c0740c051082d07000076022200140191440249114005c1d02462003504280d680c1c01c8021018880940141100380a042404a5028150784400072a5130b9a0710f07482c0c1c04900c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 545080278 1250 545079028 545079071
    0xe03120319180b331314190b2206090e07050108060d020d030c050d050322030207090f02071e0b040f05160b0a080610050405010c02030a06061d0c07080d 67
    0x21311120031200002e1190b8101c2c0400704000a0541305109010020320000c42203900e0010751a040780100000900a07080e0300d1164448046250008980007421001085400c441e09031440c225116085840b40940c409104110082500380d0b000e100f40e04480c404140c85480c940502030400c80340900180745038440e901c200603142d902604020402c51982002418220482d40494903070261078841c420b541e10403c1902d02070240303445840040f8055640070b03c04c44640d00740c1242035000701400024041c904e44038044800c0c0011201580d112958a802003102282a4600400c01e0b0711f44110f40c0814020b480c10744c0e00036400000c035000c0001904040c0d14080c005401141c2c070b2410710340c0100304044046d018000d040d9054031900c01c191030300400c10080e00c1980040c000002d0040c40100502c0d0b11030006000014006010b4420b01e0459884200541e0840d40001420383d1071540800d10625002e0010b0740c0c0b00d1881a103c0d03003003000580d20400188500203048130003549902c1010381840c64820b668 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 545081528 1250 545080278 545080321
    0xf030b03030c0f1c17071e081501020604080f031b1c050108010c020606090a0e160e0c030403140901050c1903030612020d060c0e03120319180b 63
    0x40b900d8550400361580d030b030b29118805202d14040c000a855158002c00e10550b04003045441c0e900520030042000c0e036141d280209028204440040c50b12554107c681030a40c60905607503440000d480c0c403204c0c00d0035018282078250b04540c45038080202142d1400141c03108c03107103201781c900c5d526128051034040d88480390603050f070b045000080c47c801481a60041941c2483e071100c09100b2030382d80303c510608a03110b00340c10f2400340e002580051601c1ca00322a04650024440740f00042490298040b18034200e5040b10301680700340300e600c0500030000c4005100360300c200307050100c91840c50a6a00107216500c45801c80110110200b0914856801001075801e80549001192290400031583d001034a030100030503008a85011707004110f00301021540c520058018166024002c550703600d17800100842f40b0844200b2100b02d01040c05c1d540d0501c0018120401900c03095203d05103100701c030803044488407051421502d00700603107803007070b580f0600024200d4000c61051a25a181039008095409c0d040d0740 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 545082778 1250 545081528 545081533
    0x20d0207080d0207031211031602030412050c180705040303050d0f0906021306050c0c010806030f0d0801140d0210050304023006060621100306052e05090105010f030b03 74
    0xd079550720503502030b088103170003961021500c42c86651100b0807114004d41c0524600010000110100d0b40703036440414202c800e1040707178034080d070340c210b00055000d018200f1a0305400401c50740313401e490305043c40404080c841c008080c240c149550060140e100302d22005042c0314000c940101c012041d9440036543c9100e000003400750385120301e40799009500c404822039860100d01c5e008190a48190b05880c0841c032100020070302c001681d001036030760070f83c01401c895052098007820b46448005201900102175107494155403941004070800080651503146401000c0c4c28411102507580c40390b00f100201868201329941307881c2c078000310b01032000c40c1541481c0014041c11941d000028641c2c0e40c212810a54152181500e4540030400d8504c1203464040d0071441842ca2140b5194410484a4100340914a6070b0501c541e41da030303a1401d5520864101c0d15900321420941c0710003c160390712403120b841031540d21421904090004a00c0e60060085504014980e081000d01600039800050114401800c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 545084028 1250 545082778 545082787
    0x2010c0f080f0307020d0e1003020702040e07030302010b03060a18060e0102090907090f090213140a241d0109061d03010906150f1203080a020f031602070803120a020d020708 76
    0x442d8419510a440c0c000c014801d0209100aa912410054140302d0f0000d0213050981c20100d4120065000201c06903445075485d0340081c101d00381080103100461107500040b030b40020f04800c0504002c0000d00b8400c46a00700400c412a091703104250007a0b06070f000c0c030300003104010300c50800e0090207010406030b000040c1405214450381c1226813801211a00e006143c819074451400f1016802642c0c04040702c0c288014042c021001202250100500d002d4050461282e4071111101200f00480038044104203521460ba81203074414000c1014107289984002e20a1000c00021f1028086101d144100100791600303101c4003003d0f80c000c40a41d907000340240b006040d00d05040d0024143e222000f400001e00c10300002d54030450440900494196500c28986984603890589004100a03d00041c0503801c202d440011442e2030013550181c04800d0040b04000701c000f50191520039140c104107a598030510250a540324040300c52680007480f12009600c54000c0582e100280c000d022004044c03040214 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 545085278 1250 545084028 545084047
    0x905011406090108070501020627070b09041a031c18061206170709110421061a06270a080d030c0e06040b160c080a03260402010c0f08 59
    0x3a01035006400464915800ba42d88241c84c0e40c0d00e000900c00d842c0541c00c4400081c0c10340c0c20441041c070325420b240e02c140090381806c5c0d501e60309181d00d0ba00000e00d60a0040359900c0310342880c0c81050300c0b210800348017407890840c01e80029907980c0c0c1945c00880308803074000003041c0140310b00001d60482216480d600380032900d07194040e0107a018011110046480d0480016140482086000300f020000015200140c108100d000c064680940c050060381c104020000b40c0c07881441c0381c0504c1a1140c000310811015515102007074404e00521524400800342e50b4001c00e0303840204a815084800c1003030004220000001d000c10350710450080d500c140220307400a080c4c040810f5007203007004a0340e0104003c4d04001340545680c8012400c19800c9102404140002440c5070000c091000c0d024014141864441c0e40c1c84c04810b034030f600300b5003c9400c551078503410507400c41469030901403911000501181168603049490307400610203410001e204c00c0d0803040c45801c148007041150043d401d0341d552024007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 545086528 1250 545085278 545085311
    0x4060b0a080c0f0901120b09010b03030a0903120315090c091203030509060709030302030403030e0d14010e01060f03050c041e05160908011a06130801090f020f06070b07080406090501 80
    0x80710b1503025000c54403c2c0d010b40d00d4281140d0f4140c89126010a84450a80c0c851910a06004014030390742e651303444070200c4a80c2c042018042001596445c0c2c0750032411454138001c2840b41c184202c051500301543c00c03006080041c000d00549412080c000303060703803000ca0201e4014a8580c0207140c0345025088200605901d0f800180c495281741049403815214540300311040106c1c1e10018005810033300061000910039081823088500060110b4403609841e02c0701120078a1000007400942c0d903c01c1c902011850a0080c9001829400c60b00038003e4078503242d0130b40301c416024940d4451f5070342d0000c40d1503520b0510440444c4126101081082e841d0214510b200b240517603084501007071415200180042050041504965072808043c0c0303e84900018402290811784812241c80d614550108081100344903070888a070041404090f0002c040c0184030300c40444056a034000c1d14100105001b003940240e9507904010f041c41d0168081c0c0c1e81c0c0c10600000c19074034a008100b5402d0011140301c88212 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 545087778 1250 545086528 545086543
    0x10e0406090e0d0903080a030c0e090f040b2d091510030c090209010507060b1c03021b030309030a08160f03110c1f052206020f01060e0103021804060b0a08 68
    0x80d00d045480c441c02100c41544c00c0d0560740f100901040e802c002416080f41700e900f04142116050400c2c1c1020860b600008149800c104c5100340407080080400c400d0050802400390030000050404505005003403c5031865400c0c1c0c0c45c403140010003580070514100040290341c2c2c0816418182001d0703400c10080341804000584002d640980081130040349210f079610031600c141c8016120245020800c0d507551000d05640005954040d4542c0702e001c881101a51422801d5072081e4003809202c50710085002d144103901d1703002ca000340d00c140413603181910000b03500340303545402080103511200c4030503020040f1507a43c0002088848001172441c02c03d0382202500d202801240c09841d0600c009400380250b01c0400c40c118030301420881e81703201905010f9802421041108911074410036040400e00651140310307842500140d01240700f1030701d0030301d0a00c208009422a400004015499500040d00210101501ca00352907050b5021070304010003075010423201c0c03001510ba0100d003a0b503040d900e80c0b600c0c03d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 545089028 1250 545087778 545087801
    0x51302120705191404050f061306050603071106090f03070b15030d03140f0c03060d020414011e1203080a1a040504050303100f120b071b0b0a1a010f030b010e040609 72
    0x50303404e101011498280910b501c9041c40c00020300e880e6070b5810400020f12982828245007942e24a400702d4035480d14070045d840340e44161103400d401c2113640315040c58503500821903102d41e0400d550145030418040200d54031a500140100c003540c9a43c4413082131440141ea0040d03251103035000c00e94a4030f0b00b41d040109100725a41604685968810b800c9000d04000c60304c400d41c902c1300700005403c40c80d00144400d038150000d440000c0811502220700d01d900401c1c0c201c0314011356184e48405080b0400ca040f2005058640c84034802000c0e10740e406001c0700c101501070300e2401d80304c40b2009009454822034024132031000303105200314101800c055440c1e40c03064590341040000a400401d41180c0082e0f10390031a004000302c162000300b1a10b500e80500c5011f4000300801c103070b508200d054009019450120140104080e1890b410052182c208685144c2140b441c02c00d40c00007100c2c0c8070f0303130407042058640e041410045840806580101c68041c456404140c0c0b1518012000ca4204503940c8880c50558 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 545090278 1250 545089028 545089049
    0x11030c0601091803230d02040305070e0c0f0d180204020703031d0d090909032003041805010501020a0b04061b020c150705070303050d231905130212070519 68
    0xf0032251008448040c2d42c1c002501141007000036003c098080750007000080c0784030484900b000c040f504680e050340d125610903682c03a48049400d10900300004095600710140d581400e10308030314a96102018041e0012030001c0c16603c0c9411220847c00010260a1076802402103540d0146441c0250052202100d88035007c00d003804a42401e15001411056051031526a282d02c6890001c102000c0c1c500381408504020091b0800a14812101e4040c0140015500656125030614001c0d400c00b900d91411303544500c1c280300c01001240d80214070101e42c1e94000020b075056075034a0400e2806003849940c42c03446600310095110a003036001c6104440302c0402c0341c1701052180558604060303030013914000781094204000c10400207000f0b1006080311000c448000c1210907a050707040c40a102c0c0c1070b00c001580c6001c032080014800030144419100e0042880420582c1007000d00828071501101c4024000c072285034810100c004c04101100080100801c50b1551901d00c4010000c000f400e44640f60411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 545091528 1250 545090278 545090291
    0x30905030705310e0708060a050103120e01022a0901080a440d0b030111030705070606050a15020f010506010203090607060902040515033a11030c060109 67
    0x6150214500044502c010141002002d03100784140b8440c0305000308601142905080c060750281038041d00e1188046400904800391405a5244c18428000c0050800310b24200061000a81280c0308250b64a0645032000c590b04001c40143d280080d200c0c50482c01c0b4000003100e8a050020101c4030340e011390103846c1d071714042c0d90313a0030010741d07075103101100505046200503690071400701c051155040541c001420b1a110700345034000c803107d07080051300c50060400016030801c400d400d8040c0100c41c8c18240d0007004030382442c0c2c01d000080d000290640c1e003000800501c42c01480701c4d0342c04c484050100203100d0909955a10300070003140c000c1001140150160041c100a0f40c1c00c184a080d01c01e44042c3c01441c9401226010401c003940580300840d2181ea6480c0c215003d03840f240310f424440c620005c14500d41002175070826181680005001094a90750f104908512280c000c03181d00701410101c0d07403204000540c009072250b0b0000e00028036280f1010400c00c0342140d0015986040b2501c5c0c61080219 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 545092778 1250 545091528 545091539
    0x170a09150204080f0f061b1e0405040605190501050a141c0c0503040b0705130e070305070909060f0506030a270204180809090a20090306010b0702010c0605060406030b0408070309 78
    0x5800c6185c0c1003090b1a0807480c00a200c0482003070031242d0107040042058a80180c007045180040760308034803004c0c1140081020301442c00d040c0300e24005010226150907004240c1d01007600a44030350b0080904001d00810b142c000d56000f241001c0c01e02406104943e2120a40c65100c07221210034010401c03401c2c14041c94075407083c000d104490295400c074a1450240da1880015a40c55001c540d6080030400700301c0c000107410b41c1458400d03014000d26a404101818243c10041c10f05007103401c400e0006140ca4020803403049003144070f000303e40054a4040e00c03950b030503404600500703c42000d03403100c81007628260b100c001565180729000e071088404000500100c071400e826848500c034018021031081100d0b02c03880c0b510b0a40aa03110b041c0e908085203000880d030100d44600340c0030010340b003085008500710b1814035060222034090000d400304142041900d070002081c2030030b0400b0103000c0598074004250301d0f40b00c90300a80c2c0950340041e0180c1c0942080e140100341c0d9886014160001080b4810101c1c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 545094028 1250 545092778 545092783
    0x30e030d0c021e0117040b070e010206091011090303070c1a0f04030b0a0603050f03040e1608060607050a050601030309080105070e091807120b1015170a09150204080f 73
    0x601c990080c1c0718022902e41e070200440c00300781c54040203051045d59812410034548202d1914807641c8170303001c20310781410450380c00f511140c0803600305415900000100050400005500c01c0c41030b4003550003240c3d00b5041e15500d05140b1600310103507014000002c515003488115000802224103554401c00d01c2c01401c8521071140c084d503a04d040c2001020841040070460390b200c01030f08504841c6001415541d241d0b14949003011800500c01035030000b080030402400880092540501036040c01100605581030091a681c2c00800c0c5a100c0e0350041801c00a000c810800062280d50001c126152540c407412301901c680424403c1003040d608140010f002c003031261182030602c0c0c00c040c2000149494484585d400001441c0601c0300c1480380c1b210000c1c04140d007401d05108140144001c040c031b42400035004030b100185400c1034502000b0700740501d8071a03a1000070304c0f49918023408000c030b182c2c44a8200390050807620b01c010b072000145081d0b024641c01994002c001f1140038a003240c2007205040c85540c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 545095278 1250 545094028 545094047
    0xa03050408070b0c0c010f170108010c0e0303090d0201111f05150118180908210f040807121202070c0503010f111b2a0a0b09130b0301060909030e030d 66
    0x713541d0001c0d20f4042c52540900308142501c3e00f24117194a1202120100c5d1411756003d901c0101203a44444d07820907501c0e00040311448205042d0059454000884041041002180c0c00241040b4000c021856400c2e030520607a420100000c1107045921902d905007400b4010940f5442220320000703a81000560003101030003038085220765203106891500d401980052005408945403944400300180055544d4008045420445040c003140d00b1170a10b4440c2c076114000d00c908a505400424080071440540c1514956580001e1400d86d49130850001c90341c0207000004115483d0021884008000e280400642a21070a500030840c81003c80c1844040d01c84a6135000d000050402403c0702c0c0d128151240031100d0000011560b00b0301100171084071005032039061440b08642c20500c90b10f0b600d0300841500c0104003119013142007444081c0024070142e0100e1114000c00d596009010090b1429002807001b4414148100706003942404c000c0c0c4151000b0f08114071a01656403045c4401d400f80001c003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 545096528 1250 545095278 545095297
    0xb07171315020606120d0e03010e030409021305040908160c030f03081603020315150c160807080102460c05010f05150607170304110102100b030c1903050a03050408070b 74
    0x70701041460704400e4500220524000d234040d5241d42c054006480200001c000910101000503500c403d10240d84070502400c0d040b4911075810440508003003051070003921440311f00030342c0d000d00b119501d00e00540c464006610051407803400c2d180d080f09042d041242103200700300310348001d0107440041c1002c4049210490b42c84100da2440d1480c44034134204a582500071a449802042c41d03c0c0781800480d103000751040250b800d82c01c035510240f103184030600034070000301a4074000b9400e000d0700301514550306405200344081c16400c2503010507180705170040410f420b5407840420241c502a6600240100e20800f0140d941e582041480d0002e00154402e1a1003101502c220104085481c2c040140c42c4e40400c3e0261103111600c3d410640701c11004c0000d5004922824840d1039143c0c03031000190402086080c522019454010504510384001c82c2d4244941022180e803500221080e2802c0302c0c0c1c040c141c00181c280e204900300701007010340150090082e06c1040007103400e5655034a60348182c074424004c40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 545097778 1250 545096528 545096533
    0xf0f02070b0a03060810051b18010e0310050c09031501050306010302040e032205040b060315040209060706140a0605030708100c1b0303060302040b0a0b0717131502060612 75
    0x1c2100c4900000a000000c60314079001c11a00e660b110020f141141c0c400205000303980d40c0c0706010f0460103000300c003210241c06c08092400c20480c0c550080424400484503030520070203200001c0207940034045814409400801001a81800404410950004081c4030f0003442017400c0000c40a140140860403504000c0c002c002981c00c40c1d0a00c0064009181c1301f0f05184028050000d1418841da4072520307c031100f100f480c400701e00e004204015141e000010078081d881c10404d01c0798201030359400b0b0490940503500580d4410f000c001050551059040280c0702c0c41ca0108901c6070409025140c0c0d000d500202414081c0341d032103400705a01d81030540b16034031843e40002ca1011028809030809600c070520b40c101403020b5524a50349280b0003117000800c40000340d032030030103004500d030901c203101c0d41110a84801c0301e80c1c2c1c10300b000788069205400d00504910398861401d5040050034044030034180403900b5200c1c941e80c1d01c0c46040d0005c100300300148050b01909001459a0801903084680d85414400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 545099028 1250 545097778 545097793
    0x7051c080405060f120f04020406380c070905010e0105030105091009020414131a0126010204092909061e030a02040218030c0a080703080d0b03060f070f0f02 69
    0x20080c09030720402280140c144d050002c03120b242c6070b0700e4550707200b5081070780042c95910b000d00c100802c0351006d13003002d0301c0c5000d2429002d4204030225010700006031000d060720366003508184034159901070f81044195a1241c99000300d158500e0390403950403617008440412140c0d0302c5070308143c00c2e0b803811100c3c00055403115000b9841000190081d0040600103440000d580d14211291041ca20741110186807490404440e5020025110360543c101700340f910f01d000007541014003007504018004012000c8840218110725501000c0d4102e80013800b13031315003c1003101c003285910f035109a00303501c8201d194880c10a100025041c84504e0501c21003008164180c44038610002c0e0420310806a490340d054402c90000400503112840100344c4081140030802c03d10400104043c50000300790380c00390045100d400c1c100250300c0b00095000c2542d40c043c0100d40c459240da0381032001050711440300f69240c49004180310f0107080301c0c52a140103050307560707070b40c00c0240000000b079800c120310141c3c90b030041c1d00508 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 545100278 1250 545099028 545099039
    0x80d0e0d02151e0a0c050607090506030115091205010c0813110919050405160b07080415050c1c1b0203070302090a09080304120f30090b070207051c0804 67
    0x80c0b050300d41652110103801007083c0f41141d6a0060308000d40401c20107904a0240a02046241e80c0200c040c541504030509000c0403403080e000c10b01c070f21082401684907a031a19030141c07415002a000b40c5602200c1140d8600305a8060021519000c0c08543e07890081204880441c80560090381c0041249021107541d1080c01101e850091182c9200461050042011141401843d0040340200000c2030310400309000040ca80d002980304003002e05041094500140014055400301d44490001d040c0c0c1641c509400e80d542d101e00c7d8a642e0070350250610311984030900d01519280003965985900c0301e024052501100032440f007074081e526901c0140d08200603d45146c1726980103800e03040110b8110016a52001b03260000d560440e0a200b01c00c0a40740b05c580d02541c01d00e040031952810000345640c0c060392180840851841d11040401c011409080b5030321900000061a80700317098030a14586203500945030081030140c50310600d5448010703c0d40b501c41d002410683c94001a07034500d003a1500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 545101528 1250 545100278 545100319
    0x9010306290d0905032b02070b0c130b120a0501050103050103111002161d0f04031b03021504030e0a05031204090b0d020406030c0e0c1810020f07080d0e0d02 69
    0x100101e240540b2101c4a00c00a1001c2c40580500400342846d4080101140405240d11521031440c0300301c0741c4180185404200303141d00881c0c00c40c1d54800d00541c1d440343c84801b00135210041d0041c0c59038010024003038002c02d080c0460f0b03038416155000308020690300c441c011001c0d944203100c0500500540f4000e5840e0789010400560100800e00488040c00d415860a01070006541d102950031014880304103800c08003200d1550340071000407404842450142e07005030003142e02010048030440820917076810140200220202c003505207000318550310307040c45c1c014860001c4592150003002c0a843c005903a0800241203012200c0418245040c6400c049030301c4002c102540c9980d5111034000303080c4015031294402c0070040c2d40594000c4558504088110010a501500c0d020740d01c1c1003004240d0301e00100240515610404a48400741044035000c12440c02c4c1c511503841260f405181000a49c0c0c80b000140c02500c0505038942c856026031140030031243c0c511421000c0d4003c0300c00000d104442550 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 545102778 1250 545101528 545101537
    0x5060d0f0210121a041401031a10120803070f1e050f0904020705070f060801080c01120905060a1b110309040b030f01050c0414030303060307050103050712110901030629 74
    0x4034a003c10b032000614035100180d905008559003100804c1d0520150350a03c3d010350b0020303030740b40c02d15100346501d540c0d941100e54031010690540c900076413011601c084002c0303859070001c00728100b80090310030f19420716482540c400d07940000440c00300c800c0080d1040c094007242429404985020f04075180c0031034140c600750322409410350941000c100c0b221141c5e4541c030103881c03141d0141c00240200c504150726402040300a40200c010300840f04c00400c20000c000566540011082c81c01c3c140380113a140e0064060f05170708000500c2c2d405010700704500151107a02c1000c0c0c50700584d080800e05401d0030000e071500111241003807041e4004020800f01824160401303a40c080c0054215030342044010022800c490003a130341c0c92124440010100455101040450080072086000d5407542c04c21034006640d45040d880b6284c181621900020701326401184801c0c10415003171018801d00c1514007900c01664040401e19000c240b44c8900410480000501411155503a0f40400a980c0252900c409540c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 545104028 1250 545102778 545102809
    0x5090108011416091d16111207020d021e0103061d0a0509120316021c0e28181407230f04270203100b03100f060f0305060d0f02 56
    0x4100c0e0000030400507002d085c8143d178028040700c0507241025084107081c40081c0c11900301b041009032148801030408520a05a40e0a51600e15541d008070310218003038801c4140080d42c00a0050b0032145140100b010352180c0301c01c00d90b8104501038940b1007110040e0486018256040489070009610150a0313005a400000d00b200700c41e40f500d010302d410581644100c07400b1121442015514010580400c6081d44010580600d8110a040e01000824007002445e20501c1064940c01c03044400c52210981c02e144050700c02010640364680c0c0c1031850310220b684011064502e0504071811004088400034054003e5990303402880040c412110302800542801c0c032104a01002090480140755000380000d012141401c80d040c00d8405900c400d10340707203144115003140100104122040081406009d840c0d90080058403074840511405100c403c6810602518039111703404140c040e008541644200c40c180e506204550b00d0006200014540c0c1d90010302c1c5481504909006242c00c45020300f820300e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 545105278 1250 545104028 545104037
    0xb09040216050a0305040e0c030c070b07092c0c030f0f0403260702161809030207050301020703081b0a02071202041b08061503060603010b131e05090108011416 70
    0x1c0107456403400c10443c008100c010400c0010100b041c0342811400c20390085001c400b680c150700d082c4148001520400100030103c400d01d000045441f40a0000c00c4058a2500c4100b2a28641a060380c40c02e801442c40c504100540880020b0042c11f001044a21800c844c40c5645043c0d1034420200d6584000900100c09000612030455503008900c00e221230412411189070100b41011074010b4144101c02d22101e60f80c0721000d0341440f28850390305a24054005190b80090044881e060407424245a40c0286605500015040301410307400900180a040144070104014010349500c83c85885448104405a0040d0f002000f0301d01c0003481e2502410b001400110714041000c02207424621244180c0c00031881c0181803190a04010b030002c0401c4070283e490314a10304264001514901052146100390440040d50301100c081104c0c02200400790a0b481c0d111006004035040301030b10300d500070701c0e005100ba00000a19042c0500900c0e009840d0171032210000c0c0c50b0405002c003940702e40c915010034030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 545106528 1250 545105278 545105317
    0x302030a030e1c060506040e0303040b041101050f070605060a052e030609021201150c1e02060f040b04140a0e0414030c07080102180301060503060f041110020c0a06090b090402 77
    0x14210341040543d107511611000400345071100411041740c071154801d03420366109004101c00610a4818207400c5508000d8004e801e6200c000100c5035489a0012030890003030100c9c40c0d404104940d082940268000c84a00000c1d076158014005074001082901c940344017000201c90300880c000f044c03a1080700140c6800301d211a200d46c0104107a80c0405421038601e61040010842504441d10303002d40c2408524281d00040390584440d2501500004803100403600081c01800715601e500494a94005440d04551980d985410710a80354000c3d108000450300c0c0c1c403c81c94824544040300f80c095079848400c0d0011034903151191070485840070754a189510007000142c0d100c8000704090b40040500d00e00141ea55030764079806414240303851031428002da0500d00284002c0d070300072540a601a41c45640303010703207907100d041141004a248440e02d4000c402456001c14141e808100070300b038201c00b0341c1d00c076408540d950000c031100c040e00c0c420007100360401d0001d14900c1c0390a0300104486000300001200c0d2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 545107778 1250 545106528 545106559
    0x1305040903050d050a1e0b1207060c11010201021e0c010b0901090b011209030c03121b200c0609150c030f0306100504120f050114090f0114010302030a030e 68
    0x1200c2188100341d000c200c0102e0310343d0b644851809901e0780102054400e100303030038000c40982c6500c0e1690b80c10800d07003a00d07854414929200c010b8221000d102d800d04680200d6070b1000e006d84246414002035a118101c0c0e440e0380041c1d4014000c98440400800d029003800300c40030480d44094014a0100600755241c6944a2040e6100d6540703901903c954000041e04c52401000546400401403d45000e60300740140c01010079045a5400c3c0900e41604080000304050790301a4000c203c0303100804441084101e8a001403680440d50480300c404006041814582d9080794035915220100400d90041040004021a040c518040d504a2030300d5080c0c40d04055100c2400c9046411001000465603000310400c001407034103905001070302800f8207000d0310b814140076040300703003162200001c2e1040d400746480b00308005003540310003a08601c01425014a04110214545031f8514125800141d820500c190743c1414928640078107d0358000c009001040044d0380a5907425001349c00d640d84000c120305036505 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 545109028 1250 545107778 545107781
    0x71719110303040605252001061d100e1603050a141506040f0e150607050a061109100309060f0c0225080609010204030303050f0609060f150c0a0611070309060302130504 74
    0x501c100c454441031205810170701030040307080000c002c503007d9a040c80c030f0403c21401c0107103c03040301c0c40b05002022010760301d020b810007099001c1d0b8070940041e010402000780c0a401908030940045040d40c0c01c3c0301c241c452251000170f882410030395084c512008000724210455803a04103043d40d101a20b21800c0551303c051483c0c8400c030780d600101e00c001c401c0301040241051031002c400030700006c0b80d07000e0814409444c2c240c0c0d922895040105090303900c1c4509118440f045040d2070740220700070440e608002004100030050203403001c0445409060407090740b1418068011004078100640c000c0298859205d0007c2c1280c0d24644a108080b1026202040c241414004244141006800581c1d1240b40d854014100c3d0300c02071011004044282c1804461758400079060f40010b004c17240359079998503027400905800880c2c201d291404000180d1404d854a000c90441c0d02180504010440c0300056045800f061140440c004c001500c0c40c041409940d0084d0301408883c1b400003a034aa041d03403603a02240 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 545110278 1250 545109028 545109091
    0x5030a0809190506090d0507121d0d03020109020103050a110909100504060e2406030106050a17100f080304060c0b041712220203100e03071719110303040605 69
    0x43d0f05030030400800c19059420040c01e00304241901e003c9141603000c0d11626100c440c0308800000700b0588898090031303900070a207407003080c02008008400c140b00c1440d01030b000780740b1000c2c04c9010a00b00340004451034030320301c40c20700741050084081d480e05401c0010019584801021000a500480804102620360703128500107020308524140941c2042c03201818401d501c80c15030300e540d0345d031400c3e1114181c40314415a4119081030074050746840284105642654000c00d401071503001080030015410841000c0408503010b12140507809600c8401040d1603110f1402410085101c2c4409034002070320003000d941d4854041d2015019410184032498040c1d400402d401e501c0506060910031483c0c0c0240c02c912582002c02c070381c1c081078450303980130030344800e02050641250b568804403480310000600031544802d9002c0300302c0404c081d0f11281d2010603003001c00201403101116080c4010306002d039030380d540b000740c00c00f00450440d5215a600009084018034200c0c5540a00d100c01404c2d051071210f00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 545111528 1250 545110278 545110283
    0x70507030302120103080c12090d0809061903061a04212103231017120c01020406020706090e0f130618050c030d0c0803071e09031a010305030a080919 66
    0x1d40e1041084440e078a04080c01400440181080144800940c5c50ac440400403a6110740000c1c3c4601901000a010340680d0441c5020301c4048040303d2032a030b51590000c82a07408030a0130002020000c0100403290280303005542d4484001c81104034014440c070ba511620910844000500002100c2035085c481d2608031407002081e02e0300c40c10b44050441d9242c4412644080c00c00080324076299a0129600740302d441412811150403000780b4541c0001c0c041c1c4803015046441c1c41d543c0f112810701c2c036030017076105210750390040c0659100400c10600c284051000c55460041d05d0f05251540c0030620740c01203025000b00300948204031614000b807a00e0086404001c005801600e18510504155040100403504148242c0000c0e0140a5040e005000401c00e2900301c1001ea880313039106081503444502000170300e14200080e450050304560311481300c0717058a00c54101340070000c9041150398020542070000400300d4000b800300e480050301c1307080510350050300d0f40300b10350003403c08204802c08068207881c00d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 545112778 1250 545111528 545111543
    0x90c0b030109050c0a02060f0c0d15050a14030706050a1b1a010501052104020d0807120207060e10030b0312130e01150203190e09011503051e070507030302120103 71
    0x421180b940c078841d2660000c4000780700b40c0b51046249000707494000040c80f100510505c1e102065a00b42501d042e1581040303451010002c010300902d080e00c180099203c0e20b4450001a900491074100c1c8080604a0300c001600800000707081500986450b0040d41c10300d01081007104d02c2d040081c009808540c0801e000b074848400b40000e480300320241d414160000b42c1404000c20140c0010303150003c0041d5000f1020b802c3c110305071901c1c400505264503a5801922480021511005000b101070340f184100600f5000c80722110b030340700020740d1042040080c09a0050a420050740c619002c0d0b000500d9040004041d2840d07086203819800c25904460a0b00154201006081c0403818000401c5409000c81d0482c1d015400e0462600964078482c200740f80c5000040300c560300f455a030054824003284e01d00200700c0380b41c40d03855080380000c224164102500180c10310021820103a8100301d603681451100042d89a20b82e160b48041c2d4403980300d02e03405c5007010703820000d0a11002804506501a40c4201d0301e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 545114028 1250 545112778 545112781
    0xc06070e030c01110c0d08091002030c07060807020601030825080a091409010323030d09171e1c060e0106032003150d0812060907032d090c0b03 63
    0x34180390007500d842e0780e8140b1011010700a41040005880f103210a800c640703100c143c14035850000c402d802034509164010086140314546150040041c0031b41b64104800c603860307290348480071101031806440f20b0300540c204100600108a10744001d009403000da100d40718804049462005d0440c0da22401610840c001248501c00c147d84088207134020300300d62650200c004810000981c40b88010302c8014400c090801806003001c800300c0403080b040c603040050320b4a8405070403d40740a040102c0e4205ca02c114012400302060301c1005c1070314032000c0c04020f54200406a40c240140a45c03104000b1103136040240845000c0c0c001c1406400c4c00340100007003803626945020400390640e01501d1180e0088101c140d400641ca541c0d40040c0c0364814100303800c410910b050300d404500e804c10320030000340c030070200000e428011300036140040d8060501910085600d03030718000c3c02c408860310760140d01e03a00e0080c00d42d80ca01244e5100b44180c520b40c5020000110000d403551045a00b0700a607214020009000c070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 545115278 1250 545114028 545114057
    0x40b041b020c0916020613030309080406172511070f03030207080c270606040317091305070f0806060d021c0c050a080610090f080318040902030a021201020c0607 71
    0x800d8200315601e50707890300c03071010000194407401c0c028007007e002d0105180260605209400803041503401c02c101c183c0c1e035034440100174021640d02d00e0001e6000600b8000c2542440c0107038403595603140002130352003a42e0500c0d004941c2540c8071000c540c030034412400c02040c0c1400001a00b0000e41c40303500204615440e0249403403c0100c4100250700c03c030310103004440c9140bd00d15154055064460141d1095038a440028101c2d001766040500310803542c47c40c07600006c5c840e00c0286500c20040362418004240d4100d00070940d002114a1000280381109558015004e0041e00e42c2080c00200940d050104a001110803600501101c041c40b90341195006c0c3c2d0540d07180324003201c061891800c0e502e030508000c0d024003030080c0035082d180184c06481c10f135948244542e5030302010f4039000c546084196940c40c0038a40e01d030040d0f14005101d10002184207440d150502c03890603e03560103005009502c0c50358080201d014080e410348011550208514422880f050104504c5818a52a81014400c850 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 545116528 1250 545115278 545115289
    0x203100302031b040e1506060d020d05010b041419052403070302070209090f0303010312020a050f01020c1e06010605070201111c09061706040b030c15030105090f070e040b041b020c 79
    0x10758000001b5000000010220341e0307181074581c0e00010664650760750f001d40c0e4142000a101716125616240d01e00750003c01c000368414010421a0030b002003401d0821b103a2020000c00e840e10900c1686060550b440820a03030403c80e1203840b4400084064496003080341744400440e510807940301c000264002038400071480c02411654200040c00000c040036595605059941d00c01800301620708103400480150151081104425056000069a44a0411707a01484c042e42000e201a40741d130003808201040004007030600b00042c2450f400a0034240d1a1000507687c0707074480388085e410061544403800c044071301000610025581100c11108003058081c00503d5031a46401c004100150070440b00f0030658512095500200d0441d40000d50241ea540003d00e480580b8171703801d4001641c01a4200610340391805107048641c1a581c00c1840d503180d2440742c4c0032600450300c0002042d424200c0049500381a0f00c0741d0403107a030103040001c848120085c0308941c030120f075080100583c0311100b5001c29041c803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 545117778 1250 545116528 545116541
    0x706060b040f1a03040201030906110a030911010e060706020304051e0d120209031b0a23030610060c080307050d0614040c031505010809010603122a0f03030203100302031b04 76
    0x80180034110700c80c0d803c001e00c10f944005840a410561500c2c50030041c00010f5000b0710101e61001038940d83c450103884050701a161030441521a13090010111081d5401603801003000300d0700400700c0d07103007010399500d8200030740000d08141d680784200c0c4509080303d04242c202ca0018803404004101480c0304101c000c209001039400d00e03070828014041c2c07010030340b400030b841c418a86011481811750a59a0042001d0082583c8820215140e00a041c076100321103254009041038240d0a80e51070741d64000c0c40d03801c481c9861040d140003400d1204110049543e8201442d00500c561070710500e48466006101d040c0d818540062400c242c40b00c3c1340b44207a241c1407151144840190900f80600400c92084200343c01e0b40c0d1040a052158210018181410030f41c801d034080c41c1d019080a900125400340104110b0b00b400000d43c501d656a10072101000a00300c00680f026480010600026620342e41100a500060301501210441000100046c0d038107000c0001c81d031717110420b83c10b07041042100300016200d6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 545119028 1250 545117778 545117789
    0x50c0303130f140f0405090f031b06010e010f030b15030d09051c080d0b13090303050103140105010b0a0c0201020a0c03051b190e1e01030b01031712011a0706060b040f 73
    0x1d0384200c3c540307501e60f210300c0d2000c88803c4900180e41e0341c40c2c0f2202828860750980c1da403168000024200d04065000b8000e00f819910182101e20036170302c42d080542281020702580ba2031424103402040000e1601e074180782d01490081c82e84120400d544042440c0c41c0e000511000071610003130080c0080c0c1010b0b40820502089104240c1d1901c1c0c860300d44030100c1c0315585240550b10f072528805002500c400c1c0d803c880c9a200307550100503c143c9402d00500500003070000b220014080d2805650410b0140a0181a660818034051818900320301c140d810000301031040b4154010547c034640454400304080f4001c5010344045d01400d0100304151601500608042e4882c0c106441c00074503000500804005581d55800035210a8581700381440c83c0360624044114001c0421002004014000500074100c0e48113480c9000ca10201c44034614060203204158940341040e5001006001007814401c41d00012a0f503c591500341c050b02d0f103000b5181e5075045002d480700c000400b0000341c24881841c1d0010310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 545120278 1250 545119028 545119049
    0x20d0806040c0c02010f0c0f0b0f070503040c050d0c080f0706080618150402070b04200103230615040609180203090307060207062901020705010216030f050c0303130f 73
    0x286031081c007600d800038807034001e4100210450100c420031f004594013070141d600080000ea40144038503143e50648002c0795400380d00858007000c07500803030042056031300aa0f88140c403010318509140c1442050690700038180c1c4ca6010401d00022030040501503c0d95420b001c0c0068010141040e0000c1c1489002521250140309611142c548032400100226000505100c0000c0c0c41844140050064011108090f110a140134240404c1003420420304460070b036100048005a5002c030010f40450b008203e0004080042d14001031141c020b08540f20b51251008140c8140024006103001d46c03a0400d400c0040810b03030520003409402542c0b18205084030003540190b1a40c0350000c10692680501c8600500300c68020a80400b08206074024080040d00708400300c00d42c04007840d4010b41424120705141c00b5002d81080829a0350bc003069400c550700360b2109050649146030347e4101d2032000c000003035909008280342a000e82d9400c0c0014046140c0503810304422a080c01003600f200e9416500044130b00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 545121528 1250 545120278 545120291
    0x30503040c0b0412150e010e030705060601140702010c03021614090f090c0909010e030d02030105091303020c1306030b04081201080d021902130501290f0f0c0f0706020d080604 77
    0x1340f0340d254620f40d600d94400c1620042c4452680f105015007000307250055a5400d12002084681c000400b0345203c901034800c5030082c0d2a0100152a041101d00c1c09241600082040c140994045c140c2c2c080f0702c52003807040710200030545d03015666000003034000125505216804603000d1801c052400d030450740c01480703070200707041c00e60f10f466644c550010000d00460f607910000301d54200a5208102640102094035543c4105003154402540309010303991080c1e07181c202003800711006002d6020b01540c103030000d01c00844003a0030404446031440040c110952244c202100148405500d07a0040f8842e10a03140c49440500c0c0c0e281541d00141c01240050f07002c1501d044801c0e41c0060340307174400410b110401582d4103d60004c11000704038680d80c442c145080100001da0b801a910140b69110304c2114000320701503544002e80c00c0f43c4108040c100d0710721414001d0700003204284008004a12a01080b039200e44055881d07142014180d03480307540941c0240c0c42c174240e4580c02c200300d603030b20110454040001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 545122778 1250 545121528 545121539
    0x30203070f12200307021203040b030109140106020c010e0105180a0b0d05060603280e010509071a090a030b06040b0d06050702010506120607180512010204091103070c08070f080304030503040c0b04 86
    0x701e000d5039034064406c287e0711001e01500c0308103204544c060198800c00907034a42e1500c0d0244050702132410f682013140c540d02e000040140c0f000c24004844107050b5141c86034600b0690044481d500005008403000f40000c108010995560713030356800400003490035649a000074401d19045440c000c03d40b034001c03d000c0040042d0305030307021043c0407001c149030002d1014450500c8200002c02155100c120650710340b1043c080480740001303203541254800b40c8201a08800e55003084103d0041d00310060b00b01644c00800d1000600300541716070f10400180000660200300b10004403c01240101524075903640e6060082d03081c0d080c0125680900300f514501e03e008481161980c3d2084010a4281040000c0c90071180404422440700000e01c0c000741020307a015500d18156000354490b1144500e00340c40c001c115150003030b0400540b44116001d454412404849850381d801550203404112242801a1a01000555910302450045000756140c03a10381c5024940075214140a8000003000401030204016 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 545124028 1250 545122778 545122783
    0x603123c0d1b0c0b07030f111209100c050a1b0506160908010212130309030506070f1205010608070c06020d020a110c030a050d030e0c0d0812010b030606040e04030203070f1220 77
    0xb0005d44c01c0c9000181002011440801001810030440c9043c000007440008154942c0540e401480c040301038445980c040c0e2040800c59103001d003a1004110309002480f12107005e07504103403040300b20302e5000000c0080d507504d00f4280081151059441c20322601c1660807141d004586e4005010038600031450401040901031085000806400d1440d01101d0714808042c0700e41c82400046500ca011036031f05040c40380018000c544024910310000711204001c04503481c541c000c460481d03c2c1a2103501503510740010880b08584000070a4984503001c204810340c01481c1c1c402060782d4241940c1c1c010350344c428a07107900c7c100b03032140010302c3c42640030340c8599000c0780000c40c00640c2541c01c0e0900060004001d84028244007070301408a6100801580500c24801e10000528171001071481004581c4e0f2501c0f01001c65000955910380c04c0306003484240800e501c03a025442e04203010707004917420314072a5610007440c1c13048094101c3d0790711150010301c50300030340101c3c6031600c104a00c08643c010340691407213981d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 545125278 1250 545124028 545124031
    0x4081209010e042c0d02240103020906060f0f360f04061a030411090405190c080a0c08010615050f250b0603123c0d1b0c0b 54
    0x9100d1607903180d021110407003d840d2402c81318100d0200820909020700440d882d52818944540540a000d00d0840e68040e5400300c401c5207002400000d030300b0713400c640074818001c01c0103008a03006202007298288945030103010704107121050700451f0369542406076030b015211520001003e124076000c074803003104260f641c003d901d086082d0b8940760000303000800100a0140b03039000c0700c440c04c100410741c07071052513500040d441240100310003401281e0560a000c81e1610480f40546030740c019000d144c910b100c0413900e0061542c000c0411549080e20351407070701e040500d1070204680400010a0801061100380140710050424048211516070801c1c00900284108550407103201400224245460306401019681d50b10380388160f01c01243da03250850f41c0718415076209200c2c5c421110a07903280c1504a08030b6048070b55401000104c1e000c18007441c0c4500196040c0c43c00f04030003041c80c40e00b641040401402e0700e00c1c55100c003c02c010708001700d40840d0440011400c820000c05107580c1000c034850703030f8445 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 545126528 1250 545125278 545125307
    0x9090a0c20150c090d050109020f09040507030f110a120b0702011e020c010e1501080c0a050d08070204110a0203130503070302010c0305030709030c1403240601030c1110020408120901 80
    0x900d0030390f48905040d0707980d11400811903449500c031503540301032240c15886060203500c2038880e000003000c0041080000c00c81140c001b007803070340043e0084c80040c1503004180542442641c1c802181107042c40000c0b81d04515810600d60007141103188002d02c10390444041e04002036000070070500d0701048084e81c29a2182c0d00f0304041d0b903000203518401039030941c17103110b4451380d040c103590034403080000c80d0042240a1040d0b00b450710802903610546d00c4c00c4200f42c03040790001031242001603150b9440c0010f82d08500d000b641c0c05030f912200c941d01c030143e8200805600c20550302441d900c8880c1f9554003401c18268000500a80c0704100a00c0140d07044075455041c1900b500b002c90707c9580d150422207a804107904002c2034412700c0034002582094040480405540407001d072036000040542c650304d1413400c0c60003103510802407001300300554000c1d4005261900d051507c0c20002d281180341a1410103202140f052283d0300040400c0704a10501201020041c1c000f400740c5880c0c44400000c08540c1e040546 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 545127778 1250 545126528 545126563
    0x60b0702130b150a090801050a0902030f030a090513020c0601171b28090e030409050703022a010914031902060103050a061109030a0c05013002090609090a0c20 70
    0x201d43c803090003000345c2001498580700034000361420030041c1c0050407100301d040303009105400684209207000b000b0744141409555401c2e40b501d107414100041180426500c0d04001da0800c0814011001800414064001d460303da406908085008034609914002182e084c0c0481d1554801161344500c954208200004910b000d0228228810f045408241d070140c40c19515122031800b10500110150089070400007080005030b9800c4401d6041c2d10820070101d41441441000454a8031440700c5403000025107070000900c1035a603620008512044029622294000705440303503450b40d4948a080700c80035520150109515644d41c1c0d50743d0b4845100001d000d55150806a50500c04231000d648607828020200c8241c2c0115041242031002d49004860000700300144107500024031004009055203000140c0c180040300c181100300030b40091602c2c6038041001c21805a031591350081c1e031405280c1180002984030300d066005802d80c070700e045001001e1134000b14605200080403d00c001c001480254 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 545129028 1250 545127778 545127787
    0x709020a0e0d030e130c0206060d05190c0e1005010c0809031c0503070e031605150f13090b090606040509060d060e030c070b09030c0d060f060b0702130b15 68
    0x8207440c41e140310600581c001400b800200c0601d540040302901c054429924010015040f041000a03101b400030b1440c0035078800d41c08980d050920942054465000c1c43c2907443c1092207941003142080c0c9800143c40c2e14030f50000074010041c0311402d06d9001101d44c3c03449103d01c0d103024000f820340000300b240a091100003265051041c1c03030512841c0d80ca03840001c4202e824840e018000382c69904180d9034a0b002900410b0946114117000540c40710000300004002c10301d80c980010407040d000c3c00351506802c2d200c1481400d011003000d60150804c81c0c00400100b1103a4149407100041711001c4a0403442802081d0a00915403101c1c02110192042550500010780c0c07075401140f19441003c500a06a03441c1110b041c03007560011011b480d502e080401642d0b209940c0d480011590700445e144c25a040d002140f0482491400490a4102d684100008600c034110b11526074110f03501588514403500000402c8030840c580003002046168048a04018540c42680841c5000c0120350903000c0d001d90014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 545130278 1250 545129028 545129047
    0x13050703020303030c1902210a052208060702010c0e06071a0a1508060105060d020a18060e0a06170f13060207060c08160503152707090503010204030302070902 70
    0x5a5000c0c68001d000c0f42c0e501e052402c000b8090b94804030991401503801342d05411800d102103519004007078644841c0c110420320b080d1021456100c00101403c0c4081004015241d041c1a4005000c256a5041c110001ca19045940c2c0c00c0c0388004045d03c0842e498148201c034080c0e040b880c00301d03881d401036501c0c40d25000d191030499030340c5003803141d0201c010003032500708105848a5006034424440007206055060380c2c6080b4203a030360b2070078000c04d07520402c24400144498000c0d80a84000c020501c1c1c107850580b03400700c242810701882d801a00000308914910300399420410318a400400e418601070301107a150b0309911561603c040d00301c604c5480c5400c0801c0b91044904003000300d40b908040d045581c0d0700a0300c0c045005222029006021034002400515603040e8281300c1440d1200c1c1d074680328903695403d02404405440c202402d40e10410521101d40d01e0b01000d1840320440f072500c003042092317042c01c21001c0c20082440d031000b4460781c01000240002070f80401c02c58101d9003103030000358481c0c9204 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 545131528 1250 545130278 545130283
    0x240f030b061b070b071e0f020d05010e162105210403120c03020d1413230406120f0c0510021014010311090a0f020a02100b0303070b1305 60
    0xa080d500d501c49004520100d03140e504880c2500300020b11402c540c1004c0d0b030703000700090b1405001006803480e0100310072100c0441c40b62500344140343c0714034821112074030540d000940b05000f15100351042d80d035400170700b885400c0c10000154011100c540110b5014a041c00408034110380d107181c090013038400000c120401a0030030010004261142d001000c0d0724905843c0d000c1b50300f144c48203490821411140c0706030640202c07105805660194007034101c0329a03017401070b00e1200d0041104100418208411411a2030440300000645000302d4409891a50b002500b1580030500f6105403003540381100030043c0c2d003441515212801c0e44950000081c0c00e6078200604000d4040e8006a004110414141c400a50209082703c00200000c4100b0800f40d400360b13454140542408014588a0304d60090545447c0c44452903501096604011174074071107040c0e0700400d90700711032189001759005c00d01030070388512240107221540300300350011410031550740c0360300036001b1000d408194803105c1c2803026400e00105 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 545132778 1250 545131528 545131541
    0x306010509010909140729030408040b03041514010302040b0f090a1113060203090907050702030601180f1a10080c1e0c03040f14120d08070203070b1807240f03 70
    0x2141e003030303c44440d52131210621487c502d42d41d4020401c40e64036107490800ca4079080c0d0b8061500145014101400c00b85000741c43d03840500290b8894103d003044840342c420f240079180b20350540c1e4041c8000303940341d84144015512000002071107600620011a091349581d0059a807007410090049003000040076855400d01c50b90140c4031803ca00f090000c298513800000a0000d494262091a110303600c40350102c2e81c45c010490000e5040d04070304010011700d92502c18a0034154001e040004030700750405010b00480d035886017010702c48401d0503440714991401c0d0a070400041d1007420004221b24001e8480e5000c0d1158441103180001c00501544c008259201035582c410243c2c822a45d42d56100c119607420240e0500c1103098100d81c03804a903185003004a0503180d80d181d00c1e4010b04084001c03142c150b9810500409850840c07000303004100c0031403000e05007030303000d190f0300e40320503070b0000600c0520307800e00c511a000100d41c0140208100c041c0b01042e204100391050134a411010740c01030075801c40290a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 545134028 1250 545132778 545132813
    0x70519060b0621360c060301030807030e0105160f03020c0f0604090c020a0507060918020c03070f031e0c0219050307140109090203011401022e0b0d0507030812060306010509010909 79
    0x302250500a48041c0d10b2525903c13000130740444e11000d00c0403081143c507200900000301007a805012000000e4007070400c010906a0504100b81444000b03401d02810552a170010f58901071491030900034143c040c440e0111000c01134940740984404400400c90920030791281c07800c2c00f5540c1013a00310700d91003404030310001580034003510b00440d41da20380280080402c1c012186103040c0338280380c1c2440c249208580c0c01d09401c002030b508280741603d98218000300b40c0700030341c01d2001d2040800c00d0a280d03408031420308501c540355061000254014450030030301b0304034806581c0c010003074103000542c2c0000b844402c1b42d00201c8039a07049002c40004807507403409070f407046110b180080008121200d02c004d80f40340c0030b4030a90840d0001544004580301132504d81c08100d680031502000000c04032000e810070310540201601c462055411350352a41d00c1d00840d036109a5a06a020411000c1500450603294100108034000c05072941090002070030040b040c8280d00b001c0340c0d60031031a010481c60b02010401d040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 545135278 1250 545134028 545134081
    0x807080d0c0f090602030301030c0e090f1f060b070503070b04060216060515040522030e100207050a0e0f0c0706091b051014071403070519060b0621 65
    0x40040042d200c5030701da01006010460386440865070501c0002600d04990300700e07001139a007a28106110b1139031040074020345060700075100c100e012410100620700182801700d0705110499644940b0204990054028400b412010003170b850202e000002903031070441d004033b4980c0c4562508d28000000784683c0c40140c00d991800d030b00c3c3e0410321440d580100c0c03040c000110018078400214080004441040b5140f1038115002504404c0c0345c1e100360080d941c42c0c1c4c401e04000c0015561440041e41c01d01c0035000c060010707442050300303000c2e80c01c085401300014400307038288014130308144100b0031615038000d00d45440c244002c94100305120300c581028015070341019501c0c3c1018154440f01c00c4411013800b5107401640c081c0500c0c44614824140c003091428060040341c2400d00a0740c1e03000c10180e1100680046100034015031020a900b4440e0036480109440861202e84851912030155445008003512849050083d800e00a0b044888424510900600e006039982e4030a03c461610448a00808040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 545136528 1250 545135278 545135291
    0x30c1b03320a1d010f0e150c01150501050a120c0909050a0501050306100608010302060c120c0d14070803070809190821010b0403030807030b0603040f1104060605070807080d 76
    0x410501c0c020841c1440307035554440c80c0704201c08407590b4855800038a50010b415284002c03c82440740c102e9100441d4000c0c0341140800d003d070010580c0790400742c01c0e0712041e50b455034010100e0071014503031350082c1428241241002115000600f2031459050b030743e00000d03100c1003496159803168020f840070380900340e010000c5040560402005040034002e103400303441408081070000c0b89181c404411614140d03200382a0740c0c00e50307003406410340029039480a9131180c0180d0815015041000d0030082120300c005014900501200420000707c0100c604400c1030104403240118014904495120350780e42400c08450703e07900340b0b591502468030321134035200122803840340030003c0c1040105546210308102c1d03009500c081140140c14103080c428105018410002040000e004800350b0307510407407a04001507040e0004010400550086400b280d4000c02e102d8034000304000d800051286000c15a8100b06040c00c0a10160192003032510103401203c021842208214100e4221004592003130030030b00c4007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 545137778 1250 545136528 545136617
    0x20c0307170c0622020d1a04030c05070b0415031a150703121103131e0b0901140c0d0b03031c02090a06020a150203150a0312030c1b03 59
    0x1900000ea42030881d00a58010aa6035402c11500f400644c40040010148003003660800440c41109541102c0c100106902d1660440101c01d0381c81c4a240a42c45511071500545400ca04003151a0000e04c0704500a000a100d680d4000e0b407214050b03000b505000400600c0108501d4510900d02440c0764029441102c165031060345401801a00384244c5421100c40002d460394425204050b1070081280818000120301556003042c0d41d041a004011050520440e1b03070740c5000300120a9801c1d15030146010030f01141150911403800f0211000c00030100d9410241d29140c424030404030640c02090322038244d09030355501801180c0290f006461001c000e844c00200510184d0040106184610483c200c0080d450780081008a481640110ba1080c0d503a01800150000d400180c01e01903c2e800079034180000351105900720b005035024862881ca81c040785280101030343d00b4000581c2c01c0207a40d00c20b41001030030809d110142180c0c1424402c283c0c282c001e0003000015146000d03180d24403000a5031250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 545139028 1250 545137778 545137823
    0xf1e0e120a051b0406030b0a02070f0503070501020a0f0c0b0c0a030f020d0510050904111912030e0a050d0302060c0c0c0303031003060f0b0d141f05010e0f0c0d020c0307 74
    0x185070110420f03050015008000300300884480b480050001c0e5400d03000550001c17403541c0103016035445502c240c0000403840d1200e41c03a50f00300c00021101c40e0360026511201d242c000705440b8076540e0524180034901d01c250b581007030700c420140408401600205220403618002d4000c483c2c4401d0140c001c40d00e075082c0e070440ca4081c00e8151100503803034020040115050a100c6200e1748580d03080418007007402d412006110f11102c0d8042003852228604d480840d072115502903a0309442e009036250401000382900b0822504e42a5004c1441043d4030810f080000e5000303e02c0707a602041900c54142c44107284d0303c14034181610000759541c1400300104001e64015880e08050669000340000c00141e05007a250b1b8040340d103a483c5440d0721480030b901c0da00001e4183c24a4984035244001503c0d0301210610b40d00c5c40d07a421186e504003081703440f50010304c00e4072040c502865010030540054029030500c0313840c16415100783e5002e200c00c07503000240151940d0007001103139081d50b44000241207201d1000c3c0d0030b40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 545140278 1250 545139028 545139043
    0x72301020a021b030d0906080c0706060b0d050a05150603090a05070e1008030a1d0d050706110f070501080c07170706050103030f03090302031b15160f1e0e120a05 71
    0x30210203030100030700c1c030f6800c0020b003d00302c020981d11200661807c107003003512403040040c04240e00741c004006001c00521180109401411101c800380e46a410114030302007a80c6000302030418880c500802c010380c070008000d1141c1e10480030349017640d80f612a0301b8100d080500d0312401805a1140c45070015402c600050000d101d046108284503245450b05e40703140d201e20583d012134000803280032415551310106540901000c00c000d0604502c1c5603a42d0702c0c00c0c2400603541c407050200341041c221308206a0107008034100c4110320005030100c0d42c104800078080c99000f412200740e0b2040800e900c400c2001582002c146e980d2000d11140d21041c49182440c00f4080c240411000110a0800d1102c20b9000c0d018100145503d034020354100410740b00150301c40845100420164482c814170032402c032012f040d0450158090504030105118580005440786c00c1da0070505003000488822202d80141480003100c80d0704992510010f03100220001803080d041d011030040d01070103150b000c0d40030000d0029182 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 545141528 1250 545140278 545140303
    0x1614030c030103140105070f05090d12030203190b0901120f061e0c081915170c01031407090308070206280f020a0b0a0c0c0503040303030218060906072301020a02 71
    0x4e9940f4401c018150f400d035001501c4080110b007a0165032242c40340100701078074441401421070b0b06400555140da0701851440341e19540420340c00814014140c40c04102001030800140c010b00c1201c0707103000821448081445201e00d03d0300703d12100f8081100c1f61045c40c1803950030010920502540c1c040c0c400a420544c981d000f41c0616002206212501450350319201d0720b49140c0340c40d42081d40d0070622003d00205400090102e85c080004a0b0768121600700035428040000101081c12012001504850140c444100c080701e110040002d51544142401c040c0c0e503202202d252540340034404111b10380181c14182841414030252404144088036455628209941d40d5680c90110031030181d03103c4001d084084c2080400c41e001078140c02490b00014410003041c500941038510a45400e41140c0041c3c1003100080c0d0001108450404400c8500d003040c1d208452191420109000049481c861084001c0002d014030202001e81045110800c00b070810500081d55912042c0c1d000079101e4040b02c680c0d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 545142778 1250 545141528 545141543
    0x120503030712050103110f0406050a0b040f17060a020a09050d061e020c15130b0702160608010b0d0f0b040e010603060e0c01020705011107090c08160f081614030c030103 74
    0x12241d450035600031181201e1b000500100039a120f9001d00c40450803148110343c200303450b410300003003d13140c07841d03644010a01e0401180c0c1301c07824501c613103040b2602a8425010307600c5075400c200c1000d0004c107003d90031401c0d540d40180e0314540943c0549041402e13038480b9602012100c030351018004a60030541c03080640801d241c0e868002000540c1c124058429808101d50107041a404a480c2c8110325507045041b0900680c1c6d006055614205d415900f02c41100040e0817543d542d03d000004602114050005401c00803071940c10010034410707502815a02d440384940703c2c0000c0140b0812036100080c409800343c004d00641002d50481c5018010790710048400d1450440c1c15648030300e0119201e090404140d010384034403440e040c01110f2040203983c04142074040c580c00000c10440f00c3c8030f07024009041d1303150800c0382d00c4c0050900c10024810800e13103081c400c81c080e402805c142e02241b81070f07000700540514405100041e1044610f20559503511203500f03000028010140d240402540c103d908c1083d8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 545143884 1106 545142778 545142797
    0x23060405120307031107150c03051b0c0a0b0306060d0e070b0c06010f050d17031305160504381807090302090601031a191205030307 58
    0x180499a100107000310070183c010302030114500c0307030f030025246144c600000300c500728000740c070111f00304602c140d08101018044d01c251585c0060441070b0b909410314141409941d091020f811903c43e11145400144510769042200c0c841e004c003500b200d0600072100c4886007d459071410440c0703079000e41540452800300c46070144c0092680c0c3c0d002003440c1d501d05000d1103503580c1540c002a000c0d0081802020114007460140c1010040491a03035907650b60309400c0e04017010110000070610f01030b02425040607203141000350280e0305e04031010400c1e01c0201581c0c0c0100da40b0110008404000c41508618200c034004154800340703000741840b50050417000d00000001802c40d0b0b0b040200381022070a00c158104040c50ba54848000c0c00d04105540c0d0300b02950b580002c0080602c0c0c4039290310541d165a6240c241004402800183c04500c100061440d10b40c0d20b81c0c00c01c0f589040001c2c030008 = true := by decide +kernel

theorem cover : BRFrame.Cov 544964028 545143884 := by
  have h0 := BRFrame.cov_init 544964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 544964028 ≤ n) (h2 : n < 545143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
