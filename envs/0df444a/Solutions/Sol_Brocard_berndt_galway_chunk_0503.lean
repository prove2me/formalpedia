-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0503
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:08:33.8056+00:00
-- url     : https://prove2.me/submissions/ac616082-c9b2-44b6-b4b9-cfb843435795

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 90287770 ≤ n < 90467626 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 90289020 1250 90287770 90287773
    0x705010509060d0e01020d05010503060a051b0c070e04080a1103070203030412030e0d200405091917030702030913020a020c0103110d090f0302152404240611030705 72
    0x3220a5141240c0140303c81c192009000980340e100c490394500b03903001035040460f0150345400421540c14107000c41540f20360041c404201519011424482c0501c03000604842001c001ca03d130403050340100700310006445000600c444500d4245000c0500d0f40c8180302e2080010341480e5034215801c000010754500943c010f02550074142000306003c010f1080900940802c22020742c0803602d80c54500000311014058000b80c20b12080d84a455020514101c4003140260300d00801c001210300d0120f8100142c0d01e0b9075084001158050904103c0c42400c51030b0810b0b018800000d000301143c001005100d0300c01e00395040380b80048d0400e04c08080b8040c0303031120800b503049004542c4003584690f1005180c00c20603d016801c1021000c1440c048610a0408a440c0700c2d01e81560010316404029480501c0102280901d031458207180b403a0b0030244803052803007541c0303039200200c456a446401250f402c99040c0b807400c070303000365020b1032040c540103d10540c8040380208d0800008004040102c9010395000070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 90290270 1250 90289020 90289027
    0x70f060507031803020703150b090403020f0d0207060e1507050d080603060606042409080708160e1b0901021903020c120607050a0c260301090501050415030308092503031107050105 79
    0x49860100c070f40302240485400d030f07540c44144c105680380ac42e028080e03800ba6000300302000600304c0d03161074025003104004c00d41d80524010050b01f5484000c034151000c0c141c410072091812025200b010f4007455000074000d00031400e5140c4145e9200b00454440c1e42d086040b1507032915a03805006441c81742c0d0182000703a2406815901d441028040d551040c0d04640c40c00011040ea13642401e420400140c01c040c4407500180001120f0f010000d8800000c1c0ca00d213078403e031031420110001a51070405800d000d45110020a4000050703000b4018a0381c1c20320301171034480c210003580c9030082d120717000780c041d03548200c15a00c51000b45500020b01244070707403483e0315468038001d400c0e1030954410b1b0141508584c0f004104900741c2c04030600d84007500c0380b00c0e0b0500000303841c3d504041c0714000351241604040c0c01a40343c01d803000e1030041800030781c00480750141031582c060744991680509007090003026012540f06140741c03070401c50390640000c0c102c038080e546141c02410103120a9844551511400d80040d60a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 90291520 1250 90290270 90290273
    0x70303020304030c020613140907020304061107030206030a0608010c080f01050111030903030703031407030b09060603130b101403030310060503090f0f0610050103090209041106070f060507031803020703 89
    0x250300454000f4001c0c1000d40c50f22019030f002a400fa40604039995400c40d103840200490510a510016a61000c841e080e0703580c1fa160380d00075941d000301c0c4035600401081000d210b401420502036800615006172031940e8a2405c080203c001d017883e8891313001c00e58a0071a140d1700181c860804207026492080d0aa002079103071000458514415800502c4180001c0080d80d00703e0380c0802c001c0441c7c607c07a840210f00c20004141c80b0800820007000e500c00c0c141804262500c582c3c84421181d40301c03404407034940d1640c44540b0440c0700640c0090005180000f00c106000341c401c800d210a0080718601c6060400c032070082c02c00c1c99100c0c0000d44900031241c5440b10113018036400392010b0360b03215900b10704588038504000c1155103001e00c00c10040b40700f50410000e004440741c00e980307010040e00003802c4c00c4c001904e056000c907034100e00052010740900c82640141485070766200c115914550414030003007059685051070402800107540d0040440e04e05507006040c0c0d000045200b0b81590140c0103400d007603245 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 90292770 1250 90291520 90291527
    0x9050603090f0102030f0f070807080705180301090317100f180209100e0a09020a0203030f06040f020414130504030206040807020a030f080703181406070c2601060f0303050703 77
    0x1070041861801160141c680c0020b00b44061845411500c0486a10341010710a82014082c090001020068044100519150441c11164118200b45440c80c1d64070b441c6038210184480841032154103508100085050680c018051004648000c0f5848000c1d11044141110000948030700c02c0c4100c0100703010491400c907182500c10201407035202501e00138501c00041c0c03403000b1903500b840200351300740300c244400c2c10880d1000000c0c3c04100320851a2961100e80a9035034003000b0225074109150000249003511241c0101c001d403003a006007991120744035880c081144c105440003c1c0038241741f0110b080078164034094640515019000b4006588030783d00c9007401ea5100843c240c0e00030322290400030009078500940d030039490180c9442c640740c1c1d510b490f00600000c00d001403500a480c21500c244215088013540400040e411036900e95210010301c0c1401c12080b4541c003101da03010b0301f40500701c010f50502c0005000069004000c004140e2180001c8031010038030700010700014414000103000902 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 90294020 1250 90292770 90292777
    0x7110703031404031a0a0c050702010507020d02012001020c0616080415020702060703050405120105070905060901030e010f06151106010308091c050309010210090b040b100f060f0e04020a090506 85
    0x16604801468a9102d40f141d410303e030078004c440351400c2880030800031200d031184243c010701111403512300c1c1f4100d90b0740c00003021805540c5029101c4c041d40f810314811a801814982c800500008111004001607881c050007034001c41c1250216010380c10000d51204864101c4203180b01e166240c5a180d6181e984549544402c1203041001007642005060090b90f9018050b045e880d1081d60380d269224100424083c44807008425007081e03078101300502c400b064101b413801d415181c0c20b5422586400c4101c1c0100c1c09414810368050895290a003803004520701900070405071000d5038007880c4150588802121481d901503106d09170340d0801001030001030106c0c0020321400c14014207400382d0141c00311100000002c0c200c01280c46a000040084244d40c05011075130929006010800100a40741c0320300440040043c0002c00310900b8200140d400c642c20240d65015000e141c50000840b41c861078040c1c0070350036618400380480c03a601e6140740c0c18902402124088003555442d15032040c9028184911030300b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 90295270 1250 90294020 90294047
    0xf0319080910051b0c0d03062103030f1103010807050109050105070503040605072405010f0503010e060604090f05120a170114040903030204120f0c0f0b030f0411060705060405060711070303 83
    0x2030300e030354103025034070780400117441040042006028802280c0d00041c04031a62584510b04201c02801949030004135902c186440f50303010b05010460b0441181201c0c0100000308500101103800700000c5001c6100180d000c050741c03000e0b00c90030385c0300d034486005403203a01500340001c1c010351007000140032551081d03001d0140c1500c506400300b02c00110a0044a1003158151101c02280e5640d004112005d071415054000301003d400070080c0030200714140303031030300801013145000c0d40c1c0751101c4004103d100e04403600b8041d0043c00396071100b01034526003d1039902a46a038000038500c02484005412607606c1203040364040c800a0241c95001c2c8240000341000b0b0310309406041d4280302c0014101c3e00c00e07074030400c0944686407a03c400c2d030603407601800c2c11086d41c0200c14460f1030384809000d090201c2084a8100750144900f4002c0c2c1c0d9586082038401b202e150303000c2d41010001c070f460760801c600000e529010b84e203d0401e8882a43d01c0c901d0444240c00315050b9031480e540704410030400700c0d005007100b002a2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 90296520 1250 90295270 90295291
    0xd0303090c0f0611010609020c030a051b0d090612050708070e0d060204060c051002120402150d02070605060306070e03190c0503010c050a1b0f0b0c07050f031908091005 74
    0x1d5510585502041c00b00d621203004524081d01d2030794400801c0c481d0300e01801e11811304600f0200102c00e00340d664052046ea000a2040001d00090010300e1148282c0043d400b00e0100c69a1401411005041113040c0c403490010070b030402d40140c60313443c042c06224400c007030b60f6072002125684c1800445031090b1075500c10f5000700500d8071140218140e4001403015120ba0f41780c0e00c101c00d1483c03804906d05240f1a8404d4031492049c820144142142c0250980242d0100c40280c14019500310307404d0701d4882c0c0148120050301c0081e4034010410346410072032040364100d060750826035800c0e10a1b1000c0100000c200c0e030542044c031513556404c898035140103019000310302905480340c1300d00100c0c1c211446d4109480215070040f41d68030003158092840e00e00e110070301c071002c01411250740c0e41c05184a0842002494140c1d2440095001602e441c241c51455404c10105e401104108000c03640300e070f001003c945d489076a601d003e81c4486000b454210300443c040c0001f00440d05505140720000c1c000517051a10701d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 90297770 1250 90296520 90296543
    0x303070305060402280908030712030203040206120a0b0109051c140106050405040506010f06051306030b0d230c0d08070b07020118082a0a0311100f02040302040b010206060d030309 79
    0x284200b17228a03608843c6803400d50700356990144c8003c1c241308142e41c0084c100d507004010001c001030131460400100d0038542409601da407681e200040b11405a04d801052490203082081914800c80c0c200076800030003a00c91005040e19402803080d00790307024041106c01c45032203000f0000100d030400003198102e5201c00010703400380c640c000501a9039060360240c0d000d6010800602c0320031510000d450040c00b8500344145045030300700440d40ea40e805031281000381603030350140424645580a00c02c0780e17154450302610350003c002440d991040e5540c40d02140b03070300c1150400110b81c1048007032082e8003a002a20181072010a0380d50304809034004141d441107548503080c0c42d20301024201d00040e4113104608640d01c4001085105001316031180c2d4000e44070380382c601c05041c2000041a2402354075014070300202400c0c125888586000686100c2e9440703d841c0540040f14014180d0141064920071101400f040e041c9500481e41d90505440c0241e21000c91038000c00068002d601ca178450b94031501c0c511a8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 90299020 1250 90297770 90297787
    0x60a0c14070503090f1504091e0501030c0b030702070b030712060509060d080c0102070804080a0b07090312111e0f10090c05090406180809030d0816140412050703021e030303070305060402 82
    0x4450300141e03c140c4130651113002049c00c100d81040d0b41500019150400c101661454031410907401d000d200320f0064440000201e1202c52003802014043e0100f160b24070350300d0500c043c0040c54034007503600300a690b40c60104041500d280240185010360001042400380321205e444410080e070110501c00400e640c200848400219284080c0c801450120050300070742c0740e03070b04001e40149801007142c030802200c0c83c000d0000451640194503040500d140102c1601da100c40001d141c0140c00005002d0844a103440c0e140d1200e000a44540e02402c45083e28640003041c01107009a900050000f0090560003106110310b080448a641e031080c040c1602188074004500c41c000190b540b10420356841d400054182141d040421800ea12500c040c5000040c03886d1210850b2901c1e00091055000c105101c0390701c0740c451100e002070300c020340254580c41255034494078020fa500c4905100072030043e101c04d4070080a00c2070403a0002c2c007009000c0c0285140d40e803100001c40083c040201501c0d4055400d110080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 90300270 1250 90299020 90299059
    0x50405040302010903081302010f030f020d09080418141501050706090807020a14010210050601030902090903070c050603071704031704060b09011418041103060a0c14070503090f 78
    0xe01807400394000290075299802d0040c40307204028851400401c00000c2d8500507680181c40100b1141586000030303080104000243c041d10921000742c072020305180340d140602400038010400c40c0d200c1480d02a000c00d0f000500410350f00702c014a14008480240091281c1400c46000240e401c0140761203441c01050340d40e0b0408982c00220b042e5040384001c0744000c218200301000c2006080e801c0d0100c130902204100007543c5940352072402180325202c00c080350442c0d00a4014100342c5c3d81c014103220107481c10308011580e9400c1184182c450003510b0500288030704002c400c176805412540e41e51003d10640303000300128070720060011810031088509444058100301d0040340541e1003100049203a070118010040d11030b6041c0c001c00913450050313034174024641d10f98601941000d041c12080308103540342e042041c1c89840080010f901405141c0801034082219808511038051541b02c8800a1900c600e41c0301d8103005044000f0080e48c020008903205140200315682c4030ba400901d403c2c40783d0a03410624 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 90301520 1250 90300270 90300281
    0x2031509070303090608190b270a140702031617030711011a0105120402031903180e040c03140f010213090609021e0318070608010602060f0f010506090a0504 69
    0x22980c64104240900c20142d1041940c0002c25561030100580d06181b50f07a507222201612405010315610131494949407928038014004090864075000b00c041019034103151240d04890305a59146072100e5030b00d001000300b02030b42c016140c0da0b008500f0108091030401c00180d42c0b00c0141d0359050601802d415804c11100103500c03642840d650886030b00d01825901e42035a040307002003202616818141000b85e40e020301903500e006131182c114040d644403030020a0512034981101284411541e10501c00c0c160002217666034a240201c0318049a0354695000da15040240c0700141241400c00c03003040814003092a80d40c8022058003641c030101842070b00d80e42241d0000340c6004034800a11001c1143c960349101b0000180381c080015031038030940f085080134a480d0507408440082021000c11082e106405001105040380c1e0700b01c0d8800b94070f446014115400074440c8400620642d07000421042180148502070107074607134000400c2e428281040f41c3c6421856501d40c000444540000340383e135840c0103d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 90302770 1250 90301520 90301531
    0x12030c03020715171b030c090409050303010e06120c1011150403020601060306061b0803092104031419110d05060a0e060919030e011202070309090e0f0a0807020315 72
    0x1486886100400c0a1392078540061200c00c80641d800c024040b840b40c0d540031aa4049148440903554504e11030011f03006040701c950140c82c45c07001200100e0004400119980109421102100d00c81079111855a48078101c07030140d41c01c800b4408400c15681d000c0d0810b003a2010081c2c06517208001d4140028490100443e8294010380c40800100074940e058410040601041d14119640d141b59240144203040c2c5640c0040213800000000b0310185001d100200c010b440c9503d03858140c8940184460306078115000603a82012103092140300e406d000144013a0045a9800015415010303445140d0f851028948482d0071510540c000c4e000a2800c0c4006413180440341000500c014448005628105c0e005007000f04a90184860b4005004a6030013001700983c1840c00304824400f100040f5940e84c1e260400020076400420702204043e082142d030702c248c5811210030040d00119980e02c950342d00309560190701c0382d080b001c403800202c0c052100514003180003a084851001c0021401d046101d012501c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 90304020 1250 90302770 90302777
    0xb1002060619030317040c0e04060204030b0c0a080f150d2003030403020a0902031b0a0e0123090f040b09180d03021908070e0405070e010908030412030c03020715 71
    0x40044518003010303030300c06907241004a100b0a40c1190b5024298a284261000c004180080007408208448988034080c141d02803c1007464141450990003075006400101d4032000300e007001480b50031180c000c0d0b4102031201d5035900c825440321106990741c0d1401800350200d08001541804031501ea0101d034120440c803c40c0940740304e080b04503a507180c4000128080e8800d40040208001581d544020700f016103511680050f6251031701c114008084a080342000d1800c070003c80e80c144072036000301e041100042d080e2076811840b45c0301e042c00342d180d101d08207070181503940034000d042c8a821301074071050b0b0504001d00300140001080d40004c2d0a270784101c40c029520190000039011201d02400446c06075105810107501300362003200404810014404e283c8100311646001410360752180404000080c0041c0080200d030038100d074000d002c0c208640710355002c039444000005e807428001007114101c3c2e5440e000f0660b0038441e9035085403110010740040c1c04510501001040b035018140e9101ca40b0f0f11140c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 90305270 1250 90304020 90304033
    0x1b02101e0507150203060f011206121a0603010506130207020102011805010522120e0112051504060b0c07030602070c080105090312090a0506010b0a030e030d02070507080a030c02090a0b1002 83
    0xf8200140c105046074850b2058018014071511344c40360104041ea02809003404007075810523010302d80007004994415080003810790511001c2c4044a15060503403019002040703040d43d01c1005060130303558251041a0020291640843c3c20700e0700780e01604c0d010b441440080b50f0600f000354407075205800c0395000da40d265580c41c144040e4010300c010301102040b44c5011450341064945800304210701c07420141e01800700309a07052502d1380c8500180d90b11a41c05070405c002a00304a448040d000119072401c034066481c1c40004540310a010064a80d110070f4040281059130540e601d9102030340005008981940d203038030020544450038000c0e5031244d4061002180c841080c3d036803c840421018240c40500e03002800c842c000300f80c001c610a41514190018140d9600414000314010f0880052111490001107008039590300250020305d0417900903012500403548030307031413a0744039084000300401040f0070440e00b0300142490400c0c594005081800010400c03880f41c0811304000e04403400e80010303003118 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 90306520 1250 90305270 90305273
    0x2010f06150f09030305073002010f0501050102070308041a0c030c0f070603050103051e0f07081b01030501060f03050613050103060c08010b09060a030e010603060e0601060f1b02101e0507 82
    0x41041c406042c1d4941050420f1550b00e001e0414860590040c00246440b6000340080a0f54a046100703106d80380a82e0504000801d0001c1c02021001186d015060800000040c550f100050740d00a030b030740092815141c1850407103551103220350403c09000e140c0003131205c0900b10109102924048401ea006000041c1d0b00c4681789051400e50740040b01490f1420005002094002410b080301c900240c40406100b910301d500d043c940f4004d0702041c8083e01c030304400490741e000040380850006202c1503d103050014080015419528240642400101d41840c034541c01c901c613820064100b01c0107040303980c0c5811180b40c101c5c00e6890903081960741d513403182d1180380d040f0f40c030056030f600428804000e2428404000001051031180300041020540ca44502e0960240294000300080d540b281041180700503041009403513000c01d10411f07003c1040c4a0740300001a00840442c0c101894124115099403120780c20420018564110f09082004030303151340c642041a001d071a900e164460326980d440d00100d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 90307770 1250 90306520 90306527
    0xc0304060f060b04090903020106170d03051e040b151503061002010e19060b09040c0501020d110706140c0d0e0a0501030e0709091e1a010608060906090702010f0615 72
    0x10703040a200070315141040250100450070395055070580000071861880030f0404a014054540001009502012254100000011300c1451900c07907510705020795a1150360006611080661100340d090031500083c00003005c030f882c01d90748117120b100242006000031011400d4240600c089201504000041c00303420b10b401260f20460340c400e88000d00c204a02100d41a07200c402d01002c41d0482e40c005a00b11081000a402c50800f440024029003840e18190400ca142c600407485864058080c041c01c512105124504010b8010b03032210090940c1d5280c02e004807140d42c01450b880309880313803c1c030084803075040030f00203410002c00a40e103042d803051800c400c2100300d2400e9807009041c1031034801e100074400340104010084a5000c00c000405c601c0b030341008000001c00c1c8508041410a9410b01020050340c0c800900041075100d0b42203c031390b80c80c1c0c00c054950301002e44d0f2003580241342400256061510300d6005038840300610000c161107442201c20303000d80da5140c100c107035050b43c011451071700c1f642d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 90309020 1250 90307770 90307781
    0x1c090905090604020a1e0302041103010608070c0c0b1602041b0e0102011e0b0105040806070f080c0906091207081501090f1104030609080418051b0405030d05030612060c030406 77
    0x1504050b05450038950300255a408544c80f071481403460844010030b007012070f54190b6004503009802404041414403260002c2d82c024001c00c00820440c40c0412041d52180002d454400c0d032029082d071926050000c01d51180c0c001e05401d60803050303820310540c01a21140a40d801c1c5503194010010480102c91015182050a29005045a16129458030303100142c124800024286640000c0c1801e44400101c90601c91504540303000c0c4500c0050003280c80d40b01c1421400d004203039540e44120303103c1804c0780b15280704d0612440e0303000405000c80796580c0380c14200e14030000410421264160364440c40d09080a02e2040705981c4031420000411100ba4103002d038110300d420b03444040184089141411000740075600020f0400da580749106070400c50346000301d4000e000c80059110000b84060b8004000c0d040c100d5092085682220052840e80b0488d41640c0681d20018094002444c0c007840444854000900c8583c0c8158028413080c80780409226003400341341e0b19401c2c6a500d1819052240903030f407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 90310270 1250 90309020 90309031
    0x4050c0a0b0d05011a091509040501030503042907021c02221d0601120f0632010305060106030e0a080a02060709060e060d1e0f1e0204050616051c090905 67
    0x260303003800404c5c0c0100004440c1180f10403203480308628058021485540201940d0310b070880e00e0140040144000040a00200ca156041d4012114100b0720a44480c003081141c01000f0102480300c0001440c1ca5508450f08140b0045c11b64211141ea80000d110b803840c20301d01c407000c00505610318154007150f014981c904000d50400c0040074084408440e9038984c1441a02300030180140104200714007a80700f404016000202400510400d08103000d88804402990310a03c100326030400c61100900300c3ca5040300e4000c805440304d13030320b014003c1d070292400160a003014000d072140c650006a169000c0c00740001a40d004141c1450460800340c0550078a80100f006c3c84200031072050941c2d2800d0488210001d010408039403902e022840124400340e00e03510064082c01c003024a4011112584100c1c00103200030340d400c08005002036010128480c5018981d001001040ad00c180342c40c01d05104101c40d403184044602c142201031140c816012503244490004040311810444c45035140603071a00b10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 90311520 1250 90310270 90310289
    0x6150b0702090408030403051c06060e030109240207050304081b030312160e04050906040303051e0103021e0907090e06010504120311011509060f060306050d060504050c0a0b0d0501 79
    0x203025030002954000010402408414000005070406101e041504c944042c107140c1c41a51000443c01040038207202d00500c00015a460b00b1580240380500440d84116000b400180003d0b200d403001c0078207100c02070858a2601d03020000e20000540420060004207194400b03490501d041c03c4104507081502c1e91702c280700358400d001c4810402c10203100f65400c140c00c0800c61901c0c00c468441501da0b0441108110b0380300707142004014030074401144180c40307140700b41c0e0b00300400d5803103014104040e544003400c032044104400040c0010b00f805200d00d144072118202044d000c0d01c0782c0c000a80041e2080b0342010000d44c4054040182290502d140ca400c13040900700b250400c4d0a05410280544640102508024010000c01407036482940003420506041940c2036a40d5190313000e00001c0e10aa2090040b12560032100080242c403d210704001c2d01c00040413040f00c0000354513094081c207409003054506020700b030f45204003a40c3d0401c80100900c070446a00741c81d070000400da00211001640f003100385 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 90312770 1250 90311520 90311527
    0x105030304030b0106030f0b06040b07060b0105030112030809030f0c07080f1902061803060a090507090b010f1d090a0903020f0d0e1905060d05011a0a050a03020d0f0906150b 76
    0x2540e0f22504a041d1115071400142000405410070301034451107004941014001502042a06902c070040c144540251800d1020f000c180d001141e40307200c2407058140c552021079065001038841e83e007150300319215004980c2040300072030b0414615809250800300035400004c3c01c1000345400d005d03450300c128010300603000d1040007024003040c00c502071500900c06c60300007400c114468046496000b8500014045842d0b80c90075468400041244040070740f0603201d0400c0000303403e8000d000d4484005810f039502c910f5410540f100303071200c0c1d0122010324055410620440d196480340c0f02c00602c9410405d401043c4039055040181c201240c1401090842d00120320800f03015400000070280705400723654280e1031180c80044103880c050305401c400d902440008024104103c01d0b002071b410f0314500e03401310614450700a10054a40b00c3c544000c030102e44140710450700b0034001d6000c4c00041945000202d800d038858481c95044400f0a4812204143d55010404017598445400c602a000f4418550b01c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 90314020 1250 90312770 90312773
    0x80105010803040b0c1f1a0d1e0507080a080d1a0102060402010e12060c0304060b030304080c0405130503130906170309150f070b01090515010815030f0703080909010503030403 77
    0x450780b00f00d0040c0b0301c01d03600002d072400110300204000048212883d5440e0f0340c64070a20019005400c0607880c1400c151440040840585482401032a56a80c080382003003d6501100c61000e01c2c41c2030550603280c500901030300044c510000d000064240303228040c83d55840e000c1d0110340044400101a80c8000b00160200042a0340c00260860f0001d409081c20f940c080300300c1c0b001501807070091408040600640042c48651101c0c40055401544960001c0c00070041007003d242c0e8a0040e4407c1003925400b00c1c0e24150720381429803105070011842420540e130748126468407859580705d9031004000c8030005408204464103440b444d0041c20034185040c0c1841510f419560307690141074003080c410031403202c400003221070020440e0009a400428a42c03542001d0529003e20542441000300f000d04040018114400341281a00850b005840e021a40d4a034a101001082e0300044460303010700c254948610a5642040120011031003020700ca03903181940002e000b400181030b07010f18041e0344140000d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 90315270 1250 90314020 90314023
    0xd090302030c010e060d0c020304030606060c0506070c060f0c0503100f050d08030907081903020601050414040605040c091b0e0306060625060204060503070305100b0f090103020d020d150801050108 86
    0x699034102407034500700d4200d01c2ea0000b17005100341110307051901e14010041240b5034021025001304e074020401001000e58544050302c0000b00a0401001500950001606103008621401c8001c1c0114400111051140056803c94203440094070105401004000340d1101075008103000d400d200c0d07800004030b46030a011a21615104030010043c640110002d25031003420010007009100d004100c802c0303031041a607030041c41401c495050300180034000000c11103080a015100700540c0b403a8040b98030390b81c3d03131300c58000034240a01304580c2600d14035030004042c2007078003614014100b611504424004403020280002c10702c0d054060107a00302d582008190b50350002a25140c04c20070302e64075944218980012494a41624000c1c00b5500c0400c020400c26072140103140704010b642c60420290702c600c07810401203106c6100707217015110100314501260042c48054000e004045c1009400e01d090100540d0598001e4a51a8074050391002010084581c0f04140710007020309030000c0040354103045080307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 90316520 1250 90315270 90315283
    0x8030307030b010e330309030409090201020f0607090f06030506060702010c140d02060a0f0509120a050405040e010c0f050a05030106030b0117040b190b06030f0c040e0f010303020d09030203 83
    0x5401e16580b51940e81c042c2e40600342000d0004ca00034042440603102c400c20414030f034568800e103080c070b00d404004031001c40490170849005070200c01c01141441d1502100c00064030700c2072801c074118000d050b403501d92150100b00007801500d2580f035801405003050348a204a6426070702c51400c160500c000e01166441c0d41c0c0444040719020701c3c240e403a07416103041502d0049018040e01400d403141d8502c0a4440e58040340f51401402080c006000000d02001c040d0207883d8266007005091300682c0c4010362002441d0010500d0782c031142800c42c20315951300001001c5540a040c1320081341d460300ca4554001d0b620402880e1006c069060641c03c20b180420000c225002c1401104185941c5011450f0a6030061604a1041080840000032403915280240c45000c054a2020008900303121003640001d80d4000c0c4c3c840c001025000c24115035400c0c0d45400d40b100c001d85072b000c60f45810000401c1ca08102007815208105d0105491125491407400074030b840d10f007a0b0300400300045010144010703640802e64 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 90317770 1250 90316520 90316531
    0x3040204050604060308040305010213060804050d030c0306170c030c04150b031b0a020d030c0801080d08101a180117040b15060a1d0a08150403020304030c0b040905060a080303 77
    0x4042d6030b100003090082130250006080d00310080303000000c10805400604000a401010812555844409032807070381d020380d4000d145030030002c920001180700e170740141446072103445d0214941c2d9486507000d6449642010501090700041902629400c00700000500700c4003d440030040d40300080b100c500100414016010012400400300e0324103107041c01600d1412528446041e43c031402160b01035503804001c812000401e00303100c002c500e045d00450095049074402406800c1034480a813046600c0240148048800c0d9050f4901048201e0b9080c0795010342c84505040315070b81d43c10640018603141403a10f045040050144031043c1c0c0c08645811160800d03070004140750682c50b010444058840e00300e40b1070390060008503c480e000c1d0303400300009018900001c210742007041420f0503c424800180141e00c59503100c00003419007041d0410f0b025034054024410307241020340380d83d035500007624281e20180c0c0390000818188109021171144540240301200c615403d40e1400b030829440b808010107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 90319020 1250 90317770 90317779
    0x2705012304020d0f0516030209060d11012609030406021902130209030309090901050106260f1f030302150105010c050d05030705071506090c020304080a0b062e0e03030a05030402 78
    0xb6101c100103204d2148010964800e06450038066544405621408144021f03071080a124010940a04107041c11119068102c02e046881c684030301c0044d1040d000d0303426141c8105078000e042d082d4002000c06618000c80e044406582c0e80c910700070000703141c2441c10714009203600280f000100140e540d020a01d001d03401c0b0040c00368446c210040060b02f14000d515180b60030901c1c0030200301c25000194415810303500b264690113507001d041c030703400900e00896036081040c500c410004a00010702079806258801980d40d500c88542d424600c6103420042240d0080300940e1200740e41d18040000440e0f510701402007807900d1001c0880c10380760990b49100e00c00d11002800400800315070118854411203c4560b00280e10715070400c88040c4200080006100e03000eaa6450900c414001c81d02c08012501142c941100500e184142131f01d520401d2400a030019622100c100c00501c40f600f0000c0c4807400b4407068041900c880c0b000560007401800010002612a400801c10020380c144c218082d41d4106405070b5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 90320270 1250 90319020 90319039
    0x2090102071a030a09080c0307030c02131413080912060a0c0539030c0a0605060409020918010902090403020c090601031b1b0803010f03170901120b04270501230402 72
    0x14910790a2003441f04940b410f001c006440c00034950000c01e41601d151081c0ca81240c2c2c060b086402000f19900d903114898040030460100c2d6540d46485820300c83c21f03000e03c00b030342d1411061100040b1a80c601000000451b004031040100014492003101421092400d00e0351510710280d0314600c444101040350a651802c2c1680050304032405242c40030002d030004126690744844082d0503503038104100c4101c0751a07062100050b554101406407520203a406421008039441e0300e02913056031100310720307141d5096685400c000c0169482c102c050b070040c0c1c003030703009400c1c8003da100902640a8004080e281414200100580ca403821f10740f0040345100c4901e0f0102946034103072040720b901d862401000d8410701c00880003040101580280a0481c2d128210050030300300c1c42c1c2071100207800f4100d0041d000c40d600968048180c03840350800c01500c2c0004000041400c074903e44082085d90000389d5801c4103960b1040401084002d210380340041c0042554807152403000302071200c1201d40100004c0c0142c0d40c81d23 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 90321520 1250 90320270 90320273
    0x106080705070c0e0108011a10020c09070210020f0702090a0908040501031503080a0504050a1707091a030a051e01061a070c0b12060a05010804031211040b03010902090102071a030a09 80
    0xd288402501134200040303d40c0d41d40d00750080c064081c0b4464070420703010b0368900b5412460076403204020f00c584c035009400510303240d00800188041c02807142017507002c0c001e0740341000e00c0240b00500c0314070304012032036072225418010302038600c034014044980746203043d800320040342c441d000b41c0701215424039020030301001d2526024400400d0740d00c000c040d044007050a02001d074004001e0801d591050f5200c9407480c0e40d81d0203103440241000140c0c104c5da0401b540a1024141c40d40001c80300301c0c0e201303040c1e0a24110030b0002c24a4400b40b85c3c415a9035402c640d24007007000012094140c010410352000b81710050a08804d07600e020f800301044400c401740091900200b2480e80902401006925003440d1500504480009070b400308a039900d114030444840411250702170420301d40240e1305656050b601d401040106802040d90710710304805104148030002d031441e03207140158060108520f025803285e01c207130006031410111350000c56606200d0782613a0071078012501929070102c046c6d0350100d0188520b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 90322770 1250 90321520 90321533
    0x10312020f150702010c021203070f0507080d0e06070c0816061410030209010b07200f04181401020a0c0b060109030c0e090f010c0207051905030a21020303010608070507 74
    0x800041003000d0064410034495038105202e031030711034041600280003401c5d14200c1240c03204a0702c04d0b0781d9070a140a00125003030350f116a80d01429400d039414010724015080e10382daa01c1d504281d850310f060725120302910210300c005000482c0c0100b22410b040c80f10f48000d42d40e181c06406442180c1590080130f042e854280080b43d005686800c8409550340700e5400e0071000f10b441c8250384d00040e8000c074110030001540c0031002d42152109034224103040500100807010b6407821009510060f4460000154203a15070755501c078040551498070794901c10300c1a0b6242c00c40303000180003c00441c50b4814001e03200d00c0ca030006494000350340d100703491550582c0c0301c5006030748412444e00060801c0c0e01d6040c01044d40d4a803010964006d40c01c0307004440c2c1001c00c0801403070a031004003103090700503000920200100c1c00d04208040c000c989000000d03102c81c0d1034401282c42c000e4a04001d4405034400b03140740d0400401004e0107034500c030580c0301551640d030401c0f401810002c070181440e1b01f00500040d1110030f2008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 90324020 1250 90322770 90322783
    0xa0504180204050c0c0d05070201080112050f0601080706020610080d05070606090f050a0b0a0302010905120708010f0207120801140f04200c0106050306040507030204050702150a090c150801031202 86
    0x5004200304014204026415000c2e0001c4e29040300900c60101d2946c1c0441c000c030242c40869905035140082d40c2c1c24420b2003015002c0791102103410744120810407401050500c80d25010700b00795070007021072600e0000c00a04c0d244000d012020007102038001440424404610b0100e04841410099901c060a14000c0010650340d440f011800b498907846041c2d81c03d00780c100c2e9005d162000e00604c1000d2110302000030105c460310000780810021001000203084c007015881e00b04159809668800380d64107440c0e03003540d900e40000ea0703003140c5c001512401c20070020580c1c04104500c0c03030040544d40c140a4940038100081001600c00e2503a41812507240e5150740203500c05240c1200d01106001100401c000543c001c110408407550800c0c0340406c080c10001440d61151f90410000c1080510790b03003c0c04028200602010f0850080700d6000c503101d520044298015401448000381c2c41985007411000b84880b134000506011a00b40c00b80303c030f0355002914a054a42041d500c040c040a0300006919001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 90325270 1250 90324020 90324023
    0xf120301082d0109030c030f030506030d111203010807080d0906170c0705030c0d08010909031704051c0c052b030e0c04060e010509090309030303130303140414010e010b0a050418 78
    0x6003040726070020580d0000001080e140300352038104450100c48e200398184d480c1151020b405078000c10918800034824141d12990640510960309811002c11001105034401d80050502d07900c030b07510410102c0e204009070301c45000c061600c0c45034a4282030000b000c0041d034a1518a00038015004a102d20082c401103070761560784201281d50385d070280384519460301117040010340070500c02000060109994010b143d240f590540e20301601078007000c95150f00e41c0c0c019000380c43c80e10405009032840044510982c44d07000480d12508100d2401d464603038603001054000c464002c1c1400726a5018010b1084031582207078040c1004285031041111451401425a00032036004d4109440042c1d1080044100b0f8140d60041e2900c903541e50316440e04907600c2c41149a0950980c4c070030030000311042108071020b80312038800c1c0390101e5141c0d032880ad034000c040015102a541861012490301c0d50b41400d2040300c003a85203180c003c1c41404c03d00000521308007407911449024a4445000c2c11818004418070546c0030b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 90326520 1250 90325270 90325273
    0x303110304180e010f0b010c081e1b010e1504020607020102012711030a0c0b030a320601080702190809060a0507140601051c06021b0f120301082d 64
    0x400742c0312a6020b0000d0a104903510f502e4540300c5442e81c5180e00540320308400c1078444444074006551190616886400c09451220000c01d42c0107880c6c000600803c0c52207403401c030984c1d4a2041100e003030308540001107144529070000400d170f034012403c203880c07a078010340444071a52035421500060f805041f402d1009020784030303000030044200244030107a21038a0b001c4c0040044642c422070515a03034604581d4050944411354500b00034a80c507040045900c0036407244042275034031450381c102031700c80d42c2c00c0300f00c1c07a000d4001c10000301d48840780b003200b640c002c030246048442801c0268000e5103c10b0300070308a00c02075001c4038598040c4903844003180c4540c0c0001e0011941c5016081e0300a050780c00c9120101e071003001022442601071000208607040c1c030b4006100c820064820241101c05003986003048401302e4003840108140c4904440003542030424002901d60a414070300040c3c1012104101034280746018401440449000201074004140d000076010403103103051201d050f0080b401441001c070303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 90327770 1250 90326520 90326549
    0x10e0906070e300705030a0c150c120206071202030411011b0b0c03010e07020601180f060918020a06021216030e10020d030c030908120a020405060c03030405060109090b010303110304 80
    0x40f0100b98855041599030201074904558455013019265000c00501501000325a00c00b48030000c41c2c050411510311280c10502e502c40c15542c0d0740d20011071003210300310140c0c000d582080000c3c0c6e00a01e07582816018583c0031460740c5099a215034080011401d0a41000201800c0d0703541c07040360110664107513400000303030504c528240840030429071090156240811115000c80c50b41800040c200703059030149502a230006900341034001c01000c46443c0d41d040d90341c41d07000c00a107006c1c29205103c000304250840c0c940c1d15150b070052219825403680048119400035120b801200c004109a039109405404103c903500d0442c00c04a600d2000f00c10590b5001c541088108210707038001841000510613614188494049210180c044030a0050301a014510410001200f070118100302d136401040c0d40c0c170041c2000d0f1103d0220b64030780c100e000c61a015900020600c000e0cc01c0411000b401424054010322826450b030340d4281c2d1107001803000805001000c420709a0002d024030031340340504202030030581c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 90329020 1250 90327770 90327829
    0x1110717010c0302070302060c0c100609020a11031606092607030207060f0903080a120c020106060e03010506010e060703110a03080105041802010206151201090c060206010e0906070e 80
    0x100030304008100c03032096207045500c800d003a00070f0090355155601a0040c02c519a51406105000e030301008524045000d1000c40010801184c403c80c3d0141c0204200140c5400f01c00358058803440013120704a88a070b0040c4228040a5030301058040030a5100c000425041c0035890702040c4000c031000c40b607880c1024555060b8403600f080b001b0b00f12640c0070740e0032a2140380c1d6640c029a24000a03210600008613900810b00101e16104010030020801d8a4040c03204514190f00100320f806211040c80140d440c0c51042040592084105940d100100d00800203814004000780440300002e11141c01000042113480605010348650f4001c4000310054498040d03181c940140a5030b403d00807144118078280d0404100c81c42e00342c9403070740d041c0c1c180c006140685402c95500322040e10840c2440e440224000e07107203207503e030038068030b22068480e49100070030b60308208000c2c2c10503105810940040550400304100390f0790004210782c00044a01b420291041104040761980b000007010410300c801342c0c6609038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 90330270 1250 90329020 90329039
    0x30106030f062313020913020d08040512031317030f040e0a110a020d0e041104090504050c060711060d0204121b0503030a021b011e0306050307051507030c02011107 72
    0x4010f04140c8114000c103d0186106803a8540240c50009401c02c880f1001d40c010b0a001c0125500501010074500c10107101c0d60000b00e04d0b103065002103034180780200f420000d0742050300c11810031710701c208080c50420008059001c07084030244035171041d151001c08480315822052007103460030020503214079521920b501c102c00e0b80140c10b40724010349070b00d40b1718003010760350303245d42a1000400e00340d01600b450300c0c0c0c00c20116000c120a69039184d0280c0e9460040c05103588e420300a000500c035001c008100c43c90141000c50421204031003150003480c4c100600c81c00030740503001c1c18000e42c00c1180c41984800e0b00d00c0c000d00007070203217420001400790812032038418001e003811410341260919062914464544052644a02907241503102583c02083e00d07064001401a500c810034406161041c1425215520f00c51030b060424148000b095507440c003842141800e20100300a03001c2500c03018406a0042c10050003071055517800b5080100e0180602e04681c03051652800c140b0540d82201c0b281a00c40c1940c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 90331520 1250 90330270 90330281
    0x2040312020d1209020105090d061b020a0b07020a030503040615090e0f1c09050d05010e12040905060901060f080a1509020409050609060307060f020f0303130b07020a0818030106030f06 81
    0x20114000c04004825645640100c602c070170f0781a5034013801c0240b18030903c000202e003080122401526401500341c50300391809208034a40d4503600034a0b4500a50505101c0784001038490400c40d00000040e4011079040007c0f01d810982c810400691550908a1009a0001e0741c102c41c803181d00b0020384d07200c0501d00140036100c0416a405a81240d4185190a02c02c0342107202c055010940c0d9600c1040989880c1d06c40d1141103024000209100e6411608030f4201108080c008500714008641031180702820700c50074ae40100c0944120b030595050010141ca90929401000300f0400c20340001a100c01c1281c104203038003000c0b518406900b0f0f0700c8401840294106003d80598245032030001000e03854031080b8540255000b40c0500303861800c0041c12146001011403031030940c451788180e80340e01c2c80c003000214800c04a100381450903510602e80300001e40750181600c0115441000c0e5140441c100e4811107200040345a03441e010290f203032002c81e025246c190300140c42c0d4070818031484140942600074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 90332770 1250 90331520 90331543
    0xc0703080c060a0b0a0909050a0f080c10180803040f120801080c0301110a0507020a0e09100b060910030518120a0f0903050a0f02010302070b09010b3c040204031202 72
    0x1601c42a540f0300041c0012581d401354900d50000000b80b040082000c2c1e5440440124081c400f030307561561882c1c54540301c80b82c0041e812101c0c403400040184161030144282030300e400c0500c4092081c0840080380b200403807007980000c0c1012070000f0114080050240c031240030700d41d000ca20720f41d01100e5001c0c0981490024419144140903000d0000d40c1c900e070600c80e40700d007520b40c9600c075030038603804800442d40c176003004034202c3e041509a103001c9156190100c00078481c0107420700500c04070400c0610003040e030300302101c024014041130180e070003e543c500507600030340d82d841d04d4001a00d0391903400ca41502c50603036101e41054018030304003051641d100802000400300300d4460038400e944038181110009c0d0b0741c0c403028165402c8501c41c100005c00d913105545110380140f40260a141203a154050009010784114880b07079900c0445904500306503820440f4400c1e007100c032030486150400300140e062080e0002c903080d004842d0400d200b40c2d0710359058034095504414484410202020084d42d9944d04108 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 90334020 1250 90332770 90332773
    0x34110c0102070602030d050a060b0d0603060f0b131a100903060501140105070305090a15020109020f01050c0c04090501090b04030c0c290307020f0613020a050a05010206011503020c0703080c 83
    0x6060035400090203000b201c2ca168025880d041001c5902001000081c00c6006659221500014589455005018140005200007402e20328524006003101d121425121005060010512450740c4103581140c09001d14000410011080c01900040503540140950b01200c6e00303245452450b800a030071001c0d240f10f14000c110990300c45002c4066002c0b510038090000703c3c200464000607100300c0c0608100324001e01000000e985421040e18469422007003400142e40d00d82108c000c0d894080701c000000303c02070821030326018a80b200e6940301c1220301e5006014640795898003003000401d6002214aa400c041000e034682094903005045989448044e41c03144070050b03011942c07240118500040140c1d454850b03171100f1000e0007513066904000d00030030a500400e81141c1c0441340030f22a01e03209100855a03080070110342d2040005004807504070714012841c80788188401d136000160141580c0300c20410004055840740114040c1c07041c000c00800c00d00a00da00002004448030113403801030002c80 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 90335270 1250 90334020 90334033
    0x50d0f020409020909151c0c050a0626071d010e0604080102070209010e0603030910170703020a180311010503040f060608030306011205090a1101030f020f0a031d03033411 75
    0x1c1c00346d590006c650742980c1c1c4040c00071444844480c0150070300880c00e10510075210030540d900005000740032107501010105000351b210521a002c258a2000d08800d07100814a041c20712000080c026030b41520b510104039008040441c10343e02134110103036203d0b00201207a5582d5181d5030a54040d41016600b01d01a45584002041500b56255041e109102c080c00441c28507140104200a94407442c4441c010700c502d10310b0002c061001d60385194070402c5240c40150782c4040480f8024540d1055007182c41802481d4076041c4000341c060f4030401600740d03007480d000b40c40e5240c070304201500044910000700401d14100000885650100c0514401c5d40240c80310070490075000c1b038070000d44008642c001070a0b04541348600c001160407848135510041854001054922104103000b240d11904800515002c04101c3c0701c030f465031500910400000c00c0800b003640e00700c1401d0180c3e40e80000b46c45d12031000402c3c11000003014808568080031031074144207035048050850080c2190700030941071002d074000d45 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 90336520 1250 90335270 90335281
    0x5060601020712060504030c02030a060506010207080c0a151103040e0709060302070b0402040c051606050108060903070302030a050c0c090408070204060504020910120603050a0506071e050901050d0f020409020909 93
    0x412001c00f10380d000180680600c900c0d65401c0020400117104800f809000e20821003d1b032000c0100d05500f921580d030000d402c2c28180d001a29140b00c3c0e0748040403650085500354119101d00c04048101d4041751048448101d850f40140d50f0040d01e00ea41aaa911010900007020540c4024140c05640f8503260312040072744a071400c4003680f146000c040c01a01c4c0c150040780c01410160300c6403c07041c82c02c0c0350503818002c020a00e21a82c0007503920990301c164441d4010301a40700e09002c3c840d00000705900841c0ba040c600d5502940f00d008883c003440500c00007044c22042c06d00244110300c42280d000f401d404d420318107403908100c2c40e00440016400369190000120340c50500348221290240d00424002c4000c540f1041202d200906245c800082c0c2d840e0725001000880070426a50341c01d02c10f001811107450301450040a84e81c000d10302c0510356540024141e03100f0f401800311050a2402e181003030392070859600e25009094822040e00429100250000d204103155000d03248410046642c0212134617103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 90337770 1250 90336520 90336523
    0x40203181c0e0105040f0b0c070e1e010b0304030f080702030d02070c06020f0f030d0c030b04020a0906170f07050a0c0506011401260c070c080d0f09091506050d0608060109090506060102 81
    0x200c1c0594030611b512424207002074010b4601400d5424182c504941e0341c542c0701e044c01c104080e419286191100d00030740c010250400382c0312100740500600c44007507040d45030a0b10000c00c080c7c0a80032010034002d01a000c00e045910034411210010b4500308159592070042c40c003a00b28460314428000140624414100054004240718109100b0700004609000c0724001c00c0001b020090781075400d143e038803815000e81d40c5450000d03108030360071a195a85e40070325004010300190410b88210140122407c00c102504111910f80303504448a07180594a4406100050324041040035002c3c0080c41000c00020b404090a2114483c02c042a0303195110b040002d200c0e0702c05884009002e104a0600d0f500084c04030f4044806085120300460031204d00554800060341071405d00700c1c1c031400189052038046d00d1503170800c031030a009080c07022082105140c189111007950071140a1002084000120744041c3d00c0d95801450281c0032079801d884a95a44005030001804002c8003101d25014110028004d90700 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 90339020 1250 90337770 90337777
    0x4050606121509060d051b01020102160606050f0d05070e13082830090b0106021005010510020a020d02040b180103060c050f0a0f030f0501030f0c090c0e040203181c0e0105 75
    0x10302400502038140c00102050090501f9006c250442d0760901c078054100581c4160f008515021306800a00340e070802081c0806212031044113030084445c0310051000980c0064203100b203c940c42c0f0804130369140d900140740c08010140010b0540c0b400801c64030321400c4040302090740e90310000848414040c111005071030300e021038002c081c4850151018240c003407612804c0ca202d01d0341402c4002a00225565500100d04e1083c2c2140740141c2c040c0340340c0001496107100c0c603409004101c0c0c1003208558034000013980c415614100900840083e00e400c011074659800509442800030014644c0781c00070b40842c003090b0024801a02d10600704018104864000c0c81160031a8000769401031404048005c2a40c821120350219001c051340c45032000c540e44600d01c9154045c5100d2070840700102ca050034003a00800440e000701c00100d26004259105c10f41107008801001c10a440260726070783e0302640700041b041a0040d041c1c4034003500303480e11100c04c40014403410a074810707210001240c3e41a80112100d01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 90340270 1250 90339020 90339023
    0x30f0b01050703030b120a1a06030c0a050402070201030f0e0a031209170705030f1207030c0306081b030705090a09050d0311040e0c1603090602070603090b010504050606121509060d 79
    0x400410000c000f09102e034203c00700204000c2c00e6081c3c4002c10003000f5180a407180f0064907500c00c1500c2200c8540740100529401032411002802c2c01041000012300003003051045a1080341e00088680469009030048007540348010010808081815405911414002d00c204c0005210781004001c40e121031042514841e00701000320300c2c110609c0c2c0460f200368001c0c0c04c152210301c428010030148500b07040c0100302140c5404040940c904042c0c0300a0280d0321040c0020081c142805000e000b1801d00103075081c18940400e440301c01c4907020102003800c0002c5038008a410205050401440750384ca27030040c003a0184580102e40c9003003102d0700210100c079160300c0141010300d000c200c10044407494000c3c0c02e0304062940c01d464074041001d0150802c1c2d0ba1341c0f01040700800c040081c2003060302d4043c014980240700324242401403040b1655421f0310410140546031081c0c0d5a01c01080b0380792182c5065031095001d0303011054150910f00842d2240b03c40c00540284284c20440004603241807540740c0d0b41810307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 90341520 1250 90340270 90340277
    0x50f0114041101200303090d0e01081b09040605040203100f1203021506040f05070206060a060918020a021609021324030e1c0c05060603060603030f071a0109020a030f0b01 75
    0x140b900d000445011204a60883d024108200c0403090342900340b00031409441000c004000c20508210090070040c5250b41090520032020200517040d000d054081018403005040c01c0d81d500007000006000304029001f89030424804801c2162014070004610160743c103140490103103999542e64030204d4411040b000340180c102050442c0d205800092403604142c00400101d40207541c0d0707540004881e012900080103030b002c9020b0119604110200cac03805407402c1d10300f908007241040d4058560a60540c034170088258002603c0b1842d40c42032104081241c070745881e0704c991382d40e520764200181d0820650505031940e2040001211195030244400600140c2c601066018545c0c01c290014800f852518996020384501e803078503401d90380ba076503101da0002c0d101c800040d11141085454104010200b500943c0040240074807039034008199100240d00c0503600d036440580d8604000155540034155a80004042c004110161681c000d03013801a09075070100300954000c1100341c01c1d40c44c0001c0c000d020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 90342770 1250 90341520 90341543
    0x1903030f060b090619050f03070206150f0d08090301060b040f140a03031b0c030212030c0f01050403080105090711060a0905190201141b030c0a1b06020601090509010b030a050f011404 80
    0x1030717a0341c0f00313419192042401d2050520105009140e866881190301c000181c01500412030300701c0060000e090204000c2e52018007900201c80800d136a9030700356a003d00781d46c401080000b080d903001d40001000d059002d480b280c50741e603a01032202145e0f00e54000e904100e5902e04240a82d810b140d610002141c0d010f0380c40e110750032412500001181011581910031026803500030015880301e003001c80703000000d1401140d481004141142c02d04001007142800b59040009020105e076004034004c1c1540c104650054032600d443c10300351090000350322110b40074050b101c10009400c3d890703400100024050401e852035070b0140c0744014200c1411000003800300315090075803a6415210409441c841325900030340642d100709454a203182d5001000740c03070305603072142c2040001c0100710718075405d0f402040d9042d03404207810004080c5d00d8240501802c200a80e8500000c2c8201e8802d42080102e004042c0680c0c20001d800e042585d100c1d028803030707001c40660a0810701c4002c104030b44016880349800c21001e465 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 90344020 1250 90342770 90342787
    0x801150c03021f0e0a0b0a0f05010503030405060c07170309090106051e0a031e020c01060e0f06010e0f0d05060414070f0b070503041a0408010f0b0105090906031903030f060b0906 78
    0x300b52041081c2d400c3c080d0341e00e441c01c0b08683e81c01c1080f091600e024403c1d01c0180d181004080c810b644081d0201840d0310b08000c01003000d03031030000a03102a02d00c11110540c4075002068905d00d088030031740c400a000c1d0b203070718206540b144010008210141064070b01c01030581c0c071910285c881d80706070030b82084040642c0703c100c804001c00383d015008903d024031b400b01d409040081d4148101d030500654a0700310740d0008400490ac1824440c0c50001d03c1e6909610b8036915040b443d41000950050400d03043c8044035580074401d540c0c40c40356904001e40100740c00c880c1c40803030405e40c3c0d580360201c4007242c05015040740e20190700800070344c0e1000c0303440c001504500c403403c002c0f01c1c0180c0e03000160203c03260300c002e01c070104003000e09007640b2000c01e0803058001d440e00e24204078070342518084050040301340c2c90080342043c10b99000c012607440c0a0140c2e440c0c0c03019124140401d141070418220220b0081140e0a90400c040e4181c02c20864143c0711403080c005551250000003407446588000ca6200c48104204003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 90345270 1250 90344020 90344053
    0x40e0606010f140a05091306030203060a09060603080403050a0b01080105010b1e0d0c051306031416020f10020a02070b0c060103140c060706020901081b1b0f0a030801150c0302 77
    0x100202e0186000881014401d01084040d0481c10001000c9000030032128650300345080d01c0d035440080702109008840c80d41d000b080c0c81d0070b400303800304a00302e8550030b048041c04140e8018030700548c1c2c0a5000c0350303903c0d51ba04200d5200c010b03140c0c2c11215210382100000f04001c05006050603200c840080c9071401440c00c002201e00040d9000c21000c0000c00d100201c628940c6115000c1500c4545d06c40996a03e00440003d20544268103e00b0605203403500305050354510401c0c690784807072100f510110803503c03050180c3c5800500c2c4401c41d418440d40708280320400041c0c018042990803034007118200e43c9c440c43d01071040d000d14600d0310b01c0d641c065030041000c50714030001091601c1050b401c1d201c0394403094010404540c07024400f6203038250002290811968002156948410340701446a10070317200740300d5000c5612444070b40150401e010f0224100340300f4284047e81d161070580c000c680f8000c40c24a03001d018a5000d108070003080961000100074640104044000d10350f056010745207010410408a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 90346520 1250 90345270 90345287
    0x5010803030c0919060503010807090608030703120906060902090f040e030a0c032313060c050d050f04050d060e0105090d020303070f0e3015040b1f090603060b040e060601 75
    0x1a0340c0b003081500c088144d02c0c0704c00c0c800707009020360740d4a4681e02c0d0305040840b03281000640c40320700c5043c580042000811303004415103050700c0d810714001a60040340c480281c060403075031402600302c0d8500384001030324281c00e50051040ca075058400c56000300d1140c04100c01c68142e4091a4520b4004008080b1307444c1c03280140c07004951080c2410401e601d801c240704a612481d10143e0480034000081c814555014819040000c1400c2e103003880b00100150b071050384075060b2215010030b02c02d001c555a0318080b1490151006808040c0120348190402c2c1031030800780001d18422074031946000003141616802041c8981520210307001141395032240c0700220b628119540201040141041e10081c0c240d4501ea000d408002e1090000380501803141c1844020281c07c6d082110075a101001442c010104001d0443d407060b041259504103a450300601c04403034054900e1801340d414240700105da201c5059100d04185d03401500200201902c50702404103c461410981601e5400303080040d02940c8690043c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 90347770 1250 90346520 90346537
    0xf0b0a030f0c08031b0c0d0203100911030d0e04061a041203090504020307020114010519032004020a0906020c15070204050403142d04060f0c030903150f0f05010803030c 74
    0x58410281d5036450413420343d00450340c480080041c2186101c03412004215450500300115104000248203900081d80d40443c50f0300d04120503112721700e032801d02c50540100070040ca400740580700d004081c0e072801402440a0450503109501c1c0c1400840d4004001b00304c5000d503241c0d82c070114a840c2c10000c0400c0812219402201045803040340802d8544560001d14050800340c1c0001c01e00c0c1807040c0651110280c16013000c1d0280082e00c04461041580c6c002c55000c994011480e40000101e0241d0f94520382c042c070f110320f40c0050001810b808011382c0000110110b403099401c1d00c0f4149130900800658503615072611444000c1441158054540366000303d42292103420010906030551000940c0c6412425020b503021071300400e50841212807440e41460b00d0017a204a9140a007002c1018142540d801036a004005408142c08205805a201c0c88059a0270804900d0301001d80c40302c00c000b4044102c6843c0110381090707069110401c450040c0790584a00202650965450284242150300070164 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 90349020 1250 90347770 90347783
    0x8060408133201140d1a03122106010e0906040b0406150e120601060e03030d0e0105011a0a12110d05040605010503010507050313020108040212060a0606030f0b0a030f 73
    0x900140241c0c1c0b822291102c007990721030140052409103980d40d1064038105415050003c141c1c0c85401c2c50001d081214000000c074100001c080c0c4c0340d800b1000807403150100b1581c040c0316601d4114044129034019003c080130680c2e8800c201025003803800b20401c070a40d00c0714040341c007801d11840f503460312141255001d03801402c0041d0740d403800700004080e00e00d154018221610301c074042002055000e0400120001c040c1c40c280d4124612010f0559608014030988017048000004e4030303200e540900172203003440d041c80700a01c82014401c036007900030a030a00c64034201010036100b28040c0011101901c405452680b141d01400124154441c0500140c0d5006004800300700888042c0110074441c090055000b400c00017065810f050515007101c001030006006c2c413030203004104403080c850702b05440540d8207281088007526076101040c4400307054041d0704018041d00d401c03c00004860fa0182c0200c3c0c5050350140308520114810408841c8103004546c0c11200011003071022440881020700014032485 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 90350270 1250 90349020 90349057
    0xa06080f0a02100c030e0d08120415050a0603030503040f060216110a0f0b1803190501050f0708010510050a020111030106020f0606060a020d140d05040305030a0f06052206030605090d08010e0108060408 88
    0x100d5441c039030b0440cae044414122009011003188124400d55a008040078010040c95066803000b82441c003009100600c0080310b5084001003280c6a0145d0303000244204200460480902d44600341c85c4030000d602d030103003c404078000b8503144032240c030034211000740d006d4902e00028021011549580d90010a8051085031491706000c01c803903094aa0940c0a400005043d09040c0d0700020325100c0642044100050032005110355696546040501402070501c1a07076442138070341c164050300c5240940300b0480303800300c000034840b500480c0031000038001c24156032080e5508000c110140c0501c104c40c1740142c3c07044a0010f1000d02954040350301214a0310700c541005480440c0c0700070358000701c070704800040303000c030500c2002e40e0180640440034840240910040b0b04140220b20100c0c000981c800d81d01c0385140c01480851503ea2025002d16002a014040b618241f8501599914503501e8500010b80d0030000240707110907142003905907913509002d0300c041c0c1ca031a102c10005402468283d403003040b401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 90351520 1250 90350270 90350287
    0xb090712140c0705010e060c190e0603040b0708090a030206061207080105040c05011206030206090409030509040f021e0414090403140406030c090518040305030a06080f0a02100c030e0d08 82
    0x441c059101d0311440d0a0699112010300d0320380d09442901041500360745c003020070720141c40040d000f40e43c05000c07901652030540b150344000300c508100035965281c1008000051005001442e00300904c100d42e140c03290f0311180c0f600110503540d20078900c0c010340183c1080c004507100b840d0071800e50510900c400111a503030b41d10350f0341c3c42d03003102c1c41070310201e902d120340388410002960000401120040c94000810040e4515004240d403445403e001c0c520075a81e658080c002c26015100380e82d280e54018000f040250306411055009501c84806c10520124882c1c5884241c5103130012038094803489180840c0b01041c1800f0321440c490003401c11420b100c141200c000390842c014014000404942d82c1c0400d2812100304050110401074101601880210f91007525091619030f280b504180c1c185403403541c90740c6680b1510010f001503000308000307000b1803402072284600010b9080d800c0e4002c840c517800e020502582507945a14100c0014042035035214000f43c030745421075000141e140140061440e04045 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 90352770 1250 90351520 90351551
    0x130302041109030d09030302120306060c01090b06010e060f0d11090904030e0a0b0705030a11010e0a0c03060f0e070612020d05090a170301062309040216150b090712 72
    0x302484022000803a03006018901001080d410384c00c10b0821040e000d0031900c0094461010f1075200c46020000800704005844400444400300c4105000700501c26552411004c1681c00340e440324006207050782da80e51185051b000700c56401520420541c54034503e401c0501c05421403503072038051540e050101c044140c64074001548a0340c4a90b0700c1c10304c01400d1601300140c4404542110040880c28043c040024200100300c032980141d904040707540710400e118080c00752014450482444c0078840c0d402d403c00c42024410029688510018820750f18981c2030482103440c0c001c2038410b140e010360403c21429000d0143d01304d1100001c14094036240c130001241d41503800c1034903843c681e940814107103002d020319141d20805c413602d06042580b55500d45240207040158506003c162400760078442001500325500311018403030090030540d160844140e10300a410ba0030034082d140a40c91032610110400c0e1380c805d6040e2a0f13002800000c4030344404808503205840200d40c04030707040e5104082d142c0190b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 90354020 1250 90352770 90352781
    0x702010c0206040915081002030c09120f010c0906020f03070b0718051807110c01140c01061a0408070905010f030807020d060e1b01030509030304020108040302100501080d030507050a09050613030204 87
    0x39117942c091007542c5003916851800315407441c1022014414070505c1510141c2d041100c100318012102c10391440310b00e00000d403d00d000780b02260b450358a003400110b000ca401c06640001c0f1041d42e020303a64140340c04c54a264481c403400388000e155403000030010384094012080011072410303119641590303644440100303030004c40c1030190800050040c0c0400251036840810000255283d00203403412400420020b44241d03003880d40c1550703a83d00841c2e00080d040c07007540a80002c0c1103104980e0142034464004801560103405510414094007102254084983c05510f04070751a4040e400c000700d1071520b64045540003520200e0b80241421034800c0401c400d402a00d145007105d2000c2d060b0342c1c85488071110035000e8400444d043c50f09040412045034804016a0303132040d02820700d1040c030350b6246000c90402038946855200c280c903190022505400002e10001c414040e0b40301000700340c45820080d543c50040c0c1c00303100c0c0010703a050003c2c080740c2403603006410180342101c0441e40e4181c40c0d50015042e01c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 90355270 1250 90354020 90354041
    0x516030206010320090402040b03010b09160f08011d130209150a0504140406051806130b25030905030f0d15050f100507030c1a040c0b030c0702010c02060409 69
    0xc1c0480014020f1148112241d1060707840311503c001c40c1207204000c2850088020700183c42295103075858040ca4800b0b4204184600b8001c01c40c0000b86001e8080c02c035241c1c8915030000000300d4041400b06c506014010b07450503641410070100b003000d40604990f00c0364400070300c02c685030900080040b00580303e040e0160300558840c4094031840c1060014130841d51310750303440b2510940c1481c82e01d071f040c40309130322303642d07401c290051404a181d035510b405e10004c100080051101038802c1c0001c000d106000d42d1030500003244981000b04058a5880d42d000e00e04080388205c3d8a1300d0079010790502c0c0540640d001c4d00c0407601c2802503a05046074401d071a511501b208841401564440c851140c044e141c00d0312120190004449034810741c05103002080305072520310b080c0340078803c0005e190340c103250252404820301ca0740402880b8150300886d01240000030103640c00c44041180c4800411200d0400041ea0b2140310340740102818000c050f001103821803a0900c4c1039030022002c010224110525000e03d01e1008c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 90356520 1250 90355270 90355273
    0x6090314030f090607020d0903030e0a08061306051302010806270106020304050f0303070302150415020301060c050624010302180301090602040f091509091104050a0e070b130603050705160302 84
    0x2d181041e00642080001011a8110b4100c1208120820f03004018181927a0300740c90071603414200d44001c5030600c9104c1d000300c202c0b80310303c01c00c00000c1c51900c010010428030441081c013242e1566242c589286002c00303802070201702c82c20005000c6041005c05c0040300c5850740c440c0d8001009202d00000c015070282c00c1080180c200280130300c55400d000c00d48034124407090f002189442c00ca614002e490b00204580500c070100705034003042c140003621150b1100000b49900c111754a50b500d0304050160120007400300ca1a006150008110305104030102062903d0f00036104810a0620300440003944030441c404900600020109c02c00d031800d10504140c1d0788039500040e9200c1c18414450b10b10880e95000c004014104104a0301000080c030849003100c5501c480400e40032010324050705c1c110104060b0030340107883c3c50100700383c00d200c41e0820462120200305036000e2a071100a10300c00c40c0704006281d241c030690034500700200c51180d80115030040142c42c000e41891501c0703294460303070888201d0a4006 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 90357770 1250 90356520 90356551
    0x70605280807180f050405180d03050709081b040b03030409140601030e070f0b091819050a0b030a0b0718060804030f0905030c0f01141b100e0a0609031403 68
    0x1015004084078900e41c0c0e5108007609801c2c44c01c1260022100c2c0c9003c0d560107140c850010070122012018100a0a03080e10305940e5000c400407802001040c00703c851200040f442c200c00108004003103103030b010f03010207103040c50454070301c0c031f020700c40a80401860950903210030480081c0210785881140c60000340204030240a0912400041c1603c04c0105880300c1900042d004200f959a086d284000300c401014409454094040018084002e501102c00040c41c02d07a0811082c0d4981454110301d0380495001005140c55040342c0404450411811a42550090340f05001040c0c8503210381c2e40c4004545813404042101c0012244101d110794004400b003034190081c0300405070045100008501c0903c3c0894006141000003962030b11a0f080c41c0f80911180e071242d000a034420040045070f0b4883c04002980d03a03403488121075404140000c911840c0c000c4103c1d20004884034001d034048800c008008003080030480c0c80388802400028821400e010884001d00340042004014501c216100c05c2d50101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 90359020 1250 90357770 90357781
    0x140d020f0d02010204060917010207060e01090201030e0c0d0201031a06040303020a0501060503010b13200a0207050a1a090603190903050712020d05041403070b1303021801080706052808 81
    0x18120310001e020040da401844248044e503403203451b802c11a5a4004020750092280c400d40d4028810342101400b02420303c200300ea16400150400c4607018802c1e42d040206280d203042080c0c032810003001455110503902080e5015620a802084a211042c40d0200342c402c01c01e0000b03009940260310440141e00101100028031100b80300e0180200000c3c0c001340800103102c4001128800f40400358014140c0c1c0300580c1304619041940c24450034008154030340d80e8040100040e42e10507041c41703160b2103030495003404198401058828403000322820038043c00c000c00b47c0200880e5410060500f107003409440c043c00d440d81464001e4807801802501c0300d55981d41d290030100107034000441c000055602c000700c8040c0041d44401200e00f111026002c0804404040001a00301074050b0700c042040240441c52000913082180084c086078070890b02d400d580c403400d80030720041030340c00d118031846034000035420017079240208004c0482c05d00d083c001014500311280c1007100720541c62002e000040c8050100700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 90360270 1250 90359020 90359023
    0x120f0a090e090a0b0f06010e010c05010b0d080405030d110c010e13020d021905121906030503030928030207060807092c010b1c180503030108060709090204050616140d020f 75
    0x2178101c850001900854a02100040c140a20307010035a41081320141000050107002e500c01e00e03040d0f40c000e0040c07001c203049080200c8182c000d030064a10070301864a0ba02d280c54050003c07000d8003401003010740300c00e115600054803020800460b2030341041c1170b50b0320050544010310040483c86c010300c000603181c8116807030428075450200300030b006201c1c2c10003100088003000901182d0000c251132100d2158071110f0b018501034142c40c2d00041c02403002006011140c07030042600412075603084010198490340f51a00e4054103858003000e0050f0304011400c3c42854410030350f1030b07030140e140e04041c41141e642d16440e5018000054203020f65224140c00d8080c51048081c90303500401525002500340791410382ca84018440c944d00e0720045590718010000d45030f6038031f0791410010b908801600d07160743e502d0340784075102e000c200c41401c00140001408110400c4130b10075101a640041c1c0400d0619600880740c01d841d0403101010b568200040345582c07420300c1c0401c641400c41d101c540c0030306061400a140305 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 90361520 1250 90360270 90360293
    0x10030e0d121a03150603120f0c0c0405060603161407030c0b0606030c0d0b0a03061506020d02060106050708090f0a0603020418090b1b0c03030f01030201080702120f0a090e090a 77
    0x348001e072460400202e0a540000340798a220b150b4240d00c142640340c9000080c580110388155068612002c546100c0400440000c0e00c0e06205241c01d889140004000f000219a022950709511480c1800450320211046180300083e00407800e26984840c00c1305410303451500301035000c4000840c0c0345004410494015140e81d0414000c2d030702542107060141e5500d400703005034030000360059980c0c08503943c10390300d40b400341c0001e5400043c1000f2124111180105441940c042c2c9400351003100e1000e81110b08c00a20749048420581d078481c14000c2c590354600712030740b002c88020352210440c110210309540daa01e401c401060140c40050703441d4a480360654041004401c110031080c6441064804946160102d40d84803002385503480c440c001b008890744a2340102a034140c498403011007003101c0003542041c024141ca000340c030352600350303aa0884100da880d1138038560481000d005001c444040403010000d000c44655134101004041d450f0b14aa0f41701250440303100d100b6900c40c40c0780c1028450f400844 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 90362770 1250 90361520 90361541
    0x50c06010e0117010e1002070525031202070b1c2c010606031a060705031605010609060503030309150c0c2a0111070b09040b030d0306090b010c030e10030e0d12 70
    0x203020090b0303021035543d1651020751b840b5103155000544c503400c0000034080011003000e01e00700118540501c51540002c0100342c0003c50340f0320702000380811403600000d00a02100c8200842c58645110100101c50141e40c89031345083c026110f5044040000090a814000d82c402e50380c84514110b003070038036070300b0340e8003030b9000c48180f5180604c03030419041d20541000c24160143c1d0010394070042454950b180d4480c0c24142c04203038122500102c00c004064000303c5c12103500c92020700c00c40341ca550805440748016643c21903181d01003215a00300b08101d40405502c1050426018100303130403210602e007806201d42030b0b0030030000d01409902120408130740c5402403803400e20b020100c0c0444c40c045643d07034204a01602c2c414100100d000116030b41c4036040240d41c483e024041d02c2070000e0140380171303000c1d0102e0b0103400340c52800c3c86a9030441c1d520540248a4030b03501070f82c0f910908100c0005129080c031003c06030500300340d12001ca1050020040088009000455a0307514400e12540440001c03210369502 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 90364020 1250 90362770 90362773
    0x609050a050720060103021018080a060f020f07140709020d050105030f03040605180f130905010b190504090f05030a0810060212030a021803071203170702060f0403050c06010e0117 79
    0xc0200f222880043d0b11410340b541a02c4202c0c003020b41c020143d034040c00c03000a42c400702e8202c00012072689404100d500d4114880e45050110304500c101d50001c0c1c2c007030100d001a6060f000d104290100e07505861800441c03901c030040d5141c49032114955001d81c0d009980301041c0503140c01c010405070508000403500381170800c000e1803d10741810b00007083d0388038a80500c1c1c019404d40104070076941d10701003030381810303000108003501000340e4507400e5000c2d00d1040c4040ea20380d46400380d05043d9090a81c2c4001036183c402d0100c815880c140030421005088078002903664a18041c0c1100010300100014100c0d0301464842072480c1c50f0945a03400c100d00c0ba5003101c421900704c084018500041e42c002c3c0ca41040851a000d0303100d400000c00300b5003070013000c1d41065242c071480200041210f0f59181509009003e80d4400c0d50504411402c80e1103580240c03404401a407142000030300c4840f034200610f4225100f450494640700882e82d25914210080e0071100b040c07140c4e1001045826480344070039000442d42030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 90365270 1250 90364020 90364067
    0x6030902120303060f0607060e1606080f01060905010f0302120907030506010902090108010504110d0603030815030a0b0a0b180703050106031b23070605090f0106080319120609050a0507 81
    0x42c04507824100800f150b03801020041f51080400c840f54201000d000d1030482155110034104600d00d10001891240d8804a104407002c1008000b940f10028141c48079501c85004051400300111224018440c0310030030958240702082c003510125107801d004660040007040c1407400c6040440c20418181d10a641003403040101c020700c2d0360407941d0181114001c4500190803140c41c00501c840d4894a0f8205c0701e281e2030081d000c02003507005400035004108801d01101c1c860308400906d607960300301e12005440c0c030105400060700d450094104201c8400041e00010f00c030a01181d0700083c1031800e0f5615004607440d0801031143d1035241c8036500394420f543c003412504001c84d07500903090640030301c2680281c1c0380c81e27030880500780e04440803115043d6001c40e007001607240c4100d0146e220018048115415400c20500042c546000420b480303088c0a4801d0b525005052800300b510060800c4001200c401d1b1500780001d4800aa48100d0b44100c0c41c079031011501c0c1c40c100c040140b8400468505001c001c00a4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 90366520 1250 90365270 90365281
    0xa02010f0c0f06090c0e0a050f011d04060e1c0302040806070311090d081b0106031b18020306041104030f0605060a080312040203031b0a0501061a090105070201030605040606030902120303 82
    0xd0a62001c40b9401503800030b8204060709110b06005440e411a0740143c60750403e0024201d00f0703500c1284586902900081c1507600e411090501207010400b1486501843c408500810b032598000d8410108110480d2407000e0483e1a2501014286c81903c020980c041002c10105e1002c1c005c5542c000c1e002e05d010000040201f0404450f8003d02c05034500440415000708108149901266a0740070300e0500703500c2480454061038081c12030790001700d51081800d000e5400d41100b1000e800d040c0c449003881440111801f81201d0000d4000500d500d030f0058444406000c403105080c001e01c09103000300500d0b19500c400b8180300080e203030060100e030700540c100c00c820412010f0110944e60801904104410952602d0000914500507954003403042c543d00c2c12442451000026585121351280c0001d2100a0356500581c58808050100d0b42e048001000458034941c820f10081c214503105040010350345481c0c01c045030031240d85030040380c0480e507501d071120250703e00010400c06055480006506d5450308 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 90367770 1250 90366520 90366533
    0x1915050f0f090414011e05030a030e0909070306060b0d0506010906090909060608010204060f11011811180c0d06050301020c19080706050c09010e0306060102062e03050a02010f0c 78
    0x41c0500d00640180100d1004030702d55542d0440d4500c200c1c8810703401c4165031621414610340044d42642d124854050100082504020501b902415015102c180070022303100140500d0941c010800e02c00c6000d00503011000820511902c6c1c040d00c0000c42c41529580101050350442e1006440c03541031000114080000c40d500051140584814500104503a0381c1d07442c00602405407500600341d82d50000c180841d03150361140340461040520b942d5044405000c1440f1400c8891414448029994250408000c500031110004c400c520280c60408650036595480c005008269014140f6040c0000d0314040c2072654003d403005013000b00c000314030309200300300901c1c0c0d9801d8840ca05c2c80586803079401ca5040c0300c4100c06481c0303141e80008003480103190502c818401640603106450106440408840282c100050410f115420680050019849075440c102e04030b5540d075041c102000030070011070307500000010103c1c001c600c80c00c01445000d0103440003401090b01071096404000c13994a001022440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 90369020 1250 90367770 90367777
    0x120b0a0c03020d1d011103090c09040206090402072012100c02010e030403030c0c15051602060c071d01091401060c0503090d1a16050901030203151915050f 68
    0x2102000100d940290030150040c3c0242c02c1c8118030f55103414440d00c041c4108801c503498441001c0c000704402520440c03400101d01058502125540c4100b02c640407d0800e000c40700d030840c3c00245081e04000d48800081c2c2a80d101003c11581d01e4090200480341c10000e16241d4202502240da04401340514402e203644d4800b061049400d00303440ea501413400758001c1d4007541040ca040400d5a55032910703410098102a401142150154840c0740300003403501806040c0c8000718055600c1601d001003005601041080c01e0b6400d0342d0261081190040c1c0a0003000b9001c024081652060260780d409002e06803d440140e05c802c10722030906032803400e041540c1c0c100070f05440c00d600b018016004107003403407842c50007401c1426030008820481301d4140010b008030240844100109501203596101030001441c0e00d10900001080d000d00c010040d645c0682c02640c2d10010181a8440c0c0c40394010005a06010900700c0d07802c00b0240b85400d2048000c040c0d01e901c0b52240600300746182124541c0800c81c0e511 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 90370270 1250 90369020 90369031
    0xc04060e06011205040c0e0103031110021e03060406050604080705040e010605030705060a03020403061415010306050a0911090d060c0207060207030507090903110604050102130e01050901090209010212130e01120b 93
    0x182da13907000404000200d4030010103014034148900340340d80c6174034001d42610351600c0e40c51018414442e4103850034015008030b410307001d00c049000202a000c01020380e07042e0809010030740e0283d02d03100d0114007900c4247c085c200074825000240045c0f864041488121031243d40c08400d6a41400c20034011518006041c904840c800c6d2049941e074040b001d811030080c011030704020540350500f2646548800c00d081c1302e90140c071040442c0c14503044036100642c00c0761020310a080c1c01007000c0e4803c10103ca407550298003040d09602c3c0180c90808002e00081d8072411500c1c04960495680c00711008965040081102411060004254290447d11002e544110301c0c4509612585c40d08908010980b1400340b07442c203908003100b2103005040501d0840c0c080d4014180310f0100c243d13045800902c2c042c40c21415412107001900301e0846909008040c80658031088003941940300f04480f110040740315000034100903d02c446041d0980e81061418404000c045c1c1c0190700d001209c491440c04200c0342d140554000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 90371520 1250 90370270 90370307
    0x203070212060a1d280b0702011b0512060103240305070e09071404050a0b040c0e040c0f0c060c0c051002040914090d1101151d010b07240605120c04060e0601 69
    0x3810b04041c0800c001145d6100900c010440400d220915805400c080701c0e6a4100d4407811414080e900103e526001c2e00440071090700e400390204541c0d5010340e00c410508049818880524040b04e0528040c0c1c3c031199000f2100c46c0c0c4022400c00c8010b2040701c04a0300030987c2c801809100749000012000c07110400e004510860391000401d84021550740440c10002d006041403006030440d01000d0800d4040010040c040c50810003102a2148a003125000300720b02030721184503480c00d98450400800c4d50340440000d001010780c0079070103d030007007060440c002c00054001d41c1d070350305051f442c2c0103990845c6a15000f8074401700911220b10340219286095010340d02d0303c19540441d640380140540078294401c0503402c804440460481184013001c8900c0e40141c0d01081540d1340c80451503080c4c85094800341000d243c2d65502e11101c1a01540b800001c00e4460002c01c460741c071040000c2c3c101c10910f500040c10b17804421045001e00341801604000c01c2d940e51a0605441c0010001c0c1461040c03212071b1001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 90372770 1250 90371520 90371563
    0x21507033810030c02060c0306010c0b0903040b130f060903030c0308090c090c0a090f0503070302060c01020913020a02061302150d1e0204030b01120c060e010203070212060a1d 77
    0x1405248050a860700001041c10740781e1102007801400808603020310300c0043c002c8000180c0443c0c0e540080341d004600c103030340d60748405030303541c4801d1154080544403442d18002004005200002c080190410020014900c1803561800741d81c500b41d00b000c1c2c1e200109104001c5030800100c1d411a11030940035401d4200070001c1e03a10744007105c2c1800410351500d640260b44005208050800c1030203008007000341d40320340045d981c035800d41d041301410a00c200d0381e040c0d0001006000608007400944a414182400942400b50342070000e24608142c400030742c0c07026800308080304810340c100700322501300c0c1041140301041403003900464103102800c1c2015603140c0001031050540405517011008400c01241d4008402000d070920f10040c0d03001e44410758200c10858004a4460301800d030049045030300c0303e542150185484002d54543c0c0180c0c12490540c04180101d90150b00c9a00c00003221487d008003411a40c540050010112001081c1e419128500101c08a0201c82d0020344802450b80f4072071780700f00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 90374020 1250 90372770 90372851
    0x905010617060f03010507030b040605240c0f15071e1d06040e010e010e10060503130309180f06090e0a14071a0307021905060a0507090801090302150703 67
    0x43c4007186881e02d070b01076117004200046154568002c018048003100c003406110b0b03868082051141e035031004070455144801840710308410920090061011040039100c4820a4800c045d003080c41e103000c04100100840d040042903603020042510902071180c81e03803240c0c1145c004c02400300800b0039450f0508001d02c2c6410200d43d4903403080d64010001e031018850b080d070715650f20200942c2d0a00c100021600c071f8034003190703420300152045800d456150380d649055554501042e55003c005100580600071600b502050b02c07810390380344d1760300118000d4002c01d1003100c00b850b9800312029540000f00c810701d021889202c40c90702042c040680741d081403800c8503e41607010381c2810546903500454070000c441e0f2410074040b202801641c440d000b56000d65010606a9280b640000d500c80c800400d2604050700203000d02c1c100c0c1d482250044641d00e8940300d50741d22044420f0031120300d05000d40c050780c88000c1d094035400c1c66003c802e83c000254601440345001d2390b01c0300100103001c03007441d04012200c99410358 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 90375270 1250 90374020 90374029
    0x80609070504090606050417030403051504060f020f090f011b0204110c07030c18050403140d0b030336031f0b03070f090c090302150715020307030e07090501061706 72
    0x5001e00f81c0088100880781d5650b40182c4a0360203403190b003540181310301c01c2c1156000c010003500c04694002c0003400c0752445c0c141b000300311010024011030341207689030403880c1c201c401032000c3c0004083d0341c040569a8420f0f07404022a540981c170110b410043c00401c10445c11000d07071090381105034180c0d4003058121000d0141d1034a070207040380d42d9117640300307403000042408802001e9904070f41c5050210b0f605410050007103000c2d514121000340c081243d44e04800a200d940030000d041c1031060b0007001034400d0241c3c0002c4d09583c082c0c400c0014030f00d61614036202e440c4108458161281d041c0d40d90750040f1078180b010035241c010241080e500303001d9002c0c18440010700c9802c6100c0110008003a200540e48551031822107810701d0048480c00d900e45034101050b20300038202030b0156500140100c0d00845c845640e6042c03640b103d04219060700003c0ca6400301880c040c0061400b6101c141c0700400e10302c005c1400146080056400300c00e00608140c01000141c0c0c000c40d560b600320701d50826644191340c585001c00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 90376520 1250 90375270 90375277
    0x60f1703071205041503020c070b09010c2307080c090c0705070e0c030f0105010201050603121305090f041a0f060d030c140c0405060a050901050906040902221b0806090705 75
    0x140541e900b001c078080b0010b03800b80080003030342c0040e0300d03800c51040d800300100c0490090811076600785d80004014010101c121014186007441454030b80400c004036a50030b540400303085200081391000200b134800701c410074072090303000e0080a001045295044400101000005044007100140010380d000c01d2103000c3c00501c1c003909825060080904161009850950040b28152466001000040340940c0706018a40c0141001001048040405c00102513203510810306441201c03034107180081c0076250329411a02c10a140c0380f40c00c502d481c15042c286842c0307084a991014545980d03040020160440d8001904150b007922000e844e0030841c03030240e400404460300a41080c80ca45812043c41e0302c001030040800c141a00d0038000754554800380413298078103000d030765800401d0b04018429424510311007a40480700410220340117805401146004e100940c030540c0301c41240d0101c85500c0001e0191507504000307520f40e10890b00d00d03c0b0b0018580c0d00051700ca05d110b00080c0b40441c0186d48104141d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 90377770 1250 90376520 90376523
    0x10c1d1314040b0a0b04060b07021011072306131a091c02010f0203090d060209130e0d03060f030b0c09040e010c090f08280f0f030f030b04060f170307 66
    0x184020b003410300b03102915200440b210004c0504012040c42e1a007414050001100e002e0601d5604106082e030820003a484e071101c41c0c004001540b0175421041008002400041009480301c03040110841720034440d04a489900900466081150181000050021200311354903030b09050015096000030f80707581d10030001c4042e072100280c801c1d0382400c9494014450000d100340c1f2000000302c00d0b16416030701e901840030030716400810181d0100c00700f4180d8000b0300718210b00070030001d00503070f581d03008104a803545250007116910022a48a40582510400c17002e080c000d8002841c1c03500e1039507061400080101000344118001c81d501e891502c0c0c0e074021500700030807580207100c0004007090050002c2c00c14442c200c1a00c4040000103071224000c074101c51045003402c071103000d07011844400100030154410071074400d00300d001c2c1c11000c181020091a1654841d503180b00903062400c0008059411000c10984150314044042205d1104110400121000325081040c0020662521030644c0680c00c1c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 90379020 1250 90377770 90377801
    0x3010903050d0c090b0a0c020f0a030302150a090210050706090b04060203060301111218030d0f02040501090501020c01020d030f1d0319050a020d0c06060305100b03010c1d13 76
    0x904158000001c1c081000c140741c0c0411845100000031203103640c491040a071090341c01c00103410041e101c1c40d0004c101c10f0000e403d0518817003161000c601c5420a80d80140c0060b007081c210300e4850326243c80d6640d00200644c0062040e1003007900000d50b4070001e8184c0d03100b401000504801081050f030006400103810080c0624203142a0401c0703406980110754240c401d5191030101d112504c101020348a616550140403502641d4030700301003480e0f10410700e020700184801e00809188203094000c540784c00300160409030f1100e1801c8009014044c180d08000d0664002e500034070700c0c41e41c0c00500300341c0e0340c8050302d000f203441420310400300000d000100099962403101c80100d900300710000020002c0d24010700c0029100c030169102280c04e4050b00c5051170058101f0507010300b0481c411901d40301c100780140400a81c5550700d0f600d01d8030306140004c0720f401031038850082c2d6605190038418017001002c54186170441d0740c40d00c00c8c040040095400d00c0b5224a0001d28010121280c0c1c0c4d000030b01c140d140b2031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 90380270 1250 90379020 90379031
    0x30507120c090216031103040b2a100204061403240616060b1309020904030e010e0d110907140a08190501120b0c070309050609010c06180b0f0c0304200301 68
    0xc2c50010424003c10185c01003280c10100582d00ea000104540c200c0c5e2940550904051340000b0555000055858a4004400f5210348415a01042c00041100c0c0542c1c100181d036540341c107a0141c008031848080109540051082185046501144820b00500301c81191020320100700000c9490280c114000141202030146504200860740712003060704040314113100d005c034040100d20a1303e10101000390000048000310f00003074061000d1014071078050402c040645001004505582c044440c00d50310140b041200c1413050070710050850704540145000c00400c50844211840791040c1c2484c03104000802c00090300402c6102518100807004000601507540e46005098004c084014140d070b8090300c400c0403805400000c02110011903242d207420340607a24010400c0401c0d04086185414442e0100e000703000100f0900c950f0b0013602a40e000038080300c1113820004107a110040c68284020b56180c1031040d140340450a0320340c413640c80101c0746c030003001000b031807900052001b078150740540c01c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 90381520 1250 90380270 90380287
    0x20a0b0106030e1c0e0618040906020315181302012001051f06090e04060f0507052a12030403050c0f0c0f04050f010911040f0e0f060307030507120c0902 67
    0x64014803088407006041301c81042812042e013614605002c000c0000c18120034113100c003070030118013074800035610710500b08080d0f84903c04102a1400c40e0b4040791032960000402c1004c1540707001080c0f0000d026294a10501e5100300e600510310b5020702081505400d0108110440e84201e500c04058442107000c451440d0600080c240a0401910200c00340144e500600c0400400d240c1e202c7c048400039524902c41034a072007070750340802e10003400a40d4625281d40c104d460000e01409001e008805a030780d140d9407520300c40c000219071154150031004006030403000700208440000c441e008070111100c0076540c0c0d00c403440c0560300d17841084401e10041c0109007564001038004231300e0308401041035034002014031b01041000111031003259a0a031000320034006002070b1219901c0004401c00b00f40c002d501e4541c4400182040c00d00c075901c080021300a94081180e0031403c1981150845000e4000f00025803e596072591140e049014201641c41400442000c0c80f0700e60401c6401061000341c21950740c00e06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 90382770 1250 90381520 90381527
    0x60c010f020301050f0612010306020313020d0f020f0d0c0506030601020a05060709060206060409051e030d020c06041506080307080a17090c09090601050a090222061205060d020d080a020a0b0106 85
    0x240310390351060504c4545445c0c83d003003403400c84814181080400049a0855452a0094101400191191001405075401a202c025004406a00074000c0c0c100c6c1e98014410010800e450107051030050424104140026001010304070949400702d031655102d0759501d004074a0002c140c00003410303900c05c240608c001e00340c00c4008482603801d607a0903944650b032410705000030360303041000042840d4004400514041e01d404e2100602821100030f0746d26000d45d0301801c0c026604013440b0700310540c106105000c1044000950208207044034101400560302d41800c030380c0c5078010b80c0c0380546540300009442c8100307480759580c100c100d420324007440f00038104502e0b80c656800500c5400c600821007040860707807902000990314100c5000070302c1c52120605140301070003c0d4212072184c40c20984104007051840c80c9110303005020b0f00841c0e8881d034901c2e401d55000401d550000e003400d80606241586403026031038201c07003050650b8200303d19603a2910285012840c08405100c05080c01040030004200a40e1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 90384020 1250 90382770 90382777
    0x203010b09010b0a020114100608040f0206030703061e14061c050a0b1314011206020c07080d121109060906070606150908010e0c04151211180420060c010f02 69
    0x301c580c020000510b80c9464009449020b640236041c1200301841080468800c00d442ca41c05072041d901c58881c4d0340694081041074209483c09800f0a445141c203001d030101303006010703043c0c0c11a500c516203002d19100d01d4228a5501d250098043c0c8030020340c00b8020100213500503001900c502c001c20492804c0903e800051010303000c0b491240c51142c40b071300f041c0d90300f030300920724296091541504264600742858001c9484508202c1d41c46809000450b200740303090080c0c000a00c060405000300c00440440244a00101c01c641c1b0310091800040c44003102181d0255500381e070003a10301d2559a4039100001b05c503801500340007010142042c101060040d0110070040110103191502a80180c40d060b0142c2a20003c0c084852664041214030400f031806401801c0950201e00c200c11407582c560680c200380c121440340596a025030090a0382550800600c244081000d42180c010141056559030341c810000d49018071070350110055440d001d0b51240110b9442d038038000020440312111441c554040e40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 90385270 1250 90384020 90384037
    0x501031101030203150108070c020306180601060503040c060c0609050a030c0308130f061a0a0311010f05180d17071b0b03040b0f1b070503070b01050a05030a0f0203010b09010b 77
    0xda19000d0000d540207000380c0e0b019655200c144180d40700d6800c0111707000700004069404201103500102c000d42c4050100d84e0140ca080100c069840c510424424900041a4080401c1100800c2080042405d18420074240c450b980341210080b04507003008406040c040d0000340050180c08581c20030150406c440d140c20034070a4076010255507a0954a035500c5102107000390106410b4102a000201c0d00d0b40444650030859000140c4203440001050082140e50800c949600461190382510741c0c010b42a000038076010301c0c01600d40350140b07401c2c16041002c000840e009080c45200402002840c01da00c01400e044414999140d20540c00e10200d59940c0003100c0480e0300b0000390105204100008aa200f02e402c40e2004103246ca400d1020360103040e001b041001c0b0710400f03107140c0c000c040d4103400424540c0e02600c02540c80d2100d0b03040403000900181c4c0041e20464840700100700075140452038180803504819100160089400030901514100c11250740c0408486c1c000304800704080060304149 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 90386520 1250 90385270 90385283
    0x30305100509090c01090b13030303020706090803010b030a0b03010902011e02070b0d0b0f030109030504171903050711010f02120d020d05130312020901080612010e010504030504140307030807060b0a08030706050103 94
    0x480d1f8805202e02d00d40b046ca002c41d07001c024083c1007400401c2c0290010b02c1d400c0d00c40c41c0d0014003601281c580b45101c1e0000c0e080549807071300c000103004e039500030340c051145c030701d00101c0081100014550000e40400000082c1c200d461140c501150f042500a0181c000100480c6102c5c2c0e80c1c9480c03c1d000340c0c0080c00101c40c454450300c0136446018050405101300991503a15445003480c280c2000700c030f0300d00c4018542941c0c4c5140302e0024514818821490700c4091a0721944406480e180240f922052a03c04081d00d18108812656031601c0d0a0303000a2001c3c0754000d0010059560b00c11400300c1010f446611480d000f001e04040600500080900c019038505000f0780da0710b000a40303d4003407001644100e500b054001540280412164a000e40d0440650b040d440c00004101c1e000410160940b0b0040390b09401051001c1010041c1c0c0c0000200c021003140210301503c00d5508580c1c6010582c02801405040c080c0c0c0c402c0014927648503485a40d010380645800c40742c0704c1c0ca0a03e0310b403024010034041140c1c203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 90387770 1250 90386520 90386537
    0x20c01060e1f0305030405040209061309141503070e0709081b010305071407110a0e040c050a0801020f1204110303072f010e22021303020a0509090a030305100509090c01 74
    0x20284020000000c0e00e031320a000c2e41c0ba107450103042202a400018074a0741c040010401c40e240303c06d2640e240c00c01004078070004510601c80211640750a000204243e0350710801c1451154954cc000c16010700b0350760280c0310204552155401101c100c3d00542151086214140c14104450104c0a62080480c1e0999060041c0d903680340c0e040b1200d10340242d0300c808405040c400d11001514641e0500d11000300601b0802005689012a81e6885416141510b50304d280080034402c9040c02c06401014100c05030081d481c0401c000e040321524414125040d104040100104003000001c101075003400700003c0850b03444031940d003000000c408880001e000d800326441e42e204100301d0840c42041c5c02000586903154940003113018009201d6041e081040c00180024800c000c041d00c602c09011041010003003901070906500c144801c40b40950440c5202e914000200041c0102c001007046206625140200d0f25850b486660412428103030401a408200d00381007060b445800641441e00c01400d81c0e40d103d6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 90389020 1250 90387770 90387811
    0x1e0525020601030b060102010221090115050a0e040609050f100f062103021005180106080c0a0b0a1b06090302011401030c0b1804020711010f051206010309020103020c01060e 76
    0x100600004100015800400040012410030130f111075004406000151a04850600c04c4060030a1001e51014000c640ca090023403400c0d09108081b080c1520300d114501c2c04e410000006d8210720355114003059406048002740401010380c000ca080c955004003250031006001c081152203015081e40708495500c3c0c2003402144e001c0600402d802c40b410290310720301076921200050180104c10078141c095100b81521840c00d06024803c20388207480d48021031480c3c00d414003c1500752409940040741c654054140e0703000aa44d802980c4003140c810050072541c03240c0280003034501d51034441c0e6408845003114541820b10040d41c01500d401446640208404403100035a4883c0c510b0070f02020301302d100540c03000e100000d05440140031000c440c0e008906110030a00000e805d90f071204038121446c1e901105512040d58101c18520380c070325442c7c14041c0c1400c0c581600d101c1f40d020f009292a04040d04c0d00040015039011b50b0494002c95070020003441501d4440e0662001d4503002d903850542e201c002a560403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 90390270 1250 90389020 90389071
    0x706030b1c0f060228050316020304081b1305040c050a270203070c0804080a0b060a060210022505010606020d020a0f0209041b0801050105210309090a1e05 68
    0x40099a002410155011081c0c56010007500190400440d22994518586031035916500180c0c0c17801880e0307219540d9160160b504190385030303542031401c25544144810701c03882a01082c001c1458041d0000c43d190403115800180881e0095455021000d01d001e05100911901c1d00000781030343c3c000d81c1e101b1100c0b139403100c0c103203483d104a08800b840389010305c0041d03500d9038540c0c0056801c0b280e00d2610a20850482d12110322944c01a40401d01940c0700d00703610400c00c00d00d04a4154002c0c02160b040c3d0720340c0e20700140a5201c190101301c54178456400142480401d848041a544403c0c28000c0c03c1c03440001881c1041c003d001c2390040c040035218000041d4501880000ca448503d503119000400c1e00391141e0034004100c00c00b520488043d1130006403610311070b0103030708890300505600c400429994940b0060010300b04a2070341c900c0c002e024459828121400c00801c4030b1600606542d8600384d80d40702e1344190001d00c00f8480c1031110f01c2d8000403040c0e842c00c50382c010718082e60341d6888198418080c0300500e03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 90391520 1250 90390270 90390319
    0xf080313050d0305031504060807090902090a05040b07030207050709050a020a020f1209091b0f130518010e06010e0402040f030303050c09030d120209030316110405091b120706030b 79
    0x600240040001451b000f28182c020160342c0000b80010407916150364086007887c80982104c10304a03030b140700100540c0340010040d03401c5242c888041109003015103480d02d001030b0040985040c145c001920b07800b04141044400c0007000159000c01c6541803417413040c0065485103585400510030303c0072032f045050022030322500d40584030714075030318069480044c8040302400900c0d200101c007110304160719a5180e440144184410070007815581c10b0400c0c10581e00d640a0b0b040700d80030b10401d5090f04911080140420b0544181d658409655a28034004886c1c035041c940318241c1003070000c01c0004a100b50a83c024041e070317200362001d00143d903c1900340b100a000341c907038281c2e040e404045240021405501c02a034074004454016150090681c0030902c0c0d80e000501c4a40d9a200c111609000c4c0600c401c0341c034041100482d824441410014075040e500c2d59012403d201e9010b880030f900049980d0005124184000c01d001e5941c103564921002d4000c01c80038010314001c0070320f07034920b1036440d0140981 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 90392770 1250 90391520 90391523
    0xc23031c0504051504030f031e0f020c0d02030f10020310140616051015090e01050f061e040905010e01061707030f0804030501021602150901090513060f080313050d 72
    0x41d0390602e0700d40340c00c020103402c0d003c5040b05014400c01c000700c0400c00b0203006ca00c826001e92211682c20030694201e000c04025044032408200802c1100248198041045102046c0844039440300b1106070001170b0400d414603a0030401e43c400e120200c400308016030095071282005c800c4414605d656200c1681154950001341944045c04000400301c5080114190240e01d00900031200c2a000b4111020101d814501d0038400d02940340f0020170071140c807030140480c442c0301c03000207000d20309100040030000030001e441d05101da08040921002c0211001042c21903000081003030003403440c2030424900034446803c0c417000719400c00c2804104510401520030403070308148020b0480130f1540d00d071509140d11000080700c10810401c400000702d00c00f40098509050058880d41903410b580c410801d425080380703200d66406034213000440c81603801060080440340d0545032602201d002011303040041070300c5d8000c4520824205804240541c00101514143d003101100314040c640326020024100c190410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 90394020 1250 90392770 90392777
    0x112030c0f030e0303030a020706050a0c050d0507020c0d0c0302040506090105150f070206041508010e0105130e03070614010f060203031501051b0105070201020d110f160c23031c 78
    0xc00000141c022100029014020f103010344504000742c00081c21503201b031390032100003038020501000f0300c020340c4520380d000040b0300c2c000c00080311000c10250050081e4249003d40c10754078000680c101d8002d210000050708001e0941e03403d00e00900d400307a111102804164004c81c40d11000804c0340c1807000207107050b00c0c2c0040c100b4081040d02d460404150784183c9aa1050760400c0c8804801a15888050000782480d6a41c03086d001c40b20903401040d05005911541d0001c0c1d42e01c0040005d81c03511001c942810103910000f1400d81c000914a0b031461262000041c4417038030300b0807981180b100303510010b41a102d28410000312543e96910480e56030200f604d0b0112460194508440d40d5801500146200c1c09242d204a102c064030b0b030325003806c4440407115080940d40004850441c00b1091280701407610b012640142010b14842043c42903001c2c0c95400b4801da01c541c0c0071001804940e5101c88010509481c00d030b14400c1015064401c49104182c48a021b80b1035075003011100c101c805002c04c1044182e55 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 90395270 1250 90394020 90394037
    0x3010e0609070e090106210605012003040e0a020910081510020a0212010617030708041208121501082a090d140706020f19150221040b011203 62
    0x400c9042607020b80780c50b0034003c3c40880c1c50750b41e40343c00300014000c0a99032a00e1600154444954a1028000d0b5110b00014a011400d201580c0c00c000c2024064070800c3c5640c04110408000c41e00d5441142c02003100c20542c0800c01c580c50f0500e800802a000e410b036001505014100400c1c0c0c0c000d03c0540303a2008640901d0340340c00701824000380e40ca04c400903520450302c2e199403503004120700d0790b007401d1007804a035100c400034030400d20010983c0300f0000718400254a000c0c0c058403103d050380a00c1c00f950340c1100c100308000091200503004c0d13030f40c07131210b00e40d840105080c2490055130701d02d0310426040c040382c000d2000030106100d0030058110710040800300140c1e42c0c6491920442c903442244060703404402004040086114800301c00802240c042c020300f0180e05045001e0b1a0030084405007400303034081e14800c000c1e06100d1070303a072044030342c4501100e4076000120349620183c0100c0408490580650b07108400c0741c808458260302450094005001c0c503625060000c041c6441e184d0082c000c41d120f803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 90396520 1250 90395270 90395281
    0x70c0306050a0207020d0f0308010803040f170703080c0105100e0f060f01021e06090c06030702030a030903031409010b0112021e0c010b151b0102040509150d0506070c05100203010e 79
    0x7a001568010090790300145042030590000340c400000c450203941050340800b020003059005010a8050015240110704040ca05188120b405c0601d010310b600c03d03803400ca2000800042046801c004c1c540c056800341d100e141706101140204022954040d070082c0c44440040c030101440f24050159022261144c9103503500c0c81808a0803600800b0107045205141c1810034001c0d50801c0e090340301c0c4884014058034100381003503e03d803207500c50b0f070607200b41410400d01202c0740c1c0000c21100c0001c9103003404a0014042d080640c010324415842040040d0020100440b00310b041d403050b002600b0903241c1c0c810800c021004c0404a000b007047c4007070030009080348420b043c104030001c3c01d580e0505500200d03c0e08180e101040ca8071074000e0501d0b091140210380703c42d0a032043c0b45102c09040c05403000b107003054503000c0065200c80e00a40090b44886d6080c000c0b00441d2150301049807103603086011101c0d6803c0051004040b40d06074042a510f5000c0c403854200d600320f071750003200e040341c52001e40070700c5a8946 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 90397770 1250 90396520 90396533
    0x6090d030509010225060e0f030d1b080a050301081c05090609040f06080601260a02010c030c060c050901090905060607140a06090f02010314090a08130f0f060212070c03 74
    0x107070141410b40c030078156007226918160300d0900e85c101d032280480001074900030015098180c88044070f8468107500007800302c0381d1000034800381c0b001000c0c9000c2e403111804012401203001c0030743c2d000d4424100000c0001e41c0540020055048660410417684182045411200b5140c0d00740c03000000208100002001c615000000c3c01c0341040060ac0058010710700b425002c01c4852544c031822183d00403400420103e401d074405450703035a94500c80072410741c1c0c061034125240d1491150080c1800b032050344003803c0c980f040d031005410b5070340000204881070786c020002d00107030003110005001403415a004140c021413405480d020303d60260466007004440d540700c041c1c02100111180844c0303d820000300108a0310b0003456131840c05000301003100d10641c00010150380300f001d10a440a1401010b220080c18000b91007100350341c1014886840e2104613281522003201c0364019841c02108400209018840e07a6211007140d5040d001c48440d8074a1518903441d9004602c0094a5000080e00070408901c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 90399020 1250 90397770 90397777
    0x8090f06031b130b0d0903020c180105130902030a0506011502030c032d0f090a0b0304110d0c080d02100c08060105160303060510030207120318020d0c0e0903120606090d0305 76
    0x71040c3e103034800c140c3c484505000c140c121020905d00a503d40c040300c028141c05111400c6030410a0740c4618400040440e40f6002500c10700c249409007102c0c405d00003500c07209500007044540d000303050b038a001e803d41c10225554402802500c0c01311040400381e4900500000071100e0f001094006035040808003602c003002c0c00c1c07015440d0114017402c0b200d030940f200741c8100205000c20801d050140c0b210014400c1c021200101e400814480c0c40c10070520002c00d5030204040741c00f10b411a080d0304080000e00d0305508110443e03010207010720070608030003000d40c1c01180c00007082200a03001c01440d1b1003c10308550884091781c0e0030340461001c105144800f5000d90451841d940282001324640f913982010174240c28154903040006a40400c040041202c0b0309905140f0a00030b1900780000980003140c5062554150f034028481e01c801049007040103120160303080140403521304000703140b078101095a12548549070459078120220000f6005142120940b0380c21200686081d001e40300594056646a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 90400270 1250 90399020 90399037
    0x60c0d1409031606030e1f0902180108010902030105090c0d080d060f06030c1209020907030b0f0402030a020306190609090507020f06010920040b071e0b0408090f06031b 74
    0x80d010460444075071802c100b81c080c2c4909143e00e0064443c070b849002401c54403101d12155598000c602c404c07400c00c3d0b4010030141c0b4450000c000240408003440000c1e145002485081e0080510301c000044103c8194003200329035000b0390092080e40e41d00544280c07242c030030451684d400030609500c0c00100e2904005091600000304c000100242c940104020041c41c59000c0700009480341c80d004101540040401030035031203c0b80c28002d1191a50014003902c03c01080c800c101541c480b925145951b90030340c4c42c441d00e0b50207002190b403401d1404051010358800c03191103014041c001000030f80e0b01c602c2e20052044400759075a40a136541409854030143c800a0034410442c8590114000c0f000002c0c41031707034000c1015240010345158080e5410048440c10501d210351408244010080d00044900702c40300180d01c20300041492801303504004005588140150800540004210410a80b0002001c100b0802c41d2040c0e03c2d040d482d001c0002c10721007203031074102056558000305a801c0900f0003070511607 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 90401520 1250 90400270 90400307
    0x50708040902030403020a0501060f0311030d0f050a09030c032003120a0302090f040c08060901060905010c02040e0118030e030118050c0f011b030210050603010504120804020604030c09020901030b060c0d 89
    0xb600c07d91661070a480640c6c00c81c9503d403840c0003040040009958070008806400c1d009010341d81d0000b20701400a03000c802d40c850501000180d85944a4400c08000307000e90b0703000b4003284040d0385905015504041c13140d10500f4040b400c2041d00c3d2503190000b0300da420b034950b20315210f00d0b0000b6094214042d40020300c2440c1c100c8014080c00302c045d03030f0714000c00c00119003590322200c803854100c080081811040e40b0400910607414010700290364450b2407a507031030b5010f880c040307011500d825249005190b140c8181c050b62902503040020968000c1b0301103030042080b4001d01640b1180400c40446075065507000f445c82d4803400b858001802e03d00c0054918843c14104814070144424850500780d1055100300d0050700700c01c22a1711703039200c00d202d0550040001d40c003c00c86860559520800345545030900000d10081000240071175460000f20f130302444c0d0006501c0d01080e075034a940d5002c3d40060701d40c0c0340440c2c100700c1d19102e41d05111b0309580c18100182c0c001e0184640b0a941a5600285c81c110040503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 90402770 1250 90401520 90401533
    0x11010e06030702010504060b010905011413080313081002040e0708150a14010305010f0605070206030912070807110301050f010b0f07050607050301080714010903030e040b03011e0c05070804090203040302 89
    0x25951810055841180c460300003240600c2c252410404492a410900e414081e07201800c2c4402c1e68480030646181c1c40c550042603950142556002d040b0740d281c0e020b20054400080c1010785030030700c0c000d41000c0380d1a4200726a540d00a10103c50305178069400351842540b820720004062500c1059855004041407900540701c0501d400410800d036855003190117660081c8069641ca941d140c0304190062412100e0680240c3c03d1900052203403140082c003922441001c400705400c0081030105050340700102c815103658080d40d181c104c0c40350b0010b10090b600048080718130000c40c101800751074811035070005029a1a0300784400496035420001c18500c0440c400e006030400180100402d070302609407074540035121b6240c80c100a01e13000f140d420142044083c41c02034030349039811070746040a030381c1d060500c0c400105014003c40e00030b00100b001141c4c19801c00c0c440c0e460380322402200d1400300500c010700f03001490b204082910705200705540140701401c04c20003084160059030185401604c01d1050300c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 90404020 1250 90402770 90402797
    0x60d080c010c0206060a0e160f090f12060509010b03060612010b09010b0409060b1e09010314070c12021207060b0604030209010801020301050916050d0b0a0801021309050703090803041101 82
    0x1c482c0b14014501c0036034844002e000092a0010540c0020301c4c403c8040da1451810b84004810250303450714890600801b43c184c01c00140c041c07030301034001d410307608516050b41d507881c03185803044950400d09a505034980070108001ea04180a901d4455401070021f0019490f00e2090000c0b417101019060103c3d541c51a89040d01d81e500c007000360003401003000d555110707802d208244003114620b600c0354100b040f0400c2000159150000d0071104d0015801a1588460840b4016409412825000b9800440242c10008001e8020070000302e41c03801009010480200f07507100760307038070301209100144401d03052248200040322600001c012580107000c4034149603803030780461105039081c1c0281d44c20365008801480581000c0c4220b56110f040a110b0612030400800c000c0d1031031041414150302d10f6103900c40c800b42529250701c0b150060041400071540c81040c0c0000e460401d40d103001e030310100c0b07040c080483c4585109003d541d2800c0d81100900345140c8480c0e4421400103110003d541c18032040740b0104e00b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 90405270 1250 90404020 90404023
    0x2010c05240105100201020313030507060605042a03050702030d0509010e0a030903030f080705120a0b060f040501080906040201140d0b1003060501031404050d0e010c0602180102070902030708060d080c 88
    0x1c210094580e001840703504141c1089044007801c2d04007001c5a1060007000801030380c104000c04899007604096030355940504100d405000c0c10341007103421a08111202d1020f4006800b41c82c08029114118510349052090850580da810b95209005900a010b4040c1100d5113a10241c5c010b0b249800014130a40c10b00591810011500742c03e0700801c0d0300080400c01d240c1c0100c00700030107010a1070b006020303181c8160060000c2c082c1c200e10b0b0400c0800240091043c0c4600d6010f107040d0400140034903203e1903146140075a0364014000e00740000c0d5460089070035101d002a0940c01503605854080300c00d0b20001400a1581002084068503a107034041240f90f40c84200c0740c20302070429903a0100302c441c14640054140c48045603555860341d26141000041140429424903000b064500900c0c84801c0310012504a00c4901c0082d00f66880010f0300d0700c0859480c007000045400030780a40341e1484d5640a200120f0000300c4105e408280c062000500b540b80c820b081c0c403003940c8140c00c182d041502148569 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 90406520 1250 90405270 90405313
    0xf24090a0311100306150521011403070602070503060c03062b03140c2503080c071409040f0b1012060c0e040903020a02040b040e160e06010e01020a02010c05 69
    0x2540c546024041c0003245040c0000e10039101d0f5010700f02885070603c5c211118000903d02034554003004004100205e0039410310065848400044080c41101c0d61107036003404481208420140c031034030904070002030750350020581d5812141c000f8060720669443c0c54504595034002044d01b50721040d40820752105c840000001c05403203590341e86ca4020160b4518010704041c1d0314003803901c00b1403824808400400000104040c2141074074040703625046400d01c2c5030707004100303a40008040c18404228003c810314000b415100321400e00d102c0e15898071071482806000b00c0180c40c054082400c07440341001088003408131542018240e0312100b803c9075a500505540d6914410442d09580c45004210000d0741c880422400240201e404010300403150354065074038a000003000b400340b03840b0741019542c1c2c5d8580c0d201d44a0055060b00783c84a00c0d0a0401054113550031b03000e0070303008005500119a840d4842e9030340e0b4064190603001414400c002c0d0700156031040b1402811507a0703200e510a0f03c0e02111111030803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 90407770 1250 90406520 90406523
    0xf040504020d0c081014040b0601030c0905030a081312030519091d04210f030b1c05061b120f330f0904030206011502010b04020a120b0f24090a03 64
    0x45e048480040112030243e84000003e00010115a414000400e05004049802c14002d013400070304101204010340c0c1404495100e03a034580540c2e04881d051001c1c0b40000d00c46442c140c039941807070765150000c541c44548a00c03c043c002a20a02020b0030700c080c281d04058040c000c0c0d0a1812203a5502d90704000d00c9503000604881502014051000b0014007825079a01c8050940c507600501040c02002081038010350029010143c41d2303504002d00b40c40d0030882200e4042103081c0840138180f0341c104190396150958007640401c5088400021142020701507500c02e403c103444003422915261182c0d0403044015020045480903848900101900c081135401c006400580580301c1c0500ca408003c05080c0e04141c481c0641c00074020440002d81c00705078a41507070b01007400306040503240360701240101b40701213200b5006440040c4d00d140150b0004024124420007110038040044c0e45418021443d04005903a50080182007420392145031031500b4081801c071040b41035007401694000038800d02200e500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 90409020 1250 90407770 90407773
    0x306110c060f06130f1113080f0102041d0c0d15060908030c0601090537060b07051005190f050103020906060a020d120e0d030b0102010b010c020f040504020d0c08 71
    0x140000c0c880e406022081d072020801d5604025440c054021684013401c10210140f150354030484111100c1603503006000c0c102210180e10b0b111405003400850a80301400380c4d8031244104800f42400740014002c440580307400380880c10140242241e1031407641405404110403103400d101e0754110510380d00c05d902c20702481712210462035180c04e0001e0240c0b00ca07a00004041e400c01c101144d01084000340b0103044074080440040c0c142c2ea0021840003004006221400360300b02407001c0e50000010f001a9140b001d602c3c080dc0100c20b44c3c0b0302c012081c1d84195074000700a41c08c0302260a44903410760380165840b5260644206150050b43c0c00c0310105c54054498913100340d5144014019070600881242e8001d4050b20020b15003200600c011356500400e04a4004001000c021042280c00316009041c0044000080700c120500440e03000d4080c241403002c43d4019071a1840e2204d1542c0710308843c1c00481d80241104031114400f00901c0080c11004009a8004035070400002c005280e509101c00188003410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 90410270 1250 90409020 90409027
    0x61614091914011b02090402040209090c130b03010320040f020706150506090604030605060d020d0302010b1206190905120a0207030c140f01200105100519060c0201050a09030611 78
    0x71078440e0320122040e0b18104201c1000c00040752034020080035841e90100c1364140b03d96a1840010081d12480b6800d940010b000d90501080d18080405454181046803412008039100d9105a40744e00003440040c007010716800c403032100d8207240703c0c2c080440b8001403c04035545400440d1041640d10124080361420f55400c81c000350001440ea00c0805044126840344c0307032032002c0c0700041c4c03180100d00000d800156550302050541c1c0c2c0e800700c2c2c00c40039030b40505041d0001c6028180a0700a00180c0410380c02082038080c0c00a04990200f44240f04100c0300c40034841007044120150000c1c25000d400b110580700304c1040c1e40a0140100242444445507801018810300310718100b500c0d0a2240d115001100c3c4409201d00c00d9520b81050b0b5a2030300080c41c209026001a01060303a001446c1e01d8074001d03039440c000c00d001d201c0c180704444905030761054844c200354070100c11001006200d90310801001a05216514006603c20001842c5d507c40b1441d081503219100e499500c212924081401c00108001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 90411520 1250 90410270 90410279
    0x1709030a03050c18090903070c0b0304030314071b151b020d0c0c05060f070b04050c1008040c0509091002030a050601090801140615040f03081305030616140919 70
    0x40c065140e0001c080c3d1090703814010407200c02042000d84000349441181c654000521381d100810596504641120400f2080303680c2d5590000c19600c10707207055000038142881d051441100c1c81c0498003806095031303101e500017098246160022141481190008500c0b41e030100b8100d140d01458061502c141d16a20441c42901c070041e140c41d9060b07416000f4003080001e03500110b6951101c00e0300726441a21102c0d6221140c13800204244a030040007045c00c400782c4180020700c200021400304902c400d44071652280001c50013904d0301482100c0003090751100c00d20a122504202c0312240d084082101203c80c0c0d10212200c10050360070451b44640402d5452007009915a40705003220028104e4a008114541040d51510000c81c4002c0015003c0d82c40103941180b0207002c43c0c225001418103410441ca569124030300882c040d402102d004000119084000c9150b10700885d1840c090fa207441c91050003112002410340e031201c1143c071a003021318030901c050741a50f06c45081030f02409024100300c010b840d082 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 90412770 1250 90411520 90411527
    0x9061407031b05180402040b310f030f0503070206070303050402130e061308040506071a090d05030123100c0201080901020c0a06150305150901050a0209010c0b0402011709030a 77
    0x88044544004809401d40c0001e0f8200c01100c40882e0380c4a24040c660100f4000f240291250b580001400f040006400c40310074500045a001400c0c40c41580001104904521b456800d59009407501902300e003d00300001124800c0641d40d41d40b20320300f500e061440c15000600660000c030b9041e800320b900c603070030030085213000e002600a02e010848100708030a440c080c02960b4106c008d01c0b00b00c0d20304078040c0c0481400f81440a80f402000d004100c280d03140020b140201d400700042240120b0382100c1408aa001400417503810b07171043c0b055403010b003107030310384000d004c00e03a41e245036244030b41580420400282d440300301c248083d24060b6150580302c02c90520005180a81c002c0c00c0034416403040c02102d101080105548141c184c2008011610030841c0c00d2680ca85406588000c016101d140b110b560101c0640c0c80c898424441c00d4020411540c81c806054264410391340e04e9800030f0004003100340001c02d54020305400a006141001d490f001c0c800e00d4400085041d41c43d064035610205454000d16030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 90414020 1250 90412770 90412781
    0x51e10080601150c020d03020f06090f1c0509060310030b01060e0907020a2001030f021b12040303020613110307030516090b0a06030228050405040b0d03210906140703 73
    0x210800d81010754070f184401010700c1c2c00388a00031b00c1048190030550070716108110000840031580151a458144000d02c203a9445119100042900849038459941150011009071012690b155913181c004030104010080e400208a9030b104400320b10080003042c0990342d10b901805054031070381d1104031b50208103d402000104818110b41c041c540110008141c00c000c0980d000c20303002d40c006050000c00040c2c01030001807050106452020400e201c541c61000301001503035849100b55142c0001421441d90f031407086000107005a0300040120b000ba155004c41a6429400792130501c0750b21030801d0010742480b0540c0d1003030300c1503440b0303003a2590b04400e4440448002e04080c007003040383e41a0305001c1102c4800512489040c16804a81910340c1106c05c001c2d890301c135064011601590180880280190b003140c000c41e8001c92910500380300a08001e00c42c110900d8040c4c03181c0c4501c0c8503015800390740071000c1101e00292a01c901c210f4002403960301030414483d5506881c00828a800a0001c04450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 90415270 1250 90414020 90414029
    0x15070207122006071104020a030209030a060c09060206010303090e1b0a09050f06090913020303070f030f0906050a0203030402191e0e060a0302090a0203040204061503020c0601060908030a03051e10080601 89
    0x9410484c01c4000742d00742c0c40c44408400e00752009600c60820140540090041211b1250507000c0c0c070700058108621a802403810320b10640310065a43d49071541280e8501e42404000c0c04607080b210140070007981c810310345501c05510001704082e4620300954880641280b0080d038045219024103100740d24003580c0074411010162036143c00c0682c403070b000800080c5c000e0000c900c442000800c203410364409000700c0b4070180d000810100407154a00e40141550620b40d6501c00081e0001e0001c9140c9100e40300316074500c0c119500460464035603408120710309503142c0798102810b6403101c0c0012100700001c0000c031402c103007946003030303450717107811038800c0c49000c0180f020344141e10402c1d06000580e00d80703641541150813044016142c5d03070740f840070034014082134000701030140004129440035680f44c3c0041140d10300100035258a03036618803081e038400c4102d0143c0c1100c0d8000b8007400200030b2007684040e1707000900712089404040c0420b800c19058800307403056406150426005e100b83c4c01e003040841e0051 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 90416520 1250 90415270 90415279
    0xb0c010b01020f100207021306030807060c0302130312230d060b03040503070f05030408030d051e06090115030f020a030606090605090108040605131b05030d050705150702071220 78
    0x5081d1003030a42c9850445a80c05050f607804507a080640d140c469020405400000c8c08000003510780c107040d04240c10001040754060309012500e41d60600c24003e0340e80c003004440744001f00c1829591481d055000c8241c81a040040701c82e404580b580e820504c0c0b8101c0c158118000d543c0f5003181d000a016076196420070030b0190820010322000a600004440c2c14a4101d4003886c1c184c0182d2600310304501c0340d6480b1041604c00030680d0300290748242d202e140200c01d291040002d0182d4126041d01035070044403200d60007071031301c0010400341c140c031444991014034516001440321070b40304104040303800c0f98200e00300103903480c4000e00c6800d821003100c0000c1d042c1400c002e41040358201c002026480024001000c10340c40b4404604001800071f802400c0990020401e4004015030304040e00b0900c1c9031161034880d2149600749407a0f603020b24110f0b041303a5009405002c500781c0b001a10b1181000c0584003104500c5445070002c1d0156061078950141e507c9806603129415269414034802c000c008a554400e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 90417770 1250 90416520 90416533
    0x17091909241d06030a20010816080103030503090a020306010b040305060708090304270c0e0406060908120307020712080d0f0203060102100504021507050f0d0309150e0a0206040b0c010b0102 83
    0x40e400040d400150107880002c040d0301d43c3c1c0e208804642400c0844600425101c14100c001141c03003c042d002041d2810b0070380e00c80030713560745105440d16a403401802c400c022484080c018000300c0c0c840e800071503109078207508852820300a40d012a1030007000b64404003e030f68010030107004125040c8512504102c7c3c51609401c0d504040071040c2e03d0b88228840c0e441d101410306001d015103a20486500c561414800c410006480f504001400c2e581c036100c1081d116920b00100032a4080c02a420103068070f4102008041c0c00f108048000c4556101501040561054050004030054404e01d00c40e00c0740d01c11490030f0340f60801e8100300800e8890b4078040360034050042c403c000245e603000030440740d0703181400b00c04203458489001040c00d4509100d030075140340c10000744020501800040b2001a003401c1c108448554002030012000c9603800b00e40101002c850507200702030021941c20058a07000d5080c00c0e9048640d40742d00281090b07015a00215200d00c01140d1030200010a00c1000d054400c01e0014001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 90419020 1250 90417770 90417779
    0x111005061002010c2001060f12030e060c071701020d020a02030a0809210a0e0303040914010e040206030c0c070803160320060a15120305040806131709190924 69
    0x407084c80c0e085074405c10000340113295440001d41000004002c009903003540103455a188180e1500360420640118400400c014400d0810004480801d900003028014507400d004040008164081c4030800759034092000c0c481104084c402401e040c1d1b800d8009594503007210201a00d1014001c000440030f8128500b4030b0422030346c05a18050b206854144140c2e1760030250400d650f1818100340d45509071001107008554500c2e651300109060200340c20344110f0381e80c1d802001001c58001c0318020340050f02070000c201301e603020002409034206c811094620103078039080d20038516008129012103441d40040702605158020000c0314184441e04060100e04202044850380d821000e00003009041e540e040c071132911200c0389004000b400c01111b80b02d0600007142401070003608540104032060241c0004289200c0c10070340b498101e107900a08058002071540c2d19494181c00c40d000c40c640009401e16280700600400700c6100c01303800c14104c001103142121001106030701072800452115a0031a00601 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 90420270 1250 90419020 90419027
    0x3150911040905090319020c040e280201120216020a150807050a0e0307080703030201060e070c0303090f0602030f0a2004170703051f0c03060617040201111005061002010c 75
    0x4007902c420300c501040380e840b8602e145146100e819103060301c1441c50140e50b0b41003030780811134481c0da41e0100c070248131300b00341c83c041152140c40041c60555401003e01e5840d1080e68140c07d8143d01500504026540138050310180c01641c2c48510821002c05084034503104510749090304a01030448000e400119508540d009084118054100c0040c0040811a6640203104035101400b512000c3c0035244500d0395030040a503214080d0004070013550030034401050540203404014807542c0d0980d10100c10303d9590310150020b106a6505950b03c011100008010500d1400118050502ca01210626213003c22140080303da162030301075072032078540d034400c182c4201c1c0c3c5e020395041c3c130b03c00700c50341c1014041e44028626080c115070000b03045e40145020781000700300c0701c0c0c1540c00000300000d00f800360207000703a002c030102c0e000c0380561000f0880dd608511030032504844140d5001c0c2c8103040010001207640320151420852600041d0156224070802001742480b90f1103d0101d07410f40001d111610081301d018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 90421520 1250 90420270 90420277
    0x21c20070915080c040b03030f04030503070b0622020d110712020d0912150b030a05060f0f010b03070302130b1c061a03010b030a15090c17070e10030b0a0603150911 72
    0x51740b2070350301d803a0015000e9505004445590003412a010343e80d5580c1c0c030f821303502d0390044079003620404000c0000038000d06005d1010880d007015500d200384e000d48070328050b80083d005172002c4241d4503a81c501d08080441200014480325005a1081e1111030310f03501c0003407030428a039145004100c402030b41000070801650317103101100c1d4420355051505580e81c0b100002010030300440ea51510603c210b4038144040415010700030414401304d0207203a903810707125000000c0d01384a0801008020400540f40368440c2d80034190300340004a003101015500d03045942641c000c98803d5400524107040807903080703064450240146201d82145209040c21100001a404140705515405000000090b0040450b602014000454031250080141c540080b0401000325000110109030040c10219440d041491a03034071810950b540c01c0a040c842c0c0080c0082044004983c20a040d00c0d6001c4841c140c1c4c40300e4041000d005140d40014010706444c0600c01d80f000e071980124402407415025110454019080307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 90422770 1250 90421520 90421543
    0x1b0907030e0c09010609030209070509090610020a020904060501060f0e0a030206032d04020906010c051b1c05010c0201050c0708030610090b070c14030d021c2007091508 74
    0xe02004a001890704019220b040341d0780c01414034001084494002c1401000d890003501c08a640391b641300020394041c891410b1690b071180303001001400714508000030083d05a007607c1a1901042076a0206e20800801e440481d87e40307840b64018002c0b2584004108180e82c031510341030b032000300740e40041000c8008a000c0640210000000510610000d03020728404250300803030021488501d400d4528203280c00d07030b8128810422000442d00d298071400f86070040c1c6821002816084a400c50300301c00b40840781d010240c01c81e2801c030b1540414a14043c20314502c50051001188801e4600002030840d0300003806101155001d1002d6408650500d00303403a0b200b481620b500060400c480401d80b1010600c0d406581070902c006981b10070041104d20701d03811601041e65016441400740201520f07186000800030050b807044030305198115022028030719203440d6003014151100f203813540aa11031695149111242d00c2024208005e4000d841200c054550b80068440ba480c21f103c030340c58503400403941c0d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 90424020 1250 90422770 90422777
    0x40204020a0512011401020c010f120f0e150105030d0207060804060b01030906020d1a12030f070212060106020a0302100908030f040c180903090801020906070f0f0c06050c1b0907 78
    0x108502124028401c498040300f074038030018a40d41e034a14600903510300001880e40140541c284514507540170f840c00110b0103d182c0c0711244003050b12340c91000284450a40710810a4070741d108954184021301c40403c5000f10101451210740c10107051500e050700c4104514115449007008010546d0300c0044260801d07841392000c1180703001d00c0e00480282411440103404903100040c403201c41030455124500241a4101048843c4038203c10001b004000d811044415001084540028400e440c001d0240350b00c01080294015055a901e6290030000d81010700980d003e9600c0d1401e0680422424a541051a505004c090708c0d503569040b04d4000a08544080440704000c00d04001100d07070b0306c1e005003d00301d1004460306c21803c0b40c44080c00341010160045000f115002c20700d03201c10700813a180c6002c040d016070b02d084e2072555401d0388404603000548040d845041414005104100d4410052040c4d55589444d4007020007024104030304080c21842c500e13036480e40c030f0722252036520b422a4400c50a04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 90425270 1250 90424020 90424027
    0x901030803041217070c030f090b09120a06050f09120a0c0201210c0503060f010c0803061011010c021507030c020601031403210a061e0308070c12050a0501200304020402 74
    0x3d105580a500240d042e40811080e00d00b00f0800c035074050320160116010303a03513800c4d0300601c03c44181d402c2040c9000b80c4d0b592480410508841c0d09080310500e18140f400c40888021644946030b10302116000d030b80003a19200d2401c140016210f080000004030700d14200c001d403412403142c00c050412807410000130b06000c1c00c1d50280115070700690341d03280c84a983c18410310400e58005002040c1c1d40c01119902c0c030650a5150500d615485a0802e0104070340c051011442c58440108000050141403803410801261403075240c0646800e00030303c43d400819800030481803d14603c1d47e604000000e103640c0416113000d00a0712425800034002e070449410211100ca000c1c40100c160b800e5100d24141821514600010111020744035407800c0d104419807602000071603200d08400c1c468491030401440c690580c1c1c001400484c022500030011288100381c1400102e50b0765010555071000410b05035960381103007041e8824410203000381a1556900001419400103542040040303020207000a40503c1d400b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 90426520 1250 90425270 90425303
    0x405091605150306132c01060b040f03080f0702030f0d170f0402100e0604030f0b07020a1a0c041203120b102a050a151104061b060f11040e06090103080304 68
    0x350310019011402c6e906003141d18071841800150240c94280500c5590f03c2c2c28400990144000207031000d0700c1030f1080c6038030340c1442c41d180c044e480c0e00141446a25000200161001aa0301f04201da46055035080900044026000e01614558043c800340f43c0d401c042c00304204050505001940c1c0c0568100c0c1c00010300050301c0c3c011120b02e10325900841e0040c000003000300600c003202e4505d03441288183c10602595440100c1240c464180034002418100d0039081000c03c100b0454000340e22102054011742080e503100340b04006e41c50f0706001174000c00d1081e001c0c5004402c03d8024040000400e448019901c000100002c16211a035540400c007100e40f0768002c4a042440051203070555000f908840041c010303400d0400c60b042e0603014181d5200c0c035103180030301c005140d030080d102154503545440c0140120389402402514000804075101665011103580c484d42e00d12650303400f130001c0c1e0b0245440d0703070410440310f500441c050003071407041c200d001c01080000c0350081180d9100381d00640165405084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 90427770 1250 90426520 90426559
    0x30203060f0613170109050f0f2a0301020403080301051002070b0f0f040302030703051f061406031e010e060a1a03040303090c080d0f08010504180201030c020c0405091605150306 78
    0x664100d1a0f260345404c59007004c2001c15040442000d004400340c444046139060744a0340c64603101e07107a207004d030081c03020703082e0300c031003080c00b402030524200400581c0040080009089900c1a0002c07608240044010f201508003038100600390702507400201007090909a1060490080190099160034000b0354100d150444034256001160b0203022a88015260714105440d62130460f00a440c1052007450700042c403841c1d0140104641e4602c0c4446420391082040c08500d501c002d1140c10203002d20b00c000b450840060900713500030a11444801c1050804808210380c6018070380c0300c004080410741000700458845001c581c0c00a80c18100000c10720901e02d00260803240c160b0020307015024140a41e2601d03070700100e6460034000140d44047e450f80c0c0720010001150094404c101c03403001070040410055020303901c9040c000d0f609004032001c42e04620009030644204942ca41d038150003c03400c0c4024594203030b40c60b00252104076240210300903681c0030440c2e01e000013080b25220700e214040c9407985500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 90429020 1250 90427770 90427807
    0x61103132301021602090f010e0109020702061b1506040e0606060c0106030206040303020102030f0a06060c02010e300721030c17040e09060109022a0115080d030c030203060f06 77
    0x1030340d03000799242c58403030b42100c0800804c10300aa0142401c480080c04145586250f00d050f074040003c0c4040590030460494000d40100c0c9080340c01900800180004e0343e504014040e6410081006001d10421404105481d44002e401c6078055410801e2500174030340041516540f03c42c1c00d40380caa031182d1071034602c64050415640042d410140001e40401819410340003144207201e90320301d581c0c50303807900e0016004942d0301303120320400201c0000c1004019841030b403001602940007850b80300ca0001c41c41850710110102003904900860400089014000c10f00c4658010046004444950210071440b90302003051a00000c0c01c0240080b005020001078450507a5580504029a9150b54031002d02100e040c1040d9000807080c0300d41c0c1c00015680d00e49008417004803118901d141c00c400d00c001c8c0b4011b9440f4a0480f202c4982d5210030040b20303000010703815400100344100090901c0d0304640d1018048409008100c1c08041c010803c000c00c6072100003100f03100340010f46805686040b00d81c0404c11622 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 90430270 1250 90429020 90429083
    0x1201080f0f1b0919110301080106061d01050307090b0f040311040e0703080706060b040608010305011407021b04090b0f0402100c020a0b03070e030601170d09030f080901020f0a030302030406110313 86
    0x83c500340030400764171090000346050300c407010000c02c82c0ca61581410780340c05040e01c1040c45444201401002c10354850800785420055504001842d035458420f1101141c0007c21305441010340440e00f08240002c09040102010003074a0400442030100c20b10350302c0381910b000c00b40001100141140c01c201c2c5685c0040b00510704028400c0e141c1d512418010035001c020300c01a900c44d0300f840d05803404600c00034950b6005c1d210b00d8004080c0c00100c0100d10408941e0f00c0d820b80d038840d5035440d009021a140c045441e114080300028107200b4641441082070402017010f074001004404238803000180ca41088050035580c400e8202a120358911404580500c0903d120319014000c46000044024451030360090020f1240291450500c001ca001c480c8480c1910002c3c2000300c0c0c0710303c1040840d803d40300031711840c08103206580c25044a07900306440c102e03050700102d00080d400010003050019034450002c180390b69032107003491400c2c16400caa01400d42100082d003201d20260f640300d104910082509004d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 90431520 1250 90430270 90430321
    0xf0c1606050906070f0f091512050a020901110a03090e0a020c0109050f0d050f030606160f0c1809080a110c030f07030c080307020303040603090303021201080f0f1b09 73
    0x245840340003076444803c260345a2011174613100e10004030b0f5000303c4600c0780788501a502c0449240c540651034400b030501801800611240280302020203190740140740c46400192000f5950744c214400041c04042002d0698143d034208076015070019a1100c2d00008840c182202421661a0140b0400081c0708403642c5011079841c024000c010814045003803100b0364140c0080d6012960f00c0c4038250394900c60414000084002080000d0452a1400243c980103511800c112400700c0240e413001d02c4500d6110055a01d824030b820200600d40d4203030302c0304001c1100054103000088003941c40ca1f015010310105071f03003444600029400c003420100090111424010100c9441440c0c2d0814540c403098180030680b401c0f100500040780d03421b000070440b82055030250056141c50301d0004110014500c0090031810541c0800401e4448251605628060f24000c009404240000440da41c901000b0070103207180b540000c5200f032952100194103200f030760003c1c0c0c2c40130103a83d9044000703551000e50310b0124508 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 90432770 1250 90431520 90431531
    0x150c030c2108070806030c011704080c030a02030c0c03150103031b0b0a09021201050903120c1c02040e060f0901150314040302070611060c1e090a06260f0c1606 70
    0x2542c050206401404107440343c020700d4035907400303160300c610240c0201804140c000020024803082c035a03080d41c2c040e00441d46c0a050030380d82c08450303003194403589003d00140c0c80401c0c2c050780504181715000e8483d50880040c2140c6a0030b00c00809504414403000c2c0900c4003010031240940511900498000e0380611541064a045a0301783c00a01c511070090303000c0c8030755821340100b680c4140703c0c2c5409410520001c44c10400c2102d0a450b140b42d0040c00150300740d07424895560803200e07000c81c088406440c0000542c840e070801d494159101c1004190520461203481965220386800c0407142c1500c0261410000e0003000311810f50280640c4144441c4030884503041109059002c100300040c0d882642d01c9205860b1100007169803510f06a61103649170300c0404c42e9411007000e01811040f0341203400724040c00d0052250001c0e600300c0c1c07503034082d9001c01c01d40d08011100310319402100b201c030b44510000124a0901c5c200708540e60400401b9984034980c00688030b03241c1c80440d0501115542e21202c14040f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 90434020 1250 90432770 90432833
    0x30c0609080606280f0f0e041a070210050f0f071e0e01090f121208160804020117040b0106021207050a170f030a0903120507120b010e100e0901150c030c 67
    0x130080030303620907108844207a25012550005210502c8d0040d030708034182102030840c80441c00b8035501c000e40484154420344440303980e000f07102c0c01094818840b4261501651415034a210090031000304440201311081d6410017101d0039108100903503a44500e42000303c605c2e1400117035104541c940003003141c10852000010381107200c5c040b9001e8207108040d809042446840203171611141500d11000400b01040140e000922075010140c0c403c0c0145810444040c44d840640350611060780d060310b0b50b420880041c00826010000740e1546540541064030300007940d00d80c0743d00ca101d03840005103003036680304080c020300ea08a400d0322110303a0910101da0b42d0b414401c04030b4000b0007040d1030840118403103d01461a545680c460944100003035141c1041202244134000000d02c43c1103621418060440310b030450039103444000401c032481da6242d00c002c040c818010841e116105a02030819211480e40d1005110361000f1001e4020307505044c1112610394034a4450b9241008284003a00c44410160b00720 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 90435270 1250 90434020 90434039
    0x11160c0e060a2921040c061701030305030a02070c0905070810062f030307020d0207080309060304240e0309040605030a0201020d080a020c0307030801030201030c1d0f03010e100501030c060908060628 87
    0x3d01680c4500010451b160790b03240b066030114403800300c000b8031000300001000428015002158043c0b50798100516140080d920103c000b1895000400c81e1983c1d1410040c107a5001040b041e013017440e0345484291a03280050003070862115074001ca408074a191001100ca58591540d880404103100036643c484c6400a07009540d00400040c1e000144180140001d070320b4000b008440e036012000d040c60746143c0c1d480c0ca40e02120070f8941c1c2005003410010a0180c00204c0e21310402c40c21030828809940e8030710202e0308000503240a41c21440c8250000300c10240140e80010b0f4050340c42115003080b94070350b0f0f01e420324900240035546500c5024000010000100341e4031440580c1624400d0700c0402400748003a1086411240c240f12003402e540d02480b80f81c0c0701e854106a02580f4010080c0046080740344815941d060070f02d50314849070502c5d107400040c400c211014011501501c2603142844500d403400340040e550307100240449010310280203e80000c42900402241810706080300c005905641d41001e5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 90436520 1250 90435270 90435337
    0x1002130f082a0306070c0f0b07180509010e07030b030f0706030203010603051f03240f050105090702030a09050108060607080703110d03020a05070611160c0e060a29 72
    0x80b0451840c60811481500d4010042c4919201a008003040c1d030b2002000d88460b0701d0304c1016680760003c2c1d4141e900150300d1510fa82c1c070950711030380c07030b44c44040030310000c24515045030700024468800c010061100b15000d079034040e4000b0603450041013265850700401d052000050402c2400d00451002240454054001758105c3d21a50b4081029a50ba12000d0303280442141015480d114030780004c201280c03000c0c00c066007103008107100d614151503109030700341140d5000340c2c81c0040d1512800100700e54a0600000b5601c2125400a5071500000c407100a200c04118064541070281c0c007808203181e81c42d0ba500780e40009a1240082d6030b10106414090880000422088003c1c4504040c00c4003541c840c0c001d46d2601105034690030f0910043e50754280251400110300303c90300d6005e0019041821001d90302071050750060380c00c18606802c01c101d800038020001c04a500400c50740208100c0c8030350600e510081243e42c02101007a484d8285d03903112081c030403c03c822070f00c1007000c40001030498514190 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 90437770 1250 90436520 90436543
    0x4050102070b160507031202040801060f09050603030a08010324050f100f0f03080d0209040914010f02041a07051c020f10150501050703140304030903020f040b031002130f08 76
    0x40301c4895443d50b2007100000c00f9401c2507000039000b03006500000307005594580702c0c604500740160a242d1500d240c60300315141d070742c419036400c03018600401070313910f29106a68000c40700b074002e989050000c8001500c00041880018803d841409040810203a04041c01d641401441c8051000e410100e81039144814291251040e90380166800140181c800c15200c04440313413891000c2034240313141c4588503250801140740c400301c0d400f008020542ea866115034403000744140043d0f040c0300c4008641c02d0071100f02541110103c0e104000c14014a5844040402802e03580c0c1d66099880e0f042d8030f81103040c500e4150001080e10110b84c000d501c039a8000c03c0e130402d2820700500310707400c602030b0030441c1059410200b91030b507d1008544050025500c180300408100b402403c0c07074802c48903444820055030340304450583c00070352099000d00841c40c04881d441daa80f04122002d00c00344440000203616031b01440517603500c0e0307540002e81000d0410a580b41000900c0c41c88803031402541d4408055403640701d203044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 90439020 1250 90437770 90437783
    0x3020301050f04090b0a02070501060f0807030c060503041a04032003191d1207030503120a0b12690d120f0513020316030b0402061b03030405010207 65
    0x8119942001d100d02c02c6925000100203115440b81d01b625030007940480c1c4190b585541798100800c80000540702c1e00020074842009051507031a40c108490076000310741001c030800c50f0800c24000403640301e100c503000d1613100d1044183d1540ba64a401e4441d0544c01c1c0766444c0c9240c0140c0306154918011019000e071240e4111038810401d6031010480d06010400b505c40d00032840c0d80050385050404201e0a0424000c090031554080d481e5120300d403942e0010b0b415201c8003800f44d800c2182c0e0b41114012803100701000d5411080c1d80201141c1c03039454602c490401c4041075000f1134000c1c00c0903c80080d017802c05440303c07803420200400103003500818103454180610016000000c1441c4004882c030901c1d80d41e00440600000d00032a1001c03030ba002c1001d4590410a91558801510400103101c1c0074001c444e142c04034030444550b8414941130444d41070021141d4101c00c002000420300000b1840e038010341c101d0f1015a1051120440b03000c14258090b4022148800700401080140c15401070481e18040c1b807 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 90440270 1250 90439020 90439039
    0x10b030a0236040b0d060b0a0503100c031103010302010f030b0102010209100521040209070804151407121a010c0203030c070b0703030e031c02070c09050c0d06150503070f11030a0302030105 83
    0xb018070094503014090181c0001c0e00120200c0441c4456004440492008041c150250b80c0c54001902d486101514451200d9841c941c030613000d9054892210050300c41c89002d401c541c5103800181103e003d403401601450740712070b110002d5070b00c00e42c1251155400246001c1c2c01030750b00c00300200243c0041440071015502d1581781c0c100c044000705d2641c401c0b07500a00300001d6a84101e012a00400c0140c800c9400442000e902d003130b404a01d004024200d8034426000065281003840145040c198404c2e0410103490102100082c4d5888013488038149020b003012618080e035440402d04d50720030b106040800d1300605501003001811100100074540c017079901800004101300d1002e8681c810000300d5894035050f4680643c0c844200d07005031000d030740141c00e620380d91130340d4810602c00d55108640b80c2180d4100000d980001403210320448014140032072440011840c4064058100e100181c003401c00c0c00100d151000d04903100304550407602242200342c80d250307080f440028020350002c0c000c048c030451801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 90441520 1250 90440270 90440377
    0x6190206060301050402060f0a090506030103061a010c0308010504110c01020c0f070b09010504120609021201020409110702030706140705010c090f05030d0801030b0c040803120726010b030a02 84
    0x1401380a0180343c0003040399180c0681401003100a9010410b000c1c148031340038000042694901c00558021070040001050000d40c2e002070355110001d000f0075506003c96035604c3c101195103d0a800d0554000351000900840121a0040300e0f004120509820758000550a1901c420126021001c160b141c0202c6110a841e625003a43c28000c550101c0d000a20501c002c001140059488003030703d6005980c0003603103130700d03e8020038100c0034116030600341a900024108050011807083d0407800c41034001a0782080c0007540046e455090500c2010104101c564884804000d03210850341c000303901100800000030340c0c80000d0b0100c02c20348114411010350805c00142c1e13040c045644c4010100c1c5659240642c1e0969841c0038124401900040c1601c200384004a1040c108000a00c404016800000d10780e1410b200001e0003e204072180d241d240c440c541e460803080e00c0c0d41c8030040c1075a4440540c0f0752603544801c0540000d0091a00101003401d92003201c0041c0e071b4650055490701010900341c9120b48402 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 90442770 1250 90441520 90441523
    0xc01050c0604110d05010207030e01080714120a020c030d06150915180b040603152c06030a0f0b0406050c040602121305030105040c14010305070e100905061902060603 73
    0xd20186140541014002400150480c04282c2c40000d009100c040841c2080d220f0508a80100400310040b070402080c511182d03800401995000b0301c1481d14192008051124080c1400340f46185030314005d292011400c50b410503016200c100c4490303000c8946588418031800058032a5202c0d880001d4030303600000400e1383c400c0c0450382c10b50340d60313880c40c00d001008000115800b880034214000048841c0d40045100355014005200404580d5808a405030303c40c40e1100811643e507000002c040c0500e040c1c2c12103608901101d0b2020144503c1d02c002e9a52042e010a0038900307680d4000b040c42e4000d252460401400000785405140901010410799590465103040c6100e10b00600340503034841d000c0c00743c80507a034000804003110540401070041742d42d5030201e425650183c0c1c048484c010031060500c070300c5042d213004220103a82441e0521003418075440242c1800200702d01140103400d85650154100d002d0040c00d8000c040c050300191741d446800080044c84041c2211040042c010040402c07180c1c0350 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 90444020 1250 90442770 90442777
    0x51807091d011221050405031009050d0807121d060702060405210f0c0109052424030d0e0103391b0309030209070503100302221a01020c0105 62
    0x1025405160507400c0810b08503c12424000403a0200d030701010030321300e90b0409a0300c0600740314903807240c9840342c3c100f1082608149000c0d10b07610045240c01c240c203020410010708545520b0003820801f085e81c5aa000c01c59000c10740521807480075050808100599095581401c07805c14058191006915408003c80e2520420340e0050001c1d8090324440703c01282e10900d1708071902c0e5840092f03252203d05220303031071207804c603415446450350f4442400d010700000f844085280400c034511010405000e80b0751507804000170b0240002c1c445c21146c441c210104411210424030b030020111040d140001000501e22010b654a90340000d06007583d80f0300710700508103c03000402c602d41004104080303401c1000e22820203040d1080400403a480a00324400b4580c210541e458000e513611103266045006029505074090211020031804100300200e00c05800c0c0128140c03541200c00801101c040b800c3d020500007003042980000c3d1070003400740060b580d001d13503511000f0020b0b020b0318141000b100043d0742600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 90445270 1250 90444020 90444059
    0x3070e12120a050706141501080f07050703030f050f07090b07020109030213090b090a0c06080c0304020d0213020d050a0b0405160c020411030406020a02010506060309100e030405180709 81
    0xc0c88005156030316a0340d903001c2c210441e020300d01941807400c03a84445c1c0a55064420b01401616040b003070054100c05245941505402803c1c000e0460500c20b2252500e18002400c0e102041404140c1104061082d0000420764403011001d11807070801c070341040d403210381c1641c0c1000890900c44000420000c01c41c01e950059070140c5440034403514540a01010a49a081c0140c0b459500c00b03181d40018814030032103001d44550401403030740015030f140c5402c0040168111805220080b4100000307041401c08880e8019410350380d00c0710103150340c80412001a012511252120f001040c44c11181e400340e0b01081c030a104042041c4280b90b48501840200e0b403054840c0440c0b848244002482640030364120780c4111320203000014180c044807562030450f0030550f000c448054002500b032980550900135650400e60840d000da07e5070070b21800701c0b60740761f2820003080d180540351500443c1e074400501c140c030000d101c040d084604500341000300b802c1024048918401050036804049141c5000c2c49003034a109 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 90446520 1250 90445270 90445273
    0x50c180a0515070804031202030403050d0c11010e031204090c120c020c0607050c060f09180f1801020904050705040f09050408043005010509010c020f030d0209060c07060503070e12 79
    0x1c4250301082c10ba02c1d4484903054807003000420000000a503004880807242000b64040d6440e2400c8d850800d080008003002d1202b041217242d082c0001c12417500340c001c2400c0c0242084500c08810a0109007804004145000442000f04000516001507007044080c4856a42c0c3c1151060300700080c5801c491650300118010f80c0034290a042c28180304004040840c06502212000c01c0c588000806951001d0340d00031802c0804110000c087c20302c52142d442051001c1645121445e044030401704104004000c1166488a2103031080c01c0755081d03046452142c40501306100c1ca1a150201a02c0d5501030f00c2611007030b072109800003a07690028407540c0e000c1d40c3d00200e01d51516142000c0341c002c1494000402c017805814030309184200100c0346c01255070622401c0040303414500b04440030b085440c490341840035504560354019400034040101c61842003058030043c1c9503d018408241c05004030203588490b88149640450b08a0f0810301a40c881c01441d694255141c0a0b20180101401d4414260b91603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 90447770 1250 90446520 90446539
    0x21309020304030504080321090a0201020a060209010c0c0e011707080c13020405030d030f050603030901080a02250605010812090f0d1b09020c010f05100905040510050c180a05 77
    0x45295035002140c0107402850038078203098998035800d09681c01514a40014103041d41e008029124a42d82e566100b400e0700003404d11804140c001030340303482c0044801050b041d40011007015580c09180c084642c1c075000104378865684071024407030918402e02460070b81c41d00c1c001c41c1600d412030005a4209a07462140a0503150101d1f50600c0840105030003a030001c01d03024032011400d0f440400c9218944182c5075004140b0120b2290300c1000c44001910150190300200042000c5903081017089070040003c403001656000c0403c5030980c0c81c5002c500d0520f0241c080007480050042d69000075042c1c524050a0ba021040506451300c41c1d031040556207074010f1140d416820180ca400314041c4a12409122142e0009450b4030300c591000e021038203c0700c800f80c3c0c0071031010240c0d1000d1107a0300c008003001008000b40e040c80051060620300a01c03940c1d803542e403078400242c10460244079080d124915602d040c03140d4107180382031008980040303040c001100d602900c4902c41e0702c0c119103075404852014044804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 90449020 1250 90447770 90447779
    0x201121103150303090a1203120509030304120504060215091504050f010507020703170309070911040905010801090b060d0c03080d0906050907030201050301090b0307080a0308011a120c0a1206080f0c01030213 91
    0x84d0b02a0180c00e0f4140b01e41400c80580740c0f149c42c0102c1e841003806801039640ca18040c901910828403802c020000c201003440180f100c2c503000600030740d0104030716622868603503030b0300760031b52505201c200800c0104523030000740020800300042800d0307403019410090006076280c400403170303948506100241c80c49860703c0841802c04080802140c0018001c0190b03800c11713840d06000026a070030420020300d02072001074100b0503402684142c9014005000c020b119440403900c900020540182c8600d1283c1003c645042c00c00c0910f158840085510003000f54491034150060801011401416500c01c1d041c500025100301000c507010090782d505840301e03400c607420420100d00070481b85c010a41c042c49100004200b00364108118605148699200002903040200e01d0241e12952056a03290728800e010075a510140c0c400c11540c070040b80d020701519a003580c0c000312041c04d99036821031441c0d4030b004004506030101041d03485d400504c0d41c040f1002260100c4c0110103d215602100040d08141d900a00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 90450270 1250 90449020 90449039
    0xc03030c03020a060507120f06080a02042a090f080102070f0b06011407080c0d020703111c060e06090d0c0302030306091503030a08070f0504061b0201121103150303090a 74
    0x4100d07010344100d40c0c0704081903949100b1500103548100c0890001035240c00c0c030107103a00903155030b02540c41040c01003500d400356035560769489030402440750b91140103241f0019003010384080b230801580d0b4041c07920f01042101a20103101d40c058072a1083c0603920101c0c1d0140f0500807a00e0300340d84030180c50000012780c1c0700d0010590000d0a1241080b2588140c09a085450400360403064040c00915540b5142140d00310314200c50807841d2025500010b0b402c20220f2490308041d0600107080d44d03914cd0242981400c44e0015020150003400c0364907090701c40f5503862000504610907031607401101c40441c00f540c410365241030417410050060f0302c10000184541002c1a17000c5d04a03171500001180c0660000c00a404c43e08500146000170310354004028003540c0c4007481145640b42400c020346810308041000308402e01441401801e1782034032902c1011640300310000741003c100d06a08100c0c1c1c13040030400b086254000e80ea0051001f2002c07501341101c0c500407044800c3c85400502d0003458914204040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 90451520 1250 90450270 90450287
    0xc0504210501020f07060e07080c0102060c030a1508010b0310200c0703050102160b0105150f181203070b010509100e0a020d1802090906010b040504020d180302010618090c0303 77
    0x2150720395003d00c460780a94424401070142e0b40c3c4254000b24400000da0b45030b620f40113181c0d224924552046590710640e980202c2c0c200e0300040c0a0000f645d41340e80b8031450001508081c1a00c1801d811890300c0051940c07419805002910801c805841c0080a00843e20301510f00e182c0f4215424940e450703660b000d0101c218010b048000d00d171426101c410307a0f203450f00c0d42241c2044a80b000040b081260b10b80800c880c4451250141c2402c859030701005503610b1400340c482c01500c1c6030604d103e8000401d229a81110b11113022882e0000303141c1c200362100c05410700c0d04c0b40c003c044d003100c2964400c0008030300f0346007000c4401e00c0354900001c10400d59103481d0320a891000080c0502200c1c41d42000420540d200782d0150420200105450281b220410b205200e6003c03402480740e00140c101100500010000c0c0044804540c02182c000d17803100406000c80e0000e0444a00b844c08140c9070308554001c1540640042040703640004d0a01c00e000d07001c1c281401610151907008082080f030500902c0001c0c040c4051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 90452770 1250 90451520 90451523
    0x61503151501050a120204060e150309030702061602030d0302040603140103020310110403080f090a0501050324010e0604140405060d0302030910030209100801031205070209040b060103090503030f010503010c050421 94
    0x5c081940c0750711003d00807a0b1041c0c2059000400070044240b042c00d10380e0f0600b100c0c1100050551940c07410880064880c020550000d10602d00001d003801e89c10a4860b000c0c80d840d030010103650302c1c5044603801a00a5000748160380202381440b42c01d140031401c200116040380e401030060084c80a01d5001c0c0c80c000c0c500ca055604110b44180008408a4501800791000d80c0d04480c0c2c06907288101410410a460660300060412504004204c0004005165801c004100580500d00000c0c0c1d070b0016103454082c880e41030303000100428001420380d619014040d840a05650401058507000c06120030480c4403040a00923070302c200407618442c1864200c1c00406107092500506020120740014448800302510400141c01c21005200b03200d139800726201c41c00c07001d0520510b0b00c0300c01e90128410000060000d810151200006081d0341d00a4122000680c3d00ca07040c0c2e5581c0c0381000d1021040403003801040e00a62906c1901c131440b600950844054840420107030303262510000e490b11010031354400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 90454020 1250 90452770 90452777
    0x1b23040b0f090103050c280509030109050303041209030210080a020720011d0f010e030a0c06090f0501140306060304060f0213050f06131511061503151501050a 70
    0x1000030428030090280c20700c401200d10807681c840441c0c00040644902a0420400c00d408104600d4040040307050141c42500325803010450300d0049000743c0e403030b000d06041c1d55015424040d4490800001000451049105148081e5080e5000c5011503010015020094200d41c0c66140d0003103590003140d50710390100003160094a407020307554400004040c2203124448110020b00d0382c10146d07801c1a01516a80c82100442084840000008003040c42850b2400e0502010041d140c0e49510b0a000754918a500090202007484d0780b02d100400d209918072846650711120880442c03950311803c20111030003030102d003803411521507508002c0c0c0790344040c00c22141d1307a80d40d80d54090700071003074000742460000004000304820319040031b010081049100d000d104400401501d488480e601c440c1400b59140f600029175542110b00081da10712030407004450b00c5d40b080c00100501c55456511440f01004158144d0722651800c00c1000a800c0b0700b59014100200c070302a900ca81075210300061301c800440d518 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 90455270 1250 90454020 90454027
    0x206071218060e0f01052203030207020405040503070b09010509030a030b03150106020c030705030f06010e040219090f0c0201050405121e041403010c091a07080d18061b23 75
    0x410025094010740100c0c0c0b155243c1100483d03001090101c500f0700000780000b8443e6180210078000100c00d0042c02e5540141c004e54040e0a151203603050b540c0d5142d025208204504050038400da0701c0e0407070741d000c40d40d15032580c00064101106000e03150040071204010f50600d82ea0010a03000b400d2134102c15130b098403070391880c08040c0301c0d6108214004d01194000c0c2c0b16880f8200c041c142000b0158000c14003e07407004100c207a04041c0041c07010704562908580018585683c030015000006070422580030000303d10010844484d07580c8850b480d0041450304100f100888a803d0f420380c1c008940190180c0c20458010804104004c010319003903d034815880303400e0104600302c0080d03800640240002e031584008110700382c1024491040701d1061414040001032504001a5a48104002c0704104041c0480e10104210010b41a07a5151403620300501010450102e80c0300408041e02c001c1d21450b00b41018000362506030645454826013039a240714980d100710000d050014460b080460344401d042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 90456520 1250 90455270 90455291
    0x9072904050402160f0c0501020105011203020a08090d0507090b0102070603050903030f280b03070503030705030f0d0f0204030b0a05061c0f020a03020909030d06060801050a03030c110303040f030501110a02060712 93
    0x144000410341b44107510405986060500080c21210160080c68400000c2208000400d800203a40c4421a6001d095190b603800100c0226032074020304640106584200c500100d001c2c2070b550004a0459401c4c0c1c215110103075620303000c805442050302c041100750010000f08000491203072084e80d102940304031166001000400407010358518a01c10f030f100503647c034180c0800c0e140620040300100f00c114000c500b01103050702d90030307264425880000b000b9117000690522a8000b9004003010780d1021808644403a500d0820401a40b421100c01d4540f40c54000045c925242c070341c10001149180a4480c1c4018000303940700562500d05900a81c0d00038140c10700040181e4900040034460a190005140c48581b2002100207851264010206001c0303803000601c02d686404650000701c94251a083c503000211341020740040e100c0ea1507144d00b5000010700411800c0e00160400220792060001b003040107403050400b240c5000f00b2006100580107040450301180c4120005405084085400100130110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 90457770 1250 90456520 90456533
    0x102010b0a0b040302031002092d0604060306080105070c110607020d0f05070617010e0622050108010209010e031507110f0303070e0f04091212020c03030907290405040216 75
    0x40b60300c0784800c400001410301c1142400d11001c003140700403400960404c007060340042d400103041c8580d800d1010000700301c0c0c980c141110210311034001018181699803600c86030000c01904450080c4d05240d8200400b10b00000e1050054a0049400414540020311000d08210366980156401ea030b0202c080b100710b030702040c8440340b00880244642c0c020581c040c60070101401d506c540311215841080004010005414840c8609074000d200301c030084901c0d1040d240b21340031801d181c0242e85a0740e01e00070010465810542c01840c01c0c00f000d0320303559410742c92601016560340701c0911001002e140c0ca0080f410b250b01035142c02e80d181800d00280c502281c1c558101c10300d1078104481a00020b5031921072407106080943c1200303000c0c40c0558003401041e281da1148038840a0901c500d104004042c400c0d160f0015071941598000c10448081d02d540c0d00740082c229541d01494069074011170782c1288622003e40060581a264055501c0c600742001c0c98402044000d40143c04044900a0f04a40c01c0c0700040340c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 90459020 1250 90457770 90457789
    0xa0b0a02011d06041106031e06040906091a1f050d0f14011a041b0f0e120a05010e010506030a0807060906050a020318120d05100b040602031210230102010b 68
    0x90b0000300400d00c1c05091002d082412a801c1c02d0140e8010014800c0d0049502d042108405446100b25000c0e1140c0e0b01050040420610141c0050f241414140030070107465542d00c41c400c1c0b0250a014144c940c0055020030700081150281250f1880d8020002410700303508074400f20b0f0180d0b905102800c00e40d00d0386240f4401007103007905585d54401a404a23500340801c1115020303003c0c1d83c200420100040344c000841030f401020402c1c1718a52218500c0303640315498091446030083c0201d10001d407690313001980c1c0d0100d220111015401c044002c124088140f00303807880707544014010f00710b06540342c80e411000e900854084e1140e0b0303102c8240c0004141c050007840d0191864001c016aa0300e40350b0100d4500c840d1031002000b664000c0d00b65140b0344082003059400c15280603100140d5629a92001e18981c411903002e40101c81d070100300007400325004800b0300b000e10900c0c07100120ba03030359980a079404a52a4003070181c4006460101080b180000c840c00381d190720060000140e42207022000808206 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 90460270 1250 90459020 90459071
    0x20904080c0a1a0a020a08010902090a0b0d020406021e120d150b030a0e0a0c0504110c190309120302060a0e0c03011a030f010603150209030304030611030402011106060a0b0a0201 78
    0x1580b4a5101c3d890414400d032103540302900700021402c10307110581c014810281846498503254000c602e540d0f060781c42c10340703480050000481c02d0350303940c0325203d080c0e002c0c5d08036206140150081c0c034540348001d0b0b903410b00c00503d0705c9603602034929003003011105102e68001d21589451156104034000b03202c0e03208049000074044580301e0036141e1030b080d4030f14815680d8892104186410000d0f404c00011462280201038480840300031651519060a1841c00d006000c070f480c41a1003882400301c041c483c01c0720360400160007642c900d800a900c0f020f8807441ca200003000140140d014500040b01006e003036000943d1500604195040141148002425038107101e84440442c03e00340c1c0c001010303140c1002008001034041c0c00a014030780c610341b1205040e002031180c01884903000103060300710303550a20032980070b0b6510001c10490700f49005107a26080c0c0045038220302281800c0b901c02c80303001000400520540b001000545141c3c00c0c00b800000c2a0481d1100c0c1003550740310300b0101c03039443d4416842c1c039298 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 90461520 1250 90460270 90460283
    0x2607060e090702030c06060907020a06050a050f0c04120204020a09120c090e0706050403020d02120a08030906060a0b07142805010b040c090308030c040b0711090105010206060d020904080c0a 83
    0x340c6490040280c0c51001410740000d42d0700030800c180d4100e9000c00c0182c0c0c80142101c48070703503903070f0360f030340306904100c0074442c001c0c00945010b0400240c0401da80c0300e2401004500805040c50381d030003409121511540c001d5003400018a014940180351580003400c00000c5407800d0aa0343c3e0740c54006529140440b041114607008100b0148202000c5200d41b40210100400a0074203502c3c1007400381c220b10460101038001c200540310b460540d1185a8a42011800b40b421544680541d041c4458150015261402e05000d03402c081a02454000400c0007078480301c0582510b413003690395925031a180c0b82d0b0303902030107405880c100459115107400a0640403911101c10182e404a0b40745c0a82115081e009031881503140c034800548140d400066201a0b0390312025082e0340ba1955071540c015405141d00c151000880050840200115031040807401c04d0140d489003882d90300d510040e40c480e00101c9007960445032140303041000d407609403051500b090007021031a180c21a00008036060070407100054480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 90462770 1250 90461520 90461537
    0x30b011211060306011b02030a0c060c060c080105061c060323010b0d0b1f05030d030e010b04050105220b060309010501260706080703020c01090308091203040507260706 74
    0xa001c1c2070691001007200456a841c51484c0c1040045c02d030528980c4040c00c0c0c0d1404603450750441d1410001800b186420100100d001d96952500030000884181d080b54031a003049010840d02d80510080c6042c0c07040248001c0c03d00f40c040300d00c40d10010400b00c1502884c1e03100d09002001c45c0740c00c003002e0a075410000b0403240c00311003041d800b0f0075603c80c00140360254000188000100e0585040c090f0011145200c58480700981e88821101401a4010325854000d60b601480d002e9015807013035558228020003800a11034400070031046038000d2040a40110300714800e5210400c840703500001d6107420100001e1241c1c6020042011034004641e0200760369541c900521a15201031070702209603032000401d40c12030fa00c0010907921813201d44030f860240310b0020045070701180aa0141c400c00b400c204000c214a44103810001c01d90301040c1c440203100e0007200502683e24094004070784c803c07a0032000030400d45190101305801e1210900d521402209078000c4040341d41805c1c84000020840780d50784052 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 90464020 1250 90462770 90462773
    0x30f030c2007051e100e01270302150901120b04020d022113030c02011b020d0506070906180e040c030b09060406060e06130c0203131d18060c07020604030b0112 70
    0x80c00500413140700704042e0524141459941d1220982048601d25096a0200e4800010707141041c900c50b101c034034000d00440e082844418a818101200e008035101800555100d80300f84a43c840d83c1403031800070b400c01480130380007c0107030040c00340c0e1100076000520709441d03001c09000300d80010406403001d040320700c2000110380c05010804d803c401000301040100d2180e980281c1069075499000b4140030302c0b4481c1e0b803507a01000c0450b0440a4020b003030001d200686207071981d240c0c9001c580410100e4140e40000c9112403140e40c0803100400c5900c0d034025140e00308040400d442c0300040040b102e52401c9140800020203043d13509000d241d1100040c03146d070900d45400d40c01c0e6003480e0400400c19400d0400c0150907900e01b0300690130040c5840c4c000500340310403a000c9080d807046843c1000006110100011a800702c055848082c20400380004043c0d02c566a001c3e080c000303d000014015030113171700820b48840e441d100401072140300034403d51400d9030301c2c1c1d50440c003240c00f603004400e031071945c40d103290 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 90465270 1250 90464020 90464029
    0xf120c19081e03090111030c07032106090219020c010909020d0b100507030306050603130209040302071509030302010e0706080c030702030c1005060319050d0e040b0a090b0a060201020403030f030c200705 89
    0xb0415107071b44c50345030031403406c550b05600705d004100c0e024080000440020240c1101c0c0c0181c11290b9000e0f10f0184010360320789444002170743c0441d2503160100c60402c07100003503d10104640c1e802060580d1100308039464002c42101a40082c61481001c5a5403103002a01782d03101c0d90805441d203015102c071511440305e41006002c0f5070482d400b09004540800820400d204c4d480420b80034903a045a52035080c0e01e4034142207203800c416421060302e6100b5000c8240e036039508815000c0c21244694003e1201c14069800583c8070302c020700ca04008a40114013140307501e10454003440e031150242c8112424010550069072914030034200d000b2895070f0b20410b00c845410305001c40501540c8210741d0416142180e5917941d07966201400040c00c0000b030350620240d0360707680c0d0041190b05000900c4000c1c002d80310b1841100034148034151910507242400c0c005005030060081c0c800702c0350182c640c078110f10300e11317901074015101d000143c0b0100030402d01d500c0d401da80314000d00e25080c0580002003207228203010610 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 90466520 1250 90465270 90465281
    0x60d090528031103030105090a02070317010e15010207050609060a11060a09060e0d1706010e090412020106080a0503030f100314010b0a06020304050303180a05060406020f120c19081e030901 83
    0x30300e044e04100b0050101c0e845500d6000c0d00082e8440c80140d0300da000d0304044407044070b501120416032403583d000003000c501c1c00c41802d000304607072401010f1004c03420005a03a00c40d11807003800e80040d01031000d0324181c50124040d110305a4a41480b0210300010309000c1c0c00c1420441e0b4240400d56645082c0c07003031102512070090020041002010100994040644a64040e0b4000d0719080c0c1a07074000743c201d91281150742c0e001d500182c4404100d05180c40d18122400108611000540c0b038803400003a00000010300c440e16030b070008051859034452004d10003031070200030055221900e003000f00000184921200ca00070740c18440c00020010845010003ca480325644001c0031540140001d020300d83d030100484800780500b84c50101505080c0b004900358120940c40141d0000d00490f0005119402140d03c074078100e0b680040e40c01c4080c084560104da8003640f1006039460f84200f03081c0d10504440d04808c42074130301410203a4101018000d410344104c0b0301c00040d0000d00408810301c1141da20034001c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 90467626 1106 90466520 90466547
    0xc080327030c0a02090702210703140c0606040506060f0a0315030f150522020609040b1f0e030a0b1b040302090c0a0e0f060d09052803 59
    0x40546401081d07400f607015000040000c0c2e6941d00c045200488100da0000e0071788e81c003190005100f0150403005089042c0014500b840c08541c4d0280044c00705101c8010081460381391080910040d2007018148030b005010a10048030090000c0c1c054980070902031400050700d1401c0031690b020210345904c043e1224036005400010300c464144100840c0b10746100500094480c0885152241c500f24250607400e00f180551304010300d0040300038650020014000300d1503108032000241700907000c000584c004070f07040d21490728094000600303001140c1c040340506091a0aa140c0075402c07500248001212030242c40781d200301e60428403e84020b184c016010f10041d20740341c0e52249541d0300104184001c00d480c80c5002d00113180049a00c404d0311030103004c850805140764a1080940405142140c039805003400301c035001e641e1200490100328503e070710311518208904000d8480c8603141c02 = true := by decide +kernel

theorem cover : BRFrame.Cov 90287770 90467626 := by
  have h0 := BRFrame.cov_init 90287770
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90287770 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 90287770 ≤ n) (h2 : n < 90467626) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
