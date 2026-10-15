-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5391
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:42:50.022311+00:00
-- url     : https://prove2.me/submissions/d9dfb695-6e56-481c-a4bd-28cd0cc7e114

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 969424460 ≤ n < 969604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 969425710 1250 969424460 969424471
    0xb1c05041e030206060f10200f0115080d09060804020103090f02181812030c0903070b1309060e07020d0c030e1804050607021203010e040f06020415030c02013602120f0105 75
    0x7a290300d0382c0702203284e01c0b01240b1030700c910743c2104c801990407503008e10b0710346013591040040c03035460841e00ca141700b0b1500f21264114ac0e101c00681c0c85071144100b00792119038880c0b050001041c00080042c00640c070a91284030103c0c41550000b503030401340c1d004a403510b440c0b40c0200342c04001d0002441484849a00030300b0341255924024101402e03114042410313800090181d580c800000300d0015480d6405200d00b5024103003015083c0e0700c3e5149240e0504001d03000c2d101d1207070b22171303e460400f15068a0100c16030b07214050b140c0007801c604c2c4c1d101d42c04940c40b294a180927000c100d8501c803c00c00302c0d541c2c110011a54a42c02c402000c0e18106418040c0c10a280070344807400b99800122145912620002170324110380a01d200001181d96038207004400300710070b0320001c000c54800034001c26038803102466068071628594080041542c01d100982c202c602c010301d42c0416001c503580b803000005881c02000301040304482d21000090355613000c5911551940990842030300300c2411641c1d08542481440d6024 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 969426960 1250 969425710 969425719
    0x6090903231206030a02061222030c150e0f070e2d07120f020705060709030c090e01020d110a120513110f100f090b1c05041e030206060f 60
    0x1507021403071080d910310840003a60040800b04000a40350f03a818010401140c2e005400300c0d6039150302e03986120b2000001c4421400d036600d06100850a1140c042d4043c14855254545021071202900ca4501d03c5015868001400761a1800c01c0c12a51080c0028910148135000401d2034505043c1d803400c40b000004c00b0301d0203044419038001c10256a01100001c2441e515250401d69200c2020445507002d0030303064000c5050410590404507062070340100549805001600c1403a200c80e9001c80b10003606100144c0340003440346050101140c3c550284402c020140c0005280951000c0301000381e40000c02e0b203030210070340414408005c0d90407072000b845492030b414040040e442d1010399006c4400e4402c401508583c501074401d41d80d42c075101451840c140b40140300d511900010350000b41a00c00564a80c80003500d5000005400c41c103080503100701c3c160b150b41c1c41c0343c039450724243d03070004190040c01660401c20f02c1c810701090101000a200100e40a6409800d06240a00a1020003004201540d014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 969428210 1250 969426960 969427007
    0x103170408030f16061e270615030c1d0736030213020a09080a0f120e0d0b15100903020405040503130305060129030f0712020f03040605090a051b030a0606090903 71
    0x187d40300c0c1110302d180a2307004200151104001024050000321500003c000489002c1c000c518241302e0b0380c9606c0c8440c0021603c1c400d940d05e090303080301ca20418032000c01c13626502c0303c0406802e8450b202400e0701c450150401d02d028079680e070000b07040c00300d440460a400d150b001414460041d032060421024089042c020002d041c021398580c1d0b904c52129501074110a403010f010880e091103049003080f800380042c1004004042420b100200c01420380c0c1d5214020000e4070303200080c1c1000d0003e160082126210507100382d246070240030150a0050040b10b40d4041040f146800620f02d0802c6c2c0302950190000f01042c1d03061940c43d4500a0750415169010000c1c034522907000c1e074a007000ca9600004c251100e2600d80c44424056940c0f482c640e408e01d4000740042034440005590401840c4294080d15042c88551200c0d4a01912900c2e01c81c005400c50304404804c040b200640e0404407000c40c00902200c4100d4801c0c2c41e080125189500004112a12947e26905060b841201d1000b81030311031034200c89 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 969429460 1250 969428210 969428261
    0x370c03060e01090c0314010b0d0605010e010909020708071a0702060105060906030a0f11041e0b0f0403081633060e0106030c020a0b0f0103170408030f16061e 69
    0x1a001d0052149641c01500c5112200740b15200350800409005030005014080d42c682c040640350742c00c001c0c5880007840c0307402d00010b490b45c840c104144540f07506071a40c644141c24408090007039032008000341d5201c0d038104a40d100061a084408004d1213882c00c0c0d000032414060380c007d08280701070b40400e12801081c8039548040c0e030b42740b0840b908100866000220b8004002c84100607091440408040d020081000200a02d101e8040c2c48800c4c86045102c0445890b1174420506016488083c0303044c9001b80400d00020301e80c140105030310b104a241c0700194a465503103445d6601140f254020329600c04180a401c10516080e07640c030402440d04090100c00d082c00e060346440391051065000b09030710340c804c000c000d6000740b01c18007895800c60302009207480c03d00600004e1a00030b1204035019005664072016a0036294287c8055803442806545004c3c40c0c0c1426004941201010458041c0030005400000b9694403c403074501407044104e00820000280d03000c115442c4004032070841e4400c549001e0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 969430710 1250 969429460 969429479
    0xb0708010b12060f1f020c06041203140f03040812010501020309010e1c06050a151e0306020d11070b1b04061403040309081b0310020403020d0b370c0306 67
    0x1282d907040d044002c81d00342d0f030781000900f918105401d02d640160b070303009001052407841d0300c1c440070a541640880d00412200381c00d006040c4074521807900c81c0300c605038000300003a00c941e0701c05503106039501100e428014500c010b221a42d006441c110f03500600021428441400100650300410b03090015508141043d00081e02d1035072203001141c030400352107110000480707008255406054102c0320070001e81c50903049140c0148290c240603503000109890002d10b059180321a80407212403084181d0020b4a1952558013035001200c00325505038807481c201041e412070602403e170030350240300d1031062030a02c503540007104030b9001c504c218815401c11080c0101c2e500310110300c41c9401d180c21a155290740b91f0508444858682d0081e4049001e2000d010002107103c103010184000100e05690340281d040c03061404074851440000d4000d00e104a202c000300b94240c5019078401c485181c40200c100790505007034400b900317807110f444505004040c103100314030151080c8009198607003810409039042c8285003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 969431960 1250 969430710 969430717
    0x10b030a1508030a17010b2805271e0d02153901063c06020721030804150b180601030e070f0510030e15040b0708010b 52
    0x3180003915219600c030140d0180c40a18020400c000541c1d07155003a100c0c004003002ca03d10069503203070051000202e050400f01c0100c3c1c0162010790081000f980094406040c6103c01900d9102805070038071011903502d840400c102070000c000c52605600d41d01410030414440070390b81d844c4109130414542080c041c0c230b5402d400e0156680407120705000301c0c0d2500d50403490341300d0702104030121400200084892880a001c58004400d0225001d002e0b500085015003200d6030343c4a141207a8400300e254045801c1012000960303046400340303851f194400d659090300d0701d649541c405001039125000400070f0300280b07602d100030303006001900111943e0984004100d40006000035100451003901500804c105500400c1800c101600b0300c100c00310b49250106901c68100c4503140807034202440b0151a4001003100c50580d040b022814805500300014482840340007200c4100340b40c0e440c4006150301204019503c3e200c9581c00c9138008610380785c03410110890014000000780140080140400030601056 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 969433210 1250 969431960 969431971
    0x10e1e01150c050c0d0f0203070801020306090123030609030307230a03021c0606020a170a0f0809030409050901060303030c0f2c120a0b060307030816061b0309020117010b03 76
    0x100e00b40c090514905040c5400d43d42035104101c5e6840108004c070380c0185c40c1480e8000c4007074400156507484e02c2400d03440100e40c1540e11144001c0181f2a143c06140203009050300b5440f0640e5642402c4080b0b4a8038905503800a110f500110400c060564000070a5412541d1f06121914840c602e040350082d82c0120f480750010b050f000314528031120000020400040682c0c5818440142c0d5032501075101e882ca48000c0e18882c0c030112914118013140411034042030016680e100060200000490380c0860150110302e050108010000f030050450158074064030300070f00005035180c6140340c058101e480610021041c8a13058500001d45c1e50040d16150350420b9261103040c000800d051913043e610012540c05500290001441d10b9010b030000300710190b035224520710109a19500c08056607003840344070060800e2000c0003100c0c0600030b801d50b1112075503c00c0201051540c00d0092000b51201140d800c00002950390b90364070709542c0e010412059111760300d902c4124550600daa564540d1100409 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 969434460 1250 969433210 969433217
    0xb0f1609031707080f070302070b030942180106180209210a0c21060b03150711060f061518031002040906090513140c09010e1e0115 58
    0x112090081d0b00c0d80110b60784194400c0680c1e070f40d465a22480060360f000b580080e80140b0401c00e02041c003541100490707000b40c1492008041c0800c00304000d1003603400c1000d40f168100341078820389041145050600362b2a40c040105110390b8034119081140b80220401c0110040c1e060001c1041786240500348003048076000e500c050303600c4c4010008a803070050380d00482c4444540d03031b44200c1c4500002080c004041441b90b01651110f45d0754000425440e01d0441c2d98900d010605150203000402e030303130300c810740d130300800740039104208001112a1500c09045440c000810075014000c00c003404207000b0380d540a0034442100f1100e080030030114180d203580b0420f04540600c0084c208503100d406075070440f0301c000e0090440b55469044060750003c1d4100388180c60030181000720100e04103406020303481c03140741c03d00404c1c0201001030300c030b07101c01400c003a03a880001d0103003000c824071513120460100d0181003c500044d0842c1426100443c5051034031114010380010354005003c56a80b82d500941a51810324 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 969435710 1250 969434460 969434483
    0x4020f09101b030e13060e070f0905030f0a03120522020607050f0c120606031b0a15030b090a0504030905060c030f0c011a0a060e041a0603040b0f160903 67
    0x407059070b0741030141c0718038500202066040801c259000b011800740748416216000130008490020080c1c90f107600594142d48000340000c1c41d4180f1601c43d02e400009a4179148004d990750b00042820700c03941c0c200d8501c06400150382c02c020b02d504010908120545908200a245001c01c820345244413881c0718001401d0301d40404c40306540c0c1303a10940e8243d5030460192003848040c5103e00c3d542c0c0a968907054001c0c41686d03100ba1000802141032403040708040c014048a0070100052441c1d0240382c0034495012511010204410000170124100d2201a450000b0030080a02c20089000c1e002001003445e54101002c000002c1d9110640714211070703040e100140c883e0800c0e0181c034114000c07890083c0c490800401d2507451000150071412040403942490007036464518284007010a15018140204a02005600542c14907600544201400034422846000141c00090703440d48180d030150303899004441404400301600400c650460740350b9414030303600e1000000140c400201403001520303070480301 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 969436960 1250 969435710 969435739
    0x501051b010e0105091924090503040803090406090b01021906020d11030a0f020c030f1c052701020a121d030705070f0806071b0c090519050604020f09 66
    0x2000380404160020024840c8400c4000d007207000780001c80c0c281703446201e100c10518242c13001c401100d64080e0055a28041c0e0720119080d44421485043d12406866130741c14460042102800601f014003d02070103981d449030384408000540d4007907080713800d216142c0b030f000c00748036a0002600000d5461000444542c1d42c081c1c20600d000740182d40c14041c2d56800c203004000d01c0784038000114813400ca450000c2112907104800e0034100c0c01740010010403a8010414200c007500d001c4080c1610034450340364250035840c90100b81d0300791202613071107220803c1c1e00c4140184100200f440000710030f048000842c202200c2d440d0040c21941c031045101c030608d56500445400b1400c0708100340815428074100c030764804880c502161f40d01810700c02d115004004010228a070800810b44038010f200940d9410201d5000581c51903a42c086001c040310b1040400da0002070380c007018011281724000c1c42c402c00c11010081e41004003510b40041c9160701c551b104004001801c0c09943c1a10021401a18050a0a10300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 969438210 1250 969436960 969436987
    0x4030c02040f02040305100c09050603191b1e050f070c030b070e0306100f03081c110d06090b1809030c010f1a0d03020601060809030d1a040617030301050105 69
    0x508000e90010305050114059485603001042224403450440380c102401c81c4412040301c409560308800211454010011442c0c140059504001c034540c0010030800c60080c92011106001c0c0d542032482a42990f00e1240c3e9000046940b468035450720a8604004032000106140b08940c41012607000c003103105070501c003210245e031020b1640500710040f80c4c209204050310000b02c071868035109100340c0b800101c0050900074030f04225080c02080c941d91604550b02c603546500b0a00c0c51401c40180d8030f180380c440700854080c1c20a811046002d00741c0d5840210424000d5600740d130000c191146c04e00c401c92101e9101c400052044002da14915100307510340e00041410b5203d0422150290740c2456014151140f103642300d62144404404045848040da9091103c104500c520150240e005400104806e078051440a43e0041030070007500d26050074401290122111010680005030408020061605140c0308840280403d00750260742109050b20a564900c414080c45042000c0802c0700070004c1e50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 969439460 1250 969438210 969438227
    0x8071815030b0612180f07030b071e08010510140711010e101e09121b08030a03231006030e03040e0109050601121a040e0c0901080706030b0f01090e0403 67
    0x9005103420355070400003806100d40c9074103983c110740070802c8005c2d0b41440c03400004c0492803074030500c2c064604946035850f40c01103200d008164034144211403507003916810641c02804030641998441384101c1d41850b00340031a000f95244108140100c0075654901854424156240340d6444224207440c2c0206000480703058084c418401c0c0c001c1103042000ca81150449408001c030a030141400030805070400c4100c44880b16031182801b0301c5042842d42000c0ba40b10f440064005200619410026580303101c46441e41d0700503544040001e41c1d030100031014040d603150150081d07003c2c00e40c10a00342806543d00c1c03100441c0384107503010305980b501c010000301d500b0300581e801031640e503500d01c141d50307940e00c0386130068007080303948900051412460042941d0248a0034030784400310055090144164428000104540c141c140e0040c49109841aa01d99500070700034043c21051003d81841c1d890715030040c1c16102950349582c03250f141c0820509059034401c03e00000c03100b03100071440050301c450905030345400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 969440710 1250 969439460 969439481
    0x507090b1b06010b0c250501030209030a0506090f1006051f0207090f020c010b04050c160816030f020f0c2b0611090a050603041e020112090f030807181503 68
    0x42c05000203039110024000d0002d501c468070035a0307a0700341d048505415000c1d074034401c105594014481480503520035405029040005411261030600c25103d00c0d2901d20f0071901e01005a01c04004680c2500c07040c4000c0d40c02040c55102030240c40d01348400241c0c084403465007882d4030494813120070034030b92081223084020400d050082009510142c480070181d4000c3d1a051010740c01e280340141d5504240c81400d2107001841d0007181803010507001502944440d0707034142e0b039166040c061003402c1171110800100300c6101ea00e8003c100c0a8400010703040c41c003000b010400a0300402c15a072038507220248850fa0700c40c01241c0b11618142c4465404088040060024000c1403034803c0000c18540c021004103000c0c07108039084000350307580c1d000f0400c1d54402105d00801c40032219000003848402144030303c85152050600d4181100099888030499880c81800d44801204001800a15801c55001074100002d460124545050704e07001c0180f0721280c3c450252040b0b805074520315105d110b50b00c10034149 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 969441960 1250 969440710 969440713
    0x50903041e1203090501031a01021b0102213408090103093c0f0f0519080d050601030c0f0c021903050105012303061f09020c0a0311010507090b1b 64
    0x142c1d05040003400c0c92054003c090119160800b8031404102084d881c0c0340390b104c140d00901405100410031900240001d10707044c19031007030301f03404002d034608a030b20401143c9108042e130f030300d401148400c10784001c4503201001908074050202020801c004021084e038a030042c0c016540c0b40303074940040780101200c4030003810294900320f6181611103e5071800d2211a03ca181d1341200c2c0000281304020304e03500280c010480380301c0307800c5c041c0019001c040554800f402601a28103220107410000c1c3d10145465085860500004461081c178420380308071a040030082c6820007504c44103290180ca50401000c0800c140555182c1d858115903c204482c00020106101c5001e00c5a9070326105020300020b011300f2540c0880d001810050180400c490150104010001c0c03036a61100030000b000300030741248480c089212000302281c0550140020310b0245002c400a00822919050050040801c0400200a41d041406001e035807a404106401030359140a5401d95416082d03860385007050f43c1c50308103401c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 969443210 1250 969441960 969441989
    0x14040504050a1406030f2109091608070305150d0c03050d110111070c030b0c070507030f020f150301060e300f030c12070206130b090f04050903041e 65
    0x1081543c000030603000324540c0300060340e2594001c2540320761604802c40466480000b8184c2c0582e4454246e081c01c907507445a051a1070b9800020035402ca00850307101090441e00003150207441d82c0f283c07910f903102c88a40784c01c20250505540780f41c4c1c0041ca80d40200d10600c000842d410601203400d000c0c500035584582215500c00300301c80007801d18107550b011895035510b80701400c0702c0200c61408494003250700a0081c428182550780d24110030f0809400c016140b8001d10031240007070703401c0141101442c02860000d10071500b91040100055100d072030716001e03150820b5207001e2482c0b80c4081e00d0554035581000d18102c01e40c01c020500043c405151400040c1512000d0b0390780001070003042d180846a00c0c00d440b40c0d5541d02151643e00d00c1201e16068040c1d01c003080308000750a17030350040d0101920080c10146080040a2010400c20145d0007a00d841000001c800000345440040414202d401b90f0303040c401454640e050310703240e006030302c20364030040c404081006410300000d4488010b051070f001c0320a41c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 969444460 1250 969443210 969443221
    0x22b030b03010f15150201060e0a0c110d031505040b0109031e0b0f010501021c02071e081f0b0a0b03270a06291f0228060b0a050904031404050405 64
    0x41c04000d0740f060306168205c0300d01c0480038602c18011030b0b0075154002c81c008010b0b10385911100045c505402c0f803404000202d21080150b03001400990b01b150000e50300400c0c4400361b214410f0010b04198041441a850070066001d140d80110750700040b65048207e0542400400d49280d61100d1307814130042c101d0a0b88030800c6141104d0100c0c043c180c5100b82d003181c802840b412544154805074074004005a4000582007261103140c00550003003002c81040c1010740d03503842801c1d80c0f03000c0349402e15246208224000841192040c450200000c90848402c9402c5107006107003090341c0320203410140709100d0010322100714803807401001c240550318130172148000d61a003443c8009045040c5502c12400c8010780c002c940800c143c5103030701c440c003001305500743c080780c0e030400900c104c80ca8102150079405224508005110f40c111041c16104c2c07034081c11505803040346801c0044034402c081c65441820021020701940e1141800c10f0380c0180d25041004642500e00800b0400d07024603403009070b106040404110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 969445710 1250 969444460 969444491
    0xb0a0f09120210080a020c011d010c03020306010507200d0b150901060906031119051c0b090a0b030a02040606021b060a0e010f05090a06201c1d1203070201022b030b03010f 75
    0x5c0045080c0080101c030394605022013707440300756059400140700303000316004524a203215404810110b4841100001008041852030400c1c0600f942c54480010800225215080c0c02000c580300031500e620043d8103250014066004a01a2104041c0d03160340140000c9442421128a400710180003408043d8400006010745d00c507081385480d540c1140401e205400c2035004a100c1e41400400320101036561101401c020b140c140d811076418451045070401588861040401800d002da01420000c00344195000c01000c140320700c1d80c0105002c0104000813940225080d07910b420920b05545400c00380b200485031401110f02280c0d120380d40b2203000031086e4112076640105446058107154200c40788214603150010030140840c1c0915a13102c8400c194410100b244000e40c8515010281c80b44c24030114008110aa04500840c1d1000654100755a0104041c0001c00c014040c07240c2c0e510460152850440024803614080c152905407400c4075940130740050a440d04018801c200c3e0444026101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 969446960 1250 969445710 969445751
    0x18120303010f080f0d11030d2a050f040512030c0708060f070c120305061c1505090f0d1209050d021b030706021509070b0a0f09120210080a020c01 64
    0xb491241c1c0d24400003c1c0040c070228015a040410780c001d040c821510640c01c1c1e400801e0400301800a0100304082003549450748180d1141c0c2018825110304010a00006071042c01c5240038201400014040d451502e0300d20320440301603c1042d92008000e400650845145001d0b00d42050b406000c4c51001088840f000600303544600810840314200303403103810080d51a810b01110140120b20101c00d03543c19140250040c98001a000d040d600c5842c40f02e1910381c0c840281c100048864042d1440c11110364141c60184a0b00b0600007401b400ca0902402c00d103030769424000395507105001c2900d00b03d01128440783e20403c040d071340201c1900c00d07642444000a441e0030480300200b801e44c143c0c0081c920fa5040008410303013600c100750010000102c0700c400c3d80000d064006c00038052489040008644034200402908400500313464542108240000c0507061016507081544403403040841500580e9580d4201a09001c9034242407945440d0071820202900c607100e0440c03030703940c00d02102000305095003000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 969448210 1250 969446960 969446969
    0x712021b0a0518060118030c0302031b1c020301090609050c090a0e0d1b0f0503030703060902090a061206030b160908070806190b031608010b0103050601141812030301 73
    0x80d80c180315190040100070781d41401029046000401114800c15a4a030519004001410b00d04030002c89441c1041c500501c03608100d410110304c0c0b40030011420b00f0042980209820a000b10810005a000c602000701c00e5800700c6d911b1664090040c1075407029486005001d811190521082c615030400c2542c0300e10b10b15125000320403440024540361b5581c45124050308030f9a004d04145414000121040c907100c010078423455401da82c140380000e910100c07410b54140b050001c0c540303e01d0b003103c001d001c42e10a50b01591101d40108002912a6074500d6600c050b00c07098105140303007819601c181d60050040e40c00c0100b01394583d1090291201009aa0000300e0b58903540c1c1d0003d050310391880036101c182d10b1140c0801d50303000d40b02080f00d803086250481099909401c0c00500c000e40da600283c50180700182c040d441d60082c0f0002d100d0380c40b082c003403148100002c3c00c090145041c42c00000305012040130746201d80510100c0c208180e44100440613242132002040d89904440c6d8400f8a03171294000c0c401c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 969449460 1250 969448210 969448243
    0x2090a140f040506030c0d0203191407090204051c1505040b0a0b0a050d14031c020a0e0d020f01051602150909010602070e07050a1215082e0908071202 66
    0x508030040c6003e0003440c0c4682ea000d00582020000300c4103000400050745003ca0345401105001189144c030248035081c071078010104c0241411150703021504160241d000592107500400c405d0021303489200349848103030341458200890440c00c1c14203500b10ba0b1200b182008003070170082800107100741c0b001518020001100200080990701d810002c070300080d8401c66801054800c07000d400704080302d400201e40c207180000d40786045010160500412003954070000c1a130b074041a00c01d1500d82c456214208148103650450503000103400040c503d403800105581009030018215522503422050f07071041507809042e18850f1906050b2158198208080d0107020310920800003030380350320020b034207000c0300c84103010581c0d0f42c3c40da42d1003100c940d03101da00080b0a0140710307604402c105a541c82440c0c08105a500d0328804070342404003403420030780980c16041c00c41142c0750b680c000c041d90314111110250004c0000007407122803072420aa4a0041c0031020b07000001300f404085a040e0040781c08241d1004094 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 969450710 1250 969449460 969449479
    0xc0306040e030a021f0b030c04020d140709030318080613021212041a07030c200a0b03191b0c0c08030304080c010b040614010809010e030f070c08030a020a080a0302090a14 75
    0x20517040444030344042055250b44403c61402090805c6d070700801a1542c40000811b0340d01c0602262200790300c00341d80e000e0000d00c0e8010101b0901da405a40c0f91000580e220101000c10301d0403a086907150320180c001d4103e2004189100110360ba000726400c02000703500309444146c0b40400c2080501d4000340300f400e00020115042c01404000f8204440c221603264642c4c1c403050300e0039100e071060a4000304e0304410107030104a83c12041d030f82e4519440001d102100d00256245000705030140c54108400784641d01c1030a00d034200300342200b210801c00c40c495051400b5a902070150402d014186c055038020403c501000040c0400c3c0b04580d80240780b5400341600a00c5014100c0c424001201c0080c42505000342e1482165015584203428241d00030350302c07000204445202c22511400d5500c1008220140d0f000083c00c0300410030400da03801e00030540c1601a42c04e080c00180040d4440c20402e00051100c14000b400a068500a03030640e0142100541035580190b201c0590540700700086100d01c8c4180c0d000c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 969451960 1250 969450710 969450763
    0x190f02120610090e041104060b0406030c1d012303091c020a0b070302071b0915061107030803100e16320309070e0c13050a06080c0306040e030a02 64
    0x100d4054140403101d035a0f9021162528a007070260b090b02402c100ca500040b40c44001803680d1303500074500604400d41c1159610741c5008809811039050325065414030003400342c2c0c401018030f4943c8001c0008002e0070252a50501c5107260390300c40405042c10200d0880c04800d00800d02000100000d0351015880052408102d01c401a03030355486515000748504181c034000ba90843c8a500074240302d078440c00c440045010403001c000107044460700480b440380e50f5405007043c01510f150b000c4004040300d0522a0485000124a0740c481000d4003014041c5d005c0000401c00203e4880754000080c44011032690003402c0036480b81617010400100000003803880350f05030081d070750069540c1807202107801c00c520480c0f1217032005859982008100c3c001078000e01800007000e04c1080c1d95144100d2801e0740c0130f0340c1c1c1c480c2c1c584000c040505640220b40141032019050010f0b68011402c1034005c914082c60f162203603108030002e0082d00010600c034180780030200307095020580000354242c0784266000f8110b08403044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 969453210 1250 969451960 969451969
    0x310060f18060c080f0c06150d0203061302010509180f2203030b011107030c081b0904031d0a0b12250809030d11130806130605190f021206 61
    0xe07014601e0103140380300c010400980a1002e455040307100f84075490800e0064a04503401c0e07009010918100d800450401c208150035a1028020000071074600803c0308003500407030366070b0070003e00084010035407403441c00039a1f014200740c17007031114005d2003440d2513069020150345c1d60350155174240064a00b040460f400c0585072480e050b007030702c151000f072582800c0d68900b20060001944e01c5414480b401070320340040c4c003017800b4030400745000e04040340419181c4401c01d0300d081110010244592407001412007103603182c0341140d400a41610f0800d24880c5004c04d07044803504601c04540d4095402040083c2409580000d032252010503014130110f07a840c0c1002800080103050b4514060151411f080c00301400382450503081007074201220704215030024101c08465121040f81c42044012445845126100608001410100014203114240b0340e003800141048054028029a1681c0c0000e83c03040c46011541260480100103020545017462034200941c01998003104003241040041c000e41007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 969454460 1250 969453210 969453227
    0xa0e0a0807180b10080c030a0f060906031a15060c0f1b01030c11120a02070e0a0b0a120201050702060c210a0e0d23030f0a080105041d0c011101020c01020310060f 71
    0x813540754410180d4941c0171407445a0f200800c0c203008180c2d030b4100b0030f13003080a1b4071460b40500507003000000d5442c11820400856500210405086504030313007006001080052081407881d015034250f500c40840c4d210b003a040540714a4403610b544640f0014841c1200c500503035055180080c0ca0402a0002c0000111420f48030240d8074501a844200030701010513142008002e51000341c0f060301c010507118007200c45148001c0d6010062261075030003861103403034802840002011444100c1c00c012038998000f0348580645000a485280d000c60540540e003400d002c2000d5800d150f420044000c45108140700c220707000740700d05100003919250700e44918280784403400e84007038200310380d124440b4019010804500c5440c90002c820302060100c0409003480c071014090000181d1034500107581442c00b480225a004100e0410014210311031402002c4081090541c8410070310b012440450716115030350191043c2e900b041415840002000400302d1202828801e0314517a0b80c031480d2b9010b40c1d070760842d403058 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 969455710 1250 969454460 969454489
    0x911040b0d03020a17070f0f03030e0d020c0114090d0309080118020d0b09011103090d0f090b070210030b06040306050f01150503010e07120c02010f0c02030c030a0e0a0807180b 77
    0x1e10903a10140461080342a146600c058001e05c1440e14520f56580d03980240d103e50115120380c0c00a640c40c0800d030b01030081c0d0401130152802804000f05500000f5136034005c4c1c7c4545814000511505410742c03030410111140c450000c6c188205182c2c503464010000340003441000615468940480c0c1a5030201d000e41140f9600100f0030a00781d503c9843d0755609540c054001e140b19941c40c0111106c00e00d048001c0c6100f560722001400800f42c890102900d49100d0910356810400440b009114003503411083e0398001d03406481803090301c4031000050b8000c00070b40c0d09081e40200e010170300004200311600031a20802e214050541140d81c0c0d0100c522039203010b110f6480c0031072010b00041c8440580c031803a07254402214034160100d031030b40c1201e603011102c0070030041005035100c0804600100460240b150814045d01c0218680340d11001456107074006d010001c420040c0e24030852200360b4865080d107000c1c10250040c0c40101d03a4038100c10b6081d130708126546500e6400c081e04e117030301c03854901000341181c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 969456960 1250 969455710 969455713
    0xf1e0e04150f06180509130606291b0f0a0314120402132003010302040e0c03070b0a11070914012403020702010309050a0302010506031009150e100911040b0d0302 71
    0x2181020700584106003058250303404c444402000140320754403102414000c4110702c5509440045c0307401c111080c0d6000e600041c0051003080d181e4040d5540c0c8540c1c915601609228080d2150140913092a521605c000c0860451290060076000c5000101d588406a807203910740707a03107081e440341d120030081c0200300c00407124040a50028001d82050692005030803102400000e02d0281c10200300d2014017012400311000402100500850a0030300c00c01c804c0402c4d010041c10050304200000b6511000380c0907280f000f07000460500204c9001c2c6506100490190068441441d101e00c4407000034545078482c5104c41d00081d000280641c0b1031115540044403c401c4103001d500d008e0b80c20b6010790722007207003241010303aa41c0c018004103034188410600a03100364008100c07828103400309882c1c9001c1c0c0d2800710b0300510306169080000d049c040c0c401d000321000d540c041144040d0407025400c1c40714140d00c409030541000b0a0000300180c0100c41e03400090110b030100451209a824449141503000b00200036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 969458210 1250 969456960 969456989
    0x73008090c0f1801061e030b0d0204020a09120503030406060b04080304050423040506100b0c060f0702190501140c180127060302180d020a03030f1e0e0415 68
    0x860a0030b550340034290501070180040c0300405141d4201c0350700260b000400280c44914030403010450110f86d21100041480d00f4400490075400040c1a10b440c1d030320080c844d41e400101c100003e801920a8402055403a035880c0649080d8101591658400c40d030449085150401c040f50450004050f80c0580e1f543c00004c5040500b01418800101142054610311803440c1d800f22144400b001c0c3e8040c4a244100701414040c2082c0f8100180c00074a50044541c150381446581054400010741c4d0364058008030f031400d81d0361a54402a4240010b0382003143c58050b103842c1020610005400c50410007a000c4003040a954039004a1038003405408506440854800008801903105903821840420000b101c1d90a0000c03e041d081031081e103036030011001c203070082034a19000319001910010b03080181c41d41201801e01da40003a41114040c0002028042600304c240c140720b1081c455034504c03030001070001141d0f1002c1d00c0050540c1c80d00d00e80a6201d40c1c00d041514a201e8005050130046800d603d403c00d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 969459460 1250 969458210 969458233
    0x60601082205031b2b020c0a061701050306152112030906070f120b0a2301081e1b07050d080108102a21090b0a02031e040807300809 58
    0x94111842174010218440d40c2c401f40346542d2a08480c0740204010b45602101200c024043c280b80d042c140e001500c260000820000485000030b00e600c4060300446104400180c00100549080c0c010b20381c1144a2059007040603030312001e00011400b44100c0803c94402e641e42c04821503000001c001390074000b4102500301c50880701150000c90307100900620305659940c0703d00c00d442d41034640814043c11809180204022544c10143c040e400419820f0001e000c212401c0e4402034a00300030f090031000b80c140800c524454201c3d030b0240c41c003483e032110903108a681c0391100140440700038056070105000361510765881c640b01e40310f10b00c00e130441100e0600843c02c50703030403079488541c410480c0c2c0103120080c2201040d041d4036074a503203074504c0c1116000030905001c0c1843d82503600010b290120843c8100140450403a0601c1c03411100380040c400e445c3c950303865117848245806465401810455005903c11036032017080b502508100448481c03610300120203130304844209082c2d03495819500300c542c0504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 969460710 1250 969459460 969459523
    0x17010e0a030e12060c0a090803090a0b0a1b08040e01080f060703051503060103050d020c0607030e09070c02030105040c050f010c0f02060d0624030617060601082205031b 74
    0xc0c0c025000a01555014103600740f11820100112085034800c2c000080c0f1005072600811a0400f800d0035030011401d127903015010804443c058010701a603084d0100e00c000b5000c1c40b80100c480000751500c000c0301403036005e20300f1020075002400341248401d0404008200d00b00700007190610001c0c4040140010f44405005500400000d0200b0b0080d0880d200503014684040103258001d5100d80000d24004210080c001d05010451811500c100300800011020070303480303c445012140100e801e544292a05e0405aa1080003644025095400d000802c0180b20503080000704a90050700c691810130300700d800446801e005510014041290f4ad4800e00140c20004003400c1c00c600200c02c001803168982140007a281d41d00c2100c90480d20244008035850755050003a14001e080760340c80310481810b2030444076140c2000074140f45c10448030074005140300e031401000c00c0701c00c101c603801e0f0b03407559219040940e100d074000c60b810a955050602a400300140c000b0319039080c2010401442d007031101a18600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 969461960 1250 969460710 969460727
    0x120a0519020c180105180403050a05092707030501051c0803130f0b090708033402040203010f0608150d03051803061905090106061b0311070f17010e0a03 67
    0x5030852181c00303144a11522a400c10144100c000d22540b41950316010070018400480fa1182d81b417403440750103000c0003d4020054ad00c0e81501810301a032034240b2080840d40345800e01e810000141ca07030240440500303448129107405a622a80c3c20f00c020717a281c1b4280031402d0343c05510541e2501c01032a014000c101444043c54000c4081c0a0980950503641c48034031404224600c1621f095541030140a103138807040001600400310300000e5824080180f4121018000d59400150040340c2c04078142c005400506480300c05590003003045440b96103a292a16540010740200004950743e8270115242800302400315640c204020002801d001441d901283c05070010003e11703d81049600c425032159074144a064483c05000180000d007034002041e41c02070300c0c800b03480391105901d0044244400b540c001000803a8118100128100c40064507044502a0584802504a0184603004602c210358500010111101c2043c410b01000e0030018040c01c985414dc440305250303110015a40000b400340482 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 969463210 1250 969461960 969462007
    0xb0a23030616030e0a1502250b07080c090a06030b0a091505100c060504081806031509190f0501090b0604060206070311040e270a02090109050417070c0503120a05 71
    0x81e590517075032903940c5440b1480c20806602e81d55801140120076036201241d22240341200105a407902d1005441d00c2100400c00341248003080038100c0080c061241000458500390b202030540c84401c0e640f80d00042c020300c0c400e0112480303180405400903804c211070044003c407038202c0705ccc0070803090300d08030030032528580d0244100140840e4984140100343c461103940d00c540d0244105d503580da428148002051103054242612420703051080c0842d444600d4038100e8210000e682d40c0d407050f2594113880003400c0c01582001e04041c209816403051240a4200b603040304c02c015814001d2034161820070002d8012030040c0c4005911520024805a110350480441d07401200480f916241d210040011002c5c0300306c1d1041c0d02103104074103e840790f611401884150800c07a4000d80320002544e400112049030620902c2e81c0c031919000810180300c82ca03036000499403104401d559582805280900443d0700c503114070303807080c022200207440504440e011a000841c00c0e50f039052900617009001349064104111 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 969464460 1250 969463210 969463213
    0x1031a060d0b0f0310020a030506040e10050a180303140604020717180a03061d010623030708071706070f0912030c080a030207060506060a0e060a030b0a23030616030e 73
    0x20100900c0d10300f071140b03805405d110030015036103065040340a81507031005083c02d400f46251403040318034981c004c0340c0c1c175500d07100740c2d04045000d441c0c100e199805003104894461144600e5030002c400c00da011790020b0712050481000000550311042040304a01603168040e002031449610341a20b01a0740000b029800000c0001c05c030724140180220708884c2c21500211411f9980c1d032440910b824403244880ea04044d00c01c000d000071030030720442070400015042001420030005d001000140d4003070040a02800c0c04e90111691a075458003405908800c1c0c105403221070007a18080343c40d5920965090703000b40010f1716240d030f0513440c03d010022103141c6440c0a400b0804500c00320381c0051080c000400b6200700780d91f0096200c0f5200d0070080c0031541c000e0a5188210700810031048420380209800d40e44410880c0c2c680d44804405500358041d00342c44424942c0080103810105007075000d4003140d85109002c207011127002d8651030506d65070f0f18003500d200075095000c44411620600c290401404c0010400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 969465710 1250 969464460 969464479
    0xf0408040e0c09041805030d021c0903030b01081f0b0c1006090e0d03140f1f0b180f0901090c110a0c0e090a0b0c030601030905030309060601031a060d0b 67
    0x1d9031a00005680118200c20700040001c0240b50038010241e0f82c00104c04004020380d0155070307141d40c9205611446030a03d4000c1108210300320728201c200002030200c001801116410703e40140149084a07203c0c0c0490b0742003001ca084200a03203884020034000003001071610b41400301e0044c03036800020440d05213105200c10a82d66407194001d120080c010400d01065130000c0e05001810300c504661010b0400d45046100c02c6624841c03400c00d07401003c445201c075440e03120810b0a80305144020401c0424030700c7c0000000d442d020b484020021139800301000c24181c42c24408100c20540440640c030703404141e4000521111503207a0018044001a0070304100140010070300c203082410b90182502c1100d403604007004100056aa46640103280001078100382c02e02e661414182000600442014280071001842e581d00a40c40440d145800c00c0440e501c0f481c00d036a0342d56880c541104c4d481d001a0070226101c0c0590310300e01100c0f00b45031005050343d042440741c09070f010080140d04140c591280004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 969466960 1250 969465710 969465719
    0x2041a060d06050916090e13050703110f041a1302040807030f0b1018090201020a020d0b04050d0e1305091606020706180f290d1515080f040804 63
    0xc100518003100750600106402d4540010000b00203001840d440b0b007540c8444031400b54592081c0c071501900d40350600c041e0103848042c00d010404000d80d10040140c414918044144a006140303524800800c640d15820619880140402d540a41404410b602100201546a4988101014601641580014201541e400d101d91402c1c183c0c0d403040d02c00f04443d20900b814000f040b081158008005400f070a40c030b52230728884d020981c036150241200b05990b0840c1008580c0309020034000c0580080c0b80d01a050880d04201449010586044595115501e0b158006a00482031513081020040001c42c4040415070008040d000042107074141d8044c80d030203040c085140c40c0c1000c01502c43c80c0d0080c00000c0c1480c502910105000c0526240d4031018a0200f0891902508a40903500b141ca80c0b00e403102c10000e107c10880043d11148561030501107030f0904010303c02d6102c08041241c10f00605000e075610003280e981405003203009400600640001915128980c0c8c195405c14426803040745090750b103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 969468210 1250 969466960 969466969
    0xf0a020910031d1f0b030601050f01180330030e0304090902040608030c0c0a09180210022b030f02040f03080304030507050a050109021008060d03080a02041a0901030513080702041a 79
    0x404c02c031010200070054020100c1e0b1098811029420b0040c0c008206c15410030b0009121300803c650410304001c0b000d0380358440c030b401c0d80e403410f001554804118003440c0441c02c40c00701818010307920a80b040c135500550f81d48041c420302404007a00e11103409141f510342000315983c05001c01103000d0343c11640311000040c01080410050034249003050207881c2000340c10041200d50402544240c0109040c503007003c1c14040d800541c80d8082e42d04a41004290300403410607818682c2b040d040c002201084c540c041c3e0390100040010180080c0c9030f80c1040240e011600ca04100c8c0106d01801b071300121740e2039003400022230032801181c019000303060490038500301c0d5071190303e000661001141c681e515a0225811803e003400c440000d6406401c20030000c0c5420404503400c0c50034454003070100329012010449003d1030f941180c0107001c480d15558400f80c00c4c21160380240d0301c000040c1b40064a003000040d80c0200e2019400f80e00f41d401208103280c80043c2e020000600407412070701303080030118250865039130798 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 969469460 1250 969468210 969468223
    0x70c20030f0a050d090503060106080105040506012a0203060109111902031e04091505060a232703030f0706051e0f0403090e0c0d05100f0e0f0a020910031d 68
    0x1c43c20040c070846602c910b000f403600784a41c0c802c50107a0320980050000030307002450f9034155041594002080e5840c600101e035441014104444149081c0c2603240031298115074052210b8000c2e030856003540d80c2d544042c400c5512013100c00b00340c07110034400d000e00e006808862502c00c00151045074100500d107203400d10784028282000c030701281c0c001401c00a0307022314002c10030302d5804d40410701540c1e898400820000d04c40d10038140100081c4c0d000312a0283e00600e603103500680d1582511303840f1248560305107032040300c1100950a028000c00302d102c2a2800100302c44028408000c841e082490958603440644000b030210301d8900d8001c15028070401903080c600e0300c605e004c3d0f1925030850526080c00f402e60201a041005001a080100301c462410602283d240c441800d400145c50307947d2803555815200e0580000b2150030001d5000200032605019603401641d00c043c01d40d0311349e240c0d1a402c0e402c80c810400b0340c0d03400c80c600e64411000c09002e50711001c100b0640c01007541040d150655510305110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 969470710 1250 969469460 969469463
    0x30f08070e0f06040f0e040c081207030305061305071d03070f06110f03030a0911090411130f0e0307020a08071208090112090c0819050307020913060c0207050108070c20030f0a 77
    0x346e60008220503c40d010003190010b10000c00507003015500d52a8204180c400c0b003001030706241c1c641c00410066240c1290350100c0ea007081030108444e0912407801041f07031100190030500e500144c070b0f10715128030700411510111160b220310301071014940502502c1d151540241c044040c01108030310740a0354820700046200d0080b1840014042c4158a403960001b54007160141c01500351008100002d800b156400921a00880f4040e0240000000200103486010b0345083c5890610949000d52680007000d050032a20868105103a9a203d16069a48a1180c41200c5401001a903407070b002c0788203280208aa1501803418035007868100c01400155900306c0700499203d9504142001182d8080c44503004e10200100301080400311501c80960f28010950080e2145900e8804500f19420b600e0301071000582c0814140011045e1300f81c080d45a0780075206082c0881c08400005685034801d4010014180d84110106004110050300d01408200c24101540510460b4402e002c1d01070104081600755 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 969471960 1250 969470710 969470729
    0x13080309091501020a0201050904060302043b1b04110a02060f0105190312020a14010207020f010c0b040b0910060b0d061403060c03040807080c0109030f08070e0f06040f 74
    0x84880d20140300701c0c0e41008205020a103000c40380080160303400300d00604501e0702440c001d5155600800003030700810041c2e00c000c2d400303481c0040003450107103510100c038681001d00340c10b503d0210b4000000d100311013060b0040451030f040281c0c0d100035280132120340404403a02400000b5540c89091698855038080310751800076034415010001200200310780e1502400d02680e034500c1c15005482a815035800d00d01008180011103c20303003c20360300c00c0121007001904520503040e039000c1180300c18000e520013081a4083c920b0340d0f626106035400341c500517440590161450080d80e0b40e0b51555510340e40081c1c400e07051405a03180c400020506400b03880c0242c00c150800c69504c0a20014540459207641c0c40038005009000c1210300d956404a400760340a8140ba5850740c1c1d0b070f0389a20348240039100f012401041d003170021aa89040c0b80b41580304003c01846038507000702100781c3d02000d1f60360701c2c41143c407940041c40402c1e40c0d401d141000034292030250000303844039090a80340c2000440720710003a00040c805 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 969473210 1250 969471960 969471967
    0x204180b03010c0318060e0f070b220f0320131a0d0503040b1312031214061c0f05100b090c0a0203040b070213050f0a06140f0d0305130803 61
    0x10301d000e01c103104928009003020040c40f031100f203290380c4c441c610707800180c001c0ba44c1c0c00c1c0d8540103481c1800500c0030343c40c10b401628001c1d600c0f201c0e80d604076009401120312036201d00e1401d04008803c1505002501c54480b9040d0109240d90369442440d00784168000520050b8910250241c86461003219940c00b1098003103001d0706040004400e1200c0014102e10403010030741c088000c10408012541902c5401c2001541c8445401c0708580302d4102c0c0d8090035460400392140301c1403560085200311071201c400014002c5184201482c0e490780401d40304d45030b02540745054600c00b21715001c0e6141155214404540f004242a1201401e0102c110903000805849210741141481e00201d4a030303100e554903500c60309009003504002e42c5d07405507004a1414880003c0e80c202595180d440800d0342550444080c0020f2600c144450309004042c0c1d0340e844c0701c41c10284082003012010b03203075500024018100300c0340710038003c0400000c14546c200540c103124041084103003030740307802d140130740034000e9034009568 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 969474460 1250 969473210 969473231
    0x9122203032321060d0503030403080114030f0d0509030106090e0f1e0d030b0d0609030f1b08030c030406092001080a09053d270302060103060e01020418 67
    0x1104446580381000d10038100843d10600790030900425a14440c0f10640100740d441070045440302945807070107052807201000304000c0544c0041c0d0fa0381601c4034914003502d4060f03408141039a5805001c0000420b0300b26400f03007400180700d40044c11190700300a00204040703648900745000c0301c0b01c1828501a41c6c00c482414410480100090800001c0c107282c203010104100056a0300c501c00103407688201510b50080316150783d2841c200f110102e0308000c0c10000078103e8a40a40504005024032010441c03090305800e0b01001144580c6145400003440c1d40386543c0c1c4030300d1048503800100129440382d540d00481e130100351090314002c981890720310000403910301c00300058941e04000f403006120a06003c0882c5c00140c0102d0000041d4411103000c0e5030000f0380c248801914014280e20403942d5041c5022107240c044550410740c0d60704080c0d400c401c4007041010304150000195040580940c2c8813400403c0001c1e8141d10411202e0404030005040c95142d400303c07072003820b2090281d40d01e19101c2040f1035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 969475710 1250 969474460 969474497
    0x7170103350c0109052e050411060309061f060f03050a180f060f090c09020a030e0d1d0d1a090c040c0903060b03061b0a0302070c030311060a02030912220303 69
    0x1890501100720f401008031450f111706c0c0f00321601008030080c5502d460200702040243d81340004000c80050040d0340b42c0c500003082c0c913503440044a982010341c81c003050144e401640d429180c42560f10b183d40d40c030000b00440d6000d5000d0a80038011446e034503542c41c0540d40018202c00501280c51203040001e0140481c1d080c26020f03650141e5075080200e1400c400030002960081011040760310040001da00c45840c2c101c260024a0014803207101c40c052200c2c1803e0490340200b80151032403066503001c840341101d6061110414003120f004085065191114135421000c40c02c40da4460403031000c07940801ca900b400326050703588400c00240070448150003030041140c640221015030300c060340101060701e4407160126210000c141422130075600000c3e0380075058407940480d641581c000e219024071580e03034a030003003503866a0400c49809000e88808035030a0030003030007103a00039a0003800625140940c0d1441c1d85417544200c050000c0d04400c901081d03480c80d03c0d4080600194025216100c5046140343c142 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 969476960 1250 969475710 969475723
    0xc020d030207080f0102162a080d0f0201020c1b0a030501020d0b13090201020a111503091506010519080604021b010b0114070c12020a0e040b07170103350c010905 71
    0x4540d900501070011010314802d040520a034106d074507807541c0544039861084c080c18040f900d01d2290002680420701010004c1d0f2b010026a45644420070040c40a00881c200e0048000300c0c0390580203800040546443c0d400140d084a00c01846445d0072540da070707581406ca03030210030403070146c5460354000c02c09850700c2c1c4490800c4400007002403001c5a01d641c0001c1d1036900d1100e006007200b84111060301035071900366104c6440c116410400e503480c105001c1244da00c003140d03050542c181802030005100d0394403074000e40f160ba20505800207850070001c0300c107498000340100300741d40081d428801c04880034000910b111000b0304090000031000f43c20800182500407501043c624400b0801c0568005003051894008989036425104010704031480055503c03941a40034450035622041480300f0b0202d19940c041c0100069102c3e102d03448c9030815104141a000d1202500c0ea05803444020720985114202100c43c040e420b44020058002420740309881d00b042d42c0d1100f031030790f42d8007840d0100314040003136 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 969478210 1250 969476960 969476983
    0x20a08100f05010e07120f06050a0315060b36060a030e0c0909030f090325090e060f0408090103090210090503070e010f15030b03030f1c0608030a0f0c020d03020708 72
    0x240303511440c184101411b50300c1914201c4d0034855403500750084142e15030303105801400009002c0d5100d0baa8034240710890000149001e5005850040b0005505c032a00044030039000503407203a07030507a4400320f051640c0010000004c407541c9192240741d9810350707030b458000c096080044c0c8000411140001c6901d1928406594850052501a060204083c000400d940c40780035612110b075035034090300010a0900c5040b0380c000400d083c2001c50403030414244a01007007910f1848004000c100703410602c460b5204c00c1130710202010104000400d01040042000308119a418100401c808040c1d0340401d8843c0d044039010740009500300024003040c503060110314014043d8071410015541043ea055442c0c8078644a18001150b0808040020a00a0700614050740009059a80310207200c0921070241e8000b2400c121840b160581690702d01445108038016100054011414621980010742d5040c0d0440c0e410401d20044e5280440165541d0801401c0688254090711f2503525111000d4a0319204a10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 969479460 1250 969478210 969478229
    0x1d0601020c01020303010909110909010b01112103070e09010605040602010e010b030d05130f1806080303100b0d020c1e06010806070c060c050d09030c17090f040207020a08100f0501 79
    0x20003020b80e80001903a042d2050603500043e41d517500d2174602e101318804108260004405002c1000e942c50650011203114401e80700c084000c40545562615080e0300744208030b40c5511186a2074907803003100080c60348a015070130100822030406002403c9000c00b40d02440c00a40f000409004c050f42c28042c0078090343c0395600a003d0103000c040040d40740c103188210901001004180140c84032440e82001c1d009000700c031100401507880e62074240001107202c50140f14a410500c3c0041c4031940001140c0c40f483c0d0f61604030780400d0424a4034204d650212100c5103581c1e030240400407c1c0c0c142130042d00d1070003900344450b402002d1032580880c20701005a00564a81d08030508010741e06400c908101815035001900044416071454250b5560040360421a146403400c0c5000c82003507040700d0380760240c03805110742c1c0082d5a804000e40b1818031824030000e801c03030513524180b00d0b40d060a40207407540701e10003008002c0c00c54454124a00d0f007406680c3c0f281c1400c0d02c40c0281510702409200ea80c0c007410070500c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 969480710 1250 969479460 969479473
    0xb06040f0213033806011709031605121305040b0402040f0b0a0504120503130e13020d0501090b040b041a040b040308130b0702010e06090a020d020d03181d060102 71
    0x20521001400b68400075194603840c0012652503255410240c104000f294102c100c002c490188502c0940002c4404501094510703000000011680f880d003032003a5031400055241c40c502440030100300c40d18071401c40d1030b80314142c0c12100c04466031007d0480f201240d6440d0142d903142c20108020b03140c0c1c841c031950242c2d10411003408040720720313000d0002f40c943d2410203541d0b80d003156030100d0300f520a40e4003800542c070124101004201c03001c00203110340b4019851400e505911415450a208001c0d56000c041140c4007200000505101c0200440781d8090000001c0780a19034841140400c400c0307038111459240002003000300404501500180c243c11054000103203850364036801e4850021f8000707810f00c580c0300002030944040c100030507955603102c0e0759100b4600303021002038042d007003110303a1a00e907005680005621010005444040036002005854807800d03580a0204002150b0302c154104007107c990802115401103100d001486640c003030413843c0000c55200d40c0340342e0380503000504540005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 969481960 1250 969480710 969480727
    0x1403032a09030715140a030209090709061b020406081b0102150403090302151c0515190504091505010f0501030b01020c0a0308030c160602070b0112030c11040204120b06040f02 77
    0x2d003100a581c2801c0345000c2d0600400c3c0e050300d00000010011017001d00018090000a602d60064541700000356482946601c410310265840916405160000741800900c80070083c42c60380b480c0041d50001c0c10010f4280d484100ca142001041e061004031001c521142c00e03070950b4100311013003030000203e00d513150390704050354000c004164510020380f0803500c1403102d4050040c20170490f8020140700108403d0300743c80290620140c0f204580505010b003003110210030900b0041d4001c65104600082c68908508080412008004480c030a5030103180c400c800c6151080e0b18800d46010b03000e103511720460145088001401c1c1c5241a8404d41190481c00d80241e29448400e40c070410f40e0360007100d0301c0e203030765440d900c5420034000ea000850301c50b03614910302c03c14041e4542c01001120300a40e91220315130f0300e5601300087d21410800c010000303803900705000c2c040b908420300004e00b1803000b0400752409585203609001045121000e440d021442d8007030118500d054130070b40001d07200d900c07801c1d07042c203940 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 969483210 1250 969481960 969481963
    0x803100e0709081c111005100807080a02091f0605070204060f06020c0d060209180f0106090302030a26191d01090b090402040b130905010803090d0204091403032a0903 73
    0x4003804507811100c2c20710b20100c20303000d0901c44202010410444801b103802054403006003006071000b1a22503498840481c0016004c2952001d03078040d01d00600140f0360075400c1c001030880080600e150380c07011481c201120000168003030300600e05a540d01c1d49074002c60041100315000b0f5400225492081c110400c803031600401d00580204048580ea18080e1103810f02c0000381c0700c0c480000f40c1c02540c85400c0c40103044061402406044628908032082e071706c500d02541c0c0c241c40390001a43c99400580d0540000e0300e80c10a2030b0280b003203006a60b441821f5820030300c9090308001c40b4a004811a048a942c0140e4410081d201c03d5101d404450f080317034010b50021302449194055000c1c502c6001407000c500e0b84440c0c04540040a85400195640d50500c2c07100c00780344007a010702800142458000541014004150345a140f40102903954090096003004020010020300320380304440c030040e0420b442428006140b10300c1035030103c0c0c254070510032920280911220642e4109805c240300c4410580c40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 969484460 1250 969483210 969483223
    0x80c060a02090f060c070314030c010e01060b03240307092a0e3312090102090906062104120e0306190c050d06091406220203130803100e070908 63
    0x30141c4d89980c4e105140c109180c1004496040902482160041d0392002d510010051221140c0c000c000c0100c042203080030f40c00e0700c1c12840b94200303c000500108900460403402044504404003480000480c03140c007090505803640d02001c0b185a960440e42d400703c0c03151021950103044142c001c0c0750341c000d10070080c00c042101c0c03501c14010424914548694100200d80890700261140310700342000040001040680c04004860b05010341c0f00c020503890a414000e039000c54100070301070512950b4a81c00e000306500105c0000d04c1c41c00b2204000411906142411030280380100b1700c8801c3c000340d00c030000d00b42d465185021400390340803008000c20f080c0f894107140349052000801003607003035010800712211300811030008011031425400144005c080c1d40140782401000b01d1010456507008100b001404500000504022039500c14610010050f401103510426441b086100451341c1d880740c500c0c90f0001c50300c95035480b404000a003c2140e80c40c0c56145c2c080301c203141c40001c1c28141200a80c980e031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 969485710 1250 969484460 969484489
    0x1b0b07030f0212360309040f0633050a080a33090c0e010f0e0303160f0b0c090a0311011709012922020f07080c060a0209 53
    0x10750300c00030345003003040c1c54044a108a224105207500c1303041200141030400b000c02c8069498040030ba12030b03851501c0d030743c2c3e405804500c0000a54108103d140520000d8414402011031a1f55964008510f6081100e00d00b04204000c1c03442284c5000121090a0580c800d141d001c01400000d01a0008560344034644640c0000d0303141022900c81c8111502c0c1c0c5861001c6909441140070740d2140924650380d8a0203c1b0032102da0704014030024480f41c6e0180d030710038014204240054a80c6000c504114054100d0740140040501140c1c81e0004200020070b0105200300201c50885c1803118010034003007062035441c0c001e800c40c4081850034071310307800042c64007030644002820b00425102d1449280e009101c001d01c02c5a41100d10101440d04070000390080c4601714455120b4200e2030002001b400c4075940650505c1405405415940441e5014502e5089410345917000e49808208d031030f0040e80054060003141c0c0c03040c4080e03511440341d000c01394203081000302081c103041e10500c604d8465548001030000500c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 969486960 1250 969485710 969485717
    0x70e01140d150e0303072309010f0e030d0e0a0509060a180204080331030b0c0c1207030908120c15040201020c18011a3109050a020301061b0b07 63
    0x1400d1850002d00b01080000914005843c00070306019245000c802940710b04583e0b56004480d801c01c40b0101142000b4914098000205020320341042d40202d42e220390400550511582000599000074035000003041440005010f11140a4107420482802006002c04030384c0b4240c24940980440e0051026210f82c2000000d80120b144042d1b41a034121000303000d004043c1ca07945e5a04440c602c03100c0008220404648100700d90000100036241c4900c2c0a41e40e21541c440701540740c0c10000700068200f9245983d107401500d40b8101c018281c4002020320b648640c58007260b261402070400d00b000d48450000c54504030412a85000d40310201d400705400c1c1420103018815182c03400100e1422148800841d00207180070351400460f90100040c0d412503402402040c2032524070188034840340a00440d10340c406940200d8004c000304100d140f0100c2c40c10844c0e4001030207503505240e105891081d00d40c0000180c1c0000141310720380c0e100c00700304d0f414040c2d001c024007400e80507503900e4580c0e0030040c00138042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 969488210 1250 969486960 969486979
    0x41a1c02011713140118030f0207080a0609050c01024b070312020a0804093305130c0806040f06080d17250503040807060c11070e0114 59
    0x45a024024403048a4490b260110140c075100445003a00f01d0080c2050351003071540300d10455513010500681200c078070084006001e42d4200d41d820390b0301070078120801055000c4c412002ca5211010450f0149480c0a0040800c20304101d091207818000b6241c055411500442101d2503a40da4844012481f0a044000300203140f03410415040c00c000364800c03d540c44070030124010301240f0001581020350340500d0074901d2102030940d040ea9240e0850380020030b1560300f440100102e50f016840b54008039103050811042c403411001e658040600550103000301400c6c03110500160a06d06001801c803c084d69080203403414404d07001d898100001e100d180314a440740d040d02000c06564000d440106401e80445106c20300d04c08014004110203640038a4100104c400181c149076942604a0044840e0070300b643c800d1208201140e240d84000d1003602d40002c100302007400940d4030b1003100b5550b444c070380d40e544105501400711424200c80340d101d00301740c0d0540c04c010701800c964420358035520001102c01454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 969489460 1250 969488210 969488213
    0x21b0c0a0e0f1807090204061d0103021303020f0d080f04090b1c12090513020d0b1c17090306010609051008160315030605010e010302011107150305041b0b09041a1c 72
    0x2902049405c5846010300100300000c016810212215103d0120b1000e0881c00100100440880c02211100c81128090003403c00141c10007a060070100100034000042c1400c1c0347c0c07222540e5138480582500404000075003008500324900c00c000c5090000c481c54080682404c104011400c414a00900480240c3c0200d118480c09030795440c001746405420b030701400b164400d04400a40100f100c14410a0034012000c0b05440c003118a5882c4071442441c00721034640a031109440080c803601d1071800b09004125600f80f5640800500b4020591961036002c4181800300b4414000c20b484032001c1480426400d10400c0401d042402c01c0c0e41c1001c0c500024444400509840741c0030741a400a03040920345000442c0a8800c0b0170440c0c142e9000b0b8031000699541850061380c0c8012501c140b2468044003803140c922544640c01041d00f045c01500500c5010414089080c041c40d00c581c8034020703c5030002200d82c03543c1018044e1588848202d41000500011000414010700c81032450500003284141300b80c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 969490710 1250 969489460 969489463
    0x191a010809160801062918150309010b2d0f0f060f0a03110a020304050f0607021f0e031519090b090a05011b120f021b0c0a0e0f18 57
    0x1401800ca0880341207070f0b0340702994003c10044c0101501c11407280340041820039602c1658448450903825540f4107401c3c0c00c9101c00c0f200b035010000f41d1200710089480450280d0501850152100c8000066a5020502004650212222a030301c207980c44030140400310040c10005d00c410001699003208103164500080c440d8980103461590040022075000c08174581030020f800f5448564900304800410181c1e80101c5008181c0e1210040c0e00c2003206001c2030810144035180403401070503450400d4180e40c000b0312034a4100c038002c1038034442c251000800b180c2c4040f032400740545c168084d001c03551420045400341d080082800303010a0010b038100708600483e902454500d82c012070080e095007000c1078410f450740340d03509041d00c01d50708110041015460b10b42285140d400292250410094000d019001031300350402c0070352215500f80401d814000010b40c445405400c1440941045107003e0200510f1421a0301b200301e8240340382081014400703d006d0250340152036120303000004400c052030705 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 969491960 1250 969490710 969490723
    0x1050d1a0705191e050702090415150b0706060b03222907080603010c080115092c0c03040206030f04050705100905030f0d08180a1208191a010809 64
    0xb083c4084440300d900c40407540b10f40c8500342e1114040d02890601c0b0034420031141c500905001940c010441e40210380002d1080c40307009c20068541501003111030500341c840380e140303107a030740864942e413800920101009007610a02d4003034040008900c1c1075040510400861613031205d1400000303410f00902c0801e22a000c2c01900001c80307100c85a0441024444840030540070594400380407034074020120b13102c0d28041c01804d480c0551031750742d80039684c600034200e0400c400307018050043c481c1ca01c0002c01c00310480d80c075410100c51107288a12208482081c0705240300c06c020003002403c0e406005110059481e00300712030304106408241c1465441d281041400c11240e03500141e4050b110f400140f419a8026542908441c4102c094a01713110301c0c0100942c132100c0019041e0f0000b0417140020b5040b440032084ac1d401081644220780c1c00d000306035611480030b4080310041000c00c2440c000c005801540a00785a5124501c0b88140648070b642d2001c02482690070001e14140480a400036203846001c0108 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 969493210 1250 969491960 969491977
    0xc06090f09160906020a03050706091b08011d120d0c050c06130201030b040209032d07091b14030f04061416020f0c060d02070c15120501050d1a0705 65
    0x81c400e1400d100302c8824240300011001c07400706407000e0000a5030341c004107500001c2034041e00ea0310b20700300b096940ca0005004a500c05c40d0606408101c0c01003200e0400c42c1c1c200504448000004c507850f070622540c02141043d84c03006401d03131240c10402496170b8000e09a802d59915500f01040840011030280c9840c0a10314010000c0d101d203008020781d11900c1800e80c00410b0003a00c0c200459080d0800f404280d120b84041140c250303000d285140607071707246148001e6110000c1380384003480b209070340303026820001d40d54001d400c03550315580e03040b12000407080d6041e868520340c1010400c4540e143c80320191030100522009000101c40f00041c20b000103074000c0000b681412510041d01c0c60107505d80d070a83c503001109000180701341040c420f400d0b01c0001d08001c1d01e60b0001d0080d0704003c2103980c094065402040c04580c000020a000103003000100a51080035506865100c0c24004585884007220016400988941c0b80c440707000002c10710880c1c01c00d65054504c0c041411a694042042d682071140855 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 969494460 1250 969493210 969493219
    0x6293012070f0213050408090d11030109030224070909021e2a010b0a05060c07120f1a15042307180504050705121302030d0521090c06090f 61
    0x7411030401203100302c040e01c00b500c00c95480d494002c00301194030880310100d0f00140440310800c0404220319005900c0101d003449031102d4240103900070701007400e54480200480250703106000d040a0b8000f1442090a801c00021030980b02d0314100000808081aa1103000035281d03001600ca2040000d400f103000d684144a20358680d2002201034000403844040b41102c04090110104a1182c4060140020305032008120545082c24141082000c0d03000c0c80b0f1802051041d85400034254502046441541d40105540c0042580728105200e011040090061030240d000d005c02a02c4031010381401260b070429030b00000d50b45480d000d6a60f0680c80c1c4541064102e10800402042e90790080c802407800f50244107034410203070390308140702c00e5501c140c0d8400c01148041c0300c035410702c0b41c020083d103038486044105c0c0700c4600015000310b428030400ea902a400900300041c0c6498409200c0d801c80c007120446603100500e4644609825240c6d68641101841503500040c0b0601aa541d007901d4011810000c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 969495710 1250 969494460 969494467
    0x140903011a0108070306050a050f040b090c03041209030209270601081b0306040f020418080406020c21060402280f08060708040b1b040306293012 64
    0x5002440300e140c0c0305600090b001d60000c0c0244c2d11034001c20049a00c0078180c9100541030008002c0c0c0891280302d01a009a550306001e8000e66800004d01e000300b041400319545c9040c40d04003002518207501602081c00150791701007006807118018a50b000f0380303011407140c1c1031281c03007101d03500d954028003842d040380701301030000c1000d040200b0a40400c440c0c100f4880001c054800515803104d80c00c54000d002500010b5000000d03007080e4009140c0080c01c82031a000d101c5943d9201310068101d50410070041e4004100e002c07142c1803540350540d5124840d07000351440c04100903500da0340e0800500c007d0086000b0341c0210b04000b1850300d200d80d03492030801520b140c80e440f142c00d070388025078501c00c5600c10703c64040070074145400303801014010303504625142c0240d901e40c2c14028040004610740c082090081100102040092003041c03600e41008240320b078010000038400a03681e2000903000e20410246184241c404482441800c1e0f0200c00da40a04202482466103400c1031449240048401c0000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 969496960 1250 969495710 969495731
    0x36020a080106082a0a0314040c14062b0b12150a0510060f02070e15040c030e1e010617031201060203310b040f060210090506010614090301 61
    0x2031a0141651495650700ea000d6442000d100c001106104030125221034040c644040c1d054400005c2200e140c2904000c1a40c1d0918049044015011070f0705170303200d208040050102c00d40c004040c01c0e00b1001241d0542c1040e041007040f40480d03491501032b0204141a0305281c0500405402c01c100d4a10014040c08045860304101611070134000706074101c002d181c01c0007400302c81030381c8200da02540200802002c1c19081007070a6422290140b045019449070784000149c0e24100c04030f052244118084141c004115402404283c2c0d0010101c54185130506100100580b0300041030310001101c1244c100c0450711040348a0f004003829000056040e4a00c603446014080001c000c05003203000325105e280300c2e03980308812038a130300a50198011115614040580c650f0b0441e10b0000403d00c482d41560000781c0d03c4403148816401513100000da0f5210420800519405019200e81c40ca0030f20824001800180e0b10700b034850405009200c20b2101e2085c0c0c52000302c1c1c500d0103a9100201c060020410008074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 969498210 1250 969496960 969496967
    0x30c08070314070602060c0c0709020d0b031b0303030a0f090b091606080103020303070b0c0d05091006060e0d1209090c1d101d06070602040b0903010c050436020a 71
    0x681c001501e4110081c1c400e00c241c030b00300285030002c4850650252a4680341c0414190481e4411a850a51031080b00e002140034200c51005100641420303800184040c6003009240c2800300304003001e5a00765035170200794800e890103c100d9038081001000000ca940250010000501c0240009800082c00c5020408261800907802c40c15409100141e01c800d03035650011100c1740d03030900000307400d60021301841000400203d00550810b0142006a0412016044010840300e08031450300079980034151038801a0401c4c494940901158641910003900280109214a400c0b000c0280740c0900040d0401105100c0d41d03c91024244201e000e00c80c0950450f0001c000051010202e4120300005080d0b00540c9401d07601d07919002480d0300c980038003199414041c003c028601440b1900500300700280c0c00010b00f10320003000a4818082802d0720782c0300360400c4c142114040300c082410321804000502403403a4013500c5401c1c11608a2040e644d0158070103056042880d0014401012400443c0c240c14444c5c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 969499460 1250 969498210 969498223
    0x160215070c05030c01050414030c120a1b030909060918020d06060509190605270417040303090905090a030504182d0506030613110307082b020304030803070503060a030c08 75
    0x103a91040e14003d00c8d80400d9103d2190750f0418030706a001d07980b242c0074101f0960103821182c0d07440c20b084001d1402d502e00c4201c20500c0100071000906044c03003d0010405500c5a40b000c2d04e40404104a040c802d0f40410055a00d03440e0301034803581050b000c44040190581001340601000f074502d07089801c0c2401200424142c0d4403c144007981008400310300d50074418080c0084108420030038a24002c0c104140070740d11400341042e07551041800700010ba12140000a000443c400c4c0c2d58001c0d250315011030b0400701c51015209485603004001c4d503002103603104040da0107644071134801800c03051114003410000c001d04981190b8003030607242c100301a041410700e446c44cc44047c1c035043c4990b6032a50109611004120341184038010981000b6001c50407603510100380075405402c1324032013600c0b111403618040b4000b003550440400c00b90034008441103150340304c400390003d00045040500b07680d22440603000080101e801c000d00840000c00e1592030b030390004020344e0017001059141e610781181325245c50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 969500710 1250 969499460 969499463
    0x7080a050c030607050306190302060414040f060303080612030d0920190b09041d2103040f03030c0c060c08070f05030103080f0c0a0602041409160215070c05030c010504 74
    0x189480318401c506000c648180b150341346640790b0b443c40c0d0f25002003015034044016000f080401c030820200061301d4000c010b101400b074003110703480d0460b8031b01c080000395008a0949840036041c03440070000a81c1012106030000f8044802c0400310101840c4585540103101c42a400c0d141082c1c02801030005107102c4440d107206401d00084484407600c207001c9040f226010700f8001c4422407100704000981040540400f401c000c0c400710320301c00301e042c0d8a411030508400d01c0f40710380c104401c1c400740d20035070301407041d010342141e44480c0c254a819118800842c10700d00c4040d003419114030010f600c0714880c00001d001c441e4410f604000c2c285864030b000f00b40d65000ca03141ca0200b442e05d00d40841442c01107041e41e048039404200c071841c08030a200404071980041c00b0422041c85a1003804001640900103000604075580500c1845600c00d01005030b1240003606180c0114140c510340006140e0100e04107038017101038a089215a110450700710f82c20305100e00041e00300e020200360000721000642016000b01e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 969501960 1250 969500710 969500713
    0x6010608011a0c070b0d06050d1a01060f1706011704120822020d054b060a240f050312090102031204020f090705070201020f0105070903170c07080a05 66
    0x2d030300d8410002c0c1c41002c03603008103580050810030080d4201c03002083e0361a0501e0700454603a595402242a050003000121001c0f000d40f918003003000ca150349401c0c0104650b01d0300640da004081b002406510004404604c54031a00c000103091340d015018a0a500c048084010238518283c10a02c840c441166583da0010b400fa4004c10940c1049030214583c1c00c800034600704600b00242c0c00c0041030045a03404a0b8503000c1e00e42e80910300310b03040810300c8811104030020021818601002003060007126030441c1114001d8007100648040003402c80ea00c640350b900c2c0080c0d4a2450548403204c107a0710030f09146061400500440c0a04003650084e003207031010303401c90f0300380955002e1341d11560083c018900e00503401072040c024a49400540c554109001030403000f241c0b001000030a803850801c46401c000b160000074904219603042050f0484040510000c20090901c104014100b040e984005041c1100d408100207c4500c05001c0345c0d9002000b0302111180d60f5a019500d88a55503041c00303071000d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 969503210 1250 969501960 969501989
    0x1c271412040b0705060f100e0901061e06090801180b09010605130b03120f0f0a09050d1a102601021606050403141e1b010e061005062503110601060801 66
    0xa608284103240030b15014200b00d20006d01f45020b51040c810000d09e1800c0307641d04c1d00e10028018542c444068807400e2803c10f003c0002e8180701002d0001002035001e42241c3e031404084d980c1d10510030518000c0c5550088041c03503540c4a81030100c0c090040303a0813241e07010400012102c03201c0c07107039400020b030000c0039004d6865001c0b40e448a20442d018819002c0ea00711000c0100315100e052450041039481e0303041c145100c000751104041008491310440460790710f018000b4007042d44d2001424580e200204c42030400000341005020000303031201e862110004805504002d928110a4064038034140205030366218a89081c100342c00684003d82d425400700300b04022940301401c02c0e130111038200900d008460554a114403901306154040021814030301c031101011441c1c041c0038068204441d24103401840242031840304c007091500160700c802c1c460755041100992607040d031080e4070603c181c0c0d00e24507600c035141070a00360f440501c0e005600b0b001e40a90000441c0f0243c11180c5a816030f4080040c4900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 969504460 1250 969503210 969503221
    0xf1e0309060f1508030c3301150905031c120f1e0606020604120c0309080609061005010207080606040b0d050d030c1d0108040b060103111c271412040b070506 69
    0x200d900c200d0102c1041074100d17070901802c0c03421507a20f0701d0100803047c80b078640c10104540b81003d20034083c1c04c81034018440d00c000c8030301c0b160701c20703c0900a05021400f4104280307458408030030108001d15040140111114071103000689c65000c030310b50304000c11050020056405000c00b10b004200a003201d1549031050204075148002081842154000084c0304446000c000030f48060b400890200d08100720040d02081c1d0103c1880f1503400f580300a8018201030a00c440c01d00f9920103150019411503100b441c040011030000140c00760090070503a400200712210202162506000b030601070023910608003541c0800c0e90561215500100a070fa50154140410b208030813041c0a031a48503001a402034041808203800c44191a04680705050000307040f00c1d00c0d448250581c0000c44d0100300006030b0f5012203032103401401060400000c0c0c4041c019403405030303101103040342100070000d80040898004040030320420440040010350102a25440701d80d10520514594045c1104176900c1c094100442d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 969505710 1250 969504460 969504463
    0x30c0608073c050d050705090a030b06040b0604060f02240106031e050709140904120518060f070618080315030c0d08040e01060f1e0309060f1508 64
    0x30302454066548020440c03a04018014010080b141410702c0302c103049020034828010020440c0010682d119251150041c0c4504030850300014110002d02c8010440e0040c0c941da040b0842003585d0344040c2066494441c400800c000302001c001d060381010340003402080c07060300f24010155005c2281e088481c03000704070414291b503020700e103005607a4482c01d41c01444030a00a400041b0b540317107006c0c80c506418050340203090a691090b910100494580744050203c2d403c0c40a0b0311203038140581c0d10300e4081c1801e65400c036148160300341850402c030000c1801a5640a1008070285000300181415243c2503e4021a00c5603841240220741591501c42c4e1051b1595090b15810043e03a00145134605541e43c8400800c0c554403608505076050041c036490500b60780e10354090403021030056500584445c245204424400010b0304000d0903c030b01191801401c540c8040c01854000c8010350540c56800041c40030344c0900401c59008103d24100310b52144140100c5d40806000606402610705840d51000241d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 969506960 1250 969505710 969505727
    0xd020703050312040807060501031209051504060c0804180b0a060e03072702040e010512030304110105070201054e010506160c170705150d050702070803070309030c06 73
    0x40850b0014001d80d4040110340c11420b0340075025407105850007400e652000102c46007608211070080840ca1020f5620f580100010081c01003500d581c440d22031310007002c58260049104517010009540000e10800065500b650f0007001c0036154110004480e030700b00e8014005445169000e001201400075915201d4a0b4200e10020050042d00b101400c020515a2031170048160b000010720010741840c5d089002d1008000405042203903070031070b5061078100410b03c020400d000e180d9510a00a01c008606000c586404119007401c005130303078848920051f40d0500070b588070407165003000c0700141e0a418000b55100302c200b00c0382d00195072654241c4051419001054240d403640c000e03981c018001800e007640100800c0017420181009010169111500b0710f8a41d000000c03032020003810350700015010002c60020b0241103c04004881c1d404507e480c490141c07085805041d80ca86001c00ca05900921002c1c000e0154141520350343c4403d030030050b12042c268401141c00306900c0c02e00107005485203506 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 969508210 1250 969506960 969506963
    0x90703170d051b0a0e0a05030a03030e0601090b1e1903110a0602070f09200c070f0504091e260406080a0e0715050f030a0e160510110a05030a050c0d020703 68
    0x715400c155081d50101e178080303403c01d425a0003841c042c101003013541c1d04010b4035428901c00d13600840c450480041281c02d10750f0680c4444130b010304210b039410190b607502d44054141307100041c8802d942a40a8001100389404070f500c40780c0c80c2401a408024049100c40182401d003054594161362a41d610089a44001c14881d0230720400100e00d0030701401d010b40d088008208426024024050b100052407003140d44210712a0700d1940c851801000710441003005d840050108690411054201c1d0b2244803060581c01e9842070340c062030060620801002d212100146070314807034a02d0442682800058041e80305000300004503948400168050601d0300030a114410000c0c050a442441d0040c03240b420742140c60b040c020701c8003d1000c00d01d51035a00003c0c1d4420610494041a01080d403805142892201440700c0341603083c0c035000f400241c82d0050782005446080c81d0210b240700b1040d460a04040c00b01c00c0c004c0c11030000150124085900c20003030706c3c44100080541e443c010115806903500c52481c0300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 969509460 1250 969508210 969508261
    0x501091a0f19110c0901050f030c040c030c020601151b0f0605070e0112020c0a0b0c1c0c110a051b0a0b040b1207080411010c03050c0a03020a1b050904060203090703170d05 75
    0x41c045420400b0113908d03c0840501280c40c5610342c280001c0c155181d0f103511100180e981e010701d00c2c40c25410043d40d80140300941d105008104945e030000d20b14280488a24200c0f00030540340e00800c05261245202d46410184c2000a418000700c0280038031038040e10b03240040e20501c00000c407081507108803131420310000014690115690f80e602940b1a000f060900c04010a1207442c48e100140000f02e458100f14500000d420181c3c0c000c080c01c7d1105040c0e1807082c1d64400001030000a000003000b851701ca100b00c01e0204d079500715000280245500703410100401d800802c0000d08281800d001c1c0107222400444401c481d903485108880c900012900035100510b44180b442e159405400c2003801c3c0e0b4024035080f45414680e021031854111040c508500581c42108400d09101d01d9000300000941204101642c103850640000c101c44070140001d402e03264000041004001c04210001c001c3d076000b0001904002c2c1001c4904050304000d10b80305455040c20001841c1001080c80c0c0425500006ca = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 969510710 1250 969509460 969509479
    0x1106061815040b090405010506030d080103080d111b0106031a06060f0a0306270c0e030d110336100507140c091614040501091a0f19110c 60
    0x410803000520078403070182c015030341c2d0300c20a80b40e44072144018890b40c010000030495081c4081810300c2c141c0301c22910302c10032000300010702c0000e0341d40045a030356590156011a0402c1c28041090182c82030b019042028280408200c00f4000c0c103401c25411640190310480101495414408000c282143c14a80c0001c0c01c002c403a001051041c0640714001080c42d0004001c0d4840c100740340c1e02d1b400d00d0040307020070030f0006807071085c6080f038014454142414680f071414120880080303a55855094100c0c800d020b2004110b040284c4100700340d0301e0003084070790342d807042c003c02d040381d000a41c0f90580c00c051107480c520041801c1c0e0900b0102e160300e80c003117640d0b024505145d540383c10440410178150303542603004030300f140c0b40541d8031803d1050048580080d0740103094907485010740030307072202c0c86405407641c0180000c10a580e0814210021640c24200d00320305a060901c0402c401c2c0315031400080c0f4003002142c10149540c1422880900d00502c0e2115180700005075002d59480c0c1f54504400e902c0190b02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 969511960 1250 969510710 969510721
    0xc070b07080406060807030b090f010c020d050714010c0c050709020c1b0f0a1806050108100b0c0708060903040306050618060f040608011103070305061f1b1211060618 73
    0x140301c200c0c0d0050103040001451602c5050190610481da030041e68658407140501803214400d210001d105c1c81c1c0d04008100b06a00c1c00e4019440f88101d04e4024103000e40480c1c0307403017440100300240c1c03c8a8045c0d00200081d59100074042c1112110079400d40352803044410109401600d4421546004007180041c001c42c1d498410500310405800201c82d0080720043d10003075a911200c0d85540a0101081d02241544805a4000440d9030b1548054100890034051140860080040324141d811001ea85543c88060400c41c601d004601c0e8070414580c41482c0c2000b4503c0404009401641d20a00007070080b07449403000c0042d0b00030f4030100100604400e070040399584c68a12540c26951a0181c80440c045603502d042501f1a150f560f5181440c804c000704000340071350700d031080311340c40304085454101d03000c101ca07504078040c1d6031004410140b203403a0400e060303009004810104220703400f40c1445580c0003120002040716810400c55a414803405c2c020078968540342d120010340c25080604040580c0e9031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 969513210 1250 969511960 969511967
    0x10c1103181302071a0403080a0204180c050c15040203160b09010c0309090914060702060f0f0a061701020a02160503121e04030f1101180e040c080d020f060c070b07 72
    0x3207a20380b01499401c01009000503580c40c8102d000c0c03040c1c00c00c82031161030076060140c4004001000100b007140f04102c01c1c0030f40a000072980c541d0340c21944d80007404401c0800280ca1038070542c000003806104201e030324032080702e802d1212807280384242e050b100c3d42c1e0b08800bc1d0b00e0b1610800d00500c045501e05000e0074030316510482c0c1e2452614068982251170540c0c50005808440301c54a003981c4a881c140800001100100200c1c0d0304240d0603c000c0040d840c00040c450b68810015000b6045000c03840c0c0803448084054005c0d85c0549103040446d001c01a040312618000e61000d0f4683c000360081c0700c10902e203100705003440310803103001030090a0760740d010016001d40d079400004100c3c0c0c81da441c2002d4090542d4070b9005071015502c42c8140383c96207a500c1c2081c1c80c51440d1001e182d410444140101c104100c1880c45000854242c03450030703940ca481c0e61918200c0103030580c002000b1031041640d01824070f5800600c810000403035400b645c1c07540d00c404031182110700c134925015010b18200da0104541912 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 969514460 1250 969513210 969513229
    0x10c0201051612021e0c10180902030f07031404080306010f1806051b1f0507030b0910060e0f03030f0a09090c080103030311032403030d0e010c110318 66
    0x41070320300034498000c5a07141c10411030042414001a8008402c00130b0b000d4903041e241781405905001841c5e0588030b0360000fa032020095100d5420840009158040801c114402d0005440000e20075034036840c1042004040903000c452110000741880e17500101030456460f0315001d15001a1800d10795a1034a005684482107003030300c1c0d030811100e005102806403442d084040a441196503040e0b4802c03540c1c0400d520002001d10003074440e00040d9030f01140011540c10318504105030324000c10161707500107059000b4103007407002c0383c0c110102030f0410145520300d121510943c2c0382615902100c000c0c02d4144404003a050702c0164041c0e0042042d5160303402c81c20702030316584034180f610b914010344908007001a514104030400204100e41d0040c420950107010b00c1c00305d03c100b0307040d5a0640c50510248003108032410034540008503005240381c0e098905004a070101060590700380b11444000300e419000b13001e01459800014a1030503a11940b040c003004031001000040d0150030504501c5040118400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 969515710 1250 969514460 969514477
    0x309150c020616061d150709120201050d050a050105120a030215091f140a0e0c0906012c3f160803090a0515070305090a0806090327010c020105 63
    0x2000d455600014604c0d0180313000b100c242040c0d210101c0900400c1514107421103034031b026015408410851941c2c2d100000e403040324102003420703038403044600040c1c60030700ca900740d00c520090500080086501d5642c0045d4121002074400782060700c003803641551140420400180107030400a00d00403240c1d07800206d540c101c2d00391019510500750389603407004803a5107411300c0078105840d980c101c050001403c101d5513205035441c905010384d103403281005071030790828400d05205401d0480030808070392023400000c1105140c1c60078030749840035511544603051090507100703204001c5403032034601d1041034b10030210b0300080380c1401c2220381e8030f84015603000b8400d2048190462040809151042264407200e000911400c4040d503070351a81034051164440068100d14010303106404d004111300d2080003200c04880c1c00d464819110f1b02c2900c0000c0c3c950043d0740c003418140c0f0030034044c01140f21010004011104841420842306070a04154030710403110391503d240031941103c113034005075000d40020301c10305 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 969516960 1250 969515710 969515737
    0xe030313140f0a0e07030e07030b0c0c01110a020102040504060b0a05030636060414010807150c0f1406150a0509130204050f15010914040c02101103040309150c0206 72
    0x4680004038584551507130150035040020014804196058484d11000d20700c0f20b4003502603582141c031640f91500c4042d104a11a000003c0c80c112841000e5100140c8070140c0400565a50781c2000d009020350064010184510b01d4007200045005c030081c2210468051601c82d41d0071940e41000308035020141c58401c441143c01064403109501c0d640c2c07402c4440490380ea44c3c0d0f0070141046000c0c03100310340c117150307182c1300380b80c02c0d60014401541e0004800046640e10f02c1003802078075112008036800444040014035007103e001c000c404000d0350020380f1100740c03034420407107640790341d205141040008015800c41d0041c10404060000d42030862115902042484c04581c2c0340d20194007040c01c441040f20084c00341c1030311009104071b804c0c8007207100041280c2481d040b40100c0c10030030200408041d98603440c0c4141c4d070f030fa08190030050090000c40005111304208000303100300308040d0700305035200301c80c11000540000d034041501004030a951000040381e070307a0310170b0b5074030304d5420701c409913108800f81c00350b4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 969518210 1250 969516960 969516979
    0x90a09020a180204030b010b120406020a02070e010e04120912020103150302120105040215090303030f06011b150b04180b06061b0f0607111b1f0509010e03031314 71
    0x14030400e2540481890300b14800590b51441c0d03007000072243d078041c0c20400300c82204000c448003541c07a00c0030513900190812801a941c85800c1410303031500760594450804040703078000003d0760307501c0c0352100c0e40320782d0044004a036642d0380110219540100d90040034801c005400182e80903500c01c0e8060308440c0c10803100c0e405c40c6d41d22074001803409041d0801101240e03464004100440c10020b4640d85030070b07890b243c0f45e818000a02d0009032240030050031958aa0344c4c00e00000c9050307118111034884071b417000ca01d81c19030072414105405c0b00c0314070181d5103004c0c41c1070042d0186182030900c070340300c1d58020095124003000380d00d0b924200c4580300509040d40c000780c14031071100c240640c2802d20b041d07400408004c2c24141507000703c86044c43c0e0000c0103002881010740c00b20750940c9003c201a10301c080443c1e00d60492140d000d00140d05c8100503032492148910381c2400c84100c9402000801061500743c03210008240c100040650301d00c40c00003001034403009007204000010300c0000d4200d070741030010b112800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 969519460 1250 969518210 969518219
    0x11030d06081b04061a0d06030209090f060c1c0c02010b190e0f01050f0d0f0c0306050628150e0306070e1905011e031803080108010c0905090a09020a 65
    0x3950025004181590007a40181e0300080b00781c41028200340c0e0545080c801c492034907803520084048906240c1000b0b50010f403000303000f100d540c01280035550091001c08181040541642c1c1e40610035080320580c816080072070088145801134a40302d4503c0951085540704580b600000381000e03030341c48803c3d5900c9000b6441d06a0764024010b4064003d4200340d040f007451328002c0e400b01c20001d41150048845500144520384603048030014507842521341502010303541c40c0c2403580c040241400b900a0642706004001c210550704058040c0c0c2d0b0413a001e0300c3c4002e8421130130000301c60003c40c40c1122030800004000c010458030755240c4600240c1007040310046001b01017404c0000884400001072912000300855281401d10100032690101c20031100a0803d000600304501541041d28094a200c80548859109800c2030700f1000c00c0c181d038400c2d0301c280c501d80076144403c00e000d0400194286910424010302c10024003045600c0104402c03c0d584449421200030710b4090380503038001811200114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 969520710 1250 969519460 969519487
    0x1e060402040f0b09010608190e03040e0408130803031e150f030c03030301031104050c0f0f0f07021206090607050a170907030c12032607030f0f06031a130b071103 71
    0x10f00800441c1c07505003041c132304044007120b042400441c0c50380301c030328005941280c1c010000940c1d051301d074a02d0f26610140c4440c00d000e1218086c5190300700c200c2d0300744500801c5501c1c01201450041150003860000098a05001d00601008a41d036085403d0202042c04180c503056020240c2000054141e40c0216a00000320341160300036002500da1040400c8910450300f418030072aa400701e6045803250402928080e408214454040600b841042c04607101e208007c402045590080e4000c1203080300703501101d0101c0d107491046a00c26498080c02c0000750409004004540c1801115516440301c0b200400030001c107618054070300e10700d0340304803500400050002c100d4200a4908440d5898101d100f41c82c0c010025820300602c0e4000241000c4228401e9000e00c3e030f45900f1118604001ca84001c000b903816008266941d1524055800e254000003400341e4800c049040005074810021035944c2d4814000e10060701c048010112080707031000400403031150000031420280c940c2606c0c0303003020044002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 969521960 1250 969520710 969520729
    0x1120504170c061005010f0c1104062102090a020408030a0c0807050114010f06050a0e0f1201020a0509010815150304060906050c0c0f01060b040b0a02070f06111e060402040f0b 77
    0xb4120b5501040c00e12400d1860003249000500302460040012118080008d03d0032910902c000d159181902e410000346ea01d03134110b0009003031590740891441e411100f1981014440318401d0740104185404508420740c140212000c0d034520b10010b41c41c040003114100e03a06100c0c1101680c0c4d00b5004d014901c00200d00b8042c0e40c5800300000c42c080455414920070030000c50b20313039010310b0910000b00101e4a0441d04108900b440345800c84045003060282c601007180100145110107242d440094500900d94000018118449003070707941102c1c9945d0a014981c5501c002080d0039407100e8004c2f03040c0c00d0000303440003c540c003031b100d600c020404400d0365071580c054400560300044440c00200b9644c610308010000c080036540d8500080c0141450000a01321a10031400390464400d00001c00d0307031046000304828002401858095004d807582c40c00001c000284880c01e24050b03000b007160380c220010810341198045031101000c2c1800c0d466a80c20840200801246098100d032204010719041c1d480d030080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 969523210 1250 969521960 969521977
    0x2108030f061201181106070516060e0f030c0420030901020706180b04080a1701081c0903050d1209061803020c0d08071b0b07030909060605030103020112050417 70
    0x1160341084070800c075aa072540c1c0e00d0565268034001d50407500c18448020f583c0040c0c1c0040314072041c140104045000c0340b00d1100054068031655a51030303103400003000d5480803282c07150381d024103601e41c1d00704020000d68107016144d4140e00503144181c03070f0325265110b0304036081d40c808005040f40c9280c0900072660011100d00e21141d5010508000303105a600032403890715041504c100c004200b5540b048000c0101800103480c05a001c940c5044881c041c0201d08003101035168880c12544e5945103255403580c4450340b2503000f003042407031102c206008100c040103591f80a40500300e41c1d09442412a049403c44902c0060b5549408074a070100d41180300c2c182445c10038415030390214801d401c011b460700c640d0200c1103014001a034003e40119800340f095030070090344581070122551f03a00300c540484030001d421241300303079000148440415400020304021650520700034003080b5035034101520240000d02c40030740884c6154060070707003003034045c0c0c010390f0700c50301c25a1070305803180050f410002103401c0341a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 969524460 1250 969523210 969523231
    0x100603020109121e02040f060f1a07170f16060203040c05030715050d0902031903080108010510171614090121030804140607050301170115210803 64
    0xa00a65a01c600010301800303910720072030030b4100d041c0d9a48880903007402011800e102c4840c40002107640e6074011101c040c55015050100c15142e80380c9a49904180c45031003110b070203c01150710010585010344420607040550b419480c0e258000c01201680107205e1400300001c10480c41e03800c02400e051081d402d0b8011100161685001d20f4a06105410303600030500c20f502030042000305c07410326280c0b4450300c0e660380340160303d5039401c101610281483c179070025890300031076801c20010003220700b4125004c2d000c2da80b10031950b641c850010b0b00f242c1c8242c4900100e41c1e0304042c14049084001c20050380900710b0000c4440443c040c940c41c1c0c103c0c4681e900101113102c0491f40e43c45407403408010f05409042e450540e650b413515001840100364020703d10050034070000d1000503080c0461a0b00799051030b8038840c04d1301c04074270b0440350081c2654001d00642c2e081c02050390008108480502c14060031800e4402083d07051410310340004800d000500790240b07920710003c0b84500140000d000365014035008107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 969525710 1250 969524460 969524471
    0x50904030906020d090b030a0c030f02040b03040215030601020606090423032a06060f0d050303070314162304050301090f020306010806150f0109120c060806010e0d0b1810 75
    0x32000b42028000406031041111050050042841d03c008682e0068223040e80007805a090880a602400074000082e1059201250000e101c030f003100010340c07080e071003200c000c1c3d03201d003643c0d080c0e136103501007520b00d42c1c01680804002611800c096441d5a08540903451144129201c451241598400c000b6801c00d95000800d50000d406411405480801039803982a41c0310b50200407881ea850000030b04072171050320441c1c209402c0e92140c0c903181d00c41035089402d40c0d85d6840c0841014015241e031550400b0341d4074481c40060002c800d4862640d0b03091150ba51280b600a101c00f10604081c0c4002251030610a01040001419038091190344000c51040062855028641c010581403460582c4040284d400c150104554805405601850020308490304641270a0440040b1064a0190044404d03810170041500c10310400001c0c1d8802c450f426590580c2d00d546030760046070110218020550400c1c00d03940b2110018020429113030b03210614500f800d080c8103440100a281c440c0f00b0700c10106840d6a01d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 969526960 1250 969525710 969525719
    0x31103090d200d030e1905150606090d0323040602030703140d330501050f1c1415040b030c0d020f031507090f032a03061d100515190509040309 63
    0x1404981821300001b98003000458140d2034060b2034444048a46014454540000750269036650036180342d00ba015040c0300e5914801c0c50060900300c03224001840c250324280300501b814009408440c00d590543d80514103100c0359a509942e03044d120010640450018040c10615654910840920407840d50a034140c009607c4406850075034007141ca00622a503400003802242d802604481c1000700303800b120341d0b580004642020840c2030f50f0000440003401c1c001e100c1c00720440c1c840028000d2407030038104800305c01c107a0100402c40d07031080791003509900180c80031006803400020f4005240c0c0041c14802c082410080000e013040581101d4550410400003070041d00355202808102622140502c0c060543c2961608003030344081032801c0b00c88030140c21851040e6030006055000444e0311120512298038000384102c8070310403601c1c40081078440c5550ba00da80031700c140606800740001842240c81d90312400c00b030111840c05851b00204a45034030030001903075116181d40c175110f903020b940c03400c482c40d080c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 969528210 1250 969526960 969526963
    0xf0406030f02090102060106050304080c0d0305040302012306040b030c090c0a0207060f170c16030e01031103100504090206190309110603060907030c090b1207031103090d200d030e 79
    0x400320805040d2043c4400d007002c0c2d800190341410345186041040e1a590740d480c1a8406126080b00e601072030007900884445241c1541100e402a44030743c009005100301810300e010084000c40801220307198810118215084c680d02c1030071135000150a072158040d404001c00d045d2801915003500320783c7d001407070007207180d81807280c1d0000d401e90785400784612500030401080101448611505040d4220203d4104c20050084500444d8090103504c5208150f040c06002c0c21030040340c1c2d9000c241406960b2034180c80c110120b074450201850304809050902040c400100b0301e0580480c0c201008022002e08103071203601c000000c0c1507030f6a020809862900d2b0250f40040d00c445120300480c41401030007850b90328101c079680c1c048a0f5240000e1440c030351001c11104100554000c0a600c400003481801d08040c0e0300003c1c0c480c03d15503d05021340d00d1b0380c0e000c81085200c04c0321604000d80000050a504910070b2403403101c0c245054040540160300c04036810308107000d824100010940e60184d03414080310 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 969529460 1250 969528210 969528221
    0x120609130c08030d06050604060804020f04020405030109030807021c081602070e180d050703020a140c060c03070c080303060a060e03070e0a050403030e06060d26070503130b0f0d091401020f040603 86
    0x10950b000750402d483c00000ad4841d11001e04002c2c82400407620000300d64540ba410b036801404020004e019240103410060500d6030b00b9030744a00107000d01a40501550300c04428640d001300c00740d6070180b8955890340d2070300551403030810240031401800c4000640128101d0228020b6413445030300b0301e001142680ca5890405031291000500c4020702144010a8021881224068002c000001e403030404034002c41c180030b50304251031303840f002c003280c040007001700000034200785442100c0c41c49100d510340089035920300003200e2407540719820b01c00c00d21085100344121448038070050100c030401501d80c1d0205031200d4084039544041603881c1d080100b4154140501c140388881c00c2c018102c02d0601402051014500302405401200038a024051134404d40f013048101600e1020080d448032518034040b5242e030300c8203581d011b900c01c42c80d5010560311f540e4170480700341c2200b0001092034040c0c14511400603203c4510107407040010742a420992210030300040c80741e07405e002c0000d03640303034107281000d4120790 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 969530710 1250 969529460 969529469
    0x8030a2429030609190e01020705060f09030702063601020d0c0b01151209060203040b070f08040b130203010c020102191103090108130501090309150302120609130c08030d06 76
    0x1140d100605015040704084070303003101c1c2c00e941c01a16942d6072040d940300b0b00074248010490314034080c010440520194040c08140f48610300381c99a81e1601d80c042c00e114002507a4024203030300200420001864004001e00444c0e036130005502c00000c425003404140d96031029121807055110540c0c410300d45c2c2c1484249080e80d080d08146845c26401d46845280000501a004000b807149001400361801400070384a51100c000b014005c0492500c0d26501a40054400300d1701000c021000c00c1d82c2070f010304800007071822155108007080e55183c5505150080c058134580d1002074070480100545c8083c003550082494035000507036259501c42c0c0603c103a100c041c0a01c4104400c507403440c0928480841200d40404091900c21025240e05c001e1009281c80190300802541c038003182c4c3c90801d90441401e03022034003524801e0260700c007080b1080c3d06034818500c40f01e0388400b045000907801c0c0703014148680c00070707400030001c02607030040e070740d00101011190400c44840e4008900c03002c541059008480192 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 969531960 1250 969530710 969530759
    0x11707080f0d260105040c090302130213080f060406150806090f12360a0e01140f010509040e1c170106050403020d03231603032708030a24 61
    0x42200001c00d00942a041c015544a20b8440e08420b47e00381c40b860132130000d0b41d002804614a4405140044029030040b07071164120411902c000a29030350200304020742010100c054a45592640c2e40c0200034007c4811802507201d4141012603210801c01046202d510720382e004061682241c0e0400d440c021000c030500f2045007003044410350601a03200d0031000484e0210400307009803004040d2111841e00b582415401001c050b030001420400f840c1e4480c100c41c0707052483d050003081d0000b071000c80440c2d107840c60b01043d0700700200721603810154404a552140340082d80e140c581640d162845080c0180c2c89c8600192940070400301519911a0490040140d4201145803501e503a01240c001d044078a409802c0c0503001000340c55814501c3d42141129018100c0030340c2c0d9a40b400e94405c005060b845040e000a403800c1843c03801d03044482ca0340c50750750034940b9447e444030443c0d65980c05143e1004040018060300d07a50010012220380025102000d071035000a00035034205030042c00c3d102802c40b00035601 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 969533210 1250 969531960 969532007
    0x309060a06140111010f0c0f090806010f0b070f150b0a0b03010f0b0d0f020a120506040902090c090105090307030606150201050408190c021f12020c06011707080f0d 72
    0x10000c20851903000e030300213003482015101d9410655004000e1aa507a04140c0e042002c1910351551028010210300c400761074072560a5241c80200342d40707074424020004501e012801c280094100d042c041c10000b4800c5e861407003c8092984e4a034805061240e002c4610358036035603034400c10319250300032901a103090040c1d1411585002c1980b00341c10803d2040c50394000e000103a113108405c0680100920001030a07096569080698004100e0844040710340541403400c0d001c62040e1429000e840051500104101c4258803091040400b60780b014441a0600204000f071040070b0700c050003050000c2d030042c1000144949008814171410b9500581c0b402103903d440c080100040f03d400c203650880414141d26a443d0108600980748821500310295008004160b4070f9022382c00f080000480c801903503034001c4001c41c0010018242c0c000c2440e00c401c00d42104e00184503e8900c00300d12002e84582008903031030709540b56003e60074a58001242c42c000c5d000711409024480d088281e005c05a907045002d00030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 969534460 1250 969533210 969533219
    0x91203060d2604080706030b040504050a020402030c040e090d0f020a050316330c0201060803040b090a1d0105010807080105031b061e03090c1203180301110f0309060a06 74
    0x100403906100040c11040d07002140c0301c44a42d4034000090904903080c5003a40c5580364900180e86405c41d101e03403070019051080c0c540d00350a00d4003889010340c2e0f208006241049440d4208006500028014034009100348000034030100141050790007001c01c00b000c2c058984041100405e0b030b001031500141594844c034240c0c400643c00100b00d541d52034040301d01c01c480c00114a004d02010300200c0d41c409040d02c514414007140945003223490004002100100130755820040d0070b07426034070b1520030a01a90410706c130030804007522a005000e03070080107101140f030544a0080e00b030344080ca404400301da40c1e200c1c8d0051100d542c10600c0340381c100e030b1241403005096241c10000b075a06d1451300000704481594422600c1c054031001c0c01c0d5540c40c000e03d04102d400e12410740018485400848a07071400c0c0c810441c001940d0305003d018213024101e400040c515001d01c01580f070904d000c0003a983e58040d0f607600c035501c0701c410501020f00403e40411100c603560741040800c2500c1c114014101852061074000c0822 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 969535710 1250 969534460 969534469
    0x160816050a0905060a0509070203130512030d200a181e0303051e300f06010c080f03102405090f0414010303020c03063601091a09120306 60
    0x101220300803200850f0703035034138503020070540302c42c03680110741061800d424062400d4010010b48004074040340491842c603901c008001041189200f20b803141d810403c96542964034035003200003880c24041c603c0001440d600382d4045294058140701000880600180601c0d04048240700c0c000e03d1188140b4843c03442051240501c040ca40c40001c2c1480b00005003030f6803116400005900f142602c1c0d81c00e40d00ca03506c80c01e10710240c54900b041c81d000c485583c1d01d44201c00c0d400840d42c5000f4140d00c1303500b410785c2d503401005580e41c1c0d0f003001080d146658180300302c000c42040b080c003c40c41000791000c1c83c04110318003200900d031a40e40501b03205d1036003403001d144a8159841b0041e600c00000484400c41d482140350082002001000425018800808004420f164002402009805098049400581e0389581f4440c0d00c0c10611310040480c8821003482120f216400c1042a003251000c000048c40c2e41950380b21410801d42c5403080b900c90040c4810040c1e030540510001c9100c2c030b14540c40382d1a600d00b03040000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 969536960 1250 969535710 969535729
    0x41e050d0c030e151b010905030301260a03050a08060d20010903080c1e150c07060e0f060a0606030c080f0901090203060112060f0c0c0f0303020c16081605 68
    0x11810401d00160503000d041c0304544001680c44007826083c144401c0383c00346881c1c1d5010020b9500e80c1d40001070f050011440510542d24501c0d080000f0b1401d50342040040300158a0f4404018001a801010310700441414020701c29581d100783c641944c1c0d280b1200d0040c052138001410148500f411b1106240450041c1106c40180c00350000c0914500902e400182c88504150300081c2c2000d80106080d0b006020028042207c1d00961f0464048000000b00300d03942ca04401d00c000165003000390200e03c003000c44201414809100b0107021400191250007503240108189031100d4a40c80b40c0300f0300040000318032820001c0c2605240500c640f8203100c07000740010601030142d5200c036801d03000084003080c0a500c08482190b0007030950b2099603440e6059940848216070a40e4814a083c100c0d6118403554807515540314240e0300d4070385030b030300c01900c9141800c188540b0550501d0703020400c0008004c0c00f440b58040c1b41c0319482c200d5505a00b0410380f1703450114091510030b1072240010060280743d4640c03604 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 969538210 1250 969536960 969536983
    0x304030c0320030c030408060606040b04030b0604331a09011107030212102d0207060f051303020f0f071502030c01140f060103140a090f1703041e05 65
    0x810040c80d007204004420b080e5030720241c034040c0804141d0954070000480240111001c1d10102c1c0c0d9240c0394442044064420b510070741c101e02c8020402000040d940521450b48290000c0c400941c039401c0700c0c100d445080c038007049c02d5a078110300d24580b414000450001e00107403002090503c0441c42d00d03001003940e0b12510901c1818020402d1404400001c100301c00c502941c2d002d080c400007079030b8603080b180d80c6507800407800028a06040081590010301509007046d8040c5200c003010000644072a0402548008001e0300c0c0e070740e01da02c03c560392681c060084034050101c151030a01d8010301030500908280481500306610742202201c0c180c071000010782c28059800101c001003203200d4994040e440c6100c1c0768407209065081031f800349480558074102d907105161010802c2810355680004408881841280d43c0100e20850081039080880364003a136406071243d980c494241100b80c840c014142ca401c0207001820386c00004000401440744141c04074021301c001424001441c69840a807100a104c04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 969539460 1250 969538210 969538217
    0x304090e030d0608030301060f0f0f200a05061501090e01050609031c03020403030e010305061008090a02060d052a040e04060605091005040b2d0301020909070207030b0c0304030c03 79
    0x3100c22614400344119280800040070810201d90703500485078407074009118071004a00040103024200340580160034100815540d80031190f40c80400c00e98080840981000303101d03a42141441c001d03c2d0401c00b01500c180100020030203450301001c2c41040e5203140c802e47e4104000c4400c2001807010100304070b4190350741220219202c200580c08240f42800c400d501c188080120700400701080c1e003590040080e00e000c0e940e01c119070090b000055054440988075035401009407030840411a1040603155000035121082d580c260085800160301500040c40109203581d840d0281b00491003144600140c040325a0302c8126241d02c0c000546082d070149100300100140c45900280400415a00c80320207410000c2c5960b8650501c0d100b4461042c45901540d801140340c080c03204294070345800c1c800030035125003a020a40154503043e117042d4400b801c04180e095034003805444250b82d80c80e0070f00780c864902a4001d0610342c0c41e5051000f92040d000e8618000030204100740700100750b1000040c1c2c1a40d40605 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 969540710 1250 969539460 969539471
    0xc2a08041703221a1813180c050a08060103050303130f0605010b0a030606052b180807150504110405090a080a0504030512041202090a0906020d0b1003050603030409 72
    0x4110506501c9004002e940b03c490303640c0d000411480c00141c100c2504d020344640030b5955649440c45a1511a4a242e5024603008401410091070100c24a5400712102c10010900c038130584c0603d151342c40c20304812203d900c90b2a40030b010a0030618840c2d40248040c90040c58130303516544a9540700e00c005032510754040c80b41d0100d50284030046403841e03489903002908104540c4e444001907410b805c10030791f400000341441800107100d4401c8098503412400381d0300c80380c0001c0821003240b0f00c80740c81d40c40000707001740c9856000740c80819440303c440150b030040d00c00c0e903900d44052a0841601c200c44840c0405070f85058203020202d03030f0300e13610b1980264082d10002020707100c40c02e907145098003190008009001c0010702180042d4442e000e04100c0348240100d40d00b4102002e60020707280101c1c018071011214104001015203086160960003451702180002c0075038150b1100c01c2a40c0c0441c01180c00d0300d0b150302c081903450402000482492000d480c0400c118108900081d480303100d184100320a85071141d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 969541960 1250 969540710 969540749
    0x8130806090a32030d0f0e0607020d11150702030408070b04030b0a0b19060e0a05040e030708030c0d09060c0e0103050714090307050415030c080706020a0305030c0d0c2a0804 76
    0x8143c0f4140611281203d8076540a180001c000d0908075800704001428042d880c0c114080015415008040e581c0261140304050141211002c08d105404055881800045015119000c503034038040d407a0307540919074031804c00e0202841d00e201540a040501010030040000c150b40410980d0040702d408004a40c1284007400110442041385c81e00700c4a66003110300182141d040101d10800e51002c0c0e40891035195110100030484075200c45d00050b035001000a80000348440b0019940414418112401d00030b243d0301076021150380354000c03500700395a9424514a29089003044e10521070901e014490f9281c15680240000c08136603c0d40c1c0320340c0c000306500700d2a580c244508006403402600810407400107040310001d01712644010303180440401e4000c03601c802c003c41c40c0b200380d8855800420901e450307076404696980c0000c001c149840c0d010300c9070324480601030144a004111b141c4d02c40c0031751904880c89404140b40016615040c1840d08041030004e9114003d071401c59007516a92080c03407100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 969543210 1250 969541960 969542033
    0x150207080f0309011d030f030a1d0d0804031205061c0302030f0708130614070f0c05100c060510120605090c06070c17061005100c08130806090a 63
    0x100780411012040210400c4021407055000558144182c841d00d04e0340c44880c001191070380b1495002540014040002452581d9140c000c0c2c000c1c2e65418643d44a1349468520240c107015040e15880c0000b0782510500082c543c0c4445802030444038120200006c0c02c14100040c0806a0003d189810001070503500c000d145c000d10903524000f41d1503442c00e690310803500e00000345038031034179918040e190300160104141c2d21035a491049012031902151030101c0f075494140d00c588091104892045010201044030b4035503103038a1b02840e0079903c1e410444e4550386402001d903000185940034444502400308040300702445080965900807200088984401420509054099030302a0300503000140040400190040d04011a465050001045c00800145980781d0340c0a641d80c00c41251108800e205030714090321100d099106070304041941da00c550f1303034401050f0007804000522004404080003041d1052010950005200020306016450741c0d17120604a04035501d00d0130440311840c0141c101c000d5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 969544460 1250 969543210 969543217
    0x110109080102040902040303021b03070605030406020405030109080712030b03060c0d1b050c060106050a0801150e031c020d14031f0b0408010c0e0402190f030b0a0e060109050a0315020708 82
    0xe411000395900d0f5101d055141c040c0d44188002c0380103115000740040c3c08020080070340c2503004002d01800015250200845894101401c00d1f50030035400c0200040c1d41c4d4003413207008400362240c154542c684609003014400303d00088082800c0c98140100c00840390340200d0900e50110140040d20784074505181000002c140350341b611200c425080548101041d08100641034084403c01110840c2e80c0700c00c4200e4a9002e101c2c540380c08610003030014401e403101e001c240f200e0003035a4a800e079495191040064036062801a04076040810034000340d2044d541406902e4482c10182800785219801e920480001d01c4010840c4070815004031440c1420344084109000030028035500d1a140d41c3c071099410300a003030611001e400704243c145610150b090134003e0b2a4120300148010b40c10040030401a507184550740502404c0540d40d500c40611942c4907800540601082c4000d1440c0e0700c0c08174000b400507191034010034859158084104000340011140c20a0804c1600d005a15140c00e031034030210f03501 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 969545710 1250 969544460 969544469
    0xb06040e0c0927061305120a0906050912010c08062b0b040204180b01060201060f060e010810050a271e090507030b0405460c050603010b0304050d0203090904110109 72
    0x4d90f03030900000f040524140148503000308251402d04030750a0004415200b040b00b080c010440c001c0c0104400380c0154080e24204c1c1000c1c14a030920b00c0303080105401c40c0c0f140f2542801081001d014002c42c0d080000500c1240400242001c0580444240b44c00400042400040404030380100160843d02d0303540040002e0811540e4050002e01980352540306900240150170042d841c0901c00581c0f042d9558680c41200c4103500c580d81400c24050045403401002003400c1902c2503043c0b0005040e443e180614001000d01013510074041c00080364846015018030001c00c41641810382c8060017004c058404000314081d844009004e40c698500182400200d90000d0101d1054104000a010002c1245000507160881c91550205a0300240052000c1c400900c503001c0c0814400d01c03000107a0340800000180034400114503940d48100240d420751090300480b016240100921080207010040c030725903865140055800e12500c1c001003901030703c009001030480080e0f4040400300d40d001e68400f01c06003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 969546960 1250 969545710 969545713
    0x19020f0d06060c0b100303050a0f23070201170c2703010203070503090f060412030c020a0204021603080c040e0402040527010e15010b0409091a040b06040e0c0927 71
    0x10b0761444007818806560700c06a80c01282070f800907401d070314141d090a080e00d038103445031402d03c00c001004460130030301d207141d804c188a456410b482210103407280494940c0c01c0c90144079070741c1c17085100062049001c00c0340e510106d541c40040c8001000711405031400004014400803100c10343c1c010070a050076882e282941c0552000040c440540d074450000c42c46020000d04035448102400c0307a0659885040304e000c0e00700d50003c030b5080700f490300c80d030040840c1b400a0f104176114240b03190000350481c1e010b180200100108821440f08154018481c01d030b11680c030b41c5109007800d1610040a80a10000740000e20442e940d800145083c04078142c0070a810301d04100c610041c500a0080c140204409480da1819204881c0c0c072260142c01340500505940384000744a0605203840f1048010b00080c140c00c440d0180d114000600406000e2a1544284d0040b0700c2d0142c0c508100302844100d0b00d0102000d50140c020f1050000d00e81c44601036990005002c0000c018210406a21000034102811294070395 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 969548210 1250 969546960 969546971
    0x80d02030f060a08030a0f0f031401081b0a060f05070228030507050f030a0f0f02060724140f040201030e0a06020d0c0c02011e031b080a0b0919020f0d 66
    0x1c2801d98007000e4400c8005442203140e0546911013140d43c4d00581510600250030040e0500d556807059058019541d45070601181da40640c50000a50b0b1100340c100b03110300d40c0328500c00c850028030000f5848040328191410040107003407480c001c21140490380c112050200c0011140c04540704c0e40350101600641d640c0024082d0581e550b44000c0106510042c0c0300c51144690100701ca2504403601082d00800a005100328101382c1e558034940941c0440070f0b2000e12640c0310000268903040c00801004e40700d51141d031030500c054030100c03d12075104002c000c2802e02d01442c102030107000046c4150408000407041d191582c403880124058a081c40c0a2001030046016060801c10290080d00302c0c199004d805004c8640941d108959104500710702900143d8118003021551130301c04014019403200c2e24011490024602040310000340d01d0901000040000c0100314151005200f01c1c4000c2c0800c8032410807500b8190f010380c40c60000a600c115595500003900e25041c000302c3e00303c507540c1c213215500340b20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 969549460 1250 969548210 969548221
    0x7030c1d0a2d3c0903021e0c09061017060346030c080309010621021e090f040813060905090603060c09010f03060906080307030818030313020d02042f04080303070309080d0203 77
    0xc07500100c0381c455015018160100d150bd2401050300c0c251004165100700d000e40803c0c0201841030f8000d042c058041c00b4001c0c00c1d18200c14180c99001759200e06400041c841008420000d50620780d0350242c42c034170903030600d484000036481a02c0700e00c0550400c03145912508c41c280403a00514140e4000110381c0290080d00c9003a9003003d250301c18042c000c07900006800c1c1403481000903003040140141d07108555100040742c1c40200d00d4400d41160190030340608102c440c0d80b0030848038111ba0040d002140b000c07441082070b0300d0300140342070384207a056010f0006804c00342c1001d500ca000f040c40403030500214003020112140f00e0343c458401403050b01d609110742a07803800c80503101e40c0203050590005022900064000c0340c000306032920100f0301c034001c0d403035950b43c40c0805c080d1190050b01240d10120203ca084050b07641c0d4059014415140601c01c0e0007204040144544000d8100c44000429000c1c0402c01400e1404010350b54860018180800c10400500c4c00a8061040e0702c12082801c2c40032040c4070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 969550710 1250 969549460 969549463
    0x1a06032508010807090905120f041e0f05100e040518150601270303030906090204020c01050a0b030a0f120309050f07030c1d0a2d3c0903021e 62
    0x80c100c0c0d00000c169480161161000c0c000d51b03c540c00080c1403179210030060443c200c0403030006d200c90382030f62000c0d506003a107441241190208030000e2102a40e03200006124100621007182e0007060101c8842940d1003014101403c004d1801c44030b00c0c840c42c2c0e2400040c0401d6148010007224003e110103440700b140b055082600341400686a03540040e110b06404400390100d0402d800590142d00c03e650700d101d10b9076130101e010b00960b03a41100d005407075111020058031240081c01a5801c04000440c2c985812201c100031200500c45d034030700c65805002c03a540800d0300b0540800030150010723000c51400041c2e9409030050080c1c810000c0040c0f04811000c18901d40114454007034a12900b500495240c2d555410070f4900d014182d01d002103107215000c02d06c810450b500000e00c201c00100c4150020b851842c000d000301800302c030a200815150030784028403a03450a8212a001141400e48612a600008030310002202030300704500c10340d42c0c2070b00343c092500812010b40d4046400c0c00003814440180c1d200d6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 969551960 1250 969550710 969550727
    0x503010f05220b0c1303080d050613570e041109010804060b03030f25030e0d0602070b01150f030605060a05160206030c07021002011a060325 62
    0x284074060720601c041212060701c101c036038101d60400c1140506032140580c131065580010b481c40540c54a9000000000c0c8800b400340c4005040e00700300094074a006000e010020010307000080b95286001024081311418000740000c610380c40b001580b241d000207007484003008560f19108130030410036840d00319101d64401c400d411500c1a540325024090b0707039814041600d0500c80442d5172040107001b481e0356948100d000983c068000c070404640030b01c00b000840e06550040484c0f40030300d50b000400b00032048001c2400078000c0300d00303204180e110711641c400511850090113a144214440b0104034184203007901a2800c19400480c446065607541c00d0402d02d041540c3c05440200741c01041d0103070352500034440c42045650241c0300ba450510213030800c0ba03e07a440108200f8807912041c0154025842c5c01c4c01651050344c43c1074500d80e4805590041082c201c0c1404068021a810400701000c03034001070f0108600c898099414035103d8440b4032a201e0740000800b04e5000761440303820050321555101c1c000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 969553210 1250 969551960 969551971
    0x41a07021e030d08061c1a01030c14060c030711012705040f02031003080c03130f03050106080607020a0609020d020405040b0a0e01201e130f06030618050403090503010f05 75
    0x3c9489000140030191039506045a06940c84100358040e020f0010712801d0320388a15104090700d241c8200300c5144100341c504207070130a8980311440c400a1007100c0106145100d501011524681040c9142071001c2c0c1d60f100d13441c130060002c202600c8507030301c590203041c1d102100b041049035007030825403040807400c0441941c40b0b4240b01e203044c00314040c18850b4030310031640105210402c860841d030960700e503240035900108942d405071004202c89032481a91003880c001402361480d02c121144c0c51400c0007829151103411518564220005112a10781c00046040d40c080d0720010102d0124850700001d2040511014081d42250601c0c081004028156840b103120b030075001c0003042042c4a8030062401c8440142c031040d071640d07500e9601c0c0507003c107a10141c041c41200360388040043c00058003031900d42e005810700c4c0c903c40402d84030a200c01306400584101621192400b04040c514000400000b14185404000e02c0350f0365102007000d05200701504000b400c1d010b0001e002c03900b030070784e0000002e00d0120741 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 969554460 1250 969553210 969553213
    0x206040b0106031e0b122e060b190219030c030915020a02010c02060702120703120e0904030c030905270109020a052a0a1406060411041a07021e03 64
    0xb1070064041c0c800c520b513aa0358041030182d80f03840b8070a040010300e50301000c107500c4682100483d40f0440e0400504000b400d003440741c1098003100309040030800007481c41d080e400506000051007240750350740944200460884107007000051051051f810700c103010710000d0b0202d4564078900149600710840b504203610a0356481e0b080382d0345640081196500c4060b80005030000034144c40550701c10505c2c0d24010340005d056518040103076001440c03d11102c1d4030040c1640085100300107111340f030403844190700303140d081c501e10300040440028803040ac024001000c0c01844280003050500c141d000c40040c10000e0410a180100001a100b03200392004a41403810108400860140c0ca10b00945000c01015200d81d13003441128500d2201e80440b2611880d449113055605808000c82006000381c0c0e980112100d4040f00440c1a405051500040555000c0d9081000710516880303001c04507400c5881c2c0c0400c0108400d80d1243c05000b078420307004041d50041e000f85002510010445480010074000c40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 969555710 1250 969554460 969554483
    0x6101b050d050901180308091918240e0f13060509030417030906030103060e16030303090b0105010e090a0c0e031b0a0f06050313031202070b06150424030e0a03020604 73
    0x2258280741045070200500042040c0235100d0603040c00240e10070810b5000202182007074030703001030791010004c2e409550003a50300c40d144440c000054008030281030303015840110341607040c00c0c00181100806004241008450000205900c10080c603000e00d199102d035082c821820440707800740d40c9400501859401120000582c081c801c00013045a5609501800b05408c5a195803120001002c0601410307406c1c2c098090f0a040c07664506e031f9050f015500ca902c00003030710203060420b000d40c114141c2002d8144801c0c891070007929034a030f01140758404030010b00414400301c1c14000719041500c404900d509403140f00e03180400300c0241c0b0020081c1d40300540c0c0b203680160740e4143d4803c4800262140e100450000c00c00320360105c0e1003030418060304d4002d0a101084104000310001242c0c480d54064031000510400c4c804e8510b040407a092030700180c01d10940c1441d0511000600e10514840501400d003540380c11540a58041d030840d13200f0120300000c1e01e402c039105050203901da4004070741c111141141031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 969556960 1250 969555710 969555737
    0x150302030609071d040305130602010903140c0a060902041508060405102708040e190609020306060a0c050c0303070b0709150f050a0c0b01120303050a0506101b050d050901 75
    0x5108821940c0c2e12045150002d20821803c13041c0368090802d6082010030080c1c0b0089298100501c0e005002d0742d1300005e0400e4040c200200007035807401005080d500100451030030b00b000001c0356007580703412001c00120269140b00050043c0701100000c48071510071500055040340200b84580700d54050b0b0305030303460542d40889072002c9907070909014001e100c00e021484541d1200030312000c1e415100e4854149081e498030040381603600201c0749810f560360b20245c100b1100d00f0ba401641d00410361008190b04500b004000900d03e406841c0c1b550041002003179500040c854104105032010714054243c9a07a0f035181c0c2491100040211132141c00b01d508004c1c0014040080b917a0103040e941c0b5a0b40705c6080406552044400d540103940c44400c109100c9101ea000c00c48640701c0d5030082203010103208100d005481c0c05000c0e42c0c0006c02046059280c0f804001852b11002424600840180381000c0350002c41c001081e0700c10403c4c4005803942c8281360b0f209000d60380120080000020903280c001011084 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 969558210 1250 969556960 969556963
    0x11d090c0d140a0b0a051e01060203090d020402040308030c07030f110717010e0610150311070204051b1801320c010e030c031e070b040f15150302030609 67
    0xc00480355008401d8006031400309400503400007445295200b51442208a51242031861909440c1d0744c00c5a6a203000748803600e81c1ca140c4140c0c000a05640d841c0c4150300d000406903c2c0c0c0545c0c0d004c00d0041030310b003200c0790842d550b50341101c01a40c0d10002d02903d9090036807000300e240c1c0040008a01160b140e03445401c195000f02000a40d4600d0fa00042101c070f030038400519168084074042030000c1d9203807034030100090030030b010082c80303412491a07100400c0c1c03038101004100b40200300b40a06240c549401000041d04100489503a00d4056030301040a4030703000e82e06000c000c659030781400300b024003051211203500718651500b54420b09a03512400031074910540004017414805643c2d802c04481880015120325101030311828105d4000054445510b09215046600078006403405030000a000340340440c10300401300d02420745443c40c9041140556481130810401342c00513060240c640140130410507440300c0e80c6181d9000300c1c2e090000c0d04a8070701c41c1507100524001240319006a10000d008580c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 969559460 1250 969558210 969558223
    0xb0603040c120305210a15060c021207030f0309081b060909091608030d0f09020d15021b0a0b0106020d0e010e19081b041b030b040b030105011d09 64
    0xc21031641c00109140041e140c15100c8a0b40701182808010300820203021400580c002d280d4a15082000c03d518100c100c6408a0340044418018498006801d2011a5001c80711908c0070340d044d502180040300c1203200b1403500302daa07400281b200d400b10060004250707004401104440700b1380c0803215078200c800100200240d000c0c80c142e0f000441070066061078a40b21103126000a00d6009031418441100c681390040204e5070050701c1154400240d40140e0300c07181c40b0304440c3c0c80d2032a43c200800b450a0740000c41142496502624030525020071350000b00c22036045071031681030141d960040444960280382c9401901e8001d0382c803480400c00018140e40041100030b9070b01f07074940d01c90354068508001983c4000c802810682c0010103035024000f880b03001c4507041c002d0104080107201c03110303c400100c40d054100d245450f00503400c02c5494041540c1c1c0000c54403e0310843c0c10f000c9514405140030400412600c41000c0c0d056081400001d0141c04601c900010090200f141c0d069039a2101c001669424 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 969560710 1250 969559460 969559463
    0xa09081b06030411181302030705031912030f0203070905033007050c03060a060f060203070209070f050c070603020c0706030b10080c0d0504120801081f0f021c0b040b060304 76
    0x5010000240001c101150604c40000003d08120322010b0680442d4a0070f2400c503038551400140e050b112040d4a4100703c0703d001000b0440050519003200380540b031460020010003090140c543c42c51040140c080c0c3c016400908080e48215142d16006400a001c251180301c0c1c903000303020312103510700c1c10a282c03642101d40d44840b0000c08680e120841c6140b1050703004000a40342c90186001600c0642c2d0140503580c010100c0c5800414001d081440301e0340c041480d03500010556004200d054010307141c4c0440c140d400441030030040741c0420050780954692081c00b2074451280548500410055010b901030304948070180115510b503500c0700002d5003151101408240d116a885810039070141c41201c000768040d04810915040028054000c0e00350b500075030b8119030002a0b800307525030103a4072030310783d42c010705a03880100740c240e030948103106010010030b03182c0520503114162680b144250790100c40300d8000b00003120614000c51941840202030341c1d80c0c01c920880c1010aa5076092405d00152409103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 969561960 1250 969560710 969560719
    0x120309150903071a07080403050a03150e06121513020d080a02010c08061c060209241c0203040b0a09231005010f050117040c09021c0507082202030a06020a09081b 71
    0x1fa01c80b5103058a0f982c11000d0f17502e04168540307a0501032041d104248100078019025400340c1400c044e000c01440c040075800f400200e80c4100050407903170310841e030415000310411241c01d00300712082c004140c6d00c59404002510020000032421081541580854000701180e40c480407152980340410550075441d110102800990107078000c00f141b0240e00800c64004000c0a1015115204034030704004400346141c40c0d5510b2010502848021000106500030600c0b018110300c2c0d0715003581e80e00a15a00030303041282040d9203080d200c040003141100090400100305411015182a0240a60700c0300c1184041c84a82d0a042c0001080d4062040d40c1c01070750350503100e40d510b80b10607032201a0101001030007600e5000e8407450000d600c2c141880140510000040500c0103d030850944009031640500004100110380c0c08100143d02644190405a088800c120300c1480082c00024940b0480c41c101030b201c40d1001036200a00f60f00410700100b00d92038102500d141452055980e80b81005009010b80c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 969563210 1250 969561960 969561977
    0x6010501120f020c0a050a140a080d05060406090e0106060e031c14070210030204031208042d0602031e1f18090b091f0905120309150903071a07 63
    0x1041c6940201c42214516500107040c0309180038040d00d040688902030f2038640000c841281884969000622001040c5000704031141c000d956401c200d01c10680785003841660703400400c400c0e9840d500007100400540c02e06010310601ca0f030388103000b0b08462040c0e4020914180e1650f00703900340814200c05090158212101d9110f902c0410b030352002826420900d100f030100007a00050340d4014103890f102e015550b0040c3c07158118a02501e4200e1581025014058130000708800079004071211070a07009030070300603021009182d40c5c0c544400c0d100f81005003054004420030014102c00065603000c1c2009814445094a40042180000342c68045051040d0f460041c1800039070850788406030500020078001a0901c1c1641f1451140001a500d200151f000940440d80c00c41c0710710421040c00700210f000b000101c0955403034556a14209095003410500400003c0680e40309026000d0115a00685092285099a48241c0325840000125441440080300000c903100b210300062180d01c903901c03280d69 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 969564460 1250 969563210 969563237
    0x1a0103210e1318080a0305040b090f1c09030204050a200f1e070506150406060e0616020a1d0103230c010e1912020f01020a030518041d031b06010501 65
    0x26080b400d2400f603003800100c0501c000201120010480401140e82c00101410130f440d212101001c080c0620b007503940003000b1407003682c0010511a0710031070072142c0c0c0c2011510f1420103450072150780d4400b0b50b01c02e01c0c00007088000c00c8190001012420f410040891800200d110701c1010300405201600d8000b044c080075581c9600041481d400d044921811400d100d540d0b55001c0c13902d44200e40340b88980c034058101c555182441c0c02070b40c02402c110305060001800c0d00020407514060f02c1c01c1d541a0690320030b03002c2c0a54803039001c000090200c0c2c21240503404100e080034050345400384021101194601031464401e182c0350b4005512002540c041c142240440c1c0045407040d29482030079a012400c40b04180c00300d120310700588000c2000c0940110b0584042c010819660b42100106042d50032440b0140c00095004007222040705d0b060345640342c54200900460000c1105c41d1009440502c01d40303111008110020243c140b1001c0c0c140210b9060318002e070610b4540d00300707101c0e0501140b01b4000d03c1c1c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 969565710 1250 969564460 969564499
    0x50d020306040b10030e121c021608070c0f091404020d030e061909080102070309050d0f060908030a0f110301150e030105040803010501110303070f03091a0103210e 72
    0x54215000610100b10325103c0c000260310329260560392408a640e0701022140540c2c20300202e5030070074825540a04000b20f40003441d81c41503848601c00100c070307030004410031310a212a003501125500300074a20340343c1d0018542404100340350700035006840c00c90300c00010310703101c24043c1100002c401024450181c440341d0a100000c46025000c4090200305000c00e02c01d80c44210241000d250740c440c88440c0d03800c0c10900504092410717080040b00d0b9004100200c00309420401e0102180c000b42c8003c14004201e040c4088500d0007030400900050130121071105102c0c09101640c000c41d03000c60108100c151034021042241d940b106014101d800900041001540c03003400f0b4515141a800c2100c0e594250070002400c46004403412105200003000521003540d120010761628202c1000540c514103003110040e010aa40640000030182c0301c401810400000c15510515003001780191700155849141952081d00002800150745a0070380040f4003551144806145614002d0800148604040006c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 969566960 1250 969565710 969565717
    0x15050307031e020a1b02030a020108040f060c0e040b191e0f0f03051e15130605101e030309090905011e05040506100501050d0507031503080903070510050d02 69
    0x54141952042c8449034005200c00c03903149000d11040040e603603e241200507141189200504000740d0700020290010b880005e48209429024204200c240e965898541c0c160019103800a00c100c0c10003c000e803000382c002c02010740c500d9088070184030000b8954140701740380c0b40540460b64011055902004180d408a42c0c290703a1030490007038030788615100c0c00c0304c6805005c0c0d68002aa84c0074401c034204184031050100e0307500407440007040c0e0160300e84200c0c895502d135000e1460000d4485000c000c10004104405641c507103a0b0310481c1808149040501c11107000080e2207a80126690f0000d04030070390255083c0c400c150380d8540c03502d06032503040078907941c02040000421500c0759a1000603c84100441800b220340d03078031015012920f0315092902504000c00501044c0070203001d900148042da03005403c1d1009244083c0000405944190b0120003404480c19882004403070050003006024032100180080e400541c100c82503d650b80040c00005c0d10400d1030100018400d004a5205c8007003500203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 969568210 1250 969566960 969566971
    0x70f030506041d03070c240e01020c1305040309090c0914030708250f050d0201050c15010f030302010e0d05030112050f0610090b09070e012003070f14010501150503 72
    0x150700f111400c1008410240c1840d90f0142d070313001180740d004200a0f102070502030260301c1440c8001840800d4580e07881000c443c03140e814440c00d808008002d900c02c100809020340020241c2e800390781d96003030020040c6802d450075800143e0b00c010205e11a00c0c1c1d4018141c00d48402d80e540c01d0b24034901071035106000c0340030801550502642e0800944040f0400c4019000700200b5101042c40b0700305450846c01490f140d001080d082507601080105544805020341c0701602030070300c10703619141c0916036414070402a00d961440d0348401c0c00456151003144036041540d01ca500200040340c09400080d5560003100440c40003e001040144800f02c42607610340e82c014410012280310064070320b9414101481124002040d0503031900030040464035008035141c2003811303643c00d1150b0401500c000c1041030740c3ea817110705105020082d1000340405802420142001c8401d8070f2301c400c074618003000039503120482071300c40c155070040e1030070159018811340d0b04a9034503114100d840d414066040d55150801040f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 969569460 1250 969568210 969568219
    0x30c0906110a05120405090a110412080918091009020f061b33041205160501020301180e06150409060204120309185901060e070f030506 60
    0x11070b840080e00802c00c01c0c2c10060426960740e2514108001e02809880040140e0304940c1001d007500b000076910402c650599070764010f0240c1c2c90b011410b00d44801c1c42001080760300300384040505262121520a014000c5264206840141d05803103161001d507050f004010b94403a40c5c8002a80b0300f494032000802c19440319085c40081c060300e42045038205502c90700c0b041011841c04030321441c001d07641c4004086d0401b42c0810009141091784604030700301c6491000710180040084c06204400ca00741c160702d141503002000355640d41c0c441d0410070602001010719010740f414800480320712800070070024400c6991450003510010100704100c094000700ca8292181a030030440460f03805a40c00d20340d603a150280d110301d905545404084103520b81e00344100350340c4a15085032100c4015800012100a51a010445c1031500c242c050f4100e44010880c0c1c4400145a03990012001e04241004075080c0441000204a4581d950500c1030603001d04680c01e400081e03946030b94490441c000e5115a400810151 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 969570710 1250 969569460 969569473
    0x60c010f053612030109090201090906032001050d020c010603020910080d030506010c0c0303112a040914011e050906071403100510091403030a020a14122701030c090611 74
    0x450f0900c2551080e0800d000032a1102c03a081c1c259608040381000510300038008020032403554403030414007142c03154115540045c1046071203c50703110b041a10103030003c8400440d9100c510320321150080030310b480100d00130031101300000e018488050420084440000c050445030340348440880085c10700512090512140c40c1d821070118061070300d0348000c1c520988980786414030402d1810301d09140c86c40116607144c260100008804403402c0020940c0009075000311700d01c10740340383c18114506282c01e031268542c0707007042c1080070900e09190031ba0b090311090002c000715100c0325641d5868840403604d010224901400b10410396064100a45e407040692640010007610340c000542e1031409036140100180c0302002c00d00c065450000c84038800300c800c50080d80b4018486901945400190308040c0240e10403000441610000340080403040e41d00c0c50143d03580b034807240054000b044030080c10f0300000c60031416100c40703540644100203001002d9181d10a1003864064121140356051280034018000c21 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 969571960 1250 969570710 969570733
    0x906151836090b0402040e06071b030306090212061e0303091c02130c0f03050f0105012a05072c0f22080a0e09010b03010308030a0209060c010f0536 65
    0x521819820b90301c0b440a081c458100303801000203503103482e605441765070008070030721002c6030f0040c01c441d00c01c800c00c80c0c01000d00d14007070405800610291f4040c4007440e000081e420303c01e0084400342842082c4c01c5071003030005114410134407018001031901c950564810003507994540740800e10440101070b032083c440616203080d400318199104030b2070005001516100d40300302c080d03000071580004200d030b8902084649001e14a140007401c041c4122414030030176006201004407050200c0204d01015694141c80a800b80f51240d5030300b100c1c0c41150b8100c8446000801d24004c1d0500040501200c00950a417a0325a0803201200b00c801800703550b05031049084050740c2070815212254450700130042d1644070908808050122808a491148030781c50010061221401040689055076000588181c5940d0346215000007841a519481d078403030130200d040c600c0030f84150894800200141014041034507064501c00e0401581004801c50000120102c01c040ba0f55002c00803a4080da131003107070103400c0c2c00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 969573210 1250 969571960 969572069
    0x212b1d0a0b0d050609060301200a03061214060f091b01111e0c060403231e011508010e070506092b0512030408030402100909061518 58
    0x3030b800800e490751107104110581c0341100e050395120000394024030110509035880c00f0134030380b0706542e4044840007041a42005100764400800b41c19403d04000c40c1d5086400e1842031708460140781a2544120f00014501420a02c1801e0260300d6000080c81500240387c007500c00e0b0401c2180d00b134100028141388800c030010402448042140064a550441c02c10301101030403c0b040441d660300a4030104400c0002501d030800307440c000404040c04190480d00d82c6440d41c1018141c5d00c0d2a40b480d95100078002c0d141506500100c0c8543c0303406074101170282e803050864261402c3c607904c4c034519041a02e0802442c2003040040c848440005c044c041c140f0024080d003509102c5103110b200d03d2040060780d810420a041041c5013000c0030100400b801c62030310303513100c175500e1100401c028011301e0740041030a05540107086003c080c013aa0b071028411030351a0a800c0f005009491030b15400244000303007500408543c5189070f0140c030701006050040417010b0303048498410071801c05056650070b1100050740c4024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 969574460 1250 969573210 969573217
    0x3130b01092007020a0302011103070609060e060a06031104020c0102090301020417070b07110d020f03010c08091501051503070207081c03060e10060e212b1d0a0b 71
    0x50014000501d004810a02d03081c29103240d99400084070200550000740c1e0f00e9420b44030849a0901e0f00e8540b207013005030201e082d8020b0303100c001c0031281420760110801403603400003c6100a01c00031a01c09036101c3c1840030a0302e20302d2101901d51401c3c84e1044000e81070a4005100788460703800094038008400c2d0100c2d089900552003104611841e0318000100b580500491780244844401503040c01195100c6c1d4480340380070b2441c0d912415002a06004546031140c0800d00708000900820540000704000707041c0c290100c1d0314072068081c02440707080c55200c0010243c107031080a829121a0402044d4001d030583c000383c030002c203520921000044440040201c48640050111000c40e520201c1c50080c0aa0b9860b81006c0155040102001070400311103000c801128400d01d8122104403a0301f0100d20b407903901c80c0020394071410318541558100400070701d040c1e01007040c440508020354245011008041e035400007500040c40c04441d2901d5081c0c48000044102008142d400c5199540951088960 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 969575710 1250 969574460 969574469
    0x30c04080a12022e091707030c0219080307020d1e0807150e030a030f06171b011403070c0302030405120105270c01050f1905191e0503130b01 62
    0x20607a03440344442e2581403040b102260200d40780010344002440041c03040c501002d0f4050724881d500c001c0e41040c445000c020640110080d03c006580e02041d00300103003044075181081c0d0082042c042c80c03914440c0c40300c5018080307980d01b5000d54240055907007048185040c140040c0c0721081d00303810f000002070742c0c80301c0710f0300d2907115200e09655034559150000c2e050b480490101d1560303141c00140c1002503008402c0b61190601031074000b4a8000e4005400010505900920301c1c0d0f12594044000e140e000082180c1c172087d804050140d6580c49200450340100300940f4044201420f00115000a004107804d8000900c03034015a82000d4407800030461550f440c0c1c09400d2180e46400502005a100004a10b12600c80049143c1d60440304031059584000364545035041110004062290207031140c19622220b0030084008024041d000c0020415006880b00800240074040482107290040001c54599070105a10145402d2248030039109074100400c0c180d60022a85101c1000402080886000c0e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 969576960 1250 969575710 969575723
    0x405030106060c0b0a0519051009020a0c0b130f12050d0c03060e0f0906150d1208060307060801050a15020a0c1e08070812031807150806030a0f08030c04080a 69
    0x2504141010200ca13800980601c100ca480c110602008040320340c40722000c0388180300b01103241e40300c50041070082e000d203a000b03008080c400f0540300b2a055101c140302c252640650014207664480e0b145528001e100710340014000030038010300b9000140b0000b00e11850034214100141480a03806030b51081c1d541e0f10101c400001d94401d404d02411000c00001a001072022080b0102440c01c1012140e0b108070107003c2501ca1030b500111001d4550b10a00c0741c82410398010000c4105c3c00d501100505040802c0d200c2900ca4000e9000101d83c981c0b2501c9624102c2e04e005190048003031030b0100c1150303030001011a8000310b00071390f19248049100b0544000007040c0707035546070200c07400341c001022074440a90000302130341d0002c860400219500007090505043c1c1c1d084c55940c0c07a00e98900440b8088100c40c039071020b42c0514880011000034030088541d0b022603079111800741d6614081015203540213000300600341c844005010003c5850600074603400300c1c0f5020b4503440e10340c45855980c9400301255048820 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 969578210 1250 969576960 969576977
    0x303120a0603120206090d050318030706060303030b150706050402040902041406010f0509130e07050d05030a09060f021c1404081b0628120f0507270b0f040503010606 73
    0x300802d40c040f007182020f00b840a804a070400b00c4443e52201e5081c6e04c0c4100300302e004000702c0c4a00301c00802c0c0c00003c00d6484200ea5403512503180200190402d440290701091408e1180d080b1800c0443c411f4000040701c0380c095192003591b99030080101b80c050300982e0080e5554501c0e07001a103c92082104480104c0b40400c028907040000501c0d052031a1088801c00c01c080c0441c40107071311000e445508115110a011640303400060806203416801d6104d10340c409500c644003814004084018030f03200c08250f880440240c1c550300141e52503080c0710680c10040c0d00020b0311408484029202c140505030783e02c0d1000f258405140070007681c0c0c00c2074004918a41102e054111044d440c20003001110341c068400d582488100504d500c1d484003d210368a8070140300240d10140988181a10f4034000200401000000c1d0744014280080c04101e0301d030b40c0824120b4052090032003500c8003107035403d900c4155444003141042e5003c7c120b5040400005140c00b800e01010890386c0d020701415002d06440e50714502c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 969579460 1250 969578210 969578213
    0x14120d090606212d150c0504030201050a18031b0617090c1c0c240206010e1902040b040b070c1d0f040206070615151107140303120a0603 60
    0x80b0b41e0b05900c40103907140c1d086880603c400c1000e48607440e150300a15100c1c0381a240745404013401019800708a1071400e50450b541c01c128030b40032002007804d541c10307040102c0740001e0f00a03209849a4000a40030034400c2c0841180d20348100050022403d2151200066560381d070343d18100844d4140c10207600802d950011b00c1481e6001000701da0f070146038510b40380e003428052000751715440c07000500c07405030b440450312080400220182e0b104296000c500f180c0741c5603860071680c18181420030340780c0d99840d0410004108034800600c09043e15400c50039031010782c4030252010980c0100d403040e007111540a000004a001ba020084d0008100e0040141d640d98a9031401c00351748009500096803020f40c014090100042030840150300032544003404010f5221400024018000c000c2c0041c00381e0704007a900030800b0301070400141114103196161500074020345003969401c9241c94040415809108104018070070310781c1c02a0075a0b409415689001d036500590504a00c0c1104da4192254480d0f40400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 969580710 1250 969579460 969579473
    0x804350c0c0418020103020922021207050315220614091602060f10030803040606080c010903031d0a081218090411010c02040e030c0105090f060105030a14120d09 71
    0xa002000720b4041140c0c00100744002001c0d03000c4039020b070401d1b5011500d6219520385441c2803041c54070f80f0105e4000f07804510303090006075104a0010714070581d54804500d0320b40c000c0e004d03a801640c17442d0a400000005800b030180c60030404d07209a441003444414207030200818030a1b100138100b04503001d6208005681403002c07030700020b00358112421002501140c1b4035808100a50000005460b000080d118a84c0c42c40c1d8000e1240c00203400910000184010012076a001a045880340b00694080ca070582e401502d2164061101902244910030107408002c03410110b0403000d8002070154900c19140c0190f140307050008540c507034800800280b00000e21400b030790844d82c000002c88212009150a950300c3e1a800039201801b4144200032100c0e0045503079603004032001c031000030201c075100c00e000c20b5024080c040965400e01580503140361240d0715030b8085044c0b4144c88001d002400035901f1540d40c40c90220b00070b5248565401281c106100694088000b0004d9403051080880d112300300e410200c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 969581960 1250 969580710 969580723
    0xa0506130e07090f06050a200307110111150a0e0f060106080c21040f051c0305100323010b040c0e1e0307050d02030a0c0f03140105010302010804350c 66
    0x2c00340402001c0801010b010042c215095400d80d20702251915900101601c0030342004c444c0070440b4400e0881c02a546400001a120040c0a0804849020303541c4c4019a65030314040d42882054000f440c40309166025141451380000b04140000b5039150304100c020300f050307090915a1403503005400100511903120302300340e400c007035013001042c901490480aa484031410040445400000c10001401d20285405801c14907800c0000c1d02c444580400340200c0084035424440007103403400020485c8800541c1140d0252940960342c000300c4005041d0050150002d64203109d0190740301d1003100080d80341d03400303241c035207442a482d02c0030003030302d54010070028584c02070340c44000e500964400300051744e00240d080708943c401d681c8a404110300380046400c03d100c031080513080020700f030b0340051810920390b07054003201e0181240088410501c8441c500ba0f40b03080c88060f00064110000c43c01040c02c50a01510410300600b0180c14560f44c500451103c0d41c000300e01c0489800041200f841d8041c050200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 969583210 1250 969581960 969581971
    0x15030901060f060509030c0108070c020a06030f0e0705030a02040908040314010b100f020d050a030221090d1d0f06091c0221030403082110031101030c0c110a0506130e 73
    0x210b00384102c17040403a1381c891514104904100c00c42004c980001e00640c070748100035401909a40c0503030707120301000d400342264a803030116080c0740030603c540c9114081258010b40748020f026000002c4107800304000340000c885d0540348a0010440003001604903001c80010000110000c1a50780c2800200400c400800d02c01d2410b00a42150414203258023080380300982002c0e081841e110400070201314000c0c001c2130980e0151550302c0803225a100c59181d4507921510f0303000d04a4110140010040758541c840300202c44804030900940c0d072151a01104540300d5075406050a410513011800080c062a90040d022041e01c2640001d0301c25403d040301d040e0700038900703c8461461920304406580d581d10030340c80041c121840109128000c040e01d50254074007141101042c0e045030900c5002c0383c41c410711501c4100d65004009844101a500a006810005416880e01c89407280240c031036840c0c0c1c0c1c0c0720350b05007a0310120380700c070100c0d1715500d18029100708104194618091130403c120540c0e042c501805c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 969584460 1250 969583210 969583217
    0xa020103140c0307080a020d09030206090d020102040803030f07120603080304020f03031c05041a0f1602011a01031e020d020433050d09050604140105061f0c0215030901060f06 77
    0x1000320b6884a1002c0707903004101850300329225030340c0e5840c0340c0003405540206a1030a0614840c98107060340050a90b00a03000c150a5445d0360185c40c00a9080344610f21418095420901c000740c80b0389030b002c4999601402c14100075000c840c0d001114401c581c016003045a450301c001c414401075003482201d042c412a41a001035203410407a48111040c51034000403d0081c5490320001020005000103800702d86900d8400081117040689441500d00821108410411a146462007510f481409507110400d51003421180702e00201c6c00442c0940380741c040644c198411041c000c032000c0100c1c4003d210031080030100603100c83c100200c03c600900e0b55148802c0e400e441001092581d0003031101d888500689041950349ca0fa03240500c20042c040711600034000d809110100414003c5441030740b50110583d5000b0020b43d582d8004010b214125203e080b403c80340805424401c190180c40d0128541c1c1c0014119500010294820007443d13000300c1c2c0040181c0d440c0d00007003041000040750b09001d40014207 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 969585710 1250 969584460 969584501
    0xf020303040b041e052d10020601030215040f03020f0d0507060f0906090503060a1503291e042003011e0c0f0c060203100b1803070506090102101d0a050a020103 70
    0x19041c1d070305032036040000b9107058130290f50403591b2041c0003c040b0405440400010340340c000c083d440d01c00920069006c0c0005400804114032390400b15070035a0007460114451505503000d001b080e02c49007103240c0d040ba58031400c00001c2541049000001c0000360380f04240e00024020040c240840c90b80701074280040c1d43c00921481c1c0d4045040c80e88002540b00c0010000c0e0714000348441e4028076840642808500340380e401c1d4104862080d98441602c1807000001e607214442c0008180c452602d801c40458141c1002c2000601d40d60581d8034800902c00714051a0300d00100080e084441500c0382c0c01300c1e080c0d842d42a17240303262140101070313108a0b2407c002c030300314802c440f01400c1030042c6c0c1001030900f640000064900c0d001c108100c0c002d01542c291040d00d651003a00030020500100c2c4d0264070030b00c03916800040e10310301741c01158000d0700180d024100c43c0702824a080c01420000c051001c8945c1011440400c00d0b00421042c15510b0084004000c11f00c0c03103000150454001c0460b4500101100307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 969586960 1250 969585710 969585719
    0x922121413180614040203040203070512030307090e0601020a0b0402030115080a05011d1f0207080a03020c07080f0c0402031803072904110f2107210b130f020303040b041e 75
    0x44c10f003110908000e42e00540c0d21303910307880007904010607a08140d0303000c84e1404102101810000c003951094403151036080d6a41d8841209030f4550204540d00c9006078840910741001800c2e00da000b940141c806000887d1003900e045c0060303456078050300300070410381c44001c42d401800320034040e098000c07904103100e22201e184e148140740c031102104021741414010b010000c01480c500d41c11510000d42060006458031010f803070040c042c0d40b007001940200e110700724010850f03080c0400c900d94501781c01e800401c0403001e000b0900000e508020610034480c8200e80b42504018030a10050200350311070540c09115034980e480048080907000308002e0825131110422000865082070000400001c40d101100301c0301c0c11001416004440a0041203021202c48000c0c803403100042c544240c4004450200c201a0145c410b20b01d01e00c0103910140000780d0810225014a00b106403100c0301502940340307201401029004649076622582c450b180c0a4400201000b0741c5244180082094031401c0062803001d142 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 969588210 1250 969586960 969586979
    0xf200a02060c0a050601090501060216051c080706140618010b0304080f19031a090c04140a24030605030f060721091109221214131806 59
    0x494100a00405001450410719a020071120800f02e5010040300c00568560103602c0140c8400c0c403a4074054800c81c106c3c586e07415100241d0f0001c2e213001030302d21704144001100c0c007503050240c06000c1c1c894110400071540072035041c0c01458600c49040c41c48441d00e04140c0c080c0446031405004251282000c0350050140b0300c000022643c0280c1c10003040c68417012150900405480b0302550201340c1511b003052120302d01d4054224060711600c8030300702e0a45500170030900c0700840044a01030340714141000240a0701d004500351281e00c1001500540078103859408038a00c3c0072450803500a901001b14401c4131181c3d0500441c00542010783c0a031043d2101c0100c000d541c4c500203400701040c0140381d1025102c0c68402c5c1101c800a6800c0a4248400c840d942031110901181103140380c01008880c00184800c0180e89401d4030841d200305e01c2442485241c2c803414102050807490500300440700819070b20803250200540035603050f2442542005150111605003054030159200111b41098810481001c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 969589460 1250 969588210 969588223
    0x30f150a0923160e0d020a1d04030201051b1905090d0305090307060309050c0909010b030d030207060b060c0d0e0d0206221a09041109061c050a15090902040e06070f20 73
    0x8081d81c1810703401700740384005060054130350400e990785584041c00400c10302c400740003240918040d030000c11035030310382e100c0051160f0100905821075071001c00030b803071030381c4006d0783d0021580d001c618296003400c20800000c0c0100c00140019000101e011821895900d8103110402c001c00f0181410414071a8a90f116a02c0314a0317001502e02c21016803000a0210a0a4120100c08171005090b00c21240c19440064000c2d0000d000c00d55070141b40804115030b50070428101c44c0805a00402030030701840034181120020b45404480c0d0704071040c2482c800060710380b440500043c0301030300780a032031200c1c03101c840c0c60381d082440c3d1040850400c0300300640c000003c0101120020303c01640c2c04900b0a64616054000c0c0c0300b03900d4600c1e00441e000401c0354901c03521164007001c0301c4d4503810038046500d4001102c0107442101980c88006104080100103d85403940701e07220f0684082d00c0828200d514600c068102682103c105010a5030086541101c90f8414a03404031198030002c146151802110b0041c0e9521 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 969590710 1250 969589460 969589487
    0x301060215061302070f0602270405040b010e0901021c020405030d020a020a14040603080d0e1c1e120c030f0605061801031d0a0c1505030f150a092316 66
    0x241d0008071017040c000c00c0e441c3c903010a41c001a0031b5503074810686203400c1044041070b045262a05080c0d143c0c00c02e140c40e02446014940155100b046a4201010320b04c0c0590301600480c003641d42040303213428416026480780e8980107807402c0140c450f440d00041c5804d0054019000c421504090b80d60001a680c0c035181c1e1003030728207903072408803400518404030f002007045400250582a020a0781240e283c110b803c104c075148008416602800903440c1e070101003880c1e0100c100007090440407010603407610000409006615468814680d0801c584107034200d0700d40b101c60b400000c0e190007540780c0c2c5403018042c040040005840c101d280c00c880301e09260800d010083c0f0a8100750310740c20303000640700000c001441c07020403101c01d4441d03c510707a26007000c40c0c200521441e0265060005e000040702c1c050300c01d40344200d5016680201603a40e01d040d05d401c041e152903002e98406140e08000c1120300e4030381302d0381034411142110000080352941a9500d90a0700814504e00c0132280248804100c0c3d00c02c00c03104110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 969591960 1250 969590710 969590749
    0x10020309011e02150c0304062910031d0624150f04030212010204030209011205030a08220b010e06030d12090c12060b2121070c0803030106021506 64
    0x1040412007207050880d14065a44e20b110b401c02406480c8540900442c00790b4425001044110b440214130101100c90300c003100e030140b01c9912400114144140810003e10103441c0000e83c0010100585090241074100000e40354402c1c420030210420039410003440b0707080700100d0280524414005009400d00d41070740c08e4500c00c040741c1240d80074860701c1920065640100481c06480580f004035000b0b42051000b079106800800000440881c454441044140c015000d549816500141681e052802420301c0780078005088048030312240030311140c002148942c14040a551400749003002149028201c58880e40018640344030a036000204503107064080c1c100803071045030500300000b020656500544611411020440400076550301c002071a404c01c549407081c82c511003401303044848007109000440c1d8001010004091074210760707803010a0b00141100d1800c0382d90ba0f6204082445a404200c1a0f4030104c010300036140c05105100380741600d20524496440e0060001d04a070f20fa000900404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 969593210 1250 969591960 969592007
    0x81801091406220b2701080423120a0c06061406120c040b0a030618050603072702070f150c053019110f040e06010216030b04021002030901 61
    0x244030011400c40041402c8094140c803070424090002240008228a917100e507140f5440ca05250700808002e4015034020000548540741170402410041c4100c1d2110035900c10341083d400e200c4100c0000388029070490751001c901c41303010720704003041d1112074001060144803010013a45030340303424081d141244c406001210194a484600c12118469504a24540c0400042e035025880d0103821000c11201220803144038816144290801c51b0340c2524199819045003000700b0554000700c80072800a0760503c142d1050240800d06101240d004000480b9885000c1c2c1e1080284000c1110039240c2d0700e4250070502418204a030700400d5817142c00101554021380040c010000c4101032808a41848415400e052078202003420300103040c122110310030010705005108840d10074100984544405402c0600d08290030228002c14400e40141114114803d001090a010300002c3c81c20008500480c107100381e034200360042c404030421034406074042d50f00400903d00c0c582da10502032502c118410000014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 969594460 1250 969593210 969593257
    0x3020c1b01090b160c0e130b07090e01030605062e030507170703320412110607050712090501020a260c100b0108100902030a09081801091406 62
    0x1c44110b9a00245401d40000c2500c041c0910584940d8028600600d1030102080c1e942c040400300c00300459040b40e00341400b400d0340000490014140390003851a040402c441a12140e21784040724003640f068403403a442e01e05100d003074100000210101c60010515409685503031602419408000303410008040c1c0e660001000c442c03043e501e00b4000e040c424100c0001d41000c0380d0040140c2120596031038054101810401112444030401d04c50f101c00002011455441d600c9021048010900c071000340030144200710f40c103400c1440311718410a015150243c07a005142484501140b02100e01c00070300c2441c810a2019130380000c1c0d042c502c1a13004506900031142c00304028401200c0305a02200c035600451643c03542a000b0841d4030080c580003000b002043c1c80034004590558090b5052000300c24038500a000c0c50072550003c56001c0d04002002c540d003407a0b0b80e11580c00d50b214001a403040c80c890f000381a490340e0f1142c6100001c060040303107840e075032441c000000c213680300342600d09445480c091107105 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 969595710 1250 969594460 969594467
    0x20c09040b060301090816050c030f0a1403090a320a090906152702070314030c090604030b0f180c061305040c090302030d0306140d0f0611041503020c1b01 68
    0x6000550000c3c6c030980b1100e06c00c0c885050000b102e0011501030048241c01301c02800c0c0020740ba0141a00706005144e001070316100c022220300d01541c07101c42c0780810859000b00e9221039220038010301146000301302500621034050891a41400c240303400d1013130340d01203680c43c0d034070341f18280141d41d0040000200700707846142c18002130401c007104451b9a40c1000c00011200da20000041083d101e2420341e07044912411500c800720721510300000c0102d607010003418484d111500113141d10842882600d840c08458100207078843d00582d2003240c807200c2000c1000040a41d1411194104004040f50000048003100541c0c40d0052030115500030f40000c03d4041c0f44e2111810410300500003e0401c001c03420f2150001040c8081c030340020b81c0603216030a1400b4285220784a10011a0070700510300410018102c00c02800e12561501a41c440e000c5580705000306000b441540090b00d04002e41640c1c40b03240100c050810700e205105c04e41030600c18402d452003000b0114070a0440c6184021903c42d981101e401607 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 969596960 1250 969595710 969595721
    0x70807050909031e091816030b01021e031308010b0102060105040b04020d11070b0606070c0513020403060c200a1e020a0e010b0a02070f050105190201330501020c09040b060301 77
    0x12154030b1390080c0c59050032000c03c0000c100d00d20090300c410f85810f540d4600d24808401c10784040c00e14480c0d214141e80414400d50144a07101030501c19260800400200411100c0c44a84a000543c000140d030314001c0905e42d503804000d01782900284408a0070700c00107911100c0504c1114021510f40c625140c4686e1662b046650403125004c0400081c035090322505400d0700b0904003101c10302001e46c04609585001c000740c811181c1d0101e01c0414250808042c4004505402d21314032059400303100210000d00980620000c112141d62003050b01d4000d03040c040545500c1a000d040c0e2500728211207408900c44040814400300040c50740c211503505407000c0b80c0300103015403081850200950000c17441040040050014100d9071782112051600c5050b4210750040500c5404c1c003154040001680404202c2084e66040400d4000080c0c039007085001800840034140076540c92140c0303041450420021034510b00007408087c40100a80554440071441092001d0700c0078003c400d0381c00010346c41791303000d4004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 969598210 1250 969596960 969596977
    0x30d1101150603050f1f0b0d110c0d091505090409020303040b1215180103140703060e0d080c13060c051c08090606182e0b130807080705090903 63
    0x40400c1e07aa5200c10041c0140f0b029a1021302d4074202c003000c00e00040c0c00c1d002103440707002403441c80f04055252074240c21156000d40b42c1f55205907183d84100c0151490130014041e03120145000d0b140c00840c0c07140007004511607800940c0b407000785000d211ba91a5018055a080000c281e40019010505000080c03850003141d0024003801070000c0c2d09851b5400d65110180242400d40c14980240c0241041040da21101c0c0301241085a130703800101f012070403042c44414000200f5060760001920390b112882902e485400c0c841d6994000001a08920707030011500b54030400c01c661090501c40c0d141d5032252641d90611404041100c0c2810000a0000c140112602a000313a016442d00001420014180540448001c0810b0040e0000140c40c1c0c01d1101c05038807490b010003440b14041e81d034911000c66200ea0b800080f403010707050710512402d1703000f01500d41003d44012070310103440702d4039042d481f003850049800040481c0c02c050b400b04400000042c9407410b9680072120b0041365656040c4140c51801134446 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 969599460 1250 969598210 969598241
    0x2011104140a030507151202191202090d061a01091a130e01060c061113030602031302090112060b030714042d0e0d020a11120a050a0305041e05030d1101 67
    0xc0000701c420240401c000342013011f4035204110380e48404d620040f4000c1d000114010440c0113000e41c9402c1c402c58045026a402e0800103090894135404641d040d9030040c812140740703a076034202811443d01000b50985c007800900c0d101607201e080c45403100781e140b0041d1100c0074249010415522121201d510600a0201b10342c5188440da503d4a00400054079100d0503544d00c4d01d0030907100c0e07011088800b102c000142500c46006c3c072925540e160002540014404071900c011035007801d005a9841e600507000388039440700c400d06c0c5009400d01400f10707480003181c5d500c81e5010750400c20040c5903100c004290540200c030001424205201030b52111403040039007030b10705500c140007080e0a100e00e07072110304481c49510854000c04800300b002e0b84d484105030000790250300040080c103500d2803e465884003000c04201510a0001b042d80d07014135201d004481280400ca000c1418403440340c00b803c03248404032001c800981700e2850038000c0303501e03001c483c040c05080003192001d04500072400d40000b188001c0b04071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 969600710 1250 969599460 969599473
    0xa09052d010f1208031314030f0304060501080d02120d02070209090d03050702010c02030f0d0b0612150a061209141f050f1005011101111b0c0102011104140a0305 71
    0x10324500342840d007401805011214500e01144144450f0f42400c2c200f980f0002c460f10b151280740310035400b090409421210845c850507042108142403024107864182043c1e540c0c0c40e400c1500c4c1c40c00503210160481d074000d0340f00c940c91540b030782d80c002142116004c10b404066540d040100d410b102a00c82d080000e90019a01003e010040d1400245070007100312039031b0f041140740c036026000c80c261000009080e006074003e10200d1003004d014802408010440440010946000c00106503076806c0005c0608141c0111800c103d408400c3c81281d102d5a07004681d0300b54440e0070300300d000d08110b20740a0034104642d0ba07100300c2001c00030881501c45110600d001180d0b126202d0a10b180515100001c2ca00c41483c00c1001155500c420001824001c0007503122000000d0300780350045030307003d800d566100140c0d034a8068529105440c10000e11104054550803440c803040d03441054500200c804041c1d04580c5000c60200750700c60b000e81030312309682080074243d00316003c0b06c0004940c40e86a8001401500905 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 969601960 1250 969600710 969600781
    0x3030c0c090c09191d370c0801030c0f05010f1b061406030d0c0b04170409020429280201021b0d030c0f0c03080a09060f1a0604050a0905 60
    0x20b88998211050745e40c0000b40745113840720750341284c1000d0303480c01d0040040070600107003084174000c0b1290011640300e001c540004003103404010340d056080601c0c041101100140706001600d0840c1020306426145400034a1410000030000e0303200003040010808010040294215140110f61000d60801018020045603450203401407109036051303442171103850000c450307460041c1150505113410000341e03401c0c0d588980311194003800b18100580a4581000082078241541c4041c1000d032180c8100e9507940382415004195944c01c00d1007040c4001014441e5480c541090610901204584100c900ea4680e440109070301901071a094050540f0b900c8400d40d001071000500b075041e42182d5a010300014117007031016200500f0900300700c00020805000c210201c0c0c041c1401c00e070000c8040c800040c510300b9a071503543c11940030490109800b6202d445044024078400380441034800116100c920746490725000409810b1a0712407031030300c5600c030303400900c455050b500503005140c480f043c5905480000f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 969603210 1250 969601960 969601999
    0x20d020d060513110409230702070306050703020c06061e04020d09050714060a0305040203160e04060e06070f080604020912062505070308090c1002011a03030c0c090c09 74
    0x150041c54000e5000d0304422800c2030b12805504c2c014590b10800030301e09820450800050060380442010003903000da1888602c0103045d00c2c591107900e065001d05402815841c103070303060b10070242441040600501809081c10404613026400c502308894080d0000d0b0440e10007410b1034901c4060b190f00078804188540080100e0b08400750135840752080d52403a645400f602291029100311641d0010310034032200311224080c4e808190824001001c0710900c81149010f00c16001050b04003000101101090104010b002e001c2c0b1b94100c05103001800c1c0074070384131034010702a45442c100740c0100020a00401c3c7c040c2c17030b51703412221540005001710507001c50080101d941d400040e10400002c3c1300c01c07940d0b46855072420345404126051a5916032130503505480c1200c4c00800640075003018012890301e08216501c00a0580f110901c1d5000030450314418180c405405107080340c5140a038000700191008080041510a1683c02c2101c580ca56503d030081c1100c0e441c0038a00c8800c4d00709001c482d451400103072 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 969604316 1106 969603210 969603221
    0xf11041e08010f0b120a021c030504050a0f060807030204030308160201180b06010f0c02090a0e0a0501290f0307030201030b030a0b130209060d0c120204020d020d 71
    0x446010107400c459103410b00440c0c0795620044d00f440390404500ba44000c03451040641004a42d44c4c01180c40045000c01c1120240d10818481041500030010b40c3c010301005000010119201d10407500c07881303640e004031408180c8510010722414804c0c000c55081d01e61554a80419403254000d002440d0710a46003441555201c001550380526070101190445028a0000c4040d040640c0050040340c281400308042040d01c54041f005616640a0607422845622001980700c8006d40400c5c00d00c0714030740c40203100c1d5003003039440d00e120048424580f94a0350340c1407004c0080b5602c0020440c091080e214040e800d41c00c28281000958060380c001613460ba000340545d140d5a2295652541d103071002c0f05c3c000d09a0740d052003140154144143c0d01e6602c860143c0700b4207130304480354450382c0d8100780c14030a4610a840c401055801c40d200c036019580c8941c0e50b62825903d802d03425000703401400 = true := by decide +kernel

theorem cover : BRFrame.Cov 969424460 969604316 := by
  have h0 := BRFrame.cov_init 969424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 969424460 ≤ n) (h2 : n < 969604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
