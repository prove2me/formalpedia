-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4212
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:53:57.026319+00:00
-- url     : https://prove2.me/submissions/cfff623b-1b21-496b-9dbb-3eac68bb5ae7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 757374100 ≤ n < 757553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 757375350 1250 757374100 757374131
    0x2071809020301110d15081e120f030403141303200d050706020106140a1a071b0e16080403030c090b03040c060e090403080c0d0608032701030218090a 66
    0x141322540e50b00b40990703a400780001040444507044407501d2040c0e01040d060046990001e4146480c590001d840c400002d0000c00891800c14280c840c0800c09d0004285058295a183c000d94001c61003902d5001c100c0c2c075400e0070311015002c1c2c0c0700f59510721100083c041021452195010301c00540f901300b010149000e1002181c400600b1440854459101d10b608200081d4280300d2203000d844c0c2e906404617004045000903030101c0542c02500282d40217804110150a601011204031130781c000c080405201a03031154001250607031003015201c0198000050008800e100d070a6910304841d110441141c840340c804030028040d1082400a1229001012990f0f902c010041c40c0b181b8860791078982c045d42821401040e02003151409400f4220071014330000076004012240c3c01509041e91a80b81e0880c1c03514140940f590b07900c240039501002501d00103080740d0f100300c1d104400701111002100d90700b4100440807032003042e50201345440d510901d4141841c2c000020754110703041c080c001c2000c0e503200d000b21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 757376600 1250 757375350 757375361
    0x140105040f110d03050343030c0c03021507051e03090d081308030c12090615060406090b03060a03060c170604060f09092604032102071809020301 64
    0x5070340c2110841e0040041049803120040200010b0310280020401554050540e001c090484807400c84804400162028a080700350ba8250008201500704014041c00c00c1c110400860320400003418110780d614800d001f43c0c61144815855070081c854460035100600d61103602504074010010708104800022001c0d40d01031035a112641e00d0741f6aa81041c0101602d0010307007050210034004002d0411201c81699025507019a8000003015504c0d9039511054130280300b003402c2c100f01d0300d0100c1c023403000c0004c00050051050b82180c14020b0380d108484204506405a403156a0000d1000d10081c001028024003840e088000644003a09054a0b55075000035151114010000680300c0d015807066160031000281d042102918100a00740c24240701e003081c0c0406000f0b0800040e211416031081045c445155481c00703200e00401d0810003014042e18901e580076100607a23142829110601c50408000340c0702d8244a0719030014a070a03403400030341400900d08440c2ca8804243d6850104000d40c40c00c0c080c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 757377850 1250 757376600 757376603
    0x307050c0a1424040503120408160f03020c010e0901060e121015090b0102070b300a0b03030918101a0406030c020a02012007051507050c180109020714010504 69
    0x949004480b840c041c1100d4a0900260b15003d0094018071011840c04000c0300c46040181844c11007540e40c0c1d0614942138841c40003a907000300303040e00e0000107011009207034904507440380e030a030707080340b45002c004692800c80719000302d520440400040140f680900400c480020001d0081c10450340d079484101d00700121171304c400b00341c3c0c1d84a002003a2901100d0a226010b4022240704001141c18800000e42d01d440302e000b00071482e01c0c0000c40c030445807202d101e2052680c0703da0054004050710203083c6500308006840241e240c034100f06000c500c40c60040180d6665910140140050030049140d401e2107001c0a0f000c0700c913030703c5400001f007164030300e090548c100040340001090b603413440c051000f4101c82403441d85c0404c54201c28101d10041c5c0c1d10040303000c0c011078500c11301c910031450100c400d800c080e0b169102c2940180b011840194100b201d102a0640314024001c0d104c0000f0040c091280ca00320040203002c0000d0550014000b100300e9501422003030f0b0040b03407955100d6080c029000c2c01c4541c00d940 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 757379100 1250 757377850 757377853
    0x140103180809090601080106020a080a1407030908010f2009010c0206040e070906080f0a0c051902070f0b0f0a051602040c020a0204290105220315050a020306060307050c0a14 76
    0x28001110308003003d038241c0101c0c1c2031a00407240d600d0000029243c0f00b400034001c289201c001441c0c1c2c3c1e15031190091074500c52800800c03655601151901600c0341107284500b45403542070000700c0c0031b903907201c1c07103150901754912515407140466851a030300d0a41c400e402d050705100c0c11000010141e02c0d0070010344003601c039445068850782800700001d0321003945076105108108543c1d081212071100886000d4200050300340218a1440480040e40c040c0034100000c01582404801240055400505d000403501d07001004072105441c0c81034100c491041a4161000c20000c00c01125002d10540041055202c01e03a001d140300b04455000406032070341c9030404001680814803040c1985418800c040468401942d2404c00b01440c8030301c6411420303140012414400045008c00d09e41100392040c19810082c6160000c04a4881c905046521021701e45082003034035210000314544994822203019540090806045603540c4000711034070b80c45035000d0450341c00b411030b41100043c2145900800c0150600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 757380350 1250 757379100 757379107
    0x5010308030a0b0618012105090102090a080a0209040219091517160b0a0203040f0b07050d0f12020319050406051906120201031d12070209060d03091401031808 70
    0x14288001e41c0d0f041440584640d0041215000040301c102d90381c04001000e0810101c03800e03882d100ca07110901003051041031700d8145802c006900106600908400200f00d40954601e81c8805640b552020b8100c0000d400169010100d070141c548092407000c4000d04800c1044000d445503410300c1035a42013200758002c1054002c00341f103184841d600d80008036001500401000300b030466008800ca01d103203e1031010f88400035a09983e07500c24802c0700d01031308514100010b190303607070301e0325246070b03406048295128090110390907a030a02c6030340030411362016961181075081030303100854020b43c0082e0080441900c030000128500180e4040e5510035070107000001854a400300344241010141c41d103100000d454540188610195004028109502842d0000e40031001200c8240f500d1100e040d0a403061150403607910f254285140104091071080c0c80c0410107403034000500042d50280c0c800140810107801d018080070345c1140e01d0300480310051602042d162210404032003840c0840300152801e84001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 757381600 1250 757380350 757380361
    0x2606030f2b0302090f06180909061b070308150409140a0c080c0d06021812030a140901081801061e05090601080f1501181509081606030b04020d0501030803 68
    0x60100c00e0007001030a05601d01411000042c480345200000c0da80306040104414142c080b250201e40b8042401818590080c1003040c0000d9903580d084a0072551aa10b070505942c10f410380b07506880302641e058035900c081d0b0705d41421600c50040c6511030160400e68411503200403800f04541c20255903501005002e00d20013506048036100b48a070001500743d40603018881c03036500c810300800c04064004a00603103440c83c3c010b900c09107a1001e603510740d006944d0801c00c820386201200800e41c108050300d6990419510204a80d0030f8054142e030745020500090001c2c0355440e01101178003840780600c0000540d1915045400359a080c001c1504200d0822451b040c8143c0c10f141403e90340040017400c11f02d00c40c1c58015410700c66042c00601e40c003000c0410115aa10a90240b00080904c82c900c00c0c101d840070743c0f140201041c500d9410b840d10000351410500140440c5c010508a400f4687d641e560180107042a0084d0082e01c04640e0350740d0826820003080405840512803280a54032a03040180d80c0c0c01c14 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 757382850 1250 757381600 757381663
    0x80c120703051008070b0a05030406020705030a02030c060a09020d030c051002030a0605040e011401180e0714040c081005041a090a0b12011109210d0503070306062606030f 75
    0xc0c0d08035138913070b80c840502882020400c4068550a41c441c1c9000c603503aa9a507d8580003a0040100041480c400810710920a41e008009000d5a603131100450b800b0b5510242c089003603a20911307010303402107198900e40c000f003403056801002c9980074008480303080c0c0c10300f50010121b9004071762402c107590b40d4980502c88c91625020b0311406031410402440021440100042100b20601c240d01e4240c51250194056402640000130510b61120559018a5903600180c0703088540c0b00040b44120b2428194981c02400f4001c00750141c07041014880a903030800051200070000080a80500b9010700128000c1c2d64504140510030103c886c0b0110f00c0c0b40c1d01c0d40034002940381001c10000c6c96410680d40410b8910b080f016621440011105018034054448114045031901c80188085028003614030a00d02d412000650155465950810280d03aa55070300300c90804031000b03000728001c0d01c803034003940c6d5403c1207900b590441c0700241514038440e000410180340c0074007199800c0c10303402d0540c003441d8030544 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 757384100 1250 757382850 757382881
    0xb1008010501030510151703130b0c060106050a03090204180303060b0a0516020d02373c030302100c03020c0a150b040213090b010e010f080c12070305 66
    0x48040080c82254195513460303455140c60485800d2850782c40780030310013224507503440f003000b484e442e921070148203030b0018800e8596000e1030f41c900311644020300c0001c40c0081c460072103a5082d03a2501508d926400c0900c101ea450340030500282c105600d822408003d0b9580780705011050b01c461010780700c0d0021520300502035030801d90011104400078003842e1580e54010040b154034260703054440814507d280f00085003a442d43c074029404c00d13110b8080c06620020b50619151070140c142e845507010b400104280c100c917100d4002c40d01c000300102103102d1420031500c1d081e10602101041e603040f4443e9041420018401d550046d401a4044050949414118480ca510850581c60b00b540391107400900c940d40c951000000500d0326891440940c516901c5a01c05445d181005106556502208124600b07440860041c880030038541002c544043d801034200150105040e11400c840e01c000b0401903400b80c000508071441400c04000c200f6500040418051103211551000183c6003841d40e5032007080392 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 757385350 1250 757384100 757384109
    0x7051008011a16060e060604110406050f070507080f1b0a0f0e1902030a0906060b0702180411100908010b09090618190b07080a090b13110d0b10 63
    0x2080300500c00701d032110315030309180001c0492031030b0744001d08600344020034580100134250620b08062281c1150001c109076016601c01c030740034000070702050080c00703451107140704030703c0802c5e02080301c0605605680c0281034500c0c00303541603420b1240d81e0741c072460500e1403104140b07503075410854003181d4002910403203200c092016101c06603050300744400b43d4030642960080d0320040c204400001c2c01ca40240d014908071642c2c42000755142c1c10071100b0b80014060800c8121a407508005011a05150f00c900b5100301e81e400a0000804400002d117400da890b1011301306441300034400000704902c2c0c5030314000e9541c5000a43d074125015117014441801c5034090405244980d02210034030440090001d032054110321078001100b0403440e26007405103000201d00500542d03205080860050018a81d001489603541c0e440300c00040e82da42c88000c046540d4150001d2604411401040650401004061100744142e038070441c0100c8c0c0000246004840b00400c0341c00d0603002c030070440d071450207010810090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 757386600 1250 757385350 757385357
    0x403080108210f0706060303020f0d02120702010e0604030602210105040e0c010e010309050f060f070912030c022b0302120901171b0703020606040b06040b0d0c140a02070510 76
    0xc1d8140007016410a81169940344000306030320100c3d81c1c1e00801c039103846a1040041200c1d070768134900651610b4000812254a0050040c04d041c02400801d00000138100c00344200c0c5001c01c0c030342c0195003100703100d4001904490280008400140c5134802000340502e004842102964800103001c8403101c140c00280c0154181038507601c500f01c0c00a00c41e02e0886017400d104000300c1c1000012402064000e001a205200c1d140e0b242e805c5910100b54540204021880f0902c950703550502954000030501c00d0715001607001100c000813a20400540700024401003500710304d0440c85480304020030b0b090070f100c4091380621028800301a010025800d4161028081c241411400780028115003458826048460308900c00500c01c1140300d66102d800781841c1c21265215419410b00a5980c14200c1d000e502075450140c640c1103511301441581c0865011034134042c5070038003007450383c0f001d07182800000c1c00340250903d11031071210102c000b50092110640c020003131b192034203040000603c004118039060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 757387850 1250 757386600 757386613
    0xc05040b01210b0d0615060e0604030b0406110d0b19051e0609090405030403050105011a042304110a090e0f0739020306062b0203010f0608060403080108 67
    0x403660802c40800003150003003000d02c920411040e80801803c03803104901c0c0e1000038030b90148100181d03035120020b441407004076034294a07198075060707030500d043c50781d85907100e10f007403004000042c10030206c0c0e80d0013403044402245a04d1800a045403a030801001e941d041902e9070718200313460401384440500b883c28559074204803841c01c004149001400c40742c9c40f0302c0303514000808400351515030031207007034000c00b0304050304901d403504140d900c83d0440d0004642e40d5081000024600c5102c1145000825103c511b007440c2610386a002c17807401004480600341034490030300130b0400d580ca0740304142d00040015020342d40c510781241e0003024005260004920880d40707005020b040181c00e030040750700040a0906450809040401102091070541000d03c0112001c112003001016580024032140c4250211201034035000c1c1006424585000720805c8084844c4403181a02e05d03030b41c0140c02c858005000001c403458021029001d80da0b0326000404250700c2942808101540311008500410340c81000d480d9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 757389100 1250 757387850 757387871
    0x1b0e06130c080a090303060f0b0c07080d020d0503091f06090c0311070305070510062c0712200d020405010f140901030b180703141008190503040806130c0504 69
    0x202d038005044031039507680e94004942054003c0d80980042d0003a00b60701c0d080c2d80d54803181c41d041c6600c0030000d2041c0740100440024840d01c0003883c002070034500e40280020103c0c52100700c40c0390700020101607141c480ea00f03404900d000c4020100c01071108005010071081c0c10441c112054034a0030a0003001c0510b404021400400719609850580743c2c140382c140c6da69120741c10500c2c60045610b09010b001031904200080c986200071056440311203641025036480b09844081280707540849020340400c00d4445038004600095108100462002c4a244086141c82443d24600e4000a620303004244e400201400780c4c0d070f000101c0038101041c0d4500300380c0341c0303d584882d420175005040e0514181615410400c42599840c80106600e0b801880485c0780c900d070040c401809031141240c18000361100d4404148400b45007484041a11840001081618a0254413000700280b2000544543c002803201160900050040c02e00030400c40c429880380390f580c2e0030b0090300b41c1e160350f00141c4607a140444201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 757390350 1250 757389100 757389107
    0x4120e0d05060f25020a0c090b0d063305120c0612130f0b100b031005130b06120714191206051021020708161b0e06130c 53
    0x60f802104860401420b850b61041c07200c42d02480c130050107801e0074900504041c1c42e4005000c44445c0d000b1a680740d202942e50a42504440c024001d041e0000c81d0511500007003113480e00b0010745c070307a01040c20b8408a0781003070341c01c1803030b0003055400002801d08440c100030503d010305403c00203c501c08003415040843c00e001030068814204807081c0d0f0301181d8000b1750a201d9130320380409216045031144101080324941907080c00b0303044a0b42d81502a01c5540890584926000d582c8644250042c01000341c1c00c0c0000c010700a44c600f003100310800d03224402c1e541181c44503005011983d0f452030718207108d420500800383c80c0000032044608400401d014480406000000c1030a43c480c0340d090004030107002c43d4800c4094040d54001c16044031021002400f42e0707500840e5214079040b411031174410942079100b914180d10039000042c00e40002804001c040ea003e066020029030b00c5003940000403c11540c001039000040c1c0d00c13640709100000e0401c40c41e0f05140042d2281e00018113410000205101c2c0c02a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 757391600 1250 757390350 757390363
    0x14011d040b040f0819120b1c05072315070f0b06120d0504140607050a23060a05010e0903070c03121112090102010b01020f0a032604120e0d05 62
    0xa0580d600001c0880c0610400d035122180303558011080350383d40e0100c000803580690710318440400060356207512510700c0846104090002d0001420301101c40342d0103607440385030704003503009441600601d240000e00f00d80da10005001c991080802640b081a007004001c164040300c9881d000c0c5500401c080c10009408102c9a11282d901600c1ca51003034036200089460740440189100192003617842d05191650044042c201700d42080582500503140c8100348802401660401021648450305050018040e4070300c8406910081098036074610200d4207061a081080c0c030b41c01041662072005000c5040306110540d072184004005515007225607483e0840781d00325200240030001240300080501c1d2203034205800081061040303031b41039000d4810301141c030f80c441110540075601c0e15600002950021509071009400c2002a04c000e0140e503c2c1542e42c1c5001c455484601d02d05020300403078002001c50514000e130f010304070301f0b181d4a240d1030001d065801301354103040c418548108410f0005400041e803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 757392850 1250 757391600 757391603
    0x9101e14130602250303090c12034107020301050c1801031a0d05070f08010509030313060f0204080102030f0f06061803030c06190c0e130218031014011d04 68
    0x1130b51100c1400303454100c02441c8102d90700c402c100b0301109003803603895000040450702441003105420740d03035040140141030501c00180802e902c806203828409249482c9070070000e40f16105501c035943c8000c400c0c17510810400b0074100500100c2c03c030003942000d210302d43e44640d90300c0710320b45003405019071441d07030038495030400e0304154680900e290601a10346c641107080714041d166620740c42c1c02d07241c119101e6070180500e12181c41080c0c80040c02c0c1905000311030050100c00b018524589480301c00800009203080c0a85000f501c5c0c0d24811241c0c040e5100800003086208001a1030703091611001c8500d42e00030701b5262609110780700b400308999036042141c0d0000480d0014281c1904600003013801c1d4001c2a000c003a10f4040d040400c182400c199480000c05607420408002048850784c050710307911120348006402c02c10f03050b0640c903001810750045c5614400ca80045480480f0000040e2801840c0f001400701b164903054402c482d80260300665016101c16080043ca0700810007682c6151440180f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 757394100 1250 757392850 757392863
    0xf1002070c05040e070e0112031d0109051c0b0408040e070903020307053d1106100605070203150705040f050105030609060f0604092a03090c0e09101e1413 68
    0x41184da000401030103004001c46103800c2904c1da90348016814451101605178041024242c3e0040d6a00924003007800010301611000d242c14188030074420701048106180007241c4a5048140114042200707240c8507520642103580d4445c00c205501c000000c0140130001072140043c0203000690740885c922081d40c034140d440d40c7d080a080744d80f0030641850304c01c08804500c420540c0c5a030011002e501c8200320036035600c03101c480a070081c0c01c0707641e01c100845c0c01104280300c954017440301500c91001010a240014202d8030300d407040c0501508202000c0d1008004600006420005041036006050050109080150031460840701255a0ba07800602403442010480100d10480d41d0725802d841c0034000071402000300703c54280541d40b0029a203c18419100030b0456510055807090182090780e035804400503a00b18603004da9413402c1000070388408018020219480681e40840c40380d4410f94102c4084d0000c03061040c00007900701e401c0d00150445a21556040103005a11a00b840d500640e2161 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 757395350 1250 757394100 757394111
    0x1203070c170111040b090307050117010e07140d09020f01020a03020c190b121509060d0f02030f1603021801081902060f03040602070501050c041d130c03050f1002070c0504 75
    0x950300c0c1d004240324854507a440402083c0803030801c0b440801740c206c0d9041942102c0c0010b17140e40c015034420304e900c1004e00304003450030010311040607294503a54206070136090100000002c0c4100c0c1081c1c7d040300141161040d80e40d2080401d5240100265032a607200b8000703081855460345009441f5a10124428056aa40d841a80c0801000d001c110700920116000f5030311448044081d511006c000d40e840d040224201d91207007058645840c40a0090800900c500c08841c001d40c0e4201440b0303d00e41090f40c1c980140072014803080000d101410f01d5910704100505000c0c07c510401c9108803d003c0d0144044e10800c0040c8244000028284600035841702c031451b00304880e01c0000d10900c920180490201004070521081100301c1d006440b0b22441013000384040d95407400c1c000140d00440c80b544502c0c0d11200103516141c101c80c0e00c15034120b104040003507800801d82d11030802d8150385d5070040b0749507031049072540f1f00b000f4240900480c110901809510300340882d1520003200145010f0907114556a4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 757396600 1250 757395350 757395389
    0x20d091b3c0305120c0c06090f041d01020307021f140712020705151602060403080601030f06030501050405060402010f090b0921011b0e030703200d06020d050103021203070c 76
    0x110079260046601908481c030500e1202c041d04c5140d00110170000261242480790800ba184c040203039100386801509660180c1c0301c000410018001420b01c004e04070001e4064036080a000303000542c4a040c01d80c000304448410710f892001e481034400749081c0d4851520468405800c0000100383c0c20080e20700d40120b480035101c0d4560024468884003e2007840780d40b48462000104d207111a21502c25000801a1071404450580c1c035032404450090001c0c2d6150300140a40d0700079070044404a4403240c0004141d503c175920a42107031000d540c10ba520307034811002c0004641e4000d0980640701c0552511407140c514001d40080b850041d81c8410b4030801d20b96030680746a882001d1200c07050710750580203024844205000001459024514100140d44a1181c07401e0741000515041207a500141e00e0711901208440310841c41002e80d07001d64001c81084200c2d01050302400940400e0141d41c90020f16949181b04105003214480c0c02d942c0180c100307200714000315017070050903400c03038020382407148103520320 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 757397850 1250 757396600 757396709
    0xa0905030c03040801061401080403090e0916030b0133123e0406080a0c031404140d09030b04060b010e150c010507031506030b0103020d091b 62
    0x8074801200244408900000c2d40c2c541504818100c07411501d01c404101202e000440322080226070180100740c034600708110302d207401d00e400c135404960340e000d8460740c0300442052141d00c074040c0d0083d11708610000c010702071001254244072041803040381001660310700595941d4400200c100304c000740200105d09901d081e1154011a401448c10314075902e0700c0b981000c0c1c1d6040300d0344140c09034035904074807100c9540e00901300342101e0640341203031104c40c0303265201c2c0440d01c050300c00820254201920380034089102490483c02d10b00036807080d10b028580c0e402e240761051400041240300d504005000f0380070804240c00005154202c0d40000380815427114071001684c2d0001d500c2d0000d5000203024205807420f00f50207018020f4020003100038042522445002c42c1130b03071b2241c51001c8454046520811015029078460406504181005400e08250785a44802c41e0f000031030680d0405208840850a00f115801709400380907051141c0664003013841d5003090000c221658400025100f11a48903d03411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 757399100 1250 757397850 757397857
    0xf060e0112050601050d02030405030711040b031504170a09080d1b0b091c03090510090201021f1103040812060d0c1e0803030907080d08190b040b04151a070206030a090503 75
    0x5141c00656480c03c9c40e00d400c50303590f4820311054600111140c2c12880601d001d0240e580c201a0040007012a0300c003030800880d0080000d40215400c112440c44004803150a0010340010156921002901c03031501620170f081048070003d04041081c035868010481262084810441380c22080b40810742d075401d1744140c90000d545180c002405100c020462020f640758002c0c600e481d11810a4032a104241031403032054418200000340540c1080c00769002450011443c420080210000820005088030340c5e00301691054405946c0548005090440841e0405155030000001e6900707200041094651010921950042c0107040054251120032001326101c45006031000c64280c070303564200011003070f6a81549226804190141910406049000702d181174805c55489440b08540312261210f030b0001c2c9404004164410765814206085d9113591103075602c03036440350140e0382c901418240c450402018550003184800400c001040050325a03400792070b005040340b10081031960082c5041400c42c003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 757400350 1250 757399100 757399117
    0x42306010b180405040b010518040c03020603072309090f1315020f0409060f0b0403170d060806090a03020c0a0b0f0307050f0c03040e010509070f23130f060e011205060105 75
    0x18141800c2c0b001b1300114000c06812544112034201954043c100c0c88201a20112800b6003401075402e400c00150a00710020341d40800e10703160081540c035400c41c60901d1920044003c60400c00c1c0414000b04904020000c0340d08001d07820402c0c601c1740382016510103140e00800780140700740d411202c0c2d1145000150103407000c48065001540d10749454151000c0209600d11521080e14294000021070740381e85421a07091b80e030090780c2c0310950010302c0b040c1540c0d80e0100442e002c2860b500e5000103a491014421180103605000c0900340c0381416080007441e007080788000b10700c20015003808124055440301203594070247d1b0500b40b5140e50310480150340a01540320301e04401100001c0f08482d03800080014801e585d010080304807103988402c188011403000720780ca01b001c40e440b854130501d41405a088800360030381844090201190200384c028203500318060a00640718034201c01d11150500c500207034054501858906190554000000c1c01d495021149180755595140480c810b80d10910444800701e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 757401600 1250 757400350 757400359
    0x6100519050c0c221e0e030a03062103181a1c0b0a030807020310020c070611160e33030606091b09030a0f050105042306010b18 56
    0x11a080c00c405081640400b2441c02c890045850028440c03801d036805080c0c40a09808007030180303901c000a203009254035105080e130240451807645070445c0714000c02c1c1c0c0c2c403a81c50001d1610b520340b403038024056410039000165100d500351000c0606c106000d940c1214a6051320b011400b03180310880d8400708102d103400854244809140c103040c00959407005005245050b044074003030254440c085000c944101800315800740e55640f0802c0031a42a102030414a40000c3c15910904d106c460340d03800300d80c00343c6031400c001d41002d103040008940000c03054000303901e11400381030b080c03540740d5442c0210501801148a4161840003051004001d04107003204e0070701d2102c5291313028401c41201e0f62400f0420703040742c2c800d00c18440024017504115044901414030104140c140900c120750310310352500724611140e00340c0306007840c80380450155030301400818041d2000107410309060030301d41426078070941c200000109081403410354003000500309044404250400703488030105000c0040100202c121607900 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 757402850 1250 757401600 757401637
    0xa020f0c0f031e16020d02060d050703050115021203070f180801060e160917032109010e160608072d030b040e03160201050f0307080708060117061005 66
    0x4074900200034a003840d030544402403900700c8042ea103076180c450008030b28451422000500e00504241580c1d902040c4001d00c0182001c00a0b03a000c4101c50003194030b0320001b49c031a80108107071205211820001d2079a8406003100c40d282c100c9116182c0f001601000401035034642991000307114031400e446242240b0041d52100d0307650554140a03100500441c4682d818100108030032001c0b50486801800064890b40740151400c01000680704030303040d0030b4101c2e0200300980440c50340030400b200d00d0039210044500982c1465020603085500202040700c1ca83c1c00110a200511844440481125043e241c0303010150341b456400c940d809000c000416002543c1c0f00020501c211510380d40c0183c40a82d60100615030020382004103583c080740c42d00c60036030400c2000f0501e40083c81032040c0040e0041c18541d1800009a004c44550342c000c4503031200003032a21040c0240b090b40700907030581104091801d600e8040007403408003482c4a010302150301c40c1034a641041c8140d0b01400586207081da840b5140c645 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 757404100 1250 757402850 757402873
    0x901030f061508060f0f060904030c0c090204090e0d0e010819230604050f0106171003080a230315040e120309070503120705150901140c0702040b0d0305030a020f0c 72
    0x1541c0100f5100d45800c03d009800040301018480c141d0741c4201c8000306028038545130380c2c9040d9040340300302c001039032298003334080403a1381001400184003e0044c554006400c003810038000c1d003004c0074100c142e0200407030042c1120032603a021544c550840009d020704022012018801401018041004107400599402590100b17281c0241c06108410035501803016544e0040c142e200c014090042c2000300d20058420403d40a04c0d22007580d014a410102202280d240c1c4c54295542e040304401e600000d40480301c4003c3c200654054811800b140020141103007011302c0900d846030111940765019656905451400c26410001f8082407015050300c2566810a00303100345d1920042d003d240d001e03100f0f0400340040781c40312400300d840264000010b05840b4880710507258000304003420380c41a0707649600250104040c10303040700703004a0102200540e10a40c2c1e00c188001c1d504501545407003118012070385000f0039005402c403584882444401640c2c0c055181031380c0010701400060300e03c14420200001d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 757405350 1250 757404100 757404103
    0xa0905030604140114040b0a093014030c040302040b060702120715020313030b0903040e070801150f02100203190603080d050606161101050c151006020a020901030f061508 75
    0x840c00016200170303c0246141c0300d01010810301a18014030800036500000e1102595074041c0150750710a6580004400044400301d1504174803010315001e41d00b40c0b00e861110380ea0803400d50074070750082d104a2411454201009000c50095100107030007291034a58042465503950200c512507a4000d2440b04501017210503640c0e0748250b80981c00382600c845003000c1b1000d0002040e1030320b24000d007003c41050b600b5030b82c40428511003d004804540b10500c404101c08140e030042c0342c031801c1141d0b9043d40a40c5410854003122822480e03400c24442c03c03500b0945010b60210703000c031080910401c003580d02e44a00d10a007000002c100030500a2514118010040007440030052203078001000c030038406611034108116a522441411911700345c10300000c1d40001e03251907868a00040705040c0207060451510885042101050301314140394004c10400c5803400ca195000740c050002440140403c480399400300b4403454042c00041c0c0001c682d48248010015107412000007265202c500011803030390340550a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 757406600 1250 757405350 757405373
    0x50a0f081c09030305010819110402070218070e010903120f0e0411071a0105100e06070807061d0d120504020d021206040c05030309090a0b0406091104030213050601050f0a0905030604 80
    0x214006404e18000281140740021100c007105c51000002344200030341c0c1c4d03522003208003100b0340540217a02441103001603a20104122040c0a1000d800000c40c50140e000a0010706900c02c201d06014280e2010f201280b0220451124a4220300b41150220300c8400141d030604000703000d5590103030074041540240c4984d18081c09130035105040780144415003200801d00c1c102e0034040d00e0b80214040d552110303030a2240d000c0301d0905070080d08151501e00680c4808a02d50710020080c0d58040d281c2e60070400405a0300010712050031460301410701580244001403d10103000440d001c141d031200042401e5540d862549030160394010200c00584114011440d01c6010481d0203a501040320170300025141000301c121110000010300a4501d55a1400300f04000c120746401c42e900f09035950360104100b1403d01c94003c8940c2401c01c0c1546691440c8100031078580c00d4450005c0040c01c20040c400940d0f001810b95502d0f8000c1c001c0103498a051404c110703070710541584100c0d41031042005000500c01c568011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 757407850 1250 757406600 757406603
    0x60303020c030c0f010f050d05010e16030506090601180b0406080702070f0e060d150606031a040b09041e1506050103110306031015030203120c011503050a0f081c09 72
    0xa48000d030252800b010b4039440d8160403650040522400c440440d80716461031001e400c52030421074240040e0b00044011280260414504030308008203011181c1c0b001b5083c84010f60440c80c042c44141303456004103e000c0006004c0506014191104202200c6002140c00141c00c4034401d958a440c0d542c1030041403000d05690990141c0140d100100f20148508030030801d81e00f10003900c1087e41c40720400d120502080090503a00038540d07514400801c049402103900810095402042044a45100b46071240c0c540150074031503440d01101c06200d44079440c54130342c4190480a500b4040f03940105515070314038107120091103402e1003058014602c26a50110042d50004c0e6810800c4081d5000c1d095010b11094689a40c50382c000050f082c11102542c21481c0d00c6580781d0346100c03515940b40c0c042843d10b6015905807422003008035400301900d40034440d050700ba46003054440343d218a5a19000c2c1c0b01e1030f40f07400c05005800d5224049052042c10f07021180081100d403403010703607442d022003d1002400710326030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 757409100 1250 757407850 757407853
    0x2d070305090f030403080d0b19050a1d060913050703030809070905011d0c130e06040b0301180807020609180601030c0503060f011815091502010c120b03070e0a06030302 74
    0x441d125080c0054580034049404000f07518044c01c54a80e100c0d00e80140c41d42c8601c65403034200c2c00c1c155807a00340501a02006108a1060b0642494204920303c02590000442141c41d801c0e65501d200000000c1d03504140140c80a4209403640014071080c000503101c05085489400000410154040e40081c4100c000700e050711110b54481800c0700a40e01c0a104000410140508d000300c0d40d041c41d0f00c034a41207070300712500c0b610300603084442012031201c642c000ca190050728000c1100ca4105801503543d895002c50081180480050044c1031b002010400900010300202e08070085441d5241220740c0624000c000d618a5610802c64940c850411240140001d0800302d05180b900e00590a903405000001e08090402554100445140018040e0f0f0b02d500a00307010009000c80d801e480c0c50132070480035518020f010b03080c040c0f192001c0800144c00340442e85014060000d583d4800d4401070401e04040c03002c0b840806140000b454506140c01409003090064103026690015601c010102c030b21980 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 757410350 1250 757409100 757409111
    0x40c0b13061b0b0403110c122b0f05181801090e0c10110307080d05180c060d05090109020307080c040b0f0603010b030702070b0a0c0b0105061806032d0703 68
    0x16070407105442d11140080c101c0e5030502c08100040c3c09082550040d071104000c45281d03035410400116070035060740304100d045d04003101c484028040d0000c05a9070710101840800316880907240205140c91055040f000c0000204a107188000000c1c82c0e911a070400420880540e8071a044003580c520080c881c03482c54a01d000e40300d14801c03601141507181101c00810b8440c1092130b000c1c0a90720300b003070225070710140d010800c4041c0025003140f000c0c00e48098205000202d80c5803513040c964503039607144038144503540208202500fa5441d402202d40840000c5c0c3d0110741502c420b003c00303000d003041c56402507143c0204000440c0c40c860020380b0000c00d01b4110b400340320454400c000c0c804000c1e146000b003034020500300010310001e06c0140c001c54004007984100c54503165690b0700050b09030040c00840c00010300c80d40310305041c8801d00028501414040b42c2c10342c80c01990742c04482d00c000120700d07084e008160200003e99010900c01e601c8681851041a030030b5180d848640030080c911044030081d01003813514 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 757411600 1250 757410350 757410377
    0x150203070905040b0a0b0a020102160614060915010e0d02100c2603060405070e0d030203030f072d0201060807090b03010c02010603080304061503021210141608040c0b1306 75
    0x902030010070340c10181c006069071b402c000100001d41d004011140641d9020030112100140b046120b5070703080c1c0990740020382e500005450120036103028050500c5040340c9010310506600c0c07140fa01800240074202408003606803004120303a604640c0c0083d620010186220603565004600d481e401c5100303040c503034100c41c100c40e485d000c02c1c041503005d030313441d14014070024400741001c0d0f02990300300744c0b9414102044040e900019200b21100c0d60f0890042c0c1001c418049001021441181c0240080c10b2141d10b00c400001c42450600c040365412003480c0c0c0d04c044c0028514000c0d8010f078040d062540c29201000e86400685000e480245640f502961030009800010b51040c4078500c20341c0c0c0d100c04014556101e42e00c40c1405070000c1e010829001780d0f802000001079490303141180300180300001800c0c15614041402c41184c1d5201245485030740103504001c941d0f041c06ca00c4024442c05424410b5491304d550a0000606026800c40300300f0a00024880d00100e1200030003900311040c5072348040022044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 757412850 1250 757411600 757411609
    0x3120f0e071e030f0309062d0c0c0e090703021c0c050111120a030515100509150c10090c06030c080c0304480e15030307150203070905 59
    0x200e09000880d0308400d206018004070100030070310040e104803a805200d6266250600c0b01ca070140307070803408566040346c200039403900314132082c80520400b480c0c0241901ca403030214034440c07042d081e00c00c204500b0050400c02c102400ca07180c070141402c03e110b1886440c000c1ea01035070b141c0450200780c0c8501c0a58000510244d00c04590142d450382c400c0301c440c4024500340056400c1c0d11401e4000519014501202c014907003080c000e06296605507801003000d0802d400760040b402d0341d40b0005400b074a0242400f000f080c0c3c100040b501d8900303064400100440080319080e040740105042406079000340400c080095001750071080300c00b4000e101100000f0f54449040e01114540c0306d245e00032800c4200094801e99012000c2c0d40c0c801c0c00391000c41400ca602040000c1c005032890341c82d903000072201c2050609412201c0074411007034020601070160303600300b00354469107450080000a50402c4e005400300c698a041c401e072658594440d402c403001740c403000700c1440a500111600000240300e0340000925151 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 757414100 1250 757412850 757412861
    0x1005100b1801030203101d0601110606180702070e0103120908070e01180b0405191b020c19050603040b041b0506071202031b030c0f061e0615040303120f 67
    0x384540d50207440c041040194081e420080c0140401100301c6400204034078020794401c1d15040c1500b40d1852440c101001600c181d809800c030030103a0f8881c43c2004802d40b216049880241001c4080100655074660100d181c0055034102480c813940c8400000b0401c003059100310540c01290f102c581c650345e16035031459070f203084900c18000c4004000e00100f000178294075405960503555540400c2070701c003400110701600c5080c2c60a10002e40400c2030300c9040f101600c43c522130082e41c002c000040010710a402503030307001500c2040744104a0b02c2c6e0203030800c20820442c80b000f044050300c81c5440346060704007a02440c4044400f5036a80385c060070b550001403080400070003070701c00003800d0509054168581c00e40902000c2d40087c1944003c000002061480340344140e00b40004e0b500071951041140307120745c100082041880910342c003403020710400d0004140521020317113404031140300b60750724540024420564070b14a207403541c0300060040145a4040046a00840328440c1403086040210342c1d60111130 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 757415350 1250 757414100 757414117
    0x80c04020310030b0619120c0614040513151214060609180c03100603060b15040e07050403060221101505090d020a060203030709090e12030c07051005100b 68
    0x160002c01480040c50a0300495042940601885d01c60041821110406040c642280c2c182e02004543c03041000070b0001a800035080c149441580e2845d000400740150040d8054035201d450b068401e580820801d074040d2000c0740c2442420310320755071360f003600404040740700300c0a888110034241401c034038040004100b07018038000790401485646d2030580194811040000100c40d029a400803403a550b41040900d9850300c400b84000341c030340c3c5036182090031540807214460040c07880c0c0300141a50220602507500b103842d15110500d0599403134804407054840c46d00000d10007403010230008000a009045010404840e04a8200c6502d40600c0d400011075184200b10921a02000d80d021091081e07010702403003c00507043e030108010660001d03800440940280740164404400c02040988c440e0507100188801a01041006214102c407910f13440d040000e0070307003041c000000c0b4007030b11040c00403189030755048030944004664407080000641000c0d81d00c482500f81d4035a01080800380001200e4444 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 757416600 1250 757415350 757415371
    0x20d091a0c1c0908070b16022802060703020f010908070b0106021c180b0c010c0206010b04060207120f2406050402130e09070317090910030b060409140a03030501080c040203 76
    0x80148040b0070060f00da81c90088940320382c244200000244032044040c090968000e48114014403090000d141c25427080710500284083c0d0640c106803003190741100180e50301510101d503204040e080076860011103510080485d03280c240d0050901c400500074181d5184a10340000c61030341d03542d0f0102d079181c085161191403411000003480d144c1c0c0c0103c0d079141c01c0100c0748943d40d1a02d581c1b1140301c0310303d030086011214640d4440300c2120b030300c6506111890141c4041d0304a14201402c02100941d1116140615451081c0d00c0e90900240400741070708410066120000d050700c59118400c4100c103c841d1104007542e1420b1020114491802d80203546204070084640904949401d00520380580c024009451502038444080041440503a55020304000004050b568000141c00c0c00105540201790b040b906038640f0041c00001c5d050460325070054403c07075010503000c044d4200090b120515030440c8400d849090020b908054041e0080750407070703045005468800c007140d024001640310464454100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 757417850 1250 757416600 757416637
    0xb1603110307021b0a1a03040606060c08041802040e07020c0f090112020904022106100608061003020915040f03110a0b0301331707090e0a020706020d091a0c 69
    0xa03085800d8600101310004003186607a668841c040d1400c403011038441d4020040000401041c000c07035001c0d40008018510303110900c025140c803580031034003c0d801920780084031304201000c40d4003690140c8001d4240c02d2030f1115142400c501c040d54548044c0314980c0220a2203010700f445161090340300b8102d42c1081d80d8080745415645c208210319200800c00c84c2e10101d0306071244604421203001d41041f94402c4003c00c007605205007207011f01401a844602003100c001e0402c40307242c54920030740154000a0a0246c0c48000c6040003030a00d442c000e401e91210341010034001003146440d0600c0c800c40f0b014058054541c4401e03020312540d074402d4080c03400d031014100010001d060502c0303240850303080314080d4007505111482141010b41440704421000802e46002526a2101c0070b040c0354103c1c415044c203291952a16143c61002030005050a02041d03001c03640200b8030080b41c0480b2062220b0450400050b8028606020414025040c0c4107101c0c0b00100059440c060030022a41050062703d192402c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 757419100 1250 757417850 757417873
    0x1a0919030513030305280c1401140a1d03161e080408031b0604050c100c0615091d1b0609030609060105100306031113090b160311030702 60
    0x1420018012030401808110030342001d207074070000e40c0103984a6680c0c1c0340c2d110340001c2c01061b81c0301d5018200e0070444c0f0200c1d04010706600304d102c035420150700c041d540c00086c040d220098010032546c0ea916010309090010020308001310303400b40c0130708100301e0803a0448204601b1807581c1c3e40900038101c41d4040c01240c0c8240420190104100c4c83c020b016490381e00c2c074242c1e075a403074082c0d001075002e010140c1c40480c184513502036450304441c042d84444010250740c9003a4031241c1c4c0d161035903044035001d200c0384464800b00a11405c062440340d60406024000004a0703d440c01d040030151150041c12450100c04d65031074000c00040c140d0300310058008080010445861281d038402500010b5070041003002203500ca610140400c40c0b0801a117006001598540424400e002800e00c01120400d8640101400007503d031640030f800090054030844048400a10b90b44018848128050031000e06e60302044804010300c01141c12511280d0347c00d00500194036040300d0280020340f01c00026800c00d280102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 757420350 1250 757419100 757419133
    0x10807080a3002011b0528030e0a0308010305010e0313030311010902041b03060f08100203040809330a0801050603062e2d050c0705040c0c1a09 63
    0xc507001282a2511881c2c1442540b04801142c040c61020150b5120903800c1c000100940505400c0304890030080d00d041e4000c1c00110000b0540901d0b5001c1d07140003c1c4000500744645e0118880782120710490b1000d482d9414050300302a003d00c011101e941c01c0c503480e403803040800b0003030300c54000c50f0454201541d41559410b0b50400d00858064016650303424500c07001d40c0c0d4a000d01401c061000b41040b41401c01da92001307080c0d402640001e01404100b542c00c02449000040640800010480050300e940342d07407034010303501d03c100015544c2c0030440c030b4000c403030038107080d000c080140000340420340b264070490071907849070300401c4044800329200b40d0041020f03003080c100950740000000c140ca000c818540747c07242020b184492000c10440c800c682c0c02c80e48190856990003c1004105021200f0320a1070103d014019003080d01604204006c9107071004441c040044002400d0003d00030310400101c04002072211289080a0701e07800c1107102c0c2d4000407410743c00c5107030007500c00d00c003d008100e90085454 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 757421600 1250 757420350 757420373
    0x30129070308060d17032502010507050f0904060e161211190c050106180f1a190f09020d0b04020705121b06190e0303100909110d0b060108010807080a 66
    0x26070b1017101ca56180515042c0000c02140b04804807681000348107111071841d0020300452402e01c080d60316140034000307441d07049010780386c5000310850041c1d6141100008136014110961052800c00e2600050049401c070400107609031b440c0e169231361a078080c5044590001c1c1d41d06030a0444207080204000c41907076503c5000409205c6082c180b805035180d2a65896084030425400070310281c0c907558024806261500075081107120051060054155210006c9e817446c2d00700b000140309490603094802401045002c0a00504005a4a003000d03907862407204080d60003100580d03501e915002e00e0180d6450148207581d91250400c1c0180500f01d00d600c0e040c40075a02200e00e8038034500b034950b00d40800314410004148260540761550311200c40d20b2800c40c040c1d8280340940d2007250020b00420485810103030724003003141c01100e00030034030504500345480081450016503801892541c1900d090040380f890490240e0020b0380d41a4550380e1b035440f110384403180c90090003401e4101d0301c51040880ea952051 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 757422850 1250 757421600 757421603
    0x15020703050405131407020307050714010c050f0a030f09030809010311090409061b1103221a130e010b1803010209030a1401050a0b0a0302010507051002030129070308060d 75
    0x500c0c40d1980f038100003600e40c2c2842c0000c548254031682421383d59611403510799080300060000758104103803a178607581c551420b4050007030070294150300010503a02c40d910003440d10350000e0541d00f060300c801d00b042e42c4812400d44140c0201e605034016003c26840b0310001c90442c1d82010b0b83c54180f40d07a40f40110050104c00e9407040480342d00303015031000d59450b84200d20f0254440c00c0000382910000107004501034009848505103c10341072a02c0d401c0c5004409c40c0c43d03150000907640d000308480882650b40d10301d950052600390b15914461014200100000c0c02c00c2e8560381c10a5010302d40d515408601e000f402d011b00c0311416410311490501d8500543c41d82c0110000a001600300008030010900c0e054003500c045e00c100079440505040d00b542032081a80110001e0f8044c448000402d0110f0840f4210303120080c100403001408909020303091140880510015000350751b20750307503074040000f001e00c405080c442426440a200f0420100201103401090381601c80c00c409907108020092a060000b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 757424100 1250 757422850 757422857
    0x16030b100504051303140c070e040507030f060b03251401210506120303060d030503041b061119050a03111005010b0a1d010c3e010e090415020703 64
    0x1c2615603440c0601403186207070281a059910103420000c1507000590301d4920b01540800c004540301030041101410b07282545580f092035143c92501034580301081d407001d0a0911007902c12002c208007904003c048400481c1114404210b000c030303c2d00b803000404801481c0f001c00e64410040b9071544402d007484010141070400009c0d0045040e400c8907030920031216a0640e03590304101d000c0c5440503000c611098290010340c21071400b0302c007142d60782c00c00700d0029040c0b05001c80005d042108003200028080000d21428034040d9a4503c007411130081c014144625000c2c14044204848520340000843c07a0400000c0c0740b500a40d40701903840403240d40442c0b20901443e1401d440321400c50192900070300000582c196039100307020340140400d1f04e4190103100d08125540110305e980e0703c03040d0307140c0051300241c1910071908090005400c041c1c91001071110f001d003114134102a0001d4803000c0d074503213600703072101e0315070400c1001000014042102d0003024030920031204240c03040b065020f005494460308 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 757425350 1250 757424100 757424131
    0x50901210e01090804050901120c03030e0d05030a0c0c09290409082d0306010f12020d1d161217071509110901051023040803190216030b 60
    0xd2420b425030340d907070600355105200020200841d090032000705004108010a14410407e103075103407010044144805820450341d4100e120f034581d107500c2c4542c44668010102e07a501c41c541203025204903520241603d640080c15400141c14995014204182c68000110310b110000411590008480c03002803070f4120740e40c2c0c1805000200718800a048a00c00c1340809011348004d801c618980c5103100c515840e42030400e00c14003da0380d070401440030071140d05080c001c0b210042c40d190840203001c0c5000d403500850a0102281d01480d0701c401c05000d081150050b540c540202c3c501c1c9030003034007040c420f819401888040150100d490504a0381c0812403900002e403901f189a11500314404402e0280044141e03100e030400d08000060160030f40032802692400d9056140200244507c400c000307411007880a07550a03088010030305000c251a12a90000c103646a40e02c031541c0c1562604030410303110b0070700c5000060035961800051104803208042880c62901400c5030385451003900d02030801e518001c0d0f0074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 757426600 1250 757425350 757425371
    0x1219050a0803011d09010903080610030921030e0706020604080c030408060f0118060305071703070b04050c0910030c03080c1630020d0b1e0403020a020a050105090121 73
    0x78021802011031140c42c1c601c0c001c803000d5807415044050280410f981c549030248000030f40080550b503100000b01e030907035140015510160701a01a0220007800303294460f143c0850b450015905140d080a140d50420100c60b96440007642c5010074002c01000d0f074010000900080c0001e0010110801d9290030b480c102a83d50301103130b1038401c0950f0b20003402091080103000d07414040011025950560030203109041c0786854143d280c661034002d0030b40f10010b030700890818640403c111104c00345c0c0180b111015140c2800d01c41d07202c40c8801912889844408045880b00c152080e0403820b40350003031414489107180d0340d43d02d00a42c0c0a0100d44440d400b409010000c001c1890f140f00005011116400d03032805000e11221801a051846400c00000c3d0301018002684440080505071b40d40203403040c01985898600c0000300460390440304000741c4500c01c1008041d80403454800b101d1013a90b084d884952102c00544090154400741400034241d460541c4217030700d0551510004c020b0a200c0001d80c0d1510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 757427850 1250 757426600 757426613
    0x6150a11010608062d0a110405130b0f09010308030109020901030905011803090609230609090a0905010c031803270306091a040f06020d060506030916051219050a 71
    0x543e1104911360482d104114070440740507000c0210480540c0c1204018900030040745e030f0310101a206e44030240c1d0b1140e110307062420000848014000042ca540301c02001e100c03c04000d0701c0700c110001d02031003c42c0c2040c551400c1140025050f2039104900d50708680c2460710a000a4115080080c101600c0c1c030320300008104288070710002c01a900700f1031400911070f4140075000140303070342c0070808110040c071040200400d04100085003c58008040007070718900c00c0002c4803030003144511640308101d0010301250010381e42c0514441c0d441800203008103002c020b819812600d036180c071298003402070100d44001a00c1026690707510001c12103010072600380b48810190452258101700d43c0c0941d15000f6000b40007541400014104003804045164681030703540c10b492004601c4000c04054001c034550f08000480e820240182801070030140d1240f61042803180d68036200b402034080361144038008500c40c1069105402403000c100d0080007450b44d80c4280703912100d030008084d206030065a0180000030b10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 757429100 1250 757427850 757427861
    0xa03030f11070305030603010516020c0d06061a040f090203040218040f08190806030d05040e18060406020913061a0705010b090f06120c010c0b13020a18110306150a1101 74
    0x130740c3d07a07584a2805106250850b00e0280c08049480142191800e8803a80040d00810b00b032415100100f0200c842e1410b9400390805400005250103d2201904060203070005041110361815142c4449036036107041400302e12040d00d001e500a4903030703070320300c00e880750282209038209220b407181d14191041030303c450030701703801c00c101810042c55072004040c810fa80c0030150382d0b040a001c401900d014084988082c00c1c0384907500c25100c044884000290461800c14500b08142c817040054480300e14080c03801d800254010060b103031190043d0030420140034854450901030304c0941d0a00f0071003084040e241c07105904892004c440641d07c401203040913445440140d40948080e20090b0ac1d036007402d40401c0090304004501c001190310002d1111030684c0d00012004039182c0003035100500e6190042240d45481003501d010350044039076000040c5024401c180c00f2416040c2050410464000035a403070ba49110550385103174880641c5019088540c00c03e002000003401d141406101d8206050f4402c0c02c0d80c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 757430350 1250 757429100 757429103
    0x150907180e100e040503070f03090e0c0a12020f130906050f0d050c06070f05161a1c02090a050d080408010606030b0306040b090f1006080d09080a03030f1107 69
    0x100d014604034101000940420050180801051030300e180caa041c1803200c0e10144900800c40c01c042012406015040c0300700c0324151b8001a5038040f20a407414090030f514180d11421011000010003d640c0500c4030055070448032140d501d40f03103078007407018038400a500003086000f2000c00411507110814501c080300070082c0b0300720710b010410b10301c0c0c502003003040d1070b4a5501600513000c141030000081c0c0007203610b030a00781d82190110b0b120b00660408a45084030500018281e214011051200c01008407001c4100c80c2c01c0c0c010510072821004100000b030150600d080c60380c2000c2407640c000001160058011800c001c0c0c110010140d442001840b0104120310565650b0400202072101400078022540500100d00b8103025110400c404a6551000280060852544400816a4814240208044201c1900440c0c05a01e103000034034006007894481c00505101d040072030404180a000f81c68225544000135100c4031010351001e5024104200b0358070141aa00c02d1440c51580f444006090500d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 757431600 1250 757430350 757430357
    0x40906080a171c091b06050c060105011e031a1c03090f03110f030a0b09101a030d110106050604060906030f0510090f020c060a05041209030305090603150907 69
    0x6109030304005281c02e000d0342040510010802148115031112204810091104000010302220700c4c03d0865034003000b08484900c0d592a2103000030529030050141000c036500d1825103009990702c10041d40d80075a100e21400e51281c188500d81601da0290b444040180d1089a00380d0f00d42c0302070300c0000d030700d841c0c42e50b141d20307222050340b5506040c0740d803100702e43e0080c008041c142002e1070b00b03503269458210001502c2c1d9100300400c140054040c2c505004002070207a00c4105280a0706003081226183d076510440881a14500700350500210b00300c1c10842540f000c058080c000c40b05400c0d1080f034541900843e002d90303641d21000005200d40768100103000030281c66480045aa040000040075a98400b00e2502407034107041c18400b05a03c80850030b030448024403400039007101c0c802c004a0107400b4100001c003c2c0e000e40c0c001c02c500c00c1d5484e0022031040b40b0a01c4002240e11003ca000c0d50400344900010717000407010b02a00b00c050074000019900100c0f2010802c400d018481e0010303082510848119000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 757432850 1250 757431600 757431613
    0x30f0e0313080f0604080706020c0706081e1b03130b04030807120c020d050d0b040e012c060103020906061209012903190f0507030803010311040209011d010504090608 73
    0x50594001d0010050704102e400392070789041840d8500d0b5101d40140026001e0304c40042c41c0301c03c0000c154106c400702250304044d9880c180e6521805082c000f0201d5280c150103ca203180c01904d000c8121510b44942c4040800b40208070f4503a526104035000104000c030072901e41020840858081701d0f00a12540c426075444940e458581c5004000c081d40c0700300124031904003403803156503980110762088103580da45810f07629000711814140c06005100500c98115240080c1c0d03503001c5206410202c05040c0400d0740d42e65048041188061341041c0741045205504040d00500052030800c50380d682040d0020005420001c0e0044220100c8030187c0f900c00c2c450795900070011801065120700604140c0c0e10505491294070b0f20003080d03c998040050707100c1482e00700c001004004446144244094000c4104e0b040c0039168640314041c1d034000e001c15103030305248446004507481e150027102da443c08107030b440c03500541c0744080401d10801c00b00b041130f06114060002003140d6240d8460306005000000c028002d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 757434100 1250 757432850 757432867
    0xc030304091514061902011d0a1209030f1e0206030c03092e050a110a020303011a1303020103020702030a021002010c08100f06270b030a0f140610030f0e03 68
    0xb20044140d0180c00160361480100d601e42c0d8076081694400d204c40d1603c00d85c1c1d4801c0010482c018441400319910000c1003002e40c0c10740c16000260f03902414401d0079072200540000206954800c06c0e440002c25161085481400145001c00c1030541c106010f4184010781034550300148581c1c0007210202510800842000084401041307074071001401005d120803020020207407510046d20240320713005144d1303d03074007c500d000c1c20760f92100151050243c0e00c1911120f04100080d00c80d171080c443c85d001c00f0480302c117801070070405004981c0d0b1020640720201c003c2d8955401500650407001080c0d90600a000516001d84c5804181c0814924290300014150081502c05441c4180c00362141c0c0501d000030000740203000e60004a01d0990391507003405000000480301203220080308a004546000340c18900041d4010500301440c0128904131041c808030028500d000d00321158420405a030004007004510302c2e0400742052030076a040c91502048031181380080c0d0090f144078216682071540006040007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 757435350 1250 757434100 757434131
    0x1005030411090f1f0f092f160305120c0301061d0303120919060b0f0d110f04060801020c030406030e060106020a110117070c05121201170c03030409 65
    0x6000080307650315900e09010f02e0f1070028002c01003040c0301d000310400222010440104201004161440d001002d640d196400078004c3c2c0010170792040a407101d0061501d0100e1800f4254040d1a44000c2c900d04000c141602e071000c0c28402841a02440310422068800e07444000b5400d02c41e091000c5c24a55a5152001c01072481d22100220450080302c03e010a0741c0d69070100884800c42d0403031440594923103a400c98282031080c5d9403a8008941d2000140e24108650b0340c00069209000300c0c1c00342400c018100501090398403461004104080c10701e0310021a00d4004c2e201100540d02500c00540d807034451031b2080c00c9a000c1c00c1900141e620209081010562600582107260400e00c05001c05524010300a507445103000001403040c0a142c000140c030380d108410058450740c2d140d400c85014103010201400420982106489c680106000c815454540c02d085840c00c60165500090036882c1c175000d0300504280240c128014003c010000c1302d1035034204042c1001c1d02c2d07965000594905250540c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 757436600 1250 757435350 757435373
    0x1b060204180e06090d080f0c040b0d0606090e0c07060f1107060204150c02150a0507020618030709020c0705012304150e03011505130605100e0102010f021201061107030210050304 78
    0x4130650300c50701c40c0000041d400981c0c0c0c0d07008580486103041c42d889180c100011401103401c262245000400d14101c07444c6140c000c502121400e89410500c25141c110300751348001e00b00d4040b0001e21041000d03500041096016903084c44c0413040004003070040c0c2c0005003040e0710200d4285c03605c1c0d8010500340301c0c10600e03200700c10621700340e0309211210030b2160380407619050319440c1c7c51102d080042075240304213024400725494950300921342580d40303180008405c002051041064000d100c2c40001140d07c0600f4070071103050301d000500030080b03246000011503200603001107400e011008200c001904850420190000d00340c02c51400040600c1c03c0c0b402018500c40309051807190781008100000b4692802c900c0066a200391013a0b40c00700704021031031016108a0380000c1c1c0080002150b9401c5562042d040049407409a0080c45001e84010b04a800d034010742c441c94040b001000010811907005070130f02d04030100e0714003e0360310450780d980001d0f14030408100544080f60000081104100340c0c503510 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 757437850 1250 757436600 757436611
    0x60608013233090d030c050c150c0f0a0804140f04050103141b0907030203070e030a03030e011503020f1207030c08030a03273e011704031b060204180e06 67
    0x5143c14081807100040080b840a4409414803804071104000d104060140d000716040c0540807481e00c1907048032030702d8031351b000d0098042c0500511041e014041800710780000c0311500441d483d41410304091b0700303c9035581001e590540c44040d09a112681b6101ca0244134002c2d400781c0480000c0380100b4506500b00300400d001c5411101a0080e07440e207560b20f201d03030150004158a40140c1325500c55009a551040300042d1681c1481b404940d5010580d041d04800003400c0d86900921211120b280d403a04d041c659400020b48c13040c1c000303140105605140c0008681c9940c20021201c0c00c0fa0740343c981141400341398000d02019000001d200d50700c01e030035018605070726450020409140c183c540840103c1251904001c00641542d010069040358502000c43e118001d01c084c072048080030316151a10300b030781010035400308042458280c0345c0300c1d501482a00c1250035031a403042c2d0440e03100100343c0100f41104200c0301d4690034840400d03410040030003d20a03050850001405d210706803411454103100814 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 757439100 1250 757437850 757437949
    0x140705010c0503040603050c070f15060506040308070f0501140907151706040c03020f0a050711100503150a03120e130203011412070909080d0606080132 67
    0x28144002440041100c4c00c941481c0760008898480e60303e011043d205000e00034105d040314050000c00d001941c4004504050751080801409555a0a00c40580540e100103001918140201c502142251842601c8548a000005901e0f000360b400907110340c4080c0c9116205501610041c0199589215401400c1003142416406802d03c800c101400310801040c00d03009585401388030440d5800b80e01603401e0608502c110f6a01c0d200d0600c0010801d4001c3c00e020341d004407030424007440604cc0a0342203603402c0003070355404c0d14554885040e04100841041c105412003600f400004c041401447c442120752110fa66010381e904801003002a48681111030102c1584100010800d603a602e000c7c0c090354000980c1c2e90340007105551507203800c1c40050342c007000090382000e2687c401c10001f14010200c061460804000c0030340c85110480ba4084c0c240034104020045285009003043c401c2d803502040c03982c0e48241d0300c81c00d50385004940c602c0000d16070042c19068a201811800303240092044c402c105416 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 757440350 1250 757439100 757439117
    0x8060a0b030111072012010c08150108040b07090f0b031e0f3d030c06031407030506030a020a0801151a0910110a0f1106160b150d14070501 61
    0x35000f451407141440c01003070403404140103803580401034090714584200030040c50401400b02016800380c43d8000102000941c05400281c501a550115034402170040c2d40740c120942e07480e61a814805401341c0b0500600104002c0014070b605001d1641018004410183ea01c0303007404081545980c032802c0304180c0242c469801c001c4424000d4000b550300101140c06510090504103810503405e610200012104640c0d90f240c404000040e1507080489101e045080140d0796110001c804403115030f4500b002c1d449000006c100041e1098000f142c2010004066030114001507001601240c4030340c1c045400ca0f511002c00360b5004403200e210b40004c10040708100401b4904a008440c81e03c964000e062103941d4018052407150b1051088200c400001e2040340c0c6240070605141038080a5168120b51500319251039590700d0600344180c0d0002c86903042003803040540d9999940c10710400921b0350b1501040d1010ba1221565581640c100c00d502440079452102d641100150401c9443d0b0006410301c01e511 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 757441600 1250 757440350 757440371
    0xb0118291c0b1c081605100518030315012105040b04030e0d021f031d0a05011508100c030b04021209070801020301180c300f060602030703050903100608060a0b0301 72
    0x1c140074403100e0380b103139100d0b136901401420302003d54603000c400380485c4524811144c545640c0c1d40580c1c0a058004100c80f116000c9101043e507d220440c0c0d008281c1c2c3c840d04c4600c001c1d5001d017201410a00301c1ea00b545c0e10b06000038481c0c00459000b11010b841c6111608103001c02d041c1c1050041118403425074291212503070a0300840d1a488403036091548242208c50a0b003d414800d40c0145c451014008880c000100d10a52650fa920017002d82039516500c0c241e01e40c5842c100d00040002180c41041c00352101031080507100d0020701e240040c1c06c0034551100028020b0b43e03034a10040194880c0c41d42c04942a090101c50f8a242155079001440d4a0384100014050000c8400c0180c0c1610060a4080360020114108030784101020031018128424400140549030a00b042000c182c020703541d0420507400050341d68401d403012440b4017005a00704101c0070f80807911620041040460203802c4806d000210410348044580950080f0019080042401041c0e40705010345910210110028808032141 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 757442850 1250 757441600 757441639
    0xf06040c09030b100e040506070e0102010626010e0d05040303030608010c0206040219050a0306020a0e03070b090d050309030d050403141204051c140609010b0118291c0b 74
    0x25800043d180b45080d0001842c503000300d0b0001c002030329410a440c0440c0c100340c5403080e91448255410404542d041650482030b5105111340411182c071030995084005d05010701028400c050005010f055480e00e40500d1030740400c001d00c404111043c1e0f612a0717601c2c510b05005046442a421005041e410303d41414155a800a21241c025030100d03441080904191804400f01800394400b42d00020220000414001d1507801b420440555448a8a20b44507031410181c0382d03c0c641c05001620703401805141901d05044041c00c0c0283d105a080343e00e402a5940000e107041501850321000603000241401000503d103070814108159800500e81000103000c000618040c40c01094021108034501091401074261422000c40d0008a030807003d6400700f40c42030300c90038101d509017155801e064043c5d940c3d501c42e5000801c0c482030810305605e9203003080840f602c2c0e18031800c000324850b041c40510498241005000b003030082d1032214940d01180106000800790784014410301e01c0346508584107120980c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 757444100 1250 757442850 757442867
    0x10f090c15212408060105011202030601170901140108030304050d0504060e0415350c01050708030402031f0603050c0915040b060d021c1103060a0e0601020c12060f06040c 75
    0x82c140404548041d40c2c0c0d11241d440a0041c50b41d4030504540d10001070901c41c00300780a41614400c2ea51000710351001410700c2c041c0d00c400d549060000d43d160780c1409160028400007a00440e60200100d034881d15444013240c41a020b81020449070800414802008010080a0161903103030070002c2c00c09103010409007030603510035155801292989245120703520070104020140c0030b203403840f0070b074800d6010f10007244220320441d490054001c5d81d0040904000042c45025000b4140d46003440c000582d92402030982020308201d0301440b8486514080840d56102c1e94010980f113800040e11914508041d403828014060b0540101500d00500020076800d00d80c1004a07402500d0100d840d943c05030208021344203200a118000703101044052020646243c0411760480351141403040f04e26808168110384000d03034445500c0b04d2100010071180c0724016919600c010140180c908002c03085000c50401c0011040d40d003c3c58002c43c0802c11a81030000b411908528186c908001d054000c11001d0080716 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 757445350 1250 757444100 757444157
    0xa1121150601020106030b090a0203010614100509060c030403120215040f06200a050909160c0b040302070e0a020903010c08040b01061b06140603150f010512010f090c15 74
    0x11040303002501c540d0017504540c000755440154445c00b46407500080b87c6407080304400300d00c20350900030700040f5000c03080340403804400020000c9030360340d81c0319031309a501e40d104402d0240c00140030321254902e040709002400045008000c800054010650002d0606481e0781800d400c1c141e0400a000224071000d140303040441c5c0c840c00000342e0241100b082054129a01072661054400080103000b5a9014000d03252a030300035940071304507454002c1e40c0e15402c0603002c030240000305809502c0c0c01081005031040e400900038010303110b085446041007030f0080d1080382c804c01120340020724841e81d800c0902c9002c804175000e141005090500341e596240c899018400d420820804124202c5820312100c0a4000c1c181e1229040105100c04090f01102440c00c8980d2803190045130500d004040800c20182e10414459941640b03603820081080f4001d00d0b0800417100940d40c4080810b060a258407418501c035019000c0350040916041500200c4840605450f081002c1c03815480c5101087c0d82810002e01d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 757446600 1250 757445350 757445383
    0x626030a050721050a17060306040602070201050418090210020f12030915040b10080d050a14070b1905071403040f1103070e071806170604020c0a1121 66
    0x5400904207040650502107680345004880001c048040b138001004041d503c1d015190b40c2041c20008080c8400348a044480c01d415400100009000540d00e80c000c1510720f1050411a0800d07840c0e03030b0240300c4107a6507222011200d5450030148158079041040303901c61580d51004001d40c480c0080e40c2500c807040c008a003401020080042419000309102e032450300c14043d04208503d1a160400107080b641c01d651180218003004804602c000c0017044800c400d002c1d5894945c40c000d8002000c581700150402d440310325003024400c084c0040d00d00d0040a001d00007622106690259901b0700c481124000340c4800300b0702c00303000344c240c81250940c0700792030384190012095006440681020552881c220b041c483c2d0500640d80c001c1001c410810180f4091032141d03490b00050320141046994840a88c0200000319540f00103040044d0180d09600e0b5110002400140c201480003d4091603c80c40c40ca04480400c2a01b604001904010f012818190983d20180c240c1d00c00007a00c685d15003058581d8401076 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 757447850 1250 757446600 757446607
    0x70510092d110303041d0402090604090503030f0717070203190203161401020403020d0c0608090a1a250203090315060d120e0307060e100c170705010b0d05010626030a05 74
    0x3103503000e03c02e8800406c82c8460141c204864907403603801c00c0c1400c0380d0480c4200c1104020900c24242480f4103500968018004d52a68440c03000628210710000d049600b08510311818182c035210808402d8010340e0745800031030301d85840f2410070317901c00d0780400a14110740c4144103210808400c0080c052043d50001c606020720340d904211a4003a110301d80010b50040c0102d40b80804114161000f2002c031000c1c0d03912103140343c54403003680c1c1e180c485803c00a8034460541c14a0654803803014000d80d005030154011340e501407400d0900c1204001c2580010303002d41c1011030341c0800b5040c00d200b011448440307488d9211040c60000f000640c55414250702038807030389040b4440c00032240101d180d40e4031150001c0c203c40380141d603040000c00b00c01c240300f8414080d0000c02070100071140140c040350035a6500803104008006006040d681581003c001982c4564070380300c0078962900d4020034160858040e4002062860030004040712505d294903a2040904884004489800d000700030380d03840400720b1801c02d58 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 757449100 1250 757447850 757447883
    0x50417030c03070b090607050304021305060316030c0609090e07060c020102150f010f080307051005060d0804090e07080304080d0e040b040510050103111815070510092d 74
    0x5035000c0e401811901e4800000c4801c20320403a0b030420761080340707288212506903403180f0044036180001c4da0003d4000e0b814503940c10407421036401066110300c01030120b03000c2107089a0107a400011a520a8907038092510b01400303200da000c04208050062000d0034810800c889000c981d072140703d48200300400030717031144280171684280228140703410718241c10069410301c03070b45a0400d5413080c840c9003844240350300002041d003008002c0e03c00181c0c12502400200c1c0a00402601400b40108280d6002e40716080c40700001d8500c41c0030b00b002e0449214001040280c1450f040d103486026000148542c0c0188810030603590b0012b680d07906440384e40f03003485001c0c4100010901508414507000d501030b0500c8100708800c000480c0d144101ca000340d80c18491018405018020752050345d4a150808000d400b0006140c149804803040811894001c07621740fa90320784605042c259203c440c800760310707210a148002c2c009074070700c0300984070348652404103404107030f00340d440500c4072003180100103450540c0c0e40305 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 757450350 1250 757449100 757449103
    0x1509060406061e020319030f1422051c0302091908030403080a05040b04080109030f030b1005031306061203020f121902100f06091a010203030c0715111c0507050417 72
    0x4006082d4280c0b88a1b24000d60040034020723085640540c40c155161006540b10241b81503a028081d800d088010001901060f41a040c8007000031405d581e584501848000200b00701020030500d9062560700580707404000782009200501e8412160119000d890203002c45400441264100d0398841d2a42c3e9507100c0c2010151614003481e03115080f1100042800070b50003406402c0722000e9403080c1c0c0c98440c4000c03000016400c90b55480035135070b0021000c1c2c0403d4600390040c0001c0d90000300321105802014078030340d074400a50b180c0d07030041c2c204010b50701c0c5003108141d01004507924180041000c0e009451003013080c00481e000b8620703a05141b10f000f8001002460080c4003903030f50b0400146041c403a48501e4140312000e46814820000140d103002c0c1c07161100c0200103c01c608190059003d5403440e02c0d2441a241d00d034011180940b2480a082c11001c022520b502ca02034000350207032b9203691070700500303075003d2941c440540950303800718201010080241d510030111b40680c0c190780c2c0c04160108100046a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 757451600 1250 757450350 757450357
    0xf050f011b051c300c02010603170a0f14030f0c0c07230604120b041a0f180102070209040201123b120f03040f0204051509060406061e0203 61
    0x40c00c940100c030f4100300c1c000401401150002082c0d2505107011000340d1010b003049001a6400300c0390700a44503071400c45100d039003025445454610010903840d4698580390444603002403488134044000505d1220b42c2c1d0040d445c80355010150916114602c440f481c02d50349403100600c2204001c40e203000080f0841d00803000e031290001604100c404040d198140081506014034603010032124207442681585010011642502d281c440142c036004c100d9038801d0783d05000544100c2d100d80260a9940282501c480c0d198440c1c04010340c450b4913400c1401c404203041104260b00001a40100710b50409038a450041c1500541e0a103007880c080c0f580488205c000700481e04a40c0e02650420300c1e0034400903040018100310101ea507a91240b607401e0440c54503a6504d035160a4501702c0c005200c058186c01110000d194407502441c8060000d4410394000b508640e070481d11403520b200c0046002c242805d242c8c0555510207015101004014203004000c0d200007640200240c3c0520340f0420095518828801c2e07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 757452850 1250 757451600 757451603
    0xb04030c1a0d021b060c04180f0e0d210e0a030e0102120a020a020310020322021504090c09080325140a0c240903081318020d060f050f011b 61
    0x4549030949800001c0c0000220700d1440c4e054400c040c041507000800400303c03011190102440460340359080f4002c805485603a8888540c16a07980200700a01028000b503401058542c4e5002d0348003000303043c45151907117145200c54810389849995001c100b40080c00b40031964040c200795400c0304080004034542440c07200c0302a100c05001c1610403041c0d40000d6403c408510031001d0b10a840791344032041c0224002201c42d60401030040c4803640c005138010703201c140c907103001626903400035101c00080c0c1010342c4168044841c841d96484243c00d400d030700980c00d00c041c0ca54900914a800c02c034110f8405107078202100441b04000395080d0768200140700c858941613400b40001c0c2da80c03102c1d0504003c0400c1c03401e441000300f08a201c80e000701000c036040b504004d40e0012a101c41540740d0a58407950456080591b5038007a82800c8031010a44000c9040302810406140c440540c2c1d84c806000644140c41e0107a01403542e01d80341941c2030001e9554840b042c00780c0e6000307280407511000b1780d004022004810600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 757454100 1250 757452850 757452877
    0xf070e0d0203070b0f120c03090730150510051005130e010905070f08040b04080d020d1409010b04270f0b090c090601080f0a0507121a0a0b04030c1a 65
    0xc040c07004100c0b91006d8808500314400001d91030b41c070000b101fa010300c4112000040d64004060510074020b4007000181c04031002c01500f5002210710042042d14a0b11010941d080b500788540c03500c1890b1280599540070550003180d07088640f170180400e0200701e80c054817030709204001c5030891121946401300c0c03005010560341a0f000e9651940c6190080c00192130400028560500d86001c03c0d0240c5d500034040e940c03009402906503a039072562006500300080005025400308a244d103020507170702a440e05404504030800786402c00f040610b003100c00182c1c04500403818082010080020000d0305403501200b4442ca0b480d803c40c41c540f1240b003001000c3c00600c1e0442c01e900384400c2c001d00007100c411044007a81c02c0c01c001d459280040d54480c104441d45604421050b0000d80d0740b002c0380d000b642e04a0340030306107051041c1d00c1c03200e140e06130b0301040700c41e21441c440168a00800d00d040d0702c815000b0304138a0000d5152904586402414185902540c05400003640420811410300b90440e01a45a07291 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 757455350 1250 757454100 757454107
    0x60b0a1e120603110a1d06041802030105040309181104090506010201020f0406052109190309050a1404050705130b090307050901260f0d030e0a0c15080f070e0d0203070b 74
    0x5414500200c2013030005000740200c003400724242c10001440b400b207500d10042294665a54020003015081200c10000da100c26014141e005031000d00445008511075181d09d81c0c1c9c00d061084200d0700c045580c045c1e105140c2000c105c1781106543c0da00301d4045c1c60b1003800109107aa540d0005034064425242001a14040024001203e40d0310030301405180c1c51802c589080208040c40704030400901382d6000041350445403000e003140d0314502c2c41178040c2e403281c200400b0321a034640020303045010552042581680070700150b8151716141c414a41d1111840c24038505085c1c411110000c04025400381c135913010b0001030203403030640d01009800b004000050a10407030350b84502c043c43d114031030382c04003002450b0b8240700b940d41c1580215402580700044030091903114038003103044001c0d001040764100140a1140001e0200700d442080102038910f4171301c541c04a5803000c40040035400c0040c04500046050000c0c0140158060110714079507030f045401594403005800000c0c02d082075540458486400007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 757456600 1250 757455350 757455353
    0xa0503030327030a09120c030204061502060603010608060414010e120405011101110306040b04020f0a021c030c02030a050706140103120219021f020708060703020d060b0a1e120603 79
    0x81003500c02c5015038103010b40c41c050340c091095601e00844c010700d00814007100060016060304005064001e010b400c19068540d40c0350041001c4418503000805e9201400600035403094042020035048181a002044014a0004000d440c0d41010b0801001c103e07028141e02d001c80000d42002d41040c94000a03189007001e400c0c00c07008103030f1051140300d0100d00c1c62912408004018451820103610f00001c0c1031a41d035416082200414071000c0559000760f09100100700d41c0b030800003500c0c1c9010160014900c0300c2042c0500f0500ba802e00c84600308240c10000641e0342c0e203901206440440300709052098032480e442c078218024204100d40caa0381c00c5140c1d0000020700100841c0b059120306150207481d034400c4d000200c1c17038071303240f0405019401c41b9090351004200901000700105c400c0685c4191020940c40d0800641846010358210b030000303030007084110000c0c16a11403140100744241000b85403160000d0302401c3d4810042811500310101039490140a0207101143d110692100040180507200d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 757457850 1250 757456600 757456621
    0x10503180625020a0b010e1305061e13030c03050a0302071a01180605060421050d030504060b04020307021506120a030809010e06040218070c14100c020c010e0f0a05030303 75
    0xd20150b03000c058012041d240c0a0300200d0f1181c1640d81110314100030380e0a1500e80050f009000c0c00031011100801d1048001c16814002d5500a403917440c6078103440c4040c510b200741c8200d40645017000d417031010348400c80001e800484c1ea40a095140c1001034076100e1140060b4000e001c0d50300301400d4500001030a1182150592a15040e12480240002450203601c5850304485c4180900d5400110800050103600c4103642c0302e6045081600d040c418010095072005c0c100340300202e0200100381c49606010030090640503092407044151821415440c0c0610025520340880342000302c0c15850f0300104880ba111001c42d50307181c5241e00704503911181c240c0340c000c2030040304071204545940785c815410350341807000c544207000315001494102841007425240c500304001425540600002c3d00702040040e14813008031072400200d10180000e0443d404045090f1903651004a085402c181c1005039280e0b040f0040042140090f600030301c0640e10b8030003042d607040b002d40000f645444040100300d0201e00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 757459100 1250 757457850 757457881
    0xb0a0603200405011d030f3003040309091a0a061701050307030c180e01150303020d0f1d01090e09060601020f03030103030206010e09010f0e010f0b01050f090105031806 74
    0x31044540ca0581a001c025400c0d034007a600030540054002821200c1c00c911040700d42010300c9009007a01c603261040031005140021302c1c0c410f10004030450503900c010714000c40a00c811a003591140c940366103415600280380d501c4034011035801d1691216590980c20040d400c10703865480c040c00000c04140c4030000940044005c00300c0d50081c0000400200e4603050110305601202e80c07144403403062a0070800300400440c561013519100741ea0b03034060b003000c1070424000c1140600030211902549030640c24000d0800e4240c4585406004502001d40e080320340c0321402d4100010310f14a4a50410b080383e0040b14150340703592064951440440c00d0003000c010210b03c0c1400f0700026021584042b12000744aa00ea02003440042d01503004100104698645c5031040341d4050003400000501c41c07820020001100d403d40e4000d01103a658440c0c04000c039030303c0e11641d00c2e002d40900b04503041c403240c0d51591007144201d81c1514104403005c401306002c032003502003185a141c050010f89641d403901e0200d1240505 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 757460350 1250 757459100 757459121
    0x5061824060a09090807080c1011030601030f2f0903060c030a0c090806070804030306031b090f200903010b0901030809030c0f060a0c0215040815010603020a05040306050a0b0a0603 79
    0x11212040003c030800d6070b10071108504d80c0f10421501300b1100e03444664042d04040c41c5821180900768490b8200391a510a02419583d0805080c1d100d0400030700050803500e445207400c0c10315280c045000400000d8251034400700e248142d825100200000303d002044c007685211681502c51101400f031019000300103540314896040041190708850790080721000e1451040001d250803000108600714400c07a01030381c0c040d000b810081000c40d52a0707921003c4070310030b04011001070020007043c0b01c140080e0140c030740345102502081c89075920301050003c048640300701044403850300140c00301d500d840a401807a900e0100904020340ca694074104030005a000c444507620a0040700b5080e403161800020030049510080c1099050514015066035041d40c015002e0380c0c4400160f0585040003580030041c805805d511019080341e00b200f010a030150581a0001024140180b0400f440103600000341c40440790000c030082402d45907040c8640090840c2c2c04500d401c2110f2000104409406802101296 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 757461600 1250 757460350 757460359
    0xe0405010c0c03050417011506020102031501180b031009020a0c05010b010c0804031b0305120a170c030c0d060305070306020909060103090b06060904020f120603190506182406 77
    0x7518040040b0350010042c0c00081c04140240700038001528184008418500700382c0c0002144ca5600d00c00607041340407680000010b070340000800ca06441982042c1d41c0f581c0e400c1c241042003205500107080c1d00c00307690280080c0407101000007160140b080c41d110303000303040103102199600c0c10302c81c00800d02c211030403041c0d44540c202604092154401e5140000540d0040364050a0a09580c0c0c0d111660280f4036254000078010400400030503c1488146800129014211f55803803014401419600c1110038006c100301c5030404000d43c140c000d104403a0700450001e5403640e10180c2440400062526030000740641c45a51401720402810f64020062003004480c00803851355218011025200800c10040032011005c002c0b590500f000c0002d000c00002c010005410b02c605040340a042ea0000280308040d172035900140502400c0c203015440c4640103000460122032680c0e11011317034a00300030740440c1c44080c5010784024844020f0040007040e91101a085c0c102c0c1e446039070a10b0141d001641c465124 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 757462850 1250 757461600 757461611
    0xc0c0f0f0201140309071a07051614030705030c092526091507020a061b08060303030f0105151b06270a0623010602010504061a09150a09060e040501 65
    0x50340b0300700307032440b900c45d1000400a26003060b40c84842c0c501e00c40000d945c8210148801000242c007408410070f450700380c40107a110b42d40b500800e280580b4030200100d000743c0108505000c0d0381c8000c11040040803040d910441642c03035001443e070b82d050600780e5440300901c0c00303498010a1640054104044480d1401c410041c80421031258414841034940380541d600c0030f600031422601503840c1070340c0700078103005031a031040da5503d0700d40540349003100c8640303450110300030740581076040318805400450682c011819454440b510410000042c00342c02c0c0f01c0c4003045442400014070408442008071a80301b6240b0020f14001e14590764081a900c0c00f02d0300e000440e901a5040c00484035145140c0c100c00100110b407130644401004060b455000e1706103132003605c505080d07005444140d0b80206920f6000040b24549410800c0803612100c00302050003c0c2161204195076442070b0103904081a5220304086c48030010024081090743e612001045041c40f00c00101085c514190741c0c440c0d409200280034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 757464100 1250 757462850 757462877
    0x2030a0b0103050f160e03030c0304080105010609030f0609060921030b030313060e0d1707170403110907120f090b0a090c0b030a06090516030b04050f0a0c0c0f0f0201 73
    0x50700c00858000700c030680c0c244005610f0b02c01d4a4590070741c030300c0c5c0f03400d15810f00c4041601080c00c40c2d1101440000e10342c8000740030010120244145401042d50307140012a95095503103503d2132f0943c600014040301e843e01950002d02009030311918045501804103600d03144180600f4080c040d4181015020a20700a4100c200f03090202c2198070300810418603005840c00c080003658000d0200442c3e542241036558994001918400b017074400d208078200c81502d0328480c0c035040081c903d003070320028040303641413008000003803038040b103a440c11200312001c0038582e5403c0001c941504409400350080d50a181c0d0021103001e05a1000701d0490007049403c00a546040b20700c0c1c16111141030060410200310410444404010080d60b0400302c1c100e4046a86540d41800905603241600c9044241c1c0550a0860405030548106910740c44150f03414466480c240710362014240d0020b10400300b540e1074000d40f409151141c00302904055002100c40d42c0d18000c0d01304a000c0c1e0040700c004a000c40c004441000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 757465350 1250 757464100 757464107
    0x50712030801031214094c03110418020d050c0405030d110304140613060918140c03070311040f0905090327011e03090c14063a02030a0b01 61
    0x70f01d02c2c18044481d1030100400c050000c400381000e407464010140c7c040840f42400c03909810b08001049243c1403a0f02420070044c3e500c9810308510500500d40b0307007a605038030781000d441036130105c48843c60b40052004045001c2800703449910002d540e202e00d48000c10100039426809030065a074154211540314200101c01d135008030908201e41c5280e0f100740000c01c08601420100004c0c1c0f10054040307414140f00c1d2009020084ad0fa4000c41d01050300382c01c1c18424244c0140c219802299004d40900c0110142900300c848040090858141d1400010008607064001d402c0303040e0315041700f03400c16500c56882042c06040038040c060400c1d0346040801040500b08008140c44240315400108020076274544c0190040003400003880e814845422090f1500c102594160426400903860100760f01d41586099a025201c81c0c0000000141e69030f10b0b01c00c207888500c1901e418090b24030f100d001d034070414a54102401000c8840350290101c0c114130584113243340d0003942c05134580c041c0902007035042e0b40054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 757466600 1250 757465350 757465367
    0x207030b0912030f0702030c0d030b011e120b01030213090b040b01030e1c1407030c0203060c040f0b0d020d0501060c1e030509040218030706181505160507120308010312 74
    0x10b440c014401d2011440203980168800d070403441c2c500440c1d140c0f605211100b070134400d4121001c070109a80e40d044510382c4d6080959103c5403039030b03118440e003640c0d540c44000d001c5141d0100603090b80c996a1556603a070340d01039811503100c141c200f40c607440b03d290740b18032843c00b034040000118060741c1000c11406542d4003d02403060084400d8002d00114101c2d640c1d410340c026403003402e140400000200c00009854040700403e00030f0300980d6204c0b2000000d0051500d4840d0240c0241d1907544108020402040e2140e103c4042c0d522948806507201c042108003000b1b0f00480009202480c038150000403429001000488000d22a101c400107209564039a89540c07002d08000bd000f18004202003922460a40d0040c68011414003003264035071000000f09240044581001022130010f02d83d02d200f0903101d0703000c90020803016030001601c9440707a800800f6409136646280c100700c0e89244200800c002401150302409510916040c081c06509008013098401e03c002c0d14150301030141d0b101580e00c03400c400f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 757467850 1250 757466600 757466623
    0x20c07080a081e0702040609020c0f0c010806040c0207080d0203030609010f0b030703020d090b0411010e0d020a26010e01390815060705010903080f040f03050f0c0d0207030b09 77
    0x101030400503c11120910707542103103030384400c0d00010094040140d440d44104030280203c42c00050300c41078100c540c42d00e40701018229101c02d9000b01d8a128842e0391001c1095400442034501068022484030180d161840ca900b050000d030003480f52072191941e000001e144580700c2110700108990361500d61045201d00c0c2c2c01509010902080001c01e024003e40042c001261291000510800c01c1d407a500c0155005403012940b205601c00c000407a036a00075010320b40c07840708032010700104100e0790002e10b0f683c04a100302a030a007203109000191011801880350b003050700400901052106500f064000c10200e0300f48200348045013807841d0811824184500f0482d000e00b01c1100800719210141c400c160000d0651003225841c034051169900c80c00054010a4440d03800828000060328000d1f00b4260020986444020020b0421000c52032107480035280395054204140c2d1248001c010100c21b00c540e44d00100707640714a0f030211824036070004c4c0d00d004503409481208000d844507904d41c3c3d22040326114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 757469100 1250 757467850 757467863
    0x307020c090129071b092403020d050115030b1b040303082a12010e1e0c0f0d05010b03060a0b180f03011b050c0d0c0305120a0b090a020c07080a 63
    0x81120300410307440e0400000d62090005641441007540d505c0c81d401c49201d0301c109948020300740c01c214039080c9004000d10b0300d940b0203c41c20b030503681c2031a8202401c0b061202a1041c000c4138400d0050040079070041c001c6080003c82c1104864a90a1101030003e00f5941c00d683c02c0900c041840c40c8198400070384065a40c159110002929648500c5120ba90111491089401c100d000c1030038000b46200107101929000c5440c0034158548081d107418050014404d038031113400780c03610720f044000090000303030b104020318041c070b407241e00310902c2040a02072180c2d45160036140900200b0703116030800240d403044108445030340f101a1a07a02c406c1c1039010b04100c0c0c0003c82021482000c10389807a05030b000342030501400000380003000b04c841000080569080c2c0022030800a20662060030610614039202001d0900144581d02c5a03001062171180034030300c1424540c1000442c0341c05820b5007203184030382c10042c020401c42c00c00300ca86400070b5103d00005070107031207080b600140440d004a50318010316000076 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 757470350 1250 757469100 757469129
    0x60f060907021002040f090e0d020316060b060a0903021003090c0612020706050a2c07030b090c030109060f0b0306041106031f08160503061b2b020307020c0901 70
    0x340281140c0c050810002e5000d4100c8494403409140b02401c014082c40b031003680712501d000600790450b0001d0185001030740110310401200c5070000200c50070b05140643c0f034110070307144d800c260005040c403281c1a070b0f00c000002a42d10400b41d020b1490415a80201c44030030b82c10b554080241c040b950989801409000380700e4003003214500905940b2a00310f0100d4015140815a5950404071082150701d850642d13603d90307501c001c0700c8034903050070308494003101980f03000c417000d0083c50b036902c11a200041020032028005810344006012a40043e10003800912a01c0030918085c0080d00405c1c403009a4140f45c1010481180b0300080d2a07070056411210840701e1040b03170018005207900040c03208000160310801c0034103091140da4100004c229030f001402c100c60400306014a0320750303150f00942c425070103039060050101c42c8018100031810182929070b41c2e001c0402d5005d21480011280c0d2051586420f008a010505500114481d0825500b5589140005801c02644060030b0264030400c10104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 757471600 1250 757470350 757470361
    0x110307121a09090109021f0801150e0f0604180b0f0a060503060d08040f080c040606050307050d0b01140f1803030a02060a09031e0c0c050a05031015090203090609060108060f 76
    0x154000e4010000f80004030310034401e500480e444600031003100d00c8036040b8041060606510070101ca000d04400c0660040e801c030300e00401400380d16120f124034401c148804003102c0c3da44da0202200c0080c048bc040d04204060040d29040c000c001c01c40c003090003000c001c0c070801100c4c61700640d10000c0d40c0803034031941d04640b1110f051100c241c26102c801c480120301040081608415035156000504014004042100c5080140400d4812942c002e1051004c01d0003405045500201516410314042d40006450fa22048c01203d041c51080d80c180d24450f4000744031001007603803200401d000221307440d0700503116484100745907592080c025281c0c0143c2103000461b01208072504104005400f9181411680d80da68a415425104004548011030a1010302c1c0c0100040308010100402080344c5400b1601e18100100361139006400c04005c20a694031104282d49908880b074202824488004645914044900d242c4c0c03814203550300328043c81400f000040700440016171901c200410445444540c850 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 757472850 1250 757471600 757471609
    0x180108100e0136050f07080f0102040609060f020a06110403060b0d170c030d0c0804140f0c1306080601080705010206010e132306040305190e181009110307121a 70
    0xc03d041e0102404680d800c075000c00c2c420050b41c0c1201e40314030050200240340003811443d00c0c54040380040d06174010301c030400280f504074000c0e408452035030409000c0103928042c120700b00034983d4002482d00c1c0c0307042041c00d00c81d00c03400e010b00f0a881c4200c2003004030004080411015a4940c0c10080000c00c102d134900a400d0400005080e000300b40c54203c0c0c0c2402c080000e01d030b0580b441d10103074100081c40c020800050004150403548540801009860048095003500744c45070320044d031803400b4440c0040300d0304101007a83c0c03102000300046000d4802c1e55850300d24182e02d80085100d594018411078001060351500c070902140030b4110041403406424095031580c244606030f052070507460b140c6c4030860601990034000144211303c20307581d0981e101003212400b8145111081ca59041080486442c81c258441000c000e10641e03c00510202650b108405409440325507041001c0017030928018650401ca141c000d58040c0c1d1050b15001210004680b403801242d030000b805d210b1215540303081140c076041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 757474100 1250 757472850 757472921
    0xe0a080c12032104020a05091003061503020a1503051602100c110607120c1b060207050a0c030c0920070f1e080408060f040b15180108100e01 62
    0x41080c00c1e203050100079101031440e050440400201d210f120030411007140740007014000900000c4603404200e08001c0480a101d001c42e00004042d50703075462503000c41e0120350001c08001c590040074101642e44520b40c400300702208082d81c10100303092201150990440420340c070201c06095005002225800d00c0320805040042480b4062040c05080c0222042040c456188600801d8483c0301540104603130b02c0c0208c0c2d24403004001000307010241420b208482642040f00745801a00c0540c40b405141400350400c0030780c04009104441005000007080741d280d101100f250010f04040100e909000903080e00e43c5000728082ea00848104906400038120400036084e040c02004601020303c684d6442c084500404042640c0c6108040760400042000308038099000c1c00d21401ca16140c2450390b80d1002c4c440003e050309181e140519a0fa103841c1d15040c0015050202e0340c400500030f9691910000d0700d82e103006008905c014140304030030f110390f4414010f55043e040c14103e40b03540005a891414200407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 757475350 1250 757474100 757474129
    0x9060904020d03051303060204080f0f0610030201180506030720071202040515060c01060f05060a05030c0304050a02180f1305121c02040906061b0f060b010509100f0e0a080c 76
    0x107014000030007c544e41e031000d080a407803448000c0c4041000d001000b490f104002c0c1c4502141d601400070800c2d10300c4070304080001c90340e080c2085101d01c03100081d6103240c405540c2025801c600040100604513070321040440810006c2454004400b080441d03450311658140501c4c00c0c80700c000520700c1c0043c2070940c0448c1c1d10000c85d00840040315071180014410b5400000009000d030b441d01c5080c0000ba00d500d0290000380750440d00b07039181114905c03001d070840c040200410b04c0c0060110014080c040d050100700852607004095030b000d031010348042400b040064032100789505405000070108801c3c0b24020b010b294104009000400601c0380b5207031300e40d003c0841c84c0ba00b10390400e6044801c1080d40050b10181c10b21a5000c101c803410007000504200705003031100c0ca04000c610551000c64a00010012410781224001c50b0b0320340070400503503880c071400d0b00003904032020301c81c99014207900400c40aa03054241d5a5000105402403c00c92030354407074011010786400c072149142e0070b89044001c404651 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 757476600 1250 757475350 757475377
    0x90308030a090b0f011e0e04030509220204170a030c14160b0301032d020d1a040c0302030120030a270b160906050a030c0905040e01020909060904020d0305 68
    0x203081c41d43c84100080c01a201802131100407001444138800d1420740c2140108642ca01100e09861704c940c070460500b000d04081d0502a00180d640c10b65181c4104050b11060f80304101d0034880815403003d0000d5000e0300c9140d088080d01c40c04c030140b5580100b0700c4130040b03400d41d80e0f01e102c50410341c94a00740d44500d800b10000922038800c01c1c1881041c0c00451000034650b61118907203a41c95810324000103500a03040521000410401d202d5600d840116009000c0c0c059540419000c440c2c07a081050502c4d1007003100c2c020880008010811001142500c00c0d43e20a400038407112107944180c1000d15180c1d501d6083c80c4100b400010a00c1599a00c04241c03281404010520704e4540c01e1a40548101070109441c00d560b014208010390b4005d0008000c20003d0b4a0901401307898083d0003401030041c0c034040e104150715000c0e2019110b05c2103081c00003408000300308014000c03000b80312034000e500c4507420340d00440e21580043c0051a00f0b8200c80d11450300030b03004c1c00150145581c100c1d910360105803003e003117 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 757477850 1250 757476600 757476611
    0x2a060f05090f0441160c050106050409050f010b01020c06040314010f020a02330a0509011d010f060b07121202130f06120e0309040c020304080109110a0b0901090308030a 74
    0x45404c1c1d0240c14842c081103120b851200044100950304540307008000f13000c0001c1d400305001d0407020480b80310210881c18038000700400f01c00d1a1907800742804e5071044d17900a090012171414424041101c81042c4404002040182042001640c85041440c40258009801d200800204800407a20b014240c0c0c04000014406444000c0030200d810950001c0b0050b4080b04010041c40e44a01c0001940d10042c1d80003903140008885030781011038001c01040b40981c5a201048112000750480ca0140d1805505000100e00002d1400c2c002c04e00c5048a018a030704008000502240c0c4000300e5442c142c01452412440056040940c0c0b040d0800110b03070341c03084d400c22044031641d0824003034501401c4002c07001c04504d454240000c001c02c19100a80d529a46410118139904a0010071101c04c07840a8802281d261008035040c1e095026075441031003c0d500b0980380c20104042c51118506640046400e80d290945a0400c5020790159610040c0414031001050010032000c40c0550781c013a0155401044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 757479100 1250 757477850 757477871
    0x11209020312070b15130b030a0b0c130909050c010f0918020901080a05093c070f0f060f05030a0b0d05060103020405180a020f06072a060f05090f04 65
    0xb0b048030440302c0c00a5080d01040a00030440c1d151203ca0308261803200001d158000000001d41c5841c481104034040c56503944201c155450510826011f150800340390145450400c0317407a0344070f41c0b1031281d00180d80071910780030520f45407500c5600610780e0810b0017003000d950001c00640e0480241a60141442042100064640f14041e04135920440740c0c000503881c0d03100360780003401810000d4840c8002a080004201a00800041006011404d11480950810784c08800c4020398950030405000944004407056a0381d07000070035400321110008030382c130915a540c00c800300c2ca20080c024070001800511280c0665449000903642010800600103514186400010715105940800311030541080d80100709506c2c0510074a07a01081e600d1a8420801d100c1c42e205840344040c240c0244509490000ca56a0b6210f09080da11450361080076042c84151070400c4010b000c9900960b903081e503034010000324246105400984c89a8055102c5600b800d0040d4100715190800050558100d99244e0300c555 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 757480350 1250 757479100 757479103
    0x4090e0c060c010b0f0d0f020f04020d0e030414030d17070e0d11130612061107052b170106033c0e011107020909031216080a0605030c0112090203 64
    0x2c440000701000158500c1030f60140b01611071008020380c400ca00591040b03012031511803268a00342e50403110355003004c2466001600078000c1d0040b6403200c901d440240000d503030001008000b1307101c0c4400c904001851100c105a900c100b04948070300003420040c0300c6c10401d80803454980d0046030604058503201d00c02408a48080c01c007480c00c0c7e9130405855400021400c0c610070403100455100401d10006040070502c1082a50b00700000340442c0c1c3c0c0e41494090401c40d0b03002d48840542c001c041d036019691419045803a81c0c4450002c01011485041c14007120340100c15414a60550a02007187c07603182c5079080d40100ae20712113403201111a00440c10400d90000b2440900c0c182e460041500c020201c071280c01121810100c60b0b00c81e0303240408208036a441102a07400b40c9504035040c41c45a6140340d04e0f01c2c207501403200400299440d2206108000d0b40020082c1302c0b6122995410815560740c5643d0019074104e40300d0a030f099048290a2145544512000004003c810802140c601243e5004c207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 757481600 1250 757480350 757480357
    0x60711090c04030b061f0e0310141b18010807020f0109061a040b0906091b070f03122307020a1b050103231f030609030c030f0c030504090e0c06 63
    0x204100074000070180308200c030444409421200a03542000010700c1e000040116010f4246403a00344210000004059501000354142c0350300b0130103086c00ba80c4c0034090820040032080e115201103030106070300300e8403030029541501c110028600c08654910b002c080103464006015000c00c0441c0500003015540346e1090207602da4a41c403e0314009181180303d0035500c00c0c8e010060985101e9800d004c00d00d02945d0b54294040d40011089032810029102c21031014100490402c09007243e0b40049155000d000a12940303402c480c0c00303525440342624120408000320b940203543e290030002d040c5c01c081202c40d8036500d49984141075004031000b000c0c0945900340010248005410895030201e024041c950349070180c2d0324a0050604260802d1003132064042c0f8296000b0406134141c0c500703004106864801260250056030440c2081007000f003035040003011f000b11600254045500c1c0154495844d225080c24800d090305070f9211400c00f414a18041c0c00342c003914400741c200f44281e5980f1440d959a00008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 757482850 1250 757481600 757481611
    0x105041e020a180807080a12030905070306090b1003020303030f0916090618060b0a1b0816030314100b07080903010c050d06090c09090c030906290402031506071109 72
    0xc4000c00c07900a201a440b030f40840c0c03c40341040d0400704040100560005030b0b08100741c0d01400e45048103400103c11070042603c1c0384043c141e4444c440001091103041c1d84a28803241c06a40c01a545590780c0c040d1320028045840000e40651003000000e210402c644941c6400c51072442c103495030504412806481910b4940000e008142d446200300714003241c43e410003c01c1c514664042c401c1b03d16040308290107000d101010320601c48a1a411400102035040c05070240354410380b9183c43c0c1180c3d4044c22150b20a9900842c00b21385025101040c210741d0040403440303644c3c002113884a2a00b0400c025031141c004000840e44003205110308103140e542030084040130001d44d51041d072200111070881c0150781d901d03841580014584064100000c0d8010407040c203039103003402c003c0b5a10102201c11001040c40220240c0414030f09040164044181100c0201001000d950801c149100d0000c2008074403055408900104500d040f04880d0300341070000e0002140620358005620840f00086107001d20100c82 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 757484100 1250 757482850 757482857
    0x90504110c0c0f0a0e0c0c01020a09090c1713020120010902280608131406070f050f031b120108030a110604030903080d110403050102070506070f080105041e020a 71
    0x40c0c441c00900c00b0020382000a608550f0f401d110026030f00441c006038a21701034051180b0b4840c002a038469150005ca81154100000855458a41358001404002c0700d0003031180c002e007403844003e1602c1c0300d03c240107201c80b0303d268100e410b40c42e0a900c100701aa01081d041f8140003409507240203007062070031180010441c42d40003181200d80e5104010701d041200c02101c04502d4040b8034082c1001c20f8848090503101716007000141911460b401524600079054000d1002041c540320914610010442c1c50058083d07845030401c900c00818199558040c0c900c1c15102c0400070720000742c8900141c2441041d12105078400c61a03c103108842101d0320400743c00c201010b0740001030090700168811304510403014028080e0155081641d00248401418030000e800c415010825150444195104d4542404103500042d540c940e01e103050b6000c2e4000e100c05551601505000444c40d9004071049071480c2c2c600ea5442025a00348010070004002c00e140c2180d0410b0043c2a5001920082c802410745682646 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 757485350 1250 757484100 757484107
    0x411040f0e01120b0703091407030b0601090305060c09120f0a0b06040204030201051902010204080d021507050c100f0b09010b090411160803150918010b060a050405010e0109050411 79
    0x65803040d0960103644201e00c240500c0c401000300701c2960100b0480e0660083c0d1010080c0c8800b04200c000e40300440300a400940000580f240a03040005e004040300d11030080a0b50960703400e030043d284803d880c8005081c90308103400161201207248020040320800500e00401c3c0360700f181541c0c0c9000c2020180032074992101034140c05104a030f00c80d10740e01c660102e5065250a056a00003442070003180a00003903100122a8100700c1c6d8000e4042c2c0c2c01070003084c1c0484480307014044009607192034211060722103504110220707840501c100304a0705001c0120f002841100040c0e11114000c2a00c04450182165111940d0b0502d5454481391402407404442554507039486000700401c95500c00404204c04900300403499803d00140c51011003030760090b42131516035413100e41803504101d0011720554800c2c014001c106c00320007003030b8641d8841c40b4400020002c060100040c05100d20030040080007069081c08104135540c846e40203990b03226011f262400d07030640d40b40041803d890355490070b6046c080307011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 757486600 1250 757485350 757485359
    0x3100608040f12021f09080f030703110c031206030c091f03060f0b1c12230706020c070f0311090a140103031e0509090f0402060417102409020c0705041104 68
    0x3008144483c0c1e80540104040c1c03445a440d21664400c40234401c070b0b07000000c0000313140c4034000d50240005004101140e079803004a00c113100e48a50140c5580e00c944034002002c60748a080000d064150250054924481c54403a40090742d80010f110000391503004000d8400b08c00560b25009006640c843c501c404204027854400b00001504600f03e615000913103091a034001c50300b58480500d20502905100700342e04401034115441d110303c011803183c82540000c0203010041c07641d0080040e6241c00098495050700c0d240c41c00c4d5500b2941c4409406565814035461181c40c08403111034100c24030000000d41503085c0d0400c203164403400d074010b60202e03a90005181d640e80700304180002c42c021924215142404072000130701203c2c009406030344c1240243d00000c0c110345074070044901501920240390340c29150445441e647d02d140b002c22a40c010b0074058030056500340c0b4140c0040c1401c840f4001d101072410320030074078002d4000031003146c0345126203480000d1a403182c0c4240c0d1074110301c880303090741d450341032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 757487850 1250 757486600 757486633
    0x30605090a020a0906031107080f0304030311041505090406080a2f0d1509051b0a0f0b0702010309020f0d1415040804121a09010c0e0603100608040f1202 67
    0xc20703040519004002c2050f0ba00e0b400701d640e4043c0c92080c240003d606500724030400041c058104000d11444000500303580301c20b203a00c091403040344650f600b400f2140007264400494041e51007440440f0700b0f0080c003288840e026801030980c03400040d0000643c0350343c414403186043d40b0400185c0705480682a81d00744204412452040d0741c0b42d401c1814905a502000308130707041c49010340640380000040304824103402c55001503452740e800204640b611030b55070030452001a00a801e45104d208840030004018620301c1d0b041c0301703c400c2080d40d541480000c0d001940600f070200d0b4101c4e0710200b1100c0b4110a682cad6145801c0e100c40c020b22024134524440e6165520b460042d000c1c411400700c200c41008000f8039041c0485066030441d80084100041500c1c00c1d0903030f00801c00003200c1180c00481009460001584181000d912039520100d68507121070500026100a5444407210205905c090003154004d89405810510540d00c010311810280c0790b51102c80ea40e1b22a09005800640f1b01c5061000d2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 757489100 1250 757487850 757487869
    0x18020703031e0207120801060e06070807050114070f0801031104091103011109091f2c07030f2d1d010e01060326030a0e030c0a0311121314120a03030605 67
    0x10f05040c1b614582d41084000341540401c4100300d4410800000c0000c10000e00c5415118102e03401002801000c0380310241140ca031604517519000107801c05000c0e40b2144c494034003e41280d8201c0a030b0f6801c807220b0020b02c0068412200c09a91b20341040d001030030251000d1050207038891145003802d03118441c85c010054054000b0741405420900040300c003401080c1400941d04840301204403500d40c07440740c42c0403040359462607441c002e50280541000708240e091742003100210f071107a60030400401d050400b618049200c0c0603034031441c0d44030000404034000070782c8003954149591b003000030488243e80c401d5007900d1414000c030701d450751216010820400301c4008000440d41030b180740003e1698846081100e400028030184c0110b84400b1450001d41742032044a200030045410703103031541030605015100c02c42c6162b416080c0d01c140040b0488840c03140e001c1c0c030240c11000c000c10b01c4182c900036010391420781c84584160b1290032003600844a000400100840034400c0e200801c24500d81801c124400300c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 757490350 1250 757489100 757489133
    0x6091c0311090a060f120506060a26010303122414010309290906010b0d1a100206090c04020412140c120d020634140705100609020418020703031e0207 66
    0x50811f0203000703481d1744810580700c80d40000d140010404a440c8880c4000e081c0c00c6150341c102c00100e100120074076500424848540d001c11405102048112225040b0084132060030312000c400001c1c188003203030310f2074000740d4100c00524002c02c03101159100d808044402d100d054185072040e01c10f00300507294200e40e80c0d41c00481c07a80a440290704d010304240c1507108184002100d02e584942590f48071101d58940c0a10100103003014010151084003c0c2d61180e0680384801248201e04501d0014900343c0222400e454104444808008280d541e002c44902a0040e0703002500403145541c885407105031000c080d88070004020240400f035a207000e0f05018001d800c412546014006542c504030541141c0c00d030308135041c0008a000f450903102120032a200100075050a08001424001e00c00c00046022340c2042040b0300704001c41c4d903140c0b050100e1165102c1c8580003004e00828855203026540906015800f0f0708000c1000035240b20a110a010300c03d40d40301b0710940c013082000a224200a440302c00c00b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 757491600 1250 757490350 757490387
    0xf0609110405031207240b010e0f0105070b0c041505040614040303050f091201020c010902010e0f01080115120f020315090f06120f07060905010206091c0311090a060f 73
    0x1d0304050110782ca4031401074595445000004500c41002103d040300354039000b0070003041081403c440f1801c0c1c054034204550a0004602400c40511440c001014100c0010143c58491419810342e9848032001d0307006000341d60b5500103100014a46046045610b803030f04540c0d4600d81c0d110f04207078001d4043d0a4030381141074540d0042c0b00605c00280c000d0300f00ca244811501c5140d8603030290b4400075142d10104940b0100700e50021400d410030800540207148030030310036290710031f0742561803090110703071180e9414041c000340c402801081215600c94592980802c3d900d4007140306c00343d0b00f45035820756094010044609a00104001700b840900a2488030030301c0c03c0b50b2070003071800c0008142c28903400280007035214001c09510500340320b000f0010032a80c417411909a034141c51391018054200c031203d126441c054003c0d50f001403221540440d00c078150807140c0005441e24003084030214020b051034860b0305420720382080100c02030390390050034000420380e580e0b4091244013140701c000d180b0300d550400c55081c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 757492850 1250 757491600 757491607
    0x50c0702091b030a090f020d0309050a0503060f13031701060f03110c100c0513030804030c08030a05030103110a0503060f0106020709020703020a020f0406030b04030903020102122502040608010f060911 88
    0x24101d45000c4030b4000c04c00340004162907215080c141d84180185200030b5000c0502004032042681090108040b80d008031407845a02c0c1d9200e044c1a20307540c040b640c160400d401540000e01d000043d1a4000d540380c001e1130300101c60f0425800c0051191000e81041e0007107480c100700000b40544c076004881800490349541402d02c0c2000c006103a0b91410300c0c034002003140d1191641d8020622810a0382c03800540e9241d2550f0142e544c0c10400000c0d880350105a648240b020004904041c0c0003041341c40304005907541d945140e19507161002885142494240e104078920000030382d555003001041e02078500c0801e00310396549401000392420201d680308410003401403101c0004250045800c50b01d558055905100410000c000240101525000104602103800510ec00d142d8403070f1000003600d1007a021a05d100c0c02c03040c03c0c0b9205014005803451501240105501d0140b030518820080700e20141000c41c4040d21180c415003540c1803150030450321591580f00f080040d0480c0158200c01c0c00080c01b9514 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 757494100 1250 757492850 757492891
    0xc0606120606120c0d0c0e060d0f0803190c0806010305180307030e030304090c0503010e1f26011d15090303070c03212406050415030609050c070209 65
    0x8503044002d0200b403050b0380c541062070301c001c010700030000d01c02001030040b00203104078940303034030750034868081c0444898406000a825050000100036a140c1085032005400032540c0d03125120b50004241d1180c100c0110354240c200442070094454801040d15100400d103004000102118001414200705034200304a910446d0320203c01ca40f2071036050b141800c422100d02c3d011a1551046510039295149001200c1103902e51040246050707d000c0d0304c1543c440c2d19140b013481499030705902000b010341d003928410440740490584000d10b55913021107080002c58504d4105007112400f8890411102480034000f1111000f4028003810001c120b0b816040380c1050703800e103603903408001c24840034403082c40c8500042c507018802c2141055811141d200451000005c120060042c0003001c8140e00d40b410540b030a091080076901040da44540d0300d00781064503100c0056203080511088005040d80e80e080466070501c3ca010342d500c00d400c0b42a200e50b66036200c1c81842100c620040001401e29280b000c0740c0c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 757495350 1250 757494100 757494103
    0x20d1a032103070c050c0310090317070207060309240c030605040e03090108071202040f0608010b16032f0303060f0d110d0303020c031b100b060702060f0f070303020c060612 76
    0x30f4000041303141c158544100c07407510078601345c20003a8259142c4100d1a4410307020f1042c3d003001040c140300f540c031079a400303040350303403171114a4000d072107030381c00741c2c1042805100c0144a030384040341481c0038511503001030601c881c81c041e1101625a01d0002191203031080b03441e00d9010b0007070700000c3c002550200718400d0351501d0b40b0f40301d010702c40d4024100301c130441c00310304d0440c4110301c1214494a030354811552595109035540c030489a0303209203000305044500010304a100b48040d2085520b00c0d0200a03042c040a990407a2218100c006492007180d201d06d6941012032010350054a0b000c010008503501d0902c003042004d150049524184107480b121a94400504011580c44022800307540c070160b140e4042c034098001e4041d203107030b5400e1840b01188100075507010611b2400c0001d10314050f980c0000fa0107050005480c100300d5280d400c200304000074001803c11100425281808400d11381c10a0045000e8044c994030a03c41900001e0f00400c2200103281c05000755074200d8801c441c50000c0680e40300145 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 757496600 1250 757495350 757495357
    0x3040e0609070e060f1207050702060711011b03050d1d070b0a0302270112052a0403060504120809070302090604090201020c1906090b0f0418020d1a0321 67
    0x40c001d050301804140c0843c0030f082d400700c1440008000649402e80308800c02d0b0711b0f4014034500583e45e070a8501184500c0e001e80c0c00c90f00001d030064440707443e101682e04e500200c004200216070401480381050791825122405054040381701c3e540e42607441080d80d05600030b890031344c1076202c00b081c0320100213203420000150180850302d54851440d2224800c280c19030080c041c00b0700811040c0100704200f1215400c1040396029440300341c8a88241000d882d02e144115882201d132080301102009402d0040c1000105141c100c203541400c161800f41c41c0e0780c4400a887d8107407001c4855900c0700c21280000c031307040035a2951200300340005100191641d00061000000584802d00640d03403802c1442c00e59100303000a1070b10410183c000c12140002094140c00c50a01d42302d000c1c00102d140380085241d890b540200d43c00038110858050809090810a00d5203000811004507125820020100c2581242c0180500815450000d80c10b00c4414000d250528a40c00c08400c3d0031a102c0115200c248842c400b40d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 757497850 1250 757496600 757496611
    0x203070c120207091a0913080405040905100c0f0f0c0f021e12100b010512010302010509030717071409040203060a02031b04120204290415090e160803040e 68
    0x81200284008205906080700d5800c1803d649081404204001707106024005071400241d800100d603940321440150068411100100b49140c100b00802440c03a00340c04c1b420b08940a0f005403a8821041c4140c0f80848405400701c3c4081004816615000d80e0095840d0120003840d04045682e4141c0756200c0b0b44c03048500200070b02ca078a0008002400c03100c402c998000c1c07200302400c1d991706840200811a070b207440f107001034440141060713680c44242d44102d090b50b5030f41c050200300f401d007642150300664290b0414040b1071740500c82c804c40001e005440c81d110081d40d1400c180030304421424028004d04ea030002200d0b040c00342400030140300c0181c600080281d4096249800182c581e04c446909940359160700d0b03568910f6000218010900b121420b060740012482183c0c108a080c00050f42048070f082042d05599200b1501c0d00190900d0038140c00c5800b0780e000040d1241c4446884449120032104900c00c3c07100950700445040c0c0513407085400200103083e60710010f5040c989410001c00d200c0000901 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 757499100 1250 757497850 757497863
    0xc05060f10030f0c050f040209060706091106032401050a0807110f030c010518010b030d050a020a0c060e12060912090319031e050a0e0d020127090f0203070c 69
    0x81d1030020000801020303540c85805080c403d9054240012501340c1801241d00c180c584880d910f0440c40c1070b00c00c540d000e200140049081c80c032542c441500030001302c0402d03030342000b8003a40b0900c5a03490710001e51107210101c80742560744420300e4500760300310301c5840c00038107100040084507452600005130691000072440c1050780036080c280f065081400e100c802e0000c9100c046641010b035074041d08000e208034652084000021685040c0a09a5003841071458141d0003084c41241c2440c8078500900d8900c3c0c0b6401215a0810300b0760354030010382a507500c0100010708584209800f8606185440d4510113414002e2041d8140b103401d0303075240c02260034005a0300200042051a580303043c444851200a984084500041a4140030b01751120b865030303401400721001c0303035003441c64002d030140c174049034040e598410310041b50014460311032440304069050096044007006c03021304994212510842e152082140d041c940400602030710203a243c082c00d42c40c0148108408240d0014481741d020f6000076 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 757500350 1250 757499100 757499131
    0x31104110301170a0506010b0909130209070f0306050907081603141f0e09030705070e040510110903061501020106050f100315122306040f081e120f070c0506 69
    0x110301601d13003003889800030300301e00a48000040072024034015040c0350f00151070105a039503c2c00c016010382c00700848025400307995240400d03d40c034818a48002a03500714140003800d15141c400160a0340c401f00c803034a001504650802105182a8803a0500c0001c2d60406011100800c0504000c0050040180d99203000718065070320000c40354007148008064440009000c5d003020042103499034080a0107444500c01d034007000a04031400302c00c862003190070034041c1c04035461103d280e42c01f0382441c150310720f580f03001405002c040756000d0111502501141c2c1c440480360b40403a00190a484095215906c1a01501070941664890383d400c90507554040c40c7c001020044c0c1041c5202c0401c01c1d03040107000411a220070420030284029060b4044d400d5800810400070110040340e8800e002c58004002604032810350380060a550007a00c86030104009044540c400965035400e02d4101c403004418694401c014440100541c1e82c2d0280c000e6a207103854403262203a0b80314503941c1d0728090312501d070072080c50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 757501600 1250 757500350 757500389
    0x60c17040210080901021c0e07080d050301050105070c09020d0b011115151c03020a02031605330f0414030d0507111c080c0c0102010c120509030706060e01031104110301 74
    0x80d412160406c1004084d9054071001091003002231420a01100c402c2c82503030030211346507030002480d0416640c15079940d41b13036a08102c01142d00f03400044040b42c0c01e00501001080801103400980031901400e240080c1254040c1d0005141e822040e56840c0684c000000500344a00f40140c0d81c0d500c0300e6200c105c035610b2028400803605007007201000c01150000100c00c0f508055022400c80c03040c9008804480b030300b1040c120704c1c0314410601d103e0385600806100d0340300c120340089808417006003e04800f181034880303e03d9801520b80d109404c940c500c01c400007014800442a11404200380d6025001000c0710030684078041c010307104d4503d000c0c0807400e5420311650a651843c25607074850b2801c4800340020401c514048070650448003c50807580500d0303100d42c4280d44140310309441c00044d43d0300c20805200391a00b180040c0409410b4031074500040000304042003840c0108001131a050041040961442c02c00c140203030260035007544503509107901209038445c0c2d01d042c0ca0560f426101c015502302142c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 757502850 1250 757501600 757501603
    0x90a1a0d020d0503130303030e0d090303080703091b03030201180206040303200d0302210702060a020a0302131d2413020c0a2d020d060c050c0a060c170402100809 71
    0x42c12004200e48800540021a1440b1405102c00c50707200e80c6003800a80c00405a03242c5070040480c0404c0042e0521404002091007240307030700c0d00b04810f410700240c07d0f00b00d5100c41c2110314201444201e80c003070f440740c10401c00d87c2c24882e038001003070310444042a10300c0350740c00504070380b18621001d0100800c006c087c100c0f003207040e00f11040966605d03046171003401280350301030007070340140c4200c0d5181c0d20132600c2c0701701d0f01184030456441540c80d640600003d40d1807100d064001d40100042c1410141d0a210000003100c400d103071034002e007611241403601501411004a6206001041290005c0710540d02c03103800c00001c440300310984070446d00c0c0416403940040c040020b0280c0070020107140318040010045c0428080600055039004143e43c0c85002e03107014000f0065000d00000350003540c0c21a41102040b0b582c1d01002246136036140c451324082e0000c18161505000d601d082d505035a0710016400000d800841030b500e00c21104210002c0c61800d50001010950055500c800b40186140081c003801070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 757504100 1250 757502850 757502869
    0xe010b0f120106080f18060601050f0c0105091507020f12160602031f09090305090d020111060903130609050f2b050a02090f09101109040504050c090a1a0d02 69
    0x954010750300942e518240101140b500f9207000500016440c04204504e242c05040c14001072640000d18051712044011039a036030041a08441e102c2c414004403428060a009282c000c9640c040140016a0211859894990060030000c190350103014041362101020814080c0803c0740300d80a92078080c00c001804a01030940f80003412030b41300200b001511201071102c00803074008802540401d50f2658040401c0760f070f00760f1000d0040350040c4110380c55440c5c0609481d008a20604d0b10062051008681c680303411429074030000c5942010414082c07180340003912500802c282c0c40c0902034a0715140118480940d09a130440c019000c0c20300c02d00000200501500c00216000c0440a0f003a0040c2041600e13640304030800c074800c10301007012500000401c0007141c00340e20084003511302c00044511403030061420a84903904440b05101c0d1408541e1944102d91043c1d02850103070201d0b03072072203040000d0803000400c2c1649003881c01c1f0201020b1140172540d0070203e5004d503070030940c003040c2e0b0000590000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 757505350 1250 757504100 757504117
    0x307060c12090b0d050a0b030d020c09061305130302010b090105060901050c21071b030b060d050a0f060c0305100e0a0b04060302040207080a02190b0c03061906030608160e010b0f 78
    0xd0001501321500d404560056118102202c420444403001c0020542c40348401d03000280141c1c841072411001c0c1c60000e003842e030401d04c000d00c02801e80e08035042d41d8003510700c104d40b9480150b845079041d03004d040c1c0a00400c1c80c884400c4480300420760400c0005089805801581c904000001c00e00008c1030104003e400700211380e41c103030b040e40d1041c450034142c0d103640031010485004030000e8606015805c2c2c1c041071400d0b0f80d03100584902c82c1d5104001c1c820b40d1540e860741076803184550203064020a5582070109000360180b075001c125a070644002600b650000340c50140003c884c41410040004000c80081c5c100202c50750200ea00d080c0c2400080181c030441e00040d6001d440007d8010800a60000a1000480640a8403c442124207851090b414601005800840300b04001a4840b0b06c00009562115000b05046c111000080517117030000003503003004010a9548100344000070040000102502e26007c034104600d04110b00d1518500040c4078620100c0400310308200041050020340e00c1e00c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 757506600 1250 757505350 757505369
    0x40f0302012901030c020c0f010528030212060d031e2d0e0108160c0c03080711031c0507060c300c03181506090f0207110307060c1209 59
    0xd4405a503248400401070420b901080c41c05140c0f07000c80340081032104581c8002054a81c10804c40801558141d0101c04c0d180c640c101003000c00c41d1200c00d41b0380400c4030844a41e0300142c840032883e90a0704001c002501c040c0c4116070501c020750009510050306502500000c07081c005643d05110300b541c810980e00b18400200010070401d260070f92080301070f034445a80c5590380c07c0c030000c4402c00642c0c561605582c80d00060740103184608210b805541843c1d000c0d44a00c0c41001120303521346450440d07800000c0c04540c50118914001a0b52808014a82d43c410580da07001078440d4030654058014800c0d031800a105030749030034501c072150380a0486041500030400c0c2103000c051020200d069040a84450000f085c1e15203003008920522910828040040f50394040000340056150360801310000054584030546405010507410008c5c004d00a030f1802e0a0f00241e210b50031031401009402210003518003030b90100008114640e440881c01b61080d40181e94500402120b22089070019020b8018401c0f1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 757507850 1250 757506600 757506641
    0x309020609150f1b1603150504051603080717250204020c0a0b070f0509180615041710020c07050904210906020d1427100e0a150503040f030201 63
    0x42c0915101c2401c000080b00c0241c0e8043e070401891130809030240c0c0009868141c921f1036040007141103030301203904940141c2c1101c0007a00c41c144031989003826908201c0d841c01c0d0110b00d0108001c442001540740181140405041c186030240200000c03c08044240c10350002d0601403055403690360407503c041d000c00d0242d0b0002d00650619001c0b440c0c0943d039680006000255000301d0b2842078050b5200150300500c4007000c0b04050307008001d0307800301900c080c0d030040c0e030b01140c005840355a400420080c0710050300c05405c40075032000d40d400c049070580300342d00c45801000400165032000c02d40d003013514411a4445180e860b40d08052858680610a4010003840d032038414940c26080b15070b981c01c6416075400c45034208110f440441d160400982c0096006c0c80074000b0ba40c950b008044150040d0041c02e0710b8a0605034a0000501c01005500e12603021902c80d2044407581c1c01d0198003100600641c601c850040188044014141d1000420140851052000850816100790440e01141000351803210700b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 757509100 1250 757507850 757507867
    0x11d10051803030f03060901060f1e170108100c0c05071a0f0f030f060409120e060702180a15030c141c030905091006020c0d0c0b04080106050a05010309020609150f 72
    0xa4685c41503540742d100e21540f400026101c0d00c55404060300e0041035898032940c0405064449140030600ca40000307002c200c9598542ca8052854118000c00001c40140f04018003e4842c0b41100e4600c0030040070031512484d420040b6400083d260100e600c0702c000d540100e40c4804100c0c1880c004d902c200708201e040018a01c400c801140b020303501440403055064840d8403208108000c880206c1002030451f510b11542d00303070440c000d5504845e0703081c000c3e00e0303070349409055030008449002c3c0c2040304c103220101c0070500c02000414401c68a4080291044007205400d5440b035498425141c031407181104044490820203403110061503404288d0404030818100d60785ca405031000240703000b554020003401000454003010b100c0306000300c604076000f40c03198105550a00c003004084a009035048098018005501c2d003130710005100500300400000340ca2414013081010046c2580c1c400b40c1014285007183c00941d940c1404ca9846410495001c4c50008001564200c10702441d0400c030402d030780118502c03d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 757510350 1250 757509100 757509127
    0x60f1f0605070309050d1113060b1c0605090c0714010902060c030d050604020f0703080915041406100b0a0e01030b1c03091d041407030b15011d1005180303 68
    0x8100d8401e07220100b4880e15907043c02801c0c0c101d4003015104840010301103a9a00341044501308c031108811001c54810b45958440344503507c42042203208000c5583d104046c10070621501d806060100c2c0c10f0f0500d400e2124103032400c1c0c0501c000c09071042d50a5000205c031445c00b58400e107480303903024086580b07e40d01c1090740e907101d0304542881d103101c034140000500140303841d20071500c0c2280040300321410001d540d182198601c0c0c00611320304036803241c0e007c102d8402c0000c0c0d817020f01c1144039034100710400600059103400d100000d0b011005107494104103201d40648102952220035076071800d154207000d0680104d01400102c03041c517400c542001512004501d40c6241c9117001030090b1240d2000e86d5444140058203043d2980e1034070903201c4180460300140450386115008900001110100c5841e5100d100d04140b080c1ea5480c030800103c80c00c0b500d25608604e500809040740d00601000119480204484602c950150002c00c440000d194094224000f07074a480c8d0080541140e0b182d100c861002c170b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 757511600 1250 757510350 757510357
    0xf2d0f151906030b030a0b040b0601232b05100f0506090a09021b01020307030b01030c080402100f12050108010b0f0604080309130e0615040c0c05060f1f0605 69
    0x50482844030005031030305051954981d03000e1080307612440380c01450200304030020072000c00d2541d0f0601820106c40c0104600c00f6106000d85e008821042880c280705002600b01c17090700d51007400294590204a0300c0410341415504003139643c4942404a042141032040120444e40595002502d4070050086a02541206130f00703540200700a0b40c81d85440704100002801030041007580f02074102c40034000c141c042d8020b840ca40b9084c20a8100101c280314986080e80c1040b01e41c000080d40d40c24071080c4540e810300400e43c07002220f041030805400c1c103030041002d5032940b01c400b0050003c81e1441c0e40080303204d80305180d0300f203400c04010049940c5500e421406801402c240354400c0422a409088500e4050102d4080780c0505004610302070084040c42400901049000b40706650703001001100081441064420180448d0005400c1d2920040008030791a00d08030008205000c0211030000e94005681900400d0b00c9008503619910402c21800c0385000420300b4807200c540c11000102d040d08000507 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 757512850 1250 757511600 757511611
    0x9020d050303090f0c12060c092d030606040219030b1c0606030b0c0322030c02040c0804021311090f0402090301060e010815220c08011a180f2d0f 64
    0x117036914448240c003001048661083e903026941c000c803001c06c2041409800405950074098030403201ea0208a521425000002d60702000c410740030b9003012614601805042e62080d4121000c60a20701c60600c50100d10911004000901d82e440300b800c1070956405110104000404400800040b401d10300503010b42100e02c07040313400c0c075144c00c08944100300382000d403407145440107100010022010300e4175149108252043c0d0500048201c0c8001580b114040c16a154255844c0d0004030305040c41440f0000042c140a0000503251205c036010090070b00c0102c90b030300c032030440e4082c101e02070302c02c0064024810f0442ea564503600c4c1401c000b07803c1c070070b09080724101d46000058400b10f07075451442d1103001b0411250300001d1442c0312078281100c0c0c030749031701140c08500429030304442d5500c0e050703c1800c42c0c0c0c0729038248c10305c01507910000b0394138545481d08040c00c1f00c015a1501050421084400803a007000d0003200d400203003008201c1c42d40c00340300d040340c8030701c01144154025410807503207007900c02c54203641 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 757514100 1250 757512850 757512853
    0x501020106050315070813060203010303051206010e0f040c03020405030313152a1a0108030c0c0316120f050a0308040201112b030e010518060618010909020d050303090f 74
    0x1e000440b8940814a88030626403801c18500c5685d401d002120012001410103101c0224811140049101d0388003031400f86205c0d849499071211410000e08111f000107007003034100682d0300d40280740c93f211840c6e01c9014402c181d401098a4500780c1080e00030b03016580100f5090310001c550765800c40002e240c2c0707100312002044074041001803144100e82410042d020085001d00c05240c003107107100c107602e60381c0019001d0028490090003a480e00d240c2ca05081e4408450341d8400b042c81a400c5034103100080032075004800501ca0605800f0018000200522070340780804c56800c135035028442c0154150900d107910409444540c0520314015044050548041c0c0c00100448280002c464002414240390340281085c0907034680111451251071811400c2602007503294a80001c1400013406164040c4c8400d007000c000301240000194640783c001000d09101e95120060310a040d030007019814190341c07100a001c180d100f060300200e442905d580da802021032000101300080c41c030b408a5103d940d843c4420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 757515350 1250 757514100 757514111
    0x30f0f03030c090e010509220308010e010b070506060427290618150d08030105091e180c060a03051b0c120c07050315150a0605071506030b01080705010201 68
    0x2101220300007210300a80100c1e1110394014030680c60111244c0768480f0001041e5609440008c0502e00c0b00b45900b201100451810001401084250001c15024140e41c161490a080e0303582c542c00da848902400d520300450342e0b800d01c9102003a1084620000044c20000000c0d01200c900c0c01d284048007107140030b04c007046119022940c00f204661941d01a0000415002601114407010b08072098091b01d135101103068022228400c0c1c483c51002c280c00c074000c0b04115129854141401803c10004200c1c070b215002180d9010f00040d16450070075003140b4645003810040d00300d040a5803802034020165688008046640480d481e0716400541c4a0f0801e1182c04000346030000c0ea075260350098002d1465139403c11b04c202d01c040a00c1a02524508000e40100c2d038000303980d44046400c10505034448036601000804025540380035101441c803480c02503464102880c902a0003c002e40a02240148541c000b4021135039440d6503900610302458001280340c00559543c0061940d405403885028095400c1c503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 757516600 1250 757515350 757515371
    0xb0f06130e070333050913060509010c17070504031a010815070207060c06020f070b06100e01020a030804111e010219020a091d1606090510021b0307030f0f0303 70
    0x24040d0b05a60200d01414100340c4003c150040881484c0c1c03c82c24640781060b0b20000340c140c3e80c14600c00d004103548040704200749002e040c007005607100100003c909071b04296080502e55440f8000c5190307001e080300035200e1070b20340039000c50382881164009004000b400c03c1030324201c440000f0850484e09910229040d01200107003050f6298000c03110394016030040b080c10003240d03025000c520103040c03040f4030061402d40e4410007821642c20444c000e0355904c1040c02000003d0600341c814034200382e890f00b00071281c903242d400002e41d190201c0ca4018100001100401c0800031100c0740b0068241c0010b02c00a13508601d0a21101e00314086130040d03005100f11510714100082c103004000c80b20340c001e8010411681442e41d40300c068500c0c005040b061030201682503d944409010000c201c5031001d100602c0e142c80d110000b4144141a044580300701d603c1510759003030310b030001035075551078070506078607a0301e028000002130401841d64006010516035030328040800645581060b4418802d480c100b2054621 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 757517850 1250 757516600 757516607
    0x70f240f1a0306070e090601090801021204021203071203180f03020a120509060313080418090c0512100e010608120c060114010f12020d0207210e130b0f06130e07 71
    0x98461602007500e85d00c014100303041c850000c03940900306061103100c80760f40b58181d9003281e10a182256190f603140060008515110000c0125003120f070004506042d0940c03284502420525030500506030346001c01c0003108140c182003052030740c01004036640420103060107515550010021603080070b03c00c9240140601078000c2c0da492902c00b901c01400d5607110480344560900d907110035148080c05101c0091007201c1c0c256401f0441c4113061020540808a28125035418126009244506001c154070707882400006200804803240c40c0c0e0114440c145a8441801881180c0202c1803600a809244200c180010000d1200c0c202100c22950700d40c1e80c5403005058885070409090008501940c10010284901c0c1c1080d030941400c000103182074403400e104d84c103d0344204170480f0780c5d02034440480948488090003000c001000e090031890b070f03260140090f4041c0390320310b51000f40d285d4480c403801c3c03682c641b00f00b03a014204000d045256074410080113990b5a1000e8814824080c0d060b0340001c042511 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 757519100 1250 757517850 757517863
    0x512070f0c030c05030706060824041104090f0611070c0f0e04151103012403050f13030909140402091503030d0b1306060503060102070b070f240f1a03 66
    0x82581d503100940c10550b4102d4607007980210540c0e0f240710600c510004101039101e10703401400110028405a10400c180c03446e0356061140036403040d0f813051f0400c008240d5000401c0303010301c011079000075008031510304654001703448500903100c0c40c81d24107104400311054004048850080c49401301080d51a80041c4102800d8018550022824400708002561601541c1c200045800010890140d031020401c0a80c00983c02400c0c00910008442c1d135102c0c8062020941410626081c4001d280036410341c582404041c000c0500e080003003a20609041c070031100381002d840301e04400c0c0021622031021401000e01510164454071440c804201001110504800310a4002d4040c3d0f040114603c0309100500c034010390946c00041c88a10040f0000c0244180307000741c0000d0322080d40ba410040002860320007a504506152201042414041000d401c40e01810590041c0742d1118002170704030280d419210007040c0b007411070900f8000c0140c81e200b27403c608140328100c0f212a0405040a003055900c40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 757520350 1250 757519100 757519127
    0x3040302060a14040305010510030b360708150907050616020d1e0c030303060b0403020307051002211801170a05070e1e03010b0402040501050f090d080406051207 71
    0xc030402410b01e40c01d000b0002089400f10481905042c503980791201801d5031411901102c40c1030011f002481000030000e109904080384018040c11260061007104014602e104858035a0040e10060010254208001c001900d8542d056070041c0000d42010301000d80141c4080d281409402c0c1d02080a050403011398101c8490f002641c90054403075000d01c021500214070564120103404c082000700c0318000049200ca612601070070501c1c03031450400604540181e007202d0b107039020030041003025076000103000003961800c541089050844c40c100764039041190103000fa080c10b02d9450500c82e4034500700600004013950041c00528030001c0c004640d842501694407400030800d80202d2140c0100b070b17026503805885800c0c0600d260380341c500001e124000c0329140d25503444078030503104100d0a0070b024900c2c0050060b036040d81020b0030180040e000c0e0042e140b1107203001c1c80214600c4895038a9251000800380c00c02e82050b600c64503020003d04a61000440d20294145580400c0308103124203904076142 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 757521600 1250 757520350 757520359
    0x715090510022d161502060108212203080c010f0506012124060914030604031823100804080405060901030e0708061603020307090608071b0c050a050303040302 70
    0x18940d4150500c0000c004000b000f120f485881302000d14024540e81c048040c02030310388103049072140080b00030b28020058220030425004600c40840300e01c001244400c11404902c0b40e2921401001080b41c47c81003103002510101101002c00028080044010303d401204a4000c1c00100c0c08501540180c03402681c20352300181444400e070406900d40006c0c0d40d040e8002c03180103d03400c4401101481c11407424500c1001d090f0784128100640381c0c109107064000d0004443c51952024080700080d299000100040c003484070081d090f07a20151980d42c0c1c00003500b84503040f01c8004401548001d181c1403000301c0180501d98211400c00c806004c0c982c468410ba41c00b0901c5c61400b810041840710306d400183c4c1f4541455240c20382d48e000501d043c05045d001d401607000601240c9400c00050724800d0a0314841400d241c410814844803ea0000c20441940d031a800c01900a440c1c480c004c842006090f40c2d0101040811403102d810080c1541c01181280c01c215455408107842d40101500c070312032840002d502 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 757522850 1250 757521600 757521643
    0x2060a1e0f0f0f0203010518190c1b150b010c020a0302040f060e1302010e1203090f060d050a0c0e1e090705070503071401051026071509051002 63
    0x2021155003054034404140c180110310801c00e842da210544072074440c0050b48079008001440142405c03020991008180c584041050070500400b1000300840300700c140300e143d00c55007520381c4540561003101c0582c1300d500060076944010b0503c50b0100c40c450070705006444c1054400139003584601072000301a03400408005a5528690822009002488100100540b6450000b805c84840303100d00b072003010720051032501c4d0101c1344001400c07200c4e1142480d1049042c401107211144000050300d80600c8250780500344074074482c001034158007500400341d9407182028200440ea0f00d050300028104e8080341c44030004410740b04100318644000c40c045851b21005400910194502104e03e95002682418075920b402c00640f104ca0540c3e0001d401550b4091841000200081c024890182c0c000c0040484144060901d4080090005000520f9850792101916502806414080d01c402440401c4100484030116200900a4107503813094600c280360601800b0085030001c59045211078400254803103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 757524100 1250 757522850 757522901
    0x30506071d10030b030f150f040201170406150b0c0307031803020604080d080a150b0903010b09011401080c18011805030102070c26120702030f07140102060a 69
    0x1001c03403101407545021194001011a40d03107400c00881808112542c1c0403507506040c40038140f4010404a0000a690150414000b84440e03004900e80100c100d0f81c00000c240c54a000403075012010700c19014056260006110401150ba40301580703d01d01205040526540e800405115004c1c0326003000c0d00d83c00410480b400248110700319041d07540c1d07050003080070b541c03290003090f06501729401056142d481203203000ca007150040c0c04140c0c00040700d001403081c1d0b5241c8220314a50150380c81000b2a4a1011803443c3c611380e802c0d08409183c040c01740603a81d103580c3d10707174403440c020510502a0340401e241101165810080d80111219030000310203507841d02400724011901c040704c062000c4600046003a02065a60b07003800142200f50040c3c461003001810001814091403c4031070990780780c4d4a0208500707131154003240c4002c6aa41c2e842d40c1946484042c000b29050040c05406400d0b5802140d002084910003451040b10121080c0e00311001940c0d8620b40900b1250080f080c042c089850399040d22 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 757525350 1250 757524100 757524107
    0x909120e090a150f0609061706030307020d0f0b1f05060c0a0b100305030a02070501090503030c10110c03070c0602012f03040303090b150f030102070803150d080a0302030405100603050607 82
    0x720150f00350311440301070690320741d0030b60343e8102c244c1c000c0000964000c0c0100440344d80002d58012505961050911900700800069564440c0b400d009000740050500107051081c5549801c0b10303a600305444420074134140b11461a100f502c000d03080d2082440c0328000c00c41c1e0a220b010703594540d5014004100c00599a214024041c0d00105442d4946d5a5800c0100024005202a1010094a4005145042c03c0030b0024081e00300d241c04c43c0780281e0007440715542d2450005059046800200c170f0002d00301e02500b01981c0325200d000100c000c503100005652040103000380c05401140d070980d0081040341d0355011004001c8100020780c03000c0071070982c00b010340741c2002d030010340e0054424180090060b401d540c8241420b901242c1c3c0c041c5184424480507501e0520b00541102250201e0003140342188983d01c408103030002800c804007407000d100c04801e6036114946100c0d511030300310760101d86480043d00c5c02006548102c074105e03803d000e150801340d04091a0300400c8107032603020021b0103d075600c405c0110b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 757526600 1250 757525350 757525361
    0xb130b0c0309060c0d3c050c1902190e15030c12010b10050301150804060b06071b080106030807300f230703110304030203070909120e090a 61
    0x344940d0000300440542c980c2e601c030080c030f500c042460160205038040032018000d01006400c3c1d0140c005c0e200c1142c010144c00c5503c0780344941003401c48034546180884100d50034029200101c01030b02c504803d012110048081034007005100700c0f8200d80074661003104144644061182511194081010903260051749090042d01c03103024080f580d0b4003040b040020344100c0200740c0d03507109940d110100100b505000c200544203042900703100b40f86524060100c0090200410346404111010740130504002c100d4000a030000b400429543e01c41c1120704148103a00904044801b500f03031030b058001107024040c014081100d400148140c02c048031525800000e4131090040c05d207588c0b46002c4007001c154101d000e620745a4040e660042080b07200c44000d03006520701d884071500810b100d00900035207040c260803075416036850b1600e400c070b103000d0700f04191440c00b0b2600003e5050180140100c4d03480804d03809080c0a501a04040c0d85c1540c04800c00e8a00d00780400160307806c00180340c0043d40c0c0c1c000c541c204 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 757527850 1250 757526600 757526617
    0x90607030309150603140a02090604091a0a020c0f0c060a03050408070611091813331a010c050606090c09030a110a150903020103110c1c03060b130b 65
    0x1003105080c030f560345842810794445000c42c0e281da41c00d045c401e10580070070590161507214002c004070000d43c0c0000f80d040c1130080c1254403da0b01c810155042020041c1c050340d01e0051507901c8502c42c2010f4451601a4000128428041c0314004401d0482180050501090100a4030880c031305440880b04030040d00c0010800d0780e080ca01003143d44001403d510502869030b4035403050548038844a820481d480703402d5205003200041c0c050511410162a940d00c10103980d1110000544d00c2402008585c4070f055202c0c0304050007200c00307810703071290043d030050b01e180f01c078941e940543d507203410005581d0f01d441c4440217484d07035000200081a50401818480c2c0103070600d0b4445092483c0b41c000685807001d446000c451100780800d1007043c0b0304148030002c001d4a100c0d041441781c101101d40c020440d140c1444060704150b180c040f180307031803103410040b200b005611105840e040c240841404030324960003550340000031f00d807070800100389c01c00c801519001040d84001d1009586401d441e50a9500710804 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 757529100 1250 757527850 757527857
    0x1140f09010c1a0a180c12020d050708070513020403030203191209080d060902040e310b04020111010b061b0c041415060403020d080d060f0f0905090d020309060703 72
    0x18980106075100383c40010036000440f42282403800324001c50580b1032070001c2e211039040c1100104000f03401418548283c4096102203040e64001e400004d940300030095015246010b50040811103c1c4081100410b407801036034402c40c1e13a40d2a0180074102e108511000d00103820510000200071100407400c4661185032808040003022403804000f125909601207500c520000b40c1c040c3c910200f801035070010000c0c10800c60803d8500140400024001810755045110003005100405815003d50204015003500c50001036003c0c5455074100c9020380c0c043c1d01040001c009000200014060a0140d18001c3c00440c201480d00509190815410640b05240c4c0074082c003185664649100b07401c200103501600701d600303041c001c600402080d8080034803030240108010620150301d43c0700c0640101a44800b019aa5010300c4001078000c0466800c04c00c0000620200003801c19140c1020100355501c0d05020420342d03c400200e20740d1841c4200701803025030014002c440407840e061016000c0c2501904 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 757530350 1250 757529100 757529117
    0x61510090f260a052112070305010501030b040504030905120f0111071208070f140705060421030b3a080d1a0f13060317031501140f0901 60
    0x2400442990503a001025000704102d428405244850029004440c0300000f42030041c0803500c82646655901781503107145501ca01050740201c50b04011540d0a5900c011704405a00f040361004000d0003081c803503580000e040c62010304461a0910680d4003e50b810380319199076501d00000d1000011158000e41011300a200e10072242d07104c03e0143e100c20190320f102442c0d44019174039080716070f17500540800c0f00b006070701000c10950581007003803a418000781d420500700c00e0032860948507141c880d070031000300240030726014481000038200c0744c0b00c40c0c0040d428001c484480c3c10113044044800c1c81e00702d02e82c0609005140001c90b40400b1060003071a01d09140c44801c154a214802002502100f08444c120302c0000d103009203c1d42441100e12026084850078204000500003a00942c0c80350300203032180006005042c01c1007095402a8020341e40314146811031036090164054076041182d032500c1d00d10300c410718040701d07600c1a090302500d8040a02094100480342000810360303000740d042a410b01070800e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 757531600 1250 757530350 757530359
    0x80a02090d05061b070519020a05030f060411100905040b06070b0906040c1703090130140a0e030304060504030c02131508030a0903020105070c0e10030b01060206151009 74
    0x60081ea110140a0341c0100b080342400b04862903a607501c544184101d0b607080c00142c000880c08644248502e4140850a00040c12400000c0d00c04402c0d1b03000d180d0520520000100c40040410600e01c940e00884840009028079028080326902100e01080091010203050206151951000348c00060142025003007210035a00e00424030000d90340b00000398040410031080140c00c91014026092800b43c00669610000040f50340340101c4000c14140040045124000c0d141e822100c8070006440010080c224511842040240fa594482400541e6240d00042422905014082032031000c1d0004600c0c5a030382c2c1d25100d008010142089003003000da00c50341c80140c0e84490501c442c100418100045021002c4036000d00d0034400e83c00380c00e0b2034000f03002038201940c20803030070380c21280c0a081079a69010a4545a0a1184141c1252059802410510442180204c064002e680c45055110349598a406050b40d072081e085610303d812400c5241c1c00c11490034a001d0410f41c041f81c500b04550100d449 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 757532850 1250 757531600 757531609
    0xd0905130f0603320706080c0313051006050a051c03050c01090203060f0702010e06070906114e030c070201032a03110708120c040803130e15030d080a0209 68
    0x20a18110708039a281c0d0090203001182c001142c1e452aa484c02003c42c0c624141c0c0241103010010000d9200d030b0000700c00295802042150044200e038428203443c4c40f0003040140c40002c040c1c5000302c5020b00c18060b0301040c5414085500c000c0c4010003142c4040c030307100f00e55085556621a99040d2845d540356448140107803802c1010f1800b8261103402040f1030b02d48210300900719512000c3c180303510313440f543c28880a113401141311001d4442c0340c64610358031040d164103030740ba03d013030b5142c00203441c024405014100802c02100310345070f000d1002c100103841c1c2031501613150700501c2386400c01401c0c410000309240803c07407001040c002d03106040104040e549022524040881d000481c80e4581280583c441c1d40c640c188590071582c001501054201160f0f030706c0e20b4005001d03a90300000c1103480c80c400f1030000485c1d90140c07001000407100b240c1e0340b0402544101200001841010040051039011a8454141d0381e03030112aa103020300240b0b000707505004d0071540c010002e000900101d03400c0000c64404d485 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 757534100 1250 757532850 757532873
    0x60c0727200c2104050f09070e1302120906010f0b0307020c01030b0d05150103050105060a061d0411160c0501110c01320304050c1219150504030f020d0905130f0603 72
    0x6244030380c5517803030b107030500c4010103041c01c140f03104070108030400442ca500300c0064903034000180d6000c0101d61511a40d04000d120700c41081403030102075000c001c021400021140e050b01c108444000c011035031102d19009600064801c18090382090000d10403a5120340d006e21911540104001000b6816484e0319052205074802410704865000040c130130b00c842400b0b410b410900c2904d05004041c50450020100700911107c018001c00540030089103503501d40180a01d8440200155550754400c44c5601a01c289010200c030780350112100021198003420301281c48040c1200500401c11105004407042c0e0002d4564259032035085507080083d005851044a8172030519600594a08050404900d0071184441c983d11810440700008180c40f408a82c0200340002c15030402c00500b0580303001c0c07154000f908904590380b454501003006060340014842d800d040c46800f40c0c0c0c2c02030500342040ba01014240920ba400041c17560f50200030301c101d42d20900c074811025000003409a00d030754400c82d5450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 757535350 1250 757534100 757534153
    0x14010e07181212020309010e0402090607020324090109030818010e010e030c12070317041419060509160b0f13090b0108010f120b06060c0727200c 64
    0x41d04900c0450821114070022030038440f4600086042c9110100001c202c0450f05060300c0c020385c2c011818000b6a11507400ba200119401020742c2c100585a403444990795200c1c08800400340710100110300d4010040c420b04401030740664680c45540d603507504000000d243d04000031140d41d070325041c1014500080c40341040c2c0103c42005195501a0680007500c0d040d440074070030015400810907440003c0c0c1213555040ea881000120202d2940c450078003941764001c481c0900c050b80600703600707219501c4c3d008d50540c10140c0300e80c00800803038848141c0640e03a804501454160810701d140284050a64100a40b00c80751407190350724580307030445a45180862207584520324681e15066034075800d42e040011300e4090800350806084161031b1144044400450f0381000e4401c0300c0e07002c007168071910745c64104e4150722400c00c10ae4030510350b600d02d0b1804001030303500340f403002d0341c200c042003200305c80940500300e50f0b05405900c2501011140300c0010a50303020100b005810f00c5207000040700e00b803000d09a028442c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 757536600 1250 757535350 757535369
    0x51206030a120e04060f0f0302150418090b15030d030e0a140106081203190f06050618040e010b0d110d0c14040606140315011404030b0103110414010e0718 68
    0x10742e0f0034240000d5803c650410824486000c0040c0445041080420700706c0390121416400810051501341091040341c02c140811919260607640700c88050300940c407680c0c490401d8244555900c9080701800c0358001000780e254002c3c40c441800d261094011409800c248c07003d840855110307640d19016032a40e9440040c80741d440c3e9000708031b0040140078602d002c40071075a010b8510700e007401c0d00302c07012003000c1c00f2003000c261303100e11421103980594400d002400c0060321495850201c009602d21005072403002c2403040341044000d0016030010302442ca60103030b014008503014121946d4029001c050443d1194001309480842c801003242e61a581000b00b03100b00c0000c082c400c2c00010310040c5d03080d0750004002d01c2000700e00c03a0701d9501544100d03580060000385c254451010180100e03481170104647c00c001c01400b160100c02d01402402145c100da1007403e0480f00211484103000c00d07580c00c103c2c809144105080108142c5e080ca1a5a0303601c01d805113030100750b604c0811008040110300c0c1c5c0000941 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 757537850 1250 757536600 757536617
    0x6080708070c05032b05090d02031c060b1605250b0d1803090f0f03020a03140a0507080c0a050a0e0112171306170108030901030902011b080703140a051206030a12 71
    0x400e0806c0c032806030024811405400040007100c006588c81c42071002c181c1d002803201550f4075051500d40d01c601d0182c00e0f107422041d41c2d4511002c901001805c070b08016500c5003d5404544503000e1526007041008400c19200c15515140c4442ca042c00c0d0415011108030755110840e180c400aa030020038008584a0340780d0b201c00c6824543c2c452001241340d044003202030a555414070150b5222031003c4201c0f9408070300e9540340c918a010107420564420802442171003240300102d80e4200102e1100c83e0b040080d12202050780d654810403400068510641d5a0240740d6801400300340402c20390864564018400c100054410000360b1040d40d00c50850800d1200030805d00380320042d40300403401d0b40414289220085541810308030358a9205d1490494149640c8450b00340459000f00c110308406159241010341c03880050400e04020f81c0b0400b02280020341140c0001189060340e4140c6140ca030305030b40e4680c18407400100e9071091141c080c08071a0b00d88030b46000c50001070741048407041d0b07000300b65840001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 757539100 1250 757537850 757537927
    0x2010e0a030f201507050109050706020f100216031b08160605132109030209090105010603060b04030b010e071707030b0906010e150306040920030706080708070c0503 73
    0x408040e80300e520b0035000380003034220505546428078018070111001c83c007581ca05c02407601a0041c8601c2c0001040b901555800248182c0c001c14054106440701c1c0903030700a0050754118100702c0c81080c0e5a00c0f00e91010748101c1c0c020030b1042c4013502000060280c403000408840c0c079441c0c8183c210102e000e00300c4212850100070000c450103400c0e0801d10a00c403501c010103e0356508030300c094044640c40b41e002025828640c566120b41001802035401034803454032420f101181030b0203043c00b4000c41012900348140000d90801101c101c43c102e07500044041c0469091240c1c4c20b1b41918041c1c40c000400445060092031445075500180c0100401e80780010f0450640d010712004400c024682414071031690842d405030340b11030b10420481c40401c2221940d079940c980c0043c0c02007103034107809020001521240744941c400c40c45d0889601ca0100c0480381ca8030359489088501c074004035120400540b10310003180071507000700003081089105009480c2042c0c504c2c00031400b6400000e9003040d200d900800c2c0e012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 757540350 1250 757539100 757539113
    0xf0a080903120f0d11160609050c0f0307090e1e0a020a053a0501090f2a0501050307090b03090106091d060105010c0309030b010e09010e06061c02010e0a030f 69
    0x40c449032503680c45900b44031850140315124050440e03404c050544540c03d40c40582201021a500e200f006c102c84030702130005041c030000600031210119400c0c41900200400340c0b800c0342a200052000030000d1100c5410420390801030000e0786024403541c802d010400c0d4400d102000c0d0080c01d0032801c0b0007040c1584013401046440b000507442a40100b000c0d016040301c0c0f00400c0c99110512200c80c0079540d4005503041700c01d003402d420010103002e5500c0c1000a80420500d44c04101c25940034000c0c030740a82030080d10040341c48100642c5401e024490410402042d40280051980070b6030504001d402c542da18150405568401c803400c0d000740e5501e02050086a109100b1160141603e00002c407400b032040070015a103d4042c02410305105e49003291004041c40380d140e070001380d64010910358495a40b0400c0d803014440a0340c0c0e000140d400c08204c04004c11f00004c1d00351203000000c081e80b0304070b49010543c600910764108182c0c100990001c80c01a69241c43c40030b140103502ca020080741480440c213015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 757541600 1250 757540350 757540363
    0x60e0a0b1302181315060f20120f160516080325110301050a0b0a140307050108040c08030a08040209150108070e24030106140403030e090604020d14150a080a0f03020f0a080903 77
    0xf41c0e40c80850707040d4008840e00027148480810031050301940c46013404885039040c00751400a00901c401351030040c1c2001000b20b611a80d000000c50710030360403074582da0310302d85901a5121030380f000b840101d00c220454080400680c0c20601a2074104080344c0f40c5c4000c2400d440003244d03d1007002d500c0d0342e041002428461104001061200164070030a0030041c00a0307160307110f92092904000300c20000c1814480c0d0164814001d14884048070f9a4540e802000341078a001101c003a440b84c1010380004101002004180c250301405958500a5941d030071402e41e5100c3d220302c50315410841c0280004542c0e40490130b4507408a121680d400c2c1c9944c03424000820300240b0780c031074003c0c0d003c0500080001907000801544441c40450b0034030a90395038840490020b000745420303015031500b01100c400e451100c0c2c40650f0301400385940140440808101402804d2515104485041d8010a081000718480380b144004482c40303031065849800c111107006141c00c1082906907016800080c9809440c40d041016 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 757542850 1250 757541600 757541627
    0x20307050a0503030415031508010b0a09050f07081b0408150109111206030a06050f0604150b0a0c11120304061e050301060c06060e0a0b1302181315060f 67
    0x1200780890405010903224016031042103203800d03418000c17400306d500a40084802040e010340c6d0700c0c081d540d2103098038003030059100c407140030b000581030100b42207000f806200d2203850501c003003807019120f41100b1a85103000400301741a02160340065021012076000410042c041c0d20001c014022403110a200c0c413401c10380c0b0080d85d8515204200c0c40d031210200030341d0030641c5541c0090f00ca170390391071002c41e09250130b0360300042105280c041000303800f24107140b03004e02a03101950200070070b17001b08070303d485401114050090350500500c0300d002c0b2184161290803116200d249123412508000340400c0050401f4000f01c40c4580002c0380600000d41d02c201c1c0c4c12215802d0700e00400c04070881000117003480c803041c01410200020107040809103d41500400002d04c150b40199103d480e000c4581c02c01030114022952160100b80305050100100d4001d48015030019903102d42c0c10142c41c01003000c404000340314208595101c0d01528441c4201c0546c0c58001c040300c0e1501e1055180c1403a005094800ca002d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 757544100 1250 757542850 757542859
    0x6050108090115150512101404111602150f09030f01020702010806010e041e2c03220f0602010906060509070e04020d020c060a020915040b03060f040e06070c02030705 73
    0x40501c4100b4a098600e07044400100b000d2041d03020130001200c1d544644014509030403568014400c44850381c001100444100070b4507143d80e40c21220400080d80c402c04a041c032140014800310011104110340c0701034039440240042c03100c015268440107580c104000c014411480800d001029060501ca20351a104520008600e0030700c2360781c0013a00c80800645054104141181c800b03100e92110351140c1001180c1c28032206a1900d16801c4001a0034000e54142815030702c84c880302c40000c03100c00c6100c981c00c0f00d0700185050500740b06101020025024062940c1c11b800000041c80d20440c0e1a104040c100950002c03c540751141401000e41d092035024600900030482007248103a0b0210100f1803030401140c0140c1c2c0c404182c0c90150290107003103168003240c0a408184054055603500808103100c0680d0f010480007096660048240128421300c010440c1c1000020402c1c0740c20303280104c440a00520004006a5040041d4600341c0e00311070540c00b0030001d0780454150300d810131201005000884 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 757545350 1250 757544100 757544111
    0xe100b061204030311070602190e04060f0905040314120a1a060d0b120d05040f2112090f060809010e0d0f0305090c06070f030e0429030a0c09060501080901 68
    0x650154506000788082c0c109a07940c4c001405170100d04044903202608001c0035902c654083c18204042d42001181d44041400d00b096030450341440c2c05110200c4005a0f5000740640c0740070000c00240070000d10071001c014036440c40744900d440d5030b170241000442d49400c41d0544e2034008181811201c9039000c42c201101841c061b840141da07a60700300d4070000140c3d02d0205104141c80041907200030500525981e0b4018005c60302c40c482d902001603c103c4c0e40009414035138603540c1030700c9a98403005a82c80d0403220300031070a410105071140302000300c4807840c0c0f9003500c4840e1368410403110750169400c00c00020701e080d014014565001d004800c0040917145c05403424808042c0050450308081d5580700c1415260b40c000f0720080d00038003002130307407230000340c8aa07688910914040342000700d101821404594401055425402d25102c1d00486041a00d035451040301e8480500c080d402241c0030480d0b051007004c46800000341d01c02d10307640c001c0c4203036000499141d003040005000002c0081c46040240c0c03402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 757546600 1250 757545350 757545367
    0x2f0c03030405030a2a0201050d06080607020120040f1a0f030f0114030d02060612010209090f27060c0d1e1505151902030403051f0c020604030906140d0e100b06 70
    0x1405e032074442a82400c1c0140e0316010382c0040b074060b00320307980440344502440e030070030801071703010740000c40c00d0114203549503110030391441800356134001e502817451400c1d40c0082c10700480c801d048404074104501800315045c00385110612225620454603c40001c0a42004120400b811042d400b01208114041e2000a4052100941e02d1400400c11440b07040181d80c08441c0f083d00b94129401054040d08280715841e001c080b48220702001d03191186180315002e0103145d250a890034031409101e041e40079248079120805401003d402c0844121509039403607012210071130103050b801021318040c0c100420a01000d44021b211a00154000c40c011805494610b02d54642c400c12128907500201d41102101c00c454012071541c0200d0300000e150388280c107803c000c08035030803101e2034003151610003c2c0581c0000a8049031286400d8800030082044940d09014950088409807412055805031700d04004000d105078050303600f60300803103506402190b80b00b42450340c00d0050b102d900105555142c81c0c411507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 757547850 1250 757546600 757546667
    0x1140703031e0504111c0804030501150e0405030d0c050405041d0607020f060c0f16060f050c04030b0f071803060203010e1501020a0b040f0206071b092f0c03030405030a 74
    0x40f80c000c01e06c554010304104015002d10484241b0702608140d2858075a42c0f01c0c6007050007007000149a40c2c818460b65400950041403020041c4181c2d0f0060145040119890440c0050065903c80206100c0240000310b8141c546100b01c03d2800070301e281007082c12075440d10090400b40003500102c00c44d040805070446c010400030b4002d4000109a81d015039030007d400900d4064003640b14450b40c16407000200b203042c0410380c0c20a20b0f200b6801d4404000d203460701c1594000d14841d034400100340303c596000083e21030302c01076210b80d404042070400040d00440741c0704c40222034040f500101c6007140e0200051043d8400d46102e03a034072880c09044c0071140400c040003c2d58954010320001c10140c2000009410004d40410303c903849030f030113044907454200b030385000304100e07100e044425407180d80640c0020b40e02c62203000342d030400321505031056080c55140b401244200907440c007004c8028001c006032100900100000e40c03145000300081c6456113102c08004240303208203444c42800d003114071001d0024011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 757549100 1250 757547850 757547873
    0x306010e0d02120d02030705010c030b180604150b0c0f060606120a020f2106180a0c020703051606020f07030201140c0c041401050f0a150e01140703031e0504 69
    0x1411201c80703080806074070000369101003520b2124981c0c001c031400490034540000140810a1250000748003c002c00c030400ca003110074500146901501d085201d0440c4000521010f0700010080c1c000318100c82600e8820500104a42c80894a0030001452512083c4240020f01c0c040241201031f003038600b06080061064042d0015400c6590464004505903141640c1207607028140d4480c04c81d2211040b1040d9030b80b0b0040e401401840019020000c1c86c103141c9070250100001d1480340000003506e4801e842402000c100403e007007584244140400412020006000d03511180b081d0f10544c10b0510400038140380b600154241541e020032020310050380c102054241003160302e0781180d15030441030b04c020302d04030010144035009031800d1080c040070001d52a60b54180c40c8141ca003003118180c080107100341c60761680306440c81c0b580070342c0044907158454151641106814900890081c039468107226840e480b101b801c9010940d03940300014054001c40b621081c0d41e480b02800c0215140503115038034201c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 757550350 1250 757549100 757549127
    0x130e0105130b060a0e031005010b1902010b1f141c060b0a050730031b02030406050d15050915010215040812040302030d0f0203010e010807030807030f03061703180402030601 76
    0x4004412172500c08002c2d200b41d400c0002814800b0356901d100002d03c41d44041001c11101494082c158481070050056051443c80940b202c4020a0320300700c00d0114007103014500c01003081d03c80c0300c40302c00704c08100a4105c4030448020010706401e20000780781103030301c21740c490a40c800081c407070503001c00d0b04a0169545030340c114040c9000c0003102100d80c01d01280d00a1820000c0035080b10300000c0561503030040c100c00704021051040f880b800403050369280102e1007800005441042501500003454000f0201c52135000e108102194a40e0300140d6503020854400c1802d40510a1b280c0c1d0969041190391030100610168481c41e04003502d0300181407260f080150075a0f40810702082c209403003007003280c0c03040346a030008100400e0402748000c00b0f0360081c4903801080c15a000003182c00000400c00724200c070f0340031244628000d641e9800342d41c0702030000190780500d5a07580e4001042c040704454035030b8100c1004c0185940303080c2c0708080b103060001c00c62150b0241c0d20500c20803140d640c0243c90038840300b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 757551600 1250 757550350 757550357
    0xe1908151821180a08011409210c030424030b0a030b04080304140f0f12030601170a02092707090b030a0f0e0304060314010e0702060106030e03130e0105130b060a 71
    0x1e000f0443d03404500c615250410703401621188002540800660014506401c000389401d040c0d12001e6141e40d46d104c80c180e000c110961340c4140c0303040c098828001458040d800c007054070b0a1540d0350307020b43c24480006007200d410039a1030341545078403545442040c2da04c6070125a500d50075400d5407201c0240110040000b8107041000000c41e051080c80c4103c000419480422507244600055036583c682e0702c040440c00c824800c660007050541600d800390f80c440c02c41a0b551043e05031000503c1d280c5c103803002e004407401a50821588583d52280780030b50010030f40f07154020521690282100e81c1200000b8603c1007004030103402800054850000c0701d400440d141004121040b503101c05d00014034007070215101620001a0004c2c600303400d5040b042d0704000d100940801a81c0e110210304007250f0850703800d03006030441d1005010960095024140004402c0d003280d08001c03400c1000f84a40c9400c0d007019100002c0ca0300100900d140880150000c4a0241700a01104a540000c18040e000320806201070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 757552850 1250 757551600 757551607
    0x3061b141206060901020f012a02060108060a27050d0f0c020a050f0301020913091103060f0406320f0109111c0209030a08120609070e1908151821 64
    0xa603100708100c40e1f8011403003000300012200b144c0c5d002d18003a4207500401c0c2e8a1400709000e0403543c00880c01a040b0394003400079001d41d60352224003400030b00c00341c0d040500c0c1141064007180c030084021181e854881c0729000800d0b0045c40200081e1544036111114005c20020840403401615041104c2080720810b6500b00001c8102d034000902a002d4407007020340040c00c4204241100d034450700304110702401441008442c203036500600d034a0302000c075011110020107202150006540f07911080304411810307a100d0712040025081c040101d0181070500000d205c1c41c05124a455144104500505880303404024601e50710208011038040d09001e0a2010b000c1c041c020702e0f141c43c5030110f6005640c003c09490460080f40b5000260f40c11a0722020f0503000d0120000340b407800e100391400d00480881d100d2407403845c0c00204020340c0c000166a101ca00409050b400102e200c0200030005250f4504a80341c81107160040e0341c8030303045d1040e00581c4c1c030719805a01048003030413000341c041044210000103d9078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 757553956 1106 757552850 757552867
    0x903020a0204061e0e040213110c2503031101060302030d020f061f0506073e0612011203030e16090b03060702101503061b14120606 58
    0x11450701c120b13062210100d4120b400d680144020403504080c00b030000341e002130364041c41004501036808104642c107103a040c02100503042510200c0070090015010314059400799100241c00c0c03080c1c20340310300881c003400e4210303002468014049031684d0914040c020342c0d0700c213250034549203409203a000c101c0c01c0d4040c803018000b0a00c5c6101c0760402a003000c6c10031040742c3c03240008031455048500c000012100c152540d099550710455441c107c140c00c102030300c00340415800740b070b445004104840825600303e000c0c25030540c0c546145101c000c001600c0e0070b40041c05441c0c0c028060f403040a0b418446003000f40004000c2c1c61502c9007d0003218054000c3c103564000c00d888100142c0c001ca45800a50846540000101c580038115821500da80340c0701c25081345c1d0710710704010080040e4040e601110b60800404000d00c07505402d6149032101c4c100c00581c00c44005045148075400025001e00c = true := by decide +kernel

theorem cover : BRFrame.Cov 757374100 757553956 := by
  have h0 := BRFrame.cov_init 757374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 757374100 ≤ n) (h2 : n < 757553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
