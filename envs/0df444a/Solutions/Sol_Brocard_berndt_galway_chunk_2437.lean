-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2437
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:43:17.181196+00:00
-- url     : https://prove2.me/submissions/d49f903b-ec43-4ad1-994f-ed06afb9c76d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 438129496 ≤ n < 438309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 438130746 1250 438129496 438129499
    0xc0703020a090b06030601030207020f0a090e010b0108091c022a0a0504050402220e19050d050c03040e0a270506070e0d0816020a1413060b1b120a090f05 67
    0x40140820a650b01c44003540d6101b030080c40e0040c0c6a0f03505000041c08050304480e41500880c81c000042100206c981002e211100715130024001034003c04011101c0c2c03202140c2541d81c64000500301866500300c1c010100e0070381d88501c101c5181c029480c002c524407140141101d40d110020368010041c509000340200003c0004841c10055446c1c160081a40115140d00c0d50f2526940d080d0440c4100e4281d9103c40b59107003410080b102c80050184c54440e91615000c02070f030b03062281c000f00d040c08a1040040302c450038408009182002c0ca03020380c044d140c0e000500503009082d100c3c0d071a814120040580d138002c608a5540707500c41c4d100c86041030390a049018002d00c0802c59840f030001411380750a02c455004990100c81c40d82e82d03120b5800c0c0301440080005000b54004400313840041d4040d03007645a1040d800382100d082120580c100c048800b2505a4420988105418400c40c00949403500d85a2007041074201070b07030110300e0050311405050380b01d03c0010004c0f0b094080203004e610f41c02614040038050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 438131996 1250 438130746 438130751
    0xf0e0702100c0f11072d1202010f0302092205160f020a0213060522060501020102070317070e030d1d120c0607030c05030703090806061807050706110c0703020a09 71
    0x81c0c544020241000b150b01802441401640e090340b00d44d0801040005110700c05e059000e480c44410050440303c4440b000c0342642c0c20207000810070082a0340d4044007035905845402c0e030003138492001c1c0c000e50809210700c0d80c0281404042c081d818500c0c20440100b91800800080d240352503080501da100d80039040c00100b220009400303031100e800041c0ba500090701111154502040c809001028000f140c120307682241d000400c10301018208000c0040015026506212843d100d0004900300e0183c03000c0500043c0c1c2918401072140b01c240e80c6160407250516000361032054880c0424034208400036000c00092800d41038191102c0d00d520565072004044462212a0b50f49442c007523514014403100d00d100b24070000e026402c02d4024481740d1041984403042d6905d0304480d043c00361881c0d80300c0c4174001c40d0380148000a207062804074400c0d441c01014012000a54507508000c5030310b9000764008a8400e540c80c10b01255411080b40580642d07088100103101c400c1c01c40c41805039904099100c265000e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 438133246 1250 438131996 438132011
    0x20c0f0409050f0109050309010824130b040c11071a03010905060a18020901091223150109051e37090506060109150903020f0a0f0e070210 61
    0x1512105051041002154003140000d4103007805402c042c0c6100f0030035000e41c40c091501d010800040003401041382d01742c070783c03400640d1010f20907520303880d03480800c051440209001560307601c0d000103154414948081e0010b010000c074004141103a1500e40d03e9004075003900038689056038108035a40103001050311094848044141e108800e01060140d038000799211400500203880b50030809000702958410f020716403003c0c0112200950185011340d0007d070a423000420103d1110050800940d4060000d0401d9407100000340d0b510200383d515610140070b26010200013032a00700c0c03154042e05001c0c1c800901c070b061500328002c1c1032914a040c00311210700103080101c0402e4590f118007440351016548455422850000b4405040507001c0210040c075110560042c0500021918410700e000e8852201031512041201d04203050032034000c00040c20460180010304000304400d030035201c041d043d20711964849401694424903074001100017054802048849035040180d140404400301c010000d16 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 438134496 1250 438133246 438133249
    0x60f02030f071e0c0f0b160803040302160924270b13052409040b060105070b040302060703110405130f020417030703030f0516050c0a120216050909060601081306020406050c0607020c 80
    0x241544c03002408d03d0101000003000d2500030b01c44902486045401d01910301c1e04ca1214038014801007010384010540001d407036980030030400140080e0390120040b500b0b542000070820306064494042c03410302c40d8030380046103001d40301c1d860704031a003441c083d1000c9003d10781018010312000b820b19509580c45500014140e0503100c041446801c82d07000709140103282d0f165001607546114041d0f004248000c1c0104110601d6404182c281c0a01415035060141c05803405950301d2a0103980079050303004e0300c0b1800c846100d01e282d0348640801c0d245030901601b8540c2d10740c545511038900070104000750308006500b104040d4103205194030080406010001e500301200d1000903500046003100078448005800b500d001c01c00c11081001a51003400c41e041d000708100002e41303440c5c4039804041c1e1070207400f5000c00c1c1d5152a0034003070b01c01c07100f150003020943c0d80c8600440b01a1000707442c2c48110701074806c1c08800b14041c0c0c0003d1001d480107894460391540c006075058542400185100215003040c84264181d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 438135746 1250 438134496 438134527
    0x50a09290904151e050414060105090a150510050712090e060108040609050a1119140d031403040f020a090e0a060510080601080f0106060f02030f071e0c0f0b 69
    0x2c19081006450f00f550003502d143e00401c40001400441114040404584100ca411a41c03045200e1f98100080c41814060140c2e156001e0143c19400140900050400e0a59030302c000e04071100100c010902a1740e503c0407070461004448140c3c000b5a0014840041c04510b0390519500c4005140075000140340080c0c0165400e001790416040080c00c02c0441c0a0048a4020018160f04901075600d5540140b400c5500c3c22024501c40e801a40c1d200120640b84c80003000001c200c8240403502d070b035105141d0b0100709007800c0300c150450600c00c480280c03000f0120081d019600c910b100d0911054203003558010400001d000740e2000c3d00762820041c2400105601140e0800050352000020802d91518001e072070300c030680b60f00503041a02c90100000307081c240000b03c911541d42c00b00c008000c095200c5900b101c0140d40030840f00301613841009444030611a08005018403401021500005140900710304902140c80310700b0b4600c9800480240f04013602440400001c03c1d1070700d500d6240c46100c0941440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 438136996 1250 438135746 438135751
    0x70507080c01110c0d0809041b031a0604090b210f0c0d12031a120307020f0d02100f20060415150e090304080708030c1902090f0a06050a092909 63
    0x18010313000c1c1d1030b006c0001c10000d49061039070061082c000c00306034036141030604060342c41c418002070400e104400c0180303e544112405100280c07143e8903180c1001d0014014141d04a089500040403010ba8080030050303408c02d040c00e04a54028001d401c0f00030704844c2c5007003e1303100010300c500c1403c1c81500004174550303005501100b540c140800c04400ca503000403401040c260429030000341480c00d02040c01c00100013040414421248504007100810038400440d000c920002d42203600710f8840002c0078041d5103800184c1d90107281400d00480d100002c4d820f030b6103042c0d0f100100795008005000410803110b2220307a22003120b03c001c200b103090400345161902420301c030f2910030300582400f01d01845d00902c100c038007602d14070003101c03891a650f01181c2d5496000708180b800d14001c60080c2800c0c443c2d4196203000c525001400b040c07580e1110468200c508001400110441e581e5a100240d240c4401c140701005140d20303140010402240c0e0009211004a0030001c940000b01c0d00b66503101d80d42d01414180c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 438138246 1250 438136996 438136999
    0x60709061803021908012906031503031201031a04030206060f040603120503100b0406080f220c0503070927020a09050123042904060308070507080c01110c 68
    0x14040400c1c00010180080180c001a40122444c0c00710011030300941d51503021a100751008000c05803450007103034828030500301c0c00d541d100e9055171450024a8900b02840e04070b03400c400404110b14941d00080e140d40e00c00081c2c2041ca04404004100703104404c52102298101d81815000624060350000c0d110040240300a10515038142c3d941001c3d25182c0c4150042e40c0d009194400c04c00b648900502150030031a00c512221040e044049038000302e03801a502221415104c1000c1c1d511901180c1c1d084e140d00800c50a0341142c04084054031000000503680c1080c010f00c0c4c10713401c0c50304240505003458040d0b000281910304090009030205004175a40303030511850050240700c2403082c80018030341d607000d600c521160b80c100740000c00c0c04004071203880c00052902c0303039007001100d05170140002d07240b001c03424800003008c01c5035160316035041c00364007110307594002c00c00a0f00b2030f00ea650b2842103402050701603405030700440c0b084c030403202c0400155680d420242041141041c0405290f90707205803101400e13 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 438139496 1250 438138246 438138257
    0x703330f050115050a0806150708030103060609060f14040513061406101b080a0306030b0106031505220506041b0e03010608060402091614041203031103130b190203040309080f06070906 81
    0xb5581230b0380c200140c444407039004807115036951f500e0500002900d554007a0380380c400c0c40d01c040000c0401500c0a120116a500c0f40c46500300183d200420004002c002c104a40000400b0354501c00a116407150842803030104032200302909082051140c2101c2114512052140e0003c140c4160074001c0e6014800c01d0740401340703a9460203042001c0b00600915071004180f0010500040340050301a000401c9120383c0300c02c52440650389200704079207481c00207201c500262000d440009008095007100380d010340e002d0004620100c00340140801d2002101e83c0c240042c4c2201c40f80c00c0c642c84c003070107610028440c000082c011401c0c95000612207500260514000d145520b401070303d443d0040f89003d00310084001e01d240c4556950705034528555507424100c00103403405e200da035600c00230141901e0148440803d1070000701c0090352041da0840d80034207444500c910241d00780840703589a000451045100c0d540d60040c640c5000c00e803a10300405144040d6164101008000d401035001d0700300d0b001c503481882e04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 438140746 1250 438139496 438139519
    0xb030606071407060206060402030408030712200a03060b0a020d080a0b03070b0702011e1e02150c120a1e02030406091406090c01020703330f050115050a0806 69
    0x1800c1403091403030003400034850401c5004240008912078040300da02d43c0a843c2c43d5541c80f0f0401c01244400ca130010300300e41062012070202031041d414425078600c40d900c001020640c0203c850b0391110500b81f285000900060190352040d40350280b03800804100c00310300e060410a88002c1e40310340d68000c5076420001d952001803624070b000c1c0c1164104a00250603542e0282d11010b090313143e54000c24040e40411403016100040170700c144a0031078074151640e0f40c10b00711958880300922012191500108501c50144104d1214142044441c0901030590390140d448003210300003a20000020003050802d4179021140007070383c03183c00c041a4030038903150005999690300e03d00f400c01080580742c05411144401007201411000041c402e014030741070000c507403041c0c1107800121fa5500705400000d105a8a454110500441c0d56440c102004e118080700c001d5040b5140d0482c048038580750f91201d50940310001000b44d0782e102e41c00c0708400c007500c0c40c14a02d050f102c40350142c400040032b81440d001700b0b40101d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 438141996 1250 438140746 438140749
    0xc0708040e04210c021f051b030403260703050d180b061c03050415020114070f140a051207140703020c0f0a030f030806010201020d1d010b0105040f0b0306 68
    0x8440c0078264000104030307941481d0406119440f50225888031070900140c030404180e014084198095a008290a01d461b04a134002140703191542c0d400c80a000d81440030704640a81c031040143c01e00485030045484ad441c60038458807031102e00d0f0740c0380c0400700b00b01d440490003940c001c00c2322003040c0c140c202607541d4154648a4402044118046125045240f082c038007001529981d107030080800721407414250f400e440c465490b00e000c0502c01000308404210802038068034000c0480d0b040620300000890044800c5124640001265803030005883e518241c02e4040e085100b220249140011040c00e14100c40300140241c41112510b03505180f8400000b500d0074410700090300000540f0520359110340b80c07450081e64418100325000d2080c054010350203114200808440200c90300065104040400303074138287d5088802a001e281155004c0285022100c2d49002c2c010541d8081e8010094401c0828103103421609240d051904100f03040004209440380c00e02c3c0e45050700d54541180da03480d11043c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 438143246 1250 438141996 438142013
    0x12a0207230904050d110102040f0302130b15030a05240f03070812071a16080a14010f03050c1f12062303120309030a0e030a0501050103051f090206030c07 68
    0x1108070340d0050040080000700705020805a801c004240c586010b40b0404020403030030307409140100c0000701c0c0c4205d000c0015280441c5d04031900b650a10001030849440d0001c1484160f1640c00c1316460300000042c0400348600d03104055000d0300042041d50041c0e1640b544424040a25900612802462294490b507640600c2140c2c0106111422150394608089901105410500c000c0e41e1041031801000b52180c0c88814140c4242c000540c1c4042440340140309551520014014250283c2d40d0701d521515407688801c2d140c082d10f01c401c503c1c03002e64610b2412901c1e0802c09035045000d5403448040c854100d0038156170b8030340d08180b4203204418184003a0303c00020221580184a8860305841101c9410f810300f4030065080d900781d00340c42611804510303800b0644001da07070f580350035802000070044844c801c00841102240003002c0d100c0d4540760307844450a546007a0010340d101c0c0c0140e0401941d00981d481d1084107442c404006005201064001801c00d000c01407102211113400140141040741c2038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 438144496 1250 438143246 438143309
    0x601050d05010e0f01060501020d030203130b0c0c0607031b022b020c0619020f0a1110091814010f0501170a0b1305060108010e010509062e02012a0207 66
    0x54081310951510380d0203182c080e160030301c20b442c00b50241c24002550707030b4468001c0300d1142c00d5070790040081940d25a506c500b0351100410403e075008052256007203078141484202d019000070381e0003044031808502208a11211a45c4035420b540c4149005801c01000807141c0d05c0d0106100b58451028408180507410102d400c6c4681394010000600f154142c0c6030080302e003050b078066600300c640345401b180760780d541d520f00c044018204080c001907842070f910b800c0da2518800031051a011104564441c014400850720b410541010b6454001c00c0c0b40c00301d00c4030352040c014100c803072045060700d01d81000a054a02c40c00300001d010314403203002030005002c64110a0b02044003600b0350401e036001421130340080c20250303250b90001f081c03d000000c00e9006131802d0380c1607607001480c006441d107580e410400e400c411001d03152600c0c0f800000902c1d40d2001d0312005074504501c0d07000441c04d88034a41c1c00c0702c0702144ea900c0303800305076022110b000006640054040d0640b1111001d88880d602600b082882074003a0303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 438145746 1250 438144496 438144521
    0x603060b190810120b160f1b020406030f06020d0b01030501050f0423040302060907060201020906180f0a1401090510200c0a06052221020a08030a1106180601050d0501 73
    0x81213040c0080000c0d00010500c0f403420905003000802070100125640301c413003600b080014010b521414074240c15508081040c601c0208000b80da2540c80d580d0240c0c40704400c40584000350301056461008529005516680f402460100482d60400700040c3c0300000045206001d55512000403141d1901c840f86200008070070200b035450b5203464034000750fa401b01150480654000e800300020520700500903201c4105004213103030700f060303180072714220540558405250720980b0140103010680300c810703000010b0403205090b243d100c0e0f00c04002505c1e080f12540100d0043c060103000c034204590028080c020070101c001c141d104207625042e1103142ca21101d1189074442001c00001a2b0740e5000001031801000e0940a142d0003070b1046c2c4010003212051088166081800b00020741101b422f1307000d200072902c02408940d81c1a210101585160171507090480030903000b03c101c502c1c1d49020041070703034001c0052140192642900f4840c54a418061061a00902c0800718080401c0360a40010410314203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 438146996 1250 438145746 438145769
    0x606080708010203061c0c0905090309040e0304050103150b090603060d0b0c0d0e0a0515060121090c0f08070303050a050d050403031e020a0e0603040215030f010603060b190810 77
    0x11201d090314002e50040e40c010b80b18034000c4501000485114040c030010981040c2c08499841c640442d0381c020f450020f01e260b0b40c1c0c6c041080b00c2030003070b0b40d18401ca941e07501c140d400035a15141001d0000d4100d8012001060034550481c00400c24502400222900b00c5816550035499444140204d00c20407140e0000074044c0d0410410040c2d4060944090000100b8042040c0300c0310a401c01c20946070f041c00c4401802c1500540d126421078401c00340d4241d002401031400000842d403104600d1000400d04079891503141d265140316041c0001c03040000040d10082401030510303441d00b250ba0f0795454051000600348007000c106a04181d010f00c042d40c2c17001811400601c920310301031500034010004400421380b003400d05a55001960f41d035100365000c108103500d07050b81640001080141a820041c42242c4c410280c1022118414003540030b98010000d85400315100e50402e103000d401c1d071303985400006aa0703070244000001400b000c00c06141703880340c50914030407030b03201c2410030014048145c101c544281c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 438148246 1250 438146996 438146999
    0x150d1b0308070308090d0c1a04030e0a0906080706020c0a0924030f0203070b361008240f0103020304110901080a05120301080703120302210402040b03060f07050706060807 75
    0x6404c2031000c0d100780d20303c0d400da03011000300c0041036800c40190304020388400740d16400422200c02c142050303074006001c2c1c146124a140e1600004444150b150400b544d01500c8040030814024200140400350406002506c00b1541160104521038064403c1ca10019219040030915507248041c943ca00c3c480004081c4060342c4904011204034000d0404902074400c0060000d481d21000c0b0551b02e100c0321800008103421140318514950a1054030540c003940490700d6842c020b541c0b044110b0702104a20f44902441c0d1801072010701c6205a40b2010f0010581054402005036903601405075000c407090800680760788a9040103122034414607102ca8001e0190340001c00e44071030008040c90300610400444208030103c20203000640000c0c070580e0070303560000106000142020f000310180a41a1a00509109201090702015240d41c640d01c10a840f05209000960402d4080e9014001055004102c0ca0514481e2041030f40c20041c10503007005070105640c010088950807031802405424100d5003903a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 438149496 1250 438148246 438148253
    0x304030302120a290301060e0403020a0507120215030a090f0c090b011e03020307140310031103150a0203090f0303010801020306040b150a030b040e01050f010e150d1b030807 76
    0x3940603284800038610420000381070041c480c0244024081600f50680b01503801c4c580300d0182040c1050b15039455502c4840200d0740040c4000124803c9003c3e80c0101408542d03801c01905080c61038010844103005048141c0168998820b4481c0441e400030746c1607583daa540b21000d00406020388005c160a5100c80c1420521aa031201001541e4103643c08000e03070b00f216401501c13031000822034118806e060a001002c5030b0f01a90240d54450030504202c4110880d44961804981c000c0398420304040143c0340138028400c0d828410500387c94282e00401d44175640e915848441c100040c00801c909400000042c0010030600c001e01041c0705100490f0788030b50712820018044d41048441c0c600452520407078480900e407440c1d298a4049001c1c040503d001400e1408501622405030b1840c5c1007078884500b031441c00002d03c0341600c0307403c125440b0041541001c20904540034003804415200d04030406494403944e80409100c40e00341d0044104994100c8072035503a81c6442607a00140c840c2401140d080d051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 438150746 1250 438149496 438149501
    0x339030a03050106030b0319080904110705030a0e060a05180126150f01050a0503250c14010c2001090b0708011e060507080c010b040f02090f0a06020c061b0303040303 73
    0x1640c151740ca007408180c20030010701d50307685980010f000592040580581c04140500010f04200b60040c1c00850840001b803004640d9500084088400c0d500004105003000d52160009039805400c0303501c0d52a282005a004005010382c4000304404440e140d0b0110b80b5a01407640720000442100c0b4140e203864081c100074254090460f180072003800c809c00401c0340d03464245050796001c60143c64140c2041f19286084a10b90002810041c48844800e41d80c01001c03095245200250415070ba2158500110719250000c0c0010a00d015200d80c146400f01c15081c1d04400d0740784e00d008001d08003480c030620302c42d80300d405840d000b200130700070910394024081020750081c0a541a140d8003020741c0f1261043c510080d0120f03010f032113144000f50050050400048801005100307201e101d000104248251800150803a64182c0703c1011040e400070f1039034205e08101459148aa00403282d01209034940342e4061345a26090000b03a102d860000f940e0716195031240180407800d00a0008c0326140d1402c0c0c50003400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 438151996 1250 438150746 438150749
    0xc1401020c010b1818070503011407021005010f05120a080c0d02071d0106030905010b0a082a0f01081306090b040309140102070303050c070b0325020339030a030501 72
    0x2815400c1451403116803c102030b105600c114841d000984c0c50380c8100324600308030454075041a89020300c42c8006156a000d00515941545108614043d070502a4001e890b03d9208002d40d0f0010f800c1c078004208129503128103c0485500fa107110015072220102c00e82800036070400102404400702d444c5d42c41e1400000c83c13035840d450319021201c05c1703038881103c485840354004040d034521810740010300c407191003034002e020301d40e100744000700e00401c110f000102d142c140c58008522690001d07100d669100c1082440c0600d114004001017051620407000ca0040b207017a41e03500e0b05000c841008100780360308408003204015002501001074030342c1031501c01250b4405407001d50002c1e00000d00420016551038803000c06420507002480790030b29680c0c068400360014600e84285028407000043d40041c1240198402c15500d0510350311121320082e010101d0707429028a6045600910201901c12004441940d0000001c0742900a2400f180c0711410034000400382c0411501011615030310f01c03601600710700d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 438153246 1250 438151996 438152017
    0x10110301080c181f05031e010f020a020601051e0303180f1008150a0f14120d080a0906061a120a050c1e04080a082104110f010c140102 59
    0x2d848088240c100260490030b01c001080c900303074080101d071444980c20b26003030381200300441003240c9680d0b03200042e041a404c1c1341c165150300c140d444005c0085000b8800c4035046118100214201200a40002d42c0c0e150140038050049100399003d244000a034020b03041c84110003403c0300d55a600c83c03c0742c0c120901c8082815030140c01d0742c81d1000c540d4a0030f50204040328000703684a00c03140d614251065014041820016004000b060011955541b40310340b800190260098540d0707010380180c284100910020100304160b0000d9440d130f2200d590100201da002100c5210224030802c450801d28014070b6654480c90300b01540d000b100043e400300401615402c4100031803000300d0754400342201705540003120b40e0345400100300074100000b400301c0c0040c0c501c005811102030400da1100c0300700786080b1009a06850b050000f103201d440e080c50b03181480c05403091240c5c0c1c00038103050940d02ca03101c0e004061201d07480341c41484040c0c0c0650344101c03507090803903410050b15990006d0055401e8001d62001c903051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 438154496 1250 438153246 438153253
    0x9060d02040b0c2812120213050901120c2715060305100311010f0215040f170a0e0d02040b0a030b0105031b06030601030c0207171b100c0308091011030108 68
    0x8403184081c580c484861a0100341564200f4072059817103140084125a9800c14000209541551000140b000c0c1c140d0b9866a502e00c1d2506082c0800c0000c2c58105074807452685600c10920f2000840c10100d0780c045601c0d658828443c82071500d0140d030140d840c180c0707031038040389494440e02e01500d82c203513002c4c00c44407141c5081022343c96043d06d581501c43d85001c0038200800129620500b5441502100c40c1c1c0460391045d201c0102d0001501c40381c0b800c0a40f01034a041c0c2c0c141c00703848280110799001140720308200c80c04503d4001c034410041c0c090541e01110314030840d0901e04081c19500c6a400818110034004e00d0b2a11541d1a03240c074400741c4030300380503c2c0e00a210f401c60348a00140d442100010070300b40101040d0a503030702c0c0302c0118061300c03a21640d04e0440c080c03440005802c05580364000080f240c0d00c4042c2c80401420040808641e4030880c01c503220301000b0034400b50481e0006900ea0310241c1601d00200c0741c3d0b480300216850440c4114103007901c0383c41d0008140000e400d00004c2d6041c1ca0a550a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 438155746 1250 438154496 438154513
    0x11161412190203070c05011404050402040b1b030a020601030f0c0b030a1b02070e130609050d0c060c0816080a021b0703051504020901090510050907120516021209060d02040b0c 77
    0x4983e2130090800041103400c02c503000b84041e40c0150a00c8900c80c40e84600c40d80351a88803004602079810681c810303d20301d400412601d1049000280340c00ca00e07103066000398189104090000d40d07034031040c480908504040da031080705001c1413031410b60141003008480f80d80c03030804001d028002c11151412103d001040303400700c445a40b0200b9508100c40c10024183d0507502c0301c0240c1c400300180200100c507100c3d81c9202d00c000041003400038a880b09500d85511401e04110300b011001d40703400700b201404000c40903041005071200301030f04880b100e030203140a143c20b5680d031380106d0080c42903180089519205044a480050740010401c3c2034070701c00c0d01a5100311046c1c000d201e01483c01501c0095211700103200501091401361300c1107500c800c7c1c0f4242c6002190f0380e078020034440801596031a00189010581d40060103450281c61b07003011100030b5070066090014402501c1e401c00455500110b140003c4000d1541d950200352246e44506040466541f030b0f8502500c8482d40c403600b02d00d1180d000314404d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 438156996 1250 438155746 438155797
    0xc0f060609070e0402030943051503070c17040504060b03010f0b0703030f020307170912180117010f080f01050912031f030c061211161412 61
    0x1560b4018040368036800d081485078002c2201a410041100c480382c4528485070b002054001341c480c40300d881c0b1002210500c103400300010300d03001c11030203044218640c5040800840d113030010000312100344200403d880b0344409070111010324080d80094102e2565801234806032907100000e000301e400880c0c017000600d9441c60000001d0109124100041d0184901002404001d1008042c0c0034440c0c900021040c0141945104a80041d10348400180c0b112104208241080d040750307400c44000401450303442d00b030289102c03142c4101c034071081c503c03030f540101006242d0090b01c0c4000a80b0140340da400e00d44d0f031100d50708020040d092085541c94031440501d4405100d040c45118000c80d900e4000d842000202c11521115a001800010a014901080401d00e1680c006894082d520403c8513540c214036010000307003030f404010700c03c03000c407031401c006040c00015001c01c40c0c90141c0c4844042142e1522400c102c88401411114500d440c06819030303545001108100038070024030001b004901c3e4040202 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 438158246 1250 438156996 438157009
    0x2803090c3203070302010e030f0d020604200307090e16080109060b10050301120c12030c020406091107020d140f010605040c080f15030106150c0506180a1203110c0f0606 74
    0x450594243d04024010b0015512400119100401c0071301144c81040058030b0179440c0460704c4616000503001001070104111501c54100c000701c4010220140d0307900042d00290b12090746110700d20240c1d65582c030041010034180130080d2089007400c05845142d664802150190940320000c42e001441c0c1508406070b841c1640e480b4007030203a103a940768116805c008003020320403800f2800f502c101c51031202c0002c28845215000446602c80e030384060070000f0901c144003c1d54411b0b004940140e090a65900380d288804090f2000c0a804558111510343c00e8100b040c030306c030f1003c0c029162600801c81c0d010032080c0150003c108440045e6400c0010448800d4200c0365800301361898a000303101c1001007040e805005a060040385001000014030940e50300c200826410009000e101180c0c03102600402e020051121503441300944011400c0300385480a956281c09060000502d01c1e00c481e143c80004900c281d1006074100350030b054a41c1d03101440402207a6a41580058903114070075000083c0803400e280 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 438159496 1250 438158246 438158339
    0x40b07021801180504050703021507120207080a0f0f1a010f0602010501060806011211031e0603010603080417011e020d0e0f060a11070f24022803090c 66
    0x48440c80e14542c0703d070788009080054400c1c0d130b051140400200140e03540c0d006a40740e1061400040c3c0e55a00f07546400306c10308034449056015904071037010030800c8000300f1040701c40380d13016201d008a20031528082e140d000601c5400f80a0190419046105030341d550f084906983c2800d120854040da503990481c241d03142406188006003811000c40e1207540503264644003c481ca10002c10420b212040718015500210303000000e034100e2000c00611400b645409640111007580244220707030440d12a40041c0c42107104e602e0703010b4056100029480000e6000800310b10380b100c5940c0c0d6454011f041c01c00650069004500350628148644068420003d80100c0342001c90000e814155215400c0d68000d180c0d00d40105100e043c1001202c001400c1c10203c00e210b24403074040c5007900500600801501060038810b82d90140c0b0412840082103003100f00c00d07100108002a101c00041404001c031b0103403007120001880d840c8039030008a1005410044080203060200030005000106030b2500e4407407031074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 438160746 1250 438159496 438159509
    0xf07020708240c0c0a050102130504061401140c0d26040201090b0310080a0b09010510080a0803101205010e0d03021309020724230106081812040b07021801 68
    0x1540000c00b8001c00300c411581c0070b41880001c43c100303420b42ca4510705006001e40304a500d6580010400c041c40a40c2072000007400c0140c400f04241070400c41049041c030221121a41433004503110044118290f001701d910380c42c180740c19144002c2030244040d11031604c001c05800c00406692101d80102350204089110700c5e0169034407544180381108001540c0c0c009044c4c0385283c0342e030910100d0f50304400c0201024880c4130340c40d0800d15160902d6120308444000e407400768401c2e07442c0c0041054503400121070f4485504002000c0e0b5070f44640c003e2501e440344541c040401076520280c110140710065000c0d50002030003100b41d454001220a048040703204070001c40714010032540e402e000c44841d50307000e042e84034030402c00d40f0301500c070b0008810b43c0c003021889254404c0d600c845002d0708400c0c0c00b456078110311043d210040701c0c80d4104075000e0007402e0020521030a045c50440c4040c00309c00c1c10820b8411012040c0d80240c1c4d9651101c021510b103521126007680103003007030040403004800c5c3c182024107c80c0d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 438161996 1250 438160746 438160783
    0xf0605070e09190209030a0c091103010302371206060b03090a03030b180c04030c23040509070b0c0c01140403080712050c10020c010f0501050a170a0b0f07020708 71
    0x580340312185000c0360358a0f40e1401c03590309000e1268180c908202c112241070142980381100c500e084401c009031915a440d9012544c030500c01000103854104104c40c01c07110012802c0354420111010f50350740d44112184002c0000400340c00a02c1207140c0000701025030281d442400300070781310768180b9200d00c800e0b02c003038074182d00180030303100481d2103a802403d0001c37000b062903450502c800071402c001c20064842284036403000408004001407013080340c1c000d2400751641d45242140b52010b4550f12501141140a1500d9030001403600c0000d12841c40a0000723120015114459940556594128030071030601007640c0d60038001e1a035030000190341c1144d501001e10f6140043c00d5607815064215110040e0034058207100a00b9103030810302c90000f404281820058566485030340b92402d4804104503510800d141000600107500c0381d142c02002d9032130039003000c51180700e8084118038121035100087d03c9807061906101b140300003411640d00444455080b1055503072100d02d1a520b07160400340f1034900c41c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 438163246 1250 438161996 438162001
    0xf020c01020607320913060303050306120a0b04152301090e03300a140711150906010806072d0c08070302100501080d0210050907120f0605070e09 64
    0x34451300d00102180782c501c0100302c0d2a000b12184419490403654003d040352800b04203814203041001101040121002050240a1550301d001d021072101400050007050034003403800410008000b4040903d500505010701c0c0d181608180300020020754441c00b0090519404a000c140807144203210b44104104400d1242d2034070b034039a001051221043c0801d80030900c2180b0854190041c00e802690214410000302d01d14581904458513000304000640c80c58005908a0450044550b903881000340c10692040c203000104141380041105500c08480e1403007080240d004c0000c10241c1c101c6003420211899921400c2c0252014900210101c0c6401c0901c00c80010310149103140c8450f14042d0b01700007011808036240e0481903072149200781e025034051422050102c1a500c180383c01420301d14003814203012035000007034680320b840455064964036203020603824542808001e0061a004100c401450390a01d003c641081380c0390f405071009854500051411802001c001d071500200820301240c90303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 438164496 1250 438163246 438163261
    0x316050f04142e090e0d050703050a03200c010b130b0303070b04080409051513020a1403060a0e181203010509041506030506270118021e0904030507030f020c010206 72
    0x24042042407030003840e60710a207901012030303c450101030100100041006058441001d2030f1030b8007101c1550401204000600100758090165805002e642c5000700e40f40c110300038000c01050710040d0340c1c41100710004501040c2030055022000e08442500c00c01001d000862246048a4004040d41d805800030002c3d440080c084441c46a07116204004003410a41c8841805c41115000c44240240003102d426803503051910041c843c0d03040759103030015407901ea034110006101d44c001424407104030f000880030074860340d50690b01c04003502c40c2e4079417500da910744414503007074004108100c20698015641000d0744c0c2f4500740200c0f41614006480f0294a481e141d44156100d410154038030110390781d80001200107001401403d015040f0044000c1e015416040c21115280794070310510f035181e252220310000c0400130071400f407a09030100d600d000c10070007503814200c0000d60503400301d521482100030042050f07003040c05024128002c0d40e038000e18161007a07003079a0351884049000d003d40d101c100010f041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 438165746 1250 438164496 438164521
    0x30405010c0b0901060806070309021e10030b0109150503010f06050c0d080711012a050408070504020c0a14030a090b12040209060d0204090b04060e120403110109050316050f0414 78
    0x1c20f84480c00040c3d070380e41d240100780c20084140c83d4000003a884141900940c64458180a42001044034504100c0b0000001034032543e041c66003d000d040c0c0f02e251600541c0c1c000c2e034030400105400120003108900d000c1c4010100c0d80709018084d82031094080100b10688608242c6801d002040000c2140000e905411381700000010810020411380b0b40d010f00a0350020f004e02000789000c908103141b0340c2d80b0a50039000e50602181100d080140501c020005a8000100a0120340055800513562402c06900c58107140301c0c090040c0c4040b0b40c41070031a0f4071700400002040803801940d03131101b586465111075075a5100703c404d40d040d00b80c2c40a0208015240c0007a01541010303000f0140e540451040e40490203860031103200fa90703c54041c130100801c2c00098002c01e8200e0344044060705002524400c104a076000d02e0201408458225800e801d459000b02c0d901005404000e045814030310201ca40c0d000d0308201405014040ca80b020918400c030f0900b8051a0036aa0071b44107507120503a40d0300c1d1007010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 438166996 1250 438165746 438165751
    0xe060915100302130507020f012703020304030c060203040501080a06051e061c02180910060c0602070c0e04060e01060501120f110a2a1e05120406110609030405010c0b 73
    0x486624010002c0160b07202c0036048800403040d1000300b01458498400b90030070200e440c0100c07c0d42d042204400000510144180d07040e401038050300244522130a08034558059034100805d0640b2000c004034416070001701810071a5000da98010170355407405011001c0e1400c40c8a59a0010010f01c0b400040c0b14a00c4415006142c024085a0a18070042100312050340380141c406a00c6030300090f40b40c90f24105803844007104c58117960455050910420715846041c1d58410082040401a00c0030100100c81d01103e0030781d034001c0c2c03005c43c800303844660003500e09005842c1220780c0b510b00780f5154003195060250008461050712442d0750b011600701030501a0841c4880e242e8180c0d84c071300000c0307100282c120241c121560030340d030707900085042e0680482c01c9440303c2024000c0c1500308001031001861403400000140c3c3c0d0000a00c2a100303003031070020720708102c800c0e0011211401103004511142d000c22201d964000c480f003200c68644500415a0300ca02c21170007801d000460340e10184010803c81e0340201d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 438168246 1250 438166996 438167011
    0x17130e1e0a0b0d05070603061a070c03080d0b04050f090d021506010e030a05060106200105130204090201020a020405040302061006080105030c1507050a2108061807030e03040b0d0e060915 82
    0x8810360080d81e44e181c200b50341600001c0100765201d105016849000c0d1940d1040c00c648444507103889015110040107184602c0000c0032140c001410300c0c50b107c0c0c01c0c1c00101510001030024042d0b4140b450f002c000d080c0d000c88200e00184200c2c0d0305100114800211402c508607000d0010301241ca851004407440102c05502541503c10044850001582000b1440c000d240076910310a84068200d20740030541c04001425080340c1c180f02c00c0c88500b126805103800310715030459001501e80120720040c0d081900605010394414501000c0005141d004268284101092400b81c0b64154135941e0aa600300004e02032941c15600400040307020f400c000d01505074458800d414542000100e0b03031381a140c000c1640007161008140002c1c5a038002a8101d20f00c49a0110700345600d5514000c1c010030048d2030520107146842440c040820000f0b4001e9021a09180c982001e0320394550703c451240d01c0617840f55405519640c41c0c040012070314000800c1c06801042c080c1d003c0e1241040703481900310424409807580 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 438169496 1250 438168246 438168259
    0x3031503020607080d060501090815072601050f1219170f04090f050402011b0212011107020f010e0d061e180308060303130b0717130e1e0a0b 62
    0xc800350781d8034005401c50a00c59541155039001040c800b90a55081d5403109050141e405021300c104500840c00c00070a46048402c4110303071345c039050101c0340000c0280070f070850311084c0c0e80c02d401e038031148181e000e051702d106980c4c040c044014802400041a00902011541d03040710560740300e8a10800b030400140ca002d150100452180e10220074800e902441007098640800035003042070300303900e009000c0c0122102c01c00300000d26003900081c0c0b14001280b4000540450b02524404558860100320a088c180c10005c00500403284194130300c59010840580c8a08401003040040c2e602c20307620002c1200c800742c0b005400e440b09940c2d500281c50a852298010201041083e0100c101c9100b600031510820903080742ca0850360401501c1010003070500b60280d0410400410301c6030a4000140c100d52142c10090f0740c3c0c03100d41c02c00011804c4840421110760800280402208030b880d48c0c0f560030784408195544054403011100b000002070008450b01000d80c0d4400030703d49101030340c410210a80041c042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 438170746 1250 438169496 438169499
    0x2241509060d061d0f010507080a02031306020d02040504060e010303020c06030c090d08030103150524010c050304030b010e0f0106080402100c020a061d0f030304171005250516030315 80
    0x290416600f40c45810410850052072034544d0300010004d14000d8800007008014a0800400041013400000c10340003029030000041001c02c00c91090803665250011400c540b14003010591001a500c140b042e41d02c00c604215001c0360270201c242110b412a60305400030010308000406006607a0001451200d20250501c0740e142c0d0741d01e9400072444014412902c00b6079a41c11850240d0726208402c00010b03040c1d15180401c03060a55954400d5401c24580807400c492145010040310142507200d4020190f000100d8000700700404410f86070305071483e1400e440c0007540c07840031081090009210f1600082d1804022401500b0464842c10500581d4540900640d03200e4000c2003441079103910120000d29030540c003446603012040c98500d10001219031000d42289540000e50301c0c0140d014002d20030500d180c694558030030410002ca001c0000300702c203228510780510742c40200c0d01d40c025061001d05680e0000070440d40300e04101c2e840c00c403d003060340d410780707445440460050510311907124000e01304410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 438171996 1250 438170746 438170753
    0x307080c06032802070c060f020f120c07030c0b0306040b0303120c031905040311330c1b03070b0709050d120e0303180411070201050d0203070c020a0602241509060d 72
    0x2017045034060640c44180c1842d01000504010203101008115081046040301c1c058001c02c40c0820503548500d401d0f1941490b80c1c0c5d403030a120240c0e00080c001103000800282051b200340207940b0840c8200d40800016103c5814562207104040d0400590940c440c0000c0f1007860b014040d50308800b02e006080c04031050b2a0300720040b902d040d1000d601060356141c02d041400b0082007400d918950078150030f0071031001841d140000003a01c0206120b07034603003500003c0000c03000c00203503880003c0c0c0c2d1542424980c41c1d88070071a1682e0201d203042c0d4022000d8400143d255020b440d401040701c030054803200e102a026142c655001c80d1100c91441001440b85c1d41c030032240d4007000074111041c030340c0d80c1e1201104101c1040100300c421500044001e080700f48400005070b0b0708401610140e1480f0b200142e52642c904200712020305d0004e40080d8806012076000c242a039001030f82c100340c0c0342641b4007a082c2001a034098120400d04441c45084120081c03c01e0801d41007154001c0c1d0801e001400000140c0901e80c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 438173246 1250 438171996 438172001
    0x1b06161b0816030c0611090312180d080a090b0412060f0b0a0f180e061609050904060515040504021e06040e0903030405071202010f0f111005060307080c060328 70
    0x5420f500051001e124007051240d40d200b80a49501c3c0c4044852511302c501c00441d0f181d04010031084040c07100803c0368022095010500e100b01e00c0f0007401d07604800e08038030303001682d5000b0341451400501c24400203d00d10500d98101ca0039110505040f030145d560980d1a1005844032103c1e01507401d4844050030215151401ca20707000d0100e600701c041c0300d20305088804101124168a460945040103140c02d44403030003003a0a900561185004002c2c02d506140940e1282c25950180e80c01040100030030080c8107681d40094054042c81950424202e0104d0411080d50029207010354810760035070000c100300c01e05c1d817204003101c180135003c40e0519640d1504014003d904450350540ca030070001c1041304001e0240184005080800e4480071004040d4000819a0000400080070b0080f100012050a4010301a51402c510120300300c0d02003803915042c0c4005008180e803000d0003072240c41408030340b441022a08809196015102c1411585c03541801d10385520003040b501c1c1a4914241100c18038035650 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 438174496 1250 438173246 438173287
    0xc08030c130b0919030f1118040605150d030e091b07060b0f030607080c180619021b0303180d02060d0506010f05030f04030c171b06161b08 61
    0x2030102511100c01c0030a00510f1041103010302c1300710009200178000904043c800500d034035000031408980550070404588007224283c0c030b8110001011003000101305003600032600c680c0c2c4580c03035820900304200500583c2484038000501042810000b900e09080071340c0305030390015400261001800c0d03018001025944480c00075130300252200c40108035410704060035080c4001c190010701c3c2c64941548018940e00c00a8264401208009040c11110a901e14a483c84c114000c0040c0d50b1944c4031017619846118010482e0f0146c0a07090f40c040d15160302d84034105a100d00034003d1450005040b140c12134080e12800007c2c1d01400c1702c6621000b40c0c89020182000b60b111240002d01400c0900014140107401c101d000c0400100b0002c01011440661072907030442e90506294a840b007403403502d807600d456160300c0003400b1351300820a00f80c511055a00148604045005e840042c0c0b00e07070740700d05004070a403541c07a0003090407108244c1032044064030103400796000d400705038104606452081d6403203000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 438175746 1250 438174496 438174509
    0x30b0d05060604111c0b040204050a09090221030f21090d021009020105040909021503150a05030a0209040b100e010e090f010b03060109021606050a2702010c08030c13 73
    0x964104819070a11340f0030524110828100207041002509071180c40400791000fa01d1020740b41d0140d03410589540d010f5601601c0300900c54004640c4404d0384800800640e030042c0d01c140b4465141040140740f4642e02d01142501c200950f1500c65000c006090550010215801466046405e50a03503a000404240100341d02c0010f00f0710100fa42074000d149c000c2c05008911a58035144d800d50050380c000040314122403d549003c107030146903000103004211007844140d049900041080310802d11034403400e07807c580440b500b5031801e0f20340c418503946455591340290401880c90106002c5050503403d65408a60410119001900c840d220301001c0b00030782c0050140304500041c000907032018030000c3d0003409014003c0209150200000e07554040c181b1484c440310b54001501205c3c80c0d9000240d89455030403040a00c40780c105030940754018640042840040c0c904012881c408801074654842c040c1c0c8c050303546110305800380e102c00805900c09450140145402c010701400031450300c1580300107169 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 438176996 1250 438175746 438175753
    0x120d02030a020f0c2412180f0c0d140307080d0b01030501170a0305180d050d022802040f0b04050406050412020703031b020102030906070f0201030b0d050c10030b0d05 73
    0x100d40c1030283c0f40500e100741195994001c0d208400c080e8a4803203065802d981c03503610650415100720b80d1036015200d83c4403866119a19441006207a406104103000300500c41da040364a901c503541c50654a65105884140e8003402001140f00400c400c140482c0d51000d00c501900d242c92200d5480b58140d60052031802801c80d02c440300e0a00030340e01031049600400e5485016081c45a4201145480b0052500018188640428a0512005011005c1c901400082e001d0038074281c0380e0a0442c0d0b111114040800148070703c4500c150200030401e20b400c515581140c180811054540c2048090b00f605c03254030312142e03501c45031154240d4031401410b020f40d00414000a00341440c1c285603e00034010814402550300496080001950105d4800100040004540307000905840102d080d841340340015944064082a003000f40543d160b6484070103403003602c0030003624644c4014000d03144820140031740540c209418190160800b9507030b00360503e030703d40750014004030300c48005100b18506990544480d40b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 438178246 1250 438176996 438177007
    0xd17040e01080105010509010b0d0e01062c0c0c12030a09020d120e03030a120515041104170d090e0709030b070f0201050606040e0c07151e0c030c080c09120d0203 71
    0x100313104541c00b601c030940750b01d040c03981003039880300f041d2103a00c03101b590460f07607030080007504d4000303521035006403040031113924000c8030003100d484a6243c812045034400b41e5003000f150052440170226000e0001c80c3d809452594902962181d481e00001c002c1290251106080ca0040e510008540f52240c03040c035040d40d42d40321810000f040450034100c100c0c0a84d008000c0b4006007030704207040343d6400350155008159696160121130245165080c91504903007045d80e40005548810060802d80301c840c009500d03119400d800c0c05564a0b110000c600205030805420f00007034415180c0c00b0340c00416401c003240250f540390380d003140c40038003180d940c00044c1c036018407500801d5080c0641d0343c11441c01c0f58241c0c1054100301001100d20030203003480c038400c3c000140000c10482c61010b80e00d01401840801c0140d10320141c24076024241011601d601c035490f01d50341e46049030203072188009a42e00c3d0b0340c03441e126a5031b0b4201c451003a808282d030141d000030005100481070b47e00308500000c0c02a2680595142e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 438179496 1250 438178246 438178259
    0x20a05040e0709060801121113140c03060a14031f0f0b06041508090a1209051302210c0f0408010209010908070b0306010302030a18050a15060e060d17040e01 69
    0x11100602800700f00090484100081d03a404481281036400c4888449583c0c040361501c1d030038401442411f15000340b01c100d4840d8990000781e0240034640d003007884415035640c1d03211084c40c8a100464102e40c4c0044880c000344000082543c614042150280807140401941120301620003e0806005141600c8000e010000002401440b4aa540c180e907503a041c1414038004078010703138021400208100d4517500198240c601000542070b890342103a0300d0740106c800c07418014038015244c0210f40c01031a0f0030300310380010307404d51088030791080300401c905440c80c030301044898407071a0242826801c15806c0c8561101030039004000c2c40180740840c0016510458400050881407042c2c1c0928100c3d0003d0381300f080741101080445c1e501090919005a81e035580d1462a802080c108581403070103564103003040c0800000041070050036029810506109140d48900e80036201a401074443d001e880c00302027219410a0b826030484240b080c8040e421050180280383c44581080d4003440c2d03c01801c00042104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 438180746 1250 438179496 438179519
    0x30e1804060b2e05070b0a0606170c0703140405060d0f0608011509020906040b0304050c130606020d0813050f0706091505040b0702040e071202090a0c090611070801020a0504 76
    0x160001940c080c400300008200b400c1800c25082030f00f405541e582440d46400f18403d100300c2c2c030313801d6120030f01101a080100d003442c01440a0300818002c98811510000c24811850300240b00d1101e54186078a403259559044807180007089034198041e03000e10010a003039407600c0c0500501034100e0400601c8071484a1b9000a484050f800114180d25040000d40c1c1100c00c40d4104050301c0c2018030159880e50b06001182040c442c41d40b0aa0a10382c02005000801030f02041c946010501281d2000c551042456244101c0d003151080002680c0086405e1008502900113640e00840d4000349440101d0f02d0f0720b826040440c1d0300b1031178410b604030340350a010841d0081900006041100754040003035503808805407803072003280200c496403400401c00340708560310340c0c12000c0e01420b040141e5a12030f0340da0403e00d01c3c3e103007000702c2240310b01d045000182190b00c40b0310800405185958074a009a40391990940f00100d1240681d00540075091020a02c05004d000600e00c180c4c0d6513030f505a483e460700041444 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 438181996 1250 438180746 438180761
    0xc0f061b07110307151115040209010b0a0908010c0302040326090409050c030109110a06030c1713020301090303051e09120304020105070618020406090b090105040f0609060b0d0b100804030c030e180406 88
    0x140c0d07d44081480050703103500301214152407400c10495500c20042a040d01e1041869220514039030800844194165058000d4001c0f00c3c404c081c01543d003c03001c03000d0401c10003d03414a07100c8000c14042c403100341ca42504001c1c0900d00170019501034055050100e825240011802d58090011019040044c14400414401030400789410806160f00c0390004052042c2c00c550035200070421400300360b01d040703085845c4407296401402000700c02401d10b400f402800c01104c00c40da4490084184090440128282d688620040d4000c1c00001c0d0303a40038400320740c0e00b02a1044c3d0404c0302c2448608001052071040b0f641402d5044070341140301c1500d02c100300540b07045030808101c003401c3c001604200e80ba13211103c2c1c1500d90488012444045206c5c0f0a00104100d80c840300302c090074800001401c50900b002080000c01080c4d007840760340000ca0034030400328500d040b080e00080c3d000001802003403042e406010303880d100389400304070400000001600d05051070044000c0c41074090038001003080030700c202e14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 438183246 1250 438181996 438182023
    0xf020906100e010e0111101a030309010804330e1b09070c14010f0f0e0703030f110705040507051c06060203041a09060c0f061b071103071511 62
    0x1040038020180051102d007040040070306009490240c0141a8007030421203c81c10104011140000c01c205901005001c13038030748030030b22003140304d0b20756649041c040115451002c0685903230400c0c0c0c07120303900e00120310274010a06c09680c46c01c100000d00403040803000f540c08081500701203040080285a503041030000130702c0c0314406003410064030541e00c0d0a80499400311045c20450306d081c0050030300b2400301103004c801c03099a52808050104208543d442000a921032400400110128060007a6503581c01d00018020691913151505500d00c83e09407200b40c88401c2c42130b18810740d070f18401702d0709176002994010082040454003020302510741c4030042c0809002581030255614226020303450b4270442c003032542002d84c444205c07020342d00034508a401140000d07001aa07208142210310380c4650111032503030007500803c004a03000b44506400b2140c0b0b4580055560b180074078a9540350901c00e110451540c03d4059200b000981e80a03401000c2c02c0c1c641152070351071501003080354203070a04141d01e6149 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 438184496 1250 438183246 438183259
    0x30501050a1b0e03122116091208040302030115031b0506160204061a1b150106030b030f070311180112030305040525060f05160312020f04030f020906 66
    0xa0b01140100c1988190100c1c2481c26841000402190801000f400103103c00c2d14000340d08603030142079010b41090594419079078201034455810340c0c000100b150500b100010b00e903807801d120751a2405242c026152013104403c0c9010b07600d84c0030a00b9584101c5054880c1d001c2c9075800c0040c03112842508901c18080b5101143c00c5050500058203030148540728115150440d42d18000c54580381c3c800c1000d07000c9400203501000700a821504103610060182c41c0000c400d115542a08000141810711000c000d200e08109a003024022402446c004040e554580300f0003180c0002440c0c28004403000d18040d903910402c00035108140050941c1003107032442210240c038010040f0780f8059072192801030b03161602050340e0b203072420410b00d0243c20b4480700c5d03504d104c2e0884040054521310901e41c03c46155484a020301010200d0a49090003000b50030340f203035903180005500003031140001803d001c4004070014182440c0308500c0c5016049a0030496032070b4000355001c0258689a034880f43c0c04142140c01c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 438185746 1250 438184496 438184511
    0x9030a08060f090103060b04060b0c030316081b090406030605070801081b1806030a0b0c1926040302010e030a030e010b040204120605060105070204050a0b0f06030106140c1015030501050a 82
    0x100d03c000c4030522020341000d9a800c1550010b41e50780c0c01800c02054011849520b4018404400703450394805da0358202d101e4034500700541200d0140b020184104141a08110560318241c0c818031260b0080390541d6205590307500c00300000322284199400303884141d40344d26041d030410380701600e80380c0000209000103210b40c3daa2107441d0368030386e0026a5450345125154042c3c07600c0c000300b07142c01c1c07403080014000410007082101104059001d4000003100201d81006c00d85001020b4a4000409aa03103400148080d003020b000521401d565800502c00e100004080c10030079545811500f1202c4031000181c0c850b03101109043c1c0c02d004100080a044500314540741ca00350440b070342d008000800400d410b441c1e0001980603030140741aa01120f80103401882640740c29406040102610710483e80b10380418002241c0c1414180141d070b059404545414008610348a104089a041480d6904851040484400d0b070000c0902411024200c1d080d90400d0f66811494001e0070340b2402410540c62a107003214 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 438186996 1250 438185746 438185749
    0x41401050903041e051c03140f040519050a06021614010e130207080703030b090f010e07230408010618020f042d0e06010e0411040515040e09030a08060f 67
    0x21902160004c500441060045121381e011003d8940d01c140d5103c501c0080c0003851000c40400522407621a540300307e07182c240d50045407118080c039040c60720152020b001c24403041c24800c0c071083c003c0a90410b00c0c2852907403400012006801070f080b20700141c0100302908406444504594090020002800750240710742000070110380c0c2d2600002d10038401000082c40700354241d03045034402e581007641c140d503603103690a01401412914040074010280040095800c0c2e11140d51719060f10414000e203102500c603214211444920b1400303150904400080046103184098014001006040c0011031810f20301151050000030742c107525203080f170040244104000390f140c119800c1d588034001c05004004496140080340c045003500c1004080c50142c0820b201216031034142c4035050036a41c14000c80550b0050000750785c005102c405120b43c007813106200360701c2d0405006024206c501d262a04007691902c06800b8000d058035a010f80b40c0001890469082d4450641d9a00200503184000340146420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 438188246 1250 438186996 438187003
    0x110909220606080705120a05060703050903090301090b07030506010207080607031104090507021501050105070b04020f0607050604080a0f0c050a03181503060509010f210501021201030b0414010509 86
    0x346010810040100c04440011042005011241c1c00c10380820140c0d4445010950b5405240601d610550010808104020001442e81c2506d540031029120549520800360084c00020308150264001807000790f003652424400c805080e07019003801c1a517414280000b9040b918041c08103030454111100601031240c0000740340d50454800e1400060200d064070030b0090074092a0002c949260801c8180500d4035400039030a07880555060081e409a6a07130740040d11148500f00d00142080c194200103009494113030a1060f071418042c0c2594600380803a03036110709041c012507080f40c407108040303130404106074001110326544000c2d0501000c0025070780c0703615659040c0c40a004040254860700c4070717940900c0c041128001d011451104004144400c005405008980503e43c0a0610a000000d4460140c030541045880090740e0b1054800c080341c01200841c141d11041d5110b6400b0840303290503c00305040700e402540201d040304c0d035038101883c02500c0d01c681042501840d1f8100000d000d140c80011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 438189496 1250 438188246 438188251
    0x5010614071a07230a0c080d06150c0c080c090402041a03030c071a04032303041a03161e0c0f05011a01122a050904050a0c0201110909 59
    0x1081081d210111440c0154100c03144110030355064011a060102481e04041c51004043c80c40d0410303074029002c8080c100d45805021150b40024244d0104000403801c008014081402064070105280740c4851166140c1a285154440081c01d084955001c4c0030090880344081e00065001d0701049241c440050500e07031010300041d1080342e807480340c08141d4001e0101d2030100c00015060342d45450100e81815140e181920480003400103840515094603840d004940613a584626130002462041100c071134001c40d80842c0c450300788010400414106c84500c8410000c3c1c9a030040d0035a2403405a01070240710946800002c244803010f6140004040e02d54508241c1f406a440c01d46600400c82c02c0416030612a5000a042546019441805814142041e000149013a240d40d800000542000411a81d00f050946900c2c032500d448031a01500c54200c1140211003450554104114000081c04543c0309a2715014180d50399440c20251903020302034030403001050803076903050513020004180c466100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 438190746 1250 438189496 438189527
    0x11180a1a1b03070b010e06040c0311030403050a05040b030a090201090503010524010e270105030a0c06030c0c0203030c06041e080706020901030207080703080916081504081902031b01050106 83
    0x1ca85406103074404009480d6415001070702c03d8000d594407594886910020340350310303008505010040c0e2245009004070328180400d5150540b0f0741c5d90b1910200e030540c2066070000100075007000001207220307025003e18042d100c4010005101c61580c40054181c41182d4060b45c02a41004108950040000d0a068100420080e2040c03072850040040710100c0f43c2844095200340c1d8410208a080c50b0a4800076a1072a815032010035a40c85d04205955002c0c4914000e0003180eaa090500805110360410441e15a13541018a0703109038a500080c1550002078130312855502c4030307041005000d200c14251080da040542490340210745501d078036100e8400c1d042c1c00383c00d00d5000640340c0c8860348a40d0440f814540c009105644a12403494018100200bd449030074030342c891407422180d1008030784612021500600020642455500b0f044400c0b410000c200f640d4180052008981440020840e000c4180081d405140d64110408095010310a070102c4400c45a145c9001842080c2c2c11510b00301e800c03281c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 438191996 1250 438190746 438190777
    0x106080f0402040b042702030c0a0515161205030f06060f090105090f1203041505090d11031c030c02070f060c0f21030f0b0d051e0111180a1a 62
    0x1504c1000c40d001d0280d46030502c80720084110840080c40185804030340f03040c0f08030182d4902c19801010403051064034080c00e07901c158040001c445054141000340850103103031400c1d0991b031340103883e5010708441c88842e040214800000b080b003020013010481381e2010b4100d6400b41040003c6031100f18600522080c1418094001900394880e0340b140c18034030029000502000ba1002c2da40e58080c1c41e900302e84241062454001440640a0700030800d44250f010007410300fa00801d42601d800c6103000145400740c5c1c25000c2d038a030b03c1685040400100040003d103850100b0f181c0440e400082c50101a580701e2100d4035030308801440b54a03131200103d400c2c9500406c15100f001c0071402c1c1501c0134404101403910807a04101001202901504560402e02250000300440c9503200c2c203200300381b18050001400ca81100003014441000c00007119118801c1c2000090307600003005031140e06502c040f4198860a100340c810f8175081c640481c1900c0500340310742d0900c0d0444001c03d4031104130b00681080849070309 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 438193246 1250 438191996 438192011
    0x70602190908060126010507090312030506060d050a0f1a150412030320040905041109040507170a02030303040b2215020715051f0b0c0303010b030402011b03170106080f040204 77
    0x100c142d45d10711000044400170401d5040800c0080d010400500c0100c03480b1042c1e0207000c0103140a4440c00f4490b550140c242c500d0082c00c5104200203210050001031800da46e0401680104135600c2152900c0d5854640395010003000810000d41c0c20418072010b4640318104400e002500380c1c0c02240e1078a03581801c01140012071000718017007880117400c0c0c5590880001c200060b01449903008503001d40d001e40340480ca1101d90302d040c0411180205c8020748982c5c006902040400032000d85883c4195104050303452281d0a81c4c00a41164400d13501038134003410903824800f404459041a0f00c848503130340760100074003010350740b182554803041d8088182c041e8017040c40028001c444001002100d400307034040045180000b050701018980300b92005810306038000204103280c1c100110b0ba00d00918500a40c1035a2070060040a5540024422810440003020740c9141d500c12200d24001144291034003100e07941740111030019400c0583c8110100540441030145c0d5034559a400c5412903010342c0c0215552 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 438194496 1250 438193246 438193289
    0x10020a03090f03170708013f050604050106060203090a21080a1e050c0a060504020402040f15031a010905010807030e070f061115220204020706021909080601 69
    0xc0803110300142c000014801c4907000c0540c042002c04150075015104a926100c0c1c001c1110034070002d009500c004a01441c181c080b460900700c0900018a1100d2006c100840c40300800340b416020502c11580d41e0311850501c01000028080c3c207010300020b1000b5400d111114000901000c121701c521010080058a8154034540c0200d45103030960b084580c10f595036008010081c0354018072188241d818132880070500404d442041111010090140103213500003050301d43c41d00034200078008070380c0034ac2c0c20480000d60f8000802c0fa04010081d45a40c0200900c12910142c25102c54404114107954036209281e0903a80000040080c5c400a10300a184c0303580700031040c0c1c006c2c001c2100e5004a4800c010b000244010901103c109071050f0f661050030501030018195520080380b4203200c0c526030280c00148410b0448140e005400e019503010814080203a00460304a80c01004142c40b42500028401c2c620011070f402c0101005131803402601162a040d1165103618042c040c00728030541140030903400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 438195746 1250 438194496 438194501
    0x3140309100c0f0e0a0b180607060c05072024090a080f0706030504080d0b060d06080c28031403090a0e0f01080312011a2505010f09020310020a03 64
    0x41032070610041088003502c2d41c0c060000d00b641c080ca103002888035003610300300781040c500b150115001003e101d420b007034100d203402d00341000365002036030000003e00010f8003241c0c040c040d040c0082981e843e010340e20b43c0541849101c01d41c0e103081c90340081300c4c1220402040d481c1d02162440c0d0340750300060b007841c50580118a00342886011041540070031144008161008085100b1052040101c2140c81159035a502601922812900039103c03039000d10000d032800d003e90b00984070b5001d00a00380c85c40e007a91511440304032061a00044c15583c414903044409040c50410408a0500150300381c65906138814140b41c0d04082e400014064640d51600601d1070038104161030070702d2001440c0d401c03210380703500c031000000e2070031558004540c128100001e803d140c0881241c005c403200601030b2060342c0c20003d00310210100a00e0180421004000f4020300119200b01ea5420783c1303103145070003a45100c504020b4251080c840303000c080603161080103001a5000034003002000d00601d001758070f51001e100180d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 438196996 1250 438195746 438195763
    0x1a040606030206180a0918020f030a05070b0901020115031e11060408010209041508250906060c0c051203090d0c03020307031b0f0b030117070b0c0115080a03140309 72
    0x42021012030460390400039408000f940d11405d80b600c0900e01d40da408804181c60312030681c42d890a0b00c00d502c0b400981043c1030800e640078000f400301d41400c0c03200e658040c0341080542c41202c1950012507072810542e4203014070500b8450b40d1805101080c155200c1008005141c8100c40400c2040b427440f6003001101c0d00e105440040c0141650384441d5940e5190380071754007042089100300e1a11080040e145e58601b900c0c401e658510008102d448400750361102d0407850b01c81c00c40c0c4401c0c1450300004180d4170501078400070784491360313601d15840d03402d142501c1c1302c0a098002e1840340c41c0d96040219442c8000041e00c4a1034000c94130301c0d0b50070542c1c1c1440c0e01580016080a034142c0603000010040c01030a882c52420301a5030b51351a40d101e540c41c41c005050b0002805a1440f40304200b0040080411440b0802c3d909819442682c5542e07580d00e8a02c031042d0700a00350048942d44908500300d00041d0440100c0003401c1d07003400360402d4941564003c0c2400001c40c0c1c05503609d0808400b145803c4020000340c034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 438198246 1250 438196996 438196999
    0x105011e1206080313090b090c09060c0a050607090e070305190b01030207080a0c0c0b030403080604020304050c0d0b0115031e0e0f011802040501170604030e0325030b010e041a0406060302 82
    0x994502d50017803240028a0741d8050707456510b0510701d4120041c1402c47d1600d00c00d800c04504181010301d00b000300002e43d0b100c4403050344188608040b01c808104280311550041420313803640a00103181511071034114000500030801d0514040c10402c14000030403203801028480c140004240300404c0069000303001c2c03000e01401c505008603400084640000402010a00403501450315076a2000e0343c4486200845000300090001404115241810340240d03800500c10001d89501c0445440498100782e100700c016075540e400c03907004114000300034000c0c0c1d80c0000700c0c0c038007801203080421529406041080041030740954a28041d445c40c0d0007400703859020b600080c000c1c070120031148400701c501e07141007078180d20440c5032000014100c4803800311040c3c501c0315800600702958450b01c003545c022548251842e054000c7c2d65040c512250b240c1800072803240b160034140c0d145400c5080c00c0208500582110b11952101e0f42400085102d004003043c0c28a54503001c02480c2d56546001c0b070240140382e100a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 438199496 1250 438198246 438198253
    0x9150b070614100605040b0d0e030c0109021f080115140a23190c050c030a0f0b01060806131a0909030a17010614210c0705060105011e120608 62
    0x2104220080c0c10821404801031021122502d035800c50180c03140f22441190045030040100700a450390000c082e10300406c003080c00268040780303044694116404020503d509175035940303035034085241a1100a0351900d40704005590403188402c0580442d00602500c00071458085102948622544100d5250746500f0880c5489429006000d42641a00714120b40000030440f00e5880001d107040603546188001a90b01c521440f20030000d642e50790719030009075200c0c020b100c10064a078070704005440c0c4d494410382d40d1b01400c02d0182481b1040f1501030b007146080040100030300005540c3c507006500300e40405e00c000200c0003a10314040343e228054800c2c141d0030143d024200200900040b0145c5203014260f114082c5000340e0070101c91020200340280c40204840403001081c9402d800d000c0c01100060007d224040c0e140d0b9a07030020355480454801c0b00c40ca03000101401045400e00000e4014034003801c2014001d0b410a0380a001002210003400804c008135a01043c40403140c0c000360014040c82c003e4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 438200746 1250 438199496 438199507
    0x7030206091c0311070504110f1b032703030a1e0509040510060f030e030406050d200c0f010e03030403080a090b0a05072c0d0309170105040b061909150b 67
    0x1030100400d04c0450496030050340000111420140605988141c4c3d56002c20301d006560040004590040d2041c540b40070502d18170400b5802081005140b00355040e0892803072a54030300c1c40c2200b080d038180040c5009410500030b00c110903422020709a6406003240d80f000c9083c1d0b1141c0c0441702030080513103117a031190410007403108550f64916548284e23015903640e0189c2d01006001902646c0b50800040281c0c4c0c010082045902d100d440982490810301c140410030903480d4080000e07103c00d1200710407100c20001141a608801042504682c450b1000203015050030f2059094807800010000350900c100d2000041d45507903e64803c1404942c8095407819030f0900b81040001020b0840d481004140d440d405600003620f602e443d02d10807052421900040d442f0305062141c18410b40710124280075040380301091050600308074802c064051070000846160030b04209144040281c8101c1c0210703601d92442190b41407040d91681641c41c41c95021903034804e0f5186404400c106a40507040400d004a03a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 438201996 1250 438200746 438200753
    0xb09270703090611070b01050f0307080f030408070f14010c020d06020703210b0319210c05120708070f03050f0703090305150c0706050705040b0d050a05011707030206091c 75
    0x82038038140e003d404204251100903c104ca4903102c2d040c00036003004604d0004112a00e80000101191440681030b14007130b603031307401070302e480d01c2e01c01c10540c0d2080e08081010b00400d0410045100107098007403450030214540407120f1800822400070504124000d6502025074895056000c13001e54041c87c115176a4107079050091103075140102c2620010040e12041078082c1d61070180391609000140901010030407c04204e8100009290460348024802d090b800d48a045074011425040c0319103500d5510409803800300e0415012260958000360103004803400b290824041d16106a03102c0c565a8076541142829038031401040702403414010005105010554042c050300d08a0344070b201110141000034080e40748143d011120324002000500035140401c080d40c1210b40c0001103802d049103042c0d00c46540b01220f41c0244280d20f070707040d10b401c280002d1000720f02c20b007401041151650248901c400d28407070703140c2c940381c84081c1c49030401281d141503d5543e9011050081031245007190f0a00b040e01c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 438203246 1250 438201996 438202001
    0x7031a0a031a0609160e030a0b0108061605190507110306011d0c091522090203010819081e130e010302011139040509070504060803040b09270703 64
    0x500d100b0900e0310101c08100030303043c0020311a005903261443e9960321402d080017120414003561840350301d0700c41c2100b800041180130b03800394080d19a03440540110b10b00304511842c4a888a0101410070101b00128440110000a03414992180e403074016070764411801c01428400003122001d45c10302482d40001800d0140705c8403014031848400b080b9072295181c1c100310b6824061509081c3c0c020140c00d0305504102c01f404000c0c9034102d400891044500c4e0680b070400c40091070364001c000700c0ca50010060048500420002c3d007070000741c440b500d281c6c19859603000c200780101905580b20003280c1060003090703402e00f8103843c60245000560780716035603035281500d80a4400e2009074007103280301541411440d80401c03209540040c400e01c14000105100d000845400400380518031500c0d440b011400341e039254042c1d80e00500c140802041c0241c1420200005c954195002020765801000208003451410060b100454005c54a201190303490f0000443c03020303081c544c000149201300c0e0401c9030441e01513 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 438204496 1250 438203246 438203273
    0x8190306090605031f09050f0109030c0212061303030f020d0e010f060b0a0e09070c02091602010c0c0b011802091201022d071202030c01060815160807031a0a03 70
    0x1401c1844041d43d541c0605442d821903176400340d62000b040b100b499070004107030031140d0040c2c403840c1160104801060300f907086a9440000300c00082c0280c00d82010341c41d121a800b019094100c0c0036040d6420080c80150b00300e04201c0d8002c00f41922a174a08401446581c107841600c0e103169401e020f9a54005801d41c000c0030040c0c3c103100650324142004c24600307201000d40340118515122450807000c41010012080700c001c04000800200721401310050326144010741c0101e110416044914252038400f90a40300c003850108204000e0b0110400840e89041c4064111828201603440c4804c4460174140a446001e1440e078010314403010342202c0c1c0005500400320f4402a04031132601140e1201a50748070380c0307881c615006c4420140404c0011503d404004400e0110500482e4601a0a80702203820741d400741d80b01000c00d0300199440d0019240007144643e00040c0c1e890b034143c3d0310300800c101901448006e420f44041613542c05100048149501c02e10120139001000c501304985d5034641000d488641 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 438205746 1250 438204496 438204509
    0x70f18240806010f180302102001020c030919030b040f17031e100314030901030f05061c0507030206070b010602100e070909030903021801031202030316080408190306 73
    0x100c0500c10551445090024080d58059489000c448180b1600f2940504503000328001400600400401a40c4e100c50b40c442c11082e0781c0700d00311303e20040c0b000010440003040c0c05005c5a401009400a220703004800c59607400002c441c1940c00b00d84031051620208669040200703640c042e10140800c0c440040062003182c0e12803d60303030001c0c0300c207078a40040d1400151855041c3d00c009140f03545030140c0c4a100b407035204605103940040b055483d120320381a1180c51011564030b400c00542c100c49564180118170014008410521030347c1800720200e41d4000c116540c0108844403030380c0c04800c0100500196000790f400030003640d143c421505100c1b0a09038284200009886541c10760b40741100240190000340080c00d000d4103a4501d4407980c94007405505108500300035000d0000300040c0d44403a80302104604007020032000790f04615001d412809450082010b5502c140208581040803150301c3c6480022071820a4507900c4078909500e00e806090782241d0342c01c100c2c1170043c041d50b615501c0380c1c00300c606 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 438206996 1250 438205746 438205799
    0x4030506100f03030f080414120d0f050613020c031909090c020a20010905120c15040b040302101101050a0b0f0105130e13020603091f060608070f18 65
    0x5071500d0100403000680f1000b000319040082d410381d401d00030101150f200303018001c10160390b01203101c60f600b40f0000e00c0c0c024241c0403011070341d000c00220702c2c4a8000c02c0240c840b01040700741000800181e1022000b06901019a0005010004410180103584010458084002140100c0320000d0301c12078141c080c0e266564a482e6908450030f10004560701034a42048a0070100064802501c4580c181e03409c0a1303040c400035070300004440c3c4070501d17850b0040c5e652a01520441501008001c1d08414504c40940c0c080414401840000402d000701c0301200d5044441c03c00401c0000350540704003030100c961403a07035480c25041020001c07058111080c07202c0d0885080110341d16880055840e030080151581c0120310403801402810941042103812034080920f12007507000039030000715651300c1220354400d19007241541100108c6080302d18010078101c1842801004d040c400004c05522001b411082080200750305201020301130410400040181c5405038101511104401110080e003002c484c5100c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 438208246 1250 438206996 438206999
    0xb070b060d0f020f150c010f0c0f090e070e09010e040302060a02182e02030d0b011704110a0e090304050102060a061409040606180b120f03042106020403050610 70
    0x60001054003809610042c81081c51403103800344241c504000d100076411842d59060580c00240200141190006560021401e41038880c41401616a859110b44c1031101541c41c80e84000d41000c038440c140c40419108826541c0c60600854000041a0069400010040011683e6403180c00140c1c030481c0240c00711003041d120000c07003a00302d01c01c9418285108803064200700c11403a081c5440c07040802e403041d1a89181c8074842c042250b94520700c2840025a00001e446001c1c41c50324003407040751143c2401c118186140051f281580c5040c0184010110140700b10101001d42c3d8080001004d02901c0080341c1c6907150840396159250312501845015120702000a15460010300405050b100c0f4600380806c034980840510080c040d000d081101d1081c0c5405005c10417911420150402da44c3c13540001c030710200d0120a021203007010b4060140d01340c0080001840b0325000100321002c4070f440c007244030022140018104c4070005038050085c000b80c0000740010501100269240c050f0301840505c40806 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 438209496 1250 438208246 438208249
    0x7080c150123040f110702011d0a0314010219020f0709090c052419110f060c1e0403060906051609060e011b05160b090d06090302010e070b070b06 64
    0x51401d10441000d0425002d140622801140e04020342010207000800c442d10b1080e1800c0958142e450020b09850300030544000755030344803030007000740341103142070202142c07006001c80c0e000710103800040c00b656441c2c1c0c11004070740000d60450310f64034200c02e0662000e034080480291201024948090a441440c0c40400c29080b18480c00e00401d5000f20300c00c10151505050148800e515002c00d0b0400a5681c005540d04868000402820040c0e01c1c12510350b07001e03590094400345116100900c503500014200e840302400049041d000940500007d440d0000b910031018210407481c420300c80b103000030800204001c00c54011603c29413013104140a1075440a1000108503203e000340000070b400000104003142c0100ba0891441c0c40624050303007403400c100740201c60401c1d851000c44e000e5004007507490442662000c3c078070242450301d0300c0b14544105800020380d4400e413881b0103400c1641c1c58156200b014001d520800001c100c0805403003040e81d80318002291500b100009603141d510f5500094047d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 438210746 1250 438209496 438209533
    0xf06010504050315060301060314060f13150515040c020c030705012a0609120809010e03090312031003060507080717040308010e060f0406171c05040509071407080c 72
    0x707442e4003074024242c40d840c00c0450200103c018010750340555a0300804804610419410706007080c22000402f00c034100300c010003400010003000d5204818100c004500054280d810140c1000303048030b80803410340c0f501980303100c8540b0b0f00101182d01c1450071000c0f4030081d4000ca0030315042ca90440c00d450f581c0350303900d00644214122003469484a000f41c04070090300c802c1c01c41080100c50007a03130000340c00151036513a10450607484024001043c100010019030f50341c02d028181110b20800c020318100b02100006c20b66420324100105a0724001100280c01441c40c80030480c01140c1160007400301d17080406010b40200e5080e5840b6002032035802d1004581104416070901595060752060b5a40c1c0c07a041001c8050340000e810036610a030352189003c681c0d696402100058400038981e000c90000542409180001c036120760180b00c0341c801d0441d4204d9401405450466900340c81112555844400803904080c0004601c20f03201c00c0810a1f07800e000d8140090401c0c80342d81e0b001c07641000108004041e2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 438211996 1250 438210746 438210749
    0xf0e030903060f0a0b030703060614040605030712080c0a0605040212060403090909031b030201020418110906090310060303021c030510140d0203340e040818090f0f06010504 76
    0xc15500842c0442c0000c0114000a03501901610000954504000029040002030307032094490303035100c1c001441150b9408412050321881103d0030000039240ca008641c0f50241031003000d0b920758410300c00c5401c2c04051070440b403642c8003000030b0b070380100114600b6000811042d50280d01400c4003091000007801c0c00140c41c1e008941688400c0002c0b89040303001d502030302c01014100c00b0820982e03103140800d0414100b03420164400e800150f01d40b400d000243c400b560900f0440001903090030b81c6507180e00380201c1111707660301d02516001d90f80c40103100840d01e40000c60081000703052912000106056011407803121000300480403010f61100003504600f42c07642a02d41c05a56900803908003c84004088508101240509032814100103074000a0811111781c0d58000c4060841c0f5043d24003901548ca101d58480c66400b05140306030500d80120054400240001e003007000c0000c022007044407010303c00b05000b000402c88145d9192402e0f2a0099102c2a200401e400b4a041d011641640c002e205840 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 438213246 1250 438211996 438211999
    0x91208040846060905060601080a0902130b01030204031a010911040509180f010227100903030809070e160806090112150222081b09010b1b0f010f0e0309 67
    0x282c851184004501c181c400150394a42078900d01034480000480900450030f91030301803009400701d1320b41a00050030290340100080a1189001444001a62100012140e01c0f11241c000121102c0000042c0c000344159013001d0400680000c2c0709110014400b0384906a6001c6003050200312100f00c5010703035078000d07070203034551200c0750300c00103000c0b280f42d40000010444094101c07030b84a450810042c1c00c82c0d00c003a080e00c48003442017544408c80303440000c890059580503901d6110700588440020030303c40701e03404000c0c10003d8001c0840c1e201e010801901019252080000c921410212100b141060003444080b012a01e0800012034500d40414401d048420480318004151169034a400c9007440d0b6400c50004180e00707219a031102454542001804140e11104160b07003030030220710502d030402c1c003242910690144d003800c22903900c0d03110300241110b944d08583c0741c0340c6511042c0c4000110b50892341200700c1c49501260200104150010002005180010003200048403045a02d0b48154035215 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 438214496 1250 438213246 438213313
    0x3050c0d0807020f030a0b01091401150503061c06020f040302090604150501030b010309060509060f0c090f1c0501090c0f060c082a0a08031e070903020f010912080408 73
    0x40141c2458070314100320305401000c1d240146d41c0d659460f04103450a8010f003104a40d1400c00500d41000c4040907800f40803105150007142d0300d00580100f151000034030007409442404002008504c10106121000d81d09c06002c1d501e440002d00c0510650f0000d2105030300c11842200820b840f4241441004c481c918451024600141010015405400090140d90405650b0b8100c0401708000d48181c030700840c00c02c805003202d0701f00140d00d90b01076030019011000407030080101304025601c598804440712029644c42080b071900380c1d007007041c1300c1c21990080c145508040642040102c03100f4160300f524040013000001035140da504882040904c2802000490200460300400d400c0b40d894001200b640d00310305403498826004503040c00d51084080702c81c08408000d0200c142ea1000448030b540361201e01810303051804031002080c02c1e54910020b4011420b41c0800c10f100d0b44038036041c1000e44500c01c203e008100340c6103450803c1c0d600030f100b2411540540405c2000b200e400d180780729602c00710300804 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 438215746 1250 438214496 438214507
    0xb01020615011106090a14060f150604090c110d03020403021c2105270f011101112a01060b120c16051e03030118020310091503050c0d08 60
    0x44015200c448807150600c031001044900041d400c0191070f105805201c090000340c3c10514001d91000500c010300e4920303402290809c10b08046c49408640d00141150480039183d000d000440c080384181e80042c0c0d201da04010010400c0c0745c0242410555180300000c40703000740702c0c00074102c040340030740d000083d807010104080e0643c00800b03040c560340c228020002410000341c600c41c04401c3d10803035030f020340c081100070610f842c1c001071110b180c88001041442c598ada6900c8a80012a40300c028034950741401040501c0340b843c0082580030295a20710380b41300a0b0303100d1080d07a410011528600405c044101e40540100410b14103001d000100c03030030b1041050030700c0c15445141302c140314010100d103014001886000c810f21802c0003a40c0942d4000d0000e446602c25002050020b60480907d85045520801c0104105c0104185070080d100401c400146c603501c4903111400040c0e41a8800c180c110304210910a8400c00e844550048912800886161124801c01d200ca07030a9801c60151803d9014001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 438216996 1250 438215746 438215761
    0x60601021f05040804081c0e0d0209010905100302090709030b160206070516060f060e0a09030f0f09080d0f1106130246060305220f0c03080a120b010206 67
    0xc0b481c0c00c14840c0490a0500392288061440e0404036140031880141c004036030489241c02c0036000000080584041c02c0c40700310784d00800d05409042c070808038080e5036500020046d511004403400915801403030f0021034100070800901807a03160002351006c0d02c0607030201c1e4070754248605440f0903000d140c025100c103542c0c01c0800e4036150090f404800c0e0b518612412100021140d01c944240782c08581c10000e1003500f850a0b90441c0200100207040c0e080c40c100700d0601007500010310706075080044c50180e000d11043d40b411501202645c1c49003045214003040d21000e00d030030102420045020343c0c0c400c240c66002c40c044a035a032406855081843c9403841c002030140c2422013041c0e040c00130304d00c0701d51200d180c0e132400c4c0302c0168603041c40c18610150188011850910b40340701c1d6001005285420301050030310b0980089a101c0701d001c240d0141040080480811280d1601580c034180c01001d0000c51b160343c3d04260321240c0c41212100b002078803a20700081d220450340320b40080241c060b4000c100c19030b41c03140f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 438218246 1250 438216996 438217001
    0xf060e070806010c0b0c1803031303021306050a1d090a03141b03071a01080c01140a0908030a08150a0e040303050a110a170c03041a040609060914060601021f 69
    0x2d120354108014002e400022580750030503540100481d1b00f206580c1d1a0480d00a410308141204951003600200302c205002c104070104030041c0c07034044407070305484000c0c405240010040c69200700d4004040c000000f0301901d4070804004800c081041400241c0c0d50114181c4c0c0b10980050002c1c00f1a0542003100850403000000c3c00c0d40d11000a0075444140440c03c0681c40d5400c081d800f210314040c600400c0c2e0381180d90040c040d006141e40001000075070a2540080c01030010881c2820392103801084400500c0d125a10043c01851083c01392595804002c038001d015000854846140c000402c0407032019091400740c40d4119212854000b800b41c03210f960481c06050302900c4088000e40f9075a10b0340380442c020000300710003550f07501c45c5502d0007044500b1603a04c040080000f10420000e00c03c00c03000c0b48004805803100c4035400100c0310344d690380b49014001005c184030064410352400c2c55903000c0200b0fa602c1508007500c80e50407a040c640d900001241d6400b042111048824103504003100c0000342078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 438219496 1250 438218246 438218251
    0xb030705090103081606050103050307051509031b0304050607231203040201030c170a090312060b04050108040309180b04142211060a05040611010b1f031e0b0102010f060e0708 77
    0x200740d941720740c036260729500306984013031b0402d58681c0c00000741e0004100c010000d00a00601e440c91200c0540b0b0501a12600c80c041c080401103e41c4020201d00304002003802210060302d0001c20080d21103946080c20703001480c9200e40303810b940c01c0a030040075841d40009400d5050b00c8843c50004d1031655a580110301520b030307080101050100710b0703854a5440d6560000c5520450030700400007000c15140c03d00418695508000c0300140b80351500c1030003100c4003030b41221b080d01c4003070801050700c0d01d913480c04541c00327200390303028442a80c441170b80c0002c0800103801012500c00c04035028032035180e1003c05400c29201c151036001981441d614a4140b202d1614600008540200c01017078405040d940401c1c0d00354400c8a0101c0000c6002505011054203d020030b1800326040000b00b05401d4024085085480e03140d0014031071507140251203007a14420f4014514031080c241c0300400f903902d885603d40141c0b45545409007d5400c005400b04241240e109040031944200d010503400e49600b0070070303103000002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 438220746 1250 438219496 438219517
    0x1030f0f02190929060d020a11030304060903260610050f0c060402030708030c1518150105010909090203030d0b010c02120703030906090308120c0c010c050702040b03070509010308 79
    0x2d40701a556061191141d080c0200340420300414030b01c1800d054600c1ea205060780500c0001d11406140000b51946019240940214000144c4c3c521742d0304020f580c1c596000f4602541ea102c00001c00080000540050399203511a0720340b807020407814120b684e03403450000b4070b1540811074240080c042e842c02c00c4017000c030080b450802d989094441102558079038414602c018540e80a541488110304040002c1001807103550080c42c00c048024a4043d19494406802d2241c40c040c8400f042c6c44414042c00d43c8070055804040301c0204101140c003003800790782445024040f48031302d140054011740500910040e254000c0c0658030f41700200d84040700a143d90401d481c1040154440b00006807070300d10242a84001820091100e10b24614005000d03503142d400500401c8640072003000002d4900f002d40700c405281d4203014000356650b25044d00580594800d50110358206075200312096040070090401e14000d80d070a02c2041c042c0c1c0203040c0d9910140c8501a0880003100c010008980ca031700142031101c05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 438221996 1250 438220746 438220759
    0x1404020c06040c1a034605090d09060f030e0c0924010516080f0405090907080d0f0e040c14030703062d0612140c25020109050d0201021006090203091501030f0f02 71
    0x2e0f081ca181c1c50b01308014150300083c035030f6034060002e010b00030012540da4189c50314010240a041902c001c0070641100074000916032200001e820451041c40350740740742d10300640307089190303e00500c0914040314491118000240291400a2554411400c58013204062000504004080e54841503070b54002c000f074803100071041c400407030b80b81d030780b00c20490280e0a0500141001801c0904440c00e01c84c803032811405000d5111003a0f40410303040a090210550b0443e0000f0b10468262000d0b5a16102140024448840001000250f5401d80d1242c0b040c2d400c8900501c94050300070040361100650341d2490300f0200e00c912800c100041c880c1200c00814080d0381c0020613591100b00e0300043c608426203100c00010004a80003002540d0141c3c901043e84608281110004213a00060615002402201c1c0207a041501c00d1043d03900805c044004001010700c204980761395044a18000d410680306000d103406030701803205500700c0800301075050b250424481400c1d88500e540c4c156a181250f60100d03000170 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 438223246 1250 438221996 438222091
    0x5130b09090703020306011d0a2307030c09050a0f0e09070f0305010504031b150c020f0303010e04050d0206090c010513051201050a060b0a08011404020c06040c1a03 72
    0x444840200d801000240020030030107081d44101420b000058200c03c01040c80c500340c03182a0740d00550b4040c2c005a600400083e1040000d003400c2c140c1d844081c58201c4041c000c410300010541c581d0241e030f5450003aa40d1800c000d500c1c5c03010014040c24922030704a485045600a205000e050094107801141d00d400320381010307039104070780c001080e00382c2d0007901c0c0c0740d64a200300002d054000e203c41d01f81c5030603400f45918000060303460340415081d03a40000041079494010715501c41c0200701d0440400440c4003180d0702d0b0341c3e4644021400b290304507021141401003c040000d05400081c50130701500070380000e402200301043c011207280d0021040409202e040038400101500c81100b1420b0148031080041050b2502d10603039000d8640c0341d44003090402007048130b41c421682c41141e02e81035802019038280e14214080008029000d41c50240d001c90007800148402c11030072000c950101d4409000e40080c801020040c05000e000032034480540d2854081d03030300880d40c2d0140388001800382c565000b03020078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 438224496 1250 438223246 438223249
    0x60c0c0b0106092102102109060506030f010b031c0e0405090d020706020718050408040e0117061303080c09030a0b0a0b040609050105101b080f0304030e010804020a05130b 75
    0x8502030b0302080208407940403e01c8866804402c00060386090b105501c0e20031415408685a6000e0000300f404101c8001038290956a110f40038090b202c1806905103c80390440c201800240f0007511124400c2c494507982940040c010300801841e450003c010300380c210321003d11002c010352081001820401c2c07441c81a405540c1d1744c45002c3c0240d60b110300401e0761580501d00a444c103441500244159031082d40c041100c01c0761400c0c101001c50b9a10340214440c0c07100d240c00b9040d40102e402008030900b40c0c86c004101d091030080d9046086108900315042d545441c00a00310440303092401a0008001c2030000312084100c1c0000d22a2140140482d0640461078407032680c59074080c0e410b00c51441d120740c0080458901030003004064600c100c0d0400142d4500400151415030b2000494188130402801c0342991401c0002c0314401c0741c0141002ea80c0c1e00f82840401c1c3c0c00d134001c81d41140800e2424201700744552080c030240d40b240d94090444074109081808000d1075164000c003605085441d01c0803444107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 438225746 1250 438224496 438224513
    0xf04020d050f150f06031204061409030d0c1505090615011b03020c0102160806060405040c0b07030e041a030c04051f08071d10140103060509040c0f050a12060c0c 71
    0xe40031250b101143c0c6080014004d01d050f00040c010903c60b600178103c00c0c403ca0064030498049500a007000780280d40840d420b0002030151600259241c064588010341054100840c0b00d4514840c448845403250422054070480394160b038400c1040d40040b002034131405141c0c80c2038140b02014113010300c8050701101078044007a0480c1048006070000d000d0150b295070104a22042800c01d091441b120600300300d5082d685030780c02442140304548910116051020741907410029156445000d980d03941c4509000c1c01e07650710101030600481c6081d0307403038502590031800b111080d0300050150250601c20300412010300300143c0300c20b050400203e00c3d070b410300340d14002140080280714040c0594501c0d003075600c0c0307409a060300140c20a0940c9010002981c415688a1003a24513400e1040480e080403401200100a5604101c2d0400b1680092006008070100203000325020341c4444044251120140b180380d050500c40d0840c145109e0b220540082d055400002c845000d61500184002e0a911a00316 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 438226996 1250 438225746 438225763
    0x1c151b1d0103020d021c0b010c02030c101b060e06070c0b0f150a0f030b070e0117130b07020a020307090c050a050d0e0d081015090603051f0f0e0f0f04020d050f 70
    0x1000240305102d401b01c0e01c0741c3c1c051590000c0c2c0900700004180e00540210361201c0440210b81c0c8600d0741c91610441e2a402100501c1c541d0440841402d10781800703188c524000c09a12079441614404c2100240c4118456800e05000e55880f000080c810b4465455100524030041c16180106518000d113107100e44460200b0b03402032203000c000d0282c40c0e10f1030400c0c92080c0800390180080289203c2070784280d07600051546000a01003440305296524190030421a0303a01d84401031a2040c10014495599400075400c840180203d040d10b481c144c1d0b456501c2c084400c862140c0020070002c0c4103034140c40d4040e4000c0d000d8101c00e043c010403000d005010071800c00b03003036407480f10104d0314080c123004c0c0c000c000e980e2500c040e11843c01105a41c805580d070262010301c40e80b05880815072614000340080d9070014801c002c008141c51844041c07a15404114802040d0f4000c074007000c20100000f44030001600002c5016104541c4d009405455035000d1108510003c4800e65540c4240030700074030403c07001c02c4502d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 438228246 1250 438226996 438227017
    0xb030f0a110909030301050112020f13061e09050112150b22140402030402040b030607020319140307180f030308180307021503061c151b1d0103020d02 66
    0x4058032851400a1031401141c542501801480007006610880001103a040d80c07400d0a009101e4440ba0149201901c1480307031010075482c0c040340700000c0b10340321a0b414040c1d074040d85a11b078901d0040d02e01c00703a00400000154000030f41c036070f008002e035500810381c00c00311400343e08011030120040c00c00c1c120a004241d01c0743c0310111001460102e810060501c0c5001440904910428207240040070740d00c0c480e02a1519103d958004081011903507568001d14404c1c00140548046103015100030f0340700e0300300031508908548000907a0200c0b034407403c1481c000c0c0620190366429911000700485080c51000c0c40700d100d2502d000c2e4003040500c00060450003c52181e91103040b03038035100c50100000300302c9960b690110b83c01405440016034070424424000807401e1401503d0382d441c440003032028044141c0716880c0c40b4000c045a030500c0310124000392440c40d800341c1880318820b180d1407103a64115a43e062000645941418040c04000503500d02880c28149405801c052803000007408a90103101c021 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 438229496 1250 438228246 438228253
    0x1303060b06211b0a0f1b0b040b01030303180b010e0a0941060a110d0608030306030c100f050c01060e011203082a1c020f040e0108060103020d030f030b030f 68
    0x80701550020f400008500110240d0381000f10500010300a10b0340c0c42030800c148086203d070100b140c209415858512608103444030600c0c01c4c00e09105d5003007042804150006400c00700c05405881d51100f00400d12540240140043d03840c10343c08644510029018407203841c2c40c0c42042012800705006200c21400d8030032070880c103996880700c00b20700310400042640000f0404450440c25403000c18070946c05008010080380303801481c045010f80348994001400843d1500101103648840040135501c640c03400e074210307444030000b01c00308009864000c1c00c00000031280741014261600c00c0019290941c4608004034406855240321503030030000b60020440c0340c2c0c2c104141002d050340144402c0c1c0196a45130107003e0102011441c54501504d402c01c1a020310340011131042c2034280d030b03540100c035003408038085450b80e0004408035290380c0b0a106a164140d00c2000214000c0c40100e00745041303d81c01000c0c1e41d820251031350144e5060304581c02c201e0a16076a074840300d00c0c548050004199880a41015 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 438230746 1250 438229496 438229501
    0xa020a1d01091103011e030209010603060f12050c0d0305040905180d2f101a090703020901020307030e010e090403030507020f010e07051507081603141303060b0621 72
    0x14420400c0c05a0101404604208407001c4034160340044a0646d2080202d0309401c02d0606001d01242003994002908070710100f0002610543c144e1080e015075418409800d00207655000d00c0140c03814031107000d842d5412140d02c85e20a40f614517403101c0c125120b0300b4005d003025034a603003d200726081200c0c0710784104031480c2c903c100c82c0301c240020322403202c0c1402c0c01441c03140704104100341810700e03161201c210100c100301c6e50f0000c02c042028020200e10b070102400020044841c0280e424072050905001303562200103d08164000d000391044100e0680c0150b080403040d84088403e50210304a05040c002d4040b09140315488244030309126074081c3c6c03004103ca01b0318100003031034004400c2903c001c0d6403400b9140001410301107450011601c00b1525415820443c0c14a100c241c4504907000304111000584200d04944c0c00d02e01c80d200e03078003d80303428810000b90040846503100c3c0441004641101003c2440081c203d07034000b80e0000b20140800f810461124170a1088a48103a03003088950f03480c108 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 438231996 1250 438230746 438230789
    0xf030f0206070903020f0316080a02030c120607050304020d050109060507080108071a03041109091c03091a0406060b070c1403030a0f080a091e020406050a14120a020a 73
    0x12202985200400361032402ea18001c0c00c080031800003d10400c01e072018554a80d07010030003040303203c400107a49500c182e80c03491850f90ba01140101240203002e0b203c02104a49044000e0840b03480c0f10001070032103540c801130200c0e602c0d440100120707448500c450b0480c010a00c24455500443e2044900003254241000e0103040010160722041c9a54000002400080141d0844c40c00c02c002030041203480b07403110300d1b040e1030240c81c40100c03541000c10785040104014000488648000d84079007181010954610101c1c25039510480250030440e05082c040c24154207103601a901030f00442c0001401a111481900f095124000680f40e294040c0d8091140c21103200701c5000340c44040b4000c516020204c0e0700500031540c20080413040c00542070026002c007865410000c06a0750004000754489031000051540f82d810200a9015030b01e0500c0218031810981d400c0000c1e120401560448400000d04000c0382202044074607042e401115140c0b80181c0303529212001614000b1041c0003090310f00c02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 438233246 1250 438231996 438232007
    0x203010f181b0501050403030c0206120412090b090915030a06020f09030c0901060e1c05070f090e0604030210180f0f0b0c180f061b0d14070503030a0b120105040f03 72
    0x41c02d40c05007402810000350b078000b01103c044a92500b048030f2219924000102e45c0d009126410880c0d4419504103c04c00c104001d043ca100c0415440340340649445020040c0c1074011300c0c0c1c03201c0d0170018180114034030042c0b0711034400310364030014120b4403010405da032094107070307000040d100d040c8801c08983c100700c81c5428489040b041c00b054a4148003076240c8100240f6900412202034041e01401c880f90f0303182c14141d080404480d800600b1280b00b02d607541a00c1070303881901c3c420000003d160009045506030301052260060b9015030052031800f80b0b1004600007010a548044518222441184001000041076000c014054031200c110240070782444480c45d440106140d150290400000e20920000c1074000c5005100b03440d0083d500920601003465840f0782c141001541a0003442d08011010001d02c01e4038040302039441d000c80c02d4440e40800128090b100005060760400d00c006403118101d5071008003610340041c58010003224500c1043c1c00c4171400d840c203540071100403500c0300c03d041c1c011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 438234496 1250 438233246 438233273
    0x105030f06061503041a040b060a0e1b0c101509110a1e0e040905060103020102011107081b0106120303150501140d0507020102091207030c0b030f130203010f18 70
    0xe40c080d1041d441c140d0300140510114181c84400380c1004408a818404182d4005031403020140e520400c508003401d0a9140407022203600d4030800c4180300120341c1c8880c804e02d0728080d0f124481c0320b43d40190f501c03c5000083c2c0258680405600c20200400203506d990300411100d4151a00340c1c030045410040c4600c259103041e000f032000100c04024503040343d48e009800c4180b02000b031100f584202143c00003100d0b508451412940d02074107281401062000118a06048902c02d0b00200600c5183c0301000c441c500030041d010709625070a22030912450420005041c081900100001d8140e450709940398011161b01c800383c00203580d52640281c0d160007110000040d260900b09509982950304840b10607200395145022411346650109080b030f070003501070300c00d6114001c028000755000c20b64541e60f02d41942c48296400340f940c28000400b05a0101100e010389030600c1c52103207582ea41c1d0001558036201e04000c980541d655109440280c03218403840c20f100c0324900d010550202c2a081c20404c41c40034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 438235746 1250 438234496 438234523
    0x40e010608060a1509090809030d0311071514091606080c0706180b0c0a120e030301031e02040203040b0708150604120f1505070f0201090c06050d1b0503010503 70
    0x60000a014001d00000c40c0da03481800d4103004a04c480c014505050042c40642c403812505082911071410001d4400c040c140e407a80560444100209041049040c4d03031303100500c03007000f580800540300840c00048126400300c0340a0030108640c02c440c2d001458041c0b046901041c42d822945a040356000c529081c40024142c0e880c1c42102c60511250030b040303d100d6400010080d598401580e500e00303090401c600074542e000130f030300c4200e840c241034002400ea0080072030782c00041d6a040d0180700b00040c0c0c419095200c440200031402d507804d44c4e48900c000703c042e008410741c01c0003000d50140181c0c1d072400214811440380410300c4441c04d108002401c00c0c440500204004400124001e405881d400d09480c2124590311b40103040c20b001f414a031100840c45034011349000082c0039500f1885003541c110501500d00e56803008028100e540d400c03401c0700e041c00310091086440e50310070031507144140040e241c0e041c00c2d0030300040c3c20074504c1d01800c2007140002621000c036002200400585c5428484090300462 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 438236996 1250 438235746 438235751
    0x10608041a06031207050c131d0a0c030f03050409050c090a0b07030c061a040216030806181302011e03050f01050321071a0411041104060e040b031911040e01 69
    0x2888030000c4d450b5984064000032004010a0741000e01600b00007aa584540141c1400643c14448904070054a02051484220105518041c0b001035000650505054102005a008a0442da120221103d40e14015000c01200744000b0806075072510500c1e0161111400d0960340b140e45030203104182c4116404000c140005004200109401c210a25415036001d4000102640561410b08241c0b202e110201d800610200301052205018190441d0311402600c5d03191399507559404100c14407030401000a01d1080f41c0b0b0104110352402a0301811700e0b0701c1410041580e038042440140703140c2c413483c3c040c00040e1310395040c04201c0c00d6501e00140900300940107062100b00c1564000901e0400c10040f44090b42c0c0000c0302d00900502c2c01c2480c43c006602d03648a0414105030070043d01c0711140954140c86540313454124036200c009502203400302c0d03205468003c940b00d80b600800004040002030340d03426028607d88580d600b000c03103280038900fa102d80b2803a0000c50b0040c05200450f4118601c680c5640e2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 438238246 1250 438236996 438237001
    0x501080c09091c110d0908100c0f1416120822020126070f09050a0f0e0403030e01020a02011d01150314010609050c07060f05070801060c05010204030b010608041a 71
    0x320042044403c2d10690585410b0382c2c500c05404840c400000d14400c01240620404001111361003544201200c04c05000c8030000c44104a642c030031280c8010a090101e130228510241182c0a40164111415085585800d00c2c0d5155200804115105000c841c4a61600c89501300160010040c6400016210a000440850640d511124002c942010303040c0555942030091040c80c0003031108091411110422582c2854103020f000748610306000008076415060102c0d850600302100012250f16070080e20049141c241001441800600194101a210f500c00007e162003400204407a1200e54000107402580c4603c414006200350030961990341480c0b0300100708818000f10405980e00710401146c5500b03402d8134a80103107116405885d5103401d200401120501c1c40000d490154028032090000880e4003031213804648044544001042c0001d0048c00141c0c8500b9214001c2131042000510b8a500ca8a4461800c40700f41d2011002401c2c1c001007004100303000f58122080724981c00c3c91070460 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 438239496 1250 438238246 438238261
    0x111120301050f040906021201030b09031c02091f0207080712020306060108311703040308010e100302120c0120030403241d2a04022b0501080c09 64
    0xd00c418407620340b049000d20382da03011981e680ea02480840c0d9120104541d0f03100c1c040c0d50589030b00f001344415200c451052000409244000c812194030901d070540302c40401401c110b4541c02504a07450035500000c0c0e00c154524141040281c00501c0c40c400c0d001041c04514041d81e0516003011500710070381c502804802d000c01a1000100345400000900b0011204d0340c601ea0030410122054120f000c0400913142c0b09860040c0c03110800c01c074640100e0a042070ba4400c0c2d03049200c0c070310058074010001150742c001000790068040c80c1c1e6400102111a42c2c5c1d0160b40c980000303410140c1d854030044030f60482da030060055078000c1500c5006081d64210302410b0350a00075803d4480c0114032002c1d0901501010044000340340c004280c0310320b4100d03a420001c002c00308090210100c181c5603614000d105004000e0b08203c011000e10f000b01d4080c0c04410b8600341d101c800e1101a40041d0140c101000c0c10070105a2800f0210461048044005900242562600030342505c0d020301d182010b0301525030a4107000c600c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 438240746 1250 438239496 438239533
    0xe030a11100e07170a02061201050405160206040b09070801060e09012a05070204200a080705091014120708091203060108060d022d0301230615041a090111 68
    0xb00d03404001501001100342d0340040c05d20002e018029401880007c1d00700401c1c0039030080c0360594030300756810000c1d80c0eaa003089202c000421241580984e1119000034002040307801e002c1c0c5c7c020915000e4403200f50381d403500c0a0035164076401041e60061240d040084070b407000d101d540c02c00c410040c0403a0350b2a55003000e0b4141c62030400e80040410000050354015074807030390810383c4c226412482070000c90481d0740107804140c00040041c40024010b03c0850151840303042900d0070b129000f4150340380001d0124003655080848403c200940c1d0b030034007071700c090840741b00c4207a44a1600713529060020b180200900341055514202104a01018414011243d0744000c1d01a40114241c511000780704103400000d001c003036010317980c400c0e140c03044c150041c526441402803034002009070001c1c000d07084085111049a10343c02810b0418100e01c000240b01840d20a20241034480e04040b01880c0940794803044100003a9510404036020000a0040180d680481c009800715244030203000f0031103902d100d0604 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 438241996 1250 438240746 438240749
    0xb0907140a03020708070c031a190e0c03030c07060215041a0705120901061e05030c0d021f051c05070c1103030d1d01180b06060a030e030a11100e07 65
    0x410040201e140800d40340258100c0f10444e80001480340c41d409140b5003030711103094902044441001904138080c0009280e80203d006a01381615505100340162812006000171145400346105490707043c031580d14180010010b120600c0068884036080c014042c0c58030240090345081d0300c200368208400300d0300c08403287d40101c02e07140307403441c90740c490307035001c85043c0242070b40b29000500c880140710100307a05512580c1110102c0410719020401c0e80f2403500e03401d0035885055056001100801c070507241c0310a03107001c490b10041000542001e14442c060754442042c01160115000080d00c072500070108250358070304040e0303040134030042c500100d00801d060080c17071000b040d199880360702c81c00c665018002e5400b419580b4104020304090040600d0301660900c080c590194070301400e9a003015620300c10001700c0360b001001511591100803d01010398401540402015660b414000342207d0501c0100b241d69203d542d07040d03100c810f01c428641401d000711100e00c034251421352100d0b400c0102060176030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 438243246 1250 438241996 438242027
    0x6110a0302060103021e03010f061e03020d0f1b060309021903050c091b0d1b0201050c0301031410020c030304020a050438060c0d02070602060f0105090402030726010b0907 75
    0x14103244400f0070701c46d466807040c5c085030342c9035007000c0c0c0c007009005455001d54211030310070342066001600008108080b42070b501000e90402c000c0741c2d041d008078450b0b122004203503210354140c0c01468112000c22041c0c00f402c1e0000710009441e409808154680324483c096070341c054110340c4158034a141c6d105c55907843c4c40800700740146c031003000280c0701c0c94418140c01c2090703401000c4956103a41a40d0200700612041b0000d16108403a022800c401c9403051050718880c42c3c048003030342e15590a54076041914200d00306c42040368464410300401c1000306001500550740070b0f4004548a040c50702c100002010141c0005000d1031901000108000b244150a481c00181142c4208501d90780c84184041006049100707421071000901c079008110001070307a1030446400c1d400c0c0c6910390f0316020201e8680e00160303400790b14821008010f200350b10f000b603090781d00184010121003086030784041c02c4a9409003501c82c1080310000307200000b641e600030300a8030800001250341e160350b49811907001c0c051080315807000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 438244496 1250 438243246 438243259
    0x4060309030c0212010629030711160303030c030b0909060c0f04090606270b0a031a0306010e01080f0309090a0e0a2f040203100b0307210606110a030206010302 70
    0xe05020344201c2c035102c0d8014150303034121a07800903118040d010511400f003160303c08042c0a25040030041810410340e001c400c829141d501d40280444803041c520f08000da0a00500955075400c2e104c0c1901140114403030384020810503000300c80130b400c46d6400c01000b4090880b0303a080207280380c00071482e00d0307100c60800d00682c0c443c075a032100d00d001c9020300d80044801d24903100000c142160410159820107038440d03076030700120100c41c104d0040c00c103c0d44107601180c40b0602c2a85000c60003a0000140c440c4203a85d1490031a403075a00092801c00c007a8411540c1916800040c8188641442820416a98035006514103049400810031035980104080102c0396900d010324407210050100800e416045810b460401c01e0042ca41920354108400142103001452003244050629009881c4941203103010003041e80c0c50140c0e081c40690000b0144800c1120203440d8100c019800601c50500b0401d44400091035070034141c016000740c07403105220b000e0343e01a240260003c2d50002d03000741541c2d8140e038030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 438245746 1250 438244496 438244511
    0x1020a0903151805010203040506130b0408092205040201020d0203040501090e091c05090405010f15030c03111c050703090b04060e070302060d05370b0d05030714010c080c040603 78
    0x807004207140c020b0000900c0790f094446083c0301054001d18000c1d40603c0030345109840d21441c125402c1d030402d00c002d140c54000300004000c65068006808481d06c040d001d150080c0d0300c0c030750b441040f4448080507840d0541c1e4405100c15544d040200340703401c10701e900065203010b050100107402580c0521943c01e0303901400e4000b49002409204540d4002c0760142082900f462000000e0030030b400a00111b4096032402c400000c6000341d002c407031f80841c2c004891166410458500c110003516040c440d0205240d250000710316010300e0741001f810384030011000b480030102c408180350141c800c0a80202c040508040d411408106407a1724990400d5104600103035108514021900300016680701a51001d0007041d00120010035030000b52190040107114003441d075502115161505184c40c0781c0007414920400c15405103295480811040001071064082140c00c0d92020b2459018280898034049a5903ca81e1400c00034000d80c0b04040b581d08044d001c6161a010401c52409184111400c1640711040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 438246996 1250 438245746 438245783
    0x301120312022712031201031a04150914060c0901110c030d05071b0b2203030206070e0a0308030916060f02031804020d1d0c010507050c01080903040b0a080609070201020a0903 77
    0x11a010034139080400e076600c480c20341000e02c03540c0d1300c00d10041c1e4401100200d1035403401152500070740b280c0e600110b00059001820303021401001000011200c0d4030902c0b0790591100c004010283c4218000003030155140100f400051403107070b00041c86040c9600c040308a6070f0070baa003c6001c084288203868815150584c5060240d151000701c00d1010905400d08004030320302444500034100d15008803004034144481c4040018508030714030001c0d0040c2c220b003012502c101d01c10341020b030345200000c0000c0d001985070b84581025500c00c0c1c40e101c211307500c550b44c1503406086d42c00c1c02e0001000030342480c4411154010019450f4800e08401d00b848084060203400c203603031254151100d09015040422001c2d101203003003081c10390381140030301c1c1c42d2182039500c22a5602c40d504507001c40b6804005030581d0080da40040d1800c09018000c0078507400240700110390b00303174504003900b0b10030300b1075440313031941e0409000b031040a0304003410030021a401000302190f00c0f034108420100b100d074046054511000b0007076 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 438248246 1250 438246996 438247009
    0x160c081b3715090303091211040b1306090b01082a030406060b031e090d120207030320090103140c120c0c190b060105040807230603011203120227 64
    0x800040c00310b85441d801e070345850303486000181940d01c60f80f41d0b0f00c5015200c500d211645039141c0002070007101101c0d003500c0681403c6e04202c5038880050303c140401c45d0144010303030645141d0741107400b1107170b81d50f20120025030348041c800350084035190f090071400d103d032205000c00716550ba001407469040080440c1c100322865009600400f910381c9015200d003405907c0c00705c0300842103910a00405004042281ca502c0460b0941500749143c556030f00f524045032803100a900a00c0080d014140e503201c0900b400c0e54000309444000b00c9802000741c0d2610680000340881e10105e481080501c0094104803e8401040c206c1e0003040e4007603c020003550710b001c1c017084607210321403001c03410307025085c02200540003408104c03441c54810101c80c1d00e96074914004551a00441c480c2c00440d60080740c0800921445500380d0a00c1da004c18083c0c0d4540c00ea240100f4200e90003a8088000c45030804104e50606a20001c40d5403595140242545401c910340080d120860504250324000d034041248174104da134418 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 438249496 1250 438248246 438248249
    0x607020904081e030106050403110d05031b1005060117040c0b0c030406030e010203220302030405041b0f0c11010e0105040306050a1d1c0302160c081b37 67
    0x205140300514081c80c000020b90001070f01034004041c14281415a07020781c9090324107a0390a5900c5a007014959107680328150110a4802c0d00900007104e1b020110340140010001c0f05078844100200c0e00ca000e42262a240c14006c03070039402c40c903140034020300d41c2c1d00104211100c01580054000c6481d50305212050340100da0055105080014100c014203030080090000c070703240c5860412405000031000ca0903888212142d120743c03034081c4402c01c00445010102c2e0941406441124149a00c0c0d1010404886503000700500c1d1f40c031100c51110035039620012a00c0104070614000c2080e203100d5035a06014000c02030f8487c1402005c0100311041e0340b01320103944c02144c00140030300c21400d00003000801001c40000035261980901494204401d00042140401009025140c080d03091214200e000b074101b030b03c1340240480c2d08031066000c00c8a240104000d07140080142c0001d079a5141f099040506040920703000d01200c0d400c0035440204170342c58000503a00ca02034001c0307807007010022440c000510f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 438250746 1250 438249496 438249499
    0x206181608010b0f090118090302030f04091515140c0a06050a0218010c030206010614070f0311010605010908030403060203071701060c0b0609010e190b030f01050a0b09010f03030e060702 82
    0x100340001000541500484002d00301942c2c004100c440e00014484408000d00407810500012148010815070503400345041c540240b065a003040342502d484000e07503005a01140d503058540c0440c42c1c1c0703018100400e100809030400220006510114098074100200c01c82c40c08030040400d18050b041020f100c0208499808242001145004035801d402500032203048c40e410500c41000d90b4841d40036408605007250550010821a807902500310380301d5504401050451809100d10000034548244581900d40b01380c944400d45452048560b017159031640c0554100903488404200c907000110032202038981103400540e9995400c481901e09056441301004a5200000000b80b070329800f8962014240c81441000090380721101008184102802480110f11065022a45075900098981e1000d41e4801021460f4205400080c0c10010391444040d1540d442d40200010700e40c0e24451028014011900e00311194100b61428000d070300d25020003000d0200c2680b07000025174410068034a520360 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 438251996 1250 438250746 438250783
    0xc020a0210030f2a090506190c0f062013050411070c03260306060a200706020d081b071b03120905030105060a0303022d010e010c1701030201020618 65
    0x1134490700d9000840c54011824102d6071030100604252240c9442021a14000c04990800c0c1c01c18034070b2884c41551032051418000035401032000900b103540740b40d03483e4ac003a01c00000c14a01d0f04c03180c0c4401001010301c032003004404000c50385c2c14040d0031716404291138080e6000111040d041d864001c0314841e02e100a42001c009000001c2004038500c040a401c5d5031410006040400103141e124160100362035031603000ca000d00c29409030600c03903200039504408180d09a17114401c0c1c001c00303600b030000c44d400c0400140c0100202446094001c80510b4100d4050070030301001500c4000001041d00529100404083c1c0c0001c404001076118041c0c44091030700000d011010341c203001809800d42065109050180d42072070001821441e01050040c110b80d01a00070b8850311040b00c00d600801c4030b461050005020100300d901880b44024810103114800b400c0001444003003480c80074000708440d07401d0000340d400d200014001030341e022900681007140e5580a010380050456258141160114161160304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 438253246 1250 438251996 438252011
    0xa090512130810090201050f0306030316030e0109120b0117101e05010e090a02090a15030f03140a020d030c091d1503030901140c0c0a080c01120c020a0210030f 70
    0x4030044000485030b0301c40c11079002c011020302d09004e039422008007030301151080c09070a9403503a0210095911401c010190382c60b0990616802e00000c01c4400c060700000e0701c905e40f500095030003080e00c402a211080307910500343d20b2641d4400780d00c40140a84858001010302c40c64243d10308001350100182506401c0c01803080030009020340444465010480c9410440000348660003840b1480c01806034402500c000d90300e640074004007403400b5108146050b80d40c91600d0f4503030b00200d0211701441c81100000001c0400d414028280401c0c0d00d1f41c9503000c1d100f00658000b081e00055030809803100380c03c001c542080e015006540003004d513488aa9900708401240d0100c800c115002841102c2882292103101d840d9018542c3d079010306a2a140483c41a81c2002c48555044025100c85c85a400c111968001c041b00421140200ea60100c00740750b01c8070142c200301c3d680010010310280100e581c01c001266500b1002961886288800782c0100e035402c103a018100d1282d000080703c007020741018803418 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 438254496 1250 438253246 438253267
    0x12040602010c090e01140d03120f020405030c0411041a041208030609090111071709030d0c060e060709030b0402031203010b07031e021e030c1504021807080a090512 72
    0x2420340d00410b60004407920800705010b5441a4200c2c1a2441980081c070091465014031030b03c9014828207809001c0f030702e65158105a068014401203070260783d809615070f0302e003400b45803a1040080c6607034815410030540da0031103403d06007590101e4683d0010020120201404801607200e950008650101d118500a0030301000d403000f0f5000e543e042da1004900e941301e141e480e00b01c400484036000001c0c400c0004c0d101040020009600104480c8406880c08151a001034900841105401d0100d07102c0f800c00070503c21244610441561006e004e0542807070b040d54014082e80040c08000c240341c000e07502080554808004549900c000302c40304694a585400f20002283c0001e002180061680307084240c46200745d8100800700c0c1403640040004488580c051840100d5000700c0c808140300a014019141404000e80300c0340410b80154107880c1e080c90700512035125080385070820441c4102d4140321200c4d61105480d81e0150000700300280c2808185491401d01e511104811400c11020440c911503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 438255746 1250 438254496 438254501
    0x100513050708100503030307030f0e0d0206160c02090112050a1a151512060d121d04141b0705150f0f0912070303020f030a0f0b03010e1209031204060201 67
    0x3500d034030380b194800740da41c07000110080c01550241c203030150010310100301081e00a40081c040b440340c184021510043c403071012407520010124480042c2e1040c02800004400390703040f4080c41e40140b50000010f0703501e4003c05d034920740c188203407100008400b0160003840401e2100c036a549034450764940078400da2111308200500107540891401d0042341c42000e49242c88590007141580c440780c01030030002102500505288001d000d83d0300a4a5180b0080008082c95080c5412440c541c4078040390325492401000b0340369000402c0d6002c0c510b0214548040741c00492003035448088000c1c10b846071a0002118803950084000003000d40c070a04003142441c0d84141b0860340700d110015400e006507620031100d815984030030784420042d90862003180600d20130340300090100e0b034000c0c14058a40b5486807094942580b08494a50103d07a803410080ca02d10540e000d601c40b07404048001f803000701d512075445500ca80c121100182c1e400d20018084420751010311104603040d499059454943c4c2e55a10060301 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 438256996 1250 438255746 438255751
    0xb1c050f010e06010f02070e100803270d03080a09020f04151823040f0b070f02011104050f0609040f05040510180309270204150810030206070b10051305 67
    0x941d48020000583d154031444068400c1041580201280ba1030030342c4074000d01c400500b008119180701c0c40040b9001000300020209007440860ba0860030b03982c100303665039880304104114401e00c031552864011a078403011403078104003110000500b400482c8001800390000c0c2d41480e81080c140642e03030000c9035040c200c007003c840c4c3d68540d00c1c001d107003c40b0f416001c84030240d18809460b0101c01051041204508207240d0140c800d82c9040b08404182c1c45004111604865410004400038031420005a0a0141d446043c079903100b4a400e1070f081c100015440703024011200d000c0c1201040c070320410340d1160030070f0f518040040001c0080e41000c2c05e0403616005a0035403081443d0800061031900340040500400d0a80c0658900201605000c0032001040744c2130100d40444500111702000700806100400c0289a0040001807880721807402410340c0400515442c201203030750741d0400141e1911011906504e90140c900d188035074843c080700e0f08080240d040540c00c5500c00d40409050507907984210f0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 438258246 1250 438256996 438257009
    0x40b0a1b0f0305012103120e0a060b100207030c140102100603060b0111060415111e04080f0303011433070611090112021e0c07030b07050703090b1c050f01 68
    0x1007140e89038445440e02d45d1070380b10303070a194917065442400820b2060340d60000204e440c940c0800d0020010030740b503150100210043d0b03002e5584240c0e4010929000120740050103da0010300500d0f4619180c0c42030111982c4a01071030542002503024550380b00f402204d90940101c082003090640340d05211000389054180f0300d009c100141c541800b80d81e0000350303491245030b00098120500c04e16003030600c09090145030045460100784450000b0180c6a2105001c0110384043e290301c6500d400c650902d030103850f24031090b098004200500c800528454000110030007540d601c500072031030000e002012610503d00b00c0c00e00c000b8145c820154550303200204055400307081c0a00c80d4540e032160303400f0700e0f1040b964054045083c105105800b514030741c0142543e0301405819001c0c24400300300f2001c031584681a264440c3c3c0001d00140100301c0c0c41c0002c80d41000d65460203509010306980c018116220602868080010229526014030401d0140d84002c182c101014443d07400c200544081f00c034000e01510 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 438259496 1250 438258246 438258251
    0x80f0c010806061801030f06080105280606141e0309070303030b041811040f020a020307020901090b031504081303080702010806040216150204031a04030906020a030503040b0a1b0f03 80
    0x180880c504802900c4138100f100c902d41d01c01181a03801036000300203c40704545940e465100002d8062000e00c102c1d88181307810105070081c00765400e030456034a04040f0560f030f06e95240c82d10900c0f01c954041d0f0603441641e0b0100c14680e070780c406a80401014803002064590040000041220107200420200100c9111381c17414440380301080c04010070740d6104001c610300c401044030030700c010a11401e80340714000d80151001441e0542c5440840c20b0303074031803a0304d48090790001500d00c0440c20b001560900400d00054100000c04c885400039071240c8a912480880010741c0d004982400300d44001c40f200c0d0710850854041c041d9507481d0007035550b000b1800903400f01d02201c00180c0f0b1424507000b01c4003000216240001500210b0b0f452102d00c442c41122950019420300c8084005810200401e0308814010032070f00d05885c0520300105080d031680c201c1d20440d08900703100c1d00040c2c0c201d0266504240d102196403045c2d80c54107160070040034003000307a1410383d603111084803840b608580404206115a82c05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 438260746 1250 438259496 438259501
    0x90f141507050403031d0a18020a1d061207110a0b0f1e01181118031b0105030708071106040b180a050a0f1a01080106061d010e010f09080f0c0108 64
    0xd0303442c0d000720711020f800300e001041c1030125480900d000743c4001d14028040410310352504041c4562030740d482c030000a0154002005e0440c1504a50015038006c40000c4840b000744106c00415002c0c025008200621440003000c135100c1400303007030206105401c841c02c8402d00710003801d1404504034103840000710112034a021803150a00000420b070802d024415506050f480c09555000004c0e640040c1e2051aa03200e18001148a81d800144034600480f541ca40050181c00c08040c1041190912070362880350203240c80302180d0300312060701e5100c45076040500b556650b840c0d083c0e0344919880c480d1100e500a1008100c2040b5028100b540610584066850740e48450100240d69803552078018040754003c08803400044d40f03c1103c11250b5100b4000c12603440300c1487c0c10004410203030046c1146e81d4403000207104041c2e000007402c0090034100c1e140000000d00a00117000b0410540b510b5040080020368140c00318025001a40200000e00441d1000503140c850543c580b00c038a038940340014034000c003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 438261996 1250 438260746 438260761
    0x33080d080f06040504020a03170c031306180f120804090c020a0c050d03080a020711030304030321050633070b0a0617030d05070c17070209060121090f1415 68
    0x44e10305ca01d9014141c04600350954950003400b684030160b1081e510130400c011181000300740080c0c5480212055142c00b1f007410510060800721440812060404ac01b103420003842d4009920780003240d1a408442c28043c40714200b14107288100e40180c9403450a10707051851555001450759042409245101000c0b80c4601c1001555001d096024000451090210300142302541c000c049192092008410040702200440e04540042e481a80800c1e01c0c0e10a0782d00009114000b45501c0ca8818000c01440c0703069000900c440780c5940c411000c0c0a0110703582c409502c1441c5105000399040c140e202d40360f07a01031400e0704103030380b085031403401c4141800c000040601c42c40004074407015441c00510304180b91500d10100078107000740230000b0000241c1c2d840c004a60b00341c000c0c0ca1190078005619580d41c0103801400341c01d040240100d0f040000920064142c07040e0903000c4800b00c0c2d0301000c080794029060800c00101e95074940c01504e00c40d950b07507100c18a060000f0301103120350007000c0b0380c070740d00e40e90b204 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 438263246 1250 438261996 438262001
    0xf0717090102070b0d060e0106050409050c12180c03032a0a0b040f0c0f06080f0907081b041116050601091103070318060519060933080d080f0604 64
    0xe4420740564001ca03010f02006403002c01504041c01130440028800c2c1e5500a46074070083d003a8424000b00e0000a030501100c0c0b4240a0281d02943c110280d520b4002400c0c0c401f0b1030a00000c04044c00c1c201045445500c0031420f21440007030b540b0040480707880da207040004150321115010548503000d20840280028440803d0b5170711040d8001256081c20758454540c000e1041c0550307811506505805404074038868051005000391005544024640c504800c20382c03113864000c0c041c2c44881d446030604121004000036040084176803e4010f050703d0180001203000380c00c1040260282402c0410741c5862000200340301901c107802101100c0a40c1d80e038402100c111512081001122982000003508041c0240c00c811007411031030b9109010080c3e070380c848000b11002519404030050f400d070704c401c1200c4420702804000d8021880c01300144414008040d0344015a241a4881d8800000d00c0c06004956611800c000f010b00206440b100c0c1c09081c0014030b1b44030112200344850f00c944011400d0f41c117003803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 438264496 1250 438263246 438263257
    0xb0403261f031208270606040f0b031c03020408101406011b0f03050c19020307061803060b0a1e0e01060e0306060f1210050603240c031005060f0717 65
    0x150580882c90035007208640280d001450300015401070035a00b1345c0f0328413000c0380c0d00c01241c082000e080305080000800c003d607108810281441c41c10045280e10340c1d031300800c42105000900d00c3c541d07000200c00b081680039000b2a8088102406049900c031104441c44c2c1010138494204a800c5a940e0340c0c140041d00d040030403e00079245962500e54100000d03201070302070380c5c2d428024105a03081c02810040c0d1403801c02c20881c0005048000c0124000310b0404000107001341085003040d03a00e1142902400c0c00c5400c0c03a03c00904807076110180111a0b484044008024000f854104840d00082152020410380c0034850007804515080000900512458a4252081d0010301601e1182c890104000d01c28242003003099000d0360040ca003080c81c500c1007050007544000601c010659160440405007840c191aa00400a1110340e0854003041d03406400c041e03001481ca140540c480d143c144810314a04c01c00d402c0550000c100041500e441c800c01c03000b0b840c3d494880c904003000c0c4000c01407070a03400c1c080c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 438265746 1250 438264496 438264503
    0x305090703030513030209190b01020606011b0c080a0b180610090b0f0405100806010b0304120f0c05030301030b1909151e11340b0403261f03 62
    0x180e035050000a1080c0e000b40040840301c2c0080c981c058907500010846e680540d4540d603031000c0e40380b07800c2c0c10926a000307001078058240040c00b41442d00070006030406640fa202c21b50043d180f40c800c2c008005269250a0141c240d07035084482c500101e2901100c0302c1010394100c1400e4600c8588003c0108001401c0c030710442440c0c00c4005901e103441d1800c000b90182101d0a640701ca6003102841003a00c407442440c1c8500b50b1542910b51091809010604040045c2c00102c1420300410801001c00c1180749604129881450304851284003084121440c0c0c0c21000000d0642c00000300000902400541003806020090860040840e00c00f80400c1280d03a00440140203030414008203890301d090342e02c00241c0071098468040401421b503c40340840342c4c2c1400c0d41d40402404103000450307006030f00a03240c000b20100b500501120034032004001204039140d009061481c0200001e04040c807030310b0000710916000e5151782c407111860030040785056085031074201c0070440842010303040a44c51001c004036a007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 438266996 1250 438265746 438265753
    0x5130e090a030908120d1109030a030f0f170c2d19080f0c03070c0203010f0c030b09041106070602122505180f040b0909010203370506031e0a02040507030509 69
    0x6e0241c261000b0784900400000480c0c400c1c0600c0c029a101440343c3c5640c14440e9803000880650310801070401e110310482c0c2d40802c07800301068070b072441c2440046130704100e900750043c2e251480580c0340c2e03040e05601d14409003d1a40c0242590343d90311184090000056111000041018000001c40d20601c7c210b44078110b250080c4041000603420000031a04030041780b80009003461550040307801d4079034a00900c064981d0700ca84458160740d0510400721503030011585a1100d040030380302c03003104d021001015807142e03000003000030801c89554121908010000c11094640c40c10382e66042c1c00d0480fa45a880801d015500101d06d0035105030120b817460050b0818040605403900240310701011b14001c059042580e41018103140c0c2e444410542c8604510030025a4030f1500740c9851042030009032941c07071810700000000307911210f0240e80ca8031444802c400011380d90b46080009280262810401211040c420000d400200c00460011182d03030080c1e9041c001e640b5260002c500b00c0e88100c030340045641 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 438268246 1250 438266996 438267007
    0x405040b0406090309320306190b0f12031c0c09090b060c01050c0310050f060a050d09200f0f100f020a062d090803060105130e090a03090812 62
    0x318190f0041c0216070081c03a005201644a0f81000d41418410701111501111080841c241c1000d0419103000d200342500541000c1c200301543c00d800c01c25405442550079141d09003903440d1b803545e960390440008000c02c00e640e544d01300c40308580c07294061701440100300fa03403411a8007400b03108c0c0100c286254580d0350300d144992908900c0c40040c42d180a5081d40024204000c40403140300340134081c0500c016101d540d90743c1c2040c3c061400075890a03444203001c0d034080e1640c1240c0d60b54810603117800488070304015940350035131960341c0010708a5150041100704000082610110710303180203030340f490040d0f07803075841070900e20201311440807042c604650240106031040819803042c082c407180152203004075132414442d60303075041c141c9140c0d030f0980715600e19111000504102c0326a040420103080c0c0740410051400e600c96104c2440001c02181c14000c0014080000c000e013200108020403c420b543d42c803608004105a4a8060380d8805a00080f81c01c230b800b045200c0042003640c3c1c8c030202051041d1400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 438269496 1250 438268246 438268253
    0xe07030b01050f0616030906020f071d090c030d080123030d0302071b030f0c09090302151017070608010e0108060109050a091b050301050a0c05030c0903031c0204080601050405040b04 80
    0xb41c001064007508020280100040e0305014a40c45e8101c0d8401c0c4c4849080c0350a01c2c0c0020318103480c0e584000401c1e40040010000384203035035400018060041c4203c04c07195140307031a140c071302048114040e130544a91203011481980c8102ca10f41031f211899000202c02e0210f512005503075490306a156419001100e0301c3d001903001e60300522004d4070800c4840e100c50010b00903041290704983c000d4500d0015074941400300003080d04813074050021440c040140400c6c0e514020b41c2d03503800c0c4000c00c0320170500102041c00100c07008605401803840b000c40c010600002480240c0300c600d24460034000c1581c0200116a00d522146418140ca161500a1407581e00e00700703018000d0b010107811250b800307980702c0700300010840c5181d991104c01282c43e1000303c014071f498281030840e03c00800350074400e407034150f00c01401c03940001141d401071400d140701500ca12403000061300b03520480c0106041a6140b1506182c00d4079590068011a40d24105913030300360380e0b83c405000558000712001000f2501074000503002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 438270746 1250 438269496 438269509
    0xa1532040303090206030c0d0c0c050c240c0313060f02150703020f03160e060c0c0111030c0106121103030f0405120f0102030109090b150102070509090c0301020a11010e07030b0105 79
    0x810700030315000c2020301c030f690003251603a4000c1d02c00c58007540c000030792404030718a98003a101802e1990300d030403160400c40b900c5076922110784000c128420100d005e6061111400070110091449441d500241d4031006414007a40d070341d00078440d05040303002d142c00000b0958042d10704614240150340161003980e090082e10b5103011401490141859802c0c0070000b07401c000900a1031082c0039000e0f580d20003503e0800c001d495040c0e40820144a903a04000c400c80103200881c0c00c03c1d40c51000e09142c41800d82c070010319030540c01945d903007507400c3d8600304000500e03034424440d441005003d01084400b1400300e00c181030322481210381d2044845420002008182007146ca0700b02064610000d0701c22202c20000d540d8260b0b40281d0003a043c043d01c2e00815000d106441a040c0e8000c50601660300503a803078440041d445445034032030715100e180c0b0000044c45a680c180445510400c0040085507a20910306000d0607403003d1010f80300c00c0d580781c494030700501e060000307548007078a4100e450f0f000c588c0c0ca4441007080c0e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 438271996 1250 438270746 438270751
    0x6070317071404090b03060a1e0e0f161505040f0b0c031b03030a110711061303061b090602010509070b09060f1c11070f020904060e0a1532 61
    0x100001410450b15100c903440151001c2c108108001c00c50f94081401c052078504046e00240d906e510f130411000514002104001d42c80240c400d000c620701007621511404e00780c030510380f005280100800310040d00c0622140c1400e6a030039003001c0031a04040340c4121040d009071f010304175156410303040600c040200c0c0c201504800d03207410122440d05221135030640e20340c0408002014142d00201c1032005100c014000d01c01620300030324005040500645410042048548115000c3c0c080000c50f5108031040d03410003805540c000006002114030170418021900c2d06076070150001d01003d0300851281e1040c0221406944004010300360709040044e5a00b00ea40011001507110204018201c280c8000d0000340c2584054408215603445c0905103c0c0181c40324004124080a0100309000c00202c2e5500c030b00000680680e025a4140d8581c83c1036001440e220480c04090301c143d02d000e000300300d0085206100109145024001302181036a010188000d174540154002d000410140c0c42000d1068031030b9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 438273246 1250 438271996 438272011
    0x90c14070201031a03100b03120906041518060e01140a1d03011b031b0201050402090a1a06030a0507021606091e0f080a200a1202120303070f02010b06070317 69
    0x180310342c948400081c03506c52052504c0c1030303160f1140c1c210070301b40c80d0038886003030501c0000c0d0140b17140c5082d0301c00050243c4918050b4a000b40312004031049418071881c0d505e81840101102c00041c3c42d21040060041110340b0017042c001150b14002c41204800d1a040d664445c005442e48481001c5070702e2000d9004205a590540540d690800c4101c0309040004294140c11070340c07400034002c440020111a6001c003c0c4442003560b0502092000503100c04c1d0000b9071082440a0010b415552290f0a06401c030840a0b41c03580088007009100c4c8070403c990215000e00d000342c007200c10a59072900000712400c040e20031540450f00f0050100148544090407140c6c0c01111406080d8554030342110640303481d0580c100320840e5001003031307403001c1010080380c00d141c00020403103151002d10008002003500c0524010400101d100320150700c210746900d01c850314080f09040c10762345c0324a440c0c600240306200490507000158281540e68202d0b040031170890386810341641d904001490039404260864034040c0c00704 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 438274496 1250 438273246 438273281
    0x708090109060c11101a0108070c06090b180604030503150409020406030c0f081623030d120c03090803060402091c0506180f0703030f14040f090c1407020103 69
    0x1000141d45449001030030906500c810750303440b200b080c4e03661038110780190111485d03141100d01354845450102c00313001c1705424070f01042c0a60b81c45808803400380210b20000e200074200800c80e41001003c1c2419441b9010008101448440c2b0710142036a810701618042c020800401c04a50a03141c00c400040701369002504c08181a00d0b1070b40402c08860242d40255409104084240411030b45d07980070100402803440202200b0315440501109002544540003051305a5402d03080200340000d995200460018151b03106545070050150600300c042528425491405d8000d240701c0703000303102d0071880c603411409443c00d59035002d080c000223521025802d40c2c0851040503003a400001520342003011403140019007484d0408801c0202c142c0d00038a400115500701e1214541c075100c00003080000c60750140340001446036052015900040c10380d0814007038000010340401d00056010200d021541c8151040040201003102204d1002c220100c03900005402c00a4002540c480e42080b5074401d00914017 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 438275746 1250 438274496 438274511
    0xf0303051e09030301051c030f0c03090810050702070602120f03090a0b09010207031803020d060504150e010b03071e03122a0b06010f0f050309030f04030f1104060e07080901 76
    0x140107402000c85004490ba8400001407000303041032005065050143d5003800804441643c0284c0b603002404094002c100d0741091400c02c0c584561620401004104141c80303000a01e09000030103011708407181e00141c0b02c1d00d07800140403880014000c07001c610404400b070810000803103511080d0301c0502920030354851030302c1100124607019201d5000c0e0006074001a907034240c40c50058180b14414001802004400e001007015031180741c0c0f030041490b4480b00006844d561490014409082e055801024900c0c0c491440711141e0150302c031b00f080f40c004408030350905540c0c015030b422169171020302c804512600c200400026181400d0b04000919a0800a2030700b84003c03203c510322041d01c521f046c0a65983c10f120300601c1031008190f90000e40a00c0d01d6a0013090303804004e84003400c00150b0b00200300300000050445042482960200c006c81c005c566901c0d40c2e00c0c244035603601c000c104107840c40c40c107101000302c007407500c0d1207610111a10725070006041c1e03860700000d40b2120350050505419549501d003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 438276996 1250 438275746 438275791
    0x110a0602031317040e041506081e100203060a03150204081b1306050102120a091205061008010b010e0d11092401020105040f0f1e080a030e0a0f030305 66
    0x1840c4030308100182c48041e0b020908110320000b0040c903502091180030401445000518102e00e03921030f8001c015000c2440ca5118a40024616507100c180c00f0700480001b80300030707100f40206061424840003222080000901080304038401a101c0e20f501803101c0404100040c01c1e9810310200445001d0010309242d5103603413841c20105410b107442454407401280c0611894600390010700f113003c0f00e000708829414180081d6075404202c0f55261000310218554115500c82c40c4802d001d407400500e00c0b5004d54007480c1c81c6c0e40d610b03000d64003443e100b4444003012501c01c070148982041040142e5440000c0c00541040c81100d100c0c5510a54100062140402c09501d03561070440c001d48181c94086610001e00785602c40c60812a840c1904590405044c080811200345981550682103040012054028034004550350040d03114445202010700e0442c0602c060080904941002030700c042c401940c44150140c0c881c2d200440c02000c1c40c04401b480408213110b0352005a20501e802080c0c52545210700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 438278246 1250 438276996 438277001
    0xa080d260c030103060f021303170c0f0f071208121e13021306050901051504030f0302010e01140106050a110f07172107061e1b1815110a06 61
    0x50301c0c8a01254004010420040c081c804c6801c61090458114100315a103246826048580d1101a0880040f034951000344410341c000c54800920442c1158031000800f0b84076512a401009190003038014500002410410503042001c0c0c554800b802c18504403409005501a4801078000c0003503d424500b12126004500c01441c02440c1003401c02e40d030f40b0602c2c4100310081c684807850003e1941480d00c02c01031901c4a25046064641c1110001038951384072510500c58000c0d940050602505100440181501075112010b0291160001d000041e000c0340104051132003071142078000b400c100004900f16110740d14a503010078140c4196a10030303c22410f01032411001da0030004a180160360505902c0d0806c01c9100802180540001110140c003100000d05000b07007c0050300c07940e222231a1a100001c0d404942e2148403200c0780820907040f5800755010400150318068001c034070b584070311086905288005ca8201c03180304000011104801c40221049050740b10f440f00b030ba00c01d80423084000b03990750 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 438279496 1250 438278246 438278251
    0x30302090904150c020c0a06120f0203071107090507050307050702030a230c031606112103010905150a30080a020d0c020d0209190509010e0c0a080d26 66
    0x10040c00129040f03002d20201100c403425030300d0341558480716440950b0780b200b07504001102e801d0706081284070031030030300b0001602d4415890007015100108004040350042e00c0d000c80380002e202210605611403010f04101e410558603440842d90503c00210024400e10007003400b10310107030640d01aa00e80d640e5000a00c241c000002c80c0d01c7c0740c51403019000c076108202c04070014000b01d000f40003042a4002002103201c00b03014040401c024442c00e002511420814144035010301000350078084000d1440810039042801051082030500e0089000044041d8400c2e0b0720a030300924280c0788030b1901c80f902d011a500b0040c6c40d8450541880c5901e0a0a030107502c0d24181402411215074400f01c400c1c0081c206410b4a2100c030034040303149019000f44c0c481e107004140c910781c1901c5010140e203522200d442c9400340196042c0c19141081d0802c4079200e019004480700d0800343d4110f80c04805e02c3d50810580040b43d01901c0d507540d211100b20040340d803203144140e0144140ca00307403080103e02c0d08680c0b4904a001c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 438280746 1250 438279496 438279503
    0x60f090a09020a0e0a0f030303020c0313090c08073f0e03040303030501050307082a0303130801050604020f07060504062721020c01080a060503030d05040b13030207060c030302090904 80
    0x1c02d00c07030003d54022140500d940f00c01c0700c1014a0a0070320049001d040900c2c0005010140d01040703017040031004008031000070055036081d020042c0e84049901c00f8207100c846000c0000d01c2d0b40c011411184c000d1100600c08480842103d1300e40205250807000c4d084003224900c00b580010800c0344c188841c0303124824051006001841d81c1c0d0f411820b000d41a00e8041c0d01460080c0d01400d010000f8803400b042d42d04241128109266010002c400c0e903c40380b545609030b01e9410300001542c0d00754082c9181c00300c001c40f103044000f0b00c51035480e0001c000032405000c44c41100040304008c40f400140c001e501ca964800d109160000c5d20308464403008002c02c2c40740e81d1004214070f24445000c2800800c44a0041803203885406000020410000a407140010401903041c003a00c1c0c0d000ca00c02000603004600a00400303411640c880640a5007400a0300d010340e0700740c4182c03174428041842d00203c08581142c1c40d07015001440300c2c0d450705108031f455000e003600a0b000c2540c24404002140c2e607807088140600e01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 438281996 1250 438280746 438280751
    0xe0a0f030b041a04030c03050a021e01050a140118090219030506010e161b0203070302040c02161401020307080d0e031201030203100614100c0501020f19080601050702060f090a09 78
    0x82c245044202c030012140d041d000d51101c0c40030400025440001d05000d83d0349882c019483e09082141645046040c000c90440b40c03070103440012240d18154822417061144c01d40900032140801c92b100e000070402c0c003401c041800820148824030b031168014a801900c00741c0b11144100340400e101c0a6818903801c100d405801c000010051440e800b40900e400030500320800d42d100513804000f8005007022984107284a101d442004150f64052010307000440d00540280034140710500001d44501e40f80c244134110100b096404940203141280d0190038081c181c0080d07160008a88442d001600a500704100c0541c40301410360700b042052014140304155a2030160b4a9415807040508017015010541c0a40b840c0810410121102d0303a0b01c100040d00c1030b0791010100510705411141e030b030030100c0017404640c00001c01410701140c9200030b20603400054004003801001d00d2044440b0740f4242c03869400a1814800e440c05881c00d90010138803d04039101e000d185c541480302140321034034540e000c1010b099 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 438283246 1250 438281996 438282001
    0xa0203120103080717040501090e090c100207151806030e0f030706020a030f05040b0708150303070c140108040b0703150503060f0a270605060f0901030503030103170a0f0e0a0f030b 79
    0xc1c140c179400c00e0080200d6060030142450002400a410b0303101d81198661070001040c0701c07810038020307a118a00050201e50812002020281da1008180301d03440284c0d80c0c0354001102c0b103101d81c945c503241035518045030007000c2c80d028044029100d078004400b04d50160605110a04804000400c8039a2041402580720701c07202074080c0880741c600448142450500382000000340794050342d030380d2048035402d1048440c1c581c6036035041040168034519030188000200d0009221101145000f19219410188100c2503854011248e9040aa60050480b06c0c144046106980650071410400d0701c1104420000c0d5601c80c00203162400a03114018030002a406000010049008401131254103546419403025001c15040300d54101c0140500200e55500c0819510380e030f004500030014500034904e18543d6160306006071241c0c02840111400000100507180c00d190000c02d549064105445101d04e121803210140e0b40b03925a43c4407941d204001800110b21060200c0881c2e0166000300500300552 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 438284496 1250 438283246 438283253
    0xc23011b0c0c0e06061603051605060a0513080d0c120f15050f01020a020f060702190e090601031a04050f06150112060e18070807030b090c01030504080a03020a02031201030807 77
    0x1036032950481808000c3c280104a2203407a8041102c200703c02d41741400d0300c0c0c42d415050840d40c5000c0d03150461804800c500304041804070000e201030040000b49003c001c562101c00c0e039041c2d40e80751001c0c003c040c420309111040f50070040d80c0c04135110400c0c600b440e542080343e600b824801c41d050700203d987d54540c0c824207154468401c0002c00b01070b0805603290000c3c2c1000e00c0c0007039070b92035500d80d009208000030310b085905615800b041d600b403142d01502250081000e1004003400c0c48290240041d03080c044030014500040014025040f00e03041492041c08503981403c400403c00001c00903161489084200c40180070100901842140e001e0440c4468801c410001010044440280384106003440c0051210b07a10b5000056001240c10512807151190348510604101c1140e00981c240e00486800005008a00092600c01c5141e001954000203070358005404983c0301307581c00b40c014103040c40076605003402035004101c540500d00490b03013007071002210b49040b00c0c400d0308210b0700000c0202d0b140041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 438285746 1250 438284496 438284513
    0x9090a09030e0f061b010f0e01061d060d03080901090c03030224010b040b07020114190909020c0d08270a0303050108030f0d020724051005010c23011b0c 67
    0x15100704a603441d40c0c45082d000060f107117010345400c003441031102012400c0f0b109425800891072003100f401c2440000308041049000744030601c10350f40c0c0e604c540454a00c15001c04851580f08000080c16800f10602c40d440c01c139440b450082c4460129035030b48108101161381100351100561082c1d00904440d43c40b564220041c1c01c5a054100492180c4001400280d100d00300b541e00303a40704000c0040e2903906034001268040300032a203203199204001006106101e40280141641e851a1030706414540d6840c4403504a200702400483e4076001460b10840842c8504445a04082014044520350000d01c070095507856400c9107102c141e600c240940e0f0b04240e01405100d0040c400100518200805c48044030707014812030301c00c10550313540000c041c004c1214003020710f1143c0721134444540440c00320f2a90a4020107046d98540200345511400003290341c420350b00c081005034046014000203407034500108c18000402951906075480305448010300748503400000c18081207646030b590441031414507009 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 438286996 1250 438285746 438285767
    0x60209060f03161b03091401020a0b04061401060509300d0908010b01090806010315020d1a3105040c0308070302161208030103020d05100507020a11030309180a0209090a0903 76
    0x60107030b05005060302080c1c001b50a48104c1e4105a01d400b0f03c0d111000040b800d00c0801d000041a04240c10103200910600d5032003100070641d80c446010841e602c500301a04ca500840c0441135002c140744ea03600f04400745c0c2c89080c8039241c4110303102583c0f5085040c200c0d070502000c0a10f4000151101e00c080000364400d000344d4280c0c0e40f0a0a290400500b004801a00c41605010282005011000000448406604940d4401c1e6500010019006106900d0062041524445103d0708050614200c0c98000c8000300c215240c41d900c402806201c13a42c103103405060300400564400340c0640c0c0010204031440001c01e01c052181d4040c04181081071203803c09030106400003020b10b20b100300c5000c0000c078030f0000c07030341500d40403202e4043c420785901c0c03d1440d0004400d8400841c41c101801d009129800107200d003d920700c9103103200e02011641090540d0b0f8000c04840580c040309000b0b240c00d281c00b0340100d264022490040142c07415810758003140d81c082003035900904482e540c09043c001c0c5a4040c08454 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 438288246 1250 438286996 438287027
    0xc0402120112140313060f0807050d0c050408010e06040c08150a3b0706030b031b0d0b0f0a05091506010e040b21070803030c07060209060f0316 63
    0x40c18140880c503400d038141014090a03030515203510008040c8140481c401c021052500c044030b0384e403401500307001c0a0b0300591040001140d520302044072a607024032542840b076400341d96242e0800642d03003c0c0902401e08a0281ca0030f02c1020031000c82d242d00280980f032a4404924003c01060500380b034120b40381ca02a5102c44c071141c10074515400d16191001140e0340181c170060340444c40074103500141181041a21a203c0d052080c1c8004021f05100842d0300050080c103c4296503140c0d6442c2c0040e810380d00510000c41d415007200584503c8050f8503c01c580152a0252140c200d00d880d42e903983c03410440580d607460203000c0410411107102d12501811740c0c0405a0b002402020f07030900f42d0614801c0000d00940d050125859080c07440d41c0b1b0740e510650103000000e007286c0f030718807154030451001064022020054020407001003280e80c0000221303401007540b2800d891609000340c80e0040250044807140b43c1c4424204000d61024408001550044020501981c90225049405002040aa1100d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 438289496 1250 438288246 438288251
    0xb010c1703160c030507080d060b07111306050906101e0816030902031e010e0307030c0506060a0506030c0a0e150a0305101d1e040305030702010b030606062703010c02010209030c04 79
    0x3c00003030740b10003582c090a0384000d006440d89141c01e10f44001d000a5009800c6412000c90310000340201241c003016124010b450084035100040c010200b5a640d40c001c040d00004040f0211f4103e04090700400c02201040c0303803011664076204c00ca800c0140c4214024070000f085041400702c500d41404100c00e6120982c03d04101303082c840e6010a8907110410b0300c00400300303031000005d20061030a402844150820034281c950301c824900d0050300d002c00c0d44d0019221841214009002424483e40f464250341008144c00d096a0700e070140780e00c0c95070214440c0804c02503d400811550b45580f08840841503182200325103d203110380004040350001440c40c14a40017031901082400c903c441c1100c90307500d041c1c400c484595540c00807042504080c500a24001512900308030500d0b501c9400742d4000c45040d4000d2040d440d002d0201541c1d04000d0760480d61000d4100440d00d0a010314036170130401420414a010405050240000d08660b803191001d40581d40005119034146018424005c0c10381d0b080703808 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 438290746 1250 438289496 438289517
    0x90e090102120a0f0e0708010f05061801051306030215030403080a06061b080918010f0815061002013308060c0915040f03050106090b180a0b010c170316 67
    0x81089000c40504940485613607900441406480c5402c40441c2501880450741d0103540d03000414024403034031210488030707458103003c200d403854800385a802d61a0400c215100d280d00748810070900040c40d4501201d59a616040080107848a05c0d0062030700c100d648907281c0321701c1d0903f000f40c01000010300c100c20403442c000c030074081d10b508900003940c2680101c803031007440c884501c2c00300007601c111700c005a400400b8242c00b1805c2d0710b1000c007550503501c440d19030203c0980c0d6181c1c0345a5401d248042c2001c2024440f001030030505104016240c2400306100200e1464081aa8580301010011294070090344120311f0341c0c92490f13840e070810018143d000040c07456180a0420707c0701406240172007071103588549100400500705030180c4003d002072440c1c0e0f522441d903070700e8018000e15692180340240d90800c41681500d2804044148840b46004505442680c5940300100113110a500e45814410304060640c042600c50100101050403e61025501d00307010000075007400414040104002982c0c84 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 438291996 1250 438290746 438290767
    0x509010e0603091b06040806130501061a0a0c06090602070b1012080d05040507050901080d0e0409020f0d03140a030e07050f06041e0b07080a1202032a0910090e090102 73
    0x210044c2190001c41071110b40074030340c070028a5505c0b440c3d0080049100b40000d0080189141039000c410611500080004541c0c8010000c18028840d40c0401900402d00900c49210300a000c210b91180c40b0b0030000503500300980c0c80328100d0704103e00c10b48900009804002c0700c91102d00c040d40c090300d559030344d5018007100c0d46d441c02c1c42441285040f60225460303601003010002c0801c000300c003600c00240040351542c0c481c40e0340d5556400e0484680001680f035101b13641c090400344221a03089030040d0070b00c2c12060f11401031100000012070201d041080b101a00c03400251000b016100e0600f0300d64021030900c040085041c90003405800107849808500f0315005a503030742d04221411034440c0406e42131002c1c0d040307440c51251a0140d0120509400c00148001088843c0340144010000d0303072100d0404031100080c2904900044401c900c449429248500e48100781c4401e03041c04000760f140a5241415040c041900d81d48620a1403000c5100800d0a0124080500c031450b403042000c0021810722401c5103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 438293246 1250 438291996 438292003
    0x30402210703240c080a0c08060901142409040506030d0503221506150c0309050f0f061308060f10140315090d020f150402101106070509010e060309 65
    0x4030080100f2082c5095401003a031400031102c901c9180407080124540c0c414028108000c00c8490451591419441c7d01c1c0b402d0089154a00803203003d00806002e0303081c00f4002180c00090200c160307203e04c1c141d603880841ca00524a9000c00103400c58030680f2100c081050105698003e49442d22a0b08200c8120325025408005e83e5481810003c4107002d40313090442c0543e50b2110400090400b01d09000e00311440c0b052500624111b444a21920908483e0080c00f140c100b8840ca000900160010b03a042040f8500000b4120340e0140003000154a00c00351f500080f816070000a0060440144007010400c3d03810600c400c0f0350001d0b01001c0102c05141c0511040c407241d17980d002d040f01c03141c0164180003107610304103d1400e049085824402c0079007098100f695454250740d503003a005100d0500e080040c5000030420407140118004000c40700c0d11790350300b0003c4021452884004200c052074251003c0381c0d0030001d030f9008000075110340360390356a12000141181c20300d4200718090b1800b003051001009000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 438294496 1250 438293246 438293249
    0xe120606060306210304091505011b0b07030618060302030d05070b19060b0304030c14070b0712110a030908011109030a1122240b030703150512030304022107 69
    0x444440c42c5005806948644c8080e14002c200800d11004c10003207400f00003076020354007181041e40309051540d501c8004448803054001c44490707400d48a004040010801102c1580180b9103050100c0d817117459500c0c020718001c044c8528010507894042c2003044d41400e214401c0c0607015498001d00d00022501c3d410700b00c0402034043c01c0d140041d04903000070b221580e1b000c440035205060800341d40b4100f80c140104807400c07159003991410b40c4004c1c4080c20040026042e001c40d00b240c0c03507a074105502c80e150b0640440401c0d41100502402003400d40e0794800c14032400d04400c2c800d8481c810390505141c4901c9c211105038110952a80c42004015504d540010b407902c4156480000c6007250807101c03000c658001e6891942130318060b012087c00700180001e07000006014512185142d0080c85081c400300c41e00c1142c42440981801000030541d42842500248819606604481442c80d590301c04942d203c2001c0801120980000c03003440114508403800d03813900201d07480780c00e200170742c3c84a03060b82703400c0c15 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 438295746 1250 438294496 438294499
    0x10b01050a0c021813060501050105270406030f14010e0303070e0409110913110f06070f050a05030409021c06050f0121050702031e0c0604150212070e120606060306 72
    0x81c8102d5411961240e1031100111402c00c0c184441d820030003103200d00d50000ca402192101c0c1880c0c000301d85944507030181d541003070504510f04516101151043d4020303c0c00d1100d680c020340c640c600800410710814a400350700b482382c3c0f004501140b07569070103800c540080315400b000c1c0d0010400d0114040c0d006080000001c4200d070700040d66a5285010116405220703a1150402050002c0241c00d00840c0000b01c05a4060350026040c8003240342000044220324981c035500007c02d000d04804201445155903003103205104070f40204a040e1501c42c61500154841d9000e281c00081c01150302d800a40f450300d0550800d482400902d080200090441c0301c0e200c0c040c2d041012515142405580c401801c640e24400d000741000b06082c1500004c0d01c3ea800340c0d001c00703042c001005440001c46507141c1250317000910100600742d13588541c3c2d280f07500c2d40020003110803166001d00083c60411400520b5500520143e120340400211070030601c01c022000042d0180300d600441c0801c40746072100e0301102d900150 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 438296996 1250 438295746 438295757
    0x5040308010e09100c051801020601030f06110403170d0b010221030c0904020d052220060705030a021501090e0c040e0106080609162c0c092205010602010b01050a 71
    0x4483c603640c0d10b0410000c14104005041c060701e500203d811000600382242c0802401e00603248600c01640e4500007840010300c40c1401412a001188459008071403d07150402984e2030682c1c2c0751240072a0000500005003103080001e14071032411024818041014000c0c0090a1041c0c200c076403c1e41d8030140c03d01c54040c0c2010000016180d400342d442142d0b0608001001191100045800b040c000c21084500c40420800442c00031000741d4000d1076040500c3c1c1c040b200d101c8103001010380a00d01d40340b403d4982c4e00b0103414492040040c1c424000b90000c003203540e008210b00b940c02d000b80401040180e11803035100d450120031072a203050220724030241110544020454020302c0400e2401000c26912508050251105015103944007040c088080742100600c020800d45850001001e0340c41c01e41c0040c003000051140c2c689900c40b070048140c0c881d00302444d044c10912003402081264004040c4400c00d504041d00e4024080441c0c4075150240403e44000c1089080580010f0300030704c16034a41e40103001c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 438298246 1250 438296996 438297001
    0x501020d0815060f04031a0903070f06020405090108010f0b0103111e090901080d0305073605060a0909050c031b0d020408101a01021f020d3c05040308010e 68
    0x40354100c00c038001c3d0140d5550140741c01503a80607000750104480c801e00b45030103d02095000b4140c03900501003171000e107150040f96559050403141440c0e04a82d110f03000e001c0003c0c9950340a0b02d041c0207142c03000004c1201110b0b109007404440750250f0103810b1501c0d20486000c0041702c1420f50f07151102e62030300b503c4401c0c64010710504a004010440d0390040040c0c0010030240d00104101d8107200454406001540f41c003d0180c07400564078511286901000e000340800341e0b01000f00e005116102d0b10308120320b42e101e00128070207500115203940403501840041001889501c1410303030003001c01080d04e0941c100700e09817030303803e0305400e0980d61015004a0060303003500c42641201c00408082d000c440e500b00d4201e0700100600144914800c10b10304400d020122940041280007807803061501300d02010480c00c15000c020741100c0c070000940303039440e00c4102c1d01721480f00c00300b400440c4000382d01001c0702d00b50000783d091002002031201d009051806102c0001d4000d1000350640784420005040b0780d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 438299496 1250 438298246 438298261
    0xf080a020a03201b070e24040e0c030d0c020f061e03070e010f08041115070611071112190623040201030e03280306080709020c0c09010501020d08 64
    0x28004501d01e0004003004103061840c3c2000000181280c50642d000945040b050401d815160348a0784142d0002101e200300080610440c48041d41403290310b0720300c0103d04180c3d00041b41c2200c2084802c5a42507000041d2201c2c1441c04020311101c980c4285008215a00c007580820b143c0c001840030140603040c0440d4101d071f0303003126805000412001c1400780340c691a00e25001440d1070098080c0b80d0204400c5461682203901c6111145c0c4584d401940072060000c0100521a403c0b4000c4811020807205100d007500041140c040d044c1120350007244117880e418241807980758103424050b0a80b0514255101490713503400031441c1e1025034101c00ea406a051340030f040140181040406c1e096051801d100e5a00e03001c140711070802d001d54004c3e03808100c0c40c1c8549640f141c0d0b034400c40c0101104580d0552207144070b6162007000e035050b40024a03000ca4182e40d40d803006031410040c0d4208845650b00801c004101c02010844042110000c40700b04646515140010351550a50314019080114850001c1c15a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 438300746 1250 438299496 438299501
    0x160215040602160b1012030c02090402030705180906070314010918020a09050714090a031103070902030708090c03150c1b0d050a020f010b01020705062d040806070f080a020a03 77
    0x110303d00c00c000002d28041e10340030546000846059944003802880411140c2c028070700c102c251035054442000d01032441c0c080003403462000307108a074540b0501c207003c02e907500c614842014800001451080c1400c00082c4141005002010750041516103594215980002c0f00c00c2e904480f000c0000061012810002039618450503601a4200b0804140010f040d0b010740d0095105200c180c0d2503e00302000c0e0340001d003080c440c0c4a00250302100680083c4003240b0484209550344400074211012156030f604040182c1c0c000711a000d011034100c6027001075000050085110602089014007602003140842a00791b08000e0003009c500c80c0b020812071641000e84103086000c2200b4011035100007105a002491640882001401802441095200d02d00d0502580c0c00b6598141c014105071401d03c01880002e411410282d401814001028241104034564a40300e0004a03440141d40301e0910048902c2c200d0050103041c00c208442881c6040c040c0c0c0201c040e03400950015002d60b64a2070031400320701 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 438301996 1250 438300746 438300757
    0x50706050f0702032413120e120a0f0210030e030d0f140405010c0e06041d060109030b0f100605091f020c1302070605010614070210110d09030b160215040602 69
    0x401d0f20038405140e17501c000c0803140c10b1043c1100090004e6903135030100310303007034003030341003400402801c1345041c0d00761014080d0010b200d04150251103884001501c683c418502100c45170181c0350125140340c120254240000600d1906019080034084036a00008c038a94911401401c0c0701442c4c1d03134942001880c0802c1d002035120540c840c51500c1d1504060900600070050303511800c020a0810703040c42a41e0400744140c40403502c41d203030044290182d0041c075050b000b00091030f203810001311101c040b0000311600c05650040d0000b41048c421490019100038048120b50040024008248404180b81e40c607111a002c960f9000e1108155107030b0700940c1a0b14140d031201c1030a522a9180c182464065001c2d170240400c80d009090900c626662540142d039056581c10401d00000004c02c80300001d810103081404034a282450400c84903040001c0300c1d41400b02c01e190040018006041c10418000741c00c1c0442c0d0030880c22031001c1d000030003a010196580e45000540340440403000002414840b141c0d06440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 438303246 1250 438301996 438301999
    0xb060d030c020907090e10030f060218091e0f1536061005090901030b101d15150a080a0239010b01050f03100b0d06030b010e04050706050f0702 63
    0x110506269401070718041c0b55006d004c0c0c03001d0705e100015010f140e130b0b0f075000b004580c2c12406140407401c0d0b54075028042d500442c420080f03944050a0709005444a1a51038401c4541c5840505c1c10813000b0812046c00001078045d141e20790801c0c044c890604801c508801000c1001c1315104800101d104000751000392000780c9c0c1960742034140380506240d0300b1a01c054800e107012100c0502400100c0c07401d13202c6000d210384554102c0146001480001d0882c8620340e0030400350b124a01c0c5c919950304c00154070b5180380b103001d01810500c0c0184103040d10303031114040046008641c060029002000f00440c603010b83c1c41008200703e040c1c0045082c1c00003070750448149003800c44085546038000030444030b50022024074a1681211500b003c240d00e28188980c284081c41659468500f01610074204ea06800145c00e010465624034400943c0c0500c020040c005c0c0c035240040030071580d265041021540405074417004458668100700300004502003041400d0315001d0074415160094034104091600448038001d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 438304496 1250 438303246 438303259
    0x912110c0a17070b0301080706051606090c0501030b03060105150a030b041a03070603020c07030809011b0b01051201020306030607030e0a14011a030c18060303130b03040506130b060d030c02 83
    0x2c500316421000030b5001180382411541c2041d559601416a071100744100c0e0702c203401412040c01010b215900a003200e00a8a603011140700c034546852084850054040b00c2c2404000c00410403560103000e5010800030407030180000b5890200440c80000303203480013100000b0000343c00b80529020f43c1c402d540c44035018204004030102c0203040141200b10074045440391040c19070008800c0d102e40215000d1a03d40006011300510716aa1400b05803c000034041c14880482c220402d035010290489070703c00c1c040d524020780765242a007802109400b540240704142d004100300b00303070364900041103a04610186000614a600e400300d00b82040400c10004048a4180c407001c0082401504402000ca01c600d1038158980104010140e50341c0000e640f03640c10002c0119071503120340f0211011a80081c01500392850480110700382d01e010b02a84d0004c04107002c0100a00c02405020041141e20601aa01d8508040c0d0503440b14041081c0007440244121039000651007010705c80c0c00fa040c4c50039809000b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 438305746 1250 438304496 438304499
    0x90d050f010b010e0a060c0f06090501051f060507050a0209040602040e070c020a0e190e0f030a05191701030605070201090f14010c0203160605060607051609050a0912110c0a 76
    0x40318064024100c40a000458a00c114001841e2902001e000c8404ca45c40c1c0c9241c000859076050500e000c0f5802c280c54081e501c80004011030310070300419101c1d920894030a404d1440105540a4080c0d642d00000f08102c810301c011400150000b41c0e4502132a011900112a9690741c074060010788075a0700701011500e108828400103036000320040c120710388201d036801c1d102d54441c04104881c0d0340481e02088040b80c40604100707221200e5000400381c5e0310b8041580c03040d46901c25010b140d0b9000c5849200001c10005501c00c4480c484082d00100104034078005000d041d4070001101300c00b50601020f06525901d00200703001034000d6000c2a8103641c018000388035041d41e81860f07801102c040801511550070303d408180800d00c04011248410103c0c0d4501004080b41d4032460010b080c001c04081e0031400400104012071020071000d84801240800d003007815007002c0c021402c0d900041d013200d44180c01c100360940022940d0076981040b8481e481c000c4040b641d01c90006107080b040c048111b40080c4403550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 438306996 1250 438305746 438305773
    0x20f07081509010e0f03070b1b120402010e030d0909050a02092b0b041a0a09021f02070e010e1806090c1e04090c1d370e03040f050d050c06090d05 64
    0x140181da4015410f103905070780c4645000c00b0318274080100a1004808000c40403403000c4890b42c680c0c21900615000c481600882c010034908044070003071101050b02c01d4010005802c103030042c6a030102030300c0c4003507041c1200d8201040710481a0302d0010b0b070101c502080164220a250814041540c00030704151481c1004d045c07002c2c4400b80c000c68480c529040c1e00c0080c0040d800313805644000e940c09080d40741c22a9800c404015081403403601141103020b60301c0006240f07541400d9550280100c2118800c480c140040000c50100c03201400c0a042c2c4c1141080020503032011481e00030015055982c40c10303820782d1450881030702d2207a900f0284d2203890139001400f40302400542c1d41c01e2700c810000c00380b60030340c84030b60440381c1c45401c403000303d84420000e0800303880d0b22a03000a00c800c0d07034244400e13280031100c4081441c1600c5400b109948158070100f0104140c4080d40007501c0180401e96440a03001c0090b15142d4a03009420002c1d40640000105803800c0c0d21551810000380390400300755840c0d01401c5e038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 438308246 1250 438306996 438307003
    0x3120e0a380705040501030e2d030906041503060e040c09020a050d1b080c070b01120c0302030f10050c07030f0f020c1012050f060a060e030a0204020301030b07020f07081509010e0f 79
    0x140c074001f0b4541510084120000100d0b801804100e140041d0581d811808003803100da41013169040a010a00410b0070030744902000d400a0240c41c01d1001074007a016000804031b8140703a10540803131f14070a0030301c00030034401c45a41c0b09032241d50202582d144106201511340d44180030001240703515084410154079042c900d81941403c2c00d640302c1002e9110650180f146000c0c000000d0509820300004200451140ea01c0c17600a42c482d6454a17103c40d6070341c00280c03c1080c184c400c080a6000b400e858805491144075040d4030040149040741006410780300100044288010481800300c0d005541d480c03603000304021050340350001c0030301c5a0000c41d0308004102200d005659041c0f24103000100300719080da50040751048030081c09143c809883c10804894004c41140020340601403003c10b170000d0b8a0b240015030196000340300ca003019041801c002840c00405906548050b0440d8409110101c0c01080100c8480000c00318014251a1420701500400c800742c4100028840e10511001442022 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 438309352 1106 438308246 438308249
    0xa021b133606060f060818070b0f04030303050610051204171204030f0e030319020c10020f1b10050a0e0d03120e0a38070504 55
    0x509003842021440c40030080c441400003400280030041c01904000c220740135400001130320b400d1008003100360244c24280ca422101c076400d40074940400010014004241e04641e0341c40c040c044007061a4054401100420304040008000d0b00c4c0030311070208130807901d841d503600e0441c2020b003900c200c0000400807200520072401000d40100d03e107019108440000b5041c0c11a403d09040141010500013904010081c10088001c1c00b510044107684954841d41190320007070003881e01c01d1341010041640c050b004081d0f5401020295400500b2180d03152696054031901030403915411800e0740c40c12502c0390080402404943d41a00c40c0c4010258a103c0d481c0c00c018142c2760a0000392194920002a40000c22110b0030039242e0800d44a90ba10070801c4100801c3c500c105a512082c1d440349a0222100c80316441c0302d55400c240c00c84110042d0241d95400441c0f09180a060140135030300039 = true := by decide +kernel

theorem cover : BRFrame.Cov 438129496 438309352 := by
  have h0 := BRFrame.cov_init 438129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 438129496 ≤ n) (h2 : n < 438309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
