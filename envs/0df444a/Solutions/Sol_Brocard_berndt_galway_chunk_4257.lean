-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4257
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:01:46.151985+00:00
-- url     : https://prove2.me/submissions/6fb371f9-5b34-4c87-9b26-412bc60c86e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 765467625 ≤ n < 765647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 765468875 1250 765467625 765467627
    0xe0103090201140c01021b061611060c1c0207031106090c1804050c0d030f081501082802070302031b0a020108070f0e0411070302010510050d03030e0114040b070f 71
    0x6400c140399410ba65600000c03800600c400c659030000d001c40e0b42d440d50203002d030242c228032103007147d04180c441000800649c10015020300c264541c810741002003050390070082841b0840050119084820746528a80d1261050101a06072020880202c0e07400d000261001c03d240d402a280018178001c42c0c1a00c2140d2291022540d4900003604135079040001c418200156140c8006800d9005000b101603c2001103000c0c00a0910303039109a0450214451042b0341d9082d9910801d40c81d07000c000c6503a0000e02031030200028000100060281d2660300000c0d12850614640944038010361076271080942d21909940f4010b500c03500103440710111100040c4e01a0080440010701d0118030340c040c0c43e418103079210070002f16006d01542ca035040600c404800e54640f551a14842c0108219a080701c8584908542c640242912005481c2c1414408603c80c140311a0303a850407500086941810006048085403a07440e0260001d00e544004144802d810407091007066000a40303d214070341d0702d86001c1241024 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 765470125 1250 765468875 765468881
    0x14250b0a06080a020d051c05030f10140f010c080414130c0f0518030313080c120d0f020a0209040c1d070c0609110d08090a050a05280819030e0103 64
    0x2040c0612a484150603c016051800c0e01001d51800340003a03c2218034004080c00c0d02c10b45c1000c845001a100200300040c1c40d021008050b08007500e03070314500829162000b0052580f400e050120f200d0f00503c0e00c191601da00481c00d456046a001c044951030f0303070390b4003010400414201d002c00d000301e40c0f61900500320882d0703210711304002035244c88840c19a1a40d9a04940c9038105494000d408100300080c030300c9036038041000d00100d0056402c1d1031030b0386007402c84140c1405221007805008210340050804d100b0004160040e40c2d130001d2904541c080c0420710304a04e45548098060b41002c1780358203110500900c8125981aa007a01003e02c0b01000d0840b903400381107404484040000c1d00302984040010701c160000348c941800b40c0754100c071480301400000c0c1c1d0900c074100111505503001a03030400358206800d0303403401000100c1d111000c60f8940f1010074222011007000c203001d11048174071440c03405d02d2030704203d01421031801100c410000400e000c1d240101d448400798082249607020064541c4280 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 765471375 1250 765470125 765470129
    0x603010b0126060607051207020f12070603110d020c071505072f061908010609030f060e070b07060902090c0313060b040e030a21090302030a14250b0a06 67
    0xb008080710b88001054080c501c01911150380184200b110b440829010070812101d80e0f5000d120340d81e9900c60b4410011103113048119140106000300c0c038806415004075090f4111103040c1004200c2d4400c0300c245540a228005a40c00c20602c007054107107452078001006c4003500c60a42500440340c8284105494902442400900341035198045844d81c0310288141200400707400301c1c91036110006000900c86402c6005031301c4030f000840d4000c0358600e900840070345c01029213003441700d5040e0440d140e6005030810b03c00054016038550070541a49a0f04011540050038244c405948551161404002406c4c235040309a20594039100070510780300001048074041c020111802c40c82d4805503448001900b800002180e1080e40c6816050114500b48000c00d4090802c0c0d403851260841c0160b203210320044681254102031400d9600000130b9000400c5036141c0c40c45050520f01481c0c0d450321300c85e691140c510407601201d40160039640030005100c528002910480c440b0100340d07504140300c030032940301d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 765472625 1250 765471375 765471407
    0x90812010f0e070e0102011103040303020c0d09081917030c0c0c04020a0c150b120705030118050a1e12320d09080702060f071502210a0f060b030603010b01 68
    0x2c10210701c00b035000d0b800c2000f40d070006000100340840300e0403c442181d082100c0c04e03004a900010030303090000c010711100784282018142080400e051254050f070750040214960312074034480c01c4900a00c009110600d00235100c3c0d82c04507981e450071141007a041d0f000019000324905c200000201c2c0e925040c000c1e00c090801c566600445100d01e600c0d00c41d0f200d1070b4412030340318880c0d880e82c0301242d5440d100240b5840100c040c0013031070301902d40400c1c10f084071005844481c44400101d00d0384002040410401503251704500b10358024241081280f003941072080c0d004001d240d5030861050940c0c0c0100600d401c81035542121f9440d8242c810510f01c00ca6202c0903840c2604004011420400c0304541c80507070141d00404419007807201e10b60200b003042d0300c208920b810300440440d500341000f03140c4031103d00560301c000c07043d400d0811110501031610000c04174016816400c030002240310700150300001c1182d60f00e90003409072541c1d607021160f19900c2a00c10500a50908c1403584155000e11141c88544104c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 765473875 1250 765472625 765472649
    0x10b0a0e031c0309230c0622230307180905031c06141807080a0e070b0403171c09031e030b0a0b13140a15210606051b010609090812010f 60
    0x401001c10620303038003800c860881207031402c10071079019040c425034002070a1b2740314000c8041d11030f00796101880c6640303c0c2110310030342c400790007808402081508004811940200419402c00360f01d0b001d8194000c2605039070580800042c0d1103007401c46500311108440d1152454a0410011000c0c803248018ac2c10380d5030a120190030116100a1140c0daa413903000b10000f0b80040d081141b80506403c24100b5408060a00800314042c13090289180141440014040f42c41d458011702c039003d440741d031041c483d00720411540c82c0e400b0710a05000d8510001c030030100c3c0f00d4424251020090140084c5540c0c074040e40203d18440c0003280e50804ca03000c03141d07065020202464030926212b20500f000c0c03d412a41070b00014101c500162140400d000c00c00c0603403040c0c4900c80c4441000c40343e003111240901410340c03d6400d05004025194000045569006080095002d02c00d080d681c1c00e40503002c203a0108045514140c41c401c01d000b0104083c0c040c1c20f20841c00100981da1b0382004901c0524070f8041d40c011094 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 765475125 1250 765473875 765473893
    0x603020603070c0c1e030c06020319080406020d060b07150c020c041a09190c170f0a09022106060405040b0f070c1b0305010e06010b0a0e031c030923 65
    0x3000d60000381111380309035041a1001d865000c0e1000510010b5500d2412101c1c61a0510400c10b440d80a44040c003481c0c0b0040d41460300c0e8a0701d00c11601000310058050000000c08282481995012180b4020400707005105a503620407280c0255484808140e503041e0a0402c41c1107070400300c3c00749195401e090390083c112078110508000040000e03501c1e141000c2d00c0c0304019201a259901140c1c492500c469100240d0444000c40809640761148840c08000c8000d58913802c28212a00142d0480ca126000303061a079101145280102628800651300c1401c0603140c004034038000341c2c00996a01d280f026100e994032400140401e81e001994003d113070100d4400064002c240310709000b0348c400c1e0503283c0707981c074400103442c1c1d03080200751a00c035400955008801803040c80300c2401150195503150b002000303150300d01003814009003d01d48444040003d01810990503540800c000d0f101e0078103000400207890100c007800380042c13a1154080b02c8211003120304114003045c41d2102803003640e0000203041903507 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 765476375 1250 765475125 765475127
    0x30e0f01080c090a170601260703060e0f10020c15060310020918010e0610080f01090518010203010b04051c03091203111c0801081218040b03190c0603060302060307 72
    0xc3c00104000d034210304964000518103101c990b00b4550200c005002d07201c0c9506180c0c240c0401031640001078542401504124991200000c80d441166001540040d582a15001c1c0030b05084000080c0b0b0035910402c5100415209694010b185050b40e18045804030380c2d883c41c2442810340e04603942941500b001100006000140d0024500320000800158140d6126400500e00d0360f0281c00c50440c18101d5001c00c0380c14101400b01c20003140050506542600d81007012011081050044580164403400464035a13854a64401a4085150025512582c50b0340700302e0004d40107449914441c2107090010b000030101046422100744d016540d9208082c204802c00704d0702100300701d080301040286812076501030402d20030703c480f1032032960002c80000755840000b0905401a0050f4a050b0851a0070321440d107200c004a07242640a0034200d07191107510000640104030200c41107400d4041c081d07010f000c41400c46844010240301d44901a1500e072601012403c0b01d200d408002c1d008441000030030002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 765477625 1250 765476375 765476377
    0x181734031101090b0c060708151309050309060f03090d0509060d021c09030f03110301050d02090a11040e010611070302090f0a0e0714040b030105040b06010503040825030e0f01080c 79
    0x950703041c14001c003101d0351400e108002d54444081c007a40ba400c040141f24045078844055030304040410045c410411744200084ca42c090030804890221303540c0c10160042003818002c0e02e104010040420b5203030310030452121290f0703100b12090011801502c0d004107110f801003065801c07a000252201e42022112540070303000750b00000415850800c00040250000140e004420001e0301c283d6407002da014080b400034041c1d030a40911000390346424001800962100280c0000d02a01229110025103501c05c0f244010440e07500c110301e00180c001070208000c121403c1d02812548140c0e00d64001400205481c0c1c2c84a40b02d00001b5031200382c90b40030036030010002c00016002002910006480ca4514403000d140c000c15501801d000d6003805003444940c603191162507001c038015002130050f0b103481c2d61255140d003801040d080c18084080701043c20300a024054440c00d507880e0034031003a46548904105217841da960004ca0004400c0c0700300e900f042c144001903075070720601a12020625162140d08a2603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 765478875 1250 765477625 765477653
    0x1203070525020d12230f0a260402030708010e0c0909010e0f072c0a020a120c0924200102210402030c0105040b0a18173403 54
    0x101e012044800c003607915040155079a5200d140c05000525410b20044c02043c841110030144e4804440c03620301c1013001200300ca5000d99882c444642d03441c09443d0540d14014041c0c150007071200702c20700240200c0620009280154004c60444006684d1030020600782d400f13141e0395600580100da08031105040541000f0b8110f815a0008940c01002840c081d18001d035400350506140c1c8030f058100a0b1030010310746103e810001060008004041514411181c2c8000d84458401540000c41558440c030a10b0203411181151806000d8111460f10040030845140155200b04c3c1400480800480312082c1c0800b940782192281c0031102641c1c0701c0c82400c000c81c144002041e5400b009a0084074103c880b6075011500000d801d2011400c0c107006140c60820980c1402d414410208001d10940c10709a003902c21520700c520b090703082e1402d04092440c40c4d03986a40b05250711400580d200c1d003e00400b04507a0b0441d812454003070310203400e00200c0402000d0103002011380d0b901b01c40003030000c58400182d04803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 765480125 1250 765478875 765478927
    0x810200a200f0d1d0609090a1805030703030f090b18010f0608160603060303090e04021c050609011b120e0106082d0307020609060d110a0203070512030705 68
    0xc03480001c07a9454140081c100220751680c00c07003100e1108058000440c20a01007800ca0342504124010000c64014401d0704d14091213981d1b080000786503480c40d9081840217010400008a0224080c60241e40d6604500403c40105e41841401d0026034442d10805c090f40c1c0d00701c501a0038545840c40c084810660440a1795425501c0303042031021003c40d80204802802010010141810150300c2d030701d04400d41d6044401018104001000841c0d480800c10741a01e104e0003001d84552118400a542d103540f2645850345504505a01014801c0108130144556a8071000f4080540c210407948103814a02d412400801d403034210051181c01e85901500045540d20300016060b601c8280862074486124000d88401c1159051a007141e5040020800c4681c85840118104000c50b40003031318a01a002c050740c001da90104a116803000030b604a0120559480c503216601d40c5101002512903000c0c3c5010ba56a200380406e1064444030401100d104840507a1410b040c90b151403800b80300744d410104980c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 765481375 1250 765480125 765480167
    0x3070c052505011e05040b0c0118200d0b010b0702030102070b010f15034503110c0901030b061014030c03070e100f1110060810200a 58
    0x1240421840c4400d4000c24846541c0c60300c07910b0500010070300b0060325031104903070349284115400e440d041419501580d80311200b06840e4041c20390b16a00400b0808207603403100c3c2c58911180103100c103c0030382c00d503803400c841a405481001c5105024803031415150040004480b03d00410041d40c0e000e01600c5241e100074005032816019842c5d4095030042a04801e0340e4403c410790411101c1d41880540780c0e008410b05050081450f1648442610000b1007a42c644c0c020b0900c0c0300c8414107400701c0803424002c001100703a001903101800d0041000d81100103084151242205040c950710780101c44e03034100c0e0307844540700c05c2640d120ba05019030f400d880c0c80ba000502008a030030f24108902c41019602c20a00900c2140d240d1512031001006075900f9030255025121024205044c0c2d40e02c44080c5151203c98108000c01130b501000d880c1c0f500307804001c09614645072900c046041040410700210042207060280500f858001c0c14003031903120310030107074541e441c02c101c9611a03c0c041c00005052092051084c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 765482625 1250 765481375 765481393
    0x1e08030301080f0c0307120210031d0606030d021f15050a030809030c010903050307020d050708100b090106051c0b01050409022110080a03031503050a14060601080c03070c05 76
    0x1246160800c1c0c101200d960040985034030001c0303003081844880c2030100c0050046929000741c000c1c4c45070310200041d008410f0784019448003800381d08070100e0540c800e124594000070000310280c071080103076403041c4203005400054941c00e200250410255090300c080804000c140c80003a001000d18040408058401d0a400503155440e0000c900095000701900c69480c90350508060410385c081c0760642c18800c55180c1400420310000581e10241d43c140c4625910800d2070404a1034030603e0b60041c002c84c801c0c08041c0100346034581009284800540341015103980f15601501c9902a07170300c480000c06410001d0150780380c4260440610391030181007903403406481d5040c000503039218400440604400d030800b0f912003900080040d0b4041c00090b20360441608200c041034441501c20300242c10181c60313011141611010394141d000440e44101241c070028aa440c200c5124012040c1c2c03c1c40c4e81c018000001d5aa502a10600d840342c200f07081d0092841d5940103040d9441c8050f040160740c03500c20300202c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 765483875 1250 765482625 765482639
    0x52a0106030305030106080f04080f0a0e0a0f050102060c040501020309190302040c05072006090f042304050d0c082712031c0e0319050d060303050a030609090c1e 71
    0x40ca4010714000d98a80c1e50b02e42c10444042c00b187c0c3c010701070700c40e424000d40800021a8000080d921404802419140d99914038a400c46440d883e000e40700b944030948080005011610100c6a002c6500a03020f0300c80c035035104810011a0700991041c640581c0040040359010710700b00c003c11200407801014014000d803a60081000c81d03081041013004124001400f45c02c1c080b10b080880c60b403802e054103442032400140041401800345203000d5014201a0350544800d6450f6040545014180060321042c14080075a039445000306032800c2d00c031030003032540c032140541c814420303070301c0b09604070b80700074070748580303d41002e0114a484070003000c03030b080c55054814143d540c04e01881d0340002240c01103032109100070700d40324010000b1405e0314009180010300d0194107808016610b01c00f2424044032a00d442d0300c8400e40c0c00d44203e81c1c03510750087c90000c0100c01c054003d070103003101840c0c40da0b0401086844a8024088451295000d0044000c880c020400042c0c00780203002c28059060f40300300401e540f01c1c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 765485125 1250 765483875 765483881
    0x606100c05120310090515012006091e0609030715110a02150c0a09121a0f100b030403020a2436021e1f030c080115052a01 54
    0xd10b80026103000001d010001e10180e45000192215501c00c0007070b801e000c500158050861490141400080c60311001c5034071401d050b02a000c1c004e04207840d810301d094098980c4400b04002100d107800c058459400d0b075500c000806038451850030b401189041c1241d1110801d20383e01052040742e0030380760100c46100a07594000f400c04481c0940007007002c1010744c2c5002e0b03015000180b060f16601170500c4212000b55012090700c04a805402d403ea620340c0c2c881c1061504803241c045100300c04080001484200d500d03420700544a807005a242d1700c2c4054844001e0340c4030744002e5a010340180d00540c01d0b0804035980200300340c0c1c151101c02a620110081c49034200c10b07501051100094080c01c10424504e20305000b8151050204040d6000880c8400d07900103400e001c900100740c00b03800180e40c0324088540741c1c2c0c2030360b100e505401c02c1c4409a5201801d0010081c2a15141550000e004180000b13200c4200c40b4081108130916101c080c1840f48c5541d0079400420001210021107500813070058010600b84 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 765486375 1250 765485125 765485143
    0xa0c0b0c03310e070207090b15130308070308150402030c03150f0306100f090504051c030207021f0e03010b09150a0f0305061f03030e010c08090a0825080606100c05 72
    0x10f030b4000144c40e010f400030b070500700d4962000301020b00b4413140d44516a81d2405041c03c690601c84030549860014080e4103543c00181c100903c4140001806c03420b0503001054948580c01ea00c4580e00c100310003500380811307400190340204d1500d0041c400f01d00000c03920600c0200d04100504540703140f82240c00042d10700f200070303166076150391841081408004414500c0101403c075a0409000c1d60500360340f0700d55101c4c4030050361103020000303204203034020744a9011205e40507001841c16012800300800192582c09000940001c105292561452800d041c00382c2161414003d244060a5480041c00342c0783c6c64045000340c3d440407180c800801c682c141c03162400042d40c0580020551440d101c08022840c041880400c006030031070340310410001c0e90142c0c40e10101c00007844d180802818900e00307001540a02c081c49036203c0c903c03c80c04a0644800504002c1c001c8000b40751808a00040348914480c0315a40944051030308401d002940d00d0400980700f2640d8091031410020780e480c07945038241044826 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 765487625 1250 765486375 765486389
    0x609050102071a1503011406010c08040f14010905041e0b0604080a0b040201020c010203030415020f161b0501170105100512010806010f060801140103050a020415020a0c0b0c0331 78
    0x6205125880b10680c110300b0036913009400821107000242000c11014030010881c9042220b070700700300405c0100140580e4010248d030041400c03244d0300da94200e4900c0d280e14407160f0008540e200c00003000d14080c0a03a07114902c0144001c00c4461500d4401005000c0c0e405000b034001c80c08010010307010320100f00d810919030040b00d0b00c8a030b9003031500c00281040841090141103500a0080c440440c500c0101d83e10740c0d544402c0010780d18021414181480e0060341584010032603e03498104c1031010840c1002000c0b0303035081c00000d4294851006590100078000c0d480c07905408031006020b98100410100300000310350400f181004c0c00b40c100c00300400c82c00d81211549030041001003000c07444408061014010034244401d403036045c115440c038440c0c060700e5400e0405803038102203440514141c2c12180a40240c10101c3c0300042c000002a42c1c039144160200c6001208110026680380a0740980c1c90039045d0078040c0d454240104600803003030702e070301071040d0459041e07880c254103c2e544501e001c0c5c014241 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 765488875 1250 765487625 765487673
    0x1d10030c052b0506010c02090a0509010612080a12020414040b03010209040612050606060a0f1d06030709060806030a0c12060608030307030b0102060702061510030f0c08250c060905010207 82
    0x2460302e4290944001400c00ba041c0002d07100c2500041c0c1d1a0074265502c02d41d600c40000d401e554064609024202d01c2c0e00000d0f0b0129003032850307001d00108500030005600d403070f202c01c0c3ea8446940d500d4406c900c01d600c5012105054036000c41d4107458250003c00c0049002000541440f210300005012980c55034001c104084031824110308001062005a5006004072002418080b01010141c12403004150401c1041258201c2881d5100400c180d02c000e1400540410b03100e00d070201020f000d02806010700b101040c6048002034a5140006001c11001c0d03000d1441c82072300740790071165164050f00001c112900d81e2100000704405108001840c0320b5116a41c0c0856070705ca070715001a0070400301502d04011500b0440c104625951852581005000287d07030b041e40761010004200d008003050b0003110b03181d50518481c01140b6074440d100d1402040300c0c100c42014407155240760800050444010b2000c12070035a50f40c03000c900564080128640034100151401c0500d9440024244115801e4115900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 765490125 1250 765488875 765488947
    0x11040915030c0f0303050f030c07050f0303180a020312030712090302010b0906060909060f0607140a110d11090c04030f03021b18040b2d04031d10030c05 67
    0x2154803882c001802ca1400070300340c0d80d040d910010041c3c41214403040c11005e001012542c01000c3c1021514400d41210aa0742007029034013100e43c50341d00139607030510300b28031030710310115642804610074010300d50090040482c0400356441c1002a0401801c1000384508800c03955400f160500910f884d2a10943c00041c581c02074004018542c0301c040e00c074500403081482540844c1e02c0d40c04900340c0000742100c015007207003101c1d00015994032410000078851504c442180703041c0300c400158903400e644a41c2e5840c40620610052010109a0390f4010b0414006042e016a20313007016400da0390043d0310388000b2460a0b13100e0302c1e42c0100344180711003100180d0004286d44803601030520106540001252204030701c1e900101034040803140a40003401900508001c00c04190000f00600740c0d42e0325003500c0145500a110140f81c0c1480c0817141036001c80c0440141241c0b501344d030050780400d40002802d00202c0390b11014210700030092402040d003071110402441e1161618046001080d52140700702d40c000300307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 765491375 1250 765490125 765490133
    0x3140d051801032007030318120309051f05060f09040b0114150403080c0c100210050c120118180c030f06060b0d020403020a0f05180c0d0203180c010c02131104091503 73
    0x35503c051400c80500088d160780000689040320507442506a10380425841c10a0800a09010320100d040b042a07000c01103503a44046a80c011910584d011689002204900303001d01c82080c1c0304030b50040c0340040010061011204905140b06e5000010780b1a03400041640c1c03824809030302c40e400a481c4200c0200d04490900401c0125042040c01a5400724071403a5045020b90381e9a403002c0784000c65911000003070702030704000013a5460f114114030307000400d582d102c2807010100101000700c41c14900300820f0702c50b0165441a0380340000e5118040603803480c9541c641c80c550640c000406c039540c644400002441c81c58100c06481010000030005035a43c1c0355104110303840d042039124404610034004100050340d5101d5900c04500346100040303000384c0d0b031100000300c01d108098034554401e01c00300c240b006001e600d10303c41c880c50060350201c42c503c1100d00700642d82160140c0b0025484901006000301c10941c9400c01984501c1e1b41c1c40f2036041035124999101035035241c8200410a200000007003040c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 765492625 1250 765491375 765491381
    0x1303020106121a0717070e03160f0f0905010506031527181f090305121306060915140609030a12081e04080f120a0603140d0518010320070303 62
    0x41050f043c10303860355048a16445445170024042801e01c00e00d9600c0050360384050091021485402d0076000e2035507101c078151443d50909005010300783c400400003086004032841001c1c140d840041000e8103503503c01d00715104c06052528070a030402d4030004842c83e0604010240042000240c440032401d19024103e00c0ea00c40310740011840552080c0400410340194090440300384000c4c003004649540b041c1000c1e1210322a9015240328154900200b0604286100d004101310b07103c0d840c244810340e0303102e003072009a580b040c100748012204a10108485015500c40e042d01071400b030206030400740f1942c0080d0a04114003001d8507400598180941c0b02588078a402d6841040d01100707003808030410030711001803080100010708440e40050b10b040346000c0c26090720288250449c1e0084149420385c480360203407010344030072101d00d040138081c0c06200c4c0340401c445c046080c0340c2e0b5500b0304105000b08000d00c41003024050506142d641d00040d03242e201091200a02d07a0240341800f41e42c1c68043c640203040b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 765493875 1250 765492625 765492631
    0xa05010509090a1a150d050106090c091d040212030a0203030f160912020a03080c0309040e0303011a0310090e0a03091d0601050d15080705040b040506091303020106121a 74
    0x25030011458080021310440d0600324410b03034a110241550740301d086000100554154841c1e0080e01080020b08000c815084502560b8503010f0900c41d49080b10415103101e042c40c004c0004103400380042000140c01d140b92568098001028160396142c2a000c0d241198040440000103820000c20000c510403041c000b29040500201c00c0900302a000400801800940c000c2540e007407410810302d02550780c0c00348050051740c1c2200303401c0d036500d6032004031590325030215126501483c146a0040c3d404500842500c2c1200c0946580c80710020100b1b4090105a000601d6250a47c03070190022450350b04510a42891000301d000130b141da0b42c92428040e160110560011508086048920180c94528803316030041001e08000d516410341a598401a1184805c1c0b03aa50303606207080040c0c0000c0c00600c40c41202e80a41b0204001c201c0315003800240d54080303650b541c01c84000008030725400e880c1034040c64980c0c0207100001d0282e0302e030039000e0031040c0c509005407070010b031150644541880400680350 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 765495125 1250 765493875 765493891
    0x5040e010b0c0307020d0501020906180f01020a030e0d05011107030f080a110403120e1f030c08090705011107030512040302120a2d0f0b07030e0f120a03090b0a05010509 74
    0x1c2030242c0610b10700c0d50b0f4400ca0030700034018141c8081c01300400c1025015203201c6032009281907121100004c903c0902026040310030f100340c1e112140c02086500108007a51065050b9a03150244003031300c828030a0180403110100d42e1f1399a290850203202d40100c2c041c0140300e00c0781c0c2e1012502344010700d000700380500103050126207524044680c0520b001004c216070440364040c661640c0c40802d02825204102031070a0700c0d40000c10540b04500106c442d441e100c0218100d40c03410030006040c5001142c480004607099802c0b035001c40424011980580340400a01942c80c00b00e50b14551641c0c1d85c02c2c20300318100802500500c02040520440ca040720181044448040051045501c240c60300700030240014603003060800ca405ca00c80c500c0b210060340351412601b101c0100c0c00d01d419071808501d140000c0303030928000ba20703010f00c01801c24408182189228507000003081041601c0e0708510352584112080d6080c1956520180009500e00302c4052083d00556000211585400107008002400508140c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 765496375 1250 765495125 765495127
    0x2180a05010212160c03021903212f0f030315090613050a020d0911030105010e0c04031410050901020a30050c04270c021603030509030c06040605040e010b 68
    0x254102840c082038132901c100d8114000d008030300500306152081c05940001c4d4101d040c42d080412181c1d039020801044034860643ea803a00401c01050100105e8004031000014203229900e500d045000e2440c550703c040c190342e840c1076400c0360b103068a280c0000070b03c980d00c09820100c200b140f080400c0341c41e41100c4005407040c10a614001e0001040c01d1040300c603600000744d49002041d141c1010b503040e54810016000104006550340c10642e00355500303541c5241c070a40c00d000000c26000b0a207014a07005d800070a00281c105400e41e03072401282000c80d0b00c030501620800f546c0e1014640e150007810b0054035404001070b0b0310099a80014801e080e401c459620081b04511002c0c2c058440b01e10b901c41620403518001030b69141d42c2c200161030b11540d070000f2801c0940c0400b04c00b004a8854050328194201e00c001c001c0590000d03405d036207890104100c2940340d5070070741c001c1012902580050003d02c0c0d004050303401c0619248000741c0305401540040c00011408607050044011480049000d4142c03e288a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 765497625 1250 765496375 765496393
    0xf070f090608010504020c250e090a080406050d091b050316050303041e05040c050301150926010e071701390c170a09090b01080115020f0102180a050102 67
    0xb0300351020610605000316400911000d4084003400044030440e442c2540c000c0c41c154202882900020398012089800080800310340404400680310488a900c00da18030304152910340e00703841e150001d800d5801450703168031159001500c40c0030000304a4254004141d0410700740800c0c189880c0c40314180241ca915502c0050203140d40000c152001c4035403104800d450504403500d50804003080b079200c0c5400504242c00000c40a030040003a605903955600120140c00b0000030407510030145200b00c03000ea03250034201e046289003043c14154600d0802c00003280701445401290b18109507980000301c804c1a00300001a004000c0c0030b140d42c0c440c1d8900101e403e0180d6422001594802024444042201548504100703400382512010b201e0300711100369080514920001c1d1a82d100400711000070341c5070303800450440d041e44944803510806a59900082c0c2c20b203292101c10900c24807120040d4852459801c0203038409000414104800c8030329004044c403180d0510140200c02d401c540e05541141900f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 765498875 1250 765497625 765497627
    0xc03150203061e0d051203250e010c23010f0c0c15050916060e0a1a19210902090c03010e0f070e0a060e030d03050c040e19050f070f0906 60
    0x52103000c1c2c0d15129211a0542119000a44c1c580300e004006090f4041c2e0b000c80104890200007030b40c410032070503800650320460850010019078204042c140462a411034001711942308028014070a48600540c0442e40010351a00c10000f00060000e00c0c42ea46801c0c0c3c55004223010302480950703803441d0401144011070356861b03000d07200261380850b4883e80d039800001e8002001f0800441034085021941d0312003625100000e0540c0d07108043e090182c5412240082c0754030b00540c80503031400c5407074840c50501d4494003800c100c00514400d0380381040f03600522240c03030141102042103090814040000c0c030315081d1040c40b800110080500c0300856060004120307500340e000344d43d40c1c8903011035600241303543c0b01e000540e6160501c100007904001c03518004103281d600101640360900301102100d142c42150003049043d10411245914490018003003003007a1000a40d400c1c0d004032480e10790402d890700303021100d800c850b02221041c20307140342001404003040c0c212102c050303007031000d142140c041814900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 765500125 1250 765498875 765498889
    0xc030e120a2a05070e090d050702040209010c0203011505040f0b010c080703113a1b06020409050f06131406100509040e070612140406200301030c0315020306 69
    0x80c03200240300501d012040484011185441c440c0d80301c01ea15402d811107418882d81e201c0103805006041c07150807003c200b80300d01c0004c1010b03101c000340c0c3c1c405241c103141da8280406034005000d440e040c405c0c04003e60300141e80c2806070402030483c0d0075800504900d08420001a5100b00f0341c8001c90509e0004c4850541e68044100c554081d0410912641c684061500701d8482c02c13280d20481ca503006640c4825096000f00720b10349024083c00151814100c0521116001100e1350140e07240498141c01c0440e90112287c5407010030355014840c0142807990381d040c068240e6400707c40102910100030200110f518000202c0803804200800401941c44292401142c482c030241c00389100350f154108480256104104580f410000907005200d604051400555513400358090740000c03d0107685800c60012040c454011201e82d0620080310075100da484040003058040c0c451090304a070040300d090307660401c40045000791b109001010304140740d0308203400d2501c41307903440c80b048074010014843c482d61910 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 765501375 1250 765500125 765500137
    0x2011a060a050903100912092403051b3001120209040c080d02100605100507060509070f080303160c0b0f090c0a120209010608010b0d020f0708030a0c030e12 69
    0x81003255a80180c03200185c5840c80c50b011085445040c00905820450381c030a82d0700d200f01464840003034040e12011008020310090001820244500c12000600c41c407903040355810450403410a40c0345000ca203294503c0c0e80c00428070711079100fa1150040c0790706d105206030318004210224840141e5041c11841c219071510036401134859602d00e0042820721650751020801007046600704d030851030681d08003a4503407a00c01c00540489207000c00018440c1880141c1c8140e203c502d070342e41c620b044d1b40c660b2000024031000d0000c408920401e400401c800001c040c044001e07004500065480780713416401e4000300800b40000300c00b00300300303816a80b0000712803417201070300404003105140d0b041e03503814001032070401700030300c2c3c2a4042d10400c400541d2080250716040828000e6907425011ba0701c420b42503032020350170712550504100401140780701d140c841d40541208001c200c2c07241d150400c40d89418450350010707101903000b1940e640174103840603054800c140547d810200540b9514501940d002803d0084c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 765502625 1250 765501375 765501377
    0x304050306070c211e050306031e0f160e090a0222110d06050405091c0c03021204030605180c0a06030c0c140105060112060e130f0c090c02011a060a 65
    0x34003001000c110300085102c3e1380d010300000104548509450040400015464408040c0c00710307081010490300c502c048034030a90028005084a00c2c42120402045101c440034128602400300c42948190080c000340e0070208045550529082c1401e4207442585400b82c4100813a070b1194000c0c40c0140c4030000b40e022403880003c0c100c070a803040a81c2081c05400b4642030042c0c2404005103030080b09005078040801d41d4019601048542d50340c0e1542d0b607440e10703881c4000342c00744a90706209065502c285c07000d00f030940c03007481602c200c0d032100072030304807a608035410803206c03180c4070301c03c00c4240c915a06000a51102c044000c0c040c1c00d007114040f030756501460280c00b0805450301c5100720603038001d441d0300680952010040d0340c08400e900e00d0740d008100c1500c00f10f001903030380740c0c8007600340f00e00c0c2c01030500351001c82d004032500c3e40302c101555401c613041e0101100c5030030192088802040108100343c0c010041c1c2903000c2225511000000d00b1146001d15800d00c811803c020001e0607151001501d91021355 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 765503875 1250 765502625 765502637
    0xc0c06020318011b23040909051e0d030c05070215030c0c0703051014040803071d03030d09051e0304050d050307021216050901080a020f01050d061d0702030405030607 73
    0x32a01005680007006582032042d40c2400f04a00328445040c4105032001ca95940380c008140703a40c0c40300d400449564000704040d40c1c5c14442800291011b600561105114400310f800d5500c5041c40703100030b40c00d4982101419005001404401501401081c0e00c6201500d48a8640329899002918444103024040182c59010000681300c4030705208a4000a410804842d040383e50703840c1007541ea208076401e02d52a82c0c1003660600c00d40c5403044a442c022a442051a42150794080085038140110240c0500289003003540800d40d8800740020000c1083e400c0300403440560b60308120389082544854510111005140d240c4a1040882990305032082120f04000300201030800b54554090076001a60000100c1c10b02c822041c000544889880b4504a078a07104683c0c540400908100912030800185c1051504500510700240707140c001840504019080846803004901241c0f8035420828007001041c8410800c1a440c254559128815100641c907103400d200110b1384402000d4007032001d21075 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 765505125 1250 765503875 765503881
    0xf020f0d2d05091510061101140c030402100e0607020f0a0801020a08160e0a1e03080a031a0f01140c0307060507030204091a0603151c081201090c0c060203 68
    0xc408008100841220840e44500041c42021a8010031007941d00d41040e20442d0407400300080c2000d0f603c3d100c1d40e400e96000e9503152030800c090703500703040c445c0d00100655a512040030701504010f20300750280c00d003402076649910313251050210400303401c0400c00500080d101740b80c51951702c00c41150350440d41980c500480052003404240c039400309421200c0709500100344030810341c0e4080c1d1a60711520001075520080d4410000544003844660b0900750800008141800b0a0010460b0a03c0c80680590004110f6550b5103620700282c00101c02600000c2e144c41900003c52036a028002c0465400c80e48200d943c00c0303210000c4c2801c2c181d20a4041c8007940400e4000301c0c50001d00544d19a150442c0d018040752500050007030080d4014080c808089189c00115461342d845101291b040550140c2850301c0c548510540807455003101c10810381c03024048407089901460230399014600303407282c640642c070340ca6601d403c42c400c1c1c00143c0003000311520740390280941c1a8044150781402c1d030002001a40d81d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 765506375 1250 765505125 765505151
    0x2090406030506070c0c060e030d36060e010813240f0510091b050306040204051804140303070f050306040b0907020f060c0a08220f0807060f020f0d 65
    0x100d140d00103071440c05602c0810036150b4014a10030442c500ca005c1402606440360000d482c1c40c0705d621601034041c1d00c01003004600074019000030104c00c000314100540304020000820b070340c01444100e81d040c4140072800708a0700760400e5040c000d41c942401c24100b10f02d046a502d140240090401508805d0007196070716061000000c00560000c80460a1104a5100e41d015000d0841615070707614008150340009207403200fa1003544400313070751079441d10041003801100b150150400b901543c0d000d5803c201c0002d2556611451707144036418841408a5441d0034180601c0002c0301e000018070f43d42040040240499024840c0c0e03a510b101803d1207612501c6900108001300080000705800c030f0903a80074400255000101c4000c5040c0c80411581d00303940d0f242e43e85c1d44c0c2e4080e143c00700021459810110ba04039030340604421111408040c56203c000d929160640511404241540d03400c0d400103500341400403a02644d504440200000d41c6000e20203088000d841c818010020300d00f59036100c1e20100c075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 765507625 1250 765506375 765506381
    0xf2e1115071b0b0615070b0615090406080c270a0f0207140312180c1302130b070c0501021c110c0301020a2c01050a2012040513060315020904 62
    0x1101c150040c601d000202c625200380602002e580291080310208892070002d000c1908039201c60ba8001255452901c5880503c40c80d1084540d031500400c0c5e0501c1920103e0701e82c4d00c6840014446800108000c0c00c101d4140003060f6101d015948070a0240d071940b0014114400c2d103e07410003182c0c01d000400000e0551480002e00078898014001c2000440b011f12020000001d001003805d081040340840c0c0f10307800036144c00c20414050003910b42090b0030307100c2035140074640035040032240c8d4005480c0044c00c03011b82840c01810b80010b2550140420030900b4810740c5d8550300044c01080c0010a20340003c209010312218615800c00108203540d4480c41e0351030418040d0b80d01d8818040c3c001d548800c2000c1015180b075800c0300300c0c000d0001d00d01000003504080101c1c09910381c038068559601e0b0512005044400c40c4004000c0b00d00842c0c101440c5040f803c0c03c010881034403984041c404d46031030070700003040210171341880001e0030241015801e2011442101035403440b01c400800040c0e54100c14004074003d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 765508875 1250 765507625 765507647
    0x406050703140f0f0903060a14011a130f18090c05060c1c0905120a0c060e01050c0f060414160915050603010b1315120b0f2e111507 58
    0xc3c1c003020079070300c5541e40c4032005805801411402e0300d0711a0f8075420100201c608101d0031140e54204d1000401a1480100c40d04e400800a1a01240b800740d07200280766160016900038486d82401d0003040040d00d031441c0000c0e01006055100f409a030043e5140c46024100c0c5000d014414980000e24024201d0100200c0c080200c05a40620384071104800151070f51140307100d0540902584034810640c074001240d4034040700e03441f200c0e0402c01410310404841403181442c50780d044c003000f0040c000c80104e00304560f469622051006025a00d4545054000fa001000c4e00d900980e200c02c60065504010b00440d07019106081e0300020b100b403000c510303034185655540c070a98010078000000714202c10308000502e01320061040b1a030b629952031410f000e10032410181030000400610602c0c03a1590b80d5008003440c22402054521003088150004166000340c0c00032034100c2c14080011441001c1c0e16042c03480d01c661600748820303500d048840141d2151081c884046480c0c810b0b000040d51540100d140c42c1c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 765510125 1250 765508875 765508897
    0x3141e0606120a1d070317160b0406020403170901020a141e010905011d03120a020d0204120c060e01020a020d060608250506090d060902150c0304030215040605070314 73
    0x142c50501018080050001c52649000c10f29440c40e0300000680001c0c920084a500c03841013074490205a1248220307400180d400d43e00e1040c04002440880c0034001c40343e0196004850041e90b4030b141d4581041242424220f41d07082c1d080c2070008031480c2c0e801041040ca030075080040716100e00b5224000904090f1b4401f40d00210035400c1940094081d03055201c47e210504c110020444015000b4210081707a05400c42c001c2c03680d208000c107a80c03008140345107503000281b00c0009820f02262040c1d000991300a600020b0b00054580040006c3c031540c20900340007440c3c1c0d403c0401180e12000300003510307601c410720080d0090900942d00000c1040380ea10000092001c402070718044001005204044040c480e0294888800c5000100d0949001421030300303001c0000f010054050140d0703030b8680240032004070a980c0001d03e10706c4517500e0404880208481114070000d5a0b48606520410100c01d010041080c14944148428000660440120f030404c58150030120318010121542648a1080a400c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 765511375 1250 765510125 765510157
    0x60d02030d020d12051005060a0c0206071a1608011a12090c10030c0801060309050102090312040f270203090a1b0e090102030910021c0501080303010603141e0606 71
    0x408442d0702050b011001c1e4541ea54609840607070300640c0d801d032401650b0601295003025000c0000b494520000c10b0844864146407a40030744039000605141c10004080d90080c0e4001c1199585e04e040d00e100c0ca80c40f2100340c00303480203110300580003000b10805010341e00d40c1000d0301189a83c1744c036881d41628414011040484241d1078044040f0b6100d41140d80a28045e030902215540e15600070f01503e204211280c1c0c807904c4c03980c0303040d03021805400300510640b081c2d542005001801d84007403000058920070810244d41e12450701003050f0350042c0560001010f0f50000018241c940900400b110401c20101b0000d070f204e80f036803050030b8240030708130300018215510f0b0b400e00003800000000003022250411444c500341d64400c3c0800c0d01740d2004499040c450340000d9260394921026a018000c0c50309580030400d0301c2068000300d81c048681c03e030040060b0341c0c0007100401c50710b1f0b031600641190240d040b8824400c0d05117100c074501c0982c00c00345104215105130700020b940780c4ae8903003541c3c103441010f2008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 765512625 1250 765511375 765511393
    0xa03021203130221010e15060d02060f0d05101703040b030c040e0103030f020c10020a020103090c0915030b060f24211e01080a03080c0c070b0c01061208030609060d0203 74
    0x2203c040944d0341201e22942040142e040340c11002c035000c10700300516400d00b100eaa0b81d100c100035001c40f900000300c0e84054140218049074a241e4041d00c0720075900040080c041c101401c10901c0e02e0025403265101c041d8229074680342060200940d400c45002c028665143e07110ba035465004c5000701e801801460b000c170b0000106040e40812071036518407460702503c800d9560b1301c3c00e1051000c541820240541e0010302c500c00154442d17400b00200602585040c0c10003600c4184500c241c1d82c44c420343ca03480c035041100034002d2141900c401070700940308848a51301406010b011800400304082070400c003041d83d01060070205541c10031941004800039410303020f051010302103005ca560503581110300b026001c25000c5184501c40d10ba505823103111004118500c090b030340c12111080c1c02055910400003e1194406810080284402030400006129100c441c0d2044207400c41e580caa008240e50903c40034900f02150464040f80c0d0015400d0361140c0e1701e0387c3d0310004140c5d115881203000303405106550003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 765513875 1250 765512625 765512659
    0x1605070e07271214070e090d1215060f0203040510111b03030d1d0601030501051806070903020f0117040b090706030b030715140c03040501030e0a030212031302 70
    0x3200301880805a40752625051605040c2d030507040340d000e00c109480d40786400b240410f400c01a000140c04000d011282032a4135100012102c040550301c0280c1c603400721044a00084e0000c4103608280c85c100b004005161005106000c501a41e11504050122a5811003d61403080c0210ba024100141c4016503044241d04010402042d11105e5151030048144d0708041c80091104201071001c000e006504080f13054281c0c030024840406401c2c0c800350300302c610000e0160300b8072405000318096000024140b1b401d0020382018031140c5c107803280940207102001489508580d860085e603805494a44488c01ca600044e1807581c00100030032009540d00b8100300401003082001071141e038512060303490040d951001a02034890304981d244c1d068001c05024499041003a01ca2180c42070a0300d404802e0700044840d03d81194002220003040d600001000c0c403655800d4022940081d03000c0e0018000381e01c990710000c2d29501010030550342148000042400c40c02c0b88240c4408098004090b4011010407040c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 765515125 1250 765513875 765513887
    0xd0309090203090a021003051303031802090124081303120f0207120306271802130504050120030f1b0a052d0d0902060d020301090b0a050907051605070e07 68
    0xc0120306c03901045c0202e00003035209008180c0070707000442e07030302940006c41c2d075041e00a441038941d156208004044404090b035a600c204600800402d4100c041a10140c0d002c54220200c2803034010500140714180255180c0701805030000c00d8051a08012241e80d90500320007501c42c000c2d401501c5400494508144102801d01d01c03080b1106032810489995220491a42020740b0302c009400b66288031603905481e2120b0704190341004003c150750302004090b5000815440602c1078005a80342c0d20340c100700402078248a80b0100420881007161812070198880466100041400705480203400205000410100852540441400c0c80e075480c1c5110070340062071500083d450540c07082c108004a442c0c8410861070108204400f0602031405195403a400c000d41402681240c12400070010407252032210301c050350280c040c2001c00b0a02c421040100b08485001d500300c1d0744101d901800380300c0100c0e0080120303452881c0d0000580e06110040c104141000d0840d80041004580c5a040040c843d901c60 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 765516375 1250 765515125 765515143
    0x10f1109090108060601020703060e030c0607260408160204060506160c0b160206030415090f0201080703050603030322020a0305070e07020d021506130e1c0806090103020d030909020309 81
    0x90752805141c0c0c0d0f030b003180c940d45590aa84a90240c0c10180c0d003440414030681050b04d03091805c0b01202d14145042440c1898100101c400030300181442c141161181905400207a40480c1c611007002941403645070800e052050307090880c0b2215002105e00d08548880e04800d006040003802c05450b09401c0486420b6054500070844490714281b01c04288907400c2021703640035075480d0310f0302c5c0e082245079030a01889510180c410b0b110105d10000301700c408040c0c1e0143c40b0b8080c1c8a60910903288a1510015025040217000d8200b03040c00c00c4100481d0f030f2000429680e0190a0702c501401c020f58440052a20920b1445c0281d00000b0005012050120014501e030848040d9010600b0565032007804a0300d800050741540016040003603075240315a425a81c107a0400c1e001005480310048040d040c0c0304840c1d00100084442e000703507040111428407a490820804801d0800192a00e464400500c0c4070720140130080c4110f80050505090510402c0f108003e0f0240342c1045681c4e0620884455441c4020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 765517625 1250 765516375 765516379
    0x140406050a140103150c0216090c140304020d06150b120402120303130308060114071a0717010905072703051903020319030209040f0f0506060307120e010f1109 70
    0x20070807240050708520315504882d00000c03c0c1143c5010246880090956611b20304114402d41d03c6603602c00c400c0103c2d100080c01c8102c4000381c0c2044100020706102101d20406440d2003040c070070000581c40c0d03a041d4200441d4407030340001d0288816461182c00040303e8000e041d400300b0118415031004005100706010b20b0085840c80321442d080d02d0125a6884101c81030943c03004829401c00010b40104800d0ba0401e80504109091606080880004d030300030a10584410705c045400b060940e0003c000550004518a40043c2d00c1c3c0d41406420582001841034114140d562800103155500c01ca820381c0c1c00c0e03145060f03c0d4003091420900d00900ea6200c0c00296403601812103005442e40c1d80c221440b294a905402444c2055440b4800780000b40c14096144107043c0c0030030103110a03650711b00c5000494801c94200007401c01480d4280300403154000c01c0180204030400030b01c4152900700400c01028000204045281e1001c941d449002d40345500c01d41c08903074101045802038201c00d802901c124001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 765518875 1250 765517625 765517631
    0x3070e032118040603030c060507260f0c04060207032a030812090312060d0302150712050a0b03190c09060e010302130c0f05160b09071d0103110f0301140406050a 71
    0x4450b003040200d03109480010042000b503041100021038640080354001c2d680c2c1000c050780600740c00c8508040000440107500c20501404201840d458040344580190f48951503504060412002955a040d24040a081440e150000282104d0080c1181e038141003440d61301800690759140982960304603c4020528050680008407440c1c00081540c1c448580c03802c1000a50b1100c0090007640c0003005000d9007103000301131071002035030340a400b41ca014010941d200048000854049412101d0240041513106d044c811025001d58000a1031403120020021440504451b46440c1c80cac840324903130280800c103003007800006e0000c10010750700313040b01e00036075280c5051424092030108071a500c49440c40415250030100c0c03500c912407c082c0c9101c106c051a0000f0040311503c0d128800c2d8411251441903620024092021000c490364206402054081002d00c9505580d182d040d000702e541000383c0600d801c40f911951603030303003504a0102904141c00c4402903040074242a070241c40110359000075141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 765520125 1250 765518875 765518917
    0x50909010b030c040b07030e04050f0601090b091003180c030515010b120103030e03030d020c0f07081203130f02040e01050a1811060903010207140c03061b03070e0321 73
    0x30480701100e02ca510001207803482c290805a0030b6005402c000e0045d4100840100034007401c0c1c031a0301c2500c0c040c0040c120585802e140160004001c1410350b0000082d88909000c501081c1e214010704820103441e605000c952900030840700c2031a03100342039000d082c60521400c000f0502001052221000422a011600580c0c85e1600b1880d0f61080c0400c811000c2c10004c01040482e1050071000700301d4074018182e91030404600d00d4202a80c002009040c01034001c80b01490305003804000000013460848037074480c1c00040946c205650200408885010001404180c00c0104061810302856030081c420881c041702c1c06900350003000c003201d408020340d187c1118100080491118000c14036404200007180800311000c1c81a60f801c41c5c1c22032078040d0340034080d8100040c00c00d60b003061190364a200904069055200b01840c0c0240030303120310940380c0d07417140b00c01c0c00c1c0c1c001c0812603034050510300780290004000400b0914000782010310020450781c0c0c104140812840303c00402801000703070030710072441c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 765521375 1250 765520125 765520139
    0x1060c0501060b0301080a060b062115010201110d09020f090916050f0604052205090f0c0103020717070201021f0605010201140609070c0c03050a0b040203011d071e090c05090901 78
    0x2c4401c1c046c9040d903601c100d0800780058176a03045079444a5014011509048805804605030a1002c004495a41440040081c0b044440e0444c86041c0c0091009008d0304040e83e0750340d0b50030300c59030021848190b11040701c04259142d4000140e460040900700e10341900c0c0146140e6101d42c080c48044600e940d1039280001d0030700d010746146a042d9401402d1925140c5040c4c03c00803404d00150181a822510f8100c0f80c0b802c1880d88660382c800d60b00280605000c00380782d0072490502c031a61b0b10840c1458070600c019804954080344400d10711241035a8140d540d801400184c2c5003034110f0401c4200a620307070340d6030043c079021500100304403442078009101d02d51815540d200c18000880320a6000100c503030020303841d01e00c41c40502000354064860010010f480f0b49a1304d0402103040d41c1a40c038800b00d1021b20003141402d104503940c210451503082c505a0040b45010303200c100c239101d080c0210905150740b4600d00320212600006100820b07040010908480c4080c0c26504014812441004403c00004160b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 765522625 1250 765521375 765521377
    0x70b0703050f070f08161103040e010f120807020405040320071806030803073506130c090512010e01050906160219080f090301020d0e0c01030903050910030905030301060c0501060b 79
    0x10134010380720b440f01c130f0751407080000b145002c0300ca544c5e0030400d403068000310180d0709000034000750020a041420301d60500070215407a40c02a4030408800210482401c0464400410760b42c10342c0c1c0c122404101364a680c101120307000b040038080d0400507a15040d1103c1d44e50005405803c698026010140c00e010107010303075085a00350710000d40725600400028890510407500e024004111500d10030586600d01e03a030381d1002c002451082c1c100c05141c410b102880c42d044480d8040c07003011400601140d001140010204889072140b10b02803608580c54011103002904580403da03006802005030340303040c40419641d21015036840034501d18003690030103540d10100b0100c20b0b114041e803041004a1180e525000302c2d41c0100b0803104010401c0c844044181d82c280014070012802060214400c03203220315850600c1d408001e44c80c1030515100c94480026008801c0d16042107080b0b40c084000954500c040e40508111000280240000030004c02c11a8000340100c1c0c116001d54020040241c0b91041d002c12 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 765523875 1250 765522625 765522647
    0x120c02030301050d082209110f0d0b1c20031c0e0d1e020f03030a0e040b030109050304081b010f0e1e0307080106091103100317070b0703050f07 63
    0x140c0081005000c64200186042e5500c0d11801d901882c002c141104035164562403d00d07200c2c01000301d10304000134000d9005d11078000c14182e0601e450107001c0350040038503202d11803103070f9956500c0e1003602c00140d1b00c1c1d04080d0004003000001042210031498141c07070040c2282e030110500004600c40240034100080d18001f901c420503003124004c24142015141050005a9a039009200c80f5100c8000381ca80c030820803c00e83e058078140d060351421f1040002c81031040740f803180203900502c03048620903401641c61000c25015100003409850303203c04a40034255030500034106110015000450490000f640e0450001c0355685c2c0300d620281d43d0044659070310350000740d030014100c1120b0041c03a2400d0b21000c84024610303180b0308500009000864140040c590140009035519102008040018000c0001b00750341c0c40b01e42c03451880c001e8510503203003000f0701010303100b041e2141c0b06182e11a0481c088800b032030b0304140c040c5c00500c0c001c41c009000c0e1004480040f440307102d08020400d402c4c01140360420f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 765525125 1250 765523875 765523877
    0x6031312180b311205250302010e1225031a0106180e011419081c020708060a090206040905040c1503180305090109030f052508030409090c170706120c 66
    0x140c58140d000942d4000981d055415008140d80c4100351400b041c06e2141640c000b0700c2040ca0f8a2840c000500305c1000b003502103014107a1401c000115000103c0da00b0000180320503206c43d144054074400c1c2039643c007500000c144103030300b0442120b8096217600c4141200c02c5a42c408070b00314441048440b25040510400030203511900c01401380c0761a030307205070420500140402450b1844056040140f602c9076000da210341c0c001c41400c001162040031855909039050000704481490030310166601d40e0000d020820281e640c400c400c04543c1d400c2c1c1100e000b424200700600290400f802c1003119101203101d280010b01d059000420864000e00681041c2c091001403a4401c80958600380d9155000c148940e04100a14034007000213908507415000d0380740144020f000940e406000500c80d03001c14003d007005129000410172500c8030000455082c1d0300440008110048240b40c40031201d4070702d4008400c0711090250f800c42c0d0410008080c02224407541c2c8441d249050110a002100c1140719004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 765526375 1250 765525125 765525217
    0xd050c12040308060d02100801090e070e06120a080a02010203060a05040c1704020f1804060c09050d200a18050c031e1b0f130506031312180b 62
    0x9804079020f060400d03030106000e4a050a43d410700d900092140c00e90868180100328060010b000100680c07041491081c44240180b02c0e00d403c2104c030004900b40102454071420340181c948076010418041e102e151a882045c5544496400d180603010b034200b210344501840ca0781200040d10710b09401020307070a98464403031000c202d100c01d001491041008000740d8001d00c650040c072400d51a0b0b01500e842005123010040d069050900e025415600b42c1c3c1c03456070030064450814060742c0d4410722030aa060398040382c10580c0703180f961024003051583d04022680401ca2810001d01c0341c0f1180f00248406003d20380030409170341d84030100100c600041d0741034060440d042c94501e45e001380091916030410101032011010006a2000d0340007540000c2112a4071a4003182c58180c034600d640071031002d014100d941a00394981001d1804d8800c10500014104c16803522176a0880c6002380030940d03e18091252100c0d0543e12290955120f61021800c01240900f52261514010b54000e90f2031524075458692 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 765527625 1250 765526375 765526381
    0x30809030f040e040501060806010807170a08030f07120501030b0405060901050c0a050903030f031807080c011205060f0d06020406020c030a11090c1308060411040c090302010f0504050a08030d050c12 87
    0x20f40d0303110b000500840309076517102c40104021401308502ea00030003480c001050301508096001d00c0c0309500d500c09400b140d01c8012140b000941c0310081d681e01030100b0081d074500341c0e0b0b21441201d49030414005100d00e20b0ad03100010060200044c00c81d031185004a04444c10741e25420081822554211080d00c404e603400c0c4040b04003076106100520091100604503810a40040040382007544250382000040540c146500041c030002d0104800411a01c1d0103410a43e02100c0060115284da000701103925585000280a560b103603c0044c0394201e000d40202c41035649468a2002984035009040141c8510b02e4000a0f51400040f00710341194030845000028015606003c00c15001419a60b0b41c4a001e1101c000864142c1b1000b030000c042100041209041c54100411920b40198285009034240140d45604a0304640d201040b00d9080c80c00e640500e001d03420848a9000d2504466401440b240000404040c000058020400e4030641003150742c40700342c070b400032610a503200c40181d00313450800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 765528875 1250 765527625 765527639
    0x20306010b0f0f030f060a080a0305090d0609080a17060406061e170412143912040f0f03020306041b1701021206010503100306050a0209040612030809030f04 69
    0x1500c00c082c0c8501c002828a0020000b100c49504119020400d03019038004000061a188000d00010216540507000340c079107503107005080c0d100b00c14045004904215060040040540c0401c20342030f0010910758443c810a940200b40c141c5608400d40000221000700e280d510301841504110386480d240c0300c0e201d600c400e02e048904071020006006109144042203081d05013407204a00c03861164a00c0042c2c81056507000d0001c941d240b4040b03440000c103128444905c5514110590702d44450940c034400e00e0804401c1310b001966006078100f43d80074600c2d440e0404080c042c06441a2001d41c1d00030f522103500ca680200c0300507010306c00a98194007a001043c00f040780e50103d00c0441d03407502c4002c10059196000d03100c9413048020780241d40e07035000a00b0b8140c50041d1040c540c0222007403034030625506003d1040d40610a00e03020203807080e81e8590204000b40c0403070b4122030031042c02a109000696644941c0340c4600480c903400e5011a4004000954410000c02100c88025404200500f01818083c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 765530125 1250 765528875 765528877
    0x2030909040c0f0308030f0703060608010311131d1207020609101e0c0b1324020913021312021f0e0a0b0d0c030e0c2b030804170304020306010b 63
    0x401502d5800a6039404201050080c041a02840c0903600c3c0a41d641840645139046410080c81075080618080c0c080c0900c5601031401070460303401c50a4203903c2240400003442d0105001c41c0d021070b480c0340c0703261400b1403103a003040c5249010f408002e440035500c1c4400a44241c4c070512030029407251040012001c18a80f050900e41101c1742e03481c1007041082001080ca6102e80303040e01810114004509190410002070200b540c0018061502402d500f4141c0d2000310284d00700c41d00340d45d5400c4881c006091810154152852004020103030007101000303120000c000d5109110f4090030044000020032150501d20703100000541c060305070040410a004082c1c1c0a43c1e44c5600392040007000c0540c3d0100f55101c00056001e0a65241802d9035000302c41241001c03208130580f41020b00d81003031b0740e0200000010400c1d8078075107000e4a01c01e2107800d04041400300701510020041c807456031090540103059112400511440c49110900c012030f030400d003882114002103800940c50351002e0b005000d91407003c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 765531375 1250 765530125 765530131
    0x415050c0307050109212303090c0603040f0c0b0f031b0705010c111b011707050f04080616300219030e060a201309060b070213060602030909 62
    0x14060780d00b003940301d6868509440e009542500c00c24640d00100ba01304c0f0030f004c55422022602e0410034043e181104050281820480ca815249100800041c90118040c003600c40740e0a40185015503902d8030b490503440d45482040d080c0d13100c1c1c0c9401000314800310b0441c01c58070b8a000c2140e0107411b540e201403050711840401810028420010b02074940003610901130800c40716165104d0b0060206042c4019103400d5407200c5c2422104201824492240d1f04030021000803000c0070039440781035503601e10a80d0588101d203504400361000140029100a020900b1401040300f20a01405045d041c04221641c140c0030350310300d03074461141e15166514054540500880303065480090304159143c5580c0081c40c8284c910b11002c2502c0e00c00140d030ba034030b003400b40710780c880d855400400040004c903a016940b0480c0a8042c58000400102c0c904d0030f00c0400b540c0c100078070031200240102d5454640e0050540c2055000303d0250007007501d03a141700d001c00d014020a9400d40c3d4019800c03c1c1036101007000081001e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 765532625 1250 765531375 765531397
    0x106090b07030c0210030203060f0306011a07290702100203010b0d020c0c041d011103090a030c030909150e1b0a0c020d02060a0207030b09060402100c151406011202041505 75
    0x40244010b0305e483e4485040819151030040e20f80c6081000d0250740821494a9442908000010f000056012208007582070812644075205e00f41c0c0d01c0c00c1d4500d051081008010b00b03900c043c030420140740d0090081d00c600c03010f50030b4520307070508407000300180e02007030080c3c4510820030300c088507410a2a81c080d043e603400300f004558400c440308000c94100c5407511201c243d01c0d0303000c000c40560884240110207040c1c90b621215803840c90700822071501ea5089500060030001120080018148580c100e84003800c0c0381ca00400111352040d1b071001c0d13070f804180703c0c86070268851000907100040b4106450b0811000b910654680145940100c61035080f100040b07910900702200e401c003503120701003d06000d0465800030200b290450515040301c2c02c004208070620b5019404000050700c1d80007881c0d46c42d011501349401150901d02e040c41440705000081906c0714a0440c41d8100c600e40c0c103e42c08c0c0940c000fa00e401403410250781c01a4180d03c01e50040300350503a0b00304a1100b4151060000303082030504 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 765533875 1250 765532625 765532637
    0xb06060a0509120102131e090203062d010e0102030313060e010204030f0f2303040603021c0c02060612010c08130f0506090a0b0a0216060f0f090804150203030106090b0703 75
    0x1040001032400c0007031140b42c29442e076002c69108500c1b80400148409005550b0032042c1110f0401010401da601a01604607896004800f02c1c80f140c0361850064119000f0b02241841e11070140855130480d580402c400b4009101090114180e50020044900620380b050f403200881e10f168650030058001e02c829203030650b500300f1000000c80c08814034131881620a04030015661098104101028204a400f040c0401e200141c94448a03001040f0b07030840d411803c000d80c980400e000742c019164203243e2480b445908101c2c8000103030354045002440390600310b45400e40d00c4130354991039080360303070b000401c40100f000100458492044d40200703100d00c62040e8150f074080034047c0d80b4603003800d0040d2404800c540c0032440b94000c00142803280f86d0711610b09181182411000325410b62003440d01040600011b55842c0940b580c030001d5008062308980c1c0801c20f220241251511400b154050700c10201c100d642c0344c00740d003056403002c8202e9040701d2295403500318050404202070100c0c0e00080c001c078103100f5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 765535125 1250 765533875 765533887
    0xc0b130f030f1e0c1b0503071701090605150907020f15132913020f0d0f120c0308060405130201050c100510050301230a021c0603050c011b0b06060a05 66
    0xc103031100101010a0b980c1c2d1904110041d15240c0d2050105e003030204030502400b83d0600982c1c900240046c00c030713180c050020003e07a030312402c071500400074240c0282400341010308011580d00109c003e134440d050241d070300e0001543c54090803a03ca540160043e00660800d0102e00c2844c2c00c2103000581110419402092086080d954a0070043c021841d100610b80044c2c404590075901498440d80503440c8412440601410b5000540c01c51550f80c04600c1100c1c0c0103220030510003941d40c1c2c10420f5510a85082405010340c1d800b400141c40c0010440020f2050320004030541828050507015144410410b4500040d560054420740c1024200c8a158030609a0f01c03490042e840c000c0e90301030082d1b0800082e140b07041c20149420b540c040c0725400d00d400030060038044141001120590b1064141800589540c05606480030408a80e800c62800604004000c024001c01240f00310448070241c90b403100c5c1d0505031080041c00b02c1c00007006407040301502d0018100c1d00b8058000d007003141151402c5881c040d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 765536375 1250 765535125 765535157
    0x10090b060c01140f011a03040b090f070605030a1104180b18010f03030e03011a01082208040603051602060604091509260c0c04110c0d0c0b130f030f 65
    0x31103d01020a000700c0100c14030003c4030340f4150321800b62030020301d14080d0030460102c0c1c510910000e8801420700b045032001664414081c410520b01111180030344603c2e6603030f16030003401d540007a11174104c131624101e680045003840c82d003200d04542c405120760031099041161100100b0182c40e959801507500c065049a04548404c03890203405404100070429080d82402802c034042101660b000303078581103215111080c100c9466120300000d03e8440318560300c12040300058001c9031141c01d401116400c80c181080011400360081d1a42c50b80c0c100004d41e02c0030128114107040644010241e0000d5010032020b0509401050b03032607000d110002e0b45204110006022142030b458150350206103003c015000700d400f100181b0401242c3c81000d410400188002ea80354201403841c40c0c4110741d2100e000703280384118010b84d45013609c130400396010329180c04001703031081c1442c403070448111400c4000101d01810030b08105408503048404d02c1c16155181c0d4080d285c3d44c031107040d1035050190800c00c071941a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 765537625 1250 765536375 765536381
    0xa3804050607020114190509120d201204030e0f210c030622020325031205070309170a120203090901050a060e0d14030a031b0810090b060c01 62
    0x1851180d4010011480d0020001303003124101e10281e210307035008006006d002c00380c08a1460b111640c0310800100340c0c6a6985217441c00451000798170700e011010640b0207118002d5071141c2040443c80e0503d0250040021065005200b85207000e4030030030806000c40c0200b0f200c3e140780d2040301006400004a07420000c000b450003c02d030914038150b1810b145c1440c190341d10030702050104c4a0b05400800e10fa05003485200c80c8200c401d010540000003801824040d03640401034802c1903a550300406030450004141c0b03404400d2a07000c1a120494030b008560300c00340c81041111815a01039545042c143d00301040c01d81107500449020482d0b104000e109008181214440c6140503599001156540041002e0140d007810590040348180c0900104100458008e0a109481b0704100c48444042c00549404230030002c1c841e59804451002150310445c19405921010b00c01480000142d1451001c180444592600300c0d02c40e00e00c1c101a807800c00040805800c2050092001030880b0304144901c00b4490071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 765538875 1250 765537625 765537631
    0x1b070203071211010801210f1506030215030c0d020c031c1e060b07030c0c23210c0f0411030a0902040507080103110105070218071d01020a38 62
    0x34089a07010040c2c200030410b03542c5400c500003820001100d615044078240000392440c8015800405042c000c0c1c10040741d24060111607038080d0645011418001405000f003003d03000813400ba0540f50602c42038041c0010035603119100010a803031901060a240c42c01079000440d0045942c07100740a0300c140601c0d698064041c0c445050310004a01c204039590307a03581109109082e0039030380f40010612440c401c007411129032913014206035080a40500d03000d2040102c2e0380c03203c2214540080c0c040c60285808020401070341c4100c44061040321103880c50650004410500346403079202d8855200103083c5520304000c10000200000b0380c0400c90350340305070740e580104d40c001c00c2a035071100d20504602d8144642d035040300d468900407036158150350700c0b840c0d440b05c0240c80c0c5041c00400700b504011561072030800361345001d44100150704c1d03060405010300040b100c0c104000c003030000c1000d00d1045510000c0c08049083d003100241030396040d030350a0a03c9070013244150741200d80c50300d00d105141920a500c1280 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 765540125 1250 765538875 765538889
    0x1270906051b0906040306090c0f0b04080114280e1b0307080c030703080d0f110733021321050c040b0612070c170a0e0a05091b07020307 60
    0x41d50b8505014206102c000c1c00c03049254040041c040c2400030707150031068070b090321341c0407034000f80000f000e007000c02c0b00102c2e960149080c1e14040d07001055445030400a07104480e00003000348803000c0004501906901f0071502c2a900248071003413581e00010002c10701074840540b190008810740410007450600c03030840d1030003000d00b00c8908103801a083c10000c50f80200142d0004d4a528402407000039141c103484d100c0609041d401107240074400c80d8941c019440030407520704c1040551414407540c00d41d81c0100c08103803541e83e18917600805100030310560140e03450b407028850310000d000c104000000e4002c0800740c0040c88040301d01203000000741000d10082d00d80d485a21140f0003035440c02924299820440c00c4c019420034160445545034042a100b04150f07002100c08950380d4014120781429440002800070200e480746605c03c0c40180703008044001a0303580e2010494860b80500521007100d200c0c103a086080500001e00d06034140d80d500c01a00040b0020381c2c54822190006460442c4640201d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 765541375 1250 765540125 765540131
    0x20618270c0717070330200d0c030902030d2f12070203100603081b010204031a250906110d09050f04240609061701270906 54
    0x401044011008690007a48201032030b1601c07540ea6103c203000300d803c0f00402035008002c503680081501650300d454440d01a03107009840020100119011360011010b07070700313100d89001c07165206003a5212001100189040d000c0b40713850290080a0010f1403072010b070384101070b43c3d101c0780c20041e0b8050100100682c11039448a00121482c2a20071410b061178009000064080c40b052806841c045420703032407040442d00e0b25490780818000b290072300b01200c28150010b440c0003004030802a1f044080c1c01400001200e00002d0f003400395100b4200d20039400003400110701d03110703101c29004104003800e50182071a481c1c5040724120255204441c174417004802c0200311564028840c0c2a0b0100b05001800c0580700140518103802c1d00240411105014090007100ca48405818684407508560840040c650042c5400e40300c04818110610180c001c50740020124400001e0340c074820300c40031000109100a48a00380d283c418100c10314240100841081441d507a0400020310b5540714407001c26000320004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 765542625 1250 765541375 765541429
    0xd0e1203161a01061b06110c0601030c0609080606211005042006121506040315050108010c0801120c0e0a0e1513061a03010c120c0c0f020618 62
    0x1602ca111441490604030020010884a9445030012410640d0301042d1800034900b41410350240506030440300c0c90105c0000c040c074a042c80041c28038104d0303006501c4891841e48a4800700c840024500ca040e900740e001e0030100f02d0500e42000312600a4042c008000020584e0210840c105068613a0880c09103036124200030078040b004030195844000d00c1181c1a40400140020f0300700c4c0214200d000e0942070140020304107e41411038501c1b00b40c001800e03c0d4465940b03140140b0105091700080803050f09100000950b4a03050285064508180c1c848449a0b828400000c4440c2c1066106036128031410070001803148661046034000c0b04d01c2d1001054410482801502e004504054078048482460400900544c00c0c107001c0805540524049050b034105400c503901183e1451046605500e00041005c2c01740d04100307500f01074400c900b001d1042c070240346c105840c1e081840101920051b1010400001860100001e220403410384210b82e20408194001c100d54281941c040302c1c540c1e00000301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 765543875 1250 765542625 765542633
    0xf0d060b13050d020d080a0c060515040f020301050901030213020d0204031103061302061606061503090506070507150203040305120c091309020f0405180105070906030c03020c0d0e120316 82
    0x24001402c000d4440040d405580e03030102c1e1140480c00006095a400400d251640511034110008003513000b038000c1c485410030000c080c69441041e060148150b00c1e104803581c080815000342c0703048800c01000c0c00d0103a86990207225031507c0030b40d18002c14580c2042000c42004480c03024001550091000320364550b0840141441c000c8044d040c000da80d11441c05107401a6540821198080300c40300d01040d58081a10709000078020780d404c035507000900052113111181d8544d01160405000e0011100e150720b502100340d03500d101e0300318080c106000140046810010b60740045802521078680b880c54a011151800d0030418240c030b04c3c107800d030000034050181d49000880c1510340300c6403003030030130580d000d95002030410040c003102d407801183c80300000350380010042c21003120b8040c4035000740010b15001800800c0300102e4007410001c2454114190252486071080d100450361030801048410f1141005440d1414120700f010780c003a464030741d0603203804000e1000d400c00c16480004400d2410032490 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 765545125 1250 765543875 765543907
    0xf0a020934090806160302090406180207060b09010f03030f140a11071a0d0513050a030509010306060c032705040c030515040b060a08040503090a031112011a060f0d060b 74
    0x31041020742d002da014000140030b070140c8505c1c00c04290400580d1680c449000c20090401239001a4481761b020f000c42c403015006400a2600340d10601d400c10072000c0c0300c0f081103a025070a0051200c1401181d80c14800640500e0001c08110900d00780f070003140212030604482a4000c509420010f0060b1034081ea0b803403010084800980b1a001c560004007014041c1e5603003d0003000c507943e00c9544c0701e0002c034130075000e0f001d0400c20494101e01521400f91240c2805040382d07001d5154240000d02e420000a003c510401c07600c01203e505550b07403198100d8210043e01c04100c0c21207014403c800d200800211940c0b00e10038a0344c0c0c1501c680703010400d850010509501800c00045141c0500d040204d41103140c1c0c2c0b96000c407030511429060002c0e03cad89540c00c0080c0340d8090300584070740000d0058404418420703501602c0003c0c690883d0040540344500059038203030b070091000782c1d400d80e15690b036504461506a0250440030201010242000c80b80c80a840a03912141e01c0705002c0040003c1a540031100c2c01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 765546375 1250 765545125 765545129
    0x809031006080a061a0424060215070f140a020a05060a0510060807030605130204051c020604090c020307050303010f05131503081605060f16020f0a02093409 69
    0x5031080068501e40380526486107040e40c0c000382959940c5443c001e0030060100890303041040a401006140c2c00c0600d6050701200030700061f5092100d02d40009155480083c00c3c080d003803507910700d20000d03444075032054031040c00110180c4280402101185c5074038031488083d01d41c070032169000384681c0c142ea0410a081c503a000c1d02000c0d40900b01000c011010014081180440e001d0b441e05030f000b070741e032580110000c06483e00032035440440f8030403843e030341d060640180007a610120303451a81c11078030842040e40311030407280003500254140020045804d10394000b00006090b40180d0307281221569500e805c640c0241c0001c07000c0c41550000b80b11508100d00000c1f450100582c0030442e103442e076a40c4840c4c03081c0340d01c8010007801340050903d50440c5500505024590f00900f2544035043c80b00511140c410112147c140e9940c81d804030742d030310510005444286541c843c02514013500031380c0a001c07098400911500044200010b034038510b010a09000056508081c01c2045881c070f02e50000f021440d091b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 765547625 1250 765546375 765546403
    0x70b160f02150714160c051c170c011e1a1801030b060a05030a0c2c0c07170d0e0c04050f0a0506040b04020a08150907080a09030504030b04080903 64
    0x3900d00c060800c000b0b1000c2e40c0d0007601604001410a03c20205203010780700341d2003916501411011444c0802c0041d91100040d82c4040319501541c0b94101d444820381035080c4400307070040d0324003c4076060801d8108020107900c451100089010710b60040c28070240b402030009031160320b0340d074001a594061444110407204604569400f00507005071501d002910042c0030283c0380441041c081801aa68608504020074000d4241e03200c0b1b6260303080030300c41d1031860312400449512408600b000101440342c00740390051260504000790700e5004280115402a14084502288844020010b04100c030060310964404080202c0d03022040030317540c1d08021040c081c050040341000d050000480ca03000720355a201c03110080c0065941d8802c000a4041c2030304648c0b0382d03042480060300c16649944406d003070b0300c100401c1c10442a010809424031000b03d9044039130400149030540411001015908000300250191501030708141d100c0d10b400c2e40c4000d081d1003c0380c0000000462140c82c1c00e041c45041030a10403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 765548875 1250 765547625 765547633
    0x9050c0f030c0a020a0f2111070b1c0e0303101401080601110c0a06120509030f0708070c09060e01060201050907030b070e060c01151703070206041802070b160f02 71
    0x3450204100a0002801c401c1910390301280500805108105500201d500f081e01c1c030061308603905119203004010544200d41d0b904a00110038a607020b40000712150054000501071146401d000a00c10381144075034158000c480544480c170203046015005400b002c1c1c102865403414040045200c1c00d40c00d030302072404610100c0a54101360380052a50f54800c0d02030030f1121654408900003428445c040246562060000e1004203182c0e0f4002015107613900214010446a2140c0c081030342da03030240000e000b000a004204200c00520958090041203104000d1441c2c00c40d169074060040d6140c94001d030103501034038401000f840c0d50902420782c11001800227880a00d095403034548000000030311071700c1441000030041ca480c3c5c031150120307070314090014020047c004014001000070300c4180700c0c0f20503a003c040118040d00d1008011155455402440c441c80c107450305100d0040c1000350350400101c0742c1e0921136103000c180d440803c070f8810b286005079a140344041c50341c046d00c1805c0352102c1c0707011584 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 765550125 1250 765548875 765548887
    0x6050105090907020a41030703110a0f06050f0c13090e0a0803180c0a0b030112140610032913020f0a0308070201020d080c191e0909050c 60
    0x10300142141c1e044035081e65408429035607000283d10b40444540001c0810070304075000c581000f0740500202680c040c0081c0b0401d0007201c5c401d0700803122669401c41000b1f800400410001a000c2d042c108284102c00c0242d654200b82034942c1d00c103075400e4070703001e507130780c60702c40c0c00304400c07144032031400d90f406001d041c0170341d041580c18511019021001e001d41c8500c541d58440040e2046001c200008405a2010f05695240b41c10f403082600d100049041403554032031484d541d051840d210642c0c030251010f1803840c0341135a02c3c03d442003607581d010741c0041e80d0300840820300d00b02072802840400d2250b100c42000c890a10301d180b41c11100c10103400c10390403d140c1c003100520f5049541c20613141e00b00a503890f4043c1c1010b85400052200a4081c54055010701c000344000108240d24010b01034441c002d800340c41c200e03c1d1914050701d0079082214a1201700d00d00301701140b25411748522112040388107281c41c0013035100c0441c000d49050304820000c40890b4140300100451921401140d9100c0080303e2500e0500e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 765551375 1250 765550125 765550127
    0x8150108060a02041d0a3902030f03040605100e15030601050f031b0a090507110c1f21060602010617011104060c110d0f0201020d0305010b0913021b1f060501 69
    0x1070103045c00e0182c44a0b440c3c04071b91800c2d01600030702e44940350824a0000103421052104081d07051031003204200d03000c4000c94418500200680f040400304410f11131031596a41e846c0c4004000041aa80040401c00d0b004114040a094170a00c1030442e0a400440d240e00d40c010907152440c1640520710070842066002681c1c0c401141c079a0072042020051030503005039000007200001550403c0041901d81001c020441f80c0c0300c01070102c2251500152805034140381c090002420b0120402c80868900c0300c04908107601c25800c0703c1c44280b42c2c0e111280300c000d2014088041d80c00070b5119400503915104248403a1003200c40030b14490680c54000c0200c1c001d508407144080c000d501ca02e01c1070002003005801440340314517803241240d600805420104010340780400c3d0303151090000340c0c0144a40071401c4200d90180c864241030701c40791054242010300c2d007030801200f040d128000b001c003290240306401401103900380350344080001c0350243c00b11011711600003000c0b411481032000040e003080d40421050b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 765552625 1250 765551375 765551399
    0x30307051b0723060702120c0a06030e0a03050a02030c060414070b041503020307090f08030d06080c090103081c0905030d110a0c03050d1107060519020a1b02010908150108060a0204 79
    0x2400c3d480c040f20b0000c580c0004540b4020503102a40090450303240038001c15000c03411035200074044420004940c0c442c50708500b241d0940d4540c0c81c460340403400707000209001740041c0c50560320500c1103034901241403605a04114054408079850b140c0b6890054195400b0700810000e040c040445c10b05283c43e101d240546003109a1912041c9540000481c005611500c0c201c406082c101c00010032043d500c281c06135036948030410785100c1a24043c00840c124401080542c2164402003400781d1903401e64403102c920364402c603405000302d442082e05d058072031041c1c011762185502407800396131500000c086038001c2d80c481588444480d0340400070150820303009584590102c2c0c151400e44d480e400c0b002c07140d0000301481184041000c80c00301d640c10410403280c03c894400d00d415854800d003511501d100c07206a0049001d0720f00458050818418040090b8001e001034900501d030a55042d541ca4607141d00303202001d100d0890741300d80c900042c032125408200c4107403c149102c00440c501407500620b4a25 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 765553875 1250 765552625 765552659
    0x9130603150c0909380613090c091401030c090801090b0618040218040302120c01020a03060605040b0a1b060203070c060605010806010c152403030206010f050a0e1305030307051b07 79
    0x32401000170301004501d46003040340e828850241240e60744203041001a5410b8040e4071070300304990309052010458501ca809032004444409100c050000000c03001034028240441154042045807280010043c0090080001141c05182c4038245824a5002d010000301071940c00e0101054442c02e0000584440d64000c202d0040c0c0c00c905451901d42d89800ca0400c1040e5006540d101400302c1c80c019010f07c10f600514145600380c07002c01c20350756100c80681e214042d0348940701310300b80c042c17080802540c0202040142c2e403044070102d40c400aa59034030141260029100007000480c0e24035100308008207440746102074282402c04161a00d00030000802810041d6030081105000c03002c0c001c001c10140c2c12410071101c039030701d4240304042c00700030f03101401005110a070300511818000094102d51900c425094407005410685410b081241030011090050000c112049184002d080498024070141d8001c0c0400c0d6200e903510b0068800550504035840d400881942000600300b201160042c0d580c42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 765555125 1250 765553875 765553931
    0xf080a05130209040302152503110d1515030b0118080d0e01030f0606020606011214011a0408121804020909040311070302060309010c03060609060509130603150c0909 73
    0x85540c1e585c81e040b81040c10180030004034071024414045529130791603d0181c40125800c80715040e071100d0342c044040c3c1e00c0000300030740c180c9420425840c3c40d810907048141c9800d80d10b140f44240d50f5880a0b41404850049003d40000e6034400c00915903603401110001c8010300f611010203110b0910802c3c80d2100031001100c814024081d10b46101c0343d010750401a00c2907002582001441d035160300c060344402c000c4a0040c0059054035600c0080d48040c841e004800082981c40c1a80da8244003903100b21083d41000ca0031200c1c0c0a000000e10040d081203200b03074215405199580b1481e44101e600d00080044000c1c500c214010302c03010000707864108003164082c0e09445e001c440c0c10712030081c2ca1305144507604083d4004000100300400c0700f505410440041d24140e60421507103980d2801118580d80f10701801d00012405c1100441c10700e82a001c207001c401c04982c00240003175890303581c0300246910114000c4000e842c1c0690458194204855600034000302000303200c556110485002001c9144078248 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 765556375 1250 765555125 765555139
    0x30405121c0f0309060516020f0102040e0408032806031502070b060d210806030606040504020a1a0906071406010b13180212090703110a32030106060f080a051302 71
    0x1804140301340c108841c0c00e80c20802c20049410601c40722900c08065400340005846440c052002e030030350500c210b03000c5840e2103018809a0300e855171004481d50029114080282101e08810562041001c074104840300003c0c000500340c0c59480c004522030f1600244c03d005620505c4030030085240303041407030f134800c2d030403124203682103150303e07100d107110100c2d00188200341e04201d4a60f19498100c503005014150172011a41c903580c031300d8200005d8400c02c44000f500666948410014610709612002122414184503820800c600d004200960007940040d038213403030b40f00d0440041c1c440502a041c00b6141c606a4603182030320500e000c8105c0c00b4107105040b15011402c1c01c070103001d03c0344e605035143d006090000c40039a0400c40001c03982c41e04c0b40d0006444000360054050b4007481c000201c90222a1040001c8285400f141d0503d601a0040c08814903680160b00d000c202e1aa03007840381d880908182e0302c0f002960011040018440d0300e009201c160010701c0e05062106c1c02d1440b11600e0fa044d0350450f154 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 765557625 1250 765556375 765556397
    0x509071a03070f0513150f031d280f0c170d0e06070614010e09070e0f07030b1809060a18020a140a1706010918020a030b15030a05030405121c 62
    0x142c600c0382a940c040380b46504110500400c01f90710040d6500743c80c02c550f40500001501141d0000807130b00403420180250b01c41c0c030048420007000c20b43c1c2400700381080015010140e241d19114070f40410b044040381d62400404090015144083d4547e40142406008140c01404800041c113a13811605905110b81e102003650b1040007601d8010305403040d4405540f01d1a560740d10b2003100041000d8074a4105405801404241c0100001e04030303200e4650501c800039540c0710804240d0041c1182042c9603000121201240307154405800d0060003034000100400c82d03450008940400c4070024505420620203601d00c200141e6141e05955054a00b29a520b4403880d400c840011403406c116071210010100142c00b1002c0504c0210300c0038120361400c04140061560042141d51400b0854002584a45094818000314034081c8001d81c0c015400303444420f040706031030001b91400118200407642035100080a1099050107810ba040705880e4000420b43ca10510070a541090390010090080040c140c600c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 765558875 1250 765557625 765557647
    0x6040222061e0303020705102a06090f031d090402120c09090d03061a0304120201021b0304030c080f060708060a0512060a052a0313060509071a03070f05 67
    0x105070014a500c003050885204035401c480081000c6200540140c0680d00c800200c82c05c0c20680785071b0103160740e0b64000071128400c80d1f86180c40c03082c2c69500308104000501c00000b608500c60004003e00074842200c01c20143d10b801030200e143c0140c10315924003c0f01c08840c543e1550010340d40c00c542d040311040207145080364010f1405840c0c480c0c0c03545c40fa0070300041c40f2142c180403800034610051903605021590300c0e43e01c00d41000c1c0c4451407030b64076a01c0820002d00802c5030220018241881440094640312040000d02c1a6038500c022406181d040040c0c10801c104507000040c008012880240143e01c00380e01e059a01c5e44401418101485005000149241c0d5008400760203442c0040c21841004c0c20024031941e074a4049a001160710310744800f0400d60302d800c6902c80700004210f114070100f0007003018560301580021b08004485a0000c5005000034914015640700b04c459100800c0d2052600360b013038204441103e10640351800c00c00c28404d80b01ea2000c00b02135008550b0800559800700100307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 765560125 1250 765558875 765558881
    0x305060607051f051510180e190b1c0f06090507030c0918111207030c03080322031706180109020316320c010509010c1106040222 57
    0x1000810300d000395082403e00558208009064905100c010801c940e00c0190700725612180000c039560021413400010001440b40110b02c0c2e900d80c80e40f00403a500b036035030f414040c0d80c00e4069400305210302c0c14400103040803420784a2000141401c035020184260b070021140035145051001804035242d000fa02d505005d041d0b0050904c05034004210f84040e81d690034442038880b214011650814148400039441c0c0c1000011a54066000403075000340c03243c004100100040010b401d000c841c0107552001002c22244094100154060521182d0301d1602c1001071b0060074000380500003aa00c518500340105ea8070200101503d07070540110b24194403180000f600c02071503040070341074200e1003c0004c5150040c1ea006103015681c0c0000903403550148100c2a1081e4181400542540310120b02041d13044483c0c2c914003030400b00302c50035a031602d10702c0d1203468255031040700c4400482e0b44528401c2d5059610440d09000307981240050a030a040c20760000d421410000441c43c40d40000900e424105d0075030368 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 765561375 1250 765560125 765560137
    0x603010303350f0106020f120a120e031902030f0301052b0302010f11040513050a06170303070207060809032d070506060f060c1e073503040501090603050606 69
    0x2464149440030b25038144040c6a10850b90fa84086044800000d200b074000900300c0780050004000d40204181b4009100280d08024010780070000154084010008140306242259442d60060b42c4d80c1d00c8010b40090307601450030b850f541154410810b407403541c400c03441505e0550700300b281e0b009038030821009012a52201040358407d01c0e20040030480030181c0540c008a11072102d01800c2c4400900d49101020b6406588a01c5411036030031070502082d0091780c0e12a81d0300c01c0700f18100050440e1030f14510b00025180c264945516840001480b038005e0301049100010040c2d86080d024034501b09850540300e00690070101400380310000c03004421000b88001030398803104861020381307503106410300b9607803400182c50540c01083c42c2041407016007428001c42e407203005044020405a6103a13041c400749052089039091450041c5003010604030640c1c082d1030710380001e101041c0c00401c90b00c90034205284000c405000070303a204000422445c2d070803414610450304282000501230740c80c200803a445101306 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 765562625 1250 765561375 765561437
    0x2060703090501140f1807060509090a1104030308010f090501030c03020d02032107020f1221070c0e0603010f1a0f1201020a0c120e0a032a0e150f0603010303 69
    0x1001c100b00640e4613803540e040c82240064800d04044070103006c0f60703440d280c0c607008800010b1b400300600b00c0c250900500094019103003074800038009000140c40004c0c3c0e0000e400440004104d900104926412150700d003001c1c1286076010001540340d030f910190b01d403c45100082c0106c51050519003903503010b1100700003940031498903590703041c15003180ca415548400d00c1244500410020b6155500301415040c5061f002e88008094841c000c1981c00070f082860005c00d403402c0300401000d40050791941e41d51004010403021400f4500740881018291104110740103c0c083c0b900e800400c02e00450b42c0d0f50103050406a404031460903010b00442d641c1c905091002546600009107a40e1456022581c502428000c0311400b9807180c2c03026048540114240341e0580c03205030000c040c80420b040d18410104d1054403000560701c5120440c0c03c00104485511003641c0d160180100401d4074504108141e80000407918420309140c9100000e502e8001804040d0801a02d4054080380001004034803400c0e07291 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 765563875 1250 765562625 765562661
    0x3050904110c010e0303040b0402040b1f030c0f0810031401020f0711010e0105280c1505060f040c23070206041e05040504020d0609020a0f03050309150a02060703090501 74
    0x71003003081071030b031000c070342612590702e0415540031503d0080196406554404080066512036400300310180034849031071540003820401e100ea4003800381d52041d150501e00e44000c941c4041032040039100c80314448800092088850400c14115404c280c64400c2d65440a18003102e0150088028024001e00c4160241d0726000154802030003804410340307030030020903641d01002003100001101c03c1d020350306582d9881006545454084540002829015540c501d484610300d203540e161211070755400200d203a080d9503280d007071000509240c00312164640c4240c0781030141211030b0300002c00e642000e41c840d4540a8018a414440400401c2221295034000745460780316600d440070342400d5100710101a0255a00d0100003880c8c1c10308e405454442c0d42c00400403440c40c1c0ca180c4030100582a0410101ea10540e5103a0120303005002062810140d0300940046482d040c080007130000482c07050509044203842404203040c200c0c1d0000d030007175108440b4500403900e00064170b03101d40504590a480315003240c17 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 765565125 1250 765563875 765563891
    0x10061b06090519080424050a0c060902090406150905150d02130617161206050703060b0c07050111030301080c06370e0103050601050f0c0705130b0918030d0903050904 73
    0x180311405001581d001c01c1c034655074009078900071038156103014a440e0201c2c505002240c0300f1801009c503d4a424011030000c28409810390008010f040f00b101c04a450310380c1e84114035246079000c0c1c04c00024140c2e41c90708101c10b00341000006060541007880780d11400c2c410544004648820800b003005a124200900c400764440300c00e580c2e0174000e190040164481c1d0041e00603a0b00c1c0b041180021542000c1400d00d0600e0b45803034000140600501d100c0915445800000d80d03610304c2001031521480c03010140c09014107210004120445056203804298000d10040c0032001000c0703040101c96034200c83c1103507607802c00000e00484040244c048108600d4031406003040544120000f451401556210703046801000019004c544054401600240d0103100840143d021540100222500c5400715040703030340d0302c00000704504111610305d40b1700f50311341c503040d41c01c0e0802c0c8825907044201da003400404181881c950641d40d000c3d80015200e0300c5d4544520070705141c05202101c02c42e22001e001404004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 765566375 1250 765565125 765565133
    0x312020d0b1302071403071a06010e0a06080a060515030c09011806200102030702062202090408070204110a021b0a0e0f0906070e0105040b0a0302120f10061b06090519 73
    0x141103144c0984600d0b500035182d40380c812000c0b00319680140e0128510b510400350a0388000d41031001002e990601c1007040a1580c6603680c3e90a02004000c1aa501c01e12880e00340d000c401605c1306c0b0750041d4011114540c0440c41c0e03550402c1507c0d03024501000b41e0b9103030340f28140121003030109407241c0303104403012900100d031950303202d4569403801c07050380b01100ca00d4220213046030803031000b192148016040300010441d94000d240c2d0785020210244c168460008503500080c2c4000d000382c9046452400c0010304030110b080c1406042034000390501118104041001e01a48401d88621048241e5106002c15265540c0c0c18910740041e0000181207091881d10400440341d44400b0b035000b080c0e078482d840000d001c0a1044100d84002d40c41a035500c2d08092511890784155041108a8801c1c150280485070342c8080e141c0405104100c02d1038400302c607051400c84000f00300e030150060020170529510802c40a107901044107841d5a0090001803040c0c441e0030081e003414011115400c103103a40c80c10140c244 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 765567625 1250 765566375 765566377
    0xb0c01020904051b031519090e060c0a021005101212030b03070f050f040e19120504050d0b090109051b0a080d090501080403031410030605130312020d0b1302 69
    0x3801c09650803c400d071074261212a810f00840940c140381d820030400150520704401c811980740708040c0000c21030721540742140c011002c3c180c0104072906e9992040441e4101c04025003034000c044182a40e140c0f4100f000c00035110140b4051148041e905d8201180d400100101400c0051074000002059480107151420040e0741160031100002d042503400c10040c03074003042c1101120000079031045240e160205021202032010080d6a0140c0e032003840c5280900e0034030030622031880fa040c0c0c840c0c03200c41c2031905110b103c00b00c01c45101002818001405240c81c2c2040050311b007904239410030025501c01c801d15016054002004000f0b01031400c494521041606900c1248501121840440d0f070700c030114150780d40a005040310000d140c011040006502425803550424024a00450f6900d00001d900c0858601500d000f150010300b51403c00c00c0c440c5038480e15400c040c44000c40300410585441c018901c800705030080d40f0003540041e0140c42003803160b1202615080113010095001c1c1d9558100001b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 765568875 1250 765567625 765567637
    0x3030a050a09122a0e0a09030201021b2404080915090307090501050406090209030703380a050108150a0c0c021c140a05031c110c060907060e01020c060307090b0c0102 73
    0x4080c0351340b0f40780440f1001410a450594a512034501d44c103954032030300c031000707042450400c2d001e5550802c030582d8040f10341070030103900180303000080035080c0780851800c42e41c2020003ea00b075090510401d000015900303c048075490741c0d0440c2c0712481406d500040500d0391103464000b0b98540f05964002a0381c4649400c664100d40341107804020041e6994148016407040345102503164101340b205000090305020315107203619003086d122600032950107032908501007005000c408041080100803028980740076090142c1800000f03080f001011201100c0a1034000c0c1c11410295100c0400a95051040c1c405184075600141314501030904501003015681e001981910b0040368809042c9452000050200703110385d0000003103140001103070750004a1baa020032410540fa8540d10441520020f08020785a4039101c100540a0b90400240c1e040c0f40c4840da034440c6080c0028469200050ba8011440c0c000390002656469520340d40c8500842ccd4a040a070400d00845030082240c1403641415405030607 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 765570125 1250 765568875 765568913
    0x103050610121a090702101d15041b09020904110901050d02030c0706020705100c020f070519050a0b0a111501090213090c0216050f03030a050a0912 65
    0x8680c03644001e00440464420070300002c10810301042216103441e0f072046004400d0310015154843d00080010120002981e4030700044c1d000d40313105440c9041c144110310404d81010740c00144c000061440ca078440c0c1c0352030300180c1841c00c100000b0741030088812000f12405250084006c0458548000300020340110325283d0151b0b24107004048101d1044045403560795058461508010f80301180034040d43c4010000512083c0621100700001d000c4d0024102c0d4601c150f02030200241000560412a0590715500c2c04540c003000b40e8074800347c000300301103085d96002e0b548104400f4104074409042c1d4040e030b01854010181c91400107a0498136400f800c00500c242e076440e98002100b000e4180c2c0c419446141c0131400d0110401040201020707070061007040c94500380380c40c4d12651408040d0440314445040e50158100060000400c4c060660342c201801044070030425030814500071940d42c0c0603801042d0140720000400150040c09009664000c2040c801c43c41810034040c900545a40c81e4600700d0320b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 765571375 1250 765570125 765570131
    0xa020a150e0a24090806041101120507050d15030209090304180507050a0c050c04110c070f0e070c051501120b010506160303111612020d05120f040228050103 69
    0x80d20b442c0010300c00d030803a600e88a024112002d4180021804100d1070b603030109010f001d0400040850b014441c1c244140c1c081c803000e446180c50b081c0007400320000c854079205140d1419040100c656040001d4070351a030104503001460740c0849100c0c0c5010b0055400c00b0358410004030400c2200714000004000fa51300c14001035540b400303c010280d040e50019610f100214409111030130b0b00300c1c03050280300041400750003101c1c0e02d4009500460100e500d04075280c2c4000078002030b508520003040284500038507001e800c0d14082c40c80c0060580680c01c0150103007081020701034188052203010400c10011100020201c001969140c80160f840505000200c0c2c9040c200c200025662a026007600c59614030351146072800b16556800700d006000b4a900c0c00e40807401440040f221907600f050f4030b80003078070880f20700f5000b541104001e4500380302e01d00c458082110800800070400081504581c11003001503d043c450303102c41c80000c1e482110b00014081194840b46181806400380305038504440e0203880070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 765572625 1250 765571375 765571397
    0x70e0a06030c0b0933030a0f0c080726061e031203060301050106080f040311120a0302120903070f120e060c0d0306152708030c0f010f090b0609090a020a15 68
    0x1706501019804140c04550510024100051500c800540d4040c2900c44002000e00110304428200c59429031008005800ca404000c01c090300203000c54403000c00300d001c00d9042c4990b80c49000c00314100500e1503018040b5030301c15901803000362a007489000e00c0101900c0100080e0a2034049542040315228800c0d070805c4000100c6901030010030380034810b46116040b59545c1c0340c0f020307911005000c0d120941803040c550155900c04c003010140a00b82d42654016995072034918001600c41c41c050600b003095001048044001180103000f410440e51110707010049980602d0180d60036602c4050b01600b020b80050545003001c0007280084881c59140c40401815171209aaa010f80b02080080008552002420b400710080c02e0480101014141020380e00281ca948815003190032082c3d0812642c0e0010f21440c480382000e000b04c55284121020411403001c450b2600402c0f1070b0702a00c1d0390700801584000ca690a5000c1c4602e44c400358003d0005482d06940e001c1c0340807102001c0c101c1a001400f03000e00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 765573875 1250 765572625 765572659
    0x70b07120c08060108040309030b101802181504121a07080906151906052701090b07030c0204110408010e01110a0305060a15080a0c030905070e0a06030c0b09 69
    0x100c010522075a952811240d44400040d15401c1c80500194144020030200000041c071510409100b441084000c0030400d2904254020501100c0051140c0750f005000d00f12042c1070341020307480384282c11079404102020701c1c08032441c0e41c8500d07006812340c01c0080056100744020400c2d1074504c031403201c0e022960b5550b511000c0b42c68090580300764095800840100d000300c6d1940740c045542600092004851482d281c031189803404903a0310107008984081000c40c00c071400100d624400f941c041602d450091010320000384008014024103c00000c0440d16505141c4140e184000f240d45c0174000f0000d020b120340601c990741c0c1040c8a00030503982055018400b440c2c3c10301940310360701d01301125203081c402e4501c0182c1c0500001011070350043d400c034500045050000601e02d61280490f2141c18030390030b15820440c140c940224240003814106452700303001910005405003160f0542104c10b4054889140da100500081d90000d0b02c0703010082c01c040388030441c9170001d10b2196000c99008c4526038071001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 765575125 1250 765573875 765573881
    0x106081b0301020a231201080c0f010815190e09011b02010213120807080a030f0c050405060703080a0216140c0909060705030405031c0c0f080108030a050c030f070b0712 74
    0x281c00000701804e18400f131885e016802c840c0a07025131903003c3e09101801c040080055826401040b907544024512695400c111051002d0070300c0030b01c1c0803030841c6004410501001e40d481000780c02003126030b903c041e030584602c400700098412034480b141e030f07410801001800392150583d41c2c0000e8540c00c10b0f05166070700500c03c8a520010060000c030f8454501410300c120b1540c40c00b03081d10002010004403001510100081007501015100010450550f40000f81115031101c040428084100014010b65482c103040da149a54140f916601503910160040064000c2c4c071a0b80e211010020840310800c65000c1c207001440561104468045581c40200800e154080e502e400680d044140460300280c800c01c001c5a01ca8083c40843c0c0c98500c6584e41c40c840003010407400c10300e5035650f64074115019440520303000c01b4600e500e0320300059410400b10035101d00c1150b45010070700000242c119040a1700788241d84458a031580300303a4031880582040f091011080b500b202c0041c4050001c00b018480c03070b00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 765576375 1250 765575125 765575137
    0x5030702120d17060d2018041101050a050708032809050c090408220509010f2603160f0f0305091c050c06092d040c023007050106081b030102 62
    0x2031500105c1140c40d200e081e17004800703024040c00c598102ca2a9100b507201d14080d194181c0740c0c9102e41d191031900307040c5000300d03a910340b01c11410081c040001140e459400400c0c2c40ca2107801c1861242c0e80c1e05da0400440a151804900000107940c40c0c0002c0031602d25580144651030068090703d091940e00c800b00180000d003203800510003c000c1c45004e05104001c503281c204012944840e006854036000000c181150982c08180c00181c40c08080c0000300c0300e0614056140c94801025040c101090310315501da0207180007170092074110442c07100c24091352080340605181c1150002100103200d0600074082d034400382503503008a00703c00100c0007410307594001180c5560000080c0410301c0c1c2c81d00800240e94490445c0c1a031040da40b00c00359036101944816400c410b40700f007110b00cbc00380139100144402d4441c507508000c01e6405c46048a00c0c000c40440e08090304602d40b4101c481c50504076889a07036680074810010f4003540c07900902140c210400555411000721040444204603000300415082c8d215030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 765577625 1250 765576375 765576379
    0x1b02131a030c06070303020309070e16030e060f0f0601020709050a14070c031e030b0414070e180415090f0f0506010f03031d030f030c07030b0108010c091205030702120d1706 76
    0x40144c1d0010034801d03805150050360304e1060340c0c03000e6610000d402901c081650101030800d081c074034a03100185c040c8101000b1811003006040503141044038500c0c450001400344003440480c10002c4c50b142c0c801c2c03141e08040c0c00030034402c124505200f440d440c014648010341120801c1d200e40032410881c0078151408c5607e03403503510b10030031050700c8a10700c0a81d050f841c4440d0515031107400e031200c140d6803402903c0d0702c400f101e16045050b1500040041406107480b00b50f030f014022419940b0600005100f03001e0b0310a8104000c60b802211005c4400000e2150400150680f21180c0c905020448440c1210754000d00441c1150521390303e5075444906801d443c0320043c003043d044007051031101010320940c00708100042c15a91f81c50840400e0604560007860010301e590803143c0240104100107801d107001d00032140c02080b86401c5800c0c0039000d62400e01440d5800003841c0c1280080003400c108807000244c1c00307410740c00c10842600d00f80e50f6803d200c3c10ac450105120161500c100d144204000b0b208802c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 765578875 1250 765577625 765577627
    0x10c0206030a02130b0301090207031403010803090108040807061b030b06030f071d0a09060f091103010b07080403060c4b03021e0901090b04080c011b02131a030c06 72
    0x2c01641e4002540b0602e80781e8040030301c0f00030000b007030400d10f00a0350003810199405a43c50500d0b143c01800019030a1001c1e2203e4801c0c001800b4601000096072441c0b0300a0038803502c4c0341c8480c10084030f24081d05c40000c118a040400d8610000b0b0b80710700e1102041c0190b1010701080c4800c0c0c0400003507002c12955640d88558020020f1180da00c65400115554070401c82c00b528481d000c00410104070395508510a103c3d1284020010300322491500c500418110b0010403081002104208662206204203040c0c00d001003031030401d1014600440c0c0003594007500420282c169020050074185069040d460740041c50307900c08480ca41c0842ca0507034522901d1000c540c00c040c4603005400072015581c852000c1550a11520150142043d40070580c280101d40194840e044080010003c10a6030030101000c4020302080080b4240010318416582f400d0a04000607558407118400715040613402a611490100d00480380b2107855100c50701511031040c2100060b680d071002c0c9907a8000302c045490f00004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 765580125 1250 765578875 765578881
    0xc0503160e09092104030b0403050c1e011512050a1713030b090d02071818060f050a050c13090203040203070515091009050f0d0501062c06010c020603 66
    0x9034845000400da0415494524004021803000d80c0200d940e00d81592001d0664400100102603054421802c52915031409003182d4408862403005072000f41071010114580c4c00d21071083c4002541c211a044401c0c4a5110500c64503010780030140210391801005070010421a100c0e201030f00d0020340000041140e08103c2d41e54110100340621158002c1400707009003003000440741c3c00d200080d4080c5d800849a418a501c1550401c1860340c1c4510655001e0882001001424042c242506020001c0010f460312407074098640d008420720001c01c110300d0030769844d00c012600e43c002800f891801d007041000c0d6a40c030044080610a80b41c0b090510b600c030020412440803203030000c6901a1000d410383d45450350f504003151f03d400c9c1d40900200c1c280c2d004984903156051600c43c5028052452810300d034028948008103d40b280861074040c0034242c4050b203181845001d400c064010f00c0c3c0803060814030041d84102d9102c50300d0401c25a160a2507800c00b096140d1b10501e0607110b0250018800c0b4a10b072 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 765581375 1250 765580125 765580141
    0x60d0e240103031701081b01030204090908040e150a030f110d05010f1a01020c060313050316060b0a05011b050f07061d0607050c091302041d0f060f06010c0303060f0308040611010c0503 81
    0x147d00d0302c642a041507002c002c046403240150282c80622486500d180340c0700c60401c0181c1858080040201d00e194107801e509450b6680d402d25114222608001410354507501d50234200d03096007840c40c4990308015180307035000c00c0140542c4640344005049004100c09060780d28940000448042428010780c01460a0045441e01d8002035800c2200c0c02c034110250b5215903290307130950300501c040071143c02038501c1030f1043c8047c13402241c0300e4800840e42141012b08220000c3e003080040c00460b4907010301a015038003089002c01140030544041421581c00b43d5070b50000601c130401c0802c20700d41c040c00140000900303040180c00d440d00103034444040c1c01140400d5041c04940d00004040341c204490315011007001d606c0c0e520a003a22007802e0072140c00307581c08030211185804202c0d4100352407980402e0400c45080c0600c0c00082d042242441d0000406201e810110080d001540288003801c088800020420a1001c001c10484496845a000704880040c10a00f01c4a40c0e02c1d801010a0042000032054 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 765582625 1250 765581375 765581413
    0x3020615030a02040e010219080c030c2203060516080f07030e0a08160b0105030f06040303020901050702041a040c0503010e01051c0519150209060d0e24010303170108 73
    0xd03460103411902c1c00840b503000242039032001007031400e0503540000d40040b060905211551010418140001030b410950640c160b03a00c0000e11107601d03120041009022a0388a5034501c0b0810900791441020b00d81702d00700f00e401880182d40617510766604500303189103e40900e0400e4420310000400003e1a5100b48043d4080c241c1044400e405001d8009890001064407020b8041060051400031704881c4030302e0400c400180c103030401d5100f42d00c0081d40c0e8a0341c080004006500c583d0510b405078843c941c40005032118018040002d501c10304003c11a40c0720380c01c4c0000e1050343c00701190203120b07004002005a59038070081c02019100200000140194140031400f55007040d02201038020003115a00c0e01c506103500d5441600c21822050390b11014403a50010850030610899400c501e09550f800c00100e0500c0780074031188203107448200b8906124418082c14100030f103a401503070940301d00d19003a005103080034001100804c503140001014044660f10b11070680c0e4840c0010240e11415400c1401c607 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 765583875 1250 765582625 765582661
    0x31715040b2d010212040e150103020c030d1a030f01050f0a090f03230c060901060f080c04052502060702070e010b030601030924140a0207020a2c070906170103030206 73
    0x5511842c5c10806070403d014008000800c0040c05054032410100340300240301c101f000300d07581058014001c003440c0c100c022045440403c2c4900300010109958a03c8800c03120700031a40c1a414042c08004024600044d0801c510910310f007100791805a654400c96411a906d0880c0036003070708803960841c07001074042c82d60400001c0340e001b000680302000d40c0f5402c0c101e0b40100d11a1406800c41000e100a141c001d000e1380303000d8615203108200031800c0415080c0e607001d011843c0c51145480c1c0010482846000800d240151000006003000c0b450810002e503840b0000e6495800500c00d04000043ca91b0100002c81e041c0c51050342410300c0d40d100d002c0110041c1c42020307025141000300601c4012410a0004c00c20071030101e45001203000710103080d00e12a21500184252011340c010043c1000599840d031700b500544009031030b00e417908050b01d080010000301c01010400c5028000c1c0c184600141c01c08002e40440d40165074294404c20b400743e294400e2030b0280b1000380542d1040002c145072072003400ca07180f4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 765585125 1250 765583875 765583877
    0x4170c060f1c0e030a0e1306150309060912030605090f07080c03060315010f090f110906160609060204051318080a03110d020c070806100b07031715040b2d01 69
    0x3a07030480c0d040f2098190381c0b040c1c92000100b084000da41c0707640d050681c80c440c40f9151203002044401d2406010449803425000307048100b40d501e003042c000b046040d5105109003078216030300214039628900090020609805603c1c40b4400200c0015001801551810301c200510350f188021901d40fa04034080c0340d00042c00682e031501031080c0100d0101d81d0741d03a41c54020041c80058030788041c030b403540321403c44490300c000c0c240150400907040900c50b05601210029001901c0e500d6035807400700c44003140390302c0d41a0700a20b0305080000c1c00007800002d401400c140c0380120341940c00500124242d10031200601c40f0212810001481e940208100201524001820703080c0810784410131350241c0565440941d248403150380c08603022002e241304001807000340841c0d100400c1c090a000342803148000082c414018034130000124581014800c075540c40b150707000000c5021a50500b0403030341f84810b100100c0c090041e032800030b0f00c560925040d1711803520500c2e1446540281315460f964034040c2500300b5030b00d40c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 765586375 1250 765585125 765585131
    0x5060d2d0212060601080c0702090408030a060e0c0a030606263d0f080616140307120e120d020d0204030b091015061e1404170c060f1c 59
    0x9009612040c022a82c42e4a0301c40c00b03001c0030700c2c0860015068200140000c0010b88080c03001c0d00c010380300d40c0030f03164005410000954507652488800c101602c1160030503850040c00c01c2c140107980043c0c2c03001d442c00e401c50b520305000c1152114011107e482142d6500c0c0200c0320300310020b2803121200502c20b40c000030092800a03210b2071012003183c00d41859094502001d6286e00350383c0c200782c4000b0f40350020b007550f2018a02080d20300080d02d507a444002d0000011070000e81c0541100e903000b41c01140d0306c1c20550808603260b260401000e8020303603076844441c030a01d0a080708015031020100c1c580c008800e024164a0820a0b484903000094100400c640d070030a030700700004000714140c00302d2144100e49510040040046c088060302c2a603003083c4c00e0548010082d04184002c40e0408043c2c007400b506500382c80720394202c03048110744660080b010350320b19800001c0d02140c2e081059442c02000980c003421a000d91000d00144801482000c0301c2035603080d424000d000c1c1da0f41064001c0283c1c0c4030001408 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 765587625 1250 765586375 765586463
    0xc212021030d06090504080f0d06091b021621142e050c0307032a1e020c030d050c160f03020916091a0f0c0105060405060d 54
    0x5204240d41050185603180d00c081048000030610307000e0007010704202d080600c000e041580d144911030244501c844510741001c6509540c0748156440311009007040c0400380846110400180001c0d00d100d903080c1e0043c05071000b1400c40b5801c500f03141044840c1a4000c900107009140c40b800044843d180c207c4113980e4214864000440c1040650004c0341000880e0210005001009140c003040100000a02e8108020014110100d0050302d07400652814089651083c209200b2000900046a000d281d07085200c815a00740d403100352687c2c1083ca40d2141e1040c130707420000907a0b403007107061440c692544c88034145241441c401c502500b0306900070382c1100c0440390305c18003565008009030083e5003059070700c02c010800c0d482e0920407030740c100c008940020148615140c009007c0021b0740501c884411650385041c4490030744400b02e07400ca000e0100043d481d44c007400740181c060302040e100c0038866402d080200c0c0c2d00f403410005460341607034450804103440c49a00c1c4c04050a8080b00200d07006004400c0d08 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 765588875 1250 765587625 765587659
    0x20c0c10030f0e010c0207120803010504050604020f070b06040c020703020a120c080318040b3003041509081c020a14032718060a050103020d02160c2120 67
    0x300074043e011035001182001640f04024640741540e40520004611417100901184000c421203054500c00d403004078003503590790007007000b030310902910f0b05050701c0c0050032a062250341450386014003002c403418840440c2c528400c0780d0b51205408080d40c8095003200c100701600080048201ca60304c02c03140c0140703071541c0301815411078210344007100781c01c40c16614104842c50240300b5049000b80440c0c000070f04a01494a8140b66058804000c24148460441c1e040c1e16204100f500d000b809950300300301800e52000c000910502481c46001098800d5841800320b581c6220302c0031070024241d074002d21019041d501d90324130b8138060102410300c80c0002c0101110740041d810000c481d0b1265154040d40e15240d8005100003900740300800c5180b1149031040c4912a543d10800108880e800d1a000d030b01c45203a400760070b0081c401c10700341000b40080500244100080480003004480c0d5410300b04940301c080c50150f10320340c0080c850007440304c1d914408110005840d02c001c0326000e41b0240480e000c2480030300c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 765590125 1250 765588875 765588881
    0xc020f0306130b28020901020a080318070e0702060403050a09050a23040905120d0b19030317040308070f050d0e1608070302090a05060d051006090c0201020c0c10030f 73
    0x70b4100900352400c1500310a0000c1d48038025008074a60750422559903140c440000b021020901d4a00060340000d941d500743c2e031003002040e54098100750215500d0400d500d1605a107d40c414202c88039000700c100000e0f084801c646441d00c40d10703694003c0e001729036559800320b60390b03808070b800c0340140300910a002c20261507040c0b07010007070b00741344c98515510b00d1030712481541e500e02c07a00d10510890428048000280001c581400680d04851000351100b06500014010703140c00404a900b01020061080024100100070001c89000e0786810f2005a42c1000c207c080000c02c0b40d010f804107a004011030240c511034681c082e420b804038500743e0308007078035000740c0c100380c80604031840b409621403a4842c00107542140c450000703000120003031803503138a15400b044038500c0080120400550324030000e801d540f10342030070b030650a52103010f4442c400f407451482c2006003214040c010480d80341c1014a05070030f0051080b2410740051000a006070814102040140000700000c24200f40d210700c68034295900c2c40c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 765591375 1250 765590125 765590131
    0x6091e200309010506010816090905070e0409080703090509010b030f060a15020c0f03030a120e0307020a0602010204090b120c0f15070f020906060708041701060e0702060411030c0a05010c020f0306 86
    0x20b00080380500301a0001030030201c0150107400712844003040180c00b2a08858401c040f01d50008003c41c00740d8481c03805a0b1420000501d8179041414050084204550803004060851207034640381d140a80343d106004807040b09000744c403c0d1007410400718801d900541c080301c0d48100c00030b10403042d1036202d151030b2840000c8541c6840160f40154050a51881c1c40d80145140d807100703400441c00d02041c1c0c10020221200300300381400da56910540740c250f0b5107007401156812600074010302d001a69800c4002d00030745c000d224034503089180c001140c2407464240303490b103e04c15016000b80051505202040411910541e4241c2d01400292032806103450007805800800e0280402c942c5d032140c030b40184031a8032802065507114800c100280800a040141901c0031b48102a0752000c182d0000c600076801000182c000340c40c2442d03058200240144d0001d12248114854810240054900d00625940c0d121910a0340d9110780105418007003548140c40041745540000c0c540b040701d201035404241094015 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 765592625 1250 765591375 765591391
    0x1b150a1d040f2406110c120106050312040807050a120209062e030b03030f030103031d03061005211b0a18090203150603060411060705070603060906091e2003 69
    0x55107040f003581c03400062240c01066203080c50f0b03400f208854042d0780c60705014040765100b141220358107d45a1030035407042014040180850b50f0700c8030b02910b40401034006210390f00451181180100d1103041c10709640d000c0b1071503002c42d19000001e650030800300e424010445500065010500742e684840c00c4000c2c80716070a41c03c100540004140c0d4003c00361000b8440c43c5000707a000f00003400603183d10f441145e04403901031900e074079032416840a0410007505041e8003a4144514014000600c0d410086241240c0044070302450042d600400314412110b803101c1c01549421540703424215014200071540030f808003d00c0081d45646840d5074030722001c041c0c01d002040381e50360340340f070300071400c0801001c0700d2590408424040e500d0301e040000d644940081000b0034280d483c0d10102540c1e00c5007001c3c1c40d9060380c05820740315a50b45803503004008000303510400d82001c3c01c006000a034140350344590f40100b486441103011001080c28000c010341040070342c032184c15200c0c0c8aa07143d2004a0700c05507000703a0714 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 765593875 1250 765592625 765592661
    0x602030304171204031115130b220302100515010903080306040209040e060f0c0408030f07030e180f060109030809061b030c0304091a0f1306081b150a1d040f 69
    0x1c0503800f6147c80e1100d03c401045402200c10720841002c40030a640c02598007191007242c6a448001200c2c4195107904800310f6203070b6000c0d0030010182c0201d454500050140c504000035a207118042d1620f4546640f0302d404100c07108018000700f400c0c2c20086500c4803018202514108104000c03d0460300c01c00b906c0803071600100244100910000303a819008400c0718211424541050b88041c7c681c424000c00610096000074210105402800944400c0800071701d06070b00340003035080c210340714a400c8440e0701540e50f0071000501c0c10360003500c5000a481d00102c2c001e080c18103d405000b50b40d4000088e06000381d10340c0d0142d80c0c015108000034860060000040c60301c0754504440001600c00c260a100031802800305600310585541d42032041d421021a1102040040d01104100030b00494000c001030380a003a500f03032106d0b405000005e5119030180c03001c0046d0007103405042014003076071608034009131107402d61070200a00702280035003c06004100180e071003050143c55040b14134000c250550952307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 765595125 1250 765593875 765593897
    0x80613061d040c1202060d0203070e040501080303090706050307020d08090a02040204031a09030702010c030305070e0303040f1e060915052a01150b1606060f0909140106060203030417120403 83
    0x82044001d000b04044c1320340744005945540054200d016028a1641c060360100c00920304d40d104848420ba40740c4054406c05c010350310b4411b465144d62045440030054814048001402442801242e1203040c561b0701070800011a640210783c18000906421524454030341c052015917200d200800041d48103640105070340c012090100d68003200107082d00200d030807e000c0000540d800104034044998507140008a5503540030068640c0001450010303003601c80405c0100d000e030b0b1003900c00b10558000c4410310005c05030400114402184a014010008003214020014048124240c400311060703810b245003003d000030789014648064103400c01070034901c10f15803040f00c0d00c00e109080d0b1f00440a1550444c0c503003007030b114100c035102d81124012080b8034241300c001031140550141c40500f030241c0c442c666040c1d5079908a009031103000b0f819914040d00032501100010305208074403c81d00150050742c2960b4841c0c0303a0b441100560800540b0281082054110208503410514070451281d200c040c0002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 765596375 1250 765595125 765595133
    0x1020c151008060a05191103060406051507030311120f040c0b030708060f0303090d0b10081f05060a1502070e01060201021204060c030e2b0f080613061d04 68
    0x4140580010080d4500781014070a000011400c590f014520450100307a680340c43d6018481007660080c1c041c070151604c404280f0035000140154003901e000c076001d00c1501d0316881000f8813949015101c003082e200400003200040d000c0e070800c641c04074509185608005c242490042c119100f15020403820711207504000030407801401d608040c2c00e00080442c10b510304502c014040c444042c140e58807405040c80c1c504400e5404000711188084040c200c011354403c546003d54050f0000c0d00c4800c03524100f03103004203000000103903e40100310b106042c824041c4044100000500d4050001500009050400300f0394814030803203000204043d42c0108201071420800c107041c3c42043e0402811640100448000d00e1401c200158006410040005e400c10782c40d00250001c012825919101d400758141d0a07a640042400c0d03698041c51528910109441c01141140e645030205400000704ad80700d0082440340c14081004291003c03088400280b194139503040c0410345401d803046a4034144000f040100300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 765597625 1250 765596375 765596413
    0x1217160209180a0308100f0807080d0c02100507020103020706020403030507060b0901050307050f03010e1c12061d040203070504050c0a17070509240703050703020123010b0a020f01020c 81
    0x21a00714078281d40340c05084140b00d43c981d2201d040240400180901080854145410003801090602543d0302800d41c0c1c0d03950b00d5200c849034800c1d01c04a0081c0c0d410424118007507034401d042507500418021403060318000644058200d0b00003a4105607084c09101e0010b0111320041002d54081d07100c1c2c64994225203000e0003510311110f40207024001c05d00c0100000c5c3c038006041c0c0706407a421141d0113003006200d00428010f001d040b00b508142d109030045840c1c04800c0d51031840a140c91035490031203400070325082000780e0b406441011a01068442c0c480074818070400d8941d0024401001d03a442e2aa40703400007419141c080c3c4162480c00300004050407030035004108000102510080d6a0007450005005401d41c0100e60003117006811800c02030607000c1720703c1c500440790b1a021429580720707e20b50400801603000305400b107015610340150325071841c50508951080b40c240340140c1000d6801e01c0416520b541000f0002008d52040d502110100d100a0015000c81c0300810010010031042d18034107244 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 765598875 1250 765597625 765597631
    0x308040506130809010507240e060702070b0412080903070e150d0f140312010b1201091802060d02040f0e06041508060a091a071106060102070f1217160209 68
    0x141928030b0486000280e5031506849021200342045912030340103040401003074405014400d10800c810800362080c1c04264131500e861910710049440c15500c10b88141e0b0707584014044d02c1403d4405000821892140000c4800282e104004503400d006000000c245007801c180c000b8104411600204080d80e014040310704140e100890701080e00707080945074820403007243c840190140707074072405002e4448003c00807121a030b1201d540c1c920644d030f9110b000302c03c0c1d44c2010182d821028482400000c045100e8014220814444000c60a1408443e8204031660b4084050340c51450b4007400300003500002d143c0c608004051000c80840240381501c1000200d40d034000500c9100401408240503500c1c0001c0c240f540a6102c5000061544403810700c010b08a00c545044182c01219004002100d5803005004001070b69440446446846081c016a11807500f401080301131360500c181000094040100704d0b803003034081c00c07095400c1943c1001c1c080c40c650105e040f641c2c0c4080003840440841c1445052154 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 765600125 1250 765598875 765598891
    0x9040c081b091c030e0306070f0206240d050f070b090a0602010207080a030f060e01060f02011512170904051e07020304051c020a05040c0c03020f030901170907030f0308040506 77
    0x114180b20400050f00d03031403811181000001c0580f448800f0103005142c00d8170440c1008084038654504401d008044c140740d0f0200400600451011072002500e03401a410700610710008102d218810b0000c0c05003242c40301d142544c4902c04c2c07108400c00d44005000300400340104105003540c0384001300610030f00e009564442800c6a104010b1074022039480e10544d80c0380d0110b841c02241c01429144e070303c40541040d070030090f00e0b82d601100000e01030f80c002900240f8a001c540080c000c200220403d01481c0d0014400d17440d0039610400004005000484503a2316100c0407e0031030b050000c6c070310101e02220802c55a082035452800f002d00076900398000034a900c200248015440c083c14000450f003840c00c55000a0151000c2e4180013045559010500000d4407014008021662108000070004420a1003d5000d4001c41141d800c10640c040104c1d8400e010607103494511610410105091510050500f06c56002d28003021000880640030241923500070b41d1010a1410b00c1d040c0300e0708002001e00151 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 765601375 1250 765600125 765600127
    0x70c0204180b0906100e09070e010e07030e16050402090102010e0109231b01110a12030f1107210207120804090c111c090902040e090624090c09040c081b 67
    0x5561054080303005903542005c1910b215107e184440d403916003550000020307403540000110700c182450803a40e114403400c0d907082c02a002d140c06400c0e120540505c0901d05164140700034007090425800925150b103040c80000b4540d03440205032803c56120760030460711401d00f4182c00c11402100c0d90041401b010000207444083e0036658124070100c40e50401d541409465010340100860601c480616280c0192208000e5400c0500060040c05101c107061a0a0f1400c000101006440c0041c0c903106640710000c580101070700140d4811118101c041761045100f001070100705d100401d50059100e501c1000c000d030710f03541080c502005440301c00e030a2000300080e8000c80340381181c000400841c5000e02250504200c0001a0704403a03040b040d40003840c005000007000030b502440c1d4200e0314813400800c0b003584d02588843d243d400040f2140d15503246002c0200d0ba09185501e400d0822940010551081d945000040c801280076226100300d13000110b0304000c200055068032005c4104060082c0c0011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 765602625 1250 765601375 765601381
    0x151906080715082404110a09061d01200a0f08030906010e1303030c03020d0c02030c06060f01120e010207020d0501020d0e0d0f0503060303160807050c150909070c0204180b0906 77
    0x405150705038401060007012450a2078134040c0c407960b20003003945458880080d134a2404290103441c010841c4035280000d100c260030101d110380340b9625040704040503519a01c0c1e00c001c00c140002c0b031a640881c80c0049000d0105038030001000d042c0924841482180d255171680b42c40c2e5541410208142c6c00180c0f00c1d80180108940034200c002125881603050800040102c03041d00e0450080c05000501c143d0549082e5844011a800202501b142629271040386d0301c1f0382d07694040c00180c9000c40040c501083c00302808252781c400715000799008144460006080540c290009121141842d10641e901d0350300040d01108603019008422004000d48000c1050080c0e8180c003d25807080e068540e01004004800305003940d0b0248203c4219160790111050800a91706003415142d0010608907298824824900000d00b440007650f070b00c5801c45a5202c1c1000101001d02c80f0040006007644104500d003150640165140d01c03e01001d440e41c007074150f4074241140b40458003103c0241060201c0d038800c3e410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 765603875 1250 765602625 765602641
    0xe0a03080a15090c020f0106140a050d0303020f0f03090f010603021e030a0212031903090c0b0703031d1b0103020322080c01050412090b0c15190608071508 68
    0x64540081070050002210324080d1031074240041c80307800140c0300d107052092806000303900045089108240074000c12000d03640315945160550340c492515000105101c0402071481c0c0024816400c0d4080c0c10b026241505c2d05240742142c0e440b001d0030845c511008414844084c030b082140c1c54000c2c0c4488004c1244904680001b11030001480046600c0c3c80b5220410400c0d03101070142208090307000e0940078620241d000607613100d8014459a81481400c00d00e0000070602c83d02440c3d03040f0741c003c0d50f01000c4a0419940a0b103591114505a0030325442c0d8240032120301080b501664004448000351407544c1c911201d07401c4d0f01130740340040f0f41014010701c00e010190a0300000c44494440c004034081007c032052400142c50b0041e803083d0f0919510b407404000a00c105031101e10180b5090740c1c2d5a080c000d488070080c680602a4290b41c2c00280e00c102100320a0751245c031000f07500000b210548001140716681c24400b80c2d12203400c02100354000701000c12a081c41188808044055810030b032181d441c04580f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 765605125 1250 765603875 765603887
    0x601090203060f0405010305010c1106160c0c0b16030206060409240632010f02060f1503100b2b0605280c08090d0912020319150e0a03 59
    0x600141650000100d14955100459807481000240c81403000d0760b940d0508a009008035084c40003c680e6182440300180c001003080740c8103903403c840c048201e941e00c25040300d14405030003040700d0350948041c012039035044190152282030703000d284801c21101686002410a04d01071300785070065082036509000a03900303080d0140801004410039a90380c1c2d0b240740320005051182d01c000184040d2034002446208210440c0c0041f54040002082c040019030045640042001e00000160030003c08258410f040c810940e411085d4287c5207041d10640c840001d050483e048501d00c001c6a8403a0044414203201d011030243ca540d02074100030b50a22003c6e54451a201114010901a6910001a9421400790240c5603500e01c1410303043c81c8010040c4024001d2207440004400300306008001130009000164600d48522070356074a00c800d40c0350406411a2441d405412a494014900d00c0040c080e2014280b54105025104c0e03035100d00c101040c40c0c022a0280100c103040f58006601160220f44c1101c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 765606375 1250 765605125 765605129
    0x30613050c0901140f1c050106090b0a05090d08190206160e090907091a0405090a05030901140d09110a1202100f0e0a090501080c0405150d0311030f1e0c0601 69
    0xc00c000e52500d5031600d190400f445a9442d04207200e0011a0003040b000117003014001d2003c0358041044079903262716050720780e00300c0b0f4401c403c1350090402003054458841c0d409012901009811808a0340e059541c00e1001e80241400200062140080580440e410009241c01000303040008d14859400320004282c1d00324100000d0060b1b8402c408511241c03c00c00c8420000c1003400340c10080c1030310042d001c0d80c1031140340b14954801da0502000c41da4000000c00c03884040c681c03000056190000050040d41c10400e0b50f14501042d0109010b2002e8444d01c5005444c4424455a5488000708180d81003015003003464115805a0722141288030060326480c118843c40c445904080c405004c02042c1103070705442c0c600c0c00302c0c0c00006144002030440d030342e50450780c10388000000b641c6d41c04280c80b003400115801251084034000329000724426505250307000c04011402450f01074000da050602c0145158458034804c0c1c442c4100180300495800c50820700510980108281860072110032a20b40c0d440c1018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 765607625 1250 765606375 765606377
    0xe04020f091902040303020313080105070903060b0105040b030a0c030e0706080a051503010c0f08070309020f0409300806040203090c130e070f030b0c0403020d060b180903030613050c0901 82
    0x1000030505884070450b0710707410080240030a65039183c480ca00203459070880d00455a00d015425070104548e03406004003071040f0300c0d655460010b07a15640b02c2c603016001d55480315040c05010040170800000d1040210700c103110704100450b130080400c03402812aa91104980810781100105021039030b1300022250f04801941008505a03d8140400321034207506803c3c194035610749040224000e030002d0421150441c1034a45003616555401c0a50a1300c65402c00298082580a8807407040d1405070710103c16140140c003541403800110b000f1211091562500f01e11002605814481003544498603662180c4252029802c0d030424110441e520044048240d10484000e00b61112203007099010b02c0303000d1094800c85501e030350303110864103024803a8041a0307044840700303001a0000707020504443c1225400380802034408400d403114170040000003841640002058460008013441d41400b50148102c04050760341c074146036040003080e0110038262150075003400204181042e041040d1554a442 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 765608875 1250 765607625 765607639
    0xc021906051b19060c03060905090c12150c0c0f0c0a1202030a0c0f180b0108010b0d020d29010305040201020d14040f081614030c12030d0903020303060a0e04020f 71
    0x30201d014101000c540600709070b003c2c0c0c00540000d1200b150014a0103882c191000c000300c40d241c01c44403045c0c64046821001c1075014030340500d41400c04030b00140340d5040040030760748442d10010000c0c020b0340050320880d003201c90106084566003028404e413502540210014410524038802040ea011410701c162190001c46040c40010340d201401407a1440b60301c203210590058171199600080f01007030003101c41080d102c03041625055824030500000e640141c4882d42140e10b8044a9446175004440c0c16035002c2d001c0c480000e00c100c55000d002d0054804084012080d80c1c030102000070100d002000504140c2000203100241c0d8000c02c451004401c0d074a01100075141c080b004800c9441a0b501620407100c0d041e400049803000072554800580c10b0180b140e49241c1d4030895082102031145600d5803542245070295990302e82901380000d0844400e0540e0305101c00701c0b8512044520000069015800001c2049498604400c40e0800340420341603224007810150049402d03604407070348840c06081 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 765610125 1250 765608875 765608917
    0x60a030611070204050a06081504020607171605071805100b090d05030403050105090606031b01030b01110604030305060f03191211161a03010e070c060b060a0c02190605 74
    0x81c150049070384107500030340284514145005100000e044a124511440c0551007070596440345071034542e40681d400600d83c80c100903044d11200d4490180700c5400c84020810440b101d0b003400b2180740c454900d40180c010704811841c141100808110b02041e40c0404c170b16200070004000751940e030a00940340300c1d214440d203d10401000c2a52100c061401404510001c240001017040540220b44500f00304401d54010341c44010505a440c00b211603030045402c01400c07030440b1548242c3c0141440141451700c2c1c040101c2c40c2d4012801d1440030b03901600003944510802100b07090104903044940c40a40c01860642004041c010794403000716401031000da50000105c01c2140b00c0e11851000b180703407038152201071031003140911107071029204503007261480c10310140010600c201542c0c1201c1c0c0241c40c0c0e9400f903440d510210350b450b203100f000325906956404418166120540508114521a1126162101ca50040025a4100030074072403118040030401d10441e41c0c0807080c2c03440191805840c0d11021 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 765611375 1250 765610125 765610151
    0x3080405010209040222080a0503040e070e120105090609071a07060f0c09080c01172802040b0a120c2a15020a120903020d1107081606080f060a0306 65
    0xf200311060780f41d0003070004c90043d916008820340d002c2494258240b00d500f03980d85114007520f95007480e10140c0103030000d0208210f02401451f419600410b58a400c0c40a0780f02000012031f52160f818460400da07540704100b080c907500c100079480d0071074182801401400e280c11400c4142c1c0c0c0740e4040c0254007800c00b08d03000c4c0802a0b55085021640d05089040c4030f801c1200c0c400624005d51031042d44818821002c0c0300b141c5502039081140e417101400e640714000e9480c03680011030b5041031b403d52040c420ba100214090b414071440500301a02e00c0d0f404541e569001c2c100c0c000d1070483c0d140003c002542c46c090702ca2180d19000710001004000751440e91544e261b02200020840701d5054004c2c00010401070300500c0b0300099401051100d420b134607444031b000c901c466030794200c074104503008001d80d010b9888140084d001da440d441080c0c90442c00c0303401040c2c541d40001d00f00441250800b01c0d42d03500407801e100c0320780c0246629501c01350091184071a850461b001500300300f09031002404e5550b0310700c01c1103111 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 765612625 1250 765611375 765611377
    0xb121e030f0a02060615120109020307021e0d11070f260607030f051806180a0c0305060106080c2b020d15031412070605070908060403020304091a030a030804050102 72
    0x508281d90680d211100305a0194480b541110070503c60001c080c0d03c0c480c044160f03419502c1c090302d000c1405016a0030084608001d60020f085e040661003104081040d180e1600e40484841030740c0b6019051550b0031010203400c0d1150b000c54801644c122000c1030240640213819901106c042c00703590401d041c00b0408002d514200201401102c1c00391108220070990590024440c410300b00c0c0b000c015941c1d400e01d15045400740b000d907448260b00310201140d8840d40d280c0403401d40402c2c03803054614441c0c082c1c0d03803259285280d610442d82170300300a004104103500003218940c88210609440d2038a10b800d03200700c004c0c901d4051610b80aa94040030b5128413980c81e410744404580205041108107a0201491400382d02884100c1c0d58a50120200b1141c8074040740304e030460360520318840d050168683d50040070780801007040007041060316001404403400c01026024a000c1c2e000f42d030780c6c0ea081510200580e60a968100d50340e01035011612a9074070300103290544150540362509440e00c451801d5806 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 765613875 1250 765612625 765612637
    0x91f081209190f0b22030b0417091008040b07021c0f0c080c0f013602040216031706011b060c02100c180f05061b0f060f04060b121e03 59
    0xc01c0360290013088003a000d1004080105442110f210309000000f49000c20030320a001c014010061341000c580000c401450403c4451940c1416908003416a404900314004195800c00000e04031010700090016160f840c0f504401e90748081c050310080c0005150b0b00c0394052840900b00540101e0310920648190602440741d40d00803041c90b80c5000301c151081c1da50515444011065203030124840242c00c030320081400701021400e00d0074210040720384015006884000a0b60407513000c00601980b000103251080035a4440d0b1103250711015050203010720008020031031030500c00c041c540104255282100305070300940c8103030b010a01240040040341421491111070440034104208048040d40090f4410300c100703014401174620701d60710b1040909040c058420990051000c03c02e1410f14444240c3c4d401c019542001100d0b40501220590742c90000c08030b0341083c1d54590b41e0b00f40002c0041c82d006050040c0d104644c2e10301045841800c56490303d000328841d070b08607101d025550019040510507101 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 765615125 1250 765613875 765613889
    0xb010906032f04291f1d0a15120c09030f050109060c050c0f03030f060f2803020a120201120f140f07081b120c09091f08120919 56
    0x3004036124403802200d48424522000e5203030340c95040700d03090f06010716034000c41c4911840ca0526260903000680d182041c0714106c084550307080e40c4159041d290b180c40710001305154422200d07500001c41000304403c8520407504035440c140f229084220307900440c82d00591b80c0014007450a0b5166140c6070303004160142c80144464103100d05100350f10317001409406503a0801050380c032280c410140b89074a0707100c1202c4050380494420003180d13a6062480d10344c94005000b41200410045507110310b041c403800d045000e80f03480381e80038081c400c50034036140750340082414035180d4088100550000c0c1500080348218807040b0342e5648046801800c41d044201194410f108490090401625501c1008000c035294801f081c0040701281101c0f041c5032501780c404445519031818101c1e488020f916000014145170040c00c3d0521017001d03a84d980200741405020300d00414000e2801c4503030b0740701060300c6940c44401160050150b0000b0250060b040301d006800480b1034440c02d82c400c3c00300c2148008180c10840f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 765616375 1250 765615125 765615131
    0x81815091003180c05150a1409240702011205040231020f340314040510020a1101031e05060604090509371401090503160b010906032f04 60
    0x141400b03140401d04044c5c03441641c0b081c01459407044070140354400d82503800c0005800c25080203841207040064003030702d080101031201c3c070f51000c2d004c0301c5401da00064209030408006004003c66820500804500b84542414841481d240d000191144d030220aa200544903802442c1511180700440103034801e41c1c803a00315240c42c0514540d4500d0313044000c4585101c4a144c0c44142e0309400342110040441c0442076039102c00f2001c0c3e4080b0f03610a00000401d6100505020101ea00da444070040d501c2d030721581e40100840329950500b006403000c0180c030a8103040c508803841440a03000c2c540c40c0d2010403c501d0201d11a11010007103403551045e0f505c03601c0c1192400701800341d99540460859404a813480714150861201410800244030220241641e148080288000100050311414620303c0400000a1100701601e51909580c40920481e40700e2840350b0700c1004004810315406d02400d2161800c000c000d00b10fa07548410003c0e0146403c09041c00c0080108280b201c061101c05c4529001d4424 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 765617625 1250 765616375 765616421
    0xe040f06051201020702240c011b1806080604180803040b040c0f080618010b0a06090f0e0c0708031b0d0609050a0e0706030c0219081815091003 63
    0x4020000c0d8061144200c0c2400c00340c003002d034014029180c0c04c94004025202c3c0202007440780075207034001524440c84d540c041c091041803040070b104048507940c041040c28299024100010141c440d01d03a4241014001410b0510200340e20215403a070001080c2d400189041c0358210b030004519141c5001000e48a00004100811001c100154010380c070842c0a80d03801c035100c107007a0168800c01e0145500c02d07801704000420150036805d62400006400d000020f9031001e0b4000314208100d207402002c08682034520422044600c60740040003044c0b94072000616003000f040c6804207110b81c0c81c004d829002c000c00441e5607451080260200d25106165213507440b05000402d4000d818240708280500b0316010000340c1c88c2841d4000c6e10301e28410540688201ca080c11401c0d4003e1405280c54000c40c884c01e4035070115040900301c2161b481d8000d4603101d071102c0c00c0000702e92555a54461041c0a0305007844283c0d02515064207490721000f04070f4030f035184220584011402860301e082c01e1161009260302d6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 765618875 1250 765617625 765617651
    0xe0a0b0313030207120503030c070c03021c1209060e10030b03070807090510030b270d030b091b0f28080709061103090d060b0d03080f010f030b160e04 66
    0x10074803520903025120b48980e20042e20780c0702d50b141c841c064102e030810000034124200490081c824a8420560259020703160740120b0000000d0124071207402185503180021b102010580c0700c0640d00c107141ca02411400e01c00014400084803150b94002c00035840396503149400b03500a5401194090104d9100395910180035548030010321600b56064588800f107803000c02101344880950390818482c03025910307418020304180101e030358540302d918030401c454180354009212080207200e86a03004212240c4a004000c440280039001103211110714015160300c41d071540030b444440d240d0f1083e66841e82e000522031000903610042c030401240821416032907041d04200c1030b0b030185107079503117050301d86031181c1040d11404410325080c3c845600511699141e0710b03080410030000c0e4031546007c55100031841c04100d03d01c040f0743c8110f01182200c0108004069100e0b070315170040201300e2005501034034685401601d0f61002d81031050b000c080c50070440245000f2210081213850142c000c00206000c861 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 765620125 1250 765618875 765618901
    0x2070902310f0906150c030e06160501110a081305120a08070e0d20060d0204030b010611030f030406051f090b030c120c01030b0a1502010f050916060e0a0b03 69
    0x1a80000300d0781d1500120f2400360511aa41c19200c80006034014a680074000b500c0c80d003654003007201000340c003042d07030851600e031000580050301d0081e425440c0380300d17a450160300f901c1140820b80840f0000f8080311075007a50248035103400a41028035902000d8442c140141001801e010110858200250340d034000c6034401c070400d2103000e503a0340e42c142c620061801c1200307441e00c862000c1c12000c60040480f8202d10380c04a05a020400101401d1526615070008030580c3c0050344203032080410800108044bd40141540014031200d001551900b002c00c40744041901000e4005800f0030390f1400044c14800104508a0800401040c201d0b80b080d40c03403442030302512200d00e605010707000f10300c81520582410002c2080c001d0fa048090701c0141000702c0110000c00c24440c0251780002c40340300008164004000c070199000d1280e0000c0b60703030601d041494040d100040c2109540b540f00821103146d000311400c903041501c6c224030b005151880d60500103102d140054002603041c1c20000107110b01142c0081d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 765621375 1250 765620125 765620129
    0xf0616031802010806041d01090c03110109030c09020702010302120f0106020f3403080c03070b070804020d03030b01021c09080d05030912161a0709080d0207090231 72
    0x3650034401580070040000c1c900c0021000240440d030710201154040c41e090f0004810b841d42c4c01e1842d010311034003800b007a0945503400c10540341024802c0c2d0600500c4a0050b29100ca840203090440c0d03540c1c9956206603910b0301c188151b03c2d5840c0d010481c8004c581c1300790100d0707490108582d0503d0392030401c403000302000380302880364a0141c03056051007151040003103490b1007240c1101d10031022000801101d000140e5001c4c0240910799031300100800050030300406004540310400003540c45182d145045401408003400540a120f45a0b0070000140e5455a01000303c40c0c0c180740101d440755584005074a058480703042e00e60b000d0b0408050040b450780c000710f080c0c00c0305c0340c400c05c8070840c01100806a449200c02d0314403003000d410031151000400d400500503c501820445a01c216800c0d5132200408400225010581c1d6280a03090000b015031003034502c4044c01200d00038003900d9103648806507407840c0c1440f1b103032816600820401c0c440300485140021200310030100e40c00140d0740c14080300e50348440e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 765622625 1250 765621375 765621377
    0x20a0302090f031c0e0409080a051b070f06030207050c151e12040b041401050a020a02060a0b010f0e040b04060b031b070c1809060c050904060905090c09090f0616 71
    0x1008014083c1c80c0001c0e086400710401c81c065144980c1024044500c40403180105422585414040740040d120400806c0c0007503182e80d030b40f0f0701c680b07003031021b00200010581c0c2141c199200e0007003031107042c6c50400b200c0105e0341c15060050f030740c00c880c0c80c00505000c5401c4415078000301640d40000c2880d8140b0007054108800101e00c103440b07440d24092280c900803403074604640e04107603001500080da01d8110319003090003100c040e28404011181c490949034111281c0c0c15403600401d800320403c0e010800180c200c8101c1c441401650710480009110400040300d40c410400040121000e54560f98012407084c42c3c0604240070494803030901200903441074503603421000002c245001c0c4d211000701582c94843d400a0491451440c0801600050301800c00301d40b460b5a1b1003100078009135040c4601d18044010751030f65610f4010210070070082787c0d101c1c2e00010402e03061404029180c1c070f005c6950780da0f000c0100c0d0000915142c503600d40d45804d104100000040c0309000600640c14071101c0c0c403412492076 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 765623875 1250 765622625 765622639
    0x3060609060b0f030109020a02030f070303060501080108060610030209150c251203140c060906060a230d0303150308072d020405220f0b07020d0504091509020a030209 73
    0xb403010594040e105441c2c8800c5401014001441003e80e560000c0045480c540304613800c1006007030605520b47d02074002140070079625002000035503000b5038a0380c0100b20300c10180255180240102c0c50b8041a85841d002301940051034002965a0941d44121000b0728035003141c45240f610004c1c0e589541082180b0240005000b07441c40c3e05079464414070a441003c00d40d840485040c0e075098880c90500302c0009640e03501408010200c1004000b541e01c9144501d008082c1c90802130140300021403076410665008a0f001410341100020141a000c134000a807441d46903130030b00d410114001d18081902210301c0840301000014008860b02809480303015003100140f40110407024400714000130500c0c1c5810500c2a43c9101528040e031106900c040810b4101c40b014030180d60918042c01b40c0201121310301c1000d100b5005110745080c920780c1c0303e40c413400201101140d0803000b4203180514451070342c0d05912100e804001020b058812801800058015911010705103c003801940080040c1401001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 765625125 1250 765623875 765623879
    0xb07030207140a0f0603050702010f0905100606020f0a1b050306041505062215080d090612060501080f090109080a0e180f06060f0c0613030f030606360306060906 71
    0xa04154070f401141d0701030712612680b5142c000c080c0c3c0501070003005a0190355030f603040e8203049003041c06450849482140030f40b40307809481c21210100c0b411078008908541c0f10903814040414000703252942e454000b40d2852105e102c0c070340f5031084000300f900b095806007d4402440b08000e000840b170314080c2c0d018641401243d5680041c80501c09040e011103844c02c00e030456007000e42c90164404e00c2c041e029400c007400da00d92100c04c1c00d40384c00b010400c841c00051498004101c1170f40c0c8211003140310a03046c0c005008203407500303000030130580e40074090a0032010350700045401b10001354040a000c55001d0840758a500c0c8000340605001e071850311050040894a401c82198100c0d221500c0c4502c03d21800078900c0c0e02c5d0311090005030b400000d800009404100403100d5401c6040141c40e104810382c80c0601c070106403030f14004101c1c42800e0801414113080c4401408040e03000b003002207441941d1900c201a041c20916402c0004032034070410003c1a4004102005000440d04906d069401c424000d0080c0c40d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 765626375 1250 765625125 765625129
    0xb0f040912111501210c03080a12020705060a02030c07140601050a0603090510180c0e100b0301060e010503040201030204050d05060f090c01091814010914070507020105180a0b0703020714 82
    0x880034800d12801c0f4040c030014012030000003041c0702254007010724031503400c1059440000c3c0101980040c3d411010100d02c400303425a00682444201910800039800d1a0f06652110381d10308000c0d000200183c0c000c00040c520b19100e6007540d1081d50462206000415022741683e180c010030700446001d5081c040303002c0340c00c03402400340c810387c2d40d030100041c8401404240140011302c0020003800d5542c8107620350b02c0124002004d01401390149001d841c0300d41c10114001c005219444e80596082c101c20310040284641140c0d1a8002c0c5031f080c24003650320b035224070040b0000c3c400d540080d41d002c115010403000780480069810b118249403003640c00e03c0e4841203ea244c3d02c80b1000e00c0b8a00160707900c031003800100c54201c00005c000307049200102d2514180304016000130b000b40c110010080d50b4040c07450b80000c0c110615504100b00c0d06280e440d2403d10380008082d8451002d803000c0f2040c0b010766802c0c01c1e403520390f00d004c000d00b101580c440c2c90342d0080c60025111020b600c1519821103c0740346140040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 765627625 1250 765626375 765626383
    0xf030312040f02030c2e111b0907020a050303010905060a0b0d0507030f0e190602130b030403030c0512010303030b130515030601090b0a030b090c1c0213050c0d0b0f04091211 76
    0x6c40c10812400e8040008441582a0005044d18108200d000070340d0401c0c06030b00704046032501c4d42d4405280e001c0b50841c000e01164280044c40300d01198014072104020490101c201c1c1d05481011101181e00d079035110104500050960005104080004544d00c1e648010340c007440c01800507540a11240420042144c2500d048090710525600310207031140781703068498100280e03a0301c00c601c0541401004801c080054200d80c0c0400007513100001040101541445040c408407100c0c10030328140f460030404081512014000101815038940603036406230f40c1c0396800c5400340c094460502c12440c1c10300720842100080e01806003c0e201c0d500000c0b50203401400340322003000d405011002002d04c0d5494600d071901001d051140c4501450701c0401300c075120300790710501d40d84044a03c406600000e00c1402081c1c081120a04511482c001c2841301d140c00e04002c03215103003032090b40415030400d4840040e0b8808143c1444070f07401450003140c54108078200448200c80c1d07601703480d404040c1061014003911 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 765628875 1250 765627625 765627649
    0x4050d0e0a051026070f050703091802130308090a0b031e060118030804170d0210020a02010f060f030606060f05030a1808030406050906060f030a020f030312040f02030c 74
    0x32001078080c0900c20b50511502c010040142454034041070b040d1004004640c0d040720608003901440740d03080200b1030780c01010241181e820351502910f001c40c01d482c0102094018050100032010585000341c009955406072075101101c1000341d24192769a03c0c0c403000075801800081d0003004203001c001500d000070300c140d921a00e803a84891450701ca0074a0744004034078009143c01c7c107201502450702905411502e40c100654810510241e80314105600c61281003000300400003a40c2c40401c000e0a0b441d40850b6030303281038081c40000f40c0c40d40d07294007090340540441c04240300c42610f41600000c95200608000c0110ba018080030007825840700c0b821118903090720811400b041c41000400d000e40d95070303400701582c2409200c5648030401c4039a15101039500c291825030f0082d84030000e10144500510030103402080860350740c0b05000e01c010109858040c80007000c3e1240032004450b0445480520440c2c1c1c3c0c1441d2112450094031701880d0000c1b138000c086401ba4024407403402044101d080c04941c40030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 765630125 1250 765628875 765628879
    0x6040f090c09050c0705160302011d100e0619080a060807080706050f0f0304050303100509010501020d0809070f0621020304080702060307090513290907050c0c130504050d0e 76
    0x140503420200280c1c00741c03c01030010001c09204010b42c001050044c0180755074880d2071041000345501d580001040784c071011000c800b02c1020161081c0c2281d588503104201e0700c0c1c2c1400c100010340c40d070f9000070301d1030701908151320b200d030074012020300340c29034031200e0035108007488070f010003415444003696640c4101c9400341c04841e90040d0b50038040d480c0200046c29115030201415407030565101e400312100e8005650454203548003209200d0108070a0b44143c0141c82e0940780d121066260100007075503022400400d2042c40086004181e03405010f020010183c00c26110071258103a0358280103003d80c014143d040c0e0310340a18804001501c1ea5402200d0003550090f0742345040201c02e40821549a101034140c1013440150303e0002880c1d112156030510301c242d540000142149400024078410048001c000e130a403564401d41d40c06566002292600324100385030203a110f501c804000d91511200700030b1b6135400901e5010001f00355003d9085984207610a406580803c1ca003160103031014640d000f0550703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 765631375 1250 765630125 765630143
    0x18051009120809030c0a060b010e0f010f0509030a021221091509010201020903010606080603161d041703311a0a110715140403080f040809030f0606040f09 68
    0x3080d040c2c860902250420000000c0e28034281d04001d4079494904828021200c198803200003044079a00007412121214059a20000b01004000020452106d40302800300307028010070b84201580781007081c2c107000f50380502034410342c3d018444241d6032803014554000020190741d154006560b901010340303901c84009000f044140f050b1074075088054020300c2c00181199424444204035541c03d0041d8401408941c840f00d0141c240002858103008200401c040450b2030b5004c10411580500c85504a01c40c4413905c4180710348962602c1c40d80c0301e00c801c03640240a08007005028210728403c80e9040c2551034925a0304114071034201c1715960100301d660181004004040406803d0201d94905610041c15a80011004000b0101c90080d0704a01c0c42601c1442a0112030030415180b485050b0075010154200380080c40c050b46e00518007000105860700b4617070181c000c242040f02050554000500050a031441a200e0340781a540c2c031101110a644a681030045450f0080c4c070700c0c403a40501c01c0c3c10100709 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 765632625 1250 765631375 765631403
    0x1c03020705010804030c2109080d081f0b04030b07020d030b03061801180c03060b0103290a09090b040c150507080f0c01021216050306060415030e0118051009 69
    0x56803000d0008000745c1c01e1143c1c03d130f000c1c1c00050125100720110b003406040c0344080d8501042c01404000c42e03030010f4040d40d0114040308101c6800042c60b55000070a0040c0d4007607400622004017078540184d10441d448080424040100615402468410001035086920860070000102e05a44542d281984c046c1c0204010840c000c40324401340c1c0d15940c646002203840c801c440b13810384070848600c0341628404500d840038401c200150103003820719002481c0c2404090304045001511085050709000c45814110b00700c049900c902c0140070003000c0106003003050140c80d06011030300307000807182110300018002001c5001740c85003d9201725801581ea43c83e0902000350780d038035102c1e4131aa1101518031028807000ca5180004d0000706240340b82d0110010241c1848031f1542c00b419003c071251001e1200501c10069582c942405581c115220049804940614110305034001c21451592079159424454402806e00317802003c540c80300c1c801c40440345411040c0c0e01c3c3d003086941100c0002c005107104000c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 765633875 1250 765632625 765632627
    0x110409052508010f050108031b0f070303030f0c0206040302031b070302060310031502070201051806071a071b02090601030905070b0c0705040f0b030601030213291c0302070501 77
    0x1001005500c69001c8400191411003416000180c0c00300446034003a002109110452082c06078031050894800140b005504203940c032502c03405448442a1480081e4a422085446c200440405070b007001c0c00707135909a903c83c240140600807600c0c42413041c50a004941d02e0980c80010407900c119015409941400c440078101e081e0945440c3c0007219a200304000800507130759040055009100071060081d00a14518009403480002400505a2072061043c070740540d8001c4102c810b00c498041721803201e5540000016001d0086000203004401c140102607503000d100e0300028021880c90306d4002011560307604452401c659603d0080d004410b04c0d003c101c255006e0740112491512400a88600326158800210035400100f0381c22116480000f080020703041c184260104680640c60a010680441022035528041844000d0241148441960320300c9070035484044041d01c15456012807528a0101000510a46400304d100d0070380c00b541b010f03c4001e0f00142c1d04c00c455260300546029440c0c500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 765635125 1250 765633875 765633881
    0x21921050a0e250e0f132111060901150902030402040b0d030314130203370c030b07180b0705011407020a0b0f01360203011503050907031104 62
    0x1e01c56655119803100c05103401c01d20020301165000b0701018141d41d2014488104601d840e0b0289003519640d50501441807214841c443c0c0c880940c0010500e865590b05c4c180c0b1041a01200007141404641c92440b680e50b0320851000c003420010381219126196200160300700d03045260442010000c846003048420041d07006158480c1c002800000c1c44003100c404148020f01c5075500303c0010790b568901e1554101001441904082029001c81d014200d9a02190380e4128811070f24102c0c3c5e0a0f404003444c030700c4451401580c0e000107001e50520284180ca090741740410030340011030b0030500d070000050300b0b80d220b42e200c400d8011103000b6039220301c0c4c5880c000306856408808165643e5403144842c4c03c0f00c0c0403c04055005100a074000c103500440da00748845010000380ca03a4100e0300c0e0f5079004000c00a00361ba4960b52000307040f0303070300800315440c0d0030b07103c0d8001a00e01070305642500100c000540a03d402082246c01625510300b40415030f21800c0c0700e9101d0200c0d0000600c1d48015141d6246241002d43c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 765636375 1250 765635125 765635131
    0x62d0b060c070303170f16050919060c0b0a020306030715170f090f0c0102030301150e04151503020f0304080901050c010e010f0f050f010b090112050a02192105 70
    0x1520180c9008410303038955041c00030b55001030f0003181481d08040200505d0a800d181e00c595459460006820160000d28075000c0c03042481e01040401300b050034560b5501c00d60703049500091400350f151250b0742d042c060405e00b6107a50598410768034034006000303019140200c038030a01004000e8a000703803d0445d030400d401c40c50900d5a0800c6445820303145100c180d18041c0b406602d007100025241c3c0343c103c170103524060444c0504800c9400c15488a4000d98002003030743d05448003c092103100070307003112080300c44443d030740d0500e03500c281060f1880d00b000b44082d001600390b40300390034006004004090242c060303105034100c2003c240310400018002c00d40d00d10241210410515000d80b90800120702d4a0030b451100a4819050350349000ca1401c0c049580310720000e01e48010302c20b00c218900b0044045044805120b0071403040c00010700644168801da0352410020981c02c0c0070002401d1030903011009410401204401c0404da4216003295400b40c00420300160009a005410014040715000501009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 765637625 1250 765636375 765636379
    0xd092108090a0f14060702010b09061c11030c040f0515010203040320280801240902090f420315030f010f150f030521190c062d0b 57
    0x120030100301085c0001e5000b00350726400032500c407001e9010801401d0024280522981c1481d030045d100c400c000010441150300151012120005400400e0401c10030680082c1d010740b40a120713481c0241130b03922450094a80741d224500d100c0e01c000043e07969204500000d0586e01e000341006c401401c02d50401135042c00050441480441508101250041c0c00c040301c0c03501c2c6200c0b9400340030710b01003440f41c107444000b180a008c0031a0721307105404c3c25056913030051103405500010080002c0d05c1c0d40000030120b0002805000307030311035a01c4003680603142c4135171403c241c065641c0d02400c44001020800003c01c42001c403071032960f214800104019214003500a03014000c002c6c001400136000e109100e4080540580400c42d103a81c0e00180400103065080342c0c84041307882a083c00030030000204c04d92600603826450141800c0711070380300901d00501460040e01141101c1c10356045521096500a59118940504c8081c2003070190056503203c030303101000b01f110210302034001c09145800200c190a00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 765638875 1250 765637625 765637643
    0x9030312090512030924010b09120a080309030a09121a130611041701110f07060b13060e070c0231020a0906110105130b04080d092108090a0f 62
    0x10300800a00d644c0003266804c4560304500c011200640c40c02070b0342c0d00c0503d044808807a0310360410002c10854021002194010300c0007102c401e465a004100c0c26401e1a040750070b02e80c072480c007041041d0740c03541b140c060304000505110001603c001c060201c0451188e0000811044400a080035220b80c00001d01240c00e00201010b0007001c2541c1c0e12581c05c0c0e480141c10203035650340c00c103102074801d00f1481c014901d6030380c50003070302040e80100e190545010170760411030641d450109003017180c0a4045000c1043d03128070b8140210242c40d040354006801c45800c5003098299541e4100c081e200c28002d40303c007941010091600b004a4942006c0c41508a04452281440a01d908044030300300d800c20698040421f58562040c40020b42203100e0107210100040280704603d00000050a00313501082e0042202c100400410100502341e01030340e141060000b0100b00e00c1c0c3e03242c20503c5030a03d1030b9400720a12901c2000d003038000b0744140c10b010302c608051802401140b04554959207508490034090b904203403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 765640125 1250 765638875 765638893
    0xb010203160c23150f130b1c3e04080c24180604081603200a05060a030213030b0402031e06070e010306080a060f0c090303120905 57
    0x48207403041400c9030b006035003070103145090400d6580442c0e04090203089000d100c60300c0c0c400740e9403110789040741442c1036446036444030044080e050841c0507840e100c4420f5441d141c0042080044100a009180d140d01c80e048001042c00245400329611450840080e80d10310b0080d40102d1101000801c1001c3d00c1c08604200f4a0901c038011065001b039004100d0310303005403408915500d01603881203104c2056600500650f90700051304110380c460150305410780e050460844246942c3c007000c0d10010140b510640742a848000c094a42180c25400215400c0402e03245800d100c0041401c1d404055402400d0810003d060108011181c0c201840c034800300f507001c208681c80d1400501d20f07440118891000034a49003403c1c810142000b10240d42c0c1744011030350010220683c18001034075500700c0c1c4a420310907244036903400100d0240c04640c00c41e020511034030640000304a00d5a000ca145070dc003480c003c120711480301c80700302d070101c140f84030281c0043d038880d407800d502824a5004400041c841d000300d80480c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 765641375 1250 765640125 765640147
    0x20f0307091d0c01170703050403020a08030c0a2d0507080f07051c02151609150221030108060105011b0b0c070203060a06030b16121b0f020613060b010203 68
    0x7a400c0b007054034500340d5030030035036200e01d010032206110b40001d003091206915080c840110080c80140fa00c0b007055122000308080c54001d10a41b01e032550440307100e40d074a10307040322005081e03405129514009004203000503000d11054040120b4070701c01c9050750840a0390a40c04548503000101c055804d09003c01007255200100002824081d00c10409000346020a8417029007042c1654100010364005003515001d91510100080d80802a20396000340912203c0c41100c06c031440350048401f0b4500034a4500724240c001914040700d00004c0340200100000d459688100c0c00280304100f070681c003000061100d503000d2810034030710201d00100307050b43c240d054032480c010643c00d41e0740e43d41c018030000d00c0c032007542410710100340d001c0d803000024070801e461350f0b580400000000740350031491800e28000490440c41650685489044000c00707100720b140c0752800d415444400300d240c0300800c2041c9a5044000d001291080c80303100a8880462004100d0b01c2d800d000e080c1e85000e260450004000c00c90b040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 765642625 1250 765641375 765641381
    0x140f09041d070302090a0b0a05010309050c0405011e0504020c030a08041a1e0a090c1a07061a091b070602070c0e0a06090e030f030c0c0111211003050a020f030709 71
    0x1c1c46041c01000a14618014040714000c054100c500c5981040101070703440d00d07804a2402103460a10300003d85080d03504255090451068040b544141003100000c0c0303001e0744030b101c00407601c0c1c2c010840150a50b03031000c1004911070b40b401010183c0007448080c03002402542075075481806012850b01c00c0310030001d44030188000300c8141905080e00c2140c1c04076100b003c01e96a910601d21181046141c01c680c8420b840d8200a205886502d841d040411803902d00300c10a454035958045d200b800118a800782c0324841803004c0c03030003501800412001034200032008148288030409045440e2801c0000d0306c0302c001a503c1140151001000154001020155a0b902070702c00c0710070a800040c00c50030314075501c1c1541c044c0c0d502d002283e401480500d200401960440790441811100142c2d80c601011700c40e400762840440154802c90082620043d00130b030b0686100480282494840700c0e41d0328504c900801c1c04440c08083d0855000301e01c01c50050810019550103d000242142c08050303480c038035181a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 765643875 1250 765642625 765642671
    0xc070c08010510090903120902040e010c02011406010e0901060c0602040312020102030604110901051b07030204020301120b060a03111018060201020702040f020a0e1504050303030c0703020d140f0904 87
    0x4036035503101085440f10510162074050100c61006000100650714000c0c440800d4448031f02c40907585260f24421035503943d001c0456611048000d01141c03c1b41440a40201740d20b1582c0c0b11002120400640e0540c41644400140c2c4c5005154081d1642411b20844501051600072503040b603080201001052034100d840c1340e200d80da41d0001d80e40389404010b00c802d036501c2101d81d00724031a09000416041e030300082602c44082004100d90000b0038003000e454608040d0b9403010390003c1c4000000f2800160040d05040014010100b6074000c1d1101024020040303902e100241c110b0112000905840c5000c140300400c5020030b00d0b0020b62041d0401140e20240901d600c04c0000d03030750000e04102141040d0060710b03285900e07007a045040080d5031034003800f680180003809214282b03442036103158a00c100f0690b405844090100c81c0c40741303401007070710710181d2040340c09501511800307108072a800d1149a60340722444d401e25925041040010000442c0d4020110701e561194881101c283c008401d4848910 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 765645125 1250 765643875 765643889
    0xd05150a090b031219230d051509240117040305130b040f062d0504080709051015020f120d29040b0a05220e0a050c010804020a0509040606060e040209090109050c070c 73
    0x101800c114030050b10030548102d510b4010f2b00700c2d000b00a5060b9078072300c600321850141000c2e0b8848001e03080040340e903000803090f000c42c0d400040051009160b4804068078068001640300d059241d101e05407090680141d00c0340400341c03d0801c100f030103003500c07680d400c0355070404182d41880d1441d40044815042c40341c02d100b800005102043c00c022101c0700700700000080c481c91300304000604040071a04aa5081400382d01040400841006007084c400c00861328a030345d0140c1940c0d9040c9400004c4140c5078007980c1c00d601d05604040d81060003902c00698900c0203140c100729205050341c54030501c4003801c0310040941e808a280000002c82d9183d40b02407200c81440f0f0381012180d001200d194400b101d512143d44060b07940206100000220001091299100c0900704012603944501c00115041e00c2d68010780c3d000b01110050004010007a00144140c2d074981c0c0701c1840078000c5809000480c09848042030380030046500401c5404006e600c00350704a4100c444040c94a420f41c0c44003615410700d517000ca0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 765646375 1250 765645125 765645131
    0x922020a0806011418060c0a081303020f0f10030f0f0f050a0f050f0f0c040b0d0b01082208131205160806010b0d05150a090b031219230d 60
    0x15613800f03000c4640410a48000a0403d01c50f00070800329501a641014018000000e03200c1d03015900300000c4c84016440010103139550034180c035a91896000b031104034014640450fa50800d0f20300003408007900c4201620003001d0500c0490200c001c0d141103005484103503503d40c50312a0180c62401040c940d440e80c0040854035040c6400d80500b11000b40e1101a200c920b45010b01044480000c119a0010f200e1441c403155501c40c0b04042d84684078030f070f00528006034005064a55102a9008214810000d032a50342c003a583d580c18420046250ba0a42d013403a0794070038510000a80700d48007400003209a8010845200c0d00c1d9039806002c120440e20a8a855002c3c0c02910078807a1076440450140c121703400949100c0d45042e207507c04600401c8800f09440361a0030015100d543c4c121104124038200628419403955120301c00802400050700c410f02074040e4420000700c84406804551041c0075070340500303c10003540c10040315443d421102c9041041d01001d83c0300c0d8180200740c0501130302400b4803000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 765647482 1107 765646375 765646381
    0xa0b0108011205151f030b011d09030d020a0908060a050108100618021b06010303050310090908040509070c0807060c0f0c030e0913061505010e060f0922020a08 70
    0xc2d4000c40180c5c1c00018840106c81c0c00d03040340c0c0003c80b1140303402e05040c0011810f4004945282640e0310800c03606111200130350041540300c4039407408103e0542c994040b6418284140d0300c00061580311001440811400c2c070203a548455501001c2200d0381c608000a440180c60f5200c0d449966404200d5949041c082d9210207042407010003616441d40c3c6030700d4080d100743c00079155840c943d10100004124020984150101c290b00101d0306e9051500e8001001101c01000f030607101003190108440c030009480e58040c100c600e115150100340c200301580020b0021101d01543c104100c031152040c004130b5000700510202c201e0376607030803205a6802d101c11003081e80d402001401603140c0680300040102011a1005590b000d0340c45110b000007180800280f80900101031141d07560800035180c5514050701d4441c071402a0200c40345818112085640403038010000160120317032203400f0 = true := by decide +kernel

theorem cover : BRFrame.Cov 765467625 765647482 := by
  have h0 := BRFrame.cov_init 765467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 765467625 ≤ n) (h2 : n < 765647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
