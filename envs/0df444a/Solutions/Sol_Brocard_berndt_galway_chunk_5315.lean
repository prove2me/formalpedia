-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5315
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:27:57.183353+00:00
-- url     : https://prove2.me/submissions/aa8cf00a-94b0-4518-b449-885b27a53f23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 955755395 ≤ n < 955935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 955756645 1250 955755395 955755401
    0x601230a02070e010b030702342405040f03020f04180308100e061003020307020a0803071805040207020609060307140f0d0c08060901090902010903060c0f0912030f141b01 75
    0x7190f000c040400400024400520300c0c140c2c0d10030740e4103401a1148280c2d044da0040203c214000180303070b0854103003101c40400080e0301750740e003d420254030551003040180100341d0f40181242d0a00100142040180041070012010030100c0e5410b5812000e104881000100a045031840071209003803260019000c1c141c1c031a00060140301104034644c030032500e60113182c001f80b00032184d0f16002004069584499807090f07005683c001d003d481030340c000741e00c2540e0b140d909070b10a5880d800026080c0780c8000c2d030f00c031500704c2140080c00c2c01c8604529002069001c2003203800f07902800341c070852000c000284080d0052404144034424114402d0740d030380400000c1601504031484424030380e441d00c40114600d500034107000d0700582000b0114140c42c0c2c07034210018040c042e5014203d040120014001000a165004801303100045842d0202001109000144040700b5644007000c03003c1f40c0249040440c0d0850b281403011b0019190515828030004000b0001e8800c0900f895004850040f2030565904194 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 955757895 1250 955756645 955756649
    0x509010b120d0c140c030d030f0e06040c0603050717160e010f120f061e0e0603030a0f05030a02210105031605060409051816030b06010807080601230a0207 68
    0x31100400080341070722060362811a003940e140416402c2850201242183d040c8550180001040319441c4000700042400d000005114501080c2c0358209000850443c2c020031742486c6502004010a190944800d03402d074103284a03da05040c0e50700042810248640d0324840b01111083c80c0300f4460510422114800001003600c400060034250341070050340c82004c035103d1007411680c0b05003a56440c102d40c00700504c031600041c6411542e6001c000355003034540d006000f07640400c06452011078903020007030b100e4040041030607100781c20801055005503040101c0a03130581451401c90744968071111030078000c7c880c000310a001003030300c0310180201400020b6014142c0d0f00a80c1650118042042ca070f00403610386000e8280c2c031140600041c89944202e5000385d901818802040c00b80860000d0300740d00309454003950780c0d0040414802030041c032218802c2a80c1040003840c01620619100358000c0852074060015810402c10500000c102c000c02c4003039590f010703410a0400e42d01c5140c840080d41e40c2483e8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 955759145 1250 955757895 955757899
    0x70807080607050325030f09030e03010c0e09040f05070e09160501020c0a06081518040c060c0201051b0a0b1810020906161a0414010e1617010207060509010b 69
    0x1440002d181103103d42c040d203005400030060743d030443c0d000001707001241450641038003c05d580c9504100116110b409550410f901980300e183c2902e840009050035640c8a0607104107006c180882000c0d640c55000c1510790050708201036030389042c1c451030140d007420303840e5203d0000500c6444c14001c60342d80204540d80385000c180110244581d40d2001a41c0713807400c1118035944080100c20800800d0b009020290380b01e041c081071408580c07251300010304081100b000d01c103442d5190504010800828403481e00160049003400c565140d034640c00201540304d07010456140c3c0c2caa0701020400b0341c0b01044646042984108004507030300e4480305d606070107400c0540840e00b03882911071180f50769400744201d52400c800074207000d141c807184814104040e982071000322401d91000510840c40c1c43c2400d80f10b03020310301c01d40030150340e01c081e1782c48213080d500d121032140500c0c1c0000081501c101d00344440082141ca1000c01010394051005415009008880000d0300302c506150402c2a41481940146825082 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 955760395 1250 955759145 955759153
    0x7030b0114100e060a12110c03041a1204080702040f090312150308030a0b06041508011a0c1e0307021905010206011703030c1b0f0607030b0d17090f0307080708 70
    0x918541202d4440b0303841c244130b400400c10413110f64a43d11501024850f24280725003c00e26014002000b0300e81c0d4002000740025400205003880310055000340c4101008000c0d05050404030301d009800300d2440c020340b009101d120001031800071500c85030000c0e8020001d49004000d481c4940c24040c0c243c5280d2a98605c0c903070328141c1081d11460760040c03250107403504904580d04590f90035825000a100d003540b01c6a200005020015500da180c040201c205206030303079844225450464442c400540030a4402510802808100b50345840001c022440c0c00c0401c00202400a11031105030841c42664000303508124a01c06144c01142061003d00c02c4074404e07821241140e0340c074ce102080c3e01000c0c03030510352242c0080020844051805002d01162071050160301c0c86d0112040400749043e01400c0c0701d0887c0d820003000c1040c4150544101703883c07100262022140d0308801c0e502d0079101c0f41c4400d440f03a500c00010400c0c100d55103c2240030000d03107a000e012119401c0d107521090b583d0f17851034480c10400d441 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 955761645 1250 955760395 955760419
    0xc07060c090f090f0b1e03161206020c0c030f10060909020d0b0403050409021b0c09040506010608090c120105190e0c2413240f0e1305070924020601030f0507030b0114 73
    0x81400c6421000c509c20030a0540d565941c060751048008000e940f09412601ca003541c2c0c14000366050510703520003030080c00d8082110100f81c4013142d10420955140c05942e00150300e0300390a11540c0c56100507060241d564901c0c0a031034030700954000c9a403a034404110120540b0200d0400c504040c0c01408440340525039000f040990b034400c49004140e500000c1c01040322034000c071082c58001c02c014040c1c070245201400411005030381c60810074510381d151014440960b058080030300b600c011035202408420300d08640f42e59914650042c142c042c4010b544581070700680303541200b15112082000b19618425464114003850a40c045c1080c4140c07a1040c2c245004040711400ca01c1d49100c0c4c0715404040014802941c0828402d2620b6400069401c0c50904524803407140301d124107125100c0940f10350606103409a40c03007108400400400001002080c59a000925503045950000b00c60000312510302d40a818040664802001c50320804000310394201c403181d070213003001c0f416a00d81140107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 955762895 1250 955761645 955761673
    0xb040906030308010b131505090310090b090c100e010320070c350a0204051609060503010b0301091805060a140c030412080604090203060c07060c090f090f0b1e03 71
    0x4c0318441e00c0380c0320308403800410003d0040e006411407480b1864240141009c40d9040031030b0074882441806112203944d813500c00300b08501000d036160000080001801901040d40201d01010011032000042c03003e80b9840e0b1074a603100b60040b01801030100452404100e20549640076600038600480c0d0581040002041400b40c80c2d86020207540051804510001400d1004c1d2038018101e50f089254000c101d2148050789aa00480e4060342000003251141f01500b80018403e1030b441e080f0303904000041004010441c190070a5a040d0303804a51300281e91011038145a803650a003400060481c02070700c0401a020115510801c00340300174425040441e620500805070500c01200c00400f040c0c03042c0c0300a00b0052007080141d0f0b0201c4007800024001046800007460410304903820107505500155020400000b03000e02e8840b42c015040c0401c09905001004102121070300802c204581d403025451800410358000c1415840c0c050141c0d08a03610394858110308424403030000307000b0b04c20159006150 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 955764145 1250 955762895 955762897
    0x602120711120f121e06060928030c0b09040c03020a1e1412061201050702070b13181a030705060d1109030f030d06050f010f180b040906030308010b 65
    0x10900e03200a008016801001c2c08010340002c074100802c8442481020108540c0880e0580500d0800f05a009800c0445420005001000301198000c002c00d0104100310349580c811000d4051180130140306079003504520362050003150b0310140840c9501200081c064030360b24020b1042d03a80950b0b050000d00440c0c0d0060f0b059201d0070815900241000468031000150400000800d458030300d0300c240240e880c3d10300b4801e140c0015400119411120050115919140716400d074051442c034001d12141c54410406521000107210300403550100140034142250444d004101030300d00104240000488040d0f40e070001c00c414a00028803c180b07407508201071030700089040031124001e03c4249850402100c1c6800b9081c152640030b40690b05206010756954144564801d02503681e00a60303d0f81c411207200c50641d111980f119009004401c6048a0780e640111031301042516070070301c4101240328080c8039900e450349a000c445030060200f0080f80303840c03840e00440c040324000e55910701566250502c000791 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 955765395 1250 955764145 955764167
    0x120a02070602120d0f330e160c0f0602030f0f0a05160f0c0c1409180a0605092103090d2c0307030c0608010f0b12040209060a1206021207 60
    0x141014408004410016004103100b603550036804507919800c01400c40a840210490008003410500c25441c484107006c2014014454000c078070a0074109455070765980030b40718008074204100940044c0c140181120903e01c3d096101408564a1800c4a01c445000400382e64041c0748a01220104400048a00600b4020040f03211406010b9581410544030300218400c10003d01854110600100749070240410051801d06c8a050410209108000781104018107442d07441a070400b00505065000510021440e8841d03000034060300c0f845405031a000c400b01040c5843c01030700d50361421001040000d03502a140392002c481d4910503003c0b0507204401d45108950031a480d03280038103c40701500700309911715107020b001e46e0000b80c1c5945502d2003814054200da00425103204c0100f201e5088201100c2c02847d0101c015401d08403000070400c9510006000a03110b20004004149140e81d080c8107440108000310700100c6064035850701d0f00c00382d04182ca0491403114402c0006044901803188040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 955766645 1250 955765395 955765423
    0x1b04020a020c0f01111002030610020307030e01051806130312020d08040b060409140106060f0801030203031c2918060307030b0c090607060b0a091a120f120a02070602 73
    0x107540341110b01888150741420309118100b080c560403045200c00240040103003004020000f680c1e07413605500780003165100c1403080b01158030811490003c00e0740591301440d200360929045c2d513214641c035210000b605c1c2180c0a19400900081c003445440c840030481303400c0724800d6052100c0b1510fa02000c0e40c480d08070b8000030004c21503074000540000c0b50061859400f2a00520001d0070109a450b0754003800140d40b5540381c03582d900c440c01d01801d900000c005c031002c0818030386050158119400b2980780d0007601103421104084181100d00708100c3d070012a034504c1e2118151122300340000c170410414a10340d4210780184020401c05100582d0710b800d5030b00c5000054000d1010318079581c1c810250700f9000307020201c265028007805d443c80e41c40c607004025407405581d000c5007116901c420008040400d500200600b4a4000521f140151181403020228402c40b003211441b5403a071489400d007801c904e505152805980d540a014409403009070035110350a900300c42d201500c41200342d0f602c100301d0140c04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 955767895 1250 955766645 955766653
    0x41e1211060c090d060b0316150e030a0c050105090301090209130219050d1403090301061d0a05150d02011101020a0c0507090b010e04020706150605031b0f0d0c090f03051b04020a02 79
    0x213011031026001501c036581d02074100c5000d1040442050041d00c2160030921040700d9415074208004c0d840700c105c3c44181422006410100015a11604505da8902c03507241440000314100e002d59400b90711091a09070090440100c4c2d150003208079100180702c2404a20078580390841c0c0700c40c411011940c1c401c0d5400604010404d0a2948038906007007038114411145100410280c2100d44080c01110010544942d1001040d071400780440c1002c030380209a503035400e10786400c000c0103081c0b0f80200c4e07420184c1517032400002c06503800102c03164000820482815800024036494107039005c03106145141c0a00d0607110080e841c1c0440001355001701083d2400226018a540d645240a9006084603403107200c00043d200d4905418042c45040c90f8080c101050780401044040c3c501d86404000000e04005000d15001e120b00281201e4040c02c2d4080c0c0140c0d0b0f41e8064100e00c02e001e802d91201400f500060444aa84e8a1a00c1d40d0348950072242c01a00001040c500100360501d4002d45120540c190050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 955769145 1250 955767895 955767919
    0x1201080618010e07050d020a030f0c15030b1e04020c060f04030311030f010501120207061803020c1504091109060730080a1a10050c15010806041e1211060c09 69
    0x64118036071b00741641c1c0710308800742c00000100e8105550b102d191140311180719807442c08401035141e0700042c8c012001d0509000d1103070006d6070f407815158110122524406030700c03402240480c4c000d0041c0f69061042d0f00c00d0b042445002c00c80e94401602c500d22965090055503e50a6007103054041900c16150503000c9000500c0b4960042d0b0a030307841010042c03030040c10314040d622084141c4866a05a6071206002c0308240240765051140b14481442601c15108441e000c41c03c91509102da4450b81841750354504441030020340c02421200d00c0c0b68010030050300d5440c58100b140c0c61842a182c0d0440c01c043c031601340700d4000c42c544903030900d00d11962030301213031a5a0100c0c0c5c1ca0143c4203400740b000034000039036101e0b80159034038001ca1112a2299581584404002450610b030284590194030344100d201d00401240600081e01c552141e070110070090766201c0303204600010094400000d1145207040c41d6003c50340c0d44210280f0b10542c07a841120400e449030308248110340b0540107035540180103200c003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 955770395 1250 955769145 955769149
    0x30c09020711040606080f0606031b07080c070807090e07050108180c220b0301022503030b032406040b130908310611030d0b03031201080618010e0705 66
    0x207403503441e0040300b505842110784400a070032107402e50040408648070909209003002020442580309509a03202031845c2024007030f00c4c20783c002e03241008001090004450007041650025140081552070031580c19644030015540c4544a500030040003038640381c00004c01d5440014240220341e01a11421010b1f1244007009001d00500c80c0c0000d01403013080e50310041900c6444a2003000c801075a12800d041c20a44080300a807017880754818030aa00502000c000450348501c00c103804451981e48104400d42440c0070b40140405c04103040d854000c09491110080180541c9281c01c640f5040211a03a031b80c0300100801c94080d024025040180000d94542010060340800b400ea4051085142010945018502c0030818481e8000300c548600300074010b0709503103c00c000090880c504140c8a410000312010b656070040c4c00c00d10304402c5e1640080221605d003402254480560520200b00b50340e11032980c103135036090582c1e62002e61040e1024040800320107100b0154030320040000b41c8006850601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 955771645 1250 955770395 955770397
    0x80402090606070b07090f080705180915161101051003021003180f02040b1e1012090507050a0f030308010b0c0c03070306090308151c030302130608100501020106030c0902 75
    0x646038014404210480204e02d0f028101c078410109540d40f60141402d0400c480c2c1014000e900c25805c940c004481441103544a2040d10301c4901c181032020042d690750f60141c3c0ca0101d0001814008803000c02c2403146918091000300c4011034561103c661403c6140d58072400c84000300c9043c001c0d01c6020f1b0080c00185083c400e14001c0913194600071501300300280c18a9280c155019086818107461000c000840c10603003d03904a021003190724403a00a0303601506082d1761420f14a0600c14001c048507402210300075141c0d0a03003200303800e200f001240e52030b2500a95030b001a01071148120280000006c0104010155a09890f81a5241526030b480c2c0040350f0b000703400680340038441303005000c2c03442c0040d1000c1040d04000e40c081ca001103500744990401906081e0083e0020000c4590300903400c20585424591203a0743c020a410a850000c00d420110024007440901c0c0740c1000240100085183e413183c005c5009401c0d4182030045260740d00c0045e400c07a0b0f41131000500d42c440c000802c0060280d01c0d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 955772895 1250 955771645 955771651
    0x1a0f01020a15060f06020a0209090d050703050d060b0f07051203010501020c010507110904120e1017040203010f0e0703031e0e01080c0c030714011803050f09120106091d0102040608040209 82
    0x103101103401622540100c0c1302d03085607080100181e200310405810352405409881c0c0103075400c806041c2e404100e51009001e4407070f203e40a001d1240000399814100d500e50300200041c1008142e035a180c0f14400b500180d1070344103e00568851240800c0501d40c03c04040032241200e5050300100508105030005407800e0b00040c1042e6401c072200e5103c0d84e419210544402e224038801c0b400c071681000402c1e40504000d40c04421503015240250381101c03010b80040411404502d404500002a1f03960302c00240508101610329234480c0c01c10b0900403034184002540b1090320701c0380d120070782112402c0090180c18040b1042900004504107114130140d400741d080b0b103400048040d195031411180c2c080140ca507610025085944103094100f4440ea01028411b580034a0442021320595100700c0c0c4009055005e4804c4900594000092030a041d55a01c0310b10042c81c050400240003003607689494070700501c40070b8402d2031000002183d04110070418402c980541f1419158482e10b61115020301485032002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 955774145 1250 955772895 955772933
    0xd020406050603040f12020a0305030a27241a060c120310050a0b07020916020313120c1706071b02040e010c090b0408060c090a0e09011a0f01020a 64
    0x1000007051640700e0400440c4994010f9074100c03920380140c0f409141c81d1081211030821508001106030020b81d104003100d4121070181c001092250703000385000c10705a20342c0e0744250206048081d64080001c2da9220340040c00350300e01100c2c08100c0c4142668180d0f04401444001d100120340c0700c0a251805d24081c10009441c0e03402c4070b144680d02400100d1550007600c04149418640604001c01d14091941d40301414a07a2101c0d410010940c0c0490b45440300a003003500b8261000462400a5200300195001c105844a940d10100d941d0428071030702c82c00150b01500c040c103160902084c10300c420007403048080c0c911030060140ba5210403044403200b01c0541100303450303840003c076400940e6540c0144100f0b10102c000009403960b00d414003078420000b541c064805410140300030010030001059250f0f1200403d00c0d0b5039981d01641000440710301d100c0d0422900340e00303139909205400c00154005801d03e0381230103e02e00c1e006507003010080c1401c0050603041c010703805a01000300080c440b47c408172480c006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 955775395 1250 955774145 955774151
    0xd081006320c060c04090b0607050d0e220207150b030d050d0204090f05070f02010b010e1504031a0a0f0912050a0c02030601060f1413030210120c0c02180903090d0204 73
    0x41280c40c2d410400d096844906140010078241710000f4180f0884d601040101d681d0703407900003140c0e11241c0300d160340410481407040300104034640c0c0c1c45d9032020849482c1e4001d900b031040301d12031548000942000070141d0b0319140303a14004501e031100c2e00c640d11110000800800310740003c0c4204aa281c3d10580e00700c0340c220380900c00014031b03010130f004405096044030004609490300389070050012662401d80743c210785c18008540601d076000001083c400c6000e4401d81000012403004203800d00c100d0388001c01d241006139012070081649100d01d80030320361140d401d100c001d01034810070b0196442d14030050000c0144a0780480254000c1006140c4003045080c10a242016500001e040c441c00f40e0100d00800d07040717258010702643c0003982e96800030000744954101f600502902124064070700000340501c4e1480d84040b010360040e100803000c400c1188041c05007414003c0700410ba0f1005032002c034012000d8900a0268901590f4624031464480c3c0046060101200400001080d0541c01380c0e00303d66 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 955776645 1250 955775395 955775407
    0x110f090f09012a0f020610090c14070b0106091a03010e132001020c01112d0105130b0603030c28050a06051005030a12200d08100632 58
    0x96110300115640d0080790304000403d0000d003015101000030b6403a402190040020000c00c0d2412113001c6003038403101000010300034040a000d65014104420344c42d80700b000404e600d801c020b4039041302410785081e0340d40e61402540e200030b2801b20205124001000c43c20070b2005003c0d04040c8800380740e01032102e0002c012851165100c04007120004a214150070030310b14165402d658041000c0510504203282070410901443c04c1d50781c41d029908441c00100c12405540c001011710f0034004210420440020801c5042c6003000e0001c0058040d02200c0245104001030140e14010069036401c64040020700f460456a80026030300c44141080c00f41130340c0d4078040750400310708100210315040c0d11602000988c2c3c02e04442c440c07241d05a9900c114825440071440ba000034015041d82e0100d0460380c14414550b2580031804481024070b803e041c0400d228120fa603124456001448502448040515080003511150200c40346040d01d103881c810196401414400f03007802008080d0052700030b41840341021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 955777895 1250 955776645 955776671
    0xf110d0210030515010908150c0906030901020304061103192a0e04060f05010507081606050405061f080a2306090601090606022e090816110f090f0901 66
    0x864a5082840025640d07010002101c1ea515070910a2401c00d00f0501d100d540392000c608d43e07038031140c404000f40e03552480100c0c03800480001501c40013500102400d489103800013445001750411101510b43e50306100032405401000c0d000c4034007981e012403c01c2d000c0c900301640800980500c5141080f4041c128003680100c481c4d890103c40081e0340c84c0d60300c020500c0c810341000709460399504074030601c080c801c0007001142c2e000001c50f000c181d807147c04592039102010720044022484e181c0a84903a040c0f004010821201081d000d2081102c00c0d50511600d646c100725070b215184901510f00181d1020303061002080041d000c0d00302820011010b40348001000500604140041c0e40c0c1280076440540140041c00399801540041c04840c03006003692502d13100c5034903007514441d0420800320040c1c0504040083c01e50004401160000311091340d03100d0481d0000004025140c0690300900006003281080c0380c02c04100b03c0c2282e00500c0038616444800a160f05640c000e0303c1d0800b250341e15890700e01c0e40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 955779145 1250 955777895 955777909
    0xb0d1d010e0d03050f070801030b070504030204330e070e030a0618020907050c07090b030a060e1e0a170309100c021c08240a050a0b21040f110d02 64
    0x40d00d22600602121070482c0340c09016124040c050020499020040224095101d00e1090440383c1025030441c45450700301c000d40c3d040c41240c00183d005401c01802030300310000c00d00c05034982d04040200300d58030010b4908060340200c070360082c0101d655a4601140361148203404e12030510200600f90782400705a543c600b0704855807e019218060040b1448030309528295542d5607102015080462502801100c10398450560303015004a456a4034903000140e00c0400a18448540c8200c081181c04050360105680300c4012001c4181362601c81c1302090035081c04101e801e17460713a02120b803c50384400e1a002c9006034100401c0c40002d84115405482c01944a01440400c48440e030081d1040412400004194140c104806014440c502d01401003036816641076010b814070600f05d07002c2881008002070051207459022070b501941d03d032404a1107405050040040c0c0c10111607003041c008219a25000040b4200c070058424200816404081141149007120040e4000c15a988988159000900c0e0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 955780395 1250 955779145 955779161
    0xc0d02150d1404111219030e06030702010b0906040c05030f0c250b15011b0c0f090501050a0e06030d14041206021206010813061a0301090302030705160b0d1d01 70
    0x1c4500070001d20040c000c0600d0040da41c04d0041c2c13103c00c1d00150450072141c1c0c0b02c00c4254002c201483c456004001c0c540f1900070000040302c002c100b80c0d03a0303003002207009000e011001c40c0a0b100740d00100120b8218078080c0308074408810356888250840d80c40c80390038040068010710b844600e4104005030000010784d0f25400c143c25a081d0280e0783c50150074100500c0c1c100c0300418588949100524201d800d03030700702400c0003100340c1c141000d103004c984030300e00f6a8506505078440300d400c4c05810000304030014150082d9040e03071002c3c5c3e40360300103580e6451525403540007501d0040c0c060b001800d014806901c82c006d4408a01d01c80f441251400d5914460134a00003441241036840340c0d404910541c3d034240c6000c1c5160080b10034640700b941030a0420083c00c400e10a01001460a550380c03e0409000c64252080c00c1091350081c0200441c40250502940749c0e84002001c40c0c20340180551001003120303102020082c2c5141d45256400e10201440a10080c01e00300349046003006807014146030480c0c02d00a1081c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 955781645 1250 955780395 955780421
    0x8101208130b0702060f07140102030a0c1b030819022502120610060c110904030207080d0201060630060f290910140f03070f020c0d02150d 61
    0x240d90030004440201070318180d007003004010810841c84001d82d60305419901303c0100516001c0e40d5480900c5c01d19481200c5000c4071500d9400401000100d40c916441214005020b403036600200d0030040500c1c07681c02c89a00014003040514000c52080742c45203604190056004500501e09201d8400c44071310040c20078100e00c18807083c40d038440c1c2181000c3c0c1d10034243c00c5000c4c0c01000242481300c00d95945c800f5034040e01080010170020081030082c0080c401e078425001a044aa40d400c142c2002034603030340d02d405035003014481c1c4003043e45d4191051281101b181ca5503929007045c5048214603803108901e1000380b480060504079058414080d91140e50001c0c9408030381c5545892500e410f5590417016000b40d03400ca9220101c0c4803403140c3c079078000c5888a19017100c1001a00f08110800d4031904044403c0c0c4101d4030010411103030411f81500214007658041d214619042034800e4200e075605040f44115401c59943c0500c800182410900072141c511403007146d508180c1e00d594010110fa2085140074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 955782895 1250 955781645 955781647
    0x101a160503130b0a0806060a0e060c0d02240c030408040e190b04090b0105060706110301030807031e0210051b0d02041e0f03120302120a0510141008101208 68
    0x40c0880d101c03000c03060003d2841809103800c20f114544c2c0a4503190000f0400350098070002515210350344689440314000d00028043d41d10350050807451665004a041c1e064050320404036000329150354003079207045680e4940351100d581c1e0f6414254040c1da400190045940020500c4041581e01107041d80c0c911070541c405480c1c2514980b080c1342403d5075009225140140e1504d500d690120f00c5045c505415541c06442c01030340c80715545003100040005041186411001000100803c102c3d00010f16003d40a0351b50b80c6d9415004101c0c03440c58802c0760900c94050381c0706001c051100f0300250800e51f84503083c108040c60b04c8040880380885940803600000000e680028103000181c03121025481c40081f22001003a154101602e4010004803800050042d070b1080c0d89108545210360111109a071421160000d1406c054500384050f0005496091481040e04c1d0f010484414000960341800b0b0000e0003130807217110700c0d041511108005040ca002d00000342c90049104100201d07000613040c854100720f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 955784145 1250 955782895 955782907
    0x3030f02121515180303070503030c030a20070f06090624290d0209030d0c12030c050a0525240e0c120114010305010501090e06101a160503 61
    0x6071107100b041d01d901610803004070550700c0400e041103058542e03a03880700c02e68015120910000924600541d00010100c0c80004204200d8441210285014200e2404284070716a40080c250480e820f400400d0030034218184040408604203c815030242400340c40c001030765800a46913031040d20081040380c1c004965000502c0101c11040c2042c10052100f4a50500b08100c81c91141c541d215200c0f054002070807000c51034920300c00b126030480707100c9000141203c03046261a040640310302324090081e200944841401751501d8003a020340401031840d596600d1078090084010388298010005003201c081100ea89419400300e080d50920700907000305a10050b00482070751138540011000c507a524141d060048500360f4000018243ca4048000c031ba01001c841c58109040d40104107155a0b04440300d4001c000106119041d070040d410b0320b001d10009d0200c28074001200d96206419a404035003020000010003080395030b8140075600d5101104101c2c41c102d03203031083d50764411060405a980740c10000d44 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 955785395 1250 955784145 955784161
    0x7020406140f01080402091f0b280203070b071b0606030b090c0121021c020310140604030b01120602122e0503060a0b01030b040906020403170c1903030f0212 69
    0x5040c0c05140b0920b0194120315117a400300b82038130380280c6110740d072020100c00102c0e0700104c01928809040d442c2c2c8280d84544905045899400c020310b2311179400300c10b408140341c43d00d1001c8111990580c11006820650701c509608a40000000d58615000810606180001440c0d40605c0e0004c0d40035100e094103c0c18807014240c20103110000d01c80c18407010b104500f03089050043d00203142ba21030100141c48400c11355014455021a803142450184000100841041170a00a40684000080880c2030703449039401d1021500c1940406031601c10b01500400400202c100400011882090050300b062840c6050160f180c1d000c2d03030186100b060107090814489030ba04840b4003542000361041e6003461034980800d45400001d045024003035101c240c69070700c0740d0281d0001d4258101c0079004000c0d0020303a04151000350404d02044458040e0040945115040e5800792020f520512020303201d100011130000111130b403540412002c3c180c0364080e4400c05542e0748050194000701640088a40c40c00d810 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 955786645 1250 955785395 955785409
    0xa12020c030c101d070902090f040c0c0b100b0f07050f0312090f070303080601030e0a02030607020307260405280b040510030c022104080703050106081b0616080702040614 75
    0x84204c400d0350314443e2035104103500180c208100c54030302c4001a03a03040c000002c1010140d5141005400909002d94013814513403041480d6044c0b40175040101482c1c80f20441060391482511070304075920410300c61400c0302d0007114010000c851050301140c2c0d01411070540e4908641100b0a078114010040d800c115036100d0520040680b1000030010308034080c1950340240c41d040020301402d04156980600000c0000104510300500d030f00107046640d14030708820029a04d522102c0100c0f4045503060455402122502c207030b60b071012240071120f09250410b002d00c01c503441c0e07104590b4070b40140410408590300e02c01c2c0080010300342520303210fa035031814802441042c2c44c410402e2401c0600d012041c1d000c581c0c1c04166040d142c0b166001807030b5440403442d181d42e8a405103800c0a1420700403110000b08002056010000f01c071b03104800d6a04a034102c003504620154001c12982e00300404000613000788903003104e118980c6106440d034a00341000ba0300444d04031611032700600c2051016210504852600b92 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 955787895 1250 955786645 955786661
    0x1709131802120109081c020c1c0906020105090604062f0a0905012105090a06110405040e15151c0c050307050d0f060203060114030f01050916050a12020c030c10 70
    0x2c00280305424181e59101494451a001c814004031000c24142c080c5034150110f90f09420710004450710710740ea11030000b0042c42c1c1c175100c01c804203150346000100e6030300601819108010040c0540183c0e503650b20380c0e6000d030503440c03100328040740d0301114030701e0445a041a4180300504400419100c0100101c05441600e140d0003160600c0384030340d440350503003985000076003000507074083c00315140d22560100d6280400c25140103142a091001601101e03000c01c01910849604940c00c0c46010151b10069846012500b9414011107000c00040c0480603421443c015915010b4101c004640151040900420642c103007100d0210000f4030030812850b080080e00c0140004071103d0041414542d42c107440f82d110f050008042940100c00074840340c0c041d040e10040c00720b910009035900e2070007101d5170020780c0c02401054485c0e241079000c07940e443c54050300e40c0880121520344a1030a2000780c0e0648510183c5039200204076020410b0800708481031003e0040141000000c20501101459100503039603c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 955789145 1250 955787895 955787929
    0x3050a0507060828020f04124b02060309010c0206181911040204030b07080108030304020f040513060f06090e0f03030c03131e0204050a05041709131802 67
    0x50f806001100700d1440701c14040c543c00840d0002e04070310000e038a42c040e000d0000148000384010a00043d404d99803503c0c105410300c101c3e00017081500545403c0c004104100001c041b200899481e02030424030407812622481940308a102000c82503400100d450f4012201004203944811801268a404000141d000005d08110120f0f00000107101c642c1d40b91900010724401080b00c29400a110040d10201440440a40159900e40e181c0c201200c40c84c20541d6100700284081700009510100442a680240c0c4d0050184a0381c0543d1000c000160401420540c05040c2d4140205e00246840c0308000c0b28800603200032418900d40080354007102c4000c82564032581103a08041d1003000c0110440f540480c030051000d450b074807150951680c0b40301c114002410111741c01c0d0103180c0d2521125459006520803207003800f150f5226054627007501e4007510004c24a0001816130341c050082e50000d0142000041c24030300101d5400d04c500070544014407460000110313a0300084095080c440c603000070716552 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 955790395 1250 955789145 955789157
    0x50d05090c060904021b060c0403020909060712020304150e010609060b030f280e0102030103060b010c11090c090d0b011a030f01051306030812060118030807060e031303050a050706 79
    0x21940490841c0c4a500d42e6144240e600083c08424203442c071608492143e100407c803903051900341c000e00956805404183e2080c085080000d20322240018294440d181d02d030740d031600b41c00304982614060342015108995039170700814001da81021130301c81c1c0121142400c002003a551301d020008421101c07140c00210407036500300704200c1d1003240b80051a03001241d55402010300b552140501d82c0e00b00071100c000381040c0c200304401c0740c01300054010b541a64000d500c1005803002c1c0c14019200c8130035528000300080d000d0700040c0312502e4040b030300e01c0d0b0140d2100d0b50689040c0b1600b0004019201c14401220a02d48c00c0c80140120422181002c0661900702e550902c0c1d8208454031000c42e480500c41d4034131422410791490a01c4810790040b000660740500056110244036114007000c1204440035400070f440890110000a0520304542c02c9030f030131004207844e08103a504c51001a1541c82000d166512080000350300200500d040d8030020760151001d04501501850700b142060f540b60720040c00c005c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 955791645 1250 955790395 955790413
    0x1b0a0c050a0b070f02060706330b03162106090212060d0b2d090c03010c031a01031109060a0917070f0b0d1103090f19030203040e0c070c06050d0509 65
    0xc4c410490136a142d01110400e854040758908080540340080003e040400404041c01402014100212159900d400420202c80e110508040a4001111001c804812201c20500d1b07060144401d00000c014202030902e01d42a00c03901101650382c55403054071003d6000801e90189010388503100d400620480304000c81c00895114090303600005041501c51904441003211552a1103070004a405425000c0300018604030340c10513280c1015030000c1d802942440b0140380c038203102e4420180e4006d800d0711404112440c0000460082c2048114420410000c11519200da42c6510240080d14103543d41c039040345003012003001141c0c0d15517000b0000c41c1d0001400740100d04001502c0c0c000d0f1384207207840b59102d104007503210300130300003c61001d543c03e1000414403091766004a24002c81481d05c4084a00d120100841780410303151701900500103030021711051000e100b00c001c40c42e80029a1001c81414100340351034000c800941a880f5202003903002400b10601c12460280e1503010140f0310117490721034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 955792895 1250 955791645 955791653
    0x112050c0406030201050403080a090305010906050708071707050c010b13020c070f050d1217010602010c27060c020a0801050c07170703140306040e060c03010503010e070612021b0a0c050a0b07 84
    0x3007c1e5020003011424007240e06103445125210340401542c0040080c0145e50f501d003001ea0003080181c950000254100000034102030040f098526a90101d201d000055626000215459003141078241210354952440c13006640e60b041c0801c481d446003500060b681c82140385114603000603907115a016505040c02004956601440c084090b600031140c401e0354480c0708401c65010750a0140b19a8401d1102e0010400d50750540c458401000540c4400b0140f100d069201c41c140340d03c1c0700301c124440000c05024030001e4450b450040b40c8610140030704400b0750b1222034031401d44504550034017100901040560510030036116201c500000c407841c0d24a400e00a03100201942602045003170398200c000302241650315580e0001c846003000f101925811b041c044200002540280b2506d8130a41c2840300030a03c3c040080784a00c1241e103030362a419400c56200c0f034010040e401c410015902d02d9021005400c1100c802d200016003075106106608003a4100410000c1c0411039030451000300d601484420002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 955794145 1250 955792895 955792897
    0x1080709030602090f041a03010513152d05070305100612050c0c030408011d03121503011b0507260a030e0c1c050f0d090e0907050402030112050c040603020105 70
    0x780382c20000c09a540c4c0c14003004502042050300c80d403a04145007100703141c41e011503030b110701d486c01c0340443c003e020039220701c0500b284000080502400301c44503410f94804540c01e07684103100108550f603c3e000c1103080c609003689105800400d1207241c5132514100b003001c80c0c1c035114460380032030054640c2c284c050500d00f006200500b08038949102907075401c08215400c100c01c090b20b881212070310480b6034480e201c0c40c119000e01407016002800c002d00e0f0b1805082a80044169035072004c1800c00c40015a407412003450280700920001500340d50f8034043d0100603000f842c1705201d0062680c65442c0d5030380180c0340100d820100c5061040c1e40034080c0d07003a00001c034091401c882980340d00386070202c0c02c4103030002e146041405000400d40e1180410032800d110100c4c2e40b0101d0003860051007a84c02d0301c0715141241d611035803030340034030400641044028003141c140f078103030303250855460f40454444603100c0c4082801c03a0b0003a000340f54111107007a04542004030070401403d68410682e0700384007031480e6034000f03452 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 955795395 1250 955794145 955794149
    0x60b13030c0518012601060807050f0405010803092101060e0f09151b190906110703111c02030105040803060316140607050a050d030b0f18180c092401080709 69
    0xc0030803032540145d8040e04a1444c01c0380342c82c220007000582d0703841074619541c203110700c61603020b01105080846a0b00d0140300e03280c1255100005140307001c07404000c1000c6580c1010303200d0241207100c12030350b403030350f80034030400018003400c8482a400c0e0420744201500740704010603011407940304110040c04d442d04c405040780c004211040450300f02d10050841140360040e4001c3c0072020b40329041e580c000e641d000ba42002290843c2d216031011403810310a043e03c07005617000142c8480c0c0140b05010b041d0a00a201c10b1280f40c0c601038807104070072150f00003429140c007640d081e1641040401400503500d41404205c0d8244011118000c200785040748802d824210001400e218260102d000424401c080c40b0094801c0d91140235541d42e0440c140002e00208600886180500b90a820814481c20104180c00300c0304003a00a031002607030340d03658604106900d9800c1c100c1c140030f01500600710703403201ca00700390007401001c000780071110240001000c1d030098481c0e038904000a04041c000c10f540c100e102081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 955796645 1250 955795395 955795409
    0x70c0201030509250603050903040b040513020403060903020604050c030c010215060103061a0c1e0613080d0e0303061306032f0d03120f0209150904060b13030c051801 73
    0x3429900c01c510719050843d81e6090040e014003411044d070b00c8114401140c0195989500c1c2040b41d501c1304c0164581d40c0c0558042c40c0300303603103013040240541e240c42c00b00103040440d0040054a00341d00d0f99160380a40350050340480140e40250305200c1044024804104403010035001802c525260340c00013540c0d05122542640f030044ca410101d003446c0d02c40e402136030107030030040e80903400c142180d643c02119901c501c03d962a1801407440c100180300b0690410502c1404200052010f5140c04112080c00b190480e01140d1100080001c01f03807460785d6003d040c1c0c90307881d844045c40d00c0785800030602550740d4412254040c41031800e50f0a1001a1030041404080204030f400c0d560f00c0191172081600d4500d00086190307111400c00ba001c42010b90141e0015540454020148a11107001d8107103400e9001e4a0709165200701082c00c0407140c101e50001800b01003000520105549961b000131000a91080d50380d10343c501c00b083c4040c020301c181c02c1000d5000b85415a14084c401c154000c1c1404c010906002e064 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 955797895 1250 955796645 955796651
    0x8010c08010e090a0b0a1d0a1101030207150f060f0f060e030a081626071a0105031b1c0606030c0b0403080f1803070e0a0606020714060a02150103110f030105070c020103 74
    0x101c982007694051501c00040d58600d109140594800c241d036145803188c203d0b203a1030f00a04072047c0d0351103402901d000c1036128a4015203980400c1000000e4998030b50202d407541d0340c542000862902ca418104014a05070218201003030500c1c2e0000c04042c07042c0c05c442e010340e104081401c000f40d041d20071030703202da58540ba49407100480351518000d005000e11000031141d5058420840c5950114020004c0c107205110f501030a50140e001c044800009108079507141c3c01140961540010120f51800003441c010042e1151030050603c0b2200f29400140c143c4e20241d0301c200500420442c075120501808000302e01a007043d19580d175040740e501c81c1c0009090201808035648005007041c242034110741c20300400350782c0900e843d00030b041c0321004110741c80786459003840c00024030240003142403010f40b540c141e4100340e0490040d080c081540c2c02200164110301c56500f28001400303500c511240030f984500192140c2d000c800d001c0200071807401e40843e1013a40340c10144440c4a4008102404481d0b0a081c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 955799145 1250 955797895 955797901
    0x11505130b0a17030d0b0f030d050a030204090203101e080303220503031504050105010c0809060a020312011203030f11031302010203090d0614071707050c01110408010c08010e090a0b 80
    0x10a0281e032141d4410f03201d011038400340319010ba101102504a0541d50b0100308050000c0c54100806c41c81c10649158142d00b00f072107040c2c2e00c548581c1c014070402485042c00361400d45e80f81d600004030381c0112a010901a625841440302e0000c0d03100b9809540300b0090943e02090a15030480e840e88000b40110803941841c100c010f00c00140c0300d040126446e0400c0690740ca914042100601c00c00f803182e0658440c3e03241000100f12507008021821045800110007030800700110140021984000c0125080d48010b00504021501a103034031406081c81401102108805d858064240ca404406410300c60307041c0b031a81e0400d19030600c182c950054110a101160b90354500050b401c0d840358003076843d00420310f4065030041c414590400402a0140105112a5510306104072403404451440c0c1911485c3c2c0c3d000b04a96500c01c4001d007a802c0c5050340005000b00c92651107504561099104003202d946527110501110f41000301e050040c044c4148a030500d03c1c00690b4240c541400f900c1c0106885403003004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 955800395 1250 955799145 955799149
    0xb0618070f020c040c0302280905010c02031507050a2607030b190b12150102060c03041b180b1002190c0f0f0f14010804030c0201020c130c02011505130b 67
    0x90040f8400604104002400d00e0ba00170702039444080c4080c805041c4080c0091351030f00380b0013003024a80c00c9650301044a410000110ba10500300e0701e081e64944924014005040c0041d45618000c1c13246403156035031407000c1c0c42c0c09845100703290b02d61103c02c0c00020300c0040070380301c0c242c40640c041c04a140000d140081640010b0610801440c4290203030000c030808555400e0205c0148450040003400c822155030301c41e84044001d904404030782c0160020740104230a440010040e5820500c44c0010ba12545021341255001c0f1300517034051001a00512140d41c6540a2442001c442540076101d28814580703031070000e5a241d010403000c2880f4405100320100340104001410040c00e40d00800004082e5100f89910f004440e5015541d07410051402c00039070680d4180d15609816010384940c14581d8854070140c0d6284a00b41d406d03410b5008403440404d0b2941e44900704203c0b40d40d88180010070240c010002400c6641c0301407107038010000014148401d98408030001129264080041411052480 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 955801645 1250 955800395 955800403
    0xf0f090106031205030421030213081603081308150601080f0402030d0503100905011805010602190b060a2601060b09180601020c061305011b0f06050417070f0b0618070f02 75
    0xa40340b03104800000141100b88e8150005c0c40407080701c8106800740c9441d22940d68541c0750303902e0301c1110402100070400c0012a400094a141480c1c068400390030707503803008250f06060700700f40407030446a40381042240642c2c01c00300d040d4200310311040c945c0c0d40d4901580400c0e6503194080d0440140840400051802494016510040c00c0300300c4080c4682d50f0365503c00c00b501c042c410b0000511500340320002c10694070003d00080318500034081021101da240d205c6c1c50031100046c2409400081075a000304001c90108500b10454917104034610b00c1100744018142181c0003034020400030f860801050107990b495440e1103115000c0c0a00087d0725860f0700006170301d0002038900e09904220080b500038000f02409541300c0c00c0343c3d02a00c480800c00340040e00000250708a582c010043c44504030450041056030b1b00c0994800d1260480c65040312203000b640b45250040b400440c1c00d41826500c241c100112005815000681600c04044c030301102a05c0d240540001803010042018210301898a60301c200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 955802895 1250 955801645 955801673
    0x1509130206090d140f1e010507050d0f060905040b0a06060e010225030c120501110a0c03030c0c08043201090303140906030c0a0e12030405010e0d0206030f0f0901060312050304 77
    0x70200c4400b00040007600b5120400c0c480341170074002d11840101b0503d10103000d4540b20300c05503940c141c5858003049006005180048860031496610580410389107910b2240600590160364002028500740006c4001c0c2c80c0e45420030420054a0b842c1c1303100c0d60760002010b09003840d5555210020440403540c2c084003034410340c400b41040c03a1f08200081e0400c0080345a6a015008400134041c42c03203130b60203d94a0780300c2c103000000041c5154501401183c42603118484000080c5060002d80b942c54a4100d480e4005400a41108400200000c4103030f0b14103603d401c1c25030345c041c64800c0c0251940c0010341b02d080c0d944005070078003c006415100300400b00c012034180c0b4100809243d264100340d0782130413441e04052190004030b041802c0041862804c0803000c540c00306100011480c003400c0c4401100c0d603056890071242c00c10000f130138003001070703544001441c49602e6031005e02140b85004c02e00981e204002510501e5281d16064041c03001c111001c0700c2d40c0d00d0b6802401c1c220703a20f40301d914201710700c0b0350380e2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 955804145 1250 955802895 955802933
    0x3021606181b0e07030504150e0309030f07050f040b15070303060906140d060209030106030c030807030f1119030c0501091109100620010b03061509130206090d 70
    0x9091141e00c000c44222204120303014144002d0010300311900d24040c0318460041e400140e000c10009007181d0f2013500196409441503c0086680b407642c0304c2c0300281ca4100e040c14010383c01c0410341c86d0650500308a80892074100600800d04207182c213001c21807014284840b00c1c040c948894444402d62030b10030398051174011070300c1c0c0503a8038501070038000d0040c40c2d51b020700700b40e4034101040020340f480418800e03c03100b503004090004010721903440400035400000c5441d095503c03a00004086040c0b802910015801000084d9035854140b400a040c7d0b420411504288042c0f8019580e514000040d60500c0001408000d200c07002141419980d010140c80011315a6003031002580c00c0161015800e0074414068520040ca40c8400e10180f224040b0f500800c00019100481d03603505182c4650300380004c0c0d201d0703000011001905004242424000c0b2074104a028000c0e03d2042c80e420500415648013840303800a1102c41c88036800035103e1b128007a165442409200008428084041c000350020111 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 955805395 1250 955804145 955804151
    0x7060f0302091309022715010306030b06040f0b060a020a05060604020f071e0b191d0309011b020910081002190807031410030b0c070309030209070c0c060503180c09010603021606 78
    0x8001469280300421a10b4410308105551f4408055011780030700070989034031081036041544c5840500005068843c00840c0968942d1550f24aa8860100400301d0b0400d9602401d000801414030b585440c1002d00030600a9104111033f800300711480301610b803056071001c030400b00c8140041102c003072074004580103400b01000d5400e03c05001031002101c6040140c05201380400e50000e28042c900040302e0840b40c035141c01c1080900742341e62180b0180c009035800404040380380c0100350081440c0300021600c0c1d03601c424401700140001d0ba41000b4421030503200d07140c190720301501c19160f101c00806980b8180d01380541600030a051a00a030001d07043e6048122a1062500d4001d03180c4e080010076110980d1285604408a1a50316081003110300380c41e05500e032105024519420301020450041195040051a861910000d1003000300e420081c15203944158490800001203511054012400041da0380250010074017a111050080e04407021800c0c01a210200390300d04444903030902c0d00040c030b000e02d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 955806645 1250 955805395 955805449
    0x1210302031c0e0d020106061428080403023901050705010e030405010e040605180916080c0a060c03121d010203040f0308100b1c06031407060f030209130902 69
    0x60140e00400c3c20b55034900071030310303820114001a400ca070610301890000807489030640304120540001440c4515030709010480000303903582c010b590701d040300400c2c03000191841c050209056040110942c4182c0150803540c0d052841380f030790081c40e003200c05100050003a10002550984c05801600e8030b09401c20000d020304240390411546070303440b500481d40403030111030014895082c00d1041809492000d0101440545441000c4081c031400419400e01407085403d07009442d8045c001e40c900409901d0001c1c0045d0a1a800f002030001080c0c1001d000c120307000c00500d0101e5031143c841c0040a4181600280002c0d20005060040100a0003195550b00000603c0204079440c120b0010140c080e994460301c81e02c0315580c070819891644529115070000348151080080d00702c0102000c1c410100c40014010794a80c3c4011800b0a42000c01d0156042210704100c1c054002d06800d0390003a513031a0451038502a280062200e400f0011028445a610751120b411503c0d4000d02070b081c1d440d41ca0b828101c0b02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 955807895 1250 955806645 955806697
    0x2306040b040f1a0f0c07021806061308010e010c0516170c011409010507090503060403032f071110142a16080604021804020f06030703090b0f0121030203 67
    0x106131080d48a040c1000300080d407040d0150159644168000d00200030401a150101c1407014042d00c4642d2002041007a0340c4072505c2801d041c0020f10030307080041482c5c50076003642421a40c084900e80203024040141850408414800203901c640c085001d00900384c500c0480c054071b004030711045a440d0310f010740c01d002070b01142002038410044400240700641d203022084502409500c00c06406500c4a004100044e020350441001179002105283d4011050400c0e85560f690040700c80810b400c000a00005000700c080c05400030031010399940110610400e4010102c15941503092250000840e00c091f04811402450059400c05e054452040031850b21840c0c03120491081c41182088480d40040d034540040350303440c410703078004280c400401c0003048001c040a500810881c0d1200d80b81000f81259910b1002650107500306540c0040d80d04040d00d0003100325600502003c03800d400c4840100b0442e080c00139400c00529450001e031558512914041e45103009009882d8881041c40417259400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 955809145 1250 955807895 955807943
    0x7030915020106140d03050a11030c010f020d29040c180611060a06063603030810080a0b070c020a0312050a120b1e2206032306040b040f 60
    0x1543e4408140e07161041c01101300000020021700040c00704030240604070705c071070080284110140b0141c060341e15203070403803003001e084031101550420741c1035001c2460803821421b84180c1c1444100c00b0220651207801b9056503602425840c002441076403515514142588a000c04440545282060318091515000b01400c852500b141e1030b141817040ea40029442c003a06d028503000c03286030f916003c940e120b5030501d41d864140000c0125a0500e0380c03a0403001ca040828031100000d42c020707600e0504908046c0e400811468281c0d2050703119911000019000c648000c00c560f0300a5050304182c00e020000b032000c1100f18034590f1024001c5264081e0310100d65400800400c05440c00d40e5820a10075414100c00c42140c1074045500d41250b01c80d00e1040300d601c44a042a01f0101c0d00828000808040d9900301c00541e01145801c0d041e20340b200c0040041060103100308000e0110300030400b01c0300d600540004c0e5102c0e40184060310321102c100228050003038805d00900566082030b246280c08242009100354 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 955810395 1250 955809145 955809149
    0xf1d03070e1812070309140d14010c090902070506060609041404080c060f091b150f0405040c02060f1f030209010305150108071d090f01020412060f09030e040207030915020106 77
    0x390b0240c0540daa0091000004132a9620b03416150b107100241800854840045402141307030708400c8062a00000c2000c0050140703e00145030700115440c40e2030340004107040110760001c0240740c014000b00b1f000500c003241440d44508141c62254803013040d140018050a40080d10800c2102020184410300c030301400140303004106007080391860f4a6480c0c04210404044402c9103854200102e141211000242e00080320380d0010b000f000c0e001d00b0403080c2c1146078092103000c041090005400c1103981030602418500303254500260030240741c9406c5041120600174144615200010810040300070520070503006113030041c04404240d82c60740f0b0125500c3c1d41030741d004052400d100000007a00400018280142c40c0c100452426021b2000650040307641c019100307074014001d44150950900c0244089d00003081c1c9805030b80081d50407410420304461b550b4520305a0a428120030b000403079040310882d4141d84080d50016555010350404442200158000100000d80000c42c420080d0307054100f40c003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 955811645 1250 955810395 955810441
    0x20f0904140115050711130e0d03060e09150708071404033509060f0435161a12040b092b03051b0c06010609060f1d03070e 54
    0xc0000389200361405d00814030014105804440071400c582040c81c6c407031982c94000440400c0441130740d440c16044c610584c0c52440003030b527a410100210341c00d41d00342a07080311180c006015240400211000d05440040041c400d200b80000451400e40c4030b407000100b078080445140b51500c1c2c0300d00e84001c0d9600110440303107100300030610359140d0b41d4070f082480e456040d42c00358046c41c203031901c0300340703d0340790000c0c0700d6501040b40c280320005503d1240e60000c5c0c84c0d100010b02003880700c078a0031134104184a078040c41401d04e81c00703240e806141a09040072030302640c0e81c3c10b05600c0b150380f041d418041d651050342452607541246005100c100034801c60070501400b2880140c0e442d840352050050b07156218035132948038001c2e82c1c9900300302c002d01a0384000d0704810844080c1e56036440761402e04000750300440306140700d0b03802403004006203944803803501e02601c0140303011503056643e000010904070620010789440700035117181c0c529580c2c0400c51440104800321410140e031410b0240c009100200030788030b030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 955812895 1250 955811645 955811669
    0x2d0106240c05150420191512020309010c03050c03010e0105220e1b0105091503100302151804060b0a200f07050a0b0708070f080409020708180907050d020f09041401 72
    0x6651b00e003480c459010002200742d522a2107283c04140c43c0d05100c0605985e00380690f81c01d1005178134903140010361040003140c0020554150281c07004040b04c40041c080c80c51041c0c1400180000310000c82071904444c002c4404c0481e162178001500c0c50b10074094403039100e452800c0b600d03107040840481c03032086901c582d8002c120320120312030064401e0b02c0340c0f80348150300c06082440c100b500340c03092000c4c5422007922041041d00a0b204d5000c1101303c8000c0307454011086011850f1a02100c6001108d103074040d0941d828030030b0500d0280906d0082c0a540e04c1c00081c01a00310788100c842100c2e00d4203c18804001c4200c0d1580d00c0510807040d01c40a45d802a035000d845e440c017006c1100014501103c0312240c0c4011f120703151081c01d80307511020800c44081242c1105040000290f002e4040c005420b00c540a801d1183c0e9500880305040108134402c010039005200c0b481c04c2001440d08142540c556001542d03002da0341c1c1c0100ca240ba80584a00701c499a03003c0e180410800c0d401c00f018048038103944403042a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 955814145 1250 955812895 955812953
    0xa151b120e091501120b090108150c0405060a1209290901060b07080c0a0203060a0e1618200c0a0c060c11122d0106240c051504 56
    0x40604520b00311103050084104004403070740d65100e50400c8146041550001400b468840c0000300c1170346003a4002d1303034594000c070005a210003407200c0582d0403800111841d45000d1420740400e447e80602c9403114180300c01a51000340100c4180c2082c50029030241c3c40c10242402419641200b00e602070140d15414000f40009084010501c00c6030142c0d90351100c00d50901c111550340d1401036024102c0d01c005400b80841d80c40040e1410400d0034018000791034086403985002d2412490b01129103600c50703030b286010307404001d001c80e00c120070281149101000f0910762200c82d40060304540070440c0e101c440340001945242080082000402c0521403100320150300e0740e41d9822244810610070181c00443c032105452a01d280100070300c46000c405006030385c06c0024007169031404101c41c1004002c0040c40380740b2605000b80a1103448050012560141481f0400440b8043c0c008408202002800443d03c808002d2040801540002d1940c00c40340000e03d25241c0760081e40030302610100500c400a283e41 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 955815395 1250 955814145 955814149
    0x3090d02071a091906030b01030e06040c03080d0b03030412030e1503060907030e010e10050109090b011202010c05061e0c0408030a031e0f0b0a050d020a151b120e 71
    0x641d000c0b2062103a2010400349100c502c0780c081d0340042c020a520001c4180000c1c00301e031104048100801003038400084c1e000d60540050b090780e040c18042c405a40060301008002021240244152604048410344a205050301040100b43c200842c550600c0041400140503400340042c00d4480d05c0f0342d0b00d10920003449418481500101240c005002a040c8002000760a00800407603200c5880d00e000301300b25400070103803401c450340c0c80c0400d4a2604422420052a0194011107004003a1050100042c1130551a0940c6901040c02490900c1200421500541e80700740080c0c1402d41c0c001003500c250f410085a18081c506455450850810342e080014120200540030b131401c45106001451904824803000c4004081d031540190341c10b0341003060039081010600c1110700011068100051140744882004846507a0346d0209101d99181d016000060301d982104804540c8001481e00b2136003580002a40d03030003146000c80514000ca01103480602039541203032040c074403103904d07200b41e001c1c02401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 955816645 1250 955815395 955815403
    0x40b0d03050706050a020702041416080c0904150902030f01180b1c02150c0a050106050402041a07050106230907111c0903150516050a0206040f0615030803090d02 71
    0x4400350206005000a50106905410a590001002000502c0c0c1041a0f000a00711031b082606c889900c200c013420001c0342d1100c503001c044130301041d05012041d858441c4107007060348940103000340030356221460b01e01007a035522030fa030028059900c0e0554591900000c1e588036018248030f01f000d000c4000349000e207207541620032810006400781a4414102c40403006c5032100030303002d904076005500200c4070064900791002800803088507001400d1001020b0801c1405d46029400c0389204a2041004010040040000040b0100c4030345183d0749455080c104207004000a070702070b82401003003100504445400702001100001e0440e207280c11900c0e801e40448000c202040e91480070b61005c04444034085140900c03a1400116240031404162070f5920f600d20400e070201d15881964a07442401080d04000309100c00b086034500c2c009050110800009603210300140c00601004100160b00701807003030a420442511a044003894001950313442c04402551088a05009a0003881002456548081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 955817895 1250 955816645 955816669
    0x40e2e0803030105090c16081305030f03090103110f03041104060e0415020913140a051303140a0c060e060a0f060b310603062103120519060f0302040b 66
    0x16000310308682c01c050074403d500b04046c1c0300d0483c440c4148070801c2644182d10b4400d1160348100d644946070410312210000019440e00807601c44d4101240c0307424044000410350b1000e0000b40380114003540b10501d1060544240710a40612880000030001808440005c03140051025a8100400d079510040d2030507044d0709860050160b540141c0070612450250058040c250004182d801041809035000d8200c0d01c54604581000080c0410801031080c0c3d8403c451f8020b039030004002c10001c01d0f64004003c44001e10f1250900c0d403010170101141032160b0040041664001c80070401860080d108656441c8103c0e03403411b42d41c0c101120809140b0081c004c403021a0b038000301c804c2c10810420034800c4201000c0c507180440050400c0d500c00300901102442d0300420094500090300c0b800c1c0086d200358040c845108400c100005603458001981c0640e18111425181d24001119141c2407405010f24404032090542c80342403020101f000300344068154100c910071541040103981c50424010b07200c03005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 955819145 1250 955817895 955817909
    0x2a0612020307080402100e04061d0603030901120504030318051515010c06180b1317091020010e03130801060605030c0711100507030f030b0f1203040e2e 67
    0x43c400301c1c0040c1000040c0e0300d0918014141414100b1070400424200c8526030707c840c154542140b403081400d40070100c541e8111a042d030295151000e218000f0300581e607114003d2040e5039440c00050705141c82544494031020440c41c03110081c5056042c803a0b604d1600002404c1e245444030301007500c0c011016481c040155041e10350607012207064850780010450a802d042d50141665802000200c0c0d100c0428400d8100c0d091006404225040001d45070001420403801810100503090881d80c0c1c042c05180140064500600c40c4506501d8440307400490803210031540d824041010300c021804005060414480892400026030321110345090355a54440c607008550204003040c09520075a0081c01617501030256809840118004501c501210509210000754007003000c8007003541c410301201100340b003441c0c180090203081d40064180000280700d00d200d108440c0c0040300c0d0450034400d4400a00306051004203e1074500004d4460084d01d42640c001c410044a4150180d40080900c0c0203580350 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 955820395 1250 955819145 955819157
    0x10608010b0d021b1e030a3f1b080123190602070f060c1113090503120612032d070f030c1407120b042a0612020307 51
    0x190000815803684100100404a034003040f1104c07448048440c0b62800800000040c400c03101c0c42180c00c403408085e190019841e410801c060101e49600602e01014403602c0029031f13480c130145903c8041150300401c207103400351018200180a00030181c1c4010608001001c0025080c0d1110108030713841c582c01d0148542e0841110328035460308045441c0c160000034007928001b4219009003200d0601c00d200c0e44000c0043e404003006008001c002c00c4000002d03c6581000c40c5000f84550f5083e00400084980d540520201d410380001c0100e15008540b110390044141c0307650302040c08122490f000c044405030b00948865503003440121001046411885540d58480d4480284003481070303c0351045950704061082c00e1000300046401d10346809a250710980720090841ca69107400e00031f00340d82260a001e1500040d0b010005004080c1c41040358951000c8070780c16550300e600d040101d2402081d00c21000700ca40c0072040c081c04039500c040c601958900d07110400c2c0740002c0710000081c0d110403a407800020350 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 955821645 1250 955820395 955820399
    0x1050702150c0106050a090203040512210907090608030304050606030d050a0e0d020a0603020c011508120f040e0c031b09012f1009170702060319090b190b0901060801 73
    0x300c0c5201400128050500200d40b885c1d995001505030001e80c0c20031100190700100b40020000708000c0c00c9107103030158070708034100345040d1419079001e04003642034542c04181c1c40004440c03950521a00d0040e114440341001200d440391043c542c3c07900304507030484480c4500b001141c1d00345030006002d82c6207001590351515043c20800304860401c0d8210b0b40b1a04005682c4400005a0310741c006c9101414240d41c0051f201c0d254540b24509440707010b098005405500d41c01401550800703d030300608210142441c5130341d034084458010300c0d4450b99014441100c4e24030140814402010000d50240341a000058868802e00c5064210341c401c407a007440c045603090a01c0102140142c5001e02c235001c0603e00501d5002880c1c03a11420301c08c0042c01911b14560b501005000c202c0100402440071101e841001d00b0101c880d80490384911000d0700c80e0541036800100e00c43d07090500e4020fa848107a1080d1414000e041405c8c0034170f0325102d4031000300400c508141c808203041c280207400c141210015540d907140f0764 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 955822895 1250 955821645 955821679
    0x10204090e07140607171215100e0105250231060f060e0102010b040e010e0d0c0b01050904021201020c060613020a080a180501150501021203010b09011b050d03091101050702 76
    0x2042008042d0300c842d01c18002617550201800e0300c1f92042c560480800c805c1600901003100036140c2d05114030a100d28001c200100d030f40e2200640e0541030f0364140700e034443d1321020224442e0100c80e03400290f0000c0f1403500b42c81d028040c0300714503070100d43c43c400a100c0003000310195010784a0900400c4c1a414070403108104a40c4110210120f00d04103000004c4c6a542484c0441c050300e030480c143c401661b440d101c1c0c483d004202040714081c11a194604070054450070754440740038100601c41c5038400c3c80c40c800424259565014014020803040c0e0003155684d60050344180c03500c4080700c86500c295055040089500e03418000c23200c913915150342d042825555224214010080b604807201070047c420b12080010700c0910900040c00f54004032070160780d1916000901d0003512401e91500030606000400081e9600300a80e01800e00909224205c1d000500046142c0c035800c2c43e0280191185802d0fa43c5840e8050380403c48aa0040310301c0030000b0000b60055a0174459258002e4106002c10540380c840 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 955824145 1250 955822895 955822913
    0x100e09040c0506030f01030201021902030709050c0c0304060809100e0a020d080904060b030a0c030e0703170d141005011b0609020303120c1209120307110c03010204090e07140607 78
    0xa40719a008204090301c90b40414103540044511130b90074001880180150341c4c040118000c2e143c001540300c9001c00095000c070f034541200d407140340520743d12071010032000a0340c4400d4880300506c6100300c944860f91024000d180040544505039680100004210415a14080e848941001c400207010080e210350034400c140907008019a00035509100c1a0000d0b80c907406420028400c070104541c4034140904034004076101c1c0801102414604460405494000302c0d144040b0303a04060400384208000944052921408544403c003502d0b2800400d040d091100d502406041c60600e919000d9448600540d80b13030000f0380d500400705100700c038100d00260146e0005581c4c4c03032000c1c082d40d0400c5940301241c19120000d94228803407901c0401d0400314150000e15541c1d10898600040000301c4008500f00807074480540040100701e910244842e4a00781000b42061010028000310b41c1c40c4c0c0c1e20f0200c0402054002c2451186004140c00041d20752070b03a203c528420200244404d00e0720007665544408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 955825395 1250 955824145 955824151
    0x30a0c030b060f040c0c0201030b0a0806061c0f0c030b0601020714060904020c0303070509360a0227040c05040f0b070507081f0501060f21061701020d0b100e09 70
    0x480f031203034107101806444a01a51201e19070340d440e04183c1010b18030024013a501a2050103018810000007000300d4030300001c034503810031026111215205043c807401054000c00c0780c1d02500c180351589000082040c40c050b4142100e004400c000a02d4842c1e000480c0c6420051065214105030300c07a01c0846440d010004141d149002000145840744002c5501d0035900308940d0038010605c003082101103410840303c040d044040d4209102020f00e01c440500c40300c1e41c400a814a440307900c6e500003507170092495045070200c00c00c2c1e550300a540c0747c0c019820203004000190345805075082104850071540542c042e030b41078403441131905040c10304242200c1800d4201c040159041d1054410002c0c891400340102c494130a068100fa010f440004002d0100365803044c1e01050401002006412603543d1041c0007424082da9081c09400c240700400e17401000c0e0550381c0100014802d5001e141028034815801844900d800c840280148009541007041c4c894550a6840c04101c5000c802c5c1034615140940c0e5034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 955826645 1250 955825395 955825399
    0xe0c1303060c0215040c09050108120a0305152d0f0a03120c080d0b0109050a080a0b15060a02010b032401030605040302030d090809090115050904020f07080720030a0c030b06 76
    0x21100c0300c502c4181413103a040d1400d6982c02180340043c41b044c0c01d28005d181c05004400c004000744802900c6c914024829548030400f0103654401240d100300d41c100c2c1c40c3c1001c81008111844039100c10041200d0701c0c015486410442c120440b10901c00c0c1010040e105c80303074000a000c00525440e546500302d098820008440402c240d605a110008855102a002141810707600180302c5210500252140c80182c0000d841504203e1040205010004680e8151a4881c100c1881a101c00c003807620050481c0380855844000030807141c4000e0380c1513000a0701000c00320200e0320a48150740042d03100c1c0f002e00280d0403455042d40018804101c041d0407841d0071a1091048a16000921200e40211040c1786030455245c0070000b10712001c1e1401311a080c0c00340900400d441200015084094058803544505074010b58003c02e81c0d43c3c41144a60070340e0303803030b0f600254a940e48021300d03c1d105c0345080b40940c0001c0d480d84900020441410001058540c081d80051203034049401c60b15a01a18100102120303 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 955827895 1250 955826645 955826653
    0x7050a050703050615011409040902150a050d141509070903120804051e2e3e0d0b03160602030c07090b0a0e07090905100e0c1303060c02 60
    0x4001142005107000542c0030324054282410700107100417044007404070043c100300c0c0e0301100071014102c10f021900b456104441c00541c0e02403078400700c1e00304900404108440c8201080c00b880d5181c02000400d884459964100000c00701160309000c0c5940c203984011180e044030502c104039060014010350001c6041c205108410380d40d9031140510250003142d840082c100800384000c0040800094040d80e58048a01100d1201181596034407040b005071150030840107105078000a040650140b1a1820484103011500b400c4d405102c040300105124030007405103080c600303000071101442c0105100300040b0140b604100000d64806441c92640d01541801241c1c1c0303400c44c00030101d04901c02408107030080d54035221454891420581564480c0e1202d5051801c041866515083d0240980700c82ca04c02c4d980503140c0c100c04030383d0710060707401c451000f6240006104940e0640700f000320490369801031742d14040e0303508039800c030a034002c0b1060401081100b000610000c2c100c2e40050012040c94070482d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 955829145 1250 955827895 955827913
    0x909110307030b0a030606121a150105340210050a0e01031a090a05060910050109050907030e030d06080601060e180c16060603170a0801060f0c02060c0f070f050d03050705 75
    0x50011102281c0c0234144d41503000762060104009a0501c00e4040c01260400140e40f40c4a0105000030f4418015241007050000d890b40c4030b07034840700c054030300a6150350481d940c3d0307034070402010990302a902e4240d01c52505031540b0444140b0038001c58400c40983d9455030a016000741c0154050802e00c044581e110811501282d640e469a6105a2080040000100e443c0c2030000921100d9503000e06404140c94450200748980c1c1d030040824011200140c420300f02d113903900d0384100e006041c0c45d0f1a039000d42c00300003560007138404240c220805441c04541580c501e40d90710310b016242980d070314a4031504580d05101c000701421007013560a0f4401003400b00c051034507080403800301c4a10303011402107551642d9001c0c01e00521130005031034112a161082441c0c0390440714440603001000501c5454100305007048001c4100780300d4201a4041da40c00790405845400c9029115142c00d0b00303200e21f580034851940006842031035402030001300e59010380000c00840017514111070300e9001c0101036407544241944 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 955830395 1250 955829145 955829153
    0x3030417010b0906060412111207030503131e1e0b0409061737020616060b0406030314220b040806180615030a050601150909110307030b0a03 62
    0x1080d003100c041030002812003541810485403150280c03c2e0f5001e0f210600051101889410801420341c0d00814504000d0700382c0300001d0050320002c44441418041d90310b00204100c6d0001c050040d485032013903000c1c60315803151079050840104010140c0c414407004001c00500b218403072280803912909000034906500c9908801c0d0980c0554001c000d81c079550103003004040900c2d22030510b034001d0341d070107004480c650910310480310000c14004061000716400040080b2489003c00c80100e5020309186e40303809026120040e113401e04036081e24110305168046081d46000d102d0311055a505440d000d031030040010040c0d00c40d03004040c0400068034440c00020031203400711500e60040c00c1d050116a40e0ba800c0c101a0740c2440405858052030300d0142580421081c1d01003081030f0b1186696402c01d40105841000038540814118043c140d4000c040c004900d25201003c10082c00b4490340751000345a17600d410382d00c03c83c0c0d0400d4640610348803c1c001304544905c80d4005126415000b0308058600740c032a15 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 955831645 1250 955830395 955830419
    0x15040209160309051e1b09070e1206010e0f0609191e051003020f060f030105061317070306060b0c0312100b0d0209010f08041e020103020f1209070911040e06030304 72
    0x100f229442801401c18200300442002a81c4a40946c04035200c0301e03100400c0070810010000c0c2003034050148401c004482030f1240c000101514403000708136803855a4a080c0c8098a200a4034400d0031001000001000381c18894810b5020303560409070698240c0640c10810300074541010f00300440311034100d10f56000f209a0080b07030300942c0c3d110700c44924240b6510411002d80100d20700c131801034405000d0040e02014070015641150420351307200740d4400b40c3e40b24514a1010b950000c11000ca0344a80d0403003458800a040010341c0d20801007000f0f419182c010f10246d46c090246404000c0e402040901070800001503004c0c0c01205840d1103000181d200c0210314480c4c2c000d01d540701209030b80899010704075a03020444882102c502d0501a005041c6511b6610a0301201014030300d025940c0038a42007164480e504a0380003901c18110580c450140701c3e072a80343c0580c00c2e41c02403028811080041456520b078031410510445a0720741c5454036140596003403c6400003440203501d40010301c00000d21144101d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 955832895 1250 955831645 955831663
    0x90e010b043507030821060109060f030b0a26030c03180d05060403110c01082211041a0103061a04030311100212060102060a14010902300105031504020916030905 71
    0x1911030b5141c4c201a00280340c0103c41c06a0610884101401d0024a03600b11280c9c02c252070241c0303000c503640c034045074080d07000c0c108503820150004800040040c1044d40d050107110840e07040c408000911082e801e000780d40b4010074101e0b8203a50002c0100d84540d1006402c80d560502020341031880340d0841d0348a16050080448080d404195500c08a4440100902040800d1002400c101ca0300381003501c50582c0110b0300b0260980c101402003810018480c19403489000d600d00280207002d01e00000d028040050341482585001c28244000400d141c1d822520101d043c030701a85450342000d00d141c800310703100704010004412501443e2007640d408003140c00103002001d030030b02d1204d4650a01000086c81e1040060078040340d20300d000e0302110049030844160b81120f0102c00302589551004180030ac02e000c0d03501c00141440d0002c01340705044140c000c0d44034100c420803420303240090315200030b4403030719030f01124001d503c98003002c005084107030400f2085046400724039000881642c1c1c0d944081c9441000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 955834145 1250 955832895 955832903
    0xc0213020c010504050708010e07121a0a0209040606090e0f07110604060b1011060c0d1508010c030501120506010306050705070b130209061014030702010b0a06090e010b04350703 78
    0x2c3d100300801d0050401034540105800750003044411144442035440d481c641c06080c4107110a02a000d05101800304140746150b2044101103507400c2202d4000d0081d40108100c6000c0c44c00d00f04001a1a4050b290507403c07a4090030159802e6503034a101c800540c44020a602d052203000040d8848100302084118803861041c480041d441002d0810002d204403807103810310403c041822001440c8402007030b407039000548240303152780303a082d1890018094035491500c600e00d802885400607001d4015044500c1c00040780d1410046a40c88480e030980d0041816000381150f03001200410000b221940215400a1079203000b6040000390755910703003054419940c0c1e941c81c2d05e10300317214001e40c0307451662140c11070000c442000d101304090034041c0c0840e01801940e07200c800c000c400a01c07203c1c000e40041442440c024540c0c20100d895440c050b010680c1c40c0580da0b508075885001003491004182114190340071b9401254203600142c0003840e145008004440001032014407203e41d004003040715002542c81 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 955835395 1250 955834145 955834151
    0xb01020a330e210703200307050303011a04080a080a020123040201031a01020a021c120918020403022808011a011214131a0a0c170c09010c0213020c01 66
    0x11403081d0b5403506500010226481c0240401c0207580c07003150084881c21617150500c07070001c01d2100c21320b4505001c0440039001501002682c202000f0000c002107050700c9880e00d04c181702c0c0d0b44144c00b070406809107015a40c6c444c3d002040d001c0114074118083c02c08001a480049210800246c0c44141c821404e0b08140140b1002e8007404111b60300340c05403040034410021100c0c821186900002d554828621020340590060b8041c6111141019000418190010f01d81c207806181c01ca00181181424811000d20b0083d2058a030079a000034021641100d400802110703140c21481c420401d56245040485030401d090340300004c40d10020f000d401d41001c0352480e00560079202900250401103206810505240381004902c003081c103124005070003824010202c0076135041850402c003004a8028507004103100f180c00c0007900029504544a030045640e40e0a50f01d114012035a490014251071001720a2410b12074800c3d954411030103400b400d80000c00348141c441100e8101c80403607002e0348181c450382e51 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 955836645 1250 955835395 955835411
    0x1b030c060e03060906040804230301060f080c010e0f0f01050f07030206010623040e0c090a060e0406060503190209130504060b10030e120f040b21181203070504150806090106030b01020a33 82
    0x140501c400007803f9006e00b000d91041c05007500081e21026030350f080c80c1c410041d0100d10070a603449501910362200000c07905035900c00e618200a0740d661000d1280800144095001c0e04054030780e90002c015400401c807205003424180151400501d10082c038034a0110414400d40d0000c1e50f40c2c0c0905d500405043d01e030a100d030014031040c08143c035050f4018200707000d03080003403146107019850404070f240c03511a40180c543c01c800000440748440000c841e11101c1c289070074041440215444818103101c11144036454581c50407040c0d0640d00742ca0202c4c800340e0072581c110109807110031b009215084901c0030329442d1030384412040c50030360806032224207003c040720450200d1128004015400c0714030540e198450417a5148229501c2c03031400f8402020800100c04902c1803402002078401901f15070031081d24801491000502c04103023252094440d0100b070000145603806842030001130581a0b0150031000042d469100b029045541020075410404110a00c012b824400c01d0020407018140420514 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 955837895 1250 955836645 955836659
    0x130b06090a11070f060501080d021e01020f0408030a0801122105040b07050c120111180a05040c0509010f08130b040206220906091401031b030c060e03060906040804230301060f 77
    0x383e4160481c2c10b056100030314111012b0780001d2451040d02000c10082d501c0080102180d019001d280840e103a0280040390205a1b0240440034001c1e200b01a030b210f0310b4a81e41c0b243c0d080405c07050080045e066503040148007181012149201c045000ba41c1000c40c542540c408003030485501155040c2d0b81c3c1c4e0061101c09000d8a0020002140055450028040b1000141405000d489081c00002810b20700302d036110911784a0340e170340400909004000b005510f001300400303400d50b40400591070025044164510300340f40100401c5028505c0c00d01d0583d00c4400640d01c42d0000308000e003050784d102c8024000713400416016411098400c4031042c54940151600404000b079415980085041ca410442e1500c0b00d0070074655440c0c11641c10030034101c000300110054001942072900f025200824128000c43c00c20f4109100c101c0140c0c2c01e404075a103a0743c440300300310788074103040ea0000d0008a08000400124031000d060395500319a0504411421f217140000908491300d540c0403c0c140510054100104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 955839145 1250 955837895 955837901
    0x21120203070c0e01030302031c110d05041a190b01030207020405070f0206160e01050d140a021308030405031005061309120f0e01081807030602031e130b06090a11070f06 74
    0x500322040940300d0b44d41940c5d8041e440380a0246d00d05429040f5048601402c152a00b290740502a51001d8654502c0440d01001c0038080868090740d54848452001040750b0403107038000d10402164040c5c0d5850600540c21501030700c8400b140c10f0400d03409101c40e00269556105140c000c124903110114404030081000c0e04040d0002e2200c00520183c0c100da44030182c00c1005c1e81c0e032030042443d01c02c2e9290301000c03101e801403a038203104801a00c450010030442060b1580102404115607004801d0169030f000e869a80e03224500882d5007540118444011005880c0c1100d42c10560050890141120f001000c03403c55044840a40d0381c0c50070582c5042c90b01d600204a814520018500050304201080018200000c040c0001d0041c10b0b68035113400350075206012080c06150710144c155506d003400ca1021030b241d0360100c030f50046c0039400300c04140351030480214030803020f600c40001c00442e41d0750800c200e85420000c00c91040b040d01d4255042240c2e5151009040c014860480340e000a000b42c200a021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 955840395 1250 955839145 955839149
    0x9050106090803072109120303060906140d0b071b26030105010804020909160e01031103010204061d030a0c080d12060f09055b21120203070c 62
    0x1641c10801008001c0780c15503d80c0c034000c100b651100c2d000036031080006c8694a441764007201203001052200b40401d0b616800c100d00305e6204a00a200c5552590392050001e0150310b440d55000b01d04c20344060000d88580d107401e0303200841c1c0c10821100c50a1a026081c400d0400004a50300721a064801100c152192100d1140c2c0244008850a42d0f040900280000c1030182c00030b8814482c0fa0001800f145007000602281040c50068101d0950b4403484c0540c0f080080c0400c503a0015454038440703581c18148203540485000d40c0d16038928007070003050080300c454012210758060003082c01c11004141140e2900c40241400002002d0428a1070703001003401c4100f811452643c1c1c1003d4003045003130040010b103030a440c0450700010700c3d925a02c0c0314100000202c407051401e40d911030501035407100c140081c403510700d000c000d06200c035030000b40458009202d9a1602005405214020702c01e004a680b10304800016145d600d5642d4565521035119803840c032511000180d10010f00c003400c0000486032a00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 955841645 1250 955840395 955840409
    0x6031217010518041b0f0f0b030f180a020603010b0a081303020d110102190903020102060106090e070e0310090c23150307020712060f0c020c130b0117010905010609 72
    0x1040e50400c40019450700c0e10183d286040703d4140040780510400720014102d404070b101064100b01d43c0d641c038940703440c0114443c0f1200003107840c1000403003071190002c41c2d02c0380442c0180d0001d95601c4000000014072215206856031082c3e4501e20300580712400118040c192100320152150b02d10400204146401441030301000360034510a80041d0700001d041ca0442c0c0345041403800310342e0b140c00c000d0080c09032000c030300014902c0b0005503002d0394000031800306a900070b03400d8504e580e1701e0302e5040d50810b85c140300e8020001ca5050015148030b11940941116140040503690315403a000e0161050340c50102040d51351504400c410808a010704a10030318124500f0003c803e2f00350386000241340c16910208483d041c40000000564003803003032107d0005003055546d00758940ea81c82c18008010482103004403841e0386800c0d12446254000501d20300242c0b1700405c140340d80021160031101803c0040b40b500d051080b00f80d00d00030400b007518021406000f803110300094641c90824018103a42843d40101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 955842895 1250 955841645 955841687
    0x12060f01030240091b0f020a12111b040f140c0708090904060507120911190b0a110d17010b090d060c020307060b09072c0301060312 58
    0x1a0b441d142c900051684080380c041c450700382c90b41480c0e41034030f02180124108462140d01008680380d51507901c6000807030303e2a00b4001d07031010004003e95070403150007000b00259100a1040300082c00105160901c1141443c000b040c802000d00558900b44c030716000384003130f0038120000ba5004e040c94491800000c41c4160140074503011001a0260241c01820102910b040080d20405102400c42245c05480d4040d010f0b484130300d8a81445001000180d48520001b4000916070905900b1802080c0700c4640000300b00e92490300b0101004400801e00300e10750101c03540c82e03038000340c5a80ba000c0600080491901d5203102646002521410300030600505004e01c41c0d010b07080030944000000c0e81c1d05480e00e00150950b41d880d0000010407000300b0039801002c0c0c03400c2c2603035405025070110141810300d00c03610060050403070300306c20003443d05411102d070300005010303c400e8411009041074104000448184005e048608140440c0c01d448003600b0940304c94000c0c1e20048096940302648845089124201d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 955844145 1250 955842895 955842907
    0x30c0312270f02090f01030303060e010303050a05090109080f030a4e020f0d050901091101050a140f04080d020303010803040306020732121303141212060f010302 71
    0x10307076000c501c481980825001200c4840108144408054100e03500207241200d9403400d2108401c03030302c0090008500082c186040094007000f1081c041d41a2079141d00c7d01414002c15030401c9541d50401c0c0042c60401140f9100004c0c02301c0b0a11080001424400186582c0c0d01c40e04409020f80b0321a90b590751150711414411965180f190f80e8101d10440d40e00724000384c40b1328000501000106902032405964400102c00341169039a100a05034035003580f800748241da450079050340c00c035040340502a2840110807020030b0198440e90080c0040041410a06507000742581d041025410030045074048c04400602401508020007560007a89214402580340d5810003401c03d803a0301407444000c050f1500400c0d07500401200d0b0b08004031011140459600890000118900c004d044542095540c0034114601541c5044001210030307520050003101911440d5035545440203940d003400425130301910b25907000404c03408004140702c1007480c3c03c0d81850b0802d80100b00740941030409185c1418410010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 955845395 1250 955844145 955844171
    0x90c12070302041a121f150903031e020c013506090112080f0703090e07120506100e1e13050105030c06031303030b0301111b06012907020f0d030c0312 66
    0x4490703000c401900a181000080180d4400040440d000300d0b0b200380300d0440103a001c9a1041c0c0441c1200c7c0030703039240400c0740307100c030be01303440c003010140005005802224000615501804040440303481904400c490106100b803041d1074030442003031000710f8103400340601040e0710f80340d01c0107800f401507111014540c0f06565aa80c0031441000204518808041051800c2c107005100e000001c00510011100c20b283c0204010305505040b511001480c0c68400130860605000800c00394445440e190741c6010480a401c05c8014a0840340790203000480c44620340194840329221088801064000710b15541400d0800d42003860758803045000e103405004002c0001c1902048504568143c100040c1e485c45000c082409440b031869803017590000020402040548240310503c5010f454041d201c070703640c9680c1000c14180c1000e130024980b00d1420203207850000d425005050540c1b0041060241e401c4250100b0b10300a51040c042e80410017440640090613001203103140307a5000f040042201a92001e2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 955846645 1250 955845395 955845427
    0x6080102031e0721150b0c060106020714150c0d050c0d0c02090a150f0f0305061609051c060501030c2c1501020f012a030603030806090c12070302041a 66
    0x90b0100f50203000200c4d203c148403c035801500ca0b404103158804e503e9031100707540b50803540114280c802d5842003400000d00c5520109050003501c001d100c0c0350030300304048410084141c12040c6e0010b02d070714040041504007101040200b218003800d0b00c520f40c4506d052101c007820000e051f18a0f005100140c10142c0043c3c0e2440805a8080f900550001e441c803180315010120312203982040301145800d02c0c0200e900d11031780400301e0840b031041c0120349186d5225150351110003140745100011440002d01444103181803d203401012880030341c1400004080d44442c82651420381c01a240110300e0b82061013a002d4030340527070780e202030b42c0a0210310203400307201400824003000f000e02c4030307075042c40980070300ea46e10a004140c03085040c040244071301103003045149880c00041d07041560725189445e490705120701900a4904a9030162190401d56031800148209544001c05c16401d546040001a501c500014009030150304140d5005890310b09108100c01c1280550344450029801400380e02da05c011036030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 955847895 1250 955846645 955846667
    0xf0f03020c0f07080f0106050d350a05040e09010b0a0504050702030409051501030506030a030f0503060d050a030c03020c04090206180105131409060607030815060d06080102031e07 79
    0x115006949028041045080016040780c5030001d0040441c0040c44c150001901508140010020000c0c55501e004100b001301d0203d00040000003210b84d840d03204043c05caa008144400841c201100d00440690b4100590207a80e2150104d0400b040c140110500f601d1040e0b4004c04140c0200f15180d0103000150010b502c5124030751182e5211400140c010b071080c0291001004042010f000c0c40c00c005038081c0c0c0c3e03007142c280100c0c0040d00c1c0c00009200b0f071400003071005000b9056150400c0d00403003c401107900d580000e007030a420003d017890f9800065130401106500364000c0d0b45403001e00c00030b454000d0070b03d403007030101d20b100b0390901a140c03016a644004940340c40003009103006107001c0420040e6018090313003821502120280c040080e400003001c10584286904660003030540d035642003080141c2c0540000580091040000204140030001d0700340c0b20a480100881e0502443d003501c070b0241ca0b4583c110780250794001c0148450807642e0080c600f1540312000501d009803400841c0100210000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 955849145 1250 955847895 955847897
    0x302011a03060a0b040609020f030619032a0506120a0606031a010503060a050a030f0b09190609050705040609020a2c0121050c091e210f03190f0f0f 65
    0x21318242c84140c0d4440c2d12410040c00181020741d200c8240500510142c1c00032600c050003001c0280c94002510680d80c400e030180e030791201103140e20080d8200d03620024100d0360560140c1c811642d401141c155207150103050803101100c249046494188130310401e40d916980000289030030158040400c01682c5400e102c0346a081ca46140c5990710354000800040712a4042c40c0c01600307111011007440030880c2d80d0040c1601403002e0b1066074440d10710051303407040798840201240c11b07010b9014000401c29000060110300031b408464900e40c6640c0084d00f2074038154042d41c91903a002074040c0a00d50002c00547c80000c1e10b0700950301c244010f014244110392028581c0b41008490030040003411031075001505003001c1c45408110f9440d2202401c1b10660008581901c02d031113904507005c00d0a00400114150344001e0042c5502d000c0c01e0301c0080035100d034850800c88030300074011819083c20082018111600c0b5145084200240a980180c020094080202c1c10007241c1c0c42c12442207900004c0c0c0011840007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 955850395 1250 955849145 955849151
    0xb06030c03012f090a08030c0f030304020a03060906290f0a0305070b030c040f03032f0705011b050a05150610021507141201050111011a0906190e040302011a03060a 72
    0xc1e600c0c480061007004d1500750300c102000707008030300e02000002500341c5054072412110f5030986900c020381d072408102c400035402015030100384000b8110b03800404400c0d2003030a0100d003040c0711051042e06006040c040d480d0001c03c00c0c814402d54501a0440f281e4a9010750f0100300d070707500395202d83d81c0300d0200d4094401c1d58000000464001c5154a080303400800383c402d0600c607081d4a07494000e04103c09680140000550f1403c00c01e00130a282c000c020602c901d140040000c0d92514005441c030305440c095445203940e00404940100318148007040034244204060319080c050189600c1100c0d50280c82c01c1c0c041e070040407951184940000b98002c1d00d00d803155289070f45a0315400c00310380244030b0b82140b090009002c0b802002c1c0015048000341a40c0007621803071100c0b592014123300702d8210101c29045101002c5c8015894208050b403182c0190700a04000b0301c038900a40f03014050303140b55020346c0d4030610100801090640c28030405803510741142e10380b940900d0b51000296550b40c05840000c507565 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 955851645 1250 955850395 955850471
    0xf081902010c1b0e060a060c5609030d1104091a011e02070b071b03050f0d18030201082a070516060c0b09100204030b06030c0301 57
    0x80640300007030b2550b521240c0c00c403005440c1071005003481c0c2c10340b1a11508021a030007058580c81c00c51090819a1a980d6406800411319201c410035040725a1300014150921341e8882d04c01140280880a07811500010f030075801c0b80d5101e201a068240709240074185c50a009000f001d9101004458019049410100390101083c0c1400c031a4440c1c2da004941703062602004907010807860107404241c0400b620743d03030448080603220b01203d51304a003101e0010f03000b8400600074014102e004d001c405014200c180c0c1c4400410b10080c2180c0040c1d00169a158009100307020800e408210040c07e0b850140341800b180d44000d40f07100b0f00c50500f404001c1c1400720074000110301d140c0f190801080054050081d5424229070862040694002842030b00c481c021003c10103a54071481e01c542c021a002039aa0510605440e02c07440b00501028001c1d100d5030040d095502c400c6010380c00508042c500408000032541007940c1007510b01805041407600a90420500c10b1148189444a02c030003a058103552802031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 955852895 1250 955851645 955851647
    0xf031801060504021c15062f031219060e1803091f0e011e0f0c0501020c0106050109050919020903010b090c120c030c070f03030e031b070f08190201 65
    0x200c403075000a6000f61020511601c202c100707079603007101d507411a0403c109090b0914140580150180103071408104008100c1460340607a14250b880d80b04040b0203000c10800d144085400c60784440307041c0c0107401300c0300e051080c1d01c840c68603100325400116400b000544c0c5004040400081c000300465419068003945002800d0b041c0708843e0514030051144140c2c8039099030b0410300380001c0f14100001b039504511544594001ca000d074214140105600355290082d010071182030034965510810050ba441c007120014209001520304000c0c0a4008aa01342c14039000400d4030b14681d222030301c245141c0d8240034454000760300105400592040159452000c10003082c0034010010109812054a030100004014003802800e010401491050007a8451000d88040c501041e219102e4004040200c60f000035001802c448009200c0c2c100824006a2001103d056801c402c02075000d1400c80c0b44110064507013804081d002d00b0010700c2014410f0b0404281d2580c03441c0d04001d09952503088844175080d6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 955854145 1250 955852895 955852901
    0x311130909020609190608060d2a26060a022d160305040e1003020306070809070b03010b03070e010207140f0307050306090a05011a011e030b060301170708030f031801 73
    0x132000181c81c0c0480c0980313144060405540b584902d8000515003000f01d1034915040030321202c071076080302c8012418400b5000c1c80c141140e161400c4803402ca00000001800890038540c0340c0510f0314048200d100f05910004941017902c020704070a038030f03841040303091803207800c1e0071140880303440090b19801e88504a80d190b100b54403401c8001008071815400303010825034010b00800648150302d07038109803511100040c1001d5601800000d501da000078000600641c440c162480e403051700441150364081d0354035408651355000703070000085000c0000401c080c10790041380c0440320041c01c1c8003c02400703150140041d040c0001001c1d12388140c01d40d40701c01c2240d9030104140e4014060080c1903507803e0400d1146141c0e07030541183c040b0380300c7d42400403135010031864a0701420300c000d06031a04188030301c1c01c0c000d804541ca0650410414103981d00340b140500d8407140c0c0950f010306118011a110104139081003072409607e9031002071180e00800c112083d40040c401620382005100c20b004982120094015000d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 955855395 1250 955854145 955854157
    0x4180506130213051305090303070503330321220503032a01050c070204111623030f072306040606050406150f05090f120a0303111309090206 62
    0x314034008030f01c10710400c0c040301000d401c88030119111302808802415003402c6d150100ea000c0c042c0c3e0818400600c4040c0100300450f0300c048112a4094074a12045828942c210040c031410f0341000c2404c21011641010000c0c210503410351800c9004c5800c10070941080c07446050352941a02e003000340341d0700341001d200103400003802c40201900c2c0c980031000500c1c1c200c030407031010714904020000c40b60a031020040c03081c2d50044050401d00d521f004890340070310001c0d1842d9229010943c2080010b0060351840385440f0780044d215016800d08a19000810340100c00d8491039030310b10b50420400f8548000074a0210b581465004c080059013081809030f8142061014111002a0003503204000411080e5840001a0b420841302080815201d1000290013106400b10101151100025401e480e0103900030744110314005000307010080c406004610210390214a02540b607209800140030583c2600032a80b403060842803c506048110007252848900c900c115180959a016842e0942d12020300b02d0300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 955856645 1250 955855395 955855429
    0x302070f12140c01050a0c1e05090120060405010c05040e0f0705120903070201180501080609090c120a120f14031f03080a08011a1b0705031507090b04180506 69
    0x185403110f11121902820b4200c90b210340301c501d00008002128000d00340424540c0740c008109001d88030080f015541a8803180d4054103100466240044070031000c40b1003180b02007081c0160982e401c05251040c00d41c0c4120040c0e0090100600c41881403c18801080303a012204075503031040c43d02c50709000e549501c103058400050b075400c01e040045084000000303041c003501c00c2e610703958100b01000b00b05640c0350712800307464001214500468218504a0f110503080903030302042d510510707283c800045034154840e003004100e40110740349030140400202180d00034501820088046950346030020150f043e40f5982100400000c000700e4400b01840840d0910b83e108500401819512130600450075005180f08100096100e0f0021400d0292100310b01c00041b5034100c483d0400c1c030000800c80c0703c40100008801e142c0b00b104000201380d42d080048504c5100700c0240203081c0e0070407000040456285410401c81600c04120402101d241d0b01881042034001490000c1c940c0c49140c0010004007004004076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 955857895 1250 955856645 955856647
    0x20d1a0a27230907030506090105160f1e030b1503070f08100f1d09070e0a0b06190512100e0412170106050c0c04050108030906030907120507150302070f1214 69
    0x18280f00041900649004008540182d9658480300e0700703031401124840d424158401d40b079000715025400461040301c40d81000c036020f42804a007600d0030352043c207400c0c0c0040c2e2101404901400c1806440d02c0540131024102c2c514034082d0b001602c0c0040e00382c0000100409480002c4440e00d0428415000e00802c40c0d15031100e658034003404a0202002d4004600b4002050100b500d08a0000303505044403841006d01d03201e80c0d21524850010080c03009000c2c2c021504100c040800380e1041642042d51130192034080c1c5907210480d41a00030140280008a000e8102c0414080300401094166010341d004e1181c0c00c1001c1218402c40300e600103c20705410940c244800070496039040406480c01c81c1d805c008070380344140d14008001c142d840a02c1082120f400410071800941030a00007940d000102c101143d0204da0b555040c2d81c0c0980400300103486a400c1040180070300c42c0c1c001c1c20100c001c0c0740c0d8a0b040d4203010050b19a00c4030b001e00c004e00189681440c1c007402903080c0c00382001d1030f1044a682c1c40b003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 955859145 1250 955857895 955857901
    0x150a0801050c03041e030f1103250501180c0e15030604060b1215040b07020c120c030c060906180319030c060b10090b0a03020d1a0a2723 60
    0x3501168009941c11a0351200040506100540f00d45d078480d40140c156403040400089504203550450b0340b018001090b0000b0007140401c4655059103299070a03205400990864007420982d01710388060074680d03041000c240102000c20f4941c0e590b40192045008000740a4403000403a920800075628459010300482082106000e210391155212480940340700300c49101d03111280ba1a1004208401284a01d480108000c00c20044400380c1c001c119004481c0402e0b16040003c0014604142089142d80400b1503460181000d024801600c0030550f03c10703050141c0c08001079441e01404d21280d80e0152070964920140d901080000e448405451500da80700b230460030004d1416042940550b5203e040c20005001818a2040d041c200c621079581e00c61000d04004815405030722120a10381015001d005542c62100b0511949051041c11080007800c411800184903001c022544901441030400b8082106078909200d00d035a0414894000542c9007443d420030f001c100000c030482c8074031061407410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 955860395 1250 955859145 955859161
    0x90406050d0f17130b1803010608030a14190f0201090b0705130b04030317070915080109140103030203091323180303061806010e150421020306150a080105 68
    0xb20890781030040c40564035000312248a42c0041c0b00350038085182c0b42c41d10038104240f4490348040c0428650b8528401e10540012002909403819500301403665040000c811a556400400840b001c902c030600721402e04401243c602c110041d00c480002c2803011028040000718403c0d031140c2c0300c0c0340d400300300e240c0b503030400fa04000c149400214513800241c0c5201d80208919902c4c4040d6400c49926507526003481e40450340444282e400038180c142842880c1c000465400128810070f0000203140d03440c900d05626004860095801401d6050242e18580700103001003680403044801c0081c0c00e44290401c01c00f2900c60000420340f003180c0c1502c42220700e407084c250920400000c1d00690b402c2d00d212105203454241079490b884152491507000c8900d0640a01d10044049019032002050404400d407102d0a0302080303001640103d0060702d214002824841000c4640e041a00b6420b95120140303206102d50100756900c00103428801c1c00f0344412a004090342d1000c250030094103401c0c00902c071904141c60 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 955861645 1250 955860395 955860413
    0x715020f07060e1e0906041805030a030209040f0510050118050a08011b1b0b072109021009030803191803020705040605011d0f130213080d0c031202090406050d 70
    0x74016209602d614101d1302144504c0b40d03031049040c4000e22803499610390008000050051500c1e0706040405000200007041050024224107007803610f0150340e070a0000108003c450740f00c41103140e810300d4001070201d41010b80b00032034280c0b042803c107003060140b00031048404080561003143e015140c4a0042a1740d203043d00803204440001c21407180841e2880406d40d00398000381e11310940f11402450140101703141001042d0080c2580c10110007011440081031101600c4000610507540c603002030b40f045060000b8100070780e121510f4518651400c5a80700303906440003424149159181c003040301d0381003c50341c0c005100e00c001024120300090b5146070103500d130492842100d100e0b516013840021154010448864036500d000c1407101704040c140100403d41150030b02035038200e41740c18903842120a25200504011444071069401246840001464070540203c45010481d02142120009402001d020140140c40a01580390304012000c20010207160b4032140e80718079800708190600803121 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 955862895 1250 955861645 955861667
    0x2040c05160c030204061a0f0d110301120b0c04062c0d05060411030a08040e090a0c09020c100b060403030815100f0f020a030206011e03051c110706020715020f0706 72
    0x65010300c86c4990b54101d100103032444400740700301010200700d070680381c0800b40c00502c99125000000107685451420b9842c41c2e8100b60000518442151543c406006d007003050554800b2010514502d8a03081400c000d0007241d80f00001e60201d0042c1410118440001c1c0501c1d465010260241600382100e00f01541d4590040e6000c2e03803a1122188503412030300f4003140422003941c122400510382132800110b03901807607000742a081c040c02014003800005101c100b20070001c000c01c0d1302c0503844444000e041410014640116403c0c5458503851a6560712a4400e81c0c04682d01400c0c0100c559495030120a603507161804040d91124040d000103100d560011030022403080340b5943d0303000101070848180da90f440e6000c1d018015a12a100400c24443d04851a807202189822420040350762035403a01e10f0b1a42e40813060000c50000559540307610b5009c00c0180ba808403100080c8401c618083d000f9480c0d8800780152402d0001405441c0902e034002c01455140c15580e10450b01015550740340280740030711074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 955864145 1250 955862895 955862899
    0x30305061f0507030507050f0105250302131205031b16120f2d1101020c0901180c0509060310053f0708030a081b040e0402040c05160c0302 61
    0x4100a0700d50729070500c8468036102a548a0324904812030302c0c1540e242d04800012140c602c6402040540681c0a0291070b0040c0c26807015064002000d045400d0101e60b5a1a00420540305000c15003549125080e144103d079814407810000c4029410700340d0641c411040d6990007604d5442101b650a01c000856205401c038061076660850f4446001c403517140c5c403081e0040d040011032005a40460b583c0050210583c0341d10501c6144245014481100c0c5006a001581c0d03000d05207020006658050060340e02488084550250030740c10100301e8001d0b00030010061700b456640c0c001e240c40c1940600111548032000415564503032900d6901c8600300a410b000d11070040b41b001c0c042182d0b0700c0b100c81d0007100da46000c04108034041e9000d101100c1850408002005a1050320000501d440c0244000c00d06100203607205000792502c104102c40030401e54001d8090000200b1040001c0e081000c1600d0b04640c0c1180e0200c0c18070180d07030044586005420702c10090941c1d80c60b43c1030403c010803480108803482 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 955865395 1250 955864145 955864159
    0x30f020a090e0a02120106051201020301150f140c12031609090219080603120a2703150b0a050a090e0f0c0a0b0c01110a03060303020c0a03020109050f06070f03030506 73
    0x715041e18040e260b40c0020100c0541c04903003040300500d8441d194000f451410000054040d550300001001c3c504021701c410026540040180003000550156045a00d69403d02c506500320007030b03000b014003c902104c038503034650104000d15095002d010600d850320710040f1894482c10000040501c044020402402240e82c043c1c1c000b41c4525180280c84181c41304a0f88110480e54030700c03040c0c80083c3d0040c103c56141c01800c2c0ca000c284e00c1000003608001541c0d0703407450321000301e2042568288900020030052042a00c0c0c082000448004080007281250500460b4005143c408540e604859030040c0d41c3c000b00007180030403204a66840584060944c0d01203640100074070b10840e8558100da0090f0350022256030060001d02001c80050100c1103201000007151491000c403148585c01100d003480001e61500420414940d04018602c0054400c40d40304000d0313131440d07001800190b1541b06190040380cc150340ca1000c1c0d031b5002c0a441105030003a01003d02520b00d440c0042c01410104c03030042c40780311 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 955866645 1250 955865395 955865399
    0x11040c05190e09130201020109021503060a0b070203100209031e06090c06121605211b13140f0312041a0a050307080c070f230c0105031f0f030f020a 65
    0x4840d6654290b1454050484030f032944510180080400002000740d0541d034a81c00c00400684030208452944407401c0e00650310b0b030414004210880038241e00070001640d050185002584d004542101454104840180d0302c1c00700030040303801c011000c501c1d03002d40424801c490441410200d101407103031542109465865100100b0040315000360313440da090040201001400842c50500340303c415000c20b080c101c0c204503003240e40002c0c0200c0782d800d641d40e08103800180001e02900b288620f10301c4c40c0c1c0c507440c07608100381c0301c2510040081602c101102c0c00e00c10046100151600505017a20b0700c0d020f0141d410070310300310456075100e9100d031103509641c0c920030318030050180c0c0c440b00340d50110005a80e1b543c5103803500312080720425000750404c0310b688410802c1e200001c200d070f04458240e43c400c80d000304036008901054110400040d40702c031980c0d000811101c2450f03a12004803030780040c4002040c2d4010140c0944484130758801c1d0003085042080903404002c0c0007075403603c40396803032003222003100c01d41d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 955867895 1250 955866645 955866647
    0x10501091b050403021c080f040e01090506030a0f03121d0c0a06020601090504110603071211031303050723030304140a080d091703131e0b0c0711040c0519 68
    0x4022803031400d00090b0144414001854911848400030790031143c4101d810215803240c44080c3d2190222178680e920001b010050703041c0303080c0224010104100b0800080c5420f02c0440c5e215480c01000038130456054120307504041c015080c0244440c643c40c41002004ea2003022070041c2070401175035410701e125544c0d4070083d610300302c2002001e403500d86c3d014290b580d2034060799034007900c0054001c84007040c090980b00c20301d454410165116500c25520711071a200d022828004440741d84422103100081001040080111f21210013903466041c03425940d03030805400c0c0303a401090105136072242040a1000c4a505010001c003540c0558019170b40d20a14540c40c010440d0342c4c03040c1520041112105010a03400103d0301c0e4810b00d07200c0d0041e0850f2903401d00c20002c440c883d078000c8560340c0e2103050b40c40f24142070284480500301c5a541d5007000c440b40304015118521111001030100418202c0010301c441040307841ca0000f41a110090014040d26607080c0f00030700700d50024160040588071000c2000c0602d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 955869145 1250 955867895 955867931
    0x8241506120604090819030605270a180c090b120c010c061103010e22051e011401031514130f031206060c0b07180311190e041205120a092301050109 65
    0x79050304854682c44483c0c03103102b1100c0d4400104942c02c00e50ba2a40fa14100a24a0f10800b1520348075504001e000d900b4a0304440450743c03183c801c64040c45030569041c600790400a14401482800d00f8654130301503c61800401038405c0300c44c2041c0c40c42c804400011042c42d00385640d40a00280541c00d0903007034a29410110180143c00042c0031540054813000710100c003111031188081c0000008512044c0c1030002c1e0318400d0081e0300888078642902c02e610f04902980c4580600d0300000b0100b01c0f0203007026444c41d1500d1001c16405000040804062400c040c001d4000401c1011040010b01030a070391048017400381d0f00e001200392941c55004000401f041e114428a2054904a1604400b0300f411030701d40c0c184000311114140d40220303210300e4440e102c410f0082c00324010003180051300594609440c11402801c07084c09403001380304007807007854005484404100d6100c0b071001c0b00051181103078104403d00c6000100c400b00780e42c0f021094400107582c10f40000781030714007010707042c41440c1c01c1000c04084 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 955870395 1250 955869145 955869169
    0x60a05060c060105040908040503150a06120f150608070807030b060a03240f110c010605030105040506070806030307060e0607030506090603030405130608241506120604090819030605 80
    0x41da421110061005103010b40c4088038181c00303450501d05140d2242d004c203140041208400041c6010031041044040c011b000d0a0082c01d8000420032081110f552a41d050709040ca000030315481c444610b0360b2001c03007194403220080c0b030980d0031202d050350380724941601d80d07000c2d000558221100e1800074125003004034101c02140d600a440d840c111940f8240005603694031086070103825240c22580c995039040340502041100344c08111683c44c54000449400c403010b550180d80664108406c000c04108082451940001c107070500041c00c2c0c0d02d030390020b4154400c4840003401c251074076181c020540300010380b00b07103d2002500c0402c80c82c1c070b9050410145e09002c0310181e50580c000c10003840305007801440312518a80011000c030b10307607440300100790800004161026280d00016603030b031803918850401c5a0400105482c1e00c0b0481031b4280070422030300c80c48541c42181030440c0042156903c0d15402520500d410000c0e89480301c011800b270000d0341c2d542d44d03c0c280000e07080c0700d4003141502d0520301c0004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 955871645 1250 955870395 955870417
    0x3050c0c0105180d06090206190806122e0f06050f030c13020a0c02040e16090203010602030405120c0411040810050c030610090308120a0e030306031002180409060203060a0506 77
    0x940b0300b800401c0044600004c801190301a807035018200050f00c80c540135049040c1c211080d6803031306803010401041d500703000b0710170b038494090702e07a003481400c9003c50240003003500c0304094241c0c0c1e4000c11040d00340248480d1044000d41c68000d401002e211260321100a45e141242d02c03074400480581016034541d074100c10281d100003888a84c0c800e0400a0b0300401280d105c60400f078002c4905900001c04a50030801384a00e140c1041c0d440d90f07425030000c0b841602030803020350308508650409000a5880c02103003c1d00b40a450003d102c4030480500708022803402c1c0005005100c100754801c0c0202c82030700300703110381e65081c414010030000013032403809940c6c0300d8400045071604642d9000b040050088036500201c05018010740003102148000c1c0041141003800981910541040e41c0904211210404010b0b2283c00500c01d0202d00c1d40d001c620340301c2001c64900050b07150020003094594803840441ca07030354000c1c5406404420011117801071840342c101194400401031741c60082c000c0b1032040c2c00f010701c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 955872895 1250 955871645 955871677
    0x50a0e030d090e0a06051905090f07230d1806110a05070204022107022505010c150f0903020a06140105060f0307091203080f1b04031e0f03050c0c0105 66
    0x400500001090280d11044565005c540140d81d240810005005151311050402500c0814030003410000d140c45d802c81910f0b0700e40c2d81980f401c41030081100c508070188034020307141c0345c42c2da0200714805803d490354000010801c2241c503101030020364945080c03400403261070381403500c2d031440150000c080d10702e0f17030074180c40700c520b040480d84c200002580201d00c4030040340a501d065020020090100034441c0800340c00901006114404d1401c003801c00c030318118036048117a101400566407007103040e917040390f0049062601e514180c03180c1c009428803490301600c051400c10688181980056125070075030041301c0800002e81059107444419100340900e81c0c0141040140000340e00300c413001103921851514200040a403110040311002c000100c0a80c0010015800c0c00311401c03000c1e812a0700b00b0031344400a20310300c07920000c01201d80110700c130142c1482100845075401000741e8042c0164194010240e66040e645450b014000d90080ca00464451048440d040e90719401f8000b1110b01023030b601154 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 955874145 1250 955872895 955872899
    0x60c080912130b0d0f020c0717060106050a030e151306110a0e10050d111c06080c060a0309021002070303080702010501050f0f010c1b140103180209100b03010303050a0e030d09 77
    0x2c1c1d2126480031520f802c8417980c50311303068100000c520152082c2d07030480014042c3d4501d000c0119002225407210a001034014070010040c0e1a0000c0888041e54042e040c0403c102c2524500107051070703218204c07400701140480402c10104c144a0403041031a02c26402003000c000c07070b80c2c050f441c1406080c07a140085030864107509007503d40100101480703103041c81c03da807401c05200c140ca02030360207110400340060070101d12054840344c0c43e80b04817510314044204101076850204c0750756481440310661030241d480000c9541003d8442e13002540004d0300680a41c4002040340f0700203503926800d1001b500003525541c003085400340306001c0e0504894004051500d061803940030010007035801c0790f019052000c001c01c1d00e030014004102d043c81c501050613446140c107241a60119400d8407c0c1c082c1d0381014608007800785803000740b124502040e5010303070b444805541c034503002c910203c400e500203440c03c40002c03000104055010f001001c1e20180740ea07407906c0488841c014199144600054540441c01218003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 955875395 1250 955874145 955874159
    0xf01111306111f05150306060a0e060303120c0a020f070f180212041a01120c3005010501080d0507020603190f0e03040801050c07020616050109060c08091213 69
    0x420b10002c00040700b0b803601400d1404100030f40b8980c3c0003660b0304441d12041040324803640201060f040c10000d901030f044a02e000070006441118600516644214010210306192003c00c10350314012012901d07079409042680802e0136a40080c00b5180040c4590100c410150303501040b20811100d081210303809c0b19052890294404e5210b820f00881c09500303205ca081082d448036035882c0254010148001041d03009040280c12107016009020310104000070800010f800d5401a81112103000302c0e1140d0310f01c0c8802ca006011b2120300c1072011464402c03c0c03030081c4030046d400701d4100c030140e0084a040e601003501c140c80034080d00c0b001035804034042c070020342d02422581214480007000324000544001c501080c0c02120103040c00016243e0010a042c4a8840c0912a050f004a0071500c13560901d440350f0700143c068030844041d8920f96156400710020400e003501318110103948103405208401038003400070182e00040320341c42c520344941c0c42c50111004402c41200d0b130444040041410040c14506 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 955876645 1250 955875395 955875407
    0xa030320040f0b03071701061e0e1507020604030807140106061409010e010905030d03060305250303051c0f270309270606210c050d0504030309050f0f01111306 70
    0x2c03000d418403503a081400b000d100e01c850107071f001e00080d8603251041c403001070381c207610201c40240303080038000e44a5084660340da072510900741c50b440c0a090a951101148040b852a0140f60300052410201099810811880000301002c4010150080101c030382c0c0c84104482101e4603510100401c4d80821403985907500c600c100818104041c14801c003490360316400300345400a0127110f03200080c0d40300014010007100340f0800c1c00407510641014242e146503210318030710101e584801014004005034030700761481c1c407405e142034588085404001041d001204d020281c51680d002d0003500084a02001f001405d10024820598059484545950030325400c4600f41e0551203127404044161038905c144120580100c0010385195600c81042100054001c01c10141d202d072142d51031070501c20340c40001170341304007a520844600d038004030300c9860324102a0024103411070054110b002d80381800e0130f076841c001030b40c03540382407400000c00900690040d962141d0140d20740039042c9186180e010001548105 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 955877895 1250 955876645 955876651
    0x717280f11010e1b0f090402030c0d1b060903020109090c08010918020303030405280807030f11030d05240d02061e04090903020736020c0a030320040f0b03 68
    0x100000300c0140d402d0f021450302a07030306034008582032480c910b005141046040610403860982c0d810410742010340c00692070792000302801b80200d802040c0d40051150503050035a00c0002101440320301c3c4d03250300008100b0507150205078089001c00380005900e8403103128000b999400ca98a505a1380d0808804c1d50103802c802e43c00703c0c0041a102401400b5907018001940160701c03c000034140d8a401d60100d00101041086036180352801d06408004030721158211030320103601d0710702103040c44036016090b501c50900e007222185501c00803451500d44199035000e9070044158012001c405c950711070504902c070394800342003500610b206120710018142000a0600100b200410954001102d420190150007591101d100e1541740c0880e40d052640522441c800340c07441c80407000a02e69070354800c17090007240305030520b2859054661a0380034103245d41911034408098065600002c01418024064008501c980e000486000f4030035040080c4041220110388900640400941c941150020141c00c01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 955879145 1250 955877895 955877927
    0xd060c0509060f09090f0f0403030e1501060302031801050c160204020409020c0a20010903140f011a0910030209130c0e13060c0c23030717280f 63
    0x28441d449095450380050445503420344038440d118000d05040145820000e080c1e01c640588003414040105280710b0241e5100f03030182008110058280c00a03460a159540416221110080007090440d41500110700542014209000500040c10100e089410075144403250810401c2908140610400200c01c440e000500050829503a070046c007050b640b107203c8410b42504100010400c00c5107921892810508043d5108d8101644000281030040280005800d40c40c2880c0400b00d001b0082081c46050200324009201d030840080d00340b00103100c502c81e40d52040070301d180010b4211810b101e003081180e400402c0b1a445454415043c0e10f480501017003504c220104070000b28858401d4001c1a00030068aa8600c5262150342440021200c00c0d500c10b4040110005004010540d4a04401b1494041d05029400711034000d141900c3c500c910341d4001c0107480d41c40c442401825008003d8401c4c0d641c1c0d0048031301401044c140c440e07110b0702106d00c090003040b5201250f404040c0301d2540d100c0c9074004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 955880395 1250 955879145 955879147
    0x6080a0905070e040822121e0203120910050c07090b01020a08130303030506010c0b010905180a0f0b330616200a06090315021e07051b0d060c05 63
    0x1550445815800c0840d13003503418600010380c141130801303208210b5400100c102c2c401c103100703404c0a85c000740b0140685005022040b4039041d070701d40540210281140294003c04481460396491031903d010340201503024403688590f41c2e10382c5101c0c003540440c0d40010380080546803250502119a00401400c041c65046105d84c03404580010340c2c48008041e5001082410800b05145250060a071080146120304020907800c40100003a10b0700c040b181511498680441e0319a1100903195100e605601d190400b80718140c00309050001410a000210340607200541d140e5a40d0003c802101e12074403802e1650102c8800609524000b5001a08841a0044c84145010b20546a041c0214004502910010840d00303028a4415203099540242c540a59941118503d032940103015001644005000c48910b17900c00d820036881e0b98101c1d000e10007101c81c03444c3d49410790b502c03000e135035000702604031035921580050b070031007d4841540b40c02521009120b01c0d01c00c480e030750340c4a025040d607109650500070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 955881645 1250 955880395 955880399
    0xa090209011707170705030a0f09031e021204090b040e06130f020a05040c1d01020c01020c1e0a0303020a05060906011208070501150803090f041a190801180b06030706080a090507 78
    0x40800485070040040d0346e21075890341800e011603011500d00c1c52040801c00c1c540fa0002000a8202e07488250061000d805140d11140750801641000181c070001045202e00140c086000c0704240c0c002c0d01041c006a070200520b04410080c503588801c00d445085841c031035440400009010380042e074032503d00c0070340000e10340ca59901c089400c0e40c1148108401140303403001001c15540302d541013000300c01c2003440106046801000043d4440d000750501c180106862424525602e8481007507403550500503003940c5d445a502c0c00c0c005c0d10b40c0710042048400740122408200c0b00c41000034840e05803450040c11a007103408583e80c2e0b032002e6000450450b2030395201c1c0400d40721070740d1b0454240e000302440c401643e0303602c641e032003040180d0311000c8038240300d80d280c03000d55805004041c10702c0b030350420160ba900341401120302001007427800540c004c220a6003000154078007584014003254010344a02d002d042c0399120182010307210b031014090003000030454400101503071141c0e0040390310980504180c8440f16 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 955882895 1250 955881645 955881677
    0x30206150f0d081608040914040209190615030204030507120c050f19030528050601092c0a060509010c0c150f060308040501200c0609040b04050a06050a090209011707 73
    0x2200c60b413007910040c1010074200004051406510317102003c80485000c10701c1c069000030f0f41064007420703c02e03114446e0040441c07030200641c00031700641203501003425600203102005000e58401d0000f1200d600414000041c00d100c0100c000c0c1540b41e01c940c071220f955003000107104441588a0100780e00910503107405542e585003001900255000d4401f40c4201203104a101104400e0079002500c10064561003001080e00825200c0c1907420141000c0303001840038112040f0380742607030240101c4100c01c685490141d000003c0300303040e40303108100c24403155035460001e41c225980866880e0200d040104800c00241c420565005413891403d00010f0300294012480119422504200c0341840001401c4c0082d42c1c006001b06a035810b0314814a90100548c00c145071075407400c8251501841c404502c2c1011642d0340d070098008101c01600802081c42c1166206016194520608c0d00840e85d101002c200d01c20b05000f10741c0301c408103856014500c80b00000b00759010000910074010820144101c860034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 955884145 1250 955882895 955882927
    0x2705100c06240b0a200c030d02010506040605040e0606040903050d020c0c0f0a0501170a0617010c092108030a06030c0b070303050f060a23040216030206150f0d08 71
    0x2660411940403100781d51180d5010b000b030000d4125594035001402010026039100c1480c00700c1000c400d02c4542a0b1024100081c501071048072040c0c2e040c000e0307880e030320328003030b8150f11087c41442e0848080c4500341c0d990b01030200700c80041183c1441c80c0c11401c0007820a0911f0313008401010300c070b0310380ad5140a04600c0c0701c104903044201410b00540000c03088182500d00b210918000450071112030314440d18050001e0803040340041c07211000c151410010f01c0380c02c696404603004024180d4961030300060340000b18002e2610000d4540407440203000420b4036444000161400560224040f008c0c21080d1980c8005401c002d081c400426160040440001d81c0850007100800103904515200c80d050302d80902958401440c01e000c1495035000c010b1165a2000b8000c2201c00b000055940c12080c4c080b41040c40c10030640346a0440e0001410018240c1500170864485010743e0a94116445060340c524048981185043e07000d6041d00d8448003e02d04507007102c030b40611941009181c0700641d410f1a40d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 955885395 1250 955884145 955884161
    0x1404060809160801020409050105090903160f0c2417181002040905060a150504050d021206040507050a0611030a031d07121103010203061e0406170d2705100c06 70
    0xb51750003190400c08122540515405400200c49400032490003d40150b9280101780c6400c0411604907810300038042010400e948583c1c000c400250b5a80d1209020f03034030200d841c14081c001c1200c50515403005413090380d403001000e510010060840e2981c405070b490b4940318900c090068090252009020b6202d48024401400355100100c0d0520b0034000704004a40c3c0361780904802c0780514201c03214294010101c4081d600201c80f2031145c03074205d0010404400ac0e0444100c5a172081c0800e00081c4080061580111607084ac0c4000c1000c0d2110300451311309000c20791142c0745500c14000c1e220b0031400fa4100f6142c007038243d0001d41e104080414024940343c20703903100d0000801001c0048083c80342200c8410401d5000303074001d6155040507008142440224400c28100a18184101400c1e5580da0801c200800a14145411000f44032001940310206403100002013220081004480700070070800d041e15801e4170311102034451500b03080c4242e01c244d0412a5080001902aa0b0005070b00f910070301c18 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 955886645 1250 955885395 955885409
    0x7050f1801020106080a0b0403121e1d0703031704021207060f2d1d0409030806180121051504030201020c0106080318040e01090b0f16140406080916 65
    0xc4240d640d800181c00c41d02c1c039070840c1100f07400c26000400880c01015009420640c5440d21160640c103043c91900181740700402d03030005207640302d403044034504190004522040300100026080403604180c598031030940c403005011440101e0092140019044402c0c1c2c080d0000d0100d03a130450110741c100b030a20140b90800e0010402c1081c01c0c40c1c0c459400b000101d4424010b070b0210314400d010301d004608084450241600300801c0c548032254030001d8101d100741300c100182040c0710f08903451a000e084000200c490f24000d0442c401da03c1ca0a00503a400b050488042d1541c030100403003814100e01c10182c01039400d654a05c9840b001d444034200010b0002d10550107130f4001030301e50301d04000490a4032550341c420f464950062080a004000c4c10651002240d0100c80010303104504c146614054580c0101c043c0000d1303042800c009580c51060070251040090001c3d40343c400301081e00070384440c4046c0c01c03000b40b0f2210a010920425004421064110359004200c48864060040c44040303d862038100d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 955887895 1250 955886645 955886677
    0x120c01180b07080c031012210c0b0f27032206030507020601051f020f0102031513200307020f06010f090f020c190c0b040e040b06030307150507050f 65
    0xb01e440e80c0810440d4004c2031030080d0a2460804081011052415014050f01d10310900d01039810001c5100c84109281c6101c1030f03c03d206100d650011300000003943c03040d58415400000502c141144c02100740c8541d00207408034200385103204403207140101041ea010410f00c02001000401e80030030a190350b0415010070204566401c1c00c5c001029203101404420955201d14010b0040b541c444110040d14407440e803001d20b5030f500b8090101d1400c109400110720551000007808010011891458140300054864581045004103013208903816076000e0f50030729980754604009950700c80011a00a015403040f1030141218074481810031f0400c0c1e004030103e2001410402c0880c005004080303111201c1c10046040c8040d84032881d0300e072b1940800e10f91603d03198600d40c80030044100040c0c409040581c0009840350307194207681c0c498500644003a40d80c1020000017490620340003048840050b07100724075008407000101a40c014010241c0340c401445414801000e95110000260590940c540010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 955889145 1250 955887895 955887901
    0x20a0e180f07032904020f0301090c0e01030c0510020703150e1b04051b07120207080a030c02040b04180b04110315040c0e070f0809032704140108120c01180b 69
    0x207020740200a9403031800c00134081d40c1016550302d45469a80c41038055030340d1861940380c000024014800345200802002a000010506004440c0d201e0305881c840c201a2a449444a08008602e5400c0a00c2030059022003000e00000b20300c203001c1c1a00000025001c02c0310803001107081c0c2040c034a80d00340c0d0441955422000d04078a403c0c01000d400600040e08071100c202645480c231018882d000000e440d810501410100803482003091000905207031003134449100052a0042c40e400703164800740e203d04e003040110032075442c00c2c2c031815104a03011002d0040c03221442d52000d600715030080013a5801518601080c0e01038400780008048000b1622114200c3d1405140c0300c0f10b500400d402c440496500e03031041103c0340f034201c01c040d5550380c1c0702c0c1000550b03681c4801121303286109208806000c1d20001860460400810755840c0107a07000700d5045c444442c0d9007040f00c0350b0210900c01d600142e400380c46907010000e01d0500038990540110004642640440246290410540e030106c1f0809209410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 955890395 1250 955889145 955889153
    0x408030a060510020d030221091e06010e190f0c0504080f120703050c2b0f03111603021e0a0201110a08031b1303060b120a020a0e180f0703 61
    0x3058080d09080750070010035843d01e90001d41c2c9448450544050590005030040b5844c08914030414680204000c3c840c18646034036010344130304a00311034800424075101e00820036000480c0080c10781d032020f0760f08c0003213a566410041606607008480c1c02015a210818034a88610780a2205040169182e0780d6440c1c0c50031003c036150001c10039080d1419040514900c7c0180959400c6400d1a0740524255803100c3d08071000b1800c0c207660400f8010415440c10740480a420303491071200c03207140c9940725600c82403a904410b0b0b0903108510340781c0145040401ca001c00e600034000526410728062700c1120104000310802640822400e09220000d500c45140f01007150391050101d140071900d40702629003a04907035191901030001825015404580054140c1c1c401c3e4803a082c4c0b0000b000f07252108207c02e540c0c6c10302d03e00034015582c4180c013460604010709010b8800007840310110341e0180c842c640381c9260072040a11090701401180b8001c0329034110703d4402c001003000000526059002d0902c043ca0b62038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 955891645 1250 955890395 955890401
    0x18011401080d0305060612060303040909051c020a020901061d06030a150503030703170c210105030f16381c0e06150103020f0a0804050f0f07090c030605090408030a 72
    0x44102c04160601040107482d03183c00302030f600d5401d000d4502100c6a00c41c140000d007103006035000880100d19014a080038002d0008144a4080c0d08094808462a40080491300d4400d9054003940004d005d02c01040100c1c0f1030055a0108400b8000b140451031340d802c0082e8003540180e541b446182c1d1030700701c4c1c0512903460b1504940108000c9000f10b16000b0b140e903020740840d40d50b80103003011031007000c00030361240c1a09048a00f080d02d96503004101c000009061520300c1d000303000e640c4c00307846aa4800e1040200c00101c0350010f50000c00d034910b03030a20b4030a510034010000c01048003036116240c41c50920345210950605007408103108951180324024070050004800502c8400d82828520810292140400e08079085461881030007029000800141d003c1c0c494818544002c140000751954525840401140154810000e0f10155004142c1c0b01e50780f09684076542d15181c0021508110742f8240b90f0110340103840303900b8045451961000020f818200807142039a50450020801045504070700c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 955892895 1250 955891645 955891663
    0x20d090b040b0c1e0f0d0606171b090613270b01050f0d02130e01081515060a08041a0403030506010e0a06020304090f0e010c02010204150908151801140108 68
    0x5040f0381d050440c44591103200021440e0401585603001030a044144080c0f400c64141207034080c01481910b0f0348400061284914500070020518681e01040901030526402c89161500c40e102e6400d10420070208012075210032400000c00000700e43c00100710307200d08000290078424040d0704169041c0c030b1000805441d12564040d0410008000304041d0100c0301041e1186401881070058441c4402c212526180d03203650015440700c0d0401d000040c0510001480701d031501c0110b80e004001d5210010000d61030742d005041d459002005008850545200e4420700368418090f8444650f107600d8039551040070203007034805034002600c9000304451560400d80018800600f500d4519031175103819402501c3e4000c50140c1022a41c440b400e04500c590990860604580004003c00550762000d0019000f540148030f0004070340d203c84240131206004030840d40071285802c0c040c080400b1543c103d414088402803100075201e0400304602c841a10911074418181d245001d14144e03941010f507424941050700b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 955894145 1250 955892895 955892911
    0x1d13150e060105040911090d120e09010317030618070201200901210b030f0312010b040e010501030c031e061e031e0503250b06041407080a020d090b040b 67
    0x60280001c50368028101c1c0c00311070301c184000510342075000b44000ca5202d2042c1c5654420080c02d028001c2c0401e000904403064159202d81e40c600d609030041c000040c509220240040da0314007244281c007a0010021a8010701c01031603801c1081000100e003108090a444003401030f9502c05003802c06d0f800d2012031010341000c0c405190308103490400004c051940c05044ca04141c000c00c032070b404509032745402c4074a200c10010180d076a507005404c8485e5594001b90b1020103805041c0b000011815808070407201614074004121169a09200064000d482d00200c1c3c0700130981e80b41140c00110290680e214200344a1500102e60345241c01112032465a00041110b00f1084810003003000031590704030b0412030303078240d9051100080c842c00c000d170850103010070000740d0040f0070315040d54006050302e100b14424841c0f004030420303468403400c0c0002c94080e08030442c0b0442440c0c000c1480540a04d100c80e41c004035a841c0540b41c032a001401e0001d881c0f03005001c4654030074550a1100f04a000214680d100e880703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 955895395 1250 955894145 955894169
    0x60b041503060227090a1d0a030512150d1103190501050601030b0f011b141f0e0a0c05010810030219031403070b19090b1302010f020f06071d1315 64
    0x240c100041c903205000d0301007489a50382d5014660704c0150150100d0511fa40c200c281e401c090001e05000c1c0c001d0f4440300720786010b4000c583c0020501c114140c0303018040640a400d081da001102c1e030b5809008102d0b450400d906100c0c0300c00d00c0b46000c0204444054a41c41040085501d0402c0e0380050103648001500318410340d200482c200c1c541c1d03400700400102e602043c0200300c004034181400509000400c00703000c560300500710600c4442c400c400d070a1414482c420010800c0d413030480021502c0b0003401c1001410122000d00800c610b6125110340c6070021400e0048540180e41d9a000035003425125880101c3d44500d0501041030005035410168107010071400f8500d424029510744c80d016000a00c00606410001203414200b0390580c4805401c82c1d2203040e1000e54201400010350355003a14008900043c10703030b94203102c0d00384040390120038404010b00030800b60300c445806462000744003000e036000c00d0170000d02603901d0303444030800c42c4181c6440a000400500003000303000340c06060342015040040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 955896645 1250 955895395 955895467
    0x150103020114090f0d05060403140c150a1509060f0501181a2203022106060f010225050a1e03121106150907140403060b0415030602 58
    0x60001984002d611403102d105a8030740740400001c0d003412201c80c405070030020700440307031040203000904540114001d444081902010a0220240b880f442d658080d0316049800383c2100c51200307020f0030341c2004204e400480c0310300c2e0403903142ea40711440780c0c030125125803108400c11030400307000c0032280070b0300d820301c2c042110100503480c1ca06003824034820f900d41c80382d528000c5000c1d5107442c0d0549411034010301c1d90f07803d191107118102400300c08500059100302082c010554181c00004072004400240001038002c690f0f0f0b84c1c0400c00301201e009800c41c1580035a451199506880c0c0540403c0c1409c6451155412400c0c2014800340c0f4401350800540040d105652941c0d59519495090880340c0c4a01a0a107030107680c901114181c9901e4594921407046da070520005458055284003010f8081d0307a14091a5580c0b88100e0341c44454026200940204100910114500e908008500000540013059070030034501c00b81280011540161103450340800c0e030040980075101904800000440d60440390301d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 955897895 1250 955896645 955896647
    0x6031103070609030b040602040302060711030d08091b12010609050f06030c0d0611090a030305070b0c090f0904020607080a05220b0909041110030c030b0306040506040201141606020c1501030201 85
    0x3283e60b01015008002e81400201009450b804407009180d014080d1610740c405407034a00759002c100640b2611138001c56100c812980d2190301c81ca889189081e004000070310398401c1440500c041c42e86131940103556000c0c1600304881c00d0040d0402800006030000700c1385449202d050400a000e0b03c0203219130030080307480071640d50300451060f0b9281c11081c0094030036400e50b0b0000c5a481a401403a401405100c8000140358000c4080c084150144000d01040d039030b4100f14401d035224401c60b03d644900744050a031082d042454449070b000b0300c06400145001c031a82c80f401056004114400006100000c405035100109001d009405400540c1c0d51400303810040d40072803e000c2d035000300d40200c445d840050b0034044070144242d10328402410100725641d8000006001d00700e4103007004003003400c05c2c041e00c155040c0000c440b032055070030001400c19030b20740f47e00440b10405c200041c045030000a0051221013050645403000407481010010382e00c9290f17100d09411304803041c1e0381031306486400c00108007607 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 955899145 1250 955897895 955897907
    0x20a0f080112021522091a09100b0a030b1206100905371109120a02030601060309051615080106030c020601060e0a08060f2a0708210a060311030706 65
    0x58100c2000320303032140c082400e8807101000e4481600781217552030703000040000d180d40c4075541100004158102002c4580140403c2e40340036500b07082c08000800d420090080510040c080c01d841300e140210b200d88803500013500d2400ca01020060a411044c01c2c015981c007050248402032000d444144080d160644046a0300a24408140c010342e4000c0150702c1d80540341000711001820720401008283c4102002c0145a0071212f40d2902403c045e4041d809461000240251a03a50081c0104056800c0200840162400c060210f4442c412080403034040766901034103030090030707001c00c0892800d42d6210b4000c15003c010ba01980a0624280081383d41a0340030410034190b98243c2000d0540d0313031203000403c1007000980c0c006952030044206000004000d0f0000314010300449034071404060004404d00c84000200d208407100050810401000800304030207443d1094410240c14906a80302d40a04c1d03100004498020800c0d680b900e003841000910482041c10b03040543c000c1101030b0030040b0203000707 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 955900395 1250 955899145 955899169
    0x120f0c010806010507020409032f2814010218010e03062a2b0b030613020303070602041409100f17100219020d0f0912030210020a0f08011202 62
    0x401c4400300010b1456400b40e000c80700a01c0d409001084514181d090007803505240d1500348000340c402020140414459115a9a5030900b03280074001c0d09001c91214140703c900c000381d15001c0054140c180000c225585c0d002007048000c41c00160b5038a8203055a0002004035030442c074140300c01c0c5262074805840c0003031015807050203200414205036400328884c10302a00c40c3c100781d0000c0800a039602d13441143d4400010446502d0400f5104990303150002002e881f800302c4d9840d01513010340c00040035a44414480c9401c03500123000d80349454100e4540170166807240c2c0242100d00c40d1040d560056080c0480172981c400301c00365511a055042c038940c00b00b44140c42c8a07060603050002e100c2041c01406000d841110703079680d10110740d54800000f203010090020034045000d40294025070b45618062311452144456070782d510364a2904002c003800b03441c2c080050540031403054a405000c42001480104801142c90f201c522402ea00c2c40401003025205030042d01f42d8500c4000301e407005071194101c03a00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 955901645 1250 955900395 955900397
    0xc020f0c0922030e040609090c08030c031905090907030626030a11240601020709110d021c090605102103050c0f03070326240301020d060e06120f0c01 66
    0x603620142c1d003011155003007070500060b4030074035028002580c0e90056008000451144a4a00c41940c0d103c1e1015264041c81c0c1d014a00780e00100941d00650000322282d410080c014242142005040c801150303043c4400c55003900480c2d5944011700903400010144078400b104201e58080c0380404590894032070040200b050140003142c5e00303040d4482414030a0f030404980013500c00080e030042c000382002c001c0043e181035016000e03401002c9402c482600850318043c2c6101074140c41e1100040600c0029401001d941c0424a901600c01550880b03038002c2c2180503008660210351070400d903d190030448070683c80b280740c2a0308040c8002c0303c00c0c1c00082c039007241505814850f841d8840c5848441c10291100c0d034050b41404001003020426811201810350043c60091020040181280c5402800e0701a1400180641d1081d0050101c401f24010715102100140025040400200c0902c05944042c0c0000d0f4034486803004005060824400d50111600c2400092001490400003503480c0c5c1e042e800c0c4c0754 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 955902895 1250 955901645 955901701
    0x90a090c09062a0f022b1509050f160603021e071a0c0a03061d16030605150d050c0703080a0b0307030803090102070c270f0e010c020f0c09 61
    0x3c400c030a903a00c1554181c1003100010a08840349016a4108001c480c00c0f4030800e140c04c6080b5281160404c0861042407500449416000903100d1031042c880c10142e160180341c850310340100082d014416a1134103240c0300001e24610303940799020007124100c1c3c5c10035410140306219040c80107901505001e030040100204c035548410300d090000d954010084034400c40c14041c000d00c42c07103102e02001000250416a4100241900d60300358201c2c41900406036100e41001790007094100020300e62080d0000e4140c240010810740d10000306141524400c0180005c0d4008030b9a0300c180c00c03141c003070954060000400d047c43c2901d40d680181072604040d1000c2151540d50395201000e40f4100030b0f00000e180c02c2000613441e03141031064103000c0d5002c00380c120358400f4080f0340092192410102084000038610f0401c81d085a00c000400060503240c450a48240e01c4440422404c5420f00c03a40402105580c0504082d4484104a52900c0d0703d40c1e01c076600820150b000c220000711000c0c400400d18400d50860 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 955904145 1250 955902895 955902917
    0xf090409080403081303140d1d0d060e070302090a0b01050f0c01060b03010b03090c101d012001140f01080d050c010b13060914040812100b03070302090a090c0906 71
    0x72540c103004542004040c1c040000c1d01110b241c42003101207080380d1041030212442c0740210585a03c1b040e80b42c448801140303100720998012412991610417500f000b80c4642c05020064a6400c02c0d203055241400301604050018000c0d409c00b5103a5550101c507075203080c041c1e40e84034400205580314405041c01c10f4080440c80c040300c60000e4120000805120f41c488d03491b5616000140c4680e4030581d503001c804c0c4111400043c0608010018040c05002c03503d4039000814514a80117145440341070361410882c11070600710720082140c90000c50190450000582245070004900044001031324014607a11380030010070501e403000424015000180c5083d544500c4010102405064829032099209903c100c040050075026803201040700c44c2501d081c0964503a4220717542d0030750020b031009000c80c1c100300171035480c1e08641082c0d1500140380c0f84070200c0c0a0382e11004502c0d250400c1d685280080c2c7c0000b11388405151140f5840040c00040b142044030341c441c1c0c040038180040a00c0f075031046c00401030352 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 955905395 1250 955904145 955904153
    0x30f2901090c0e0319031e090f17060609090a02060c0309090709080607031505220c0f0c0f0230060c19140409020a110607090f031403070602070609050c060f090409 72
    0x1440100c1101e000180b0351f60b1b050320014001040b01d014526880000d00c1c1d0010311041c11154020010840700c01a100da92100304c184050540014066a8039201e1079441ca00182c8034580240f407030b841404c01035a01d80d80e00200304100e46034050686010030404080a02000750045004c54018942c4d042c00100c00180042001c580c0405030b0090b40d0014000f03a4285030b10300c190181043e080c425100402c240d012524041c0c802c8428013443c10000345105003400c00003091111140622800201003941d04050020651304440c40f08030340c3c401a1243e195404580384040102c01d800000340b1080c9410301c2c40c94054060307564064402d0b40208200750f194468000403200880e8040c0c9910340c000c0d0f5036180c070070001815050b0b11140055007403080c140042c8034544a50000c4c010380d2400d03c4074025061440c1c480100d41a4170710101d1140380010000507002036018402021000e1103008040f07460300391820040e06100541c080c03240120400c000c4603101c80c003401d003102c0316078004840001d40d170006410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 955906645 1250 955905395 955905407
    0x406030504110a0e1801021611030f060c07110303180405060111060106181e060c0602090910050102150403081f050d051e0106050a030f2901090c0e031903 68
    0x5040307900211900c20204504071841380491042144401c03420070503406004003030807403040040c0c0f800e0440c6d294540e00c0016140440d12258080020215400282e50054103030400c0070a484481c0980c100065520070006641709a40e54003c2c120301850030804504041c40418403290403240c03080382e40d80c0014440368080c54098a50340800412141a50f07100d00004d82101000c000d480c1807451512400221f0140154124984003401866607041c980303401416a8807504a10080f035003113800344030405003600c580c0b041d180304d4004410f180c0d03480c0d07145c20000381c00c2692410f4844269240b00c0c0405c0301180d0072400701a04006c508905941c644410301030112501c03500d802480c0e004003042c11030800d00c5000941e0042083c03030603100c003d20516408244d0300700c0c1c49501c034550b040241c1d00010000304a020304c0310106517004d1031100701c4407000b071510344012071013200300d07000581340c544018002501d85215100c01d0f405981001d504210410f00082c1c0d031030349245400028414040704590030544200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 955907895 1250 955906645 955906673
    0x62304260109060e061009090f02090702120c0703060608060f060f031009050c0f010207080714060403060f0f0b0103020708120933060a0b09010c1e08040f0902030c0406030504 77
    0xf40d003042440d03000840307903807255401d4404c8031400101202c04103135507886215038001c2aa01403d140c0e0b550440b50700340b01d01c2800081200c0c06501800500d04403641c1028001d0540305821005000304900f140707040b07000c807142d9070004540c907131044081201c3c1c40040e10300e80381c01a8044441c0710001c49072600207407400c00c03e0300003d18030f039040842202c10080300068822020780e040300c0e070382c801000b13031401203a480241d440303112400e40c0110f01c10010704800b813a140c50f980e500903020500e86600c0351603050a41344150106000325948166000300f51100d4403480c00c20b00700034681503203000c4640c1c072081918011401e00006254000e00407444541007009141d071252003e8402d42120816140768503400900c2d41c01c0380d100201e00c04002250742c84d020b01c242054070001ca00c140d080030703006401151240e0003101c0481d81d0f42d036030720018007403450350403503010174036211702c5d101551241007945200e164541d82d44600035550040c8180700030320700d000c0140c806443c1c0b2864000f40c030780c0d154244480030319010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 955909145 1250 955907895 955907903
    0x10902030631150e0708040b1f15020a060509030c0a0b09030409051e01090213091508060910180203070501050a030b06070804080d0c0201021b1306062304260109 71
    0x70072691070307584a0f0490314400711503c01d0207521040e03840c1081540c900d181114014011400080059540081c81103030701091407c1c0180c221009031515a0348800f00d901d0441d910141c0d00c4040c2d120308124036401010b51003101d01c1c1c00740d41801801803140d0f070b41e0003070024020003040094000440750541003060341d005040246041c03226042c4144000c064103620308032419281401d60011a80d0718413402100d80007103100d4541d545040c0307000c03010001090041c00000c00d030441081c00080000d000c1207280e00500c92172020700010454092880104c0d2400c2e0081c00c0d050640100c864003507074001c0750843c1200c40a003401580e800d0164002c5004000c00c2030203070783c03022007c2022000c0c0301806000e041502c0318002107030040201010191524225080000d005a10008440c113500d900c00792040c06440d00034000e0420b0441e5080c04c181600d0182e080900000c05c43c9510250580301040c00ca0b40c0c0d000076000e140d2806040110490b01561402454034100900300000f00c180f4100b54021180d180e08 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 955910395 1250 955909145 955909151
    0xc1403100e13030e0904030c060c0806010f081308030601021204060206160c150b06090916020d090b30090d030f06060e0d0609020d050a0b010902030631 67
    0x30a5064450018590145420032a501d40014541a4041d041140455059141c4031030440c0f030746041103103d0707000510480401c5070f0007001e1030008096024610041d8015150021a890010001070424000b811100100294501031012080d1100105106145c000003a169260366100060f454485030003000214604000780c000741d203a81c0883c103980078585038164201111401001103643d11041e00001e06802c00c0b808200805220691080c40d01400103408507061030705510014035000390443d010141c0000300c0312084001c50741030101c80034040701ea0509002e00b0b800c00403602158040c0c2c07003103054027906a020310000c1180071501d103032113002035403905201c9103840b003072064560ba484844031001c24148801a90a404140101000d441031640d41400311201e03481007200c00451510207444c0c455691b40ca86000d61250030740e90305410b018000508a85d150340c5864009504160711070740d40d4501c18020f001842e40d5520b100310324501134000804058414400340c0300b40c081801070580d1264a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 955911645 1250 955910395 955910401
    0x50c090f191203050a09050d03170403021f0e01241203020c040f0e060124260705040303080603011406010513090218040b060901020c06160606030f050f0c10030c1403 73
    0xa813000007010906100d0384e070054100e568005100c050810700c0c000401040241ea50038902c09440c0c045150310a00a204482c0d890f00313003c440c40142101417081101d155150f0140d59088034090107080c0000400c0c1c2c5483c1d000d2680002d46c1c8100f1051030041140e410034203440c1c076041c1403082101490404d030080007001a0710000340d64400174005258058071034080c1c0c000001e0b8179200c1c00e04541090300c041c1c07040d540c02c51658004403501507400b040c1130003229040c0e2200310703c000d00d0a400340c070907401511043c1d036071411800d01400f83c9200502491183c0c1c1003060780b40c51030f401c1000d41a0020001c0c201281c0b00c0341034000b15030301e1b000d81d41c005140700351000c1081c21a03100b11200c1000092000e03101003028182480030702c0307981d120705040a4007591000c3c014a075182841030040021090026120039105120b07079910b81690b015030b0041c2c0c1c0d00001103200d002840b1080c03041c0c03c620384510005020300c1c00d045000c4ac43e0f44051f00418801c0c1030350f45011840740e03400ba041064000a44d108055078902d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 955912895 1250 955911645 955911647
    0xb0a020909060a2d03060c0206220f060f021605010b211902060d0501030804060e0f03070311010c021801061115220f0c0504050c090f191203 62
    0x24024121080c8181d1020300400c07050b051598110b4183c030040c00c810080911074440b194128100c0104410b002d42c1c25220002c0803918500c40c404240e000c03640600b4250a02954280c1102c4003010a0044a03103071095043c00202401390003040745a0040d80409c0e10147da120240007400b4031040d000a0000c41c0300c4402c10040107503c004a2143c0880b049030b030b0740d03111382e001c4181c050001d000c00003980e0052181030b5003417802c2e40c180b8882d188001c2000e40385c0446a000c51060703070400e82c82101c8140d000b0405008c25070b082881501c50001c1611252002008a80000da5235001480003a148403103556004040740d203d05400c5100a4001d49440d141e02e4000c0700740c040c40002440f0340310028100f10000700b0b241c440842e86401802c980d41e12040c8644481000e42e408106060303004080740354015400c000920040600b422080c000c9400402a41c030700f400b44001d46000820508001408010403105030341c0325010b6103240101910890a4040f01c42107540f80040e1315008447c0207120030200f18201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 955914145 1250 955912895 955912897
    0x120509010504031e0c06050c071202030315010e010e010e060d1a09150109270f0911090c0d0f110f0a090603051006050315060f0408010b0f0f1203070b0a02 68
    0x891190703484c0f01e515032048140741c43e490341d40c440140c0084c01050b03460740869001e070041038201e41c0e50130b07100749820002d41c0c4621503004c8051043c0d000d40c001000704818501503491b1030303a10400a003081e07400307039202e000000d100b080c510b013409042c00965040c0755615241c100a0b5000d81a4050342003160744403103290020750181a0f00c50750303c1030070079030000717911039021000c0301c07883c00010303101c007072480f41042c020144110b0210900403e20b001d104c0c21007441e00c6d441c00b825001030303140c14000400303400c2c030304040300c03182500800103009056400500512a08903800c0711602c0c0503800c000103046d003508806030081d104010a080880e2408103402011aa0b0f241c0103102d40019901c41c0c1d02000d1f03032110290700f075403811546500580b8101404000242c02007004640c0305108101400c030600c15400010301e02e8000c4420584800c0c40841e0038455080c0c06d1080808140d011a02921551200c400144a80000020f880e000c0d1070071122000000f8800c0041d1810581c0c00340d1045076a10304000c0000007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 955915395 1250 955914145 955914151
    0xf040822090f0f02071e0302010209030304030f050f0d082206060902043f03120c0f030c14040306091b030803040b0a0207030c060e1f0203010806062706011205090105 73
    0x525803806040007003261113442100c4445900c112030280c2d040a40c84260942e895440c825010340d5020441c02c51103560500051001d503104010400c10807489080079440c152000380c20006550084002005c0990000001a48120201500140d203c42e04902d048000e100e041c0c01000d850800d00701140448003a0043c20981e00480d545859031291043c5440d06001508001d0000380c3c030040c200c589a020300001c24841070f0103400d042a00c8000c141a0a085450702c1500100041a00c06201072081e45405081c001e443c0074601011088100203000340c9511440c030009110075620454002000300100740e00c1c00f001a41c0850780b011540d03c0c1000480743c1c2c0115022907810035a9400107581c6600c900c01d44519680540e500d4032204915a2854018508000410760340e10640e80b24180305d0f400c41b54507000c1c182c1d880e080580c0301d5150184a520303018028141501c100804041307203010303901d0440003903103a140000a00403903845034030050314044a0f5290840100c0e04100801402c40415004140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 955916645 1250 955915395 955915421
    0x1e05061618170d020a0f1b181b03060e130311030d05090705011409010c02030708030f0903010c030e030a080a06120f0c0504060506122d04060e060f04082209 69
    0x41c1c6503908408030380710301d0140801403c2d5103011111b01d010038070100c00524213032194a80e00400603260724840c0303070603066021094192903d516801200002003401440c1824060078144441c03400c04403000035480009003e10346028850342518181849201c030010124982d03001c2da5580c503a2400b2540c0980350440c0c005095104240000a1315403003030840d41da0100074001141d0070309440400444180110301416a17051081413004101e80b071080c001442d200d54007050140d503941c41d400515086d580d481441a09042c03900c002528000b0010041b904510b030f8602e4110481d81c0c403403002c140100300300d40207101c000905c941101e0800184030400300340280640d14103400c00d95910204800d41d806c5000d0b254000000748800100320406800d259048200c81c10240d88030b1894043c0c0c01c003950040e004400714203200c041404140030880c4103462840c1d50000113042627140c00300c004102905c000d4001050800b00003042c1e400444906c40300e03410500c800251440c0d00d41d4444902000c2c02d640b41d904c403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 955917895 1250 955916645 955916653
    0x20603010f2d181103100609051903022e120f050108031903061a0405361e07051b0118020607240203041e0506161817 52
    0xc0340045002c0005816900096205401c0c181003182418031201600032003610307603407a0051104401048001365100300c82c02c030070907a52103203002070040246100e640000c3c0114a000c01c0110039894410b00078013038079010b0b01e4056214000309072071080b817403d071840d2000703036454082c0c0403a0b043e0b0b0040a00c00c0c5041c40c0c000502007051120703118401c6517804c0c400c048030f40d4400c00400460002e001c09107848414513080004071580d90380052000e1011550040d812810009000c0c40f4601e00451828480c1d001102142c0501c0005c0500d21007580003540d81e480c40d0f146c05000946502c011061a0b002850840b840490318207240c000608990044051282c55030702c0c540b9400d060110500c50000102c0411070250f80e0f00c0076a80074403440b075024a100340c17006281852600310351491203088800c01424800d0040c0d0b03d00d01814a90030b501d1500c0c3d004048070f140e001c02d003408103d00054541c1c100e11450b02d40c40b011141c3c1c00c4103466907440f0a0f03840495000c0054001a54071a070031a0b0315070640904142c0f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 955919145 1250 955917895 955917929
    0xb01030e0c010207210804140301150602030a12020f0c0a030206130c0308180316081902131a0414060f01210c0c06060803030417090604090902030109020603010f 71
    0x240d0300e90740000c1c000c50050384414030030030032040500000c40c41c0306908415450001c42c1501c400c805548140c20050010800000c0851542030902c1210810864030f0072013420141032200c002e4491061081d04030401201d643c844030702240701e50440740c004c0c05c111045581c51440345541500e60301019015800b5018a00001d51703000e00b2811004259503104100c0d0043c1411a070740e0156070340082d600103544055003010240c1545003005000084901c100150341e00510f00613400f0714200500d1146a56a54030505800058641803440d80e90b45459800105150650700d82c41d98600d2400c0c0301a0382e22034141807a10001d4003102c3c8105000d90b00a6501ca0107050540340150761800450a48900071840c85410f100c2050f0a0740c00040e03c113890b0700e41a1007081281c0c54a10603540e06400500540d040041444100512101110921440c040c112401c0c4440080041d40e2802a442106080c46d00c2d4090003045540a520041304558020030b81516543c40c2c101209000c3d07240d00920300254200143d07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 955920395 1250 955919145 955919171
    0x30515063c060f0d11070c1e0f060e0f0409060f2a0c1401230702060f0601050a0c0501020417060105090711031911070308270d030309140a060b0103 65
    0x11a10002200740b9241c0c64060941200002000f07040322805c60b005041c0580e03c0090490313a01079000707109004000055400c4d0400c1d4141c0d1560552180c0180211818100a01d135007040c0301d60b884103000c03074132051500b4000c001300f0050800d1800c020701c1030b031030070240880c2c002c129409000e6000c4240d9071740f403152401e40807104025015014140120305103a030f0340000500c5140c50014804020713000881c10480e9001203401030785070b489450300484216010000d07036560421100d40e1014241c03a1544160500c000040c040303205840b600000c00c65103040c0039090081c00d4044400900030b5440c2035004049454845e07807200428050240300e00e0845001c0b400c024814200e5100d0403520380f014501e01001540340340c0c01c4c5405d404400052200694004a00c3e0800b4030034980218007440f511680d82c40740c0c92500c04610700380296244410002400c0980380d449400803d60f405074582000204071011b810000204000b0700d0754214284240000d080400c40c10781c00600d075200b801c1e03c040c4407503007403920 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 955921645 1250 955920395 955920397
    0x71409060607021c080c06061002010b2425030e0108150d0c03050d0c020306070903030c06020a1413080129100e0a03051509010501030515063c06 64
    0x5003941d00150070301029016103400b00e0181c603800c00d120b20400c121400d50741d07030740280d0b000031001c80c240d500f00200b044001c1c108605049101c60540c0300030090000c2c46400901141c00c440206c2082c1d021f0861024150b401010407210003590b000c00c42002543d0325000d43d40d400000c1741d02200040d40c2d050380c024a550241408c5405402c94003491422216080d081c003448100700c900603124041d0010000000c290140a60020b458256849240722042030050600d00400981080204030720b40108001007984185504641d1b540440c0c0035a82d20205601102d2555040b03c00f04141e08000440e102d00c1402d003e540822140308200a226040d01c054000704484004960a424540f42c4a603d00161514984140200c40207040c545420b0800001052020120390001c076551f070b0100c0c91503440064110686640410444001e02096066640315a21400c550144d06925491a8003041c0556181100c4400d181140c0405e82c0e0f129220044040602225240e0501c03075006869100c107550034208 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 955922895 1250 955921645 955921651
    0x30a080702030124030809031216050106060e0102191406010b040812040f030204021e04090b03120a020c0d1a0403050901030506030714060904061a0705191703041a09071409 76
    0x5040c3c04413502e140c0315a0091791207100210703810301890702c5850014041070040c09103000c4130b11920040c03c0c003e1821b107086079280e030441414030440c1d0324440d140ea0380c00140c0603105446540c141860649500d030003411716a008021600038007409002240160704540a841121070100480304050141c0701504a14441c80c01020f00e2440154010700140c2043c0d0000c0400c070b896440800c240414154890640d40c0060f001140401d4990080303070b02c245802c0000b41c0700540c201a150b49400c26140010399940d42c80380c10b040c0500070030305030003050000c1d4000300156044100411581450603180041075a4070109107140800e24100100303c0c14100002d081003135421400341c15030700c4040d001c204000303070300941c80e4554416242c94001c60b2282460710300c0d207910364120001c00e07180c8405180c040c1c2404207030f09129090961980825000c41d1640705501c8004003414401c0f5941e44550a1230703410305c2c0200c200c480c80b0300f09a50030300400d80700004940044030415412000001c9501c820401c03404025 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 955924145 1250 955922895 955922951
    0x51318050f1302010c20030d0e01021b0906091008010c0804120503040b070e0402040816030201230415140a0f02070f141e0d0614060a051804020f030a0807020301 71
    0x2a17030020303800428204074111181e508044481216001030300e000512031403400051404045005256010403840103101d1141207040700600441012419041000700791f41e100d000c1e8800801c440602c01c07003881003e8001c200003445002000078024022880550341203a5041e101b50041403591300c41d0302601d00465020321b50b404140c40d204002c0700d81c19031400038564030550822000403441000c000e1209004401c5a10406140c075500000d88440183d05880400301c03039090a03d6a11516007048409884800c000c410520060b03080440c1d841c150340003084007040000a90030440c40e000689040344510300c0d4201c071580c0340c0b50407003a00c0c0203180784240c0e0130705c0141a540000c0c9217451904612840705042e14804d0700404500060503500e59000d05590965840141c141c00301c424024079680000305440200c0020300d4400400c1000044049082458280001240842d030ba42241864220401001c0300d08034101410403a00e140c0c4a000704038800d40c17a18503076504441c1010752100c000c040c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 955925395 1250 955924145 955924157
    0xf0903030f04050f0f210403080d0905030706020f0d1b0203070b060d2306070311070f111e0f0906370603060510031506051318050f130201 61
    0xe046200d407500c400c0904201c03214003d802c001410460100b11200c6009803400041582e02da00b000d000010004502036807401e400100010f0010404546c11114020903884001600c040709007041d505500854030014032460001501040c02035030355020340001c02c0400420402c40d4100c640300d0f0340c48194030b2a0000541c0003032025034041100e50741003951101001d0003d0201103127680c4c2c1c003807864446c50000301503051504500c9407440f8040001035840001801d0800071004c2510b80a03085014070a802041010035403134510401c0101240c949402c94054a692800008031001c0c10801144d50000b60140b1450441c0c105145030903c0328138092400504200d54907240b4080d9442030031498803034041404040712441070040981281d00001705501d40e0001038040c24901000080c0490545041c2010300f800031f20700005031800310910444411741401c80da503c520481041d86c900b03895100c41210140144520115117944d0446482030041c1034504480381c0e910311820a4400c605038010b80090f007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 955926645 1250 955925395 955925401
    0x1206090515041502090f03010e070303020f0712060f02130305100c0513060f1b0f171c0e150f340e181609080c1f11100902090f090303 59
    0x2003c0d9000380502c240142c803000c0d03880e402e07401003801d6420403406031691f6072240c00104289941402140e48641d840d40181007420b1505801100301e0018110140c034090341c0380285902e0350560b074100d4541010104e16a00e2682c3e917070070000e458a5414250002d902d09144003c8517540c400d0084032020001a46480e02c0c0d00c1c20800c08880081c03010484d0000d10040100d43c1e429445c2c0c00c5401100140304003070f804d01c50486882c1201040c0303d40c10510180c03080501c0111550447c0c418111007000703000c500000d00880110000d46070071100920b03c00f6280904040c00f4402d40e90341506441031307480048590099040c100000400c5c60500100b000f0040960341190381c1921403440300c1d251880003080780b88a2054110303c280d20710016680d09070340410340c014011805070004103000041c41c944014040303031480035011400b07414107901c12815406615580e411003a000b0002801c0016030001128000451482d4540040103801c1303050f40700d0803000002444c0394a6081800707114a2408d4040e60450b1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 955927895 1250 955926645 955926683
    0xd0306091a01320f030a0b060f090d08161103070501052104151d1507020a23060f040c0b03190e1002031f0504050103030e12010204120609051504 64
    0x2240e8040d100c81c100480c000800d040c5607103e01402e181803a5541056032401d003000760008a0300b40494807402600180115400380380c80d4402c1d0384d8040019240005050b05501e4070388624400ca400550244003a11203c80c01d00858644c100a011000d41c12944500d44803070043d2114001c01202c100c040c400c40d407040340c419001401d0141c01910460300803824100e0607005205613800d00c444500b009403800c40d60105040e003003103d05402003410102c0d009504115000a480310400103000d0081c40c061000c5451900c1f502440c0100c00001074140c1c3c0403400c003403c01902c030003826a03060350b41082c0c0c1080481c402505504880c0242d480500c0300700c05510b00c241c85409031401d401d81d60a07501a11030401d256445500055206a1304d03626901142c501c110780320081c1c00e02070740143c2d02541c076100040c0006a00401f0310204600104ca04001101040078540c0c0640b0a1360424200109000c03484003c0042603007180c044544140243c810b214802074007600c4640c011100034041840e044082d0b1251 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 955929145 1250 955927895 955927937
    0x303040b070f11010f0207020306181207081209010506210601061d04050a0203011a040f030605130c061e02060f010b0c0304050613090518121b0d0306091a01 69
    0x30b00d40c81c1080e554505145840608481e40207642005007900041c91200b145028000c6691242c040c0b000c10703004101041116541b10b04140d01c550f8019400070352881844000015603880302001660f406043ca403c05c0e84501820055601034002c03403d00080641000144105e44a4040e034000200203e070319215040b1040034511011004000f62800400303025142c9024075032050120030030260341c03540741c00e50700c2d00c9910404480c0580f1160920081c02000001d484440443c6d4004101080c035488264564440000c1820014500303121b1440001c0c2458020301d10050798501da0000e0501c100302c6003416a2607000c2261601015101c500041c010001c458020700b04a00c41042141d040c0b0f0f4036031000c14031903402059510f00041071607400304401007003401029409445045450100d2040c1c0745120781d144545000150280008606003014035100c0c6540424180c0c030714200e030341b1a00d001e68003030010071050140305540350a2440f402085827007110b94403860501a511080c401c1c00d801e0300b0140f0307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 955930395 1250 955929145 955929167
    0x90302010c1b06151212021204031a0a02040527060a0e19061d01030c14180615180f0102010e0c120c2d09060d060f0905032101080303040b07 62
    0x2d9042d040203e40c5c0b4004480540c50548100d0280b001d40001d42000f03403a000741043c02d1910701401b04414800a54115490f45994001d05502495529142407010190249402c07168101a440001a21050000d0304591030101e290502c5440391320780000344105ca03202c5000b08400b0b250090040f918041890340b145062034204040022081d0315440240d031a800040d1181c942101213000510510040b946144024514651072503842a1114007003080f80d03100100149205102d14005a210348560b900c1c0c904a46000424658460b41d401a50b100d04074900c0486010b100d6004880c11554014441c0e40443c0038840300505045010740100680380001d0000702ca814052007504400340d84030041000c0c9011140641303482e12014102e8918411109512034600c02d1214505100c10303a04c51707442101c0d810350440700c04104044030641220150111140c000c02e907102c00036040355014407c40540031032810209030800183d0362040ca0642e41e010517a00984008a00404201c629000b5685409 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 955931645 1250 955930395 955930421
    0x180102010f0606090e09161205070f061d0a03020306060d02040209102303010605190509030d05030a0b0301020304051b030f0303011509050603040f02010e0a030b0901090302010c1b06 80
    0x11207040c9000d8500581e0000c0e40a400496820501484042c94205159078003800a000402d08000d850501c1d00040c0d43d1403046a0510070b01021000602c60240609406441141610040d00c0d5465100038800c180c1f00340900d44002d0309601135036052a0850254080304c1d0014018407c9480704010420310403031344607003242e2255080042603040d40703071000000d00c82d40e0325850700c00c1c00c644221b201003000d4104a8040c0200700c0200014031446403c04190b6000484002c81030100700b0f10f800c0705031483e00c5148070055040c802c50a0f54501158001c008502c6144102400d10401120101b403509034041500d00406a070040485480d40c603044130001e00c07298038000c0884481c20403d03102d2030b05550081c0c1100c0b44004a408601441680107034006000700307000d9520a02d14a8251900703c03007444002c00013410041426a511903540d596620100503580150884899050002a460080600d400c0440c095401e250b41d040c4030900400302c420b1501c83d5880c2d0358015080d43d9498070020038401030404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 955932895 1250 955931645 955931651
    0x1a0d0c020d031b02060a050604020d090c140d0c030b0a0204170a020a080a03020307060b0a030b0a0b040b270417040f080c010212070b191b11060702100209031002131a0f18010201 78
    0x4001b40b1203030080c454000d018a137200f9450f4200361000000d2103055510a00a00111540500280400b0301080440360070180c00d00031916100700300700c040e1045a000890300c603c414003045000303201150040c0c1c224422101d00781020340d01c4030490740f02d038004075004c0c000d0b802c00d00111000c501241c100940d03d100c018184e6844503281e40c0c4100e060441580d8107003045540301c508080c1424207202e0200c0c1040c3c01c894000b440b0040c01504101c500c21140345203039403045007000c101085403081100c080f140c000f0115030b07191600c4200e03585a4070300030320030980035215030300d8440301a50000c5a4000e500700010149443c01c19070303494001551001411520b0701400d000209000c000c06482003d00f804103c0b20b90403001440660000c102c00c43e4078001c01001d030403070340911188035000100000640030002e0301580314002840040e05000c407440d200e03c40c0d03c0c000103080032041500b4040c1c5058441401c886501c822003c5108101c5020302c502c0903510000c200036846d00030300c0c8084048000f000500c004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 955934145 1250 955932895 955932907
    0x10f021b0f03010209030f0a030e031902120c1e090f010b0921010204060509040c020607121802030304080d1b030210020c1f05090f0a0c1a0d0c020d031b02060a05060402 74
    0x200b8038054800c0c141c2c03d03254000d21281230030150300a11140c0c09030401c60091662a41c8110440f064415502c0024412401e9414505000b403043c8800742419400030303c1e481944440743c0c07020355007080c9403803014495400c0c0400140364074030008005050380c01b418181d90400d8040340a1055480c08a40074080d01d841400a41a40e00400d000130000340a540e5101a22500340005005c2034038a00d0100000b1364004038104400e256002101411000e00220003045114407030f2242d0700c50030301064010790507000006021442a400040c841500801551000c200510720340e40c0c0b034003c5111030801001a001034a02c00c030094500d401501130005d060059482c0c030303400d0b0a5800c0c3c03019175030202c031a41c20781c480081101159040c030100189903040c1307000d48410404d9030ba5545580d68a40188400006502c6120000d079810b2000d64070780d1041390904028050415501035a07541940c0407840000342000c8007010100080b915000c0703010b60b581c000344119200c41c602c18024103001460716800560034801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 955935251 1106 955934145 955934149
    0xc030c290c06060913060f0c080121030c0c0510020c040e010b06030c07081903020426210d061d0c0903030d02030601030227010f021b0f03010209 64
    0x30030004d595484000740b801145c0c80d00041d04242c6081582110440d0603070060440070300d00d03100c650051783e84e9161204084142046141100c1c0f81c4054040024010040b40b00250f101b01810b07202c9603280c60108240e0070182c4a40b01c01130380804040121814948240010703504900d00034015001640e000c0341e81840040c01851524400140314020700a003a401d42c0e0220035210994070a14071100801400381d0400c1c018410120040100741083c44007d0f400d0018070b06200c0d0103880c4881001d280070313041003003e0502540500c0c003003104030002c00042c861040074180c01c0722400040f41c1116981d480f20300f002800401d070b40000300b00c4800740e994004152496072184510142e80c1e5541c0030b00490290041c40c1c4450032403400052003002e151509072110f802d5143c21f980300c00c4400e5014400300c1c0d980c414a20a550940076807410000141040505030314508000340c0098600307880c200c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 955755395 955935251 := by
  have h0 := BRFrame.cov_init 955755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 955755395 ≤ n) (h2 : n < 955935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
