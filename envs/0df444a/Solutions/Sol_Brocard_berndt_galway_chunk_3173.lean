-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3173
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:52:46.798852+00:00
-- url     : https://prove2.me/submissions/68ddc491-825e-491f-9abd-e6a60ccb2e45

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 570503597 ≤ n < 570683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 570504847 1250 570503597 570503603
    0x504050103050c0910050c0c0315151203120618040507030219060804022b0809040f020c0c0f060408010c030225020105070807051e03180103020c030702040e1e0f06010909 75
    0x11000170f00b52001a00c151b4840809602180615011054240d45c28043d03000c0608480248003014902440d00110040717440c503555105844071003a50207980c0c000400d64002c101412500f0000d625001c00140d02040300e9180300305007900c072004010811002281d070204076072003620703840411100c200074010445400d0041c5e20009a035000041c000d0324001040d40700514050066640001e06a00c0401608425117410340e1040800600040300d070910340f25110720400140030450034032009003402d07030720b0341c00c2c204046120700d03916204980c1c103a4404049400030514400200320703c0403c030070060040c0d00081c04031401c010320f03524495055116910f00c4001d09a0583d1800d2902d02140c2e10861190071828041d10b0b50b208550010700c1c80c42551b400441a0320700745008644544009500710140000114002d0400d030041c000301d4070008002040c0ca00c15507040350b01040c17407011040b60501c3c00c0080c80340403102d508594480040024040b42d498403d40d80705090385c0c4240c1c1c8607501076041e101d0450b001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 570506097 1250 570504847 570504859
    0x2070b180409021503040b090d0206010f050d05010608060a150e0705220e0711010e0f0319021011130905190f140f1f0503060a0c020f07060504050103050c09 69
    0x10300091030a40d1203a02d48901c010700901d0102d904814100e40798204031403c50710515803070103215010a08000302e69068509100a207a01d604002503031000450a11586001c1c9141545e050208003080d044207020340494811900b42c1c0c034013080d001028202c4031154407501004078002090180d51540c40307501c16403268840c645040000421841041c1c072114403504083d01004000c40c0110030540804c1c007803030340c40c2e94007216000c00144460840346a01c1c05410140d0046070f500b9485007010090301d03c407071003040c1000403000c0d01d41d05c16400c050740c0070700ca01d00f0980b03012950b902006044001d01000542d078105000e90039129178162044a105444646064110780d00090024076180c111512070500c001d004111421151080311213081300342c40d4441210192410030004455940c4510482214007071148209807401010070b8455001814000c246030310303021002002c42c0200100c680c014403e20490342002e684030802001a002802103e00190400c03001c02c483c1ea00031015100010001040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 570507347 1250 570506097 570506137
    0x1106040c05100c1a09070e0423150708060d1a07080f010b0304120c1209092910090e070809060109020304030e0103050a110409061412030a1b12020d02070b 68
    0x14811300c0b0040101034040c148103130007000c0740c0c03400c0d46d08446010700d1060404280e00d022100c0b41d04e47d0482801002c8620ba48030a00003080c0c160803c850315008240360070141e000d83c803444041002c06021240c040c20354910104404900c08038210090f21800880d40e414042d0f490780d407070b400e011110078801e400c1500001d0001c231340414a92407246112a040d400c00c8104105199505c045042e9168044404070300d039000100030b0356115000c2c21410b5080080300324020000000041c1c20a481e5070511801101c0401d005482d1074001c0c0030641c00f41024040e01d01443c948543c0084c4901c60844000c0d01c0c038004c0d0310000840d151a03000b80c0340100c5e49600ca02120038201001100100300080ca100c00003921032995004142032400180b000e81030700c182c040b81440c105100e00c0c4040980503440b43c0500d003070310f031880d26441e004016208080203611b0444000781e9031035602002003000c103002400984501010b0b0f9952a00050f46661000654007030350380040ea80c3c0040749140c018820100b01c50504031302 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 570508597 1250 570507347 570507383
    0x50303070f121b084b03060109060c0807050106080f0c1512040c1a07060e060c0702060d2003180a03081f0306090302010c0216050612071106040c05100c 67
    0x5000c202000c5c001e07120f900c0511807107580010002400e2555400030803c81171090550f0300b40c1c101010340307036a1803440c61801c201c40000c1400c41d0328400c060412080848207010001c4500441d80f80c40d0b0014028000b840e01e4605403611828101402591446941c3c0c0600c3c40c2d091141d04225661046101141400c01002d5034540700400180111020112604041052103030b803030f881000c1e0050b4244064940006103460000c84020b8402e42040d0343c044000c0008100342e003000c44030780b00e50541d042d40c0c032044403803c010040c1c10550000c82010b4020441800c001c50040d000d98070a000b0301d56440c1007400074651494032072080c03550140020304208001030712110641034401e0040d41e14801c00c04100d80c2d80c0c03076a1040318484282240140d440c1c030306004456030b04000e41c0c0c1c0740402c000e0580800c40e1801c80024880d100b40c0003141c0c042d21000001544a9006040c01d0140c20b00e00e4040d203516103001d25110413606414041c00b84600680301c4650304e254031404103d070078154407040c0c200c482c040100e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 570509847 1250 570508597 570508613
    0x1e060f010e040902030105090d0201060b030c16030908010c12050106051804200f120c030112060b04180b01030506160503040f08092d040905030a031104050303070f121b 74
    0x40c0e1a03402c540c4816403800183c90910a29204001c848090513509083c60360090030345115078000103810405005106241a400c0c0845a007682c001411030105601450152510f0b40d40c0d500880c3c0952a14001010003600319075000c020448001081007640c3e05e420040d41c050081d51224a25907600340e04040441c00c06034007041038002c4800245000b1f2108212403a82039202c401c048024500c00301c0d4880b1030301802000c0582194941040904560409071306d034070200c1d030000d80509541d442e4200c0712055201c551007200c070160010310800f1001d940c0c3c01d2801d1040d500f80301c101c60724070a0900107505c0c0e01c1d058201c809581e0740c1e5940d0900d036480700d454551449856000c01c2c0c50b144010000c1754102e0740e451401a5070740703064103c00d01900310100110320010441e00d008900030740c10312034641300203000402101c0110035a814000f0303400010f04511101ca0090342c11494041c840081c0560901490480d806445c6108402d0007508840e100341c100c402d06000c0e0788192400d10100320b408005849a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 570511097 1250 570509847 570509867
    0x60a0c020c151804151701200a0c08040909080c060c030c1206031212040b0c0a0507150b03010c030e120705030a05070f020a1203110706020319050708030c031e060f01 73
    0x41c004548903122128040183c0f0280e8400f8103088110b01b490582c1c80801c0c002d091a108104001940040d01e042040d50382d445040114000c200b203680d100c104000302c4100392000360031490000c01010700c007031401110360750150300b04400620443c00005d0050100c601100d221341f00102c2014103250f40310042c541022805001507a160103031a280d510b05105403006031807000f59620300d8181c00d04190030000000440076007600c04003001000703481c00e0a03402000321145242d1040002004d41c00106034103000f8454518681e500d5400c01c0c001c805c107a80d01d0b0700216180d0300098260303035685c04896205041ca108000e00280143c00600081e484607001d00054030246000d0040f524580d5003039400100358140d42d0f00030703e241c005034440200c103040c0d014a01144840d44103000740b81c07a60422802a42d6070107a210300940304a41c502030721000038450320544501640c40040d00c2e0300c90406074208107081d0011180800703a0000004d140049007030325002c1c00d001c0c60000e0b02c1075080d02215001100c405c080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 570512347 1250 570511097 570511099
    0x60506040b071103100501051005190c020f09040501051503061308090105040f030f151a0915041b0f1403041e02060304050601090c02030a021c11060a0c020c1518 71
    0x4006003d80c154600380301584c0386078000c00d000a034941c180b908104106206042c1da4040040c14071101c02c0803c00110321a0096a450a1182140d0820320019400c01c1c9102e4060390070505001c180300810005400841c05106030f0b400c0f006d01c20140005059541c20200c40940840246051030130101d8002c0703009100180d07043c0350262071700352185408808225150300c1123400c050402016400e01054800c031045891900806128444d0024210130420741408c2d02a40300e02e4602020800c0c0c0d8121031801c2d18030100181090104209010020100090018004000c101c1d69200c0840300c5224003405100310070798400c840e0075920b9079143e00741b20b6040201658055002c40d00f540000da9290b5010354410391160004196640c14003100005a411120079402594410b00070408800e4011550030f0341d511203172444250f01d80a0400c22910070420b00b07040c200d180500824004802840d800103120482d85400301c511011a010070b21800314803d0701070140a01080c8844495120b5801030804c00c070f24 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 570513597 1250 570512347 570512363
    0x314060405040314040b070b0c04062007081005090105070206010609150306050411090a060e03100216020405010623120106050903010618090b0105040207030c2306100810060506040b07 81
    0x203040c00c04c00c1e044c2d407041d000315000240101d28082040008505598020015a0501c0c1801c0c904180030704038048519003622540e002c80003203040d1601c20001c00008041c3c4c40116040f00406516090042009a4191a1550801c0001003006000141745070488800e0745d01c1d1125146040c40325007101d2814650032003095154a07002030150f0f110b00403007174a41d00713548100d590343d02da4508200300c45480f40d200700f0a00c05001c2c0440c000b95800300382e40600b403802980141e90b501a04451103010803030b0040080d4040e2402c000401c00c1c0f40c0c048081c003c10a0340041c840d5034180c2d481045000b900984804204142410b0014030001e4070480c050302c0155005800400c1560315a200c0100f01c0e221911000040c3d0780c2d41110720107000c01d6034005801031a0075a411490403420303443c014286c01c1c001d81c1c09041a4600310036640c44103820490445040c64041c142c40c040d06201a0803510b210441c803c0954030b120380040240710200b03d21900e011580002d01203490a840c20b60482803035008540c055071025 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 570514847 1250 570513597 570513617
    0x9051c0c080c191a060405090d0c0f0807080408151005010e010e100807021006050d020607140a0f03111902090a0e0f0106051206010f0501050706090221010b0103140604050403 77
    0x402101c0556031042c4513000d000031040c19032400d180c3d01c0c00300903c000d00c01c034144801e2050380c0300d000c00e0003036403000c8600d01094032100a0600380030102d01140011b0003110009800d005004885d805001139800c04019210f00c2070001041100340f04081d961001181d907a003404000304c2d80503045100450354181000e05264151030b0004190b07071207050a80c0b02081c20101082003940d41404169402100a1000c0220070b00304400725511206005000b0b00891000416000b031140d06041d8060b0041c2e0035085880d10415450f00400021918000300d01203070300e0040c9040c4c407180118100920b0220700070138400c00005502004210300c4058224a00700d540c4040d6814604010301102080003070711400403d000e403402043c400c0d171080c01a5224016040600107104140d24040d140045600c00d2a00035156070b01d600f404001030480003402076028014003144100c4a401110303203040450044020402200001c0c019400d44001700741103070b041100b000003e5100d01c1e1642c0710541081c007070b1401504003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 570516097 1250 570514847 570514873
    0x9090504111c0209010506040f0b0c120f041d01081b060c0712020a09050408031501021009030e0a0824090a021002100c18090b0301150909051c0c080c 66
    0x3030768840c104182c07540c40c0451410154107058410a004003401e40e4000d1070903250031010b140b007900d41e0090406034600081c00a031018000c1200310020242d05001c1a5111820200e254461b03102d407045480c0c881030351240000420004803c0d604035200ca40181a003070031102504414016200030055002d4024011811450000c002d43c0300544010440c82c0404480e40c0104210100d15921030f070041c41c249003c220008248509894019484001c0001c2e08103903400140d06080304215620038171848c1c0134013034041c1a8407540715007024805581d00d225080d00c4096041d11007055000250041020361121030300d0420a07803140f5800f20102c02a9540d51400780e0010364880400240480141c1c420b840d48800e8403800d00c181c800720500c07410107004000070000700101440e401d06c10b44002e5661354a8060080e1820b4005410152010441b4095192514500c40040c506428165030034840c075050450308034442c098104101c295030b01d45140031a03603969002020b03405003558150305d005218101c401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 570517347 1250 570516097 570516109
    0x40c1e09020f0c070b0c0d0c080405090a140a06050102070605090d05010c11060c03040b04022205070908010e010b09040b04021813120f0c080d0b03030711010801150909050411 77
    0x300d40400d452031560f4003075842c0d0051514495801440c1d0a4404000c07401e0b5108001491044030700c09803c1070382c10080c3c0c1c0d041410690045522468000c0c4641d010045a1042903005420a2905412003102c80d11003520940840e400c9004007030160f440040d0034050700c1c0c050b101505040c0c50061540c02c480d07103e40e80c0c0b54255a07020342d140011400b0740c406d02c0a0b1131f0050000030740c08072100101900750300e05a203846510b0440a00064040c1d4040100c0c510725210b2050b00d002d42c880e1201062010b400c242c40000e04040080c400d00303030b0355480e100c405800d952042c01504424000108000e20135140c41d2a141510790b4060402c9030f000c5070502181c03409411002c03503107100c0e4100d0010038584800c0785c20410030750000d085ca600100448011906d012540000043c116950441d180a07164066040004000c0042203005030b4184808500c6104008403450039002066082e0b1750808983d030f0354011000c0d8034182030490030201b0903590050000b03500035801554490702603801410028140e40100305 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 570518597 1250 570517347 570517357
    0x5280602041707270b1203070b0106021606021002030702031204351204030306051e10080601050417070302090708040b1b072a1509060503040c1e0902 66
    0x30415000780d205a9102c803050100c0300040071081c036044500a84800c0019000786280200004541d81d40c41400d42a198199078807040196882100d50b1368030a41000004140f0134400c800040c800c980e1a500c1c0c1082d0109290102d0f9a00e800a1200e07400c1d86810703101a410042502d41184002d001c91441d00020326516400b0354042c9040b480e080319000644080c045075095414030343c0c8082040c540c1d000141e101107a042a00c032002c9a02152694070b400c602a140c40d034445644410101c0c501c4413805085012212280c80c02c61b4880d41c40c1042c083c1c00c1d139000e079080307406a0105500380010850421002600404924a0800c0ea030101e0307201d9000030782d8140700303841c0d610000380800104410090090702c990340260020130002c405548000c8920840e1090400043c0124400c526548480e020381c40700040c90210842990011030311400a07003040c41d00d14400e01c00007500708600258050180c0c0480340032741d0f044a07880102c103040c0341d603416100f000c001441c00c50081c40000000d0002d12440a80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 570519847 1250 570518597 570518609
    0xc03070608100b0a05040905060406090516030b0319030c05010e03030a0204150c0507090216050303010902030906150d03080c09030f070501030b1804022218060e03070528060204 78
    0x1003840c103100c81004000d96040d04501030b00399007001341d520040d8100007038178101c03007075540701140a90b45e510105019000307a901c0980c00504080500c070780210700707043c9a1802d1009907800c100043c829010541e66400c140c202c0c010810400e01c1d02d40221344541d00c41d5036098010b1001041c511040300c030042c515402103503030401d1180d001c134003403000c06020300760900901072505e400c402e06101901ea50f13071204c1039481481c05d030580c00144101c3c0e850303490790320149840e007040c1520380325a03441e19500c0180d403040314000102e0154a00180703501c051088038841c040c6c4090000d9001400a0707070141c0743c81501410b5042c0452060000c8140c903502041540003498040028002141c54400050140d4020009461107203100c000d0b6076424000300003509a002c1e404503640007001908024040f01030150780405180c05080a0940c00c405403a11212a02c10740b2450040126140f04081141c0f02c2c055208000c02c190040d42c058034000f0389016040c0c10581c8640301c22404810107a0f2034900f00e80c0164820 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 570521097 1250 570519847 570519857
    0x30f010b0a140316090923070c08040f06090503030703020c0f01031d100c05090d11120d17010e0408030a05150d14010e0708100905071215060b0a09170c030706 70
    0x6801c15644c40600305c00103100404007845400001545040d40014000d1491104013406000030350742c5106201d00f0040c260491407295407207454000015040d6440d00a400c0071a003c164002001d040000881d040c00350564083c08119588504000c10400d00d628118101600c6042d60094000001074034465502003400810001c0341c0103140d002511b41110003081446014000f040c543e0f1603000251302c070654498224000310329600e0010740e844032411000c6085100702004280000d0300044849414460b0600a403266070381d5204400b907150040320300510b5841c0074000b00b54000c043d034120300e400c9080722444c803003080c011a000c54a0f00198450075180e41c8504a014a0102d80031300c148106030211901901c3e5450600789103d5485250304500c1e4211543c440c0c0c10014040c0c140820030290019111801c0c8072611030602d008070720403400790850010700d0007100252a0076114110f58110541e91940100c0c540381c00400d2091031440030682c1c046029902000342c0300e41e002e00c0908003402050b219 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 570522347 1250 570521097 570521131
    0x90105090c0306070905120115060906030e0309060f09030f030a020d0909060b030c0304050709050a060914190f09080712020f060603060c0a02010902120c15030f010b0a1403 76
    0xc245091450144107010f41c204400b404829640000444242c1d1803d5a004080b4924249110b0040c40704d41000340003002c045030003103403041e0b228040b14202c440c140d034240108100702d040c9640b02c0c23080c400150342c801c00c10400841469140b0000d400b0410005094540070820341c0715481c11035104030240700058000040b02001903800800e540042c049002c8104001e904062a0301120300c0090030741114080040300184c01c1050400c400406050306000034400c5050855007040982a00c0c02030100c42ca04000403006040c0310701c2d11841c03181c0c6146810168040c4441c22920041107001103c10015403200b4200021a0003040108101ca100320781040100d94400030003820b100e480000002d0b140c0056003400455074000400c96046000c6d201050398030707242071100f6401400c030b25030b0094201c542860b820403010f502088001e20840140e68443e1900301001c1012a544070407500b0040c01c2a03190010b21206c03c00c3e0025012707d03d09424146029545003860744810340049440e00510380e14400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 570523597 1250 570522347 570522361
    0x30609060e0f04030309051903170702010c080c0a02031e0301030605010b030405030f03102606060d0201120c1403010308040602010f110714030405042a0906020a030806060d05090105 80
    0x110300c20040901501000c102d04055070400040b2502900183c1003540307a480000c01c1c06401d02c42030801c010318000c1f00310f52458030710f400361410b80a036031101031b40c00d01800001d4055006001f07082c0c03466019911442959918441c41d041c9030008550350b000c5200c184140c4207036400240c0c0c5210500c20044507940c9941c914a04281528416000901900c4c02031052100240c80001550000c0b00c2d10561644ca95480189450504109a01c80826004115011014090892580300640e01c940055590b03070341d60f001c280401c0351001c2c580280000c01c1e61b182902000e036181c0c0281882c010f503252400035001880000081600280c00969460200040800c41180c0900c116189596190028030203202c0c0e59421940741e018812003c0c06400407440e01c851460800c0c401c440260800400402c9002440402c441c1d5030903d0298030080d15070010007020015000305181002c503805039006161029043e0317404c40da600c03009440641c002200b88402141c0c2182c90040c50301c07922080c2c1c00000c403498803203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 570524847 1250 570523597 570523601
    0x2100c020a0c081906091b030305180f01090b07060e0a03090603060e1506180301290a0305060c0c07050a090f0506041401050d051e011b03020414010818010903030609 73
    0x107488101a41c4c015001020840100f00c04407040e5a0001e0300000c0b80c89130350034010504041070b089070b501001380510104c101900880602525144003a00415290009081c001c0c0c120041c00700394046070341c18000300803003103010004041c032a11811021416004c44184c40380341c007048880446c0441c1680c902800010fa26214000c000c0140010b0000d9500303140c002c040304007404200d618000d200001d041e0b142c03a407a46503041049003010300204147e4490305201e106441040e002411800a00c282442084c40e00600c0392041c5d94011001d009103485409004801d0303445403410790040d00986030000340c10341e80c15207002d0080100d0000410b0035000354011404a0701c0003854203204a281900162441a0800d0b00c40d040d6901500c1c00b50005100c0e00700b01380342ca00b469414007802c0b118100d031842d1803803041d084904107102c102c100303600300c4681c40000e81c164061ba0140c05900d00c005161413038258840c50b01c0a80005440c44040c0304d000610f000c15080da80c0f01102a00030a480780010030030f0032102c3c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 570526097 1250 570524847 570524849
    0x40e0604170f0403080a0c022e030204080d05091503070503040b060621091213030b010509070507020d0206040302041a130c02060c07080909011403010c0302030108061602100c020a0c 80
    0x1c07500311480c10200d8241182940901d0001818154000c02c06540050242200401c6281c0050845040c080b4000c42123900ca005841aa10300c858130f01c50031200c0307500a00946041c0c90059014104c48081d0030011101b54010f500380a6014050140c0e098561500d280150302940ea9503071050750701c0c134040c100620a20405407035a0b00450742040751f0340e6004441907140d4100c3c3d6844030050781c1511101d901c40e00c0c0c145008285c1481c150f000403501d00e036442641e04a0704581c03103502c3c400b0150b0390760b000300203203070008450210104400b004200014500340c50308030002440200346c1828541c685c0c000c00d040740d000c0c803a2100d5031304103400e100300d030b5107485220005803844d00304042c084101c100c04002d4440340060003950b040310000c0b0309502005522001e0740c1000744041d00e201c4056a41e00303d0303241d0548444803914080d5207047c040b192614402c1c02160f06a406200040c4000e480b10312b40c112000c1c02c0900520b046001308103a0b1000c8554038040d010003088990b0060801c00000c0c1841403600100d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 570527347 1250 570526097 570526133
    0x2090112020d0201080907080d020106080111041802030a23060a0e0702030f2805072f0f041104060306030b0f1005010807050706150e09010c0801150e040e0604 70
    0x294820380001a074445040420300c2d64203182041080d180d24007101d1801b071260308208598010b1100d0b0b140015415400a000c4030a020000d00c0303040020b2051700c000b4412030040403050311901120a80054181d0011904082c0300440017400d07080c4464202040c1c21591006202c0000450900c0203624003500c400003e00000008641c0c542040000070350340e07200328180c0600c1b088002c42c0b80c0c2c0b11181501c41c1c00d4450061800c4201901e07070742220080040e8000b10049880a1400d500380c40c481c40c0081c5501025071401c00a41c040b034500300c0811401d9200f01c15841e61203500d54030740b91444594000640300400c3e0f10b440c0880d5007400c620f4412903d6400414603c1000c01d00003c00c02c15a024011030303c221442030810041c140c0324002d0442d00780c1f20700207029015908010303900e000390a9110302a000c480c01f21108030b035107440d007064a40c00c0e0340c001c440c3c220008043c88018886294041c809408a20442c1400841038640c1d001040c02e6919000c0c40c020345401040c10402031100c17560503660f84c801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 570528597 1250 570527347 570527369
    0x80105100f210908040303030203041a1308030606160b06040f0b0a170703120509090c1905030712050103060515190b0d022505011a01080f060414090a020901 69
    0x114850020800c08181c061009210300340000d90001c0300b80c81d4440000541c100078040c0e030343d40d102c0c20064044d61007035400701c640e00d0b04030221841030040c0111407801811160f400d080da0384265200c40c812908041c1c400c1e64403907010027400180310307100e46103c000c0038440c9048135614034200080000302e0f0040c01041541904210042c18940d0b1621f00e00002c0d520f00f8040050b560301801041407030141d02d608020314403070300d1f600707891007640c0c003d0080d1161000448040c44160b0790500d600403103004203040e510002a040f5201032050380034502642d4030140610701056200c0048a991003558000e030320954559541c3c0060001c511014408103d4041080e01d006a54144072038041003200800d2094070626403011645c131107600c503140c04507504400303506400d0841c9000c4015410301010a07041c03c40d036640c60070f5800b502000a100015104980585400c501980d800a0042c1e00c558011316696010381c1d242c040070000c031042d0b100075000e68105801481a4240d82c07040c00030400c01a084a4540c817 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 570529847 1250 570528597 570528617
    0x7080f0327120f0d180312050c0412241a24040b0702040207060912020d11070e0c0705060c0310120c4a10140111030903070608010510 59
    0x7502c2011200c00c1a60b2801c41030b618020402c40c0c0c2c00610401c0031200703054205802520502d070b480100c125040880250401280e16100c82c2c2d000c0314400ca224905115aa5041c07460102e6840032402c071408a0b1001c2d2000030b83c40e03c90b0000c00711101c85007082d04207110601140f220782408140850414202112220114081c03000d455040c082c40c410491281e1000404900b1074481e901900c400f154401414440c010399403070304110940d4405101d0700144504482ea030001d0340710300801180d030354041c00a403002909100740c10841c2d1000808040e45031000704070070710014074100400703442278030058892034490414068140c441020350384694a418078000e81b09002c40c0c0d40c403011101b00e070303a036120300a2103504030405143c41228400030034544921204900070041e00001380030303403141007416101c00656100c080a82c091000c41c02201140301c1c103c1c42e2541c8650042076160302d0015282c0859060440030300002c2d14003600368104800007a0400010051410090450180680c49081c400466 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 570531097 1250 570529847 570529873
    0x23030705160f180b1c0201020613081806040b07032f070e04140a0c080d030e0c3c01120903020c011202040b1603110706020a0807080f0327 61
    0x1c1c1d4280e00400103405426030822141080316840071a002d540545481700f0303454610840070303800c14280b00c1603016010b86c8000401d1150307848150040660700031032017410101c40f140c449080041c0003503502d4005a00b0800419950400b2000d008070361b1081d5545103038079001c48001160704403081300d0070b002c134907003102e041d41c00b500040b48040c2500d151683c0b40125039a54107000f080c091552903c04040e004588554062068803010740e010368100394111754041070b100000300d086804000202e883c54001c1845020311346415059030303281c02071654144150404180c41181c84401c003141d06081120a0048141c1c6560400041c01d03029420b03d000f0064a2150740340a5142d811030b905c12410403482c00d6550002b402d1316416600a000310311811030f107401541d000d29404241200e4194085405591040c012600c001458000d032426035010b8240e00d8403e60307520b800c603003102c2d0080380c8002e4103008a03a8102c016202440c451401c840d00c2001b807451307442d510300d40542d240c2c60042c40c50300711b10542c9001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 570532347 1250 570531097 570531119
    0x80907060806010e1201050105040c0c02060412020f031506240d0c2c150f120901060504090510050108060c09010e0402120f0118091e2303070516 64
    0x4480c0642811801a40c4120041300c9480e00c181c009540244001d41c1303a075040d141548024181d90742500c04012a554441e800c1d201d40844040c029031240c0f0800051250b40c10a0f940c0250713051010701b812850b9031401000a0410281e018850411140f400030401d4502e0620048003000103000003004480034010b004480b18880e414018041e1601c9049112641c1e00c5901e5810082c8150400d03410503840a00070f540c007000c0c0c0151498480c2d4003d8580760b4200200200721451088114031151409070400441c0450420080c0344010135569140b0009242d00c0c2d270b001d5460003e2191000d080d100100114032001c544040c3c200c0301d100d5002100f080b2201c00d400c011526061000d09140c00340142100009020b407040f0f00b440b1071000d400c0303414000e040c81008000da05848414010150f00381341e100240044840b4581c0203004c0007012009100b8043d21024100f1004d0300540d1803042c01100c010380e0f90300306a008000200650700000c4e0741c0c0700b03200003030101c41d058904d401c14100c0043d203024100c0d94 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 570533597 1250 570532347 570532349
    0x2107031b020d060b03101b080c0f0405150d0c110d09030c0b0f070c0b03090d0c0b04060921020606010201060f03150c02030c0703050c0a0504091a0615120402030706080907 75
    0x21031344c891078554550340400c100d00804141d1a000d00035505060340c405203203007005640d40301051019022a020ba82485c0940d44240c070325040080c02c080c6040c04220100340c001c0380312440c000c0100060480c1418901078034104002c43d44a4030000c0d0354462030945040c2c01002d065041114032001070000400202c0408100c0f029030103c1919896000110306480c42a5980201202103864000805d801142c01540c8107800074002d907050310002c402c0903075104a007914014a400c0c5540d00240004038036030f004050703040c010340c4243c0344a0103002e0600c4009007000e01500250b40704804101c09980d090040c00c02038031034000803082040c510341d28240d2000941386850340e010b07100c000040d000da20800030307102c54151060031203000c1981c03414090345803509408000e01400740034002040d2400c05000302200c144d4400d00504155100080762010a031003d00b44030780c8100d8040e410300d8100610303009001d00c0c41d421800c403411400d189c8105850048070381d00050500040200b0082441c1021480c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 570534847 1250 570533597 570533603
    0x60806150903010b190816060905090c04080a0b0406150503151807150815030d110304050a030c08010506010e0108071d060a050706060e06030d03020c2107031b020d 72
    0x584800a020002e405031a1302c03100310303170002c101c01410013a0751200040501101d4804003a103006e465981052100f00119014150101c1c02c00312040026040c0203001c59402003034071011a04240d1950b01850034090000e45c203032881a00c90050001f4001c0c0c512a82440801c100600c035803142c03414012035290380069111400344d5a50707000244200c4032000c1d02c0b10600b11200306581c212900d682490191800c1c800d0300c0000108040c0c0001c0701e0620900020f400303810014014445040711000445a00c40b035000d106009010500000035141c84010041c800303148030301d860031001410f11070b0003821a50010803490403c03241e0301e450185030760040740d001d800c86914541100e8802038004400c0c00c03031284501403a081400007032005401130b405005000c65034800d107010f01c803584d501e111035101d040d02541c1032641501305500d00b40d01c45020380e004110b07a00c00c15080d1052546a40b4006000c3c4003043c2d0031042444c0001140410141e002216003240494008450040e40461f0041010021010402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 570536097 1250 570534847 570534889
    0xc020706120f0c050304060b0604050a030f06060312090515030402010c0f11030d0e0102010e07050a150e030a060207030f05040605030117150709050109061103030a20041e060806 78
    0x3450001007180c2110202d1140900b05106952480000034803a6100700d40170f6902614090003001e241ca030405c1280c0c111407009280300007003803c5403581c89050b0303c51901250b60580c0c9640000004064100010440c030481c1ca41d07000321468002400000c080c1e6405c0190500020020400140e801002d00a06290000c11000c0c0e88110b07464584041541323101d109506d40b00c1e00c0d00c1d007040340da4042d0749107400200c207074020302004600c1c210b0781d659200785001d440d6016034050740c1488206000b00c60602d420000d498007100004e01200401d0500a00703c1083d18480e40024500c41410707004100c502c11752000d07182007442c1a1401c44010210300041c000d0420312038245041c1d10b185c4404000d210000c80ca4841c1c1c08001782040100a40103049500c20b45010a84200d40099000d005403940800c4080d010080d6107540d581c449004005d1000008a02d0700740c901407404003000d00314801410207803614540d104111601040781180c0c00d1200e80c402002c21031a0f0040001a440e1400116001096213540e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 570537347 1250 570536097 570536117
    0x608070b090111010f0f06050303030601020d0518041a01081e01060c111801050a050a06050316090e0103060507081503150a0209040f1b050c0d0806010212121501030c020706 76
    0x482d444500380d41c1030150b07582003c4030100c1a0205e80d016181640007190100031a0759264141500c030b000840d29603015030050b41d14000e80714002c00080c50045a0000350008480510001504a80f000d00303211682d401c0000307560701903581180100b5000081c22100030820031308901c843c0446003050140904000040403035004001440c601a04003080c0200a60550b400c1c83d0350820386000b09202c0c1038404c080095000605080c012028401d444065481c28510b941c1d0054501120351540411350801120708000646c811903842520301a5205a20102d840c0c107103240300034403400014011014a14060a0707c0005039400141c400070780400306405079090752200d0101009008004500c1d070850b0400802800104560703020380e80da42ea204120203040c49070003408950a0190080301d00d410b170b01540044c2e80070343c00350340743c0f82d4040d038144125000c0490201c041030081d04682e15483c5c1c8400404180700580103e0044100349a40a1904000500410400a656041a00c1036406001c10440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 570538597 1250 570537347 570537349
    0x130e19061224050c0d0c0e010504090e0c04020c1b03010614120106080d030e01050f0f011e03020d030c140c030d050d1112040b0109020c281b0f05040608070b09 70
    0x1c8291808902c8100070042e914010340c40300c1481d41701d000b0035180f041c60841020f4403540281d5400d480a401071f51080e0074603007040d140f24000c042014442046100b42015004035584500041c611441a82c1c040e00d0400f8003451100418032000c005140703c0c1e414400144503100c104901a0780d020800c5500d00440ca00303900c1c001d80140100d40244549004421180d001d468058200c0280e0644030802005155100c3c43c00c41040d507000c1d641d1038810011040100401c240c000c0c404001003600004210380c0365a40d0740040c02440e0f0151044000c41c00715882c180c184500d01400c1c0908a070000003a00729200e940000076110500c7c61085c40901202051008400c5800d0740a19003013088400320703594030038401522a030490011102103c100a0030f100108101000c1d00903031780010139a000600c106003c18080750504029905c41c6410511107002c0f04020030800c0c00005c01c01088180d0f4004000d0030318041844014954011070702a6003848010807115000150041c01c60b050780b5038240d21582420 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 570539847 1250 570538597 570538643
    0x21140a0b18010608012c01051215071707080402030a0b07020114100e09030c0304032d0f050708030909061504030b01090c02100b01051204030302130e190612 69
    0x1008009001d0341000070072259009041541a141c600f041061964059a4450040001020300b06c09801621004001508101071000000d0942c074041e1400b481d101912080444021101d040009200540b4245890a48014241c01c0248c0c0d107803203000c914140e0042903580301001c0c1d00400307900741c40b400100014400e6000c41d01c40c5a44e059008000d080c002e40303044003003030540a02d6603110361000114843c500000b04541e0820300420180d4105031542d1070341004041e4003052200b081007012415013130107140303035400780e42d1520980c0360320003007106030510902d802059080f0755850f40c0204008aa0b0340d6a504049601642c12202c00c800d0000c0701e088500c0f140100e40c0005e0555a1482c00400d412402d50090207048140c0c0d800c881401c51400d201200b038544100c100c901141041010210400b14007800e030380c1c054041d090140c681603c0030100700c80041168000c1d0641c0c0e036a00140302d844500c8021030705841e181400d0620200d405c058180a2204048200804655085010200c046016 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 570541097 1250 570539847 570539869
    0x306130203010e0d030207060b0423150d0311062206091401090b09010e0604031d1f091d040c0608040f06090c06081f05270721140a0b 59
    0x480030364030313080c15988000d400707900a21002c661042c1081c00a0480d03003003522030029032072001c00880300001d034224481c014492002c2d080003032082801424801549540d04502d0b640703446a929041c0c01260b0b24209820710202400196400d4070700101002c1e02066820000703002031b00440e001a00e0b10030b51510421604100e004034045509001421040c81400a0380340d1240320104002d0100a00300103034035869400c02c560080224004070391820742800036211814001402400104101f102d00240311980d406c241c05010003d44400c07414401910210300c070014014485040c007240b030074955140f2441c01540c1c0a02001c0242000000d030a20041d8202d28101680040e001c014804184c1000006181c06000d500041441c43c00413580000b83d5a410400c8403440902001c070090a0a0402944100c035264080455548444150a9410b4241058040d00960329450b5480d96540c0a8070000303100c8003404105a03207890b5440108031482c4645961040200da4005480c0d200b480000e40321942c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 570542347 1250 570541097 570541121
    0x10180e031c0f15051003290103090f0c060f020f0a02060f1b031905030601200a14150718030b04030507140703030e0f0a0e06220b041406030613020301 66
    0x600840d90030342d510343e00c0d1140a1320400d0b204241800003a40e015410364680414180d041512081030061961803a203071a00c40c043c0c1450086510343c9191100c1a04207480032003924182c2d8410700800203180c1001030003480d02501c0c006001500c821441e056112a00510040d00902d03000400f02460142502103034140380401d00d036031148444401c2015501c0e008440102c0d14058a03080111103580a00c0c256031040c04142c1d03807030004c05840d4042c0400d1050600d0408c86500c6211280800a0150302d41d007000184404005d046002401c200c594681c0409004c000c107226038500d20046214508045e0b901b52600a4090075403a150f070f1030111524450301c10301900c2420390000c840d03103024000c141282124040e9442030b42c1d0703252900c1049274038042198400c0d40b01c0311184040102d110f90381c409039442074005082e80b400d1700d280c1500843c1001c0c1080ca40702081d6407800e403001e941c0303040c1c0b240046500c90484003405130301e41500440ea4170030010b0b284003142e215414078102159825081000700b503c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 570543597 1250 570542347 570542351
    0x61a030703111e0603090c0901060903410c0a0e060102070b030c040f03050105040c050909031812071e09050c180a0306020408100b10090b03190510180e031c0f 70
    0x240140f030b040e4503451064030b002d100340382440c00041d0f81844bc6410344240c2c0d40020091002c2081c01d00960396040d02207421500b0b280760035009802e01c0742100005804103200ea0b02818103491260100f00803111150024400328104105001d0703e642e000400741c2c00d42e0403c0b5004d603540d88528902c080940201d500940b8007081d0004040304100064116502451040040d0328011340c80d8810404215011203000040b540184846800103000c0c0d820f02c586803102900780c90f0540c03680c90030203013003034101d401c07008410701c03090141c000d000702d00400e103001084c008400700000d04208000c01c0b940d22845044d5900ba451030400c06c2c0c01669181c0001c1e00455204000715519581c4034421502c400e4007403a618080c6152600c907031110b081454003209003074541c1d514a55018100044070045800c060901641116851854038114080b8450b40380a0740ca900c042c606030070301d03164009011102c040107100c0c1d030601f485d0040908500010541d402e00140d101740c00a03a00034000482c0007800c000406400b014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 570544847 1250 570543597 570543601
    0x60903030426031602150c0a0315091113060e010f0c0201120509060a110c060109050403140408031e13150c0c0b09030c03030a080c13050409061a030703111e0603 71
    0x440e4807222840280d01170340030b4450f800e6824081c0c1c01258002c481c410218003003002144080c521940c000c0a000071020f035800852900e89034600c0c220b07000400d1301200f050000a4101c044000c503541100200500e181c42d6200248200009083d003103844908024003c4490000d011607014050b21245c610340f0703410812841c91301104442ea01c000643e615550240390045102d686041c11046502e1030311010010245a403034840303290300803c0300820a40801886810001581c68154010001424048021610380303a104076009420f240c040210070341102c0400c43c40c01d20b40305d000c040004403003400f110001c02641c500d400740d4602070303559002040101140004200d11140c60040c0103c0a416801c446000e00e94201f8156a48110301100e0301150300b030000907202681d0b8000030180c40c01552146a11070b0307038900c04101547e65407603040721004e48030445107808140c5c4050104040404800401e0759519503200c00d141000c240351898010902580110640e4040c0e540e0050710300005440c0036624 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 570546097 1250 570544847 570544861
    0x20a1413060e0d05120f04050d0c08010c05190f1101022d04030309140a0f08060a0506031f11041d0a0c03050f2403010c030204090e06090303042603 65
    0x112014012140460b0301500382d61290308120701100d4600c0d07400300040075079559800442c0c0c480e8000c40c055100350101004041107a403544064403103124810795178640c6450803d040f403400d442990200300100407051107080740d401c5081299151108040c102070816071003210003201d0905118254891960000a0b07180000c4000c0f181c42d030300451050050100682da0610202c0c2c0c5201d03034880a000190022010301c40d1103d451010450114024030480c412662030006014030038082d403001d40d40d9000202004030491503402015071299044029005000101c0e201d4000103100c6000114500e9560007101c01c118115001c94014022641c0110042d40108050069280c0c040742d18402c0c8900b04200d0f250749501138051a0f0194541c0000010f81e642e80c03e84121510445010b0380303505a050b0171141e42c16407003c1c4100f0600d2000b41c0c0d800759440d418020013409171380d800d1401180701e0380002c081140c0201c0105c1038070f030441d9206654140048002021042e5084007100340d1003003150010601202c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 570547347 1250 570546097 570546127
    0x70e04060b0901030e0102030f2d0412030c090510050d060b0c0303010611011a09190509100b0a03080306010c021503010801020d0e0d02120c010f0501080a06200904020a14 75
    0x10b41d00e400d82c1e05100b56004403003800c3c03d074081958044c682010b8503001c01c8a42600500300d00301c42d54001790303154800090b1103d0a190f00c0095500b503a544400044c0d040d22598180a40342d8810290304100e09840d1030940032a0202002180c000200440420800c20074516a000b1000410540c100c080c2c482301290452030b01c0c3c0c1d000303200710f4022a04103412a410b1180601404000d013280c94210520f102c12842030082c0c40d00d0003410900c110261a00c0b108007009c040c0f00301030140016000a28005801d941d4003421281450903440c03103010b08140800000f285081125480402881e000e00407a100348086510300482c0701036840445000b10011500400541c007803c0303141d5212405020b0031010400715603c0f004400c514200603000034000e0351813680c9000080030724507400400042e140584501c01e038100d5a082e0441c050a03005400e01d0001d200c240d005803101c19028003036200010010400c080e21a2145801c03140c040c9801240340c40c80d81d8003c4c414150440c0001d07400c1703503a5150030340750b10780 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 570548597 1250 570547347 570547357
    0x1018111801030b011103070b060f0d0f0b07051305060c0a0209010308090405010f140d140d0c14030405010c0f1104090303090506090c0112150819050120040e070e04060b 74
    0x40041d1400840001942c821200c201c240d114140186d0704d814035548031125030700002440180c01c1413460068a5803034079181d03a40c000e020300030004049190120b02e01380103000000392001082050a1103401000840c680004044a40464034075543d2204035244a04040c90094040d46c007010f803100000501c0302500c0240b10b00182141c04106c182c3e240c2d41c1003516011280136038415883c0c010f42c2c01c2032034102907031101507050064074190038400346d001199243c1003540d0b02000009030803101c020100180d02c9402000040184069030506003400c0000700205194103020300292500b9081006200c2040f14071115003201800920244005060140140000303840450316440703660006140b2040102d410001d862050350303035001d090301309080000a8080c840e10890b2004403144009600d10003080300d13a000a10305c20b203101c455003803428120301311070300342c40b8000385000c07a610b80c081840c540404450aa40c04032016001c5515007603012241c03d0f85841800b500203181510100302c910b44040070b00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 570549847 1250 570548597 570548599
    0xa0e1804080c0d0f1704020d060e0c180402010e010f03090512040302100807021002070c05030109061409060105030a080a050c061f0b091804080d02210603030310181118 74
    0x40c3c008024004200c4184046000c0307240000c141030b1070b004034400c1c07081c0d07050f800038001850320260f120181c660200712420003280107810b92150040007402e007080004080d000d907088101d41b5691900d5000a040b5000c9003100d103040000c54500255010700951060740c0154000080b5141551000d0f580c403926800f034001644204a5500d1601190b4407400000744507c10a901038203800448444030b030044d4001803411109403e03003000201c1c1326103013442842503541c01910b0124448140d848812404140a09549550b410450040c0402d403000074516400e140d01c8404203a40c2c80c083c0c0f9003100d05002d001d80c4400d080c003030720b0180440100d42080314440b440d81400304001003651104000d150744904003001d508240343d520100e1801c00c1e400d122507030180c002d003865880d01000040c1e82c405c80e841904c1109403204881c071001010042203110070f6000b1420f5005620b541041d001110540c005881a41d00305024290300c01c44d40251900a051590500100e9580703803103100c0a402e04240c1041205 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 570551097 1250 570549847 570549853
    0xc0307030306052110110403171216052502091609060306082508070626040503180a05120a060f06180b01031d0616020d02030a0e1804080c 61
    0x3c0c0020009020840740078a10900400c0c05d200c44a001101034914400800c060303007014040003002c10180c801f5a482c000051031041e84e51450b40058403110903014101c00e0b034040c2581058545c2070f400c10111041007601080341800402400051143c0748516a0002d410000742002e00c801410701c7c05520848040e03d07140c0d4414241c840000f1000c5036124481c0d11a41c0e800302d40000c100002c90b100500c0c24081203040303c15810340f1565024034004003948081c0c0001e400c40300c82114100259a4801481202c00c1ca10f956820b060301c50aa60717014038050402150059403500031207a0302d03c40010010300c4080c14500c4c2501384c40400a4840881490650700c2e03e041c0340c85070a4400c1035102d00d40507524406201c200c0c81d50111440c00043c60a56070542c1403550701d4441040d10300b0180d12903000381104800400581c031b40380c207500c046008503030b584900755400840106085a0007000303071010018280b9080c0100d0118800190102040c1001074541028560501042c0321040c801424099408011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 570552347 1250 570551097 570551119
    0xf050d1e0f090302010c0224040203070b27061207050d0b0a060f110604170f04090203042001081b09150f04080f0f101a0a0f060909050408030703020a050c030703030605 74
    0x1046c1d1b26a00311200c400c0546c44041400c02034023200b0000207811900103400c4070744050300c0d81c02039440c9510600103e407504150300d1981c2c0411500b0300d0030103804032040d42c2090400700c182c0200c840000c00580070754140180402d08003001d614990003035130700d04401080750300703e1035880303201800c051070000003030740080e906142c040003e460005625024030360026060300817a018041e402c150303030080c100c0c25054500030840042c041c0c01174005580154080c45125084642c800c80480320025080080360500a40404125260720500d9100c40b618103000340c5550340308c5180300000c00c1c2000c01054150344810206200c54084a400054003c3c0c400300f00489600707403142c91403240e4444c40360120790000e500c645560b0400000d6600034050800d00500320f41c55032001c0b0800620544032a4010005046a041c1c0800c4500d6000503240001d0070741301e6042001d800c15460b00d11003440020150420300d40c00190f29406140301e07000301d520104038181503d031102040c2c54010058484c42c8a968072400041e50 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 570553597 1250 570552347 570552371
    0x11030a0c1a0301030c030f0201020f0a21022a06040b0d0e07050a1a0a031103190c03020705030d09030c1403040e0609091903020330070f050d1e0f09030201 68
    0x20841c0e05071385d0402c800c805104c1c1b03590b4940304a00d0100c01c0813811030145641c01e444004007004402a0340340724a5101d801a41c1d14200f0400b190521100c1400715405000c1704803551400002056488c40c0c1204400d05801103000071500b144a65441000e00c2d00d4001401d0301644c80315404078508803000d13000c0d40d003c00e81c0c0342d080064180c124012061000020450320f001c414552000b009404020300b030125106041100804031600100e91155560000c0c550408411845124a01313282d0002d080c1141404100c0e1a683c0ea28080d00c415000d006a640300d0758000e142c0103114003200580d00150500c4111030450703102e922500644155224108500e01107282c0d4900744000d02d1041030200014130f02034040021b4040103602086064003540001c11000550080d440c50940f0712442e580b8010500b0250355410b2459440010110410416501c06130840140d010040f070b00e001c101c4520105455020705200f144da00c0c00700d40200da400d80352480d80e03401c4490344e1f0042140c4034000d030020400d90749915 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 570554847 1250 570553597 570553649
    0x91403010615050306030a080c01020304061514060c0c1002100506030d050f0315040203070f0206060307030c0e100b04030605090d08040203031605010f02030103061b050c0c010c11030a0c 82
    0x7004076100e2440014036854042d02c00d401845e4000b0380181214500c40c1c440d250300003035500103140300b4010f0750008104000e1000f103015802e1500312803150305413424a0502804a5681041102441248001440080c0103401c01541c48031140050080081045944e4040c1d5903803000c24a1304240303424200010010720307020854a105010f01d4a850b03150424842070950180e0008000748802d9014600d0303903941c0e480c0e5101961013007425455904110781d4445010b4549000180070303500c40d034001482800000e03482c0e0b1214085072001c4401a410380c0b9141c2000e199010b954000c0c0c6940c4c040814000184503650308084c2c01446601d060358151501424100c402ca181120040c1d0182d01c1001010403215824a00c0a4410301078000059403c5189400c1e0303003a40e0080c0c4c019a01191120904495030541006418044015044c018a00031458206544076807a061180f818840d018801105012041c001403688006c020113486600e201403600380ca0350712503806840799812158902c07411192484d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 570556097 1250 570554847 570554849
    0x50c0705060c122706071d03010218040903020a050f1e0c031e011d0708060f1306090305210114060705071e05090a020d14040f121107060914030106 65
    0x144102504940e01c0c0160a2082c131100a801d10240840022541d01e41c1802d12551b4010012039507542c134581d02c02247c1c51106202552020700c170341d10402802140c0703401416156801030b001d640c00315040003503040580c2000c80408001e44070b07001e8482045459080410240041d00704500c8601604102d02c24031a641c41030417091a41540c005015101d400090b0820403524240803000820480841d40003020500422503100c0c0c0d26600a1009010000061048075449031810000c94040d1400031250380c01002403242c0a8840e5655000d00c00c1131511440031182083c8038007100c0044290400040b03800c1703d10901c184005010b580c1d1a11265140c1042107400302078200005000780c3d410f0807425180000100c1d40e542050800740d5001650b51142103c591044801e10760050701d4101150140055940d842c6201003000c6d801420400010403c0e000b9154407500700140b112030007080b0200b501c285000c2c51061000f0310500c240040c10960205000e0141c868024921903400300e410203045c269115 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 570557347 1250 570556097 570556117
    0x706020a020a090b0f3c03060a0507170601120207140c0109061215030516030c0b031012051e0f2a011803020a031203051005010806010c0c09050c0705060c 68
    0x43c43c0080b805e42c541600445007080580d848102d01c0e48801d0b00c8401031000480030205001d6040d9403820a518050001580c0301e40000f00c280404e20b015031008104550b8a0008a04045188080f40076648950307000b2403420f504220840d500d02040c20b000c40e00900c4480070201502c101403600d0030f90751080100b1003c0f28000d8541c48090300c4401300c0c0001504610a540000441080001000c03c0042204040c0380c074845c0c5100c00810b0541c01c1c00d25a0042c150050703503c4200c200700703000540040c0c0a02030304864032540211000d5941380745c0141085080030061640e011545441c3c8285100880e04a84000c40d0100303d4000d0314918480ca030403010350105c5600c8078001c902101009500031054641101001c1255030129a02d960001e15000c805030015140c0f81100c03003001002a4041c481c881d00980400c80314800380e450712000800c914402001d06040200440d030b90020003100d0b50f900c8000d42401082800075162020055181d07810202e0140c806200b20400b1910a20300f5404030303040007103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 570558597 1250 570557347 570557359
    0x100e0906030f0c12012003010e01090912081302040603211805040b0604080703030203030f07110a080904090209160f1704020913080a081f050307140a03050706020a020a090b 76
    0x1c0030700c00c210a104201e807240000c2d54032240703410341800700003940d02c0206d80e28411a9460354100450200b080c101600501d81581c50400300c0000b00301c40700032001080c41d03d4501003100f5960404802035929080348020340007401c1500c00700410500031040c05144042c00d65110b100c402c8024100c0d0b03007000303a040141d1440703000c40041c1300c6820203410140141c0d4001d0901841c013680c031803046245c61200da1003907006810100c00e006407044002c020b143c11140c00c1c0313044d8580007400c0b0441629050075400040c9100d400055070310058595802c016103183d00204522164603001c1040c81c0e1071500d00d411040001d22304641048524092a000d2041c291050441c0c085c9907119401c0c0311010f4405402214801500c407100000071394008010400388126640301c000b2801e00c88052440e185054003540601c4903203003014001c544000031840d0444181c1d101e92140307070f11341700701091100c41c2c150400740141c0100107020900980010fa1000450701c262160241c0580d0345078980c00700c5410254a0307910032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 570559847 1250 570558597 570558613
    0x80603150105040c110d2c03060718091e05060409051005071202041e0b040b1e07020d0b180a0c030204020d150f05010206090f03090d050c100e0906030f 67
    0x30400303502882080884c1d04224246000a12010b4540000d449140c00010144074000341214480c2d1a00c0d101c44180018488a03041141d00003030300c44100030710040c100002914103028403852400716a0050a00d03810410500303800c4220980301702071000f80b40c081c0c0e509150200c0d071036051620400301e4039900500982000c0c0b0265200001502003e407180e02003290b48071403103007400c005100500c0104102c10303500001010040091300241c00c1e90348154815170040c4420072103100d100d811100c0c800200b4905c041c22640d04d21061185015080003c1d400c91032082001d810406c04400842c0144011079115044104615500e542d902c1007820007041c1c1e0f954a402040103003029009420644c4141c00c001c18100e00b164850003005800c0d611100203c203210230700704650358062068940020621007d40301c50541164441e81c0ca204140005010b10301c4040b821007404020b2106140401c0c0082c403800b9a9244d5050040201001910083c03050b0300d0b070404590f16140000d0702282080c1001e015007644 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 570561097 1250 570559847 570559849
    0x1707080c030a14030906030f0f060f03100b010908060f1008070503030a0c030e130f0b180408090112020c03040906140901051203040e130506010602070819030318050d080603150105 79
    0x220003e07000f188510007400f10302c410b6659000514890400d80c840800b007403500c0140d180e07500e50702070902401200d4540101106440120740100c81140e400000318a9109001c0101ca03d0301040e40544c109008407000e000c04044541c0e10180240240290350380500d03192004141c9500380780c800d0951541c0200070310000c1c1401a00e4401c1c002d400390170411a1102004c000c1f401d0507005a094181d26541c0760303a4413104034070a00c100220304400f607070410400034404825207040d00b4081d00c090400c1c40e0111303170200729a2048410b0070302011407078001c1d5122071150300d03119580e8005001314604070f41010000328450b8480d0000314109180101100041e03442d05041c00000044919095550b020810000c42e104004204050080b107000d0070851481801c0d090a03420120180c11032003c5420184080102000006011074100030114560300001e295150a03030080c0703a016041740b262034584600006200003c6985d882d00d1100351100c4580c2d580780c908060300c42c05c110b00300c01e1002da1707000b0051003a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 570562347 1250 570561097 570561113
    0x121401050c1c0b0f060d0609110c060c0706180c140907050919051e130e0307144305100509030118080301090e120d241707080c030a 58
    0x380e0054945400d2004c22004607003203501440c41e103014113849950821161280d481608410305000d400c0d5800c04203500d04041c1c540901a002d20424080071409100307100340d030340c07050a140d4441c59050305c4d807801d41d15005001500c01d1080181c900405103146a00e1f08041040610586066075200d1601a102040129080000c2400c40c1d005c22040b402094588581c141d440c400c2810490131351000c446407041100d0030b01c00544400740c4601301828200300d01d034008162419a0740c031041c1d40c11031a000f148007518100321400c0c01c0e500c10403060800f1103030001c480340701001c000180da80f14500c440c000e2100c4c6000c1040d481501d401001c005603046000b449840644048a002400440e80848840402c006502c070b044082c0c480c0c0740f00100400c04a000d5120740d00460840b1400303002004102d0200c0c00d11401640c08268944d41c54420801c1c091107031101c02c83c0d0587d2414000c0391425100c5400317481c1e00782080e060300745d50f105086010039a0303440041c1e00c0220610060082844920650350005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 570563597 1250 570562347 570562361
    0x603020f0a30020d0b030304050616060207050105070804030809010603030905190b0d05160219060914100b1e030a0f030203040b0a02010b1017041704121401050c1c 72
    0x484451410581a84000c204041180b074902405601c03140c5404525040b5094045058800c1d44104030400144d182c6c3c0d425607038060f072100e020702400e4040f804c00201902c2800002000c5500e050100240640c0004980c1d018074025038445006a54020302c4601b2281140406808038840041c00c0020b45801c40030540c014404664040d0450380d0780c194420543c20410f4201072440e00e520810041d02d103101d07280002070000b803005082850382005030941785200e440d40506225220200c4a0610034175080c82c5c45004801c4086484a4412941440080c00036200940c0326a0b241c100024201e040252164015072009001d00040e040540e1108208254114210250302003030200040300007140010b0300f40004e440d00042400c680399810006559200034401050151042d00700000410540140da0300c182d01007103c407160f0441021440b0107009a500090a51801480140070421b00351004100b00038104001d00580d111401160018004c0208244c036880300794544921600b82608045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 570564847 1250 570563597 570563627
    0x50c2203110d32070801060311100813020a05091e1501210e0f060717072007050301090f0210020c1e040615020a15020a0f050304050705090f010305070603020f0a 71
    0x4450702c0d10306121424001c2950117425181d540c2c48041040c0080072000580c607100403905002900c412500241c40700802400c0c00703c0f42c06481507503c046442c1c940b01d0b200501b000400004992820084024104c40e001e02d0851007648440040b50040c40500020400450305848520620424424205c0d814240d22034100ca0a030311141c5110001805200c000094210000a85200d2030728000c050074034200c14010b41018010070003080381007a0700205401c9041d04068004100c83c5140c054545044599003001d81c1c10751a140c40142040541d22100361050f00c03c2d03404580c241c80925051740c0710360052402c42d40002006200900403840030b980415010002440090015100d42310099600454043d02002da8040240301c07081c0150b6120131082007444800551800c0140310000f00500705001c8aa010f020b000700105c2c041220601c016405408040c00b01407031464000350750102514284420380c1c49010703d840210b02c56229008540c250052800d43c0c5141a00d0100102c0b50a1141c070954 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 570566097 1250 570564847 570564923
    0x4020d02040b03070f020c030c010e060a090f1514030f0f04050a0b0412180b190318030f090e070507020f03030d0f020c2806050c2203110d 61
    0x104041c10b00d180614014081645c6405001c0e02c0d0080107440c1c08810701c805882607100303415040c5a40e80c0a0150f030ba07031350303010b492054492008801c1962034112a400031002c400c0b0705000890903c020300c101c2d11203204150b80700301501903140494046840141d521260502d480310010f8061010040c1c040d810600c0b40040300c6801e052600d40c41c44d0501d064500320782013030003522034200303a9600c241e5a4602c003504040418855260105892140c411b000402c030090084104040c0c0d12402544000a25541e00c13590b410b05256614008107020450800a400f20340803078804a440e00802000c10b1003121507442c0c0030716000b5285c0810007482808403800c3c0c0e051008025031201e507142405403020390001e1000150702e501361400d8050038402d8558240384e11002d0100560305100300c003101d00e1252900b0090004030b43d00c41d03000c0c030704103441409604018401920000c00c10700307060030312200499005805500a091145040000182d5425009040181c2c41c008044481d040314514601c41d502c1c013120 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 570567347 1250 570566097 570566099
    0x30515130b10030b0c12040b07050702030f03031e0c03060f220614040b030616091706070f11030a080901180f050c030309030a06150302060c060a11090f04020d0204 72
    0x3800300e02260885400e46070300c0c2040030070010001300700d48098000307802d100b0003800c10300341104c0103a042c94010000341810349803c010403111400b07102151112900501590598104003444580d603500694882c24409072043e203200c0e041c030a0581c07150240603462251459500c415081190000d50380c982c0d41d9001e412505011100341c10b24031099418086103002140c080c1c0741c1500f555411209030140e82c0214280501049960380c003180a03980050591a8030942403000d100440d60f100c01a000031903101d6107089a54880800000c2e00d81c854a580d540d080c4203025000800c807042500020b01c004158002d0110b000b10f00d0143d40340642c00905100001140349030035080b01817030b280408054400e5448804401c007480810b010700b04c054541500250320340781c0d0080c0400e40c0d8103c040005064250b0390400100314640d441d22210086230001e001079140c0d14220030b900c0d104c00081d18aa801e852400350443d000c08010340c282d40c5030800050102600c1c1c0410001d06c03000e03606c040c55400e103850342044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 570568597 1250 570567347 570567353
    0x71101110a0804050106050f030a2603070512100501080a0c020c09010906081606210e0615091003080301140301090204020714070f03020a05060d09050f210403051513 73
    0x9801c1c600d4080d911280d1904040c208a4219403083c0c0100c0d004004000c007080d22610000385480010780d1220010000000080a103111007581807140c0e2800c0f2400401e00220560040140000c0214525480342d25100c140c0300188528141c46040d004c1416400043c4041c1103e40c0700c0d606140b003900594007091405c500080110b40d0907080420607554420041c801cac944101f020007489101071094003100f608103c8090942c82d8103813200b4040e095082800280310150f5040008904500b038112402810441114800d225419210034050700204001407994402030592200b00c030f8001104500c0d40c0d0900703a0440904400300c0c1540d03090f640f950014801621284010950725000d0075000210036200c0c0384143c01c21469920030782541e001043c0c140301680d0383c0b0303076124221842240c0142d0b81d5200c005035940a44101107015020380150828041001000302e007108040035005011403c40c01c15a00d41c18460203075010141042d41719040c61401c4244440ca02c0d900040d015080a14040e45c640d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 570569847 1250 570568597 570568631
    0xc0a03080c0a120216020d140d0e062b05070306030b0609131b1706040507061119170c010b01093309050310140703020a120c05090406060201020306120604020108071101 74
    0x24115180c14003069248d08042c020320544045012a00d044010045038400041c418091a1096842c40d0380c08504c0010054601c8083d42c0c40100821052005162104024000b4503083c030003074403088a08400144145413000c07085200300c0c21843d515151600a0f11207586154020f5190980c201c101c0b000403600034040304c1c198a5010480340140002e1520740b411074100407055100c1c2c4248082c9070a400095000801c40c5030141c1d04503074010f241c005040c28905181b840c00b05d800d0604210000b915102342e00107400ca124210420b07210300030300e50703075a159820302d16801074a0303c8040c0b944010f94501e04030f0315500046d2840350503c0e11000341c5840f2400a4108a002500212000d81d00c07256003426246000410f5030054040c2021410314040d081c0c05003010094451070100550360701440d1205a008400355400c00c1c9010b0010045281c40c1c42e0301078001d500c01d80d00588036504140c4401d042d0350300040c40d10b01c82c80d810781d603000c15912107520658190a0018000600c2c1d529040c2e1518699105 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 570571097 1250 570569847 570569869
    0xb1906050706111303050606030c0102070b04150e060f0a11210702041413060b090c03070e030a0c060306030b0a0b0d1707122a05120711060c0a03080c0a12021602 71
    0x9040074006da0b040c0b181c04c044c80c10000c00c5c072a40c13354100380070420070381c1c8000302550120b88007295140c0170848101c0080b500c0000000945502070310100d010b980d052a6240901100c0d105501c07101402d005145445580d0110291a10b900c108030b600c00090414070000548072444c400341c008150880c04500365042ea00c001c4070020b4204111080c00c42c240110b0b030041c101588401d85041905062200c1260101d1100505001c14800d0383c3c42c1801d007e0301c0800001c111160807508400d02c0c543c4501d8002c0c09004180710036916400c030031f80469601403d611a8402c01300c0d0041609074000020b5550766040c00162041080980c8207012080c04140d55048000188460750f880c2030100d0b0401010b4400140280450540d80b4612488100003400c00103100b5003c0a00d01c0f0180d03120282850010f90b0792003039401103500f102c808500440081c0c400a150320314a4802d0301c40c6113890b030b0b071a081000240682c01c20000020f0003c450741c100f14180340c0c0100300b0340c0d0400f08400008640c94020410401203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 570572347 1250 570571097 570571103
    0x509120a090302090a0e0d110a0201030504110a09050a200a030b0112090b040309060206070c1106070804231203090f04020423030105091501030b0a0e0d02010b1906050706111303 78
    0x2286d401c00390f9039005105094011140c1c0c10254405c40725001d420b80d88444000009040c55910004141805010803024001140041604d608162201d1000024003030507100c0140403414407203203541350380484402c4119940e011200c10305080035420300b20064039406500390706007c003400b080500f08506000300c007d081d0041115040d54241842c004016035041d07400441150852418403c8460740712405030211604118a10900501e8400040c100d21492000520350b00c4002070010758030444001a416450520400d81e401c01220b60074080d1510310000b24031280d800420011203545469440044810805000181400c0e00c440400082d100c107840e4550003c07000710381c441c10502c1e09016141c0c0c89510742001c1c000c01000d8081000f49120706002c020305080d400800214914544e9101d0707550b1618910481c2c010781180c20010f4020054405480c1c0566610b200c61007003102d54200c203a0454070280da5441c41c1110545422005041c0003600045948040149600802c0409481c07005580 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 570573597 1250 570572347 570572351
    0x6151701020403120306050105162a050f0906011710030c1403060c1303060911030a14071508070c0f050105070e04051f05060f0d0903050307120509120a090302090a 72
    0xf0441c03d0455a904040c0004400c25003440b41c1072000c0c0c0d0380203081d5400100402c5581c6221445440e011406081000c1000c00b4102c0310784801c080c10366030080c440f00302c070025121014400e00c85000d002241c081115002d0101e40d58000b5025407600080c0c829a00510184005405540302d55071075a1440159000c0000040300c1c8003c0035051a00b4080369070030404040ea0180340a116450258a0002921000d030a40d0340d1041e04c40c0910210245841c8094401402d075804000c4c20300d460a2024511300c41d50302d091080c40804a505850b040000e241d042180c2c5601d086a512031200b10b460080c2c0d081c0849054281113201c03800981d090080e2030103808241c40b50b00e40241640d090100b1500020301c43c141181d401d601a686c01019006000c081e00c105603a0a5614940c1e001c401e0f40742d1141c442125841803070484004145540280650300a44a80d40c9251041c0840d40012043d01c0007079410140c03d800a03da103200b0700300c05100818600001e4100140d00d00e56035000502420310840d14095441d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 570574847 1250 570573597 570573599
    0x70b0706050f2406040308040e01060f0302251406010303080a0b06040b191b0506010e1e010b09040e0105104709030a0f14010b0d061517010204 63
    0x1998080d19078880c01d0382d45a00700a2a08404011400351a0701c000420700c80b03680c42c88542910740e08200d8000d540c01c100c0141c0d54581d02c22200f164071509100703000001d4140e03901e10700d11178481c0c003c4031000d50300c2449010140c405c80c501e441e6003062040d01100e1408074041e80810710142444021300031341c004c2c0c554810b2441c0030003001058811000b440340c482c0b041048244040022081071324220ba801001c2c081d2070707280d0341c0b20a0721aa904094030025260070b40b1304407000c1110025540d8140c031110b00c41003080f134403548911020b40119003030300030a0041120042c06003403048030207000100402000419615030700003a003030840c0c07000d5880d15200002d03c0b034240812a4084503050240d0405040500e074402070a1107510f100c545a2101400d0800a004400c00c02d40007005444c0100300c001c00b61a224446883d0103202c11510b00380846180050641103020380106124880c41034101030004118106036684c1c1034000c080c0002c122404503521800031440c2c041e044180340040304030000040c1d0b62 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 570576097 1250 570574847 570574853
    0xe01090c09150305100b030307140a06142a190804020a05010507031d150d020a080906061e031903170a05070903060f060b0f1c0902030309011808070b07 67
    0x1c1c0b803940c2c50300600e00c40a1101040040d00000d207404944070051030028801c0b0702200005d003188103506010304288200910030040c20401b24070090340b2813041400300000240c0421400800304202c2d443c0c83d52041601440120030030030030a001002d07038105a103e2600382c60495403520011042800c2c0002a184810401113081010380000075240034245507007040c106540041850800e960f540d0014074907094000003036152880700c1c14007030104040e0b058940c822844204000d4010784802c100144d2000042880a0b0020070704500030030b80500b45940b010040180c11485040010103c1c3e0188a144180b1044110080c003400304940303e941c503100d580c840d5040c100244038001d00003041d163702e00b4051002641c3c004d00038604482e070050020588070820b0f86510028115035000e03103110000059007014141d282802451020b050000003044202c50010b03070070840d1005480250141d008001841596000d8003680001422800c01d0071603c0340caa40e921400c140c010380c0b0090074184007003000410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 570577347 1250 570576097 570576101
    0x40311060708071e060603031223010603021e030a051801020c0607080618070e0a170d111c0c0201091e051e030604111801060903020f040e01090c09 65
    0x81104119010360400481c2c0c1c94480980c8501880182501102800e4408a034514039401c1c201e0390f0011400c20601d696404c01829180b8140312461882d442c017681400103850509850300d0440700c4504803591a03081900c290000d500003040c0c0b00d500c0500c003060260040417003008511816600308040780f0707070424441000388026040e40e07414a03640107003c1100c0302e420000340a6803100c9a842c1204d104d4890102003224034a501080111074020034040000d03268020300444038400b0203544115820342d42e40c40c01601a4007207040c03407507035070008020200d500d48206100481c540c0181c05950410780340340391482820f00000c000401207194213020009540c0c228140d00003c103207021800402c50440f0404c542e4039507940c080c05120700640c000c510b11201014a191142040103402c40c3c00e0340c02d01e401c2001460f40a0241c2620403c044003401c1d41d0500d0b94100380e41210003a4585480d02e60841d8200314001d03601145440d0480c1c2e13140b4185002c0c0740e09026490045000e0901c4a410a081080e8002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 570578597 1250 570577347 570577373
    0x1a0405010f11060613091e051009030914010302122e08151f0f0801150602060a0207291b04050f040b030a0503310f14030109170403 58
    0x6120840341c54991560700840da4941c000b0003141c40100e030303411740c00d0601c0c010104440d0240803421204200c0c801000c00f84501c0041c6800b41003100c030a03440d118032020035079003c01001000912080000c10012010514180c5840030504004d030030250702ca0188442c06c4c1080f150900450031f00760582c0700118006698140300300e43c40e080d01c1031075420114100d54860a00703d0a00c00780001c1c0000911810000c0101d5158a401d1301c4a8a1034507a104001f00003d40c20740100c0c2019441d14400c151104085400360b42190180c3d006051260340d8640054000d40014100755064201601e071004201c80d200b04400001c400700d540701e0068141107041e00c200303800d4960084c2c080941004140300a41d5810100e60171084221000300e1001d0045000c6410030110f490020100c2c400807900c0a0400480008034071078903c00071180040d03050b03034043c10150645903c14024800d265403820b2058100401e9504004a07003d40007282c00b841507503810402940c01d41c0a0301480074041401d004020101d60552 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 570579847 1250 570578597 570578627
    0xd150c1808010b0a05010f030e01060b0901021006060f0c080c071502160302031009020607060509060f16050a03020a170702030405100e0f0405180f0105010e062d0a1a040501 76
    0x9201c02c10003051203486136001d030300c0c1400203002c2500c440c01d100e80c000d0010500100d00174040c41e40e4030002440141c21409500d03026004031f812401041126200310021a90541d450054061010006580c500c0032441d0981d40c00f44204003000044c241008540c00900c56881c1010315200704081c028201055a855a4403880c0d07410010005aa030029495881c1040c0800000795048180300103001c51088040c0281301c1030800c400c000c0e600030007140c410312811503034000c2040ca0307882030408071000c0c0c210720090010400a1005020042c840ea0240c40081224201448580040081172520310401c4030803500503880090140010705214005505282032800c02070441c86c00391002503100c0c40036034661800b40365600f0000d21404040000345020311152826254001d01d219030460181400340078030281c5404079404104036040c0701e140e2480c584100210300603580c5107002000d25a1041e81055940403900e280080765136404c0c0c3e1141005c415201260702e641e00c4c40e000c000341035801d12004403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 570581097 1250 570579847 570579851
    0x1030f080c071d071d0907030e01150504060819080906071e020103060803040621181b0e04050a060f0b180118060602120901030204090216021e0a050d150c180801 71
    0x1540c00707913001703510103039002040702d00c60700b00d64901320101c000b4050a0344400c210743c00c05070180c0411030310410440039220181c805000303860f02d551216a48039a254110f00242e2000f41424000c1540e26014000504c80140351910340501511f402c10050065a03805031110300c50201c1404640c0c00d445008000c1032504061b40c10036260200142c038080b8001c0c084200e0800c02c0c1041c03801541d050703014072410051070407000e80142c5141050b000030b4a401007022041000718801068040c0481c403854840d56005000300b1001c0c11584d00d40000d0040350050400c0a80c440241201564403542e40302c2c424542c5803003120031985003804024001e40405407403000c9514000061102950106100140000c1c06401c0c9507a141c9500040703000348901d0b405001c030340d8408a00d0203d509484013407610b241d0700071520b610a0148002005841004103219030345e01003a40c000c10842410243c810f00806805084080306001d00741009005407940c41c21081c00080b03a44a440c803110442c0031440740645031400003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 570582347 1250 570581097 570581117
    0x406060212030c070b091c09050a05010e040e1f06140d02220906091a15040c0909050709051918180507081f110301030f080c071d07 58
    0x1a4981940700d5125001200010000703014504000803036124992240a44c141d83c503040394402d4681e40007140500c0c3c044003010345d05031604d00c246a20f10a440000748030041c1e00749000015a01f01e0480e511254001e40c441030300307a10040b420302c42c000740c03180b0a01100d054455990918005c94081e03801410030000034914042c02c84d121051089900b83c0d040d04c0f080061088000e4135000200d50b0040c01420034185000c08003040000d0300034128080c800e0351821110402e044098008034000c0f1070f00040101e4081403c06a45000d402050070041113050842c0da940c1c94001c0c250544404075131050100722180380401107030410480750810000601401e0792000e0800100c102548940040c100c441501d4407082c0c5800e5008051108090750f00c03000b01d910013980d44410715210400b01e01240c2d41c00044880781068034065000d105042c0342a00c00540c03441e800c60303580e00569041c451094503114021300c01441c0d03030030301007000138060715401e0700c4000502d025200201400c82e0091203441082043e0803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 570583597 1250 570582347 570582359
    0x13050405070f050909100203040503070b07020c12010b0f0112090c030605010e0f0c0a0f0e030a0303090b060105070510150308030901020702030c010e030606010e060f040b1c0e03070f0c0506270406 86
    0x751b0b40e074202100b618096500d4541d4102305140d402643c40203030140b0414010b2001291300040c1c1c01d502c00700e003558485000340180b94081d0895143c0b00c281c13a00a0502c045540d40303903100300310001f103c0e403c1e0700000072217840b9501c600281d030f001a002215650b5540b8014441600c003882c4047e40f155448000b02440c2c5002d500a4000303011fa005000148001420044040c0b40194004c8400004c0a0100c0e0440410780c10001c02030540d940083d07986090314000b045481d403081c000c40710b526800c0001002103c007051040d400404c000300100807801c0b40c8001c04000151043e004500a0310540d00243c0c0724075160040605001c0818220703030501c0483e0300034000c80e45021030050381c00402400c00020f49588179000c241c0c1446091b050f50b8041c0c00000740441c66411840c058100515001c01d82c001000701001140700300c540850240341d00c0da109008220018030717444142a01e00d480342941040090f940c0010031010781010540049245440d5101c0b030749015204503c0721458401c907400d00c516442c0034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 570584847 1250 570583597 570583603
    0x10e07260d0c0807170c060f010801150303111203090d0806010c021302090109080f0f0609031e03070e06070605071d0603060f0d050a030f1106070e0402070213050405070f050909 78
    0x7000b400300d03002040c4d41c4180000e000b6140c00580e09801210341d41c00c400112280c41d100d0440d051010000040000319031070405100340c80d814251400071034815415600c0640b42c210125031508128415481c40141c407015130005540211000b04c010f00c42d001040901401031800145002d040080f0b50203002c01503500c1041b80c00303c034403100f800143d85544a0004961910150b000341100d403003180103202c40f040000407104a980035035010340356030b500d034000f696450348501c0c01e8002000c8601c2040600c07041003031004541241e45c6041c4080d1030b50118010079100d400040d0180c0d2700d15924002c10a41da0740000c1140031994070800385643c0d11075000000744c960b001c041d115601130341c201054485c80d9140c2002001e540c9411401300d0780100100c0c43c0c010240b412407220000001c100d00c040e1841e6010004030280501183d86a1313a05000080e014840290803007141a64407018070060b070340d0304108a00c0340703034043d500603005000c006040007905038044030a50711081c000c507541010400c4400003c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 570586097 1250 570584847 570584867
    0x11d0f0105090f0a0303050c0d2c01090305060115271520010b03010b151e1909060201180c3309050f0108090a020d0203010e07260d 58
    0xd080c066100c1d02e00401042d03100c80c001d0001034000c0074002000c004c0c1500b1101a0929002d2042110711980769040e040743d1500c10f08105042d252400c584141c5888194101c5107803014061601a08480d560b4441902c0c14401717a10183c2d111300c0740a01c821900c1e500c01c003103081c030f00728000001440080e560a0280c21007d644214283e03000c40d880c440200c40d100e903621040304880c40c000c80e400c1095030180703103008000d0762031064442d603e00303548841c445c10042d400800105000302c00a09201000000940910545145840c2a10200810840396023410007081090810b41d41c0c442040c1d0070410040d00b11440c994140c09114180c900c84800203001d980d011094603562810040c000c03a14081c14080d13144c004008166a104925041c2d40190384071581404032281220750001c080044001074800c6d8600b0750707904121781c0004c1600e90260504018403108184060000995003040035070903421700f82d8030f801803400082c2c2810b40c00400c10b14100c0c1c024409440e140035158208050502604081403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 570587347 1250 570586097 570586099
    0x31113090f03080c0c1b10090e1306140c03150307050a1a1b0f06060103050c0a05220602010b0f0603010602070e1902070602040569011d0f 61
    0x8040f0009401071442c5050340e8042d454201111a581c5841001080240d00d4035440b50003000000404a6034611820381141152841921290070b41c8804810311900822880305030740310340d2a0301d0420310303000700200c0d030301d1040c0200d17a0a6600c0c0d090180307003030f240302d840864050710940c40941d00b408903076240403400e0111020070a43c091180e00b410313a072a1f40d074010441e800c00e51003540e48003250407040c0440c0300809811000156007032036691800550403035209a91b1100d8a04081c08050a000d0092004017010f0411400480c0700380a850240e41e5071200a42001d0010707511841c1020160600d0445120b030114110340c014155810408001c4d80d42d40c140c811001e8070300c407140102d040c0040c1910000c940d4401440203559964140c1081d2010794080d03c0361030700922007059044141241250007160940380c2d010a06181108054403a40e000811081c0f8103903074400000d6501a021070f2441d81051104030000004007005400000d409510301d1240f8400390450800300c05036543e01c0065484102c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 570588597 1250 570587347 570587357
    0x60613020711030303040f150504031e1701080706020d03020903030a031107052a0301090b0c0d021b150702070e19060e0a0509070602031c1113031113090f03 69
    0x155504080b0040c40d410210b07250140400001d0105214000758010603940c06140034140141019804800321902100c01800052513425445000c500a0020071144000e0b4035100322402040c20582444d81420780c064055076100e45000c200d450780510442440c040c160804604010a00020944a120f00a075000400d9614056040d030340c0e5061095402280d0000d0844105000040e410359006d03000c00100101140d0f00c0f4442c51184c9414014403000c0f56024696000e00d4490b50388906040d000418445000c580034402a07011804200354400d600b0b401600074003180100d0301b0101e0300e1050140281085402c04202407103841d90f84034005810040034003010081c4840c60740d820000388400d401464480600380140009a200d9801240c02943e144040e03810030343d030310201607942c0d06c145001a2a0481000e0009410407804d50080702e00b2082c81c060a803602d4003a51001c8111901900200d0ba500d03c8005045898201306007518800720114504000d2100940c5a180b4142952000102004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 570589847 1250 570588597 570588607
    0x207240f0501050621060612090102071a01080a0b25030b10030608370b070f090614070c0515030a0609090b010905060406031b090f0506010f11030c0703080403110306061302 76
    0x2888003401c071203000c2344a03035031800103003401c40909010707500009003606c80e521107421615940e200c6809081c100c4028070020520520b280c5e4512490841c0203081c0455030480110380c4000507442885100880f401c0e03540000c101240c20700300f00710f4203101e05808003014a40a4244a013203c00100701e094030000d103616035200400102c102c0d1610104080c201318100040d000d1000300058151040d00600d06920350103010910207408450721b5209101e818001410718404a404c07040d108000e22070b080c01204860012910390003c2007030000713881404c18280c0d4000040110000c05071044a025020800c1d05210b1404d582d1101905081306004030522213607107a000c00c05583e0f80794040401194011040c0d12502583d11400705491981e1003002c0b0503d041003054501030490f445114882c0f9416160481210903000040300e0356401c03400c00214521041240740b1140c0c1701000305400a40c41400e00964a5065180480311a210003011901a50185090000aa80d1814900c04281145030b00503261 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 570591097 1250 570589847 570589849
    0xf0203040816240c08060409020a1203020c2808070510080c071202030307032f09010203040306021615020a0f0509210a02040b180402040207240f050105062106 70
    0x1e101c1c00e601980801c4603031403018500e03a000c1c2c000c502074104d01e03101d680340c5a440c401407106581788004020f60080f1920414003040c6054501d074041c8030702078411640003140203004501d800610700414a0104459041c03400f0148060395458040c1c421100941803951500c13000c02c001c080d0307001000c0b060061083c0054282070142c802d40720043d07004001011082c0c9600c1d0081d40320740c02600c0c01c80001c2c3c10210849080300c105d90000c40c0c81c40700700300e03100c4440403103000040250f0003858a0320b0442c00304010010100710f6034009031200041c03a41c1080c101c8101071500b40c1c0b5003c80e01d05040007072401805803c0485812480f6000e80740c805041a603030b42c0000b080012251080d0303401800c01e9070070a5100440f03030840000d203c03001500c295001c10101200130108a02d0f000107a0082c150041c9240000b001414a030b0042c05034207104604c0c0301360740d4070030001190b0001000c44c1280e081d00d42c3e89000c83c104003040d0182c00e00500d0f09443d89894041c01910b07510017132140c075600c2510516158042021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 570592347 1250 570591097 570591113
    0x90a0605131a0903150105101b060c021509011b0c0506060f0103021e13050a0e01090c0e09040f170301080d18030606030c14010203120f040f02060309010f0f0203040816 74
    0x181c00010f051740c1208040041079030450030301780a0079000740392881007560380c02d00842e21038101500308101c034008020760341d0358240580f140610307450441c0240340d03000382101c804c040600e0003184540d0000c10b200c8084450050040b800c26401c03420084005d204501089004c6041c5030007101c16146600c11001100040e4017a104000c00300f185500c040f020000182000800b602c0040b861414840300d6179070390400c005000c48031f13005419801c0c100c100100b1a0001983c050b510010407420b0050090100d00b00280325558122816600200003064440030001c021420703a1402c0c05005045065504100b500d56581075041800307070a105107264a042e00d07440702880728000719849a024041c01c0d45a1820700c6604589108a051082104914600560010043e104460301c0225000d11070380e034000d65800c1d9210080c0069868208031a20302c00561150302c001d42c03044004800218000c0120b60510044507a0080000c44e100c1c0705105000025014a040b149900d90300d59106c60409131604241c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 570593597 1250 570592347 570592357
    0x4090f080a0302040e010902120106051b060f04140708070b0f0f181509010c0b19060618090510031b1701141e19021b03090a0605131a 59
    0x400310001003041d03041154590010710a90740351821048460366a548804264010340c580c5c180c0007123200005110a911490241110384028a108481c58074810113103424008203841074040c1540d46420041030160302141c0c000581955001030020324074040c40c4a4450b00039000348800c03401d00080c0402d18401907000e40300400e600d5400c441d1b84010100d081d00d40440116841e9026449441204000180c0c84040d43d07207400061310391241451140c1e0b61081d0301d0130002c10186010146200700f81d0ac20226106031009045a902c03030301004101e00c51000c54540c00750b48040351140c144020011584514044a0105c0e0303413000941860720b603010218000d00d6580d07041000003402c04030b9003a100d5001500500b150652540c414a49521081c481084070300e54a40326510552698020640415406911040b2018255401410910b01c10540c011050b14040c6c01c91080d803021408200e1845d0045c114002440c523400c0c0f0a1a10b90070b20000031b4035840303611a00c44408644c1040000745d00460044034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 570594847 1250 570593597 570593603
    0x20102070c08060f010503150606090a0306022d160b06120f070905010e01081c0509060403140105130f330507020d050c0307020621090a031d0d0204090f 67
    0x5803003a20b5141da1a9a21021140f0442d010000c800015040c2001700302501f40007142950300c0301c03c1e603c030720502101d58815603a080c1c1003883c020000010901600c0503044800140a40d5259850446105803401640025405000d02c0400c44054103e00c0501c140c0412035000e4241c24a035510400011003000a600da0000f2901900b9410048a80301240e071109481a10340204001c1c0d0b01c81c040d843c4092024054482c0c01d41c046804400907120681401400c000300c0d250140c034098041020a403940c01c103500882e8241a50f204046011800303019155000b44002d00c8400341036001d484000e118401c1e041c1c040c28a060041d079042400399224543c1c2c4c481d03c0d02c004024880c080700b4080c400201021107041005005811180d0300c400d21a00c101c2e81c40c0030601c002182401c0c07264080001913800800303000150200c5080d40d20100e00d80030b44442c4620485009000c08424506001c1c210300d09280040341c45e03a801880440d2a42e80303001e09960701715010340d40080d90801030320740141b842911080103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 570596097 1250 570594847 570594863
    0x90504020d0516210309050d0f2102011427030906040308091002011e110d060801060f060309030518010e0d0b0601030606021203072304080c10050309070e0702010207 73
    0x107007142c1d0100c003400004881200b440b00c0300008034034400100e958101040100006d000c0c000800aa14080b0070200866004280300d901e60702d81a51110400d20010340c0c440c040081d13018900b80045c0c0c0a100d045100e074400780f082007091510181c1451443d04800d202c8200c28941511001035290400a40c1c14840b0090042e9658980700c0c10103141c50b400c58103a00744900200003042c80c00c4c070300c10300400b10001031780e1480b000030912107401100a00684540807500b42d00070f20021030203201c103010b0640140803007800011030504100742c00c806448590441c0090600700340100001030740c840102e90701d49480d4046e0782101703a80303080102c85000100c00c88a5102c062944606d003400040d60b511409240309803000c0080f13a0b0358070300c180c1c2c50f4074405120044c8518180005011607004000400c491074000c0e03c0e040e15400d0761040c44074582c005400c04052584a4002c1208504040110392034582050a2141c103600e4850007550742c5640d20b001e82040b40c9500380202d41c5a034001d4042d101c4840c0e101e290 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 570597347 1250 570596097 570596113
    0x80a03050315180f06030c04060e01080106211e0b040c0503160e0a090c0312050301030605010f05061e2106090a0902060304030c020f09160f030204050a090504020d05 73
    0x206540c005551410b11403204200000080c90403080c00e480c0c046140300c03000c0a50340d800850803650800200416098043e68003151505d60b2a882000041c0c060f818480b0001c1d4146003909084500c2c0d500024502010700b860034580340a214204a4001e41c4401007649014201c1c941c80710420702004008d2071650751a003401b04100819901c007051703034800c0c0e04850040d42005a1550b1a0079140b0480e425580110040303000300000b0f82050786600d015154120080da581c0d40d458071a50005480040083c902100510401815000310741c01000300b4040652a40d0914000504910030303007840001c4014403103001060314140310190707110b94004414000341d13150302c6190240d905d401120100c0c41035021400050030445640300700d0444d15000781c091401c5a40f140d40941d03094200410a030380c0011560151681c079526462540e214405403880b0603901c007042940a84200c22400051082c036005000a10071629000b00d400c040300c80c25440858903890381d00124100420240d0050840c0c050085 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 570598597 1250 570597347 570597353
    0x616020109060c020f0d0203030c0a12060b0307020f010e1b1002010b04020d060303020f1b09041e03051209150a0b01140a2105220204290f09010308040b03040309080a 73
    0xa817400b2228103407800e990000000590482e100c0c80115403183d07490009104d80c00c4080c0c0320b03031000301c000c1d0f0308034400285080d1224002d0246400c201c0c0c4480040e88848a4903107038007028001c800180341e01d040101610755650036401041c81d09a00d03400e01416880c50684c610500c01d4128502142002d44110342d50600c60550780041c0c9164041640588180c5400700c4030124002000d0309404114501c440040c400300d01004142100504159030b09051692071840c05172885561340522840380e00c60603510000c2c90007192078404001c240c00d1039500403c1c0080b10f51b40b03143e000c803584500c4100c800558000000010303100341c0d690116110040c00b0205144003499001441d60701c500769074035825002c058403a56040c0035035100321034014950304000c21100c00181e9003103070407403442d200610224080510050170001e800708414440c6c0d07161241050403c00c0d0a1050b01d8580405059542d10180e604580360040c003803142d0320501e6129040040000c060510601c6401d000d40100800d4070003806c01c0e41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 570599847 1250 570598597 570598603
    0x306060105070201020129012703060b061c09150b01171308071218060507020112020d181101140318030f0a020d0906030207050a0f06061e080105070905030616020109060c02 76
    0x40c03e108d01143c0348200c4440c08420807104001c040004803a41c2c0501e0b0300f1982c42201030f00d4617a080a4010209200030341c4000300c4503075421099041540d00103001c5495080100004150034181d1840394505400d065407039a200c134400440e03079103008451520f6100d4912001c207015590b100542081000702c0c00b00200011607461008050107681c5182504082c00d1123421a03841030b115500c0071820070001d190055000d1900c03400a511011401802d04800144500980700078803c000030150401e50000200315a140030120b001c13800f0318040c04e1072104031007591060720003e00046440d00a00a90410f141d0040049803007440d004d840e03603911102c550b80301039a11390042c0b10074008907012100101d4040c0c840c1c8280c0e500e09030400700506102030b098503000d5071400300310310a40b80300e515140046040e00401160415507034580000300c020625141442d42110300c041c2c1b40400704030302030204004a40d00080e0302c64008840d0b0003070b10306101d81c001c030590051074100001400ca0b030501103c0a1419004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 570601097 1250 570599847 570599921
    0xa080309070608010807091509050c2805070f260403050616210f11070b0a110403032006070c050d080106051b0c03010f1509020903060601050702010201 67
    0x1440031540041c0d100d00b81900c11100034001e02505a00c190002c1100b040190400d0b850702d40004003c03252240c6803500c07907040d0384044030200100f00780081c90f070741e80c0d4810340c81c3d100720b4555900104c0030a24020200500714800c201014018420341142442804949a400e00075000c41040321441d40945004140003a00a44001d50b194000c150014881000003212006915960703a00c1e10041810703012400e0001d54455400c18a01d80d0b5240c08220248091081d68413007010810401c0d01c80da0140f524140300700c4000c040302002806c0c4080614115101010b41c1c003900d0741410300a400010b180d4100c440c070354102036191102d1281600340107826400011881c250741c000c2d4162040e0410020059850f40e00a10076100050703802c014485c03442c031a10080c80ca00700490f100740c0f8440300349500000c0c2540d20034810b179400c0b2556030001c0300d050f52080740702000500b4840c10540c240950500003035142c00c8024441070500c40c2c002600411a0b00c02e52189141106c4101018008020080e01c0b40e000481 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 570602347 1250 570601097 570601111
    0x9060702073506150a0b040b0f03180d11010b0402160803040503120f04060b1801170307080d0606030b011b03030c09050904050c030c0d020a0b0d09050d020d090e0402060d09080c0a0803 81
    0x425170200e410215441241c1c19103441d01d10356480c1076552041460b407030340300402c0b0010410390050a14443c0d6024400e500039440c0c95502d9480341c450f41508117084170242c0d60642d1040e4410410b1414503030000c1c680c0d1000640101200d0780784d0392039051207400c3d03115094400f510301e044201000b840c4441c414003240198000c000402c40341505006110a0121441150080e10300440040266103180c0040c0d2004d0100c1200b0f590516910359113888480d0050001c456003d0303240e030018070009600d0f00c14408072110900e03000c1c40000d0712641144a240380140044d0030140c40e4100410214040c00b81e17100209805810015586010b08045403110051b030b00c024030074003a40790400044d24003c0007007a0b0703564000f000100303007a24000a0152a610424000d40c03642d4580ba0141c0126405200e12465100a03070054440500b11b154001e115692541004c00d1010100b81070001580703d140c2550034020380c20500140000303c50511907050300820620025070b2042020310810050340700c0c007440c01040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 570603597 1250 570602347 570602359
    0x41518080307170c041e030209040b19090807050c091e0a02070c060e01120b15071703040515010b0f090405070309170702010e040b060f0703030f11030906070207350615 74
    0x500c517846c6481d039191440060350240c4144080350108040ca40303065000307104001c02240b2401000749040607a81d42c9a130a58520b00041100c10500c1000d001c2200414001c6404d0720252401040c00400d44000a04c0c080201d00c5203400510300100c194110b8180581020003012200c1c1e880000401310942204414001381800086040000c0a805040f280b5a801801e09000300b14034101100e00d608041000d40308209420b020100708800d080c005c42c012805140a0720b1144a0303402d04034202201a4046140040c3c01c0001d00080da2940d02a10014181203c01044640341d2801c101c01520030144003400c4c0c1d0003400d506d00801c6881d20010686980700ba00c0b10554080d400382040110785c83d550a16802040800000d45140000c00081c03158500c681000500107002404003000c407161111507500c0800c0020611a841c0d504002840c2d00c1406c0d8801400c03514141018880700b07040c1e003090a070640d102881c1c45955810703900400c1c03044151813030031101c2ca40f608005003801c0b60740681195006030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 570604847 1250 570603597 570603629
    0x120106020c0d020a090b01050906120915070e21011103180a260d0c0c021c02030c0603190e030910020d050307080618040b041518080307170c04 63
    0x42810300b508840150020b0040c40075515180a58000e00711249800303040080c100245910380d03a0f600041c02130b01c42ca502e08401b40785842800310f1300d0106640fa02070382d0f84030030908000c0201e512000c801c414450646012401a26490100d0080111005004119401d00054244d01010900514845d452415920205046c42c0381110744a001d030a0740a0035000c40d94402c85000010798034008170104003031207100d10380301700d021901003280c00a80d010000141950302031000e40c5002c2d0310885650758455000e000300e032450f034006955080d02c00e4419004150200029042c099400c0030a4220003542406125803a10388042c5516580407084036407165001041c800c10302d51000820a0020708180c035250310f140c460710350039514202c00403e03999000302d00100079982aa07580314280c0c096032040b010603085017050701c1c044148014400709491214640f4a1811750102400c0c07113030b240c06810001e580c3d5a900da031102241c0d540490000c05141861100c01c4c0003100000200501c120b035200755210340e80d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 570606097 1250 570604847 570604849
    0x60702060c07030c1b050d0303140f011203030c0e0d1b091e0209031207060b0a090c0903021203040e0c03100618050609220b122409010b0303120106020c 67
    0x280242c00707000c0c002401140820002800600c00210010401801040b40d1996100010040c0c42c00302000c5000a44840b51402d0b4080b2144883d500200d803840594841e41c1000b060b50800144010060708150b120425051018040d040100442c0005000b0076080d0315a410099400da035504030080207120b0030400054144d00038807851031501441c65401d0b029511450b40c90380030b0b40064000a6050081a00403c10f10001c54010035455115440114401103d501000341805143d8031218200e0301b04000100c41b60340c030000640c140d95048074102c0c4410084003040e455401070360401c92401c0d800c4030a00003000c0d000c0d80a90311500400307600042140d25004200c42421001803100b400e03050b0941e017070045141c400c01800520704080e10500c011201183e6005461003907040034001a607032030710811001e0810b0b50004d500e2080800c010a0149410000c031141052038040741458002000041a855074013074114003a51040107084945442440c0c1ca400c43c401300a1150f01c01500c1060000082 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 570607347 1250 570606097 570606121
    0x512071a0306211009030f08070e0307060f03180803040215120417120a06060f0905030618070906060f0905011e080712022722020a03020d0e06070206 66
    0x30905024042c000762011201000003005a81580395180d4004c80480f408041c529100f812610b5019546048a50a25050203020014050301c0781d42003001000c1c0c030440d10344000030742c8011a1580c2c40e00d034240d8100384008600815000300754624100307245402d0320034400c540c03010b5030150340205d40684240640c520745c1d1400b403140040501f0305061071400a000329801202200805115150941c40c00c0740140c1540030000c01190512140c554502e030500c83c1c1c942c0081d00c40759000840c2000b80e507850a0400207540c035000201240030480f4078400c0c104290005210800003030001841c1400f02c9522607001424008524800000041c00100009130035841034031900b090441c0000000c25070b22003800111004003009100800b4084c80c03110740c42440320f06100034010020140d9609009840314407503106c000040340d002d60f10500040c2d1280c14201e01c8004090707403403280c000700107a40b1086004154044e0003170008200b100342c0341c00c22540c03414030b01240b41d0340b003150a6801e40702a507943d220300e102 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 570608597 1250 570607347 570607351
    0x40605060c0a0809040209040c030507020705061e090a050a0303050715061d100816090e0f0618070e010b0c010b0a2d080303420108060a0512071a03 65
    0x101c0350320403071000d004202c0500040909440251000d480d00b0b04010201f4155003e4602c2107001a54641c200602540c1c14404c05002d04400c440300c62801c080d200d80e001001810018075440031a0014501c0c00307690325014614010305d000b034854104203035079080140c4207410114095802804021004800840c14440e42060f119090001a40341c420585907074030840004100054032801d01102241c1c0c0c1504100c0c09070010507181100000505000c0d894003aa02a8100440907038410b0340103036000c80002c915168031101c607890800c001950b045900f480e059195001c0c01d80d401a150010505034064402082040150b000a0100c1403481042c4440c200952080d100b6003101c0e042080c01d240350281d594054401030142401d803242e11106c1190860384160343c0300d04050007070803840d481640e41d00349035100c416112001d0502885079808003400208201045410041850300140d401d954001469010307000c098000006012120040da54403071003130088103034280036010610310415102040764 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 570609847 1250 570608597 570608617
    0x709061406030a0f0b060c030414060306030a020108040c09021303031d0901050f0402040e1303020d090f030f030318060e102016050109030905010f0507021e010e03030c0c04060506 79
    0x151566860000d001d000300b0804c01c001e0b41154581d42469040c2e61190040d1032044034420207180d49500d4140e00180f000105024030307000e01c0d0f040c82002015a0b01042c440c44060f0207007011022a41c0e6403078000051080d60b0801c0000c50702c00b01e2034002107000581d000055a00c01d03124806d1113102803820459140a5100440e0b00c45e02200060080c0d062400d800c0c3c805480141c40035007869100d10b00381c0c0440108590360f03140080020525014180c0c100f0111030402024200700c40420304144504600ca5400d001c040d1a092100c0c1003841003510a0340201017071030b1024080c00f81980d19140c0720014081004001c112489030448030001c0e002d417403007080488920b0f0025200340080d4404902e615403c40c1d2447c1001060300007103000403a03000c2c090040233034840d41d50070100e5820000017522559441240404103c4280302c0c04e8010385807840d0244600c005526140000e5a180c030040382e00380081c00f00941c040c00f0214002002c004c00182c1160360305400c40d406e001d8507407035034144440b5000300204a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 570611097 1250 570609847 570609859
    0x405070501030e0c123a03050408040e0718081504020d0303090209010b1903050408030f1f06030f1109010f030e031201080a140105151c020306010807090614 69
    0x8109641c040d41c045012030f03420300c00340d480c1000603034006010319049031442e0790b081c0c019011808003181550741251141240b000d00e440408020444030f01410f411060300030916581380c01084c2407121010548005006051941c6103030300d04040010407407450071510348c0c241c1c42c0905020824075404036129030600b10401d4521900ea03500d40070041d081c01c80000c1070307007415038945220740036817141340d201c0c2c0c080e1070b551105030303611348030519500e18140d203000c040070806182c0814007002542280c212600009960326044a07a11180c00c1c1e004403081040504d10090300aa10008e00550190170110074200b5402c0200400003050450b0940c038841d5032101c0f0f00040d040815801c143e400707580a207004121540480781000110704055020030402e030028034055011011940401c0080c00c10390400f00701e0340c40240024140001d4080c980d86000c080f852061b065000340925041c41d0340c031500d02c0e16400804030b40042d65a803030400d071030355503901840980c1740c202940455114042543c01c1d914900281c08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 570612347 1250 570611097 570611099
    0x614090c03250e090a03021615030203060f06190305130201080f040816030302070210030606050d0c020c03011103180606031002250c060f03061805060105162108040507 74
    0x200740700d45142c01c0000201d080100100d200441c0000143c0305500b40002000302c41d01e03d050103031034000c48200c0e14003000c1880c06c1c1400410b400e00304945600d181824056120b464510000d1541c550380c081c1c4d203400410100d0000c00707082610400c00215060383c1c80410894440100780020200070600190102e040d01e00401c0b042c1040c002010f9125014030101400c1412008450303500008a0006500107600400c01d10151b18003070880700700700c9040e030804201640c40d0030005459805074024041800395600304408a0b02d0080c0600303900345030010000c00441030711251200090f04242d40c090b01d20410b0060b44180d080c40000c03228001c1d40d00500428180740000e980002960140728295000c000d41034581851380a20540c40e43e2451140e5810441a414060000d21651a01000404050400300104500c1e8103041c00404090710210740420f45980300b60060b1041d104002c0b100d45a0324800c4103582c12b00000a8418a102e6403051084007542000341044480c248150344c0540341b40c0128030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 570613597 1250 570612347 570612373
    0x90c0f0807080a0b06010c050f1501060e01080a020903070306061205010606050c030909220b01060807300b091003030e040c0f030e070b04031103010b120304030807030504050d0614090c03 82
    0x350460380705405140402000f0038640d206410200100b440700150340c0a0102c01c8ac2c4207000110305800340042d07280c058491055040000c00f81c6d40060002005d0a03800240c801c0d050b1000d12440010310f8001d03506100c0ea0750742e041c1d0315045d141114416203541d4a040c601281e014030441c104c0b45145820001141400e0f4484200028804060480c8018040d00201181d403d001800c483e503c007070103583e4001c1290315040000c0c01000300284031204000d8212a2111903c10880c081c0c41c60011054043c1c81d10000107445200070440c0720650ba80c480340041c1003000c00d03d9540c0000702070b01d101c0d6684200002c0c04000303110988540300d0381480862103400300000c6080c4241d01c19000034040c0e00440311103e65801d014126a4420f80060764019004814580541401d01a0803803410341510034003100e0300c000000c4d40c0c03a1b000e140001000d400e000503244050510030000d55000e850000e0035800c0d0b004caa8038020005010440400140c0d90350300001445800002c200c01040d8080030740030304144a1180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 570614847 1250 570613597 570613613
    0x6061d0a1d030711030129030c03011b11010609090f0c0b0a08060f030c0405151e0a0b0a021606030b0f04150504090f0b0142030c12090c0f0807080a 65
    0x10403619090f40da210041440002c69111f2a2201c100b00203c2c6a41c1e1501c09040c98140035000c201c06000340e06028002a03180990040d5401e250400c2c40c1c41c1244510311507106001d45284c3e8400381040c0e003008402c030244819540d10542c2c03544649240005542e640c00316020f640111001c03180030905202c0040c2050400900e441c84500c001800e0316407945902d40000c00f1a00182c0c1c040307030a0b03403580503031407058242016040401c0009800c1c81e0b408408a50004003400002d01541994200114440b40c0c41402001009107604c0a039242100ca41c0d242e060060042c0020020140b040000f0180b10035181440c1c410811070002400044100c10300701814080603003001d01085889030460081003003c5003856074140c0c06400c1d00503103490314010798141d006021403807406601c40c0c0000040c800e0312500651030351a10b50042810f002c20103254092069550300d6a564071b41500034200540003040000c5941044199840ca80c01c20341c03040c0d02c54a010b82c0e201050b015200c40f40d03218644400c0031a483c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 570616097 1250 570614847 570614873
    0xb01090b0d020d050a0209031b21070e1f121205091c05010501030317070815060d0e15010605070816110a120209060d050607080406061d0a1d0307 64
    0x88025181580c03003040c1004913901140c06001e290b0740803c0f01d01d6146024005420001e8910280c54200071001d000074070a4036441120104100e110203410407000400d02c8507030300030205e40e840082c02303241c18844480c80d40c2584001703c0b60300d0184030011421000f0700100040b201d42120390400382e0300101109845c03a40c0300040085e8071a10b440c4000d04a01220158030118030300c070b680040307425491440c2c0a4038104094004034003401c0150204071510764410030301988000849254450010b82e8400304035684100c03903d250a075170a00070324180c048000265040c0e00014140c04100036a42c8078000c07185802040300080140c0f02c10070200803403680844c1001c040c580911843c200c403884080008100320300ca68055002c1e1180780181500b94545201e540c2d03400314055413450039100d0300d6560127071500c90041c4200305014004021506000035076110901030011220360303525680705000944601d50045945000d46400c20040300904500d40c1c040707107c4505e520b001182082080c0d55080c80f52400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 570617347 1250 570616097 570616117
    0x13110d08030a110409020703050c1522061122080303092d01141012080a0c050c06030703150512120703020c0603070c020120030a050702061908070f030b01090b 70
    0x1c01c1c13102003004a500e20007800510f219480300307680c034101210400c1c1890034182070605444640010000c0326005040c2451300895400c500c021509050314022004001c0c0d00307001542d08001160000d82002d15030b00a011585d14030f50680d0f0156611200c07143d9a10003150008121b0300801d6401c411140341d03060000c841003c403c407881d0303031440c40c4141900310781e07450403a5404100300005211004070303910028005400c42422518100ca5980c464480c14441c0070580d404000b500c652032000c0c45001e101c40201d20780000c000e00d0380c0e402c11290040203020340030700c18039184017055400181807500d140068034442111001d42000100a501c21304650051382c421380c2503000e00001145951740300d20080d8410120360325003509841050000511a10320391407119002000e000e038060003a8000002d50740014014501a03544100d28070125841e070240c800382e40c40c41404031500107902c0340c0000002d44680c68030760700d00d5003103030000b03500714295010381103e140070801d060f5040c0321000401c0700400215039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 570618597 1250 570617347 570617381
    0x302070501093504060207210f08191b060b06040f030c09051e2e0306050106080903070b07050d0621020301200f07061413110d08030a 59
    0xc816111818012040704002d40c0c4902241910103800c0702e250164400c2d00c10f1850828106030402d08080d5a030301c5c00e4000c1200394091141c24050b0041180800c0d110f0307a0340200c488152000500e0000c010f60401c0803250042602180d800781140e01c03c000494013800402d280462400c0780303413254001040d14800b6142c105104100c0420308114884a0000651040003032021091925260308101e90700641400c1404a080d11500401d59550040d1908400030346104040c80640c501450040c00300c4a40ca41e04440106100005001c01644030394100d0700240c866044a944010b182e54691144144c024100101c11003c503801901c1080035001c1c640028200290480d180c2c0020303600301c0c0408903025442d130099060582181000c0c058986043d0240030460110402d406019006001d5820341e0149541c010071070384144004c58001950300001c1c24a48111810310700400104192014002d654681104440c0d1440c3c2c20060083c6081e19000fa6855045403203406107171001c5c010300741c03c40203e00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 570619847 1250 570618597 570618611
    0x1020102070209040f1a040201050717130b070b07030501030c09020306030c09090a03090e09101113080303040308060612070f0c02030f0d08010914043918090203030a0302070501 78
    0x3e2210075055000b1401600d00c140e60401e10f103412072040c4500304070b480c58141000706100c0142d8001c4103a444080c1d21404522400e00705811541030b03402052804420300b100144006815000103000340012401b4094010303003540e0701402a41540c0c7d00384002084e50110120402a200d0154013450304210020142da8000d4100c9000a21410090318445580e0300710300f0303d820806400c0542c030802818020003442452a1400d105074942d0509007502044a40b15a141c1010001c05422a9190b0940c0040b10000fa1340380c41c1920341d6501308650441c0414492070203e0914a0108203851a0941e07002c001c800d00c0d913035080304039482d511a0401c1c40503c02e5800b10500142c0e020b01101c144104101c0c010400b00404620062107807006a01c5103441c03924203080e07003402d2403509512a90258200b52440d400c4c212801c03801c2074014150701002d40617a800c026407000720402501e40c0080783c144c0a90030420182c800b0782641143c1074072000030b50580c0300f00b0182c0041402a0090a40c090180c3c0001aa070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 570621097 1250 570619847 570619849
    0x50307031b0f030c14090601020706110705030a03050a1812032a0503031906030b04081308060112030905040203060a0e1305010e0105060307170d1409030a0c05040b01030b1806010201020702 83
    0x100903403c100c40b50000c1e01414080c0c01c806545800911004070b40104039414078100207034a0341403901030107042006000f030351a1446802c100405c01080c5c040c0490394400c155040c0100150001005000024000c03100c010000d80c0c268080700998613030b00d01202c0c0240aa40d029036000d030358000d1100d00aa01c1c1050202202d101e80080c4117464001d81c0035564902d02032080b410350702c0f05060070100e1b60703243c0403040c00440c91880381d003503010340c0c465a0540e84603000500704000864540c09218503100e03600000c00e0b1075041840c4100890700c42d40f00e808016032904100016804211425600001002e50410880002c0031030301c0d800c40c440d464074000782e00c410345480d42910802d83d00c00041d40c2d110750a000c2d00741000c01000c4000c00160040f1448110200400c548030040300000d00c0401400c1100030818588407011145050f400a08441d041111403402002c010640d200d828801c40c80c080c02c6001c2540240245c1d54030003c001c2c00c13810340e0701d60302103140c41d0560082c000e14110341d4207008400c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 570622347 1250 570621097 570621119
    0x60c040b030721050f0a02041206050604110301150806040c0f03110d02120f010e0613020702011b030e04150807030f05010608030a11060114061603141c0510050307031b 74
    0x140d18445180031130a071070100c0000c250918040e00710700700b40d40b04102c10484060002e0b1119107240d84604041001d45454001a0150551002d680340d0710308008000180302c009041410072a98050701d17801c1241d65108100400c40d8a01d8040001240000b000d801030113200b0b44c00043e5000c841c661241c1045401e11040f01260080c40c56810075242c08000c0c00130f003c451034142401071a62005a031a94070b800700100304140040700c01440e1854021503040d0440e03004501080001100c1102d240302030782d90b41001000d1260003190315014524100c49011000b101e04038107030544181c4070007408950328503518114045034104e8195419540d564000c1f8865406000500010207180d0782e00d8500020b011036142084c1d01070307008841c0c100d00801d007804603441c0d890640311611115902e444000d03410f400c00b40c40c0300c00000781810140e100082c00140503c108070080c02c2d41c2100400400441d501c09406680544050151942c0759002d501c0800000760400b12003c04d07006601102204ca60340d800d50107078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 570623597 1250 570622347 570622397
    0x43002030a021006060207030336090b030606100c1a0c2502010c020108090102090904150e0708060604020c0f0d020a151802040c0201200403020909060c040b0307 71
    0x503000010442600c40c2e040000c0c8910b00c004400400401e80f40120103503491a44d84401818000c0c1c40c10308c0403a040d4a5801c41c4560884000346071020480b4044221040d1454010f12500c07529000e5211002d04000034458030a55001d0000300422031400e40503110300d10728400407903010038412030144440c628555001e02034007001c0700d403d456040c08030100c100c114600000391282c2e81c4903894200580e03803000c008180c0580a0811060545544054602a2242c0981c194100a0b03140030b1008102c00808164400c0c4501d01007017140040d9140c0058488a6a00c01d2002d241d0181012407e645032030350040c030003030103060222008002140030315030030908a12000300250308035120300c0003071040c031003a03000140c40d45480822410854440d01c00c08010300900c06401990340701c42c0b105081e4001d50124100740140c09018903c020034026440c0a0b61080c00100d000b03020b22000b00d420705400060710f078094501d00850909150801684102c40c1d0001171038802000f8111003140c1c0201e80d42501f0003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 570624847 1250 570623597 570623693
    0x1d030712030f0c2114070308010f0f05060409021b06010806040302100e031c06180b0406060507020d030c03030b0a0902030f10060905192103091d04 65
    0x840012000d0401034400d0341000440c4081c405081c4081000034104d031004041c00d00d03180d484554540035000e08881003032002e99110305509000030500305141d044081e00e4102c403202c0c07180b80121a1104040b0315441c49601c11141c100c2018401488000440d4015022000501584040c0c0c10a4800180d1401c00300381d00281054000c0d03030030720091590601107405420012241030040029642c04141d50b403140d004e80f0040c00c0640c2d041982ca40401d90014001054090707030310b09108406583c041c004003042e000c0140706502d0b090001a00c540104d0645085903002820001c9117519500c00362a03141356190304504055461581e01c0740781e69000f49140192180c07400042e120718001c0b41c445a4410701402e08407a80fa072100c010010194441541400e841e001c0c2c03002d1100b0014440c410302001070f181c000c07071030f03400d4140b94000980c00c02040641c0d14600a56861803003a43d074101116041702000e001e801d01840d82d40000700130441e0440028003084140601d11404814011581510403821030f0b98 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 570626097 1250 570624847 570624869
    0x7020a23030102071a040f1523090706050d1803030519060e01180608010e011b0306060503010b07030c0f1401060501050309071403030f0d0b01030609050f01061d0307 73
    0xd9024a004056a80541041680210300e40100c1e0344502290251480305070260b0708040d80060108036184054034540d6a0000410806264000c60300001c1c180c034401241d038803244105c0141146011006141c040d480d0400608401e07800c0c4a81140d4682c40b135121100f80c95100d10071548403040051681c80001d0280c4d500250506124883e00c02c01c807182c080602045052000500c11030441c900100d045411032040d010b500d80c030585807500034000c1c9622050446d481d2401840c7c01010640080f80c01a14000d00f0101035000c02406408a400b94091b00c0b001550610041c4a4004000000c002460080c104130359403140964031128426000801141e1070a980380c0550882e803000d00031a4090304003420101d0852800510302d5070b41c0c94451242c3c20304a4401e04400040382c81c18808c50b071a03011761100055551401400802c00744c450b0800c0c1c940042c1c90810f00040e90754452051034061896059070700c640740d107010300445441e040020040e41e00000040241040e80c0d0400040c00144029242 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 570627347 1250 570626097 570626129
    0x3070803090106033f030e06090c090906010627030203190611092206080d050304050c040b21030f21070f0903121209050309030708030a0c0206030c07020a 68
    0x2000e6440e00c080a824031405d2014040102820660620b4039501e44c5401c0c207810400ca20414100c02074054213482d810035028203802e210403d0700100d4110410102079402800640320b1100311075641109101e86800540350200304040340000d90041021200140000b0200300e407242c0001c0d00700b121180c500350840e1442c002c941c0401c00340340500144000e06940ca6402c04c3d881d500850ba5807902d09600c03940240c901c007140d0101c40100d82c400e030060722843c01101e88002000f140a061640151800e44403449030f1004410680380c14040c2c40e125200180c5043da1880f503192a110303560200480070241c41c0401c0c000120b2802d905c9004e044c041c851074407008403c080900c507100d48044040c0500301005130710004889040d4100a000003201d42c040091145c400e0310300000c88803000028200c620300c078103207040c000c14404000041d0240380d00c100c081d03030841036513040c60320340c2c0c0e03c162083e960104040d91a040301514199005c0c0d5888901a46500c3c502141ca43c0041c0105200da0021452440f0b0208c07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 570628597 1250 570627347 570627353
    0xc0803010603021c050c0702190801050415050f070507060507271a071e060603080f04080d0f1418040e0a0c06030501030c090b0f1306140306040b13050307080309010603 74
    0x80542c044881c0c50000c10103401c00340301c0c03a040c2d40b24107880a4021060044e03072740d032031114003203000000b803000c0e0340204400d00307142c60801c14191400e41010705460819000c204803500c41304c4000c2c002c0010352a00d903c2e0850350364411010f4000106104144045007141c012403080c10384c0340b40c80004100759031101c1d483c1082c0c071701c50740c0860403016403900150a000c450000361a07012090000c0c04140304590101d0441d117408406030080d500002c045480118100851504a4010300251913410090742c60086016030200c8812403441d011100158180000c02c0e0211080c0009188411494a80d00511442c4c0404181903d00107c48080164000c0c1045000e02130b07000d12807030140140e46000c1c070640d403558554000e04d0901e03003e420181da80d500380c4000c882d980c4e400c0682481c54044e259807002000c4c2c0c3c2e84d0000409652041c04440380340422484041c4c900450024411a40f001200302a40ca6000040045110000c1d00b2522440200a4040410400406035114000c20800800e406c1c0c1985 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 570629847 1250 570628597 570628627
    0x9050f010623040b0a081005040212190201051815041a03090a02041e090f030306080d09031103190501050108070f030b0a05041119030b062407030c080301060302 71
    0x3902a1071000503a14102200c4444032038490240d8008a4000c104c2d21421400179000d01402c0d4800c95140c03180601d000944030142e08800d108074021a120049144041a85c9845495134103414107040300f04d10041c001503020b200502001c4a030300c0454102e0200f9200440c000c445001b600084a900c00301d01003081e01241004a0404035101c04028194107103e04050303900c0c3c1c10100000d2090362a41a22915031842d14061795910003204030520040f180c40c01c022801d504584020380029007003040200e101040090703526454001645e40d809800d10319101d00d0b0701100b81410045c4e050007640640400780200003140c0c009503010314000240d652401c40c24034500101944604968103980d034041000c25102021103900c405254004246071f5a40d10f007204100b041120402d138011b0301c00307903010028100d000c1080c0030340f48a841d076032490f610703200d0401c0840358008805890010301c499a401070222580d0182c01401c0c0321b4240100441c0c0507030b4485140e42c000360082c0b40000da02203605021168a2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 570631097 1250 570629847 570629849
    0x6131104230102070302031905120304081309110403060506030a080a11060114010c030509030c130b0310020f0702120f0717160612110904020307031d0c0d060504031209050f0106 78
    0xf400200842c0346180d01003902c0b0950088000040c0c0d5842400c070341440300c24481d405520380210641c80e500c0c82e1a01d4803035540d030040d80300c14503041302200000c00c007000a4803400c45a0103010441c03034100f501d103036107482c050080104181d416004e07902140340001c2d0300c4005000b01c203001d0340350390b000807030401c00a61030640143c0c0711032580a280c070b1024607030780d030040d848003201d50705441c02c02d5850300e281004c00d00c1d114195181c141c110242c07903010070004040358041d501107607045043d142c001c00004040416405100c40c204a8644108901d00051520000020310217001000f0343d803241c1c8400c0000d50030070340d1907407110031000710032141e00d0300c00d2109004180000310101c0c600758550741001e4005203910144090910301c280d40799020220050020180c03040c0400081056559240600c0001c02602c00c6010590b0b51400310750010101d01004940d00f18010409001813140500948039170001c1d05020788140c0c18005003240505521405010f40c0e4422805a8000c00e03e104181c9507140c03c403051 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 570632347 1250 570631097 570631099
    0xf0414010603061d1e04030309020d0b1603110f0c160806252304030c1e0b04030803060d08070203030c060708060607020918030f0d060f06050c03030613110423 70
    0x7412017048801c0302044d6044624103400c070042042c994807440c080c2c0c010551824040c0d880b05804407080c0400410100e40d92244124040c1c0105080c038a40003039041d1004c1e003020b2542d21005100d48400700c00780c40054502c0c0c2803040104e0b00b440c1e113008034240380098030b50031420054114000704050b1001030300808010100b80701c581316110342d4a00005140300b0307a950042d5500d10029000d210340c00d045000b52005107401109000c1c585a0700c0c100503a0040441c041d1101c5111009170010b110113282c01030b01c084a8000082e1071442d500c84003041103003a42c1041c01c68102405000443c0981c500700043e03d00555604c00515150500c0000030701000b5006084c144200810001c070401030300e40010306c6802c41654004001c0c021000d56819003940120703540d074080700c540402d0725104e0a0355038020703604458100d00358448003510340804407120711903074080d0002c0d9402040480c0590405040c00704200030000c2e40098600c01e00030303a500c0541d002d40d000c5c1440801c04003d00d0042c140f01e07190410b075010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 570633597 1250 570632347 570632399
    0x40b0c010b04061d0f06130e0f010605180708070201270204050105060310030609021c12110313050618091603051503060417070b0c0a120e06060f041401060306 70
    0x9140e41c4d440c60b610000340464450308124001c00c1d5145c1350100b002142840041c820712140200c010707402d9880d074403140024051760900100051174100025220081c03d03401001180c696100c560a41c0c400d400a8444021503581c0c3c840e40b070100c804040c2070801c6d0540c101c003842c14100a0700410041c0c1d0303c1070b000684540c10800038041c20701001180c16003125804040440c814003940001844100040c2c0a00c031100c020701325a00420660300b164000b41c0c2c11035104c90200117207041070a40d4900524466260314034100005002a00e0410701801812004041211041c14464085440c040e42541c1c4400303602043d440c50507229805008944d031000b440030101104046003000295203100141c80a0912049643d8000400c21407404480d00b094001013800c003c3c1c02c0c80c648c080500c0e0b100c04904d600280d01000b01c000c6800c045c0c000e02425502d0600240140d072150f0007002042450041c031150300c1940e0b0700d03104050002940880380240121b840000c6c55502e001d44519201b00041001d1022103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 570634847 1250 570633597 570633629
    0x1a010e0603060c041202060909100314060c0706050910140702210403030c230a06050c03071409030304031b0503010b0303070b070804020a09050f040606050a06050904020f040b0c010b0406 82
    0x10f030210507030301101d680c400c0070500c02c1043e00200b4094401c070301100e900300119100704820113541c0109001228401c00b0052800d00340c985091f0384504080c0d07031042c0c002c0c8003089440c01081c855001160000051420383e00f8142c0d40a0030401150140e0b42c801c0e8658040404110700349805002d0489141048000450203120f80d075030541032445035010040920860802c1101445249140300d4591150040e50031031080c1d02052469592059500440e40242008006000e100080c4281e074010704081d114103514a50449280d2002e401603014141c25100500001000c6a9035404081481100301c0c40c0102c5203042401b41401c0d201c0c5d00720068040e6104000500004084004295000c00c0510b8204500e0b1200e00c0018a8800d03198845d020840c00c0401b8032100d00500e0381c0e864012445103400f0031405985006003c04c1d12858410400070034002e20084206007059002010340c801200001d900c1d05454001480c111327085480d6021190b952035006444c00d007440d01c619070140980311100f603448 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 570636097 1250 570634847 570634861
    0x70611150c0a0201110d05090106060c02031e0c0301091103070e1e04170406030b13050907090213030b070903170405090a0c020c1c0b01090203070e060c0a1a010e060306 74
    0x240c0c003030315a503001100042d04281c982d100703501c4148078107000710203d9a101800c40155000c2c10050f10743c5c940c554a0544002400c5000f14905001d041c1e01802400e054640d0344c41200e40032000c4418940b490040780082c0155690a00c03551207542d10501c4103065825188d81410b103011619002008000b070f1000031b000410b000c0442c14001c0860301c13a03113600300e5521450b10851400104000000d003420101c0c01280d03058158000e0030402009549000041524441c1817040d94415120110720340c10183d414003000e0300b650020f2030342d10b648520407512141d50340d49000c603100b003c45614000607201003040c01003101c00700e14003d01d60704c0303841c4003420903040400207030f111308002e00001403080c2d8600d0003030035050007405000c180d244010300c80c54191a40d0006003040e8001c02204503507a42e185400800d4401741442600d00600b41580d51040c01e40007081070140700e034800c0d02e5185952003151090000590791602240d00300c2c10348a02c00000d0b51620072080b000100107000d49109411074400c010130 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 570637347 1250 570636097 570636133
    0x2180c12180a02240a050406030b030c01080a1107050a0503090108150108010b0d09051e0115081216061a040506040b09040602130e01030f0b06100c2909070611 70
    0x807a404031568496131003080c0c201c800811684040c2041204041503184c1c441c0d800c0009032003281c03869107081c8000d500d1902016240d1018407107490101f00e4020114422035400e9000d008002e41104406240c1415034803400e01d0824202030488141c2d000180d03140087d41d1010206400005510003095a00b801000113068031205001d580b2100d880880d8502c2c215600c1e0300704100b1603402000b6508141c58140e03540014080440402c6940d600740410400c2d07042100701d5840442d0503c4001e0041c414021014207550b40c4080201600c004212010401190f0140301310710b002d19440d00440303a00d600d43d1050000f5688002c040314400c0345412483c08140c1c4644042d2030740550b0040c8010713030302c008800d1900b61400d2203401105418000300b00200400020270245004940180c13007401982c3d941c40c042220408038603001d88001510920304000240307009002800040300c0c40401010b03040d01803d03400f906101140c102d1200d501130442000083e0301300901c2007076617201030040c0c800c01480c10302c0004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 570638597 1250 570637347 570637363
    0x904050307020913080315010806120303180705190918030e04111b0a05250603090501111c0c050405011b0219080f0c0420030402180c1218 61
    0x101071400c1100050741113400505080388503900042c1d1035120305022a004915460965a00340881c0350400401c07800d103401e160088402c80d5590046246a03140900d08441101d90003010180d40728100703021800f82d40e0b859809100c030321444003a100f240e00e01003070031040d1a900c25100024482c40c1002c0008079034014010410030800342c902051003801d01214203100d10500405500c80d035002c005924289001040f00198180503400b111050b80701c856404420417607200b43e45010703440d107440410200b03000343c2004400c58010000040c0148224600785440c5d48403440b018051415400c6131a0004030500c180102440355160260902e400c101c006403000780c07480c1d840c03c03000d98010142300c01c540e00c0c0500d030b43c2d00f00301d0b0401d448403c542c0c50100b1036580c2c8070311100d06440e025901e5020041d0402e480703504054888000d500100301d065004c140510b17800500240d03000750b020325401e203c00b000e0316405401290201405a0f880d0007943c001803035000041c103020140d00455580741c2d008503002602d44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 570639847 1250 570638597 570638599
    0xf19030f060506041509030b18101b0c060207060203070e100801030b0601050c030405040e0f100c0503131a010303020c040e070b03040206031305101a1906080702071a030402030c090405030702 84
    0xa01781c840300303007015a51404564002400030418008008a4242e00000025405003800480b0b4014000c070183c40b09850030002c1e1140c94041c07000709600424070800c01c43c90040e028010040c030f841031640b10801641d01c110f03001404190044045003150802e492195250f4400345400201d95046640755810503102500041c1006004205031040c00002c0c4211401440010720800c9a08100c100305622000201014038280c041e10014100c10302c410301034100c0701400c07a590710380796580d603118042c01d009040744291400c2400b1041c40d080c188004000314003840c000c5e001802c42c0d81002c4100405c1d6541c80c0700251403600f0047c002c101c01e10407103041e2600194100d8195842c0da446104200c00c1540c0b8000c060070300e10407241002c0c184180d5501c0700b0a034485c100c181091144540090100280119032507940810f5a40420010a4803c000c1e40b83c2000c200c0c4190358249a81d00002c01c200900c09091104e40403000092104500e0f0800501074040d4055403d01c1192605858a5407a8000c112020b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 570641097 1250 570639847 570639869
    0x1f11030301231806060c1623060c070303080c19090f0f062a051605040b09070c12030e0307080c010b03010905030f0702130f050a0507020303060604030f080f19030f06050604 76
    0x32506d0110103001104802c1040c48480309502d42e13514407004080140c80302d4012241504140307207058144001203485028404008100c4a803455038212103407000200a60002030050000c004c841d401692101e00b101c04c80d569040c0140d0030021031800e480380c0c41d401112a82c6111a080040c00c1e085440044002c9952126844100007800031715a0700d0035900c1c0062031030042c1100450303412000f035921002c1c0c61082d034081003d00c00040901c101c551041d52518081107050a080340010140741c6c4d44001d00d0307280c1c43d0202e40c103103003011114a550000001124241c3d004102c007001c1280903c60603003603a01c218000e100c0e0072900e40311207880f48100740d09149460f500040001c2035498840d440303540302e40710b4001041811542c0c0302040c0100400c1c0c0d00f900380c6500300808542503500c0042500e00800e001420a45001c0c6180da560702c03030b44551042202c0c503e00074010402402c0c034000107480806460034002400100109004045400304c01c6083e10072494101d0911a075164001990143c0e07010040c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 570642347 1250 570641097 570641107
    0x8061b0328022116030506010e0909010b03030408150906010501080403050a03060f06052203020603160e061b070608090607030c3c0504051f1103030123180606 70
    0x100784041d02c01d401014400b650800e14440f29584081e140ea031055000b102000e5543c03103420021002d41d40166001c9001851000c03e80c0c8052411049003078108010400000e800000100803d045401c182d10120543c0c2003680380091103540041003a90140450001d04450343c14000060f1140318050700c081c0400c400421007a817540c0c0250702000140000040c286825a6100c0004119500504080b481010f05500380031004041e1527255041c0da030700918140c10360352921000c0d20000713034194649080000c95048220a40c6804000b043c0c0344e51700001c0241a01c2601a00c68548180c590102042224110400502003000b00300c0a4100c070642c540464640c100c4501283d41440c4e400446c411000d403241400900944c100358a0315496040044040c00354600100f60340c00c0c0036501c0b41a404c04181c0c0c0541c0c49010744104503010812a03428160090710b00f4903c69444c5420036080700500e0011904049429945040c582200d407004949100e504110403182004c0b828001e0001c60040307001040d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 570643597 1250 570642347 570642421
    0x40803010e06243c0c010204030821090a03020c0103051506030702072409170312040605010612110910211401140303070f020f090108061b03 62
    0x503010036201407034100582c1401e001040324803994410450081c003030700a15040d2003040c0341c070120550110001007074118030955000304c10700f882c0d104803440040c55508000100020f4040c0b00502100411000c01510704240c0781075407106040d0250907000380e58000050200040e41c00100e1880c3d80500307184c040707595220b4a8034007002488920700ba5a000d00c0101c00c1214090740041c80104072544805000c1644034512043c5031419042d04c145000200b44160501c06d000d04841c1071580c4200400031a441c1c0880100400741c83d2106490031540d8a0b200c81c0100002940944840501c0c5002d2604000340e407010052030751140300b40301034203000318103020320300e12054014260380b40400f990982c05801e800b134502c00301004040b209403200800c080b0710004244160304240c8100442c0018004501e070680ba9120100c021a5904041349c1c04651b480d4424040d85998689900a020400c001c016605003203440c080442c40300f0104141c24002031042150300b00c074814010401080d941513450749410792407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 570644847 1250 570643597 570643609
    0xd0201060e0403031107021c05070e09030d02071a01060c030206012106090204110c0109020301110a2109020402040306090204050f0609011206151d07020106030809090c160b071403040803010e06 85
    0x1c60040e42c403441080000c0e0361413400c8c04841d130109101d0010b903040c4076100c1c090300c0000300c0300380c03007508481d0302c24003400281c0352440c0d008200c0785005000e16888540101840d2003441d0742600001c0000f42014040004c150b010840c441c050000000e400102e1884400510105013805401400c0603031030341100b406544444d40300006020507111403580c7c448543c040140a028030301c004038020340ca1300202030203034884402600c001100c10f40e01c50510f0f501c134210900580d2051143c00d10103e030b0b500c030140c0041e5070b284001c20085102d1140465100b44500422045410040503201c0301c80d1044100481a40d680e41628159070700002108e408140034101a0010310a4036801c65030718034440d02c00300d040040348548011512070440b48181c01d5a402030103e00781c41c0d0714480142541400e003e5541c02e45015142554440940c48032582080d4030048009070321540c0e5401a2800611002402410b50744000204450344031010064510300306581d426800e44414400c0d0340d10810414003240c8250ba8030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 570646097 1250 570644847 570644857
    0xd08071e170f1504060305030901180803040e0703050106020606150a0203070f05010b040c1d1c020907030e01050a061202040b04091a06013b010504090e030c0d0201060e04030311 78
    0xd000080007510b48054600001e64090340c020441d041400c901e95a1440d0901036207069036070120203941800b803031130f0056070411401e0044002000d02d2100100700c0700c2081010f4802416a01202c5016013004a009000c81c0c43c10303001002150811403c2211139140c2c103114980b1108442c250b9903076179907440c02c1242103000303a030401882204a400c4c94030034040150881400030200b00c9003042154405075013a61004c0d11400015041c0005200038101c034078000e0100c001400041c642c129041070075030b0024079500750441e00700010a9840c2c0f88410a5102442140d03405030264404004032070030a44140703940c03500010001d00c62901c1d4400701c2c0c12078445070000545a03511407218002c915041c6c20f103901c000002c690850005003c070084900b11150340c6c54090300c0340c044156601c4090281e107282005140380c40d2049061000030072000a940c101307072140500d1654400040e60702c034181903403440e013410031401c3c00c8800c580c1080e03014070050101445050704581c1c141000a0000c0900104803168015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 570647347 1250 570646097 570646127
    0x5010f0503181e030702030c01031401090e0c1002010c111906020309030c03300408041205011512020a0906031a040624170a120c020102210c0d08071e 66
    0xc12512152000004c050241e0a00c00c4003600d4031a1140001101114010a8003000880c0c4c0180100640704540e80802000441102a204480844000303e581d0381c00155004006039540d00400c0e86503a8404411418840c4010140000d46440b02c03162142c2c01d140031024007010303800004219a0101013048400444021042c0c0f41c07074541c0f62062a00203010480680c2580180c2c0740c00210201c04030316214499607110f2203550034981000e40c51040402d0807001104c01d9940d80c01019003920342c55516070001c000c6400b4002d140d42581c414846440741a500429503281094802d100040e0301c014200c00c80a807000c2481c40c50b031707141d06180c0080c204c00c84c580281040750746410840b9609101c0824180c0340819800d50701d0070042001f4a0f6110180103000e82030401e4040c501c40e0700361003000703038800960052040b54441030740741c0d903d25031000900203115155140082c0514404009124400c0c14141a08241705c5614082002901520940d260703140028038603400009664050201100d00f414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 570648597 1250 570647347 570647383
    0xe07030b040305130e0601050d0b01020309091807050114090d240b012c04020a050c10020a020c0102031312151d070510050d0b0a0b0a0807080105010f050318 69
    0x140342c180940154098100d66400c002c42c54000300e440c1810880940c010101031352800d14010741682c40d031006050107080c01d030441c0010416200d1954604410030702424030f050700c6203d20000f000c1e915203492140c0e8000e6062150705041c150340310958205503480b41c1416150000d8803d414a084200d5945e0720180d03a030240a80380c45514003c000d54440d2040314020f0300c408118034808d2440341c0b115190388448000061011b202e05c022800c0075006040542d9442c00c140d420241070080d0b603410024401424207045501051100c40d080e07042200500642082c00554902500c004a00f601d9180d10700600140c8401d0200560070051003090711545030b180361100b0400c00420303818050303048520a210381b00c80c1c0701d0300070040f84030b181c9a14000030407400da4942c5481c0222040303214000d005c0510a0b25480107a1010000c6d408040718024083c001481d91000e0040c0740003080900300c24010b03000136040220802c01740a220340c00c80c0489400c0300c4031291000c0c505131a64106d1b071a0004600d482d8030900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 570649847 1250 570648597 570648601
    0x180b030f010f050c0903031c0615080a0605060f2d0a0804030806012c030f0f030d060905012102040e070609091a09042d140f0c10030e07030b 62
    0x300040d482005041c400c400280680d07101c0581c541c1c041c0c0035580b4041e6041d0800c11054003c1510002160004401030001061140d50350800e841006d40104903140451102d42c02c002c0b0408107882150040e00b0704071500303401c1c0702800404c4140c80c00380c0e81c400003924560081d8004842e0040c490210000759071540d51ba03862680c1c9000903c0c105007606e0440c08a45500f0124cd825030290700c0310094011840640500d8080302146500f02c1260100050f4060041d85c1c500345080400340601d030040c003214002595204140c41c0700f6000c50b00a0307406130044d64680700061202c4280e4402103658041c0c40c49009025a1072800003074001e010903600003807144a480000202550854030303072422600846020050b0324120400d42e51240c9100c0d404940c040b1300e0f1400100001c52403020600c5801c2040e034041c40215181500c62a050600c95098403841040e6211403410103040000064041d010b070060001040c1d0a40410703426100881d01c14181615444e80d1034405100b00042c20080d60001c0385510f00d8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 570651097 1250 570649847 570649873
    0x7020a020d0c0306290415051008070206150a03060902060d060602010507110c181312031e0e0714060f07060b0405061504060503071b030207060f030c0504180b03 71
    0x40c0119100840e1110305101038545c88102c5130a0702c40380d40e16000b504c48018540101000020401303804459070320080c0e13078804206034503244065000702c400c588440e0003504100002901e0100c005119410440c0d1400002c607441d120140c0e20000c4036030040700880c0d1001d10344005030240c0509524049030520709600010002d6054002c107010b030800ba11911142a000301140d41c03a15049200d41d504070701c101850709038904035119456846171820300d04901d94010307590303000340d00b07821000d0f1000006c0d01d030301c8649500600c2d03040d44081c1e04100c0754100840403030204519110006803040003900c1d0049141c01c062174860504071800180c0310b25002c0e5845000341b070000020301404201c0ca0140d41f402c00020031b0341c1000b8820f68541c1800c003034081c0c2040c2c40d000c41120303550720003482c0c00100014070300090000e005400d411444103201350040c00c941c07800c0420046c41c3d00d40482d104030405003414011100702d900b110854050743c07003000480c14207250150310700010f804c0e4041c1c42505031180740446405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 570652347 1250 570651097 570651113
    0xc030e061b01050f0a0209060405150f0a020d090b032202031f0914010c05030f09100606120c0912030c14060106180608010e0f041406010b0a110304061707020a020d 72
    0x1080d00310300d441d400240c172003408120490140e11241600110200000c0c04a45401c0c120160040700800d0182d2400d458082198000d8105100f00009a8048074521041c2904030bc100b05c060484070040c14250328020a005c49400070310035028200c8800d104c145400d42d1800d10494030041e040020300b52501e181c4a84d044001c00344404181c2e06510403c82007104080c060040c07880c815280c3d540d003800c2d034403070402d90500c00070040c1c12150148140d418601a00489026030001004941c07541300c9103c54041210042d100004035001c00c1200b10700d814446100031a240c441040c0e014607003499200901d1500b515022901507408916105510000a609501c4885222030b11200c1507080103031641c49200340d80050084c0500c02418a40d14001808440b119a103564014060001e200400400e8a0311608120080e0040111084005004002c40745c2000d440c00300b0400d914011407a061505030000c14840400400210114400003c80d4241d8420010b4034150b035001006003941c031701d081c90a045 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 570653597 1250 570652347 570652351
    0x10f0f0e0f04020f040801200f18040f0906050601090602120a0c050304080715020c0f1e1e0a080606030c0114040f150e09040c290d09060b100c030e061b0105 69
    0x440c1f513081002e2041464038038211100c4609114913041d080590521800c98580c009859030940c0c540300e420304555940d0f841c0034a51800c00700d0400000c104a90b4180032064070402130045051000d60300c810010303e0742c0080d03c154004088240c103511361004040488403500380b00009080e6100124020510342004140c0300d04a0b4000380d54500d0505110406a0304c641100046aa00260700c15044520f410f05e280510300583c2c0241c0c0c443c072007512400c0010984c000301d851008612050302e5040c0c115080200c0413a02a1a0040061941d171602a00086c0d0360342c1c1001c00641046041d0140c81901310b889002e0304c029150002604052a80b66079a210b203c4040120a0000a0740018104203074101307080d005001d550480d05225010741080002d01d046001c9103c55400900580640c1044043e01405070141600100011481c0c502c1c60600350b0030794500c198940d1203110110003402203590403001c4400c6055041c144018105403140000e81c4902981c11001035000100f9401e051118040d40301c54 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 570654847 1250 570653597 570653609
    0x9090405010c0905150a0513030501020c1006080703050307020d0f1e212c0a090605210a0b1f09140711120d06030204110c0c010f0f0e0f04020f04 64
    0xb607583c595860030040058140303d40d094003048108003001c43d080c030031001410b5400002400140305660b0350b90700340c01c90348000c07500e12890b004400c00408400a60042c0801404e05070001c0c1a4203085807103082c0c480c441d49000a114072000304070f0108100411000c000070743e4120400001c14171425595841d0340302903250840745081d40c10788040401000d00c8034030100c03156903543e42509424580c01c0c040000464440b040c60108034401c0d11140355a4110b448000c0d2100c0715010954030304e8203003801750129240769007001c1030071000e00c070307415a0b54009408a000364000c0c08040c4141c49400100d28001c03c801c50344a9070041000d07004c00c44d8001d90b0020412015020040e400c80c0c1d8810500700e401c520b410b08000b1044d0031401a800c81d802a003000790070400c0c020301000802c180d403940010f04a81188040019501011501d0711500005100303880d002e0000b801c1000b583c200020004000250304040c0b00180070004520b4905c80e100c0390f0007408000c0000e0720441d908c01c0d02e80d085086030b070002d11440d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 570656097 1250 570654847 570654857
    0x70c030503131d040f030804050a05010e030903071202061e0d0f090b0603060613090503120a06150c02090a0e010e010504034a130207061505190902030c09090405010c 73
    0x50300d00f0042024090720803900118400180021543c08a81d480c0000d00186e03003903c9039401c0703900860001e1060003500c1510000450340c1e80b070003105150600c1c00341d81c010305282300c480001601517260a411a080380540800c2001c1c2e8030030040c040c00403030017041034202ca00d40c98032681c2880074410b544803e82050003284107100340c0d9030741400c243e5203001c2219450b800c201040040500304130300d030300b01020342e43c480d4003501d0a150294210502c0048200d4181594548440040099a071503210f000740e0002140b170039504000300d80e00421900c1d0006052089059070b03801650084000a610100114800c42e00038019030901e410000c0400710444200303290b41650b002c00181154040c4003001c0d103001c542004d02c0c41740c40c4503604408011325141030250800a120360b81103551440d48018541c56200782400110000b02c0b010039840d0240f5604510f000d11800d1004000d81000c0c0c000b0700040b40c100c1c0c2c0d00544e81340e4a0540340740e4030b40241441389801a508a00380420008190001d840030640f50b912 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 570657347 1250 570656097 570656129
    0x90a060b0402130506090607170306010306290a09050402070b0f0a090b040605070311130312111507091a1c020a0c0f020303040e011e080c01090902070c03050313 71
    0xc000880c440d22007203e01d0321241035800c11080c01d00320054040548000c110324104002910340c00c447c099900400300d8501030010800480e9a01449454041c02c03400e508422540c0b8001c80a58420b642e6600500e013005022810300c5101d031040c03c403240507041c064825511205a8074001120505c140c8200309881803107400615801803910420a2707194000180d06461f40307458803040300030f101c00b41c061403c242c0c80380398248040b00d400c0700920007809080d030b000d28614a1800c2c402142c1642c050000b08003c912034000240758400160b41c10680d40501c0e4440c0306442d0f20348143ca81000603800400c5848404510400e0000c0c00c0c0007400c0d4240090007131031001d111f0f2800e41c0040f841922090b20228000041e40400b1030b03450300800c10002d1010b012a032829860b03004c84a2400c034240d0000e18601d01c1022426009041c159550f80140318a1004180304030190001804080d241c0c0109913410780d010400c1c0c418040085100c800850b007007010789035201601c414911054216000d05184c1900e1900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 570658597 1250 570657347 570657349
    0x2704020f0306070c140a0b070809070503060115210c020309040e030f0714070e040b220c06120f0204030501050f0c0c03040302040c020a0b010807050a090e06010905091203090a060b 79
    0xb400d944181459910405555100d564040c407080d6592203c3c000761160350304072400180311a860711b0190240340c68800300381c94a040318614205081d044103010390807110040100b5828006003208250741401c116006c00c004598440040300c21000e50704030903040c030f15031959154000c4020006c0400658080c0f02c01c5400c50403403680c03481114400f1150402c00c02c00e5601046014400c580c21070950819221b0459440c00000b550311004d690030703a80c030300782141400200c2401421510039585248405480f5000c4c54070707000e603181c1c901e106180c00d101c614400202070241c5c640c02208159a8a43d04640b030315124148280200004c1319620460076444000c144200c6c04902554484400d91000310700e000e0866003031101a00d42d4003d004158802c0480403000180c0b042c0810380604143c00091054910300010002d518840d50700c072407030482c9440714688030128003088541c195010100007180c2c40e101c444103540b900601d408600d68496010041c0325210303c0214841d05c1850148006008100d4520 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 570659847 1250 570658597 570658603
    0xb0307030c260d0e12070b13060e010c0201030c030603021512101818020619020106061b062721050901050712090f030c05101b112704020f03 62
    0x7028280079584102c40320301c1020720810213044200c81c0645404040004d850b5464a020031326003140c816540c002ca040d5280201c410145001064507103421080700b954900068848001414040d04140d150130030a444580a500090011540a000b12220305007881c0000c012303410200c6100c140d51084008208400390b41058070b41603591907035404403005010b40200b8001e000111080b0000c0b150381c0244e80140e511100900001c12107003520045014140390000d0860b405a04084240050302402d202500c0c03500a05a884680c0103800081c0200c500f001c0d00603000d00d22008014046041d900001041461041c8841030b049581c59100300301c1020009443e43c0c0174850171140090b60510008020407411a4901c1d0b001e90b040c14003100e15502d1701c0c914105039110303801c265000b0000c0321040006080441d5052194162450004201c03c0d4401c26224070f0086000b001c3c3c42c1101070000180a90f9541551064075417401250010780700500440c00c820110843e0283e1090b0b9444841136000d007004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 570661097 1250 570659847 570659909
    0x1d061906050310020d060b0703030b0316120b04080f0310080d080c070b060f0a06020f190b1b0f0417150c03070309031e05040e0108010c02060a09060b0307030c 70
    0x20b001e00908031004400070001e400a0101c8810b2648890002400400900c000e100b00750181c0d801080000c1040141450656404100441c100d12021b0400c0000300c500182486254004c03081701d225200c80c00c0c480ac460042c41d04030f00300e00d94000280300079001c605000b40f00b181c512009891192b031650b14240da180104807440c100306c0c039003044404005000d0560036540003200500015004610b0004181da02c0c00381d40180c40960310580c4441c0700d1480420605124200ba401510902c510b15580d680309100050401e00807100c2313140310b44001c6080001520064166600503d4840760344607d00c0583c1c0d180942c8001030b501034801c0c0203500003d00c0f0b0380c0c44c0c03048031600d10703051554a0354503084004000c800415000c10034403500051030346140c50520068103010341d481d1511241056102c3c1c0404c00e045c2d01140c00d81e031600150014075600424107030751000c150b00000990142c1800d09101030040046c800f0340c140035400c004420000c164a48100340c400d00c01641030106640c002120b891105 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 570662347 1250 570661097 570661099
    0x9190603020c2b0c020315091006080a110609210706030e0a02010f0f0e03030705010501092901030c170709090b040225020321030402130219080a1d06190605 69
    0x1000d44071000f9900444000480a2010701142d80c540c00703c405018888005540c0703030700180c00490026540903c240030f8240030b803c1c403401414407011169241100305d031420807040d00412021411206942d221055079100c0d80c240d020710b030741850602c1c2c074842c0c13618410b0007840003081c03900515000c25000022810350340d550685500002c9403001c0420b0b1244546800d445042200d8903010130500d4900f4005417600c0e03449000086803550500c0665020307101c0b03c41c82c6001143d5418030301914002c00c9140052001804e0800280c1a00b59090848000b8140300d0303054290494078051012155020030000200c640031281000303d00b0607041040706030f1140100220301c0d40c0100e80c01a0281380140c1d240701250340300400f110f18040c650304101c40154101401d170321038580048204025424004619081d15102040c00c516100c50328070035250003d001d8206d1030401840600041465113a9032008650341c561b189080c0112011900b200e644079011070711041c068807020076a503d1744083e8054041541c2c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 570663597 1250 570662347 570662413
    0x50f0402060d0b040e010906091707050307150f0617010507110d140910081605032809201302130e07030212010f0510210209190603020c 60
    0x42c001008000b0305094112954441c1d0303140800c0260400902c03504205610600000c41d44190904040211800b405001d210f007040c104818000500080304990019500c00e440342d4801c501000701d00003c0008840c1404d03c0f17440d080d008106d615440c0340240e01c40400341c00a100643c1c50302c0045540095a120b9240d031580211609004140280900039424022401c0181003c050b040020b80980903007504602007540a42070001036411100c07031594003c2d182c24004d1860070300c0d11382c091141b4100c440c0d000c540385410130f08901800c0141c0000300d1258100c14403103466404001600d03564040742c0d0005200f004206000c250180342e500a4030f0145000b03c203044c0c02a03250000c22a81400010314003000c040e4200030155401c920303c0340c0d0a010f01100184450114100300502107100d140c2ca1400003030050581e09032200b40f00317402030210760740c002c01005600c40d034099021074038419403808041030310008190080b6803035515601a00165006d80e045503a00e401002106903c0b11201c550260922 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 570664847 1250 570663597 570663607
    0xf031710050307050f010516060b242a01050a0f06120503040909080418020d180b06060d060f0e04020a06050406020613110d0f0212011505090907080604080904050f040206 75
    0x8a0500d0018405c050107060440c0352110b4425160007080c1d00000488000b0354403040700c074183c249401400315075002c05000147c0a80490001d40450181520000e008281f00364904484005004c940c2c0080c1d000030300034445824601502e43c00b8080708403807480071525120f0b0000d02c514461321804010342d0404003031441e02c1c2c109860200603110b000e03400c2c1c0311100708102c0040d2010300521010ba580d9014440182c646000e55000d01c10380d600d00c2c2a60301011900707600100071aa40300c1703469030894011104140d94122010400e0702405603075011030580740350410001000c848426149102c1c4e8400c40320561455121401514103014030700680f4016444000003484c207200c21222070740717058003c00d004840b0100e1300e00051701c3c20030500001c40742c20801d04810740850034429500c0b1090752000009100318201d10711106600d158610801d403180e00c81c600820340301002031000344050400001964410310300350500c9405680819005400b942c034000000f03c807142081d030600d00032503006051030300d04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 570666097 1250 570664847 570664849
    0x90604090c030902060712020607030209100c14011409061f060e03010906020304060b0f0307060e040506120f061e0f010312110d0e0405090a0308061c0f03171005030705 74
    0x4000e8800703101d003810b541d00b515002681c1d414004d4008581710703445800448204880c001e00b0454080e01ea10185030050042c03001a65030b90409030084c0c1d1852400c9440c00c0c5850508490109200c5900e0280c0e5192074410b05030490742c44a117511a02801e42112999111002c41001d12448603084540c0c0980a50302804404c2c0324010107071001c500100013040391181501c83c9800c81c0e0096a0441e9a142c0d269421211070a161005140d100b8089002d840598609000544500000c04003d44520303079a0000401c940d680c3e503194102c8060403422690421002c4110565039041501d8400b0201d840c030281003003030168003900b03a01c1f90103400c41c000c0740c507403856071100e0101e40e411500701c0a00c1000158413440040400101d5000600c550764050000c0c5240140000c0710400740000400350000720b02d03280440d4000341900e03007014080c3e40b9503043ca80c00010550300c603003202a0051200000c1d8150005156001154421501d500d6006142c0340d10381d908644103d039500d00c1415010b4002283c10000c2d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 570667347 1250 570666097 570666101
    0x708040e04080c01020f04090b011403070e0d38011a0a0201022811010621081c0209100305040b0a050702010b0402041d07050f04031118040311060c09060409 69
    0x152040c0102c6081c002500b03030b45030981c0c00890083d400c1150126040000c01038031300407140d20303040c2800c0020764401403d0502000e4400184400140622442e00c56601d44400010440e0b460b001608284062564031109201d150b80c4020603621100340c40c21540c8100b03085840c98102c42010348050000f10403070032403502075000310078100c056550a02004082a40341540c0c2282052044110a44804c49803001783c600c1e000e080013140c0c41e0b0725020050000070103031144035800e00f00381c0354100c260460b503241000407489103011b00e010600c85050f031100e54864036005086400400c403000060008114021000c84008850190200185402248a580c15940b00303580042c141c1c07001261459141000c00c2c01d9910640c00b010101c0085840800654800201140c02a20506e045450902401103078601c2d8000c902024042d950b00086000040c0c0d00e100904040c43c408100c00300c1640b401d424090310801450a04031143d016030800995549080d004030303000800010303d000e00b041d0a2221b8000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 570668597 1250 570667347 570667351
    0x15072a061e0c020d1206081b0a0b0f0301060e040e0309010810120c0e100f090f02040302130b0a060e010f05071a04051c030c0c0807020d1b030201090b0708040e 70
    0x3001e03000d2265000c190780348a015450318001c640e0003c0800501d0b07944000c2c01100c0400d0000419071520300e0620020038080340d81802490900800c0390080c450070700040b00d4860039841140803800008441c1101d540e048042c60480c0e0b000c1d103500821070034440c1440180e8160040758400c1c5d400400c501089580a5110180c0201128500c40301c1c943d00c500d0301040c000c250710740589034408042c40400180488118282d44020100503098031070345800000150000d05002d80d0f035965403101a0b00a00001b10742c1903800a64000b00b01c0c03581c4170480b104000040400482c0c00c1d0084210100c0401c0030341c01884403201201d010780d9089904052500700316115040003804a40c5a09038250116000088e0744206020b9030141010340700011101101680301d00d440c000c124245814607507040e003500d812205007003210360010b42c1d050b529807040c070028a0300500d420008024040c0e0003684003c0c40302d01d02500007940d100303890380d4801544031280c00301c1c0c0e80170b1030b44003c08a070f82c1000180314071141143e1550b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 570669847 1250 570668597 570668621
    0x50603030909040803041b12050606100e2e050702012706030b03011d03130e13020111101d0c0f0a0306110412060203060901051c120e0315072a06 64
    0x220b2202c3c100c25003000c81c440d03035015234110820b11100c40c050140c148029904010201d0b40c0c04001d04030f0741c201503d20500c10011030b108118011801c8041c111804169444160700400301c036800218000150490300701007030907400552800309a6642e000d42c55251120250b00084101c00c59203080c0d4114050041a001c440c1c055494000499514010811020b5140010307001fa40c1c8442c44400f00321340d000c0440d400044401d100c02c003030100c024081041d06070016028640100e8661680400c030b8a40302c7d803248001e1600b49415840749110108482410079040703c1800da404801c4198100080c55542c0e801c11540024824000c10000f01c490f030283c1d4034603800c15a07040c14144c0d113800343d40f640448140c0c16104190000100405850003080840c0500001c440d16011000062007614801240010051482c52100160080940503500c0d0300d46505005084984610460550301003032942030b11080046404414520401980d00b103900d0707000c0441c2900d4081400c3c2640302d207005040c2c240460 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 570671097 1250 570669847 570669863
    0x1090c0509030a0503091f0e0d060b0d0c050909030c060c1e040b0306040501050405010602061311101d030a05190606030204020d1a060f2217070905060303090904080304 74
    0x20a0302910b05103d03031000c1ca0300840c05503490380c80c034106118403071400c00807072060469000980c80a66030041e9011a02000a84c0c0c041c4402c191883c0079030080207000c15103948004504103000410105000c031000341d45041d94881c030345898005c1c15035500e001c0d080d60840642c004d0b40000c0c0c001c2c00700c6005818503c1c0503254011101d11b094085016951098003e01342100000003080110b003070600840b4018101a10308121039890200c00035180d1402600c0220130008204003031081c030082c14501400004020700d115500fa2400b1405004144a04601d0603568105e03804001c1a03d00882e0710301005800401620364030361000f030001403103010303080b0403561a50390380c4010015890701c0c4041d0100320b03d041000142c94182d0380802140710010030301584201820400c00035210001c5042c0d8142c005210038121100c108a58880001c4040e9040640c003120500c9140094036000544981116007205e42000aa2100004d05846c1c1c13140c0e01c2c4a94001d9684000310f4001050b0000455019000302c00c9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 570672347 1250 570671097 570671107
    0x1c15171e060a0b01050f040302010503040f120513120c0b030a06080712051c0e0f130f05040b0f070807050306060c0d0908150103020d02060c1606030c0806040903020601090c05 77
    0xd51a5100182612111507501c60010021180100d1180368040304090a1460800710050700486142c0300d039000081c10803d005c000b1900b0001032150310b194030390b03210510b03001200304003600802ea034201c0c01c4800c40d00e08090000040744000c14002c0311400c0d03004048821807a003010440d06050344094000d04030b05075038181c00903e41e001803180401030808030480720400042400c1284c03901d178507a42a014440809607a00c00310903000b00314060b00002c290b8a9094400210f400180e00c1c1c420709450a004a0510703444c2c4500444980c4503e100328400c005403142d50702da443c21141940c504403400c1e00403d04c3d95002c034541c02d000e0005907034814001001d86240140007800c260510758102e802c0004a80301c2c09041c402e1071024000070340c2c018403002100b40c0cac279895a0005580000c0c51400a4041d4400007a40e1146003002d0141c440681d140341a103015140d502c0710028014000750314070000103114000030445c1440c01740910322100d074055005100590819003002c000384401e09407081805000c0003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 570673597 1250 570672347 570672373
    0x3081b06040516061701170703020303030f0907060f12050a0608190b0105030c010e09070201060f030c0f060e0108070e060d06140a08010605150901050409111c1517 72
    0x800380703104500c00d40203021a2607010050b1560840340e5005403051140c01101003001d480304424040c110ba103092075202c4002c4100c4541c60405846800203034260000104000c02c8038008900c0314000d800000442d581c51343d954100300c480c0040608410300192490002c12040003994100b50b0b0800705001000412a0355403a08030700e4100401070038080341e8044425081400100e4400741d00501054016041c04500c21000903c105020a038962140d8130741c4010aa143c3c2c400d6000201801c14044c9840115403a030030041c64122182c883c0c004038009958000c43c40798130a14880c9401581038444911981b0343c2501507544a82c01d0386503e412990900026940300028001c1e40e00816640154064180b55041840200181504100500d03810014100302a495842005241d446080340458988154800413551407056603c10101503043c51180e000c400c041d10000c240c200310b0313582880c100c00c2d01c0cdc460000031740c0c40344910807801180949080103141810852401f0314000c1006a80724050050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 570674847 1250 570673597 570673603
    0x150603090105090c04180b0a06050a120507150519020a080313021906050a1b06020f0306101409010e0d0213090b091c031a331303081b 59
    0xd9503565541e44400502000300307014888034620082c196070900c400d1024081035103605034543d800400c0c0c2d085580c000340007030070254042e01c0030b040d00808040229989041c400c624004d4070f9800d5415016001c07002640141d400710420b1322a016440325401c003c82c1d0202c00c4048150041190258011082d00c02e000440031b10007544901400c01c0040c000312050f006020322188054903200c0c12025013103050000725044005d48400412900c2d00308810000c041d0240c012400140000b801c9500110341d00d0100c4115101451007850207a481f0285840c3c1c40e40101c0da03d503008164541080c1c01005400000d5124030100d482040001d418483c031500c1c1980800c3c01410300343d100801c0385a0702d00441c820001c4400c90350b0b0b0001020b20061003608160445444000710030300b10603007455594200404240d141039030000150100426546010440c025a41a4a407225072000f144076440c0c07068010348180780c0c06482161140e0407640700c10505640d60011642e001555013012446695000e01e00a0010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 570676097 1250 570674847 570674851
    0x1b09041707120918060b0702101b0b0f0903070221070e130308070f05030115260f01051c02040b12060406090210080103050606090c1b0106050a0e130b150603 69
    0x190b6244180d0b503203008009005000f100c112540200c0c244170741000b2525552081e20b5840d82c04840c5451600d424240640306040001c0d0421040a007121400040c0480d9020403407203903021542426807591900d4407551a0310441000951096a0429a640780c0305c031031050000c8603000b5022101a6078964400b1840c86908907540d44440e90001449070070103901201d000d401411074181404000454070000c1c0403130005011b80480151511000710060744207114030841c3d100c01c04c81c400120f98130134102d0717041200c08403000d00c804022403000203641c2c1001034044903880454080c5100009141d800c04c0040d20000d444258403139602c00b01800001028004103001d244140c0b0002903000b050301c103001601c01d542420405000e502001000413440101d44c041e4841001c44007414940d41d1240940c0e0a4090020b103125400514802c880001e28154805410755104071505a19030f9030b81c10450a208000300d60408040009100c084000b41c1d840b001300c1e4100124140d01c0e0050807401003c00c0e200c0e001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 570677347 1250 570676097 570676133
    0xe0a050109020406060c0b0c13030b07050d0b0303030105030a080f2101060327030503041523100303200c04020a0503150d020307120203030d0c0804051b09041707 71
    0x2403100c0c41e100714030342442500300400140c00c000d02241c1d2070303032604c881700c041c0200b00541d96900003d000003d0035a0660007004ad42d4801c0c825122418074840007000340d000002010341c0e0f58030707018105459280002c2603a040b502e00030000d04c03040051b595941038581005594030240d10302403181c03004600f5211403c111501c14100c26181d21343c034128004040d500c541840c001d039440369000d4941c464002c020380030700c2d880d00b5092550f130b642c581e0b103410b071545070020446040040c5425030304d0a00c905904160785011444c3c1018500030b444104000420601d00d100080104040c51000280c0c00c1c034401030400c80b800480c1c152943c00c02080b01003026a4414070f243d4000480010800041d0040c0702031108420708266103072480c2c48400e40c00720b82d880b4141c0c0204c003144030b030070f02c441c40031507604108484080144220600180c968400050544074050b90212114060070030034444200e94101c920a81d0100108088240d460342c0d10f0711413005c0c540300ca0390f0b14007070400c0040001007001c2c60f010260080b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 570678597 1250 570677347 570677351
    0x20c130c1b080f031e0c0306030d030203221403120a0f1a011d0a0311090903070f0f06061d0a0c0903030801031502130b0d060f050108040f0302010e0a0501 68
    0x1654000074029981446840c001c03120141c03410000c1000041541e80c92909100020342d2900c90061102d5100c180080d2500e941210034100540c1c0d80b014805903000b140c0c141d00310380241d9000f001c1601a4001118450601c102038542c04480d5404540303102c1301d00303024480024042580d17400c503a0540e4040101444030802890a0003900b01c0148281c4e2180050f10004204084680036405045d0400d90500d9040006041d4801c41000008081c411450002050046295660720f40300c50305e100045101403250b0000000a44e0240340481202c00ca140d10000001c641d08075030b5580c003402005200140c4586560b00404034060742c0007400b0700084003505003040000e240403001d0b0410f0320810400c4c4020059103460800000f500641403c3c152540001e803450320303444850321a40240521503e541e0003091550f400660018400b0082c21215510341c02071220584902e08a01e00707e0300ca1058900141c00030340014080f5040b5500202e805210380b0010403402031000c00540340144031030050343e06075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 570679847 1250 570678597 570678611
    0x20714010c09050a2304020c1f05010b030f011502281101261e131b0b030601030c0c0605010b0a2003091201060b0d1b090b1603020c13 59
    0x6030030404031402444101e444c0800a4281211090210015802a01020140010201180d8a540540b007207211003c00300e8418070020b0b01d03104000c2070113625408005140c8400491911103a8003140c2c8940c01c4044044000d034a0118a0351410501c0c80940c070440c000c843c1c602c02410141074035068065510380030003105100a051913009a000f4034040e0341031001400508085101340a100c0404812016681145688600c040030b01c11b41c4c0700b90482c04013984030041040d60300c90310340360523981c60182c08420228004040d041c680c40c3e001e405400c09052090000615030f61017500401016031142c0741905070707070031165110001c4e07c0c0d080c4c00c41840c140020450b200341e254050410b01480400c00d039000404145191143d4692003211111805082c403c28002d00c02c5000f50800002050510042580c882c0081d280e58004c01c0004205807035002c403c5400da0780d640c80342104105a07600300e03c1640c0b81c0949000c84c0c0403a0824040e01f10154020065240c10342d07901c0e811803c03c070030f04212000c5101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 570681097 1250 570679847 570679871
    0x31c0f060f151206180e010b0f0f0f12010c0206071110020304031701060504051e100c0201050714100e06040201020c040b040e03180f2407061b0f020106211502071401 73
    0x6524000201406d5a242c5003403141d040d918240600c40002c03068031010b070154041000b040580040d05c40320783e0440b11209020007100015440032480c10400e50960312291550802240e940302d40303800341c5d00301d988800030403c50501d05600a41d0840d1007070408a00e00300d0180c10811000c00d007688102c0104401003010001d80c00e10450072000b084048083c800ba8059440010700c0c0516014070203030410251009100444e40100c00702c6203241d17041842ca1003841800700c0015643d00303042c001d10b0945801c000103032018201c0019014000c41d416000b0386507000e2002c0134000241154086280c0c4141c517001d84050156052000345043d0700300b442d4400e50703c0b1518091040c20036500594034000d01243c50521180b4104851500c0c07441c2d803440d103650b0b540006003011405007003202840340442d07400e46030814410b03401219002050788160001d2100c80c0c0d4a250815540b20206942051000040e50900006a41d40b00340100d081035030350010309200c1c040c0c5410007261740044002009a54601b036070200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 570682347 1250 570681097 570681101
    0x131d04050d05120118021b0106050a06110d110106050a0e0a2003010905100512030304060c021c0507170f0d110307270305031c0f060f15120618 63
    0x701101506060740380407500215503502260500c14910b48200e4100c80c1003180c0c000c0d0b01110401000b03148150506c060490070355000b49001c0c0309040c49603455a100182490181070300c0828000400b010305a001d0344054103a91440031400d0f02ca502e950785080c0407420f42d44840c00c07032002e8030710305031041d00c90f00d050719501086032540c200e10001031451242141c204140c6401b1641965600c4c20f000c83c243d1514142c068015040740c11480e44140d03504003c030703100d10300007001d10b10680c000c0354103001d00740b01510141e0b01d410290411000c951010240d0b022442c2c0900002d00049108a028650041c007180114030385400c594036400c81d6101c0001c105080c0106c60003840090007401d0407413031440c2041c403006808400c800c01d001c03110411b0303c0a0b9503e61800c00f69003000840c0c200c02900d1752040d2500d411100141441002c102d00c81ca0100c0d00e0b0840a6a4442d0745d090f28403801d0903809503401e0610540d036004030b41d5103060801862b00302d000d056802038008c80c00281400c40c8a02c15020754080c01400b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 570683453 1106 570682347 570682363
    0xc02011a1c03050f160312060f050111070f1502120a08070309020d05070305060a0f05010f0e0c19030c031a1302090d0b09060106020705010801080a0602131d0405 71
    0x4804040d81e6901700280c4666244101014002d000b0300484005005600318280c1c02401480303c0e5000b100c0c0c001c040500c880464100a0b40c41e030320360f4403500582c1c00c080c0c84120b141031160380241e0100a0601c5041030100400d081440d2000e0050207a50700901c10020503844140d02c10541d2504080c400c1940c0c0c20400303a850b500c0e03c1e4145103a40e2403003038500d50a030500d0108800c0089000d481001d0503158040c44601ea00740c0fa00140c40f110110181c04100407080c10010381508082c2c940840044208030740300030841040c9505d014040718000101480309050001001c0220ba64503072851590030304071a80140c4515000000c103d03501740c40400140106403160500c0400320002654504032030b103c0d82100e901c40d07100e400455240f4000e100d0304034140e212040c080000784213500900302003120401502301c0542d940c1e8141c0d2225912050210104101c602440180b04040c09508 = true := by decide +kernel

theorem cover : BRFrame.Cov 570503597 570683453 := by
  have h0 := BRFrame.cov_init 570503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 570503597 ≤ n) (h2 : n < 570683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
