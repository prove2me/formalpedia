-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3660
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:18:41.45875+00:00
-- url     : https://prove2.me/submissions/560e9476-82db-4339-b6a7-003afd70677a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 658093525 ≤ n < 658273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 658094775 1250 658093525 658093537
    0x60f050621010209030f03192f07032001170907060822050f0615090f13081908060a0f0506030403030e03300108061603090501060308040f0b030c 64
    0x2590303410501c00180c20340d00a001c1ca8030050f40500841e00c109201040c0071004241030095000302440a0910308002c0710031740c1e00039001c164004908020364505a10204a08420a20020452309516201c0d680c80e4600300d1617a032210340000c4c080c0d0321138401e0760b0081c140c1e16043d0401a003a009918000442a03a21030151146405000d003100118607035818410b0602c017007440e4400c00204840302c0f0711f03007541d880c00c031801d84a2060003240007052601e65407080c80c404e0b41c68014a6240c7c180c6440d6a541004507029209244580c200707640c000000b03a41b0005007103101c2501d04141201494410003909004008204903c140c0101c2c00920500c400402d194042c2c40090303844507100d6581e441c080d0300a00302d001e90020984004210f1801e150345240c021201402c000c00c1d00d0282100e0300d410500180400c0c0503d205a030004000209181640d0740c80080000c07035850007040511306a101d250031900070350010389000c0400a070605c41003100070b0820004000c0c650708945146000c181c0c0c0101c5004507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 658096025 1250 658094775 658094809
    0x2090a0b01021207240515060c03070b040c0503010e0f0a060e03041e090c0318060c03020f0f0712020303041101080705040b0307030614060c0a02150c19060f0506 71
    0x162038404490b442040111816603c22440c1655040f080c14520b017151204c1a104140440c0c001400d00060b07913601986000c4c48004400740b0706040880f003084680d800003120a0028802480b2441c0450300a40481d40120f00811511803840d00700000d16083d01c4035042a090907a000d410180303c0d1400c002010591940c01c90800601c029000b85503d08500c6594010f902006242c8084203080072414a0b9100720740811108019060b40c19000360192100060394150448110710f000010407910341000003661800c0c94010f2130071621600c00c00c2d964020813840e810381d0f003001c11100f00b0480c62010070380e5841c42c54001103086140c242c0d030381c03600030050b00822070401603d000410041030050007500c0140100080c075139100d2030401c0d801001000c903442070082c5101c1410101c006420a4011980e2480440d4007407c0f90214540034051650505003203420240b40c1006200d000700c0c02030109d84031000e07802506540110a5052070016150038520304200103242c03400b8840d160341d4403042e84c4d402d2415 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 658097275 1250 658096025 658096031
    0x603080304080a17100e010614070b18100219031e0b0d140d020c01050f120408040806010303021e060c0307030504052a011706030322030c0f180902090a 67
    0x80b90b1000c40d80c013600070002410a002c00320501c980000c3d03c000000c1550510411407996030383e00c50f4101e99800700f03a07181e60704c0c0c035600f0403203071011910b0b0407001a0f0000701c0c424407004a200f04081140b603c0c0380c2c031440140090f8041040305011803240020a4844428582846400826980b58580c00c106c100540c00305c55507010003205580310382c900d140078250468100680035240040c3c0c2030700d03200001040d03c011300496200114940c002d9041e00e012503034071155103080034280140950340d44c0000d441584c81d18024400083c1a5404200017030203580b00794087c01d0040f1018580030208407a02c605094150030030001c001f0405200d80940340d10400a1901050307580300d605005080c0345580300303082d0100f40d0742c1c055001c0e64084202503c0206000780d917405c21588d03c04510f811080c9d402c0d11804ea140e0401c1081d0310340005106140c00070704580110000d1180d560f0743d00d903540480305034000480362040800801513000f4180700340d0758a42c80c210043c07000c4903c550000b44ca20390007c06039402c0d0b550f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 658098525 1250 658097275 658097287
    0x10e01080d1101200c0c15160c05130c02160308070308070c060501060504060f0207033306080601050a090b010804030311040e0112020906100507030302030711012d060308030408 78
    0xd4250851000009142c0161094000c0141c604000380e000d175000d60320502c100e013a01c000500f40488042c1c110102c5401c42410301c0c40d0b058151442038540d400c01e946198644c0030129003503039003040f00001104c00c40000125801e07281c00103810031180181c2e41d20004400041003000c07440b480102c0350401c0e1b0500c0d29a20542e107922061380d80100b0003101610080c0340c1000403544c190003d000b8000e843c0c464543c07030044000c2e03a40032aa11442070100400c0d420900c000498001d0000d000104041c0700380030540f070248802140d050490380254404a49540090010446800c1009642c0003400d0135030010b010304040007001030300d980000740c001810075a598401c1c09960364000c05030350140403d0300301010956555510014070151040c016031246450501050081c81e01c0480c104240c071045c0c0f20f06042c0307802902d042c2c009400040c4440d01340040c0c032640c1d5455440030b2103824480c2c000410034800c004100c00c1480c40349551a61240c0701c003450b0203014004070764500181daa0199000d40d200380e640b8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 658099775 1250 658098525 658098557
    0x1b13091805100603050105011a09040903020c030d0c020a05090f070c020102010b0406121103071527030f120806030c06160f0f050c040501061706031e0d0206010e01080d 74
    0xc240e808000e4894011090b2520a100780394000781c040f0307405580284510390701d403a88130b005103581442c00700c49601e00300002c1000d81095003007203500b00d02900507117090b5005000800e050408616080c000640424000e030110300d0b03c004414090041690f10001e94509070900802158014188030309001c80d244c500e01c1168803d40247d081241c000c0d0040c801590750712124884c0428009040341c01e10f00784560606541000501c00040380c07568034a0082d5180708081c1510f43c0b07070407042c035020303a182c4498a4000c191b0081c02100001e40c46800180c1e950246811300d00007014490781000204203505060004603900010181d0032814201c0d1215500c0402e0400946c101c941d810004100d05d03c014030752010f001e82644500d042c13030f0194058512454050303003000100c407024000c00000c504101c920010b140c0d410b0031020390050014045850340218400030a030404a00c8081105980c081c440500e4148c3d41445490700420060400c81015410441d1440d1074111907042c0c42c0c01c0081000305e080d42c00e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 658101025 1250 658099775 658099811
    0x504020d06150f082a01021504080d020301170f010c0906200f0606130b0a14120f01150602010504150915060b090111030a081611151b1309 61
    0x20400f920761006100e60350b0510b1625200b10390080481d0320395605032a02881c0004c0c10840f60804160301a10440441160440042402800c2500e4075401800605064551072000354040c00c000039001c50345140d1080381c1b03890550640d2850f00c150341030500c5070f4220b075001203030802034404d01c0c204074004012044a450101035000c600a000d44a5100e01791076082000c00c400c0d0160400f9283c0601d007401c0403502d041643d40e002452500502c0b40b40b02041000f094070541d9401c0b0000500702d001c58003c00301d6182c905198800c40070b0180c0d54484100c0c4003d00c01c0c0c204000104400e0000340024941625038103040c6611401d6900e4480d00c6400b4102001000f000c502d90b00c100429041014a80351000050990000703114940807440c02540e03054000c40000640360f4610541e41c2d808480d81d0303040c0440800540482c8801c05000003402d048088285c140503030510810710260401c00d42c0742404020b04007003450076440144803010070200020301c2d0116100402d40d0641d03440425a1f605e040d10329541 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 658102275 1250 658101025 658101029
    0x307090203060f1f08013312150905130c050d03050c070b0a1814011d1005030604050c0a1d0d0b130308060406060c030e130525030504020d0615 63
    0x104c40c0b095280e12078001444c4044244505403945d581901da07889000c820f900500c000c14000950108030030341c41103404401c5c007550249507140703003500225803012110002d0742c410744040d000065824500740590131591042c20380c8000309281c00d1041e110070b9103455181c41c0b11070040038024100000910141360280085440c6e08d48840300700c4010b196103203090781054100250510004501d100000180c4504010b60015128600510708038038000c0b10065405406030030880301c4005210b62026030564500700011038400301511743c1c035501e2500b10100000c81d50001e02c010070148040c0704801c81d00c0c1e03100f51052610300c1c2d4000c4c55091035400c40006080c5d08143c100060005014208120ba444010740c0403103030040c030035107079400c00e500c0383c904010503110035005810004070240d0014012034031414800010704809072040030003038120417591040c1c1d80200d41c2c10811402669003181c41c02c00901d4000f03883c21691404208a080940c001070344d00c00d407147c000c1c20958a56104030084036101c209000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 658103525 1250 658102275 658102279
    0x2121c09020303134b0b031303110109051e07090f2414011d03010509010603170f0f07081b01060f120b010e070903050307080d1a0307090203060f 64
    0x521000d0340e201c0006051311500400d018884848030140440f8180808070740300000007034151840340f001940b5114411104012028201e040c0ca0000481e482c6000003580141050900b40360409031500700a0180d20891104401c607030f01d05440000031170001b0507201840108035a0400c4026404c00ca40361400e00c5036000002001d00c6c0c81804e40900a0580c030140e4100004201a002d0300106c04207440ca103d864801c9441c0301c1c91518a01106603c110000e1840d103017503105641c40d03c66a00b0110342121811a03550320103070f54684d406e0040c0310558110035501e028032100350345015010a501d002c603010301c0c0c03680300100b200803035214208501402540c1910181c1180c41603006c40590301640a04014802d50347c502409150208040300600441c0b081c1d00d0700510341c1c426591900320103002811009021000700145903502000140d004e00007081064081c682e400c0e141d4014500170002c0b501d400c1800007101551b000911a00d8030045084005c5036900f490040c1c0342d69a80020131102e02490f4455a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 658104775 1250 658103525 658103527
    0x11150c1605010203010b091c020f01030507090911220f050d0602070602030a0615030207111215090d02060a0204140d031b0b040c0506070201170c0f0304110306060102121c09020303 79
    0x8100f0010706c030b01916103c2403c850002c04842040c0040700050050354000c0d4008500401000c1d50b5402900403a4000d581c81c64030742d007119680c200350811202d00a2880790055030001e820035914445501991319410f0550114400358680301144160200c0d910900e03000360700b07003125401800800e41c1a40d000700c1d000441595070380342000e112002048140103203080049000e1041003031610910907664801d501090410401d00c100042100319401c051108049104441c5503104a141126071103000d040c41c080103101140c0c96080107810a000204024100352040c0300401c01c80240484046181c0b04c1616101c1000721103050841d100f02e0300d51410204da480d1042c22008104550804611640c02005540c1c130b0070351924200b003090b108150020740026001e0751020025039995030b00319040040c98140c0d521b840d0005415001c1504103c9080e034150540903800401824244640359116409101a08a101c50b11401d00458091643c1303008203000e02138942c401503d030f039500114284d81c00034112 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 658106025 1250 658104775 658104779
    0x11b0308061f050a0f02030c070b0c010e0708150702150606030901110414030c03060408040b0a0c021005040306231602070513051902030606040302040902040914010c11150c160501020301 82
    0x1074819031010001e000082e17840f40325680d50310f03c0801500c3e0b2040c081000340a00c2880c000c10315065401c011401c096555950790442a1008100038580042c0b50b46005002c07204901d0b4441c0c07201040090440c0c2c10354000295102c03850f500052956030080080700c69580340d40701c5c440d45d10300402d4840681c6442e8400040d0100340890351403c403682d03001c0c00301c0450b01d22400c8002450349403082500d0003080200140010300c038010321400646059051840c00c1d8445036095000540142071211343d00002c03038400a0103106100903801001c54070545032440c0e41031203110030b00059400c14020861040c440800c01402d51b490300c03d00403403004010080c6603000c101d038040d400d200140303070955040c0440003110614800c0c485090007524841c51000b03081c20b00b000d10316000e0101800015500308ea02540c2d41c2e0b2202c001810304201c818811005000000360f24103461405480c00c00c020754000c3e00d6500244600c1c08809004140310307405485900e1075a124030401800c4c0c1480341550700c000306154004000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 658107275 1250 658106025 658106027
    0x25080a0e2a03010f0e0d05071b09050103060c020604030f030b030a080c0d0f0c110d0303021c06030b010b07200f0d06020c10021c05040c05030f01050411011b0308061f 73
    0x3070100822045000700402100c249620085420001036884150032040182c0b81540c010409405018024410001641c601c100c200b0f0780016240c01c2442080da41e1030040c0b042c07001a1040701d4200d491400100030760300303041c0c07005410a55100440c008154444101592a4070140840c80ba0941c0c8111503a465030151003609466140b8145404000f40e0b07001154241c182c410b280d01510180c01c04415007030050b0000500000c800900400c0d02459000c011100081ca40625146c070b001e1046400081d80b2030841c90092121841030780400325212040c82504042a0300a034100c209000d0800340c4c00c04154541d003c1040021154000391b400f818100000083c01082e030001d01c241040c19090f0390b00b040c0c00707c01800480c05211001415544a04c1d10a668100d203a0b10080d002402821030b031021503034810000f071030100100c00c4020a41d44440a1104001000010203085882400c003a29201a000c4101c411038501c0d21020341000403080109a07a0344400c0b00f1016940348044800d0092501020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 658108525 1250 658107275 658107343
    0x40c17042108060f011403012c010803190224040203011b170f070507061a0406060302040f0f050d020915090106080f0f0417090103150e25080a0e 64
    0x150f0079002e000000c81d1542e4540c400c035889a20084520429030440c1d0070100d40050329101482c070420032000c3e00c0c4403825140d41d0900018000c00080b00110707035410b20280034030030b10501f5924110640d440044484510a5202040c03003c1810803140701c0d03203503030f03603800028003401a0280401c20602081c0041e4020327a80040042c9074042d2080d0101e100c2d880d0104c001d13000c50030440e0350b907000801c02e100d07020011340e498100c48071600016805840c041d1a0b000040c0031280e141d840440429400281000040b041c940004000c01140aa600c200ca203050042503070703120803040092240da012000074102494043c1d020380ba202010b8240c00c560340c1c4400c3c024010a43c01c0d01e500c0c550441d600009442403031005c41451107107512001c0c217201c07000f40b0305207020030390000d52202d418941c46c1e9840802c294203403a50340c0010300c8000e2441e521410310030745c1d4880041c5080c0301a101e082c150709140b9035281e0030240040e003095005900051102c21140350604000a0801403481300d09031b08001480c88043c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 658109775 1250 658108525 658108531
    0x9010903080a030b03061302010f03020a170a0c020d09030804030303050613090f0201140903210c0a08040929010e041e0b031e0a02060f0c120315040c17042108 70
    0x5d0216482526680103200c06144041c1000b400107552216136003c0604c00d070054a03115150341800c000c0400406d40165075080102c4004004036900c10400c810183d040252904420860420300100e50440d120361a683c401c60001034181615000402c0480d1038048400700e02c0400c50a080184880c2071824054003401c88070280e0005042e4000a50032650040849004250084c028801810b480c40043c00342400c0c010910852001813120022107541070106000c010310940140d40d41e80d0904c0c3e8503504413038224200d07030611000c0e01c1064043c9410740d09900001c81003401c0545030b4050348800038015124920900b031203100704204110080c03070940c00445d0a0700c030032800e0b10401c100c909240c401136400e9410200180e07100030000f60150a0032001403600c1070030309030b500e0310b0203c1d11003c580c07604100303501c0528006800020009440702442c070b90110150304850620a1300340c0003170000c1c90103080d580240020030300e01c0c02150400142030402d010b0b1110756505503625044001c005060010f0807 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 658111025 1250 658109775 658109779
    0x3060e043e1e01230d5c040302040207080a0f1103090d1506080a03180e01050907020a021e1c02060f0a02070816060320030a0209010903080a030b 64
    0x4890384420107034075001100c100441a925060071035000c1c2081041c00d0300e071a109091603038040100da01d4000c4035000702c1421703031400078070380c1c9500c0300c8003601071050f03004011400d1002407140e4a4521050a085407040d100d02c3d06d103100c689240909100031030510603548000d41c4284000b071203c0410200700c3c00780074021444d49607070410035602e403815070715400004131080542d0010030452140c0d01d80785c2081001a0300840c0c0300c80c900108000103d007125600d40210955610030411002010b170700c2500304103a00c5102c44288041071800f50003400f00401070042c28859020a40002d402c64803c00c4000d070126001818034291310620544942c0c41c0c00340c40c001d513019a0807070842c244e060310212010240303907074044d049500c0c1c410046424046600641d104c1e0f0214000d043c0001035a52040140810306040d4000b8030038034616080001e02203400b11841100384070070400705a002d8007042420b5903805540400007603a11303c101001224540866080140450400325200885a40c150b02c07408400c042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 658112275 1250 658111025 658111039
    0x3150316060f0305010503030a1b02040513020907020309030307170d0501030b180a0b0606030c19030203061305041a0c0d0e0d030c141c0902090a0c0201050703060e043e 74
    0x10b01c4004a040d10024040c2d01d4040d401004507201ca240b03e407074002c42d14402245845800540e59001400380c48068406030119215401000190300e0b01c04a455000381d59030005525100f82c00010070707101d028841c00540358101500b0315085c8284400f044484284184030208650341c1c4038604a10003d5054801820540b002d80d41c080131110001840050f440d0892543c0e002551807808001e640d074401480c480100c01c00b4007048240d403641c812200140c20280d14003584915102d000d000d0502c000c40b280c406c9017070500040c0004141c0568031600f0f1002680100e080c5a81c1384d094810072481461045006c092801e0b000b260284d201003880b010440055034280082c281c1502c04403458580c0003003260703c13110100400101c2450f80803118060080640c00416402c0c0c0b01c1d000500c81023000c0303c4091000f51500952a012079080c410164040f5003400c08100e140d0811307000100c46d100041000b07000b004d00103012081441001a007034101c0d103054100309200b15007060311603150303505c0070100340c01088 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 658113525 1250 658112275 658112297
    0xf22030c0b1503071e080d020708010506150d0c050c0a0c030c060507120e0a0e0c1e03010f03020103020d090c0803040303030f14070513081905070503070312050315031606 75
    0x8400890300c459188020003e003403140c14240c411005c03007540c1e81c400b88003002814000640003018452840d03041c02c99009003005501d400040f0b820741d1002070009110301107481e107594260f080d80d8191840080303440340001c1d804400d041c060b00c2c02d100303803141c11403030744110001802000340c003840c001c080c1c0c3d1090441c014641c3e601c2d00242c03658015000001d00d0420910504111140f141d69104850b032070040a0268280d99001140f080c0380003615500100c19002a0407680c001c03180700b661103421017095040d0701e1503141904407242c04103d400001d04054000881496090103030f001030181680111080444d50b0741c44030001d90b2980b00c1d00c8203c001c030703040801d198403110061042b5482400a48402c076140d558913042120194029090341003800b0100340f010640480800010031001000041c0121045040c00c00d02e140405582c000c0b0301c6a44418424400150351014159800c21a070074021b480c0e4482030306174000190100e441603014421074031050380201003049032034100c5e5802c1e101e10440074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 658114775 1250 658113525 658113541
    0xb070c080c0d1704020f0d0c0e04120e010906050406031a0301020a050705160503120306120105090303071713020d14010c0f080105010c03080103150b06071b0608040b0f22030c0b 78
    0x1120032600031b54405250001910349080440300042c565204040c148005030b250001800d400c002a101a00d01910700c0c440b0110709500400f13500d640034403d01b0440041854aa0024418441c5000d00020141c80340301166082c001d10b07802c10340e2608000c0003951180030b001001002900040b9007035540d4030030f0500b80c03880e801c03000300224280c42c00a0080d1031000b448521840b07440c1d101610042c0c00403001c14000e180b0301030a100340ca0145280801a56590801c90382c0108103952107081802c01c0c02c02503041c801034800301040c00b8000395064a8481e0300410500b450740f41010b9180e05c00d4495420007500035000c0780d02500360f07941100d60362924040c0d662188011038820b0b1040d00024003150b580340041c0007142c4060868810f411207110301080006104001c07a1650b0003e060884005456000354941401d952141d440542114542a66186040d4070f80241c06034018060107020348010010580c0b17594442c420880780e41d00076905e40440820f030300e801401c0036403900301603170b250b8031041c0403a60013 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 658116025 1250 658114775 658114817
    0x506060604083d0b01080a0c08013b07120902090a0b13110403050f0c1302070602070c030b060a05040509031c090c06050d050a180b070c080c0d 63
    0x1e24102070080881d22007821a1841c0301c0c500d150f100101c42404601242030000c3d060708026441c00c8990080f0724011804009044038074042c014941e0300b410140d142c4640d40c1e1180025044440221010324038109a1b0451400044c0343c40116000505011215800140d40d1803a00c0c0540e274166103ca4000400b200d0304021070700d80603402540310401101190ba11a4244c102d40b40c0400002d1030510030700c50302c4508108480036200101201000410704009005040c4011408840d001d0050220381003a070340052004a0100003980d034140d8081441d030207004640d4103076892254005100c1c40880e4990a00b108000801c680d064487e031405540860242043d0240b80d000340b0039080114180100249141200c0480c00b102c0c10115a4918107000806c04050b04074000b803c407911200d0b070358547c0e0700c400803e032800108520303051030400c52014415089011240350503500240130309901c1c0c0b5001021505c60b140041c02900c50600480c681c1210341002c5541003813003d03030762540001c103c06504042c01d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 658117275 1250 658116025 658116029
    0x705060c0c12041202040b0111030406230a0206131a0a060503191e02030102090402030a0203041407180504060b03010e0c01031503261605010b090f130314090d0f0506060604 76
    0x8454164211304005044c15003010b0851b86c4141844080c2440d0204400d1864105034030480026102a00540d04030322000036007a0408a9038044901c1c12032421400783d5200006410140c018400c90301d4003003031050080c0181c444108201411041e820f0805640020709600c0c09142d1007405501501d0741450701980750b5072401903001c030f2a400b024402054480340300c950300c0ba050760155000c0106200c030b03544500c01940303e100051001a00d034140342c1040440d9035002d078590402036000c040709101419141800103001206540081043e0fa0717585004409802c4d48400d42e034240d82072203542843c0cd1004502d00001c54420b9038104100c0e403150310740e0035025015100c080c000c240c52500c02c261004c105000480b030f500d8054169071400d0702c00350741d012807207040003001c2c0c600e41d544280d03456403403500105441d008811000a100c450070020340646042c103103c0313401002d2101c4510020a04c407020001d5440c0079100905c18141a02181803511040c1c0000f14112020300a1200055241c9031100075901 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 658118525 1250 658117275 658117289
    0x3040605271209010306050d120e0a0b040e0a0f0c0e2d060d0212010b07020307050d0503030f07140408070e0a0c1b170d020c07051f0c080705060c0c1204 67
    0x125100700c0c050b038507440340e0003265803504040d12280003140c3c0341c40f62035442540c5882005800c21813250840b0013041e030124455124411502c40300204040381c0d400c003c1d101511314100c0c3c4124261a01c1001070020f012140c000d00d030139814818086e45150300802c007661403101c107a500c5458082121f05100214984c03c044990107140303041031034443c1c00c19a000d0226001c0d54440107241c030480d40d0510192201c26070084000c42c800103007040860905100c2c55008060549400c40b10508a9031000e85a020052295611200790720003d00340324441d80c0703404552210000910f54032901c50b10390a89491490040c1490300f60420045091460903218500d00302505650303168000c6801450103c007401d8040050b9150710040540030a11200035004111407a1615001607031480c4c01184581014802c0c0d0006110751908112040d240701907c003548103800342d030f1030702e102a00380d50b28202d9194024200080d1461081004220541101800800307602d81010103c13418005070003000e15142c07040f400f540f1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 658119775 1250 658118525 658118533
    0x80a02030115050c03071e1209031a1512101505030604020607080409050a09030f0216150c060504050109020315010b04060e0103090f0605190204030c12080f0304060527 74
    0x10082c540b186000e040018240400c0e03c1c42d218282e00e8085244200c10190825104c80102a408000e041102d0460f40c283c02e042c1583c40919580303036000054400209502e5100350140043c2040020301c004103820500204a850510808590559142c00d401c0010440720702c1c01162030340e0460740804007c00c443d4002d0040c0a40d035950b07401e001701600040c00481da0803109000c081644000d41c01040d1044d00b4115000524001c2404c004040154410502055400060820406507010042802070b11894400300068800d07d003002c60b211141003401410403482d0005000c02c00006410982da42802182100d1780e03000b241c51480e0705101c1c284901200c070395080000700300282c0030304684030ba071700c0c0141000268806a40c603481704060030000120b5401e40e07158200426103942d02e0140d10001c2264404504242c02c6580324505041c150158060034070401d4200740402002c00b04841d90554003a604940b00d0615291640140905690040300318007048a5140019007031032443c11502140c030020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 658121025 1250 658119775 658119809
    0x60e1c02100c21030c2c01020c030a061506140d0b0d0f0614090a02131a0604030b190209061b0c0406060908061003050a060f02190f080a020301 63
    0x103500c6811000c10a21112a902101250212500114040c81c0654200061080b00f4000f03080301e84005400c0d0074080a880b076203800d400f00050102081d042144c000c00114071441c0182d140000d6a070003240d0510540e0b0081003005000d80017070032002920040c280344581c407000c09035400da400b11400c4140941c20700c07a1740da031480d0581081c10543d034094613110000311036856a0f0300d8291500380946070769454146e810f020b0702c2e5407001154409154000f901001072281d0004159000342c201e10107907952900c002c540e04082e410198000e0788801003580740e5542d41c07031801d84075221040b5101044050004101a4840700d14002c8030940c44000b44158a04450710640d901c0000220900810340e00c00e0415500107038599100d10005012640c950b810f41614008540c3d1410303000a00c1c0945000b0307091820000079100240c80300c4c241d5030201003c144d0803d6503484500038004c044045080150b11402d030715045400042e010103840e0560f07507101943c0d94840703114042e84428860000741c4042e82c0c4030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 658122275 1250 658121025 658121029
    0x20f04060306080c09090d0c1a0702010e10050c0405061b030403030f0801061d0d0c050415140604050927010c17060420070f0503071101090f081e030c07060306060e1c02 74
    0x11341e04000d1040c6071029501c1c072701c0c6c8a4010880401ca4461025070b540f808440042c1c04200001c020413680c0d800240030380c0c03803c40070704c0405000314070506000d5500410200b02a03104a00c01c40100d85120782260348480c0c0d241801007610142c1894200800c01000000c5030303d41c0700f5811800f070b03103003c40c04a1002030101800e000310110341c4c0000351a42d604921021903507548901410000480070428400400d0400d100d0404c48000d40c07044510900b001c200400075500c9610000e40d02404107582c5683c01c01c01c4000800900d01d189040004030751030004941809a04984003038410741c050340c110001d50341c03817105020485116000c510b0400c0a0100d407032148900c408004c04400e80301300b13050720030402e040e0344440c51034219520481d6020483e0b0040442303940d0001d2214020002180c28501040c502011541c0301c450b0b40c0700607070800e028a8515141810b0400031030742c006420314116520190b60315002070081c5100d008040015015803a040702c40c2c6803040c1c0725011944510000030405007140d007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 658123525 1250 658122275 658122287
    0x1a04051c0206010e06060d020702040f0b030c041802010e0a0f03050303040b0105121b0d06050406020d0b0d030f230307030605130b0303030a0b04061707060f0801060e0f04020f04060306080c09090d 86
    0x501140310030340809c240401616a03005411142400800100c0c605820b0300c00c0605000480e20413a02662502048440481c400001003841035020308109080b5810000460114035044e0404e440e0180c84401c0001040300000046104501a00380300c226640c88a0030032042ca8001c2c0c0700000154440b005001030f840218000005492000707040146006450303440d0030581e40212000e5640c1b80d4041450b144100c064080c080400304100d8160b03400210a550140a200c02c2d40103036000c1190420b035030745880440014070038500068201c0c1c2a1a842c0550740100a001c00b4025280290240c0080e1110f03034402d8080c0c81440600140990b0546e551107a024008103a20740b18560721135100c501c002001071406003003440c90307178060020f0001c042c01c2c0003010f0701d01070050101800300304480c8010410240d21030300610004200b10b0b1490700c0600b521000074045c0c004c015062450b07a500040000760945c25034007003412200400180ca04004a460800030121421241f40c100b642084100c8008280b08003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 658124775 1250 658123525 658123537
    0x120603021f0905040e1b030307020916030605180a0c050f0711031606110c0114030a09020d080309160510020d1209120801170a021c1a04051c0206010e0606 68
    0xb2400c00c00007640c8a00040c162401085869081d410044035050300c0c8040544030b5a0251050b00110311b0184950701003580c880b0024811007944101050000c0f2491207a00134000234a00106103100031120b9007200c1070302c08802d490f0106142c0c07a158900034800e0154050700c068104601c0c01da41021525101e04c26403104100300b05905020701540c0c4181220300150401c06011542c1c2c0d07034900c4202c00341c070300d5240c4030201c455a414000d11821200c10540544112a4130040402c07001c034505903a8404070f5803030400c481e0000c0c0002408001c00481820020702410807411698105030100d54440c14408826800f8000000507041406000c4c4090f014160790b51300c080381d58000281940302034694000140c5032000540c001038a130001004240c54106034602001d4100f400f4042400f50381d800030358910341c0ca900107080001030110364018080d0b508140000034651002e41072a6240a2503e40e031103840c4d0760300319500000c881021503606880000d480c1c1c181e81040400c031105071244020840c242d0042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 658126025 1250 658124775 658124777
    0x51903020f0a0803040b0a150b0703050717270d030f02150109020a0e04020a02150714030c1b06010f060c080c0d1805030a030c150905070803030601120603021f 70
    0x4241107101048100000326549000d6600c03552242421310380840b001802070302c201d04060034070341c45441d045604400c4a00703d40c0c3d02007646039100c02d035150503a05405855800b400035400000a102c0c410344c10802418a0005403001c50422a104076403400a4030b0300d000301c0e9800c26840119400028050642650f000c0788500480e0b000140841812403100800d0300503075000d5030089035403403440d5000300d03009110346030485d410341c1003207078000e8000c3d940c05001e4890700d00500d484002c182d605000d10680c0c14102c901c821302d580d40349003610a40c03071141d0040503085d003807142c6500c00d192131781c401182180c140c44c103c8180041803440c11034126256048402d0a880c181d20801500c040e203401001484402d10b441e880c0e20500301d07107960544420028031f5200c0f83c02500601e4032031001035403141c00ca400250388007007509800051521440000d05146200411920400300007065070900080070318401c40003640c1d6602100a403800103002d07508540b01c029000002414803892440544000030724203100b03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 658127275 1250 658126025 658126033
    0x200901050f07030203040302090c03240f04090305090a090501050d1205130602150901020f160503041203020307110303040501050a0819060f05211c030609020d02090f0a0305190302 79
    0x11500460720150b0211074100c0250348000f0b000c00c00c605003c0c042542c07060202c0003a80c15464a00200c041c400140d00c8000f030040c8441d4003000042d41c40300602100000041c1c400c10011209190107441035001c0054644100300000d000030701c10780e80e0b0103401d05840002d03113045020340e081d503940d0b5890700414000106009051000941840f40803220800a10b1142e00a0161015100d615400c1a1001d00528002c2c0d0042149000500d41392049541e00014001c3c2c0ca070145c1e803182801c0f0308502980d00300e0320707c1131107009401c414198000045c180c9603000398908410070000604040e660720440c0302d46400700b2424411408002d0140001c5613108100c5580c0481d5294801c01c204111040c0d60061002d08106003018045828060711240702d030150302202110241c0002c0680d036482c4107810310740c90200b60301d26454042b0303486a000840107081200d01076440b01d281c2d50400b00070f50088004c035401441032007171003085850a01c1490b022a038000c400343c854901401ca1820400110341416015031007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 658128525 1250 658127275 658127287
    0x60f0503070c0618060c2a141c020607090501020a0b0a1d010f0e010207020901050f010c0b07020715180905130c0e0403020f0a0c15141303020f01020120090105 70
    0x88901800000e50b6070840c1011050313111380b42030b000f102c54200b9240c0c20096690300f50410810b003201c80140d48024820f6019266100f440c0140b039880000174516420f000e00003480180968141a03040041d49a400360381c090764a01c03408841300c030708034803a0a0059100319500000f08a40c0110307140c20004844011404c91110f00d00da468210203e18040c0c0683c1d91030004070b4280001303101b40000303c40c86000a510705483c07900065840d030010b003c2c95101d00225040c44d58581e0180b0003411380ea5a2111014600d4a80540003949036550381c0302c0e560442036101541e003d2103200e0350001c00c0310034130301221001013818071002200400000f0860b100500448100c540810449510359005110707844444190f45403500e402814903415201c040201d50103100c1c3c0b400001c11030000641920481502526104c0d90341c681214114180c100e5041c80c44030006039150543c0b070f035042403401d59009803001892001e100004a00304d0f14500110400071a041700c81410011081e0000c01c24100c05240c543c0c104a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 658129775 1250 658128525 658128533
    0x30406060b0705070e3c010603060509060f2d1306030b1b040b0c0c040f060f031b05040c05030702120319020702040204050612090d080130080c0d0801080106060f0503070c 75
    0x41810700c0c241000d11403aa11810407aa40406e4040c09412203181c2413013418581404034548030740180105210707200075141308249494420a980e200400341044040c1c0080035a4504540c40d084d8900600070310b42842028010680c901407441160703807100c10200385559842d50580e030143c00b168800c000150410001130392400c6d81d0098a01a19840c02400c122550798040208641001c007210100e030b800d1801c00c0140c070303c00c4940b500490790800610900e810865407055000f8131290407a41e80903150840203005140d006d006544202d8194080350046a120f11030040039002c01c89188000e42c08140c261f01d02084190040c104440c4094000360919482c3c40c000344658011b020f070009450400130404c1800c0d20704002c40301002c003041c10408400d5041481c0d8216a031480c4c1c03c40d0080412154400801707070032000c60500d40607003200c046c54844601402075615038034041040000904c0e07020010407144010b1048038112800740c0c41e0380030100e910b41025525900000c084c0c0c001c6c000d003000904003103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 658131025 1250 658129775 658129831
    0x90a0602041701051008030715020409060303080103060c020a020a05060915221202130506120a03050327100522030203070215030f060603060a03080c03030406060b0705070e 76
    0x1401e07034142c1d0500d06060110031182141e00050416a188018035401c1209000220482d160a5042190a201d1107420341303041010b4070460b400f81340403034038011000080c16400007425040e640714110a0042c0c80f0101c0080740d4802c0502700c0650b0102c6041c904006a24044008041410000d0580304207008000e03072010642d08142c1c100341541030842c0d1a01826070042d003030203025125040c200000c0f1000c9401041d0f40b4086058080c17003c982d580d010901c7c0303596003081e8041e80751805088859802040c900242150815180c09007800000008042c1c450b08100350f20b2092300c02540140000340210076030034060480500318008552824582c5042d03a030030303000d10b4050540070b0340043d0f07511141d601c1805200c40314540400f0740828240140a0741e01c401546094120400302d47c01c5850761030b4800010045695603100506061000070200c40c2c100c400b00141d03200364010081080350581c0e0308940d420034400d4260080964001c40707818411100444c1c28190484043e288a16401103003820284070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 658132275 1250 658131025 658131029
    0x503100918140c1507030e0402070204091e0308060f0102030d0b1206010e04030906031107120306080313080105100302060a0c1a090f061b1e0909251404030209090a060204 75
    0x20380e0402062800c071030800c0c040c0d014084500c0b000f013034941455500c00814500c2c04002c600c1c85150001078034401d41d681c6401c0f1400c2c10b034100d000300e0b07207004085690f00d02040d41c0c040101c0200b000c1a00045051900d100180720b00c40c41a0090351a0a01d6401010700520201140590060844507000c414003c00c00010b0f0213412254030841c000e041c14100903005c0e0956030f104c8401c050800b40610204c2d08600e00b0380740c4aa80c0302204c810719608124041d0301070310550b08201c0780c03880040f6412101500300000071085450b080d000704085e440b00a503011211030107000194116804000d040385c40c51060302c02c4544140907407001042003100440240c0c0700c8070155032400b0168011000580e0040c028051560030600000401c2202001402e01542c01e02549415003a94000952144808020314017100c0e881e0310300400810076031a100b056004149102c852200701c0d41040c2c40e405035154018000c5000001c0000c1400303040520356800c204107900018003000f014025060440b00040a81c00030f840 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 658133525 1250 658132275 658132313
    0x60207180f090b0a15050d080307091502010605010e09060d2604030b06090a1407120209030706030c090e0c040b03090a0f060e0c03070509010b0f0c1b0109060503100918 74
    0x2405007080007208094440e198101d010141c803818082120b80d447e590b500a04544c04080c954407992030680c10b81d0085c2581d030010810340e20000d09440c4407a419405881034800980300d070b06075120b01406108901c007048401c290840014580c00000c2745200c04441000707005604007541d080540380c000c40705a007140d40300301c1314002d0402c240540d0345044a03101e0350001c0c175101d0411200b0340300080145200390181640e02440808110b04409180ea0380440c0c00e01d040140c21691800d5451600030018a0442d1150f0b000484010012912075112a9428081c0816001da203003017609101c000040756001400c040304c1880740e00001000105208107143c40c19010303003000500700c2e1031207500c3e07400c200e03100204078480e4201480600041c0e5492030202c1c1943d00d01d40d5281c0e1100c00940c0c022425100e145011812442404004640320303044e402c1c500c04050007030380c890503850381d1090166240d00054070200f9100603010340620482d02151301c545141c40407401c4d05548021941c071070591030352580a64007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 658134775 1250 658133525 658133543
    0x50c040b07061a09090606010513030b1806090714060d0b0301050f090c0f03060f1b030f101203170417040b0c010e030307080f090c0a06050c1204060207180f09 70
    0x2030210f041120b08202c600701c2590005180e00d0441c1180d51950b80060825051010100e019480400c03c0c106001c0074540c07140c00500d40b41800d41c00d084204c01032130058500b81c8104400600c03e40404940b4008540c2001c4094414540381e4040100c0e58120030040c01603665581200012076409001d500e0042e41900505031181c1030045900d070806003024101c078040c8048030351461103500e000480c02e0b44165102600f4940703440b00180c0b00d0740640c3e5130100d040b0440022081c0000840100301450040c90182000c581c141e03603680041441842d42c0da4054040b901072002901040140190540e02905c130310030b64503903006001000485600036811004000c407000c02c1101421000348900c10010041c1c0000f0b50652624040c020303e042402426684850007050200351281c10410840e440f080000b003503032035003a40b07914004084d504108100700c0380744074000da65400864581d04803403d460140d8042e04001c0e0900000c59051010016580742680d03a8480c0c0802019141c445c1071a024461900c0c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 658136025 1250 658134775 658134791
    0xc1d0414190b010809031b0a06020a0513051c0f230d12050103080403080d1407080f160f1d1206070215090618030c0d1808120d050c040b0706 62
    0xc00c210b074080321440f41846203010510140f044004181c54040403a11b46080c0c038100f0b21a5007604010611100030a06800411001c4803146c006000d02504043c000d6445101d507510390030801c0285810702c4550454800102c07400105160061040c6558050007020402d5828000c00c440f2285000426a4594100c804c089030383c0769000071494101c4d203046270240b10039415a03d6500241c4210b100c0141602400981030301200b1143e00200026074512540420500d014800509100c01c00c44d01c04030387c21040000550200006a0400303442e4202d5510040e0314040e0060507100c0d112210702d100c654600700422460107580c3d10484050754101c14001d060181403004021b4078052411340c0d0110f0f580d4083e0100f03e0000000990700b0741c00031811000340710481005d051141144504043c0540b10300840488503140303504240700d0581c2c0030070300d280509648e07650070740b05895000540507491542000c01051b00242c405030050764005160380103c6150035940d032240c1d9029802414120b94103500c079000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 658137275 1250 658136025 658136071
    0x703081b0312071818020405210a0605060406080712140609100504060b0402161245080d0813020d03230f0c100c1d0414 53
    0x18001040500d400030350410000e9201c000d0518070003007480c0d0400803001481c40c41003008011140092500c144004107020384500490040e501500406028030000d400000800300c030800148040c41980018241810300c56840c08058280508503650142d00d5001c0403c40d20402d204403c01814055031800c5143c0c414a0f002d11503080b000c4007104541c02840800001d0000805c0030202060110f0000840e55620320f0400014a0052001c0d0b810600c042004111010102996840d1a026110400750400307a8003080340c50024000c10352115444005800e160795058514407050b030506a05000c0c00104150348443c0305040710340c4008081d071310501e41941d1554000d08040e8010008100041d85a002c0b6004207207401072030b000083c10401c6203640203003000d1315030f82e44112520441000660303c00340d0300e0408076a0740010740343c103203140203c1d141944c13440d00d244075480d500d160700e4903242c064042000301c0388580200000900d17003040c1c841031502c0041c0c00c9000b2507441a655802104030700c2c480c14003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 658138525 1250 658137275 658137307
    0x102091507060606140f0c070e040609060b06091302031005030a030f080f011d1015050d060e06030c06030a0b130c0809070303080c1e12040314070b0a0504050a05070308 74
    0x4c881414852220400d008030041c402c2100c00b11401220f42c0c0c0d40c1c0707040301d07803000746042040c0e80300160404070039092004119141d04001d0350a8000d0106004c1356540f00c4c200155881192402c50f40110035050384400c2c4901070300a194032007004511200300030f61b00e03000b0078108918404114000f80c40c41c100b90101c15041000750380c2104004d0200e000310341c10b002c400c166003a200103051194410f1031001500c00c000030303950580545464512250308118208015020f902301c80b1880b07021a0a0100224009070a500218807691001700104400014001400416400a13240c007400ca900c41c0104812a00c2d00b202c0080100c129680c002010010300c4001481d4400240c5015001d4101030340070008640c1c05100541c2004085819591703c0c13652100b800e0342031070700d8654a19201400708840d03581d00040700705c0502c52802a1280100400441e0001000b031140c10401401c500c400c1022441c03465113036204540c40b601ca042201ca1600041c0c40e81071411215600440d00e40b28001145804e04902903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 658139775 1250 658138525 658138529
    0x20d0c050a0828090605090904140f011b05031504052d0f0f071205070c17040e0711120702060417100b01030c020c09100e0f04020312040e07030e01020915070606 71
    0x403510039015810301d01700418078411039041354490080c000c080340a015528000001c1e2103050302c1150a4414103540c450b0113019000684201b04420071054402540220100c920880d080c030036060025040340101300080034080d00c003544007e808040300d1a8080302007100e0403003601005c90302211b480c1101202c070151100078910100c603090a01400040e64100d074107001d9410b584c0d04003055641e103000084420460a000c060100064410a40c10b032560340c000030010b03594007800038143c643d03a142082e154907054490b9000c040c0c0c800100000d800b59549c0103044c84070310007001145850381e110040003511500745c44091007500030545680c0d0700e2806205800036001c013070800f0301209100704c80c069190042c030112140202201c20014903801015140d14002e0000008100c4941c100754080000c1400f0840e41203023b071181c25106414440707800240d40840340d601ca014a110b945032642100907110701407a160f0b1a64080c00200b041c0e590300ba66000b04a6a00603009888009a0805405607200c50b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 658141025 1250 658139775 658139777
    0x9040e1c020102042907061e090c0e07140430080d0506041b080901020d05041410051605090102010f020307021510030209010e19060b04050916020d0c050a0828 70
    0xc011714900030420740950b40082d8000000040c0301e4003640b00d010100210000e01e000039480c00b050041000710003015801503440980d0410b4266544400903100076a0f00c0403c000614020f0200308030940b94003091a44130a0807120128800c40160110310403010341800c00c03282039038049031004003500d551040035444102100c0030b000565407841c107101002140b01000d402c020110001420504094045031410300c41040100f04a240c90f007070201c4280282581c0359030398054801075604000c0307203000d098043c4e01c100210b144007080050041d211a4032080b034030307415552685c02100c03d4514610185108542a40140010540604800b500d041c8001c00718140030401d61024000768030394030740042c1510020030b221071158845c03e0020000c5180b18242070300c40380c10f0410210308108482c01600444900356400384c036603214030a0512441d500b20681c2070041c0d001034055605d02d4480c02c03c003c40240500280c5224441c6034940c01a15402603409140c1c4090140b58645414208600101d0344031607 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 658142275 1250 658141025 658141079
    0x306031a0c1603022107020102070e10210b010609090c050705030322050a060c033207231e070c03030c110d23010b0609040e1c02010204 60
    0x6001146001d02891903000b90700956032000004250007044a02e00091000c4220014130034a110785811680c080c0070100d00502500b080006c995140407445400b0f1494040b42202c1241820818001c4a1526040300d0184440d07420303000100300208149400b0b011f07140c4c1e4184000d8100007a0300d041d00c01407058001080030800180022450100c103998006100444c1c9840b0031001d4681c1440070100808054a14011a405030040140c1980001345666458406000164910216100303001020a200c44503c3c9281e040f2440c110088900c1030740000c081c200790219502c1a0448000c80b0010801d8101c0000006100464100c00c4100c000d803e00d41030050914118590b40e68010b80c61841c070008060050103c018010071212424502c14202d010f000100200d2481c00d2501c240609968856210642041c2401d04018180600300c0c0102d03006d80a289840761400c00c0c1b00092061100e40308190090140d0204000241d0388540c0c4814490381c000740e211070611500f0780780519100c0a010b04c1c188 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 658143525 1250 658142275 658142281
    0x1050102070f0320010c05030408010b031b1c03051606150f0803040b0a032018040c020307020108060607062f281809020c0105090a05190317070306031a 67
    0x24600710200070600c1c0b1207041d0f84c0d03020540b50060b1490b44600900405038000428042107001e070551101160725005ca08440f1844d00004034084031207510841c490f00b04c440c4018408140d01507115564042e8401d00c0d107070b854004211721440c0c210140b40000c481c0d0507124172141041440d0485008003912801034049242c620346861160349124620801c1d2080300041034400403c1c1c02035004141462041e405d018408000c0cae070040d03000e0341c45004640616081c40d4102000d43c04c00c2c0c4100084001180c00451400c03174030b5001541e10540091419501900030040302e80000d0f480e00442d401d02e60010038001d40c0c10311201030712060160022008103002e030242b1180280001104107981c000c44019074915400c0011002280c1921450000f446c0c420101800000d0901e5181d004100b004030790300c020401902c50111503500c42180b0035025109521110a102000241d21320358440d9078032908209415010a8110304041c0c0c0045910341c000c07964a8104100340990268001c010900d42c00152895103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 658144775 1250 658143525 658143533
    0x70312051e0702030c07140102061e24030f03030714070f11030312070f020d090302090a020c07090c02010c0914010c030f1b08040f0b040e041205070f060501050102070f03 75
    0x10409801c1103850540c1c51022905507402070003217400600340c40007035842c2103031250030003038840a154000e60300502c140030000c0c14502601c000c2800c0b0010300c81240c04207407900c000490800e0148140118886040c14013842c00e80d0301048503464054650024580b00d00c1c2600000d030907035419400c0c02109103010880100051070400251002c4ae602a00c4681403007031920100340b440c0141c04041213840862024021200d8001400350100798056080310790040c420082101ea55016100083d04002101c0105030841e1640e000f802861107640111803181d075540e14401d05883c0210102409071b50f4032880079000c10340c40581034011389420411314009403d401d00080c80307454881006401c00c92032060005281c1e208080d2044003000c1200c100d5807940c1181403200982c1d0141c400d40c1100c030103401c4000b03039156105003540c0484221907031000e0280c0d565100c504007803d8a8480b4400c1060410201c00050742c2003010015442c001d960008072581440e0004e40381514a41003030310b254901d184200001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 658146025 1250 658144775 658144801
    0x3030315030f121106040c180207080412030219080a0909061805060a050a0314011a150f07061406040515060d0218090408070606060507020a05060313080f07031205 72
    0x2c50344000711030f40e010900b25088030380120f1003800f0059070054030140414400c900c0070010994410510700d40b4004080e81c1070000301c2c842d54000600c2590144410010040c01d4188040254000d0060340c40390001104101c0b042d80e10103074100c4030580701040c0380d03921550050700038011345200d4004004090070220b404a10b210f0f070042001c8043d484d00e00085071500c0b618000c0e001000c024240b0524151285408038a130805215030404945c64885246003000034208080c200350301c0640b10445460b040b0040d1081680315454400701c49804004040014031107105640100e110b0044001d4541820401c000641d4000703895a020300602c41250b188030703543d482c210b4060030301810f80180e403180c0c2c6401e1100c01140d80b280407603001801c41d040005100700e090040074100c0c0700c0c004c20440540c03140019581ca0240110180d04002c81d4041802542000002980c00250031802212600792960b2040300540c0a20081621460041104c004040d084080b03500090460704083c000e601d480b02100a070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 658147275 1250 658146025 658146053
    0x2061006031802040b220b0316031e050f07090509100b06040b0d060f12050d0201060b12040312151a030c030a0b0d0b0a0c0e0102030a0c061a03160303031503 69
    0x45903503141c00c032400342c2d9280c50506c0648500c5494131040710390034841136001460061031050007030003049016600c84540451020a4070b600003415080b81300880180e80c1c10600745141100d19200b407205120b034410701005840002e208060000c03035585032800c021401d0464101c1411000c03400c050100e0300d41ea40300c1040d641030700c074001800340c3c84040307041058021340202d43c404c0305010300c044c03004181101f64046aa280da4082c00c2191210a0848012402c0f01c07074620804111038000d0045280052845200d2900a4000d00d0800a0b03814a610340c401100c2c40c6030f10040d15094241c004101d505001e4031194030010b04201c40c0780c21340c5400e102c6084644401080c60f800d49684107018140f5546e244061214103070000100d080a10b4002c4001004100365003104000c20030786940f481d91076100004451140c0038583d01d4410030184c903501c01c1c0181c8000c1c03c1700004801015482801500c0802c07541c100000303031440140195146080240891f403000a14805e1080180f02c00c1c00426000d018005d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 658148525 1250 658147275 658147279
    0xf0a0c081501050126090c18010f0b0306040605030114070f090810020903030c2e0207231c08040b060f0604211a063604020f1002061006031802 63
    0x4c64050407081e0003c401030315a0480091911030b0003408500c000010f039030b220221f020b07a00c40300c8890340aa44604d04500074402c0d5810441c8480b81400781246410145411a42c0a000801e1550b21200001d0075034558200d825903002d000400c000500f94048500d283c117088a00f031202d00c880c100203803551550b0368001400c000c0340d0005034050054030100304441102100e8000c3c3c400800f891800c108140c0a02c03120041003101c1900054000e25031403003201c12484e40282070b0341a03524107035030140210442040b0100f0310b028204009054441400b100000342d0300558801c2c0b070525040c5849016558041c043c680101001150413800e529901d04036030a903110b2100384220044010002418070000010080c46502c2c4ca040d030352000300299000900808048480e00007241d850360032407401c1600010341003e14543c9a9200d401182c940000e2a001400034054218071070200c8041440c54400d81d04280050788810304001c241c0020040000c05404203207810301c50140f48503520040c141d44a03c02038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 658149775 1250 658148525 658148537
    0x11131512291908070f06030216031b05030a050901020714090f0c041a040503210f07050f0a0b01050901140a03031d031e070e0105030d03050402030f0f0a0c0815010501 73
    0x70381c1581c2e5418150100c2d403030350350052215540f520b42d80d030b480d0f120310701c11849070008001002c60560700034001c0d04c4001d0711a02001c61150a2030b10101c41800c090881c0901c004040110400840d030f0600c0144074090303035522060354514640000900d0301d4160307032005072088900f4114509554820700d00680190f03100400b140c1c00d441c1c91440071801d200300d90000e0264410f80b282c150b0800030701b2025000321803085003507502d00201070454102e60b14908021118101d402c00841d094808410b02500c0f03414080e1044550112104203800d00e0054140400d030381411240004014510b0008580b1b4003502c80c00c100721212452040124803900c04a000c01402d00007102d4002030391000541c0301d8040004020102c070b010345224000b181c1c459004400380c41c0180039440000c075103030462550290486502070024200200740300030840086c800600200d03810301900140e03c0d5084005c1106082481510014244072956071602d40840c03501d90b84000f0041c3c100d0302e0004541c810390701c00e080c1100c0080c2810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 658151025 1250 658149775 658149851
    0x10f05090c1209072d0612020d050103150c021c050927070e06040305070b07030302040b12060f010e0f0d1713091a09040611131512 58
    0x4804502500402c40e181c00c2c003003010040e49100020b02841125107908500598440410518101c8024407000250148101d03000f001003600c2a030204055031380d260001400d0040e0304561400b6154203a00981d4190004680f46a02c20514800d0042c00b00b401d00042030030001c240803200380180024a08003e00402041c22207950700e07084881f0440501c903044444402244003e0b034410584181d80c03020000700c510f0790200711400c0040c101c40649030014003d10280345003298086840d4881b0f0400c408241e02404009205030816000c2e1203c01c00488a416080c60700d01c040c00019520000c00300d040000c501c112100c0ca84800a4850703800b00151648034064019007403a10303400c40011400380d03030090b00247c514410401400c0d444150792144405002e80c0500301d0907511140c5d05641c0d8030b68041d003080042070015800b5030080c2082e020b14540e8031f003401d02c095a8070150f108994082d21003420340c00408000940d10a01e0000003494849040108100252031001c0401741c84036a200481048010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 658152275 1250 658151025 658151041
    0x90316210c1a0a0e03060108100914071214070e06040e1f02042402280c0e0601030506040509030a030905010b0a080a050609011e180c0e060a0e010f0509 67
    0x100809031040710080004205040c2d40c1e101240d0040e00610001840c6203122051841e010481d170f4100d8401a0082207603c1550610500070281d000b400c655040040104002c00d5030148451002400303005106c19031428103041500000e5100ca00f240241e8102c00b00c1440300140c0c003c3c0c07441d001001030301c0c00946041c2e060080c0d480c06c00800c100c3d01c80782c1ca0380c005420140ca0160000c2050b038100d0105000350190300c001c1c145a503425443c844000da081825030300d0b41f41c1c0f201d6103041e58a0603002e628074140c1c42d81d61607803034000825402003c0081d8228003004004d5070180581900071364203940c00c0215140c129401500ea000e04034009080503201ca240b030003442000d411440009c00003c01c50f6030700544c1e8000007541c0700d813541011515801580000341e18450180b003583d000c03628890b08030b01201140195400100120201c1000564040f40000003040034210030303202410030135181421604140040110841c25580500c03440034080005201c2c090b401c1010320215002901c5000751030b02c42d404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 658153525 1250 658152275 658152293
    0xf081309021e071a0a0b0f09010e07050a0215091e0c0321040e1303170f0112030c06020c151b120c090d11010e010c050c1302040f060509031621 63
    0x100344212600507050003040802e586c880326610700d00f26104043d18242005210201c1003d11039441400d00c11000218418090001440902c81c2da01c150352102071600d8814804140944025005600c9203a000c007403000c141c640400361650040c01001e41000c0d00d0300186d9200303151080c62840520321a0003000481414040d903000c5c029400d10f4a0381882d100039074600c1625101800d800260b4204001090746030301c0048240a01b158036010240c1e42c2c02c18041d080c010405d0401241046858100c003004070700984054811070148101a143d90000d40c0308030a80050080c080c00ca07414641d00c8881c400400c181c0485140b407c0f408008a0039a5032038030b10040380d010f01c200305500003210b24480c00400501000c0e0326100c45090300c0f450b0781034400034011103000d920341100415a51007507100007810300d0b01824042820b40300583c050300d02500d0302c464070144040c552050f004544040741030201c41c9024007503049120440221410102e14041602c02c60007000c203204922140c24807003000601c20690 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 658154775 1250 658153525 658153553
    0x30702190f0801090209330609090405100b120a03110a0206040602060a14010509010506160629180606071b060e42070f081309021e07 59
    0x28800c5a9100c2c1e40e01206400380c002198120b02c81c0103e40d00007166002d80034204801c403103010903a0382d00c0b03e020100482c0f81c82c0c0d120341c0c0b40e540302d5010321041807a80d8452811f5446684610301410008101380e010000343c0710100c2c41107101701c2603001e58405995000502590054151074016100d00e13401c1c40903410504034080180d00000c00140c0416096000210b0a000711b0864604104002040c0c41c0c08604080a02546a000e03880e07d00402c1146010030203440403020160403426444841d43d030380400c88030f0314040100701040000c0c1d0020141c20301c4a06140c60381e8282c0d0511b1424600b1810408801303001000e2910601001c5280014425811107071605920342c152107403031054807201c000c1d00c0c00f41124400d51203503018101311011486011180c00d003044030043ca44010b00c10784103482c100c4101d03801d410048500107104640c081000300c408007031401e0082c41040e5580c0c0c00440c2c0340d0788c0280c0c11740003041503500400104020030050403850b08580000c88040c2d41b11038051800506000504c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 658156025 1250 658154775 658154789
    0x1d06011d0f0a060c03020f0601030203100902180a0b10170112032309090a1802062d03070305070804110d03120e0606240306090a0603020604080105060406050a0803070219 75
    0x310502007a030f5500400265038090080e02180d04d160743c103a224564950342408001d41681000795101346c44c4000e030700000c192078402003400d14583c609a802c4100b5401c116a0110042d03100d008041e41070820380040d0190210a240c041c00c0c090a0b040440f803150410300c286003802d10451f91040c18184108000c41075048050350f41e60502c408610300890075007212103001d1103613804001040c00c0102c3c5110710036a0003001c460604501c0340c603400300300e000d070000170800e040b285c070410401a020810720350f182e09080c07205103000e0b1281000000217084910050020041c403441c481032001007a10340c00c0c0300764801421140244035011902e030884064036007507401c8103070340d081002080c3c0c682400309815104003000d0301c102501a4014009040d03080c0e064107822012501000419141d0400c8031444e0750100b04104040b849503501d0b8003191450744198003048081e591042400030614190240c079008010403200095081c3c1072440c801d840b4810f0000003407049101c18049201d001c6800703200c100400c02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 658157275 1250 658156025 658156039
    0x3020114030903070f300c1506051c17030405071203120e0a1202060c04050f030c060f0a0806031c0c0201090503010c0e01032a0f0309020a030c1d06011d0f 68
    0x404e107014071401c2d802d80b224461180f0003810b034008a6089008140690301c55039507050001c1a980c48c1d2403202200030034842021926220701085c240c4076030350b210600314503601c0c00031044010fa0900820a4404002440d03070950100240404140c1c000340b91811766070000794105c514411884c0c103a4132544c0004c084d00e100e40c24032500142c480008940d6024550040c14212115422420200e0310746004840050103100140814002828408600a441103001c1e084540c0211014001181508002d41078015031000040d07082080c1c0e8045100d54220340241e00606100054420304021201074202d4030f010001595091015a07104009080041c0401740c0200700071580b24000910305080d0035001c0f030100b400e1906404444038041c0040100b01100020300810400c4560219030045102010030b0405407161800c20141e543c001c1781c1c3c0025803188810034003280c0b0b030a56103c2c005881408250140340001c04200c80c2e0303604151000e4010240b10100c2540c4034088001811406265509e140c100340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 658158525 1250 658157275 658157303
    0x10308070213090c1203201b150d06081b030703030e180709090b060408211306120608010209091f03060f1a100207180e060a15050102070302011403090307 68
    0x1c170140b01d050300680a5910004415048600e90035201c5a8501000c0c85600c072807103198940080000036648000004c0c000c084005d02100b5002c504c1d0008070744002419924002003219104c1007105007070348081860051003444207030300040c0e1504106e210280c18001e04600c00b02c0d080d81e41d01d07411040c68030303010341100d05818191001054140030303000d19102c00e0f01c2e000d500c80f480d242c824156812100746000801d12604032040613902c203500010088084002800360007640242a1035800103004982e55886901c240c0c084154156411688100d8060b44100f0565010b61141640a5800b9600241005001c051005075020404035540042c3c00a450800481903410035500300c0d01c0c0301e19950b503071003111242c41d8081102010003000c122015178800d5504004204003007603088094140348100080c040343c0800c050b03083c01c1c2d080354010700c0190741d1394901040c0b400e034000d00c0010b0007007840200489401c66001a00108070614848000d620220004000d15402c00c00c0300e80c038552046c2000d903451 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 658159775 1250 658158525 658158539
    0x140c15010e011208030109020a030207120f0e010903210504080f06100807120b0702011512020306090105010605040b0903100204060809010608011107060c02070509090f1005010308070213090c 84
    0x1c1c060050080c0851000051080100303c18500b01604110040d241d80d107000f030740b24020341c8805840c1007455024040b03540440e02511840c002024141c0b64400070003e120b1008101c00f80c80101c5605024a00e4404d001080481c0103510305460782c4041818010540d007001d507a02d0280380c0c000340b807138420b034402d0041481020428900406070b0b04102802e4a464030882910b0314410701031034070800711031728140c004175141d04003039508500340f4000062103919004c5001440b24442c0c0004000c0c600c220100c03400c40c101005104c1d0b1194041c5c2c002c2007994100359005045200700e2060030200c042c00304030107860756428840c00902e0300000d10115681c69072150054800d5001f00e4842d00e4a5203446400582d00c6018011039200401000c00e5a25160b01e99840800401079240010214420b840c40486e09803a6021500d004800c1e8100a100810312103c030145002100d604d1000d51904004c01040002c141d40b007a9110580e0417501d10001c0100c40ca051001440d60002c042e2890920040c009849 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 658161025 1250 658159775 658159813
    0x180a050402040611070b0a0f0f09031a160905010e150d0f05100602010621060e1203090d171b0c010504030507020108010909020d02040203090c150c1e0d140c 69
    0x13003400744c15500300d140d0326643c42400b401003607006c401066205091014051090320340300080041d908080020903103030340710b6102c401c0000e4804020502c10b0340a10411051405228501d0b817000e1400000c503d00f000d00091412428080ea18060201d81c50b1740d000c0d410480c07051301c4094008143c100102d8013030043c0e4002a200c2038a04004402d038030000031410742e106005010645100480e060300d80210000c40c0d04c89440d0400e0300307880090b0b41c0c5000045800c0309000e00166040c2d4220f0781c5840e410b25055280c00e01c5912800138052000400028003002c1610880950160b01d8070108500381350910780602e254860700b150240c6552810080108042d0483c020b8000e081c000e9030f51348404da0b03c1306003000840b0103501c0081c0d0b001c0908500c01005181640081d43e01960003029a0021084a80402e072030724504e00411990314000f050103288807038100720700b0091641e00c0c0d03c0321610580158445403540228042901041405040815060382c00d004a4604aa00b00c048941100c02110101c202c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 658162275 1250 658161025 658161047
    0x9050d1115090d050703170408030405130617070603110a1d18040b100e070c02040b0f0d032106030b0c0304170f120109060501092702030f070201060911180a0504020406 74
    0x5080f50781200e014187e2202026141500c1003080258036043c10442081080700e003030001409003d48403000400c0340b1100c107100740d024260702d80092010f00e081c6400076042c2c4030500f4005103900c0b42404283c080300d41c4608030b810156041c0b19245030400c0300030041100f0483c0c40845280c2e0642c50020b00040000000c0224800d103034202c654aa0591180c443c14070f46901981e40c40d00260600e801c0c5000340c581030703002100c501d00080410081956040c046107000c1042c5406501003021452120b900840d4607401d80d908c224000c604010050a641d603006483d100503002c0780d2490404400142000044e41c00c0500701c964141001d600d8143c038070201c1c1e000368041c02140101d030501c0400018084c4542c0a40c400740d9505840310100d150814118a0100000d14070641260802c0100600300c80854802140182c544c1c4140014a16060002900355140c0c0c0c5d1042261a16254404183d1040c14054030914a0f01c6200aa0340c004402c001640442880e00071540c010710004002802940081e14070b10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 658163525 1250 658162275 658162283
    0x706020d140c270a030b07020a140106050a140d030c08070204051311030105011a130e0403032304150c03021902010b12070e04170403050f06040309050d1115090d050703 74
    0x2092820b03400302c3c1860030303c5480d2070390049041002400001c0303c04c42e007664030400f1481100ea10000c140c07280d800b06d6064049002440c0d54580c024455410005e41c4d50020b8480310712003a0f107540f0070b400890840a114040034003003142c01c042c40707010445e04200b00d400b0303160024014000d506004480710705542c0c111400b03c8080c1e5610840241e9402d060103818100d50f500300720200f03081d104070881a019442201c0180540c00b2103100454031140d0b041006010320300036500001d401d1411208480c8001000111501c2016031b28100130028100c15000064459401ca0100310148151310560190045c490340008810030040d000c101c940e41503109000c88038046903480e07a1075407541d1ba940d0721080d103401122910305081c4000760116154441c0e078800c0d01080f2b009685000d07500d4507a1424801149007580840d0400e0f0705200170b0662021114018080840d19582000c3d117aa4907003c0c1c0680d91648140074003080c0070211040d030352400070760340b00c2200a8400882c00b003003860491380b0368280c0c2c00119 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 658164775 1250 658163525 658163557
    0x20c280e09060c0346090c0506090402040e0408191706041503052b03090b0a090201090b0301030b01030b07090b07020f06130f090c1407061841030706020d140c 70
    0x180c1c1d1701d5805052502c80e0403507103120440c1d00f00024800c50350302445416422a03001c01001030340319440391003144920f0181c1065030712031002c00754140000c83c4201c00142006400c00c00840e4130b401d0120384582004040760009655001e244242003a00d9441c0e002800c640200c0c0030820b038031450b50b20b0a06140f150030000c562020f481000c25422141031500203403410301078100044030391040307600c50b03803640e0b005040c58582580e5803041103e16900980003124040700d1b02c1c3c01081080404c019254101901c0d0601c0004141000c8910f0f41500500201038800d81c0740d070050300102c3d00c0702021128500c00e015185c40280d5112910741c80000303035038415074030300798641154840c0031441144c0c45100d0f00186007029150800c2500c44401810340c000320700310f42e21079422541000880c0c007031800d13410701c6a1301d08030f0700551010000308241c40c900115803201100900800a2068400f00454517040ea0055006844840c0d1607000c100030400c207040307410020a1003080c04980c60300103002c1d22444211000c95 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 658166025 1250 658164775 658164901
    0xf0f1509060617180601080a14071206021c02040f1a0a08010302100203040e0a05070f0c0305030a1107060f0b0a0b070807020d03020c280e09060c03 65
    0x9008864079407050400088440d001000c0c400c104400d038540040208490000c0c400c0b5281c0c2a030304080d020790009515504c60785694080101034050452506018005002604d03d000441c1c000b08003142c0d8020001940014454440c015820b501110302595840c02c545450310745840b10300c2b60f00180105a10020304842c204071aa04010848240044682e00e054041c1d03c1c5900f400103803401254100154002804007103050000100c0c9540b04044402c030102d46814a440003800801d5520086000c1007400c018013004030f608001102d411440c440400106560540f0580d1198003421400604840c01c2a10780d202c000519004001c4075142259403503403043d560b5500d031070988240300e402400c00703100380a06800340c030306403a91140daa80070f8019510600382500c009410f0101c00c0c3d50721301c5044d03848800c076800d0000030a00c4402504403080e00854a080c030004c00c03991303070381e004141888502002002608c00c00e41f403503441a000d0100b460000780b80c003006e0a5440880c0d03140010103030110010380b00e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 658167275 1250 658166025 658166039
    0xc16062009040f0e0a02040207022d040f021615060f080f0d08091c1205040b010819030207051035060f0f01080601052203060e010c080c030a0f0f15 65
    0x40c0944c59010078008100203030131942404003039041000141da000340c2c80314418860041304442c1c444a1100100d441a40b001e5000c204000c03603e443ea81d2101961041c007403080106804020803443e560820b01d00901800c0d8141380070040c0007241c1101200d4111020700056000c2c00181090950700100300762420741d04101d00c1100c0c03249044405900f40d034882c030b081c0c000d03240d240c0585480040040c40c140b052589070b110280306895059404840003281107004211900007803000c1c100e10305003610241000520707034400130b68955080c0603040c840c0444007800c1c00304070700170391496034020080242c80c40c51f805a403208010044071420b14070f411150342d400145e00c915044504145a0380010107400d0f0300300541c401101c9204008001a040c030004014040455903076804d07004501000c503178018141c50445c5007034800d40746100c407201090383c14255000000c0e41c105150742c3c0c3c04140030040544a598488040c40642030303802680180c0c9241c40c0e8060500040c0b034000300d0b03000d0400740315003003245d0359481 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 658168525 1250 658167275 658167281
    0x60306070c08043f060b03011e020d2007050c090103080a031a0312040305070b070506161202040e01062d052209060e0903030c16062009040f 62
    0x7001000941c0800040c4900800c00002007203100c415500c4066031803015400855288030303a4a880618008042007030f08001d65030242c482c081001340d000f800364445482140c94803800c8074404a64154000c0362600f403c510a5025080410800c0000c01c41c039151a81c041e10507a024007415a243e0088000f01c00c00c9040c1030000f90304807640048080c0c80d042e0848811801040015815802c54030030207103c0c407050382c0400080841c0e1108084080d0f0343d92440c0703841443c110559101d90041a0180515008100003040c1d040d40301008181d001c03002580d090b004c0f41d0744055a44c450015074400708000c03a085180d400c2c0281a50700545440030240d0800090600d50b8014402040740072500502e144041e0f031240300500341e181c44e402e0ba5203242d00c07040e0403009400c4090340c10861200780d07a1b80042181c0400707000709641043c03c40c03000d5441c50038112020a6a881034000e0f84d044940d85201501c10015941d00815068048142084143c000c903046a2120f034020501d0912a6007415944410080184 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 658169775 1250 658168525 658168547
    0x31e150915031c0309080a05211b160c0f09180f0602030408040f031545060e0f060115020c01030b1f090303021e300a0201020903070e010302010219230606030607 71
    0x9104610303030f00070018852b10f9030102201005107050340d02c4180000c0d100c035621001a100042ca804005800c00540004840e040e100c6c22904d21101a41640440c1503002c28a0340b030b9401140150383e0b50b8580c1804000e51246502c041c100e81d01c003074030000034000107680800c03c003082207406014040d1030b803141c0c40310307151404160121540f01c56604044840820040c01e020560342c3c42d510f640041d5a1640c0301140d98032100404550404035511140c0c100602406014042c00108040c01240541e402591000c243d00c049040c182d990010001c0c41d136451449440040c403050022080001d601d500400c024400d110480141c0300d07196540b043c042c00340c64405200c2074504000d150b0190748844040d1102403c0200d28191200d00c0800f038100c51038200103240001c465000940ea54407604141850005207500122580c0700c51070060005070380c049040d299506603d8080c4c800344816040c00528070030940003c2c015003c890030f07119040c0780003258043c403c260480580d2000d80e00e65009544940140d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 658171025 1250 658169775 658169791
    0x1110d0f0c0507110d17220f18020a03020405060714120903031c150f080d020d08060607020117072001050601090b031e150915031c0309080a0521 64
    0x4d084a90080c103100c00503d100c203014111001c6000040f5544000c240d2003440c441024980118040130300c910b495010200416112010340380c3c05191030318010b42521169035482d40e0640009030000320f24482d030155405008000c08681d902e034401e1400e080221541c0421820314096641c0c000407500c01e500c260b9000010140c059442c01544124101060349030181d0b11103019520086e0458044141054201404401810280a500b0145180e103801c86400b203072400c40d44510580c20190340c0c04070340c1682100c0d0641c3c026494664501c0184c403490441c00301603001e41401c0d81040300e220b9021840004c014002c10011160f49401490360b0b082c0c540c115a424003040803c1c1080000309552001143e00981c1012034030113000c0104050051002e0588041441d900f1608000d0003619200c002e8581000d4804014824000c80101003501d41841d00a001404105960200c03030060281e00444a859406420380e0b596070405d1310040c22541114a541c15841c43d1054141c203c51501e0320014051920 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 658172275 1250 658171025 658171043
    0x10509040b061308030408060903030408040e19051906051519050d060f090b032103070309170403060b0108010e0f0a0b040e1018020d020d0501110d0f0c0507 69
    0x40001030001401000740700d59041002004040a0442622545405003a112000d0741d501c0d0301d40080c451404401030030002081e00100706000000d1311410445007100d03108502ca590681d503d85040d52844078210300b441120f400e0008102c03404903490304100600c641204100981c6d40ca4805200c100c041c010340d00c0d609440100000569410b003102602c60100d41403905510b06600c0d08607060a13203215a010030000314141c0030a0004101a0042c00014403090307004144024510003e40710080c0c00c42c03003114001c400003010482c010b1094001070081900101e2044400c0c09442004040d03a00501c403d0303580c9807501c9840501c80d845421021f040300e6001040d11216281c5044460907200080c10302519243d0f03554460700c2d1902c2b140240c420851149015280c030700c03041d100350420b48501e582c0074409445000d41701d0b0016541c482d16402641d8046d668500f03014801d2405600404281207c420700f0703034003c03d101000da641d03900b0036840c5001822090204400c180426500c9000c0c0348001804812 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 658173525 1250 658172275 658172287
    0x5090a0e0a0e03040f05010212251106070506010e101a0901022406150f0f03060a030609051608160b0d0908030a0603021905030d080703150603090605060f0105 70
    0x34456034000e01c00400014500d9014680b040c0f81d90711a40c801c8900c100961000c009540e018400700c0b0b1a120000406490f18101c0d03482d4009806107042001c40c450409600d1740c040c400138044200c0094001f030f188580d1910207080160791050240300d0030180d884410000b03070310a0341786290603085801c49084030320603a0f2004540a540d03081a100b25046204402d05810400210000079005000c0000d440001741456814406225109900c0c4680034804004419130400450212031501b500c00f00826100e46910000602c5281030364406409507040c400310106218021808483d030181e142c0190304080e03039501c030311a00c58079041d60080303c9005200042040300e00c0007005002e40a400480043c5080041d5500030231604196090390010b40e0b541f8045c0304608004c2440e61100c10032a43c1c980d8503e180c0800255039042e04c41859040140d8032001c91512070107034206107882e030100b60000d4055a101c500090052400075001c0d5005820300d00405d48a040c16107115090080694480b842c0ca1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 658174775 1250 658173525 658173539
    0xa140a170c0406060f12060b04060e0406050d030503070f0e0901050111030c1c020c1804060b03070e090114061008010911040902070c1a13030b0703111209070605090a 73
    0x1028a4003011203000d0a14a2140341c1e40340d1068070050020354039103042c0365070500002003101000726400e8000626102c0709021800d0f2501c1a602100c9045c58500c0030281120007040181026501c81c03500a203104007000704068000000c0d5104907103659509107400002d0780101d90b201401c0402ca90050714500061049520522a1903000e00e10501100d2034602c1d01c4038000e10300b0101d014140c02e03010240651071040c40d414002c6849080048640e902441c8000c00320000a04020303000a0820307a482c034940c2c0f81620305000300d400804134610806040e18111100c03a0280a80d080c880c00c2580e24000050f80c41c0c03406030414100100140c3d03903401075078201603a0ba001403803880b800941c9808184030004a220f054001003080307a20401404059034034044912040d0180c0c4040d009542e070040c80030300d200701112050a002c0701d8020811031050748450000350018481c070610214101c8001402d480c104a08004080c0110380c00c10448058503038600f02102c840c0038400107680d0004440c50108019 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 658176025 1250 658174775 658174799
    0x1d0d08090616050d0903110904061103040507050103060e01060f0807021e0c12010b06070602090d080f0c300d11030f01031e08071209090509010b0a140a 67
    0x4a2150010500d45016000000c4054000c60a004508030050100d0010004184034100d1031944c0f07424401c0c001411076843c901c401d0403030b4034054002d411440004040c414503402c43c8800c8074161040a540381000d08120b602c840050240c1c9010034207000001418400d502000c84c100c840d503039220002c201c14442d045541c101c0140030f840c01c52061540c00701d04884a082282c0c034030a4a9002494603452071824000d00300744c203201040160b40f601d92042c003a40c440c034003145c079501e40c482d0380182e070741d2141400128a60740405020305034890200e64400d5408254004007081a03080f800c07956840304904101c1e45103842c4500150840c1c403d140207804440340074000e0b00d205201c0610226411a00381c00e0100b0f1500b0440b0220064444c00c0010824003100c10f543d861804a98001040701ca1816103940d10107108500c802041038140c0070401020a200c2d8520740080c0c000018240011b0410407401d6011307014039802c46206038440320717001850010218a03540b07840806007004208510b011001100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 658177275 1250 658176025 658176049
    0xb030709050415080c0612010b0a11010f0f0f09110f0609030d0804140d05040501200609100c032c28030f0e01090308030702030409020c0f0d1d 63
    0x501001440100e10707582ca50007844003580c0d80e1000088110302c1e000c0e04a21701090303107811500a071400c0008401034041001003506580c4081052640c800030a40c0031150300c0c580700c0800c1481d5207003104081da03d00c800d4100c00c15000c4514001d1007142600e008850072610500c00080c40080043e10690590410f00000c3c246d980f4000c000e0750602030100702190402e01d00750703528000640150104020080c12031590300e410f8030008007e01d620400488068820311070350091505002514544000c0c00c1081100d10001c0310045050302d0090500000655450480c023444c40186802e01c1c1103080f07618444d202e0040e20500495a40003070400b484220b0740c0b01c5071000311810b0240582085c44000344200d5007990381c903004212140100c2daa0a0034001c050b058211070007810000703004100c8100c1da900034544800e507074018690503a40c1c0c450031000d030305d0741c4641d52151545600204203d103008070007003512030102d240e0324199810705105c001c08030340c181d005203822031000d05c11100403040c50138841b8030001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 658178525 1250 658177275 658177277
    0x50f0610050c01020c16080a030c021c02041805010f020c0a11180408030109050c0909071218080408010b060a05070f050309130b03010c020309010210090524010611160b0307 76
    0x2140c841040c00083c20f80c1d00403c00200c0d10b44c022444940d83c10300d030118100040502c0f4001d000341e5105503500a11011000f03901034806c00001c202241d5903d00c1608441e00180e004000708180240c1100200c0c4908120000303a40c0c551074075280200340c0d20707240215004c0002d010f024000820040c4d0314080802d03020000940c018030782c1c200403c00311034103c00c4c02c0e0285009510703c41d120361401c80d0120a0300c9004001c107000c91750910011410741c0303903400095048111400c2c490540088551400c00130000181596000e0b80303560305490030300c00000014010350707060030024898210802d0612103540704002402c800201c04020200108442810440ba90781c031603401c0d01d00d44281c1000150300054050b5028100d40d940c0c1c91030020903c0c0034401c04030030900b140059424540200f00103034440303544c1d0050300b602d039840e0046072003045803e000301050000030001500c8259444000b240d1035407070074015180841c46144407180b004000040200c540306032000704007441410500f400d6050382014103400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 658179775 1250 658178525 658178527
    0x140102090d021c0804120c060e0d02010c051606030212060f030307030f050903010f06050306360a0204050702010903081806013501200403080406032a080103031101050f061005 77
    0x7000184d114000300300a083c541d89102904000d820812a200855481242407214013022200107440d007010541078a902401c00d1410070800c0d040403814024802050240400c01401c00b040c000e4040d030262500100c04450b0800c80d5462805001d46400c440b0706203030b0301d13900034040307000060700c5040d0a145000103860300360b06040300034001c00d00750303172400c41541034480d03c940c810310841c101008155401891007100d00124030341101010040030603610f07500103401d82041c48042c03210080007420081a4042e01c10000340c40e01d0075000303009180503101140000e10000200b003090307038101c074520705040d9918042d2085910313203c01070703240031901e03030b1034417011403040d48201060700c42ca029246804004c240049021090841460310710351103204070502d980030a02003480410300e60070558041d41d5142c240051110b034010f9080100c00c0303100340385052080401000c07812050340450a41d0480e480f07500ca88220705651a1414241c0f00c0840706a20320b030b0346000000303034030f1300c0d00f5485040d068031141082 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 658181025 1250 658179775 658179829
    0xf0503041d1618050105090414010f090606050a020c0904030309050a05010c030b0301090312150f0b070605010608070f03150807240e01090303080c0409020412140102090d02 76
    0x7500c988880c41050300090407214104090350841030b00e1504001454038102d890414004000c0031201c2c0703540240350410a01080454545c2c031581c0c48440e030051800700f60541d640c1d44a0700c043c1e86002a014010302c00303040040016219000300191280300d1040e801620340300141c80103200c4441d9009006404064450f0b40c3c900208030240925814140134800104184101c020003400355042c0741c032000d000342e14203051000403070380c03012084400c20100c0300302250490601d00c60310319980098000c0368401d00030950018881000320002c0840a03c00e043c00c0c002680c0c1c61100f60340301c5000300c50b8100031610050720306030100c0c880c0d88024078001c0842500c0812031780794403002d46010203d402c40c4441c558080d542c440c2d02608a5200e031551086890700300390b69030340d90f8002425288244802420301c01d0800c08100b9080b902400d65000d0225803100f1511b490f61400c0d8a1007440d071051080d20a84000c01d074010304144180221540540041d00c1c81000d81c0003035092041c0301c100801c2d40040340d000c10040c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 658182275 1250 658181025 658181039
    0x6030804031218062c030313060813150b0301060e0c070311070b12090a02031605090f22060e0a21020d090e0c0903060703050a0b03190f050304 63
    0x150000d10b00507120450b84100030680070b0b24014641e80d402c000c0f52a8a6800c001c86075000b0500b4080090480d0340c6a00d407a4049030484040da10202410713071500000c580c00c1c840701254824203044882c1942c40c040c2646a00d440c40e103031140c40080c007a002c1d50003403c0c00c001004898004035400d85001c2d000140e40c0ba034941c0c01c000082d4042d980f500d40604001a00f0b401d0550280003021502000d401500c4094500710210081c1d00c51101e80d00d269140e6440050030031070b0148651203c040d0040c4c103552448140e00604c81581c0454010940301c1c14004000c01c283d5014420307028421043e000c00100c1c00e410031140185000c1d001a41101c0076a110140c0041610cc14000e0001c2980f1840205c0c00d0146040c620900c3c90754000580e0046600803209000ca042d40200b081c0e0840e804002d0600c060344030890b20100900c20340c02c006030035109150600080036030550150384545040f007403c0107244400010940c070f40355580c00404c052a007000c2c602022501402c0010300440c450f4007141d01d025540c80e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 658183525 1250 658182275 658182277
    0x150311070b25021b0111070e070c0c08061308220909050c0603090d0c0c03050607080907080a0f08090111061e0a060501170c041a0301080c030f10050a060308 69
    0x1981c14480c60002c01014901c80c1079224941000300d0b00c0c00645401a0540114400c0c801030038585410000100c18802c100f102c18841000a0914400303040041d203014200038000c00194403007180c440c806590005800c440119a06006182c440c0200c62008101d860300403440d080b501c0200401d01001e190510a40c100303194420003820722020224002d4441d0070301c0d1b402d005010000c0742c0190740400c20000306801c00f0400000c044141d08240c0c18040403400c1c45051b00966401c024828440c450a0000782900403031038901c940f40d104112003025498843d0f454443d03100510007801602910b2406000440390b030090000054189407613800c03103002e0380019151410a89400c04c010564100442c5404541181c3c189e100600e440180080351810000070716848013090b02003810a90400801c0152103031804039030003494501c1d951442403460300c0e581181540b0a10441440340f01b10480c0505604001c1440090058800301a160120703000304d61801411000701501d445a68a00000c0b0010341160 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 658184775 1250 658183525 658183531
    0xf061821170f130335030405190f05070501021c03020904200c0601141c060e010c020f210f18030709020417010603080405220c08070f050301150311070b 67
    0x201ca4805098590300344170042203407660100c80390036000c017180300e03c880b0840042e07245100b010b819103650b580c490818a00700310820100044203441c0c225000f0510a50351703030f8600346a0050301613460103036480f00107a9071070302c4444d1500c81140301d0925161003076001e41e002d0401d01e0400b03003011038501070740d1611042c1102206a00445104080f4038000000400c000040c0904a1140d41c80c0038140c0d07000004941000890f000e24102544141190400c69643c020031445440c02c8008e10004000040c040d4030384800300003412441c804c881d800c1c1d074103a1032500e0417190002112032107841d01c94510b58002c2ca030b078451000c0c42480103940b82c0b0160f441c1c40812200000701031400005031201c3c1800b440d1402401400c021802581c1040c02c284041072440301220200e5004444000f140305424105041c14103154040101b01c614040c1400907540d0054806d82c8110813a9880759000d00280d401902c82f80401c2c000c2008413581c0400510610703000e90f1001030800340f030280450500081e9510010303021011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 658186025 1250 658184775 658184797
    0x90c01110c10140a020f100203040305041a070b010b032a031302010917070905180c01050a0e1906031401210311011803020c1c02040f060f061821170f 66
    0x20164101c1b0507106225403071181800500662450405440041c442c1c055801014840603110000c4000002c411045a5003554450401e40d05980d66100305a15504204d0b1415440d00441d0501d0b11ba030500b00e040c000d845507081c00b0041c20b54484165940c1200da080c20124140507000c5804110103502c1d03854859501d0103840180312840c03c1c03401410a0792000380600032404c800440100da5010046420702c4907081c2843e0154651203850011154014540440d0390400507000c4034500c00074100014000360349180d102070086618113007031400c80a07024032814458160b0801040480440b0301e000704006d84c028a0124002c0d550140742c41d0031280c804000c9001d803015028407004040d01400b0145951508681162000c000c5090007894040850b800a104958592802c2555082d076408403010b82802031410061a0b107a2030043c080c2203a000948101410103070000070107032540c2c4c40000301b8200e0440c090b98100c209640780e5245800507980c1d100d01200c14030000c04951503d0707001d44050b01c50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 658187275 1250 658186025 658186033
    0x2090a09031e0c030e1c060b040534020312150a1a0d0e010219171b07080d140702070e0c0412120306120308090c01110c10140a02 57
    0x1003071401801c050712410b0140b44550146095001c46904032409049950300760500c49401c070400070010b641c1c11243c10001800c82c02e04100b003030070300519500200c211501541c00308401e8035030041d01321510075101e50124990310100740401c01c140c5031207284200ca010a0040303d0070702010200d6000c0c0d441c000c40b1000a40d6018a0640c071603403900251354801044022421181c014050080d0722280c403413201c251a07842c1d110328103150707040780950450354043c07034000b04460000d6400310014001240700c1081c0d401500d81c04049a05107050095091104000c00141441c1203969668443d00307030461581c01403142c0e528190070700e071101911146441500305078050800c0070b0078407414002d030900182076048190410303c0180100d0003560500d00d0b031143c0010900100301141c6100300c001d03244c1a088401840c0c802400700e0105500803c400d4042d00d494826a85802c0040004490300018000401011307403048440786074500b030480707001c1e5110049180103030041c0d500280100c0c117030380070b41c44500060380 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 658188525 1250 658187275 658187291
    0x207120f020906100813050a1203050601120209090424050109020301080d020303090d050702060d0f0204030212060402010e09060301021314040e071404022503180b04210203030702090a 81
    0x1038020000b0303070300401c101c55a003803400e881c03e4028542c400040c90002c14168401d1120705100003001800810b0381e0000881a885100120050152800707a400300d010402e0700700801d152003182d0090319904403000c0c000c11040c0d0f0b21a1640e442d0003900316113106031300300907800249003401c1d40d0040b0f501a19200a015070340e03500d0004c050346040f010ba109442150014014442406c101040d0600b4806151078182c4e11071030f5900014070703903101e2000d940b0030741450080052084807c0c1d802900890703008860703001041d2031104640d41c86a01c116402030000d4030800340000c0e281b070162a00390704040003400050405000c4140c03007460b180c4035086100d440b42c0034110190a49094010412002c4009020700801c51a115459000e80c05415400b03120b9600800e8942980b2081c0400380501d0400d001007003202c03200c6041c06000d20017180310b80c400c04030b41034001140000d0601c003114101ca80c00d1034545001540c3e0800b6040100044d182241c1c1400108030070070242c0e40703008509000300303080300000036014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 658189775 1250 658188525 658188529
    0xc0507120503130602160201020d0e03060420130b15030906070c0503040506040605030a180803311211010501181109181503010b010503040201030c110f2a0f100207120f02 75
    0x90210144204010b8150f44c01031035901d02141560704280d01c5503464000ca00c40c0750740e072407400c1c50007093f00b0b411440c4e201e04030403a5a155040604500019640507500c424046020045440101d0306108160311802c04503074440d12800c03050900b0703806403059a0901e80c440c3e00003045903000383c0c00000003e2000c4144104a14648034008600c0203050081d03d401410f07640e628828000145042000343c941c159030b00700100c00f41c1c3c0c55503110a01000d00600300c05e25140141081000c5c1c42514002006ca885040708184144112410384174051488403890710820a508054040c0d0342081d5040d0409119034401a01c46450b00e00b80072503030004849103840d10800948800c00c00d0290184281e040c580e0450050740c000007280d802079028640828070484000080d02c54000d1801034044500c24100700c480582d8010681c122079801c00c0400d910840c03000040508069500f111050f4000340303800f1502c82d685020000e9a1084c0c030507005031003580e90b40700d000210041c0404000e607410000d000c1c805c003c40c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 658191025 1250 658189775 658189783
    0xf060c010614030114010303051b1203090d0f140921010c1206060e011b0b01030501050709050102070b09101119061407090e0a0e010515040c050712050313060216020102 74
    0x850340a400800c00a0144030003172001d4181880003806000f070025175450116440c01c030703000003c0300f4001180c6071116a00d400351402d9104503100780c524055804042805c600c51080e003a0015125603030740200d0070400040416590200705000e50002141007180008603c1d4484030062541083c00081d060071203c0020345540401d00240002618181050010b00c0c3c0208140060710801c1c0b0b0a016107242c251242800002c44002c0580010a850000400c12005401c89440303544d235076807000c0d5180d0307480005a0b0f8a503018001c00d0f4a41d07009200d030584508ac10105c1a602000710700e0500c1050303070132030151350070800e0800310341e4500c0141402800074480c01b2f008034031140d00d41c0001e800c01460301420041030031645010f076880c144403050125a0100da5034200108020024000300440d0600b0030b241d54410708030300d20310b03400f0754100030f52001c00c940907106641c400d607007111500c8125400c9510849241c2e100402c1c1e010100e01803504240841c41c144041c100e0728501400b0725580c1440e500001e858 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 658192275 1250 658191025 658191059
    0xe010914030708160303180c03030905060a05040e06030c0a120c060e03060a09210801090509010603030c032708060718212d0b0f13030804020f060c0106 67
    0x9034001c00034000000c21103c00c4034000e000114001d481d8071024a005c5001d81000f00300040403160004d1804240100001c0d003d00320383c4661190f8100590342c2081c400d01d40900c9081c03c2c04141b0610080120024a40301140c0c0140d000701075560300b02148000400010700c1c1d40220b0140c0b200d01c1e01120811210002002c00342034a414040d0245844200103955000002c002d8101c0781c5c1c540113a0410480741c1c01e1128050f4444070903c000e08ac0c00150001d119000c24402c8120550409000c82ca803000c06108a000b520b40640e03d00240c030380d142d18280d4002c1514104000c903111411008031044540e10080400740a03200080d2045060140300100310102e000c8003032690000d03251040025500326100031031031072401e284082c100d0845081140c40c0414802d007445d0403804140802800119804256100c0340c8203880c0706031140c64203620300c502c2600460b01c041840792000000710100e4080d402c000e40c0544014824140611900d0100300aa0000c0d440344c00c540e91101c10500060070303408100c0c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 658193525 1250 658192275 658192313
    0xd1b061710051201090b01120302120a08131e03031a090105130c120203040f0309060305070c0b0c070203012c062a07140d091d070e0103020d0e0109 65
    0x4420705282585140c0403420744121403042c0c0c0303c2c8442004141c800c1d00059282900601440010741e50f498503003481c5510004200d005000d1250364030369115030030307040d00c041c05903d903290304c102c0d07650749202e0503c20519401502d8500c00d05032204400c1d006070507981362280c40791780e0120700520190b41e0264030104010f55035115010010050180b81c071030013501000000d150790045070f808d489200036a00d942e00d05a250024074000002c12060041004585010b45c4c4079950b60030a4561f1980b045041383c10507540180010911500440416010740c0443d030413111b0034006a240c840c06500090860316400e08000780c004001800380005e110b41c1c8484410408000080d18143c580003400d0384880d00c002c8103514520301d00c0d1003260a00c041740f80030303601c5c82d40c0d002c0c598140c00d080245150755100321003a04180001c83c1c1b80c00100b401813014a800440601c00c400b940382d142ca902c0070a403440081204002e040507828401980703841340c10301504287c444100300026038412a81058400400c01e030003120 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 658194775 1250 658193525 658193567
    0x4150806030a0b0112200d080913090b010e070504080c040c050c0d032405060f0315060c0a0510180b191a09070c020d0b0c1207050d1a0105070b04020d1b06 68
    0x460691200e015010005030f10108c165070700d07100040000c00552401241d0055207141501d200100f1840c03e070124162a00001d1484031f50ba26044200c520b8840d034000d000b059045200000010708180c0c220040c5650750b41070003414007030404086440c0c11031043d05400040d03111050f44900c140325603070380948400c1002d401c2c01c5640c10240811841e20444841079400d50001000680701c801400e294408148010301941c2c0e200c0e80091065610b068454054849010743e08011914101034410340811121b000304108421006888206040700003c114044400000c6011108030515114142141401580803020811080140000c4040003080341c0240072040c081e00002d42d40300e0040107245517100c1860f240070b81e286070454082e40202a0810380711101e081c2480301c081e030003c003d8001150050350030000d04c0b1517100380da180354080210003030218008201d80d1010070700c0001d01c1688240040c00e0170200f00c8240d910289508004a0700d802c15141616080c001c0943c40f0343c030303080170700001c403480307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 658196025 1250 658194775 658194833
    0x140c16080610170304080a0326011409040302120d1410050a031203140a1d060402090c0c0a02031b03060703050c09010509010215070e031204150806030a0b0112 70
    0x42c034100301d1502801103600045100301ca070441c410011034018000100580390000d00b40c0c600602003403032038401200210f01e9008445400300b140385100341210b200031400c0580903114820701c00a80701c041c00960450003034002d00e41ea580d24400041c107110f042d43e080016044001090400e20100c003030705010400c243c3d124104039540c0c5d007411000a590f0089090f11585e210034500782c00900281007900030b00d07007101d4200018045a070f4400c0034414490100386281c0b40400d14001c0d00c9600c00c4400a6100b80703c500410400322700c80c8085c0402200382e2003211458a0140c0003c2e2406c19a200d032410310242d4000b6503051420309116240d080162810700f4400d80c00c0c1011000014002d03003224504129010401115581c8204942c2e840c0f40c0b1414803040742c506110700c000f00041c80003904e05001b40b040382d10464400042131300302c600f04e071140002d4081c3d440c011501160161b2010300000e40c1803013502c0242003c280310b680280d0003050b00c0021403605c21030901d808070b4440700310400c215605488400f5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 658197275 1250 658196025 658196041
    0x1110405060a0e06040306061404051312180f09230c0403110402120412110c030705040504051509070504060609050102030901080a020c01090b0402040e030a0c1101140c160806 77
    0x81c2e407195080e03810044100d501201c045a002d015661000e0682030800c00c0010301050380c911a1515400f05071001d1106684c0d0f0b01c1e00c2d00d00704506a0b070082c03c10340103446c89251540f10300c81c0403d0030300e1281c1d600d550382a80c17007400d45ca03075071041e41000c5c120594a2074200d01941c0f2600040c440030320a03403411001440c0c07803401120103021701c0c8405040e114001d4210045035999604540c0e40e80c180c0041038009003840c0c02c1c0004e20785148403c000200b0300c0d40601c500000c000040701a08401d00400400b03801d410503003440058040035104485a05ca0b10040d00d0301e01041c1c0f10300c14810810400100015407400007003109030b4806501c15018001440c03014440f5981c0032086521760102070800410545076006454028030a0092001e0f042d440c0560708420004d03801a40c601070ba0086409110007480fa0911503120b1150003800c90200e00105000b10004a0710304640520400506180b4a42c80200503c2c2e007083d4003607282c0a48581200c1071141c0e011603416000d201500d920001030101d8644060 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 658198525 1250 658197275 658197277
    0xe060f091b07081606090302010b0f0a030f050c060c0307050d0f05030a05090c130f0f06050a030b091510150c17220303050a111f09030215040b06030111040506 70
    0x14400180000144070050015007012903400f180c4508040c4c1001c001801c0000c01048294070880065003480c5071030181d07107030a8440040350780c03005220048092469807200280485240c00302e80794040c0d84030312030b90b0740c0e50f80000d00300a00200300138542c4c521091230030500781104100001c05001140c2c3d80c402082d5071007800d83c1d611900c02c2000040035200d8032681880d0100ca800c41d0765003d41d04e2015400210001d8104114102c521f12040c050514001e145a094400c54000d1030f0300b101c4401341c204081440303150402c0d08806550141e0341e251032640703208210f41c44103c1e503441c0d101c80a010200001d02e4402040500e0400c40d140c120700d141410780e036a044042c191048840c0a20b00400c2d07004180c0f20342d03282414041442c1000c01219540d0349009400c540103000b604000c6010f0021a8640311004100c0c0e40e40a03c5000341c508104a04000340401070a4500b41582144901e08a1400001d180007025018038010781401d071061600008040c01d5903901c2c1000c1d060103000b0712080103d43c45d044c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 658199775 1250 658198525 658198561
    0x91a15091003240e06240105090f1c0807050c0108130b01090b0a05030106180c0f170a092405061e0f0111060106030516030608031b0f03040e060f09 65
    0x2c00c143c481d1841400c1c0040241100c0d07500f141a50140800707101a030380d89000494100e41c8540c07204400044441c0c01501d40d0b0166904968210008180301d40380c0d441e204054039240c61021013009a4600c3d0741c0c440f00d1154001c020120340540c0142001041d030f60b044140164400600e00f0341c1c0380814480d80d40c4041d01001840742602c1c10380c442180c4801a90b4040c0103a0180001400820402d5681d40070300003c6080c001c00800c955240450801880340b165280564007405c5882e10440049150703a01d0007044001444261415600c002d0203000600c092556003101140040901c0842041107a510444a01600d000c0c414600410030740401d0b03009030b200c04800700c0100c501201248000300161030b041480c18040c0458000d910020588030f0b0541d001601070482070400d001c00541140003602100c0460091131180e0340f06105a00000040032a140341005810301510302c0740c0c1d00d4000a0740b071604190000c000c40c036282400c200c00c80c00d14908032040d40c0e0702150021524101050002100c0b0091 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 658201025 1250 658199775 658199813
    0x60a092111010c0525030804031409041109030105010915350f0c0a0f0506070201030603050609030a030f0204062304030c060c150c12091a15091003 65
    0xd10003030341000340680c4545400c141800002d03c590030114400814942c01481210880c00f8140c942c00b114403e02c185201e020340e0725072100200c0303490303a4405541e031040ca204a22000001000388001a881e18003a80c000542041d0085403103003600c204050070740e24140c00c42214545001c000520785140e09505104440c2c1d9400070140034001004011208200301c06442c24414580c00c4440d0340100000b5814110040101075440120a201c208103150b5158030420461801518042c401440c100d4002d041c45881410000b031100d50f00c1d81d4082c1080404c07940c010040e0000305080400f03540600070b090116240d4002189400c0c10038102904642014005660307960040360000c80800c42a0b045501a640103540c42c2601039507a64010302a4903400e108481c5009040340040481019001b028a018110780395200703880036034081d00000b840c0e01c42003500c8246139903594000301040c80303420303a0098181c2075900010012410902c1714844000c3c0000d903120001d85010408109017005190710300300b00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 658202275 1250 658201025 658201073
    0x30f1a0f06100c03120203010b03090f0c0d12110f0d020709020702060a051b01020711040c0201140103141e0f160f0603230f070906020a0510020c150c0c060a09 70
    0xc0c0d043c112017000080202030050b41c400800400c180f18104003071441040220100d4071005484100c030350301d41d00008c1000e0b400216100120300001e0aa03401c14a004c452440c1a810198110038801e01d012107550030020035402510701985250345c1800802c014184ca000150f12303003110f5034045034088c071910807180304000000c0740250100c1141d050780d40ac000d0302c6000035516090a400c043d012158000345240c071452070000740d09140d0b40103000e40c3c000c000d200b988140c0640c3c07940d150a00111341c000e034008914002c1104200d0001e0301c000344c0403070386a0484001e00394843c601c00e43c2c3d072030308a82404c004070800d80f60504111400040102d6002e8415501d03020458103480c544d20070b26560b2103100400044545010840320b603207ea8140d42c0303e458160385080b80d0541d144016a181c803010b035009402c0390070113002da03a407410194004041e0044e0030310440e00809103164416282d00c0081c0c1d5205d0440750006468a156501041008e411812421040124115681d290a07500c2d5842115400c4420 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 658203525 1250 658202275 658202297
    0x170307030605061908070806090601030b0301020903030a0305095a0307060f060f0e1801110d050703150303120b130605030615010522030f1a0f0610 65
    0xc403a810010081501902e61a00c890403c00644400344060700c0c007034000b41c04040000c90103445001c046c6e02465024208101c2a01c0310001103001d402200c0000d90159000c0082900c2c40d203080006008208d02e07658001000d0a1400409042103c0840c000305c0c0020342c2c041d41071000c0c031501d205034030401c6410404248084021b0a039584c0c2060f0074014070038840c5018100001c00c50120040c11a1440b60104101d01c4c00d03188c0e0000c2c225035150040d82d101d4808400244681e56641c0090340c0c01550b400e00c03100212080c3c0c1356850a41d25003c180720303401c40740442c20300c404007490702650390881800e0a042c4850541c0b41041071203812103200c003404206a121105248100c1640024090040508994440200c0d800940d018002c103104960080c410040020750040240549a01107941696200d25081c10440c0c045401c40200c0300c1d08140224851001000403414400702086500c10000c0c0c16180010510741e042107840103241403401c051314003c0102d41c1e0741c2e031140521105039a080c4008224 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 658204775 1250 658203525 658203527
    0x203030609100b040f17010c02030a050f0903011a0915090610030e01140603070b070c1412030711011b0317100f17010b2b0303020705010c0c170403170307 68
    0x44080d80603d100d0200014040740100301c03082c40209682c030b901100a003102c5d041e201c09013220701c140c06c18001600188101d0030454800c0c2d00403e103039100054180d0a014400000a0850300842c61030801800c4410300104282810348600e544041c08009400c000c0802d940824507800c002001a403040040b1504103410600952106c00d441511000811030722404580c0c000e515202a078809118dc03040390300c0041c0d1a2204000c8807102c0b58010300072008140740c45902c0c0810000a802e80d0342c018040d594203010300c441000a080c4040c05100740701002005c4100140018039254044a0b0300b030705a001076004280c2244403040d4111705002c5005541d6511140c8408d8203443d50441d901c50000c00340001400000c2c00b0200840c804144d0007000344401860403c1220080d072000b805045001030001f0020b2a03c000c0c95950490290034094030b4210390b076444030b003104c413038805141c04100f91940b0072051064115084030105404141e03585403d080d603c1d42c50040c020b40d11060140b44002001958203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 658206025 1250 658204775 658204801
    0x9150c04030204320f0105191a0f071b0b0c19030210060b0c07080316030e010509060708070c0608011206020c150103080a180b090111011e0f0605060a0203030609 71
    0x10a03040c1c016080e21100c002038a412205040c3d417103429001d10030001250302e1411014105074240c44d03010325081c451a1440d5504031a20307055401c2c1a40c182400030850f030382007440050000c18070414090814410340c0c1a0014000c455030014405580103010000c11420000340c6250401d4803113100d02c45920310fa1030121b1038503042004451132030342070140c001400282c00000c0e200c0c100700041601c1619440d1802c199a0303002d01d19089400e40186250080401d0040b00c214403860010316001d0301d4040101d000c6180c650112500301c855820010b0000c0a0028000c0c20384003601580c548503401e0b500d0046001140070211001600311980018140600c0c1c00401c00c040b945902c41070b0643d071035a0342c0d0a00350001c0e00440c0740c00003c160040e115800002d450500c0009480440c080700b42001d1611004543c20f500d50035560036650341e1603042c0c0e0444040c1c082c2004066021020210b12100090300e05016100a603204074000c203030620043c410184c01006030b9510686c140c42c1c02c01542e40e109058981 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 658207275 1250 658206025 658206071
    0x1603080406120b10050a0318230312131104060b0414030a1502130e070c060c02030d0524010e1c030c1b09110a021b01050f1209150c04030204 62
    0x1000c003001320100711468210f0044c082c40506520200720140d8008202203000107141d9004100010700d1b00513080c1c2c8d03c2d5480d000c115290200003121300f00041521a0b50045505582c110381c01700303610b208881006000343c800700c6444030540b010700095180090018540c0900d0041c21075940601174280e03010385007007001e4808107400101c00042500e4010f01d44000b03622214910072000500e0801189484240010f180505850365485503035648030f40301c1c003004080b01d5084000318001080f240d1a503142601600d07010340349601890700082504800b8444626240c81441d05116080191071000d507142c40740300000b0015181c0342c0000044500d000c90742191981c0d40180251604e114211040b40c030801c0901c284c4206100c04c0041e84c002c24013017041c03130140c5c046071070050303110300d604108182c0180c1e0044004141810000e0503c01c201e803c064180d000707600550b800c4442c4104102c9070100c1048807818805060001d4038460518490ac6101c1c3d11407808040d00480e2211010b10202c0b01200c05580 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 658208525 1250 658207275 658207279
    0xe06060d09061a03030705060f060d0f03110601080c06070818090711100209100315181b03150608090c0402030901050403031d03091e0904050706021603080406120b 72
    0x181554a02c0e00320001c02060600c0b1400325640e911100071400e00000700e0361000e8100d00248240d40d144603440c55040e030f0003000c5a8108410108031307400078000d620009000c91203500d4041c1482a00410640391003016441004140d1152000c680c1c5a140c0e0170440b200d554004a002d03035078072801840d000e01010003030141b6030003606000230884e43c0382d071080303c59181500c82c100b0b0700c02040c040d41c01030080c1d004500700583d005c1070a009800c40d0b140268030114000002c0c21411040341e40e6815130807422034914050180003a201c0024a10f2600f60480250900c9200c1c1401c11803107040c0e01030401e80d0102402031105215020000c16400c050800840424001c020010365423480c005100c2e50181c0429074046000c01d0074074044600c0007624035403000381c6c0035818004605009014041006130046440c182280c00b000c0300b204080d42d1a50400c151107203014500a0800f5132034810000e1501400c501207200e0704240c07540c1480010826400c031002c4401d940f415990605031151034000600301d0f6030000e5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 658209775 1250 658208525 658208531
    0x3110f070f030303110307080105060d0b0a14180411090405030c0106061d03060f15060c030a0315080a020901090b010e04061403010c0305041518050109051e0d090e06060d 75
    0x607080c803503070200c0c9055920aa4040c41901d00411417601d55000640f0b00c030000c80c01b0040103011504004000e809100001d030710116120f0440c80c00b190030300d8040e401c08889000c0c154042441c0341486400000b4683c0300c4240030340145005e4503141c2c100d0401914043c40340040380041028000100152007100d001c00c00204076450752244060f041300742d460300b07980284000349400202841d011074401e00c02d0890b040c42c50000c0e51607807881e180300c490b17900f102d0398406024401c24058990401c0a131401d08820f0710001001d8035558940200c0351480d90041c841507125400c1c410060b01d50f0146241112116036000c00c104a5090050358030286640041d60801c0c038041c00015110b0901d09aa0610341d8154020490742c003c448089095560856020340003610b0508a8415020954081c80700c0007059401e080d001e64065440038250b65010348140c0b002da00994504101c0d580c00d80280300101701c060002c09550010b8440078205461911070441006080000981d00351110401c4480d203004e404410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 658211025 1250 658209775 658209779
    0x4020a120e03030a1112010501050a021203010315050609070f0318150c0f0504050d020f0a051306061409011b030504050310050a15050306160e04050c07150b0a0303110f07 75
    0x1a903c0c1c0040391145202030070700100305105a403c20486411006d45050020315a080c080156425481940302c00111710880251080c4404124040c601941c4603040d8070712544a003d20803421750300d0140416100b00e03010750170b01132040d401c0a805c80590419080c04030f021205031190032403180029002421520700390949600030a04e5030700c00003403600d0581780c085080b01c4500007202c0034000c13400748070b030041d2071a80500098030780240030464031a4010f050b01090358460700071130b12000c80400403509e0700e81c44100038001a43c206940c80300d40c1800f109001c0c10701e0151070000f0003100c1e180103540410b0300201a02010f02d84503000b11400382c04040d084803c1e21101c00b112030300414088440c401900d2421800580d060704020102c0708075103008004107441d0700d40203800600c410b600d004200a0040c1091101800d85a07405814801c24800418544520341da0500d0080200554007a107002c91030213440729603984d540400c1c2010380c2d805140800d0902e5040308218503100d0304000e0100107110300c402c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 658212275 1250 658211025 658211051
    0x5060307150206061e0f12011104060903140a0b01091805120a170108060f0a0e01062304091509050111040f1701050f0c0a0c02040e03090f1c0204020a12 67
    0x5094000c00d400d0350002c100d001000350080c072201805404550051030040c034041b0504d0314503050b00d200b82c5900300010304401c5018406c00c2e02d03480b036401100410350a41040040c040039440c1e981ea01600c04010b042c0b494480d070b40380120b40d501405250342150351030303070181c22000304944a1100bc80e8014115404550048985403507604442d541c800010b141c00182e0781414500840c3c64101d80c1e4180060929840ba000c180d610086e000700a0382c0e20655401114040400074021400242010302c2c4600001134407070445540021701e038500b6400382e807e00300c003c8001a1400300241052500c4000002c0c14003052810901500483e04516003070f0801040c046000302081000408640400540b000d6071113184200306d0a0310001c4805584841c20280060f0400032604001c2800701442d10f040302c03c020307540d40045c085070072003109020141d001181c0c2c180b203410051400c3c0c0d445039044508003c0e42c0803c0c244c009450424080080c011030f00448d41450301070048440c1c0e094000050018801205040c0d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 658213525 1250 658212275 658212283
    0x1b02210a030302041a25051504031701050d020a03060209150706060503190c05040b010509061206010f020307020a05060a110a0501050f0a020412030f141305040f0c0203040603050603071502 83
    0x640d01c1105c040080400d42c6a034407421180404401c180754241e0b5160301e80c01800300c804180c070a441d14000c510010342035044400382e0318407551098072a00d01c18001520070002e400303c1600654010702518131a076000d641c500c0054812203030700000240c2e50306400710110701c40102e40000c1c1d1080c064045017190410103181c04c02030075690143e040343c000910300200316946000005020b004450868801d010070b0515401c5002551010704182e4644468800411255803004400400e040c0c103030024400c156070f0001440642c5006480218240809900010040c41c0c081c0f2a00b8480d8500194900d03010b4040c7e5000c0c0700b01500300017901c41c409094144140a01000c40b85c016a4561440008110b041184213540c19039000c0542c00c3c0482803150b4050300c07100d032544c01e46400d00050041a260005100d40101030348001c2c0d130940b041c0b440c0f0f080103100946030428031030020107081c40103d00140d5400001c0e1811502145000700780c0b42c64000100b8100b0502d9000310403070310424900030500030b80000b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 658214775 1250 658213525 658213529
    0x307120501050a050c040e1005060703020604020f0f01090b0d1b0f0e0d1a0417220b030108120703030603020310051e090606010e0a0909050a0308071b02210a03030204 73
    0x38028480c95071101c400100311031086602800d9044248014002c0d200408416903210308460380200e805500d820004645401045044005034410b001304800c41c100090201c407500020381c0e407152640603181c00600f4052150152a01c0c0b40000300b96035007102c0c0b464001f0480101200202261000c3c00d07000100b80315006010768004c940100c00b42540350600c2403180e4002d5803c4000b001740c2c5200400b03103118510b0081c1017900c134800c04c11802e05155540000a00032030307176072903501c2c4000c0000d440b0142661034503910a581d40c0b58140010490120040b0740310041e101c0810b402980d5a42514042d40106081e80010b034041c403441c0c0344414086095440301c1d018608251440c4040c08044041d24040072003140d400045400500c0420b8007540104014400c0307440080000d6070f110348a6180604407100b0000640c1c569100304500000d040d08202c2003a00041507250007880000c1e880301c158100044501e0003801207941529000d0180c8806060392424200b02c003c2e90f20354089420300801940040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 658216025 1250 658214775 658214783
    0x50c011e0903270504180606080f15040209070806031e0607030e0a151104081501030b0603150708071202030a06051f2003070804030528030203121005030712 69
    0x1c10820302000c6108110040003903245200070340f228144000d20003e0400d00f401800c2500c602100b140028070103005802c007070160a030003060704107945500b55140c84000d00b440601e80d003418081c0030260326200d03403ca500c000c8900b462807541c1c0380c084c082483c00140c1200b0b2403c03e242d9081d5160100d001240b075030300032002075806010711800003a9885d11f80207008001042100442c0501d000030b80340d504a034030128407000410381010f60383c0c000d25041081b80d0859420031100c120043c41000682041650000010b500908280c40c03150080b071200c10001e0902c06c1404003200001e0f030818401d80808084c240e88480540d04ea041100000029090341e0065911400119404280211108209243c0c188032a0340f0161245011003581c2030000d440d6000b1101400100862004100c195000700000c1d4031800c003e050300990304036a0085200c0c2480640c06c445204450800425400000c3d992864211550302160f9100c1c0e07040301a400c40350b54845500b5001300440010801c013011404d401d40c50207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 658217275 1250 658216025 658216037
    0x308030c0d20030714041703040810020909010b0904020f040e060a052b0c05041103010603050906070f031a040e070335070f060908210402060901050c011e0903 70
    0x901c2c03000021039038012914201454051000442040c443da44030340c0a406088179651515448004031090304c0c014021200c080c2e4800901001041c03420401c0101c07140040e482141030036034a100040c100c58042c81602e80032000400e80c0802740e600c2c8e0341201c5031765081b520307001e03a07403941e0f0002407600c400100ca40b54422040d80340001480e0500080030448001a400c80507a40400d5503d85034a6640003002515030140040d00810300d516140f00b03000030102c09014480d125898114018161840100a801a0b40207901031103c401d400c0591f0413080c0300c40d81002704062000ea101759250610010207030780e0050400c0907400503004086031070000c2d6405074000b601f107230300e0100c44182e40500036580c25011803404541140c0442c142406004401e10030400820000c1d100c4d11003205960340000150342402e000180c80e062901c00703441458840408030b00c0b0329a185803d8000542c180160440107040c4180010021501d102c02c0d404212000244850149080a07000b00d0703000610344180b0403008910 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 658218525 1250 658217275 658217291
    0x30f0528080f101517010305010e0d0903110603040305120a0b0f03150c03190c0f03181203050c0423010f140d090c090e100605010309020904020405100308030c0d 71
    0x51586a0300d4861000044083c11151510b51104628510b00b6080010009514aa805070030a0b0b04e41160007140a40008500c0d201066a034a003003c0007000e100c409d001b0007400030070001da070101d07280c2804501125040d0301d030358503410291402d10500303001d000c01c0b0138000c080182801c400c1e40518450101500c0450011101a02707041d90f60708400b21040d41080f011000803500702410004542c403140162a010806d4840c1b451041940c40110b44800404c0d003c0c01c00300c030a0f0380c0c50312405800341070041c0164208074103510740303801c081d100e02040700130036445000160301411603008580040640045240080410000e08004044034860650001d0400e8101e4480c462003008c0110320802c07950b01140c608005580300c3c50082c580711404031103941302010002988070061060054103008800545a0703901020603510480e46070303810050601d0702e000007100c09078842d00000c0e68000d42c151030001e51500c4030151400740504a610080c102ea10020411100001920250002c00d00403401030003070031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 658219775 1250 658218525 658218541
    0xf05010e01061406070210030905030c0a020f06072303040f060305180c060f03090709140a0c0207080c060f16030507120306120b100e0a0e120307050403030f052808 72
    0x3c51040d034925132114040c8842005071030001c2d003041c01d22940c0e0400155480c41913071040c1c00c43d0032202103a00160009110f180560034007414503032180d4001c8440c80d140c20565030b54442c0407000095081035004001503c40c0e6943c13410030441d0080c20004000d4241d180d0f0b241e800801800007207070886c8411118981106640c48009550240405c0c000c0542d07041a448007403c50080c0c000030002c103000d00c9245400180880035100c0d10207200003500e100891840d280c4520010341d03043c041c04004540c84104104003015001ca00f000c0031031002c946031603484044800c801c545004820360300030029103450b4880d08041d040401403c5641c0301d0b182008000060700d0003541181c1c03103403007602c8521a10100b0307040011414911164802ca020b0740c4071800945840f9a0700f15004211a0b12803000ea0301d103400088180208502c7e002c402020000e1495441e043c48014424002d42c40000c05028455100048031406030054400030340c00c10303001040140b01e1083d0008040c0100818002103220500429102 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 658221025 1250 658219775 658219799
    0x909010c260403260a0b01081515090411040603020901141207050d0905100c02010e12092106150a0501030c0e060903150f010e06061608090402070f05010e0106 70
    0x100070310400c1c0c9074032561292819901410002a0a0f425078001c90340d00000500b81c1200700e0141444010000700092920009080841d01428a0001e8541c10780f41d00c0c880d5a500c0c0b12103a12142411709651200303002004207014080d8080450980c1c034011074045040c5034903501600c070711078090b41c0d03001d020004845058881c0c854507900075103444e60440002c041c180150010300014150502c009084a201d0b1a014101011800401980e45d2540e560a601c030303909008500e040d103445406030002030a07284014940e1710030394262500030720620178204031001c1d0501214510101d46000e40c0c0321445c2c205c0c3c034081c1c0010080c4180b0b100b61801e02c00454154802c0c40398407890708950f1502d0400110480400426402481c06598188101502c02d400a0000800c99000d00b000c0d60f000c603440c0d4140008103080d980003c0081f40203070801d05c0b85005226030a0303a460b0100d81c010324403d50303410001c001300b0003a10a80c080544040e82c440c1546003005015403120b40001e0b61003008100003900c400211083d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 658222275 1250 658221025 658221077
    0x20030f06100f06020c06090f1023091e010e120610090c050306041d0d110f0f03030c0a03090222060e01060c03080a02071a0a0f0203070f110c0909010c 66
    0x41c0c0c0400a0042a810440000c000002004000c54002c1031404001b511440e10180c440d8005002d8111075a00c0300c1c04000340030042040060880c1c0bc16210300f0100d401c00310b07182020016520407514503000c0740d016417050300300d280006e4665100b1a69144c0700744c1d40d40005a452036448270300b0320710010300d000c0c00348501d90f41d101c0580d030f5031440c507100c507000c0101070809020794110352031303001c414288100e8040004110003034480e00c90281c20310042030f80d1401e00004a03001e8005400070680301c4d0301c041000c4100c070b82c8071180781c030700684400030310748110001c10116000035040201104101c1d00a00800c2456400e0302032464184600d50b164020810b003410207103d43c05c0130034001d01224000901800c1001c0e80200e070101c004ac01c002d003944905101c03264010071001080030a07800c0c000c840d12503006078180c05803c00717025032850600090050034030440d0b884140421413030494003125a9011f01c04c14980344401004114182441c05805000b01409500c000c0841e00da01c0c244040d41d06002c270882c070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 658223525 1250 658222275 658222277
    0xb090303040210081e1303032906070c051021110a26071e030216150f0f0209040606020c03072d030302010c0e0d0f20030f06100f06 58
    0x5105481c0350f1040c0c0d10014050001c00ba84c01505036901c2c440320f200101184160060091121802035500740942160354080d940e0b01d45502401a82c5104090711044041922041d40c40c5561440701d41001c1c500e00d00582c0106a018020700100309506602c5035110700552240b00e100b00c008258911000e041f900e1900b0030035559882440303595150350041c0f1214850f8202c0c3d103d0314895601c415000d18502800301ca480001ca0700d008070500c040401c48400c50074005072401c04518008031445581c520485006c0000e045071f01d11070074896040f8182c0c1110f240300c6d40c1d5031003d0103840c605908040103500a80c1c4a240114505580080c40520000d441a1541d0018014100940c00c01040130a5540e00c1c60700105000045c062418884079005260380065020b9400000c12020f225001850120f0070790015200c0c4d07910a0341c200104d40351000308010594070055005a00b043d08405075110501e1344911030381b5000791700000780e26000200b12180f040c501400a0000f041d02c030500010f41f85814040e5030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 658224775 1250 658223525 658223539
    0x3030c0909150f10050403050708102412020d0204140108100b130b030a140a0b060109052d0604030c141807080408070b010b0a02060702010b060702041a0a120b0903030402 75
    0x9841403e10f001e030458160704a217030091415480761a81031802150764030100840c0d024801c400300d64102031144048640b500d51118260000c0d29441d4042034455000340e6030425101c410b818119034500010840240d03000c2c0c0188030111604812074280c0c40d0074446d6098134010040004000c211910030b0600e12540103010020207070039a1000c0d0300800301e0308105a0544102a80f9101144004c0d60a40345c3d146840700404405250b0325108080d114041c0119043c0104528117100301d5560880b4a00c103980702141880b500d0700c40d0005032034800c4034070f00c0454205070006000310a1200400c802030a40716520603003621010107100707001819240c04101503902c0140e0010070115407082c820305805c2070080300114100b540540310445100d00a80c0300b17040c028000100c8011017034050094a40c804d02c14002008058015400b05c1d000e032180030340083c410741d07881c001088500840404848004805001480c5840d00c0c0c1508038402c00d1a01d20940d210060340340007581c3e90307070300104032445203034050481 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 658226025 1250 658224775 658224799
    0x10b010c0b040c030b041416030b011e15110114010308090d0c0503120928140a030602070c050a0b0c03160809040c080709080102030108250803030c090915 68
    0x36100481d0181c0700312448203c20f40004042003404401c039005a014025950ba91081c6114040c50110185220313106081c0c0c001d002c1000c0384810b100c0904403000b00001900c0307240910213161148807250010150812018082000c03a41d106440d0b280241000008011040b00700c0c041c1d00c5480000d06c4001c03c0100100301f8403c06040c40881150100e100c0c00c1100f65031512038000a04061810080d0403049101155002e02c5280284070389020700880700a018020209944911780124140284a04402c80e00d11244464072003001060045420081c11504d50f000d40c03420f103000d82510310900e4400c0c402450b01141c10703400c4504481444412400442c035100c0714510035008072040440584421200348509203503500d03140105500801e9603620111030307141041002e00740d4810303504400060380c0305000601034000e0006074105c60002c82000386045540c098484007940800ea048002c85000c003001340040c3c02041f10117801f1380328040302d00c00f8041e554880300516032070100c0c402d554414801100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 658227275 1250 658226025 658226033
    0x5060d0902030f01020301060c11090601080a1814060708010b040b04060806040605040e06090105092a0307080703140606180f062b050d020a1208071206120212010b010c 74
    0x4032428541c8060140c40c80342c24004905401c82e00300340d00020108070b8080841040012815444551020850b02c0d0748040c24000300081082c00000c00c0c54014540d11541c9061450002c810072004030361001d0100240d004040e64940c490805640c290301080a4400220b0b105100c1d0040d14242d8801d0489541400d1410004171001e1001400c820381103a5500008101e940712030041814040c0044010486818184001030031964010075000d5150400620481840d14a030911030b1103d0950300960290840b180c0040e050410325441000644078141c3e00000300000c5149001d6840140c1c81601c1c1259201018040198040801201040100e40006100d41c00210503680c003e0009040000c20f0f0103000a403003103180402020b09100a0901e100004204081001110711100303440a40560310490765807511004031000d244052092a0002603001c4c0d1181101440c9134000800520102d603660303852401b04811580261b01501040e4444050800d050061103143c00060f55045446491074403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 658228525 1250 658227275 658227281
    0xa09050105180a0605040504081e040b04120c17160503060f01170a080a03061e03020d03081803030103030c02010e0907020d031d0a0b06130e030702090901092012060105060d 76
    0x40f4120310a90f03103010116031520356101d0a446a4452000305554411610300c1058030514462200c0b03811008000030300074084080d0940d01110a4010038400000040c9040c01020519410000c01903469081c0491202c000107003098059541c10381400000d9100c01c185607c640040310010000381140f001040600d2030950701160a64001c01510341c5407100341e50f00001644144055030009172642800d008003800340a03608801d030b1521b2104240e551070f5502084982e02c403c1000740900503200c0c0000c0c414440c1d0384c10901100f024009072580c960310f9260241c6000d20f020307010390002d60107165151042c24109400c41c010200d0382c0007016403241d210000c40113420f10302d01c04640801c00180c00458040308003d040b00891103034408640c40c1c038040303090044000801e00e4900500c0d05010030303038451007004405c44041a405944220f059038800c2040b03805440c0c00e0900401c0380040c451880c440c211420440f0510380d2088030400c0c1d000580e004201c0d070b1004280100d5501250411188a500300f0300d074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 658229775 1250 658228525 658228531
    0x1929010201090c0b04080d03150b030705040909050601090b0103020c100b03070302130204150c170a110d08040303050606091c060e03030a0b0418080306190b0412020a0905010518 78
    0x110010414107620342d503082c0006159030000c4c807088000304081c04001c1041c04803103420011403408000714100d242ca94034000c1d1840c499561810380020218003840d211f031007103c010b80541d0109001c220308034034100b13035110340034414019010322f0543c0ca0360040d0b02c24021102ea5000074001000403980d2030100c007004002070019079900d03201e444000801601c4078600e04a410400a60050302d5529001040c0c007444000e5155904001c0700000700e01c00100d0030804041600f688911158440c00d1000c815907031304015010301c10541c441c001031520b41b03036840131850340305a00c00c0d42c040c4400d0711600d09001a0740900d00a4680c0426100f0140780599541203400ea9070601844010454141900d00ca604540c400c0e14401000394460f003c080301400c1c28016041c40e10820921390b40490002d44551020340400340c1014460110b4181080310603a480495001078440622119a0340707940c0d402088044101090490041c43c241c80000340c0d004652003460304892000e031207450f6401781c14440d200a0ba00c01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 658231025 1250 658229775 658229777
    0x1d0907030204150c0501060e1e0603120f0304050111090a0509090c04020301260a1203090c210308011e03020d080c06010f0501030e010501152303040803192901 70
    0xd002c0011040040344055001520030746a0094403089818513600f0b40f00c541d04000000d8986205101c49140c81c04180e091070040c03004a00c20b40d45921000a00301580340b508040c82c0b4402048242005506100450040b4800c400800c1000d41074044030820740252910207600c64007030b00e010841401d2041006910140c08000d9030303c17000c4c00c40c000508a0b0000e8000307010030f0b1001c840c4180700310710002c28410a0880c040041000750042e0b80d4000c1070222011000c02016110200e84d41001445a00c0390050440d01190380303426604181d00040012014006900155020000180e41038005916200748802c500248445500307640902468131100101203440078820020a01c003130600313020803806440c2c250105014503103070200040035034042000540d00c50745480010401507600c1da0950748000002d090406400c0c601c0d010640203d500c10703c1c140201e0800208100411501200552141061101541130900da505102007211880d0000c40981018444a0307008000c040c410f600400c0c0c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 658232275 1250 658231025 658231027
    0x60503120c0106210209070c020904030c0f020909030a0e0109080307020d0f12121b0221070501020f0d0606050705060a020310051c0606090b0d1403120717071d09070302 74
    0x5200c415107007800010301c0c1c030030744180741a112074218507005e42c071b264005c00ca900d4184094166600002c49060300034000500744404600c240c020043c110031054022a002003000e4003034502040c01d2030700d95201029039000600703040d28822481d8000d5590f002503901d4000218100b500703507824851002d00503801a60200c440300040d100054401d0400b0154a442c2d58070145220f08550080090301c1014441800d5081400c00041050b640020048100f01950b441040c020401709400919403103480c2000e0941d500009060200102c403900825040300c552004022040d9120400c41d110302510034003c0298120001254940600d50080e5030070203156010309071410350310000507085901150240012001031542c400511205200e2107004040c500030a200402c0b40d40c000504001803880b00610184006249043d8140100240e44900d001c07070200c6c41803030600010151401112030b1000100d40341283c000743c183c5201d180252402003a446004040c02002d000b0008501c3e8018084820558 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 658233525 1250 658232275 658232279
    0x30a0305030103061a06131401031b0e01140d06030c0807030305040e150a1404050a0506010e060d0605030604140615060403121107090e060c09030a0206070611031612060503120c0106 80
    0xe191030080281d03040040b101242546420388c03007101380810183c01414140b8000252011805481d96042c2d02449407034100092a250303001696040045116800c0d088004950b464081129600503c1507078010305000300020394840e06e4a0b0340d0505400010000384061108001d03a00c1c42500098000b4412040e488005400c000072884034041a0711034104094940d05c0d0100a080611031160041c2c00110b0134051441d0000010301030301541d400d09030180000040b11080c810442d4041d4018241c010196801414071303040040b00e0940000030f8220b18060705000c01c804d000c1401241901c2c0c180a4240c40c1410f28680b40c00091001c0d011250741403090001160031080e0040c80130401074004001c2c0001c400d03186040301843c042c001043c0c0c080086041060618680c4c00054440005604035035103981d481d0036180450291501400c1d5101c0600c2c0802400440403120300078502510840e030720501005045201d581c15034005200f1070303030943c210395416080b00c0e000d0b2000f0030b08026800c001080300e903 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 658234775 1250 658233525 658233529
    0x15280203070b0f06100309030f050906121006170403020a0201050f130e0106020106060219080f070c0303440919060b0a0b0307050f03060a080a05060114030a0305030103061a 76
    0x1c120f845072560f81605040101900c0d100c20110881070003440c007000060f48036503010301420303d5080c0c24001d00a003c1062003c0e40e070f5a5040322544665440ca0414130304007071008902071960b40c000e580200340c580420000c41440c1e400b00b24810b58141c0d0051203604616001504c1e0769003f000c0e00001040100319002862800c1001c1e0001495280805682903141a60003804c41c0c000303400220854029058208107020b180c40e90400b215001005596151032202c02c40c030b0305201c0c9a400030700c85e4007641c0001082c140c1001d404030001d2031400c02e6883d49002d40024042c4041e184044046503c0d01e1400f143c1540c031311000d00d80e44100038400300d8204160740d80c2c60a1000c40c6521046072181d407180140411418074800d80801001010801800c5050201026100707000d00e4410807008140840019081d03543c0b070140c103000b0503100e000d8406002041c10309a84418090081141405025410103581c0c240001e031100d141d50541d95090459095a903800040c2c00502400d07a00c00035903082e112019 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 658236025 1250 658234775 658234793
    0x1150c020301141b13180905191a0601020a120302090a030510110307050409020706020f0a03050a0c05030105060a1206030203060c030106090603180605060102010f06080c1528020307 80
    0x490100c0f5034010540c41c141350801075010b00307004000b20001c400c0c8210721010441c03203108019981c40801c003c40c0410040b15080040c4108440074209114611541d03040707541c0f80c0790041e00940640180c0b80401c007040c250660b150300a031100e9006a01014801e000f0600724a12100c6400203442c0252030400e20800040b5516095001540c031500f122250806011603031080105102407041014254500000d000e4064041d52103402c5406800055a03010090294100d0b441014440c112944404007a10000d0040804a036900c41c180d151620402c03642c0e02440c00d99049420060100345040c060300c40440b042024642025441506c805012005990a125081c498229480384a442e50300d000c00c020402a090b601003000e140c0390400c0d4135144c80b40c0001c0030b41c3d8990020b002040540725580101d00502d9a9500c120099150500100e2170786400701da0f0b81200b40742251f503051800502c50610b521031164200090042d10800510f956101c0138080c0040c0d01a02e078010b0324140300183e01da4030740c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 658237275 1250 658236025 658236041
    0x1090315020d0b0301050121050703170a11070509010902210a0e150705042c0103050309100314040b280605100f0906110c1f0f0c080301150c020301 65
    0x28454000c9114520b9800307902c98800722000840c000d001d1549800140c80705401003100440403101003d103c002480020041d0303500a40e4800340c0c03003000e40a440744202d581e4100008040010b50583e02000000c2000915031081c0c80000380f44a22992a00344800001c1d03201a61541403640f0310101c7d00c030b105200c80c120f0b51065806c0800401c0e044000c03010b960038100c402130401c3c11810b003201400a0642d00a0580b03094440c02c80c0c07110003141036400d041d4114110124150104000c140022040040100c0503040c40102501e0000d0b000b0340c81582134040d00e1800d600c90081d009900001030100d82140344683d08428202c90600382c070000754103007251001e103030414000e5564642c00200482c3c20010070414020b40c251030301c41158090700b0002000ca5416118500030810b200c0002402d1103000c3c0711034126640000e02c40e001241c1022030050752983c1e00c0030000302061111055548907405483c01e030801e1580180c401d4070b1a030a1540b0814915417a22403003041188404d402c1005031801d102d0105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 658238525 1250 658237275 658237313
    0x120807110604152a08070908060709080f030a21021e070c091b0807110a26031009050919050c040605041107020d2109060905010512070c02010903 64
    0x1004402442c0f900b026500000c0543c00c0d0fa0300450380c0041506180710b20360440300d010307180c004001d455480e4200c83e003d01d2500022040c0c01104103201e0040d070442046011503142c0780c144d468002d48808069141e02440340f005c404241c4404d60b04190143c00c440e81c00c034615000d03c0040c02c291507089044442150340d2540f0310f10010019011040c08102e0082c0300c01440781041c03d102c40c414410b0303e04c0341c0c0490034008000340300340c0750b01040b1990700070041c84615002c11401c43d10103408a003441c62044032401d020707169007101c605d001000700b0034607801c0f80d109054076021590300501d014603520042000070154a040d0003221800044039000304c16400741c0313070300960040c80307812010320402045910503032129100d81d140440c0a04c03800040f10551b490705804035500e0442e6206401c2680b10301000000c16046005000002a0b4660300710005500303482c004c1d510001d40540b03580c01560301c0c1c8115080403603042503480000b902a8420b40e007400002c0c1c0b0614000610950301d640341f0701040c0c1c010706440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 658239775 1250 658238525 658238543
    0xe0d020f030709050718050607081c0f020a0c0c1d0105060c0f030406090305061e06040213090509010204060f020c0306190b10030e1006030b01061b05060a0b0a0909120807110604 78
    0x500740240f803803106c000341404a03205071602d101c40d40d402081d4803455081c419488082840540d182116a2222024a00400040d540c0e03140c0f003d001071440200c55001c50b44a82011408180f1201820002d200540c1c0c80210b10400d074200420800315411000c0c12121510503a04c06104d0000c080c00940300814543e02d400e03003e1801e40c60000d080800040145507440f56030703180303028441c8402d00300d6034101c48251740c01a65040b112455140341c000e250480e40ea640d003090184009494150300901c21901c480e0f0318282001d840030022601c071040700803280c1c1c1c194055400304480c441c2c6040c894202180b000d200081242d00f81c8046008140c1002d025004250b80b02c0c89021b4006013445404005201c144041126030b00b9542ca4026007035041c000c03174042000a209100d4502e50300d4034071348601504141102c009291640d2024041c01c414025030b40030719889140080e09040c50f016405440d40d2100900850491281c3c044030503040060070482085420b180300148030400b030003001e000b103019400314 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 658241025 1250 658239775 658239797
    0x50a17030709091404020f0102070f0b0909090316060203060a12050a0b09010e0a12090e01030b01050a0501111902011818060b070c06032f09010206070e0d020f0307090507 75
    0x1a2182c112548480005814403940c03048950360b208070550710903812905103d81c03110080c0100c1c40c001d00d0350003441c40f440c0c00c4540030643c1400c0700702800c2c2e0903e00302c03000580c0b50344424155807203004e0704041083e07100841b6401e200051040d0051a8000c1b8040d0031015080c4d5581242442030b4881d0390180e48580051008005000d201d0307040325401060390000b0b1050440240186a40301584c00300a010380d480d0354006c107031052080b20640b0041c007496240c04040c0d6101c2c1403e408001003071040341c1c4a020180301c000fa841d405501d000b41c08162002c0074190424070099012016880c243c0124100525141142039040a09540001030211004c250300f4111548000c10b044070181d030881d40441006020b076000007081c41c80304a0a540c0c2c5031802083c01d0311003900b41540554110a0580f00c0c036400308421400418a8001d170014840c2642124240c0d11040701c2a980101c4000c900c03500050308504050260500301d6514801c40e10140803940c9503640c4000703e00844d0002e9940c4800940b048840c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 658242275 1250 658241025 658241027
    0x90807120305040b09070807050126180c030d080408090f100c0501060b092b200405060f0a090209010513081c02030301150f1704080a18150c050a170307 67
    0x13916a221200e140280115800d05502513900c00f8103129107410064248082c0c0e6008242c480c2071900303018840d00503c140c2c10184940b8105494003d2101058447c000d0440240d2400003410300d43c000c456255030159031070341c3e25015a2a0f120a044503048403000c5150462900e84440d003003502081039840c124038140c0790ae040b5094035003d61200c08141d00c14030551007603036030ba038040030500004005039400c040c16401030f0420180200704041c185129400b02d10550f00c10709040d0285080d403c480130000b65131200c00b00302e51310040c550015040220030b2020b01c043c2c1069070040001c00303014142141032550b0034291078001c08064008041d660071a00c00103800051246c0000c83c0c507032150000c0d504560602840070000000181040200629001d58169190141910400348002d031b8404031716a01e01030a11043e03540c42103500000040384510034403088102d0782e03290b405440c0c0080260aa015441008681c12101c4400640349170042c4e000e0320b0700107240042900c440c0414101440c1d200e1803c244 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 658243525 1250 658242275 658242293
    0x150b0904062c19050f03190f0201021309050703110c0304060323060d0804120c1403030406020a08070201030204050603010f03120f0e100212120117010e0303070309080712030504 78
    0x203501d60428241482c5080440d010484040f0185600032181c14900c10781403103803030704001c1d41413554036000000e0640340d80000c81502c004420034585500c1d000a0204000320300703d114200140001c914818418840310281b034020580115851802044000b819070302091150b21101d100c00c05a400020308200d4540c140c041d40d51082003a0f0300307628090900008d482841c0700c1c0100760754400c40d250407040e01044007002c180c1e0040d0131a01d00840b1411000e14240400608502484451300791407100c01845103030010440d001d42c4e201e0360143c8040d142c1991208200d030451041241070580030b20001c03601d512050046c0d4000d10000f18020b8886155040806000c003910100000b00102518a0b501c9260060090802d1100a40d105034031190080750807801d0600d0701e40300c1c03041440001400c04a012845022605035032000d08085512a84400c80d5822503a50b1000140160014070000c1d0301c4074045da1040340582c0c0a140c007607240c018140c0c0c80a28403000403c0d264040f075590b4080c00188100c0e40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 658244775 1250 658243525 658243571
    0x2c01061404090312020d021e0304050f1603080318300f1206041407021f140721020304030c0b090c03061504020702040603030e1516150b090406 63
    0x61810400e02c06070b520020461104158100c000d650001488200314900782c0c1115000200e425120030011403011803240141d0007520250b40c0341c825030030045401b10021421514120f012904203205a1039030b5201c0d0701c1508010b00002881c440d00d10301c4000203e0030310a9010d908200201101107920584420b54989000c07520b0102c041414807190880035203040c110303207080083c10390948207943d0305c0300050040d0602c0d507080d40d5600140ca081c00300158001444800c00c00c0070f81c1c6c460111400100313105007144c4000508417034107507503c00460145801141b460684001c81c4005107a05010402494140e07402070750214001403040b1a06030a00403402d04080d0405910400b03818040450350000c0d607520800342c440f0152002c2d8549101155482c6d5040711a59a03010780103019003607403420007a140700342d030341c0090f8001c1e081c03601118108440b020440c0c1440c1a9028000c541807a20b4070360b407203201507080201084a603078040b0030905968034010036204034454000407603418591117400b0540c0c2059 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 658246025 1250 658244775 658244779
    0x21091a04080a02131e0509121602010e030304090e03090103062702030a15080c1203070f08070c1806030c0b0703021203310302070e040210032c010614 66
    0x9000c140424400032075081002d64046401c2220710442038444002401d60055810010070010614061403000d50032691045982c101a12000c03002c2e003145030000c0c0300d4080072120a941c404031100056000e0b0114a02d03070f55005c3c04482c101600c40084c282181c0462001d0b21070741d800031614ad031540da49405514041c00d03c804824010707110100c0501a460340c140c3e40b50302c2440e00400001e2122446034230600004c80045105170718540c6c0c03141d446454500409459010750152400c1e80f019901c0002140c4040c0c2d03000da5010000103c0d0f460b01c60b841e400802c0c00300c2d2460720f144800141d5402485007496002c1c2c0c3c081000079000c3c5103240240703405816a00400e2844010300240700400c0d00810809107041500000d26a030740d0b240480c8603505401c80c1d0b20000c00c0382090000c40907020740541c06101a40c4240c0890740e0b00d54492400c0401d040080360700035072020007000c04243c158460340144050640001038020760f5005a454861209014a070002c40381c2e5445008206244890545002404007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 658247275 1250 658246025 658246027
    0x2150f09120f070b070e1509090112080a11010906060305011a010206010605041e270e0a02131d0d11060f01060503180c031921021921091a 61
    0xc4282c0b108074500a600303025107488070803000107107444d0084803910301880700101031020b14040b400c8000059002032035010b002d481e0300400841c80c0c4031084103880100343c1202c905424021f846004035810264640807410325501c6811020000c0d070749000312005144100001300790201c603004100401006488010304650110b13004111032a008000c480070303129000c120404004910704207200c111000c1c1d210480800d60403072a152072081403081c2c80341c1301c00c000d9028030140c0d400d030403407950792404182c0196125603c9058403141112507070040041c01c401001701c648000c41c41c0170650529112190003800715843d03410741c3c08041c074240802a0321120124036101d05504240f001416400f00400e0161385021102c10105414010001c4010040c0c0003012503141d0000502d01c507003201143d81040310308080c10031790307005280c040740700709140c40401d0740c02410842d100128240c04d0305440c0c4015501c0b08100103854550b245a55011602612180c0307581c08410316001204c104048a80721100100740 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 658248525 1250 658247275 658247287
    0x807020606100e0f03250911090d02121219030213120302030705060a0b01170f061903060504050a03090f0f030201080c0c2a0a0506090402030702150f0912 68
    0x3640032100c081002c224684070303090341c110002250311405445500343d41343c4280c110520185580d030394100040401d012107038000a0b680c18000040c0c9400d44002c100d01b000500500d861401c10b09005850580000d20940b048000301d6000c074148822910380082e082c000003841c010100c1c0040e042c0309029164a011491700401c02c043c0e80b00d0418500419800fa04d0a600f12028944200282d8040d00c3d006000c0d02c0c0725040c017101900040c0344131b0040601041d801c208202d1040ca554810720b02c20058000521044d80d1240c0c2000680c92406403d00031780040007401002040d02d44c4101c51040d4804d030300400100102e41000f41100d2015400400035005a000600114031262503590450754207082400091703c83c2c490302d110900680d50340c01807500c180d1108004450440303104400d10618071b84002d00106000090004104041c040c4640201c800c00c035400e4a810160300840c0c0c0300c51140b042e1140c402403800384050800069480d1003c2601c404c003400900c400501c0342d1180d41c000203035440d180c05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 658249775 1250 658248525 658248529
    0xc060f150609081b0117010f0303080a0c17060310020706023c0304081e070b0903030723040b040e090c04020702100e032b02010b0907020c06070c12080a0807020606 72
    0x89030420413242011050f207218030b82e401070701c24070201d0011841c1d000c16503131509802210354015210540004a84402044008a161040508010090ba036138400742c80c030300f00810744880000c3d201c0c5401d44a14074540d4001061840944a12817003500c0150765109030003c14180052040a1030b4025031201c01c6008841c01c007000c05941d00780118441b01c3e100e03607035410141414091000d01100e106185140440114410327002412186d208003080629611044146944c9000807070303100c0081104181544a100301c541400c00b10000000f00481c5400d403a621809002d4000d40e000264940481c802d0000854051080340350041c010fa40443c1004915000a81c8000359110b0000900808040404403070310305000c030002001d1382040701e91000e440340000d00035101d6a0210840154a0201c0400252412041c1203015800c01d0f0b0080c9580020402005684e600c6424115616450170780006013038101400ca04035220b00582d4055240c411044014100c030350f0050001e011908030b081000016 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 658251025 1250 658249775 658249783
    0x11010b1012060302040f050105090a05010e0c16080c0105160f14090d0203060f06011b0506010308030c1b010606110a0b01150c02030a0507080f0d1e0c060f15060908 72
    0x6014103140c410200c8041c5403241009001680001c1d410a09148600c102e4904a4000b18101c400c19604190b00382c0c0c841c0041011a0340030300a0184401d40400800d0781400504083e10f0080d0100c80d185440455594480d040c99225001603842ca94603a003c001c20001c2c103c44444610540341045e400101e16001c00034103907481800100c42e80382001c211080c1a858801c1c851110303590180c1218544e0804060041c0c10603000c03034405000800c8444280c1c26115031800b020303c4a540140103008036400c569400a241d0002803a90844402c03c0c01340e4001c139064400c413007500c144030b14000129035040800040c41e068030100600d0003907000b90000e0001444c0d486100341101c150025014200d080658212001c02c0150340180d414030608091005004c404240c070f038212032120084410415181041d5501d4100c81668100800d5079403405103140c031800508402c16503513900e80011203410965440084400c40d281210340e503640c840c102207040e1800340a14000d807041c0d06003982c0151500c410269a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 658252275 1250 658251025 658251049
    0x601021921030f050702010f050105100c150b1801030203071508150303041a1b060106020303070305060f0d080a030b030c2803231002280c0b09070611010b 68
    0x14900154080854801e034010581d80c0c2c000303541401380d41003c0000901a000c10a2044080c07441c000c000526460410f49402c10444241ca500c1c00b249101e0b190f400b000d07022203d020b0140b41e2603540e0300340300d944c8000d0800d40c915086400d06007a54198018585840c006402640f84100c08102d0040010740014484d9030004402000c40c800317854200200342140916400f10b6900c1c0740c0580e0b144111a491009401e8508031251103070300b05941d2440700d9582c0c2d58284107850242e0000c01c042075000c1c1c0701c2e40000e944040c020301100500c20184012803100421004269084a00892148501603050040000e8803030214005c0540c8640840040e00e43c020310030102c201d000c40c2d0600406ca2040084030f4a000b5034100001a4045003d114441e0f450105401e950005014441e0002c2c2413869034800d0b0307100c3d1403050142c90508071806040c00f8814082c0903c0005001c0f031000480c0010740051006072041c1e03c860050500d903031401d0400342100d40c103030f1544030503641000140302d80c940340c13110103800c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 658253525 1250 658252275 658252313
    0x604061406130b0d0b13050f130c081203070e03060610030c1103070501090b1b04030f02040f1e0c0503090a08091c110108070509090612032106010219 66
    0x40d8030000e4a4099203850b44a0303100700b4610b58003284581c0c82d00f040707901040d5042c0041c0c1d00c9580031500b081d0540115402103c400038840700348004190071240104d40c89254038454058608816100d0b07481c14681101c6080318441608000200300c0c090394040c00780d4034210000c2c2d0007000d06040200000d4514821a031040701015038599114040b2440342d101d84031442203840590381d80b001982041c0c0d01030075000106440f01c0ca0301c50041601c14401c945585808154241500e0074542540d4a10264060390801640e100d40c9403c00d000c1040864840c42141030100d0701c50b41902c840005005003035903610180314090060030720811403c04e0707010501c80360465200325007a0f61854450000385040303101a03c90800180c014801a0401c0b0000c4500d06881da402d886041c8503a03180a0122540d1042d541c20a030840c0c1040c2c003042c1a81490444841002d000d003040d0381c200140c0a030080c0e103a056404510510f40b10b540c09000b02075806115194811900c1c1c0e81300c014042094540034031031921080b00e02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 658254775 1250 658253525 658253527
    0x10915081504140330010f060c06020d0605030d11010b01050a052514060703060e161d060738150f06030c0d0605010f0219140708070e0604061406 64
    0x5030141042c01100c000340100301184c0d1010040c01d0700340717400940007030800110402c42c0300041040588811100102c2e10582e50382c01f0b250015a481001a4100417141d80304680c039828089400d80c1c0500c4212102d912540d1078400d15064044442d094a07108218141400000c20200c070b146503106045900c44140d80518404a401202010048080109014102d1103010000d00800e030304c0030a855002e010710307540c14400c084e02c40400704845041901d00028501d81e508445001078081c04180c400d41014844046800c190300d40410307025400800200d035004102040000070111500320f01d420801d00150140c00c041021070000f4221001800e040c590f03040c0d030b074001d80659403560b0718865001c01c040c1166860b03040408820f05a600002120076219051180c0450294810794420b5090710765980188a2112046482511b040320003c050710814110524455009400c204460080c404500200382c81807038000b149884803006807109100d1414403200300004941d4442000030074030b003100c0103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 658256025 1250 658254775 658254803
    0x1e03030b091e13020301020a1106091216060f060801020705070e01050108060d140a080409050f06090109020c0106030c06050a0807090e0106081e0703051602011b030504020d060203010915081504 85
    0x24003003e5211030000754558000540340401d243d00281283da06c41c60402110181d803185109030f529030180f036a4145240740203004074603039940085616150540244000144010050006401d90b40a81c11105040c0e400080340c01c2000403c00220008141c018020046075040c000004c0c5400b10141142d0b10844041d05240117100c0d8400c03800300148015000c850b030410413864154a103030014854a00b0f03081c9060005034004001600c62803081100402c01c0c1091303802d00482d44001d401c68001e030001036596003008400904503000c4240640050f032212900e6200c010710041100d00000c105c03104100d00e41700704205000c0d08800660645034203080500c1143d032600d81c180100c0e40c80441c01481010385006020070f06416a00c0740c0c0c00361101e6120024401b20002c402e81c01d850070903501502540c5440f002c01589880780d4400b0b40c1251004020110303000e010349a0209030b81007038102d2804159500c0b049044a803186c02c0740f00013001c000c400781c0119012100400460240100003418610900900c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 658257275 1250 658256025 658256041
    0x90406140a0605042114010c080609280c0207051201050f0108031303031d061b0c03030a0207050d0c15030606021b030d0f0e0a08030702040c030b03060112060204031e03030b091e 78
    0x11101204026200800c450b5090260090100e4000c0d24103d01884bc00300100b411901e50485600206c4041ca42c460040c0a10701508030080c10070302d281604500940e400401c0c0784e40d444c04108503014030b00d000410076003099014101000c2042c0d024512541c410030881d4003e24400d000319085070f4140c105000d0180140340c0040c91103071089401540100009030702c0500b4142400a0300b000c0301c4803806c86940320840b005260f664418048010b01682c031115081000d481d048081c600064400e0900c000c3c2c1d08e40d5100c43c0150310b103a1580b00400319031140f1007440303440e5040040c00710034140707000e030382402011000c0401d80780e00028840744e040014410b500c5550f503016502258110700013400700300c1000c1e40c2d1141c080c2c581c1c0265a00b24451070070b10f058070380b00900c0780c0680b00a000e002009040e003a4a4880c020054102158040325207507001d00001002c1100100c417048841c400c00300382d04030140c00e0314004080f070382c517500c440303103d4600300f024045886840d03042c1401c0750a0100c401415500d0303c0ca4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 658258525 1250 658257275 658257293
    0x31d04092a050a031a07020d05070b1b0a0206090c0102061015140a0203130b04140907021c2d0e100c0501020301120213060302060f0906090406140a06050421 69
    0x5800c40f180380800010004409000c060082504500308503a8507040b604980f101080710403040000d40520145001c13501c0783d05401d400c201c010080c01c5c005000e10301010501e800c8205882c0258029a04105850340203001080404000b440901040c0c6490311030311450a41074050003034185908a61000c0c0d0a0103011107113661050a480542c442c104000000c2d80ca61105035103034400080c1c2840010040040c81c01d84040d80ea003105c1000050480c481807010641c0c2c010480021840359445101c56028480d01100d02c048c0d05548615218208100c2c1c0e208203031741060180002c01600030418403203035110300c005244440440c0c90014900c03001a080b284110546030103480c03540f0000c00003c074807068000d0307142041d00c00c2e1001050511440030a008403880384c400070303400190421803850820149002004c1c240401818039040c100d901307012404407101034204003031a1440b00795209030703032a1820720b001c014000d80c036105181905101c007441c2149004521010003a420301c0840d810840c20070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 658259775 1250 658258525 658258529
    0x30b0924030f1608010509030406030c050720090c03040f17090a0b1b0304080a030c17030f0702100b010c02100c080d0c1740031d04092a 60
    0x201100c03203242e10080800c0c0c9681400807481d501034001500000d8460060043c10700c01c0b0182c1014506082c600f1200764041c14081040c00b0400c030342004004000f42c91400d04c041092010b40821111012201c280960100041d0641c2c1c0001824030030800007c01800403a00d005038840061a04280510b50b80319040c080c4d0468a42d1051422001154a41920300a007100340c00f80f01a004010036160b00b03d0761240304a0044181a410921418000c20f004605200d511032003503400300d420091500b4400e010b500180d034511031442900080c055420b0781040380b4901d0310301900c0308211540303030a0000b134528031b098140240507111201e0600b9907907000d030407841466508a4095030b511b401c00400d000061405d002c8010219a50300c42030350060a042000c01c0c4130703c0310f1260b000b50181c101190300306084000c1c54030710341221410f01c00714100307142210703c402014420f40350f156240f00c044800e03041940c140740c14140504e1a02d21000c0c0801c07460068010001c95a00324003003c03655000004510751096 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 658261025 1250 658259775 658259779
    0x20111010906150e1603020a0207051e010905120c010c140102070b040311070b0f07020a080741130f050c030901230c0901020733030b0924 61
    0x12041140500c0b03015000703030300071251480051403000d4036440040c0c102ca8058500300c22910343e02c598680c80e01c0c020750003031035540403a00444a440390b8400004040364212400b503504000c8006128400d941c0040922010700f00464074003605c03040880516035100302e01c1c0c1110741003080e0307031124a00f03105000543c0200c0c9078105000b5545e40902d8140621a00c5041d20101c2c0082c0e1841c84d010a80480410f210060350100390000d8907040c40140091102e811407039084c0c0e404507081c00000345c00d4504000c2000204030341280d821481101e0b1fa4018004403682d5080c490303118500724110302490380018001940c4608036aa135a20002485121000b810036481400e2203500d05002d001c200c0541a02071485141400020311107115829503401c0c6242c0e5494080744480d05c2200030501e40721070b4401078100d012040c4116580195102e118181c0e007007000c207101c003880064591100c14400c50b42260a0101ea0604003407001a124401207801c00314020501c064030340c098400c1c07041461401044144040b00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 658262275 1250 658261025 658261031
    0xb091512090105011a03060a0512031902100b03030f0403081b030d0911011815111204030c05011713060615030f0608070e13110a090209040b06030103020d0f02011101 73
    0x40361401e24000c00702030042a8450401c8402c0d103141d190400c080724410034000e40304c82260391400060140640ca00700311040f00d4081440040c8002d000b600841961407240c0d03006100130444c601049007200d8a0048090023a082004031480c0902503500b10380440741d208018668030502c80e65401c00c503000600880c0d066000003d10400c481079541c01040506004559441110f1440e000558030312515420b05d1103120418042000006001300c003021014810b414000c07603840040c611513007048451084e807075003240003141c10320a0004241501c00500800c1c20129401d00052640103104840180024241180c070b550700d82c00c22509400c041e0013030008a0042145041644015003e4030041000f415200d207020400502d0f0700001a2340c1e81162415480c0320401d8880740001d800340c241d00d20302600ca003401c050704200d4a484024003a40180750b000700050f2110b1480e410001568071803038009108880500040c4003594900c1c4a2500b50340c2e001c00c03e0f421180d41407006907400c132109a00000154a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 658263525 1250 658262275 658262281
    0x1020c07060306030b07080613110c15010e091f020702040603060c080a140114130216230d090b0d110a26040f15110a0c05010b0a0b091512 61
    0xd003640100f8296803140481030b007141c1d114130b411901b2941c1110031940c0a084062030703941e51100f80d4040c1c200700858007510340c41c207841013520078a031054002401c284c0d105100c1c01002003030188201d0a0b044030b00c50000c1c05002041108488645454010802c8515400182081195141d5208000441c0c1c032020030f1104111480f03000d0042c00013240c05480d018201107a1000e10020294801d041e42c1e55011040700d0ba0307511205111104c50001000326425034200300b0080008000407000135a58441d1801459808109000540001c6c0451403001c00ba80b00400e00c1d2006604002c003002600c122454894403004e543d2068000b80540c0c1c15072490b01c540014060f000c069020340f61641c07201704e035141c800c0c4114000383c1024420000b103402601010044411400048c500c85100e680f00b01c040c080800c0c1d03400c2100102d00943e02c414060030208441258501c10081c007800317aa540840c00715030a0314403a1810382d192585101c0d4004841c894500101a01680014401500d040c5507049800d110b1901d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 658264775 1250 658263525 658263527
    0x350a050603030a2109030809060601030c050d0f02090d1202190201020d0809010f060e0709050d021e06070525120c030303020f0408060c070c1203090909020d0807060609110c03190201020c0706 84
    0x104107175036907002380c010000004c080703500074000c0c000c0c02c1181d65200d900c4c0000307112018000380080882010b04c070350200020a4140e94104000d07100e00d0044d04801c0011310399410180c0f03454000c8001c2c12030401c00150000250780c020a0060180f18a42444a910350b00c0c031003050300420003649040d240350f00e4280f01150000c5444a40c1e4031580c3e56840e24041c0644032010010f91000d4860001e60004140600000300e820020050035510b80c046e02a50a040050b51000e00b07090a42d004c00800c6030151000e0001502003001560040c11800b61146900d234807a101c00704100f060340005405d0580000340f1803900360040044030300400448007900e1150600800042e025030000005a0b87e000f2f4020000c0b40e1910544a0b0f04a0340742e0640b034410041d841e01903094040d1203081400d03070303000039400079603004610b08000034107116118480020741e00d41000d02e035808950741c085540d00206420f1080301c3e680b90000084904a9032244100c02c0c041c21000d0040340a4462040076170404d0240860003e046 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 658266025 1250 658264775 658264787
    0x902040e0d08070f090e13140a030314180c01030b060d09080d1a06031504020d0603030e030d091401111c1d010c030906080403350a050603030a210903 66
    0x980001c0e038480c8400143da600803104055580a0324048144140114070301f04140c45503407003483e00c108041d070303a11103070700603041c0c186202d0800a8002c20f0b02c034014240400c10380500143c0c804180c04000d0040c0c8241c0d0700b00b40e9504050710501e41810b0b03032452454078070756800e010340340c004500803c1404541071501d1300c100306070800204150070504050048424507603c0d54020b1403440b01500721400c50380c91030325546104201c0c00d5444d030055400c20200d403800c41c25025240240d4065103a000b40302d2000414181341c480c04100c000100805c000c402d00c1800c00320000f1400540c800d217170610503a8070309104503040c06441c10034080191800c003000004030703070040e04000650309002c046025200100006685100c1160300003800604c6458051020501601e81503800c94001d1510b009048582e031030302074890740c4070050b0480400ca82c94200101011034100d00e039211001080c14485803d0500110356203014500c00d600074007039001c01500c048050b44041d02d0482007a828188184012401d0117490 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 658267275 1250 658266025 658266031
    0xf1403091806030a0f0c0312050903100501080303070e150c06040b090120071103010501090618020f0904203004020102060408090d02030f010606171501030902040e0d08 74
    0x10700c900d034030900452030300302030061140c0005070150040a015690b0705440441030b4104641840404030040007148903000b95040b103c01c00c1d192180e503a00c3c01c004151626440464000300d1500b0540107211100c0084181c87d084003a9050034400305044500140010300c0101605d0400c000114000d121038100082403400303103001d519070a060b034941245076030907610340c4984440c201c1e029692650711080c060b0010310619001d9545006800403a078002401e640080e03005d05211130719100b05206a52003680000601d1490361011460900c40e070458080380e000fa091214070072542c41e01011f024030f40303015540d42102d0500038841e03900c200040000c020320340d1742c0c00d03003000710801c10f00c2120700c0d0680401c41c54002c7d60141c0003400b1030b60f2141d07252603040e84800001a00030704052400401a1010086000d04011030300010038090b0070400020000c0c0b805141608566400c1018400716100880c3c1a040c0c0030001c0ca030100b4041918000319000d03100844940c10b0a1060160280304c0340c0d4440200e40c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 658268525 1250 658267275 658267279
    0x20a0e092d0703110c06010b160209040b060916091818080d1a060909100503030c1507030203070c06020c21120903030705161b06080f010614030a090f140309 69
    0x8032440f40045540c180d170040d085000c201d41e1061006020040c0144013401c4440d0382e00d1045902114540e022413003404098a04441c14000313502408081d14101c10760642c00b80034110302c560402da006400500100f6940b04000d600d1980030061215842c0540201d480690203004902184089103460300349588190180e0b4951440d20b65034001c01e00b0928034180c241400144414200a010320422032000009418002c9a081c0c03584009070035181840649212070204001d030000f000d146060840c00326000f0711020400d403040003000b82c4160404c0c0b45d4906075421000040e110a0001c850a03d0001c0181c800540040d2541004003132010003001000c9040400103600c14544841585030f60340d00080d0b89490100e4024003c800c903034600748285c40f1205004d0100e41d540740c012012600740701010343e04a1000100300400f0000d0b194803ea165500400071880c0096940300548451402408044c0944c03090300c0e00c4d200f40e40b0a201c000c944209095411514181c7c40240007491165680c1c0b01c501414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 658269775 1250 658268525 658268531
    0x609170a0e040501031109060a0305010c0e01020c09040302070e1023040b03010b15160b0a060602060702070f03060b0102100c18050415060e01050f030109060f09020a0e092d0703 78
    0x1c64180303400f406049aa01c1030760044d00c807064400b004010780004091540111a2000010100d1824001c50114086a4541d81c103020386540009050400b01e00c0403034000c1c0d035050700303001c0001e50000c1d212003102c0546051a5a42d180c0401003958010140e0014003600800d400c203010b000720f99281d80001d06012101040800c1d0640d05150070703241da42c020141d01040351201c56203c2003442c0000c095070041000c0c114181f805940d07078189800420740e504080d4940e24882403040e02d804228003504050207000820706280740c4501501c041c482070000510250311120f03004007a03402000f21001d040c031107150034014023040050040203c0300301d840009200814100c00074803801c0c54400c04000c80c1181040d10b5205003000c209684460341040210b040060411020092104504c0558003a000b800c034086501840c0c8200380f0340520341500003aa2142c4104100c0c8a016000864a255800243c035918225900c11045190944c1007002101c4203e08003d95405841e81d41038070303284144c203252010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 658271025 1250 658269775 658269797
    0xa0608010506030604120201061206060504050903040b1603210911060a020a060b0f061315080c07021002120403260a2c1e0102010c020d020c09040609170a 68
    0x20034260740e8103440180c1c254001c2e4001c140807035440c54421019001e54000401c01c0d45c6d403031451a00c0c0f000540c40655026503540f07020310403440d080c091f16400018000c0154102400c2800d5100705102c1e00030360804081d246c3c00c1140415000d42000304900b044290843c15103980000140068854004102d414420b501130104141c85e026095410b0380070b1542c000c00c4c2c00031459071082d0040000c82d200316070180c0388408110740ca60343d41e001040501d225203051100d480c98401a0020764001103d01401c0c06560020001001c10500580d5079407a0116040e182290502106038105001700c07030441e4000800007004828004520302030984078403401c2d100541110f2004411100740104004000081c891190b4000f40f04d100403c00e020a0888c08043d00140041c9000180c0c4660310407a980030780c84224032070411300e42e0288a40019484940064950711500e0000251280b100300702143c0b28402d03000c080340c184626a80300c101b50550020499001024402000ca0240c03c89032002001900c00510 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 658272275 1250 658271025 658271039
    0xf090b040b070f0e12031b1005010e060d0803100911181507170d09110f010309020609040c0e0402070c0e0714091c0c0f051201050610050a05041d0a06 66
    0x3c07001c0044456841c4650007860b0303000c0000f095070075001c072140c612050000381c14040400400403404240d49000301b401045a800d41815940142e0200e903030100f03e00c04000e80e42e1615650100a103030b00403040c030b07980d94408a40c01d02080c8141c21410116142c01d510356240d284a0005000180f14208290000b40f10b09040003040c10180845405142e4144908000500e401c3d041a09100d0b142110b03a09004100006d981111006001540c5591005041c803850381030103644002640b200781703014000a071180d000325a203441149079050040d035481c3d240300201032140c40161146600180f065545003820f0901c0d1206640741c0c0100c20319030a03580e0100b00b010b80200c6090416034500b603591400c00c40b44270200075041c070b842e98641d10300003440f030b9020b00054101a0268044d00003c1c440d031740f50700c0c02e00040c4000442c5a001948440e8505810700c2565902d5800190220003149002950340588440c01c445602590303100c1e4004030420489a11040f03484024580310f05034030b010410810f5641e9076 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 658273381 1106 658272275 658272287
    0x110c0c0d140313091428020403020a090501080106170a0b040218040317090a031b0218010801020c010506040c0e130204180b1008070f0509040f090b040b07 68
    0x9200c20506442082680c1100405a545e58503080f01c29901c001000c0b907004180c0c0c00003680f0b03540c40b00004d40445001d1507001d018504540c0d80d4106500c0030345004e00550070294201140403812911189071801c110030558000d201c1c499468661500d01d41010740181d80003080c100c078280702040b40d180080e004074802e80d038200540c83d04100711220a0300141200d11150009640000417a42c04036800b4503c50340d0a410b070001482c0c501c000350321902003000c1c0802402c1c803900005018130040d809084032200f044024405e0740d075984108811610302521103004500c04140700e0519003030445045111580704400145090348079040c0d4018500c1c1120030243d40d98403501c010300c02d800c008034048584041410517100b01d040010014142d580d642d10b42d04108017002c91034400c00e0b070703442d0003220031000c9072041000a601907080001c40701004640665100005001007141d89102d40 = true := by decide +kernel

theorem cover : BRFrame.Cov 658093525 658273381 := by
  have h0 := BRFrame.cov_init 658093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 658093525 ≤ n) (h2 : n < 658273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
