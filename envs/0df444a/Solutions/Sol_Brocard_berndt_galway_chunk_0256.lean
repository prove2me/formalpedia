-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0256
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:47:14.104737+00:00
-- url     : https://prove2.me/submissions/bab42270-c220-462d-a529-ca5f87ebff4f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 45863313 ≤ n < 46043169 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 45864563 1250 45863313 45863317
    0x102030a060e0910110d061404050c070b0c0313020d0b06090106090305250806010906140405010501050711030715020a02031605100e18010902090a08010c020307020d020a030b010b131208 82
    0x1c0c941210750f8440145d410b061a95080d10a00c1c203600108001c110346407001031503885808205284203908200000d8100c0e00c810041c0e0729003980c0051001c80e1526031910006150704010500b0120703401c2e0f80588409651881980344940e03000344519000350400070140920031205800c55028004a41d008100240c000117440d0344010f0700c050450700c04030a107030000945584a40c13003400144115400851080461381c001021034039450b8480c0e912010980601042d200300340f2405001c60424405e8002080c504014408844d400501780c84803076854140900075045210179900040c2e00421201c002c50404001260007008d0a641d80440341d403400d0000392003890509443d1040081c4001061700646890712030012080420100b0300c030f190303140c4103582c0080d00800302340c2d07104002100d00010b582d1010311605124805550180d4a00b068580900a090301800012a0424034010700080424295400c16010b40f0b244d240140c1c1ea000d90014103080c11495400161140b079001c101080000c50f0941 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 45865813 1250 45864563 45864583
    0x9060605011412130204021b07090c08150d02030304061112030907060f11010f0504031b03120b06040902030906040311190609030e0a0305070f08010506090c09150703020102030a060e09 81
    0x4a544069540c0d000c0345040413070202c3c0000d4029002140d816181c052a9851000009802040f54101030342d0307070102d42c03e64042c003090b4804180c024001c00c0300c2c1c602d05800c041802802070f01c2071400d69259804286198460785c01000000c0c0904d00d10502d10b0310030321070403007180e00c5520400e0941c02c1031440c0380e85808840c800c000070302c0400400e5141c01801910500c0315400c4001c0200640c01aa000b41c801400c42110101d0000d40e8402c0c20100700d411540201681c0c0d60165501600b00075460b00c10001040150310305603000006200c000b0b0b5400541c0011403190000c070002e05114100b914001d001d50407880324201a5821540010300c0003000d6000034003550343c0000c0080381078400c0f03040a4031054501c8255681004106c00080306224001844400f00e40c610402c08020903500d148150880340203071401584218804040380540002001030715101000410340d00c100d1034421031011066019100c22030160b5008020442c51281500c52440140a40c0400348402e02d400960680c031980048 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 45867063 1250 45865813 45865837
    0xf060c020a120f0c0305010903170f0604020a030f0204120318080607030908090306070c02010908070b0324060403060504060501060302161b0503100f0506010c0807060f021c090606050114 82
    0x1000103000c0c0840c9143d48000741e41c00950a8000546900b80701e8081c2510750010f80c080307100e9054081c2c018810200d200d115016482c242109c42c1c40e002d08000c0a0341c0720b0016502015103580a2015410251006000804800700007201c0b280d018600a0060708007100208215051030030100300c01040800c0d402d078412060f01d00010800c002d441c02c00b03181d00a101f0708640500c03c040030066019000000c0048880c000d1f2510362000b569030030403d03038550280c0209542c1d050301b070002c85d92012004103600b0400c00d2000a05c000d068440000c10303010380207548155907480c0c1701c9040c01b00b806414469907005d401645402d516055039845003484881c2e041c103005084180c1407000c00003450158a03500e000e0031004050b01c981c02d415100c4040a40505a0341c80f0741e841c60903011411541c020150340701c4040c0d00c500e8041c101903141c0c640d40010242c415102c00010b8080180d9441180803001441c0c0c2e004003120009101c440714103292088032915003216050290034100e20342e080c8001d10a0324440c5240b1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 45868313 1250 45867063 45867089
    0x6080c030c070f0521250507033203030f010b070c170f07050a2402010f0c0302120901091106090a03060c03061d06091b0c070902040f060c020a 63
    0x1c004a50304510400e071010340035600000040c0f040200c04210090980d07410100d031044c0f2032550300b400c0014031400140385986030400c50480585e42d00100d074203c10034003178003d50780299681d84400901c0c0800158880c00c40c40c0d0441e040e103180d83c0a50b0141d941c000d102c3d00071801c1d45420703ca902444035060003651841c030004540070b400c00101e400000c002e07007403001480381c031484200e0a15680702d114001c9007004d405119804929410003078460380403101030b4410384040031003804a02c018460031008039000c6548805420583c91040e005511500100d5900140d03250300070140101d1000d8045c4c24200c440c2d0420b2802d002080304907500143c80901201c44030f0380d13100300c0800075440e400540d000800d4a42404a88154a034140d8802000c40e50599000d44002141401c00515410204c2d0202e81c0b00301a01c0100304903c001e02191002c40000390003007803034990500a007900c0d1403e02d6122000717282c1c0000e414000c102441c501c002c001c000728240087e070b820f01c50340000c80e001c0c1540100710f090268 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 45869563 1250 45868313 45868321
    0xe09040206072a050409051506030a05060106020703030f1704110406030b0112060e0d020d05071a040f1103010612020405070e0607060504020103060509070e0405090f01060b0c01051006080c03 84
    0x141074100d4a5460303026140001400720314039841c80e250416864050a5140035a000444e0700b480d016540c10154014050701d0b500c1202569a030071210090310041d0140b0486050341c000501c10007240d0f02030101a0000d01e0780c244ae43ca0000d0510941d0050740d41080603e0241307849034905003070520780040c5c1c8106c00304030340b80810000c10000c18050707001a24204012000140703400c07080c40245030301c1e8000c04d024424802010900d0350350b06400044800140e21010040c2e907224450006400201c3c4a003942c03848205060340300700c016440c00d0b034080d00e403440c001040d1030030090007030300b9241c031900309400034000a03150010316402c00f000c0102c040d01a41d00c0da40005c806512440c0e40300ea0345280141400e441f0001814494000d10040742c049000c2450820041101e184c8521140e00c90300c00342d55800f41500d103010034003024140151141000e071040e031704802c00d919028000d02010b8940d80403999241e20150450909545000d06651059104260240320141c0d10030348160b0b01101040407a5aa503c3d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 45870813 1250 45869563 45869569
    0xc08070c03020327030d03110313060b0a0314070609120213020d0c0513080604020619030b060a020a030306120b0f090705040f050403030518060601110a02060a0f02060c030103030e090402 82
    0x3182d4206100d1200130b0b8881c0d8050303261443d03c10340c2c5134942901203844040031050b09904850f01c0032400d000085062001030704001c0b8503055113075174602c030b030340040355441c02d020201e071400f90309420407609240b0034030075a9085072042047c00000c000c0d900c0c04040040c90f0500c1d1000081d5500c10280c090001289110640d0308690102c5060216242c0208129120407400416540021081046050b0300c2c0400003074940c40083c80c41d018540080041c0e00c0c00030024444421405003a40e5401072644414100f05265a1000507000f1074026070060080c2103841c0c50014210307100c80e004100541034200690000c1820600085e91001e00c03005038841c6912641c45441c50800c20b0fa00007a4450b081030b15255180d595070700824000d610a80301030005486040000d1400d1361074204180b17680d0b1000c40020030940c4100400c0e138400c0d01e90801e0340c03113551b0b107900802c2040d8020b5403104041340844030020140b41d410044e05500c150844100b5056504564000301015107840205101d20075034004681555 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 45872063 1250 45870813 45870817
    0x9090204090203070b0903060a0c0801090b0f03070e090c06030c030406020c15040510050a0504030c03081003060f020306011b050d0e1201090b0f011502070e0403180311040f0c08070c030203 83
    0x1640080494103419030324401c2c000761b503100f038415034000d005540203e00303400300501804540d0320032615107170000d038207254502c0d009103000011284c1c4401c1503006c608031500c0600c031b80f20140c61100c40c1100d49182c840359483c64005a1104240a0841001007004801c40328081c0c070b800c43d900c034402503603030780403522002c0c603201e200c0740e0541c40100714005201c10400300203401c41109181c0c04040c061a59110301e180110394048501602081c00c14070b11600091140301c40c0380d80b01310440744403d2055141c0e02e4080c00c80f8012400060381c980c3c0082030040c0b940c0c10590440c002c9032500301c5c40004004036682c3c50789030901a10141d05000b4140c502d15215500d00d0343c0e041001e50008001c00c4083c4403400c0ca20300202041da01462101d61850000c11203810b0b4081251203209240c00030915107140a42e10515140010019030811414038000c00c040e0b6011001d1000071f600440e01248140300b071408100c21205085500700300c1c1860072070341c0b54106800c4403460303610952a013800c1e40e0059072030600360b043d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 45873313 1250 45872063 45872081
    0x10f120e010603080a0215070306080a0204050910090503180901031505090c150a11030309030a050c070819030306050d02090a050405010e010c091d0c040e041104020f030a0b10080109090204 83
    0x940100314400456400581440d61f5003007144107041a4458410070380031941d07a03014034030050700021107080260034039800c241d400400c13a100f00c600040040341c0300411a07007101d0003112541c1001a65590400d910291111403443c02c881541c3c00e03514660301d00c1000039441d003400744e46503120000141c00103c2031003609408c00f40645004555180c80b14040080d5200c4050400414000846014041000019030f407107414040c0085141c20450003040d6034581021380800024442e14102041e03071841809141c1c0740340305000003107c0140c1a45000b6064609640046024480b255030f03040c0542e8a21405680000c041d11000403107072503d040c020701400e003503a04030456600340b102c030001c1c542d4015110421140032543e5140341070131410100f01a80000c2c0c1d078900308444244000d220082c0b11101c5590028881c24000341304503001c03c04202681c10107000c40f200d030600403042003812000c5001c5d0700340001c82140c1340321401c1e4068501a140c208103000d000c1d80f0039502c050240031911a40e12a03091 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 45874563 1250 45873313 45873323
    0x120c030a03050405040f05010302220b0d030206011505130b070303150e0a0b030f0c04150305060106020c0f0f0102060c0a0c080408030304031103070b06090601090308031003020f010f120e010603 85
    0xc82030352410080c100d0b500034800c10340214644201401c890002d403252a043e030342c7c028105400c524003924002011000c00f5200c5100541d500c072420002c0d07a4241165801500c240c019000942c5041d0040344a8481c2c1046107040c810100418201c0c0790f021304100d82038980b1040d81c2900c6480c0ea080890060007411080302450b9400380000c1000c07078141c1c0d80c880c400c080000c0c0030300069450f0303024161128044c60f03103124541e01ca0b403030380c1400f403401d9040010185d000010000681d5921348a95150200a90100740560821003240300181000c284107024044181d07102d9100c00d201c1c10000703640c0c4800a140300c41d42072000c130703401d000d0b60b104450b084500754126500c162225110b01c41c0f0b90301d03071340207130740c124042541510031001c00d0a021040c0d952094018214948541c3c5031410b029035600010030550411404000200000d0405000f44d4015154052980cad011411441800344a40d0103440b0541400600607501c0540340d0320504004021202c50004168880390b25030984c0503010325000108 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 45875813 1250 45874563 45874573
    0x30303040c080f030702240c060a090507150503042a03030503060a0f08070905071701030506070e01021c05071109040506040b06040c1706010c20120c030606120c03 72
    0xc180015040c00c00300b600d464505448140030301c0b998031552840380d204025008400a0b070410101000e0010786604424161601031401c440e0b0114241851002c4404001c040d684210070401d20104000b100003510507c1d0015811405109000d00580030040008050741a80286a01400f481c0f08151107201402103440d015540c03203107006402c40e0400c0304e0160081c2c00241c000118048011250340440300e100018000e010308050703400019003002044281441076040c4410741c00440741c08c2040c001d42c080c00141c5403c1c1010500204008800c2544a0465000445911703074101405401c060107009030406684e202110714011078407090164016030700800722800c10041c07220200b40e191140e44600301d1103081c0d94035001000200c5010302068000159412039410700b150312416015084401418000041c8002d0b55580905400210054184e111034801c80c0c140c0e400c1c2040e4407566440300c0b0000d00a01c090080100c2c1c0d440c0d00041000e80314401080010f02ca54500b40070640c41006d024080e11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 45877063 1250 45875813 45875821
    0xa0603020117040c0305120d050c090d030f0203120a0e0d02150105040915020307090e010611031204060f0603050705040b0108011d270105060109060201020a0c0b100819031b030c030c03050405030303 87
    0x842503002101c0005000742042700280d1004c40100860782c0072200102200382c001d4642c3c50131900f8240548450082d42310400402d8107400700500c3c0780f803155004502c00b190044408003894144071010f10079206541c0088606c00344030320040c0545043d20410340300010794040605100e408404081c101c41051031000051090080d07012440030140c0b540c0400c03440081c0d80c1c4e1081200c80700561001c618098000b4040c500f20241e48480c80c9400c40e01401010602500b02005c80c41240e0140d80100d606510200003001142014021100c0408090a204000c2c2d8984000e9a08140b05050700348107100c0140000b43c220000e9180350f18001c10502d0011440c00c0c24040c0c0c3c0381c0201002d49466000c91501d20340000c4052050088488502c0c256944d41d4070f101c0035550303d0070001c3c400381208101c0c0d01030080c003160038581082a4891820040b09040f030003199410301502c0e50341d40b40994041a4a00c2e42d0540110790041e4104003030071b91519003403002c1d807460b0070120751900450300304031341c5804000300384 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 45878313 1250 45877063 45877093
    0x90801090b010e2d010608010f0b0f0a0c1506030605061c1401020f03181603050c0f130e1b09010b0403110402120c03040c080106080c0616020603040f05060a0603020117040c0305 78
    0x104e4180c0301151034000701031743c03503a61120034204107104190704c20b541001104840b0700c40c071002d001a11102d0401c1e6140c841c550342c0e000b00143d134802e14040d07480c0d81d0346810014400b0318010305401c410151070200c03002d18424000343d0000d841c240080c00c0000c9442d03d082500300c0950449030082926444541c0328100611610004070415840e03850030710410122003140f9561650503011a9440700041911818540c10301080542211025902507504511924810001c0c0034007201c0e00c800b5806402d5071142c586035a0013200840100d01e004602c0040148140c3c40700c0422101034076040008194403641c05c400003000391141840071450341594a05021a140e084800303103002e44c2c4258059101030391108034071400c031803051040c14043ea00500041009040003801010808819880061115130b140c001c20195401918120341c106401d2111005004061101c5c0790817070200b000074040140303150002845141c41942480c0001880700110301041200380001008580c0074090364450211160b00d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 45879563 1250 45878313 45878401
    0xa0b01120e0c060f1810120b18100812070209040b0a15090911030d08011a0c070e090d0302040308040506250b07110703020303030109020304080409150303090801090b010e 75
    0x5046112031740442110505d00c5c206c0184403c1814039a10020000a0340c01c03000050003d030b5195580104a0a4034011081b281310300d42c51052661014002d501d03464492658076101c481d4030325150790401404001c00595802450580190700704280d44c8403a01c130000030b24000c0018800d004010469600000f07900c002075045540524050196003030140d80c2d2030103068582c25541100c0c00015040720040c030560f0307055a25000500b106006481c14404140c9103945800d41c507400c904050403034101041890740007048940030341c110b107103020340c1442d01c0c40d03907010b1040c000c0d4010688244004540059014195407007814089a07200703900454441500f4a101c2e00d19054805800280d0005c40341c24030300744005844811262301900940c516842e002410000350400f80c411601058100000225546076000d10f01501e10103e00c020318491441c60013038038400c441d502240641e414000a640400c8a41800c14111003140b80b0750040b41d5141e0070310114400c51403600b801c01501001c0004403004c081341c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 45880813 1250 45879563 45879577
    0x9051803040e100603050603060403050d0e0a050106050f06070302030904090201050705031306030b0d020d140a020d08130603051909020316030f050d050c100207110a18050a0b01120e0c060f 83
    0x340d8107030081e242c0c0c80c00c81c00c0da201100d4288e0103521201c08180006d100d04000d000003d041000082c07010004805503040c1080420191141da4407100103104c81e10b4640c44560f18104100e62103490288107a030040d40360700488081c113129079951582d40301964042d004075080642c0c0b00003036a680c0c40c40c40c20410820800c0c5d01914000a250a410f8152030510b100c1e5840b1390394009020030a1051715aa4056045400c80000003d60180401c0c142c01615031b0091140c80e20701c10440152500d0005400307080c1c0072000c1d07100e00308043c204024400014201400824800d51050001c50030105600100389402000700d040042c4a000000010030f20404180031162184184c05803841d1340c103440000c4400740188401c2c403034240c108808100e1160004d9001385000317440703000081d00d12440340c8001130b140026640048510716101c400f8800000303030b910500d503000042850411091404d240020321036000b544400422960324460800741840421180c8807080e0014011035035103004126594207034010117 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 45882063 1250 45880813 45880831
    0x20309060105030f030d0b040e0d090602060a0c0804021c1707060f020408070e040615030312200f18030604050d02120405010509040209011101090302070618050a09051803040e 77
    0x40000c20b2514001c5520300d401140070006504098403c54141c00500c807100002c0d6019a54400d610000708050191303c4844126444901c040703403429501070b003002d0009203c102c0c1c8500c4d1912000029030400a40c2e9001501900d05a00350b202a42120755038046980014207034090702503100c06000c0e0302400800e840c511480d4203005070b00e50030003103105a008030302443d00715400c654424000c51080740d42803540a40101400b10301480c001d003480705003651540040d00041c800300316401401c0c485018441d030a441104c8400c031a89421000c2c3c0344103008104140000074800208883e100c4010048446900700c01810b454043c240341c40d144e0366807171110f606074000d07000701c501660384200c0d4a02550f0480c0c0060315000e1034a082c0e00e003040025400408824107020b0720700b9804040071000d128205406101f0b800030610581080800f8000c181e1110903489050b1103000c0601003a100c441c44101141c07446003010900d80c90b291a000d203107a041001c000c2c12840040b034002a83c00403d032617640188021 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 45883313 1250 45882063 45882073
    0x90d0b0405060601020f0f060106050f040e150a051009053d091d0c07020409080a11060c0403081215060d021c02030408070b04030210090605010905090c030717070e04030201020309 79
    0x1b0701443c41d121500e4161526075600200010002540100000c2200c484c9004d61a80b500d5114481c031076080d071060f105540346822070aa03503803045c280300c0002009450102d401e03858155240070001c084040c50b002d40741c0103282e110702403407815000f6544283c041300075400280d0303a4107200c44140f212100619000c40001e015400000702103101e480d141c24429420110420340b13030348188a0302c0c000e41c4400c13002c036040340e621111080400c40480c05054188001e95900165845440b05103107417400c00b50051046020412042001a00503002c54408031101c0c086640c0c16610480710079003100b11040c51540003100061b00644042955005060900b091030a441f000640100c018040f030000f00c030002d2402c3c8080025001042e0003080407a4082d120b84101c0340e5500c034129034542940c0e04080200c501c1a12400180f00c0d1040b580500c640c000d60800051411001b9040001e47c4e468151254031148008002003800885050211402800070288501c41f030741003514000303000b0b40c030440d40d6903024015 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 45884563 1250 45883313 45883333
    0x90e040615050409060b100e0a0b03100e010602030a030c080112020906030703050f1609060609050d151514030d0507140c060304120e0f03030d1d0a0302010c0f030506090705090d0b040506060102 85
    0x54416040c0b5050050000010542080c02b0b5144550000e0715405c8070b141d0b01500002c2c4400d1210005010784810707805907803204901200901030310714062502c018040c900c4010720002c034071049924071140d0125184415510740e54040f034100056600050030034014030006481c54500060105184840c0d1010305000d0b0355100c0d820000c50f51280160380c001103440e00104428904006076107122130003501d00f401c4900c0c030800444210b0310703180302e03400c403800b02c2000811020810f2400842414401e40c00f03407044141c0c103440188035115408004003903003080c0d440a080c650f410050440c0d8a4000361005d66641040e047c1018000082d664040014001040d0310089041c0401140d908603000f034011801d00704150021009480c90811160058105070a50085500b0400c450b0314014000d800004038840d5460009005212100c030500502d4100000e001c0241c985610250f4004868034000f5201c1c01884009a9052064071000d0700c17540c580c5003400280706000c42d02d2030084109030205c0b0b40d0446 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 45885813 1250 45884563 45884567
    0x70501110a170603030d0b030c0405100f0b0412120908072301110a0b060102010b0901032603010303050a050d02040306050a0e060916030b07140c0c04060501090e040615050409060b10 80
    0x1030b0842d0b009400d50001d0000c2000042d140c0c0000b2140031005043d07404034180741c00403904803442101c403147c16000080003002a001c04c0350b0404090000d18014070316060810b0f01c1480c584003030748001008100c881802503600c40c0b0a0418502901030f0700241c40c1055903600b40d11b143c80c01d00f03001d1030780f0920044091981560054800a40d0555000094020910151190080420010810360555407240c1180380c540c0d82c1c0c0342410f0b020b1449580174038040e558124800035031a12007003000300c02580c208010f00109401c074082d1407203261146802c96031004c821140401a010f164401000d060808003408054011034120540748866802102c2c0d06941c1c040503269940405104586070800c02e010a20200e41c030a030382203a010b0254182110618680c0d114a100f80d4010400d00c0242e41103541c0802c81c46c80c0a020b02001032200b40b03003004482d4204030602044140242c0700504050741c07450300707080c000c1400d05400002c02000b00100b0203440ea40c01c0403005010f50744000d0344501c5034007140201d618 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 45887063 1250 45885813 45885857
    0xf0405031e0613060204270b030109021804050102120a090209060603010501170406020f0a050d0b060703080a0c030906060605070204060b041208070303090c030c03020f09090d03090206070501110a 86
    0x15401d000202666150548400b1a140c4014019141c0640800003c82c4c0300c1760041c0484501d1104995034507015001e40e1010302155419014107102e82d06090280d40940c0d19038001c03882c000e003010510b181c140c44516095009210b56810300c000440d01008004d41d000301039000d008424000e40c0c007a100d0760f490004001c00c3e84424024217011402d089500048000501c0b25140d1040c0314500041c07400509115281d642c0d0048604000066400a10004005441d000e804440c0d20180d038294181401e46d6805404888000c0c6255401039655a03107141c00351107a049403c115811410410013181c80e140d00400b19444918242e000381e09113040046e00f0009002154100c035800b042a60a0000b80c1c2d480521a600c03843c0c0603400c041d100e036024004500310f007103283d000703612a0084c050102d15601c148024014400d2540d44503045100800c603500c0c0020641c585d0480482c0780010301c1c2d49061000452601034004090f19a40c601014410100b0799880105040d20590302c2c0c0e100b180300103c11071a014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 45888313 1250 45887063 45887113
    0x2060105010219030e060d0b0307061d060a0c0b040b0702010b010504080d05210112060e0c0102060127150905091606030f090203030a0e1201020408190201020307080f040503 76
    0x6a008040c911042040788100c401003511030f103458110801510000382c1c171504540345102c3e507d640c1e08003946491600700b1260f0001c00725070074105808007020303e02141d103120081c0c0182c014400050b5264600d88a2002c440019a21000512890038a400d010407000300403141c14016600e0501d40805943c000d009480c1260119030003800f00c800584005c440d1600503204200c0502d00d40d4607603e12640d201c004240c0a8844a0260f12400c040c43c00c001c815240c03071100403c0541c01c44c00e09038110780d80c0480c4031030554111031100e0f15070305680b4108100060300480f841d030700f040c0b0f030500544452140042d2030f4200ea028400038040e81d16a1459142c8403084204c04215003141030354100031250280c0c0000c4007040140d0300000390710714681c0129041d0f6000c07410890008031703041007000c0b41e40f503c00e642c6400b03480e040008600309801c0c0015150345207d42000314900e1003030001c0000c1160310070001c4941003640041080c0e2982114081140c00c1d8105001c0d80b40310b800340314651a10035480710124584 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 45889563 1250 45888313 45888317
    0x19081602011a1905030d02032706180609040c0801090b060c0a060b0d14030a1d030a0f080d060608091203100501080403030f02030910050f040503030609070c0b01030b160206010501 79
    0x502c520b020880c61500c90361584910320b61030403001644d40e4007445a00382c08101c54002d503507200380b4003030348055000c00b070940710303107518041804001161200b0094801020803a4034900d0f03110307159800105640284002c0c19449400d041c04040150340c02403e1f54100c4030084070502c1070100345e00420211b800b42d224174200c030754004a03050022807450f030411512030401070041d040d21082c6480341c909540001010300c8195000281d154015684280c0c0c040039240003240103038800c50031000080d01d0700b060700b80140c08944424415010f0150070f00448412241c3c406d0204100f9540d040045e0252008440702c0049004520564501c26040340440b8400d07580950707451210b0b070502c4015280000080c0003a0100755444c0c400780340240301440107500840e22140140f4001c101002d8040584030018600088090f2602c24000000c02c0001078941050003124003044035030728170381c1c2102c3c1403000c0e000240400407990000018460014107803030003241210205400303400740030000d0340c0c1da5000f0721840c6c1c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 45890813 1250 45889563 45889601
    0xe0606030601080a0605030715080708070f0302130f030c0807080a05030307031e06030305033903071418090f0402030a02010f11030f0405030c090c1204081908160201 73
    0x11190f00c2103001a034032000ea000700040d12629100400e103080c0480e04044591120300303400351100c9801c6951980d0040300d0340b81601d41c1d490100c1005041520901c001014190040b860403102141642810041d04000800d513400315580e0425080001d003900c2603401a00480c0c50115019001040c0000345681000095107507880d809801c8000307200c4140d003082c5e080c0c3c6c00b81d002804003c040c000c64008502a94940e80c03a42004407208000f0845421b20307910307000c00c14560448244603050400a014020800162240d841500684400080301042006a20005502c4100000601c5058a2050155107255956948100554058005841c003a60692008541000540c400c541d501c985422514018105090140300c0c1855600a5110064464000700e800e000c241000c005050001c1c8084035201090f00300410310340180d01c04e449101488142142c0000e040c04040d5084447c0180240c0411000034000c41e00140004000d451086040f03035001e0084c0030007481409000e1068104484000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 45892063 1250 45890813 45890821
    0xe010f0e040f02010306030501090312050106050702010903080a051e0a0e040203040206031605130e010e060402070b0a150b030906060a0e15010509030c150c06071e030903020705100507020a0e060603 87
    0x350307606003502e401c904141d1101d0000c00010001e0040c8100740c2e11a84440140d50460001407040e01d105030001001c04c141407000b0740c0940e0b48050084c085a402c038180d195541490b070300883d0b60307202d260304007040b800780800c0042c0c09981080040148003d140d0303c40c0201d407906c80410051340300a44010b076102c80c0a101107202903443d545002c0c84141e460801ca4038004800503480c91501c0d82d544515124001040100308a0039640c036407e45c0144101c900f1840c2116540ea958428100613040c0400b440d41c2d00c44801c0c440502d407091601800c0480b544a86a1800340142a91441c0485007035014480020303000445034000c500c00c5004550441d000b945601030600110f4282d001000000d41c18803640d00c91240700c1c1c03100c2e500803900341941d00703100d940c5a080150326480c0c6480035241c8000c0124078200c2d03203032100b9100c1d0f40c0011610b551034041012451811308a1400300a0b0304819801000c10601c0007015801030014280c4502c240c52030203007903a03901d091251340b1004889007900030200304006 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 45893313 1250 45892063 45892073
    0x3020604150e0a091e11031f050a09020d180302070b090612040804060f11070b0306010c060c0206060f15040b07020a080102030405060a1d10050a20040e010f0e04 71
    0x5250554428548a0070b00400d03103000a15000c40c5a000040039a40c81d4081881c0c41100341100d910100c070303000140007103200300c1c0008442d8440104011110b8103804c08150010f9081d07000346006200c0100468616916038800c18025404980300c0004140350642c1e01c000e52400141074580701f9010340150121a1400c80100000e07400054410b40c052020172050050841a010150040e40500c0145032200e00707000000e840754482407400c90034454a0341c04000903010000e00d202c1590081448581c0329100c000050702c209002c0200188414184130700e070044c855000a0f13081c82450200d9002c0802d922560900c404a2061003452422050400c800d004c0340104a00030a105e0784080c2c01d44c9101030741c8002d8642260400e03a4101c038035801840520280301c2043c0500401451032040901e81592200c9245a841c5000402c242101e07032908000340c2600420b03070003e60792000d505580c84030f140d0284c100402a034800c0c001d01040744114000400e84a031100204016034442c0414070290303071510b07103030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 45894563 1250 45893313 45893339
    0x3030809010b040905010605030d0804050c0f06070803090c010909020418020c03070209090601180e0604030f02070807060804020a0609120f0c1a0702151602010e03011103040507080f0102030103020604 88
    0x60201d648661840a1640f41c61140f40c04a42c0070300000100b06090100701030410000c1c100d401d003003000d640e0074030010a10120b000c5604c584c1c05c880c2c140440240401040b664012284007400310040401040082d820200b51030010140c2645e441095940342e01c881030481c002c0d0700032625016021208880e04900c140e006280c142c0c01c0c041201c2c01c080320f0768006445440c08480d0480c1d60782007040100805920001040310200c2c0e03200043c013909200382306452380c44400070b0001c0c04011158103480c0c03644c0e00038011400508441030698080c42e803070748005009500203407400c9000e5590b18100051841c407880800c1d0584005803e20f100d0300c003107a12420760300ea82000d0107039500c00104c100000c41e003500f1052000c11114950829031941854010402c2c410348440043c89403500030008044404030300c81912050f6907090804282d0301c900340003c00d005100c280303841c01403004000300780424484000386660842e2800c1088585c41014034426500380d0000384002034101c1020711042c0035198500340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 45895813 1250 45894563 45894571
    0xb01180614090301050907060206010f030206070f0c08010204080c0102100207020a0b0a031407030c1d01050d0e07030506090604051903020606010305070513031b050105040302091b040924080c0a030308 88
    0x740030307040802c0e000010b821944299204090b40d481840c080050b50b8043c4404c0d80117241102c4480754480c5550045680b901c0751301c80c003d0004400301d12901c01c000c113011aa0b00038000307040085440b5502c6180841d515100d60312a00e01500c120040c4ca0380030000c60080383d20140d8003a03c1141014035061010b04a5000980d03403001f41600c400c548418403c007550103512840003542c2c04686100e1140f00a0034045034940d040868001804400c041030741c1040c12141d803c0982c0b0000202e030702480c080141040850f1f00000c10701c2c01200c0510075220340c009004c0340103500540603140403a2013030004801d40c40100340c000f40035070452070000300c00f58040e503c401d510008a0429500c0c00303030380c201900c00c40c803240d80003190074810002541410580741d0429201803d002e090403031070141140c00045110000034039894641c0d098020802c165444141690001e0400100c18094608291800c05001b1400580e40c1d181d00750764100080c140d600000c0512211030050202d40b115030a5072000c540c8100018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 45897063 1250 45895813 45895847
    0x60902060c0307030f08010506031e060402040f0305010603170301060c020d020a050306040c08010c05160204020d061505030105030c010906051c11040902030f180706031a13020d0b011806 82
    0x802801c0c260481840100b80040c403940e07450360407002045c030281103c801a080300e800758605004103d03400d041008a4a45050f500c1180301143c0d40301d0000901034030840d041764240e061605400030801005400c540d0549114a6406201520310808421240003d2240f080050600800003026040200c48601c80a0000d0000c400650300d070700210349460030680c0e040752204050344040140d00400e1249892000072481c00602d0f100e4101c1c00131050400e90b440191259a0015550340c043c0b803140e00c040c0040082c0d01c45680c9145006030060615002442414000d01030f901c1448010341c45030722000259500e40d11041c0c20701c0c00090001c6c02459122401c066455550b41d41b851541e0180f5010b040104942000541c4ea8607007203540015610009d8001c9144d00c9002c14400394441c004a22101071701d0032840c000607080b90323001c910785107400c501c65420b030082c0d401e544008448086400410320409105000d000120f2040d0044609400c941d4040c92144000003003408060700c02d0315040300f800320702 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 45898313 1250 45897063 45897067
    0x30a0308040f060f020f18040507171312090305010e03040e010306020309010905070b0703030e0d080412090f060c020913080405100c0501050a0e16060f05090102010f090c06140903070306090206 85
    0x1002d1300b1400ca07849881d8140700f20502146d1450301218404100e9110b05043e01d040c40036091040000d03080035071640b4040c1488441744001501804441320060300140c01404d0140c06202c4c3d00006800c65007240019502542050f85101e18004000116001c07034003445800c4455a00c0d54890100079040030b0a50b1000b55200d04401c80450741c00c111220180c80061b00c22640c1d0390700e500d000303001c44450105811aa4022106c425400b03500200501c0e84190841190103802c46010b80484100859820112411901280c0411015802203184903c5442960226400c0e151041180d15014030654005c100d968200310500503410a003a8450220740b460078240c6242da603654a003030a6502c120f84070054190745d0f03c051200c200040205074600c56000d0b05400d425424010f00410081e1400380b8801403080000b48500c46034801d45c0242da1b01246404c0030011402c061418004a000c1842800300240086452a280c160014120b0b812480014014441c0e9443c50380e6100c0981a078000980e404482 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 45899563 1250 45898313 45898331
    0x20102090d110f120a02010c140609070e150f190305150a0506010c03081f05031c0306050102011109190302090103080901170903030703090213090606050906030a0308040f06 76
    0x300303244034403624882c07402c4480d86480c0700d090118035a1600b0030144281d14400ca40b0426000c0490001d081540a2911200c69001400c00b030400f07031880c2c2402c1a1a110b1300c0c040002d6860045500001c1d98900401000a074842c0c4003200c1c40200c000140e660b03c080d01d0078040d02e13185849400804a10244d48141880c1ca6503500c4560070403141100c90241880408104044e080451089030b40c032040900b071403221f56500392030042c0300100040952001c039041d010152240750711a07a0300c00080500604840c4044031031002c40d9082d040d8680ca4102083c10f2036008115980180201d007103504581c5402d50508401d14200040c0481d242081030081000c50004809038880941840c065401042c9596840d40074a0005210401040c401c610b00c10000080c08244803000c021a600070780c49103404941d50005000107500c807034041d6042c180240c0b400346800c04100361500301904803041100c241c0c1042d40c5850505440d598019001000031b20303940c000800081d40780b6458902d15010f120700103600c3e10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 45900813 1250 45899563 45899569
    0x10806011e020a171c09061d10050a06050d0221030403030c0308010501090e041407090f0b150406080c0309030904020406091e0305060109021c02030a060302031006060801051002010209 81
    0x921565041d0040e04103c42910a1003401c04e44c540d400302555909500d80410250b8a030242c0810b042c20407403c90329582c00f0010b02255422682d08041d550324094842c01da10f1100303603070303d02d0104261a50203007017000241010380d052199404480010344114280342241e0308000c15101e110341500c5481501c0c01700c0c025040c00c1040500055482a00d40500f0341c030050401402c002c00c1640103d0400c95480b90a020a42c42000295006940188140b04220805d44441d0800c44075070042c0b5041480c0c0407003150b00c10041d801002c2c001c003003a1020301da050194294070115100e140545804110300f81e01041c4440003400085510102941c02c0d28209170344580020280d80c059488100001e01d811014407140c03440401410340310303010754482032038079140d0341c4c0f200c0d2122014810700c42e04030b60101d0441d00d10014650800b01000304564215075918080c4c4c001402040140016406881552607950000d8101d00c10401954900e0302c072a8481c0e8601070810001d9120395040908554091010009d292 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 45902063 1250 45900813 45900857
    0x50606010507061808040e01080f0304120201020c0306190e120304023a060b09090714010e090c04150f020a060b0a050d03020705030f03090604030609030309080d09050d05030402030c01080601 84
    0x500c1790200790380d00d6181168904400d08182c0109001d40c2004007e02001440001103404607150004030b44562485400141d0901ca0041020b0750140601070400c058550707140b541010088403c4810400003a0004015554440c8000c101c4a001c40400200d0302526041e000d1401c00d10241d10b2071214401e4442900d0740030760b001480801c118040c0700110b4200003260040c00001e40007990680b0b203d103040000c06503a800c041c401d001e05d030401c4140048482e4800c454115652001804c501000e0501e09440c603541d5001e44280c04024101d070124840300c1740b040c8103100300340040d41e0003083c25038840e468500042448070005175214224020000e81903e45031a1404890301907000b4051840c54082410b00301442c8292240507904108003800c027a43d9810141d0b8240c0c3d801040002d0015001d1805034010542040046c0c10100041140082104590051003046109405440341c000d040b00d000e85841c0003e50b4000d5058003c0c108050740c1e548581040c0d82e002c04c4c145801354201d021074001113148 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 45903313 1250 45902063 45902111
    0x2040b040b0a080106030c0206070c1b03050715030c0801090b01021c03050603010509030a2c04060b070507120807110f060313020f0d0c0501080a0b04151d0405060601050706 76
    0x30040402d1544440d5004100d0a0041100b81001d120300ea900703110094480c04000c0c4004c0600802110103c1404038800300c0280c0400b10644c890b1101d61203050050340c982403841020201111082d0070581240300340501c0d0403050076526111250f07401d06904601a108002c80c42e0b0462003840c03030300a02c80841d10001c02c40801e5507100040c0d20700b048030905003034079001025619140e00400104440950151920382d40c01c1c0c01d548c410800b0100c91444240e0365201ca0b112503801401c3c140045006590f80004000c10f620a030215000320795108035072840200c0c580382c09006103070184071160206000d1401c11000300c0c0300602c3e600b504807041e000510250401d4a41e00f5400014001c5042103003090007018010507800c0729101e07481803960b07949107002a514000c2ca8100a03118000ca0724828150300b00090451000f001486020000031242c2a40006481440700c1040d4018845005503c00c0e020107000350f4100c1c1c003034041079a90200540c0c141d884242c5c11500c09948541440710601c00000138081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 45904563 1250 45903313 45903329
    0x11010908131d010302011b020102070803070503030708240906030a02040617010605031b01030b06070611180d03020d20010504050304060806061632010e0708010b010507020405060402040b04 83
    0x6080045034040d1042d00b11848551000c11801440982c2c0c20100c1c0c1028680c5150810f88140d070140f004034185034041e0310110b07445c40702060110810070040041c5105a00c1907494484030340d2000c40420103070104240119010a6180a100e040d0900d20112644400064222001c4c0c40151b80070408031910380d84120b00340b85c0d5201e500f403403503002801003d006003000c03002003142d0044400381d410301c0141440001d05159480c50441c4c050307111030065036034458114070100801151807035a8109039200b102d413540320091110280303100303203005881c50300032a4141c2e00900b11411004001e0300c4102c030060b24020944075504121190341310034000c0c079200307900c294003540d103403442e104003e0715007503025019600c19842030001b040505516008010321a41040c200107d1161105c5014403070828040c3c9201542c4500301642020101500004080c40b246812a12010780e15000e8900321400074004a000807070030800e0b40c0251401c0d80000d6000b00c0c00a00041ca4156112121090303a03119602401d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 45905813 1250 45904563 45904597
    0x6060e07020c0f0f01050d020a020111160b16021b040f0609020c07090b0607060b0f181522020309010209042906091503070201090507080a06061508040311010908 71
    0x42d8a0500c50008880340c40144c0d08400d0840c41c10001a040c0d01501858086165000c950000558800d40003070341c80c09003884282e42d503150034804c02034505421500a807203500c0300754041443d500c0c2e060950010303098198050581141d083c0205904480c284503000e83c80303074076070030300c465840c8140c40303248000c2c110b009005940300071032181142020361035070010101a15004407682c164480c20101d561990f4403540000d009018040000e810b5089984060b4101c0e000761041e10492200147d0b260161541000707440510b660b000400141d0300c80360b1085000c0c0810381c01c0d442103690441c0c02841c1c100100400150030251820081012140d425032039004500300c0e16101401140451a20504030505480151a00540d03501203a40444210400100b100c1c001000400c0d0510039804021301c6980a425030f4020359882040545e10040e0907000d47d041481c02c10009469074800c00b5244817040d00303803540c00c01581e69403010390b000d030000e0300d001149540b07031035100c000143c0c6800105520071100c90250 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 45907063 1250 45905813 45905833
    0x1f060303030f06030210080a020d090b070e09060f0d03050c011109130e03030613020c0105150301110403050a02120f010e03190206070207050415030506040602071109010f1206060e0702 81
    0xc0580302c80840300584145440428805a03c0f22407605260300b1160030b0405140c3c0317078820150b00034420320f07004e0325540786824400001c0003039004040c2d000d149160303107140b60209008104142e48105a541d19800400b4542002d26070409410360305c042c0c0e000c0c1c200641031000c144041400d64002e407049c45d459a00c0000d4082c00c0e450643d0207544c1124492104010040c1d48820351950b0f4071000d00030394402c4065040b0840703019001d4046a4002005000034042414031154030014036000c01c0d07080740303c4c1d403c0c8004405410304407802c0d03400b02c03030700b010050107401c104e42c00740501003015511003a914015402031811040c0709001d041f0540d88400021592010314081c2481840c0005800000f10740148043c000d006900054601c1176440840d8000f6404904107554021080c3d90340c03006100340141d508000a0160030760241c40054051003003006512007103400c005803020240111401814089400e1050340080d2a9003012140308000000f840c603221048a410a0000c480401c0103901c084a94 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 45908313 1250 45907063 45907067
    0x50103050c070308010b030604022a01050105040b0a0e06040b0a06080103120c03080703050c09100503010905010902031003171e1309020a0e1e0904030c14060c0904020702031f060303 80
    0x90754464000180241465441d80d4001d012000620552510090100100348180d07643c1d41183c0f209400b020141c40b464102d00c01094940c000403240158039480d103000003d00c0c1c1014065034148540041c0740c030300740d68148901102c0b105000382003207821541d100d0241401d5224080c1040140c60346031180e141c10362441c902a00c0100c0c0c1d40b000c850811003640c02c0301c80000e410801c1960042401d0a012419135514400c10030b59001d00c00c00c043d80711140b502c0d8003103019040001503050700e192540c1030105a880300c08040607407005503018617292140c001c0420208181820200303080782c030000c105241042c104d5443c65054a09112901c543d10001500740750700c0c80300780a12008201d051429418545981301c040c00318046000913038080c10060413500507003000741d8441c08290000070041e01143c186030500400c204041102100e0194001c0c0169000703e0002903021300ca030703204004040c074040c07207641404003940010070704a0b018400e940554041c03803100d0460410380500382c580024031503e14100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 45909563 1250 45908313 45908321
    0x40f05070504020f0322061104050405010f050607081803011407170708010b130f0605070c0608010503060414010b0306070201020c15010f0603021b2a042c030c030310050103 76
    0x4250702c40c0707104105500e5815820b80c01e482d4000303981c0c400900e4000300f1800794504d083c0c00c0c2d0401000a4501a9801844207400e000f038411380e00c4c1a43d003046240c0e220f409158543c1454010b1541c08001401034200207920340000741540d40c2c480b022190400384020110b801c3d10064020740c01c1c419000001c204c000742d440512040701184080a201c00e90501c107102030000c908c10f0040c15800d90000070030921600101138143d006000c201900c402165440c1402030040d000100100c9190602d8080014914480d03d2000d050f5007004028007141d498660b00d101008444412184040d502c848500c811680c0511140d4859281d60300003617943c4500b08102401c142003803112140f9540014014001d03080b85c09000c0b402e403000703800c00582c0c403a0403d15034014072004824440c858810810581c041980310580410b4180101e40c540c05454000030801056070404013416403260011011140c0c42c03980070241c1c0a8032003c6c0000d49180c0401c0361409402c540c02141c640b071211040401c10022940d140c81 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 45910813 1250 45909563 45909569
    0x30c1c06060203310501030e030f040e06010206010f030c050f041d0705010915020c0405060f0d0819050a050703180807030c05130e0d0f02071805070206060405060303161505040f0507 80
    0xa4060340e13001c0480c0c0c190f1288161030092904040d83c070344046a4040c400c100f29070f07a00c1d400c1040140c403203503100800c0c444a20200d45090040c0250400011280002c0c5907440940b5402206a000070b4200014807610354280c2e9240303a4071035207801d40c00d050f10950f0840031310842c1007900070703000d071a0500d0009810590954084070f040c0c01940c0c2d0341020981d001c82d645a41e050100c4010503030b92a0b01001900021400418075072103204042c1140c00c100c5400700910141c2d13004403540105810009040c0c84501800c011400452010040032002078030481c6d400031101201e0f01e0301c042c019204c1d007480780342103440d400c210b17080c0c9000c000502c510b00c0c0402a410303844c0ea444200b40b040c0070000c0700c016120a000d07420f800511070384042d110b40290080c4007840141c00300325486105007030303540c0119000d001e042d94844054050b248c08146182424010a84101c02c00340085240840c03011040070781900d1540143c6805a516801c9841c1c1d290600525010f28062031029660f500745041640c2003030302a074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 45912063 1250 45910813 45910867
    0xc0f090c02010e07050a1208040b0a110d17040b090f010203010605090117010303020a021e150702040b030d140703050906040605130909020a05090606070203010e0f0f07030503030c1c06060203 84
    0x402c1049191b407112244400d440c2c200003401d0092084d8600502c17240103c1d00b24026007003001c1024200658481402c0c0340c0a01d5a40844440b81880c2c0002d6501c000b00c0070810303022541990009011a5078030103c0c60308030b80103804032800c048400c09054226007080e0090300000d900003420020a69000103070f00f2071181401084141545190340c0655210f0812800038010f840100045002143e9207500b2640303444090301c0d4980c00002081c0c85502640b10010407842a4070f030184170480d90800082c428035264407a00c07000074146a10349004ca0b40e4000b02c1c0100c040100400c0450300d070b622140f01030300c0240565140c00307441d5852082c00034203810842c1c000403034140c1f60900c840301581e0b8803e030000c21510203a4600031a515040041201413045000107501503003445140104400c00040701c0b040c514030001a203905a60404030543c4a02c81884041d15541c01070002c11085110303800201400c8040c0010464100500c40010060700c1030b9a0080c030141c0c001140c0358035140900200c21001441032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 45913313 1250 45912063 45912073
    0x8061c0b18070807050f0d0c0906031403090102070608100306140109060e0c090103090305070204092001020d0e120c09070314062205060102120c0304030210030b0306040b040c0f090c02010e 83
    0x1026a480e680d24085c0706662003080b445404481c10344400c0c100c120300d2500700c0e000251035034440001d20050442403000300c03600000b12951000002010003a00d00415050380503140c4249402e00c1110100ca001d040d9a503206105d01000000482c103109a1801301c2c010f606c2c4c441d507503141c2810102210426484450300381030032000c1080012204c2c08440f660002400e002505400c20f05085400780601000203401c01d15000501c000c0c048101d0300490015001c003041c0c0c299002c108012a1100304407640e176404a080085d44111501e8201c007000941c02c410021100b941c1ea03080009a025201510700e074020a5840c5103209680140c800d03a17070751001064440e111110341c2d403c501c0034164501603440c0000c40c0d440d80841c807141c1c0300b406040501c1c0b124110381a103925401d07009540303d600a1008a01c5410541c1c400a003c0d4000e00400b2a10706000700039106942e62603ca030000030030300038004c0b210303004410004184642c00e1424040a005200c5001485140d00c5101a003103d0010100d140721340d100c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 45914563 1250 45913313 45913319
    0x906060a0e040305071b081f0605030d0809030d02070305190e010c021201140c04140f09010b0d020705010203070801050913080f09010306030204020a0e09070503130308061c0b1807 79
    0x1c0114079800c203905150140d641c40700d034148418103003880c600f080c0100000800020740e8000014500b402c2042c100e0004080000510b40c007c101c50b2030f841030315016001145040d00079402200800c0c1d00c04e8002068914152118005000300da1041904402182d000b20344608500c0902090302401c070417500f80b03040403280c0c03400040c0c501c100c03083c0d000744114a00c40c10780d08043c0007034000c1540d900311200200e0b12801c020308801515040703400f1300d4500914450741c0011030301c3c043d04902d18018003e001e2480740d90074400c81d560700f94400040c00f1204e9400700101c0c4000f0700d00344000e43c400d5141d9902d20b00d480d41480b040161500c800f401000200314101813480201c0e440e41c1c125080e00c5107440700b0b0780d603032150400107a01400760f641c0040d41c8548040b0358400d000d50051ba1a40400800310b454010035540d020040c1c0d080e00060300d850403c0610640d17240700007801141c01d5900001d000f07001c0040c8030070041c8030060f89000c801044903414002e20602070980c000391143c42062004901803c00d09003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 45915813 1250 45914563 45914579
    0xc04030c030b0702150103080c0f1203010306020903031c060914070e0915030a06090302010e030a0e0409150e0a02040c0c0203060609041a0405030310121a0c190201050906060a 77
    0x8480e0001400c0b000204000c554010300802094064030740700c2441c0d400700c0da524109905079403c041d000b02058021428a400c0c0013001082c0c4900e8110500d2a4a0451342140c071048004c0d045450032a03094481001781034400e480701c0c1100447c2c02c1c44001c01080303650510228034155049400f195000c43c01090511014903009070742682c0c403a0003078491048a60307901c00e416131022840b40209400d8054035602c001404119006113800e54041e4000303004a05409027020350300d208502c848000210310802501c082e00e456003040302854059010355502182c02000c14040383c03100980802aa8062869802141030501910100c15032505016102c2a80390b00420345032540100018801c1d02da40e0b001604010141c12072502400030652401024540751810942d03030b034001d035088260741040e440c0024110510003040c26a035a803180140d00780314071590208807840006440e01c0c007281d10034009100800d01d00500d40941c02c82d0f80d400418182480c07408942400009498175004020b09102480900307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 45917063 1250 45915813 45915833
    0x80c1c080f0609060307051305180d05030408130506040b090f03061902030a11070b010603050c07080a03050601090b0c07030b01090b062703010f0606021c08070e0312030a0c080c0403 80
    0x21026181e05002e60f84d1280000e0074400c0680101c2e47c4840410000422a50a40e10030303889035612201802c20440d00d81c0c00d4903580d0318400c6003e0005031040001030b0000305200b0281140c642640441c084881d01c50000031590382090f005198441800304681180c0d18004c004008000d0301a0090100f90906c0e1092507207581038025100892500000031a40e1000d845c1d01840713040094250f60b0742c0310500340c40d04621014007841120006030401d03000c1101e2800c103008440d980e99029410510b02804581c054000d403c0c0141018103028022000084103040b00c80200141c4011034003400700c050031450302e0910800181c02034180c00d4a030a41343c0c89241c803030000f1603010b0720280c0341040c0d00c001b03a8024100901d0441c0462501942400f46010070007600760440c1c402e90368039800b030350121220070780c14200c0c0020307240300c0200055510000c13860440c000c02c455440f400d0090b068400d5142c1d1040200f03881c2d0301c1540c84940c0543c2d40d400d540c42c3d00c0c0d44440115000304940542601d030601c0c42c0c58181e0f1103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 45918313 1250 45917063 45917071
    0x10603090201020c0a060905101103070605071e0f0210050c070201030e071a0711011b0b0910110c07050307030f080d060e070206010302090a060f0b03090a080c1c080f 73
    0x115568140031019a0b0080140700d2028400505e081030b21501d600e8010201d040d54030138580101c0d12045c0e01d89125000f50f5070007014141080056092024a8907000054800503184105006811103012108280f04801407510482038881c00b005c0c81d0b00400007031500c1d0f60500c01d40a014500310610442000c42c0c804c89072a40d40901c0c0100ea2121080d0100f42800c250f41d0009004c60b420000041e183c44401001c5c01d0aa4001c00480301d813280f0050040da5800e40740342c40c01e88515541c0c0d0640300020104010142c0000081c0b044030b44004000900008540d21940d494460010201d509a0300d45030400140019000980140221138a0f50761621110030510354010512400426191041c200c1e5034000c00041c0068210003040d402c003020040c0d140c141c2030009078010900302c3d000a41029140c05142d04075014041c400c1050340c6016020160747e003000d06025068001d15202501003070001015001c0d103004600540100100107803c0000b0758183d00029050003034140403c403c4074960b220381d07540 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 45919563 1250 45918313 45918317
    0x51305091c05071407080a05070503070501030908030a0903350108030405062d0403060b03060703020903070605030c0d1d0705040c1704030215090a020f030a050d1b050601060f02060a05010e0106 85
    0xd03102c851301a181c1001c0e92600000401d1090100c803c00f804400179404017203c0e400e909417450261118011015641d02e4203000e0702441042010841a29032903005a8400740249031070072071015101d01c0c02d410100c1a44400994280e044011002c40c0740081c070131801810b04038019441c09181c107020600c2801a0586038045004044010b88107095403004000d210961041aa035129100e2074040e005207000c2280300e0080c400c4e840010f284038040c1c800c481c80314200034000e00d4414a004011903403640024039102c031203001400310003003100c81030055005032003000030480009802075501c1845c01302c6070303409684201e05120761b08521603000020300441800004003000d05e80d440e42820b130701d0040e040d48a01c41d40070040341004039601c0045089a800ca108440c1840142840401c16a99000f26400500275405c05040c104000b4041c1480760101c900c2c25407440c82803200c681710581040400d03802030004c98409001008031070303410304c0b40641c085040031003000b80d94140b108213405c5540501403681 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 45920813 1250 45919563 45919583
    0x6040e070c03091509180608030405130902061206010f0e012f0d0905040c02030405090f10080d0504051f0206041e06020301120212030c060a15051305091c0507 70
    0x1407500c43d4885002034550340282c000295001280245480c210b84201c120204400b2509002c40f00a0f006000841e145040214249424001003040360300c2c1c1e00f1004e040059a8410303490058680c44003500103850300d50a0109185880030014118800c11b000a00070020340400d801c0c010380c2c1114504600c0790740008410742c1e011618075500c03015204107089004038454240b602c04203d51009800c0c3c15180d01750307000e00100b079511105030303964040c40c002c0303507408044d00c0c4c00500c82144003001c83e0380c400f02e082c07998a451aa0f035110b842c20300e058002d0110002d840040d091021381070050003c0d41c42c0741c840704c41c0301e0f481800341d100a440b0307400503100400300092203014490640d1001460b0030200d422000456030303940d540341440388400d41c2500c102d0052150000020761400048240c030f218a607184068200381d40d680403a94010043d01300320002c0341c151240045801d468041400b40c40c540e80a5000407581405222149420903071b0204954500e0107158048220b5442401c0d200841d500c0f0788454 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 45922063 1250 45920813 45920837
    0x1050a1a0d09050a050d0311040b040e0601020a080c010501060801050a030f030305060609130902030616050307052101030b0a0b0307050102030414060c0a1a0a060501050406180905070c050105010506040e07 90
    0x10016002500c00903100f1320a0100c070300d040c4030021a54141d4200b5644040094200c81000b24943e0b00551140c0030605100388420404c603680c00319195030000c0144152090410340f0b0340d507031919800203070070380307002d40e41d9000140701294228031058090801103031107045461840c0e07550503169564901c001c003019142c002045c540d4807000c4c00e5904c4004000d2401900d00c000d445020018458008240d22920130304c00800e1107412400c0000c01142c140740d844501c1c45d590340c0400d41d4603511150400e114201044011907a05401044c0c26000e10710400c41d20546040602400c1d0541e4103403000c0510070382201700104030766078002003120704a51910074140c4c0e68032410b20010b040f50084e01171914183c00307020249000c000c0215906403050000e4101c0100580b80c00b00110100d40e07040c001e01e4003240c001c01050080e00c1c01020380000074149507402e190745645038003014058031030941e0600045100c01c1c0341c20b010018203000d0203024140903140715082c0381c0303006407841d8041c50141c220028000c00d40110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 45923313 1250 45922063 45922087
    0x30e06070f030c0c030602041205010f02030f01060c050703050105151e130b01050418090b07020c0108040305221502070b03040b0103060207141c080603010b03070303030c020312010311010801050a1a 87
    0x44001c0d504801b045446541d10070407074920010002044031035520346000e880c0710116a1003642c0c0594030b10940c01c01540e092840503074091008000645003482036280010024100b4002e00784281e50000f24820500d0008061260030b904808400740708940b00460f900c001e48a41407961005c0300d8007600405c104400c0343c010ba40d644110f8010750007401035180101484a200d41242110511524505015540324030b412a143c0070780c50308150009080700c01190100b4400c1010304030410031801440d410084041003a800140b0310381c0840000e400741030706143d0b050b0b01404032200900035104414694541513956520715501400020000d9501158050512141c101c14040c1001c100003124030304506843c1d0240c1d5a01c940c440080000c40800c001030341414103000300944900c019004014090650340e055001d84440c44103402188800c1c0400581c6810700d000c0c1c64020340c05011402140042d000c0010840c0b0016001300b80128110102044840c654281140049030f6260040781c49507840030346 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 45924563 1250 45923313 45923333
    0x5011e03020327071a03012301050f03071107060302070b0105100311040806190b010219020f0307030b06040c080106141806070b060906040e0a0609140a0b04030e06070f030c 76
    0x88030f025182650445603808500203100c03030170741d00610241c0c3c0109051745141070a5100902503481c00080c0c41400b0800c08651200c14500c50b041414104d080500850217030682e070b0801c4403000009a07003140c15013485c58041c800d02020308050f00d019481e0241e5601d841084000611405018402c5c5501405080f032081d402500c2c0f260868030300690b00c2d55200045503a5420955181d00d00a03802002c0300b00d603070b2082c41980707020581038020b06041032184260300c0c0c1c010b0312a00240d03080100400103003a00d940030b000403c0610710440c4e030144182011010700c01114100c02181050001440052013584d420a0444500b1594548003e0b907418035103241440402004481075003101c1d0204200c010000716020181c4261025501032110743c2e0b5901c00c000c02c0c1e810300c0c50040096007001c2101004214190844111180919902c00707143c4240100c0b1450418296426590300e01c20005000c1050790041c43c0080c01d08080341c0840c20011952201c0c0900d4143c20002014041800d6610007000078210b6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 45925813 1250 45924563 45924601
    0x30810050603090d030e0a12030203060103110f040311040606080606030a0915090212120f0c07030f06090302060702010516030225080c07050303040e06040e03040305030f1305011e030203 82
    0x80c450720ba04010070210381d950b5401c00e0703201c00700f81441c070003012040002440ba414030740c000401040320492000f00743e00941c4060462070426444a04140d0000300103401090300018007256295160f00d9400c0101c41003585c03c400c18411810004100003440c0d1182d1040d4001c1c03000c60700306680303131030b42e80303d5000a084000c001007865401c01040468451964000f82c52207009850b286a0284071740016511601d0074000554807034018480d0720b01d8024900098900700c42002c08417035500d030312511544030b41280301c0c04c03c841c00c1342c0300c40c086020980d050110a801c1110350000348120300f0260308824001c88207100c070004055010507031280b1040c4507002d411210b02610300c20081114076050881041d4047d01040100b031040b0400061141000402c070707021603581c000301a5141d00c5910800000d04500e1468600502c400d100200c0490001c1c001000c07002e0400c44a15507034003d5200e0321f042c2e0841c0343d20250605c00300024210014070034182014071801c01d4640141d4981d84c0c0c03a10340307020824102e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 45927063 1250 45925813 45925819
    0x303071226011703070c060e041d010213120807020405060604030614061905030303041709030601090603050d050901050307030e1c09030b060d03020a081303021503060411030c0703081005 82
    0x860304501c101001d031464165002c1980e1420342d0305030003a50075901d00c40e0300c100402c0c901d010401041900d00c5100980c1c10541c005102260301d80b1420402800c401740e403180715005950014100c1201c000c0302c100c0d00002e0446040424050005480da12b17610b0240d2403010340036a807208009007441d52014201e60145078003603400c0110101000b1147c2c4030800c00c84501e030285600c402c90120039034030703c025001110700050040d40385a48943c0d52030005540500c0320041180140000707800d40d81e0078041540a0402c5460000c0c0062842c01e20500c0c00c0c134059096028002c04100e103a0042c0d0f401002c03294010960706010400e010071007540380c0b401e52a08880c4c1000c44002000f05007150f40610300d0011640601000c11710790b1a80001c00c180000000402005a0311140c165000904040041e050518400d180c880142d540ca03004112101c01c01c00c030442c1034290000c1001424602845080404650000b413542945030020440d1803034814640d001d0188801c5100140700168810400405004c0103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 45928313 1250 45927063 45927107
    0xf031905070c0201020c01021b060717040b0d0b010c03080609060d020618030f0601060801030b10080102030a091e020105180f0301180519030207090c050d0905030301080706050301030203030712 85
    0x6140001d007402d0030340c142203006000d042841c003031035072000899680c9190301080d4046540066007c000c82640702004c01c56107040314011240004042002800085c0600380800b5521262401490110351840781c0c1d03070307041c40b103e0380c841d40200340d104d42d005038000420b450f60a016201c0400044098408000080d4810000102a949400030841014a00505408485600701000301803910741c0c07424020310307000662010040010070085040280c1141242000e4001c0588840c8400e003a62301c103c641e96103642d02c031017040e810000e51000c4035180744075017642c1d580019030940c0000c2c510b20841240c40202641101c00d250203698000c51102014001030081140b002c1400000409030b400010545050140c1d0348116802d085441c0040c2d886507041c3d002e003000c542003403030740c1c8002c12100015404001e810701095802d64801e200e003402c1240280c0055032a0762601310150315101c12a0003070340c1040b000384010030060310700000f0340e40b401360701000b020040c10a41c0340858042c85440400e54240c002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 45929563 1250 45928313 45928321
    0x103142d0a120917010513020f13060f0e0f090c040c140706051506030411060d090f05060901060503030705070902180a0e06040c050a08151507030801090507030e030f031905 76
    0x20803031900860b10841c0c060380b250300b104c51480d400c80d5421143d1400c882880244800149413101c0c282401c40b0004024410b10b8180810003401c45000341c008184000a20005002956881c02016070001d0b590079154040c0c90710b000000c2e120a550b01001c0c0c055910341190302c036541e0207060611503030700481a810742c176001701c1d050860142c0b005480c0168110382c0124980050708011085910507504071501c4d0b800c0700c002c00d081c4a16603001d00c280c54000351f6501e60600000c0c1d50f04040c1e420540c0203000400781420842c1c001400c4908542c00b1511030343c0b04114040002d000031451004a808a14005807901184d140c54011140a20400f9600c0b800340c030404110380c40e082c82e47c60b014620a5808100e0342484d980d054407188241400310001c59940000035400045d8521030078100c02c806421011404a1503c541e2816080054101d0100c0c100100500000707030b80744140c0f60b00010924042c015100702d102c0da0b236224420301c0000030904034004002101d80030f44000c0c1030250b0607101d40400591078 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 45930813 1250 45929563 45929567
    0x26071a0306040b010207060f050c010209060c0606010807030c12020c071e090b09010605041203140a03090303051509010303111204090606020c010e130f0e150103142d0a12 75
    0x20040311079510552034110004501d51001840c0015604146c880d4141c40c40e03c0c030000c0d21590420301e81c0007455074080190020f03d03168034001e401401c5a24000f0445424260000b515400c80103059004052070020544041a8001c25020140110000050390b905810a5550a00c1101d4204003080d030b5520743c0011407020491402da04881d10504200410300c1c04034200a007a200030700c40c540000e42d0620080c402000c500902c043d2440c441d060035041c034015008268030b03d0704038000503000300e9543d042040034150940551035100e81d0083c4100c079803041c4100092001c2d4410300019003086081071000308181c80c104080441c11b8103e0070a0b503101c0e0b030f44030025405800c1c00d001d4200103001d0202d60040650081040c05038074440184107014000c8100c0c400c8008000b887ca85030701c3c040e00c03007184001c505028480c407240702c801c00e4151aaa981182400c1d10f11418080251215078407816400210050304036048404c10325680d108000d131f004000d0501d00c3d0500107003024110f01f5510071820882a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 45932063 1250 45930813 45930817
    0x1803080709080102040503060720071707080a08030c090d14100b0904050d14040e041401050106110c0904030903060f0b2d27010803070302100626071a 66
    0x3a1140d48000d04541c03142180c0d800d0b07005510981707170145d01000c00301d0400e5015009803804000320703c28804c078105080c44110319007982544540c0082d02c450400400c0d2260520a00000c0c12004009051004256070341d4120751100402040c0b0340395003c1200c1039a40d4401c541200d0700368028401c0808020a9a0b000e42c4507401c0451203584a460084000254180241c4540c4180d400201401d800d0b900d0310f0701590745080710300c4c0c0340150701e80c1000080f90f81d946000101d406940a00c07050420818030405203400c54038180c00542c180b104101400d00416400110000f2450303003034402045907140c914044d507601c6960b400081c4841d0411802c100c04a080d0791095030151030031100320f42c00e404143e0340801c41907424201e60364022403140201c000e41c1004180300c6d80107502d42038091041d10b616100f0f03128421083e081080f06410018902c001c0c550704010030411000542e20401c074041c501401203050f0103d100c0e0b5a41046e03501c1900c41d90000d001d10014008100690b0451414071840000580f59 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 45933313 1250 45932063 45932071
    0x170c03010501060806030309040e010608030d06090507090b07080708040905040f0507050108070903080306030a0629060f0306010806040f1a131b0503131704050414060f040906180308 80
    0x250701e030500024a2a2003100304c94014400540654588996002803001038030b24020020b0456407543c0000070705250400c01001000407821000408034240b00b12003054640162800c001c02079843d03020300c00d501400084071201540309024550303451161030040e0766805141c0c841c00a4a00e840100030911040840b1000ca02d482903096501880d11900107449116040e5451000200205001c2c80001c05084c01942c01050080031191a0315450784c1e0401685c20303c3c00c0c4500c3c004030703000311840c11042c1d800c1020032012048524504001c411107400c801800010481c0d810004054081800782d21107a0058401d051542c0051050100000d80f8130040310520341100e01500c07041c95841e0702c41c16148200c3c0d000c04c4070803000101c16006114100c40c150000350080c1301d10b491604213007002412603400303140341c1010a44001c0d2104d02d40010030049900c86c265042110240004024440e558803030050724110040724001000d07200780c00e00300020110342c05510103101d0b04071820001e0503045091a880303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 45934563 1250 45933313 45933319
    0x30e0a121101110d03020d060308130f060305091c051b031308010212040f08130602070e07052803060b0f03090105072a080f0a0c020f03011404110604170c 68
    0x780114011245500003810203e0355411102c825500584640c004200c0f00c00b00d00030203d04a5229151019550321825a125032102c82e03403010480e064801d1110f20040c9820f00f1304101038a00718409940302c0140391031303000316404048008001e050040c0c041e110b2540609414005900c080c0d03042540c1d90f8401c103994840c0c20300c50000004c9003070050007114860928040c4010842e00c6903510004807801d22001141d92020500400c0c00e100181210310f801002a640244070311868101c1050800f0b901a165008106041004540b00b20f2080580420550444c4440c2c0843d401404103e0080c001900001100440003528000a01082d40594003500e1100000c000c1515400c4007a44d41d5142c0c564201340c010481d81c1174010007480003800c440b03028001e01800703180511f6118014002c1e0301c0080c110000c2402e516511b02503082c00101002d020800b58006c20464034403240981c08500300034001070048a00380708406840c0c40301c40c01c0d50000d00c8403880030f072405005100c0440d1504800c09036540 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 45935813 1250 45934563 45934583
    0x403050409052809032703080708030601140405030303180f030c0105100603091203050705090d060510090507021b060c0609030406030f0207030905100905031e10020307050313030e0a12 81
    0x219030760803482404d11080e4540c072161440c2003a142075521401c5400c0d01c010006540f81000004629034000034910a44680740d1107507a4581180050300d503c8110f64804400710003030109006948001040341e400c0031064143c540b051381140043c515254212041d022180004240e4250080d81500054010004030b03002c4204e090311294102c2c112106041c0180c040004070307188a009500a0340201c0e0001c0d01d610307142d440c00340800042100a000e0b080220b410950740c20404c10720300d8903070421202070074106009008500b04042c0c0250b035103905540351031400e288c03121a442169502011140601081d105861039440e00c203108540ba604070b0312070361000c2818101da01c0e08440300f5200720307002a941a00d0307103841c41c1d0404040c48114610800f68030140005190b0228965074204100f02449081c201e0040d001101c941319941031078001c0c0303109071640e8014001d0001d142c2c0c021090765480307090582c003411403c0d01410304640b50800000c1c880d40041d65507001040300c0040340c400c078070703ca4050b500d468 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 45937063 1250 45935813 45935881
    0x6150306080609030c07030305070305040308070f05011b0905040e03040503010c05030601110705030a030503151905011b020915060d05010e0601030605031501030b06040204050619031b0e010305040305040905 91
    0x3981302d10407000341000c1e0360032a207018030000380102d0241403c2c07802464002d00b015100e0b41e40303481550010030b050f50030000000080c1d0402034240284480d280700c3d00f030320a02024148202030410700c001d0107100c0c0303e039885070090210124200247c81c01480000c00a0041840440c4080c2030b0740d0094a84a0000728011444440700c000055aa412214090020851300038141c5044505410280c00818100c250314442d4a042d95074808008043c511001905035061030280050a6070800b0b05820702034004581344400540e1316000b103c0da0102d125202c3c40203559170700c00024031921039000205441860400042201031030451450b2080c04203890402603280c8410406650341904d80302d400341d450b4080300501c000703030009a02a0f04148007900260415131034000254071500840c031103440074824108a51000d076810300811444a64100c401d4040250300c0c078000781a12001500759043c503803030380041003c051142c005caa0050404400420260800000d14000145100c00d0041070070500300140c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 45938313 1250 45937063 45937081
    0x609040b030a110418030206040618020607050c040f0b03030d0f020c030c070e070c05031903020c1002030a06050f030613050a021002100c02030a0f260c0c06010f03080a050d061503060806 82
    0xc0c1017a60103030005c10300380c1c5d51999803a0240500312458071208400d81c1c480720068581030003510a2611480160241204010900c0110342040640c102d000b81040305021241e10088200c84c6910418000410000b500d001444003a22806422103901c1c80001041d00b40c11a0101e004010340c1c440000c5040d0350748a01c40c044070b80b001c1c0707814060095001000707000c103040f01030600058010a9410b0150804c0f0500001c1420026a44400d0310626000402c06c800c10155100b94400780c1821201034450124900102e9034400b8020314400d4181e8800c0440d6061020401000c41e003580d00500110310311a12640081d19182c0d180b00b001091402c0c9440c1022141c004810340701740102c03507501e1030300c15420200101c0d85c401c100c1400c00080c6140010900d00c2d141c016982d14410340c100803025603200481c0300781c83c0c0380980584c8500e0706401500c81c00e00c0000c2a0b0b00441d2515129464000e8480140c41d040000812459220115031585a040800c03140e825805c040100c514240036144981e8500600b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 45939563 1250 45938313 45938351
    0x613080a030806090421110714010201050603011407050d110409020408010c0906081512070e0610021506010507150e0123010b040b0f0c07030305090a08010b0a050609040b030a1104 79
    0x30051010074160703814854485006e000c01c2c108199480c0c09a5115030540280e81010442d070841e031250a460300c82d955065809020700d45c0c000038107800810485000e400d5414410801500d00c4040003000602c04009a0440c0c1200d1400c1800d2048140c1e50340e59820700d81c000f54000d204080446d400c241c0c200c041c06018490384402c403166a21603e45c15030380d80762940b80401c40c81c10000d03070001c00d640721100c0800381000544040d0414649130706160504104000260412109040855011a00e18800e1009c940b4509411031320a0030a03a844407600c1c60016602814842c00341d0040d03140c0307440340c421001c05402c0012105001035402c001501c00da642d951003181e0074000c001909404000400001182d90000c0c680540c0c145c1c070a0b410400380c82512804c28880d58401d8000410100746c000840c80c00b01031030f200800c01c840003004100740f4680400c0a1900701c0c8140b034441c91001c03c04200584a0380c00c403005081c03000303081d20a655154500b940500c0c40c8040424080c61401041c07072040001910 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 45940813 1250 45939563 45939571
    0x705070c030821040c03050c0a0602070902161a0406061202030a150204030c03030c0308010b03060112091103030a05130e010e181615110721020613080a03080609 71
    0xe8901503504684484034654030051000c00c007480a280207044207200080c074240210303c101082c549103451410203c0c078000100001e1407240001c42c1f010400c0e690005155400c40d40940030142c4c40d990405c1303502014500c0f45d02d010b803c07000080101100301d440200c40b50302c114810740e400c22440342c40306650303203200303100b0b0310000e4040d4410b031204008100d2130074601c00c003010600800746c40c1c640c680d99403c400d20b0f003650084020407089081c0c0410960810b014902500c01461600e0031468107030002032904034420303c0c108085943d000e4003001d0ac4151091a100480080e0450380c1e200c141a5000307040d47d00c45206c40c000040c0200e00880c0d0383e00c56000f124100d600600e0103501175240e48402e0701c00c103030100b140360781544134015041c0c040e01c2d040c00e00c08006164003407120340e60001d4a2400b03019070030348000002c0960091082440040f04049021480204100c0e0040500081c0e1000c6201e030301c00e20407203c2c0c1048944800040240001442005162003680c1e0486592115018841d650300c00b52 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 45942063 1250 45940813 45940823
    0x904050c091c0f1703070201230609040204111812060106020618011401031a07080103030f1202090402030405010b100302030c04031401090219080d1106040308060102030d020a0203070b070507 84
    0x2c03052201c00b07480c42c40360326094060001c0109103a1103640310710550348040c0382c1d011004804810000c5040d020711600500a41000703407516072404101c0d100926840081455110700d030404013081c159103465100c0e01d058078115054940d07500500d500804011500726201d40311b00940d80e8040811003000c19036904842841d00107080039200c5410005c142c2040740c40e113290a6607100c0c910302c041a940051607000358018a0001c491901c2c1c0700100440c000c0040c2004c040c040c14500410029500000700b9100305101d240c6070003558401140314019118045c1a680d015001000707110500c00194089640d0010031241c4010b03182d00c5181c15002e078041200c1500300343c00d00b480204082211480c030241810704040000451006aa00040d0010000c0840c1070510b00e21900c14030021000f0401c00e070301c5008600340307210306902c6120303020382e034000003000142080b40700c10104940b0390080040d10403d94000318150346400c2c0c0624006d60700d80000d441994160410000700b161140108100c408a44e004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 45943313 1250 45942063 45942079
    0xd0f0608211c0207080c03040f03020405010801091109090312010e0601021c0e15070f0b04050c030304180b030f030703030c080a0b010507060e19050a050d030b03030a030903120c050904050c09 84
    0x8a0b1000c0000d41001c001074130544410800ca000350070b014030050000c2d00018042c180701c40d0a500600013100d5058202c40c116a14100403903000c13a01d1100c042e80503107030885011160784d841d020006d007540542c269101000a02400120390903030140f50481c490700003a42110341403007050f03045201a920043c096004030380031070b541012500b810b221030601a02007004491905841d50380c1c01c0141100b6502c1925260040020f01003002000d00289a0034a0304034001d60074241802240303030040051a6400742603031341d25000c645040d1024031050200025500540e91a9100d5040240103000480b0100c0006040702000032054661485081d0a506042e0349244c00c08440395030703440051000340b55040c0300d071043c3c501d185801e41150303944c1980f42e8802c01c09860000154039005150072005542401814140082c03603220752000029203e1520b07030b6103408035165516040030b80b081402a003941d0203250400307135603007042030308030b0020540d201064804211030703515010b0416050242e100c8465200850b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 45944563 1250 45943313 45943357
    0x100506090112050106180c0e040605030d0302090a0803030c0a020c090708010306020304051e07060206090309010c0f030903170901020d08040302030f090a08010c180e0105150d0f060821 81
    0x81d414200c420700d0301c40d000003d4040d07180c0384454130a01c2102024940c5949441f44900c09550000e4010303041d013000d5030f00f0f0000314140b10020340c50b48001e11680d0101980400d4580b425601d40b40a14014103604060340d5503030500c414000d0550b4031a60b85a0b000d44075203016006242001c030351661080d80655510801c1b80d0840e40d80c0e801135400a0810b84080c0300340200c1d5180071050346108400c0010001c0104491440d003003002e03003488802000c40160760400d000c04a89030360402602185c4941c07000341d05500e0b002030300d0705139001d0b80980c0000d0400c0001c9082860b05540003c0107014000c1c0036000c440f40d0714006407040750140000c4030300600680092180401404010b4081c01c0d40c0741009280c050815210703400d042c02c560549002030001070010810042203849200c903c405410000e40c4548550305040205c0c142c4000005030b024058000a20510405940c1c0e01c104403c8141c82002d00825a40359101e03565200074002078070400040c074208070759140c0050201c2e401481800500e80d10401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 45945813 1250 45944563 45944579
    0x9020304020102030c1b030d08010b03070e0112060905180d020a20030303040f14070303050f031003080c0601050924120304030b0115080606120a0b010e130204081005060901 76
    0x50400c0741544414170556108007811320070070003003490707007008000c884010000701443c002500a02106102100c0014040400d0140842e6808801c50030b042401201c813400480c4c0c015030141104140a01d00040802c0072002a0071040c06010a0701d80c822005242d0303e1002e448051010368907015030310100b2102c0002d030404003100003124102c94a80e501c4481400402e04590048608a550190070f1805d2820850140f8064030002003080082200e141180e501405512690801407100400800054210820168120043c680c452240e503120950f4041c81c80e61203d0038003032240305015000001e0130342900f01814600b210340a040200040081c0000d00403c081c040b200d90000e400f08101c08004603100043e114004d100c4d2450070a500304078508004c2c1866009004248244001c1020207405a0342c40701d02c07504411407a6001940c03254260050700c0d4108060a86034200050810400301e210b5a80d000e001102d071080107941400218070800c10465a00700c0c0c11750350000d64980180f000c21 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 45947063 1250 45945813 45945817
    0x5100504080a0f080c241518190606020d0908011104031403070f05150f0408030403030209040f060603020408160e0118150905041203060e060103020c0309060c0106051504030b010902 80
    0x6004d889031518168001d10454102030b603c0c40613a00d00c5070088140c0616161106556920001381084d015400c16a139001071045481d02c840705840003001000300d151001c0800c050507101d840c0003420010603a80d010040d4a6015640d00d0002003000c1040009016106000d020b5141c00a070038800c0c9094210b50f18030984000c08500c1c0c0700c003444144007800020761841c80c008526405840140f207120b8581000c4020000020020404200781d10240300c002480c050680e40c02603458200980c1b1030841401040c001c10340785488911041c2860400119950150700400a0b100400103a4190310f0541242d40c1400782c491245070251385248004004840d80c07031000210015000001043c0116414403030340500d900c982200e8400740e5200113000810002551041440109090512507146014203000c18083d0040c4440d05050300041d881c01c11810510460b0b0041da07000b040107444141075a05030b0b00900c1c45000d018081c0e5450445108044940c105407002c903944990b007600103a080c01a054069 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 45948313 1250 45947063 45947093
    0x509040e031e040806100b0909040203011e060602011d0a030e01170109020a030509010b0904140309030345010e01050c060f15040b0319080c0607030605100504080a 72
    0x60300090201e034540080b0458150416041c400095440f40d042c1456181040d80c003070714000e455a01302104008081400c0265070b8000070440380b440460f030711400402d0143c42a04030012041c0700c0301c3d4a103010b5028a40c011400c0c2d40f940e6008100c0c1d422a09100380101050075045a290392064000c500080c1c4a42070038204110189800040b41e10601200d10b10004283c000481007600070036003e01041c1e15100302c43c3d000070010700911000038400c0200c2c05035074000d003001e80710004500d440c140c261010000c40c0c40d0300e0320250031655280e418001d05003801044a9500b00315171500d02c9040082182d0314414110590841c070b00040181d030180056a1000d006c4568a040c01030074409000c038554140081441402c4080381440b0340d1801d8500d0300c00313107030203446410f100d9803400c1140c8085480009540941d040c41d0b0b1a1340c4900000b03414540164011f0214409081c8100301c10400d00540c140c22480803108183c8921520281d4040241c495003c1c5004062195002038050408101140c944104c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 45949563 1250 45948313 45948341
    0x60906081303091503020c0d05120402100320090411040605310303020a051002040815060d02040c11160e0a0914011a0a05032b02010e011401030201080f0106050904 72
    0x1041d5a6020301c400e4184130b100072900030a501103a2001c1e070000c280301c0c400900302989007081c500110740c0c0180f01c0740c00d00948081e014107164810074100c50b010794040171000714080d100600044000e50f107002d056200e09280303800b8070306014054134600100001e48082e540c4680301c050034404140c055031303c0010f4a54668030709161801400c1c814000c0c0e0444e0384c01450080e40584a800c05078107080d0724240c2d1700e02c0c40c144a10700c104401c01000034003040000041c14425661036071070710307090300140e40c00041100295200d0b1034200301d11000d503040590b012501148105640c3c5000c111406041c80b1b0320a882207032030351070181001640c241d0090303016240851082d11800242c903803640c0e03068211180d202030034030321020300d90803101546040010345008040841c001c0c01c074009000b0402c030945144061682800c0506804c0c6e459050003904001c0e5802d15a00082240e1603140e8142c005c2c0324000e110503030118a900021840c5071140c0841c01e8161941503d84502c0e00c61150140401480c00c501083c907 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 45950813 1250 45949563 45949577
    0x605100c06180305120601020606150c010b0915030709020f0301090504080c0714120715080c0c010c02070501030b09060d03050f1b06010302190e010918080a0c0c060906081303 77
    0x124601442c01e181e6031500990312a0740340c07030700e2001602155001408150565200108200303c0d80d54054002c030002c0401c09015480b01005e1226030b0251050b81c06240e400386070241040b110300c10302080b4070380000b411401c44030096607483d2480224442c4051118910b2401c00061046090755000b2581180c802d000c2249407070b08070090141400305681162014502281461300180f8202c504800e0302c150300c4014004007890058007485071051104000e0500c4510b00c0001c0201d40308505580c0c0501c00301c0000d202c00d038840c16000b0344074142400f5060211340f80008003601030400b264100d05c03a08010b40b0a05e40d000113900c050303401790810b51000007081e6003084050184007001d041000c1004410000300b1655055104014407255008031004801c6480d581c03c000340181c0141c580c0c115840110001400080d45031603500800c1d08200103417001c0d40004002240720341c0060f180001c24015410b4039056511400100c9001f0858400d900c0014244c00c04038031a02c402c1014104182d2180c20522 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 45952063 1250 45950813 45950831
    0x8041e0501020715050717010317220303080a0b10030e0f030a020601051302030405060109020703090506040605090a0510140f0705070303020601030c06080709090216060f0e010f0605100c06 83
    0x60aaa0180e8001c84540c44204550f141c0c1107414005d064100009003401442002207240140805c001480003030700c0e00751b0203442e2406d020005c41c00c480f06100303502c12607003250124002c484030344129403000f00c000174540c400240404215106003442c0c1040103240d41440c4210743e4044001d4120410030712054040c084c1040d83d206820002424040d80c150007401c0150724080401030b10020349409400304a0041013000300040c80810307107506407500500010380300c0e0001d0408a610954640200d078000000140c04500382d50440090107400c1012500010b00b15180d070103200c64003920306480c0000c2110781d2044d40070244e4000180c41a4142e040100c2c0c241081a2112881c3c455103500540143c0c010b8801032062180130b0316007001038212820945058100020020510703006485105010765021030400d068180114064001a411030301c103102c08620a21050010084051005802e6103030070901095414180030721012520000d112803d040024070007a565a27041450440301284c0d201c1e40c80e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 45953313 1250 45952063 45952073
    0x30724060b04080c0a08010c0906080c090d14010507030903022802060d060e070f0206040b1f06020105060a050306010506032a0c01051608090c12030412050307030806060a08041e 78
    0x60b00c0180300c4100200607048204051201c0c3c05070170f030030511190f4180010302e2811b07034010301314404940c85032510081950354003a000ca51800307400382203580080c2060b8403200348420380f00243e4011031084000c01071600c410030180c0460307071194801000740c0c03c503a48040300c4d485c18200b0314000714110b6655031079044050b400958568040040420a182d036201c0903c9603002c22101c0b56801422420311401c405100301c4060b42d100d10051005004e6a081d90010b00380c0e149191140614072112034140a0460319040003901900c421141c00340140024040014545800150303e412940f01a28091030354407441c01c1c65400ca20f012704081e005041d040000036048800000030650012400f00000d4641400c4c90720380103101b0340c102280b04206c0f0480c248407000d4404620950305d9a401c9620a083c81140c0401d07609500655110440b1000052000000e0201c08401485110302c41d540354003403656110300700301c00e138010360441e040001d407808001000104444003a01110307481400c02d070400c611039521 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 45954563 1250 45953313 45953317
    0x11010c0b0406020306040207062306120a260c01060509070504061707020102070209070306030c050d1109070e030703030804020907090e040807022409180603030f0d060b0304120809030724060b 84
    0x3000700850b0509170440580c0c04440800e07040bd0007100c1c140040c0c0d000c0d1868954491980e28050300e101440ca5031968405c3c1040c080213020018809200e4440e040985014001d084034440c0c07034080d605400010300c0051103801210113503841c54072405100700c12030702c003045512002020703401035650801ca44030250b55071703030050b6200e0343d050350380441e001d4214034060240060380c4e4071490141c081c03030040b00005207842070f9030304003e0001c0d600f10540390740d0341d03c0031980c100b196941d1640600601201100f0706501c00d0009100314002e4844041075280c500c4100c2e121003491003980c40c02e81a480210780002e80083c001c01c50301303000410076400782d00b4803000c2510405007929910b0034154000758040e5981800752450381d02d448442110314482c600800031a071284540000c940000100250510a00205a000701c000d008030601040c0c580c6460f20b07085510a1a02000d4000300700502c0000d00544800001c03031300744503404200300d034400c14200185541010743c41d140c0c0107100c0e2a00e00100c5c00d81c040c540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 45955813 1250 45954563 45954581
    0x210510050316150509100509180109020901030b031605060c01020409050720120d151701020a080112080a0507060b0904060209010e03030915071e06050411010c0b040602030604020706 80
    0x115444009241140590b000c4420380584004c3c484240485095a0758180003c054a035080c100155604041c900294440042034480324441ca129000400c45030180c0c1e015204000c000c2e2420003440301c2c2c6408140d44c8011942c1940034000d810101072244c2c2c18680040c20660003488000f50a2941720a0350005440c01101c601b0002160601400017849500e4054a912100080500901501450208800e100702d8038152541d5071034a41580000104180810007042c0d5070034441c50001c480010140030303500c11007205c40042c0701c100002c980440b442824162803580940c0c428500b016500090b07071990442c1c94152102c950303a90f0b024409441c1c40c412144a103110740d01c0180d032007416a0001d803141c2c24164005e80a80d00a002e25000c40e25000076203402600d10303012140d02c0d43d16900d81819500c400c2c0303540b020300c402616070307074020812150080d500551140c1c11000c40740089000464040050510250610980d41d02040114856500558001001800140ca031031103544808065030b08900e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 45957063 1250 45955813 45955843
    0x15090a02090a020c0705060a0c06050103080a09080708070303120f0c0c05070f0f0b0d06080a0308010801050a0b090f04020111070b1209060402010507240e030c0d2105100503 76
    0x11844204600c0d00510555004260401c21800c0180c1588001d944a00d180581c1703000e0800007078604082406800c1986200342e21440030b200944c0c6038a840340d0507411100300301c4007094219201003991400881c0060648003c0c40c000c007489883e68500b1200c0700444990f41c102d9560780c264105003002140203004881d01d580c0c890809000d094038016103480d240e0341c00004002c03500d84050141034a078001840441e54003c403041d8846c005400c54134001c003038644c452a554800c00d54860101604018004d040b19803000081015581e0803031480c0a558407101840e6002d0901c000192054482966a58201d0300600d4040c2c151554100c02d2441c1107601d802038000500042404450780b00e2100c5026070241380140a4000b82c20958006071181c05541c4c2c3c01000303180b803c128030f402c9461212608a4440300c148050000c0003c6100082c1c4a90003000d8003041c5004100030701e48100e010b0b422181182c48910001054030f41005c070000010100640344002c0e45e82e40140004d07556900b004101c0c042c007100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 45958313 1250 45957063 45957073
    0x8130c0909050d050901170603030f031609060305040309050d050129040b03070302030705010c05030c0d09031104060b0d0b011202070c0f0608010b03011a0c0114090115030c0b0c1509 80
    0x19040c020314110070743d500d200800c6010462090281da11082041d0203852190960200d0340320040040d09500918041d044440d0001c020060b91a01c0c80460107401c0103540c0b00d2854003604d80b68100c059501c112006004a01903810400c402c0c01d110080b900b0340b40c0038100000304175008990321201d590380e6480c0512103900394640210036150030321800c4240706044000344070440c5180e010035241c0c0001d119071810700150300800c0c03090050500c2243c403803003d00025915260b52a030400382884050340000e442c0c2c0744040844640c10700300f270b10034141076403200e42001341460000918180070b0110300c10072504000f245d03000d280001c640d9001926005100d08030340d07141f160800e04070406420a80d4010010445101c00402011020504030f81c10345513031411103a0311958200080c48180b007100281000d039032a00c45551840a4501070300d074054100c92000740801d251182022032402203d005c00703004103845035810000e00740f02d50014009078504e101038900c520900c1500e80038880e0103c50728000d94001d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 45959563 1250 45958313 45958331
    0x3010c03060f1d0105040e030409060e04060c02060601020604060f020706020f0430060902010e090f010303020d090303050405040506041d01050403080a020708070318090f0b090603070605030708130c09 88
    0x8010200c40250450f031449910b901c2082206010410043c03140b6401030341d640b489040c00c08070510451f009040301c0107051145941d16401040c00c1907085605882c550b1034210414005480880c29500400059005068944650b1242d000900701c403801116116400c200300e50004003180081d0109042c9002103944440c030b4a0b0011048049549800015000040100303520104048581921076042200055028101d20040c0d8540c41011085030f4403944940c204100102c01c040c01c581030700d209500b921541031680805903000c0c40c29000090100760b081c00140510304040c0d10035540030000400100b02c88104800442c482d43c0101c9000800d43d4681d001c10050640003802d00c8e402c041700302d0085103000010b4650081500072140000d0402c504044031110410f0118001c2c00508081c6504000514000e5960780050036104007242c020041180003484a142c007203141e10455117240c807154903503522110101e6080400400c101034524000107680b001c54942c2c1c0c200d03c083c4c00316400020310404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 45960813 1250 45959563 45959579
    0x9030b1f0819110307030c030605060409080316030e0f0706050d110307090825050402030901060306051329040813080304060806090a0b310203070c14031e090d0203010c0306 76
    0x601c0a100f240290300501e010400509200c3d80d00040340c3d0001d4002030688c982c0000600680031403e0b001d024a4804800d105540c143d0300420958000c194508120f03142c84040b079540c0b02c542401c1c51300c0080d0400d190400c840c0e0701484c0140352121000d03100040c90340da500b98040032030704140d8802001464043c02400f50030000c004208085207000641105100554242c12013218a800f469004079008404160315540c250803000280d17170300031800d0105180c0a0780d030f103800490310a030949103c640807001d0801d508000156082049a0440c040d266980d640c072919616417000c2012151600d4000c1c3c00a601d100c1803010344050b007042c1e5520080f07828841c00300140090094a02c0e40003030304d840c0c07040c0c20a5840d15106040085c004e0000a4000305501c00c0d00002d407a90b07107034083d117030b4000001c10986560200800c09594400c4410002c040f8403c0c075120307500d000e6020900314040714140c40b8030024480c0e0000c0e0214802c0180b05404550850b0302090235a0b541500010119480710003d210030b42e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 45962063 1250 45960813 45960833
    0x3090d0f1401020f030a020703030b0d061a060910050310180f0b031b040e01020909040506041406041e020609030a0b0a1107030c081605070305060402040c09030b1f0819 74
    0x2800d25000f50704011440c2d500d00c1a0b8403019003010039050b400038038442014000e402c00d0036142c10080020311510968140100909170560914001c42d041028a1045140480585100000162814046021840041d02c080d031010b040c401c40034150314000546140c0f02d40e2418040a0410404a9070b44c50000406099884280400f81700390041c0d05000782c84c0b00200e200d6500910104e50100c0c214004c090725a00a105a081d02d80d000b0b0403010800c020300000080c1130b401743e4842c0342c03c00c2d0320740d0640030080e44540060364010000c010341c100321040764100e17144103903196000030100c80c6009108400645800030788a01144d05010383c1c0204801e02e01c03a44540b07484c0541e610b0395540b0b010030b1594000c0807501030440c028002000810ba40001c0c00041d407110500582c050b0840e5074141d01e83c145550b0b03ca5049034120712490134a460105c500f4465500441100e0703000c1e4441c03015842c0d00c2849654540411307440304034065101400558100d0070000c1c0400150088500c03400c890560408509030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 45963313 1250 45962063 45962093
    0xa0513090e06040f0602130b190203090a0b07031704050a020f010f051210050a0e0f01050f0a03020120030301090608150103030f080408040315020901030e07141203090d0f 75
    0x10354606004120155404556203602c1a0302102c001c10480300d5141c100000e01400328507110242e0034440126040aaa1000b0854506491842c1c980101100c034100d90b64440d40001c180c00c8519890204030345100180501a01482414100fa00707030140201e0303180383c1504403001c0c1d50a6118100603070940c1400280f01e240c00740c0a1800b00c0e0001030000300500b10703100390f082d00c001701c030400c0001800524401030040c01800e002418110b165a41e44128500301c2c0050b60140c404000d12800010545007041221011070300203491005803500d03503001074810450f00c9041500035491445200214202440114080c1001e500000b55a5082585141c0b920040b040c16003102807800005002003604015810b440d01418a411500c0355501d10b4940302c1402503605c000c0c03004990544010700b4400395009040342c00030a0f41c04001c1800d004a5681d9181107901c90495104148050b102c211704080a108030071100500880b0700d08122013000c541d02076141103060388e80b40c1c2840c480c0001c0100700010a6a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 45964563 1250 45963313 45963329
    0xd0e01050f060d02120a21050403020d03110115031b0801020c0303010509060102030d0606020622020d0201051e12010509100602060f100806070e01021e030f18060a0513 74
    0x40c6010450481c1044000d4682c52282012030f2426085554001d504554103c584042d500007071103916019000c508025058030694107003010b5981024450000d4a04a0350003c08854000c1c01c1f5032002d0b0360700480b072008404203548510365a4002e2010781c0c2440700442c800d0395038040341d900c010702c0072a00c45038035006100340d42d004102003101403c0000c1602c0c1940c0c3c013114040e00300d40b24040143c0c45c40c890203030081c1c2000d0400000089150300480e119215080700d10903c084181039044c030000108400b54002d50100c03c1001c42c40240d44500046c014070581503010b042c2410303150786244040e0704000d05140b007000380b40c00140f109013441001c1c40c2d08108182242c40c02203040450103511003000a14021000950a002410b26240306041400a10107402601d049040090005100c0080c500449003d131080c84810305010031140c0da40031800080c54083d6003004421240304286070322520007402c84001c0030341030382c46c1130b601c00d0020302111082e611003a66604010240e5074405038507600c003401e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 45965813 1250 45964563 45964571
    0x81008031902121e03060105070512040e15030318010201060b160203011d070b0304060f02070f051e1b0312040f0e0903090d061e0e0d09080606011e230d0e01 69
    0xd000030003004103c02080010071481e03c946d9648012181d6000c0c000c000340252142c21200303a20602148020030981f040074840804503515080410011140394100785e406500400101c6034010040c00d030540300e0700d41440081250b65556401801c960000d030840e0140103800070f030140c02c600d82449603280c00c591010700c4c0c440003007007101c1d040d4a8404a21404004600000006d01000708540c80000000e03502d12003191038544500382040010803100b000c4600f4440c4400201c0720b0501c148440900c40354041c020006406403442e10401000c0201c2c807070b5014030540d03600414660313450001e04058000030244160b05460f08800d501d02c60b85c09001d4107601c0d0010408480d9a4940d4041100360603000a8003103028120b06070003000785d0074001c80c2a0011858800e061464080209818000c0600c5684003250540c0320b04109803181d0080da061400700b0000c4117103280c40c0544103528503088a16080040c904032645000b43c00c010080d01120001c3c1000048000c0d041280d0b209203040c410010740200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 45967063 1250 45965813 45965827
    0xf0903020304150e04050c0d0b01110c040c0504031502090a060306060516030c050604050d020d0e100e0d0813061e0c0213020708120403090e07020a0308100803190212 73
    0x10791203105900800322040242e00310940007901484e012095000c010304100f201e490a01c4000c4456002040c4072004d8a007010003a000303a42c0b144840851341d42d02d900c0a04600c007203480030000180100c41e5035070144078090000002040c0348401c101d1640b0150b039005a542c440050402c460400c49410a4090500d448400c0c000144c1c00003d8620a010000c40303201440d03000c1c00d06898001c5d4000380282144a01c1c000c010030024041003d401d0f0f844076408481d21a4ce03141030a64514001212041c7c008101e2071403000341511801c054100c03c9030280c40f80600c6140c5441c1c8099680c0322044440100071807400403c8103540c840c9044070386102d4240254104020020010152241502c0103441510034000005081c0d5195046500c030b150b2242025644d46000124002003a10031a0140c1c00728002d950001101698080c82904c12203082e07024080c0203901e1b40c6c0660315108081d000a1495040043c00f207200c00041000f400814080d440058500e44110b400074508000024000b41d0404140050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 45968313 1250 45967063 45967067
    0x6030c040e06041107030c170711060f19020601051305041a090c0a060309140a0c031407030f03020a0b010f0f0308070204180b0901051b0706020304030c05061602010f0903 75
    0x2440c141d500c41c981d1040c1c607480e020300050141c26015500940d20f0f00026030b0070105070b0001108049240f0800c1004002e1802d1500400381c1d006092002d81400214082e0000b00c0c80c208008019680120031290b040500104044005850402603032005da40250014441d900e000402c1000c02c4049071014007062806950b006130800404e007490400c2c0540d0008185802c50070300c01045d80301c501610f09404203a60740c000401a02103040d00752426071040c42c00c41110080400c030072030125000b061508a1603c2d541d10110252607202c850011402206004400907403000e55a0b40810300a40c01001e101e40e060510410004042c2c0c0912000c100c0030f01c007000141811610340c0101c1e134025041d10740f03404050000c0f4001d0003910304000610a1600f00403000c200d5442c602c14006c3c94070100801c042d0361928004c44060000750860305904205000c0480000e04580044d0f621902c20301e4a000e020b00c3c02d0742d409240c85002c0d144107022017a1808280299542403250000f440034542c010300110300d8940740 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 45969563 1250 45968313 45968317
    0x3030e06070c0b06130e16050301021204021c0503030703060503151605092107060f02060c1c0b03060f1e1902070c0b03070302042c1503150405060906010506030c 71
    0x1d03d0036450800040c0603035100000740700400c84816050208510044940b41c4030320240602041000c1692004070302ca00b814401e5600744d511b03014003407000b510345d5020403400d200420000c0d0320b650449a0740c0f90000f034062000c0c500501007a180443d005090008042c00c00400306c14a43d415500d0004000001c42c50b00c894000e2401913050140d42d50300b207400421200c05106850f0511b60300d0310744601d1480d1038001007403000c4492595400309800440c1c00220f0f1035040650b13012083c3c01046c804c4a4442d034201c8100304900340c2c102400035510601c00e02280c2486c038200c5010700c1d085817031810083d207a24002c8842c0800400880d81e00720b1807428446285111400c0c240d050000d50380400c03954100440c145402c4090040506a1501ca2410010060213136102e4050f000070a0012190440318010042c070f4001d4a044c0b400c144001580c9806c094180d0859103010b0f01ea05100701365801d07a40c90b034050340b218015409500606002d00e0290405860000180c2c084c5016480810401c80341c0001641 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 45970813 1250 45969563 45969587
    0x6030b09070e030f01090b09121201350105100f0506030103080f310608011401031a0d030804020f0109050102060f09070506040b03070305090f100b181303030e0607 72
    0x144060294200b4010074030341500d00f00d120691750310706080d8906000c0035a0301c443c42401d11804644c01a2880351050311030f0300038a201c09020004210062040d200196041c0161014101039881880840000c0800180c0d100c0d0080700c081c1d5650040c030190301824a6400050291621034056240c03411010075858401440043c01c0e0620202c0c2c0c6550040100c021203c40c1c8405039a6044080001e00101c1c031900000000b8490071400c4c000000740041c083c166060490744001380880e201015035005502802c1c00868220344400724500c192096640c1011288940d0f00070f549030b14592425106000d00b06010918a07410b124515008014a81c0e0000300c199000701007050507885a103035007410915101c411782155a100301c011078041140c504600242d8442d82c0d0796501400350792500c1c401136403500303170440746406560800c15442c1c400d41ca1a0304421307054035001d401e1b000f9000c1c40040c0041e105e103041d0745285c030300d805801e511810b150b494019284145440700c09054541811440606014100e003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 45972063 1250 45970813 45970817
    0xb03030a0909051306020417060a050105011707020708100b0102010f090507030f0510090308090c0a0302131538120406050a090b040c0f0e1003060509070b040306051006030b0907 78
    0x100004040a13401c200720780c002d95002c40190f4641c1e4846000106c3e07107920000c000414812030700000c45903104c5010710382c100c0301e0603140d0854072000140900801000145403d044d482100030004200208015005000001c000005005128440020301b034405019207020b1041c1006400c00110703c0201e50303802100d0744a000c0e0a451846440c00d10308000d0050b21100304103141070304103000e041d080070307130544030341c040c02c0c140c803400703030340f04042024040940c00083c0d0071a8020710072600d0301c503a40e17010f0b8840c60410300c000c045841d41c5507035059552500702e203048040c0220b010008082c640050340401255002101c8078100b051603640c040c4600b2000b00040e11480c3c5031800300d650107049511140450350070181c1616145007608007840502c8240c801c01c12401c104a100150240102e41201c1c050041c508000e0386951468a542c005020061b007010124010501d001590400d1368000b03000031480f452022680c1d1400744c03103d21180c1500c0d40f00c64141420450051200d584601620394090018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 45973313 1250 45972063 45972071
    0x9080a050a090803030903030f0906090a0611090910090e030301180903090305010524030309060f0d0b0907020714040c020a030810090207060209030616051914030705030a0b03030a0909 81
    0x1c141107821445903408414540000018811104000b0008521403404207200d400135803107480480b550b603030382106d02c071078140c0220611070001192500702886d4040d91707054560914212a0001e208200c0949226003011f41728482080b0307207078080c02515901018100a14199850300c1802440740303801013460049540c1e603102c00e600305030150890b08040c1d600301c03000304518988034080039007040079000d0305109400c071072040b9041ea03d000400c940042c0c00250500d42403480a034001e015681190b054101c5103500d4001c03c08a64440d1103107144210170540c020800f1034640801d010302110710071207181c01141404403e118258001650400c02949032924242d541d444a510039050300c0c0710f40010400340d00000b88042480307190780103065601001c80c1603c00a448520040303c016a0f0807a070f1340b012131010310008050f840c02ea01104141051801c2164040c0d440b8038080c00b945d441101e003480411004014416101254827030841d0044041d80113624140c00840054100707065071007071a0b10036440d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 45974563 1250 45973313 45973327
    0x40c1b02010201020d020c06100509011d04060f0203270601060903032006130204050a0504020904021905060d0c032003010b0f070204060602030712031802010309020105090a23030109080a05 83
    0x1007541124054008241c00b10740721108020f4880e00c46600349d5040414004203400451a413030b180410f141200c40903104130b10f07001e10140d81524815001402681d06540e41d101404c01103445000651092010b4000880304140440c50010034003c02040580180e200e0001801101d80180940041d640c150034140080540391016000c921441c80111025000e08024858202c4006206458071882100c080c08555151040c0408840040f10041d41c0a4004000304001d070034841c0c5200c0d070b22403082d6400440652030f100405c1150748402c800c0400da6982d096001c2c6400d07030620900c08002040010343e81041e441da800c0350303c58041801040c80c4604005902c40003200300c0c10403502c1941c0e0107001802180d030346000c081d4990f00000790590b02c04030301e0864030000d603101e4403c01c0411802d518649154040ba0b4004400601c5500c0c412410b211080000c1861a520904594010700204503e0408031240007810622100025031407400780c0c1c100b1900f040043c101d6029501d6003885445d100b0784590b1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 45975813 1250 45974563 45974567
    0x7030e0a080c0f04051909080406021b03070603180501020708090f03032a010e19060b03060c120423010903021b030604110a031a01080d050405030607081911070b06040c1b0201 77
    0x101c2d81c80c043d0003103141c00c502002300607030706000d00102c0d4441e03025a0780154501e50702d903000c15107584055a05401c18a401d0041038082d030b10400c020766603403500b100d01d580e540e0b40702c6013242d0220606a4000d5404219145585850544060b088400350055400c180c100591611031a02c0b5012403003101e05044110703200380c1001d510021700c4030383c1e103800c41d91114541000c1040c410208030064a01c04d081185014140c10001403181c0600030240d0040c0c50030403208140600d100c03010b401240c8506402d1802845608046000d240062950000241200390340c80c01a180400781f544440f042e01c140c0700307000394540e40450f41c141d016410002001c08959810b00050244500341c0008180740d51807280d0552012110003018142c0780e40700c003241c04000c0750b444141c485002e140700b000d80c1a0300460004044a01c1000001d4100c1014120030902c6143c079404801650444480b114107172402041031028400d695503100d40014068404200f00c1010800007010b02080180e00c01410020005440841e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 45977063 1250 45975813 45975841
    0x209060a11010b030a0b041122020a020c040c110c0907050d0e0f120304030e030c06030c161401200c0303010312170708010e090f0304120c050607030e0a080c0f0405 72
    0xc3e401001d0760340301412803421350030410701a80d0a940100c1603481003100781c1403003240300b000c0b8540250300c2c450940c100801c5001940c0f000401008500600e003160141c1d444600840040a2254894003000020744400030f10b0909625082845462003500b40610b840e0080c0882d83e10401d400c00c00700311001c3c2c80d61024541341250207803203140e00c03851181c04501080a4040e42c0501c1c881d80e21452104565010199111400d99115a01901c1040802c181c1c0320040002e2802411640480b101030050707841b14031031203160110300307807140c0d45403002c08628a002c515112415443c40e40300a00700000103191a91340c1c00140001440d030004940041d801a009034002002407020924001007403512180c01031101170207101d0782701d200242c1e50201c1c1c10000042000c1c1204a80c85005606191410f0725210520300700302400d840b0202d100402082c0c68607400000c103401402a00c803070044d10074039414008042030541c05000c03030b0b4021180d8001c040d900c440901c01040c20807a4040780701d8640c00c54141c84a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 45978313 1250 45977063 45977081
    0x90209040204120c03120801030203030a0c1a010e0a060501030911061e030c19020a0f03180302060315030c01020d020a020405040305210402030c01030c090b0714070609030507090209060a1101 84
    0x951200f0491010040d000141005892207500c140303110581501080d80c40312800e00000b036151300144401140366102e0320340c099800b8040c02150340c0a0171782ca04868540207013030b08505031686e007c0c0200300f035502c80740c0a01c1c002000203180802a5202c0e83c3c231484680d20348000e51134451880042c809800201060f40d1102100440c2e103a0359403800c010310807207850781c41a2481d070301801030580301d08001400400e021813440c0d0403090000c50030138542d5003298a48200c05941410902c40c2c80e020000d03031030303280240d84a600d080b0098a4400900002c25141a0745907a1650441d44081d51170080c00d5400318500003c80e5055134080340d543c46918041d5010b000b000d03039400e50070712504000c009a03606000344600450003602a524051000c00044003610800314100000c01c03400c0380c08201c088100c00003410b01c0b40c018a21084462094600207081522651043c000284040030078014008280304c454000e100c2344030118905080c14000c00c04901540311040c050000410b460084820290040c06203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 45979563 1250 45978313 45978329
    0x10501051210020a2a03090906050d0f0309170601030c08030a02070e1504020703081e0618090f0a0c1802041805060d05240c04060903080f090d0317070e0a090209040204 74
    0x164111030020106040d4180d0019800107d40041c0010b00b8855403144109031003014100224120071903d60702c4540458040c111f08200e80c03400300044440d0340d9060a6101c0b16250060071481d4598144200c8a0503d900480078035007007006420102070300060420101e444100b071218042e6102d036044402c0300c481d00c00075500980000b0304501015442480b080c800c2c1682e254402c032000803602e5030032542100316071860700051001c40c00c98002c0142c685a079400113900702111400c082c150006818030392039003002c0b60121032403602403100041d220208510010302241c110708061800140544100081d110300c500569a50301242c1e994440c40200c1c20803e800104486214403061260807960507c64070500d1b012080c80c012401c2040050100c030111651903481c01202070954450505640c800981d0200c3c0120400020392152141c100046460b07019444804031560510b80c040c411000003020981040344103100d419541d52442209800e030f41c240000183c48540c05000b090003031082d44c0002c03807 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 45980813 1250 45979563 45979607
    0x1080f07090e0c030a18050d0c05010b0a0f06091a0702120c030d0503011a070b01050405070c0b0403021c030203060901030b0a02040f08100c02060f070c0606180e010501051210020a 79
    0x56001c0e140701c003c50140031110410003c2460f106506e0801c04d03058034006205412a0864105c49485510000d01c910b010340000030b000003a18000070410b400c0b40d800646200380000040080c280c1200c1c51000901e40f1001c120002a1603414541e030742d1041800007840341c00320386d160554660f01000607a00705c030006402c4420540440c500502550402d10907240310801800c00d0750f42140c0c500c025501c0c007543c0f00d9a142001c0e4240010000a032100500d9102000821041000418651149680a10b0094001d4a404003200d01c6c2090194134002c10002854010000c2c00920789907401c8290440f504101500c00c9034880d074044034044d00c1258826101102008404106618042419404140034032420000003006050982e11085c040b1042082004840002001d1314019542ca000781ea1040c000010103e84550341ca044231b9005071601100c0c0ca948580c1e03400f107208240f248030302500c0c08a406d6822a544050115560f5040001815886402252468440f0b0080c030300401d440c81102c1c0045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 45982063 1250 45980813 45980821
    0x51302040f0506041a030a060216050a03260603030a110309100905180910050c0f03090d0909060b0f0705011d2b0e040c0c050607030605150901080f07090e 68
    0x50080c0c901541d195125038600401002c244010000170f8055100240283c01c0191300c98072040002c4d00314041d059203440701072482d50b0008500707000320003181d407207500e84895000c0b07900380300340003500488403c48211030302e44188421590300005a4a980002d4134005140700d60041034242140200c00102d50003010901c40e403924a60051045405d0712801ea44c103060301411702c0040d00988a041c3c95007205500601c40940c0c4c0c046250f00455884407486009903d00311070040740702c010350b10481d03024002c4d0300844200c1501c0f41c0d00038010001400c0d0200244506030419056a501c2d220b40d41002d0703a01400011081c0030401d0039040201850344541c50b10445101078440c503515481c401050111610030403001d54000c5440382d1601503030482355a0b03128512200c58090000a02e900c003590f44c10320001d03580c0c0c0e10016404102481c031402e00342c0c2e0041603403440d003401d0201d903d02c000c03d01d42045070203000c0400a80d030301150380c661018000b00b00c1902510f40b003600f03940c00300c00e541207802080790000402c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 45983313 1250 45982063 45982091
    0x3090b040906091413030f05070f03050901020d02010915021c021206010f020f0601140d0501050a0b0307080613030305040206040f03050c0a060807080403050f0408060901060303030b03060112020405130204 90
    0x100f2148101c10610445000d00d002000380c0c0c80c01c071000404140717014454804a03101d8507000b0088003c2e4185146804801d80318425417100d4204120002540040c0e520555603050108981e6400d141c0000e00420000740d0724003a8070a412003510411076130200d080e00203d02e10079100003a00342c0001007150394141190020000300b404030741150100d2184010030140902c0004c1c20020300d200300001c2d0400d6401c10218900c01000d195000b5807001001d01c511000c00c00c28440e980c01400000000103810717010074181402c022141d404200241c12200402071610116203803070042c40d80c18500014036030f5a5100090050207a038001e1140074009282c080b0410030001803070000b85004403070000b10541c1c0c4001c11150f042045840c08000b0703803480b0200d000240900041c1035980407400c1400d0a01d0348545072540b60500072110204140e4441c0c2e0200140340e0584213030205004190088c2042c1d40c103001e440314840640c00b070000c0c00360f90307a40d00203166003d4a030464914a03a0060051040d1107075140e107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 45984563 1250 45983313 45983321
    0x1020408010623013603020f0d111201020403050f0a0204050a020307210b030d050d0515010801170a0b0c130501050306100e0a0b040807090f02042103090b0409 70
    0x22034200d0340c605080400c250702200e03030010b50f6185241928914820b4a401190f500e0508442a800300035456061a00c8507074940c800e015000c5800e1007080c5861542c0100095840c01c941002c2c09103440303070b03210b0f8003088445c00041c6006500b685c2c801d100400e0030107030900a120303d81c0068241e00480070141030040d40894220781e25402150300340151340310340d01d980b4101d00c029644d40d800700798004541c540d00ea13105080740d141c00c0b4019100091000d0554082401d005541c0c2104000035000a14912024460b1040d03d410071203e008071803111000c40c0001c1c0c03050340c040c01110400360310300e0100071034090100200743c0b1580d80141c0c10600c0f4180801502da054208607004507803802c50038400700312944a1026240304400c0200a0541c002c0404819240040103400c1e00303030010281c09002c16213980c9607004000400f1034200601c115407900b20b9040c00c4859108200080f18010481007085141e001c07210380350ba0300e000b0f220303514081d4940b43c10780d0008201e502c03818000c20f006c100001c5910440c1c1c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 45985813 1250 45984563 45984569
    0xc08090a03050d3b0d080d09030809010902031222062a030203040506130306060e040b0a060315111306030606110312040807020a03140616050c071a0417010204 70
    0x484540c600c003184c80710a4000d0300c03d80301c3c40c0c0400240300b401c900d20311510380307041c400d14003e80035000d6428243c4070464141c2c812130b012002103803103107070000425034040c003126407014552000300894a50b40c0d000036221110300c5c204400d029070105800c4100c407181061450b4241451100e101d01d280c0da120050a840400340b8801e40780404000c18085005501d020001d0841c0c0c540e001c0c625142c108010400c01740c000c10248420303c0d81c00c901c00703c0054141d206103405010483d030b40440301d107858503021961032030041c00303946a503044c20410000202610399881c0c0903480c450000c00d9403401d80001945a0240345208402c40312602000034500390550310140969003d84d481c040b003000100e50b03542e502c0c810000f1800004965400040c04180884064800c0f107100501d40000300350350740c50f4032440c00c400030014070f405c1d0401c0701070140102d052201c01c80301c10780c0c5080243c2481d0078001455290a06440390200030410200c010ba00c0a2103c0308440c041c0007400108041c080c0d00780f415600070b41080c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 45987063 1250 45985813 45985817
    0x601030f0308010605030906010e0a02070206031f050d0b07050304032c01080114060d0c050408060420010f020a020f12030c0703170301050a1a07061407030f1a010c08090a03050d 78
    0xca04c0398841e00882c0d1292103103000070b220a907e030514004822000030054800b443d400d0159000503074405000b540116203200d00c9a842c107403491481d0452780302ca50702040c8601c2c072101c0e0380800030f80090100e43d4040880c1c10190307200c3d5524201698032005203840f12058038104003030311011105007038016003000d0342a03980d0000c9070703200d003c258401030740802c0669001c00306000795000c100c0305402c407942c14400d914100b410301c0c2c1d654205078034103881640c3c00c58800302c00c01d00d50381c05035024020112001c4800d10b4810400241008061b40342c3d10090130123806002c020000380220b1b118104406105d0421a0131291f07201500c0d909261070318070602085403003210040d00d80b8070041900040e039058401c020030302c251040ca44103c140520048414a1840c2402444441c011541511600c0e50040e4020a0442c152400010003030889421440e039101d03403860817840a1503062800a650342451080c00c02000302105400c2100e5240591981030b80d00c240c0b140004410030601080440b01c1145079 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 45988313 1250 45987063 45987077
    0xb04060b060c030a0e010305070e0f040207061503140102070803060d06060302060a1706090105010206060108040501060803031003060c02010c140a020708030d1d060105010c030f030b030d020d0f0309050a08030402120601030f03 99
    0x10000442c148c0710184c5120703001641c1443c800d4003900d4246c0e40315141181c02000145400a15921442a5406550544481e0050180c200140200d610050307000122001c000c61601c0b1705a640c0c0102c0340001340c00305008021071610f480402002e51b1001d0080e40c1c00400c0d01d0b45440880700000c05801d4182c6034008040f0544e4003059081c100032004505840e8160007410041e0b85900c01142e008500910a84007503413501400034a40d00203000031070150001300f080c04c01c25030641c209a42540e0701889070b401160b1510101980c5164000b22518a0b41c9050480c0d941d602c4108901324a4001e1980081c1c92502000910000d100750313036031050003003a06640c0ca07281c1c02c01a507056941c171a84c0911a16000c03135640b50701200040d228500c840a400b410f4100052402c16a1001c2031624a903512404013613440480d032246140d40000c1100c100000516013480419050b030354590f29001e19131002001d13000d011020030304540c3d4030214083e641d4108404c40e125580e40e070030005140d103031081c0f01364040307612 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 45989563 1250 45988313 45988337
    0x3060906080309040c0504270507020303090606120a0c0f0311010f0c0308070c080310060e03010b0d0b060105040b0705010510060e010507030806010e0307030b010519080a0b04060b060c030a 83
    0xa0082608031040c5001550030f0405070000d22020741030116502080003010400400c0354125200d1802110b503d0341d0090f1522000c100c0ba0004444010788054190360003402001551480011042ea000d01c0680d00b2000e200b21110703800c0d02c3d04c003602d600241400d001210204810300303029a0724048034000c01ca201403244a035401514207030108825000050100c10740c080109008984260304801186002c00000b452511356001ca42c0040d26600701540ae0500c00300318a0754444980c50359010100c000b000304011341400240a501611001000e000510b40054410b0b80a0000d642c02410451015a515800c6144c20360090100b110402686540303003102003681445001e80c09011441030715007078680728840d01d050790304020040c4850b040100d045032414441d2400c0c06070400030362182b60606441c0d410041003083c0090009000d0100c088502030030040a0340008400110342d803ca400a03030350340c585003480c01c090a07006001c5904400c0000d401410150000020300c0c41c0c40480d614040408030f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 45990813 1250 45989563 45989579
    0x4091a031204081005060d0c08011b08011805040c050d0f03081b07080309010f020d14060f180901020d0204121112120f0712030903021203010e01060503070201090507080c010306 78
    0x2e203000700012603122080c02540009598003a98100b0030040c0070101c40c280c280c6c2d540e6070401c856088880c40b6512084e4800340d460a00c0c41c400144200340c2094041903051602082c50380300340d0b0b0a410441a11140401c007845681034100c8041c180280c445112000903040c0103280c2200054120001050301001581c0c4000c0e21411000142c295200d03075142254940758912107400c05407000005540c0c0724085107140030588010f2450407d500c0c0017040416481e15140b040304401401d04c0e009400a122507101aa10b4101c1c45401c0e80382d031240001c0c961600b010141c0240101c950f822860752000401040440f07136015003c140c18070a260240c40782d590700d41171000c90741795060503448651012500800003400c100c090001000c40611060501240741c81e40c00345648030b0382a24003c0382c0d440304000141a8103103c1010054450030743c191542d4034008480c202a00305100e4401000300200c04221803900c03e4000628a07038000d4121440d843e124441035441e5400000c0030350209140c0074000070050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 45992063 1250 45990813 45990817
    0xf0e010b03270f0a03030510170604081303050307150b0402070c090c020c040204030b0f090303040b040314160b070807020a080f070201052208150112020111010204091a0312 76
    0x102d045038040380510b51002c2da0503000040c00c00103090292444011150804000c034014590282d40c1c08101814851002204400580c000d04c09134030328100c2c6910309460000d082034005500000315a80c0e21400e840303160400d50240c00040c014007000403010203205e0250200b824030445004100580e50015080004078814240000c20081264004002261040c1d001c03c5803003e050040c1c0d01d441c4070b8400010203d13402900212200003003003051181c000540d2880980c0b04691500031403460800352684100801e0040004003009068113404500703103040070a40301c040f94040c1c0040c450b620545440d051852013251810000350000303000400d8103200050220f40340e50003841e910b260201d14214041ca0750f2281c05c00b43d0511600301b014044034459007840b0b00141440a002c0d1104c0d0303040a82c62420088a04406403000f10048018844c0450b0303902045165542400e03c4800011424042c03400390240742d000c00145031600421042d0058034400840d094035007102910041d0716814603605440c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 45993313 1250 45992063 45992071
    0x3071509031704050f0703030306030c060201020708070618060509010e0114010f09150f0e0a0606090b0a0e011710050f04050106020c09040c0503010203040f060f1109010c03050d060f0e010b03 84
    0x107805403103010702250a140003903000b1380201c003602c804c0043c03204101d14051195104a00180d41e816003001030114544045000c2c0010b88029880d0103c10b44030301d992070003200405480c40b03135a079a000151480211103450180d0384040144000c2c035041c4002d50003032441701420383d050350800f0040c400f1032410040ca07038180c6841e6003094171050b00f4003040a0081c20f4086160f04d1045c040000420b140442741d201c0002003141016411040c94800c143c102503945907404001030000d00502440380c04144420343c1d0b50104075240002c440a548030040b913100010b109940060008403060241d03030440c00111a080d10010f58100e210082c04134144030131114240b28400c01a000030410300384500c0c100b0105600b140c05242c5450527640c40b4070000c0c0c03ca900130b403405c03034120031402050400c00045000e0588802c880300300802155101070b94a484902c90b85c0b800d58100300030001d01e0000c2601420580b1050301c6168000c0101c15100c105c00300d0b40c44000c1c0120a145019080000b0390a002c1004503442 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 45994563 1250 45993313 45993317
    0x120501140c030a0903090e0414190206040302010804020f13021917010909140f01050106030605120607050307031503060e060603060405070b0906120906041e05120705120406020307150903 82
    0x782d90303150725200006190b1501d080b42001903150002800700f2001040f240514010b88190040ca400450410300c0c10645802d000c01070304407090040b0250f52210705440031240c080c00d082965540d03920004405080d800030071a440144100700030020784080d40034211980d03540d0000361000a01e008140c40c04810580d800c025440810b00501001c00380350081003814ac456450a420002d0100e0a01d08020238003500c10701e181c0d911401007000e039615014440040000f030b40c01c40014052222400e0300e4940c01071101c42030140000c0170410491080d80508003064507000194651912880c00384050007e00e11603d5491180c140490028980441e40500481d80b00000b45020392030030390002e0403078101295580d4403403818490111801c0302400301511542024025090b289030500d80b140f01600c02c1105568078850342d044c003400050780040c007911100b10910f015038407054203242883c0b4182c503042d40210710707150214000603050717000805005900d103e00a02c6185030162414401120000380c40540 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 45995813 1250 45994563 45994567
    0x2090406020904060308211006020a0308060a080102040b0c060a0b130b01200a03020d02011a040216020a06050d060e0f0f0406060503121308070f05060a1701120501140c 74
    0x100080c81903000304001a4041c1000c103280d6626111382510750002c0c40380c5c18030040400030803104000840c04841c0d02149100344260103e08140000f580c0390351401c801418001d0450100e041a5919428000140034008c008d5596603100e0088668a80055143c3c44140c829040446c03002e50140c020440002c601800940b0390404101c0030360701a0460303914250500401c8041d40c10f0141c081002001e0740540000100039643c42031400030301d0607408500340c10869140c1012001c043e14516010080e816048a000d03031030383e600719041056000300020013507100000080000d2595001000307409103041032241003001c56911404d010401800b1110f200011200100050021800c0c640c0d4580242c001c0d9000140c0c5521000824540075098400c400710724000315560190b44108002400604001e030042c0c0401440e110241050072400e01a0622940c8003240b4880700070710554101745800002d842c410169651090100c1d03181d080b017801170b2040e50a100704080b00e5000000c0c2c2501030700308025028 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 45997063 1250 45995813 45995821
    0x40602031206101713020603040b0402011209081801021204062f070b0a1e0207090b0303090306040f05120a08070906051201050108060402070501060e060a050d08030a020706020f0c1501060504030209 87
    0x240741c44002061085c2c40c2920040c80409038591b81d025601ca18826070b05e080050900d0300001d03161424107110801114101040b1000245900c0151240219020900707100c1002e114010303030900400c5048071401901c040b90000f101e0341d100398010f0415503004103054040114000d004490040407482c4400380d48181403c0000c1c11000008051003241c900d000329049000342003104034400d21031151001a404602c1c28030a454161140e1b4070318050407001145000e0480340400c0c0c44200041004d048489007042100600c507051222401c41c02040c00903541e138a92504028018400c19506000050402c0301c0128480380181c0c101d0b2220740d03414082036503e86ca8000111013040004200b56001502804002c000880234080e980180c01e90011407040d030f160290031f2101021070b07540554820b04800307442d0000304000788102c9402181d0100c1c0507a8030303803007030804402a00ca01061145c41a43c00200307070054900104103040140d000c5105150643d03030781c0e0812105030040b808040d611010a030045 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 45998313 1250 45997063 45997097
    0x212010605090c04060804080f041806030308010603060302030723030d0f0e04050405100c031803051b0102090a1406040f060e04050106021b12070302060f04080105070f1d030f0304060203120610 85
    0x4d41074909c04107000703610301501d401210380701e4903100107030040c225200d000038400c02d5003104046014050354581044507500d5500060350350201c0b40b268508040c0a4a0010050031a0800441314000054221442c04150340001030104104a0b07035200082c01205080f41580b401d8000c45000d940c201d0700802d41c60854191007402000b0000c00c1c6028940d03200c021300058a41c03c03d18802d601d01036260f054550000c0c11280308142074014900e640d50344108081c02481e41c0300c0841e8000e9070702c11207503e4400c0e4a03c0000c60450b100360f070440961401800b03000a07a1541c041e1031740c0c992540544003032100380d903210016a44c0319440074008044910034407001000781483c0c105d610483c6500740c1102c1010360341e40c01003041c5a000302c01c60485848000350501c10746000740129a0000e5003403400c0751002c900000f0090205100880419056241c1c020b81c1c1225a82005280c41c5024103c060340c0e40d139686e40c0c80103903a9500407820044a06a800c0028a00d45002c95040c440c0411580754a00341d00010310712 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 45999563 1250 45998313 45998317
    0xf0f030b340c050f030d0b120303070c0c09060b0910030c14090a0e090609160303080a0b040b032a030c03100e1009050c04060806041703070207030212010605090c0406080408 76
    0x25001c11154500103804143c1c204182c0000205003006183d60319a080361000a0b280800306160141c25952400480e608000040703e6103c0a10b01d04202592014a040b510a00e0503a04c040300442c10001c010980350f544600520a07608207c580a19000d0f42c1030041d0251841d000303d10300403c907044004117800040900401040800071f24150740720f5118201c3e120708800507646044035030f11040401c000b40d0300800400d102d510030b07403032000081440d69400600b86c3d0b01c0106029000754a5502c80013160710749400c8041d2008004007921321007041081003c0318020700140d81048620112107220242c107000c41c400c400a48081c002d0010201d03204038800c09001d141070b40300700d10321071020300440206041c819405130034419170191010b014030100300701c01c0d5190341e0080c4074070b45c102406020000341a10813144040c1006041180c0301c0e030780d0410680c2019810b51010b5005003207074004242e011410344c4100140c07030381240e90f80c0302603c88942011050180c1d00030100410024400f080102c0e4203400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 46000813 1250 45999563 45999661
    0xe01020f0304030605010e010806160c080d0207030f030f06050f0f0f030f0a03020105070302040608060d020324040203060c0a08040809030a0206040308130504020c0a0305130f0f030b 80
    0x4452550864940c02440c6600c143d2083c0e44040d40d0314014071403c0a02c45209004114910060281b802e042c841c02115009010143d02809881c91f900b00c10400700b0001d4400f030114400703045403146078a081c0904107070b8039141407900280c6414401800890940f003184141c80014000308184039001042c005204400d0328456400428001c802d50390359401c11162411603c520f010301507204040c130f400b0b03013034601c003a11800030700d8010b01041c4100303030741f204544d40c0c0500101c4440c2c007a80a6800443e0034a070381c0503074280342401c01c00d006014442d0b20f1091940120310aa003100c0c9141e560030300031f1030307507010b034041d2000003540343c901203004900d4810191030130b00341c018140d0b1403c3c0c0c801c0c0e0000c4d4180c2d115a0040701c001ca07002c43e40032020f01101074001c0080ca0159070035890b04920281184d260140104020140400882c0c05814400c40c900403d018054a0384116452030b1103821480e5465010302c81100c035016510300090307401c800f00180b400201e090f1001d400034969242d58040c07010321945 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 46002063 1250 46000813 46000817
    0x2060901021c0906110301080a06050901020306011e09030506010f0305160b041208040b0313120804080306010f030b0901030f17040b0f030403020a0219050a0b0903070311060f0d050114091302010e01 87
    0x45c50681c044010b10040d4000c119010042c6040ba010f440c0080550707900411031200d43e44140100300007030340c01124000b000c1103200100741184800720f401351a45001031300081c1852281400114100381d90040c3e078406d580c00340049950143c00319401c050f48000310300845880350802e11041040d080e1504094414a05c181595824103480e00c440b80c1094204544101900306c1b2000c5400501544450a2100038842d146c00c1c205807500d80c6a030f038602c1c030010302040d04000d4052018402e240c0b180e445049a0040200b6102d000e5030b4a040c191403c980c1007005450000c1442c40181020f0b0410044400300c0340340c2d100d00b074209100c000901c241c5801c0204190154000d203980c4500503134807000807500010340d01c0d1050748004c0c20b04007031048580a507000002c419008102203c81c40c3e0300052640c0880c0e07403007000789142d070102c14045002402002c07030700ea00341c40d40811030200c80300301c5410481c1650718903080442100708440802c0b0642074281d40348600c0c42d81c820806000b44d441902825075880e418 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 46003313 1250 46002063 46002071
    0x30703080d20073e010e06070c03080408010507050c0a12050405030109060501080d14090909010902030703050a0618110d081e031803190c0507150f02060901021c0906 73
    0x181c505190541e22060040b51100380468001c005100000b610303032840203144e095400b0215482c90b40c8100044041403040c18031024624003449680c580f01202c1001d40d1010640c0701c0c0940c0ca140000c0941c1160040c00318550a00300014841886401550b01d9140410300801e0700c0040e680344c1c0d013040324500c8089403c000c0308010200710f5071002d0040d04180780c0300301400200d035850900e5075410700a080141500300b1405003220740c00c00c10002d0644107403800c11107100c00b60362a44462580103040001c4001d4140c000c0290000510101050b014400c034000e0400b88244040d00d49500c1001e440f41d0300c0140000d0601c50700000c181061200c8c200d11383d1007030540038a44141644550040d6015100061310180e00004001c10107801c080703014000b045020066090103070007032011000300d00788905101000156203240b0140001002800b0081514566004400a101d00002c1030303070700c0c9104801c01510a10000c0b4906000504c02c03940740300144030b42c0d8400e952580305074070701501111505407041e0ba00c0b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 46004563 1250 46003313 46003361
    0x20310020a1805030609070b030907051206090c010e13050703200a020114060105070b07030204050411030604050601021c0e0604030507290301050d08031e01060807020705030703080d 80
    0x1940c4020992040e142d1614020007a003118210030b80c49150f000b1a00903001841406101c05d40085d0b1002680c0b044604c1c1e0782c0f40e950f420306007840c1406036807190794402c01001c0c00703020400000c951140983e0a00040e030b01d410502200542d60940c0080d215600f001c0b0a105400b810a81540240e403c0800f614002c5401d00d45009045003140c10401000d00e14500000c0c2c0940e03080d02441041d070b5242c0003504111562801d8000a416801001e0340a40480814400116240c1c804c1c1c0c100c030007408004204200c4600e492218610707680003160340304d02507498140031482c0c560000600b05a5403003030345031014240801080494041500500058114200340404000203200b4041c21015003440c07808051000c46202910408500b4004a03401800b004c000502180d00c03060320030200240c212031210754980322409440d0603034000e86600c0101d00102c0c4008104698010350880c000c003010340c2143d034185e459404040c0c48019030711000f0820101008110704080c80c5400210f00c5a6251040c160320002d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 46005813 1250 46004563 46004593
    0x405061603021b032101050306040f080d06260604020d02040b01090e0c030403020105070503040804030b04020d0209040c03020405060312040e090708030c0c03010c140304260c1c02060709060c0203 86
    0x18554030f18900c182c001054021845001d21800890b00300c84001003c015407411020075264030000d0320103070040c48042e8884080c800501c08407400e41e90048810231900d0768030400402c02c409094240801507402034107801e140040000e05038001c0f900203100c003662001a5080000400c29588010305014032180009505110b004480c3d00c42c0d0b8410007200e64070311700f80c603000b42103410080848083c030000f80180004101240d050310140e0b54400703030000d1a62924000501500d4001b00001d620208000800c400c100440448500304c0c0e109031418400d50702d50400b00b41d201c200c11a0a008a40d0040c08208140382503541d030709401030282410f8500305034503640c00b03c0c01c40d4002e00002c0820740c000c001010b5203050034800e888000c0e0181c0b800d100490284504c1c000540f002030710207001c0799203082580d008603040b84564940034003c026415910b89220016035101d000206110310046603e88180e90b100d8000b248045c410925995800c00c5142030a0041d284d5903203641c02aa0148615038080403680 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 46007063 1250 46005813 46005847
    0x43305040c020c0310060663060518040b0d1a0610050f0a020f010204080d140c06060105031503010203070e0306070f02030313020f0402070f0c0806040506160302 71
    0x1001580501403003c020020f05103030a402c42501c41d1711900d095420000130341d0001038250346010100707410f02083c1c82c0040030102540141322582140c3c6484000025900b460b4041007100254215251403048540a205a500003107118603030108904000000003078031407010421201000603c00603013080070380c0203d07050a400c450212801441500c24003441720b00c1d000100c1d44a402103440d01c000100180000348280a5801d403172060b45000300e44640c555000b40304512a4a916400031521691303a0032486550b840203080840c0440c40c0d044500c03023030b111418200c0e01038100e000e0092100c0d84951004540c1e0381c1c0014003244101903a00d400c00420f507030a00080d4041d00c0255200c0b2003482e403a00806040c0140a4907071001d100c3c4581008543c1900071003a01c0d4000c0d48000200100c1c1c20074000300e20064008001a90700610015400c000c11500740054112a405521040002611030140a65403c4143d07000760890b0b101c14005141100401559824aa214600503003002c04801a4450762 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 46008313 1250 46007063 46007081
    0x9030203150135030a0824360705040f06020118141011030703050c03060a15020a06090605091c05031f0506120105030609010c0c080919060801090b04330504 69
    0x20103480c20700c080c0e03401c48800d00400c4c850349485400a419481e00042ca208c0501c03003c0c0d00c1e0b001d0b05070188120080485030100c1d200402c0c1c51502800d00c1c0c0140000d0159005004500300c032405008080b1b081403051083c0190704d2a200c0080f00009805d171a082c028404107100c0f107030940f04141090280c0c141901503601d00d118454440740e01c0c0d08218501800b5a04000e000d481025003d104002551340d41c445544111584403820303143e85034414900301c0c10803507160790180c6420f0804000740100075081d884541720fa0510802d881f590ba240300444d8800b20503290000000071401e001246d1503900c00541e403000a1005e5820003003c40e601e40104d0300d01c1e00420042d0081184e40c2d0010000d50401340100c50380401902c1c0200110f410214001c0d001088440d0042c0081d803003c250f4001c540c81c0d40c440b10000b0310301e140101400c217035680c100415080382406113040d6a03040035030900d05401c0602542c07402100d4204400c90380b030b94010100340b400032442c18918803141502d00020b00768031203101c2c882c59 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 46009563 1250 46008313 46008317
    0x7090905010b010e090a15120305070507050a0806040b071209060b090c040f0306020c03070204060e070f0309030f03050402030c091003030e0a0b07030c0804030506010609030203150135030a 83
    0x580000d040150031a4007009032681840142c58400e04655200d1800951002d610000040c241c00c40740020070320507000b030300203003000b88008510905254000014144083c400d004035442c8a45490038400348200300d10448203e80c0c400400301d0001250680150b5101145150600c0302e010129000b0080d10101c080a450319903503804400d2140c01c15403d85907108009400144c42d0616084000c0360b0207010344005002203a011841c07050303404090040325250b40c1c0080041c481d13103807280811000380800307451502c0801c20361004494150f000313008001e000340d0162078203103142c542e011098000e0000104100da041c001c03041d0240302da90381d00e100c40d8054409050120300e03150642c500908424034085d8551710030481050704200e05601401203c950550628003802021040c2c41e00e50150f0085400003807041c007075030002080a95011006108a0303000702c0c21541600f45d980c1315074640c00f5003802007a18a001e0344901c22986c8120b18840552a546914003080040164600c0b03810368200c842c007140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 46010813 1250 46009563 46009571
    0x2b0603050f0d140c01090b010305060609160503070f051309020301050a0501020a0c0618030c0605070605060405040302060402010809030c060a0b04110f25050303130b0108010e2505030709 82
    0x41030040400c151904240080002c251103040440040d0a035807510840000d000303000244802240400c3d040000366940c405941d8800d56101d241c4075442d14012105140141040400690b00e0000000461ba110040c1e0b1201450f40c0c80e40700e0700b16108403220051205100c0e04024006459014505250062008180c016120f504082c10048100c00c103a10042c110f50042040038086840007001d0000c0350818204000100740e400084900e800e4258809004c541a840380090042e4210700202001481801c040003240c0d10441040201c038000e54000d00142d00c0800000c0040d40076866040d0401313119030499007407a84964820f03141040c12201d2010f4070752551103100c0d145c1014083c6008032051041054104911080500c0140c09030010308c4014581003000a440866002040e034005c941200030307031742d0300c0c80c0580010402c00fa203124101e50500b160400003d407010f06114030312190f024840070307204500e03921035282d4604000600404d5003400504000035503550412854000b0b10015001007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 46012063 1250 46010813 46010819
    0x607020705030607090b0301150306080304080601050a0b16030c0212010204140f03010504051209010e04110307140a090909020f0315190203060a0b0a0c080d1e06120201052b06 77
    0x500f803480c06405407003401481c1c00705000040241c03090300c2c1502c4802060549000b40030701d04070701814056202e04c0c254000001c011407040d01c082602416074030180c4d1003110a90303903480303441c96074498003494404699008640c03d000074452540c0311750039400203001c40f00d4941e1172802c09003203900c554404a1200004c1d000a11141000407101038148000c400030132151030301d80c80d90380c1c8459044181d019004800520030003903030701a00d128440d483d0b0190041000c1a0615000003896005480340401702d074004440c2e8150b0f020340c40843d0b0034101d1355662004414500301c241d40150509000490b4450a0720b50b2004154804000303880038030326680828001402d00344400b1750401c1102110300c100074010010404c494407a001900c6c02c0391000c583c6a0355819500204548402e5110402401e0706000540b64040d80ca06820008a202141900c05c80c2c0c0301d070b03920100080360081d00c5001d80454060201c1005580102c01030310380010786501030840da08002d01111f901c0c04030340c15a1150141c0c0c8070414 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 46013313 1250 46012063 46012069
    0x207180c03180b062206060806031b0109210501090b040b1602060c090120010218010203030405060406021b0706020105042d0210021207080c0c060717030402010c050607020705 77
    0x107100b1041505a0001d928001030f219015140002408039024040c0c180406101c0510040c401c10340103101d00d000c02c102c5449400c02040da000540f660382c8a0720500c0c1c60302420501e0f5446054051a05031200403040d07180a88014001020050784249480010808070100d8000e00900032554401c2c01c0c524094030b09031604c03c1070508050075070081c0b034a00400c4540302d60303000280c240e00302a060402c681c0b103d01c2040120f03030841604041d460380b01d0090440240700070054000c2c001400c0d04070766002a0403248801240e03240021038000d0225884507000c540801c1c0203900410a84012010000e441100060000d00c0c0010a522580050795a00104400d200080e84994400003800c2c0d103149810344a102c10082c810034585000e4803400014a10355100c600030090102c0301c0c86071071001030f2201810708007448203412414450302a8000d107103a80010b0301c0c144045484080d070182c816000a500302c1c00c51062a00018000c0b414481204000c0c0c02080e02084110302c40c65240c0d0091003000d00386414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 46014563 1250 46013313 46013321
    0x30e010b0409060b24030a0207020f1003060503120f030604090501060e010303090501090506040e0a2c060412030605010504030303021602130504110405130602280203031609060e060306010207180c03 87
    0x13403403000f848102d2800840c510345c207049a8016042c40405600c440a9000042d80160302503801d540c040c1030409480c40050b0150404012980203d0660309041c03102101808030740310701c0f00c01200c503800420004000b40303096406446030602540001030800c1d2039550049440d0303400e8200360b000c01c229403410007981d80c0c4500814050070003a200c55080a1902c0181c010200c405000d04800381e454107840c00111241c0314103050031644058582e135038001d0340804c068a0340d9098070700b40d441c1c1c0300f10107145440501038054402114410303520a40303010700e161000c40c020340011050f45001c12400c0898000369035000309901075030300170041c00074603401c0c185803c4020082080c0d100b8061802c040401c820010040280c0a941d900044090b80d01c8410109120503040240d900440f542404400064101e5000000d18428000f0700e401340351042e0710103000e440100991044c00c0001c3c0380a8040d01c0b403030034040043c0d034125906004072480e040c5c9441d036805ca05203078010541c041039902d0b0341401c0b4203940350007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 46015813 1250 46014563 46014589
    0x51905060703081b04030210080601210204030b0603060702120708070506011401030e010b101d0405010605120a0b03071512090302030a0201140105090c0903030f03090102030601081e07030e010b0409060b 89
    0x250315217454a142d0100f4200c840c640d0b051428807080d440001d20b981d0052004003c0200d00d00301e0601c201040c445500c000b50802c0c0000e5507440b401000090322030400040d494010040c0350000d00015041c452201000d81c004882282c6280040c409400003034000c00049000e0400c2d403141202d00d00248000404503118102550560b0781803451110558031094044d5040980b0703803425030f0040c00603a0200401c40401c1a400740c11500d440000284030743e100c00900081201504100b0541d21007030149400d0300c44d82001d060b855080300208001e070000d50785028007448828101002200002c2c2e405004951a54400b980980c200185050104d070b420301c194031019030750b83e8440e1065410000801c14903040142081b5100c0000101f86141d0703901081034800792812028400d42d00e140c0760f11418080e41043d198140840c9954000c00da64805110403480626025139440c0e180d9512803800b140038260100d4441215543d074941161103490724014004101e020360000300340c81200d0000e100d60f8a0300c0394 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 46017063 1250 46015813 46015861
    0x201051602062502010603051009060b0a030c0521060403090f060f090b1305090705040f06050c1009060b03030f030f01060305041502070303060e180106061805190506070308 76
    0x41d003000a5000b04410902400340780c0d00c081c200540714200113900416082d040540580308010940046a9030398001501c0d1503c10314041c454214800700f0312000800030301005080341603100c824040e5040c45034801490031000c21401c400701c0c000060503400c0c05010b07201503002a603030690a21100d480204000f0042140349800d00da40325007400d00601105140c0981c1c00403240003d140d000b40350000b04843d01520005012507924107061401a041d07501c0303489101d0322840c0504c400920039000d8010f0300d95541c01c00000d054480d4070240008020600c604085500d199160340050750758030200b0181070920841c04515903203050519010001400c16071108003050300344420003002800c500c4281905114030701d00980c90744141d140c280d01400c016000421800e031502c0070081409504000d01c03c0203640e0100030444640c48040c01c80c2d42506c0c500c3c54000c0104104410800c6d41000c505015000c1d182c0e4114100f41d58640c030005115511500003500015003039030600c03000148a0284001c000408 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 46018313 1250 46017063 46017073
    0x90b09010203240d080304020409080a02071a0301030308070e0d1e140105040302030702060c120a030902041a0a170f0f0607020706020a030f0f05090a06050309150903040b07080706020403030201051602 88
    0x103c800101001e4440b00000c4c40e450300800840c0454845400c0f120700f80b40e01948140e103600300c0703e9001b965805d8070300c510030a070181800d238991b03035013100c200b164140c94041d9610000d9550b10340701900c2d10f101202481d9003000a2010580110b4642000d020b03404050740e4807403600c40d01c0c0e030405003240c4629a184c000c450749083c0074000001d0300002195062503059402e1038407194003030031036401c2251202542003066000294010919030641c8a510001d1003241e040185280701052052041019800035070000007404081c44016003005074181c00d510b5110131100342041c0400d026060200300514080d444d88050f0034450003a80500440014068620080c007a4401c80c1c0c030000c0c104090340791500c09200301c8511202c059441a0100c40007984090b00480e15240c2d107560081441c0c0c001c541041040c003840c40441040404000107502036080c0300020b5081904280000d0304d81d81c04540100c0d00e4003801c10001d0002201e03030010f40000c6000350000112450110004c803410b03855400c0910840d004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 46019563 1250 46018313 46018381
    0x90605030a030e1f090905010b0306030c0f04020408030f0405030f031606020d110c060a1109010504050603070318060b090612100902060c0109150b100c0f06090b09010203 75
    0x5071141c125406141c52118004848040b1300f140c0c3c2c0c0400b10b454507024100c00b5060301c54002c51010200c60607020100aa6a80d8030010750160005035012a456003103040c24080b075140c540801504c1c030390010300051510b41e443d4002c6186a10540c4e98640b403801c0460100400d19060140d080d40050340c070701035450040c0d2103044152084080e03800825580e4007060943c0c030708501d81e0291481001d00201180c0e106089002143e5a40d41210108112810300004403a44089281034a51400301030b120f0600700780c1400c0400440b43c00081802003010360b0f41c0401d2030007403654511741840078055400084c00d48921814043c110100501540c052094504a1001098005101041080580743c0059450700320f1002a81034400d11401500c59130a045080042c4020355041e0441e215070001d00b040b00100380f000f8400c00d0460000d14001041001090b807001c1460300412400b4188107480006a00a0581d5285c1424409a4a1401e26075010041080c00008070100c00c8c0104400d4000e0360709048 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 46020813 1250 46019563 46019569
    0x40c0801050310020f0d020d020c0f0d02031c0f05010b0a0e150d090f05100e070509072021030415090503090f040b0301020c0d0909020a02071a130f0f090605 69
    0xc004203110b0356190b0f0019451210001c2d04081c0c0b4000c00d1b450805642e544280d13010340001e504007991440700c501030824002411080010688401001e036005503082c00030200b040c004030a01c800a510110707440e030704c147c152242c40f0710615000e400400d403003544840180400401041d100b100041c020100c070b0708208107110028058400c0000154000314102c4100d10304450b03041c0001030001d0042c413a1100c000102c1410b6080340313107040100c10459100503039510030030800e0b400566080022404c000001d03034420070318101207ca8411303c01c0440e54100c404141c41c12040c0076801019854200202c240400c10184650b8401450f00702e2006011804040d140c1684034411401420310681e46107001c089a5191504680d00d00711000b0b00071511050250f41d41c0743c443c1e204050031000181d0300d400108030740d0f0380781c4207030368158034182c1c028030586052010010701206070821081c0c560703d0034880300e03000301d48101509010307281c45051882c03200d2520000210710a4507800c040da1080c00c0c04801d102e591 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 46022063 1250 46020813 46020823
    0xf06050307172a13020c0105040602031e0c0a05070f080d09030909051b03071211030906061005030f040c03020409050d0e1e0609041503030c1101030b180c0f0408010605040c08010503 80
    0x500d00701d91400d2448010201c1c1d04c000d1203003a03860a599401d00080005201d0a940558441c0c40c500d40d00c5040c82c0d00000d43c1032114841140e948000d90340902080150600c00e1000d804a90b1041142904c01c408580399580c40c4c0d00003080340d031841c0c0e45890380307001019802040c2c80c000307022804c0c05100b10700b07000a003110041c00d0b22078081004000400090b100502c00c0c0603c848102d07072607000704003031224900140019802116018418402d41c0080b602d6400c0401a100c610b9045950b03940c21034071019070411b034181002d0810ba42d2024500808809a541c0c1e100707201c46103100d0b90041440700b004140180c210b500d01441c05214003001c00031f00003408005004d650b00040c003100c4044da42d144100000d4001e001840c4452040d5138020404410140c002c801450f0f69405801d0000c04240340c0401102656680502542c001d484543c01310007001040c40100c0d080220251003c0c14030981c1c06000c07080e6081a4002c0780c05a4541204001500b0540310741000305425203001d00c007560401c0e000c66900c2d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 46023313 1250 46022063 46022143
    0xc0619090203060a0e031e0408010c0206040b01090906020405150304020111160608090106080703200411190201270308060306100506070503070602030109051e040201020706030f0605030717 83
    0x39921000301202e520401d10841fa641252010001401c490442250380c164005000f448129840c0103040c4108900000740c0c1072195074440da030503595038201848000544500361084400d5a02480701086039580e11540303081a02141691079101d180a0000402ca407404503005681c64002c464001028403503241000203407030080c2498070ac1a1264030241340140140c0c0d11200c01801540030100800c8482e14402c0d5649032852141d620040000d000c0100325100d14108100c0c000342003081c3c192a0f541550700380c6902c0e40300e00000a4500ca8203040c1d203044010040f1040035012080c4140d41059044254107402150a0340108050b1a103160200e001c200d07507001e01441010301064a10422108004031185603034022019912540d503420100042c01d400e40d22018054415545003040740c00c1c1c0704246210f02c0e0164010408140b40c2032050f4020043c50042c0c098043d1903c4012880d030b18204030000081c9040c0c4d10301c50400d01c1492030581801c2d06815010340850341e0801da410007243c0100c120080d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 46024563 1250 46023313 46023331
    0x1b080405100209180f1f05010912020f090406050a0617030412020d12020c01080105100905040203061504030c1e060e060d09051b030d0309020303031b09060c061909020306 75
    0x3854816100140d840e140c84c0070b440c0551044802084500000b01c180c150052400c01c18411140d0024250040044514007602c0d000a40031340d0700304130042c14014034807000c40c000351120540c0380c460008a00002000c84043d584251184180450080d50303102e848028400020805150042444100d441e44500d114030025020111109029581c0740781a4050311a80100716002c1e0041845000e52100245511a4041407006000280300d040c420100130040c681540e030019080e003048104002074001604441c1c0020710031126101444a140040c005180629080340c0e005217811400405403105803c07a580110b1500002c1210681000401407081350072140681c03180003440000e401000d901e50060503a110350009040058148034454040c00303415400d5070003202c801081903081c1d420b100c2000f0f41543c003c000190032181e50b840e0300d415170240d00c4038030f030300c0c11014200141c82500300e0310843c2c0da41d4000d0410300003e1000303000c0d003100c5c003080d0507000d0010314402c8d000240c40789401480085 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 46025813 1250 46024563 46024567
    0x80105062814030411030d0c150509010e0f010603020301050a06030b0411030313030f0c050402040605090108040f020307030c091b0e01030e0c1903021311040302100210020d1b0804051002 82
    0x410640100e85044081a484070b0303a030b4582c901402c042c0382840001495038000c0c01803022444c0350301c0c0304581c0004015004840c4d00800702001e03002c140240070050525030f01d550b03241c140343c8684005224441c0c8480004e400484c9890950041500712035000c2c0207241800d00c1c040c07003000082d035400b507415030054001c06044000c0c405000403a0070b601c1152030016031040a5840407041040c64180200c15a01801c95a0102502c41050100701c1c03142d4000c0102081d010702101c1c41c10362040c482c403039110307203e041c440c10042256408a46807042c281c01c121000000c4c10b0081c86102a20700c6014484031250b00e12803001d0100d00400b800b28200c0c035618034109502c400251447d541d0801540d01d8696014220030340c02001220300020b0b1100c64003049128103409880207006000034010340030500d524168062406155500b002040c040c02401001980246144611000316510160920030000303007000c10b030b4440721415204003410708004001401400d10501002c0f6400092000498090040c016 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 46027063 1250 46025813 46025887
    0x306062206050a0b031602010c02190c1d071d0a050f060c120c0c03030712230c07030c0603020a020d030b030309030703050d2a0209180105070f08010506 67
    0x20302800319900556089240a400000e00d90030410065105400c2c1c060516001050765a04a090b60817680320040180c1c0803c00140041c07894016032540c8922030401c10101031303030f14030400b8440000c0040d200303402c0c10f0190030024510b4020782d0728212000c0344544440c5821200001a90001641c02002e0045132444004a415103600049580d0720301450201c4040c10600b41c01444564801c81038408503011300e9001c00c0f49401c0000c15200016440b951850321b40084110403a2120f01c848080d2124801101c1072205442081c00100001d01240b800740c11510308500f4030780c956501c65844030003094410400d0507a01c030750100c2c0050380083e0501e0007055060810300081d1450040761112540750142c40000000c0080004030882c0c00340c0315880c0c0c9402001355880c03c443c00040c040301d684000d05080034483c018a8280c8035154030241000010303110490a01c45d0350700319402214004081032102610158180e044545076005000c115015071910031072402c50b0003102e81d203c00c007010030000c072083c0e8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 46028313 1250 46027063 46027129
    0x70503060a031e031b080403080304170301061e09030305090d0201050903070b04050405010e01031722030308071701051311070f030801090b0301050c090d0606050603010b07050c030606 81
    0x2004542101103500b400c40200c0e030f5400350410ba4082140802c902000e204501601c88500d198481d4001d1304045c1003a1560315003562a500040084070078004100c0341d0f900c10104000910701a0003250387e0691000c1d61041d140c3d40001030f17201c2d10303c140305600c082040040e0f8000d044840c8071200782c0b90b55800643d50710040e030301405a620030780d5041c051440c0100d20741107841c000e0000c40e50700711001d2200707903600c0e59100300c1c4400030700000e8a1b086010303094403021050400280840326130091808003080e100b00d82406a44195041100040c03e00c2d01407000c09684014002c1300c0c51159508502d03554540000502c2548120891503400f684034070440713502442c0d0a0923075114070341101c04860015080c4c5002400c00c4000d001e0401d038070b0700e801c44502d03107070405200d928030400c680d40d01245095401401c0241c2c0d01c1641c0402c5541c00d03200c0340c002c03a0a85401020314002e0075002c00c4540c603962a4503140c2d04282c4041c24550003540708400b0089207540381001710b8842601303040070b41c031407010b8041c030303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 46029563 1250 46028313 46028329
    0x5011b02041d010204180f060b07120e0405010906051908060115030f1104030c0b030c07060b040b030a030e0103270821010605040608070206100504180b0f0402040c09080607050306 79
    0xa10b090a5202140010740c0342c500c540006011480301700c04001e141d0141c14107004482041c0542982040c0600441e03001400100211141ca1b40504040107800311803c001820389a098008224182e261041040503041200e9201c042050580300b07051114184002d99955003014829442c1d08010100ca40d071415019a0000149007200e00050141e200343d4079030645154002d11003120740c819400400140e001c0010240d03406295020758103850b181180e19018051314200900c2940f1641c0c0342c140c0b254075030f010841c01a4043c0700303031960505005007100240071101101070108482607009210603000513005000c0490b079901c6070169489a01003008039900c124220f0862101450380000490a2038100d0b010304100c40307050784c40281c940e68100c0c04985901040da589001998000018409442c05030413045000b0520385e200007103920a07031103a14100c4029640d40c0301c482d2011003400305600b03141c000c045022031b1034107114002c2d0345815605550703504002c0554081050200c049140355441c141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 46030813 1250 46029563 46029611
    0x906050705150a2304030e030304150c030e0409050c010e030c010801090e07030210020708060a0204151d1003020d151503090609150f0501050301060501050703140909130b0105011b0204 81
    0x5107113810695807010603002c2150a4078190081041c4051803000362400204580513160f403038004540c1c0100004080d10112a4090224107016034408451303510b0f1100d100700d100e418083c1009256280c2548000350080e4090248035000c0d41107050ba4241990704691070310b0446548400016800702c1a0000c64102116901700952004203540d03402841640040c840090301c8019041d201c0b141c44036030103c13003280324902c288001c0130480000c006070a0b028a5901da160503d00301d03868001c45c480d0300024206540c1900501c0400c0d0702242d11900c0402c103200b00d120301604484555111410403030b00f8504072400c125803100300340e00c8046120400c140c030340000b000303164050314030f0310444203804146010f82903624048242c2440c0000010b91407805000b00012034130103844662034094030351400c5842c240c0b0484a9041004208041c088640764a003085105001c0b0703d480340000c1103246042640345a069211328100084186200d02403440741c00c550000d039a0441d4000368910302c0d4103018185c0e91009c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 46032063 1250 46030813 46030841
    0x90607080d140403030506010201060f0b0c01060b04090e10050912030c04081902030105060f091602031201060201020903100c050405100e13020d06060c0807171b07060906050705150a 80
    0x8180d05250100d02c615503400742d03100380c40c184055903400004a0032502c90784501000c000806004010110b1100d00500010140f4000440e0143e00c910200d00c041d4041e901c1640d019a4580030324000e107134280000c00c5c4c0e4030000241800181400c0c0d038a0b507078408030420707410110180000411110310400f42114000c040d60415295101d07004413100801c12039102040c0c2c000c0d42440c001516620304892848040c00f0018000c0c03002e51503481a07060460180c1040005502c020010100408543c6e606903000701444e50025984107500010315080169200e000d030841401c15841903c42a00042680c00f035400c191250350702c41c4012032041707500110840d0726030b4000c802400103040300003840e0010100011044030034005140d46020440d036036400c0c0c00c80580f403c0401c5c40340728005440454080d00c2c1c14010350300c02d802c11f090100c0d000c200380003180b500d09540e80100ca0801c045604204010010025411300d1802d0820780e813680364481840c410103181541045001445200d45580f015500c0003000b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 46033313 1250 46032063 46032071
    0x280f0206091b1f020c040501090509071824090e0601080a0305091305100e091f0e011b03090501050105060322020303040f0b130504020c2a040507020c01120209010203090607080d 78
    0x10000217500c070f84264100074062400c040001c112001940186030151007880001c0031803e241105d0011034000f0f00ea014103502d034550070500c5100018822103c900c0035071501c0c401c0345625180103038080701c0d00120b420303a060700850010001c008000c12901c503401d406081c000e507150320803000070300020100b4030300c880c82601d007600384a03031484104106000e80c0d200310107100403603c9440c2980c0e901c00300e096940f9029900b80081a0510380650071614441c03402000125050480c03503404241311418046800000750340d84044828000240a1640101030070b9605504d941810002101e8070301e441070040c02401d100c00400402c40d2020003c940c010800854003014a0303459604610040e4070004802c0e07010b010180c0c0215052400b842141c01e036000c520010804400400c0010360b203c1e13240100e0000d0104906070b12040d07a200d50042500c12603c0e45c0c0505a100034490024003180d02030044c8079800f51050042c0c10050b40c00000311094503c0c212044c64640d415403400362194070a10420380807103410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 46034563 1250 46033313 46033369
    0x106030b0f04063c0203010f061409091305071406030403050705150c09010315050d14030705010f0903031d060109110403150903080c090a03140102280f0206091b 71
    0x3007100c1c200206502951013803100d103880d076900f00c285e000a000d40b8409072000b200401219004c0c0e000c0324140410249501d00b4240e44000040c100344040390650300b4074800c8440711041002c10b00c01d800161290329401c000d080215004a00d8034040288000c043c44070020f800d00510400f0000803645204002c036541440c58642e00c1d080e02a001800c0140c046810b009040c031214440d1403405050312009002c401980380300340c48500305065140f545070030300d0000708902030100e00203000301121210340c101e0104176805103246c02801c85640e001e429851602d5201a254160008540c60341160741c4100d0208200381603000c176102c14800d5a00084c40d1410085001002c0d45142d0881d081080c00781d1292401a82c035007a40034400e2061802d400e078440c5d400c81050001450600002591049000005090007989044207103455014130b0f10220900d00280c0072000e440e804220080c1a10709440903001d50305010040a5652030507099402c04420b800341e814810303494800914440203c0d940707010102038a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 46035813 1250 46034563 46034621
    0x20406030c05010215060f0d0206070b010906030c050303160b2805070e09010b041a0405040f1e09020109091a06031e130803070c0201031d0f010e0106030b0f0406 71
    0x4994416240940500f0311017161074185e05040520032900505480c400b0300249013003240d030020403081203034841c0c000c0c0010000300307644400040c00392960800000d8901d0460415100040090f4469440382e4000c01030344103100c3c1d854082c00e2225922468880c0320b40c45179144407444801440c040c0c038006004101c0540c007640c039600003d00136541a1901030803210b8002c1406200d981c00d0040c0803020320104401c002107814051980108424111550b041546450014050f285000282c851480c2c6030802d481c040d010b0410040c40ca620042c60070000d01080f81d00281c080d010314824420026501c600601c03600451280340400041c00400035a502e1410460030006200b0906041d4404901c050000340c01c0100c610640007501d81210b0311074115660054111844061113204a04254856000c032201140c448445481030140c01e019100c41d012404801c1d084076400c1d0401c0103607038107152040012807100707400650001c0c17490240311a559030300d00f416006440f4003400619205030742412007022103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 46037063 1250 46035813 46035833
    0x118030c02090a050105060a05030a06050a06020a021002010515130f09120908070303050f130f09060306150f0b031302090f09190c0504180c0303090303140c03070210020a02040603 79
    0x7482110507807070075110344240c2c5044030024000c0c190046020014031022030b014101941c2c1c08a02d03000041001038942c000f2400c162403e500a81c0568410050001140742481c54011034000e6440204441e01d0150707043c1c903d20141e40516030086603109405407040c0e1680e000031031401030030601032005d014140740800d400b0a08507812000900b03100008030700d12a000c103142c021030f0341560340c090500030402c0d508c1c0440e901800650541008100000072103410140200000700300b2100009201c91030b43c2811002d5030700c1c90724010703503003290590144011700071100740c5401d40d01207252183d141d5540031071925400c0c04c1075030040e6001c10f00c003040264201c05131421503c6400c070380082c2c0b000200741c40c800c0310410400c107500501e81c5003010300c1800681080d1b4440c482d42c10841c5440b04d1201415140c003a4000c84940080d030008006d100c0910074160000b40c1030188400203010607292007402b10910b903c0340600b0100901c05c1520344100041244200800c150b8141c00a208102d80c2d03071f503860461350701 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 46038313 1250 46037063 46037087
    0x1051f06030605010c021c0b0103051e0105060a0e07050d0203010f0513020a020a02090c21060108060604080703110d30030b011b02010203041701050105150f1803011803 74
    0x1468011010546078030a0080a08031401030b10703001301c5134a140c1d0800180200e940140c0d01c9401400303000101140c1c0b04803031640214041c0c1d016103462000c1c880e4001c13000400c5034541101da030412080c41b16580b01c0e10020002c4030000c110000554031104000c4070b00780310b10f2400000e058008030011566194550060045a00440d140c08000b405141c03420164080d200018004da0015a50200541000080190b00c0600280d43c140341400c042d03048a400021528103030000011441001569600306d01c009801c000119902410180742c540c0301c3c1e503180c01a010042a00a50781c0070b4100580302d091044500950010f0840d05860038541c8103003080c1070b01d0307026034020790304862101d881c1030191140392a801d506a45145039880201075415420810410072130451104200008450000041100d000c01c48180089140d514190401c45134264030f0401d09017200080103c036007287c642c82c0c1140d04501c00000400c880c039a46900290040c0349032012000c070030348415200c5080507481128a104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 46039563 1250 46038313 46038361
    0x1602031c0605030c0108070c0609110d0302030403140f0d050c011d01020a08150d0209180d0207060f0201050c041203020f0609010204050406120503030601120605030d0e0907021c0f0c050105 83
    0x4d8507040000446202c80c0643e00034001c511040340c01d9021520b00d4103e0030f02180a101d9a102c0c0003a501c01090710707080700d800c0540050b0804a000c0c800c00c0310301410520f041c05441d00400c603960b0020301040c0c0f030f441441c90000a10900255414001000f0b40000501045109201320081140d20405001c1d6001c91921000200c000b000102180c6052005820030740c80600005810003090b8248a14448042d104c51484c4100340a269800102002050058002a4080d007151494400003400d40c4041c50700c0c0b50250790401d000c0042c8407481009031800ca8540300105054400c2c41c2c1810790270103038002e400514600814040081c0ca40b815002027048803001e0310204151640c2d090300e400c000341d80c00002000d0740c008101240b02c5600c1400c08030244517140200180456440300080d203442413109051002ca500e126081d06c10386032074034405030700cc1d0160001d41100c00d00407580c002d5840442425405003c3c41856502441e445142d0001c01958010003c20050500080480400b021800c040d10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 46040813 1250 46039563 46039573
    0x2d060d060315050c0f0a0302040302060301090c090803090306070804030e21121201052101050a060504140402010c03050a05041e030c12030e0402030a230a060503151602031c060503 79
    0xc84018800c9511800c4c8100384182822240360007646564840020b00041503024070001c005a580d000c0103600800b07164000107041681c20002500c21070700c80c0d1100c8000e80060000c4c6655407000b280c1154012498a0055800d03903451a096410880a41c4940c0e0403400328821400341000c00c0c030001c15204401402c80703540c0004082421243e1003010400401c0e00520b600420641c10440800091080031240300000501c088156501b110000c80c3c1da01034854440b50104600e0a180c13080d9480c1c0480310502882a29003500081c0c0010034204001b01000000204916501d1213002501c0c0601444506403d0b250b0390740d65107008100b07080c00142c0305c0315208000014042c41c0c0310a9a548a0f616403119008460724a041000a420041c00c20011503114103030740103401e00341c0c0c54105604644241c400c1c52400e0501ca260119010b03600b20318002d90140f03211849403043d14400360382c4140d0300201c205292010080490031809008090042d02d03250808445113800f0782e1300900c0507900c0070303402c0314 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 46042063 1250 46040813 46040843
    0xc100501080c0a030b060301091a15010507020f10030b10021e07080601090906020706020c0312060a05030a0609080409050f0712020f180301060e190b040b2d060d0603 73
    0x2540701c0300c0324030b80c0301d600101c002400c0001803180700841d540400024000141d40400792900007403807903640010489005640308011030180b260041e80c1d0150000c0c80c1c29402c1401e5540031514081224502901c2003508402102019200b50070030060000c1c0a4445074240e50425006503071503a407040ba10f00030b0312116890442c400070000307415045070452001015640d181140d410010b25896806460240d0200300810100d40280002c0c50040700d0304005542d104501500c42c00c0b0028041d05140c800c0a5490b404c2103e9030340010400300c01500000001041c0c25a40f81c6501103114513030100365014103210400000401481c5070350701c41d0003e516920041034034440f440f0103e105107403012240c0c460501201918100b0104607414080c4003900005086440301000d01c0c4003601107525850640c80b0145804500805005007100d41c501610300b8010000b0754030026484049200300c40d40e1190644080c0d56121171002d49503030700d40502401c0541d555550f08842c5001c3c0c007041c081035951518091f140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 46043169 1106 46042063 46042079
    0x30109030e0301050601021c03020a090906031410050402030a0b090109140c0a0609050a210b0403201903050a0509131a0105030103030905040f0e030c100501 69
    0x10841d581d10070105400e440700207140d10f045400c40c4010b4034800300c151200e148460004e00300561500c00e01c2400b201d21640c6944a42c3c40e250505900109000c0b01400404003260f030041941c4011181c048000c00380c0d4800e0710002c0d0598004000c07030010541e50324440c0e4219840c6070010490764140d4a4034407028015a0f42c06005400030810010f10f403514000303140c0200140d040c00000c0c00c0c90b00c03000520706600c41c03081c02e000341101201695401c11020900000690000041c15071342080d003401080000c1c500c200513413095400408400803032000481400ba440c1221082008510315501164a0b0308500c2d44842481002e0050034426901d0254103803505030a2500021a200c83d0a40510003407401418141031010400041c008641e100344080c0c103803541a64017207118a85211035200405503000092040e02001c40c101c1101100400c01c0006200e0f02142440790380d0b219601 = true := by decide +kernel

theorem cover : BRFrame.Cov 45863313 46043169 := by
  have h0 := BRFrame.cov_init 45863313
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45863313 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 45863313 ≤ n) (h2 : n < 46043169) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
