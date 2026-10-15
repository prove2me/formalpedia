-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5303
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:25:19.753672+00:00
-- url     : https://prove2.me/submissions/2edfb5bf-9fc9-4fab-b9c6-86909f5be32d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 953597122 ≤ n < 953776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 953598372 1250 953597122 953597143
    0x306090b030109030c15110d23011a1b100204030302070806060a090507110111040501020c0603091b0d050d0203120f060d03050d27110d0308060f010516121101060503 73
    0x34080440c2c1160201c4e20044c0403008030030b401c4c47c0c07021895203100000b07030780441804151240c018141e619807100c0c0302c8485000b4054541c4040401c480d10f058119164090b24840581c94540da0190440c0b004151414415008040703545400140900c00c044d4144001b00c007c080b9140103000c14200712001801d46011802200c01c05996103002443d858850003a41c200380d101c0c000200320100115107410250b6209010303803030151103a0902843c1d903050580c1100e00c50036002d4081c021807031115034420286a2219200d0340d018100211079400f007402440100c121000a400541c3d841d03c041e26070000c400c500502899000401e00104000c81d00c030f45014424180c1d040c03401e696a00c6240d01010b00501800f0100b5210b043d034002c120541402042c5411022030040507031a2060444400704180c008101d507000b40041c8802001c5803c508040e0071020f8038410505105044c90620501c40200340700c80300741a00c0c442d0780d15030450002074004400020b52100078009000e194108000f282d510741c00d091 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 953599622 1250 953598372 953598383
    0x100f140105070f0602210106090501050d0e010e070905070801140607060908210f060415090b030703080c100b01022806180308040b090120070515070306090b030109030c 74
    0x50990400c10306418001040703510880840d2501d8034a01c801038506c199841d01c2101014100000c0740d0309005040d1002141c005039a101d180042040440000e1728103641080420b6407540d81104802406100c4003020344141d41c000203c929146074002e001e010107a210441204030320344400c03410b8a5500494080d90740080300414114858a07010b0310503c69a0058210300400042c02030b61610424100e07030003a4141190407030303141c81d46410003044400d1039560882d141081017040040b00080c4d005403002110080507140794030381d41d4660008580c0704561504040e0401540c1d00c038512554460000e88030004c0c8020300880c200c2045030301d0303c0c01d4840705000c10000030007944400c018643d08147d1850f41ea0842c00c201002d09803401820b000e400b980c0446103980c040e00043c154203414070503411042c016080140028100c140e140010317500c20041660f5901404e0800006003400400aa00546199078001103140c40c000c4208200c03611140c945100b80d040c0600140400d03031211f00b086100780c11a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 953600872 1250 953599622 953599627
    0x30e10090303200105070201020a02071d1803040801090305032a0f16060e030406090902031303050c0f07080d0f0314150d05060108010506010314060108070f020c1503100f140105 78
    0x488000380c1006160304503400344d41c2460708201103640c0c190081c02d0000e0154003101c85442c1c0b107500320800b04540105500c1461807110001d41d6400c64000c01001c0a84400203892609031a00314039805c1d10300084080e4041070001050200c034808400d070341c1e8044d4492810b2058150440440d00c0f07003e2081c61070900c50321101042c00f4540d01207002e0015030550348440704000e098400e521440e16500140b20b81000b09a00c00d0002400b18010300803603100d564035400e2003803044110380d0700b03680c04d0b04080358000d07071840f90842541088504000501c09484000300515009400a000400d100d004e0380c0014205030a22a1608140301c4d0151195004202c0240a20064810741c0100306540186280902584070304000042c15103010750249008001c01c2c0d0341440341400d81c80d0501c15492060310403c0c0000c180c04009007400d07200b603804c50081e280520503943c405c05010009107016680c001c5100784404004148521484280b10030030081c981c054138100d00501e0200307800e0401500c0b070120350500000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 953602122 1250 953600872 953600897
    0x90a1506080709090b06030d0e090a060b070c03170a090e1302030d0302180a0b03040b0a020415051b010507080f28050a0b010e031209030a02040612030e10090303 71
    0x1640c0103040500240c50480710402d5032150804094140b0240642d141c031a16004200141008110a0350711045511043c1d4440e0a01003030101400004210359003840d510380000c207003006507000600e00702c5e01521020a25608508001900400200c8820340d142810015035005d15000b5013034008031881d0202c00142941c9088040075101d82880c0001d5160242e507244c2e020341d540541c0506000d0303281069641c0030500c01d80900c076011006005910380c0800074000140020648d8184640c8055072001c0582850781c0e8a403075100f08110f10602c1400310f44c02042900d000e03000c4400c085000d191040080c8402c3c140a100902074200141401500d41c0d10400001c0c04040d00d00c91074200c481c298100034403080550700700c15009103c2a98070b8845a41400f54000d140c2d8410a0505000103000f800b804d1101c1c502c950000042d4010807101ea0140100c1c900c00340035907920f10072100181081d094040c0e13194140d1070020720341da8000c00054403411a0016898100380e005500c502034960506010441508 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 953603372 1250 953602122 953602163
    0x20c1009050f1c050a1a010510140c12130e0c0414121510170a0803060d060b06180108100305070e060301291207080a230601061d010206090a 62
    0xd243c002400c14401d83c0c1c0c1301c004021710003116140001101c5160540b903600c1350308200382c40301040c0c0b41600060000c22000f500e40a01001450140b214400b1900c141901c0d4011201a401185034100b21a00a0008115100100d40d8196000c0d1414403c207141a0030840183c41c10600b0018103030090315840c44800b0a50410030404d1010000c80d182e485051509114440400d032850141c4801c15625001c8881140030010b952403101d540030240d07608590f1908184180c0010700749046d585c554851001c80216104d4400500c0c0c12140c0341903c05610300d031400050501d8002034002c1e034541e03070317440410804141c0200d00042503c0001d0151840f03031700c039440082c0c0544070191245074044d03884c16a1301c019420749030340c02441c0002501c001d08445a540326182c0c031080d0512460007240c10864440d000903518036075106400081500402e002140c0c81c0030245400c1c800d8102c00041585054884101c88908031070107030707800702440100980d00d0220281d0f5264001402c00620751104100c00044030384 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 953604622 1250 953603372 953603419
    0x51b0f1e0409050f06011409100e1903050c0306070f020607030b0429040f0204030c15170c031b03010302010f0c020f040924050121080910020c1009050f 67
    0x108408041c0f10900b07008a4048007404c0c16540345000c160081002c11030302d80454107566482200601e940b0115002c00402d07100b0043c18680c413507000d1110310340b10303100c1c0c40070581e4031000d5400f8100904a018405017458500800a82013501303109540340c40044041d0300046442d804400380c43c01240c20141440898040c0c100c1c94940106940081c440f10460302c09030401424959040f2428010f141e050601141240f04500015101e55440007040c0040020108540006016494403100742d04500881c40d0080341d0560710261000400000c0c0203c1180d00800d1001a81a0880c118a1035245a0002c0c182c100071107203440c144503100d06070b1015942d4201c0f022000740000b0f0710a214102c110319100f41208500412040c109604080d81102000b041c881e030b506860900c850080c103032100e0307048015182e020311400c60b138044007000381c04802d440b8080e50903000c1a181d001130441c0045c05041100c0c299081c00390608000000310208030580d16540404480f140641d400000d00e92180e480c2040c11 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 953605872 1250 953604622 953604629
    0x21070503060108060a2c0c1305150d15230f0705040e19020f090108100e04171603051b011416031823070b0f03060d0510051b0f1e04 58
    0xd041036640d80345000007c03034026010780007115a680d514404d0803004044901c03d9404094440c805500c038945824848000c0401070b02444101d036440c03544c0440c001c140c407500300c62070f030b40401c2c90310150028840e00100c994102103943d110b29001d1604600040060084d44120b44107100c01001040c0c1c48080f441c900c00e0f231804560019581c0d40a1001a04d80942c02801011f0001c3c601c2c40c001114102c1c4d18141d042034520450012100d03072100d449114003010030004082914200300f040100700c50400030b194094078400d880e416258503010743e56041071121940c100341aa4104140140c9188000b00b81c20703404001c0c01003000c1982d025800842c001c01030350783d81001110301200003105100c4070305207904140b107841036410010400c01e088141c0b1141d05100b552240710f014409503c22001c0315014662081001d003039400450242d44686107481c003401004500580c1d00e070140420302518441d0380640b41c5160506515017442c031800351020b0720803015161902102c1030102d0708071070400021a03005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 953607122 1250 953605872 953605931
    0x9030601060e01021902030705061c140103060509010c02120a0504030606291312080c0114090c010e01170c0405060d0c0215011d0402010e21070503060108060a 70
    0x40e684903000648071030700700342c0c00a02501c141070a4260b01d0b2111603540384c0c204d40c0900502082e80c500400c1c0212504420043c50102e901900d000652520910440e0b0494119240c0c16441d945941001d008540c0c014100c1c401d00d90420080c2052a40c000610380e02001802e841c1d1a568103481400310f91501641d04001d0400b8249800040d800c02d0700d0781c04801c0281000c10743e0b5030342900c0e0003803074040344180d6014000405000801304041000c0803400b107021802802154588142000304600f11403800117140c01d0072800105004c55080d0410100c81000342c28200b40c02c4a0415100103050200e901440502c60104840040c5010750b05009030b41c01007502502c540d854100c506450030290007010f84900040c402d400f0640554600100031604030743c03000c5501098840c030b000111007800002001030b070501014003680d59203501c400310550511004001d600c55211510840a41400240c3c1d0215100740d10401c014800c680002c80c1c0b1580013140c040c00055081c140320b5800c5010390105054085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 953608372 1250 953607122 953607133
    0x60506360a09061829030307080d0c030b060f0904021312050604030809070b0a1b171c110a05071e0c06230901110a0b0a0207030f0f230903 61
    0x60400c2c19030014000da80f0034080f02c0f4000034440e403220007140c80480c0741084509240001d03010700d080703800d90700008030b201400366841c1c01c1054844041640c00860b003140b150b582d800c0e01d0a00503506119025142714201d850518044172101d848600c0c0c002c01c40607502c00d550018440c40c500f004500d0500041035080116000d9889a0910b2038550700d0440e000c1d000704074442c1c0000c1103207030b000c100300b810f50301809446810609080740480b154103e244220301003c04041221000c920300600c804501600440051f41d05e00456600000312408038500848440c200f03200c40301403030751410560b030015409203042d60300d62000d820584290348800000310255081e03090b40005116031101e204060751801d807200f204c4003044801400c030046014180c0301e440d18003030060b22250340c03158400d0314030300c001c00c3c04880c0035003901d40300e116091000303032440c224603980000c2840426801003a40c0000c0212420910180b03007107400d015105040d180b42c0e59001078500030384245440140e80540740c0c0c0700c1d00070f02110f1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 953609622 1250 953608372 953608379
    0x30609030c030f0e010207031118091e011103010b090303040f03150e19060203090304091d0105070912060b12060405010b01111609020d0b12010906060506360a 70
    0x9160007003081c8140c0c00583e006030500d070343c1e0340580314030b20300781d034040e4000e1013010f241d034940900ca40081e00e5031503030003003420905450b0315110b11491402003030020090003543d11080d4105070030280d0283c5041250b41050b50f03220030100240c080d2811103800d044485c0d500c440010020b411840f840d00140c0c01c0310708400001c401e01001c51641c8202e041d00001c100705201c801082140d581800340700642c000020fa413035810000b00d0316005103800461041c01c1b01c3c1000d071186108025507503001060111078280b085486807407407090040503080071007800c00600d518140712682c1034030a081c0901804a68031426200081c0d250700c80900e40c20140d030000c0d90307520f00301441c1550203060148082400070b00b988056240354000850480c9441840c0c20230f81075414540f99500d8040d400c60102e4003665503070303000c40304201d844500010181401c01000003d00c0c01003072500104650054002c4c9006050a02c0301d9000300715125924110302d03640c40c0c0280b0700d581e0807890616983c0c0e04a28400d401211206000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 953610872 1250 953609622 953609627
    0x90301060509070e0a0e151018120c0e0c03182d0c0306060303070b060d021206070305070318060b0a0306060f08070b0901020d1103070b10050102010b0a0b19030603060903 75
    0x10b85048003183d0140074199200c6040342c00382015110048152031f40c5c8030b81c0130a4039045000394a81c4e400342c1031180c80d014658a8910340e60740242e03c4000d49404524142d410088000e040d0b4000d03281442d40c0e41d5003401d01c08000d401034080140352454040390600c040b8080710b000c200000191700450102c42040203c02020044170180c0d02c004840c070f10890401400918020403414031803440036004500f026696121030808145c060845508140d8228460000d0f8448800c0031318081002c900a0119060801008049840051a403010540742010051421205010074514107420500202e4030740d0340780303000503814150355100424861a0020018280030210862011102a40d06039038003a41e503000c82045a104200005005130001c840c5002d000d03028000f02e20020500c0b100f10381c18007400d030340c0da20445038058604001e11000c650301040781e0369090069030b000c0d480a60f0100c00243c41c0100c80300090040c14035205c0350707034076003840200014403d920070b100464009805111424003030401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 953612122 1250 953610872 953610887
    0xc0f03030f020d020c0103180209042f060304080c100e0715050906090405090f0303070302071112060103060b030a020d0c0905100b071203110307030501050306010f1a09030106050907 80
    0x84010032003030030394001d03040d00124040140a0440e00600906400900110010015251038000110261211001580703480341464480da01c00c8050f00811032a40740303928883e681c0e85900d02445078028a0521700d9448040907a501b06510400803a01c4900ca04e081074201040c244a41e00d20030b140000240d8030780070024016007200c101d04460080310032918070440d401d1203182c4109400036010441c1e60218100344d80001d60110708003041e1007020703448d070800d503065a10513640000003c0d008107459051101f101381c14240000c1c1200c5140d02198209e030000d445040510000d02035590312001d5a020352000e01c14040007550061150801c1c1e074182c60101d84419150144144d8030345490002114004000c94440076507000d188640d00302841c55903403a22001203517024004258413000c2c481500724642d4003a5000d4000780d200412a0b6040c5170901d450660140e10040240390203010070002c21b4400310b012280d2289102569598461030404240540015030110b50048640d40c10800c40513840b010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 953613372 1250 953612122 953612129
    0x2070b16080106020309060415090302030d1d042c0c0d0b160804020a0905040821070311032a0f0f0c010501050618041a0303040602030c010e010204062a0c0f 69
    0x503180e00d0390343c0b02c210880e56801140381c8150003c0c001c1006024046900854801022107840c003ca0340686136408607013007908240c442c2c40450341e00d4114107000180031584000064040e50100240102e0300c0d8028442c1911407000c2c4520b400d00410700c89203041c140010f0000440140030034081507407501d030820000c0000c81e040f8505001412a240200d40319001c05070145800806840d900b80c24403007080d00400020740101c9040c00100840c1c5140300349820500361030002c0352a272003020b00d80100050240c07049580b030360019240800030407200c0307400000301c19124030480004c5500f240760003060000c0d521a060381111440000f0800858074072040d001000907800d0000244a03e9a1b18028072140b030017801e20915540031403001003856414240e0065500b410840c094881e42c1800350003007820342d4065040440160000590103812520074003034801c150116400852420745000030041518102d01c07040700650600f0741c1c00c0d9440c5100c07558141e940903007000b5070750209640c481c07443e1441c255610 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 953614622 1250 953613372 953613377
    0xc0c080c01140c0c060a0e07031b050411090f090103150f020d05040c15020f2a1801081603050a060b03150906161707030b220906200d05040602070b16 66
    0x7000651058441c0610000c507601f010003403581a0035507903152113003a4011848414904403080000c1c8564990041c29200014414400c3e669441c913001e02c0044030301e0902e810f001d40c003604010030014010244030700702c120300b88100099500d18083d451001e4800e043c12040c20701c1c20401070005120741c408100c1c0032200518403007a8a9040c3d000709980350043c000c6500040e81203118115240c64500303894000380404402c824180360b241c000010000710701c20b440300181140707950060007149800c200104044041401408580340386030b079169941e81907440020000e5440e03e1803201140c0302081408102d441c40c1e00041c010f49480703882907503100c0e0b040386c4103103094800b030302c496081314098818880c402000d00710741700d89a520001c040c0e0252620750042600185024480c00c07100504414056581130346407000315003142542000c3c1c050b1048803146022072080380400400285040080322186c840341c480104042d655421f11400030300030508007600880360b000812070800078869410304104820f8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 953615872 1250 953614622 953614633
    0x1121e091a060913020112180c080c010201021806070c03020d050a0b060f18151005030a0b010e0303030118110d050717010f0b0702150408031c0c0c080c01140c0c 71
    0x940400024840680e030850300300301404c01074000755104512060024200c0382e804034405521803100c03203490318141029101c0204c1c40c2c00900c40400180100c041e00d00c0c0c240300a600740400d46004084a80401e10450f109010026000080104a0a50b000210b40040085620300801c2c2040fa4840784030300b0085820b25502070000c1c1d628904041c1e9070500d001301402010042280c40b90900200030040d02c40b150b80c520400d8401034035580e195009002010313a07a40c003a2a414015051410b441210403c81c0c1400364910000c03c1944000003074030304440c42c8020025804003800e013008020111640054110740c400920010301400c940c219900504150f40c81541c1c1c3c0032001c0c41c0400303942c828020f071002030002001c05c00c10310907408080c0242c54002010051251980700b80b084a507403143d8414040764001043d610f1000340e440000441c0510b8610090250a040701c0005140860846000340510400f103083d5002c10300950001000c140340440c0c0500d01d0030950300d0444180c0102a011811f80b00c1c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 953617122 1250 953615872 953615881
    0xc08010221131a0405070305100605031608060705030c04090c0c150b0901090c05120103050c010f05070c060c1401060f1a040f0b0a1106042f01121e091a 67
    0x100762400400940081070043c2030301c060803108121403000350094419210b11070000c07011403024841d00510f1108220001042c4d46403006150800d0341e40c4002c2d6803211052041004001d0000c244994040b4003480c01c1070743d0f03640740e00e40350156000316004180054901107200406075044810a8400d85c010900c6d040c4445000b130403142a1046180c005400c01c0b250b1004001c104d00c41d4000f00e2561010b0700f031240c10009000541a00200309034010382d0140d000c0314044020b03580125902a40354000d00d040c91030540c0301d440300600d40ba00c510a40307042090080c044001d00108540d007c1402c68480000e000c0b4a503940d004203103003403290007a5480e007052a64a0f50980c0307001000c0307404980003040100c48203490300740c01c03103560341141031450140181d0a0744180702560500003035224520400484c0d01014840042e80207181643c96680c0e400d028030107140c1c035103a801044483d01007680500c045a240c849642d0700c030301050385036016030745242040c21507800c0119070a415804450011003ca950f50746 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 953618372 1250 953617122 953617141
    0xe041a060d06020c100509010b1005030408070f020a09020703020f0d020304030f0803060a03020909030d0c2f010f141504020a080a0207170708090109080f03090d0c08010221 76
    0x816030318664001c1c80038408100081854010f086004420400d170303503040c9031485440c000e6070350845035001142d548000403401d501d850082d0783e01502e298681507042d440c0030307a64001c46d40300d841030240c08208202070030800c541d03421102070090102460159100d202c1840d0180d40c400c0018484003041c020202243c041c1807001041c1c80c1220303040f54146240783e40c90f441c0c414895002504841e000740a00e800400540c540c1f00042d801044400015642c804044445108407914200241d0400241e0540c4d2941a4038a525a1400e8000f81000c20f14a04c505412513005083c500310100c4494245440303081e4460f01012a944500070101c0300d0030b08880e0308001c0000300e11520088a0100302e151001c00d540f5038040e03014006030b0b0f100d034a8a10115030ba4107038a5603d500b00c0390007201c0414000440b010b0030b503400305030a40100480d030000c10880320064030380ea4a9024007543c190042d41039854800078001e903555448002d080b000021556000020b00c6101c00380c241003400705041c640d503400f0500380361 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 953619622 1250 953618372 953618423
    0x718090b0c190e1201020c03070c0911030609131b14103f060314070f0909060605090f24090402150d0c0503100e04111c0506010e04 58
    0x82c01e6946021034030109010030350b034200e8252520354010300550281052084244000e148403e040402952185020700c0d191000b01e0303417900101c074040d01f007200c009503038124401034a030070030411110035043e580c890400311450521100c018200102c01da0802983c103201101450590b000400f142d002460840300307200c02c01a08441e01000200300c070590302c401c40324070060303107040040c2c005442c2e18910500032a2012907500603440c40c2a0360352244200200103412141c420341f408124090210701c0c2c03619410440c003002500c05d2184a84d265080b100400440e035002c0e00141c000180300001c0c03410031001c41000c13043d003281e0325105118403c031204240d000c8040a51b0118000401604240c2e50759810d011076902907201059403810280b0980442041c030b4000c56400710916540c1c01d40300e28015410100a6141d40d120100840491061101040342001940b109081c19101c80203100d900480814035100c2406006d8168015080045032840000d804c0c140120700495425241064041000084a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 953620872 1250 953619622 953619637
    0x1020c030d1d0d02070f1d0103060b010512151c0f02100519121a090c0c0a14010504060b100f0c0302033106030501050d060e0718090b0c 60
    0x15442440100d4901016030040b01d0455000b070680382c40c64440c0155240360102c4802c0400140e04030710b8042c807180c820702441d10700600c40704000346a1400c0020224205101c180005000c5640740c10502070f069020f0404c88034400008640c5905c80c0c9007201005111101a1502c40d05c505400c52211090300f805410004415420000b52008400c4603420000b140032005103c1e000d001090020f512102c085400365119440a600d60b40580c411801c090000c54044880ca4119031458001a46154841000c2c6550008105040036642c1380ea01d01c5a034900a02d444009103998030050000c9001031064000034090b61064a0501106900b04200140030689800c00c0001844001d2854001e0740f00d00040c0421a0103070044c1c4e0701d00441003584d55540c014441103d040705610040c242c82c400e4044020300d009003864a0100320300c2d4140400a2102c070103140c0094855912405c07940785c0080301340800401803420621154800344201031680c00b404500360b0a803003041c01c00d80010101c03c184c0c8100c0341341 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 953622122 1250 953620872 953620897
    0xa1b030911042306010e0d0b09060609150409060207080307051b0712080d062402150601081b0f12160305010305060c130b120f0a06140103020711130b01030e0102 71
    0x180b03c41481c2c642e590102c01058281080034202c14100d007526803402e142d01603405001141040c0c58001d0b015403904001070007160007418070000300701c00700714021800000418101e40103d00c00100c7d09220340a4014100e01170000400001032100543d0008000d1010066011445401807000428541c480c402840762130720b02071025070705000080c41c0800030590040b04150004000b40c840c0001880e44803603015040040041280805000c2d40400000b11010f0440d002d2400d146461030000308004800351034a01641d100f0404001240342440036a04440f808200364bd455002d0b20301e0200240009881c0e600803070103140d001d29601c0e8801e01a1505036500400207000079110703c41c1100702640708000c1800380f03440c4500b0108451700c60f0001400480340d0300b000c0005506201d00049010000074080802c0d0f2407a1200801c04002c51108034090303044242801625090641094810b1007181b4942503409103001c0703d0b80440c50003d500401520b242a40c0400c42d00341002c000600b01e10601e240c1080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 953623372 1250 953622122 953622161
    0x603020109060e040e070f05040e0604050d0c050f030c060109060e15060306030a02040f020a0216360c02010906051303050f0c2a090601050a05120a1b03091104 70
    0x581c0c3c0900c2094007403040103000003400c006441481d0381001c490341c004417103889003544c00b004946041d0007607000c0c6511a0f009400c1ca4205582e03840d60b5512a10100c1090000c0000d0401c02d0103818030903015594161001c0e280c2e02c0c808104040e40701c0000340106505149001404240000300c100e6081c450400308003241505005013040040e950001001958144617810f03154006884a00482c4140091094056100c200d1400060b06002c010b00040880341c21440007004220701c44444680c040c0030054511008218002c180e804e54803945100d0120103003091f66007001d9135030540c00380308420b01815042000f9182c0700d83c00c21383c074820558080e000400510150185028207001842c81c00d081c0801c07940c8039120800a0180d9502c401242d402d158903104c510412418803000c42c0e94040024a00145441c0035180050864017947e02081886817000c00090860380c2540d000d00507030703404011818075002c2c00b803000030050701c40c280e02143d0200700d00741040000d0401b40150141d070020505185d8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 953624622 1250 953623372 953623379
    0x170406020d111009050606180f0a230712060f050d02130f1d12120708040302072105100b0d03261e060f090601031107060c1701090603020109 62
    0x542030b1141c040521003030b0241810466a0000c580b01d401c80152052002c1c00c1a03160440400400c1000260254040800344040081e2210420240d9a010508003170000300c40d00845000c4002429100340b1031803007441078003440509500a8100d856040c3c01040a004083d191440c0c104d04203114441c0507040b515450442006140000005900c0c40c0c10b160001545031100d0704000550b40300711400c000b51002c0c40509901d031039051140500b22107092815525000020049404a030801040b0720204594400490308151081c0614001881910b00b030030b0191f0200c042202c04070044070741c01c6405200356114400d0540c0d040c060f42c641c003440140060316682030750710152061040d258118103509510031408203040c00050080d4001c9001000c840c1c1101d041c42d2142c031030343d0006000940300c0c1803900050b5406648d60f1000540c800c0d801e280104581c807050718440458059060018403a034100a40c200e10650701c454aa101030001e5241c20807140d030f841c5500d030219001800301030b00042c1c0404060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 953625872 1250 953624622 953624627
    0x10c0f0905060a11152403030a030f0b102f03030a09050f01060b040906090510050f01140f031f08074b050411030a2a020a170406020d 59
    0x140100f030100c0c01c2031101e00040360443c40c1030524909841c400062083d0600c40311291100d4100c8650038841d24085030000d0700c0c000607959001c0c0495160416442d424050700c440c1e49a001560110710141c5624200900e0b03443c0a00814038040b02458509485c190b14200040080d850340c504e118003201540c1b840d1100345001001d82000e080680b00c074410fa800e0049448000d01c1250018006030480544440c01c05002a007a00d0550307000403180e0b8104402c0c007072140107000e010307003c8400868410341c020740300c0d800507680c00000e0382c100750642c00c020404d4140180031400a40c071540b01e001c1c2042640704000080c01c01000b03203029030031240e03000c0e460900480d00b210000c240d5110012103290303082080d0340d80c4132100c10715003500300504410001844540d055046002401f40000f2201888155078000110145000080448103800d032159410744208043d11000141c064607203900e40c8240e22800e001075915104000d081f95841000a10707601100d001c282950184c41076940070f0105c0c141220401c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 953627122 1250 953625872 953625877
    0x20f03060904080c060408030406111c0b190f0302100206011a1e0f0a09051522091d0c1005070b07110d02010e0f0a030c0b1306051008010c0f090506 65
    0x1c50703c00f039041060080780d01c82002910701c0742d07219800040c0d99240503e0302d50143e072503810801281d03030010b1101d503c8e4080710240e0860f01c442d603500006036421803900041e010100c1c14140c45080c0c0490100400c040d556064900241d9000b5a910100030303032000012603035900d0900c20714007010070b603000a8078603001d0100100b001c451400e00c446403602841001003000da0148948444d81800050380011a0f07810030084001010204c4d508818102c501d040d1040501c2486003981d0f00d01101444064007140420800000c0d1440c460300700112405158102590300d500080100107106850485940e071802c081e010001144603030311241442520342c1c1d11903a440c0301814810602480121280c0c2c0d9050400c00411200348540c00807841c15805000d5a0170407034000d91210b6903400c0318010b500481d41000d0204501544200d400c146540c80710300c14614000c403900c000f03000300c1c1400180800541100348443c00d0301c03454402000340c0c6140301c5017600c00c0f82d1100f0b00c603004038000000820407803404901 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 953628372 1250 953627122 953627131
    0xe030c060906091306050612240102030f1312050102090a08010207020604050f030a02030f0d2a0308180a03091505090904030809010f06081c0206010f1a09061606050a020f030609 78
    0x40109610740c903a00000d06940023440e585c40158203c400700400e81c00039007000704001180720800c0350000701850000351a4880c0e00c1d0700c62a0240c001440700240c02030030b11290010020304041540c1c4500c5490700368080d501503804540b180d0101d4401040303440040c400c8801340c80e4021700403481e103440c00c0d0038052002d802d807242d554940502c2c03076440d01688061004080003404c0402502480c400c064000e0f0003034406031b010400049881da81d410380201507001d001d44581c5c150a001724240d88104c81000014607081c4c04042c1ca02030403960204042d0801000c0301a00c1041c0c40044502907444002c40b003074044c2030a580d60090302c50002c6030100703000b10700c0f8070741100540c80049136880c02c0d41f5050301500d01d40da01030b085540c0102002d200044680c40c4a5070707541014400742116514100303411014100c40e024246100988941074011010480c0841f1407252018010b6910b5965940e1b1000c07046040c1c480980300203050100080c2208400c0c0b0817110700d612a6075407141940c44060600902040080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 953629622 1250 953628372 953628409
    0x60f031214040303120b1e040f062303011b050301030c1403031e04090204030506010f150225050901180e03040b0f070f050604120e060304330c0e030c06090609 70
    0x550300000c42c1c80d200b60401101d060450045904a07c3c5418041180c40d0009104010b6240c54014401403954641742450070303e900081ca94001e40f010002801000c5000e0b060b0342d00442101c4203aa23003900140514101c0c0d0040c440c41e2115039890841000900d4502e0201c0d038183c008014880b81e103503044100c1c20501460400d007504094a41d080d4000f00d9005d034100f0345d225804a00100070f072240b40e4000c00003806188010083c10500d21034082c3d40c038441c2145c60340b102d03080111441083c458068285004103070040509009581d252403a03914004000311004440d410098034814860f0008204d90444000084182c6030251515045072a03821080048070000301c0395250070041601005550f0155004984410000491003400707020100c102e1000350203a0414030800010869103c1c90a41c000e041404107500c40452800d82c0046140249814000c28540008104419400807000000c080203070100c5e100c00f2905020441140165422244d005404010801841c140940801398500001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 953630872 1250 953629622 953629631
    0xc0524070c0509070306080c18060603090c060711040b0a0b1b010204090204090209091f05010e0f030a0308061504030b2701360c030b19060f03121404030312 69
    0xa00000f42045400c3d10741c140042c0d00c8401c180b251600038403c41e40359000444d00d9042044981c0c160101031000102494030030700002c8006030302050700b4003001d01c100c0c1d4010296613170b03007078149031196210320489005c03402a442c1250b18401c034203103843c882d41510700c01301d002030400414a442038680b2440001494055401f170000040501c401c0c006003010304a1000b0240c3c80f0070443c424024054001491064554855941d00d403080e031480049400b514800c0c82c205603105c510b540480d540300076112200b50175104040006042c580c2c03101d801409100d04030b905001102d007040b140c4006000740d00024201e1050803001c02d009000807605034902c601d01d611141180146e5640300c80c2180c008190003020f56002440041d0203660328502c04000304411860f009110101d40c40706600589140001080501483c02180c840041c10101d0b800c0c4210803c41840003d03100d20780c07202100c000c1c1c40110f4041448601450656004a0088814070030481c80c00741003d185880031a500d000315132004030b00c160344 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 953632122 1250 953630872 953630879
    0xf0402090a0302090a020711240a0509091302040e0a0305030a1503020a14010f030207112e0201060801050603300706020a030221091203040c210c0524070c 68
    0x81c42c85185c4141da56150043e20b9194a08005004052002074544247c81c0c140034284481035290301d44014041c0c0c1440c0580381c0c1c415110a4500384038204040d54492500700c00c100c480c10b545100000918800c0d0b03000d00a01200408050b514070143d070004002c540140700040000c0c0855111317107200d110102c1c0c201c035282e0b03503500400c100030707036030b8011105140b0420808801940c100303000910b2218107280c218500680c03038072050254600b02c503000744101c9000484100407000998035840740c0c0c14010f0328800c01c00340c1e0381020340240807a104100146d42070000140f4545000700300390f02440041500001c0b44080400c4812018545200310740074140c1c20b01c210b8000c0350707030351014150340d982c1c0340c500503a55030420700b1005840d21002040d168070110b84081144180707000c140d00700c100c00210141030700e9032190718002d1813804964000c4900a003c24070744081981c074036040c141c05a40503184a440131070b100c0050185c03070454140d40d124410071407101d0103195114440100b05d0309000700b5a5403155a00e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 953633372 1250 953632122 953632129
    0x20120040911070f0803010305010c0f0917010f02220512060c0a020312010e01030b0906010303090b09010509060f220501090312021005010806011d060a030813030c06030f0c0c020f0402090a0302 85
    0x7800784c251512100800180200102445150202c080606011880c806000e0b0020500d0002d40908140c1c02c150790b085608042094018824202034540c0940d203c40d03a81020345004c680100c40ca8002c423942c603800040768208840310705040000c0f40041d01c802e42d40c1070880b4000b60f01140c050400c52108118003681b001b0013003c100c1c040e0400c4001c50809514600781042864030103060400690410001000020b40009010b000c03a11281800727506c0704034010040e02c0ca03014000042d500314070000781d078000c6800d1a2000704080c44140760070707230012016907904090170a880d0044a010030700c0618140041841d411030381d48040307050700c1151401c00310160440151282a0322041903030344100018805c14040910048820b4414985440d0318541480021342d40805844050001c2c50b00040003030001c0e04e10036680b0083d5030030040001081e540d03410000c00038040941070040b046c0c80c0c6110703900c2d10745c810800d03065130b103030000d040c2c0104460900c2080000e40c8544070681d0321108000300000140c9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 953634622 1250 953633372 953633393
    0x20f040507021510240801030308060a03051b120a0530070605090105070302090d0206070c0806070503070f0c03080a0f020903070801050a150b04030305030a1e0c02012004091107 78
    0x100000c4c0742c151440c0c40c040480382d441040115544c075031948041c000c140142c4c0a110181141d4051405410984820001c640c115a880c2c0010b0002e01500010fa854805c0301031141600310f0342680c0d15800b246840c2c0c4085c0e210b0700c440ca40141550007a211a20100720748411414455066070041d07410b000c655940005d05034402c1d00c044171450348450812a40c2c80303081c440c4030f50205031414190b02e0311014000081c2c1c0c044010744001d109180100c0d0344000e00c44100b04100240800c001110001d080001c805071464108945e584005482010301c1100c0c0341c40341c0c0030303c840c07a03505480d50016600c1c0c042180010340b01420340320001030303400d104440c0b00d40da04000005c01414210000038250928048103000e4802107095a8116290001d003044660b5079241100c08903505440c0c40307900c0ba258254050041c03c00540810199100d4260340c0c0b200c100c90380d01020f40040c464008006203169400450b4499400206902d2698014070040205008582120300300b062480d80c2c0b0ad142800c01d6881c4403003038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 953635872 1250 953634622 953634631
    0x5180a150305010b01090f0b0906220602072c06041d03041d090c091909020307180e010606090b070f023601030b130f050d0201020a1209020f0405070215 67
    0x10f1303460b40203000107540c104515074050700c52411840466810702801200e103103c4c07600d045004200c000b40601241013000302c21400303903248001e00e0a015599410083d07860b121405152901010b030099400c000c03600c2c5681c0c0c4402c0d5882024840c143d41c0e0a01000024003c8540b010640009507200440340b11003440280b015050201c0c4265040c01e40345a40e8841c07060013040d02c00640d102c95603941460f541c0c1040541c1c050116202c0401c00e44241070428060041c111000f034240c4a020000702d207103080000c8404e0113045010042114480401560f400d0314050320918002c55000c00e0240540c00b0504000c000310f500410494000c2e20707550340070801704142684600428807949401c6000041c50603560401d940e15652540d00c6541551684000460003070708a618100c46800711104001d103001508040940140c1681c1c00300c0b0501101038041e511074281c0c60300003540d8050b40c0000c1c88403031061010441d0060f200340d011524000a00000703250152610040d4407a040c42040d0b81c60380c80d100c0d507114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 953637122 1250 953635872 953635883
    0xa140322080703110a080601090f05071704171c02070c0515030a0f1d010518120301090507090f060c1203090222061205010516020705180a1503 63
    0x80c0c0004100d20000030525602403540d0800c4400d0030081800c0001c0c0c001d0950f608042400104407010300050300c03a200b5580300141034000c500002504129603488081e8804000c6024040c3c1d40d90248211000300505001c6c21850410101203030200e41d08115105039008a699801d140c600242c824200d601c1c90780541030740d4903400040303150402207040f88500050200f03903281d82e8007251010802040707004c01400e42c8003803580c801a060751a0b0242e0062840b40201c000184d101b03120912541c1e001e01811a44000c0243c611840710242c0440064801000168401058203590030545084040c1c8030260060040084140c00400e0401603040d142c030050546459444400c03105281c0325240c0e0035a90500001c0c145410b03a02005078660240911180404182d42e00c0d20002c40c1c443c810040030513400000c201800d105040e01040415030049002d47c030030310201034104140e41c44c120781d2200b9500605400800079055031005002c08a101600015090404580a4078000e20141154800c0e403050302c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 953638372 1250 953637122 953637127
    0x82401030b0301182a06050c030f0a1d0a0617060406030507060c03081605030c16060216060f0605150c0111120a140702190609140a0302070b031302120a1403 69
    0x304000c41740e4508240c44d245019004501607001c810110312500e02c9480d091090018103a001540d0a0084514110f2020050342e111000c50070002c2110103c210b00b620f0034074640d1324400e05482c11540550031194280d0707600001d124001484045034502815464005031201e80c0480090400d0007507001034001c0b80d4400300c04030b01c0d50a005024181c06400c2441040280c000d0790107195010046950246141d030010366100070103022a800d100386510083c1c001d40c408100d03107003002c03070215040c207529002d200e040c031040c24424000c0044818500c102c0c0d600c491035200d140319116075080548046204e2400014401210030701c0da034800e0340010071250303505900d202004401c103800e220740b80e2104904113078084d480c90079181c041d45d81c031001c0140181d10408103000b0b0f13003005001d400c2441b50076440307120504030004041c080c5540e0f01748580100c01501885002041098280c42568400c01024280c60080003064007408220505503030780c0300440c0600d8103041e02042e1705c0c28407060800064002141e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 953639622 1250 953638372 953638421
    0x10b091905030607110a06290103050c0412020613060203190309020a051207050d20090c090613030803190606090501050d11070c170607082401030b0301 67
    0x180080000d92a100c035440d60100601054a00242c2c503540134001e07040c50300c0251189a1a0780c60b140e900100100820b091220010000361001c1c496100d0110740700749801c00c6c1c0c450320010350540310708495964481c1c605100c00c0107103503d03440c4016020380c00070702404d01e0300c0018003600070000066040746002d43d00000e802c060131654a580044400c6151a00b045900d8035640020440e081e81e109292107020032410a0000307850034013200c030060000a00700034000455240466a40307070715000100144400c1c0c0d01581d1541012a50b0358070404140146a2030006000100415038018484a200805034600048000703400380c0002c501403e1b60140d1420540a4030359000b00755070054102804200c0300407005c02150360000c0545620004010300403503180b0703e50208140b280036110003c0e0051042c8480043e000c90000345840300b078003c4205440c1e00d580c6840059594460540d00018103110700c41d000200800c6019039201f48120500d4040b80d020756a0740002d017520300c60034198040038445048039 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 953640872 1250 953639622 953639629
    0x9081309061809030816120608100e0f060c070c12080903100209012a12110f0304120219090f0213080a030e010f0909050a32060f0d0b010b09 62
    0x30b806075009a0700a000d0010075580090406802604803228100000c50100001d0702803080252140ea500508100c415030f0703004900d0741c074401d500308060702524000c80380c9c00004001c0742606103c0c1c401070084c8400d80b200c8050341503951052030181c40c0b246902c0b9022421107000420310307031554003604049848140d624201401d100c94400140d06240c41042201d0380b60340c01800f0f9030121a2940180c520701d03122117004512440c20084000c010107a800c5003c086540c12174004206441c080c41152241204911526560b2207503010300c2125000f014101c000618000000c42401c5441500f001c4180c3d59a00d000740c284e480c492000122190007154110060f0003080260004214110041c614402c09840c003401c1046860000d6040001030840c041030b4601902120000700076170001041607180c441c80c544000c1640105060041000c1c0400036000114246c0a001c003281d03e8003483d100f500c0390010000c0c95018845100d4010103520849404260484840ca001303003142500380c1d645c0c24035503041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 953642122 1250 953640872 953640899
    0x501091b09030b0105040e0c0301140711070b0910050d290603100e071e020d14030424060902210105010819020a12020c15060a0303080a0908130906 65
    0x41800c0091401c0104040740f100100390381151000d440001d0101e08400742c450401ca10302018a425600741818560700804040655101d07050660317908038150302e403040260315080d891080d103e04e070384203110030281441c21221881d400c441e2420030724038005500812205890070000f281803107108026002040d040740b001d91040d112800c481c458a50310302314222490399482801002e4141c420040000c09040c02034040c840e103440d1303e500041c1c20007080e6600a5851601a034520b0005002c4481c82c181d004c00c03034007640d000715400b07801e810600005034003007000c48450120f078900094560200280c6400540700070041c682443c00c450b84c48039404200c407064603074103a100034100b0100d00d04000300070500c0718291660b02d501d5540503956594038001110080740011205403c02e01c001a461008000080e880358841c3c0ca00602e4055035076000c04200d8240041d12014020446034000100c007100258030169540b44a03a0005041c05c09105100b140d602281d0800ba0080f030381c501c010301c03a007030305840d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 953643372 1250 953642122 953642171
    0x50706030209010804120e0a140a0b09180403180306050901060e090318010c080c0c0f040506030c01030e0304030b010320030d0509090604110d021b0304050a1710050109 74
    0xd00390314000c002c4000a048060003440544004c000c80c142c0c3d0b02c12071013501647c020b00b00080c0710303844d4503031261030300500602400162440741e1610b2100003220500f400695030300480c0180766045424200921402c803c130010000c49c00c2082c84410449545100510b42c80914003a480001e0503183c00d00d141421180301e0b0f00305000e140d80100c204401040008111782d083c40140641e0400080b00400503501108500c4008006400c003041031404c0c010005200f401050044030382c840d03042c52513000d010450b04140c40131038040d045a0440c80c0154001d4000c9000d22186100303ea02e0f083e980c0d1258082c070320b0300307802c120307446040ca81c621030100309c180c20b24000c03c0c0030480107444040ba1511020340280301e01c14100c0c2c0a1081d180028440c1c0d45c469000195a1b03840c00d1029640f0380d0b1b0140000029403040f04d2000300079214103660b2107a12000002d640603102d0241081359100d041081045550782c080d01c040c48588515800b07001d64161300c1c01594003c1000034004200c454075074130b008486020161 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 953644622 1250 953643372 953643377
    0xc1e0f0c0a050306161205040303020703030f1e0903090909030206100e090703030f020309030f030a230a030e1009030206070e10170a020c0a1a060d0302060103062c0703050706 77
    0x14002d100030f41e804a185a0003200155481d1050010824292001c011900e4040d0f8160700c0c6c0f03c01c00c400d054042d00203148162082d0380804c0022200d400850441e4080d952204000b100390050300c1125806610030601d8600074101400803136034642c0110140c6102c1c0350104c0050300030b0f40174031101c3c541c0411014040c048100c14802c540c0b1f400d904007a07849020f844081c080002545040f00460300902c21180b92070005800c0e100282034150366296290320806a01c80062440c41c40e0242d61180c104e49040c40c0f01c8000071062400c0c02000045000d0f0071441c06240c10360084031469461141d16108610a20344a0b8010300890f20b40890007515260594400601414606ca00001200d82c4521920843d8a4007958100729444038a1a5402800380c01d00307082c1075105001c8180c042c0612030014024407140c3e2030707541541c0d9036490203100c501116820b001303015a00060040c400140a504a210030014003000e0500f00c11034650106a602191403400c80142c100030310510610100380a064040c20340390 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 953645872 1250 953644622 953644639
    0xe0402031e01210f21090305070f2409120b010e0a0902100c1407080c270c0a05070c1d0903130e09151f081603080c1e0f0c 54
    0x700180c018030140d070003000b00801c030882d10000c10004005600300c0224243c070302805003001740000180180b04180000d460a10885800041c59a174210822054941126003001c2d8034071640c80d40421201d0b06038a540a00980907008180b10071401d0748544164010032000455501d05450001c1d480c0010301407244050401c40032001507194081001d801000b5803410f50b481e0400e50508201c2c054000d806040907000711a00094601030014001603c5082195800204e41c062800385190566031007540960b5254200091540c0c0b5040340617007500461420702e140f5080300d581d1040755012494000d82c0050076016844443e0402881c0c4140c1d0129000d401149030003801d6410704072000d9284030f0490400120400a582d244080c490300302084003c0007810b4481c200190b44000400c081607000e40450048400042c040f1000030701c0c044d81c03900c020b003003402c80ba04644030302e0816404001c1e1001c8034801c1201601f4540c0b271546200b25104440002b4080075038954524606040e03007505098420b0108 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 953647122 1250 953645872 953645909
    0xa240e090a021f020a0203060705040305160e0c0c01020c1002030a050709031716080a030e060c040324090b0a0b120105010302060901210905060402270402010f0e0402031e01 76
    0x4404007440b40f1510408011003042c2d0381c0208903c1c01000700f0000350175009036020f11008039004809030055078801c8080c1c031149880f4601d800c09002152180284541016000c02c0d41e607001c0030b00502c0b2003410380d000540303003070312804400340381c0704211800f44503280e800410440316560511038250000511b02c1c3c52640d5518589070118000f001c0c030030740603010b000040e0030244440d000d00120b442c56401840240c032628290b1000d0000c0071030100c64005805002c1c0000c0140c103101c0c04031002e6903408404840d40c4806c0c192200c01c3c0d401c82c404481c8025076221070703000c0071984040c40d10384903330b00300000410002100000d01001040600321450143c0c140401840140d44200c00c0d10101c81d030a1038000700300e15040501d44040501ea581c541e40384d61030808404107111001c2621072003079000f80c440f844514807403200d06d002c00d05001d407040600071a48021800540c452800701c64401c902d8070f004060008650009012a44151000340000d104401e80000510a040c2507500500080c860950403052 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 953648372 1250 953647122 953647129
    0x901020a0e040f0225031709071202010516052503020f190312020114220209190e0703020f03060103080a0804020a0e04050f070f080705090a240e090a02 67
    0x3048084144a0350316510482c0f4010029419918810013138110b5644c03518401940c0540991700c035109800181c003403030110f8071950442d40424000c284400042002074a80418200c0040d0030388012410003000304a111008141c0340401990507003c4e001518507444920170500c65000f880b0a04048102940c8041003d40d03985134415580308000c1da02902040c1002040844440150700001c03c0e4000005409410650541c080700c24809110220031094840402c1ca04142038200e000210801246400d9401030030600300c41c036003001e94001c40b481e80c110800c510740180d860f0050448100e9100306420010b500c0c1c521600d504840c400e0f0040e005a50640c0c844444034843c504150040c885654045021515101200d0b1300410308050925103071b00302803504030788400820360a0305640c0f080c00000300c0d403010403018610403039003001d008008075850722040c01b05c9210003c0070348165903074801000e02454440303500b80795403428601c502004e450411240501d50000904110043e80c041e030b6040380145c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 953649622 1250 953648372 953648387
    0x91b0f010c1e06020c030706050a02030f0406021e3001140915060706020a03050906160e06070b010609030209010b030f151906030e010e0f190c1a040e0901020a 70
    0xd0b04100c109207a5450000e140ca119080688010600d070720000d807907403840b0700100192140600c1031030240720343d894440e5030000b13a000c1030b00c1c0030300d00182540105000401c158002e0150019107420024503074004041611250072910030500c080c101003541c0e002c1300c841903648922072002c00b0301c0e811075541820702e45403840074050b080c980200700da1008215443c4080009520b0204010801580c880880c07800130080d4201844c0040880c0c14440465204c510210300c440c8510382c41039030300c50070550a01c8200c2d0750000032501e1a40210003000080701280030028541d000e0003035510340c107814610794818410280016442415814030500a100a10f822050306641040d0082200c42c0480707042d0b0001001d02c02281080381080980c481c0000e1880d0301604840a4480e296000300192a02c850601d41c4076904000001d0454110800410340d0044810700040f10a00980700e1031141038507480d05160440c100010710503800c10104003001201400e01d6420781c0451104003e50a0001c2e000c030143c502c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 953650872 1250 953649622 953649647
    0x10021902040b011205100e011415030a020915041a180108040204020415210608031218070e0a050703090f30090f15090b03150405091b0f01 61
    0x840d1922540b9a07103a00c20380d6011607082e010401000682130008100e02c0d1500e1a20800d10702d5491080002040c100141000410300005090100041c40400f0030300156480245442d0410b0360074045178103035489000c511041c5590b0031286a58407401c0c0440d0443e15070f000d00018003000f004216481c00c0642e44440d0564441c028241000305403182e00c00a800381c01690051701200c100c02c0c4114880941c840b160851502c00400f608500448581e40c80c400c1c1c4000d0301440700654010080301e4400d00501501c03540c414480c00c01c04400003503022041c0c0c1003c4955010703400c40b0480609111040080c0d01c15070f50007078030a003820440710002d6a917081e008261410003030101c51100840c481e0504e0b5910500024040ea060007803980c0c1107808001c0d1201d101401000762507071201101240c81c030801e540c1c10b800b0003059182d2460091074003618580c2580300400d05000c0c850b001c040341d501c9403124002c1034010104c4034090940420308001803942c886100d085540b0404401003110010b90300040c454005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 953652122 1250 953650872 953650879
    0x70306061e03140a080d0506120706020c01050708040e07020a0c120f1202010f0516020f010b06030112060204030c06030b040b040c0509010c050c130c12060602070605210a05010510021902 82
    0x225070f07494511500708081020040d00b020070000b548100c246240d4005885240201c401000d0000302c3c0b501303c1da682c640303405102c01580c80403d02010640c040c00203000c0d6240f15803806403400f5181c00710404159411f0343c5090159201341000e038200aa50403492000c2c096000d0780c7c0314240d070541c4840e080c00407000c8010f807400741c0c03141c81d81050910070b420808403071030289401d0200d410072001041f82d070202c0c070030054014003c81c0c1c0c2d6410700f141c06000702aa041c400800030360550742015441410a030341c44008640041e8200310000c0080c070300c1c0b00708600502150f1000216048620103000580f04e107a49124812446c0601510724a50060192480d20701c4c00e20340071015010724500180390003690b14065505c071811194510b040386042d0800402d644041c0d03500c00700782ca916000403041c3c41240c021840540c10a02d003e0155070310900c040c4c2905c11500d0308880005901080d0208900006c0e0f45140c0c800741c03600018021030808022611840c83c061004084107450386240407012054450028030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 953653372 1250 953652122 953652143
    0x29040605030406021b0303090d0503040b060f011215140d150e0102040f1814010b071209180b0307120b1b22080607050f030415110c070306061e03 64
    0x388211135050b14000b01c4141501d2041c0070b54101c0e1750f81e407078000311040c00952041500914900c2d100740c0030b490041d94012150112500e503442004000400c610800c0e04000055014414400307990148a0507500003402681000303040c1540c11010206808981e405940307041031a20004d102801071307280c503100702c0d000043c01d49100740d400c60291190ba40450082c400c06800418017100c42c4005000030a01410204039414641c404034100140902c1420300c06a810722010b4041800c218203240352441078a458a540d54588110402400c011003191101655868443e03050303080070440903024008160110b00700d0003143d521130010a5000300100d55113010a100e10110079800b4084da805036140b010501c00044a002c0c0d070f0a100082c900c10449184102c1c1d0100c0c400c140290101d0301c514000265061450380d0355101c00d03255001180900c2c0ca440c6d554417108500b9000a4080c102c000c003180d02078100740d841c50030228180d40464000a451403441d548400503450040c0c05403046036800a02d091 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 953654622 1250 953653372 953653381
    0x9010804051c091e060c0308070318050618010e210d020301030b09060c030402100804260a03060e0106170a060e0103080307030e0f06060d0f02030a05072904060503 72
    0x1d040040080340988249104045000c03100d4200f5000c0040d258500221071040c0420b5100c01100842c0c0c3c49040085031003003803d40c010030301c0752171701b26071143c07040c280440c2605a201a01032402070241003a1695004081480f6188000d10794041c0200d6041000b4003c1010f046038842e00c48a0030700340c2642d5410038029208030140c4007401d035210309054200440d01c03503940f030a04001c0d0260484e0409218011440000e980da102181524020350f00902006441100d00d00283d0700602d02400a64514070018000c800303480c15100600910382040e1002c0c4c0e210b5000e4140030342500c1c400e40003070b89241142c41c010700010380d1282215141d05039602011229865100ca0306000b40305503080b41518118600000c001d02500c00025405446c440d030703041142c40a400c11080e242da0840440003034a401500c01315841c1c0c6401d44460000c14040d088070050350286900091400c80450030031207c0740c01000007044112120424200700f07140294040708060000e00b1101c40030720480c0261000c1c84804170119 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 953655872 1250 953654622 953654633
    0x1014070e0a030c14150f07030309140d050a1803020f041e11090108070807090302040b0f090f1f06080109110f0a08060406061407080901020a150603020f1509010804 72
    0x10021a0480400710340c441d2a4013241442240c1540340c140201800a1072038580e00090b4119010340c18207005650400205640c00c40141070415002e541c648a4182c01502002d418400e12600703180d10340b125556460f0252025145484002d80107010340c03902001040581c80300c80510035170440403a00080d50440da075034501504c0b08110310b807103009441c000304011044580380c01080d645e2003d8070380d0091955101011650280c00700c07280000187e04050400050800350014006c0220003803442812103a43c0700890500d43d0211038010f0900100c074240245400c404048404050200c011202c6407810194050151a018820810789641d14628042e6000d0034400703880f406840c00c0d0306960b94290030a4010402801503400034816450018009107d5009083d41d1031070303840150000382402125150501140c01c81d03681c0320f0560003110b14110000380b0640418010154141c00050410304500502402ca2500e501442c0190f4200da0802185901541a900421000d00c0c124000da41d03203140c00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 953657122 1250 953655872 953655889
    0x3010216080a11120409060b0c250b1204020405010501050405010c081812011a10020a03180b04150806041512170307020d080901141f0b0d0e1014070e 66
    0xf1240c4c0240c0d900011400509402002107411212080c4030954403038803409443e115125075805c0c164024090301a4442010441c0101c00294000001d903240d61003080c21401d51220482450b02510141000300314a094461140900420310705641898200360002e068030782e4408003d0441d01d4040b0380b6105c0c1b0840107080c842a59809400071004805040005019004800401e10b4030402c20500f01844c0c10300846003000f9040550042c00e15260540b0191b850703104503118180540c6603200003080980c1168001c100070100c1080c0312565207546200104000c40140c04140b107641021900014800240c4c00da4007940c4410760511140e801c545401d844540c5110001403403c200401001481500030800050442440d11040780f00c0e520a009036080798511a012500041c950b07000c10307003681c00070072044081a8011528800b0340d8807080c142c07003160440b0b44200c942c55102d003003180440c01d050101003e001152002031100c00c1000940010f1403100078500c1007003010641340a0110342d01d0100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 953658372 1250 953657122 953657147
    0x403050a0503090a300c150e0106050402040303020c13020a05071203020d0c1107082103090304180510060e030a2d05010b1903050c060a110118030e03010216080a 71
    0xc0b0780c0510a441c200104c542c1c0d0044503003d5540c10031005c1d8003018021884401503d900c1684012028080845080245080c4000900e01d42d69003d000c60300d900c0d90b100900146010b50000c1009080c5641013002c2d142c107002003600301a0050101c030407183d4100050350480c80e8400e403011402058a1000c800a00072140d103030060070708004c181a01260070400754080001d1180980700690f440b500d0040d81c0700804011501d468008011001e1010482005140c000c0c14800690385455501c0701e504014808041d0640341e010707643c0c0e080c410401080d1725198024402814117680c0041039500080e2102400f0402402030b40710040d89404003140cad208681c5024440a1000d0038807005414483e0081424828039402400904c41c0840751614010100c0201c0b5400402089100301e0030302404425086840c010081c040101e4100180c00300138003a1440d4039682c00c01d551000d11081c24024a0001284078490281e48100904e5850041881c000c0034941e03080003045da56040045000c441c4840ca404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 953659622 1250 953658372 953658383
    0x91612030e0103180f020306100e180c090a0606030c26070e0406030f0204050a09021315052107050604120609080706060e0103060b18040b06011809150e0403050a0503090a 75
    0x582c0d00f41005031200c03480e17036024003d5049806c107940d8984c00d0341004245006000a10308510002840c0d00c1c1420008034103442043c00350354880c0d90400220700d5078081030311314003603583c0c80b01030a100c9a070b89880794040807402c030700d0013803007428111010060305100c0c0004445010418800114503034016100c0400344500900108000c1d6941d0a10700703040c5440241c100d104509180215140d4800c60182c0e00455800420344841540011219001090760b100156580c20f030201000510780d40318101080384107a4810b08243e82002c800145050040540041d8480c0c00c0600c030900c61100390212503c0b10790b0703000300b00056a07025420035002c58001c64100174003444c00c0c018013066a10840004038100c9102d0502482407030390b203800300b048003190804c0c600405401180000c01080809035030640188060401035140052070340116404d10058104039090760300c0b01141a58811100c46900c0200141c4c101e81d081410241c0c2c008005102e0300050908204ac0840841c0002100b40480184640d000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 953660872 1250 953659622 953659661
    0x1050d03120615050c19030503010e043e0d0c060f09080a0f0b0a0504050d0f110109121202040e060607150e0a14010c0807030e0a061103091612030e0103 67
    0x11900070704d142e01120031500503000b201e00001e1140040c4401c810b40c1907041c1c0f00d0364196800c02035008550f000051003901d01c48106111401c49120350303600344040040c07404440d10321203098020032418284036400b5501074240e001800c004180f800c4a5101a24403030b03e00881c040b00c0d00d03a0111002d0801c1d400160301402102c0c24030041111102c0d00c140c4240c81091f14204d036580301150134003160411a8041e041c1d4000004d02c0460900c00c40020801402c9400e0140d46518800b00580c03c4900090044848541400400701040c1d088119640383c0740c4207041c10b40c682402c0c00c0d880380503800085e10250203030300017042c0c800030080800c2d10510522032029040204001c818040ca0351000f454000b511003d00381a100074a044040c094900c189180e51138152080d2071f41c400450080c040b08500ba04076009403505400056903078012055000c0c0344581c1c031502e07414205c178040c2c1446600d0007881d103a0700040004000e0642d401121541c15a090705145a0310101c21005030003600001d8588001301215 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 953662122 1250 953660872 953660909
    0xe12040f03121110020a21090501180305180d0f050705040f020414090601030e0a030503040242070c12050d110a0b1504020712110601050d031206 64
    0x4040384101100d000b8a03059007221810102510240080816811103030058103071070405140740d40007040c449140b40381c4030306081d00019031840c0c10f00306408081c0101c0e44a00d000400e2060074040c801080c1c508140041050000d40c3e400381040c0700e0300307400e2503024401d2032a07418650b480e91606c44040b6004080b801981405241007500c90a680c01018421485c00064500100c1c8503c00c4c1c41c1501d1039429100301e10f4404108100c007040c1c00400f424100358407403079030400b000002d0024440461181c2c40741030312414284108680c2c2005451000b0313122080c019201d0b00514060329641c02c099408500d400040401d400c0f8100e50302c2a21809020101440f800243c0c10340e9101600710080e0103035003a02c0c00300c0f00040c0108c9403065a00c20f030600650004183d400403a4401411301e811080d20002010040c90140110381070b600404801d90740c22103510900354404c0d410a1844010b4440d0b18050320b103542c100f400160090b000800058100154265142001c051960011000e0705850800704c110456 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 953663372 1250 953662122 953662139
    0x9020c16090204230a09240f0302090f091006140a0b09090103080c03070b1e090f0c010f0507020a09050403110d021002030c1201080c0307061b1e1e170306010c060e1204 74
    0x180c058036420b21f18210744000030101c2081c1c205500b940e500030300c0403000e51030300a00d4004203071300644404c001d40520ba0071005c054095219540040c0b41241d0301340e448049000c10400c036134110390301062a04208000001e107669a003107600c0d040da54000c400940b28510202054030303500406600030030300c24036070303040c0306984803483c0010b034030841c0f420001111659400655912a411140c2007101c0b50b002d108940a290b00035104082d00500e079103009418101d007600000c0d4131a0b416805000c1c0384d603540c420b01c42415442003400300c1c100c0300b5000801200a00301c400a544802072150302c50307603c0d8040080f8402d035043d03804503200c1342085222a022944c442c0b04243d00c4143c03500e0703918401d2045440c0010f001d4059680c0018441d425490000c244955444e010400d0040c18000b101d01c0038a0050440011001c9446003051810320000c61100b100a1030032800c4c0001e60b00310030408007030070310421143e80ea100c1d0409080c1944058041024140c66001c0c40c17404c840c600f509090b41d0000304011500a0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 953664622 1250 953663372 953663411
    0xc0d060905060a08030901080136050709080a030e0d020112021911150f04030309170712050c211b030304020f0d03120c020709020c16090204230a09 65
    0x148101c0e210044580e135066140d5413071140401c56400310380b045004014038441411044480d00d942c040804070540c1c0910400c40e420b0402c90014800c507520300c02c1c000031a5100140c8005440394800030480d80310503440203481107030149000d91150017140e8041045900c80c5034903c450924042d015920740804c4403400c2ca240c110710000c5400a0b0101c202c1007212400004c50302d00c0034890408042079501da064070700f0122000280103400703054544003041c0006119001c0280400d00003080c41d51920114584031700d418482304010301c00c005081c0001c1024000114161320101542103108050740d9403c0007221244c0100340c1c003a0707070b45080350880c44040e4402000075032065100302c1e65040300412500c00c100e0344030861200640091041c111602010071107503c0029035000d140111100c1650300c001d40c030141d038880700d200601d98102002a40644c40e020403250017900039070300b06504007420625103054074a04003486010b00c0c100b0701d094807038640352121140003800744c0e038009120424001c5018540341 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 953665872 1250 953664622 953664631
    0x2040c050a23160203010216051e0321040201020a0203061006180305070303112503030f0e01050904020a1806091805062d0a0e0a0b040b06120c0d060905 67
    0x1603188500001a6440c100407010025075401009042c510000d07150f00c030460900708201c2e01907600b0040441e000700902c08402c1018807a0004100340c030155050792051608550403000c0c1d80e0300c1400110418203501c5003a41c0d00d1004410395030300c40e55440c00100e240c00c40341100a50540200c8060241c0b030301c61030019806a0f01c064603130341d2980b50000c114000c03420f01e9100280403904202c2052000a1086084040851171320088906031804244d070328503d202030f8041d141280d45560350800401d6000400cc01d642c0c0d80c681441c0d50200300500000c0d20034803580303407690b1090781d0014044e00c0d007074041d1048410074854110701030071503602c031840940f441402d03004208c40491900140540303040e0742d00500c0d101d600c0251030400d504086490701850046c440c0c2c120407801d1840901d850540c1c480410510003800c00341c0e002031481c1001c1d140c03c8100c03170392a030400703008074100041c101c0540c4902c81111450300d5040c00008155684101c40140ac4c00380c00c3d01807128505100340001c080003a030700030320b016 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 953667122 1250 953665872 953665877
    0x1050a11040b0304020d0c0803120f0603060402090402150f030907140a06230403080d0b0a060f02070e0c1e0706060b03040f02040f02040b12150a120b060d02040c050a 73
    0x5498614028040c1c1c000c0d031140030203059081002070010f0916004001c3c8452141542d102d802e51200c00c05810b6402c4464032610003030fa18000c00031a506a080384a4100364160301418007810030350003017031600c034000300040d00416940c841c4483d00794410044944407911032100e02c0c0c490034411601501d038811031095002003040300038103201c945040e000e110100d40207600c83e081904040d60444a0f0159403030480c8152407414000000420900d0004102e00c4444c12800200c2451541c1045134a084980200003080840380b40007090f1500001d801c8140c032002e03003828a043d41c03007942c000c00a00ca103110044415465115100e000070240c00034180c00d074032a00d03080c0f04042e00c2d02e9034100203010443d0081d20310308c1600c18150140c01c0c95800f0044170314201c03001500e0542c1f00c407080c6c18650700c44e11401e2103c00b400c2c0200109070705610394141d0090300071150442c0b81341ca020320b062400e1024610140070705150302c02045250baa18603071480c0c101e82c0540203001d9003540c400080d04503040703814030101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 953668372 1250 953667122 953667131
    0x70606140603090607081003020d0b0727050f0a030624060e130c03151205010e010c081f03050d0918060515090a0308030a021b010b0609150706050901050a 68
    0x1a86080e00c182c070710501c0808018085a0b5900728122805c03000546104114050840040003680780c042c40605400e008107140a40c60030a040c005065400000164401c02102100b0040400c170b0782d1141021188211140307a0811400000542c007040d840c0d0005181c0ca10f4071403403021203925060103142d05030800d00904180c0e0345d00c61095403100f0001482036031180c59100c0d22540507950754000c0070660103c1c40c000030502e8003081c0030302d2111200d4000c118500d0404d4048003c00c10309024008803480fa0070001e02c0101c001c0746018041002c05403081c3c0301c04061500008041d42c2c0420440000c40d0490101d40111040540192286025004001c00e1a003072207201c80c108006801444101d0720040c111588002c8211403544894100212041c1c2c8017030705020010100c0d06410107103024001140700141c0c2e602d9030314100c0c0a141100650810307503904050a8041d03036910403041d55060350b0207031240030100410000000c1d083c072400500600310351074807080c001c1820b030540c0664400c84441d40f0402 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 953669622 1250 953668372 953668409
    0x9010b100e010f0807020a060e07090f02071121030a0503040201110a320109080c010e1b0415030206120105010807092d0f080a02011709030a030b030c0303070606 71
    0x203a450101c04201c50120304042e420b030300c05030b02c100255680409107105440fa10310301c942e07606023640d001480100059000d032006200b40d9440d4072610079128454581180782c5146580c5540c110610303000d070039102c4c428000203032074221314a02c550350b0480180c50030340e40d8910180c030010f85541c10664003a070029810076041c0200c0304000074060404c40d04804041c070345101000700c220380c01122500b0032903c3d001460341c0d601810803d0003041c0c0c0a1784502c0c14985ca4000b1a0b0603c0d0840d00308103d601c8a035884090307411030917409000388084586081d01e020440307800e0f040030381c81121140d40c002904010000380c090640130344140d025042e110240c0c2e41004e81d40b1000d008031680c84442c0640c040312980e20b400721a26103011110401951404401040744aa44040107141c00040390f010512030381000003c0f42c110360b4418210220a0840078500330b15082c008409a0750780aa03142d604141642d40401c50001d5804000c5403c1500c00201100c1e6101c070546410700c00b902c45c61088910081e82203140d031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 953670872 1250 953669622 953669627
    0x3050d080a020c03030406090c092a0801051e01090b0a0c050f06090d120e0a030207080c0103380a0914060603040506071d1302040e0601090602070b0703090e09010b10 73
    0x4500d40600f4900a5041d17490716112031000345200201224500c0e000d80b400505510180107510720a006985c0c0e201001c0401007d0b4400c2c00301c50b0901401b00034460006102c0c5035145400c00f828000b244099840000c0d40700300594190301203810001384074a0100e20094126404464040110710400c244c07035550031107605442c6e544034103a80508d00e9420010030590038a200d4004201c04118a21000c5030340c1404090441c108003083c2c00960060300200d10501402204121051455000f841c0c1000b0882103070019607480b16a03c1034104000c0a640701803144114100320740b0464170300042c03140400d15580d00c8200014062003000e541550044c41c001034052034014280c0e8480e40d042005400990b55055080381c080100079003074000c0701e004a901005941315090403210500101c0c41c0140d40300c0c140182940b4001c0d00500341410400244400e2002030360205100003103075815a4400d032991064542559481455002782c80311080070350410080120540040c040482c1c00c2e0707240000c030603c42908 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 953672122 1250 953670872 953670877
    0x201090201080112240902090106140d1112010b0d0e0303010f0e040312050a020703091502070b090f0607050715080103080319020c01050f010612021819030c03050d080a02 75
    0x1074042214180100011000a5011020b09102d9110700481401c242805061802c40e10908000990303288240003c6040c0030341c81342c1c00340c030a600300404030744001103200b001403003031b00d04080250f61951407a51848d030303070780d801e070f070824121a07210203090343c2c54420b8080d9940001034007141d464108840c0b40c5071402d012003124140c3c0d6814110440150070004214528003014004030100a14034010000b9002240708550142c0d28011001d6920a11814002d1507400c0c150004581103401480030403155400164107801c480d01020525100d41c0c24100040103070382c584ea6101e41040b0001140804c0220110301c10342901c0000740394a0a60454800c1224a060b0900006182010410205905c014604d0805031021001e64026260980006c419400d541c42a9a008000b20f004c4006000311500b1224128142d490b40300c0441c00c280c51002d0310703c032080025215900881c0701c4d1202140c00c0c101c00c003208000e99042420141c0c49070362403600315030794660207211f0800500c1040200f44610303c20f008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 953673372 1250 953672122 953672141
    0x20a03141f0b09151b0a080702031608060631050901060b0307120b03031e0703120203160e0303090411031f0b0a180e01090b011e0206010303050d020403051b100201 72
    0x2e0707a04400711406100d0b107174449000090141c00c0481c5803c031400f01044004030070b42c420001940c803480c080c4180341c5020103048a48818855104040c80401030003c2c0c2e003a8401000c4410001c40c1841442000d44c4080c04450404400d5031925180030086054000900440507080200591075441103080518002075983c58000f0f40741c480b401d00641090741014040070002002e0b246072032060b8880c11064416040c0d030240041c0081600014150441c01c0501440c803404130a5265281049000780031b49490070b100b0041c09207100d40359a0380c0d10100261307400558040c00421031800501c18450a5400440e0b092490614211320130120544048909040f9514801c8050030306d40c007070700c054589a0545031211400401210b00080103804003180a008155003d00044c4d503403002ca000414180a4444104031078010441100b035240c0e001901078110703500f40c0340c03154890722229060310282c0b0441e400034046102e2600e50781400b0000002950b00d00c0e83c203eaa02204020b02c03801a030a07207180c04c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 953674622 1250 953673372 953673379
    0xc0a080114181504120f020109170d021c0917040b0417030903010c1e08130f0201050706020d1406180703050a0209060408100627020a03141f0b09 64
    0x11682a141a0400d60b148030921400e4800240410001602058044605550328000c00500e8210742d0380003001c0c02284082c40c0b00a01c4203c509840d070907074400c074281001850403400035444040d4151a8180c440411100300b28107100800000c0500160010040996800d40d040c844038088c2c501c490102c5080701c881440b068206490714945905030411581192418041002190280e58080c0f040004002098880c85112b4820300783e03407008560341800c1b01082c454607005002007000c0384542c0078002d540c0844d002203405401d10040b903090160a000030320990004c070f8040043c0001d80c0060005044a0401ea209036640004002d90022a206940c840000900101d01c1c694801d0b04800d6020a0f0180c02516100724600072038902c0e03029030f001400720f0700300224449820380580141c02c0100035150304080315491010f00c0d000651140d014180d0101da00042089804d07010703800c2400c0015a031402c25405142441043c144541c0701d00c0c0414401003008004107916003003005030340c003210015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 953675872 1250 953674622 953674661
    0x10b0105070b192315031b04050717040c14010804030c030c020f030d1707090305031903140901021e041a03040807120909140412031812020c0a0801 65
    0x20055071185004141488000741c4481c003820303032031341c5060040d00c0080d41545000810b10f000310800c2070400403a852a4801d42054411300c990000b03002d40740b03410300c804a900040070740355079070140e501040c5405014800940c6600704405c0c0180d001c400e004648259103010310707141000004540710102100c00030301040940703000780c0c0428400c130640c403400c500c06000f0074441c4c111140081d02c0c0000e00a020b0300042c00944010901c92400f01e0010780003e003500f001e90b02a4119070b00d49449000312045010846007820106101c03900c6038210a510301c0c01c01d445401582031010200b4080e42c0481c000d007007030314000041c624503040800c080b9011108603500b51340c4040485900401160b101034010703240f240c018401d5030701140308e61414080c080140d89410b04d2652a186000d800e0741d203401c10f5041184a44d00c20400403c480c1403404c401f11000d4540000c444801e00b20700c0c0d014102540c006040303500034800700c0e000d0b1130300002d050f00c0d030031001c842c4c1c2c0440603540d0840d1806c0e1801e05468111041d540c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 953677122 1250 953675872 953675881
    0x3170c07110d0203010218040b0f10230a0302030916080d030e15090105100909031d06190f140c0a020925020303061305060307031509020904060b03010b0105070b 71
    0x140058044401d00140385407809112600000e0a9070014604014206000c45108610380b0b040c1c07180712440380080c3c803000d403030f0210f4000254454107030b1459041409510990880030b03208908081e5a400c0321911090345403070241000600075002116040420700c28075844900000e6410304203c220340311003008080910138400110301070420320400c20b04ca0301c42d00d81044007100074544485c0c410240200005034901d0840d111000f83c107610b506c0403001500e400c0311381010a0b400f00603506042e21415808800f103403030b0305c003041c214412402e214411031030103030309000002c0c1c0c0454240040c8140e95194803400d83c0d803001d40c5000e4822b040c1980300d1075000740f10100c01030a01c41003040e840025a90301e01c00c2c5400c0c5400d400c02081040030703502c0040c0c00c00420401c42d4a0312a0013120300742d0740d02a040105141c170002280d0f89504502001e0514048a0621384440078035400035403115901500300c60560070580707000c001404180c090780344294200201446154801d1096424103500040a298641c85 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 953678372 1250 953677122 953677133
    0x3703230405210f0f07051507050d05100519170f0a2003100207171918091503140f0706050c0c0d0f2001020d120617070303170c07 57
    0x500c524007038030981e820701070b00451010b10f80140801c030103450000382e0784017600d00c1d2140c20421034034101d0004100540c144005654003809403191107500800c001900c0d1a0554583d0301c040583e4452948945015a82e240c1d508415032110100d0b60300640740441100381c2501662641103000501d81d56070311940c0804080b414005042039421001074174800c00d000150f0109080c800c1e1800c2c00300f405038001601c0b10400581d400000b10400d00007120350309102d008007588000d48502122803042001400d40d0800241d00c40d04200000c2040707402c2001140140e0781300e02c041d0000d074881611f080c0e018104040032040081340000c50525030601a202c104e041402c03c4c0e401f038114039541038040c418502c2c3d401168a58140080005002d020b040420102c81c0c500a41005603a01500d201040510f0500045980005005081e4601400c0c8440e02c21069440d43c40280010791107580c4c411003032040c03e1003510011403050190782c000e80d211459074002403980c0c15801c10941786d4420b030070400c2000401084 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 953679622 1250 953678372 953678413
    0xc120a1101050a0f1b0602190206100e0c09040f060914090a1e15020301060e190b0d0c050717090a0e01230d02030601090b0a06080405033703230405 65
    0x107170b041c2480780c1d00b050540c44407001c0b60403014007903008500c0140001b039081d80402c0102e41c80131302046405032617404c0443c4140380030000780107a101c0d80000304615195036601d800491036400d04903810802240c4d6080003030050300721590742d80840b51144011808070000810240d600613006242040484200044211034500851083c1c50051050303000382403405150000318020100c03035407502c03c884a400e01700003840c00301141d0381c5240307540311004110051203407040d99162410344000107412000d0804c141e0f1281304105004041603031071002ca034898003400001d807034442d0f416121240720b03540714103911110703003000e028440c8080140700002012420091002001400c054101002031001c0d50111340342070400e0f0410765200c2c4d25210340014508280e101007005280c14502807103107042989880f0f899102c3c81c0c0c150600b201042c7c100d007a113003181c00040c00d03041111a14040c01c036401d51100800a2860011200aa40d49043e03a05082e060110482c0e010340d420402604800b0499884e924402 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 953680872 1250 953679622 953679647
    0x5041d0a0b060a0b070b100501021c0e0111030f0a030b0d24020c010507030b01020c030309181b0408010203040303051506030718051e0f0d03080f04050c120a1101050a0f 74
    0x342c0c01c0b00820300104c000c001d0890580306074007003102800c04000705000c4180c580c00680c119444403001d0200011004440703007129074a410481050405200100c50110b000d4002c50708030f01c8009400540390618030003c1400c41d2580c0e40400c41c6d0403500c010001c1901880b400540400254501d00b800c480e2601c08114038198503c000518000d01500c0240c01c1d50703000c80701000440c0d60303003400f6250b958045c0000c4461400440240d1b1410103070728000360900d807000540c2204502680002000041c52680611810403030502c0181c0783d561320b9800314081d40c000c45041b400a0308050104a00d52840c0301301c4c129040c13000f4207060071a0348541003141d2040c824991050b20610000000519071540d0780c1c100300c4030360419042c0c0144a07103d02880948000050050301035000d00300301c80e001c280e04c407107096000b140c202c0c0d280781d0948690401c1407410341c406003215071000301040a142c007150000760608904c4e100d03904556000790035100545a81c0170704041b64010811090380400500e01c01c03610000b12 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 953682122 1250 953680872 953680879
    0x34050901050d15022115030d05040603230108061f120605060a0e01151409011b110301110c1b090a0b010c0807030c03110102030915090309120705041d0a0b06 69
    0x812102c1720003c0c07013444007080c00c07080f420645001c1c48501c40284c003919a405a09900400c154a419000100303648141e20800c81090368581c1d00954003c00a004803008543e41070080a03075584509801d034560b00180e403100305d1007030b1320701d5240c540c180e10300402c0c001c94000015044031911117842c0c0310b014180c02070409511001d00c05000c900d1454248410340a040540e6420f02e2021940c8000f601c0207074034171031050b41d40e03806001c900d80c01e03079205000010031b40302401068411441454140f1980b803140740700c61740c0f40d420103100810410f400b401501c80d03901004210381c200c46a124241c9085112801c2d8550801e14100008a2495454000c02107030b40041c50036400c49801521010300b00d42141d6011400035009065402c18154030441c3c100d04070806c040214a103003070029100d0341e00c0c141d0b0815682900c00e0340000403a202c1d01401a102c006002512021110003d05046511402a805403034404d510740301d2140d040d54616000898500480750007005090030684990880d8100101000d61 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 953683372 1250 953682122 953682127
    0x10c02031e12070906020f01090b04030c150c02010213090c090e180304030809030c011d01230d0b240f030603011805010e06010e04051e34050901050d1502 68
    0x3036654040704600d103c0c0708242d0790703041c00d541000c40090400e80700003940842d5138144208240856a989030541e045649401d00c10b141c681589000080704c485c515443c0c3c551440c1403152241c4640640080c40c224680e070b2200007405460701f854404844010f1099000039034422418001e010b03040700f45c1c035004a0003000400d03102041800302842d40c0c0c001d8108a901400224070176000341020041500d1311242400c3c48004181c2000c0c0096003104d6001c0b126041200305400d0310045922118a0000621480754035503850080243d80e00140c50040003285c0210340750032015080501c1501194071041d0907051542c0f41c500758001c0c0c5c50341e030342014081c160b055503210a490f135000f48104051004c980704100100c1d4451110307070103c0c20b08070168400e91200c5100c1c0100000544007280514900400035071101c0c80004040005e89800001595241c5201a80c4007440420340f1001d0081c0c4500000c128248015403070320140110008280300c0d051b080a41c01e682480000d005950b000f4051604240050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 953684622 1250 953683372 953683387
    0x9030f040b0409060828210f09060f020d0302070c050a030327050607020603090708060c2203030e13090b0c0c0609010c0f1d040e0d11010c02031e 64
    0x1900358801d074041d00e020000054200a110341e280241e200400140300a07094114081445e40000880c084d0200d1051407402400030400640c49100760100e030140362458425011800094411a000294040410b04014001079094030130545c0402c00d400503400340c002008100130a4000c4c0d00212002c030364419541c04080f03184c0e10350501d6072000b54002e64400f10001040c0b8001d143c21030711020075811400e0310b100c003880039445c0c0c3c1c000c0f104081e0b410740f6015640e41c1c50075140c0b070801c0b00079003144c812801080144540b5683c00e1002e004429100d0000c40c0307100515a425041c0e610302e03840001c2c0401c0704c1049446040c0381442060188174000e100100340c5d821283d44010761500112a00406041c000c1648070300c5480401c20154000c41e03040080004020000010b0400c1d038041e0b05480c10800701c8040c1c2c2202208001a00003d0307400a0014480c10446152031500c4801d8490171000184a202d4901c0d07480405000d80002e44800350003440c81c005d048920782900d0b43c880e40c1007102400b000c00200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 953685872 1250 953684622 953684647
    0x30603060c36030b0c09030604140c030c09011e121a0c09130c02071a03040b07090f031e02100f0f0504030b0f0603010b03031902101e050903 62
    0x1249980c0c42a03841030700b529010074424140380301418400c10250120341e00403407040c450002d49030640e50489441407142e603031078103c0b004030312507844165014040c00c3d00740420410071402600e22a42004191040d03280002c0c14180d4034441032207a142e000d4050f01c010810411603010b03048814036a0041e41280f02c4c1ca808400c000c8040101d000c641038030603480440c0800d080002455004085104003d2805e4107183c0000d1031740c41c00302000e2941d6540c4543c008006802009450000d020711380b15000b04105a10140d00550030440b01030346c030000c2d501c00007030240d13105003500c2c419601c100c88a210018110340b1129182850040e000c54100312014282000d65503000d800081c5003a26a24884100c00c4081c0040020750102c00c0c22050081c1800144001080c4160440c0d001c058401c1000c503e1781e0301c100080c05001a0980e081d01404006207280902000c0e2030f0b4124840826005c50b01c140c1181d92002c001c4840e075104680460f4034005606104003104d03000030b90018040c40c100ca0404555003102e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 953687122 1250 953685872 953685881
    0x1d19020903190201030507030c05190203091e12070e13050106171006090c020a030311071e0308071d1c020306011706060d020604031e080d050105040e061b0a03060306 73
    0x103003680c2d942185440c0b401c42d039141c003075180d219040340342c1030111800d1200090224026248130f81d40d0080c0112140b9440d6108006440034007078004e00741080c01941d000d90214001080d0790003405184554071404e4030540001d09072085502d03541031695a540d403102000b6069500b160129000c0d503c03018000380f8480c0001e0400d00284a200141644000340c000d001c0032075100f03034807280b580c6045c954070301255500811040784107078050a0115000f41c940140d100b031886090401410350502100c0c0320080320007051041e00941c46600c0754003468440420a40f22400c8020300740030042e030039054804043c2814410b080100b100040200b40f0703082c035030340000d080c0f0b1800d13040110706400258050103840303420004144c0244058031f1010004005402049071407007a400090f00d1520681c1d0740c5102c14130341012015006820060242e102d8a10302d40307013400b5181c00e114280c400c50400448040150010a4450103503605001004043d40002c0720b45105410031420942410b42c0c2d0702c40040031440e0b80c0038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 953688372 1250 953687122 953687143
    0xd091e0b0316030c1e140904020c010603030f03110f090117040b100b1e0a050408120d050a021c050c270a120b060d0602070609030f091d19020903 64
    0x824000b00305000e030040880d2000f140d2030041210780b110740b4424400d0801d0b05c00c403441c1c4c586049040300810719141110382c450302480c15001480098020308005040d4171420075a4441e5a490406c0c2c4880c0c00c040f402e42c1e41c14070f80d14900030820010301c1c401d51150002001041d4040c1460041840d0301c0c880e030621440115002d440040100d0700300404003001c8642a009040c500002905045500c0c4040000c502c26080c05500d000300020522061406041075500030b20b000411601d0706446117140c61580c1d00310549220000f8145004164140350f20700036111142d542c40b000c0f00c800101b22000394041c10b00604403031248002000b201c0080070985840c0030b00e410740810096904130100d018001a00d4241d44465100090351503090300143c01440310681018049462030001d1285041c454028416800300800013460301d60000101900507546282c1c201c0d2544510a0040d070311a2441c003502d103212402c1a2010724900050285002441d6510320741c82c0ca2640103003020000008203241001a26 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 953689622 1250 953688372 953688391
    0x3030a060f0803040e0612011d011410061d01140408030705070e061309050316050c010f110c01030510091503060b0316060e190609170d091e0b03 64
    0x103003841220800c0302070078018110350004510740340c0381562444615002504c02d03882400b0184104501307035400d4020b00141ca4000c241c2d00c90004c0b0040006000b4007002d88403901100d0701800040c94454020400e03002c440450711800c441401c980c01e0321102140300c0c0300752414411990045240cc1810b000030700003422090b0300648e40c880c1c6a040852404045a00c0020b25200364010800c0c541ca50b503074002080841c5003404a110302c00707031400f0b40c198051118492203d61800800405110340014400f01c46076080c3c03288440d10090700012205200721180c00714541d0700c0740c407040400d94421f6224540c00020f10780d0000c282a11030031a04142d40228900301c0340344011000c00d005000a61003050381d0503008400170011440c283c3c202134080c10740e911a107007c1c401d0300e40102c42d20f5241c21040e00b8021150006100d4025182c04d0040c00041c1e1601803a0304183c1c1e040b9114803440d00000d00184030690365241e07000c02c5440d1581f0503c403000d040c0d0300c030003071070159400000701c05e607510014500610404 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 953690872 1250 953689622 953689631
    0x80c01110d020a12270c42050a2d052a07060509210f0c120c0405130b10140d030801030201050c0109050f0f0607050c0d030b011103030a 60
    0x4402c0102411140700404481c1c45c40c0c025070030b070b81d902c0c542c2d80020b00610420040800ca801c074100f80c0451b81c401d41c400f9046c4c64212410129101c1d194944996001480030583c071980c0301c1204001c460b43c030031b41400b4007180040041840507030144201140e061045030710340e5100d450420403900a41d0002c00d00c64003041c0081105031300c041000c0c1030120b80301d03200600701203203c0410702829580c2c003052040340305100000134070200b00d0700c6200344094810f002e004a440c40140b03e0000071740c0c0d41030826600b035040c0129040c00d2010700c2e00c18a07a44800308544010500111214104401010082c01c1c1c41074848006580000261049100c144252818105002120b240c81c01c100c0c000454003005a100311410005000001d400071051410b494081c03822980f5090301d01e249038018900954090f000b84244655114a00303800035046280c040d80c0c1c0280d600c203844103d0191014062400361030783c1c079004403a01240071442a0b01508414005251002100082043c418210f83c01a5203004480e5200c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 953692122 1250 953690872 953690887
    0x904061802120f13020103090204020d09050a020102060a02210c1e0c010b04141f05031504050c0303030601081503070f140f01020c060703080408091215060a060c080c01110d02 77
    0x180806541d00c00e401542542e110b280c0305004c15540c445001c0c0080c14035680c1c099140075074565034141c40e80c0c1d88180104020300541d50900c00e5a5503e00c3c0c00c01ca00600c0b0702c1d400204c07000c407180251408501201d030f040c5034201c02c5119920101200802072060020203201c0c815003a005034160740c2c050900c96080a9694009007800b500795000b100303002e80100d040041d088806800340d661640e00c50311004131503441d0440040c001c10741e407489501c80703a454498261007402c40249100c00c41c2c040e506c1807044030450b1949806260700c901044400074007050280000907008001e002d90130400110003001d0743c00b250384803600020040c006800c00c000302000c100500013682008d901081c44290240000d040c019400710000b01c0c4c0344180c0c4001404c02000304c0201d0100624001510b101d404020058000400741000c40c0e965160385070681c040ba220800081806400c02c1c04410003512059138800c0000c003c40e80f905007841c3e0003844100c103190350700d48a01c800d1002e000040c0c0f0141100503405a41c8042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 953693372 1250 953692122 953692147
    0x50111030108010c050306010f23130e0a0504022d0a03210801030512250b1902090307061413060905031002040e0a090503040b040b030a0606020604050a020103020904061802 76
    0x1802500b41c01d001d0101b0902603180c0e000100b0142e11400b1386490400440551105c075803090035514a0b49040e040400c550031243d6404d4103020544400210b1507546a4814140c681543c5041e1806500800040690200c02e0440c10328101d500001110701d090100c1c0c40c2c00030410080c03c50340700b6070703403607841b0800c80000401221031382c5030f00c21051614411139410343e2501c607290004100600741c4000b00140d555030945101d04160f00c10449042689a001d00d2410f00c01c0c0200001c03039001001d0303112180310b0741c0c80c4141c600c03d0710701c1000098018206130b03003044416204e444403020702c03070180402444008802e8032208042c102404160740c60a0b050f602d000c06051801035030840da80407460048c8804d106801e46018816880059403102103003501c03103410090f00718416500310400340000041e0119102c3c10314030082d0f0007016813040800c0319982c1c0b40c800b240c0790030080d00d00038061b811a08030000035621030380190808450080c00048d40e9660790400c640c015400ca000141e80980100e9190340303c46 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 953694622 1250 953693372 953693381
    0x504051b0c01090b06010807200a060603080405030609071203120204081605040e03040834080120040509040f020316030312230a020a090f03030e0f010e0604050f040905011103010801 80
    0x280d0a0070200820305202001034510218650034035052411380da80011027174010030035840c0858009000300076050305d83c20040104c0d4018020203020f4400d04003c2001d2980002d102011542c200d180c1c094000c110303640c2110309401c9004090041c0741c00b44000b00c0c07012828040044017547e14102000c09618210034442600d11440310520301e50000c0c4020841098041102e803040d94450700075044800042504410f42070080b048201078a94181d0701068200c0c055002401c0b648071090050201c00264507820800e1149004081c0c100c80b484002ca0005621141103180e224030007810340304602c0b030181103c40e50000d00d51065000408010101c5070940442c403a2030a0000382444a100813141007441190f11040501300d0b4100a600054441c115445803c2050103800644a007038a034a0b901c0c100100306000e400c0403288511a9030711610f8956004a030040341c02d140240039207007040d14010030800d0410070481d1036600541c0f00c03040c0b940090700a2050100c00007210880030b413254100b581844c00c54 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 953695872 1250 953694622 953694631
    0x40e060402010807090f171501082104061b11090c2109150c0d06152010090203150106090e0f0c0d020a03200a0e01080c040504051b0c01090b 62
    0x8400c0c4402441b105200c00c0d15001074a4842d09140002c1c1d0b0360365943c0b80751021030740b80d034103606d081c0c18000319035a0800306035170700009651880c07241c248450045004d01840b543c4200d80c00b142300d00c0b000c0901802e070884903010240c010181c058001c481c50022960901c8102c034843c806410000714611a03a5201d400040b0422251b194003929142c9290290fa0f038800940ba0030251400c110b00103104c0f001000e044801a42c91860b00b808540d94912172004c80a20346180d840100320f07803000e01e102c01402c26550261124401c0000c0c50500031403440c0d10020098080e00ba41c0501540803005002c54800b00c9050003800d10b5a1000e20491500000820514026100c8203505646409000200080c5020b440300c400e0391010041c0d848404080030f5000b00300c41030040c422401c06110510702c0f11400009403040050544440c420001c1c2d50004490300081254062044003080c8401c0c032150034154000e80d80084000d0340c991680481000440080c0c000e114850102c3e07442d6419101009108030716607410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 953697122 1250 953695872 953695877
    0xc0510030b0906061c0e0c041404110909120f0c0d05130308091c030e03070f050a0b2b093f09050d15060602030304080711040209040e060402010807 65
    0x50381d00e0400240c428401800d0944504801304458000701c1c00c114002228284100c0c04010410a402e00782d0707101d40c08220213a104a1401c18546502c031007200d0646c1c4615030100e4224030780300420040200c1080d0203401c9110501c170b10411501456141e03002040201002103001d5210390115850900e00919181d00d101000010b10105020f40d620070403100541b5070041c0b0107a01c900218020519064100303102c03215940c400700541e0300303243e003101d101507200304182d05561a0940707070ac000880281542c41070342d40003910581c0400c000c900c007201401500700303010103800407105451400664021a8450340c6200ca070341d00402401c20091020340300418048141d843d13003c22242c00030040c42c1d2103116449600c803a03512442e1003044d1140c0380302c0740030b40401441b80d044000141031900d514100480d07810041440c1c8000840c40714000801e60384125889918180307001c2e440e59a40e1300c019512000207030400e03021b2000d00c902d50754074083c4e001c01c11003200c000c20951400d03000051184102400d08003e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 953698372 1250 953697122 953697131
    0x1031401020c030a050919090f05060f030a0201080603010912093305161b0e0123060c240901290f031e0307021518041e090c051003 58
    0x12508003205a9001c804e0794101561200102c0300030480c006845900040c081703000b02d1000c10401c03500d40c485840079008100c2006290b5500e000e01c164004800c6003190b01d41d004101c0b0400641c41808542c0c0e1181024001007000300c00c0d07a03a00300748403181c0e15880c804906000420320080303680c0003c1e180e06c03a204141c1c02814081c4420700c0502e00001d094400c040000000c3c034050340381c0e1a1040e030240b03154048580340c4401c00060300080b056050340500150300c486140001010040302c0040240240040108981481e40c6030402000c1e50080c03903503041c140aa1403003204100b1480c030b08018443c6009140280d00c0c541004034900b150400302800300e00000c00e840d01c011a0b001a070f00205503280c03c1e10403040c40c420711000245841390150501c03031954840c1030b132181341c41004009807001510a075114091001c2007035021200b400307a0780140c019918040c510042d68542034001780003808028030750b016000180c041210507a40c6990069505d200c0c421001c012070308000720032850035405480e0400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 953699622 1250 953698372 953698387
    0x110109020108060d0323090a05010207140d02241b0d020c01030e0f06041b0501081504020d11030405150c09030618010b03031801020c010e09070c0510140103140102 72
    0x2410b210024003034074000e508801d800002c00d03008455480d4220318464125a080c0321001c0c02c0a80c07903100c031072a103014400c0e5900019107540000b4425088c4d883c6921348030a60308848090201c43c0301e400e4000c0c0e0340701205040452030b84400105001814564021040e502e840c02510300e044851041c410040e00e901a840b81441c01d5808107200c922010246000b090241d0000c001502d05048960b0804450040324141300402c03030780d17610f000c00c1007801c100311440c90f50380c40e401510740071002c4441140a03451000d503192180351982c01803e10f0300d0343e04400100050300c0c041c01e03155508111400c0341d40d940304800c82c83c3c001510074546035100d444020b4091030a0202d80c00f10352a51005001d500c2c10b14201e411b980d80707240c000e40010400180c080c085030f803181b24002d078500c10701301c41c2c41d00c59003d40200ea00c410180d501c2100c0c0b805000b1009840240b56844070002200c1c0009410400d80365406180c194404940180c002c104211a44000d044810b50450410265241f010000c2d0304960b8410032401c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 953700872 1250 953699622 953699627
    0x2c010f06050a0303120f02040918120806030703080901090b0a03091703060f131d1501060c020a0e0619080d03050c12010e1803030103060f0b1002060a09080d110a1101090201 76
    0x2030717000c16803284021548641080b084006405150880c7e8509814901c1c44041e44040b00e103900e00540c0120801c40c40c82030504010340c1c80d54001e0b1104c0340c140d0054001407011035100401018050700c185010b0440c9991420308030b845130086100140026120b070b07640d009200c407044107610913421140c445481c50070f00d200040c8000c60080039642c026000c103401d0307960441c01071780303c00301c0020681c0c087c8012015449031a903d50441c2d4107003007141d141580c008141c83e4400c1528100741075020384040344e40d504101d01d071520b0310401880d0ba94021810b11100d10402000c40c074440040082c4001006101014040901075500041c807100c2c0464080c0a8081c91001000f144e83c1180d00d45189200d00d0388031001440d00d001100721901c9041c0c40004000010030134140c1c02031807140300600d8104103159038501080b0b100403c1c6442080103901c580b010580005059200311400d511234840749291000b40c0c81c01d40700341c2d1361001c0038039181940030036071101c1e1641049201a1489a00008200e074180300d80c000b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 953702122 1250 953700872 953700887
    0x305070207090e0102090a170d030c0c0f060209040f0c0e01050310050d1e0b010f0509060d0b06121f060b031003060914011d121c2c010f06050a0303 65
    0x3254981e07a12040d040c51603d00c207604030384e0416030261881c400640c0303400d051550310301224010300d12481002c6d5202c0801d4800e100308600c0c0129a507450001c201c0984450000d6441c050b804d91f00141c0c2044034000e0303a951407040c1c2c40d40e103622900216401c124020060a9240310b40c2002d41400b1007003081006c004900b41b510b20a607001200c0000401499040c00b410440b0201c16008414560703201040c140507412120740d04035042c040450001a440b2020b000d44c50300184c580c3c940080c5005181c0703000a0240340d0f0a0351004c405031000030205610000c85182910f4114401d84005003010180a6101c00380600b4019102c030815991450030486100c42100e4210310002c1d144c2c0313990301d4a00003000511440204c040c0082802440443c20601c224034000c02000036201551082180c000c080300804130644004000260b10030070619142201800070723010041040c0c0d03d0803c1302c1c00c480c00010650746801800c0a254000250b07040598140300c084072095000310f44203030780381c000400020358010b88 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 953703372 1250 953702122 953702129
    0x910051512180a1b150302040e0f040201020f2b0203030603070b0d020f1b01060905060d031404080d020d0f020712060f0f020c1b09070818070e07030b040c0305070207 73
    0x40c0302c034890786000b058100b000c1d00c080104290380149030103001c2c81059000c2e1058500d041c60205e43c0c01c022040640491143c1d214000000340324000003000c04461104aa038094010300607548111112164541070011710080c01d01d14030040d902c2d02c14807030140809001e484816000840c07031400c02c100029601c0b411407142c0c010103480013962542c0c52106806540c00041c140a1a980300d0300c81100e80e028a13004040e42200315842c1c401c0000d80106240a103501602c00542421207014254800710340301005c01d1010915900c00300f00000300350718104040d903220a010390141c4003103016400300400c0c03084c0314a01c00046511401d01800801c904640581c15980c0c000c2000850941c6d044c80c4c2d0001d81542c6140391629031000c0b60b038408001010400364804a100d406d0001c1c3c5800300d004000709040282e0340038000412020020784880180a00440e1540021048032102552a41e030246845411508000007944540700000300d4101801540b80b54802400c0c18411440c0005000790fa5035070511 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 953704622 1250 953703372 953703391
    0x20d0b0a0e0c18180c0a0b040303020f0a0312020a03020c030a020715170106030b011817100504080a0509060c012406300f090602090a080d27050910051512 68
    0x743c0702c035540711040141c800d1740000940910031956a42010001c250013611041e400341c026085012564100410341c00001681600d40c2554400d00340b030404000d411010035542495820800c0c015007080030005010030102e10383c000c14520b8180403044006004c941e56901c10f200c08103440d00c42e400c40403100141915024980092941001001290740c5100a1300040f0b44415180010489041c62200b5120403a9480e046075004034030642400c3c2100c0c1c04440103094640240150704440303100c0c070000c01551a008050300e0500407101241c03803c544d881581000440388054101138242903420140d00202541e0900b64003400a4122000c6143d00ba1514080e0700b089500d00d00c0c65802056000301100b9a02c040704010704152840c01134020361040b20f1044c030ae4610540001201e42002a0001d050106607413221400340e103480f00e20501f840c02018150440c03104010201d0207031140241c1070f101d440032404102c0240d142000307004810745030420121400004210594907050720300ea05941103513040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 953705872 1250 953704622 953704651
    0x20312150a120c0f05030f07093303060b09090d0809121201080c0604120b1e07050a080906060d0f020307030c060203031608070f050304020d0b0a0e0c18 67
    0x344001103900d040ca81240d0000d4500026a8050151030b080748401c1c1c50502c0b01210050ba03c40c000c1650340c0d042424002c18941c410300e010300249105800c42c3c882c6000441e80184040c400185e400d0341c90100f254445506640900100244401d43c050b0a610920036600524113007080004661180342100044041c082c892002c01c4900e0380400c01314409450080e10f2503194140c103100745a04400a00c03800b0103a00c158412080185410b0f000ca8048541d0450403a0552600340c1e60f5019442c8001c1440e031009403d151031034103515101001c80c1c8241c45650764180c3c2c410031440050907071030000d0301031000c41c0d1040040004540360800414420b941100c0c0c6a40c0e400311610000f4980030f1140c20007041ea1084520020701c507500000690f005a46c54040c0f91081c0e448540c1c00c8881140848040c000a1807403e00b900700140200d00658201d40040c0040c018200700b502c540d13104e110142c62488000b80e40c0d040d500400301c0700b4041250340c130004031405070080e0320403407154400030b5000d4102e03048800c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 953707122 1250 953705872 953705911
    0x1031218030308221e03140a0917160e010e182a04180b090616110a06060e01090b09090c1203070512071502090d08090a03020a090f0c020312 62
    0x440342510380544c0d00c90710302c0150385108499044004170031001100072400d1040a4000c058200f42925070146584d0741d480304031880d002c21542e82c00b80d00c0f442c804250040c0c1744209000301914094101a01008080403225450448110b244c000000c4c01c1000441e950214014080c402060440c0801c2c0c42a812158001104e070740c87e8400c200101c0041e500610304105034590030f03081c0da80018258013601050181d0381c0c1d25158281c85a82c00c85607079600641c00038189024034041c80f941c4411480c0e600444101030190f5840e0800c90341150400c2034501d10b144010011044140121640184151800c0c0c010b8240151010340d10440d40340380c81d2003072002181061201400b001079607200d0381c1041c11a00d4462039079200d00c007158450801514091044042a1004600742c001c840c401e42014240310001c064179286d603411038200003150780c0d20089855000015a82d40003540d005444401c00c00034200300f0204440341100c10310441d542c15508207210905d00321030400c1002c0c0c0d101140200804c1e8034201d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 953708372 1250 953707122 953707171
    0x5030307110f010224090114090a06050c0d0c1707020c0a140d05030316200c010807050c071e090b010f081902030702010b0a0801330b0301031218030308 67
    0x140040c1405205030705000317204190701820034001c14107100208948910075046104009048034020310310b60161000c000000c10a07400703d43e00c05041c442980c1090450014102900e1302e0600d0174000076404100c5a80d100035000100d81c00468500050110059800200701680c010780300c0c081a00018810210f21070f101c9144030b90459600800b0340e03599151400c04001e0400b60500b8000c0043d0a03007407000005103440d0400c800d1000581c00074540382074600011200070030000e09081c100035040c80038500030882008020085c2c040b603026001c1c01e500c80142d182012110754021160281009801051640c010202d002400b0051411a00d90340c0c5101421401440d54080106907910000802450035030650104442050807614809480d989e010100e00740c075401e0369500d5441c110117a46c041da600c14bd02c03100e400e00c1003600701142e01c0d9603200c00d8625150400d074003c0c0c0c1e680d240c2c003c02448071a8801840945808a074002035155030071620028810f100c0100b00d05000b40e01c02202c0c149148 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 953709622 1250 953708372 953708383
    0x70b0910050c0a141015050a0909020103110a0309020112090803070c03030608061003021908100b0307081501151d010f0e03010617010f0207170a091707030b0105030307110f0102 78
    0x150043d002a9404c6a0b903000c0c07039a110001804203581c2c6141c600340d00540e000c1c4450301011604000c240042090900751407000410f550a0220f0505556400c905464002480503180d240545e480006c0c15030701600000d0000c0303083c510b010b214540380100020010360640c060340d411030041d103400e05d6a805e282c50150f00400e05034021000911030750041140300e511819003802642d00c20b49280d109000b41254868800080380510741190300143c802030316035400d0f07601911428030010300311490780e6030b6020620b05009420b02100c030055955801403040b00000129140da0001c6848d00000220680218085c0108280070b07082c1000084c1c2064045070740704d01140c0c008440010020880555943c00c20411180c4c81d402207245035003802c001c010081d90510984d204140c01041050740480340125105050384603407810018405050008079450030250312401004420307100510041e801e5041007944100d0503406544030754020016000000e00c00852400800002c3e212820030f0511000180d040c039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 953710872 1250 953709622 953709643
    0x30804050f030c0d031109090604150b041202010f0f08130f0b070c0204151a0309010204080a05030d0f061203030c09150201091104140411060403060c020d02070b0910050c 75
    0x5210200c0c4002260102050340c400c544c0280d01c0030008500440010f000300d005e1a50416803000c00000000c0450400307820044101011803091980745032034100f8a0141e0b0440e400c17922803440034480f440c04550b00021040414002c03030410032100c0c3c0d0300d031130300605c0d11500030f00d40b030480680701d0385540c20030030310160260b0032551068402c90603180c0784c000100003200c009000d910403400c0084640401040401420640e51000d0841c21a24816031841c0a2688040c18600c2e5640d0b0030000010700301414082103d55600c01c602940c1d69001030303060b51041e90560105e2540140c40d2000402098070400c0000c01e01c9a410f09001c1150f5005440c00c0e1220107403035020801408804141101c030740d5066100b100e08601c1401d69901c0008450180412600e40085141c00703003000502149c0401d0150340754017400311005020780d00c2d00d5141c1d40c5810a90792191040b5015910070507a0500d00d0350182312480180c61038400303c5040607203043c0012070000080c20703580e00707005001030580c20301e010031710418800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 953712122 1250 953710872 953710903
    0x4180b040204090e0607030e15091513031d1804052a190506040513020c010c080915221b060c1b050109030605070513090b121903080405 60
    0x4440d0386107010009061030300c44e0f10a06010701c0d000034103064080e01c030304413540d5601c03001407150480004000111000103030800c050f900c10440c0e202d05d0006040b55462040204140c981d032604454600034051100c041c000c00c0281c003541a0041c01030301c0355550201c600078032156081d400d4807181030143c180f03402d1038007403603181090400b580d900705112417040e0908441a2800c414030228920307100501e5075103000b111350014080204000b40d241c080010490032030464401440d196064240d1400c44d11441010004a81803d0401c644003200b84024401c02d00b50950b00010744c40c100c81c4281c100c1c40300c0000b1000210000c0854818030100554403010401240795038010031f9100e07000500227003103290080720406180c101c3ca00810803104240c01c1124410384603962aa070440e0b450001030f11004081004205051018100e45074050300407400070030750524000b4011011006005190a034400c078036000e5401070000403038005060113420f05c841d4147c6004651134036240b13401814100d118490120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 953713372 1250 953712122 953712127
    0x3030c1704060b011205090c010e0307091503020103110306150d0207050708010b09060d05060103080304081204060f060f0b07080304030e190f0f0e15060c0a050102031009090804180b0402 82
    0x300035141d8804020104240c9400101181c5c80100e0001d50b41c2c02c0341c0d4100650090040c0300c40950007507203402900b010040607106410786411a941c2141c0280d00d841c0e1480c900d10a08000350350309449184011700000b0034683c91450040c0105907200c040c80c00c003a40c070120004406050303200f6903041e10380255001080e80d00807a540d40b0464040c01c1e24000342845880a0b00103d00c403850300c0030f03045070703115400009000715a04c0d46c4c40d07411f03a68000030010384800b0300c104110100c5081920403244285e1240c080018546603284172181212203540040c681c0c546911001d05c8484071030410b4076880765001d110380c0c1c0d40c1e0390b880c43c1c21900e818072810401d402000b5940d0340c94040c1d40d10104007098510b242c1d00388160303039500d02080d903003247c00c0d200ea09100b4855001080c01e41c241e111244054000241440b40b4000c0d40040e81880c01d0b00c1d02c0c800781d0341d50b540801400700d0f400c0d442d20010020100c183c006d000d940ba13075444044a9114070b00c41d013550050807a80c3e422015040740c02c2105c440000900454 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 953714622 1250 953713372 953713381
    0x11120709060b03010518010302010c031d09130b090102032202180709170606010f120b061902060907050612070318230f100902060f0f13080304080a03030c17 69
    0x40c0c183c000307005140c841c1d900c00204010440340e030042c036812250160368001d08403805840a0718981000c0030031140096010040e88042e88400480d14080c0040b1030300c4003c400040d060440f80c1031009000c64000307900401c00d00105400140019003524400d505008801c50b082c4001040201c0428000000780ca1034030400a01c0c030f8100465801f190b4042c1042c0d2414920504400c0e110081240d241d4007040b02c00c55032401c00c034810b00008807140d50f002000258075491000103074054000ca8030306521070300e440709032150f11a4144584c0f9080304006008080c064280400036140b03010340c01a101c004110b400c009030340f0704d2080d003015585004014100d801d06a203401e0038800b070400c0d00f1842c807c401c2d82c0c0c01d0009810344001008030030007180038050607000901c240c8403405010215016603000c40e00784402064140d01034020000c820300d00d445c16540d060b005030106024012a48420801c0d0000d00003000508000b00340c280c070855152074009039174489079806540400c0d02c908004403240c004801c10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 953715872 1250 953714622 953714639
    0x30f0f121404020102071530060305060a0c0801122a06020106050f2709010609020d1b050408060106030b2823060714030f0a03060e060d1112070906 65
    0x1e030180d4000c0e801e07070b10545d8030760f6505a03001d9500d40c1d4503c0050958a1504002d00341d004d021421008598010031401e5000c61104080c4c40061308245da85800010500062400c05d200d2410b941801d820403200c2c640c90a0104a00100c080001410100e1004a881020321032009904080c031056030285030510f80340c00d00280200308502a19014151018150070f13a0310f445ca070704ec190b500444d2000030b01d5140040c120f070034428001d4103444142d9210003001c00c2107500d40c000707810824099000001c00b04240c440000221220b5141282880302c2000144460f00f000300c3c445042d00e501e03083c0814042100e1b0003160f610b400c5d146c0c406881c400b045030308400c0308801910f884111076998840c699134002450651018500c19a41c6d1948500104400c00004140d4001000011040c2e400c0d0303410175074043c52030b040f01ea0210340e5840001f583d425040c00200003010160703800030b00070b0301d0a8161840e9a590303c52420342480e480c9204514010300b50307201d03110400c1200d0240070350f90011b00000361384d1202c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 953717122 1250 953715872 953715911
    0xb010f0f062a0c08030d150501111b030c090109021209030f0d090c030b040f06050a0203060120070b1912020903030405010503040312090825030f0f12 66
    0x5084000d80d014500266842c031440e000d1542c1055220360075400700e03120040c0b40c41c140000600f01c031402055000002c6441c4240050800107110340c2020903110403818040390a032103103800c940e0520400c1c150348400d401001445410440401240801c84407103070380000d141010100c00740780e100b22210004140e9070440d801400b00c00604419145803234440074501e940300e01420a0000d05904240700c01e14100b405a0424280940110098519242c0b2a1201880000110b8040c2e03204240344c0044401c00c0701500c00d25a11400864085007142040e400081c10803144144541200f03580c8502d540394880c050242c0ca00800c401480140d407000012500300005c0c0350b018840e0302290040070200380750fa2040c000c441c50349800402039171400f810000156056000904143c0130050b4a8a0740008030400f886507044050040f1200360300ca0039800d0100c1802c6401d41011582d01940b070091600098010b015608100503a06200c882178031600003c80c0e00703014a00c1c01d503020604006c0d85a0b04e5400318120b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 953718372 1250 953717122 953717129
    0x1205160804170c0a0b090112021c0209100e2d0405041103011d0a0611040b0a02030304060b06120604020c0a060516140c15060a080307050d0e0f011d06070b010f 70
    0x54403002003c0c0e10410583d1665440b814032882c174100540319156219100c40e140190030342d00f0060602c401e540c02d10b9180902c1c0307404904030755400038011a440c5002c0c120442c0400300d600c0c020001e400b01c0c2d80130602c043c100c80d42c01c02c1010030b240010700c402003401f42001c0025401903c03c001d5440e140c101a101c04030b0061825000c3d510702184a003a01c0c0600c010000c1c282021002040c0c01c1500340c2c0c80030014082ca91000c3c003070f504d0a120101d0859041801440c4200042d4015601d03070074903040840445c1c481c1d040c0e0301e205003010003240030115140d016103a401403085800603111100c44a00b24100942d00c0c0004154074030341000c102400e0801d0094411a6800c0c2c0e075a404030b900d11018030100d510528001c103005038005000380380f062245251060f4000d002030448010155a074001c40d2460300a124111400d8000c0b01a4503951031f80b203406000001401c031841c0c030070700c001e61001800f40c40d040d4094018000c61048690915154075048600050703000c0d02406e89903960380010210200c0502 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 953719622 1250 953718372 953718419
    0x50a120b04140406320601020a080a210203190e0c120f07061b0b0405190b060f01050405010c26040303020615030c0a051c0506090a050f0105041205160804 68
    0x22284145d0000946030b43c1c0640c0040c04d00705545510306100d40e1080c50780206428114030612041d400041c900300c003d00240d10203900d5245021981c0f51058440e26105601d05000c01d20500030024180c2e120b00a000c00c4055140d4002000410601c00a0610320f24400c115088081d129142d641101c00003102c40308840c8000944104607100c002c00c40b01c40d903000c118101019003084800010460302009640c100b0300c1101100c6880c40901000d104190420005440c0844a402002413a060840581403600d10902c2c00528003410302001a10101c60080f0240510120180a40c0420659414410308021001040342c81e40e03543d141c020340c1d4440446d500c5030030120321038008859042c0020481e000401c01440899640d00f040c06014540401240d9500b000b911741d80d0b101c4c0030545c1444990300400801015001544a0341000c518064400341c400c0002c1e032500003004046010120310a81044151510320384c0c450400c41403410b040c3d5040070190480e4000200002c525a07103041402c02c003103840c0e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 953720872 1250 953719622 953719631
    0xc0813080f100e01022a0705090a050702060603060603072319030c0b0f09010e010e12070609171b06190207030b0f060a140105120f040309080d050a120b04140406 71
    0x20f0005800e07805001c0400b203000410030004052480303c2c020038a403c1c59030404581846640383c0001c0c00c084410345500841a9941d0306001d081c0364148006c69002c3c206078010055420180c5c0441d944080c0c074031512000c0c00c05514048005603000700c2306040c03110020014221480c2c03540000a00e03000c03511007120004040c0000103501d8107803030103a600c07035032021007000d0908000c0c4005403042d030309035031807141000340780300050003140c0d0b646042e1034000d14030000400d01c69003400c1001c0e05400d03854001500c42420f20603280041c4000141e900b40540541000201441101c0d000c144140501e130103120700803410002160410343d000030460100d0b401000d039070342c05450360000c0c040a80401d94003985c211782c078004140710428849061038644403042c5030051400c0c07400184102440030039688100c0302509042800249544035141601078811070780545106805908e002d0700510030140c004042c007585280d200c500c00d6607035200d07040c036040251040c4240031103c500c10221001c101e900b2190503140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 953722122 1250 953720872 953720891
    0x50c190602190c030f0516060509010b0301050705070f110303120103030f08070c020906010815040207080702030c19030f0609080c01020702150a050d020c07080a0f11010f0c0813080f10 81
    0x14441e100003840d01501e40341c444072180001143c11f94400a80c0100c01c66940103085d000800621489200e0107001703000040000c024401c040c01d46a01921060402c0003d00510000c01d5905103c05103199001803004401d510b8000070a0a50080c080840b9a800c000c0000005268100e2080c0e850012260340340c10b09641e91600660f0300f00e801c80c3e000394112042c000000d803294010651280c00040043c0081d8020a45c8400075050b40c0c00094101d03480c0e080800c090086081c100f01e0780070406070485440d28401034100c8100f0009280344005032040b030710b40e024030b4148001940310041c0c06030010700706030fa0381408580c036501030750004000301d004204840da2070303aa072130500b810b507044903a8aa0f1018501600051100041d40000400200d14000ca141c0055180d0041160350310462090788070640c04541401e2280304000241c00250500201c20f507040d0a983d40a10884c140b10350203407165450351404084500b00c1030707080d04001100e1186d422004507070240001c00100c5035045450038000101e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 953723372 1250 953722122 953722127
    0x1006020d0206071202131e14091323070e040b0a05070e1e0a0f1d1003030309030215090c0310060e1506120f010510030c020a03050c19060219 62
    0x841e4400009005054684200a0650010400401c002d420001e8a940720000709020455551f680c0a22007081c69041041e150344d0340203481000d07000c8884080b14645001c01c940f00c071040b102c000388a43c01d0201001c107004804007228440341e2040f000c0b0348915840e5402d4106403042510306617800c00803000002e4024085001c0d00c3d11500d05643c441d0b101011000c20b22684803500403220364000e9654926141a4444ca070f0b52900401111540341e006a1401c003040700c1d985400c80540d16040390300400c0040c4003801030309490490380d241c0741c001080d100318102281800303526041110070300507413401e001c48800000780c1402ca4210071400c0c0d542014280101000721140c80c411a00101c000600203280490414510a48424054880c1c0d191900840c02c0110404080f10400101c02e030b07400043c000d50401c10802c10b000c47c40381c01c082182d1702c41004c0123991000c84034801010040000798065002e6014855032901a9030ac4500000918051900c80b000e03400c080a0318100900c1c00c0700c500700d00791 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 953724622 1250 953723372 953723383
    0x203121303110c0d03030509030409091a1311060f0c0607020604051c09050d020a0e0708010306110408060f0c040801090f0204050610050d02130f0303020a060c0f0e061806031006020d02 81
    0x4070004e01c9000380002075642079019180040c16280e441c0070074400011500c000c0d010f0440310500c81c081c003801c10100100450220000980040f9402c450100300d0030004076203088503015210201e030104d4440a50380300c492036500c9081c003100c42270f01411091020303050300001c43d64015440b0f0701c00d46027001c032100e050032201e0300851102c030006041c4007810401820b101d40c075469401d0000d003140b0000341e12082c0c0708202c0708068500000040134440108240030740d034440c400b403508441040514141c03412141c1c0f41e40d01005440094154140c1c40820b012440820440d4001c1031100f00030312030642a4207010301c4c00c80f200c4105a010700d04140004015142c00c443e80050510035450719805c3c40c00b6124207200940008030003260448102501080200d400001e820013540320b076000f00280c5503140741070400e4803040b024403c10301104100c0702d0a020740160401c10f14420580d0310b2070700d40160780135055044001c0c9a0103a000000002800790341d01c100003000e0107882280e000c44540102069040340e652 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 953725872 1250 953724622 953724643
    0x60a020c0c01050f13082808120907080f070f0e1003030c05010612080c100c050906070201020114010e180a0503030c030a0b1819020c0d03020307020312130311 70
    0xe410440c0161007560040707018000140c1110784185c2888080c091030500304c010368204040c2680190814060a031031006520181c401c0003801007171110060741c40300c50340d014400180802465072400568030b480704124810003071103000101e40400c9003004840d925451640a0703444607900a400200f40704200e1070485e0700406401000400c0c3c40d1642d1401c4440000107541110700395200e28001602c003132000350b10800207000310381460b50740300c10202c0f40f4900034802c40c40c5c8031010f04010034030045c1d681200980d5031a400968400d543c4031130520040380140144131481d2050208100007103170302c1e6070301066a48506000d030304005a42103140e0034540d642d5110381c0b00400690040002a000c0c4c00030002454100081c01404a00403e00c0c000194450105181c00482920260308012407607000a002648041e0351030b000714a030983c90207440391900200c0380c1c10001e158000010a60413031003001190584100703980b00d134025040c40750110701445200442a400564040c0c001200c2e1640440e210750103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 953727122 1250 953725872 953725897
    0xc0a06030c111f090312020d0c030f0b0a031401060b03010e06190f1404090605150406051c140717010905060604020f030f0c3916031106130602010509060a02 69
    0x1910310f0b840f02c00c009003400d44000c604002d01d0b5180b5a044d40f00500142074003031908240407410304440d01000b400c03503500d0301e08188841d081100b09120342d2541545002176079040011051082506440e69000d00350b15408030600d507400000000c4d5140881c6105170040f182250401000051240c0c0305010ba803080c01004d2102a40c4d0000300010044441541d0700c1842c060404103400c4001c2e12444100e50b01202d6045110044001c03801152516104150140104490468600d02419003a410b1a1501d00d002498004c21b418001e0000c04200060402080a00039a112606900d0489030190181d4030b01180c080c4143c0021510740d1501d40243c3d80f01c0449106683d00b10f03540c40b00084616403010f0b2590219040401c038802c9842e135078401c070f07401244250100e80740419000c950a4150680042c2e1480e580d00f20500d0f403c800c50700c10307811504990304402201e5510545400080841c41901465605c6c81c1103007500040c4980c040d00400d100d036000c24196400c5e5506c811030382d0140d00c90402c00030350 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 953728372 1250 953727122 953727163
    0x60c0c0f0807150909021606110307050a030f02040f030f03030c1b060b0a0503060c0c0708030a020618070e040605040506070c0c0b130314070e09190308090c0a06030c11 74
    0x41651030002a90320f11680c0c900000600d640c0e618000c02c03031307010b40844605035000f01c0c254001e01000e80540050103401c1070768185145414030000705540203490002040684400800c124040a90140c40c080c01c0c6d03a40c19021100d581e45041c81d009441004218046070070403c2c0c5c2d500c0903000c1c448010306400900c00c0c03c808202e156559070300610f209451590310a10500b000704032604d0402069210715a54400d1039030b105d17004804a460003603281c0c042c144d0391f40100607a8002640c04030743e281e00240d541c43c08002c0008180700b580c3c24070060350002c0e101003011104100500446030403035030099000e04141d54051721540c8040300da220844e03c001d8000101c81f6810041891241c00400404a00b0701540d04840c1e10303a5181c0c00c0c001c001c00862012640300100074000c0030300d2520b229420a00e8000107003280002615440202030b60340101030280130301c40000071448801030040d882c010070020144480365454040c05001800c100d20020001150f506500070306000008030185a0a81082400c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 953729622 1250 953728372 953728379
    0x60b03010e090f07050d0813060305010f050a080a020103020c150915060d0221010e01150509010b04031e08090301090506070206150306180708071203020d03063804060c0c0f0807 78
    0x907111081f610341c0c0e42008801c1080600e13201a201408007980d01107000c2d450070781010300a101e41e82000303202d850044800c0201002c0060341e91341166080c20050f881310b0500c0e5031181001484840100c40d406c900040200141d80030500c0e0307540b21a10008203a681d15800140903e02e0000d010003900104081030401c0307a008800b10782d211000007000003041980b0710b84045070958601941c0d4200c5508038070303414000f5141c4285514090b200488000303041500d5a1940c0701c045910132041417040300c0480d600b03024400e45204842c60b004018000b07000c0f598113403400d1030b07403042c08a031041c006001e07800110f244601c440c0d4903442c00160040040c4500d8031010300180c010960003883e610513205040d00040c0340311050050000600701c44080214051441c10042c0c10841101082010180b40070070a00c0030300340c80c04282102e2241354000c4610a60b210407006500c55100311a00d403040004240081c1c100d03030000c0322000741c3c2d200d03001c0c0102c582d503140502c0e00082518013608d6210340101d8420b1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 953730872 1250 953729622 953729629
    0x2030f0708180703050c03061e0106032a0e04420509070507121e0e01020c061803070e390a030f200a0f12060b03010e090f0705 56
    0x1140c002c0e00c0215000c41502a006480340f40c501c0c1588116081e811a0081200343c0c50b0601107554041095020030183d8070640d40401d100b89814001c641c00d0507507a03109080314a00d0345040e072034600c640301c003d0313440b81c6501c4070050480620320b05440c0c465400c042071071810088120b014100203402c00143c032000b0103007101400488034001c200d881d0000729041c00080c1036440600e0707107008038010344030f169407001541020801d000070b1a50780750621103001401c81d03941e4044003420907041c0e603d00d0004034041603900101e0601d81210b0f0850303441840801c1070760054075444440c4411100440403124002e540d880101440300003141c5600780c0c40c5100d2184c076407000621951039040c100c1b0343d4410b07400c0070804010040c1c0d0341100319410000f0782e550004104080561142c0c1c0615124126045130504001d010158623100704100701e8200a01d0f03c0c00c1280c110b00840e5240f4040e0030288052100a8a41c41801001e410921400c901190400007040c581c00020400e0800382103000042d25210b802c240c1030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 953732122 1250 953730872 953730887
    0x2070909060207050d03020c0d0c12030207030e090903040801060906030803160c140c100e150d060b0c0607022103070318020301090c2c13020117010f061202030f07 72
    0x1514442d80030849000002ca040c05800c64504081e140142c030b8548451090386481c40d5a4140c0d4244400c803054070f004035a050886283c003540f24600540d486800713240450380d603503500c900e45401042080501c0748400780400540f050f50300103002002019034034800c0600f91141b42c80b010700300c0788040020401401910030305101d00350752420400c000c10555a943c44c0080d03c0c0c5207920b142c9802419015030701c0d1410328501c00d8200224a000b00e1802c2d4150005075511008007540034030950300181041400c4c1b80b64101e10002c00c0400c1c1035946031011409007588900c5c0444002c001401001c0340a030005682c00b02d42950b0f244040f80b858107551b14420300354002d02a0040c184901400e002d0101c00507502409001800c3e0b11401018020600d8185481a03d42a008075055401c41c420380070100b1160310030500380e100448180c40c0c80402a03a00068131450907040c0082492800c100c008170381c400c00816204112103441e5560948440703820300c448200d0200703960040c515441c00380400c501038401d140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 953733372 1250 953732122 953732141
    0x3060b0f09010908060c040819020f0d020a150801030c0906080a060c02330105030616030b06042c07050f0708090a090204082103040c0b1b010f2703020709 68
    0x1008070003682c0f5022a10b14010040341c00524244c400202400303032384010701c1494041c02440554000a2010364005144403c0c040340b00c82c0603011410110b01507540c3c8005d514010b00c052241c003036038448407080c01025007500f400240c1c2c100c1407000001507034136094072881040316210000340118801503940d42c8094094094481e00b18451492421701d10340c081c810b42c0494522920380c052000710001c0c00911004016844188030b50440000c004c110144881510036408a601e00000c0418090b400540301e8003490300301450591444238440c240d08403101070040207804481c0a20340079503c0143c201c1c0d09110743c800d00b2851060900001c0d00081a01024010802004000ba1706040e19201200102d03000b540c09140954086d020981c8203c50a8015803401181f6400440c510314142c2c07a160f80030413583c400d003c201d0000041c400b071b00f0744540c1c040d07442801456009004002c10200300e10080c1c00d103000b8503028450040b10116903c02415404400305516402404c45d07180340c030a921005103040207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 953734622 1250 953733372 953733377
    0x150c03020705220f0c050f0a0215091e030304051506010c060f0b130504120e130e0606090f090c0f01110609060426040302040f0b0316031203060b0f0901 67
    0x81d0125003a0b580714106000041000202000800e8400300c0e4010358228003401541586840f032a480c003280c0c450304403105c00410240e40c9542c0d0b1100c2d00224039045e001c1d00b03861207000c0c414042c44414100401e004c20240702c858004000e5464064101e52a440140c0d0000c2c055070005a614228141c0c0c0f100303c56012105041100388000b594a038001030300c03101155130400f60341c0c68107012168076242280e02a0889801c00400852400c2d9551500116150390400148171461310400340300e540384901c0d1100202141e0b414420b03075803480c080030760310300d000c2d9245440ba07030b480d4000030300030241603060078454040340009104400b542c3e0140f00700304000079807840c100700600c0c0f00013214400c10040b25018040f01d000600040c0740a0925549165015040c07031100802041005854052030302580c00b640e030129000250302c0760301c40607030008240030544240c05004100142501400c80000c240c00c4034061100c8440b05c10f4680380c11000c940c1607000e4447c14400c244240103440c0c96000c0038000c62074060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 953735872 1250 953734622 953734633
    0x504020f0d020403260f1206011b210e130f06170102070201030f05160c0c122001031b080c04090509010b0f01080108190f1b031509080a2607030c02060907150c0302 72
    0x424200041c11030035007500c10b600b150b289114130f5600e80c004002f00c0c0c0f02524000801081c0040043c20008130103030344849880e101c603286010200f0b181d10010090070100035070a8a02801ca2030540030707400c10b44007a8042031038150300305404401405124802c0d400c07003d0b01d00e811807a803803040d2100002603070151207480f415a07008c2462000748a0400e45603010700703a00700d140d281030b001d41d451a1503003608060425080c072440c02c400380f00b036500e04000c1461034101a106035844c0c0c070344501107000356031003092803a044c94180702440c00c040d8004180400161a03c8440403e2000103450420b003c4c403410140354403224115003038020746540000d100d4840d8504102d03407441d07900c80070791402404007110500303406802c04208011004600c00d5032124140ea0a0140e4015622408210b005500c040414480c1e04842052410b40c5d00c2c41e60110038a2490903402d203800c010100a008005101826001d031040382d0204480e6400014010225650185105202c1100e0a41103030343d00c000c08412001d41c07089 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 953737122 1250 953735872 953735897
    0xe10030b090a12020c0918120f0d1e05150901140f040c0314070f050a031d0d26060303090411041211090106030b03070504020f0d020403260f120601 65
    0x91620000f41d1070b0781ca50007040010b0400080041d2900013900070610000c1201e0301800e000404a80c0c1d59425004090340e070b8503400302c09400035141c0b00d0781800b885030030329244103250380707190a1141c4508595030a40400c015a2000c520002515140035019400600700700100404030705420040040600544074009494110002c50255a42e018546c03010036110303103448460000b1031b4040c680c486c03c13620b0400451310603050094418410054400700300350715031859080741803804440701d5a4101850403144444001c040082080340785840c200310300c0d1151030500611000c2d40f5a102d000b103034020080d40c40c001e0103408101c0102882103500b42c0050f400e100001d0500811080d1501035401008200d02e00e5001200700840c10605802800a040c900900c1031680c0e1000101141560001c0d0f60060b610358446852448501820300c0600d4024000200441003191a0742c6003102001c0c00b00f8402c02c025501e03550b000c02ca0040038613203840301c4018403500c0300186500c0545a042101070400d5141d5040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 953738372 1250 953737122 953737133
    0x50d020f040c0c0b130605060105070c0e07090302210c061315030b09040f03021e0a0f0303060902041e0503030307020d0e041b05130608092a030618070e10030b090a 72
    0x403c98129400c0a61700c0441d009004c842e005072548040c00746031051600d0b0b4a80c5d030740c1c820f41c0f086029460f542c0c952400014100e41c080c4504c8000340d40c005100386402e842d540320b03145001d280d5000d01c064901a4111040ad1401c01c0340a40d036249a44900c0c1c0e0450b03501b803400d51801402c100b2031803410180c499106e40d0145c0c45141006015602910142400c0310b0103050203850041c50707581402d04206070809160007003c010075907010352075000003004a501e07131a080482c05040306401c45019184005000134050a00784401030280185540744820140e0307034001c050710b03804125141005a0030640502c1d0819104078441e002641000b0310000c1e540c0104807501088a00c00704280d40424400241d0490030507462100d00d0040c0a00d15121b021450103800e02e50300c90070b445031025015580305020102d080d405442642c0300100141c00c8440e41e1400503003d42c2403c88400340c141441c000c0c500042000217955114501c030301103103010591514915a6484105c003002010602c06028503a9000c00103039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 953739622 1250 953738372 953738393
    0x180506030c330712050307110105181c020c0625060c121b1d10020d090617071b020d2604080a0602070302071809030801050d020f040c0c 60
    0x3810312040142e012030007070082000405a14015450009100040000b0701c1c949204100c0c600900d09030752030f900d420009480040d008031304502d0b554206010081d0001c062581100d81d032460f081114006100203445218009203418400010303007005132a040c49041c00001070045003e03640f0a0002d080b244007141c90b040d407502c1c400b2070786181c079542060003c55010900340201c10340d0b40030411900c6110020000c0f038000c0d004840050281040d02e4285403031222540e07103030080018001f00d640f4141110001e486605403a40d02c004501703100030119005100d80c11812020007081d10010188e107602100f070718218004209236400500003030500e00162140300308644038512600201c5c0d042561080c07071405035016100030340c8400e8000d0004001000e00011414070040d000000144d07107054504080b81801c0140d04144400104524129030320340bc281d10000e8070a000350340d1412166214010803182e140030a6001e540115008840c08040c541a0301c403491240c60360820020100513560381c0c2c488030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 953740872 1250 953739622 953739649
    0xf02061e03100b0a08190204030602131e030f08090a150801080c1005030402190f1d060d12080a241509050d1104020904090605160504180506030c 64
    0x14800071080c0601d400e01200301101400010880c141400084040109a21070051520258852418211094640340d5040350302558101c013040d076482840740c00315418401c0c2845880b0f00560001c000384007042c031012002041d40c0c3c0c814031401c1e65010390f490320741072900301c90480d9500c240c07202400030b007402c4030007901410b06000d0744403501c0e07942c50405020304240005c0b400e20300440f41c0400300e020302c80d8014103c0b980036a044809009041c54844489803406080e003241c6e80c046091000401c400f00d10580b03461840711641141d0500c2d42c4c1c9c0c1014032a03a4008040b0090012549601d002c02c814060841241c1c4011102c400080010034160002c0c9101444407840e403104038200c40038080c05242c1a218212030015040c006202850140422a206d4400c1d03c00b903ca882d483c1c080202a41d0b035601254041c40c0000c00500a134900e505086008110950f020518040441c0c4070202090007a8251401c4a04000d10071410f075800f05400c0e4042d100c024071580d8076024814050142c3d17950b01c101020032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 953742122 1250 953740872 953740927
    0x30f0501091e0c051c0f140a05060f060d02030601020c0a172b05070f0f11040f110f0714030d060305060705040302030304050d0201050d05150315130f0206 68
    0x71880c80e00080c41030508010b00c942c04003801c002c49845407a0700a022a403440c421a2007110300303180340540c0c3e8801040d2005000d020141858240c0c14228103612451340203202000b001c121a0b10341c8401c10650781c02e600981e41e00001305025815169049d0f50245a0210060064400700c0d41d04d0300c00611195603a0300b180c41ca1101184009250840402c580840e4125501001e5940740c801000002c0c05107824a21074200600007902c2c0e02005000740600d40d006034041284410b518407841c100c29140c544000c0540524a81086d10084004038000d0020076054003407014582004441e103642c4a6010a00036100d0300b1407003201d207480d89800c000400d901d03184e003580000c0e228114a8400c1c100400944041d04200042c0801d101680d0301000315821030b642265820342d890090310050316140500071110381800d150004100b50321102c10015081003400310240d400680c04404801292304d0140c0342e07064010700840544000440f5158010303001400248003604180035100e0b00000095140d849614 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 953743372 1250 953742122 953742131
    0x803131406241809030d020a0504061d0d03080a1503050a11030d080a050423010906200306040221150f090903070b060a050406140f09010308041203030f050109 70
    0xb0300202501c003104042004000800c0e40d003000000281090348407001c4200704480b890100d540d4500400449408440e0050306540329100f00c00c0107400d54220344540c0b000301c1c03004002e81207154400c2101ca4041c0a00416004542110392030449103150b00405440465594509280340e8103100c00c0b0880065100b0300c01400000d06510b8510030400100e02d1a074066807100c8241000141c0044c0702d80c0e4007410362000041c0030303940c0381060f4040114050581c001c000e00440800011b0304103400200304d8501410090004070340404240645980d001c816481000060002c110346180c290018039042008036051210400451420740202c1010b40d2002c11103050300130349501c1b41c10111038212a044040780c800c0445c2c40c01c00c0071942c0320710560400501c2e110415000452030f654050b804805044054001c000c02030701ca0044125000c100707607410384151400e00e521881464100c0f00181a0703a4000c0c48241002d1406516070740e86100c18500b00c0924de1146445024041503109950007041c41003400308 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 953744622 1250 953743372 953743381
    0x903010f061d010e07050703020312040302030a0212030c040b070206041d1b030c0a0c03200d030f050402030d11010b06030a050f151011100c0206090706090e01030803131406 76
    0x401c0c000c03030000300e0006904820041005088130380c01a80d1210341810040ea6803032075840c00300c2c00c0d8483c40c4181d03448840b11100f40814183d002016200070343c80d5808854160100f03c8048815000031075450301c0c03601d000c000500950320500090310206101510542c2044d484148101000c002d40005422813000340d810041180385841501a00c3c00c80450701520b0342c00d019601750810f00c070300d140c0794007885105207481007003501c0b609002034a09911041c18041e145420300c184d0f114050303807021000107130a0410405c0101818070920b4022940140101740c0540915425600504074a01e2605195a142d626038481d8980e00c004520440156200061a1900c4515104a82d0029054030440f414110400c02103460f00102c10406815504100d0210070807200d203240381480507008010306030b0615548154058001817801c2c05580c4420070b40d114107407114001c0f07401c96858070a8401d07200480340100041130b0018015030b005601e40340c804900e02c1081c1c43c2c01582c9007410f10031507013540c0180e0410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 953745872 1250 953744622 953744639
    0x1e0111070b190f0504030b24031e160e01030201080711010905033006090a0f020c03040504141e0601090b1204030914030a08030916030b1f06230903010f06 68
    0x2e25040c01c3c181030903810b0504640712a00352481c0240300e01146d5209400c10314030b038407407134030010b0b0340d12402000c9400103841c00c0320a003815074040c0f1858219100e0f030700380c0820180b01c60000c40706071840396801c10701903032031500112091500944808207002010034166980e640038010308010074042c0d0019503452078002e205419907a145040f4449402c071402d10711080c42e04004031190814000c071104281c9031501c0601f84010943c1d00da5615000f4030026900b0303078003179011001e04115441140c04001118807444a5072110388112000b5003c460708496040406011480e000d402100600d880b1042545411a80c450f681c00850340c0000c5510450400c010103521850f0300000c0c08071005480c5440301a40d02103940d8100d8024000e00e8002c01100080d0f14081c1000791040255040041260055072402c10703502006050303905255100501c41c2e010340341e16010410b1011203602e40d40b0510314a6401c0c2100b604d4280c0347d40e01006842c0108a801700c5aa0240100c80700e0620000000860303600e010640d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 953747122 1250 953745872 953745887
    0x815180702070f1508060d03030f0603030801090501050d0b1306090b1905010b0c07031401140112060b01030c080609060112020f091306030809060708090d03050909061e0111070b19 79
    0x3015a04088038030040040c2d4072441c11a002981501c0940440c847c500e01074014002c0e0b4003410849610b04a000402d140d0b0101c11107040703c11801c0b0800c51647c071103081c00781072100c110026040c1c01e6020b010480c0703405214202480030b4000c040006481c0c0259541030f52881c001d4031042c13540c250f000b40c2c46030002d880e817160900402858064a2501900303c030160348544461101520b24052101001c3c8844820740080420032841d400d41c206a45c1c4645a0070f540d50113114050703e4080c80d204015200e0350203807050341c1c403e10654441c44400d580310000c02200050003491241008100f00103101819802e0011b4100c6444103215603885184140600010014903403529400c642408000c001054080c0d0844046103000c0da2007a070385039814244441207109072110305400c00c1100f4140b03803d00da40200070f0032003401c00b26040c040940307841d020000c030a400d80c2c00d1307180d000030310180d00420b44d030140d038901181030711030320544000b26a0748a101110780c2201c50304d00c0d0014500c0601000d00d540c4200f8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 953748372 1250 953747122 953747129
    0x308160203120c011d1c17041b06170c0904021c0e011107170a0903050703080a320a0c02130b09060312030f0a0902040c0c0308010801020405010815180702070f 70
    0x4085803603c00080410f548825900040795210503840c005403100f8402c170040384d1994035051f41c55001c2d08040c5421915128004100002e40100240115215209000c648510804008002d050340c07070701405028564840c4c0503c990083e0b08000301c80d858007110b503078011407031400c203000244210104081c500b501d200070080040c2980400000c400124001c1304421810740c100584d5484608122090301d425071581c001400c1d03440b4030a000810020322600421012089580b4004a5a400e00741a5800d0b038101941c2200e04200c0c11512480e9196100504401025450300c6900da090a4000c03480ca41c0314240f1070100305480304c0c2102403d0601680140d0010016401015185034420203a1240e00010b401c1002c42c403040000f00c1ca40e0003d54100300140b9030001c200700159a0611400b41034414420400c9000c13940950000810400c1032007a1022500103850b0300101b980e40070421a058503800f01300c1e40c2e002e90000020109000b0106c8418401c1070f55400070041d850824030213900018490b407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 953749622 1250 953748372 953748401
    0x16051c02101d030a0b0406021e120420030d0c11060d0504060c050c060414071a09040e01061a03190e150c04150e0301060e070c0c1a03010308160203120c01 68
    0x2400c8000584400107513502a03044000180c03142101d481409941607440607142c4241408030b560072225110f440c5c100d0103184561001644070402d80e00c140c5040ce40894000e41c940c101d442025207050103540641590f0384144024007110030010002181e075000400c9420185507134108100400c2080e200f00c02011096041031414201407405140d41c44c140240000c0c95804c8028a079030707052000300064806444c070a800802240c03958207076500c3c1030b0000001d043c45141071424a47e8001302c18400c240c15542c5910f402c01100071083d16402080c0d04c00303003101020051100d00022a19400d10503954000e10007806804002003802291010460103070005299a000300300400610b0349a2800b8400c5541c2c83c10400318103480d00d40040c1c014450783c2e20030007000300004100400039a104c2882d000e00d5200c0ca000c0489251500c444034610100c0d050020440141080180046000440a000404ea103c2645824107402c2c0e40841e003043c034046c070b90796001d010104404a02010a0107150711000060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 953750872 1250 953749622 953749633
    0x70b090109080910020f12030402010806011e140c0d02010605190b030703050405010216060b0a06050708040501051b0706020604060501051c200405161116051c02101d03 74
    0xc2c0c03112001c0d4840c05441074460348032500406101c50003800300c0ea00d8090301c00b0503240286006900c9828a80c001c840490006a21100003125036003e0000c01000e03001c25400403c0300d0000c0881075601551a4503102e68122050104d44040c00c000c015048520f41180d0000c500c492500c070910500850a01e8074603480d69484a050140400c01c406582d40261245000304180e103860814038024419501e161800e490b0302e009031014044950484851080240c0c0c15101003035884200f1500e9021300c003401440311404000c10841584a200a40807400000c88003090480000e180d00d03242601c941e1000001d0380000c000c10040c8481e600c100303401020280d03000e480402400c00c103000001102038000b4016410002001c3d20003540103400105031002a10800060504034a41402500801200000507429518405440c440400c8802e9031203d020740707514819041404003c0140c210f1389060f070450b0310006c0d0440250343c3c0c0165030440c8506a85030300303a01c002d404c8940455a6085031039030f4020387c000e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 953752122 1250 953750872 953750891
    0xd050c0a060f0603022106011e052403040501050a1b020d0f05090d06051b0412030c060207151b020111090d020d06060b1b1b04051e0c070b0901 63
    0x100d4800490360340880300082c030400b4011104010900c0350000380d0001d418000340800d82d003034545070880f20680e10044030441c0c1e80c1e41c072000030700c00701d40e41d504042c03104001c1c0c0030440c5043c04400d4180e6009030400e000030404018008400b2504201ca091324943e44840500140f002c0502c50201242511a080e6151047c841c00180d59214102d000d402006043c0c5140c3c0500c80c403c0c0180c8201d400020703e42c1c1c03919200707400c181c8080c08096609601840d042008034402c43c040008490441e0810030f14505400300035102a9141e014016041e94090780801c695000113802504440f840d0030b083d04002a0100054202d2040244440c102c20541e803504071400380c155000020340741e18040c110784071001c02007503202107402041c4440004201904050b00824504100c001a080e200855002414566203040c1d40c1d40c0e40310460107443e50442000f010114290820741c0249034851040d102c01104401100c108400c1c04808a4403140340d00d402148060801002c2208103404c070344510028481c4269 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 953753372 1250 953752122 953752147
    0x30e010509060415110d02031809090c013501060f021506060c01020d020a080106140406120908120f070f09150f0207030503072402030f04030f030e03041203020d05 72
    0xd5020781a940a50b50000d00213540c46a200148410000702c15210004101c890280d5030340c200e602044c900e86142c1e001d2100e00e06000303654512507c2100700070954140040b00550308030b00d0703d00000d80c80140500828000c08030594000107400b0710780150014541c07604034000c1410658401000454100c10a42c0c0b030312210001a96401c0403081307502035a250103054080b4020720400c0c0030206264004180264540e03000100d550482c1da10b5202c0c80c540d241415000d040c544501c1c014500441c02031802c80d141c8106960041b00018400c01e084d0349806c000c40306038054010100d5140e605001c8100400018640c050215086041c040c100300c030003e03061045000100c02c43c00500410059500c0c00c0e180000d2080117000c0c000c54202007500da4a00c640d0038552680a8a07142500010803001802c3c00411024170849101701104950202180c6031070784d045501c258800b050104160301c501c0004221071052000f0002070003003000c80c41e40340c003562501030700b1310340300007000018803a081c004e0005146 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 953754622 1250 953753372 953753377
    0x120503041a0403030e180609191d06070f1e03061805090d0221030703021b010614010503060f040e010b030d0e10090e0130061d1915060305011404030e01050906 70
    0x11003c0303d1402382550b902c9d5503810032202a0403c200d01d6800c18140710034400341401c0683c10a018107003928401d42e00c01c0b43c03e6654a02140d80300e8006640d800c10752041000b02007042c0c40700013031445d002c9041951000445003481e10140c030b2141080ea03030820b02103010b00c204910742c1e00311702900203414040c400300c0818030031a1001d0700b1460305120000018081600c00d9040303403d44003030b0401c43c52070444440c41280c002c1003540100000c10141d0750042c07000e503016405992040900a01c0b061400c02c0070000d2201034a04540089031035900c96048011aa40502504680c20030540d00d040105000c1d40401101d0800020f40505109860806200150b07205070340d24195821300340c0e408012201070b00404280d00d4410411049a403489250743c3c02c111050b040303214441411100d105945001c05407140e2100549644e000c101000405c5050002d0440c807060516000c0303900d0001901c0760350351100c60a589500c41c03119050034501040004040e040240c20404008c20700c0e00ca401c021040001c180b151 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 953755872 1250 953754622 953754631
    0x150c0c180f2c0118051f2a021c0c0605010f03080406050315040603030c020909070f050d060e07090b090f15120c15030a0f090507120503041a0403030e18 67
    0xc80c14049460510004d4010004800c10040841d041101c9411302586400e44800b0711400b507415503208400f811154050001c0d80720076924081007a40c6e4150f00445c840310004804001d40c0561315044290403c4400c100a590545865984031605035107800d0048600503002908600c94241c030900100320f0b484260307410369040d8280a90341792280340b00c14a1100607040540c0d8000e00301000401010340c0101259405032080c0c5403243c1d55201d2040c00c94440f0745034061b80d0b00244111004005e68640840d40100c03160003000c00054043d2130048107070078524036400502c107041d20b400b400381242c1800380c0b8007584071101c040d55040c141002c40703101d4240c03a0b601950600c56010544080c2c0010800d02c020b0300c91200091a0129100000c2c14101180d04215040d17a201c0789441140c00c6000c07518042d001c980399000014200c1503040045400140070b81c0b41c0c0540312031205000100301c090801c03000702403211501c40c01135110b42ca140f07401451900c3c8005d4041c007850800c82e0300c41011a11901d0586c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 953757122 1250 953755872 953755931
    0x9150d1b0b25020d0b04050307110303070302250803040b0c0715080c070611190801060f120914071206060f03020d06110c1207020301050105030604020a150c0c180f 72
    0x526034500000c4c040b80741036800038014010080510007040400001400014400e42002000000140415840780a050400350150b0020001d0030444812100c1c03140d103052000600142c640c3e25906a54a1900240c01c0a0007402002a0300000c0c0041003158000a20640008104810b40e1100041041c84090700089104038045101c0040040d240c104a40001d51800d006171100040c5040316840003000180f64045a07500c2c001040c4a4851604045032100e96283c440d80c60080800d850000d008055080e614181c124440308000801400203200030203016070b003403000403094240001140e44660200c0441d810140041005880d6200d080a50799040840015013401c44083c001442c03040c4e6040d480207004400c040e29501d0013070f00c050646107000b40c00801190380c942007410303540e490035074019602c050004000c118502c182c1000110080301031800180040240c0c0d42c408058060b500070700c00148140207280000d0131284103491700d19071070007014042451707a0060036940f02d00084c5400c06 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 953758372 1250 953757122 953757187
    0x101a1521060348090c03060f2d18010f0e0c0a0f03150305010203010f0806100308030f040515010f2d0510140d0c020d030b03070509150d1b0b 62
    0x45000c0d03842484022070003400d40c80b424541041c2c01e082c903510442d0b58501c150025402310303040b0f051401040c0282084203008903245000b4844400b0760910280c03c00e60f114018180d400610590581d000d0300a0000c0c1c2c11199200d42444001000700e00300a120f648041c1c014000410940ea0003106001079800d54100065501c0c2d0724000440c01c1d0f1110380018103658000400040c00c11f008107040350403220040300307460a9840c0d141181c0a035007003910016049800900110b00080b02800c40c00760414452000c81d01000728080c04000c10080907400850601243d81c2e003040f80c140040074110f01984041a10b01c0c115000022211507001c45009050017039459040640056019903050398a03451040a250340fa90940d4444001500c0f640320340034018000c602d03034007070803034040e00038015a000004c3c0540700940c113010a0040c24840100142101e101c0c20055010300e884240c10140c40c54040c542c000c807010444c1100c4814aa0164040590307070308200890824402161f01b160354003510828080c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 953759622 1250 953758372 953758483
    0xf050c0d0c0819020d030f050c0d050c04080a0317090a05100f0608030315181302090a2702040510050102060a020d1d070305101a15210603 61
    0x94040c0078403c0e941418000c600d000c50100c0c0e400141003243c03448281ea050004c1580c4500c00320035607600b80e4181ca5801404d004441c0350401603041558030402c0780b00c0302ca051958804060b460111107160039404108100300700494806003c440a50005110000388450340b80c40d074400342d4604c0c43c4086054180c0d41c0d443c07408540b5420b90400750040902c1d408490302d0b8100b03000c030196901008203005200b0100381c028040c0003140083ca00c2d00c952000000d5540340d803040d07000d01c9108000144003a0301b0315503071480090594224040015034101100003042e601e08584103000c2120400751503180b081c1a030741d03810041d981c0d00113840c950003826881e0160303d4202d01c0803c81c0242c036440b0000c82100580981d12000c0360000140042128000c10032204420074580e40c20003280e0b079585440a100c034030b400d0801c07443c2c2008a010424a000381d50014074042103100e0b544071440410203070300d40044040082c0516850b04010407200108072041510a1107100c0240750543c0c01c80c0410020140304500e84103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 953760872 1250 953759622 953759633
    0x913050c030106030503130801140c0a0903020901060e10082e0b03010605030f060f010e0d0c1a181504262b030903020c2b11010f050c0d0c 61
    0xc103084401400902c0441c3d200e00d4569125040700000280d2002c58420000d0b0244050040c5100181000348440329500c1c0c41402c444a030340160b441006104100c85c0020040c2c559910003402003645988215845a001c01084110910358800c00c0800240900740407200c550200a103034510403940b410b01d03521110b087d240007000081d500074009124080000108076030040010343c4200d100100f800a10713554403041011101c0d030ba0003140d0006e89a000d180740281000354204541c9c42c000c00d0b804c00d1150b40c1c0c01b07060380d0796024424030200b0000d01103125003032000602404180c100003110860500c08420300c08880c03500444c4660008410980203a0080c0003214a0300400c0506110540b5182800603051584049220b010303010041e94040c260040303240f2074030030400e20b207600d68050f044499004c0100301d0650103c0440d001c04080c2010410301c928a07401000c007003640718104410403903403143c00142003100106440e1081c0002045040b00b11140410320021080300c2d41040900c0074081e0500c0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 953762122 1250 953760872 953760883
    0xc090c0f0c0a050102070305030f2811270111030f180d080d06030b01080d231b0604050d08090a060c03140a0e06180712050a08040303080f0c09091305 66
    0xf40240d4800261201856480341c000c5105204114501180b0f40301c0b080c41c040043c2844103105214055420b480c0e00c0c0a9080d00090520000060b00c1801d03c14003178840c010440343c614002d2303480810030050080300e580050080307880412810195081666502240b00a8440c035100b420441d08801c40100c265035410180c1480281c00c65442c41e00c038502ca180b41c10003400c150206a40405010f0700008014600040700442090079030380340350200c1032020948a0b400e10000d00141720030700a100c510110b0014070709600084018500504507410309003001030a0130403c202c8041088550000c0099074080003036814815644500c0002d40d802400800714010480b4103002c4581654080a002010307003a60000031618215800369207107902c58441034201e0540d608480f8586410138002086000e40c00142100d08501900640b00c41a40a07607900140b0b03402500100c02103680e1506102d1108645001d071588080300310701345854030f20048005403440400400b01254200c1420312641000f005024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 953763372 1250 953762122 953762143
    0x150618090227091209100c0501060510020102041508070f0c02040209220e160e09030c1606090f0b09040b2d030f070302010c0b040812010e010302030c090c0f0c 70
    0x28141c04003041030103600b40042c001d4407000000d12030301c0c00d081800c1c00d144003161840c0400401b40414000d4240042e01c41e140000400d81f40755695440001b41ca448800024100b511103500060307079142420000c8207040b03608000750003080540002c03c02c5564102d0303a80030051805061400b040051840020064410328491680104410100c400c42803802e000d61940710350b4100d0148103800903c3c803013a50340c44101070704214824589100f0441080580c0140742c00c242c800055918001700417145528100c66090009103189a01c001040056030291a05020340b00740306c84614000e140c101540498025000c49a118984e510702c48801d5a6031000045c0ca00700c604480602c010684800c1c2c20b0114042c0740000c1e0081c054006e168054080115240c0140c0382e0584075031304030754600d45036050084c400806c01c0f20341c4078040040ba8240b115103480940280810302c007c02c107960440c4107040c00d005403403030418002d1072007400380304100060314256904040b03200840da403a84840e928440c40c3c02a40c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 953764622 1250 953763372 953763409
    0x1e0a020423040f0506091f0b21100e1501110109080a0f030504122a0c060f02060405060601120b040203040c030b013c030204181506180902 61
    0x10a05401e50141c2070030850200312001c119040c006041141664021648158096030443c009001d801112111a4108a104074603011842e1a8801d085056200e100d801ca200d040e404080450f050b00c5031051a0311208581c59400d9680c0b41c16489066890702410544c10541d04000700388059103e544040c41408403c002031202441c9070402a0103644554404000510110510001140680070b61400341c0e6022200308007140316540211f0f605450b0100310210320845110907090400ca0100700202036009038005180e41c0e15001d40600300d4900b0302e5170001550480010040880c0012031810b90106013070900015800160308104010001c0095032640315102005000038803900181940c00d0741d202e06550a03241c2d89880c0c2c1300d080341401003141f454200324280d440104c110200c0d04500c00b5507a101d455100340c0c0d1031780e000805a400503501c1901100124001100b8040c032060b003004135644c0168204400ca0a1500c600294000c5143c2011100c1e16041070600b151601c2d101050102e4254 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 953765872 1250 953764622 953764649
    0x20d0e06030a180303050a1b0c1103120408011401053304090606031d010b0307030f020a0b0f18040e07030308250914011d1309171c051e0a0204 63
    0x1413030050700401007504c038504114a00310191205000383c0c015600768800e50388580c2c0321304045036181410400e42d0202d060b054003805004800c0c0300280c801410107041d40070008540d640d52500307407a81641c816032010b44039418004030591401c181000c030803090b520154140742191001a1504a41d107d194041c460540c542580028800d915a101d90904c0c4c0d03d045161001d900b076817034a41c0c01e9407092640698560400102080050b03c440611944a480a00701003901659400043d526401116080c04c0072000000c1c5034480c00440d50120803445822181004042c03282c0c003005039245041d010080038000d005010840704000c1030304240c2c1d040c1c5003681c135092801041c1c1740201109034500c40c40540981c1c105948060b50300820910101148607401040c9801451003040300d603050401e1005100c503911003883e0f01250000c51602c400c00014005c007a9940340340b1205800e01646c00c1507030035580f803030702081c001c06194841410750062040c8969443c030303031261301c011002407085a1154a924040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 953767122 1250 953765872 953765921
    0x280605300d020a03030509030c0607200a11040b01090e06150705060106110d11060a020a1106090606010905093706260f070302010f1106010306060f0501020d0e06030a 73
    0xc2c2c0c0e800d20901c285d03820703c80782d103c10030040d6403409210f4400d180b507080800001d00440c0700c4c9120080803a803841441c482e24400c902c04905061413184260b95200300000e50840909090003650b0101c1403c0ca012808140b404603518800203007d80601e2140b010708628025010084041c1c4402d690000255255541e40704406001210034110ba89820702034114145080750080c0307140c440b0001e0f40d4001d454aa900c6100500095001200ac141845541c05405c0d102250421400f0311070f0344060010b215509003100090b0105030641d10a07880ba5105404000c1c98a029410442c000c0d80811068448449417541030007032400015a42c4103c41c0c07808100041c2907004e030741400c1c1071080002610180b003107505481900e851104004622952100c0000c10055114241955000d00e846ca8820542d00c002d858050806a081c2c1c415500c558841c1c00900201091190380c1000f00300c00d0000b0951038000d0072001d05003014044ca01ea02c00d01000c80000c44141e9684c011032030312070207540f0a0f47c0f200e84 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 953768372 1250 953767122 953767127
    0x2a1b01050f12090606060a020a061509050405061812090f0a03080c0105040201170108060f041b080601080d02070608130602041508070f030b0f060f090306280605300d 73
    0x811107a0200130f10841000c508541000c0c4112508441240d000c0c0410b80c14940354500600407282541064000c885400141c41e0f95501c03542d40100d200b403000e0181400e20b080310303a1800210b401c035807001d5003080d8600e00c5110b00c0301c41150441c007410f5031880902c0c0400800580e041c6a10307800a0642c038000559001500410361046120318400d8913030500b40515044076056a8500340501c410316849800440c1007244e9450480b544036201c0c03c403031110445203c03440f003009500d540c00411258001401030100d00420302c011101c40703000744024210107182610050485c0409080341d143d808040000c0024000941c045502510440514556064000070002c00041048941c8000600c801c41d0003d4020301c6406158040740000f02480c0d404c10b5041b08002540d400030700b0318000a8810840c00140c0d403418086148a01c4034501c2844085580140d2440031051200101104516243d014081691050085000c03900455403000350540d0b406104102c42d6149079484000b44500914020204d5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 953769622 1250 953768372 953768407
    0xa020a0302010624110f0f0706020c030312070f0903020303070c0e0609100605130906141203030702030318010b040f020d0614152d2a1b01050f 63
    0x51203076008001c499902c070541c464905070076619a03006010150300514181c4134104140d0100703010360540300d4594908034420300d440d41c070741c02c0700459810102d002c100b4241c050003414a5108140c001d075242c9005464010301a0f00002c040d1818880600545e10544c0c0c410304640000e16405802c503580d0f10054200104420301d43e2142440000d00c95000883c6420140c0040c3d0180913103106c15503d4904240c0103880e5074001c00c17072514000d621030100150110036401004020040c025082c440500c501042c0711050103001038a6500340c0c01003060108a9071f00100310396009020180c2c031024503446009081c0500480d40c2200d60180c100295070300107031065401406001a044410801e0f2652403480c2000c0c4400100306550044c2e0115000d007003003d61500070940e1840149402c1c0c180d611003e003078003100011f02d554901d40007002c100541c0d004030344011045400c40f480200314400002c400c25542e00e0544004c0e111030f003000c800300d840690b40a502641d40003036000c42078540b103001c0c2454000d11403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 953770872 1250 953769622 953769643
    0x210c0804032003011401051c08031608070804051b06041e0801061a07060b0607020d060207030807090b03270f0a061803091502120d0b01110616081503030a02 69
    0x8004502c0421014941403081c418500c089401803491030f0300e44405c000b803503100302d000c07145c080413150104d000003410000150b110343c0d200840003c10401161000707025a030300030700740c0050140c42001d001c0810300020740c1121107403449030b036402516850008501213000310b13800508050088056025824506480441940c0001008101c601c2d969891501c8004035030303280d41c000c50f00410103c0081180364200c002d1020024041c245801071030780c0402c01c180e1007100182c41d0700740d000c1440c03000c06a1101e14242c20000314600040d140d400c1102d600e0141c40040c1c114281c3d02029240000d05075201004802e440c0c0c0082d0588146c514044080d0340c990306421801c41e4a9850b051101540005104080c826240c0541d5800310960902c0344001d160210000c00c85e06611803000c140d603e40314003100a01a1908482011621000d0728001403c00340c01c481c0c001b4800d420030001c0010300520501114001d40651038000801d8a5581c140407181003100c40d03143c0c050100003242c00100d0780000c4d800350744c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 953772122 1250 953770872 953770913
    0xc011104080a030e040c0504090203060f030a03020a06050c0403120e0a08010e031e0c0c0607030306030b042117161b05010608070e330901030c060219210c080403 71
    0x201444d5401c10007101c1610281d1070200d50184410301c80c0d00380c1c681c0070310ba00c500c000e8042c0b0071000300600042c2c81c14290708402c50050b44906514001c12542e0700503a40c2112111960a080c0f60540d5942c540a40a0403041406c000b2150140f006c03580d5800d030f42d0380c000c002d440000c0141c2d0300390204058499100351003116500007410700200803010a101103410f203001e1400503054010124080015030f501c007034419410152241f4010010a90b0207416034052407017845001100ca51445034080c1800e0441b5200040c000911240e0052146407000741e0747c01249411811039641c0c884405035500290705e803558204019407000311040010540c0f00350182c4003140200e4119642c0d51907640d402c1802141e0600d00f94030785502150520a006032040140c100020400c2c3d4040d010300c010405940d000d902c1590b01d4069207404024075030b01070200c0340715852034a01c2c0000500d110348609091070b06441040c600c4480364810070f2580e900c42c001186030b0230361040c043c44d41c6580d02e083c0030864030000f601c08600b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 953773372 1250 953772122 953772137
    0x1e080d050a0f0c02030301232209060b0f010221071a04020315040c3321060609050f0117240105091011070504020f0705100b03030f0c011104080a03 65
    0x83c00d0002042d00e040701e0490082c0c4c4000d40000000c4142c0d60400342006801100084451940c201c4e82402c010561101a000080d032030329a08015003518800c10805004d08052480040103981c00700e403220f030300e82042104090000540303c2801251044a1015020082c03240c00e1307281031354a13105540d00460086044074031000e564480d00c1c0c2080c005450081c01c50044440800c0029030260358400075001c2081c50301c05903103803040c1c14400c442078440440000790302114401c010000b4100c68409088020b80c0400c40d8908055002d0086c03a80c0f0f0003141d124445030744082c103140c7e00c5020030440081100c00024990b0412a10502c403000b140365818a000e1403072050782542e544a202a18001003000302140c4002c400f162042d5001c400c440c031400201d0145070404159034845000405540c0442c40078169141c2850a2031030502240030b0313038034002508103003182c601c0c3d40c0c000040c0c401910805400b10303525483c030b5079000d00600072030306181c10403c40409c0000d05c0d0036003c11b104074694080c1c0c8030f81d01d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 953774622 1250 953773372 953773391
    0x2115100e040f02040b0304060903050904050f060a0e07051606020f0f0c071d0415110f04031502090307030b0903131401030c0314220b0a1b05071e080d050a0f 69
    0x40a138080c2c0d00030245400390501c0000c01042e81504003254150190404518011280b0003040035948200c0b6541040c5440c2004c0c0a06810320365200001030800304481c403658188110000d04900c01d9540380c42800c220101d01e9400d01c0000c3e4112280700c01a00c0c11282d4401c47c1819000890b00800c008001a015001000900000104a040400c182054010841c0d9030b00c0d51880c1c801c0808602032684107130b50700b425012825608000781010024800c180d9280d82c0b540c5000d42d100d405c0c41e100d000c0c0e500d0044c041a54541c4001844c442075036440003008080790b035800c010b02e1031400b45012540c8036580d05a40015a0b2a0070030b4192203402003a40c0610540307410150544c150b408810381d030178000c10070740001818007803150764041f1080742a8101100480b403030b07242c01540040c10b54480b1240ca950302d03640c140003648400f0390310ba08052800c1140c101002a00c480c044404458802c141c4140c6402c05107040120742412a50022404542042181008180e510041002d0500e03004114513011048 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 953775872 1250 953774622 953774651
    0x1080109200a050402030921030907050f0a12051f09060c0516110609040f050f010806160836160e040f060207020603041b06052115100e04 61
    0x1c0c098140180080725024608002e01c0000c0d40014102221030007003100c1082606045605540e50301c0402030710607202e0900d40b02e41401e18a4a80c0406d10034050030399183c20a0321514600422110510056800101c407402e08904140403410104e890b640102c01e100032182c01c0351b01c80c94603a400b80300b0070400000f602409545522607072042854001020b06100001115034060343e44202024065a0401c0d0b08140841c05456070719000a55280e01c82d41008060075418a00d1401000c0141c01044035003000d140d5004c8035050b4050350801c200982d400600c8441c03840c038043e9a078550207201c4110b240d000152400c000040e10285542e140282162601549000c411000668400880c1001c0315296661818180707914100100c440d48d40a125160143c1c1d0b0f01e002031882117000740340d003920840011010f0214841316420000901a0900a00c040001750704003072050289414824030180e100ca10340301c10411508803c0e00e91109580030078864860b84072a038000c003854295424090150403c178030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 953776978 1106 953775872 953775923
    0x40c031803110f01021c0e01180b0a0b030c01020d03052a0310050306160309030c0c0602010e0f010c0f300219020a030f0e130501080109 60
    0x182d003000c080920500034407000000003103240406a00803081090f06880031000582d42d2084010002002544040f404203c01c4110406100300c17468000030345081110b040c40d4007401c210b216845030030002088281018144c028094060700850210010800140040802801c0d55403007100040842c0312500040001c0d541c82d696803801021541001200f076100c64042d0f4010403c0181203050070546900c0700c4e100c1d140108440e0014141200e031000410400740824611a9000801940550010701500303140825555061078900c2007070f003280d600d4480c030000b0508010050f0103a07441000a011403022800d1307450f110801d0282148442001d0b84030352150b459000600c03008034110005107800103000d9200509016100e42d44c010601c04801c00f00d40280250703400f810050350b4881e0860041c82d05092801c010039079503408168040c2409101c240c800010303649085082d0341400b0752 = true := by decide +kernel

theorem cover : BRFrame.Cov 953597122 953776978 := by
  have h0 := BRFrame.cov_init 953597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 953597122 ≤ n) (h2 : n < 953776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
