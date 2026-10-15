-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4140
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:41:11.495982+00:00
-- url     : https://prove2.me/submissions/25665010-f0b3-4650-9bb8-433bf6316eb7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 744424460 ≤ n < 744604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 744425710 1250 744424460 744424469
    0x50118090203090f060612070509150d15050a141501050c0d031401060c02010816020a050109060204290d2d06050a0503031e160c08160b07080706050c04 67
    0x41c0000140a0001030029a040010003000300341c54141c1c56040400c40b000e040c200724145554040d400c1403000e403401d00742c000d4020585810134103880001c079010900c400306088040e281c007582c03005644850900c50141d9544007802100400c140c043c032070030400240d20060402545203280d01c00f1680d00d42d02030400c4907901c10740ba008807400000b2030350006000c1d104200000080c0a4120000684076029854100311141e058480ca0030581e2110700d0301000d00790341f02441c0308500c1030005040203d6020711500c110a805008050b0307940d4101080088288510b274108106c18016070071a0030079210900540d5158145504003081550504001c000c90025000602203112100740900c07034400103643c0502c086681c01e88280c6c001c01e40d14820162039000d10310b1516030030207c0c0c0c24104042d05500e802884580c0e01c049a40170080f1058a4921400d02d1a8200010550040c4582c007184c10928001800604022200515104d071030781c0c1e800404d008440c001003803541c5031000300f034005c00c05405840141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 744426960 1250 744425710 744425729
    0x29030705130b03010c05040608070c020d021314070e06181504081b040c050a0f140f120114010c030e010905150a0e1e12070b0c03041406070b01050118 66
    0x1c02080340c02800a02d801c01400744203601e0400b00a052500a00964048a40715194050a5680e091003540e00c50b8512100303e03400b08481c083e050040c0d4490090395400d0034600e000060542401028204440c0041d0400003032200360110782c0e007142d0764041101c840d019046500d51082140c00c01158050224450101c1585c41c007040c0852101c3e0000795107440a9500c01c0500c0600f00b00c00c080c0310494000707125010025800f0001c0c0c0820a0090742e5034201031040d85440403072955900c44151550304449050150140d00240e0702000c00d0f10b00015074050203400c7c1c20a14412822000a080394480c050300070b050000300d880325681680254091001000c01038843d030181d031b00102c10100c1e990b0021681001061111a604c8024140002c800d000e0180e007094441e290843c91080040c90000c1c01140355031032080304c501155141980c4041d0404500c0d0500554a9030f041c150306420050b015800c00340201005d1003100b01041d0f060030018112402820000302d95940d2502441103a0041e400c4000c50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 744428210 1250 744426960 744426979
    0x810061a0c07120b0a0e2808090901060c061a0603040f050f0f01020403030212030c12091006090b04050708060f01110c10020616030c02060a0e16080c1306051809030409050702070f060329030705 85
    0x24de800591000885215910420292025042000c0b0000da0744115a412a40a2001500103210850341c40c400314012002c48584d0010054840d152000315100c11600ba50042820030030941c04010381d442002601048a046291a0050042d28051003e490740d41118080105031404028010106803500383e800910520b03840780d120002810400c100b19000700d203444002100640b04502c4907016810007441d420444901d013004558250580c680c40c1f00a0160601500d01565031192109180607a0340150610707180c9450300995140e000034110b020b01d414600e01d990903c0d4045241540920200300c00299180401100d40c6090070308101a884907451a00c04680010001407030709a044080303401c440300542c0d00420000b9a5405c3c450300390443d160464030540c901840c25100d80c0480c07020116030615503a140700105541c4161034510250300050400c0c80201c0400e000c040240550341402c0c00142c1100d803844c2c0b034009800100101e00b14410020141542d41400a82e0084c4002041b0310017 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 744429460 1250 744428210 744428219
    0x6041503051515063f100501020c06070f0605040804050907170108010c0801090c03021204030807143c130810061a0c07120b0a0e2808090901 62
    0x201c210041c1c56000601080700c480070a245040340c21a4043c02e60f003210f20740b1080c0c0301c0000030184e00c0d540ca030605c1c0c80030b5906103000c5002688140544992481040686001c3c81c06001a0a0200789100a40150800c000d0803010031454050255410340c850800a40c955990820341010b0080d41c109560200705401400101a840b00e440e0764855001c014603185a6a03c2c2c02980c00c03652050310392408250004010032506038160302c01c0d103034010f645c1000351908130410b65200315011700b110220080351499042c011850382c42000070750800180c200c524a44910414100b021401800c5030600010340d02ca444042c40940030850740341c40580c0d580c1552200350b06100a04e14003c94041c04086114149840d01c49a1141c000c8004803841c00310a0f41c011640c0c5035402019174000764842d1210701c0b0307203107000036151010200d080f0307200c7c010844100d0504180c1141401d03900740114655880d840054140c07094166402c1842140903403102c0c2c03028419851602403458029a07042c95803040c141400000d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 744430710 1250 744429460 744429493
    0x406140c0304020a0f0f03060b0f04020a020f100212010b09030c130e151e100b030a060303180806060d11040e0a1a010e0a182f0103020304020303030604150305 70
    0x140150b1003166204034083d10b4817090f403031240d4644540001c06401c80740801c08148541d00c940d030b032013102a090003082612240410240d07401080c102d801688805180030f0700c800240003416000c20085420f5140060203640002d6041c1306001ea400f005c400010354a40d296800c20130100341c01d0000d015114804080885040100006420704c4020700420385005482602042c0362480b0707180003286c441044454440090600390300924080d0307048801d40780424005a060013440c494890000c01064450540c9001014182081c1c04407003541d0b6003181c14041c0d05030110340f0640c0300b1000c4d41d48180d0110399007001000c1323200826200b034110303140c04000c1e042843c010441c0001580195501d100c0140700029004013080240301d49401c0c1110780700461031203ca280c2001c0d140510401502c04010003540311884840070541c1c6804038000419884890340301c908e40741103082c2109080460652503d0b401003500c912009110f02e1003103984401c804c4484070302c20f107520040c681000888541540660307080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 744431960 1250 744430710 744430717
    0x5030603031303061a06070203280605160e1e130f0608010609180c0e04030c1a0714070804030b04020d0c06110c0d050307030f121a100201090b01030b0406140c 70
    0x2141301000312003a9051900380785088602603903018004061a94040c0300005141d094000cac0210031080080090001c24000c1c0a180c0c025003000d004000031400446014007002d642138000e501a40704d41442c001200014003107004032490aa460090280e03403100250001c21981480e50703040b600d0490b003c03d52080551016043c3c46011008001280003180402c1c100c1c030170340324024140ca10641c1c00344000d0030101070b2036802501c2070604041c80c107042e5840e0290120b00022a0403500c502c1003c210805900a50381098850010070242c50b1045644404442e031081b800090070504480e000702c0d085440f50400310211940180a405007240c94030300050643c189414a588244110000300d0400c0c5880301101212075404002540303010480d5805442d440c0e0300c2501081070106801b214000e0031100e0281d00b64144c04404109041c1e180b0108003d40c480d4000404e00031685084404400034450481480c15650800080f007215540c0e460041c01400c404c40b90001404055810b0000109040c4080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 744433210 1250 744431960 744431981
    0x3519060501050a15050a020a08031806010b032719080a110c0d0303091b0f050a140604120609022e11030306010f18060f020d02010207080702010503060303130306 71
    0x1402a80d80e00c0d0100b0005a00d14000c020407080c04c46804180c0600a400a01c000050360043d20701e202d4060301c6107042030b08111a41043c0800254005014100c18413032180035203480e20400d8203504101b01c00040e45008100528072414444400c80540c62042110281c6c5c1d100180e01d00d10082c5035458001410b07040081d071880441d00032030f101c080c0c00b04085001104241c0c094041d001c0e900040e03c044018100e21003080d125651003403524041350541c1107001000c1c01b40c0c680002c1015141c07806101520030680d011020100c02c07076400051035a42c03c030445040300c1010a80c8104c00b0124100b901c010100f800c802548404144102d550180811340e082410340091040c0b0300e041c1200e204191040d80120391105c4094200300700082480d8011121349199207c913241c0203494010300030b0309010304001b540001c4042080c0103007010001307030b040011018800c0188025400e000399682c860640d402030240c000c1c188000400081c009840c10410348841000c00e00000b540303690b0301e0400200601c24010f6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 744434460 1250 744433210 744433223
    0x30b09090111070b0c07120201051b0702180c040801023609010b160506091006150503040f1718010905031b0607050c030d02061608013519 61
    0x50320315481846001c0807006011101c80c039045040c0e030783c3d441200004040008851003486090042211305800300082c0078560000030341828103249551128001c10420704950104205400041e11501048409000400200391007521801e00c25002806190058a80c40d132010480c070220004400b1180c0c0005042c071450500301c4d20741022000c02c001c01c41760701d0f034001c88417100412506403040000d103004046d554403449442d11540d1810304181d420354000c13800c0e41c02015040315030070452084000500e01d20800088550fa008400342c0742d0b000041c40640710401040c6000c0a000000d0001018401e00c800f00da955400300050003051700700c849244500050340c4000c0419503090001e030052244480005003a0308640381810481c03558040a0129000e0042070036140782602d0821444402c2c21058015104a00c1c28400c1403004040f0502ca680801400d04010040b801c42d800c0d90440d980c0b024891109910043d0503420142c0c01e40700b02c8d08800d88589000c014140c00741d4415903001e18840c48 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 744435710 1250 744434460 744434479
    0xc0903160312110c0d020402090307030605060f0f01121a090405030a1107210813331706310e070f0501110106050a030c0e0601020a03090501031812030b 67
    0xc000c9914800f888038901459108011440591901d40b000c0051140f0081c005071030700d002000071a04203d4598400c490150b240c000b8019289400b20b03048048500a84920801c1004000000c0041603071220010800b651030000941e00701040842c032081400140035600740c0c0c20075242680e6217074828058180043e03e00c090144c001b900100b000021100180700484144150514400740080d41050032507101c08104510407a01609001c00002041110480c00604205100020142801500301e4004018559880b80119084003954581d44105204800e46540300800714a2250301d94000110720106c2100040a0160060303402d40400d030341c21024482c9201195041c2d68562640c051044030b080c840e241440baa511a400001420702c00100101e00380c0d9503070300850801c5000f9003059074604600c030800d001030404261102d810203802e04c01008954000c0e02c005041b840e260081d40d0425480710710b6160740880602c800385005821404200803500c0e000c401400400d00c00c40c2a40c0210b0802 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 744436960 1250 744435710 744435743
    0x71209121701030b0c0d0609050906041403070f080d0b090906071b02060306100909020d0b011b02090105040f020417010c03050c0406090e1003080706061406180402030c09031603 78
    0x2040b8102d13a401510030f091612004d4004905411184259000d50f0b030303404001800e5a81740c00f4050003864000302401c400e0800b41889003291b1300d1240d148450307901c00c005070302c0042c0f0441c044081c50f0390800740d15529501c40f401072501400014895076030283c0d10f58144500b100000c603095029175195200d00d862061182608004070b602c1d4a40039600c020306200081c0c0070b0030042c10307420707010115103481e15107075403919a803608980210100c4604e0b0390741d0b2502c0c000596001444ac40c1100307400b0300380c0f00445000d0780c0000c020305014050340d802141c40740844c0c49a40c8403901620042d0a9100e00e03c80840d219440f498001d188152040c1c0000c2d0a02d8080b85c9104a50070489081c1c0b071140d1b41d2240440d003051103040301c1d4030000c0c3c00e04542440034407000000c80d04040181589034030900c004208030b440c1c12903204025070200c3c141c43c490841000720040006504081c50010f0340140c60258407551103054180050080c1020183c0502419203c1107140300e090300e0344030960344103441802c525030f00f0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 744438210 1250 744436960 744436997
    0x20d0801050f03070509090102040f14100e030d0c03020127050606060c03341a01060206070e0d26030f070c022b0204020d06080c040207051507120912 66
    0x960015050342001e0401e005500b4810310003603001f01c42d94000352030940e4540c51002e1682c0d03964030240450341003e0f17900c0d440d40b0b8104030a010b8140e1600d491980d8590050001e500c0d1000e2800070818880501d81000c01c05000390400301c20403410054440442c258940c44041c40002082d04031107500072400092a14a008425104441452030042d403c0000d26049014110142d5250140b0070316051103030b4400516100d1981c90681c85521801c0b03003a02c0c010484c0d0865203040e04180e0654201c0d90801c42d60590200d83d4501c1440300301e542d4030100300f090402104a060f228107040c101150111140324500355032000354041c08102490464036501c04030101d03000116104000c2d80614402c01040c3c881600010011040300034400ca41e180034010380c0018126840625a602c086071a01010004014180100d20750f200042e14154070300b141513566151548283d1040e010341e5100ca03404248c007148174039040341c00d00070803190402c00c908460620100f040c0c030b2803140f40d0003d0f40c08141400c14404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 744439460 1250 744438210 744438229
    0x3030b090c0304020910052d0103050405030a0f0905040c0207150c021f0201021b30220b04032d11120a0605010e0402180c0301050f0f10020d080105 65
    0x1041c41035800c50700c450342040915040078204499aa40413003002c502a62108425003050440031104003a001549110740c1103407000c44800d9043c149040100004540040100c44200d03010385400344103c03140320016038444a668010a030440e29102884030016000100e0009441c184040d210001829410031130b040c54040500079001041d9041c010780007080b508034a140c04c1c50a00025042c4128502c540592118160404005620224202c800d516640804141800c00b40002141e00380600e0908545485008441c1854070005813810861640d4410100e015004004d0040c3ea62692800d04121301d4194039090109208981c40c89030100b0079409984403d990320460014041c0100010080300103c1052102e069001315000c210000d010b902c10b5074080c1c40c041203a030489041c00d005110751200c0f90f4000d54200030340d50741070090001c42401501d046500450303000f245000703a0350108900d401000c610a8100d22480c000c8640503401164441c8107125664030100103030303a601700308501020b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 744440710 1250 744439460 744439471
    0x50c1e0a020c0409060207080310150207061b0606030507030c060e1012110d06090203040b0108060712090201020c0d1110031a01120608032d030123031203100303030b09 74
    0x20301030071542c0c0441c01d0603005000010b0080740014148410394841c84030560088032002c250080f00c110500c8400101c100b40803c1c000580f00815943d41840b8001d4402c0c401b124003403554101462007070041245e0f6070880c1c00950ba0107016205441d56a207000480000b4034001e84011840711020301415007095051010404040e03aa2070900304a401c05c40c200420511132403002d03820f010000b04203404c0290141a005118042c001030380c170301d054140026a040e068008402e40c1e0000d1051181c610b40c003205c2150b000725030090014050115100507480c00490b103200700d8211103c003403d04107000c00c501100d6a030550503101480328400c000421411507000c0c02c01080d00700f4081d04030b050b040d485000c910344400a021000130340d10380c6420120345541c104164415554800300400204088098a40c100e0020702034041401c0d0750400f024898809040091403106041501001e0501e50702003050182020b00d040140b0b42d00e0034000d240d40c0d40141c4e00d020540109041c08052211400c00c210700c0c1e44a01c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 744441960 1250 744440710 744440713
    0xd0e06150103020310050913020102121315020a0b070503070e010c0201020304090c020102070c17070b0c0601120503091e0a080312280c020a0611120103020f13050c1e0a02 75
    0x54040c0015002900040c08017840051651008140703600d03250145070040c50b9244001a1182c01880020b26004a02507085c10406042c00001304601c100c620b04801e03910f40b010b001c4400f1942d41d2041346011740c4910042e00f41061141881f1000760080300460048549544248113840c00d500155281d280c0c146009005038010481008203590b10b900044501005200142c6410101e07200c035411026290002c54402c91710a03580c491a00f0b0400200005100050300281016071040d1699200c000520900902c1c0304074440c3d1301c007048424812140c18120007001c0d580041c4211004041c414003c015550003042003a0020034040800000e0314501d100100528403103a561041e40c07510000c0700310580001120400565030b01900300d014ed01c1407003c2c56801402004202d0030700d40c00b958004a04a03038558001c00621031244002d01c00d0b14192501a02c02d5000c10069002003a0401c01c05015070554618010a02c010320300c0701401004401400b85035030305c116680c8110f50b0340c0c030701c26010303483c0c0517 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 744443210 1250 744441960 744441991
    0xf02120c16050601080105010f050102061302060a05040504090f05060903390f0f0c010c050c21011a1807090e090709021209010c020715052d0d0e06 65
    0x103203038080c00500c4400c00d4080e80460320070003940d8072882e000e803c0e0003010007039448400601004e4120381701100180000d100134509814202c0c25492030700140352019004000010f9a50031040c0a6811a001840003820030080c6801504013040101c100b01e80c2122140150700104007007000020030b9402031032040340e4228140c0400c00c48003240307d025111aa00e15405c00e480b820034040148015801804100094820480d100311118100390703000d000302d41401440340605005c582c0000340410403007000e444a52200e00c5420f42d07051040308080c0103030b09560801d08112100c81c0d40400202d41440700350340c401d082c00411700c00000c6045040f1202c20000d079003020104032850301d500000750400d42c144180c13074220b51113203404c13030903030703006c3c0c615841c941141d401405203000c1c0900c281d805000040c400b5000d5a403c0001034101c1810391200e003c00c118012a1081c8102c94403d1201600c44400501140f10500e00c01c00c2510342d00465181104149010f400e007041c1400800c005121b02c0103070001411 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 744444460 1250 744443210 744443221
    0xc01090e06150309030d24261905160b0f0319021908060102070608070c0203010b03010c0207420e1018080f06041403130303030603060f0212 62
    0x1040e0000078001584039141003400c4200002d0640103501a9a44002455444044c0500e0006407840035090b981100c0c9840340600e1801c085144040c19202003640002c061400c202d54501c602c411088140000e001c1c060300c0b40308041410b01814505842101036800c2008108050381e1500224494003030809420018592504030b8200115800783c46a000b1741e95010030030015804a801004100d41c0120103040d64400703090300002450751180c02440209001410b00c000208130300c01c058000d10603c0720030301c061001c56400b901700205103030018000300501941c444000355074102c0c51040141001801d05001d41c080f52255034032001100c903400c03007101c9103a840780c0994411044402c5c5810807035034071400c003041ea441d150342c00300d0107400e039a55100300301c0040c0b800c40032001141d210604940c40010012300030031010800071751081d0012801c039048900500000d041d8401d640302d0143c26940b40002204041e01369001c00c0660303014035420030800311096640b000f28030400028260601b10240000c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 744445710 1250 744444460 744444479
    0x1005150607020127062007091107060e0303010603050108030c06070e041e0506030d09031a180f0601030c0f030f020d1704030b1602060606220e04060903110c0109 71
    0x1041c40c030615000070300d00080c0d04054440c6404074803903280011604801c01034950700084d04807884060300c400c40c9112960005580e51880c0c548104a075079030300d6601c10101c10000b041551080341d001241072143d1030540340c10b40e40b40d600034000c440100e171400001142103000041915040318001c001050540c40c1c0103030035103103103030303d01c8040c2d038055100c816101302c14200303c0d82c0b070030000c2e0071001c081203d040580c20981000e05071003210f0204003240c2420008601c00e20650160091581d04411190710f804c0c80000b030302c1121000c0300b6000e22071039a608010002c0003950b0b034100e07801607001841c810380391403c25400001b01d10010b801200d8103c0e00c1e5016180002c02250020720510000c450a00c5843c600102600191320903a2010601800c00c440f1685802d81c840c05440c061018059915000002450381d000744c1c2036800e000400491001018114222448090800e0500602c5c980c600380c6031010280c030001500310002600d000c3c25182c08130000885034001e81c0140c4a1142e1103080610a4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 744446960 1250 744445710 744445717
    0x503030a1407020a060309020f06030c0414060c0703050a260a050d0b0934020a14030c060f07024608040b211b0703030b1002070810051506 61
    0x1030788880c003009550010b079030b14030300d40000740310300c0d02c02244030f90107801003154074548403002c070b8041c010070000c00400e801004221401c0d20fa4104070007940c1c1c03603000301268541c00307039121618042c850041c0110170302ca070016419405030b01c103100d44041002c4048212001000c0b124030000340c0d034024000c900e0901c6c0100060048a000344c000066005161400102c0d03e86054030840c1c0f01d07584017041c914401441d40742000c42c207240d22800042480003184002d64031341c032144000d412081003040e950780c5800d00340201c0d006006e2006c11501c8504092020048015040e10420054400e0740c090481261020304054001856010108045a11807280250314088000307165020115480120009041c1310084c2c40a080d25420f15a140c2d02108440e0020355980c2500c1e5400d2842202000b1100c51b8240102441c8800d14100a4a64105241c190040e0040035029a40300c462400441e18040d8000745400071100070100300c44807152400d07481821240b0a8440491100220301201802e041602c0103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 744448210 1250 744446960 744446987
    0x6050702091815040303020306010e0f090f040305040308070b011715011806080111071115071707060504110915090604021b100c08010b04260319020a06150503030a 72
    0x3a2402d000b0f003004800b000c2c0d002120103d010036404800e00106503840010181c1d9003a041da1600c46800e0303c1c10005221110040402c00311141d030300300140403d8070510a640040d40c0c81900245ca80400d8544506686024003420307201010300049903c841400080360080c040c1003402c0a050790b42440c1c02c0300c10f18542d14903202e514548070350001071101000d00c00d501d00005c3c0d1002c0d10740c41d200d4078a8421500e40903c00a01e104140031601002d00c507001004440c80c141d4072218002c6e5000d24500724480c0c42c014140f0141425192404000c14001180c800d015011002c03159001e0f560780d0502405d079a060040c2100341c100701c02d01d00207038441c00e003580200284205500c4840e048000499082c0c600381607103041c04a89910350149580d29600a05001c3c0901540d0320705500305810800d041c81c180401541d04490404d00c400d034903c05100c24400c4400c154030321141c8881c107443c258000780d40c03540e40c91000c449042c903041c2004042031000341600c042d80c00045c0a9450004030a49c11209010715205 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 744449460 1250 744448210 744448213
    0x5190b190201110a1d010306081905100606030515030d0906080606040306151e0b07060c030f02030a1505040b06090d06110d09150507120c090306090c0e01060507020918 74
    0x3c0350180382c058a00a000b66080a98480080e901541d62004a1003030190a0905250514405000c00c510105200401004039503080e59401c43d1030501c1450201202070203608985002c00c04248680c2c19081188100800d8800405441c45403062594036100d1000000008907402014400e561003800400e0b080640101043d050503141e0700c90340119181e0001d2881d400302d86c482c0c10071100790741aa16546c0c6c1722010402101c443d140071030410443c0b2928100411207076494021500a034042d03448004006680c40c4115240c3c98621800c4004001542e142c0c0e2030040800000283e80c54507028800a43c1c00141865060950a030280030081c1c8140008852142e16030300410349080128000e0961510544400700e111003d03420303c80c0380c060f800e031081c11032603040008005515130001c1c80e4480102a074000040c8480d4100000c40301c0300031a800061015007040b100070b041c00800c00c092400d550001c0402c40c4a66039803581039906110f501c0c4001d420691034000100b0100c411788483e10720013130110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 744450710 1250 744449460 744449471
    0x9091143030c14010e062406030a02130f08010b0a15140403122a0507031211030f0a031401140907260912040303140d0e1605190b190201 60
    0x944144a0f12804a201156a0340d503400c41a0101070800c042c41e044409205038100e4078241040700281010544041030040320004049140414107038100c5010021740220b4220302c60700c85000040d94900f9101d40001582409012205031900c01006000c4900c1c0e100d2000d42041c90040548103c01e40c1c00d920300a2003005c0c4000408a00c010880c0702c1c514905603a8504c20242d403041d0065a00650010381c401e12000075805070020704001860fa05403030300141c000c0005034030b0f0102220081d10903411104039020110309600046907007405880e049519480911081c44505107170507000e5824842c14201c10b602c1e806003903141c1040d00140d6000080382c0307405488204050701e695819803a041004018154081c20007110300010b0281810300c2903400006440c00c3d145440040804840002c4102a064005801c410401e000e0748540614034043d0705440c10002400946c0b5030301020fa200d405e01405c1c0f54644150751088c445450400c0d200c6c18500142407069032510301c0d40061000100100707543d40d82 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 744451960 1250 744450710 744450713
    0x1090902061b0105010f0f0e18160b09130e07091109100c0c051f051815040e0709030f06090312050903090111011a1009091143030c 58
    0x1900b4200e078002c1403400106555260072440484861243c0c810846050740050034081c9003a042600798100c08a42503a04010b080d001e200e5041140050004020403000ba02c00244c2c001c03520060410711200316909140710100450510035a18955181d80460300b00c9641400440e00c0c07580152501070b035041d500c2d07040c04902004112010905010b81d40850341207249041000780b000c0c2034401800d42075405a19180758042c1071600310b14002c9840c4148040841c00081c40305000740c1035076a800004003100b80204101e00c44464541c00f40c01085c0c5030310701c5100021300c107034000c11039903088952005501080003400c0d111b2000408903103004a041000c3c94030040b0306941c440c0a0749004a9000c40515074aa400500152983d0004510015907904158410080213201920100c0d000e50a039042c0c0401c0342c40c002c040391410601e03040220010702d050544910098940007412103a592804000455945440800b03031002803800b103048000015142d0101c1a5100b50910000e20712070300304008441550f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 744453210 1250 744451960 744451987
    0xf221412041701061a2d09120703030c060908090d11040e0c0612040c15020303010f080a0b04080c100204080303060a0501110c09040f0b040605040210170109090206 72
    0x202602080d28420100c0c003803111070401014841c1c06a0764400800440d840d044100929080c00484880026000b003031800510140c1240036a1010100981010401036980101001d4005030344e0b40740681034400750920300340b000150041c1540c3d01500c3e03088082c2c400d0394554026100d1000125110032040c44041d0305610b452101001961254082035115101c00e01848111480340c080301c1d042e035011003441d003059100c29040f58480d914810402c1e41583c1c03541818420180b4030b80c880b65036006032903265200d055004c005103060b60002d210542000e40e80d08903185d030f550000000504a02002004540051300010060580901080c15a5042c0b10aa40c07072500b01c0c4c0159102e2409078000004001142c41d0001900d00a8003090800b100004103001c0015079944069038414050052a0041001d00640089400040da1312030444800d519092611401034041518102c0c091405040f102c10100d02401e13280c14202c01000d000301050780b0386041140580800101603030022820001003250161 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 744454460 1250 744453210 744453223
    0x90f0a090c02061f05241905040e010506090f01080a0605030d020109060608010501060507110427120f021b0a0e0c0418021303110f13140f2214 63
    0x201900502003e291030750071340c0700a140e00c100e044a88162a6401c0c07100390b41d250083c01340300443c1e034070a181c1c3e1403180008032081d100b1162041c442200c47c6d003111381416407000061003560711045c00090540da980051284074090103a403a98000d0324070341950025481046143c0c0d1064881501140440e40d6001203414100c1303280f007841c0103035155400c1009201c06802001d004040c24002000998134200c001091030040d403000903c4179100c0e200744903013a902c035080603100c018099000710180d00c2c10040407491014a0908640d840c400801c0c0c2100240a03400c0c201310703072300590080c4c00820b103800469080c00c842c1c000380b240c0c001205180440d11800241c40d00b8422481c2c00ca02c182d0b503604000f510703020541c03100c8104840c540100100d010004010a5040c00c40764000a001c4054060038009210703107510744191034001541c0c410390418844070790010007042c140c83c7d485507090740307411154a09403031044628003d94064095040140d40150500107403103401008451804400840450308004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 744455710 1250 744454460 744454481
    0x240807050d030c15060f080f190201080105090a0209060d020405100c0c260f03070221030414210610051206070516121d010c0320070b161e08090f0a09 66
    0x11300c08050f01004423420004080210320035400e0499514a90340000c0c40c0f01301c140102c6026440c000301260aa840d69010345109081c000c061640702c000b0340d0f107084000c2d001445198400c02c0407007111030792640298009010b045d0805002c0908508001109035000ca00704c0080c1d9502003214142032194206100e0740304504403000c00395541700740d00d004100c100050b0701044260700b40103c100bc40004000000c5500700d4503002101780d0101d458000190a00341c40c4e9558140f02441c000ba00b0103503d10101e02c2501c500000354403d030107075803640305001401400c0d40d00d003a1158006c0300488d115034050720103000301c00c450040a603100960f66468103149080c2c1030780c080204280f014842d80c80340c40c450244d04110300038602000341c611f903510020b25425107245020b1783e1807030b5520030300030b17105091040401401031003944654881d450000910b40420741c0f4810354002c00032000701d010145a810301840f00d59000700e200341c1071000b0b50003000310301c6080491040d0700a86608000500c0d01d43c5014580d450f1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 744456960 1250 744455710 744455713
    0x3010f0503070819030c030e1206040618031b1b030501090312020f0712091205060f090c010504091e0501030303090215090a18240807050d030c15060f08 67
    0x1a89040c09140c50708045802c101c00f82d41140c0021201e82003000740000078a40c1501c4c01c0407584200341420b40f103001411007119000701305070554400340c00e40000c009015030b2184604126440603d90440d0408001440040c0001c03201d1442c03408103620322641446081c00303541340c0c0303140d980300042004010740300354405c0721907075182c02c0081c090503082104140e100314204400d5103003032500341c80c00145114a00b00144402854245250014030803001d0801800c21341d12000c0c80c203a9181805595131508940c03018048120b10300040700d0802c041844941480181c440c0da0500703007800085809804010884518480307210640f0305001490301995000303600980b030004c3c22100300d0041c4549042d82c0064611600d10070000c0c0045501d64000c2079044441101c07012241008089110014044441030056000742ea00c2c01d20b48240009541074045074400350458100b19a10018001e41040f9020085d0101f414144070303101250441709100d1075424400d00009250b5121041c030403407179482e0782105030325 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 744458210 1250 744456960 744456989
    0xb1e120915010501170c0d0603050f101a0a0e0702101d060601090e0c090d060501170601063902030a0308071407051e1507051918060e0a0801020301 65
    0x148408840744a0140000317103409480e81c0030384100c0703081c01c50380a00038134a960f41c0010405054404e030780c03008014541c0202070710300c0182c0a41c09159a428000700300da042b039280c2001c403055070404000c04400f014010340040d08503440d0a40108014000a0040f010f500035504469131444403845074a80c2c00c10b003451522005c990a003031003407515800610660502000c80340901c80c08480c0401d45034000300d58582266594103070400300c4c2803402a400003d004a00741000481c00303d07848a02c0394120700b031000c01c40c2d04980c0d90705000c9071001104a00b10781a0300d15059003007181c86d80110130400c161a819848003401c0603545c00b10b8500f0a0924043d400603000f44180812564498a01418080114001c3d41410a240c64050f1589081c10810720340028164114282c40b82c10f000e14052114400007100a62400381005405a401030f4021069200c0c00844075038618021030f507a0701c0340064464011000750078440182c400803038510105c1d074040180312000401d0702c3c0074001140070307082802c01c3c14075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 744459460 1250 744458210 744458233
    0xd03021309050411090c1308062a07020103051b03090717010c0516061509020a1b0308040b07140d02090a0801020306061e0423010f020105010b1e1209 66
    0x1000940741c01c409034450400042c4070119110710038040341c004c000c50303400010b0b46540c034a0b00154803452819140740b41c0400340020701c511020076454418200d141d070444071200c1c400710701c4500007554501c0e184075160610100380994841c1d07202550252000700710070501c60104142c5440b075002100c0c640407a0740050f000f0b110f1650300c5070000030306801c018020701c080227003820060001c0c000ca0803402050b10304451a48140503680d00000001005540740c11007140d19041c03190017951014001c140880d081d407407851101282103800d140500c0d0180e580f00d0068031590b17299400311101415010070810000340095440042c00000c0211403694400181d80d80380f50130500c0800c01c5c160344140c10b10f91040c0200034090310b0b001c003240d040c2c070b842e10f840f0620846003e820300068001c80d04020b2086076017005050f850458010b001010710402d0300c0303444e152a0720f00b9040f0700380d030000d000740300c1c40200c103000c0c0c8200c0e03800e1030f03504420f909144005a8108040b402c1c0001c50300c541104c078142190b004209034103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 744460710 1250 744459460 744459487
    0x80d0b041e0c09050f01021203270f01060609121104090c14131104050907030e07140f0405070912020a09140f07020c0d080f13090b0a0f1212020a050d0302 68
    0x1813400340c0e441c2c0c0a24042c000080d40302c2a00620407111083c0c0040040c03000c807001036070b0702d0350082d1003603c0300f503042601542240e440f280c40c01302c404950310304000440e043e0302031850281100d6290601c458105410b944103064500d078401055009500d91320000300042c0040e090501410f4042001711014407107070304006d8001c200441c0012000c1c500310810880821510844007915015900c008503500d070310301e0490040c528802e2080d10b41c015100045803644000b0103c022001080312584811907890082101322002a00c031000461340d40401040000b8500d5503001c1c0303550004000d480c0d2503948003841070503540c001d00404400c080ca441088103484084e050940c000c68248010100868408046015041a644041d10b51030010032840960b8007004104c4002e140c5a01811901d030f0760301d01210b030147c800d050407544503500410010612441d614554800c80d824a0f00c40240c0c03081e10380b00c200c160141c04200d00114001c050501002c038404122544400f4142e55005a580d0105006003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 744461960 1250 744460710 744460727
    0x9060603010b1807031508100614010512040201140708040f030302010e0303040c12060204091506020d0521040c0509070f02060a050105031507050412031101050a09080d0b041e0c 78
    0xd00c2040d0720f1912480c6108189100c0d580b18043c2d081c005001081601d840c528154580d0142500d482060b2001c0f8880c86940c20203030440d07655507200e20403850110010344a81c0034810002a24480903000a40075601c2407250000c40c2456181552408200707845105580d03005030091580f1240d0040100205a8244a055641c824000c003840c11814165030740040307020a40702c0d5030451602400359409000040d03044800801d20790108003c4482180e100d180c02080501c00c00003d8011400c40c0086c040c024400c135204008588400003001115814105424402510a0350701000300000440c0303035261104000d010785a5a1141c40d0b00b110342000003454050001c0a1900f03280c248001004103803400180300c850182404605800e594602c8c50803500c5020702d40c803113160210007102803400d040e00048483e2034002c0c280003c5c041d540d6210b802d50141d0340c2d40c000080c0695402c0160040342001d66104004400e40108003080c454510441c0c030706c0710300c0502031010032542d440c15410800c54000c0c507034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 744463210 1250 744461960 744461981
    0x510090503060a0b100e03160909030e0a150302030a090602070b0a05010f12020d14010606090f090506150a02011e0e0610030503030c091c0803070f0504031203091a0906060301 77
    0x184a02d07540707203003c20b011482d005c407400140000314100081590f02448442034400400e101c65203200d98034242c503009004802d906a01207640c5d80b000c048903003840c050305010381e0303803554920131201242d1000310300035403005090019803991000841c0005100c1e000030a5001e004000c000c141c1d092246401c4110381060b4041981e210b00c1c1e00040252501c4030a150b0300241c3c040342c000c5c0c1c0413800c1c4d0a010f0f104210320f0b02d1210f4a9440c000c80443c81a4104041d24148c42080c804511840e4440d40d03050704070380c401d44250341e210011080a0f2090810240145018216403001260784201c041c90880e1410880801d80c804a444413a4684801c40400405900011500d040c81c2c00518540310b1948034030000e0541c5003120000038001100b5203c006504031481049410790204013500d080c050629002907850b4400101d002885006191003003090324162038210703c0840c104103402c1070550042258200440b10b6200b420198100300c446151141d00c10440180030741418a44007041600311600e503921b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 744464460 1250 744463210 744463231
    0x6041101090b120c0702010c060603080a0329060a09080105090a0210020a020901030204020306060c07030f0308060907080a0203040c08011e0b01020106060c121112040e1825051009050306 82
    0x4a522002c0508180c1c1140e44462405e13914201400102da024140302d0015003000c0c00c0c250004108806a4010f101c0c81202d075500700225078038510101c007422040ca01c08038407a0311b029040d10540c80c0c000000c046540700c500b418552a941d8020075030a54404865070f01882d0040100c810650810031000c085d00000c901c09048207284542c0011500e80c01800302038040d0707074003000151039a101c1030210f480e1701c04104111003a941e660b283c013100d80c0f1030800b030850024480802045c4181403210b500350142c0d0a41e22002c0c0c1c02d42c0d64109900003500014810b07030368001540000102c2c0e004c20301c9006206641c0006200c0f06e540c0182a000549064640407411685884002c008255101c0011810325a000248031040d00c010350040342c1891607144140014000e014112001d1031181d0010b1080342c507a00d0300c812055a03404c4050f0b5000035042c020301d01940100340211801d0082d46844500d489035403810060054469011403041c040210701350012620f074a400317100754503081000380c0c0d00009001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 744465710 1250 744464460 744464467
    0xf07020d110607110316150b06070f08090301200307090f081e01060515180102070501050a11150a09140708030415020c13021801030c1b110306041101090b 68
    0xa01c03199198402002801000100d0003c049201c10500407683c0000c0c0c000d50b020b4035100c0030b00b40205031080079442d0301c02d9640380402c03410301b50801d039055440f840d070010b01d103004001080c0c40b040c03566808070010036403555a403103c1500c00c42004881c00b01c042a4804a583c032840c00300406007540103244c20055a059181604101150000854011243e03c022040c4a40007031a50414090007007500010b40c451700513402e240c4605454400f40a40c029403840100401d4480f000590b2550300703500036680080c2c1c042010314140e44c052a0100d0b43c00076008219108480e0005181100c514292080e0740301c107840361790204c2484541c0c0c50b51150442c021014040c40c85c600201030740d60340300e180703d4503401100c41c444040c440ca0003400903040740140904151100c0445910090080d0b00060300c80800626140f0b041382d10354868495600c40d0007082c0c60b80306680180c0c054400001c40c0032242181c444d1080034061001d624107000300c0b80114810302d8140c1041c00400000b60250360b0f50340141c9294041031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 744466960 1250 744465710 744465737
    0xd08040f0b100512071a1e0d020702010f031803051b06150a0503070b070b1009050405010618090b0a050910020f03010611120423030f06070201061a091e090f07020d 72
    0x10703000355061005000e2455031f506849404446401820f42005255480401c40122100d03040d0010418030780700743d03904000809000d40960031519031492407145d00c0c848440c01000240104024010740d0b018106441d0a100482c441524003001100c403010000e90010500d0418180700701c007a4090403045001d010100c1c2001d880b480e6501030707000050036450703c0c90049015021590940d0015108220b400c6c449864241459030207409184941100c450205c2c2c121400340e035081c45250368560f401800781c031150315040584005424050609a07140c01400c8a009000b071071440140801c05800207407540725031500c080905007203400e03282d1103204d402c091004091000c05004070f80544e4038203989100441c0729018400c21000c03e0a600a0300751084118040402c0c0c00007030381c0e5124180304e900a200d00c1c0d07241c078084011181c0743c958101d4031540078046641285012200c141c2401c091a114203071300034020707000880011069031010300c0c182c0b181e01400503065040c000025100300a0411444030407a1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 744468210 1250 744466960 744466979
    0x60c090f08100504030c200a06032f0c070f15030b0d0b0a200c16140108090307020a0e0f0108030708121807090204060201050112050d08040f0b10051207 67
    0x150400810b078682e070350005000c25001e0310409000c0ca800c82200d00703400c004030340c220841041280307503a485419007450008070240700c0d004a004e00074220100760101e540a21840d0b600302840449441a090144031200d0b50400400c44100141102440d108034039103007011703030703154020b02c09540e404160500505400d00d449080d401e0034030945c450070580143e5070b500d806000504502440c001e038249140140884c1083d0100904130b00700e088810b407075440300c2c0b10405210b0120140b090301d500c90b105600c4242158080d84c485644296240247d91505c140ca03400a6880d010341d400080c80045154144428294280480c030b014000003801146801c0c0355403240d008a00031a8000f1504021250010b451072115000007805491000c0272035034032a8590001a000c0c2d0061700500b00150719080002400448040c0f450301c9440d084009400740c6007038120200d6090341d00802c181c90000503580a03400003100e00c2080b84c4100c480748160301001e4100320411100394880c4000c40010341c0040e809102c0e90340c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 744469460 1250 744468210 744468223
    0x1506080c090c0d09140d020c0a090905010e010501032402070b0412172a04030b010b1b0d020304090b1206010501230c060f010602070b04090207140307060c090f08 71
    0x100300d4045031a035481c29402d585a204003441d280c8400d040c24005002c01813610148a0aaa50301c0151614030180e04400c903641c214440d44194030522008003000402515032102405500480002c2494008c178030045e400d403030b000ea10071500e200b4400060500103c5d0440c50344100820923009502e04080e40d16003505001000c3c0001e4001c001030101498442d002b1243c5058100c000141681c65141c001d00e81020004c2c255042d25000d101c550f002020300070400100c1d025a6400205283d159081c07001720002604041750101d0001070540c1e007420a24010044140d540d15642c1c011603542d8180412803003a510510b81031030003a4013031108841c00b50b07800f18065065410030b203800d0a02843c14001e04c1004140b010070800ca500700001c2d83d40007220080350712803003030314550002c070101d9070b80311400c82c5e0382c451070721411140c0002840300780800100c0d50028400b25009409c600044129625000d0456104500454401c0e50390901c60024541060110004110300da150b045090718141400c0e0311000d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 744470710 1250 744469460 744469483
    0x3090f08041508010b040b1303021009080f0c0310050901090b040609031202190e0301020d091a010509131209030210020606030c01030c12150801020c03040602010516140d0f0203090a150608 83
    0x6002304600f410600707160036090046800402d04868000d4a0300e0150100c115801030348542d000301402c004404600088040050001078010b10311407130344410010003004050715070381031552551070741804510341e5104a80518040e08000079010300a1901a0241c50201ea280c03501038014800d01141c4004c40741c1c50308100025040051206400030006402031042102c4d192105181044807014450300c51a0040340030b4480000c412280d0300d403810440b08643c01c80e240500881c20414100014800141c180038410705030925404030b039200d07800258885013202d9042c0060340550200702440c9410030401c542a0303001c0c2001c000b00c902d44100104012a01103086d0318158454000c00880901c1c5480e640c002c2208030021074444541642e50380e1030b82c0c010f106040056007401c0110300742c003184180c00702e41002d5517100e100048a5408015040380c000d10030119285646e0b48283c0c140c0742c1c0d1030000f50300c109000d0015000a0b40d040c80c0034003481e001c044825909070324040080c0000c000004517070139000e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 744471960 1250 744470710 744470729
    0x50a0809120f130f091505060f031f030506150906090c180d06090804150e030a020d060e0d0305180a05100b060f0a17130210050a03090f08041508010b04 67
    0x9055400ea512150f840c16400751045410380035000903201095032054600c02c00a031400c1034000c3d60741e401c1182038081d50268003420a41000818965807000f010a103101031106a4841c0309507998503400c1c00c044080301d60311422075004c01000c440b0f28000049992102044031035100a0414080203200b5009460b4008066403080c40003045640d2030a40e4840340c00d46c80541841003041078640405e0540041c49503002c0017400b410744080b207501981e10800304080c080e00521400c0d00b03035001c001d98030886000903608503680ea000d8103052641440410310424071600d010540d424044001e0300380860144c4106081c4c1c0155010000161011a480e2a201e1403004c000c9180e40c0d45c031000440320310400c1101e0b40e81d010002000e00703038103070400c081211403550281d0038115551904100c40d007442949100950054980300c44042e680c0c001e80191031102090700d4005101d00f6255211080d1140412003901d80e4100850100208044240411b56800040c40e02c0303c0a5494030030bc4808a008134001e810a4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 744473210 1250 744471960 744471967
    0xb03130803060d02060f13151209020f041a0f03030901050316020c0a0609080c010f0c0b042d02120304082e0204180c031505040506120a03050a0809120f 67
    0x29075498182c45030f040c0da0010185984e0340e00d08404580b00e6400600e800c0301101a03110700003048014140c90000d040550744032000c0c050700000c0d40c20700904554808991014580440341c001d612188103150440c02903d60b900300c828030308010030100c1c280d007030405442070384108915406a68080c0c20380303070445083e482541d4000c0ca010b0040e4200a68041c0b07031900490203800004116501400c080c0440e03080d041a90140ac2025004440e0454182d1003800403e8501c000034000544d50300c070260340980240c08061042c2c1c940d0041401810030104505503880700d0680c480207510300342e0703540c2121702100c1c0029854946800583c9846492200d8090052401c0c04071b20712800314a160095000950754008654403070300d86403041340764121109001103c0b460310110040e02806031040036609841980d01c0580d1038501020000640402801690820055903074500d807844200840800b141c40390f102c0a45038206040010320740f2100030300c00c591503030010640303030b008400340400c50705a0180308041595 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 744474460 1250 744473210 744473221
    0x209120105070905060c010f020c06010e060a121407080d0c05011503050628150312020f10020c011e240b030c03130b04030509030d0908070b07020a080d180b03130803 73
    0x108200c0e03848d20a06800040c80f0342c3c0704000412501d040e110a1110941c0603260b40080c0060741503c3d0086406940c5080609400700e6039000030350311041c411104464145440d00e010b035040610729015480800c0b00c0082e01c108001007801052a1074517080091442286152281940e5103400381041d055000319000f0348241d801c181a9024824020075800d001e442e04000000c011805244402d030ba142c03150000041c011803021800d00302c44e82007a8010302c03050325402d100350025404020044507030b65a9190b0a22201d0000f2014018035002d4040010450680c40740c3d12a401181441c0802003005240709000032a0442c01744c0303401c074610b03507a5541c5950b1400c04201d190007884a01824203c54501080101507201c0c005148a000c182d081d175030b9110070384109686660050051014a820105050041c105800d020b8824540014681030308640c0c2d6a00f075500b40001c405580d800202d0b02028209070091505842d8024440001014903500c1e169080030140c1c00c8527500100f003040300002240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 744475710 1250 744474460 744474463
    0xf09150e060d0813030209011403060f0919050d031104060203040620030d0501061103130b0702180a05061906120f06050a17010605010206100b030703021308010209120105070905060c 80
    0x5a440d070f004492507078039019098038040030700280c0300880c0b0a102c41c800216a000d412126902941d101900a102035156030f6460340d18054020040c088500c210014280048004030003550801d000314054a17030600d076110010180c4103542110803002c034007003104000340c2da07000048804881d481d02d052250042d00805040c0c0e00b0344020311181c030505c004501c0000b51350301c60340018101ca40300d0300d440c821010714068068580c0150480d1801d0600040c004004499554000b8441284002c00a030104804440354440e0414180c400148141c0d9800030007400d42440440002d0700641040401281d5140a900a00500c00042800140c44d280e0a881c03803100c0d001c4d0015009000002d0000c1c0c00191580a40d210320ba00580800c000b5609007030000500c1d50010034034a00501740145c0e059020b0b4204400c40145602c00b03003d01e001c041d0f003001440d000314101c83c4000080c11030a00056983c0916a04009a80c0300103c1d1040080e4075210600500780d40080d81c8104030303a829940c00e5140c0c1800c1c074665 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 744476960 1250 744475710 744475729
    0xf0804060b03071a090103051506070305070221060f010801050c030a0c030b030f0c1302090109050d08040801090b270c210109110901060302040614092205010f09150e06 74
    0x611994444c1d00d804503000010f80d002d000701d283e00baa42003046542d10850f030800e1368910441c0940000007085144082171140000b44070307083c0081c00103c0c848650051460902030780039000c10094104000307102a4a0310380303079042d004020b0300c002408642002e0000d541c81f0300c0080d203440b403220780e0340e000f0074042030194100c1c80c4c4030345000b8252085041200c14840d11408602407040c855080e0a0400202a04c1c0b8825031f00b0807141a903c981d40c0608140c207115804518040c1135801100c00e12000580d2142401000c03141072040d12a0384d460705040008101040310020840c001891001007450720a00c00250440300b21000c6510031901011452150250340000d00307807850030350903e11001e041c480c00240c0c5500ea20030585112510340e070795503800c40882c0501d01805000400310950311840202c41c00c050300c03000c1002050654141652240d1040600751407594520142c1c8900c0100308031210322903400010550071900313000d20b044d03203105100d41d48001c1c0201c00b40e100c40b040c0422111f40350f0481d007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 744478210 1250 744476960 744476969
    0x10f021903020325080f0702060c01020f09040b01020102032e08060a02220602060606071502070b150103060509062e0306050316210602091314070f0804060b0307 71
    0x30140e0300d40c49040080d1a64051480145103001e8025145113900d050060401143c0d04281e40030704160411103214001e0744501c0c0c081c1d902880a00100c240160203100130022504c0304420255159044410700041d2000324080305d041d079105000300110b0844c80074003504104190718280c003209203084080710880301d81c1e402208540c4201e00030401781401d03d80c020701200305903041400180b81c40c130450454600c014091200160000408103000b0304000020f4400d89200d40d27130102c403003042e00115a0480e00982010b40c1c904080c14103010a100200e161030895510a1800784165820a40416402030001e0000c5001d4841c420021030f00340070808040c001c1c0000c5166000c0d20300b00ca090010080c2c04030f400b44610078050b000304103008840048151040b2000788100090000740c0c041380f0b100640141d03000751100e98080098100c141d440702140e4504218209001903a0a400d055190541400800070b00600100c552014512604103441a0b44264840400300d0911019800b103400c00c81700c0d520 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 744479460 1250 744478210 744478243
    0x2e09090b0c09104e092d02090403032f040302010804020d02030f030c0d0f080403110a080a031a100203161106070807050610050a090e0c19060f0815010f02 68
    0x4082e000441c0c50800c0e1950700c0d50040c0900000c002d03208140e0111801098000c1c1461b200454031085c0200c4200341e081c03c2002110340d6040c90140760082544010b048800300d0010f40e0b1160700d0900300d034075540b616080c210f1102c42034003010000501000d4078821400040d040c010400c001030115951b080444088070703809400d031386ca41450754045680c0c03900302e00c080b001c80d400388041c1ea100c424814101c54020703c00d503a86100031600d654071b040d11034017020881b0443d240154038074280440e40b00310050032240c03841d42d000520541c408a03400c0550944910700b6201d101c095000304070302a40001540d440140b000e01d2443c2c083c4041c60040350b90b1124207001368010b0380104822042c40760000203007550301d0042060303400d242d441840c1d030441c2c044540a07580e400101030701c09024203452640143c0f4145951070860f9020036040e000584140b0101d4050502200107407001d10141e07900450054005103582411410341c105410302580208036810428100100320303010702c64440c420000314000b5280d0f0f05 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 744480710 1250 744479460 744479537
    0xc1b020f0303070f021c050718150f0f0e0903030106081806010e0a0605180c0d02040504110903011824090807030e03120405092e09090b0c0910 63
    0x1408803200e81309104241e114924100740c51900c082c0b00240c542d80d081e4000041d0175aa401d04200201c00c0b0f60550f038406c5200c0d507400341d900740c0c80181c8034240040d240d034140040c00603252410424081c03d958010305140301084080c4440e070500041070340d041d1440750800035aa0b586141c4a58421014680c02520381e104900000541011a201041c00341008680500c1000e840700c06001101e06080804904001140006040560700340301a00c14401f100c1409440c256903200003405482080060410111002880b040549000d00c168030b0001c8004803030010000d03d64a40c04c481c025408450b0721020290342030740890043c10341c00101101d03840740103981c854045040c02440c01c0f1160000c54003038401d061480d0382030144001a038040303400040000c50640c0d50002408600b581e101d00800d1a1130b401c141094102d900ca4202034003030000c1d07250004100c5824285481c081901038524510f4a1041000810302c4e2941002a824152582020442c01030303003151094410302c190350710160402c0c400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 744481960 1250 744480710 744480713
    0xc03060708011a0405010206041101030e010e0c040f0605090c0c0109170d0e061519171506060301050112020c161401021b091605130308040512010c1b020f030307 71
    0x90780c181c6000c00c551032800301c194004403440d4483c1c1d0280c140940e100800250020f201c0b8030300300502c00c4042c074002c00c10200240e0407500f5122300b42980000c542218100d01010304251195000c1c00c111124140255454200407500301c803005440e507880e01e03800041d8050380c40e00941200039140c1e8041c0905150b01036454064410303401610640b644181000c6c031100301c0c0400000c0c000d00654503040240403410540d01000314445081e03103005811094550300140101419001c00c411121a0025140b070300c0c01d84102083c1820000c00c054840c1c00c0a00042c00701d0b9900850010011030700c0a001039036140640510ba1400921006200034200c079010081600c0a00e018814001070003a000c840044003c000c90080480c0d1040c42c81c0e4100e03240b04c00040151b03550600c0c51460034500d08240f40b41c191003045001c40e40c0f0164109450007a0300040400c8207040c08801c107010030116900030050b10580c203c0060507441c2c50000300d0b650701d004020010641d940c0562a018911000301140e545140e10b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 744483210 1250 744481960 744481967
    0x1e030203040b040b071a0f070c230a03090e0c03040b0423010f0c0503013f110a0618060e04020f070f060c1107031509050a0b040c06050a0210050403020c030607 70
    0x1403c0480e5070f08048506c1420820030703c04003034042c446003022541241d6034203104a40ba078058102c1520510800c0e41c52072004590f100410015200d04800760400040c0e50070042d104081c0f5600a002c440c640f0f00401502c9000d0300d059940013a4400c0e00d04401b42c035681000c400304144000c030502c520f946100c009410410542c0301e8207901d282000c00b071100c000c03000c006a03404d020911803402c0c0c14a0411150705860035061424841c00455000e050050001d2101d80044403d82c900c2120b00c01401080103440d807034850010001040320385402c5401c100d81c4490040012032a03c161007d110130003030114210f681c0c68055035019808520381c9603c41000e42412003000a500d40c5c15101075103804080c40c17031103202d80781c0e046114103024001c0210520316558800001078541009185650358560301e8000350040c80300c103d207603010f50340060060406007011011800ba40d4445420320100b003001c400c207641c02240460103a03102c0540051141e945040a0342003490000599500d4001c550401850303540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 744484460 1250 744483210 744483217
    0xb01030303181e02210703120314281109132d0f05060d030f17010b03090f01020a170612010203070216152109020901140906030601031e030203040b040b 67
    0x2181e0745e4412246044004162010920700075034581c01c0480140b010a040342681c0150807400c0c54000741d1920580315000791500709a0700ca00180c140085540050144400c0500765155400010800700e044074102100c20b22880e01c0c0355000396000c507020740e2400440c1e0320040860418074139444903442c03000c0356040e4113410500c61b400130358a040c046d41e81c1590ba61260b503103e0341c4040d10f05810010b10341c40c1501c8103031344030700c044080000100300c42613144407400c1224001c0006481580e1241031101c1c0c060300b05004d1103091325070340e8070600c80040c0d040d5200d519080300410305880000251110008507208400c0380ca0603804544c000400e2042869001802e603100300b8038204050200f44d20391000c03005d0420000c848900080b002482c00341114000c85101003000e841e8a030020b542029940420b0680e07200741d20421640b00740510300c200d13504042102c1d0750311240880103400e6560440d0b85003860324008081200700d000d030103c1203d0400d07000f00115805044001e803104d4499a8820b0080e10613807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 744485710 1250 744484460 744484463
    0x90a12050c06180705010c0c120c03060b0906150c0109080c0c0306100608010911090411040614030907030b130c08010c0e100807050d0b0603010905070801080a0b01030303181e 77
    0x10415001401c0f09044241d0040c6900c24400035000e482c0c41c0c0401181c245651040640c0c0520302c04034002150659a0b8610800324456441e400b00c052950411000b103580d40c2040c1c2d400703698404c3c204170b40c2ea0345101680f10b0280208007240e0f00d40b00c04c0d1002500410140b0350080400100149403884010002015140c107503080b8100c4034540ea840b810b050102502d44500320102d21440300511811000303401486070701803102110750030000403200040664104550305070b0303500c02c0002c05001d25940107116104d03040d01c04103400e00c0c604220103910364442c3d40e4803016090010600110300d172004003115080304145c001070350103000d58603070702028002c101e50140f0360003240b04136200200b281400384c04050001c24a44070b400c500d81e9410801e4919a009080319101ca40d41c030000020300d50340f00c4002c1c5000e410141301c0000c861802010241500310180c00c4000198000c6003e040000d01081000d419254146400301d080d8052482c207a100b41c005075001060641c4440c040e0081c9406080300d685d02a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 744486960 1250 744485710 744485713
    0x61002030c1f05061c060b1c0f260f132601050112030e15090d0302010f0c02010603120c06110d090b060604050d1106220303030b0103110909090a12050c 67
    0x303488004c10000c100d1507805400300940700b240104408118076910140340c03218040d0503245d81c940e90700501a0082000c003001c446c0e1480c43c90350a41031040c0c18440b401c5685140b03008110000e103900c260012805050000c250f005030000c1d407000300f00100b840c4d050042c104404c10340301d901c440c8441d04688650215600c010b961924000141c80416148070007403503a01522450b10714460802405000c10903115865510841006405c0380360726100c0168400500a0740001611900e02c0c850303c043c0c4030090303e12000c5a04280c001d00119402d100707040c81d00701007410804602c0c0c10384c1c5480c82c05440c0700020900940400b0801840120243c2c0180000d0361080b0304100b00c80ea608000c104180c040c80c080e1a802000e0100590b0004030040c501d036a11180051655043c145415031004400040f01003031144e28500075410410103030903004512070b04000f4207080c00030450240ac2e0107128000c10001d036229105550100c0c210003028045e5800203500000d5030048440c907160701400341d034000d101c141d509 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 744488210 1250 744486960 744486971
    0x3050304080607140d1d0d030228080f07020c1c02030d09030b070e040209031b01200c130e060c1e090f060703052205100203030f061002030c1f 63
    0x11580b0404284080f9243c1004c640d00740310300311501074018020a40303c0d0780c0240041001185041c0c04108040c001c50301540c000d0f07560f1418038003081400d582080c807041004064039034500540e4000a100c0d601400c80c406144580e503507420124603100c09103610720f070040035000c40c01944403903c5032500782941c000e5049484c1c113031180c0801c03641c0d405140b0002d8000700940700801e10540c81105920004040204090f0405c5c4c2c0400c0000d08104008094940f904580e50004142d541c00546485160b0610208040c120454200e6192100700000e083c0d4840c0700312008030002c028a41d4002041e540d100070883da580d14005908900c1e40e40080d1420034556070041c14021150070040c00c032004ea04010b001f2140340300610041c080c10743c0014104800f0b104042c44034410040e15070003484110780451804110b814a020203020b942c000300c14094085420400c1040400c60b0060f035a40e030070103000d50303040b2032101c03010604034110300803003280c413000f4010900c01710100321787d10380303c200f4910450f10200038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 744489460 1250 744488210 744488221
    0xd0819030c080915060f040609020c062530060611030705070329090102030402131a0f04020d0c02060402180403020a0f0f060c170703181416030503040806 68
    0x19125400c03101602503500c14a01e01030b054104c48140341e00910041e296103107a030b14040002c0c0580d40b590704112800c1c0c1d07000c104801c1c1c24a04102c03850700900a0b002e800e522601030f000850304802d0302c00c000c3d4144052491140740d0400d40103c125203840c3e00c2c1d4804c0f40e01c1d00c01d0994802c0505554420040044c07a0741c80542d00740800801159245030b0f01c1030042c52a14075690b03c090b02254003402e401c90382084070140300c80241d60401c1c514818480540010790320702d803d204001902c01014412071034140340200300788024070392504d4440a0101190060a03440c1d0304070006001e8030518144003000c500707010492452039000150b080c012031003252450101d44c0030f01d4000c2800380040b140500180d1081d407501001c90034090403c0b370084d00691850f0081521504c1d00b009440110450b240000e10301c2c00626402c40c2c81e081c01c5600404186024001d0308407070301c0e004688207242d00002c0c041080e10115014440801c0003000c40c10200c9401000c0303000d9803130501a440e80c10502c96032059000c0c0d08000346 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 744490710 1250 744489460 744489467
    0xb0102120301260703080703090906060912021c05101e020a050f070503190507031d01020606011b021509130204050d060b0409150605041409060a0b0d0819030c 70
    0x80c165001c404910441d040074950b040401540c03030303c0641090140300004004180ca01004069003030003134030740e202c02c43d1038801e006007214044e0b03100301c0c200103a00030300f440150760b61041070040d190129242c590700c01c298000c000c0e16038990b4900a1081c8155001054421426045107020b140106042200f000c0004181010f9100340901c40380010300402c103c40c0103041c100090164903005004490030018904202414024203e0389500420300100b01c041c201640a500012030101010010401c0e03031580002035036070200509841c0c18050355003034225a100555085000c0e99800501c907001c40c041071030f00451503a004444003402220184c900c0480c1c185c9074000c6500f02d070805000c05d000007480340c03070728001000440c8085906c1038071280000007065440d401c00c02010034a500001e0341514141c100011556011581c00c000801d010030400112408134580354061104000461401e8040c000618a8200180c0091002d000410300d0803514801c060b003101172803800e8504000c1c1d40700501098 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 744491960 1250 744490710 744490717
    0x10f0c080307031509060b03160215060105030a0f06031a06030a120c021f0216050d08030105060304050c06181c0b044d010801061707051c0b010212 65
    0x600300d61401c10201d94014482c0c1c1c00074848851680e6030302005074031003807500241d0b9001c6d40444500e22021050181000c4401c1180303025903420f00051240d00b9881e45200c0602c04d004200c0c81c14400084002580e4801603009201c80301000c40341001070a07260725000703c0041251018401500c265000911a81000a02d8000c025041007410b146140080000c5944005200341243c11003a8850418440360781545404a102c0c00d6402505803810100008000c405030b90348510301c02c02c00b049101300072804441c122415204141c501e1a5a9622800c04518100680b0760725600319400140b80051301015105581c2e2010044510201f0700c080444d28100f020f0070180042e1410302e000b004200080c204c648460810b41040710100080302424807071460403001c803070b0851038458800d003502e090342d0030007074030112887e0007404d084140b9414894001c0c0420742d0f50116444400c200e00204024a01840503102901580c440060911070382c7c81e00c0382c0103411184a0140544560742c0d640d049201c0c11000d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 744493210 1250 744491960 744491963
    0xf120708010f0e04020102150109050402030607031b0e03030c070b0d11040311220e030d110328020c010c03020408100c0e0402090a080f061801111207200c010f0c 71
    0x102d46124280b241081030b00001a1080b4154811903548003505103200f00304074000e0401c0321000a2502d4580141410808010115801c140c505043c42480e2980341044c40c4154049242140c004009180400d18500c914084a00307240700307a200c00203070511690010000040c0d00c81c000d2220f55008405505180114007000b0072040c884221790502e0b06010307011900018152807608103091800d10030710100c41040204088035080055541100e070098045e000820242c2c8191a1441c6010000410181d402214007404410101079100c0d000d201a01138400082008000704418801c00f0405002540280708254007801040326800314100c1c54031030740098030040d8440c2c08025000104000c001e600265800f42c0c001c643c0c0002145e03041c400c00106c080110800020001410f100d240300030030780040042d0265580c144503100707001c88505400d484030002c440b02c1c4c510658407140010341d0ba03103442200c90481005142d112100d0307242c002802504402c1c00380ca40c1915880303554001c82d00c0d900054030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 744494460 1250 744493210 744493229
    0x40503250c0e07051215011715010c0c24090e040f030e03030c01021207030b1e01120b030609100c050708091908030309030301060e0a0e160e04020f12070801 69
    0x1002c00c408004481c00c00ea01c900c0318a8410300d40030350b4551000d410704081ea41c20102007010b0702d5008595802c43c0c03280c89204401840c04030286013451a061507030520380e5869042041c9405d40c0402c0110244001000d041c080c200d800c43d10016501028a1070000c00c40100051a01c920029001c1020b4002c240190341045410b0001005502c00b5500940041d0001e90180700c200208482d00c0d10a10240900c4a441442d441150900110050949030061849841148040031019031400d4001c40c064038200c080c20000186e03c8040c80040c01040c5529105030540509010007035940310101e500703c3e440ba52400100400c40303020008540318010300f807009168400c10001e80c04140350462910b0044d011050a550600d51070718040c81c2160000c1d900c001d4203170300c044010300c013050700044908105202581c612010742d1034a42d441003204130117040c0d0350380340032040c07200c0d02c3e451b10444005c107142c0c601600541d9104600c1c0c0c0440c1d203c4e0700600700004916149000b00c0c4000c1e10503e0384c0e82c1201d00242 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 744495710 1250 744494460 744494483
    0x609080d1d0a062705030307030e0607021e0a150203041701061518120f0f021504060909050a0608030f0a1803080909090a05031602030a060504050325 66
    0x400e581590310640701802441c1007a22040e5141d031000312640c0a080c00359182c0403820050341045150019030509850000c440384c0007404075480000548503111f800d8640200513007440004a203242c443c2e200e001e90001c0c0c9908980f0340d02e081c1e10001c1607041e8019900c2d02c1c00160b440f400386000d002601c1030701d001604100410032031800030000c03070000c112140e4000660b241d0350700d80c06104444040d041102142d9107802031aa540050b010243c02800d9909010090075400d5913081400c0d580000014050303034012808405540f5602005c00500081c0d200c050750701c07a01c0f0503000d4100c003d03501c10051325a00340300008011901c0d80c0200421206000019420b228903c01216207603000602000100105010320040b28180417131950300840c041c0c0c0314240c0e60503c250900c88041c400501034110303030340252000c200051000084806400b032070010700141088910000782442c4a00e140500707840c0c10001440141710b0301200a11620381d01e5820700d000180e1070307040e0f106040b00406000c0c4c000403805 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 744496960 1250 744495710 744495733
    0x70206060d051e07150309030210051003082a011509091101030507210212090102210a0f050a24080d050a0507061a012a020f0301021c05060a060908 65
    0xd85100c0f07480a400815070314103d031910070065054640421550000762280d2440c01403503014800500d00200c045070911481c6005c03600079090110034072000308400c1c0000742d6074076100283c001007820400c0100345500341014001c40e01c0e0180103405000300501d10a400b000400400368811450b4041c3c5c8081001420600316006400400004007a03509001b10305550440d80311484494803e8003199000041e224245201c900f542038800130300c00c0405a10402681c034000c002e6603424901158258046441990ba1401d48c0001d4028290482615800c0009225041c0c003150404105810540c102d0001004030748082c82600396584107507501c3e41c0105d003030741d0030083c07003000200402e18881c01c0c01490403410b940c641c403c42d07407040c080c040a00c0190841800744c3d0b9006007003001d5070484030340c0402c003801d01c48108005003003130000c028407942c40c030880522592401e4042e01c220440f4540320400b59131008000c1000b50004541c810b10501103400e0209040f409040341c407043d03420000c018040728201 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 744498210 1250 744496960 744496993
    0xa140408090117070c05060c0a0c0f0309090903091d0610080a11070b190e1002090411070c06111f09170c0f24060108040807060203040308070206060d05 67
    0x1c07400882c1001074010150007400c0050700b2040c09002c4550f01c2804103081410943d06111001c0e00011200d04100402e040082c2e04c81c902031006504035081d5800c40c0742d079207016038666409920061940e401c0020300014143c00c1a41102181c42c641150001c002c42000303030300d42030402112038a40c8944000e00c2c41000c40c2c070504005a004580490003e14502510402c801a401c9400112120318000e010000b4420303030b602803c011000514424014000e4007041c09480f2a0070607248425140c0c00b050743e1241d5503864005940104000c284217540342460705091844421070b02035000440c59440ea070034024080000e20f880400c205c04032168030700090804640c09450701d4801981e03191400e100300505014064002d0450301c003210002e142103c19800200c0c1041c036400c0b03048070000c03d6000320032400c000e40c00d501c560005003464220001d943d103140c1031081c1d008014025207001d1001c403c1100f01900509101d01403175440d02191015a15042000751810f158240201190130070b20140407007020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 744499460 1250 744498210 744498217
    0x60901030b0a110412030f0c080a050a2003041a0f0403080f2a0c010e0918070f0603090201200a1103010b040213050f0619080c0403051005010e0a140408 67
    0x1141c00010861070400c80e20b00103290455042a100c0d0050045c008081542040c8209148015030404c0390000420351150740c0c1a000b40703985202403040c0050a0600d15116101d000886503844514240342c0c1080310030150b0340d400038000c24180100941d620032445840e07009451043c0d01100310145001e00f565201103060300000118890304900b8440c0c800e900118410510082c41c0501c038103880c00f180300caa410310702003041c004541840380e40896159580c9441c8a00da81c800000c01d054401d00300e40804081ca05507241e8014a0580301006000c188994507421880580d4000d0781c0310a003075003814008640341013481c04410303080e91181c1d0102c0b00044e54484c110303030031207401000003540700314003804201079034891800c0c1c0044900044050050b49003402e080f02d0200741c1680c00505140212801030651046061140c042c00840b40004000040a2080718040c56100040d07520001140719400050b04081c0560b50030552848002222a1401d218111004040e401c0040050300c854859544507030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 744500710 1250 744499460 744499471
    0x1e010e120a23031e01060c05060f04030905060a020a03021606020d030e0712060509061f14030316060c02010b010221070c05041d0f1b010e030a05060108071d060901030b 74
    0xe140e007805407040c03451801552080419141c180001079842c2003204100313005070416810701010003100404508001140c6500c02e03842c12280c3c0c510b84071414246d44e901c1403035201c60380c44600050b41d2900700340c0c08503403525454800c0d000c9036909800344285450841441c09550f006034031507074015402601c40d0b00403000c01107071481541e41c030544a000756141c03c100c0c1017081d0b800c0e0b13446005102e2083e00411050390300800d90f410702108412140385001728032109116259a2030300814003164103030b41c10700c1140e01c0a0021071040741d0300c001c14035002001c0d001d88801140954a4100100ca441d400400c10400032040b0710f94040360750300d0710400100d940e00511000c0d03604400c00b00001c40c4a0325a40701e9081c040c40b1003030103000803c0341c51410301d16049580150a2060300604840c0b0410703d0058011460218242002000d441000022900d0400c2134540504903101700f100000c0c03a0040800c080040d10301c0704440c9980d105840313070310240c0c0b1003084d00c40c207400c41c0c200d8004101150310300d191341c0c0d00312 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 744501960 1250 744500710 744500747
    0x108040813090f020a120203011208030910050a052202061c090c140a120203030f0d02130e07110f0606090c120c040f12050706050c07081e010e120a 65
    0x90320340300b4a604803428800302880c0c00d6400611039024540180c0ca000d02608101010340c51503040c401c41d03115090150400510654002c0b0110b815807009004220024051110803c66460050642c20142c03109550341c80d50a0914029031100d400c0381405206440d40241c05185020078100c555059802c21100c01d5040315600c05503440091641a0720200402013081d48101060440d020030948007015844440c41c000340102d01401601c011040d00e915021104c000340d00c50a858102030003900c0369200e120a1042503500c00304102011100700c038002c1c17040ba034800424424604050355030316920368100d003080d800f4000044580ca0407484440e03001c0ca81d01281d50504400c4440025600000e0303500070050b010224041c40468801004503006098100d0741c50390716401038940c2902e40c4903038059802048000680c84060940810060707008201003002c441d02c84410b5960001d403a2460b141000c00e035400c01c1551000c038000081d408610ba201c208001e850004c0c0d180054a100c4035040203036841 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 744503210 1250 744501960 744501997
    0x2090c16020603040f14031806031003141506040915050408071203050a150b0a0e04200306120f0d0f02100f0b011107080a02010503040f0c06121a01080408 68
    0x50302d030b001c003560040e07200e41600c42200c40149400c51000000300542240e50f4014402040c0d00c4201c0940d0146100c000c0e55aa40d59480d403126110752151541c0000d040d44c40424080210f8410000315611280c004008513100c544800c030070041511005100503020000300300703540c03100302110b51000341c00038401d00c08503250003000d40da040d94010603004404027081d03403102001400a1540284e40100d003255407c140b2041c00c1420f0955280500d82c0a9030411620014001850301c403a0700c001c083d0120580c0803410745000141800711a07000712403030381c0940c0c0c4184a00d600190002816011102c0000107000000840c017001c1b9003103850704580b08114410b14a100c660600b5030701ca40d06404011a0010664031440000940001d1400301114002c1c0d000c0c40040089420124001d80060b5091800680d02c1e129400d000c4421320030014080c00022201000148594005804c400e07009240041403160081034130140101043c280181d030b0100d4407990002e000214840010301115010309004083c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 744504460 1250 744503210 744503213
    0xf090402090d061b260f090c04020f0d060f080c10020c09040f02091f0b0a050f0a03090b0108010203040f0b060321130b0301140f01050d02070b01030c060203030402090c16 75
    0xf0340d0003441510130400c0c81d0b080048801c5900c00c0140c2c04200241110343d45e840078488a016200900500c1003070040c54040226140502c11311040d00c80d808001c00175134407101d894642510580c810044040740500c1c1ca07000190007549006000708560480c0082c00e00d41d030265090200020080c2c980108502601820b030701540d5a5021280c0107501a2800d182500401e2060000e000005401040c0d07035034208003100e1207065500c003504c3c10340e044044842e440f11074116094070b460041c0f0841902c1c500010940070001d95060b4000c0001e18000c1030031101590381d900005080348410341d4054022030a0a10745404075420000250f04172801402701c0b4030601c01c3d820b900f000401003c0c14100450000141d10000d148010801c5001e0107180400602d154541001d1100748808802d005000301e10000d002c4070340f40c0c05002910743c601101c00080d5910b00c46c030316119082070000d00080390003030207c0c1d80220310144000181d074442c0d94054000380b01c0352031314188400301d81c11801500b0f02d225455035000c030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 744505710 1250 744504460 744504473
    0x80c130504023705010503060901031205040803030c0d060f030f0b0403110a032c0d02090a020c070b0c12071a10050a06020c0f100203030a0f0b0904081b030f090402090d 74
    0x2018551034000b611480510700400c41001003484e407180c5c0c1080028400d0001556621500c181103d0b0b10880581c2c641c40d040c1c4060700d060080d40d000e102c4038080481000001c0512034010919403001101c200076040d182d56007180a4035490001401070a418000b16001601001d0741e15080390103410890b48520a049842e45401040c2c079003140003a0030600c0003580c0e460300680480240e4043ea42c403c18648084010031a80c049022001e4801c40041e0046086600903504440c06003585800307441085490303844208840d40710000d002618403030003001c3c5014048082c1070356110303039003c80d8006c1d01e0481c082074181011000f502002d00310140c0180015965910700c0d903d0300038032468002d0310400f10304008208032011071240c0c0c0c9018103102c0150440c003a0b804001c8991200050400081c602c0340742d41640014000f4002881d000742e56202031106100c1130300701500d401c8040c0c0c01e00325581f807007a049081e100d0080129a032401d480501000d040e528203500500350400c00940340711185003894490a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 744506960 1250 744505710 744505759
    0xd1d0316170717090a05060f12150f060706020706090c1805011a03040501240306050a060b0a080c2109011b020304051c0f210e010f2d0810080c13050402 67
    0x9034510213002603109c261002950f2019440305040403600c0900241c9004117440030441c0f000c0c85c3c860800003a0300c2040240750782c140d030411030f00a10b0820100c6101d10307004c3c21284090080da03100c8030040803004c0c01c40c40e560280606940f90701c034807040041440c503901641500b015104a400d035403640c8044044901c200e900202241c0c04040318003009256042c04422100c1c06005061142e040c540c06010041c061000c0300d40110341858107100550b180c0b00b142e1214050703401d01400c0e038078064084600400366160614042d5880e04020403010014004001083c450b54218001603001070100300035600c2c1c034440d00c2440c00040c001c0c0001e240e200d035680500000981c01d0442d04814001c1c00249241d00126049040d1509406c1c074074040070181c40040c01d4000707045040d40030001030b06141e2401e10046406002400002c09800c0741c00d0f403c42c0350181001c00100e8000500030f000f444005450704001030080040300b4090256104100740d402444042c000007481a81c01140280394071503c00c1259911 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 744508210 1250 744506960 744506977
    0x70c02030109081305010504030c050f0a090c030917030f01060f0507080d050108120c150402040204090e0d080603010b0d0f11120709050a0c050d1d0316170717090a0506 74
    0x2007555404d010010410102c200390812410030000740803e00c0050001e1000c9800e8400854112184000c2440022140c840f03070b40104081c10f00f88120805050380607001401031a1140f819500360141d1159907400c0c5020490741c05800260002c0100f1165018030402c14001e0806d10f0547e1400e807043d198030880741e00004914500703503510070040000c09070a020088100001c0d525140c40c00051520f070a688400031054000e204000c00f01060440d41d555046800030a00302c0c1d424040c40358003000303075500d0b03840c03084121001c55001d4000410ba0b14043c07141c0c07101c2090041c0046004580c0381c41c0e000c40422521000c4406880c0d91500300ca955850350742000f48020400d000b4441d45040c06c041d04107490014019991081c103200d60751203680c0c1c001e0203a5405002c800b60005102a0f001581000301c4541d080d021a00d0000180103004040c003400880011800346030704000114681c1d102c6100c5100c2d0070b01c0a0b00c2c1a4a60f03040001c1048280c4c0201103d00b0014004100980c030b510004e0940d0740490300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 744509460 1250 744508210 744508223
    0x414030c0a0c1e0815060a170c150a0f050d0609050f2d04030f020a080d0b090c0322060e060f070f020c010509240415020f01020a0c0b070c02030109 65
    0x1c080140410107061680300f001510f14101c403451600100680d14180041551500c81c2e4803400201591208901c4500900901a0135082c000700480c44580b501014030000b03000e0030174884440000d00780fa4040301d1186865954009500284550440e850b40200b005102e00c90381b44c910010b000911030040c140201c8044401c414103003040a0724000605030703510303820000d10742d007113290101d84d5808020325441600741c03c1c60040740171545412810010180c0004054010110390a80c07110030590100c1120030064405a01613101d140c00445075010441e003000300c41440000826564000700c40348403525200e00d801058040b89010003505200e421604004072000100c200020b10b0750140c8001d8500115002030035806000c00c0c0000c049120308201d0300c4c042d810b142c001004582440060400c8076515998040d25140c40c0d442108090003071011160051183e8030104007070090620881c0c6008415403201048070034071f40d441d55040c0030014040710911000d8407094025031028000c0d06c400310722a21 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 744510710 1250 744509460 744509483
    0x905010b0418090c050609120d0305010f060c050d0e06190228030905120316060c03051b0909074a0306010e0603010603080f0409061a030414030c0a 65
    0xb00c051614051040c0782d00c2141802e80d0f66021440048843d41030f01e105032101c558404100010400c240d5690495040324802c903409410159415440703070741680c804900c2ea10307415a544004454a5062100142c01034101c1c400009003030b80140034203a0101c2e0040c0940e03041558000303018180804080000f00580c1281410241900d8140e20004541901c4040d110680c400e0351001420101580202030285080c8450341000540400545112460446030245005120b00c0d044000d85032004c00940401d003403c0100b8000c03003142c400506550300e00f0040b00e0810300604200302290300003600200c203106600240c1c07803152440b4001d140030142000c20700308104501c008821007e0140942020a042d5481c02443c83c541c1c010812604407400e41c042841d03181c56900001c0c0c0101031950001f0408000022141188e14082d40a4070880b0b1029004001c040ea43d2012400d8116900c1882140c0c4802040054009000c031800c201d06001d281c8116828008001d4002d403030890b0b60402511400f5005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 744511960 1250 744510710 744510719
    0xa031b0e0405010b031e040203030c0a050c1e09070c0206073009260c03190c0509130b1005062704150e070e0a061e110c04090c0905010b04 61
    0x10301070b450040c000400300310303c2c5150a150340b01e80c904401c41060080d0003035402003015540c040041d1120310143c0021f64440f400645444c1d582c0d04203054041e806020408007044000341c424404500c40740300039100c3c40c101e60300e1840403180c091900400700d034001c40074007803032012486e91510400709081d03e0344502c04a26070f0000c2ca10181a40c00084010004100e0082c402400d02c018926620b6403030b06c22076003a10310b0b1980d04504104018400c0c6806100b0340d01946400308601c0b662147c0725000c2d0191040c0c464840d800d02a10041c1100c554a040b40041841070000d00082d29260f030125515003200c16468841c4c0012301640e0180c0603083d02c54030402c07088000030740c07402d600d507940b030800312400c0201c210602c03030340050f03510b40b40700d000300002600300040d00d0180500c0303000c5000e00004059003030054481002030700964109145060010030321030200401e038040c811000e000c5841c00020641c9d0801c0d80c0400000e04500401210045846440098a0813031170007201e01030055807a41325200d40c1030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 744513210 1250 744511960 744511969
    0x22b061b23040b0a03021803011e0b030a050d0503070f02010e0613031205190612020a05220504080310120b010b13090e0a030f08040b04020603060d140f07050301200a031b0e 76
    0x1780b807c06109900d040103000f598950b10444030380513030030f022010070045820320010382842d02c0002c0241c05805102101c0e1800d03a0b011000350701c01da482d51150240100c40c1c52040b4221001113a030500d0383d50019002c50301c40a00b00b103281403114400d140a02c42d030500c40c03c00307000340c580c1940c0010a00282030700d6892480078500995000d85a4440b00000240036600041d0818030301d8450107024403030513164401e42d000070300da1000e64220203103000d0145080c9850b00c860b81340e0cc1120f018024810000b00421107080e05100c0740c416a4008040d40c840c1c1c0d080400104159100008030300380c50300c0001000810200500820401c811664054442c1090310302700904000000c0300c4000c100041903082100062409a5164110307405a80140d1659901d402040202d82c1c1c0c400064004a15070300c00c41d43c9000001001d40c2a038680205076944c441c0d9400c207060a94050100d214144a031000c440e070326510302040036241c5036055103008916034140901455148140692407400601c0c00014034665061 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 744514460 1250 744513210 744513247
    0x91a010305121606021e072105030903120901061703030a050c0306130e03160506240a0302040e190c080c1804020d022b061b23040b0a0302 61
    0x82c250100b6241c40d0503034000d2114103240f40002001e840d4080740c40300a4200e1001903c0007030b1442014180e0302c2086050219182c0b41c1495040185120034070038060092082d81524007902400d001181002c00c00c0a032144c03118001131024030346641e540000502c01207202c035610041d407600d00103150707a4180b0090010a0700c40c01000b40c0396030b81c020814004c0035142c0010080030640030b110001a21000310032036900314070810a241c40900e80350070308141488400716440b4010702003d154005050320190060b4801408551104d5014400c19800c0002d410310741c000d0151041e10340b00f5100707207015204000c505216210740c19181d004410f401446100303010004240d446008070f41604416034211640c905d00c11000340028050400c44013030314219210700441251030301c14203040050300000812403c28640c0701c04801d40d42e2604020014004155040c1980503e41e0742c0d035907158031005114240710410107403100801d400001080000f603480c0c0c08102408038100c4a580143e503c200340e01d8502c840380e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 744515710 1250 744514460 744514483
    0x6031d0604030e330a020f0105010302060d090302030c0a0b040209090703170a200609150606070b0c0705010c02010c09080f25030602030c131a03011404091a010305 72
    0xd00010078400400d40080c030701d188040781100c840c2e46107000c22038841d06815014110001d40c01903007011285601607103004e450b40040302c0d03007180c03a414485480c650a82d4420312019400050800100301071580c140c10207045d15019004403841c04002003d002e01e000d0703003608140da56004104c00e0008510700740040702d8100201e2801005004c0c1142c403552211a40c19941402c80380d0000307207000c0f00c14068820001000702d81d94415040d1a81c41103540e4440100b11000001400350103c0220b80c0c4012601c090700030080604614140b8001396641d0301c0600c8040c001105c20402800150005030090040014401441e800481d2200d18204080d26404c0290400380094210018100200e800020f502800b181360b0000030300d140c0140c141013481c8000d1500041c0010340000200580c203580640202064036000e04852015540c0740c071507900b01010161032182d081c4c81000100081c0307000c1c62036005d000070300400000300030110307a40d081c4103103407040c0700c082c04801c3c408010000d01500f8401c245120 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 744516960 1250 744515710 744515713
    0xf04200d0c17061915051201090606050303070507030206090301111801091a070b0402010e04020706060807090207080406080c1c0f0e1b2115100503161413050106031d 73
    0x1800d06411002204260361003a02c4005d58443c9582c03034800344080148010180a8100d01d110f604c45143c081c007821401100307071070860400c54000b4036401c000003102d801c42e40050182c14160308540c20400140e2111240f16071640d200c880c0c4000590400005000014001c0c002103480a002e5001401c41c0b40540d00c40303261400710864000c100c02c2802c2c201da170001c0d0322000c2c07081c940e5580c0c8016100380da1042c400c20b0300188040307483c0080091030341c402c0066951000444628940c1d03086000280d100b11400240480e00601c030400209010b4100702e5080200071080c50b091203000840c8441c0c0043e0800b0b6000540c0d141c00310007440500b20301c6107115045002c0d01410307e1841110103184c030b1400c07017403055003d4500c1401303450008052070581506881103009581d050941f04580c080ca5480903990461441260301e40098031745000202d030b00a4520744c0808030710385413800c039040044403100d441081d0005402c4580c1c400d00013075485654003070079054800040060b0f01c1d0881c04515070030f502402100d13 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 744518210 1250 744516960 744516973
    0x3100918030e0f0d060504020121090512280504080115050f0a0f06050703030b1305040209010b0a0e04111204032109020a030f140a0b070f0201050f04200d0c17 70
    0x90b81c03a00c04d03408086a4010700040b80e40d445070f1004950021400910b250444400000c11810303040a800c419280c6000350100ca00780031841002d007901e886981c01010340c0080c020750301c02c241031449104290700304507030420b20b050650720301c005800d4903009031441211100604050251340b400c0403202e44110410b907000e60710389041958400401c0c2e00c6004180c01d00a02140100400d032007a0882c84c140c140c017411845c00b503500c0c000d00320054581075404a100e441070700008140b40c89600d003a6001607089030f07521084000400c050100800e045c4840b00e40f00d040400000d54051404000140507078400c0d610851030103d200c40d00350ba429055087c1c03240c42402c05111a015030b5926441c0c0c4c0c01d91340c0215010012002614011050900d0030079000c0243c041c81c030401007806400c8d6a031500c201c940f40c030307552460034174175034120308079070044a00d011300c7e49040020401249010b90f41441140b40d100300001c00d580700c00001041000018001c42c0c160040b60410702002001c440405120100540100031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 744519460 1250 744518210 744518239
    0x14120d05010b0715053103030e0f0c150405030d0f0e011d040c2604060c090302031c03020d02040b0c0c010c03020d0e0d140a120e1503100918030e 64
    0x1501c0d64071004c2c103d0000d4540e400301d50900000b4141c8801e501e0090700c202c8603401196290301c0c0340c0500b00d106070080b900c1e0040b40c40d6046c401186071002c206c50000a841020480f104100d030058114000c1600c41b00309000110303050310100301703800f00d0109903200c100b01c14090b00341c0200003c14040d405030400c031445a00800c02c20615110b500f080d0801c59001c1090082c0d003400302c03888200504203440c8441c0d01101d802c1c1d00c007842144540164060141840741510b13004040d2489000361000075015840000100c00b0300340c0c1000e450f0b2894460346000361820001d020001c0a9800982000010300e10016202078880300030020914040030a080c150095070362510040d41701c01099003558103210329050b44410981c0d49010341420a5449400c0c00840817900350010303500d0301040401c0741c041c2d030018140c0b00d0050240031603205102c8020100705860603c9403a454080c2c0003d0b02c214144d14946201003070404607801100d91080c0d1505905054071510300300100300a4041da21a80190241402d007074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 744520710 1250 744519460 744519473
    0x10e1603060e030c0109080408010c05030c0406030515040204090c020709060f0e0709080703061d1b0609030304050a0b1e093001050c0301080d082214120d05010b07 72
    0x41100c0d04020005000c0c0b0010081c1402c42c0f14514041c8015468404108200111200900240c6d481e032402081482c031000026960323880140e032003c504072024401040310510941010b5885a8056800c0450354040004601641c2041d000045515242c1c52114052750381089044018225480203000b02840d0448403600629079010340010300d000f220010b80c500780a0b5507584000c10f101d604440c1e18681c1c0342000302c020901440c01b202a4181c03032411408003540000c16020a01d8911001c820f08a503c01c20000941d001c42c4080d50980014407001903d5901c100e02e0000904000b40c0c096076401e02c0114405c0303d00d807212420411900c00380040314241d295411840c40c240749d1710b041902800446a1005103490075880c90150940c208400c002319000700320f01443c100c4074884c0454000c1c0e03c00850540d020541101c0d40d01080c034001c6805d5001c2c01e01c90381524a20741c060882070710360b091200300c40341c2810441d07074100780e00360000030300490f0307090543c0310b60782c010301103070000900744015907880c007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 744521960 1250 744520710 744520753
    0xd110616030903050c0d0e01091413050601030908120417070f0803070c0b070903060e030f07020f240a081503100509011b0c020a090612061e020c01020c010e 69
    0x510070141c0c0c2c0c80010701014020000c81703440f010100110f03080d035014030000522006001c1811800130b1984c1c0c0340012440490301c0d452036602001080004004940c08400005250042219040648641400c0f003c500c0305030003403405d40740340400d0308021300c1c02d0700301113140340d03402c141000c1460380030040500400d602c1241508080d80c000c28aa5983d2182c010484840c030545a0140c490300f98902401402074008400c8011207110b100c041c01805170300b1410588900070064066507006040194000518005200f0030940800034082040950307032040c4022007240304401d068646800045410029420991341c544c0b042c100e01007880c004803400c01181e00ca05031685030b4180742e0780f19000314442e66000e400014500d5110700c41301a1010080c80000c0c809032512106a0260301020313000304001c10640035a0341500e41c40d0265240c600841e54401c0000c20702080c3c2c0400c2203602c005c078802503007820f00040a07855208800540c441d031141d03034100c0c2101d4200307a0010044d4000460340d4480c2070403110f003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 744523210 1250 744521960 744522001
    0x8030615040b0f1602060a0201090c05330c03030f040c0504091203091a15040e0d020606010f030b060d020d381206011d0703060503030403021003020d0e0d1106 70
    0x56407510900061300d4400741031380034025480b80c0042501c0003131603030540c80040d43d280229101c1c00c0c41340d6580f00b0b10140851022410200c1141e110000d4541d41c4c5241200c42c690220880b581d1500c1d180742d24107404e603081614150031400c003000c284401e01c00035070144400fa000880c0e00f040f44880da41d86410801e00c40382c0301710081c152110105030078800121585c103102d0180050402407841d1603102c2c0703050700e8a5405c2080c800c905d49040c84540f1a00003400035034401e019001009243c8509005580700001103000702c2c1010703114070000545441c0d1401810140350405005600c2d84481122102940c4c400000300136030413101004558521500e42c07031a4105100d0010184842400401103074414603025180d80e141d1146e0400000e84031701001141c44035050000c0541103d441c2c0020032010303108284030380c0c1c1e450761044c0400d0001d440c022840001812a5090051404440c51581030944001e0010340e48150400040301c044680c0000384082000c880c0405003120385480043c01020305071030300380e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 744524460 1250 744523210 744523237
    0x31e0a05120703020d060602240108120c0a1a15040209010906030b0409020a14030708070b1c0e100608060108011404080702040b060d0905010c05090607060b040b060708030615040b 79
    0x1040d030082c0680d04581e0001e07000e617014000540c4881c406581c640418100e0002450013070075003100310705131000180c1030703c0c0741202400b4001c4c0c90890008481d04044002c100341e006008840c00002c103032042c0e50303007042002c02d1800e50502c0c0084842d2180c0420030001c0e4010f900401c20030400780e90007104101580d6075404e00050401c0042d0218009110320803000b904600d144101203084100c400d402c9082180450843d40c1c0075882d00421ba880d075819210380128071205010600502000b4040b1403c010340005000455034501c0c3e51041c0340c0304100001111301c90356414140b20030001805003902401942d0000d20031018050f11050780b80b000180058206031000ca0724104650380d5400071040020010170031f42d00c501340b1a84086c000c0155920071681586484070b04000e2900400c262158a207000f000c9500b00a8652035000c040c00030340b5859680b15642e06c040040c580d490b00090640031b400781a50703e8480c03500400f808412a900f050300420180b042c0001c1003440031110446404c11000f20 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 744525710 1250 744524460 744524497
    0xe0111031204031b03230c1b0310050411030709151406190914040912030c1106160210051b21160215150d050c03060702031e0a05 57
    0x50499643d6821200501c20513004d69090007815444001c84100700340300e0203117901c0d10512065140343c512980503260465000441c1c00d200410030340c0c0402980c034402030262513000c60300000910450b0340c11101103401041d000441c01f81b5003000c000200c0901f4010104118030380a0f030a803004a81c60a02c102c20304604050100d00740c94640074252045900710f0904035482001002002c0c0c40e60210340100800304080034034105c1140342034002c07041c03282d800c00021983e0800010003100500f0342ca644820a0150b24502401c03401c1c1c041051601c2103844036101d00ca45009410000d00700540300d000001c80500f001c05201c0b00e03c0d10b0f4441003d00080d129003141c0c0c1c6100351110001428005590744a0420381c00041018034010200030301e4280003140d0984084800001050400d4a0182d0b02440080c1c0722500d104110300341038130120080c1e8050070403603501c0c00c50310000030b1801d0000c071960001a000843c1903200910304802c0d90080e003502c04103a900f070400996000707089010341d4080d04100034009 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 744526960 1250 744525710 744525713
    0x150901030c051302071a072618010b09010e09160e0c03180105040602091216150306080a0c030506060123030a061206200702030307200319030e0111031204 68
    0x640c1100c20495001c0c0c0e912040e05040c0481030300150b1b01b1280d01001ca40c40440301007010388040b102e02c40b0901a92000312950300e6190780c45082c401012003061840d96910180903841d690098000d0082c06108880011442d000100e00d041c0180c1800281e80744900b440c06002400a1a00b481d0b40500b010500315100d540360612410700e00000065400c0952801c81800107001c8560000c2c0301410042e1030701a01c2220080328565101c4101e80e0840d40642015001d00148224202d564100031440c940480c4042d2035945036410035081c00d20803103101040d00e004008000c02813100076808032090030044403600d900c00c13425118091074a01042c0c031080020020320050305561211024000300c90381c1d000400031034902a4000c18820190b0310b807440e002e0080c1d000c401091700840f1030141d4064051428a020b507a01d400440300310301b9000d400046020700403042610204000c080d0a07080520742210420142400b03012410458400ca04006d0107189692404100000316885581e100300d1a4210380c3e2207 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 744528210 1250 744526960 744526999
    0x2211c170103080d051006050d0c0e21071203080a0203101a03043509030a06020304051e2a130609020417211e0d0203150901030c05 58
    0x51140d116030094000004014096404050420350740d040104000c0d94644071100800c10b507442c414600095000c02015044d2030007074001480c01803860929002c1100328038000385540544240da41c000c2060318a04101914081158000412105603002c4103004107403802461070000514400680e0b40010204080310b241c40701e410001c0c42c070002c1c02500346000280c03043d0264015501078418241d81c03214550400403002e01002c03140c03148a8804c0c1070750514017104005030082c1001503851b000f194000800718502e070004500c218841c0c0041d004900038445010342030014804508819440f180e0900c25041c00412901312000d0010b01420007a80c4400010b40040b1204803804a02030508a0024400f800e80c0c01a00564100c807500040444406440541d00c4014034410300c480200050400c03d80d1101c980208950015551a80c00da00d440003220036a079801510760450840d400810403110409034428036412510840c0c03d24a1549140c513801610310881c01000d212301100600300120901 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 744529460 1250 744528210 744528227
    0xd1103090c010c05070b2802060903030a0911041a0307060203030609010b07050a0f0c14011115060316060909140615250f03110607050d0b0103020408010e060402211c 73
    0x282c00e070f1881e961400c100390391f4500c00702001010010390403250009945030000c41d1076880307110351400540c1140e07a4080100c01802c1f001c042a2a41d02d00c10321350b610036403601d0144003000c0d410b03400350f00107a0256000303252030508242d0004003150000d101313011941d65900c415a045031101c02507140c54a2050802c3c0c0e080c009804c00042440841d216850108448240104100d90300da036112180b640300c240064410030120940c3c0e01d025003101ca19004403a5542043c5074210300050101c441c0c20503851542c2000e680550060004181407130000c12011516000d03040c140e00751241e0344410741c02c0900105100104140380c40d060404082441100e401100c44100c041d00c20203440c00d1810941070810900e10940300e80250b0024400d811840076001d070002d0880e00a00310760f6910761074003030440a01001842c1034140103041580800c0300042c903400900071405024415400740c1443d04040c41002480e03241d058407000311000e40c0d00500300403080400c441c0c040c4c0c40b41c42005c400100039060111034a51 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 744530710 1250 744529460 744529469
    0x1311040609090c03050106090c020c12011107080c0d030b03031c0b0a180b09040507091503142a011b080d090c03051002180d14120d1103090c010c0507 66
    0x10302d4020481c0900030260012400c89010704001c02c4440d031903401e20b0094414002004016910207426030545003801c0c42006007800800c1c00004001003042209030f10b59000c007105071a40039001c00c6004006030144490340300f405260504100d8042c910001c03075124010459031080b1480ca4848854155000350003440e002c01c0001d1244012a8460382c1a0080c40045981c28900c00c6c5400005001c60918000050244c1e410500401c07200345451122000b401c2c40350030304d0750340103100080000000e01c903400000078403845102404428801203640c20356012820880007140c0d02203004a0000c0c1d0300301801c039541c6603d40c0c0b80c0c180c80d02d0700d07803d04c40c089106040d202140c0901d0085c88209000070440c150043c0c0c2d229000751030f41c40e070740a60300c074080c0c1c021040448000c03400592946600e16250310b60000301c600c01e101a00d480d40302c030b0238910b0034450321088580500d580000e0840310f4041d944254800303032901300102030440c203041c81141c0d0381d168808101410320019502d11018410100503100040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 744531960 1250 744530710 744530729
    0xa0b1f090509070309050c0f0a181b050a2d030b0303130303030603050601060302040f050d2405012c0c07081603020d09091b030b280806070813110406 66
    0x40c10045001401040100815141b030b0103500e01c049800d1804080c0c5a2641400806100707205013003100214400d1840c4407140000d580c3d4194030080c82c05222881c00807204151503403911341400800203060441340c00025404410306440d002000500c0f0040c2c510000414900002c030b600b10500807034034622440d01e2034100d000718003900104042c1d042d0000401c0e2842103051b15100c0c0d990b40006c1d8180e004500401c2d8000480d92000e0200e41041803035640c4286c05201c00c400c000e40d01141021081c102034101034110ba850f00300504c000c440302c9507120710348022001d864240c00d9510010405005d000f4140e4400820009240014461b080007502e034a1200105101c503880c00364540a582c030724190940d0808610388042c0044e0841081c46408070050301d00a00c801601c2000100314000d0100700105544000c080407030755840801c0e01d41c1d406280c0716142a20100703a0414060518100d0003d110004000500c000c00011015060b602046660702c80c8000c00400d0348100014040d20103034004000300c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 744533210 1250 744531960 744531979
    0xf150a090507110d020706050a121e050108190f0203030c030c0609070b0403110f010909020f0c12133b0703060b0307020d12090c0e0f0a0b1f0905 64
    0x481020360001e0300500954440c074440200b080086925000511031242c0035820404082105902a030300400c4813500d980b8081c0020f8038a00704400884199000902c1c0c030586443c004e01c00c1c0d2034184111409414003100a0184d801d09407481300014000c0d11004008440c0511400215201007041e10b8040c02d10b2019a601c82d583c0d078003503e0703542004441c0517823a80b25400001803000561030894040e83c1d0401402d4050000c8a01486664098406513a041004680c1c0004020082c0d2000c3e10380c20410019841c1e407440d9411090340341501960180703404043c204000c564854214604908a0300055060b5006651000310031801e04903458007142c1000354640c8920078100c0b0324100790302c41e19264604100d0b1540707400031400300c0d02049643c47e025034056061016100c0c000d40307030061104805100030039805000c1d41c2c5c084c012482d95009a02e803502220070701c400c00b02545109507100325a104100200381300480090500d000409421040800d00d0900040007407180e40020701422000d041a0079 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 744534460 1250 744533210 744533219
    0x141309122a0309030b07091502101409070303110c06071415010305072112030209120313091e140603070e06061e040e01030c0302040b01170f150a 64
    0x611000603181d850250001e00c0c480040d100641a0390010715016a6103c100c103003180d44a11112001412207020700c01c48900c002036110001441c2030150009034080c16000d820304a0340419030b0040c0902005110041042003142000000c0c100102d17a098030300031b610010b560f150581405e060400254004500013210024094945402507850751a48112001124201d10f6040c0710301d070a02006040d9041180304200503200000c07224540c80f1074549003446c40d4802d5440c004a0900f450844012940209045480f86881d075401c3c00007010314000382d80f8010103008100c00c0310900d40140701c403450792180041c040c03601200070102503c1155400b0806014030b00e0110507001340c12a4264441d1003160320104091075076540540c0500b4001d004107040a021003030310340c01e075000c002c8c011a00341400e1000041e030340b10001d070203402180940e004460483c1540144019500018226418460500f605c07001c0c0c101c0d01c050503030740050940c03c50580340e1145000485010b1464a902d6070028a0010108 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 744535710 1250 744534460 744534467
    0x50f0403060605010f03020a0e091b040f080c010203070f0210110d030b12191203020c1b0301060f211115090405070e06070f171602150414130912 64
    0x742600c10913214071322601085d00e000c41c1a4800e1442c0400042c440304816501270601d0800e06810042d040300c403081c01c007135a004820350354010394460325000b103c00744100003400042c003003510512000c1c400b4525044050312068031300d6805210086c0030b509100b4400d0115032050305400e045401c46010f403124000c0700b840040181c410000715a2103240c036040850080100000d03028000c0c0101502202d000c0502d4403207450301d00d4283e041a05154007080b1541c0c0b820014080c889121100d40390998500c111300e0181400c4640e60740041c4005035407080c1c1802140f011089401a026464a004c20000007515080840c0781d03036444800c0d04078502000041c000c542c0140500484801614204000c0c1c0c0c450100b1540f0074148030701241c10480c2000844049500c0a030b24485e12406088528040202d1500003840382c3d2006201920316218000074000f1458540d146d0384410745040c0c0c1d49401c0505100c08aa01c48400c14003041c0300c3e1391000d90b42d81f2000303107940042e01700d55001141c044c40941e2200019 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 744536960 1250 744535710 744535721
    0x90d0308040b01050916050345012a020708060c120906150d080c15010501180803091c0803010902072105031503010b0307180c020105160807050f040306 67
    0x4039901e0b074240001082c0c0b400d04a034020311401d000200520a640082c3c801c1d81e150384003400d2008030f015192000c40d1410b101012041c191240d8008100582503a00e10400d000d003050b080b4100180d040c0000c160000060fa038030924542c640c172002003240207140000ba4601140c42c0d11040e1540960740810004040b441c0141c00b40b0b500c0087e640030aa5940c12080d030320350404560000c80a43d840143d4540341c00c0000186a0300e0b41304008440c0b6001410b03912910b0b02801c0c01c415a800603a4600500c0a56846618104080012540d0b41100b03424885110340f41d00902c445240030300c4080b5040210080120b40c0d00300b8403034004544d20765a584400d0a1000381d03220f00002c1d24000d8900304c0f90306c409500b034200c280529942e9507031039086403602c00000b00410035100b40301c0d034550340f5400001000c1d0f03001d22040c801070500801680003000c0c0401d9a074142c461180049055914141c1040954032030040307e80b2440c0d84c00d291104195840640a40b1075014069000d510326001003008001c016090b80030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 744538210 1250 744536960 744536963
    0x81f091d010b100807120e010204140102190210020a08040801020415080c07020f0a09050a1b0908060c0c070f03050d17190b120f2a0307061202090d030804 68
    0x6650511a05010941c240da0300790000541040c5030b080c8a5481d5445440c1441d0406207900d441c800e106056024001600c10302109000240d40c0058100011807c0f1082d802c01c2650a0000e0030046400c0c0c040c41c09c5d05c1d844002c000c0c5c0a0a40580c40b136100314424031000c2e01075130b0f0108038152910f0300c03001c03414000c0d002409010302007980041c03030040700d0303020300c14184c825580d80031150710304901d65090142c10048a066a60490582680401c641120303000386c5100301c1014030b00040c4640014224070b40082070174518410701c480b4010921000c01c01180e51507218040c0c08070b503030380e400e065003025181c0040ea5100c038220b00d0082c0b40100400c90042039103031865240b50350b1040040c010481001001d4002c1d505041491001116540740c58030f16081080b0703040e4010714600c0d149044c40b071101e080c03c415840700c0500b078109200013802800c0e440030190300307546141203070b40d5288810381c0403c0e500c411a0183d8028002940554207c0100f540c0440d07007021800f4201c00c1c0704030340c90328000e022407805880 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 744539460 1250 744538210 744538241
    0x705030d0c0803130303090204091109010f050109052b03021006060e0a05130b0312070b01080c150c0c0d0605010e0901050702070b0a0219050a02100305090c01081f09 73
    0x140451840c4900c040c1108680c202c2c8400e031441d183c100110f4010700b0b4540040b01031549030458240940e40700e11801d90404d008800b190586c0c00d082c07082180e1004c0580120080030400e8806005690340190345400341d480556510702d100780078030703800e04107e40309584d00748000071041c00074001c140c2d0115402c00802c84031a024441d0350b45905041d5030040340b0700352542e08101c0700d1804209902d000d6840c1414030060b0000007424000210129041427250310040c441d850000890304104036080c94403031300600301da4001c2c06464845800041850f0b100512141c103508004c80d113580cce245814450120200303001899040c9500032440c111002e80002d101d043c2150800300d000a10004040c01224031551956020300075031030510b0001d541603080b00c00b0311703011071103111015011071140d00e14400c0d004d03000e10020316001645d841000100c07a2074855000406080c034050003d001c10000f44030300d121409003415106943d509405e04812070403038000c007900105440c400140700f0b080398030030b1502801c03804 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 744540710 1250 744539460 744539473
    0x10204180b0319300905010309050c010509060d02070f1a0403080a020c0106050a171606091505160f03090f050a090e011517070617070e04110408070503 67
    0x1524030032100408940e60b01504811078140985a0004800c40d0720b41c0302e07800380308004500068060fa00b02816920b000180c14003220303140c80942250b0210300620007441d0030700c0b1500e000d68a05881d46185a1940e051040209101031956030302d5081d03400108208c6421901d40b41181008801c407022803505607040400466084004c0e840201c81034030407030305910748400c0d41d20340165100081d404899128119580c60001048a0762140d40000c02007801072500c00b5180b207200b03001800d0510600d05500d041005160030402d1541000300c22007100c1446114550a0031100400d031940d108990755041c040c6408070f08003040000d01d00d64111000c0c000d5440013641d0362104103864481c01c080c00b9803903000c2a43c40f001c11000c00c13a03400000c040881d41001161030602e017500c0c028100d1107a003009030036240041580c002c071102040200010710003031401000e01318030440315610000d4080c12030030401c402420707d80d030b454031190410664007040c5646542e84507640d80100e80c88114a01030b4074841c1c00b404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 744541960 1250 744540710 744540749
    0x1703030a110406050a270807090608030a02120901230c06010603111c06080f070e0606031014030a020a18110a200705060307050318150c0708090a0305010204 69
    0x1c0c00b558151046622054a017072103411701a0346084c2c4a40440d4071a0041c2440035081c400383d6901d440c01002200020701415040ca5201c0040c0d41c00c6410024003584140001d0440581c00070f0703000c107a003022010103503681c242d000049690102810140440307012003c10807226104c0003004204800603101030350381590322030000701c01303541514031031180e03c003410f0203400000c075903041580403081c0d182400080d007250354005003410440c1040c02c80c0110707042a5802c1020364060b41c1c0c060740c4075000721280d91a44c6001940c1c0c1040340b41ca40521003041d4448500000740e40c40401c00c507040540c0040510701c007030b5510301e90b04103d099203034120550366050640b03c0300050200400d40320078002da501c40d0b1041e0504c110031440c10900c002c091040300c1c49021000130700350b115600154001c008640d81c0310390300c1c0350607104285840300d01c1c0164401507100b00906903103441d00b0007400b0b41001c48840385655640403801c1071034990040c2036015902a80d00603000040150550050080300e0b00680040c6054014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 744543210 1250 744541960 744541991
    0x60c020f0406062307020319020102150903040e09210a0201060f03080708030919080702090f04031e0302090301020c031312080d0c110a0c0602060901020a1b08041703030a 75
    0x203503c03450000c1140748441c0d81d48090283c00c0f0303120b602000d00301d180c10301030281c0010780303009010b10451001c0d048682c18207055590500a52061204046034501c5905140c8450f5a40740310b280308070f800c1c41031038001090000350284404100101710340d00542c0c423420524904005680181c4100c07025607e4090700189212450030103030304881c1c016501078105201e2b91500d80c203691000f00b590885003d0292402d03140d000c40c400025001d8000d40304e141e1110410b1040c0810071380b02506840d2040e01050030000000c4c0d00800f00d00e03091444071350003a4008905070003940a800b0300900554154004107041064000000103006680c9101310411511661040c400164001c211006081100304004941d0040020b82100030f1422091400303410302e205040e5079a003031140d01d21048034584520203081007141c3d41041041d4001c80301c50021460701035209030103440e00000c40c0050400d02105500ba030144000035058a0040000c80d94003c0c02581d40783c41d161304c070750080790b000d00a540780c100a410a81709 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 744544460 1250 744543210 744543221
    0x80627011d06071b021c171c05010b09042c030c1b01050f0741190201110a0c0f060912030503010501180302041118061201052701060c020f04 62
    0x14004c2001400c00c1c0160240026840b17640c00114004014004010014011401140080d04120010ba03221a030300740c1254403070040490000350030f40c107080c0107202c01c00411040300c00c080c00c11503000400503581401001a084102c04120b1241d9409102d8500380b00007100520614641d102030703d01160050320103003803241710b03d02c402d0f000403400c0c003180311101211401009024090022144441240318294880002105040e0016808501c000b42581045a041c031340103c0050003a042ca6861030075080342490030304c0301c06810030000c00d014081c54401030040400c0c07541c10492a0702c0c8280c0b01e50050350312440701e01c10000095500c0c00300090401580e48418001a130643da01403559182400445101000065607074003030f50310040001c0160380b20b10418407105407049450f51502601c81032410642c45400da0f150051104001d000c02c40702c000c40015065490480f02c6425102c0030396041c2d640f240307080c0480e0f110410910008142581c106811003413a510071100c441250403404184011360b80b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 744545710 1250 744544460 744544487
    0xe030c0c01260c18040f060305060a05150d0f08070b0603060711070306020c101d0c0d020a09020a0c0f1a340c05100b01090b04080627011d0607 63
    0x142c041e02280700814004000c0160030101140e400d81c04122100040803900320104415445545600400c01c02100b400b0b0258006000c11003006a8508904a40442d0321802c0c501441803400840700b60411501c00c0040042c0c0b604207042503103a5046241160703600380d00b602d06a04c2031080d000010300c2c440c420030003c1060b0403030501510300d03a85035641e1031010750040501800c1031b002d240088000781100c0d206850001c41000d134072100b082d000000103420211081905400340d0228014a805601c0d00d4450b40115000c0c0e072001070360f03012010401c4a55461700b15004001420322000700d41031114013000d198078821554500c10658984400c0c00000701070700c0d0798403031912804642a08000c00c082240d984d403101242040070356462590303a081e0501145090b0701e00070380e1b90b0340d60b83d990f0303941d0082900001d0202c039402c440c82c04d810703d10781503035a800c0142185c21400b040b144981d043c400c1c3d4105d419890400400a1008981c5902401904541e010030095036108160000e4184c6105044881011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 744546960 1250 744545710 744545777
    0x301030f06050601030b032a030106120f0303230901050a090f02011d151c090206180a050a0e070807020601050121140907030c051906030b040e030c0c01 67
    0x200e0507607841024010092a56050690710000302455031400c0c0094112a90110201201409011a139034460f0301544000d0b4000d80c5080d40a10142107211103034224240c1084003205280c1d000c1c60101d019016898440d02624652400840a034104e81000e600130701100000340403c1d9a00c078400d0040314042c0030007800000b000c103110307000343d4081c244000f5050300340d5062800002a09005c150344516180400304480310000341074255803544c031005208010308072002d120700c8420b40c0000d040c9001c1c40e41803500104103020219540d0751682404c0008000140420700001e5484c004949074a0f81207420700f0110f4403540c000340c9031510225110341610816166070141c003403960402c41803183c041700396480d40360b41c440c801d0740d12210341002284034982800c02080f0702e500b10700d040c0c14104034592049001e107d42c9100b280603220000c2196081e0f400034900010750194070000640500000510940d9500000800d8a000200450303403500e072072070a80380c0c5a08030848080a40000c00e2107141d02285 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 744548210 1250 744546960 744546983
    0x305070c02090a1413031404030206270d150f060b0f0c0a02030f0706120c020606041e0f15080307020603060409050a0b0f01030b0106050c0606120102072f06030103 72
    0x1803406401154203e1100000094012600701103003180050581e1080c00c1c02c0303001054603040540c04101c0b8842e00d400b041c180d5017000d18650215101e4042e8840e0346000b540491b5043d050400312010307914030340c8402803108124a8050411006516220348003180d40e42c102042d24080084502401c0101d401e2113980d04d00d015000d18010b029904064521140c9004440450000d40d40800421058040f008050000c1340d00d0300d000500002c55540c641d141e0f1030f0900d00141071094001c252168001e07401c1d94082000401000005143c41d4411a0401d0080c50610f081040c0706080d401800d05c3d680c4858030200035030b11030051940c0c0e0f0140b0703540250702000400000d045414550008084284507a049810740c0585940d04440600116501c2607440074040041003408441d40e0042e00400d030500300b00e454081c031151810748034603004086500910424003806e61043c0b0940c11aa440707074000b140c0040074906092501d041c45e00d4501c00c0b030104030026421940300c1c40c0030b9048a0480c0d902480c611203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 744549460 1250 744548210 744548213
    0xb04090c0611010f060e181f0510080f07180b0915061c1a010c0201020a23030a090503071a0a0c260d1409100504140d02070e070305070c 60
    0xb41c9915404001000755203609000000046a01450005d460081904d11607490300a03014603030540404003d82c1d495018034200c3d0031185a0401605401c4000c0d0030100b0141e0b030750807542944070364951140f2003921400142c04840310003c03642400f540c1d09180e0386100c4480c1460054280c0c0c203c0703032426501c003105202041c0c0c2c01104d40024002000c02034403160034213080c089505d5403002d010092602c41503c4013402180b4100441e491510700400342805080402d06400003941c032004c0388030040540311904540101c90900500000a20050301e04882ea44c01662200920031900c601c15130380170344190040400c0380701d480012043c0d02421400c2903414110400c41c100c0e00000a440e094480030414480f20303008041e807941550103941a20748040c5c2c0e509d0551500d40840e0300030315810980c43c2d0018180b00b9801c2c000303e01842207040c0c0d6000481c040d103490070090303401c078000e000304825881624400102c40c0d4011035910f084400b40803440c8525903860308158152075003201c50000040d05514100c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 744550710 1250 744549460 744549467
    0x120907060e2b080a0809010f11160609060e07030b0a02040617070509030607090303110c090105010e030102090a031b1a0a0c15050f1006091a0c240a0b04090c06 70
    0x2180221110040142c030b105a2110b102a501400e100400200310504001d00c1d54003d002d848681d000720401000381a0742003807280704134003840340710303031100b400b156124400d10006800283d6103903000002044101c002c8500b00350350f1071032444111404030300b407070006218409034070955044070700301d8465400303040b00b00070002000d0390b00522141c1880402d00501180d070710200300b140d1003103040e074943c000800d041d403e010f07120345500246450154000000c0310a5174a0700c0300520b04542003070030843c1c1c0084807000002d01900a0161064000100070000024040840141c2c00400841c0f1100803809803121102d46061918541d400c0007207800300310081d00f4501c64844100c00c2802403100700403082060b00b4a005a40050366149840b1005500340702d52510341041a900900700c42c00c0200c1d10614090f403e10413074050522459585001180c0b07001400c009101c040752a580d41d000e00383d204501041401207051068848080c20303850100100d805040c6441032038a81a000b1002841d11850700c01c0c201d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 744551960 1250 744550710 744550759
    0x51009020303042301090b130302090a06030209090d1106131b0905150103150542130f120b04050708160512060103080d0b010e06120907060e 62
    0x3240c06110820000071201d5600b0200381080260064240c00c030101c0800044c210882c0d5081001c2c1c040c01003099080061610031100308903907064a4002c181e0b5141c035a100010003003076001a4100142108012520303c012610980342c040540702d294a900500d0502ca5981c0030850300c0e0b514441030b00030110049841041c00d807846480d00c4030541314071a102c85210085d180b00b0340e0510820b42c8070945105140d030b0180665001c03402c11840c10101d4518100008901c04810228094004c7e6072141c0d885e401c60502c0c000040700390701450f007000741c180c14650790440c962190300200e144c0c0340b03403600c0400c0003219481c1c210201c481a0aa0000c81101c644a4031071007140a08200c2e480d2054001c00030f030214007070200085015540048900d0645410140083c1c98018214a402c07900800014070010b91700314180c803d00640e05000050b039040660040e25040174806070250b1003100420861140d031101c0121034030410201d01913900d07141d61a0402d0b550340742214103c0d0380c007042c1b91011407540f0780384032401d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 744553210 1250 744551960 744551963
    0x5030415051b27100e120c1504030309050301090b0406020c0a0c12050f0715180f14041d0607030b010318050f0601080a05030406030c020102070b0c0301090c0309051009 74
    0x4031891a000c1050802c0315a1184800541207403141103030055142c042982103105400c180c0380b8100300007600100a10012a041d185841152541d015041ea5a0100078404614101030329100315620448c01c0c2d41c010703070401e01c01107002490420300850700d81410300406034066170100d2030b44500e0b103480c0d550310040e410112801c0d210348208441d000c04101c01081d80030051031410410312442c0405c0c00c0ca05e00b810300c11501380c40180c1c40007504002c0d20002c0084180740501070b02d0b1001801c800d58115410800c02a8410441c0f556844400314400d031051020700c030041c40440d01003089004580300104200d5040c01c1524582d080900000e914074003135008105030040500d0001a00d0312a10f595440412045501365495801001a09646102046500d0240c8000001031101e4841c0b40c0d146580e83c807440c001d00c02016283d190145900b4002d4040da907429602c800007800701e02e00507010450941007403007900305042c10051003001e1076000c1c1c0b05080d80d40390024050010082c04a00d150081c0000100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 744554460 1250 744553210 744553231
    0xc020d0c02010e09240a0f0509090a061530230109120206100b0f070311030a0e01031b050403060203070e0d0303050105090f13060b12160302100503041505 68
    0xd10940c95a00d1000d0300c5c0c41401030701410300718012603103594120844101542e50103254040000c1c007101c01180304c1142100c40403142a2019a61100d00c42c1c205110810003c1900d42010030b08400704000302418025524441d030fa40701807404420000003420110088903101e01510356502c0085584201030040200c600c202614441054005403800c5a1902e003081d070750b0040c00380b1244c130482c0d03040c00744070382190350942000003550070b0404500551003041c01c0300208840005001c1e081601490800c000001da410690380c075509c420318050074043e140754101c0e0000c0d18101074180740c084468590013280020b56152410306095540b200c0081d400501690140008c5d1038889616546445000068a00c6940c010038554540001d00c100224040d1660300b44e2101d5604200c699244040c0086805070401c80206801c081000462407001e2040c4041c0c41c40c0c0038070000320ba0043d84500e81001205c0c400c1e941601100c500b400d088404c3d000644004044104581d48844040c1081c0c100079040084200e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 744555710 1250 744554460 744554477
    0x20105070806041b0c1e0501060302090a0c0f1803060608030a030617070311040e0601031a01060f0509130603120c1103010207050c010f03020f1b06090a021018120b060909010c020d0c0201 82
    0x304103881b0481c0d00111103a0303450300028021403c0c00c00781160080000f070342c04c6c840031a0b284006090413000882c1d9000f001494103d0024842d004a503a8000719001030003000354035101e5081c191260300070510440800e0400000003681d85020410150064076100500b140c9030955aa06076105440244158456100c0503422a28501448000c0c000c511454030b0b4071075540b100e0201c0c090203a050f80004280442140c10002640e0060b017182d0881c41c4c200c92130f040c05200d03021544010301c802d0700701804c2d80d21004241084141c001c3c0c4114001030145982c00c00029442c02014240e10a0b140c004086821841500c0c407694001d002c4000c0003115801d0241c01e00328260b00140030f9410a040e0070129041110204001427018804e55802a40c5403000e00401d41464020a5540b0200300303141042203860324801c80341c11154031129001d001c150303c40040b03203071542c1400321700314000750744507882040e9220108091510510400d03900041540181844119001d42502c00e452045000da05001c40d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 744556960 1250 744555710 744555743
    0xc0c030e0f030f01110c0d0e0a09020304051f020903010b0a0b0a18120f021003051e0712051312181a040315060603150e0a020f1207020105070806041b0c 67
    0xc1c010320000e4036020422503158074900f10024a1f0004201c1100144940c03072100038156111451444240c074448000943d490301c03507160030740c90840b00c5031045111010359003101c581807402e40c00800d10400b00301e0003070100689500802130b090b40188124100710b04100300040c23044d070040095000c5c0740319484014000c1603503032558a0b0f40c442000011112145000080411031030041205110700c08289020041d40ca481007030b00c1c0e40c03051b401c981074107a40e11180024031000c1c030401d1032100704042c8100a0080303003401d5580303c90458010b0001c641c02580d8041c1b401a03144900e031544032000044d40841401417411918500044614030880e8000d002000040013240510044400101041400140c494604000182200c080c5000d01d00ca40c05420420407002c0005518660071000110b40140c1c1c070464115000b0403441000641c102c21007240c0100308200341c065200510869007611790308010798521042100700c9010b00d110b80c1651401068002e02c0c035200e00340142d00c540c4910000604070195 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 744558210 1250 744556960 744556963
    0x120a06030b1614040b0a2001060603140702060906130f1406041101030203160827160501030b0a14031203150310090b060d21120c0c030e0f030f 63
    0x211621000b01c4400a150400c1c150301102da0884000712440f003d04107070a01e03428440c24441c40c02c02104106003511900d140030100802100c24401640080001c1d543c6d8030805805000704c5070b550b0072802485000681c02d14008101d407413142200c50058609941c800e00310085010f05d500d820f441d242c00000003000080e015a008440d40180c1c240141701d1450310740790004202181c420460f0425005000b030040243c80c0328080c0405011500b00781d07106503190310314840c4440041030a9155015401d00c118a181800b00d8601410545006120b080c2d1341c8600055059542d0902040d070090301c0054200040d0010070005120300b8001402e442e05a036507805150075980095881800081c00d6010402c0b40345020800c1d1440301c050500d0500c04403c00e0344580d9503043e8000d10381e1b402142c1030800c22007040819000c0a0402d5a944030782050b5440f980d00003042d44101a1058408528040150462034050325922801c3d561540d51468661103c034140310102d0010302c10340d0340500c5417200003408902d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 744559460 1250 744558210 744558233
    0x60301030b0901022521020319050c060a0915060303140c0a0b09010209030706021504140708070602010b0406060309170f0d02070506070e060301240509100e0405010f0b120a0603 78
    0x1a841040c0e649080368144012407210300004040003035000241d0104094000c0f041d40c0d09800c407000d5030b00549c090400181d031075100d03800340303d070b0389000703040c10483c0b404a1903011410310360140c0c0034a0219000120034074115090350001074041442c1e002c1000028110700f000b0000254010245c4220141c5991034611112050b02d9800180c0d4001c030703018205080400541c0300034503d0b4402820200c4002410380c07c5150040c2c0054403004c00074030b48415284e0100702d0000185980c5044031f1380980c0e03e00000f4000c2110305082c5100703908010740000e0b180d00c203000d1001400c1c0c1141100c0410440405203240e598840550040c03407040503c8084090703442880540031a9006002800e003900c0c022000034407010361144031500c81c0c40240010311500340214040d15403180484e02902800300610b0301944c1502651003056441402003c2c6258280d0b070080321084d0168099800303015698a0780c1c0040c07806405805806918807080c49030b001004458941150000741c1200006011a103035164000304c3c40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 744560710 1250 744559460 744559507
    0xb09030309031e2a060606090607060b01020c0a0902030108060112020f0907120207050a06051e01090b011202190e06041505071424060d030f0c05120d0c140405060301030b090102 78
    0x928484120031140140569035215030300703c0307287d0f1800c1400c100040141c0200003002d050240d40c3d50548086074004c20200c0034200c0c0007444041c01c03e03a41c0c510741c00039500c24003920125020f160300000714112248110024550700508141d071105c904000d005210b4001007260082002600d1185238082161004054603030041014000c81c11450078024161034014104a00001081b21984201000200c1040c191900c8040101d40031010000496004240c18000c80701684001405a21a04400101c040707404640c0c4903d24003511001c104800d41c091441600b40070700c65015426034452160008104042c42a010040103e015081d4140b40198180852111003007502e20f8106c802e2180201c1075006008541c1115404002e0760000e04081036944088103000000703000f40200101805007407902d0f0400541c0c180c40d4000d0116100c06020301603121070100b510f002e82a11400c14503021103007940e00142000e4036503480c60342c4001800c20010703e003140655090001c1c0d000c00340f005101d03524a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 744561960 1250 744560710 744560767
    0x604051b090606040b0d110a02070602010605370305100606110f07181b0f0813050705090a0e2505010513050609010c080c0313080d08010905060607020d0b040b09030309031e 76
    0xc0c24454040c1c01c48410b6000f00740304030604440382a0000b0304070300c40f01d980c010034001e000c038909000410303108504551c1c2009040740281880b000380c50300c8903445a400c5900b5507591240345101d00108580302c006540348040160002507090040386002400d0301c60107280c0440014900c0c400c4010714040d05415805540081d024205070780b4005e6002c40c16a0b0401d01590019519444680c0d901d50765030194440d0718001d8188000284483c0361a03840014052800020743d41086c1e10034010b0242c841d42600020b07910b6040c0800410b0700d5210b002914400c0d240c14a20b210010b003040200304450700007003e50790402415a03010400140480054400224207800654803242c0305400d40c8042829500100641d038400e1440802007907000e002c0c141120184d080005560b100c031404104184692704002e50440d03900414a008c105180050711f104502996004030710f6102c21040c103480c4e22060300c0310b0300c8952084c410100c207000301c1081406400d00398040c45140c12131324540711044600d0600c1d6250351 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 744563210 1250 744561960 744561973
    0x6091e010b030a050c041401080714030a0615030e070918080d0209031e0a111c150e1c0806190806190c1403060609030604051b090606040b0d110a02 65
    0xd8541c1d00030583c205400c034076103070b0615082c0b402c11f4400707a640006003030400c0144000306079500d0161004000382004510403541c0c900e410419600600000e101303400e0740994500d41581d031148640310f41c500d0102ca000140098900d00740f00000607000003001c81c540e03c0e08107058080064080c00040c240c00d40900d802603149d280c15000c15041510b8240d0746048400c03d0070300c0c41d80300000890302423249070b4481c921115011016001ca0308080d80502514800080425010140120071b102c100300264040014400503140c1d0360030300e40b140d02203444003c9130002c031809600d101307000303400f002c1c1c2c000c00150200d5030f00310700040c840c50f001d0220380c410003182d04a18180040712a112601e1140301030120024024070380960310041800100c0004069402c00105c08035a1076540e04c01103840800c0e0080071103003642005d041242e01d54001400242d2242944001b50246007400103c40e03101d03440040101c1d08007031810200c421140d001c0e11611710100c1d5500b0556081c1c00c8850058080320f691580280035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 744564460 1250 744563210 744563221
    0x804080d0f031a010503040303050709050415030203120f1c020c1903110a0c0b0a051315081b03040204020c010e010e1c1e050702030304030501090807061b0806091e010b03 75
    0x12a0100b8030440c0e03040030340d003c070a01e07583d03081003c60350030541c5490002410358620764125180141900460b0340a8242242c20401096000742c001c00d9a008400340ca010501c04108041180319411101450810a00800120b410f548890300680740d2200d00140c500340c1440304050070700100310712191242c040120ba09050540c40381120425652290040c010020503895000e00c4607814031415019410004138003421030310507801c1c0da0840040740241c1403039a40ba14290f0260140b0702468000145000703000445403c118200c640c044010781e05050b1550f2074940900000c0e5028584050a940d240e400c80c02980340e00f4400c69402c20340c0507000d890140182011800c0703003c120f8200100304200d40c0707040040561a22440c180d4440d060401503a20281440482d056000d2a4400f800551811003001c051009c04001009a94800c42c2d0030454208003100070405c0007411040000000c100f807002805c141801500b1541280034a0940846d07195100304014590500760440d9101c41004428002d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 744565710 1250 744564460 744564467
    0x803090601030314090a0e07170c0c0c060a0c0204020d0608150f09070e01260708070914010e060d02030f010c030b03010e150a1104170c090f06060d090804080d0f 71
    0x100c08102c4d0b6128070314201c1c00c84006890f420300345c040e01007810321600104214502032501030407801001d8842004e00d1030708005030081a00040000383d070b1402034452040342403500700129070840010751a03900001075540c00b4080250068540c00386210b03901d040104e41d509080180180302c00c0764030421400c521700354640d12084e550161a80c50260b1001809100c0705254a25041c190341051071081904c08450344d100128640e81e80b0281e1047c000c1600200f004071020580805440c1500c0d41442041418607902c500701609204182e07240c02800c0c040785182c07614050343c5611500080c200c941c451203444805085405a010260100e651070010422500b40ae024ad8089102c00f900035141c1405018542c0e00780480080c10140c08954070611304002c11000000c1d0750140211012043c0c2682c01070000366919801c0f0f100d03a134030807401d010009603041c0d104c42d4414410a4064145824003c0c00015400609010402161514403d000200d900c07881000316034505480750783c80c840c00071415000907 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 744566960 1250 744565710 744565727
    0x80604060f05090c09060f06031f081c03180c080a0308090607050a0c0501090606030f0b0f150f011421070509090c220e07030608030c0c09040f08030906010303 70
    0x401c0701c030b04002c108000094085060000350409803083c01440d17132200001104150203481d100e0f4000d00120a0040c3c14034980f1008011200814000380400e40b0b034542a6568115222015050310210949481240c4207801118241c142c1043e0031003030128036076075603011590340e40181a01d980940141000e142d402142ca54103c40391101070211810013010090807403050340701000501c10390040480810000758040c02c0403d03005101004600c0d180c0c81c10000c3e200d12644c06441130840302010507000041c203e0064094150100c01c02103200c1d0020900001c5480d41e00084d050005801e20461040303aa440246068015101d20384003192420401c1d4000da80080c09000030010248180c1c3c0d030644500040b9900904110080ca848001c401c03c038888580c0040c2d40c8152112151074001a0501d24150703681c01041c407510140001502e510070a6568042c040780c044565000b90303104e1016040c1017040c07a070003900030001ca0b2803203e455101c840e100c2e4015116400e980c1d0181004000707065120009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 744568210 1250 744566960 744566981
    0x90405010b1516110a120b06120d0207180e0105010b130806071d0604080f06070807110c0925050904060905010518190c030603140316032708060406 65
    0xa2403d00b0607103000b905070416040e000811000d040745404c022a941c4082d003800404600441001405462070807c00825040d02c070a8042c40d80b803071828842c00c4012941130009106607008041907444c1c00d404003c0788481ca42c80317068031a0703071b103044228800c02805002d000c1c006185100b80c0d00d1840d000000710701c42296201d030145070401300902410030741c028030501e01010340b200380100d0202030307100084142c45a54400d07012840b41d45a1042c00503400318200c1c2c4500519101d40400317984112040d520740f40022030b0700a0300c0d082040018282c2c0b8201241c41d40000780c81c0d50130029203d05208000d40b00e4501040c0034040340c6e0100d0382c00703481d2074140a42805070052420a00039035140c003021070500c4907a54502184003c134400010440d038620302100c800400c1110041c406e0041c2540f028005000e41e0205441d405240944441003040010803101c120300c0040c000c607803242881c6c8045030b242903d1403200078444094440c5030080c1e0221308000015118604c0030340b00b40d007424501502150b029118 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 744569460 1250 744568210 744568249
    0xf0506030606100503010e100e09060703060b0f0d1e0c0809100c080408210109150806070503040318180e1015060c030201060909060207020a23100e090405010b 70
    0xb2005401139001c000d0340c1c1140d0607070304c4000064540d0003461903903242540008240080e010108440c2020000d8040c0c0581d41c6034608119440d2580910347d02c512030044010443d000412482c0400e503042e50202200300001000c04800c03602d500e0141003650300035010b010006041c00d05020b0011700034032003040342150200041110000d150400341c11098010000340a40c02e020a500c0b004c4e000c0f46000000007035070a424103d096848042000003001c410391001c01014450002040c44600007400303500450103920381c01d05550700c680e003c66414080c5503c044a15420002c000340300000c0070804100e0703d80c1810042440d0300712403441072401c0c410203ca200c49505098400c0c10003055117400c00d086d1200c0d880d2590003d102c6041c140d01500e12a401006c80d145401102c4080c032005502411106201b112000b80c0e01d130742c90001e0010860074502c40e1403004815814450245400d40d80c4008a00c520304181001c40390010005030b0191040318103541c1a511030213130840620f03140d81d416022102252 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 744570710 1250 744569460 744569479
    0x1020919121103030d0501060807170103080301030803040224071202011509020f0f0c010c020f0d050f03060d0218041115040b0a0c02030a05031c06150c060f0f0506030606 75
    0x41401c0550150280a0301c40a40c00032006540c1d10140211a00800041c03024440c07940d40761002051a40116000130000d188025941c105003910280c05048070303002110301d03045034255212005683c2c8003910807a0700640030f003044166503902003040001c0c18030f400412601c54209060010781d611014241e80f045900d00b0028400d01035081d1700110030354554039070058030b50300c00600c2560148201c481d540090b840100e818007000505411520424415609840d40c80d102c1100d295030702d000c056142e81c00706400307205803081500041c004e1940014002c00f60711442c059600480e4074400400b80e06c64180d0420b1082009110000c00780e0002910f0580c0c00c0c051149502440e110140140e000e00329409400203440070480e4441c0c0404d43c00700750002d06903234402d1004e180150752035201000c03d808107403071407054807005007052080074103c460018040d40c4007560b031002160340e5007214404a5006958441e05c40c0c1c0c030305651068403c082a1283d000a05081c80400c040c074024000b00380702e1040003a03c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 744571960 1250 744570710 744570719
    0x30506040e0607080402010306050d05030c0d050f0406050c01060f0608100506031608090f0d0518010903020f270109062d0608041a04030302032410050f130801020919 73
    0x40c1407640f0003518070300604985c9039840102e000e40700d00d178001e07603101003080085010300101000500d02d01c40e880003121245040600242c0b001e019484110741f14600620003000542d00074401000013842810001801d40d84540244c08840316940085002565400401100b00325134414000641800c5550383d045d440c0c02c9040c07031414805030311050100705000380803d020718010481c3d4a452903003001941c075010421100180281c00202110b40b0210b071401444642d0350060391200142c0340c02400d40a46403114005105e00c40d1280c86d01c0c00d0510105804100c1040c82e080b0b559400303051203400100e011864407001703140011500345000c81d941c00320101d04021044544e00e10003100d0043c100b443e16507070750b070601001642408440101c01e190300400c002c03c140c1e15500440c482c03500e484070300c1f01e11b4852125900b41001e0301c0545e5500100319111031918a40140702070007804241d00784d281d240c181e441d0202c42042080b94031034022a03401051810007880d040d0344600400304041c0f1002c01c81880c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 744573210 1250 744571960 744571963
    0x607050d0c092d09090b0f0708060f060a1e05040825210605270307030804140c03010603050304090507080c0a0e0411030f16090320060403021c03030506040e 69
    0x40310390000002545024014007110000843d00c010102c1e120104103541060a100c5001c0500700c03020164070030b042c0300003100103000c0c02c00107020b05c90143c00c00c03807440161010301040340d201c4180d180510070341c04180014000c0906181e40c003e045942c4842c0c642d40b800050300c1c0b030455010300b1a076000d801030840c2c1e14443d800c100150201c0d020090041c00050820000c8130036050b000d034010b4003031030502003044100c0400000310074140a440d81100748644810314881d071207010304407000700006c803408003213008510781d00d2a800100060206650100380041d0029085515603407046840e40c00c003040401c00b20080b4410303e980b15466050598a504e4503405aa000d8440c01200400b8045038036040840c9807541c0d80700800001c030040e2404c0d0b590402c040c40303c5140300100d0784c51070758440d9041006c0e05184558228811281e002c40b1800050b540583c0a00d6140030a02c000f5820000034000000176990312043c4c407400d015860b2001d5440e40b03550500409850006085600a81c01c061440358113590 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 744574460 1250 744573210 744573239
    0x7050102100c1b03090b18310b0f0307030c080c060304020a1e030204050a1a03190618050102070c1518150c06052e06020c060309010207050607050d0c09 67
    0x90104003000c0050f80340c00c0e20548846d41001c0b15203980070540a2485c0140a10700d240602e00f180e82c90f841401900c03031340680300701e105111900c3c1c0e00348010191803800c150f0845d0460794402001680a4200e050119150040513031040e5284d044042c01000400000d201102c841c0d582a6030741407843c078007a004114006aa407040fa08000325446040c0764030706e24a0640c0d0091540104180702c1420500610809402c1122a02000b055164168071151400150300010b170b003500c821030307641c0507140e8892400802c508051017503d50400c6d6080c400144080c401031021030300c40c40b03a0200c06418100f2000ca0328108507140003d00c40c4e1104000720803800c2e4031481003100e0305122039540b4604006800c0354003e41400008040354244010f1003100c00c2d0081d981411242d520040c1c079040703280703043c0d5010300e0034040c8144c1025800c118610201410140011a4441c080c3c5001620302540d0365506481c10104070b402c80c00144022a0720034441205009188c455540b5282c140f40c13841c1042d500a00504 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 744575710 1250 744574460 744574487
    0x12150e0f061603241e0b070321090b01090b150a05070b0708071205090307121d01030207391413021317010f020c030a2d0305060d020d0507050102100c 66
    0x11020100f610b108550305c0e0410f030151000b1114561940c2c550314000d48a0304562000b204805070b14007a40040d0b59041c4030311030a25800102290282e441e040e0b00400410b00d4921040c0c00c81d410344424031110401030002e0102440b1a510555a0a060305002c40b0942000d00850100b019039400d0000840e400055000182ca1004000910f500c0c1c9402051a40c81007840042c481e00408800403031058100c01d465008105c1c201410000d080c112004604038480c1600051601003008610300d524180d407603e03c484680107144060722185e46284801e045861a40200d001320b901c1c0114414600302030303202200c0002140710135801c1141d660051b03801401c1d28051030310001d4030501004480d1909402003e803e0030620011503940a4031072109440c2e600120300e00010030300408a030f0100d0741d412005559940760401c0c10401c010850082100904005000c580e44015072042e18005a0366403c49020283d00c40c100603c0001d14200019041c0507000a4180d6080c0c03400402880e8150003908190201 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 744576960 1250 744575710 744575729
    0x105061602012a06050106120b03120307091d07020c0d03020a0f02060405060f03060f1212030a02091e130513080c010906050c1312150e0f06160324 65
    0x1d1501408002d05218003c61449000031080040c040d1341e81c41181030b140c0c65030380c680765000e1a66130a003d0300e01c03810011350107031f0015203180e041e440110301468209000c0d2500f600c0c02940c61344084d0403020303000c0303802c411170510304203014495404101801d90040292840020040700e034802940303031031903c0d2010340780c1c0310200805030840d550f1108840c080c0c40002d22141e22140e0120481c0d19980013101e01502407030110180640500c0c00c01002200230f1030032002040803044015030304000c0d410281603401c000d9028840210103a5a00710309044842010400c404810501c608000e035140300c0018803184140703008180014212241091032904ea00280c3d500d075501840c50725580100b03c0060b020300000d14040602c04900005c4000304000d505020b01520020f40318400940c41107260400100524841c1c0c4070300703c0e28070301904400000d441040a54800042d4a0074280c01c00100b12101c0d00c000c40e0b00c5c4100041c1940612230000c0b6400800310320220032600101406070078100d4040d005d0308 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 744578210 1250 744576960 744576977
    0x60f051227030c2e0e0c060a0c03020f0307021f0207080304030f0b0f04050c0f0105120103030309050f0312150d12020c01030609020408070501031d010e07030c060f14131e050405010506160201 84
    0x103401c5c00c0004030412800500119a51800300000500c82000d08004030014085c60748a52142c900010564200b070380c006110702c10b036a4450b0402d90030454100c801a0640c003030900001101c644c144040d1000b94020703840a00740c6241840d00e107400b000020050990310413004144400700301d0000d03000d40080c03010340300c10b00b001c400c80c401039615020740214132241200c3d45002204041d85904103441c40352041e8101d42903003440700318281d1680a101e008500d0030382d0200000e04451048c0e801100c82d04006010003c075424652103042925420380030a401681c0880d0400b4419645441610b0040c40c5d890421403c1900b084080d81c1c0302c401ba840b4160401d615242e0b94035100c5014440f010112590000801c892440024602d13101c5070548800c0c0e80b480c050020000c0c20602810206d080390000d81d1741c01802c41103030780301d40e0f4a80d0440a40c490740714141c06404964000741d01680601c0d8514060584c09061030b01c020001541d80513044170707008000520080001c40c000040c58840207a0900b8038581 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 744579460 1250 744578210 744578231
    0x10b072301150803040608180c040b01120903080709060302040b030f041703010909020102011508150901020f0c07080c22021c110307020106060f051227030c2e 70
    0x161100c0c03010522582000c042c0040c0040740080100100e402c00e882d07000b59559008001075070032511082c5004150081c080700700c810f241c85d9200d43c0c0b86000504000c0309031007000b141e0800302c510303402003280442c61039024801e5054000010f2001850585030641c6800d0500404120500014101211041810300800c0811400c21401058011404007041d202d41c0e40e810403070301416504101783d0240d40b1b000b43c2141c58220460000040c1d54103100200885260305a40082e400300c01488000595828002c03001c0c0043c00d0710040040300e0340e5000404006080804003810488440500b0340f041c09101d42980558004845d10030328602c06007001620380621404034400e4a407581d5004c0d2009240154a408180c0110041e6004000710f5008102e8580ca521054620028034240f07030010400a104140762070707103036078611940107580b0550011000740b902d44508440743d84007541d1619070404150048a0102003090201c106840381c038038040c080700f0640141918500d580b419104e642c88400070807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 744580710 1250 744579460 744579463
    0x31061d030a0f15090804050f150c0d1b0c0e13050601030807140708100213030f0c05011d010806060f090a0303080610080411090907120515010b0723 65
    0x204424000c0c098441041c03541c6001000481820710482c0c29034900c14014031800054070030480032603440311129140504000820007808800f04807a58407501020000c0400031840b00035055441d00c100041a04016a0342d000c0c220300744040741f88003c1d868843d180c0c03021030241901d00049031844c401036802c1c2d44405080c0085600b00307100c003a113a0722408000204020f03501000709261800703000150001035404501c1601d0341000c0c820030340070394050800403034040b40340e500500f00c40c05d43c1d014100e04103070707242e8801136542c00c400800d58035165449801c000558100403200724000d144840d16134501c0c0d201001034142c0700b01502c024000c04001c1250104c810b030305011117031b142d0002030143c48070540c0d0b03240c002c0800504550003405585540460040c060041039180d020300c0e40505a0340944880c4002c0c03000162000300030b400d0364800e006e00018009101c204242c10b15000700c01a01c254640659003c00d0041c040e4050001e1240400c0030b00c01080c50507200e001411524041c60f84200401800329 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 744581960 1250 744580710 744580757
    0x130c05130303020304090b01110703020114070609050604060b060a090605031017010902131a0405060604031e03030c0c0f0212030f04180b0f0904080a03060b0f3106 72
    0x80d200140c040c001c414550008043c0c004c03150a41e106000304461500110345030440d042c0c91144a500c10074083c00150f015400303000c005988849000e0400c801521080c05807442d4003c1aa41e540000043c4010301240340110306a40405941d040d24003220407038014806030081c415501000400300200d1120018502c0314401800040d0030582e62071160009240280f414800803840349141003038454204659000d071340307028809162040fa00e00010400c0c00050b003001083c0941c06041000084002002451001084813021070601041e00d101d15000d4111592402e44205104544440000048003e800340ea581681a50b04040000c8610b260502e0340c000d988401d0350301580841c010900d4040e03614800360204440000744509039a8001703110414200521494200b00c500b00014041020080101501d032103500e070000c2c200d5903403108412a42c011621110241a0004071f507108120b954100910058a091002c0e80d0803182904100d6416500e12800c0d0070700100c0302e5030800c5000b40d000075 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 744583210 1250 744581960 744581977
    0x30a02090103060b1305070f12110f071403090904060905070509090f01150506090d0c03060207030e030c03010e0619090506090106170f0a0206161a090c0906130c05 72
    0x995540d507141e2803d0030280502502160080840c255094031509407405410b008807165256141c465000b4641214542062148180702ca52500b040c2c020300380d400302c0241103d00d50240c0c03441c0c852240d0714014140e4200700160880ba603000f0b00c00445599500505242c105502c403030002428401458802d09201060388000d81c080000d05c10407045100214410446c46001002044209640200e40305140e40900500f81c101006016001d503e04100c1c1003031048a000350003200b079440c0d81e951010140c1e803145004a001070504031641c00310342010003008407551012802485060710090b5520b55070603000f45032940d999216803c41c01002682d900000b100303600302096592601e00301800034003034503091203030488003405512408441c050114494100c400b03500b010740320403003041d000c05c462508400401c940440e203c00c48500050208200400c104e00c850382e40e44010720b0040c1820307040c00082a000350040ca1880b0030000309a94044000150308441e200001c0c44004194045585008400c81c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 744584460 1250 744583210 744583219
    0xd110a05100b0103140c041d15060304020a0f14180702060f06040e030d0b01020712030f05070c05093c0406090311030a0e0a0b09012f03040b070210031407030b030a02 73
    0x103001c1b040d00701d07200410598040320076041a85002c05003082240e0b100320f441100c0c8c5d5440c01412411890900300850300300c0d000400c4c08846035141c90341c15092a0255218a40c5401c007004007640e9404e040701d140c129484048002d6980f450190343c0030351030b080010074120f00c03061000c0015a80b6540c642c015442814050308582c0c85500e03120341e10700200841c00386540580300b16940000e401096031080280654182d5a0102c0555a00c00c1038403207801c03008044400800342d00c004200740d2558a9224800c2502041550100f26044105042482c590796041217103403042010704410341100c041542c00035071000001450300e0090504540440070700413002401c1c000062604140350f4400204202158101c582d54a5030b40c0d070f0b1840c5845407140004240c041008690000401c6150758030010004603641c140d20b500d41e003034800890031580185c020700010400403a502095060005480d54a2000390508000d0a00e40400f00e840c21300c0010b0282d020951034090042442d10248038446466a0241 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 744585710 1250 744584460 744584501
    0x606040f0b04240c080a0318211818090b1f080c1c060b03120418180b07021617060702120301140a0e090d110a05100b0103 54
    0x540d102d48a040d42c5210620910031803c0900d008920b440c0071540c403030b00d00620b4035035100389850300110040c41c180341d036945a400300c0524071541c0300b040ca842002762145a401400c0744034a20001110082c0c10080c5030300381c0010103600c00000c1c1c1c00f522402c00501c018001c141400b48042c084e07007200103000001c0b040074400c00300384020b0801682c010140c440000325488041c110b90310f0414903c0980d12520760840184501184422101690700496000c80c9040107100400d1030a82c40c00380400001c07400050800030b2540696005e81403100b0040c0070b11980110042084a1402c11400500401c54031808522031500802c407a8220650445015802d641e441680040000c0b07000000c000038051040000c041c079101041c04823441400d005418256400e00801460307002800411542107412f420020a81d51b0b20030011a02c44d80e103103001421100990800203104840d40f017011504c82d80010000c000150000c1200c50f4801078803035000604943c1d520040b0040c1c064000845030516074075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 744586960 1250 744585710 744585719
    0x1c050304060903232e060e060a060206090c15040e0703020a0306090510030b0901061e050a270b0a0b0703090503061f15030b12060114061206090606040f 67
    0x5042d402c2101c1c091111010f249441004803202c108000c0300c0c100980e049804d0389030441c1140004100c80b42d010201400c841c080c0b64820f8000c5070602d030410148413120780b0401025281410510300585201d00c0a07045030f0400b804816900c5070002040d0b4030622540740d1181e1114041c1e0192801001008001c0c801d605000d18050002d500500903040002d082904c04504618907002c0c4500841c0d642200010091460701d0780240010050b0441406540f920000181c1e011502d107018421036405c0342d0b040300f591a0000300503c6600c590701541100140c013244850082003052600002032456202054080e8840e000401d002c0c401d030451500654003040d20400d042c2c2c0b001c211001c0c0c40c0190120745194492010400c024441005141c203c0701d110318083c84a03150041e290b6220980c02d04000c130307034500103a001a41303048210700313520041e6000c070b80104a01c910f609407900340d0b40c3d400d0700c5140c50314413181c4e844010100010916409030803400e000c50390715101c1104550040040c0e0800c00c031801e844 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 744588210 1250 744586960 744586967
    0x203160f0c0608010612020909040201140d0f0203060901080c1003050403031e14010b1602040f0204030204061706150927060106030b03010f0b03030415050c0102040609181401051c05030406 83
    0x80c0545c40002c1e2100709031100d101e04c14401c540b01d0342e000400030181c3d55150382c0111049000403000140d81c1704e040c403090581030701c5d80c001c0400c2c001c0e48010268403407030400284110810140c6c02130b4051703400502d0a19043e100d102189402c21014034000c0340c2030b512410300b5000b41100d07450341c40088030488030f0320b10505000c1d407090301d5400711070320464482e9030ba4030030300c88460180e9903800c0c0094103814500e0300145040e80c040010b00700382d440c1c050308041e034270340010741116504d60107009a020f00610a4100702004c0c000e06500075030251654112048490104420300c100501c2c040070700761b9280f8410404010b030280e105000d04c00710f08803030752303980c55030300042c050034443d25914042d41c02c02d0901800e44e0b0b094011400c2841025000314181480c0001d881c08000b020b01040d418850300300f04080000704280001c1010b05055200ca00b09c5038644280003401c3c0ba54000d1200300d4034074000f60444c0c0305509401d024115a011203048500f41600724034171902d1301500c04001c0041c480040c00140c901e07003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 744589460 1250 744588210 744588227
    0x50109080a110c0108090d030f061e0f12030509220e010c0e09092808130f0506090d12200c0f030604030e1e09150f100203160f0c06 58
    0x10b0402d480d0b040c0c56200055070507041c00e55411045401444071410030714801c1d480001e144840b8400811020380d9485101104140b1000005031861405014044000c8013080c0d100102002e5140e010140c4150720024580d0080e8090386104000c5007000c0c080f00e0320b0100e03038441e01c030400c0c2008010007900825458000c10306109603002060710081040964585003071920310850340c2e6030281103040807074030305200f40700d81c5800c191442506c040049800700c0c0b03100340603044184184602000450808903400c01c03d00103903011612504007013048900c4c40d01c902c10f402c1c4220341c1c8811018a900b190600030f0f0340e50005410b4a01e50880300e100b0301c101c02140029440f003031520036111000700c95840d4040c981c44220449000c1e012802c1c0740b5064055040040c000c030064500c6e110b40c0500c1860710000600e0881003a0391001c01d81c0c121460800782864000e04002c128001107885120034a004c0c00c000c0d4490044001100c4140261041c020a0140349287c22a0701c1d9488095880c4a44c2c58810140c86800d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 744590710 1250 744589460 744589487
    0x20d0b0f04060c11060f0403300501090c1e02030f0f03041208060102070314070302060d0f15050d0605060a030210050c01230105090615030a1a0406120f050109080a 72
    0x1d04041c41c946802d03001e002400340c0d02d00f400c0d02030482940c600350191a11400a8011010041402c01c03a904141c003092340d06528038201d00b41c07aa50001d009e1400c0058900603040b2045041c40c0c21540010b1a0704a0b035540d1031007040503451040c810031b1040c00d0341903008518840105a0f1b002640c6503108200600170742c41984603582c00039215014040894125030210b451340e016174440041400840d81e070010501c200d50000e07044030107082d1a03034042400340d00001280900d01d1744038505551502c00c1401202405240fa1401e040d1180c40d020025500e021b09180141c0750390b98420110351540c656501f40400342d45c01411888070308509402c02821a44040800c1c10154a0300000400c0c0c4041140c01c114400060407000800340d0a04d0200401807a000c0c24940d8001c1000ca81d040f010f030384420285105450b42132000841c44180c448600e0b84c1d01310520a43e22451505105100e894403000c04c1116040e0806d82040d40c100462400b94010f00f04c80001824641020030380c032074003030380c400e0b03442e0584c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 744591960 1250 744590710 744590723
    0x15060b091201020405091821070201270605090a0b04081c0903020f041113090b0f062503050706020304060c1202090f0126040803040b0108190609020d0b0f04 69
    0x1030312244041c0c200d020b180500707948005000c000c184000709500290f8030801070321023501c10f1418012811441d1a009403046d40d821031000c50b9040956070895032280c2c2e040511070417010b1000780d5080203842c060703c80c001c640078003a0101d00700400388c031801007600140038256942a695500c03802566680c40e020500d4140841c40002484042c9e0304ca0801d00e0708490380036051180850250040002410f100903401d010f4890510607494506012101880100100000000c109484d9410302605400f0101c60300c0c050710f020050704036500207034050150003c140650405403c9403a00d011140c6110360b000141c122030010041c04103001e07213503014240e03c885a4458078088568a0f1142c1c040e0f01072001c0c0e4a0b4071031021082d094055000300301d8422081070260078213010070f02c0140034138107030b45040c0c03010b5400c0c0202008100411000306030441c054407100000700945640710210421000c02500e0081c51141c481c44c605c01191219000452119807240c0e40013954a84100450240c1c0e204490641d0300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 744593210 1250 744591960 744591979
    0x1521081614150c040b1804021c0b01030c0c03121a0d0c1509060507120905030a030c0209130b040f0203120a030f0f0507050901050912010617150f1315060b09 69
    0x300c0d01c80200c40440d500d030040e003400e0807201c044c80f00c2c06d83c007003601c0550402e40820a000024541c868114207003c4403020010340c64008000042c2242c906800e20303c28000d03500c800d100801e820036010024448031a1010900b400c084800c0d03401c00340b40070314103600030103602440300800030340d00d00c504191343c0140d4140d074001105140c1100e001045200b0740c80803800c100004001700d0304803d050780740c1110038289542c0e4199580c0100e4035185900c6800d03000600081005000c40c174014420340c0d00710405103e50a101c10803a01e962010b614064401490303807a00001036021034a0501c02c1382441c0c025140319945942c42c04401402800e5034020303800c10240f80101d00ea840d00750920401c1d010340c0d00360396090306054074030005491650040c00c0c025803011909609190001c0240a9800600202e0146018003d440104c203480c181f40390313488000424400080100b2484041c021a40c04540b070508284c01c15003a0a00f83c1ba0954030f084c2a0405504180c8082048034801c0020401e0403416945200d0b03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 744594460 1250 744593210 744593221
    0x5010f09030804031103070804180603020a090b0f04112506090b070f09060206130203030409050903120108070305030306040f15060f020d030e0c010f12090303152108161415 76
    0xc0301d200b0b1f00d01c028000c45040c041441100070b00c010f2140b40d6424980d000507002c0e101d8000031801031003030f4001410203442d0001000542001a1504000f0105460a0142030150042c000c018040c0c5032110782d00043c40344203e1000d684a1103000350741500208104450304040c2490190500100c401c400441c001c20715104495104001680888190ba0302820391a100c00000035010b505041c1c09990511080c0408200454240701e01c602541200c030017542d075410030440c00c3d074013440140c0c0710429a030080401000820404811258840c0d003c070390018480144d8518400140b000440e040000141c1c51030104000b078100d12410540c41d00380e0201d45410185003000c9080d00c03000080710384940c210083d8040b10394020030364150505007604040c1060030103003103080101d505a58099000984a01c07400f1004c40748107107100080d000c0d124894000d0100c40c0f00580f10840e10038001410760200044482e00c000c001808a0b45036030380301000140c0c04612890040d07480700388080130782407030202038040b50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 744595710 1250 744594460 744594463
    0x61d0c070c05040c0c06050c18060a0504060c1a04200d050a0210050f0f0403231911060a12050105011b0f231606080105010e0d05010f090308040311 65
    0x354190790001c408034030700d070602c0207020281008160038024060355444400005510380109403107286407401c0c540d16203038654052100b4600d41d100b0180540c50400507402425840300403102960303102d0030f0001c040b080b507191402c203001d0007034032801c1e602180384140401c000412050000309040413064403441c80a500c2009a00003600720002c3c800c0d40103080d4200103040030040300818072a142409411300c4070388aa10062980b0280560400076400601401080998514105518800c0c44442c6c0c4c4903003240cad0a00c2d928800c407103c2c0d0f5000040d80000008210354400d65180032000980101d840c0d50200802030000107034440b042001a040500124155204419918684040c1041d0030680c62041d11004a403207001441646c500301210001017050f0b0642400d0a458108580101100180002d0f01c015505180e0016403c0143e010010040d0341c1e800101014809001c0350507a00c41c000500c1c1207801414804640d0700c0c018180840324040c1900180240d219a01079291011005e0031621404d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 744596960 1250 744595710 744595717
    0x20414100b04230f0a0f030302071d13020f060a020c1228081e0d05071815030b1801152109142a031209010503040201050706061d0c 58
    0xc1403110805083c00811080c1e110600a141002e069880c1c040c3c3c001000c00c0303541c0203070780240b10100c003408010400c047e41080468000d10702c80c1507502c510b141c0c1c07030b00300c0460007405040c500344820b03104045801d55035440151403031100c00030a01c0c0e03034684071a00043e489407200c040301403164541d1050021504000b15040c83c1040c900e040c41c1c11003a403d901d4011562191010545e078480050000803401540c111242c2483c4c020ba1005503141c541260707001050f40d10040c19075080201e1090000881c04007288508240c1b0b14807000c1190880f91400304034000d0641d04503040e030001464090000c200c0b056903005041c1c9505080041116244160544520014401c1c11a1084a104d040700002e66030341e2080d01c503e8171070b481c85c44d1010006202c0c21b140081c040c000c4a01000c45080141110588403110a82c4000c1540034000071106501125540c1c000c520040d81030000001c000f8046a2117401101c05895001c54200055522100214070419003040c081000000307400c0447c18041c5010142c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 744598210 1250 744596960 744596969
    0x10f0e071e08010204060804120c0b06060306151209070e01060f05030408040905180d02011a09070e060706020703140306060715020c12030a05160c060b0a03020414100b04 75
    0x82050a18004840c0501101c03881c0d1100358094820011a03050303000e0000f0002000c40340c0e02e5030654103003030628003401e0314642241c40c20b110071002c48100007141e5512041e0720081c01c42c1c50503200d80e11030300441c26010030b5004a4400505c00185202c246201001c0390780501c0e00e807021210f8154071844880200002802410041061140369140c6140f00d41c0c002e5078485e200c0c0d11402c0c00c096461000c50280c40c1c041e5024000c002c02c1da91400305035541006000c1c02d548480c8001e02c03414056481c1e8140d402140c2071280d000d0420329001420141c0200c0c5000f880c40381c060300242c0d813040c05041400094004101c101c0c0060341076440e405c0c402001c0030550740584001085680740c0316480c2d45601d0034882d5210351010107502800600301000c0140080f0007000c402181403a66843d01f8403044040700c0c0014001e00e444058103460300402c640c8085501c1c40983d118034002158015a00000c000d80041d0340000d61060501451411462005d0f03420741c01003600040403080c141d20769001c21200d0050f0f005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 744599460 1250 744598210 744598213
    0x20a05030a0506060d0608010f2403140a1a01090e0303011412070f0902041707300b010f2603090103090807060501120c23090402061603020105010503010f0e 69
    0x403407851901980a2600030700014100c6242071003903105c50055039a29849008a42d40d00c807080a0855920701601018254031000428480d000310107071034500205000203440c2030805000304582c1a020802065030300d40129076401d80e00c80740f09840707074581d200b4014000114200610440110800800e4905a480c1e03050702c40c04084a0304148000c460b148418044107220300140000e0107e617000c840c50161034000c601590740c50419601003c2003d90001d10805030340702c03141c100444105c03490314004050640c42d85c2c604596207400080003460603c030026141c0d450a000004819a01100d904111108240460b2028020780d683e9405031803c00480c0c01190400c01c650400d5602c41d5001c05c0800c1e00c90340c0076905244164940900b210001d800090203551003c01c05420f00c40740f04803410051040469034a5282c00440b91003120483d001d0096000704d4a0002240855607014190352029a44108030441c0e141c3c9818024080c0000303100e120700035460444904181012030250032841e145140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 744600710 1250 744599460 744599467
    0x40f200306010813030521100e0405070b130f060507060c1809150f080d02060f04201203070b07080c04030c1701150603020a0311040e04060c02030c161701020a05 71
    0x52501c4612400b080031010446c00304184803105010720861302075180b00c5130051901d860101c440c40c802003443d802800c18030080404200002d000010801c007036621500d8103940f01c0783c4050304604641c081c0d8200d079403d04c0c0744010228403903500c0b20140c503080c1d000f5001032000f80e85404040d101e203421001c164604094025081c4088190b0303800001d916103143c0305a0440c0d40e9201071101e4070400d80e420504d59a00301044000069604101c1aa00144c428022008506181d52003031f0001183d40ea07040300000f0030108040c01603640d143d48661060400e01925690540c616207141000d508aa5490200b41900301050310004603005075000c3c2c3c0e600c01510b0070440d003030442c881500c02403d80240340319901ca16081605501c606505070040806072000340e1075a5006001409a034080621807a8250050000308042060102402d0b045078001c280001c0060000608a08522030310b507400d0414030450030f44400c0d6002c03105c503030011075036154140c40601c0800c140290030f0b803148071104000070340180f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 744601960 1250 744600710 744600721
    0xf0b1e09092a0705151015200c0102071809020405040602070210050307020312060f03120c011b090b0d0f06080a020a140607140718020a0e03010c090b1602040f2003060108 75
    0x170081d49070010208101100100e41d02d03411190407840b51031990300021403030079580c032070b2926100020203000600c401911980e0b1b043d5000030341d0740c07289220b440ba40242c0da2505075903030102a0321443c10103802600038402c529003030424101950155001700c1c01000a00a43c0202d00c1c07242e82176a001d06150790145107012100d0f214640560750281103564400000d084604031a9805c100142143c8132181c1241e40b51821807541d00d08441d50a06035694002d81051802e2500d40d00c070fa01c2c58203441c03a4090464554101c1001d01e8001d2034140b0f00c0d0000c0030703d84000854014000135400f1070407882180d2045026427611600880d50680300d031740a410500034840038001901443d15500c2d41d6603124200c0300750703503a40c43c4410718007209600c004202da07900084800f81c40b5484a020544210140c1c001d010000140306c00800c02e0201d48110048413402081c0006480c000001085115400410030702a12000e0501c110040c00c0074a40c1d43e40314503510702240c00101d142003e07a1701c151016140c4480e50f580c1d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 744603210 1250 744601960 744601993
    0x1009061223062a03040b04021804030804140f12040906060201182319110904020121090606080d020d1d06030a0e01090b100f0b1e09092a0705 62
    0x40d0b800340588800d0200c040c048034983c41020b544154000d030052070305411300c0e0060104a403c120324808038411102c0c1000017003030f00130519640296000c0c044440b2004502d80441c142503c03d00300f106940030322a801c21041000c5c10160040d2001042d04000c5140c0c1c030318080c0d0880b040c4140c503004036807010050101250f02e04216007010b6100b207113400c020050580c2950b080141c002442c1e0103c00a440c1200706000c1e03a01c0391403031664815110311185051940018062950030300d0724107050184e058511040307100036000040480e46c41070080c004c0e20b40300c24101351039011250001c0300501c10b0300142e0750340500c5160740590310240007802040111b903c0060100c15400149542007450b182c42444205120134452445c0181c0551805141e500b04848001c10703041c01c6500081c44141140d03002e12860995004403607805c055035142d0310a050800c1c031004d055014882549a02074800710411469444400b6002846107006030361901c00b010610354080c4601540c4800382240c0d01031100170a600c0c02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 744604316 1106 744603210 744603241
    0x402040e18010c0c0b060d26071704050d030c030e0618090106050903030a1b05071d0a02160201030c0e04050109020a1b050c09100906122306 62
    0x441e00c50500e6907170060300d07107446095008031450820001024400c068010680040c0782c0038030491040c0841c0d0040c14065414401d00c2e541c1410300d44d1600c00701c0d426110001d10949444006890071215008551002c50034098400c109107e103a480502070f2501100c1607519002d000340110601801d9641a07100030280301e014440c420703480d074000c070507940100c081c1d00c0e144203049151080301004000a560180242c005c090010800d089503c02c1100078070742c161a5201c0580710082c8103001c030700c180300800c810030004d40840c000544c8280c00403c14200c1628014020001441c001811128280d0000785c9080e40080c085810030f40001030051303c103605090145425070551a1039840d0034000e1070349445200310307000040186c47c1500200c4090311080c2d1040201c9901c40e8a24400394031682d8055542e240c001001c0d5441c1800c990850001c2e40344200074003000c1d10760400300d10341c004 = true := by decide +kernel

theorem cover : BRFrame.Cov 744424460 744604316 := by
  have h0 := BRFrame.cov_init 744424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 744424460 ≤ n) (h2 : n < 744604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
