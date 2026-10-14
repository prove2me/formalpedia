-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3108
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:41:21.081921+00:00
-- url     : https://prove2.me/submissions/f40e436f-8753-4ed5-b4df-92189c63f217

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 558812949 ≤ n < 558992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 558814199 1250 558812949 558812951
    0x23007050402040b0f09150d090b0609160503060a120b01030311060412141216020105010f0501120213052205060a03120c02220504050f0d09090509011d0a0501 70
    0x36114010002203204510815488044c20040d0442081341c1c08054100e0880c000c1c036440362409030000510007076100e0415141502e903a1700150701082030440700315070052030030380703a12096142090018211192004110742408001300010f90355503584048900508080c41c4148201e804074a006652054280011004191150003540c01e043c3c00040c62071045030440e103504050b44560f5030544880000708001080e01e4010004401103201c080740c858001d26050f18203074084004454001d003190342c107802c60b98088801040801c240c0ea403110822150614861006030380d191307200342d5440c044095900882e0001090003065060310603000c98a00c400350b031240240000d903900d0b800c00c16084640d002c01480e140c50480b6800e0020301c030b2420151183e10151041701c00505140c88000b141d0304c81e201074240d003900d503020041040028085550741183c00c0c40200040c0c211240b02518048682c01850b00c1030707968100040354440300b500300c00d0404041d2a11101d200b40c6044182d43c403071446003000c1d5055 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 558815449 1250 558814199 558814213
    0x109030215011505040b090109030f05030d1d03181f080a060605040e010b0c010e0f0c0a080d140a02123402010801050d080c1204030c06050c190230 65
    0x2810283c407284a80121907500c80d0f203024140028007005d034000c40781117410040d103c1d4001c00020300e240c0440b14a240241e0055450b1100700e82034a05445c00d0341840c007600316000c2e411200340d140c0001610800070201e44034401101c030210204080d03119400740d400c0d1284130315420790046604040c129000b0960102c00f449516240d00050f10035201e18403508103404c0081c0010040c0c1e1000d000505003034602c020010401c0c0e01010302c2c0e0ae207000c10079500c22200307030811100c0f964503241c91103010000344580c2c005004002c44000000c2e09070b14000c201d40005560004620007094424440c0680a2004400c3e00d5254061003203082920341513110958034422014103250065500401c0c0303a0807c80d030507900c000c0d40ea0309000c24081e0003400d181088400b0b020500c41d185010744103007e02551540c108802c25240c501c1d41c1010603559000b503000c1401d1000421429005143c045001c0082c841c05140707120348030610f807010a1600c0b5041c1c50110007442112020641ca0b0604c0c3e855100c4d0804c180c1c115024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 558816699 1250 558815449 558815459
    0x31e0305040311030f0403060c020c1801080c010c0c1505040806010807050f310204031a0f18070639020a050f010e0f04111b1009030807080a060503010903021501 71
    0xe280314407084000c00705c00c18030040000070841c0e00211044200d500c144d400411004010814400c0100010002044542c00502102804001c0d10200c04800d20f00410365140a40f2899040072903800740000306000c2100c0003240d1030158088500030b00c81e00701100c03015a9504c3e0345546800e01c502890f0b01c81c0c0c8130404121000e181410850640060444010003038010001c0c10802840c010380440001a03001c1c40300001054085048040c1d40502c5c00e5815040d20b06020000071100707005182c000c1e07400c1e0800c1c01c180100000103010003510341a06040d02c00030307405c41903040102d0080d0300306110464204503208884040511001d40e0074801d41c0c541c1d00305501c80082241312402c410b1030303500143c0c00c1a124062843c0411640c260040c02030000220040100916402d0b603001e00710b00701c95126850300303414030010100192101d04150507800c21442c0c0d46941e000f0000880902100d0400010f00041180030341e0340d40c080c41c020300e00100200a001e11926010b500c0c0c4c4824622803209148140000513 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 558817949 1250 558816699 558816703
    0x3030a09120e1305070306090c020304150512040b0a090606090b130204152f06040b011e15030b1017090f0304050d05070b0301030807110a050f010c031e0305040311 72
    0x5000c090080400203003d001c1003601d00104401400d500802d0380307039040000c000f0b856101d4000c0907038043c4c0c051340e80e440c2007005440d00e51801401c40c100300b2000f0802c84250303c5000c0340090b002039114519030710750740760505803401070900e5100c0a402549403040004e029a1968422035404c401540d510440380b01e02c4460b03004a001d107106001c00560024104d148981c17044500c9207541150402003030901140c0d4208883c42c000680c80c121046c1c1c400e0f0f092109003c400800c15004040c04070320348003da1560014407440385407a01c203002000c0c50b07501002c04500d00981104441d0311000e80041030b181c03078003480140b40007003491181c0b0f0100d8a0b000411801d07e0040394030f41440b0b0300c0700011442c01d4a40421722401d91002d007400d550a00641001290740714005000b940210f01803032444c0d8860302d0b1030404a03a54110403880501c585074140b020030440e1120601c242e41c1d0282424414911000e40c1001d480c0128003030000d505140e44038083c00e41442d0543c5c00140194083e035110000c501c45012526 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 558819199 1250 558817949 558817967
    0x818132901021c210c140403050c0105070227150d0b060603250302040609060215010605160609120801080d05030a02030411190905150604090e0f03030a0912 69
    0xd801604120322100ca071880c0e002e0b003041c007082c091074501a07200c2610b81d6040c00e41c290340c0f2400c184640b14029400f81e0b41d885030300038103850324141d0a14501441d560f5266a2a404508c05d241800701c0032a8010179903940342c18402c071801140144034000c840707848600068100c01c8461204921400d0441c508908000c6210348080354044070140441e00d450f000c00039a074000030001103950b00c880c42001c0207000c003986400c45680b000d886c0980ca4605003c00903110704031541100d421503002e00c003440729100440c406217045a1190034030540d160010071584040000c0c505002c2c202c241004030070b0080150580c1210400c842e1662010401d0744c80d0005691282c500c13219603000904e080c0089915602d556000710f800500c2801540d011202a20100711110201c0a0300207540c112068100406409030085592080318202c500e00051000000102a40a03d00903190403961300d00035003050203400c01c00c0c0958101a00122500c81c5007150a0001400d80c1e480d00701e450300e00441d00c6000060240d5420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 558820449 1250 558819199 558819281
    0x80603010c090f090b041d0601050a0e04211416020a050319081c110306031605060a180e040c14040c05030f060406030819110a050a081813 61
    0xa6264513103000c4421014002503810705030710503942c0490b08101c007d00d40c02816102c0300080642610340c5002d08100e11849560300c00d00c0340c003c44100300000920001107000d078100c440c0c150942c44981e040700444211580b0f400790a041140065103205003c07840300c3e242d80b44c0344225031076218103880e2030a060f25141d00300d01042c059403203150000c1c000f55100c4007a141480f03680c40c40b401401c14008034542900d910742c2000051400000601145060500282c0c2c000307c007812107511a58a4400441c0c0c0c144240002c80d404c10140c0f040012181c518421100e00034084035030b60030701c10304050034500b26000c294032400c519498a07496144950406000d82c0001200c40c2c0c40e00c5d42103983d20f080000804c500100950751059a900c4044006503045000e8240326000300c80b000e40701030b03015002511001640590356030903440381c3c905c1c0e0700003030000803624031040c4c0c42441d880d22096040080d5048101154500d50b0040d01c0d00b074900d426666542c05017940c0c101d0501d0290302100440c48481a6410744120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 558821699 1250 558820449 558820469
    0x20f1210050901060c0809030123071805120307170a26010504110c070605090f030f07030f0c08100f05130b04060e10090606150825140a080603010c09 66
    0x4110045c0036811030342105008004051800520000003421900800c0c201014042c20504c0501c0d481c041d001c0d0b0540c0b100303150503c030a1541001041050301d115900c030b01c0d4803581b612403d140400500348103031207099601c000c00c3c03070001d00c640320005c0003071b080500350100040e0712410840c843c10b21034180c00b61000d86140d102c00c580c1d083c48140005030030b00440c05030402c14200840545403808005510003450542d42d440d4441e0480f02c1008603400350312a00902c80c0c0d000e05583c0d610307000007140400031245c0c0003000700254146850301f055261415440885580540041c0480d1030000b50403840c5c90001c5100308100958840820001d40ea686020150641d46824006800140d43d98003070b10a00d004581141d030180f0204021000ba0b4841c000115101504c99808212082810100c0c0341c103d004d500301104d1903d01350440c11071000d8003060240795415405e0300e8100d0b0390b0003034900807400703200701c0304056480c3e224184c0500303540000d8540500075860411f140800c10b21610709002a50003140c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 558822949 1250 558821699 558821701
    0xf100503060f0406030b070806150f040b0a0c1712100602061801111c0f090b04120c0b04051f020405060a050c15010e0103120c02060a0f090306020f12100509 69
    0x2031080e0711584002d9550801d5460f0808004074041724105031043c001030303076400e0842c41c280e0280302042004100c070851f544414840300311a03a160f00c0136a002d440d40d140740d240c2c80380d0611b00c044448040300b060240c0749181c40b40700d010081441500a01d04040c00000d003080b83d498240100540030868401c0c0c4006803c1900413845405003802c00003401000b183c000705080303140a03408401c50b0700180305001842d00c45800076046406500a00003000d142e00c9040101700c0103603c5103114040c00070401040c00010400758000e5600424410500c51341044d03624115140500d081c0c0e81d030748018000301c031485090300b00240030302e2041d0080340c0c00c6e5507000c1c20380750070165a84c00c1580d80780c01c811030484460081c03960551a48c102c144a00d8000e1007010785138040c0d94510705010300784114881d552010005041c10803000f40c0c50348812102d90701c500d490315603c2e0107c40752003118041495000104110700000f88802c100c00c4140c050041c04400038800d042d00e407035500184062911521584ea0440007500c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 558824199 1250 558822949 558822961
    0x3050601020d1b0201090f12020a0b0a09051201090b010603020702030c091009020a140703270b090d02010e04090b1503151807380c0a060b04180507050f100503 70
    0x4540d05540d5106041501c2131641301c0c7e1461140503003a40007604140350b980742020551402541c6000103044906036140b8115007510003c1051081e0701032136004001d01a4001002582540b00c3c820203034004c40408555615000020041d44c0505000d80c0b180c440d408440c1801c0c036202140a020b90481c49140104925201c04200130f90860b01c072407428007808855045281e80c3c2c0c50b0041c00c2d06407207640c9503004442e504100074510390030801c510f5082c41c401042844800c6015044561904044900b5551901240f00495030005603203a020b4000381044000000c0004038818140901c050309043c403601c01d01d110030f0681c0c80c0e5171510f046594800784804103401000100300c40d0300140180c0b080c3d8161a40340d010f148a06240c80c81c281d8540d2000da43e0300b82000c000c0750717036001c618081000c001e86040c0150f240c0c15a6404840d01c0a01100d44c1da5682d0420350341c03594001c48012450003031814000240b400c00c1d0340c0f01c00d0113204070b502919540305104074a1502d200e08548010268070b80d5401c6032500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 558825449 1250 558824199 558824237
    0x51501030b0330040e040b04021516170903010216051e060414071707061205040203150910090c03020a0803030601120e1204081b120703060b0d080f030703050601020d 73
    0x4100d00480460801c40840c5c002621106507100da8010060301449090500c18015181c0c003d42d074000105400b40520200c9000c50310103050119003000046d0315a1210080e0040c4611400c1100e41d4950310005c0c0700030344604030500c07248009000314103507043c88807150219030185d04c1400e040c520b1500103600040000e200708881c90903040c1e192045907180354071094004000952084880042e500c014004c1040d2580228504a0310128240c00e014a00b0070341c3c04242e0302c2200d061011242e03010840001c101c0a000c211000c0000d622900520508090b41065401c581c403601090b4052059088041402e204c00070071640504410380d0f41c154007a4820b10300e4801401c0010010f1018003909000030240f0300080003800203081c3d4400540b40303a0032844402c12031081c1d0040403e0180881091100791542d01040403001c40c2d800c1341021881650105c00a181c0300702074180104045000304204000c2e154400c040c503c5444151010440750315007000580e034856007404a40c000030035500000b0b49281070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 558826699 1250 558825449 558825523
    0x21f080411061c2004031a06040c09090915050a02130506040509040b07021c09080f0607020715090515070302060106050705060a0c03020d1a190e07030519051501030b03 74
    0x340441d0010f081340c03c04002d0040358015030081d107860035281c68130710100ba5640d00e40c42d0001001c4800b04204c0100d40e80140c84602c0c24805c00e0180c90303460185405011600e5035008031000b680008100f03d14295003410001c1d08808501444851500c001040a0a03c0412202924001004442186d81c0c81c0d440d03555203200106104114010780400c04090b00328075060741e1140f0210780f103203401e890504e0075140c40c046d09da15403510503511090a011007550041592400d0301d9850a0f6060100a612019500181d407540b03e1608085690205010058210060300459111740c0c20784d01c883c1d903100340842d5540140040501640c10079004121164a035901001001c1000c0c2005801c0002000c1100100c0b2035501c03040e4806084080b000c1070700d00d0980b0100345414060340400c490710381003c01220340da40740185404117060740c0344089400c000c034015440c044e810054500b4090352a0001c8640300c4841d0915419010a050211401ca549404550b40c494904102481c0c2050016003c001c184206 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 558827949 1250 558826699 558826721
    0x512061207030b040c05090a0b0d02011d090405010509060c130b030a09080d05010806130803040b070905060d0c090b0f0a030c0915020f0c01080906010b0304021f080411061c 76
    0x204005000001482e00000f040c4100c1c01750030740305a018540b109000809000410758075a2500c0c2003161046541c0f003c2025408a0302840c080c1c0c102203035070484100031138401320f030320398441c0741038003003108010054102078420381056054401588504000c81c10380d0042d44410325882d0150b0301d00303200da00c4001000e181d208400c0c1e100840c0a0240e52150141a4060581841c146482c0c034010302c100b00080003c2c40e000b14001e2091400381c1229110848d1502002e0300c001c1040c960800411110b80c82490076202030b0200030596940c038800e5229000c0200760921803a804201030140010302d81c85104190f603019124400b40a1803c548168110000c6c92900d80d040d09000e145000030401d0500358050351400a004d4004085036065481c681d0715149140011504001b5078400b086451000407402904484808600c07a48a46441c40061805d12a0071481424108504204100d440d444481e180c000c0d800340c604440108440000e12000b445201008050040d60404141c82900d045c0d000c01c020070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 558829199 1250 558827949 558827953
    0x30b011b060204090501030f1b140405060d1e110303121513060b1206040e070e0901090807031707080f0c0a030f020408011415100305060301090209010609060f05120612 74
    0xe4691308840c00301c800a810170f90301076940102400c10805600a140d400d078071020750715410689070135184181d101c2c2406219002d1500e84000c5052900c0f0403211800940d8800380b00c1000000e050341507c403c1c98100c0007034801d416050502c91003420040112500f8900c020080c540f0b0340d88070301c0c1a408c4040103034000d030b82000d2000d1000120f82c1c0303140301c2e92026001c080c842030b540703940c500c48402c16804082c0403c0c0c412071a004086052600003d0487c045980d0a0b40b400d40aa490488035070040ca407103000900a82000984013003010750200d5403006e400394081d02c41403503440d0b650044440a8044525000c40c05130380010800d032400400103003208808528000c1542d506440284099030010b610800040e03440d0104510100902440c095020070402a540701d49500c0784d0000e048205038840540506949502044e141e4500b0b40007034200a0f009082c0240a594408000700088802c1c0f040e4400a6516980d02c0022072040007150125401014a4006501d60208110705a04000381d4502e041c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 558830449 1250 558829199 558829207
    0x11060a1a0423010f06020111191b06020d05101d0a0b0312070c26030403061d0303161d01090b090d05071203021006031509060e0a1110030b011b0602 65
    0x1400b082c400d07800707085402c1d9a14512442c0c000042d09540c0c50918981002a080c0404080d03c0d0001100f24002c900034034128142149101c29541c001c3c00585025120303600005040f404a42c0ba0740003540501d0711628662a1f003582c0340d0ba42c0c003517003400d100540e2482d034961011600044103500300b210106070040c00d4801880d0503d000fa0850b03801500129002d11124034104200080d42900302c01c0e0b14054241003440030340d040c1d00251203100e103000c000d00b640c3d0388039a40c000e400d01c948a550f14501e20642225502d04103184610320710180152407500094803640e021079011248241d50307000b8070301170716504403050400e0b441d600c590300308100d106d800c070121013420804520100310101c01483c620b180c0182030029410000d05100d0b400311440ba02c1400c00c030003040040d412550344581403468210004031044036140c160050b117541c01002038548926142d50051141460303600144d08001c8401c4100b0030841c0ca0282c05403801080200e003c944050418600d000000440f652154400d080051034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 558831699 1250 558830449 558830501
    0x40506190203091806030c0d03321b0c0f0a050d111008040507051801120203011d160e04020604150c0f03050703030f060806160c05070611060a1a04 65
    0x1540c0345444644e40700b815500d0901c03204d400d0911007111110740c00d4404c44d101c0c41282e240609140c50f11407801c0002901a0a008a0700c1441a02e070140801403000065036440203c90480620f1a50740140b2454010107503d0841850f202c00319040e480c0020342880c602c249020104101d40000500544201c1040c4c164200300f43d446051607003000e4002e4558140760f04203814000e1074580a5000b50380200c09100c2e069900850320344009045070340e105800b00ca132034240e201003409007600c0d041b043c409019500e82204000c80c082050700480b06448820343c02d49640740c500c03480e0410183c0b40a50064010441409015600c0c0e10005400303a050400703c0c42082a0b5603003001110100d141034000a0000c6050002c00d80d141c05802e01c16020301509000c102d042503041c58aa82000d07001144110789602c442c4d40b240e000d810f840042c0c0c0c0d000010380364642c0d40c80102034050540040030f0840390241900140d02072489104106004020b8542404100040c80900000b00070781e68a01400c10600c03514802 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 558832949 1250 558831699 558831709
    0x606010e0f0d0b18073305070605040506060f01031407051605060a060302040507081b0a021015030507050909030901031116030c02030609240a020f0a03060f0b04050619020309 77
    0x2001d1080780181c1d4242143d9000c0351030412017a500104007a011aa4019000c0c40702070349502040d655a05040403070046214042d0365034410403a00030a0303a4140f0b000c00040c0540841c3c0c00384101000e4070040d079000d03041001142266500402c05000c0860400400c80c01c621880150003160028241800c0780f01150700ca0615060044410315200c0362100b03024801c60400d401030316008003140c20f00107480d0420710200040b003201b2000040309a240403420040d5203208000c00036030039101c10b000300004512021070b14145941d40c08152801c0c46000b0000420b400c00b00f68561186440314091801e18806d0b00045016110f2080c1030a041c02051100d815220503035510311207a80c0c82500e5142a100b480e1040c0750038641e009060107240d81003800c150101000d4100c40310516000900c48102e01d41d02d12903000002d02600c00b08a00144c1f0104203072003c1501a4011405d440700c40c03002e46102540c0e9055410244a0340c010f00d504070700144035821032030942454020810b060340c015a4145008180418 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 558834199 1250 558832949 558832951
    0xb01050714030a031a0d1103010f020a030603020a2412020f04060216140a050118170604060515060d1a09070509190b0f030703060f0306021b0606010e0f0d0b 69
    0x801180c10025048221941501c0f824012030450102d203900c4200b41710004520001d131441c040c10158045039440b10642e420742c04620300f40704d640720841d15440c7c1c0200040060400f40401c0303010341040c2001160100c000a00301004410315640802101c080340390443d0500119003d000b01e50b078081c0801d0140e41c0c1c07588040c2c405001141d00070820708007081920504030b44558400a51510042540d40460300c03031001c1001520001e091544040303682090500204072140e102c400849442084802c0d840340c0403803000c1c0124040c201c1400740b51944402c245079000701c3c007030b2154850001c2001d6401d002c0e4603005002241000c0d0a030000d60700c0e00300301080450b5000ca451400041000501e5201890050802206e40e501d00c801000d1032070511025092a1080301d400b201c50260120004642d0f510a4100c2c1010b0a255007090701072540d0b91034010003a400405182c14041e2548094018101c400180c25200c0d0405940311a05540c090b0b080c00768a444581c402038000003090800d0005c00c154080d85 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 558835449 1250 558834199 558834233
    0x5150c0601091b0e09010902071b080106032f1c061e06090b1311041a18031902040e030d0603120201110703140f090d060903020609070605030a0b010507 67
    0x1081e0000440d16401c583c1e042c110558003448083d6600b004113485100946041d00d10030300f40140d035807076a410264221040801a100307040042c65000c2840740064101408032440303414986200c0c40705405c501146889030202121611026840c0d00030352610408481c07040400100281403510302c1e0b04c884050300ca610a4083c102c00202a040c40c2c3c40c0c44a100d00c50040c0303c422410000070941d01c00240c8640da01c2c40d0244d0b803168441d814a85d555400c0341c1100c0007031090300d103620811100e1000c08246070b007050f029011103c1d00014080d04c05e040104403148018020340000038040c000f9405c1200400d0b454080400ca4482400784c5070b10200144140c901030350194140f450101c414640080c20740b0130701500d1a4002c0c90900034100000e030400703456400103400c0904182c0302e2344003018085460148103015030313008240c46c206100b0712546621a4426034065030a94009a44105143c2c2e9100f100d44100e00000300300f04001110048140d025812419051404c1440d00c3d00f01c4c3c17108800d2500e1021741c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 558836699 1250 558835449 558835451
    0x8180a0b0f07031e0f0615090f170d0309030e040606210c021b061e1804050106270b030106050c061308040618031b05030606030604050705150c060109 66
    0x80c03190780300040d1031880d40100685003c2c0400440e5820050a021800c1001c000054407030003160801001600420007515980000e5180380013000001000e6030b003140f20b8403011404403400801c810f80d0341000e520200074424001c1c40c40072600f880c218010802460107604012030703107800590503952409981b00509055490350b01c803125204110303566202d072200d407000040c41d005084a80c1070b004501104854480c8101d41c241d03800d410301050451040365142a451206040c04840d01d4031039001400707203024507900042060b0081c0003400100c3c1d80a0041d0004201514100d22141c009040c955010380740c07400b400d82101e50f503941c00c84901d801c01e801041c003042010070050150101003104607031140c2c0d8100c5c11003205205454000081c0b013079014040421000b4041e50010324040c80140c0019603000d41c09004400c906000501001090300400d88a4059440072600c2881d00080c01402160090003400909250904120319064000b01c03a241800c3c040c422950b5032034043c030802e8003c00020070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 558837949 1250 558836699 558836701
    0x1080c0922020403060b0d03080f0c040f06050a02010c030e1002070203031623010b060d020d150621151401140703020102030412050310031401021614070b070b060108180a0b 76
    0xf821342c0560302c40721b81e2a03000e40c039140c20b00030201ea400082c550704441d01139004005600d038251044031500c2190020104484c1d0342100064281d0301c07500801104a296000b000500d001c404202c043d10204d1504242135409580c1010701003100d0b600510182d0f100a04580c03034041140001801c19106c03003000e03600c0c06110000781c400c000e00700604164500030140204901e061010004081d0f0150114201c1c0e55680412441c1c6d85013815032141644803500c50b5a03035901c52b51440d0042042a45070040c0944032440d10880410f5a51b81c0a82c0d051125812101c0002c2c1e1f0410f81c004008417107841400e810031003854a120102c004250007800d4860181d400582d03285014103000c1c4840c842000c0503030411100b0001c10880d0f02c02e009102080e40d61064010f00703094a1a450b5601a0140054041090380c1d000c0c7d864041205038040f0680c10440c00f400d940034207544512900550089001c05000b0416110006010b0345c42a0503843e8000011340800840c00f440c3d14441c0d10b485a000380c21079004449e10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 558839199 1250 558837949 558837953
    0x50f04020714030a0e03150c090d0b04050c010212040501091e032301200304060504060e030f0309100608070b0306032a0f090603150c09030109030917030901080c0922020403 76
    0x8440061514015001041100311807e03580b001c014005003480031811000c145410b280c0d561724540c9030860303044941426141840d003452a01da9482c0d400c1c0740e02500c81c2d0110a040d24030100185c90880704140c4848403150316000960810202c4c5c1e05c0001102c5c2e03c2c4c14401300c0050f880508180c1c1b2080515007070300901d46190002c508403150140788a285001c0036004485007051401100d070311550103480495180c035503203809409480310090a5446010214855000780c4c084c80255100343d94130000c8480300b40d50088800121348540c0600380c0b05420060007400f401700c10030019500510094216601d000001042c4400c16214101840c10082c0740c180000080c0707031880941c01b17401801c48200425061601c00030740c1c0c0e500300c0040403d0803559000024903250340e44c003d450300300030f01034002d214900c2940703801010308486000d01d050000e180c82c0203502d40d000002c1a01c00c0202c041c0c42d106001c3e150b2a94240003504041030655211107040601c00501030040319456419459000140c1c40c0d80c114 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 558840449 1250 558839199 558839207
    0x1103010f09060806010528050604060c050606040c0c0b0714030c040302010e0a06200c040903053a0b040b1e10050f0d0c0228140d09050f04020714030a 66
    0x7030f90240480d580700c10010b101a43ea400005880c50b40200c92101c030b03603010550444810456984903035032150001c580080c00a420400048425100d0019290b05a9a0034200012100b800c1d600c44002402c40f4215400643c50f1034559070003145504040101d1a14120200c00759481202c090035000e5000c1030400440d40c02500e060b01c00f030421110915035601300000189030710101003065120561103011f50b0500c1800b0702c1003101c04034000d0000d1000c1c0b006402d01030460340c040d0721500b103202441d140030781c22510443c400801c100007070260750305085480d00101000d841d0b22501c0a40c4103980d800e1158a6070740f400201f42400c090b20b00c00d8903001d03070000c0400451a5940444105110307042044c01c07000305402c8129032110303001080c005050b11030700508904c0c0c0700c8801e902c0780b0044070301340320508011032088849462910992032120040d490010305034403401c0700001070f00072402001d4184128540000014060407010b0001030410b6116100e00030500704049021131035070000a00240c809501c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 558841699 1250 558840449 558840461
    0x6072018130c080d081605040f030b0f09070602060609041103060a05180a080d0e031e04080d211e09030e0a080705010c060f0209040501140906042d1103010f09 70
    0x50f1000c1e280c141504200502120703801008111032000115030050010301480c140e902a00c7c041e00706c0c0f42541d0f1a031030405000c2c2c0c41994026918426100050210900001e440c1c0a0b2240e65000d80b1440d125441071058980015000f1909030001507a1040c05072001c000051044079a200003107158140500505a14180d84003001101d801c100c00180120f00041c0480d400358200500c0010070400da020f81c0c60550144040464004168440002a6540d900c02a100743c46144050320060196008107880620140c0f07110107a01f000702c481c048440a2039030002118480b08505016010600e520800803aa0402030407008200c00805058071424012128009050000003c05c406401d102c00030f409030792151401070026441c0c0e048120980d02c0c5d81c040c0d07224110094800e2055584809407401a43c02d110440d5000e0820440000c0301131911707000d6040300100700c3c03510300107068500c1461001501c1c2e103481c00c004162901d40041082110000840c0200220300071007c20908103215401a506 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 558842949 1250 558841699 558841709
    0x1503091f0f05250305012601060e091c03150915080d020d0206060609030a0b0c130e162111130e1801060f060e0102150103030203031506072018130c 65
    0x201e17240041c001d81100904156490801d8041011440700104201707026100da60051140071550405004440341c000441c0c440d61546441c101400080d0044100c0031218184281d0074003a29621003009401a0303940f040104820791840711002a866020061505481c030b13040d0740059009440440040b07905011081e0003401c200e424600d404000b400082c0d0744e08a41e000a400c1c080c924010031880300d03240088812100c180d20360341c032a4940c3e40260302003607501242c08407508100a030690403081e03c55154240001080c3d00800c40d00b00c6940c5120004002203050004150810802e0024010710311a031400100190800c5094038039020f40d032001030741e50003400108581c0c1000380a2000c040b140c1c004900b034914034504241e402503d000100d07c1c015014070620500400003001100313141c0d022006500c40c25208c684007481214000500450f80b040b047c1c0a004000e0303841d00c1100f206130b807482e05c030254040100883e54403408042c80010901081c1e038050402807494003414104106003150600900e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 558844199 1250 558842949 558842951
    0x30c01060b04050f22230f01180917031e090606150a0504051507081305010315060504050d03051209070e06090402010c0212070b04141503091f0f052503 67
    0x515021100b2024030420458a00c01501d841240000ba80401c04001e0404041400c0c3c2c1b2135400c146a421190010078003070480030301303881d03009124106542e0041d034903429403024003900144482400580642c00140c4441c1d90340c0d180101c03060003480e4020400340a105110701810244c2840000c21070b04116603116518448010b028112820323410001361012508180c0b11151215043c0710303441214481e8020060800e00b010510080b000a4410040c00b41d034030a032020441125021808072442030700e445080b0000e01e0412042c000350501d11142c2065510904109041c042c55591100d011802250200a00d42c1700381c80410a41100d1221503130400c006942c0320302181040d400007006954403401c060f02486c0024540700364240200041001000c2c1002025115038071142904200100508014482c00c0b2501e281c0660600500899000b101400024800402098094a84016002c02413090b039036855198000c184038034000c0c648201c0030000c02c0070070b52400004802c000041495880109 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 558845449 1250 558844199 558844219
    0x601050d020901120203010f0c0305070e0303090a06111e0321010f05010509030f0f011a150a141908011806050603010b0c190807150b030a0201030e030c01060b04050f 73
    0x150b200d514946065501844500c1c201c07070141d0002c680501100e04c45600c0080c6040c014100244e45540942c1c0920304981d11041c4550100c0200750f528012003003800d5015107222010004507002c1c4901e03440254411050303500500101c54146090064402107403000e4000249480301680000c2c401d402400e030101e205081d1b035042c1160782010400f14000c05041c00303800606c901080d41e082156803614030f024000c440c1201340088515018200c07000744000c1010130702c10222403a1130070102140c01217603981c581c0350030409040f500b1142d40380060701150b81d4030b800700000030070410081455402d07440144c0396604554500612003c104561414441a851800d0014450f80d910030f000c580c119a010031290b074650030300004842c1040f129522000288400c10017500800990341c020b0011540141180703845a0744251806058450186880b50305400c4503455030015070003a800340101104d9a011241001c4424a0480c21a2040d4004c00401140801d08110500c0c4c030880c007511084090f00d407440a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 558846699 1250 558845449 558845453
    0x90803041217071e03120e0304090c0305090a0b1009090318171203070909150303170f070c06060b031f0803070f1e0206120915060d0210090f030c080601050d 69
    0x40254072090300c03010038000080901d0f224504101d050201118104500401f03001e01031350301e500900c40d4041482c102400d00d50014080d2042901c203190394409091207208603a155820b461000340702206085001170042898444c034442c07003d6142c1709444100c1704140e00c06503114070120590121181c042a803028100f256408100d403203541401100703098498407007c2040e03c2c41650750b003040704a0b41c0f80445025408041e0052201201d010b616040c600c048000c034214414801125003000d0384035000045a1940d20070000d003440d0358051180080c0c1503403181401c04080e4029540c01070607901130607443e40d001c0c00302c01100f002414010000e600d406100d9541181841000801510044034400000032030400c40c8129000c0719401404a80c1c0c03041c04c00c291203403440080d1075092651003910050060002940c00c9240103041c01480303c06041c6440e0308100341384242d542c0080c2085500f000004a1007210350408010354812440842c140e814030020a10f8100142c1c0204d01c03804184000c100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 558847949 1250 558846699 558846713
    0x32703081218030d0f0b01031104231f0f020601060219050a0215070b0105030d08130309030c08030901030e0d081305150f01090b0a0503100c09080304121707 69
    0x9070703003401070400070165841086140b40340a80d4000325050340000a9100301d880d890380c0c40350301c1200201000700800840f240046003120700c01044045081070030007060100c1101c4150205010040c0c450000a01c04101d001c603465100c86100c4960340340d01d81041d40306282d00b0040840c0d16200c1403000f82529850700000964a081007550b0b040701c05400907800c0240311b07042c080101b103590054500103403081d030a90366241c04e0340300950540c3d40d900b0610000c2a1840d0204a2400220345682c132404e136034035403800c0c1c2d68601e14a200100c00f0b11000d2180000010b810407842d030010500e01340515115910100007400303a500008003a00d441d00b003007102d54002500b0a05840c0c2118a86500f030940e03807510302e0110314012030404a644c1e8440340d00200708442440ea44098141c070a80182403006003442800d121400300c081c010154907403c6941400010091540000c041d01154070702241100d0b99450100d0465000d5040404122040c0350600c00780400c4881035414a91503c80c1107150040c0740d00e03448 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 558849199 1250 558847949 558847957
    0x3120e0301093201150e07091802030a0207021003020a02010b0402160b1b130317030f010b16021807030c081b0d060e090109020a05042c030403080703270308 69
    0x3c00d1207040d0540ea20700402400c24000704003100000c00c0348816828031110741c000c03540301d00e42c005071400d0001000d89108200c0f000445184080b8620101500c01208029410040c40540755136402d015010160baa41581c1d0001c007101e03078034016924090640002d0a451501d1465405540100301480040141c0342c4401841a04143c581d0030710386845c88800002262106c017200a40c802081e10010800945040411684203a004965503007141400f10f1880c00f045075190b11601c907980c010030081102d40300034032200107080748501201600d1341c0050381d180d040c4028801c510003050700b0450b1040d05482041c1103a415410070007071038585401c0c458032a05891500ba00c2c60700300424694000036058010b13401904051141524500c0e042140c0c9000f0030440380183d02c5921043e034009042c0c10140b15204508940491504c0da000c51009038503110010100c0c03640f101d220030840040800c0d890005040e22500ca030341c41600302800c500c0c0059212060406509000d00c2480040001a040000311 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 558850449 1250 558849199 558849233
    0xf09030e130e060c07060e071401090f150c1104020a1d04060b0a0e03010f090803101a0a20030310090c0203040e15010201060302060d06030308180309150405040603120e030109 77
    0x1513517a5009880e04802605441b400f100703c0d441401030102d1100202040004c10712030070707a02d41c0b440c140d855004400e135940610841c0089600c17032401c448036500c14880720708c1c51400384501860805030f00d4085012a48819540304c0010f0b0b5140e554442d42445501009803c0c4046405001c140d09002c1c1600040c41100c5000c803d10140130140803481d1000c2d0482301440b445250704011198803400c0400090381b00303e40011a40101103404210003003604044680040c0d0708550030b040500c034030404d03182c91500c2244901c00901900300384201100400080d03118000b00300b61203040343c0c038140141341030b0360280140710259001400140b00c81c0e00082c0015078440240015880030b1032031100140e00504464101035000407002604481340f51040d00b00d54221fa100b99511036041d90f4081100741040c02e07005105405810411200f03500c0d00e069482e11f19244280707a503440c901541d0b0b0700040d040354807541c401c884114a400d2000d603890340207005504401030640c02400a64140d0fa101e040c942204c40031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 558851699 1250 558850449 558850471
    0x6140a0306181a010c0c05011103130602011b0504051507060f090308160e0604050d141009021315031707050f07080c060c0303190f09030e130e06 64
    0x508402144690044801000c6a002c2001c5240c824a14000541800304241e4445510800480c10552285c0c0413001030540050180105074141401110442c120904003822444107000703902003441c0c42c2041d400100140d400000e031241c2e40d0991903284000150b20001440340c03d0104120a480701c0d070b0620074801c5015112a41c441d007600d031a400400d255a00c08001925140615040541101d0384901034001240e440343d0010442c10119104200141620b42000b0f0902c402c10107800c06603c2c042c440d92042904090b02c03038101c0000b0340390240f10321500e00480d0701c400c250000d40c241003480e01c40c000701c01503041c4007000040446000304c0d9010310009061059020001c10000742078410741e40c0c3d00b58002e040d0743c100e00c1d48080c40750b66200303180205000c1b0b001e0307541d000090340350120840300300c001d19001641c2980d0b1850b600f5403000d8100d000b00402e00e6195a0910181c081c0d80c41030140b00d61198441c100d14001c12800c1c032084400d0f681c0c00265940c82d000d540b1030021070020301aa80070311240c2d5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 558852949 1250 558851699 558851707
    0xa0c17070f140f070f021507030e0907050c060c21061f050f04030f05062802070302011e020a0e040612020904050c091e0603060408090d0c0e090312100614 68
    0x400c038040e80c81141c50790b1800250119aa00420102a9100c2002802107038011f00d0584101e40c0400c140c4101500100425100f001c00c0b6014240603198591000440c20450b0034854040301c0701e410042e0458000c08a4980000c0303030545000d41d08002c132440f142d003007415003861907d4008104200c2c200c070f0043c41460f070f00c401003451191084044a607601c1d098400301342c5441d2b0300d25003110b406807140000c445500490002640704520403a03513041c5440e038074081040d14210b402042000b075000003030541c219501c800c80350300304c054491030020034485030450060756110070807001801111001d601c588503d00781401080301c28841200000c0c0a90111580c00c00c1d0745503841c1203454440c0002c80e01e07410000400801951000d0728203c0c10310311042a0300200076a45a40c2010f444c1c10313003240c0061089a0a010401c4d0a040290407890722034440c41d4204200764071140c0c03040f101e42040712006c009c1d0b8000121031440108031201c9036000302c0180c4035000b80c11306109001e0009800e80129a0106034082 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 558854199 1250 558852949 558852977
    0x304030b0a0e01271403040611191e110307030b04120e0112020d140705070b010e070903061d100b0307050607050706080c0d0c05090405011e140102150a0c17070f 71
    0x2140743c0417200407140c1140c3c0d8699403454050030407410741c021031103a40281b001c454031050090340071602460b8012014850180500c1401d00082c55101c815035010f41c0078242020b298a003013007140051401100007800a28040c40c045644012914100d800c109891816a5031070341c21010646803070159400243e12642e80c0b9074528000c00c82507180c0c102d5001c16070700348462260440d004100305800340e86680081d17a01c4028003441d01c80141c03200310000e0003203603080000c100194010088d90381b0130054018100711309000d01e441e00310103c065680c0d00c0c0c0e5038a82142e940c94100604001840291015030038050302c1e1b12826101e188510a0000380442040090003042e02403048404106c43c2da8410000c90400020092680c1c0120020f94045d038500f00c0041129442000e152000301490039a20a443d41419060030441d0004000f0394150311940800d0f5045081c1c4900d024821803145800207a0b00b501004010540940f1682070303140c100c4254180a50240d12582f030f05000d000701e00740180482010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 558855449 1250 558854199 558854213
    0x22b03050c0309040516081b07170f030a151406090904020406080618070f0503100f06120b0a06060c0b130312060b1308013b0304030b0a0e0127 63
    0x3c165889440e000810a00d13045034490031044000a950798030455031004480c64149406204000303548006200300c0d00002d0221210400f0304041038026414140c04060008041e0007e5440c0950075442e00310f5031a0540c0001d14060007050750110000c046803030351700070803103510946078202d010346010070006081d5101d580121000381500d0b4100c03101403078681c4015040120003040310046014a1200045410600340039074140c60b8014040d0841ca82400e0345d4500804164981904464481d02c0005980e40052460880039014210b410b40c83d140c00c24610b42104d000750002800d210620748100c1c003243d0155601f5a105c585a810200826031504041d5003075900d80c0064111241401c00106480030700c20068803003480402c0c9041100f6442c0c1030b05e24280c403a1000101030000b9200c2d030b40041c1d4070b003a00140540c1008a03e41d098201c0c17640013580e00315032250300252501007800051008201107842804440134044001b002020410074824501d180d1065559042ca200310403114140405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 558856699 1250 558855449 558855457
    0x30605161101051e04050a05030a020d03060603050c04090507030b03100b1203041d0a020d15091401030302060a181223030f040308090f0d020601080f0105010b0d0c02031312022b03050c03 82
    0x1a04a81c0c4800d14803074000e5961100c0140ce40000b41030010004025000e0b000b0a0300507106c40c1507440c1468105040c0d02c0c02814001c20b40000c140c2c03291b004151540307042c031842c4c41c078590302e00340826100500700510251009644104800e80d104010403c10342040c030030710440304500030044591075124220000c01038002c40c03207040c6000e4644030b299400701b5890480c072001c403440548281316402d410040078a04503000d00c005005600104002016003400c2d03401010034400703040b0404110000343e10f907c4042d4041c1d80002c0c0200d210030744a10500c041d01d4100444400e04259154034524040400c3c20120002a20080030b010107034021640004042c4601441d001004007103038000110703910000e6031001c1c02e22542025000d00e02007003411005c1030040c14144c400e03550301286412491348c02c81c0000e10801d600001180014010420702c00d44504003500202103100c82c860400a450040041c1c490f8a9040f90420011000fa000309543c0041c2c07014041980606049450b0b40c000c103405825442 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 558857949 1250 558856699 558856703
    0x1116050411130e01050418050c01050318070b040617160507030306180605010807030b28030506090120270a0b0703020619020c190804030605161101051e04050a 70
    0x5400c041030080340181481c0c105d540c122001c0c0a000c000140c441d01c8211104405002070f040a610640c155000b0801940c03c038482407080c140d540d1007105034a0174a0703031980042201c8940080c0402c203040d405040a078021850424031b07005c5081207000700c0300c1d540051134003d0504c00046400014140603034000d00c010550f40b041c070344501c00b60327540440007080c0600a0a0224603120045542540720f4455130781c0300400901008640207050b0391f50040701281500000c0e240e0316810f00800000c0080c000b80c0d000310158000490b0403180302c1411240c01060a08904c1422070030301114031202c911480b80040c1550b00254881c0d20f444000c003042424030707160004d0150880010b10f10b010036a001801c1c0340324090110910040d443e00855000c182c3c0703d501304006041c1c0c4601d1800030040c00154010002ca481101d02a140596a036900c0c01694011184182c846c0c00e81031074a0050b40e004180303612180c15440080229141c0511407420703000d50030b1018540c40c8001c600060401c0710130070458010703507 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 558859199 1250 558857949 558857977
    0x71b0509090321010609032d0b0a060b090a0918080c07030302061b031603090203070e090606010306030b0705090109030209041212061d060102100c050a1116050411 72
    0x46403003079955035203038001d84005484040b880000e0000003100c3d4461816500e541c0d0300d0b0302c206841e54030381e041c5a60410120101071503e8840b0161201684080310203541c0c40740013080c050f1301d01100008204c0c3c0980c2d00c04020900104525070260b41c2c1c045082094030410400002d0f01300750201150140b0400300d500070020480014000315800700051040100d030f100c0e03400c40c0e5040c0e8540e9103019181441c90741050340000103001140300b20242d407074100c00030398040c03400160440c550b0f0000303480d102c002d91045001d84443c1c014044d15000601a482c2e01030400c1c2020700059286039145050a20010b041d00c1c2001404506611142e224100240042d90028030a003080d050504060075400328080a803808210458103554243e0524003541d03003143d6900c02c1700382251107400c2d074010754140000c081904501990b108001910403600c074182030000150303101621001d6081018103074148105404000d98040c0b0001410301002c4405031066600a40c2e0109050340400c425078541d0042801d0b4443d05 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 558860449 1250 558859199 558859201
    0x150307031e060f0519060c082b0507030b010c030e010c060204150305090a0302030708030411130506040507020a0c141801090507030b1f030504080d02070506100812071b0509 76
    0x9646950403180c140c43e04400396a200c280d559003008540b1a40f103444650a804455040044038059610409020b0040c010186400d1856510088605c039028816042c12410800c2d5030003020148901c0f58001010709041011b802d02c200040c10882c5005801410006894038114050340714500e2000640d901100a54407543c903602c5600908050281240000c0c4c50300c400110344a100142c80607841350141c0185141c00c3d03039a00d444000d0b60001304141d0300c401201040101e5925007007520014051a244c0000c0c1c40c6c02d20b00200002d0b2031300a0003040465100036040d401180070042c0c2241191031400750180341e00591404501005100210210100070890000074a540c49070040e5114105a51301003100c04020410002c815003810310009190070022800700b1680e0181e408150032500030841e4a06003d810014042642d0101008070342542100c0f040c0039400c22407203030781e0015160641c05400c0b080b022015098050003405006010000048400003035900810940805000041c000a002e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 558861699 1250 558860449 558860501
    0x316030b040e1e16140103020f043c0b0711030601121101170f06220c1404080c0d11091e0a06141e03060f010302090c030615030703 58
    0x907802d0146281d000f00207440a080000200412200c043c00c40ca540981c0c2c65504084c507054240070003581d00b81c103040c0c2c00c2100c51180717040c24015000500b414104154140016180d00d00d020b14250745040c0d403000c20070040f032558541c2c1c01285069074002641caa46030b6425050038100589160300c0780e90980101c900214250080c05003604141c2d00460b410b00c0d06140c248011200d03030403807940c0350441040000105131044114030dc1c1075003100c0024110160803400e21349001c50b01000d200c3c40d00e4915507988241e01c4a0b030300841c1c006c071258a141007460400e0310f00f6000c41d44962003d01c90602c1404002c880a00b0014080d0314208240400b8000b400705280c80d0445d01031405030a0709054013007407042e0001c3e1440807035004143c10390350219141070440700c1e0311062206008000e4130744154190907802d0408562001c00800d40b2a60303900c480c5c3c58040d45103005001c000c0801405031445190200704001d5148c862103410100c08900706003c580d60343c1d414104278000c001e140c400d400481c042c0204101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 558862949 1250 558861699 558861703
    0x100603181407031e0b0708071101050c04090c18120804120305090909010b1e06040e0f060f030f030703081504090510051005030c04020a020106081f060b0703050316030b040e 76
    0x40e01d200e5001a40c80c0708442d655424855841c1303400501d01c140c0c010004217038520940250750048400e043c052190b1515075030650a64a046410001001e4081000c000b4080d16014044103a001d078240034110220314158040301e003105014040300b04042c3e1000700200080e40c02210000c045591104c20030b888c56203001400c660010310b40901c40c2610383d012400c2141c040c800c1400d10744008084540b680b00ca41c41d1800d00840c0b142001e6800300042c4400280c800034498001c1c403803081a02c13a800b241c0342220400116008840c0718900a621068828050110020880300d8494141c20900129510290484000441403d05030307003241c14941c100c003c216000680304042d0b10780c0381d800e20a07580d95044807200c0c07640922820798558030107506215503003811390041ca0706010078030011070815120030000740b80c454028020101e0107180031991003100050702c580c2001d09007500135203282c6180e641700202035000141062590009a00746070001c1e5010341e110441d20000500248261000f01a4440e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 558864199 1250 558862949 558862963
    0x10506030601060305060d110f0d0501060e0106020d050a0e0303040b16060f11070816050106240801050a03060c0e100504030501050c09031c020a0203070323061006031814 75
    0x5400380c4107440020501c00c1c042d000d098841c0b24041d01c06100d051064840000541e07801c40b00d03d4220038840001e4040f602d03880740020040c2e01a6001203400c6280c108031b0580300c08140d011800319040f202c40c04071203070783c032208603807140c5554904900041070f02c100003411441594400600b81d040080c000f851000416078210301c450150a00b046540102026041565805280c51800c41001c004010014038820090f20b8120740205950070403518507a1810f08603491501719100680d03884d0b0b01241158a1503010800700c030400d150011041d4502404600010345a0000400c07140e142e0298000861141c4880940340c40024501c000d000e50b040f801400591090009035480e50a200008800c1d5000300c0840340001c070043e004054154224040039680c6070705040150440c001c0340b64080150350204043d030043c5009902e008194401040481084400101c10400701e804c03007010000311600c01e001c403404a0700e850802041c148070700c21954980b41803c01000703048807100c0012a10b60b0000142007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 558865449 1250 558864199 558864211
    0xd080916090507110c090619030c0603020c1b0906130e0607091508010b0d090c0b0307021506010c03020c1011060a090303060f1206150b0a030f0c0516110f120105 71
    0x3a203001328000e540ca5854610f980041384e00400d12001042c01401c1900f00303581d92407a42040100c48588030b40e1640321000459200000294010400c45024803050000a14030302c0c20a04082c40c6038240c5001c0b0342040d8005044502c00c07800040e007044810841e8001001000e42074041d1580d610b469203001c3d00341000d5020340d03840c0c1d03010020031042da640182c1419060320014030069040102d200107070009001820400c840f083c098000010b9020102000b5501034001600580b0150031f04071071b0a20595001041141048100418100403d402261a0140c00c10543d10b4081c803160f00303542600c82d682c00100708802c1b48981410005210050b9100100c1203100741c1c0d09200080e511a5444c00c4024507002d032882e00f5504e016110006001903001c41622120480181641960381303030101c8945d0001201d54001c242c450140d00707a804482e2140f68603091060500c036003003005a03440e88207526425100107000ea0362514003600c155403540d08006001c0001440724004601503010240039003815101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 558866699 1250 558865449 558865457
    0xb0403020f01090809060c01020f040e0a0510060f030905030c150f100f120c0b0301030809030f010e030703111204060224070e130b040f140a0e0d080916090507 70
    0x285801254043c010020100d82000e542c5041518000402402e0341c000e0b242d160b05594200802001a46441c02400080c0440c0d01038003031500d059031480c0c0959030001c100740c4a401c42070b5409e00c00a9001030308558141107a00c1e00017103003204c501e0b09900e035210b80e0420003124459044549124124044410711490ba515581c090315114060040e084030410302071003144038540041404215208010005440d0041d41501c400590300c1982c159564000c0c3c0081d100150002101c40d250b003401c2000140f0551981c0003000302c038843c0070300070b51240201c42006003046488541c10100b000c04004c0e041c450200c206d0303050790b6070740e540324060765481c01c02c280c00c1c54030030f1482404c1c0c080c0200d1001d01c3d403242c500d584480c0301248050007040100c100c4882c1030100b980c1d6031011000f25403214810b80701d5200000320001801c41c8512000003501c2d00041c0043e082604010401620441c0421102807885150500104985802100c6802c4ca11415118189c540f240d4600155011440d000320307000742c01d2a21 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 558867949 1250 558866699 558866713
    0x6031305120304050616030f05070e030c01020a170906040320090a150e0c0c1c1d15030c040806130c080c0d0b0a0626010501060c050703060903050706090b040302 71
    0x7032646480d010403240075015810040c00100d2a003104662120780781c2840c940086c2c10a81440c00004036681907403050000307205220507185a0504100c01c00000d80700340010f140c11101551030780000c1c03055001c8080c013500e0100703508515841c2d44060314007950f48800408100300c0c22035814952600b4100740144248140c070003050000c4001c1c031549482403040100c0c10722150030914510070407000a400501c1e180d800f00800d44c0280305c14040c0840c0321204050014a001125500600210011003140c41410007401810401e541c3c0300074103408000c2c0305041030740300d0b69902e03c03e0b00c950003207502c018528043c030020000c405200070aa03841c014071609502240c9912500300381e0351046e002d10940d03040a100c00303400000c10708000c02c0c2d030b900449042000c5002a120251110445c1540b0020403400600301c004011b101d40038060395015102d1440c0000308003103281c9400303580f414103120203800f840e0f4500a80043c188200b08841031581c000340b081c0044030003031074000c544090845d411b80050007450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 558869199 1250 558867949 558867973
    0x614010b040e0f0403050d050f06011112070f0609020306070c12050306090f04060b1c140d090e0a0b0607051005011a0d0e030d1e0b040b0114090406030206031305 71
    0x90750241d404141d60494242e4400414000c19000030b8429424410706103d8241b00400b135000d0944100d200081c2c00300c05041801c005007a140d449144c04829030840107041917983d80c4001520009a086a1a00a00b9590b800c0902c000c04070500085c3d010f0140b0010800340c96004001e806c139003032290310040300c84aa105000c8806020980705036501107410b20110f44030310780e0140c81c5904039004400002d46004103800180b01980b040c84440200740c0d89c0c0c1c0d00e001c06c1c45004c0c0154540070031710308041d0070501019540200400b906009860a500785080403418006075a44040f01c000c2e805403400e5624505410032594034400d14107000700a500340f000105034981304034408012500005600c500344211141840081c00d80b03442200c807031348400e0144034250540313070155401c44040d40c80385c0c0d1040c403c004411400e40b60302d81d1101e4015030421a030f841190b68000804080290301002003a129142030700001c024013000d500280d80020003100307001c1c11121101030102524401c00803240d40d001c1103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 558870449 1250 558869199 558869219
    0x13080f0d09030b0a1104060f02060f04020604030807140136031b080d051003021002060c0304031215030c05041505060d0216050609151e07030c0504080109061401 71
    0x412040005041d52008200280e03541c0102030f0030800c074900225001d0921082c0c0310403908582c2c8044002070001000b00001da4041c4402e41c0c102501d21040400d034035094000c180b10307100f103100c01002c0c00c000007140707020302c0034120001c1a00d48075113000740071000c80c0c0007140c0c14401c0700d144c1d00c002c8600b8039041d0705006c00820300a617601c0c59054403010f600c40d040c0390784580d03002c001b80e1090369421070800191280a01a00c10140300b0501c010800407014114014000c000896180450556005c1028851144a000c06403a480703503061070310782060152411800d0140210200d07004102046560103c100b10642d50900140c440642e42000110082141105c2c40341c0c07688511a0401e030b00300703e043c42e5400581c00514130101c10410200903000b890b514946400380842d01c030344064011004000c4605005030b07038241c028066070201d50000d00d5505032104030003c05004281415550240340348642c0c002c80680d4001c0c108280204076004450a000000e45800c10304403e1035020a0000b094610030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 558871699 1250 558870449 558870463
    0x31e050a061404020a14130f0b0310090b130b04120e0d050a060b0a0f0302100203090a120309150f1d120105010e060d03080c030c04030b15090c0a0e0f1513080f 70
    0xc01055903260701e170201000510940b2100700c050f5403209c464421680f0108440030b0f01c1c4d0850f84000030a132038542131280c5080303c00f0f003030001e40c1c0c0c2c04100c00c180410400c0c09129086600702a22842c4030184c164103441100e00c3e80500d42d013107050900b0381000e1003c04103a5904550040d00305009034030800c0f0070486643c2a6018880d00e10b0340905082c000b43c03c258855681000701c3e401220310349401d0900003902541d10b50310005607881011030f00410035900c40d400c1801003021894264100d561010040c080803655000b620800c915610210ac5003400c26182109103000a8903d4802c0942c804030903010b071409004032850540008082802403d10b52611310116400d91340d034880325242d0b4050481c1950024003c0c011102d8240801310225501816003405034050002c5c1030701c0d000b0794500f80310b041c0c500140b0619030a4820b01400312042c5d0000450080220f084500c0b407420310b103180c005807404007281c0250302041c2c1d000c21042624100e1908810540e52240d0441d4044490045116039981c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 558872949 1250 558871699 558871739
    0xa0203040b060418080705031204140c06031005090601021f150e10031203060b0a05030a0b010306080c0d03030906050906181b0d06181211010204031e050a061404020a 73
    0x9224030200d40480d175080042d0810510960036207207014400031110310b6007a000c0e2415109002c009110329040c0c2d004003e0100c5642c4180c0d111400c51030005240000504544580d60007140d00c2c2002a840b80e10900c100c403440f5480c40c004e01d4500350740946590040c5444000f2410095448801044689510145505c81c24981c0c0d084428141183d5a003503c0c0c20311044150241074440501168404000000d01004031440d80d41c1c0b5202c2c80c2070180c48080d01c4642000905052400206202a10380410032003101c01c82a104104d0381116450f04400916401401030304141c40c04080c00104180416154010054130500e0703000c80e510202102c0d141c0e1f441145081000c601e0005142c004c0c2040104502e06900802c000107450070701d04459049401e10b60703c1101c00303800c0e0303413011805603411260a03499482240000c40c10035065035206103c0e540c14004484450492254400400004110020040d0f50140f010f01c14482c03428424510100161401c80c820500300c20040b51001240b400624070306 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 558874199 1250 558872949 558872981
    0x405060f07140f01020304030318030914150705070611060f060f01050409020a030506100224100314010f05070c0b280c080a1a010801031e0b0a0203040b0604 69
    0x1124001909569034071070141160b1071208a0b210340404881405940c1e401c0410500240c0ea81ca00f518006044842d0640819070b444100100000465400780010302601d0007164840a41001000020a0703600c00b5801c00e0325903400041c0100c2005800310b04003003119210341303a807511750140c80e007403a4540c00c0440315041c503001c2d1100022100d24004202c0c1c040c1c0c4d0010704005160035203c00070007040e40c9c0890a4070000c00e071200c080c088503080065804200114610103405805028606185084400740c900a4400c1c010004202c0c00c0305138041e80e40096603c401c0d0703108040c1d5513030403084c003070132050b01c03034085403442d01b000640340070300588080b10302940c445444215170760b0325940312200c040000d01404107035911002202140e00c2c00c9c8070741003000c503098031210842d02d407881c03083e02680c128a00c081c0c441041050001c3e60f0340d80042039541502d80c4100b01059001092000f403800c0c1c804600c0c0a4070066000c1c0c144800003c06a0056004901881d040c11482e85c0740b000340810b807640c100d9036258103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 558875449 1250 558874199 558874207
    0x1f03050c1203160f0f022d090709030809030c030d0206010306230402040f0b0402131404090804050111010207050a0807060e010c1d01110a1109011d0c0c0c1306050f06040506 76
    0x943c0c040c11134860750f00c141c034038568615264010594180c900380000c0c0c01400d4000000010154501c01d1402000c0d00300da401100d80381000d4000d007844604d101c0100038030f40200c8c507016190360a1008114024014049a0103c2d0700804002c5d510b203002c0c4030941d03989282043c8038103c03c11000d5030703030000c4010f1591455140c449900717100003052200350700d8035100c0d0b452900c8003040d50303203000a00c2e11301c01c070040104d021402d190b100b250441c081c10134148030b585803004120020304a18161421600d00b42031a01400400b5100070303000e40704040005210340200c0b2840c500f04000302d0090040180961410018081841041e501b01c40140158501190380e40c510680d070440040c50741d030400c94040c0741001d006852000c600e40303002002841207a068004c4480d0701d05d142440e01c90a0b00601891401d02580b89118128807000344000d0641e154005002514825810003003104011452001c0c0400d400c140340039041e0750048c43d41d406a648030350b04c04070b00b40c011403400409980035500014142454 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 558876699 1250 558875449 558875453
    0x20307020117070c0b010305011d01051306090f30030209180a060302030111090315160f140a0e0a050d0b06060331021801031a1f03050c120316 63
    0x40b20400415040c02c00c03981401e12000a900000245e000718860030012551401d4100c1c00300c02808071140c1324a40380c0c5000c0800a610360301442918003660000c0b03001070110440e00382004d2690b42e8000103007085411140d1040c4180c40402d58944804106407441240303a10000110140c1c880d4213140d6a12818035450800c002e240240c4c07040c1c00000c181c100080740390752540441c2c25980c02c881e02d50090380e8007247c00041070409109450000064500384c11b09441c080360540c101800f65012403080201150618905900400b840300f400e401c2000c10680b07648030f00900502c58413010180e54010083c0d03441c000b449092044c005440954080381c4040165103074018855540c00c0100b031807048405644600c502d080071802c4908580d0041e2803d03100c14032082c01400000c000000c0d40507803001c604001080420f8107800c456924031044000211a0748680d030030109244108a450303003038100d022000200b000300000705039013034103002e0300c0115401d00445070701d035201d00074140600740e07944500341d40d000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 558877949 1250 558876699 558876737
    0x20709050c072f040f050f01060809030a05030402041806091a090c0d05010f24050619180f080c0315011401260a1a1e01033303120203070201 62
    0x1803001d000c4003c1c40403d6000d000014161141d01c2e0b81000e00542d1081801842d0040018407400f40c05c0d10308208115080080703600d0360fa803041200c040b08200b000f001040031075880380c0290b80c5039610704008076944842400c10030700401b20000202c030354440b03051100f6070003410040f90382d01ca000800081c02620f664035050101c82404a40200d07041e540c0c41c103410240380c005100b41540c1d89820080020490300a61080883e0101034205030301c284014441c82d0040d02d550450340c68100d1a13490508208103c6050701490391200b03030418485100303003001c0071802d00e00001c0c0c0d0001505048080b64180c611400001200354003c0c02102c41c1036071090b01c0c1481c1d5500031403410303103080300e001d5076004030390030954020040580a030341886207507481f6146601212104c0c6102c003c44441140c0c00c1c1c041c2d00d40f44a8603c081107500f01668103040d00d40c2c1440601d50810301d26442003400801481744003010f60513503000c2d00c3d01c040c0011a1960740c01d4108104081c07000068500450741030310f030128408a1950010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 558879199 1250 558877949 558878003
    0x1215030d09170a050d0905031b060306010f170c030601031a0d1112011104060e01020303100311030a050a080c060f090c13020910171b07061802060a020709050c07 71
    0x20b18854200c1c8100014802c002c20600458181d89220b6501d0910040500f46108141e600c10091546051450340d0758507401103940145090801c0c84901007030b1070b42a10b60080c00401100d5295100c0c0030400c0042145000710710540d0241c1c0d080120f6560010411013140e000c01c0c082d41c100e03803030070304110000f8000ca0480c1241c4800600d09100c070401d400c061402d49101c003008a8044c03c0200e0b003040181d40000b2410184042400a1815850004c2804c4c503101d55034800036207040c0c0c01448000345502e003800170540840c1c01c07030141d6215003d0b60900414541c420204035405110b0b18001800d0700d0700c1604694010402e0f4000b81a01050715800c000ca27003540d1031040d1201ca40c0c2007102c42c03043c2d90b0b414444203072062141c64064030004a5800350a2588000300059030410645445800509040302100c0c580c40d070003000058080c503004089403e098003440025044040040e6520700d1325000103800c412240c0c1004140916683c01e032002510340240000201030b01846031101c00d010764002c1601c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 558880449 1250 558879199 558879239
    0xf080c0c03030c180a0f140d05030a080601030219030510080a02030607080c040504050403020c100302040605040b07050106030204050c0d0608031e030702010905031603030e07080703080a090b1215030d09 89
    0x113111482d40d10f400042141032141d0058283c186000c8040100703050700d00340c4608041003283c4030004056141c446a440784503180e40c410810030200b000549030380c000d81c1590100c000043c02075902640c0204040d00403c42951010b624900b580c40c00100030030001510544150301901500c401e4036800070543e0302400142c40c0c0303034540900b4000803c06495500c1528807803402940104031b0040180c0c02c1c09020450402000c040500410042c0580e40d0820206e6040b9218020f81699030701282c02d08070f00400d00364200070351041c104420300c9801550300000e004041055541000006c1d9214102030b503d100e0a0641c511504034540c01ea294492000059a480582d500000c2404207207551140d04681c403000542680100c0d80b031540091591500c1065160300c11900200302c0942002d040954803080d80c0f01c002d00f502e10010b1000800382c400c0c030000703004080c800641034440900b441d90500d20701c0d0440b480d210480f1000c183d83ca552800290032003000c40e954942c98034082c01d1a14010000b10b80040ca = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 558881699 1250 558880449 558880477
    0x2010506042721171807052814130e071710050a020c011401050a05040905121602130212060f0a081c0801060f0207090b0d02030109030f080c0c03030c 66
    0x210388250518020400b2104220781d01c9010001350580ca54506034406001c00040b107441000e00e0311804400101102900c400b260308811404040080d0703a0140c043c00c0c414a0041d0100c000082c4040c1c901170740089102d001c8584070703229062a6800c200b11030100d146190158000750341000949001101100546200c0e07095807852090003000c0c8050310415600410101e80c0003481c0300b0755450038420521001070310104299030b94502000158641003e0062911941d6546500c0003008420401c0c040c851248219564031864101d004640c1000e4201050f405600420350580c3d421106200300c41c49094411030344a1a074a580041c03040c84d00507103070255086003c1a201003030400040007280b0740390310341d0300d85506c44060205000708107005c1071b40701c50140718960300c4a44420381c001c42c8180c04d840c0220400550002e1003800500075452155019405501c7d1030724020501d54019801e400141003600e400d0aa500c640144648038031412039010b090740c00a00129400d034014038001c00d10f00c08a058 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 558882949 1250 558881699 558881723
    0x71d010905071e0e0f04020414120f0703030503010f090203011809060209030318121504120201060302150712080709030f020a0e1003140102030402100c030207150f020105060427 78
    0x11016614503183c0708801003502c00d81603583c9840c156200c4070540000380c1e02507040a160100b01051007840b608410310a003004404074004e070004101f16644044003034101e401d07890f9030b1304002e40154428014a21240c13550300000c284021726000300d9040f913160300d4a50240c203a000581c40020000014111002502048800403d503410000f412045210300305200a0803005010800038006140c105070140c2c10044203582c031040409200340e4096001074446040030322904080380104403580000394007540214402e240b502e03000b005800103034414100d00d1614000b0710310070b90b004202103610800144e85004113100242d0540000b2207102c0c406400300c0c140c4c2d901c0301404050240102c40403941814841c5c41041440f8a00b0b038001416011500214a141000c0e00440c000030b9401894809101c50444000100340c420000d1600031b21680b4443c2e00040780483e0002c0894440d41421001582890003244040c42c0602c602c88d0000c0c021100e23030840d4007403c01d030441030010021081d40d0242c0400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 558884199 1250 558882949 558882977
    0x1140412020f0f07091b02060f0406060b030403030c021e0616091517072f0a050609011b05030f040b0702100603030215010b09090105060903101d071d01090507 70
    0x10043c800c6420350003608880341460030344400c440580301c221202c502c0b41c0071200d146c6500232640039005454841004041e544604208020b411a03a0240342c5014000081209042c0c0c03581c090f941aa98540c2a00c100240e00800d8140080581650a440742c00074800b15800081000e000410190345040264105d913a40001c4540c1a0031004054041401003011000c41c1444409103a03000985041c070100d001c8005450b25514859440034001401001e54840c00c0c035403040141c2190103a0140c1103400c18580b81260034003824440403c20b211300c0340082c5214840740600143d034828885c400d50040303280d5075620360050341c01c00500b001082d8001d498031440d000c0b40500800e03000e11b000350000d100a044010040c010b00740c050340940078a8801b84003a18031a5280104207044171800c9410f00c3d2254130340c00007c1c0c2401c0c0c014000c280841d00d01055200c0344000d00064400d1252840c080e07540150740c580048406941051a000d961140d000040c0004285075000c5600600c06241c80a4119005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 558885449 1250 558884199 558884203
    0x501030c1704080903160b19030e10090c0602150406091b0603060806011401051602060d02041e080312010303031e02070b0a0515060a050d18080403031101140412020f 73
    0x2034070b0035100c00344000341815013410104500907041e0035458001003210320b1300d1075051083c01200b0061401c607110502e2000201c0c40b0790020004001148240e41070100c202d0628001442c2c1d20a00315011030385004001505800403c50340c03180c01c13245109407001d0b61180d644100801002c1011031705850318012030301e0305c038901c203034520b002e400740e03440010720f403800c01c00745507d4000160b01c000c42442d1260784012850340d02038140c50f0b400000000b079081c0c4a45600c0019182d0090b1420300d284c482c07001c40d000584404600040320b0145098a51080e983d85540c849600c80c8070f0300a51a000b0707949440104002407082c0e00603074030441404040343d240154a0040030682c1d00c18201513510301548414003240d001c0a1003915007001540005a000c1c00d000b0010910500410b042c010034048040340910a00059401c0795030010001140d90211011501c0d00301000d400c60300003940002e007101c400d182108014071940720344007804c0001c0000d13955141c3d1070703414610496950030114001c55018440d00f03c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 558886699 1250 558885449 558885451
    0x4051c080f03040501051006090909030e031b120a02091803070501020f0306010224180307020a0806040c0b030f010312180807140105030c030a09080f07050604060f050603070501030c17 81
    0x52203020b5903905080c1040c40c20f54101402d400900c100c2c0c3c50341001b0494000741c0807002c0f01c2940a020542c846c15003070a403801d910301000c480e09406980d11403000545002c1d44131104080c1181c002c83c000c0d181c03040241d6140450380b0000d420202e42c001240219881c04000e50040c00c1c1c6504407458104c0e20380d507030740c2aa00b1440f00741c4600d0201105010140d03805008052104403034200180c1c8000302070a501daa400d00c00340000049800702441d0504074001030003115045a0007400d9100019910f01011b1351f00e103411641030b01c40d0011103030040381e00481c00c0c040b2409446804d000c4003107642980c07102004c0703980c03020030710003804406000780c0220503d980e44140100a4400603080c403603d0800758211701c0313929400441c108107003001048008829030702a00d0b0000000e9200080e5a040b03840c1c800f400b48209069102c4060006c58000100000040c403035119a215040c244242030b000f03500c00c0140c40064800076450f07000300c4014031032944240e00c01d050101e400d2400c1c030600c00181241018140f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 558887949 1250 558886699 558886717
    0x706020a050904050702010c020c100e030a050a21020705090a021b060610050c061f0b030108060121020d030e010e060403080414060307020d0c030c210f03050c04051c08 74
    0x501060b10841ea2406104241d4010260700091240f0060313510000d495104000603144508524040300220714424240d448a000c40a02103a485d2041c0307052980d60f405a18000b00c9149209515102d810b44100d40c0c58240704000e50010070fa201d041404005800b0350041540e509540c1c01c0c0b06800c90640d840200d16000440140603180c1c0e420000180b021102004017403a060101c10001d1902c0c1060004000c6e41c0081c200000d4903403a03582c1d050086003640700d503020f156014004000032440c0003010482074101e6a6111594000d110502d60401c0c8151820102030343c0400d4024010b40800e0003004244a4007074140761402c400f0507040005685500300360401d0741e02c04000f15050140810b030713810703401d103030322040f11018214941444d0082d07444007010b440104104400803400201401a80986a0958440710416259220b29244030720080d400300074100140c0001905030016009200e4140107400b8028002e2170941490103101042d082c1d0450b02d45465210504580400c0c00d036009091852 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 558889199 1250 558887949 558887957
    0x61212030509192003070f09020c0109020409030f082d0a110d060f0b030c03061005090301180312060612020c03130306090b0c12010501080903091002060718051309080706020a 77
    0x50048025103c3e20200f84c442d00d4041e61041609001740240348000d81d00702d60516401590b501c1002406501500c00300300029000703800c0c40b00600400d90404da003028102c1d000e5451003c80e80e907022007801c10600d603030302403000c914a0100c2800c0740c00321a41c0182c0d010107000c40c0031555100021031056280c1c0f0123587d8220f801c2d500c0784c2c14003ca00c10340038050000d281c1c03981340c1d50840c10401d05c5c05280c1c0c400542003078852441a800300242d540990140c130900786c0014001c100d9695401e1a41e503031001600d80c210006044000c03011002c801d203200740800d40701d071591500342c2c0c5440011064025480074400386807512050088d50140414051181c0c0914443c000104038030045150004007000054101e070005541880203200d802c0e01080d101d030441d071007407820008540300d450144d81188a02855140c114090548600340d15400140c068000c80c0965100c202d02c400c1e1064410030001700c0e010721075009034122104d031450390440c0c00990b40c0c14000d0303800305d107040c40c1603a40d04202c1e0300c480c481501213 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 558890449 1250 558889199 558889223
    0x1d10020c010c08060f061e04140112150e060a030b04050705030712030509040903110303280b03062a0d0506100302070f032f1006121203050919 63
    0x80c182802200707001e40d0581441202c0d410000005410b201c88800040d004603000705001d2200b981081c032102d5030106800710300750340c2c0d52240100e42420348103c540c60301192541c07089010400345882036503030354503403696440045424000071641c8100080c20341030340520382d03400210100c0c900c0104c150042d4031071001450058500800d050400e003a45c0d00151854100c2802e40c000700390480201c03030070306c501100d00251000c082d2409a0303240c0e101d85548680d901c8040704004591074802070100c056214400f54100008201d1203010503940140c2c01550103400c0040859507c5d0340001044104500e000040a900800300100001c26085102542030940e01d8005000c0181491600b04004000c5498150710f0807400d40c44d080c070400b0781d05000804000c4480c0c03d9480c0b141145600341c00700240d000c0503007101150704c41e00541d01c0130f002c00128240c03450a0000109a038070120401210380d0300c141640850b81c003d650075401481d00400c0040341d401100c04081075040480a407655252185c3c1000c000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 558891699 1250 558890449 558890467
    0x20a0503040b06060a120b010318030f030b120712020d1e2a0e04020a030b0109020703140406091e1a04060f0801060801050d03021006060e10080411041d1002 69
    0x202c040c028000a0050001308400a00250720545040301c0729003c3c0e0012070a51004c000403401000130881a84444d15030b038a4003002c059100c244212400990355061210950080801c5621601d11f618403a580e4070100040214410301141d104c0010f00090030b6082030981c0743c031f40c10056000700c0815403010f821500d4250070042c0602100c60044500001107207011401e684210040042d8006c01c0c05818030680018115078440040d8005554010500c04103075944500e02400303500070120880c08652007240b8444107005807019036084a040d5591020f40c145030803800050f440c01031441d002880c40030030000c00c00c40c0d01c10000c041d50031184c0300308035030301c86c80c01e0002006080316541c1c2d8010018010010400f407940040e030301e415903e040b500ca00e410041860180c1ca080650042c440f0300e5810084005a5030703400a1604250b1102610b11616545849004480105003160001c0200b80c130603805403500d0829034001c0541a654041200140e41b0342e4041031300d06080c22610481140c0c0024140103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 558892949 1250 558891699 558891713
    0x90e100807060c030c0201081302040905030d06080a02030d030b010c06020a0504090c0809150c070b1906080a0c060305060d05060a0c09080c030c0904051501171212040209040302010e01020a050304 86
    0x700030b000790300d0180c56001c81c56038002d00c00000d905020781088441c10225105958400e80041080e0340280704005180d002d00d0669182c1c1c0103050220012881c20b0800150104049840410190700030050103a8040c0c0b5602070f001464038100880c108000d50484600050052000301a82403c648603580c80e03503d400e0846007647e50850140040020300c3c03041c840c80b1000083ca1244850f8001c60710101c070703996006412028000c103680035243c50200c90a2111241700c0d0001e40f01900710500007031010940b03400c0310076514040d00d01c00800c0c602e1811010080b280c440c0e40070310703003040700100740211900380364039003070b01c0d00600b616056a041e99481045803984e40003051034004200c1c1d44050090380ea000c038006030321004400c11940c01800e8100010702040000d00c1031a07a10501c2082780780b11561200d501c0000e4140704482c8031000d203d0044046401000034043c0e491001c141e41e84207030599126824404040c101800031001d564803030156001c42c200a00203800340803240d6a03242d88914081c18404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 558894199 1250 558892949 558892963
    0x50907090207050a060b120307110a080601030b010618230a2709060905060c070c0f180c0908190606050d052a03060c1b0c01050910090e1008 62
    0x3040d500e2040000c940010408511103070055004980020412080b41c0840c2001d00c40d1052102140000100002081080ca03080403c0c004150740300b00301d054450b0203043e602c90b82030001802c40350115004000c0c3d58460a8240c0003611200030881ca6035544803c1e82000192030080040003207a400300c100c0c040d042c07000054008040b50b02020f6610075040d5075a021500c0c14507184540b0305c1e12120400c090000c140c000c3d0800a62000071140741e80713810300341800d00b50440d9000b2210105085030002301400e10503240401d481ca5940001d0185881401d40b100405101594006000d14002d0004201c041846640346a450021001304442d800b481c0c207208488454120500c220f00d15003108003c2400041c41e1303c21400400c030001025400c8850700008000c0303408100f1703407512400d01000303d094481d001070241a48500580070902c1e61303071419643c0b6603240c0301c1c4240c00280c0511403c840c51524942142c009001810910030607901c80340c3c0c001600300100c503002c40c00b150300341040001500c01c002c42 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 558895449 1250 558894199 558894209
    0x90603010f061b1518050f030a021b1509012001060504060e01140405091c1d09040201020d080c0d110a0806030706080c090616060501051009080a06050a060513050907 73
    0x846008800355413264018102c41e1008014142c0d584c241e800c1600c003182108001540000031180745030b00100c82140d880d07000d00c440c0c0e0b00500960001d01c03210600d4040002c5070841c014a070044600d100c0700c6507101c50708a4481d850401c007060007104221342c8540b5181d091003030b9034000810640c0c200818001565207903480720034410740301001009184000701446078440412100800c0030b440d41c203000ca10300032090312001080320560014034015170b00103205545000b400342410300045502c0041203a1b802084034041d015811289403000c0562290010701c0d80b00c042e101c1c045003806092842402160407030a00310b003180400152410445801801260380501d0440c000c3c0045d0307040440c01001e6840146c40788000c000045406074403542c420065800f84250340c103001804500909080c0060b02080c4a00c40c0100ca509200d10102ca105805103030a0b42c82c0f1a00a00088100b030307407038034010180140407000ca16504c3c0b0020410b566100d02005516800d800c020905007054032009081402c16405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 558896699 1250 558895449 558895487
    0xf0f0b0f16020d122709090203030f0c070608060904030f080408042102090f010b0f0913052805090d2601030506070e032a031011120606210c090603010f06 68
    0x402d0118041703a51001c41512a0b610011541484600c04646107000d101c028801001011820252040300000c540088440541d00c440c410785460050000c01a405c0c0c0300500000d001443c2402c40a01802c085a0401d200b000110701c0d0560700c81c6c14084191030613000c0f184a1040300c0c01075055280c11050550412101c08940d8029490580e83c1d00301307440f80000030b500701040420000050b96403080c0c101c0d9006c8034200184120702d0644040d540d9007120282541003551502034102418607a0b200d160712484409000b828040f21252050329140d10000c4c002c2180740c3d0410410341814886603109000714402c0004009504040c0300c050a00a480c640c2c0c21b0080d48200e211a49071000544c0d00200142c10048180c00b01120501080c2482d0200c548021054100308810b008004004020010548070340740c805c00c0344d00d0b15420808544218121482c80340070801000707000d070202200035070300207828a034818074200c099000300d4150b4000740d01020489500c51001c100a64205000c443c041c062101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 558897949 1250 558896699 558896747
    0x1090e06100f0522110415030506091311040906051009090c12060b0405090c010f0201090209150a080604031d180f09030c03040e010f0f0b0f16020d12 66
    0x801e007040345126461084041c0c81c00132164000124055103580c1091205000d500c20031510701c0c07a00d62003403285c28100b40700800c0c1c651485129200d84c0380902d000918440480d214035201c620000d170209002d68400b0380340e90079055641e4030b901c01c14220714821040400c1514003240340b02c1c2c40807205d6220781503141c2030012160000d014000d40100340c4082c5258005242124246a401040e11100c000d80281ca080300340700c007403080081c2e64001a00240e8540c56940143c6100328203175440302d00d000307410240e8107020402d040050080303d164164007904a03d009075a5249407842c3c007400356002d070042000303440c0e05201d5003000c0b01d038420344541c251048200901c01d644000b00280d001040301820381016400705081400500884400950520417252070b0794480045c0368100800b840392001c0d1004807500003603034100c03170243c402c2192410001c250404c00c150185c1ea29642c04002280030758a1504884001a0384a48905075840d0142101c0c1500500d20f0070098541034507145400020050b402d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 558899199 1250 558897949 558897959
    0x412140a09031b1508010305011a01080103080706090f0f020406150507410c040519020c030417010507020d05030610030b1302070b0a0f06050901060509010903080301090e0610 77
    0x280c1e20044a03448203070200c040d1214003229401c481c0d2030700102e0380b02501c9220341c0d00c0030354091080350607240244020452420b01c02104103600c0c0c0c510500c2030100d409100100045408c19020300540381c007501006c43d81e64815512001c1a41034000200c0301c01514454010550409200d020003030140506070885040381ca480c0500180143c02c2c0090007421002501200b04402d038108800c0100000601d04901600c44001701d01c80c00d0b0503103650b000d84240c02c080d403507601e0b080c09114080c18100e088840322046900721000607510004644c0003a1000300000912140c4404c001c43c0d4218200c1c3c00001e046c03c0031031009050004038040481040410703c180101540e07500e03540d00c800ca01c0d5040001d1039102d0a0003140740004820004031f070451002c18000d05019050002520916078075604001d603955542a0308100c172024040c1e141c212884a006020b03240c081c03001000340800c141441e80c046640c99994103c03507482600100d03034664885082c406440360810605030412407183c42d02c5074030750400c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 558900449 1250 558899199 558899207
    0x207240c03020a0e1917151510140405030715110c060306132004030308071106010e07210e07060504080307060b061b0c011103031006120b090412140a 66
    0x80032014811005c2d503a48411401c02d0a8050004000840740b100305562080c5800b071701c401002030042c50050148002403410303c0174491020030040c000b0100012100041da0454800c812840f0014410200b0000480c05030b504028040c010005161803802101c0070000007000c0f020340170182002c80d030024800c5641540c1c1d03d4281ca5000000b51005000300e45045241c00c050600d00034141d0340c03d4004040d114071101500f00800a4a00946548459032194082103c45c0714610302010350b10381101b8010302c506060603440300d030004010300d00011340c15908a50046500b1300002d00d07201450351400e0380081120b0a00400307005203071509007a401d0900d48161140c90b0b200d92440141101e1f03442d004102c0130303581e8500f5109c03c1ca414502502d0607054031818595129011440302d400314810100440d104840001200c3c80364803c0c0084100051404030709540484480c80c0c5540301e00d031540e00c469550744686185500c9140200e42844000c01d1803000644031100110040220113000c0055800e91508 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 558901699 1250 558900449 558900467
    0xb1c090c06300f021e070b07080103030509040f060824010f030302031806070c0306020a1416140c10180501050c03040e1f12050c03010527010207240c03020a 69
    0x2d200302044034160941e00400078401d0907a0010840484503032580c140310110007521607a817050000450540320319500323a03800f0109201c0100064030421100300c19003420b4010010070071b14040c0c0172801d2901c400b9840e050558070340340010998407001601c441151000380040c0140b010011000340503095032002507c030300c81c51029400800344940003008030340f5040d04440d450382c0c11840c0b680c1c0c1a6201d00c2d2100282d8032164440c0c0c002024950203500040120b81100e0007143c1c1c030211203489007425510204044400c0800500070701030580d0052040d281c403050401d11042a994000c17030b1050b14400c03054100d2040c1c00580c1041004c3c8018851360754000b00300d0341a102c05102503170f0b191b0388440480b80903040030070b14890390a210b120009016812801c0445074548940b00355000c401202d81814200c86040b034001d0441c90000d6105d680d102400d40d41c51095501c201e00162411103e912000f40300c07821484542c40501d061030b540701c0d104d1582e100f5081e00002e40d280640c941821034400411400c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 558902949 1250 558901699 558901787
    0x150b10050711040504031101050601090b042c0903040504060e06030622051506090f190b04020f040609080d080421110609030417160b1c090c06 63
    0xc00644581401420701640b112154010401c0c009880d041c5801042942101181e42c6150b0034800806c1842d8003e0601009a501d6100441e0820b880c000035210500001c110b0036140102941c0c000e00b504c03600130401e900c2810300704003c42c3e032a882d04081c0000c481e01a403100c045140c140060240b83c0c0e8010482a0b00211598400c41c03c00c2500c2d0440c1c480742003807540060140c440c00082c0060b40220104e1540b0610080760303801c0c469501e480c0211901002182c008038590b128401c001070b04c1c0c040d03a201350302081001d0310050800b43c40c0159000035078081c0e0860f01c003040060400304140390040021076401525031a1481031800c0c07507540e003580000c91044c0d550303a03271440031443c950492284c0c8500c150106548101e07102c900b42907801607280d034042d00400004032110b03201c0c1100c02000084101a04840318200850145003180e01c080c00d402420908043e5203481c00e44060500250080d912410f004000c00710f2000d00d0200050201d088003010307050769000b120074000100d0004a610341d0510 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 558904199 1250 558902949 558902957
    0x151d0a0503090111120301080a060513170c0c040f05060901050618010f0e101206090603050c040b0f0306090c010e09041a0c0f04060309110102030c10020c03040308040909150b10 78
    0x600d6005920741080b07102d00800b1017545010000081444000610b08062130061504008a80303907804000b0400d5500c5001403c80201c0c8404a191250240e0007800f28000280036207111a00c0100080c01780c071504030310640d1040d10354042c4910761910040f940e005240c00ca92040c600741d240f03211400002a00070b14141400b6482041d07420550088034000d0714020024202150352000c4400603024950b0414100710440c50403c02103810720313042c801e11050700d030040028080e03040070b00c08110181c640041e41035000301e05000816001c0c1c40411065000d24038a07800703403001c1070703140c0700040c50340c14041d00b00da108408180a00001c5014a01c08414240b03981c080c1b503401c0e0b40c07079806212461040f0284402e400100050002c1c00550603446804060b201e010682c5290200343c004a80c0ca01842902d20442e82080b0440c000c00e2005034004e080304108031050783e09141d030f40e0304c0341400ba0b046544401c1d00c160b00d03441c41d9010032000c1886024100c1c80304008209a80d132482c085082411881420b030248 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 558905449 1250 558904199 558904217
    0x715090201210207150219020d050409020f070c03121205040804060815060a0905240a050705070312030b0909060c0a0c230a03140c030702040216151d0a05030901 71
    0x30b80180c1d01184c1440744c2204031200424040c00d030810085d4002205540c9030300c5050212604544045141070b600245a5038090400d800d01025100075070259004010500003080400c001840d58481d0360300650081007411000d08912a000d01300c001c491140720a050b190904100002d00c05800fa9006d4a616113021032803580d5522402c40d07074207000d62100e68054808660030411650040342c3c403050325801e960101c0c88030b0700c02140f4001c1e04484e40048172611014881361400d42c2c0300d040034011a6008801710381006035640c1312201ca180341000200e0010703440f03400c1e0f0111410b224a40c00d03044907801c8014030207445c0108002d005c0d4041ca4002c40100300c01c11002c00240545115000c01904404a0851999010080d156130341c1c1c0f111542100030070b111907914550001781006540d00028a00c01851030840242e0800000b540314440f000c508811014141c0e001c80c40c241401680035004d100700240703642100700c8042c00e6240e1950920902c0e03101c174174120f00140d4044151081202d0a090141003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 558906699 1250 558905449 558905507
    0x50d060504051501140102240604050c16061a010c11010f090b2a030c060c2a01090302160506091e060a0c020f041a0d031e050715090201 60
    0x1481c4807a03c140c0c5100203284004145000d6840c0305401c84070003602180c0d841d0803000c030740f200260180c4c3c0684620360560b00004020b8141901304603130154036a1a400d15041e034621080f410f6041340c0c030003510029a64803145020725804030715002161001d00b41003100a0095451101d2640650500c504001000204600c0030b80102845005003140940c15a00d80020380390301017803c00f140702d2248004c0c40309a0303041e02c4008040221400d40e1000b401810856444892100465020304140b0020000c40d098119240a521444a221040c400d0000c21014840e0034002d2030690401d070a000030804c82d076400c1080f5a141c01c219540000706450007030482919012604412413515099134102d5000200004210b03440603114502c203208075481081558240d06000c100c07445a04010b030706400b220620705291401c1c1d189841c200340320b840c2400b0907504400640354120110761006020076070204008080110b030212881540d1300c0e0600400c400d070941d0300020042240c000140751407000b519141c1c24 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 558907949 1250 558906699 558906703
    0x6050904021f0509040f09050d1e1409040207030c05060f15040b0607051501061704030c06020c21070b2401110708030304080301031209080d11011409010204030c0b04050d06050405 79
    0x108460001d1081002e64010b20301d02c000361087c007004482a0080104401100c2c1c011310b10000c1c0e0186400040d0714070500c0d1002900c2c600c039038a403101d036910010b000a02c0c2903074540c00202051486541d0b14041005907141c95841e00c04d024040d00007400d0381c44100688402500c500800d81101254082000350150020800c2c81c072070350390098540e000c5d042800d50201c59801002e4101d40c840c0c0c0d42e05a4240040641c0c6140c0003050360024000b4000c4038032000842c50070303000b0380742c40040d90054940e081c505000c0300c44d440e814503111031030741c0b0700110b0303030206000c180c0340c440ea405100c42c005070261060000710300c005407a00700704040c14000c210802401c04179081040e400905100d10484e50b89003001d04011a40380c2003440201d9030101803000001200b0b02c10340e285811901c0a40003044001e0312607500b580c40501e541c000305803644d070703030113400ca4a00b0950305000d000380200750006940310b0071030a002030b0148854001031103419040000b00b02a40390341186891032034201a00284c03544652174024 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 558909199 1250 558907949 558907957
    0x20c04110c06010e1614090402091305181603050d180803040801060f1e05012303010b0d050f0118110412140f010911060304030c050607030207030306050904021f05 72
    0x342910402c000820403851521800e0300906141801c140041c564030411940e494505442043c01c00c0140300a0600b814160058000c1003001002d808002c0191801038003203074401c9900b0b88071030011130320b0b420440700144001d034a105008842c11040c1c41c2162900396031500400781034020801c0c440c1e062003020409010480207400760b1001e0381e50707135030382c8462140c041e10850003800301c00b607000d075000103008808881d42c010404000d450a11001d252a0040d98040018801c01c9000c16405918181003903a010045019140001005d6140d8054000705012102c0003001c1500c48840d000c014003649074000f42c0c03007068400701e10020a54200006146d0030030301a80e130080d43c04003001f03a1081e0400c044042140070095101c41160001c207003001c4200c0c01c1e03c0700701e0006401c03205c0b202055003450602c0f030021507003d8040e0602d21901c41e416541c0c40d2402000b1980400065404103145040552500238800113110450703001d0b20a0905400003001c481001c0300c001807441e09440c44202040c050380543d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 558910449 1250 558909199 558909217
    0x50d20060a111501081b06090d0b010e010504142202040603080a080f06060a0c020420030a0606051e0a0c02150a12020f04360204051c03020c0411 64
    0x503a031600c4121801601c9094044036199a0b0301a15000b44100340819200300e040740c1110b40180124031080d80029a1501c9000f16a90020703403c210f1154103440f40b020080302c043c41400d5000042d0b140c180102c800b0441a000300744501d050829200d10b0a1031822541d4121205040c0a0b003400d56621321941404018100250018240a000070a200309400641000d002e0340d110100c90341c2d10008180f40503c412502503134055014465250014443c3c1810044030344041c00000f402c0c1001503c00008200c0c001000c42481c100008020409445015580003051203040042c20502000041c48500c0e00118002c0e04800003c0f66440d241ca03c9654143d80c01500078086100400700181038510b00d501c08000c010200e44402160081c2c0d00c024402c9075101c10701d0120031400c10b0f080103407800e50208080d001c03030820040e080818142c961903100d000388004051100503900d030300c0c0009105004105089079405080309506410202e500800d0b0100f6102080710000741941754040081101c1c060302c558 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 558911699 1250 558910449 558910459
    0x1050108011112150405190506030106081b060720030d030203010503120c03130b030a0c1106041b081204050a1e031103070317030108120c0312070909021201030606050109050d20 78
    0x40c40340d01f800b0a0000c07403641c0c0c280c0c4000d010303d558800c2814269003092241c40d20039840085000030200b1030149080d11000e00404083c50318007140c940c1911095091a4081c60507844205141580707020054084c001c00f040c1000e6045616010000c1d88484a01004082055000400140d500010700803651444220b0490a440315202d6585007680c0d08201c8151202915044019102078000c8242c01c1480c0090401044541d482d0740d1982880c076000080b0400781d0503240e1002c80c1048040c400300780c0d00030325041c0d050307100da25140070001c8803011036102148100c4a51101d222184075000500150790300039420030302a1001e100071a20f8242d060340040d0040c0e55403001811a0050840210b048800380002c685456441740700c52101031050380548103c5a20400c210b403602e054042541c0d50100ca60704225101c1541c50318075109070f90110b40c9242c10700d10a10014010020f95204003030207400203182100e80f1341d040c02d02040328030b11407a8000e807514071015100c0c4821704842c51200c20425020349 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 558912949 1250 558911699 558911701
    0x504020a091404110d2301140103050709060e0f130f02040e0108070e070f02070338060604140f040204080304210b071107031b050301050108011112150405 68
    0x400601d504580c0c01000410028081c030290140f03003a00a00700c0c00850700c1d60326864000508003200041204842d412070000d600001c45680c0040000128004c3c0304500201d824114040001030854200504210074400880300c1404100d0f0701a181c0e001550060b10002c1105112200240c0c02c0794042d0050160b0342d0030001200c80714125a00600704075021115550307100d03601c0d019090344591060203039845900c4441c000480143c032810858a4620f503c0c01980d0f0b00c0c03512510345400c0d086500c00c110305441c0301c00b55104800c0d1080700b80c40100e4206d103c8a00d07054101600040d560344118844d2808070412800c041e5019910750150100d44613000b40b086584a66421410b03440340c00501c994004482800441d010100d54800013581d0a40d00c03912001039990785440503200b800c0303900241412485002d00c08400580c2e0240b03004a0152814000f071300d00d030b240908040c02d60b201604041c0d52a414500079850548001c6c040d0342940d44140d075240101d60b120000c601001c48086042e81d80a03081c54 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 558914199 1250 558912949 558912967
    0x60d0f080f04090f050c0304200306070e091501091503020903030711031005070e0907031404060509010e030403050d050c031608070c05010509130b01020a06090b1f0315090804050402 80
    0x1d0014001c485101d60203001c041469030801040b65130440302100007885c1000000d000441d40300b05c00401d111420b0601c043d0441800c086407402201304c4000000c9039101104802518061082c160b01803801980d00c5002d0400700002080e8210600c2900e14245107500402c0b4018000c5c0c0585820380c1000d030441c2d888094604090641c0c07818030607500d00034000c0e24420a0900c2c0a401038500c140c00503107480814106900c244134600d03d000b80100109603a510400407801c040781d1009000300d00030b40005c910703802c0240f0102d003101c410804000003640708100c01c10004001040c000c0b80f24516040654171400990002400e51141108411300d10704d1107480c05007080883c41c0504212801681c003c411191100c00541725485081c042d240c0c44540e515039070040090300c3d0881c0890725010b1050702d0b4090742607901c440903107140400880f0b402201d601013205e1040c214240c030104100804107804a10328584654040d207010881c2000c1503500d564504060108240c121402400041c03c219a241c03621 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 558915449 1250 558914199 558914227
    0x204020918100e1e0103020d0f0b07030f0e0d020a081b0d1e3b040207050a060c1b0b06012c0406060306060504050607150c08090d17060d0f08 62
    0xd020350314000c03c4501c04a080c2541d81400e10101c1420041c401246900f9902005049054070b041141c0403544100540001071031200018090907958a001c03800400301d80f84402511066003440ea116400762401c1c84003d940018100c0005402a03041c60361214440e03000790b150000c03e80c1c0ca10482c440d140002d54800da1142d4506592040020403240c403400c090021100d1b5880d0550001080a1000441200c0c00f1545040e007052038a0110a5a90041880105007a03030451202525541c000c450040d00380032072030245100302061032a1809241c2c13030301240b05040b405074103409040f10f211000020700c00e03400740184200a00b4001c0740c800100b0071080c8041140c0500c0c018080c000c9091a800081d001d00034040c40065885685a1600380b40c10003082c030500f81c0010703a058498684502031b880c0c00e40d0181c0300310881d101499850f43e50702d00d001d00d1300919003000f5903031400810083ca020074207182054418141c11200480c0d211702c02034560f090840100041b0b41e0042e00150340080d04129101031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 558916699 1250 558915449 558915481
    0xd050f010b030601031a091e0a0204051b1b07120c06030c170a1812020c010206011703070b07170702060603071a16020105070b0a090b1807030204020918 67
    0x25100007407205050280602d03440750400c0c88000c0c00b041c442060b05600360011201d06a100386040110380ca411900048003d014280702c542e6005a0401084003055080c0342c0121603120501035102081040b240051403210b100c0c1110b4081d41c0c41d00041c003101c001c98240420301c000e01d50384907140e00e1141c9500705440c040d0701620070384020900d040c3c106004d0740d0040c0c10410007115460580015556a2213040d805480801c04000c1580c0481008500041089000c0610610b03e81c2c02081c902d1903072070000e440c189040e00000c5094008001040e01d61900200702e0f525154002c003040466280c003030b4284c4d0500016008207003003034003034010040c040da070010320148030703040407012100e901b995002c1380388400244280c44040060200700a02041c1d810034500603610344103150840c606100b0351070390081480300b981c0c12455151142071120600c20b00070410741e044219004200301032140340c4403040ea5880d00c0e102c0240507607004151000266902c400780a01c401884000c0e079507a252403040b2861040e5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 558917949 1250 558916699 558916723
    0xc15050a060e070c030e041409070e09030f04090209012c0405011403060117190606050a0504140601032d0e01050903090d0f05070b0c0d140c07090b040b0d05 69
    0x7160034400260ba0485110140c050400381c0c9600707418003d103403421281d015113500c895801c5030300c46840f440000c0c407003081a44500710b0701c0040d01015051210328901d00101510881c95980140f1a88518a02403021142200c00c40c4800581e92401d03000180c607010201e076005200741480f0703095111b02c102098a4200d001104032801c00440c0e89545442019000b6080081d806600003c014054902c0c0d41c003040881070189011503c070303510b0a02000c0002101c14804807242902c0e20400c10031428800b9011014000031a814001100c0c1c192007001c12103001007903181003545034004410242102d04001008e17114042e880e4840d032507405400c1010f8005540100c8840d0300e03020024410070004010348030003010003005010300158039115030440354400081943d00f401520310000c1d201d111000200184150080174000d10004108040c0c140d0b114107514442c445001c1242002003c004502042502c2080c3c0000030b45d290044003041c010003154613003d03003003010b001c582010320a00040580c2081 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 558919199 1250 558917949 558917951
    0x70503151507060b1c0605040204090204050412090e010e1f03060f0903170c09101e0905120d02071502030f040e060a12030c02010503092109010f0206010e04030c02010c15050a 77
    0x24000030180b040075034072110f4051844034140c9501c2e000450b5a001f45e074002c0c2c00204040340b500107a80014048600c10384040310149103019607080c0725078000540e1801800030543c5907220398503040365500c89113402025801e50100030018a81d017a45600e49040182d03411503010841e080780034043d01d000b8584850103901182d0290414948401c030141510b00c21005030b90103500340240241480801ea1200d41c0240601012150300000411180e284442174285c0303135202d070069481c00040c099804204120766a481d0401825800c5603900024582c040301c201141e1200c601041c848100c0c00c41c00368090403907103c00c2c0050001008181010050b0141c0800c0781c00c0a001d42e07903200c10b200150310150000b13000c1881400500b001d50b0241c0040c542c0010501c09860740020242460300882c4999a106112840c3c0070402c0b10055030b00000f19003c0c0c840d6800140440e5047c500d0040d40d9003401040102040025502c5c1011a445820900d806a0f400380d01611030141d4105482c0c00760a08581c084403075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 558920449 1250 558919199 558919211
    0xa12090f080c09041e23031218070302120705100f08070f0e0d050a030e0402070b010b0d020421330b040608030409091109010e07050315150706 63
    0xa0815212110031030300107000078880815000c080c010301100c01401602c401c014031514813207140801c00c400800c130f4407800b2190100c0002c1c4100101c082c07541c01120f4440d0740b0070702100c0900582070b142540c2104041028400e401d0564a4907460900e407900000d4210841ca902c01d0340c0e124002030000146c810495035030f08100d50b802c108444101d035050f05c800000d100c0d0b00110b1500d500801402418020320325007210a05403540103c0d101c003010ba01c08030780c280d115104940038136502000940d10004203d40039461301c011a1500b00303082506005081c0381d0340d0006804c440030030039503040390000d10b031010030000742c00440303036103100e0200441005844486030b11103220301c52a00c94080640c45001d08039058800452880c0d0500140640342ea000e400954074000400d00004c10005403004220b40c88021500c2602c0749458022140d58000d450300901d42c02c00140a907200702d6000981c8006103182043e00d036034034551000c0340703140b84030726a5402803402c00c0794109955042000f000b00d207010344024401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 558921699 1250 558920449 558920459
    0xb030124050f100906142107180f0e060d140601030309090213090504032109140102040609120602070218090d0e060301050d0c08030f091206070c150e0a1209 69
    0x704039030f100c83c4107001031000c010600c01c40e80620780c036080c04881403404074207041c2c501140c401c15100d11510210903298179030070480d01075485691600c22010246000c5042807504071812903090640c024540321079590000a403294a40d40407441d1040e4010740d10090000c0b003c2d10298075801c080c0401d400007084664046911070b0340f03000311001e081c40c1e0788158034002c0c0740803c074200914000d0030840030030002d420301c940c0c2000b22104c0044c140c20314610008003421180350900541903c665490380c545d0050004110f615006080c2e201194030b1600c2d421095101498224000d12038001e00030343c4001c1c0b48041d000d0110a00c24030398481d2134410100c9902100c03040096410140960180e503022100b00014841c50800401c5000f00f240705491000d103031615541c7d202d045810513182d02d072085002240300485031402c90700c0c0190a001e500080d05003400c2582c0001d1040358407000282a0105e284800348001560380d0044c0c2000383c8010660b561603825141040482040403003030780000352803005c0803039 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 558922949 1250 558921699 558921709
    0x117100b030303060904030c0204090303020322050303060d2109090f090c050f0103110d05070207050105070c120c120b06040b031f0914070b07170f0306040b030124050f 74
    0xd03200c00500441c115a900010403261002c010000c0f820411400d0030030005850394001d14180c28801e480c0540c43e4580007c2c005a000340c070170b6000c100b0340303058540040410743c003000300c1c1d400c10341c180c032130501261060903e4030284883c085082c01d0241514040410507034803400d0307403007070740c2880005004105180040c0320603203190040240004106000c204140e2402c2802e01026070010b04000c42d11500301210021b041e0040108414000e0b1030310100320103198140031080141209082c85420414542c071000f011201c2801941d800c905d07454521028000d40c03417030080060014882141501c03a007031a04a2244000352995030149081a040b00c01c0e03894040741114a200701b00c00f002c80c400c0a05414000a080340c400240d40b2100002d11042c1010340c2840003e000d4840080d100d075840d03843d8074105240c1c5085109505103103109010601c80c0040d80000c032900400c04503808139850307a03d507001034018081d200742d40b48010001e000002810303209580310b2044510880341e01c0c58020310b07081445 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 558924199 1250 558922949 558922961
    0x303040e011e0b0d0b130204060905091e0708070509040606170f01060f0e0409020a08030403050f0d0c080a0e0310140c0304020319170a2f0d210203011710 68
    0x4039043c000340107880034102c40b40d02520f0340d40c000500c000c5640d208003a104d8101e0b40107401600c00103580c00c9007400346007441d0710b60725085200c200341442418007480d0010380820003e459041003280362008241114401e106660449800070b000300030140c3c0e070f10009020207181d100d400d10400c0c4402c001a00000070040b645040710941d80300c0a11074240f454003100d20a0032100350650042da2070382040f01503103407098107a0240c4a6007004642c1c490860510928007203440f41c4211a95000251030200c4951020140007076640c028401070300c0c0d088405040c1c50f500c188900075600b510a00b500300c0b0801038107400c640c00c0009070035004030082d11515181092440700b120040d4050340804180344240d51000104c0c16505d024880141000440d00c40000c2940c2c4180c50400004006405180c8078400d00e402040d42140d4520784c100300030402c409803907102c41458411805010240c40841d506d8410341c4004912a00a00d03000c650340d41c0c44441c089000c8000d00c81404552044a03115082c1c60a03500c118 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 558925449 1250 558924199 558924209
    0x627180c0c150f02040902070605040b0903280507060e03180103020f0714030c010e0102090a0602151b12041202061608010905060409021002010914120f0c0a020303040e011e 76
    0x60340040c42215501d8014129518110f640540c0c00c000000d1020305902c0540a51403142d20040f606040c9400d0296520300301a0801c885a0403c01039964081801030b012401e410302600242241c190342042620705006004010340454205081e4001482005c00100048a5485c000c0c141c1030051500440c124098241c074160b83c1d407401c00c1540e000c80c07020901c2c020303001c5004044074509010761b0300d0030b420b540900340d210045a4011460034890714000c9840006041d40344002c0103040f0070b00741c1d2002c0620003d4a136241c00c0611501b0008201a480100d134150b05000c10b0304060b40c02d0030719202619480041c034090041c0100707c00700e507410f0301c0c0c404241d00301c036041e6448a825074240000c9500828025141aa00035070301d500c06001a211307007034108610b030156000040d03100894180460344010101c0140d8951700b0aa2000904403501403d850f5070800032102c3e5510307607455680003841c02c4083c2001a61521001c50001581c1c1100100d41d4141c81030b801e03889425103d841030100002c0518011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 558926699 1250 558925449 558925463
    0x50a08060909070317041d060f0d02012007080d030c080103110a03060501090b030f073c1509050607020d0807150203010b07050106140a0627180c0c 65
    0x403898500d400715007075030041c001000380c800c0555640c0e41c2c040202d4086220000121011030b0410156903480840202c40007200d11a0f08603180c0940010200c1d8000c403420792040110400c00010341e4841e00b00c02c1202ea021030110f43c900078038000c84582d1002a4410381c0c803544a0144100082c91080c00b91401032036042d00e4070f800503406c550750b48111202641c580f85d0440c0070302e40c00001095460003130500174070064030000ba00740c0d42e14050606254507520710b03105580c0599010002c0025079880301e030000c64085495101207100b0001c0003402c03508104201404c1c440310030702103540010a031465908141540356144403540d19818040c45018045000c0c0d8000381c22804c039008140414001e0100341c0c800c0c0ca6006008120b454500d00300d82081c0c01c41c511801021034980f003000001d01c00c680142c1004044d144207a104880081c4203040c860160108221040c0e4460b09020040d2141509007812841c1e8040d04c00d03100c030014468920b1580c10074001d107050221007174070700340a844500d0b02c454101ca1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 558927949 1250 558926699 558926701
    0x31803060a0b0102120c1f0509150103033002040626040f0803180105040302100f020306090117030705010c12050f130b0c09031c180e360c010906050a08 67
    0x81c5c00b4440c0c00c00e0811248600030f00440319036071061142c102c4550359400800003000d05102d40c0c51403030440154264407803d18804c00600100390800041901d112402e0594685822460307014042c2e0600c900d51600084c4c00840c000ca041c0790010b010700c241060281c4411016410062100d0104e54160781c080c168085548200d0041b41160700195440511841e840c011031024402d8242142c000321030580060b000f214120707020601a00a06801c1600b03500c09508600748038000540580381803095903903071201c1c12640602c00600b80256407896820000800208020041c05484400480301600c0550310707040c001000c0b018a800210f016440440020100d2021035403801105040030342850589134050040c0549580c04010302c08030414203448041c210400380e900a0003d040070420401690131481e000c2c85030381c41020341c3c2030f44089242400e00340944103c030881341c1c280078040c0160b940d51140d88a00c056030300004101c51000020390b50502603698030700c01200d032030081840000014584034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 558929199 1250 558927949 558927973
    0x80403061b2f0d0e090c0a050f07030309020d08130f060e040b04060b0c011505040c0c0b0406020d090b18061012170316080108010216060f0e031803060a0b0102 70
    0x104941208442e0900e100b40b042e000c4001516011404540000084c06409011228213250071038a412040b9840a9030030891a80005051406a02240307128001c001c0f0340c1c401414826003148030314503000b074180f080e03525103810724800d6039000c4829000c1305c115841000602001c850f600d002140c100ea47c490b103505404e482000040c05042a1055020340c945002040030441c0c007000b018240c500c14000074a0661188803082000210f0707115600c0745140010010105820400800c12160700540b494237070340d50f524100e002401041940402c503031130400710707504000d05021441c0c003d14030314601100c0358240010140d030350002103c034140841d01c020303020440c0c0484100d400c40000c0c45030902845005000703002103501d4108035074668800d84200d141d5000c10707030001203807800741c41d041c8000e42c0342074255940031000544000004042d80e40e030360000f880d0400070344d200d40350042207003040e00d6840c405084410081200c0094051081c01454041010a4858410460111410303006030207201055 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 558930449 1250 558929199 558929237
    0x906060409021c1b0e030d02071517010909021f050d021b300c0d11030c070602070f0918030e12070801051009140c0d02120103080403061b 61
    0x20b80e8111442c1c0514285035080d400f081c0c00342000d0045020119807014101c2c081c0204101312070044035010f5040040c0c91520613501080b244103981603c008800c0001c10b0a0040301c0d200c0d002e034110b0242d0030400e000864410200d421520384640201c40100c003050843d001d24241d542c8075000600032810170000c2c4900c0c0407040e0090010010444a0080c5486401c41d2090601e4030355202d01240128659501448100d10810304509044600540d030810342d41c00701d120740d1444100541030600c2814140e1161504041040700c4e01c02140c0415203d00f10343d01c04001c0d40e00d0007e4020f0f8602600d071201c006c58203204a100c1c00b4164503034404900c0307000c10181c40c2500c0003a003040d541070300b1030f091042003481c00c50304001000080000d0400004c2c58581b13028030600b4000680c0018102608242034008a1411403038650340040003401300c0c40c0d9079151401002d000384a0034480e494840e1000c0000014800c001001c0c1c01143c0c00f58009010301d4140c10001441141c0c54420540840d103003500c0540d03402d0710 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 558931699 1250 558930449 558930457
    0x120606121b0c29150901061b0618050d0804060506060702010903020d02240324010c2003011508070906150c02011209051015060e01081f080601030302010b090606040902 74
    0x1c00f0004054010741c8005204070b2034040f2418012500300c0c010a52180c2030031114140108002c0c608a411490b19205030b21841d0720300f820103070400d901c5903403002d01d100c1c8140700700c480c043d070100803551030000c0e4420207418008200c030180d919519183c00101541416000c640300386505030340340d6410301d0540d030800c022070948503401d07a04900784202c2014000703c803d1000f61001901c0000f1a16441e0442501115811440e11800c81d000140305c2c162440c0d270000c6503c40403507800080315104000c0342c541c1d200002c0200840940c0b40d0300b84000040c00d00800f0749141d0554100905580c034031501c5140310000c3d648940714007512940708900041605204805940702288145080d050b056001011407094034601c12003524117070091110074100a503075216811400094000300360302c43d854803401801c8810b50600d003905000d01d18000802e00714148038552680d103e050103001c0000d0b1906980369813110300340000c03000f40d0300c1c07d500da0b81140350a03c8000c0c880c0301300400c2a80307040d00381100c036406500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 558932949 1250 558931699 558931733
    0xf060909150510180503011a040f090b100f050603010522090203031c0b010309051c0302070203030a0c03080c070b0105040902061e0904140402031c120606121b0c 71
    0x20110118140e83c8400060182d48950340d07490590800c8084803003102e820540c4010310a0785007261549880003000d00c510707002d02040340c0000d4807200e507010403005031800e100000d001c8580340040102440740c611940090b229010200303104640c442052051a101c00c0c01041d91044203412142002001d042cdc03031040030a02c0ca0f4000c140b410031940801d14542240072007a502007124903082e40e11510522078001d0030042480d00303110080300c503242c10380c40710b40c1e5410408084d0700380c44030424014000d40481744681d81c0031f4110f03680c0740e035524001840c0344200c80084000820500200d00700c0c070504419541d0450308403403040020303441c200411004141d4070a0807a0440c0003400781840403040b440813107400d60b4080e0110703a03840c55854200000c40b403040c00307030401d1303c54084244005a14002000e07511480d2581911140380c2050800303036400e0719042c0034003c1e00390500802045866000f000082c2c06e1099031028000d030350700b1081032580356000e400c0d06000554503202c00c1d40801e01d40c5446000100c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 558934199 1250 558932949 558932981
    0x41a04230d0b0f07080901090c030303050c09060d0504050c0d0305030105010e3c0102010e0c0d0201090312090e07030c081314012a02010903090e040c0f060f0206010f060909 76
    0xc1c1c0c00b580c8003075070040102c5440c1010380c1140100700300c0e2504801d501d40c0c0400d040d0003c000d4803450b50b0700c45501403041c1c0006000c160f0343c3e0000a502d25107180444980c050024016030304c80450340c114901070101100c044506000d42c850303d80f041d080030304806050b954191a2581142e080c0001111044000c00109600810001010407040da02c0c030000d00d03805082908030000644c00c001c0c203011090300e84c3d000700c0c1160725100e509010110081500c510305882143d000c000c1c10401d00040756082025007000e003070107008001d06000305805c00c03501411114400c0c180e106560350b9200940842e444410f040c1e02040e01e102c00261a003e0717607120031039050b2150812440d814501666035007126483e144d00b41855107080c0011008100345403c2c0d22031100b252000303110546a0381d60080015035984110019064540041000c0008501d08203014004445500340b4051303035420010301c1480c03a803100c20094011000041042c2155140480c15100e1075112220b1480c038115903a4005c0030183c0c00c441701070b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 558935449 1250 558934199 558934219
    0x2031317090409030f1112120628091a0f01050d14070e03100515010c030908010c080703051f060522080c0a140f120102070f08041a0423 60
    0xa40e40b40c1c400d0410180c0203540e207916120784124003a0001c2a4031005a00070380c41102c1410440c0c45c1d16040b1285c00c0c0c010b10010601f0349842e008190a14540f5003102103100e8015520614403600441f200b0445400718800e00502e05c00f0b201e08001004090009908000042d1980c0415400b0302c00401101640d40c0c00080d54000041c1d06050441c015a201c0e00080d0401ca07005060786420401600340c3c107a150000c0055003080030301d086614414a00880c1840344280259081c51b014a6214004040d2f00380240903d03400300b4402840074400b21803480c0032900d8440455545024000d00c02d61441ca403d5403400b25038280343e03040d5840d4104403004152100f64810501d07205441d42c80d000001d003084070050000301250410811000c01a402210710700d81c14100f180b1281e40c500e01c00090408007903881d00980e0361448012400b9200313280014000b4110700d0049000c00503000d004104446800300c0450321105000c02c0f140061003148600340c0e50712003030384545030340c20f10703200710840d54080081804100b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 558936699 1250 558935449 558935467
    0xf080702030c150a20030304060b0111060a05060a1401020c01051e04030b0115050309060c130905360303060609030c0a06021501061103070b04050c0d0501020903010b010302031317 79
    0x8202c0249602c0c0c0551000301e614192190402c0101d08402e011780c80303010a6205c600c44180e60f80c040100040d000b01c0d211090841c090f402551004100001f29080e02c46502e400c01401000e49000d075020340c0582d000c03c82c006582c5403030881c1031480f150140e0140c149035443c0b03c011182500080803085c2440d02c01140904c482182100500042d4800c561814181d89410740a0150b00d401c10543c03014003408108004804c607011450035030012142c1c0c42c07541c0301c031006ea8000250410a0300310304981031618061108072044014400d4440e6452454103581502c540c1441c00604d0302c81021310015402030010980525085c030241001040c064100c460460644000030001d5103039621060158004c50491107902d4401c5000e50301501040c02d0608400400e0003031196a0310800c0009400038040e84086010008184400c819900c4018282c40e04165907043c111700031741c0041c40300c510a603e00a10800b16500034000d883c03052103c0e40405404144070740b1801842403075000890102c800810043d030b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 558937949 1250 558936699 558936709
    0x3080907050a120501051b0a1103090d11310b0d0b0c0304140312070f020a0c14010207090c09120303020c0a2904020f01050904110d0e1203040f080702030c 68
    0xc26000303406403c4940c0c03a090107400c40d9030152140101d08150040042d4101003142150100c3e00b2600d07203400c9154007450001c0c04e6000d10040d055100303071400f64000501a00140246402404a43c5028242d00c04240e51001212080341030b0481280740a2480e12110b82e0303840340d0803504001d0528648880599541001c020342110701100380e1001005100038026159142100c118401004520b0100c03040184003800000800316802c01c002c3e42180c4148500c2402401084c60703010150708010fa85907088051101c01c00c008003401407041040000303005806002d0000d40341da468940c610102e081241c07401c0881c0e866881641856003c100001d201c1d0750401242e6003d0707008041028120003d4110482d124601c0d0401c0c6061015280c180000b50b550f81c1c0c05c85640070824240560342e0014600441c01502110341c18482d010008150243d200501d83c010305a41c910040a80342d00704003010700706500d40800d1394040d15140300d102a080010301031200600b44640010304580c015004c136800aa = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 558939199 1250 558937949 558937969
    0x60a2a02070305011b02160503030301090903110d091503051e100b1303021005120f0a090c150201240312051b16050604060e0d0609080f040503060f0408070308090705 73
    0x200e05c80d07182c0c00010b5109505000707840320020b0b21081a80340e9868040042d65038001070080e0341495640e072200408041c02080d6042038031a000c0241e41207125550405800303c496846916004e07000a85100480c0303100b0701c00c8522600311404442c603a10043c2c00c1d01c0301c04040080c90001e4541d03010303101240498a00002d010010b502e038006041007230843c810f1205507003040e5030103002c4c81018000e058901001c039a041da0300001e81d443c440380698134008400040d00703580c14041d004e02c40301c0c5404940f07490a0800c1c1c068884850f002407050010b42940044100b191201d80e160000000c003082c030015281082c602181d621614103141408609100010340071368403852202d80d64401c5580742190b00041c000d47c00148001c0b135840d030801d454100068400035241100a00c24411000210100002c0364441d03810706800c1300800740c44118035040c4454070f5200f4001c852081c810071002804441c01d0030ba27007078800e0f81c1c40020107003441c00350394068540040181c6203030750502510b02e001c03c581d240c100f120 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 558940449 1250 558939199 558939221
    0x60c05060a090326060112020a08160201061703030a0509070803030c030a02040504050f06010f0f0203160c0e0408070b0105030604030c02190314030d0608030316050a0309020910030302060a2a0207030501 89
    0x31011800c02c1750014109000a0465191950040c01090242500010318907888402c811115010b409071140032401801c550b00880c0ea405400010a08851000809103200341d1b0b031481c00704020303201d03644284d42c0c0b1400e522a40750954000c20001e01c0010f0018042c60700031010710b2000d070400791600300003000e444084a0203200c00240034204103283d17034030501891106001c0c1c1040002c0002042c0000d483c0e10075045d4214840c0300221058040003010318030440140401800003801c1c1c1401d24059146900a0100b81c0311484e4050002c5010f00e030104219001d00c0d410307250080700020343c1d8244007c0c0c1c85010502da500728008000080803828070200c00341d0b240e5564028540c2c4420721685501200e40d943c00c4004198014410003c100140102c9031405511604200f5142d10195800320081c1050782c20003500001d0702401c0c404940000c030340c06010390b44241c090700c03103d54401d40e92002b159281c60b07412006003181c00d44068416100019080404c0d00c0b031056840c41c0e0349a44880e401d42d07c400100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 558941699 1250 558940449 558940517
    0x1128030303020c010b180c0a09030503040f030c08061303080c120103080a03200406211109100507020a030b0c04030501051f0e010b040308130504090609020a060c05060a0903 76
    0x7180075070f80f1082c4540f9280e090100c55541650340220000d14880d8030051811068402c00a045070303009005504020055a1240807256074589600d280d03841120703144070880f13140000d204041024003010039514460300c01da540c1104086043c0d102201e504d80080c01c0050003840c00c0026881400c0d203c405540654060b01041c1d507290720300c1d980242281e90b2a4401110410364800703800d08000910226021107902c1e1400c100350000420000c3c1c09078100b41d01303080800e4070308101c665400c0d006402800c0c1e00c4504441a11840c810b4103002c0d15113100e080c01c0250f001074445000d10004c1c103c40c144a400c03140c0860008e0420780c5a50f205405c6840650f43e402041690b00600e5810301603245609015052449102c042945031100106c41c9005030300000b0903003280429400e654038160b0070008001d200041c02881480398505180e0300811144500b07900404603c2c40216100b4018100003489691210041000d66980c002400007816105022402c00401000a003520010304848100204035401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 558942949 1250 558941699 558941707
    0x20d0921321207110c01020c210a0c050102070605042d122a05010c38165004080d0e060433020d0206010f03112803030302 54
    0x1000b610b00720845221104e9a4040744507890701c0c0e40d0125000010070340035140f03422514004149a4022254009004a1846001411410301c00440f40050460302c0070303001d8a02e26512189c0c115482d02c1a401070810b454030281d44030b903200c0c1042ea2100d0404040d5402c9655080c0c4503800c4c02c00640c1c00d0030084d11a0143c10f00340011141c0c40454890203640010701210700780703240070300181001c0b40c0c4083c040c00160a60010200300c0b80204c00c410916804402004a5815880503880c4400010f580171f6080502d002165410300c2d02540241e480d00761040042c01d1140c0c0344c40004000e460082000c00c1c8800e4403810703903410b800215108071400705000c00d031207925207040480081c41c06440081c0c1030100940750001000d40d803141411101502c1d900d00700b0021600d01e9203d402e810301c207400c1c0300240c14010014044c07141540403c404040030900d030b01b519405d9903a80704840c0141c1040c040a880400400d81c9002030345000090700800010194032150350758074a589070074098140e0740c01a00401c0d0005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 558944199 1250 558942949 558942961
    0xf070302030c04090f08030406020c03030c03070f08040b0c0c100f02280c080702041e05180309060415121401060e0105120703020c010f020d09213212 66
    0x1202c1c00c039900c00140c5003000340329495120380d2002a1809400b404005c070010100b07013881903540440e00d8203a100c0b022241d90742890a0121280d620454000d00015248400b8100e2030b44144140ca005540140c800c1c1c1081e1150000003a06a00c00c0b2101e25583c8602c0784c809203d21010300981080c1454032100503156480848803196215410109045500c040c0f9900101d13507412084040140350030500050f00d84e106840413400410a41041030455a40e04181d03168828054110700d200b224280c3c03962070001501c605c42607407400b0f0803100d40d9101a06000a00c0102c00d141c0000300019054940540e03580c213440342c0031048442d003480052802c040b05005100030307504009070241000013031800e40c1c5001c644018010882c2c0c0060011001c0603000603101c030300c0c0c070400d4010242c0141c90701021583c51904c1030301c6000034520a03038101d40c2400c800c2c2d401444a030804000101000140c0c407489044058690342c0820590352203103030039a40308000c1c020104058035601929149131102c4003c08270342032003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 558945449 1250 558944199 558944203
    0x609041d0d11070603090809030105101728110d031d010801150804020f0a0e041502090907030905070312030b01080603010b03030d11070503340b011707080f07030203 73
    0x4444800c144444603500a5002e1030000d840421510b01e03240000c0c0340380d03540c0351800c031610812010030f0340b40d8248024407104540c03003040d0b030b8101c400c01c8030002d50700c60111020701e46404482101c20b401080d141c0d1808036141c9100088001107114085c000720091225001512801800c1c0c000d40002d0700040b86403400c5000b24410070325044027400c100c1415031400d9000203c80080d842c40078108120a00440e0031034940d510307003c0070b02400500c10303540f09880b0305120032410b400b11025210305100c02c9085083c4402031007122020240034251580641d12940e05501401002004441c180b00c0c008001000c500006503110801d006a603010503011082c000040c4011310103003220f80310340d150924110840d9000030032200c54400c042d5021983c000703c550036220f14007880c030020f4800c0c00b001807c14240d41d400c684548070529107542c0d01c0c02054510003400140c82407400014104240c0100500641099103200b01841409130b00b141c11b11602c0f400e02904010007000c00d0107403075000b403005008502e0f003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 558946699 1250 558945449 558945463
    0xb060301200715050402062a0105090d0e0d0804121e062910111204030f020114090306130813061107051912021513051f020705010e0609041d 62
    0xc0510131301441c00c00e41c00050840c8600c0300b0407620300300e10700140d44e602954421090116400d1030002c01c441c0c60800511501e502004070f9040014180c082081b800b4503240c900310984c0c90f04004050300b014286410b06030a40c0340ca92044c2c0d840103c1001030080340c140354440d081030610851010a000740b08003181d84510080041c40306810311440e103403001e10380701c1e5041e040840c001b51030091030f904543c1d04030038100b00c01001030440701800040c001c420700150a4244614510030f0707070344111920944600b4000c900a0015040d4140c1200011a071100e8a09518466484c040c0c0c05452038620705180345680ca624651005c008218951380609203010b050000600074101a40d4016021311406100512080346010350489888440b104209544801011000c60380700044455651155070b0031125050900f40700e16882842e01c82404030a80d10440d0795040000c0041e00281403403400c00c401580d1502502e03020751b0304258107000d000c8a543d0355000e6440b03528240f0300c40e1640c040040d00d03101d0820704 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 558947949 1250 558946699 558946733
    0x40b0711040b10030c03060e09150c0a0c0b0712050a0605041b0c140a12110d0507050a060903050d09030504140901050901120507090617010614030a0b0603012007 71
    0x4074060b03040110792220105a4882201d510380020083c0c0c6409041d0028902c2d600310181c41364400013001039003140000c41400c0111a807a21500d2a56002c021003513901c02c0044010001d4082e03000200040d150f2811141c000006080842c050003e01814030300b100d00031500440c43c1e54444104200900701442401004207600310820b5261aa00c132000d0014003400c4801080301440e01070352542068140020150560700c504180340507000b00400510340601d0f4903460840d4016400d910800380d0040c0100c440061340701c0c010700b486080c02c3d01d40b0401030603036000c1034003405801c2100035a044814403a02000c0ea20a80b601620346090500d1048100340314a002409094000010720003a0b55203000941180d03412088907107a85014901582440d041d540b08140d03882c00d02d0008070707817045807a195280c401c0d0144001c11881d6034810140c6410a0b04444581d05078000f0705c20003000c00d20000c3d400760b11070400342c00820010311102e001d100d031302d01c00310300d5042482e070219842040001840305c4d40003440c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 558949199 1250 558947949 558947951
    0x17040b031e0c040f1a0c06041a0105060403120e040b030304081506041503240c0c0b070c0b0a090f12030504140f03030708090a0c060503100b04080703022202040b071104 74
    0x44c01c012200c14158140d0141c0c020002c1c80800d000710701a541021503c1055440080e107580b41090714010219509010061080c110083c002040314140b2105480469403c0011800031070703030000c000e688040e13400d0b0300203402c1921000c000c501c980b02000104001c1101200034501c0002c041c0e4048400c0501074075a0b44560708184070b981d041e2000e409150f044d260400415500303181d034070300c0400c100030b0320001d803441d020b061030300d0b81c0e21503500000d04102190187c2c40905031b540c2c80140498080950320310041c42c5d102c03c4408507942d02e5040c0e108800140c403030b0007041610245912a08140002d12003813200103900d0300c2c2007000b0898500d01032000044d60400501058294103d070644038000103103030000708a038840001c0d043c240100080159260020041c0d007101d911034400030560340c0704075800c10404101e40400100080d105044404880f0b01d030001d40111401c1d0703420080552303030090070340c502140303401802101d4600504c02440144103917110182d0740c2001c2c3c642298070312003c0c03000602c91 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 558950449 1250 558949199 558949207
    0x60207050f090603100e030a14030609010317040302040f061a04030f120c08030403020606011407051b01091701020903100209130b0402040b0a022802010c17040b031e0c 74
    0x164440c03848184514104550044159543c0c401003460403410202c841016404c0c000da250807800080000e00340740780c407640c5001004124010840f00f42c4410346010b5042451400100007007400c003603a02101140a1144500d000c0d580c0d0002000c0d51b44e05070035400c40707503079580c000c100c0000460100c041000c1030442e141c0c141803075900d4000c041d00b100c8002520301074a0315201c045044c42142c43c4403100f98410901038480c289420001e68881080302c0782400318100c4040d00315050041f0003134940140e40080100985500b4021807800e00080c40200e038184080306001013a404030710b011908105e4410000141c075011484c041526013546034295141c400c0c410030601c1043d480d04444140040f03800c0030045001103102d40803c0083c4144d0388200c24440010880000055000c0741001e8412600c03104a0304000100c201c4c0c540f6101d80c0e000081c08500c1e05100348000611700380038003540c8a02c10f10003904080c1d6496903001140d000f02d0703080c00c900c6124480701481c2ea604c44c0a8076003114800c44040d0034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 558951699 1250 558950449 558950459
    0x20408071505030721090602031501030b030309120a080304050609152e0b03010602010f110405060a1101090611030414061012240204080d110d050a0c1a010f060207 72
    0x40c400a0003490800c5450300d4214480b11120400c0b005c0038003450820403081d070560800c034000b504251400201c045800701103484c103601c44e0050300d10011000b00614a40b00022007040800140d000c2e50703550754041c0c80350101c08640e516014510a03400b44001d0900d9180c000780660624980300e062071900c40805041c021001440820510304009a0346815141a0b12580c4903081f400d0941c8450a0f0350400030000c5003550b0f0641040f06403442d034260602442c00c1000440310f442c0a1409455040001070042414040c4506000c0c840740d030801000080a08403901d8401c00d88520020540c1d40c0c003000000d0008020b12085c1d1040c100f86901c014010600b400e80c0c1c1542c10006074460403070310b11710101a01303003446a0317170201c00c0450b2600d80c1a0050a07012022361000b0350010b1060710030b5401403803100c1c2c0740140664840e00d000303e03240002c0d01c412040500e0954054102c011140200b00031003141d10300180f4034180e14805090140124036066252484800e10b08845800007002c5400140301000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 558952949 1250 558951699 558951707
    0xb01050913020933030d0311130303020a0215030702060601122310050604030309050402250b0603010501120809040c0e03120d0506090411150d0207060204080715 71
    0x106565044032112041d448460040a81c0000c00a0181d4090041800d121001000b0400c141529074860903c006a8030031440c1d50541131a2107000c00d4041d04200c0c600d24840b4800c0e030103030000548001500b82000c003410400b645110064004601603841068503c003907280640140185485203000e82d07141d443c200300000d4854038041d12042c14407161484a5443d42d12035089841c03411030101d04405400000c03c0070b003031002000d480303450b0183c11190300480d20781808421030703040d40e4254135a6641d1500d00303014013001394004450f101e04074000101c0600c0810041507228211070103420006060b040c21000c1508480c0103a014054503034413010601d0000c2c8413241580c24a00e0102c900282d05e0180741020742c2e0035206038403502c4d4140a44094101460b0501c805040460b500358000c0203540d540006102c00c1d9031056a010340320203204900c1808518050200151a04103000ca4600300103949214a059030080c1c10704580c03264011030180b01102007080305000401c0c1520340030391440403480d0050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 558954199 1250 558952949 558952951
    0xb0403020f04050408221a040e0c03061c0f0b01080c031207021f08040605010b1201140111030307090503120315060a0201091b24120b19140a06020a0b 66
    0x9000b90346a0000034140546201914075451490541000814404010751503200311405100c2070310240d51040103207104010152016104104180301480e141e000c0001e101d130b00000e00f115880400d1b200c2080300d04007001f079012011880b034085012282035030314200900d080160400040c562115030451001d41e400104281c010100c40c012a80c0ca002c9030011a014509140079010404140881c0005050344005258403c5004d128100400d0340c8462040d0200d201d94500740e14209560001801480c1054154081d50101410040b9030180440c0d0a5810360700101c540a020551400080101d801c00b4030800410845180001d031a5141441094800c00c0000d510300c0d025a60119400050a00035800011015044a850030030740c2d0010049944503031150064038054030708040080700c52000381d030000e14142e01984851070744039558400f040052085412081c2e01880d034030041480d11802550500140c014040f10000280b010401c0c0000024941d2000c0215400380380031a010a818420791 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 558955449 1250 558954199 558954229
    0xc2c060406210207051c03020408150601110607021e0606030a0b090304030f110406091a060319020309030408011104030308041209030506150f060a05180604080d03020c070b040302 79
    0x1058019000d214080b01040c98020401d0118030016032441480030000302d0020340c480104035160b1200c4a040c00b20281d014502c80e01c48030340d100d1a0007401264400400c0e81e40100107160940320055005041c924040c8161610b0003d41c219040c11403200e001c0360f40e5400c4a500000050045081c0310700803076135900e40b515000e00140501d001180f5030840600849005640040c081400c074a0f49040620b14003d04a40607031096282c9400040c1e403103414042c021002c1c2500380d0f9010400d04180074800650300003408185e0141b100f00075944115004e201460160aa07540155200c0c0d0500a516085071006882d00352110003d202c200001b90740310300300e554803d51282d6461207001e03070040b056500382800d030402002800380c2400c0140d010361b0601c02d407401c50801c0b600381d00c3c0c40c0c1d0b110007840a244030711070b29103000800800c052191a02424000140b1510241c0098501a6641c1400303041c005d0446071640025000540203000010802200006c0d121018203680303868550742c0003e14601c5070390a1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 558956699 1250 558955449 558955457
    0x15020d0b0a0b0a0917010e0601080d120c17060f280e0603030406111903030203090601050a14240a050301031a13030e040f1a04061508040b15040c2c060406 68
    0x300d814441740a4020b59060f154080c201d031920b50316101c480e5202c003903004140000400641003211000543d000d2200606019124007030420711210781010fa4200c0185002d1b0840c283d80781a01240c1c44905100c84d6800e5045d42820078002100418810120a607011000c84000d603c00c0c803405582c040200c0c0c0440e621400c00054041c4064080c03800d00710014411608080e000004009042d019001948100958826120503a88031020000d10304800d0180c40140601c20140c4991803c00c902400c11151100101d440403500703808000a2580c02018010b00041c4084010070030130014100002148508040300d030803500d03007060340218041d481e44001e41000b029500070b01182e25903500c00c0d15404041c0c001845180102141d83c28218020401a40100e00d0454006480c0c01d4000ca102d010075003a6840c0ba940d510350351241d02d0540d001800c0e01c1d4541d00c20350a90203140c1d4441c41448050a00c4d500d071001c1d500801368825805821012204410002d075014058241d80c0308803c94007035840a0070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 558957949 1250 558956699 558956729
    0x7021c0c030803010909030e0901182a051c110f0a112e0501050603161709010f05070c030818071208070501061d0c030415020d0b0a0b0a09 61
    0x200902128815070001d05040320001c008629154290400c00805000b5180d14070b040080e0400c0c031100310b109100ba01048050490002059403041d0080466003e003442d070b03484103035410300103141d0315400c803c094004030b800090400c60040b0f101c50b4082180241c2e400401900c1300200180d0050300c1045042458990002100b002c254015030845441c800c41d0350480340c0d005410b401c2c0a003202c00301c910208940d41f140323109c020302d40c0581c02254142c9001034030039419034540f1508401420700701c2801005122041900511500c90b43d10345c00d104000200010990100f0440e82c80c089586c0074108204001403541403201191304400c402380c010b185216000c0d014150210507038103210300c0760070082d051158a43c030102884038800240400500070360082140d684e0351035000816000040440c0b203541d690100007050b00e000c0c1da0185512074024081a400e8903060180700040341d02c805148844603645c0c07141c440c4075042c44075001015003034500001349070160743c2d100500030031007a214501d00010094 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 558959199 1250 558957949 558957953
    0xc240f06060906120405070618061b020303070f030903060b1f0f02121201180c0f0e040204030b0910050c090a0306090c0902040303172508061f11010b0607021c 70
    0x4680411200c45120200c5060610340147c40d5042440b43e2000034001c54010400443e031051810120388154458441d110b1580c0c9039104c0d403200c8054166814001404a000420701e007441c0303042031621982d2152041420b525100c0116610240c0761070044204110010055903090740109a2054030309101e00ba010080c0e00817450312800c00c1111442c2800410742441e0100440707800b60613601c50b8840c018038000d420030ba0104840c0c40300c0b15800010342c1c0c0c0942e1000d02c4e0160344c415980c4a009000035182c9a22502d403004004400e688041461340180e010460440380c82c8186078011400010162810584d43d0005400c0c40342400044e218503503518624040020004410004054840040d5121552428080e14441013003100c1217108500f00002003288131030385a0107403181821240d05040120413081154440c00040c4442d42100303890040e00b05040d01e1b14860601303d1400e940e950144e032854880d40303003910301c400070342d40c010f640a005d1540185c1d1841c1d10006410041c10110064403030034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 558960449 1250 558959199 558959209
    0x506041b0e0103061409010e0a020c160509131110020a0b0f01030507061e052a0c010e09040b01061b060207030201051803031e090c060c240f060609 65
    0x4500300032403850403801540845400264118501000341c9041100981e212585c2d5400392015a4190340640660010f00c07a2000c00010700b500a0603038100181400050f100f4940303042d90b102606031081c0712144040210380b03406450703182c1c44141c0c030b203460742c0c01c030002d80d1034007440700c01d610b0b00030300c41d130f0ba24408101410310805c00102034a4000c0060400703414880552604004c080c00195607a0043c00d41c0803032154021451021040340c042c0c0781040e02c04401d2800c841ca60411020214075807000144510384841c03040c2d664035010002c01c05410181345000024241c0400200868000d034020300c10030000c2954012564116001818880c104154543c0344842a00031110004c1c05184007040c0d150038540e055201602c00e0070309080c4400304d41d80080000340c0c0c0b408112100d2113040882d40000007402883e030f05490300000ba0b0741c2115812480400000c449030080c5007400440d80c05030644800c0e000c0c20304100344a140320010150224109004040d158520090030b45015200c00203034050305481d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 558961699 1250 558960449 558960461
    0x210a0e12010b0913050c03031806070c0308030405010608010606030e1e19050303010801050105150315060903150f060d030903060b0f06030a050414160e060d05030f0c10060f050103050604 82
    0x20300d864001d00e03044c03040c00d00c50103003102c06807154030904030842083d0600000321317003401940034414003c0008240800071aa440340a00311004408481c002000034500c4000e9405940318000228040e0304105d01c683c01c59049511280805040002d45020140c000c5001030061400c81c103a1441808d17450500c904c0d103082220604c1c10519601d02c04400d018000c4050760581760600024403c0342d0303a8030100120105030419000d0803160410200348980f00030382624840060181407603027000101d000283c01d0082d17502102c108a00e1500070040030303481c5000203d40c0058103d5541c40241d0321a2801441c1120138003009140d04c7c0c0c0c842e00e961050342c400340c102d1034000703001740f03510307a0f0385401d0725800060b06044d2004c6400c8400415142d120820100750a141c0d400124015890180307031902001000101400c0c968000881e042d070300c2c000c030b1000d100038025401041c500c980c0d21661401d07041d01d009100b1200c42006881c2138014044901000300d0b1000b01d403c02d00c1d0100e610b844520001d002401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 558962949 1250 558961699 558961721
    0xa03020304260403050708062205100f061419180f110403050c010c1709061309050108070603091203020d0b2d040509120a17010602210a0e1201 63
    0x240e00c2c20b01d6107400c40340100034010340344a0b200b03841140da510030126956031402c2d02d22110795041e60008091484191084070182401142180c270010305100c2e0b014110380f86c0d0000d82c0000d070b442e0b10052002c2c141a890499015006498880c042c2800301c2c92080040350500030050801980102c440240400b60808003000e00c503200100854000410414a50f920600c001c0303800307002d041c1c2040001e60240502c5018540c002040c0c0e0200b540d144850091540051001c0368854010711600c20410f03000300f0480040c01c01010b000a0f2541000c42c61450203446920a00415051075020300002e85400303207150000d00c15060241c0c5a0b444041c42101500d20070301e0843c0c0028002030600ca000080c10343e000f4003001e980c0790a141e00f514440a01064403001c40d03030031409520542e0791a50344031408009040000542c541201c483c40c40d030840700c40000d400e0b4032050043e805214042811798400258000a206688456190407841a0080c10001c01c107103410b80300f207145046500e840c4e403080d041100020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 558964199 1250 558962949 558962993
    0xe07030b07050712020a0507150215010b0403050606031c0c210e040b120705060d0212010e0103050c010305130b0c190c060b0102060f0a0b130c02010f05060a0b0a03020304 75
    0x1107005240202160441141902c6a0680304c14451050b40080703140d80e1407070b8111000d132503900c2c14600000200321182106500311f10403032a03504a0a808100d0b00c5000c1d1844081c0341c0d50303c40c83d6040180c54244003411040c829040110f94164000140c2034140090710b40381003048540d0100c0c2803a05001d9144800401500c800800009807294801000098682c08680801003d107410092000c2000c0d004c00740e806551180400740038a1034032401a042c9036142c02d00242c5403200d603980300b4021500030392000c8040d00700c0900520400c007007807005440b5800207190400080c506100c0740700762600c0103000a0f100c840003c2c08260312548030070494101c03c0140800d0498011044002003c00100301d409540281c40c0141d0b004041d840411814012840c0351140c00c000c0c6c95079080d8000401d03d020403d0791000340c06c9281108000d09000e103400440c0c132a0000510031a10408800c1601c1000340018410f4013005001d000401c0c800058480144485c640180c40341d4035445e000c40e1101c041d0007650980 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 558965449 1250 558964199 558964201
    0x1807080a05270d09140a1701090602120a050a140c07030309141e01050103081902030409090b0103021c080f07020a080a0f0c09060501050405040c0c0210030221010302060a030e07030b 80
    0x50002294607144965545100402d599040d50b019011400c001c43c81c6e0140246100308080c0c80d1103854144410007640c0001410344aa540308030480c1d0050041c0c6d420081c2003800c2014001c5a481101e90109050707a046c0a1b00c0c06d102c00784403040400410b907603100d00000c00c2c4642414807030b46c0102c0da40b41d0311100c2c05451a04108625a4510081485201e03c4084894200c0c1d02c440601406048a0b40030400b1030a081c4422000c0402610050301b813011031200740400550042140520300c086800741e000c00c0030703550550040c0001d400c080780d2100d4041c0791440007000022031080032a0138601605041c180c8860891000503420300b000c1c3d00170500781c42058144414800c4845410b41c0c0c641c130518a00340c0041c0c1d2110a4400e0f0754a51003040d020620601013080f082c1090b4004c05e2011101d840c010401c0707001c03540090040c003009100c6000196001c55013043d218a01c02e00c40300045485451a00315601d15800030310f040c41200d0303000c2d04041c3c07102030f10540c82c001001b882d009154070031544445 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 558966699 1250 558965449 558965521
    0xe090c090c041a19030902010c1a010501080108010e060f0c09151801020d1713200a0512031e0f07060b01080105040e061602030c030d0b1807080a05 65
    0x715401500544450540640a050640390a2412916603200c0103001403003600d60a0401c3c0e0081c40005e034241e041c40700c03c03202000003076041881102c242130060245042541020001401c01c40e05800c0403205da0f14040e2510000000000d0700f41d80f00413408001c00b4182d95a030b9400b40a400703443d1035550018071200d0250300c0402c1140c05060799800146881490381100c1004994901c05183c000e0b0108102c2018a0f14648109462680c001155507103000307064065651401c01c00c02c90740c50b4200400d0103020204c3c10740307410f0080c41c00801d01112100710540381c2e08042500c81c8a40c2c1c00c8510200c165041a0912114400596044181140900341c0721603c0b810140040d00f111041c44d4000380505002046a141510490001140701c5004002c159a80720700c1e440c03143e0940045030154030040c808034032110b00400003010032141f00c1001290b4204000e0901117000500c45070403031080740b080100018030b030f8800c000035071203038034150003281c02e840c2c1c4022880300003982040d030141002e07080341c0340321 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 558967949 1250 558966699 558966721
    0x10c02060712111e060604060b0307030b01050f121e2e08071d010915030308071e020d11010b03030924281d040c03060e01260d090e090c09 61
    0x2c40e6070031000a9861700d0f035985080004030344650081034408481070022410b1644260300186408134103051581ca0484003112003885600031405090001e0405010443c290700308401c59100c0e0f624042c0e008036103040162410404040d01140700c0045202c00050302803074008a001c081c005d143c10000c0d5007546445100300c4880480c2c0300c0070314600c1008000001858011b03441290490383c0103110b4410014110768046480001c0a00040c08021015039020846600c40f00c204048a1041d0010084103d10413000b070800d051490049013140d26088803401d003900c1c0070040720100502103403241007846d4500808e15054028035803e0b0036103280854641091034001c0e055034500600348002ca81c1042d09402308031201038044210011900700782114015504090304160841d600d036050201d411038440c0742c410b8103034200342e0028844514030f00140c600401d5000c201080101807801402d880780c40440003804402250ac5600c05401c0381200244080405000c18548d500004081c3e140500f00400305036 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 558969199 1250 558967949 558967993
    0xa02031009021503010f050910030b19020705010c030c0318020a0308091206070302090a0918021c201f05040501080417030403180b0a0c02040507170c07030806010c0206071211 77
    0x14018200040400c40c0d8100c16a09e6200304c03a8000c0780f80d019a0b65412418501e1941803031086482c035000e004c0d01001507005c1c001c0111211305590300140d11640481d00078103a5000320015050031030f04480711005038991580c00f000742d0342c00440360790791745145030041360ba040050801c4091314080d0a0034003024580c950006c040b20340781207070310140b4a038a60450504070380c0d49180c20107004000e0282d807001400c0445030442a580c0f140e00d0542121200d0712404812288811102c02074100400045030503d0070440c1d00700407051000400042c000c3c0f07800054550301c914080d45040c88040c000103410403400110410a0000b140da8a580301e0419143c085c1c404180d40114412100d4450000f140000c000c005840c08882c4503170300c200b500d403810340a01c00184400343c040f0f01045200b046c0408200f0500d25035501130322080300b03040c0d503130400390900820303d03031001e8415410012480000000b69407480d090303410554000c4000ca008103040340080d00d54510f0701d50304331214000c00c110800e804140741541 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 558970449 1250 558969199 558969209
    0x80112471509010e060909030c0106031109010f0f0b0309100c0c02040608060925030f080c1002030c1c0b09090706020c030f030a050d060321110a02031009021503010f 73
    0x4000e1640300401003005002c024000c2c510003881040004845240180200c1d80008846040e2031400c1e010351090740c20f640068000703645140410011030f4407800c0c0b210241d401805910442842e50b41080103102c0354685c40d1140745c040000200220303203922401d0000168019480381d00700081200d8201c040c0c60350f4103881c4160310031840c21500090664001c02c21a00c244604400b0345100c1007411620360340c01d103090300507461031540e6400100001d00f030304220a160034000e43c4030b10707101d16950002c0c61510300b08134414043c0380e0040c010300071150300c1c1c94140e81d80000d81c0001c2849051034803904100804007514070740e038070411510520140d03074004144803040e1003450b425a808690014185030755408506c00094040d8020882c1200c0c081c800c0300985248a00503002180080d92510391113140d205000300075440301107600340542d903035402c84081300c44801c084005c0c0c025205c00e03030002600d45019400748005541c541210354119034036001d860142100d011907181e144c1d42c444041c01c5c9503600501507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 558971699 1250 558970449 558970471
    0x304080d0f0f0b0909161205030f0a020a050f030f0d0506040f05040b07030c02150402090403091205030a0e0f09041403040305060906060301110c0607050a09150305040308011247 78
    0x850246a4080342e02d10040c512040700d603182c28542003e81e03007c440e0003801074030103000c1402030100c54446e0700014410f1840940c020701c80c2400c9400c000c0e090403030604c0c5040c3c2603071081020054203403502c000d0f59610208200c002565035107178030109028100c2c44400d019902c4c039040c104420407545810301805455542c2e01040040044801030703a5401d811075502512048110003d001403800207030966126103e49401c1803440d98804410b69a400c4840342164035070800700e03052441a5024200032103080c011508440e40b40c1010001c2902448080c001800c60782d0503029403407110108000303c800640e48002292010b16090455039111641a074041d407003942401c840e48204486a02900c2c803c0d000400508410f0308c40080c1a21541d00885d04402408410140002e40d1000f0304c0741001400301c60345020610745803504d8010032864050f0001456002c4403220074010540d4050544405032419441c900e8054803070404008044000302e0350b41d49100244485840c5641c128011030144814420f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 558972949 1250 558971699 558971701
    0x1c0f0f0c0f1b03050f03061207120b0717190615050c06010902040506160f0209010801090c0b03071407060902190305010605010c21090308030702070e060f03030304080d0f0f0b09 78
    0x16610742c010034205800380000b80300f4401111850203100040d90440001417000d4040c01c8110052414007840d6800031100c200000d4140d410b100d282c0c021144d000e41145050a0341402500181511080140100111042c8090b032245141362650000003e00041c5103c00041c049840c00100260702c1300c1140c0140d8040d4000000e01b034000360007a60243d03180142540e0622070008103e01e2061191b81080c5d5075a01980b41d2100942c440c013100340d000e01201d100115544030503082408800029500024421a0130400c0010299105e61010901e80701c1c50152035032003880d400c26002070078142602950202003a0800700b00203101c2a80c800880b88100d00a2001c40d0391100151400410744d038001d04140190064002c02c41d5065040003c61450390030250b000c146c494540c03500f20b40044444102507446510140140c2e44c1901d50030b903220108840c4207409102c180c0111b61a400040c0000342602804240061301c2081508010710740b00b0060b4040201380c4031280c0040103030440060440c00f0302e800764 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 558974199 1250 558972949 558972977
    0xd0b030606030a03081b0403080a08070207080709090827120303010f0306020723010501060201060b1603050307050c0a050102040509070c2f061602010906051c0f0f0c0f 74
    0x2045152050750014043c018402d03140d1800e480020009088881b5641c4140058802000c148051710166001d0030b18142c452100e007074050102440034051074155031080000304612900020404251004000041029895450043d0550051050b0f401c80207006084007025a241141c103907044d5482120b01d01010348000500076240e100078019242c2c006800303002880402c1c0e03280c0003400c40b00d10030110703440b82c885082d20841d2042c00030480b44c031059460784010403110b40c0c240121405070011203c1a442d200c401c906059424244000003814030601200040c210340c020020b03181c12984990036603405650314a4400d0003540f080c00b03050300ca030b02d0110200311014030600c40a0012a844038840054400710300b04884007204131082c02041c072078051504045074a44401814138072042c0380214402c8142c1c0e10025081a0444e00320700d08101c02405808810482c20100422000c44580000b030308400700110b5a000c0c01c40009518506414100c54448159101000e05000b01061b0b0b135510b10702d0004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 558975449 1250 558974199 558974203
    0x603170d1104080c060906040801050f010504051006081306090b13030912021c0c0512031902010225030c020405090d08010504151e0e01061d09040f1b03060f020d0b03 73
    0x1c0c043d950f00c50f44003002c038241d00d040c550000c02a0500040207103040c07583d900503075404d6690071640c00071056602d00040017507042c64000c1c103030040d03005004502002c0c14240002e0484000528040100d206081c682040c0b152903400f00504503000fa80700c41c110326014030480c0c56031084010842c0011840040010310140c01c8030829161b40c0d0040c003504003181c40040d130b550707803483c480010344180e130703141e40005026510311032055400c065810186403071b8031544401403c40481804088103690042004001c0c002c132100da030741039091001e80905040d407020305041360b0944034110001d400528000c103200100c000000c02d0016240f00e0750f0303100f419070b80316006d21050f504804442c1614041d45181400500c0510110140a4036009008444d41d80d4441300c5160340b010a038840c2c000705a0302c2045900c00b0200d0b02445c485c6960542e040360040c28070b40d0740c0d0700c0e180d072583e90040d0503001d0a100b034420700714401d8038078001180c00200511003170702c00307455080c02036120614100444d450701c90000014100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 558976699 1250 558975449 558975457
    0xf090c011b02130f05090d02071a09090405120304080726040b1b070306020a122003070e12010e0f0109080f1303381b0c010603170d11 59
    0x100d00380e644201c14280e4244035102095154411000391110011000b03020180b25107032040c1d2044c0024036410703a103804068285101c44c2c00c81000d102c02401900c0081030a07004a6100ca10b0035503a00d0009d680d141003481c2011044030004050007400802e00040c4405a8041c00c4041d014280d03490400801c00070107190f071800d640070889800b07030a00003044420080c10180003260a03011002c030241203c00e0685090541c5500211001c030b50103d6903000e01d540c444100d8000304800e000c10041d0300b0341d403148070801048861a810303402800000140c07080d440703032201108191014045c1140410f05214003406010711075880b0341c0500c140840c0c0002c00c241405a0b02600e600300c0b03030151400e540108051034541c0203251020a4100b07a18000000600303009070150014071501903082c4001c03024140251080f941e001102c842035084041c0005c17000815440d2140400e07181016a6802205007041c0c058001c0383d00250200855a1007000d503205500c00502c41c042c0c00c210100705045c4150609025070003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 558977949 1250 558976699 558976727
    0x60f05030a20030a1b090e030c100c030609090606030210020a02090402041d060406050a0501150e09070e13021c0608120a090e01080a030e010813030804080d050f090c01 74
    0x486051008502c8804101802c4161000b4080d81c19113249901d070002c2020146002c0d4041c04035000041000c8000303441401c512032240d10242d0b09e00030008000ea907540001c0400002c5e000c2da900c2e040d8604a000c0e901080003045c006006002a01c101c1c14440001d000318071050303002d601c40906c040d43c45403002c41c0741c494183e401004406243c4468003400018191100302019411088102140c00e4208114441c0300c0d510a6102003038518044100300c0944606074452031030100d9080c0344480c040c0d04254004070b50305060321102015964405d08030392402e0b140c1095600880c3c07820030221049055001809061512009440030b4500c00d034204044540034401c460140c2c201c01100c01882150900514080c1441e1403d210180d48404d03680612007020380c4074041d55481034803184101500442100345150090801038100c0c030707000441100b28015107400404102d0340b10700140c00c22544409a900407180d400c41080f8619104090781d078030030300c16542622584038003466440e03e50b01c030f8002d10307070459 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 558979199 1250 558977949 558977963
    0x20a0212010c051c0b0d230304050d03050a180b09041d03070336031101080702060703110c190c0801061a070809191a09031c180603060f05030a 63
    0x40080f034091481281300b41540188503140c42a980e00f0356a0310008004450050030011050300c0301c61400d04014408415600c15600180400c015031313900d032440041c146405041480d9545241c1208890014008a0449014080b11004603603001001c02402c21032609580c200812100381484500b1100d00702d01c0c05580354400c000810003c0d218151220942c80309542c0014000c1440c0c600340d40d45450308104101ca10880c7c2410010b0240c503481c1100c81d49000e00341042c040c102008025100c0780014006401c7c5a2510304540801d589802140d140d0300707940003558000041c00e074250a80954128050ba2a0308070100301140110b81032003090202c4410304050440102e0a440c200b101e81c008800030340d81c001e0103000e84c0586440d80c0b11840040002d00301d036140c1d102d0415a0300c2803604845074142d807410805005111940d100041d0800b070360b40040c1c4548492004d0520700319030003040100303140720515000c0c0c0002511030b090b40000e810740d65895640401c158039042410740c1d80c400072070003130111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 558980449 1250 558979199 558979207
    0x80c0a030c2c010909031e0e100212030c0c0f1501030b070302090402030a090219050d080708130b130e04030807200d0c050105100303120c030209040c020a0212010c05 73
    0xa410b4840c011070b00844101c42c2d081d0868126021088261001d070701c02e20b80c05880e000860700305a48900059040041a0045010308900c0b540c0105041c61589000d130080400c01c0b001055180200b140354202ca5403505015500d1800c1100c4590607004240062118441c00303da012020001244282010780040d401d016540e2a503103c110180f84090851820305901704017030540c1e41c907180015485040d0000e8007140015162061000c1c200b240007a001b001043e440090140d507681c092070100c4541c0280e42a903d0b52010f04200b44688906208010490b01d40340340010b6011450703001e80903403003202403545615070740d8015400d10503004070303801400200200000381d1841d0090071185138481c09030390000000c20034a40010710340000c183c0490003103a0300d0681841007203c00d01810740c0c00b442c440b28513a0f18500e503a80c00b0701003001502685601e580c0314641c036042e5500c683c2c16a100403400601c284a00c2c00c2560b0003a45a40d04900d06a003da20400502003203400c05010304a903042c1c207940c481d454 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 558981699 1250 558980449 558980459
    0x2010e030132010b1c18060507120203090a2003011407081b040605070303060e0c1201050607030806010f17040308040219050a09020f2106090f01080309040209190b04080c0a030c 78
    0x5601c000c60f05e15a603586031501c400403880740425249100b1400090541881080a440e9a4011514100d520700410804c0041341c40860302c48a05a4003120011014140c2a0400c1d900540d18041c80d41544c81c00f16019100705011003480c0c013606040d01e50081584800b00f504a41040b030851101402000b0041008880c2c4580001c0c08400c0c045d15000942036104c83e408007140e402501c080848800228821420701c0d0318110480c0144811034100c0c3c038151503a600640440c0d0020196414080200a0401100e02030701c0082800c1503002030701c1141e0725161801038030030340040e40c06034081d02c00a1404040c04521b14014000d0b07900003401e0381c4001d0714015000f400381d230041c003a115603920140b29114000641e9030700c070800425001341800c614500101400500c480040103813042003001001009411004404c9a01091303090310090b07a211500c030041003d04602c040451220b1201d141c0c001201680d5030040d0003a1413484041d200d030b20800008000602000340005040c9410718481048 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 558982949 1250 558981699 558981727
    0x2101812020f1c051905031005030c0a0b1c020a0221160b060d17030105120a1e020a03120f02060603070501020c1207150903150513060902010e030132010b 68
    0x1038520600d113403403031400340c801e5681c04210b0342444081d004601c0c01b00c03e12604c035100c0583c1501810302a00100600b803c54400209040014412184c11000004080c0d039903081402e07001c04c5000000318155540c45684400940e0740240000d030804011600c100c001c0144210700c1111101103c89585903041c481d2600c40409a0300c002c1c00302c60f030062218000800054505a00e0058040100c81054680d03141409000b00e11000c0b03414800b0315040441c080d00010f0701803030700c02d0441a882118041d590a544003080000350f0070b0b0005084852001c0c0ca0f131b0f145950028144200d4035140d07084e1a059102c1e441459950369090258a01507085074030f0012107400c100064045110000d402c864403a6624000303090141842d15040c00015826041442402000d420110018103280c00802592a0180038140929401e0000504594542c0005015a8880d80e40c0700d03d4080000d008000500c03080941c4071240302c3ca5640c44003800c424001c1c0080e003107102100f0a0480d076414000e5850322148a40440c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 558984199 1250 558982949 558982993
    0x30b04020f18040627030e0306100810020903031e031005040c021b041d0307050d1713050f07180501050604030f030503220b0f090105090706050a02101812020f 70
    0x1900303072070800c405d0300d05200d901c00c08200518000c2d140d45480700c0020051508160b002407100c200c603000040d0811898100003043d0845801800380180c075100c0703160010303003544079002031101c1d45401c0c0b103000e09440480744021406211005c000020050b6a041407209a1351841104005600705004042010102040c0c8a90004008000140403090840b200310b05041f00c0740c04014a03030001c1440d2041042c10440c501a10382c8508201210141c1d0300120309a0750f074018440c15403030181c098507004004040048054000c10741003074980c0a916244801d50f8580f01c01807010300d03941814000241420520112410f40b904002c000a0610994506583e04c0d0300181428085446074814201c00c0000b401080b10101d21130900d00103039080c4150404a50400034107000e009902d86014060008000550217085078500c1c1001511518800016810a410a1030141c1c204c0c0c02c00210754907a49079030441510107449030581c5141c005514208030b03502d40310070b003951009600c4907840d100d1b1126402088 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 558985449 1250 558984199 558984221
    0xa2003010b0d060306020c07060224180f070806070e010e03060604091e1b082d0f0f030c060106090e010b03040807122a080403060f02090a030b04020f180406 69
    0x2080d0f40b6640d9451038101e0340500034030505a000f9402c18880668140050343d5a13500084180300b4100c2c0c0340110492040003d031003004000b855801e511501c24083c001202c01a03a400c0683e510b8aa8408109444030b500f11402000100070042002c041c2d03000d80c81340401c101000d4001c0640b80d40304418440107009a1009981200000c0d40c5103212030301030840100e10511410580b20b0806054115000940a070b40062025802003a44107400d24021007030b082000811010b105000e4400100013810404080c2454443e802100d00d52250050700100400580d44110b00315140c0e60790300c02044404003010b0140b04101c03228400100304150000000d1a080390040c0600b82c90306003207030345a4070a401001070150120302d1009241003c11281404d00c1c0f000a412129070080400c55070315944281b06a000c000e068580e5103040080420003a419202c08400180c00324280710b4480c01e002d801404110b608901c5102644d2800b011130070101c0359151144510500000c4e140c50b1650388401601a82200c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 558986699 1250 558985449 558985451
    0x15030b03030f120c0a0c060b01120908030108070b0a02060c07290609010503010506030a1b030b24040207030507080919090906200403021005040e040b0a2003010b0d 72
    0x850010303039024001031101c1076100c0e01c2c150b62908040340900302c1010042588013140028888100c080740c0200310010469400704d8002501c850800c01a0360f608441c03e0311059803031800c007801c0100821031300152305850b415821503140603650b00c5030320503c2c4200b4079164016000100404e480000581c0a004081d200d0458000308510010303200301005400070103c3d441042440610000d030030716024041c05001c060700284158508640130070341e94015008007c18035010801525804d00c0c2e00c01c80c9801866101c00103013403031300744640d540e00c0480c44c45e581d40000340381300210f1140e00d18007031080b00e0031242e00d40c540d58240a5a03455144058210100300c1e0740041c0207074840300a84045401d900081c0843d000b002a828400c3d0400d5011100c4d10360944a460010034407040346080301801340c070112a41116505110250b0364002c5905004c3c1789c0c014000c954408060100700915115100e12541e8010410880040010100c10100107440300800c102d000030001840a44042001481084841c0304 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 558987949 1250 558986699 558986711
    0x70c1203090918060f0501150e0316060201090213150e090309040603060e010b01020705131508010c170f0403120b0105040f1706010e01080c010305070e040212010810020a05041503 79
    0xd000b000d6030410b14101640c049540e8042c3c0030000c15104070180c121081d1020441340d8146084000c1c994043c0403004148201868640d2036554200803007018070741a4110040443e40d10000030340a80350700f04049114090400c81d103580319615111740b0210114031110202038500d0b240d40e450a07140090580c0b0700034041000440c0b2640c685018050055102c0c000000b01d46a004507218216001411401e04541089004000d15076402c0760754405043c94403000076481120b00b0841111503202d5110400079402c2449051119811420184035243c01390524100b0b60b41f0702205009040301103034014017203464240d140c11003450364bc2c003e84021006040080c83d01c0c4c0c0b59210700d405582664024421503000001d98100781c04180000c03401001200c00010465051003405504e41841400d11410540d807100040c05642c451000300080c444040e104640d24501c44094210047c1c0900074101c80d80f04854008240340c65034404c503002c100c4550b48a40c1414101031119082a2908602c5e0040540b654 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 558989199 1250 558987949 558987959
    0x610180f0e060901050a06081e0102090a060c0c051005070b041b170c060f070602070519060f060e0603030d051b0301061701060f0807032004060c02090c070c120309 72
    0x44141c03510401d40500500880c5416a9100d0075910010b100c161480e091407001c0180b0180001c00c45540810004075803400c00700c00c04000d00900601186980c4003040010025507550840300b00d054041c054071000458589800500084080085800e000070302d04100c81b4011541c00784c80140c0041c4601045150140d4000540401044541044035695182030100c074140070b0410a98540160a589007400c00c0c058000b82c0d540c502a0300310140071590002036510800000307002c8112419400c0c4ae42c0c10070801c480c00c1400c010500c038200315842c140390100c040b40441c01083c00611800b0000c0c000c6280840f003010200291201601203007880317440000300c41020008401540c041c0c1119503500710540c00342e11030201c2c20744040e0300003000d0001c1490b1301c2660503840384101d68001039a06002c07400076014102d01c030500c12102c508800000010401040d115400305003a41c615008444400164a80000c290001c2c890304a004060b69940501008090f4490089865503402403c0084080d5652 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 558990449 1250 558989199 558989201
    0xa08010c050d0f060602060f0711010c0e090f24010c080d020307021204030201170705160b01050a1403190302100e1c02030c0d120b040f14090610180f 66
    0x3100224085400410107602c4041540702d42e4204040c0c0003000d021561418002940b00d45014080c20141e04105e800a4030650041c00409000d1552100811030200c0c0300b48d00030540a1354103182d61052100e00080707505d8403c2c0145541c01092198000611070401c40d001030b264043c05410641400507040b404800308280001070711000828401c0540d680c0340a5600a081580d40000141441d00900c41840540d034406844070f000180000600815260f00c01c0079551409035481540320343c0300b01d046500804c00c440c0b04581c102d0b8010740e5107094089d21030000c56000c00d62a50219015071201c0c07908041d2251112a8951550003401514010107012070410195402d180f115074042d401200000c404078828290f0740e8440c4241d00c0a181006030040324180c403010b08150843c1048110b9160103d860810351100e103080400a000300b21800c0c04922000c09024603144000c0034050010001e0712201c00418000c1c81203079040203a0510034182103004001b0148a803031070802c3c943e0b4003070b2034480d8866 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 558991699 1250 558990449 558990461
    0xb0a030602030109050c041401230706091b06020c0f010903140c100e03030a031e020703080a060b040e0109020f04030c0b09100912030c0f1e050c01080106080105010302090a0801 78
    0xe0103000d6079940c10480c2d0442990000360010550606c01c0008000b600c3d1111003840600ba001d2070b24020070806585409001811400d030302d18100d070009101e0b400c111070b80d444270028a01c190115407010102405108850301544240001768011501644040c600103007200b084160504084550940300e403a03501620490b05c80c5410701d948001d64000aa02e0228800302c041062803604c405004030300f0000c69228040c00c8c1c109010f0540740c0b18000740c4601e031111048222500684215225503007130400034040d041c142c0760b0700b02051420001041141c2e800d41150240c1e2203601070780c09207919042d03044009600c81c5030032154400e0300380000300001380400045402070604603240d640340c070ba6138400c00440c13204842140080c0510788008011603041586107180a03501130800301c8600101d8140700000340e580300d034001c000c1c00e803840d180e491040f071072100300004a00a0084030403241c04540103480b038030002e004010104001100410142d8844d80041090b100f01424803141e03141d49451007402d44030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 558992805 1106 558991699 558991703
    0x10f06051c0902060d1401080303161d06040f0618051012151d0a09050c04090f12030b010e03070312053711060f18010b0a03 55
    0x300551045100b140c01504041c0c2ea074000c1054140100b07145035816082c44440000402c0101000068a218808907610b410036850480e50649d039051102a001c1e034800c0304001c2d031007003a480700c0025000402181d440502a14201100a02106810482d40791801002c050805c6181c0d034280c07060f000c91526043c0400321028a244c1c04020301442ca14440c02d022003100001130308140312003640f00680d0010043c03030960b100c466084099034204c00c40500076274000580441d4620b0903900c0250214071512281805070b285a941484103103118103c0c41c0441e17030341c204c2101c155810030f000c105903100440c080d10780142541e8651581c51290306c0201e0802c40e010131904091403a084a05024050a80e03583c4055000c00f41c202003110b040a0200000800e1031407900881480080c006009414007840d84415640381c140c00400d20000c00700ca001d041d901c44400d120151100986000698 = true := by decide +kernel

theorem cover : BRFrame.Cov 558812949 558992805 := by
  have h0 := BRFrame.cov_init 558812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 558812949 ≤ n) (h2 : n < 558992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
