-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0226
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:34:50.28988+00:00
-- url     : https://prove2.me/submissions/e9371f62-bc42-41d2-a571-42e62626be22

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 40467630 ≤ n < 40647486 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 40468880 1250 40467630 40467643
    0xc06091603050d030203090c09180c0102031213050a06060905060108060f090105060f1c02031e01030521070506150f060705151503030a03090309090501060f0f0509030a0c08 76
    0x1000404041401c2000c500c001c15041d02503156030a0140c2e07240e40c1d0381b05140c28444000e0819a20100d400709000d11860a458140d050b011040100d0380c080c803ea0300103913500c0c000d100184001500300d00000b98843c4055400c114410720030307403c88100d40507c0ea62802501e4850708400e60341c0d6510000c10109683c0844140c1e01320b44240c0b41c03d40c08001e0000414100130050042c94011000081e0101d4000e00d1802240c0321503050100328000998442c0c0b2030700c0171b0352003582c2c190701440d1440d402c9c020080d08902c9060489074400003d00990000341c4181e01c020815078103aa0b0352141c280610004500b040c030040e803003000b100311941c09807170ba12020881311460540786a0b0040c0420302000c400a40c0000d442d40542400301040300050fa40d0303030040c103500010420300d99058003010490452082e0150040301000d0700c2900e421050b0342d110450601100c400b4460034000403078907150100e603613015001c2c5010404041c9000c40c03a0240c0a0003207403a0200317201003141c0401100744100038400040c81207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 40470130 1250 40468880 40468903
    0x2270708040308040b0903041509090606030e0601030b060415090e06010806090c0904050109021504032901060f0c050d05090a0e10180605090a0f0b010e09150409080c0609 75
    0x1055030381c100394900501800b00204010008000b040c0441e850f410700300141c4008100540e1125003145004800805000346403041b20411401c220300420041d000c0d004003408511004000c0003240e103140ca5001c00000302400301c0d03030030a56503203a00c9084000348820340e0160610120108111160300031951070054140e02060440e0802400d0002c100804914049002c400721400e444507103990a2031401000b074688000d42c0324025513803084040c98403070013801c04c41c1e0080741014100301e06001900500c4400c9281020124058030040c400329009403101641c0e00c0240c40d000c10b80512a80e60741e840c1c00401009080403800c0440c511401d860901e100b1005000402071072007913400d2460454030801d505000d0a402200203070701824450403103030301040043c0740c018081c00036800c140c1580d000500b001030840102600b065000402d5500410220b1410000501841b21a13503a0308030300381401104102c6141c7c000e40360071280c0082000500030704490b00003640a01110b041c05040c5a140400c060803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 40471380 1250 40470130 40470137
    0x91e0501020f011424060304060b0a060f0903080d0f0906050a0e030910050a140d050103031b0b0a050a15030b0901050105030a0305040504051b07110301060503070b0409020901020a022707 82
    0x3050544150013000358003c260000911000b40c038a035002250038024201c01a0821008802c2000f8000c0ba908529008042500c4104e00640c580e0006c4400007210818640894110002007000480c81402018815460000043c01c0080080180180e03201200207880740c580328420300c0303400060742c8550120a20500011403401c41d00101140300c2602642901c0c0c24444007243c10b05080e03009240002502902100c1613641700000e1040c50010700083c0000d40c0011a41d8200720502e9454214042d01c5c60317044490b80d60b10359181072224015020041540c0300c40e40c3c5070208140d40c0240d2000d01c0010318490580d10f600c0340ba100316294211407050b0702c02d0340300380d0108804070f01081d0844101d5055a109a501245030b5075102c0d42001c1203003c0848440d00310300006240400d0115820f034000c0c10034402c8009014440c0c4c0c034001c05a481925008003882031804100401c40080035500424403860103005540f502e9519400003411120140500801d0907001034021050b90651241c0c47c1c0d000b90f6506 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 40472630 1250 40471380 40471391
    0x60d0f050a050c0117061005090d03030c0e012f01020c0106030309050f0609181509041505010b0301061b050f03030f0f09071203030e0f0609012007020607020907091e0501020f01 78
    0x1400001c5c1c00d80d01078515809442d0000e036114089200fa811554218400381000c2440380b1039140003002007403140780040000b0704004080241c1d41c401c405417465410b40081ca11010307601209006024180112070920a6508004078080e510080c02110000c2d03020f521001440c6240806025016542c91000f80c81000100191885070355042c00340c1410034049007002559690b04590703041c840c40c110250316488210402007100700482c041540329051070041c02400b040c0d0b038501420000740000e00a400104214060b8041030407608285002c040d80201d0464010081d42201d0b14155403040c4c40d03005100d1642c20400c046a088040781e1900480c0400041c0a403071701d001c503025603038900c00900804054503400c14821825042054a05000b400780640e0b606090180710356000701245060040c5106079510140207843c09241521080e60f000b8141c5450083c05608002c2c078402c0041c500da0603c640300c080400d0101540315450525007864401d8850305d4209000640745c03075001320042d480c9a0601 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 40473880 1250 40472630 40472657
    0x6040606020a0b0712060906050f0316050d0501020409051f0602030a171905090c030c04060305031b0f01050106090306061e0b090103090503030a0c080f01081203060d0f050a050c01 79
    0xc10034150b64216040d88925200c0100440310300704001d140f05c1c1c0f06410008007117160086030780008202d600c101d503c1030701100b4401c103158031840c04140032420703c440307008208594103104401c48040b07031082c0001413506440302c00880c12140241c2d820341603100800d4854904007c40d80c6914007602450009504280e9580301c010056130020340c1d0002d91031446000700d0980126554114420904000d05105500c2c25091059881d010400014420720595400070307868281b44c86040182c2c0e4011000e149423a40303440c00d1841080e1144607c8042e4072034843c002da143c620030300c0b0b114081c1082d40d0700d843c440751840c144501501d4440e00030b21030003c210010410746003c02c0307845070101c400b660410703a220715205005070010640301c41c001e4102d0000100f0060400e10f40e501c010703c04811500e8500607500c81d420450f640c010b00340900708550340203510a415540c005005554020402814040071112540d107003800c4082800088460343c6c01840400c0401105004034086c2c881d0078605031183c11000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 40475130 1250 40473880 40473883
    0x601080c0f0d0b040e0c040609021e0310030507030507030201080a050c07022b0303020301170703051203040c0512010203091e070509041109090a0303110708040302013b01080604060602 81
    0x4840064204403000101c441c05a40b10360000c924064000f00304016040d80040300f2030311400d000d000700344200c1c80c107030010030303040302a10071b44405503100d102c1d40d50b07501074411514600364400740051000748000080000001e030100025405584034602030f040c081d16500c00035051b40c0002d05405603490809041001120450003a1a4003540485070482d1540802036180c80c01c3d13403c0203904680414090300d28003850b0301500207604813846614a02c070084817056507140c8881240c04001c08a030000c217904e12010081c0c030091908180a01311004245580b0360000d1461044c0c0d0080d1181a5000300400c954030380240300c0d1090b00e201a1003e00040c961500c6800e4032105540103081c402c0350f56101040a003c1c417107203800c41c0c1e11030240c0030b040c7d0b40c01e00c124240d540340118142100001c0c10110040d003441600400d440e241030744108401c0c102800c0d0b90040d144402800d0704d1044400039010188482d8015102012120349074610a16031445c1400004040b6600204a035001e641451801c100d200d50 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 40476380 1250 40475130 40475137
    0x211504021f020f2406190807080307050c03030408070b0d020405060a120b040902030606100314040c030b0903120402040504050307050a110103110403080a1808010608011a090402030d03180602031008060601080c 92
    0x101121481000702e186e00004007890019040135502d442403400200e01502d00000510809008030201c8801090b000105aaa032099015404032a048144100001c00091014200c01100c059001d42025121000310f90720350410140c010014484a40038020711144d4410010341130030507103050200070541d130082942c4210142200d8000c440d41a0b0425216119502c141412040c66100c40d0044c10541411006040603000a40d0b00e1150701300440c140741e81c00011210180f4001311090500e0341d80f83c08101c001c240091094130140030400c00c560010b401030041441d012702c541902000400749a0005048884e80d9100e20303103140040100344081488070043e900440201e00d0624002803040d0340994a20303c582e0320000140d800c3c10740100d01c041c0190009024500308198401940340031070208125544159030282d0035070000011008220720a400020210b01c2140c01a9450111075039000100d0b0b00840e01e1240e107035026202032040940034011240c10420910f829101410402d203452140e11 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 40477630 1250 40476380 40476391
    0x1c05060303070b06130609090c150801060801031b090f1e09110f040605090405010e06070509061c2004080d03090803010e070c02060408010b211504021f020f24 70
    0x3e48004071703810b41201508100301401c031480050280c0219071401c0c03801d1008500403045001045411400740314824030010703040b1040c1d90745401a992940d112001c100d00ca8004110000c15940404200d42e046802109141612410002100d043da003100300c61426031441c0ca1129241014000742c089080030a100d80030480403a00b12450401c0240000e0003000b03030340e000075040314401c0108000c1c0401940280ca0603e00201070758003903990108102e0b100d01c80c5010035544213000303201d42400001c5a15400040030324242c8001031040b6819040744a01c0f240407907107220100000341c140a0f10a041c0704078409856203080c14001045c151307407400514003050003044401000308001884003486882d503440e400b50080c004070359580c1c81e0841c0b14041d0031180c40e49805400740d0901458500c500741490b078081d8011401620131610392020f019801c110281c03003640d029001c6841c0013040c50340200c29154024140d0014a21001d6407448507081005158190b5104104c0c1071680121036040a0480e9108 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 40478880 1250 40477630 40477639
    0x8032409070c0222090f060b031204060804060f021c060503030f041509030f03090302120606032802100c03171302090717040309170610090b01020a06021c05060303070b06 75
    0x210144040300f03440c1c07481001140b0b044c60604028000b0300c01c403104140042070142a003880305c14007a4007410340d0f5a2048000c5c19191a040208000c2e06105860458115200d0300d00030542d031142405c0241660031591001010b621009040f10074421203204000042505402540c02c004604204842a01640c890030140e402b00e01c8001300390a02c136414500266600a40705950480641401171810b00740d40412406072480681260329000005035003403044100800811303902580b0804c0c00212a000c403080444074812660074030041e9078880b41c0c107130720400c6661200d24200e043c0c00c006103021410b20003142140200002e10101007808082c05e440e0301d4040e0b402c0c060f40d1b254030004a03581c40e03001c0b43c24510070310180b0a0100b0550b000e03d1400890b092030b51401c0e8519008885507884c0c4c14292650300b1381c00c050320002c00c820f1116802c85940c612050040e109810300079204c900590b03004a01060003038540b0109456402c145108050f008007003034004505040c0c6a070f481401050000d042c06105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 40480130 1250 40478880 40478899
    0x100306050618130903050415020f0a03111f0c0905010507030c0f171801030b0402090f10020a0b070509040f060303020c0d020a1703120f040f030f050708032409070c02 73
    0xd81c07214420319a1403840700b50f080100c1c009604006150303070454020000c050381c40c40302da8211140700003441e5102d030403540e000c0c040c003050980c0c080c1c800502c00c001c001340502403400c407040760b003103d4070800d00f00061521020a00c1c5440e40d4008094202640049040c400148100004030b40d0261504044c0c65022000e890083c03110b0030040c00e08102c400c20220b801c140050030b10f8045c02015500c0076100300a0b02d06002560a01040005078010322031090380081030300f02c000c2d030b003482d000149a1104440d40142ca00d400307001c0e103540f8101182150f5038000300c2c0303000820320350724285407240f40090350342810100510360465400079150880c0840f078920031560034034000155a20070321048010b0110100e119a08043c40311380c02d441e500180914841c859140b80060b42c0b01c040509200c0c45998030560700104008550b80c01c0d83d201d01c40301009000c0010074059803000070036013801180205a40045404814400d8001c0000c1440275103101c0e006000398428001d4003a0044110100d40d54101c42d600b01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 40481380 1250 40480130 40480177
    0xf0307030305070203280609240c030b040501050f210d0903030e0d1515081603030212040506030103031b02060409060e060406030b07050a0c1707020109080105040c0509070e030604050c1003060506 86
    0x107100340ca0080149d145103466000500b214040d0f02c00b12140c8032030b460910006903560100000c0329024450242c20540f5500d09440900e0070303104810100d941c40c40d140c6481c4940301c03502880d00c220b861074500031441c0e045092092582000003880300340c0c000c460828050882e9651512240740d040c0551070410380b501203610340e0f500191080030240501ea0121040040c9441c000c0044007450310060b4098020414146c3d900c40c80f8500300c070140c81020301498030b140d02e03690701118000b01107e5411550301c5180d11040041e90382000420091940c82070214285003080346a0408203c0500120301c62494490100009190700c07040651248950a0a60303d40048070002d50300c442c50210f00a040031140d842e00d03171403020070102814066000fa40d0f460326140d1213626903800c07501c0c1558090402c124100e0100726924191000381d9020392540307080140342030040046071030a80305650455880c0c022800080d4141443e112160586d05e0500e02032042501e0900440e030588a52000b002a2a030461031005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 40482630 1250 40481380 40481393
    0x703050f07020d0506070201020315090112110303040306020f030105040e16030b07200304082107060906020f03090c03010c020a030914010203041d0702070b030105010f030b0f0307030305070203280609 88
    0x20b206a005005e40b07a141c0b51900e8024003c0d0300407500b2000c500709070340305044503050038400b403410380d840d4a1200c28801225280c0b01024403243c107015502d440100008000550580043c28400c60700d8030f6002c1d00ca5040c0410001940d08108901c1d0850780700f4010700e0b0410f56000850021660414000300c4e007502d0302481280c4103d2881104408402c040c40f40b000401e8000000300b0031120501b0030358440c1200c0400404440503542d10312150120305100c91804121a5400311139058850301d401854413145c90714120494000b00d41d064055000707048020020f090a001d604000b8031a407000e01401842a90003505000941c02089500c0c00c0c4074298050b581d000300202c1d0080d0400400013000c500c00039401e0412854219074840060181c044002600a2002d09070380c185c1d0720507150128001841403046004001004002e98007520300c01b10211a40c80a0003102e0155029598180e5035102a0044c14030f020224918014100b00e440c03207042c5a000c0002d60140c040b83e0065020600c1e11180c140070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 40483880 1250 40482630 40482649
    0x91802090604110c150606120a0203150a080105060103060611071809050f0d0207050108011a07020a05120a1403040608010b0705030405090106080603060702070510051c021317030703050f0702 84
    0x21403c1d9a000104000b110300c0029441117002c1c4c2c08150321002d9550b000034080180280b22000796503410720004141c440d9510307005140d0211141d100b50714099031000020307800b1000741d841440d5030795449041c0701003540d2600840000d4a41f40c203140441c8286101c3ca0340c3e50700c050384941094210000b0b0070399071100c0d45410003228240c00c84101d07803002200c440760325240d440b04600e00d00036100305840010154017608141341252000c0d4464101ca16403200c400d15540c1c0040c0003241d210300105408a090f694068040214000381402000d00d00d0092401640d2030701502d848401b03d43c000d000c100b20203a800583c090540340f20001d441e4451000c0d251070780c610300454215651000100c1c001080329580540d8651017120101c0840303150382c0b14000301383d881d4515802070903001105ca040605100b801f540041c07800300004298a150035445100d400101c0e0000d4205820201032079104008061810f5040f0320f030101d410b00654a4103007141d802805c64403c04080e00d42c0d9041c0860510190754504155 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 40485130 1250 40483880 40483901
    0x2010e040b04180503040e160e0d080903010501030311010f1a01140c010603080a120207030905010509030708120a1404120b0a0b0409050c0108010f0305060402130e0304030c03050601091802090604 86
    0x440f080741c8441c0341c65601e83d0040d004000c1c0e40c0c0c800c1c100094606d5500350b40b2443c0d203485500d90b050503540036014400c6400240c003054031840c0c01042803d04e10f841c04d100b070600840c02990b402c41005600c011181c290b038511000d011069042544401d040300d03801500100121090900c5009504030707840500c018020380c01f02480a500e01100002031064800c005e0044d51784540d2011884402c44d40d1800403405046400f80009034034100900655000704000c0040303000040880e03400640d03030181e944c40c0c00c0410000b04c0c4100030102d40314084503080f0b200c0c0c3e0508010f03a40702d1810242890b4800343d080440740009041001024081030b010f848a03408035110f139001510038051189035040036607580095000050000d0180d0000160b00011080001c003542e51050140c56207455907000c1045409808040071580d40d0f1340c0b0f9100d400454200003c100031171140700083c04580c614207105041c441e05a00030107000b42041d407813404251500d4818000e03168121740002058803800301040042480900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 40486380 1250 40485130 40485161
    0x7031503050307030e060c030711040e0115030b0f0403020607080403050d0c2304081011160c0602010e0c0a060507050f060109060512010b0d080714030d0911030a02010e040b04 77
    0x804010301c1030210081010702d0094460314071282c01c2c002404020f2048003013031840707504188507410000e40c042c0c1a00300d103004010004140c803010001210b0031607034842d868001d0110142400c1080007004002540d00c45c0c403000f800c0c0b80a00d0140c41c081d40729080149a0010040d2003000101014040d1090ba0070580c2011000c01c8070f15050300340500041c8000100806038410110700402c014241700850f0151410107010b00260b6007444c01c02000f40496102d10740104c01c06008402e04d0f07503483d900440714140242c292003112860b26402034210341c15580203005681040d60a2503031501c400d00210304035449850300c01d40d602c0b00f6060807410120700c051741c0c501d00d0188000004508000340c011a0503103904543c1e14000e0102d0168250890310310020f10b6400c1040400408089120b500281030001e014100341110388500f443e1441c1558004a89480d410755200050002c0c0441e0785021807913920305400800c0c0158890b00080c2556845d01c1540784580d0710b520782c004a07070311143c1000c8840d210110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 40487630 1250 40486380 40486421
    0x6050f03070e070c1205090f030a050319030905030c060f0f01060c030804060f050702010203060406080f0c01050702130507021615090506031e04060906110403080301090908040e040b0f010b0405060d050703 90
    0x8030050580d400340101f54842d03003031300490310224900850004506980712004501e8488045556030686401804440505a45400b490b000c580b050000f0802c1411660240c800c0349040300c0c1c6850200005050000f000410300010b20541741c20180386085142c150901410300d41d510720340040030304084a15202e280382480148602c6070303015005940902000c0314280542625171308419550b500104103c00c8980c88014404e42c0d65005000415045001400303000300b88503290920400c2d15402e840480050340202c03101a80642840c4420001e41814400d4032001075850b00010100915401110b2058000202049901400640c110300103000309221030181d02e41030801d000140250b0704182c0d003003820400c07040303955143d400445080d00d80c001d200504503401d01a044000703000c081001c07902c6110400010801d2004144804c1c412807244614220781c0c68001c180864404c01a400084860340c2884144031a546400568881c0d1459003c0004d59507924041140540741c1280f9040388402141c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 40488880 1250 40487630 40487663
    0x4060b040f0c11030a2106120f0b15100e03010e010c020309121204060e0103090804141203040815061f020d0305070513050904050a0605010803040906050f03070e070c 73
    0x9802a030b0303002040d5110001150b8031200659102e10480c2000000030b40000070404004007540d20170244042414000104181c07201c0c040316246102c046c2c2600c0c0110510141000c001d205440e82e42d2000a0000219006900c0004508480c0d2003052880c103212010701d10b0450760300c0941c0841c40d00000c000007800048003860303001c0d45a82c40640300500550958021074000390b40040e0003d240204400c03614035051405c1d000311560b80e10503c41604040d1280303410320100d186071014001800c030442403105030501801c2041040250103c801d80317075810600c000c2101603000f1890740840d0715040410f082c42c0e50390360005440701d421080040d02c03100326400b10080305940054904000c90b010b840c01c2020384c1790250b00f80d806003e40d60390f03641c0c2c00c03e550f4420301c164140400c0c03d90300140b20720b0455050000c41d0f030760903080da0002d800c0040650700208040082c40c54a000e030400500c07041e034031041d5081c1442e011031340709c140318041e07c0c4a0301d0041010603041c41c461066102d81075040040e00924580c40e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 40490130 1250 40488880 40488911
    0x210206130602060609010501020a0b0c0f31030209060d05070b0c03030708010906120f0302101d0706030b06120c121017030a0918020405190e010b0304051504060b04 72
    0x89000e4500144a100002449810b0141709241601c40507002402c1d20005a6a50300f41d042c03000302081e144810600510200704140b1000e013042c0b003110300e01c5940301d074054808170050800600c0402c90a40b051141000035031a20b95840b81c0000b82036544100c90800c0342002842c0101c02e034031183c0710f0000090030603070900005c330240d4001c0d6010340d01c0306100d90781e542c079a4050b02c8140c01a111034052100d0b1040c0001c00306c6100d00c58091090043e04c400051100344041100c02d200040c0750302e0019000a40c000f00014020200540714a0904102a62000d804600d26004118520500b009904045048404e841c000c2c1c800d4140801e001034014036020724407507940b000c20b102e52200b41d0855142640c00020120a03aa10f20030555500c90000340f034420358240c5ca00d42e0210703040d182e5900704004a440d0700c80403511003d074582c40344000d00440c50000c29440b80c5005901c0f80c00703207610178014007000440124005112000d416000d10964690b410008002e04034000080d80c40b44c501403105045102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 40491380 1250 40490130 40490167
    0xb0607170306010e030d0e04021614060106180609140402090a0b07050601060503010810050a06050d05070e070302030c04141507150e0303060a05090c0705070b0c0c041104210206 78
    0x7030f650134103000922001e150351245c503010104003040c1050801d100300e007016800390404500717074204295212174648030b4034842025044512455002000103101560300800d03d0110700180314910310845182010040c1400c3c014003900c01440000e14000c111a0b403103406682d00440024080700f202640c483c07002050741e2001c4802c81b240d004880000030300600a00c01c0e00e040300d510034003508584280200c42401068020000f05e00c00341d5801010034107481c1d00903940540c600c0390004040c018109070110060700d100503e96410180108104080328500d6016102200c03805003603048251034000c00030b8903c0e840d2205041d000c1101090010920440c400f42c0c070001c40038242c00b040901c0800c2d1016459100440740190030038103041d410460703070801c1c0a58681c441000d0a50508200382680c8603814004640c0c06914001030118200644420600107203c141e034040f6010007403e0800901c03400d4500442c4103805814402e040b03600002c2a50400415000358010178a40c1d6862044810070744050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 40492630 1250 40491380 40491391
    0x30201060501030c08010e04050f0106060507020405130f08070507090903051b0a030801120203120a03090b0f01180f1803030203100b0301180207031106040b06011103031501030b06071703 82
    0x1800c0190000300c55000784500004c0300340e00e980d80c0b2280c0c1e0900e0140105208098822a1144245d92030515018420304c03449001d828036a590540d00c20705ca0042005586c0d002e048410700300d481c0d03901c1c2c0000602c2d004070141940da10005030354480049041031402c00703050b07900c2400441d040451b00010550f20000a1000b40c00c2039100000100d421402035076034030a1100002d000c101c40c580140009a54120514159403000b8101e40d070769001c0c0484002c060b00300780c5010b07002c0b030f40301d4804008000c071170000250701c00b500740c160404c02d614040c00001200102c6540c000810380e40c0c0c0c4107240040150f000f01035071a2584000310150034451600400030f50040762140301a4418000119070580000c7c201e904807000800084540b15414001390004d5200840c11003d00602c0e4103c0c081008003801000d00c26401628507919500e880340c00504901d0f801032041c8020b405c00c2040181c1d1403200381c0c040391030351400c0c40c0000e0403038610310100751184115076000c6c20741a201c0b4044446542000000c0d4400c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 40493880 1250 40492630 40492633
    0x1110109240203060a0504020d02070f0804090501080609120a09120c060e030f03190207030b0c13120206031501090b0c0601090b15030106050a03060e0103050307120809150c0c06130302 81
    0x80c0740a1000104a0005071034041c0d102c200c00c0000c220ba4039058016090f0102105001860300b031340d55892101602807a80c0441d225440424100402c0c8024440d1600400303907100540510f26280841c0b913100c00170340c25081e40c84130700441c050707120511411a507006004003440f080310310310003030a0465088499126601c0004d080c0301c50840c250801051340041307801448001c5040032210020381010401c039840f4003003188130380c600000200e4804008035000d460f45480c503e03078420860340c0300a07a024841d004103010150803c1c0c030000607103a2004403a0f025840e190040d44032250200100c46800d1b596000003180d030750101e19400b26010200e805812595850000c10001381d54109004c2c149680907844c01b5041d20600041202030b01030002020400741902d00011078648680d0050038640d001c0c1c0050381c40d43e1001c9401c10800640c800d0801e694183e90400c402d89281040c2c5041e5160076810860999140700000700b000c81c441d120640b00c0c0c480c18941643c3c010316100000c061304103c04074003603006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 40495130 1250 40493880 40493933
    0x10308121006050405090421110705030a03050405130912020d08150a0e0703020d020706050405010b0a0e01090b010c020604081c090b030106050c1005070201020913062301110109 78
    0x1886070541403002240c01c2c54483d1814149000104400190020810b40d243c1040798035450700003640319069040000192070300305405404162081c40d03d82560071040c001d51144003a0804a0740240c20386040b40c400321501410102121103c80203000300700d1000b8813944c00b2a0b0884070540d000700314440e4100c0507640e500e4644e900c41c642e148505440a050541180d64403000f0320070506628050f80c0d200109050251070010f01210b001c00303c0c0d02c250400d8403034542d0340092104026080c06240d90b40b0700101d0346184920b0a100303640950203418070402008960300c0300709440c03503402000c0b0350845603001440240c48a0740c07000c1481d00c6d141c403101c032082d05c441c00f400780700c06003402941440140e50b140200b06003035a003482825540c41d4015001d5400600c10710008080085460203140c2c4030b0040345d8000340e2182c613501c00344002e111300c01050088541c24120f06102c0522280c40d08401990303140382c850310300504080141c445001502440002c1c0d4200030006c420300c01d90003110b04c4208484007103840c1c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 40496380 1250 40495130 40495141
    0xb09100305010b0d090f0b010e01031101030c0207061115040602070501110705030703030b01050d0507021006060c03080604050a0b0a06050c0c0d120f0504180504060e0d020303040605040c050901030812 88
    0x40394401d004400307019000f0f020500020040c1c0d8404811180b04406c900300840341074848100800e401d034881c040c0c4001302001441040f2812a081000300d0003820f05000c0c0c95807824000c0d442e1541c038002c0c5c0081000c41216140805801c1182034005108a0701580c014105410170002960000d40306440d03940c20085101603200f002d104686072143c00030007841c20030f4019070b8114060516544240d04200341800410000c0e10355218041c01b0320500d8004003d820705035510b0030709603202c0e90302000c248100c001e401004aa041108240e12140071100041e10740e90300a804c81c001c005140f210b40e0045402d900104d440d0742c00000a11510705e50204030791a10b181c00041002400490038003e0042c0c0c40e400000009a0042c5226400d030700c070314140581801d0312505d00b43c1500a0303c01d201e080030303502c070300501003440014441c122080d008000a4900e101c801d1001035668800640000e14041d0384100007001d02a802250401801c8000c22000882d6524180060644c0200c0e03003180000d4440008143d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 40497630 1250 40496380 40496387
    0x140408030c0c090106090b030601120f150e010f0b160503070507090501210201110114151503070f0c0f0501020a0903060e0105090606010c0203030d05040503030108121216030f060b0910 81
    0x5041791070a90b80c0c0c516050402090f030303d1541001c0d01442c10300c450401e541015400314062180044002e14000844800d41c00102c1c011000d540e0003422440c2148006120007400392080c070b402e80d600200d00a1340d8030f90b0b0414061500408400142c094003011403d14208100030515104440c11160107001903600c0f9481c0f0a02c104111400d52a03e00086441c100154041c840b00ca411500000000411405580040010b05002c0710b1990700e040e80c040440c0f266103402c41440f082d054030000414114a8864805030640301038680781c006004100fa98201000382031711150342265031040082d074070b401c0b41410161000b0124002210013034281440080807800c1407040500c104a0407005050301d4403610010744203050b0485007030381c041c003040011902250b0070303001c1c5074002c1e48202c0007195250b15180c00c003400c02c20b107100c3e1400751080c10850000070030400c0d1483d41d04007005401142039034469203070a031f0003041c40134030f02185c141c104200001c5c0015480007404070640b003034402016a501110049 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 40498880 1250 40497630 40497649
    0x6070501050108070f0f0302011b0c030c05030d030203090604031404030c15080105010e090708060103060b07050601150f091e0305011404020a09090506011202040212010305030316080601021507140408030c0c 91
    0x1b80c03024820750b8010005903220700e503444400602c072141580e215201c0d881c2c11001c03d180b41c00c2600c0c840f0148208200b07a04080060482083e0719190460550814000340c684400d405000582001003240369503004444810444000303552002c07904440c0781d550440d0002c1000c0c2400d0520200d0b14a03c000103155010f030380311204415004081e000540e0b20300c0815100d40b000542140e04041c1e41d41000f252085041000f446001e01400041c0100d626007100a184c0410040e41c40c001c108e049448200700304c1e00400340790180c0d10586030303008100a0768200017000110380c0d40054841e42c24078144000c0c0034071010f1076501840c0240c0d0f00d9040c5645840e00c1e041a254030700030080541c0c2c03103100104910242907105010b540d01c000c2c009450440b0b1310700703451080002a00160707042e0f0070002c00e2101d061041000406140030600f004c44862504000113525880791002601170482c03101d00003182c0500c00c0341c9408007001d00810541c0c5458980382c2c003540e41d82100c03010425501ca0200300070032524140091 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 40500130 1250 40498880 40498889
    0x102070e09030a030f0605130905160b030f04020d0f1a0a020f0d09050708033001050a03020402030403030b03060c07020118260307020a180b04060312050703020c06070501050108070f 80
    0x551520883d5602100104140e404042000d13a5561010899030b640494401070400d00020101d0800c00c5414018241880a06a01c401c20141c002c1001201608001d603a844091070150350381e00c0e6594008a4032890386100b000704822021440282008074038940003407500480c400041c181d5a511740054100d200b20b110081c0c51200070b000600d9001c885400810f0304520400540313080340d0380c40320702c5c82c80c40d0040d00e824420015980c0041c107454a603040c01c07898200b81c00022844551401d00400d1801c480c07800043e0007160004000b809141c003a402030043c1540203412201103241c52003992005401c401c0040b03000a0800911107031a040743c14003036096500300c00b1aa500b1080c1c004a03e19200600c92504103140018003621000d40d54440d4404000c001e181d0686418984410407070080768a4030040c280b043c0e1500c0407c4c4045803c0008411a0f0340303ca06142da44c0c0c10650030306070314095024540d141d02100c0010090f04114040d04007604a80b5010229a14141c858a903202040480e006 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 40501380 1250 40500130 40500133
    0xd02030414010210050106051209030a0507110118060905120a11010503070c060e070303032d0506030703080c03180d051002130510022506090e060102030f031003020102070e09 77
    0x818446030301d6000c1261210301050044980f0400c1042254040d81c40990010001c1200410713480000b58110300301c1d907444662400031314605a10303281c01402c940aa42c0000d0000b07001d070f03154229241d01440100c400d405c2000c04061009550b104000c00b40f100c1c42c007410f401036581001c0c03540c44440c00680c007001c1982c0721582d6010109000011141604000d101400b0000120350030f10120f5203920846030900300d00c0f0050003542d0f0450502400340c1d10303244041e60a214281e000009520100f80c10090314180c3d1000204440e01c0740c0b0300082c6002c829030006003140c0f00001d0f15042115000005102010780d5a540091001601040060701904a84081c2c80c1d40c005144d604a00e00d2143e00030103040c03900f0324504c0130403a02d45000c904040b0001d000d88001d64407507001c000407146002da4203410b640c03826908001841c18802e0041c1031960900c20000c1010441c00400c005a0007441556113140140c096192640381544442c0d039800c1c1540310590160003142d0011036809010f03410350384039040010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 40502630 1250 40501380 40501387
    0x30f0225150b1302030a0902060a09060905060f09041509060801050420090a02031009050705030a060f080a14071e030b01050102060601082e0803040f0906050f01120605040221090d0203 81
    0x20082d402951008154040303980d60b8001087c010381da004007a10352565155115008281850030140c6400c51030342026105040501090b810703880541c00b114140c4400350f4020500c5100301c09910220016600110361160030008003082c9070605610540c85640183d034842005000e6010398401c031405a80c1c0761703400140100000e142e21407250000c6411102d644800e600343d5a944107110101c4105070b07100400118004248076031340485005460151440b441e000001d14a00480d455880c0200c18009041c0d0048000c1da07032080f00203024644c020503e00b140c81c080940169400c0b00c1c030354038a0000f1560803051400124165100140803032007008107071200641b585950313003042c14000604100710308020180d004c003281c1040c45202c000041001000550311142410032003c0300040c3c2c0d4100c2c1007003601d0090200301950b94924220540c80c0c0030b082c0344030110241c0441c000601141d800c0142c01500009890201c6495030f030a041c03c0320f54041c500000c9803141c910305a110410340e22244010f9200b403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 40503880 1250 40502630 40502659
    0xc061b030f070e0d0c051201271a0a0903020d020105010506030106110a02030f0105070e01020a120309170a09060f0507170c030d0e06090606031c030f0225150b 70
    0xc08981c0000c0b00f8240a503194030f03100001099040301500403100001802010401c0c0d0400c0c0c441c0011030030855000380300c00e58448202000b0802d104c100c2d0400c444001d1004428042040084920550f06503203140e92854901c0b858009000410070407001403003403014100f5460b00c188100c40c161500200402e103503901c0c00c40100d54604036400c0c48030a600640c5513140041c0c0c1c04000065600e81100000302c0d180c0741c4141c01404401c0c480c08140d042d500010025000180c13004d5220ae5455401e00300000d40c40760070308142c0c1c041e5200d220300d1401300c50001580414141c02000200403501e9a6a0b00e0a040b150100204c6280c021240010300d54021003412840850700700f009440d03110701d40d60440f0f04007190301501d9030070341d4000300c028160f90b00100b0601071f00c0e0400340403e5a00400607001000403200961503841c000b90301559031004c1566469064220442580495007444154007481d00c00c000c480d10054001200351b0000c64056104c05000030094403907005802188800a100d142d8201c440d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 40505130 1250 40503880 40503901
    0x307050708040b0c0705040e0321130c0b0d0c0504050d0f0201050904110d0608010204080d2f030a110c0d06021606060308030f13110f0a0f08030c061b03 67
    0x200d00e003219000828440030031583d00c850054040d030058a0700030300a803032801c010700049031200c5000900640041080612300701d01d08954810076035500c010301120307a6902c2d1a003410500001c90052a84980c80c40000e280490039001e4082038441c0e86081054107000241910148194411144c000e0600985003010681c040b101c0d060a50060502601e411101c200040403a00c95070640d500310580484c402c00d9190b002d228640150009a008614060421806c56075400482101100704000581d6140c001d00d5030507183c543d8001c041e0300c07800c00c01c010207804503280c6d00b01c07003010f10001d1003500c107628480b00006103409040c2c0340a4080140c01507d6104c000107980442d4800c0c20f00808250080d00058203481140c00030340c0100025070b10390800c491040f20488014184d1101d5140201c1c01c0710110741c06401600152204441e151406480000441c00c0c14131541e1286260340c4090340c000800980120050405801c0300007070701c07480d948884464407000c0940f441600310150030320004002c1d800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 40506380 1250 40505130 40505137
    0x1030c030210020f010507090602160f050d050703150b01030f06030b0a2304050a05160f1809021806040b06190e03071505091804020d0602030c0912070302030601051203030705 77
    0x2154416151318100e000c01181c00e449040d01d20000040038082d0401c4060350502003a2a0700548000020025117070407031545c840f0005001d1a0300c1740c00380e082c01d01d082007000c00400006550082c4a0f42d90780d280d204040b4002e101d02c079100f50220307060000c0b00b14220441d2240c40b094a41c0248066010303101d500d400401800001c441581600c00c1080781da0321212600c0f070040c0329070320030801004070303034041d180890a109890480c243c400921040610030041c00070401d1003a29000d48015418405803d1000041c004419010750005000005a242d054142003a10300c1010305480900c01d2061207402d1212a1150b04069541054048410f406091140916007401d400090413101465154404480c60114860200c03002c46d01c001011415030411660404803021101000c54040c034050b004100c1c50103020b5001820242d0000c00150628103250980b40b00b0304000d041403850203481808283c3d00c100390b0105030300c00c0c450070000040790f1815007074003149500e20002560564580d610152050b42 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 40507630 1250 40506380 40506409
    0x105161b0201080703020c0a05071203031119030b0a05090a0506040507110604020f1f02010c031103010617070201180c0302040b0603060102030403060c09030204090b06040506040e0d0c06061d070f0801030c0302 92
    0x8c2d240001000c41e40412210b0041d040c1e060510781c269895240145c21103030a00d0444607801b405008001c1c400400301600d0341d03082c0941c1008a1032075003030000241ca83c00c1c0764024503401a524824050315502c2075211501c910401c0d10100100d4882c24016110540440c50104040e0300c420f00080047c1810481425407000c09440801c108091600c4241441115410301c40140e642c4c03400b08200a40c0b40c000c1d0b0040400b4410301e53f00c0d55050400040c000d50b103c02d0301d00094031020740400c2c0c44038405d40c003100c408031801041041c0f002e0700d880c02d00701d61042440241e200d2810701402c0c0940d0319081085034003906058000f980f800307240d07541d480c019000e401018400d200560310004050384450040204640c41100144c601e80303400c804200440b44040d0450340640d25001060f02c3c074200c00107120304140b560b410b02c00d05003401860a140030301407030740050129681150000c10340700001903486004600f43d0726200c0d607042144904860048003440040c2c10f00d4200b043c10000360400c039101c1030644 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 40508880 1250 40507630 40507633
    0x1050d020c0a051f0603110402031506031009050c09060909070201060e0717150a1a0702040c03020a1205090c060c0a0c080d02070504020708030f0c07050105161b0201080703020c 78
    0x1545421100d05040c407001c41928141c00204070841d81304443c0c000c2d034240400000d000c028880c00c2d40c0310414429500614107000365400000b203040d00e1014003c40c13451910050590b5070303274a4100301c107100e4550746125840c04982801c0c013181c110203160701030351003007100907200c6070400c1207643c10031500c408040c00400542d541d9160201d0401201c4000f117204e250140c071051840e41d070410f5280120078000b0114a0320300041e221044062341d81284000403200c51380780004890007000544c44a80c85001c1c4001d600030314141000300c907a50140c01074454403109895400d030344484510880290b88040f10b10b0340703007500800740a4041d0726151010305180395410040720f206a91940c3c6d92148405a41c009004550104080d52081c07641013020802501701590290309101e01c9507901070700c034000a00868003281100f400074020344100c2090318030701070b0000b000340090305003c9003018800d40280c20340c60004103807490701d90b07800a01c40d0340100680c2c0d040c1c3d01c800b8076a45008044009410600d6207a026 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 40510130 1250 40508880 40508887
    0x190306140d03111b09070f0804030807181d0f010f030204020307090308070b01091803020a021e0307091a010f0203160c0f0b1206030a0203250e01060e0f0f06070201050d02 75
    0x1140350800ca0709035041d44686000c00781c204180304005c2c15800051855081221103000341404a80c010b82c8150042c2d070505000e8855140c5450541e518495002c011040200380c170b40000382c20407090600054880d01c80c8960780207469858200700e102d80b0034040c503500005002010001800d0542c02164425024502004801e48907503400b041030740403d800380d0b2500c880034010700011a00740f04a0340d490140f4506052a01d80c19a4013075103c070640c80e030180c450050000983c0341d0601005e11010f030b4000017000c0d580c00c1c1d070b100c59544004112001c8686000c445590740100d4035401080c510001d0000b42c0c0066041060b24042d100e0710809110040354080301c01800014402021421a0058810245034540300c0380c4403c240c1a4540c40104028800d9014840860140e2008200341e852460060802602d00090390a0b94101c90f00c2a13001610a40f125070001982c5a84a040791071802c40c120351141604400204100c200b4501031840355000d5400c00940005600510040403000c28003d0090700303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 40511380 1250 40510130 40510157
    0x3080705041701090c080c1c08091002071e0333021303150504080a050c010212070e010806011418150d09030809060702190302030909010b190306140d03 67
    0x55100046241541d16034413940c0060800c40d0307801c0000301070288140100341381001040040c1100c01c005100088900c6641040c10a020042048880c004005040c18640c05100e2034000d5550005110381e080081c80b01c00059854804110060120b0750082c140100301712100d6228000303030a0f42e01406403280c0380e1900a03944085640050710504540300740103180b29103107040619186510150051542d840c0c8420880000c1400b020b40c1c01c0d600e4145051504c84103e110700306e009100305403805507901003074000c101c0c0160340a18607d10600080c1c0c0c821409447d414019075100141c4090100840740a200e0001c5130441000d1801140900410044d001e110102030410b10381d02c0179030318200d0162105250b01c1031540001d1300c90b030082c100380c004107010300c1e045000030349921041e01e180e003480d032598603c0300600d4030030401d50743c0c900b1004110f8002e650759070200e002d0982c031618800f003281190381c0c12180d81c41c0c001e01c0340500310f544103441e514240c140c1d601000240c1c44003600c101c080c001101403512 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 40512630 1250 40511380 40511399
    0x318030f060a06060e03070b0a03020a05130b0d0b01050a080f090304050a03060501051005040e0105060904090605070e0118060c0b07030e0f0102090a150f0809010b03030c0c10030b030a0308070504 86
    0x600801d001c90b000601d4a0034410020580388040400c079000f80c1c0400000c020181041040380d040c800245070068640c0740724801141c0e1845a000e981c4000c1c1d940d9800420100d81c400b0081c0128096442d0400c4a0312a04006460754051105004040713190321000a00c11003100e0741d010b60101c4a80160380c44d05440d0301c0060304046198000399880c1d559071006002d60f003000403183c401c0014a09100341030600c0c0110202c0b44c80014005e46005020100d03281105444507000cc010b580c0e4000c2040c0403901d01040300070f01032811a40b4031800904403000c020311610309003181da010f40d445a6103540845510361030320071509101401180406a50394006680800d003404035810036600f5500159440c6180b00c2046401036064001030450045110789607010f5070802d00c84240010142000032841e41e03059041e40c010020041ca554060000042d81180200c021681d00030441d4101c071110441121031740200c0844458400660700f40e800707490320360301080c00344c104164800e110b450590300c5c250701c80310f041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 40513880 1250 40512630 40512643
    0x60102070b120603070e0103020a03060b030709090501020903070b03090a06020903190f0311031306031a031002090114030103050a24110a02061501050f160606060c1209080318030f 79
    0xc00d000304000d410f000c210310b014440c00c4014003541020f02c540d0750641d000500e03a049144002410555600004070007034505012000091800d004c041110100c0f03810803038040e500c4200003e1180c001c2030b030b010aa104244080c0c074011342c1401d0040a00706501c0d80c50380001c0d17101d42a8503a044c03040c00203480000b58141d0090303100c5841222001c101e090f851a0203865a5030a00184406030824450840500c0c01d0440c01d20880f0181e00c0d0218169081400c0d49081059000000383c01d4001c001c1d45903007980d0142c00a2106420030323038440f10007411760b4603984402c2c0020b000081c900d401121005011899000148400140c0090445003450343c0c8260542116014840305200e5000071908860064040c000e09038000d2694036400d05440d40d0f000000c20920555022002c034003008108541e6286500030b0000c10107601440821009846001c09051004011400c03500400d0b804032910b005403050021000f21040c403001103013801c1c1d840f4240c280017282203104507018801c400300780361490030400c8070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 40515130 1250 40513880 40513897
    0x70308040f030302060705160f080904060308031b04050d02010e0619020a0308070503040201020a0b0703060306020309161706040618080d0c031d0a06021317010e071a0909060102070b 80
    0x1d400207440e52402900306400108050107121081c01002d111030300c1d1b13514110000794054a03029180c091481c003c540f9001d0414a25000340c0b4020020040001c2c100065001e910384090000000d207003400314071840c2c07103240949500078464160240041d4002c007050083c40000400442c2840484442a014000c03031000910041e40101c60305414103400401d156082200391a01c68070317500c0c06400107942e4200064000f03020b500e4440008005a100394002d9014661118041d0742ea81490a0242c2d901c400b0042c40c602400c00c5d1a00000d0903840f00c2444e40c0e040b00d0907001038032441d50340b03848440c018407a0020150f0030302c3c81d61030705d00c0004403203000030208050110300020b844804000700030100d48010010600c115014820f92443c1c50b8001030600300701c0da00140c05681c412001c000440314a82641c092010821251410032600106420988410307240408440d01c003030351549440c090791211030020351010300800000003a0704142c070003164412010700440c2d15282c1d982141650b2648030f10314 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 40516380 1250 40515130 40515149
    0xe030418270f060b0a030b0610110102040303030e0606030105010614030910050109020d0b0a050105070b0603010212010810050703060501080612070e01120606090209031f140a0207060b03010509031b07030804 91
    0x85441000004d20410510101c2640e582034240d01303680e6403400395030303020703010911510300c0030724583d007840c070405c4100c0443c2c5144000303544581d920303c0c024010340200c002020071800b070300b80090b0032410140304460480b1055902e61004c464624103408482d480600320a0060144082000415003680907507402809242401640d8070000b01c0850b04840141300507611072001d6100402040ea4020241c07980c064001460301620b407a0f2000090091042c10451001d04102100020710904c02281c0740c80010007828090040c0e946400317084048481d01c0c00b03202c4c04181d030180030808904007404012502c0040c281140c8640b91280c10721940004264002e10041a900c072030f803401c01ca041d015120090910040550415160000081c2c403003080d03032038031114440d60f0030301104480465001010802c102030402c81050420b502c841003e540207840039504541483e00f13080e140d0405100c3d55218481d070348017031b50800d4280100b60205070000c2280210074450400c0100100f0740c10302c0104020040c512 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 40517630 1250 40516380 40516403
    0x601050f010504121103030714100b030601140103020408070f060206180d0e03031209010501050102071d0c0f0f03040302150f0f04060515041b0305072303040c0801090609020102010e03041827 84
    0x102004d2500710ac0c0182d0100d400d0500901c209651030004020381990440d40607901c062555400480081c0520780c41b5541500c0b500c0c4001070414061a603401c1a15501e07800d45903160344200703400c520380d1100c2104221030f500c0902c40415603841042d080498000c010140d0f0320b0460520340780c0b80409010303200361a039a559039004102c0e43d03804000000c01020b43d0503600780c00e205da4441c01c0d5080d07000144400c082d240c00017036072840c01030f00344c084800d080906146692a401e1504009503110460600318501c407543d0000f05042550b0011010721581c4055450043c0780d031195902c0014100c040c200c901540c40e503244804c0c5a640e02c0c0602642210007030707000c0b4262007080e0001400d40e4809440c500c1803101000d656210290551800002110168800d07652a1910319001420800c00c0d403000c01e480d40f03440c5e071000070080310382c1000d17619078001d90081c80504041d003203c0b5203038400c5214102c003901c0421301b4004410203d410503010390700b00d07152440c08000b204400a2a215041d80204c82c2c400800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 40518880 1250 40517630 40517663
    0x90d050c0310060303050d020d020903030307090e0c12040f1b0b2101050915010507020406090905070806070512041712010303080c1c020306300601050f0105041211030307 75
    0x400620141481140c820b0003c0c61651318044c1440c440d901901e00b8443c1c0020300b030400c91a1a40440d9865032000d821030b5030700d19000c2001401800039029100c401c0e01c1c050b0120b00d603404000240c8507440e030503110550407034a03036964001c070b54403511104940c28512640f0403040580ca14802c04014400140d140f95107600b42c84150f48044198540304255030310010052000381c8509420507445a056520864065030460050351180550b0500035030003820201c1c08610b40120b41c000002d054800c0c400c80da2210344524820343c0f40c032030444e0700700c0000f0380901201402542104400b5040750140c901140c035280d0b1a1450905135000c162142d10303140c51b00004000305a484018242d0040040e1b80d0a420b0000000c01d13003060b5000c3c000d500108a40100c042501c0d81e0b0b6807502c0641e04440301400d0340508032010450862148582100112030040c040002664141480516280c0d071050303552620f02405d00c80c03140d6090a0084090b140207244690724549070f1000c00080c03005d2341c003d0740d030381410300000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 40520130 1250 40518880 40518883
    0x3170403021302070b07140d060605041410050d0b1c05031c0606080403120b090106091805040b060402030702101103010504051e22020d0809030c0603010f030206090402090d050c03 79
    0x806035030074000f481000090003203500d0484281c0c01401910b000b8601c1e000349032804105014041d40744148500d06980001d04c41d820000074822207a14a140c1220700303001c0e60070802d00111341c812150114008200150800745140c1c8003108203c0700130f01e01d43ca0500d284680342c842185401085910740d1000901c0f4500461641001200041c2164288030311f41c00c022006208480c060001024009440f0402007550102e401141050001070000c1005695030f42c402400d00b4030030710500103500c0c1c0c1c1c40f4400240c1085030203441d00c140e80018411840d900e844040c00000d5200400c0d55003180101c007084c0601c900d0324003681071007861901c2015129410603081100b1550041d00f0f40d60352414005205000c003101021840d8400151003114021b42400640f6100160310048006e601408400c0340070204a40381001d030951107416011150203241610174031200303100030f00444680c00b11240c010401890404010700e02114050405800d10700e041020030340c18060008100c1d001c0e0813000042009050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 40521380 1250 40520130 40520149
    0xf0708071403030c04140105040e070818030c0601052404090905060105040e15040201030b1809060c0a0c08160b0405060a1b0e010e0604080a03050a1101060e0703020a090317040302 79
    0x203841c4003540c030310306000b4880e502c0340c4610f100d03412140f24020110b5619a014034280d4005129a000d00445407905407002005154101e400715060102b40c0c82d2000f00c50800030079a000d4500c050001c02560b4203000402244549012040c000b03110018107400d2001400806040202404907011400480d589091410300c0e10580003140990715108000003240f40029021004106070540b01089889500048018004809010760020166140c1d03074003158a00c240f03548209480d1044c0c032220b854500c92101c283c425800480005880b02009101041a5100502d140008105021003109042d0742c0c80d5920001294251501d406c0310b000c105084d00305005440816403410460514014203100150031005880c038458108801c0a009074915210441120301620403001107401d001c80915000301194015906407001404130341d00a40c5d42e441c14010711003a10701418042006030303600380088009401414010040000301000040030403217110009444102849040d66602e0840c01844400700 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 40522630 1250 40521380 40521413
    0x200d0807110307020604050402031f1517040201020303010b03090f120414030619020c0a050109062403020102070603020d090606080d020c0f180402120d081005030102070b0601080c0f070807 83
    0x10010032003c1c0044c0d503400215015a07034200c0d001601ca48880e41074004804c58000081811201208041108003103200e10945545403643c8820040c1020000725102030000d0b02c3c0240036910500044c84220340100145038403140740c0341150b0003c4604074006145c00011004456403420005042c494000384d051a043c44040680086c001811700d5020303840c0305080d900701c5603200e41d404944d00d20314139414442c000043c0c0d0008000c0c030417554581810f80c01050240020a000c0741200050391700c07002d4450f06542140c0d0160041e00d43c2078944441600a5400a580b40382e03e90b17550040755000401ca48111009002401c00401303614090b00f00c040d00e001102021603100305c0048440d5002a80d03036031310700b40b0100d107501041d424a48482c40800e150401c006145107841c0a10101854060380c4490701a00c034600071100415000d9645080c03600f00d20a044021301000d110100003071455003d444440e8101c80c6000c00c2c43d01d001c003520a009002e8107c00f1048444a00018800051080c41440c031000b11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 40523880 1250 40522630 40522633
    0x2a05120f100e0c04090b0a0e0a0305070219031202010504120c020f100507171c0e030a0305100b1201050406060f020a030c020409020604030302030910050415200d080711 74
    0x60351001030031540c5800c84514604240d8070351400100c029020300c807000360800d010b0310a102c48400c0e480d141201c0807040358205001c07468000c01e06002032001036008000c82e0507803201460004140c09101c0114403003509100901008000000010f0700039000341046041980005078a043c1403414101c0c0b08508a6071104003c3c40740c114a015983c2c04015181418040340c0084070302056607826520380c007aa1801400900380fa0b00814400100180107207055541d484401e80601d01950720b440071190840d440603103e07441800011803281c0030364889500603040044c00319070560303511516200b0b0b91190b40300314591403404004002a082c24007410000d02940c0c2000c0c4c072030b880340381c0c0020b41e50444803074007074104400c0740c0601d001e40d11581d20129a280c0c0244c1029130307403038036824080d5503688000364250040007100b25100080d803150303080d41c003a50142407411181e92280e020440d140307000300d10540402d022819150019079810040b6500c06c965584030803441c1c0c40d1402d0f001c1e0098a5011888009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 40525130 1250 40523880 40523893
    0xf04060504051e030703032405060d0f0504050f101104120c1e0314030a0503070f0309050a14060a0e03040504090302030d0606020109020316150503070c0506010b03010f0b040308030a092a0512 84
    0x1000c0310800000299032082c0c3d101030b00c0c0d40cbd00141540140c007003410b0345411035241c1000e02c000c1c040080f031001c12001d440c0c030487d1100312201d00346008850240b804602d0540060100784801903546200090b018066044410f1458403200e4602150540081212812400007020020840c0850340b8821008600c00510304140d51280060290f102c0201100c04205280c00d41d20300903030007544002c8406070090225000b258091821901100648000102c60300c90000064100c2405016035286000b01d8400795084c1450310080c80301606030060110250300040c80403102e514030a200301c20090103503a002040781405c0b40181810b0402c08014202c00203c4c4c071032306002040d5030569041c641c4040d482d010b030f41c941d20300204590744150303008003c285000740c2000041c8e005800380558160b46004042d8003005645441e100c1c0d2512652000410b0408140001903202c046d952048c24954040d140072048109070104012042998082d10741040601403014400381c1401e031420450b103441000201003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 40526380 1250 40525130 40525181
    0x310060b1b030412080306030f03040902030403090806060a140103091401060303090b0a0504060c0c12050d02060114010806040209010306050d050303070e01030c0e0d020a1a07060b04050f04060504051e03070303 92
    0xc103e03009800142200c1400401f29940f6281000448000d0801400380c0303840b1601d8140001c0070f540103171400d4000881007040460044800305100b03018000051100c0d40032841c11600c1c44804071202c192605056903402c1070300108400b10055050030618a0001a2841c1107103009400d260564201410201e01401000c0341c96800a04032000d0710748600340810440c1f50b80c9401c040110300c1d50012074821640410400c10001d000520025807943c035000d42e9016038840c80039a001d4101c1d00d505500140b0150046121410700b5802050194810b14002c9101a29400494040348224008035000d500c004100301b036442c0e11660348002d480003481c051140040121000b02505c00c0300c030364140f01f000080b0519045580302000c0c400207002c11680c50b10070700304c10400304003d078000480640d661820321012001500e81446064420050081c802d200c64070356403540303030080100400440340c62284100d0304110034200120480c422036030400855686041b440c004041d20b80340d00c0b80c9407602006d17038801403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 40527630 1250 40526380 40526399
    0xf0815031b040f112d070302030a090821030606070204060f03062a0e0d0b07110c0a1505130b03010b0403020f0f0a0603020c01180b1b0306130b0310060b1b0304 70
    0x1802e001030340700c5080030014098405c0e48440218101a8501c0b24001000e408040c0c010001d0400400d4076102c02e862030b40e03151840d5072681480110310219582622104aa04940002850b0800d401800c25800c240040c1d022404a0300142c11004803800c84000030020444503004002d1045a046070724402100317502c41c0c0e41c800c110f48403081c0c1d040c0f08500300c98110b10340341c82c1c00c0041c80c2c80d0468609441414400000b40c80c4500092002c2030310b000d032030902a001e0400240c0c0c28101c13840c0c82c1c4030354144090400101c0301c2e03821000c601c804140341c6190000340c18441c0700185001c0c040900c062940e40e0f18500c10403410065010040d800f6007860003180c10659034400ba00c200329012814056035800030710b02c1eaa03004104c3c2c8103210030b0305e01000d01244180700e55080d400d84103800c40e00040ca507480344c0202c040b00a000440e802940300304020a0b5100c100426084085024400b404480b03982c0d0000301340300b058030032907080444d1241000c9651018100119801e0b9529840c42002e14500342c140017220 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 40528880 1250 40527630 40527637
    0x70506030c0c21120604021606020309010e0a020d03180801021801080a0c080f0c0c0604060e0d0512010b0d0e062509030f06090203030405090411090f070f0815031b040f11 75
    0x11440c44c035018000131050745030364048910215001c0c0800c00c0d03242440c54004000e40050b80e4101540d0302e8540000503507800000c1003a100c54008018004480960f0b800f1a4101e2110600c240030b84064000000e020100340060500d41c0c595a200d40c40291503100010100c000c024400b80f80c040c18024001c040300d4000307400d1500f011502031a880256106501d04110b03103d001c01750f07591882140e01300001e00801e41c0c80180c400070f0b5442580d00060540900310344c240901802040e003400e280d00108165061100100f10300e0030069000308240e9800706070207050030003c80b4800c000340861600c00c00210003c0030726000c40003c50410140481c01c50302c4040e5010302856000b040281c0d9a2944015560204141c60044c00024414a01481c142c0742000406404005881c06041c1d101c003c03645501404e00a41d100c0c46003a542d000035445c0300c0508030383e40e100251003c0a075003a0b005001d034450b1000d1003000050a806a02100e180691100b132000700d584500455003014500100c6000c4c20740640200e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 40530130 1250 40528880 40528897
    0x60406051b070b0c010506030106120b010b09010210021216050c071a0702030a050717060411060a09090606050405130b060a050703050904020706050118050910020c070506030c0c21 79
    0x903180104480c40d8403441c008641c1c100204414021900c6604e86005401030381c8105415002400025036640703081e1440d510b0403c0060016400c84010700c1504041da0140c00b40860510495401c408a8003114040f40d000e1440c0c490000750000c1009a070300d00243e0768403101440780c90305a28081000c5040b03030700d85025000c6d03c80300101c5140b030301d040f4221910603144c20a03002020b0340c854152515203941d550149200e0605440512960b0180d201c00c08030782284102c0d00310810a0a024a6404000e8158019660301050080304800410b800c1014491107015007a240c50782070380e072800d0100b00300e0528410306a0412103400c02c1e10700890354903528143c81603140c05040c0b0a84940e064a0182c0d0a4082c000300075400c01d1003c240c207020301c901d9402c001d040301e00c0528103001e07459010a1050958000b2900321003254040c1c24040e100f00c070654000d004840100b001c0e10504c40d00c880000e03289902c10f1707a0000301031001003244c01e4a10014004040140036100d180c5420080e044c0003803101e070080003035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 40531380 1250 40530130 40530157
    0x203190201020f01061e150509060703120905030c0f0304080c0f0604031506031202010c020d051e03160f170109050c0c100606090501090b04030605040311060901020c0c06040605 78
    0x10080459000b00807035a001585a40284059a1030b00403681ca40003070400c8100b42000c03a028005140507000b42070060f10152551803900d09007880b07050040f20340c00070b40c0403020422030346807440c61a6001e114040c441446000a0346c2d13a50303183c036503840c60034160b02003a0030b2542007000300f0050341500040100083c10103680c41c0004846031800a00980503c0d88040d00c8041420202c0700c2a13415640448103503403041542c41003084010a0482c00ca54011200d00c01581c0321000040130b040c042c01c0600341d0241e00c40050f0038a1000303401e2403075051f041961966228a0303540040e0100981011541c003140280e0314002842c440007100c9250454818400ca80b005961003010031031f1184070108030380130106104225007812100d00d034003200800c61882000000b5004001c0810a0b42c841c0b10f98908817045802110f08050035500c4010040c18090b004900340f184181c07140280303040074030015106070001000180c0342c9840682190401034a01080c03481100d080006000668201007503030f032410002079 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 40532630 1250 40531380 40531423
    0x301150309021c17070506060d0c0503010c0503061503061c03050d1b090605030c0a030e07050319060501090207080a080603010e1f240501050f161101030c0206040203 73
    0x24800c0c0c00034410440043e40181a83d0b054040c504010401607040504c02c0c6006403c0f0810400d0401e014001c10038000d0240c4c1040011811a1801e000c003030603d41e0140345c010344541c0e0b40e80002400c441c001c26402c0c0100d60044100003151800f0a40b842c080381c40d940103e4550b1800b00e000484ac01d1187c3d2100c101e001040e0104818107210f10161199040003000804c5080d1384146101048140d460890b00052070840c004189540f003030082e24081c410040c40c0e103040581c18074068014044882c995a19441007810025040d49c0c10000045c1c40800c8881c1c48244001c281400c000f60f50301600030080c52401000703a4000990018120b1307112960b0382c503203184a5140c1e08000b034003400034003121185503c910383e920907108130011401d90320300100c4041046409000c8140c2190040031901c13040c04622124801c004550007840249a2100104c2c10b80d4501032440001410b000b0480100341c400c0c101c01d00142c001542c061180e814440c02ca40002e001c40d140a90001780d440004100c0340e04100e1390362 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 40533880 1250 40532630 40532669
    0x90f0602031210030b1003020405060a0303090b160507060f0207080601030c120f0510020a17060303030c071703040c031104050f1b0c01050405060405010c080708040803070504050d05070f0b040b0301 87
    0x1c08454043d55014109005c541410f04246a034905e59000030792007a071820001c61803615000c480b000880c0d5150f101d14145516000ca10b0f046038011000018100031502500000140140b2240c030190505031030309880f6010900700203141041e5a004035445600c03540050000c103007508500f40072160191200550b100c0146043c0031000f40c8510010941c0c4501c0465000c06056074000c0c162030004c40c0d44d4801032200c0c403c440342e4206019a2001c1d01a00b0402c003042070915488024484240143c107010f2607022606603040740780d8004c03141900c4000b05050103004110300442c00034801003046900707021908008080692503440070301710000c241007440346541100c441d581503030b40b080c2244008008503e09800c10742d0321040107c40c100c83c254a05104041c2c10342c05041202d0080a955940c20a00e548558600080340d10203000c01302404030a100000d0196660003030841502d00c40d1000c0c1200034a4105030704030301c00d0baa40040c02c0d0b02c40144401c0c003400141c41c0c01d4034119003140c5002d070000d0154 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 40535130 1250 40533880 40533901
    0x20c0603040c1701050a1b0c020616020d08030105040515010f20030703030603170708070602090d0c09021206060301050f0d020f04090503030405100b0a060e031c020c01090f06020312 80
    0x5900925111000c200183c103000700640c40184154103030341e000c1c070201c8070b941403070700c01c0b8a460078000c0082039690302c3c03480c050309041000c2c0408022160f10000d0080e030030780020340e1900072240d04440004000006020600f043d0003002e0b04000f4811648404c005d6640010388012184c0d0514000c01004040c082400740c0d1190301c00401c03154503c01d07a60342e0420350900134040d011030b02064602c04105001d001a9003072030011101c0481c0c002c4001e07810072449548240c041d52082c1c02c1c42d64040da60b2801f071400f0900c0c000001d001400f40b2000140c3d6413023040c0381d0705003032100185030601c950401e000400644e1640404400340c0f080c12580426500880e1000031203000c1141ca4140e040307031800b904101040400401580070314020802c41380c4040e14160120151001d00001c907070400e102c5401002100d004600c0014140c0c4014107403201e2a400d9074400c3d05400d04000b810340140d210580214030b958114200901500c80710b4504940c1c541003e40103580c074822051102d01414018000446c0d4005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 40536380 1250 40535130 40535153
    0x3071e1703060d14010902040605060702280305030d0e0c0a0b030703091707050309030f0712020d02011707030b0406080705150a020703080c010501150810030204020c0a05070e010806070c03020c060304 88
    0x340204150130b81e404201c0030b94001c18640100b01e0103540b40200c0801e1a1901a0603138254983c02844414503048010820b170300d5048400c80c011100303a0350140800015000e0001d010048101c1800160b0201001e00c4d00340b1b400c2046041901400007841c3c1404002c003843c080703907800070b02c0d41401715000c841850000e9503110303400d94092000300d010400008002000c0000c0504c03900403000c40385203010b43d00d600e036150980380c8241091488000c9200c00142441050b0f80384040c01410f00f41100340d07102401203500b210803200740c00041c1c0d0301c3c280c3c1090f80ca06440b80c0000b404018001b04400d5040901181a640c1e100b00c41c5441c80074041101c8950320300c2088058099076100d01e400381c40c0c0000080d8070340604403e00410208210000d103200c03005104c0c580440c840c0d040c002c801d0724524038540910009601c8000c4600d024010b090100020600803c00302004000001c0c1c40b1195614282905080c01c0c001b0340041c0400100340c01d40000700354009665003611104458050f541d4a40d403800a24824 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 40537630 1250 40536380 40536383
    0x5030d0c0c03080612062e080303010501090f0e01060c0c0819020312040308180a03020a0308040f09050c070f03091a030612010203090a061109090a0b0103110f120a0e01060803071e1703060d 83
    0xe10090000c0f80000c8d010010714100c48081c0c035560960364847c1049090300740340e40603100400700120010005c0c00e00c28a0a5840c0a020b9100440320503103a100480c10320b10030031000c8020405e410444411801c0c2000300003290403508000d02e00b0310703080da901d0030078501c070300454885003200200d841e1115a9a11040388020765005100c1b220f400c0e030341c0c6070400681d0014032450111200c100d10000c0c03103164038082c40340304a8650036210715200cac2556074002a40030154050702082080d403000b003694404501d03c8040800c031068103540f01e1421104224403502c841c002c5406507401031080c4000c000700040c00319980c691001c0041160340b1a540b401c2d0187c0609201154014899400c1c480307031106a61083c0603030702081c2c1e01407040f0364058000c1140c91080940391045e280003040498400504101c020b900200d009201180c4050b840c40b04600f580c1081e00803400e95000011540200100c604041e0a02c8500d0034000c50901d1264990000113400111204820800000002c100350b50300441e40003541e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 40538880 1250 40537630 40537711
    0xe070c1b0509180f01060302060a051b011802030c0d0f0f030203090303030703090b0f04150f180302030903070608010e04030804030c020909060601020d030905030405010c05030d0c0c0308061206 85
    0x14605884401e41805010364003071610300540b420f21003080018002d11b0207890b005080b46e0328201190404480e01d510120400c144c15814102400100000f80200c504000e001c8900c040100e0b03050040508086040320814850300715405550b000440c81d070600c02490341c100e1009090070b0b10310705040e4110b20804040a074140800000c1003646a01a801603c1d218060110080182e44070386c0e22110215091320003815201d8156007010241c0e10a8200880c40d500c1c000000c640940c010094602e40900c56104801503000171841c0100b5040c1004600e00600541c035014941f035260000c40c1e402100050409000c20042e64000340516028070102c504956002e0a0704005d840c02d52045610340d10292202c50050042a8980050512074001d002a40d03421801652420b45030100545091805a10444041c0024010242e0000543c41148103010503519207030700840c0c041c81c0040c50701070001d14030307807140030910300c01000310700e0008680c1e0307009410200d1401c103e8490306e442c5142d50203180038030310751 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 40540130 1250 40538880 40538899
    0x1b101b0803040305030115030c0e040209030a05030304080d05132d020612010609141f020f0303090705030c150910050d15140a080a0308040201170f040c0e070c1b05 72
    0x1010b134800000c41c104c0c0c0003404c0707072420032090103411000d81f282c0c503410900180d8181c0350741600f40f4141c0c0c001c04800c2802400c460442469907212801e5800445040c1d804840108030006580340c07901600703910103d544240400155155588200711510080015002c0304424141d080085603100b00880c0e02d4000b040c2c291038283c002031400a46009024030340c002000300d074002810442540f610034014000400984141c482031001000d0380801e0000c00c811449289110b02000405000440c0501102c03400380940703030701f0b0200341132400350503c80e158004d030086050b01105079240d00c25180140b80485141e00c41c681141000c442c24003442c0307010f10100b860035000c1540d0300e401d4034070581111601d841600040c0b01c1035080060501c0c00d44140c020a400a903600b20009108600b070756845032050501d0541e012095941180a0008440c00c5400c03600500c18481171100302c4180800400d46040003040505c2d0140c0002c121824501d0002d042441442045104a0007010018003421028080b20038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 40541380 1250 40540130 40540133
    0x20306010303030203150604120215040f0b0924030702070f030206040308090a0b0a0302040509130803060d03050d0c03060602060a0603050c0607020109030f050c0109080f030319020c0d050307021b101b080304 91
    0x10546a90f010881c0301cbc00000100320b011541c408290b4044605803552144101d24000c461304071988040059a40311001161551442035048903007a4004541c00c0385607220b20b050360001c0c0c501340c060b401040c200c1802240820041e55003e04980603203030701c0446039071940b1002012940c814810340243d5801d20010404003030107075050b40907204449044642c0c541c2ca44500184c8101e8036085e1001030181314003080010518200038241001e0700c2e22030310700280b420400122850480d80300d4240c076400079850b500200040342e410407071a83c109404002c108046071842c0d0b140355680903101c4c001d5004400100d80b030003e5a00030401d0030000c640015440821213074030324196881d0341484e420a408034024200c08110710a0000f00e141080c002d010080d40380d41c44202503003081c205038000d1414000e07020084001204004d0148000740740781e42d110b035912400d2001001e800c00803000140c0b03403030124101e802540c4d5521001202114074107410815041c20b5041d0b100c501000c001030000e040440000140720 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 40542630 1250 40541380 40541399
    0xb040303050a0b010e0a0605070f06020d06090b03030a0c0b0613050a0b0a061809051503011407020c06090108180109120c0210031404020f030c0a08010203150d020306010303030203150604 82
    0x41c4244002d0a0400c283c503a408010f5545282802420384c10860320030041c440d00e4050300c000d15406003d20b84100e00160f0b80d50f54181682c0c030000d800356005842d00c408008080c160702078610b040e4402c80286081020840000300718120340700000c0d01003580301c0d021075156168248600004d043c0710b8401e20551420b0314402018210b0b03804030030b0182e5242d0900207111032189900e09681c4908443c1240f40307610b003c0100c8040e040240c4044000310104001103ea40c0c0d003445078062140035048052000c0c03401880c00781c101a2072440c042e0250904220418490307901103609940902005a80ba54650200e4501401000065002844e031064100841240c54100c6001b020b5240300b203c100d401c00000c61000c805480e110080900301c4000c05022a0040c40e0141c080d00d50814045c0464803071800310703000111004007603445400300c0d03540001401581c0c0c00c0c2c03240242c4c1005003074541040910f03540d40030a5131110144006407c046c2e0110114040b502d00b01c40f00900280000c0001d070302d8640761031096 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 40543880 1250 40542630 40542641
    0x9060e030d06080d0215011a091807030605090108030d09060e03120f13080d0c0201110d02070c0906030b060907021c050309010c030614130e06012c0105030a03030b0d0b040303 77
    0x40050b1041303044008a0724400190b603800d51015421400b09a46081c140665110382c034223426a1910040c4400c3d0b12603100c01c0e0200002c101c10340464540740c1045e5074050221815a0040350107000c220b00144502880041111150402c0f040b0000d000002810200c0023051401d031300c80028000050300c1d0380101e00c036140701c60080c03c080490395600e031220f120308042400c0c07048004102e000c0c01c0c441850224400c1e840450426098000491f0480c081c42c802e4172564000102510415404507001013400510341d000c50142c6100c48041118034110b80ba0718910707440c0180868400c1591a0010308010700c20b201c8000000300c03210481c407450b8001400a000d54100b1901e45041d9840c1089030010540b19010f0a4105c0741400d007030550070f2040c074061113240300c0c0e01c4030742140490b280d070b80301e01c0311401c01c11520307000304810000c0c3c0c1351001403408404854000d1070980314842c4951001400b2a58000c2503030420643d1608001031141803c0c404292110141c8001401c070f14030328070400040c140c054011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 40545130 1250 40543880 40543889
    0x3071403070b0c070506150f0405010305010608070b070f0813080d08010501080f06090403110114010f05150f030a0504020409051c0207080115050607030216090c090603020306010503060409060e030d06 88
    0xb682095480c00d0070b1100d03c1c0030740f41c8060b01070b0b4030007404a0307000360450300c5a200a10000e0100a820040701c0082000d1718400c0c0d000312190b139520201004101700c240030003400f078859081ca5a24000c46515540001c2402c44009400528001540c00c856460003005500504103034040c0c40c00340c0840e090140000c9424401c850100e10f55400040b80e030120044900d00c2401c004010070b400ba1180e031811030b0300e070f0b200c52400c01c2d45658076403900751021640e042007070013020304920410f5410709180c00d0140030207403078800e541c1d6107005000c4801080140016250300044400c1c0004496485000040280000e240c01038a43d0040102803000c04401410342e000310f58541d000c64110070b50302c0740064209c641c8180e0019040c1d01240041c400e901e400001000114000d02c100c52503030b09009042800c4a4040d07009010003545c80c10103103c2250002c0e940d01c024500c5040450443c0f03402c20004e8058400101114450b55461404004110a607817218a610a403041101d031905040004540103010b01d008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 40546380 1250 40545130 40545143
    0x90f0a05070303080f161409060408071706071d04140a0b0a0b0306010e010804050f1c08100e0c0a0c0611040512011b050a0e0d080703030c020106080d110307140307 72
    0x598040720304802c54046da142000300518009002812210005014510116400d04000402c01030340d4800c09000606000d5000d07205103490030300d081505400c0003c08101980080e4208106075400c045102942c0c540008444005803a40c0c0000b8001c03c010700b18180e6581e042000c1c05841800d55001d07969521090303583c0c10101d40c840b11001c4aa001c121003042c0040d007481a4091194407400314150464454801c881011128544032810400800070901c0c205400d40b0f0303c0440503500882c0a9009601e80061400f0182000704200005d1801010905040c800040071414940310700140c948494000c4800c000224007042c4800285c4d025104480c89000100348000100b02c0611882e00100e400440c8104024042981a5059041803800c40141b102060100d00c040c2c07a05a1081c4050780700f541040d0392020302e4074018041b1442d0a902800710f80c034040082c400c20720700013981034090300031341003968504000418451451182030300091170344502c1c0c11210005e100000182112030b01c5a41e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 40547630 1250 40546380 40546397
    0x506010908030405061e0406050a021204030c151e050903010b0103110912030d05090114010e090705060c0309061605010c0804031d04090615090c02190b090f0a05070303 74
    0x1114103201a010307514064204000400907440e048000b404c18415405d212200e501c00ea8001c00807035006075101da0081080050720262540c0c2c14040390228040703800d46242810b045807194084d01e01c06010f007402c40b849072841d46410314015503c084007559809220310f50700c280d9100c02401c0c1e4108070790075070007507080583c108529806405141201c41034250ba4038281528101004128809040780c041940010424400180100d01510b44103043c03003070010074040307100c3d00c0318000488140d00141d46401c940080c002c0300c0c01c0104011045400885809403504039413820241984a204d189550140002460310f580c25a002c3c03d42c190140640001c00000c00c0120094036009000c9800a0018207640c000011400490040350384000025100044101c09503a4200072200c01c82c0610382d40d804120003c00504401340140e40400d2001e101070244005109078403003c6890560001f408800d4220010365040010003480400740502c108443d1303200d40d503040040d101e4005020560000742c81300d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 40548880 1250 40547630 40547641
    0x20f0a020c0906100203030604150e01270501051003270b010f0f060f030c020106030b0c09030615010c0305160b10030c150507030e03010603060519140405060105100219060c0305 78
    0x116100d503c40107890300994910750390b000410004200d24100660903032b00000011640724002c074070080c040d10324858581c81700801a80001030f02c810800b82061074074100801403000e40c44a036852103104200f07040c0454410002a041018107080445070804104881d104000348001c410800c0d040f078162001d000703034044c1c94031301a041c83c4400740038290100f01420320907521a40701743e02a030b8409100c0d10000455584175a2903a1070700205468040d00442c001c50b140200c0d14003030040607044a10202c80600d24a1700b0310000c0d25000f140540074003401004502c901c3d01c1d0b0459070f03c01b590250301101103129483d0809140343d04583d40c0c0810381c0e03451250703400402d0707030360000201c00c0e10301c44c150312018207084007994100c480342c1140c10525015501d4450000014115009150007580a155070726134942001070010102c40a1524482001c41c0802c1440040390b00441c03400d042d164181d800d900d201c0800c0d4010380c50b10314400100d1425400da00344440500c0f5941e4050140f0281583c0c0c00c1c807494031030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 40550130 1250 40548880 40548889
    0xc0302120c18160c03110d0905031b010f11010e07030f030801060e03030301090c1b03030b01030e2404051507030f060e04050d08090a061803030513080306040906020f0a020c0906 78
    0xc9442c0000303050460300316030049004a6211031081d01c40d06c1e00344c0c50948060595402d001c441c1c610980401c1c441c00c8188031604d418406803000c0c003035020701e0031082e02a0400090a003a00f140728403040c040300c00710030180c01c4001e4000002d1340c03546d181200c4250707a980c078002c4030f488100c203000d0380054141000814000d00c100b81052203118010001c5080d6401c20035600010030186085800f8400740b5a078840802d010a500100e0b102c0c00380e2400201c0b00482d01c0058103591b4a115582c0b4982c0054a003c0c6803205080e861014821202030030719200c1c2d4440c54610f1410002042c014042464182004011a07140d0412545042e00000611010340e6680c910200c10030151001005a00840b0325210114170484280d640420f000c41100d05000b41340d10f0340360490f12401820301e90141c000c80c030342080c55098060789412104982d048901035119480d414214000584003d204545940212003400700c65015204041c45d4141004c1e680c02c00d01c94040d5440012400003801280818009410f6280 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 40551380 1250 40550130 40550179
    0xf030c0504050a030c09230106080604060510080402040f0b01080408090406051c0c06080108060f0702120a091d06030a030e0316081c110c040e0a060c091e05010504120c0302120c 78
    0x821021f000303990390031314405898034007000306519045942d40500003082e0717840d5001040e00192545403140c2900b410f00610094030480c080e50b02d4841d080183c0e55205980c00250140d0258000c0d066903100c20303900c80002c010300401c1d840035510a2003007410115908501a102c8111441a201c4880340c60b600c91003601c400313009100f2003242d074001d4030000c1e0304800c50048142d4005985e1050310030200c0b0304042c00d07000781c22501800000525004040c030018000d100d0507103580e100303103441305101e1820780006a50341d07103d440d005040000040040c82d168404100d1943c2d2408894034158555880c2c50381241d999a01f620030312000b480c490403510380517001d1060484041140000380c001d0905a0f8180400f510344200c030110141f048080740c8021860a121f5690403210942da440d1046223400d03120408125140c002c0500e82000748001c0203580e03000002c8034120399034006a403885013087d00301071100601c01d61020303400c03440c4e0000900c00c450000c100c90140034401c5603050120b80113040441144c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 40552630 1250 40551380 40551431
    0x120f05060105070204020310030203010f0b090901111e04090c0507020f04050709050609031903020102070326151903030203040807060e0609010c0f080c010605090a0c0f030c0504050a030c09 83
    0x802c100040c8015040c95001554401102003102258a0342c07513010a003140d904040f4800410b940700e10352441d52400c100b405030418080c000030f21800d290645022502c3c402c45500c0f4207007480c80541d1800c0d0400c03450651700240180a4100030000340384d800909143d0248104902c5000c85040421151405200b4140107411964407000c2c504c0c00d00e0203007d001e44c0410600b40c0c2c540300c2e02030780d00661070320f91012a072894401d038009600c0300c0f400d01d0040c00b4001504000c0c4c043c2600784c612040310704012050207074000c180391f604011401002c8082a0008244016013040018007080407040c103400200070400c0710700130001c80303880d1035a40c00110f4500385000ca000340d1080341040b0207000c0e58890309900b00c2c2c05000740d0061a551480c0e944489140d4403440a0410b2030b51508410000317450310504450340031304200303401d21110b000c01d030000b002080b0407905141030560b070b45154440da07403141050b0b401400b4003800003001192a4202519861114030503109040d0a1110f0b10b00d031012000e80c0c05c10b248 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 40553880 1250 40552630 40552637
    0x9140d080f0c0a020c13181406060915060a0903080c160b0a09090207050102040b030a09020a060507030c14030c030f03011403070b0406030c140406050c06090d1407020d080a120f050601 81
    0x100c0c4c006c100d0f01e0040000034440107611061049200c9001c0c0c403034180560b202e00070004a0028941c211410150000d041c1d40c8105044020001c1d40580a03400b518584800c41d40c00d6655400c1aa007030302e41d040103400182c0105408070f01c100c0072490000c0c5500c0c0d07540c0b07225802c0244c40d64400807902d19110700c000c10000940c20312010460201e594016000640c410000541042e88032003002462780c00807200c10540030b898100c04001d500709085900041c0640c7d140440c40e000d2a5113024010340965403004000800b1181c400315526414010b9440c41c201078420b4a90720344100f44c0390a101d401c00c1c060205030b500961402245450005911012940030b44c8242c0d0520b40740100aa009010461158080c00b5480d100780d9159082ea40051010303200c0b03a211140c071142c0a0000d079180040051502d80e4580c0070f2801c01c00c6a54009a160b015282503100f01e6503540c02502c00304000c1400054003c0c10280049140243c0325008a030034411203481d01c0c0200011075003416448183c8009840c00740c0403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 40555130 1250 40553880 40553893
    0x18050f01150507060e0102220e0f100e040c05130207020f240f13030606140d081605120a0207062d030504020303070b0c1809150409140d080f0c0a02 65
    0x20b812034000d480320320405000181010303108010300e9900c1823001040440d114440304d0034004110203032142074000003000410016450030001c0041c8951040c01380d81d60300c110802c0014208890341302c2d00300203002d0240c820002c80c541d1413001e0001c2d400c1002d0803441240ca00744c0c43c0040341454402412000d00d02034a8207404c0c1c7c40d801b8140c50b40d501c90303d090000140204412100101402035030001144501c0f800201c036464141080320606440790703014400c0a4800149011440c020103544020031054100b800c03402440c42e003e03141040a00e00d80786401c02c00306900748800d80100d40c44d01114400d40300d12400300c68105c0c00350040a2100402d401210a0a03282489144203a000390382c041d1000c6e0440b0b10380302103a1911047d5603004c842c0b92003224400104c540d5a400c0d035250b160350258094644540709d0920015149510300703155107140c0600d41d50354041e0700f80140d203007050350410f4500d0241c82044110078002012403008031001c020880064000c10650100c54040300d95140780703a40a42003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 40556380 1250 40555130 40555133
    0x13020304020d0b041a0108010213061d0414040201110307080d1107020d050c0420070b0417070b0402010f0c030e090702010204080706020a110102010608030403060b060418050f01150507 81
    0x25080904141d0b0400da101d03054500103084503101900640c0911000000340c06644030310115030805800a84040e4010300210141c7d560200044054038180d0030013015880300c441c00c801d00007490404284d07100c3d00313102096030042c1180411902840c000e0f65448001d03410400280c2c0c1d2032040702801007284a0400000c078030700219602444881c5244a0320500d0300d0b02c0d40e00015004005482c00b0740391a0007400c8502a9490035216040d102824a13010481281d60341d91459018003403d030000e0103020740d0340f001504101d03061030020700307011450a8064407039007182410b840001c0110360480c04a00d0307818a040c0c0d218050010302c080c40f941641c62160000381c1e074040c8101c00c14090020025036401348000b2405071410f10050025000c540e00510b01c3c20f1075400d2070a0b08260440019040d03900d001014450f8100120844054075003003030022540c100480003040c2c8505c076a901812040d4121000004108016005180240031548070500941d0321000041d00c070108424044010843c1000f0440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 40557630 1250 40556380 40556419
    0x50d03091a0d0e01020a0305100f03140f010c050406020c0603190c110303090d020709051006050a020721061a10030b04060806010b03060111030c0c04110c0a08091e 72
    0x10721001c0c01e01c04a03040098541215040c2c807101e030090040790750080356001c0a2540b40c442d280e8888000000e078104180350204d030b240046080c1c000a4015008449402d0101c0c0f0100480c41903a00d00800810456154420041140d08940500b44c018043e554503802d0610704941a6409440429040040c8403c40700c40000241114a404014407070142d503200007251040c0069031007081c0000103003d0f69404108024105802600281070080c54842480383c1030140c417900105072a8103003082580d4160000f010707031600d0b002c0e03444250392801c1203a0914091648205980071148914020b01c11100545071140c000170000822540117028401c0100d00c2d244a03400c0100802c1c03001e40000342c1d441e201d0743c01508002d000d8100203000e010010a022003940c0c0f214480070711861140145041c41903461413907880f5580f8800d080d10650b00e54070b06d42040848101101c1000c0680c000710703005c040903860b042200b9001011014404c4000c0c0d80e9041e50485080c2000034510001414070f0b080180204185 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 40558880 1250 40557630 40557659
    0x30f0f0512040213050a1505190e0601090b0d0b130902150904090f0807140a0b0415020c0f010501060311040605040506180d03020a0c090606080601080414010612020a050d0309 77
    0x580c4d224000c411004110304030741c410382d8080c460b200804114440e0304c081105071810343d80c0c040ba002d200c1c181001e4003292002ca2040d000d482d010315100060b41c56400049940000f0743d081005051400100301e9548120f90f8041440c0403815584151303902c858803850b008807803404401070740003281c035980b80e0601d0b03e40c0030041042d00c10083c4000743d4040b1a48138451f600c10011390460303013408001145003d000000c0e00d100356203040003005000358000ca6031001040c042c0980000c20042ca0f02601044d048490740540300590144012a6040b103000300465028007020f129070000f02e8a060400c2d58620000000c40d025107400d0f884546c0307450702d00400d00229070b06c90b0769080507001c1121210000c83d614604400c000c1030107940140f14404050511084020050303100810040c5401402c000d07098100ae46a41c0c44042401c0c03165150b030703450401400c04440901e04201551910070302080702d001e0760401c010028002d580c2c03440425210780038000c804142c1d5032b0103400305494110401c0084004001c0c0f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 40560130 1250 40558880 40558883
    0x30305100b0c010e0c09061e0402070204020a030c0909110417010b03070f030b060303030403090e10151101051005030a14070509011211010f0e01050a1803060504030f0f051204 77
    0x818000d41e4800c000032964000340c280091a944a10340055110410014031101280494441d8018100b00c00064403100408400311300c03041070300b40341c1e5449959a80c140c1e180142c01070820356a85030001c000800800d200034442011801243d00410610210b209002c5080d5000070411314103420900212032040e50240543e20540d242c41b102005500d0a01c54000245075a6803c5a030841c210318007200310010042c0a50b000398000d00c00c2101096111460004580800d6061640c98070743c0d000c0864141e203660020040709030f43c201c200d4007940d8089400300c2400a844000c10540d11520f400c01c2d061b1000384284c1d0792682c400c11021000c25028403001c2c000441a1040342c0805548102050341c1500c264046d00d040c07501008081c0a04c181e0030060707800c801d07003441c3c60070202400250241040d407650141904100000c40c0307500b60b0701c1c006d1191007040c084000d80080903640d20301d040800341104a42c21000540d518013003040b10303030192041d200400002d031106820b10410803400e8540000c000d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 40561380 1250 40560130 40560151
    0x16030522141605010801080a02090403031a040e0304061409030d3507030e010e120d090803010305010c02160e0a0f110d0b030106060c0b1302030102040305100203040c050d030c030305 80
    0x360340c00c401040b00303401940e001102c1d01016490600090311881050b8001482da40140100d200103956002c0215403245e414100040c0400380c00040c4481c0e455202c040b29040313841d260580485810000241c0304642c1156100000c00059198600b1903000d998803d035090362206000d0142540550108104080910101141403040318281d0020f1900c40c00034000c2c1a400f87c0c248807007254140035020b102078407a0700074840c14084041107540c465883c0d41c00380c00c2800201354403010301a182c002080c1140c12040489d2a07584906100e8001e002889400002d8840c00e454401c0044d4208050002c640340d4803c00b1116035034181015014020044200125942e155105101c41c203040c0c010f060382480c490300000f101010341092500711010350700004240503203115400b00041030010080d40c008589080745111420900c0841e01a01494000806034051070311080c03c180c0e015409180b01d10f01401c880b041c7d95070b559085c0301e11130201002c05000990b8804000020a009801c40750300442400c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 40562630 1250 40561380 40561403
    0x50106031104050f040e060f010513050f153601210305090f090106020d0f0e100507050a020301110c010506060307080408030601110304170c0a080c10030f060b0316030522 75
    0x401c00741001f00848885500707a403154010304c103030304110400e000348002d40d04003049581083c102d003441d001801401d090318104102600c0c07845441c0c0310407181000c100c54048030441000c0750244d42c900700301001301c601a034260394000201c2d6250301c1c0142e081035180c0005401c4216207a24204c4281d48450076403a000079104c0d0801c4c9194542c00040c5000700003607400b401c0108116a00140300e120200c400e04200010314850318416510301900104218071070802c0c40c7e480303800d8a045c608040c01404043d50552030244802c0c44207507150018080303212080000c10680d91620100704840c0419183c031800249141c0c00900001c240310015504014141000000d0400c4501038907d558003d030072489a202c4182d42041401008014000b007000045601c00c500c00d080006080d83c62a034050314030301c9040c8042c620075911b4020780c010240010030700c2c1c0600181d81c0380c4507040b20070790003680c803041984500c402001c4c240d40700c1c2c41071b107015010101c1e20850070243ea184d224040030000b41c0a485001c00710 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 40563880 1250 40562630 40562651
    0xb0d0b0a030f06050928051501060201050103031701080706050c0f07171b06030c0307050d020f0a0807021f0b0a091404110102030c03070305031308070c0801050106031104050f04 78
    0x411008502c590300c00d241a10940ca04141030304c402600560076a40b000c031600d550151046424100000c1020304249000000c0c1082450500c4889412410b5100c0c0c80010032100c2c1d040d00164182e034025156440d09032403940b00c01208440074031400c07601d0f4221000c140001d0744140000c1545156110440302c004481035009803c000203940040c543d890f100c2e07a020503041090051400e00750f0781d4203010301143c60f0800440c40500c402001030209540006c0021006070244003952001007040c02c08540f00c01000c144a10701f9400014aa40400c0d51040010011440040c03100510742a04008001d02c050000084014141991250303921080c082030111f442c02c00b0b07200724009040081c0b0b162400c2d04050500c08905029801e50b1030440d041041a0f0f0084d290000450303025030f9141c42c11540e20307940c1e45990040c401821030010450807000401200740a14810144103445105000b0070a0fa641c4003415821200d00800441000205000400c4145005015024080409040460300b01c041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 40565130 1250 40563880 40563889
    0x90515040507090e0603031204060c02150903040306110c0a0f06020903030a12050702010c05070f0204180501090b0603070f0b090a030b0903070c0e06060301031e0b01060f110102090105040b0d0b 85
    0x110b4080d800070340084010072000d02c000c1c2e01c040c1c0000050300554038248a2078010f03411500003d2010b410b450319641c0c003150980c401c010100c103e0210642540b220f090019216460f070f4400e100503241d150501d400030f26408400d030304480d81010004028141d1301d40c20350f9040002d01e4540c0e03003910070303d0342404200c2c03c5480c1440100f1224109540f04068030390743c0207000040b101c0250010046a150007503c031000e0b90441c00700d0b50300c15001843c0c0004540d036840054040c00c0c00d0b011102c80040240011410070005400610009110f00c40709034a950f41c078800c1c140e0750061440f4510800b1100501045143c1d468402401d030441c02030300c02d810044d100d40b10742c41070080c1928007a01640c00050ba0340c0520078001c6000015104542c40f5100e00d05107000050301a00041c000900458140c4006000d03174440300c813000e04040c0d48005110080e69407000054031950f054055600810b66141c85966000b8040c821100610016160b05081c0303810700c00030381c12a030440e0004c4a0080c0e55022040d20580d06c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 40566380 1250 40565130 40565141
    0x209060d0602030a09061b02030a050c010e011d0c010314060111120307090e070e0a090203070c0605090304080106080a020d1101020a0f0b160315030803060103020f041e0503030301030c09051504 85
    0x80440003045c103603102d140500441e14500c0030702211070350f01c85401c006280e01008a600600403480c0079912000142100790050858840c0e0502c150b00c1c004881c0d170308054010142c440341d00307104103030b405051411005400755068621035070218060720b000540d440d130080c40542108480303a0125540c0c00240382000d01103503c1030f5125400300328002001c000341020f1000d00c59000003d440d0021101050101069482c6454064440203940110001d049684580c8920100a41104061256051070529152aa032007400380030680e5003000004a1070040003d0091952a07001d8075400d0035040c5611000680c00c9840019411402803603003107008102d00b41e800d112610300411421096081c092816000d0128485881c03007818101a049220854030020360411640c20002e020768a40d551030040b4002c0c404d40f54222628500410041200b101c03914440013050000141c5541e41512141007580e603010034070004100440ea920144185581c580050303400c10110480c580c0704091040c0001c09842c0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 40567630 1250 40566380 40566391
    0x20a0507120b011a03010302011b02130b040e0a110405091c021501050f030d030b010315170111070f1e020a08160b0a02030717040521010c0201060f030209060d060203 73
    0x501d40c1c619401030000300880c8a004107500520b82c000110311000050550205110207810301c22a0a040075000801115103540300b6802030004040354400080c0700c0051440320840c0b03004134585115065000400550102060b801000c20348a1a075400c0421003d0580200200980e014010401c0401c00050104d03014001c0c241d0080c04280f030f42c030103001001c02c1d0f050b40500d2242510900056250306c01045801d502003ca26010515641c00001a005070105c22100c3d05000201c1e2000221064046003819001030b400000748032690610b08500b15038041c00402621400205504100149460154840000500c0c40381150380e40140c00142040a880d8088070042d0441030b070200e541d240d1004014058071400074081d040c0003481c81d0083d580c4c054050005c0102c008000d21a05a0147d0f806640c0102402460364442c0c044415044038014400c00002041d58240021380c0003550042c0a54000c5d5644000c07118080f500d16001c1040341c0c01c02908413900320b4188542c031000305003c1e000651040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 40568880 1250 40567630 40567649
    0xb0a050703030f051510031d0a02120102040627030510020a080702070e0a150906080115060504050d1709030f06010f06090b030a230109060e06060a020a12020a0507 72
    0x9100310309002d020766044000c0d540d060f07440c0c202001090500c8040e502c401d520142c8560354200301248042c0c1c0180102e000c003031848028644210304080c80080d20b4415580f00341c07402d10f0304640d4081b1a49c20b0780194050200450201da291148a074210032689038a0b1a44040c1c1140e107640d05d881d800c0c10b002d4013078054000c4070340000707000d80f119400c01d0480b0340240e03041c80244041e9141c41d0400c90402e801800c125003080c0c480202d43e108107150070310140900140041080580e035618096802030000e40c002d0801e101e40404000b96040c040e00c240c40880d200902402170b0744c2c625a032910492080c48041401e030309801c0c0105602c0d501c08010040028403018001e04995040c010210800c030955800308041000b408401c0c01802610000e07641c00c1112400007144130344002c1d8400c40f034810b040302c056409210100c00024100c80b90f0b0051003c9407844100340f103041d1162014004a07115071345030200940d00c140401000103405001d80b42031580b9510568808070b10039694035080c4241540800340c034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 40570130 1250 40568880 40568887
    0x30c0206190503061005031608060301060b0309070305010c050c030405061c180201021c09090905030c03130504050105040c0e0108061f0306080d030c02062a030a05070908060112080706060b0a05 85
    0x444c18545c032402e011030b4440c1000303030952030310725142c0e00640001c50f403440420860101080d0303586c40c250000c001030440c20340e2558a0b80380680304190303200c1d89484213070351a60810b40c140072103074059801c0300c5600b458400554602414001030000e540d02118200340f40074404104515a550603101d014401440f008004401c040240002440e241c03a1401031114446c600051b24101d5400c070700c1c90400c69078440700c0825a191241082400d5004000c0c1050b00b5000005188045441c00c1e6402c0e0141d50044404121350790f00d03001131000300c0c2e101c1360010303020840d580ea00c44801d40c004c1354a03d5002d00c001f424900b401a803000c0180720201481a00d4010a4880e071090101107403d2290340c002040034601080301114a0301e009550b04409404505195200002480010f0442400c01c20106503a4510340e501c0c101051000c0050400325a194005541e110010510481c045101c0c0d0484090140c45600c440480c1c4880310315901042c000c9488560baa0400201e8079400c0010b09180c0c841502e401e5107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 40571380 1250 40570130 40570141
    0x91207050f07080304050d170408061303030e060f0c030a1506050c060606130501050309190311061003030e0f030309030f1f0c050d09050309030708070f080303090307030c0206190503 80
    0x2502c0041e070089009034105100a0205d0b0700c03050042180950810030018640c0e0141040d2281e40c812038200030a2406290100310f50075000240c200d045510a590070071440a80d6100325459000644542e0540071954010480001c0d130750b006190014020100094041ca481d02e10070840c100d00e0740400302140c0042100c1d0002c2d41c00b4084980d103c1c41c10754840d480d0a060341403000065802d4010030b0705022011000c600802020071a00398140c0701c40440300804040c0c2c0c200602840409001240d0511034140051741e4a0300400100c0c00700d07541521100415080031041018203206a01207a03090b03c0148003140a42d64104440c92800c0d0105000d001401d0802c4800e0150348a003004141e80b00f41000205204540e00104481c0081c405080000d100c4081c2d15042d4210f1140c24803003581403240705070224401c80d01007003000445101030000f210b2140e4402100762a400100d54802640d0814098000428041c0710605240e1788002d00c41882c100b119510580180d000400c07160016001004101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 40572630 1250 40571380 40571383
    0x1080607090905010308040b03070504120f02040b0d020102060f070e09011410050f120403030b090a05061009051c080c070902071a060904020103111c0515040612030503091207050f 79
    0x50140540c0b02c0203000d2903045894001003441540b107803800e62030002001031491403040003640c0161a541c0000e15480c101414500701250520409134407462a1083c20101880c01d500f60082007981a00a80340341d646410303100b0503071040248050b0078041d0101d00c1090076502c81c40d0b0b0502070000d010048810000000c00e00124646454035001400400c20041160350500303019a401101e0f81c1078202d209941e00d150440c0034010103244503402c100007406002d204d414681110380b01e01001d0380c0310100009001c000302c4191415104840c1c010852990031029206102c071016103950003804003500e4008805641450484136a00c002c42c4254042048010080c079007601d01880e036111603882180d4140080010000d080107480241803565401407103642c01490000d440303404003044481152850b0103a00c00d4041c0104507903c0301604051850352100349014480d68040d14400020000103540c0380ea0180ca0541c00a800e074401c521510580c0003010050b10000e049503031042c000380903003054064425 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 40573880 1250 40572630 40572647
    0xc07080c090108030f0a0c0c0303080a2936070207050102150c0c0f0601090902010809010606020a03050a1205011409161209020103020d020a050310080c0607200901080607 75
    0xc030711501206004100320700001090f5200c410748039911030765920b0041015556034120000081542c42407400020526030000c02a52060051140034055801c46140c1412622900e041c10803070840e403076007113040740e041540480348035a84a0700201880b400c2c4180c407c0400c803400c00e10b0340804182800304045a941800b03104010182800100201c00c444902140b04000041105901d054046041ca0b02c1150402214600c0a100130a4401c1541c4a04820000c0c241c0c05006030b020521050215400d00c40510910003254060b030301070b2500719040c2e941202ca641c0103d81a004126643d0341c400c942101d40c2c070400d4000c0000255000780310304228280305074928010904480341303d544c40b0f107410843c0c0040b000c503c42522400001041002c80c8010380c028014819504500e0740301083d07000500d6000700080d40100d049081d000b003141c0c0c0e83e90390181c2d6074120601c900e800410a200e4400044c0e407040c42c44107034507018082c80303184100b13006c0411601c000907400643c040d40081c06100d075194201104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 40575130 1250 40573880 40573903
    0x30201170c0307080903090d03320304170c0d0207210f031112040905010914040f030503040602040b030a27030206010e04061104060513090b0f0409170c0708 69
    0x5403011440c00702100d4207140001400c1c030080c802d46400241080c00184225050850010004028034219042c002e2110410780f2400c65040d602c0310a868400c080c402c81c4091111122454601c0d42c0e80e81c0d9602841680074104040c12040180042c1000074000c0c41442c0200d1540e9009029080c0f40004440301503241000400b5100550115600450b290364890011590107042802e84081c00380c08003850300ea03060081c0d030b0700b400d000b09001ca07013042c050304030034101c0b08929010f0100c406940202400d24600ba900200500c0182c40c144e00042e01400146500c9401801c1c0142442d1784d40c081c513041907000b1100210078955503125000d1a100c038280500c0f616030030f2001200307924216600a941d4080c18041c50402d00718080018080000d00d411021178111080341841d2299a10316003d01590008a004410402518008140286144560000444001d210a4100d40c4290900c0001c010810060b10400101403004980c4c890940c0107290240d0a20b006100843c5052140350906201c0d00b035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 40576380 1250 40575130 40575167
    0xc090118081023070c110a03050a05070501050f0301140103090c090c14090a06140c010606051207020102090906010f020a020411040e130230070b04140306010b04060e031f0501030201 80
    0x3c2c044191081910700035070002890034410300303a018a0038070007140104188025446050390324088101300340030070b4140303145118404807004a80c50b0401501c80340074526404085030300034001001100b81800d020400910181400101403829031207000a41d0441c0e04092201906e55201c850303901c1d400811424400380078200b0f1814402800005030f2104c1091080d80c1c2000301380441019282701031400c594003590b2440c020071280d540c80d02c010b402d6400081022100800d03190010780c3ea18010300840e201c02000070882c0341260386900064518000c454120002c5101c0c8080107001621588140740340f80708100e00c00c0b920740b480d044009214200080103044c03140005410b2000503220b065031007c4000818401c0028003c1c0c1d80d06144100c1118031244500307220b00c540024021004000410690700004103044a2034040000c2c165a501e00b849802d038907540400041102520402c40d400c200000202640d05502152102560306560030300750401065407100104115030700141300300d02400140c0d2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 40577630 1250 40576380 40576421
    0x412020f0c1507080c0706080609070203030f0103030c081c0204080c0105040320150706020d0506030c090a0c05040b0c0d020d0206040c090902040b0d050c0a0f0b030c0901180810 78
    0x100403586989900d000785501c44400301d60f11041001e0181039400103a0510211410795a84400041240c54241c450b580600566000719030311510102c1101d204605040d4030340d40d242d1843d41d003247c0b0b60004030419102820705018041c403030092090142c00b00c2400c7c80015860303034200b104450a20b40260111410302104010400006803802035060f88480594000e001500342900480c161102801e40120400f10004103441045081e0340030300a0000c2040b02040159200d2050507034440200710042c0d4000d1400300041e4143d605504903101590492500c1ca0501da41d90341d01a50f1908980082c500a401820407a030440e03504204407401d82d1640d01c02060b076810706403182c0c3c0b00c4400c01c2c050800f550341c56444150641d1102e0304502c6c0180005080c4100d407840310b04006807030b21520784034140310b1750b203181d400100d00d101d114414007640c000c0e40b005490f50711344404402c071030307806145a079052105040e8120003490a05202000800d6030402502c40034604a00742c1046481d031407071030300c0e000c00c2c0c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 40578880 1250 40577630 40577653
    0xf03070f02061f0e0703020c060712110f07020f030106050d051c030b060f13120f06060b190503060a050a03140d030213031b0504050a150e0708220503030412020f 71
    0x7891404103d0759102241c1c078581d205d140c001c9020307100c0d2034424036031441100b0511444550040b404981036501c03520801c043c0c070250520381c0041c460903a00d00c1c0701000900c0000c0251420144191400703000400015000c0e03036602c0401c00252030b2680c00d98003038001e41c4a800b20700d421045100312046907890200810210f20000410038003500e0b0f0606044000480c0030b101e01805500482c02138203122680b50b8020b401840c02c0c802080302d204049401504000000178041e007540f007500c111000010401da140380c0040002c50701500000c1142e03030720280d400313000582500e410b002d05000d107008469189190340900c40d140d10b00400d14110000309031041224000401690521509482d4055140011000248815a0340b01e03c81e070002035115160409100107581154401011041d096082c500b000d90759855170008258100c40b6040450980800109a0102a06042007885c0a80420040030080c0d03281c592558000f158211500000203000f04041c40d0100458010708a4210041030729400c0c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 40580130 1250 40578880 40578931
    0xf0c0a0e040b100e01090518060105030601060c0204060906080a120c0302062e08030a09060806060405040e0f0f03090a0b0309120306041d0303010501090e0103110f01050f03070f0206 80
    0x100050702da05124030106650030b6070307685114001d08500101581558503404504002c05040d1803000016860211611210b00003080d1a070480310010003038000c603880d211048e2040d1100d400220703803180e503400c0d001c645c0580a22920001c1c028040003407907480c1381880e22601c01c0c001c100400301400071910b046400607500003000e55014069211908407441c80301a1502907119031052440070021641020075a10800400340641c40c026070b548a00300f961b140030582c0c900b41e044c2c80c00d0b03411600c10801030100e0b0905400281c440707094135044038510400001405d00b842d20003541801c07160030010320885180341c0b0307141c0880130b48840d0781d04601d541040f10340907544036074100449208402c00b00010b0741541c0c4940c007801503078412510902031504034041141d00da41c800d005140c00714041c000003041c0d80c00c49a01550503a41d100c19029100942e280401c49000c007001021f50403c0380800c00c00b9060f0b04908080c502801094070345611b001021503001e0300740080102400a244900142081c8030300b0b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 40581380 1250 40580130 40580159
    0x90509030c210c0618010f0216060e0a02060f03010306050604020f070f0203070807030b040b09010b0d030302070204061205010e0f030a09030209060604090213060e0102070f05040c0c12020f0c0a 85
    0x4a440c00c400744440d14220b451405410380f02080e80c01610204080c00f5407a402a80b4024800e40003080083c81ea010007004074041d00c8403204076800080c42420000e60544d0000c80b1703900c91901102e410f14180e1b80092034590025031a0b2504410100041041020a000c0c3c0340d0440404c503030550070611042c00460300e60042a1014100426549e00d0005544082c0880c1c3c026083d4030042d544141c1e00c2e070508200f0042d051b20100c07040d0703c00d0000507440a0701807198000d100301c014500d9054800b00d0300d044001c1d4000400c16a4442c1d81c42d080018015172070281100964801c200114040103c0200981400e030036800a120a030401c10a40404a60011010041d039504541c0d0141c03644802c00461140d004940084184910002d00c800b84400243d8003041210303415596030545075812401280c40301b0084c803a004280701c10003024806490140c0110a4444041c0b500d07021122564569a8240100d01e248401503005400c0d01c4039010414443d0300c0211006503149500d0078a0000e80201545 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 40582630 1250 40581380 40581403
    0x60204080a121b061515031a1021020d0c0903110f060915090d0302330a1a1f09061d0d02010507050105151807021b03030c070e01090509030c 62
    0x140c3e50181c400f21140044c6112019210f00078102c542801d084070007500a01d903e801c8c00011040384050280342e41340040700608a001e06582e00604001702d00340750001c4040b80d00040c16600d8090001d01c2084282e88100c81040d42642e50307800500d0314504044102d03140c00d000d103070b00030155016141402c0e240c4404990340c05000b0359110f15486505215000300740180350403e17502004400070042450742c00a90b5055003103603482a0f00e11110140010641c02c061031043d41c4202c04030900003050442c05a215003d191f0b010411000c3c15405400050110a4820fa80490307013100400080f600a50104c41000608500c0c01c211030f5021209440b883c4c40484030b1181c138410720101d001c0070110b910641c183c03601668407074001e00241c28100400900145a041e0941c01014403802d02c0003001e02800ba954064100740c1c0161070105840040c1401125a4041c03c40d0184420400d0301c0c0094001c11000004004c44090342905504007203118050340d41c042c1812072954000c2c0f00100030801d01268511104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 40583880 1250 40582630 40582643
    0x8010507092d0b0c0f060c090406060f210b1206070f020c01020c06070c030f0f020f092203090f0b0306030c04110a0302030403090b0a0804020405060a060f080406020403060204080a121b 81
    0x41300420301451900507590034888640c081c000511000c0c0c542100a0000f050044a050056986580c801c440700f45100d0345000c002002350b41108210002d1030940c5200ca45a08030108030004d0346004214a40c3d44c0109144ca0380d840b52003002740140d40705a2440c03420b2490b2029224843c40078000175912640c0c04038180c424000021610704018900c0e500d000215032001081d00941c1041c180803141c5082d0f00000e0340524440311508906103812844e01c0e108007a0307440c25041c3d10380101c214000314094403104074180006000c02041c06052941510010b0490440d0581e580ca0444141420004814802400f9030300341240310b210703040300d24162000c2035218a001a101e03500c5050844107400c040c1d00084211800042c0c02d032020f07511600c864030850003074070244140d4498101b0300c602a82d543c8541c8000640407031000702170910076000903030824010388001d41890740782e4a81400f02d038001e900c6940305a0090f1541030070001c00c800c0da414103004504000422048041c03040501140c07440c4001d026 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 40585130 1250 40583880 40583887
    0x6050d020f04050a120506010b12010306020901030e030d020a02120a050307050307030902180915040507050609010c060f091205070308010b070f061e0609020403080703081008010507092d0b 83
    0x401021a068400520001348001c41a41e510003040080c2c08a9880c15103003409001e00102d0150b444170201c860840c0e01c2e0b88000e03541da107503032290300094010310102c6040540340e0110104444081020300440c14185a005030b4034031500d44003920748991300c80c81d041d02c808184000b83d2051741003420b13243c0c8081c007802c06517901d03078400d10120002d0801980080d4051107442c40510301500c0310310400c0c03081101000303e80c00744892005d11030b090681264000c02c036510045007440107082880181042c130f1818180f003980b001282e5114401c2c0c1d035409103480540d6581d621501c0a108101d117068034194010304186182c035010740c42c018414103050240b031a44c108001203003400c0001c403031405070303850b50044420040142030a2188c0301070307140c5144d00820103082100200302011184201d42c01c40b6400f4404500d0a000c540d405d0314800c1c0c0013450802c61055500c40001e404500303005040c4070300225920f098030281800d00307032030300030318009003401880810310402e22048a414031080d00b581c0030100c50585 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 40586380 1250 40585130 40585147
    0xf03150c03130c0e010312081003030e0d0c090e010605011805040507090503030a02011b05040b07170f03150103140105010c0f020316080c100c0f0b04021f0c050705090106050d02 78
    0x21510010802003032048240342c0000c4d00c00e1003614250689124070605030281e156060126a040004e96030626510220341c0b040001a0003581e011200c88400f5000c500c1c0014940c5503050400d505500820740c00d81ca400180299401c02c0c400c00b005400c0908000380041c4032002404400c1646006890240343e940000c600c0060050455000070200202202d42e00c1c0d5218100030301820144001140c05000d81e101d1150290207401501c003912a00d05c441800c212a035202c12034001129020041d965000304550040750b1203040046102c3d00c0480003030711203055148001411102100342d46103181180c000140032980c2e2101010415a80040c2041c02d00f050798000a82800010788001514106080f400070740140d0118500890030070403580460261482c440030345095a940c08014600340f03841c0303102000984020001d070703081030000d40011018000c1c02e01550014005543d82c2c0003180402c84018104034003002518042c2c00260b620f290386514044000e080d6002c0d41c00080e14690b0080385005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 40587630 1250 40586380 40586401
    0x9180e0a0602031f05030d050a1209050312040b0c0405090403050903100c030c080a0e0c1002070306020708070b1e01140f030111041505090f060d020c01090c050f03150c03 75
    0x18041600007070115501d081041d035580f0090000c48038281010414440020f01e031401056400164619880740f601d000c4000c038040702d1849000040a1a180d5100004804904200080c000d20f8012005a54250803c3d0402024891f00200549001d0324100024091391312442081c941213940b505049482c1d20742030380020b051211101030808110320300290840d1044c0c2c503070000c00300d001054540c001d46464440d001e20540d085124014090350005107009120b08000195020050162064a0070070b92269100d030b042e03901c044015160317480085400304c01e1004224420380c0000300541c00b428804034061402030003601c144550303280031044031690181034940901c2c250100e40700500800c03041e101004a4800343e001400f0f000c00c06449a100340f444540100101c61160740c004006103052074001041085561102d004208416002d00040403040024029802032610403180d401d8403c1c14602444003d003a4545640c1c03003031323019042c03200032035040b6602c060f003101104011690380d50b548921031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 40588880 1250 40587630 40587643
    0x11209050309190609050d020607030f050c12030f090a0201020604080d0902090406090308060a03030e10031b0305070f03020a0905120a020a15020c0d030e13060b040b0c010b0109180e 80
    0xb260002121200c40001c1440b0744402c4041d640552120034405450b0341c184000003101c55002500404100000c0020a0040d40707040030703141c26890040e02d0f1120304140c480c1001c00e10156101d808002000307010703085040b2a441940704014030020f0100791540e0700002d50b90b080252018042440004103408004c99a40000000c00d07009440c0700c0550409240c40030040107c06810340009040a022821604d8814a80e60803a50555a2401240594800c01c62880c030741d440c1d4802416500c003844010300c9910104890840c083d0303107001942e45407807080548010b40207100c0c40205803040024000b101c3d084401e0000f40c402c03e40300324158480460540e85000440000a50700905840c80099800300350103290290101542c269401d98442c801400025003602000502054540310b02c1803080c1415080645406031b440400715010340c0d1500c5101141e0302c01e0304002644040010341c82003e0109014a408021080c40c01c81c05603441c100c1d4904450315450349014840d500c176080001c1c0400b081000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 40590130 1250 40588880 40588897
    0x605040603030c020a0f0503120d0902041a0a06111b030106030614040303140402130b1f090503010e0c03061f0806010605040305010c0e01050316022506080906060112090503 76
    0x1048916201d00b000b500280703071150304034070400c4200300c04642084d1450000c001c03110060014003143c145450000f0312034000d640481d440542e1030544d6000b580d5140074447e0b51180c04001520341046440a03c0261141038021000b0f0204040703490000d41c000107900480d0f01c0a914001c1c2d000c1134410000303400f4268a070b00151005007010722440e04d81000006890195129490400c01c038017280044070400c04085401941c800b40c490038041030300d059504002d44403000113000007070343c1d241c0b0721420a00389221007400c0001104100c041c46103003070900c6130241040040c4002c1c5645032032500040c0e52070000900d4440724202d8180c18100c01d0880301c654202900300f51064861560315000c000381980c01c544415200d544c200103078100075500500d5040d0071230700182d44141c515501c0d88220742d021f44030020340c001103100b0540c050480d400700c12603c1d1410070843c0040210185452402483e618020b1320381030064000070103001036a80c00440a05062184200100300119141415070a601070101d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 40591380 1250 40590130 40590139
    0x3070309081209030c16030f0201050307030212090303090f0105040506070c020121051e070806011b140606120706320318010c140f070606031203020301030c05092502010605 76
    0x42c80f8801001001a041d03100740361085441e40800b00d46001d034485054440500038134030103d1001c0155204400a40e40304003281005842c0c0364001a2200107070b14104c900503840c0c0c00210a0051000c800d11001002c4040c06d4002e1013242056141d568907130f8005000f003418031101d248d00d201164050005801e1a17900740560109a40084c1100f4000c0e040c210360782c10310317402c1c10010040d4a441d840c000302c0c040c40c5c55591b0204160390b100010b503001098602074a4202c04038400b800000b541040c80d02c45d90070955030190409051200074810b616a01c2a074001c0142c01c000001c0c40341c25401052030b0700c0800003901c081070488403140e4580c04450b0611a07031001401c008100607810040c0d60001c048000b00e00020001900881c0c8121426180021411103496081081d15464051b0390040e00b03c20b80504000265140e40b40d441d140f00a602c40c811202094012004009020800c0180401403809540745141450400c4007101404069050b00c02490403251790301807694404d500c4100034010281 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 40592630 1250 40591380 40591417
    0xb0a0602010c09060804200f0a1d0c19080a0605040504031806020303060d020402250b010f05030106150809071502070906050607030f0c050c0405040c050405090d02030307030908 78
    0x1000240038254a40340b0501007500100c001940714426524076101e26000340c0d444000c60f481200410307804001085d1a50711406092078803021340e80c0d0000c414021318801014140c18910b6000c0464940001045800031034414060a441000305d021800225209403410344013581d2450b130102c00070f00c01c60300140d13009480c00c81000105a00711005030704401e0740360403d00e60543d41340300480c5d03688011030710641c11086041d004070060909402900d50142c04c020804070500f61590004803070840c0c020309407880408200104001e80e85610000050072042e0000e04c0030300c0c240702035018a03054030b10030102009101e5000403030b4103000f404031401401c400c1c0c44040d40c02d10800d030001e54a40071809240243d034a402d0001800349010310440d0740b010b0349034075500c40700b00c080d00d82690001d00492056903c1e00490a02221984d540d1041500c13851058074540c502c58240300501084510003408426140e120b02400c2401c0da40020603242c1c0080d41d440c0201d108905172400c000c850203961f04035200c445d50350 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 40593880 1250 40592630 40592639
    0x3040c0308030f040615060207050d05070305030c03070c0b04050102030913021b0303070e1e010c0503040b0301090f06050d0213110c03070f0b0c03010b030103060209060417010e060106030b150304060b0a 89
    0x58101d5000d140030301d0050021100d174500da081b01d507006200e207030701690080c10200305504050700c880260b14050002d40c5c1c0050f035651101403d540c4509a072500d04d41000a0100800284101210140031a425030509203418100044d56174498801c000d88145c504000300b4429240780c0d01240c0310313805a2402d101c1500c59003806c8503070700e800070307200000411105412030703001c1d081c00c82c0d1104126920b19070040c41c400352500155000182c1803010340d2107000c204000310340000c88000950082c0315110700010611500035409080720595001306110f038070780d090044007581e42c858820254640e5071100098003d09400d820000f40b0408030f80083d076000202d24201884a001192a1aa4001c0340003042940d40c41d11401d601d88402d00410307101d18020310051010800e85e50107040b03640b2002d46010b20702a00c4003003a042e5500000c46145440c1e44881c0c0700d540c1c04106015040c01410a81130501c08041804005804000c0c101d4004c00c8c020383c0840058144401508060340450b4007030710742e040e45901c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 40595130 1250 40593880 40593901
    0x509060a1e0501030e0a0f02040504020d0f03050403120318020112020c070303081602060112110301180f17180108040501020409060f0e0108060f130c030204020408010f0b03010608060c03040c030803 87
    0x502c5070a01003132605218583c4888049107141070340303912240c003000180316542041b00600000e8030903a0040313290a03d0800241c7d0680b009519240640ca9039916245507151542038031100740420300405040c00b45560482c2855000e400f407403507090030300043d440904803054000f4010340e0703902481e80c41040000400c1c0740e000105d05014514612103058920179001d0103070303603580c404c0c4110f500c412442288140410103060304002900d500800201c4c410f0003036a9100c8039078811030019122045462080303010000540c81035005010720200e11230030455500c0407000a59882d0b0000360512040f00006801c01c1070030f5048130081c1030011070400002d0b4840340b000040103032a0003540c015050304400031074080c90000c0e07068070920320540d6008159640034481c00f65006040070440b02c1403200d0700d010005a40d10700281000c1c04465000003050107a8001c25003d40d50b03103d118900a074500742051003c600042000d581c807842c60103225980780c0312482c008641c250700703a2001d02202c80101c1405010a003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 40596380 1250 40595130 40595189
    0x1202030a0608070506090a17070302031506040506010201110301170f0105150a0f0b0d021b06070e030c0603060901062a0809092404050a02070c09050129040509060a 72
    0x449900300c0350410384841c14040307181b05c3d1906072640f180389800100023400c84805030104440030141510190b40d52603010900c0d02c030b07844a10004100900042000d68205445115840442407000780400703001070081c60043d12040c058000c000341135034040c1c0d500107820003071060310a05d01c2c4020030482c5018018140035a150b100f000e841815074010008454000301c03408010782d005001c2c0f480ca4a80c1c24510540258031040070160403d00601e504840c050b07041c05154410083c0e901c1d19088045000704145c10039952100641c0305400505c00d20545445920000d410742c2d0b40d50601029000442c4e41c0911591260514100349400101c0501c0c10030102324060400703032405840c0c220440e26406e200785c40d80f004a01d410429110800700020041c0b8180d0041d03a045203100350011b103000c40c140c8450350706c1000f40d00800d40080c1c40c0c00041115a003090790400721000f1200724544100464540142d9520a86c4200c03403040e10000c0201c1c8995841080e2030004002c414001d40c2920b0641400c000b1880 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 40597630 1250 40596380 40596389
    0x15030f0210020d0504050613080d080603070b120c0d0902030d0c050c10120507050409020f090a0b030c1803071d09010f181709030a14010e011503030509011202030a06 73
    0x1100c07032240200d280e00008103030300000303140e4950600306402c04003480f0103030700118001102c2c07001e40d000001d10740b4014840d40000b800723180e841d800d5a24148090500d8403a0b02e038481e104461041110045264207142c0c40d0f40c00107802d0034010f0742c0301c66810a0744090a58480e010b503050282c868a2510706410007006800c5600c5001030340d4000005400f000002440c5180307880109a007050310120000007039110540c02006400c0280c1080e440f02074460498012034500c0c82620760002d0285c40c946801400e010003000c500e01501d1075483d103a150560031780120904a98207000052088003103540034040040038001c4c0c0384004650a00c0060f28912100b1305442c6184c80394030300b4030303454560030345400780c05d0105079141c4440d00b141e091551200044540c0c00740030016502e041c0b0201d10142d40034030141d080f55005246540e01403034182c903d00c0c01c6501c1c2c1013807121968502401503160300c103519200e508a941605105440c0e04104005035440707580200940b140920001c01c11002110a074014805da6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 40598880 1250 40597630 40597639
    0xd08040e0901050703060b0f030702070807080a050c0f0109170a0213090b070e0102061f0308070c0617010509040b18010603030305011401050408100902013f0b0904080d15030f02 78
    0x151038a0905400b00d820707c1c0a90380b03100004000f0f0305556100c07840296013140c02c0380704503580301d039540903181c2c02c00c0a1030700402966000310380c2c0700d014807078100304580e10180c00300c8007800c0c031501e070b50000b80410980744904a05502010840f000c207180c01d001c2d0480990f000b5011040d07015050070307541c0003844880ba08542e418071207400b188190f440303000c1240c0e6444040c0c0007004c0d1030311031601d420752300c8108005048120080e04800b000141d180800760100034424520004042e0608038007502c03510702c010030083c60180300001040b040c0e4460700c1887d04141c2218810f02107844401e034401e200040c42c0c0c0c40d08081d601b031170000810540d040d03201340d0403a40d40d803ca403503c5100c000e0045031079100314400c003032242d80540c001c1d490307580c0c80d68000c40c42030740705040051400182c0c141c07044050540d0302c070f455105107015420384990044454042540c0801800800000800c44001491114050400f900154001c14400b04004403a8840c0010f0118009551048d65032854800400551518103e000c1d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 40600130 1250 40598880 40598891
    0x5041d0f0901090f02040513020613060e060a1218140a030201050106030b06040302270408090901060e181816090b030304030c060e0103021c0b01091a09040504020d08040e0901 77
    0x286010f02c6941e440355400480c2a00304034550b0200300160101900403010001403100c1c240050b542d100c000c250b22548000034150461030600090304080c9001c0009019100070060112600e03400b00310300302d02d0082440001030032010f038000034a100b07010300030041c900c49290341c2040b00d8403000200341e841a03200364001c0c844c581e00d4070070403400d441c0304540301a0000c1091100b03000600c2c0110200c214011001c10341600141c03107000403180d407402a20140c6a18000046500c014108a41c030a4054849420020580001c8102141c41114107107c0c0080034542800440c102e50b00f0001095270341c0c21094200d40344e0385980454100026183d105140405240000144040c1008000d6070200c0b034200c403191018902d040c1040c0c402c0a10b08801b14105070b400c0142d8107a154640040d01d10100440000141e8003121600140004429400c45024607a100058401860705d0748111106003809503004261900e5a10209030f544ca11468000c1008502040c0400c0d5040717100c01e118803d06154009102d0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 40601380 1250 40600130 40600141
    0xb0706060f090f0e1b090a09021008090111160803100305070b180d020a06050d020f0a090e060409050d030f02090303070b04020a0909030e040207050312090610080c03190305041d0f 79
    0x25100eaa041910300f000030ba10101218506d03052580644c011001540810708042690010300c0300e00d202d902110104140c4002c0c40480403091084a10b91016284c08900d8a84120541d40144004000060010380e000001030480010724030302c1c0006590100c2200d050a4407a08610340d9030f0041d1400c0c0b121064508071200e01890011740e08044690041c10400c40b0323508040080341d041e0702540755441840d400b04081e004003801c500080c401500e0380d54500d0526810320781c26000f96980130f0105403151f82002d100e0030100348081421540c007640c03410700140c00904050100003a02488130801c0e818080891548180038030302841e288614803c0701d07030705031a035107075002e450072540d8103200035000610542c0c10000908042c1d005040c1d9500031011a410031011101490010104564040302034000c00e007400040a100c00e0f514001d40030321800380a00713102900200340e884072040414042035001040c00400d050003002120041c043d07001c03c0c44d1f5065282060303542c0880c4255881d0020800c1c079000200d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 40602630 1250 40601380 40601383
    0x18010504020d0809060418060e06011107050415030c0f0602010b060a020d030b06040510030b03011104120b0a0e030a0206070e010801050d060b030f0106031104050106030603020105040b0706060f090f0e 88
    0x348a954000d11424005034103898099240d041100c4194112100308000b0a0180080900e244143c65076040801c0960410700040c1e140f14014041606010040001070104030004c910f5906403007003990001402d41c00c583c12801380c0c19003540007401c1c94080b09400b04c3c040c0b0310702400f44103070340294009011085a4405000aa100e07010251006800a0300806400e0780300ba00110320b6408000c10316070030140c80b28001203810140c10441d03030200359500100b43c6542000e0191803102c0400441e65410580344c40004103403941441303030003000d000500b00020f201c200c0550042481c0b02c05441141c1e1982110b80029560f042c2c10348031180440d20601c025007480d07110301003190513076070013a200040b0340d00315950b00b0024010005800d40d00d8098081c0854400b0800d01c20329004502410000111000c00d40510040300c00c181c005008150034401c3c1840542d800100325004c83d00c040c4102c40d5101c80c50304040f4010710a60300010b4041c403441a000034101c0c6142c0100c00c2074941c000040060750000306106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 40603880 1250 40602630 40602641
    0x60106080417071202010c17090c01080901020c0706090e090706141303080d0c030501140603010b030a09120905040c090501120c021f02072d020f010c0203070e1801 72
    0x2000103504540000c0000d41d07600e0031203007000900c0700200d007060601d555010107500b60825480050703654110410300e5030790102c01150001c409450b62003060429411081e16041d00358011810303c0b0400d0013181e4100030950403a85400c1e000d80a640e030f4151200d000800c1c0c940a40305490010341c101340421200d10000c14003004440c2962904800038049491040068010100071044c00c18038010001c0410312240040101e118160300c00a2513014143c0090219541a040000b0103074425000f038110b034680c1c500300c0381980c9502c400981c0707950700e020500020305000b00000781445104445100e8494012120754240c4004031014801500303903c40498000da101c0c440c2c2800035a0300f520310000d6940710b078014404c8040e0391043d1048030041c014840c0300c007685140c00009455000400e03806000380c0030307038044000010800003001040a420707526600020064083d10811003400c1401007680070300c81b0789800690180079108150b07902c001464002c80f0031282a1180740e0713100305c403022401d41841007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 40605130 1250 40603880 40603889
    0x705060a0510061b05010518010e01060e010308130909080702010e1206040209060a0305010e030301030501060602030f0a1b06090b04020f0d0215030a140108031c2901031b1e020601 79
    0x39415203498030104803407800b100d1a030b981c5005070400b07a1303001203178007070017020710400c0c0403c19546000300100b01982180c3e40c001b600701440e4500034007407011300e411110041c11a5004604940c98443c1640c8001400e41c0a60080481c0ca00d0a01608100900030026020860003601d42c2400c110702c2600b848500181e10400c04450b03040000010018500622a1504250040d040c40d2143d610b036900c107400c4443c030282e041e50340e50001c4010403c0050134000c0802804091000d541018580090013140d0b01031800c0001c03e0040008540302050311a20228085d41c1e04040140084000c078103003141040415035059014080360120804141403c4c1040c0c80c290341e015001d0354028417515509802131b040585010012501c601c1d030f0b00724420391661414040c10441d405036030317688a0591000c810b600782c0d981281c0200d04008040500080c0344030500d40011075209404001c5404100480090049404000200b03015011034a21290300019002c900ea0550360000440c0702861003c4e44d50300007d228 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 40606380 1250 40605130 40605151
    0x5060103180b0a110903070305160b1903090302010902100e01090f0b0a05090d060e150709050a09020d090c060c020a09020405090610031b030507020c0103050712150905010b0705060a05 81
    0x11030030301612540700713203409032844a119052004110010342849041e40c41660340d43c1c0011280c1c10105240ca40120041007000c0010340b404900c4450092852031545200046c0369035180c104080c98000c2d084001d9840d401490140d40c90201e2101800b01411a02d000c2e000400500001c41c5104c4210440d0341a034190040036401c250b40c002c8100e680ba400100e2058100352100084030000d8854003c1054410310304025010002110301d00c010002d40052128041001c040401c11041d154409004203640c0661000350b5240e000080c48806040802030040440c0940980007030051340c4400950741941c82161220440c541e1804100160300030ba0040591080c54807000c42c1d0310307190211095654164605010a507024240f00422035003103d500c1c140c010a8807141001a882c0d411b020206502000b401d040003103040c01c402c014550207010700100c0e40d10f41c5d41c075403460b04c2c0c00c081c601005c0204051301061005603119212031246801191045480303220f108c0205d043c080460050030311400301c5c00d5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 40607630 1250 40606380 40606403
    0x20d08060409030c300305010608010302150712050405040c02030c0309091f080c010314091f0b0d0609020a0602061506071104020a080105090903040503030d020306061b010506010318 80
    0x808100041110b507104506000d20100f5001c0000c540c0281c011801c509070040444018543d000120f03d60880c2603944101440d200042c0500c40c2c00c01c0d400d030705494065840c2d00c0c2040c20f42d4480c040a02c54460094040c1440d000980540365100300100f0a85030140c50034422920607081c1a40d41c4d005201000d00c0c29002801020700e03030b042030720303480350320900d910740340e0301c403015180d042c0a0000010742116000f600008802412560980604090644000102c2c0d0052506400b4162a04c0e20044100d0103202100710078072103003c0d250000200d21800030300800c500c000710700c0c1c028001c2181d140100d01843c094603002a02e18008240d8610640031401c0200300c2011113030401405130311104040b240214141002e10554850384083c0110012a807120b0311154105400c00402c602c006003844000e500070003040c0465100801070b5549940d070100003603241c8d295880050880d0050020000717000c0021180b18011080c1500140c1c0215001e890030454419100c0d5202c0c000003004502070a00790128 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 40608880 1250 40607630 40607641
    0x40b100f0819030302040e0f060405011401080f060604050a060503092104060c03170f061905151305030a030c1506031106030406090c150921030804082b0b01020d08 72
    0x5089030b040600c02e1a00514203901e401c5204c0d481901582d5021200c1100c4040080b5810144a03050140c05405940c604044c0c40b100002c0502000070a00a051070342200440c206485d0182910301801e001400c203d000390701d46c100144160800c5810089900ca1010044e41c420710a18a0690700000103e101d071401d400c003c41a12000b0035500e080741001004c011210340b056500e031250340503113076100c07002000b130401c40300b00015404001c40d20810320769a200c0c100616074921540031644401440c0046c3c90b85d1010110b40d841902a5010035010b0140e04041e03802c0560140c9420403982c4a440210003230181c140d120703411160180001131000700c865441ea5028903040c400b56074440d00c00c04000c50030301c0140d07072aa0403091050380010210514540c00301040368100c07001001904040a0031075602503000011540c510500300c028060180714000f0a0511082e0012662409803650700c0a4450702c400c1e5400071214402c4170101d54940c50031040600541c80440e0407070030845a03a98032810b03916075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 40610130 1250 40608880 40608913
    0xc0703090302270703020301140102061005120a020631030b0705030c0c010c0203180306040803060f12010903020c04180209010b130302040f0b040b24090105070b040b100f08 76
    0x1118408124090990f1a80c1d81980c02c10750f02d40e10032007050394013689a514001a0108038040e01700703040c2c1590070003001c011001d583e402d5507600f00c40c422100440d10300d000b40b0390325003840c429140c080d4010000140444601740180c0707088800501414650b90070324000d44503611084686d0000500503140c03030010540b45481003002c1e41c0c102c00300702c0c1524680815045500c3c21030724072400100c05604040394410100780074116036007802c030090b40030b010b00f441c0c0b83d134810185100c0100041c2c03181c1030b944210b01880d21810503000a107582d80000300040f6541e814044d40d00e001090f0359920442c1442c19a014540b0313115070250f880341c5c0c0540030050b50b0b400e1154109050b0014101205003250051002002da0780b01d007d8480d9081d103410000407042e100c0c2080c0410341c0d20031050039005003c00050b004031000310814a0301443c0c1c184910700d40b600c41080042b60039220300b28001d80745841800034481480b103c081070a00a10394074210303030b02d00e55884240384030380c02141c41014241d0300180600f40ba004c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 40611380 1250 40610130 40610149
    0x90907180c03020408060f060a06030b0616030c080f0d051005010206180c0d060e06090a170a0201060b0d020c0d030c0203040e10030f0b0f07020c09040201030207030e090a020c060c0703090302 84
    0x75400c0143c142511380010514100c01201c0c00c801209410043c4100f5003400302840d0701408492505100d80c00314000401e940b84a00d400c0784114494000c240018580725115840046602c114410760710768800074041082c2d08030421601c1101d15190109070b443d00550b641e503007110b8040c0c01030001c9981c1c0030041342d410300d0020143c2c1e141d405030301082c2d041642c40c03209030a205841442d0000b01e40c0200c0c0c3c8031900d4200c0c01019410306030f100003002004500741120404581900c840c6440e40c1d104195402c82c00342c019a80145004400880c031865610b40da5000740c00380b110100101d803d181c40e2604100c055444c44083c2d42c0158000b04410f000e2003240b42c00e030300d80c480c004400260000f6541d40c4d80c01c0c4690b0312480241c540c4140c11051000c04805221b400d034012070a440181400c81c00342c00024603010001e44004d05041e80010000105400f680c0345118505006022815500d08000b001000c0c0d4004001c80b000c9015600000e03090440d03800c143e5040a4040e6103e668540c110780c24031a8042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 40612630 1250 40611380 40611401
    0x506030a1515020601080a0809120708060c04180b0916030b15090907090501090e07020c0a08030309070b0f12060d05010e010b010f0c0b070f0e03010501080303010509090718 76
    0x303455000c1e8001c508a038480010041034980241c0ca081410154024142201070700442d40310b13000a8400008941084191465054119014411401007400c110b15001090380b00b804140120000c000c412400072001c0c008451916004940c640301200c122070851394000710465026840c00c4c00300701c80c1540c1c880345c0050585542400502000801c00044083c4242c8688501401c40040d01d40e01078101040b8031500300e00b95040c00c0a1117400c210011b04410304a005030750104956100242d02d003482084400200c00001d040b4012b00b54560201580380e5108a440e84054890b4500005140e001d60084655650f4400c03076040c100800003403031030399904006e8103d96010310410034441c0411000c0c0b07e4555411185000000c0c0d0080742c900240003001d00341c440109006816160ba404030318000c010301d50058062034242049481c07d10103945c9180b01501c81a0550301c0c0800102d4000e5000008505035082110078030321594484c0d803d01e554a00c0350007005c42c8a00070501a4a068020360072500504 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 40613880 1250 40612630 40612651
    0x1505060a03140c0303030a060f0506030106020c0603041a0f040309060908070909260301060314160c02030f0a060509010f1104090506011707050306011101020a09060c020307090e030307020d0315050603 88
    0x2040400117071442c0c1080d565a008a96141010403903c0b00b086001c1d00108400e41c0c90506641c50442c019440c1e210900009000d804000700007070801203d070003070400480c211050058075081014103104410021203040307001c14022200428003500a00c001411210a40d000f0711109003400c0b26075002c0c1149060440da1185040d43e036000380f403901700d00c640c4d4400c41c50200980302d600d4258010b040d50000a100142a00080d081c041c55850040c40c1071450005403d180004a4442c1301192500f03c0036000514240241100401004140d070400c6010300c034154000e00c410740d019280e0004490040d0864105000108803c00003058280c1000f54402014141803a18034102d410301100510100c80c000300250000040000c03a60700b01d00d0170008038161400850405130311a00141c0050b4442c0900b406024901c1c50f41c00c1107540400c000c3c0c024107403199084c0842240380035074940d01c6e0001c0e2884c001501030702c0c1c6200100351181c4a20b1419400c411462080203150106104030b961000d890300100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 40615130 1250 40613880 40613893
    0x1030b060d0e030408060c130e010b071101210b18010f150201060b04060302070b0f09030d0f09120903030f050309030f180a231c140a1e1505060a0314 66
    0x40700818016588505d00b4002c00c80c0e600d194002309682d8071201601720101c1c40584d640180900314040040e2840c05600c040d10009405051005a41c801902d0728820070b4003c018417200c008282c543c1003043c04010503034061103074003210040c00c0c1d4404000d004450a13080c0c4d2102c00c2203032032111074001400c400072b8000016081d407155542c2c0050f07841600007001281e00069000100802079404580c41419030074a214141850002e680e02c9100d0003240d003071346c10b4540c0026201007800e075005020103544440b00141d21410000050040d241600c400e5011035140c18000280c24011401c4911911043c0c000e986032a8600903200c007182c102d020b000d00b2807440c0e9540c000140e01c0303c07a8603074042d001c4104a6200d14100307010240c200b14200380341c2c6002d60b11030036029128030103044019403555400010b2580341c59507058003d1410700c8088010700060044054040d9030707500006007100460081030710f100401c1000040005545099804e0350300030040400401c04151100c0545204001410540e02c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 40616380 1250 40615130 40615139
    0x1030203100f0902040e01061d06030901021201080c0906090411011d03030c15010b1c1a030a060b011704020d15110a020102030a0f05010e010306020d02070206040e09010b01030b060d0e0304 83
    0x851440c03034200c052a50b90028083c0044103483c0c201074010231315481c0c030480160519000d900c45001b1041c1c080d0090f180400840c03c9000290190384205240f207030003202a43c0d40c0e140071661100a02c4400e4055044400424803505001d00854402d5800c420700e024640b03e0007004440102100030340704018021081043d13110795040c130003020b68405240081c0b060030300f644556506c0001c180d2060320000010040c1e6101e030050902e02c41d142003415540007482080d5802401010b82403000010b6050042c0c0d0b1030341c0100700c00350307129003060b076001c2c0d0380d214400440401d800d048040546001e035010048582c07440010302400c00801c0780040005012032001841c020712205504805c12207005030f5008002c000c103401c3e0a116201c800302c6011000d115a5140281002c802503040c0005400c254002a142c9054030341c0303030116204c2c560b0242c031940e641c90352140e49081a031800e070b401104039424003444940c01d621900a030042070000038100f514140e01c25601b14024000d91102c0d81190005000025 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 40617630 1250 40616380 40616399
    0x12020a0b1501020615030703061505040c090e010e040c0905070e0603130203060f010608070503071403070e040b0d0b0c0a0306080d0c0c06050a020705040902120a03050409150e060103020310 83
    0xe010700018801003481296210002e070a0041c018040d0a2105030324148820300e0790300080c00700c21a80c0106001403024604440824603034216080607400c43e041c001c140400070303885180d000803522282510052641c86e07150201964a09031001b91640118680500407461154804c40e0001000d051074400c2c080c10700085031040c0c2080300c40715400d02c5158256415400e00f400304650202a0300da4143c065810a5000351032641c001c0c00d4081008404000604003074080d504090701150b5141400d5160f01e000b940c01008064211500e034056070030b04941c680c00e410591600c0d81c0c41d650003501020103a4803403840c407649802025426003056203c0341c1c0090075120500020034260510390360b54a80c442641000000310000d81e000030704114082000c2e03000d59501213241e0003500c0c0115001b103512946400014801c1b8100500340c0503a0041c10726490030107030480300034001c0301d030390610912a180038246090102e041e140b00f940102481761b800603c0c5584681c2c019076001c1421480c5520b40c546070301c8003c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 40618880 1250 40617630 40617653
    0xf1302120f0a0b030303101a0f03010305100c030207050a060c090e01090603020405070207081209130e06010306150501091202030a05030a03020a03060e190e010b030d0302090a09140412020a 83
    0x700403881254140201d40819028079054400c095000703624605203e045103281240c60700c5094a200003c1d000000c1c00e5501d0800c403800c50302c4140c1811740300c0d40c681c10925180e18240b007a2420b030341e00c0d0104102c681800b80c020f46041c16080005031210700341c0c035203650300640104480d15080090201001c00d80f4081d03c01c1e114060318025000107941400e610502c4103e510141c80c0e1000e661000354200074403000000e62400c07150407010040d032240c50003030201e02e06a101c44040505030341880001e2003a007800040c00380c12a4000d0606101c0e51007a18000c1c0c10381c1c03105005060000e030030b6100c1400760070346480c0802a104d1011b02240c00d0149a9100c0e5800e680040c000640000e40028800d5400c039458062240603050581c0210010304110a0111500125903504520580c4410074111380d030302c0039030140d600d216001e0240c440020516400030001d40c4070410342807103580c2d540b80100384112244507080070f140c00001c5140146d102da4035028001c00c070712900760045200d000102c3d0001032244010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 40620130 1250 40618880 40618891
    0x19050912061603111e0702060d0b030709020a2a0501020408070303090503010605060304060b010c0c060207030605150102212209050a050420030c09070503070f0801050f130212 77
    0x2a24090918000c0c041e80d54915540c142c00700350070400c0610007441100102d540e003002c0d4107a10010301c2d50541c2c401055004042c0c0181d400342011a900410368002d42085aa1203011030940d84003903241d901e24401c03800745c2c1071080e00042c0d0528004140326100c41040316a0b81c05c190150380481e010365142d41c26a84250424a02904400810401c0541020303000001c2c00b0210000c0c040b06007054080380301c50100038005014640c461050b01d842d079006144961149401010291030a41c86810180d95020740d403004803401031034480007d40d440102143c1c0c100d10b500580c0509100c1c5000c410444c10001e09070103007400e943c410005944035072003141c4c440c80d42c000c61000031910780740782003c00301c1181c2c0c0040090925a040004100000f558085900401c00b008503680320780100c80000b0030300e400e02c1c102c1c00131340114070712062040c800d821034042c600c1a00340da0b84075541d007900e070f807822504c0440c00e01c10550031911401e10301c42c542c82c000401642a0401c1c3d0b4005040004400c086800c0c0c2c10182e45 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 40621380 1250 40620130 40620133
    0x807080406080106020319030b060733090f080705120319060b07020a03021302090a0905060913050d0c0809060d06060206100501080604050601090305030705060f060a030819050912 79
    0x10300300a6240c1200070305006003691300296007085002e0301c80c41c0503d01c072981184101a6944c502d076001ea03a40300151005113400251180401a40d43c5000c2e085e003852220140da4503119884001c40c011140c020881d845034010740f00c850301c0034140e6414617903070040d0b102116540505107540705080001d5018500c00c040c050009400644801d442000b00d503a5900b005407050001c200ea1005a11102600b0342140d07410355000001c00308030140300000f400f4444503a503002a52500000f84c542c3e01d81c1142e8085c00045480e02000c1d210314242c6800004442c1c00180181c00450700012424000d1011340300b402d008004407481d1281140c0010950382c0100d6410600b10394a2006003c0e0550421206034802555161103500034180030010340040001008103100c1e035124000260705903c14000140259408801c80307449024510f0000e88644046135102c00c051018400220640743c8045040202d0750001c200a10b010a2044d04540000b90505e0400511208000d0781702d1544904506070443d050420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 40622630 1250 40621380 40621387
    0x12150f16050309150a06090630150f021e070318120204020f070611180301061809060603170a030b040203010506090108040317041202010b2b0f080708 66
    0x5500400035460080880e040000c184100112030b100054030514504480703040d01c449503201c02d406005003406070807542c1382a061441c0001c0c151600e0340e8400080226400fa1203900000c01920141a0280d031130140207024100c01d02c40300b000790740d8420b00003100960000740c9852250741e01c12901401d06545818040800101c2c04281544411000101d08860301131048580c40e00c2c2c10103844100040000e8461580007580c1070411402c00200c03204107078400024000520024441d080c950401440040700600d00060350041c0e00c0c040c8688030503103400309100d4080c03503440c2c10040001d11035007000b2902540d56003004030110380600c1160130241002d604280d50780e0031841005050b00c4003e07a100b401180180014452a0703210401e8880c034100a203000140755070f6900342183c4550030481688104a03820b0140014017041540603000a006900284840302c0400c0c28481c9405200e07000107001044211900090b0455416180000e0b001d12000c0a1600d42034490800c0b950000004030340c03900000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 40623880 1250 40622630 40622641
    0x504030804032003010507021e03040905010602010b01020f1203070c020d02130507180b030103060e1905030415020a0c1505041706040204050105010906020d052b060f09061412150f 79
    0x6003c200c0d601c4194028020b5040414002e555204696011645001c910071038141e469070401c161002400036403c00d1155503598040a4002c080f00c048a5005000d40d10140d45110000210ba81b400025192101d203565112901240d01c0c8910440c105c2c1d01040b0f40e446000903030385e54000300035607040f80b110000c1e85040c42c81010f401705603481e10850601080c0e96041050b14184400e50381103e401040c00705004802c402c91609011400c00d000035004040007140003800340000141042d0313075915030600110351041c074043c0d90f103c6041d0001840c070459282e0900c81d807040344421403042400d50500508187e11280c100b01c402104c04211045d50344500104400d628080c06840d006100a08024070010b090072802034480840314500341c05c0c4080045c2842030300604900c0d400700d0320302000e80103e0141c1e22544600240c2098400c4d01e031180a5510080f94810a0303202d035000700d510003013000f1201c090700e0080c00f000c2820640c040c9040c4c01900402111500446407580c8140e6085e000d940c07035440c20 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 40625130 1250 40623880 40623923
    0xf050a030305070e041e0908250c0902091c02030111040e0f071b1b0f0612060608060a171204030c0303032a0804020f041d0c0402120103030f050403080403 68
    0x4e02294a20441c01c1c80c07020100300c1d042940e18101d5102c12400810028102d0919070b11b00e1103002403514501d2140641e82c100c40c4000e1111008661140010701403441d61901c088003039004141810b81c1c13042030050b040703003e0f404500881d000f00344050000300700c0381e1144c613a01c0311341e4000e03501480c1002e41d0350041203000a844080700381e00c12003c0c1030134519114506c0d1005860400d024008004100000c41d040a8400c1064241d0051694000341e060340ca45418000b01032024464a8264044c142640410b8650003158440d100303035005012071000e81e1510000d5403602c035110700e10322080d0064003030f4885140500e81c0144059070184802102c550728515004044450080f1040400c550303210040c0d84c3c030000308814012811035494491102c0c1c44500005041909011003581d00c9480c103000e2003d062242060020214042010369400b0441d02050000368881d941c080d0300200114001071002070701549480d40d80f00311034075083c2c6c105034580c0c0d00d4403c10341c0550000d80355102054841c46000c140c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 40626380 1250 40625130 40625147
    0x30f060702011d070303020601030201080406060801020d020a0806010908030d0c05040f09020405030f01050f06120f0f0f0d050c03030a15030606030803010e0606130302060a031509060611070807060305040f050a03030507 96
    0x20f80801840380c0341c41c548009460740c0d01804020b04110541e00401c06120701500f182d03002e020729100843d5984d8820300034900942c0541444400304441c2c1c800248950f004443c0801100d8044c00654505501c21482000500c06070380c400302030002c18003012550480000c4c0c00e1002d410180710050f1742c1c034280020903150000c240001e240302c2e1b04100402041d00404440e16810010a0b29080d075451501d0b005039040c010b100d9880d803014450301c2c03000881c4800008a010f00040340c1c10076144417401c00481140d1a10a181c1420364035401040820104011540b240d0135001c808000a40007a46950341c400c241c0783c443c1c1c010b84490501000600c04914034283d0707250040800ca440510300440c801c0102401c08252001034418840803518422050090300907031441d040620300d0b1500f00782c40b0540d502c002d100f18002c0000260b61240307880601c00700011110107442c0000001d011852034843c040b00648002441255140c042484050000c0c400b004072900146c46528049064500724800505040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 40627630 1250 40626380 40626431
    0x80901090806010f150c02131a15030408210403020a060b060403050d08040606051201050108010c0e0105030f070210021206091f0302010507110d2103020403030f0e030f06070201 78
    0x1003103100100310313400031000610700f01c43c034203e50b918103044800e0081c0d6102e004c0d68006904106081c00c8185000c0c119404080c103d005827141d004100ca41c4400d100000000d4100701e0500001000424049114280a8003001e00810794240d05100c4640c4200350b00d400a0b242100541e118a1160f02041564000c90303154041c1903c0301410b0510719120745a80b02c801c0c42074a0b040c0210400400c00b40701d4580c202c9000780c013000c0c0410341a0030100d07031203e000342424490707460103502e03100090545030f201d04050f58840c04c0583d601e40c03c58640c40580390b8a48c402401c580194460007a4031501c1026030b0001d001d05020b0304040c1400e601d807020078403000000040194100650703e400c68200e1403050700c0710805994080c604039864402c0344c07501e2402c440f0810129a0300c045428600d004000704219803103944160700f81d88801040746044194241d01450000a0109205444600b03034144591400720036504000d08848941c881d04100500b07184003900c151005035150200301401424205104020b0b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 40628880 1250 40627630 40627633
    0x30e0a08010c12050f060f010c150e030703032012070903060c09050907020d090b0a03020f0c0607020d0c08040e06010c0204050115022b050306010215100f0b03190209040e06040809010908 82
    0x3898000000b030511004001f42a040c8001c0442070702c2070001f440c80b68041003500d140100300700e0f680704c000b02e640d030b4100e108210000fa0a0000a0082a881c6c1d400401411007a184a60800348020560b0340c0380c4000070121400c005580c0000804145240074140030a40d0640b2112861404c3c141400540c40c07005080606651094592001c116840b01c101c00031241e0750302800c1d44420612000301e000e0321442184501013000420102c8030558041500c60182c8891707000c41d403841140000c1968090400300c0d014001160910040020201101c4204d60000c0140340000b00300045600080c00c841007a0030412100d15206145148140c04008601c210001403801c01451245018000c0d000c0da1a01542d07020014003002203005a4003c00c6500303c2c201d0200e0f00f9171f0346403502c40710055034003405200e04080001048000207090300794101310b0b4065100c800b00d840203040264650000382d403004900c15005960f400c03100740c01180502815002d64821100c10f5580c040440004060f101030350402560f6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 40630130 1250 40628880 40628911
    0xc05010c02090403030b0f0a0e25020d05070f0807140c0f031b06040b0703051c0c051e16050601050301050705040501270902030a050613020f0403030e0a08010c1205 72
    0x56501d0b400300700c1e4020f6051802080a110300340224448040400106803c80302202000c2859120a10b4203407040c0303000b58000040000c41d00403100607140c680b40060140e0806426110090f00c160700410070315005000443c0840001e0303865100a5001c18400c2d00c1c00740e43c41c16150036010060042003241c40c070854180107034041c0c100001e40c5038803460a0f089140b40d00b51000b001140c503541c1c03c0d500181002c540e0f85032114100d080c003030180c2c0c2c0801c6000388412450b401c0144070108a00c1420316580e003d0751007a00b02080032680d10101a207500350201000018450300501e40c08d0b408880300300324800d401400d190751412050500303440e00070340352001f400703424002072000d41d80c4046640442d003401d0305a03d0901005502c52948040140c10480400380000204a5031004035000716000f440240c0d182c03100c074080c441c4160304074050b184c8a2005058100000c00100348038500c5910440c60081010022565a104817401c42d48a02024404506910040464a1100e10a4541c040c0d0040443d094 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 40631380 1250 40630130 40630133
    0x519080106121d06040b010e090307170c0a050d0306030510050108121606060312020d08091e010b0901030b0f01081b1201090605092d070b070203100204030605040c05010c 75
    0x140c024401244203080c3c2e590340c1c074550403038859010300801c0e03010001540d1240c00c0604007141c005c0024000d05c1d0082d50700e48049850b0b50300000486020ba90060032140d0b0545484850708280d500903c0c0c030402c50f118019010300818428080c00c032802510ba10002212480e45ca04541400310744500700c3e80080c684001000023481c0131407500d280030034002106544038003600050043c480d101e44040c20700391810001000b00541201c500f6000c01c2c1507001c50713a039080381c441c003100d100c030044440149640021500f006201c29104c0509000c0705e0f03500010815109607070104109040903841544c05661141c18030000d0700326248940d015100030b0026000c00c088103080180450388041e0b1441c01207503095842890700d8400e601040009a004c0070500090801310f0203903541e030045545070340e002c9621100b0181e100c1c00515603450f40d00680d0000e00b01080c80c001c609100c5d9001035005a800d4000c0c0c101070540c40d84103200a1024501c40c103030004060800e420282012502d0390042418003540010000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 40632630 1250 40631380 40631387
    0x20c0d030b0105040b0301090507031d0c0906120f100b1207140117240105040e0411030a0c080105010f0911030a0e010b0d081b07050d03030c1404060519080106 70
    0x5a840050801152107400c0c0c01c01210030b40319507403100e58141000700000c12a450780390041805000555800e0220220000da0310b007102c1042c40903c1e07030383c0c1e018504562031703801d00084040c3c0c00b050090154885d010020030a504182054412200540041c55102444500d40c07058461880e01a0344904040044800395503403100c0c1c90140c500c0e07540d4504806c4400b0380c407505002800062034040201c00341010038666550b0211040e240207004000b05081301035500c2501aa0210f44245040c102543c079603850f1034007002020800c864241c00703600303010404a8075201c4602e00904200e03000054070741c98540d60400350b01da81e1300105070309801c01c0420b058a40306042540d4008811400c0010702e001c01c00c29503401882c6070095a9009030358100100e0901c001c01c400ba080050034044103891884010070482e49032080d074052983c0c0f2140d92440200440d10075402424100c8290801010801080144e1403032a046644000000b901c0042c030360403100356203040303440480f0b12070400c410a5414194042d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 40633880 1250 40632630 40632643
    0x1020709020d180318140a090b06190906020d05070308060603060409060c030b0a050301020c0604150e0105011511070503030406050f040323060c160201050a0201140a0f06050301020c 80
    0x240301580205194020030000e900265651041e4841a00d80d02c489180107055013001510161598a80700d100146e02e6000b80d44095210300c0c0242100c081d1820000000000c207102c1f0060781c0c20000911a101c090017055400d50380d208050b4503130310a190301c1e0110003071900048502e02810403000307001100009400c1042690011021505143ca0341d4500000c2802000680c40141540d4180590b400c411a05544112802038042d96000c50301500c40c02070500342c1c411580d00c0070a41c0e10460009002c18504007a1418014104801042c0480307407401e11420340e8802e07000040013a00c142903c5059541000252030000c1600004d42034940c50140042d03184d0042d881601c2c2071000014003220b2100b541000c03100510b600001c490003101014400801452603480c100a8511481c404a9400880002900c41d0700c03031001d00181e440010741d40111980d0300b001e0300c14000d40d902c0e0a20b041c58034024450ba64490001e03200300140d000700d510080003d650303c0c1e030300c524042c1e40b04001c00074031601d02280b032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 40635130 1250 40633880 40633889
    0x209100f050c1225020f01030b2d041404110f1311070c05030307111512070e010305060a05030303010e0903190909050709060e0f0310092102060105010207 68
    0x498011902003410754540c402c0c80d03200c14090241c25442c985508103100507140e00382d4034107a0410865092000102c0c602650f800c007a5200411207a0000b2943c481d401150b001c0b10702034030078032078034100031600d4194014441e45a00c40d207a01d00c0d400e9940381001e104014010940040300c0e400790801340c4514148180d9104814001e50325203031203070741603201c0b590303061884105900e080080030805c3d00b640320b007500020740446210715a103000042c90301c2c0000540d41000d8002c00b842c0300b00c044a00401c144104101c104400b20981484208210b418520100b48911100e840d0741c034071442490001001c90b031005000c24401d4204005c1030201d0f032000000d8905503805040c14510a03112803449030300c0d6001c0c2c019443d428250b0342c0e0441040d0740c0d02620410448401400a0005485414003503400d0201801544000b40d017401041010b0314000300c0120000343e010341030340e0078080c102d103444080e60102c0a0566a0038551803490441c1038004103070000400b014406001203505020000b51118402d00c034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 40636380 1250 40635130 40635137
    0x6031303020c06070506040b010f0f15031d100608010501060509040b0a03060504050a1208060d0f0f0503040b04030209010503030412031d0604090603030807020f0309010f020114040b040c060201020910 88
    0x4044101802042416840b200c003c0c5a01d03268403080c0b805591399042180c4c02c6540b0004403000240280b01c0017152400c0e0b07080401551506414446005042407090000504054446001c890081c24400c00e61144020001c050200c5076940c1c3c4404045c0c1e04541d1140d00c03144c1c5458010040c00d0750213025220121411200810b6500d01640007940302089030304080e0485250009000820a00148000c0403511560150031800b4000006582100c422038600c2d401c904211826000240b0118a50999a101d500c076a107507000a07480d01461034229030842c260081c3d00040078415840c0404080740142400c9000b1440c0a082c2040c10408580d540c1c001010702c1041c100c181d120341002c08604101400241c249600c40c0c4d503422150019000700c2c0b00503000b0800f4600401e0041d480070410f0300030004400019854400c9080c01181d50540a189541c110355a5a10b155005080040e003240030720702540350010f40c0d08003070a11440310042d51340000706680c4104022206500c0b8181412000c950509 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 40637630 1250 40636380 40636411
    0x109050f010507051203180f0a0b07020a0c0806011802090d0201050309030403060903080a06140a15090905010305030c01050f220c0b070b011a1c021305060f0c011503020603 76
    0xc0060b1240c1c050300400810074002c2c0344041e200c006520000d5807058003640d91101a05114942c920748440796140036102d55000b00010340c01140c44840d102d500550b2501c1100c840b0300c12502c50488080254210045907000400108004540c81040000c51a41c101e41149400c00403000604c858040074070090510102000280101400380f013902c00940e0041400e0007107514515000b001d0301c1e01260401c0000d03140c43d0011070701000913035034614481e00c0500035003142402d04c591038000180180119040014003071001c502220302d801058000d5102d04000c51b01c6119128000e800c2d20001070203d036103400b14804010a540034841d820804a40c1300c5444407410300142040300140c1d8041d004405104800528a07042103c1990300a0407214240b4010329408007089031520580301d400106242403190311a62540200d240d0300414441c1e1160032038032840381d510408550140c1120380b4100d003041011408030710341c0310203010340820412603012144035241507600084460101500040940700300c207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 40638880 1250 40637630 40637659
    0x60d0305040b0d020706140405031b160e040501051810020c1914010e060106050a181a031609060909020901090f0801091703092a040207030305060108070905010905 72
    0x89007150054072040c0200c0740c0c3e6a80704401c0c3d0000c1c1d4800c000131100340349080c20741c070081074035102981e01455100019611f4001c100402070640306440400f0030f924002c0901c410f9166100b03285031402070010000315000e91a060618500b12203000780b40000c04150000840e84070040445c14500311000c040c0c2c01078441c0025429149400f84014441d07101015004e400024800d0954011090b215500002e0189900f41000303d0f48601081c410324001c2841032140540440c0140003000e0383c2740000d41c801140d140c1c1c0e03440c110300000010f03402d4104038400000f8017000440c03441c000c1030fa02c81e640c1000074840d45810710003440e10071684958840709502150030303403503680b02d03003041c10090010703003000c00c1865280c01f0030600030100d80c00120340b0983c04214010b500307184202503d2040d03103418050040e0440d07401040c0c5041144441145204004644032142d540e44c92025040090180d6400101482c1c52000941540c001a00c43e00a2020002042005a910240a40c10b450040e2610342055005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 40640130 1250 40638880 40638887
    0x150503040804081e01150b0d020d02090406030803101e0323011b0e18010e04020105160b1005090906160306080f0a06060506040b0a0507080f0d0506010807031103060d03 74
    0x200e0700600d00f5809862469a02264807404908036250032000800000e229141c50b082c10810031310031180402001d015200100b152039026200740510b07044054949020040010b007242e1544e0002c075920600032091240000040108a02400b9488022070250300c80341c00b101c070882c030140305c01040030590008242c032150350f20b60285603419211000340210100c03900030020082000d11014006a0141102142c92400e14142008c07040c007a541c415080c1d08000310382e0344204006200764184401081800c1e0074414854408020b103010f41c0400440d410505400c0d0186899580b145104024030360034801460310100d14140c222407a0f01648803100710340c40d030a601900c0c840d80005142d001d0303400442300c0713400d000c280b4007042449440204502902c49041040900590042c1d68070328106102a00704a4000c1d0001c014140c0501403090500e44c4141d040022a03202e0003d0000c0d260311001448a1540c02118142c0c000200f400c080c00f002d00500960105400010181c41c820f500180c007041c00d0502 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 40641380 1250 40640130 40640137
    0x70809040b04090b180706120e0106150e0f0d05030a0305041b0305070f050607080409020c030d020301030812010602030c0307020904020d060203010605190201020a0912031403240402041505030408 86
    0xc041d1003448002601d080c100c0143c44c04035242c0d00400b0343c10800500c81540410741405482c85511401c00c80641c090302140245521b0118008030341d620359001c54404001c03074103010307031034520ba079a00c0f420442d4a050040f681381201000740100f4100c2041c2c80045c1c008020344014014910700040c2035503640c00c0c1400c915114800c0c02d400c91a404034003005004021a400007620040b8005428a6660300700703200c2144540d901c09801c118050106001d0242290020300d01240745400b00c1c0d040140d001e8031002240d00a80c0115402c0c90f00040400040c2c503903d154600411690021b07600303010410645546078411440001c1c4114880c0000508660319801e61010341038204808640f82c1d078492801800c0c6521000d100ba6003c190340d00340b00c80085c4140212204901f55030b5070100410700c4c054552400c61103160342141400548032400c440101d00e100514803c041840c529020808119007003920045400805800b8500400041c008010403598042d07030b40e5420310f000d9660303a5460411468500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 40642630 1250 40641380 40641401
    0x606080f1807150e040b10090506030c0d0203070c050c010905061801090801020309030a18050d0605060111010903050409060902120105010e030a29010518010510020a0c03080301030611070807080904 87
    0xd010f5004181d165484a503c0102c1075041c0d40400026120704d007002083d0b801c0f11400000103c89110030700443c14518040c68003c40205030035070034450403540074026030300b04451560004412407007160038400100b02c0743c1041902800d00044007400c1030007085c41c1d0300c12041011005860300e81850f00d40e9105482030301c0180766040c021034980c1409c84005481c2e900501100002450700028841450a00c00141c030459100801d0b510303821909640c1d65015020040129060282d840506a0203603803e02840c00703414401c0e03a842d075071541000030190440b005504441d146910500c00c0031035403500400c03903034192203090170440580b50b110380c006442c0c25400d070320003001c03803d00103001c01e9100d4110000e40d44940f004082c100650781c0315811700c030b0014a454605103052000c0c000400c82070901010405940d5003a01c10343d6421061a201d0a1040903158000c4070042d500100400038064644184070841050080c11031518007240c9810007540035848000c1c00040700011101440d60780c980c0140c0345003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 40643880 1250 40642630 40642649
    0x103171e04050f01020601060e0112090b040c0906060e0f040b0303071401020a030501090506060901031a060c071404110406030c2303040501050708091915020c030a030606080f1807 79
    0xc42400d11180c00c590001e1180a018010b2000b03104181c0d030020800c5410380b00351f541c07502041e1201d2070044502e402012025074450b40d5400d8204003090305030400510442c01f40841c21011841c2091010032900554484810400b603007498564070b03914200c0784d0304603c400700c0d00421274460500020b4154403500c0c5008000743c110106c2c603c1200d5064010b401d216800303072010080740e0f07a00c1c480e003400e40d00211b500561240b000c219035101503009030b020008191180c41d11007400c0d140311010a245910040c01540243c2c01041308100038041400c010031240c1095038107102c1584001510801070041d40070749400e140d16550101391151140c0a02801d8200a03940f100d035181a041c01000580c0c020b403003c1c2e4040d42003c00040f4070038003400802d400303044d03400010142e10300840c400e4207000744549411101015400711140500300d990020b00711424030440a03540c1c1e1085420044c040760810382c00801032156200c00c22000b0801005450b9000c11008400d981c65010f4141b990308020040c6c2060b42c45 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 40645130 1250 40643880 40643917
    0x80610062a0f110114030c0705150703090606050a05031e030c0a080a0813020916030209060408010b10080408030703020901050c0106090f0e0c09060f03071203080703050f0f010317 79
    0x10b02140c44803008041d8003d0a070000101c0c01200111041440c40429116001c02080410540b0208200030441180100186c4a03499501c128140705990306443c0da4000a403100da2400a01c00b943c426440245000c6a21202c5a0310f003c01090326000c58810f4240d01030016000f41000340024030884203141c01020039100d1100707261414400310341100a1031400110f041c4000783c002c00c0c08100d01034a882c0c00a0030001903559507860b07610540380079031f004400c06800b4820705c00162102030140014100100003c10a260a8424450800105007041c1d081200200922020480f04411070360085950324000d642d43c1003110050310203114001903407010b9840d00100141c4084158046002050319940511003d0b503c10b40c130b155100c0095680700d602114100103d5014502a0f5440c19040c0d405000e803001d10340c0e030300c0d052100182c0c000c00550101d200101000046031b0700d0300c01e40b6840303044460350031158101b0040c16805040140001400c0c3c10308150030511544004042c5d645810140080242 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 40646380 1250 40645130 40645133
    0x1021509010c08060306061f200607030e030708070209070c0b07080709090c021002070201030e030f090306180604020f150c03040513020403200604090207060c0801080610062a 77
    0x90040c502c001002443c1140411900c0c0340c00b044040c001c240013400040034542140030b179052070200e19141e50600a00003d4964078103c0f42c140d0342201c44091024021a280c404409000c0e201030306031500c3c241d00100000ba001601d5403094440302038060712281003039070303a01c40700391441c5441b04800340c024100c81041004140d8016861881001c40c0d42c2c40c4480503644490502c1990700c0b000760000981c01403500750b1002c00e40c2e075000d014101e005140214008619555450450348204480e41c100c60f00020081c215003020070140d41c2055505007a0482202d2a0366a26111030002c0c00007803182c10200500a41640c6442c80c072040d00c203000104964602c1c0c0d41103c03a40c0d940c894410740740543c04081e20003408104501c241c1c0c048a400054418084841c4883d0840c135540e20000a90b10400910010903a40f21038806810000c0c891640010403617203000c8080c010f200140c2c005242a0f0010082083c83c41b514010303681104e00b42e08000610140a0f4101905014000c1c1100860042c00545d02d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 40647486 1106 40646380 40646383
    0x20d0f170a0b0d0308010317120109020d09080c07080f0304080c060a0306240305060a0308090613150206010e01060302040806070c0303020910030b040e011a04020901021509 76
    0x58a4001c041c0003522403c01c101e030542c00105840d0050080000c0c0102495801c0c640c07804960611417046100110340c1c2050080c4d0360403d802140d000c44018894200e00d031800da01c9902c2076190b0080700b10135a520095482050043d00c280b20301c40d424241d0200031034094458560240003003d00030824010a42c0c40340c1043e50402d0f46d0b034800041e260005500c0c9406c0000034840e65040000c03009402025583d0150100b482030780381090401c0040d01840840d10030000944034640c0381c0c500241500015116503015101c9402c0c00406120a143d012400a05a444412504003180d0300d40c18120124042c0d80141c154a034400800704031458001d00c08000c440e0300c40d01c1c0240c40c1101a80201ea403644c4139607484000305e61242c03141c00c0030b4581030040038204040304008103c50b85664000c030306043c64403a0268060354bc0050181e5140c0d100b0b0080c496903441c00040000c46080111419 = true := by decide +kernel

theorem cover : BRFrame.Cov 40467630 40647486 := by
  have h0 := BRFrame.cov_init 40467630
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40467630 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 40467630 ≤ n) (h2 : n < 40647486) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
