-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2381
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:32:24.061441+00:00
-- url     : https://prove2.me/submissions/05f9cfd5-f29b-4f9f-b598-4cfe037bdb69

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 428057553 ≤ n < 428237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 428058803 1250 428057553 428057611
    0x5061e1206070305100e04050706033801030e03120c0a11010e0d091e0b070c081608060106170f04031b29060a120c09020d0e010c050a020a0b 62
    0x800c0011035151300030008900d10840d4a4401040b01001c0c00c200c9090584a594443c87d403402a0800c160f21940e4088034640ca44040704000702580703461050302510443d14007040c2d244611141e00282c01d190082480040c000f06980e5068071000c044081600c0300012150b80764480c05921040c03080003484014011400e00c140c1d4110660302d400fa00140c0303850b4000620303905098110707a103a41c04403008035102d2109003043c00140d851035442c40707076107220a042650300090554421219481017038129200c800b22141640200e9a61400321006c40c0d032108820307142018002d01c824074024401c80020400134100503841d0300103009080150301c0b01c585040c030712010407078100245c4000d0400d80f141c0c000095030441104602071050050140c500b0b0041c00640c000c403e5218401441111031860014011f400c03040100034680404210f54030b8081c2c081c00340191451007600c00785541392074242145640141c2c1255202619076016102c400d1655a422122001c007810845803440a40c0a2501c04072507100703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 428060053 1250 428058803 428058811
    0x30d12090b07020303090115120312020d020309030a09050d030c0f111005070506060406240215040609060b0307140402070602040e0a020c0f1c080606070c090c1205061e1206 76
    0xb015550f40c0c68041b9039103007512244da955142602683c80308000b0aa04c1544c0d20500503030518024414403039010080300603000d810007815956100006001241304008000c0101c2005915030354043e903618001c00c554400e00d1100500851030203103824001481680905071400d110f4042c621200404601080d000602c61800c0b1003c1040001c940c1d05001d010040c1550056045a00b4044c9600340555080341e070700707800e514107140000d149145c0c1103140240300d48001d417412070b400c508491509080c44005041e1804081e60b4061900400c60b006080c0804d06200351035440e8520302441c2c40250502000358001e0200b03850150742404003041885069a0a40c0909000700016854840c40380e055410401004850552130b44401c0160041030040e01541c004158141041850355507110041001441141070080c40d40032124030210780001c00d5400029619901e6a17565082c880b01000c800c101c410a840e955130050650450900710310b4000f007410720040024000364818000620740034542070080d2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 428061303 1250 428060053 428060057
    0x6060e07031d15090304091406090702010c1d010c02090a0603050c09040b0f061c151b0203090d06090215090f0423100b0403030206060f040605030d12090b07 69
    0x424040800d601d4052441038011024003111070a94401085583c1d584200c445220b0800c214000350740e0003014019500240303182e44041c04001c090380f074002c01200d011a022440788081e5008194600c0c030510500d01454490f483d0014000d0781002ca00425081900d00c00b410405003000c00401a105c01d500e6900511078500d0100f089400c510b802c2d4107111596000c180640500403c10012034081502a50054400e0a44920b2031b212140441e05450380103c1900341443c1444013071007001a5200d2054003e80c00c0c403420040f0b66583d05451041080306d0341002d0041e4014014551280f911840490a048c4648000980e601d103c0d03000c200c0e00d036103c0300d40c003058410114050f10b143c200f200010003120002c446c20045440c41c2c414011602461660024001c52488006032140c07a95060240140c4400c010007603c0d10307a41d00d0004d60760b4100b1100d0b1409600c0101540c0c01c603003058054082501c0c4010054805560705002c01c46411480101064107a41c40f00c82e2039001c05c0580d40341c17902079206d80d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 428062553 1250 428061303 428061329
    0x304080a0c0b090109090209030703020d0308060a05010f1403150907110d05130e04050a02040e160503060c040b0a180906053d0c0203100605030f0303010f061b0606 72
    0x241019940344065a000621440d0b08101e2052160380c04003d40702501c10383d406c016240c042440c046403520710b658100079003010104100e00245500031100e0f80c810030040381c40101080c0ca401c011039521380060524408601d85c00108031003404a000919400107150300040c07054103000002070052007091322240e0100d55064521584003005010000e203009003401c0c5103280202800b00c10302221b41070301c0740018804540c0040750405c4018841c0c9110035400401c1404400d09155420307407600ea00f0300c170224a0b0b003592000010a800c1c04500076101e4580d4248050030031745001c00c4121035602ca44030700000c1220521107005e01207034800d21800034142410000602c07a0070401846007030300350b8424039a000d03d082061800a2a200104e00e1000c115a00000841500c014001d44414001c00e0009600d409110788444480e140c903401642103c000702c088465152598000a842c0c1c4401c2c02443c80c2c1340f411030010b018881c0548440c0424502452400710032110f82e4413803004a07000341d00405040f00d04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 428063803 1250 428062553 428062573
    0x52802090115260105060a0309120e1305040f0227100303030b0303070f02010f0e06040806040b070c08070308040c0e04050d030606030b03060112030e03060903041a04080d0806060408030408 83
    0x212501110001142c1d9009050501c00d100b0b43c04105041442000d22a51001583c551124843e810021246600620807214a010301c0c002501803011a010240590401055284507450301d00502d40a01d400c107100b01c052a0460b0207004120508100c1c015a1806090080f0004030004800c01c0c410885134400b0290282586802020342d01000c903024803030b078002d00c10b10001ca01e10005660855509080c400200080c1141c140c901007029182164000000b05000030042d0020407160703c02d40c85000c2d1248140c0d900e060550310000e9850029104000501107240064061203150350418002d1103464600d558400310000071000480703080300d05401ca0040c641e0036941500820300076020b1420140081034180000c07a60b6400e051003012440c60040090340c1c241030043e240304d01001006400d0300c5182c50a102c84607070f00e0340a0301c62900110152100646222101d6050b00c6c00d40700554043d104030401c0e44011188040c010b0000d0307510200410000549403400c000400060417401c0291002c281 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 428065053 1250 428063803 428063807
    0x30609060b040506011209240b090105220e0307060207030513241d030102040e220809010f030b06030a0b03070e0121140d081909052802090115 63
    0x6a800068012801c06040c01050ba8201803446c0c0881000040010200c64500b44600e0f0075440c0b081d0251811042c092881e40350b00203030060480a0380584045815998031018403442c0c1350701c5c400d544c04401c3d11065503081e2220517002504d00c03040100031203051030620b4680008036880000100d010a100242c946843e806213000f1000508000404e044442004002c1c0e03010880701c80e2003001081074840d60380030031954050b030340118190086d00071502c6a490782c0180b1101e000903590414402d940c20710241c010302d40071500b424110f521aa600382096105001507401d0611801d0807024952947c80780b00036a200c071800f443c4030f250590000f040c0c100954092500304511500500c030000200d10050000315144880c2e803100b5410800108040400342c10080d40c451250b564030205800f41c1180d41160550180c1c200c2d000f1495102c091400c0007884c101c40080300e07010400105160094902c180c240042600c040f1103a40d02510311441c90f1b5140d030300141c98900240c110001140035201b18102281e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 428066303 1250 428065053 428065061
    0x102040b0f0c10060e19060f0303080906010b0a0210020c102909060a15090f0b0a0f050c07140d060e0109051212010509060d1a07031b05041406040f03060906 69
    0x28554000c0013400c5c1480207030b04100304014582d0703030881c02640081c20084515030000005050b140088800315449140052200c54240e445840311310071900080f07000e110340c8040700c40c0003445800415117409a41840c2c0041c2d008040480843d02514110a002e00040e005032140203042800540e0708420554a120650f180c0b000390602401200c010482c07036484030741c0c503102071320750340d00d405403c845014004031180d0001c0c0e0442604d100217883d000508240d47c1000c0c3c2101d4881f5203a440e184024410104d440c0d004131213140805601c08942080708454003119a01048400b50942c070320440c0c9916038800340e640b03600da880f0a80e0b650303a58580074444103000e00e880d42a018600203150400c410700c00d421107507040c0100fa10510150022030000d80d13580c5000341c005544040c900d0f0200c411404000c14a82c0c042b119040481c1c00d000b220388842c0543d48860142c030401ea240c1ca8207081c2000c40c0340301c00500c02003116070051010480030444142c01c2e88410011803040c100071800700c140d8600f1000351 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 428067553 1250 428066303 428066323
    0x3501060903020109090b0411130303030b06030f0a0c0912080d06170607050a050d0f05070f020706050f1803150717070c0b04030c1205090102070819080c0102040b0f0c 73
    0xc0a6042400141e03400510a411a24001d8000c01c6007840300300000c005000e0405d1082c90a50b0004410300d88021484000c01181d009860401c50041980103200c52441700f1510110700717a541e00006151102c01e039100140010052410600c450b8656800317000d141c08422040d104540301042400804178140103800c054090304680c0d01040e1021650702d41c0d101d00c06004c50b424000c021480c1e4192601c038030141c900c044c20004050005000c1e038a0304900030503007560703004001080801e034410014000240b901c21225155140743c90480c441003031007041c2d0881890000d120301c02c0c1745600140e903810031400a81022210001030301d814081c9000c0e014080314111194000c000500300503170140c0209144050030b4200019480950301d61901707e415801600008020065a001c1980d04550040103085000c0081e02150795440d2101c8105a65014060001e2030700a080c0c5490070000d40b041002e03080c80041c0100141c01c1546805000c0d00b6900b0440303400c0704040c4e003c80c1c01e01c0c514208210450813 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 428068803 1250 428067553 428067557
    0xc0506040906261905030d06030f02010201140405030405010c0512030903031f08030406052809050f030a0b070509030709050a020306100309030e0f240c01060e0106090312350106 78
    0x400600f0012442c0c84110072040000c038407218503c6007040c0b02060040745c140e514000c004110a03a00c900d4040008001c48100360300640c030303228000020074042c000c0c4a00490300000190306061800004440900d101030741110240950f50300d2420b152642c10245000f481000b000d95264038120b80d100200d544008801103407443c0c840810006110080f00712025554103182a41d510807001e20400040c0000c41001400c214118960303540c11036200c505103080d80e1003102c09202141040082540ea514819000b03030014034220007088007180184011725140303402030150390b0b595980d00c40c3c81c807c8840894030030350200c0d00041040304a1410b4490b010404030f0600f410130240c20181c40003404120b045e140b950051070400c85c06112595000b139240b05801c0e01400b0324082240c0c04e82803c52640000e55551115801e10308085889814080d843d8180c80ba56a10400701600c1d40c0c50307035482c20341c4c155141c400740041c0100ba45400a4148020446030201400072450241e0a41c0300c2d00c42300c5416070282d02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 428070053 1250 428068803 428068859
    0x40306050f04060522120903150c08100f141c03020604020306060603071b080c0102040603060e1305100903030b0901080a030f05041401110f15040b0903070b0a02070c0506040906 78
    0x3c1c80e404202084010a401854086c46000d40c0c510545540302d603504060100400ca2040c0311160300c540e000202030000c29610914103446d84003140550b91510b0148002c00800c864050103811004095040032240003020f803a504101e000070440b01c1640b00134150016000401000258101080040d4110301d0684c0c02504e1440d19100041c00307071314080c070501e0113040000c0f00c58060041210a955005048030700842d61182d8404001e40100f1140c412042c6903107240c0c0001d000400207650075100c40b40c002000d0440030787c49200240007040c2d460070441c00d065540301a4151a2291034a081c00f030040d207030041183d4241d6003000382001f4013440c0410100101080188142c5541001c006a40c41b428282550b180910541050511152442001d51442a40d05a1540b01c005456072400f840c0100c1c40a4003e441e1450000c0d00d030300c10700b080030380300c0c0b0b908001280140606138001c003d828055403914075500c1c0c03a400082e42c15401a8030034040b041d107450061144400c000804445085107030701502c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 428071303 1250 428070053 428070091
    0x9060705090a21080408010f06152f030f1c0b01020741011e050a050f0c0f100b09060f1504090e011b02030703090302090606040306050f040605 63
    0x54040340c158007030940b446a032007001c800f01c151a4501c45040c26801141181c0340d40d01c0741c446034000c0c10250711011050381061800590020644030345120f903071041c1c3d03800d10040d0005c50030000c6040051484210020300841e001c450540c01d0000d08000e0324111402a9120706818075030700304d02100003004c1d1020b440c269400c1c0040c4e07000180e2500f2904031340c00074980020301e0f0f50b80004031a081c840f1001c0304040296034030843c1e041c0442400140300244c0760701c0d543c5880d46001e490742d1500c030b0091350f020400c02c0003440e40301c0c0d01400141210601c5081c403145070454081502e420807100001001c529800304080c4000d01405002d800031a040580d8000c080d45006000202c01c40c00c000780d02c500801d07900d400059940d203c20101e801902404209002e2100380c496040d0081c03c01c8000200111b0b0001c98000c1c5e041c0c804001c0b20308a03601a6520000303a8255000c03c42f00c4003029001c140e220808000000008807503000f010712603030000441100c640f6140c06c085054890041009404804085410b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 428072553 1250 428071303 428071309
    0x1e02010905040213090e0102070203012a08150d0c12050d110f0c060906040e090a030323040212030d060e010e100e0f0402031203091c030c050409020c120408060906070509 75
    0xc070b545c1c201e00402c136000d002540c28024821003002079099401c001121101031101c00340d0400c0000f512002500028004008451090054454404445070b248a400e102e140c0741d1495100c0a0281e00600d0441c1c1d5600b2100c210300c0c000100407201900000340300403400344c0055070b60b50000240d1010b415650000950383e0788a901c10b4208510030780005c101c1721f001e51103910982c1c010f824041102c1c01d890411a00151343d03a802c01c54110002401c190103040c00e103100301501c6100040c44000e0180c107444603803c12241103800fa0341d10380f051009200c0c1e050105103c2c0100310046c07441090443c1507504049a0140f40c0600521078640007000c2c0d1000c100001c520309003160b00407040090030020b40c0351440000d09103240c482c101c41140c070010060002081c40441e2809080b542c40d41d124070760102081090741912100c98242000c40c005000421a01da200c2e00100420701e008029034015181d45180700d03003036030442c0d0072040356030b40900c00f0400d440f80704102160300803c840c240709040040e05400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 428073803 1250 428072553 428072587
    0x1c0f030e19032105090609010c030b090606070212010f060302011d03030304140304030b0a0c0e031507030f06230a0902130312030b0d11030c1f08131e020109050402 72
    0x2004080002c40e4458800030f44040c0002001400b007030381c061115081607482c503031b038400c400c0d104980a5460120180d48290092240c0040620090850130041c1d44941c100030050300018000d9030080c0640401d60b82d00702007885849403000420100107a6142940001402802c03c003101d03541da03010301c04000b1080d90f800410b0b02ea2081c3d2160300d0410030a0b4044401c2d041d40215400200b0403001030060105101742d68005580c00d03e40c954884100f00c000604240d0f075207082c0d0310000724104182c03010a42d400d10036004280e033180b18480125102390349045181451926164810800c500b0000c00030503450b01c46d84a4006040c03143c415410440d81c2e5000c550503500394480100b2000e21094440c0285001381c1000051000007440140c842c0050704000b07030394181c8003405521074094010740c020350f850014615550f00140b10002d940d8074800b110f090b03510030b0000e0126010711980d0002540000c2195144900e1720204045201d041d401500c0050603c6500340c015511850050003500700204401d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 428075053 1250 428073803 428073853
    0x803060609031002040b030109230411040b150702090f010605090d02041410030203011503110409060605150c0105390f040e010f060c0b01171c0f030e 66
    0xd006a503000d5480000340707041e541d030100384502400031400050007045040914100ea000038020320500e000c01000450040c0c00301800b0201039070001c0864045a03545500b1055200040d1000410341c9120000400300400300795040d080072000a480307400c5045c55500e69410079025188000194100f12000d0f1450049280c2940109680c2c22000191354842d0091f8240d03080d540d4091800d0f0803c8000202d4800045c00117030f00030f60820000000d0130403c01080c1c800c481d000000e4401c107040c0c4504001c0030380030010301500c1c1252a40804182c0b41e4461040003803001c602d11038580d4418032035034550b007920b4006014100559608038a03a80c0706421004441304018256100f400400d056183c401b414007407003c0302040302c40c0119001c6401c100030000f440c1a50800282a001280e651307800f00c803160010b050082c0040c800c44010001001c2641c1094111001802542c2031811480c80044944c140d03007500e03400103a07240041d4a141034151098081009441014021540d11a4002010544095 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 428076303 1250 428075053 428075059
    0x216110901120f03031104060f0212040b07030c080708040e0a050f0106050901080712050108010f05060319300504050405060d0309061101090501020403110306100302090118090507031419080306 85
    0x44043c0c0402d803103640181203455080c0a034584403500e420b00104007051120b4605c001d0b00c115088440a8840042640c0889101c2c01c071a0b880c0c03803030310341d011100c001c59807604991048041c802000095a00350143c406031400c407a0040d2645001c90890040c2e03403011f011100e07002060700052101c02ea100d81101d014001c2800c1c103200984174400b044034499000240e184495141c000041384410042d0418140308070241020300031a00c84600705922550001031071000c1981d21404a4000b0744584d00d61b820140e910104c0c00310b0340b061070746511581d00d2a1644000007e80001e070510031450b0912807a500f2403410f48800d45809420380c0c0142c0040414007a50062010044403913070161800d4000700d141c0c80d4088029920380340e40c0d142014003182e2407030f0a00c0c820b00036174000640140c1c1030060300040325001800000c2591130f0200d250b01089044002c0030071941c41e410200d01051082003400000c61184260108000c1070800003801d0032034040b903183c80b00c1e0701100c0c4040420301d18030503241c10003411 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 428077553 1250 428076303 428076323
    0xa090c020703120e040c02060108100b0f0f0307030503120103140a1101030509010905070902070b07080705120c121005030f0a0305030f09071e180209060d0b13021611090112 76
    0x3d1070a85200440d002c2c1e040e80107007002d0301c0d1404145c1c0410640d048a04482c1241e1140c1c105034030a0b410780707034100212900200d003481d1803440c619200070a0100380e00082d040e540c1140c0c903511142d00756401218540001001c2c200108104106c1c440303805c028080307090140c01c4921640d903c1d0103103011a00c420358101915030000c2840b2140a506c1452001d52100c1103d82c201d503605010390182d04078100a651350440c1400040e005030161808074420700e0f2036502c0510f440c0c83c2264041d030f6624050081c4c800c8000502c440b0042e00f850f052424080c14000c9010240c8526100c101072400c0c0d124680f00703003103403c8a41c0380c03000070380c00009aa800c2240700d4003540d21070fa00e00004502d85034042e1b0003501448454441e0220f805085039800c41541d040d179803851444070318040391b02c05a01c1030905940d0040800c1261b64081d54440d0300030404030300001e103c2500704601850303e0060343c20882c581c42c2c146403021075800400413032034002d44179540c080d07400342d0070b940c034050003c00707000c1d0140400340c516030748 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 428078803 1250 428077553 428077583
    0x150c032802070b04060f060b0d0e010609060b0c1209010504030803150303070b100609030b151201020a03020d0f050405030f0a170708060f180c09130203010905060a090c020703 77
    0x481045004004010002191607a80b80e00703102d01034690a540544403a40b0304410944860380b06d0140c0010348401c0076a0354588071421200000518020326010010b55a942000c928070b4042d00415000300b0342400480e80b1140c501c04d00d00d09202d5410b0a91008503410008410281d8103d01501d00300d03030b00714940303a0316581e49004a021810f0707030130451076150200041c008100902c07840c151b401404440c081c0740c5401e444072070a85009150380409000008020300290350f6038100070398040c00090140007808940c894508050071380c0c110f200d5602c080783d00400e03829084603075846045005070581d14144030a003801d0b16402d441e486405002411100000b5051440c1402500ba00354851120108580180381c49500140100f8090322000e1058000380d000c2d040900c1d200c4141410f54030b0008000816868401041c42c06510800b001904004650a5034100b8115440914000d00c503900c1d02240902d440c004200e0110603d400c41048a0f18107503038141801c1d4002110310980f98000d03e100c0040c3c070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 428080053 1250 428078803 428078851
    0x70b100501034703070b04240e04050a09120f1202042306040f030501090b010801150905101e082505090a060509041202010b030d2304081b03150c03 65
    0x3d64002550075104400d00000c0c0515028010411134a4032500d000c0c0c1c0d540c00841d02c50000c0c0260300e8440000b82603400350320580c074241d400b4981000952800140500d05541c07192240d038000507100c3e01140c02c5031200c4c0d80141e000000b03040b0794445035100318605401c01c0400e8032a0076454482070013034400c400e13200013546c440104a901400715801070107081e95603454418061712400030101c1d15814000700004040c0c4050007160551401010301c0c003413480c1091030380001032000828981034990b081d00b000a030b00e0a9415079494000c070001ea403400e103a08021342d0610300b0310f80c4114240400406515240b465000d228002d040d280102c0706000b8035261418030741c0c081c00494202507070116103070080c801004007071603e1001d406440d8000f07021020041c010151240e41442c034000128160340904220308003034926000c00301c402e038440c5d10304080d110394510349005180340c0075440c00c2d10264a403005900d010001c00c1004020342010305140d18000390b00342007034000074203c2c942c810560402c82001e20 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 428081303 1250 428080053 428080181
    0x8030f130204090b1008011e2f09100c0b0610020715030219020c0a031203020d140717011503050405120301060215010503030a0f030b03120c010b0406090c050a080c070b10050103 78
    0x200300c270304050102004a90f04514142d1149000d94403803000f500d10142d045002e4500308040396041003d400f900e554450a010022507900b022201314040e081002c225044404181d444142c000d03070b401a100c0c88401e00585000010b91141c10556200341403100d01950fa01590106490780301800c80720101106800741c002c0d00070000c1162405040c035000e600d0000c0ba06130728501c10084c69541c00b0301c030405c05800c100c20380700030301401404d0b103800400d045856010380c0100d50003c2c855030483c3e41200840040071916002a000400140c01070050044214038107150680501802c901031481c01c0c0c59994007800107001444c03a8024142c0b581e0345800644c0e428003500745106030b0040307032a039a14140340b650b0b4020006105960b02c590314003000400c01c007881e4030400081413042d40750240341000000054410b0000104022200e000401c8100c00150142600d40c0c000c4580c103112500c43c50821002506441c0c1c01c65544144c1e050620b060101c420942001b101c540f04c4401c0c05916400440321000851 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 428082553 1250 428081303 428081351
    0x110c31150e090d080415020c24100b03070905040e0a051203010f060203090a0b1b0a05030304020906040b0d080d02040b030c0912060408030f130204090b1008011e 71
    0x200d440403000800000c00e00c6450b200ba0442801c0c2c0b569054445410b50f040c1105580242980090030204110b6154640c014040c9080744000c480c502005541c1d0f5000c0e14441c41030100080e42000244191b00300d203007a818015001501e0020705624000e8401881d0300b20910600e8400c40d00e03451340050000c424815540d078140c019042d654102103001c10300d450740d84280301d4030300c14211a4100017103591001c02070301d5541100512425000b80380c01d291520030f8001c040031046820410b030078560310200411000d02080c1c0b056020310340340c0c9000e004102041327900402c0103004504149411038180e0b18070356111020b95001c1a0180c847c03075889654402401b49420074401c80c0400000d120013500c8039800b0704880740c400c0307480d1881c0b4030032080c030245c0b2104c0644000f030a1000c14404205e400154084a56000c0520813160410304002e070000750541c3c003110340945400c02c04a0501104c51201400d000150078220001d0000034050160030f140105104a00810942d0790000c2c10416841c2d00c03c04455 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 428083803 1250 428082553 428082581
    0x601140922150f0602030c07170102090a06020106140604030f170903010c0c0b100614070f120f030509030f0403020402070c030c03050f0f06010608010504020702031c110c31 76
    0x1480342c00255600c10141c640188041004407801c0016400c0c0f0000840308038000c00805840c15525111114007280c038540190b01c1255024072096025440340406038000f4001e6500128101e841e10050701c0c4400900d00505001d04c038100018130100308016941500f1951004484491020740b45403400c040c0a45804a5032650030703c050034204c26400104107035664007030b074002d04490b21983c5060100001512516010551314044070f40e894842c3c00252080d10b0040a510080440c1d41e5596450101341000e4030000c9113414010000701a4103125546d40001048020340c0782907510035039900207006c1c138071000740300c0c40d0002044030810100004140041d980614010b4450303442c0d140c000e484020596500240e07204081100c03150200c0010118101c40880e114a24140d08140030f100c0039500a44050341c2500c02e0703400d160104e410842007a4400443c50b610008145c10039080c05040c002c400702200d02c20b04524035010350a141f45400c0b10000c48500402c4241d0109070320040000d040740200c860030b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 428085053 1250 428083803 428083811
    0xd0501091e060b091e04050307060912120618090609020307081e030702010c02090903071a0a0f09020609040213030c032004150b030705040e010f030303050601140922 73
    0x181100c0d600354400701c1846400705014407890f00061020208040300c1d000482e444140d8000d540c00040c020301e0360460700031410360340360902e01c1d12580103461a110313007116a40000880651555407210000c050382d0700010b0140162454031196013444444062021405136499540a00b0003000d42c0c040d9503440d03406400d0700e440350340d070f03c11403510340500117030b901440905544040c00301c4c0c501004440b03c1550584408000001c0307602400b2640d0001407118050f88000c0041502041155658101c40d040440c0ca005035031030201405419158024039405a0f0740c104041640140d458031300341d600b5801d081c0d80040e1585612031080c1d82550541e4130241140c04115404070501505802c82e80c00482000c411009000000003071008607034440542480e00c0b41c2403030b070a102c3d07031603800c00458204085241c068103041d166010440081400c1c0d100b01135620248408008042d01805802c0d8070050900740b002c02d5180142c20041030344907807030b2694071a000c01400b6070303000c40030b00509850340711f18050200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 428086303 1250 428085053 428085083
    0x1407031716060b211005011d0f070507060920030a0804090b0105131409100308030a09030306051008010812090a03030509010909110d060b031e04020a1a0d0608011a0d050109 76
    0x20381c179103d040c1e2100f076140d402d01001099807a2072030603285040380c00d00d003940d100f40c4d80c0321540064007a020b09401c0800504201540108401d40110842c440c0210950300c80a02c56603003040e6126103441c4400d019811010b01d200200e880c0e102600d04884203c0c401081221404004031000e102c2c2d40c0710888603200c40100401c400610720391410b1014000d942c40e00c110384646c010880902c2d1184001040c0500400c00280040c5458104803050b621a040c0420015200e40000f414040004060400522428010080b94104000340401c0c1c4414a40d100d20f05000c000206850026500014081c0640041d081c1030300e91143e803840d0010181040b08000020744042c12440340c0d8440e4240d4206141051800704102e588074049900562200313491030050402440107407004440208243d038403142040002074070035401c0c4444924042c1e030a40250ba1000800414400c40746640c2084025a05d0031550f458240c2c40c542c507001030900e08032181070912403d85002409080c40107002806181440303007203 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 428087553 1250 428086303 428086369
    0x130b101412181e0c310608031b25030305031008030409020a020c1801091109060a0f09080d0903081b010c1206061d0904020303071407031716060b 64
    0x83c4065203221401e480003101c419040069545008028080e2500341505d18500390512880c040c0c8028150400881c40650b5400785606640019403088028100c0c010202c1624005006000380140c100ea0900b400030b40d0011100005600b40c0801002e0080000c085880495450003000040080c0f100300ca0f0740315224241440030303401080402003d885511a203101910340407080c103840c0c5600c01e08155081c3c1c40c2290300c1024001d0b203460004580d83c1000008015113496006100f0f8100d1a1175100d6846110b0800031300700d1400d40c0c0484626009812058030456001c42040110f9030042c2c05640c5802c1c12014401500260008140496180041c60300f180f1f81c0000a40a90548413001000f0032655070304d003500d1910080c01d0085d10151900600c40c42c2e494002e000c0340c0c105001404490800001e695100e6402140c4503d00c0c84031390260608008000c001001c1803045040030b80618200340c0e40b40c080101044200c0c900616554661980e219640c80e07900c20941c0c42515107103a076495960300420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 428088803 1250 428087553 428087593
    0x1a07081204050d0f02010e06061c02060c07140a0806060f01050c0a05060402100306060c140703020307090e0105010f080d0f0e061614010504021008060f130b10141218 73
    0x114050308104130100380107104019201c0074a40c042c20503a0307030781010068000002510190140c10328030280c00940c603140040c184041401009042c03a80c00c2c4841c0e00301d40315501c4900303441840d5040060100d500003045880d000701055600c4180402301c000107a42e81d01826a0540551003040c0a035018488005442da00032402034424460105005074200d00f07452050003001c2c04241c111007810f00051a0440b040070720203c03001a03c24540c1c4130b600103400c0205503441010043d480300304000c0b80a5003032013405c1c01049201405d85800d840d01090b15102d59004c04900203101d0020203203d2200c0c0500001c0c40c3c5410020901c940e02c1e04017580301500c85e0401c040988840060002c6044000c10512541340a243c00812000c0c0c2c160010108917150b1000604817500712a4040d020405510380b940800400351003000c01295401540d010300c80c1c003608103124042000a201211658031402c0f400f15094602d6101342c500c503a03071b50f03181d810601424507a00c10a0764400c000c0350325065110245 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 428090053 1250 428088803 428088823
    0x21012050a180b19050910060f120206090a080102040b18030c0102150a0e0106030609050615060306100e0d1a1602060f06041509020a0e010305011a0708120405 70
    0x4003044151980c184800c00c0b100d160261140440c41c41580c44041001c40b844554000744c040c00342a15143ca0342c482e407055441c141c81e1030641740e00041444105a046000d00c00183c401c8101c0c8a949601d00458070840002c0e942c40a030081c0c0000401d0740003034a50301501006011210000c2d50340b25940c8400701301da60f0104056001e49002205660545c0c6404119180aa08140e0080c091f1901203ea09807090701e001c0c2480d80841e0341c94108407108602802085e00960080303100280710400750070260b0910340010903680140354070250f0341d400b41d075560050703036041042611180c0e82241503150640c0c802c030540c1c03521a070000040c003518080010703421011000041c02c0d2040001500d41803841801212000403003005a0060000150f104484150f074030380c03002c070090021031a42443c4100c15820f02854000303416090b0002401d23030b1070641004070050601428039007000558034003403810303240003107030f0030328251800c2c0000b004c4040c8810b00e000d5464141d011408204035003898606156141c000031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 428091303 1250 428090053 428090087
    0x40912120e060c0c070e100e0708060901230904080d2007031218051b1e09040609080c06040201020c0402070330090605100915030605130210 62
    0x5800614900d1140111a030a41d1881c00804a540f14240707041c1c00ca410801c803100d014410030100154500205c0584e9006485c0c241412090a0810b050401302c540000c0a06081c00306030820b01c010768466612150454501400c1004411001803c120140002d50151036105001d00288020301440d40024201c03005404420001500c0d40301113005078003200610810264007d10440c40401e01580e060089428102c01c0080c49500301c44034840781d080803010580d881cbd40401d1134fc10500210742188010100c0c104c4214881080d442600307407050940790146401040100007041c1000859003100c05a198401070854941500008140d991007084406038018400c503d09071160307090503c200e45402c2d40590707078450024464107092048040901d040c40195940641607100c4040b680b0404030392600c210004180c50406514084e1107001c280c114000c07a5181a00007628032240c00011000c580d0301007804103042c1d035643d0b80c0800c1c0d14003280019420064522030b00c0600d030b074800d4412480d03413102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 428092553 1250 428091303 428091317
    0xe1b0a05030a0c0e0604020904020c03130e01150c061b050d060b07080912070504050907140906030604032d030c0216030b0112050a0614100605031005090601020309040912 75
    0x91081581c0da10b04894040e041d01c00f90001405440040369072103a000d000500007610303200348000031030120b038480350a11382607800110340c850481841c1107000d40281954401c0041550602d800b50303031800180d0220320148072002c9942001c0180c80e400c00041c4926460501840000700880600158054528404010318100c00450504207210986040603088114213003401d5114050002c0e440c24190741c41018032030100006215582c0e40030303103880b40ea13130200580801403405540e444180116016940318803002000c204454500240d1540c0c400d07010b01d84849901d11032241000a481194800000d1403100541030b1199a096001840140d1007542190b411b0035091800d440705201c1800000d2900441400411800500e18414080c80b07000e03a0644240a40304c0d45d44038201c501605031140501e59500802c40c540980c1d0681c000100590b09080386585000590510680c615004180c401e0f0300240128445910810559084050280040100d101c60f0b040040c4100d5445242c0d2000a2f01c07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 428093803 1250 428092553 428092559
    0xe030a08031f061209050f061005030c03060417070c030b041a01120c060e0109090e280302060105011b1208190b060306060d110a050309060c03010e0612010e1b0a 71
    0x5144085811241180c0d030f44c0340c0c8850041340c408043d100f4070b90180c850303200c1e01700c111140380c500b8840070f400382c0c126034000010585040180340c100f210317010f01c1d00d209401860801012038a0150130040241213070140aa41e800a4544250380a030242c001818200c46102000204084400984800441d0030601310750390382d88103109182030100d110001c0602c242184200003c0d8082c061845000c0b2050400001254540040f03404840761920290210b0340080202654401d1341c0d01c40840443c441513603500400550745000c0e594180611446040000d6924100c031b648094800d001e00c0b840e4060803c1108416a9000500e030381c80c1611810181107c00300b040c813410300355101c1c0d2101c40c24041c00d03da00b1541e811041221603080049100315032074139410110711400420006009600700c40c4c032810340f2420452000d45c03902d100144585da2002d82080140b12030440107140c075a0044007141c110a00424a0013058003615103000020310f14490f0f40e0144103500f81f420801c440c0d1000c2a074400c0929070b0307 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 428095053 1250 428093803 428093851
    0x90308010f03050d0f11030d1a24160213090203011103070f2304060504090506010503040818010e0402130e0916150c020a03060b040506180a0207030e030a0803 70
    0x212a00c0010107591004520030f00b41ca0144071740c0000c00b03c0c81d09080030b2211400840c2c0381550700000070f0640840c1d940030f12901c2080040082a86840180d4040c001034a4240d5074960742098809100c0c2400e0340482d044045000219086c00c01c250b01501c4e40030318840010000028045d850b204911075420411f032601080410170580c2d100c2c1c1003039940c2c0e54600141240c03da6400311076694030040d4110107407405c265002030700003d0004103803950381c00d030b9200d01d00a00308044401c060038690410000b0810300000c1403c0a0640e00c49420350380320300b160707081b0460042c0d403504900c8170401e03005800800c8031704055000e003c4440849111440004007070707aa203001103441e598281401804080d0b40b0303106100086010b44c01d100c4004445c1850900c52080d900010f0380d45140794011543d05850b08079000c403078100b03030181581095064402c40036001100c110300c407001c50000c003d5010303035070f000c1441c0d41031600c104401d1903000b40117000e580300a500c0381001c00c0194412506081a42041c00e01191320304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 428096303 1250 428095053 428095079
    0x918040305031303020a0807081902031602040b181008010614102304080601060f03020c1b040207150506121c050f07140703030e0d080909090a1509030801 68
    0x2940c5565054515500c049a03d2103240e80142e059007148a060144000242240000c00080d401025a15118030020308510085500d1021344021034005201d1140c4008040741500b24031981128046500e00d11440400d80440c03030120603e8030400218140180b00150b80f241409944460000340603040e115180310742656143c00040f500401881c90205045200366004410340d1000b40260b0944420036404a001d500f00703811800f0540c001d103004019843d0091804a98155542820742c01d040b100c4680075140e40c044103480c44080f94050a060301c4e17a031039074112016140d1160f054040981d0305000b10000b40011904c01d4050340c01c89c2e508100d40c03800042c0c0401070180030b080e8503d402460380c2040720741303804c901c0103070030005018408400040ca080c501c042000882c05c1c0100601303071440c1801042c5c02500340308a80280c420450401c0400c84074000c440b4201c000340d401140f5a1540c0c0012450007016250242c01ca6462802203880c0d00c800f90403210300603009590b40a0a030340c03540600c080071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 428097553 1250 428096303 428096311
    0x109020105030105040f02070206120108152710060905091002090a060c020d1208060312041508100803160c050a0f03200a080309091806040311010b030109080918 71
    0x815010b100400551800b500081c0d4499205580941410210b41c00718020b41c001c50107940c10390200500621458800b04001301d0050b12500514260303080c00c86110004000c0c0e00c5100d0701e40da040003000310b81400300b00070461441000d8001045003a9032244248000c01080e07030120810b00944101c3c00d105030307003402a10081103000b04240e83c45403903c00d040d00c0c808041c080c101c0c0c1100d030b0350321580c012507003d900304800351459844590551610200709401c00300390b91000d001c2200f080c0424010a040d264451802d1802da040000140d16103800c140d107008440c0d4049075941c407000800038000920b0344080e507403c03480b9244890f102d940b50300810541031640e0080e08a05200c80804002042c28140081c912400000b030ac51201c6130f1440101d20880c00c15004080b040d440007458004c4d81c20700a62040e403140e60703849000801e410700810540c0310315018001904200b00c000740c5640340d200030742c040895a8801002008500104d04d821070b440d4000b43c5900d072103501000640080030038220065072007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 428098803 1250 428097553 428097557
    0x40501050901180b0d050a0c0c0521190203090310020a05070b06061c06060e01020a0b070e0a0806010e0106090b030403090605180603010305061518010b07060e06070f080901090201 79
    0x1825070040045030700c41410000480d6159690000107480041e850050104940c070300804102860042101c0c1c040d502002594401c20048002c00c1010a001080c2c030741109050040c1e241000d1000b00c0400c0050050000d0040c1c05030030592114103e64000000f01700c00f0f241074042e81c0c8440341401c01ca008900550a141020501c20480080024a08454070760b20401c002c4c08941000c800710b855111092410394901d01451f41c1d541d0a220082e00812803401c02c500034401046c062505a072480d03056000984820284202a18801d03801d50303440c603465003e018004110f031480e40c0e691040504625080c40703082c01141ca01071011603034a041100b202c0c441c1f50035440c1c1c01c80c003600d004000c4440e6849408900842d04045040003901c3c7e0390309000714025130040b0700034001c0382402411800d06800448420303204440c50054000340c0140f112503141150a803c00c40350300c40640f070402801414200100c41d505004038420440015041100c034041a0300c41e40d0303900805d54447c0a400e080b2907241e41d010740 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 428100053 1250 428098803 428098807
    0xf0106050408060a0203061513061d06121b0304110112051e060103020408010e071a04060f050319090b0403020d09050102030f301b0703050f090d211404050105 70
    0x3c008500f9400954000310040d000a0648801c010304a00c10340141c8000b56459130341d27000c100079813548501460703e40d8184681e540c258003d1000010510700c80e031654004044d1f181c50000d100764280c11007018002c1c0c03512600030303540d00d002d250600f1407503203e42e8404d01040754040e0b1f600c1ca40c1340300e00c036aa20821218000b041c2500c8500c0c0034110440000300250304040d0200808507a10034280600c02c032500881c40244030b07213420021031a0000c4940b0103051040c10041c0004c115241d0702141038003840c103090505503541e44450303035001340c110358141540d040d003420640d1042c2003000c0d424450313100720b02980c2510141040d501c411a044440c0c1c1c41140d0050780184800240d0501741c4c0020004620f0070003044071002c11329911451101c5100035400f401102510800c00603141c041d038640080041c0d9141189051810b41c0c000c0d10502030b0000c6800320748030109181d2850f4582d0b0840f03049a03600019011030030080d00b00081030380784110118100003248490b01c030300c080600300203a5098900c140c444034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 428101303 1250 428100053 428100061
    0x1517040201270b0c01060503010207082502030a0f050c190b0c030c0106060504031205040303020a11041401181a1003111603030903110a0309030803090f0609060f010605040806 77
    0x44072044420200503502900ca8492a91090885100402403c50780303103443d00c62801035803003821900107a00442c000d9004020031000201d9803070860f17000c0e5200700e5044868005000120344050300068009415101d540210418020041590741506109071704031440f241b101780600107901c607045990700d25001d24400500040c005500030b03000803251041260700341100c0e07400d8a03003555400e900c40d0f00401d030002414000e1100c860b6590202c2201802c0c110b24180c510b5034000d644074030608000c0d0002220298054079650355402000800b41211042c0d0300c0395840320342e1850b9854000c5420029503242821968a0056440003800c1a500041c000000400c404106030041c009201c80143c1c3d0b41c10402c01440c40021400c12640c5607402a40c00050028ac2868040c001d05c1c1c915850744115840204550000f07540500700c5010b40390302c0b0301c0e01c94507500c0d5000e1003854110003601904c0306005540400c07032214000580940b09440078040d14410340d0b030b581415030b00c0d48030354000e10106802100000b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 428102553 1250 428101303 428101307
    0x3090f02060c03131e06020a051510180617070f03080a02030c06071205010b0c0a06090309050303070b0a05180d05071a01060807020c0423100b03010f1517040201 71
    0x1401c0350003510020349207866022004d40e8501c0035203400041d07116010310794040d00b00d4696108078001d450540002e01900e80356458840e9185170803403541c640200d23060001608080c0280300361000741a1181d100c22840800540800074018a0160302d01b488441101400c898200203124000c80e44203c0210b0702090039611001460f40c8030355510340542c401048004041d4804005551080600781d5448800360804c104100559006901c04626164180300200617071a000c94800071440e404240060004c08a14007a18500d040c1d5010079418007020808106004101100512601040104018a0740d500d40b07411000e000d201000000303035000783d02145c081c030702a6008101d42c1c0e0040c130541c05ca017101c2d918640c245207801d80200c80060710b03010502140d1a01003081c2c40307030090121800d010303800e144144c0401002b40071041c1d50b9940900800325120030b1071b82d0240006030230a15905a900d42c0c46031280036450803940301d6818500f00007022003030418412142001d60351400d01c1c1901d026190b503001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 428103803 1250 428102553 428102557
    0x703050906040b040e09010b0621040f0b0702210a0c031d030a11040b04051506071505040305041d01050f1201020c010518070e062b050a05060a05010603090f0206 71
    0x1426044601000b000ca0482090310140000780f448006040080c6480e403440c909442034442d40303900401c01400411000c803a000c040200c1a030b80210380900c0c507a50b40c201754264103940000500144280301c184a015070780410b251003040b600180040307580c11003150715a01c500c1514001000182400c00321000248104007860310f00e5041c08410049010843c002820a00d48c2c1c0d030300321800d909221703070300200303080900841c10201b0301140c08011603d025440c43d4001d035a26415548640c00000e020801c0040704071450519484501c4100100c1c50f1914007e8091707441070003119078154000e80034011080590103001e040e130704060301d000e40880741c24061080d204d6030340c0d0206080395001e10025108420900c00c03a8800c00b00c6064800c502040d44001ca820640b00d6040062448404070800c0b40c81e484814a00d419220400307007000d440010303034000102d00c1c80b00348001042405907403142018020300054688c000c40d100c0500304542c4c0d07681c1030150100ca00d00207004062505000300c6002610785040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 428105053 1250 428103803 428103817
    0x5090712080405040c091503050a050c120402060c1e071d01060905190302040c2f19020d151406010503090a060f0204050a030c0f05030f03030a11070b0123030106050105070305 77
    0x1b0054095500c074024400c1034104130112100082e92801009920240e500074a0b4008140311051071a000001c4243d02d5029002800a80120b200040e10950304000f007061514900c803841ca1040b0701c011229890b512031265108801c10340070400d0683c3ca40ca02c0214509040b525543c6900074401d151905100c0c1203042c51241750054110401c00002680321030044180000699854400b0380003042103540005c040720b040483d07500c40d030b07040c82c981c401c0b000503c1d481d03881c0d40c4c4030181006041c584000740d440041c04200414601000440ca20201c290b03810280b001c40300301e00341c3c501c00c1d5a110011a21030101b200c1c40c00702c640c06201e100003c100c655100b94a104195600035180c183c6481c01b068400300a54400c66072001804e00401000564050000c0581802c50113000546061103590380d0f68000a00582111a529502101c0f04c050483c2280ca81e550302580c10300b11503a42d910300d4140e50f0300b008072a414441400c8515102d03850f062280c1c0d42560390507104c80f81001c485480031200c5030000a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 428106303 1250 428105053 428105057
    0xc050c160e1b1e03071806020a02040e03040302100810080114040f0c08010e030909060612011a090d060b091e0a0b041814070e0405070b0c190605090712080405040c 72
    0x2402240c0401d203510628103c00c1161070b58a0801c41002400c4c1102d0200c1c990508845c9481801607560209815011540441d0085000f000402c4954198421070b0302c002e522480d40c4145181043c1c002007006d00c20007a4012094207150384110080c2130b2500d101e10707014140d13008400240000e0303040340c9100805d406040760142c0a0749a40a02d405c40f06001000c0d010303948042041c0c0c8951400131440740d401070303059800c2424903056480349444001e042c083c0201c50f00581c0745001c903024150050b1400d2a0008240b0a100051403c00b00000c002c11111a8080d42c0144005154011100e4288194079901d82c0034403419925642d0380b000914042804951060300c84030101301458400c0b0b40d000c1201c0c09044c010051402120040e86482102d91084c04409882001c2101261011860004580342105c1c0560341d0074131004814109651a52001e085040d038540f4001400f0165224030721807010401110078607500c804070000340d8040c0310002400100d080000b803103a410950044000c00c5114 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 428107553 1250 428106303 428106307
    0x303170109141819082a030a031e140f060603090d030b0a030c0902040e01080604030527040e0a0203010e0f1903091d060a05040209060a08040309090c050c160e1b 71
    0x14020441301050034007420b41e28410081410a0081c0c0f210007030355a003400068039a03403003107102505030b9240d004800b4500c3c04d1540d280310106e000ea0300181441c3e12041081000c000800c0400c0c0500d0b00440203403221188081e503a0b001909900f00b01044038040c1400f03600034600d80c0d2510070200c0107000000d1107580c00c02101c0c4030020010b0360200c1d140d0040c15078444007507291424005940c0c003062050307000042a41c07040b014000803079080030450f4503041c0d10441c02c1e004c407001015480c2c2514001c45101d034100d440c240c0c0d8620400008511003090601c00ca00074080303032415440041d981c00c1e480b204181150800c0304003c000f000110755843d10f07184642856562035036944142c1d43c1c100c5441824911003144082080380c01e00c0c01840070350141504540450410000720701040c010b010300400300d0240600d83c000b260504d4000e0482340b005040441091081e100c2000300107280b60014141c122180c807915543d840d4203180701208909035401d1400c44121513554615400840c605108912030101d41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 428108803 1250 428107553 428107573
    0x40b0a02130b07050d02120409090503120a020d061e1710020316031b05030a0c110f0309010e041b08072f06310203010b0a03031701091418 61
    0x2041001a000b009803441c540d449511505013642030050180b410021074011004480800c00050243c60030f41307140c418005001c2480d49030281c5180b140920304800d10344104c0400c12400b60980082c40c141c010700105005299981c03e42c100925010303203080d1049a10003000344050703650781d044032401c10750000c11a4000a96030048600f02da000707803551010b003040400603e5520b03406014031140d0086940003030681d10602040100a4000949151980303619003288000c114421101221090080c4041da0301c02c2d001d0040642d0350341d00c07800640d40400d504013032950252500b80301d0b2a0000390104181c6a01d4000e9110488818100800d04401e000b04500034860ba0300c0f5000302c45005104a0788000c4000c22000019460100e004100540c21a1a9440c20b00e41c11580a500c0d2089118100e20100c1c1c074401c1e10010340900340605085400a00c0d036100001495481080300b03560072521030f440201c48c0d132500c48034010b9402c40d104d12048400010003044501048070366000c00002504140d981c6005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 428110053 1250 428108803 428108827
    0xc0d1d150706050c04051206040201080406090f150606140702030a060209151c06090203090a030e06070222060f0e010e1320270c161211010b090f040b0a02 68
    0x1005813011038842c0004207040c003180c100328000480310708100004100916281d07000a0039200010001042d594558040d0b0040050300f0540c07494082d0b2041c0f003c40860b209002810007006148602d40000c0e510940d0192300040c84405c0b210180c0d000380c041c200d00d070f0032a11041d010750300021305150816080305c2140403000303400014240c80c8046401075100e020b0300c1380741c800540d034003500300c035010a2040060007018400020880e04041d80b5080011712403c00300005582d6005011000c0d40000d50906015072540e54a01d00210704001107408000b4141c803100b08503102185c50140d0240f0154100c0140000120044001e91140c0c05201c1c0034100d240d907503200c49506000e840d1070030b06050158452074261a008801c2c030780d600c0708102c40d5000250300030003101e1454005080181e090740d000802e036400d518500c444c0303080260480c54030072030270f8202031000b0101e480744003e419440d441d00c0320340001d62409440650290380e240454260030f440707944a034041003c0103082d0845069080081600c461 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 428111303 1250 428110053 428110061
    0x20c062203050114060a0b0909090708030c03040e0717180703140f010b04150e06030a0506180607030525030905010c050702010e030708150c0403170c0d1d150706 71
    0x98031600000c660804c02d440d40c40c19641000d0101803050000607420b220100740c400c1601d1808904444846050300e45150550030600d05400c040206e010009202010000000050040312007965403580309030f440540c11554241203010034078070191b0f45004600d0b200c0c0c85d84107418400300c00c041583c420300e559949a02c2041d5a1000b00c240c0c1d41c0181d420514091828410000e6200041d2004c0c082c00c2c50420a038112054140144401c9184001c00f180807600c00b080542089a44070301119081d041051564990404440300345205208076400120320600c41c1c055280188035040d00d160804c0003160410351a10321900c55801050341e5417800e4004210240904903500c0320b1b903154140c4d103a0031030000400075154007201c14029445040104143c0c0e00000c0c404003001802e948500441e16280d0307204082c1d101b19440075140041c0c1e50780100e00241700c04000d103c580c81c0075040f0303400081204019607802c0e1845c0c0d04583d9000c103103a0301c40c609007403160071015005562b011507490484940c0c3c51000b11 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 428112553 1250 428111303 428111309
    0x60f1e13060f0e13111606060f09020c0307060e0c10050306120307050604110d0804060201050106081e06060a022103091207050c1923041506020c0622 66
    0x30410801c00030709810084003000e041261070410a40340d0020081801c00c84140c0281800d103130344030454484002240191403c030304040d10342042c08500344c00d000c4c014005600500a0407940c45e00000341200e018030131640170701c00c028051802d12070a9180c200040c0780d241c8071440c0d03d009506c031080281e55520703441d03032502040381c0700c1d55102e0500c3c0040c404090500c0790b01d400c0c3c550003044003c000c00c40c0040d18560281c0e02c03101e07021000840c035020070f00c950300c8800c0c010a000d41c045400b10311180c064121034140c030051741d0f078070328199561059222100c400400200003200190f02040035414010b000740100040b90045903100c00c11060345104410b4160f008406030030b0048180840c00d0000c0c0b1428418817800548a4205190703500c905440704441100207204111001d0040116801340700c9140c010101c1640340ca0f40c0782e495151070135003281c040342464804c614011b60001c40700e4040c1414000d135101e81d401030100304070b02414044142d001903945121034010600d4600c5d40d00e2045040030203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 428113803 1250 428112553 428112577
    0x60304030807110a0209010b0a0201150303080103150b060d092f100207061d010c020924040c09140319080c160e04120c0c0605040302031b060f1e 64
    0x402c0c64a408014100d0050180403d00c070703005180d00c80050380d03d2110560540702800002541c0d1114050700303170f0060040d049205002612681c00009064100411504807070080d0801481030f0154503101003184c04003006990301c40818440b030410030589a00c00e51496200c0c0160130405010006c1c025001d011541b044940407040c000c40d020301e414409690f010b45d20b010700060032030f1030411101802e00c150941d0958084040c210000050b68072605111002c83e0300a40032459500300705504a402e2440c0486c41044a00c00080700f09090034540310303030500d1b44e0342595141c447c58203005103e0a0b5940030401c9075450703c505030550300302d9005c41038910056403003000b15668540c1e00c1c090380b5080c4008200c40215008503a00200807803d00080416881903010341c040040d100200c00640f0740c2002080050800919500f000c508960460000c0045c0c90084007100c0039207400950f20300c0038401c90380d80c0a402020900000391101d400b60090901500a0083d405400344104110600d80d0455000310782 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 428115053 1250 428113803 428113817
    0x6061303142b110a0305120c0d1a030c01020705060d0c030608100204030b0a090f020607330f02041419090207050309091e2e0308070308060307030c140f06030403 71
    0x4116006000c0c0d81201803a14081c0041d144240c40250407409001c041800c0f440c040390001d09042101c0084a07a49e41059030200099403040d10140400e44043c8030280c0640f01d581101c95840d800090000c1c22140010100d501c0c0030a4122038001400e03030302c41c2400c141034480300c002c00c01c10814052001030160780c0c400141c843d899400c0c0303070302c0360f2030701424000510789031140d100041a0301c2c0e034400107040d4056400d5992024280341a1100203452042d000045d00b00000c0c080030704c80178544c1050303c0480d100090000600c080048800c81c4a00d00c214018030007080c86241c050300300003144040c074080b1100794400c110f40d518802c01c01c0c4e900840c0f00701c9140d000002e44d941c240c030740303107280c2d90b0048d121145400c0a18041c000050040c10003a00726181030801c0007606454605101d042c803180701a4060702c0700c43d281c0c1ca161444454001c15411008181d85000044140c1800031781d44003280d4000c0f0101d0345103840c20b8000e10b90007000540164006955051003083c54840d40300039805684a50786900d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 428116303 1250 428115053 428115133
    0xf0e0f15010e010810051806040c0602060a020f1812150718060c1b150c020a0605161101031401060c020307150e01050309070312020d02060606130314 66
    0x180c5100058100701580c1c1d1101c2c0040c0060080000c5008000c0e1902d0390014140c0c44810a8001841c86242101441c3c03290f030b03040004000da42a455000c40d59160201e0f905529121a804207a002c1c110150020480c03d000301d140e181c00c0b8051004c6a448054441d961f01202103078000d0806001c0c003c10307111800001c0034420b0040d13220702e02684204155001c070b604d290a100c402001c007051810040e1180c48083c0002c0001c00c03904c29000700030501a10700b24608450302c0005000643d03460000d0307100d040113260010f0b155024a048600500c901c06005840400541d91381c2111000b40104504066813000f042586541c81000c0a0103851385481c8c0b00f018003143e10401d81b4043d4903411003598541c141c0034001d800e40d00300f1200d41c5d4484007401c03c1034495661348142c6151500b03d500250503c000c081c81240d98a4000c150500030151a60039203a440d5100001d0110f540f00e8031640d020001401d00d001c0021902002c2d06040999024068800c10411070000741e212400381d000001c421040580e610b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 428117553 1250 428116303 428116333
    0x15040b1905070309030f0c0510020a060f050402090118091707110f100e1206151c0f15020d050106020313081b0409020d060905030a0905120607030f0e0f 67
    0x10040302601840c1640c981500b40e5401407000c0d10a102c014000000c0034610010031580340d0303092001e02070103020100d4001140e0300003583c400c044001542e9031450082c1d030508080c424011248a070707801814064580e440c1c922206028910110700810981d034451036000000d165a072104004071032480c0c25500d50f9035a04000b02c800240150b544c1c8078000c102e56100b007684500f2145000317032140e420310040409162001c030f407c4584a510031a420b0041d9800c0110600c042d108800f0742c0ca1080e907154500081088030502c0110f05900080c0a101e00d1055140c001040c1484034240da01484c0e20250034090040ea0140a03590217030000405070304003280756010700c803074802094024010328004004092401280c1d210702c0b10000b150038000d40c0c0b965401003e40d201d0344401650a40d00c00004c02002915040040d1070b0f0b00401501d00c0092065100040c0da40b625040f10003013081d4180103000300e42c881c040242d0040020513044507030700d9200c0110032007103541031250581410f030030805000c10742001140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 428118803 1250 428117553 428117587
    0x10807020f01090f030f0f08070e1305040605042a05060904020d09140d170a020903160b090f010f0f0f140d060321170717010305010209030f2a15040b 66
    0x206d102044402c20001000c00d0303100700d0709500b00c1c4840c00c0085441c102000840d13000d210b5074180390b00c1d503800c050030b20080216039404244103034000c4000d8a006900c0b8000608401034030b030008650003401040900c414036251009055110300200014644529104080c0030307961840010780c2d085214070b8848958510900400700368650703600e851045084080010030101602401e12000740e58082005411901c0410500c0d0604204080241105980e0796445046038020b010702d40c015062101d01c98950350084007501c0c00102d050302c030ba110082d2000f4048404c200c607645100e040188182d0080f01030300100005003400040c18501180903821414030018046401d840d50702885c2664032841403035070380700c5a4030305003000101d01c100064651345002c0706d030324a0020a0030322440d2220000000c000b0154010078030b125040d0151082c528a505681d5259040200c60591362856108100001d1100407ca51170344800201403d03084025000168940e030801d4000f10900ea2001501e007008083d8140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 428120053 1250 428118803 428118827
    0xf02010203060315040203120f0a021005010501050a030b040b060c01090b010e070f12060e0711060601020a0c0504020c0f0a0507230a0b090102210a030b09040f02010807020f01090f03 80
    0xa610350304080b80440d9480d0060006548001450404542195002d010340c10210080c414803585a561140f001d21907070303100120b050051b11650150f000302ca6564001d0504884050719071a0074070051440a4000e40150602598032a41c2c81c00fa4150742d643e04005009100100350000902c402c05141c07401c1c14a44c1a00030b102c10420000420241d50340c00b0300094101d548510f0410980c1c80303002d00f910040c2c0741c1504094080040c103001c00c40500e0340840854541613092040b280580c0302c1c030006a803211400140580321200041040c409402d01d50018129004110100c81e0020341d0900c129040c0701c040101252180c0200c0003c004400011403c00d0510400d004c00d18032400c0c80f18001440b01441d846240707649800424010318070781c000e00138106d61070200000c080d131481d80782c40750900c543d000c18030010110745000148401401e02d08103861089030310402c001410b2500740c0040d104840010400400c5200e0404250010b40c02030180705206445503109400c1d0552910f0b01900c0c40e02130b14 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 428121303 1250 428120053 428120057
    0x15140106090b0c0307031821150b0109050415030605040819050a1209060605180f0a02041802030c07020a0f061209050316021302041e05060c070e070e10030b010f 71
    0x12140b0f140d107032000b2040344d426a9160034014100c0516034540c0240c03d41560049541d40302d1080c1c2642c00b180340302c03600081e40c2d104401c0c503101041d00b020750808071585981981d0014031300720420f00086c202a440078000d03c2200040c041001e582c0d0313a4000640301d00f01c1e4200c40c880000300314410210300c110001c01c030b1401a420503a0410085800c028600000041c40d0810079850f1840307a8144086584040064100581511518809450301200e074031004d403620343d07411235440300140002c0d280340300f52025594a07049001812a40d8103802c00650805840301c0781e41181001100016604e50480d0801404500e079403203861460f04001070310a40b58008036945480c100780701301000a9000c0700f101c850703c0049841d110002a903002081c00c0107000321100d10414800240032a82c01d090000400155101c0b0760940c5440d034554040c01001d0103041c45051150340400410705c00d060103004400d5200b0524039211910f04074000000c2e00c002d425600c0603010954825269049580c046c0d01c041c00c50741d040c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 428122553 1250 428121303 428121307
    0xc0f040903080a150f0602060f0a0c02150c0409090c0e06100c0f11041a0405090703030203040e09030d020a0305060f09091b03100906050613090b06090415140106090b 73
    0x3030318054814000200302002c0a65103070100d0f13621046455100029140312001001d4483c2c46110180d51510241c505691007592100058048903e074000c1f903c2c803141e298094502010449299018040041c3c1000000e0800303000208682d0218482d94440501403c0803401071407400c0e01d141c01e007110141c40e5a004461100180b100d2a41204c09003003a41c0d8402e010600c45019402d00014021201c0d60722a0f10606081080041c500c1e0200300000d07010049400308100c0c0c0710310703c1495a802051000401681051004209801c00e501d0340e56032003001d0f50140d902d004800d1101c3c01c00c81e070008900c0d501090b83d170b1080c048503003021848041c2c4480700b900c00300d10031b091050205658440100c0c045180140d001421501510301f1701c411900511440303010320818501c2e25020303002d00012204140504091600d0000d44400d42c0200d05000740c00082c158015150407007030006400c0c00410030303907208800125042e400a2036200345061070f01c8400210810307506101008000103e55801407406041c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 428123803 1250 428122553 428122571
    0x1030c06090b0316020c1504050a1217130b04090204090b010206060a030b100e0a050f0609040f0209060f03031c15081c140c0a1703070c03120f0e0c0f04 67
    0x280008407500143c898100c1c2c00d4020041c54200d241c1b03500c602905820412502031b2040c0085150003400c1030310700c21541004483c5d100c0d2040d90040768100009010481c5950100c001d5801c0b45000b0503602280d860040c401c6501c4664205246d403003030380180c4000307500050420801ca400e118207082800e0034030203840103040280005102d89094000a071004000001103070000d25240d902a004000091924030703a880c240309443d004000031103100c88201c3c0807034001502e80c6403110005201d19400405800c02d440c1c01c1d024400802e03001020035030000d0a1100e446107558040014101000040715074a82e00b5a00c0c50700c0500b81c48040641104d03c4808502c240504000800c401001c9611640488010807054500311000140289032104404000031069a071900214040540b1380c040c0b031b0500c0b59000b90a000001e1071204a818030001600c002d600030010f445850f4145002ca54540c000c94201004403561003200c064110b900c2156000c440d44c030409041000384000c000200303c404110b0010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 428125053 1250 428123803 428123819
    0x6060a0e0a1a040911030d03050c04120302150a1a0906010903061a15041e0b19031b170f1501080a02040b030a09021923010909110301030c0609 63
    0x380140406003842d840d18100034031018550344405090318020424018140c4600740f200e004819495024040d02900d0280c4120754003900a2a02611301c1c03201b62481c007450b282c002d02050300d41850481c1140a0191084005240411440d004080e030f440c0c0040c1c0d19000305094004134496104071401120314104000c401d81e045100c5104032500500d02007442004906900f40c101d1008000640c000300c24040368030b180f40100045c00036a6a81e07100444810120030003413200100c1841450320000d010442340c01c05184081051040200b1070030302043c1c40b910030017070324140650090440f0000300500c0c00041c02c0c02c503034000142c0040c4281007040c0c0c541865444484042c88950b4064184821070001c0794a840d5540d044600800c0442c0d041510790522064030005005500c06c113038400c1c04c02d035084400c80d0591607500300c01c81d40c000715080c0c0750b0315250764a40f12000341c203080325040c88410507000600c0e4125008100300c24256035a090b590358114076103017508003050341000c0d080003848401400885 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 428126303 1250 428125053 428125079
    0xc071715010e0a0b150406081e060a0b0703031808032a070b0601181508061002062d0109050105010f0f0e010818010c0c200a0b0c0c0303040b0304020306060a 69
    0x301c000c40100302c90508002003107010554001452040d14002070010704940d000b810140209c01c00d1507a0000ca800440350b40c420940241c13281030380700d91310450400c20214a00020504544a414081440c40c101c0c0d0180850031808102900d0000d000020020005d500002d420240036005501d9100761105416184282c090807100505281000c00440c1c21a0b004004c00d14015000440302d201450302c5086400c401d045041c1e1205c041070303071000410791518000024600c085c0150340207100c1541e802c1b4440c584410041c0e01f0401c805154209003901221103e507590281c40c803040003141070751422000511400c210701e5140304001c074440c02080c03c0e50380102c424864540910303207191302d51910000301042103501c3e5406a4590729011006c1002a044000566194000c501d0b0000300c5008050f4445c9a4101100b19503010303010a100f4404011401e01030300034103051201b03d0301c00c0031031400468915806500b20b100c03031716400700c00c210841c5410808580d000c0f00680703421040e90710305130520541e2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 428127553 1250 428126303 428126311
    0x303070b04170405190806101d0703180c0315050f0a0507120f09050601050102030c0d0c050c060406090920040302060703020f0d2d20030c071715010e 66
    0x400d82c025104000288000751030107410000e0098039200c054003211440841944210310060040c8000130b20322940c1d00c003602c030480d04120700ea9038080d4551079034007441c0c60300245440203159950b01142c031180c601e85c03245450144900d406aa095080d402c0001868140c0b800000c41542400308000384050b00904007900101e10300760124054980400a0300c008200c21002c8210f0751070005a243c402102da08a10080c901407015140c083e626a40126182d124807110447c0300d500100e55064054402c030f240d80680384c012030a0b21584800b44000036a103038026408a00003e10b0782c00305111090741d07841101aa44240606228600c1d01c00c02c032b5030902d01030741c407000c0d1003044041040030605000f803001002070744031441a01e0741e010700728101902544115000d07032113100c10098051402d0b1400202580b642484e51104581100f2402c924981011615041d2440d4001482018242c060420602c400b40c500000780c40d241c1c09045008a03c0c001e90f01d00b058190445800042019042400681da00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 428128803 1250 428127553 428127563
    0x1140609090c0f070c140d2307080703050d020706020316151503030305190221070c150209040c0206060a06050c0309090f0601091505090904060612060b0f0303070b04 73
    0x2940c591020810034012001046070740c0b03000041600030000008882d82c15180026070f15004100620700b070040b07007e00c54400901c0384000e5800c1041c0f5002629504c554030350075100300c1e2103254460b2515410a40c2c81d900888284c0e10944192881c1a01031051101030242032004604182c01410401000440d050018021454038070002c10130902c40d400241c0b104000c81c1c2d4102c1c41c0380d52840c004004040440d002c4090041d0316016600c00c0d4490300880340c0010b080c140d19407032459029004d900c1800b0240c0801d05001740d41900f2400100212000d6686054090005803940c0c01501400141c5464000f20411508090100080e079503d011410003a203080d854110340b242c1c1c015102929511401103005d511403041020858400810310300c49200b4602a40c03020203480d5101e00d15215024646034040100f50240b0030014142006244c0c41e03031041c00342c00c1c0442d4240d03947c061a0480071035841e050b1103098a4484015850424205485a000054004618028a6131240943c0f500f010788000e007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 428130053 1250 428128803 428128819
    0xc050117071e0504240201050c0c10020901020f1015050406032f060f18060a020304030335070f0518061815070605100e191407030c020601140609 64
    0x2041c688070344251030103003102c1207017080301d8107521156141039010580048010360a020001d440b400c550020b489482c40640020803140740031021440203900100070035030440c45070041c900b840c144200200849503900141c0099605903030b240c40a00244035400050082d41400d004100103184555035000440c2c1c3c61994036204c5500c0c2c00300305030708901e500401c0d521a0307010606010003105500204059000f003001c0740d003200035034020b105850288038104000350b00309020404c0880d004600c1c541e00d811640072004451708400b1303110079000c0c26581c001d14503095100104800030390400511013044035141000781c00d0500154032800c0c1e00f520915080d002c0d0001040800d8404050040c005070394200500203030442c0031002c0841015002010180e612504000100b021040302107810001d441096011541565544034054011400020207035800b964803c40b201004c44800c00d00d50080403240d40c08601d03001c59a00003490400f040c0c02c47c4c000d0380c4074a101004c0e42c1c0e0b20300c0c0459141c40c8050394280 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 428131303 1250 428130053 428130107
    0xf040b030a150b010305090705010e06181c050637021c0c090e011208160203060405010c2a26070f030f0e0f090604020c01090c05011707 60
    0xd0078401d480a0061a000c454aa503102555080e001125041403e03641000503a803070720681940c60000c0c0c42480d010610070601c04034582803140060080d840380d203842c596511007000114074007910840c3c000c686e04544040401c2040014810950462422013a00150001481c1948922100801e2141c2d0140c603006006010b0340c07040e0144c0d2802d00c00d1103035428200f1650b61407080a04602d014207000105401e4010500001c51076282e41a50b100c040e03241941d080903030710741400340d101e001000881c1403656003c10041c2e40801041e441076105900100d020031050380e0140441c1c291300c1c0c840072003242d0250742c811280d443c01000000150030004d01c0c0d0b40c030010110050280590a00740029031540000c00300248069071880818245c42551076917695542400b040f14101c4001d120305030b0040c01c0844031072552801402440c1c01400040c0014039000f9000002030840325502c10448501c2c000a00800480d038004803805000300c940701544c13003245044200205401c180c01403601608240b80810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 428132553 1250 428131303 428131309
    0x902031f0906020c01090b0609010b0a1d03010207030c1104060b07062a2c030d0e01111506040e0f060c130e042003070b0406120f060e090601080105060f040b 69
    0x2103004076000342c030841d595000c4415113406002d41540c02d135841c0c02101e0109000d0f08020f40c1c441d040700c41011980d030030a01c9900c02241c2c2a0700200c4140c00a0076410303c01055036400b84020320300e05109450301c164040c02440c003041c00c0105011a00e128070b142c481c00b001800c0d80784c411100780b03c0d40105d0004a05042c990ba1b040b40b42d100c09500030f188800410b541d94110f4000c2c511100c803d4812140303220384c1c0c001d5407103280010642e801094054000c004600076140c042e840e20421120141031540c401006804c00c1460600e2000031132002c00601c0042c403046040512a4441c0007a42101070719402c0010b10000c0d0b9205000352440140d5003001401408411280040c10040c0c4409044e103955410079082c1003900100904c10169202c054406290302450300140e61002c82e00e007007020301c1c20940b5101081d55050001b441e41c40e0302a0325250001900d6006100b41d402410384a02442e10078203140503001d2810304140c1080e10303168503107000c0c002c4030f640d49000600354580c1160301080b0750b5210004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 428133803 1250 428132553 428132561
    0x1b030501021303060b030c0f3d27030b0c0d06030303140f0115031d011b08010b04060e2709010e12040b070605091c03090b0601030902031f 61
    0x40500654408203401d48504010590282240d014607000c4c00001481400c1680ba000100c0020340c0c040c1d0171410603c03060420f8a124060903102c2e01c80c8001c152a030980300d1000ca8011085442d8081c02020441ca4a640040603000d1107040c04185d030100c41d8184445050482c1d41d404040c05900c02c20f00000c44907030010b003c650350b01e80e0b850014000d65681c0d2030040c000e0070a03046100c071800145400a0030000d0070314080c90494003101b104041d40303c006078095004091000b24500302c4400040300307070301c003000c24000c0307021000c0070f000708501100362184028003601042e0070074411494104020011160301c000d284c40d160f101119604484443d500b28024009003d0440791040305802080001c02030b41980161046007118042c3c6004da603103180c0380708203849140213180d8a01024009000401e00a902103135014070508115190a0415002034004440c04188100041d484413602800c01000c61000b40e0048420f080034007080a0f00e6002075122407168100508008400b80b501c5115001504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 428135053 1250 428133803 428133809
    0x906030c0706150f0e09060412050c1c1403101e05040c18060302070201120c092103090509011805091207052103060120121c1d0a1b 58
    0x4200100000109541d24680044c0706507852008075840000d2659109829a44901c44040c0902610f5845a5481510202c4c440d0a04108031301886a5a9280d004100c020611403024410150a2401c0000200b03854085080008035810a0080c00b000e0b0310410341c6502a00c0705e1884044d15211461203004000c0c23050350109900c641031602e540216a04680c80c12100408080206446034031000d05905921521000034005104940c040303080302820340c0a000000301c03d240902c08513544140454044642c61359a1441c082d403110308008161304070f40380d45d00400041e2014004c0d5858020046c0c00d2161080842d9a2540c0f0b03500003414409050149101405604965645a0300300381041035a40042541d1503000084404501c04074216050a9900c5850141e46941030f81d05000d25541a8010b0501f00300c42a00c00c3c028940c540070002d2010380900702101303500c0c020034511102c43c102619034100c1c4101d07030300001004600180c40085841000c49401c0b10b45552145000d0038460034011f5640c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 428136303 1250 428135053 428135063
    0x10906020409021803030901050906030a020408070806100e060a06080415240e010b16030e2115040b180a060603050f0d0503010503030d1806060603050613110906030c07 74
    0xd404030b031002d503990107845141800c0021030b8118929605142e9280325000c00c0ca40811070500c148031441c0781a00007540e000d040c0c403801508044d034959245140c9041500a040c10350011010032a030b14186e6a0001c0090007040424034050034004040760045026000381c00800651100050034801c07403004030444042800c1c420000c141c4e2038150b8100d0b284505c40ca40c04402c1e001c0200154400d030904025044c5e414615603a8507100044560301100d40e1003e0085060043c5030582071171030f03a5170b01d50304204040d81c048483d140001d810307076443c100b40748810b401c0030844007101440b0100d84849442c070351216862058800c1c04105903441ea103030820001000300610301300030001c420042d0125404000f110344500f210348180140c502603441d80801d0141c07503015401440220241405504901c03140b5a6484600d801c000c2d10f038490006030b0f205ea801034808240c407141845041c0c02c2a045920a40c4022042004401390900120001b40305404c003c41c030826020012400d948504411103440e2980702d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 428137553 1250 428136303 428136307
    0x1030b1909061e0605070c0e0c03060a090905120c0f0601080f01110a0e01050f121e010b0906030a0506030c030d0e030d030c0507021905030a030e1002070609031401090602 75
    0xa0024480040e8091425a81d0824a0005a40c1d2101d0024401503588201c941030950030101e0864030b6400c1542d0a9030303048004c00c0000b03107210340340b01d01c0381c059200340c442030380d69142007800e005501d0610751108030710b145001444000f08001140040d00403818240c00c0303598103585600300e454100140341c40320352809160f0001481150000e0415400b07020301000b403149803102c1064500c1c5014260100010481006400e0503e6110360020f00c194000841c14030b040100c21055a240020f0840790303d090300c0480c002d91901803030f0407900c2c14010a00c45501c2840c00d070740207011909502002d4403c1003070540311070105090b5642400441d0b1030b2071010b01111011210120024010040c2e511140e000e8010722260b000c14901c01d014841c0d0209141d19040c0c5404625400c0c48070600008040c244120790420340418541d0f0701348039244040c1c0c000e0381d911030a0303080c1100b0030103c0d102d010516019540b282d0401c20015800030207507000c032904500615102807180c40500c2c05003809420049c600307480 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 428138803 1250 428137553 428137579
    0x1050a1b080c1005090106090e0709020310120809010306051c0f0f06020f030420280b040612050f04050606090403030219030515120601170c03010c03022809090b01030b 74
    0x1c503611407417040d09400000e006055644100b18100e813418610001142c110f03250600115005800864200400b00041004940e562214601111200e4011223200720002a4001d196a06001e0400071348800c071101c5010b1640401c42c0402846540c00042c8150001c1014a0601c407d407414030381e489421031001c0d507880080031070f00a110360085408860b012000202c400c1042006d2480c03120080e00682251000b58540c5040512000c4100d44500440034407080403a0328500407000c4c00040000342c8074407903034185500e60503040c3d400040a010f030140e0200c00b0080403e0001841075001042610f01c4481516103060071070207032040c03c401240d500e070003050046695a2582c070030352054608520710011445d854081140d10504484040010f5100000501000402500200030484a44c003241c0d528003003400800e0a4542a080d11004682e020a42c44051084800c010700040303008510010360350300162000e45207a420780100241550788a1680f282d5900980c005401410000c00b0001c40043c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 428140053 1250 428138803 428138833
    0x2030a0c1e080705101806090204092a120206071106160c030209091914030c300f04090b01030905010f1b020109020109030b0702012d0b01050a1b080c 66
    0x10003e181140e81e489003401000c5000300324456520103440715403090442c004683c84000c00b0700800c500580e44282d8880b4100b0000301e2814182c0c84002110060a00e80002010030041601099000401c0341422500800041c0e035080111154aa03003d4440c4481e00035030310216200340103d1101d140c00d8000d01147d0300a202c07903e0200802c81c0d100301e0320058156203014201da1a106251a0103008400c5401504005001c41c0002c103030700365900c82140d0402050a14852038880030910141c49041d442c0900c07503c49a0b20340c80040e45500500c0765910b443c1c440c01080c501481240300700480a555088111280e070700c25002945036980020007441401302c142d18810040c841e140340303400e50407070904107a01d943d070040c0148044590142c440d0740d14103140d40c41d0105100c2000381007a0455503120315141c1e0100c000c244c1c40ca1354184201c101014a641403a101080310082c00c0300b10305228040c810754588a91140d0110611a1000445180c042d405e280906c420b004030591144280201518003076210303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 428141303 1250 428140053 428140057
    0x70315030809041b0c140c181005010c0819030f1e06050a0f03020906030102130303080708010803030f01060302070204090506070216050f01171504061d09010c02030a0c1e08 76
    0xa40111420000850364031246000c440c40d01a000e40400d0010501e45e021440b0020003504a401640a8400411030a070009840140ca5406c42d148500030400b4003032071008108280c0d01902d03081c01c0c1240028041e840b030b0842402000302a42046034000103204145200790018440c0035240d6100344680007050720b000407440c4c02c1c000b44240ca54a0004000740c40d140041040c0c080307485050351003441508540911508400050032950559001c008040b6521025495440114000e41d255034640c248030000518081c41a03003d00c405a10078414880d00019606110781158054180165281c0c842d01c0400e028014814028107240900010800040d4000c11600a800001e03007407404550349a07c10070103020852050300c2e00081780c8192001980c3c070118040ca4200002e80c484e0400044800e000409440c00c680240036001c072250b0000c1103080c1d0a108094006a00300001c0c071032207254010095483c09149204402c001a41c40c00b0300c04d00c1141c101041c0301d041c0082c400d0080503001d0034203007056 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 428142553 1250 428141303 428141317
    0x6070c0803030f04051005010f140411030108030306120105060a0905070e12070510050403050604080a1b0804180b2407050102130303091703070201030b180403020a020a06260703150308 81
    0x10b0151b104084141c10441c0320f00381c142d81e084081916050b091500140c0341c507000310305140e08507594083d0702500c0b030343c050b01071402000120001c41c0c0da8582603041c0040704007440050b03940c5030b042009200041e982d110501091b40e580420000701d60340e84000403900d020705c602c2004c2e0418500c642c01d5a1160300402e90b40151141a41d100c1a0346030440750031142e42c4198400505160010b001050000f42c1c108000d020190403450035181d0000f8400407455550804030044030540300000d01001401c9071031280d00000401c0d014104091646500440c40311284200160480d0b010b01034032880801040d415101a190001c000315101c850000d00020704089a00054000c01c0328102e001444480f0020100e454a00000195090850640c019409001c1201d201a800085c88000b0003c4c80c50300380700f080c0304600030380c002c0c01858298018045881c00640000301041100c040085041ca5000c1c084000404000c0002207540d4401c0c104400400c1c04602e4000d0f02034004e030b000014000540054040e03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 428143803 1250 428142553 428142563
    0xc051314011514131a04050f041103040311160306060302030f03040f061202040905130201121b08040c0f030506011a130302060a17280204080a0206070c0803030f04 72
    0x690301c03648024040e108002020000500d542c040c01c00c103c0c0f07010302900c120142840d40b641415220701001002a041d618007640c451000b140404c085d24005000107105442a60208481c000403000c0c910684030050024003070100300c860f104010141000b60f410228044400004500c2d180c0ca840301c0030b402e5500c01a07101e1702c40c150728120b85400110440301100e41444000d0003c0b450007500b03aa180c007941c03901252040d828000040c02060502459101d4070384141c0c1c0010540c1d0270310000d400c00d0710f07418415002714a41704038440b143d10181000d5031101201d081111440e95140b502c011696550340103c2c50012140500108014000804c01e05980340ba680007400145110410b1101e401582d0010404100c554020409814100010545003c0914100c10001c4410b4041c551003001900d03520032041803801e00303240400c451010860184c031040b0041d45014a030960241e52880d89032000781c400c15000074000b082000b4990700700c0041c51904140da4403482d21402c1521245411281618 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 428145053 1250 428143803 428143841
    0x120c01020405210c1009050301050a0b040e280c0803040e040201120209010801052715010e060702030a020103050618040f02100c050604031d0306101706041109040c0513 74
    0x110f821802c1040e840c03103030b00a00148020001c42c01008903109400300381c1414402d04440200da907450a0007400c1c4208108a070110700c0043e85824802110450150b086140d008036515070440e00401c400342e081c850041001100c01050740c2403907041c802d001d92081510b444006800240d003a00490400e00c030b1030003621042c1001001a05901c1a80304180006002903910b20050190346060700d40d025414203000003501100d1150301c02c11024441c10341e6a40381c41a171900c1a076455681c00420007440740d4040d40c40300d05240e000e0340403079660042020000d041c1502c4800049841d21000d119036048000022140308500302802c00801400e145001030340280400c90703860409a01a4411074180c40d4018021300d5142d1366620120f4500300c00411441000402401c200da0a6404105103401074100c0c1c005100c1c450300c0c201d85800000d00740014800c060b00b1000c104000704031403461003007400c0c0080c0c4550400d03a80717929000040d1855608019484038440c01d0342e0300b444520b035116009c01c2001d040425 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 428146303 1250 428145053 428145079
    0x90209032a090121120c020409051e070317030a020c0a03030c03150303050a08191505031b0319170304080d06050103110d0b0f06030903030702060a0603030c060e120c01020405 77
    0x1a0685400c00301410104001e030b021320740001c40b011080089066589005500404581c1c0010203540c81e4000c2610160305c103280300c1c14129034040314014101185001884024510365603100d0b00d144041040c80c180e540030000680030b11468044403a001408400d4400c60f4066240240052107403244c0280000e142921207021076290f101c50805a98040d04da05041101c2640110340e400402004442c625202002e0826107084174010f00341085d036a030b450900521309103002c0c54501410795030840b140c2d1200804e0b200c403035203000c03c009240040000c0c02c0e201d8160271303040003a0340798035441130103141d8540001007005100020000e40030401c0107000500c0020b03a200011001d0754103811410208070801c0203140700325801c503800204d1685010f070040540d504031000080351034004480680c1c45400000400c0100c80c1d0611400d903200060003c01c202c0c0b2400c1d910f005141140080c0000e001c3c558591418013810070030081005090031400583c0c0c2d558020300e1255000c5e400a1180c18040c0b42408a50 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 428147553 1250 428146303 428146319
    0x6050303041202061605030d0212060603040323041805040312090b06062203120219050703080a120c09060f08190902150a0507110603060901090209032a0901 69
    0x40d02150321184401c0322102d2681c0030045140c2c0000141c086200045d078580000139018000303810151a18540140c81c0d406950031141c40c00c1005159070300c601020410000060303080203444002521130359025a0100c0942c85140c03987c810791b0429203011451008007a03c403002500300381e00c00d5200b40c1c0c403a00c00d181801400c2c0182c07070410360001c260b100c5120025000c0c0c20003502030f0075210f008000240c5101030302d218030300d100b880a81050f200d8044003440f58a1098040010b60740c0c801d940003a106001c04e8a0326610b0700d401150100030581100003c2d429103061048043e410021040d1358108101c030074200e40a0401440303849008042000400d200b01142d0090311006d10501c030240070b07500c404405104110003000b103050120f078403030215410200c54000c03060180400c6940ca44480e07a5031999030420b0380502010340d25591242e0420001c001140e120591090b04403024404c0140e224090000000c2c103040401d10024654060899500b0440c40b019001d174943c1441a07030003244590b20b034041c0d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 428148803 1250 428147553 428147557
    0x14210a14031c0e0111070b10050607050d0e060904051807210f0203030c03030a050a050c07033c170705041a030601030b06160201020d0f02101a06030906070306050303 73
    0x10704030b00b001e11486000010154002c0350800240c0c000004141c000481c0c800341680120409903010012041004641658440d007080a48021a5450b04040c0c15646995030b800c1c4250450301003019002000c11036440e803405441c024100207005101d28545810146ca00541c3c0c5182c0c10341e40d00c0380c004005030002000d15440b4810906144416803441c240e2100403050100300740c220f8141c40100101103070480d061000d540a0a44203002050ba81090480b41080d1480602001c209060820801c0002500103003d400e07094428080c0c100d483d42c8182002d840c400704c015800c2c407640140c40d410200181c2c840b410404003024007070000165200d1075030859040c02503024165100b451448030800600d0743c1e0018561100c014900454007154410201c0e82c103801084591450600005400c0d0840d80c040c00340c4009450503240c00580c1c601c01040007540d8154140f15400603e43c0e400c1d00aa5041d01d424042444010141009030303a03050048400340c0d40c0f04c0845640300040e150000101d040c1c0743c0402 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 428150053 1250 428148803 428148817
    0x181a0a0609050f0d050d2001140f040507090608100f0c0203070206070602040503030a0504080d0c11040207080c061003020a06080c070303020a0509120706091a0414210a1403 76
    0x15500d6070550610b03042c0001c07200c0c0101890b52140c1101901800030318104941c0924001907684d000d40403400600e4010394140c01c0c488080b00383d05100446040c000c401d40803030f511115030404051903450710704040d400e203e420740020004a041100200b00b04800042860448d00007441c00c0111b6540500b4940c2151f100c2c414140050300100f000402625059014184a90186400603d815903504c00a403859200301c0d5041d010403400f0904000500703050000104140031400c042d11140340340e81d120315100b501c00411038403071130b404202c0c0020700c55030000351252054120102c0741039041942484100440610080b40314100b01d0402082091184c0c1c1c1c51801903006500050510344c09580c142c000e90030518001042000c24030030011683d54200b0300403060401100071700145410000e00410450698100c0c030000074000c5480020203501700c0c02c4800b100d88049400c2c0145001c20300003402503102200c01d00b00c00d40303110310128100c1c41c04203100710b100d44a210011f98060f001c6400030303100d0003515 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 428151303 1250 428150053 428150057
    0x524030d03050717010602070314030909060103020a05040f0f0312173106090510020f0d0b030c12011e0c0e012106030b010e090f0a1506181a0a06 64
    0x55200805001c1e80100b0380007602c07070403c5088105110b400c1840c20b1400d074884001a0b010040030400c0c054100360010b100709414010f1442d04060702d000c642c040c00081c00305410580c0c0014a0042141314009a6004e0212039652440c03169440d009600780500c0d602055990350b0020f0f440d000360900038002501c2000c41d9004030300c2184d07600c0099010002c06e01401c01c1c110401e400b40c940b80003442a20442d44a4400c00000400004904000b460010031301070507040d441c410400041601900740954070a440305c0c0e03a0204804c807540010a0419403200402c03500700c0890759000e41c01d003d042d040b4100d80c112055030981c801d40443d031403009031030743d4a200d800898800352030801154400c2e500d9084041d0720f031200d00d00128150503841d0460b142d5520594010441c640140310003100000c4483c1c00a11440041c103988002d0501a6101d0f03a07002d5004000554241e24292180d1051304642d00410302240e2036444840040700010191011102c1c00f0401000000c10090138a001d00241095903010703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 428152553 1250 428151303 428151313
    0x8010303031505060c011a0a080703020d060b060f1803010501030c0306090c0e1602010b03060610182105010c0c0506060103020f12070c020a0b040b18040f0906052403 73
    0x540ca081d030003004003008030039605a90304800708442d1140d0004103140400d01c07000080e04104d0040c3c00102d800c4248103144100302d40380c010419003d000460105981c0c040b21801008522490150002c1c03035443e15a0b9002500411700080780c0c004e55015001401c200d014070080f9020304400c2508032802400005d20842c1c0050040c004601681d001d01501c903c2891240022a214004040e401100b00d48040c0340449101c840c1c0e1425034280941489000f042e030081186050040003c3c00040c1100303c00d004109160078000740340740c2ca050800d401130180a41d0901c540612100c8039000d102e0317041013560340750300b03104070003202d14480c0c801b000d0f030b03550414040c01c0710380c40d80c800450195200d4550608032036014000303102d80c0c552203c815400362a498444190b09040d520500c510100b180d40a400d141d40244010000002144111181003c0e4104504400421400040c3c02481d5009990b005185014501d1081105030341c403a50291030032802080621a491036920790080d50320349803503015046 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 428153803 1250 428152553 428152559
    0x11103070507050a0209010f080106051e060903120703080109062c13020406080c03011803020c0913051006090e0304030203070513060e040803040b070f0e090a1d010504020a05060a0801 81
    0x1c01c0010b0300b045441502600c66110290f000203091240c00c0e08540d1090301820410800120244506d40080c8001c0d0b80d140090381f00d0345410361205580000290140f080001d0144003960b0904c01d00c440702c10200c0100740c48c0c5845003002081d120090041c1e18040b440d1210115400c1030702140510401c0e000c81682803041c80200610700c0d1001c020f00340b40c1001d076070210140c3c01030b40d8501600300600401001840500d40042c102344c00d403081440e404443d00032500248010075804100000d8085081e12a05c0d00e68071106a006699640840c024040c2c0c000c1d288214070340d0030140c0044c0c0844200e010180700c07040c0c203584903d40340e02c1640720080d4164070504c420042410420501d4215441e141c00014502d90303180c2043c12140000c540c2224280d42c00400c020401400c0e04009030003520500e0042120245060b02070405109410b915100744407140010b58103412f07a8208110003202e8122180c0200d03e40d8442c81c0c0640400d0318101c2c030070441468080341c00d003030101c180c0342510041e5817440c0311070746 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 428155053 1250 428153803 428153807
    0xb010305091e070b0706020706060b030103031202070812040803061813031803050f06010303230301050609030f1e063d1203120b1905150d11071401110307 68
    0xc2c025000a185000d04030f000110a9011400b03032804a01546000d030b80c81d40b5030f01d17041049807015000070302003071000c1c401400841d0744800c06442100780000010382e92501820f10142c3c5019100013603c0c03c02614040004001103a4041c500800d000c0e207800e1480d284544a81e0030881c4204c645a00da09004045040480e1003a0000384080010f603441174211a140e498840c189901442c10380f00c9903211200400800d80c0c40080310074100345810302c05c81031520828142c052484180b2030a0710420000c2400398035540c06011448241c02804c08503001c0c080c440c031079248100c80100440d18140988000a841035801c14007600e185c020312241c044a18444845041034082c41060400d42600c5220f408140304000040001d0310314080c1e00c483ca880c02031a28900d05450341442c07200d0003080110710405002e2400626101071306d1045440700300d6040c44601d180014069040603081083c1003401d0020005d40003001410f4140c020354031508007507804480c490070784620302c40710400306c5000c100080c07a142c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 428156303 1250 428155053 428155093
    0x31e020d1b020103091407030b07050a05040b3a0c0c02060909090f01020a020309040e010b10030b180412260103120c051e102c0c090103060f0b01030509 67
    0x90b01c141400604404542c4903103105e50075003402c0040d6070780942000c0c800d01c188911201d40c462a01c0c9040791034105c1400d00200030380903921900c01000030205078682030410203489003210503455280d6004d05500644042922500103094030400c0d45448a440a610b209402c0c4d09143c40c5c01600f00c600e090b81c06414805d01c88001401c41302c0320700540e01c20141c60403080c001401d060720710740c3c002c0d81c88102d08410001200c0c554281001c0310380c58118110302c5501d81d810381440081090500185e0906035001041c03041810561100d1800081e800304002c215400c1c0540809610666960803031056803c01404a100300d1011a060718400400410010305031007904e14204c2000d140c56501c3d50407035900d20f4549410b0a00c4440c40c032010b1700020641180810036507407003c444130000c1c86640e5a00700b403a80070b44a0034170810714804207501031804204007003010341d0740240c0283c070420389517a5030b08110307000340702050f40000c0d55410300160401540c402e0041c00d029201140c09070260000c02241d6011355 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 428157553 1250 428156303 428156357
    0x10b160212120a05070c2c060f0604030506160302030c040b0717120601021614060318070e070305011e051e090108070812031030031e020d 61
    0x103031041c00080209100140b0103840f500f100c98803065181d10381c2c0e24080055280c20340140c0007009000c4088203100840700050035164960351700310b88541c1c4403030002c07501002080c06100d4000c0c070001000001c014000a1440c03160b484203107001c3c860035030303070108070260321041d02c00305c040304c00501c800d0000c008004001c20115205084242507800d40000283c030741e27004902e5090052943e8010041c603960140300f0b1181c4116080d040341007203401d001000c030915120000d110701410002c000904d500310714016204605140c00201c03510f0b15078512800d82c0d0800121902e50010b4101000007640c602a82c581c0301c02ea15244030540d030264100070502051044660200034441f941c40180c64031910b803885018060310204001d0807543e0b0410a0440c80d092004403884400300301001001134002c41d0086080a4480c0ba03481c545540f415480c40c000f0b0107505030f07100e41b000e0700c000c0d041c14101130b00192040c03407440710a0945070f0500c07004c2906a03212216100050007280c05841d901c6007881680c6224512 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 428158803 1250 428157553 428157589
    0x70e131b030b0c03010302040f0b03100c020712050c01091202100804020d060c020c030115050a0e04020a080106181b0c0b0910181115120c09090702070e010b1602 71
    0x40c00c0d660352104501c120050b41c5050300860300000520560600780101c1c8440100b0311400d0207034540e04001b04e9903800d1102d01d6192201da94102090600784240049001881011006402c1d941c2c00d0038580d03294828bd07445540401e908010000d082d225082241a590307070000d00c0c88801060000042d1048c8800400407079002e0070385405130001402c14451040510b10b41c3c0e0050448044103002c1c5821242a1900c07100b03421a903481c10440c0e552011109000d5a902402c0700200b500c6034808640b00002c1a04414070f40c2d401c080d404500740e900307030242c03034a250301c541c000b40504400400c501071040ac1c1241528001403d03405680086060031020a800032350040403910440b00c400b091104550a4000e01298025038180e807905000544006402114048401110f844047c41e041d007002c1c8184040039440d408418001103540c04880c094403508500680001c40916290b440203444454034003400348450080c0002246401820069a03c51298441c0c0e0420024881d02080316aa00216030100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 428160053 1250 428158803 428158853
    0xb030a0605101d0a05090412020111120402101d1210020d06030b0a110301060c0303060911120f0c1b0f01061d0601051c0c030b03060117070e13 63
    0x4650b111030b40c542e04049955aa0380e6120f0f0f00b400c60380c00181e5800c02c1c901c1c1c8594401001405580d03120403013584c000f07600214100c402c2c14608801d07805000c007505418003100021983c41c14035540307044c5040c0300b075108492105600c5c19016099801c110640d041c803201c40d40d0545035007102c3c20b051540c0d50308085480100c5403c494500803c1c01644c0c006c0440071002c540f201400c00410103000441500407141c08024085182d10004008050005100305e00401103c1d90b11401454008c2c0d0000000d8505440184186444001603660315485050041c0a0f24544000180115180103d075400f8203250200c031031400d821031519102041c0410000a40c07800b4440082e80e041c0400d05c40c0e20b009100d4045d0555403561030032415100d1071002030809061040c02c009141c02449001d141c04070030304201c00000740d03000e96110114024610080d00c20303050f1043c0000403403002204070000b85181c0800c421108843d0b1540064018510300b9920381c003241f41c0700056040000ca28144244885c004c0c032080034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 428161303 1250 428160053 428160059
    0x12040f02060c0706080c0f071e05030414130902030c1207090c0c17070b0a050405010207140610081606051e030a02090a091802090615270102070e010b030a06 69
    0x4207294000440604181d1000302c0c2001520f400180e0703a039001103002c0d0701034113242c00009510003e00ca0014000c1560f2801c40c0340c07404041c98440703031815040e0050700300d0f40c5550300c6031045450790300c141110350701c0b580007840010740d0410f480c095101c90350740c0038010b801c0182200050100f40d58410740112241d000782d10011800018074402d042c03d541003960780c1b00c0014024140390f0001c030511b0758140503100c030401007178002c2414289201d40101510200140c0f070703941c1e801d080e40207000c1d8101c0100b005403810203800c0342850000d20503000d1040c0e207107003c0505a49289107966001d04000d4020402d04604041091600513009000d183c090701104008034100c411030f00080c3c1e07100715880003405501144084450808174580009803081d00010068141204100ca4038004442c1e0028450403010000a20700e4640044c0c0c0c0c0721040006d048152034107601400310f2048000c00c20747c00b402c0c04035941d50314011741c0b00181c02c2c400c481101400315160b90802240030302960004000c03528154450b4000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 428162553 1250 428161303 428161309
    0x405100e0a18320304060f0c0503031906080a030903020d1e08030a060e0601020c04090204021c020c01050c190c0201020a12110c0a230f191a0a0512040f02 68
    0xe94660784582d04480c20340315030085600700c20071124041583c6046a030380442c1c1c2c01c0800800c80e030945503507007051000000c1d034840444010a02d424001d02c11700001c4180180b0066461085010184403d000d200340c0e5240e036103030381c0c1d1600b40820180009605140400c058140940c860403c0d600901b403003450a074000d21258502150800201d860070701c00010000c0c806001d11820010f003240342c8421040d401c028000039600d55415410620890b91003000c00e0865860b5412241d00303020351a406864010a505450020b40188000c84455428500001c803e40c181c0c404039002d40f01130104405039000c03103a40c220341c80c1d00d00250403415889107060a40101d4405041c080d2203103000d580c1c20710b018420000680c248802000864010003621409102c022441c41000c15a50b18461001c840500b140d400115801085824550070512504600352054800043e81c4c040d06c511460540c4602e80d8403040c070f0500d10501201e0b60010381d040c4076a007004c010414134260451300807080030070050240e03000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 428163803 1250 428162553 428162591
    0xd09120203071505060f190e07050c1204121b090203150f0102060c09150f03130308070f08060d030302070b180f1606080903040b040906090b0405100e0a 67
    0x1005000d64000300e0110208403100c1d40c1c1c900c0b5015056000d10080c10620003040075200400090751003020a0820102e8409042e810b0070b0085c074150301036503036070700b040b5101034030650200c0c401600c640211841030b000407924800302c07802c80d0154003028200107015110000300c2c10401640e10b944204c40315001590302c51500155015240300e00c205005014050b0400014074081385501e41503401c42010015070f019004155200140305036500d00650501c040101918800c81d99200e0b68510048103008080d0704480b440e19a50348039445100e2552903901c001e035000c04020139104002809200024000d04007620341903a103030b20a00b070150622486076140510002c0c1150a10544200c5240349500311604202410251048101500a0300f0002100b00d100000d103010704000c0c8848003001c201e00c400304004440081040e4181d081d00c85846074440e40207005284107541169080c0001110745180521800740602c01c001c4d4007180c80c52030009841000400141259135041d500d4075540e91a00c0c07a005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 428165053 1250 428163803 428163833
    0x403020316061d0a02010801050103270506040201020105011d01060e121e0c0a0506181804050102040807090605132c010f0e0a02100804110d0b060120070b0d09 70
    0x314503041c0c092084604a241d841ea01c20555100b0340304c82c00943d80200e03402e4151a420320300841c0340c00112106030407480c0742e21449001c20914203981002d2060110b03082d40214401d0303000b80541d076681d08000181c044000d801c00440392009004100050241802500814000c0d11310380040c401e902880c0e00340152803440541c0d9078145500c03039403448001c0c8002e00a0203011580d1440c590304110102d020f50003541ca042c3d800010b40850503045a54140c0c40410081010b91b000603d40307014500a8080c0d041441421418803030303040c01141c0041280641030584601404400d00d8202030341041015100070340b4580d07070f202c500c0800d00ba07045030b0114540f51186044000440e17070042030181b00301240c54511001c0244d400031903003040181da500c10203094180c05480c0c5900e4a86a50500150602006d41c0f80e5a100044840001c1000f04510215105040036205e140381b803050440c0310a05c03005018416680b54100d05014024240408084c000000c003410300001e0b45031950b0788684004c002a1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 428166303 1250 428165053 428165063
    0x2726121c020406050c07081212041407060216051e010315051009030302120406050f07080918011707080706120e030a030519290105190320210403020316 67
    0x44010410071704000302002070a000008141d0f4080900c50386e1164016001040070500203000880c1c24400c15000002c00041c40e9020303100c16594074440a907491100c0009400c2c10500c0c00c0b00000d07203181c0030510301908501031544840584004c1c1c0110300403c94940001da5017811020081096210040f245000100700d480b0a1040d5055060182c40c00c0d90030070440d410000200024081d09030710030142ca890718503800516440d10400d1034110b000c2e00819284c260000c49603166058800884000d19040b52a40d602100102500614403511086180544080795000b102c0801040d403190800a100c01207804d000180d00301841c0e9201d0850344492000c40001e0740300e40c10321604003001c05d103480107000308040c100912204855030005040d141c0c0c1049064408404040c2002d0740644100c60350312403d5648a214002c1c0c000b0058001d10b40c1030002000032071480e18511016403914202c4424200105103c01d86691a110060b0341c03041c0200210114001805600e0901c40e860100c00c0c1400e100b8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 428167553 1250 428166303 428166307
    0x50d090b07120f0203011a0702010c05010f050a1b020c011107170706140c0a150b04050a050f0c0702010801050409020609090108030c0d03020a0c11012726121c02040605 74
    0xc2c1ca60b000c10340b10380031000040da80c410001046096034040c55014120560144079484030207600050321101d0030008040e01d01c2d400c141c4d01405101e100e41c0858450009100208800c05400603040da5400071401202e000d45e00c26486d0000541c0074444d1880c0304520b1004a8040e00e440c0d0880045280014140343c039a540541c10900005800010b000202d9022542c414204010005019590105001d0180002c0840324208a49401e01d40020620101c0580240711908144001100400c800c4605030348640341040481c041503080012075107103036016925201240d02f014100001084605400c9030310050400c03030210540c41e0480068020891040956240c0c81d08a1000c0d040a403005590f50406104110112070270b07400003541503101d070b0407012028101d80400010780302c0292000110603420390035031440c00408a9a90104140c5486092641000152401202c1001c44422202016030070050300c08403100c011102510181c103800264001003130307441c1c82880880c0c1c413641140c03000401c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 428168803 1250 428167553 428167577
    0x1303050307060c03090c06050307090e04051510050a05120312040305072d03081b16031706031f1401030b0610080906160306030c06030203071716050d090b07 69
    0x514803c0f40403903071050a0900442580381e5444250b07411034054030f402c1c0080400410f03010707889110000c0140012640000c0c190a15060803641c6100f402202c10700031450400103515600741a403c01c1c126000a000222401d003440700f008420300f280328003c404d5200038424810340d40c4010741c1d110700a074003c0d252141d03644e080c1e00b0454041210500400c08008a01400c0540101e495086402c066094540300e6080d80303440192003031040400c50b0940c40d149010a0042100c05145220b8919520945844605441d10040300c030f018541201c2c2e440c0e0503000301c0304100d189401080151500c403242030340011742d00d4070a10300d1040310800313070425900c40400740c003080080d041544c0311007100e885900f011001d40c60180641951098006c00001e68141403808040c0c9032402a00309a02550740300c08100c582540381d0400030f00a40007250b0b504005886280d10103480540030000b54060024486403060710055403030282c8a42d4000c41207404c0081d41e0328240000315903103050132805041e20703954581035400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 428170053 1250 428168803 428168813
    0x311072102031207030c02013c0510090203040206070803130303061d010522020301031b06110304090207080c06150301051e190207051203190614151303050307 70
    0x94428020401d560040241e559003c0701180b48603489400f51402185926441e0000c9014101e5110b5030307424a40050044805e049042503400000c903400b40c014070f000310aa0129406a610540c0c102d001e032500c0140500c81008160000c40d03100c2e001030113442c502030440d902c002e40c50b4411035003031070198218101d000070160f041c042c0000a2599001a1042c00b1414500c10a0510188a403d105480600c200030496044010082d20905140381c21916580d50303050005400d181d17100c051614080c0038101090440c024a0121a040d080c0f1001390308150900d61041c0095101403000e071815013050001404d0300404001c01407003030f02c08003010311224a445062509464020302002260002d280440800340c00c00310a5651280c50158681c111075410201040240f0528401401c14011403403400d4403a5807035401035000300d050152040211b1014500141165810f0203060f2219040442030016881c0909031045240c0c400c181c000e181805070900680f84c0401e5510454840e0804036190003440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 428171303 1250 428170053 428170103
    0x1060e09070f0e120c120606030d0c050619060306020705010c090b040b2d070b191b03020c25051f050406110703050610090c0e01050316031107 63
    0x8401e41048810540e9030000984825142a001400340c452000302d151400f10070815003982c00005050541426140a221078840e01d00300c50150091203441801e0ba0307410b101e28281e07252a41c000000d810907454241c2c0d40d44080c0f90000103407414607101c0c480400800d00700e00c02400100c0c400c00001954154600b009011001950b101e07070700c0890240800c1000602d520111100708002c07509012011090020138042d004102c000604c05d0a8041030340020000380c114540e0240d828032211720b00e030388000c1c0071100507211207152080b1076403104103800081a000b178000e0b103041c1c406241610701541c080e001b0a0194400104d0038425100511010481c90401e400d04404110410500140a500103140584180f140344200300400106441c84280181d040c0304400146601c4004d4600508201a15040240c6207001d00d0aa030361514141105d2240100240b088105040c0c540e20300310303554803403030103a0106001c1d58003050548840c81c0100c6020b60000a0641a10a581d03010619481d050521114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 428172553 1250 428171303 428171311
    0x13020a080a0504080a05130b0711120a0c0603050702030d0e031801090e01060507170406050702040e0307020a0b0d02430308040807020d0602030702010f1506090e0702120301060e09 79
    0x9103140c101800f0106540c2021110405502d082c4150703500302418105a000d01300d0380c81003456403000720b0081d0070040245800d400006046500082e0707040c3e2141c2e6a903d40038028401404000303803940c1002864001d401440c0e004010b4010b036420102ea00442d0410740c1c030390500d03511082c3c00c0011049006000e00305402140230080c81c000040c41d051803a803140000040c0104030034405c012840d0710400141d14442d00c0b01d54081d02106840d1b40da25131001e0000d03041664228032032410240c500d4010303440001074421250b0002c2440b2081c03440c2290316040c0d640054280040c0342c2d02080103c0e00c00c42c0603160f1504045030090404101c1901c00b40d41c0c000c85540603405954a1080007c01010035800b256541d00181c000154655034180c520000b1080c044280004295038000700801c0300340c076011341c0300703808102c03170340c2828040c0b03403032001013480c0b95a800d003e804081a0950402c1c00100300c105400da501c08020700450302d1485070b101018284d50002d9010320000742c01407000e90010700f00104201e801c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 428173803 1250 428172553 428172571
    0x2040f0905030a0c0b220b060604050303070506090c060f0703030e03160c030c1a030a020901090302100309020a0803160602070f0515092104171f15080309090f1513020a08 75
    0x50042c00c06071200d03c0803803086c4081c01c81d601c5040451182d5481d5800c690003800000c0c112039850f0800e01e880d0b6103031202164042424040c03032240145c41d051100454506d030450302041850110390ba58150001d000c1183c1220f0706110912440c2920030481001c000058019845032180901d1441c02d140480083e4116004480317040b103150020390101d100f07903508401a1440943c4461202c001219840104e60000c0e6000e409000c030110640d8050340300703460b100d0084c0c40300805503850f040c0c11a034910035020600c0756464880c400d08041103480d4080c0100e940b003980f8543c503285003034440794501600026160040d200c40424080854020003582400c10389071020ba40456a515410b0b55942c082c61140745880c0b11608034038145000d05001032020980300292990748048092804c1000b862070090490402404070404200c01c500041a12036401d0014079048541d980c1d40500c850714403019018004840702c5443c80202d0780d95003c0010500341c91010010384405008200400c5c50a01402e8034003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 428175053 1250 428173803 428173831
    0x70513020a08061c020d0308070816020c060a0311040303020d0f1d131d0303070906090803030a1e0e15060103050402180c0f0c0709240302040f0905030a0c0b 69
    0x1045507080031420fa400700f01212408004400200c0c03c500310078100500039071184030706a4600405410142c01405038000d0b035100e80040e41e80755205015021000b40380b9016030710510304103180c0d107403010082c004061240340126503484940800c8140b6040b40d0400c4001d41c020a1806000e25480211a46000c0e01c0e0f241041e000039845010f110024024214107010b0940e6404001c1c0322185034000c011001c0001d4910300aa800c0e9455450703c0380c00aa50010000701d251030005441d0b889022404d040d190294041c5140d03454202c80140200440c22000d84c3c034107460f0941006981440c4101c1c444001010084d001895901000c0000c420f401803a040c1418030f00070610025803503080e100101c0b1001e2a01c0403041c1d840f40c209200b0140103501102c61440000601c1280c5604040345000031a05680400d01c03d950030051001034002d0708404c03003c83d1101110041000d4581500950010b600c00400010704241c2515000e00b540c0c0218903030404200c0405600d401c020301c24078041d5103c00340010040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 428176303 1250 428175053 428175067
    0x603020126040b060f0d0327030b0c070302010b031501050a090203011203111006060c140d0203030a02070602120109050910020f0702060309070e07090314010908042c0907051302 78
    0x8003241c500540060302c0e9aa0003400078a407916296400089000001d00d440107120381803400506030598804402c1a114142c0100c8207104500c07000c020a596004000c181542d8403000d01c44030b150441c4006074119921112034072400d850030300220681d14a24802d000701e66061100707116902c20300758007130719159104200421600700c0522003a03840651610340b103a102e80384109118038040908000e20301c203d2400500150541e00700406080061007140052040c0c45d41060240e00c1d00c0c046103660300560030810000309200203a500610301148650780050808106d0206610032000c00d0700460006540d4000344240b010303040108803003e07541c207101546041460b1384862400d02a0035402406420b010010541010301840b181003e0305500f850112246040c0310014980381d56803000b600c0910030780750000b040c94811f00030702240e030383c12101d200d140c285080213003a002940200c0c940750203503045901c5c0f01c0c210031001c0041c1c002c2d0740010081141905120412120b0281d02c0504410b01c0e02c104410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 428177553 1250 428176303 428176367
    0x5042f09061903140903071103031207080a0e060f040302010e0705030c04150512010b19060f1d0a180e0606090408091804030305070f08070c06110c01060906030201 72
    0x80d200b04034550044a8001403640c003c2d40a48046034a040f881e210303c604002c00e85c10004058072049000c0c1603901c3c2016032100502d80c407846a101d1301488140d01c040090f5106001d00700c0c1d2a0014050100080c15140700b460841c20f006055812517101003450b010b100506509009000003c5041d802800c440f0b0b1a0100080d0360b41031111159000d280ca0b4042650000c401d844480e00404024050340c2c10391418800c0301d4028405013445600c640195009920460302040b004001c2c0d5405440b1100d139041f900740e040d00c17060586613040000c0880000a130076107440d00c50200e80104202204260351101c00c40d808016610302034200481680030b0340c20800150f80d06594a81c1041d0040c45007903441c0d1030ba8000c210006d2000751010703000c00c09001803100b010b50560141d803042109a4503454060302d4144202e0b20100309990200010704043c20300c402007103070b55000c1702c102c03030b0f0013441c05103440c0500e0300f080c2c25120107a22600e009581e9490400175942c20001d503680b10030f060032080c03034010240940 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 428178803 1250 428177553 428177557
    0x10f05030d080a050a150902070c0b04060203090f0f0d03120614031926090307060512160e1002060109060b09100311040506030c090a06021c081005042f0906 69
    0x251503041d4458021031003017419584001049030310640305604042d1180302050203035208610031600705940f84000103240511070300760303010b07030300537601440c030300b840d8401086011100703040380a41c031070304101155130555140070145a060748280c0300d15103001d106d2040c6004942c0702c1d51000174034421400450340c444d5400f1071032182681c01c0b84c0c4c0010341114141051021040317100d10704043e0588050090312540c0741c801c0034043c4900101c049541d615100e80302110705005035178a000340c0c210a0381c0481c9801104842140800c071141c03620b0b102c4c4003c4000000c0c000f1242c060404c0143c2c00100050000c0f5407140103120103031140d14005840e084084000c60300364081c030a0014201540e4040c4054003980d49021a0020200208855100e0030007180403803243c0e000302881403040810880c00201540007245401904400c65000000380e246814165a0021f008005000640105001082990300c40c030a440300140c02195410f03081c2034503d2003c1d0900590b10395005032420900c0840c0785603440f032007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 428180053 1250 428178803 428178811
    0x918070302060c071e17070509010e0901110f0a021b1c080f040303120b04091709030a020405090312092e020d0606020f0d0e1023040608010f05030d08 66
    0x207200b40ea0381c40c1080125081101c07980150141701e08650341d096440844904003410341d1030160030810309540c0d0040e0581d440d50780d4865150001c10390742c01004200780108426034041c84031380011078000241000160a83e224400041c0a00c0c4d001c500046030950402c0309100810007503101d00b400000c4c00002401d002c100c400404910b0100030760400400407000255029a80e03030403022a00c40f40c6900d000741015242c000c3c807800c0b00307241044940d040c1c41e16000b01040c8641040400c908185245000c074219440710301d680d50035214030501d000040e15a88a29031140d10b403140516160039803010350400c0d0701400b400083c019407200b80308440ca594158a08480d41c54505524071400c22038036080c4003c0d02408007010900b81c640040000e400b90040788143ca600c0d8014180e841c0c0002c626800e94540d8080784145030030000c0c85040e8140b0360f004506405c150400e62401600c1601500000c241c654441d030856030000742030400411020107040450b001510040713001c0c3c02101e048550061a26200030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 428181303 1250 428180053 428180059
    0x390605040201180e0105130213090213030b1314030a021c090503060a05161809020a020106030209011203090b030c03070804080405030f0f0d18062106140918070302 72
    0x2400304003160b0103240020b044490b05504140300507940c000d09011a0780910030107009030303120b14600980c40d800d40300b11404803110b500422001814200c194000f034000049402030384e0751500021010500c52541070f485410141c80401384c940e4140741007180142150030100c03481e841404140c210513000f140107071804e8540c6046031550041c06d002180c08250350345c80305405004440c14008001c8860700214819080c080d07541280b8032554030111560b41185001e0f400e60492844184604200c580092010511600c0081003554403030300007a00e400020307404042c58807900c00c0c1103070030940c10405820080440168050942c54a904042424840103000314200711810340000d0400001c60160340280c100a4100c2d94801e00c41102c1655401c1c0317a2000503403a20407000d802068070711076101c5980c200e4403041040d0119103440401e5400741901c11800c03c00c40ba40d40c04002e00100c542c4240e2005041d040e0032050748514040602580c0c00c000f9060a6841c40b060100001501c0e0024220f8212541a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 428182553 1250 428181303 428181311
    0x5040e01030305032502010b09060a0506040501111213080c04020909010302130615020c0315060d140109060f0203060f0a240c0203010510170721050f0604033906 71
    0x81d05d034564040d50b00c1c20b000040300385881400b08000d505601c001d000400903503085c01d180c1c66840070400f05109901c5031540c0400104801d1015520414800c4003668080701211441c0404405005540e001130381c0d80500000700201c200700701801004100000c0e807065600714079094500d170100c2d0420b601400301900406040018a51036085070b40510000c001a4032440248c110039140203440b066610030342c1f4828818040000b00c482d0711038104502405000f0300c80b03000d504030b907580c004501070703000c07a1610389540c0c40a0160200b45640034018124150050069030303840c110301004510484481200d02680308a40288031400c155040002c41e02119022406078030744011088503c034000540081d0103500304003e03c12221148815541542d40b54003012075203004060b0202da9440040c415689580160030720443d1800203012481c14882c018001d981c050030044e801d062400c01c00303640c2140010180707c0010070001d10b07600702500411458a29182d401c4102004003811a0041c202401650351 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 428183803 1250 428182553 428182561
    0x70309030507020a0f090e0f0d030506011e030c1416080c190507032a2303160503060603030406050409230901020301092a0c081b030903010c05040e0103030503 70
    0x1e0400d664a0b036034001c1518a0150701c07403980301c13a03103a41c030302c55400268205003408010260115001103050340c4c10000380020802540d045000c2c2c403019044034140045404099041e0120300a0646101039075100860241c0081400170840b1644100a8620582c10310400c05800c116002480016030080c120540700e803204844c2c18280407071249403e80b1a41b40c007806104101c00070420324100c0b4000d611624100f07840c64a402c03800d040380c106200d04000c0310700c000d0122038880441e0812400f01030b180f1950344ca050002007454006e014441003640c6010748000c0180e8030f0100491503010006602445c206868010040c00c0d5016500a00c08203075240d4103c1d84007209171003210f16034040c195441584c070f4204a50614000d44c000e004039103059090000b4504280e10030016900040710800c04001d0102d035104040303600500441c02252071842c00c0190003200c0d124091a94000c40c0b80d08080e60f030b00c6220108050841d44000002004e0100078041005150422290b03a811283c02d4145076940380c0d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 428185053 1250 428183803 428183807
    0x3090303060f12050d05070213110403060e0606040606020d1202090f031e0c0103020906070b060d0204360b01171606030c0e03071802070c03020315090d11030307030903 74
    0x100701d4011a008080410700069403850400800101e6406141960612000c20380219600c3c8100d1a019420800c588082c844103841035110720400c0f80c80c02400c2c0c1c1000c0d10703550380760240c1d8290f0020740d011b907109109200040c580b0f071040368001d008a0000344140610440007502e4002907074900700305613074049071510300380d12481e00224100f0001070944411604d05a001031906a14503000f070f02610030400d0304031072540288212062841c0080030300b81000090794444408400080c51940c01410050510005807990b0180202d0070342403016111046403000c00381c1c00752040c078043c8024540f80300c20060303011400d07003250103064601f0304440c0c4241d034040b04035152910b2108190550240c0c1d101c540080c1c642c0e81503100500e180c03400c0d503c810320b104000d4100b5a88154500a0305110600c032020104103150a038010100944108099085c40da66a0002814410780d170790b1114402c200c002c200b0100d11810310500340070844070b062107454850020911075407400700a0990b001e050f9180380c82d0003858 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 428186303 1250 428185053 428185061
    0xb0703091e0b010e011202010207030809060d1104140d1101030504030504032f0612010e0709080a06060911193b010306150503130807020a12030210091203090303 71
    0x50407036108440510162030848800042441410000c51607600082586403c030348940c004950143e00030038071242982c40300415a44401141e0740d00641c02c1101059020050094400c8207410408458685107420410382100540d42c07401031007030460016000c0000e98082421082c2102071170002180e0f5107514003038071039100340c2c0c002405154a040b900c80220764080c4060030500c58031030310281c05540d0304c0c1c14040c0501542c982e03070410600b110018810f2500a03220541d0040e80c616080314181d6a039a074081c24242d1000058601c0c50322001c0502c00c012486c00350700008641c6e4200c0c140761000c940d00d5a0f122004400d041020080d1001c0a0740241c105021803010070b00000918a03d00d90011030500b412071140040305011034204140000c41940094001402581a40b6480c1c91540c80f00345202c0d00142d40181198520b806000000260303c3e8040800080c00100f200020b0010003420080c1c40c243d080022030502e20b05184181000030b406c1c0c0003241c0c404100c0d00300490003003503a180a601030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 428187553 1250 428186303 428186333
    0xa020306011719061a2d070602040e0105010503010b0d020306010e1201051506041805060301090c06090608090d05070807061b12060905090a0221060f060f0d0b070309 73
    0xd981e0841400055070394110074405500a000080280c05d903507220040340c40407140d8001c0006503040c01a000c01d101510000140a1711003e2500c102003102c464080f030b1a00680c1041e03c0e0b8580c085401e101110105007201e0160000342003083c210740c90044100381030720900c50100041d540200101e8240d0740a54442d14a9040041101c0741c070040d540c14080c02808101c40595503035114483e2061282420001c85040c0d65001da424080312004500900143c40042c0642c1d816668131010b500c0825401c01450029103260351b02d42550307914003040240b1100024243d0714054104d01450181c0d2030b040703411100415401310005031640901d060520081401c0d14000c1b50300d0010704580c0314032a91100404404086c10102001140d40f914a0708007102d00032154100310341d200c0c240200261629140d14503013410781030a40240d41c510b040c0e44a0030321409982128480500c0420301c00103150074011150424070594100611509a03210300d102130310060702030400d00d5030302d0303141009021241040c0700e50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 428188803 1250 428187553 428187587
    0xc04060f1a120a0207030e040b060d0c020304050d03020715020d05120a020d090507091d071a0c01060f060e0415060318081c20090618031b04050a0b090a02030601 71
    0x803e140030b9207410041e602c070300811000038a9045940f5203510b060b106464854601400070703420094042c1c1c80301c00a00402040d1810740c4010b20000403655600b41e60703210107034404e50140c4506490107a02d095050b078021440005d5400c03c0031400341e140d0344981034940c0304004032402c7d41703540c44c2c412620000b48030319100984003a0034012041c052000c001543c0c82160810201008111001d807410344a03848040017444030382c0c1246e1020000c0b00c0d01788181d510641c6844603007514011841140e2030843d07440c0c1d030024042c040703240d10801040b900242865030031603080c0e8050100c04803617101c03c1031a00440c0920414180d6450f0501c0716000040d4603803c1e8207502040d25035440606081050040c840001511283d0341005494075a10320140001006000710502060901d0f50680400c40603400034281c0905240d02940380140c1c035541000a10701d02100c0c190b62109081b015000d00050300c0c0c004101201e9681003248a1342151266212a50311004603480140c40781c50304801200c10344142c51000e20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 428190053 1250 428188803 428188837
    0x60510030f03091401051305040504062301030b16052a010e012901080103030309030210110c0105011e0303050906041d012912060d21020c04060f1a 65
    0x20800d5040f411101c1559500b500c0d0401c0040003038011165442045031900710b00314014020001c03400c1075041b15404c50b10588020034000182d003154110400070303070340426000c211070004105002c00150107079000b802c44402e50300e08034001d0001400f180300740303080e040404441c41740003014004080c009004000b000d00003840350001d45400c4034041c0c40007032140328482c030542c4a00e0b03c4103222003540301425030041c0c640c480380b68619102a8010f0005840a4003035000d462089010b081c3d5620655927003070912080b450b15080609090b80c210b42c0160010b06a00502885110301d00101312030280459a05240907a900c11545002c9901401aa4048030010b648618091014615050349505035403a0b000701700b4911402020300515106070100c001041441000100004010011300c2a030001000d0141c0e107002c8103030360700d801407200e88001004500c20310030440c1d2a0582d060015060a1400315810701c10301d820700440445410780d91107042c1b0407244c2000000b024410b4482a10382844c41004051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 428191303 1250 428190053 428190083
    0x10212030a06170c2b080a0c0b3306040e1305150103020d06230408090a0509010e061210020c01060527010b03101707050102010510060c06051003 64
    0xc028040ba4040d43c0b4800300110f001007900c0f500080c0201001c2c800803c0400c524a10809036820034002009105d5410742c03480d00c5101040024004202d42d80342c42c1c0e90324104e03202c5030a004003100d00c0503040703880060011750a4285821446101c1a40d5044103003100da8580091002900364032495002040034912982084101c06000c491488142d00800594626142c032004607a1641424000250702500c00c0000c0d2010403402e0340b081d404488406030a0319104d122050801d004802194102c54802001442c00003030304003001c2080c02824185c0e58841076505090112008480040000f03005061400e10f00d17646600801000c038110002c402304550303031100b01030300781d0103089203020306405207407201e001703116042100045c6466240e0079021040580d00713112805506500180020111200b8110042040c880c1440641d00701060100102100c1d4580b0001a084d00e000812003540c6040e91041000f0894029045082081e405680050595180c3c503550f007103a01150005404501c00760030070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 428192553 1250 428191303 428191321
    0x18090109020a080a050601120305160f0519030e03010e030412030e0a0312090e09060402040c11031204061a090718030c08060f010e0114090a090605040f060c0305040b070e01021203 79
    0x41da10f6601031740954100303030303210550f001200e018030600130005103003008107010f003609888a040100348100e2002c446100652030b841c1c0b522195a40040007050f074110300c0c00826400a03c1103800450581c020b10045480081258590050340314161400900c0d0504800301441000400601100141030540840c0c5078100010800401c80040c40800c00364440405c0a100c44901c0c82d2086081c1e10083c80035a45550901014062103417141d018005261786241c05440103001806140342d06c516075109514050400701e054940c1003550480c0f0700c0010807119070070303150112103581c001440e0502c00c41e001140d540c100c007140e6141c0e00c0a01840074800c00807840e81c80100d03155020b4a16189400c1c02d07a40c80303030b44101c02e010081c40b8907520081c1e00d28000c9a503040ca15069580002d418030001a010343c40d03211182900d1040b1011031f512a03031250401d08001d1640314200d210312840c5000c0051345800c0c0e80c0c104100d6005030041c000d0080fa200c40d039400b41e108110ba4000c4001100310a505da08214181c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 428193803 1250 428192553 428192563
    0x11030a3e280f0c120507020a08060112110406080331060e100e01021c031503060b01110604020f1203070f0c0503010b010e03030f160c030b07080106030b18090109020a08 74
    0x1629001407081003090402c248550010019580c01143d1104000c10044003650594085e4500f01d0308a49402d0001881c90b0301801824001c0042d412940000c0b40c8514144c080d0740c407603428551249150003018042d02070000b003900d13900da040d0004004084825078a40407890604a0511030f14420000b02182840d449042c440c140b0200740e9000d101100103c50a0750250101c62041e1700607440480f81d0342200e0310000800440046a05001840000c1b0017200750f5945596041a88e9a40d110050a455564005901e061800b103500240406044c0790340011401c04065000a2142c42c00c082c4188080c1018021110038039480280700a105e0040e14012182c4840b46c8600e40c800c0d46822203403045075009418481da07030311009003c2e514180349a0080051504656800300c550304451503101c0002e12050722600140d40604039601c1180342580c0004c4c80188142c000300c081506210070030703182c0e45504040c61001000066030034015075508039154014018000048e5001511050010f186000030513 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 428195053 1250 428193803 428193877
    0x50607020c120f0d08130b041407080f0d0f03060519140102190b040303060506070c08071a090103050c0f040b071208061f0e0411030a3e 60
    0x10341401240301032000d00d480c0c04865611000fa6001184000d048910030412654084500300004c509164140c81d400031001c4210b038210f1f05683e0605800310348d078034104040b00081030070000038010309204400701d5413180c502c0360400c07060284042c001c1c010103000c0d40041028110180503c940c08009480000201c40944142058500321030071810f610b520216a000406000c60580c1e0710ba00c2c400d507902c81c031218005006070205603a405001c110740d51032400428009001c0d07000003142909010100b4140034032540200904042050f03952505c1094809446281b0300900340041c031661040700b5200c09100e00d000c1441d0381c0000113004204000c44001905002d4094194141290100c410540d2404010b071680d80d808905280140c0c0c034048900c800380780340f81e43c0e0b14218207a09544008034045c2c6080324050151501c01204126030890b0a100301c02120b01c0f030980c11010020307600c8512541381d40400180301c11020b0146001c01c081c880358101c40c03000d4824078204c0701146010b030210000c006c40c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 428196303 1250 428195053 428195059
    0x12080c0114090115080c01050403111305041a0106030603031704140601182909090f03180108060108040b160507290a020f0306130b030708010608100203090d0f020307050607020c 78
    0xc165481d00241ba00320b07420068492529260440c0c5814280e46035440101c0e0f40641c02c409a004d0707401503800358034002c0703100e080c09002100340d01e4a034010100c0141c02c00d00801d850300c6000c00210740d2084c186520110248043c4485440318204142c00e026161002050784c03140000004640c10340b06103c13090f16840440800c41042d012180c0e9003480007090018450800001c0110f240b8648400582c2d0080340803002c5450189020702500d0554014900303014120140031900e030380a5801c1034600780c3c4160246004c54407454030359200701c076211020780b500c001191301240064200c2e0141c000c45a000c0c2d0400000c210145080c3c3e08010900c80381070741d8944203e400e501088085200380240c03601030410f241c1e038504641e21002400004101c903e480a804d54440420317500949080c4000b82c00342080348008a070150410884ca07240c00240110401381e18410402c00402c0c02020491b60080c10381d600d03141000d83d4603090224914052003002410702e00412003813003102600000c00f548145015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 428197553 1250 428196303 428196341
    0x1109090114120303010e0402190f120c05040e06041e0213200403030e040b04020403080c3003010e0907080d210b060706111608091912080c01140901 65
    0x181d500ca940701e02082c400c103080e6100c044040790040c40e05c07030130325509d00707605607070500c82595581e00d056104c0c0e50580c48000103125041a48040c000190049400b401054074240718051984044c50f079a982c0041c0040d004101c14070f002c06c00046a0300d070030130445400812095007107d00d5000074000b1304241d40da0003000e40400340c149425140344c80035078084070b0f05600c071001d180002200b4840a0f050607010f0b40d1344181e003008040b0000c0c56400251960102440041500000c039808140078070210000803000b018101450b550304110344000c59055400080356060151190480c0518010301030304091890b0150105114003036030300c40b0a42d6030041d07080b8501c5106c00007078052a81250880e0540e940c01210810203007000c00c0740f940000b640303041070100881c41c00740c124544c01010080f40e03404a4000c180040e412030313240380030212501004400d03103800c0402c6240011180c45a25240001007010f81c2c00b0515010700902035014200300407062201900d10320f454007400d8002c020710081d0046036442 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 428198803 1250 428197553 428197579
    0x2040b0a0e0a0e06013209040609060e01020f04120f0209180c1903061d0f0d030b0603060307030f060923060708040c06030b030c04060603050709080c131109090114 72
    0x2000813007078101e907801981c20195200c502501d45100960001d88012031000340402140303911407040152007103010f0b950029509002d07281c5101030b01c100c0c0d0041c0459038014843d191984016104076003c030342034611810380040040c9442c10003104c90341d4000e54007e42c28001c200708000602000740340c84145a00b502e5181541d01e0802c41e001c10030804007032641413135178410310005040d0b620144e41080040f0344404940f01511060345080f61080c00440c00d900301c03d05001e500381c1c140c052202e226200300c402c10304620f400c0d40400e5071291036120151840d0700690208041c4000d60b8440b02e40c0b0b40d0411008422040d24a14a6218801c5083c00451921850000030101842001240c0c000c5a010b9282100d881c40d10200b14040c014440c41d455050184008000540c1d0b1180300310401000240c80110741c3d442d02c80409081040a540f1610300c039040054059407665482d0384109040390100000110300c89070071210b03007550041c4281c6a40140960001041d10072034000b170150710306002c407034070410025 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 428200053 1250 428198803 428198831
    0x3020703050307050c0115080d140f070209070c17030609061c1b0e160e010203190804030e0907090305010b0a123305010315090203060a0902040b0a0e0a 67
    0x41940400350000e01d061003c9000d90748188002c2c80e4044103200041100d45003d024401c40818a074003502055001d01242348841c1c0d00b110802900314003c3e141103060076080001c800072071280620080c46a280000094409405000c1c52340c105904048100422a145207500209500603030740c542c0700e480e103d8002084c0b452715610585030088a44a43c010903281651900c26011204040c0508061303ea903021900c0105049614030a0624039003400307a0b00c2c1d00c554043e0100400d80c003280d0440d04104580b10040384010419070440e8190316000401380e40340d0a0032200881002034035944400c42d10244402281d0088411050b03a000f1b10081110f0400282045011855403003903041001100000c00b001c600b034880c00c030300d0000042400041c0103606400d01c101390522580052030b0303280d03100c0040c803d120541c4030030295088800300030841e60b502a00003030b60320703200105030304601070310381400004544841c4c00507000000058401300101e82c880c2c03416081000304451405595241c400c0c2c40e640c0030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 428201303 1250 428200053 428200057
    0xc0a03091d04150b01050c030a051b03040b04030312090218090c060c100e0f0a050a170315220c090303080903070b1801150303051207021f0b030a0203010504061b0302 73
    0x1590210000c60761030700800212010b010302d804c49505200303061110000f10f00090000308521101507440307070340d1075201c0c410741c4442c040e017042c1c400c030f203644117000c00c0c44120282822102074070f0300350500498081350440c80c0c402801c940c000c02500565081242982209020003242c01030582e4426551204501e4080c090070b03008a88070011315510000c0c034040d071054260f101c521400941d0054801060104038480e20f403030043c5a0407182644680328030014004210381040c1c14801c40b00403640386082540c4681490b07154a40790740e02c2040134a0040100c81c035032013040c0e07404071500c0ba418008460490809003940e0f8540c40240c02250016000410b550780200444540c9584000c042846031120f800d0206031814048007580300f0b41d69081d84400201580080790b00651003a40d03582d07a0ba09074500d03c080d9941003c1c00a8055503c81c19210901c00940d100e40e0fa558010390030300003600c00c05800000e01d88213140b1000f82d01546014140402e12041e41c03c00360b030411001408505820100341308a04034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 428202553 1250 428201303 428201311
    0x403030c02010e1009020a09020c0a050d050307170c070b0403020f0712170304020d082a420a060f08030a050703080c0d290301090302100906020c0a03091d 68
    0x9604212004c504c1c04140d40c0c48001143d0021380386103509a00e4030209400c80c0c2c8014058502544540300f10420044100309017005140c9604c0c03c1803c50a1800340504207000c1c0541030001541c00400151698815006884080f03030881824800c2c0c0c101414060740300c10340c0c1c00840610f80191500840c00c10400700d94003103001d83c040c030162440051030107444961b07000900104e030f01214082c0c5a501181044004e0a6546440c2412441c4601d90011280305100b2503240e420395a005103100e4068044034000100f81c200c06543e1444c143c9256403100c851588074050072600704c220304024400300c6d5045601450543d0b00440414007840d4450f0341c560b03900d02900130200b00003481000303a0740010b440303103404a0b080b09141520394104904001c00b40180d48079008012111000c400c2030103400c18054091080c40c0303a0a40080201c6202b5444c002e450f40342500c400700c0380c0f503129a21130301084016811951007610800644662000d0385c900201041703000e1240c491403616428985200d14400203015000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 428203803 1250 428202553 428202581
    0x9070503100b0118090501080106050d02030a060507020c061b0f01060f06110a020406060203091315030605060f09090d11011a0d170301060908011103040b18070315050403030c0201 79
    0xc0040000070901901015091a041000000c000030070300c444c140c0040050900c050001c902c560600c0980b40c05c40719641d10140c0b140440411a01c050380b400301d610300e2800d410110204143c0c1d240103069103400c0c0d000302d40c0e40e0414400980c1105800d6400b090346074107280703001560003140c0101d042500340c41f054050492281002c02c0208212802940ca580c0280d40c400140c40124101d5000a4221400c079802070016800000720500d0500d4684250400c10101d020304000c1d000c0d00e1440b030b43c08000c06010013000c0c9590340010424030343d0780c3d140d00040020000d02c0720303d840c500f45002c15111415404904040f400b2451584010701c070600485055401d070185050781169118100404180550000d0b181c45404108441d10200050004c50280440d03880b0a101a850000f10508540f0700c08441c00030741d02c040c410301c40024080c0c10000d800803a000100322401b40013005003420f1444a500003024141128040307126401e40e0740106200b180239880400651040c860280d007610010000f8400e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 428205053 1250 428203803 428203813
    0xf100509090c0a0914090f0726010606030c08150f0105071401110a110102190e12010c0f030507030e0a1709040608030403020a05060a05480609070503 66
    0x145003041620a5480400a82111840c00704440842d940d0300094000c3d00203a41c0301c83c203041e00103841360b40d0b131038000c40e9640060407020440b2035401c0d210384090040c21003c260401e4444092001d940022101036101c90080242d90b9503900081e005242c40d1038202d000c00d8003140000d003401d12001e180500f0a00c051f2156145640c00c40c011103640c1e00c83e0f40115032211032011048a801001d01c00d090485d0310680f070095030344400034000380400c20040202c4030141c2c01080300004200d08054114200811810004200141c140009482001411078404150b203840e181d030f18030303581c0000207140498554030108040c1c0c580c0d580890641e003040294410dc0e9100402403000164601c01d054002500c0e00745089c08c0c511b415002030700b9600a036206a915030b1000c40c0070300551800c0243d2000a00f000c4820b5480e043c5003a802810300d002d1040300030307918100003130781681203190f800c00042c002c4880c182c04032982e402c80303140b41c8001e50b401c0034082c0d09100310b00010b00d6460002800c0070a486000b40144 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 428206303 1250 428205053 428205059
    0x1b040806060d02270f061509060c030715060e011202100c020f030a030818070f1509030b0406021209010e10020904111218011a1926060f10 61
    0x1161210781c1000880c1c208850b00c0d071401d004000103c4060581c0482400310044e410034150f0a503142c030b40641801d1003a403e1200d4004c4d9009032800300c508114040e54042e0700d5000c0c9a0f5640e0643c05202d00c00340c944841484882d030a0f080c690300c01d0301540c040045541c0ca903626030f40e40211205460030025040381004500b141494011400131406520007070000d064101041c000c01c0c1010368400045007c9040c0000b4458014000720b40c1301c2e4244500c000821180c0e02e05026180d0f013480c2e07031141c650101e1080348264885441203050a010b19080011240e02c0c0c2810300d8210000c0d88488040800d41d0340803400714061810600038501551149001050981051300700720f0000e610030001e58ce4001d682e0710700344d050042200081c0060785035540c40e6556618003042508550b820508030b60190340d140680803070000c105941111210325040c2e07148200800542c1e0540300d07e030359030780020301400480006507021103420382044141a07135920903a001a210745001100044c070694403280d00045c902014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 428207553 1250 428206303 428206309
    0xc04060306090b01051c09080a0507111017040503120c0d0c1d04110d050703050702100b03070b07030e03100f06140a030206070201140a080115020309030d18030215031b04080606 78
    0x207000020054070000030303442507a41c0c40130055400052001c4c088ad5000c0741110603c43d009100c840f0303400080c1c91104012a80c0180100f001000001c1d104140704203001107014001d0800642d2106541ea0281885a00f80f03002d1101e01500204e00b8040000d040070310b1100120b00c203603903100640c45205006100211402c040002030003100d080e40c2500704040c0720401c03400325503020b81801550700340c03800202402d1006009041040111840c01c40d1400c10190040a4a001569404070350240018a4554503145400c403031440c0710000c46545486003114082e804650340c1d0000741c41c0b20f505407040000b10713982d01c07043c102146c140300201d6100c41c5540041000d410102c00800c01030344149440403411003044e05014032600248440b800060f402d81c01440f0361801c090000786100c107540015410400048002550bc05600307088004000050619030420104a140000610780c0100720022001c040382032100c05400c101c0300400e2100342e05a100045a440d1801c4905580c0148042d2405548035018 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 428208803 1250 428207553 428207587
    0xc1305060c0a02280b070c0302010810150e01080108071a0c150c0408060c0f0904090201020c0a060804060b0105032a070b0103060b150313030c11090c04060306090b0105 74
    0x403101c098001d44190390010f9851815480102d13010800501a04100e0310002c11100f8298000c00082c1c5810024030001c1072140c8100c0d011030b942440d100c040c0307a95109403a0403241c2c0c1a8400030389588009038074820780e604810310040b211400c2e641c030101a81e0b10130044d699440740d4441d0200708144000440310030041e0070b005095503050403003200c43d651080e030801174001c58100e40c040c1010102007424400124140308081d00803150481a504101031146800e000d841034004e8213118039aa03198181c11a4002c0c091015406001040700c9038a42da581c001406040d003c071400c942e40c910b4903500b06420f6004800f81c030b000b0303112070491030480b8605a02412000c0202035039502ca40c03005000001c0020581d4020f580038602c50380011420323280e00c1003801030002c02c010700121104020320400c10700d4450480c44065154051800300b21030309180c102410440d0040b02d5041c1c1040d08182044081000a4020001c036031b80c540e8204881c9a44d0300c120f6086840300f1102c540001c000700302c10340031010343d885 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 428210053 1250 428208803 428208817
    0x114012105160b1e09181009060b070308100602120703050d020a050714010b1e2b03020f030f0711010e031b0307090b09010b070512070b010e0c130506 66
    0x445034070b5500c00401c00e04442c8540e010360346814000401d0700a0350700c01c1d021070a01d580d615240d98241828940065511203032080c800c5850f4040d98009803a40304007a9248006091820040009644407000c40341e140e0710206040c1c0c007294100c400700310090b846100601c225070080d40541904605010540780d01d600c002d9055082180a1040a60041b410b01c000d254980450321040d135940e074213240c01c9060259503440000c40c0e0345010f03640d04198507441d5968000303014180070390f11201c1d110310000d800e03411101c005c2d001e111040348442d103000d0507070000141d0f414000e03021070f00340b12040c0b04080e959110b49450040500814456540001c200d001071080c0c1ca0014141905072107403040210307160802101d28008020000381182800341014030203500a41a844014006908001c01045400710180f062140e1140c4c00660b010070700c2002e003c202c00c4907100c4030044d43d03240000c1c2410300462030280220b854108403400070440d41c013150811120101400210311040394034141c00c0011a400c50340e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 428211303 1250 428210053 428210063
    0xc0d14010803090118031e020a060e010903060b0a030506130b0906040f03030216080c070e06010c03021c05040b071203060b250c1805100527060a0b04080a030201140121 74
    0x180800010982142040c61294809903201e00031f0b4540100144900203a00820030f000081c070b58001141d0384110b4820550390170540118418200201040b43c04401d644094098042d84050000c001503443c22200114090b18000f01c043e01c40a0007107448100980703006004001010f10840041c0c040d8018051120305441c450240352626241e8908039803011050003a42e4000c0d241c21300c440509c2c00a0130350440428601810500425a4040d661710140d00f5414045580c001c501801c0c607100b00225000b0308800790125488280c4c41c0b800c3e0305154020012440400c1c204400412035602110076650041080c044000d00324148007100c40044a40000994180341e0b4a400030800841e440c0415103015003129001074607180c9013060300e40003078058001a204200c03540d4841003a11000240b99418040c4070741d600911b4507204000307000e6403c613078070181000a0104000517000d9011481c401c189000350000e00280c02001011483c0f0a424084c200201c2c00f50103c0b42803a0700d1020301400d20500c20 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 428212553 1250 428211303 428211347
    0x60203040e130804182c0d0c05070b07030c142404330b03031908090a02180a0b0d021e010507060f0516021b040b030c090c0d140108030901 61
    0x40c902c03014004064074a03035141c1070301e40c411803524117851440c180d61500100d071320203181c114107401b80e03881380005001c10301000801d490700418403205010703103801001e03d42029036640c0b00c00c6c81d0281034060004000c0d2040c0d001c442250071810170120f0b219000d0804941d12000c1404407155404800b04090000c0d83d602d4042c03840c014502d8004901c1d100c8200240c040c1403080300c281540c3c003080c3d0b00b044440c140079406c1406010340721505554581d02030103081c00d001800703640e0340d41c60a00e07080c56010065803240c00b00301050083e21341e0140c2e0f14064412400c0500c48104c80c4803d00144046954000b5080307400111400014407400c80300400100c07051503c00e02c0c01c0c0d4640c0707490b029203040010b162001a9503201b0300290b90078820040c4907079039150001d001d030071032940d10190354075510001050003151078190803001c9035802d110602075080c00a044c46a10f0401e194440619001240c494000310324085001503e001800341c410b04031200c11300154034028404004540c00502101c08008000709 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 428213803 1250 428212553 428212559
    0xd0602070b01060306050a080106051f0c2108010803070f1115070516080a03020709090305040306022d0405030606040908250302062409060102100c0e0a060203040e130804 75
    0x1400c1d986000b80305540d40400c0d02e40c200010024031081c15404102c441e85814810803460b22040d207001041c1120b0003140401a8094100b034441c00c00b040c00c01400712000c083c1a5181174582d80c842040e8a074555107400c003c0c1e8a40d4001c41e0350b0f100f030400140c910702507442c01ca400200000c0c82d0007203605024220007980540c112000c5000e4100141c21252a00320701d1042ca109900003030500003c161400080102e10100d44010b500e840d00d03070141d400c0031a00c40102d24241801041245c004542c068401c554070b159000c0031640c0741c01000f414036121124200ca59808040380010383e8140c0718000d003c1c2c40380747c0701c0404000091800640c1125000024090510304038003000c1e81c40c100c8001c00c286030040160303d14001382003480092682010110084281618160703100d58030340350080c190380c440d0b590b460303190040c2d2400c03981c0c03600d5142a5040500c0c0c40100e5038480d543c820461700503140c4100e91a111300080e40c032400b03240142056000e01100086200c0d41d11884614058000c02e10b03180b500f51 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 428215053 1250 428213803 428213813
    0x1051323100e0703060c08040f06020c0304180903082d09010e03040b031e160e150c0a0213020304030206130303020d05101e03020604121407080d08070305070903020d060207 76
    0xa03580b04880c1690000e01040040c08102e0080c05c01c02c1e11039107040c0201e40340581d61003541060382000980050341c0824815a1414200115000b5001c0e01400f0f240c04115204030360060a541c8108800081c43c0d0340104001d4030301010304126643c1e2003801c1403c000d1940d50107094421008100440710b6480310001c02c040c032001e00040001c1d1909071940e66580c940b00c40c60300c541d10004484040c65020740c000300201001040b8001140c1c481c9440e260500343c10038400141419415040c06a0703518000990140c0240c0005507d034605109540f007842d0891400140000c0f40012a4040c015800c00c500090512407800ca500300f44030310038140141040d022943c442d08031401201d10550640042d54107200c100688127070212450074011107c6e0f41079007103901043c681d001e144503440804d50003d0310360701040581203c0d40f884684a408541d07545a0782d2030201d90325000c00842d000400d04e081d0100d10081e21074052035203e098141c0fa002812480c2d5400d00041e004d1581c0306550480d800e10801e00050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 428216303 1250 428215053 428215061
    0xd03020c1e0a0308010e0606040311040209120105070906020a0206040509071e030606092310051c05062b0b0403030f0216020307050d030819150306020c0105132310 72
    0x30750401c01081a0801450060240881a0860b407560401c0070104101e0359100c03001c44003507980c03240c003064031020310310080360181c01101903141e480203902c0e0302606401415400548112120f40e5403244880e920b08050f6101e40c0000b038040e4001604000522281c1454400c003504000d061522100d03101d00d14610032040100020b1240010b91030348001c00850b58070a00540c058504035144203502495600d00c02c070442403003aa01d500800b1304030303420030312540100147c4644d2110345100000841c00c00950303200501d012900c0c148141190700801a1403240c04400e44d0601403079481e200e107401c00366114051640702c0140200c0800d81c3701c000000c0b42c9416030015180c070b01c01c003070161845080346204050030a555600940c1c081c9450f82c0080010a0b0f000805540010003146465240c0700d401d0440e1021300003800240481003c2d0361400030412a090f80141407555224000704816100c42c50b100036040040c180207070100b4031300c0c8951200c05007104105c1b00d12884040c211541208610340c624192 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 428217553 1250 428216303 428216353
    0x6080f06011b08090118050112110d1103040c061e05030c160b060112111204020604030204060305071415030601050903011401080d170f22150b030d0206090d03020c 72
    0x43c0d0004070f00e442541d40c1129403a164030006126001c1d01d46e00740700000b445c00b03800790543c550054031080030443d1200e40320201e6802d400520010b0000c0e40060039000c07100e6005907811076000c28040c80c0001c42901c40d5100314401c041c0109080b481102c421411a42c13a00302400c50109010204410501040c0c125154410b40744a405013003403d240000002d440e4a041c18804000c039810050310300f090961080403101d802e0100d118401300e5455500114211f40030b0f07034000035003180c64007101205210000846000f2219240c00c100c210845500c1030100c4c260350700180320802a02030000c2040f030360042c006000e11401c00340c00060b46640003007044680700420381c440032032038200c0c4100040b842ea0001c1c60007000c03004102c956400381421000c100042100400040b03600c4400e034000d0803004210086001140d40110400c2d907e001e1160701c0301c2c010901c000c00030b8801d129036580200d00078000300e0f030700f4401c0d140328014084826001c88150040e62042030410000d0144c03092840020401c40c40b1f0b9010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 428218803 1250 428217553 428217563
    0x1409061309050609040c0603090318080c130612020402450612160207031205131403071703040503030f1207170a021312120f050406080f06011b 63
    0x40e0918240000701110300c0a80b050740101080000c000101e007640540c40100c40c0d261038000789854850400f20b6044c2c2400f070000510840a20b40003401000004001700c180c030046902d01e48a40c980041750b0202d850502c83c3c0700c2101800e50042000d03151a9001d04644203d1401c1c511602040780300201d210328201c40440c0581d4203807000089001c101d5402d840210030191650342ca08915600c201c480c10000030032010925411446134944503209000346001150307c01052078240d0124440940140c11202207070200d0340f18040001a099068030f1248480ca4016001e42103260070031691140080c103c2d411015240f204100c00900c03610200010b01861000a400540b580041803804201000c040c0460040201011131345420500000e00c685c1c200c8140301d00141e8034242900e041e8803004181e4031801d00d01160030410000d03ca0408030081217911030355180070150f440e00d8020358040c0a28084c1d0740c0040c1c1800300050001c00780c882056080101410040d030054503010b0311a03050440c00c00200c0e1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 428220053 1250 428218803 428218837
    0x5060f0d0c06030c03020403020a03060903021501030c05090606033904060206010f05040c05030c09030a17030703110307051c0212180c0307030f0312090b090f0c1f140906 75
    0x18443d81442505026109403906501e814655000500030080034000035102036a5a0045010140208034001c00410f0f8040002d949681d00d040089805070f451040c42d01880c203180008100745006400c8911464251140810144041c180400002c01c03000f0441d02d40c600b00021290200b50309000751006086c1507005184542c1800301c07840c110342031544504c0c021400c101c05c00303514540044c140c03603101e0014101a505c501c11500000e02d040c0c030001c80640860828019130b02c140391300500031807294426480074444100a800d0164181c4030440300040090001e20100d81180c007585038502615080304805400c00a40d400f010b1010041903c24014000882c050410000000d01c042c0c03021400c04c0f00030f00a02440c648400d0041300d8402c13001010421400c540c0343c0c20612640c000d18055800a05c9414545060440e6994604400703411100b28807810b60202c0c182e10b080003210a11081401d203000392040061000e0350000700c103441d00484400c06014a490a884400c090913000d000c5060040d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 428221303 1250 428220053 428220059
    0x90b0310061509080a0507030305031e0a14090c03060112030302040b1602031908122505090a05090103080703030e0304090504051605010c1709040b2107050102030a0206010905060f0d0c 81
    0x80c1c8108065408050b02c4e420441170b803008074001059031412280c060501a42c0c0c1e50b00c1c0e90f2075500301084190301d10f40101c0e100b42400109102a80441221180c020304000d45440d00001990340d00c8151103500c2e419800071005000910845a00400203486424007508290700c4205188441c1c110b45c02c00c811140540c000002946003c0081031640302c4401d8040d01c02000913190030081e8441c200c1c03080e40d50740184010584080f01c184207804004001100c0030300c60404402300a05591011407602c1c8520010000441e10703180400c5118100c90340291031620f80003e170703075043e40a020b9000190b05580414000001c001c0018000c40e8030851141c8040c00980b030384002c0703001150119402c041d0400c81040c0060b800078050102040052030400a00d030b8903140315000140141070501d06c5140c1003865417803880700010513020703441311149410081d111025242c100480c2d990060069500051b132003440104100d00c001e5104c16000301019003044040340d4000041191444110b80445030714000e16020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 428222553 1250 428221303 428221307
    0x114031f0f06090608070905120d12020406020705120304120503040303020105150303030a1121100503030a0c03051e19080106030e0a0326040507080705040506060301090b03100615 79
    0x2801600514151160303107030402d0301c01003c00f10180100e80130302208202241150303015520160040a009120b18094011000c080e0b0301d6140400c007900100e0800a8040b8404d542402070b44c055038943e41c02000501e10b010108000d01c8201d1600d1403590100b00404078201c800d00e10705041c603a0149005503560740c41d600d802400c607003004000c00c81c580855041307003171141d4002c42180c2c4c1001440307d0204240140e0900315420b84503006400001c410b0410380c3c1c404250541c034042d8030401c85041d00381000f03640c440505840b881182c02100005a82c5c12003400040d01610203403494816108100004040c828010b0312541e204024411410000c1c18104c480340d5030200c40603024003a6464240807001440122603680c42c050400101400b20f08103544910042e4900481800f000b90118609542418204542c59905e07a000300070345400780003400b2541c2c0c2014080c280c00390201500141c9140c0c030741120400149100b44000d61705020701c00301e060324035146000c4c0e440540100c0f012082400821240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 428223803 1250 428222553 428222611
    0x2060f070516120210020307030b040e07030206121909030c0506071119140313030c090504080d0e0f0607121d0318060f0a090603060e150f011403 64
    0x911420008200245041c081c408201c0b12862a0b00290f18a824880c4000076802e00300070160614101d440481003003109503264201e11401c3c001503808221031250310010540ba1a1207010180d0402d2040107100702c0301907014100c40c2c0c4031a0640002d013070320100d00c2d54603060356042401070300080c0d030641e20310703044c84024851107400096609006004c4084885000d03190b0b8140c00031484034000540c20750080c00030740e00e0080940074402d4143c80e030b00e02002c1841c488400703407070005a41d9600c64100c00714100a080c845c45004070b4001d244281013900010010300648440d01c1948658000e40c00300340200401000f9460103a07126071515800d003803011101d281260f840b0500410a5640500440e03400038003c01103601c180b4800810040844401d4045030a51090008030181054002000c0d140d050b40000980150344441c0e500f800740980c1c43e40245544082a13450303c9205c0c00b00c00f40c0780054030b0900a985650035040c10003c081c000351940310056508210348820300400341e601600e14184090701 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 428225053 1250 428223803 428223811
    0x201140a0209090606090a2c01060203040f261005041202030405090619080304030f120509010203090d2f03060c0304150c050d09151512021302070503030702060f 71
    0x40850520348504001110f02801500e580d004400000e04401241c440041d4003000d02410714002c0070840880d80c1024041c0311080071074000903d10b0b0004528144044215022620a4220340d1041810904101e041050400c00700d41c000403111180040083e042c482c0410141715a00c0000709803509041098901e40c0c443d04490031904204001d00c41e50f0340e406079181e0400002c0e40e604800040070214a4100700b4107030010046440081130010070800c0910112209070720a1142e807030f0484071044c090350f00c0c0c000c5481441c0580c005110003412408d00f0290b450f60b82d40903400464682e1182501d00a58805181c081e0342842d91070b07800500d041c1410054107030081b081d080068a90b00d03007600c5080503d0711001103110240d4942d080010765502c104259041c08105403002c00111704145803100000242c92040360000e07007001d81071203c0040c08440380c422604021002d08007034086502304070800e00740d043c481e00f910f41c0c24018440801d0040004d94401c510a800034412410404140148100014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 428226303 1250 428225053 428225071
    0x2a090f010807140309030708070f06060f03080409020c07090f0209150301060c0f08120708060301050906010b1e0706060b0c06010902070807020f01210506011b110d0201120c020114 79
    0x1d110903650b00c0f4000d0841d200080d103566480380c448408180c114884c0510144c6505030100300d00b014060390307081501c2c0303592003007104100c0c0315611101c1640050681c0b0001c0c0c46444284002c0054003484c0d002048208950402d50700364a8803844604c0446c0c203110700390444654080350014940c101003945080329420440094215854010003d01000d4007000c01050140d501021204121015082c0c40e240c0315450341130030b4a440c081000401c1d12801701c499920943c20840410711002c000700346181681da05c10000f5180c01000003a644d2400b074140481e40c003011040100001207601d40c801c003070192a030b26900c83d0755103c4010031207107001410b8000e01c5a1500c1004203030000350382c1d1000c44140da5410b0362a0704810300c018005076042c189000c2e8085191381010891514018180c0c040c901c120300c01d1701c54048629080c0f01c110889200950000c0502d21102c00c1c94240d85084460003007418414505805071922104540e019600307a881c004001d80c0d1500d003080c00c031000641455034055203003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 428227553 1250 428226303 428226317
    0x60806181504030315030b131203091109071403090a0b0c040b090915041503050f0f070e09240a1a0904061a04021201031401050714032a090f01 63
    0x9501611011001030b10007000d050350782c48400d07129204001800b00950700801440014a080407840d8104440b209080303404402e82d04001c940c046c0244201c04016400c0201412030035540b03c280b0040e038502074800400c0c0403141038aa060804070130025132148030010003809400085240045c1c1102e4050521000590180002d100c105a40b4043d18010101151091300c540ca603120310100070102c40113030075040790400b640704140d03448407000303d000c40f84110201e481e0040681201c036158031007050b051116410070b1a04010008000b00c02c40d0f0860107060503588500c101400c0702508006860452140480e001c08200b0303d02124459103a15400100c3d21481016042c00060031610005000400103503540740c50030100941c06100100385440680308559800768250703803070322074402403008031001c080c010640c24580106020b054010900741e203c41c000f03903002040398222070b04010140c1d56844aa01c501c2c040e19090780f03005584081c07104003030b61f83d189908401d00c20b0040b410800d8606000c1d41c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 428228803 1250 428227553 428227573
    0x712020112020f090d03020a050c0402090a090f020c010e0d090b030705040b03100f06180b090607170702090103030815030708032502061801080f060d0609030507050106080618 77
    0x1016101c05005036801680c0307440040c0d1002e52070103002d4440340c1050300c1c9013410081503000942e40712800c4c020802c842250b0f05c96000c0006030310a0749044d9801110041d42003001d0703500340c7c100c00340c060414600541410201c041e024210340321402410066031040c0d8001240c242c1262518014008151000d89140f81647c00a001e40c0f0407403003810b510b180000002021580089580c030007810780040e00809142c0e0f00c6100406a20204c50345e464500383d2402c00013552411601151244034000d0300040c1005460b40340d078910000003400400b01c40c00d00700200001603684003081c17400385200381c0f9000640d003003064101421500d4504600c0c000c2c0d00c10013040c0314542c000815246002958034101c0004400307100d040240c0d0003c00c0d0001e40200000c10a00401e80e16100150103042c000e0b80c07150b01a55509609448140781036482c260846180e4240001148568200c0618103001c2d00b455032516244da92180c2c2125400d0b0300c402d0f5280c0007041400100303a0111902d280402d801c0004012240c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 428230053 1250 428228803 428228807
    0xf0415020f12061207091b02070807050904030507080d02030a1103042d17040e0618070f0504050d0c0e090a24090c290f1210230307120201 61
    0xb080b1020610360181850004105030380c2c00080d140414010820b03075070318603910744c6410042d0508000e5000c0b4601510390f07002860780300207201001c440c07000008100c11441e113800c0c066001c1c00588181c040100410480d00441e44082c0101154040c0f100016681e10b00300d8000c008070f400003449100120010070510000c1210380070124080d210218174001d20324180ba19407042c10307102800081421084400525a1100c850094000c071007004103503450682e00c402c01c03c21003883c2106d01000803640c05000c54204c1703200350308030800d803e40b030304000c0c2c505905c46000410380040840120f84500041c14188008280325044a4024014000522011840b03550303007a09003c040340c40804004070000020b101c0d400d283c000c40810794220840e06180d54990030700d00d040c903400c1040200140c0c980303440030001d0500c81084840a038001080c450420f010070740791700f09940c805040741d4801c6912080105208000440c01c21007032078079032003001030041d90f40145400d003035941d40140f44110314503c01c1c0003d0b0b6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 428231303 1250 428230053 428230057
    0xa200d090e042a0503010e01060e0907050d03050a0528030b150a080408090910030506010b07110103021b01020a1206090606050403080307090305060709051f090603021b060f0415020f 80
    0x3d18500040683c2c1c4807100880e0b040541580210351642c204100d000c061641036002e901039910002900c90503944600f0816500e0742203100c2c0c140c20079491031405001c03274403d9020b41084180d91904c0d51400030441a01040070040f0302101a144041c2c540758024950184200d00d0714440542c1d80841071010064050420300610010405100d510000141040101011201045d000611203846820011a0500f172513031140800c494510903003002003001d00200042c2c0c0c1290790b0020b84c070310240c0c50a034011000781d0001c41c030070aa101c1e03045003c0200f9a90a001400d414181c5642b00c0d5130307440100c0510420707203106900c0952454075105042c070129074401c0803202583d400041c801d90b641c541c1d8004607a4200f0070341c4003800a004203428030600b56400383c00b03942150822070b81200301003940f11030304203c50380b04607803400420848001081164000d4001e07082034007451441071071000882c80058104401100c2c074a01c402043c03c200400c12420001c11700d001885400c00314208614a0a1140f440c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 428232553 1250 428231303 428231333
    0xa0c021605060d02041a09031b0303250203010c1d010519031e0603080909070203090a05012003031503071d0c13080d180501020111030a020a200d090e04 67
    0x2071400207014842c9001580417500104460795031515282e0799810691100e412800c1510300c0780c041d1030740c1c070740d08081c40418070344210b2002000381d40360070b0422801040602180041d050400c0008540c3d0000d03079400e110b103048003205510340b545000000101092002c0384442c145050000c00d002012080d40d400d0310300980342019042c00185462040c3c80e001203030300702260011103241030401c00f02c00c0210400c0079041c2c0325400c0d14003a40076280c2080030f03a104d006480403c0c0e00030303502003800c1000350b2150442a6003c11800003a106c0456004480d5049d03600440344103901a010304000b544508080000200601c1d0b18031803008017002e00114034a420740c0180282e40c00040104101900490b104240e50043c00050100e0322a4440300c200a8251200d0b0520107070f5103954100000b62550060040c14100e0005c0c0841c94035540d11102c50b0700003500603003100420030644842d580e07920b03014074030781524400105006242c0e04495502c001e2010f17505803c0f20814112070014000003d060828014035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 428233803 1250 428232553 428232559
    0x1b060b010302130308040509070302090d061d01020c0c090115120e1002030702060601120b06040303140702100c1b0b040909020f0301050109021e04050312160c0e0a0c021605 76
    0x1156048004074080c1c01409601012880e0001c0c0020402400340000d100b281c000341c605401503910341d0710a404078040c002540b500f10307083c400702200284456010220f0540703c52260314880d0340301040c9a089801420b503070042907008248000c02480c20321416070051621014031030801500c502c0c0181120b0241c82030200154480701040640704080c4041080422a102c00315140d181500009680c0d81058035070b02d001c202000c81c6842040d0480c0128040032401038005441c061950390b003207804910744d01092078000401d000d0b500040c0c1e5100f400032005130301a940c0081c0642141459241503500e01c0085425441c501000c001402d48c01054604480e58800002504c04080c000710b25050591189560716519000000c0358500c200e0340038042c0700c444c00341c00112019104500e43d41920a034007603a680742d48200c1301e5400d0040100000e00e502014085a144484040d1307407112080e03483c5401011194220408010b220107940c4a101c1400c81c0510080c200c100e10305140612445540c010070340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 428235053 1250 428233803 428233811
    0x3010504020117220308010905090a030806130f06082a0108040314072a06050301080717071710053402010e0303100305010c02060c0f160f030905030d1b06 68
    0x290021400c1c002500312513010344042c40c200c0c02d441c0040c1056024094610801d14107008104100310005901c2c15165040e1640801900c45100300449242082e054030042d54840700300c030500313141e60301980b0010300404000380300c0e402100405451420091000c7c101c0e07001c4011240040da83d2040da656001b80d05401d20541e0644440b20140c090700c200040940340e50380c9550b07030710f50f404174503c0129075036044610524900b6071940c1c0b00700ca030f41c4801e10540d1000e6100b20814003900440ca042504954504801c594140e50380b02c0800c04980240080ca220641002980306250702103070207601c0e07116000e40d03e4441811891203403500e80c200181c0c614141c0c05d42e00050110018000d500102d000030031301045035241d150002d845010b103284c03804212500d508050f960680c0034000140d544c010340c80c5001c000d081411031400107005400c00304113018141d00f080c62540120380b20851004c0414002d80d100b0f0180c1e03051809051504000034020810400e00600743e040c6559101518a5810787c001c1001c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 428236303 1250 428235053 428235061
    0x370e0d150b06190f0e0d030203031536061005070303050408210109110301082a042301060906020309010503060f0603010803070b010801110f090a0b0309010905070503010504020117 79
    0x1591400b68000503c1040003a401c15440c0913088109a02210304690751100038070000b000f070090081c05020000e000d031b130050010031040f070381d00742e000300010a01070100066546201012411401c0b00b0720740d8000e09042c0c560161001d01c0e200701143e07000302e0a4820700080030140340f00815910961201504050380c0d480402d04122601d0102c0f030b0b003101c00b041c001446400315003105942001c00e101c0c0c1c20308585440c668240304040303c01560704840c428000382002d5100005500c1c000e030b0f080f4101c03007041003141c1c0c1c0c6456655228070030b95030001c50210b030f00e103404401e02c078601c0700c1c00340103070088420700c0140a07007000301d181d002044030780c00380c070a00e041a142c0e120000440d2444504a105a900c61008400403c403082e0004c003800c81240104884c0d846a66100465422030340d200784a041c0310b002c00c008520041454000414a003880540202845a901c1d8048020f9401c01c0c2c032141e00b0380e51a80d440400b070040401800c00a444101c00070000c0307040650003c1d005101785a903c0741184503040c001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 428237410 1107 428236303 428236309
    0x1006140f0102190507092c0c0f0607080d0e030909010e040b24031b03070503150a05070203070f0506070906021603030302370e0d150b 59
    0x80c002004003d540d11109050a200c10b56140c03041090010305211144103c1198220080030503c820b02d920040710f07124031540c0c0c0c01e1040c5a1044c0743c3d0b400e00c0e5507a4514250210401c1314025a5004c4a2600c0601401148050700350a440e16101c84003410010000b46040c10b01181c2c54105680c0344e021f042c010b90343c2a0380142a0710614400980b00400c81c001c01c6000c0b000850458811900901c002031804843c071403111427a1460214010190400300700c0d4001030a003c5002c2c044101c202c00d40341c1c4484e90014a00e029460700c80e8003040c00c0e680248212180079130080e0461940c042c05040280e0b940c10203944a00001d10310140001e40f80388085003500701d580c0180a61022949585c07400c034080d401200104203069140e0300b50b8622245d001e101c0700b45110100c8990050340000c20b201038481c0310628121800303403000b8255500056920325035186d0078520b02d00d00083c007110741004 = true := by decide +kernel

theorem cover : BRFrame.Cov 428057553 428237410 := by
  have h0 := BRFrame.cov_init 428057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 428057553 ≤ n) (h2 : n < 428237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
