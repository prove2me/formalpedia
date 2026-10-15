-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4273
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:05:09.539162+00:00
-- url     : https://prove2.me/submissions/3bfa24a2-513a-40e3-b32e-7c893e763a3a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 768345323 ≤ n < 768525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 768346573 1250 768345323 768345329
    0x23130b01060e090a0e1c030e0a0803040515101406070c06020a1b050a06030902040b040903051323060c0f12180301020304080906030403050c0d0e041401060f05180a 72
    0x40c450609044030400c018603c2400b5028094141c00c00d240710110080100c1e00b40ba2440e40c4050b0880421030220054029150310481003106024045a2900348034044008601c00c074030860995000380040e08488414900982e9000b0381c451080b04144103240411090000e0828014440c80c14a1f5203940c8000a00b1042d411900058006800e14806c000740210300c960350042074010380b8038490812020402d10250b500c134003410140c070f405020055407520b51040080c80d40240003072209204d01d003070281103036003d03492640c103802440c5000219480046c000b00c981e07070316600202507502e4400003040b507940c00448802e180780c0110f180c4c0d0042d80340708114041458151949007034881c041e02c07000035503081480c22124061b0340104100000610b52500b1034030301a41c110350160310390315a41801c0350203018425242e46140b04a240c000c042540080c80140002800c80701400014540c0e000d2802402082c402d80001c61b0800005900e07160241d0060404030700714821490751001c0a600103072644005d68 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 768347823 1250 768346573 768346577
    0x2040e010e041713151d010e1206010e1801090210050c160312140306090c0a1103040b0301091815200f040807120302070b03060d1401051923130b0106 66
    0x2c0d1302044941c0480b11004e00207407440c2050b500c1012800d0a0908140c06040c10324100035007108030441035a0360803006864403520004842c015a1114008040950180c43c645551810764080d162810700c14007403c25242d034060a050360320141d101003615503030007541012000c0d001d0603842c0306004040c4202c500c0254080c0c80405a04400504054004040482003048034202001003012544541c0308582d0403960028403146e0364026118100d40c200c803c0340070300c4d049010010380007030ba4a004030302440c1640c400c10410450761411403940e265020341c41000419030061010b400e14402155440b041462405188040c0c070002d0187c000f41043d402650380f50100c85001c00c0a2103050010030080000d03000c0c107a070090002c40b140c1ca000e0340e01c40562180c69002c0740d0000000d181a1a4070a003e615960700c0b2561440790b10380c1440c8103000e410100c5642c0b00702030454101030002c018030300500b02c003242030100d944101b0390340c008085150741c4000c0402401e49001000c400002d521414502e000f4201c90f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 768349073 1250 768347823 768347857
    0x804150509040e0615030a170a03020c030c071404021207030f02040906030f060e06010501050318031e070b07020706120e010902220506032413080406030605090a02040e010e0417 78
    0x1c5d02c1139080d1207110000f41806030780980e011000043d50740c00c5c0c482c481480041980c0e11050303801030890191003070003c030f81c5250001080100440c90001890030a0b10884c4440b04280d151043c180002ca004102c3e104061484510106d44210f009500c0303034140c0c10110f18094981600e400110081d00c200e0b500c111b498000700b01d2404244a864422604ac00a50f00003405c6e00c4c0d40341c100000c040b4000074101111a01c00040800400a009c000701e500501d140d00320318095051056144e01c864101180c1900c402d1208000100c04a201017901c03000c3d075101e07480340c0c1a00095400050003c0041c10100d11507990b84010704800351780e55820050f40e0f140a0340c2070800e840d5511450506954001d41554080d0344490014004804940071120540422801080c0f0326030b1940c40390316213641000c1e8050403802000901107881079058200c141031b90020354080003e902c0d00488001203202d1803080060b00f6040300d005000444030300741101c4e0090b00039002c0b150f10210100c0c000b032459200b071a01d0030310100a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 768350323 1250 768349073 768349081
    0x31501060518031207140a120503040201021c02100209011b060501032d02090402030a0b01180b0913142b20150612100c1b0804150509040e06 62
    0x10320b41c2086003a00305401400c10700f01600b64000c0b02c2d010b1400700902554140100c40103103842040542c80c1c0c1034201510019880380420082c1c0b05620a40f810303030040c003515482110103240e0900e10140001d4982c003c00f440d04902a50400a402600d1036030704111122180c5141d400302000b24200d907500400c1c002030a540355290114000700780a48410092004111043c4003400b01400240f0064040d11088010b55070782c17000a0601649001c01003540c8600000800d400311901d08060140760490340400c80034803210100003841b4021107507240100844415100080c8400d48401b40303500c91203007101c0c082c0d18190700c0603e0448140703207000d010544509209040d1544160400c4005503224003074842101940310070742e110250140c1d0082ca4800c0030010a10030707220a40f06e100c400d03003000181c03001001c0c40b0312007901070800b803c40b1354000341e1408071108000420010f40a0010303030100600f49800e141020440e52142405440e40a01209004103009511140142007030018001c010b8045890 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 768351573 1250 768350323 768350347
    0x102090d030806010201110c070f060f0507080304080f0703030f0f09020609040f02040b04090e15010b07020d080f0f07020301050117061909021002010902091f230a0e040b060102031e0304020315010605 88
    0x34040d84801c1c2004030360802c06103810340102c00c0b9210641c100800d20750c1c0b650ba42c10403031541d204045003080344c0c280004001f414540c0c5580840c01412220700180f01070071000701c14001f03403580c0600203540310000f007006003030602d404c1d8003440c0c044c2c44401c40541450764031500d19003d50440d90110303c0098907801642e1200c002031013000b00da40e10028450b411541000d05600302c900400348002e003c0ea81d2344111509000c181da0603102d4907000b4811845e900d0590700301e5002c1c1600303d444101c2c0690700742000400c03280c40c20319041c0820f02804005200d1a5140a50562503000d01841c52800d40c1d60b81c003200b00542c50381c028618290400381c0000c00c858159106222000200800d486141c1c030340006825052080c40c00c040e021a00850f0700c0346000c050414421204080024825034015540310000030403081d424a49442680941006070140d60303a0b0006a0b00e034480c0061300d610703070b500070b104004031800c0d00006140c0290000d000c907904030807501d45100e00c50300c0030b810240100300c0c041207410b4502 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 768352823 1250 768351573 768351599
    0x3060717070503070e06070609150e0f0105060303090105030a15030803010311030a020114072d0c1e090e0f060a24120201080414011a120102090d030806010201110c07 73
    0x40202d01d4868610324003550000c1c20020a0403040d80300d154000780c038200b401001c0c3c00c1080241d030800c82c0c604854484c030781108001d1125000d403418034014200200381c148018841c00f031248401501440c50502c1078801101c40d540000d1840711215a206a0600000c99188044000c1e62003a0b91190307482d4114100b0410140c03000f8003a6229512000c0e5900040c0d03030011404070018500300f41103498803290716142e00003000d65954042100162030202194140f4a035142841c280503840511105440b03003d050800342000803500045031380076104101d08005580445880017800d02a00c20601c61640040d042c004241c0b555103d094440307600100d80b03e410342d610450815494807a00f0350618001a40c540070505c1000a03040c821000001428001081d010f00c038500c07100c030001c2056070303c021020a0003008415a19000c0c0000e0130349011074036414400c595498500030021881444c09540c1111401c40081580b4115500d03401268004045040906004c00e15100686081804e040f1449000703 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 768354073 1250 768352823 768352831
    0x61908010c121b0305090c0d0c03030807050403030e06130e071806050405090a1d1005070806041e0e0c0a06030504050d170723030702030306240405061803060717 71
    0x42441c0001d08140081c240d8140da0f80280f0b10300340416195504085241094036180d41d10360005101c42a0004101040c490714042d030b13101e41c654412503150b000b001c8030140264000140492107851448851340344c210090310300f22440c078101c100e140d626503403410002142942c011011946006640b60000380388040356020701101e28005080c02e15190002c0c200f410f000d0000c150380e640d034007607130200c1c101400344240b6071445080865040f40b0850503c140180012902d190000d0b086038081030440c86c0901528042030750a00010022000b00a80c5030020410315107120a18403414040900d0b540b40c00f20310000400c42038800044610f01801e0080c24000c2000c015070030464801d500250b1005821400c81d00030045141900a1005085840748007403030402e8003c0c2c0d02c032400300411154560000055104034002d490300600000015a9040900d00301905428910301c244414003e44c281600600305417595100d40c0300b0a601000040380c1403c0054510b000090071703410140381030401c0300c00001d401c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 768355323 1250 768354073 768354107
    0x3060a0b19030209040b0a0f0608070305010518100f0f0603050109020f072301020f1c060503030d0b04060506120105030f070e040209040f0501050109021b070509040b061908010c 78
    0x140150300003900d01c415100304440340c1410340c04250344185407225804280d512002804031f0354456200c06205180c90307400d02c01c1c4400107242c02c001038040c1703110b80112412240050a42c903038000d0401c188070403c0d20000c1885007070041200740010b05c03401d8210314030010701e1700c8158901c4280c20400d005050b680c05800020800b030041001441240c1014111050301d40c20446041450015040048100030121000c90040d800030400b0201840e512000380b41c01010340c0c2c18101c840480036820f4007035844501c80c1e2681078100344010400704000341c00c01400030000400005100b80c0350400100c403a00615130907042e5606550042c040c90404200741c2500062620003800c0c22860080764140303505005200a008805040100d020003603100c00c0949010b90040c003d005640e114078440303000707401610150034805c42103880301d0b02400c8045104000d07100064070000840c0d641d51a510710421014000340c1d003088030072200386450090340700a100905280340011882e00400f0708020640b0090b1081c00c0d00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 768356573 1250 768355323 768355327
    0x30605120c18040309080109110a06020d0909050606040909060b030c010503010311010c030c05010914060a091104020705150c0702090105060c030a0c02030c100c06050901060f09090c120803060a0b 86
    0x14079584a6082e112003200020b00c1941d1079850b03103002c0700e2290b9903500c003084560a0041000821a030416001d420344400d40742480101d0340e500c3c0490fa2818400c0c00c08000c80d8000c03c00344450807a94102642c443c40150156103010360340d900000441c0c0c4040f1050361459a41d5014002c9494203200510140d4000d01e015030079035045d5150a41e00d0700c014a4014140082700c51494101030103800d88485054014000b0041051541031108040440c0d0500b0040c5001c0e400001d10089058491136040a4001038107568450802c020300000350311610007603031b080c03090000da000328032054002c40f1301c60300b00c4111583e00d034591441070108860301a080306100700d00c00e0104014200000003034481c442c0d09803601003214001d80c00440c0c00d100d5001ca416400c10030301c0b403a01c4182d64000d040440b81341c0c440e000030041644d995680600722030130350007001c1079002c08400800c000160354000409842c0a1540c030009580d88940b140140b485540d0704640084000c402c0010a00d807a0819400400380d24205038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 768357823 1250 768356573 768356593
    0x11270f1305150f10180906080a0c1703070b040c0f0b1902010b0d0602030a09020603070e01020c03030415050a090f06110c03010e030406210e0a0b1302010206070f110a0303060512 78
    0x1a41301d20600d045004001c0c441d011a2011401046070100070140903000300300c072944445980e62248030b281400e9030402640400042d00b142150018001d010295010314100b044a517140c0d8950180038105a0718109080c1c4040303440d03601d4103094001080301495543d683c4110484450803000c000c2e4210082d6458101c00502c1900e070b1824088096900020060790f0382d0390003010000520146201070740204001c010130038202d800440c500d4420009800711400c00e20b1400415a681c802c2d0f020720521806c542c5034010b042070050000d800d421905003441c3c614141c80d565030b201c1d08100b6500510001c0c600d000c01e0104604107000309494210154000e00c40b0100d03618441e6501d12486c4210410489102021541c00344c07502c121074080f4510300c03020b10000c114201c0d1981d55101e0000d09481c3e000661f008100c00f03402000f0010300459068000c0d048079a00c0240940d00e10b020844880207028030810642c0303004070280b01d00c0050602c607440004001d8144018481d4200d032103d51000e165120f40c0c040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 768359073 1250 768357823 768357829
    0x20a0f110102012904150f050918010f09020a06022b02030423040b1f080c070b0708041428050111040303080a11270f1305150f 56
    0x415a0404522005080c0800040b401410040d94907404551010820400d01074211001075610400f268207001c41c103000044ea164046241c41080549000c0800c01c21130390800300d21f140c1e4041d080042120455008140f16401d5550441010880a5031911504210715100c08480007a004c184010201521f08040802e95400442441c0d20100b500c0c003040000684200211405061010341c00705182c04886103030500a9000f50626118600340201134140e81410f451040301480406040801072418110139a00c40fa8040c103d05000d6004000b64404180f000b0303a0240601400c1c1d035091410718007030400e103203c0400345400e001c250300089644541d601c2c0c01d2a08088500084010701c611900601c0c002d80100700c04001c0b1103500c10081000001c0c941c028482611916034203c05200242e10704552841c1841668103090701c0e000001a09c84061910180b4001c1c983d00161015800c02100b00000d01407818102c480741a440d02d4408201415406020b14a803000c426250214620310401c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 768360323 1250 768359073 768359093
    0x10207051b10030b03190b06151e031b04080a0302120a090e310606050105090120010b030f0a020a090c14070c0e0c07030305071d0f0f060c0319020a 65
    0x40100f0107444854024560350240300c83d030301c1c0e2000b032940495215902d1509400b403040031035155206850401501110030001400c81d1461244081d110400c1c12000410b1405da800240c003610288100314064007a074200c07c1d0040c00a00b8001e4000d0007480d413280f800a180c503101c1a505505000d090200005441e00f001e01c01041e100920900d581560b0b40f084007400e20036102001c074041d044581c081c90b4210200c0c0656a09040c05102c00b44201500e42005650621666114a00086508128184480342240c103003c000000b400013180301c2c030110b80040c0c03a01004064410580d0004401c010441c5001e100d2403004000440b014002c2a400c0c010140552400e105452041c160001e60350080100104020000d0a468511a4a1420444420119900088004c40c0801d00e04000f04541501401c92151440ca07484804500003000a050102195013030342496049181030514122541c1d804018103044643e41c0015502c5000346000038040b00965142c5100b550082d1082001203800400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 768361573 1250 768360323 768360349
    0x1e13150e0913020d021f110105040c1503020d091101090f08070e0c0c01050c070b0c03061e13020304081201050d0b07030c0c1506060f0207270b0a08010207051b 70
    0x5440500b00341c01c0c004a2101001850020760100740d81444680354074002250210300c000a83e9071400480100390194225034040c0c0d00038001c1c1200c030b64208661000c02c860050016150318000d400c20003c0c65070002524100f40084034075480360383e030784a040e5078003010850040c804040180d168600d040d80e00382e1210564010201c00d0080d580009800740955011540f4100c004002007109207481da802c4500d54211100844040c446a0041016041b122054a00481000300f2420028080041481050104c0b0500c03942050f003801c00520068604d02c003542c400c9018400d080d5940c00a5002240303520380c1608a988038075042d0313a0040c0440d0001e11010b51240d018100010382c001111402c1d201e43c0110b10000f0286014407005020141c0642c00000454503179445040b03081651000a81c0c0b0748145000d00c400c6400c0b001590b903400403000c40c03080070302e0781c40308000110600400d003caa00061550000c0403641c1d00000c0200800c03204100c2800c80a011072142100b01c184d11002440fa508504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 768362823 1250 768361573 768361591
    0x5011e060e01050f06120c0c06240f120114010305010b0411040315020d06080d08061f03050408040510020a03020c0121050403090e07030605040506150f1e13150e09 72
    0x1004c01580d8903510b04a440214203c1e032419618035050840001e141e02c02012521079000e00d00105071444010f03990800c00c0406040c8031510040daa600340715010700a00c1c00030b0380c01040054000050142031080b810340b4403200c20051019811418201d00b901c8030030f4080d0740258030302108010f400780244144c4090b0395000d04001b002022405e0040040e0040c01c10540c03606180000000b44040c1c0004e074910a44016141d40c40c05035280801c001c0c019810300d40c3c41e10104407680f20a58040e2107540900d511500c80c4410b42d00702911400403411007180d4040c40d901503031002468400b4183c0410076a140f042d000d20b800e00d010180500f041b0004a641c11092958a4071070000c102054020203104000e08848581031036207240242009021700800e00c0307000d00071450540403842a04190f0105910304410180d1140341c4500d00b1200450755004900000d41d145164501c0c84103010702c6402041da072400703014480701d15030070b004035100348031282c50248080c002070010449003a200d07480701d150b020000d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 768364073 1250 768362823 768362839
    0x9010c0c08010c021515060f190c1a15010e0301021204030e01110105060f0f1c0818010212160f05030a03020301030303110723011d030c0d02121206010e0d05011e060e0105 75
    0x48000d51808d405143c50b46403501021503c1800a10303807104410251034010050030000301500e030300c1d421456400b41d0740105088584440b0b00200d50040b00900e400900140005203440c030f9203440000b4409060700c040b00040c1c07400410982541e0320052420403a083d050081005003000c400296401c0303802078046004603001203200d030250791110700c400c00348400d40404c014080e40628088843d07521103009200809500c0107203208551001030840e5442d071101300c60b18600242c00c2c02c0d40011080b40c040843e0b402030194035010004800380003070840c19965840140e2654150300e0b0240580b640c10000290401e0203200c4800403d40340100d0940310601107010b0342d095662408611301400803108154000c4444005c075400d07411000005010071407402c41540c000c0c0000300c6040b03844045007040411322101c18070851410028101c02160404014100202019502004203000d2890b020703065915035510890500c290148420b00c0041c1c240c1e4000030840681000030301000e00806008135401038103c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 768365323 1250 768364073 768364087
    0xa02010e040e010c0903020a080a030914061905090301050604090803060112020f28020a08030411010507020405090c03060702030a0507030e19080708010b0411030a0209010c0c08010c02151506 84
    0x1965000b000301c1000c1038000d020a100c800700c0600600b080744400c034001c2c03041d0f000004010703101098038054640e144e500c0d100d695142c01c0e00e80e10902181140300e6440241040003021485128000d0310342e4450325241c0640b83c80540302050300b1248028840b0b8040e6091100d8400000c034010308a0790300c20400d0819060705c040148405000b801507050306808000700161900030000e40549000044680e000c0143d00307582d00f1001240c5480d102040104600310600c041800204801c1c002e0684030410b03d8002e04281d101d400007825110700355104419600500c81c905501e003414042c0070342c0a00180015441c0000f807120041803485081d00107030410048140001903641c0b5011007401095044010103c01502c4925041d10380d402c51103105103e610301603c541841c206409400070f121042c40015085a8a060b01c0c40040c3d0702010f8450b0402500c4041c1c5c0001803039141c4000083c0c92000d00009500f02001d002928100c10ba0024941c0d04151404028425003024020f032102241901d20310b403201a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 768366573 1250 768365323 768365329
    0x200705010e091005120a06151512020903120c0d0207030b130c050303070605071d0a0302042304050309150c031806370c150510080a060e0c01050307020a02010e 70
    0x42e4507003040f54442011008403000d40c3d030001c0c0c901c005c0750081d041041962188800c204180c2d140d4030500c2040c18450027011005800b4050403018242e00200c050b2502007024002800d241044e0460200c1c0340001c0791400c7c0ea44400c000290019030036000801c0c1d80350440e05c40c0046503100400501e80304800745042e0042000c01003110008100203800c481c0c445e565031a11710301501c0211000b00c002026808001c40c00030a00803100d0302c03003034041c1c0b42c100c4442c150703020301c0081c0c4881e012512940a646418000325044900000d1089008001840c2c80706110307070802c141c01c030110202903c02c07041032040c054501804001c6406c0c105d00c01a2242124035118007041050143c00003241c0060004502d03031810b540c19044198190800e000450700406442c0b5082c1d5450b4035046000d0f00c0004252490803108405a003c1500700f06840941c0880035950324801e8a84103210b0000c841c2147c0390b41d9401c1540e8001c00091088140908240b070940c5050130f8025a0360013203800103810403004500c0c08a080d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 768367823 1250 768366573 768366601
    0x70e0420030c0c010509010b1008070e040c031d1c0e0603060d03020f1c090e0103050d08061f1d010c05030d051b040303020604050f070b2b0606200705010e09 69
    0x100000b4005d1020f403808183c403034002d1100300982c900408001d070400e490340e4841c20440b0b100f0380c1d040d2904064074900e082800300401c400122801070540d1035112118002031804035201e0381e2000402410030303081c0d40468240048081c0150383c2885a603075062400d41c1d07203040599500c9002914524205c4100341001ca00c1c08203214800b0700c942c040c0305021001030600c0c11808110841b55110000302c40c0e038400c90948011004d100c05412900592005403a841c0700700046500b0140048c2a0700000310031540121200c100059000c0c081005a94440308403045411240c0c444142403d00000800c129150300c0c0d101c0c420300c0503a58045903140300140884085d0201c3e62480040c010219440e5510b174078029543e00e806450545441c400e81b14840c09003031001490344184c580021180782003000c04049001b244022018007070000803154001d41c2c1900c1144140320040c040765076440403a921544012104280d151101c480f40c1d0841e080520040e60803c00c00b80b001072003551030590f280d5031040322007450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 768369073 1250 768367823 768367837
    0xd020a0e0f010e04120302070507080613050105061c080307031e0204082e0c112407030204060f05030c1201060806040c09050d0b0c1c05070e0420030c 66
    0xa045000c00e44400300480c0d140304503440300d07a846241e601c035440e03c55011802c8070010072121080300200c850b14401d40150040912810448030080e8403203404074145102158141042550a00140b06000090255941101c0c0c00c3e6201881c001070500c051b101c0202e00c0f44050303d02500003003c50150380c030030b9000007403410301e81c61400c00030344048050320040e5100d8840c40300e65201e03945019038421040400f07026690300c603400c0d10130304000002c08180074150070240700041c0031000c80101090740092040740c502c1c000000c00c40308900112140101c02d100080d00c4001010301c14002800720640004502803c59401d06115480c0d640f02c0c40743c2071707440c402e8030321002890148800000b0301580102c6a1405410120b40602c541074655901300d4290005200e03455210701e1400000001ca4076200354103400101e405d856600c1c192140d41c907581001001115400b000d80d40700f04116020b644044554900b00041758140000c180016580c0c64081180d103010031186000004140d5550048040f10b0309 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 768370323 1250 768369073 768369079
    0x10e01120503160507360e21040609150903150b030114090d03140610023301050a14130230091c030b1818101104060e0d02 54
    0x419541460f240c0c5e26960b5510407400d000a40c0140c2c465440150320440c0202e02c0081d4040c0748a038000758915001d00981c0c1e031010040d00a94a00b20744442d0311b03102d904400c45009a42c0356403107151520003071045d140c50784480c2406a58070f8811f40300c1580014500d0480c0e4115a045005408500c604002403032a4414242c1c59072a000c45240d10b80b80707101929200b9403a601c1600d240c1c02400d0001e41c1603500f00400807041551209c0018510318003604c080a4282103132041b1140f001c0c041c8459040c01c200c080c0c1d086110800c2c6449a84080f440e0003506004d06800d40f0009502850014201c1d0720311003a07200342d07228001050507010804065815030301a040e0b482107000c200500d0162101c8501c02e0010580070510003840091980c820006050301c2550003003440240707040522404500404c0444807032580a5140c00c0d0340720140d2503214000b07025008002c070b101500a800640e1038688505101d401002030705005202c140844000103560464402c0d060541a440c49070700055260545044000d40c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 768371573 1250 768370323 768370357
    0x606030604140c130903080106110307060e0a1b0f0501020a0b04030f0c15020c071d04020114070204060b040e071106060f03070906090902030d0306055a0405010e01120503 75
    0x1011100b1303030300050340f050700a465039201640c80d1042141c6002010002052507881003101b100041e040d6032040e40702cbc00c160001c0e943e20042d0760f40d803000003013440d00d06441000f2002400384204902c44040400a00c402d000a100007000390b566032107602e00c01080170f414445011031380078841d0b0082c46500c1c07082d54040030203954000302002080c0250003008611019100300d44010402c00f00401d4940520030400b88100301d0b13995568011182c031590f11686903140c1e0428003800c0010380711809440090001e101c8407588441c00c00103d80383c0b0381c40007000f40c410420008000340c1d800c0030215071079030005019504080000c40704004203182c0702c02d65108850186c640f40d4002040c4003250700c00228070740700328191051070846000c22000c2d50f80f50701031a0350140c13405450341107800d00c55180c41c0c400100d4284400b040184200f181c0b003909801166128450100d150f010705580e404c02c801b07042194112001c20540d4103144040040301e805000d0100c0813125113507503030213100f0100180c5200030000d1529403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 768372823 1250 768371573 768371599
    0xa020a0e10020706030b0f0d06110c0307030c0b22060c020c0603040b0108070b041a07020111010e010f05092107030e100c0302150106020303040318091d0c030606030604140c 76
    0xc2d40d4442a00c500c80020749058080c1b0301d10714000290700c00e00500200710700580b06958588000410454082920701c0300204540300071801f09101a20300c040c081d4803844046c000c5400d1820041d000101803002030180c1c100302d0000001500701c010640b94200c3c0700040c41c1400c8040685c900481d011000d6800311011080004011292080e103068520500031703220b2055a03810001e001d4020744c05401018001804181480480080940542401458406041000700560070300b15445041604010f0351280724000d0183c43c140a11600021640c008106081c003225000b480e00d4680254142c20b04000100d5005040c170800101c2242c4c0c000500b050300d4291020006041901200400c5025000e11481588c0d800301080722141241c03e1500914170315511035408603040510580c81d0015140300780741c0880c00391464416104c9038400340d8071040d980c0c812400038a28222984403800d200e03038003c100308001610f008c01c3c0e20fa0001e0344021840c00003850b0399080ca0605502c0340d0b503140c019803154030036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 768374073 1250 768372823 768372827
    0x33007050a02150309070e2203050306092a07020409050f060a0c02030a1b1b0602100e0303010501091a070602030f0f13021023031806090d080a020a0e10 67
    0x801c028030880e5800340010081c500c80c406408101c4101503e0740000c5020003000626816040d0320032148402102c07408401001c1600f04003401e10247c00091011040240c43c0c106100ba152b00b10b2061400c1114201e402115010a018581040402920042582421522150000390001d64050140d0f0312000111034910360750401101c10b59503650800e02c121035082d001100f00c82000e041a0388002400304000e860fa0801102c020701255040c0d5891003a00204032801c03044400307010a85e001c0e02002e030796609844203846084c01c0300c0f1425001000104160703038006016108607074a02800d19413541e04c10100f40c0507030142c28805004280000304101c0141c071240705952245181050444e03c0c0c0d01c4208a454401d40004030007500010203503c0c408086001c1d00700c034644540b00d03280006000c04100c0701190242c105407800c5018041d08642109001d0041c0400769120010000030084d00400500c010410310307001d408107540c29400180d48403941d204540190400301c1c0034100c494482c80000300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 768375323 1250 768374073 768374083
    0x30c02071502010b10140708030405100609060501020706031b03150306090c0f090c0c0b0612120c0d1b0204110706090309180204030206071e05070e0405061503300705 73
    0x40074410020460426404e1b401280d1034146140c0c00f10441b800c00e14643c1c0c03004a142d00150080c0e549108016855420070b80c940114009400b0720800443d078180340c00d001910302101d07500300c44140b500700a8081401003803c0b01103003c0307640c2440c7c0402d51035051002010010f100c0c0d04040e001d1030074030b1440c80c2030184008458003102c0d804141444019503603001682260b246000d910300180c104125480404c80303050b0070a41082005110960401d40008510b06d031982d4294842100100800d03a502105004e102c0c221420352181000b005910f03040123421007480000c01c00034411965500c000c5581c00d000b03400e4940c41540030000b040821210b04001c1c0c51560140b15581c184055540709021f17569050003a5001c803540585083d0406120b540c3e90461129090100000c20702590210000b02c0c0040110b240200400312095040f8100741c204982021801000c0300c00645070f1240b40c0c00ea5403000640041c00c880161500c1d50007010040c0c41c280810110103010180d1071022480b201030210100f1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 768376573 1250 768375323 768375341
    0xc0906040803120a0c0512180a0501050114030f0d0f02030403120305090d0e060406080406110a0804111903020904150c02010e070f0e060d030203070503160209091606030c0207150201 80
    0x3603c084141e40388000d42094030700c1d203181c12000034018481e00c00d00c21003030300c201904188100c941c010103d651012140c501410210252030682d1108010404078811f950700c0500800141c000d8400b409150203480e50741e00b0b03442c3c4103504000b052070584403424402d009840103190302c8000408040240c4000038060b0109607600c40303050141000c000078241c0540808886c032040541060309151800009079401100148150340c40e45d03c0f5219102800c03480305c001d1010034220380b10010f060516041c0b800207601c2c240c20260041280300000240403100b03c0400c01100e90444c3c2000d4542c0da03519020750a003400c24400305200381031944a50302c958064001d819400f490700e0407150400d0f40c0d210028401e9081e440340240c2501e603040800c489041c04003013813000340d0280c01245d14140031a5078a41c9503500c0a60a074580208111143c003c6180c80b04c10540c00051581c010002d8140043d080b40100300f05202c2d41051642e01c18404071070318001d000c0c0302c0042036480004907900304040d1010740030b00a40c0c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 768377823 1250 768376573 768376597
    0xc19050f0105160501022719212a0f05090604020c10060303020c120615040b0321030402040605010201050f0c0a11060c0d0b151920070306050c210c0906040803 70
    0x3504450b02c174144801c044ea52032000b500f1031420586042c1030594001c90110104c00701048414500300881c2d2501d010158041e00c6d501c0c2c0c804608105102b07180358809070b40210384011f040c0300d410400c959502d030030107401010486005039107035064124039103080c0c0d40361003240d0458282040041410340115440c1101103041e907400010740304a0460f40e441d03810458100007040307141c8400b45503505055009d0038040002074215412940f280209a00200244400340c1c040302000080008604050082c1c030024402070001b4041801d050401f110208002009030b2814200841e5446580e0b120780d40b050040321502d0705840f0f60b402e01c031010780c5881d801060044013460a0002da841e00b400d00c0000ca800b013801c40d401e15824140781c480c0d1440909046d05c1c104081040c045405d4107850441b00b50148400e600030700512440d843e40c0f80800503500c0c0103088005040083c041f86c0c0b81074200d00a803603400c0d0a00740405550390340e43c0c480c0544502562684a8201d0740115010640500000052001c04e01d0b00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 768379073 1250 768377823 768377887
    0xc120613020706150e070207081b01021e06150d20040213060206090c0a03020a060809011e0902030c01081b070606031406010e0f06010504090e0708030c0c19050f010516050102 77
    0x180280d03230f512094407c02c84c036a0f000c0d01501e490310b00030400d1885262014415140c0d0301d18070760500e4680b41c9074041c14248940100003408901100703000381e084004400c0d00d210503a00e80c26103c40000181085e044141c19104d80400c1405599a5045580d0510703d08420344b0a680c845c48004d50300e00c800c50ba900c00900c0b48002800c09803a00403ca00c0450742d0040c05034a003a42001c804039041100540348007100e43d01c81d0036201040d91000303511111760b5014040001c150005004040c40c2252144409062100c2801032100d4603160190b880b281029100049941d02c14a14040d00208042d074009840310840da80e003401110800300701c0c18120f450550442e046501c812040510146090300c0c801d011030710402040004241641150111030b00302d0080d500c0e45582c0720030b994296441a02e0600301500100000c640f140752007035a4140c4108000030740e240640c02d12011070300c01340f10b011616051050114034903600746003654401c60bc0b60342c4000203549504600614000712501d06000c0840700c3c131a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 768380323 1250 768379073 768379081
    0x180a14061207050d060212132001050d1503120306170c010203030708090a0c03060e0708030c0705121207061b08040317090307020a031a0c120613020706150e 69
    0x441410501103490810251605503d00b41c1005a05043c0440464800da0248130303d400e402d8803d04600d126601c055030a190380b2030180340c030b500c03045596178a00140321402210400c05907442015a80c8041581c10005807035411034014520300361407607000500c0742d10044401001c07a0b50603000f002c1120125044100c454002e0100592102d2910041c2030041c7e0040c000601410320418080e90840040341c16100454115102c0d20818101a0010b0707502a1301e0740445646c03101c0c01c11003c002480308002071800c105a48404c2c68544016215841c80351010001c04220040c0900c14516148401800103681741e00510382040940420031204c03e012481d072511100b014042c011541c82103070b01d03959000c1501c00940720440040c0001d0030b0014507100510103500142c486002e00d00c013550180340114001400c03041e03081804036005000003683c410038810799591015054100750050b41c215100b440f508502892500280640704010f828103081c00b0110400050081e1260305840404880d4601a51 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 768381573 1250 768380323 768380329
    0x1b011d010c090e0c07020d060212060a06110a06050a2403020406090203042a08030f0301170a050318190e0a05010b091012020d05010602071e03030e0f180a1406 70
    0x1651041021180d5590001004018400d00030301800e1b00c024410071280c0601d841e032808a81001901c1040c2180200c2441400e10740803506c50b00030026440c204a1072500d81525075100c45103c84001d040d1741e12000414980c41d8541c01c503d0700c0441d0507a1442c0c400340345046814900c0e02912007680100d203403d0020032075500c24021a403281d50000d0420380a25917210300102c6000d14410350760400d0000079400301c0e0302c690900040100d00840740800e80c5950501e2108000c085003006401c03490f43c840b804d06000100e000c4140d406c02c0100990103100e5420170307804504d4154421703081d1403c62200c5403010950400204841d80204400c01c000c00c216a21034820300d48502c0380c4000c10b980080b140c0c0d40b040e4094450081c440208611801c09402c044240f001042958401e03001040980c010500c00e010b020b5085850008004034601c25509a80c656100500050081280d140c00f915000380d505205494002a2600c10b04240856080d64036008a1000c01030440d0803e09640c1d403410300210352985 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 768382823 1250 768381573 768381587
    0x812010816050f011e0e13050103030c08031e0708070f020607090b0f04031e050d0f0f08060105120f01060e03010e030301050609180c070b060111121b011d010c 70
    0x1801c684007002402c1108004000d0a001030050401c2040010b107500d229902c07103d10b400c4a129228404451000c40421548a143c0f85c400d81b0461b1030580100040382d84001d54100864205400595940750700000c80b030340404002ca0301d49004070401c00d008419074049242c1e0b104040580e074214a09295520407619480c1c103580500006904101c1070228250080040c070565800d0b0300040c4c81c00b9566958260807021660b4503040c14201c1c64280c0c810b10000b8030242d5120340151800791380348903000c0300281c00c5640e51103120080001000004405902400840d03403034402003580e000e414502510035407030b480c1003402000c1c000762230729020003803d05050154074603081c240c01c00b0b14110380c00c000500c0700a4002c01d4001c0c2c0e01055a5107900100042e2000890043c0d43c0300648a81c2c0da802c5040c50b48100704050b10190400c884c00c1400d08013118003142840b85041084c1a581d900d82c0820940900865260032014481d483c0044900c1c541001307e4004040001040080c80105440c1d40309462030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 768384073 1250 768382823 768382843
    0x212010516030c0e2d1509101407060203150603040507031101050f120601020a08041424030a1d07090b0a08010608100c2109021f0c0605150d08120108 66
    0x40c205d510101c15480804841802c040c50300840415103107038110008409091044c55401c405000186184150411018a1f9064610360602c81808010341814865900c207005c800341140b503021001c6840c0c0b010000e04190b00b020010000c50302c9007080c5c104240c03a581c1c203120850300141c54001c180515409101a2602c2900f040ea05c0c45c2054883c8054a00804005042c581140625114000024240009040580341010b11414000e4940082c40a0528140c2c0c074039580e103a05154005100064804895000c641240041204010340e8081400310f000d10064204601514201240d45035580c1c2c44500003501c2100d026418a55400783c050885074217000b00c3c205500501020482e050850b0442c903500305141c078107501008100080131817180494030389031071855142c0e06002e0035441c0c0561702140240310311080084004a084003d0402d07510024001c11884d00c51000501c6854450075070700c80301c44041c02080d02c0183ca1300d0202c4581e13221101c01c191442d28840041202e0000044c03030f00803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 768385323 1250 768384073 768384079
    0x8071401180e09010b2b0c050901170f010902060414030c0901120519023a030f0e100203031b0d020403050d0f09050904020904061508031b01021c090212010516030c0e 73
    0x41601c90b01e031b002c0341c18194041c10b50340081a00c0d8001221f481d504a814000c02491040d034548603d903500c418103003a20480b034a4403980c1880241000359444208540440b03031003000c0e295204100c40d0220f42481110a04294441c500500000306001d03450000d030210352244040e520348100904002a6100c030200000e5041600e14204094408011403040c010b00345102c40542e0f044d00e102c001092444840354103d0014501c4c0c202040c900d0781002d4031724001c580445a400d80a840c1410082d034a00005010140c1d42003000c400c089808081012100007401d5038000b95502c980300e040081c3e85046040e050800200710582ca10045845400614242c03000140340381c1c01510717550200700503824082d106407451541c0e000490054110401301c10b0040503014080c5840340b0f81840602400407003500c1100c0a40d004002c42d0840c08030002c0c00d9a4030a40004000a0068060022070408110b050302c1074111b610345000e000081801e85d1000030309210a81d82403101141c1c0e4141280c01070012800030b50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 768386573 1250 768385323 768385369
    0x10b030d1d1e100210020a090608160f0e0d080f040f0b070503092716122313080706050a1109101220120106030608071401180e09010b 59
    0x640c3c1c50600a20003007004548112401d48042c0d180140482c4d00c034940800103d681210200400d5802003202a84400d440444414094121700301a00115182c9415070400c48c2254030010150745450800c0c1455801c50b0b0410740307841c1c0c0702c014185184e1050156480e203104025002546c94003d01c1220016035011025509101d105400d10842a642c18203d040e03205052183c0e010240c9d03042103683c070a1071144c0d201010b5440381e02c409400e41180c1c61b00782c804942407003c0320b1303484403034840302c2081600c04550b2072410307540307010454030f500710300003402001810000348140520500b50012406001b000d0000c0007602080d44100d5068401d400c142900407038031540700003505004811640e2901d49184010a600d8844041025141d0f85448250864080821000c1070407150070940c502400300350400708155420a4005a650080341c0314201d0131101984069410707911070341c04e841c00d455006441c25000e940ba0f41c02d16031600012101b0708210f40c0f90501120242c41e0801d82c038003082c0c59004041d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 768387823 1250 768386573 768386629
    0x80106030c0603021e16060c0305090a030c02030307022206050f0f04020a1404090e01141003081b060f0103060c0c08030a0e15070e010f0908071502010b030d1d 70
    0x90040d42000d14850f086610408180d171803800031800400707132940307806041440b4080718540082151151402c950400d880c2030b0030459601e0340040e01488060700b44c10000442e440610009280d80300703000001b500018111381030300d200d0b0350103484508030840c0d00c7c1c0d0078001c807601c1d1b409222522601c80c001d182c0c0101c0000b51440982403d034000c02d6000c100d0302e4510a41520441c0c40f00703482d4401d501404102d0b03640c0420300710702e040c00c0c46188034001d541c05450700e240c05c00140f0181030702c0720b6000141c6401c00001e442ca078042140580081000c485c00d058a00e9441c01e400c40842c9203000340300658038079090a4800014a00c50050312516030f0344800b540c0e00719221001c07454014807400310700200500c00c5a0110202240c5000018890f910325501c1d45140354440340010f100906280504042c410400401d0041100c0420484190ba88030190510201402c4908070b014000450840da054080c0006070301415610006414403200e891200152001c03a03070051010b80d9a000b8043c40c841c4030f4201100c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 768389073 1250 768387823 768387827
    0x5030d080c041505160b090c060c07031113061e121a0a0603050111031e01030c090504020a1e060306060509010e040c18060c050d0305040308060d060612050a0c080106030c06 76
    0x82c6035691030f80c40d19604104061100320311080b1001c2c400da50482d8414100800041d040120078000720095070302a040c1500c3c00b11b001d0b0754107814080144540d440c0e4010048940b80da550410043c00c0d4100c080c8045540e640e52441d411a000300050b200b05880c1c1c501245002100c4650031581d03074060004000000d403812510002c1d040a00a00c541c03981301c3e04004040303842409000c0032421540900c41d40ea09140016490115800c1159040030048000400100c0c5149010b1012201980000f24140d96140300088020510342c000c1d0741c0340e062001100e42c52018003c0346a00352200b5407010440c194032120261164001e1840d1213000481c60b2100e5820340c10180c01549140322103040608400403481090803201034103400c0480069141802c2509125041202c000884081d050401842c04c00d604c0c01454024014903950060b0303c07030000481005519480310008201e02d1000104d0207030300c0d01e08951100e02d03080c810b4905020148001c0b800c9101849070328100c80d40314110510a40c5001c9003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 768390323 1250 768389073 768389099
    0x10807110307110f03030d05090c10140304030507080a0c03320c011b050a02072715030c12232a0402040906090c030b0a17030f0a03020405030d080c04 66
    0x4283c00410500c4405103d41701080a021070110000c80442e0602e0690006854660309240031841801441182c130700d6039400008a006401e20009c2c0d9a98a0303907103040540743ca01c10011700901d04000001d19035105644044c1692804c0e10035584d13841c2c03901544c1021902e150207101d1220a84428000325141c415010005000c010056400800c1d95905d0550741c00034041c0101003500420000078503c10b40690501288026004a41d006544500020310303420044456501c60441903945260b00d9020b01c0241a08100940c1d0008100480c991108141d00000100714400c440e4001c1041c44a68207100402003000d403008050f00501d84980680c08011000c0011300c100f100c59441401040c6081d1500d000030f0000d80740803c4040345880c9845080e1003110103c0540004251410242911a603560600541150940840244812541d6562031700758401e40314801036860700025a03120070b5815401900440c1c1080b01551052000e40c481a10013280449840b40c2d006400c0000740002407046207 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 768391573 1250 768390323 768390353
    0x703090311010309113601060807050c0c120a050d020d0908010501081506012607091706040602090105041e03020901050306011d04060603080d0603120c020a05040e0a0f0f02010807110307 82
    0x82060684040c00104400003401e401941b0b10007005c60010721900f6040000c4a403ca202440e0161904404010842c1c5030448400294800d0800303212981451004120031054560040165680b010100e940a136950710359004850200d070255500080440c01032090f98101c6d4261030241140e100500010141e07520010080d83c11f00c400302c0f0324511041c1149003a0400242c00684920550401520161401801c0c0d8401c24801040d4141e002d80014042521900964000320140c2c0340c5c42e227000161a2400345030403c01d01400d00301400d1840e000d15031034a1003100c0c02030b2115403ea981703030030a00d900c45000b4000d40d801400c4228640c2468448000701d0740d4000d00821000460588036591019550300c5401902c020780d45420081c01440092010049410700c1810441d2220000b070f4041210801c40303120b0b00c0c1c86a0b81d60000358401960511000c00201d83c8a1244803031110070b860801440124804180d0000d03103060001866503020b408610742400c2c26a0040d8103080c40d0355602e24103090240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 768392823 1250 768391573 768391609
    0x20a02060d060e0a050f06040c0e01080a020c101b0c0201140d02040509090c040c09080705060d06050d080a1b031202030403030e01050c0405120a020105030712020f070309031101030911 81
    0x542c000b80d41c0300101c95103801402c881c0b40c04030700750406020303140711000301504aa105a04e4a04c002c69416040000130f0720048080c01d240d0300305da948800d528000d001c0d82042c1d0300a40102c030780b44504100346500c49808000e07800d035481030034012550101c0d10001c441c90001c0c086400904000381300300210001e008405e60b8070f5805854540c684010520880e004c0e254410258000183c1c0d1607103103403c0c01074070811b44061030074403e041d25046001b03603903603628816140518400510f455800d850341d041034000c0d01c009802e20035400080d00c0c0402080c0e001c00c903600300050381039504108a0145808031802150150b5a5004091081110344000d500150046091641d644600520410300380681441303003000c0310209460b40e241100340540aa0720040b800f29540283d03040c2d1300141e0300441540c0d000343d070f546004135210940710020b4000744181c4160004032200441d105040540c06401c44082e07074420b020050364603035030800540c1907079102c8070000c0962610301d04051003800c1070500d000c80c042400d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 768394073 1250 768392823 768392831
    0xa1508010e0c1606111801030b040b03032a0d020c0108220201030b03030d050f090120070b100308040b03070e01020a050703020613030615030b06191a042606090d020a02060d 76
    0x6451a0030307075540601b090010410300304405204940c4c01d441002c0c0441010748007442803080d1280082d8603803042c0c1c29020f1001c0084d00b00426050400350110b0400f000c0c3c502103800300c4002410117503840f2402a4000d0020300100c000a9000c040e104c80300d2555144410260f88074401a030064001d81400003000360540300c2030102000c074a03a0744c00782c0ca0007818800d2403003940342081112282500c1c0860301081c56645001a000301c0e90460404031116650490038202071a265450101c0c41507505900103400c00d44003080115103007800a0040d8003d1f400ca84400000640050044e61130384075200d00a402c80d0883c400400150801c0001807900c2d000421001c0c29140d00c07a0740307440c22606070b03400c2ea21004452038000d00401100004a5800502c1161040c0f01c05815015030000b031080c80c01402c02d000348450b52204800d11020544000d80700b8815200404030201e40004d825201c503541d02481c030b100390404a50984000326042e01610740650280c02408299000d01080c1e50100c2410844c00d07540d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 768395323 1250 768394073 768394091
    0x140907050f010906090509042a061b0f110a17010510050901050d0330021c2c01020906070311070506090a0902030c19020a120503010b030a09030c020a1508010e0c1606 73
    0x34011275400701c02101d42e071104105061403401851103240f008071744c81030707d4205003100c0480c014070003540005601181c80c1d880480c19a000c1242d48087e68031213802904a910601060581904500d1040e0341c0f8600c045606aa50300410080310720a219040e000790594421801007031080032a0040150350201ca045681040314076a00c0d0f401c0b810858400266010a2201e01c22002500e42104011000e405105401b0070320100c0501354440c0e01d10038038407401c030480000050030a40542c0c509000007020b0a84408035800e0180009160220050090042000115040c07034200f040d00c07501900a130181c01154100021a8002d500107417407018299403e0140700401c4141a04034004d54407164040c5c0810401440c0c26040c48117154bda0b281401410300c01402803017190025a94080c107200e5001c03a01c8002c608007030300c0c2003001c0b180107504000b54400205040301820607500304001c3c02d55998001c0c4e07a99a950300007114060703c003d003808ad810005804851541c2050043700b0380602030001d1640c034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 768396573 1250 768395323 768395363
    0x604090b0c0901110c0a05100909020f0909160210091110050c1b060d0507170a0506030f03070b0403111c02150603150f0a140907050f01090609050904 66
    0x120490700d01c03004180000344262556408101c481d08040401c00a050040e0740100144c918400d500456000f403071807110441c500d41c800d400c2c2c0380080c41c00001c2195075241e14000ca06203a4840c40d0000d0050160034042000f010141d10a220301a110740d01804404648071040c20142048500c2900c8858250101c203010307680e503901c143d1801c451500ca0950340c0c8485a503103424000d07034442c0e681d80c44c03000344030b80031640d142c8038121203915110030000943c5940b10241500d14046c800c3d02e00d070b4400009420000360410980c0550b01881046007113480c00781489000603620b124084005181c26486000b1800280c043c0d0440c83c1c11811a9054072044480da02000a8111400444070010f0b400310350143ca9241d91100c3c1d00707411510550142c42e021603a035090340005007010f0440580d4003d50000990701c00c1c090740c8120b82c00700d0400244040703070825441a5541c1c105a001c0c0c2c621840e2140c9013804c0e0340d8003807043e0b00e04485051700c64520f0300d4641420083c4518009009545d03100040b170100300380b00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 768397823 1250 768396573 768396593
    0x5090d1b080f06040b160f03091a132a030809042307090b120f190204120b060901260c0402040323072303030c060403020d0e06030402060307030203060409 68
    0x10030300c00600c60f0345084c0c1001c0c1c0c0a250060311480c49500c50101d91078001e603100180d0343c806840d600300818101c205107044880000d04c816654012030040d0180007130300c00132700030200c1543e000d010810011440f190390fa40c2c05060101c00c14401e0428943c0800005604501405107104001c20014076071120b681c0b2109240d1250400c00f9001c0121002c00c00c1c00c64014150f1005081160b200d00c1c10090071420310b401c605c5005c0e00035003d070051000000c20000ea080700c0406818012401551215519401c5c1c1f4031003800500b0031103100da182c60003d010b6040c500900d60480300d40c0700d080911604180000c41e0b654010503c500181c1c022130004540e1500c442c0020801188a043c44c808a01d0050b1159208400c00c0c0d11030080c02d401564081103010718500b03813544407000700b1403810f1410102200291440c071440c04500b12a020b10b00401040c1038003c90030020001c0d0989170039a10700301e0304003004a984012140207510a2052000c545014401e80c00346a01c502c0142000039200d62a40b6805411 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 768399073 1250 768397823 768397843
    0x201020f250515090106080607170907241b050c0118050418060c030b01050a14120f180703050607080c1209060a230f070903061e0c05090d1b08 63
    0x183c0315800510140803824030464000704402c9000d04018101200000c040c1000c0c480c54452810403440401d20400f001c0c46140300070300c04202020100d1010540040c0100801901070005ca000010721000d00c0f4400c100c1000800c1d4000042d0958000c18001901e600303800248490190300c03002400315041e215031060500b00c148a5200005051181c40c040c0107441140c1a00c07010541028107010f410b0740c2000941e80ea1101c2420405001d06c5052490b652900440c2c61805c07420802a082c0490b80100405541c0500c07210211030480c80c0d000600155220440d200040c0a980508002402e40e44170341a010b4001c94155480c620b801da90350122170081100340c6a021a41d04440c0c140f210442d014441d107280c3c01603104011880b441400b11078000158011301400200c1d4a20300020034441c131075000c44010716404001080034420b00504503d039030b5132804080c403a8519041070081003500070820348042190041a105c0e607050b042c2da8044003a00304500007052402c01003004500044240034940d40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 768400323 1250 768399073 768399103
    0x90d141b15180f0f090a0b040501120807080f0c0d020c2d06070f05030301031b060903050d030c02030c0703030509090c04120b070926010c0201020f2505 67
    0x12400a42040003008114214030026a010030841c4201c0001c0c1140040c1944000300c61030f03184030780d514000c1003220701860400e6621601080130003000c0c0266600c100c1c025001641c00b04007c0c5c0c2c80f00403101000f5001c00f40902114820b00c01c0c9000070301d501c401406810b008140144c1001da40803003651422b4181d4001034007603040741c50945220704000e50b402d981109100389500c7d08020040014500d42c401d400b00f40e00680000402d142440940f100c110a440c2d03010702141e90340d6070f40382401a4211100e110000d0317103103d05000029180e05c00c0a170101030340c1d04a0041d00d4807019500d0160024072031800c0d114254042031011341c003122410b0042000460094a0300b9a540c0400401c014203484000d003c82100c5209010520400c800018100d5610364485807501031511090000d80d590040d80c0d120680e1b00c3c5142c2c4503018524007400406603910706402c003c3c48042d4003c00141e00341e0240d03c01d01c14000c0c0b424003404103985028007104031880d08003082c0c0b1a910f280c03074031703141d091034000c1c400030070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 768401573 1250 768400323 768400363
    0x41a0a03060f080a05100501050105120a020f0c070906120209060f0a05030714030f01021303032307060e0f0c031f1d060106140f07060504020f1f020106061103090d14 73
    0x180078080c01045031402030f0500c10400c030740c18640083e26334050200005010030802d000110f510050341d0440d1103505440040320f8843d030a045900d03035034040c00e019030a1800d051050020b90a142d100c1c2d40110540c3c001d0904034156121010b02c90b412614000c0345a002d1711805000410762000e00c0048068840a50051403851b030041c14149400020414039242d0380c410041e07240348030300c642c1d0460140ca0341445c103074641070401181e0303003d260302d4645a03c144010001301042000015400301c50141c0640c4103031035000380710000303d9807207140d407c13103160301600030361440e956400040c01c1101d45c18050300c3c07002902d544010070174a07409031040b000d860140d0180c1c3c014040d00d500801c0040046c1d0b081e120380f81c50302e51030201030580f5004100c0c4c01444144c4501c0803900715620300225100b40800070f440c3d03c0d9891050184528006140500403005d9460700c100801c03041d20034000e09802d4040d82c401103241402c12414400210303c96441551380302034507042104901403e00c01440d1014132000c42c03007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 768402823 1250 768401573 768401593
    0x90a0605070e0102070e0c1e0f04093306050307021213050108061e04090f14070e1501020303010b0c1513060c0f450f0b041a0a03060f08 60
    0x2905e48000e980011008602c1070782000440c4201b04120b07400ca0a04841034080c5500002481c3c00c24050307400d021003030010202e03010802640d29403048030850101d07010890451002c0d1742085034a442810150040c20b0501024000240900001c42d0041100c2c03040300c3c50100110303850b004680201c3c010810081548008001070340c2d0001040390000002c40e0405c4070000c8070790104504420019816008684460401c018060f0400081803c541c0054071a00c041ca03144600b0790300d5031511300581000a01007400300380445420950130300c1c1c002c0180c00440c51030742046a41e00079a00041e0848026104116030390403049124a4220300400c0082c0091046114078609502961980e201d0141006070b1190416440c552258880480b030100001b2003801c480707044aa04000c01500240040c0080b11500303c403018a115211003089071203d1385441304580c2c96809a20342d910861056100c110b581040040032a20f901004103035500c41410006103e90303403603060b669907480b141d0011f02c154024071106 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 768404073 1250 768402823 768402827
    0x31a07261605030f0112050c041d0f2113030c031208160c11370509010b040e0c070b0f150d0210051b01050a0e1006050117090a0605070e01 61
    0x80320721554207040f400c61900c00d05003110107005128009070707030203a491341d2000e00500b480990304210000c4e03c24059507921841000c0410b0f1141c44050b118401c50101100c003480110700c1c1e01c22000c048030b00c807211070b2000f408510903412100003200480051440040003541d100c0280006600c1075880030840c024085024210b003a000741420001c0c40503080140c0c9555001f281d88410700d0348640d00046613400d02d0702050303080c2c3d1171b64400262007010264a05003420b02005615080030500c05190245480c1c1080c0403c0d00000c3c85040c1c058102400188804080194840d0b40306401000c003a0a0440540310044004000c2d0b42c1001121008d20031311841c0003d0121017910b400064443c0d900220345a03010030010102106c40008100000c1525140a2910b040c0f00c0030619640f00280b001e4208840742c4002000d200e01101c100c1c0c81560015a5803400c10300403101165016150010390146e00c1c0c1c3c40e4019090010600700a0b07025030b05629000034806c1c490740d80542855914012803003018400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 768405323 1250 768404073 768404101
    0x303061d010f09020c01020c06010311030c010201140a02161a01090b060a1d01030e1c2d120e100b1509090423060103080304031206031a0726 62
    0x5000c103036000401406501180311000c2d04580500c400169030700c00500400d402405040580a241d0040800010501001340b4a034110202c04030300f512025081440164200d4114a042ca200c000403440001c2140c4240d6028128000c640c000d000d01c507240c1d540d41ca81d1002100c03210380c407a1506200c018031920b90b6034454a205220251602480d080c20bd80b405000554404049080c45032030111640d0140d01c40d4000d010a0b584480440302007c074032032000f400d04140303c1c0003500002d2a688506c2c2904000a40d0001306044190a050f01400c05140889208080003402a07484c1d483e070154030110f40e020001440c44541c82d210004e0041050001c1040100c170100320107280e110103025840540e0b40d02100e46804c40d0b800900c860102d0169024840700300b8039071100758150702490740000140034800000314403031480b956444401c8401c140d030460171506680409410341d511083c810606c2c0b48441e20007500400c803800c000c5001c9040c81010074500181e1030a03000300f400c000081c00700140d1a515 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 768406573 1250 768405323 768405359
    0x405061015051c06080709090204050c03101401050f03010905040303140c04062a0b07030c0f0e040504170d02090a050f092d1015080103080d0c020c0d030306 69
    0xd014040c4642800425600902040c80c21010b455429804640816406807001784600030039661441c0d81c40c0390380c200621054400b64095810b210019030b001c059001241c0c03141c06d1003401350701c0c014105009021900624505507060040030892519160403000180d4001c0c8045d84010034185450700c0c0040640d82107000d001008042d0a013440030242c0c401094070250781c168a000c5845103910200d90070301e82c0c11500b0609407849480c01800c00d20941c105020310914058506010b0000f2440d02143c0c44e504030f508110010784546049501890290820345d08280204000004003000c4044d40c2041d500408000c8019540015101c9283c00e007074a2140081000b02c40440c101d060306030100e004c42b20020010700ea002d620702e413400705040480b0726501101024a840800a2400510a00304404070703010380d5007600340340007031120703403920450f10300d41600d83c803419140c180014800c5001c0601000c8d141041503001d860a008099110140c448070600e00179507000c110799140c16501c1e240344124032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 768407823 1250 768406573 768406589
    0xe0a060b13051501031107060c05131203050a0806010c050d0203091203031b070c0f030c03020a091a190b0309031206030d1e210605040609020a02060f060d050604050610 74
    0x2404209440301c243d40c00040101007800d0100300e203030620010300e00d83e01c201c000c001e00c1145803840414210364050098041d60384010b200d03070314040d12818451118541d100c3c000380002c0d010440321100d10310881c50030b40c0000741810600e5545512b642c1d424200000340401c000141e1020491081c18038140030b03800410010000510300e1810100c01d03009684284000700307010702000195110400010040c00c1c0010405000010080c603240e00d80001c030841c3c5840164800c50f076560000c1004e0010f0f201c0e07040c1b014a02c1a10342048815807090000c1202611403030f0111140c1003c0c00100c58020710021803140a00c5070285550741c02c58501d0000c1040040d010381d00a44c080400c0200290300300640401811400d51401651030090a04558102c4280200e2402c80c1c011060124840d205401c14404d035101200c0078001d050329130081390200e000c2e44a541005038000d0300402c054200d40b003041904072201620503124020070f9101c4c549880c20a0310100d82d10741c044c1d0200034038891310b420a98041d110700 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 768409073 1250 768407823 768407831
    0x15021b0c060a0c0b1816031104060e07030b0f031e0609160b030c250b1609140d02030312010801110403020a0b0307020709110c01050c0313030c05010e0a060b13 70
    0x1d1000109180b02054008018a900c6030114208140048501401c111284100c580c00100013004442c10185480100e42001c80500b00c0b42c4230789054010007040c0d071130040c0400210303520003408601420210400a0700300d10040c1003205591005d101794205242034030403207408802a0600d15240c03210060025460fa00b003c80000304100d03064200d90111018800d00c9a2251140b280001891295001011510900080b15a0a440400354a40c50b440c01340c0200030710b668900303c1c124519082200042e000400b01081800110803190b5130700410304020b008204104060340c0071a24661041d40d002c5071120f5172000401c4400c4090141241d0910702039481401c0c94550350100b40307000d510303003d807d00c400c81c00302c0010700a5108211840003048144010700c04a148403da40c491980b10b400d011501e0f50030800000c507941c1180080305d0180a0300c040380c40118130350313031800c81d0203800f8440103c81554880d450098454000c211404149000b02130018040700110100a24541e510381d4500b002414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 768410323 1250 768409073 768409087
    0x2060d0b15090604061d0910080609060609060d11030102040e090d1d0906040e0a120f080118050912070804140102010c02060424090501050f010f03051915021b0c06 72
    0x202004d07181110744508019204946102d030b41c0309034864407140140c201716004104110701c0070160070601101c2d58032065540940f51984016221f0750221040c1d03030415814804103070141002090503260f01c0c0145403046c070102c1344400007400c0e40d10540c0a07405658009041c05100c5a06200e1202400400c1c1000c1c0c50424440a191034442c0c403110380c1c0b9102d2509000090181d4680790008013000e0109819a0240380e01450100210301c41e004000b40040c130314401e5482e03404e00a1120700c4c16035034076081c1e0ba501c1d200000045800340c0340042c021045402905203444500f10f6031000350040d03d01c900d00032602c403400e101c5034040d880d071a501c44c030741103a05040c0c00c4400c442d00403410581084d000342440380032070002080741c17220b07008098038040b085241c404c86c80140441944058004c01d0301480250303c6076030b90600608040d040c0d0001821a4001c20100381c0183c120103c0008200d00c03d08400c0c2940350408000300072600002d10700001c480d841c102010840e4000d00c075000842e0402c68500341440070b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 768411573 1250 768410323 768410329
    0xc0403051c0207050d1109040f0b090109030e062203050132150a1503050f07090303020d0e0a09110306030709180b0c1303031d092e0302060d0b1509 65
    0xc3c0714460180140e4400306503405000200d43e045100e140f010b0310b48519414a40782c40c94030810300c0c1e00150340034814000410b2a200d010701030030341d00d42d4041c0d17200000380c60074000300441c661040d8861030741d409801d0000900700901214100043d030181e00006002c1c0750901d070789000146c049940b0386186034655017202c914001c4101c0e540d0842290b00c8803400c040380c8040825200e40d00c030b03001525101c0004600d007191a85c56003000d0321035082039104040079110240241d440140314000200941c001040300d1990f2842910440d184d01001080280040d80c1c40c1030200440390f0150345a461110004202f0a4a0408004507002401e2184040090181906075a544d421401d40d00509468038040480c90040c2000181d510b8081e01c400f030440116503d2401800702254007000c40e621040720f4040488500c0c0402c00d440c455074040c885603040b0a81490048c103000001017078402e80c9140301e5070100150310b038140541b00c58000e540000035256906010060f1800c90043e112002041c00c000101050f1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 768412823 1250 768411573 768411583
    0x204090c1a27010210050a0f0608010902090613090213050f0f1501121410060f020115210c14010207090b0a030f03170703090b0a02130b13080102030c0403051c02 71
    0x581c0341c50b2080b42c100d80040c0102d091404589a101c1114200004d10040c184180d00601a0b414041c40401056564000c2c2a0030780c0e905000203903002500c1c10014010782040350b1042c240c09045440015501080c0d0f0005000b40c07040350507400c8403650790003040f41013820804015000745400403481554a451650406258404c01840741005200c1048892041a68005a80300d000140188020740707410710a07010001c1e018807074913001441c0300d2550b11700d050047c814007200084503100e80210b00c1c204254034152031064801300d00350401110040700030500001904010300003540748100c10043c4e590009203400000d0300406540d5107450034201d0240c0d00c16508500722a40100417030ba1446032801c09840c6400045c0302d58404010400802c80d00d541d250b8042100a44a100207146c41d440d110030300c500301d018284141400a07000c00048c8003100c104800380c082c201d01e21502e01c442c141c030345610300e0aa2704241c4003001c01403008078050040202c18880103201a85066841402e1022480025664 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 768414073 1250 768412823 768412867
    0x8040b010e190f110c0a110a0f050418080a020c090705210a090807030e0a0b0f07020d06020c071e0b03190c03060b040608040b010e2e030204090c1a 65
    0xb82c0d07614000142c1000580103103c5822040c6940d03070320707a0f004411407525404105011152900540400c40fa60300c0c051410b402607541800303007401882d0800060100a012440c8440e80008000c1000c00014102d080100090038055003e007019440490038041281c2c0c015003404180b100070f1001d030b51941c84001519520a800c8000e103101c0307480e000c2c1d82500070800994081c2080302c0016032032040c19008400c0002c500d4050341e003481011354440b8010158000c0304001890700344108850702c00361a2070260100c03030501481e001031800366050b014501e401040c2c4d0007602503406c1d4043e24003442d0010040360300202200001d09296251092504030440c7c0e00c0381c0743d810183c4d910b14140b200f8511a60051010740030310101d084e502c946900d03002d0036055040380d040ba00c501c1010004202c4440e0500400c1c0100328000c440a101000c0c082580e01d045c0896500c40c2d00021020307000030269903503003c0d0801e80c900400d43d410349181003800840da48643c5106424010004201d00800c00f412144810b40b5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 768415323 1250 768414073 768414121
    0xb1c060e030a052a0d05180109030c050409020102011d0f0c031207021207120605060918071a0d060f1802070302120d09140f0c0f0d030819020a08040b010e 68
    0x100c8859503000f05882013020b00c0308100c1c414981c28901554020b030050200c00c0b65854440800c8034aa801110b100c212400024a01001076104200e50b040c50b402000c1c07524070500020a5100807640742505010800504056950001010420085040c4001c20716a0800d0340900481c04410b00f10102d0340c414510020300400180c40c1540010718140a510094000400d003181032821608101c005803d0949201c0d05c41c1c40540041405c10300048810011060503102030209140b13014810080b000054000343c5451600704203035024011503108850140030251540c142035070030040c10781151542c1910b0030032007901c1000400d011940000e1048010340b03107244c04558031941003c010f80030f002c2500d00105096a4494103490401d404225084403201c46000c86952003d0b240c200505000e0b007640c51900500d46003510380129114007136141c0d0000b49c1a11008505540c24899012a8440c0781034170300080e641c501340700410030841c0b946401401c00c01c003900403500304100125811060f41c414020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 768416573 1250 768415323 768415357
    0x4050c0a050324130503070506042120010618020a030b0117061c0f030314060402042409080d05040f05040219030f06120c0e07020609030318010b1c060e030a05 70
    0x1050510b0b9140200366172140c02c0d00e4032140c2c180f800c20b5403002c0c1540c08540340010394103101c0f032500e5240207c0c2c1e082da8180e950f80e61900100c40c06654481000054500c42d95215540851a925a041c80c59101d0000020050392401000001402c40750703c49940e074108071100302003c12403882c0e4800d4940011080f24542a0351604a451602140e1040c03401003220f207005140300705150301a07010b40c1c41c09140c1d01110950f40d54000400049109501890050040c0100c650b1000ea0038001c1c001e9020704207040c583d01342030301da02406140211246100700040d100140c1800381c0f409001040c0020b09090f60b095080c126807200c146203c480090201c010140d0780c042d40842005607401c9000242184008000507640034104003c030b46806025003000c41c0204030100e480b0038030000780395110f54080b80107541940c882800e5044411081c0b01040b40d15925000c0c1001aa80c95440f00602d6086110400017148210724018050f0344450814448603042804200720740c907002b4017203607d0a80040000702d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 768417823 1250 768416573 768416581
    0x110303092b06090602030f1510030b150304150b01390c060f08091902060a090b0301180b10141e030a05071815111504050c0a050324 58
    0x203407000c0312620181c0100d050074429814400c00d40d00441c000d1075101c0b032180107070362200740c6059800070a08200e50003d103524070008045201e5480000c2084000300003a81102d130007000d01c00c1541065400f0f44002d41000709405510100703115a100740304003030070140342c036440e0110020341b100b09440c600301c08100c03800d6072950302e403ca00008e007000c240e025110940054032040010820303054040d07075001055202000c1040c0490028200910401c400d0a078032403113944e40d00b03010702608480c070850f0500c03d81500c082139010f0340c20b02a40c06810604080400c01c0300200c4440140c66401142d18015220170405d0034902d0b030b2152a00000d46a00e1141c19641c00c003032152a00820f5130020948124079010003401940c42d00d07130700514080d04556860000c0c5020300182c00c030225065104429800b021205582405401205400d594201007000d45518810791040015a440101c5040311141c01105021540d8600b44076030300040d00d425401800e1700c0700040d0f60065650000820b140c1114501c1d4001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 768419073 1250 768417823 768417889
    0x80c0102090307090b0319120f051b0105160807020d1103090415050405010e160e010306170703141506061303021903050606060702030a0b04050118030c11030309 71
    0xc4000c4400601200d848aa4865134400104020032400348031b4014a0060f00046c03406150100d0990340000418044040300d101c10303240101140004810705c0002d02449901220243e140c46007650404008030300d0749010900c0030300d071000c80000001481404004d100090364006104504442c01e81000500c640081c1c90141c84c42c003496015075406820100341840c3c404c1c9500a00d012548103a03000d001070790300e80c06030041082040390840a808041e00c98654081d1060010001030303001030400150003a00d03010781200c804654070b0946040c2e840041c0c100304008441d6000791000883e5409040580c0c6020500c62100b400a0105889414080b0711055460900040c11009607401003881c0300300303003d0100c40104882603200c280c40b640681d000044150914804507550961700902400500d6141c0e0b480d00c500e12405030040d5125945c0e04010290241c1c400c0f0507003003160098030307500c20a0a491400010740b440b54010b4034044d4005001d000c180352980428a201c0d1101010300c90711602c0300e6110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 768420323 1250 768419073 768419077
    0xd05040312060305100501080a12030504020105090901031a070912031116120309080703030f110a0215070b01080a0f0f15060303210606140706060312030b010206010e0f04080c0102 79
    0x8076030081480c14034000704029000420040ca0000c46809110ba0780e680c1c4205a00c609a81304c0150003d49002400d030000c034400d070302c1280d0040c414100079003010160070200c1c0440e0005d03003040310b8206e801211004039503011b0713149a512031a01e2502003640c600305030b00c00b41c100e85c0354030303006040c00540304001c00110410320880c4802d02d09201b4150940d035a40021115140d40080180c01050384880702199a00c03010540105489d09a101c0301d6081c4000401240c1035150034405041c07900480303005000507590000b10b08984220107801d40c0c0c0340d811a050601d0007440c1070303028801e550700071961903000440408880e403040c1c2d0001c5030540142403508007522040000f04139200c020b441c108010007090f410020449544400e5400ca40740b4101103c910707070440d4500e0040d00040380c4061f5020052101c0b410040800510071308000c80c4844d40c903a034040d44d2050044204010a4507510345040e6541e0400070030717005000342003000c1c885041480b204140b040e4040c03c0940015000a49401c04400c2501 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 768421573 1250 768420323 768420347
    0x9080d1d1f14090a351606060b03010f0f03050c15040305121c2c030426150408181c06050405010b040c14131703030603100504080d050403 61
    0x605901c0078030b890741c1e800340c85994180040341c030000e010308040424204501485000d02840802c1040114410171500150301700310303146501c510b03424162600087d407c0c084e017002090740c0000380d500c950400c41e000c00c08042ca500722042a004c5e21a0030008a0000500c1c944161010385840030903595001900940d0301c65a00060020f12480c5000c0c41907004041c01003080220030002c1c1d2a16160380041181954800c1041411622500b00d01e0100780c3c034030441c0b29082c04408006c0303a140666809408400c689600c410054001c68a840850601c109210782228602131004c11003661406940d084054084d10442e456243c214a0307400d29540c861141c1c18003000414964510480c50742d01d000c01c00b42c10100c40c101c07420750800302441c1c031500702801070140c018884c4d2520309801c074000821003002c1d00100a00714980302d01c040b000030075400450344103400e200b001c406183d4900d401c00901d0310300750300988411001403400b4208008a540c04081c2c50385084d2184c400304064031030341822206082a05 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 768422823 1250 768421573 768421601
    0x90c0901090b04060c030e0402070b060f06040f0906051801061211090a121419020d05030906040308071403030708060f0d1202070807171e0f0109080d1d1f 68
    0x40104c2d6090304007524010b403520070740d100e00705907411105000c1a4084d50000402e4103000c080812624038001821090100000d011142413695503003020110040d50742c04181c1d1281c0d80d0005001a06014502d0300b0f0301c0c9900d140091495260210082c80c2103150006ca03600d16680e041400d8241e007226045403013200005041d402c920362214480303920200788802c204c40b0f1540e652241c410050021400c000d401001000125211500e6000e04c041c02d214010b048890703001c1003005000ca0b5461602800246018510241d120000c0b4501030100b040c132220007000c00e90090080040580d801aa02a030045c02038171074504900001d0046000305200320001807408501c07080a1343c00c10ba0000c0d003502100d99410480700c10b00e0b6205041d880540c030320b5811075010303044030300e030300e960051304207030f1046504054000c42e000440c440b4140c908480758107004480303090000640b00710303441c11030007229104c40007001c3d03501e2038503a4610040c2e500e002c90261082079010060a0007004000b550104941000c84 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 768424073 1250 768422823 768422827
    0x302100e1c0e09011401110c01140703030612050a030f030501140d140a110f0103020306091611030408010903030c0305060307030b0c09150306090708100302040506150c0f0106080c090c0901090b 85
    0x51845c041c2411940e40c400c074001184a402008146800580001041c0060710781460ba400c1e400c1140c5004e5000380025014140c541c0d40009281130408200c50189001e58050090200e452500034507144000c0358101c00c00d8100001407107102110304c00c441410301c0c01c40c1c40c910120500c0c5002e85405049651440c2280182140e00003400180c2c01c00c0591480304680c003000355901c1000640880c0000c0c0e5520303810800d100c002032190801d4007520030383c0d420141044012940050a024075580c0140c00c226900e944600e076020405405002c0e15040101501f001d02151616102181d6594450300c000707003440c104440810910040c02049441050700908030a402c0344158001400c0e943c4280c1e09503004018040c001040588280c1100b8024407214466054282c40e41d020000070300406451540d0054102041002824416004200740445480030701071000884000b20308407078456009003156000200541020b0b9282c000d0b00d03a0102c1d14030366550321942c41d240100e4015225821401c0f1740500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 768425323 1250 768424073 768424079
    0x50408060c090a230102010b0d03121a0d1a1302062d0c07031109040c18060e070305060906191a040506070507080136050a0501180302100e1c0e0901 65
    0x84c0098007080389001c0c1c00902100b01c014040c400c41109a420250020361070046070f0171500e24036080850710309141d1104088818000c00003480d13010081104460042024070300c3d8958041040880394482c104400d01052101503402103400c2c2d215840c0441302e910300845810802d580b02c2040240740c0418080ca068640001d0000300755612990300069078100b81a08080740d840c94030480e00ba104560007105920b8841c40c000100000d03403180703100010701e03949507080841c0c442c01d22001c00d8820781d01990007054504001d4107101003801e01a1100740607850030040c2e0b00c01c0e0040700800c1011030f100c1840502c100452582c10804501441c2c00042e840ba0b03001070324905000000035507030705480520000f0001c4a602c48104000038111100c1d1002c91034458084141c3d08419054101807a4040c005031402044107580341821507441070306085c911801403500e07d05260b070400c06080f00c00c045181c100100c0d002455240c5c0d4030b00b010b600c01c1072030a81c00f22250905501c26098540982e0024008140d2961 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 768426573 1250 768425323 768425369
    0x3080403020f0f0705090a02040b0712020109050d0e0f01080609071d030706180608130b04060209150d0606021911030a061505011409130507030e07080319050408060c090a 75
    0x103080c402c0a1246e4218008914804d1440c42202d048400305282d091503c200c0d581c401d00000f00441d6061309655803440d1200105006100d550240240d82c1e07142da4402c844001000804030300c9640141c10011103000f0400591500c5039206d80182140c2014450010410b07000030480c80c42c1c03031509414cc0510756000407015005584030708820800c0e0252404541c0342c07101152041c0d0111703601c13242c00a10702c003501c0104402d401c0583d080f50158801600d0650114040341d481c40c0070340c11102440030002030b80d0b0042d980d203105001c09070100e440079041d94110f003903404403890089d0030013400c0f00f0502d4030b1041035a541003002405031a03010750140881041c5402540f1401850f100b0103021604121420001071107001c201c0d40e0a840051a80c60f07229000e80700100201001042a002d240ea00c0e200180840b03401c21415000b0405da800840e90f54501c50b5401494540003042241407081c103000a206a513000302e8407580c082d500017019a103c1c0021400034a201102d58440c01d41402c0180513500134038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 768427823 1250 768426573 768426583
    0x21e0306210604050601172509090f060c020706120f270309140904060f180b0103170910030f2c0d08011d0606040b130e0604050c0703080403020f0f 65
    0xfa000d20180e440781da9031070b9800320601071058540c011a4005040d044400040c4100e1200b200d5040c0c034400c0c48944d2103074a45070864140d1101900c0750020080c119041280b68000c1c1c2e50f07000c83e5440901707400c07880d0403006001e44d20701c11005074407952558200401c1104a6001001c1071024074108079005508101c02d010690301030406030001039120101080d00c40b00d10140070410600904500070300d58132621003000800054503440d10036500c1e0703480307a120444481241415a070041208080302d514624042c1a00c0409082800b403c40781880307030b200103548070704400c61070080a040c0415810b0b444013040005203d8a10010407040034814089141c4012421980c0314121442c2120011041a04251040340d42407040d07400720b4040070008020004140c0059810031002340090381881d8842c41c1141d1160000e0041e6100021941d00401181c0443c100c0c66810800030b89040200d818200130040b981d1051880140520690401150801d4400c00040116884686c10382c0d15000069400d41c2e252 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 768429073 1250 768427823 768427831
    0xd0804121202070e0a0b0a030b0a020d0f06050a03080c100203040803040201020c19051017070503090d0c030f2609010501080111190804081219060603021e03062106 72
    0x545040d8010791900c40c000180c0e03100381c030164a188450f035603071000514090071070107802a0700070391045400000650403c0034a405900000005611254a2102003040b10181c55200c0415400c0810030403070782e01d510104c0340a69801007a1141d0324085425118034201ea003070030340304004c0c6c40042004240701444000c1d42c05203100340c1c00d444103280c81500b00007a8540d650345007a010107003c0710405c19450310088103141104a07041510403100da110b9040d11446044840c140803c900208101618034107000d411980c076032905015030407c0d50340c1c5000340500c411a071321100b40110300c01d800b191584100d0396414030b00700c0c00d01d8100d0030b40382800c038045c0601000c0c41480c4183d07003018800c1503115401c030259540c010418120209805100c2030131100000f002e401070b40e83d00c0d0b04100209035080803400152081c11402e010120704501e0b28031440440d01325a11070400c1500c144000c1d400c1440420103038040842c040c54141d12501ca0310001140060101307500e21050000c0054407040350f02c08280c00c0e00c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 768430323 1250 768429073 768429083
    0x3140312091b04050609280207060207111005040605030601030222091a090c0313020303030f09060106030507120507090803040f1e0501121a040905101b0c020f0d080412 74
    0x2030684510a0000396013060707940750740c0300c4078040005001003070308420304071a00441c034590a02c1c0003800048a0407607210503030a90395150002415001d008042103800c210420550f101c100c4c1444051000305540203500602c020003100001283d441c1e0b1103a01038400d071941c00c175400641001802030280401405100c1d000e00242481400000d00054015002c600d8001034200b00c656030790a11601c1013940020700c2103d80000103d1020050713181000518851703001c409442c5140c1c00c100100c913241c407005030b201c141094101000c0121880d484008a5402c0c00c0e40d09000c1110f031100d0340c0c20340b6416000c4c0c010008a00c400314002902c070429001480c225070540c4c5001e0140c04021943c13401c2c00140d40140360210780c1c0b4228a1a155402d07502005201c15100d030300300f014004010015041d6284a1800c2c0c8440c0c0c490410503807a50751610030880c001002440064482072403803030107020302104c41d401034442e52101030598141e44074100e504001562280c105d40c1d48640b01e86400007680a004001c0d12 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 768431573 1250 768430323 768430363
    0x1240306050a12020d0b090a0c0503010b01090909030905130b010306121a0a0e1c0e040507020619060b03090d1209050628050c0c0f06010b040314031209 67
    0x15140a03225039000d448000c1c114900d2282480fa00400c000c140c07003c201d800c0010300c00d03403101060540255a00840c1c03440c02820302d210701803d24400318102038000c0340c40b903458065010300d503a800031100001c03a09140c2022031008842d06040c0c0380c11940e0741c085500044802101024000c180e400100400001d072010080d4649403e5000300f04a49054014000780c030481c1c000303032030213000c6030741c650b00254030301020132041400c1003414100030b07a60303501c1038070003051014401888d500221410400581a58100040d1515a2009640d0070000d00603412450f01e8410104008800380c100f680076042c0d1034680303962401e000503002d664010844041000601e40140a80701c0a010300541ca0b1541e0000000c00c031640740d4001032103d0540c500b46280400100c0703000d0014401c414041c09104801000140d81c5400408003114281944000c006040c0d401c008014030500b00c162041d03a0179241c200307407081810200141d0051440c4180703843d51542c41212020003281c80000115040040411110750f1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 768432823 1250 768431573 768431639
    0x60f01090e06100303051b07120314030f06040218030109050a12091a130e040c0e06032406041d0a0201021005070806040b04110403030306081501050607060207061401 73
    0x10707241c42e02961074881e01c4102d84020000f02c0d204601078178180034824a1050040b17101e542003480d19483d03501c00c40e1745101c1c9034103540c1455085200007506241c1f040b40ca0b480c6241503800c03628082c000510b07583c03040e54040b5150540301041c0110400f2610041d0003004941c0f0a400c140b1ba4480703154400f1206981c417101a4040d40c1e01c20007000d0120f078441c0b0026501c500d1a40301040041e04204074014400041000c0003945000030b10036913008601402e05200514101102425041c0004083e14065030101805981d05281c2d8030410b07410751603030302c0150300711b8481c01e0016010f00400e403120400e0303c1e03405000d20410341011500940790b030320036022610081c5545515000340d0b41c0c11111003011030100e0300021110308064000c81c001030401440090940b00c0308145c0c40080e0400d800070340000390303114018441e11604000005c58000c505c00f141000d507140c42c00141c0c15101c0c080c0010704150300461140c04024184d000400d6486003c0c4d240091981c4818000c2d001c110b200d1007030102904007900d41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 768434073 1250 768432823 768432851
    0x100e06010918050a0b060f151b1b040203060a0b030c120f070c0f03110708070f050409050a150e0a03080f06040b130903020708190201090605090a0e0c0c060f0109 71
    0x422100f0380c0100506003134110354907400d0382054005c003201e400840c10203e00e00140e076000d01fa130360350f01000c504443c1c594000c00b0104042d98070f10500c42501d03038807100e06502e00e0818003122507800700f030844016075a6921a00850100c1030141d1040701010008010700c403180c034021024151a00b100c481030601c40d81d0350010351030302141c2601d800d0045641e680000f400706007029251281140281810349582d0307003103040c0500d0010554130180c180d401c540303010b2025001d8100c03080003d2108880500c00b001a40c0c44050310b4259007440100340c40304038090300d14210501d0304130407010030450090f60020b070b98a003005000c0740c000b1034500b8103040128002070740b540703072034810460442c0001c0c040303900580c024085a07000709500c4106405620800d0310005014000700301c45c01d0450070941d40700d10140c540f80b001510400554115074144941485210312546404404508444808a0750711140c1c6030506251103a10500d2003102c401e0040c40100081481001c945034125000b0b00d00c02c008a00b036260704 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 768435323 1250 768434073 768434111
    0x2060c1f02131203030207150e071706011203020703050607080f0a05041502090f041109100203030f1b12070c020901120f06020918040501061e05010f11100e060109 72
    0x1c0b8501c640c4a5020a000c40b00b032541034982054440d0400505e00055510f900c07221b04000c040580000b5140d002000c423610050207280000c042e600c898510005c0d0703049070981c40340014040c4009400400402805061080041d00700454010f8103440d84d5081c81c4000404e00d40c411101e801e04850f0500100c4c006c1c44041c810540301ea0b410032064105d0b08589110303c00691300000d03100390311110881c070503525035485201d080845c199242006a03107010700d4013400204c0001d0b841902c00d40d0001c0c401c00050380201150b80c2d600c864086040d417213003014058540c1881c01524503802c66100a4420403200700c0e0800000d40c11503000321069080b40e039a490404540019840d8010010340380800b89200260766600508003c600c000c1502294072009a4407038007420040701d040d01d05070f448000800c043e81c84807618402444050080e4441181804006020744c400e480817035040216402d014811800103010210505c2043c0d241070101801c425141e0359290000e010701144a403038129030072540348800c41 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 768436573 1250 768435323 768435337
    0x403030524030a12050f0a0503090613030918060b04080a1401020f0904021305090f040b0f0114010804150510050307090603031709030408010f0e0c030723040902060c1f02 75
    0x2010343d180726985582c0300b603100385a010f050110034442c0803008902c2c07102038007410a0a540700b0b51285003061000d8a48030703002e007484002070690302002d80800d0748030000c1c5080d10940c017400c441170300b540006200107240a0b8409600c12202003000f02d210f18010400700b2400d8000d014640071855070080003403c030b10844003c1112034038204603949550a05802602101e00006d002d40010390b501c074081800900101d075070002600c6290201302c108419010402c0d0000c120f030740d80a64a6041c1030b10301e608240000040c80c1849540c0e0001030810801c0702c0100b04900c2800c8051016046c00b8483d10740701d191a020303c61280c0502e410110b205600d0303208241c200d075015980c907110000e807889500e4200303030040e0401101d40420070001c13610079424001c2845191a11000181060500302c04504060341200207c3c0310f03030001a820400d0440f84411a81840b82012551b00440500e03000500104040d04000350410000b0500030550003000c5100f0240860f94080c0030f242290b0003542c0310032032180701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 768437823 1250 768436573 768436579
    0x3190e032b020f010c0305010303080c070804260d120609052202132306040e0a1202010b0d060f0e030a021908071a010305010615020c0d030203120403030524 69
    0x40c480d1041081c91030030201040082c010340307103107002c040642803d64403648080307800701c2e880e440100105a0322510031944040c00403485800c240c0c983c0c0d16508107220b070303108101051440c058440700c4541d40903202042101000121410020541006000c0e17040c2ea00400000a00c0c4c0503000500d004a4001c1c07030b1251040704004242c074220f092a04071013401d0480c0980c1c100312501410110303100c01d441000e1f02106030700d9500320b841403048426215180c004250601850a0158100c042c1c07400081036021244d105041501070740e21104201e0040544000ea1580040280301e02c1090044940c000080001000030601074030003221140b6580c0c0c41052220390069101c000048108000c00920b45880ca02c10081146045d8864454000a42e0848003201490251500400411000b403143c070b002411150b0484c5d00c02061400007a440d004011001ea0140380d900103031404052003030041304d1580d101c0b203500f01c196003041d08000303000b070100b00d400072520026003a1652041c402052034002d860001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 768439073 1250 768437823 768437863
    0x403200601030f031808030301050f01030b030c010809012c0d020105010f06050c0c0a030302010b09150a050405060a050316080f07030c09020a030f0e030d11030103020609011b020303190e03 83
    0x503580300d0800d241c82031800d4041003c0c2082003d00b85c55144580e400612002c0010764495040c54100400583c1d52400305061500d8802a8444c43d00c021851410200090a102109a035003d014074050140903a540300b070705030741c00c080501d142640d08842000c03500e12021104c081d4440581642240d00038041c030384001083c0301d01040142d10517070003410050280b20aa40021021300080313005507111360011000750f5100c081c3e0180c182048400d050784800c00c1800d501803114104089070000d8543c2c0601c07405203450b1400a4842c2c1c441d01d800340001e060180c2100d0840002c58000035042d55030f802802d00034020b070382c2100320300c50f0b0001c0d01710140c2c3e0f000303203983c402c107450140701c0381c02035008030200c03003c0c96203440c2c9104000280d4410302c9040240701c00a140d960410004940c202c0781202080304046130f05000500150f2111b8041c0d8889220a080031880701071a8102420550f03400c00c4000e41c58070001038000c0e00c164552603d100b14141c9519900ca6001c001c404240c0c4408108400c90019695 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 768440323 1250 768439073 768439079
    0x70c1e03081b060f0403021606090605220303030509061308031918080a02070b190305100f1202040522030e061b060f07020a08030109200c060403200601 67
    0x41e035000740480e90303051046000c0900a09151420814100c07502250507105200700320516406100c152060100c0c2030440f00c41d00d0030580c018107407000300c1c000c0382d0400c0340c041550f0b0120040364400a02d4401500c1412505583e0380c500140030700320450301c03902e481c0544d03404501070007100c903c03807841070790302c1504242940d4501c041c1400e01c003f05c228403d0200d40703403400800d02143c0144c040f40024080c0015a40d03501c070f404c60191a1982035807007265080c80411061844120040702c560f0141890b15000c0340d95203848421210f01e800d190480760200309017001c00078180c8800301294280c04d1098805020968520180414540100000c039182ca1a003050040c0000c0c800c440e039a1080e8001041c01d0700780004801d071030145507684c501b02c031819800071062201440c025480240d0018841c80205811002e81d55640781d5804188681d8125540300c400b40f2941e400310310315025aa204050382c090326102d00201065030307010309883c180c1c04501000300f43d0700b0f910301000002205140d040c000b0030b42646 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 768441573 1250 768440323 768440333
    0x3160e0402060d060914071d030a020d05010219170a06050d1103073503040f0b13030210051c0b100e060c070806040b01050937020a0302070c1e03 64
    0x10080140b203d0307160740d445011503980958400c001e00b0664040d016100c0e440c142c500907001c602041803920240d6001490010ba46d5030003e5050304250341601c050402c6c41140c03030164003a006a10301a840d668a00707105440301540500c014400340c0b100c1c42c0700c40759a01c6074548030040b9185070040300e41244409285001040b840799954039041030107030445e00710a64404d2200b4001004800c070a80059070f4000300c1e02d40240b0008840d44c14084040914501454507021009840c498417500741d0310f100224500103101041c8002c00b00030754000c4c2485002c02d1103207030014140d5004180140000d00021002e42d86c1800c1d074814034494031000380545d401c10140d00d90560f40ba00318406280e600803c10009124503103000d0101d0070042c010f00c4001c000ca42000c0c80c0011801c541604a41d00070030001007001076014001c03500000444c18008510782e203034010001e400350b5540b0301030f500001c00c0c00024911421941980207000c2075000728110010591102049140654030703a01d000b028120141301800420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 768442823 1250 768441573 768441577
    0x6050304030e0d0605010f0311041a100908030f0d0c030519021c0207051c0302090d020f0d05060c03181b06090a0807060507020111030c120c010603060e0c03160e040206 74
    0x122004101c0401c0d001156140c0d003d40d14260440521220003020810030809d0304420502180d43c00c403014405500c0c02042a1415240800320354030a1034016125a041070055480f580a0728550069950310790044800c40c400303a1094203903010941c64021003c4845220307104607409600f01243c00c64441d600000040080d4000302e0b1441c6500317a45010b0201e0f412440e100514409100307002400d02030340fa82502540000f444220a014140100701e0800140c1d941010121584c0d03046070790300700040084002c1000b40c1f511213030050252060f2800d000c0c2d9004244040c1d80700e0618031020038140300c081c2c0c2903a40c5070201c1c0c40194900c514983c4111200b49041400380070b224a000d0304290025545901c074620b1b04d51107600c0a0017190300001c034802556804000800e59003840d000a51900d1480011036660300c86c1c40c0b2003461a50008220b1440350942900000700541d08030006000e035807003407010b0369210400c011405100748a0302c0181034078103212460000440f0002c01101c400c81e03840d50203126550b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 768444073 1250 768442823 768442847
    0x2060a0509010b0319021503010f0504050705040503010c08160215010b09060c030f071b051c06150602160f0303020316081b010506010e040501050a03060b2b060c03060605030403 78
    0x340d503d90494811645040010341194100c08450210103d40c0340103025201403010003d01e168001000184081441307040820100c8406540c0004c4581c4c601348100c40d58005e5070001903040d402e08120403e8180d21181d103d0150481084e4640900e6940c0c0045c0ea5964000b00b5400101100e940100082180b44002d489110400381805107400d440d81c0d0310034250341c0601c2c844040d040010402105000c42e156a02d0300310b106251150704501e06100000d19004040c1718040784003d200247c050800c030b0f458000402d041e00d034200076542c0580341c4202a4803160350528034a441030218500080b81007204040700b080740c1e0590040e502e00034985591030700616204100369002c00007081614411600011700f083d800841c00300004e40b03402c00e540010000c1000301c50303680c8968148001482690b480312800411641d00c10000070f611078802001c2642d20003a9040c1c00102000410f0700000102c0e01181c00d0f483c24803a103810044040181e4003501141c1c1507001d99400a881480080d0000e400b50300c2d00220 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 768445323 1250 768444073 768444091
    0x1b0705010e092707090e06072705131a060307051b24010e0a0902030c1e04090503030106110a05060408160506012d080a030503040c080303130309080d02060a05 70
    0x401da0345200500c0001000283d0080703503400948200450304051089021035070001b40a00742038244590007c144e00550b010b0071005c1381c81103204440641601880784001c000c003074030320740c403500d0101c00420090140f00281c004e81c8200c0d556001d05468010116481580943c55090902c02d9803000f4010b049000b02c207020052003009030456194004441c000c03d1f040500d81120340940c140600f83d07c00700c00240c010746249041c81c20400c0140d0740400c04902e00380c0c090303c3c100c812004030b140c007403c0d04074185c0189400c1840d2028031014004088000e6060391401c3d1a40d4007121154602c056540c000395030087c0036a00007401090002e09440010032902900305c0000c200d280d800d40700d0a003020800c1e407110070b000c40c2c50403483c0a140c0b20991403080b4001c2070207000761400e14190b40310b51601c0800c4c000070100035000000404100442c0c0e0020003804104040301d84a02c1e000a80b2420850460826004240f4a01e4005010000003c1d040074404056000d0700b4140c950f80b501a0140001400c0901 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 768446573 1250 768445323 768445351
    0x2a08070804030803040605010f08030a12020306010c080c0706080f0c0904091403220f03032a080d050a0f0228030f0c021005010b2701030f05010b1b0705010e09 70
    0x30204140f1005180503500584000649515102c5481900340c907070703480180d003034000388480c40400d90454002484488501005681c0e40d9505004880c4202c003004028201c040104000c0e01110000800300c1c2601d04070b880e00c642d292903644600004000868411304001d4040045400504040c0c001c0451a841000480fa50f0303491111101d00315005450780311402072001c4c1082070041c0d4001c0428008008054502100c10f055440084c072020415401e4000c52607191310304002c4940c1c0a01404000ea00924a181c0b20043c01940304090003054a116030323014104200401031040600c21a0001c4c818042950410b44000a00e20040101c582c1a0418555182105281c03043d040c0525060101ca5a010b05902100c8086103812900103030041600d60f00240000704500c10101d5100540b075428810740518034100c1d0004801503c217034804446540e081000005150101c1405080f020080040c004100302d16640c68a0f0f903130b9011f2282c00d0000b41e415007044c00604100203603d0b0441118000c4c41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 768447823 1250 768446573 768446579
    0x13090f02070b16020706032f04080105100603050a0c0c0b0a0f02030106020c092a03040503190305011d04080922020c28051c020c0915012a08070804 65
    0x240700d400031115500e41428844140703001c01d44c1409410003505090034100b003200d60103d554003c180010548a91b040701d41c183c010443c1c1224000c0d0740090202030b0080c04145010b12104240040a110303480c0400c0c107200124200719070078040c1001c481d2550740d810910104544800d01d248502500d402e440c6039894603401a05100c0b07000541c06070251360000c0a11061100512503181c00003014003032040e880380c00064040410010f040314002e980c0c582691240c4032424180e00707501c2039084110700c3c003a0781c80c0400a05501508068125003980000b06844e01c03051100c1028110116001800840300700420030f110716003100c4001003101c1c2e12203848284150324800740226480202c2014603640070b61010001a94014440d8008403410030129024940b55680c3c1076540c40402c504891081c030a04090f000715100304580400c45400070300003141130920b5004411409000c807011030029501c00340b12607040c0341c428141a800c1c2602c00c1000e10303d8000f44c0340c1e40307040d801c4094122002c0d04200000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 768449073 1250 768447823 768447833
    0x100206060d0602180316080c04060317031909030c1406040b06011409220506100801090c0e2701090204060806150f03041b0f14040b01021603140f0313090f0207 70
    0x4040084980c5c28074a603043c1412529498256607032159440f850074122b0500018204464081c0c410501258180d100d0703c1d040354590002c040304201c2c039100307850f110101052542c0003044900c094040c3c001002020b603541e0100d42c1f0740b02c1c03c47d80a4900c0841c007020607c01c0d441070144400d01c2c8400411507007403c02c1d16001401612040c104148042c0700c0351040c1d030980e80d1901c1031039040301c0c04a4100306076150088018119140510407460250b58900c0d14401045c01b45036201c030410300c010418070704e0b003140800d40d0b0740ca100003541c2c148140d2071141c00410141c419108983c2554066298100e82e540c400e13041202c12140c0e00101080c401c8244a181a0000d20700c02840c0110b02c03d03e4680c02d820046044030000c00d500d40d104040405030b01d10108514840011001c00540e02a100407402c2c00503000140c0c034088481b1a485518040e1403400014082060005038049948802381c800c190b450724151a82d900030301d00741c45030740880b04808004110280d40101d12414501d98094142034080d160 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 768450323 1250 768449073 768449083
    0x10806120f1b0a05030714180a02071b08121614060415060b0a050d0b0907020109060f060b401502070b04120501110a030b100206060d06021803 63
    0x72100d51a40300d551803000180c0300384100a02c00c041600e40380c50f1989000002a176441481c4120080d9500c4c008001c4c60170f45a000f4503075140f0092140d01850b509107082d20600941c4106025180742184140d4000e61200c0d44070301504440c1000c00a001e9142d4058081c26598440004a501032030b0006600e00012810055084800011405080300d49080c0c1080700c20302042ca8100c19078507280c40000c0c41020341505c140c1d12900050304d0b0445d21100f500840c0001000409007169222001c941005402941500440c580c0f41c03060100744541040000d00c08140c40ba04c4c0500680140180300e50001c5202800e001c2600c2c00e0710005481d1801c28030100740044c1200204001c45401c80c03000c050240d010505000c140350365840c40140303009480c1403c030490718061805032841e42858490300350140902500311150203042401c010b0341c0d60040e410054000c1c000d01300007600500040c406085828000714010784241c2001d00420011f07000d503a5982c00950003900e4200f04410401644070741c07a141045 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 768451573 1250 768450323 768450343
    0x12231e07050f010603260301090f330801020313060e1908030f07020f070902131a030604050105010206040302060613110d09030201050115050f090a0308070c030b0a0e0c01080612 78
    0x80d21404c50501400c02c040b0346c0e60050350150320505860f841d101c0d60040381e045580310080040d020341d02002c48130180c51000c02c400c1413200c501805d0701c80901c04965036441406042441001266500307281d40c20b0b40012508005a6128140c60304041003a030382051a003000c0c04019a104007803040d000d0782c94400d46080940d4020000300c10040700c810511410380d001560f0303000a002d9089840d00042c0c1c3d50f01507004000505030045600440303500b14a001c400503004902c1d111140b03c00007014682d00382c0045071103610580c00c01f000010030f035001042060003107815901074112640c03240248034104803000d040c081c1d0309984044119120f0b19690240c0208421042c0100d50b890301410001d0a40383c041e0072009030214003110001025800000b07d4103098407004246444030b125000040d240c101c036030310181650000082070801c2241040044040d17038418603114503a0b40b108040002143d11311100310045278001c0600c0c1e0165070040a41d6540100d004107400b581003266203040d41020b0000d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 768452823 1250 768451573 768451603
    0xb07110a03080c010b0d0b04020d44030405120711100e0a09052e080601031505070c02061c09051c090806040803160504050d12231e0705 60
    0x403907a000780f04000e01a00100b208100c8846041c400300c0c0d102d8040c0d044010304000e2040f00030041040400402e9035000c0450503401042c407241c85880400502401c0b000040142c1100300381818401c1d404880003968025500440200300344880d40d0f510002d240e100c0c100c283d811a00c00c0340c04407415036840c0855044109180d903448510300e0402c0c184120300300b10750009a600d9007003030108030711100100c8208401050041340b007040306a2456031441c2884542d0031001c000e000c0c000000c0240500880c0540408800c0e050800807070b580c9202c11259414100c9000754080c40811402580c240c80348a00010b20000d030380c001030a004241d8520345001000b45c04042d54401866081111035040100301c0c009220b1348003d0305080c03409030380b0030030184001840040100c00401c1d920030840d01c60800d44015090203060b40b000d0001c241002d21801c0451030256000a807002e41100380140200246610300c05201d40c11401e29410000000407080c0500c0100381d054014848800803500402180d8072078030020b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 768454073 1250 768452823 768452827
    0xc08010f0c030b22021b01090809030d090605070201110c0d11041a18090a0c0b070b0a2c010b150d05010b0a020d180902030a050906090c06040b07110a0308 68
    0x5440701800390b0f182140e00c68070039441d0480e03056410500e9075084200c100ca030f0400503030352100b0521528100c02200034414596103004101d04c1000141002003444950880480d19000c420180840d0450b08601075800043e2040c40380301d005500030300c00142e24141d0340d0107a440c0d441710100401e1200e1042c0c2419580072003905a4400242047d1040825500c45000d0b400d414001d01c00200e4841011103140420809200b000a0013841d400d010001b0344981c001e1044000c0340e6551101230507900280d9080c0c840107810b402050342e01d080340c80707030381008a43c0600703e000341024110815080108440c0591640d505c0384111080d540d02c14106030301e11710342c21900e541ca070b8815480040031520140c101000340b0030100b209010300f5070005141520206145001030034004500c0d00c1a401d190300780e00a2280c0c1e130010082c4001c0807841c4c0c010510078070708801246d540741e56821201da550000b49000540dc000300700802d210440b0f0980c000c1c9440e601a80c29170700300301d001001141e00140036904c00e0302c80c07040c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 768455323 1250 768454073 768454091
    0x90e1b0d0204021c15170c19080604050c0307170a0b0703020f0c010f0608010908030c03040303140705031602030316050c1603080705010c050711060d0f0c020c0f030a0b070c0c08010f 80
    0xb4010174402a12181c0c01001030a005136201d00c2e40c40f5000c2c5000b0748903d00051440f00f200c0b41501c0e0000c050000c10041d01d400b41002e00c0d18a96034010340320120701c41e01031a000030035609402d20100080413500f00003401c201d10f03552190030b5840307005441c08080540130403005d21100142c900608103007103140000103000304003020500881d44207030407c0106034108840da5012524040c1a03940003049014900c0d03507515140b4080d8020a520344100c8610030042003002203250b0098090352082c80c410010103403041208100300d071644070469000c3c04030180707030604180707a61080700a0000c1142040444031720221261103114001c000d41e00840340c0ca00005101c1081000c2230051902d000540d0901307074223003d40b0f562020540c012102c030050103070074042a88003001000d60031041100e565008204078030044010000c2d16188150036480c000d4184500314505400c000540041954001384205801d4540c4c943c1140c0016001c0d6080e44d42c0050004007084c0036800307106605d10300c0400c2c0000510088 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 768456573 1250 768455323 768455351
    0x1180e07090e0f09060601180e0a091a060618010c020a03050a03090f0602030a14131806060c08071211070f060822030302161704090e1b0d0204021c 65
    0x10080043c65658000403e00c5400e107000a001600142e007400c0c03503004c0b401120144210030000d17901800300240030764244010070760140e01020102d0b00807003040b841221141440004460141d80c17642c1c01c84410000d0744034088422040c2103140d10b0501d0101030284103500010641080d40c4c00503174641d0888600c600030583c0042104000740400741c01c80d0002c0c1d01d460b002a40324001c06001d803041c400002c0d080389440d0081800c5415100c25640c0e410340c06505c2d0291022010040305074554542d15200000c11040e0080c8846c040060340500b40c80c1c60720603586d071005841c0e6010755810742446200c241240200c1c60a204050180c8418043c0f16011407400500810140300a00161a400754503c07541d2944105182c0580e04181c244c00c1c050780c2c03014941441440c10340c0d48803001d0542e0983e00509260342009400420845608074414082c40404100c440d440d0001400458000600808604000d042c401c40e0342c4005400280014100902402c20f5003584440d54420f0303014683e12258102014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 768457823 1250 768456573 768456599
    0xb030a0e06161206080a0c0806010b04180e0f0a05030c12091e06040f230a0503060708130f0303140f07090b03060f04181707020f01180e0709 62
    0x364100140400d0070071078003906a50851401a408215a07a141c8002c140219042900100400d008541114009050005481055000e6407406004110001075a0700c00c000695050364a09075034002c0445111400314020803152140301510700800c074000380d20070800d000c003403c01801030f80036598403650401d4503801e007241c1c02940e01d100d050512a5070b10135100c40c01c0703000c03d000f0482d03c010b1026120070700140c5940115440207455960404020400c4400505081104480102401d200850f08810062100a41d000c0c0c0e40d015841807002490361481200c0c03040d000340e00d0620242c8d800c4a02d4640308641014140c4c00d402080e00d80c0c0c40c0e004e040445c42881c0d81d0040400004840f00d003132002000b0031007856807203003011141c0080040756460f80c8640302d00c18000d4004004100840c09020180200c0112140079181451040b81030043c2c080b900342152003043d4010282c050f90380c40e0b0700c01034070b1443c1031114402c1c01d201c041e100400d021107600021402100030751a0204100c0c6810260343e200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 768459073 1250 768457823 768457841
    0xd06091a0f01050a240309050d030204140d0f080d060f12020909060709120206040e011e091e0c12151505070c0506030613020a200303040b04030e06070506010b030a 72
    0x40d61360071410401005004c903104054203001d44032000c0c10390f203610100e000d0518890042e0841c00b515140d58425501503000f0320449614508a083d003052120400840d160b039014007802004c0500380000c00100c5000040600c420711540000e40700380c8410500004e11100d801640010b1908086d1905501e403404035140d10a00c0480204001d00e004d41004280c15114440e485141c641d03c00500c045680b0001076070003601c02d080311401951780d10701a002140c6138443d401c9100d44203450021514046d2400381100402d40c00390a031140c2c044031039a003402003000090392401c0003200c120b40d124921090152904001d000007034990f9890600c0f1410389062104a05030045c040100701060000360b51481e10012a0011100e840d120b944600101d00074648a0b001c0103851803000445000345070700f006102114045500051180d0012070040c180c0e00e120079540a0301c05131412001400092007044500c904200292400707081c01c0482ea145444e04000307070848042000048100704045000744149584 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 768460323 1250 768459073 768459079
    0x7030605010905070c0b090c041a0411072d06180201020105011e05040504020402070804080a12080405102004060507150b09220b01080a02040c020610050d06091a0f0105 74
    0x16401e02000103002807164150040c01c8145000000f0661f11040c001450801c00241040c4000b46003003c1da0140103503d002d26078030640ca0300c4140500b00a050040d1900b441d440705003814844505841c0000b11a04004589280324002c4180ba0009090b0f000703182d81e20001104841c40c1080758030019003941d070143c00807210b48080c0c13103050a0303a0284d040da038400c9442c10703500003c058440d03001040c040d2095400280c9038102c0040c0008620000103201c910244c0901c104c841d400c803180c21300725400070b003e48000e8165404201c071040c03e4400c070707440b1004900040c06c0c6084942010601c0c0c4900e600709a02001c0450302c0480c041c0c09009404c40000310782e403641d05080004102c10400241c950030043c00340d0b4028a8a0100c400c80180307101000b1003070300d800051035005981e582099a80c1c4d01c2080c5000ca000341d0402403a01e0441703000041c0240a0071a0120fa44243c80c14101400390300c9101f40019070b80c00d0703260813144012076224030400e907002d0001000e03105540f07070003203c000c3c41c0441a840940 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 768461573 1250 768460323 768460331
    0x1050313020405040218041202010b061201090c0903020a090606080901020a080c0310050d0f11010215010b0708400f03061d010f020306240a141b070306050109 70
    0x84140030510415405a81100c00080c0341d111800451510940c01c0400c103201904e9038203100c14003081e1101d04d0000407a950081c030100c00070b002405201d004610507074050011910050145204c503801c0288800180d207400311105642c0c2e00007030410031056100c03c000076545c0e001804101c1e4060030965102852000962812001c40002414444e00038190400301001201142c0c8a011103404030000b01402400403003501c1c2b01c0d00b4081403074000180304507004421035841c4143c5500228115180d0317125180c03c0c0009a20b0320b010702249902881c022203001004000c0d0b0045080940e1101c4002020002e144400c0341c2e20780c0740d100440070640080308807440d100204009103e0a00d400b13909880d404100401e401c80c4522400031940c00080c086c00240d428241d01000610316680074500c203110881d128902145c126240c13150708880480c8117000742c1c0040200d11061340c01080045541445031114a1600f40d444680010101004d0304601d8a0b4120100c00c100340900707400b03224091308110724200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 768462823 1250 768461573 768461581
    0x3150d0819020a14010f05070c1a0601020a050102130e0106050c030d0b010e040e0d030b0f060d020c070f030c060f080c090d02041e06231c0606150206090c010503 71
    0x41410300900414804541a8041030500d01d88240b107240c0950740e1180d14050045105208203010306007000603450054a014001207010344502e03006e84081d5001030004103400e104c0e0b500c00032020f83c0188003905500c54041c075800001c4017440101001200021000b0025040121100d803082c01a8065001c00030700344600400040d01200b1030b04641403110002840d090b400006039082c65140103040e51080c900000011840808901e42079001c00503034040100c22412010030a00130510800b064000109124010b40035805078002e05100310407034101c82142d40e5545072031006c50056002201d103900800307000c00c0380c160098088402e180540c04d2900b224a0801c42c140340d1802008039a501c42c01c2110301d14415902d03075602c03d88402c041d901c421454818580c0752140603001d0b030b1140c0c800e0b52810044902d400341021120350f0340c503540200030010001900078004100e40c82c5581c00d0302c0030b5548500016015803440114880d80880e9000350000b890106640382c2407207442400c290502004000300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 768464073 1250 768462823 768462833
    0x510030c02031204051e010f0f022502060f07050d02120412032102030109020a020712030516081201091a090405030406030e010b0a0f08070b09090a0e0f100203150d 72
    0xf4030a03030b0200000411195450b82041c41c540280381d14807602c2110b0300040340c0012038040d008080c6984200d2806d000050940c144807040384910402c2000282c070001d0411001200d1648150341180001c080c14208512140801c0c503d40c484c000c2101c171796012802780c02c80c441d018420300701118803400c4c0c110304040c80c000d500101d0501107100201000229111404041c0814601074a81e00584000715180e68480c4507401c025401400301c074002d441800340004055402504040c8055895907a00341841d00c1b0540c1400c1c0001e43e0101141e03001c2d0f040c49240c07440007900c8003040c0200250800490100210301c100d00851201c05000c5014059060822020810000440b000c50300e542c50001200f00a5485080c014a0a504041d90100c04400d00044480c800f0842c00262126402980e00c50707580c0d51320400003449800f643c1e5400c911408005100c80903a80d00440f08044d515094501041c44444424100743d508501c1005265000c8180f02c107020804000c02e600100c140c0d01d2010190302a211 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 768465323 1250 768464073 768464077
    0x911071a0618040f0206031f2d081c050d020a0305010911090a14010504121a1f0308090a05031f0f02090d0b060d080301030507150c11090c04120c0510030c0203 70
    0x40c6c0941400000b06044019125003d1000d0024021840c0810f444000d040c007042c02c500c203850a00100100c100800550746040d0b001100c0030b11004111401c07481c82d40513103071001004001e05102701803258814000007800140000001c44c0c0c0e00280960400c8161400c80b903040b1180c0ae21104140139020047d00d80c1c1c14030301c05a44100480000e0b10160340012031b8070344925080050180101c185079810004100351952042d5008806940c00350743e41040c0c83c05e00c2c0002c1741e4001c4107100e03101080000c07a04800090684c0440a80002074480e2203502103480c240204100c0c13880d1200c0c12441c0c50100860b8030800ba4248101d4000b9881c1c4501800003801b4205006409007010b6201004680c159903041c0985403a5680a410309880e9039417030521a4580045220b004d8001c0f8607000c0c0d120020744581c269141d40e80d80a054000c1c10b103031110920a001e00010032031a586c090410011607504444140f2078002480741030030311552401c2400b4000c01c1101c0003140018103040223000000e00b900402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 768466573 1250 768465323 768465353
    0xe0915010f2606040204080a08041805070207060e0a21050f0d0207170a390b0403060515030303010b07051209180a060e0a0501032a0911071a061804 65
    0x14802c4291520f5000500a108a611401c107902c1000b0782101000b01400c05802203c40c4019103802c10840c004d4000280c40c4210b0f400c50040c0c000c0581404000d01501ea40d08881901400100617039031640c915440d0a60601c076000c162001810b141e03010008104803002e820344040d4090880c1c000c2011019507141000d0040da840d04002034002c0341d102d07404101d81c0c0420b503001030f400d1103c40c0d070f19121180c261034400b00181d0415030844028912044d031074018070494140c00794040c03410b4a991100c200410000d04094241c43c01c104040c0030a68007013015502034044a603100313946660740e15059284c0030112101000c40070b014070075210079681d144041005640403114180306d5070307940c4003000000c100035044200780740560024840791032841e5021505903407154014540c03889140c00359100b41c08402d02132810b13051500c47c2c00d005100658000100244100802a061070801e95807451605d0000c0d4038074281c07003441c0c0104884d40c90700c4003400e04107441c0710b1510191400c00c0c1d120802800144a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 768467823 1250 768466573 768466637
    0x603190b0a020903100606050a1e0e0d0203010f1518060806062407060f0c0804020d26040b030f0708010b07060216200f15090904030e0915010f 63
    0x1c50700f400951030501002d00d012005600800c44c5a466120140c140d4200d20122000140c590540101e0030465414010303058040c2c2c1c4604c074801c0d001e6020000c0f00caa210341e0803a0995224440c401032030b135007400341030305281c1c0620502c8400c5044c0210402100e55007241513540c0ca0600c3c4003001240b1022400741d0f00b08200783c0c1c000703403581d01220380d505020412a0303140150290001e40e000900c1542d5201d54020415040b040c00040840101104c55041c199000b96010001001c4074000a0118690070800c0d070040c40901031500d01c10704c1401840e04943d200c082c0c3c40700c0c00002c01c031101065440080e030081690030802c9107541000d40e44041c0340a101401803c540e80044da90000c028084000000700f54000401220242d20400100c0c03050800481113000d24070950409500c1e10704507205540c9100052100c1e414603110700200102d0030801f0304140c045c07080b01500e40a05466802c0403a103d180724003003081400346568001458500803204050401524a00390002005030b4034035180c07001c00c18 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 768469073 1250 768467823 768467827
    0x1091707032105040c0e0106120b03100c0e0306060907081602030d06060c02040b040c0e0402070f0212030a020d051611280e0604060506031909020d06050603190b0a02 73
    0x14078060700e4071020314100c0d5860200800c112001c00440b82c1116128510a0104105841d500c1085403441c51007030042801050f59801480c5014a0070362040c0d0082c44002d046800c18400038642c0c0040f509070b0318845001079034820184840d41000c208a640005003564800d0082c64041401004650094031034000c40104c9031100600320b10800c207940c0c00184c40b420400c051581d82401038107018000000b01d000b42c0c00d011510141d8507251080e0030000300301c0d441305240d00c01540c0801000f50b1010004460300202607900c0005030301e030b00034a00c48092001d001141d036054001c00203840c0452100f5020208403007001810300f190100c0c40c13484949039014903450f4000b9100800654101140045441c4600000d8010b008a944591005048964501c2c0c0b118180d11a4428041603481500825030002000c1020a0040c01105080e02a01400620000d000c0f5800c0d8005a00b20048040540341c1e607031104180100c51605210700e80c418088401c2820507140305644401c0008801001000280d40c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 768470323 1250 768469073 768469087
    0x20d0e0c0f091321030f060b090d0201020709111b06061332070e03060c041203170f011d090d0e010203130b04080f0708190206091002150702010917 65
    0x211440039405503611141c101c1c50449000b1240000a084004060010341006e40d0318444079002e118032001d964442294030700d8005100c0030b01089025503c8100d0441c0300b40070001403601c08a114484403503460003805907842125100805044010f01d541c1c5600340c20800520000d0ba44081c1908555090524013290a410a100400301310860301140410700244100d11903286016480c210721460503038a0b500c0d92480d00360149941c0300001c503a2034180800811090140d17402c0030100301d6404e4801e241c50013004409092180078a103003a10519000300035040144040d0b132008284040d100280701106005103000d602240d40e03501403030401002c0c003024007024941039100340b04441c03683e0034001140b41d186a599542c980d803a03015214054403801807504100207614080f441e0fa048910000041c5506142180c1c26810031205c0003003240e10883c20050007520b81c403081881c1c000d00055401510314540c0c132040c15200418000e001000710b9140ca032140700042c040380b01d2038181000c03080900b80c8841d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 768471573 1250 768470323 768470341
    0x90d02061e04020402250b0a0902090415020f0d060302010f03090308061e150d18051b060706060905063604111c030f03150e04061b03020d0e0c0f09 65
    0x100f40a000002c08002c2803031503c4920f00b01d1100c07840305200c2c1d800c80c041603661103048c0301240c042c00b40c0298071017010b00204000c100113040c888017000695070700510704030640c0c100070340b594400c4c64510703c40b0b0b4a44008009545c0c020b4010322940c001c07418144030021150f54004e061180040015224003010b20b010780306401002e0401001d140b025004205602c130114101507240c00090044001c1e900380390000c612400c010f1000c8001550050060480c0d10061816544024031210b03c0381d04070109026407800315889010309802092000390004140c1004000d00c5200001042d41071140b4002080c1c170f0184015410b00000c1c0170704900c504005a4a55240c10700d05142c01001c1c01e50f0102200c20f10408042d10300390070030440b522136201d5180c1030804440607016241c4039102c2d1500407078a560108401d440e14040103521910424000460803a1402112840d400200c003000c0001d50100d480c0c4030030300540c420071020411050041ca010a41d1800081b615021007118038000c044181c0802d41c080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 768472823 1250 768471573 768471577
    0x5011d0a15051c050f120a050a03140403080115030507020304090c170408250f02100c0b040602031803040b09010516301d0105090a0815090d02061e04020402 69
    0x441d00030100e03515204440f418940321540c6280544560040d609040900384001814000d0410100403050508800890590341c94108a080070b0916442d801c00140259495030000c0c8500d11980f941e64103541006c1c0c2a103c07442a0392000c0e4140351900083c011000d40020a890882e2408200807880c454805801c0f1403604412180f00c804032401001c0c07000300200c0300050254050b908100300c10114401c800c42c0c85a0f209500040d26644034031401c00e000d400c2c00740711950300c0c0b4154146103015401c41d42c1c0e6050100011681911003a50100c148499840000c03070310003001d00842c0c015820702d400c1011003085841128001c0e0705100000070400d0200744104042d94484c0e40291010764032091829200c00201441c0504416101c41c113246011a9030107145a00d50b1402900001c40c0070f800040010344031584800c3d80d080c0e101c07900c14800618000d0422031440171f0711030100c82d141e90b41064a20b4a10340700540080600b55046403041001c00c0e40311031504440803040b044030a038a9281d600110b4024 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 768474073 1250 768472823 768472829
    0x30804150f0f0e010b031f020a03090506070908010c0207050619140724091e061d0a050d0f1d04060308071208060916080a141905011d0a15 61
    0x154201201040c2c0303042c10390712041190112800030300c401d606500405841d11203081c03101210510904c0100c2c1101d100340d0180c40e1740e80e00c0d4100050301d840c0310745440b40307401c4044807032000080c0640f2040c01b00314000e0207006552070f0310340000e11301c1e1030921002a400c2d000d035281c0b040c0114426a48071040900c5802101400202c1c1194a642c484080c1040c140c20803018020308038502540d0364280c4103e105211740b601c6d094000007410082c010041403aa078211400f1801d075107861720b610703400308200d031405070340340f0080e01c2e520040a103c80549009810a900400c4400c140106503541550050b042703100541031410480e540001c017811b003c0007400910080d000a002e4410108a01080210a90420b5080130b4a0b81f02d50089655200400001000882d03080e800c00d806100f01c5103909028a000a8204442002c00314912a00c444030340000c84003200c08148071500910900582034941c46418090a80c20a000c1002c100415600760015030141c10300c0d02090780d17900d10310110101d260011010f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 768475323 1250 768474073 768474101
    0x1e04020d0f0b01090c09050a05011115090706030e0c060318030705060c0903100624050706020d020403021323042316080303040c0311031501060f0807030903080415 72
    0x2803039126040c0602d07061800d01562003500d01d0040c100c41d4040c021000d603421644014004640300b81003400445e00b84ea0700c114003500921507007451100058140c411f91b0301c01c540090040c80410f282c1913004041d1541400214240e4028052050880d21110203c1c0d070720002e00350800400b00c440b02c00f072a14501c1000e40c007820b203014960501079032070407240080c58401070881c1255000c2134024440422200c00d8800c0001e012240b2100c42c07843f00c820865007410242c1030500608100c019111203083c0ea01c81ca80b10022036030b00160070700c11440c1c0118903483c0c3c0802140c0030400a40c41082d00100b065000d540350300201031a0001074104200340c1750a8200c807100041070124a000a0300044d41c410350020f07240700341c4850440100700c03c400041500c1c801d0350042603100203030340f80d5245e042c0d0281800300100c0d01802001240d58100400b41d46031802000690b480d40300140201c075004146071405045581014104510400031a92181003940c000d03811110409451008076004402011420f000c1c2d04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 768476573 1250 768475323 768475343
    0x403080c150c0403060e03190305060d0515010812030f07050904020d09060603031e12051005030a030203090f0d0201080a050703021b061e070912020a0504020d0912081e04020d 77
    0xc04002941c2c05081140d10501040c420f0361150350115481c1d01400c00e070750940044550210140500c01e402c115085400039220384509100c5440306414940d040e5060100300c4c0e0100300421400000b0080e030750003d041c510104d0f046082c04001000710201c0035020900f0072801003a000c0c040e541b030740c0c1140e66508900c2020040c0e02d8042c5040405054107100541c00300700b121b0050b5030311034040042d0b040301c0301d040d0703584010181d804010360f0010400606001c408001400e00428581c8041007038410641c000c0e001140c442103036100700f00c94110039220700d030301030b0110882260050341c000d1101500120400710205180c0d031803910460082c010b00458080c1241c046481d641c07100804280503014102300a10f040d5031401c00c1800765003100d4160b8070f4074005194024104130789803000c54405001c0d4030091841c1d04503540c88000030f0980c0c02000c4140c0010f699424180200102d1450024a0540c00e040000c4603203820b0380c0e0f00e6544155612050038038040c1400003411075a40c01301e01e030405644458020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 768477823 1250 768476573 768476581
    0x70c09060909030e012613021921020a0902031305010c050901020105090a21090801020d020a0f0305070905040209030c060301240903260c0f10060b09060403080c15 72
    0x1c0070b070090510a4020440380382c4038440d5035100d03080003440d150340c48600c0b11320000c0702c01daa00b0306184020f04024202c1c220401580047c1d0b16035403207148030404895101281c0e0b04000801d80d140d00b100d420401d42c1a0003500744030041c2c036440108800c580d80e06400584a0b51001a01c0600d00c0340143d00078015440d004242850503001001361a0004080c2d001300125034070f81440c0c40d038030403060f03030041c203681650040c031040300c11618454003413101c283c58814900741e6901e1201c3e0a9030441c82ca0070441c81e1300442c24140c0c850b40318440d6102c0411514040c4940d0420403400b40ca90b40d42030082030b02036900052840380700d88007080307850182c0001828036552503a440b00e40000316201c130445600f0450785e101213842e000e4411881001603076000070b1400190020b1a0007c034a80042e840190112003044c480c449a00030244031b90701c503e001110103049840905203008003200d0142e00f00c51f007200024407500b18030b5100d0b0300035201541d920a6045566407800000301d417402e5945ca080082c006600d000f00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 768479073 1250 768477823 768477839
    0x1a0a051e04090c090f12020d05012306032a040605130902280e071710031b06200304080601030c0510030203010b16060e0f01140906061005070c0906 65
    0x420448040c0c500803c0341511102003140e089086201d03041d203822402000380310b40315041c0840c0890b0751009180c001001c3c0e641d9203a5003500c03d03403259030201c0080108a4031081d142102403591000c000c42c080c0c160300707000c0c00c4003158130b80c2d11592a400303001d039241b40506191034950011000e4400284000c01400401e920354000e460828801c03405005800304080380702146060805201d6110940d1840e07042c1410840140124000c003010108100700010b4580c000786164114020220000d05100f00da0450070a540c40189403c2c1007035109504a0f0108900350388403415640f0f04290401241c040005000c15500c2c500581d00154094020603000004100e814204d00313003107400980703004842404144041e012800244210109a80c0412100ba41c9044010118841a00c80d100000d40e0308034084140e4a403200088002000769507850b0040780300500041029400301c2c000b03005000528041c00400d0305801e203207420030240000414a4420003140000e40409050084420002542d4036142 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 768480323 1250 768479073 768479077
    0x909090605060a0902070503030705030402010509040603060f240e04060615081b07021507050708060a020c1504020102120304082b0c0e01080610020a02100201020405090c041a0a051e 80
    0x1162080214243c0060940c3d050700a481c0c0554101c0c01860655442d00029195903000500407070410800300300101140c1e5a81c0b0900e4060b40c007400000400c6200000603100315214844140314010140601e40c08031502d014500042c3c03a50804002e40585561612002a02e515041040500a9074011700d5440c2da10140b8148241e0340700d840c103c00200141c84007005441040800380d00100e000c01c40304848001a40101145445041110300540c1e8440341c807030a2090a03950341c1071482c0c00084551000c101040040003a0401c004407162600b0603030b002035548c810261441c0d100ca64003000040900558905030f52141c100804468040082c005000410011007020b00108500e040807108000b880b4109a604e6000181c5805550341c6410341041001c0d40c54031816000c5101c1e01c1018001a140c3c07500508102c00c0c65000940c60394140001c04c8050300c801016181009000d0104000070852041d0300c009110b40c0703508080d900c0070032900880da00c2c0300304072400c484602170241c040c448080001c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 768481573 1250 768480323 768480331
    0x110a200d0f080a0504050316022103180943081b311a03090705090f04110f120a031101020a0504380d05010e060108070309030909090605 60
    0x180c2c0d805580d540c5000c1d841200e006581c003078129030040c8800301d19020000e000d104030600050194240d0603205511800b91000c480480c0c186800c045420386158103450320000319580d040707680d40401c2c03800ca1003640c2c480e444889000345120003421520204e400e40612804420010341d0011004900048040e200c00003d40b100416481d031a003005001c1000c0c142510048a026410301000e03000c01c120032003181044250103107a80304c00c5a00040e00011451400b403499060390703813264807898500301c0c1900300207040e0300550045d101c0000b04044071440d001c5c000d40c0160b111809098204c401d81c042240210300b282100c3d040388032160740c100d5080700014521051032099076004105508201914280d00416080301c1c041003091005001601b00c45100788a001e28109aa10105415200b8032181c83c15076070036202d42c01000510300e0350a1904d405001c0c09440e0850461044d0300f40000000d11140b40100702808059403085001d003054400c42c0c211004001440082c0329400f42410083c000f05000c0e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 768482823 1250 768481573 768481577
    0x507050d0f1b11010c2d0c080307171c06060201050402090601030c0203090111010f0c170601020307020603010326031602071d1f051503040203010c03110a200d0f 71
    0x1450348000900c030712030100342c003d0788181c85020048600b030065800300420070007225402c061352104c0b20244414010301c041e816412411350a03501c40741c2004280c4440f5a04190020380041154a020950200417080d8002070403c00a58400a8205000410803520544c01c0300d0790030300d0300c00180e055054000078042c038003c48800381162117080040d0101c43d43d2224100258006100310720456010311068a400c3c82000008039141c0b1003404030303008541840070180003142c10107420280041c0758046403035202e0803c0c0020741c40e01c0096000200913010500c0b005190701e1007102c8282c2007004041c01c1000c08034000000b02d84909003851303500c4103102028040310061023071400000e46c925407010ba4a1515403500001146500c0381038052504442400226101d0074842c2000111a100c018911041090424682d03459040501c105401c1d10f2010203044101414840c40000c5501c071070b01200c003103070094101440341201400c0f81c004140070746e020651b014081c0203c1552400d410003011200301800b9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 768484073 1250 768482823 768482837
    0x203040501110a1a010303082410110f1e060c030121020a0b21160315030c030312060806040203102f03010501030501170a0615240e2e0507050d0f 64
    0x15a60070341541840c0c01c0c561407100078400c03815070350402d0082001c100ac51741c500041d1014019050318030348420004c800806901c03043c4480e2600c04541c000a00b000d001c4e0000d040142880a0314201a000601400516007101202302c00107801c0c4c42e80e5005c0443d80a01a041c106a55202d40c1c5099040350244800482c45d1088070502042d070000702134410f0303100204c10203481c2501c0004800802101e030042a00c011f0040700400401d88249040b4020b51090340e8140c01c58222944c03400680e040c681c0202a6a030010041c40010b0b503020440b011891242100042c2203c076030404281c00c200c0f03a95605441c80440c1c1541144801c029000b10705850007030f07e051080e40d0742e41410b13018a00228107140c0d02500059034000008100b6001101042c180004c405182615a2180301c4050800d4414510100c0074480c801601034102c1a03a2011100480382080e4404980421124a6140c142101d083d041c40200b558141c5000702c041e05d014130342010450f520003600c2c242c06000111303041c910b0804036485e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 768485323 1250 768484073 768484081
    0x20d0e06060312040e04200a030602090102070905090d0c1b03060b0a0f051516060c110f060105061e190906080c071e020d0b0a0c090b0a0203040501110a1a01030308 72
    0x1418216001c07229031003445c030761694407612165801c4102c10103a04150510500201b20343d6100c2000d20055809024010b0743c44000c4d100192400c10300b0b91060b26902e05103400c001c41b58a011a81d040c4031122801d004080160f145003a1000e9100404c17085e407480105031011041c0038041c2c0c00b8001588050b50803211240c0c40d0700020400384054498613603c4009200c0103066184ca0301c000d4a00d0408940010f4100042603a410302551281640c100c006800d08170075a0910304100000405848002e01500e01e95040c10041001ca100c0c1054840c3c05002c010b517080f04480f5148201e031400030220340b59401c541c11900e00189003c02a1040c00d00055000000c03400b0026810308440310280d100c0328841038180300082500303403000c981805030f83c00507400c1e200d840462801700c1e40d07030b2107900344070030010744180309400c080c0840b0f080e074000242011050049103031050b000422241911400d003040c801c0882130824181ca06034030301c07000400d022504010890501104240d0b0f41c16a403107901c5004066071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 768486573 1250 768485323 768485353
    0x140c090a0e130305071509030507061505010e1e0d05060103031e122301030528020306010306050c1603020115090c020c01050a0903060e0609162403020d0e060603 71
    0x9030a9034185580c101c0d482200002034044c0740141710080c45000401900081003070307280200e0b04401c5059000c100d00054100400c150351141c15010740801904408107410207000030b08101c0410308140c00ba058079030a4207564428000e0728200182c00a00726800036555180031600c545e028403040340454080001d03900404031410814070300210701e50300c0200307016610820b04d02400700c2440141c2c01d1400588841e410741c00b002c1d5030b14040c1d070013035005084443e4000d4001c810086512100514620b0f269200401640d011540c1411650401c00c0480c0d192198184602c642c4a1001c01d0b1204008549040041603010f401200f8801d0381240708144450b50307142c1d00c42c15528441d11907001a04101460b0701d0a6024402038800c1058505d00070801503101c0e0b5518007100c0a8172040350140d07003e1410803110b58401c001004142c040b010070680d89a242c980b400540740c3d40c54642c1d1000a010500030300c1c8040c030a41c142e40e0100001034042c005602e1005503103866a1050719118003034040d410070407226071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 768487823 1250 768486573 768486599
    0x6080118091109090a030e0103020a081512161e031a071b0318061707050a0c0b01090b09060105030907090f020c060c271e0301140c090a 60
    0x4440244045040140c481000001c21031690101c40e260801d0b800c00c6916250120881d02c11100c44008150540e42805d002e017401c5602003459040500420036140303040e50100c1c0a68000301c9082040a07000758010005c0e0f000c242010800c1900d10554014640804501c8108021507003001230007401e1800003c80c40000303d0a0340005091495450180942000e03c0f100710741e0311505914110011810500452200290b0040203800044510549038401b0a130300301240000c11150400545074524607a24086081004004c02c5c188140800d00701c0400340520020400070b030344044000c8445da15184000700a040281c1d03500e01442c000d4000991550051007202d005000401c01084200c4c9405091805003024114480703e0315020f1003c04148101003201c1d41c050207900340303019180c00144003514a12007020145408400e05400303520b446440c1d005602040c65400240d03060b5100c0b030100442c0c0901b101c00043c10031038031800b0800c0392540b00b04028290084d022202d03c42242d665401c204034007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 768489073 1250 768487823 768487829
    0x22106010c020d0816121205010e01061407150203040602030f0f09060114121c111207060507030905060405010b030f030301030c15020f070b0405270c0c03090301060801020d06060801 80
    0x2031050f4880d020603040c1019040d0840c404140907050402c6940e01c0655107455034564002c10309a4189843d505882c0c040c2c00c2c003412000c48140919894070754020900c410042c4003042d40000000c0300e03028800b1841184012422900b8295a203041628209000354012641410900e40000c0803a02101d0b2405105000314441070043c240b5908044160f544201c0c80100940d02158416020132050300a200c05080c2c0d00864203443c644064091020f001007043c50061901c5401254000030303803082c0581981c0300da541000b0300096170f660300e600c140c0c02089024400b924031f10820003084101f01d0150428210320406409854121050000c0d041d41c0b40002c0c00000d00425080708240402090aa0f81581c00141d80c81200c40d858070501c1c042c2e042503080e400c450b00100001800b80020708110055840c4240c3d404030030480c406024040498080001d071005070900400258081c402000708180c4101c2c26000b40200301c8140e071804c42d14000d41c00b0200d1054114240b080010f8a070b400303084010b0403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 768490323 1250 768489073 768489079
    0x10504150513020903060405010f05162f1006060e0a03020a120201020307080703030b0f0a080d030b0a1d0109050f070203030106081e1306051b090f06040306022106010c02 75
    0x4031400c0004004100e010030742800381c01c0d9030920481c2000d03501048828007842c00b600000030408600560201a120020b01000311180150781c48040241e01061a428041003c00007a01c15840d40441881502201c11000d0551160705109406c10710345922040490301c5030703204c0340240b80860060080400c050b200203988400d0111042003217820a5400c400810320510540340740080c182d0342c01815030441c0d03a042d00040d940361a03c807400c2c140303101d5010b111281121011426464070034402d69a1a038122040100754880d0011003454680c41c00100144c01510f005101c00d030340c20340b24011883c1013485046401410400450303000d00300d5070b50031400b60002d40c3c0034500e160700307000083d901c920b0007412404a0460203040b800400c8071241030036020b66800c0c111034940c1d0b006030400c1e07402d07110301403d002c4008001c0c030340b409640233054048643d1404182c0b82460b0012044c800112a401954000342c000c50000a4007028a0380d076044030011070711607042d80d11301c82c0c035208011203d9807849840250 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 768491573 1250 768490323 768490361
    0x71106070306060e060717030907180b06071415070302250b160e0d03030902130e0718020f03070e100905090408090f0d060515040905031603052b05010504 68
    0x5203428021700409003180210020142c014907042c1650150b4422950b890054022010034480f0340200340001c5013140c0322190502006440200003401403003410402001e456048070500d411a23002d01410b20000c00c1726000c0c0110b864000303005000703175204151140284984804d005907034001c03682c2c0c070106c003604044d900804d550b83c2c030700980c280000c0ba5500410702c444600071020950756076150028081c401d0390081100d461920501400c0300400c80e000c0c001e80e040400c075160440c0c00203101821201c1c0c04c10b041d0044507140c0c00c0e01d0000d1261454055400400000700f01040f170300088007042d500e10544e0105086900e40c075041310358540038081c072a44a10440042404102d10300060310f4491002000d07a082010020005000401f102c04220340d5a500d8038100300b00303000380380e070641c070803450545d424000e0030415542c840d00c03841750400010100da000c3d00c01c05d0034948517100750340000b03983c4030b00340c1c2c3c1580480380c8000342681c0c6018408445400c090011450742058000d5212051404030040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 768492823 1250 768491573 768491597
    0x23090d2609030d0204060c11040912140d05130210111b04060b071109150102030f0c01062309310201110d080405010f0501062a080307110607030606 65
    0x59840c000181c408400d5200902c40d82d2407285492008100901803a21101c0104090b0f00c0c00319640318459400a2155240c04010b0010488130044916400d1540c40c1030f02034500d9658114120303024000b04100c00340e14050030003140070041d01000780154000c40d51020313500300d80f400c00c491001c40d45500321001e0300700d0100010103015035144151003650003000800c41341c1d182d08421403250805481514540c1240418aa040c1448800309070000340403010242c640d8030020020303641e40b00d026070b50b03001041d001409140c1d01400307610000103000c0382403480c000e590b1206810303070344c940c80340480510408411008c5000c06407140600014a1000038a20103850402d51034225104090710091381801242c0200380c0140c1001e111340781c1c290301c0940b645401410181041821217407540e8065440514107001844400d40000d600c9410380c04900d0f03c400744078000c500d4842d040450403001005198044103000c0c0954002031001e41e503814071000c0320300741c3e40c0380602103040d100039108200c045405143c2c1c80b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 768494073 1250 768492823 768492887
    0x1205062e030f05030f0708131a0901050d021603021c0503060108010530011a09040308010506130b1206010206060a140d0503040f06030e0609060f0606030a23090d 71
    0x14516240902c007601d003417660340c0002d95882da008010840c0c030b14000040711001c0c05c118070580009007100d400308400ca000b883d05448aa03104d0484030302c0c18000049003d172003001160b0120340000c590380040491629043c940070f507880c80c61550a150050300c0c0b0b1451000d65201d08281ca205401c140c1d10002c00741d1900f0103110100603051549c4000c05130100300c10006e5890058400c04c1580554000640c0c500c500030b172080c4c404030042841c0d00c2128680c0a001c04664482805419200101c400c1c07039030b400d0f80c0051289140040e5214080da240082000e40d002e40115400034480e140c2a02911b01581c0c4001c200308a03880d0721300030301e8601c04000b540100903040201c00404024030840440c0d10705602d91042c940048101d0340140000703a203131144500d101800740f045640140c2441d0040000781041c00d800301d44c10300001c2000f40502404400140d101d8255002500c0040c6840e00140c1076064440d07a1140c20b9000f00c60141c1d861041035003040300c8900c51000d401c90b03000c00b40001030035071114100d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 768495323 1250 768494073 768494093
    0x6060f23030106030c0537020102033114071406070b1503033f0f040303150e240d0b0f090a020a1212031803030c091205062e03 56
    0x300041020074020b100c41500c0da102244080d1000d207500c1040ca14121f411084d1042030030002c00b045900600501011500f0181824181c9182c1c540d030000032600c102419296901c42d40c070251894143e4034980e01004004035009041d0742c2c018098101110110050081d940304490009281d07050100000305101c00d03072416a4205180101070340e14024182100368400340d030001c161007185d2002034503264822642c3c00451013498840c0c2c9020780301e00d0011402000c5007030082014050644074504551140025102c440150040c50406401420070400718200c040481c5541d02d00c4441c6007243e8a803030b103080b0b4a480034080d8840c0a801040d5216462081c207500040d10003500c0384603407961440141c1d034180d03200e00901070134120a000c0d98180e0800e0800b80d1000262441410718008480f124451404203125040350942404101f4a49540c0e085403010003a80c0280e0440310b0f40e403103540c204040441e1007401341c1201d940750009081c1d605104e007010414084803403014200070800f00001650909 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 768496573 1250 768495323 768495341
    0x80409150302010e240c03030a0b030c03150705041a071202010e0307020f0a081906050709050604050d1a0106050a1d061b07080102031305061b1c0207050106060f2303010603 76
    0x184040341d10350414010242c010500518041d04003104200c080c1000d80314207182b2020032001030000c2203801020a8486011846c0d01c20221460000204550300030421140280130f107040702103444920034543e0906402c11b100807038003101c00c00449840d040c0b050143c1c00404119501442c6004e04940c2000742c8503407a541d10b650802d08043d80040d940d5020301c503a034030240d007000700c1a68040c95450003000b11036000f040c0340c0a20082c54818020354950f58207840135174409a17440c90f00c0c98500d00b0304002e0001030040c0034800b00c004d40004a031459210001c0d18411403140ca8002d00002050444090703080340e03410480d001360062202001c82c1c901413000c1103070f02c0711030000c1ea1449a142c061f40382c00d903441212102102c541d2081c480040040400403154010071031041c944844543c03418145c003e100300003940e42c0d000300c01504050012242c0c2d040f0380041d40d0140003000f665960355005800c002c1000080b80105408450603200c42d444200c14071080000311411a2940c2e08047c825001411404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 768497823 1250 768496573 768496609
    0x110a150f0908030d060302210a0b2a19050c1011120106091a07110f033919030201050f0706020d050f0604020f030a0507170103080409150302010e 64
    0x181c009010b02d01880181008000d203800401d0850450051200400090340c0b0442d032008400c05800c8040400b040c04a0455400383d40050300703031034228802c0094a6070840c2440461a0b86030200d094201446c000d00300860f03c0c2100e08068401054240c406001d0a900c041c880c1e000003901160000041e0b000040114a00a995041c400140d2200021050980010000c2840700800b03110710ac05000649010501d00303e02603180504a95a002000092045883c020384081144400644d0107000d0b8045554802000a070a04035106180189680c6000b81c51000d13001d808120246040018882c3c0d100d0101c0c1e1492905585154011074040c0d00802e0b8a5036454000e0002000060042c0028400ca01d4203440c00f0a50b8103002e890706c0a1514003a12640c82284100020b00200c5440c40550b0303880710400c0300010315503541410a41c0c0b906090a013607017448117200c2c00030040003a07078000340c000e5462011080081e0400c1c0800829418541e000190229641c04101c102d240b40205181d0710b980c3c6da0b5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 768499073 1250 768497823 768497837
    0x204050603030703020c1903080a090f12081e0c0d02100c03060e0f070221180a06210902030609030d1406011205090709021801030f09170304050307020319110a150f 72
    0x26103407011181c114501c450008bd40c1444200801d4a4440b9400c0182030880f1400362419411ba49943c4c2a12980d07006034140c3c009c038108607940701412001c2d42c4da4140c0d5001650442c100a81c802501c43e1070f48080f511400f8980711841d41114031038820718043d1607414045092a89038040d44160680006090400314450040c0d00c0114480c0390320200f24207900b606626480d0fa012506000b44803001c942d825002d4604428200280d0380c0c007a0782d0343d0004c1442903042207004008007400e0060803604074083e4152141600380890740400000804c82c3ea402648104080c906141c501006203d0135104240014416299401c4844243d130019810602440441c0c0b00b0a94400e030b64001c1c1c6e000599106600040700a070b10704a5600b500929811089000d402c011400745641e44100490504c610032500340c0020000a041142c200210740c0700907002411591481982c001000c6a8511072500300d54000020b18034186909181010720180c41051044001510401c00111613521030301034100104942 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 768500323 1250 768499073 768499079
    0x8040f0807020a0303260c040621090c030b01150e012f010c0207050109030f06020901050f0705060103020a0905070e0418080301031101090f0b070209130503160204050603030703020c19 81
    0x80015070070095110b510744002041d8514a00035050080c49942d45c600706d004810030807222410001c4905030b40c01410400d13003043d81c020031400201100e00003502c2640c507240c02c840601c4070000e20a0101d03032003118001250b070380300c0d600030a8440c41a4019030101c0e85036200c45c102503010301d80414284440141440c00e96096400d080b662122590414419940d82c4410090140d41448201c015000a0900e000d0062455584070000320142d02c0262995030702180800704d0368070074001c480385807074002c0405440b81040d08140d03403506420b10003248104c0e4418400101d10301c2c01d0003010b100364603580b6080115004007050101130014140d2400148044200d894000f580303030340295001c8e5001d07102040b04810848005001a0100c3d0440400610075070400c015001d1004111280c280c2e060390307140110303111040c81c0d00342d24080700e400078030600010070741c1e941003030004202e00102e500881d41400241c40748001e06480344654240030b00140c00503c00081241451203442c51118400c2c4901018185d0f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 768501573 1250 768500323 768500329
    0x501030515060d1b0e090103140316050c0108070e1e010509030129010e030a03031a0a060f030b010e13052d1b030f0a0c0207090213030b0a090308040f080702 69
    0xc81460545640d84c1d40b141d00c40518214448160182941c6040800825a070344c030005034112814030009000190011007548000000d0040e40c1200401880710a036101c840c2c50116190600c11000e103000600480009910500c508201c1c1d403e02c5000e40780041e261039810301407240c0c0700310864840c1480001c0000400355102440b80c50000303a40007110714404005e4102009402e000004424100020300000444035980464615034243e40b504000602000f407140c0b00c804582481d406a80c0809d05500c005861a046900d03072000700c1c3c81d591b00b0000900240015140a02444c4040360040c175000d82c002000015076008980080d0482c0206030310741841d183d40d04502601e40304040f00c00000b48140301190102c0140720003041141041d40d070075413a02d0219046a1000280510b094944805449045500a10404000d00303526070040d541e550b000221410041c1544c40200c0e819600b000001e00d101c90703a0b229009841d075160755903c0e80e54840d500e0760203040d41400800c0c1c032541020007001780144d07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 768502823 1250 768501573 768501577
    0x90a120c030b1f05031519060b19020c0108070509060c030409020f12090c060a1b020910050f1203041a2206170402010f12020d0f050412050408030301050103051506 72
    0x500c80d640080f40c00200343d00300c0191410b40d8409406648200d80c1703008800386400300c0e5640400302013103c5c2c50303420103404490050140395021110342d0000140400e842e45c5000e100000e495419000c9505002010004680150781100c0e090300143d01808601541d1034520001d055000c01d4900b140e0603c2c1d201d09104080741d00c04402aa803800001811381104001076840c1948035000d00c015041401030013010604510071500800c08010080c0c100380b61402ca8020f0307106c0041d0b0060081000d525013500c0c90480103440f4050540304159055103d161b40c0b4044019414080085001e9401c2c03034038080382d2070420420b008914000c18014442443d2080b0b004106240d240d0000e1062015289030000c0501441202000d4103505a0902c04110150340c10031052030031400c0e540b4080b8605809604228001d00540700304032030440c240a14031100d03a84541060740114003a22a983c84a00007000a481034031451180850541007170004000d01d40c0217911850f03204182c5000c010000c00c00000181040e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 768504073 1250 768502823 768502831
    0x1501110c15131e170304030312050c0706050403030e012012060409020607061b0e031518010f1506020a2118120b01050402040b040302091008150a050903090a120c030b 73
    0x208009840800c50b2421498142c01d21904c450040c42c038141c11610001e04c00205e00c008211136a4a550102d221940a0000c80f0300e50398011008200c40d0a041c50010003030024000c146203d9800c160080004100307545a0088840078101c52600c0d0411800b500d11441900030003103941b2503900c100040158840d03000515000744125000210f08148020b55420310780881030140030040408103006080e10000703400d01440c419004114515030700c41108142c46160700d0301a0a80b5400c010f40e00099a502e80c001204114200015501e1a900c50310b00701da40740d483e514003030044241c241c06001915900d0011006800c900d01d021801c50309080c802408180d0140e0014070a1000410f002c02030109039811280903280c00c48055140518041981e1100d02542c000640325810340008206400241110300d0f00800008050300c52001c44142031005d0240e04854150034141024002800c15002004882c906d00005100784070660808411815009050400b281d51840b40740000c008124100f89042c82 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 768505323 1250 768504073 768504119
    0x9050a1e0b070207030f02040f0f0204080c030c0f0306040f0f02060a0f020d031506030b0a09050a051b040302030a0f06021227030c0727051501110c1513 67
    0x405421071810340c01d1244000d140c1c0c411074001070000d10003c0c100140440e0142c0d0111404944074090000300002014108840c807011440020300280028000c40c15440e2030f5022404d41c1d240c00c451206210342950016103051b4150402c01c00a070014016810382e22256004209034200c3c05240e81c0850100c4e446210f801c4045440c800d00c140f03d10303604100c920014103440c5400c0c01182c100d225142d200e09101d0084500b410340301c81011506403528000000200300b10901031040d4102005208014042a110b103c0120702c040840300b014902c000c11182106e03400707002020348041039111850742002a42084030300b25000c21004c44000402e5580780c0c014a50340d05107081070007840c40ba2241c2c014040c1072201040e003043c4140c4488290100b800c1c01282c03c009007400c0806030065a0809480710400e401c6034480c07910381446044448004a441015820389544100819606d201590303018a805215484a080c44260008181c07440c0904483d406222105101c680c8800a00c2035031520320415200b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 768506573 1250 768505323 768505373
    0x7050f0d06090c0b0a09260703140a06090812071805040209061c0e211b12040b030406060b041211010201020d061e300312020f07121407030309050a 65
    0x300201c00c40088030845600034025920701045c01e4107da4890b1614070010303005640400280030306420034080c10060580c40841007103000e10600c0c0104454000c01d810000c0240c1075000602c3e076500030841d0010301d40700002c240d00d101c4e24100411000e50311400c0401d0b040102070050700c0072040c00036403905031004c480102060404444035468540b20901148100704c0003103c1403088a0807810f000c42d0001c68404e03c0000c4078034102854145051680d8840c4002e044000400080050100001d140560701c10b9209010a84e5a01c031900c00701d0042e8015101802100d0744001d000412501c01180002d506000150600c5505030402d02100e03c0303640204000001601801409078858a04201400c81e10101c0c10344542c00d42d100031004900c500f4038644c9400045031550916025040040940000c11410340d5508035002a0380241c0d04200012034042d0140d2508000e03450280d108440b400c000740c03880c1030030301c0c1c8a500c0860181840503411790b01070250420b108081303451035100f01401c50100c3d1480c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 768507823 1250 768506573 768506579
    0x1b0105040308160912020303192a030f0309150507020106090b0405010806220618030e040e0309012708160f03050c010f1205071107050f0d06090c0b0a09 67
    0x5030003040010301c030b400501d14803c1809140c607000420101501c40150225141000b0361000c40d2842c840e80c001448030f01424008520b01a034402c540000f014440a00803200803c880f0808425440e030960080104415240c84402184a0f40c0003a40707013030198140000c80d1842e41c1c802c0301110300965001c001030b511110148104182401442901c45003500e0030400c035854075443e6912000003070110812a0f407800f070b58078000c0c0350a108014455410200030042c1c84003000d0303c01d400702880c10080300402d0607444000080e1070548600840901080069807030700c0e080e80c004560b184a0b0b181c07900400307088041c0c0b04c010280034440c035102419180000344100410315110203e2009150701c0110208050002480087c2c804210040143c200b804d1102d901032030103100350341d0081c0d200c105101d114642010040706035840340b0514103450100d070540307903103c3d111410b00c442e119201c05e040d81c1041c0c0400340440060010741c0440f843c81d024161400c00310f0340312a80050668804021103001902d4401e0074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 768509073 1250 768507823 768507827
    0x403050721210f0518040903020f060a0912030203090622050303010902070c0f06050703050711120c01111603080901090b040303111005040f0210140d290307090504081b01050403 78
    0x280c5080f10490820905041c400c03c49400c24600a02d4294061510f0700070718030800d4000c11221a0744050300303081c1c4503d807400c100080020040c0000555203038005400d0141d0715070103031080b41e006400c1d110140100d41d42d100b208810000e02d5400c4903032070054056a4401265040c4080d5029080340a00581c1d6003c050402210350804c0790000c101c06074010300100710284e0020120f510040e07150a00ea0340343c48a604103811032000b00142181c0150340890100f10340708011800034002e0000340c0301c80c00307081c600031441382d640d0080b480c03003c0e46059990001d00128000c880600010441450719105c3c1640360f040010381070f0881d81c000c40c040380c1c1d0704d58150600c0e0400d00c20520b02003111007080005251580303c4500482400c10064050309103414200c0d07015205051501d0705280180d06140e4400c100c512080041400c106200c098108804211032280c0b50040950201a0020003d19070b16090207000001040b002c0d2007124801e030f04222145441c015081cac4560540340850001a03585454140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 768510323 1250 768509073 768509087
    0x60306010603020a0f03050c040314060601110c030a03050705070b0406121103040c03081602090117010f05091f0b150a02010b010f1d01021504050303060114040305072121 75
    0x1ca9024180103103c0441102d51080c0380c03460310121031501041c1a151110000904d208a41004d00320311683e40c16039440250008030180984004e90340c04042c240c0c40c2c0074468903071400c0b021496258000c1260980402e1040c030203010441d0040080c2c520725076440e5100f5000b030344241c0c41040411203000f2002c040447c00c2c807034841e154460760100c918619251352160580e450300d0000910400002c40c0241c02e8100288ea40c002d1240c0c0a4a02c0d5640d5071600b0300b03801400350300340d0b48040c0c2e5800c00c0c2d00761004400c240903280c01040884002c2110303808604c03403054076a45e0741030030407074081da600307010102a512041c006080c0c10490115907a540d10b00d4100a00f500e60f030200e018144a1228452801580e0204400320340c5500001c0f80d944081c20500100d040c4668104107006988503041800142b12000c002140640801d8a0b5040c1040e600c11002c0301034043c910018105d44c005203c10050410f100a503031403600c0c10910846c64005090365420043d412901c00d1840010762412440803040d08116 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 768511573 1250 768510323 768510329
    0x16080a050609060721090203060114040f1b03050402120d090612051b0c0307050738070602031003120201050103051b060d0c0504030c0909020a3503090303040602010506030601 77
    0xe0203242c40c240102500342c4400040f41d2000320741c2034540b4800c0f260690301c8010340c00d5004041e80c025503940c25140c0700301c004011401c1c3c0324a237005203036011040c1d20311541e05024910544420090b10003e0164028500200284e8220f200304501018095060140780318400040e20b94180700da04003c001031440803803029180965207880180110b07141c51410000000c5002d01c50241da4900d074480c40f80c1035001d4500020450b21548101140c07010300c04010462103254601c01303c07a003000c050516030811030302080f03000307104400b040601c0110b41c0d190019580030203900030780013000f50349580d64010001034158140c0144d54600061040103000d000c031020700000504600f004848240000f2840d00c6101c0300c00015903600c407001001c0500034815a030040d03402c041c13a01003032aa124528030213030a01ca04200d214a00fa030074049501d400c101c0415070300e0310850001c0b0381c8800500c040580d4034220800240010700c0284503882d100e42d002c00c0203102a081d0b560000c140307400e2283c145441e04106030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 768512823 1250 768511573 768511591
    0x80a150221042319020a0f0b0304050c030303040b070c06060509040605070206251d040905070f0b0f19021e0a0b01050d0201081605040305010f020c06100b091216080a0506 75
    0x43c0988441d000c0009002d4120340e894080d20840040318130002d40740c42165403140941c040624400520009180081c502c240d0141050708c4607940d10b48101501e07840104d80c0100b00011407408a00c10f0381c4a004140c400394400c02001a14070380b60030000c1c403a40c0341290f0072245036441d082000305981d81030040d80d4002c4036024034050f03007103460001e410007695180b56100400c031070010b070308912680c0100c0c01c411040380078004110102d4141070280e111201d84c0183c6000c8411742400050141d002021034030018001d848007400c0c641d413907940041c0c3d48441c0c00c80408512851140d402c24030504103800845c0c6d143ca0300246480e81040c07600286629050b80410711a0014605030b00150f40c1100e0b8065110407483c11421841320807400649542c0a070340c20243c03166281103500b0605400300d60040491801c948121540340d40c9681c0c25488652143c02074500c0b880b0213011308006800c01c030040907074080420003900e00b407100158a08801b080c00fa072010f80240e1000100c02d05021040c040c0c0e642000c620 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 768514073 1250 768512823 768512873
    0x110f0a03080a050d0b040905030705070608071b1104050106030605041413020105092b060501050405091203060103020409090f0317040305030f18030a180f080a15022104 74
    0x68035240700c0c42c0107402c058410301c03200088407114071220340d0144562600040c402c009a81260400c01e96a400124048546104090001c074086006805c051b02c078801da9585e17480344003240044840403403481c0d00c046540103c85140d12000e541c95000b0030f4040c00240c1c0d00021560301e803d00300001e4611061030000341c600004140244269141841c0e02250313020b0800c00e503a0b20414001c5500001c00c2e00e41e05144880d081e032440600401c0031141c009441c0180c10900c00350362100b0821049480542d02d55855071b012003203600076031041d01c0c082c544c01001414014249032760781c2002801c3d0744010004030340d00e420b2014400b00705900000300203041c901c0005920400d15066602410910000d401c04100b00050000180707540c6035010041d907407015081c00c1d6501c0e11581038020b0318842c203000e03840c1411a003d80000c00c8142c400118803048650400062001c803105444800410020442340c4951030703020440a48000405400310300c0d0b1030003110001c547c5280c0b43c00d251081c2070f0405181031650447c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 768515323 1250 768514073 768514079
    0x501022b0213120237170d110f12040509091204030f02060715090209011a1b031902070810060b0711041506110f0a0c060807021207110f0a 61
    0xd0365002c000e8800c1c03007040403203449960000950140b9100d8606038440c014074030408641e00001e141042164200500c003000d2500c0e201c0c07000031a020b14014032402c3d40300130003c40343c5601c07480507070354100c3d05d6909542c46c0b85c0142442604100e40509101604c81001504005a05000c10725640c4440b0308005007203440b0502132100445d10030b600c009020610420142400d41d540c8800711110b443e4440c0300120108a4054800060100d034142a44201c0b00d4800010f003045409083c0e16001b4007100350a071414800c14500c190582c0091010901440305014900c02202e4900c5c038299148034a40003403050310310704580307130f031410022041d045490b504000041002e460103000340d030411a0b000c8549800b491515004c240203001111036950702d13040e07403a00002c0c000c0d007241c50080c51084035030565014252070300c00d8940e125140400103100d110426020001148030740c41072900000e0310b03c1079030450940c2c2e80d00c6242580090380c4c00d4542550003e405069450a00c00368441200203a521104d01c40c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 768516573 1250 768515323 768515347
    0xc10020c0d0c08040b2109060f0c0d0902130617010b210109021e10031517101a0f0102160e0a0207050304030c06020c030a120c0804030501022b02 64
    0x8541c50080074045407004601c100101c04042d580a0118002619102c02c01c0a404100a0100032800600780280e0303000f08110f011f0120300c551240c1c25120b0030007040c0d101d02d10420a40d60141140d8014140c0e581b86840c010f17501e03035a445a40031014000407482d54100040480324000344039030940300e0703803605c0110410b948070000043d80c00301d070500d1407088119440400c80d015180c1a00025440890424050384440303401101d85981c48060700c076000b11010030803080d000c4035444104c020340000728100401a50188900540c0034070200402c1d202c00c0411525803605a4401c44440c854080b18174400420030b040802102e00e0a4000344001c10704010302001802d0424414018103407003a003000c00050002d00c03250100c0c0c4459910404480d5a00d690713003003140285940d406103400501921191008525000130703101d041c1c1c1d0700004281442d20b5800415201e84100303240c09c49040406000001c00b080c42072003e003230020f03021072400c2a00341204106415550030000301c00740051040c068a00c05074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 768517823 1250 768516573 768516583
    0x803180f2d061008210f07030c0b0c041d0103150c0203040f1d0a0605150a02011523030601062a02030a0f0c05100f050a09080f030c10020c 61
    0x540034100c0000000e55000d0856429600181c891906219a000340324840058205010407110b80905482d212519421100d949105803e2042410305040c004600a078480d5402072484034401c1c184104107080e070790307521402e002c0101c84c10f0089900c08901046200c0745440e90381514801c0006004903581590b4a1201e5429481d2260700d02d10754680c00010403600030011100504a20060710190a1781c1e5116648001d020f49070b402040c603507103008508201010300545d025560000e2000e585800c48840c03401482e00084610011992078400304581c131650381a0741005401c03c060400d15110b000e03820720340e5105007190040e01903800b1000402010341d1041c0c0820b03000e4040c001170100010709216001410301c0005020398103000e80710105c01080704402c084222030f40f18400000907150b840d01042140c80404910358003260202c1c0c00e54007024451030061450b1406814000100354850000500d002d002c0114440c00382d00008000421080400400503081d07001c1c6019841d10128041c00f645078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 768519073 1250 768517823 768517843
    0x24010504050c0f13030203060c1806030c0f032a190809060610140a0216080d050406050f0d060305030408120403052523041407090302061305040204030803180f 70
    0x15403c0400c4a826101550f030440006580050840384c050400c10140c07400741e80403500d2001c140c020f05100038218100002038a1050b2403d42856003040032800b0402c58aa200a11000300d00d200b404c04201c068511042c00c1c10240042c01066880ea8025011844000881c4c00c0c00b0040c041e8a4003082181a00050025400300f001e6441e1f41503052441000c0c0d800fa0700003030a0700304020001c40d069038090b5000031450258500054001c0344540d4a42c2d5045c1c071010030340703103c0e0b0024508000502049000310000e021080700b4990702d0745040e550b00e01000803100c01c0c1c0c104443c40c5d00009030400050030b081242469411028030b0b4a0318007461079440c0c5654808020700181e40118500714941e01e0400c9400c180010040510000f00100118101021a800034486075100d289000d07401038400c0707032003401144105280e8580b1201c66003540c00704040b582092144c9010540e4109000c0350944540c00508000c500c622030180e11f80c14482d0b0030301104a9440c00f50f81d055401401c84265003071000500f2610 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 768520323 1250 768519073 768519097
    0x9170109020f1e15070c170d0e12150406060902040807051003021b06070f080c090111010e0114010f050d02030a030c06060306050c070204140108072624010504050c 72
    0x703000c0d84916a010083c1000d60540d00445043c40e032031455074a080180038079032003001e0b4040040d8480641c043c00354a0080c2c0e85016030f10401541302a00d0084901d8480c44100401c552500079080520a1400d01d4a41c0301da021b180120041c40100540ba00460300a40002c550540c01d0030305016500d96903031000c0c03190500c14505203460791241406030303040b5600c4c154009004e10a801d41a060290b0300c81d411b407040c0380042c00344210845058850f0513003900031010b120f0078070300d49a204001140c001203a243c0e548078039503030b031840e05012020900c5840412841481c60503100c3d89001c0400103144450381c0034a01a403440b2009000580d80071602d44140365250400140c249000e060040080020f40c04c001c05480c9824140b003000d02c40b050151030f40a00c00c0b201070010000a00242040300803c0c452444198419038080c0852026100c0c0c5040e1400c00c0c02142c0141e401d010a454a050540b030200300160022003054400c180d4007041e0140503103000d690a004904007080c4440d01485206e01c8100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 768521573 1250 768520323 768520339
    0x1080705070f110409050f070501030c09092003090d020f0705010903082b0e010c0c03081302040e0d030c1112071e120503070e04051005060f0c0a0309170109020f 71
    0xc200004030601d0048814013500800109046150080e6078001c02c1c50140c4c154415840001541d601c240165070b1460020380c2d680044c2d074905a60750003c0e10078001c1070030800c0c400c5240300603483c1001c0042c62040003d01c00030144000c0296000c2d0820702d07042c03080c2d500da400664081c40303031740d8000c00d2801c104c0e5489010a9940da4841464010403140c080380040e140000c0c0c10210510f14640d003203800751084003c000c01c200058608140c602001e00280200480e5004000404805440c4080b040c0180042d0001c1200902c8250150824001804001c0441d0352480d0b201c07181d6038407205004031126010014040c00ba280c04041c0c800d4091104010a070140c0380c540c2f10345000e600260244025402481c6a1f41740481410280c92030304100ca0050020f01e20007200f159916081c05894010f0b8007101d640e0342101c0c103110a010304da134480c8071145000a01002070214a040070000743c0f001c24003d683d1146c0320f03824000a10400803032484101d96683c14031100b400135a84503481054608070448502c6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 768522823 1250 768521573 768521603
    0x30106081023090a05060904060222090501060e030307031e030f09060501031106041202040c0e1e0112270201120f050a0b09090a06020a18030f110108070507 69
    0x3103070032400c2c1c0c00052180c120b2508020550745110600140d100040380c00758100c0d41c0310030b6844211041111429400700d0713080e0128010401a5004180c0300d800380c07058403141075014a80700e0b0703820350360303803003105001d82e9040104481c540c00101003601580860156252140710f460080500700315600d464000e50100b4421071450b40264004601d4060025041c070040c1158240003004140920098417070941d5001d51140c4ea2420030122001e03109001c2c0b0001c2c4604c2c2503001d00005049104600052090f02c5e04200e01d6940e4001c01220f02c5482d00340e04901c641a000e000521100c0c0400102c2d00450400c00c40c88503036902c500030010903032411310388076114008500040b2101c02c001c0e81400c490b5441c000300501030f15220740200344034400550043c03000854140500c5800035044900d04002e400400c554800902107400070060f243c8141307001d041c3c0d44058100c0c0001015558401c07203120103030326003840810800346050340500342c09082c02025850881e00c003408601c90303128020190b03682d08500c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 768524073 1250 768522823 768522841
    0x12d05060d0c03080a030608030a12021c060b190905010c0212011104080a110307030f020d080c030a11010e011a0409080f0a02010207140303040f0609080c0d090609051503010608 78
    0x1401c503642200c40380c808269a41006051071380441c6201e0700103800d004d008200d408001040f105034200e151303584400365180481007002500310822010000d407410b041100c0c85070f0b203030003100080e02c0c54804182d541c0d80209030402446030700000100c1803000140c010011a070f0000b21580a142c0c0590f400c940c820700b4280000d006000404511891400204011900f158000b03201c24650340305601c41c0304045602300405903500e0151000900018044014000508009440c9a2410b110b000800d04020215064600710f0b004550b03584000343e48440390501d8281c090040040a0404c04001c0115901d103000c070300382010130103c24130702450300c80e44240200300c42941190603280f100001142c0302c0402c18802800b0390311011082c2c0e4655400444040c2540004c0b048900841c0d03c02102a00b12a0f5565602d015041520040d58030150a210210340c1d000f0034041c0d42800116a65032000341404d00c0405490055a0f82025009e060500f040d014103850072011a4191210340c200115166110311407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 768525179 1106 768524073 768524089
    0x1403040b01050609240901090504020a020c01080603030c062e0f09180b0703050415020403022d12030316030b061219020705030c012d0506 61
    0x400c51450004002c2414120252141c0d001d4600e000300c0305c844010310480010b0070040019050700319030340006202d002d800c00315001c42c200b00701030100035607036000306008078184181c50b80803c0c050781c0e04109617000201c40c04200d811034600b00050f0064200c3e80c400b4609004113403120301d100200d9402022017900c2100c20240301c110b141004c100c019066224010b00d1441c1c1710b40d00403003c511069005440791809460204043c10b213403a084e40069403000c16200002c1c418070003800103a4400b860b456a4400c400d40024542c0f1070408100980d40c200d040440e0712000342c021145000c04040080d40c40b5041d031003034080d490341c69180240c09440c1c480d284141e00c014100010760b41c01d800418000e4008100c0f414516042c014043c40b1422a4000e40c0240c1d0a41d00110b0380502200090241812048014038504040c006225942401100a00c0800354050301d4a0001e20640c0318400 = true := by decide +kernel

theorem cover : BRFrame.Cov 768345323 768525179 := by
  have h0 := BRFrame.cov_init 768345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 768345323 ≤ n) (h2 : n < 768525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
