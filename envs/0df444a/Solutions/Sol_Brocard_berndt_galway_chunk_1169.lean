-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1169
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:34:33.726706+00:00
-- url     : https://prove2.me/submissions/8c53313d-f5af-473d-9a57-282e6eb7e12a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 210071942 ≤ n < 210251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 210073192 1250 210071942 210072007
    0x80103060e0705030a0b01150c03050327240702030a2703020a09020a080f07121a040c051305100f03020325050706050c0c0d1202211605 60
    0xd414541000b84503041250540300e445003260400190059282c12a0301010034040380c046030000071110f00c40c0400c40500019801c0c8040340c0c42c1e800080d41c0802f401c1000c140072003c0b541c0119070500304101c541c000d1070320351100c2034440651002c01507200e9001e40c0c140f0140d4a0044600800340014025000c200c5c034070075143c030518640c0b2100101c24406550000d28007601d079a62800780101960110510200007513420003c41e40410f4030002c8280289140d85030390041e0780546120000801218041101240400b0b01c10346c001c0c0c881e403055090054091743c3d0103507954002080c03070b01d9424080c0e10240c01203149c20000f0441c55880810303030340c1d89001d9140c00360b80c9440300c0e101e80e002c010342490080c0c880c2883d15402003026400000408000d8400c200074015541d40300b001c1c0030307540181544050680c010340312200a05d446282c03101c542804403100103081226002c40000364520301001204490004000d00180342072010552a00c0c400364a4a01d01d412000044c1c0003d030656680300c114200b400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 210074442 1250 210073192 210073211
    0x3040b030c0f040b0c0f06070c020f030a0b13021503010b1b01090503121e0123190603060302091b1605011e02180307050a05060906070b0103030801060f02010c08010306 74
    0x407004503101c41040c0890b09845a89030302c2c520b0300d035610500901070540701c4c03030880d41e003240303070106d13203103104400e50740b1602c0740003000c3d800b1301c01c1c1c40b001c13101d15a42c5030150000b030100140d103030b083d03090042d00001c070320800b02e80b1248103114a1003940083c400c15101c09000401503858048100c40c1c842a00e0240c0e140b80410094a032805412100c80c0200940000b140440d01c1d0502200d42038800c441110a8101911118001c101c0b852002c1c06284128042e070b0840500d00322507a1100104090054262001b07c00517001c00e440101d103a400690009880c0d44040040d49003661619400001c1c1050305050f008020030750032200d1142446044062448202c4541408030a500000366440c0c0da00c07851a2072650000440000e40c40f2800c03d030810040f00842e038415040010300102641ca0140c641c00400d4204010070207650040301c2590340c0688104481d200103020414118002d51080c0c68a084035414008040c0614007c400d0000442e8584800043e495500404042c1100d401c0b402c0010b81c200d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 210075692 1250 210074442 210074461
    0x90e0102030c0a0302090111030d05070912020a15021005180c150d150b0d060602070b090a03080d06030206040f030b06010e031c11030a0e040c0309032c0a030b0a0b0301060803040b03 80
    0xd84e0401c60394239010109181134005040e41029100e801542c1d02e094555840740d0301e145440d090200701a4000c0010b00c018818010204141ca280120a0040303034400103800c0c46000035218201c2c2c0c1c1c031421800684074004040c404211180801204407800e9003000030f10b5041520314002d12403403448290701c50620080c0082c40801203000707801d05070342503680c4400b9001014090203140c0300750300051140b03150000c0c17448164005c1c0c031440f40d00280444030151940d250f12401d0b400c0301d1001074009540d15000001a80c8000007070008021440703202a00700e285041c0820320640082040381400300d5038070194148c2d070300480d0352140c001c20300800012000d244441142c401512110b54105440005010307883c0b10b030440030040c41c24030101d50070301440d1102041103007a20b0318070000402240180b070800134082d022411f07060240840700c0d500a044440c1c680010b621556941c4165a0742c002403041c8581c000c054005c0d208000380650092251900d0305d001156a4811032184100640d00480428078100303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 210076942 1250 210075692 210075707
    0x3090c09091b1a030411040906090803150a05010203120a021902150c2107031b27060215130203030708090909060708150f03010905060711010b090115180f090e0102030c0a03020901 79
    0x51f042710f42040360318240d03d8081595801907808000c0703400860980c1ca110f00e801407080c0306644040c0d01850415000c10f003a40440e401c0a043c0140b010b80078000c0030038840c00007280c080180030b80d9000344500750b0079403510f0324100300242c01d42c1800141000300800d01152a83c004520f10420090078525544140040340100300301d81036240c1400d480341c2d152410550182460340180b0490034249181d2a506030a5500d00d117040c45160301580040441c00c403054070034556240d100100d441d00c035518502d1580003d065a014080c11141041c003c103030000321b810081d08459001c059100140300d9420a8500038021000c010034103240341507009034001d81030715004094076040c80050003d00c510001c03490182d032540303800c545410020310005040009644140220f01900740003921500c1140d00302240c3d50b8618501c101070304240306031002121311207180650f05000810301d030080094410308091828099030541d400300106680140144a018800e81040b84c00c05082030900503981e50f450030059860a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 210078192 1250 210076942 210076961
    0x9060309010f06171e0d0f050c030403030203032418070e090a0603140d0807080705071a0103030f051804020903390405010e060103090c09091b1a03041104 68
    0x690410800045404640c525000d801103020305581c10241c00701044036503174600c415611440d60041c0c1503109454081c4130a0341425100d4903080f03141c04000c40b240c2c2c0ca1a441641b0890041c0d10000801c9142080c84005171102e2814452505002142800081450000024403040b5401000220f0f1615005190500100c50050b181030b0091400700b6030b800040c07100344030540386000c81001046428601250024039040d107070300c1d201595112b022084441110007042c45050041c02c2101002207584140c040c11141064078034003400758154a001440740400c01d0602d010f1050901050f008000021907c0c0c140311410368006031200041c400081c03800c0d0454128442c2c4601c1c00b03200c20400060400e02c070000000b20f400e041c2c6171180040c01c0c0002c41e0800d21072560a221420701142d05907120390131541d183d030b014160417003682c3d864a549108071058604219081450740c3c241564803031010401c0001080d03002d00c0b040c03200c010203100d2402888002c100611003404003084001a41e01c0b980320848a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 210079442 1250 210078192 210078221
    0xa0b0a030510121b090203190f0216050d0e040203011a071a010b120f0402100f020c030d0c06050a0b0a0302062104030509031b10030207030311120412020a03050906030901 75
    0x3d83c1e905050104100380365000f000d2034141c4102000c00e5100b0240212800791003401c0140c5d40d0810340407985402401e0780000e14101c80e03001c0203240c81003080304c18207250b07090040010b4a0317100703480c1300d0141542c1d030541d04c614044ea0041c401000460040c1c0242940111070b2195640e49103101d00d03200316190544200304100b240d00a0000c5140518803000d444200604030080d0210b81703449065450060003190000e40c003442c0d056400c41da040c0b2070b0b040000b40104a00490f8068803141000a0401040840150005c0c07104e000302c03014044c00b070146079080810504100003901503031000c01c10802a03400082d009a03000183d9100d22307241064003881e05000121079103601c0c2010314005019030312004400d44244500e00390900910f891101054075a41c004001001040341d00c4d0054020f50440101034040c1980c3e03005c0504040d4110005106d400d2144510102a150078500a0648184054484119401a180100066049400c640c0486d208460207616641c0300d800243c090250300d03028800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 210080692 1250 210079442 210079469
    0x30a0e071a0a020d03060e070e12010c0302092106070c050f10021317060103060e0106090207060b090106020d050a2f0c011b020a05090a060b0705100b0a0b0a030510 72
    0x1155035084020b812002000c0e801e03503004965014045090344d071940145000c400380040420358150058001d64044180601110042c5e04034440e080d084500305100c0c40042500001d04c442036180030036038003003520100c0c4c1301c0d088082a0b041c00a544e40740010200014000402e0361841400002c10041400c0b8500008980c40d601b049502d4402942088100b21a00d102d04800402c20198000c0490328000c441402041140e103540c454002030145594110002d540c0c0c0c800105012680e400108000c40c080d132800718500103500188410401c050b4400300454000201002d51954804100d50003184c5910b0011014601c186901008100381c0ca04420000000070a1070500c0d0030104201c3d056610036224060b10b100c1c1c0d0342c0341c01140b1003020070080d80402c034880d050003285000000d01e900f02580c2100081c00c2a140c40d0020036503030060106071840e5010002c05d400c0e1101c503010b501c80148007600e0820710b0174035180c010300c001d001d0030505509143d12000040c00c0e014609818000400700031a030010b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 210081942 1250 210080692 210080729
    0x30509030a05011a09090318010905130501050f03030403030207090203060a09050708070f05090d140c04021b010f2304060b060a0f03050f1005090712290306040305030a0e07 76
    0x1d0081124075050250300460500ba22205d20345561664411004140a50f1900309808007000c9a10804502541400030200340070442d40c5942e100c46020f2070001c00000b559505080401401080d030401041c402c0d4803c110510020340d010498200b200c04900b4003503241d458060005043e101c0581200c5544ca2a07c4204025243d112202c1401000e440d200c801034441007260459140c80b8004405410500907210503002074106000350361076110070000c2e54840035140c000078040e0b03440060b07400d6003007203104d0040300300080078400c82c0140d1210382c00c10040c092220410100c98a0507140d00b0810312005070001d0701f88410354019884041c801048540e60716405080600039038282e03821400020300c0c000c0001c00c10542c01200d9030050031a0a030601c145494101005456007004101d807042103000e644040b4071500a0242c4c42001d41c400c081c40007240980c01c2d4074103407084c0b03a4800c5071096100c0303001c0c480425002800c803a08030185400118402c10501c2007586410313000e511440d0540d41104080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 210083192 1250 210081942 210081953
    0x20409060903110c0a051c0602181507020f0904020315191514040914070603090605150904020f03030912030c01051e22140c0112060f0e04030509030a 66
    0x10700515109884581c1107051642d0902d80e1032004000442d00400010014021450581040a010404055080307056145a600c1d042079030442c5000c000e0045107203c58085520702843c0d540441c80c1090381803810160644c0009007060301c4a000e880c066202c0e240030800755101444800080165400c05040303d06119012400d0b103607901101030141441c00301c2914030086000e0101040750f40300c1c1090164050f60b1010030006244445084982846040c3c4002c076055051261030002c02c1d2070b40300014045d01e142048c50030340b28001c202501070038500542103c9507565400759074000f501900d40e45a6003d484c80070038514880c8070401944510494145484030100000034081026404000e100076160303103500681c004020307494074280c084c1d4200001d4641440f00c41c15040c0b60350482510525140d25150780f02c001d02e0f48901031540e904021070150079542c00a440d2008184880010428149414074612010b08680601d0f41c0c2001e5a40c041414180b00e001a11060000101581c0555a036440c0c02e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 210084442 1250 210083192 210083201
    0xb061c0605270a03020709051f06024e0409110417010504050303040b1b03010b0c16120303050606070c150305090c010906270602010209010905030d05190c02040906 72
    0x6076550550b000d055840c11011403c802001d60540007004258108107070480540b1000f44001c846034502c0556049114107120150018070140d000303003035002040f401d0204041c40b0030301101e6403901e00400030950042392910390302d41030702c0b06c0a8125041044a00110061040380d01200b0020304040402c83c0100c0c0440050040301c5a5440c600f4404000b03801280c00da034000c131030103420350700148000743c041184294a2540610011135803010009a82094103050f0020b8001686444010a8100c40e0003001c100051624200300c401d000410b1070540c0c08100c10340e4101d001020581ca950103d90b00e501c0d55010342c0c2c0c0407a4880c204d1100030303450b481e8040f0f5610002c01000006410b11010075089100407407108454a0180d40c0c0c44081c50601d030040e14119051000c0420802c1e841311456000101950b04c500603203440d0b800503130746017198400104032481540200e882a00416804a1074a4210741100d0403550712110440b6003640030700b81a1013000b01c490020750414100490b000410006910 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 210085692 1250 210084442 210084481
    0x9041104181a0105120c1201090912020f070501030e0705060a0c03020709050705040b0c0c040c030605010306050f030604121e0206040605010b071106030c0d0e0d020705010503040b061c0605 83
    0x40402a0b0080c1c01c000c001d00b2a016001503011a100f00300f0b1140c09000800640d62002c550125280303004624110b02c076103200c00342e2006503020380d01c1c20908108411403e06074404080d620040551305135110210317886460511483c0d05161307031454004044101806420024600101030a40302d0b524050054120707424841c040340107000d9100007240300116441f80d140a01195039400d03003020b080ca0321100c5c1d50fa0060300d00d43c0a510031385003603542caa5118010310000122980e40030480e6850704001600780d4010b07802184c4904000b0f817801103280c400040300f90b4456089181c4405084a0000544180c0c428000b24426201c2c440e056038091600041c000e0300441c0314503005c000d507a0741d460000c0c10034060144010542c40b0303082c00902152404d04051504403060f4010710b40b40c150912088002ca40700c2d6031201010744c0201c85c0c0c20742c0c030715010301584004003801c1c01c0462451411380d450402000700245524420b01d02c414201c0750304801014008502540511300300445e0600c4c41024280144090 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 210086942 1250 210085692 210085739
    0x8102409170a1509062a0306061b0c03050f030c0606011b2013050f0f0601020613211e02071211060906120a0c08060a050609041104 58
    0xe00040d10302440c00c00340740700103299009000400090741c0c2d03030071445010a20164a8988899084002c07031703900e1056010544504502c0810b1400140010852007041700000c000e240c6403c508000313064025022555080a550100118a10f6403400e0101410690070250480c4a50100c85000d00c0002000b842c203c0c0c0c0c110115045035550f4030044070809696102005000d40c14108030000441601200360307107114814108100324506001b003041040400000c4614a440c4c1c0c051007040c1d0410015503802120f8607014072100c0c44c1000010359241800340079030205c0050007a50304c05202d0751b80f072640c0040305074107916400100c0303108004148072036014150640b0707c840c450031403003a80006001411581e0316031400c000e40c407550700d94600c42d1603800321040d00322804019401050741d640313000740000c0560b007400003810b0500320100310485000381840f00038040707801c09001265031340031040800c42e0000c86030b050b621100782c00404c02900561010001c821400303d0049020002624107240c00b1290382e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 210088192 1250 210086942 210086957
    0x6070206010f120303090c05040507090501031802060f0706090f031e0906120e010e1009050706090305100203040203030903060103031e181518090606080a020c070501081024 76
    0x54500002d448190300c2040c820080341000c52001078001c3e002100d00902032814144615541c3c0040f6064510440300900003403501c800500c0302d5030309480b448008444000d00445840d240394041203030303403047d07094043e80304001042d94400c105650b001030044552000031030392210000c1c0f6003c1c102c00300480c510986ea00202e01080c44561103803080c20110781841d6a0100d114007507035aa035004042600c0d0880c15552160b0300c69500000400441032501d4480d94001802001c504000341061440c0c0c02c2181040600002040803071000909040c0441002c60016070740c0e100e51002902c3d611030407121603014010100000181031304900e03100c02003180b00c6900e00880380203000494039441d1404443e84584c285840a07c1480e081c4203102e040328a00303080400c860360020181c0c028442071a800a0001c43d103618050002c103601c062002d40290610300154140144900415240c0a030340c000d040c1009640d200288103403881d0304442c0d008240c8000c4404000e2100003502d000c0b04525030b580c00118070f52 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 210089442 1250 210088192 210088199
    0xb15130e01060507200307030203071e05011404030305030a0b090405070501080c0c0303130203190c08210909040804150503060906030303090d080a020f03130203010b030d1b08041203020607020601 86
    0x54013103442d507580c45982101d0b10b100c0c0b55103250104c3c8541c0c1e001074051241410200040e10308009403c084c22403407480ba144c51820070899001a2100d0304858108400c20300390103101c2020800392402e072036160803c40c0d160758618042d10014100c410a2a40c0081d0340000d01c0240540030078001d01f55182030360342043c1d982d911503010f0034901c1071680c1c500b055441040001c4046e41001c02c503003052440202501e107001c1d120f00c9805d0006d208428159603410350a0401c02c052441008240c0a6000004c3c2c00e8000b540f203c0080c0324980038504d0142c1c0201c6440c00001c00b00321a0f4012100644244001100402e80422004100d6001159420300440300300380071408618000003600d114400d008000c1c91035000902e0103c035421006040903062580070f10845090003c1d013005548680c005c23050072020304802e40109825608810000d5000e1381160000183d0254800c0c4258041d1968820030b20841020380740089281c840c0d64071030f118841d5840424000c05030b0100f82a070042d0059070031200e4998a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 210090692 1250 210089442 210089447
    0x9090106030c050403080310030b18010b01170a0b01230702030c09010b03061e060a08090c010804080a0f02030409020d060e160c060b0409061b110102030f06040b15130e0106 76
    0x14000740b076001080003031000b04006002c8100641d44208440180740b22141c0d603035034035445c941c0151422a80d05c0460308010000610034422002007210910f084000758006082600111001034400c0c0f49458a900c1c00380156400b489480c1413252048851540981c104e000228464100e010708902c2030244100d40d07141031512080305810781b4164400c1c1480d6489000c10465280c8034640c03c0c0c01076026003541d40d0483d56409003d081c0c89400d41e150f00300d1514008402314101503e224855060060b9101488007154040303059a030410b2150421031500a10210140d28500495100b2000c89000040c02c0305805140d80110f02200c20b59584410203485511544404044190301d01c0e0002e15143c0040700031414a4001d0b0020880c06840000d940881d43c5070101950102850722655020201c09418441d030b015280080d0515840001c50660408818000c0c0a890160000d881140c64000d260100c1c2e40307869444c01c0034220040071039904d085164071400c00005a218815541c020000001007650 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 210091942 1250 210090692 210090701
    0x50705210a0210090c0902090a030f0b01050405070201090f03030b061b030a03050603210f09130c35090319080601090909081b01060f08011a04060e0f070201020f0406050909010603 79
    0x96005203401700090500c042c10000750440600c00d03511823140300c0000003142d00c542115007418011055002950f0612062000356031000c0d0145085a15151900300410814440301c000300b5403500e4082aa20741d00c1d000502c4a00a52010035039078950f0b008492034a880000c01400036000644050106940c0c0c40304140c0c4403250814180d40740400300854285c1c00d1941c50050130041032b840f062074148104140450201444a09080502c643c2c40c010b072605290040b41c100f03e825020503c480484190f4400c6005402c0c004429845403002c0c0004078002640c217209071843d484902c07500c90309013481c0280040104d40182c4250380440c00c0c5080204042030346025050300b140d001140b4604d0301c4107268413001850004102200a550381d004003103a1802040704140050040d5030002c1018031260300894485280842140d02c910300c0c00c45d081050303145c2180702507480f41e201c40458040384e8030701c00c06a0292003540034070100140e000030007181060b041b8002e4081180152602042030b81c03641e405800720b4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 210093192 1250 210091942 210091961
    0x103050708033109021b10060510080c0f0313141212070207080319090b16120c06110316030e030f130e0a0207210c0201050705210a0210 60
    0x2240302110008510250f9009000c040b03c00910901c180e503d50350742c02245c0283c0d070b0303000f061940c0000b440c84a1408010f0440d2250380c0e8901040454034260000b1801e22440343e1000c18407100d4400507039035a60b81d80c10f6030340c40e06076846503507500d00d8580510b8844091386401266205c000202c044840328000071006040c20a00e00c083c0d10b40301052049518026000b88a41d00b10f1280c4040811080d009002601051900703801c035460000c0300301d20103419503240390441e20a5103810701040d18036441da202c480700d03000c0e00b1451010f00050041c00c22100543c0c0110b01401041c2800700307440300404281c000318811310801c10b8020048917002e030200c2c00c3c1c0d1070844098805500c1480140e0340704008900401021074400c41d00c3c0d4515550345656901c040c0b003215410303c6c4603030120301c5c3c0c414040914214031041c46508801040c1403004503000d0a07075807030020080c1c100400030908500300401080604407020f00744911040300c0030f2862001c034540c0d001d02003450042c0034054152082507044d0080740c041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 210094442 1250 210093192 210093217
    0x50121111c02150c060a24080304061b0206030c1303060603080d05090a0c0e060a030b010b090307080304060909020d271211030702040c1b060f0506090103020904020d02040b100206010305070803 85
    0x10703260040b50744003910a0b4546241e03401d4170501210300e000030100452001b23104001c0550b85551800c60098642e481da00135001c4003400d4040300c03100581e105000c0720707802151010501e4a84a80f40383c103060040041c3c00050609140c02404028405036901800800c0402c520500c850303a41e52212507115a1803080c0108001d131800b40a00202c540048251343c813607000703405009020741c2c9403509204450280c0c0460950080020b00c10307014203050040300003034194400150715151a0000080550032240f045d40c1005a0114450004c05075580009046801c0e4040d49032100340e180710307402c60840b407040b011280070440700c0314104158010410300403488120400b46041401c55004c1c440940600d1295078108038064421315845400b400d0480348007030007007800080424443c9402c85c111800640220305c511080001000140d440240c080d51155059a400320f040e500d40c03003c036010381841c101700342e8040c0e544000f000070140d00250b04e41c101d0303000d482101e40480c2e0700c03420140c8030711507498001384 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 210095692 1250 210094442 210094453
    0x9060f080a0212100204090e10021c0b060715050a05100f060302070c09050c0a140909010302040e0c0603011403060c0a0509091b13140103050121111c02150c 69
    0x5441c3c04001c541c0b60a00341e0003030f0f400301c3c102044460101c1e030254100c40c80c500c2e030b03d140351044200104a600c03803c2c12469030461410403041c141c500041c0302948010802615000c8601d030715140c80301a04d00c002d6100c201c69105504018000c4e020b00401c6440d04081c0b45000002041e00b405080704404640c20344046000990902d0b4003100a0360151708c0c10b941e5101003010005501066100d0284102e4001744940d440d495104801050780c887d60380f0790000143c045c01450b54550350449500d044030307811500003c001000100c030904016044022a0f40400e02100010301503204048564003101e0840030f0302c3c1e00782d40d400184280c1e4060036002c03c00140c0b0a100d440c8090401002041d00030340c00340083c8242480c030581400c0190310010303442c010781c03050650800480368000b050f05564842400c00380220760400c40c0100b1032001110b00c1010b11461072000038144680420561b40d405005043c03031803007401c1017070600100390460f10121b0048a0411003a22110803410903205501d014901400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 210096942 1250 210095692 210095713
    0x90504020a050f0c2404020319260307020705030610140a0e04031706011e03021b0a1407120819030e0a0c081207030507150e070b0409060f08 62
    0x203400040c14101400410488281c0c0043c80e20080d046004c03140004001c00405503400343e044407001842c000d03508070202c0c2804010781d004180110032444549160402d0600f90038440024654003109420b1102c1c1e41800070a49042100190b00c1900e40360200c5003c5569402415030311101112910701180d030241c014491208400f04c950080040141003904440d10340c018403985150540e000c8001c00d0800c0742500c111192035180c140d0040302420a03d403007522548600c21a0314010711032400301039000813000c1d150441540c0001c4610480011910000301c07925040c2c400b40140203210700705228218000031209000740b00b0a1b05141d20910341c90600c1408540c1d007100303c1003154420705240d1103000080e40c4480420000001c2401080c11514403031404c01044d0501c42c11500d203908248007004500040b94020040302c036203507800001e000900d0449150b01e8020102c1e4070b04484540940302c030014108150030043e00c162000884208061540c407003100c020499a40718900c0c00d40c10481d04203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 210098192 1250 210096942 210096949
    0x402011824050f120a050606030103030c0f050106171e0105240312030a0911010302030705090f0f09010602030a09050303040311040509120c030706110a05070212070b0304060506011e0905 82
    0x100d1000c9240c01c1040c100000305503c128150014030384035228840c0c1c0380810a4100d0113000e0710790410130603103034a441c55056072001001c14100e9a80503001c903402040050421409600850083c5041096143c411010703003406a16507503040602c6440425046064803000c03010b1207054020f00d80481c140213121086070b006268002804802c940c580580800081c800c805807005501c61020306600158103c0c40f0f01d05a0700ca22612046c19041510601c10000b0b10741e000342c01c4600302c1c07008031482c0d030042030b01400040a03601e601a000340c0026129000003420b6070004064540c3c545661103c0e204943ca66040c0f643c3d9010342e01c4060601d6a080c59151840c4c00c19500558002001c58144c40b0300b1000f410304910315034088223126400d944005404006d0001d03510480d00c140111403501da01d0708800c10350061403030150b41e6003c3d208002e58100000380c2c00007003040400810940d0309490b100d281c80d04110300201800c03503a2078049a040095200d13440900810280c031203000c5d4490654490424091 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 210099442 1250 210098192 210098249
    0x2090a060c24050601030e06191a0406030308041e0201390305090a051507060513051009060b060309060403081b040e090c010516020f0409080a020604020118 69
    0x2d60b04001408040760400440c400300703901c1640d0484000c9a070b1304041c0001011070b200c01c1e801020580080f001e100044035004800700d0403003200c0a01040708040c20450035010220041c2880d4040e1902c000001016080f52a181c0b1490050340411614201d0201e07040f4a000e01c0c00e0700a000a51300c00c04030980c00410307500c2001800713108804000c03a914200c6c0d610040c803018074007a008140c0120700d02e80f452401c1703030011024140c165103c01c40c50242000d801407600803c0d8008000c40d840751700045600d44c03a14000c11401e03401c001254200c4040b10f1844004118922050b034802e4180a290062810310108481c0186071120003040e4a9995880444407200081d282e0315941008c400c07062075103800c04019001404aa2829410030705100d06d00c246803002d182d80c0c83c0c2c140082441440c42c2d031500318003500315064058030041c100021200005c1c5c010007929030020001ea10204600e20100c0d400502d15100714400e0321144503501da8010b4040c414400c0b44034400000e41604040b070518a00c4110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 210100692 1250 210099442 210099467
    0x705030a020d09050f070905010f051e01020a1a0f070908191103100f060503010603020319081611010305010905060a06140403080307120606030908030103080318010f0605120102090a06 81
    0x8000035110740710754139281020100444111144d00c03003e0240841c4170b003442414010108400c2505c1d07820f01d40000b10700e005503805d82d02c0b41c0a80e0ba100ca0020281d000f809034042036641700c1211004031402c5026900420016107048003c2c8250200255840d40160300c14403c1e41d407944010200d0800000f80c11340c00132698081211030110034042500561070401040400070102040407071f0041c000e0510204a4400c0e03070040e0b02c00c0c1c0c14000c0410140e1400f0a10307034841039000ca610004000c080c1000d09040c4180040d5603003142c4010601410301c048100e45280303031752099038141700750b90303881d03041100760b0340c0948600c0e90021030041d08110782c0c0e0090502c2440341d01c48030222800c043d501c0d00c85420381c0e002291190040341c8095003080c4c020400b8860700f8054100c5040403c410525901c86416a0105000007000d00c41c000020441012000c4a4001c1c1070040400030301c10124612840c401404903807041c80d02810a841c0b0301e2921003011700aa4071702680140c641c1401c0b0b0718000d000c40b100840c4a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 210101942 1250 210100692 210100717
    0xf050103021e130306060b220f030201050f040b03070e09070c030801270f0203070807020706020303040b06030c030a2a080a0f14100501030c06030207050c060d0e1917030705030a02 79
    0x810010010342c1c0e9004040040002914035510f0351823507a141d02100d00c00c40d210a90f0506034410a0119120300740506003542d03028a0001e86807180c0c031200041601c11030b00810b070261004400c11100359485007045ca0011415140d50b0403d0b01c076000c0540e00b9411426008002c01d08110040c00350800c90071900d058041e0301d14078071180c004204603c8089a0700c440c150001160004100401541c1181f00b1035040040b920090048030b01d0800020b403070780800741009080300000d02c0400d400396420010507100f04d10040c03d50700c2820041c6007803113850305000c2502d400e502e180e002516540080900c0c04086038030b0380002d001780c180c19684500c17561040d01c0d401c86081c0780703031407446e0303c068020040710f8401c0001005c000b66550640c102420b4031001580702a0403d4010001c0000140011a051580c25000d6915135140c04101080e40e0141c501240e034548a0b110784950a00e918040c0340c039541c1054001d410040c107580f00d80c0321800e42c511048540001150f400c001081d206401640206020107c0c1d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 210103192 1250 210101942 210101977
    0x30b04171602060a090906030b01080705011b032003030702070807060903050c15160f0c090b060d151509050a0801060b030408090a030b0c03040201030b10020a0314040e100f050103021e 81
    0x1b00d0a0f0411550583c006039010103007600140403515003004050050071017401c240d00804051900d5207015104030f80010100250b2403441d10f105414128803044401d001e4041c1d03078036450550310080d17480410784201c880b98491280006040c42c00b40003500e0649801901a00140c2d822206101100c80c1e00b41000889040c00c0001d01b0310100060580300c80b00e031050080828030f18140c202040d140d090340d048414402d103403007a0700d4007542e03441088400b406051080400c100740341180d10b810101c00d40d80505840015001e040303403413540c00100d02081d07030000c440142e000c907100e2020908031500ca000e0b010544400304041780105184602406440b10001c0c044c00c4100c1d266039440444030800e8803044000c0760080300380700031581c043c080c0a60200007541c04102590081000030343d1840b2046024050009000011601c81d85040c11500a41824401c2c81d60034200307404189500811807080c1801002d00c0d80011423107621900880e000a607a4403460a8020300819001c5041d5001429980303200075030b0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 210104442 1250 210103192 210103199
    0x70504050405120a0f0315120f050f1b190501140f0904020f07060b1e01120908030702070303080c0309060f15040e010213050402132d030b04171602060a09 68
    0x598000d004405131556501040c1200300e03009420313100c0c40c1d6215a2003c250b00002c1c40141001242d0710055508021036200e070420904000b400d12400710381d203405a0044640c0c0901c104038101103828140000e442c8096215000300c001d9409800d54002c0340d0001d004100c0c0044045c1100c8007818280543c000400e2508a1050000e001c980c071510003414148800300321182481003620412206001c10340d0114002451004500129580346072114180503a10309030020000445d80100c1d0159802500c0c150b4070304118901035500d01040c8801c4000400041c00900112049401d40380070300180e1004100da0f443c3d5136000e402d4040000e003141000442074005400541d03482c025240c00301e1200c800107903030b03410400c0e02d403a030408130b1b07049a4080c500410409001d4000109100304448080790517882d03001c0c15416a0b503e1900b800d140a000c1507003002d0100030320440408190203284a039028100c4405450624440c90140e034250170440d50a502021003d41030103c020400c4020750300e030140e800b945 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 210105692 1250 210104442 210104473
    0x30b031c0207090e0f0a080f070605040b0108061f091e0903080901060f08100207030311030403030212070c0b0402090405011514130207020a140a05060a0e21070504050405 75
    0x400300200401644145400c2000b58450312400c0b507040703a008080e0a03082e1204019507640c0903d050003c000c40c0d80011240d544c184548103461540e40d101c0002e000700e0a0074202040d500b00c00380180d10031805084041100c0010326800030013000e4085e00030003030951400001400401e04680c400c14070028180341010340c035103a4030518078040d11984840701a820700100d11421203125400004000101c25000c0c02541000220301c4c4d1500509440969180c00c40c4c0350440240071260b00124699001206000c101038264020f08184200309407410310326a80c1035021641c1007a0301d00050111041d1101080150501e081003643c018001c100100b00c4501503501300d024291240d104c040a4140300030b41800a140030040b4200d400001c0b8000d5080c8075071500041d11121084c8240700303c410004141c00c03015240ca84507107009050060a16450f41c40d003401c05404458105032142c402c0707501c01203d811070305a40c2c100b0340f6010303074923001070401d00d04100620000300070207002900c941c82481041c080d040c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 210106942 1250 210105692 210105733
    0x1401031e02130e0c0105031e0c07021f030b0105090607062a020c011115010608180106060e0f18070f1b05070503070801060b07081804050a0222050d03030b03 69
    0x4021900c0014480c007081c20709418200f4000c1145e04000c030400502c84500d1514601091001030480703c0d40740381e2200e1034401709511511030001c0d044820030700390003a91106481c07443c0d5590160348084c401000f08000444080c0302d0042c0d600d0340302c1802d1010001080c4903500040c100b012010b1034000000b28031040d00982040446008010b074040c00d8040c06c25680550541070304102d0380003c00c40c005124002c1180341e02c05000340c4003006124000242d801c3c0310309140300100c10f095030080042e180c913404010625124040028003541025004805504240f40c03206601c0c042446140000e0316120740466034900810700710000c000030107064601d89007103110324881a80c454030050061074502018113041180c83d81c404451a4076012007006820008000c68086c00d41c03200c0441c1c1d54440f03012003d003032140340a149941251801301000046c49869004041c140300072008803680c100021a500307400c1115000c2e1980003000c6441c0c58000034000d400c0800c207018010305030307804000381025100d81103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 210108192 1250 210106942 210106969
    0x7170d06080c0f030102070809011116030b060406062c01090512010902010f05131a071b0f1202031005090f1002070b240108090709020c03040f091401031e02 69
    0x581140c02c0c26015072401900d00d001000f01038000758200a22525110b001d8052449154144042104503101040c000d010340c0c141c20301410301c4a4180b43d1641001120004100c1e8042d014a00d041d50204245024503801c4140702c044c8240700f48142d010300301960801e081840b9290604c220740801140a83e5160900d00d2403900000001030300e402c19000042080140250b20010302c60100521400030078801c50f00c03002e0310503568038882031306861031001e8214464040d000c0c001007a00d4510740c0802010000500481c1d038000c0400e400182c44514000b441000074038002d50580c0312544002c540d103019000b0f16440701451b01900e14804480380014140888000c1000440b603001459204011800b07940c00e0300004003202c0c0041d0001e80c8655a01f140f0500ca95440c1802060800141480f80c100520400750810400541d21644aa154169079400c43d000707503d1100c803551000300f031244982c0b1450280190380100060300381d1854507100520050400558080ba031001204070150b1606078440912 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 210109442 1250 210108192 210108209
    0x709033c0302010219110d0516020a08060714040f210501020c0607090e0f01050405060a210605010b03070207031e02030a2906031b030a12080910050105010507170d06 73
    0x154802c02c1d0680d08131a8480c005101403140100c0806c05884000483d9440140b06080880d61151206ca02d10f05094001200a40c4100d0342480800c180c58045510f038001c0142d51074420390364215102c0150701d0700440c0035a03241000d04060801500108070340308210b0f80512143d0807400304003619201c0c01e82c1d0020103451b24650011090052282c1d010b04460001e010711143e070741c00c0e414000c40200c1869410b201c0c0912603501d99010079859a103101c41c11000304070300171003000040100004022034031100d50703054581c50b242100002d0710a6450081300d119407143c0c0d01500185d811a1754036503000c07070814203145002c00038099800040c0c07810081c0c01545401610818201d03038103218683e1301001c0b083d0f001d0750007005100034010252800a05442d000b5400b8030400006450304010030319001c00c500f405000c0540c0800d07000381064102c1d840301e0041e220101500c260016041c3c2c0141a41e00170300c145400a0010018000802c241e4008200200070320381d0f4a900e0540c40c0d948090a888141c0c01440d42c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 210110692 1250 210109442 210109447
    0x27030c06081005061204030302120a0506030c041a100908010513060b040b03100b040b040f051012050a02101e020717070b0f090a03120807080709033c03020102 70
    0x240e1500101001d5010442e041d20312402410000440e0060185082d030482480000c00454100343c02601500d51400303514000302c2040c607008020501030b203c10f58510340a03020702c1c240c65603103013068080d26025100f54aa022019445141400302140d0798807160710820114800101e042c030401c0c06210b02800c000c2074802e1900701c0c84d04144049820622000341700300e00d0310902e0043c41d14046002d01000400d17181c000344206171040490081c2c000b000a0300e610a10f0141c0c81038a00300c81340e000701d000712500814410340c1c41c1ca41b07031038a01040f00d40f9000f801d150322030403141006140030160703403d10174082c2c60002d018041001100c007144000d84000005078000000a000c00002c0900792884045c54000a160144c40c0009020544c81a07030614128103d0005502d005034130780b192988020765000f24035003550b4030000002007803108181e500b071000442040101e8181841104484180c03a000454140e040c01d8142c60005d010001d03012881c0d03401c003409442002c0955115120004500903000584e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 210111942 1250 210110692 210110699
    0xb1621090c06111510080f0604060608030703081b25020102100b0609270c0d0f02090108070c020301090203060705070b0108030a0f122007110d110127030c 68
    0x407412a0550060820440d8441440000c144001200c4003003805100c0501c01c2512000c2e01404071204c2a08445440d20580b003034003101e00000115148564000e1408021458071021603541346d20074208041c0000716040040b030b019a12112619082d2008485024501406101c1c510004030055040b840e413440c1c41005030095580510410840b024802c104104110a500002e2103034001d0140320f40c002c40840140709108440d80220420302d00190206c20568584041c071551141d01005500050508003185504501c9075402521803041058541c20104c1e42c0d044000c94804501d2042641d00d503480740c0401e005a1428001607004d106241e031400e0b5500c03090306284c1400c19042c1e0089845034401c02c43c00c10915801601044580e82d1890b14680c075420441e0828090003200c00380b0303103a94520041f40210690810000c0c001c0300d1083c4c42c4035074514444020405940c0c1c604034003414892604941c007034998800c5440b100180c50f08a00e0303200400c0ea0300d4500200c0e440c29001110310203c200703c00d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 210113192 1250 210111942 210111953
    0x1a07030503070306210203160f17100e0c030d05030907090209061b030d0b030a0c09051008010f060e06010206060f060307050418020705070e090a080a05070501020c01050a060b04030b162109 83
    0xc81c2c2d2040ea08c481211900c4c81c1c04192036258940f0f00c18000304510020405c9603541c0144031508507500312034070501040e001d01140701d4659000c100903078820700c075001400003124001c0040e81e01c10309954001e410361500e440c1011307003c1e520014640382d10480030880200200683c541c24400e03220b184000b1520f80010505003030403910b40c41c41c0b25100364442940d50b4001750401c2c40101c15945103040100b41515000301e60310351480c5c7d82d0040001035082c40708000c0c16084035400041200c016027015010390700c5250042e61203500075542c035a008652148100c43d5810803c0055412440a142003031070b0a03520200142c90007201e80c400700d41d49400140090900070308000f42c1018180c59a0b0300d900a0078020044c40d52540000780c028418800820240340c2036000d44203454131a40c000000755910035000c440307103000380000c66040d01664a400d001180b120845401d0f202940d074090090b0f10141c0340c9680103500c9045140009080008600d20f10034041070500790810941802000400c1c00110352805 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 210114442 1250 210113192 210113203
    0x40e040615120c09090602070b130506161b0203032205120d02250b030103150e01060b0445050609100603050402010c050105100801061a07030503070306210203 70
    0xc02d818140600041912402c8250450380c0240d00003400b40a145402c0020380100903016008496a20400581d6001c08505031030316445841503030b0702c40c0d884005000e0300c0241034800700001000c9645a4000d001c0c4d1050008080380010116420501107000810413482e03203142d80c0b60546400030b810406810056507003244840b4010141101d003049c060029580c40d80030607501001e1403643d018034070300c6c6084074526001c0c00c580300001e96a980c40c2e0070700c4d4442d910402010390005282424402013500188128000d4819540c80c41d0310303061402e42884525000400514214000c40d21844803014110040c1031a46003800c801964140182140b1404c4800c02011240070345070341000c00c01e50f41f1007000014141c400c1420000f03050b0301d0784e00040358419030a410040c85907182c10144001080107400e1401158030701c00003072008a84503080802552440c0c04080b142940603ca1480040d0140c0003441d0722469501c0c000400940d07418480c001001350a00c01016120004c0026055082c180403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 210115692 1250 210114442 210114449
    0x80a1b23040e190e2b03090201020606040c0905040501060e01121401090c0c050f0c102102030612010603080a1407021f030e0f25031e0602040e040615 66
    0x42060500785404901c1c5802c03040100320007081015400340109441041c2d201d01850b18049040b0b6101a030102d821540742c680c2d904070200c0007110300600800540c802e01641004607410390140c50f03191942401c0c0400344c45480c61541c2480151800440c0c2900c2d98070445009080980d124142c17111581c0c000b500b00900c118000d0401030500b00c03d1180e080411800504440000c00002000843c440c0225081030944e00020a03501410300c40034000400080c1171141041c1c01c03541a501e0056120381603034000d03420348086903c0d20740d07202610380d10748885c2e01440d4080009801c0102011109180030f084900700c3d08222900c1c030010410b82601c4c0d40c013408510110340009500b502d03050850f00041c801c050001d000c1111551080c201c841c145105c2e82203010384400101c02c9403131118590600e40e80701d4000740c00b0f18070010004070351040102403d9404408507a000401e49030000c44484c0c0001403c41c0c118401c0d243d903071b000c000008032010701c11429403041d401802c0001d03030000201c4074042c09288503813 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 210116942 1250 210115692 210115757
    0x90f08070204110f040501231303050118050a1103071205060118050106021b030102040b04030c03020909011530050303420f03030f07150912080a1b 65
    0x4810004c1030001c80c0c080d00c03400d003000d401c035140564150300011624030b64440c0d0000d0210303804403090a111407100aa9100703400078000b100d0b181180700c0b00c0240c1c0440c050020383c0700c0d880d840e000c244400868000550045c00f5038a2154a402e80391420401200048034039500c2840100500915003030301180d0303013001020610243d450401d00a6990080c120800d420840c58004c4840640d804d504490003400c0c0b040da06038485943e81042c01400000e84000da004141190000b1400041840380007410240096400701c01c5051050200000701418905041800800e200e084407610014145004070f2052004596920348042180404e4181381c101010703d0304103007490810b59200d4444800b00740030a000016000102c880001c0351108240121a0180800103240d0030a0541000500d40240a00724440021302508922000c55080281c050200f034007008800110511070302650341c110800c00004541c013402086080c081c000d807001980045100c440358440303500c1520280388101d05541 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 210118192 1250 210116942 210116947
    0x10806090106080616030509010f0c020d14030417070507055113150903171206040207060f050a0507090501080103081e1b030307091401020c090a090f0807020411 71
    0x40070300c41c17020004201c0b0501819141c00025058807025480305040324000b080a1207441c42101d030103510740000d442090000f40c142c040c90380074844418101da0280ba8014029214041c1c943c51542054001e500d04440c5400744440020705980c454680d009074070780440034428590f2003d030303e100c8050b000d04034890780508001c140d9007202c201c4c01c03060b0448036072211426a48050010300380d00240b0464120106403240b0848490b0076583c000300300401e592081c0074217800d10000700404c3c030042c0941d003481c4903454604400941d403410640c019100492007818041400c8251952140941c1c0003120f01030125940c1d4001c002e48130781c1c0054800020007081c202107001e035040d03880d02501c0d88115201e0071400d00b100582e03100b1480d00002211303003c008214904004100e05000c042d129402541c00c000015136082010507800d119960680c41c506050300100340c1d00e00d40409110381c01c00700421866030b00c1d6640e00d07148080740d0342100003840b81c0d02c603244040d645e5440e441084216074031803001c02c035040c82c103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 210119442 1250 210118192 210118201
    0xc06140604180215090f1201051609030f030f0e180f060105121b0909240a06080f180a0305040302130506030d080a1d030307030605030313031401090503030108060901060806 76
    0x4240e044104c96400081c01503031104180d0200750103c19110340c0b030780c103c2200000c29200075810350101d4001d00050b41c1c54030038849007140840d900790345800080e0402c03040c40d940b040024018044807480450900344210740c0300c06030b400030b0400118034080c12207090000302000b80c00314000041507408842400c1c031908058040c10044840d0600520783c0080c06112050082e61850560a031407411000a002ca402403600110300200410b0940010b0ba00340c0e00b054002d019807030441c46080c140c030754503954039050f591407003400d001201029002000d040b00391200106804010700c0222821070190312140c2d6101e00c2d41c41030005001c80c91542030700441c80d100502050740d60100e100d84000b1030a00d05144d05803210550103000f09100701501c617084031418084e41803c40c01202440c452038240d1000c00040383e48800345900d910809040001045995405100240b11041c08404031040c1c0e01c000913044070a5540e442ca10350003030300b25841541c400003c100500c042401403c000c0c001c220080c10803804d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 210120692 1250 210119442 210119449
    0x30a14010605071b12080d090f120305090d08070e0d0c06030606140f0301060c080c01060f081009151a04180c080a03050d0b061303030503180c030601090207030c061406041802 77
    0x10305c010010640756002032445882c07100c40c0c2049001e150444520801c4c000185402d4102d02c0880ca0b4a0000c80d0500001901e03213000403c2a07000072400c0c2d140c40c0350303039994030344111405004428240c1d44840b02000180100d581070b4a510003520698500180d040c5c1090400b0b440042a00b085409170b1004000d9142c0080c540c41c2036030304554450070241e0700c400080c900100343e0301502e1403003015580f030000002a9003840d1082501100d80f100d05550100200c13002e01400e03556443e101a0035589001c509072584403c0d984910360b1046400130346401d0b215080b0000d01540c40300b4004281c90001d1250120500c89207154a83c010010140105441e101c2590080d15900403207041c2c110503030355612170200648901d000c440c0e2802c1c618510106560322032401a186401c00e032100300079a14280300131092400000b41f2010700c0c502c018002c0510340e1030200114046c0d880b0020880c204003041020900040460080225468450225119034038040c01408210380d04c40c3c0c2c5c01c2003500704410061003d600c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 210121942 1250 210120692 210120719
    0x914010f03022202030c040306050603010203040c052103030f010e1806010302010e040b03010e1b030f060c03040c1509140418141f090c060c0305040902030a14010605071b 75
    0x2607041d40d1605a41050443c01e411504100703085940c118000410002420ba8940003001501c2c4102000c102d1307600c0d0001418200d000442e8020310201c50b4036010300c16031a05400340f0080300c4081114084440701010300b03605503001900e154002c500844014410b400000007d141e002c0b00f005a0700380c0e0311054206c401d548400c1840701a052144600320f40c1c0c07a985854020040c002e070090024802c0008504a5941c2c1d00103074084944806a0710419141d00c1c6404540360000641000c0105099140d030034030303081c4030b50020b041243c428050f0800003070f500c07603d40004c2018821704e481e00d143d15842d01c100410441c4140002c107100d50b1500700d9500203014400d004840c030035040404d08500c6800c200318603107060110307545001c00f000090391140111000340c211201c0c0c1ca20800c02c08888650b9548282c548a004a800501240050000b4054110a03074051540000341950102e0140c4104d91049000c90083c7c1041d800a0000900c103400d00c469004409142c401c0c1903800c144142c546001c400501c0e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 210123192 1250 210121942 210121949
    0x819060506010507020d08031f0506090603090f0604140601060207030c1202210d030e01110405100e0a0f050315150418050102030124020106050102060406050618040c0914010f 77
    0x5a940000c07610300d921403801c0d5928564050403002282505081c0a5220381003210050701050041c100021810316a420180c00ca82001e0100d43c1800c40c044100001600018003204a5100f07a039a07e0510100070400c035400b0381d011340850f4900c2070720340d00300030f00b0450141c020340d048d540044010800200a225050200c3d00e1610007240011018800502d1501c0e81c41c0c44113002c042c006042c440c0520007c58006010005510304000310300d0f0200443c0d0030b1328402e02030003003101828001000a420022804030540300149443c00b984100c1200040700c0080d283c00c01808401101d00034005424100000006140787c46821680c0d4035101c910100c50f03001452060780180d4503511034134402c3c07451400014a1961100095403690b03100d61400c0d04c600114060081101100e45200c50303c0e50040c4903130b40035502c060b4040c2030a40e540303031103501c013411015114075001705040b94414200250802081d010f148034290b682e40c0d0903c0d0110940985542d0b8800c0c00640820360010000100200014005c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 210124442 1250 210123192 210123203
    0x303090a0f15050109060807060912170d020a0c021203030f07051b0312040314030408031506070605160807111504050114040501150f23040e1b09010819 67
    0x642803511690290b240226801820f040600209001d65250494000c0c4c5103038408a9883c00c0d654a02200c9400c01d620558404121541c1000c0c003042c0038030140d000b9010f22010b071074546030300084620100c1e0711005403030000400c0c42c41c00404500e010b030040755000034103d00540c19820201c070003284501011f03081200344440010545100c3c881c5001c4210103820318019a519060710612041c00d4040440d021000100590128002403040400b5240215080300285041d0b0350307005640c40d00441e80f071101c5640103000340300420015001d80919441514030003904e03d007400c03562002030400e01c03000d4500e83c00d01480c2d240328032000c0b800083c035113086901d240d844082174849051460040c55090760280d0f80100e00001c2100f032101c1500180403051205400c5036207503580d00440c0012102c0d501807840c0d81c2081a91400b100d1000c054440c6101c1e03001000003a0061800100d145017124080700a10394a010601a600c3c0c2d2414540745801008050094070318016125241c251500e61000024030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 210125692 1250 210124442 210124463
    0x1b03100b030d0f0315080c240307050c0c1002100b030712020409060e060f0709080105160309020f190e010b091f02190c030605091b040c0522170303090a 67
    0x103548241c0009440d900d0445a0407a1a91905000c07070300d0b0030b0384445541c0100c00064008d03200c0910403480000c44140910b0441c1981c4031240b085509501c81d05543c0e9440c4070b103e6802c2525502c00c000719900c0c0c100d640007440e1307482d2180b4a840c155070141d004e1500c81d030420780c0d08005a407035445c011629260304580002d0039083d146400300003003080c812140881e1207081c0802010f14241c9544600440e02600c3d2440360b107036030341540d0342624001c80783c01013203010100b04218298000d4000b641d44620081441c01c400d003019001c91141c00010384400d151009490301002601d01003810706000d4070911035494a00359170400413802010b0300107151061040d503013882c844443d10900002e4a071f001c0d0715141d10088011428601000700e4540001c0e00d0940ca0400842c400720340008908141801c01e14640d24103604c400c1c1080018592501c41c0414003008101c4803600728001800042c0b40a04884884900c42c240740c2d481c800040d410311407c0442c3e208006000117138000040041300550300614062 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 210126942 1250 210125692 210125717
    0x406150816050a0e120a08040501110d020c0f030102070515150402030f070c170a0807081e0619090e0f06010e04110603040204110304060b0f03070b03010b0a0207081b03100b030d 78
    0x10f141701006650210103004d4a03035124100800071004004850090742e44030861800300c1c0c2416112800041902c4c0503900469140104d4149250202d1065400800060601c00140c40b0503003407030000019050021040000c005581020406640440704140c0d003c44c194545084008440755001e05201e0601003408642c2c000c10a2024042ca100b400c0d280615803a9107182d4030140c1064000d81e000c8020900d42c10000700150303c011440c2041003100b000b1080035440e8501031203000c440d04800303907070415105100480c2105080c000c502588104400514801401c2d50010303040c40c1c01a001505694040d50610001c1407401012201e00d507001c803166607032074459200043c01049030b200480400580402088184041c4c0da1000c1c0c0080c00550303207030540502130300c101900e0390294000c0d02c0220300300380b00610812081c1000740600d4140ca00403160082d031a10109854140154000c9550b01c0c0150b40c04046030906208001c200b02c1c403480c041c0300d4240d80c0340000c0d0300d43e04140e10b10400c010300c400401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 210128192 1250 210126942 210126949
    0xf0801062c030a020a03110406050d02030a0f1401090c0503010c02060f0703241e090203070c03030e0705030f071701090c060804050c09012c0f04020108040503090406150816050a0e 79
    0xc401e0fa5401400009965a03030310704a029101d641407010f114524010002520782030001c0b80561455004000c0d000d04d00c02552134514036014010207a61b0010440c43c0c0c0c0e10522400d12030400203a00807481c8180f00d51418040609541d0240002021900b009040c8071580518079074650b0060540c1c2401304908500b914240100340c3c10160f5107903054848600002c3e911280d03e081031400350740d4001118200c2e11510240f06130722060b101c5400185049070b860b00480c0c4a64000348294800c00705540c491590b0300d0001e854800c0e00114148950000e001c10040e11802030b42d44002544a04001d0029840c0d503107804440100a21a000038081514000703810400144612950071400900200c003e503129010f007441d28040381d540e0342c0e42d007a440c0316019480c44107030035441c41400b424598a885175110b07801161750702c0c00500100c642d44018804000c50343e030703140034000141c00d410014100c20016410300601c6088003030544d22040715124200f45070103501000b05c800903165030038800319216030b00d80032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 210129442 1250 210128192 210128203
    0x302120703020918010906020a050304140d02030307051305062803050108030703031d010c210603020604120302100e0303150603100902030601050c07080c0102060709241e0f0801062c03 81
    0x101f086200082d440055a0044041c6005074051107009404600c0e0f580c0d1a503035280070800c45000b690060002440c55841103006002c4114241181d002041d69840801e40c07640050b2100355001603150707081c0c172514003040a56114000545004d002e42d501d04104c0c171346ca84c459040302404268907140c05035030302003c501030004c185c90404000c2001080c0110018103443c0c07256045080c0041c1242440c000030701502a01c015285c0060076540760070719080000d140101c8069045066009a95035410f44070140c1c490304002403c000c0c09550350b85007090b03500407003175280f40302c541c03089000f40103103c000d405440d03c3c403040e0342039680016601e4450800680315401605855400c41c03051041c040352032400030401c0c040c00402030302200c885481e001c900f501c061619000d41c41440d001050b07881c809800d00944030041d01c0c2d0b6401d02003540444103140a01d2050035201e084045410010034120669100780d00500400061409060511803102d10001a00036684820f0340140c50800b0180b41d540c09110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 210130692 1250 210129442 210129461
    0xd052d07030c050f04180f140d141308160518161112161b08030a080415020301150f020f03040e0910050702150601020a0804090f09050d0207030212070302091801 71
    0x4090030f06c410310f8542004450780c0300c00d003200d9405c035200455106c1384002526002c01102c42e20380120f00d20504210016580000b00c0080c1c280007a40c4000401005c1032000319a019101c51042c0069030070300c410310002c6620081c1c10200003600c00e04001d000e072401220380c20809881e2034104491800e000525241409110120800040014004028244c240030b03042c88203100704020100341c0180e40319004172165038070070242140c10420404182d40d205031592a445407103180c901e04480c401900030401c9800036008064000d10300042040615003020207842c1c0b00900703100602c5200c00d130328883c076240d00452044034075403a490f401080c803280090010070a00d00c15110108000e01d48080003d58602007164003001407020a00402c6c92540302042003d0850b410010103460586009001002019800c1c41c0444441e41d030800074000900500c0001c04056440e030003800e64904500400c50b425001002054859228440800042e00c82e59002540a02000d200c0754199041c2031400d40541403861 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 210131942 1250 210130692 210130721
    0x3030c020f060d090605011e0e180303070c140a1707020103060902070c03020a150215060103020c011a010201060e10090b0607060e0106030308330d052d07030c050f04 73
    0xb46248040300544c07041c480f050243c4414000350f6692550040d0f16041f01440180105c074a410500c0f84500b512030440c1c1007003404009610b0080d25008482c21900103550900c0011886001d10050042e000204842c421515016083c5010ba0390303110310500c900f08601400c102d1000c6540015a03020790300c0b44004052078a400c0d5550940e81c509400041c000d80412440340b07554103804640b521511403603022124041d00144455108203c81c002d85074002000281010340811a141c003c282c04c0c003c20f1070420b01ca42490a1218802d000a42034070b52540140e20302c191410100850391a021407031004413018000000399402e204404140648960301000d0502400d0284036100004150b08c02021640aa40d039402c5645410300b40752982101c0810014003108207090100d028200d0420405828000a210070075030031041d0340c0d0b507090039004000d07070003200380c281820007020340d0b0440c0d4402c940d50140090025241035a4884030400307881e00a0501480c40010300709082d0320f07540d000c0d446004208 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 210133192 1250 210131942 210131947
    0x19181505040803040e01030620090910080d0f1d030c090a180b071b02031b030304170622020913030302070812040201020f01180f1a07050403050c03030307050403030c020f06 76
    0x106400e42c1184401c0c80111034089c0313407000c00c94200f0740e1044c0711a45100e03070102403860184003804004007410003600880314401e14500004480f43c2c10001e41d0019002c545550445401c0e14034041c240c1e1801e0411f0194200a94104c0d443c56500407039004440343e41282c46800c00d89a240d01e800c02080031640d07584c07400c03012100303800070310400031103ca102c0d544070f80d110540c0d5401141c000801c000065002505079001312202c0000c0c00486000503d0804050102c900385a40c84440711a44403018460012a8011005000900031200c00c441d440d9401018058041c1c00b4583c04558000070003494407080c01c00e146c3e44c0e078042500c40c1e0111960070750049006070301c40d5003140030030030000402c1c2d034100c3c00352042001d03010000720b040c05403200142c403d0001201c2c1e20300e181c444e04107005074040202c0b601c10000e01100b606404c0c00e04154002c1c515517903080d8581d403d6213041450305038445544c0344203500030710801a540794883c0480d01501d51503d0140364519507840403d54284000780c2e110782c4101c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 210134442 1250 210133192 210133199
    0xc080f03071203090c2102060d0605120a030c030809120d02090f1207060f050702030a060605090c0309071404092103150e161704081918150504080304 66
    0x101410078540110610158940095010b90844e03000c030f20010181c0d07034180001c009021022202e8011031101d00c4443e8001c1206a00203801d9a014038684642c0c1c1c0e0b6204010301c400d0400c040d403c50303110400f0340245000c0a4a40f00902641c0280302d004003040b0855000610b4103105100784602c030351240124176200c0044500a40194001407111405418031484407070903407400a00e814040d0740420082d00126050040494590900306545c10a00504000070030050f01c04012340003045025181c001905410300e0100061054040e05a039900042441800060500400c1503800c44144001d520284142000850050440024040c182050480d0070015100299620b4101c01201e50b03002c00ca08400010004404031080c0a01191210400c00064258507401c0d10b00302d0003c45800e29440003540165803041800e0110b408a4441501103409502140a1001001c900c9250b08100f014220a03400100c503901d182d110780c81d03001d0307886100000c4d060b0280c8111800381201c0700c250703540c0b141c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 210135692 1250 210134442 210134473
    0x11060426070507090f18030e011b050d02011118010818010c0e04050702030a050d020307110a0602040602120a08060d140f011a1005071104110d0c031d0309010305040c08 74
    0x34070b2188101e028100000e0208600c5d0328401c40112625a40206071013452640f01111013480180c6c00350b044c0100c983c01c02c805202c0c04103002c0d0321785104000030710341c03041280402400d503040d6101c002a01c1d078040c000080685410305096007041002e2824400a90310864402c0341a411f010203d81c0ca94644a88009010780c059000c0f0711405050303a090100c2d485600381260380c1e104102200f070004005002403449402c0700e400440d00141986800710300381500b44c65107401e04500f007408403801507000a04221580d014071403050180b010368815801c1125055018280001c02001e15200d05108051101003202c0c501261406c40c1c00441101d4600110680942c020f00b654004200c0303031078139022500454070f8030030b00200640410399500c42c28403850759074404410b640c4580c0f2590203611120001880030f039070790240c900da55140b9000b140350f1a09003006404c5030005041440d10714036099000d207001c10000111070205000f803900058031b65403400d1000150000d03030084411802403501083c003150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 210136942 1250 210135692 210135703
    0x60b0d03050304050d050a120f09060204060503100e04020a0b031b0a02070e060d05120c01060305060a06090b0904020303030c090f03070609030308010803090120031608030a0c110604260705 83
    0x103110b88112000f200300c81710150303218055009824001410860709083c1d800d5503400038410b051076a400411507580395a120800c3c1c0e00309820103000240301008200030004002450001443c582203c00d015040036000f003003c6101c203008081101d5000404540c2020459110b4040724010b00c01560b103a501e4007900a480b8222031140f00210946400070580510f0310001d000c101580c081c004001900c240507402c2c0042d00107506200d02d079561000c0000100e0800d0200714071500e0740320380000b04541400d00b100216051400c03901e001305036460401006841c0001200c1c2c02c48014180151614100c000003048004080d04568041c081c00a00062a64104604078284d9102e03440c0d01d1203a80e21007070855502d024600c0f2860000300740311f03518809101c1c81c1003400a04034500065034034000860381038038204658541c040714130070300000c1041030348062031265803001e2526203404601d41100b50324456480c00084d102134001402000104242410b85c0107000c0e41c1c52103066525120046801c1854450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 210138192 1250 210136942 210136951
    0x3120e030301090b091302041107060905010531020105090f15070501051609031104060b0a02070302030c10170604060e07032703020a2d08090a06020c1c060b0d030503 73
    0x641040700d0f42c0458601800117901c41d5a1404141c58100c0a5800304030141423100e100b40c041020801103403001c43c0f094007480d60664003c40002c01c3e241805610074200464100f41c1c01e169140940800445d1900c508a1541494091030400d48601c01c040c00150704400710482968030403000c411840540380d1440203000175074080d00007007000740e644c00c404040c01c5a207503c0850001340340c940d09200042c00c01844510405004e00001041615940700b040241e020034141c03030159010440400441c5410003403000d40503010b5580700d50000d0b03408409043d8161107000f5001100084001903055100d0780c1c0030400a20b80445501d2150403e500b000c2c1c0102000c418100d0340010554000709000005503403200705c2a8540e0041407142c0c0b0a4690080d600d03242c7c0100ea0b0048425852030f040c1d030305580241c01076a0700907061240c0d91140102003002241440c0e10107030554016180361100f654681c0201000d00111183c20030048400b8907028005000c0c801e40507901c488040c0d5007109140e0b0220165104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 210139442 1250 210138192 210138209
    0xc08070b0903060c070317130c05010201110f1b0604030c0311030a1409040f1d070806010b0714160b09120a12050c0c0901030f151803080403120e030301 67
    0xa262111000812442559081c40c0c056103d1070105180c1a0110000c0003c18020314101d210ba0241904140c3c2440c03082d100c2d0320301d200d00400e004040c03000f1205030030001c003001d0008000103103003030700d030100785000f43d88040c0e28982c000f0031a68040c419001c0c4081001182e1029280c2920341403902412101440c0000d400281000003140f10f8054008100c1c0d0b42e80015071605000100c515407292000d510241440f0b40103078640007180d403d00214020580c04a204003a21505c00c243d0b0b0407200d1910300564801302150344803a00400120720808101c6030b2840e042400c040c4105016001549401c88a140201c150b001000c0002001d0f003801c0041e01000108440c00941c4d4810589800d80d90000918080e00b800c1d240c130582017959008000a000c0038080d001a9040d44520f0030024030444000da02c240d510340f6510300150100300700414540d03034041b0f541004000130b4a084510000250000e070000b07050064a00208051500441004001130b81002050004609440b40c0700d849030002c3c81201c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 210140692 1250 210139442 210139453
    0x1215040305190f090302090a0b040603050618010603021807090b0d052d0a020c0a051203091608030a050a050c010e070603050603030a05190e03030a08240d030806120102070c08 77
    0x1000ba1080c00345803500340c55035540b42007903402c5400300502c100c006403401c803c55580303000844280d00d8901800e0002c1d03000b0005010507140c0f1035107400c451060030481f02040d914004090005a843c98070a18500c11918081d40c80740d69082003e859000007600400c04840021802c001040c1c200d820840c4205141c5030416425004118040d60041084803c80015041c400c00500404a2503018103158034000b0304403505c40300a9200d16080030808107985240c0c4400004101005030100100ea4a04000c151180c40c558503005003203840c0c9c00350200c46010000005103d15000d031048065910b06030079a8000c101854448680540e00c01c107900c1000046400c050008510380b801009482c1c0004e01d5807981440c0510030924042c01c0761038400d0103024484103a000040b10b403010005400417020b00d84490303070941850030289240080b00c0d6600c0c031003d138440e00048540e40310001c202c0700c1ca43e0b050415054688440c0c0000d52102c216040c1a1240c1d840803440c0414404c40d400303980105c490080c00d40d003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 210141942 1250 210140692 210140737
    0x3030f03130314041d07120c0314010509040309060e01020705090106020d02011a0102190501060b120f0105030a020d12023405030c0d020d0309090906140a050907051215040305 77
    0xc0783ea00603845518056211039034070700c1003018001c14069100c0303598584207000d00ca07a50710010844900064010003c2c1c0e44e1031700710480f51031010480d400350108507402015482d0541c2c0042c0070260074012030041000aa0324000721364002c1060234003800740200b0314101c1d0740e1556002551400503010002c0103600300f0041d202030030151709500e6207660042c0c1c0942110500e40f01800c00c1c5200540080360603668400c0001007a402c50710241c126641300091500b40f40c02c203082e102144200c183c2103217100b0f800c6400140c0042e0b88000540d42282c1e03000c9404103420440300c074142c0c2800ba98001e841c5400048500105107020001c440720900c404a850b4606001d40302c8041c103a5400e10841c8560308068400c0401e4007520b011058801124464900303503261585038007110b030070303078525074800c03211240c071240715100719006880b029621800501c0c082140b4070342a81d5450b6110381d03a00c10359006051019920040381010721990030400c0a5180741821030402e45002081540940e4002d034543c086105940c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 210143192 1250 210141942 210141977
    0x9030206060414070c03021c020109020a0e010f05010305060d0b01080d0201140f010e04050f030408280201170c12040b011505040f06121d070302030105011d130203030f031303 77
    0x2c09103059441e81a00855540034410745d59441200c2c015404d61290544003003080300000c00340c450b405116400840c3d00e184620500c010340c040c2e90880d00310b02403024014041c4621181110040f6402442d0100c1d940c2c0b54000171401400c2c49107000b41045981200208004a0005403200e10060a50003004403c00e242045c0b0341d0014250340c1ca07250111032400400402d0b0100403402e80040c003880a682d00d10303581c038039018619482139001003160b800c0201c1c6110303207a204a17041500c0d1806d141d0507070b154641d00d81c0001c101001c81805190b0340724002c0c01040b0b89030181005d544184a03000610502c2d800d213800d0084a0003030912401c0c1a0001d1180e005450620500a880407200070010190b00c80307041520941e0707030300d0391080040009507a4842038001d003100c0c0b82086c80040c1400e0702420565003940117150075102e050304016041041011851880959144490741c062105980300c540341107188002401d500c220300000c001c1c200040103104800d0791814000c42441e1081e1240501c42c812708003003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 210144442 1250 210143192 210143201
    0x1e0204080705040c1e0e04050a1103421c051f180f0309050108060303090103090c0902070b09010501121509020f0604080c010818030f0711030d03090302060604 70
    0x1403051a42000c0350400c840e041c1500070000da100c041c01c00300300303a181203e52040c2003000f4000b90030000b440c40c00c2150007400e040c400c0740e801c8190810144001031400e1071588051202805880c150b4000e16041ca4440e4441c100700307201c1c0c002281000c41c0840e0410050320904464008407032150050f80e860b285080c41070b11040e00a141e10402520b108400001011085070a014a00540c240c503040480c01c442480da0001d04e1492080d15460040c0c4460b0800826034031281e04510706101d040d100340b0006507400015660850424600400c20400f907180001c0300e000030fa400149004d002054500801035040c526500c150700c150020000e0361b0b40e8034000c01c1020b1510b0400303840205a140c650200185c00d4010310001d07400a400c2d00c1c401c02e1003d01099495000c1e9209002c41d400203038100380365603801501d683d00b004000c40c1002815503070000e81a128450443c3ea20008903002542c41d04000c00d070ba21068803101d004050320f0603da0b5411020740a441440000c030010300900c000590382d80752074401c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 210145692 1250 210144442 210144449
    0x13080a020d030503090f03191205100b0c01020d020c01020a020607050424051908010503150606180a240306051207090513060504050a03020d02070b0910050c0109061e0204 75
    0x44a812410303a502d0549007640040e261500030700034448003540c0b9100800040c0312032411560f15206a291504000b454100104081c90000742864180105541411000c40581b0011480295a0320f070414942e4028400e04400312086d030f0010404002400701035014000600307480d000e0307401c0f030b958503601121148518050103603900981c030f80640245914010004c0c501d6140e04085181a04140349944022240e1803a040004c007160018440b85c10103200609610024891100140c21300324009a00c0c1e000c0c1510b0b000140840e4406030b48182d07501c01e405002409001c40f2444050001c0200e69216143c68195202083c101480061141001d03041060402c2030f510181415906088295010700000b0f0b1080c40100e4090365840003040701d07807051600540c03040700184101d4240345406810f011452541e5425504810810004400c44600b1100306040440b0034644a00d61500305641c1802240760140007903292200d0760041001e40e03440b6030014000800c501240d07a03081188001680719a01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 210146942 1250 210145692 210145699
    0x100906050d11220305010c091d090120070309060c020d0201080403090f0b0706060504111b031207080a0506031b0105070804050d03090306140709140102012013080a02 73
    0x40014804103950201640650902d0503d103402e0400294038012080c1c0001e00f0350082656104008200091059490381c0e260380c01c00f9914070b0702e00201c4020344200901c0c031a14060244001521a1a081d402071242600d208240522564207510407021601f1001044011842c01440429424000d200741d4805d164024036a201d10020342d8011900780344040d004505209031a400410a4100e9030144d1024207036040e51291256014200002a00e6495008500270303454054a4101c86040500b102c1940c500c40501424400401070703880d14502c80d0b03400040b1510340310030604c020194819085ca003d400ca50905200c240c0722581016194010003030040342d45002101281c0d03295014001078100180501d952504040e607810200303004409881c07013100040d410f01820300c100021072240000301702251443c4001031901080c05455040140116000f0000114801c0926032003500318a00001411580d9840d2400300072030700b03085070020180705a00e83c0040102090150340001d403041074a4009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 210148192 1250 210146942 210146947
    0x4060302060a111f020702090c121308041a041d06060a0e040b10030509061005090406020702040213090c0e030102120a09080c0714090a180215070b010f030210090605 73
    0x5620039a400c081c1d043c1102114060350301c80c50081d0b5003034603803d030700c0900544015030340301054410807203804001021000d880c542803152054a805031110107a100720484500d031082c40c0d840c240103210303000e15800800003d2141c9e0401070043c00c9030b00503104840c0354800c2d1265610040148810380e4000305c03030081d04080b00381725150440d8841c04d8440300300c40c0c001d000090f03070f0700300c2c00e01140540c100040c503200401d464505202c0001c504201030340c0d000c0040c15100780c006081c5000200004c1c0044c1c00135004d00d40215624040d559982d040302c119100c40000f210a19a41d0311a00019114409480740411006940444a03040600840390f140d20398110303412031a501c082134040200a40d07001564440000d205014880d4410442c19014100b20807200101c11403160400503101e02c001c000b6034400f410520740d00082e05070810511283d80d8100d98803a1800344c40d00418810b4011081d000d04504800c0000150800400c100c0c042036a00954200308658120a01940d242440c0e01c50a00065000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 210149442 1250 210148192 210148207
    0x60f0f060a030e0f01020705070b1e03070302120f1506250c1707053109081e040e0703050618040c090c03020903010606030e07050103020c0a06061508060406030206 72
    0x50010288900725041c001401101a01c0c0c82e031518100d100d41520aa40c005100d034103001041044a006201d0b28401a160141c261318640c121010b030b0010b181c49030004000302d0080c43c02034054a031080800d1082007040d19120640d00c00801003640e4640d0048a03c06508800b13003807110403502c90060941110101d1410711001c2c007500c00806078181c4184400c0c84020900f41d039000300d810b820320403620080080500382000c000184000500c805080c0c0102c80c98000014520b660f12810008084000280d021490424000c2c034882e0a65640c880320780005488040750300080070704299140b03038009603132039950030318103400b161005c1e2207140c0d203c20f02194201d1105000300059500c94800d1080b009216591202c61341521004240e40c00440d8000c500d100302e40c00c0134410074006180c030b1715051044004040d44141c0b03032204c60051b01d04040c2c000400d101500001c02c44103850980c400b00c00c01c04990380758402c0710440040c51307a250001c0e086170049401c074540303402088180c0741c0081c000c910740a007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 210150692 1250 210149442 210149449
    0x301060e0906060d05090d14030403080106110f030d0e01050c090a030f050c03030a080f060a1a0702030718090201090e0123030c101211031003080c161805060f0f 71
    0x40104503c0c0e0090040042084419240c016980104065401032170901c003140000303420700480320b003c4403d880302402000301107544843c1c1c090448105042c405440d0940040e501c0c10201040c40c0c02042d0300c40028030010740c1d08943d100200d80d5448400070002511075030400e500d10310a5001560340810043d00c02e00204d0010449100c80603c648103c03401c1c1c0d48010003003411508076107441c90200d2400401c0144000ca4450741d19801402218415100f60405100720b02c21000005025040030011694208540742041558090103188807907042021390030006030050155060100c1c0014105440062040d1000103050306031468890b0051049520803081c8400d81440030a45500d84965800f90550741c903105403205503070005540700283d0141c040780010940f12608880e987c0510100200454a242c4200d80825264407103282c55492201c50b1039145092240306081c07407110611500011156503400d500c24119002020030300540c1d44040420204071620401540c2050031501180304a14 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 210151942 1250 210150692 210150709
    0x201030209060d1401060905010206060307030b060d02090f06030706090f091a090f0a1a01090b09120607020d1404030b0a051f03240b010207120602040918020f03030301060e 76
    0x20041d10b0141498102c460403c240ca03201e001d13851a040c0c940d0018041030b0b5210700b00c8000303040213000070403440c144a4040b03a078499480c0300140240d14888041a11036a8030128524029001010801c540c10071001c90021600c043c0c6036648244100140003510714050170700c040450313099403441ca0201c5d141c00003440103030a0f010101040388050008402e010340c0d919503550702812040540309091f280003503075403044460b5141c0f064003103100000810607503039200c0804415108030040803512400c030304010859410350708d41c5140041c024082004005640019000c01030b18460b55000403000c6460107580c010321540c08007a000d80a8640022b80f6a502c40e003010390400fa400d88045109903884540301e03e1416160000c4520000e8101941910040850391078288013481800708440d124442c0080c1d075447e010b1003101b4030180d5165805040c0000ca0b41070790018030030180140514050313484c0500380c1c0c03a01c1d180204c1c443c040804010b020f03400c001090b03038107031109901d914140003445d42c100a8045c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 210153192 1250 210151942 210151957
    0xa03080307090306020703030f0b011409010e030c10020a1a07090504020702030f030c0312060f06030609040f02031b1002160506070212010f050103050609060601050d270503030702070503010207080702010302 91
    0x8078550b00d0002c0003500c644002c1694038002d5800051100c50860680240d500e8284440c0c100400305070045040100241102c451000900340b0030302401010012074100303807806aa182d448605d040751601140c1e000700c0d003190460710030b010040070742e65020300c0b04950707617004d6030030314000b540038076061082d41415401418214001000c88000c60326240000b440e42e400f040728802242c0010801920f160000b003c07140e08044225500c841c0c50400e030001c5600750200428062040c030040d0f01050a001c3c1c01503c59001d03a401800b5a004601e00010a020090341c4048007030040040c44030003540c00780b0109206400c118050904003034940380108002c155004040309a0f07005c00c10740380ca120700040911170142c2613a040c80c0d0114942d851400d2407030403c54001d1031b0b5405900520304101040c2c0e804012140d00f1040d0103000513810840428101e103a0b84000d84591145c0010103001c0d091010000245201d172840342d007101d80541d03c40b01414280d0040c203800500b9224140039034801580690040c0200c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 210154442 1250 210153192 210153197
    0x60a170705040e1603151a09060d080714010c0f03050f0415110c01091406010b031b0403060c030e01050702210d0b130c020c0906010c06050601090b0a120e0c0a03080307 74
    0x100c85038140d084406442d254806c6600303850100d5400012116405004000440c1100d01020002d4880201c1d5481f03d0060203148a10107408842041080242c05d81e000c0d01d40224001600e0304800300614002d01842e0b006002103826245440c0d0300318420300820340b01d8102c045842e05641c590b03130307a007480580401c0e00c461000c94480010f0403220710950042c08503500040c0c0049865982d60912100e50001408900702980200c1c00503c404400c1400300ca8204007060b4416225a07000e0103403004600817908014a01400e1800381144150306402850b402c502c180c000b003150383c0b07035224240d07a100a210720005100d0300400c10811891741240140503000901d910109020107101c000440b2904009410a1411ba03034039659014580e04001e030301488203082e07030b0701c1030713030341484070003e0141e01400742700418442d16a400a100c3c1d9105802da40c0040015890b055140c01705090060320001031f0f15100300d50f0500e842d80c10b201c0d100000075010103185002c4c0c000403c860031515034807016030004045130b06 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 210155692 1250 210154442 210154453
    0x905031e09040c030915020a0503070e0402130b12060f0102070b030a09020414090d0905090604090f061d060901060506070b130b160f020109051b041e0203060a170705040e 75
    0x11035032618003410440318040d40c4c00140010071881c0110390f265414a60b000d07680d1051051200c00350300181180e400c540c8508010910000e554005400303486640d1414000e007505107000906c62803c100584401040c00031030030003950b209024072040315580c510150042e40400c204100540c018402103410000c8580003103514074613038000c182030354445540304c09401051400c00c4201c01c0140403514400c0c800d0314004524514040c002400312102819041c45550f842c5540c40c2008520078200350480e500810910041c0e8100c49801c0441d0904e40c01180180200800200b140d0410301c01c0c50180e4000420032800c260309501c401c40b80d070704000e02001c40c0041312490000429801d004003480740f00c081c1c003030b00316400c0c0700000207000030034503a040c50a680c140042100060b034046050741c0d2140e800413020903105007c50000700500203191401c0e5401c2e2070501c0032000007a0580045100c0d0a00341c50b40200603588403003801080d500d031880b001481c3c020040038802d92401e504040340c0182c0300d100b110f8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 210156942 1250 210155692 210155707
    0x210d0b120303040c0810020304020d020f060706050f070215040f0f080f0403230f0607050c0118060b0102060c040b0313030c1b0501110703030207090c02071701060311040905031e 78
    0x5255a006030350558980005140c1000440320401c80c000b50001454400e40c00c505056001c1104a20bd00320000c0c411004a204121907440d5030702681d0703115030080320038031190500007900450140243c90b03140050051402d813043c1901c9000406008030b030310148000c14800c1c10b44030000c0039030601074222880f1038204111072504826030701800c003450041480000c000ca024000d024504903082518981e40c000c1c02d2092000c4c031001c00c03115804051400c0242c0d48d03400c0c90103024010684070325a1100710070491501d00070f115131755102103500d402c2a02240d066450701443d070f00d6140554450140f0821040001601d05000e070046400b4191090503c801d00301696550513817501c1501c03003003030200d40c1c03c100204050b6903c6907046900013611000703011650b0840d140203498040b9401085100c80e02c41d40b01405140c0708001101c01031040c1200804248052255580079111922003a03803d0359283e0813614040c07604e07100c0c074016650b000c00207514100d03a02c0380c106031205259805d50415501408501c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 210158192 1250 210156942 210156979
    0x100f1a0f0405132306060a0f020c040618050109060e070e040b180a0b0909100b030c0303190305060102010c1d01021f0207031d06070215090d030e03210d0b 68
    0x18085151500d40203d10405032841c00000c2a821501c840050300d44071303017801056101d4004542006000c3d00e450500441c60490a034584070062240581203803074403400042054401240d0300c550080060140642d990b540f000278156070071801081d60250741c0e0b402050150740940302701c0030882c0b8080c0012680310700c4d142c0054101d0141c9502074400000300030422007040c0f081e104107040070404907103210182c2803c55070966550717000143c030608142d0740c000041640da020411202444402000c0b030780d41d9002e41c101004081c0b0810b050201003030901c00810920760060107082c0140c4120b80d6610460304041c104558490b4000389074a040d405400c112144410401c06200c80101ca0044050781e90542c2c0d02e001440542450001070f0300e40200b8407907501d42d9a030705048800704c9404a4007802c212203070984001c2a8803410049ea684500003003001d10400d50440c1da5806c002c8812419190300c00c4212003c02486480d81d2a0543d001c4c00803c4082040080c0da44241c0f1513001c0507202c44108980034600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 210159442 1250 210158192 210158209
    0x60622110711030706050405040e0307120c0b07031a2704080c0d2f0304170a060b01080601020604060c05072a0611070e0a14070305100f1a0f0405 64
    0xc802018800045003424010b954600c0805804140d000b4400207103426002016070240d030282520884e01e82c3e10100010500700141c0380c03040e0b007060580340402c1c403400c0058200c10400400321804600c01e400562224060710907041200d602d00800d2108920060401003032048600d400b48041c050041c8015030f00d1851000c1600c280e200340c511560301c541d201c000c5440c1848214501d01004081190230400511180c0d44542e00c0201c14850940d0728a0100554250701658101c600c40300b400c402820781e0441e0009284100c2c0e806541c0801010a655004640842048031070038056840f00e00810002802d0b40d00c202c01d0440c0e280350407400c00400f51384a054102d0120000c02c2480e1100384040103e031107074408070b8002c0100b4281502d0802c1e500f0100d64640d0120711a9120b002a10000150191816001101442c01c071400c00c820f01e2a01b140c0240040c02d090352014036031001d11601040c3c4c580082800b07402e036000841110114820241c040000c1c2c2d01030b480c0400f0700c1d0317014400060300342c948455 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 210160692 1250 210159442 210159461
    0xc010c090302041b0504120f080729070804020904020a0f030b09010c05031006050c12030f0f0c03060a12051509030a030516080403030c0c020a090606030518060622 72
    0x3115902245503004000503100d043ca00e08628540e040740c1d604c00b0b160000d003290104d5400c004c0d068100c030003a040060840380584001b0344800000100f4500b04000c0d07601c00c0c4524000000c40c401d040d49041d00310160013104984000101c0c07221000b040240c60250045580701d40b000700300f89a4503071110081c094111044c0c1c01200d81c20042803e00c00d10b50000e00a04c0f0716140c1e503140580c11440d00c0d85a0030441d0941d4031891050110015068158010600c03101a080d844c0a40c65a500d003000814540f09110841d420f801280240e80414020481c503000c40e4012140280008038040c204800c07a101b4050808080300c1c3c5218000350000e0540d4800c51451240c1d03000c0f0040d60300c0d240001e60180c15680f0092100c1d100b0f030b8039824070100240e0001c0006801c5901450000780c030900c664000d9034100429440a540110341440000310000c41d90014010ba415560f41400b040e01c4501003000ba0317140f407040002c6160000000611075040540c0a40700f030009486a4080b100715800e4000225550390340c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 210161942 1250 210160692 210160697
    0x50603041515120c1d04081c0507050712030c0905040e0c030627190311010b03100f0b0a030206090402092710080625020c0402130905060909061501050c010c 69
    0x40c11005000c1c0c040b02c00001400000c8014041d610320303c0300f586814800520040c40d0b1180425802c201400144150072300c800c11690030869030410080140994205c040c0c100d0f040c80452081095081c864020b2940c180b03100c2d01c0c5c1007061810401001301a041d0812120900c0c424850791801c559070410a4500440c100410704102540031412134002200b20900c03072443d03a00c18074143c00c1c8210440c1c11120503c0e010b11b410012144100040342c0502065085a9070502c02c24403881034103511036001c207020500c141d408102c00d00c131500500400364181d01c0082d40c0200144410032182c02c05030010110900c0040c010220000048141c4451342c01403c14141070050800810609030950100a0b01030b003003c4005090794948596256210700c9207410201d40b000107080f91442c66802008554010b500081c000e54950303203449403a0701e4074601480392110301414607011891509001010b18010803030003020301800e0366034000205040e4402085030381000010403420440c004203208442c05c10703051b075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 210163192 1250 210161942 210161969
    0xe120a0605062704061505131e060f030609020402130803070309060c05030307270605031510050706090f120203430203070306050705030a0c0801050603041515 70
    0x3071007403025a600c009810b40f054484440d41001c40020282c491340e002d58804404135035000c0702180040254819801981c00140031320001c068080290072501a510500030110039400c0e45190b0322080d241d0604c00c1e00102c0035030440500100304150000300d0304c0381c0007038000342c40c0c090016012000d0b141c0d25840200c10360004a0036a0800d42e0041203800100300318945503d01003040d8407525268130019104c102070050b4034140c12958542341034400380303190110718104c00036a507881004d821039004840800b10310350041c4110b1001e14004010300c10454241d6949400d0150341d0f911f84000b0180f850080c1c5c3c1650341d42010400040000c1588425410305a02441d20381c4c0c00c0d4810080302c90712203981054104140310000d80c4000030045503403807a006c1c001811410003490f00101e82041b0461300f01401550810040007115501302e0010741c0a2540c10310b080000e0211920102c032134007401e002d02e951008080022a012802e045000c3c410040c00a0000821205152481070807045076406840c411690 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 210164442 1250 210163192 210163201
    0x50c0417031e0d1a0f09100b03100801060518161116092306061b01020a0806031507020712030e0d050106061103040e010504021b07030b062d010e120a0605 68
    0x3030084c00c96581a82c400000b441201000040080c170545d6005406a485600015026650354412800034096001200e030350741813500b187d080c1d40307115010380080d0b9820228000b400f0304000404c022180308003000480562540c150314103030305140010500811150050141c0659024011091030141548048003503500c0c10088100b1759040000d10703031142c044c0039605000940d041c0720742680f0840c12541d1982d40d880c1e003000604401040c0c04000b41c3c962000c81d031100c03099048000180a08030490484581100c07100b00403141e0319040f40c1c4c210068104110070050540040d03207080220380700c0d09081ca004440c020200308444003190f0103a81503911000d00300301080d000740c200109140c1900145107400d04100f6002403d580600c6a60b020725030014845c0076164001007040d5000c50540280c9885d01e9076810482b917080415607100e8414800d40e550724044414200755203041c0031a0514118040d1703100310055456050300c00200d5000025801f190b001c40c0010b00a6143e802d22520b40064607041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 210165692 1250 210164442 210164467
    0x170301090e01091a091501090b01030b030a05030909070c0506041506080c15070303060e24100c021011030d020706060501030501030803043008150301050c0417031e 72
    0x80c403110071520307034584a442008140c40042c610301c4012607840031001da445a50780c10313281803205204000340003965800815842c01e0781d001704c0306442090740c0c00d1150500000c10961500c14001005084e0750041203000c00d1030401e9501c2c940c0c0250705007440d407035400ca0380e10fa0a0400c00121b4040ba0400791450703481c10288000e208800240010000070b2582c019240c01107415680a59100f120b031400100c0c1a03000c05101e41c0012000d0100e030b400c01130708d034141806440310f030314036492075100c0c064003000200003e82800003245208840543d5001e03880c0455400703000340000c43c9100302007040052105c004c0051380401c001c0801a00e80c2500580d5990700e13040150848200d50000c504040c2000d0040001c9800401500e80140e08030491050064242c0c000c4182251918039121045103202010105282c005000301c1c41120521a010741000300002054200c540485044051840a20040c007145c04001c1403008100340301003c83c0c3c0740c401c4200d1407865546403403a85112044e40045c0d040019407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 210166942 1250 210165692 210165701
    0x130e010219030e210a030f060302060a1e0c08040e19050115111c050309030702091e060d0b0127050f1f060e06070602090d060b0a050d12050903070317030109 69
    0xd10b51054204100c03d44e07001c2203800d2040d011500209074071290380c0c071003885095008500a40e4000c01c41543c070005010091310311009031700d886a0b0600703650b09041855024034006158554000e403110325290810340b00702c1c910702000e003404244040c0c2130280ea00c803003614480d032406070100800900303000004034001045094424140e940302e400c40b46425140800441c43c41801c2c3c2e01c203003002520b035514038800d00d256000b40c540c00780d4807440c1031b418041c00703d007a04603040e00c9111119500d410395581310184400ea4171842002001801940010405500445844d01c20807074003078200b4103075000c001002402e50f04244da5401043d40b01c0424040b4044203810b001c050b020513220b540d240c00d0301d08940030b440002c01c0c1c01d0403402180300048100c100041ca134112481480000c14190140540341041070003803004503d0b0074001c0200e0f01000c00c103880d02d1891990503952100c65841c0c800e100000c101c50725048106c00c580c151240c400044000b401444280091440d412101a206e62421806c20142c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 210168192 1250 210166942 210166963
    0x30e1504170c0603070804030c0b0406020d0b03030c070b091503090304050906010206090d051e031810020c030301140f090a020712090312030c050903100e070e06130e010219030e 78
    0x1507100c0b10001665403039000560740d000e50107017880300d819a81c1d0305060780d0741c508038000100b0200c1c84104010401002c2d602606046260440400c51003a1103400c2c1540c070300c5040b281503056032000000b044a0040d41e03000705001d5a0141124182001000c1c10301c4813030700240e690341110b41020406120364245030903031644c014024401410710b42005014140c079654100d840804000c00054000801c10940b45d058420041a85240c0d60324074200740c90324909031907240b60084030300802c0d00b90075035046113000355190504484041d5240d40d00e042c8000e5500c5070701503030240d0800c032220402441369844800c494480c56000b40702507545c2d003851800086106660308010140031401c4803c1c40441d200b000e1070b030402806801c0000d11020482402d4404e4000c10031130710751500c074a1001071044051034225502c4081440200e80160752102d1615003000c60880f021034004070040b41919032050980c011174070354182c10000601d0a01c086480860720030965075128080398849400201c4034008000c204c407003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 210169442 1250 210168192 210168239
    0x10020a0e03010506040212070305040807121806140a0c110406080604032304030809042c070b03061005070303180818090f1f181e02070f0f030e1504 65
    0x2008652103c0e00040c02001c4c240322304040c1c0d43c10000d82000800f80c00c0300c4031240c1128601c020243d000100410490004002e5138030314552480000b0740c140910066003802c0c0300b4a00035410000ca00c0320498100f10024400d4408005030140c900c1e560b1114422800038010342c5001d08510f29140c00e001e40007800640e01c1300d070041c61034010760b142d43c920f103003c0d5025a64480345855948032110000750182c0f600001e14130440444801c0b0340c0062155001d440b0280c080c0c02c0c2602d82060b69040c040b001c40c001202c0164224000d072070141c50491080000300b040c18464200042c0f050702603101d80c0c813680c0c8410b0044039100310025504208840c030100c02c4044041c00c4984c5201480c0c0406002c080d65406454100b0104444030300510b1004824003070006003c0d140e002804000c1170050040190641d00002c89960003000b20100030a040c80c000c5954194005540c03600b0885169255540718146d40d5003a070400c04d41d402c03c00030a91310724101c54240012030412a071194109404200080004442d4011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 210170692 1250 210169442 210169447
    0x10e03062208091e0a060e010e01030b06121005010e0a0e180703080c030306010306090207050c06090a03140a0201110a0f0f0c0b160605010603021201051c08070b01080712020d1410020a0e030105060402 88
    0x2da070ba000789e03031580090703007860082800ea60b03c01c00b0640703602030f82e420790410794141c2e410024041002c2807490110340090380c65240c4440740c0010311500c4410740c01402071940100d000030300c131500c45000c91b0030b0343c2060200302c5400381e55071340322034056401802001d035603078000006000803503900d17004d2071024080c991411494210300e540d8140d07880304482c010740c0c05010302240c60003c503a14100e4600095811201c01c100d02400303001c0103034484108070012400b1800425181500305c500144408c03070503901010b1000d80c080c076921502020103985c3c50849003080c2c0140b002c91300e540c1d9031016000c81080f80c40da415001c441460241d00340c602c140c100f601054810710208841c64400d00080e41180c401b42c500e403480648008040d5a41c81c07007030300c01a00100e4005035901c02c020280d000b190403070f04403009441c169a124165031000120160010398095010482c050120302c00481c04481407018100b1168840c00d00032400003030342c1000304e01401082540c9120040c90600b03002d01d5030b201e00121021072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 210171942 1250 210170692 210170717
    0x304030b040219081b010306050a09021b0309060a0309110414040b0708060f0409020316120506060a1505340302060903090d170915040302010e03062208091e0a06 71
    0x6658283c0b140405d1680d13a01c1c0d42c4045000c3e4003e501160151201400720000503803619003281c065800480100302802050550006610000c002d403109040010007162600414480840c0138180c411020395010400c8550040d03150340d50300c6802ca03414030740080c0007501e1415083c002441c14000700303c0c00c24859820204109030703891102140f04503030121030001e00c03140c490010915140441c050a9041812602d001c2012400345a60b424043e1041045801c43c3c1c2d200d205018100b4140d100b062001010802c007441010b020384003030b046641c1c8403e10140103001503580c0f003c600400c1c11000c100c004c21041041c0138154144400c65006c25010300441c50460381c1c002048104149080c007070541d4030400d00c2c3d441c00d5082d00d030444040c00c0006140a41c0351400c94219111980244012400320b849190080e8290902061281c41805030002c41b00e80c1d42d00100c04e09094108007902140d031300004000c0202e9550b100b81c00c00c10080d1030160000542e800c04018800c2810b5150400300a0100324007121 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 210173192 1250 210171942 210171959
    0x26040609062d050d020705010609050108071d04060506181f090b030c06030711030a0f0e0d03090e100302040e01020c0f0307173703060603020f070f0302030702030304030b040219 78
    0x1040b100c4a14038100e0b9540900c0103041009000303110004046500701007000070415415000b0354142c41d02d09058840303407a643c606105c0c865400c82c0300c044c8041e03603140025021130060f0f4401c2e0743c4480c0240c100079200c05a40f031000750514007280c400798403103200c1c01d03044600d0108162a0000d807403640b02c2044085501000a035540c0c06e8004254031600000001a544030702c145503010b0042504c00459407204a80000a446130440100d13040008840002d010114a80311107001440b603016102c02501c2c0d404e2103035545013890000c000c1c141c291202c3c0400070040c0c4070361082c902d64602c41d10006071255445a403c6080020004004c4119401032064002040e10703070141401046605107916a1005030040003294040611014240c0c00b21945090001d42903254200608818940d81049225100c0406070700701d002d072078203d0710041c80602130400050200304c03254001c0c9000b801120b080114607400280756071b01540045071020150820300c0110700b44820740c00300c00701c0c00281d0b410820741000082e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 210174442 1250 210173192 210173267
    0x9060e150702060309010b09010605030106030c05090f040c020c031005010905090604170c07030c12031101050c0703050723150601050304080901030b0f040f24030b042604060906 78
    0x80d100f01000008140e55020940c00b1040c07134a0050121030540d80d50701c0d406880d5410034410100440c0c107001e0750f11170180c8650119850391000628265405040e003003400024a45c4a02c80025841403803a42c20140e50b04100b03000328a000c0000c003140c158140814171041c3c40340034115a4031944200c0c180700001d185c0140781031042070003c2d14030341c0383c002e414a99407070b1900b00d45c07000e021000d0701c0801103603113106109d05034510f90103920743741101c5021300d0495088540440d041604040c080c401540003a10440003060342d540140038a880d010030360205070769070071110045400c40398002c0302500c2107911242503c40c0d0004090030a28190301e001d403141c013454464828440d0415a0390403400a040da0f40210100c5a40b2025100300a0300c1e81410307950005241161071941406940001400c2c44000ca802c441d00342da034050707114480c9072074035558651054940e104820382d42c81c3c44911070314404456005080109000e9440b01c0b2954074000024102001315180214003908000541d0740110356802d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 210175692 1250 210174442 210174457
    0x5090f01110a0806150d050a1d0606060901050a02030c01020d02040e09010b09060d0602070f03020c03070e2502190f120512190b06160c080f0c090403030b1009060e15 73
    0xc0c01c02580e00174454010039031040f80d840207005071405044c0070314424107030701c104500a0042c44040a8030840d0000300c0c1d0b0b07005c0465881e5030015040042c0c0341c2c19445000034280200050044a00780000e415880f400da07046414002002c550214007001400000907901c0d070004e0041b402040a01c0007000881c01a90300201500c0c01655001d122508014035a81283c1c0c20980000e0b0b842d1021400d850020b4881c001c000c074052180c170800b400464056035503a4094058030740d03070080416040401010700084010f00c00c0380401c0d07000b003200030242d0519101ea03402c91644510040303000b080f03407483c01c2c1318002c2c40c1901c2e00040210622060b082004003031425a0403802c8800c5690010002040704c1010744140b13000103800c240003260690340c0c1807038081c441031039502c00c3d15041d0765640c44040040d500d061b64440e4003000e51045200403507a041030341340035401c603009160100301c1d079040b40040740740c4444585465000401201040081c03a51007040e5560f00141101e500f0f604203111080d540c1e19010304078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 210176942 1250 210175692 210175699
    0x30a0f0f05181804060504150b13180f0c08060c03010b1602130e0609010e0a0201020a120903081902070501020c0d0b100e04080a020c04021207051c05090f01110a0806 73
    0x14698031035414030b003428003050b101683ca1030540340c0f80c0017402d030645003225100c40400344039070b000405d401002c0c0e05040203049084542501c601e044050904c0e150b84040b04410304400801141c0540e4940880b1400345000540e11464042040e1a02200500380040d20320706200510840604504450001221200f510351007029070002546a01201d15585415460540b0020080070086403040c4940010b2000300140345155003030644444c031002001740140c1100b003660300007610104080300325a00c68501800510703240c0e40c84400942c0091a010003c0064803001c0348036603810880403014050038400342803400918404551000030b0f880c4014442d21400000840641c007603c07030400200712002c81116107040c0707802d045240d544120095401401041101000350410380204c0d201c80300045440e001c00e80d00c05200f00c07819003103070f00a0010280344104001500f01c0300d004d858002c00c030711000340406590251001e401c41d25003201c071100180301484215199034008007030a900071800d9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 210178192 1250 210176942 210176977
    0x123030a0e01051501030b030109030e09071e030501031209060815030c0d03090806010906030206090f01052106130e0c12031201060201050a0b0616030513090905030a0f0f05 76
    0x2208040a00300307072040590150300e82820812004103402850140c0032003030702d00b04403141c050030a241c2139071201d80c005000f003408030500f03201c107080c40c00380310b58050301601d132250b00c5416506044d00800301c50501e45002940354001841840500c1c0121480303004a42002042c0c189840409040d040b8001c001c20b8240c002e1180c0e07040c1948080c04140003440300200040003680d60b610f0b007e0107400007802890b00b01c1c030440002090520503849028140ca4005290310f0401510030100a0007240f03c1c411541008070a1150703200e10103110109074171290849402d50781c2441d20f40c003440000129029010300c0182040600318a910f004a900c5e014104181c4001d0303100c05a401c421441c41c4900c0c2e501d200022041e0000140c0b141d419400140520a42c0c0301c203001d44012401084924041e10740d007010201c085d0455440024099801000520b104171011080c040da6148954211030166a05940300d0b0400201c0c181c440303a00c41c6005080c00118200080b00b03003100d40e0000c0160143c98103004111021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 210179442 1250 210178192 210178201
    0x5040b0703051005090f043e0109121208090a0c090902030a080a020615120606040f0f09150b090108060f04020d1212060803040b07060f060302030a050f0c012303 71
    0x80703150f114050712018207400000c3c1000841c00860700412075084c0c0f0012103c040f541d5411001d200e0701c80145881104044c0484840c4440c03e4a01d0304034240e41d07042c840030810006107161801112510f5501951035152030782c0c0719140140c01124020040070481d08442e4400740015070900a0406580c91000001110700c06440070038945a1b6818000c0c000080206000b00c040e0750009903184944005049100c0c00220380081c05a004807040e000000354001c075002a055041c00d921902088114030408254120240110b42c11200d2469007510404a0040000c000b01c040d402045851002569082001d6140c801d1690f00d41364064400b51320111460040340641d5503d030304182085070000354004603051742800140104034001c071032560700d07402e1800c0007551140101c00d8808580c00e004540d80350100b03e0f07a540c001007421083d001c901e40da8070080803003d40c60810040c0010f511600081114803140034106140180c8290344030304201c9420a070010b000c0034410744005203078000060603201e864 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 210180692 1250 210179442 210179461
    0x203090118050601060207060509132a09050f1c033009230304090e100f060519030210110f0d05131707030206130806190e0105040b070305 61
    0x1400d6100148040500c10703080240030002c51802e0480c2e0745d640803a91a91380e15030b4203036072501805854030380c45581d000710740202070116005500c141a07059800051440c041c60480d880d20703134110310500004d1501c401404141042e520948480e4406c544c000e00d4188500c0080c05843d2030480d004003002210016250141e22404290301c85182c40c80a0007c40d1000c460a81c004003003c036000d548a801e900c0300448803043e5242503009203803d0f02c0241d40b606090504000140c042d0314510001d038411409080134a0742c0c2c0744100941b86859aa004c0b411614190030042139030306080d80072030a062050400c02c0140e40d5000340300412480f500701181e0180d4280480b504003940e215544d4211300440c10780095099100000300a8035008980000440380c44030040c545100e1190300c2102107130b0089805001500e0540c020385070031120280d40031a9203403100d410a0600710305880c00850042d20f08403059011071b140c01000001c0d000c0b600200007134036145d254030b103c00101030b210006060351140072400d040f0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 210181942 1250 210180692 210180701
    0x60f090303070807060c030605180105120708060c03060a240810090203070e03061005030714060f0c06041115070312021e0706140108033405030d14060a0902030901 72
    0x1500210626150401342c14040080d0000302c40d840700203403824201190a260486410324110f000d0041c10f96540c0c03c04090046805159011a00070301c2407800c001440d6408101083c030031202103070b4860316030030700c0c82c00e005222440d43c020000c020380c1c04a10b8003183e01c440d001c55128580c58603000d040c50702e40c05004034410000390800555203000004008940307400c100c4000760424243e04640f03d550b202408050403540340d0241c15415005900200b10009602201a00400000b0300c00d62402011320100900c0351700c010003895554009000b040144110301c2d0f243c03901c03c5020388464040c1c07200c401c0084124464181c4c002c05102501d0056003840405906681a80d035800d25021071810440340b2144182e0844502103a6207030400200c80621910142294102c4a00b50019410500d07020300100c58488001d03000507191110642c2c6004c20014101c81d00201401138000d5a5903021408403c01610041c01a9031002d16482c401c0c001c041d2124103020f800c5900351140186c981d1070b803040060151 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 210183192 1250 210181942 210181957
    0xb1302011d2101090c14060906032e06080105060406051b0a060515040b0a030201050307110c10120509060903030105150408160509070e030c010806300d030506060f090303 75
    0x203199000070000c040b001580310741c2285010300b0081100c01d544149841c602221030503d181c00a10a101486103404c1023806190042d4001040607940e0402e440c048050212021443c040000f04060800c0b040741c0000c1458054030341940c0f214501818503d001d4072a214500c2c2c010440b4101041107240d203c2c0501080d60011361080081c006400c0c02d50f81d00106d0f002507074032a4030481ca0850540f600b403520035201c40840b40c1c1a100c01d415561540400d44000c90040440000b03800f5517001e86e460755540070544280e0355140d4a4844005103107010780011500b005000d040c1651120701400241d240001c241d904561007116a52070b00c008000c5240c8803402aa8086143c0d4400c3c00f40c62428003d520400c1c8050351829101400c055444820840d807504480d8007160709900001000f42c00c075441581c103945e1007407014100000300c00c5140444030000c62054250100c0809008070a40c404009003e0501038440360b28003807116041c01e03c00506030380300d5a172030600c16100c006007900307980c1c81c03e10540d04003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 210184442 1250 210183192 210183229
    0x81c020f070209130218091204030b0408030c070804060f080702010207321005010815040c0603020f04080604150b010c11060a090b04080114010b03010b031305010e010e03070b1302011d 81
    0xa1071805000c00c0e103d4140d0b10303c1548c1c0281044881d045854100392000c990300111000a03039155612081c00d590b00150001c81c101900300f2002001c0748560000708001e00c100d030341c0c80c050f8035a0343c980100700c1c400141602003164010403d034000320742c1c6a02c820504c00401c004860017111880b0f40c46400f1001c100b24100180549090301440301c0c07841d44081e04032085123069585548003105e4540400f802103038002c0c580c644c40301040c03289038403d5002d000724444220186141c662141c40e07040c50500d040760300321185844821408400d120078060400741c40300a080000040d50070b0f03900e80309841c4580100500076903001c540360107501e00c210b1800d001045010340c003664607a00c6180140c042e1801441004060150310300000d50b494007501203038122018000b0081c01d43d2107000110ba00f004800c7c0c0240c85664039007030003461420007803254000e900003032001113648035030900c2c00601070f5100170b01460082e09414000d401507604003606041c41c5942d00c0b0103036a16904280007070a80020030301c2c170200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 210185692 1250 210184442 210184459
    0x607120e030c031b12030a0203041404020f070b040212011e0510090504080307020708070506090f010306080d03020c01150515210403030504050c0405040206090d0519081c020f0702091302 82
    0x13405158421035220f000040c0c543c0c00c2001100d0108941c1c81c40303400c0c040e20040c0c3c000c1104002094a810001e00d4001c40280054949100240245020707000744000f078914505140038842149040300300003007071290000082c488800b40c9491242005c924020041c03e0303c0d01c450006152008100040780580082e2908001904040c20110400d401c121480009446020720109503403900152070000c403000240701070724100c803c00c10301103c841a40101c0707060503111074010464132400c1c01140c0a0f0718032507800507240c01d840ca04140c00c4d2000900e010784800d408820901507500d5100d1446d104180c841415a51801148140c2d00340c48400321401040514000900c000c0541c5504001e000f01e000b0000c6507540c2001c0070800003215400d603002540045d0400c044d030810704280d031200203080d00403401d84e081006000040109040c5241c01100c884900040d4001a001c14a00070104d203162000114103105408889102c82c1c452407030040d220340001000211a0792810005d640f615902800300030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 210186942 1250 210185692 210185713
    0x711100201050610020a020d0f0230151603050417120f15030607030f0e0a0507051002060c031b040b0c0109030815010206340203090405060607120e030c03 68
    0x90080405680040c0300781d139403e0200030001d1002034200306d415001048510f011240781c1d02e5050054914a0890300103d80c1c1d8540c402030a0100240300c03100241e011413212800d0095201b038209440c5d050001b60b0714001c50240302d41c0c500281116800022582800140780d101c0d4101002c40c9001c0650f00c000c0d5080002d0701d070100100300d41c0f0460069041104d14200e80d11403943c1d2684402c0c44161854060b40038100241416219821440e0804080a800210320488204540c14490800b40070b650b1940248800c0010b800d120040b105803044510250800c0d09180120b200c041c4800f820311081229411030080400d102031044900a08005580582e14007030582c542e806450504d000340c011802c2c0900148403030120440780101514164040c100c81d6039140c01c80059401040d542c00c0050f0255007035600504240c8040705410a0550029929040f400c4100400c0c0c900040006003d08014006000001c9002e040c10440c84a6800c050440450b500c01003803034016510501585442a4060b55 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 210188192 1250 210186942 210186947
    0x50420040f06080c040303020604060504150c0c1b0b0301180f06030f05010f020f1c090b010602030c06010f050a030f0f020603010b0c0c0414160e090115020d030606050f071110 77
    0x4900b202d036551251000c44d6906258a113580c00356220190140e00141c00080004036150700107940300780304880c1d0b10070a051010030b6104469040c06180086019410040180111101c41c1c403a41c3c01d0705541507400038180050301081d404184224214140002400c008110f242d03000b03071400b52004201008150381c0c9080a000fa09030140059035107510308000f148942c0b295008481d4140f8041441c18030740748402c45008034a0040110740c0c0c0c03400350313030720903580004030310140b214024081da074010f43c2c82d90b961119080c1880d80c1a4010100c4262038001001039458a0704a101141d405c0440242d02e123200c2d013040040036040500c000d600c180e00000202c2d034199048041c0c402100f0007400c40340d002c00c6d10b00c14001101e2411205480c0c0200000008401c1425480b081b1100401454407804408440b0013241015100707070410308070f045440c81c400700300d2a0304201440c0680707190b2400384052031601c50007030518462070b001b2522400d00001c910b81400b150b5040d11510340000f0303007074900c0c030308048900 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 210189442 1250 210188192 210188219
    0x308030f0712050c0405120703080304030c03020715080403080a0b0d03030f0c0512060402090a08011406013b0a0b04080601150507200111160f150905042004 69
    0x40852140c41c10840b0400142c402c1c03620465555211a24003424030f02003040040c54601c050510b80706600300400011191006180200d01c00e4445030b0a0301180d213400303801c20b0b480380c001c2e1482001e401249000c00d54070400e550f0700306406040c08180354590450400290a0f00c1c60004d0b00030b1566004a01099896804000d9421180d00c00f04083c0d110610205d0309842642500c0c1d1582000801003122841c0c640d004003009480244004072a950704c00b0442d0035208501440816110b245041000b1540c000d455484070002604892141000070740c10010043c0309088003000e0056108440d05041d10b4040300b02c0040c12030492182d881e5540c1d0400c0560300e01e070900a0016100f405810710504500030401d48005652200404510008203a104a01124010041c1d0304010a840e001221300b4030900104d01d070b0303941c1d0020207401d00381040c412a0002d50540d0009e40c0500ca6506681d040c60b91001c07030401942c00c215000700300825000c1c0074228010000e00e054242c8500041c0000e41d041d071903d003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 210190692 1250 210189442 210189451
    0x4030e01030507090e240312120f0f040b04060e03120a0b01051e0d02070602030c0702040617280605010e0109060b040609050d0312020a03021c0507021509070308030f 73
    0x207061026070b40e4043c08569024440c41160005490040070410590400c610407411403c0b24440b0001c80302c03400300003454514100d00744002031600043d8940c1e509400761a00e40c5c089500740c1485440d007001d00f14409840070041015281072000b1000c40e0401449811030294a00754a0449894900400c1580c00c115000e40d1210589483d01c014451a540200c0c2a04c0b0b09411020181c04400c00b031450000f41a0301c00c9000d41c007100d90030001200010301c1403010f503016120b0700f07034541d8840c03020b48103020846803030343c01c8a5018140800706003840c010000703a400300080e101d031212000050458070564024010100240760070705110000c1040000740e003c4030b040b00c070701d0242403054036036030011a640c9210f64003a04001900302c050901082c140580c0e640c203d24401e250048402074007200f44d400f203030005010741e000207400140c0844100303050b0455805404c0e81040802240c105032070f007c2c0d038440100ad00d02c190980700c3d8001803041c60050101c1801140c009d00350907540e00d000f0a10b80c01000040704c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 210191942 1250 210190692 210190697
    0x15040608011509120305090d080c1b0f010f0c060b040c032f0d020702060705010504080c250b091903080306010201230105042304060b1002061e0a09051510120302060c070609020904030e01 82
    0x10b0002f1410b1400614003441218107840740c10080022001c110341200c55500700b510aa0f1711980400d102c1d84030341c481e5820401c0c642d500003c1c850080e000c6000041e0443d40340c0703074250001800b0000c1c00d11020f4210b4940304400c000041c5d6480045c80418910b010b45400a420380d403a020800040c400c0220041201c6030f81942564807500780c0b0a81f120722503a501c510030130004c02034441400786002e100001c01c000c00001b0034584140340461280401c242040e0000c407136500340481800f00d42c2d6024022042840001a45130b024401000c6002c445d003401407141620940d102c2000e003100c005265030410103c001d1030307101d1260f884c00382800d201030000c040e44280600e0001551030304441c80894414000c4012100c505a0714903082040d01a5040c09002800016642c003600e00c0060740402807552000780d075800342074491070700502601da984015403100c4404810865444000383d800321345030764480d100700e401946a0f581e9003042c0c002008242402504046241e050109150700621040c0c08000700760f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 210193192 1250 210191942 210191983
    0x816080d08040f030305060a052d03010e0c062a0f06070f0807030c02070b130f0503120301090513080d050a0f021602010e15040608011509120305090d080c 68
    0x16040307034410310072a40038201d848102d400b903000a10030f03000716070061801401c5d109155150000601c0d41000c007240600350945012103986078100e210002c1d0914942103002b041403142240e907454480d0410520305128072800600c012409084203101180020794101d0031345e2040c0c6000d022540d40740704901345c2d1b03841c1c81000000b0300d100d071084040203804501940c40011230b45070309400381c02601e000710030401075024512002c550500c8100c0900701e07070540e40c001c4140403894403240300ca0560103500402e002e50050030102800703d03400c0007140e04507481a0800100c56503902009011043e5400b0002e00809001a40c80b51903805500594010b9a48110400032554500c4501d4120310507030311809040c0b082502090003645c050748088040c80d60240483c2072300d40c0608401c040603440350b0407800114a011005104000280002100e400620309091072400c0c10111480c078803032010039000301000b0f17002802c05101e0b1180858448840c2c0e01001c0d16071240d0345a2444c0380c98804c0140c0c43e01d10201070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 210194442 1250 210193192 210193213
    0x906110708040f0b07020117100803030705040603051003211101020406031b211107020607031107060f020309090c0d0c120e0303150f0d0c081c0e01091e081608 70
    0x40c2d0003161500741d8140c54400c4400230301030710030b041103500400c006100c5505180c0010b80c0340341800198800c10055039882c2d99281410b034090203da00c0540550700040181c2030900000390841c0b070130211458a055400c03000c03481d011080760301112411041392554000b01d00013810381d4254124443c00c8403004e94840c9011240a800c45805100102100307600807001c0f020548406180cac170951169203015241c0e4070303080c85a0041220740d80304110480026054007c018045c080900c0444003070324140ca441c030340c1c1401110000f507030390203401309040c4100d0501011400750101032040b42c4c6020807030041808140d05d10a400790030100d038401c184803200d0420030204031028010048034401d0058000348070419240d003040c465940394440302d00b5042201c0c2c1c01c01a01241c45508440014100d8200428241c2e4905510f1519074500301c0305081845607100b00c202e116a0040414000d84010501038842c13810b00b04074208104d00184d0147c4217901851825902d9001c1481403401607503418421690007540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 210195692 1250 210194442 210194459
    0xd1e05071a090a1404200c010e0d090504151805070206060d0503041e0503100b011202030411010806041508010e190c0e09120301080c011d010c060906110708040f 71
    0x21158020b40c040c00d908010b0001203c1c00b5504405268040c2001a00341b507001001510140d8610002000b0040494180007400f02400752890216946002d030584000703148002d010984103014251042d0f0716003110810b40e000c3c41e14540020140c0600300410302400843c1d4400508081d80e0f0f4034014000e09000070024140b0b8860301c0300d125444802585031034900b44c8045002405100411920844c5880c0000d5964003007244100b140350390b2400081210101c0c00140c070511b4049840c642071303030061082001150b10310f00c0c0e81d000114207003043c2e5440d070f50b881c00160003481600c444a68641d00a0004509800154044490041c0c44402c603602a20a0288080f59000090b8001d001c03c2c112401484080040f00034190046041822110804a00344400c0c40c2500240c00c55034496000c2b0365212680c0d80c2c4035042640c524201508900f0039548d0400003410380c101d6400181800e900d4245510400006501031402d15468412403602c420300c0d46404a191781c868411401000141040802c1802 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 210196942 1250 210195692 210195697
    0x7080705030f031f0f08120d0603121d1507020111010e010c0c020312030f010b0a0507020d110108060a06090603090201170f040b0a0506010807030e0a05060408130806010308090d1e05071a 82
    0xc01b803000920081d80300c2a2440c41e140e226003000d038200c5131038400c004000b40080e0540d4880c00b210f078035001100011382c03c1c1400c00d6007442c11000e128504081d0540d51142200044030b80707042c5c0a20300303032010f1403002c804580504690103504d002907103003003610200140c5c00405049014421400c5e1400d013116548079000b00e00003a030b90345011101000c0100101181c2c400100450300c0c071421b006040c076805400141c404804488181c0e4401000c918101c000e42c0d11411651b030181040392101449405e00800614810183c090441816910441203081da0702a440640a250140e41111a6450203042c2140711010644080f078005444401040700d6401c00c0c002e1910440e0107a4600249543d8080110b002e41200150442d16000300e02000022900c2800354600c507074000c3c4c009a0750b900c0d07003021b05107900b100c6034004c0c2c03d26000b400041c030000c2d51217400c0b16401041192404a1180e05044c0f6498840c1207051100a10000c41f0201d410000049820401c0f5101255994510b16000d41c0d03108051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 210198192 1250 210196942 210196949
    0x518090702031b0d0f0e0915010c080a030209040b011b06180b09010c031805061906080d08090717030711150309060a0f0b011e140a0c111507080705030f031f0f 70
    0x7c071140005010f0402103070004c6060505151401d840011500c416203c0e50000e1501c0c00003070b03000240e43c1601d08182c040c41c6007442081c6800100007400d80d01810040c0742c03c0c0c600809094944d403c4004801741c82c01503040c0301f50005030401d80340c200620134500805000400f00080b07801c01d0002244a0b105001402d03101b9040005008280c1d2420b2000f41400c251031081e0081569590380810703d04006c0101c0402c0b014103458080e43c40c01d1074002da41c0b90545d41d034445554401c400c500e05104d05d80100c19201c50700e40c4920104501e40ea01c40000d544003541080d11800d444020080016810300000c0b031038090794038000f0400400e980c60400c4010f0314030145000740411054441c482c1003661401405503030390300760f01e81980d0201d80d901c2c0d4132a50750302c4110b00e0310010720710100790821f11000c6040b08030020001c8421510360614209a240c0358000c030b0102808030907011411900b80b20007403046410706540e032a18156a4601544c04600d580c10344070051545400b151400f1074481e20040514007075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 210199442 1250 210198192 210198199
    0x30a4e0501050604030f080d060312091512050c090301050c120a020a1b0303090c060c020a09060806060105070f0501050403030e0c010c0503031518040803010e070518090702031b0d0f0e 81
    0x1000e0940e254226510384502d0300300c0e0600307c10091040701102030300c00d21000d0b6224800a6081c5104140010440f990980003031a207405240c01d801c10481c0c00450004559055400c0428150f40d64030314414180030760107510f909942818104008241000000c0501c07440c2149500c2c0c1546500400c54228002d0180705400316002c400b00c1c0d940c90940d42e01c0c00ea40076100e03141c04100c0b11040e83d60344800c003203194001b00102d100c60780540e045142480643c40074081c03038101081098502074000e940c80360050300c00f505003c40010400c06011403200505000d5030440d0091100342050702e0000c00074814055000d00c1d500450000d05210342c842c40d400340720244c21034000c5007180c0303071003283d00c050021400c2e64a510444001018100401d61240b084c4924011783c802174803585443c1d0041040227000380010700300401000900e9186030049038000b481c040c1034420304c00380d5a0b40035082c3e10b140308410420a07032680511036a440040b0005a079591409940d4803600c007074401341400c0e03030100004d4007800d61 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 210200692 1250 210199442 210199447
    0xa08070801142202070c0f0501030e0a0203070312050705030f0307120b0906011b02090412091a2709090a02040b0303040e0406090201051b0106030501051305030a4e05010506 76
    0x1c02c100034071000f00032006a044018501840fa0f0382d500341c003402591182c1e100c810840303000c01881d0f03014481d4040c56101940548880aa41d900203500c840ca540030081240704220b0f100140284500150344001c0d9109046954403041d040b80c01c50550022183c540000d2900e0001c00050482c41c020203450001c098141c40310750b1030319030055946800045259511501d02c80c2d412000d0f03501c820580d8001c0313000308004100749070304840003000c00c001030b00128040001c00280101e8408080d080f10400b00e01d000c60301d00b070b9130a80700c030329401c3e1985244001e42c403140440c244821442c0108924030554401c44080248403103902c01c0c943ca0b4040e9104491f404c040c044009408140250030640d4000e105140284c500304050a058542e000320a071030740c0c8580e5680c8414070401070244141038020a10030040900b1341c50b16964503580c2e1044502c0b40081010364640d9001105512240d11008040c500e8035000302c0c0c000141d0310b030b81c4549408210100c40da003a6125000302041d4800c0318140ca0020b8007807071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 210201942 1250 210200692 210200719
    0x91c030509061014040b1c0c050f090c0307080a020d0c02060a0f0605011418030106030c1712030c070201020c0306090a03030b0d021c150501031103010c030b011e0e060a0807080114 79
    0x10106c0e101125000705615180020b5201c4c0c0d801c1c1d140c00d0760321440902e40b003e4200000c1c0003074100322981c04c40c0a80c0c1584280074101c003012080d03903071003403091601d010306030394a035040c1e00680151809400000e081210035a460364000c51602c0c070070011428108044400c038440340d800c2c0c5805109d0035001c60344100c5103480740c4980000510407802c228a0040c11800540003003403c44e50310754425186010464000d0104018442800c45010000700050102d040b080c2e14400c0b241c8009000c405042c04001217050444e4002e1150140c504001400d90301145000315a02e601e901111a0440003c1d18114900e040e40c6408c410000e075203a006820a42c043e000c501901c40c00209c1000c0c1500c0d6441032a01d42100701c003003809641d01031482541d074140400314607001d25003502d42481614041c141800031a5200382da200120342c1ca200140d51030507071072010f2120140c0d447c2d80d00b0900b0b690480c0000030074404460700104200d004030602c0c0ea84850581e03803441c0001d0b100f001c0c8049298061907200005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 210203192 1250 210201942 210201949
    0x10305192109180b0109150e09190504110f0a142b050706110606010c060c030f0e03120c0403050a080a0504181a0406120209091c030509061014 63
    0x1508074100c0c0c2001c8100d25201c4a103010780c910440b140500040d12194021042d50348892558014000044000c0c42c4200890015000c040000000c0b4020f075145030001c0d03502c41030901000c1e4000c4040d80200180d04040c188404620810800d240c042c40120a47c0400d505009101c803003100d0040b210089400010001c2201800064405600003403010300b0913510b081c07108456203113191140000704003031440d181c2c001e0440100a440c0c1e0442d50045c00800100b039820001c0ca00b030881e404080015010425841540107108003540209468540b000f51000b0400000c000e00310012240d8000072503680e8007481d501e0390b205a000091403a00003210307000004050f040588075080c005e040c00340c2440d8462043e217294104510203123680c02e44130400d104548410b0500c0c21102101500c0910920f401c0000030088504401c0000f4050302c41000069440d1a00380802503014000c0c1240700ba134100300060080c060581901c0304010750081d10080713030840080000c0503045840040303407440390401d08000c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 210204442 1250 210203192 210203243
    0x1e0b0409051023010201140106080a0b040f020d090b010b07030f0c020a1701050417190c02042301060305090115121103010507051b1501231801030519 66
    0x642d100074991050200384898400b215003a100e8a803c08822140ba60030002429600c0304020302c400011060014482290300c00410740d840304c5228000303d15584d41c01d01083c020320201072849403403440030400040d000700d55004113040c0707030059a2000703680c0d88441401196215032400100030800c181c01110780d140c081c040c4090040c1c0000e0002c0100f9a071a40c582c9802008000340c420b182e5554020401080101a1200c00c66045c4020560600034002c10310b001540351041618240881140f03541c04640d06c1e500080d015444072012551203a18070104203880e0304081c091080420305240004100e03880510a098012505401b40e074402498600307014000204000c2c113071140300700c0c400002e006450074001d040c00fa840c01e0b583d103552040c0e140d4240e510307681d40202c51480c0d904040c501301c80030b0145991144c152100701084048803004c0c0a40c08580c14140e0700d9031030b04589500505039072005905940f50403039019a080c1c5400703840c0301621384144485900e00410030b800d10100003d0140f8169034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 210205692 1250 210204442 210204451
    0xc0504050f03010e0d120204261b0604061206080f0106210b0c09010512091c0e0a0902030705070c0303050d0c0809060c030a0905060a0504051e030301140a0306090c1e0b040905 77
    0x100500e059212500c030603070b80b4921140001070000b000c21600510904000c0c000e20200101c07180c03481540b2000024004cc8180c1c410b81081004408501c0c0300c1009680c0206c0c0206104412a03441110b4124090b02810541c441c000e10420070303444403600300c504446085d02e101e45c0890a0a030306e5807081c00c01202904071054081c10403d00340541e000b0788104030115401100454001d0940c1408050a015600165081d401c10070034110001c80b0503840b04558001034488000c4090f03101d5450150803030380b5000b140c0001d41300b0a800c03140001455040320080c0f03440d0a0707000003800700006040c0c0c182c4820109840c0c0e11903aa10000000b042c0c40640809035800c030400b4100401c1d00c08154440c2440d01c3c40c19140b41c41d4a5130b8500a101c100082080405013000b808800140101a81010785841e4001440341e81400302543c20035144560b50440c500c400307180d0155041081030642d0a1010040850740a242400140c0d00018022021700e40802c40880300036024031880c060400801c240034140c01750 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 210206942 1250 210205692 210205727
    0xf1006030216020607030809100c0203091e0a03080d05221524050414040210270305010c02070b190e060403080c060f061c0f05100c0504050f03010e0d 66
    0x201080c0051351584c00504050307010fa1340d490890304210390700a0414250700030b86a42180b0f172012480d0a00d1300402526804d0100b01d07080da00040c1c40300f42132282080c01c189007540c480c210500100420116201038030100c1801a8200300f1603641c01826808408000802c1c81d03500300c0d08a8860008810b04030080000844c0407012440182101c1210056400741d410354010000215050101d03042030b21030340b455814403425800050900e50007051000d58080d04400402242e68031a00244064021440c5840551a040c0b210156a410306900910031003c0280050091480c00100c0140308030a540e03190001a00f449588a5040c6c0c0a40e034419200c0313180c070b0704883c0500000000c60f4809011b003402804070009019140f070865980d00403050f004050a2213a0702d5241e13110504ca02c2c0a02d028000d652202c0c9481c818415030920320315040440c140c02d003415050140003022715030b0242c0a0011901c09030b071070f00c0707c18404a003010b0980d420306c2041422070b40012001d85409120703004c220719402c840e8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 210208192 1250 210206942 210206977
    0x5040b160908120406140301050a15170c0405180c0f0a030f060b03011a0c030d1e06080f0f010603050607080c07050f03040302090105061305090c04050406080c090f10060302 76
    0x80800c14240f0401802044880a01140c01c000140d0080070010001d810728048034910f60401c00015100c2e103250298020b00e030500700b0600e0b14240519500d0200701c0c1041070127001c40c070306400300b00e1450340580901402585001e80184181d40803c901c5401030410440c1a402c0c0141500210030a42142c28184105078440e400390210181c2441004d01404c201026181d580d81043c580410340070406207000c031506002c1149030200d007400f00c2030710080b00e56404007051010b820001c43d203441001c4448003d2451a2a40c005001540000d913610010055000d40350005410300c1c51508032006403101425a8100b003001410b61885400d81c0341d07112143c61156400c020702c940350b40349080c410b2122003039264000241407055280000805004210440d41e407481c1800509180741680810b20805024000d00303004220708100c01000d03140540000750013040314598507814a80c3d52032502110501410401c404185500f0304480700a1040c0d2070119001d030481e1615504500075801090340d08448402c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 210209442 1250 210208192 210208199
    0x20a02060c0a0b0a05010303110f0309010e180f0f0601020307020d0b07020a140705130e0c0d11030a03080a110702030a1511030c030a1d070b0c010912051c05040b1609 73
    0x90011180200d4131544000342075815407502503d03822a0100c0b00e036043e4032003041038049900010484410782c10030f10b010b55a000f0b12a0105406030446800c035021504c443c010030141c8c1030f0740c0300da41e40b14039114000070081d0340f01c00740160b84038419000040e40080d069013449001c2007801427407036000100391044580c0304840b81c45016100342c00d807483e1501508070350300070030a5180401c514031940c50310300400c0004071354929035103540d40c00075469103000d034009518210601c20052044031074104042c00380c030189035003407030000c00803401290036071070b03541c9026001c24608074003905a848042e0301070300030504c03000c440c0c541031070030b240000c0202c0d50a82c580c20b5034015078901c0303000355000d481400c10071905da00f41400400f05a07920484c0014220f800d8411070420b417500000c170a0119110700c1c0f8000c3d03aa03001c6085090240040c2c4a015000704054807510b40110780c003e000344521303c016030044a10340b07035154000081c6c59082d10003034071149004001c556010b4070035403248000c1d01c04d4242031031420b64 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 210210692 1250 210209442 210209453
    0x1803070312110105010e010b030a0e010e070609030201120b0306040312020f07060e0f1605040207020102070906060f08010e06010807050904090c08031b070b030c07020307030609060501090c0f020a02060c0a 90
    0x91200c5041c0010711501103941e225600f4040c00e0b01420300c0010030032203903043c8144501c1c64003000b030001d50020384602140d490100203500862007840c0843c2070b200362549505020f400200148801ca0008010490b404000361480c440c4004103600140030781f00944490320200e0314040010800ba1143d64200070702c41d9500303540c2000f0900b01e88603100c04208040007a0446040c040c1e00d00d8698800d0700300e000224101400842502c069403011540143c07a8003075800100c3c0b805007280c00c4078070007929154000c10901c0e08101400311949803030b036504042e80c3c2c8401c000c410041040d6196404109101c01186040d400f81c0c01500b0305040141000035100f6083c2ca0340c12810382241c0c0405219000060340b0080c0700d9295011207210b0f00303400005e0111a107801c0354511281f0004181c04000c20380030451100b155001e215100c001d40c0c1043d4240310380d00190520400510302881500c8c49189071000c0e40101e903009250311030f0510b070f550700a440c0402086d0244607441d808902c0c0e50005000d8101440f00192 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 210211942 1250 210210692 210210713
    0xc021503010909020901140307031b0e0a060f0602030703050901080403031812080c0c0c090903040b0f030a0b15030a090501060801060e0a0c020a020901030f1a07030b090606030c18030703 82
    0x1001c0d1000c110001c01c0e0051001760310068100036280c2c00c08460002c4075840000307101c001c60b50301100b847d180c0d40301c00c0400d4149400320b13000300c284548528141300742c0507030941000040d40e2045440c0d18110f5a285d50a076502e00c40c0700001804903e0a2048200641c00b03180f110b54064024103003c41d01803009089003200007940901112a5201d20200d043c809071f100030299401825800760310302c0c3c0070032503100540d100c0c800e001c1d09100304907040014000030820f01c2520000e01c5000102d54403a8905400009140c10440304001c1c4145086250742c0325141049460b4407102c0c0c820034440c43c6884410fa40030240c0094031069850359241d8100103107640c030034450303038004000708170a49082e404e040c1c280d94240c4044228030b60466204500720b01c0547d0b10090b116045a50bc10400400c4180e1850100d001242d900c0a01c40d802c80c0c001c0402078050b1305031f000540c41c0d4800320741d800c3d1140e507204100420f82c002031360715148041090040c0c4804190995042c128083c0050440740d00507030340d968004140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 210213192 1250 210211942 210211949
    0x2090f19180b100f210501050906041515050f042d050a021206091009090b0103021306060905040e070801060902120c0406020d050d150b032a0a0c02150301 68
    0x4071101541070140403802810b00c2c1c1000c980340707000c440c9501c0c1c4220030071002c13494000c0b1402640c892064a038401d04052111100690000082c49185090a036454544004071001c2e280c0b03021a0451059003140c40c800c20000c44080c0141070406400d04040c030000103a901030540d0030071703643e40d050b500c044203a40140452041c2071800004088006400c0c4040d44d8003d403100b40c02038014050041c20040c002861548003106603a00e688556580c41c521124805582c0052000c83c0342c80c070b01174180004410581d0503a4001c0d1001544000c0c1c1d070101c24204c410701c0c81050f00003005954107001a2600b03030041c440080304001105c290507124195103003101c1080d031000c00c1090f40010301201d030800c0710703910030b51000b4514080350805140410107500c2d44100368030002004000178098140a00c0359000900104401603003030086515a034460909501c142d03021314441614541000c40700e0420180503440f0100c1600d1181803110040c000e1710008186441281e001701400c404002107100d1070041c5008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 210214442 1250 210213192 210213221
    0xf060303070b2403010b030a08030417070f020405060108091506060403050717070602060f0f0a1b12051305030405100201020903060c0414332203020f0303040302090f19 74
    0x52003e0140c5810b51448681820b8043e074100441d91359259404030348013900b1600042d03455901d075200e103007503a40550313003580d808041c440100b406c9003440403024180c09010f10903102002141c07221401500c001c80110f8030840e050348100c040345a000340c9504c0c445c8d001000a401d40d41096102d039621820101300303401150610260fa0803a041c4000100045c900034042d0740082c0420b42030041100c00001c10082402070380310680c101291030000240c0c042c8ad92842c14110314070365403039000c1b0020016043c00c14400040350030000420007607511465444131169100d4002c6150910386420300100c55170380720080c02555400d00001c0e049890904c0024400c0c00030358581645d850810a008029011f2080050300403000711540d001c81000c0e1000420a800c42d00042d00301010103210640118442c0c00c18031141c40301d400003240da0602e410398824013503030700c05c43da5038851800709000e05a40c1d00a500c4080e600400c0c1101007480c0701c5070040020b800c40b001600e50452800e1428a45068910140d0360182 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 210215692 1250 210214442 210214471
    0x9040204090b0a060503070203041203140a03150e07022e0509061f050603070c2112050c12060d05010e0303010b03011e030201091406042d080a0206030f060303070b 72
    0x1c0d6240211903c00506002c0c1001411400c060b14001d40e64010b500680c14640c0941c4258001d050040c0301a000074544170725803603660010190000d014084207012000861412000032410b040740c191030b00c0c031416860f4003c10001c000245201c1e900d6080d85407000c07040f10070751200300e0050510300400744180414001440382d420a01e94500e00d402601d0008100848015014030155031100c04490f0429600e182400001c40d850034441c0b01d11350803a920304085110800e007180e46079081a24002e00c400340c80703c100a19030310400c841540c0d1181a58202e609a481320001d41180341240980407450b0040e00001000c40c3c1c1400d0846c91540203070440080c000011004101c00c01c01b1824820716100e04c100c1c00d4400914503030002e09520502e014800b181d14282c40400225110074080d5401080c00c00d250ba04841000c00600705444040741514104e000c030440049081c0000140c4004a42e9010300102c0c610ba942020819041d4406009030b94180410024800440c102400c2c0f20f004828041640e60b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 210216942 1250 210215692 210215711
    0x30f0c0503180c0d030804060e011a0406060503041515080714040e1603021201110415020708070303080a02030a1407090608100b0d0c1806030b04050c03011203030b0301020904020409 80
    0x40c085140b4100e01c04690103803c4840160f20744450418020ba450b0511501c1901c440c0b4280009d4250703210341804a62070003400041c613a480b007540c01d0300040190340412a040e103401c01159644800c440141c402e0b1103401100c1b0102000d644000c0e0251250361fa030078690b50300c405c581c604190301644551000720302c000400c145c908d000d11640200043d003600503c040e54070403040402c6100188000b0703204030008110791100394400c1d08145282c4c3c1e940b6030100d5a540d02e0b2400c07030f4001900ea80305240144200034000c1040f07200050f00300141ca4041d101d10751155034000000000e503000810b0341c01556100c0c034920010034500f0014070301a01c0c032a01d401c41174a04000380204100c40007490107190402c080303020450080e000c0125081855202c60106981d803002105403000c100307006a85106881003d00061642d078164400c40c41944101c1d000d10403900d802900304042e000038000c0b0005d081054202c1000a806544201c00f40d102c0600050704000f18074001608a801c40e510007141d4944a08160 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 210218192 1250 210216942 210216961
    0xb0c07180618091a09030405040e06180106050913030905060d4506090b0f0a0501080a080a0f180f06030b060c07030b0702030906070327080c04090201030f0c0503 71
    0x1410031911800401045035a0f0704e82c090402640d180c002209542c180106050301001d00484016000240003071014a0301540001e90b110411694600c443e2a01c01d40c24880c50018060038003107610050011409841d0b40100c1c440180780c20308120140a4407010005013510365401511040f500342c640010031840703119021003154400041030304c0840f400d0282c200002c0c4001649403942d02070516801400440c0e18014005000813480a4001c0f41d041c0c2c02c010810080000840c818100c0d0324081c0f0659903200e9401d50f5403090007100034480301050054210703940c4640070510302c080041c07a1644000745184001c529110158002064012401d5414080142c15002c2e40c4d441c000191442860003458144813031300e501c00d60000900a903100d90205035a10310030000d03160018801072400d651040149405494807401d0310700f80c05004024030a0f00c1d8116881000c250480e018100038022054003402003200511000364228113242d45c682c00d000341c041c800e00c12203001d07a251381c6840c2c0c0d607410144c610 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 210219442 1250 210218192 210218219
    0xf04080d0c02130b010f030b03030c07082b090608071b0818010e06030a0902060c120306010e0102060426070c08030d060e090c01030c0e0603041b060c05070b0c071806 73
    0x80701907081c2402009909039901507011b02c03815415150000d401d4000d100002d0541c03044c108401c0c000d00c148100400e2510002c1041c0f81c5989041c0c0200c24401c1e554050014010f1850f102a00842c103200c0d42000021b02a40006610043d54030f0034a802d041a0784109a2041c80c1ca0f005907050003011603107003600b0711018450fa52546090070031603180030700040000c525200041160b607002d52136000f07400071929001c094803d4121404192a0801410103500869400c2201d203640091480c2c1c90080882d40042012802690010590351059254a40c0d038503400402c0c00d008041c4410802c03181011903102c20803040a409140c014503038507001c241c001015030b400b580052402d07854a100340404c0060004000b4103081c030a0070301080030b013400503042d5140041600300710340100d4000200300411004a01e42c0f415200a034840c04e500a460704000c0f10705c03059000d0010016030040000b807094000784000760001440e074104464045440d0013071a403003081c0070f4803410100341e1030313000c1407080d040e40014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 210220692 1250 210219442 210219469
    0x2010501060e030c280b070615031109100b040b0408060a0213120510140609090d0207060c0807060603030207181104050f1302040b091309030c080f04080d0c02 70
    0x104900e50481c2c281c006601d5030302007030802c4c0c8542c005484030000b01d102c050f0040003040303c080307031030044541d1071192104c0c990007403074100c62140c5094402444448001900c0050302d070130901070201071109800380650386034080c0c0301c41c141030762301d640000c0c0d00c60f601c60043c40541482c42e48951118940943d140c0b909030040e002c050002e005020a024030184400d54104070780c0c40e81d40c500c02c203d900c1d041041c14003c0d014101d91149080c14603100418034000c0c01d1601402e07082e14003502e42d070740746907243d80c0350f070300ca10440c0006812003e0304100c1544500c00a1780494000e42c1d00c0c9144c288250341d04800c0b20010b07407044000d604401410000c202501c0d41c0301c1420310390800c0a01c1490810710300045184164081d051258040040809454071040742e42d001c50070849208566032a251503101340540c0010042c03074441c42142e03c841203041c400e400381050782545500c48920600c440c0d03640d80420f80103201000074100c814403001500c20380c100448030800c4407680b00c4001d452260b0042c480300e0040d000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 210221942 1250 210220692 210220697
    0xa020d0f050705031906090c0908060f010b2205030a030207030c0806010f0b030a180c1401180b030915131106031005060a0c0204020d1a120a020f180403020a02010201050106 76
    0x3802c102c00160001c0840354031107005240b414200c1411110800202030baa008644503a29081c8600001038104c0d06000030346442c0000c5403501c0e590403441038003001003401501903a170400d00110161040b0460150303500102c420008c07518a17140d0010a10b0700607084403d030016408528200300384102e81c10a02c01402d5140c010780300c10b40c144004510050398a104000c000100000050b454007440e501800300c881c0590b2a10701084481d00384829288881d025883c100070510100034a2503026039005408170150301c24014400c1e141032030051203a00010a2160103000f21710342111101c1d90494014450000301131142c038005140d041000c1141c01880c5140e008000c01c0062054241c004048201101c01c204c032541d40c0c1c1d950170030b800c98141c001040c009400a0002c40d661031000203940181032a050303040c001c513201c505032004000201c4443c501d6a140c03500050310f008050b0a10303c002c1c2d50741c1ca40c041e020302d44030300c2074041040800804403001e400503001968044215a4203009aa00521603803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 210223192 1250 210221942 210221951
    0x120216140a1e020a05090a1a0a1215020f0f040815070e0f0a0b0a1d06040608130303090b070c060b0307060212030a0917040f061b060203060a030b0a020d0f 68
    0x26a120b03007280380b0ba08a84250050401001c80843d924000740c40041e0101800211a504211f00050098101b00500010401c0b841c2d400c0d08250500c02101e000315500210510b8036100325444840c0301040c3e4511100d0700c0303902040401d40d440110340003408002d035900e0030386981d40c0ca0484c03294102882500c2445415210300280180130741c0c002174510fc1c900084451a00c08080140003ca00314900c0d4031400000c0c2c00452400140c0750821290000142484001d840400120303041042c64032840c040d6501080392600425009041b40d42540b1440c3c4c804d0800280c0307000710b602e1b0450151000c854100c001001c02e2000400c1000724000c1188040056000b007400d6810440c010351110b0110160340807251000c0000f540b0030038290014031503290400d4084a181d504030420401a920074056042c20030011000014210710561101c0d170041035401c3d5402141e500b0741d441501a42c40a031270a54008591702d004000300d410041c606000c0d9055000050342c51407100c01307010550750307000e81c5020480d180 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 210224442 1250 210223192 210223213
    0x50705040504020609060a030e012c150f0c1c05040201170105090a0b0d1506030201090815060103090203160e190b06040b030c130605090406081603060c12021614 71
    0x984003580c481700c800700c59160726a070251720300300c0040001c040e0700c10b1258242460000c0c24120742c410b103090361000011100c022141110001e555842405201c500c0596100000c1d00c5100000c0d820b80e00715006001c800d01d0070300b8030210213188101d0a0146a50155100148000c66030001c450011190580c80240220b40c90400040e200d0f0074000c140180c80c0391500c0b00c4c44102c2d60703024482507110740d02c982c0c42d192100f8101c01000080103140804c83c0070030f90107070010801d800002541d0040548001141d200f5940302030044014001008089030144507205000361441d000c032140c1c60162112402058003450800c0800c80301004030101c10084074517103a14450107442e1326045900b6100418902641c03501c4101a80d4038a1003201d4443c1e4150074107403000304031035038068010840c00c00115804c6c000561104240c5413110300b80720004580e1088810100006a0702c0d401001032800a418051448080032451a040c0e074032251868034103007074216000c0300304840c04651080581c140f000402c0701840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 210225692 1250 210224442 210224449
    0x12071818050a1b0e030a08040b041a07050c04110c0d0f02010510030503030a0c0509030a060f0b060903060402010f02010e12130603020406120203040204060518101502030702060705030c060c0705070504050402 91
    0x1c003d003504003003282001c0b441c60151010054213000d07076800741040d44e84598800b1074110b517410502603514a8124a500c540020b030ac8001522300d00c0b80c0100103080840d08082c200401880d4400007141c8100003070200000046c0140300d101c0d8010b24944a203001c04c6d03030310354000b42141d90043c034001d00e40c40d20072001d0001c6200003003503941c822000a030024924203028400d82d0180900c1e80c02c81c0e4148143d039918020888150010350401e060701100b840311018a2003007000f61301501d00042d070076038400c80009026601c07841c0003c0744490305000000f24144a00400350600340b181d0b00751401d544000900c400c02400d602c0085008150034a811814181040c00091080e800746140d8400b1a4011000c98250360300d56000c0710040500524003640480c06a403008500182158018181c8900210015800134144010201501c25234084c1d4900181f590801283c1c5e00001400c0e6007600c8188030403058801c0c100060b9004810030352545846814500c3c2c22450000c058022902071030811003404010384 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 210226942 1250 210225692 210225731
    0x503030a0e160b092b111c030c06141f12050d081f030b0a1802060405190e040503030f10050306010b0d09050d030209120f0312071818050a 61
    0x9250054007aa10030500c0b000801d86450303001040340301024a00b4080203800c0d0340700240200c40c4191240c403030344100b031030802034030051840c7d0f00d0561210141194000074070481150880d1449020000781140c217210512028050807a85119102c6540310f80c036907810928446100142800164600791040300d0f03480036203451000501d203080c8200b20300440c0400c1ca8281035884e010946a00d5202031564908100c40008801d07074540018030305e49203a801d062601c1e8505502512b8010b4001d0740391915103c248040d000d503904a00000b043d5148c8042070041d060790074540194011002581c683c03c020204036a6074001425145040f6007007207040101d0f44010610904403040c10036a9500c8036125038003080a000042c0008189004040c04d05901907055400b030326400a0590381703542041115004507a840d2540c0000c0e40c1c3c140d00510015010608800c0c1469100c51240f0302800504100c6010304c40e007040c9500061500c8140700d04500140c500d42c80340e96400720315910184a4121a40e01c41d40740c48 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 210228192 1250 210226942 210226949
    0xd020d020d020a12110103060b07030c03230309010e1c08130212010c030e071505040b070606080d0f0f1b0f110d0c0305060a1518090b040503030a0e16 66
    0xc0440e100c1d20015503031200c02c01c200400382c100030079a10a0452401c0f83d10445007002250220b8a44400807400604030015607039025450744400105445170f84059440200031070a800e6070581c3c01003c1c19540e100180914040c40c0c7e042e0001c20302024010000307003003448106411070b412407102d03600300c01a40c0c400105030b00400a0240741005a86500114015002040c00e000c4503600b000000d0355400d03810b0340403200b4000540107495400b0780352616040302e080e071510790034001801408107200c5200740200400c43d0910034200051f10382c0d910702c1964107103084c00301c0d01d00215000480e21000703143c01040740302000c0d850f481c0c070501014030310524075000351580d440075101c0101e1078407150400460400700391b04003900070700c503469880c040d160842103035815007c100c40e11b008031404a12680440d004a035806c0b07454400481c4001c1c00c058140d0b1450781c2400c1c020a40980351340150000c21039400405002c0d6010303001842d0303649042041c100954403104e90a185d0741d40171080303840388200c400c01c0e16002d9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 210229442 1250 210228192 210228199
    0x5010809030f0309010f1803020c0907020c010e0414010f0303111c050a0306030b010b0c0f01140138030f13020303090d0201020f030307020f0607050c031c021c0605030c0d020d02 78
    0x3c80e1a81002e00e8010800369251801041c648480d2583e0186920840a51a0322980c03c070741408241c0e000344100d16006482c2040035900078403e01c0c2040d0b002d1a041004088041c00000d803c00c29070720001407201d82a44501080400c0203800d00606900007000d00180c2d0f0350070b0043c804c08071008001401c60039618052010000c0100e4800c440313900c02d401000c004c5820030003840441d6101c640e000042d520074200c0b94031900c500c00503551604010700495254040f518800744041e864941400c8002c412513001e102c002020a071103003d00da54807824095055140308030b6686038940402c5101444502030985030f40e03099231840c0b480050783c000040319000d0000742c86160681059100503131412031320165400050201104000c6101e078000b0342888103480a400321102911020000d443c18481e039442050560070800242c2803604500300301052070346a00307500600c0e0031040d214004015428030107641c0b015403100d80810081c0780070800c0d45900c01c400c60300301c0701400007903000540514071503c0082c003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 210230692 1250 210229442 210229447
    0x3011508120702092202090a0c1b02030a12180803041d040f021302040b2106090103050703020409080906030a0b1002010b011707140d090201020613260409090606030c05010809030f 79
    0x20740016400b00405d1994064003003a0b060621103001c501030306449100074002178003d41030b941002d07010b4803000280340c0c0182c0604401c504640f5001c2500c040d440c1030314144950503000c40f498503900c41240c1c0082c174002000c1c40d00c850030724101c0b0a116803100580440039040380c00b8040407603480c1d8405c8220310740c1100c40d84504000581044040c1c06954131450030341c2e201140034043e000c41c032000b4031a10130b030302c80c1c40d104265104000c0046883c400e01014040d1f5200c00c100784014142540100c440600441159082280b0880092100d030300403115010702c1a155002d0750641d061a803010240561103000a020550240d40020301291359914080e51002010000c9100786004540003480e245140b1061030340da480174002c80c4050305105070100e0040c41080300007080500701032200b5004981c0074030586c1c215200e04044180d680040504824406010800004e03205081e11540c841207101d4100450901d180d420b00900c404002d034030480c1440140b00070403403110340c00b01c21103000c031003c034020030b8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 210231942 1250 210230692 210230731
    0x10216150c03090b0d0f050f0702030a110c0d12140c0d0c020a0503030301061701060f0e010309061103090f06010504021e07110d140d18060f0c020301150812070209 72
    0x11510702640c2d03c6245000c1c0002017000c0c500c507207a001080544003aa006011340d0304d9071496443d0000c0202c4040c40103800912890041c180f19204d5100d15011304401c0b00c1224440c00c0000703d0320070300c0c210100d032100c0520300c000700e0380350304801c8030f885110303252441e2418000c0c0058035a07210214030340d04a0812201c82c8440086540d104400350241402174216a120341e1541000790007461241d031500c2070b43d5104400003441511855002c0120740d11a0f440f40740c0790000b080198042c00e01c000d01140c0c401e485007000c0341c03400600405903100d130450000805003a940e000c0600d0400506810460180380100f0105143c0e1a080311026030500e504c002d0b1030b80d070345041d00b0004084d06141c600e2a500030a04103280c0c090006844482d0350500d208010758458600c0000c4c1583c0c0c0340429015031080120b601820083c16001d5507003c080042c0038140300c090a0010360000e800c5524400440e29020003480c81400000c1c010071401001e11300030b52010b4a41401da40010b501841c00038070030320008010b280da15 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 210233192 1250 210231942 210231947
    0x21070522020307050c250b0304050a02030f0c0111070b070305210405030d1404020d060e0304031a0714030f16030f090302010b03121215030c030703060902010216150c03 74
    0x4100c0c20500c03204540341c2c02d282400400a40c0000c80d82030f1507100f0b03a40d611000c174080e4006000000039500e042c402c140d00e0503400c000b880d0001441540d60f406240b0080700035880c24000741c0f0480b014100031300000c0c0494000036054000001c114000e40d40a0a000d000c0200110101c402007501803c01d113841c2c1440c1c29500f03809004031011810200c050b01305001c200407000001c0e01d09562001c5080c065001c1d0740049070a000d400b1140654044011020b074401f26296a2014699032070703140903a468240c07240c8038010482c03120410701005018220801c0a9142c1c41441c5905540c0c08215943c030314201604c904880b00009003c220702d0456010012083c14042c2e03008400c010302030b100500003464103050282c005c0c8950803015000340910025004014580c10407104c50010004001100c1e49642903e0219074a04109181e0548240c20036102e03159402c122410003503116242c04a0030415603c00281801403500002400900520f0180000382104103020720071a405c0c80e00c44441e542c1070604 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 210234442 1250 210233192 210233239
    0x1090c140d0c0b030a050a050705072006040605040305010b03010603150506030703211d011d0406121b06030504030e12100f0b0312040303050406080703090c0e06210705 74
    0x78020111490b000860000a801940c4900101c0004026a070740784480082520011110140011001c224a01c0007030201d01c1001100721411001c200000e0b010349c0816003a84c45034008401040002c0740820070844c09000720001850180c000780b25551450340c0c5d00348490310205c00c60416a40380d10014065440805c1400c0040d90880007880b506080f080103002c00c4414090401c00045c0701d0146894030240d200441a450a8103a4550300d8428880d0b4801d0590b1840998a507882500e4a100240104c8410601d0301d40900480115851f020000f00f236040c0407045038000e800381401d01c801c001c042504101c0d01482c1050645108454011251185090142018117000c419207021203000ca54400c5503c21010820700380c044907040004000d0201140c020b030720005001440410040c09013a200c0c00080340c110b1040e040c085400c0c0c80c43c1e965030681d21140d80101e507000705810200312152505c0c0c440ca5603000c161030941042c0148800069803106242e0284074001c038a11080c1911040a40c4107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 210235692 1250 210234442 210234469
    0xd05010b06030a020a030b040b13090c170f0f0105070c080a0e091609140a0b1b01060308030a061d06010e21070e06090106050d050c091215010801090c14 67
    0x2242d5640750025210307000390800c0003e000000e103000c200d040c140c1841d100c1c2007410721000345401602014600300002412032003c00319400c103412640000c2001043c1080c01241c0c03030340d80c050303c103054090007014a050399800e1000c0c00d587c144800e04c91f1050b0030900403039201e80c000300304036902c00c008078003030b203502100402250704640207004001f41d4402c2c03c03107152001e010650306d48a4842d03950007110074907240850b00300e61050040008100c1d00d00080003c04c000300203216519046c070450b010003821901c85500c280c1e10300038000200f0407480a244592806440c14140b880b1040141e1780c0111103405008028a040c0441d90f20090229660b1803000303461446040746241000342803181d001c1d201c194501c11000c1060039400802c03028a011400c41e0b040e0340c0e40760740d01818501d104403000c01420f00078100c000348841c10007081c441d40d12035808460b0840900303c01016494203850b2400c0380c03104c0580c06608540d140445250028a20000300d804481d41f2449152a0a42d241d000501c2029180c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 210236942 1250 210235692 210235699
    0x230a150c0f09120303090519020406150219030311070302010222080d08100f0b0705011409060a0513020406030605061003060609050103150806010608160801030209070c030c08030c041a12060d05010b 87
    0x6044400140d802d4040301295109440c10702c0702f41d03900c6c21501186ca0b039030140c0b103000d600550030030402a010201c03600e501e40c0c080d1901083c1d04c6100c060740d070300c03940c020681500181d4000075202c0c0c8094440941540d41c05071019409021485c0540d11a00c40300d59412200400c4880c001043c0503821280d002d00180103850031000689a4901036903002e079100c104101c6465081c41101415001ca540b072a038422401e00015000654a040c90f550041c00002c140400c2e6000c81000c10000d43c94a111f0440030310300c104400655030508034100892841300e82541400c040c200041886078542c02403040381100c400782000b2075021f04c052001c10710319000c4c0e08420b10a101d54000020300d0b99008207090302402a03d0091440e161602034115070354a42400007a4102c40c503540401c0740c0030301c41e0139120041d40c0a803903c4c128911465507101640c2c1c1c030959250540c0345010905000311a01982c0e48100380c1c00040c0030314600080c0100c1401c44103002449144645a40210707541446070a411409450000a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 210238192 1250 210236942 210236953
    0x30050702011515030b060301120f0f0b070f020c0901150e04020910020105010f0906120305030c070501050a0b0f0108011802030c0c0a0614060405040b0103230a150c0f091203030905 79
    0x4044103c014081510380100080c1070030700c032824030b06181c0c1c1103d05842026000c11041c036031030346560042001c840412250482000c3c00c91020a07403140046008102503030740d06d189000321101c02498801c2c01d480d924401e0755135000420071010700e40352035506039000d4205403e1007060f003400034000303009211000d038001e040421002c224590662002c0d041e100740c49040d41981e030311440340c14101c0307640d8040c03603032040070424110000ca400b03500a5a0b200300303086075603403801c04103684050940c0d00581e4100d41154540412440900c0d01030024403c0c03a40070f10b4108075562420000c1040c0824548003090441d60010100302481115400c03501c00c5c101c0e00086070050b001d24a00500101800844102d0308520341c4007154051409010b40b40c06a50890a011156425078495a15121269489610220101c05000314a603400e10441c110607000c1c0302d6130b90b88000200070340401d0b0703504d205040c4100004030010307080c0c0c650460151703001d13104922800451441360380b40c1035005068002c4080c0251084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 210239442 1250 210238192 210238199
    0x1020a0201230705030406180305030f130504020d0603020108070f1205060d02030d231602010807032318030306010207030809150412020301240512150115300507020115 74
    0x100030001c55103c3c1c1d44232694503080c5044007c540c8800c0c0030081c09600b080025a00c540d10303034005000c09004509a95900598841c00642242c0c0040403180c4001c1c0c440000b0001d560704404060b40c8200c1c942403840e58400801c0e002001a141030980c2a8031070707a640046955074903400346d0741d2a1564080c040320f150f000e035854090128070600b541002c42d10700102c6c0c41c032110403a21007500c410401805603104d181409500645806c0d10040000d0101555112200c1c0c104240c85042da400c03650f6103400340c0c86030030b109890040c21105202381000580c010014090981da0008941c8102c035080001241c540610f41b0000301d0b100c0303541303000415980d40803501182d13102820094020342c0b403007100200300304007803540b8880300500c0202b150140015811410496803e250006c04d4004441303006450311454001d6286100c91002c1e0030100300b004145420069203a080780d2220400e280d07640703002210804010280b1a0320741c0e00103160700451f48030008a12028003d4100360950040d050f01c030300051f600d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 210240692 1250 210239442 210239453
    0x19050708010c05130e0702010e19020102060a050c0304081605010212071106090d050a020f010903050301051306051509060c010911040609050906040204090503190810080c01020a02012307 82
    0x1024040d00c40316519202c0c00784000c60140f41200c0100024080c104080c91400c100c0d01103840005020000f955201c1e101504110307001e11170190300d801801c03807140c1d115040f80002454154020b0502a18034506000c3c0702c5a942000c3c141d0340d100358000c82c000d40d98805500b285900702400c190003006580003098180300610303170f5070903135202c2d5500750b8404c4028841d000c1e0781c565807501036810702c1d143d400040300b44840300d1140004165000d01801140d940035003a8298608580c12040240c2c00242d02000602151600101094080100060034409a814900054800c00a80703103d210704900008202e2510745400090b2180720002e90003c0103a41c4040c02c2136000071107440e605078440c03454400c002c10100498400e003401800740c00c004080030340c4e41d5428440145452901031700c0600c0140312500c0f807001c4c03154203040500b01ca555804803a0400c041d500205030b0042d00548a940c100e85040da4035030f41c0c00240356418540901c2d0104200d000640d455002008a11181c1c481c1e40c000184c040c03e00c017 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 210241942 1250 210240692 210240703
    0x60302040f0b0d1407051201020306150f03010e040c170c120a230106170d020d0519080a020409061d01080d08010e0901140a0f0c030204051503091905 66
    0xa0003500d051000144459a08045070b0341c01c28001d82c403100342d03051407000c1040f00300740079444036403038017103c2d021500c0303174005410140480e50b04540380e07400004111950030700502440020107011042030404044640640d086c2c0014010784c3c281a107100001001d0042c85030031100104448046ea40e0001c9480405907117602c82100c40600440c003c1380c0c1c0400a0400040041c1641e4109465407103120000d00100c05d40c0c03075103a05101466484201c081800784e150101a1a0202c03000c004240e400080d81019040400040c0b0b07410071b1100501c00c0005d500e00350003c1503007644180c58096010343c1c0700c01c0c4200082c0642d4001004507840c203c00070032140166a07120300d404404041c401016a079400e500c0e544c580c40404800c00281a0000400c0211420241ca0740c00c101c43c2000812010302001c1c4c4400c03d180111000070b6080d498010030901441540b03d0355001070040d18040d0705d407908000210740c1d130300800c10020a400d840000040d21042041c40f503454602c00348401c0b071580a950b401c02680c1c0d035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 210243192 1250 210241942 210241949
    0x20604110d06110d110c0d11010905010507020d02060c12070804060e061e010504021306081008062d07052706031314010204140d240204231c03050f04080106 69
    0x4c0e107001c80102850044030192809a501d00c40200322642c1c5100b42142c7c0c00d0248002030080c0d40d00c07001e900340010000c1c000c0c80e20903034059005203e800d00b100741c001d02d0800003070031414944c03004000700d00302203843e1203407030307034001700c070b0304000489858514100000b09500035108086014900620810740d0140c0606c142d440c1c005001c64000e41d072610208400c900c148040280342c0301c064007042102c03500503c03100383d0100e0701c8405034080c544c0d0740764003a0421400300c072092100c0e00f00302e080b000f4901070030224107202c204808081c1e19030725118a003e0428031807640e10030380032050034001e021941c05281003004410006048141c41c2c1c101420a400301891240b0121460115450f01d20408481403003660300b01c8460308a8850322140f44001e00190390207140c0f09860510004080505140b180341d010710360844400c000507035462901081110070307000881d2414030020451031145c0281e41d030850b21600d12848846045520015103025079030ba220300c090f0b007054a00d0106000a5684065211100300c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 210244442 1250 210243192 210243217
    0x6030b0f040b03031306091401030b0310090309030c0305030316110c06030603070305070e07030b011112030c090603040b0709050406050306011806050307030c06080f06011704020604080109050a0204061401020604110d0611 97
    0x8102c48c2ca0015020b0b00c0c010700c070305500760344000103003181040c5980100507003078024180219800c3c1c89855014095059030401c0e01d160b4000818008000304c15464100b01d98000d1400002c0305010301e4050792115141120310784282c1e00400400e2140c0e40c1400300c0380080d40c1c001d0490306090b03503410390b140480780d0464480300481c1c40c11032401101d5018940986804800d00c010309072456101d444000d141d000602655002e010501420210740c445100640c0182e0140b0756030159031034210b50041100056810290099003422801c004940380010783c1815503c40c0c50001c1c40d221100d0740280000d011582c03040344c0c903121718a4000103000303c0001d22000d5a41c0d07070380c51900e00d54401620304084402524030a00041380f00e000f403110104071003506078000b8802400c0520785076650b0381c40d41c01c0d02c0640000740e41c10b80043c0b199000310b1406100b21401000b507015003042c4141d400001035100c42d00104050400b201d20400c00303030a540c1e030390700780c040d8035a101e6410000c0401800d141f885540024481845 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 210245692 1250 210244442 210244469
    0x910020c191d04050c0a060503040209010807181107050a0c08120406050301030206090d241802010e0904050a0804240e031c02070e15010906030b0f040b0303130609 72
    0x903001c1d0000d4a800036500000c15928900303601c260030300a8288010401c0c0c0700790042e03005400b0140d0358240c4c940c0c0100300c6661080d442e0704090041201c0018180c0c0100002d5010348400c002c1440c08100030109103400d55000111985d0802a184451241500043c0700c2d000340700703144081011302e012540668101204982c41a01c441c42e400e03100703100714082c1c0c9002c01d07000d100420040c40c0002c01000d07074000141800c442d80c01d069480b0240e450344104901030071005004461640200c03407013000c0081102d90901d05650300c180c0c00103811000c481101c1c900036204030000405000c0c081000d00040e5a02031812540c456903403034029001214003025007080c940700500140664401c03041c521105100a0203049075028051512590540400e041425401044800507428a03450400c40c03290303804003680e00b07604c90130500040030400190040814585041ca000030b00c0d88034079407003c000e000e00b5100001c1d54203581001071300c0d50080d0b412590840f04101d5011030002d52040748c030f90854000d21103880 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 210246942 1250 210245692 210245719
    0x801020703111501050607240204060e040b06120408040314010207110f090a0f0b030a050304030227133e03190809010e18070f030506030a060b0103020910020c 70
    0x81c3c0303450042544200ca98100c0c401400a86403160080c0304440c41403400c4070300b8501260141c08070300c549500c1201c445030301040400c002e507003002500f0004941100d0411001134900000303141c60048070b022603c0803a6000c00101041000002c031409035030040c4003204606601804907010b94010001100d043c8042c035030b040203d00b030000d241ca042c02c80003403270700c0034550754140031000820b0400505110386441d00502e0066480c01c0c1310b50b001036801000039541d00d83c00c0d801400112503441c81480c5840002c0c26035110000d60110006400900500400344803000d10b00f0420b8191000306000d1940091074509075004603088048546110109003035803a1f820541401c245d00d0ba08100c0404a0f105c65040000e40082d030300d20018600039a0504025a0401c1d40d90046541c00b0b40d07280c0e071040e1745828501401030941c0c1200c5080150704803072900b400030f8500000480d845088003180140720f0307901d51203190300d00d030700131307010341c1c00c2944080c0511840c81c4821600030354a5021220081c042c000550007030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 210248192 1250 210246942 210246977
    0x1306060c020103051f1d1e07030e0705040f0b03100203060102031c110c0a03030e030f04180f0e070f0e0702061612050f0a05060d0308060105180a0801020703 69
    0x4219249500c030300c284210190010360240078024001c400ca4940541c0c001160301d0b0844034840070300700c44940000c07030f03003031003203000500340000f6009003513a001d035542c0f80700c00390031f082c42440d8015014913001c1891a00310185503c1d0000d6600060782c081c1c03c08500c01e48141c004da01c90400900110308a5140312100c400c80703400c900c019941d540c0141c02c02c20104a41014411007a40a00c02000d40001d20201607450200c05800c1503912101a40081c400f8405140d81030003043c0540a42001641c03405502c0e5101060503c218815a8000c0319090324040d0150210741c0700d110303110580b0405100c0003000c1305c4915120f1350341317000c0c40304800c1c410038000c034950201d00701881c842c0300d06400034501c80c2c6404126074101c100a5848000708840d059815a00212602840b409500d0008244c00c0320b00f0641c009400b6100d0027850240610400418440400d03404401103400103801c0c00d16690713502d40c0e9501b011811082c600341d01c1e04140440070000f0301000541c001e0041a000756101101c100c3e442002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 210249442 1250 210248192 210248201
    0xb040506010233041112061303031e0e070602011404020607060506150c011505100f201b0301140915130f0f0c0f0b0d11130b030613 58
    0x40c01c0c0181d10a00701502c2c2407840980003009825800980c060403415a2598482484100ca007194074030766009050020303062101885480b40306240203807035640b826603502645884072400c060105500d45006d60942560407616840c091240e00c0244007441c1d070f00303000340c0c0c0c0da440b1445940c00540c43c1100e07c0f0010401006003d004650003444186445029200e074009000b02138641036202c6826038100320007800d004020a8042d058000125050010b000d085608000c154000b41c040da503180c15414a040d40a003409485c24064142104408544401d01000e0301d94014185040e101e41c0382030140c032440d6081f40503007004044000b48480d1261a10003c039000c0240d44100b03042c1e104196003180107006001c0107030b005206081d003082080d140d458200b4006e002020036180b82404c42100d5040c05004201800500803c60150300c0c00d500d00b000001041c0300301c1c4070b829406d65607000300c10001d40c11001107031380a40c00c24002c04d41c0d0b0764582da4060044c1d4020b031250723441010002c4491391441d581e07014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 210250692 1250 210249442 210249451
    0x16080d03020a080c07020301020f130f05010906020c0120070603090b0604020408070314010b0d0b07020607080c040603090503090901080d120c12020d060e0910050604021206060a03110d0b040b0405 86
    0xb903c0b462600c8621400440784c110201c100d07490754081c01403d8041044074050000e40700c2c80190301005c5032501941400c102c0860f0405e50410aa00c40c00b440003d4000175100c100c05420300e810241140122210381407580510380546040c001d522002601c40d46c160000d05059021f0f5040909075100d405c10082203208904c03860b0000c1d0000314040000c100145405840402c01e0400031403061506400030341c2d0002d041c002243c03140211002e024015038100916540700c10310b420546c1042c00c103441c0e031486502a40c4125402c140c0c41d03090702c50400c5801d0065941c0e8080283c8100f0803961a11042034407905440b00000003d05910302d4901165803e000c4c480f0790500588407087c506d072500084c48040e61010151a0702c40d92521000102821241505482501000003814040340d0400281c401c4d00c4010b44a0fa10542c01444030003212002100000e4000404a503925500e008501095002d400c50f4100100a0503002c01d00c1184104540c1201000020468042102410090800c011640260b6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 210251798 1106 210250692 210250697
    0x1060f08060906010905060703050409020c010203040512070812130f050601080d08060616050a0803010305061801140f0606090a0312030e031c05070e0316080d03020a 73
    0xc0800e07002030040314a5002c60600d81c00003000c0d50118060644503600010b1000e0800d0b00400803100100700b520419900c40369441c10145c000c0d0401c55080d80d4900560b407181e044104c450046480c00c540c4604030034100505144100021b403c010318100b21039004480c007001096880080d6401188688001e12083d81001d001d00d081002c041c201e40c0910050205101700c80c0c3d07401d4152036298081e00800c401c85201c0f0b0034040e14200c03250b8801340800c0380000001c000e014022600512400c0407055540c22040309a408900305c41c0c24407100f0b0840858000418110b105036280c01740c0005008148030b003803903401400142c0c1007446a20880350300000a1940a5558050048403540b25526020718209242012045c810b500c09820040a5590b68800a03904078040c09101200c1100a000c907030a00c0c80c541d00f0042c401526000c1c840c09407082c1030740810514868021100c02d42042d6 = true := by decide +kernel

theorem cover : BRFrame.Cov 210071942 210251798 := by
  have h0 := BRFrame.cov_init 210071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 210071942 ≤ n) (h2 : n < 210251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
