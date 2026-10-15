-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4298
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:09:49.523559+00:00
-- url     : https://prove2.me/submissions/75295e0a-e9aa-4207-9ddb-c4341a97025b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 772841726 ≤ n < 773021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 772842976 1250 772841726 772841731
    0xd0e0d0e0603180304171e0c06250209040302010c17131403041508040c050d030c02060313050102070b090105010e04052d19050106080705090115021e0102040f0e0c03 73
    0x18000c00d082e0220f04048501e14003c95010310f5100340003600345c1800c444007040d107000400d001c04000c0640c0c402143c1164440701c0d4081c500d60061010f02c09080c411140c0710381003081007040400028940d0700f41e00810301c1d40c80101c3d0240c01503034513442c8000d18690300c407400b14040301400c40300149a080030100c800510204103c0588207040e00d60036094a10400d10494008080d00390300d4001c906544640034082241c2190240e034610180c5100003141d040454040c290f00c0c0e0f0564500c9410440d82d0700700201908050855807100c0e00b403003440300c0010001d100801801e0b00a02403145580f818515050039514145c1100302c1c0392641340c091000007040003940c0c81010507003e161062241c1c0200461181d002d07892441c004611509035a1103200d070102c8990024030b03019000a020441d103c00d03074140c1d244454450345401001010040140c0455a524a000e00e81c0600c159500c1030700b015964210350590b401c050340c10340d600040800c6130301071280d0808000c061550544c41503241a8a02c00310b40d0100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 772844226 1250 772842976 772842991
    0x31b03020a05300114010609150c05070510030b1c0203100b01121a010f02031e160203011112010906061e09170703060b0406050a0b0a03060b0d0e0d0e0603 68
    0x510306030300c0c10300040410009003e019111040740c4000c0154000340030700705002c4000950030f600c0b000071480512420003142600d510004001480c015480101c0d002d044006082c1c2d42d41c0200c03100410a03030f5602407010400d016a95000c0b410b05070000070802d15218900304101d036259002d04c00c000580b03000c60007903402c0d80000e4000500340300110040c0c0361410b424201c40111441e1400190100c80d4950340e16403040343c01c0c0c2c2d555034204040c1509aa4034498020b000f400d54210841160700c0740d42c0d000040c12104401800050b00c4410ba40c046030955020900880c074002000c0307080218054010301c101d0061900190501c0054034002d0050082003c100940c0c031038040e07d4015560326805407034004020301019540301c12084503601260b07101d40581c00200c0c1d6460038014070300340a03d002e00035070080c1c0e04001c2250526616100485000740c0c0710a180b10249030700c4400004005104002814515030740702d02c0172800d10030740e005c05414001111805401c0c008107144440c0140c03106020b60350b000e0790 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 772845476 1250 772844226 772844239
    0xf110d08010608070c05030f030403180620010204080f030406140a0f14070c2409050a09021e0711280504020d09060504060608060732090613031b03020a05 68
    0x84c0c3d000c00700c540e1520f140c0c01914510001580402822403c0c004520a034043d90318103007491f08042e0142d09003090351041800041140c00c90714401c21300d00c04020039090086000510785562100c1260178403034030b0f00700003810383c00106041041540108540301d40e1035401210b68a0456085005002c1511540a01040000703601c4004a082d07800011100169004a01c003082555500e03044942480c000292075080c4404807684092a400f400e03441d400d0750740080200244505008040b0b00a420148200f41e0725006010582c011003203171001010814041c030380840c00c00340c5090032700c20b02a0401ca201450780c59a40200270844100900368010344104490140e83e4104044c080350260002c140090102ea143c08140001c20a0650103081214a4141500d01030f6980b10420381d1034403009a00c0c000ca22a801101040200c5802540c070901d20a86002f541040b400b034000c1151500140c121520300404140c0c1070040c04000141c034410104500141d110160071a4007003401e4040c01d126042c010b90 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 772846726 1250 772845476 772845481
    0x30a0606030330020a0c080d0f0b0f09010e0901060e04030509091014040b0102010b10030b1f0219021906110106050f03150405240f0c0f0403021e09070f110d08010608 73
    0x1840360200880681d08011180e403523030286011940280179510010010500c2c002010b1180e040071611014035000080c01f800c2c0eaa807034281c1c0021001e40050081185542ea880c0c0458000c07001c00900d40103a00998545444468110600102d180090014410a0320b03d076030421404440c5004900c0c651030070b40d0701281005002005030b01600b03800010300d41c44145101c0481003564103074410032007440204c0b035091000030b035503544955680316282c03440300680088100310100c1140c480104d81041c40504030030540d1030801500b03040d444164000c2e04c0043d40030f03166040040342c00d01030b40d4041c0108940080f01402c01e42c1c0003903922042008003102c440e0f130b050001000e007c024002a2030450200d000d449290500768090140c0d0242102c040c00f11140d0704011903014400003080d140740b60001c600d1145003506540812140c0c00900e00da4010303155454280800c0c1d0f488811403e030103020152603042c4a48030b06480500010308007084004207034002c180c04070019501c402040d0440714079061015458 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 772847976 1250 772846726 772846747
    0x1b120f0a141f08100b030106050d0b060105070507090911010305360c0d0f260d05060607060c021b0315010b0a0507060204030f1205030f1b0702030a060603033002 71
    0x4180c0c1d01084150040c0c003044d9020402c1ca81001d03c05240c2280200030a644036000c1140306510f4034009090000110006461540154024400386000c1c0007280d00301607449103098240c07100e00300210b41140291428480650b00342c05002d400031807150032040d0092075410000d164000d400904074040310051804804004140068804144c001d0803130717040504281403000321090445800ca880702ca62425031880c101c03441e50300d041c0d031400740c11100d80307403403810305843d1301801c2e02031304440d8400b008001110024000d4424560300c800b0300c0d00034003d0300440d1201c000340c070450030585600a40100b15040a68038501169905651302c116410341c4a07a0722540c100e80038050100001c211920006021050100303c510703440681d440b60210305d10140106400312001d020603145082c207a0003010100301210070030b9141d514a03124000d202d5060061640001c0e01d420580501074404039034512003072060580c00023404144100300d0103420900c4d0b0100020162005808617149420f590120b1112140b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 772849226 1250 772847976 772848031
    0x209060609271f05040b06120703050f1005130c030e030c0604050706032903101d1b0913051002030405030a03050a1a0103051b120f0a14 60
    0x4540c006014100c2500c1007218075103400122100c00492200e04000040ca45940200f050300110501d004078a0b156107000700703102c0034107005222954090024840d42d0140700140a03182d21079107190350041102d080c0b82040d014044005090701404100d5100140460303103800080d60040300c20101c0006a58240300c000310014441c03444142c61600001500d050b201200281d101d0185000d070082e22050f944e240d0050b4100d840a41088400074034501002e200c04007141890300c4010320160580f602d041c0808814000c030b41d103161200759011030304501c484030b2000030003103d0025000511030304a100360901c00100c06c140003c00c00d08132081000e00c400d08110092290308810b200c002020741d140e09080c90f00316120740042246200003032400d4000303121580c80c2d002c3c0c013071100c00d00c4000c2605139204200460141034000c1018180540c211030698103d80c2410041040b208515100546810b0041c00004100c0d00034003501d008904000d407500001403101d072283d400c002c900c03158420780c01300c61056810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 772850476 1250 772849226 772849237
    0x6060702130f051e06010c0b04260c01020d061e17070302060d0c0f0206010510140702120d0210050f150f0316080f0f1002030601090803030106050702090c1602090606 73
    0x5009041c80107015649404c0c1c1d0071440c0380d500900c109809a554107004645140302203034003400f002c400030045004910108159030482400c038850784072440c3c95401014483e40f211012a209a50001c1e401c0c00c0c02c1e034988507000c09006809800890380c403441d00803030581c9181d8092409016150507000201d85c20421140d0011540505025207e428103d5040001c0101c85d24000126002a091405044c40400d809042c1d070002001010b1061684100321901c0c00d01c4120341c91040001c00c500d102507900d0016081d40404504010700040400710402400c140d02d42c40003104090502c0709100c9040c6100e482d150b80003da0400019940d108440000d940001c5070300d14607050f009a11220100c1000103681105503081c1004035084a0580b03140a42e0311120740e418a01540c0100829181c0f402542d001560040c405144c40001961101045c50039a8002e0340203c0c0452400242e800c11401e01020803076005620b240440c2c01c2c50321080700140300702c4ca8120003d12600c051340008081d5926a0140c40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 772851726 1250 772850476 772850501
    0x503030d022b060f08010c08040b060d2415080a0809061c060e090a03081503070503100507020c0f030309040915090f1403030106020d050d0f1109100302030606070213 73
    0x1e0000880b503500740c006103e14062180074008a410201e603040c2c050041c8020400030b40e5a0120359521500ca001642c6805489140d210740c45c030102c613001c00e15022010a80c00d1601400101c80410f035410103046680107032a80918200340d0300c1c100f0120ba4041003544000b60090280c0755100e402030300107601846541c2000c00d28410480070911031000c640d120314160345846060450a864a40c1d030b450343e641c0500e10050020b028480001e00400a065a41098070009000c82d001c2e65154400a41484403c5030300d44074240d6202d042100f80340d41080b071003100b90b009980e070400f0004c40c030300801c1c1c0344d2194120b414005d070b0312231040100f0400c8908030310701c100c5000e5104100c441082e103420f500c490384000d420b4801b19661000301d01240e00100880341283c4c855001048045e54600041d00c0316080415058402c5541d4003049542210070f001d110510710070242c200390f8034088801081f00303000c142d024140405206100b00603a0744c440400b11040143c0480300210100317641c4040901a03d0302c0403120 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 772852976 1250 772851726 772851787
    0x30f0d110106150509130513020d0c05030a0f0b0f0708070818030c37020d030224010521070603091e0c06170609070503040f0606140a09060503030d02 66
    0x180c403c80d500c540a004a1803007110011511007019a420307003950002c2d505001c481a5105c4a500145814803200402910404240000c170350b8450000b81001a41402035401818100e080420448220f06480d4811406c4050310818103101c1402026050000c0601e03040c0041203002c5a40440e03501c552101c001d86103821246e9800718200060703140c40b04e40c0250b100d0298280c5a9041c02c1f11b44000c1d90208010383c80001084001540030805c900b144004140c055006040803814440c80d01a0070124100c4058424000795140c9018000034110401040b80c82e08602c0d144038005400120f001003c654280c600800c003145181000300341c9110036070240740f800c00501090400c10408034401c8046414a40f1508100c0d1004064000ca00204031822540072403075800080025008102030740d0860301542600028101c0ca80d901c600300c1e0003a400120000301403445a440d0b5161001d850006008010010b0190500c0c100229549005003110303881c9041e008034050181102c800079001d140340c1c280141 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 772854226 1250 772852976 772853009
    0x4050c0409030216260609151b04030b060109050f0a171519110403080a031a030d02060406050603030705070513021201060e1504060f0c11031e0c030f0d110106 70
    0x14030310029540e840c1740c0703400c0484001c14180b110302042041c818901c01c4043d00d01302c030301c8011038a1005030041c11485500103034485505548204809400954800c121030307a00ca0a0800c0050310b00251307644454815140b1042202644e210803003980d04650403500d10881041d410b03141641000c0400c070014040f05191401c100d69048040000065028030351410819a2a5030762425002c3c42140000b400801040160201e824460752010249920b503403101504018500006406c140c8110204c00040e4030110910050008512030b803a001a005c0307000718503100240c2c3e01d15464840501c0303050300c00c4508801d003000d90001c41c1c04641559071590407892066840d03401c003070203071720702d910f04280103c100c071104001078802c42c000c40742a07616a860384005185480d10403030320882001003c4a40c0e100c5480d214065480406c4201c89000304001d6401c80e040103155403a03e080c2c0d82c500131a11a074040041c1001d01e1201107001100c10a680c42c0a41116074420307030700d90240c04198002012504d01a0702c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 772855476 1250 772854226 772854239
    0x21c0f0f17070b1605191206090c020105160914010e0f0414100501080c0d020307090e070504050411161401090506071707080c180112050f040c09020304050c0409030216 74
    0x100e20078038200d816408030149100017124a4002c4400300722030050864441d0329a02d004450003120071898000100307a003901c824070f00098400e1840c2070300150713440361300b44401801050826035000c0a1460322518840c41e10a002507001d0b402e40e509410307c00b010844500c07d840310700c190f03004908050824130092040c1c809954004200b103502d0a01c8282c2d40b000400c1541c400c000c00380c0100341c04140f56040050904610000391f20162103441400110344d80010460a944402481283c1580b035040e02e07070380303894280001e507030301d40c1c6038911203590030810303202095500355060300301c1c07600034130490a0306807911815401400702e1103010b0300601c1060300b0025250750020a0000c41595811600440e494800c01507804031000e5812104203d002d1042400c1111241c072900002c4405240444031f6a400d00e9401d02240c41c240e88101a08a864013004280b029109680c802002661021865071800780c6a8548403c4010303a078604c00c2c0c8c0c40e01a00010b261081001b003080d840003c83d8200030301d54926 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 772856726 1250 772855476 772855493
    0x16030f0b1c0215070317060f030715020706020a020a0303080721020405040b091005060c031b0a0606050603040b0f190e0d02010b102312010602030403021c0f0f1707 72
    0x400c0380b080d01d8407001448400c50f03041c199800681e0588800b01110140c02c450004558000c0c00c075500326403000319492031030b134041104c58000d2080710201d1400c0c0362a01c2e0020300300801c50700039506552182032002e0040c1c9616116604a0341c25240100054894580c11944840c1501d014540b5206485100c0745001c43c0c1e43c020300498608071800c0041260000600c0701080c0100ea1480c10035040581c10021820044000d000a000d414240c1e45031908144102c10700e8040d18101070100c1e400003035a40701f0020f86201c0d450191004450450440c94256940404500001c00c84000f111601e808601441c0d402442c0665510076101e0a00c1461400070369542e03078580c403141c45801503003488100b000f1403d0903d40342c0b51043e27681c0c0d141e0f060800c542c04a003111200604000c00140e5003003228682c1d00c641041d0150182c503699000d5661030340b450041140048034071503c5c140c500d600d482d2010002e1003103049034003070303d5100c03030214020f61450400800c500001a0340c0c071940000060b04004020030308 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 772857976 1250 772856726 772856779
    0xd201509030d090302090a050726040209091507031112160822030e060403050105070f090806011220030133033f110c030616030f0b 58
    0x25000ca0342c2d203000000b011141000c86101c0650440e0140000c10316240c09a005203500407902e00705031405e00203013080c00d000c084500c1109001a50828141300071840c203000c410f41c1000d224402450400c0c1380f00541c0c040350714003800c2c0209055442030311110265a8405503603000300241c0003000145031080308464000312400c2e58000140c9250002800f44071640d03401c207110b03590090f0000c094400d0b543c00b078811610221804d0350210b41031000000160007401203520680655540362014042c0c174101034080c40d41608404041d4024500500071601a04944500c00e81c0080e0100c0341c074a101071003084040415140b070750f01542001c03d10088a03803440c0821001c80410040340d4030a60740c2d0005c0080d040e141c1e00004107503968603001080d9480f40340c000700c0302c1c0c2c160f020507203140403880d0200b011229a01104070404a206140c90681402c01070001e80702000d000d034050b04540c036121010990030800710321104285a9a6011550051269030041c2c0c1064005081840500740341d170f49400208025 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 772859226 1250 772857976 772857979
    0x1501140913150b0604050d050730030f1806021e1c0c21030b090a0c091701020f0c10061e03020f010e180a0c0203090d201509 55
    0x2500c0428040080390300c0034900c00d0742184a09550301e030842c003140040c0c00201c1c15a688120140030101d41c030354403850000142849540148a000d01e0500300d005401041c5030048200100380f0000f4180d00503400e00942c010741d00d45410071490010110988840e103180d01d6a49404950710350105100d60001045004d2072992000101c24002030402180d40e4044d4824171845864030544050000e1f0040d54070800d024400e103280000c01070700581c070499549000808400003600c48680c44081d0401170041504031072003040c140301855030103801401440f050b00c1517030410a1240003c08412500798180e43c403258081d10003503510300300b100d599507a5042881034521140d02d403010001d003401c41d2625041200813100e8200103101d10716000c010780c44030f0302010b2038180210000e5101e40c0380d0b83d44205c140b005128031115541030409a075584100e0355401401010355004102c441601d507140e010b6117450703650007010a090981703012021507070704600ca0b6419801500603030441da101040d580181652400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 772860476 1250 772859226 772859239
    0x6040e061503060a150e071709010f0614060703120b0312030603010c030b0a03060f0b0919060611150603010902060708030108010e0307170310170708100207031709150114 75
    0x640e51251800c4518003d000c40d112540000104019103011490030b51041f400d0412030240075030000c411441d0801162a00c0311070f5901d01c3c10980201091041801411404540c0290142410041042c42c41555400b4041c460b85400380300074040160802c0c0a041e01c09410780301508000c440e608250b0b0001d0f101e02d0322035400c00c1c81100041c0c4c82841203442205004014aa0992464071640020956209400e00c40e0340c0755110980c4030384076610001e0161a0700f283c8001008038240360001113a109800180030460202104c10398030134009104900c0041c1c5090056041c2c40f00b100080c01011510310003500090082110400d01070303803102660403522800028005d14071b1400b03d06803a40300d500c5000b031102e031404a00b03400580d0300c040507541c42210075515241c01c6854500880c0c800c0202c01c1c0449195110364014403001001307002c0c080c25650801800d40c14010182e4001e0b249000122a41456002c03050026044c0c0e101008902c460321540402c54000b541c4502580409008565400340a5103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 772861726 1250 772860476 772860481
    0x801020d2a020c060d0609020f04092f1c05070206040516030f03141605010b100504031110120e2b0c060b0312190807080c0703050306040e06150306 65
    0xc1008125000000060303026001078540392080081a4005d401d00c010141d0380c030540400e0109451000b00038240e108001140c50301d2624134104152042c00030503000381b480c09054004401344110b10040d100c104e801200b9201c2d001c80440c4000119184034915401d410142440b541d01c1c0c0120389076000c5e6002d08180c8014115004000403201c1d0503100c0286580f012284001c0424400c00c02140c0310500c0c40a942d1400912104d0340c4000444000d05440b50b035541e1002e0700d220f190601d1480400016424101e05007861611002420b0000c3c46030507000f48060a50040210b00c110391001c0d01e440860710400040c40310302040760307a40c00c24071000c100504956110107895079400d002d042c0c4404c02a500c0c401240c2d0150f8840d8043d10319480040c0d0540b19607404031001d5545280580070307200307000791210b401c4100508000c0154801070400410312680600340034607890028225802d041e00b60500c03940d6500c0d84408240100205468043d10713000f0385040c008200081070a1506200c0d04030101c03a500d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 772862976 1250 772861726 772861781
    0x106030b100509040c09030f0308090f0705030c040e15040803060f010c02030a02011206082406012109020a1703181e15090916090b120c070c0801020d 66
    0x6010100720101e1028400e054291034250049081d140c0b8500c0c20b40a250b0392a03540c0b0b05a4400208100c020940c46002c101140b20100a10360f0b01210b000001c083c0685042c000c81c0e2030380085503840380900d45400c4171010400c403c204c11028040b24070f004801c00d02c1c0a0400c060325400c00e54060784034114441ca6886c0329803192000c2c44080d50000d001d4000c0780c03004d5006507108443e03411140d44203611110002840b4000740100f03c0c80710304034001d020706080c4116000e5040c6000420550503c055100284002118189441900e80010750009500046400080e02044c6240e01c25000c0350180c4801c0d0314159400300140c0035584000800320300826401c000c0110b010b82c1c0c401381f5140c072003010350100c01525040c000c4a4607110884a5140340070044804110303043c104440480c0740000b0400009030169021080d94010680c0d120040c0c1000941010003404503000740900201007000b00340001404020344121000300305101c0215520138038203007504041c00d204409082000440c02814040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 772864226 1250 772862976 772862989
    0x7090606080402210109020a0603151707060c0303020c030310080105090a0201050d02090604090507050a0f0f0203120601030b12160f0530030a0c1e03080a020d150e0106030b 76
    0x50355000b020480c0b840409213091406203686a02c003181c2d503403501d254401507180c61000b440a840c5a03640400c1101000510800a10650340025204e500e088980b281c0382d40c022800c20260b44852a004c1421082030604602a00460440346007a00000044c40900c0160a02ca03008441640b0000c0c00300360b030740410b43c0da221038044501a010401c1001121200b050590007840c500b0801028607040c5510340d4001021075034112004408030700000340d0b0411207900700d81e40912913031061030050105028940e00940324020840c620750034442c42c3d0041307802c5a001e9000030095003c050a080110010140003950f00c51000d031700a150f18400480105040340d080701c400b0103481c0c010f8501201c4000c001103030840c0ba440a10350755a02881e443c5404541c80040c4020010014a0758440780c110740705052001c5000c4450060032242804100c50800090704204000d61024405000603103c2d49066580c7d400342a0b04101c40262100081c0040340100b0723550b0065042c0c40c1f8581e81040000000f4081c06030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 772865476 1250 772864226 772864231
    0x91b0f06120c08070f0c080403083f060406030b09100e031e03041a011404060509060108160212070614070302040807030f11150712020c0a121a07020709060608 70
    0x20b0034440c001544c46001d6002c5030404541c5262210342d001854440002e80d4015070021a01c086002505079000004115480354055900d40d000658800350b020034070100000c83c4032070360711080503800617503e5959030307014000a5402003900c0b041031400b2803086407101a0b1700c0b0b0009060f46000c090680710703400001030320b104003054504030000d4080800c440d1035903000280200c03500d4004c0b50203d03015455451806000b00729500c00000000580d6042000341c0380c290300807070f0290240340204207850b030b172140840c2c0d00000310241ca0b21901000560807810000d040c403d1070f8410100085880411556622044410012000325021500c8040040741640f1a5111319402603000d0302e02030000c00c0d2090b060310207030b910031032621104070401800328401001252401d42c02c00c1000c40c1440511103141a18200c058892000c1e01e194001c2c0000211007e03114002c2e04501a541907400c01005420002001d102503886140840d62800460003075170340d802e0340103c0ca50703e414074ac400145240900e40890 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 772866726 1250 772865476 772865501
    0x1406100e01050a050910120f05010c080c18181005090c0c1e012c010506040e1b0d0b1f0e0c030a2d0b0a0506030405030d091b0f0612 58
    0x80340c035041c05c000d030010002e03001d11005e03030f810a070004403032503050569100c9921600002144080780d090650844002001c3c00050252000811217090410340483c0d0b802281451303070f80030920742e220125001c00c403108400e95103e840f8000344009030f400c00d100101114000c540f030403496518004d00e90024002c070045c00c0d445a00c5091403051b00158001940080ca580d4000010600901c01003514050341001014040d05400056124045030030f008495208605603414482c801041d00c1c12039070ba0304030140200220003080c1141900d81c0e41c9004040081d9003241c3e01407254141010714100032189a000071850032142c02c8005801d2080d1071a8510590518030f1180c115960031846001070094118005c0c100d9040303500d02ca44071a209801c507290788030f0b80440014205c0b801d005000c6080c480f078210f5440341c1c03024802c2100048001080b1141e5a10b0301502182144440c5049105030300210700d00b440d2441e0405000c02c580340e078002030303c04a91580c0e46500c0d00011000d50241101d14000c01035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 772867976 1250 772866726 772866739
    0x305070515010807170a0f050f10021206091b16080f2d03150d0b0f010e0105060c1b0105040305030a03090203100b0f2e030f0c02070f120602071406100e0105 69
    0x9004541c5810711f6180540c004c00c03c0e01c1c00d180350300000c1d5040880090a0b030b9103565010440c05041035400c00c20541c091410b468079540d505182c01d8516040c0b101500550032540002406d110441e00304016543c3c0c15801060140c0318100045000d0194010450f60726030020980c440300705001c20580c44500343c5082c0c104181c5991610b901e502e803c502101155600500308a001d9070008480e809014031030a544150305980d5410030b03880059603641a407005200d800140500400c0c4c20020568080001c01c0b051090181c1c0a0340300180e41601490780003503e0ba00012500c5140030740c15400c801002c074400c5050b00c0490040302c1c0700c074040740e090309181500301038402001446820820302545a442050326424085a00382400d100c42004140c8030200180e2100000030390620b05010300584400c480c00540a41400e00081342002e140314860006441d03070441200007880300a504803030031643c02840c10000c0c5410401200e565035016103d142c0c8071101d5403000110440b40301c4416045c0c58004214 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 772869226 1250 772867976 772867993
    0x140a0c12090203070314030a020706020706020d081f03030f1403150607021305010906080f1b0603150a0b0a08061e0409060e06040f0209070806030d0c030507051501080717 75
    0xc0400801000390200d070184643d18003c004980f41c02c1510341d88811042c015036603640c0e0500b00a050031901d0307002c8011365004200601c132840c0c0119004040c204546440c0304076036903032030282a01c80800c13a0440ca50381000d07074000c0203065105013015080042c0f9140e00d0007654040c116488607101c101c46880c25040c604032050b03614035111000b400b0150008101c0d030b402001102ca000201c84081e0700400c0066038405c002c0100040500c070386141400300c000a052440d040d40280310656222220051003840c1c00000554000b8032401045030b0707c00064002c0050640300c402001c01a03000388422008070309004001820740c86c0c10010001c6802300020f1003102c1d41314580031302000d8002414122101030702c0d42140000500104001031040303000e00761401d07034040c00780144002742c100504800c00304100181005040d450000e51254450b4051030140ea000d43c0c2400c00f04c907580544070000b80140219503600c44400d04d418100d5040c1c50651094444160780d500840d1800000d034042100950482e581 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 772870476 1250 772869226 772869257
    0x1f03091b1a030a23010603140f01050f0a03170909060301020c3d050f1807270c02061801020703120b030f070b070309051e0d0c0902040603140a0c 64
    0x3031504140c1440300860756014451a04c001a20007440c68032290600100400c84141c0c1400780c030305003078035080024140b400c0204c800703110b400050141600604040c100503155844100c41c410003950400801545042031081e000060b0f0f0101c076069104220b0311012492750301d0180f080b209201001c034000d2800d0031003590021400c101095010450540116141c01c0c094103003140e207010301200f0303d07000405103801113070420007040140144198034441034510341c0060b000100c5000381c0c0c4070200405418214022500c01080b8100e10003c1c9003030a00100c0b0780c00c190000313040d03809039820301900020742481e01c010508078001c0d160081c0006200c94280f00c00b12500d540710b4405014007138199000d000101c00094a00803003030f84841000000000d042043c541c2c45802503000e00402c868069440d14001c0800c580d2041001c0e040d0b100f005d014103800204021036441c840200300c902000e540701c654444002d00104400e9034020002c1c1241c0e400143c500880b07200c0c8c203020817a50b40701d06060341c0c0c0070700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 772871726 1250 772870476 772870529
    0x4020906270f1b0d0f060f1d07050c030418020904020714060912040911120702150a020a0f08071707181401020601060c05010b0306100914010819021f03091b 69
    0x1030713000b80324581c3c0c1d050100707112080b101e105014244020311088030a42300c40908035800303001400c0104000051104040d014000720480b0100c03801604079101048003119040d00034406c40a02d158424800034801040060701d2070b400c5190b80c2074109403560395a50b42c01d940e80b04c1c560f002442c80300c00d008000500c1020500d03230000c0035107460061003604200b00550741044402d401e6a101015a114000340700c5290b10350350700264090720011003541040c4009a01511103030600c56420240450072001440c01803180d03c21040d4138079082c0300400c841c10b1000300505072704034607040c09001013009070022580703e211440300002408181d0003000240e00e804c00444045c0748030b4404480715500c80d82d01d091a55007c000da9405020302d1060301d181140780400f6101100c40401507a90501600c000401c00e030710703000c503501e507140c840c1d42c4427884c46030340070b10009802d2005071588212a103400c4040040099060744040030b118840d0b030b42c01041048508840704032440340c0c811401c01e01c05201ca0040380c2c006c01c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 772872976 1250 772871726 772871741
    0x18192a17011a070b040b061c0c12020d0507030809100201060f05013b010f08040323091e120a2a080a030c020108010f0302060304020906270f1b0d 64
    0xc074070241411074595034510150010786054071514440b8090003083d12300318903810180c0042044c5d0381c210544654a502c0c0812041c46070640300444640184295246d051006044584c040b0540e4052a101d02d00700c00130f038200e00d180600407103581e43d041c9030090052107181309582400480040301031608004540c1c0c000480c004501c02036851802c080c81d80d442208803508a950640c2044d980d42c0108001802c500700d00641d00304010fa014144408a038200b100316240e64100d200484007400030880d0300809104200d40c690300150803d415042816000b4500810349000b00c4500d11100300021903155203024a40014200800810000c03d039039036046068900311081c1041c41c030040b0340c0c8003a040c2c1842103100b0207074082448025141c08560744280c2080c0074000400d88595140d0030b42d0085540b038000200300a0143e000c1c40c0202d02182c2e81c107903e031204c5200100c1c0ca40d40400405c680c0740c00400c2c0940e42114001440408500014003441c20901100780b8440013604161030514608040d003180d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 772874226 1250 772872976 772873019
    0x5180d1403040303091a030f060f030316030302070213020306091501020a0c060f090e090c011115010b1903050402010c2907020a05070b040518192a1701 67
    0x19411003911038003440684000c5000e5210031320124600540c14020324020750401c0c0031444108104082660031074030a079000081512001c109030410b00100c0c0c40c0d489991740152740c207007420301c0040800d603164004113100b500c207648a85000c904003458030140d002c140e0b401e170361020800700000e00344034004042030b401400510403110620380715118a07900000503009480010300c5044080c1c08583c001002c100101002401c80c0710342c3c03401e112107a40f108a6850702604020540c080083d00c1d0000b0000350000032280b04011003a0359645c2070b031543c079034061020100440807140441000e02d0007031185600c540c0e01a101d2641f070700c5156549000a1020300d03500c2402c100ca141201d1400602c00c54040d124509540080c001f02007141011460008207a00002001d501040140100d0321190142d41014a003000d80c86002c1c0c0b103002e001d9594040c3e00d0b03c411026460b03c40c2c1882c92129010300c0c021040b40c1c0c21050703400d0701200c407400c644003c2c0d80303c01c00b146a0040f2004004550a43c00141c040400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 772875476 1250 772874226 772874243
    0x21006060f2303010b0423330d051b040e04110409060509010e0c03070b090103050702070e0c07140c0901180603050a050c0a120b0118180308040b01050105180d 70
    0x80b6020020015082a08603100043e4082418080e069034408040072071104d00421400e03c42c0986c3c0010030f0407510301c0605a001c90840d400c00c500040030344400e40b107107516000c096150a1007100200040004442c3c081500510f079540901003002881141c05172031005c0c107441195a40d0703489102240801c000810f0b003155446000700c001c924a4800c00f801007240c1c1d000444d03d0254181014030b040c01220701a4400d400082c8104004440072007107494000b42820040341603903070206c1c281d040000c154025010310382528100b00512103643c0051000c2c1c1d00ca0b00855508901c0c007881c41d81d0300e00098000940000ea040c0042c000c1e10600b92081200040842d004203580c0d4595543c1418120002c00882d415400901c20701550301e80a0410300c0500080300305840ba409070f58442d02d151038018410150500c0300303403500d0141d12116800c4031010b425070210518805405160003000560105c4050b59030319425000851103620a00031100113002c10514103000300ca14908001c0c2406420100f124544e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 772876726 1250 772875476 772875527
    0x270607050a050a0212010c050702040b0402070f0f0b07050301060c11060f0d0f0c0c0b130614071206080c0f092d16020d27170706021006060f 62
    0x1001004207001c1a0310490140001002d80d20601c030f00c4040704200005a6414400d011103500e910505441980b90102d401249007a80d69000c507000b07101d2002d0241c1125030341c909150500ca0b1040c032651120303208100000080c1c0c0d8602d8112905d000a00803403000808070241039000c50f580e600104c0118000502c254a01201d00201004650107030640c0c0e0034135900c501003130a01200302d108400b06000c407810704120b500d900e03640d424504480100444c45052048c0c0609040c001185d00c10901d5680103440300c440341c01c01d450041e01694001c0702100b00c0f5800c00e400400c1d020400b0480d90546034014050f54203c012443c00c125050b4070043c50082c04540040d07032190000e5113142e00361260320230900c10800b981444001d040350340040900c003001390741c404d50983c00c10681c410341806654000c41c500201c014410380303021004070350341d40c800304c9000b01886882c4484c40010804c81d04640d00340c1c0032290a900304803101010358001e4454000400c07210400025424001c1c034042c00c2503040d14010481c1c14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 772877976 1250 772876726 772876733
    0x60702060f0423070f030203070b030c040b0c070506040e04050f1c0c060e030307052d030606160f080406030c08010305070b520b01061d091806010b270607 68
    0x81000d90084120300c401715070410660400b0310041e8054040c100200d861490402d8410815100354412043c01c480300203038209484100b4408034026000042c0800c1e500e0341d940180c074000510a8509a400b8011400b00e0b60509e1400138801d98032074241b01a0000c032291240701a5502c2c40d030384074181c805c5c3c0e40b03c10b564481e96409000540c270503605615101d0b181e080c1401c410b88081031403100d0300b0104010034818400c90b04098103896011404841d901c1e03503565038118060a40780c40c04002002e00c40e030440100100500d40300034005030345050350704000c05440310004451a220a210150003600011010300800d0303402401003c0901503031101e64100ca581c0e40c05417000ca000e1b0a4218049481107a0782c6118aa039486600d545070032201e070040c2000a6900c503d1004801885044188016001600c01031002e00300300300b24044008004c2182840c061840a03094900d0070491002ca0141034004190040580107841c0743c01c00d2104041c00c061880d814090000306c00301e8445500000a02480000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 772879226 1250 772877976 772877983
    0x1b010f0516050a05120331020414041e0206032a03160306061d0111070504090b060306071e03151a271503040c03051e060702060f0423 59
    0x1c51081d00103100740c1d071042c200300e41040c1144000c8201c0340020400e0229160103110007583e180c07000510b580ca01c003490942c044142e1a542c0c0e0003034102d82404080b03641c070000d00384100e00c290300075045003220402000f5420b0050401e040000d510030400e2020a0512080540c0014040d403140a040c454511071504800660800c44099101e000b8842c01804e0413503041c050000280668200781c00c0e041040a400f00c0c8006041144070704004000c2ca0318a2001000c00c0354500902014100308249201800d06012500e412505280203109442c00304903114070030000000e6103c541008040e680b0b480003012005492528030301105c844030070741f01162024400865406030001c181c500b6035202c040a004a00e004c080b140f400b281240c000119175040d45403442d081c1d028042180c4040c0c0d482d0f07154070f41071038405c90580020b000781c8600364440c822520045c0e4101c1030220807008803047ca54858100302e9454801b142c802207000d04900101e00015240d000c0c1032100030b0a135031301101a50820008925 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 772880476 1250 772879226 772879267
    0x20301080a120201062403110301260d050405150405060a0504030203011a0a0603022206022d0309010807030b101d040204030809100504150203030a0b031b010f05 71
    0x1141c11041800c0300300488061805020b000c40d000a000d100d18108062010846480c0007109050849051040c0640701e42d00c1244400811200140c803542c4444642030000c10110085050350f50120001801d0400040c0d5821210140da40d91841e04d8146014049907c441079a41c102c6c080d024000459550340f84000b03050703028040c0e5161a200d910718010076007074405800c55a4001c0158200601e0b0603201c0c041a50240c5455040241e0b070380302d94100c5805080000116004251605800401c0b02980490840588030781c1c1c0001d10713250038201054014402038000307011590f41c0200100c01080d40074105042d806400b80c00c0c0040d04c0709000f004902c410303009a2268000404176498284c50301c28048101103840d130150ba085080c6401e5568620451103455942031003200b4000e23801030b895100f0070442c0d0180020700c403401c50199542c2d5001c1e40e03d0300140c61a884031070038400b001825080024104001d82c05400402084031411001076603108001c0e411706040080800c260a40b0040b034428000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 772881726 1250 772880476 772880489
    0x30a0c0c12110a0b07052a0a1d0603061909170304050703060c0e0a090b150d06091808220801060b030a180f0803060a1502062406041208040306020301 66
    0x20100107031601000380922040c4c110b42aa40703000d11840300419400141c0c410948000090440c5500700000501d01c3c00005040041e80030514000c00703d809005018404160040b44030920b05540701d500c101511400200c400c81108404108440012030345c68101001c498040e130003c80a00341c4801c155141903004035000d5995074884141007041010512844000503101d180070b0702004079410006048280fa403080c010b5175611010081059a03888400c9402d203403105864543e1110800c0d40369010304100d10520178200d00c0d00103410442400031181c403c046500109062500b042c1083c034103180750b0740340c16030000070b80802c20100380c180c000d00c0354002810380e0007900c90302d078500f0354842e0302504c1d500351480d54444d018042c420b00060b0038000481702588e11017001d43e120741d61403010030300c1342c42c5660194019000f003d580c2c40e05550003189050040708200c8075448203110041c0c40d10306401c0c862040b030350044c00801003003000c10740400503044102c0c80f50040303070b250544d82d403201810303600282c0014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 772882976 1250 772881726 772881743
    0x1090212070503031215040623190b1b03130807060207060f050309072c131e03120c170f01080715030e030703032306030c010309050c3003040503030a0c0c12 69
    0x14503544443d045210401c9c01211000b2242c0fa1000c12103121000c1445040e410020105d80d420780109500c4150346240001301c1125110501c40d0342104070300a451081240728020b5003400f00303005201280031411350741c007070700c4202c40c0300b0030b0a40407291035000030204503041c02844000f0941452540312410034045812a508103459110904c1448640251045201d41c10075811200022031a0300003a05200d02d034212283ca0281504041c0d44051801c000d0114a07480c140820104075003044101c80124081007089000707960340c21500c4a160002c1c0151007491780480400c2040c1c45c0341c00c0000b1094080361501083d051216a080c0b4950340010004401280d2030320030a001d040c140c05080c1100940003110240b8504040c0e012a0f2036072640d0b42e139181015291401001440020041807840c8100139045400c075640d55400d650702c0e03c0d0034840c0d01a5145561208020204000065400741d0701d00a015502c0c2004811007680d00c0d1500c5401158803076400003001859103100d1140c00811130054414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 772884226 1250 772882976 772883009
    0xc051501060f0e0d02030a0305070516080105041502120609060a0e090105010501020c240702010c12030e0d0903050615010908070e1b0a02030a18080d02010902120705030312150406 79
    0x20341003d2108000314000c048090100d809607400085c130b41505909810000d035101c4290810341d00b0a2a50880040d5a00d0340000000b50711031b0540c4010310075805452210102106c801c0b84074180d22174101d9180c0703068000d50101c1c4180c644015a5500928018540c12480b0782d20030f89103d11540494441c0e1003030755550010002d5580500034581d01200489100c2c00400400000e0480d43d084045424000e1001003824021039020712160f061150700000d90028103444094000c01900b8510380010060085018000da030900841070130b01500c1e0300c440548840d5407031608280b01203001f40f004134104045840e001880110910040e009026011950030755441d06070500801203100b10800c402982c0100b00c82c5505c2503021003a40d003004241c0c64005800003145500600780103191700480700c1409007130843c0d012650158403480206200303443d4195510b9500b0300c0651105850b10500d50160030402182c3c140d001401c0c80c40380c0c8107110b041140356141024012a08840c1950080c0201c882c00210 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 772885476 1250 772884226 772884257
    0xd020a0c06080f0a150b1903060e090330040c080601060903032028170a0e1017010b04180c0509061308010f0b0a09020a0c030c05150106 60
    0x5280190280e8108041a420400c42030f108924004000d108219503680c000c240320303c442103019005102c1c0e513554980310303554005100200318045000074042441c148001581c1c0b60500b014500c50854000554109030318000101c2c805078403858017019400940c009030901071513035000c003802035016207006601d40d402c091429142400c1a00070005214090100300002540140c041e41769001e070007084103c948000c941c06181040706405411090211580001441c486040b2000c0305c50007800c80800101c4074650a000510034400310000042016000b45ca880c2020003448070002050300d051070410100010401d1500d400f0707040141d0001001400700a04661a042c03941400700a2074104014030405002414520034080c4107805040042040041070443c03621413001000d030b8000030710500d07e1406000c001404003112452069400301b0300803890116610035038080e044c042d2110b0740b048856407003c1c2c501400c820011202071041042c101d044a141c112040c1c004e2000c0d84405141d01d10184 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 772886726 1250 772885476 772885493
    0xc0c0b09120606062a061503100912050307050c1b040507030b031b010c050313050a0b04080a03120b270a150905090f25090203040807120509030d020a 66
    0x980541c055100100307000305039503030741c045a00502412060900303a01142a1844070400e60b882810890b001d40c0d070801180040404078098040012416070706003074030180c1c100048032a0610090711184c8840904010036016800031500031629041480c205048401c54902d0301c010080304107602240c0d0510b4540e5810f25010700742c1c0008586c18103000388c205001c042a51900946070100d210f805481d842e00c010b900900c2004082070304003065075507c03202e00b000b50720302c0c403440c2c828107009010031300c000a0501c80800585042d14140d00151008007090f4400301c40401c01e4091749000c207507945a0303a9080303507900b822607040c0c842e00c403601501d403040c58428050680d10080ca03002c40c0504000e0845501030980345030a09940207050000342a07101d2115040c50010701c0c221600071803044d01030204010040c0c0c1c2d200407018030700c9010078a20580f180f01e03100c160b010903280100342e1803042c043e20300043c0700d20040b001c20420914041d414403490b00c00080c60403201501c4103025800204101d0300b0300c80c102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 772887976 1250 772886726 772886749
    0x5010209031912030518010608010b03060601020a03050d02070812040b042d2a060206010f061418030a08040f080c0409021804140d050a110a08090f010c0c0b09 70
    0x8035507052000341c50f01c1e407400c607400c003860440c1010f5982c80051682c0c1d480c6170140d4070b9040380e03100030400c1a8480580030700078003022070b01c0da10920030000041c001c0d6100142945540d9030541d1058100301d038542131300d400794100200803103080c5014060007450f1004243d03028490340c0200414419401d0070304084a4044010b82000642d24030012610b444402155001611940c4140203103100100c04600a807505000c20107000b51030b00401c3c0005156900040040c140e96264901c120b280390758504c01d80e10302802c01c0e20f40e20144002d00240140c141461241e0341544409019144100400c0e96018000d9000f6000a084401015014424481d013081604d6403844150360811000c12a50005041c03903d00840d00302e5079035035040c005000c0203070340003118461681243c205c407144008800040c085070004c0071032a0005040c01d10700c01c089200059030442142d08004110b18103201041406a00c0003030030319a5041c8600c0190100c00960210030301001040c0c900c40c041d848080da2010010a202d51 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 772889226 1250 772887976 772888003
    0x8010e0a090b1506040f09020a0f020d140a021e060702070905150f2d010f0309030f050c03090a0f03020108070503220f02040e10050108160905070203160501020903 72
    0x20466410001054075042d960070100311030300b2809082100c40021410b00c1070340c0110341d43c084202c100081034005500601902900c03601c0341081e440844404a80d200046004000010088110001405440c00081c0700201309403042c1d98120004440f001c04c010303407072541076240e07912000c20002043d40c14402c03040540300c0e6010a001c036003000030717a44a101080800c480d10860400380c0070480d44e1b07161800c58800c00e018644200080348a032403000d1a0039510100b850210f0805889400120301c20303c03030f40d20940e92549a403070703140c41a881b04070762030b4001d0702002c642c81c40200101100d6940302468040100721000d01d407910b15085200060134540c02408510078070038140305101034501500343c01c88950000006018075002181482e101802d0386040203504149030120074003100d5404034001d40952140d03030741848030341d0762154840da80700501c0d00c0145410202050501c0482c203a030b00441d800030301c1d07481101c1c20044240d40784c00c85042c060008803410380d0b0001d001003c40c142442000c0440b0300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 772890476 1250 772889226 772889231
    0x20a120912080c131502012012060a230112090b1009062403020d060b090901060203030105010c110f031c03060f051302130905090d1205070c03200d08010e0a 69
    0x14911008031144060300910341440300c401484c41d10715100752300402e11041c1c0d4036011031011142d1342011f0b06591103081c224403942d000d000014281e00780280803008940154000303c0050070898560090030b100c0010182c1000650502d6803505100d901800400074081d251240382410006820300d03600196a1140d40170a041240400030500710010380040e1030207543c081c000d0700c500c0803030840092082038054281e10340b410001148010066014010350002901d00c21090390701c1d46010380e41c90109210b024005a8065000c0c00040d05860440c0a40350008e0411008580c00b100003c1c100003113905042c44841070945a080e0f05035150180c07100401e1000703005002d81d414680420140314080090352481034000412140303004a46000100629800c80304003c1400c01018071030b1136401085403800000c240b0711035445481e003244641d60140001d030700c400507964540d0b5000c1e2000e00c441c1e2103046090414000700c0c2c108010501c01c071549180301c1d955a40e600d40c14000382220290f00581080f80072403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 772891726 1250 772890476 772890487
    0x609100f09030804080a052104050c15030718120b040506070804020d03030e1501080d020d0306050a0e0711010513120c0302060f09070506040b0d0605011107030204020a120912080c 79
    0x290408240f54019030071480383c99954480717020544192041d000128600040100c0540e052464591458002d503c10025107103100302d19020004010000f00a40c80380a1041000c901141e007e003039103880100c2d45440341c0203010f503205100c5411081c40135061780d0000d0f03400108020081d040c8400c5a006010742081000c50802e83c02080443c248440d0003014160307143c0051804401c10400d407400700403030440c041c05541c2c580c0d42c200e4484010300d04600140c40350743d004030300640c02406040c05071400039203140f4000b131601d10034000103007000d13220005004900300c8240982e0703421300404e0f11840f105103102029445500d01011000700c0e90f0388410412607a2249040001d5010400da50400f00400681f09683c40302003915082407682c0e032180703070f000b140000e001807032800740c001a01c200e08100500300007059075040151488101545440c0440d00010418401807420358090140c10b5684c3c07070b200d1425510b0070810400c41d65107032410307500d6021401c152120700c5e070b1041d03519910541e00080300b400c1030f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 772892976 1250 772891726 772891733
    0x1091b0905091609051003050a150e1b0f041103010b040f09060513051521070b0a05070609050a0602040b03060424031419031101050c1e030403110609100f09 69
    0x1609800391300c1c802501e82d0049050b20110703161140c05141c00200742c4025506502d444a91600a120040c2c0c1440c104861069010350205241c80001041c1d0000c080d091402c0041049444028840c280e00559404601005a0f0254007440c06403601c06070aa941d181850340c16003e400181e070000320058180b500a0100c0c0d191145801c9603189aa08081200c2e04c501c1812400132002645280d0810049003615004420301c0a05100c0002180c0a6809042d101c0d80b80c01d030304d403060480715400311782d0800481d0006415940040240da000d44162000750882d607035400c044e6805036218115050010003848494907040c400e29541e45000324180c0108101c20700c26445000f00c6200c05000303500d000d2110300c1c1025060140781508404c10070483d09a103141e2030050034400c65032505031915032030000001c640f525500704440009204000108c45130807a2860703400680d10090080f03041088000e41a114000704000981c02192040081d198174500004c40e2011102c00412181c1d8480c140b403101c0010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 772894226 1250 772892976 772893013
    0x6020a11011b0c0f0f290a060609121401050118140f0a0213030501050f011d04022101020c0d02030c100b0904020603040f0b010306091707030207050f0301091b090509 73
    0x203407544200c920b00080010b0601440c842d8400740043d2071400e01016110307082000e11510840b8880701c60351b403049a02c94030304940c21600ba501800c0301044e881d80d030601c5510207622490600310700c1605440c000201e01000c580c00d640c2d081e4030030a6005103040b07010300c0c0401c86000e1040d04501003022a0450b1821000c015508200074007004110351b030000b01020452400d00c1e4035000746422030000e00041c100001d04440d0114248a901c8620030795907240300010b20004507081c0a550000d111401d041c0074149401c082c2144054114043d40d4204044001c0c2c400501001d072030300e207598002e0f41d100c004c182c40540c100352208105e0800b032071919200c404540e030703131200b419002074050720107945a40e150322305296600303508407019050780b511800020800000307400a51160303121360064058121405580c01403800350a034024090b8011318420310082c10400c1e2544a8294020700100b42103400361102c0781b4401040180c0d055008a01205104035000c500646030806025001800190146a4590503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 772895476 1250 772894226 772894247
    0xa0903120c06020403080403050105131212060510021e0307081e072f0105090f0904020f0a0810060b0a050a0f170906150a050d080d0906020a11011b 65
    0x1103000c5030400892000d104180d0140c101d680624215560340c1c03642409005074105210440d055801c120000f114002242c510140c5180c2c422507000940300e01034410b6810620784d103142c9288030f40e6402c002400d0303600d60b0b260389003a90064026111850b5019400038030056a04404110396004104801c00520104c04691201d11000003004210030382c504400c80b40e00c9035540c00381118551520801d902c4131003030400388000000e0086080300c2c803901401955140552130155520501030040d50341541084c0500036030041c4000d003e12120141c54000860b06e0712103411003560f545c80025060041c00d01e503c15203001c1c000c03000d1924240003201000070211307c0f9050300308003000114482d0101107070040480015283d00c01c001c1c40041c2c41c200881c15600c0c0401c48030014403100b0344019002c00d0500c80c0c6e001c0242c80340907007998035944072a00c5410880c0d020080000a55681c2c010610108009102070407006a90341c0c0e59030301381c0100d1101e6a09403108115005581807422401c480c14980102c807a09 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 772896726 1250 772895476 772895483
    0x15140a06021f0f110408160e040804090506031f020a08060a08030307120b03240a0e030406030c0c140a0507060201150501030506130609151a120405100e060601140a0903 74
    0x2407440d01c0507011000360a907012139a141d80c801281c046144a00860503aa08559480d0b80c461a00e43d40c150703111850354151406484210100014440e07a00da46e044207602c900c003c4c04880070506980d0402c170b40501c46502c0d83c03854a0f40803654000b079651000255401101c1150b0210119007848002034070381c403014140134148030072a142c000c80030004c1d4010141d03409000342038034081c0c4e010038081403100300d0140e10310a21614810006040445511400000101200040d4205424054190b0051075042c0490052110b103081d404000f0742c401184040701800000030342a2085c0500d0120300d0984650400c00640e41803242c2d89034041c4580345108121032091a020030030f91505401700c1c850a08205244020504102d40401d080b1296042081c210101d0f4442e1001d0907550b00c000040804900d45c09011034508221294441e0123000f540c5401500400c155404249600d0000c81140c001074120340300c0381c00030000c03c800ba45c0c0050903407042c40c114400507031900c4054240100421480e00006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 772897976 1250 772896726 772896731
    0x11202091c20012115030503070807060f0e0d0503061311090418050303040f0c1d06010206010501020c01020703060c090b0301170d0801051804081e03100902040506030a0b0415140a06021f 82
    0x2c4801c40c3d00a0509170003160003500740d0f41c0c0d6201605000c802030384410000d0f15190300303140001c0c0039131900744900303416444808050488481c200b20b00700c400e40e20141150783e00400c030b0004180030b0101442a03050760070816040956030f00c0781ca02400709a680030724144041808108248002c5140402140d52240d4490803c8a102d040352a00d0720313503000c00341c000001a49000307200c0561040c9088125000b024243c00b254013a80e0703140b004a035501b50494400c0d006070026031040002070321340d80150320120403030b04003900314544075840d1481e6a0000d9015602e00039941c1d02103001c100003404021a00070841c41d1151441d0704040104450b11500c0d000e0480c00c074901c00014090000c40000d9550041060121000003141c203000c00860fa001aa844000b0008068000550305a18402c5a040380c031301404141c29036642e41d01d840e000b00315903001139401c10345501e8a800f542c113040790804003402c13070340c154800c40c96000000c3c015800340341d4009030150340c8040540c00d02010384000180c040380300003002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 772899226 1250 772897976 772897991
    0x50f0a030f05090d110f0d030b0f06070b0403140f0901111c0f0905040203161d10030f050a0c1209020a030b0421020705011202091c200121 61
    0x2103009020700030328101920320308000d00c16104408284450079607029900d8181074150008480d4848100f1204403c05038080d4010b0718465000c0e8000a220420040003111000280390119a4035808044c0840d840310b0348508010402d40c00055504420140304030441c03e07c442c1b4003800d216445400780c5541882000070041a0b24034081203120720707483c281c00c60075075100c0e032039040540f40003500c40c84200810342031540402c85042902c01d8034410780f1103850404c61904030328030686404803142c01d543c1c6502d05e0804940c0c860f445150040c0080d03180da07a000901103004241c02d8086401c0503115072842da007080703013050380954400000a9000a1068002900481071000030310300019540000c2c111460002000184803603840e800e060003200d4200003c0070129580102d8a6980600540d4040380003101c07104d407013040640c050b01c0c5640018082410301040d1941941555484050448840d00d170700d051100c00154404c03103d05140c0c000e0070542d464141c1100c0d0030b00d4000c16401c403c50b4079543d8200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 772900476 1250 772899226 772899247
    0xb07021b0603152e0809060103021203120f101707051504050904080301090e0a12050703090e0a060501030f1806020304020303040e041202150f040b101a1b0105010303050f 75
    0x1002000d5050040500011300c1d0f1030980d119039640e0f0303c4189414940a41c441c84c008030b000300c80092203442054003820103a0300b140e0030003074400410302c0e02040c81d2106100080c0784c103a492148501846140524400c00d00d8007404880480e030f0035810114104052005060400100280c1507059030800c591004820003031480d1000e49005175444551701c00c802c0400c0c8020300c600d000007103050710780c00703c8184280346001111565600102c040202829404440000c0891158024006c0316120b40b519107143c650701d260000da181010358561607015510b580410079580c03d481802c0c0560140c0005102d0004013009a012010502c50081e0155400000050071075409004483c0504030781c49034003010f801c05060800346800c03140100c8025200b5010090500b29290307010038481c148281c4101d159548607035a1110101004c2c0c505e8421586001021910207110340042c0110000c0400e19500c411000440c210b840c0c14400451120f0303403400006001081e030000898071404813014006030b88008100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 772901726 1250 772900476 772900501
    0x70501090b0d0507110a06150f0b07150b0a090b090609100e0c07170a1103070809010c1a090a17090a0522050711101a0d060902090c070b07021b0603 65
    0x1c1c1c04001c0c4d40505541c01c0100215a4040180040708d6920f07e075845407244c19801e6034801034058800d440900b8000030000800400004000455071540850001c500d100440e0668000342c01c0b0f440b02540f54116540320742080300d91542d1141b012039146915007407001c000407059026014541d0380b00c1001000a00c92954113046034030b51075112801ca0304100402140584541112000703400240b02c42d0403a1440b01c01c00000c0d2501280c0040e08107203410140001501c207070b0300c03580301105c08000090308003018039038442001d44281c1071000078002c07061840c94a43c141100013502d10004840911a85126459035400c1100f6120203954801c1c0042d45122108084109600c00103034803070030270040102c8541d1004445001d03642080c201c94640f200e48402d01d05030f41402e40500d002c00a038003c0800079140c01e4000040c0640338a44c001a4001307181c01003904e441c0215a2176420031000107495080240004d0303042e030300501e41e201500990200d81410350600b90007810341d45c4552400f1003c03484100410303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 772902976 1250 772901726 772901747
    0x1f0203041e08061302030705131b08090d1805240f0703031b0c03030213030503180324010332100b010e0a051c0b070c05070501090b0d0507 61
    0x10031035100442a00d980e81c012a04841c000ca84260241e0320100b0b254070b20f0a00110101c5a008000d405820b0400082c4000f017130318051440c05c1a612400c046414000200700414516141c6e502d408962915076011440c1400c8a00801c0400107001280c210f13400d8071503a4a4103580c82200c0740d141c522449401c40001406150500755902e90020307051440b82c40150040028503c20386040c0500403130100c510512000391035005011861045440d00040c0c844d90040202560b510f8800c05d8607512500c0751455501701140c0c41013072941ca070315802914030b0200105903d480c02071104580b030b9002c1e4411b0000d2050188130090400800780541341e940b11041d5044486184084d4411201c1403071200000c0e65200039020141c030161038414800d00c2944140c1c6846003090014040185052414007400400d1401c20f4401040c4010007101800141c0c07030190050103140c4594034840740003941e041090501035140d11413814450180d01c1001150064001ea4142d02c10f401c2000450790395404090b107250509 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 772904226 1250 772902976 772902989
    0x70c050418020a09050a0b06040618120809040e0708070305100605030102070503071403041a070318150c0f02090408030109060603091a181608060603010506060f0a030902090a06090e010b1f020304 86
    0x1103004254a6444400c0c040780103a840b96003c40304cc0d46081070032079229a80c0014107020400c021400b958106a003004d14100075480855600d1584c4040850402e1516001180c103070700700c1c5040d4041018513000c2c8202801049000714a04030342655059507a101c0e07540028042000812800302c6d5550038401d80d8010a80c6d200d109000725900d6041b403c003a03221714000c6005c90740e000c064400c5070800c1d00088084e0b42c1040d500808000c10140241c409140020040b00c010040c1c040e1000140c031030081c254047c900c04c00301c180d141c1d418501d5800503075030b054000d241010b00e06144100801d42d444004a180010341d025441280c80f40d2b070b01d071510781074001d0006610344039074500034001c115220044070845521005850b03080c2c0f55003080500307940054801c01e074424402d008048a003801200101680e00c05410001603400c1581d020554001085911011583d60b601b42000189064014250f5401d0800001c01c400b11410000039550b2003080e29201c0b4100e8452600c1415034001c0040381c0207000c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 772905476 1250 772904226 772904239
    0x501110d15080303011e05090f061003200d0e03121e060d03030515031b041514220501062c1806030114090d23032802070c050418020a09050a0b 63
    0x14149c0f049580140d0a4800901a01a0f032001e101164401c0c81a00220031144040c030248000d480f858030300e5a0460414211003664617000d110390210104014889503025001d005201e260000c80c100c02c40034545d0550040c03050490070040c09585150403520821350505000a15456124180741c861011904a94042c4035101c1c000340325400c0301c68500c1450704203c40920501d030007015845c24041c00352040300340390301100c1c0604e02e081c42d003481000c4510f20385224000e00081d94500b46c0c01a11002c0e48500c01180c01020341460842d41c4011000300d80c00008190780400c244400451002c0000000c1e081d48094070b0004250103640c29000700e40407020b0101d0f01401d504203908230315204c6001821a001003200da0b002c590f04149140081100f00c8a40a449411356a604801070140911594a907801c00ca2018040c0301a41c00392024040352405241018846408c01080c8001c40c0c000e1010b0060301c4002031b0840006940c1c2540e40340c01d640710701d0070200d100c0c2c403088407000c003505c44a14155030081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 772906726 1250 772905476 772905481
    0x81605071e0501051519030206030a0e120306040621030e12010606050c073203011812021510030303020702060f04230d0b220501110d15080303011e0509 67
    0xc0541082c5d0051410781602c62085820030100b211012403c1c2403a0500800004100301603e0100d01656100b01101c0000c41d03c076003440e5802d81040e1008402d80c02886000c0144041420700e0b01c60100030346031088400d1040210320714903421400100d10300408000a0391300301055916104401c45080d0f40c0e8000074040d00d82c44000291482d0401418940180b050f08000100001801c10400000302c680340c15a4803035030400e41c9085411000091a50959250303015030341300782140074031010340e603005564940c140c10f9844402800c02e0000a8015804055001446544031100b400e21041b00d40c103040050703071001d9070300c08a1140d008540c8005c858080119000a001032881002a005a600309225282d00c41110030071006d0404458003030f11503200c030310000710301c9441d6000c4010080644421002d01725181c0c0d0300c0500791141a8525040c2c00c4011039900d1100403c3d015441020f0410a4000e080c24200100c5c00c0c1d89001c1481030f040c0102001c0002c0c51580e0301003003503e01801c0701404d011501d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 772907976 1250 772906726 772906733
    0xe01030b0f06030a111305130b30060c030402040b090c0f0a0e0a03060b151201141f05130605040312180305031216030911091506030a060e0106081605071e 68
    0x120154440c40d03004d40005480c84841c4040c62181114041c0c00070204100380d0140c0c01d192001c0000b03000c011042b41010341c41e20100c583c1c10440184503101c6451082ea4918051041c4010f44580c0e141550103900820284021440880b080c0c41c81880c45001094075000444001c4a00b6070a48607400e42204840c800030040c003003a40c00000c29008240c844841a42c405480c0e01124401c0342102140c0b18210001404001c4080d00c10076501c1400034203002010f071128000c9205a0b880001c0d0350081400001e0f0503843e509503442d4807004009600f445420107142d902c0742e828080302d1540503010030242540658249070070100700303005140c01904880d01c440c0c4101c1c0841d4000c00981d807810340c1e4030060f07070394140c2103120f4050000120f0f4000c000880002c01c0806201100c603000e481d01c1011030b0001245c01144d110302000c1c501c034103c0c945020450f145044448024018181c200310200301041c4104940c9002100700e10000140c0313440d1042c0d540700d040c1412101007160344129003c0854100b800f0060 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 772909226 1250 772907976 772908007
    0x515150a02011d03030601050708042303060109020702031e010e100903120c1b111302040e010614030708061f050d0f061202010c060e011b0e01030b0f06030a11 70
    0x2408540d40080000d82d01a00d20011814605140f1050380e5100b0000079955501c55000b074134555103d034180c0303414941c07a40750742200c00120003014882d0110140b4850743c01c1c0b90420040340103010f91b2508615082e00d81d00440d481d80e41069000852040c1c0d40c102109025003507100005404003907080d194107030b40480d50325002d005145002e03000181016040b41c0420b40303d120b03001c07420303040c2d44079031404070034002c0384000050406205881c04861050030640c90f40b81c854241c10800308400005a03554213040c000c40c0405410b8011204201c0c0f19074070a200400c1c900c0489030050364034203200c60250381c0c440025448060503014030070040a10144c090a0940082c0078001041c42400280000701659424030106c9402d8450300001000c040c070140c006d540980e025a104034000e0f40b003c20340d20280362107107003510044003001c46024881c040c041e000c2c41d40088d00d56125a003d01c2d06100f50220400001c8600b4001d4480601c540340010110701d000c80c1d581d004801aa03465916a80c0b94401c10b64401d05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 772910476 1250 772909226 772909237
    0x3051b060c0a030c0905010801350c1309110d060605190e130c090209150f040501020d0503040b070806030c0406030302241909021c3c06051515 63
    0xf00303060400b6021140e025100f03a20940f981a55400c00c580e00c0c020300242c1d018042c000c0044a1200c15072402e501e080c851500183d00c915400082940c010882c050020b8100c40040001a103458050b2950006007141c50f890650981160940c03910211410113400500c0143d00041d4401c4003c80904001c4000f0862079040742e4050622a5884e070740e00c000c2d114480346075440104408115a0240100314065014190000016150741121007200e8038010301035110090003114242c0103c0d0410040da410000b40649203aa03183c15815400c007540d540701c060001071f20b08070600c072000c1e00085003603e0422603140e00420007002071048580d40c1c1006500d80051842e00e2211507003030100c00400c00c00341c0f000680900b2080d00709440030700326040e03810010101c8841c2260701c208100c4203030911400d00d0201002d03240c0903061010400c00c1c0c0217100049081e0452a08a1788144003039649107000d0001520704410340c0020000c02c030381d91014140303403c8001c3c0002e0183d00c640c08402c403000e03560400c0702910 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 772911726 1250 772910476 772910497
    0x90318120d0e12010b01080402040216320a0816060b09040c0905150607061802030a0506060103050a111c0b1314100806070c05010908030705031006030e030703051b060c 74
    0x40d012070841d01e03603007a541c105d407640e8003003082e00001c1001030a1583c000c2070400721007101e159005503665a80c44606c2003070b60b10f61140c0c48044021180b440b100707140c41d00c1d08030326640050091080300d5951503454018504030700104140c3c50449010f00056420046840e503004000c21503030320b0103103004681e69029000303440c0700a2504002404c5501c003011002d0583d18018299418140c00e50b4131030024201c0302e8160712001c0c1095400c040180c034100300240490784101c001d4a070600c1d22100040440e1360080c182003036181040300c80103100c20070000b02d03904846006000c0c01c8080401c040400580203c100c0b45801070408286990407110039801302c41e490240d0b44600c4041d40755201070880e87d0002c0d0042c991980c110790701003840280074070769922000e4841c50001c1a10702c1a0b403034220040d00100c841402240001081090304000402030390003a00389401c01b00086103002150681c5c0c0e0180510083c00d001001800d4040e40d01c8a07a050f05410f1420310803503469140c20340d10b482c202c3e0000ca0085 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 772912976 1250 772911726 772911739
    0x41e060f0c090f0509091c1d06031003081e0d021206040908121305010216020f0d330c0c0215030705190e03070f05011205090318120d0e 60
    0x102601441080b4507021203082420403108241070008010b200c28016000c13011a2080984940610f112400f40c006019680d40310042d8810f4200da48985641080c1e440c1485040304004009100281014039000d0b80d03000509291182071001c503085400c082d400c80c142c0c0d241c2010443c06900403187d0014201c0300300b24101c54210b5100d10051005490008074020711102007400b180311002112844258040c2c12034000d68208002601c5441c22071b0312000d00c401460b07005a01c41003c0d400e2180d0722070824042a2800410403085440e0a07410400c0013144141b00d2006054117a01c10b04212592010000c00c100100700e8a00c20340b43c003800842c07130050100e010305c6151040c04251100340c07040c0c921a403020740b103030351a100900b140c144d1100000f5004000303205513480c418210340c070204825000f60405039800b88401d070400002400e240441c0c00c1002c400350500d01080181007010081c0c0d401c0c0c1c01008890454510110005020b09506200d5885184100507092000325840300854010b40f100340c0340c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 772914226 1250 772912976 772912991
    0x6090b0c031005041a0603070c14151509040b070c02180603060108120301120215030a06030308060f0a15032901031b081302062b15030c0608041e060f 66
    0x1132000382d41c025001d02c0280ea100c0c144072074040c1450002075074401c1c082d00d03059070280d459940f03c2e5082c103042100d0041580c01201c110182040115540e5000001c002c0556480300350b580c00105c80d144000d100424008554000c2441c42d40122010200c1035402002000e040d100b084149103050412030b440c0e8070a101e0140002144074010626043c402c5002144614503070811005140c4c1e074010083c100c1e04002e103008030810355000000514003c440e410170105000b885d504008107140400390465108180380c0c41f0030b488981c0c800c6416802c0b1408040c0c0c0c1017042c0d07034140040d001030031171084681500c00544049200c003501c4803154420320800362000c000c4851012540315680e00d80504800205025a0109200403801c804155045100811ba0352800520468050807640076200e040c615908504d4801003034145401100840402244e00202480c0b8580b036150109016200702170070300c014000480d017403262030b131138042481d83c1a03100c801e00404949000c40c010f000703074818080c1440c90080c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 772915476 1250 772914226 772914229
    0x3030f010608100312020c04020d050f0f01180f0f020a0221040317031503030a18120b060d0f061109011d13150305010f090b2203080406090b0c031005 66
    0x28100c0c0a040030050ba40141030a40e52650600c1c104102d001d41036107d040c4031072170142d94900050412650440c03004c213040c10405103860030100301034461030582c548000140110704404d241024185008c8201007588400070160000400b04a050150784a000080c01c0c4e004603000a48041c0c00c4100d0450080711591400c0812982e011b2030000402c035508a2a102c1140d0541d00044c40e04100d6641701c4a07a07030b00301072001a01c0c0d41c0c04981842c001c1038030011406141078035015454000c000c3c0c2c445501943c035466841c0e010769540108101c1c450800040a007003808603505147d90040e41c004c80411005520700c569500d42e0300165900342c0041c0c4502c000980b00300600c2c3ca40b0190400c094002c0c2d40c800008040100503001c091490144d10b46510000000b10310240103141400c038100c480050000600c3c1030407808586c00800034400d074281c0d58010714400c601c20351704160440d05490800140d40729494460042d10780240098100c0c81c43e40203006114040c40002c6004803103403403401c15015a20030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 772916726 1250 772915476 772915487
    0x22140a080303130f0203030d06090c0207060504080d21090c09050a1401180908030c0d0c11030403080d060e040b0609060a0806040f0503090901180b0d080304060b031e03030f0106 78
    0x350002040300b88981c408000070550070030240c080b0701c02421f0b00d00b0031015111640454540d5800301003580d458001d005200c40d0140310b003202518041c40e0071440e141c10400304668644544161104001c4480c49400d40d243d460344c81c05109103884c1509012603a41d608040050920354004c481c1e0161511001c1032410034103101d031018405000d40d41c1d0b96581c0c40d0600b003100740d00302c01114440b45601c030410709000603142402035201d0505c180c0c001d5240c0c808600340c00b0403501c00d001a4410f00011801200c1d2412000007540c045030350011030b140d6148d60740410b0340c000d041c02d54003030091140030b4024007007005000080303180300340c90698020b034450780c45208204c4050514031559495400c0f07240860f000c20a0034001080da40d0060007101d05e0645094041446010309901c4030194518680480751030751114000e424403050300709c0c0e440e504a010b5440307120240c400a400209081e45d00e501041c2c00340c500b4081d2004807011100c0301451100c000030155140d500c1259403458401131840007040490041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 772917976 1250 772916726 772916731
    0xc1603050c12010221160203040f0b0309030f07050a060b0402040b1e04050d050703030f033602060d0f18030c080d0e030d390522140a080303 62
    0x10000c040600c81c140c140088941c10303050940095400b0066400d032210203d080141405440d8008403079403502c07254045c25030380a00d00134000c6400170441003200304000c0350000c00f0b4504401c001946c0703490325074909145128094030b2248444011814805004c0e010a1551300c082c000c1c4024040d82c6403440802c4102c1c0b00303600030401040340a0102105800400c6140789000d490711442071700c0c05450388000749038244644000c841079881803030107204150340094480c1e005980b600381408400c8621581105c041d00440a01000203000b20303041030300d8010303030300041411178024017259592000340303404201a0500c0384000c011542010610600d0340d400310b001c45e140341c1d0944c0d82e2039810809640d03250715a41c001c07110803400d1030302c0c1c5280d012400818001482c840603038070030010768040400d40b0300303209100780d03510781c6a9861012000e41c48401c2011103480d0b010014900942c0c1d4000011030411a499030b0340365600c1c514400f41e00810b94048128485001d100700b00d523540c1003695a204d03840d90700e1204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 772919226 1250 772917976 772917983
    0x4150c020109061209020301020705010e1207030f0e13110d0b03060f01270c120b01081e092b090f270905010e0703030f05070803010b0f1c020c1603 65
    0x31140801c595071182103200c501307000c08100820400e00640019003642c100c20825122a50350300b4118071044010031061075640c910541d46818514a6100644499140c1500d01c080c040b0b420180c10103a07407060b90900c0290386140c8100b28480000c003184841d504400c0c8041c101030300e80b42e038000b6949400186588140b601c8041d80b00f2b16800c00341e001e003200b07180409000310405034806400c00d4524601400f4100d5059946a4816119401c640c0041e10403601107103040c080c240703083c001d500100e008110b982c861001c92280040d10351081707262600d46800c2d9005903810304490814100130b81849804000b4446595032001c0035162041c030003a030701c83e910880032010307010315100d08004a15807101d00c48800c1d00d100001e88044940750719003580d4030042d96200d43d8101d6002031040507003010000341c600040e498501d0a080c060303568212140b0043c01000341d80b140c041030741a280d40d44d0004590b01c3c87c040400e0002071141805401000c0d400c400300600da140036004445200c0e034004019078040b20b40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 772920476 1250 772919226 772919237
    0x40e010b030f031e0c0f10020706050c0304020f041d01090f1712011e0e0f04020909070803180a050612090c040c1e03060b030c0c0f0d0c030f0e090c04150c0201 70
    0x40c4e0040042d510344c001c254118682c040c4c11808180e0003001d001440d45400c0c07001000d0b03562203091074948101c6d000100741d60a0a8401e0003840056100c102d0003140c980d0050b90006404d4412580740c0140c1081100340e4402ca44c02c20304002d040288616a00031028400e2040507500420844030180703a000729520b000000b1178010041100301861600325000400d403100d00c0900b6a1250250b105403842210360600341ca95010500085040c4120b40c00e038072000310350203801c034907040500c09900c92044a449541c840c201b0b98481c0ba1031b030f5440075154010310004140550300c80100317808a10100c02107854218a000340341c0d440e038050616002e03141443e80141d90b9503031105e0309018003202303a4020200110402d0350710280401c062241d0001140540c21070100b447d298806240c90038a0a041810340440320340003441c203230b4078041c0c0081f0411060742d4981003605001908107000c072003070129209080c0c3d000d0542001d100c41003500700028000d5032080c00312119054102d00f4151080c4c00b0001000340000c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 772921726 1250 772920476 772920517
    0x5040e0309030d0f090305010501062006040323160605070f020a0803010b03040303021c1509361b170d0f0806131d060f011406030402010e040e010b030f03 68
    0x30310808400844d45180c0c203114403229101d441e040d0840d10240c1201020a802c1c0d0f400003512601321a0440c8802c3d02040102600e00e0b140e5001003030040817804982c0d11800300c01c0c01e01d42061010058418004144240210892190818030f01504040d10900c011590b01c1c00c2e010842c0d40b000c1584101142c000390b80a00e16440c110304e001c510340c802001501050703800d2010130840807004c007800342d40e004404004103010f400703801c000c2c0c1c0f8003144d6030060905620704102c4c1003240c03030f0704141d25294589981000582c051250b00d20741410501c400300412141200f80e00c1820321041c50004002d45000ea41140c2500e100001601d0381d1349800b01c5144045181c5003e2065202d2050400c194044406403000c05140319520409041d42c00194405500441000c040140d0040400103640e00441e24022103c195241c006a40343e20703001c80c0c06440c00744400100081c00c0d640140c0182d0714603440908108864040140b40d24002c10102901c80c0c824000c0217041540751340000190744000d4405141841e910 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 772922976 1250 772921726 772921753
    0xb0304060b010e030a0b0606091206070809060711060105040c02030c03030109021c140f0603280506060607020d061814030d0b151225080f01150e0409170d020405040e030903 76
    0x60302706030b21a40c0d0111045d041c9000b01c91051008a020304170342d0301c64103410f007003591341ca5003032a000822400401c01410790810340c00070b00043e9503044032029900091800c5000d40b0403400c40c8203c5403030740070303522001000180026040c2d00a095281d000004500b048948031280f105881c6400ca1400180c401e0301c0110303d501580079003a5400040c010111f6070610400e0350f4500541a06600b801002039440da43c1c0001c3c864240009a48000d003211042c1c90700007264001106605101000b8040f599141c484021564044514102864016840798004a00d40d41c055540ba0f11041d99500c181e410441480020b00306080d5005c86200001d4000d41024051030124225040041820160040c50800301025828015415034454402c0e42c030070700b0510308400340151418041e8400b03207040c0c036043c80000030940d100501c114910812980412404468184210703a50200c401e12003845078001050f1030b00580b590700800440340240c3d02800400b44140c030058076030040300041074050300040080c0a04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 772924226 1250 772922976 772922989
    0xb070605091c0c0b06090108070b0a02161401030f060b1801031b0e0321071709040e030301050310090b011205030f030907030b1315050606040b0304060b010e030a0b06 73
    0x41410301040b1140b5401ca003a0700000c0800c05480750011800500701c0390141305240e10180e902002c00da500c0c480e50751420a00c555500c1440c42100b0346420080340401109100307116020000d05110303500c0510711f444818866882010002c1d440c0071a00d880752040215049009a4044412282d5103608101014407440450026622041d042580d50f500398100000703403e92500c1e5002d80342c1d1700c3c2544168580f05140c5040c402c0341c50311911500412101242800d4181110041c8d580314882d452010040e000030544d500842070b140c2c0d40300d03080135000702d02030754000081d504980c0114101c0346022011031054040792a04000581305503010703030040c00420225250028441d12500403a0324041c48118240e02b50f410a4401992a400c001400c10600070401d0000b900550401e010440d40d940d107075207100c00c2c0850003148680310b548031340c00903811f036951501f50380040848440d015502d242510f05000100080000c15010400165803216242400a2010104e0703074802d85400305e44e110b02040100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 772925476 1250 772924226 772924231
    0xc070303391b080307060209210a030e1809060907090207050309120c1503160e060a2a060f0c0f050315190303030c020f03091c020a08070b071205040b070605 69
    0x14451110000070f20824208010001940148001600c070415002089002102800408a040003070000d81d050b080c00881ca2800c000d40c1428008548034003503010807030380ca00001c044440400c1c0e000c10001d00d950080340c03191003015904255112a91980b50520890040c504040c04a5005201140e140c2c1020404c05144556440071034064407a41c000245501e408080480350840010051044680562324a00400d1106041c860b8030031313090b200400d40f94040c80c44100100001100c0c1a210601c1e5402d00c031424072802580b40380000d46904100019010300c00c1203002891070720340e1000042e4070990081508420381d0383c5203131541e01da0b0319020038100041d070130865100d16600c92000c41029520b43c240000c52203a1008158103d0300e21002e4101880b5581100c0786800810903c3c020b44d40c1c0325030505144031005100ea515218500110740d606d4250703003100e0558402c0c040c0109021141d40090318004d0322500c0d4100007a0841003003283c6d54026840b072042c0305007043c04007000280007500080d5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 772926726 1250 772925476 772925513
    0x9030c010e070f05040f14040c080c01170f060111120403020312131a28021902300a0302061006030c02060c09060705060c1b010e030d110c07030339 65
    0xe1f180020140d0580491003606d0403543c002c1410070420440c00d0a000301100c565003400c3c60340c80380ba04180c0040109400034000b040140780040081e801d0f80c022001290f0917080030702240d402d07140b00c03039480b60030f0b602c180001d0b8170038480c10613892802c1340b40008841d124200003400f41c8800c3d2402c000c801100c10801707020003042c03605112650030010b050b00500c00404124200845100310f0200107400e00305102d6644171286030384801080541c81e5074500e05d40c0031212410605008125040440b48210764040318a038600940320b10406055002503101e008512000140f0b850950700c90303081d000c484200c0050005070300100c0000c1ca0041060016062284001e00403601c0d00b6507503550716060020440d402c958004001c0b42e40c030003410500d107174001c004018030020003c850b01d003e0b21030b56a0003080300700b0f40d44a49554020b03003a6803020303041e0741e2007810f1002100d0700c41e5203914000d4120b002c40001d2402c0d0305180c84c121200c00c0800140b43d14030221001c40c000054045494040700c58a0922942 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 772927976 1250 772926726 772926731
    0x100207030b0a05161b120221030403020706080f0a0504150f0e011b050f03060613030302012007030f2708012007030801060e0d0204020309030c010e070f05040f 70
    0x458038000116204201020001400d45401d04250712110b0300c00103000b00300200f4038203120040d17000c8080044c0044e04400004001012960200c4c034101c029800d9400c04031500c44480d034001c903905d000d1402988030781c081e0356201e5119001200c607140229540c85440e1040404a002e401c0d45074480c82d000741c0125814502003480308442416507040c80101c0039010303a2020000301d009003c1c0300d5011030b0848041601c1c03003c085010b00034043d000303502e000d00c0030304030000102c1c61a0780c82d40c1c01c48900407500c4544c103c029a132030401a00a0140707804c03901e601c0840c14400344248c0614002c80321001e6040c6c4039100210040002150780802040942d100b40c1c040401c2c019480881d0341004008080340000810502c10305c040c8200401c0c00040039502d841014000d00c4000380e001000f0906480b01c91070b0007090400c413800029504506000d010350083e00c00010300514150200003400c004071210002d015001700c8150565031070009104551240c0716001c0306105a03e03090300b00f210481c1020401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 772929226 1250 772927976 772927979
    0x180103050c1e0912060403081008100209120a0f03080c0f0a1b061811030304150c0f06050f1e09070b090303070203060c04060f020d02060a110c0a0b01050a0e04020f100207 75
    0x807550909000d050132640e5031016041108050b40200607941c8848a0fa0b803441002c0d15100fa074564542090880c070100a030040340203042500e583c011039003410200400c8030707060001414080d28030181c2c2c500039000240c00340c00040c400d8440104640d0240c1d00462801e14000383e806044940810380c43e010100074001094800c089266405000200d2450114480520685240c00004203e0b00340405d8001d8005200130003880200c0b280620010305e003400c000c82c906c40f0f1884d0440701c1060300b1348001d02c22031500c002d000c14038143c030041e24402d03505444151681411544610034401c0116040c451692040700f00380030441058028184242c8050102d9091a9250340020305082d41160403034600031010804200b001d83c41030034507000404a001600350f1014880b4000c2d11005c00030698055251039041420400310000101c44030300383c03902c059403070454282c82c045400c42820304c5502c1c030401c00d00c0400704e0722840447d030703c038000c80d801061080046103500a00001317601041c800d03810750044400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 772930476 1250 772929226 772929229
    0x50c131d0d0512090a17030114011d0f03030d1a100215041b1d0915100b0a3f02213606100302061c150902180103050c1e09 54
    0x80e81c41c09481403c031443c0d120f40c10039507142741103900c03181501d0402054544200316154502e01d0900c8004045d82d5401c14401a18042481e41c8511060781c110725252500000000c541600c44141c0e0f136000302c4410381c140c0668101241c1c1d407181c801021101844600c04600021109842103035045824520300b644aa075994032040191207440115440703c4c6c20384200a14208107000901804901c01403151040c00c021a1103050100103000b070100c01d00c0700040d90859140078403030070b0b959030199034400104404c428901040d1a105840c000920280100c071244d50800c1d14002c0c1c50205810342c601440d004040c1405d0151980c002e00150414410029140a40402105a0100c583e032100d0030040c00480740c0311f1030703240850040000e250094405030a00041c2d4600c011160001e244091030010743c94146091002403000520080c011004601c00096600c6c89401070804130b14003850354500340344c18100640568034110b40707121080c181000100c0c00c0840b0301414000450410402c02c4c01d1406030030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 772931726 1250 772930476 772930493
    0x30e1b18070324091d030a120f0203070c0201141935100f050109061d091005180f011503060504020f041e031e050c131d0d0512090a 58
    0x1008103490f8100960180f00700b9809002d200780883d49400d01c1402100b030406215104d01940b1488000c0001c95031428441c117a040d00b0050404510100455990505d03c50203440d80e80e410500b20301041d0305143c05c3d0a1103070000d0549001040800d01c1e0358401e0940700c005c85400710384411a403a0f03020020303100710b5070040d030340004640e80441d03105008140c00c1c40d0a880c200280a94050920020060f5017482582d83c4044e1500450380603051443d044170750781006038071041c020314020703401001c000c00b00611900515000c82c229001075500e282462080b401c07010f107054048a20720008400300004001460388a501d5801e40e00980c81c0001e02c0c0f0340c485000070180c0e400308080800d140c2c400708050140c1d40302529003540700422a840340615600e0360340c2e11843c084905090040c5848001c9070784050241c1808004a0880300818500441c2d0030002150020000c13460310140141c141400c030682c1c4840028019296203454651074205940d10741c0c00c0d204100e000309140300c0c500a41c013001d0700196080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 772932976 1250 772931726 772931771
    0x190309080a0b01050a240318020409080d0b01091424030a0204140303030603121b010204120606050d0b16050c060405010903030c020106030c0306021303050d030e1b180703 75
    0xb000d0070142da500d020108004004140c01c00c0130420100840b520244e00d04885a101120345402e01160f060009000a105078410210280d00541424089030401499200810081c0742140c000c0252882d07103401150406800c1c060f00c3c01d0881002c3d003100d090b00e082c80010400d0202d154001800784203281d001d0401c2c1e042583c0d80d5001075004202440381a411001c140c0750f810040c0c000354114a00385002a96809015010740012040000c501d070b00c20403141d814540340700401000355a41e070307510f624903010f900c03148401f512804d14140001c43c0c02d14121110316140783d002554014646c031180c280c03008240c0c03520001ca0501004001801c0704007814003010f885580500d00010360a82c0b24100034007651741f038221340e500b1a40342090038000a1640858942945c2d0018401621000f4400d69203846c4152a04050001d02c20140e042a0043e8160420220840e03580f0645034070340d9080c040c40d03611030000324916030310103050340c80c0c0780d4a8107039400065404174144c51702090329541c483d040e583d0322420 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 772934226 1250 772932976 772932983
    0x624030b090c04090803150310020a020c0405010510080708060a0e01030b07120501060507110a05041d120405131a130f060b0a1e0918020304020120190309080a 70
    0x18181005240e607800d02807464040029941400004c03280d54a075402488000d084500440d00c2540a00c0300da2400c200920040d9070981c821035480d01705203406540c518414400501c038a007040c0010400342080320218414640d180c850790450f0302d078000203940e200801050300360030210060002801845c00c00300c141c0214082c00c5000840e040800000300703549241072074a01007030f0500004004241d4058103e8201c00c0d04040707040410040a8001085140c0755488680d20a00b0466085c803440a002150181c290070710701100c7e8103c1d84100005c00a0280b40f18071075002030260000c5422400c1c075000b00c0f5004140c405d210a1403e50403002a00680c01c100d4945001540c940c61140c0042c013911840d4040c0014603007550521108000080403c203010340e140c9040413201d40c2101d08180521509070140c503034180d1008920680400c044000d42045038181d000819145081d1802c5a9000c410300804c0e0500019200d944120a006840320a880c1030840400001c003900244111003804100e44140c40b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 772935476 1250 772934226 772934243
    0x19021c090b07081b090604080607081e040302030a030b030a1a060102010e062a0c010c0203180105030613020a0e061305010306210323120919050703062403 68
    0x80c0e5040ca070003510801030007802440440c07818041d0080150582809a07021444000d42c0c03500b1840c08a51741d4047c592141c1d0141c031a0009000c60141c0001c01e29125840c1d099102040b40d91403c4076031410307142501d0143c0581c10400c8012607540c401c5d000400f203541c3c0982142c130b9148071669282403607000c4064840b40000a201800115071f07080c01804076011000d03008008a007050602200300704000007400d03448401105800301c102c5008411340c3e560034200c8008100b11000640082c2d100d0b84507454091820341c043c01e440100b9030040301628021070700a000241004403071016840254090511002400702b051254000d96841d0001485c0c40360380400105942032504c030015061f601260006d59140c041002d1013207550f40d0710b98160a006815103499122542d07204001c46410a03d000600300340600081c02ca1000c510078103440d40203a117080d046400240c403d0b0310780c0c0c05c04000350b50000c2c444d0f0000c0e54108080361494000020005101104a00c0340755a50300c82070948055900031282d114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 772936726 1250 772935476 772935491
    0xa06050a0f0209060d02070f0212060402150c062a13030c0504140f060d2f10051605120c0a060509010b100309031710180e0619021c 58
    0x40c00340390141e0040500950524800340c00040a6025a2802c091120b901040040501c003110308462011a00902003082c404500c00e0030541707988003110240d000b00044034004003645409002c90b080d1702c90305806000a62148000c1103150003566141c6d039500840000ea5000180d03941c4014078103003101d054424501460352030f18050300d0f20030b40c0c8194417039032814059420b41e000004185621801a40c0306d14600c1c0e40e030600052000d004140f0140c0410103038010546009a403403400c402211000c00d81c0c032000300e010b000700200602d40d02c5050b0002003003803100703111508041d0f4950101c0c0388200245d480080074001c00a40d29040a1000601d030750100d5207400501496128581c0c204032620000c2c403400350740c24041000780007810004410140c0c0c070302c001c8083c58030175003600500c017412165088050800051003141c0004900a660241c1c4980d40b001020700c84500c00c80c0420011200502050780d50f12401904400343ca6014290301602040114601c0000403822002030101850025a0070b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 772937976 1250 772936726 772936741
    0x20406090807062a0506161b05330a020901180e010302060901021e0d09060e090411150408070f0608040b0f09030708070b090d021c08070c050a0605 65
    0x844a80d4442036050b0884901803201c1d5a0191360f140c9012012098004018800b440d02510b08603002c3c405030050040c907003170043d1803000c901d81062580040d6119411010302d421301e04002c00c1c0280b401806940000140494815201d140c1d80d8002c1260079440d003064441004c550070908101c1c0d02d44001680003039520402d60b0002c0b075004a2000e140c40114006017000d108140d50801800041e209880100c5e00800c2a8030070000c01c0d00c54025080e006104c1c3e4004082030751b50b05050103d41c80464290140420014480d600c0301c172250000074400441360316251241c0d07130721145054059800100113004a1401e240c003400070f10091108800500d41c4034981100350308240650f802c05030400580c08203000210b000d0041e01600480c55407145076154803680c0c44140b4600c0344402c024040c00002c00d07840c0c2031050403481d03e1310035104001652150380f080a0102c0c1c48407000120880c0110042030001800340c0314244156211000381406602c0300c205413129443c0c424003990403545186c544003000303085d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 772939226 1250 772937976 772937987
    0x1a3303011104050a0e010b091909090c050906010e03100b0307030f0309030501060501080403050703110106050a0f05040c0302030907031101230d0c0e0d0204050a02070c030c0e0c04030c03110d05010c03020406 91
    0x705105c0843c4910f55051a60a204030301ca500c40e107520550140c0041d598030850003040e140144400da004104101380c1e0310702120440b0303062050380d01c113040c010006a40384d402403d0305044000018040c010b61040c0340031500090540c2e02d24103800d40b0620001100081850084035406070094031184a8203181d8507042d8203584503904003504202c861824803000940103c180c900565045c01e00310f911441c0c1c160340d98010303e0246d11041d8000404900081e9003243e8120003002d4030f02c10394061208101c00300342038059210a940c0c0c12515844840b041021403040b14200c90300f10014905480c01e803002c04001c0b50103510140d2440000c0c4000107450f1200c102d00e00c104214a041070800111007030101c00000d010b0301036034038080d0095441e03c0000304a108a03030304965039141e1005000c50340b41c0e181e0074041c01002c6280200030b1103002c0100414440c11040007540c00b120b60145242100d40d046a58881482c20380022040e00606079400040000380203006001425882f50780041e10380e868980e0040c40c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 772940476 1250 772939226 772939229
    0x110301060522060f08180718050606160b04031209060c0f090803031f0b0f0304030206101202060702030114250804150e10020c07031a3303011104050a 66
    0xc1101021010015613802c50f8188800b444541030618943e41d410180d030820107a14020150b07140541d14000c114900301c0b06a280300d07000090410042d41c0d80e003500b408150b1160006811500300c003580c0100c00680b0240c041030b0300c00d2180c1303000041f400d03402e1082001c1e50455802159000e485011001005900140049040701145400c00701c1e54607101b01103460340300103090040c40781d004503008203410040d209140700070604011016950100d0304002180c503002603a044006028200c045101c1c2400800501d0507114108190600482e00364200034040d40409400c0745c06540340d045102c4071044000c00b01d441040600284507110304220402000c0c845a1103030403083c00514130500c40440c420401e0580e02e02d00c80f000000307200414554591a0035070f202d1f410b030394103400000c0b80301c0e03809000b28040341100e1150b42404044036189405100c45001118002c0c007804540030249035103414100d02110080c4503903030107050340300c0300300c00b02c0c5c04e550209100e90903104000030204440d040c100110320 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 772941726 1250 772940476 772940527
    0x12120d05151008100302220510030c060e0f09090109020420030a0b0a15020102190302090609040b0111100515041b050708040f0608150609060a0804061103010605 71
    0x304085120009040d002c02c40040c004000040001400014903007840ca00038540040c0501c0a000030307020368000740710320601c244401504000c0403522080244100d0029242d108842e000300a080c120100c072010f141440c440e500c012421001c0c1c40326121440000d00071101d01001181014250040c4000c1c0c6441f15080f0060703014181d51501010108001e5035009044440b020686191640010756000c0d01901720b41102242c0c1761600600680550080010a80942105910078420f40d401d03400c030b000b00560746d600580104800b81091400c1e601440351550141861f0000341c15150380b00d46001d01510050316426a60018010354100c0004d00800180d0121014401400048a80184092201c8155091000c01b00c0e00e2420456514265800380680bd1019400c8a40e43c041c0107058000c1582ea0544040001040c0e04d4581480021110142c101030110b03898916441e204440d1b03c580200103a41c0c8507030b58060005000c40501c015030083c090341d0b079615168640410340001c40406034503401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 772942976 1250 772941726 772941751
    0x50d0518160b1e07021c0b060a031a09160605070203010b042714190b060103110906070201030603080f0a08010905090703080705160f0611030c0c0f12120d05 69
    0x4000c03103a0044200e0320a4203c072841890f440c0c4110302e400e0f003036000e44040290b20107880344103454032542000096204a01a02c1240c29680301c00c01400f140080500010f4034221031001005190300b00108415004446a01100c240c0300044007807040404041d00810b0024800090140540ca001d00842c803440608440400424420b8510065212420360140c856090341600d8481840b10304005041d018207402c2c29903820160740c401d0400b14603101e400483d0400c1d81d0354049a00c2d03501c030344920254128002801032400c00b9420401007140c224020032810140c48800100004d0313441c4000e0548030003000102612000310381005482c0013016000822081d15203010411040340001d0348000705ca4200c00d5040c0d440c1c4690501609110003200340c412088101223000600d0540301c0100030841d1781d550780e40e4030a000200301e01e81e00c0c2e109507440d9a1a41d44584c019a40304e140407183c203520603800a03c3c200f60500c00c40d001d01d013003c1f9844404616034102141c61021700c0d40501032544e00288a4058 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 772944226 1250 772942976 772942979
    0x30c080d05190e0607060501141e2803050307050d030b121c03020712121a01021f090c0e0103020f04050f041103010f020f030a0c03110406050a050d051816 68
    0x60342c840300d29454040003003110f00fa20070101601c4800c116403070710750015814001503031030310b40a808019210313010902440340c020344c00e10346411300f64285018020027080c0d40c04d442902162890403440c100d55140c0415103401d80000080d00400091880030300c9071025100300c003e03a05001d000c0f599141c9419009040f60403203242d0004000c02da0b10a1032060100c1c0020308202840220024042c0300c0c002403001038010100c5207115000140d0503114103690030301b27006143c42504951110140064443d01503402584200c0200030b4003010040d507401c40ca00c6c000b560003565150101c80303021952240708880340d10030040c0258100f04800070100c50081d1001d101c1401c00c0c08061020003030040c0b014105240c050400d110965080d0086209161f2943c025902da860314074059038075620594100100510301800658094040d0148046080e851119541850b142c5041520a68001c0d020a810800e040011620794460b510a80703008010000b0804c601c1401c002840d46030851407076807038015840380030f2b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 772945476 1250 772944226 772944247
    0x40b060d0b0103060f0b0a0b0c060a0b060901051c020a08010807121707020315090318030a05070b13030c0b070201020f0c091504420305191407030c080d05 68
    0x1d580381100c0d841040050a0a13942da43c41e00140004206640d1042800400113029045c0e40c0141800650742c2050f6041e0382c82c2d40d00d14038103c0d0925030001e500620244080c41d00c035030080014086502c1c100003804121804400394604030f80c024026200800d0b09903006002040040110801600213000780519500c21501d8940800321580c3c05000c4001c00002ea180854505100f080c180c5031803101e80c10510700f880b4100d50348039003164000070004104101c40354031500d0002044221540c00c10044c1c030f401c50920038103015952000b40032810300001c00e0000000201d442c00b83c14010700b2030501094490055200080c1401c8100400d40007a0340001e80f050881e0390350744035613a04000605140220340e4807900204000e07100043c038211960614030000b541c84050340018907005600000c64800c174540545c003010081c50180070103030050707005a0540b00c0080b56000b06113180d60048410760b0400e0f6212650900d000d1460b0000c071440c5030b004404010000040003201442d018505246003012081c05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 772946726 1250 772945476 772945493
    0xc060f011509140f040c0305090c011b1b0e04030206041a04170c1e0a05010c021f051005062803090b0f0a0b030a060209030610260709090b040b060d 65
    0xc070300c6001441c1d4810301d0160b4444c1480c50f980580036006001c004600c2902800402c411030b80341e000d0740504801b40d40700390b10500340c2d45503021110040854001203078403009802103044003005466019202c0100c1c0290007010760350310079032081e0300808080c0782601d03040350242070b90400b10412100f0725062000040d00001c2004104e80400c040310340b105003d01d0f4503803501000c00a0608128610b0400901420003c240340381602d001c0c8000b07000e140620401203030303280200204140c00c0b00141401c4500340100340c0103580c1007800c00c280340c1c907259203680c0010103580c0055001c2081603441500b065446d02e084007681c02c82c41503405e08010a410b542c0703e0713120007180200020b20741c562000004d40d2204180c0d000f64091500070f03044a010070030030301e0300500035841054498404d01c5650000b60101e0501a42134055074944030000541940351105505115800b44690302e103402000400301e86a01c5510641d025580540e0004800f0f0409041c00c1610b10b10140c026800303500d180140002094055 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 772947976 1250 772946726 772946729
    0x1a071704081606020f0a0314010501090f120302120409141005011403040f0f1b1e12061b1809020a200703050307200906011b02030c060c060f011509 65
    0x44403200319150b074030b141600007031003545082c040000c804600f5082c0a64180c0c03100741c070f401c00318480040d1a6255801074400c41c040d0321808240074081c2d8810702010019840d0f181000e440f03401201d84410790302c1582165030708640c1080448940d00c4030319604010000c00f2040c3c11920710140c1a6045042600091000c1440603600c808401c0000107d82008080700810004981115603100701c08880d2a010403089184440d80d0546038081d007020654682d8114200182c10100070700640d003510300b0900d0301c0201910202925150303070341c21800b24010b82c00005002c0c6810b0950703900c02c10340e6440c8ea403100302844540000700818410300c1f02e00000790700102c5102d0700c090344043e0408500305d4031004918101040e00020401e0101040c0d15081100d00b04c7d04102e1140c9485100010107101d4040c094950802c0718014006400070b0b114244481502140210280c00a42074680b21080d183c041000c07030b48107101c0a200d0364000402c00040746000c491040c00340400807085603104003aa50001d0003500c46 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 772949226 1250 772947976 772947997
    0x6041b03020703050f0c010e0d0f020a03080604020c1b0301060b07020a0605160c120c050306040c03080a020c210606010c030815041d010e010501050f0102060f0a091a07170408 77
    0x20354142418050401d5440d50111710050581c0c4405460003603000e00600d1001700490712600c5580b4040b80d001d180105043c00813a4003c00108001d42c03030880c1d009038058150750308581d08100345e100d0510140300c20b05030440c4050317001200d080c0070400c1c9801c40d07415621904c42d0b44018815040140d584500f10002c8a4880c9040ca07152070104481002002000a0050400d60381e4a40020801040000410a507004520600d5072a650b88141500c44004841c010915a9016400d100094480025283d0265a4411114171598074004580c410040e01079403907040500c540700080f40034040000c185d22990a10781a02a01d01d107950241007284090142e20500c2088074040885495640c09840d40d00c00315640390f50010445040c080c02491b442d1640c1207254202800882c0a040c0f0b440201103141040e4018940307541c420310098419031000e04441d020b01e80b40c01d150300c041186c0d034031758481e14440c42085200600b040d610180c4112409119941840202800c200205031103d081d1143c0405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 772950476 1250 772949226 772949231
    0xf020102120c0702010e0306160306050f010f03092a1a0406051603020102070f080c010b0a08120322080c01060602070b04091521020324160203040b071101030506041b03 74
    0x3e441c801650030720014005545c05114590070403c0d24a2503101c03461504105841c00c020f03898542e0300340900c8405250b15280071882090008903094860307844090294060a03c04c80c20036008201c04018002d820703000b0008150207002804240040c04c2090441c0520040591a0510300040602103008a640003e204c0c1e00045d181000e15000790115034005900c5040e0301c41040803440c2885c841c0d0018036040c1c48035841d19040c0140303406c150000f001070f260010010108814012100010b40d40010002641e01c5001116002c001c9403e00c14001200d20070701744580c82e102c0c5590810b00f141c0c1240c1c8482e0443d4410003003000106464822541518425a004641c00b541c0081181c1202c4440d48101060046e5200c2c880c000c083e803c0c00c000300503108400b61034086440c080003100700020421001c030f818507803002244841590300d060103034695050045d01e041036501d074004000741c4c01001003510b03c00501649658150b07454810030341d01c10b004a4003081201003000f244207100315007030030000915a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 772951726 1250 772950476 772950487
    0x92202090702070e13051b060d02220806062b0b07180339050907090e040506040b130f1502090406090903090509010312080c0f190f020102120c 63
    0x1d1003403001c40c01070011082d00c50200d09000800404c3ca001705541a54140194940340c3c80b134050a60002c0c06080000f07003003a0400c0c9094035404002d40c09a200e031803d0b0160244000400489054600010b19400000e40050702c0c0020a0140304240c1505a110f030000002d80740b4900d82d6411045030030241c000403113588035560f200e815101003d0241600d001a0843e0200004204004030b45024a41d68030004481c01c0c00721002e01c54100e148400200d821441d03242c01440320f8185100f88035400442e07441e09401a43e500ca0080c922000b00751410303200b82c1c000404100910111402c403940258101200e03448440c020703203800505040c148001440e41c800c0d04505160110b168042c0d0340f0055000744100812555801d50320020401c61404401140401d0350001d458949000803c0c1220342003003500b0100c40e0550f8048a49a40040540c01100d0b418000c580d0042010005042da0b03e4003075015014036101e010002e402d0f1a0003401d403004581c01082540103000c1d0411010350032181c020145034448 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 772952976 1250 772951726 772951741
    0x70818060f1518070f0504050a09023004110d0f030305070e06160b0604020f0a030b04060b041e09020c070e1801050c03150303040b03040b0406060315090209220209 72
    0x407070b14800381a40000c8850340745a4401102c203280f4040d06040d140c41d4041039200300709071414001d9104099022180712810800c0894680041c00311509074443c1c9a0700b81850300304c00d07070101e40ca4400d00b000d86c5014402c200030441c0790010459504021900b0030301c00d4040d5a00c2061030070a0160090400d6280c50124a0302800352100038061440204441e807150070044035410b00074880101910622075180c0800c0d00c60409200b1540304078000000c003881c20054003001c0c0d0162840d06e030724030340203a51003034000382c0c40350404098005000501a090600100d2000602e007100040d0800c10009104100e00c0e1242030b0005050301c01c5030300d81c0c03206941541c0e401500d102c0c103440d050b400d1030f05035091004101c550040c030340066100b43c049110740d036030311001007017030690740c0c060741c065503044010410124010070100c2911030750080c416103021410740d840e0303900c0410b000e12240c00e208000b5259000d07902140f410880c01d0390303c9410241c01c00c014045545041804c0090802d0180c0140003a00c0802c010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 772954226 1250 772952976 772953001
    0x612011509150f2c01060c02031006140d050304270b0109061b020103061d071e020318121605011412010b0702030f07080714040e1213031a070818060f 66
    0x54100d04c901d0920306681d9032030040d20f010138541080380310b4098004800c03c4070001c2d116010640780003940d5120744180c0c040600c040701c3c01000050b52140300500000640d120b40c1c03003115503501c02e0a4008000002c08500704025543c1d41a50241848810803081c802c1580c011003c0444c54121000300d01c40b130100e80016001400203070442d102400303c005046988682081170300b4080c00d025502c1c10004500400410142e0810401c0d80e40180c204016030f504142190810b440342040007089040d000100042031860078000400041003d00c0c4054200959a08004c80d40c4001d4040c03403481b490072001c0311000e03c0254050003210103510001c100321095440030442c56416105107422114005d442c0d000340c2c4c2da5801c540c0f24240076410055030b00300305424540034940240034801c001b802110040d54100c00030b900b100440394044680700c840080071030850460440f001003014044843c03070901c000300409003c00108019420482c1c0401070560a80001d2000d83c80045000b01c83c0e410780318000807111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 772955476 1250 772954226 772954289
    0x112060504090c0314120307081803070b101a040504020a050403231c0f0c050f1e01060f0e0c13090603110102010e070602070b030612011509150f 64
    0x10020718200190b020800608411015203001d91804940e0400c030888503503a0312080d000c42000c00c0f20501c04104070f42c1c000d440c41c54000c1f0380e0500e02042100318001140c03551b000342c507080ea44039000100340228480d003159a030000e00900201070f100900e80d41042d040358441c0d032103001e00943c0c4c001002e481d028412002e58001d568002104101848414601414840d1810307101c902030007034403813000d0007403e03020540100544507290f01002c0445006c090742d028055600a0300c06010f003412000c0080301c00c1c806106421341514408400303141691401b070855003182c1000100c6a05050240038401074400000c0c0c2c000c02c01c03a00715030354086840d00c80500200c41e6010001b40350a222020081143c01c0f400080141020f0b402040000101a1902c1e50f820452241d44e0140e0803803041400301110241c000c0d6486007001d41411070642c507000440d4211a04005801a4200c80741d10034030210315036005243c408078110048210a0381400604140c14030603214225100503419880020072407000c50880 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 772956726 1250 772955476 772955479
    0x10b180a0e0a031e0516081605010f0207110f0307030b150a09020c06130c09091703040b060a0803031501080405010b030d18080102070b010603020a052215021b01120605 74
    0x100741c54010310b8040c00400803000c2d9449013040050140c221a4400d0040e10718040940450005084e22a203c1c4540e1340c0c030061492281d13850248000001c90800d0145e14400c0c0d410a0300181e480300d8900348008040111003240c2c1c410201c00900000540c0c0018194083e43d40094851510b51981030540340002d001307031005500b002035000d00083c021801e40c0a00030481c1c01009446c256903500c1e0788410240c804180081049050000510120525a2162900f02d100d41a8500c0380300c1701070b00b9110aa00211000c55201412208218141c00c04a60395002464250000c605605010a4103403031821340b031f43e60078100140c0000107020b02000f504409014070025056420002413110000c24021440c8002c0d80402c01140001508500500c03c90740000d41001c094913290742003040890182d842810b030b0004114090000500070030f11403014410004002031880c02c0c9500e08001c001c410445400c070301e401d6400ca407400c14691070300720030340843c107000900e04000800c21440240004017031940245 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 772957976 1250 772956726 772956733
    0x30408161a0a060602030a14030a02130e010611060403081b070f150e0d09050f040e06010906060e1e101e0206010302120a050312040f0605090109020405060102010b180a0e 75
    0x21545007121244003401055602d900780034903525003906907680d00c45c1e1596940020000043c1858404c400b0002e1030f040040a6400340c42c0c00d141030f1580e41440e1050700110303041c42501d00100241500302c0051420180038001401c201d29150301d019211060041069180300000c1545010b001030800031201c03055805060400090410b0528008802c447d00d03200c21190300c4c0182c988460200041c041321090300541e030719a030741403c00e8213100d2540e5201444582150301c03803000d0244450203100c2e482c0031306004c0b50005281da142c00002000501071400c014002c2440c041d03081c8803480760718070341e001602d0161102280001809411114070401e11500000700050801050310254081005412030b8000c03500030380e00349041e14005481c0ea5403001c000304190b0007007000c903800720807001607660310500850083c05144110b48404090307410444595201d65540c03400042140750902c83d1541041d400c1c0300070480d242c00240811540e4103104410b84008481c00005078066120750405801040008140e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 772959226 1250 772957976 772958003
    0x80a0210110d050708011a090613030f062306060306150c01060e1006080601180b162906040e07051e090f090a020d0f0b01170f01020304020603040816 66
    0x12600c00e811a40390102c2e9541440d010446007407288a003907040c0c8815001c0c6401f002c0c402d21a14030a540300c22410f90b013001c410311819200b0340c10440b4450080d030086481e81140c070b003c1d107000401c4402102028003482c0804540c4032019510425041d80580140d0340c0c0c6940f070721110300050018100c1400010000d00c0002c1d000000113040d0881d008803064040560840d48403131000c1646404540200c00005840702c001552640c4500701611100d040301840e1440340d611561270302070a500484001c0550004601d0803170801002040c00c4164842740a034038055843c10140c1e40805210180c80640f0454840034505d80d141024040100100b40c002e004d0228000708aa04000380d41c1d64080c0d01d0311402902d03000036154200000c0340ca11039207088001d0314004080d5801c100040c07602c1001a90030403800f205690000d00362185403030103021030119001c0035240254055107058842c51014145034014018400103854050036250030542c4400500d4482001659507007442110440107460649c0312202c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 772960476 1250 772959226 772959251
    0x21b031303020d030c0c17101e090f150c301a060d0603032a03080703060803030a090204180b0609061f0c110a06120c180902120105010201050f04080a0210 68
    0x905240c444c24800544a0088d460031000c002c8840814480c4034809800b1a25803010340103611110001d4840c5d040c80060320400c0d04e400c10700020110350551015510749200c5403035504454072804000d6902c0c0300c0c0700100c05044840d0718044001c10410a41e6445d160010130171490100842040d60740604a151102110b094010284c0704130f100590204549174071100070f6005030b54211035555a80100400700c07424984e0129850100113004a040555940c070101d81d0101c113000560150204013000300303074007000340104011901c024405407903619150ba03008000070302617030a02e54490000c494203c0300e560f480c2c01043c1208504003a44034400b85200e00014550781003201a090306001d080c10300c601909034001c2c003001c281c01d4019040400ea960b03a40303010507105500310608100c1c1601e828901c08003a40c60040c0240c00300c0d004951020340105c0c1d40065a0400d00d21075005240910090109003081c0c026205600c00c0075001820304140003818200c51802040000000c074254078042203138100421 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 772961726 1250 772960476 772960499
    0x120100c1d180c0a0507020603010e09121309110c0d08070311030606071112010e0a02040e0309011e02070b0310080105071e0c03021f021b031303020d030c0c 69
    0x1000050048902180400754180750082145000c4103406081450f2110304090781d642d003000c0c440c01308110041016000613102c0c0c0c0c0140d8000c1601c038000304000c1c104072841e141000d641e40b000010042041c42000b1480e4840e03400d14007100c01d01c0400007480b4403043e40917078a504c110404e0304001e03c00c840c0000c48440c0e2060140d4400c1409031f604102c400d1080c143ca40042c4415910690301440c00d204090200303051142d0203240140052400200a1045034514256505004150095000a0203880960030140140301400d228100518906076030600040c00402c0081410036581c1c1044da03100b0700060081040001403d26603c01d15140d2403c000240074100c1280203808482d401c0102281c1030f070340203031500084900014561409810300301000c0318400c1c44040140c04510440b40351209003440d020407e4500090201c01607521001020a01400300d412040c00449034810062020401d05e0820f2078401d8903030488501c0c0c040c0446003401c4803200c01d141006083c110395003030b001807004c5130760 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 772962976 1250 772961726 772961747
    0xb01020a051c11010903020607030c170c0d2a050309031b0601090b01033e030f04020f10020a08070c150e0406090c050d0f020403052512020120100c 65
    0x30341c2e60407403c1080405050a031946030b0f0005025a008001003140f441c080c5e000701070000300d00d00d1700107444050b0040003002d201090f907514807250400101d145079a03950340503400068562001406030f80c2c400d509010400981501c05000f000030200c0880e01b0081c042c01100c2101d000c89404550b01c4030a00902c0d5242c1d9402c2c407130000007a00c4c05d030100c999540240101c030b40c00c0038a0030030700d008a01c6183d100c40300c142e07000480e0040c581001c0144207402500e800514022a180e29888000c0d14042c4140003880c0b600a48036482092030356882c0301455400120480e500c0d90007e0001d40f901c03054a490a2040266040460b89403074889641400c01e1344a0001c0e0101e017812030303007440030726038030041c4100f1545c0418142d0300207901008580701e005401c2d0404900400302c000c0040c6840d590f612030904041d00b50f8241510100d50340e500d001d500d4030143c01200035001c182e8200300c01526a0b80080c1405000c1403a68038400b800042e10b0300e0040040c000c035250401c00c1d440074414000c00036001030002408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 772964226 1250 772962976 772963033
    0x80a06090206121018110d0e0f0f010204031403040f150323040302060c092407120929090f030c1215010b03091515040f091104110405040b01020a05 65
    0x11a40300000c02031450280000b00742202200d28508000d203401c107c0544004442c214040c80340018055600c0741c1040301d800144041000141c4807801d615000c8210401d507001d411282d030086c04140301205104616908031240480010003030200c071001035011f407840240c616a000c9407400500409000725112600c112b00c2982a80c100c0c1d9250481000180a01e12542e500001c0881c006030a0a4401c400300d204040c504903000d0a0215640d150145403845140e0300c00060941c4204003c111420884007203c01c541c4414800889580409003081c0c0c051a607070648241c03500c440c500c6035038605021164039900064014105000c181d803015640700342c8420002c50f0f03407294100000c0d2a19401054038020701031240900421004890700148412001e811a0410710030b01a0b2030300c590713440344203030484c07100a40700104190b51141890110b0a2881407040c0c002d0341460300c13040d00c6504440840741503800441e00064406100070040340740c2132610400802138840c04002424204c132419403190f46004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 772965476 1250 772964226 772964249
    0x2070e1803121e07081302130501060323070e09180615100801080309010c170403050a120c021f12051f08030a0807050f0c010c090807060306080a060902061210 70
    0x2000c1104841c0e07003c0448901001a080001003804200841503400445000038401200c1e80c04030b4803040202c0f4420b0b8032000202ea07940095031007209084a0468020b12455003c13412840d004101809503002d00340c420f8032031509000001c1030609200c020400c02020300003100c1192a00c8191890034a190024241c45036118001003102148200c801c0b078140d8414070302441c2060040340040d101c141050310304564004e00c9000f2844001e0400d0301420065000764001c1658201a050071030f8201341c04280b845c01c01c600da840400141c2c4500c0d40b840159201034282a8000c0c0005008032403540000150f0451503007000c0c2403101a084078449404a40c510f00044071519613a082c80660b644241c20060000c10f01035400641c2c010300580240640b80d1008550514100762800d9590840d8111092030f80402d025107000e0184140412030a4050503807401d040086508000006603240701c2c0c5003008294a4032441c20500315114141500d54100701c541e0601c2040c240740244035000c00e011300032300d0f0807502c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 772966726 1250 772965476 772965511
    0x1104021c150918150c05161b0603020301080c0f010219030504031e050a06150e04080712110307080c1e1e010c09260303100806010f0602070e180312 65
    0x1034201884100654800c88848200c000050410017910031030202d4000e2080c2400b1841c02d00b48505041d24440303200c1c4004280010314141941010000387e0450805c252041c0010b2065007000a058a00d962046509880210380280100c0c07070002c2c1c40b09140c508240a0000c0300805800c44050415644a14078030340510802e4001d288202098035005411381e0300400c02c00c03010914583c003003070b03024107002a61003400e034888141404a100c1550708a80800340000c10000780403600003071402583e002d140c06040b4171071180c0c0560b9640103407100a03000c030400082104440d0410410030203088100d0503100350070000100c159448404039a00044c000d074176400a99600c280c184a0f9810f40c20b06502d50890707003418540100d095807102c0001488903451020411012041080594032515190140d406039904243e0300714200041a4000b540541000f0750a10901342c000ca040c0040d03c07104904118640c4d2000d03800201c2801440740d900c5240000981e160300d060b00c001c8114840d0741010703951328505 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 772967976 1250 772966726 772966751
    0x110a12050409140610082d0402010e03011a01210606050a090e011a030703090b090d0905012d020a060c08060a051c06020c0f010608070608060306041104021c1509 71
    0x240c070480d1130607480440d00340701c049102d01805a85800045403038074002201a4a0448040480706103c03c0813400806000c1204541c4d020325901c6030090194000c0c014101c840c8601c582852484100741e05019001c294480010352003108a442d0243c107001c01e1016030f84d5110003502560144013100d0024007881e00101e103d0754002c040398104d4401c1d542d61046510128600c0c005508040c06107400c06403144035200200f400301170102c1c012034903580a895003c46400002e4504007441c0d028030306201c0c0e10140d5200f6206a81080c508051015941604241c84003104a09000c40d01100620407840c240041142560102c010b074814102690f007480c20684401c10840f130940d005406840240500e43c10b41c00054440d0050561401e40383e040f200324803131b000341c46420340301180c011583c50b6200001c1008025400512260040000e5016200e03c1c2000d403264241142c81c2d0b002a401140c000910004445100700b1082218055031350030808400300310030801e5204501d10503089580e007081c42c00e4151 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 772969226 1250 772967976 772968011
    0x180a0e091c020604020d0305040509150a080c0603060607112805040e0c1516050f071508010618090c021e0106051c1b2c1501110a12050409 61
    0x501c0d0140e0000c00440c0e40319401c001e11030020b80021010003400784800102c0d51a6107400900414101c40d52540c81c0044005124803d44181d0064506902071032044186468000c11650440800d4416507035032001c505051440701040c0503419001035505150014694015030041ca5100c0300c035202e540346a80d90030170001561240021302441d5006402d5250741031411390461428a0290b030059401d003c2a48418070800c1e88011301640e031500710f100003054559003404000040d0040d03680c01d890344c800c00311000303100b40c205000300001c2c4081003801c021421030340c980410041880040034000b1442804000751649545050707401c0044210042000e80c40c0103014190a95001518004100f00d90219040131004041e209503501d4014021051081d040d0b1032484000e0020721243d00700c1c50b8a0081680d08402c00052011001005c08050081d505458012403903403040900e0300c20081e0000c60203107810030701d0070307440203006c0d180b0700d00f4801c0c0041d0024050b00407180b214604000d003400c038480301070700e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 772970476 1250 772969226 772969273
    0x4050715090501120b091302090105091512010207170406030c020f21090a06050405010f03060e0f06041b08091e1020070f0b18060606180a0e09 63
    0x20a49007902400154480c02030000f00b501800300200c0c4200040000c2400c89600762030711406003480d10072203000c3d41402e541c881c1c0140b40035110440249095a036084221043c12a02486038038428909002a44c0940607601c07115040003231100081f0160340e1200c002e92051003400c02190500081d403100900100b82d400110401c1f4001d442c0007603079180c1180100803880c00e40c03500c07504240010708403515000000743c0908440e4551703da45506103000034141200b1083c44e40308150410380107020710640001d901e50041d51019036550b65844490000d000360208810300306070450f4803c84449070070380c031400040c05045a001540c000522081c48040c0340046000e806507641d01c900d03c5540e036202181d0045220603850304103540303c4900325660300256401514290f9540ca02280b1070710a000030202c400d81c104000c104200c0114090341100e0761103150040c00144200d0340802e05104c540c00a856021110500424000d002501d5a01800c0d0300c01054804030b149110340a076203d0a400c02020354007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 772971726 1250 772970476 772970519
    0x313081245090a2912100203010303030506030d0c02040902060f0310050406080316020913020d0302152d0c13240203161203060902030c0315010212090123040806040507 74
    0x81007565895070000c0606492101070300302c068a01040c20171841484119004644288003694030352450400806603134000d004507100307400c00340840007402c3c1c00031a4860300d0761303040e50080340141a500000e030160080c040500030b200c10010070800e9002c070703002d940825547c04842c00c10215444005403980c0b402054030101e4110401031301d44c0c0c09450326180a0307a200a0100c0c00c1a004401c030303400300300085174804040b40075a011070420b84070f168200e01855400540e41c070b000800040716404a0405103600c0b5080040d521030a000714a130064002c080300c100d50030136207203c403810359140c50186404138400003092038002005001c40c0c5080c4040122a8020186a04170208140c035484210f80900c2c118001700034140d5484000810800c1170018511a0f0b41c50504141c8a05d401002d891a42c0402c2100504540098558044031050a0140c0d00e800900386000100128a661b40b1405105074041480b9072040c0490005149000001c4243c0710303170310034000e0b1140107540b20b146001c0c030001d1031181c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 772972976 1250 772971726 772971761
    0x2d26010f1403071d24010512061915020610050603010320090103060903080f0408040902070f02131d0703050309040f14090313081245090a 61
    0x1005074189003003016030892402410359445540d1080c0d5a015810034500d225881c0c0614005c01100c41028100c0e0101d444074200c0c030030104550348000071722a05c111940311f1110700c92003000c2582178480c8404c0113104441c002c503158a454480394003860607480c40b020305005100e164005411041d50a10301400c0380c60203010302d42942d01f182d5952805001ea000501d064031006150711f8002d5940c404200d0080d8007070b480000c2c0c1c4481606000300450002060030b0802103443c0140310000d1044c1c4101c03011108111001602d40c4400d2405021301c400101c4080e5101c00c2542a060400300107034800103003490104612041541d0b04424181c07900c1644c1301c00740c9250020710400c10307181003a80290344a03d900c1c070000a400c44555030b581180c15003e81d014099075002042e12941c2100460800014050f460300610303950f004082c988580340b02d02c3c1d840c841d0f50301c0d00b683c1d2114180722100011241800744404072598450841d03440c00350b9001202d1103841402441c001c101180d540e4031500c880020320f076042 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 772974226 1250 772972976 772972979
    0x30201050309030d090b24030a2307080f070f060f080709050607030807110114180307171c0b0f01030e0304090905011505040c0c032d26010f 62
    0x5445540000348000610f0100700704030380c140140d510401c144548200f0811a0504041110001215654070141c512240f5881e18407800e54002440080327040e400b40c2110702c100243c440724604400380d01c3c3c2540d054400c400c804907141c4404a000780031501c01d007084919650303903a2030141d203610a82c03203084081038141041d002035500c65403215500080798201301c0032031035440340413505e254858207050300041d102c0414082ca4551000d613000005092070001d1248007080107070050941c5000d40000d1086081044100a000341882030f01d20f2a50440340c43d420784000701d0402000d5900403481c00841e074901c0100d04240181c0f62040d801000c60150050070858a440010b500601c1d481066000300c4c8028400000c41007040e01034280b94038071480010940c41078144184c1000b40564010301d00c581c0c1048050420181d008415201d4941c251814400c0b4070030404840d0f03a8080b201c080f1071946510200d0210f4015041702d8114420209109000012400c04d228648081d5080c0591100720007007810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 772975476 1250 772974226 772974229
    0x5060a030b010c080c032a07050d060f0501060206090d03060b0901030b0d060507020a0b060d170706020403050a0c030b1e0a021e0403030c021e01021002182e0e06040302 74
    0x800340d50305070103060840c0460036580b10301e8481c0d00501030b41200c59000066a03011080da4118064543e10300980151005240561481d00c841d401c0c094a0b000b0720810b003048042c0007054200c2c2c400da210051040051f56104e50001b03444107000c444148892240c800c3d000c0e1801c1c42882103504a0744410307602d07403c240d02e503401100540548085140e002140071180c6011a500d4840c0074007541840d00109043c1d0034034a442003003004020161031280350b45144150204d24a0000181e982c401515940d5503814945007040082c015030300003500074030800390440f040102e0f41f00c516007524028101030600e5920050902c0110820280c0349401e40c0f05140481c2c04080180c01800180c0c83c80f80e0150786c501c0c1150107a2700390350020f600980000d9082d0040c901582071040501a01c2600b025454018511000000c7d42d11000064108603440d800600e5000c62201d0600026213104020f01d800c40c0c01120300e071450740c20468403184002183c40340103041002c41c01070485e11010380c006042141024503680 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 772976726 1250 772975476 772975481
    0x8030a08071407050105180d0314010312050c03040902030402090a0207030e060d0e06090c150c031206150c0604020f010309020906090703061a301603060b0c070e1005060a03 76
    0x2a1620b40d44400f804800300190f02801503502c1031803008000c3c12aa00c01d0400c0e10305d04000c884040003418542425078140d10501c080311410b607600000300514181d0003600c211079901c182445220b00307000c049408a01c03c41942c005500031802202d14841d50380720300010104078841c00e000100880c0781013002c01d1141c1071180240c9003d814803c0c0004500c891542c10711b007410400c503102e844507040344042c07e24a1500300c1200804100554209050011440c0c9a55484c4030310030711020344e10650300018005a03178038150707282690030b1000100e4484418041055854000340c40c1288688604041c420055110780710760120341d60020113200321030303c407081401500391000d0041e104043d01c9100c04207013000a1910214000300310188150340350103600c8240400e00031030400003190001140803105049208108a030403500261628125000d4040150006d110310780c00803060f8070f00418200170100002c6082c0c0d0031030707070a4266495030342d49a900117400c105041c0240c40e4004018840403484510a5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 772977976 1250 772976726 772976747
    0x31a040905030d15081903020712020f0414070314070f0c0510140109050907060824030d0c020306060405070f0804030e0a0b0304030f0e0a050103020f070f14060108030a0807 76
    0x640036240340c2819412640d066078454039080b0741c06070311607204012417901000322001020441c00000d4104665aa000b51906054030413152000d090b140c07000305664881000d40c0780403800400402081030200d0364003002d050100d6030000442d00c2d10a140f420000c0c03543d18640305000030b50300d8203090302a000c0d0541e0010103000d01521588075000038924542c0c000d20511041c44801c022441056141c24000015103c006250700c000750450a010010950041400c54104140c09842074008281350588a4680450010194035125880c0c2c502d5007a500120050310090080d000ea89465560714180300540d0070680348580045c3c81e00740402e90303035442240c410341c1151292501000300024540014145442d079048440d00003800000c1c4403c140e04012185500469420081d0b40c80003544001003032081d152044038141500000c00080a00908088030142548061121404807880c10140e0f10202c0c46c42c2171850a204090011400240001c1a190400c0180e510138820b5600d00c40111062443c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 772979226 1250 772977976 772977983
    0x3091302040515070212011803052209060501030b0306100512120a020d0306060206100501030e010b0402030a0c0311032809150c08160c0b090a0807030903020103060501031a0409 78
    0x81c840030909a8a40000803403003002282da40307494001c2c0e03004201040b80c604a82101c0d6078034100312048580c04098001d600650103090658550a44540000016804040070000282056404200314140340d00c07043c203a640030790702000a213503840141a0758a40540304075400e1110020100020701d4038544c1d19812030782003001c0c0ea004581e18025201c16400c42c02c0503c1c09030700145240400203030b16201ea00c00410032440140103a0404031400142c03141d0b1030184504254590780d0781c2c1c032000400d4010104010000e00110350341c0ca003103d6518010403004056900080c10400380110840040007030343d004c0c44400303002c1c01d0740701c441d080c80c140c00025041207103854a0f1200b4204000c2010403140700e417500c0d945c2c900402c14080b010401001e0140060807481c25503c0843e246101a60000c030741c0048542c0202c0741c7c0c036980c4030440d0051900c000e03120000d041c280300090f42c0c2c04060f440035081045034402e8800307001c07160705c4100550607100c06461240c006030003085c5103078051038a5044070045602 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 772980476 1250 772979226 772979231
    0xd08070b09150a090c170a0b0907050f0a0e1906170f150f0106030c0e1e090703060b070201051317070f0e0411100c0b150f12060f07090906031202011d030913 69
    0xc123580e181d09030340c4101d4203260b0a4000d8a02001f00741040240c0c4000401c084611004035410f0481d140010310020f41802e046070014000340320385401c2a84204068000700c1609524a111340502c81e5449001c150070141900031681130101c0004c02c0703441d180c01100301c00e80d5181c45a090144c110020300c07008203114100034400c2d80a62464540c2c40d51803054442d40b540c151180f035600000d0021201003c0d002d0703810589410410080d4112201c1600d404d9582480c025503605010011042503058a8001401104801c402003c41641c002425002c0307070500406003642650346d2070041180d00003110090850b101d81107500c060f91a106500c400d058a0508001a0803240c075210003200d0402101c11703207030350181d841c1442c05520301821503600a010450f005504c00c00d00112441e25408090401c44000e252080420354890182038214040d001c000020000c0d16507030708207991054152100d400c055464094071465004100c2600310b404142440154503004a40b03050000c016042201c20b000d003503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 772981726 1250 772980476 772980493
    0x2010b031603410f0c0922050601300819050c01050916050d0f080f0c03130501030e0c15090406080a0501050a0c17060d08070b09150a090c17 62
    0xa01015112059004010203502a049003070842c5290044d075035204d280c00c1d4400150980199202c290995200104c02e000c0300f0b4584904228071100036501000514a0194100110307800d0012058080100c1c5070004a0b08200101e40728690345544114025090600030408804112801101d500140c54a0f1078528a440f00c010030305404c446007920000d10507001a08504070550444402d10301a090445510011220503510001d0400f400407009010450101c1c040c3c50f080000c40039286094814429a650b41032a0301c0415070308581c03405103034040b038034141a03030700d40401c005801e10b1101d8015010629091112448200c280c00c03032440701754401d4403502c021644031000e00c4103030556845500041018102600400181c90006440310100841ca00080780c00c02d120030043c2c2d400c4075055401d81100030300c2c3d0170880311034401d80304041d07c01c18814062103000c507070014600040c8071180c3c00e600020344669006e242070300d8683c9000b62069100e140240320030140144030100c4500102c04452121 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 772982976 1250 772981726 772981793
    0x51012152a0e011206050108060d060209061201030b0f0f0f1f030c14010806150c0109081902150c0702190e090303090f0a020901030f02040e0f0c0102010b031603 71
    0x1840403104000100540c002031040d50300a504040c040a013008180b22050514000804612008010500c5440d00040c203205001c01941204c140e51005005190345545400c0d1104030328000b84802c0341d03040308440c00603900442200381c0e9401440e0b0300d213145505450300008418200009040300c000d40f13214105d500b891131441803456000b0741c41010f4480c6502d143c00300d000d4401c0390b0703120711605001d40036007000302756503490201d0011203211004142d00ca07030040300228010300407040700a240350000549041140358420300000d0000c00c907401c50f41350f0030440c0044c0b880440191904022000140001001403412454403a00c1c0003040c1d1402c1e200c1966404d1a196421065a80c2007040d00000248004010240540003440450800030410b4174069030209000d50030512001c1c00f6170300c06021600031036907141c12017500d0700100340443d840e12807c842181c2d01c03080030601d0340b0301661801a0324041820301240044907d42e0321041d1083c00c5241d0b4550a100e10328050089031820054100305680 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 772984226 1250 772982976 772983041
    0x311815050412030921020d11060705040501120f020d061e0506030105040c0302120411031e0706031e0f050105031b0f06070206070c030b010f17060606090102100f05101215 75
    0x40807442e802821f40d0490740340d024041400c010062926500003100b00300d205508142290100d640070300c0e04003004440c5004640003820091090002c01c1d00001f4851003511a46e000401941c5070103a02000704d035072011a82407840c409204403a0403c5c820b100410152a0a500c5041222503a080141c42c0120080d1103041d450070403a0b0032100c90210812000702420100100d110700c450408440900d0199030804580e5103507a8480d580805d0384030380d051402812100031400311112600024040906000e4240c00506003d008050080c454400265401d441000310031a1045010704650410f00951080c010301741d200b0181641c012504021010000b10003044120040d0b000d010b42c4510303941001c0d6030000d0500c4a5100030700140700490526078565020929a801803000c40b40c5d035580e0340c02000140d0408074522040600c41c0e140c40300c00000c92290342c00151043c1026010103454030340360a0754040c81c04102030050021207500b0030356914071645030f20020754002d4040340c2c0c02c580c0c1c5a01c0c0301c5400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 772985476 1250 772984226 772984283
    0x21020a03061a0604060203030c072307061b020a032a030b06040501090207031d1903110906010908150c070f0809040f06053118150504120309 62
    0x40e01c5075180e00c0707401c8019811003903480c03074201103440514240c6010360095803400094281a0414000259070081050b0301c1c004054214019200c036a11810024005466940302d01c202c402042c03c80c101402d4040b031310a0546540e5500900340401c0c1421030f19110a0010000400300d41d800350b160101051003801e83c50200250304c00c000c412407500c0d044060009885c0c0c180d10101a00380188403c00009410522620b5109203107035402c004825610005200c42c10706842c400881a1007107004014810103008510754103a0036030344c44a20b034980030b00448450b8001d101781159600300c80c02c3c0c0d840c1d02807030f8010103420001380e440c8a801d1007619180c1030008020020210354840c3e000840c9001c6040c00d0203141c80320307220800200803541c9400042041c00c0c52070500c400e40c5002080a452641035004d008070311600450740200700400c80b40c91641181c50341140240c41c0e074240b080c1407003c0d007880c0e4040d25126a41c001c01c00c0f100f94a40003004c0d0003901c0d110104960038001a00e00c8200320341040070043c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 772986726 1250 772985476 772985483
    0x1508070f052a33010509010b0304020d061506030e060609180c030102180112110307050703050c011407201c1e022404020307050118090513032721020a03 67
    0x40d4080100d6441024414600381c1c81503c210079080104010390320101914116010500c0301562a6520300c0000c5800000c51170040c00d5515290442c1a40e42d0801100ea064407000d0320204070040145218035942d20013110880d81c0415002d000034910403001000700388506d44501198030360f07480003001a00b60307000420a4001c451a104a070815580c0c008924001e40c101c0840030840540213004060b45484001c02d42c5e07051000000d02c810405200d0070032180507680f100001c0244640039581120481015a403003000194081207103068080105c008491110000c00200450045c00440381c0c0c2400c02488680240031105416400003040190b0002c1101150f9000e440c00d404030a40c01c01c02481c102c01076080f8040200c00300001a140000c180040d01c2090920010158074a05001e6825402d6040b40403140e042a0903c90340056a243c204a854400d031112501441d5091210020015042c81d0700d42d06078085404001034211200c0b1300354004150303400000d80394000d80101d4030401956200b10b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 772987976 1250 772986726 772986763
    0x9020616021c050a060605010302190302030907170106030b07081003032102030a1d0a030507080d061701140a091a090102130605190c080d050a14011508070f052a 71
    0x540402841b88107400103040242011400e00050300200c1501c003000300813075414140c0c000003044004c0d40c10401c40b40100000b6003c494030301e6000d0740c0385018051302d00c400c550003001c10380815101805070b80e40f5481780040c1f51071800e001b4070716101121942039400c2f04801d03200b031070900c0040000b050300041d40301e04010a0082060f101e644403182420141509001d1607410004012002a500c0000c4400f6650005907183c1c03500400d000b2103005003078642c04810092680702070304840145c19000700c084902c2044001c0c3e032a40d00d800b998015200c1100d4020201c04007002c0580041c045080150340000c3d20500050501c001c0d8106010b4264103600004003041002c00c8103515529000105641480300e0b1400c1ca0710911980d41e40081e034043e001400b5007554036180003494009190b8840081e4044c169980a05e40d40d4500f034400005480b0a040c00008400400040203d07000f20503904c4048000ea640343c0c90b114214012038205440050307400320219490340000d01d401c1d003c00c40c010304892580c805 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 772989226 1250 772987976 772987993
    0x160912030f0f0203031308030c28080c0405060a030504050109140115080a24181112060114040903020309033306010818150c040807080109020616021c05 67
    0x3a140b00141c0d041d07030003158410420006662440c0405485059004c124103489851390b950a1005000da14034045042643d0410580300601001d0754035039000b400d84a10840352640140c030b42103889540500c6420440410041500610a0707010700d074424062800041c1051145d540c0024280f003a8010715500da46400e01008544a0220084010301d605c800400c02d0001940d1207007c3d070700307680c0003030300d210001180d40311100000c50b0040360807a00030301c00080300380007a8a001c08d0900c00801880e4041c1c0038440c80035214800004101c0d059a0942050002c1115a441000081c02507041d0403401c40c0400d1010100c0d0b9141002101e200e6004001500000354118010105500d2210340a20102d5040000c0c068266000b40342c03a90003507140c08441e9001c1240c1c40c0c10618016803000840f55804290082240441140010f8401d032039111007501c4070a83c0ea880350038281d80b1881c1000c0d40c01071042160310840b40d0148040012203201805d4a0740259030008400d10305195a4010390381e81d0490443d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 772990476 1250 772989226 772989257
    0xa060c23060a1d0d20030304031d100c15060b070c03050d020604031403040602072010030905251802121e04060c0504080102041e0509060916091203 65
    0x654007150340150602040003030002d0a443c1e49800b16808130043c4131901401c58044108083e4002403c00f00700102d0784ea07410989801000d15801c1401c422144052220102407841c03c6212825031941d140e482010038896500d0704102c0754440e944c2a040705070b48400002d83d1004900241c0441c034014440c10b485c141c40d60819a0808840c00e141c90704640100301044000380c2c014905d20311040400da80c031610382d074a034038107240248208000500710788086080113546180105890b0602503054680d04d201710b880038019400c0c0c0d40c40b81c00062064001e40307440060718094481c01c25030740300c49405510005d0303500e259012050403080c4204800940024070001d00304080da00c5071b80c0200029183c913009680a034103803c1800340181000f01030b59100ca44065406d4801e00a80740903124100085640e1591802c018800080c41964841021140b110000701c07403038140030040c42070710098064101c603070307443c1503039400000d1074003030a8240901846d01150039222001c4131801d16200341ca641c030344003a0061 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 772991726 1250 772990476 772990481
    0x7050616022103010821041703090a0e040213060803090105070807020406060c11061303110a05040c1106011401020307120c0b01140306240607030c020909060f0708060a060c23060a 79
    0x112201008107050540941b011000001c460468240350f01c000b128644214031581144901001141c1c00482c41902203803848004610f13900407403084581e0b400700d0710010301c401c091b14950f2043c44103640090009040c19401400200121482207142e546810400c1c0c0c00502200d4607a004800000d5600c8404001c020045084030400361040314481c0c1082d11601c030315070035098a80001042d24140c141e0151454503040c410781c2c081c0000410500c070007420051b0080028000c034808074004c0c442c500c0000703030701c42d41009411034451043e400346252a20302e40b107881d940c107a00c00c9068202b248414210011482d80c00c580c501038101070380c01d008c1e419180300800d031400c4005443c4442200160300c0018400c0b0003455a0040c0080644000e0703280d64003810103442601c1c580202a401c2614030781045104600451014841c405403210120181c503048403c0b10580e0040301c0564011404540911240b40100b4095803000d00c1000c1e2140c1400300ca050520406074000104401e0354002800d1041d480a40d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 772992976 1250 772991726 772991743
    0x417060f0106030e0a03030c030f050a0f15031e051501080d0e1009140303041d060a1d0703020f04210c08010c0e2b120e06070506160221030108 63
    0x1c3c501444806040f184182d01c4019020004003810b80d14084042c01e90300a420070b00d1341300b844c2d117000c20651420049100c05090302d540e010910030b161001a8040841c2904d03644240da0300016641d04811064181c0c8207a6401d080094a913807040825204254012100da2406000310b400074200c101d003002d40190510000c08646840790044160041240e980464100700f15030061041c026840e064001082c254421900284400503076540744440083c2d140b0100c3c0c0c060b620039100c41410a0b07503075801000b24402c101030001500d140b02d0101c0c0c1d1440c0b00c0c0c0c010b4502050309662552030a944c83c1040303480318803001403080003018101d80303280a202104082c40003c0150500030702c852a41d40030002e0004408510151140e0300d54003100d00440e100d0300c64100000c9a8a0014044203002c0c00c082021014940b032410004074100005a000e00717001d0152958194070000415540e1500c0010482403800160804110320901f51100490100215080350040740e582ca40355495042c09071450802d10760 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 772994226 1250 772992976 772992989
    0x61a0103021206010807180308120f0405070b07060b041a010801360605060f03041115030f0403020a02030d0906090f0303051b0102161a060108070e010e060417060f01 73
    0x14070101c000c40129800b800e0b4044000d1070300380841c1e60b4a03502074521150003901d8203400444030b0f5001c000c101840c0024505140c2c4e031138942c0c0322940c454003504103034041107400401070341120038104820050702000d0602c45104540218489008402190466141003800340c41d000030001001c0ea1941c000311614050140780680020391400c0e001c0c1181c40b6803100380b040c507070a5240292a081071007160720850140100600c1d2130740c0c4d080742e807512110b160403d0b0f400b50381050400000c41c4561400c13107040c10041103040b10203803c599903001034a817101ba0040098096004442c14a80103036001e00000130490641c0e00d030040c00c02d040c0b00b03009000100681180044240b4504240046030304a420b84490031943c01400c120702e01c8848405019002d41d040064046028550800400c00c4a1448144200c02c404910b95960745000044840103407d40760f8501150f00d4061421003948a10203906070024043d003c1c500c0c0c5079540c0d1000400e4000c803c40304c480d48d00414244402006010030b8940103010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 772995476 1250 772994226 772994231
    0x50d0b060a052101032d080406030203100803031006050c0307020406032001020604050a060203071701060905040e16050906030a0f0c0806010605190503100b070f050d181205010b030307061a0103 85
    0x41d5552400c0d80100f140b608070980c07103100400003040e603000f0b41111b102a4405552070301c0d00e0340d884026019400c1a210641502c5007508045000d0030000300340d9218042602803084224908101562a94402001c24a0340c1c00200726100144c0c0b20f6028001c011f5116240303c2c00c070219607030f140b42e41114180c910305045401c110700b40404110b0015001d540d0f10b410010060392034480310000c0c0d6500104106903003040c9148070000800300e4000503a0400c43e14240c40a003c031019164125460b405c0c080300680b00302c192041c5c2032005080103005181d010801070201c56210015880354290705074242c80c1220818040b0340180003110041c0030050040003181045401c03c03c0c04040b401c003c4020034060800c0210200000380d074440107122350310003808e5500039181c2d2180300d820003040021280d082601c082c4940701c4140c20141c410f8121814510780148241c245908142d851810381d0b0f281c50003940c0541d04d60300d585031503507030a00081034402e110788000628410151000c00302d4500f1420700d58180f62 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 772996726 1250 772995476 772995479
    0x80c0c0c0f04150b030a0609061809110d0606051503091e1204120c350a080301080d08010602060f040303090c0e010611010608010219050d0b060a052101 67
    0x15800208509809001c441e050740318076030140842c0007851648203002ca00242514000f030301641842c000c40c042c0002d01c03018040103489203540001e07680207114100742c00b03c2418032404584a1030b0700c0114a54419003000540000c48c074000f404844441401750744460b0313112401c10503407414100807000860b09a030340318114584109003580380c407032585060308900700d00c40100410441c1480000440520a042c3c99182c035110707105c0200362040203004440711a035115001c91040305c55450601001c142c54405030380500455002c1810540141302c500191141410481c0081c02c1071020f18040c180f5007005240e130014507200101468010781c00780c815500118140002088031804441d445605420b001c2440c60862030b18408810050317002029000c540ca001040941e440404601107841d280002e03c24191105100e90803440b0350070030b40703504081580650b441c10340560041c2140d440b140b80c000444511070000b00b001640304c541407030000344000500c05015140000002045030003601d4000081d07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 772997976 1250 772996726 772996747
    0xf06090905041a0406060801090b060f0d05060613020c1209030709090206070b042316321212071a090606090c0f040f03171c09060b03010905070501080c 67
    0xf42e040d9801d60500d19401d000081c18400103030403c00003400440000c100504440c18500703148002a2110ba100c1c1821010600d4a40340110039240040e801034041e010940300c0701d08100d0010f452104824a9540a004601000e1828802c0307624952001a0381a660b0145504160600581da001949118035100603a405601c940b001da540c8580d11610301350049d11142006052400b4011010840c00c04001c01c048280101241c142300c50000802841c40c1c2d26120b188843c04580a800750b001e6080070406135800c18261204400c2c6090b04c0035180c00601d141c8c215200d400d0990828280304800170004900c800c01c0100d4181880e62450106d4041c0c0c2801d14040307140e169140a4150703446800c80304003041c4030901400444504030040c0c42400c1c0d03a0396689440400e8900701e88001c1e0ba2110400410713400100001086840208014107458041070542c034420000349080d400c11b5605d1a5621300c200302d02e032070034811603070820f000d80018a40700389001e0004024140040074a0303030500040c800070040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 772999226 1250 772997976 772997993
    0x41503170c0c0d060f15080c030c0d0b1f090c0210050103031d010513031a0c0a05030f07090e090c030c150a1d0907080415020403020a0b1e03010f0609090504 69
    0xb007000f01c03500140c299184c03d00c0c00140c07800c202e6640301945860702c9001c40e444200080300403a1607840c19100059400300c20075854041c02104c50781c03c048031444903c00165040240d07030f03002002d10102000800c44444540b221740c0141c0000c1007031551400c00c00b078002e40400104c3d41d500f642c04028031a40d81155802801c203101d913210318006a0411591142580c010416030303031060303040354000b04c5640e0380c0c0c1018080b03204a81121122100c000700496102412081242c1c0c40c84204d480f80c42c91a00d541781224040180140440f0800c5100d003000320b5a00a0356a250f07001e4403040740104000c0d6404410182454502804644581c0c1da59414205001c1c155068484902d000c0c206041003809504103039803a0000051925400012101000100303900300300780f98001c500130055210020145006075040340702c0c0d0b02000c0d6000d0340446040000401c13032401070003440780681600c0a0f45030301450040e0290030a03004841149444282403000c6948013900c40300030000000240000d050507100c8460 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 773000476 1250 772999226 772999243
    0x1404021503181002070b01090506010c0222020d0e0c0f0102100f2003040c06050702030a2003060726190c1116060e0d12030515041503170c 61
    0x603580000c00069508203882c1c440064281c100010b4495485144034100000c2d485602c04944010350f9100218a29601e4030489108035410b03110807034621010703002c00074440500c40e00b1000c0e01e100204001d600d02001e0001d8101c0c070044010215003c042841040e06012154442d640210344954082c1c20340e81c0d0005810320403802e20800060740c954407550300f00c041d101554040c0000810070541065101540004600c12400b80c0e858030140f94030382c94100c0740791044803000380d81644014241c0b40132030741042c0b40001400307004030345d12105080c1801190600c5002c94103100400d00c01540c0300514943c424460b405d0800134008441c19140c94204200f42040d8400ea0444060340d90640510440c019581c503440b03080194219204a84c40448030040701d49a405508000345500c1d640c2d8155051000244a0650748850310341503403c04e80c2412401404000c14214510030303040032008103901d5500c107103c0328100401940340300500b0b5003014100d5840a05240d070b18a42c04201542450300b01158251 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 773001726 1250 773000476 773000509
    0x10021c05030907080a12081006022112040c081b0d11121e1b0f0f0a050d110909034909032d051c05011206140402 50
    0x140c4a4a80b0004540751500d1030f00401d0851165418003002d06c0600130301130901130318a6032510a25610085c040ca2003144c41c0c829640564000c0c0c41d40019000186140c122030040100c030582441e944920214041105139005c0e10900341ca01018811841d0502c03c145002540302e01d072120140d0140040344a0240c8903c1c0601604900910880181d55201034121010744607002c4502c1c0c200d0544c4151195221540001000d1150005c40440c02c0355088086401a200a00032445e0075500c00500111550200c0c0d51a4882040314011602d5644c84007070003201e80c001d54000d1b4069088105000d003485002c4e0030f020a0741c0c824826036201c401407081000c110800d034a011064404c410801800142c241c01d0748902d28410401001d020400507401482ca03280682e03590186203140003002840b201c600340d091803d4400481e0424901c81c0a0703c010a012040715451520000c110312809017141c07000e0300002460301e07282c400c1c0b100b8023240380200c5400603042350481c0198107256002400308001282c0d1213 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 773002976 1250 773001726 773001737
    0xb0105090f1f121406011205060a08030d0204080721080a1103030a0b012c0f0d0609030c0b0c03010b03010e071e2111040909150606030b10021c 63
    0x4080d07034591002d510202164001e8500070180c0b10304014041240c04480002458940401c0c1c07801000201e20321030184c001a1034014410b00b007034100f9405084003d0017146c0003507550f01c000400364400c0000700052a50300000580380d5080401c81410150036034000c0c454070105400c2078449011207240c001d58294810310850b0fa50400340d0050700c0360140c0300100c880d180004000c000110b01e00b904514140402642d440d80001d2800200c1552050040240c14000308200911016420202c0c03545408220040624404030096654001506c04032a006c40c00034444410100400182e601d40c250003103010524941598140a941599800148580400f040c0e00c500466451401800e0600481d82d00e00c581005248000401425080d901507012141c2d0048103032055038640c02d4414072002c056100036641c0303041c2c0307080c0000e070180c0841c47c4161820a80140460b501e50b5840c8140c1004214a40b004104846542c040080341000030301014255080400740c1c1100d400049014246540d01f400d10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 773004226 1250 773002976 773002999
    0x30c06050c2817071211031308010b27040303090812070f080a020c07050f01050c0f1609090f020409171b0c03010c051b120a0c060f0b010509 62
    0x52520300101450b1215580c408400c0000c2d29074020007605a0050064221603414040c25409908602c10818050080c580e480c00b2041d8040c403410003020300c62090401c807400c1240c11480d10040b41000c1e4007803407850790341310034101d0382c2c1c103201c3c8506908010b4003444108025807400c044411650082005081540d0351031408208a03508099640341105803030958503a15000d8000b40219450703115070400300e0b07419400103000001318021510f848106801902c3c5162500c000e0200703c1e880144140d040c040144200303018140b04210b09071140c3c407110003c20915089590f0000301018a811260103a070800080d0408500c181115001507030341a200000c0e1090030303050088802000251041d04207000098092191080b4203010031420080c0c0242d0f601900241e0825003280c9514418902040c42402010450b01c180302505400c00f020b5820340706002c1060030314140310342c8140c80700b034007051100010005018151041d00d18003d412041045030a40d02130000e40240500856a4441c6c1c059104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 773005476 1250 773004226 773004247
    0x605040314120a0e0109091118031e0619050f07050901090503010e10061203020706140405031509100b01081801140c071a01060e04020702190f0f050109030c0605 71
    0x22035041d81c14000c8690f03c402c1c820000a08002c103070520180028141680440d01401d00d00c1282038521101c03044519003001c2e2426110b100b0f5400755019407600075058003246000317170000d001c1c1d8900200320292030300b0f00d07000b8241321080085c0c00c080750711a4a410308200002c140d684a0580020150405a84401800004031200c2c04a41c00caa41c241d401c00c3e22540d110107000550a05a1004880030b00800740c40b620b5100070305901e4140500140e0042104000240c007600d8103204418609103607030f2030a0344460110b854003d00e10703610060070410204008001b2018860158501001c2c1c0041c4118400d000000740440009071030210310f0000c50782c4444084038254082024440d40d05e441012628008440001a420101c010f035600c42030603804e03c0e4442e0411803403d040c0c40c081e49911035064100020710009401034241240c1120b0a880d460884a000c049440020143c0c03e6611003140e0078030390400b0b060190b0350b01403418019090700900000300044c0c40581a100145003240d00c5040044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 773006726 1250 773005476 773005483
    0x90306091e060e010e12070204020913060b04090b0405070c03051c0e1b09070c0b0615030f220807120e0a08071a0403110d02010915120b0105040605040314 68
    0x24011408518981c0c40d910070441c65800c101e081c200071000070425050f55411080e11101ea4801c1c049048104000c0480140f40030b03406010302641c00b43c0f43c03019101d40105810308413800d40d04184481e1001003010480191103008054010390156000c1c4050704040740064124025103200500b071120101d0b0f4401c885201d2222080620307800e55082c0300c0300780c00302d00240d280d03031400a40341614420259402d005040c05681a07016010701d40e918645a0902d448040103050054081340d0b104698030917001d03100340c0c0f4002450061080094407501410540c0c20950301c50444110851603440c4c400310324022030907050542d0606900700d001000042854001265a03803400039032254045000352000c00c50440010703c03003042c2c800c80c51a1000d01e40a50841c40954000c4e44070003054500c100f0102c1c541030810992240c2d0661060428000c03168403544882000d610441c220000600da43d80a040249403d00504440e0038082c00c00c10b2502c0d081400082180c8101d02000d02102c206131402c000340d202c00c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 773007976 1250 773006726 773006753
    0x836060d0b0105160f11030604030207180213080d03050a0e0a150209120703030f1d010f0201060e0c0c060a0204260a0b1e06010809071a121302090703020a09030609 72
    0x1158800103284d09843d00032210400d441c03098601c07544190035803159003000140d071401140c0580040001074a81490b0300c40043c10241c5041445800340600711506205103210b00107440c000c0b001e0813908140000040490750020420710b40e2506003000d030182d0401c041840281c0c1900101190603144500d1300c400041d1145000454200c1085003400c035000c50081403460035a4400e94422008030f09003a0304650325800c01d0611a03111100d6030bc1201c680d800340030005051901400082901681d540c0d000da2103980c101d41d02041640001040f64503104103100c3da51740400c00e030000311300740780c00c2509580e405240107101455400a9040c138a90600c001c0020502c0e01c0d610050003e150301c1d1150503600421003d5507440d04108046002c00d040e503005e0842644100305a5000f891550703d0300c010b031130060a08c0208110320000403c00d841404c3c880344225071068500c10802001c0005c240b061000d4180010010000c0500c148034180c6003d0340310070f80800f100c0e0002800310740308181e41040c1040d110700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 773009226 1250 773007976 773007997
    0x180103051f05101b1101080c0306033409020d11040f0b0c030424110a03020d03110c0a08300a02030a0e03070302010e0f0307030203030c030a090836060d0b0105 70
    0x20740300b110200010091031451959080c2d03104038803a00c03543c003231401034001601c0e480d500d5040702c58030b69405100003c2055403461071002a12100105116090990101e5003210403555000580ca0420b00042d0040c0d071580742038940014601031402091050010581c0100040184002036401c2c14100400507100500b02000705119040107410f004d1103659031000000002c0b800c100b007096031165000c10002030301c94064010300011800c084046005080f1300030b90581d0301005028042202c01c0800000c24804e1044012a80c0c6d01841d0b804d15240d55000c101002681003801410f249402c1d0109031035030400b514190240e101d482d414401303009003242e162019103030303c0045916810315505411031007020100c2800d84240e40d560b90318030340e2030f0701ca20309000d00541e00400220b60003140520080d03a004451140008188000355a11030300365200120b440015045116510810850703403907120860300204040801700100d040202e8a01e00800b030031190402d03903562050245900070401c4400c0e1440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 773010476 1250 773009226 773009267
    0x14040b0702060405030609010c2019051c17011707150207091a09010503030f070b04020406050d050343110405131104090218071103180103051f0510 65
    0x7c00c2d1450038000c10480484400103091440d800c4100300d0182490443c841c0018013030050242108510b100d480c0c80500110380900c61440ba00c448041c2078180c0c0c0d0744904070b0780e8035808542c1074001070300201721060b08000d803200030304050307602051000610401124003500403007c0180540c0c0082c0d06090495000544450a02c00021000c004400440c06292800c0310641c80301c0e40c90700b06165490061055101161700c04110700e0307000c105000d84095210b4801813002c01e19640703c1c00403440303000c501102242c003039102003040100302640740240c02010340a030203040402403001e801c2d4050084a02da00e48110394508201406110382180b40e681c0b9001c01500511050501088811030340703807a040306980d044007402c20041545001c3c021041751a400400c0e8428034140a000d10240c024058441d00c24001040b10b5002080018400352900e40c8400583c08941d0f4240300014003501d40c020074140d01c802440550168050f95a100002030b03400559880c015110880301c2554a81103803103c1240703604 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 773011726 1250 773010476 773010481
    0xc08041209150503090d0806031b19060507020307060c03020c100e04091103010b030604080f1b1002030103020906030f1f0f060f0602010b06040b0a0f0309020409050f070614040b07020604050306 85
    0x2600703c00118060341d03038802110180005507604488410003079860075072641100c418064800d0210044407282500141640804801500c0400520180b94881d43c007140000c03500d1019881c1c14480040140082d0400709900b0701d0956000392200720721000184a0581c12481d804080d01c03410801e0400d4002401c1040400110309088200c054100c000511075801d241ca01d241c14100814403a000c0c640c03003c02a41800c038130103e10281c40e04281c04001e1240303c0c6207070110407080d04100201c40f414030300e1401030b540c0d4114018004d1122008020074007070350040016402c1002c0000b038140303a49241c50b001900c1c4044c0c034006d42014110300100e00000504003031010561400c60f190b205d01705c88085d00200003119102c4c00340000c9006500c81c00c0b030411800c0c4000d140d624040c80b5005030004c01464005040c6041d03900141c00ca8011805c165499801074100714004001004200050045402c01614801c0301d051140c005100324081c040c500040800c0340b100319202e88042d01d0141800505466491 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 773012976 1250 773011726 773011769
    0x4061107061812090b03010b0912070b030901050c04050f040911220e01151818050d0207090e0c0d02030c0607081201061404150e060c030d050a0c08041209 68
    0x1120740700c4103584410240007040c0e01907010341c04c08811034000c201d6190035a0b2a0103082d40c02c94100d4410301d070300290804801d03800d031141404454042c0444036440b0340c0303a00700907801c2d03821280010800100c004041200740419a2a00401d0f03445030012903010078801e05c540340041e10a216046050b40000b0302c2c000305c609074426503030111603940e1441008c11100c000c542d002401c4e210340100c14800303602d00d904d0911105844046603103d0150403940800c0092030000c006048030300c164410707542034000740e00140c122a41840580001c0c0140b810a01c014005030440c5622034201d040c10038422003050402c0c00031501d00f40080703200c1a00082156850ba1001d0510b503045910280c840d03901810b00318004100300f4003d04241111860580710641490300702502c0c0601c0710313090340011042c8460002d0b004c8003661514014000380c0c1d12507020315101d50380041040e00340c07080039240441507401e0104c030f01c1c2d50561061006c1d038815041501540c0c0c085a114083c0e50000060304030740742001002031074240c0c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 773014226 1250 773012976 773013011
    0x607030b030c04090206031603020f070c1401080f0a0e0f0a0507060206070521090c040c05130605030108030a051b070e0402010e0907081501030e060a050615030f0406110706 76
    0x3549026015689406400070402085940400c0003c0d4002e0301400800c1180442801208141c546424010300c1e0011002c12240590010002100c010501c52402e21442801201c500d007244d000b800c0405c0d00303042607080d2070400400180300c4030409a07a03103018050101308000501a00d50030006407280303542c4c10b043c43d07034440c20396000da00301502c03034400401c41c0c41d4410300c111085c0032036200100070204400c00741c0b00d031000700290000c1814802d030804403050385c0d1103100f2028015400c0e00c903140d4031020302e030403042e07460a59406003040c048240010450410702000311032140640d841c149075903034011458421002694049649035119888001c03410b20b40b0301920b10300442c000d881d00c86403107a803002085820b80d412201d101c0094200303400300d00d0109d1520404d14180d881410b0115044402008151800204a50409140d91180e0500090307050040c2c503204044940c2c80054038510707040d6104008140050001040c1c9035503480f1350900d5448890656080551200c0107000c0d511102030031001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 773015476 1250 773014226 773014241
    0x2030a0f0501060c050c130603120f1e05160618150f050915250914010903020108070c0303060f030803040b06031908070f0804080d0e1008010e0414060703 68
    0x100520308000807800c3c90050410400340c5900c01c0007402894281821b1110b840301000c480e02241d51500808000917603c50051b0900752700380d13610003000c01000107005122440201c5d4180c0b582624804400b04103501c94210795680d80d110140201c050840c0c548a40104013400c820441c4e40080404070f01080004206491140e0316028144080d600c48550402110b4003581c8243c22a40407204488480d040c07504525071191459540d048020000c4281c0742c00c03d03021503078102c00251820320602c0402c10b0030b80408003110082c079050b0380180c00c40d8000b900321314001e4110070910002d01344d5041014070030341040014004200816015666902e05400580c0080d6402c4585c00a130b0300010341c00f42800550501031221255034030f5004410781d00c9043e62984030550940c3c044180700c100002143c40507008000070035821006044400092000802a29180000303601c202c03020a8120065944040400d0544602604155281c0c4a0346415403225030460145a40340c01090108a0f0160f0035600022 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 773016726 1250 773015476 773015501
    0x1803030f0a111b040504061e0905061029070614070f172d041119060504090c033b01110703080705070b04050309101107140a050402030a 60
    0x1e0702104090000e8036100d06100c3c0d281c0014040140521516150f0041c9030424099800001d804060315003545c0c25200d500c50301c94039591541c00d0682085000c110303256109400001b03e074041030800c840d503812100601e52090300c0401500e166000400d424040b120085d41c8031404000004407108407040421003119402d0100b01c5a50358a994140201050144101c80507d1000503544980411410003192100e05181006400200348018900948a8007441c00340c3c00c1d40c20103940344010400f1400f02d00d0140b914214082c0420001c2c650410207031400d944441101107403880c090002100104a08003850031032803000341840d0080d07540b000c41002d244002d4041a1801980612210b09031440e412042403030316410014036012a10a1040603048501485c0080c40c0040c1a1a40d01003100e007500c0c2902c0542001403900c2d281d1816208800c0c41c003000d03003051500708081490240d15043c0345e2194003a0940d11121003012942c82c8a028009040020800c41d2a824520b88800041911003070382d6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 773017976 1250 773016726 773016737
    0x60f0f09030a0c02040f450f02010309020f1f020d0f14070804080d02070918031b06020408011406040b1203040b0708041a0d1a0f04021803030f0a 64
    0x3a4050004001c0310301c0d105054440a060701d400d58280001440310349500c105055440f80c15200b06a0715a0340e030310010a0800f6800035007044294035481e00c0040c0440101c0300700415010304000b441220920030364980901b40007401031030a001181400070b1094400d680305004002c0340c1880304501d0106071020a0b550300b11441c0c0b03401142c059607244625100300011903c2d0408210080c120f41c00140b951900c1440182c2c01d10741d5030a9164503200f120524800507800030f400500c0040c091b0b100b00070b00c00e200c64182545150080c3c8000c3c050050030f0845104441d00c010a04091000030b4046600070070b14480204020080840324116011b016a4102c1c869814010480c0c080c0c500996000803410710040510314240c944041245e80da030050380211a0b10500340030014440c10048a584403104485580e02d58541c1107030148030844052245095001c08200a5445680c82e60701c413107071040f00d00343c50044c1d48100d035071706401e491a2941c24980d41031000080314130380030140b900034001303404141e141c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 773019226 1250 773017976 773017981
    0xf0f0302120f030a0c2c15120f1f14041103090a1a0702060c1b0610060e0307060f0f020307060e070611070608071b2a0b040b0d0b0a08060f0f 62
    0x321801d03220681000701803040d228105402c101b16031805100c0d41c04c024458081da0001c4941808540c0010610b60000c2000c00100070541200022055024058403d00226550580550088420030f4003480c15042c900340d10a034225121988407003001180c0265103601c07880d103440c0d0595201c201660032540032100d0848035104054241a0307a008000703d070054026a920507444000542019140e040c0901c084403881c0d01c030540900040f400f4001400685c10080c0c20840c01420216078506054040c1d032001b4400c2002e56404980c800b2462203d00d42000c0111038010100e10b1401484c1025045500d051100301d0080f40009032102269003a0b110030350300000b640c480036220b6103140f1440e0045007500f00050b5102d486081e000b08072a074681d040982114141d103d44040140d00d0102d03401c10040c20903c2c00101070003522450082840e5107203980760600b4074000740b0150203144400040c450704c07200d07060196990300700400003400ca80c500301c035004d10348421188004c1c03105481003065580ca6001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 773020476 1250 773019226 773019251
    0x709080303040b01120515010602060708010b1801050d0908180306060105030709050d02060705010515150c07211a10051e13020408030a02010e0c010201090f0f0302120f030a 76
    0xa5074461030300300c0102c0e803260703180900034403c01c01074000032156400344500751000d140087d88200d010340300340c0d4024200ca19120342c010f0050074044c0c002540c0441d0034000101841424554050240c00070718156403110020b2007013201a0002c40d0008000540106640320302d21900e400b2105200000c400701c07100c03921407000544a910055800400143c0642424041400c203a0308c0341a449201900c460f1a103085611030032300f1144140d501c1803801450001030a0545881c00748065180ca04425003850070080070074031a90b07108a4441c00c0510340306641000341400c984c0c125840f845420a000c0f0103550802074102c0c0d0f04813000c5994962903030100d80c0103e05820003100b11008203030a206c1031801c0e20795000410112115640c09410496001c0002007074281c1c007840680040c3c543c1c1c0d000030800710a015801030500074281d0001c2c1c11685082c140d0070100349580c0c1913074407058002c500b6490480031030604901f0a004030415070408800061074581d04400a00198864071900004000c01c035400c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 773021582 1106 773020476 773020483
    0x121030c150c080a020a2007031407170102030c1c0f1803030e010c2a1a04021f080a0b04060807032f060a14160506070908 54
    0xc00e0402e58640102c402500f0518664055050102c031400041408031403034000403408684002104408106002400140d40c0140c0c0e0004008007484c01c041d03542105105800d01000070a6040e440e608040c800e980c0681403114000c0d00c0c00e80c40340150700c20551984004a40c1e1541c80381d04283c800e0b1300c3d200f09500d055000802c2d4800b0082800c02a007152840034001e891031341010f41c13455190340e02002101c00881c040306110400d800d51500c10013248443c05c00101101c0c40c440c011245c14181c4080540b040b4401c864a02800345030300d020f03407440301c50200f5130004120901c0110745d440520350411085420081c0001800703a50b62004a03140c41d44c543c0c001d840000390b00e502c2c60005003800345181c5401c103e403843d0284000381000480d1840c800c4003802e00401441c52103d8203880104004c40c0c40e032031001540d1281250050078074030344031201030b5140da0208240d1200040d0842020 = true := by decide +kernel

theorem cover : BRFrame.Cov 772841726 773021582 := by
  have h0 := BRFrame.cov_init 772841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 772841726 ≤ n) (h2 : n < 773021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
