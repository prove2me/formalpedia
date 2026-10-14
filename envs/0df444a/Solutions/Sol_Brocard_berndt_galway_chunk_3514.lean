-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3514
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:52:54.040951+00:00
-- url     : https://prove2.me/submissions/51178018-78a4-463f-804e-9f9de92bebe1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 631834532 ≤ n < 632014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 631835782 1250 631834532 631834537
    0x30b0903040503100e19050a051c090b0705100b12011107060b01030902010906050c0708030309070311030304030b07030b040b120d1209020306130606050607080901090b0a0c0f060b06270303 83
    0x74440018501010301b14546550803024441c20f1750180158108400411003e02044044421030091140d501111000080503620240d0113000401024454100000c501141d18080a642000c02064444920b00010401da505005107100c0d507180a8ac114085400d00010f00415409800d08000d004071201c015002d031210450000e00140040e0000d00139940610b014200c2031444c242115010368640841518640c4181e0b200b40c0d0741e5201050410402a40c510544030040e0240d01a5050038a150340308ca80742036010307102406040e02c48410310907030f84541d40062813400008019100b204100302d0701c82d1b02c4d940304000000001d41518510240c1c1800c5000d0103c0841d4060024250780d03946807002e008110381000104c0b880d90310f80c1800a015074801300070344102400351406658901c0e00000141840e90640d1048110510070300c034042d645900328140718031003a00810031080150b45441c00301d004040b000e22581d4002c80201d4080c01c1c0180969201d00805400045034a451012104056903070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 631837032 1250 631835782 631835801
    0x2703010507052104150e0c0a06050f0f0a02190609031206060e0f03010902040e2b1e03060b130f09020301080d050d1e050702060a05060a051009030b090304050310 71
    0x1c441076403e58103000c0e00324803035006020b45221105011210303034079170a5034409404a042548030380742c0d044203450f103050280c0041c41d4a040c16483d00040d805207004031700916544071401c070b83c04182c1d0141c0078000d004260148103030010342c0150342607500e094001000c21200a500144501c40401c08019440c030031541036503410307159001114503980400c201031a21405154041d52035404003001a10b4a0040100c0102c0d80405000b480001148146804c40c606444032101d078040d40d0f10700306240e04400001002404803080499010740c000054010700410b9000118200c0c1c0000d00003414074444209405484104030b509600554070341c104020f9000a004000d4141c10003118492103d0082c801814114102d03900801d4048100c1000300110803400e5000640315110010042942e81c103201050380071410350410030281c00c041010403070b601014054a4045c01c0000d0034140b0641c0100d0580c2d005551181c42c0c10300a140131038400307407240c00501c101802482140b042c803403511103e00461030340 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 631838282 1250 631837032 631837057
    0x81e0414010c0e0a1a040e0a140901020909070e180a020c01060504020906161b0b0904050609040b010302011119050f070503072403021b060f010f030f110105270301050705 75
    0x1002d0625080c09004080e030080715040704006c00000070701c10441f118841c07242c011184001000f40c0c0b821205d00040300014096013051344100b1000350103503609102e058100d000c03843c000c3c0c00c052007000880c10060f4543c030740c4842442c0d600200090050341d90003e1864855200007030011aa0380e00030311099000e0645901c0d4440414405078030719824111204071001d016084070300b011a102e1043c20210b40d02c540294081010000360040c00303040074043e05401240c00d0300c2821541c5415111245400c00601000f4100303c44610b5613500400104030701810166004c414000080300c0e4686143d0700e400a241c0200326024480002640c0c0c40c01145140480d40d6203001c01540c242c0300448045e58800300003444c401e140c1e00340443c904901444200c8221404110010b00860a20100d0945130450581c002003400140c000c0900004480f000c1018465500c210218080c40d644801a1482c0c003a50b8031a505249808480c58030840740c5a80a0540c0380c001d4000304100c2d16001811280b901c1501c410a48 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 631839532 1250 631838282 631838299
    0x80d180b06100507110906060f0d0501060e060f0a0f1806020309030105100b18030709060b0d0e0127110315040c15050a120b12010b0306130209010501081e0414010c0e 73
    0x400d0030240c9a440d8030142c0101030301c0c50807041c6140e40480c0c0c0c000c0001c0902b42c942c2c920040c400c1c1034104c4c1d04241052030032074503941002c0c40c1c5e103080f00e05841030440388000c1154845448000901640075070148032036400410444640701c0c000207549400c00505d251196007080c000c40e40203440d0b40c41150968005030b0710986000d12140d001010210385c401d1207274040c4140000003900b040144a24405000c041c1001030b0742d55003202892058488006602195074582081301c0424000015113008990054401c1480c01040d810000b800001c42561160140034a4448074544103040110901c982d00c501c2511260716101d4800480000d2003c07101c00100700b040000c07240c881e000c0d441d020b041d0f041c0c00b5400b0903c0f440220100340340b0f08280302207040b039a45508020099150038040c4a43c081a40303441103c074072440c2c0c0c00155a2000601c40c040c103105102c000309099481441c41061409018252112607041038a80341e00254509031381140e1035440d14251250081c03203840b0581c900b0100400c42075 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 631840782 1250 631839532 631839563
    0x13031509021906020a17070515010302240a0c02060403020d05060f01060c050309120f0a061505090c1207020f01020f0706240b090a090e240f04080d180b06100507 71
    0x1080406c1820350003806100f0320003040020420840c0c50022004c1004181041d4914414480000120700441d0810381150364040c02a00c80c5400f52000900d191412050842c818004a1050f100d103410294111040b0034501c018040b0009109014030076498020313035260b1343e5101c02c031480b9038403d0008002e604204030b8080b0500d09a040701d21185400010b40340b5403191030008a00e088600c090458070745803582850364040380e0390030703000300200815500c896030751a0581d2041e07000d2203400506040301c00c001c804140a10301c01c0000c1c11405810300c00855480b03503100d0200f0138a80040c502128203d007041c1d14144050602c8400b1410540030b8101034000c03508000c00c0302d1050304024101500302c803551f54005251700c5117008492080103508041d200d88003580000e4000c9100c01c1e001a01c19020f103405000308007220070340d656070007604140300a07110400043c0c00c0c1c024040c040c0c2c1404c003a80c03000c3ea4200c140151889604e0088a00f1920100030100c0c45070295100c0c003444c10047d000a4900340d000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 631842032 1250 631840782 631840793
    0x80d030902040b0405180f030903100c020f15010302090c0c0606040e010b1012050606042102010302040b0c030307020106080c21030922050603030f0a0513031509021906020a 76
    0x2048003038401007000c60b40e50405400304044070421640007500d80c112226100c0d0040d001c2c4002c02c070245d420406507240109410200b5642c005140402010319543c01c507001840784203000c0303060106003032000d44400610341302c041001c940c02800142d110300381550201310854810b5007110200040c0001a08443d980c0c101008000c0080d40307000f6486540704d09211000340c0e030390381000c01e850f0a41c1d00c0712a5807011030420b130011100018401406280100000c0c804103580c620310401c1c4030b084240e11030302010b091004a005e40a5940243c0016001040c140303102c01002c0080d42c07007070740f603503008100550b40c1d440c10326907885402008170713004011491070079418400140720840700f19440c0c003140e16044001c1c001c51504c40f0040400c003000381c41c00101c15422202805015084801240114148910307485658010300c00d0144086c1800320016554000441c0c06031188000c5030407203d01c02d1b42d210b480c03e0604c003400e00000c0c101d1080c03900d0b00c4400850b40303164000341e041e80c0b400c1d80205440c07410360341c41 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 631843282 1250 631842032 631842041
    0x20312010b0711060a0f020609060108060412090e0411030f0d080a020d0902030a0302150c031905071209060c0905180a020f070b16140703080f1503030d09110901080d03 74
    0x1a00d0700943d6400205154440c840281244075007991403101d81c10803101c000b07051860140804025401200042108110009070b040d089034101c080c50108240400c0e080c5c504100560004401641807801c00051048040c03901c0e010a0303003541550740d44011b076500103488070040c80004011034443c034080f603d10945980580800d8500d000002400b40950300064907003040346004a005a00c401e0510260900301040c00340c0040e0322690b61811810f1003c0600700308085042e20742a00381d83d03600003460030f0348501d8800d502807400410801c240111814114003a0844200d0340000c030700400710014180c00e006200c4034070505802c5090b00c00742c0b251081003010390300c0030a55070001203080c413080c404100d820034810700520710407001c0348a00784004400f8159200100300507861072400d204480c0401c0d0402009035100c6914068022595074843d41c040c1c1c00c4ca2801c403060340621020544a505007225403080c40d02c03c1c0501b81c260400e032145c604100192400b401110345503041001c010100c140280c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 631844532 1250 631843282 631843297
    0x6090106051602150c0d020f0a030305060f090f0426090906030a140a1e0f0321020f090a0510090308030402041b02030d1a1e06040902030c03010f06020312010b 70
    0x8548440c0e81d500d8000900d13810b01c1e07141c01c85504000181e50170b1540010031400c102c490485c005024a100301c02d4020340c562400200190902d92150f00144480d9108007031240c1c0d0003001403d1601e03e04204400c0c014006080b90b084032035960b00100d030b03140300000c80c0d150048404e202c81030503d04045101032049500001d0102038040c4030780f054543c0002d0b601031100c050340307802a000302004100c50034202e4100040c6030300e008003194803251140104a41910101403160141440d103a059810700042c00000c1c60385890700003081c800308070082e884902034010144143e00f110055002034494042102c2e4000d806d0341800840c01a400c10000030f21079001139036110b400200700184111580c00c10b140c401c03030301030310041c016040000c1035101004688680e44036a2011910714049102c0c40380483c5404c10f02d004a411500b0714082d4000701580c03681c0c02ca0700504030301c33001035441c2d0070039030490300ca940c10a0046600103500c615001c517203944000300303551010340c0f59014071205034a000c540a142d40d21512 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 631845782 1250 631844532 631844557
    0x1207030f06020f070305180607173a0e0708030a110109051b01030f051506070524010303020d0206041e03050d051009060506160809120f0c0103140609010605 69
    0x21181400c0f080010240400500903143d84e9650b11045a001440c40c5080400074030403c024004000410000308001c8003811400c2d141590b0340c85803900f0b8086580390354541d1000040f190079840c00c0808110000240c580d078582c1d0a0103447c0c030581c50f07903860750603034013038461541c0c03051211210480c82500d2001500c0070f16000060076007000d8a40f24141040103107659490380780f1400660352075070301d807080312921038824038100104d003010b0440a0044a0482a56204010115400c02400014422942d403c0410041c40c4a00303501c4a500d101c000783c092200307802500588507407038081800400e440c0c4c425540203c507524014810b640d105001c0e03c040c07e094081201c280801e18800c0a80d00c1034500404a0301c8800b48464580790031301d010b440254001500808003404042c070284030540740e00e1101e0b9480007516480780d6444011036145038007440092003510441c40a0322340800c005c1400c418050081c1d03800d1140c0b800008945000d00d50a40c0c13520f0302316150500400296120794044c0c1244d00144 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 631847032 1250 631845782 631845787
    0x90703090314070b010e070206070207030b060114160c0e041e080f030f011a07030819151410030203010302010e130e0f03090a080105040305070f020d0804120c051207030f0602 77
    0x44480d40c14070341240008079904010000184003406c0c0030354185a110710540f0081603e41390641c002501e032555440028818032207803003c141d041e07010340c880002000380c1a8585465150060250041c1400c8050640d20000b180501003040451040303080e200341d8202c00c40c055040025400070012403810441520144014014601074880400085000c1c0101740b2080e90700c4e50410310364852b440c034100c82d1060102000c020030703c0020303040b410803640200c03401c500281540c01900f094000c0e000c0b82c00c680b101040b01010102e0364554401204684200c29140d000c54814603107030580482c4401e000180c0403c4a080c088101c0c2c1c5004c1c1d4100c1d451143d207440c0070500510701d608645ca042c0442411b802c00782c001140c94200c9051500005000b406224000d00c0703507040a84001d0014802e140c1d024064207081a115004c0d501c030700e03c03100000369012602c40e41c1c0b00e50f259901903000000040459400c00c61203400209413814040c031480307103034030403016100d41442c2d0380d204080c68000e00c1003141d0a1b40c00703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 631848282 1250 631847032 631847057
    0x40203010f0f150e01150518040207050601060909090b01050f0111010501080a0201081617090102040f061d041406060a030e0105070c050d080f010b0f19030609060504020304020907030903 82
    0x940540900b03011007501c04606004081c2d2400c020320003980014000314480c10040000c0b40040e08811110440d505003580e503072a0301c1c251000a900503000c0c043d00a400050154100200002c04504850050ba03586141686842d00d2800303540e9280700240484000c400144031514050581c10b10000050606540d401003e01d04103080d510241c2c044109a04074120341c07400e40d60400e01c2250310150681c030880b50303240e14090180c582d55000c901d600801c031012002078986803096041b100940000c006c0401007503030340c84000b00b25840c0c503002c1c0e02c425420000711035841c1c2800c0c042c8480c03000d0503082d0006079a8810007484655000701c07211900701a240d20848100c201c00381304282c0a1252661912404000c904105140c645002c44d0352041080d40000c000080000900d1541564069050039985014803002001c40b806004010840c1d40040d00c042c2442c690182e004008840c15040300380080d0343e850041100328001241c010790400010740014820500c80c2c2c2c0300103400ca00c070f4102a07085111 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 631849532 1250 631848282 631848311
    0xf180c020a1a070e0d150905030f0d021c290105040308040b0c1501060f080c040e070c02240702040e010e03030a0e0c090106050d0c051c06170705150304020301 70
    0x2449040c8544480b4040520454036480341c0c0c082c0c1985800d0712500b501c002c503603079510703401041c2145414443c1d5495450004100d0184110b46018010600140c0c07030b02600383d0000001c0d0b010706100d007115182071800610319181c500800f224884510300020f01d9900d54500444881e090b041c241e81009410000400029089406030005d010120522502c1e0045528054a400f04d820300071307007541c0105401005076135131024561903210700528100348951030b015002952409250000001350b40c1c0398080054480c0c0c407241e0032155a0081750000c4400e886050040e501055608551000000800801001d82001e41001d882d002c1404000a0180c2d680b910560450700141c0d2088060354954402c080703100c82c1008005060130b4210341140840d40340803c0a49144100884076149640342c2c0841c1003200e000301c054800004462801130785007101c006544004000780d015020913640c1c40032215814443c00104081a2403003e0588212140e0103134800c601c5800060089a15640b80e9000e402d1805 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 631850782 1250 631849532 631849553
    0x80c0d2001090510090e0708060d0f02042901090b0a02070509090a060c08040c090605091504060306150314030c0d120b0301110403021008060603061c0515100f180c020a 74
    0x4180d13a0711781c4180c504255140e400160050126070030032800109005d9240d40b4500445907040e442a507480c002c800d5440410090000841ca90400440901505061810001c800614000240d0703400400702d032070307030030b4070215000d2800d03410010303480b0402c18482400c04c810400d400c011050700312158440655614070035180003108407400a500c400c180301c10041c800e1002009000000003c0c0440c42c280000b1400160f0010181c0c102000302c400d402c140741d2103d03071150300a150001c1c000d2224144500070b80c1980790b12480216075002008201c94007020010003650004030000010f800ea80207000c8013212003080d58403240d5604d65807440702141641c0d0920549514008880d203903030311145540108070302010000b19110502007680200600d0b40c0da40012203901040c00c070303202103201e2080c1d01040d0030b104c40b00000600c54403847c40385800702c030700c1c0380d40803881240c8005000b0429516590001c84000039481010154207142000d0560f203440c40c0c10411303040c2c132984100e400400d4540c94043c00d10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 631852032 1250 631850782 631850809
    0x40501030c020c060a0f090b040e0601030c03020c070e090c181303110d0201061508090c1203430f17091009030501051f051020010204080c0d20010905 66
    0x618200d0b00d1006c26500050100d000703100700e05000d41000c0c50305032004652403000380b040c2d041503643c00503203040500070ba041e42d01d54512602102d07001d0741c444100c00c52418050301c9190003071189081483c2240f51542001d413801c02c80742d003030013030720b80351003841c2020340072003003400c8061014400e0b101c001000c1c10402c40c06130a02039800811002e24203190306103c12080019030301045105003c1000d0594005217481030854250f88503500030f000605510305600412090105040c0c80401e80e41100f0b00320502d4540202210f600d00e52030b0450384001152907556180010446000e401c5200c004c0f0311540c074040300c07018030502c52526202c1c540c030014079150203290610b40811400340b414024050248038840c1d001c1e1403210b004072410300c994007510a004040c40368520982d032580300194100d02c02c0c441d207101290644034128414850350700e0107010b90014050001980700700382c2d00d4009481d1410407540c2c0d941e003041c64680701a080e42010031310301c1900c40c0032506010190100080e96107689041e001038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 631853282 1250 631852032 631852037
    0xd051b0d051005010f050a0e010e100c1a0915061813050601060503010b18030705062a0d0503040303050a1508010903020f0c0f0105030703090804091d060903040501030c020c060a 78
    0xa501e00b003521203620205a4204030b04008880c09080c6056801c10202c82d122519800c0c0748a414120400403503806091841041d040341551f4161070300c00703800050b041d001d40e214800b624010030749a5100c060f010f03401c0b100080c041d0b025a5210f500f032089803042d83c1e0008005800980d00103039119003050202000d40720030b01c00050014040c41402414403820b405441c682c605a03165500d82001c3c814030703005902c144168082a20041d00c0320707507820048807000f000003511584e280d92003015028000d240079040071011070301540842c00c01000c003060a280c2004241c41c3c071420740e101c07500c2c01c40080c507008103000c180031381c0e8800e4841c403409400d01e0000148030079000807860b100345180c001e0038072181c1d111082d001d070b02041a0840c00c2d500c0d058490300682c0207203800c9d9142c0d41ca661040740604104000176010b0400058007140145140d04a0960462010f00e6298941c042184042e40e8401c00c03185809130b03400c280414405580300750803004c1e041c2041e2045035468070b690000259141c2c003603100e5502 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 631854532 1250 631853282 631853291
    0x601030804210302210d060e0615030705160f050105010902090307080a0209010b2104030e040506060a12051b0309060412050715050a060314060906010f0b0d051b0d 72
    0x192201d0304521400303101c582d0348903030701400b02da90065510641521091000c0c1c5024004011401e001d00c103540301c02d500160248480c50392800280380e018030a071800780c094003680288100d9a00804112401032482e41c1c0ca5a1600d05190408800a03038004022211038483c01c0346040440c1090051601800a418005956003803034410580342c0015584100440d40004c503000c00541e9507011030a04450302d091503169100c010b03070700e0724441c8403140b022803448000c80000d1005240c7e02001c00b43e58010181c80070030250721000d0402100d0300800314a000000c0d17488081000ca082581c104030b40000e88404082100c00800b258000c054201302c810301101d5001c90104018071500c0c01049110303220600f0014030303000300c64868000594182048078001b039107407004200500f1640e03114100071900025440025280380c0920390329918181c40109091040c40d001094500c0e80c0880b0004586010310701500e421803c0c0c0a007005000b000f410303005a070070340001048104190710000e14604805600004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 631855782 1250 631854532 631854539
    0x1704031b0807200f0a1d0c130308090102010518340303110715050d050702071a0a020c0901080a0201031e0504080304030f18050405190c020102040608090109170d09050601030804 78
    0x4c1c50560380f55180d100d400f0700502006255590080e4124540780f10218103100c1c0d40300000024144a524404801c3c082421000014840c0c0348002e0004c00000368020b22294541d407190342003910140b002003066030400c840c5008104090a0b2203400440c40348135410505610601000031228285d209034042131015000c0300f0408414448040078004c0c145802c148621502c800800da4094051000301c041d641c2d0020401e92802045041d00500740c0c03099036081d000c005134881015401c145440800340c8a84c52512606140134111a03044e141c9001c001c00902900390011070150210704486121034201905441340303401c060080500c0b9900903e10259030342070920f4020903603400440c07403a0800c00d08200b241e02c0c0009141c5401f00b12282200e001c40d854981d03458480d1202d12030030f0f8048540c0c3c942403000450301d4064018104403169512052500d5980e18296420b0b9481c41c00004c0601485000002c0d0f5a07084202501c0d100401c0000050000f645036585450320304203030810b846243c0c02017807c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 631857032 1250 631855782 631855789
    0x30b13031707021e030c121803010c32030907170a02011d03010f050a150515070318030c0909020f0414180a020618011704031b080720 59
    0x155050031a4030803207821071a007000020748542d0625108000382c0c002074200700305400d04006580d9120184000e84213500c03075a610070750880c2c0c40704080600a10100740300081501e0184a0700612140607215014143e0b40413204103240e00d045400c245038215004003540703240c14400082c51207801054001e060796414050004901c50180c0b00003030560740885001801070340d000205080502c286081d104980500e480083d01500701ba0700c03070345e640600e420304009040c84150007101544524007080b8071025201c0d424486c0c13001511b00710043c0080104042000030703214007850f85002c8030704105480c03425200d0366142c0e0340005583c002500b01c0d490700000303003e501e4194040130b860070b0b04650403c842c50301080b015406c0030b00186000c80c0040940998450740c8418400c8000c0c850340180a10354076440110030020040343d024130507001804c1d8940c54070095803155604c90003280c242c0c890864844c00b2118036a0b003941308a4089440f50b90503c00e03c0e0009820307070302c4940300340e2000425444180d603900a2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 631858282 1250 631857032 631857047
    0x50108090318011b0c0e09010e160308090a03050a0c05120a111e031006260c220f05010f09090201050415021617010e01060f030204091a010e15181f030b1303 69
    0x8400240c00500000c586000103d41c200b042f60f90050b40705464200080c000399055070309070303c054083e008285c808010020344180200986400303c868440503410700c808682daa4400b602d00615651140c0c3c0a50044d1901041941d021804031181d041843c05980c040307414886146580120582c41d50713010321241d0002a8030001c1916122100022401c040d8002c80e62800803000380d80c01785a103095840c0c862000d100b0038a0229010080030f00511607007240b0309001b810709118500d01d03400c182102184a0500d800b8041c10180c05039600c0d070400742400600c034002008003901c40c1c15031240d10703001104804400010310040c046859085101052210303240d0039a2800c0c04c4481d500e901d41002481800c0b140e0701000d06603034050b900090803034100d150560408d60a10b40d0900415181000080c0c0a00c14000c49440741260044480186207900e05200d694800800801c00707158106001890114104045039842c0c0078403038105c079840f80d6075261143c03078100548000f590034850003204028560428032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 631859532 1250 631858282 631858301
    0x71701050115090e07140307050903010615050708030702070801050703091b03020307091a04020c010903230403110103020d091112030c06010e0402180108010204050108090318011b0c0e0901 83
    0x1801c0901031840b441c0180703041802e0083e007810a4458011030145072181e80f4403420b0a5454a155a582c104400007903c290010003035580300b5030a000b0702140d40c102c0b2462441006805454582c100340190303560760040c0c4c1000704060218450b402c40000d00c07507424010103015909503140090218040c3c201b042801c0385801000c031114a01740810001624002103800444142e024001010045c0c1e040c80c01c0e0300e81d0713540545503000340042102c89240c4030661084034000d203e5280c802441c2d001c6070f042c10103107190000b1501440000e000420100c1c1c2048441c0c5142c10051500620788000c00c5030820484981007000e5900c160200e4011100c3d003410074051081c40900c4006600348049540c00c2d55551005009090002c20307410045030440d11142700c0b41044030290701c50180302c3e41c0c450550900039001445038034005564000814008500402118031120080c605541183c0728400152000080e114454000d2044018400c010840340320031840600f00d0144440b1090400e85200c03803e41c0d05412 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 631860782 1250 631859532 631859549
    0xc0a23060403020c040c03062705070804170304080d091a060303072d0c06030e0d03020f0702010e1c08040810020909012c090c180603030412050f0717010501 69
    0x1010300010030f0b0001004071000000310380c0441e4601e0700300802c0303001d81400e902c00031000e0b50b20761140c06180c2141140c0c40300b020303d00104000641e0b400034111403c100036038001d00200302900500302019402c0d801181d016004c0c14406160891340400340040b288088000c0d5900250303000c0311140200d00081085c1c001310110b000390700b00401904c4084030308032454400c0c81845c02d10485c1c0cac3c411000c060201803049820030f0821000985c0c40b10054060b00e240b8000304440c2c001c410340202030602074405d8986580344a4151810404564015607940740f501b1109a030214051201d01710400e510602e103003c003440348501c01d07103031450400d00b24a044c0710400320410744c60052020100d140c86501810b4112030020240b07840900803540242c2803000c3c0d00f0740c0844014560400c210b000c4900040d13402000500f034409076500310b0540e03d800d403403900c291416903040d04200302c20480c00c0e0580c407440c0c0c042402001600c0d4101c2003010080e03e00207140e8420a4808040070360a400c880c0c081c82498014074071207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 631862032 1250 631860782 631860793
    0xc100f110102040b180315090d09051009060e12030406020d20030306010f1407060b100306030b01050d0503040f06080f09011a010507050a0b04530c0a23 67
    0x115400c4e140c1c09100300050400350850003e00d15580c0c20007150401c7e8a02c0e1100d60342c24204a01e0541e1507440c9001680d000c01c4c2042c800141d1400c02c0f080f00040c2c03039290341d0307800155401d0440c00c503103541c4045903107640115000c00a012020061000308000d240d0350700103000803400c101028040c40d400d5070050740790042c0c0d010544020316002c0112075100000346040d1800014078001a2207410008034044141c0d500400c5d000308105240e031000400880c101c070030281c4014442011020785060b400001c000f0500d2100402c43c0d401c00c3c13007040955038460003d503420070340c9400f0807800c881c0301e941c0407400092049080c0005024528885500302440800074002d0103142d400005040341d046407024100a400220103041c0001409030100859020000e003100d401c250070f02c01c0f006901c80846050000010102d401c4107801ca22201c000c0c0c181c035417050112410a094107118003072070b5a001c0d00003000301700704890080303606000030043e0038800c10b98080d21a811113030100601e0300d20000741071260f120 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 631863282 1250 631862032 631862039
    0x608092835090307030807020a0b040807060806040c020a03030c09120c0f0614070b04030908010c030f0c0c03080103141204170705060f090906031009060f0509120f0304050c100f11010204 82
    0x1c1350b030200b40e941100741503940c0e40a62000c0b4401100a91100040e4900801c01050540012408800701c0700e0554a0101545503042000115225400c05202590000c9150000640240c0099192101d5403c180b104255610003116420300d80f603001b00c503046400d4409210051070034a90b007015048502d01080e5400405803040301ea44100003002c0d0100c00104005020188241f01d490b0103060300340024460404c0e1090040d02410751640d40440b450300780510045001d02c03405184641a070182da44030003603446c40d00c80100e03114461884160324000c10008a14106810008100810b6028908040b081400a0075814200d00d0341085101e81c00c10854002040110300036554030b40c0044891840d140c50300720002c0d1a088500c55001001b40c104620350f400d00503668088014a0300c41070060200342e5a20407000e45500715442c0801140c1d02c00d000714030410341d240d0041c0d40d1061062040b92890b44520340010b8040300c030340320403500103107091441a01e120780c8100d2402a06001d80020742c1002d08 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 631864532 1250 631863282 631863289
    0xd0b041b05010801090203100f150306060e030d1b020607140c030607050a03020307020106181a060403050a1205130f091b02190201030b0d0615060809283509 69
    0x181881165505c603004804a00d841482500140040401840c000a02c0381c1e20302031483e0f0040440002c9000c24600840010b019020347c04c0c0d182081d40040181400060b8071805490400781c00740300d100d03440c0d980800f400040e21303504000c150003030055480c40350105003a00c03c01e00c0d002100074018000e80008050011072a0010203a8443c500305080c0540c40c1d507102c2408074014400365105041c94000320b850814604960342c016403610300c140b519585041c420300c0074014588640e1000a02c241d0080246401050b102980401c1c4540e144c030b02140b03082000d005082c0544d240386c0003000800030808080103044524455088855281d9050305100c5498440103034941031030a00919480342d100e91071204681c800d6003e50300005e00140b0540c9070048600340007000b04218020690000038559000c10103500402d00188992000381c0104401c55a6041c0c00800396001c0764441050101c08100c2c9000402e25940c1c0e42d2a00000e11a24000500241980c4001821402c1c000003403107080043c41c40684 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 631865782 1250 631864532 631864547
    0x618060c03191812050307051006230306040204112101091d0a0206160602181009081906020f0a02011e0606050304080304030e06030c09030610270b0d0b041b0501 71
    0x55000c11300d18800191401e109056214101008010b802201315419001c2e90303940c006070581e4002d8040c1000c07801e5104035510403516020030a0b0b03050703001200140c0145002d4109014140103580c00500340010b0440c0a041a1600c1c036a030034401d070601005000079003081c03159080c0c0d403843c04040944061170b01040f44e1a0200d80030b001c1d008000000ba42091805030708001180c15900003021580c071040c100380b02c0500100010194810040301c00c2d0601d082e03101d581f656080d5100c1e040a0245100c034900181c0e480401c6d0030045510715021700660801412800180c03042c07220760780000c1f4040c1e9145200c0c84040302a4004120306901d80300c010f02c6443d52105c01d41b64020360080c000d035a2901d45050544d01420442c0900e51b001d8000010041c2c95408180900840c11003541290303126190b085030011030703070b4407070144626103d01c20952650344030904002901c0908072105c006081041c020200d480d0342c5110078203940500301d0780705020070461503090440b00203014a0808090a08243c002095070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 631867032 1250 631865782 631865789
    0xf0408091e0d03090321050d02211323070b090d0605100611010c1209020a050307090b15090120010b0a0609031a0105010e0618060c031918 61
    0x140c00c98a008800c89584810704410300304010410909240b040c90020b20b008401e02088030441034010481c00c3d0000f0300011542c4c00485912240d091a40d603511040c020340103442008040b0700d1100d00c480c1340c520245022800b580d0350454002d0702c03107050308084561520410306090aa4605104c054001c0b401140c5841910f203600c84142d030b0b50f02600005404200103e101510701d80c50001406402140d220340b84e4100e44c007546615980b010301440040c200e034402034140d40428460070341000e1010b01944910300140c802030401e0710b921b48441c00304e0700d41039068100320425945e0301c60341c0000b4603041136115483c4c80308540440c905140b0300c0008081280c6407501100280c10300b1202c0d211690290880361300703031030301406469580c0c2c3d6490000303000e400303548400e0310340c0c1c198007001c0040a000704038694145c40c1c0684880040c003140005000310383d400a60b100c1c61000118070085182d6442d1001496810840c400440e161000802112081080180f02d2030501514205220444080084001c01c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 631868282 1250 631867032 631867039
    0x90e090a0c050618030709200a021c03141503120c0316140604050a0606080d0e06180a031101080609040b13080c01140108010b0a0503070312020f03160204050f040809 73
    0x168000b00c2107041e044c00611a240d03a2500800e000030901010b2548002125098074038140c4060342c1440c500c4059116003040180181c004000c00c0300382d4a8040f410b8510394a641c80c0024050060a2003030b884140e054800c481c40380202095604103180821012a070228840360b0186006500315800d9030b80d2052083c148070000d02c0d100c0c00c40900202c008021190000714040d20f02600d810715100e51600c80202c0e088641c00c0c603040b404140004000382403001240e5907250710a4860585041001a401102c0000c403980304203042d040c00794030740036403200003548580403820000400c0030000d4050b4400500041c005e28500c070401010451301c4840503041800500b01802c0c00e0300c213041222080c400c500b2900201c1d0300704491883c44060f45020740b4129200c0d50001c0054510070000c010303120145204642d070682c02000c0510125010181100f031901c400e00444011040c0000c09504680042200d80f0a0b450440d0700354095003040d006440e4806424803000400d450181c2d00c4442c4c86c056126020301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 631869532 1250 631868282 631868287
    0x4061b08040305070609060305010f0b030f060604080f0609010e010c0f0c061112060f04020414090a061d04050c150406050a0c1e0501140c03130302030904050106090e090a0c0506 78
    0x40c405000c04950103150440280c5540035128a0041c06116003480b030040020700c1c140002509240f9840c07104c05035041101018510384600415001d003607005085564480d8080000161280040106051880403040500a2071030031043c40c0d400c5810104481c802641420f440700c10351a0b000f031000000341d1890030131803428015810310000900c20182030005242c40040e0241c030352245481140d104d0300040b1500c0303403070031401003d01040c1c4c000da10074050b031843d05203032090a915188150036440700b4000000101c1d40d907240b803401c0900d0082c0112a24100280d4244000d104060100c07803401c20080d100322304e034540030340d0105209100e1485210308028011980e4603d403845103041c0307040d09812400300030100f0456214001c0c1c04d00c54207022552980780c2083c60154134440000240b040380d10041c0c43c0e007140d480001749019941c000100f2070441c0010840050990b130b5a1017840d004c0d04a664510b090700d4246105088000350290840076180d1113600c0d00000285c80804c0002992010354004d078 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 631870782 1250 631869532 631869587
    0xc1103210a0b031f0e03030709031203060b0904020c0f070b0a260f180d030e011a0a03060b01020a0609030507020a06050c0d11010f1b03140108070303080415051e0a020406 75
    0x24001c05c0d4054207130666010020038041300c1980b02c1019001d59028029240c890101401e00340d040302d46034443c0e1400c9140a0280390101d14059000d0140254a60180c3d1040d05140d1083ca0a1203d035801107222460003044220159500440f54900d16450003c0103144c0118490804100b03440182480042c40b120000240b040511410400c0c210a0715000c403034046d49000009005004074510f1080c41c2c1d0329042d0a40d241d00110601d00d404914098032402c001030941d01d0700e0000c0d201030480c2d14194484d0407291000600240f0900011310b00a0799441c1e00e804161041000d1884564041e2082280074480c1c02080d21002c6042801402c560401c6400645209034407800740c0900b52800544614004d80c0f64884c10349000030062885490345c04004e0088016242c0354005428020080d566011074410b10000b40110355107508140901c07001d05280d01001005820344000b2036402c0e41c08010201480c2401418091054005440d00400d40c2001d0500314000c0005103480105000c2c01107031603024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 631872032 1250 631870782 631870843
    0x711100c1209030f120f03060f030f020102210d1505010e21070f1404020a1b08040509130201120b011205060d05030316090b0a080105040c1103210a0b03 67
    0x10300455103c4c80b00184e1400604014040b903044105d92004180e6000781c00841078803d10642042c1c03042d49046a903441d0964490001500001d00200c0c154800c6401a56104920010384040c41e410800310ba80c6c0e40c801240d01e8400d0310b401300010010301200c6441823007141c2e0415440045802c0c1991401c803461014804500725140c003000d00311060095200216091081c0044801910700c01460404882c03420014813080707119402603800042c100700700b8844907030b901c004020a10b50190b107105007481e407a10001405448203981417a40c5408000c5800b04558000a0502000716408420810413200c440064061441154440c10b019078400014000780c1d94203602d1044650000112034882c68070f8000103095001c02c0c07880b940811481c240010b41006000300f100d004100d40c1e40c55034056482d01003840058980e642d203140c1840403142c5c40066a003001c0001d08103c90040910807411494401d07002c00d5040050940710b82e1504000a00c980c40e20002100240b411054404010350a80c0f461030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 631873282 1250 631872032 631872047
    0x130e100501270b07051506011403101a0a0e0102010527071203030501170303010501120209060913061802070206120c1308061e150420040b0711100c12 66
    0x903107040c081ea02d001003070080f05075001e4041d60344160b0840b591088140719080751100f0031a8124000340b0f0300341c2c00e5140c0e15203036009503800001003070f8144001c60f110302800e518251100b90017207204e50040340a180c115441040341107410307030a000030015801c3c02200c1c81c5944160b2402d0381e002c04124106141425020080351000b02045010f1100841c8540741c002c01030319084c400d15920204105202a01000c0482164101e4005841d00b19007203c0340c0e03116002941050b0750107540319030180001440b80e1950300c0c14000485440d82c000900b5401c1040c0a1081030508695074850380c4144841c8005031208400c070340355a0348019a84a480d03a841000034a94031a040d0f815442511194000504841c0090b40d50701a000e4551000e07d551480942e54403292800c03180c08055800c1200c0d405071300c0c20194007116140e0321045405850a02c2200101410f5019a020005611000a141d020701c03400d000401c820460807552421201d11004004100070080ca501804010003449203040c480e000301341 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 631874532 1250 631873282 631873337
    0x5010e150d02040906060207180504140d0c120c0c0302060c0313031a01050402090303120c09030708070503070501211802100e0103050702010c0912060e070803130e100501 75
    0x6010703a840070601d80d040040c0d0414826010840e007000800b0480500100380a0180c500c0c4115007007040103000440070103044040c0003030321003458003030150450f00810f2211070480010b80e114078400720540d10703203500d40990303003030307103002000000141c68002440d0724168900703d03501203902503120701d0000d04050a51080707486018428079421400010814250b52007040d9000d803080920300c0341e90714401e01050b4412034401c246e15400820249140c04900c2c1c0c0c4c140d8000e401128400e0800308444042803900e22140c01444040c1c1c45000200098582005030801400c401e2824080c034000407200c900d00a4403c0410780d07115901c41055105031988110300500c034a40041500748510b0359494042c00c600d14030b0f2b81c203600107410070b030000b04180e005014103941034940c2d5646c604150714041d00203500c140e2035a4111882915001c1c444200c010404c034090242c01008040c550302d503100b00915050740b00d29480920b18842c01000c100c8a8800b8030403240841e00203090103085482010902c2019040c0c264 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 631875782 1250 631874532 631874569
    0x30c0304120c0603050c070210020705130608070f0509040b130f060507030f111e0d0c02070501021e03031303020c040c0f1202070818011106190f020c060105010e 71
    0x4000403101078900d0010421070050508590040e10b600c3c044003503030001ca500c04401c1c03108000304001030801c52034a440c079401a105a07a1401e0b10383c80000c8405902600c0c0040d55619410709001050051040400607d0410007018006180c03002280021000a0024242c000090f00046800c400400d00950a82e440700e02c0c0c0306000c1300303854160002d03c001e8a84500191500b0b000c404c40756a50b106280041e11000c8586003456130202d81e940c401c2c0840304015240b50414885500c03109800d00031519030381b81c1c64000d030101a090000081c07402945191710710202c001c00054005500011040f250412002d802d0007481644600782680707011100340900386c20a180c81d13110542d0a60140d00b21203184019610f0b01c0c1024080c4100070180c0c0114400074105d81e804000750019249480f01011044a042c1003036070403800c40d100c0c0c550800304200d440712005c103008402c0b008002458454a1402003c220003142460340c0d1641d03c46e0f68030030500865046c448600f000707211a980e660a1b02c0484907505 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 631877032 1250 631875782 631875787
    0x100b0f04090c0b03132a030b0c09040609020d0e03030403051e071406060f1002060c070c08060c0304110904030c240614100f0f180b43080c030c03 64
    0x103041c121006104030605075a102c0344241561040302584c408a03501c6c0503203518081d81a820341e12102402d24000e03000003948501001002a551075030b004280080c030080e4030060303ca1142500040076075504000d200d400b60002c00400c00001e4004090300c190030408240c6c2c1c000c40c60811a103075002d21840c400940103659444200324a10070008035944102c0050f00c00410b8230712120140801d9502c2400c500d000740e003105000800b0f02c50307048050506507004406021001d0b50b0707841000d080c2002603c00e8443c20303500004001c10710170842050305541e0300c16918180369140c1528014640307450804014010100c61500d04040307020901140366903d0000d0040050690b00c00f4552101501001041e000d825403c0048000900605020749108441c0c1c1710801c030804111021194114040741d02a04e401e0a04c0001c00c109010f400908004200300c0000360195003000244101000c4400c183d82040101d06081c44984100880f10314160307500811141c0c070b03203002e110554150300501c61107030740c80d02c0003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 631878282 1250 631877032 631877041
    0x8010231090e060411010207060c0611092119020604060320191202030103080301060807141903051501022d1c0f02031206010e011206060908100b0f04090c0b03 70
    0xf2905038060340c4103000441c104094540166100c1d0007620405002c81c0c2080304000100303038242c0000b44549200780c0c400d4500b0700cc0000141c1d8543c001203444e001c0d25801c4d00e100b0b0740070134100007100d2083c0c1004003116041e1443d45c00200c292145024000c20140c550101d0500303029001c84500d11100d98034607550700e9082c040c0c403080182c000182050006003100c89034042484540c400c49060383d41044242d85980e0070840c00740e81c40d101c0540700301c00b0070812810741480d111800c0c015141c9181003c6003841c0011031640d0050036908040c151280c0c0780545c412052180c0c2c2c00040128200301c807002030745108080c40c00700b04682c0ca004010341805001d00c0580c10845c010360f84808079403600c2d039203508041c204107103c01c036600d00600c00c40141900540300466519801220343d40140203051600c040c50500400c02c10055a030140e000c0c0e0003090b26003009100303c500c14031680d0014950b0050400514140d100001e00c04181010b40f603004558071541ca0040c00300541520001d00300c0e216070305a99050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 631879532 1250 631878282 631878311
    0x10030f09142a09060102030f03040309050907050a2c04050906061c030e192301110a05030315040b030a0b04060f0c050904111303050a0605010801023109 67
    0x310103015103050007030319908000c4010340b03101c1c0240030070215000080030340c80406008040b640940040e040d407200344541e01510201c0f50046200b280700e95103080c1c81c186000e05021401ca40a0000014007106000d20100140d000700180700149012010160700280c0c03180000402898240d002d4005007803408004034540b000412502900d004d0b503518a2480d50191007078040c008040c4028005010fa84002445180241607003241c2d4509200010b011641c403032084400007c20030342c0800d052030507006010317150b0308808103801d50124000a00780c0e0240c2039071030603102d101c003c3c0080c491907403080c2d03554280d071119030188444100160480e010484e06040040d95103d044408480c80c60410003222840100760141d658104510703110603042040d11402c010207080500c840403031488003441030403505641c800501d8001c50142c40681080441d030304101041e200c050300411101da0040110320521104171001010390b9001400c1009807115203201c1783e004d44001d50044000508200107041100c0c2c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 631880782 1250 631879532 631879553
    0xc0215040557042306031504200105190507050a0f08030a0b0a05010e5b050702010c0c0317030108061e0c0c1203040c080f0102090f10030f09 62
    0xc9002c0080300c20b0a1a020401500d40c0038210591511003010500d03c040f000c480c20581004004040e0341503126036140508200305c0484080d2a000c1702c14070007803440300a80107550b0a10100f071030320500d090b1829032042c3c813200543c0741031400c20000203421000c2c00400e0010b048002d601420364440c044490401034130980017034600510061600f00b41202501e80120910b0444006842d4820303054101820841c810010844504030030031190740c03c074200c4411a10502c101c6030003410a03800c1400c40e05140e0000300480400802c04601641024a469008015255803950900e4241640005480d204130340e822198801450710000000035014080500080c40c10f0318070350400c40302ca640d586000680082d10160036450494540c0b800f01d070200c80c40e40c0041000c224440201c48000215800b090a0b81d402140c7c20359541c0e46507035040c05942000d02c2061945036285c0300a6040003140d00024024002000c116482400019003400006000c0d4214400303080c4982010030001c41c941c1011460f04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 631882032 1250 631880782 631880923
    0x50907020313090c080c180a030c06030c020f0604140a0b010602011e0b1003110f032707081009230c04050106032a030b060d0c02150405 60
    0x920720700c04081260f2100d4818800c00c9000c41d5218803c9807600416202c042c1c2c8080390a10303605260042ca8801500c1e080500f0004500c80c41d80e04000d28075040c8002e00f2a024845614215000881146102c0d0380c0050302d540c00940040c1d104100400d0200800d1800300364120050407902801c00000380c0c26019408011020005414400101c2d0701c0c6404c00c0071280c00020340d9505c0703a200075901140502c40d0b07024410035000c1c0381c203117498440c0003d80e40301c40303810454540034a1100b9945c01b0320800101030b12010050884c00c02420314600b000545034948080c404032103002d60392028000240044605410919031075a07041000c0e41442409140d10744c52030302c0080740910f0034078000040b03183c0300e4440c0d0940c00b02e1303040103114829900d0041e0b8446a01c6c16200d40101500c0b2024040750741d0341d0b80d0042c1a104502640000d818141035006070030300c480d68000400100d01041040003003040400c940302051041008034800c806001d07150311a51807961045d01090090031100140d4403c04035100c2d024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 631883282 1250 631882032 631882057
    0x131b08010e0112081e0c010e01020301051201090302071202210309032503020105130503030a09080d03060302060a0f21020a030e0d141602150912340509070203 70
    0x75680c890b0100a02c4014041c80104142d00c00c0160503a200c1180814040560080060a150070b90400380907080d10700182d69190541d5000004000c2480d0140440a01e0700c1c0c248028055003105480103921501c1620641103003840d0000c50f1802c41d42c2c0c061800a0350103000e070305414100391203040d20350780b5040038070018000d1180d41c006142d20054200e80b01d0750821074403c2d03110301c24210340c011070b03c40d002001505040f240c50b03840411039907400c0c0094a1085515606e40e01c04d0f61604422600c1c1c4900c10f205502071516020040c40941c030b03804112208900503090410091300c2c0154101e405510740c0c0051070b440207404040192070f24440d002016107091a503414400710050300b104c282c07645d0340d000c80e070b00c0420203030f1300800e14004d80c0320b016040020501003441c0703034140c0c9c1e074001c02c0c00841c42041a42484500040c0062145001c0000500f1910301e04010900c0f00c804d019510070a002c2c803810190702d900d20560132010b415400c1e0045000d010050080070a038240034202941c1ca80041e03005414 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 631884532 1250 631883282 631883309
    0xa05160b0114030f011a060d0f020d09121e0c05240709050a0f030201110f010c020d03050c070f0803100816060917060c1b0f1005060d0f02131b0801 65
    0x300e40c42d050041c1001b4451030307134003c2d0104002e002040425888180b0b030710070464a800c0010036019452000e81280004c100d00032500610615107046541e806456a4081c05951105412142c0206074104440e07000b0b070801802010613400e10b40d2034601d00a441c122042c010910406480782c00311b0a803801140b054440342c840340d40303684c10048908035900801104101000040001d503110308403461200a20009440741c01c0c1c0c41e45005400e4820410b0b100b009039001c1a8008046580742c03103500e0b4042d000301c9900e82401015500d00110b1038014601030b04019000c80803034036000c4010300140081145008031780c20320b945644803070000c85080c030948010a802e04000074444101c41e01d0701410260b4140139003000d03070300c0ea0700c2c2c02c0031504005410b28440301558150141000c040207881d54100c01c000081c04880720b010388203016120000c1c003090182400a1007000098800003004989a90494001c1e4a28040008150080a49545131140e20040101d80e000b1580c01c02c1445050740e001d82140203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 631885782 1250 631884532 631884553
    0x6031003150b060d05040f0b100302130209101d03070e04120203160f0606030b0109092303161a0f040b13120e0d120e03010e0d02030a05160b011403 65
    0x504035900c0340030b0140c0244003003000341c0c01c4000951003a030344140b04100c5520001026104c010310010b003169102c25043e0b0b0301348280103500d000e03140e00794000c011080941c80d010b1600041810108080085400d105d45188090107140311803400f5000600082d0454441c1541d4410701e059180d0284d4080d9040c4046050610b0b80d581b000c400c0700d0401c08004043c10b5a080d06649014040d2201081543e08503501d04001c000116141c010b1402001c0b841c0021900e07143c40e06200b441d8003005e80b1010b0021514010000c8045404003c5d42c1001d04140204c840310003440c103103154444a152000800d0160748030030420814242c41036507000d503000e0300d07401181da51295612901010841009484d181c03440e5030b10460700344203414040354500c0242c03000780031100541d220654070103c03c1c506000f2504805240b0030f1030400b407054818101ca078500418201103460000303034580c410381d4401c00c02c0010000e110b1b041101003107040d41030568020035016007507943c3c6032524603000e841a0b07104e1090059040c4007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 631887032 1250 631885782 631885823
    0x50c0304202d01140a0c0f05100f1b020a03090b130e090d080f060d02060c0a021206011e0e010b0a0203070f0302031903021305010e1305040b100b040b040e041106031003 74
    0x56080110320f4480514401c0c1b02c4c0c0b600c142c00c000030581100c092060b2003000d400705c034050140d0b004c041c14080004c1340b001003610401c0051450f0001500031944070f00c1e5140c01180e03211141d02c0032104c4402406a0300d0401010b030040006885e0440b0b50180c450310300f8001016400581d00340700c0b048654800780513032900c403040100503106443c40343d07100c191025100e025151070401800707020300071011110342a0711580031032aa0108540070154036040038004000702c6540410b074115507002030030060402406d20040c1c0c0050b510600649101c8a80800c104017000d008104558403141c1003100a07140c07413590b26000355294400c02c0300f245590700010032001c3e85070003402a42d0614442c60300e08a242030500b00110780c82c10240c22816403141700683c44014031141072184500036409054400b400349452030030002c00101551000018507401c1204100e4000c0f0101aa0f09603000401c000b8410380721810003980c1c4403003101c03010350700c100e00000b8403e00c501041110400c507071050340d41000862500d00704 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 631888282 1250 631887032 631887037
    0x601060807020a300809011b0c111c120215160807180b070c050303030906150d060c0e090a020a30021b01050c0304202d0114 55
    0x10308000d41d008600000000d090341e11525108a00d19010205034000c20300d54016a04e240720908000c00c805030144207002c4070070701620400c145840d01214080044403001081d00444040141820742c00c4100700714203917103d59114184c00c1010020090501700d03401c01c05a4038058241710b40c090310841c080310300d54200130003041e4400d1003c3c02509404052441040e1803c0c80000c003030200300f20180c0300d0200341c2100156a90003134450111200d071110300b1460450601807054010314420b900c00d000f041001c01c0005015688240103500c20f00350101418045403022001c4440100032038142008900b07019400012414401e4046034111503c1d00d64480240481c402d0304c16190006004c0002180481e4002c0307603040030495070000e400c40356961640c1c1001203802c82c3d28403e8402040418000030301c00d090003600d4000145406042c0786080c00c2c1d4030204081291800010089085448054642c0d5114040c40d0480c0e00d4580a0915040b004811006442c800c00c00034040f8200300c1d840e50030140b54105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 631889532 1250 631888282 631888291
    0x31005010e010801030f110310090c05190b073215160302090a0506070b06091e04170702040e0f07091b030b0a080d02240f181e070806010608 62
    0x5403c0150f9003961130b82800d40c001e483c4191541c071014035207013195481c1000400ca020440002c0061540f01e0380ca0b1002020040f54003141c880d01c445031403540d01004c0c00c07003103034210340c290b200311642d850039490024507800c04042d03007143e0308003d2416802a040c0180480c50748041d1002513501e08030344d840000f040e081090700c000380c440310744030500740d4070030b000340d00405803064001d0500181c55030b103c00060b0564040f103030440c0e40c4a1070b1003c2c40442e0410101c1e0b2034120030301c101000780d070584024082100d00c02c0103101070030711081c0100b00201e034492a800c8403842600900140302c03601d0070822850b40d92101d0003070120b082c8036151000031402c0c800c1c8900010610b8103c0c940b0100100740b00d00710080c220b120300044d4012040800061290400c00c550300b074140c4940c0151614a0449980c3e044c681448003082017a40b0f00c10b8108140520803a0b01c1aa001c610f42920441c240090028a843c081d048501c0d610009507038802e0440d00080010740d08210341c00c0004886250380c0780c1d44203c80324541600d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 631890782 1250 631889532 631889537
    0xd0207061b080a0b0f13022a0a110a030b0f061c050606120f0d020f0715051c11070c0305060a0912050c100f0b040c050405010c030e03010b0a0b031005010e01 69
    0x22402d0a003d980000c40500002001c038001704040c1400034131140c506015a08045500040c2c01044c5c00d4162003440c4d50050840c41004061040c0c2070480c0c5509003840c00508852061407102c0319682c6146c800c10186802001d000f4081c500441010407400064480c00d11403c1003542c10301192240701c080d00c1351207a02201034055a20f0720f50a100901070204070300c3d84c140c0245049410801c1041109890110865005000ba40180d00e045418a01c5a0f002100e220080044200c8400c0d0000119412a81c0350034008124881e01d501c500028140603001402441001800c0c8050041059252068a01400c166200c40d1200780c81e880448450b040020004241c80f005d40d00b0640c040c001801c1c200107560181c8210012990054040b14080918000e10560740c103201409410180f06036001070f800350405518080c241000644070041d1031400600700220210a0401500c080d0480021600e000d0212000f17261143c40616207600100c42c0003400307c0402c0c000040c0c03076215058120140d18180c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 631892032 1250 631890782 631890797
    0xe0c0406050d20040c050a090b04120b060424030314031506030417070309081e0c040e0c030102070c03140c0a060e060702030d050a09080111091909020d0207061b 71
    0x1540ca803400d1003a1240c620140c9018003041d400a83ca5174041e1801c214003e42d00c00d07a03115074a1304007510f106880e0304651000a020b1205000e0901ea200c011224507810181c022250b58032340c2e000401407c1e03000104035841c01d00112440111100d015140d0980744207881e90701c41110380000898150000716030745008400303004020089810118002c5810034003900881c5040f52a440d05003d03640d00c00c800071000a80d106008021180c0244040061b0b51300341c19030340f00521b40c130003042c52b82c8480e030308c0c40c061041d0740d5100000618041017140070515a0054002e5440c3c55850420b0803c0b14440e11040d40c03040e003c00c3d2846047c0f4408a1114003000000301030565003802c090007110f1420702c005a0a8001e0420006440540c1d0200300e84003203e1542c0c0c0d00c3c160b490041c0d0000034210107565210140580c14500d1100c0d0207150082510750420055907901c6c901d244810716006451034a50060484500c0040d42c484402c0c016001800550b00540003808040d030a044101865401440c1c80c10003c0c40c032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 631893282 1250 631892032 631892059
    0x602010f0b1e2d010906210506010905040e1b030307120f0c06140a0e01060302150a0903081611090c09040905010f020a052203050a060507120e010e0c040605 69
    0x1a40c98964140c5016010300d1180c0d031a800e40746083c44440465640080f0030f0101c00d030b01985d005081401400c09443e00001c010854408004104442034410888a4403100090ba640e4811321a4a008003c010002c6c04403d1a000742240c031104980305140c000b42c002a082d8016007400001c0300c282951201c040c0e580049006401c490301e824106100040014291502c00421101d02405c1d14005004452624600308096050210b41c8440440c4246904060703041026a88502a4071010050209826983d641e0341104554042d042e40000b00940e801150340e120341c1c0c00582003159120312070080010b0040c4a00c041010070b0b0700803140c0d54050241085404198107090f040020398510910002c82d80d0b09011078103d05981183d9000f40025034007080c0c01811015100c508291511903592071190f0740d045807280d83d02c071100342501034400e03034984c4041011244103440742e008d44103001904100f4904098142806001f21400a030131610450142c400d45150500c16082210f00003414484428803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 631894532 1250 631893282 631893319
    0x90902090402070f0b090d091a03060d0c0e0921030604020c0c090c0a1206060906050c03130f1805010e150402090603010603020913020c12180d0506010602010f0b 71
    0x26100c00c0d0081d07024081480002c91840d01c3c0000709208400001d49441c04022103031919090903004002c20921003810400c00048030100e680d07118940710119500c0d50341c2008168212015000209199820340300000c0000040c0c1d2440d009001d0b82c0706039240c1864030000e83e40a401130307135092180620100041007044c0742c0343d0300400c40800315901b81c403408500c0f40700290414004440020030420002509226103038048051004805213403010440c2790300b000801403040559020381c0e803d00200080743c0b0305021003042910f81c1c0494080c040100543c0751503510420b030240d4800e8008040700b003250244003140724000e40c0c2c180c0750101c423050003d41d00c0b80000c06242c171000c0303003007500a030f0300308000845625018010750180041d034501507070b5040301c0000d000e18450303030300c106100c207501c148403e200c40ac10107d90710180034041481d07143c80320082c0045002e070344964111503501111020000c8100030003c81c04030b040f240c5a40082001003200410803095456030301001c1c1d030140400c02481182d10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 631895782 1250 631894532 631894537
    0x1104050402030a14100e0307050303040609020a0305010c02030405011d0d03050a050403051b03070806100306050402120a1b1413090c081002040e061021200d06080607090902 76
    0xc0c0000c0440e4840c98840d207a402c0d40c80c0c0320404070892a0050796404010300c5981c06240900c26005005512301000c0e5202d81d0307101c1c0006400140819103601e6450190342e182c50004020f59044002000300e00041d05e0060b40e65807080c031034580860103c207603000740c9400390607281210240141000e000d021950360f085815070f00202015050190030311020020400811448010004003804002e50150078001c01d4541441a030000c1386e5035200f00c08200d0440c0700c011030542104c3e0300200100b002d0329248000341580a203841003100520504800b0414404444800400c1640150020030701588804c00e1b4200b00900307d100640050707080400b0100d40d150f651001410780d004001100102d6125018942402c0c010201c07905c00b50740100d828407001d81d20102d0f0580250046130018842c0850010203010b000c10549400c0c034a00c22000c10100c10003094002521880307441401240000d04c0d124140000d400c030038510428240382c0403010480c5c2000144140c028112511030010302407a02c0f018401a5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 631897032 1250 631895782 631895791
    0xa0f1b030525020f0708030a050a05090103090b0a020310090c02120d140702070303120213051002070801050c120f070206130c0f032907090b0a020703080d020307020d030207110405 79
    0x55081c1d25141c0001107000c424030802e980c040d4081e000d43c02d400c801c21483c0100d0358001c201303250001c108001170250050200e920032074880c2000e548540c02d43d80181c00400c1c20110152400902c2c3d000c109400000d54001c6204803d0150181183c1e500e411a101c100e1b10241c200002507840203054070340d40d006000140c1007003110351740081069041c142e20800500300031754485000d41c0c40200300f0300c101908000503a0030100c00300411424043c0c4c20071071010264007481038a00500682e020152014030038800280a401880002e210381e0820604186d400d9004060581c0045030001c0816001c0440d9908240140003690007080300b1307101c90710035804010b0000c200300d840541c140000034105030010201e2004601410240c0c03200150118020b840500c507155620014047c041041805a04500101d041e584002034035500d41c0c500c07943c2646400b0040d0405080183c0114043e14624420f40086201b074406509843c007102c1d00010950581c0a5440002c06003d40d00c000030003141003560200383c0c00b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 631898282 1250 631897032 631897051
    0xe090c07150f02091810141201060f05150c070509090f0f010c0e1f120b090123031605090717090c01020d0c0506240a0e0a0f1b0305 58
    0x99001440118040740e01140b08090040d4010403034420b103103446400c100c14044100003040d83ca2520500c0d501c030036006030051405401c82403400c1300702c1743c0f030f880e80d00e440b800c800c040200452900d800322141049002d104440c07062212490800f400c1c400c100c19038a50380740b1354000349030040c100707420000c070003200800e0054940300c1c49d544034103006000c100340c9601100d460300024a030000e50000a286041040085004520000341d07000b806800c40544002242c2c10700d40302140080c0904003801405051440031342c0007401100101320744180078450080e0b80c0480c1032404407214503400f0b0544600c03404903080046213003e441000300c1d0500005450707024895280c0700f414100c0302d1040200c044002d40312a0702d00c0c0d028511a5000b03503010801030701340b001c486c1000210140c0ca81d80d030659980004118500300c10080e079619144040c041c081c2021804024051100ca54032103d140c40c20003c2164000d410324100120400c1c91030551052031590640d01e0503403001c9800120058028050103445d1220 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 631899532 1250 631898282 631898303
    0xc030908120f16080a0e190b0a0f0e0604030509010c0b040f02240a260f1506090604030321060b0406081530011a0306070e090c07 57
    0x241040001d0010781c0185581010604081990740214800200518103429000c0340040d40703140c0010341d4617406100c001c0b01181b00c11018480c1c0742400740080d204442d1246025420007000480750525114014540b820466082d034085010300380c501c0e4600071221504010301117004030f44120002d0003804018181140c0a00d156914111001d504072000d90b589001d44501d1011403600405800b0211200140e00442e08030104c1c45407250310450a00b070061111900103022000942ca09105264884030a0214903240501c20802904002c03241030500800390001c0040914102c8142e0b926a48050607460405046075400d0314691001c0c1c1020b51090703414072041c0103201d81409103101910304010520f8656123800f20280c0101c0d03001c4c054200400c4450401c0c011a11000481001d50055110004a46020291303a0410341c12041c810500741d4201008541596030401c1da210081c8420b8046502da40e4404104480340b0412005007540314000101054181e640900a88001d0b4051080441c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 631900782 1250 631899532 631899551
    0xe0d05071505090f09040201050d020c0106080307050609100606020606130f1d010b01020601031124070503041418010b0319140702010c170a110d0510181e0c03 70
    0x140d505070144400040c40c0001c4503c000d060030042406124015615250035041a90011b042401502c815540c0541c0c0415030118580094101e94000d01104095139564415424204e031074910448a6000a00c0380e903a008100c80b07210b1064608032440c69010b0000c58443c00c1c00c0180300202c81c0b280c1d40600d5180c0e070602c010b045040c0325421040d04010450206208101902401d4840101e4901e040d1340010004101240c68001c0b01040420206d03800305500d501101b005107411050034190081920114800b402c001d0300000800a940380c005035203646d64026001c210a080d01b0300d03044a81001c20800411000e00c0d03030400b5603000a00c1840c0c1c0c282086180416100b150710313540740503454010074010f1080440d020711911021003403d240020802e43c00140045003504058201c7c510740b030741d40f100040f500c01400144e40c50412881030911503803e042080d0008058980282c00b214203000641d0003a24015215041e5041150034a00701c40b0310b07019442000809541c00304000f495161003901 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 631902032 1250 631900782 631900799
    0xf170c060708010807060207261203010906030605280905340902030106140705030702130905060c091008060a050603100e060a030b150a03061109010e030703030e0d0507 74
    0x14401c0c041555000003561600c0c6074070346044050f5100d4410364010203820301c1880440ea2144030017000d40c010340199003030303885030385490800c1020030100c0200002c4004a417040700c80d00074104032406101c052095840c1c40c842025000944521b10708009054031140702140016085400d010740a070080d9080c56014180804080104924803070030340c040d045503c44250621081c140c003514412608500355814030f100940300e15100c18100f200d011000c05c00700308200003082110711465020b040e010098040a1028024045460302120b950050b90f0001311101040d5069980250000304600a07501c03400c3d01c10b964025000e0290343d0010303401400410305466a40095000e07800e0384205814841c500840003e100c0405041240700700840141000480d024901258000c0102c00106104210880c00101903054a80c0002c20041c20880d01d01606c3e1612006001c0e040da080e00c1d10110032a40c401015101e4260780401030115801203d140880c1c00c102c82c407040c03003034400c074100c55075651900d051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 631903282 1250 631902032 631902043
    0x406120c1d241201080607080c0c0c04061701050603010506060412020109050303030c03010e07020313030305090607060906020d1103010513050c0f07050d0e062a0718090308130f170c 80
    0xa12441c40740c0010f115094098180200b030040c401d040213400b00d0304102900400f45c0b0701c00752045a075030101150720039072140c0501456071841401032041140031b030b60b680785000c40c2488036034001c40c40d40391800042013410b040c054980700d0322004098510301414807401e04110007007960306904011000001182a85040005500490303504c1d1003280c580d85440e4410880800060003c2c04540092141840709841802c0050a030381e4182041522218004c002c1101801581009440103007003845040c14008103600400080301d81580030704c4140030501b4003450510081c4920b680201a242e8100c0c0c03140d440c1d40c40390f60041d000d0240700e0324000b1524500400394110b01002e480b80c1d041042000d04080d000241040d4551003958a141010703842c140e1030080041c0c0420003c2d102c0620785142030296402c6c002c1c0c0020f80041f03520344020980001804005024200e4103c0102ea4001c000c80c0c19040c00c4200540403d9002e0041540c0f8401d55a40030030101d0011801820104107200b00300d1030381001d020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 631904532 1250 631903282 631903339
    0x207080304031109162a0f0c0e1305030f1608041e14010816091805060312130315180506070e010302090a0e04260406120c1d 55
    0x240c41d106112500f00880308802504001702241e031140200e00f515040340c00e15801d031850581c0b140d030110303004000f41c00800074440001d001e031110918000030406400000403d950440212444e59a105c003981003c1c9448180c014100350b005015042403152801d0040c00e2120a00e0340034150542d181c5e41d00d0392550801c1c1c0003640d10480ca08032703500d1071244846101004010390030561301c103d500c242c0060400b06006e1301c3c910300d20700d12207858a901030240000c18000d10103560141811b1101c80b04140040c001620181c0c441c0c043e45100c04440307800b44085d5418080d200c9200c0720000d2860b5140280280d010f001d0078402c076210440c55400c003540d80f022206203802170020380070500c2d2810009109504011400e81803620610850400d522140348080503500d10705603601441c2c0710750500d55191044012541000300d0341902c0c00e401e03a440c030005041103580e0340c1c07101c0d181ca22085203a40140ca803000c82c40c0000923004c0c012421001500c0d481440240e0001d8001410494101c6846030030560145 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 631905782 1250 631904532 631904543
    0xe0c0d090606080d110f0109022d0907090609050d05060f0a0905030708030603300703050c0118021003051509061f020c120303010b0f0f041e03061109030703030f020708030403 77
    0x1c45c45614038034213101c103140c0043c01d20001c11824449a00140e9107000c0e81071b907500424040082d64510b0460780d2603805d40003900502801c06480c03e40c6006140070120b019501c0054800300c0d00041d142419610b14076042d03131101c0504020b90b40d54000010014000700900d01864485030088081030091004092040c09290410f0741c80ca04002411b140030a12900544103080f0303d10742a034000b44500c031071003a1220741e105260343c9a480d0301382143c0a000e550320308800382d480e2110074807502120840003000c0304d1080c0d6843c684044050019411518112108904403152a000c2c140d13624142d04c85c1a0700034001404c1328a240801001f0010611a4115050240c1c1c8400500720751031401c51501c5215001c00401989150b04220481606004524400c0c02d0b0000104a40000900c1c440650f005400300e444420040c049121143c10048903921064404501d0f01c18210061b01d050030440e20036000103001030940130300e941d40c11200141303008040002c5006d5030301e01141000f020300003003000f1401103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 631907032 1250 631905782 631905797
    0x4050d0c0c32060a0c02040b040b0603090703030f17070e0d1406010e01090908040315020c121905041d09010213060203070203010c030c080f040f0b04060c08010e0c0d090606080d 78
    0x980c000e0b191414046510744640b03018004840c071698841c0381030189a40c1920003060b40d004000101e400780c0640b80c8a144d00c030030044104905d0180001e0366800721380c080e58440c0c000e41c41d1a0700a4030000348402c07640d040b1070000030008803240d000352510f000742100a8600c54240049488806240d03246098007031182d0040001013104846010b0002e0142000c070b402040440b88580d20900c09100c0c0f80b100030030300e41c00100b49003110b51059059172402c000110645000072028192600c056010420500000c000c49404e10300b070034425019078040e55420704502051281cad40a06494080d4010315040c45503400308403a6606040c0000d82030b0051160b500219110300341403040500b0f403000c00b21110101850220408550380d440054a904500c0408214101c3c1d144c904111507400c60741800909544109003d100802450703a0101580300000c1d500e51520b640c03140707002000c00380c06883c0c2d000c070307100d060210055410055024000f40c51190400145450303a5552190500d04000c07088004550700 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 631908282 1250 631907032 631907099
    0x1505040f050d090501020d03050a0207140a030207091404080702030a080d090c0b0c0705012303010303200703020a0b0a0c02041121060d080d0b040501030b100e04050d0c0c 75
    0x800003000004200e04001290f1418800000e5803407541ca0307090010540c0b80c0e0003184501c00769604481c00603811420145800e1031001d500c5950350320f800000c80052061401c0002c803001c00d4811100c1604584030700840c5500c454540e0982c0390040c810a03a49400340f6030f0400700040c110380040c160110081e8010901c019641020784903143d4941c000c42400b481001040c8000c840455910180e41090038103074445900c622001010118031111181c08007000400402419000550701601c0d00c01a0b01100034038040c0e1910585800003840025080605000240a8089003801405454000c1e10305220251100d4000a0640380c00c41c1d1000b00c03000c070000781c10140d14071142c1003491005043e29036108030700740030f4086414401c072038201030280440170681d16001400f80d00844e90381c5500410601042d6124148098403507000d42d610b01d0004080707100055448084030929101d1038101000e021880c41001c410f944441d000441203600344007120020556651007102e5015618605140740c083c03400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 631909532 1250 631908282 631908293
    0x60a0b0d020a090509070f06080609070c020d02091e131a0411060304020411030a0f06050301090b0c0708190806040c2f100617060f1b071505040f 64
    0x404049050140081500318009619076504002c11a441203600181580d0f540c02c0c0c4509141480d04600503074018031100040150f40202d0303190251004a4400d010741e1201001682c11441c0c1c0034000390050748407c0c5500142c0303440e000071355000035040200c000c0c01c1107503200c03291045000c40b03082c6030b05c00301c035801201440303000446c00e00c485a05040107c06418070b87c8038003140810f020080b6102d00c0c00080001e04540701d82d0045d403000c0c014040c0c03958403810100e05200181460303102c141d039801e00c0c180d0001410325050065181990700802c000f8100e45410f0700414045d07104000c01e80c1c0d4100c04004400c00d1a000c0603d45004000302e584035169800d0240402080e42e088201001c1000041d500404411170503084040c16509045111304400246920060504c40040611071102c2d10702107000802441c0c2c3c00414024092044c291070060750317049141d07812010b0076500c010710701150b13001d04035041001d000208a26401418171002c1c0d400c60003014015203000315022515100f2080d01d0702d08102 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 631910782 1250 631909532 631909541
    0xd0c03050a0b1207090207111818070b250b010e04110a05092712071403040e13050a05010207060b12150a09020d0507060302121f2c0405060a 62
    0x400c111085010125542d80030f0b5a100f1650265031441680018082c00304890746c600079100260140034400c070700783c44000603059004215000d0025182005681c48080408204d400030b0301c004048007414011400046086400030448460745c02444100c030201144079280118003c014200142d1458030705494400c0440c40540000750091201e00c2c024004c03680c0c3c8941d03041e030015158000484801c10080001d20104040000c10313540c1c0240b00c0702d90101500d850080c4481405046012070200c0f0703040e00c240da2442070780700303842002c1c503c000420801d03201c00142d864018000c104490702162203071035140c2203038400903080708d55030303a0380c03503501140e00304045100d032072005540c003901180e2000e070002400c07840001d01340d524103a80d03084000c007155900d02aa65155401104481030141c8490b0080e000754000045408041381c40c400198180703040f074120a801308110065010a18940391000313840903d41b4a10b5148055480c41c900002c6c040300400701d2249005200401c0c190411130000012074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 631912032 1250 631910782 631910801
    0xb0105030d0201060b07060b0d0f0503041a090a06080c0f030916080c0108040204020f04030f0503280c0807080d020d0606030f060308030112020d080309060603011805060406110d0c03050a 82
    0x690420301c080180105040654182c10f80180d400315802c2306100003c1c02d101180ea038001c00c0c0c403007003000d01e0041c0100080588196140300101c03c00da0000c00203a01c101d030140c0d0380e5280d48400200700030b01ca024451000d040c1c12a1000d100a410500003070200c003400e0304100c0350011103a02000e07505814a0382e501d403445c01461040d02401c00517a651b4002080b070b0800520190049800280c205c0c006a046c0e400c403002940c20005010143c00d403031420549a070b003d03020401021017512071080306522104d810000c440b990380c44410300880c03e0340d500c0409400c080c1050b1075140f0148480b10404240d40002e004820846d00001401401d1050180403030340030102452000f03140c0303034040c00000c0801080b2030540c2d85150310022400410b1000849403010040010420a00402130110810340054510b0050100b2002030207100d0245602c0c99141d01d0410018086501600100e400301e2407540c490081c000e0b28501d12858461900341c3c90007581c0500c000440040d6952041260311900d520031110903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 631913282 1250 631912032 631912037
    0x120f0c01050f0d0e1c0e0f0f1f120908070b0f010f0302010c080c071e080a1112011103070c0b090a0c03020114130b040e071e26040b0105030d 62
    0x6040c4030202d82d51590180c580f0742c0d26455520071a459020000300b000f200c6480c0c100060030f100f854082c3c0d001300124000030800c0d0148846954140d100d192404c030000c0108405080c0f400348928007041d4130a1105012a8001804524003580d8509000b83c0210301085000f4010580d6a164920b001042e605000342420420901c44006001c41c607890380c0c42070200c90302443e180c08a4066411318464601c264103440d036552145450000c0c40182d11114500c180f03545042e8803c40b55600d50b2815203583d0240f500901c1599101c000031400c5c03806030303c4c4004c4001c5400000545c05100d2110785030310781c400d030749100205107010741c50340800c0407070034101d54040e000d83d02070a011111980e4948081e4103d000c003d05200a01c003001c1030310300c240c000303503440200407403106c075209665000305501d03a50140c0160240d001c0041c000a20050207040c510103a10300d00caa114454200e4000d0460315000710103501c3c6189104a00300c00d20f071160300c440c03a9004c1d03409070602940d03e5140c01f04243c5081040d218481c107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 631914532 1250 631913282 631913287
    0xf06020403141917090103060e09010915110915090901030813081531061a01020a2a0902280c030c1509061e0f0902030a06020c0c120f0c0105 62
    0x56104002854074413401001c44d40c544200c5801078028191079040b1104d407210309030820062400542000d04281d01a1840b61344016000f00c0710340c10b48034545191801c2d044100001c20b01c40c02d00314002100000a00b4003981048550030000312120420b910a45950300d001c41c0e5240784280d440c083e20001c2c4003440c0213104103080a00034552181c80104414804500340c6000d0342e114610030061410540d640c02501e03038864503031904500800b43d50001c509884800080c450880d4000101144042d8008001010980900341c003252008040d00b03400700c5084d40054006800540ea0000c0c00041d00c5030650307498400c258079200b201c0003031114691420044046aa0000700f90404010600a034000107a0300e51a0004910312000e4184220003d16582c5040e4001e204940c2c40c40282070590740c0d4540034000e0203152101b6806403080d41c42d0195158005035000c40010b04154003c0070400c044505560000d440d4400140d800002da50104030b40341c104621880a5440c240a4a201036109003050760 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 631915782 1250 631914532 631914583
    0x303110a0c110303070b0103150507030605060304060e0712060f0b0d03080f060415090c0206010501030e100b030a0605090303041a07080406090c0e0c040602060112020f0d0f0602040314 81
    0x781080c5814401a09140c0c0c034100205907500d0500481c0c104031740183c541e5003503581d00d1409170130708045403203003e07119031030000031519a500c64060141180c600800702c0d420340e10b0700e882e02c00042292568006041c410000c00055140d00508841026405100e0000758000d0010014094030b800d1a019440b9030a07000354013000a800100c199006496240b60070f003e503480c5401706006180601c203614043c00072403030024035480380f074100d02d481b82850f40c281d034007690780e13800150155800384001104a030056201500019011fa1000d44090b0004088400b01000b0391554000c4034020f44062190f504000100001d001d4003190242c59180c1000038008a0301c0e02c0180144041400342006003c10348403000340081c4903d03004920041d14030607115000900344205900d845611078030502016001d46000000c2d94240050082c14540d009420300901c400c0c0300c0e04105010869407811291200e0b0302080b1004206584041c2c005144594011030f51a9040b140ca203281082e948440d0f0b07418070540e0a002c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 631917032 1250 631915782 631915787
    0x307090506060724061403011401060906050705010209120114010b0a0c080c01020c010525090302060703080712240e09070504020a0c050f061518070807091508040303110a 75
    0x310800342e0000e50311485110316013041d030103d00c0d00c42c6114840508208010401e004000001e0584035404c038003c0007258940b94201d454103000348185004500c210508100c0240140700a0500c288681d00051a01101e40c0c001204081012605121a95a002d00f81c01c03064070b05848502400c4c100400c1402d00c554020008c00444400310001c10070240800c1c2194000025010350b480d510006009000c2da00d0311207040c01c0c504503003081000100301040c040314200740c0540031311402e0b2134001e0141c615040f8281c03820349250b00054110002c20041c02c0b01042a5060f0740700e012017480481903401c82400e070442d080640c010043e04100c0b41c904401c0c0511070000c1c1d0020340d06080b44c1c001c0c0c8015880d101a088140ea10049009001d0001d01480c02e018400c0c42c4041180ca2140c00e8031401d95010105c000c0c1840030201141d07030999804d031480780100303000070300800d034441e0301001c18506402138903215808982c031150081380380b02c04510900c0034841055014000c241c180314090b10082e04000c16074000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 631918282 1250 631917032 631917037
    0x10812040b1b0615100f0c020609010903020a080706181d27070e0c07031209050c0d0b07030b100504050418050d0804110414073b030709050606 63
    0x7034120200000030001c400d0503800d03840804038249a01501c8251134900c86480d400e40345100da45102c2c03407060030080e20842c0078034012240d6244694519440b6070b0b80b80d081c840c40b640050380d1a4140800d22000200603560781c9030070005000c800c400b07080304500d005d201514009040ca1022024402400300348010740e850415448454040c1240038502e031a620304014041800b942b2110a0812001d007480e003489001550b20121840c0c001d800c0081c2d503500c2c8200a240c090350300700a0005040b400701181444542e089403107041c1c0070f03000fa5420344050750002260441c2c0b003a4110344c1003010000b0406101d815100b104045c031800d4952000407001500d00a280d03200b80c0c0107852080e40c3c0ca0b4003100c2c2101ca80107803c41c909501c2800c44070000c8894001030000348040710111808203148001d08200c2c05e150040c40890101c8140d480d031340e9203611030700360340210b40f62740400c0c44001860709034200c070600301c03a175030b210b401400076a1483d00d640501403505040c41fa0700a8030ba16130030328041c04441c0c1c44082c02c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 631919532 1250 631918282 631918289
    0x10f05040b0c0307030b041d0709060311090c04090c030e0d0c0825120203031f0e0402060c0123090c031507050318011505040518071a1303110901081204 67
    0x2d903480d41c81c2c49090f03004181e1010025045460003d5000341c43d03035114244014005a10111020195640e06403c00e032191350000414043d42001025140c3c186500310030340003100700040d1400d013503c422012045030307500c030302020000707490700c2004408620900c034204502100740f078100071410320741c0c942401c24428020368041810481502c1260049001071010419900c40305c4034440a00030724000f5540d400548601c00070042d4688a0002490461000403c5a0341d0103a0480980c0d100e030200100b90708802ca03140c907a552038440080e094000280e80030200c0002112031800348c18941c5245207800f41401c1d0503070017a0320403828085100409820560300c07600c41d1070210740c1da95a05001381c088016007200c4d05407660924040076414803d0418103402e64005036001c00103540c074081105100065907980e910b40d40c114001c01e104005400140c400e01c841c14052592402c2d1160b9000880d1301c4142d8010386060b40e80c6848060146403941100e401003521400401180c404102100c406215a20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 631920782 1250 631919532 631919551
    0x4060b06182704050f01181203200d0e0c030f1e0a020d05010c081e060409031b080711010305070f0f090e0903190f0909090f0501050414010f05040b 65
    0x108000e20318440154060b1203180c82200810726062900d0641d03501d81d41000c085c44107509206c0342030050b034818050803940070703040840f000c40724000038400d8004040e04020300307144d41040c0c016286c3c04c005450040640124100c40060b086c80424842d070b0410b0f1400ba0b40500c240c1107402c0d40402c0c0d150000e400725040c50100c07402c0c25405800c105c01858410701e0303900250040400c030b610782d06000d01035015812040240d2200c2e100b9540d402690580810002480c44441020002117101c44c203040c0e0014450a00c44c1c00c005281c010384105410b404220b100d03084030000700004000741000080c0b410090300b150282410301c0141030030100641500c121741c260b4410403544002040803948034481e040000c0c40e0841d80340000b42070000e10180c0b2940429491081c0003145402c40c0300c0f01d88615442c90269160303549541c1d0f801d041000001c00b4102001042c1c40c0045045904c002140b02031040a00a038815194203e4505160900070b095407140701501226500d400104804518204c440b95804030146 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 631922032 1250 631920782 631920799
    0x1091503020f0f030607110d0c0c0b09040e12070c090b060418241418060105130e0903030103020a080f06070503040501230a0f050c0702010f0909020a050304060b0618 73
    0xb0004100031510444903194988203680038000c5c0c0c1c6070010000100c0101e4001964005104018261a080c00a020041812001c524100202e05500001c2c1401440091001c200d03841e200c8134541c58001c1a080402c91408d000400004110b4010148070023484a070406010117609003000a009000c1c900c115400401ba0304503000341078510303901500e0b100f410b86603022568240d10802c88103110b6a80a0910001c040c000d914205103400d1624560900c01003c02108541e507503001142e0903000584902000042100e02260030344181600c0743c800d2005600564896245004104210205a100800c1600700540304160401c0c08a0f4050f8040c0560800c50303603a880e24502180101100080282e18007070b80324a01c020480c0800b0242d0144500c02c1c4107100e00020b1041d24011104181d038040c4000d44108142401540a58170b1583c5815080c10300080b05a95998880243d034006400c030320010b01c0000c00c010400c5a60302c1001e100c01030590303449007890b15803602d012842d054501d0315485640768 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 631923282 1250 631922032 631922059
    0x420010c08030a151202131e0e0f061e0406020a0e03010e0c1f020c091e0a0501090c03090809041e091a0711150a150b0706050109150302 60
    0x30600890aa40c0c070046a581d40d00c0c0040b003040080c4a958580c0c50441a041400a81310307800b54101d41c00a03030002d016111603141858418000e280c0301d4503e2807040400d0000700324407101c6114a803041c140d500d02400c2808941107460b07090a40081c5080ca04a012641508410314844245a41b160380f100c0c00603030f100700c030040070744049404400b555415030901121400c0d1038404a151904c035030b007c2c0c40c4240e80c5100041c4c414088140d070112040189d0116903804241e2501c010302640000ea041349150799000a03182c0c96448403c01c5130031040b40c2d511000104101142486030310046109031400b0420700d043e5541c0e18038107109140c02c19101da61200c03039444120840320100c009a1010745000c008420305854851000380c20010100010042d401c0010440790003841d072920046201d40c00b90113002041c003804800c9010181c20b0008403a91039841c2c4070400941840000035002c08502c807038941d61580b429909072401600848170260510754060403c00c0c9408445040d2941201c0203e0502003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 631924532 1250 631923282 631923287
    0xa0b0406051e251b08031608070f0302160602030f03070f09051f140909040818180109050a0c0509040902010c0506151507170304030224100608042001 66
    0x15500ca0300f0b07800d81581064204910358282e900058a1044c8010140c890300c1c0080f01c0794403480c0e40300b104060b030010801034040c25400b2a911041a00c12080f8905104a43d1035149410303039122401c42c0540c0c06030038125019010841c40b074006010038130041d480d00d08040741540c0d09020180002007401004182c031f0704410701450800020b410003400f184010390b80c80d0368249959185544c0d50000c5000d8124070640c0c00d82c800d040b540b0341c40700a002d0401545031551035580300e0748440342c1c9840440700b514030901c1c183c3d03070310000c2c3c0d402d109101c1e03c108e929410428400100d031405440081e13924a0001c01132101500001070341c2e10148211400550320a0500041c0c9103e1583d40d03008002d4001e840c100000000b145626641c910740c20394503907000e501188030426952203074030310280200180c0108420740c05994001194060300c46e1040d2a80303029002103001088154080740b4003003100c6039040160401442d4940c10007002d01c3c0c50248458203080e120207041144000d03015070940c030910075000e1180d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 631925782 1250 631924532 631924537
    0x50907030b0a1a0f13050c1c090c0312050d020c0102030a11030717090f1213080a08121003051504060b010212090409080906042d21051015050a0b0406051e 68
    0x7170703440c03c0c02c1c030480c54042c186042c198004030244c0c0054501e100c5400b100d05481c4148074856a004003c03003002415503c40f0408e001010400c903041010030049190902d032207001800c1950342920015849044c201410802e486030900c0c9031101d01014401c2003130310365012542c2803006104446a8109807240b131911810440d0300c81e06d2a078940b0880b0860780007459030300010140c00b01d041c14940211510362624540701c1c5081200030b411604284241c80313000100c11080e5802078920503035000300d51303a2a40c030386081549042007031031440340290411042c840300740030300c07a040711091010b0b0030782e4001d0600c46249405081000360295030307600075040400501394125183c0f000011f1400c1e40b296030b83c1d6040000c6601d2412818122030130030000140c100b021745d40d60803d071844100a5950f400382c1c4c200384c051618040d00706a0351481a1308200003c2c4125200700781e42c40ca007a2032441202420304050068041560380601d41450b400c10041201e550b110050340c2200813401c124204007024110013800780d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 631927032 1250 631925782 631925809
    0x9030d1e02040303080402150304150f0b040e24060d060b31061a0405010e01090e15030609030a020d0503090a0b0a0e010507030615120f050907030b0a1a0f 68
    0x3a4400a40881415003000c80e6074401c81c0300322071450101c1c8010404001c2e5010541d00200100284245000c00c00200c1d00144904029100e00041808920307001409403114600008c6c1a03802c4400554600c20a446617480e001014901d062120308160700805c8203404200400b401055488000d082540d0310380f40d0000041000d445070036000170311844c4030000914201c1c1c40c2c9100740e1516070001404068242c0682e2000c10ba00c40c140d09041c03510006541c0207500e101040c0c101304c804c0301c0109194540d583c205004256040c6044d52120865040c50b02c0c0000180480c5850341c401d210b182d01096001421f14940ca0652500360744035114854039500e0101701e4000201450715403402c210303144689900404032401e50070b0081c0304684440300280c0446d4114011442c903c100c0700c13403020f42e044c0184000d0050880505000070301c100b03d0081d00c01102d00507528076146401400040050041d210801d903008003122408100c100f4081040c014910751a807401c5006502c80701404406646880c844080d2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 631928282 1250 631927032 631927091
    0x711151b040f09060617060904030507141002430c0b0c0102070c05041503030f11070b0a0f0203120415060305030c010501230102070b0c07031203020a0801090509030d 73
    0x2600c2c0c4403101c0c0001303007410303004d0040080c2c2c0400343c5422141c40e510b510b50003448080c29440aa4941d030b00c0885613688003a0301503400030600e1030542d54108080060301c0103044524030058880182c031208942d0000030300482c240031480ca21380381d9800101c41c900320a0025400d10301d07031035488241c5443c10b252004c0303a1264000742004202030441740010b4008001807132041024040c0d0a03100c2003000202c50190a0030f801e4450024414030020b80502d83c507100c3c068060400422840701c800c0e2079450300085070009403101c0d038081042d18200e07800c00441e650800c01400510300b070404e14129809113400c02040a030003e01e240c03070441c3c007402c130540c0280c000d50381200a903569140025040c502030a803e100f4505600001c2255410341112180d2680081a05a018002a030303e801c107880701c142c0145660b032445015100c40080014a215005009601715440240e1101e0900001a050040580c030001c0c2e0181000c04004801801108882402d058180b000400d40111007102d40009244000c0322407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 631929532 1250 631928282 631928309
    0x20a0c0303080718060f110c0a080c031e060a110f28020118080304111c030207060c0807150902040515040e0109020109061d180711151b04 61
    0x78158481d003110b20609094840014140b41c202900d0f480c0c54282c8185000903503017510b007070700341da00c10440c040401982d5021152060f407008009200388059038050740c000da100e0307460004c4038103041c488842802c4240742004403041a0303058898803440b00030520307940e955454002c000c0744030600040e514403410b00d40c034141c3c82ea40001581d500c8100c81c4511503500134907031501a4405841400ac2144815886100780c2501c100c80d541c600032900050403c0300d0105c2d456458058903161402da0148200300042e01710820a00750901a090a0700e0f504900208080c034075201d070104541d8800c842101c0c1d030210300c0c0a00c40740c0a0300090014103030540001d50050034075042c82200d002421080307140003c100d4040100f42c03480400942254500d0900a000c260301990400c10b05014108589a04181d020b100d42022034810020300e551148401d82d00224404109200b1842d901044811b080d12000c001000714000c12114100c0c0000018011518100001d052000008012050350010405e107200c0f583c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 631930782 1250 631929532 631929539
    0x1f02121b0d1103040201030b0d020102120d0209060d090b0106020c0306070c051006031104230604050601051b011d0a0b0408130f03080c0c0108010f03030302160b0405010608240610020a0c 82
    0x10842d070320584c0e0581c006428030040340c42c3c43c548a0b44841030164160010841101c0e00300d0030040e66040441200c04080e800e0103074244603200c85004108051445900280382d50817823401c80103201041e00128110362100c4100d00940e100051025008615414a00b100a4103440c0c60780c5884045c502500d800380c14080c00004005d0100c2042d98880f0342104c050100300585002041c10704101230444205041a00200300e450415600c17498000c0c2d4103152940ca08600c0203400c0c900051040070092a9a5440c0002c00c960711039114110243c2c940c00c80900708150b06515840507810380500042d0425a0000e18000c5041c0494002d10003025107801706200c030381d0340703051840d02038008604010701400b1b201d04280e040d62051884605030340c2c100d80c0c1c0c44115421034030118020341010390b545058003000310241c4041100302c492544180c1c851000400c8150a10381801d00300b1080703540c0c0c1c442c1081003115000c0c81c41c40c00200540d00007010b583d01c1c840d001001c242246001e4180307502800a100848011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 631932032 1250 631930782 631930811
    0x110a0c18090519140d0804060b01270f06031802041d1e0715090e27010c020d020105061003200301030804140f06030106051b030c1f02121b0d 62
    0x50710f500400e076044c1e28141030448241c45c0c3c925924510b0000341c1c0d1000040000356280d01c002d5110750185080d09501304030200c6080203408480200381c15415180c41000141c000054141c080c200504d01030001d160240e41603201941d080000911450b00ca80e070318510104040303061740c2c09010700d404036500e8281d80c07a0048103801120b000710f94103005841001c51200c5000c01d0555002d44c4d10768594a49500e80072039015818405044684040c840329805c9400300150043ca041070351480c1e00001c0e02c8001d000c3c1c060b00d409100000a81564144010440c09683c2c81441d100c803030340c8908003ca10041901d0840f01d05015040c81c03446003240100010060000100103882a9159074041c404030b0001a410001c141c40301c11003040d4040010001400010312950203802c402541182c060845141c0744110390441d0404100c00c0f2082e4059000944030070814000c4107000c61010790111300e4801e40002c541183c2c14004e15030000c008021420703500542c0b409040795184040e041040140e401019040d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 631933282 1250 631932032 631932073
    0x150f080105092a09030105011d1803040e07030b010e0f0906060a020c09070804050d0c0c140f0a0305031914090907020f0a11130c0e09060112020c03040303110a0c180905 74
    0x1c5011b986042c0021480d000018170442080d8500c01c4480704507560214680043c0e102400110794902051200003501210100321078015506618040340d07034000f103400149034803100c0300d4841c4540d800103401103050300c80c15501c0760003400030780d202c07035490b8950f130000e81c82e21541440c16a00014040104040c0e01e6102034100d01541c40b6000703546150707600d01c108854204010310058420000800200020a10281d01d200728560191110004662400020b44011025401502d280d0000140113030a880841414801100e130b9092403503032081260701c0c45405015500450340103101c154046a10030b4000c2080208003100c0004407402c50f86245030001c124042d844005001e0307200c0e10600c42e04030543c0d0050512211071b030380c0c82e0203030111032504100591070082d1a0705e05110144078140102c400070b0005289064401e00210f0ba04c40c40c40c5001000c885000c13000032016000110302100183e00c03c00368400311440ba105038001c000380b820446009140300c04006040e0b00c6a02095403080b5841042c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 631934532 1250 631933282 631933297
    0x1e0105310812010e3d030f0b0403020606150d05090114011202030c0f010f140c0d090f050f0a0e040602040b0d09060f02162a060801150f080105092a 65
    0x680c1307512510300c60306400d151100c401c400302255032041e2510401c0c034081c401c2c038804c0c0e454000f00780c2c2e5030380d0b00c460380c2e1003484400648141015408102c2416010020540c00c01782c203444a103403100f01c0f04080003a6004544500705003641302c2010407903820094020394588500c904003540382e03580d110600310720198044801c9010f8003036502c0d1880c5503d4401c00301c00f0740c0101078494046582408008503030b070300030710210340d9501c0d00288083c5410640800c03405103503040d09e880d082403190504943c800d07000200e42c0094402c1c00503000a04843d25401c0700c4808549410103601499100c0e4508032000e802180c00404da0514080f4900200410b103030050500103001e16020020720159404210036441802c60f07084042090915100020b552000c02050a10f00b480250302a610700301204010b8681d0341c0c0c062000114000010310802c0d50180798005940d0b0181446020b800042001501101c014070502d48960307031420001d641c04980410380441d01c0300c1c030040100394a1503071280303d0302d6400c05070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 631935782 1250 631934532 631934549
    0x1e040c090305070b03040201120c02070801020316090803032e030f0b150901050319110a0621020301080d03090503090306040b2a04050d02031005091e010531081201 72
    0x20b00003104c080c039800b203e0040360184d449446c92100781c800900580071a01180c021840f40c00d0002030003c00030700c099401208004546242e0384441440188404d0715500080060341040042c003111941083d00d40e4842001403210340002d0825001c0c04240f200c0340e074006081e8101c144540d5040040805015200d2079540720016113998510041c008044401d004950300340d4040c200040d203480711b100305510b4041c0b03e0502c0d001c0808442000c6001c5000702c0e4005e50102e4503c0e58501c6841e0380408042d240a851a03030300314110361600840c0c0f592191804042001d0560351418442444000d100300c907481c00300501291200d06151600402c2403200b2903007109619440300d8100b007188044541c0014003100301c021036003030034104010003400c1f0003100422613140c42071202e1019194494003800e0f1164018102821001c0d1041c0004031040c0c495024040345a4500700400034040c8140034801b46540c10590081980c011940465501418906001d040b0085c0452001909102a40d8040c1668001c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 631937032 1250 631935782 631935793
    0x170901050412030e121303020a080703050d050c07030b182a010c15020d0209130501090c030203060108130c080f03041a030103051b0d020a03030f031505030304051e040c090305 77
    0x20ba00b1411903030543c0c00202140c10072a54500e50041c400094125411030b0600c0100903950307a070009040f00055400356080e90000d800400c1845003d010f100c0b031031011414003a00d401b062802440d100d161600009040c84626408519000020316000303a44007075000c00c0301c5c801c00c3d810318808041490780c0c0c07011404a80b80c030221400b95120300f10445100f5031050011003022036414500019400c040040c0c5212503007441151480e9440d40900540e240301c8030030015455040148807000c2d1120786a18805050040091068699006600e643d0007410780340e03103018007801403600200c0380441e927000e000c440c8200c00d140a2074000210080040312a103010094603030074038210f11107030750100b4400a03100c3d800c00c423000428040c0124804510002c001d001d4480ba181725400948860a5900203900280c040d2070524101501442004000940c413150691300d070b1310f4800040d50b68400c0b4001d15000324001800b81184900d810085052520004c0040c050800c005500070f107204981e1005984503c1003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 631938282 1250 631937032 631937063
    0x4031e0606080c03030d05340e06070f03080402010c0803011706090115060c080d0204030606030b1005090106030e0f1c080f220318030c050411040b191709010504 71
    0x50146002040900038500f046850041c0750002c14006181060340f104441c288d030780702d0000444002d86030030200c04410a24490381801481341c82526881c038001e020400c20003010400000502940b20352503d043d4045556900c0100e4043d034465000820000010001059102c540307039031204200390900894080d0360314906424280c070500c81c0243d6200136442c50500a16100b58030240c2c0c0d03a070050001919101e0241c001008a9000b80d209842240d5110020f10800c80b00d8480b2540250f0034409481d5243c2c10940050540003041c8509002d050740d0341041140310001b8072000c44030685480503070b2101c603040e00c903041c4151500045400001c0c84440050035410b04003803814018651281140300030080c24064000161502d1030540c2404000414403581c0303032817000048055440b0300d448110140c034243c140f00c00c1c1d46003040c5419160394140005d005010032042a600b02d051a103030007194685401e4415148480410581e410503c412010080e0201054108030b009a11232201555001503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 631939532 1250 631938282 631938299
    0x40314150f06122407180308180d0309090f060b19030507050a08070c0201090801021617040503030306060d02280806040506030604021306080a1112071a0a0504031e0606 74
    0x115650f421640744040e01c080b07000322013081c50281c1e00400034240030a90020700300441e00d0a184a520440f07848800007043d112610780d00d0010058204140e0705a05507440a580203040c5108500505040c59600d880d03480e6105410341264000340681d131842961500300c00c0c2990b904100c42484d920200c1d081c0404282c281d8401c400300c2e090b080740e613a03d80c0b4454991b00c0c411980c8561011080c0c0c10040c500c0d8000c5601d0400384020f01c4091080b46144260590038608109000708000703820304018800d0004011a44010045a0303100c3c1084410a42d070b0103401c90014020b008200901c00440082c1130a03000c1c1c00034029520980d20140c0d12094900e07130368101004161802101c000c1d8040d00070401143c01400c15080b51049041e40c408003183c1030380ca5800552400200800c1035442c24403812066200e030403d00303d5480d00c1200c0d140a030070920f081103c030740c000089000d50045075400004840004e10720074020395000c0c590003a81e00082c1c55010071110b81014407100143c5115107080b000284450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 631940782 1250 631939532 631939543
    0x50c030c09010e010311030a12110d020106060e060f070803070903060509076e06091c020d03050711090f07030207022101020a170408040314150f0612 66
    0x5603400c00991541e800c40c0d8504419861040346c540d05481b42804140000e0107000d412000001c0e6541e80300074150203588514605100002c480d02507916003030080c4001c6070702950300098040c06a609559070007000c0082c080511459801400d04c260200504c90b10540c440010411280101014086611203100041c0c40d14051b00c56070500c8821444440480b02d06400c031808801814002140110180e4201d5410840c684955811541c454851090042940040c1c00d00b1201c80c5101e114900380d00030b020400c64410041c0851064800f50080a600d55205803410001c42d400b420000340c0c403c1514014007950409202180d4202d1100c208000b070b81810404148500d910340102c1707031161034000c020b030000e500408084c0d81001101c400700303030906820403280900070b00000006989403801040201002d03411488105151001c60a0001090f14801070ba8140e0760010f01d0b20001c82d0505071154500400050019050380d040010851551038454001d0312030300054603007503400e40300700c604d03640c558 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 631942032 1250 631940782 631940789
    0x1b06041802030f1f0501120905011b0f0206061e030319020109060c020d02070302090a09020d0b0402010e01210f0b130b010905030a0f08090111120d1a0d030f020c0607050c030c0901 79
    0x303002e0213904000d10f600c203800f20078200301e110400065510302c82d1201429079480040c1e01c108440e41d80d039407124050707015060182c28025403015011905107040042c802e071014084900340049980c0c6422a10f41d003c1c0203c812000c02d41200121540500001070301900583d441542c6152819042c2c1c840140003117000d8007082660340c040c00300d49040d9801c0000148000c2c1592580030303551400e20340147c90700160b12141502400c1d08001514140c400181804807104180341088440440205048d50020401e1200d107003a0310003069002e04025000028041206203d51107010100030b60800002540108103141003aa00d1524103602c0e54185a504d0426407002004032061010032030103d04003001505400c03805160600001c440340c4440f916001c071054115030315240004036041540d60a103d0000055019000905013019000009022a40600001c0c0a00c0080381c6800d170840d100b07000d00080f01c54000c001c3c545a88060a005a07030310814002c95010303102d20a011502072802c02c581c01d049 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 631943282 1250 631942032 631942081
    0x120406020606010c0501150315050901061212121a0109090209030c0112020c070303051225080717091e0a0c050607061127040e1b06041802030f 63
    0x79182d84004640307a51507114140d9295595101c44e4044c00d891411000040d400350200004200788201804222131000d0407205c22030389000d808000e05241c95140c024110b800c43d000380d03090429004144c507002c04542d0601c3c442490710b50100e010840f3300200d030502ca4801c0e039030041069242c5240400b280310b11425036606601510b00341a0303c0d071003000c0d1101541c010341c40250810700101e20b100e14003806a003040380450b00c0426018401001201c1c1194030100300d0a4250329481001c28403140c071307d41640004108000b100c002070206000d450349081405400d120030f1158904516115160035203d0b026000e250045c40d036102d0300340c800140740c01c400d0f030b0000c1201020614110401200354043c0da002c0b905c00341c55082084500c0c0c800c802070810301c0350801c056106002c8901a414004912445840c03142c0d180c40800400d10100080702d10302c402c02004d208040c5c941000000d8002d00031540107117003d128803003040314001d200380c0285000d03e00a44400300359864882c0301032785402159021504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 631944532 1250 631943282 631943293
    0x5070503041b050f130618060302010210060605041a09090705180102060103020906040e15090102070312140604020c010608060c090a0608010b0d11071202070806011a070204020a020f070806060312040602 89
    0x21310314001807014001c00b042d900000d9641d42c5c89086212081581429255030b66407842c0c100b065580501070f4031904882d95404102e0b10742081006480c6014030b01a01b00c1016900400c103100c0d51042041b00c2054200414a0040345070403400280390f54000e2400d5440742d652424050071a50000580c141070b01c1d40140701710003683d14441030200800480f23020380b20512070814490040d801c00018035001d400c00c4000940c1d1a00d007403d0180c1085404418000104d140c039510043c840040c0c074100790408801c070f0700941c1d10014403a0183c05000720b6009082a8003401060065400d0500f00030071900b0410340e2201c0060360388420580f18200240301c0d48003d940b041080032100c03c4140e0280103504a8668011305100c3d50340c5a20040c0103e160b5003202581c001401486a04800c228180c01081105002c0b40110b00c0403052202c14092450003e0240b90003065600c051030017070003110743e10403040044403080c5940c5c07014103039901c4017502d0140c041d008807107440b408840004102d806035000c0340c0081c01c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 631945782 1250 631944532 631944559
    0x4020708041e030b07020d02011104050f2e0c0c0b0910050703020703080a0f0e270406060b0f03040c0e04081621090801291e0405070503041b05 63
    0x54454000d910b14840c0000c80402200040d06a8103680c01180550700812003203840240282c00c641c03201108060041d82400101710b10342d254030790140b200b00d042e620b000030b00140707491012241c03140c00c3c40d1080950b00010701140d44c903408140504014002c0304c020400c65910250025144184004960004411104100f05a0042d002840c800e0b01c01e1044a0b8019500d483d04c1780e050300000501d50014860002d28010181d02074405404000100c0d00c000982000d44a41e0007056440c011703002109880704001024030400354030440c0146440b19407290b95002031714043c141548125400c035a9030442031702c0864040481d02d09944a41d6214868519143e1441c100c4205605d84084c00c5510380d0600b0008003444c0ca4060f0a020140d520f910b40502c075a0070002d07070900396429202c0303980d03202c001c15122031500007242800b100f03d00c0054030745c003d01818000c0001800369484030703240c0c1c0007030070242801591a0301c08000c1d031090380203540740d041d00d100b824954000c0d00d655115070740d0300519201496 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 631947032 1250 631945782 631945799
    0x1060e0a05060a08130c08060c030711010b01050307110c03060426071104110715020309120f03181009080d1d2d010905010b010906020601030308011509081c0e0402070804 75
    0x40912070046d02c54022044d900c0700b0103451b2041c05c80d81110807550200512803401e4011100000c500703101c2c4020f0051041802c00200303a40001403122003000326107031490880d00018401c2940144020382070707034005d246c1400c0008805200d03004144409204158101c200c500c4102070301d031066800301e03d820701903001c0703030804c400b402c62400702caa4800010041c007400218419200074458101c00d070096100d00d0001c1c00c86091554a141c0110013860402c055029581c050088030390056215074104a00d00515054607d8540030440032210540303819203400900207944041e0100c0c6619040900c041174582181480c0c6903060300d80e00d4000d0b40624000340142d00d00c144071038882c031003446062801c16007180d03405080d07443e181800da689075940c1034081d0003560720014103000303445103000801d841c1d455541d0080c0140c105118400c070700d05035074413034081c02403003180084014020402100c100e0661030b800d205004004c02d0003617010800d10010b4400d1810140292022503400c07400c01406c15180111a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 631948282 1250 631947032 631947061
    0x903011401030b2a09010519080907051008220203030d2f070b04150f0e060a020a0203030103030806180108150a330305010204060801060807090f0303050c0f030301060e0a05060a08 79
    0x8484c11f2000500c19603012400140131140119802d80c0c1d071641c9400c0210000e0b0034684c5a400c0a40507101110207004100c4d00f01c10f2107030300040c2d905014001c501c607502c801c0c040744102160007941800f0006220300d03005810b170091140091490f1180c401d00c04451042e90761a45c05213210040f0080034030040340843c3d0180d144a41c0701d8003c4194010240b205860a000c5404803607141b8106649c0c0c4000d0010104200441035014043c1c090440c07620207040406581c9000500c0010204000e0800151150b124980704201c0c0d40511a942c15495854888080c0c840c4182c80070542c0c580c000e4000207000503c1030003130920f2a00600300c0100112400c2c02c3c620b004c01c10300220788800d40740e107001c0040010300910052000301490ba4443d143c07541031080040a40201410060800403213080500602018001c01011264182000c594428640c891207040c10010700c03c400701d5000110000035001d401000524034254101c03071340309407523456404000850245034028000208030100081d003c4022404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 631949532 1250 631948282 631948297
    0x50a05150907360204080a1106030601051c09020d030305010330030b06040302061602190e1306090f050d020d030e030a05030c040306090c0e01080606030a170903011401030b2a 77
    0x314014480003010f0880144da00c240c1c403024a0f0760181040d0b030244882071a0300d540c404000c444061039030914200091090060103496804403509200c2e48101054690040100c00d0f4042c0c140b0a4140031400d000d402031109200544a50841d00c4565610381464512944010034000700c02410a0018500f00c1c0108044030000350030410802020025942c0c54015010030160040b414020782010f205004400405031854190040320b100305200e170b400015106523200c031079584038104a5800e820800090900e021019100b071404942e00c909121010070180402d001540844002600c42c07201141100c1008503c1e101540003480101001c40c440c000a40d04140040011800d140d00c0303403180c40442d907801c202180c0d00300c00850104103807810b41e00030718010544000500344603c0d014002c0707500d900d5036043c024144c0010044850030020a9019034070f051401900070481c01d1110811b107001028203000641d020800c040000d1401070b1341a8101c14ac0d14410065120114032007144c200c09a040401d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 631950782 1250 631949532 631949609
    0x904170d0e0601090203010f1502150c070b041202071401050306190b0301080d08060f010e040b010318060504060f06030c0635061002070819080403050a05150907 71
    0x411020110300104000ba01801c0d098800503900d51401851001c03204460b80040c2125036000100d08145402080441000d81c41d00054001030355003040b0f0b01c40d1889a858010040b51000081c4401c0c4081c441d41d056800356a5001c6464803034030342c8008942d034036094421a00003101000024850304000200049096001c1e0000c80742d02e4030384103070341e109403c00d81000703403594000d40e1102e0b62164400c00e41600050103541a1103141c1c03204000803c61400ca0030154021030312880320709101d03440703a482a40041050001d4544000c01490420302a0000791416240c950030403503141d01c1c810152180b03c7c200e0f0707489114416a10310700350b02650701203a00d045241305202112001c08801105110440411841751003050b030038a0880f00704040da000e4107044108540c801d2000340480e81000640358501591594204209101c0380740042a40c0f10380d40005019004001ca0380d020050005405d41d119028000302a405030f807074800d1075a0360740082c451001e800070708568210040d81c281125a001460b0315 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 631952032 1250 631950782 631950791
    0xd0318050a1a0c0712030807030c0806150c100e0f010501090b090117240610020a08030c07050a050a03020105220f1e1a0108010c17070f0908011104140904170d 70
    0x85000150041d421710701500460b020030108800720358540b041c00d54052143c20085042d040110124011009641003a030009000040107094240100b0042e030104020001c03d02036114140303915502c8041e01a5942850b6080600106150030140071300d440528002c2c00040e6640c1c6010001d1001158404900c0040d001b00180100004070b07100011a400030035101d50680b90030281c080c842000403540310081150040b080220008800c28200d80d0410518048a5180e016030b0038141c1c100001540010310510980c030f60070341096019000302e0320504040190001e0010320706484604081c14060007401c034806600080c0000f52050b445440c440804078442400325070035030390072041c00e081c04105a13014540c0c10042160010902030046142d403d80b825034404400c111180c25a16400f9055005021070310a4404d0f00a02c100c031444010413a41001780319400040200d105154814050034022505483e0400340b1810400c401d58065940400034110240580025444035004601d0706400180c48 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 631953282 1250 631952032 631952039
    0x90402070c24140702090105010e0a18050f011d07180504021305040e210703110d09031a060303120604150602010b0306070c0503040303030203090c0d0318050a1a0c07 73
    0x19468071164114075451003401e16540724002034648800410002c3e18480104010401078032444005411140c007801c01d804d00c0d1a903400000c00c402d013141c0206002140c00b01c018811000150030040c003414860407248916601c1e6501d01411100e650070030800c01240c035010034140c500c501400c0c081000f0207070914800366202c00c006800d0760b000006000c1c008a001c041803207145014400c640f00002090024041c14442c0d403100e4848a000b411b0400310f10001040c20418180145140c03850592500d0507a00400003c2c2e81c060500301203804261280d8590003881c0e07140902c00316060b401510028015802c0030b00c9494940421180140113903045038481c840c82d00c0840004040303102901d40c0d9000490758080d880c1c00d140c13405000400001c04c02000382640350100300f010088600340ca800d460096601c0d40c580900a10307040b000404240c00c09054600c00d0f06042d0b008046030300800b00403922006455030b9004008007100b040c007401c21180d550704d0300d00001c81c507101c009144051185094401c0f4968 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 631954532 1250 631953282 631953299
    0x30901140a051b03031f0f0605160501060806010e070507032c030f101b0509060703110604110108090705012a020901030c0302030f010509061303180b0a09050103060b090402070c 78
    0x19020410f21469002209101089028a443c1d0b410703485100c8040303800524140c40220501000c0c8038036418800006181014a41c084007020303981138200c0000e2210300c0d0b4a00740c5641c2c0f418244030340c8030422420380106071500e20803000c554900b50159170f03240398a007201042408046180300c4c45a403904051028020a8a082c40150240c0c50703a0b8001c0c019401c110303c40c04043d5580100817010710040303100c01e1044560840152010710f03005448464451015107410781e035442d80d0700d159041038030403802000304210f22107c0ccc1950504080e030300c49176141c0760300b44d00750342c4e99043c0d010340350111b020340d1072290078001644414010700c1c80310600141d4441c081e80200d4080c2c0300a070010754100c11004424015401c3c10052481101030103002004946004540a5203443c00a0848203540d01c4852000c420f141c03140602c2c5112600c00c811190441c0c0d0f49014103002a8003d00e00d14010854076080010158007134030a0208076595000e006207880081010400290700c17480040340c1c09035061601044004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 631955782 1250 631954532 631954567
    0x3060a050405131527020d080304020114041401030c020a02030703110303070c08061b1201062118050c0a08070e1e160311030705090409150c030518030901140a05 71
    0xf031480c03000501125119a5203261180011601e8074110015071300e80f0060700c0b0314150607401f41d0000d41d041d407280c8440c40101d9003101c8501c80301d500b50300041008030b20480707031542e11803401070262810090b454007a43c081e6120011140081c4d03140d008041c082000c03036003210b901005d08000405503403404100b5030751070102030250313004900346501c050304010241d01c0c0d441042a0300e00b05081c5080c104511182902215041401017008020100301c0350102d10044110000c03525188640c01d00a001032031300840c0c80800001d00c00e0315a48580d000d080c0760b170b040c8a10041c064880000140c0074060901c0030f100c94546001d00380c0a844103e094185002104249150f802400b554207040c00308401010010305445d020310780400084000c0003442072060300039089505640080d1008103243c820340c18544004007150000c9025241045640b0240d281d041e8000c03071140480c652445411965540410754a0043c02c082d180411390500c103000c001c8400001404032960f803881c09a00d425615a180a241c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 631957032 1250 631955782 631955813
    0xf050c1902100e070e010f180e0a1403030a15080c5b051b0708010213030b090a020612101e0806071404290c1606020303060a05040513 59
    0x1900304500074400e4810340f201250051030040641d05180781071141048021100c076081e52516952527154030504e8105104800312aa0031080c203048400101080f180c07030f941b04480105080d4a803000708284217440e003140c078003520203450003008040d00c590301340240401c0d00403030b000041b420b032381c4501c082c5e2040c80709001c02d805022001102d400c00c080c103001c2101c00e8007140080205d0700a850410079662050507aa400303110300403d40011140203080c41d041111941019104d03500019000c210004213020090481e4802c0021180941e10808170986419407100c0080d41f020003003091030b1426400c0c030016a0440d009540b8020b6407990b54025616520300307440003017641d041041e4104039400d01402220760061950030001c9001e90314002c006164480d03401902c1003401c0003030b81540b030140d5000503078801000c48007189948040e0302c00d215558801c90003100c00525000800420300034400300580b801008003815000c01c060600713042101410b0000c01c802c80e00400542d0600200d4466099000072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 631958282 1250 631957032 631957061
    0xa0e15010f020d0807082505091216030803100801090f0b011706010506030c0d02032a12040210030b03010f0906050705040602070e1803130501030f050c190210 70
    0x18800005041c0d0224800d161040d500000a003038200c540020ba507540c0103100340381908560751015481c4403c100300360400c6041b178000e4800004295084801040e44042c01c41c1c80714003071030350356208550b07407014140c030f4680d4040144010400148104042d680100c40c0481e00286a5110b600081c212840750100340c501e80c15403802030303081c45117840700940900309220011036081c2c65034520980d54401071040f24000c80c800000130b040001140161201101039860541d940e00f401241c034a0240741c400d44c0e0300c2c80d42c015001d220b03640c1c040341000c40d040d00001403070310b80b03081c1e40d6078007000301d0000117000d50402c1c03588a040140c016a400c2c4200c5803e0398034120001041052400d01c20101e845c001c1040e4240441008140f1041e500003503c032045030803404a41d03c45580c1c40c881646990b070020b5650110f40310218420b40f8030303081d608184c01501c000381d0f41000541c824500000035554142c440c2c141c40c0c8804c20080e11000c480214000300d001303950040740c0d03003100394140c0c0d18100c03907031800105078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 631959532 1250 631958282 631958311
    0x1009080f0c0a02180903120405010b03150f10061b0809041d0f030301121412120405060919060e0723090f07092d0603020d15080316020a0e 61
    0x1180380100c2e64030000c846184c010402da151100f2030503a00e21038401d88070307803070310f091400102046800d4201c180c075964013400346c5440b2511800641601b80303040d609180741803517a00029907990803c06003142212101c2d900c0d100104130429104405000ca2207040c0d608450800104d001d0707455030700452803c0c01031303c80c442a00d440440495410007112a80c680c00681003003004001c03801c0c0d1414514a007607040760001045800002c8403c0c901002c01e400825048404140680c4a032135021031144154007542c10381e01c07151707904401d440d201c81c2030311501084801c2d000070550100f0081c1d840780361486400c804582080da100d030440d0b401c9140300004a18a0281c1244d8451035007040c0c005550800c45c803030340c0c200941c140040042d007400c2d01805040310301240004a0001203064040e0342c0458074041401d2401c083d1603003c0100a54015540501c41d2814134006080519240e030030301c03044624000c06981494041030b040c205800900b18103990201c291072022811480b06000346005691010001c030b03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 631960782 1250 631959532 631959553
    0xf060e01050f04110406120905060702030304050625301a040612080903030d0507080103030f0c121409060d050a140c0901120912020109050610081009080f0c 69
    0x100032503000702e0440c09181005000d0b50102a940142c030151030007418584070b110a90741a80004001c0200090814456402440300b00d90300031004501640c0500e082d0b8550703545001c3c541d152400c100c45c00c94240c1d6050804407020500c180c5401601540c40700701c480f0384070100400d110300008000304031340d01a41c0d10f24400d06c16038004e06c400201c0540c255405c0c8030040ca003881d40f44814403020009002c07802c001642034403d03a0705204270b0760710030120241040a030030807140c004c0141c0000d00084000c02d43e0120199151801000d80800095014002555004890b441190152041c0d10310b03209034901880200100d0380c034032000d4240c80300c0b4194002020b14202c1800307015520b2003034140290945107028005076000e400c00715481c003882824003040c008201041e20008001d414400f800c45540204041055941900440c6000b8015022100c09071284540f100c0307800654450404c80c1d6001c04030514240000d60452031a146c088d8441a007031040584c031075207481d406010a50300b240c10220101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 631962032 1250 631960782 631960789
    0x3090309150806100e06070f0c030210050408060105040207050615300c0a050a060807020c060f19050315010c080c06071107061e081504020406030c030b041a0904060f060e0105 77
    0x24452103220305d0110b08a5401c3c07400705140d40b05109000d020040c0004480040c0312601780148000e542c05040c0001007034100c04010300e241c202e402000b00ca0300070384000092a19050095a002c65004400361043d521002103114281040003100b40d0803100d0002d020144200b00c0001446007070f034020000302c45c2c2d200340c600d10b805d01042c0d1090030b20a140b503040501032031b01c960080c00309031000c509103410f2940b2803030000e030311b4a105007559a074007804c000b83d100c0308000781901a0024520201501550500d1104243e1302c0d80421501a0f4000707102580800242d13105021004115003d0101c2924050301c241e08030b07041a03001c880200c08111346280303054440c0003c010220013842185008514020442e80502c143d050181082c4104004000411488030301c2c0cd90b00003008000810455555a6030100500508007074070285010a203800310120543c100f83c050981941005106183c0c03181070981008482c0b030340034200390f501968030403800688905611410000d44400b0315030324015890134040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 631963282 1250 631962032 631962049
    0x23030c0a080d03270b0405030405030604030c05010b0312030a1d0d030e120705030703120b0d0506010f051804030c150e0a15021207050a0c02060708090406120b01050103090309150806 80
    0x284a404a200502c0c0d84180d46402600c041407039000020b17140030b48640c20164507501840c3c01140d85402100c0911003019085052401179a11840091200602c1c5030101a12059840d00c00c1c20500382c00c000103061052240c1c40280502414500210300c0c1e45141899440c3c00b4002c15a02c0200341e8034141d802c104607080211440c3d44c804c01d400307140b0385440c0303943e12622401019030040500c480500c0d07503c640b8480350403a000c04180501500d80b201035600740075641c0d800c284914032140940c0391000c98541080010100b24040c4d07034511084503140d0740e43c110f5641c07050380c00990320385920446c0514215810b004201c403400f1080c00a000452080c03d16400340042500c04d4007110b4810480e600c100c4901c1c0e0000c990000f4142004c1e0303111300c0049410381f4103a0343c3c0c000081d03012000042c0d400c10031203030b20007030040104190380c10841d00f6204d80003041c018a0440c006848e0210700b0340100890340c402c0d00a03012052080c50300540740e80e51110701c400c0210912030410f002c104c28a08004860400310f030b4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 631964532 1250 631963282 631963301
    0x121309021222050a020405060a15210b0303160615080703030807110606010e0303040b0d06090c020106050a3501020a0e0118031103031b06010906090623030c0a080d03 73
    0xba0400c002055900c82d40d4600750404024005c5440303100182c40c1d5503902002c4001811884401e943c11f0107034090003071146045100d0402c0601c0d407581d2440350252075205448002002500440c980080d9084880c11200011022940d01e51a2080e110854200d20203240080c69040001c1514a00f11701e000f50815100a20100411544008540c1105d400081080d041034080c28523810307442071140401e0561081360417044500300c0c00540d0f84000801c0d03500078401c4401403e810411035004110480c01d0342d82511980b544066442800c0c407580b00020440c007540c55181490f65503a420b00300ca003209810358604401302c180d6001c68104510740d0091894a20304000b460b1a400e140842d40c4040e4020310303035000c00380c07000e41d80c0b008060140e10100210703404102c40f010b03054583d10401202e1a40c1e804240140307002c080c02c1160020769058640600c1e0f09540c011010404807020703079232003900700710742c105035280d414802c120701281aa1107210404d4050246000980500361417648080c0680704030b00c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 631965782 1250 631964532 631964581
    0x8100504080304060213031e03021207121101150e04060f063f0506040c061404120f060c030f180206070609150c0e1206091213090212 59
    0x2000c00c00000c0800301141d0388594005401601c0b00d240c00240d1544140d0340d00018030100c400300590300407460320342c1d4084007a8032079401c545800d802500c0340070305800f0b42030004202d550342c0340c030b01d0007524015541c2c8084000050300009412000740c0d50380c00c81141560002d040701c1c103190140820700546010f59881d400c1c0000b000c0c000c132460100818900c800380074000d5207840c1901031503d076101003050100c01103060b94140c0100c2c0401030400302d03211241981c00300c038840045c440015400780910300003840701c14010002d45c105864010100032210f640e500c111100380c003880d0800002580d51080d032601002d00e40d0005400c81c1c0c169482d01c1203035415213038141454000480440103a803018111000240d020701e0105403056589455880f2212040c0f000d01090f04108144542caa400302500913284000c1301e51445109140302400c5d01e03442d0a03148442282c0003503001a41c88810a4002e20101d180321614001c91541d404581f412a0032560401420b1000e40052040400b048441c0114600740036 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 631967032 1250 631965782 631965791
    0x70b0f180d0c06240303050901020307021e031c0f031d0a0605010620032a0604030e030d030c1b020a0801020d05010f0f05011d04090227010801051b03190e070810 71
    0x195441000e0384445c407006042140014400705203174800c6c0107a40c40c00754050044e03021a4400f0034201041240815124002d01c6002d01008000111160000c0080701d0303525019998680c0b86801c402030300b0f40c605411075024020040da840e6103410000412880e00800000800c2c2d410084000c0583c41c0d41c07603080500003a030001c80010030b5408021030782c01c00c846414021288030740c500d0409448108115403520307801942d007044103058000f82c64038000102142030365000c0a81c0041074007142d208809200014403804045004204070346110704160780003c0c1580d9241ea030b900b20307450036644410401d10b082a01e800040040307800981102002d000e00003104e44105051400091162105c05170800c0544066110b000e95a140c56024418440d0054012240c0b050244015145a0310341d01c0ca200c0013a000c01d0000a080ca410b01c641c6009007641020341706c4042082010f50314980010b00040b14000360315209440310161885a0350b5200302d02e8000d00a604d181429943c14400f02c070300380300f8086050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 631968282 1250 631967032 631967081
    0x30b27090706050406080a060503010603031106060105030f0a0b010309051b010e0a0b0f0d0b0d080703200606100302271906090302211e0d020102070b0f180d0c06 71
    0xf01c0f054030103660b064608078089598000000000e1f12030b6034400c5806502c0d01e0404000d26500c64624215640c950701280c0158580c0401190944801c0703401d480d01c80e0140000ca110f00c0515002303842015014500492415000e417612400c00d02900d100e008041021220f641e019604803402a0f0380441c201e0780070400303a1824101112510580428020750b00c000a00ba00140300369a0109a1072400a400791010b2201ea1070000038a520061068012690801081c2001104150404000800d02000d80000d4581100b072120030041d411240701410380900040d01d410f0841185800e82032203660300001c080c0c0c4c9980500c16000000302104210b80035402d428000682c1020900b4100ea0b81991400c10104c2800c000300300500744003410410038003030980d61082400c0b0000d200c420f4035008605960784980c04600986c200c2c8260840240b26140000010b03a906401d80c800755072201200254500910201c06154209200710207040007246200c4120024042c03144103402d0000f000903601480680c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 631969532 1250 631968282 631968287
    0x30c080613201e01030e1606030b010c060204030b1b18010305130b0c0307080f0405070b0d060902130f0501020c031e071a120601030903020c210f1507030204180c030b27090706 77
    0x1148c0c01201c05242d110402c1401d41c1c3d200341078068506401800454a598482c40e0a105c44141513580c0d4101c000708030303c00e0000c1100b040855201c0d038405d0340b082100d02003640066000e0100100072070312a1007440d8a01d13000c94164070f4100d100700c8200300c400e9945d01c0c001002801d0404080c00c101011300c4000100b10008000081c2903055400d5013801075210000301c684000613060540198401d00d00210b02c400f140360501078104151003010404d1552b42d500c1d040120399030b541304010994158070100c5800301104104081686d0740c4a20300c05d49500580303070034110050071140b0486903c3d82c01c000a00e03440003034505041d030b90859803d00c2c0c14032010185890080d079413075981050b42d01c03030324000810601360490080300a222045843c203030b441d04c0003400c19081d21600c0c2c95140d241403584190000310a948207200716400e40d0342c241000404d584030004a41d005080c50f00d07082062581e80c8050a40a5440325030304e02486a080020300354003901515403030b03192003018050603034952203880103000d803d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 631970782 1250 631969532 631969573
    0x80106030b1029090616020906190e150901030c061d0114090409050f2a030d050d09020411030a1a01120b0a0b07080301030c080613201e01030e 63
    0x62281403d811018003009518144a8101c0c0c00b944600006a01c06400b450a950440300328001c4403038210a0756201c0174401001c9a401c28110f4055640c0b00a010310030104241da074000804151031909401c1080100704001c6c002e810540d40301090000c1048001c2d8442d009900072205850248071103010303000040c0100542032581c20301004042500d031100d44440d8000e000d001d80041c2115014003514449586a0b915441d03104009101021203103180c03902ca24107001c04d1500a0020051684030120403969500003400780c10200c0e4403000b41e0700c0565500d00501e0282c031003035540d4507602d0416100c02d00c00c494550000e10003080b4a8040300c10143e8020b24140030a030140d001c0030810300c1c60303400020f019a006800c281c1285002089001c2804062000b031810380c0d10401d00b44d40043c0c2c03108051551994106d40500b10020030300b030810005540c10f02d00c940c424948145481c00c407a00c000c0003500000304082ca1074000306002d0f00c4600790350b070700d40112658105070b5806004010140307411041c0b0b21 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 631972032 1250 631970782 631970819
    0x21606090e070807050d050c04090e061e1008060906060f010807140f0d062d0f270219120207031704080403080f0304020114030106021024080106030b10 67
    0x1c0103050003c1c00050140d4101e441580700c04401f00481d1410002e80c0005030014000d0142080c500010804110800500075004110504080d0459244950840d4100800807c4540310b00c4007503c00140302c03241003000902402c5c111001c1e040a25190050000d89025245010b040041e8034040c0b140041d007107102c0c0414080c50401d1180d44001100280b6101d104460341c084065140400004170300c82c91001a04401541d080052000780e06080c800010125500801c040070526007810011f0078084910100a45c84804105000440f001d0290003240c0080c84001c8064040002d40040c0d0b50f40500b035013031b400005003821030400c002a180200104011000c114400841c140032609100307010099900450f800301c1513940d0765206e620600c800350002d490480c0403446101c0c0020011f0310002c00e40e8103942c1940d0003001d030606140140740141512081c01032000c92100030005202099240300302c09844100c00100c0c0b080c0c46d40c036003410304c8940100500300b000424101840203000304600c40703528 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 631973282 1250 631972032 631972037
    0xa090303170114010c0512220801060513020c01090c1203090906060c0206160f1a0c07081804061502070e01050a030f1b0e040b0411030105091009030e060307021606090e07 75
    0x15170103070b1a11514101c1d030001c1405c903841020884600c00c00e590340211803519812040001087d83d18030304907090784c0b60b0b40140d035402442010f4400d201ca215a01800f25241c1c45000890603102d56110044400305c546c1094000f401e408000106060304400c6501c010450500204481e91502400421200200000a00c60440050b0f51241e0055100b100c0304181e421211b144680a110320b421880420119a40d4103841d1020300091248400300065884103030b00480502c4c6410154400c481d42c0c107050001484e8800d64402e0042481810900c4030900e20b44280c008003409070522500030a00b4405a2007244202070245d03040c00018281590013031041e601a007501e0070b480c3c080c4881c4a12260f5508190100c00c2048200020312400c644c210380224080c00040785010907030400c0c142030741c20813a00703107411303902c0205043d081d135105078071040c0e006003c0d18001c58031900030000501e85d0b80c03064072000c1c0182d102d0035030501d074000600c4024000b4880d5003040c400d03062070008010081c1d40e000307110405 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 631974532 1250 631973282 631973297
    0x190e09061005040b1603020f0a03020a03030e030c01090b060406050f030304091d011e2403080c0708100e060c0a020a0809062a0d0c0c05040e0f030a09030317011401 72
    0x500d800b500640303002d81050b0300f855407a4000300f441c640010355007200076001441400c500c41e80540c800701d00c41c140326405a000c3c0c42070750400d803019000340802c01c0c11100c0344d00c03080048041c0480c0a03c25420340781d1142220400e030f81047d404000c165103164101030703c00c04030420001410355000007107908803100c0502c003081d004552042248409421201840c00d5403c0c5480340320007401c28010740c80c0303003684400c04000c400428440e0180c1301802c0000303041d881c030001001740007140c2d501c4080d00d0702d407403c2001c503040f2586500806051525202414490b42d0f10346003031410f0641c00b4400701e54040c11a1510904183da0304200955a1010300d00c040d104120025500184d6114403040799140c0076402c4a0086078103030b000301c1c0c05400000104140700b0f4003d038000c0d0503142d84244283c20304550003011004031641008c0c10000100a6003041030103601c01d0941401c3c50440500c00343c440c003c50380d00c0c3c00d06081c2c035508026002c4403202512220700c0d80d0000c0184880d24940c5500c5003244004e00c3c000d40c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 631975782 1250 631974532 631974559
    0x709090606120507050a17060711070801150f06030203070804081e040305030310050102030406090b0f12040b10050f0603070f0e120f010f020c19081608190e0906 71
    0x2002011142c211211103030080814a082c0607000404000311003003915044030f641d554a0210030404c0b074410100180d6000b034400309407114890302121100100400a031070015940314865801c482c4900e0b2a45015001108100321100c1c0a10501e00104028281585035140c05040140911030082000b001c481d00820101280c54040300601c0038000fa007083c1c4c40e507031500c90503c039a8bc0e40044603030038074070445214086295440401602c0c00c55859460701c03038450b4104242c1054940140c034402070705610030700c4810140c0841305031250140f030080d4401100d5007000801c0031003101a0340c103c603008004400c400c18085d1150800c0300ea100c00350b440c2000001189420880328205405401517005c0e1440b40130103284100840c0400840002c58000c0000781414181c4c0c030141d00480b1344100c030701d030824011a000d4100d0324443e000801c3c4180741c0070307241140c50f01c0802d0403000d0000d4183c0f40c079040481d840d240e04201000c1c0041c800e1013400d0081c94142200005203059600404060058080315400c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 631977032 1250 631975782 631975793
    0x4030203030909040606210b240d05011b03200403080403120c020d050303090f0a05070e130c080c0906011701091e02040806040b070513050f01120c0c0221070909 71
    0x2014200b02201000c5075000590800c60b10241f182040e280955020082410709414a407454012400015010359154030740b010800742c542036880550305552240c0031580d622245101180a4066034ac40c00154149048568005225000309445131700074100800c1c00890700c600281e0f400c80b980810400b00041000404032000c904410000790005210602d890410001101840c803440d5210120b0b414800e84140326030750351841c6071019242d900710800c1800030800041c0b509070301101c902032480aa003415902d261050005a00081d000e800421210b0001d10300598076541000c0701346481c4107001200c1801444202041c42803804155039100034a00011070b21310064101c0700c0c0d03d1401c549959850300348607100c80c000c031400c50341c0e00a140c0004101d50b002c2c80903240d1140761106400c20751070903d0240145100e2120401d41804114004581000901d018810b00b0f400c0c00c0d03642c06881d24940c41072160601c0d8041d120010001100c05035030228500280f00d4088030000034004c40c160045041c0f2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 631978282 1250 631977032 631977041
    0x50432151c02040911100f051801090f0e07032a120b061303050706050f0304030c020310110c2e050c160c03120c0f02062206090317040302030309090406 67
    0xb5046410110701d9001d010998818031030001054031b0541503095003403001c542424403a24403c1c04a5010303c20040282d0300d8082ca2254510306040400103a42c0300d0401e4425100a03030b000e031000d040e80d581080300156141c00f0745500301c20100780354085212000714040c1071900c0002c49004110f00b00ca9281910000b0307400202c2d201c10041c00c1180d45082c4075000f000c0745900b9000139110340c402d10000048151040301120b070310b0354917594914256161683d0441c0c40b5005020241d81c1403081c4080b8050808080c420420b81c03800401c0c15940c1e80f440615003505000032040c010150080700740029039031100314940d8200300e184841c400075096540b544c0c603601ca03016000c4000009505017104c0ca040009800c08882035900400080c07281c01e12200d0100c0c0d001c0d5181e940107259418800103840142800c0b0040c0062103a00d0580368a0a14110b060512903070142d8040000220106810000d118403590134548a50580d030f002480c2c1401c503000701e543d07031050001250051030b80100240074044207500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 631979532 1250 631978282 631978339
    0xb010914100201060b161a0f010506163e0a09020a030f060609080709020705031917240901030816150c02010606090522050a0605043215 60
    0x5d0094442074540700207425041c40348000c4500203009600403420f00b0350403136424420241c41507118503582c24041803040c0b5801100006098250809804000a1540c10075607000d00c10000699070803081c4581001156212050300f07005005440c4203d070340c42d1030780c030764a500b62041e02c0c0001da604c4813211004c4008201465080340014500300b800b1450950059810088402103000c65140340c0e150b076110400c038413504000409503841000b001207891490722910201803040e040601d3301c03200314060500c1c95082128049080d03c03a400c000c40d25040551180a0000c000b600d403614079605541e0741c1d00103440747c43c00300106140484801010455402c8250444409010b01480200c9104201038040c0043d0700030a40854001003020601d0305014841d02c0f5044120743d4000325038040320210704006c0c000607050512803502e90001054644440c064a10030a80182010307000a060351404025040f10442c082041d03040350080c8901e07000e2091030001c0380001180d02c100c16054210362030744250290b41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 631980782 1250 631979532 631979549
    0x601180e01030c0f050105030c120c0d02030411030f0a0302100b030c10230913091103010e030d0b010801061d0a0e090303091b0604091a04050f0405010b01091410020106 74
    0x200040200440c0c001e0010072510f07504d0300c4040d0b0303e07203490065a407400100d440c1d08040701c052090741024080c030319181d80c0000c017200c03405140002c030000c6035060ba40100c40544504800e42d055042c103003020400c0309070340c0c407142d07001c0d00316044a660000d4480c508000c1e03054145407955104103243d5414040000e113298010b205840d940540c4030301070064081d4030a034800d150070f4000c0354444040400d0840703440da00c0c01400f841d01c0350001418034000786904401950305d18135810307003c40103442c24072400c80b140390000010364980211014400a840c203180500e810888150f0041210750341040c0502c3d01d04c1001c044451603a010000810000c100c40e500000d4243c1d0f40d00300380074001e90040003e500840f034500c2641c9590090800742a014010b40b0702c480d4200f03c003044100003050301940401000c1c507690405807100300e0080b000409030b50080e551036501c0756522050001b00202403003080c0f0801420308140034010f1822140480045200031018000d43c106102c18048500c00e50141c8050901003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 631982032 1250 631980782 631980809
    0x11517010b0d0516060203070b0c0c0a0203101a0a08210903071d0601170112080f070c170c1302030a1508030d0f0b10030b0316060c2306060118 63
    0x1070501c030340c4d20030010001451211a100c00418114804001c80740300740e4001c18034041b55103512042ca1015405060103401c01c0c09040c50280040c1d0b0141b0400c2e051581c030800c04241440c7e044030301e25680c60702001091107007840d210100301c25140030941c1d00c40c5800380b01861140b0320003100c00301c030f135071041041581c0e060190000c082811003941c000200c00c80580100240c1c15a01e500064031090b109140e0044040b1005004001c0f941c031442020940074410031141c0c2c1040159520a401a0005e1804640358800c2c66024032610461a08500810629000401810a450011031002e40128001060640d0000001000c02c961034104180c541030001040c501039540b04403c58a81d001103440345811402c00c05604080b1909014148074900000d012240251403254150000c0035040d03038840d094047c003000c440300d10000d804241c0c01402c29823a0b880c132030f2880c0d1600038155480c4094008000c44281000640c0700710000d40f140e40840d013030030100d00301210400d95526003c42613001800007a2413 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 631983282 1250 631982032 631982059
    0x60c030706090b010609051816020a060203010b0405010816090b21040b04061a011b051c081611190c081f1406010c15060e0a1a0102011517010b 63
    0x10f10071424101e80107651031138803040c0c031a010048004000700b100c034100c5680c0c80c08a42000c200001c0b0301d241c0300060044402e0490188d40d200d090360000da112101c902004a01003105580090005a0091990403d40c0792805800e00160000850b4001c1c4880904041042201440b6607407000402070b100601008040c5050710300a504801c08540844407242003107002070540ca0074006c4071031100c4058540c115200c001030310700346a1200791002503d00d03225581146541c0d180509103480c04407020f5482c1d0a07507107040c480405110300c200703030707000100304030448108003c40c03012805402e00300c8079140100f4000380300c1c1800008400950400c4d03896004042c407aa18508850701c0068201030805810700080002811900041c2c0c400c840c19800314031101000000201c4503102c244070f0880c2c0c04000580c0d00e4070f941d4030040c4260100c5812804d02e9640da803a503860810b18042d10b060200910003445070000d082c00030102c5400324410740c08203081d50f022800e002d41c42074000c0205d008000d01040700d030042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 631984532 1250 631983282 631983293
    0x1a040e0603010225020406090219050f0904090c0314060c04050d03181206050c04050f09040317041416150e010c02030d08060a09060608070e120a080a030b030703050c060c03070609 79
    0x400c401c101e104038904100020407408c070340243c5501d1000c40100a0300302a1051302a180799020002010003c14108008412555584500c010660007803080e101103d0551a040307041402c0104000038550000041000703079a5500115030039100c0680d46144900d019190990350540780d48103514982141c14030202c2c1104034255a40030a83c0101d00600c190344803c0328190342445940a92074022210b0000c4426a0402d00036040d0428401c0ca0f011626101005166110303840644084400354011703625259a450100000000800310080019105240c18420840b509a4055032002d00c0400080c00c10241e004004c54011944c0160645410200e01500100b00b01d00031200b2034443d0034002c501042d01e045d1072048006035070a0313440b64801c540b9003000656425039446035165110f4030b980400c070b40c080001c0c8030130030055204030545911030207a5030010b0143c0780840a118080c0e4428002080413403c0069000306500054804a40d180d84201c625070852080b203901a01180c1810340520400c10b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 631985782 1250 631984532 631984597
    0x1706090c0d06110d0f0b1513050105030c072012010b01020a03081306060f1d090a030315260f0a050a06050a060812090306010509042a05040c03020909011a040e06030102 74
    0x200120b50410140710010000d07040781c000c231804225441c41624050056500940083d5002007201c3d0340340b130605a5070707518512801b1058081c041c60f01c02007420344149042280040d640000224000d105460007000001c0d507982c01500007800700045040032944511600204203410b54119805104281e03c03104142d843c04070720f00c688181d02e0492441c00c5140058031a03200d01400c0d2a1001e0810f141036620110041c100b44c02c0e0b81c011201c0300e504e000820403001d00b1100050341403c40b40c41201c5240c2c03c07500c0d04003000680c007050b0343c1d00802c0c050b03000100046074111045500c0303c4002120f841c0c4000300001803040b90400b00700e0348035042051100b06d02c1d8130702511a0790800c50031515a41e0301e81d82802003103082518002d145a111040c00031100311142149480034010180681c10a07644000181c281c035068800400401d60006040d401c1c1d08000c0071403805088030080e00e00560040e2400680c41d88a44c0c483c1780162100c06010520315a002e40407520700525020a603079021171055072241254 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 631987032 1250 631985782 631985801
    0xc01030c110a0b31050c01032708090402030109140a0c0c1b0806041a011401080103081b030d02091801052b0804090203090d03200d0609061706090c0d06110d0f 70
    0x184141041d5034031b02e620900410101401c0050752a581c462500308500601030444400c440c05101400300c1d52150712148007450080c0031803070021903010600c41c1150034a82c03000c1c00700c004072418098240a06c2c0e42009600308035550150180c1e07100c40b0074490000d01c000c1203802001290291506010511844800180401d00d0000340c02c0d0481c3d0381d6811590b821034441078420b0202e00d40c0001080851100c07001b42c2018000c2c1d43c0d07001241182c2508035070030359210b8094240903540c00703d903010303907420034138004119100152825106941440b0000d01881e004108118504814443c503c0c0c8228508030b00750130300f652080e03507113445a48564098000c0c3d0421201c891962185c6084604020710034081d802c81e42104520172060f01e007440c060503d01c2da0000389040d44072070725200000340503192445104e0003410481a5040c803088a12596400c044000d01040101c1c1d00006040303020755a0441b01006040d8400000607050b454031810801500a01d1041d582d01c03450700c100251010fa443d00840f102 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 631988282 1250 631987032 631987043
    0x1a06150f160209151509090112030203130807090606171f0305010203070305060f040b0f10020705030307050a03020105010e0f010b0304060e06040b2d0c030c040312020c01030c110a0b31 81
    0x280e00b1000c03176002213405405441640840310b04010402142c00c0d446042c3c91501070b2040d6450080080c10107013440321560b004e001a40d12000081060b000f15104400c041c00351454a400910005507000c0070b1a00c0c0034000f64825201000010808240142c5040055604c44029526480c1403900500241012030b200d030b0041518003d09420352400c2e100300001c012004100d14100d2003000184410a44c22040d40001d501c40ea10010910340d90400c00b401d29648614010807903a0581c1c5002401e4a00c1a403050fa00c91003280140441c464981420340c0c1583c103240701d1143c4a5690381003200241221b9100c00596008441c18030003844030145c080f03440340565000f5034141003c1000400c00100c0000c44110a45007500b0110f046441c0b180e0003190041134004001e03080540740e072600030f07400030381c0865100036900103541c491341960540100f00c00030b003042c02c2c545520045c054140c0d84580029030018443ca109500103080000501c0041c03d04004680d04440900120844124040301030f003c00d882 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 631989532 1250 631988282 631988299
    0x601090c0311040302062a0a081b07060203031617040f05010b0f06070f06090c0f0617011202100c06050a0c02010f11190c08071a06150f16020915 64
    0x540d100e040300d00b2a175018000a10700840309510340780e0b00c05070440350501a1280705a10040d9070003001503000c0d89004075070b810740d5401a098011101da41103912030101d0f810600040003c141c0200c00d0725880140c100d414209039002e000110f543c80300210101c3d0f040c1035480d040c0420b200c1d4041e0425416032240d00200a007001c02c1c42081040d50001c044950301060801c240030003e0201d80d0b11f80501d40c8240000305402c00e0319500d240c0341440641102c000d0440d07601d41000381300d0b44400e04204c0b08e0302c624816451075040c0341c0c0351100c040c00d461019005480c54200c0100300e40c0300d00100441d907504903004110794100062108041c08903070314a080107608100100205d400d451003000382c070204c0cc04119180500c440041c904241041402c4c8042c4103512a042d0042100134000308461882281e08804048a48040c0f40444c20060100d070b02940d13101c24013030320410050048901d141c41d0700d1203071921180001d11206040c0c0c90360f80029048000603041c0304d401201c08190b17480b00c8508031040070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 631990782 1250 631989532 631989551
    0x30207080106060f0224280906020304120c0506070c2102071701060e010302150f030c0a08011212030e030c0f01090b010b0315100c0602190207080102070b0609090f0601090c03 77
    0x1115080c1e1126481c40d0000080b000c1f92040c050b128506003811080f40841410b040400c2003d01220001102556440d400200304010404c140412410601d40c9040681c42d40246803191076480e04002e282500f4010700c01305820178070010f81c10440004c2807624082040c8040d00500946070000b03031007082d260490003107043d0805881801400151800d50710780c0382d10b503840c503002c001b015139240e1003050043c64204202d00d80010448000c2d0b00c20a030a140c6903644080c58000100030500591041c001414582241c500084038038004016035259447d003c0b0b401003034200c100d42548200400890548604411101d00c10010340204046500450211035982e0381d50012a00d184000c4891441120021b5880348840c50202044010780e0468a0484a0007070590b56031403c07a40880c9030a1140000c1809151780103034100040c0000e881c401c4001c1d030421810b5505c03031a418002410003403045115000040705900b0410240c4250000c84007110f0407944e440765035000419a010100c0002414a11041c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 631992032 1250 631990782 631990813
    0xb160c121808030c03270306010b070c060306060f0e03010b0316090b0607051504051006140a05060c0c0409021903030522060c030509040b090106030e0f0a0f0f030207080106060f02 79
    0x454a081c4c048001c1c41c43e10101449201601000078080501c00328a0688076045440410800740a800782d41c00c0d903655181e09040c448191a07081d03100d00d04250600f03900303000f000c3d80900d8400d10610030303080074160308407841c002a000d011681011609403041e14040041c203160300441d84100d92400200300f2129001600340461840f03400809040caa10401c209074050034015003455010740900f059512080c0100c506000341e580c581d210025494002d9118030705403619842d072130000c1000701e070319601d0301d41343d0540c140d112018410614480c1d036030340c014541076445004001e04030403a840085a1025180c2c900545507801404841d420100a00399035241d10340700b41d01c550282c50039a1108003901c03045542c121207a900460803640c00540710b04140005407a03450000c0d01074500d5890104211040d202090700c2c220342c0712101e8000303030301000d00e000c0401c03000300c120360509800c50b00a85207004142030a902c0c100b41036000d500740351301c1d101001a00d0740c3e00000c10b005600c255800c3e0780c100341495003030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 631993282 1250 631992032 631992037
    0x9011407050c01060b04030f11011716090e0703020a0207080619021602150c16120206071403130f061e030b01021006090c03180b160c12180803 63
    0x45085104200082160a806000a0705920a0410010079000d4072050341e0203c1d604654408c54084d222608690100506e0100f030160316002840c01e042c00804a0004481042019005a1071268130b14040741200c2e105007161000351040d4100d0034001c0c100320000800960054544c05c0040c012220041780900d80810030318000c4000a40e0204512040c81c403d20003540b2100090001103242152100142c40e010704c00302c0a540d0b68145207884010042c05d40e0b0a2030884e501080b64000070314070610000b112038108607985501a03501580300c10041c0340c14500b12070b00200c1d50603d44000316644041d2001c85103510284d9150b156501616a40c800054a181a60038546101031141340117004426102c3d0703110140c461014412140d11f2580605084c04413401a0412160181c50f84440880189c242c003c003051010b00011131074204c2041e0b100c182c260f01d0003800c410034041040415800c0d00d8480c0c42c90803410342e04401007080c9a600410064424003444040f44550b103081a0001140390000c4207 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 631994532 1250 631993282 631993301
    0x7020a050d08070b180d020703030f020102070c0e0c1b0106150c0206090d0c05150c0c010e0904030e0402040e070804110f010f20060108030d0f0501030f0b09330901 72
    0x582e141020f0160343c0c1c01c01208001041200ca9402c4140c00c15010441080043c494031100c2d00542201030035400c00502c01207110071008256030040050700e00180300304101500700e501c074140d948500d03110200030f5840c0f44102d02e0024040c08018600300c40304a0194420701c00c6a1700c004500038200c001500940710500b90b4170020750301001c18000204a801c1c107150921583e4131800300c6981042d04e03080000c42802c030084107210100300100c0c0c41e10309000100a40d039405402401d1885201d00ca0100041010300b000300001c003040116030400144d03444c0e6405440140104090401541c50000030050031781900325000d40da01e0040c96044002c904045008410a0714107a6405650b0403a03a0f8040d41c00500b410012414124150040c81059a0600c040c42c040d05880c40034583d25190680b0707000554102c0e110007111985020010400a00c54445001c61280e200803160b070265540f9440509210400072a61544900c8a4040c50384851003520345c0130900b060f40d41255191110420340e82203134038001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 631995782 1250 631994532 631994543
    0x1150905031b0906030109060e010f0b0a030203120a0912080901030f05060a170a08070302010501062007060f02030724150f030b06210303040201090806131101020114010b07020a050d 80
    0xb014100103007801205a548204090000300e0314801d655120b000720385c0351403140c140c01e940d80c0300c0010781480c0d039000302c401d101c8089544542d001d0458000a489640c4003072641c12000000030316070445070289020000074000c0d10f1000c0880440c40c200780c445540502c0c8041c3c002450a40f4405076030005208080c05144054244000942021074140e50000e124401c02c1c141d1088060b2640001c45003801043d885100e5130010034a035150110113002d800090704115000200c207488180c1030702c0d00140000880e4404d2910200180e090401a030440c441c05c400507000854007401d818852140d00c000b840390614045c03040000e10841d0700c088030204080d0040750354a1000040800c08990140d15440c0c0001d0002c28141c1c0003c0c1120000e001d0104502c0f2800003508003108000540d80c01400140080c01c00f04043c103418039182c00018021112001c0080180082c01040d000c6039201b540809441007070720000c0724880d611356050358400d4101400480c401c200050000c2900e00303007504148902584030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 631997032 1250 631995782 631995823
    0x3090f0603021c05100e09030d02030109020d0e19030806210610050a030b060d0c0b04080a11060910081906061e230f070b0a0507200c120c04050115090503 68
    0x7012030786d59650141224a02e03210034000015441d00510065000f0306800341d00503a03446800407800c0544130300d4441644a6004504004d0520321101c42208015915252200b81c51b0707154000540744100e50340c080070031861411704442030100000740c814014400e00c800700441d1507990082180010700e80c000240304c40c2554010642909281c00070024451081040144141c1c8410802e0071a8121794410049680105089024000c0c02c414902c1c1040040c0d030301a01d4103940801041d241c070411a041c2c000c1007100f0000800390a40c1070120090b40c0b64600f018020159900c1000301b15102c0542420341d19075000004500a40c050311001d4801424185a60141301c00c504001d007646c0c000d0400d042000c10108401000100c1c00200d0302c0c070035800801c0008107410074a20082c03415421041c0d441040300d10010815800030009603e403040c150845521010010b40c0310b20900702400084c00e250410306003400824084221700408a1000f1703242d80700f580e103a50351010545d1f01c4580c4022810301b181c42 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 631998282 1250 631997032 631997039
    0x2030d051f0902090328061107020603010620100902090610090b0f090928050106080c0d091b030b100b0a261f170c010c03090f0603021c0510 62
    0x942e0003a090000004041e50f090008000324080c0c00c1420103100410070710307004110746c1008810703c0380800940311400041c0c1410b00e00c0d4041a500e1206000380000c4c000c1c0194189145450f55440d4107920b000d800541d4001c10094915001900540030228801d4414100003040c60428003141041c2d241c07159138201060340b62130300e100d80c00e6001080c08800004108483c2d005911a20103044c00340c41c11594408410a14a030002c0c04c0c10701310b002c0d10f000c0c1400e000040005a03402405030743c01c0154241081d80e54040c503a00303c001400c01c1840108080c01206c417266102c0b02c018160b90031030340141e40d40001076170780560001118150b80554400e0010a101c0c41964a11482c04107d1406201800a51156841c1c41010800c8003c07100307051010079050403000b4045001c4940401040c5081c10030411000081f0b0041c2c5807200c02900c01d0400c0004800340c01894889c418080040024240c0e0a110a449000040c041c2d0f00a106040c00d25000020b05002040c40f4800e03180f2034150320701c43c0d0241c03905 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 631999532 1250 631998282 631998299
    0x302090901060e12070806070f020c010206040b0a09050a05010608013e070615030510060b03040605100e09060406050f04051906110a0504150c0c0b09040f020a02030d051f 75
    0x404051680007254043c2c4904801c03400c201d807174080c00c1104010075145c078162038010000c2110764031000454101400d11826079800152954105510003941d0016544004280004040581000d043d5106c0c0040740c07024402c048d0300507404d88403540e0091045010040d088800c03d001c0203e0101d0358502002c02c00d00780489501c3d6444c41d10a607103200c5190a1007a03d800007914002031a0618210b061181041081400c07c220b1130251300c0002c05001d001d00d003a00c1032425020090002c0c2c803054542c4c00243c1c1d01c8120001c000d000e0302d00e1402020041c2024202c0a82c1c54a0440d4112030081c6401e001c190912030075082c00d481154004000c240c5005100c084a080100346201115419212140c03e4210f042541c050301013584540c0c1d40d0386e02c540c035003075503001c000648290344002c0c0062480c3d11004641500750f0300d000d80381c40004980d03a590104004c14020070030310300e500001510100740f460701c0a9000c40100011500c80c0800d02c0715488040c1507149036103408015544010484108000d00f0a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 632000782 1250 631999532 631999547
    0x60806100302211f061e1107030506010b041a0f0f0c010920090f06010c1209030206042c010e0612070815010f1a16060914010f0b01030209090106 64
    0x80082ea000c411521900300f001031070506807400302c41400001c07440c0d91800010280000100b0b058545105130720a03400700809040c60501d503105c10400d0300d1034111a0720300e04001c210011076001048620319a95058000ea80e1b8005016204481d103c1e00540400403440100b070720007000d000d54000b464407144118105450f4040940b0380d8844d500c42c4c0d00380700811695154802540c80407000c0d200114200c004004409100600d80100c80c5c11200601109076400382642c200954001d9041c4880d202d103410607518a401688001e40c41704000030301240013600100500143e244035003072180c034480442c0c040d1284400074061002c205060000040c2a40b4181500345000f03000308065035900c83d20759079001e003010900c0030101d46408100004104408105182500410004101c0d00148885550b01d6465100e038202107903069400321500d2061000742d90010a030194003406811044226072aa64040c1010202c2080c0061501e07401c3d00455000c0d00072210510350050540440e40c1c00e004d015100c0d0b8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 632002032 1250 632000782 632000797
    0x3070e090706030c120209040b0a0932060d0f06060602010b0117040314030c090607140c01020604080d05370c0201020a080c030c041707030b06060408030d0b040e010f02070c060806100302 82
    0x1270b200c5003c64910380765403840d440a4080008007041e14852000d0142c40c4000b0000001040e50ba072131520314448502a2078a90442d03c212a207110401da00d081c815a42ca428680c00b80c200b61800c1000104035405500c8101020001e0301c03040080340c80e62810302c0200f002150007401141810b10580b83c5901090000c40c0d0107044d51207800e01309800c03600811096002078408440c907400390315100000344c10400501c1d170245408d100500e0701e854180d4034803a80b4000c1c6100c2e00c1400d910344001c03c0e0b04100c554140e41d00044a041d90052405110340d01e040e80c800740e1942400d00d1481c010154100d40e1041c02124044075040d201c2a0707958581e00c40e00d100750740c00202054074204051101240f00e01c00190001344410003000103241c00d9082d41003813409ca030700c040c00b00391258504000c1000030360800700580320080c070b034508009540f802d944c0c0480d010b4504400a000320f0351a00e48003202102003a07001d4503840f13010b01c10041d07241e0386408090303072403502c1980e40e035030b0103114110000c00440c865002030580 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 632003282 1250 632002032 632002039
    0x240504180906020409110d0e010902030d0c0302032b0c02060928060507080a06140d021011070f08151003120e09010f06081308040911040503070e090706030c120209 72
    0x5140d600c001c045d080b0741160795400f02e111000070300760040d03c030380f030003405035070a4008001c00086205a0000b80e0310780c15104082c051000c8104484e0500d8000e00943c4c84685400341c480302405408410305502916810003541e20710702d0702600964203840040d002c1e1183c407403030005002d5801c03440c40003a01f402c5003221501507200400d1104000802070b002d104d010301c400741c842d070f4000d081c012880402e80e840ca0308461040e07040c0c1544c00880360749150350784002e0380d0182c40c0c40154988844044601107a0703080848414801e40100040040307400078030303604503010441500c400751031184001101200607103207240c891070914001c0c00403528000c0c002c14043c1d007a00784440049500400308401400980c0000000c020740242080b007250071090f49503100c10303c20990021411903075540103043c0101e0080da0308035580c0c1d2441c61503041070182110050000101190b003c1c1d44c0d180b08045c0a994102c45144082c0100744000407054004d00800800c03c1c2a9101e24150440580301c3c1c900075000185d60590 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 632004532 1250 632003282 632003287
    0x2010f09030e19090f0204031406090c040b03010905010c0806040b0a0806160216030c2414031305060a020703020f15150112021603030b060403080d02030c1324050418090602 76
    0x1803c0c4e800e481083c5544c21001d030090303100e5155050603070340c0307011a240c01c58060308900100580c42c680401d404800c21800c641c00562200d407200031030f00600c0c00d000c0c010300ca0340c6080603440c000ca411074a035601c9614101da0600980701c0540c00c1c0044103000340326084840e400f1401284031a04240e0304071941900b00d204440d955000e402d00c00a000440e640143c030181d039a02804d000300001d110089580e01d00c101e401440c01030100c0c04c014000c15444608041001000c00441c020111071390030700a61030303044001c0f80c0c070740e00746900da81000b58007000049000d842503110002c1d801502194030080c40030694500170807030350360700c010700002d15506410728100020a1140380130162580f014251030101900b04528440e000e16014046074003817001036101d20000d010400004400508803101c2805621003d610b81c0c81d2443c440045003e81c0d4890b0800e480d4040020403600303590300c2800602c80280f000c48078240200235007621284600c6c02044949104c021820780c1c640d0b007540200d03003030b540f00358001032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 632005782 1250 632004532 632004539
    0xf220b0903090910030314040501050a1409041d010b0109080d08150a09090303050c16061503020d05030a0f080f07110c030715021b24040519050102010f09030e19 71
    0x6000d030108860001d0070138070703103030b0184281365101c00a0720a0328400c42c0882e10349814100042c026000b140d0070f25040008074040c49030041e81860a40b00c592402178024040d940c1c090a410380a0369203081e661880350b04c0c0c1100440c2542c82050a181103501c070700d000c0d210300810030804550500c0014280328440d080d44010740829120005003030000d200410b0300241c0b000c4149030080070f450003d0003455083ea800e2110300e0010541c010451016940200300103108000c174111180040d1159002961241824040e0410300c600030000308401850355030b4003400145103241c140c0c0e1000c001c1d03540342d450440c0c041c0003c202d613020300050022506075000b101d10740b01c0c506001074640190381c1c10079500300039445901e081341901085a607944d80d541489a1620f051003001150300706005504031310044140000c2c40070500c8541048030080c1070060040450005905042e03107040143c0c2c0f040ea8010340c6400d6017425120b03023500c1440415a803540e640c040d42c2c120441000440d02c408940706480401a01002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 632007032 1250 632005782 632005789
    0x2010e1203041208180703030c03030c09030b180705030a24090c092a05130527060112140105010f17010314010f06030f05120a091a0415080f220b090309 67
    0x258401d076030754200d400b82d0f8600201900e5034030b80423305101500f00700b070000a241c1d20000e070384900c0b030445649814241000c110f29001a80d03000d03a40500948040005009001070100d04210008104c0c041c03100101030b14108aa0003074102411907614402d00780000d0078240c100a02d100011030801e4102c032507003032100700d413908003002d60030114074006001c0920f00c10050075207008101c00c840b0424403080501d8000c40310100da0680c02c0008d411500080c2090380100c034054032000548208002c403809100440004510078054140402e06d0005492001031240401410a41500c80306500b0340c0d2956841d608500f240c404003000b107540780c146a00d0300c01036070b100d1400198082c100005c0b0b107291320b0820a003014464640ba200100d0b0411131040d86641200b5a8401c907a0202c3c103248810900b40d18102d814040e80d0001210001503070213403d103241e0301c0f1060720b00440341e4185040403512030402c00d40b40c0c000c0386071880810341148020300f000320b481e01e074010f41d0007140d00b400e491401140d075000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 632008282 1250 632007032 632007043
    0x160e01261231050f0d030c020907031103010b0a1e020a02010f1b0503040f09050f0106083402100b010c0b180a080a0206100e0c031308040602010e120304120818 70
    0x10080390b925410811641c6403c2c16610000d081c10b4844208218494800401e020311651010b4054500b4001007000315200f0b52100410201c80d0224540301d503141d0402682c01d40c04002e401000070440814500702d5840c00c03021030103600c1c0980043c83d0700300d1107074015120888a03003044000d1000720180131a0741905000b5a001c4cca00c0384000d181c1d1582030182070300b5030f1141e5421003201c903072804c000c109890302051100c41c1501c0b081e0a0924007a43c2e0343c0764042c17141d00c160600b03850b6000b02d0310088106c0d043d4509005407166098003952101d84042d58900100c602c1303a1061400609011104004121114002030300141c401420000e08841035004501d00083c0107406c845003e0006080e110b40395051100c1508000c0c00100c00c0e50b110325001c00c0c0d0044940c081e20461011034004080703410985101452500340b82c0c060045503c450340d030b80e4080d0007000388012a60542c0109034810540b1013008007102c1c07196911800042c1001e0f403110701100c121740c0c020200225004510300707120f00d50208000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 632009532 1250 632008282 632008357
    0x612060509070c03030615230f0a0e0405090f1c0302090d1a0f040b0c0a05070b090714040603080a0806010203070c030c0315091106030702160e012612 66
    0x503450002c1c903184c03030010110780d26584110b1401704420b00040c82c03958042030400601c541e14031824040c00200d41885c07094810640358101d0306900065003084a41c00c280354054801084604004a6584c112296142e180288210b80941c0080301e00c10381919030b0312002c4d503d100c0180b60060070604000049003c1c0d240b00c0d40b00b640d41c0032460b080000d602000000d280d5029015988078850340c2040d0b1344600084d040903014003480e53340440c0600c0414803960641302000c0c0c003d141000503003071451140b5110300b0319004040700100640000381281c20140a031000b1294444083d41c54100da201c0300f11100c0d0b41c0509081e045001c20007499010500501000c009140142c850b051304500d1442d003120417005400c02c803c40c0c1801c00d05420085240ca00726410b2461058551560743e507140d800407410495245000f140c40c4003401000f04002d2618181d0386d0580e80320350482d1058048440440b4450103410300b110319564001d0359012820150311028145c091162001c41c80100741641942460615204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 632010782 1250 632009532 632009537
    0x100b0c0f070f060f120f0911010806040c0206040605060d02090406060f060e060a0c02151204140102042304021b060402040606050306061602180414070509060604061206050907 77
    0xa010344421681442903a00400300320b90000c0c611442c105000d030102c4091092a0180302c0c80d00181d214a699517041142c00301c0007a9401c1250b50403620340416201c00601901e4001010900024590f003418452074503581090340003401241e0721036031110050a8003c0030150400340502d8404010303290440700303e01413885034201080a40c100740000501c003a09501540130440840d46403012612200c0c01ca07682b0640b40e04d411f102c0409680081150000a600c001c07403030039400244e1540b4428480c80450169101d12491100101001c4015090f8091405200c000601204180c82600402c59205842c40006003026040c0440000403983c2c09581012034032058010004001c1140b80038880c00c0068802c906101d4154244900840d4040c050001b80221040e170703441b98036055550380d44142132000191040304440786020724040c44071030311501d80d0f610644980300001c41c151600032032031489803001405039400c0502d030003030441b04014044036840c0055550030021405031240b10690b8412103254 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 632012032 1250 632010782 632010793
    0x80c0a0506011d16030f0b10090810020405090f130b040b070f080108030d0c11010203391e0702100504080d0806090606130909060b040608031c0203100b0c 68
    0x1150040c00326500f503a204880d010700300c100b00f04100c40d03040c01000c43d6483c0c40e0014000101844181c0140444e1041c1984070140034030b4036000985c85181c01e800c1c2c03103089064500c0c5010310600a03040e40900d001389a0301c00e40300c2c800a0742d40c054804c5416480f422140d4002c2c1c91043c01d490b04103080c4000c0e10259500c1514108105980c0d4110070804100c03a803915080c2e03ca50b15044c0301f10380703d0140c900550700e650385510b40080341314810780c141c90280c101400219902c0c02d20b0032000c00300e011205441031100040c00b107000c0142e0b0940d540441501d08009840740340ca071415070320589070800000048460031082c04004e0158564010b00d105503403c98440ca40d8803400d021038a4941200340d0011010080703804204802c50310b0b5a0f140c80d0300540c01380d4699407550035510141c54094059040444118a415111310a0040980110342440001c0d03404000c000d460f01d504540b60710030304080202c00c00c0c1c000c80050622400394000e6a10040c0894486291910340882991680c480c0890a0171039104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 632013282 1250 632012032 632012039
    0xa170909060609012309062113080301030204020a031e05060108132301020f030906100b07111203090d0506090c0f0109090f11370c0609080c0a050601 66
    0x64800d50004030440b000c9080c000a440024400121a15501000404c0102001d02c1c0c20842c800d46026640052030152114282c440107000c0c0304402410480701d580c0c0c40f0100b92000d003145a034500303085e00118014a1a800d40d001d002c042d42c0503540b29420140d0301c000c4032403004010025104900c200760004541070900200040c085140a42520b0502c2c0b82042c145000a1070240403000000b8840300130065207107064541d500901840c80040f5040c11700208020181e40d0204400384205200a10f0b116215128241e8070058020b0880c000c0090584c4610035069183c103901072a1020b884500b102c3c0703011543c001143d6008807100d41114594400c805100c0c0caa0401c0c081c49a0129040e2540707000300300c1e0301c03000030411582c1c2d1040c40f4101d5901c200e010160303040c0390001e29400996030a030303541d200355401500c80c0c54070707a44800f8008a40e041e68010b0f42d80451901c0d08580c100b540e5180400000d041e1555001080d480034119403140040110728900141031180c40b040d05d0013500030303206543c0b5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 632014388 1106 632013282 632013289
    0x616021309021f090b0406090611010605031903030605030c09060118120b070315140f030307020a090504050607140319090b04080c1510030f050a1709 66
    0x1c0b00440080e54400d0f05a100c0c2880815030b0740c0301003056803004807803004c0c05680200c40003d5605c10307040000d00c0c85440180307105540b44000203031135503132840000c9ca480e41c030300c2c824051031900c800d640741810303003500c20000140320507405002d0340c04200740000c4030510018103043c18403c00d0304298500d5412038030660060202007444a198003064103080b100c902d402c4519200103030611040c052100900840e400484e04440d9a14600d243c56008000c908000001003c0d0144414000030026982e00da6458000703000f1020f0001c1c50781070900700a400e016004200009004803a8541028240c15204680e449600042c0c040310502d2030b2054140605090640900750700b08120030b00090100c1e0300300400940740500c4c102c411842028180300f00030141150284103049000a0800110780c0e6014a0802244980c1c1600d898081a9031007500d1300d01000303242821a5030100c1d80300403904 = true := by decide +kernel

theorem cover : BRFrame.Cov 631834532 632014388 := by
  have h0 := BRFrame.cov_init 631834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 631834532 ≤ n) (h2 : n < 632014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
