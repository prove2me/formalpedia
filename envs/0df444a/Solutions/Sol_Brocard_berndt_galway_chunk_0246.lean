-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0246
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:43:05.557207+00:00
-- url     : https://prove2.me/submissions/2bff69ec-a0cb-4631-9248-f45a617f379c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 44064752 ≤ n < 44244608 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 44066002 1250 44064752 44064773
    0x906120b03030a0c1e052113030312050f01030c090207031403090304080f0309010906030b01020c030a0b011a0c0715110115140618090a02040f030b07090f0303050d0522 74
    0x10740d01d002c04070ba80740c0c984011705400c400816410900030405580100080c079800d8600e948a1a220f490400c4084c01074050704846a00171030081d2250040185480c00c0081580c8004100c080b18009250051001484820f40d500984000c0d44005031500218074003a206032400c50510121940c02208002d40310000200410076900c04100b580e81c1c0c121203000d100d64901800046c0c1d404070360b01c2003040c0f00540c801d40c81981c08440c1407044032001154100402d06184d40924180d501201c10350040c0260390b500340c01c03004200c4c125a10305141040c0c03248100d032240c4840c0141840c16031042040340e4000d00c6102100070003c507200007005403404c1070b42d042418034414032802d282c1c00c07038009109401d40380403000d5510a160b40a4010481c0119008101010000070f200e40c1030389600380000f01d4443c1c80c900c2d800d006140300306200744080c01c203005c1c0a00820300c65844030702c01c400508421310000751f100303098610442d1510790200f0325840348a159101010108500700310034031036510308024030442541 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 44067252 1250 44066002 44066027
    0x6100f0e03060103380a180f1b06020705061818010b030f01232e120506150708031b0a0e010e031c08060303070803070207090612030906120b03030a 65
    0x341d1040c1d0b0301e9005c100b10b4400710500c2080b6103010702d800240c0c50882c0ea401c076076582c841c4003c005042040c1aa914483c00081e03030b17000c3c1c40d5142e80c0c4658083c81000d00744500060512800200b07601460800010014802c0070040c188050408512003036580319850803001008234140b10b00050740c2c58640c002c916420031104040c01c0b20700c2c00700000f5038011808410b5a00301c0070f1b4109201b05903240c8140440d4a1303080c24903024804518507050176040c17009003804041c030701a40e201ca0903881031124a201b6a403015140d180310b01407620315050410728803800ca9440036408501070ba140d60300c041d1204400341d01c0701d4010b014032500090075002c00d6480540c04032400b20980f5003507da0f038002401c2c513030ba41d036600910010807a40000e581004500404001d50302c080002c0490f031400d0544c0c0d0b030b580d60b0760700160781c08409a80710080c00c1c000c64485009172401f42c407400e9480d80116840c1d84009181040e01d108030414040c0c500c040d0100f203100750300304031961040541102e9480380310741401000c0045041d07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 44068502 1250 44067252 44067293
    0x20f0409091b051c0b091f060f05030d0c031101020d1a130b0609060f090301090302060106090b03100e040203100908090103060518010b030c12010324020306100f0e03060103 76
    0x2502041a20707103518080e540000c20b1920ba05501c106540e43e05c01000c0c05007885000b40701e5686484004e40b0700998050a8603201540031031020700e00480f0344102101500b01c14030a410003605241610351020840955607014907103d4000402c000030140244504200640400c0c10f0110400354860811082040c0202c181d030100400484500c140d0102c604601e1007a900006c20407a01c00185884400340c1800844d2107041c03454054000c0c002400c45040e1141103001d070b0000c0e4010094a43c00c0380c2e03020000c201500d456403031441d00318a5501c1c28951030080b02d003c801c0000105003075407800c100c901c1d44040001820402c100e2107080210968000d200c419000906214001c02c041c2000030085072045081c0100340526420708443c4052908002c04514152a041c4404488042001c820b203000314010300640100c058040d8426850b80105401001d83c58010001c0c4100c0b615500b20269104500d89060980d8000c03400003115480440010a07901d44206800403003442200a00702c1010b000c0e04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 44069752 1250 44068502 44068553
    0x30b070503070f110111030406090302010c080c04230301021305030d090f050409030309120905030105060607020108040201120f02040b1803070303080a15050a080309041d0d03020f040909 82
    0x148003198a4402110650b000495010400c00c045000d51482005160760800205c5e034000d41e10015242c0340c01c100d80580b080fa4460019805054086c45041c55480851031b080b5000d103450343c022036592003284500c8442a141c0054051014000610b2031050f800050003503688011062034100380214900400340309005030180c48008501510304501141e8a69044400d10ba140008101c0200840e0b0000d5043c1611010702a00154580b00440c203001d026803030300002c01d4104024182120001005107020704420040e41c0b01507a005241d8680c403603424680701c031045614503208409016403a000b0380c01e850001c03a01044224010f40a082c00711100320104551031080410103603186418800900401ca001300810076140c00c6400030045612004c0520007040c0d50340c8003284d402e110315444090203800c0440d480c8468645801980000b54001c0c0700300f8844020030f02500d032580c80d0b1103c04014960f000031804d0000c0c19030303003e507401841030050400c90300c142c46c00c082031071818030300011450815030b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 44071002 1250 44069752 44069761
    0x2090904061d0c0328060903051908010e0f070e06040906050909070311010f020111030a050103110307030308150102010b0d0b0117061b18030706030b0f03030f0a030c0c050706030501030b 82
    0x103920f60710050f0003802060700440074190070710104480151025040645c0280c24041403843c006e5405092081da9502d40d6503c40003000254602e05200e980100402e00c001048040c40d06031010307411210340d40c4045207980b10076078265000d43c00300100790340040000ca80002c01007029400042291300503918032540780e0321402010744030015808018084401200703040469441801c2c90003014071103000004084e41d032a841441c0d40c1e04211160859103407114018810081014501c3c00d802c081039000f0312002d4290f540240030860020549070401100044550840e0700c02d402950314900007410540c4c0d000d60300d00b0180c08803c0c0900900c3c4004019644402009800281c0e461091070711404031740c2c1510b031388244884036030f1000d22906a1415401c1410401c2d0ba42800042c00920403620006a00e00020050091018503468064880d4200b480210a282541d0007110206240391a00040a000801043d50720300e9003002c01030280c3c401d0b020086507451309540105e050340d001c0d64441c1c58584d00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 44072252 1250 44071002 44071061
    0x1005060603040303110f0c030d0b03010c08040b06041508030301061e090e041401050a050a0b040b0108060f0406081506030610051c0c0504020a020a120e1806040209090406 75
    0x4261911500000204005000b080c03081d4400061200c01c100a82d280c410700d90360001603a08400c5a80d0312980002555841d002c0c03151245c031051000aa00078000c55a144c400030b8018500100060680203003440002c84555036030b0b102c0c80c240c0070b40103032a10820751603030b008603500e4109001da0b00116000f0740f10710021f0400301008001921041c2e55a50301d05052552101e50880c1c050002c480c00c0001d00080b9036036071020300031140710390194400002e1a00c0c1c10400101600c030121201c0340903d1800c400b010325640e0120459500807400c3e5001110500c086000c5002048194003201550152114031400c2004030100e0900468040b0103c61103070705d031058100c500344128801c00d42d0082c141c1c0701e040c9000400d0a01002045c3c01403c0702d9007020382e214081400d0380d002001d9240180c01102406d0100188000f0038030184040b860503c000030494808a4910a800c0c00c0b44a41412b0800001d4492b60b90750f0100c401c0c00340e01920396506d40c00c00d031034035a015006800c1445601c14039255078680d0050f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 44073502 1250 44072252 44072261
    0xc010506060f0301030f1e050105090d1d010809070509040f060501150c111801121a0702060112080d061d151c0302070305030a0908060a090302030706020307021501140310 75
    0xb69440c212881c0da443c560b29502c020300d414104a441d0b204c0034900b40700a503c0d0551801c6200c0c0580c0011590349000d814030b0341400c103044070510034400c60001114090300c0194820048800a082c0b40e4825100e44024901e026082d074882039220240c5020001006030750554070380031f1841350009001e86c0c2d0f00c503504a070344500803032007481c005201c0800c0c0c90046400c0c00c442a03d00d000c003601d4281510031801c60034030741c1602600151641c49118854104000c5a25100010004030712030886140c140030b00b0003929400e040c800c80e0b0f030002208a404c000c3c0145802146e1615500210811000e5038030098151145a120b0003074510250b070400045800340a000e44070a4000010141901c1c440c11030819014103803062010f0f030851003840c1001c00010320410041801982903294003810034940010b17a403400030005e00005055092450f00070003c0c0c1c000041e10781c40c940c003020158a13590b941400700d1170998000c202783c1164180c10000100300e1151480c50040c0340042e815500c0246002940ea4280d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 44074752 1250 44073502 44073517
    0x80907081c1106010e0106020f0105010e07050703140406020c010f0806180a0207060207050604020f030d0203090d060b1c0b0105010311190c02060a030b030d09030b0406110903010903050c01050606 86
    0x81d046a1180c9901410342822000300900d035050441c540c040804016203010002d82141100601032401848200d0b01007180002414540f0700074001907041a80354065540c2c0907010009100011500404041c081c4088060110030040303100d413100d5559900954070760030884070030b0101744480c031500007085c030070303a1414405c400c040c1c074410440007045942075100d4801003031441965428000000040d40b14001000c4441c00b840040041341081e0041090045805412521079485607008011040c0c01006550110340c0c1202d032610703401c0d51811b0540160255210300d0781d000b0038525640348a41200c2c0c0e144079105014100f946514ae0301c8800544c21104c13088000d102a20f010701242030b82c4240c5004d40700c082e01d402e00c1e0a4001c00816800314446401000041010a8807490b201c211070504200c1182031546929090001614648500040100160000d01851f0315032803101e0008c800801101c0034040b01600821034214607080050158000704800410355080802240d21440c02d502135800e40d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 44076002 1250 44074752 44074769
    0x90501140a0f050903120301051503010305060415090215030901050108030f0d020f070f0b040b0901090809010806030a0507060908060a05062d06030a0e010c08040b0115020f100c080907 81
    0x620a80761000d0300ca40144200705401c00c50200840345058805100d120382c158a410012034995042c0300410402e6403503240d0b03001c11004203000400110394005241c035009070308010030552800c0000c0d4218060021560040d40140d0030280c8002c00070003182c000c0d841214a10000c000070b0b626403c80c540c41b485043c1200d101c1030000c2c0700926400d04176a00900c1c8900168614a2518095542c1c401c140b04410714280d6690809100300310610071503001321a8001c480200800c040c07185a541d000980c040d80d8402030410015800040903501c040104545142e0080125020196a4a0b0081c40f000e014094100d09002d03890210f07e80c01c03aa0b015960068800034a41505070700002c0540f0790401400c554803018040301ca102691030b85070000118050701d0616408109001008d00071801c2d0f070f400000c14410403200008100105003881e072054195501119003002041022074100d1030b000407801035074860b0145001801010f40560300400d41d10f140d136220304000e5a145604c041d250034041c418001c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 44077252 1250 44076002 44076007
    0x3090305011d0d05090109080f010c090b130314033106020109020904021005040b0f04090501050306060d0b060f04050a0504020a0501020d0c0305091c0506060a090b0a090b030316050d09050114 84
    0x407018013400190646080c103141004c400780d688c1560340c0c40d00c40c5940410391265500c80d103c1d00c501d580302c580d800151000c1041d071403800e04140d00c0217400084922010307100082c56140458500d1060080b140c52100d44901c440400080c5105510001560080d40c2d20b120300b140d400041c89030040c054940140c1d0010180071556840707400717010242280c1519601040001c00021502803c401c0190450000311000c541e01c490422808070304441040e00414070a5000c0010051655181000d203655154084401d200a4445501244000c45c044900c9644282040204030410003182e00241c2305500884190400c65594001a42c540c0e8072210010000f0300c031144c0c0d20011a00440013080c6620001d001210f03c4051614800030380070b0404811500d0750003600a2160a2900c421508013400c001042001109a6000040c0100c2680e1041d01c2d400d68a0300d5405d0745647c0d040c420b580e641900103200341c500c1c10031461b107251103808000140c0c012425004010446520804040120010a0b42082d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 44078502 1250 44077252 44077273
    0xc1b0103151409060315090c030d110c0f0411040603020d0f09050d1821060608060618090a0c030c06030c030b0f0f12010204060215090d0207060f090305010903090305011d 75
    0x3c0c1500100b9154140c4a021000c118910000c003242d4864030328000078002600e13001080604059241c8807010401062210300f62100750089005108107808403840d03140c400f641c8000c2005800070020100340404040390000324285c2503001408004541c820412078654100a101d0031035181c0c01020740382c0da11a100300c0e070020740110904080800c030360040c41d505955555010040d1004600c22004042c8641c10000030000709000754000b034038003a0058440351070914045550b1038500ba14500004100c1400b084110006016850040390000d40001940303881e0308040b54040300342d100350b0700002d280252103040c41d4441c0c843c015002c000148106010200c1600b003024000c01118041d03400483c000c02d580319290248002c00042c441c2d078015064a400900f004425204028140b2609421031880300b50358940c0812800103450781030400064031360381410222802d44d0a030300010b150f58179010707080c030500d43c01003902c40440b84502d000f8400c03450802d40314000300000e41c010001c0e0350300500204 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 44079752 1250 44078502 44078509
    0x8040e0406020c010204090b03010506040603030203090d14070b07050d03090b060d02130e010c0f0e0907030e07150302040302131e050c0d1416050c0c04090303020c1b01031514 77
    0xe4026001d03500160030440c84405690032640300382c1c410700c000e0f40c4d641d0a0000030f0800f030140c03680c01401124204400d03440c40e10b02a44030721640300c0d20f521031582e0103002403c00c1001c0283c02c88140f2141e0465180644840e039200030350f8000c1c103007510540b2407403d40c241d65178401d000b80000d40d6030000c203240b9551202c800740000441401400c80e03002050301c5140e81190030610070071035034152850002c0359055161202400c03452252500d0f4040086503591200242c076104801a00008146400200c043c140780303442d41000265041024100e000315800c00116a040c1c01601c01c0d680200c41d0741c0da80001043c80c0e5000c50364140c8500d038044402c20444000c0e4032032a409640d12502c4c0c103044d035103403103411081c0d5801c60781c184455840814403130051092030318900c1090020000d00b801c0192902c5174004000c2e41d40d6140040310b511554461030500c0030548a901034030050000b0310b08562032013880d00c1001d40614150807071580020318042e1010b41c5070811143c0c0c2c0044500d100307501420f0b00c9218003407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 44081002 1250 44079752 44079779
    0x20a0609030525020406081219090503120a03050109060617150604090e0c010503040312150b0a050a020c04060f03060209180f010303080603030703140a12020c031b01090804 76
    0x41d001d2000600c80c21240c1409002007507190400142070382c0d107851840c410072084400075041054158404c0809000c0181203804580542d006824150740c0e130902c41d102115042c0c01504116003501448682481c0f05100c1800703807086204d161001d114a80c0c8462450040307551030b00c1198001030000ca901d00081885c40c0080750884050a07207003062105110108000e135206a0008008540e101610821000d091080c000c3c04402440c00d60300e1030034191001020924032138121100c840d65202400c5001c0c80445491004104010480b611080000006002c54100200300b43c091f00891040d00003600d040d104110590700d0b603e9a0203001c50540e01e80784000c2d0000c03c1c840360810102d0070840360900a510340103104201036261152158190310b4024036504d40981094040d074002e00c012070009412001c0002055024030071280c0b078800d41101140c0c02c0140c001d01c11521440099014071803000807000b003a002284500059960402a0700c280c2200d0b084000139080820501c414800d02d04072082 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 44082252 1250 44081002 44081021
    0xe0607080d0b040c09050310050103171303050a03050d0c0f0909020d060503031201051816030c02010b040c020f12030411090402011205090105060a08010c0f050a0c05120406021c020a06 81
    0x400082c0801c2c500049011600041c4280000c540188400c01052a003081042c0300c440d1100c00a000651541d43d4a03406c1c94900c00101c2c00301c100110751410000008403d0340011034000b400c03649c0041c06800c018040e503004c060b9041046042480750642d180c0500d850303440341580c503030b141c102061402e10100f00035002420601d24280e00d030075000030070750f0f0200041e0005c00b0903515280d0300b552400c8108041a03101d08549006104110b040010303208000a00d4812000c0344c0c1008142a0200c6000324018030301e80c1c0c40340303a0280ca0021446596035002507c105440400700c21100c090031454880155800100ca0060400124040c03581050805140450700284103042c8101d181484c44000002da400c1101c0900e82a95160100510fa103003040d1444c0c000c11455000300121701840d01c00178040130006000070284a0005560302219118207800c40b146900302040d00c000c2045110032200d82d50003407044900622881d0505010011050a2480781160ba41c0061002468503520780b00600300002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 44083502 1250 44082252 44082277
    0x209040506010e0f091f0e0a051b09060d091a010e0105030102070b01051504050a080c01021e0c1e0a060302030a1b020d1101060b0c0a030f0816030506030102130e040506070e060708 79
    0x102540800b2108801003014040f0311f60448058a80b15030303500110b0b000106008141020a01005c0498001404807072400d41c0954400780e0300c0080100d031308042c010804004000c0344414612508105055084a059600882c4114610307607880082600f43d002d10714020389a06100801003085188c25044c0003541da201b00001e80c20140d58100040e80c0c1e20a5074042103554101c512641c52541c0c1c10f0003002c11040c00140f4081903421400c5006607030703030b00c2010b2481c0180c540074090401072022041c415940d0900410b07440000d902da6100030040d400a65941c04018100349440f4101c94030070328085060000c42c0d004003a03082801804940615000781c0c508015540c4100c08182803444800803d0032010300300c000c0200d0f0010780760040c003c404000d10001049565402d20074650300d50803070b00380d20b807a0f20700d400700c4e1744d44802c40000c0c02442003114844070a9034044000401d80c00030724a1031310460081c0c050745e005a0702c00005035080c10104a00c5548202d003001803e0009814001511103540820b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 44084752 1250 44083502 44083531
    0xf092d1309050f030406080603061006030b0109150c020102191707030509060703210507050d09020a0f03032001020316050a03020c1209120f070323100209040506010e0f09 75
    0x142c5929050156040b1181c07840d80000406020f9150803011007a0040d1041e40141307018a08550110300c0d17000b041c0912400c1545860560320701d40e00c55500c0754003401c1e1855484217150710660000d0445401d0a201300d0140c0500b41c000008808a06076003070800d0b4000b2299200007283d481030780e90300e501c9408100c0901005201300250340d00c8080c0505001d40c071a88504050000041d100f0020b020150020207002d070503d01040101c5602c4401d84074416260400403d9002181c400103d405c00070f600141240c42c040203000051551124512030b0a2414641040b1814400c80c0d415090b4481150104445031001c0c00b0842110310a0009100c440d281e85001800c041c465084242000205039140300350359000300304040585821382c0c4c2428442c0c034400007440c5003101c092030303d511340e000d903c40a03242c2441180c040d05007130310030880000c032910b000003641c4124081904000080d0032104103940101d2519002400c0c0f5400364006c441ea5402c01441c034084d540d200e80130001c603108001c06481044091 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 44086002 1250 44084752 44084771
    0x30803090303060a0504090c270504060b1c03050304030c11030105070210050601051206060304061401080f010b01030b131505060a0c05060f010501080414120f092d13 73
    0x40005140151024805182d03030341001d60800c00110802d412680c0300b43e29140c25040081e40e61004030702150325049060030f00e4524200803401c04020001e54102146c00c0c1030410040040c554003409a2000880e000480341002d2110b00302441110344c8010007040082004c03c0109000d105002c46e00c5100700070070385215433100701180c00c0d075100740c0c2da10740968803d0107080141300090242d82e90011007841c0107400e1080880d4002d43c1d04001800c2c0c83c1c0111070000104092105940004d050040904601001c030b503580c108150390b5100071301d0310260f107510b0300800c48200d612902418040e450002d041c02429802485800000d0074130b00080824107041941c001607a443c0c4078050003006c40d040c5c94201104481e410b02c01d00309103000700000b00c00a10400103010030f030b0f042031401e134205411485045408003c0c041d500d2130301e00300600da0750701200040f803140f410004100c01020711038416981000980c1c06103140c1c1450381803005a1402c8552a204032800c941024442c0042490f40180f020586404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 44087252 1250 44086002 44086013
    0x506150403050109020306010b1602041a040501080703050c0a0b040509181207020f04050907030f03020c030a1101030c03050c0a0e040f11031f06020604020402220f0807170a02150403 80
    0x5988102d989946410a036010351070103120580c010900c0b060501c2c0b5240820304c0000a000142d10000c7c07041b40d5031b00c100203400d81102859416082d01034403c0000b56124900650b903008070340300490701403058402103017a0742050b0502c00105c0e0300707804820f03061500784000c004040e100244000c1c02102840030721440c3c0300040010f42d40b20300c07034060455a26616030052220900c3e010074510f00450420007400070003500000c01d5000c0300e800c04002c440c16061454101d04200460b07505650512078040700350203105001a501101e044240c030200a00540c3c0341c800da09469040b911203540c581c0030f010a02c5614041d201c20b0b21030400062002a010b18210101001c98981100711151518048208164904008041c0240d0f0802400040d02d562600350020b540f1880100024001d03074000c5041885400715810180b0018080c1c51000c0301c550b140c03000c0004489051003855603d2090750400038006000c0082c01924200e00005884001400d03003d0001f1420810121503880c002004000301294 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 44088502 1250 44087252 44087257
    0x30c110a030809040608031201090207031106160e0d021f09091103010501140f0301090b0d050d020a0b100501020a08030403090b0d0b132a020f010f05180706050d050615 74
    0x18414501d294070f58800c5000d1004582081d00024100d5008009a003e50800c4102403411950800c0c400b5076592002c1c41d00711400d810a080f0b0402034440e8005011f509116001081c07242c030416a80d21111810000420034001305051020390800e032841144110f074600c03000c070031100c83c2d490706085401e0f03503580c03a0490484070082c0d905510b016000c0014030242d83d101e4811920304079940c080c2410000c101e480052035120620403030501076500e4100290544540c1ca00c18600d40d045403e580c040004140060340f1032a80c0070044421910f4100010b40c0710524032410010342d00180d0050100b2961691800041d80c40940b06a00340003d4120010341140b9400c0104025035107000042034050241c000d00103005149a1034040e00e9041003211003044040110b01c1c0c4480400f1801400f0041452100b0b03402c1c080fa9103465200755080005078200c035511604450301680403440521401c149500c078440c1c4451990007041c0004508002c050440201500402d0304048014044108822615840c54103a03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 44089752 1250 44088502 44088509
    0x61626120402030613173406050612190503040807080d020708031206061c0c05180901030809130e0604030804030e010903150e010204030f08130b0a0c030c110a 70
    0x2040c90304001c21401c052040b00e40080c4401d491490744142a50761042c0c4046581d002c165000e00131800402d4110180c1c8455502e141d1444075102d4165040d62412011010b49400c2e0b03102800d1001041c401d0800c00542604d100c00c0001800c001040340700705482480d421042a60300e03100c140008070f850b1506100b44c20042007403000414801a000c08042c1c1004841c1d88040210f42041c4070402040c0b00d00c449142d070012040380c0c0c107a0340750211100c2164001d140213150100510b4030420b451031300c0d0040000c00b141441107650101025a031001c00c80b00d80800d0000405044041c44504c0042c1400c042c0011880780c0c500c000b0600010b2801420320b0084101c1d070a50000c0c1001c024802495040b1040a02e840e40a10b0400c0000d42580c44810034400c4003128074a450303a41e481190498042941550051130344480006c0b150303111801d2500203a00172000c8092404544c480004604800c00103e610135403da448a00c58201e1a031000d1b5102e403034150040c0c40380c0303d845800044c65640c7e0300d1040c1c050f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 44091002 1250 44089752 44089777
    0xf0f0d1107021503091504080c0601080d14040302030706030225060c0306080105060f10020f030409021209060114060913050f0f0c0c06010e0901021b07090b061626 72
    0x1902a02c0c010040c2c008035000b4507a030100403c005012600f080458807045105004050004586641c54134980740e10a811540c251030044030004500e014000c00c00b0b4224040300c1d900c80340710701d070350041c0b0980ca0b200c0d0740703c0254945d0184d40c0402403e40a49c001d40000c01040d07111042900c00780ca040f4001445140b0300311141d56603001c0030918140c02d80309007006850f42000800039468030502050f001c8030b003409207612075200005501c182e280700b0000a1002e103a08015a51180e689124504c0650000715000c0034070031072000020112240028528100c50280b00b5400107114118203003e0260300c042c1d109a0860220080e4552040c03e0b801418000d1417114007110140c5465105029911006043c002c1e0002c4100294200c3c203c00040302170640e01c040003a02860b841d03c1148600a11840002d41d00d440180700000c00d1041002c03c40342c00b01c0e64408000d1007244241c00401400f4411000d0101c1d11514403410180410420422011164600d075100130003a04881412400340e000800c00d44074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 44092252 1250 44091002 44091007
    0x5060406020d12090201020a0f0204020d06180e0f0d030f020d0203071e0504060c020112060e040506070909021908040501090605091b091303270f0509070c05030f0f0d11 74
    0x102c01c1c0c0c0c00100210302c1103410b6000c00c801941030b80000d460f9060003802406e1104101c42410a550f00ca50440d020750724a10010040c0c1544d0b5820301a15114100119483c03034505540000044004150003007001c42250150400c02c0c102d640540080278001c051a210075824052100c0c3c101c8544011401000300303440762a0742042c007523000320401c25081001401c001c410300041151a40000032120b98035424200f0f00960031005420b2001803049520808e10004400d00340401d0090101e0031031302401d41695044041511801000180d200e582460100b98000c3d401c0080428440e25000340c000d0320941c0045400f00440d2255070584e0700945518001d900140c28440d840d101c0121901c0b0b080034155440c6501c0e00c0d10410b08074480302c0c00500078050088241d00c00756400e82d044520000c10581ca04282c10841d12110350038a2800d0070700803103000b84900e41c04240410b00031002240115031140096280c0103110b003034007281e904031030b29002c8048410310014042c00c84500407082140402011940c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 44093502 1250 44092252 44092273
    0xb0301140a030c090209030f010203010306021309050f010303121d010204180504150b1206040302070f0e0f01031e0203070e09060609040b063a12030c1211040506040602 74
    0x52400c00304042540c407600440c1020000203070900401d00881c1c940706001a10b60702d41c44042401e01040c00304600c2071354400070001c000c1116950140440c504112104030800741c031002d03000100e84054910b00188603400d8010400a0710035240700d00c0c40300c541c41003c262000300100500f034519100000b6401d503500460184441c140b400d40c4c015040001c044140311601b41902d40d030a004070462407c03554680c83c1c00700d6149503164050140c1c4901d21040c201d40d42e610701428000e4443c180c0303001e1060f2201e158500082e4580510004a008860400c0001d40a92841e030700d400e5a950400700300004014070041d92000b5070380c240700c600700411400d4240385940c9820380040d070800000030304e8103102d805540309000124844000e8282d110300255002400381610396200c032203103142c00204c1ca91000c00601c5117884151a5080840c5203407107035110f18014034940806401356500d02d03008400045400e142d40c01341c104290070984264600d00d0700d580c40c2948070004188980c0c400e400c10000350b800301030742c3c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 44094752 1250 44093502 44093519
    0xf06011e0c1412030a020a03060f120b1302060d0903020715020307061812050c0c0d080c100c2c0402120115050a0f030506010e09010f030501240509190203010b0301 72
    0x1206100a58005066460341e00c060f050b10501020300507031002d42d4045114012913000341d01070b60180140c21280030724550f4544c4c0c10043c03541c80c2a0101d07440301c050710200d2942d01c0312210000d6060360050426050543c481900c50080c441c2500075011481405400561402500000058001994051951140c003420030718241c900000034100ca031000c806548010681d40b52081a400010385001980c400c1d4108400d89044500c90304641c2c4100c5086000301004a04002415151051800d4400aa4501c0c02d42c0c01110080c50340200480c40000c11314002040b201503040089984645102080d00b00401082c12030f000744107246400305e4144c0061204032041c10240000420a2505a00d0110300d0340d001408074040c0c214110a0544501c0840d24580c09210741c49001c410141c0841038079030b1365290b038050744c903010f100546030f95207040b42c82e0b80001080b50112490141050440c0c2c0d81e58600020f0040442c0003c103c45070108a4841700391140380240021802840c94101c0240c880d4100f000c43c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 44096002 1250 44094752 44094773
    0x504110d0605030d02030a050711040203010605040501120b13020c070909080703090b0405061e071a1609030b06010e03030d0c0305100503030c0d050903010207050703060906060b0c03030f06011e0c 86
    0x2083c42503200343e401140700b6500108403902146079207402622102c10349050359021410011481d840350001c0000b10740180c0c42000780c000c4070313826a40e00000c071159001020444cc010f00c1d4051f0016400c00e07421031680280e8000706039071034010040756403040d52840302e0022120811000c450301c07180001e41e0000d06910003004d101410812582910b070a140400040795071245429080c02d114078400240b43c0000b0881c2aa021243c10524188407822000c005040070030045800482498480c0381711407206110f042d0001c150303907001e0b0911030340c2e071900001500d28407035884006506100421401d001c01d0074038010041040d103036403408149401c24085070700c2c0c841c03000c0c0c01480c0a41d00034440b6030200f1600058501c20400e842c10321607914031022010038064810020040c0c1035215111000040015992000808502a0b04204540350300d4021020042c030900c5e140090a60052010035051949400ba00b9000a0141016038000c41d6554607081ea00c94910f1220000c95040d049404c1403014a184 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 44097252 1250 44096002 44096009
    0x605040e060106020307020418140607120b0a030602030603070f15022a0904020609061210060c0c0303030203070309020d1104050a0e190c0e16030b032806060504110d06 74
    0x80d00c40c82d0704002000350760780030742030010b0310480d20b50b1180110140102101d1b02205e4002d14281140c0d0481d42c8001e68035107041e90104006040a031554007a0b610301d126160440000030202c0d0020791450311140041d403c040e12141d458050b9080001d8007a40c945c004400810b40311102185200988101034108443c030044410712801800303400c1c28017040760209141c1400e0490b9288065166800400d109000d1203049a407c000c0020340c0b481d2007228000541d1041009001d03c81b1107585444013111426540c201c001d00308034541c1c40500010b802900a50b03404440340c64002945403540e00010a01c075090581910380741000092546e80f82024010340f5485600e005c414810440d9415040b0383d0748000f80070003040315001d012000304000000c0310030030080c07250304504051030801c0c288464001210300812004246419440b21203420040b4049250952480d40c0260385055000c101c0c10f0706840c000c048900580d1040041001d68840c401c507080c0109288815032130312450010300c0d0403102c5a80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 44098502 1250 44097252 44097281
    0xc050405060403080705070305030318010612051c031b05030103120c05070510050c0304030303051008060115081503060a27020a1a0d060308070b01061803060e0c13060504 75
    0x8814090307a1941000c0300c08a0390301c942c0383d41c1d541e005804c000782003045c0f580008120f1300000043c07000801d0004a58016002400000c124555940c074022b041074810701c03001080340c0c0144100d02c2001725071201602ca11811401e000c5500c06a520f01d030148081c541074120302154010006105101e00829000301032245c60404e4084048961a802d5851851340305851042c83d0000600d03c034188248141c480a00b118411a03868a85030f00d00500901804c542e0403000051070180010300000001c2e1560480781002800c0490301818581216212002001e462654804078010402901e003005184d00c074404181001a2000b2010b012400031380d07000121103141c040c5e00403002d01598a0b010401e0850341c2d00d03c103000c0030465000c032144181c000c201c0e0503c0302c103180200010604c00e00500514541c2e1180491184a80e2116002e440d001108542c0003498040d040040c030000d01203510600d000210340c002c89000000c03903800a0120306007200c907020700c5900e40200300964281402003451400c21003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 44099752 1250 44098502 44098507
    0x1805070206040512090f0612090d0c03122304050c09010504110f070c03020904080306010f08070e0f06040f09091403030705030a090f060507031b140703110f0a0c08010c05 75
    0x291070321542c420704c2080101000303034005900c0d034180e65000c0310002ca520001d80404e4540641501c069210641100c0390f13005401403a40c0c41c1d600500c140741d054403155140d00c0380311541d440348948034020603003e40c0039280e103002c56000c800c11441d4207084c203214500c03800051100614032020b01c400300300e0690109015500340034022602103414000e82d140f0800c1003458948608080c28443c00c1d100f0f0a51019400410b48014442417010807070041d03200b0300081c1c85140c0f601844c401e045803038800840c0c00d10b0014014600b10b15992510100c0740d640e99600500c990309040e1550442c01e0b440c0e4882d4081444995521440f004011800c0b808080b1041c0351800345007549003451015009102c0100090412552807403600d041000e02801d00c0081e81d0014020001803074500c01c0a802841d45150390090b41d07003408441c40516100c0e032025040ca180081035542814450f03642a83c4d810070040d8484003c2c01829a410b1404c07104014881e61a4050a9011070403890f00a8840c03c482e071404101e000c00404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 44101002 1250 44099752 44099761
    0xc020d05031006080c0712020a0506070801120213090204060f0501110a0b16031b0806120f030406030911120304050a0f0e010b090f0406060504050307170c0603040c0305071805070206 80
    0x1203441e440443d030311402d10003003542ea407030a100203031300c69802e0060881a0120005001650008144608510ad8011690a511782640c2940e10b001c0034403800c501048a00c441d5030050604d03210f4002040f4050340c01041700e140c298005000c4c1c1e035042e0488031002d81001420007003580e1000030b03920311b11100400f07004002c0d02074880085202c4020304c0320003c05210b1050a010a21a90100c03c1c0b00002c0c200e035055240303142d80c008111700d10507105030388912840300842c0392401c000304a003203542c45200300640c6068903204055018040404042d1584440001c02c480070792115081285121400700c040d5560340c3c1007400304a84484650000c84500c551404240b00c45400081d426064440b11404181c0f144c002100160314002c1103582d2540090406c0070010f000c0fa040301c09407080d00c0301281901c16840d2692040d580902c4c001c213044200c0d5100c01e10281c240d040c510300840d0420f008038408843c0503101d44a841c82c02e41039500a0210f110821600084200c10380b00309a0400814405084103081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 44102252 1250 44101002 44101021
    0x114071401050a0f090519050304090203040501022a0a11010c080301090b1002030c0a1e211b03050d0e0102040f151b03020a02040c030b040c0507021302090114030402010c0f060c020d0503 82
    0x2087c5040b01c130007825160f5081c103022082054800a01141405541d40d1400f1719106020350405041416944d5240c1c220300110003481c07180d910038112500c010020049603450b2150054010130845051000b0f4000170300114201030019070181c0300207900440c0b00c3c0c1d0481d05008102010303060f403a0840d0424080103038803100200d80b008126400c10701c40030303462404001148440f201050000c140070000400a090b00d00000e08400c0c0c00345440d194681405800e4007030000314007200000800003001048100e0681c1001c1e4840c2e20300c034008100060030981c441c814140b1445050f040104007e951081071082694004410185034801480014001d120380e50080e41e0b801d40c42c4d00081c42692a002d0a140440c81381d80300403480c0c0e02c010024000181340300c10151496204c18800d1b40603007a03501c0c2400003d8500d000b01c80d00e01506a4880442c9841c2c04142900e40d04040c00c100d04020711b08140c2d4000c1000150f1100c5020700800000035241d07490b400c040d180a051140d68024040e003442084800714 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 44103502 1250 44102252 44102263
    0xd030209100809280b070f050906030c070803040503031503070e07050705010f23090303060105090d06020702030a08090f090601080a02131517090106050607020114071401050a0f0905 80
    0x40030382000307242d9803900e0040a060540e1803501c2a540310503c032040d606010504103640c00140a640c0b440c805442c2ca50080314010129501e00b80420b00407c1090003e00b80b0900a41e03202d0800c0b6013040c14500c11b6036900807190320540d804e845550002c024000d072001c241c40b0401251300f0813402041c003245000200039206600801342e409000011a4903010f0000a400c8441e95405100040107004699008546000542a03007010041c1c0c000300099089500041240c0c0542c03016110035040a07000c1003041210751000c58200c526035002e000c000e005803000c1160600c07503845200f0954a0b00440002e200c187d000f140c40e240d109151030014000940d0300a203141e90801501ea1000da69031807450001c401b5046560b200c00c044804136220881c0c0d03103501500030404140328078039084050726032262207402c6e00c1d01401025800441000030b040198010300381982c042c0c4003141528100303041501c1c0c6254501c958280c0c084283d4580c01001208980b52050700c0720f000c01c51500b00310040d0591940c55544 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 44104752 1250 44103502 44103529
    0x1401050307091a06070201031b02030c0d030501031a040804030c0e0105040e01020a1409030309150912070803040603020a0306090e01060612090b06130b060304030c0c120b0a0506010e040e0105090d030209 89
    0x80304c0c0011058256440b9401002ca085c000024403480407081120084d40d81c3c0c42a4400d040c6c5000780444008024071074080c4a0407281c02035441040c400d02c0f400c80b004440130180c0101c444607820000000086c02d20715500d4028070b0381c611021750b590b1410051200b41d03500342d5401251a44104407500a0980010315003d00700d1040e4030003a00c1d41822404640b543c407c01c00e42550014001700b42d070012041c0c010040403080c4054420045100710800d46035a511a07078000c02a41e50410301083c400e083c401c0d8040d0003009014900801d03415070390701084080b00c8410f5040d69080c3d440d05000c0c40500d421138040c0b071206c0d559030020464404141c03a1582000c1025200d5031141450703900d448150707079041c1c02014140c507006001c10740c0c80c10549005800c0280320700d81107800e038162407030005e070f41c000348000c0c0c0d02c4031a00b200c048070341503603031aa0b003500510005006506002c0d400790584074546a0b48940701c402034440000080707a04002041901d040085480c600416004200c152801d803100480010301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 44106002 1250 44104752 44104759
    0x105040e1b090607051f050c0a110705090114010206070519140c070f0306050705070305090907020106080601170c03010e070501050d18060605091e16050705011401050307091a 77
    0x102000400c0c50000380b082424040d8401c00104030030b028421302007080d041030300424100c00d105081c5a90720304144e039000c480825000d00d00344084241b05008902c6d4101080340201030f10081a00e510000748140000c0e0800d02c501082c80c0c1ca59002542c04001d03282e00020941003480c1481c820703030b00045540d6100790820b0100325226103c0303800b40b20b25005542403121184180e40c0b1540e00d60950301c0c0b42c114207200650b462400c200109508a014000f00e908107078240c2e5070f040c40c1242100610106a00c050500c6046658810340001c2021007400114060701c030302e8001c40ba0800c0b54003625440c20100c0c442c494441c0e4034009918a490750b002504108484080c00c01507201c038079621040d0020316403c20280f0391018802c0d011010041b040d840402030311400c0351510141c2c0c803045070b0382e18050800c041240d0440360490210707401310140d507401012018245000ea01d8030520740c0d18a0300795242d10403c07140300d240b00001403190345001d2001c1400ba142c4040108004140c085070303480281190100c0900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 44107252 1250 44106002 44106031
    0x801031e02040207050d030c0f11060f19050103140f010501050f0405180709020d18030806040509191a07050c0604060515041503020420030a0c022404050c0105040e 72
    0x710740b00c81d0152403016810106a807007054204034050044e09554210100103411100a1003c1c1405002000c2e044540c19005113095079a42c00040382d090005883c195804004d9401e2403100c094900500e800b075842105100443d80958403060318007192000040c1c41380c1d05203001889151141d9144602c1c50800715400705490f04c400c1c2980b6400f2001407111204da00559201084100300d9800074080c0d0304800d00d0404c002020301118243d80682203800800240180012405510301900b00c950001d002000341c60000201c0c00300484018021201203800b103001031000c23111107a5200000e80d001c036260502e1071070b14010b56503050301c504c00148000d201941e0390002c202c2100114140c0d010901c0c02500801408000941c200d030912050304c01240704500b84103216041c102000c20032207484113403842441c00d50325842038150190140000e14030451054500c12200c003415100c40d40001c1d500300925402e0382c01e0a080440c00d043ea200741b00c5040c89800c1008121444100a01d5984800501110302 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 44108502 1250 44107252 44107313
    0xb090f060912060c070b15010f0e011101060f0302040605030d0c031805130203161b060b150f030108071a0d05060a0306020f0a0912020a0614120109020903010507080103 74
    0x1c01181c0715042c40c070403900c641820005a00a07600080c850f15008410441059035409038160358100f10030000e5000400d1201d542c01c1c0607000340460041d0a005041c0311040e00d0501e00301a08480d030503070040e10a60b0044400b0404d40c1854450540540f2003600540f0020f24851400b50243c0b208070801002c02100c040101300d810191110940139120080c00c400d80c0111840d0244045d400550390650150a0083d00d4400140250070f5070540040680701c0e10b0aa80441e1078403c02040848440b40e001841504070400403040035000b0010180328601281d01c950408100398a0703c3c0d0140c014074071444100040c2c960780a00032080c0c5885101c00080072403241d071081c020a001d90015030005000d1070000c25814981080700d005420313880020340d2501d452035520426000e800319000c90180d00600002001e01115114801118500510208607460301d030740350200030501c010903840f81030308550125541c00d4901e002c0c01a42c0d00400340f840d0060595040d500d8000c840030201800010848a08500d103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 44109752 1250 44108502 44108509
    0x21e0406020a0201110f0601060807030e0606030c040e071206020a081b0d020c0f100c030c0e09160c050a0b040303111305040e12130303020f0a03050904090204020903030d060608010b090f0609 84
    0x185541b0361100c140c07419965100009085158190b62403408281405900020240002031240c0b142000600824aaa0328903080c4801000d940070300b0400b5020396140840c1c2d900003201002c80c0c41e0302c28036005030f4074011000c2c005c14400000c2d05c02c8c1085030440c0740c001c0039001c5039410785990311072440c00183d941c0720b2030100c1d034901400c144640110f07005d241800519040154048850001c4984050102c11010391007242e24024040c0313215407285104000c1a21202100407038082012142844e194060541d21054640440c082c0c040703510400c84c1d010042019854051040440c2182c0c408a003446201c016000200f0500c0c02820f000c4c1e95560179081845004000c3c1d1401050301005160391028103c20342486901140001d03400b611a01a6000800200180c25058503415543d0079003800d010200f04006800d2403001079900540920140300140c0d402c1c00145038691541200242017443c2c441c0180580c041640f014074495410300072000341d81c4507820f202c00201400c039601e9684040d0300d0000f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 44111002 1250 44109752 44109763
    0xb04050715020d0e06161109061c1419050607030f020c030a11011806050a0608032104030504030c080d09050123070f0c06020f060a0504030c03080721021e0406020a020111 75
    0x800d146c0c10040003240003030040b10604031f44a2070094402d81085c4d034a120601c40300020b2016040c4090316100808800704600d41e410410b0001d1000580b000d400350540310403c0b10b40301500070399660b0002420300c01800d1f010320420030901010310056040c0f8040181181c1c907802102550024451022442616183c1c00c0d030050f50074859681388c010784e4100a0414400a000407100341e807840c6c0c501080407400400c0002038842d44030494002a24445414885504103e8003800c00c5003440342c00c1c080400003074032407176451015100a000a00b9881d0500c94010035075400d95003d141407003245e10705d60800710f80b0891500f003c0400d07210220340d203130113503c0e14002d5a090810081e0050790800c102060844d804a80c04100c082003108480b003d8580c094644120307003058038001d01143c620421035001a0040502c1759000c80340b4145401a14458000351030341c40c00c07401102e450700358001040b144490400c900d180301c00c140711f41064105410602d029586a0288201034140024a2449521410200003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 44112252 1250 44111002 44111017
    0xd050403030305090f03030c04030b0f04020904082d070204051e0a150302041a03070608160c03050706090c0501110f03040608042102010b0405090a020a0302130204120b04050715020d0e06 82
    0x86035074a22306005c038410203030441d001c1212401c43c01d0000c03801c00728495a81da801203070020b118071600d4841c2d50300c0c1c3c032a85c2c3c001e00d04900e43c403103001e40b00c00382880074509850381801d00f45102036071113a1920411044420061824103002541c10301042035103a0810000c1d03100b080306500013000c8214a06484404036103a20095210341403110343c01074072030a43d40603060814150304079046961151001d94203100100c0304130b80180481c0040840c12441103140c40125400fa04040c6d1400f03c158039400c0c03e607042d00c80c05590b45c2d64100001c0140d540e0102a0f0515025950041c0c8100112003450b541c032841140f260004000354840030605004805156810720100c01c01c00d40c0d0381503a40032010380070b85280c0705014441c916040004034080c00224008030240d80c000d00440207182940d00b0000074000c4140d111405541c20712003c50000c0d00c01403100314040c02035465007201e00d01464164030704074041d0020490103800d0210f90245030740001e140181c51269007404042c0c0541603000c5100c03070041e01d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 44113502 1250 44112252 44112283
    0xc150203250318050304030605010501020601080a080703051b0601060e0609030307020d050c0d030801050108060d080304060f060b04260708190206190305090d08060d06020d02130e0703050105030d05040303030509 93
    0xda24401c0042c001700a1049920410702271120b40ea03646c0041e0b88a42091041500c0b50700510200000140c0f0403005084c2c00d0700c2030525a00740801d50300c1003088002d2070320a5144948c800300041c028136801038100c04200a0885100c0d1600c44c404021a03124000d2a00c024013802c000e031400d0080100601600c402c809000d442c100d004251810b009005003828440c15011648000205d0b0150800c904080e00b40c507004000f035855a2200d42c4d40740c00822641c41102031890340c031000072030419140b41c010030061220b1035036540100c074002d2101000e0b038140c0044880551000030704109090001c075002145004451040309101130758000301746148200c0341221840607898241c6a020794040c0d000c0c500410004048885407104000243c0c0c407a001030b80d405a2004034201d440e80040d0042e0014071500c84208400350030032642d071785003800c2640135411610400f40402c04121840340d040c81004d0040504178001d015070103400501900c2c43c425404040c04140e11794000420a100800c0505050030814 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 44114752 1250 44113502 44113541
    0x50d02120a17030421080c031807060e0312030103020a0510111006060f110322090608010209270606250b100611071e030c060c1502032503 61
    0x1102c40c03000743d841224201c03040a80c201c0903140e01c02e800c2c81e080541580c55220382da2180c44090414001c0e4000401352082401c2d03650384428000303401d000c3e040003005a82c42c4d0071110b4030443c08040c2062481e200c40004284144010009603072500400d02c1102c400792081c0001400202c02100c0703c0303610b00104407091042e0303214421145515805501150340c1551485080e481c4080101c880b03146040b032240003a031041c0642200f40d40d02d00c004a0242c0e20412140741c0980d92104498180c40d20391f0302400c06a540454803e56604080060110704070241000c2038081000139190780310310b440941103d0050704041390484240c40c04481c442c05400740c3c0d1200203914000780c9858520050226120505099425800121303203014880030b407040150000507002e0700b4100070401c0c0f600d02c0b42030210180b40f10309000010120b040c003150b11000e41181d59401d1504016410a120075038242c82442c01d0310f600c1001002511008900b40c100300300703103030340d603425142100420403400341c8401c0340c1182425580 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 44116002 1250 44114752 44114783
    0x101203180b0d05090102070201090603150e0108010e0d09080d050a0c05010203100503010b0303090108011406040f0801020d060608010e07080c0d060801090b060108090703030305091002030103110f0a050d02120a 92
    0x30400940401c030079040042c0016612949002d003030b400303200340003270108055a00031b00a0f203000307030040c8054802c0039a1494110340c1e10b002c1889001000c0c0d10580a50350740710b41d0401100d4041c03080d0b40e400c541908005141900d0640300640e83c0052140020420201052a0a82c00e20401081e4180b9400130b00a649074141040103001000e483c2c854a0700c40d601c3c01110040b1030501005564005105850700320f2643e28000b2141d80c0a18140076041c0c1c403200401004c00d1030010b580041001c1c060700000103841d80040b0f8820800caa90603000305051001d064010811982e15444181e88400c4510700448241c64a071141c00403401021888240344c0d040540200d072820055001840304c900640082c61291110401900d000703106a404c64250f800c00c980c1880440d02940000e904070b0002821100e0701c0c820301d070300203049030020b070421200ba000f1601c070620a447c0080948002d102c04559000c011482c0000199011451400090142e18010400941ba83d020b10014541c20340080c00c44e10300205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 44117252 1250 44116002 44116019
    0x1a19050307030f0b060d0506150c0d26060415030602160606050402070317090f011a091e070c030c02061803060c0405060f03090c0a0806010603110310120318 69
    0x401c0700c02030002854090050350248090141c0034103d40043c007001e10f00780c01650050043d080040070190485003144440f180d905268008026641c03840d006041d0214002c14000d040d00b0a2070702e0062815480b1030400312110102d190550000e0049800060803c60801729141d03060481d170015081c7d0b071021038072100300090390300e504070b02510079a0300b0805075449204001c220f0040140160014040b4444019011085a9041d070028410021038100c00d07400b000385d03401c1d0b0703040d0040c04040d01907243c0180b55504011400ca0340180074903024002c1c600c8811741181c00c2100061010b400c204405250005050003405100c9030290091310003541d5255220401c21034040d010596406840fa00d00010380859200b8182da0136982d00a00c880e10b004072000701c003546504042d0007052680101da41c0f00700c447d550083c80200501e0f02002500030356245c87e0000d801c9911400800d003210504200300020211600b50300d00a0300d042240c000c8207040d007410100c2d40300d10480c0d1414886c1d541560042010791 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 44118502 1250 44117252 44117257
    0x130c030309090b030a11010806010909050c1206010c02100806010507080301141008010e01030206030c040b0a030e07080a03051207030e0307030e13020a0e13241a03010803041a1905 79
    0x51090005001483c2c030281070554a1a91020180180d10700107020b40e2190b102d8441c01c0e800c0b4405242c10455151501c03502c40440e83e058a4a10300344100042101c83d03040070500705a40f14809092031301d0101000d030046034400d26902c090000b08507400000842c5a030081d0107448600b07401191301074032980c454109034100b10024100b107124410041d8000d03540c038030800541e03059a01c0e1450f958030310f91a40d402d02c5450b80016085c050402d8051101194500150001c2d00082815039030225022075151051380c03c28040f500305504c260880038100000c0b80d0070800f110798074644200200354590381c0620480040c076656095a15500002641405240d440040c1200700d9408503281c403070001c1f520506600b20700c00c07016200d011511401c0d13510103915014010192600d1030600200d00c400c0c0c0c01a00d000d500e144180a00d12103840e12205001104000030490710b0103000d181c2041c034550511034107d42d2070003144a1001c209003640714407407850390b800c1c086d01e240000003240541c0542c442c001c05001e42c1c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 44119752 1250 44118502 44118509
    0x160c170d0e0708030307050409020f040504020d05040201180501021f0b1503070906020303060901090b0d06051e09030307170405010e10090506070206010303050d0e16031101170402030312130c030309 87
    0x144a8140c000c02c40300c1001c0105d90044045440d0340741303003928199000303029402100c02c011802c0401e010024840e161130000f07000c41503c161780000c0c0382c6030074800509034410707407005860280c2080310b0511459070001080c3e545120481e8143c100184440510f0001d0030042c58004d4004036541c1b002c42500074420059400742c41c564407048542502c0e0501203a0b42e020880340c1d00e5001e0601d200400014103a6030008078050340240c0140e41b0360410351200c20a58000340d0b0f149a00326000c02007031400c00d009569082e00b01e140000030354a14180783e500100240195030700d2011950f8800081070400000350702010310940c0c4942903480450801c1d071224001d0422000c19034041c0145400203017200e00c00726003e4142d03581134032620309042c0d50401d83c10081802400600503403082500070100d0b030034103419644c001c502c01c910208003598104001843c85e0b001400349140900124240401a039001c41a240c2006018200c03003081d81c0e59494030f04079200c2108002d072095a003a4404401d02d41e0101041064 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 44121002 1250 44119752 44119781
    0xa050901170601021c02150f07030b0d0f0816210306050102011e110408010203011e0e04200a120c05040b030a02030604140309150403030206010608160c170d 69
    0x40c07581d000441d1000d15802c548060058229110300e60007001c0001030030b17138843c50500c111060000300c080c140030003520070f4549104840843c0100f1440d01d03854000e40500c4c07901a205d02e460501e5654580d01c803038000e03404c0141504800300700d41e40124a2802c554410641103603148542c0b58034480b260154000f060084000242800b40c04a00c81d401402508048801c0703440d82840c0f4412006000020701d9551000c1032041c00400002070b1ba144c090000c0d60180c0140299000701c03500302e42500d0201c0c006036100030b070030fa00700701d0800003c2440b44145030300182030145402942031010b8001500c064458200e46507100e035451b00d60b800d010a48407410f0a40d4406e032000c00250f443c003000c043d0b8800700050b000f94144c5c0031034000b40004032815074032039804481208490a20030030b00006032100d000f5510b400c0b10900c010070200f0903da41003003000d0040a290030700c015282808900b00c4143c2040d800480203112890304120108816034154030142000100d8181e182e80000c45207a001e0450101160745 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 44122252 1250 44121002 44121017
    0xa06031515020f100501060314010e0411041808192c010203040b04140f040b130b0a0803041205060a09020d0209070909020301090606030e0c0105041707030b0c09011e020718090204020a050901 84
    0x3968a02717510002d040c0c1c0c9818804482c9592140d480c40018216171280ca41c006441d0200c04150080c0f160100501c81d00c9401215150043e0070100c3c51030a4522100c3c900f00304403000c2c058649041d00075003e1101884c0c2c81d003c13011160060044c0c0c0785100d290300044400900140004203402450000710752160120741c0003071200ba8000400042d02c004502d000e5002104c0e04428481900c0c40e4800100904040c0c010002c05960302c0004e41180c00c00d60141c02d9000441d00e8400400c00140b00c1c0c00d9003c407202c4e40820900781150041410005401e030000c1c01000d00d10042442c5a000b403c500000b891800340556036580c6520601016204c58440c05002c28148118025800780c003041b0300d4140710060399507905140c40c0020314620b415041525401d1400703030080c08000704070181c1c0b0461041e10305a0f68540c1d40c0c0c0f100d000040901c203c910a4141d0325448103014a040c55000c0b450350200d40d148003409000c0400409044010900e0a0000398014400505035000c141c100d03000d003081000c240c94014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 44123502 1250 44122252 44122271
    0x90b10080145020307060c0b0f040c090f0e0604030e03150402060f090604120302031e0304020d1101050c0106080709060509150603040816050a020a06031515020f1005010603 76
    0x1048020b010070380e182010303050712000d2854404003074001c02c42400c14510409203160042400c041590700b00780002100c108901c01845032001040e40c10001600e62070f912881c1948411440351390310f0044e1100c10391680c000b00302040c015001045982c281006848071400e00b40b801070b06504040b10118060b00850004401e00703400150f415101d1600034290038a0702040510300c1c41c8642c007aa0b000c6074061000d00021851701481000e0b400158882d400855544080d096030884140c3ea098110900305410002c010068440b11164800c0a6000360721554031441003005a840d40541100032920b5032a01000082d8080002180030850b800040b0800c030352605c0b503080c07200e0038104682e0780348094064551a005401d200c0e000310303402070043c0340850508210380e0500030009040d6406480d543e01c070f84101419482c280110780d00a09040c2030411000c075848070030041c114110b1003201c02c140180c071384a0180314024456000c001200c1c50070350b0140c1010000800003410b081c0501c10001c0d02d00940e10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 44124752 1250 44123502 44123531
    0x1b0f030f0c051806070807061a060405030d0804052107060c020c0d080915040b12060405090703020d020f030d020d0318031704030e030d2c090708070201090b100801 72
    0x501e020240e65410310b840500c0d03050f00c1540301d4600060360441001c000720008540040e001c1c109441c4a480c01096a060000402083d03801d46034005104040402c01003085030740008091f07000c0c7c403460801da02c4654035070403c2800c040707071000c90560f18003240d01c0c6214011108001448840d00c1344000b000b040880c0d15040b80e90300307001a01c0e250003000700320a46c008540381d0005016041c400901e0004280000e40003d41d80750007942c1310b01003010020842c0002407094882d081d6100c00b05450410040c6400300d090b95881e02c0610001e0302505109541c2c20554541c0420419551401780441e50f0169901c40c000756904402500500080c0c0380c600c854102e84040001101c03d1178141d1780b555805885541c004100741e0000d0421024003045070300540341c585061083c41c04000241c0c0b10b181c50480c00c24200f20000d8050001406855070040400c501607491700c1da559040422440c00c071881f0341d83d8a01c00c4e0f005154522001c3c281d03041d180b003081100381d0860165030540e080d0000a124149544245 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 44126002 1250 44124752 44124761
    0xc06050a1808033414010506010f050d0209040f0c0801060f020f0d0305060102100c020d180b07030309080705070f03020f100819060e100f0b0307020c09040201031b0f030f 75
    0xd000301d41e0000c00100da07060b0702040c1d0181350b048502440358600801540a0701c40c6049078031040701c451000e80c4d482d8640360000e1040035403080c02070900d001d424040000c010031500c00c0d043d4405050390f010450460700c0e11164004480a6209103082103200c085d140054a00142403042100289140350b918100c2440072404042078080368008049144250205a01030000100401d0441c841c240b02040301048901594141c50036980190031900e222550080c40c1e02c0c0544601510584840e03000c00c10042c8081c03c940101c0c0c2c05250001d0400058502399000f44600c0002508610403104080781b80042d8104040889200322030260003c0c000505000b40304204260321030200d586180050340c040c220180020814800e9440012515128041660034030806d4450b20034050100c28180003168842c2001400303400d141800b541140f5080340001d54038030309003000c58003810811001c5011a40030f07401101c03001c0d080385140d003440c0800040041565a0410403040020300b000c1105c4c00140f5140324 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 44127252 1250 44126002 44126009
    0x5151903080a120905060a0606090609061202130f03050d0905040c02030714030c0a060605100905150a2001020c0c060306030714060c01020c060a060905070806011b0c06050a18 77
    0xd071414a1a001019603c1440ba50070902d4403c0d04c400c088000540140400342c4902d001d0880003508904051004000b511a038001805010700f0141c14450142c0020301442e2031290008056510180502001e280709069881010f00e10541c14021040250200d52002c4074410742e5540c01d1240d6865041000761104c4502038405030304100035904c00302e0142c0030702c501c2000c105801c403450054101c0c3c075140b0f001074026081c4c4607a60b80346000c0c4110b10700400c000707010514a142440071141480001900880b8004801d500040d0000390014054011400e54443c941c0d016400700c1800c02850483d0b004c0d5004147c0f100b024018502c1d0303d00c2038903200043d40d000d198007030300401c1c2241c2002c0211140750400900740354000f606000e03c1807c1c2a0034002032542004500103071245040000c00d180c00c0d0b44c07054229400060030082048800d03a4000ea00c0d0754402c0092800060050114922202c295200800036220201c2842d000c214103420070001d18007124590390b0014904004801e4220060f120702 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 44128502 1250 44127252 44127263
    0x207080a030c021908070c0312050901080c0f03010e100306060909030e04060e010909080c0102070f1208090c010e0616080306010909090b1f0e0906040b010602031306030e01060905151903 82
    0x1c044d0030100340704001070b109180c030840c44920901e03280e841c0d405840450301c45600c00241c0c0060078a19550f482000d03141c105003105251410012003055085450005000700040d00c013070303003000032800942c010b070100066401c00410041a0f13200c20031940a007001c0b040660116010401c2101d803410903105030012a10007000c400020307404d025102001e4140c00ba07091f52205024813040c3c501980a100401e10640f040141c0701c20600304d40380c200018003c2c52005e905225074902001440744000c5000c00c920304003440d20344540c40b030200019041340144585495070b210500c4024007005800402507001d500c2c00d0702d48914403030f5a8060007099030000d16000f800414a03501050301e1801d0302c0a991115000078581c044400c2d222000301c0625a01111001983e50001c1c3c184014420440085405010301c0d2000d0b41c07600031002d500c00d48241e41803052508065840b4018041420203611030000b400b101c0900342f02d541401240c9240350722440250034452040000c400c1d1106003500c411100300c95008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 44129752 1250 44128502 44128543
    0x1090207060506032d011e060905180c0409080c0a0605070809030708040b031003120207090c05120601181a070c05090f0106140723060f010f0308070c090207080a030c02 74
    0x2144171103800100084c84281564803400398820405091401c180d001000328000907a140c50429248246d4801514203405091400c45031884032201048041851030f0944020502018510b019002403281840e0f10040d0b0240042100c1044030365000b483c0100d900b942d0f40821a114101341c01d460b80710f841c1000f001010104000c01c00099028043d40d400440749403500700b46a541d8844001c80142c2d103c0285c0183c209070350900c09030b4200e02c50700008410030b19001d41040d28541a50704511300141083d07040c4901e411100c0441d00c10045c00202900d0444004458112272096224164000c80300495101021040108071820240725091003441081c0c080807003a40303040030a8a080408000103920000108082c030040b403400e0400641c03030542150300340040035400210130308041d4003a040ca01c0030390390310004200317903c01c2280440c296a00b04c3c004036592138051810340d0811045610142c03a10b80049183d80c180b00710305001d0301b2008043d4505200c05c5001410890f107510b0540c12140140c03064 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 44131002 1250 44129752 44129803
    0x10501050a0810090207050a0c0b0304080304030c14030a170f0c03130303060305030a0e0418050d0e0d050105010b031008070602101a0a090605150403050606060309150109020706050603 81
    0x3904a01d500108904540d40750f0688403802181030340e01445058a5030b5200205280800822442400040c403240c0040780c1035083c070341e903800314500c00034002a04000e04d181c126007d1049001500f00c50900f4001140c0d41c2c0d200c0080301811f0840401162180880c1c0080011008104007800e188603400b080d1955146a0301d11041c030020b1544084150304140d500d07076012001403c200000c0a90310959128070072505401d01c101b01c20340304c0c42d1130980741d5025a07809080002b100011a00a15001401c1c960f44021150010179103c190420001e4115800c207000012240d07010002140191080c4464903602519050016940e1140d88100c400603401045594000c803079a80c4010003040f00c090b0902d1151400d48002186010741d0f03080b000d17205a071600c0410451400071003400502d1140c2a05508192568039400d48030100201440c0c060800000000c50b00802404000480d01e248040707001d0a5071140c503d00700170741000c00700f2911940360801040b224035000500380c404000035050004280f81 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 44132252 1250 44131002 44131007
    0x40507060f0c0f050c090a150303050a030b0901090207030e011112091f02060108010c14031308070206040e0402030c1509010c03020102040504110702131512020a0302090c0a02070b03010501050a 85
    0x18031900c1010452140a11070000e80c2e0050f0388401e050040780100b034000c800b401044440c50b00a001e00ba03540d89007140f018240c9040a4000701229090b05081c0d1702d030b0300b01d40400c0d4003071b104004080307a00050342d20022a00b00420350107404c06900030f079070700d40c00301b000c51005651141c480d04461416030b001800d154400ca07030301d200408800102a104d91012010b02c68002400e80c507413000540945c002c0c400600c050354ac01d00c00c10404c0e012070301c0c000c1104034202d43d6140540c400900401c1410300410050007d0280075404c440c02c96a01400c860ba850382e450844501d040000d8804034824000d800c4881480c0c500b25100c04103001100b0b44c014074121024005450716001c102c011000c0d075400348000512540c0d2407090f03910642140b5022980c5a9091040000b140080501c0b02c4100740741401c0c0c502c1e240b807541d0b0514143e44404070400b0407a86280002030b00e4a00950000358001041c004010001d5518400343c50702507050f400300c90541d0f441d101d050308075002c00d000b0b65002030b0003072102811052 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 44133502 1250 44132252 44132267
    0x81b0d060c050d0603050609161802030a020408030a0903060b091e040c0e09101b0801120501060905040f05061305060a180f060c02060702210a02150117010b0904050706 74
    0x4071181099458845030b800300c44180d607915401a6216003044d0100714008500348246201d107041e00481400050411070b0f255000000c0c2d4180008040d808000503024681ca07504444c00b401c0b0800459844000400009107100e02501013101e41031301b005840410703400c1814205d8050840b41951016485042411558802000b4400e82d6800c450040008078601030002c40d038003450810000e083da20b07290200c0d5000365401004052081c9460308018414a81e0003803419040d1035040380d180c18058850704025001d00a55000010fa07186410140810030141e480000c950310b01c108155401d5560b40c0101c09055140100b000d085a00329000181785100d040e840071920141481850341a00350a484240119281c0705084500b15a540c0b510300c0b1345a010481954002550301c0107003080c1040502240c21051425804c010030403000c203d01184070300a0000000604c04180e18041543c5e6400440300000b81c0000350100c1c0354030b400144070240c204040818410341d040b5009240b96450034008032042e8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 44134752 1250 44133502 44133521
    0x70c0204140a050114030604020307050d050f030d05040c0806060307030b0901090c090b03011b050f0f04120302160506070803010b0702060c03160615080a110619030501081b0d06 78
    0x3540c1c4084400c040c420500701c0c1c1d80201c0000400203015070420703082050b4106030150b43c0744070758001c1c8100700050354005103907001d40700d00303980c0241003482911303240746440300c540302101040c040454851610081a4840e611550040c5c07080b540f0b071561040340d103840b000160b6509402d5000007005001141c40d459485410100b038100004907400252503440d100940b50f040ba4103405e4403584035109601d02406405a00d2000215041e40401000c5010303119114108099142d0000407607a25010349030a02560000d100101c10300304003030701c1e40c40c0007502e440031841c030920181c0c403403400801d403410300c1019140c0060388800d18038a50390a00e06401220340040e4000c90b4002000c11900440b00c900f4400303464450b0346220401800582450050144d036603000c142880c0c03140719001001800e50010b0a030307121a8020074021880070200c001300302c0d24400d603142650000e10313281c4940e0310540d160384002d0485006800f41d407031405807255000d0b20b0914060350711b41e000700070904180c0031602d19402001203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 44136002 1250 44134752 44134759
    0xe060a0908090303040306060e0c0c07030b04030e09040b060301050c0301120318031a1005041e0203060f10050c070e01050a0b0a020a020d08090310090201120908090301052a040e070c02 81
    0xb400071010001e1300d035900030340007165115107406080000c04190710700d442c1c000407030082036804d0040c400301d51550750300c1600c0090b224400c1c290218052500a5030111510300c1c5c0688603003140d10300b03402d225070a202c2c2640c4040c01707903180c14005020080796034143ca042c0c1c1d18100c0c0c1d100081031103031401c81e244040b1400300e4101802002c0000300140e90303208a03d400d81800c40011006181040c802da0109100d94001030107941002c508403294440041d4080f80c094001e04c005847c1d0b140d4001103a01d40508070923650700031008607512729a0540000150aa0030398070011034001035100c410080480d02c00b03100311a040350002c101445052484800340c84600c4c1c141c411608012481c0e0001100c28041450658102100041e12090780c1000d02078020000444074081c4003441c00307580024001c400582e0304150740759032f4543d26010040e84104481403048010002e01040c2010841c413940e5100300c0702000c401421004040e24801e80105c2a07404a808210328224243c0d100c6a090b2004400c034281240d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 44137252 1250 44136002 44136007
    0x1050a0513020c0106080a0c060801050307030b0a1d030c0705040b060a030507120207120e01050a0c02121e01020301090c09121e1b03060b1503010b090612010e070207090e060a0908 79
    0x20b000004d1040c0c01c000c001c240d00038840d081003414110022310740c58010314204251140140015100010904112a8040e01300541980e075004502c0c0100030928842042d8016040030451082d8000050701c40140d050041d644926568001c1008031024400c5081d0414030510000400c0da00907400701d64400c5035400c140010302030303140c0b42d201240e00204088529074103000e86c0d80350865014040000d500b9080c20042e2070102c10980c0502041c1d21100020310542002501c10140c190900003c80b0351484144260b034801c2e10b0089c014084d400c240a640010380ca030401d9180042d20541402d401c4400c180e040c10034540c140d45691420448030704a41102c442c060703008400240300c2010155440314211080e44000b41586400c90580e800c90322650b108521841d040c0b9407000a0804990441d01e41840c4107507901108408201ca82c00b61100c5044454000400020724100504501d88146426801d582d4040c2d2a0b4038040101c03028650402440c0d480140010410405a803005210300d0181d1071150 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 44138502 1250 44137252 44137267
    0xc0708130b040f0605030906040f080f210f01030209040b06030a0210030e010f050115050c0a0602030c0d05090d0c0318180b040506030a020102060609040602040f030c03120801050a051302 82
    0x1454000250311000707a081e000201044407941c12100d54002e0300c03840c40c0c81c52035410540c1c4903944e526806400507019172641ca205204019044040341c0c04038045180003a01c3c1c420200403403816096400303140854181800000c0d62000040041714180d03540280000031546607134480e80f1489030300038003281d0107210f01c2c0e5480015079034042e00200703e00ca0940d4003107181d4081c241d074a425550030140f5840e4545c18a001030004000210607103000d40f200e40743c0719846500c54411245800884840540390781c4c4000140056504050018480078410000900158580700c1d10255141650200d20000070042200e149c0024070481441c6102c0c1840c004215006882c5c40000700c50b504100c0302e814080d5502c1d0881001d80c10280606076010200b02c0140a032072929400203915100001c0ca5203128010840000d02000401c0e419103001c5d088a20001040c140c407850002d2040ca414041070390304842601440310300c103100b01a40c1d4143d40b0050b01381e040c0186444103102020b0a038101490040d5028801748 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 44139752 1250 44138502 44138527
    0x10317070803130201020d030c02030a050c010f0203100509160912020d06050c0912060103080a0e01020715050306130504020307030221010203090c010e030f060601120e01021210050303070b0c0708 86
    0x194042c10620f210074545080602c0064540841d4100e00021b1604018004c05680d802006881c10010981445035464888100b41c2d401050290515001584044107020810030104e41d001c00f03448007603580c2049501c82c80c0402c2440c600c450705050004005020501280303c1c40d0f04518041407006d404212044510350324003040e52801c842c1c071001d4010104a102c080e00d060861180300400140c0904415411529004003a20541c003401c0c1c2400415050822123234420400350001f08486210303440981a45940240141c0c01502c0040c403030030501c0310b02c540441040c4945805568024001e0503e0383c0355909106180000b21300c280b80800c1c00140d4103010b604d00380000c40c458814400079000c070005580014203000152000140254460b440000924900150894004409007840c0005c00c9034040b08402a007840030b8055840d500225001c82d00c0400451020b0155403d401c07100801925401410742d640654000a440c210b0044049442a4941002043c2d428000c00000d454808800e050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 44141002 1250 44139752 44139757
    0x10f090503150a20090603220f172a01021303060506131811060d1109040507030c02032a06040c090b030303040c050f3c04090b0103170708 61
    0x1c0000c0328090001c001e861441ca04c542c0c000b0107000c0030b103c00484000403c507107550050708a017a0040100001103a2009140381003009402c4a921b074540d00221640b80000c41100c0710740c0308503031904c40142079030322100d6518251160000044040300e8021602c5044440c524079946801d8000c0d5401c2010710340c0542c0c281e115030003840c003074000403405060040510507414512080314105520300542111415220185400c0041d003040d10340340c3e42510301d00041c5c0180b00ba134032090026494000c50784a0701c0d000c44083c0c29840c008803020440c82d0741e4603405800351062034a800f8016001000035905105c0200e246801e443c03007840000c1070701c41034841c2280c40d040c400c0e00c0684a12003526020040c0141c0c0307004600c0b042e076007036010354110704142c0d6403901e50844d04e000340e078031607202d40424041603114020038a1002200004490016000c9106031040700740c4518800514480c0142c2505c0134106801050380c0d041c1d11034000002c0b0707840d613203810b0180c80d030a42c050092600e04207c00390104403098003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 44142252 1250 44141002 44141023
    0x10020304050108100302061b032205011815050c07030510050f0c04030203100506010c06140613020c07090209030f010504032607021005070306080a0506010f061103040302010f090503 80
    0x2140d4a904200003d0155500182540050b4481c08002d20042e2249415150700740c0050b41c08003400d10815030300a046020b02c0950604007074500c502e043c1c81c0d19400b40124201c074000c0c3c0301c0f1003171039a1007401d00f0500c0d03800d80185204500780d55808044d241c40365000704880c00101058500d255101c0d03948905012030000110400c3c1d45a8090201840342001980c1d009500f0340005482d061469003c81c0e11804001d84440b0344640c0c4100080c1c0c0769024a565121081d44048200a46081610340c105c9803c029544a802089940300822168119100f241d90460180008083e83c52621040401a41c422003460b501030040c6492000b203180c003402842d00592094a901950400c42d420b0041c5590031980348008452280e01030180b40780d00030800c0ca141d9000c1c0a0081159070340c060050f0080d0545070712001d80c80c49014014401d00c040415010305803034005c400d00c100c0b6562081c084404500180c6030a20642041208100541c018420b85012080306c3c20081210369440d00040c1c2400500507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 44143502 1250 44142252 44142257
    0x80a060b070f030206130309090c03021b060907080d0c11010e0d03020f1009020f0d02120703080904050a0204081e010f02040e060a0806130204020d1503051b09010308030a020703090510 81
    0x104070b07020150103020407507200700d11282c803251846e030544005044124603c1a40507169513940d1404c0c0c5103100c0e070102c1d41101400d040c4040701030030340b02c031043d41e42c50f007103507410094041d111000c507000102049103801400d15a551140f03c40081c1c0b603161181c2c642400042c103106c501aa003a00b10f4a402130400c00322030203030700581410030034140e01d1414040721038240e045170b514001c8034800596510800300100e000c00e662a81c4402038a2010541030510900229120300c10b0b80e400000304001c0e80c1c0244080d0038103031800d01540d03d400440e40280e0069004030b40d45900024104203850303101c400401c4800d000040040368801080805a0480e070041c0c100340b031504150020402c1030f0134140520300083c8603410080c011898440c205506000c179801000784181c0d0000f403016509420b41d00043c80d00d0b040e02140400c00c565901c0c0080d0f0360703d403a1100c4295100001030101c00c46ca01041d065040341c0e0000b0340795103135907035440c8080c00035440401c080b424084071000c041030b00e07180c445001d4160f000c2078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 44144752 1250 44143502 44143523
    0x301140f040b01050108060108162102040602070504020903070308030403050d0515031509060c0a0c0c0602011d03070206070222060b0d060801021903020a05042705070201180201080a060b07 83
    0x1802c00c0061144141c020a041c0030340030040c001143d0344503120b5540321340100428a41501da04008494070344004181050014a1580050303110a40b6402801200d50075002c40305000c1e541c03418001a8011210140e03415000900e080001c10307280d80013540d03c42d20925000d440c1421145042c821140290354000a1812a80216116003820000f900da18420a01400418600b039084e05030784480042c841c18000c1d0002c2540382d1440e0041030114150782d130002802c9100b90f128603009000b003405020380002c1030540d40340022091404000c50b941242c026020601e46000c079000d20814841d804003041d01501c00449810a000702482030342c015040911500759568000303484841940d400d40c0194001d41d10400400c4103008955404a0842000303040150320f40e94404016552070255038880a190136020880d4203820000319a0048032000d205002c000035280d21700300320b080301c0c2c200d83c104001c4010394026501640c0100c0e100381d8000300c5c1e1070000c10b1303442d101c0b500e49140b0303042180d0456990144 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 44146002 1250 44144752 44144761
    0x71a0c0702011115160c050105010b0c0c061602010f050706020c0606010f0924030e070609060f0804030503070c020406050d030509101707120f0221010f230301140f 72
    0x458200f43c5107401010051000141c000c21500d8810806048002c14240303000c660f2101c40e02403510030002c160094000c20031980d41c2c820006469104011168544c000c0346180600c9182640940d1a0b00404040c0300f0300c070564690048d10013080040806c81405018042180000e0942c0001d20750030008070f01030442401c15100240160841601041c00d12042c52014029928281a5400e03101e982d4120b015a0403800107059004000003a02031034240a14240401c03050f4200c100d01c030480d04287d03030b01325074002c009000310740d01c0f84140c0b0b000300012400c1010500300c034458501c004810303000a10010310035036644002071071801040400c030081080850010428a4041202401155a81131000c04201070400603c01000300401c00000e0141c081714050032516240d0002c6540c028101c0d0440d621151400c19041c52030f007100c44a51a07801103000070070f2b031091400020048500b08545140321800d6402c06045081855200340e03090b650b0f41c07603142403c1040380306080c011011003030341ea00139081 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 44147252 1250 44146002 44146007
    0x7050d1d100c0201120204120312090803041a0a151e090f15050409020315090307050d080103150b0105090103110c030a05090a0f0506030610020f0f03030a0b01020c03030f071a0c070201 81
    0x401c40e0800340880c1c8144008c2000010721685031000036454600080da50080c07002680041c0407044000e041e1a101204120030400071340c24562504200030140c4460303075600c1c0d84d035400752440c145c031803c0d00f02c00f0401c0c00c000c10003007011080940c0264590b00100c2035160110384048607401c00c14000c01316250754900c81152140f07002c0c036018050513030b400d0115081540100c0da540301182100c41c03402500c800000d084910034020b07140b600f5448815240f03506107011000300710403020301094582452a60ba9100b404929110b10500001c06844240c18100074800650041058050404c56054200681c0b20101800e00003000d4140051712102d0b160741c00402403029202e0590043c000441d2402002e0125540c0c400079a40e200ba8210b4403082c41c40b881000490602e01a0012a50180b08070b043c4003c1841c00840a03510880c00d00c00d007084146603243c01241c2d40c40400810039050342007000031010350303060030b002080700d180074a42810800394444111041c01130119004940c95101042510866a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 44148502 1250 44147252 44147267
    0x1c0e0d050313060219080306060705030a0305010e0f040209010b09061c060906080a0305091e12010504140a030e040c0509030a120305012c07020c060d02040509060607050d1d100c0201 80
    0x1055200804040300110498086242c2c00c24020b800006c0110006900c3d45d100d0b02150301003035004003540d440b0302e200320019001c1c000a000750180c0d03038007000010743e04058004031540314030340040c4141480c1c0d2078422110707560351000c4442c5410107000c01c00400740e0300d00d010002c1003003281d803640011824904070000003281c0c031a40080c1a00c0d0010103454010a51101c26030b07030780d0035003128a00040854120302030080c0200c0c6850719008000841c00c0075080c4c03010f40c04148128000e04403a8403001c1d10543c000d0311100c400744001c0100f80c20402010741d506155200d05c000802d20f060843c5460400310000b0f1410175010307030884210a820701c01031101130b4103001e100e006180308110301440c0c0f14040c1c4207201115403410031000c10071076040000c119a1007040000700c003141c0079090a55824140c07000350040e43c440d004142c015002800829098180381d011120003541050203460303608410030080701d800000a00049043c0d01c1291000b4031341e9500c2c220a044c2c08007039100c4110089852001400c0c80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 44149752 1250 44148502 44148509
    0x17041403120a020714010507020d050120040b12041a01080601030606060f0c0807060b04021c0b120c010c11130504060f060302011b0201030f050f071704051c0e0d050313 74
    0x20001400001c140b95000145036040d200c1a200c41507810942c0700040703580b4001c11001a50000204100109000040d44140300d0004880b008119a00b40c0308900c1c0c2c403501c203a10501e0500d03c2e04104a55400314040340142d041842140c0700030b0b02104000b11603100324000c1c0c104ca80307140c118500400803c1018480d1000600f91400c001a8034001c0c84c4000d0041400c8400c0940450800107080003004080d81c45410080002031003151658070f607015a11000281caa103000c01c40380340c55501030452900031006e054408d0403c0003007820401c800c1c01180e828154450849000c800c20000d003400340c2e40ca90021001c400f0514000500745080e0804406440700080d000c0909031038030f5410310240c0d07407041e5101e0342c1040110b010003c0d1011032004900034100c6a9800300c0c131030301d07000078480c01039460b08009000e8042903580b4440c440d1070380c10490642100362802002d90b0b100ca0529030b4040c04182104010340400d082c41035805100001003031840000510803540d80e000001c0083c084c810f01403155024 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 44151002 1250 44149752 44149783
    0x6170106060f020703050d050318060a020c010c0203070b010603180609050d0801120314130e0103050708060f19050601090506030f0901060f0b030a0e010b1003060602150405031617041403 82
    0x41c141780d910b034143c86541882d4000208040000040e4001505078030101c8456143d1003140c1e9103152540749c40000f9002940031007060350034006040903c17880001590348054101c1840c00869290810640050010784240204000b820015402040c1d062140c501c1650184001c0e20301280c0b1440e005101e0385050300408801000c2c05040408241c2c4010f07a0701d40c11126410881c0c0e40e804200100421080c6d580c401661007a400001200f080300c046604005ca800440458216468080c3c0d446803006040f03071601c0c02e01d001210b0000c000c0380c2a81205800813030605140404c00d41302c0f400b1404d07590044404000300340d820b03014841714540922510004121000c00380d1a41818000d070a4282d22001e03108075000e43d00d0b04241200705d00d00794416090680000c01c009010034441c1d00c003030050903035842000d0150080c843c0802d4201031004c0860311032540103014601d40150310918040c8460022800d45000f9480c0410f6046d085045008002401504101707888035071070b4000301071400d944072422170b82 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 44152252 1250 44151002 44151013
    0x30c100804020103050c03090d27120b0a020309030f0904110a030911040e0c01030902120604030c0b0f0411061c060807050405011e051513090203071e08070c020406170106060f02 78
    0x80c5400c007180009ca400310b185440c42802039500400c1c150354104c0c0348185d40b0780840c2507000940d5051803808940c2c2620840c039100c00790ba82c08201c001280030480b0a6441d68000f00000c02c01d402862004040c40c440c028800210302e800d40072004200d420021244012903a941c030fa00d000e001c4c0c15019029036000c02c8405120b4142d0300e01d8003984070181d4510702e40c1450f8940d8150411541c070400c108521050840440700f11745060304009040c4100c030201564100b0070180031030440b004001c004e621032a0055103140014000c4418482280e00c081d031611440304400004030341601d6180203a0004080b0134006080b8503040404210450360180c2c4000303110171419030305491100380d4040b89002c4407000c8030710307441c1041a441000200c0c45004c0e20022075040b028001718402403641e0145000d480b5546e10044078881e010b5080c00c4121904090002040c2c014000880851150f015456141e1010f00b010075a60342c1d0b90441041c82e20034000030390070b50b515032400340009a80015100c4180045100500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 44153502 1250 44152252 44152261
    0x90c020f0604050c010507060603080a02010903090602061e070e0904060e010c03022809120309030b01120209181006080303160801032001030b120f060108030a081302030c100804020103050c03 84
    0x3a5130320450b02d20300303040c01030104001c000c1c003455501c039900454001c03190035641c07180018000d000b4582054120045006d0710004070790244000380d02841400c2a040d40c06040030003101243d0030038001064007040000300208652552114006035008601c80c050100300130460f14140c07400c1d60324801a0000300b51052001980c108000c0c8621540c520802441c61600e850180c0100d440c644c0da0313000a20303001c0a54940d04200b50780840c1d03000849000b00a60400b40c0d0700c815042ca4903043e4050043e5102c856100414559140d00950300d00e80c0c0941c0c011124220f18008002c0c0589284c1c0d40062107640010041103005100d2042d00f02c00c2d02d100307140c0b4803855815981c5070b0320b21400101b440600d2800c851002d0400e80d0003540b1411a460b0000c007000b1103003e803d02142c1d6a50441c03040d0703003c1d0303014100c00000e810500005880401c0956200c0b4079080c0e03260542c48c02c00075040030080c4d0b07143c49441f4400c1d0843d12079603c038981e5103a0642c0e90031418909400090143e94015110410f111001c20401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 44154752 1250 44153502 44153513
    0x509030a0903060e0307120c060c0504030302030d1a03070605120c0c030a0309110a12060b040e0a0311030d06030308090d09030305030402010c020a1703040302030c0d0c06080a060906090c020f0604 86
    0x401c241d9501c0500020351190306040c681c614081d8100050441700d01d0100000099004000340d50041d100700001d10040200da0803c0358a0302030307880f00501581c0300740844134803035260303800c03040352a402a540813080b01286000286451920fa01060200d1300000d90b01d41c210022a4541d984403c0003515140360440d10410b5541d02c0c41000340748820582d48903c00c40801c5603410050f058004001d01c01f803881c0d51903070740180e07044150100440d0640d00e004030700603144c240740c003d02c0905041000902103420703994030103550401c070416452809000801c51024031014074400e2101450095480d0f8200d894003141d0741c1d20700800d91402c0c00c18007680074070400000c1e602c8012a5406a828030300540620f0f864070109040186c6908000502d50354000c2207103070802c00101800449008400b2208a80900030920400d0b8405450141c1014010034051201c180125689034000700071801c0010403507940c503294000c84595030003442420b600c4110285480ba41000010710000e01c990260425003420360b41e1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 44156002 1250 44154752 44154767
    0x90c1101090305090d0c080105040312050f0c0306040c0c06020c0106030b0907050a06050a05072001030f020f0f0304023c1e0909010b040e0303010608011706010e1323010509030a 78
    0x313520809030f400c1c14000700411449088028900c110081c4240c0c2040c4c60050440c8202c3c0140c14000351414001803500035290582c64040d0b59620102840c503280c0c1414400a0045240e40c0001d0261403c00100080e100d807004143c420070010002a4450442c0751072840348401038091202903004a100b40956a00c56101c0c008541e0746050441d603a045444003601d523402210005446240a5040c002d4100d45000c5094540c1409030790810092501102d034004900440c46407580044040c00305108011000d8000e54100b4001040b90540c41c1603c1500542408500000c4001c45000005005080388443c00c1031070850040f41e42c00104112070403006400060f985289204400040100b4120042035021481350340c07001d0010711881248840142c1ea0360300a2188400140250000151803465040140000c0f00131030080c1170180d203001125410064050080990141d42c0050380b00010100030f4840c40d40d01e130f034041d403503d2601c15006c180c2c00c5a030300811000300398108011101803260301111 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 44157252 1250 44156002 44156017
    0x5060705060705130302130c020111040f0b0705070308070609020406090209060304110105040902040b09100306050a0e0c0904090b07030506040c020a0b0c0705011410150c111504090c1101090305 85
    0xe000fa2070380c2c0440c0e0311080040e0113a1020b504020300f07810b03401c0a86000d4004200075011274000307000d600055804245144a5807088030303c281070106003449501c03450001800902d005008a0b040c582d22900ea1080640c00b8035001c440440c0c0e560140e10071810720b401224000d202d182c20850400c2032250101e1035a100003003005000e0700d2500d025038042c1c0c0c01401030760003401912904540b20764850401108651000580c81c0c89030001d082078552a41c403178040d40c0141d40000d4442e00c00a4540059146005005040108410014401140a078503a84104d0000c603029015074442810510006800c58402900c400d010380d0905041d2128140c0000d1240c40c0554000300000442c7d0f07400242e41054041d2420040c095403d1030100317007441000090003401514801034a4881e00c1c0c4d10b5100c84070035540a02c40c00041843e1054101c00301e407000c006154113200107000c103a034208905d000402950300c50b070400c1c81082d942e600350f030307442035031040e500018a228200200083d1842d62030141c5203004189 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 44158502 1250 44157252 44157257
    0x90b041214010e03031005040b0a0f03080a0504080d090303081308032d0a0b1801060905060306030a140303150f0f06090316030507030201110606300304090f06050607050607 76
    0x4180300c40000d42c4544000164201540d17180d080404072440d5010b803600c44d1500c00d07814034801f02d82ca4a00010300000300d880c4036511203030f40b03480d564400c4101d03040902c81d5800d00c10300b840001031048041c04404a200f10b1540c45800f0f580c15464013034410180986080a162044c4072000c000800704421240c001802e48800702024010340c240031210381008020310b8000030b4500c140001c4039001d8001c0625007008654082c040c90f400f03100d184d2400300910400c40043d41300d210070040e07030605200070340e0000000b501b611303003100c01c3d42c4428010400703030311140c0c0d0260b01c00020045983c41d03c41942201c83c2040f01c006840c8a0118000b4035003048940d11a84207500009039440b456404003c0c10445140b0409400c0b2402c1c7d890400584580d103500c016404600c0040c2d6207111881e020510900c1007030010711b004441d215a0044c1902903007084042580307803d04840010000c0b0082010308000d10800c41c003c078070140003064140550314103500550085401b4000500010710128640350b012000b0f1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 44159752 1250 44158502 44158523
    0x30402030a03030b040902131401080d091208040509040c06020708010603110f0f09070201091101050301060f14040b040f03050c0102031201031b030f080a02010e0c0d0b0406020904020316090b0412 86
    0x7000017402000d0601000b9801124029116090301c074540007507030024019403915a03280c0c0d81d00d60b841d0f194446600520700181070500140194072018481d410940d001e20701103410642c07100301140320a641500c0a841070b0200410030031a0b9a4100310300c0000d0000c05000b4014245155510700f1002203042c0b0a82c4910250035410b1055250b40201c00c0481200510815080c00c010300082c1c000c1611010590710b0b9084081040030550150088a0499155a40324032aa0384100400c5070482c146410a4240c9030302000000350002d2114040e002401110f800d41020a1031481c103c2e1a2010656505044d50414040c42c04d0039100a203c0c0d50440e6041044100341600c40c0174010b5240c84540c00007400109104001d006010b00341d009020001842d030020070444055941407680c0701140a81030307520916030030300c02c800911014106a00b1520034400035041c28106d078009000c0c1d0b081200c00c105034440108130749000c141d00012140003005841249480c050070203088024041006a0282200903039 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 44161002 1250 44159752 44159771
    0x1140a08090a06020a092102060315010314071110050c0405120109020a09020d0b0909060105060a0e040612230607030c020f0a03080910020405030319091a130902030402030a0303 78
    0x3408200400c90f80710320219602e0032952006407804807180a0740a038001220b0130416075084c8800c00d040f085800038107039815540d440340380300441045940d1880c1056140c040034000a0741010600340190f10359290304100241b1080118500041d00d11407c503030030305140511080140c3e400c01c0b5401d8803000c1d80c4801c032a1807421001405400f4441c0d0007034001c901400000307007000441e4060a0314282581d02072148242d5035003084076184082da07801810b604008010032143c680b540003400c0454072030030124102c0400f10001401c43d48a98028900000000d4403407040140c000030200c2010302141050b0f02440403582c00301d07036840c0000e04d06d400785030b42e806a001c2017500070045094242c0c4040c0407600344002d10300c2d001744443ca050f203001030a4810010304040b07a10443c0207a900380c86025005500740715988002005003042e0150031000d00184210200b078070001c4410142a80804448055403283c10901c0c180c10b00c04241e00401c0083d2050080c1b00069401250740c2d01303515013529000c0f480046 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 44162252 1250 44161002 44161021
    0x1505030c04060332010f120209160e04020d090b0c04060f0c170d06050a080106120209100807081507030504030f0c0606050a0612060b070c0e070504030f060e0c01140a08 74
    0x10004c1c0a0414899180440a503140d0108486042e90712281204400a9652110802c0520030800003540001008002407410310000101c0040c1c1c81c041c075140209903100004102240c2c81400702d42030840e20342d43c1240a004000030321a8020940b00d0041c2d180030315101005040800064066041000420a050074842c260a5900140440f60101d40e03039607400c0e00140c40100b04511425009032000e00e0001074003c41803061408035004541504040161a400c00981c40f41c003d000d4041c03100b088030080303002c0104000f0480a810414014900c80e240c1d0888000040c00042c0348404240c100f40c00c21001070380c07260030310003480d400b07051100950341c4504e0041d000e444280c01a5400c0340c0c030103c002500300e030300a40c044000722002c0820010151204690a07403072048480203044901151400c005c0100d00c134440b00c0c0d1180c41d52519034141510780d0f0360303a00c0042e544001070b5030407a01d4000c00c0021640134004005001400d017040c044409514001400601400301c0343c109210646000490ba07a1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 44163502 1250 44162252 44162291
    0x2090102011103010909021201020a021009020604030605010803070c0b040303091809020405070c1505060303090607050109060c0309060507090501020d030e010e03120103150506030703020d03050918011505030c040603 95
    0xb210a00715545941c1c5070a410801401c5000c0140d00c103484030001e64814050610803101318011941c06000301d07002c0b0780c0d00300c0003400c1d02031000c0781c020313008000000104010340318042c0030f020312038013031581c8190318101825200c11981111000b550108020000250803569010803a00000032100c09004206000c40c02006c10460207501301e401c040c01c01c181d10368002840748840e8813514950b026080d001d000c00044074021541d0a405034010418000f0314900003024081d018818400815100040d54803402941d0b1629a4107011035103c280e010200700c41401407660000780380c40c1c10490a442c1c500000d5a964950b25814180340e6184904058080207401c0125101501c00441c0d03510305042c010010221402d220a65003601c002030307086051051401518040c14008006141503400d507000c2006417800305108505000c3c00b08001c05498650001c81030710210585100f00d501c0d8034000f10500d140e00ca8600a200b042000c104101219000d80b05440503903080b0b02d40010520703900e0703200b0040301c0e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 44164752 1250 44163502 44163521
    0x608071e0e0607050a03020c03100b03071202060d0c020303010f05090f010b0c0f0307080d0c14070b1e04030e030c0a05010801090f020c1209040c08040201170c1b060108011508030a030209010201 85
    0x307020392045d08051580010360600c0c04401a001c0f01c9c10025210320400448190340d000d40c1e41074000000812815040420b102070031800200031611b000b00e180d184404075400c3c4011180580c101200401000c2081202c00c0b0040c1f400303a403000100d241c0714250b10400c407014000c014803588040b8408a4034041040104c400f02246c0007107a13510001b0381022150f98005c280300f041c09504040000001e1842392000d0940c03601d000000d18142241aa030f208420700000f003101c00000010302c110f0104403071001c8201d001c4c9000703846210112030f10106050411f000030401d503001b0410400100541d0341d02c9000541100c0712010005182114200d050300648140131903c492032182d0112450428981f4008100b1500100c4007084070307010340e140640f400308013250043c0c0460701180d50880791034001c3c1c0e1026440b100341c032000351a04c1c00d01112694881038038009600305611030001404103440c24882d800c400030500210003401c0f482c1c83e100554a124040d03100040580208170480d50342d00075003005058 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 44166002 1250 44164752 44164763
    0x15091401030204060504060f060f02010b0a0303110f0601260c030303040c140405010e07050a0216081b062a07120b070e090f0106180902070b010608071e0e0607 70
    0x451100a820640102804142d00c41c034503251001036186058807441c03044035087c40070020030030300e0040240d50400e05014108255501e40d10700142a0782c0d401019006144652551150b02d0b000c0c1400505d00340341580011455842000140049070b0f11380c1801301d9030b4101c0801103008800040c08141000000035215405200c0482800200107003240f03540b05446040c01c4803001d201141c4100000e03158203200c1ea003038418552022440c5a441000141101180e80c0126810a04810218007020a40e44e20414098000070205010100c3c6100880f82150781200da80c2d0414450382c044500400b0142c2080c00c000142817092208648207010b036000406455403685034402050800080108080355804000380e01c0c005240440d107840840700303006a03c182010701040c0e0030103030300b0b50300040c1501192541900106001481d03036410b00080510910441d05c0c03840f0b55140c42000f61900c84041c1c507000900425121241c4a140040409865084189002c00c107092030200443c0903849102805000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 44167252 1250 44166002 44166011
    0xd020c0d0c0f08060723090d02030c18180c09010504021b10020d0e01090b1602031b010b0405060a1a030c0f1902060106030204051c05010e1501050f040507050901031509 74
    0xf0840e00100700c145c07042001e81c80d604143e0f120000426801c8a0651505880340824801c0070000d0034559501804140b010301200e001c0851040000c0d282c024000c005402c9114000030404606400f5280c240380d80e4251008044a0401c540080c0340d03020b0500515008580c0882c141303401d000303075000300459081004c0a841d210341d100c00060010b5407000d43d00a280e2400c1803080c1d15000f005201d88c5100c1c507000034545045458040d4140c0c811140c0b80d0351041148420b00001100b90100c0c0c1c1203d4019181d4400058108416001d200940348003c04051007850a42c01c00c002962015013440b40c207180c042d1400c0d54955480d1007548141c001c1c10240c0784041c02c00304150480750401200f00d8414220b64084a0035a0313a40c1804070306901c00d0303004140d00305c004081144c40c0340035082024a90184510004541400380c03500711031501c1d4503034011200c1c444071200100801d00f80401c03844450001500c050005161079071024000d4403d0311074842c1010b80e02d4580c8407002101d025283c001d440240414030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 44168502 1250 44167252 44167259
    0x50a0303020f01110c0627011d0609060f0a05070c0b01090906110310050126100e070c0308010501080612010e01020d180507030210030605030106030f050f0d020c0d0c0f 74
    0xd40d41d0311072840b000c80720341c0780c8441c26030b0403405001a0340a400c01903000302002c1e520750311201504841c0090810681e40c1100341c203580343d0401c1c0505002201a2808010048032560701c1c0e525020b000307005151190020301c14061803510800d4056030000e04c124001c2040e44501c48200d40524608402a003007544010001c222154290401c1d45410700950080c004090070b1090600240300507110304040000081c070810880d402419802c1202d64100088201890079001c21219810200d501f80d090140c418014400f40040c500e031366820200624110514503030700d0360301506c40a03040c0203060621034a500064050b81c0ca61950307490090f0b810000b4001001000c100c0c40c040c0d0003840075802c4e0389007050110380c24008100303115282d01e174016004214541c61a002e00c40b2451010001c103003003640b12040414030341c4090142d500154441c1484100e6034078541400c0741008401d0721082c1190304040d10b80ca04056002a00f41d0640c2412600e00c00645401d2404c08049200c95009001c032554402c3c001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 44169752 1250 44168502 44168507
    0xb04031101140601050a0311121003170403020a09020903031b030a0e010503100933051503150609010c0203011505090c071713081504150c02030d0b0a050a0303 70
    0x1401a00c1090009100c1507007615109254114100c0304540003550a100508900d4440d401808504496401d4140340040b201104180040b0403a0703140c0c03c84088103810000c100b50b044189100d01c103903080d1542054110781c000780702881c16210380d080881d001704150b511554240700303e03580310011507005004800c003010342c0c980781e800041c00303032003c10042102c80450f540258102ea1007a00c2030b1322010200c60410161400078100310030b88548500300000320444c00d00c9030040003401008144500c460452a00c001c0013a4080c6a18080203038400900901a6a4801d10303040d54100400b200d2860b281c4000742d004a540d40c0d03809802a60540c2084015409100300120403020340d0002c3d241c0000030741c2c03054074683c030034071803040001e01035030044c000f60200000d08070240074090f25403850b0f12030a9540c0e280891501d080c0b000002107110800c1c0511081008414268080d100d143c0c2e018040c0b4000c20f0000f0f03490f8000c4070f511110b03041d2520502c043c030340e442c4c0c080c0c000603040050035040644c0c1c507806c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 44171002 1250 44169752 44169767
    0x20708040803030a1a030106061704060b0303030405030d0b0103020412020d03180306091109040201020307140705090a020a08071103041a2107030c02010506091909170705010b04020c03071b030b0403 87
    0x1020f2170000002c0c225143c00d060250304140e40b0941c40395110490515005480340c84000c1c000d444460341d031448034125607070900017540124007078030045031504141c001c09804c83c0c04d41c82802c0d05151041204028091103010342401c81a0101c40d17088041e01e443c1030948018004181c25110450100004420030840e5884000b010703014a0101c800c0d00620024031103d80c2041e5030103030160340284071031000242c0d65240c00c0f460881070010384602036600e10100343d15807401d0f225244c030721b500450700700e40345603104c4200307603009a0600e0801d044181d0b00d0350454480c480e6010305000104098918074052004000301e42d04440c140e1000240c0607404801140269000ea0750840024100a0f0005030f80344140101c40c0a4000201208100c0d19103201d2280c5506540c0c6a0300e441589844950010404036000c04244031f036044038056448020b07240c1503003160720f40c20034684203d10501240b00090720000595058a50096490030440400000405800301c0c941c00180580c034104100400c1581c007010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 44172252 1250 44171002 44171021
    0x606050406021c0c0f08040e04080702040509070e0c130b070302010b24090d060b0904210c0803010b090d0c030c0608090c0906010e0109092c03030f0604020708040803030a 75
    0xa8030f0849100d02440d00c0c4080415070300310001a00b641c03540c1e01141e4948441801c4521a03241d03a17141c9603890610200000040700e0039181020b012401c1c8007542004c1c015103500c02c1050014000031410103024609006018144030b1a1110220701c0b080003120103440e08001d4516521240d80360106c03031400902a01800300c1107070040200420f00c801084090349d841924100c00304040c0e0138003006500b070001e090f1002000f40c854540303581da6000181ca5070f010340c6000764080c0410044441009811203803210200000c2010407201c0b08a13500465065016681924442d0035001e0740c2c1d03650403000802029224074054400d601001d0000204071641021000700c81d05610744290390b0381c84503038070307034403080d18582c469040b1024000164a80d172203900301214082050602617680c0351030310841e608861543c0e4414003100c2440b0268041c141800440300003080c8084020b5181d071401d4650946020070182c034213409181c0116a400420030208107031006013125408803916442c2003002c08000e00200034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 44173502 1250 44172252 44172257
    0x301110712170907090b0109050d0c0303020f0a0503040302090402030c09010b0307020d0e01050a120609021605060c03130b0702030f19120c0516050c041b020106091803030c0e03010606050406 84
    0xa42a00b540b1500b18288a140c403c0080c1550b1403802100d10040c140306581e0504100290701c022030076036903601406e117405000d648801441070840c98040e261103281d080c005900e0340070118242c00280c0c00403c50303003680da041e20714140c5512203102091810306441e0b040341d030041c1a80c00114000c4043c0020b1231003030346968200c60203602c10450555011134040314043c00518100f24191025000b0a01c0d1400e0f0701c4078030000130300141e54106000481e00090031020142d400303071814038240704c3c0c100403041e0800751484a09155042400480c403800011001c010030000d025000213a00c14001c0c81610001d00c418590726581c3c00c0c1500100c0c5240e410300400303070045003001600d820b06807002d10600c0d012481585031185055130484008460715641c131400c8070503100e0f0403080080d42c1c0b0f542c0500483c070031542c2c5445420b0f000f80034010f030956a050300078150803841c1940115200c034048d81007005464160a0004d160801c503203040720307903580444449070150700f05400080d200f5842002041240c441d41e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 44174752 1250 44173502 44173517
    0x24040e0102071505010b0403021333030c0905010b040e070302070c0f0305062a0c010905030c030301031401090201020c01030e2418070e16050d090f060501140d0602090301110712 78
    0x8030000d4006d4011030001940094006e2480c404002083c0d1007110f017a4038060b2065246e50800c480c400c042c003071051001625070302100b401c20400841c280d801c0081e0100b818140255810301f4113900e4903016900c620409000c1c00c00100300342a01990403200901c1d0417401200b01e00340c550913551a2000341d8481203a462140700700003a920354440024580f0414015076003411a0340c2030707561a913a60411941c04209550710b1004c0000950700b0401400c00e48044d50103991650b166083c2040720f13180b00394945020784d0401c13507180c0040c1c0c0e0206101b2183c1001f420000b4a1514040e00c092400c681c41400b0319034842c03441c0c400c014403042a0b6501e441072400103010314003c0b02603107469450710080d21507c3c21100e010004100c5595400848201c00e0070507180c03c40c18130803081c01c00b6040d07845120f03040c0e0b02c0210041ca45028440365000e104e000d8001030f10f00b200002000000300310440c0a103140502a15408103455200d5582074000120409002d5002c6443c1e02d083d003014040103a40391004004540c45 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 44176002 1250 44174752 44174759
    0x1b03030106080a05131106090a03060501050102011b0e06030a140403030b040c02010903090e280510050d0503031906090e01050f01120201050319020910020c010f050324040e010207150501 82
    0x9402076070710a02151010484600b529a070741240ca10b89031a2241c2e01c03403000d10440c1c0027a19001140c6004600a904c04201d95250000190840d00e030030107050041d000c4040c5088046030000103607003111606071442c80e0b5030b9a50f07c815200408101404011640f083e8090006040d07050704000e0161000b12400c12425900001c16801c031a102a00140864018401044a5995100c2d002d038011281c46520500100c0b0b100045084025024100e9038190b83d5824030031a0a8002508800742c07034187e030f1000213102d89031901c03030380c2c1d000092252410440701d06600107452119080803004140089007408400810501c181c040d00003150440b800d03088403000090302801c1113513841102c0c0c1d011703100d4515540f507100500e00c0c400d13403e120030a0401c0d000c001c0d000d210303110042d4010044066501405288196100040500b0801646442040014024403901152611640d0ba10080c0000055440e81c3e40d440030402825114802c4c2c13070035510120b507100503c0b1296545038080310564000f000140e1300c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 44177252 1250 44176002 44176021
    0x605060c0705010c17040f03050c010819090c0302030d030c14180105030406020c07030804150206100909030207090c0503010503060c03071202090409050d09180522081b0303010608 79
    0x5040d220300281d6020032010801d5500840ca0444140d00588508603900d043c0ca20201c02c550050f48007030501002400c0c108107010f03003401140d21001c0c003440c00101c181808810040c1010084240905650303039103050404000d03482d4410750003568081d0689808400d41d01014000380f034440ca203d80482c0c0320246090180e80d41e04105c501040b1a2884544064508801140c0c0e64100a2080f01c44c20350030800306c2014581000004004d522844990380c2d15801c04002a003008200c0c4110f106560288060001c41030904103024241c03002c0140016000f8401d0600b03c1c60b001940c0e03c8000c0041c038150100b00300c20740c003000940c140d642c140e04071100e54642010044091004442900000e58100c0740d071042c0041c90f030000d103000741c2c0040001c21521004d031140c500b423004040d40000864281c030010000d0a5448001603070040c40001c08104038540000003407428546282d18a801102c081c440108000d10801655402424111440000f8400c01802070b9260300a004000102d5a0640010310069 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 44178502 1250 44177252 44177257
    0x801022d04031b08060103050a020f0d02030604110105040b0c0607021606080a050a0605041406010210060323120705100f0203060105180f04020a020105150316180603060207030c0501060506 83
    0x10403035002924003442c5031540409510041481c0e1060182d250300002da204041224a0103180075001818050034140304220a41002d024010300501210143e0320140c2e0300804c0795907000d600301840891b5840503d004890510603500250030620303020a030452890000624544150815001c07901920408682200b85915520030b0600042914000603103174a01078000c5500600c00040110302d15884100107001c2d07030381001030301050b51001030401501e0341e8104030b518510380c41600300700001c0f400c540b41d18540e003c1806004904005100c81801055001c00460b4141c0c0401340903145c94101601e096074640c00706540001401d42840f4005090f02003a20803240039000507101d440c5032440b05000480204600d1801c994440a00c000e900616141c60008140801c80c540c0002a07a00c1e1031440700560702d0b04030102c18003d43c042d41466150b542c04020078419920646400900301b400000d880020b801c0c980c0006011030300220312041010f8105004000152050001307111058442e018041c660 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 44179752 1250 44178502 44178577
    0xa1a090a0b0a1e0e03090a0b0a0e0d080903070e010326030703090203100c0314090a02181003050304090e061605090f0f06130302030d080c07020418020406080102 71
    0xc0707031004041070301034030203900007460055070310040300c2880158441c2004444e241e00d40403015070000600c2070031070324002c80008040c1c641121524101000c12100a10081c40f94185602a85c059807100d81481038000907116040c0004044640c072984075003201015420a01c8215211421816000a09015621205031030fa41c807440003030030742d0355180084028120b201003e98050260b800810b0000750240100c0c19075504c2c94901080c0d0001805049410b040f00401036002070304900c05050044e07940044040c080440b0644540243c1c079003204100782c0c001181c0c00100240700000d000112907001e6000816040d42c0c080681b04241c2da00c3c029811a902c01180c035100040080044440074540a5084189082d010b40506c10712071a01010507080e900008040b0001d00112030100210f00d020042e01c6210f850728500b8140d00d0411150152050080c2c1c00e0082c8299110350445010840800464480940090040c0460307036440c0c54140c000d600c00d00c41d821b031044000c0c51825507444070410f0300368603 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 44181002 1250 44179752 44179763
    0x10c020613062405030c01050403020a0504090c080106030f0c080f0a0b0903040807030c05040c021b060304030c05060f01060201061406040e070203090604060305090624010c020102010e0a1a090a 85
    0x31551480c00d9906460080704040320342568481030f00b450724040c814803001021a41000003140790402040501d040f218865031410000d0410052005858511103034040314401c0d503000c281c21186281000b20711302160170140166180c401e0003c24048103645071400b2502402c4407001c00c0343c990050302d4031051014907030311040d400300a02c0000200e29800701c9030301c01c0c8110300307072410140c40388512401c14444d50310941c0d0906910740284100c1c5490b01c5048039565035400100403d610043c074085840c643c1901051082e400440001c00789400b549040e0201c0d9406030a0b90054502103420319124442030080000662901c40045000c180c40d0480642d22a00148141c0c01c0034035100311081d8140004042e0750031400309201d0011140c03609070181002c2c16450b1804107082ca8030011841c44c1010003030040003e03860504001c08a002c8942803e04814000c1c0b8203001b8580721400140d0141c01550194101e07885400b45520600c446142e051080d525980c0c480c6041782c8401d100255250344555003c0c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 44182252 1250 44181002 44181013
    0x18170a030f020f0f0c0907090501020a12170c03100503060106020c0d0204150e15030105010b0d02030901060f320105030609090708070306020a030c14030106121409071502010c02 78
    0x109000c0d0941d803455010902c100c034201c058200c005420440c0c0ca490f1050300703510181e840046890700603074280d401040340c03501448607441c01e00000c0d65080100d0b0042c01d2900c2c0b003480c4143d014030405d0050b50801c0c80140c0e480444c103115501480319441100c60686210b200000403540e0301e40461040d048071015801400c12043e01010050810f4141c20304981c4150b5410700c00d00e4141c2c0f0b5003405070007130800000c1c0480b10701d4020050f400c01e4001e400d0716482039151100600103180410b041c0c480440307000100503220341c0e4500c02c650040145800c400c000040250000a1844002413001c503105040d00341c04094410b94124a4105550754150602048041c0b00180d00c0e410865002c80d0b0021448003100c20269a80411604082094206581c9282c0004e00c0c01d03203a98160182c1424071040746081c0c0030041c000f2480c000c240c00103008002c10801105442a0541c0c070f0382e0880039400b0115410440c0354280011850b5444a040c45003031100d4401100c1018140d00600c0b403005002c1c1c65401420b03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 44183502 1250 44182252 44182273
    0x1503010c080402011d040207020a03080a09080a0c120305090a140406061805040213030609051506010c02010807081005190501080c04150e12010203040b010e010906030312050703021204031817 84
    0x4150320b61034172550002d0342800a46c3c05a603071928450700940c02418000c2c0e8070704c0449001401c070380443c0c10400065011079a00c0000410421007542151f8410325000420000d5240484041c803940c1c800c01d0344642e102e400440d22403902140c014050750115010444903588410648900ca41c184600400c2c1404a01c100910308154000389920b010185510000035102c0ea66a4112081e804066480707502040b400d4582101c0700303e0280e004031003401e2000041907141e000802c401c00043c41c1e5000c1115a43c04580c01d0280341300031760090f00c4000c1c900d0b030722000c0c89000d000a200c01e500c265030010306040045010a91407100b101c0940345000d0004a080400d040c0c01d50303c102c007090685810004160704101003070402c0c4040d42c0914815145480380f94501590780a1060303040e00200b2141c2d2900004000090b0020414800404107100109003941c2d0380406900030300400c85031203480303541c0300d0030002013541c0600c04141c000c5801039911681501c80d6280711025246104d40b0f0721030b901c41c05040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 44184752 1250 44183502 44183537
    0x50108060f0303070c0f0f090b030316030e030d180e061e0604031509020111030c0304030b0603120301060215010b07110d02040608120706290d03110102031503010c08040201 76
    0x1c40491400340840386810f0907a511140012950350201c3c1010501e081d05100b000d215071440700040030380580505c0070003801c3c0700080d22807145e060540c01e580b6071258803004240c011080c0340291440113080c1d43c00c0c0e4400404c0901410003940840b400388041010101e41d0320000e0702240d00810018090030138040011020896000c03000c4c001650058040c08000001640c4001a00300b00111000109000caa144000341140410310070303803031240d0824000301c0f1152100105072004c80303400c01540505c1c1d840310400700c1e04140f0380c0403102c4021840000040742c03443d00000d007506556500c0c0040000c60781e1b0392034005424015280d000301030018102d102c011f9850180743d24a540380c00100300091055071502034620f0042003280003101d002d0040b40d80000d2040910490205d51034141c50116404504110304a8490700148268810216100100149440740404000c024a100000c5599060101610f2001003500782202e200e9070030b0403015001648078020160245506031a061420070142010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 44186002 1250 44184752 44184769
    0x907080c030405070b042c040803130309090212010e070906050f0306190312020d03050405030403060228020115080a0b0f0a0b0603010b04050406050306070804060b01030e2e0605010806 81
    0x2e5900d442084d8001c60203d011000030070040005100021072019002d9000d2120401980403080311500b000812010603040001c40303a00294a00d40580030610500c0c003a074010050343c1191050754070200d41c030822825003820070307810f9528402040341140e0b21203030102d48509090041c10300099060104800d03110a80011390303040b58000f419180c0a0080e003038200d1109a40f540305031541c40360f0348032100d60070f0f4060180c00d59054443c5010b0204d40303031944445641340b14511006140e0b036800102c1c1281919250880d0201c001d10180508140d800040000c0c0038000c0c0ca03240740070a0207072141c006000007000540a071700947c09030003101c4954581c803000800c00790040812100f50344518801019595110082d8003030060306020603200d6040000344001c55050b03400050090340810140002641c114004592043c2c0c01040440d10480312001280644001d445044041c405e071842d00941030300c01748a1a8042c05c1d900080408075046080400c00d4800a100f61400701301c40b000861645d081c843d40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 44187252 1250 44186002 44186011
    0x3030f042f0d060b03190b22020906030a0215070308010e0f060108190c020304080105070203130306050606070b01120b0f012106090c061101060605070c1e09020a0507110907080c03 79
    0x400180001414010a0030041c41c40c810b2203c5a004007002c03020040307c40c03130442d04a03001e65080c91205a610300341c031014064401020348503c00c0e0100041c965542000740d0300311558060482035904444824403406500403140480100307c0d98000401c40b80c5080001900c5401065070100c8551151401036807031000207412540c24901c6a200d400c2003840b50300451180709500d60041d0740d50352610602030308590000c2c0583c02107400c1044004e11034600070703a090041e26003040b00000d40751603480c00036a4510a202004201c00b0a0340000100c2c11a002e001c0c15806000704035001c00d80d61488850409030300240110403800412021650a50034940d504000262003000005030100706522070b100c00344201d620071400540d5060221005450a00445d0f00404160506604000242d620403080841e0ba02410f50307648804181801e036214441401401020119401c541e101e928a400610360b034403c0800343e0301160410b850301d01e039041035081c40f489080169200c4859840750600204254400382 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 44188502 1250 44187252 44187263
    0x40504020307032001030b090609010312020304050a0603050406200a140c0a0c03022d010309020301140a0b0f060c0307031407052409010209091f030503030f042f0d 72
    0x12000801380401110000f80d071001d54050b0041c410001416101c2000c5414095058041805035a844001e0450b054990107a041ca002c520740400480c550f000d2130780460f5014000c1c1400090b15900b40e0302460086014020505c40c0c084809446a03a107010a202d20300c0450b020045a900d50307109801840a480301e04500034986129014080c0c41e2044907103041c2c4003240d88420030030440c6003403210480d021801c0c1d40034420000d680d9510310116203861034040e050549a000482c00c5507001e600c12048140c1320000c660072401c001c10140e008007a00d003035140c016810182c0d00c1e000c9107400c0058900d544aa000114507214250740c0480e00100311000d14070011109101d035800051042c84290f0003001c001a4528022014100d46e4a125201500c500718603481000603401ea51200b00b13074594411240942030100e049a0740d14200f61076482d9101800601010040c000501e1007424820301171401207581c100702000f04400d80c0d580382c0d04860840d0003103280720002011403c0000c40140224000c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 44189752 1250 44188502 44188513
    0x1905060c0a08070506010e06100203070314040b0c100510080606150903060702030d0c080609070804030207090204080102090a080712060915050705030403021c02030a0809030f070305070308070215060405040203 92
    0x503614034826800c101c10844d02a08000c005004118080d1130345540580101e5030140315012140c4065204e104018001d010000000c001000808070311045600400703e04002580c1d030700035154020340740e2110045407003042c0d0401c00030821400d40303840718100f0b07100c09001400080e00c541c4100001c032207924022503402c19051103003644a5406214281c81400b10750003030741e0340764940c813904812961807640146c180151b082c1803001d140c4903441165482105800c0040b0562030302d046c180c0c9841c669520802c151030000502084848041d000703080c4000f0245e41080b45551204d075030a4a82c0fa8a00814601c54040300681c030102d082500800c60b8940203081e150200c0c840c100c0007400b900c4d001ca4920307000c80c00000c01c1c0420540d041081840288104489241e010042c000003500c1e0700ca01e80d1101c0400200201040311900280211056134109010071a81c0b00407a150140041e0400b0000f034021900d0100000e81c03160001c01c0501ca141004600300d0480c1d0b980c18100001008046e006903014806d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 44191002 1250 44189752 44189773
    0x810170f0102130e071d040209040f05100609080a11011d130c11071503111603180902040812071401060b0d0f09050c0f1f0f030b1905060c 61
    0x80c40103000000c145004020700c0c0c1c3c04c11030603803284600034000c0e00401c140c0c08642e06030a0050044556002821180940d803031a03810009000760001b5020a1040e07440c180c1800071340703544601030108030341450f140c1984003680c0b202000d0b1624007414002e45115042d014007030a1303610070240c0c1044240954aa545064980e5011400300c0c8984907000b80481e03036507081c0d89245038000e0901c0c0c2d16015040d0040c1030141c1010b0010042d444003002a80c181515071409528031a000015a0040500c00c19444503515590400801843d81d100e171031003540c2d204540125401c01c2c1402180c080d40c0a100060410903402e012840e900e40c450001030b00c0d4018145080c190b940b0b420700680004180b5040b4103622910f40c00840000c0354000f85900c030004d4a021041d20010b080415a00340405048034825064042a804500840320b440b44501007000342d803002c1014150031003c60700400e101681e0400500b0609000d0101c6c3c3c0706048114140402420301c10455407400704000d1411107080c000b41d5a17010103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 44192252 1250 44191002 44191033
    0x305030301060e010e100f0f0908120a03051f03020d0206041e090605041e0906091403120a0b0303090907030e031305032401090905150403020c090601081017 69
    0xa8000b580054400c0d1818819503a00c513000102c51a02180d4000d0464920301d0050f00740daa49031507100c03e00c40d00302d01841b145401446811f004050a1007a01c0c4001100c81c2c001710f5550107062607101091520000c50100724440e1420060780c100d040d203550b8424156002c200a50305e00c0781040f40e100704100404220300492024541081c852010165003807402d2080510a071140d50b000140145c1c50014034000a80355040c00e000b280880503000a403085450038400c02800c502c030301c0640309400800d0b05000340e13032000000340003034401004000c030a0b4403074165080541c0c0704480d80a03490f0b407043c04035081d80e140c0710032540c1d000221420002488001e0030300d490f0540d0412091000380e0003012608200d68141031092032024511821081c40c54031503011420030140040c054036124075520303a0340c90304000c81049034200d02031007244108050314003450001c0d56500c107400300303078024150880070442070f50140c02054021440031a521508074200342803071100001d4401600d80c00d00c51124032600840 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 44193502 1250 44192252 44192257
    0xd1107080a0206041104020a120b0a0b040b070b010806010e010308130509130c15020601030f030e0904140d0311030619030c03030f02150403050702040b060702040f06140108090601090c09030503 85
    0x70098019042c246094188040d800044614150055004008500e80140e1003000c11002205011000980d42000350202d0b1038000e85400a19441c1e80c00200441c1c000d05200c0607003020780c0308900c4140a41c0c1c907104080c0d220002032064101040c21280107200103003034072024000808800502e800d81c1640d5500059001c03034103070b6080040001c00094030045c010700e080d0304005841032580440c654844e2031002565183c1c14070000d0440307d00145075408041c840c006005d46510000c18904960401d401c02010f4101802c10310a5144188844446201c0c0a40929400503554106241c155640e10050205408010058030045200300c1e034040006040640c1c0a000f440c003d41c1e41d00c001c08001c40010b46490700c8a025140b40441050070040020350042c12500c402c1d13030541340400d00081c0080410403600422034003e604c0350900407191040c403456800142110a085458054074207101d00541d060300c010f035031904150f00303c0001880901d540b40c0100c0e80c45001450070345003695403a19100c0c2940c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 44194752 1250 44193502 44193517
    0x70b07030c02010b0d0b0126030a051803060601020d110c06070501020307020114040c0603090602120a0b0306010f0302010c06090503071704030318060f0e030f0f030705010c0905060d110708 83
    0x1079624011401e0841c0d09100b1041c00d40f90580d4410481c1109450365014032405206642d083c500c0380208000c41910a0210910a980441141d44420a40c203018106411054049402426501d064802c510780000e03024007070341d810307000b42c091107407242e00c11625001c101c03070a001d451082202e0304226860325001401e5140c003a13000144c50f41000c1c0802801c0d140000c0c10b1b001d001d80c0390703800c0c040407442070b001d1030040780e00e1801c001600d42840d01c1c0c4100a4080e0394442004014044108001c40c10140c010740c081860031026240d06070388558030b5040380c0600d40000380c0020b00707070b5201000084145c2e01c601d138aa4084c1040b40e0410760f40f9510a07515681000c212038008101003000c200301034000c1c0c0001c500742e2680000b180c2803070403d0001045102c4c02d442c645c08100e05080042000c2d1818840103100031b03480c500b95101c214102103455502da0103890304a0700d0350318080038032815a00c40e20800d0190380000345005d28180b40c420342d42004d0030340b02c60200b100c4241004800c002075401e80c001c0404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 44196002 1250 44194752 44194757
    0x105041d0103020a09050601051c0f0507021006090507020c0114070b040c0314030304020d030c0f141b042c030409090b070f021b120c040501030503040f0605040524070b07 75
    0x103541c114410b00681d000c8603802803035910305020600a15a8100d811b81d80b801500580c04400c030b2288004800c0900602e0702c7c0c100384c40c2d103040c0c1130002080d130201d010864204080002e015007070b65036056138100d403821603254005803c00032205081c7e611800c842442d00c42c560a00c242818002d840d049150002035400b103a00c4402c83d4010000c000b8000c080c0c1c5507048a01025609500c2d050b00810103d040e00303003000b020811541301e800104071050b4144500c898202248084640c03a4136165035950803219281c1928507402218001a4505406646039005a0003402c501d4003d400b03001c50400c1d2404941e04000c1c0c0810702c0045005401485002d51ba03500400611099040100c4080d0040c8a5402d500046400c94192844101e40604002c8a581002e41d110b4000c0b2002041113400d01708070a4695a000e414074000000b070003c000060310a07102980044903400366680c0007a02ea038400c902c52107802c025451083d803018504256100c0e251007102490528280d12591a00b0b01e40c141103899001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 44197252 1250 44196002 44196059
    0xe010204031703010602070603050a021308100b0a1203030203190509031306030b010e06030703090b0c0304020306061c08090409060e0d12020c120903010b100e01020c04021c0902010504 81
    0x60205580402a62550b200319240c503550601e180292600118021502415140d82c046224024290304842104880d05080303144143c440111079202c000310400903d149061106e40c0c04946011740612040350a21840c4008104643e41e00360081d4000400810b605201482d0300305008160b40101c2d4481e130300c21000b455803040714803075505000d0300d41e03001003040500d01000d0000350391300181c0300600488204e40c40781d200c0e03031195411030103490030b0600145070783d940c1010300c225516510065401188203d00fa0349550780d030740e414802220907054601101200020203940843c421100606480768090800308030200395441e20020f0341c1c080301070f0300c015601100702d0701c1100340d1145298400b1515403409500d0b0000f40c08821740c1e244001030604007100f82c000340740c094640c3d0940c030903042200c020f01031081d48840940d0191550340b900e00640e026024084010849180610031a61111041d00d0042408102088903500510400c4002c905000e800c0201041c00031100001d80d8103105030540b0303c034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 44198502 1250 44197252 44197259
    0x180f0601031a1006050d1d0a030305010302030f061e06030c060412030f09060e120114130506010e10030308090c0618031204060504150905040f050103020103050f010e0105060a020304090e010204 85
    0x42c8618401805105001d1102006008895001089491501403410085810381020340790700c0288481000c441c9007880f07074020031000c141c0c01d5040241224004c4080d07a55610303c01101d2a101c16041b901c10346596251030f200340c44920000d010316040039015007281c400c400c000780031854503070154109140c0d0602c082c4440301010b0b804090403000c0e02e19458400790081c606000a0701e07000c07a031142e081c0704150f814255680e000007544640e0301d105115403160310904000f00c81c801c02501200c070680d0240194000401c007507810100250044a281c01087d1001d4038584003110480009042d200480c010201002c10a42e0340340041e01d01000c94900078411003000000300f52500d8903240079680480720030b100401c4101d800200fa84c0c200c0f1342c504407a554500c98a4401c5990b41d0361a000180d1007440c01a02c00c50003c07a81d800030703050300d1003078034100a0f6485040411440c0c820034414880d05c803000c60b0041c07141d4101000605003d501c236004890910741c4518480d0203446001038020456940800c081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 44199752 1250 44198502 44198543
    0x60c06050702010b0604090914030706020a0207080c06040909050307142a2b050712060b0f0f040b030c04021909050108010602030a08060d050d02010c0801091103180f060103 76
    0x650081d0490000b04034001e0081d022031154021441590102550f0310520001d00814040710003e9800080c1038a640d0b28103460654001d4000c07090000041c0301c2c540c4003040840d0300080280440c0c4008024a00381031030540710001034080220308032035501050101c0800103490090102c2808000009400c10383f092520048500442c900d507151040d55812890f102602c480f02464861202d501d02400007888010a9008941d070f8808014184d210300000041c8054036030070b00942e0680b10310400d1282802c20020014103180c81d100c03056120403014484421803605d544081e01081e009010354044100040c001022078001d48100503001c540c40d0f03201800703075901110b600c2c0a4902402c1900c46541030040085d85ca00500d0b8442e020310500001203441550340e007417044c554582c44802c8480c50400860b00a020b4459036110b4000b180316440007040c9160b80b4001d295200e08561030403030039a9030b10120f0340303041540f81c5400d018a00030505002c1a0f22030512407107019502580e90360300d82d104200d410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 44201002 1250 44199752 44199761
    0x31b0b0a0c050f0d0b0a051f02010c05040303021906060b070c050405011703221203020d020f010612060209120607111603020a031217070207091b020d051308030301060c06 75
    0x1d00c820080100034015261070004191030f001e491240d400244200c01502145c00e1040d5904166402084101841c50402d0384200681e90b0207c150300922060781c40d0402616035000f1404010056080001c0f00c211441c0d001450903100e5008550205155aa0390300321801a88501c400f65201480c2c10720520480c240fa009841c018201e115941219070502d081694503030040300c8900c6145482d1000c00801d121000010a0181200074400921541540780103595034841301000e50160092400100004138184030311011038035101b91042e1584442c1c0e031202d0095000a51455002d0007444101210311010405036100d501c4540700d4885840e088480e59180c485000450a06c0c1d1112031028001a01d5120701401200e034084005925004901d0b005d9506100c408401b5a102c000003080182960b4002041001c50744801c00412a0382d00820305000c031070112560010250f40825140d980541c8600001d0180d843c0c2c00c2d150002a0780c58181c0036045905c2030348240b0001c0c0e07120a1240601019106 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 44202252 1250 44201002 44201021
    0x7050102060609040807021908030a03060303020c012c0102011104030606030201021203090c060c15151503010308040b030702070806040303060303080c09030c0108060d020a120302010608070e010b07031b0b0a 91
    0x80c40c402e04e240075a211107080c07268240c000e00580d0095070810a2401425000010381540400c0d40d40b1499550700041c010216031105a0041c032030030980741d509501407440c00010084034103c03203001c55070f68002d0740c11240e198407103541190360390000080300c0e06204001d000914414240464040d103075000091810030b0300710800c6101081042444090310000400000085060b02c0007034407907100c1046903050000680300c0b0402c5201c50713020070100c00c0090049180004007100c000044100200400f030560000740001040c080b020403061103155424000340d41c0c0f0030800c0c4112803605468003496802d0485c1550100c0110b600c44074107104040c1c105014980c00340900030428103041c0e10038000b0390707101030014000c1c0c1030000b180b020034455226400c41c48000d03134016113004541681c03050301c051000032024081d00107511b8040045034149000c41c0031021601c44485088450b404c005105100d90300c0b82d030044042c0100000d00614100503840144001401070102403074a1400e450701d070059544406 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 44203502 1250 44202252 44202259
    0xf060714040302130b04020304110a061701051e0a0602030307030b0f01080708190606020a021c230a0618020112060803040603110f0f13090507050307180b0309070501020606 76
    0x14a6502040008030a60307088030b4040312005101401c0f025188010312108400b107070410b00000070001444154608141480e100380e40311006980c0c6c0328821641e0003000301c1480c0c0550082001001145488810795803040200c8000d0346078010643d0014101c1c50851340010050707013000c4200640a90148142005030b00140d440402a0185400007022890000d000703074248205035004c541008441c4c0c000150115107110100003076500c07844065a50f50103420202e11400509034410005005601d2041c1000d44c03022080356618401c00f241c0011801500aa019500c105011040400c10303500440c109456013119500b003100c1c540c00010f0a00302054044800541002c5c01000350300d08c00001c940c119042c520380020201105c40c0c05910b540714050744511000c40200f90100e001c2c946c40e0003020310100c1d600c03500060580d680f0151003903a00407203c420100c2e4081c400240240d0180301126544095085611034a1303131034000350f8405800542d114507190340001c3c4180001e58041158982040088 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 44204752 1250 44203502 44203517
    0xb09010b04020307020607030b0d080a080a09061a03010f0e1c1b03030e0f010606120e010603060510061d030607080603100c180801150302010e031903050306090703020c0a020603070905030303090f0607 88
    0x92f11070107014401d1010840405c08440d001030741654180d88108842c80c0c0c070107010f01040710101d04402e9040c680c0c44581d0b21035464a0003201c1c1904136440f8141500104c0c0c40a00851109901c107a84402c1072840344000384000d2403210301c0d2703c41800340c5862000c2c1c0b00362800a890801c41cac2c2e445203401d42154030719503244c2c07601c40103203c03654000c2c52603d20014100340c08035414184480e1580500243da000402d00c50401c000c1c0110301001120f03940540b08550340c3c0120b18040300724aa001e100d400035040740c143c1c2114021030801c07403141c3d41300756100c54058121506d180000603100c00700c0d540d85941c640011880c0070b514070203ca24580040050808400030b11000001e10241c50300800280f1000303040c03003c1c55001100940741400758008005140c140c6440e44030043c20041c01c2c0da0700c00c0b1402c512681469000607000d5010380b00b5a14480444170050044404681c05d02005038000f811820501100701e00c0090030f903900300000c40c032860090000c0c2c01e400810358006031400c038021300082c0500018 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 44206002 1250 44204752 44204779
    0x6010c030e0405091906050f0705180d0206041205011a01030b0a0b0a110609060901180b07030509030904290907050a0c0c05120a120810030b09010b04020307020607030b 74
    0x80d000c071800c00301c0e800280d0343c64001d80b0740d10f0200340908820032940c0d22641c48082c0b1000c0d610a81c46070180712110b0f00c0540c1e400c20100c0702d5100b2081011201341989603000304d00d0034241d098503011032024110740e150907242c003070413070941c0c0308490304a0300c503134443c020401c0e01100c200390200c80e0002801c0a1056a094400240301c1c401c480c001c407505c1c032030040744041e000c0e8411012121100c03906001d9440505011003400d403510411a483d40e195820008010549100036800b940c44a8022540500c2a240e40c10101c000d010058031089952205100e0002250743d00c0c824207810b0007420310080685801503000d0105800c080c0805c6208048102c20001143e80040c12600143c0030340c0307040150101103241a51000c15540c1149070000c205240c1540f01c540f00090f168060f50080d80208202d0300d266130116403d94049900300054002032000b00000f40517680400c0c1c010747c0c0400042140d4401d0340110b02242c0040710b5080040c0e2014040c00322040d018451200600c00540e0320b0a0008031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 44207252 1250 44206002 44206007
    0x90406050f13050c070204090b07090602030f09010c020d02060301060c0b0112020906060d0603060c0e03010e0f07061101090209040803010e0c04030302030a260903040f060c02030c060f04031b090506010c03 90
    0x81a00b40ba50405841e40005601002c0321011a40c81507030003001009084e0f460f0a0503401d043e03044842002027a524100400c0040c0004181c405140c9042402450407280c80011030b80700c1c0d0b005104a170006c444040781401661810082d6003c0c2c103066a817100c7c0c81c0040c0c24880c110750410f03800000c3c4070001b0981d800150f115614075a50140701236886a90301d4052003c01d0005000e16400588030b81d1500b00d50340480355100c0810484030000310002d10040703400400c1e041e224903140401904503407201300c041040340d00603015441400118000010840b08503000308800d10011603080300c02d48070000040c00450014a211070300300c07100c250750900300350840e85c01030354a00c1007c0748403042c088402c00c4600201d00e003c0d03401c0d8800500f11110452030410080e00b5959800501400108101015001c80c81900c25500588203680043c028029900aa4103126160b80b01c8415243d0a100030000800881c00d06c07040c21002e0210643d0072510300380b810210008440001c0d00035810410580020380c0801d9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 44208502 1250 44207252 44207269
    0x30a02070524070807080c030301141c150905100203040606120c090911040c0f03050603010b01050f070501060b131a0f070209180a060506030d1103120a06090908090406050f 76
    0x100520003e50b20840340c10180b106000d0450010b1010f40001200342d003161000c005076040318213080301e1806180d134100030402003034110054120188902c50301800815032100d40200d020900d284005090740c000d4031003c0c200550b584125090540020a0008210003403007108020718481030058001c0580d541d5543c0c682c0418869504001d4542030040d0a002080348222103e40340207100300003003060700b41c014010301d08070a02800800d14080000d1024181805464411801603480c28a0001600600307841030b0404003040d0340700d41d43c454020940020381d000500c1c0c41c51502030542401880d20104207158540313a40c100c11030010a001c2c007403500035044241c800d404c2d8100d8000c496541c90600b800c010203030b440c846400d85d1181d243c800303050044561005000f0a025000d589034102e5860050f200c610510310050199407040107002c0030b000f84000556000542c1d01000b05909540310640c1c001e4a03c0004155074040c1d0004d41c0c420180340c9446488000c0109030341c180804030040c8006224407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 44209752 1250 44208502 44208559
    0xc0406050901030b0402030a050f0f070903020405091504051e0102190c050c0301020406090f0503030301060c030f111e0c0f060405010c022b0309090203060f30030a020705 75
    0x4004101c0041d1a030082d00480381c800c8014200310340300e1420780544e801808054a115840c5818480480c09054400500511400d081e1b03c0d40d500151840d402d000080100411400ea18000c05e940c82018803030112101d40990301510081000c0d901c801d10589007500303160802880c42e0710412628260310032000b104003951101d800d00b00000d0b80c850428a040c01d0000c8281c80d415440001c02107809d50300040548141c4507000352100d51143c41d2000e1560360f2001f0701400020642000d58103002920400c1c8030030401e2014680480323640140003000c0c4c40c0007a140c4050311100100141c0310580031080096003183c2c801140da050741001c02e0300124a13903114900509042282500b000d0040d0349800381c0120110741c00303041128444d003200c91380140015130424120001056a580090001c01e1402a00e0081900402c0c80100b5600b0000b0040c03d5480b002c10502c1c416048009412610081c45121201d254910069652082c2d03403c8002d00740000c80d04014800c47c0140e10f4006000702c0c0c0c05089918 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 44211002 1250 44209752 44209757
    0x20c010c020f010203070b0a1a0402070f0605040503070f05010209270412030b131409070e01051009050d0b060103150810020c070807080715030e030d050408090a08010510050105030c0406 82
    0x565240b280103d095103d80000641060400c0c030611984150380c0e40402694031429001118510f640b80401090780724610019040703c10301350800d0302003041075100d16000b5116000312072401d41d0321b64030b64071058030310b5a003900c450b540807445900906104042c0080c41024040b9900607400d1000e16026801018202074289030051a5841c0521700070342c007140c9811401400443d01c44001c68a00c40078202e00b004405030314211a001c1482d07070800003030a10540b5440074002046a007841c0601c9640c00381c1c003199004208070300c24006001c0c1c40c1c0c3e00d0703a141060300035507602c3c080703241243c00034040c2d910000810b62018040c060030031030413401140441004100d0500503940c0c05d0040891880c108882d0881c880074014001c000800310000a820002c484691045141c3c00300812400c1e804ca0b6140d224400507500200422640741d0380366800071307038494400c1c040d450401d460302d000701e001004150001100c2e43c2d5500c00f4801d0314503000c1a0070000341401d103000c0d440c6190902c40480c141c02644201c10a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 44212252 1250 44211002 44211019
    0x3010e0f041a0903130308070c14010c0303021602060409050402090610050d020904060b0406080106020609010c05181306080309041b2a061a1003060501050906090103090c030803090607020c010c02 86
    0x100a0b9061044030045240280595034091b02d0b400d01c0c0800d9404148111400300e50f000001449030400c0b0a01c003050071058642070005030710b03030b14150041c1d0301104685102070b00c4a80d00f08010ba45034000380c4003810403000c0000d450725291041c00200e00020342403d1058120324400c10a61350300c402214003c1301d0008000d40c840910302c01060103000300d600710801426002c107006c54131a074420401c504031401035089070304075151060303241c0c200d42035008000c3c0000c0080040c803d62620fa40103403012030a014043e203a03e1841c55400da0200c4043d600304803c19000021240c44074a0a40a080c882400e41c0c00007015516520501800d0002d48194941590710741e8952110301300c044402c0c16041e00e40003641400754074980c0d50301c850801440e4039000e10901803c1864580075200c2e1084d0020b07680c0607101c0c180781004501c200000e9403c841a6a4109500ca0005000264034508011b000b5032003554503684a00305150360506040c0006c080e04115801000210351a80c0d014640480e441d8040d01c9015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 44213502 1250 44212252 44212261
    0x11d061311120103050a02100906080604020a110d030c020106060203120604090c12030906030c020c030615120a0501060303030c050c03030a020d020f0a0c0201080c0a09140102010612030503010e0f041a 88
    0x1641c50082d8940703030300d03400d24800001040c88004159988079910803070345010102daa030b54090f1410300c00781c010b02000844150001b1080d0500b030b070081c10110350b0f90410082000e1070346801d5161092180c04c1d01d00081d02d0303821030000304c0d409018800203426030303001960030400e4040d1040103460005080a11a1361162001000e10000080420207407461101d05100a5441d040c040d00c0e80e001c621400000a1400410300d0656102042250582c20002c02400954890011401e0341c3c410a0b0b517201d40c401101d2400d240c12000800068100d984600e00100b0308519500b009800c84a407000d001d003d008040141c1c400c007420100030cd03688518100e500507115102c42000d10001d020302003141d0400c01000a24070791645c0c1042010a0180c0700340e807040c19a54414124920b207029404207000414940441407280c22044000d1080d504030620000414a90f6042d50301d08210900c40107078046200000140000c0103691150350344003050550054807810107643e2a080d07000390f00d0150707022079051000726 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 44214752 1250 44213502 44213531
    0xd0e0d06020f07150b1903020102100e0c0a0e16030207030504030803040303020702130506040c05130e04050c060a08071101060e04110f0901080c040b03011b0507080c0105010e011d0613 81
    0x94145940204c6050310407550343c40007100901d2101401c61207003041c12115104502c016100708140e2358182d0107000700883c50b9100d0001340040c0912881c241c01528051402504d8299642c00144040168031240b8144000c504406174003000003202050300420848020a400104460031079500034901daa07a96941d0404800a004981001303511444900500110440380c2d002240035090403901000140202203080e01e01748140317504d82a80c4200c0a80800c002e092000c99190310602640070f03150b240c0604000904940e021004200109030154140010160721400c00c95103203030400001c21500e400d05290081540e00200000d04515405402d003165486001c4d8005590740003400760540b41d61141c8003907446030560154140142e01d00906201c440c40c05002d2500c022844c1030310791024030780c0200d0481d0380d540400000c0c2c2d8100f00410001c100500c00740310310350003083c034208903c2095050911600800c41040e0194042c0e0b1440420300000f0b6841e003010000003240b0140c00114034802e403000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 44216002 1250 44214752 44214757
    0xc040620030a0906120c140a030e0d110d02030309070308090607050a0602041d0f04080a0c0c1d0c07030801090b030f07080102070219030c0e0408190906020d0e0d06020f 74
    0x200c0356502011400400c22604688400e080d540389440c0c3d002c440b0b1007045168215854a143d09000801405400d03a0200b400c000a240803581c6242c0414841c80c180807080c81c201d61902a00300261416019420b141d0301400f4615000f8020310196140d81001c0e240d8503a9020a4040a0501503001950501c160749600841d0541507124054070700c3c101007410040c0094101d40300d01c400141c3d190f807694442020100185100b451285030780d0000d51100e440d8602580c0082d400741061121141503c400304001181e00001840840020782c40c803c0340e00a0080e03d48800381c001c4880400510000e000240c0084609055440e124800561301c604440000c1c038004007a20540303500d0003442000705100c00190005d11083d0300075a4400490384a0b01c00340440d0000d035100c0a00450200c44041c03003108524581180c2085c094420a414a42e219007200c40b100c6080410300003050030382c58200302181e0140300c030010720311072424603606182c080004503c940c500c04900604056000807515a00c814020a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 44217252 1250 44216002 44216057
    0x6030a0912020f0f07030f06020901090b0712030b0402030c090f150a02060f0709050a03030e0627030f1b090a2c1c0f080604060522050108060c0406 65
    0x100a619030a070288003944402800111007003601070750300c490003004000100c0208070b90348182a044e01c203000d5107940c00290000c5104904000001000141d01400d102c0680a01030080d0303001c503d4a50018009022201405c4007a40541d005100f000a44c1c29145c003550768250096909903130818400d800920400310b0455100c0130b140313012500c05d8003240d00007100c074810103003043c0b0758205840e500820b0700c42803050b20a0316072100c0290001d1000910600800c0d04480020b40f456003025050489c0b014036180340424104030081055201ea8145804c0049039800707495880640b043c0480c0195120540201004960198440e0000f181030560315034861703803864100803111581c1c02141000c05805524850722030441d8130270703025400314046890041c510b0110b51502c0700100c00541c040d0595280354010007103a881595004006015154808405000030505034041c440c649041091000c40d181a00100d0044e03000c1d0301006031040069044505444460818520080040c042410080c0c4c0201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 44218502 1250 44217252 44217263
    0x6030201050d1a040510060315030b04120309120503040228061d04020a0e030607090602060a050a020d0e0105060109170a0f0f0507120c06050310210c030c05031203011406030a09 78
    0x5c100b0002c50200344000080d10810394042c428000e0740140b0712848150350001034824206c1401140c002103000b00c540c07013180d20034140881c12110390b4503040982c2502c8000301c0c010542c004204001c520340904215800c0c0f01c00700d000c1c068010442c041a0f41241240106c0c3c0a21140041191000400d400c07203aa1001c0018404d5607241e01c0c01e42c00400d0600600703100c40c041d105450101e058a40500c04007000e985199000309165694440c100c0c000d4000504013140c03c0d5404c210300d0008034124040d034031080247d0000410326003441c60004181042d150b104d010600c07005c0d00742d0085e518010030102d00040d040798403021000c0301c41c00c00b030aa005180d00e00425030f11908000282c3c010202d00c00300b441901400c8000141503980c070050b0385500c0110340d030260143d00103000748403606d0740f1400c90b11030100a00c295150618681e880425400d0315400584403d030004c24108064501008030714592103e00e40414250751501d405400c0b17803012003000c14401d01d000702c0001e06260195000b81c40e100c4d00007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 44219752 1250 44218502 44218511
    0x20405060c1c020a0b1303050705030a0e0a0f140603040206041707090b0a03110904081c0b0a0812040e0c071707030906030e0312040507090e031206030106030201050d1a04 75
    0x74110340e1005403032140309025500e80c0540700b1940c008549913500300e400c00d407500c12030340e565246514140300c1d01c0402c5040c0002406174002054003000500405002d50319002c12982d07240d0200700110a240e48030a100b204000e07014011924001e14000803401c0c2600c0071a221385841c80000c0b024091904882a0302a411001c00032007040007540508a030300380300313040007401c0b940c00038469880c034503020140c0401070700804180c09007050b17229164818000c01c46903003060102c1242c440d840c0b18401144070116103a1401c480c1a181000240c40104140c10050100f1044c5510740741e0300b03000b00c0c400d0700c80b0441440c0000c0e0343c0316007010032181c141c0d5200d03040b02d40001241800a41507000314070b00303130002840da20021030018001d00c1040c640000003002036040280d402080c0c002114014001c81d0786009221001550f0303600c03401070b0000084408059610b51403140404036030754000800e90341c0320703030705007802040540d07041000c0340d4007200c6481f004074155907a00071810125201c840d00b15045484d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 44221002 1250 44219752 44219767
    0x50f091c050d091d060d03141605060f04031e02030d090b0a0b03010b030712030e040c08070f020303010e0612010905100b030106050a0302090705071a040c060908010219030e0102040506 81
    0x81071890340a810780d00c03003a85440e121038280008100000300108908090000700c4c2d002e185c005080b4008078468a080236510001f10500d07034540d009260342036020347c1c1002c001c404012050003482c0d4800c41c401c0c180ea401d0725050301c0041c2081d00c400b851400e441101c1058401c0607209008030707020807840b00d4090207801c0151070300c00e4000604841d080e440e946010203d040518040c0680316017640010000c05500d8201208800110880d007001c405001482e400e00c9447d072200e00078042c100d071590700d071140f451400c50406010268682c140004540040006010074019001c4c085e030010b8007900d241d01800040c0c041c09005040054000d0070034840d17284081820105078004c80c2c203080f8143d00034440c0c40d82c1c460500454a50b6404029444411200020070580c07007200175083c07080c0100340030490346065001c0c84010900c181d40640c0c4903103000c074040c002e85410030a41d81c0100200c400031440e0600c4454030491580f80440800c040540740c2e900c111401c1c0094050701c028100007003906550311107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 44222252 1250 44221002 44221013
    0x20f0a050304050f011704030806060d060b09100c03020d0807200a0c230d020301140106020a061503032001110d0f050c0301030201092903040303090b0c0901050f091c 73
    0x902c01d032482080014013050180d440344041c0041c1c890300007000c5215803205d07502554114802010340d600800c00f448010307075402c00c90054100400806135280d41d203907107600074801164041540c030820f00c44ad40340700d0400650300141c120000c084c24501180503845505040b40c85070800002e084c2040128000c0c02a001001700b0040c42c80d034440c0c2c0c007400040d603a40002e8000ca030216441d6201102035110310030f1440c00c02c02200c168052004000045002d088911214210300a07089480140e0202d91484100700c0d1501c034986c4040501fa108081440c61980c0081a607005260448400300c01048010f080180c25082100007920380340c0e942ea102c4601c00700c410018104160298032850800c0f000c9210084203100b1241a00d070180c2d07401c3c036420b081090450100124401c40204124040702c2c01d0f0250401c14091070203075203e50340106035910385007841580c5000213010125041c10812034071070140c0c2c0100464280c6243e0f00d8a454407450000c0c00521107410842d0000c40340780c82c401c218400c121 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 44223502 1250 44222252 44222257
    0x3130c060224010b0a03021e070b0406111207030b042901031407051b0705040609060302030c3c0303220e01031101120b120309100201090b06010c03020f0a0503 70
    0x4070000c100c0d401020444004100c14000e10403a40d1310320041203e042d115209400801044881072460768050600c801e6240e01940b12a005840d1261414180002c1221500481646102c412615418418543e800c0c01e246240500300c901495600e01e0100741d00c0d11035030010515518106441c55000c0e61a00c951034010540745040d038002803405001080c6550400d20103030050031a503032850f017000c00601c80403008080c1012011303841c0c455000c000031590f4560241b02c02411407140f000c41c00d18610b2043c1803510f0303104040c0c0d9100759010725100701c0c3c102042900f90494000701c50b50703c00f191600310001081da01c00f001210b80500000403818040c15144005c0715040182d4400c400507250390f03845140701c088080c080108101c51015540e0803a6100c0e00c03210b003001d43e10301000070300d003155900020100c00304541c5900040c1c00214480c50a0702c2d00c81d1507080040100d0000384213890b0213030749507612294001c2c04d407418030a150502c074081c5031080000c4c4000303600c0301c021a0014101c0c1c2c14403c0c0e503074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 44224752 1250 44223502 44223523
    0x2030109050303190203040f020f0a0e01060c020f0108040302120f09031516080f0613140a1b0201060e0109020703020f030a05031014010519030f090605060306010b0304020306040803130c0602 84
    0x40c508034903084d40001c1c10348212449103401c4034811041c42e0300ca41c20004915112448142e201f6080c0c400410300d680c205180500820070f035101d02c101b110b040d1050100001d071082843e810300c244001044042500410f440306030950041085603a071018003840d40c00303405403400403034043c49100480c4a41c0300d420128540a14281202d16865032074541040325840e2040300c90b000d180015038003154042c2000f03104641d00140e1000e0104254020880c44804d003a41280d41d4084562149500004000d4013200c03508544100c0c802404110308018584211140610803420348aa0000341041418424029a02054400c1050743d954078595200102240c2043e9481e042c908201c250008030380d01c0c095031154018006071203450030941003a11006071540c10142100500d501d403141500d10010602c203642e070070741c4500e00018560425409041c90030505800c650440c103410020701c030250345d00080b860f07030040d44000826a80d50310b45502c2e9001c4200340800a00182101d0f2000c103120f138000c240d81100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 44226002 1250 44224752 44224771
    0x1b07090f0f0525050307090306050702060412020118080903010209040507080f07020309010c02120a0b0a06080f0c01090b0304110a0b030a0c0f09090c0504080304090e12091c060902030109050303 85
    0x21600c1d1003140f10b44a65440707071207190706600ca070a08914180288040c5a108002d414034520481d41c9031203034401e8071800c94440340142c2080701000108807850582e20340e104a00c2c4020000140380c101a4003107409075000141418202007514003450b41c094040b548079000150040c0b145041800c0007030030200003034840300007010340800080c091a10003c16112450030507034810b40328520310b40900850070803007d421546405a10301ca2804124403884050151021000018403c0c0c1740414290034480e02c96408040783e0001c0040c04520380c1d00401c10016a00c0765000c1d0780c3c4d00e032502d24001c00380c00e001c441881c2e042102041d0006074240c020014521800c0c60200a000558400904886280507014404049460701d00e003130141964560045048a0403801d06034034164517403866504d9504243d0001d032110391103140502e405803040c000c0c0c41c00356041035075450500f45114001204070314140380700c038000f062400c0241d09120316078014444140d00500204003242d403508060b07440c1e0740102c0e03a0008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 44227252 1250 44226002 44226011
    0x2130f0801020f030703051504110c010e011e050c0c070303180b0a080a0216020301091b05010206011203121122060c050606060c030903060106030b0f0a03081b07090f0f 74
    0x440c140d06000f20b4059080c114521481c6640f80201a0300415015004600d101f200c003100102c0c0d91610700c00c0403810300401c0103451710b40180ca004203095910f900540d044603410604440ca406030095080c1d8540705002e000070419988a0144840700e02039800241c0b004d2041490000506401481c408900203408440b00c6070039483e60340da02001d00c5080c403600000303041d103800a40400301980c00741040c101c2d00700c004210307281d8039000030742902c6880f24156444005210380c513240a200040401c01000c003800941040c0d80b500210414440e000003014090052451032186034815070f91000d1080500d604c51203445d81003140d082480f034018040100303140650134002003826801441c2c0e2440080d400070003803982d940c40d041401516080300d1161340c03a0340300c1449603000fa5a001e0010324041c0005940006854040e0001c0084030020045118003481d407a54060002c508000c0c22034031080102c0b6861000c0001200400740780c145145d010040f042d15000301d50341c40807456003042c071848102038000d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 44228502 1250 44227252 44227259
    0x141e07030203010819020a0b1803010507080106080a050403030603020a03030302130b040506040603271421071101021204091d010c02070510050702130f0f0b1c08070602130f 76
    0x301244001e010b0304980d58445007401c440d412130601380c00724040c4041d09100c0c0039590f5103515912600f01e851400e19001005002c1d03251800c0c24400d03e40e005e0040e1804c080254900710000d0f2030b0b807038050302c0580038940700c5002a043c140650030900045130b000c0c00c5006400d60700d080c0107000b9005441e54a604194140340011081c20703400641d020740d10000d118520b8103141080503401400701d001180100c00b51941280601c0302211444881140540c01054000751098905402c4c07102006000c590381c1013884010600b108403000340e4004680c0031708400140300d11100142d00c2c01000710070120070340c030300003c0c0494003c207540c006083c60b05e0304036040c02d003640c20200030500381c420b552900c000607840024200060301d4900c000350b00308052030601d07524148150f00403c00f401324180282c1920b0703481d10f0400080840f00d1040030910301c2100400c0120040d50000140040740d55401c0501c94221081c456050040c03a504940780942c0c09101150f8031000d20002d40d00402c000c0c4105914040c8008001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 44229752 1250 44228502 44228507
    0x203100603030806280f030203060a1104030b060f030f100b0105040308031b160b10050f130b010315090603141501260307050c0f0d030c0602030604141e07 68
    0xd4060360380c1500c91002c44d640310414003484c2103c0901c0b44c140c20b0340c030180258445204844038400f40000c09a904540c9055006040c9801030181c00400403525002c00d120003410000c0549003035907808031403035080c1d441d0344000a40107001c640f1a2540b50061400d8585600d00001d001d90004040390710621200700b40000640d0310f8002c510014043c24800c00024521008101d503c02d1188103403041c00d030070302000511840141a44400880e0880c008109015041c00360b1071004009200448403205402c20322000324041c4148d107802c403484991912010070341c0f40e000c1c0d0002d0440c4280c80501c0b030801a40c0b10000b801600e0180300c2550501d401000c1c81d10508404141c103030382403040344138541c05a480e1503924808806c03d000c0800c0c0d1080d54075440d1424500500017071034485d01540003032071a0703000841013283c00b880707500605110700403c156180010f90806c08140d01d060f0000401038170380d130b0b5400110b4049c1014086e041c141c200d51000304040281c0b95444c003a0601c0c080002d02e0316564811205 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 44231002 1250 44229752 44229761
    0x13050c010207050d1101110a03050a0e150711060904020d09020907030b0901030f08070804031506080c0f0402030c040509011d0903090a0e09070e010f03060b0f1c110607060504020310 80
    0x4603074101002d0044e10300418000c400200503880185001604000c481b900f4500780f080604045002680020301e240743c4541c071003601c004a540840384405c01e0340310000703031150f24403c0749070007400b508403a081c0b0405583e4510554030741701c0c03010740250350701e80702d5807042002001202c100b02d21030816600840c64641c401c0c81410100c2e4800341c821b180613403c58448040d550b080d00e900b220b41800070014034000a180c0d8018100070341c818a034501082c0d011107100000c0c0c41030794112402c150f00012020b2850382e2074190f911000b410641d00180e90340c640c0400036031f1398812074000f10b811110100001a50b043c61004a070030000b950b561302d6200c0e489800006489110705103800c2d43c0803858104c2800901c401d8400c541d00070340114105d440c07050b924409008030300c03800d030302c0703c07600c13003501039003001406414018a1180038040f0780c201003007881800082c904103101c29280c8000500403074080c0403c0803607043e0100413440240715546500b4145010000b410b0101c03404c130300a01030040c02e010b10500034001d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 44232252 1250 44231002 44231009
    0x702010f0c17010e010f050d0503070f14010e0a050d050a20030901080c041202100e0405010303020105061c0503030106080c070c0f0512010504030f052d040303030606050f0d09020607050613050c010207 88
    0x814a0b000b85080c0c00c0080c5007074512009c1d036141c00200b001800044c908803414001c0c5100b030310681e410740745040d446801c445000420100a8001608240c00a100420780c0c030400384803818125107030040300c40201c61541641c0758407501d200b0000b400642803c3e002000d4814001c09980b07840c0d0550310385424003418000c6100f180c2000140e10014801031a1004a0044d03400e010b2512021401c54100010144ca5080c2d0082d40581d41d83c006210a601300424862200d80302c03640703c0107404080381e0310740755a44014403410040003080c0020689000d0202c04a621603034000c40702c1e080706629804180e41201c0c542c41443c0c0f0401d40c594140d000401c060042a1041e50903854070000100d2406083c1d81e103903c000b414540409164030700385013808048115002c1c004a840c02540c4803415403034050100c40403030b0400b000b80981848484c14011080b405c60f01c2000601e40e01003020022480400c0403805146002803483c02004104601c0e01c40460303400d100d03d8010400c80d040c000092005980ba14034a00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 44233502 1250 44232252 44232269
    0x4030605060a271e0c0206060d0804090e03070f08030108060112080702040902010e0307090e0f03090d140a060e010f0c09060203040b0306120303070203030412091404050702010f0c17010e01 83
    0x340309081c0580f52890300129505510400710b5100b0305045050b4541c01e100300c0582503269a80540105a541004550391208055903080410f1000e901c0340c400c1c1e406140300f0703012642d0312682c42c1c000d40c0c003003807055a0f501d0740d100c00e0129540c44c1e1868039150030341007405400041d00c111000001c0f1588101d03440f1011303940180080f45000c04071340030f220160962000903818840113008604454404000e010020007071100b0004044e44c0c070b000e08509140c0b604600d00c1c055072042c4140b000325607641d0790a2846651240000503c8828900c0305413319411010142c140703443c00d11400c0b01d0103010f4201e04007100c0d2484042200404100c81950100b8250040100682c0103200a006100300c49005542114000b0b02e0400c9100c0005003071869540110b0f0b1a10041c0c0000c01404100666203201e00258510303070401c030f01c80e0360500c40c40d04002d4841010040c4583d840348045990301e4001c0d8400ba40c00c030060002402540600d0074041e01a1440c208a01509900340d400007a040401c0200c00f0f06985030301 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 44234752 1250 44233502 44233529
    0x30f1e0405090a2004170709020c0d080a11070c060e0405040b0105040f0908070c05120613060203070c0b0702070501170c0708090102030f0703031b0305070c080307030e070b04030605060a 82
    0x801100000c001c40f03c000181461035540b02c21040e0384c4040035100038440a00c4070b400c030180d16101c1505040e466030040051500500801495400c007203000c0d04810828940f1a000369a2014000d01605000d8545514502d002805030280200401443c0966a00341ca03404840e4400f0001d01040340c01c02c990140c108201e01c4014012482c158100004445c0d18080200c0c00ba00c00707451b586080d600c1207070300711442c2107061400c01480c24002958004071716481c010b8403d030329181041c00c2e0141094003004061b01c1c0e000000507078883c060103289100907040010b00089141407080696140100e0058a01103001014010f0001d0240d14802e885802c00f1400b9508040301c9654221154004044850540c0018050604031403141c50242c4031304d902907640450403083c800103d41240d0b01200c490300401d0700f4141000f820a410180d12901d070755215007450b1343c81e41c50700710440060001055000e9980a0b80000081d07070310702c0340081e01c1900d009a00421494656008001d07a050310f920640350f010410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 44236002 1250 44234752 44234761
    0x30b180a05071e0305061f050a06020a020d1a09070812070507030b04030c050f010c09061704022b0b09010b01020c03120a09120305070507080105070c020f0f03030f1e040509 76
    0x6409429090710f07080c0c00c400c3c41522599800d0501c0340840740b80e0a0102002205424120042c101d500244800e03100d0b000b0141c20000b000f5211000028080d000d561038034203000400c40720729603050390034501045007050390030504c8140b900d403e000d110700c180c46c0c45140c1e01c136030380112035208452100e60702c41d0042158a28640c1e60384107603240180258140203c0d04004004107a0511108110ba5440307000000c0312417114002410741d000c0d942201040105000e040e036800400d0824240e005901150800e1150401c142010080441401c07042105001c811051007000121240f0a00404201c0d000f4000080d190303004907540d440ba0f00352140e0640c0004403100d040750100c401005e01c0e00b12481c00c0003419880c1c8842c030048401e404400c400080002480303509000c01840f20350050a44030000f0303c158100094002c10003030b80c0c0c0d440a44a240c1c1000520b10302c1c4d468028081a02c0405010350382c4a40e0071401018154224088800521030a45241c41a0700c0ca1007046601f07480b130080074071606458 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 44237252 1250 44236002 44236019
    0xb070209090f0f071a030f180a172701140c010605150307230d0213080a08030412030605090a0f09020d0606080c010e100e010216030b180a0507 63
    0x10081d041c8031440c000d11032072402d100c070188121504041000014940c051a0a404d14104100d80050341c001d0035041c0140124406003211544d000180c403c8050403c40c060400b407800d000440d080100f80c10207000005060341d00b8400034000719007065a030340c0c01c0480c00849003036035640c0a0f5811030002d101a000040d0111100014194100040c000002c10940701e0002c14542c500305034901000345404001c01034038036440030b085820410041680c0039403960481041d09203004480640c3e0b4081e401003103810341c2c030080000180c000c0000b00101c4000ca40340d8100340c4c0b46580280c070150b41e2030f4001c41e1040b0443d406805001c04442d40030341840410b6503811241401080040100b10003e0340380c0129101580d60010510300082c0134403000642c19160101c510f2a0035080300086040c0104500f2000c1a90b84089840c04c5420103410150b0f1101d1032940100d02f130501510049100c0d06007100c01100380650004620300c9050504065030707002a00040d86135403036000d40001080350b070016005020206 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 44238502 1250 44237252 44237269
    0x506070309080705010509011a0607050d12140f040309050306010b0301030b0c0426010501050a03021c05010b06030901020a02010507050f070f020f030a0302062215050702160e0402010f05040b0702 86
    0x41c0644034060400d02c40e130b51400d003507a03001e84e00005281e44401c061090300442d64241c010301c00e800c90b1181d01e42802d82d546d0360384031207003264250148000c0344440d141f529260b0700074450a00089102082c2ca1400100e54412514180c90135400611520700100d61400c0c0007480030b040e030321440c0049056a00c0c40d5100340d994203005000c450005c000340000940040440c0800b1500140d403818a004c02d00e01d44106421250140d00c9540302d40c60040080025858200114920720f15440f010880d1382e496060540c0500a03818541d500f203e40041082003010066000c0e25400115a000380004d403501c00044409000b90b20822070b102d00c08001200000b4201d180c41c10200d0f00c05003407016521800c0001030300b0400118030540150304408100145080d0b800400002e050040842c1c502c85805900e841c0c080415511708007440554840204003003c6c002c00c11090044001005121080c0c0ca0f5607103007002090a0700d040b8082806101920310f041d0080d070540c2c054500301201c240c141882c44c0c00700300601 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 44239752 1250 44238502 44238521
    0x8090c040c05042c01080102030f060f010c06091406010621020a0801120201021f0e12040e06060a030612060c0201050f04020127050a030b090f060402030c011d04090309050a050102030705060703 85
    0x24001c013880403c080b0104001c00c4d008000c22000182c60740f4000d050310a14100c0101b003d881004504101c00d042e03030f08000c84800054218800180300403891600b03500a00072207011082c60310420000040a5074000c184179036462486401403162264038004000781e02440703840002185c4584010b0042c000840c0003008203a00501c11a042c1c5d100090044608620700c0c600700203003e890f0441c0d000915001c002c11701c080410541800e04c3c15140249882c0801800f500c0b00c0e214610001d880e40c5554425081400904000f44808100806600d0200001c20858030240095420310002520808116030458031a58040e150a52116540c850300c220085080d07090b0200c002001c1400b2076030307442d4890110003841c418002c2154500f408a0b100c0c0c5440701480c81512668803070380c1040b0040c2c501054a0010000171700f00400e0b001100000d001035080446d49040d0400c1c9060f2585040c141e00c04c021000304c0314141d521040c01030701c41004984034821058040d02d180d00a9000c00c40b2644242c3c08045c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 44241002 1250 44239752 44239799
    0x30d080702030d0c08090d050435060a09020109060807020c04020d110705030417070b070807020402040b1306090512070e06030a05100b040b01110604030c05030f0a08090c040c0504 79
    0x4180e000c3c0c44400483c2c0c131a00f6444002000303c000c00032404410080460046140c5c00c0082c04d051400040e045140b212450301c8020000c600f6002d4020051301d10045d2180b0485403d41c1c07c17610300a84840000c01920005078009582241d0000e81c0c035010348215070150030a5406000150015400e01000e5409491804a00c1d80e4030303010482c00440050180c00e078944683d02650b95145403c00302d4100b6540071a00b03400f41d40118004000c12407402003200c10050780000c265449a20500000b00280a60f80c002409090005446c0c03440034182000c16081d104a0384912000c240c88005008071070100c070007032001c1d9a000b014207000220306440c545500520017422110240f11a1ba161401c042a511b1900500da8581d40b6211051400c0c1c02107101820082c684040342d0000008959a40c0002510190a02464802d614140031041c02240e052400540c01305560340741e500c100810340c010031100000b650040b00c1c14901c2c1450f080c0991698520982e940b241000e08044003c032031502040d601406 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 44242252 1250 44241002 44241007
    0x1210c05030a080301030203070b19030c171302040501060806100c0203010914060417031e09070b131a0702030c010f12091101080603010605090a0f090209090604051209030d08070203 80
    0xd20796000c00c05058800e1050b81c0480e200d515600c14545400040e4018581051050000c0c0c1394400303020b1241d0212442c9442e01054002d400035054030743d4040c5507407031040800203000300034558146d0101201c1d124400d80c1d003084035a03a110000c442d401410741d07505901003010003604601b148a0741440b22034a000400008480580b6a184d038000303260301c0400400790b042002013006225400091503a06488800028074624051523900c1208068078907412199811343c01058240900b0454000503110f244c07003d03992020741598540c0074100c10311030000042805060700301c0b4100004242c510007903001e40240482c00d069801541e5003c9617120a00800104000194030304002d4002c07030349094020020f104075141140b00040c40e0200086c0700e0f5000c0d84c10407070104150b132a48403080f54004c21843d40080c220701000c1d20107003d4010164040d40c451074583c18855100000329406000b54451000c47e0341032600440015128040ca001c55581a04400180e400703840c0140b442640c00219841505d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 44243502 1250 44242252 44242259
    0x80c01080601020628050f060109090b0a0306020f0d05010305011b030b0603010509060d1a0411100c030e01020307080c010b0118080a021e030d020a0b010618091109060a02060a0f0501210c 82
    0x2103800491f0445181d2010405202d210350300b2a0020003d00120603080c04605080d01c0458104506413000401460b40080d101045c9803504083e50000296240244000e507502d00744140a40110a882a0941c24100646000e00c0c040c0c030500540645c0540540d08580c40e000802c010800010022a003010521500328001112085e0130069030104c2101646942040d0800450302002c04103070602540440c4552105103410146030300010354140783c10300380011200c0040341513000d8000020014400891029510401134001010710034080c0d840d00c080f0443c2c1c1002d15490a298400c90849402061030300c8054101501065045204082038003030b500c500fa0f020900e001d071018451001030b0001c0d0100c0c010071030a0310300380c2d0040c41146003407822000d0b01070b400203280007503120300302c0c0c030b1030b541c1c42118071003036081c1c09071046500e008100c251206040c007006074543ea012034984941c2441c1c50070000d050b030f0301d620406050f07640c030004504080c04c40b920f103607004240c42d003402d9810082940703000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 44244608 1106 44243502 44243581
    0x10f0e0409050708030406120f0203130b1f090f0501051e0409051005040803011418070c0c030204020409021b01060e3904080c010806010206 62
    0x1041e011078034040d80380024030f601c0b2038180e000120340002c0c0ca07038010581e40c01c20702003100180030315401010810102d1100701d624454881d8942040c01c00b050b10f03550b00c1d075408490580d10301d03a0f800442215080d088941da00c04195140c807402c070026031001900845005103400d03901c40c059034034040d804600100300440c005010380c0c0c0d20035055092101c1017005a0010328180300411081c03c060800480301d6009006224044c0001d980c02c81d15808c0c400310030981c1c80c1030390b10365140c0360f03e0b10602129183d2002c0300c15551b5071044903010000d0394951000708000d020894005950f90440b008503102036007a03000131046a4500081041500110b0307195540c0a0756804000c99032503604071040a0702101c1541c000e28001c03010010001008030f420080041d6050b807004c55035000c101c000119551740f0f04940301d0b401600311001080c10101c540c111680c00c035a06101400b0703424010b0485 = true := by decide +kernel

theorem cover : BRFrame.Cov 44064752 44244608 := by
  have h0 := BRFrame.cov_init 44064752
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44064752 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 44064752 ≤ n) (h2 : n < 44244608) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
