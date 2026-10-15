-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4493
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:48:02.413556+00:00
-- url     : https://prove2.me/submissions/f13e9cca-b73b-45bc-aef2-a99153a208d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 807913669 ≤ n < 808093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 807914919 1250 807913669 807913693
    0x1c0f03060806151f3014040c050a061b05030708030c0910110c0d05030c01020a05040e0106020d0903113706180b03062b0b0c03010312050904110417 65
    0x107131000c01032280c0d9503141d208000c003902514800400040b02c214000052041c01508a803641c1708402504807210300107501810075090219105401e50040d40c09490f11610038010b0540000c8401402d000d050012075048a060800c02c3c00c502592200038038185000050118100701c01005d41304080c401c0341c1c403198181019000741e07150410101c0d1407906400c403001d100342d1890810211890207002d00140e03480c010601e5041401c93740702c450b00c800440d4000c9824016075080e07681c91800b4100900007045031031404d103006010300e01c0c039100050022651340b03049103807502d540c01040d00d0b4000c011000c40d051021107902038046185900010f90080d1001c10010743c6500c9801c03506443d40030b04143c414030701e0a200743c1c20b1040d40001d0080c0e40110070106a2000d000b2588903c03c074001028461501d0110640b1301780d00c0c40180548414007504080c0014000308042c18201c0c00390b141c050801580d00c41d8400042000740c92858481d6032a9580890001000c10741e0200c582442d41100c0280e039100a409 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 807916169 1250 807914919 807914959
    0x8031012020a0b0705010905061305060a0e030318120d020306030114040b15040b030f031903060515030601170f0a0e0102030c0301090c140f0d0e1c0f0306080615 71
    0x808040c2d0300203100c000810811901000070000b03240524000300e41e1444a850380d43c5400d40a03900c240c01500401103034000c0c48002c0c82219000000c0d00c0040c0901c000701000980d803400040e180c00700c800b00d14120010324100821040c0e00c007503000403001d6100c2c136007805404000e402c11284d15000303501703002040044100c003501041c4501e40c000c0303105031139440e4020007503000ca00d4400440d410075582c131032008155a080250a492032a90b40080d50780e031503032009018401c0342e014010001e041c2014003d02c916501d213080c6101e60f0102c8220203403207075250b9004076002107546035108510210708003404149403154180e144240070003030050003a09010380584d4201c1c4400c841c9003d4030101400180f203440b59907005060000501c1c81c090400340c10098001d140c991085240c00c6100b0380004d80e10244003c580036003c9503070154405403203880d0ba140c1d500d20210f29901c031274034104160380c00462a50b9003c1c0d40b1090280c8680c0049603140c0ca170090101c41c07590707145e0070118814500d41c1e05040811000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 807917419 1250 807916169 807916199
    0xb01060305241005031503031c150e0105130f0c0c0203210403110324090607050a050d0b0a090908090405060d020607110616050a030906050c0c01121107080310 70
    0x50f1000600002d844030440b11030304003a050304240011411686d52503681040a0001a200d421340f448118084000e240200c401c04007404c09030640083c1e04009c803d2892825a04441e8240d464580403046030044800420780b45051810440c6031200d200104da038030032225203200d40300303804440503d8201c19000c8081c05c1a03030700500744d0220401083c00001c5d1150700c01d60340c80c8070180845000381b0301d103801414000654206800d0300410384041140d40c540c2084030503082111810003a107821007001d0000c2c581d11402c44400003c60700e4a0020025032507440c240001080002410040c0e02c05502e0114816800380c000c09120340e0801000c0f4035180340c1078207898000d41d4000c00051408519581e51a9403001270041242d2221091084003082001c0c80c0f00050080e100e40b0250110b410640782c0a400c0303102c65081201000010300004564110004042c00600402d0908a444e4000082d020f07000d405510b04286031442c0c080307118800c1046840c00f070f41c01005120401017410381c40d07030066041941 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 807918669 1250 807917419 807917491
    0x10e0115050904020d11031905072a2a0f050a03140109020607080304030f0c0203060117100e0d0210140c091903030f0f0518010810030b01060305 64
    0x100110000c44420700032070007800541c0c8094005418503603240351030011290741d190300c2032688100000300005031540c000980152500c5800030003460806c400300070001c08001d010f00c2c01c08186190700a8540340c0c001028040a1b92213861030b040140032103824502d2400980c1c00c0c05958884203004248100218961000d482c8084c03c0c0680326480d43d200c0e40304003021003400c0c0c1c4d20355503200340150250b01c0348401401c10500030f108a81c1d690801c2d250007480ca00e1044204001c20819000b03840059030040fa50904651151002e0030240c4070300c0541504010059080101d400d10b484542e010080001c07920b10f0b40c1007001c1d000d075842400d491100c201518440611103840c008001e0015144220181c00f038407881c100948186010003200400040c47e018179003050b00481e13415000320115641c00810f00c41c6101451906508143c41c1c200c000c00c1c00e044201407141804003000020310215086c2001500940d0082040e00c4207594824000c1c00515040d9820030300e6100400a0b01005124002030341440c0d9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 807919919 1250 807918669 807918689
    0x9010c0f0e03120f0d0e1f0c0c0b0712050f04050c1212030a0f150503010c05160f0203150406050f01050a0e0604150b040602060a0e010507020d05070c0e0408030609010e01 75
    0x80c1154010540507800301345000320f822403c0c40000088921407260070002c001e0540104201e00380500740310040c18601e510354075a01d041040380485c4070760220f41202d00d00d80c081d428001e01e4540c0032085d1050200c1c8100540d00b00e113080c0c02c001d442e0740c0d0040002d01942c01402902d001c2c0305e03c0701c2032100c22074560012a13003a0b0b0101044440080c4080002c507441009088001126a1844070082c1030318511080250911070b0050705107c3c0380307028860740a007d011802e2951411803803803003a41441403044009000000c403800d42070159102804102903036141c4403110740491810b1311b818001170100f5103240c031070304422030b00200d02d0381001a41c1009039000c02c10000300c507607540b00c10880584600c400e00030170440362860004a400000010b40040e014a40140a0701d1408940c3d2408a6985c0029542680e04060901600d25004292100302525510b403095980e03441d81001241c801055000141e00b2a1500400040c4641440518001c5804841e0001142d9840081000d002c01c00e01904040f0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 807921169 1250 807919919 807919933
    0xc0f06020c090f0603150403050a17070c0f0c0e01030c0812122205030c0d12060f06121e1407110705012010050103290a05060d020909010c0f0e03 64
    0x224280f0800d40d031280004003141c0000d04d08042007441c0d10001c4d9021404940003250460b00503800c0500c0319290003221020410b68074090310300514540f940c4401404200340e220201c41480020000040070b0030400a030941d0740d5940e07140c255941600c0c0c2c0714545250281503841000011150115418036400100400032604c6500400c10520940c00408103ca00080149400104280b0150079480541c03805071409643c07001005c5c0003156128003000300c00d45403080c14042043e5900c1c2041c1030b202d85240c00c542d01d004001c07215000303000d0001c0f4141600d5260143c4500e20704603070450b112003814447c1e1074040f5101c05c00180c4031074080e00c0e04a04c254004070390034819544155003880c0a142c040d0106048110401c04c0142040d09a11410341c08544030001441400a0000e032000b5140352070388021804e0403854004041108090300701010300b85c482d4086081a95091022003c56400070a600c001e81032800c03a04d4002c251154003c004103c44180844005020300c421034420100a0007404103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 807922419 1250 807921169 807921181
    0x30203070212011109090a020c12040501260c0306030a08040311041a0d030f1808010c0e0a03050601090c090b0a0903020918030306040903171603060e090d030e190c0f06020c09 77
    0x5120300240f02c44810355003071002c0031113084100045485a01e81e0500d48be0f640c3d0500c13000409000700210307100d0300c41107181c000c00322180303d0704026640280c001d43d10607100d03100c081c00079040c10700343c010180001d00007207004400c0c0b1031403c00101010008035400c114002180d072503000c0148590244583c0a01130540c44d0011901400d4000c225203401e2038003501840c50000781801e141420b8120880b1a90f4900c0a00062504020350303d818035411281c6003c80e52560303484d036590740740502554516a440b400c240764401c0c0250591400b4220891401e0740364504040000c01510003844164032070064071001c10501c90ba072400c0003028903440c4014515541d10141488080c0040901c1142040052800c1c420301080c05d04005004440d00310400c0b9210101c034800a0640307406411207041d00021400340403143c0781c002140b20320201d8034200402c0e000c50b20310016040001524206a044850f43c3e168010003040f1100c80c0182e8022010250445490b000c01f03d80e03901c500780c1d0700c03034000c0513100120754 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 807923669 1250 807922419 807922429
    0x1203020102030937050c0402041e080115090e03040315050603160501020a0209061f0801030506060105090901060f2024060102071809061b0206060405060102300403030203070212011109 81
    0x141328024412129041c60010120f0300b2a8040ea02c6200c01304001c003044c1080410b0740078460001c0542c40024030030079001d0700e50a119107005209048003c0c1c1c2e00c9c500c00c0094401030007958011a049049100000d000407071400c042c01080b50003602c240201040300d50090428802007080d240181e008281028007982480318503007000e03005903406074041c0c07880c0d10404034005001d5100310385940c1d00121540355162041c81c101e0050400c0d81480740512a060b00d0ba107a00014a0441d00e05103008444900e185401350b4520159481c40115951403014945e01254001580708070001c00810300c0000902d120041c1840900c15140d090043c3c0040a04120350210805880c807078154004000031000129920241115444288058a00c1d034041c00d1782006a010301446900ca02c054505000510300080000d46030540034280d5441c2c0d4005038074003014010080c0b5149040b041074800d065a881d201d0074013a6480c0c1104408900ca1007030000029401d0b0b006000d031520b100c40071a402c42c10b02039841c0801c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 807924919 1250 807923669 807923773
    0x30e0316060e010e10021c0c020d08090f03010510080d0302040f050409031e02010605040e0312040209090102092211120402060f070203032704060e0c07030912030201020309 76
    0x604010304100c0d684060754070030b482240030f0340c5c01d5001403030030728003001840c10403104000c2d204043c05803103200b00c405078840030705078030405611465603681c0d4040000064081c00c02d0400c0c4941640c608000c0080c207508540101055a4400d411a581140126412404d0344524007501c0b8150741105420480c3d4109a003083e006c8911034200746404101411140074140a80910100181c0d101c010030409414035200b082c40b29806c032400b841c035090303403606501d0301c20070082c2c0028040c28000700003e203403100c207605071502540300810f001781c0d501c581480001504440c03003010302c0e001e2400710091a44220401280d610000541046600d42d455800300902e58009001c405441402000382e1300050b5010310080114805d03645001100000f030103961035820440640c00c40c02903140c6002171211440110110f903001038880500c9507546802d1504030713401c0c02d191780809200807a1848003400c048d0190081e501c101c000c4000c8450006902107440144644917829070200b1121200c3d03c1000142e0310030359 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 807926169 1250 807924919 807924947
    0x206090307150b0f0619032a0c0c05060705030403051002070b0c1c050a020315040e070306091a091e190f050c1e0f04020424030e19030e031606 63
    0xa502240e5204e00425250343c010001054030418483ea00c1258542510840c490b109141c0f5003400c16112032842a045410101c9600c2c0c28480103402800401c12200c032030b00e01074000a030107175444e031100c0d00d412a9650054001124540200700c3d100080f00514030030b03a449103402c42c24118a9898035102d00405134000e4541182d02015201600720207040b601540d0302459050000503070b0f91a013200f1180d01c4d4854440c140e03102d1402d082c1e08540b960000204002501d0300f05c04002902d898034540046002e91a2040d83d8500a82004203e003400700410700c062007a0401e4025041e440b8015901c54903040d4240e0080c0841020408800c0891f080c0220306140d0381c819005c50703050315130140004d9a124510260a241d450b80b00d11094414245110b030802092000d403000e50a00e802d100700203030003030b106120008001070380c480d2150100307100350010380c1ca013891403007642c2010103c083d032481c4038a50348409601084500d044500e81d420000b0b0100042220700c08041c8115080c08400c84c0c80022130881 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 807927419 1250 807926169 807926179
    0xa23070c0204091a07090e19060504240f0807090f0e060c0a090f050a05010302070c1806090c0f02060411030f07081c050a0914210d0206090307150b 65
    0x34400040c0c890344201d080c1e0501a80705244125012482c01107510f80050112040140c01d140c01c100d0900d801101a070445211400d401c804080d0a072041e0082109902042e030041c24101c03030120038203900041180310a0200c50041d142511040040c1d00840c0d90300c580b040950000c07404010359105a4000d075113944e062400810101c114180e4685001c00a0b100351014800000305030540b80d812400700b000502c04505203107400c41c034103000292915400d11907a814542c000032250100580300e40c07024050300c88266204148200350380740c00000c010502608048a20700400d41034501e001e08004241550ba99000b0032242d6500d80c0d4060705a40001e001ea9050b2007940c81e0140d5a02d424818440606000401000c801400d284031588241d2288500d2062081c2013050b085034503801640401525103c0d041c032415004207401007803d030300c0440d0354135101d4140c3e000310660f00714012920102c41a0991308403009a19a44070309a00d074407030039600908601120400b0107110003541c100d488102d4000701 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 807928669 1250 807927419 807927437
    0x7120605130b0a0605010f0f1d0409050304060306030c092705010b031203040506130827040507050a020114070e040e0c040e0304030c0e042406030c0603020c01050a2307 74
    0x9182e4010000554110540903111603051285590210200a00a455140201200010480180481c0048201e00603ea0b2050618050f55107440d00400210b650040c00c50340d42d183e0302c030030050080020740070803543c640c0300c014001491001c2d4001c0058624442d420f0352440d541c9032640030208001480210b4a42d5240d040e07241182e501031082c10760307400d220a4000c2d039a1900e0b00e041ca080080c01800c507900c40c01d110b41002c0c0803c5c0401c0c25185030a0145401d017180c0d80c00c3c1c50340355603481289204240e01074104800c024542d980100540452041c42e00280214034002c411864880d400304c9801c2d0029041c0000340006182c42d4005012202c0740c4025511030107910b501007800e071135503002c1d80c809903030000070208100401d218a500003810807064682a50905980d8819030032030500d51841d480e010702c01410305940c4154410b100031076010001921880e40c40c9405006504541071240c559441d0200240004c40300b400f03106180a29000b8445801d8403c0c90a00e948100280800041183c101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 807929919 1250 807928669 807928673
    0x203041205090a150e0112060308070807060608010c0c1a060f0d0f08041706010602010204080a06091a0906010614040f15021e0102120603190605070c02090406060e07020712060513 79
    0x82c0c00c401c56176600c0c1e2265500314000902070a4416542c0340d0624039081c0c081010803000000d41e1401c03580422a03940e50545414200081e00302c82d0880d4609500e00300c5001c016540102e00c00d5002403140d08503000d01750a4400302c0043c2482114090380000d44986018524a400c000110015101d80001d00d00070130640c42d1a002d9401c03540182c10020101c401b55010003d0030004c8500500d15071001750b00d028140400c0d90f4603244100c60091150b40c44000500804c03c0400718560414a0040c4031003031440c2038007545586003028461180030a092954501e44a0004022241074032004403221544518005240d030f03050120749640004c50085030503181c445440143d59283c0c20094400140c2c4030003401b0144e2210076000341c0524404d034031860740841c114849803160380303030300b90440c100040c996510030f4150385088001900a60010b0700d50104030070400f5a500c05004e03200205c1c501003072035551090690341c079404d0303008041c56a401414441c0000c1c20300d03000a5401901594007034544000d503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 807931169 1250 807929919 807929939
    0x5070801030201230f130807120f0c080f1b0a05180901271106070f14190507030b160203070b070c020607150b010914010c0812010f0e01090203041205090a 68
    0x4600f01d05171340600010510300881e1100705000c09400c3c2031003e04681403416003661014598500000d0050342400310220a015801360800c0c02407142c00706072403d8a400c104030a444519040f4146404140f642c55464a42000d50010003601e80107050145030034080c04906643d102c0040910300340b07640794889400d1a2615074210500290000c0354071700d40d5509440d20071024405013501c40d01a4909100c81004606006540280d4541050303050300c103010020003003800c0010302c034040890b0b04000c20038503041000000d50803007200d00403200c4580b142c8944151101c41c11f00b02c0843e500580c402d00040700032517152144260414260300340901700d01c420380d000c20b080f90002c6400303495440b4140503c2c00072104500811419000c01d10780821283c2c01c03e4041800c0c070402882503410403504e00c18100401c0b0300c8200700c0755540004512240650394610705844410018010801c03030b85c030054000590035041d402600c1c05140c0c0500142c105c034418000813601e942005039103580c02104401d00180e00511 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 807932419 1250 807931169 807931177
    0x60212190e01052a211801200a1112090321120a060e0f01090f0905120901020307021807020d02160e0403021603060b04240b03130b07030b130507080103020123 70
    0x100285c0800525020b128480a6090343c0242e44259050080c440806844442c3e40140310503501003550300c41d40d841c1c4c01200c015000001e42c10207441025014280c880703205001d000c1c010001c804440000d00d2100d10002c3c40e03a0f201e8002426544140701002e03405c5c0045e0303240e0380d00c10741044c030008245540340c50a000c13002d01500c850401600c19401031102032000d018210115950401c00d0108140310b0780c60a07038850140103440d09108000c82d00d4400707a8130900032178407401c1e0010552902d8240c40d0440256441d000da130814013610940483e1a1400d001040502401189240b1860030034900004c2242080006000700c0841c00380443c8940e4040500031840051405601c000808004000610085a00e800038041828444001e0004508079030410b0405489a1506080d00c0340ca40b80d420480c0342d600260300030720200c0c002081165a581c160f000c642a01003c5900c4260380c00080e4903401261026201500000e6806005102550140c04403005d0b25201802500b101560402d4094550300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 807933669 1250 807932419 807932467
    0x50c120301090c032307081909080a080f0f1303030209090f060a08120d0e0307140a03020607080402061209030c030d1e0c0f0c060212190e01052a 64
    0x158a1807000200355040c440c43c0039049000404107003581c40f2015817822168010200307000c001d01980015081c00000f0b16140040195003014844000707549080000c07501b2030907410001030425030015000d82a495030300c40c0104104102c04109413148401035003040b40f8580281c0501d0740070010144192240301011b0322a13092344c01801c460b810601308003da5200c3d50390200b0308681c001c1c558921400c4400c011a0440c1c44804c40000300c030034107055118218090808003070012404141c0100c1141030200c0c440d64641d200350f098442c10341d6140000d5601101c00c0e10040d41002d030178007140014013036400304160080c5101040340c0c140700280141510350741c4011102c50009840e0003010341407541402a1900507031140c030091100350110140100f00e040844003030340c2000980d00c105010301407945d049440c0c1003110300c402905840d00445070b0401d0301c080d5404503440b17840c100091400800c107104950042c10300328030002041014401004140c0c042c0341003415500010090b0310070f89550f07007100e40c001c48 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 807934919 1250 807933669 807933671
    0x702031203180c150909061c1a0601090f063e0c0d0b1b04050a030602121302010906050a09080a2103050106080103080a0513080f100e0d050c12030109 66
    0x50120310b49040800c4441070f6801070342404152551851440c00741c0703c0000d402d0769002507a940c1c44001890403103c01c02c8000c0c9100440e421982070024903a80b1b8041c580101d11615056100c6600444400c1040d00c1507030951020302805101031480794034a0000440f52000c85040d00b890700703049824140d101d0305010344444a255440c42d00240901810240050484400303402140d240c8a601c4c902d1001840c2c01100e00079030f06100342207a050029035020303000c0603002c56112a00ca1420744c00a60180b07201289001d011000907401e9490480d440c64065810796500e41d0042c50a0f8050712070307400001c0c440f024801500b20209101208102c00308046001e264003000107200c0141400f110502d020100e0201814100103221064000b4100c9045a500050241e91070001c3d5130216500d000725591582114450100018045400540c0d0303803910900c4015140340071207080f000d50840f01d461540074840d422180402085900640182c11800c1a00090781c00c40c8604041076a92540241c010700354807 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 807936169 1250 807934919 807934951
    0x3031b2b0e0102180d1a13060b3010020d060e0f0108150402180414060a0e071403010e0738071112010e060f0702030405150702031203 59
    0x311028040d050005940328000c51800da036100c00380030072203005080301c0d0061311108203400070407091031081d8010754140c1100c0744507401d0003000828800003030182a90040c0c140304030018145032886204800b03181c0481c42c2c112101000310a400203200d82043c1c04100e00880302c001030040224002407000d03c8440e0b000007042070510440200718600900200d091000610041c042144000340c40040e4001c0d0780302c01001c5035030b14400034029281111500d84001a01400c3c0003c11580004c08901c0301c91003015504ca65803040d0316074040340e40384010706e8556070145a0402a00345074807a0141514030107400810428400242c1901d400c1144d40040800541e00101905011001244120054007917030011007040c03503075160303980c036010325440501010140c41d00012103503280d480c0403a40c0a1190024404403d000b0509038456004488216100d414400016444d501c084211016070b40000c2c402c41204c1c07400e5581403025045070030200c2e0140f150410440305040800042d61052449222003840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 807937419 1250 807936169 807936247
    0xb150c0105220f020406090f020c060c0a30111801030c050306090a0b041802010e030309030d21060f09200a11010213031109071103031b 60
    0x3118001828581030084403145450600100411584843d4020100c8a000e003d00d0002800510301d650295030310b40e18028900900c00c1054010b4140291600e059620a643d40344580055105070607000000508070400e10700c180000d48580c19001d4039214071514016440c0d840f040c212140c001a02403151000304001c036045c181c40c44840004d420a1905102c0f101070581e000c1c0c800d0001400491080e41640005590703010664040811124024014400c10b120344201c1600160f042c8801e80c00604e000c100701809060004c2200c0d0720440190040641d1900800100d607001c6c1802200103014000f038910030724403512401018064490204c20007281490008000121600c200446440c20600c1c040441074240c1d040070340740c0034640b0741031050080c18840302681c02403141002203410110b0a030804010b004105480020b03034001581c0c640000d8944120a40d032001c030a50000c0042c0e4030801c00500c0c01241190040029801d4440d0f540c1841200c640ca00745540700300be20314a6004140583c051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 807938669 1250 807937419 807937421
    0x20a02070b181009030b0a050a092004060b0301030807060504021c0c05010f081b0306010905030106030b0f0606040e0103030315090e060924180f07060918050708070f030b150c01 78
    0xd0703041801314146180d40300c2c0031224004208040b003503503d000044801c03074a500708910302d80d8840040903400001030101d94995405c50300c2c0c1401107140c00c2c00440c40c404a002102c0c16250440041420170000740d8801000d06401807080340c0042c03007903044286029550380c3c0094071500c59880c04541c5424240010707c00c0780c0001c0024200301c1000281b00b40840036510044007616044490395aa655040041e504110660301981c3c1540ca8184000141314591a849001d8030030f02035803a0f00f035144c1404100403405107010750010b2000c510010000240a54050381400024807500100540c0e5404804101c80041d260b150503604a03034104001da802c14007c041c4034490200582240702480d041403c104ca4009040040030300700d000900003883c0c010003008070030044840465210a4035148001e0104805201c1c0700d1490500c20112003401c0304502540f4400c00c0d184c4d0f0b45031419a54004121450465100c66109040d51000080c1ea00c0d25007006018030b210f0850038855403004e208000034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 807939919 1250 807938669 807938689
    0x114030c0301090b0d0b24060f030a0c05041d0a29040b0102190215040e13060f0225020a03080301080f070e040305030c1c02070c032f04020a02070b18 66
    0x500c188030a803000c200041c2c80c403241e1a0008007e60760f0364102c0340030110f0a0807406401030115403051000c580311000ca0b03041780c025031203a81c3c03005060000c840a0402554903000754058440c03030f510350b01000c1c02c075800e01940c0d0503801300c001d07580800d8681e1913a0030842207890b800c01c5400d4840d40c0e51200906c0b402c0030f004a007090308003031000701401022070500f030381803044000c4d00078030640740082c5601d41130000b1020b440181202c0d5601c1442428144261150000303800821982181880483e204200440c0f094610700b54910340070088203907450320905580115040103d070303c142602c3d00400400d2401018501800c034040007440d00303444021500b440d0006544c410000d46c0ca25204010002380e01c102500c2e004503d60070025281c1c0c001a4103003420503039250700c0204040c0b02050180c2480502c8602008484c02000c0c0740200e082d070410b04540c1d0151320f0500c00084c0c3c00006181c012810701d613005040b521080c1c8140c03014540c039100341c5245a40300c4003100e00d516402d900c1c082c000340b9040d0030f04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 807941169 1250 807939919 807939941
    0x90813140109050307050d03050d051e1003030f080403031514150c07030209130f03170915161407060f060518130f080c060702010606030b130504020114030c030109 72
    0x600d40a0f00c1c00002030703503899050003003600440e508401c0004060003217080d1620452003010a00492806403604400a15041904500300303e500011840512021082506498156440b1403aa0904000c191043c0ba40903004038101030f075420318910321003404034008c00a8100c5110000c0481a2602081214016101c015142e440d041007500c1d111035000a0351001c882d8181d405889a54450000f410b03d8809400c0c083c4c9020003000d940020035502401c56150101e00198021140e1595041c895584006039a0401e6441c0020007046039540c14221402c1450340a240c05142c00e000d036071014600707400103e02281c0c110344500105045403194084d141c090304c81500c408011510300303095080e5a041c098030208403000d81e8440d603800d0154042418400942200000d9514411131042e0340e41c81c10103c5112005502e42000422a1480f902920101e0b0600802070744049500f15450300042c04094022418401d010b0b191140041d00000614451003400707560b26103d40c501020701c4142e074409204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 807942419 1250 807941169 807941177
    0x120201060506091c2907030c080603152a070501061d0417071403030a050108010608070306020f0c1207030e04021201210b13051606140c010908131401 66
    0x40c0710720303102c0041004d074101c0c450700c94940c191224280a41d80d80e900940c0b6240f040101440842d034005040d8549020384401e40e801c110014204800715058203042d2042c590507002010460008110ba4503620307001080c00104402004401d008032444011590264400001c00302720882405400c1c8244d000406175203130b85001000400c62003107003402009000900000718014040d080c1c411310000d41c0c1c01d0b280d02404003034807405030021807543d0b9042202d0340b5003054200800800c600c0418080d01c002c4402c0780004100f01c1d400c65454001a4200b20801965114213000d154440b0100b040344614000c80d01c130200d80c3c1c82c1100d0074004c014429940450740281e004000e10b1503524041701341141118403a40480c480880c1141d51802d943c1152403002c0d01d000c613140140400c81e4403441d000c58000d0310800490b42030044d034040c3c00031031824512400f00415599035500c900e440d4120700821010688400001d5510b80a582d03070b040a810100008115110322a000d0060403018a21095180c0f82424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 807943669 1250 807942419 807942427
    0x1e041205060906070516050f0111030402042009010e040209100903050f0309030304180902030a0615061b06021308030706020a0e030c030a060e120c010f050106110601210f120201060506 81
    0x800303030082c81903d22045a0071440004101800410300c03400c80070b00084802407002c0d104103090ac0945800a55060f4816031903c0170100441401c1e501481ca001901d040d0207007080100401920f4268030a2120f541050b02041a80c2c4281d88440900140340c0f440d80b07030002c509080d42005840c182003d120000a6442080710261564000064030304840d604000e141802030682c3d150b03800383c2401c0400940510030114541e0802115401c2404414a040901c145041d0745000490b070200c007407040c0d10283c0d000340034000046034840c0c004191039484000c1c210845981c2d45000c3d483d5500070507064030959404034184070940d03400340d040740030f5290440c020303c901403001e00043c0d2a40041c10004008c0c545c1c54168164230034003408080003100042c000c0f40d464143c0c070700205010303021406800748000c1c034010011072247d0003805110391000404008102c26824070302c5014605100c892594903a101160401d00092130500100442c18421032030000384000141000c0e083d40d480350059845030707000340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 807944919 1250 807943669 807943681
    0x3140d0b0d0b220b0f0c190206010302010e040c08010306050a090c08010b0307170c040504060b0a03061d03070c18090206071a0c0f1e0408030a11070e04020609061e041205060906 78
    0x135100f03402c05014240402641c4415080407598412135507412030391380b299407211820303940125205040b45d000382c0311825010000703800c20084802c820541004142c44c140180b000c54080d0b4091903100790065400240007074540c80e4802480c17901c0d400104580e44941c0455480d003014030a1400400c6441c01d41c04415004450b01502c5a0443c580c880c05903030b4440c0007400340611508811202d080260038110155200c0c2001070107400340d00110700e03c103448900441c2128400100300c40e403a9401450050169080041c00030b424141e2400c81d4407507e03201c5001d04003694840f00100081807150210352110f5040700d150280c0d50000030070008080c40306000d41c202c01d000c00c004071111403884882001d0107145102ca240c0d901d001307540245040344000b00f4012400c0342c2044410022241d0007003192012580c6a8000704d45000480d8001d4118078140400711203420300c000a801100045c802040030408141c094101030f0700b19500014400030543e0403402444420b11010f500003211101800303442c9051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 807946169 1250 807944919 807944933
    0x5031903062108130e070c0501060b04080d180510032909070e031f020a02070b0f0a03020d020d090b160c12180305060f2203140d0b0d0b22 61
    0x32090203440b44100013a41802094840c4440c400780991a090740c01c07905020320001c2c0344031842581101d02d03619003803020074011048420f4604403488940100715000d81080c0844101c440a403000c1c00c030b41e10b4070501084558611243c501c0d0030703400e07a90000f025000300c42c3d41c90010060020043c14015078203041c480d00d4461240040c1c0c003031020309120b0308100001d0042858400000350200b9080c40045010302070304201d80040c00380ca040e541c01c4905094035820942e105108071079041d00826030421814102c81c1c02500035080002da809001801c008d0b0200700320055842001c0b00f00c50202686003000b5084080340b07050440c102c001d190810550855640f04900003200000d02004c2c401600105518140e4040f04c0e4405141d000050394006e092024041888103025521024200c5080d08409105a030300801e440719550940c0d901c01c450100e11200c1c1a071f0394070549101c200b080d111860503181e80c41e62008000349500c1102e4814152400f041001200e9101039100c18035242842140d9000ca40700b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 807947419 1250 807946169 807946229
    0x50106211a011103090405040b04030f0f12053409060906210b0316060f1403040615120804050f0103020405031c12061707082107020402070503190306 66
    0x20308100d10041c00480351107145005d043c1c03511317900a007084100404c0111245145008600c02e4450f5690160050f00586e204d50210f465100080c0304103607094100c41403900000e80043c1d0f80c900040d0002a40303c1c030030003910280601c03202c920030301081125403690b01401c440010314080c54003400c29814140014401c4c0b20074035000302d03100d0710981c9002d411100c44c0d00810700c0303d00040071203d2440400e00003103c8850b141c498040480d000140c0341440c03034020055444429880401e4610b035558a03555080140902003002d01c01150f0030340d012a1f13001c0220300b500002400340c1102911117140100300702c0301040840341241010b0041c08100495100000d03403c60164041940850f1402025800c486100ca03402800101702c0c20300c1d00000b9040c840ba1001c40e441080038080d1400705460303070702d21a500d28003886000503480422648501c1d041c000302c06011000d2000344054900003003901c44918507000383e203480c02c044410142003011540c1505c0344c04028180780701c054140028014140641420b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 807948669 1250 807947419 807947471
    0xd021b090118090f201201180213020909040311010b0301060302060d0c0201091e1b03111002031e0319090b061c0503030109060503061e04121b0b090c06030405060c1b0105010621 78
    0x301c002b0440120182d181c0586003141c0010340207a0740c1d450f213420028a1150340c003030080d42d80e529090348006d550506014140070342c1d802800c25841c0041d0806014002d19403150340c0d00441d562043d210303002a50100300b040803100b00c050841ca0b900e0301d0f070402c883c5a6694803c1d202c070341c20595000700002503080c1c40c6140c44001c11207030003900354440c42c0309a0541c400e1100e00482000ca00a03c2e1402520b40c00141d805408440f160803100441c662040084418066001d0040b03c14800010f1242c42c001041c01e07403101c0343c01c03c1440b0104403680da00e1314581080c0c00131089907403211028801810100701c029884480450030421907942040b00607101c0c0c2c0050005010f0301a02808042028091030740d502c0200c80e11800311301070340c4041c1044c20341c000082d02c03405c000740a804640c520768500403040d24004c9070042c000c0c00c0582c0352421038200310f46c0300e0380122215070090b00f8440c400c50001c1c42624024865600d820b580c45113441501600803c0c41248103002500e0181881d1180c20282c03124140c00d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 807949919 1250 807948669 807948679
    0x60f030f050f0a030f170f040221060a0b030606090c19090b13060201060b04030203070b0a020a05030409061806030b24030d021b090118090f2012011802 67
    0x40e40c50600d01d09001c0580d414490354414201e002040552080f0440030001d025517450721080d1105000e5005200c017a12100c04005c41d4501090240c03414026100030322150210403402001c11112072800d080048030790404181d40e13810100d48a060a2040551181044501221520385143e1141d114022a0080040b4000200041110500555010025049c0408500c0c1c0301c0c0e2801041c141e04c0140388c09128010b50a00d1000103140c80400f099506480c0e00401804415041010b5140da075040000c6c00303000c6110303440c1c001c4007007041840100050540005d000c1000e50034406400c0c1d103051147d0320617000c18030307090080001c0b440100150b9000800c6804800c140744920b0012054003441d50081a41402184004604c0341c0e00041c0c031803214100405124007141c80c1030304209525109124801d070302403441c004080c480c041076100c0210a4410b45036070010003040c2d114000d900001e100e90b900318940360707001040e13103103400d0f11000030496941c0020b0006a44a6528850a00e003480000340a5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 807951169 1250 807949919 807949943
    0x6030c011407020d0c03060906140c0a0804050304050904050a170a0f0807020f010e0c130b0d02061308010c050705010b0a080c0f01050d02130f0902130e0a0b040f0b03010609060f03 79
    0x41d61350030015100240c20003100941ca0f604d03420004014010900100c40243c9884101180d2500850031548980c0c4481056800c088660005898201004100b2100c0d400100b001003110b03034803401c00501403801000107000140c0e091821241050080300c04504c448030074030900800a5100d110090000300302e00d000c00c0507884007101a440c3c01d09003504800709500340508016030410001e24040b86000c01c0301e400c0c03030510070506a0012100700c00f44107a08610f00000d208050f050070001025001c1e42d2a0700c614150782d03a0b0310128215551006540001607000070441c060000902428103a220115000d440103898141c00680e1805040303070550140384140303001841d03a07004405507091100c02140070341daa0003286c051110445510700030703003904401da100c002c680c4040d50320985d520b00407466011030009007007104903103040c0700040540113081d444090001d10340d1100c0c082c2c010f50085840003c5204050380d020542560b00c07070303007000707c00303619040c130401075400c0d980e00d10011aa00700400b4002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 807952419 1250 807951169 807951173
    0x21002030d0f0b01030b01050405150c071706151f03050601050c1005010807150e1516030306141e1e0d141b010507020f010e0d0308040b06030c011407 66
    0x85008840c040d540c01842c020800310494501e4000c01901242644e0400c18060308500548040c040c43c0140e6410111103000318401c02c800078001c281c1800c0c00c404a450303c940e40c0c1d05500d501000000d20110035085003007400442d43e20f09d84161114002218031251140c0f0209240c103070003000300c91000802d51240c0c085a00d42e4040c0003140c0d085070032601500c402c1d220800d071540142c0402e200d0244030f440350f8a40056200002070001180c100c1c155030f00040c001e00700c000c00c4001916035600107030f0b034103042090503507110100e1101c03078500d23100351008104249000900405014002c2d1060b004d01c3c01101000e13000d140800702d2032041d9130103c0e5180300841c0319415004001720388486440c2c2041f00700b0001d00900500d6000c001d041c2038884101d6441d000e0103a40c59011091124100d030104d0b1007804020010b00d071400005076030300d406150400003035100600040808001c0c0000350042660901484140000f09a20b1940481c064004182655045000801e9440c01180e01801e1810208803842 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 807953669 1250 807952419 807952423
    0x130e06121c090f0314060f070206040303050c041511100b010f050d0609020708030405060a06232b061103010e130f02040f02090315010609091d07030302070815040b04021002 76
    0x143c2196404940c8007034803460071012101c040300102c2c040c1c0c41480c0000c0d81d0040c0703807040d840c4100d1483d40581410f0b00d940e60300380c010703003800740422072010b00c00e201c0407c1116070800a0b80b0394082503901c002d2281c0c11034603454204010030205102480c1401500e20850341c000d40900070007015460f01c1a651000c825888004140365080089001d00004003c42803150217800380d80100d000b48140ca04c4c50f22036883c16403c039001c0c5e01c20b450100d001c0304111045103842e43c1100e20042c802034900c0000600200d1b80c00e1206046001c12003a5420811203903043c0106842040c3c004000e00540c4c51840d414600c08400400000380201082c11201c1c1090041000d16154040071981c06001400417100311100d1001941003900310354000e103d1608444030039204100c1b0181250020344a41301207030704040c602000340500f100022012502c001603402c1285003080000c00842c083d5014000306410040310343c0c00c4c0103880c03200000c0510b114042c440454142d020030303504958100c1d8000c0c01e0180003801a4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 807954919 1250 807953669 807953687
    0x20303270106060305100e060a0b0d23100617060613030c0806040212010c1418030a051c2c1216080606060f160c050303130e06121c 58
    0x4000e500744840055043e4050300894011943e0744888140642c54556080440d4408c582c0680d04c01c446920403c80800b02d00d00515003203a143e84045819582001c0604c0309400c2192a0340b0a503c4000c1044800303e41c2c441b210002c0e00030351a14100c2c07001600035094040701c001d01118490790f00080c10501d00c03103140c024a401540e0007c440e074025552100000c2d03c440e0101c609a014504140a10100300c50610546500032040e80300e10b602e0946403003052506410004178602c10b0020b0209030f01c01c03542c0401007501c0d1203128400508101603520801202a0000c4441c2c000b0702500816485410166a0103842d040e900500300d00d04c8011444000303880c0c00402080c1c0d512a008250a4244045203681136800b83ca031407030201c5070b441c0c0703030001446013920603114003206441040c001840600c01b0818800b20703030b82c018080000328035100c000103030441d03201c204070f5040c031404c0c59001c0040d16104c5500903805801241c1070903c180c40c0780c18403a01d0b4107400058480e003107802e40c005915640100c0c1e02d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 807956169 1250 807954919 807954991
    0x15040302120a0510020a08010909082b06082a152808040c08030a05040b130e010b1b0109080a030c140d0b0f06030103030c020607030c020301050705190f020303 70
    0x20340c9441500360200c0c00940c1b15000680c00030310f2850004c10fa1645c2c50048090240e4816500c503e840b40d034410315542d41c1b403120620720810404040c200c4840d00c080c0906400b0700318079006840c0044000190304d100218070300880390f180a54900b41142951795448140350705188400c0295101420021031805244108202c40307441141c110a0700c1c100d5015100340c0c07041c0c0c81452410505501c034614030350340740644a07804002030340401041c800780000c41d01a10882e1000014190305c01e4031521605140c01c0e098101511440011603248140c0006071240400740700c0c00002001021525155240c5510801110381d01f032607180e40c0002d24192081a4030304641a000c003040d600c5841340701d6071340050400810140d1203032100e81010921481c02d02e08682c1284e602d80c40e020b400710820340c280486034100c040c0580601c40c5015203600540c07000c1c007529118251660b1f4044ea00c030034010f02c190101880c4c2180e42c0400c82c603c50ba20300c8545e0008122500042c901a100c000001c0580101899184200c90 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 807957419 1250 807956169 807956173
    0x807050d050f01082505011b171c0e1905030903060405100c02030f04050d14070f050901090903020c010e0f03070305160506070c050d0f0204020310090b15040302120a05 74
    0x100042c000a148000d4141c914400030740e880000700d214000320764079480c0b821107650703411364004110a40c0600d004030040e98001c41c402c1d03144000e68640c0c01c5a0601c0300d00d094610f220015843c19482040401c120b21546200010010803a08011481d0b84603028800036040c1184000c0754170a0201c03c100307403188824010100d0340c00340381514000ba01c0f4040e0803c9250f4507401c0c204c240c00c08a0000c0151564a201465602c0c1490314213010485a100c1012050740c40041e0050400c082c11402c0c480c0102400825101c0b945031454074080c8000203034164004404a89400d0204001a40c04a8114180e02c001d10340010041c407101e0000f03101d501d46245269051203658000020040041034030701403214a01c82803184d217582c40f42440320740d03c2600001000c02c0800f0105200320300d0300c484450f800354003659111080d045a903002c20100c0c1c0c004d4450052030003400b5020031250110303002d40c01c60700f08213071021208902402c20241e001d010300e0000a10032a0101240c5070130034020010402c80f1504242 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 807958669 1250 807957419 807957421
    0x15151905032e0501030f090314071b080606100c030e0d080405030a0506060a060306030b070305101a0d0b03010b1806150f0d0605030c01080c0a020f1027020603070807050d05 76
    0x2c21840d2203081445401e01090620790341c13110311385151203244805501600c5400070301071102d90444a41e03100c076000300e400c9400d040c5444141485241301602800c140c800a010b0b50601404025640001082007810000314500c070354002540a14040d8403a0800c3c0c031415411581c900e0304410501440d04a00d40512911107108240030000404e10b008070010f035200c614075a100c520490594009000c0601103062160126420300c1c401d13407042d43d014045860b05039115460385181a1034541c0800d14044c0180e001c220a882c0c82000d200b0180c5412040b4020011000400081500c08400d02c2407490300f403000340001421515541c0e0b1040d42c54036441d08042e074400280c0840e040d1a0020060800010b00e0b0074800701e05070800080901e0132500503102c0380c0042d81c0720018100780ea8800d14501085004290303140c00c000302c0030804114503004c12880462544011904a82198038022011110f825014a1350015848000031070b45c2200d520315040c04c45540b40041550035109091000080ca0301e40340c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 807959919 1250 807958669 807958741
    0xc0501050315040f060e060307270f0c0e0127060507020a09060b07140102031e131b14010221220b2505060a15050402031515190503 58
    0x6440101a034921b0099081e090b2504d40a241d6070b80400c0c014042c003864240000a0000c00610340c1d407040a040030000f040c0b107900070407074030103948119104002084041505841c69a00080b58030b101d00c0305540300c41d40e0761446580a0304008900d1094405212000410074250b480302d00034030026100002003403120960b03d5002007601d520030301d03007585ca0750b90740e0ba1640080007060003124010706402c010340301a00c40c0ca032030b20300450b140a040701900101100c0d1010008244042c1c2080a9106e4442c00074881d1a08801e00c524031203180091f411504141e0b0b45ca211a00d00c00320380403001c2c0c0d000d00c12907200c1710041c010818020131502a9501400c0400b4001580e41d8403130010564542c0c0006a04075807894005640d584404600000703100c0c3e0448070000f54400c0072988400c0c40500301c1d00180031160b6070f0b00007150890340103641c00014030034100146802d0f400c004103105881020400c800f0b2401c00d074000740e1001800588906000c0001c000b001c102c5608441400580e454441e48000a03006492 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 807961169 1250 807959919 807959921
    0x10f021912112b020703080d05151c020406120803010b070305160807120302090603041502090d03020709050606030603030d0513062a0e0f151908040b0907030c0501050315040f 77
    0x40c1e41e80d882c0450181405502c0c0c0f500c042100c2040701d40c0064903604181104a5100180000071b000ca6014180c007d5000b0050f03586602e011080d100002801d4101420b50040c401030710f00e5500010000704001e2521340004007860126030440d1a00060191982c0b103500c0c003120741c1e00c5082400e820818400c0360741310500c181c0d034004041071761164810540d48000e40d8401c1d01039000c0e11500a40c42602400014003103000042807007144090903600610388040c042c0020000318a880d02030700140d000306014085020301c0d20540750401001ca07206421440c1c0840040c0d80c1c0c2c03040030f2240709903a0301e60021950360618181c40420440e802039081c41012002c09004004500140301d982d080d0302c210256600c1c0c00c0c01030007a60744c002e074044c10014076040c1060a003c558000e2207805081d05008011500308070042c40001c040207200b50756040e1a0382028100308101520241080c02607070080c0c03604100160f0300030307045021203000382030198507070b40da600c4c4032103071500504501070304541880c4003500b40103a1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 807962419 1250 807961169 807961213
    0x409060f08011407050315010c0c14091003050a021e0a031a07030504030504091a090a0603020a0e09030a141315030e010e0a03050906040305011a010f02191211 70
    0x1140c00030050a019000340c80c1007010292141c4011030800c00200381f0355400b03070080b01051038060400c070524521903518091807900030b600c18100d42440007a1141a4a031905407240c00550545521000c9411900c901f5113604407060b0082c03045542005808070201c1440c0ca500a210004010848541d604c1c00c015070301940640c3c0c0c02503040c11445c00942e0981c001e1240500072034059580d14105800c1615503c0207060040140d60b0030390714880701c014540d0314014041d01c510b0500c0030100d003142c910f20600401505a810002045000c101007092090000040c0c8200440c0ca2825540400b4a5104e088451081c042400d0402c1c080031004103030319503025858111a101c0e80d0307080044600c07507854a0708903488800b202050b500100612000301e0300c0342018100803000140700c0751a00f0398036541d00d0b0840d45002101c00b507503100c84180011075038200d0442c6414540302c1c00078214502c010703002c80c041210326407401002002c40c44030032000705201e40140c6c01007070009e00449090000c02c0500f001c0c0703000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 807963669 1250 807962419 807962429
    0x1906030515010807021c02010b060d06030506060307060e101b060e060915151c05060412050301030f031215170c01020f0319120c030c2304050105030604020409060f 72
    0x101c0044500807544038920151041c080c0780d000d02011a020090340c00300c41c00c080d034002c045640b140b03010304c2550b88100040100c0e482c03210b40000d489e03240d49131440c24440010300441c880c7e00200c07030130082c03140c004074112100501159040208440070400399141c0c111045203a2180385480021002c00c07419034099140d6030441c0b803c4841ca55940300b00c445e0fa805902c2c9a004540707840740d001c0340880600000c031440190000384101a4044421200c4d1841000880d00b030b11160b000300184018007506920303484803102c5034605140740d0342c107517240d03825130440c180c1303005082004d054240384500d0800ea2201c1c82ca800d0321002d200400b552210840d0080c64104207040c260f005a900d83c0c22158000a00d071030182c0c82c01000b035800c084220003161440302c183d01c4074206000e20710310541102c14680c0f0a040410480741c0b80001c2d240d44010000304850100400c080e000e004440032806901e03003540a82c1c044807001d02e803050b03803540d620010038040c1c0259401a02c0181c01d01c8004600340fa840054a010b0314 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 807964919 1250 807963669 807963691
    0x605010909060605060315240c030406090501020105060a1701060e0a06050a08190b0705221e0f0b0a140a08041502090901030209060d151a090402130b19060305 70
    0x130b480d0b6041061500c0252110481c5481410120480d4140341c071100c00781c1d405186081540302c105080c840c000b5400521030340104d03000040c0c2440400c0d00b062800003d080300784000c00080c90a203021440184039400f8645266503600c0c1540328123002500404054805201221100d00f01916401c01601c03080c024188500702188003c161100d0008041240403150048040c01031404d0303c4543c0d0980300904071108000007040704003011040b14540d41002d21b06524036248075072602d0014040c0d8841c10f007100c9820115040c0400050078504a050280c8100885480d9580d01d035102c280c1d1003d144590907100c0d1035001c82c081d4001900304d0381c814421401a1030500d9080c0c4004841301c00c034030600c00d29641c0004180d0051001d03080111200307500c0200603000301c40201240d01d0300700d1543c4001c2044c4000300d07140c0c4100900628407450b2801510416600ca00d110300f043da0002c1d0404444940103290300d9680c85511140e5550661101e1301241040000700700581c13103000c000c002c0c000881d0300c0540c80d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 807966169 1250 807964919 807964931
    0xc02070503010b090f0c0d05070531300b060102011d0714130e0606030d03090312050606042d14090711071a120702010c1b0807060501090906 62
    0x41e04042c0a48605910300a200e049503540b00480c4014201000d0b20240c0000018003041030310700e645100d058000e00340e9894407502c4150241c07490703a040c55123403504607403406da400910184451140d180c0c0705540d001c28504ca0030442d13410b00418000c01c50038248041b4500c071300c0c1240500015000c814003c081c00c0c0c2c003e00c89100307178020311001101c01e404190115400080100010702045031114498000282200f581071007484110065440d15801d6071038079004501449401d260030030404801c80e0242c00c06100b041030343c0e10068403001c001080c3e0000d1548600c0015101d036200411600906020401040f0f082d071400010742c880c0108486c00b07080e42601c044080f50030a002000c1c100c148100904060b071590b5040c6003151166035482081d6090300c5000000b00740104074914012104070350151450311111070b445940010f10003d07000750f00790b91611910810255010142032a0300301c43e4003000c08807440e1480c1c5421144a204006440580303090004a0110b20030780000365400c0c0142428005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 807967419 1250 807966169 807966179
    0x1090608010c0f050d1811040c021911060702040501030308070306120b01050607060b040e01091506080c120f0d09060f110d12110301120b130201020307080c031603030c0207 76
    0x80394102c404007408076555441d0fa00d2030500c80d0f0020000b584501001085440310a140248100c07442c1c08111a0b50601011000080c10a4441d00006802c0c2e4401040c050400f05941e054000308000043d20070702d148034800100c0d8903010122401c80c0d034040c10810583d031750303414000c2041a007910701e940007904010300002c03070381640d028007200d0ba500701c00301e044a40d2800c001c01580342d21446040b9a655101c1c003020030540c0d02e6200d9801401c03990760001c0354007012454011107108141040070059464414240b02c1c1038000248800c02c81030039101050002801b8507054500084035100400320320415008110300c82e0300240420445010792284444050445000d41e40442d6640a42d40b07181d104142000306240710320f4100300c032031251450002d501800722a154889034000d170000100c8444501480e0100705c2035400700e951041001c1001071010a680e40002e40702c3c17258803005003c034040800e4000c0303102e600f030040b02c10202d00c070301000c03a81341c64514010300944585005400035004800002038 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 807968669 1250 807967419 807967421
    0xb0f0f0c0306152208030d060b030c04060c021306061809051e07052808010f1d06060909090a020910060c0f0305130f2108030f0a1b080109060801 64
    0xb002d100c0050041d410340e4040410300900d41c1001c2074100c40c5610b842c0d5a0b6280f8070f980060300001c1d02029014582e0703203410807101400e517481d50744180d000c440304204121541080405840c2510100e00e0700d00301c01403207800091080681034503140c1351640f828030009221a00801d9822034a0301c807454000038942e540c6006400c031001144d9901d200820f060f4080d50882c10b20003502d40c07100d02402c0240c2005082114510000b0510691900c0041e0b100142c15000e504149444d0060107602241c040483c2450f45d07850100b4450900030020042c0403001c2150741d80c5100c243d692030240030b001514249000c2036201c0c0d40d0401c2d04410303030080641a000c200f2041c200c170890000d403820740c0c49045591000c1c0c3c1d5203c451014640342501000014400e040f442405424660001c0c580f182c00c44000700e080c48d8070100002c608032440310b0039607800741c0440009000101941d9114901c00030320005035890038040b41c0500030480030000030090141c4e0710400c2640042d10b084c1aa88880410080961501e002178 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 807969919 1250 807968669 807968671
    0xf1f0801120b150a1805060306100f06030917072603070c03050d09140706020d0e0108040f020301060504050c0705010605190509150319020301180309120303090b0f0f0c03 75
    0x40c0c200c0d409000090032040d507480304042140d0b0f028040c040300355030f00e0390000c8a00c0007100659844648510038807400d031808000c2160448080c0301c0000b03500b1300c0c1c030004060b0b00586200300403c0c19281c8075a0001d1203030b030119125500080e604800ea5481c010f2034100c00c0540900104482030720000f83d69103203c5030050940340300f10099201c89002200e681c806803015000303a541000101c0e02e5900d03110024034031140c0c9040c0d201c01c1030005d00c40c031030914601909118159a00b401000010b492990b00c503a440001075402a401c18007108403120b09001203401f400490700b140382c00c2410f20042c03000c0b842a220003800350502500c002c110850701c03141003145a14520b1400c800c407421005040c81646808050039411140d01038642c196021242c011070b0514824101501011005020780d406505080c051a0b215101e0182103200c002c503c0e95000c0e1442802d4000d107115061151210010140281e011101941e0003100420035171510f411100401d807402c481c03411f40c41e02d055000c030303060b060300c08141c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 807971169 1250 807969919 807969923
    0x905070807082202030a0203190309060206070e1003020903070b041703090306040816060e030409271416030b091903020c060a0c150507020606120a020f0f1f080112 72
    0x100c8504042d4544003d007030b030030f0164240c1e8075010791a0740d000181e400b084140c444420701c502140444e103160802900b05071951f404441950800d8040058a0307a00401e42e0180f2901100d244000c9944c40358103c0003170149101150b098401d1078004109032460b04003802c2250650040710301d1110403608840c0e12402143c00d443d4040e4890385c080350000d2103840250007030040800021912002984444007039444500940103250000203082c000d800050150054a07030303907904079142010700704641441d03003400214054800e4001d0800d0038416101409406065200d511420b082c442d00da0030304d1011890155071020301c6100e030f4030100383c00c9411000e00c84c000c1c0ba01500a0403010700d4100a00445501081071031040000150840b00013614105581f0401c1a00303480000303191038244000b91070070300d000e04820700c82c80d182d1800842e1080300061000a0781d5054410740c14400301200443d12028a8040559010550358041d051800031481d406590382c1d0556514211030b40e031a14001200e82c1e0070240 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 807972419 1250 807971169 807971191
    0x9041d0f03041805130c03081e0301120f14160512070e0a090f08030906192d0b040c11010b06161e1211010510060507120216090507080708 61
    0x1100c0000e80303e42d84203d03800000f06240003180c40380361382c0e402043c0c0c619800888900e071001c00c010900484456401c00c119203080796507031655040c01e03c0750141b0f41d48114020100c0c442544500104402c1c0d102c0c090340003804408070b84d026103c1d000d14002002160003098003404560845098000d0005810760031510107812001c8180c5454401c840130b40f01517841a42e0311802d101003440094100802103100d042f0480140030103042c19491a0000724520450888040c103103a001c4040c0d18802d49455002d90303556144c01c024020360006000508420718601c0e41c41894900e5036442250018402c550700741c40500200810211542040242c1c0112030501d1008181c0b0f4000340000740021159031040c01500e09190039500b165901c00020600043c0004001100080c804040070003d0227201c0d0065102d140e91900b80d820048010024002e507500601a469005a03018044d80203002c00b5610b0300721400350413600b9440704280400f410703040e43e07070303031300081e0740c4000614010301c10310390103014061140b2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 807973669 1250 807972419 807972449
    0xf1204060c080f0403060f05130209010506131d010303090609060206010501030b01020c0a03060b0a0f0e06010e01092c151f090509180f06070210050c09041d0f0304 72
    0x300c200e80e040100001220039010802c0010f20716036600d4058401180726290110381300708403a041109a07000a0f06c2c8142074a21000d0550043e03445d01c0456040d104203545aa4407220030078140e0480d0112a07115207200610031000b280c0076010002100d05890080d10f69030a4551b444500710741d5511103100d258016000704d030050020b584603030881c5d400d003401407044408180034800000c4900c90958070440b03065079102d69045041c00c10000341e400500c8100c2002103164a81120794004440003030005040141414015020b80c0c028003100010307100c4252540c1419140324040d40f521503120140c201d86030070440c0020250200b54130000c0203220080d200003c000101010500c04c3c0040620300c90074404040000f00300c94860510071441040b030b4001074a40600503242e0541450208a041c0c0308640024003045600740e0002180c001040072610300095554a03070f940e080340c03030140b40710041d807180c00e12203141c60f00c180c0780d2a40858440703201c0030760b442800c2d40c1a0306941c9104a1048280b1850166 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 807974919 1250 807973669 807973679
    0xf0604171510030b04030c12080702010b06130302330309010b09010b1902030c190b010618150c060e010209090c1c0e010207050106060804050c0402040b12180d0e030f1204 75
    0x3412a0317082403281c2440800000c040d51980a445140e916a03400100000c081020741a070902485000400a0702c2442c41c1010008140301854400d00000c1e010328056002c00e5a680300c0b0207088940d0012001388002c3c0f0344000012291168802c1c1c41c400c0700c541c2082540e000d13500d0222195412201048207852500b11080411140d040504100d207003035010901c060360142c4428031420400c5600712030800c80002503441c060300801d1040e0062800c100d08142e207001e5082005900740c056a420421a0082c40c42e4040105d8800b98a014000d00403414003d46e26018401500034100000c400c5400c400e41d5030324880c0c140382d11b015040244881e02075955000c2000c0020b0344c00403074030b01c61103130002d03190054a031a01d600b504c1450740000005070580d8200021b2040602013032140c0c1c030b41110150701d080d1a00c086603209020304447d03480e503082c049000c180000c04c0d06012048285041007546c50401500d41e015000255414945020380207046a440500070081000c4000f100b8410410f0304041c104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 807976169 1250 807974919 807974933
    0xf030e0105151c0506010612111206120109120801050f010309050316050c12030a08010602010504030f110a02220608120403031404080a06050117011a09060f060417151003 75
    0x100380103459a11a6a01240480c0003445100d010740620340b1076404e231901a4500c4011203400241e480030001c0148464016050618680c03504440c0407208091441d02d0f0001e007a00400c0c019000502040e100c500301c43c0c000d600030707451604a900403501030542090920045d401e41d035480d10010919003003007000001c04408a03c04140503402007040703800c0c002502e001704451405402c0480c10030352000c10f2804d03100b9440320b141c50160039603100030b0140f81400e9030054803070080c581c40342c41400714101400209900030041041500d400611b221280b000403030200c4504821850001c8505042c05004034401c080020301442c8800c2040049280c0351860720100e5402d6000f14090070304440402002503400000c000040c400e030b01071000060310307514000c45514094032220105030349074100560918440c60030030001d00c1000342550040381e070365980d0000895440c01049010742c8050041030101d60103c1c0024074048041c2c2410072500f0801d001c040440c2208001c03075080040a4a00b1402e100041d14 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 807977419 1250 807976169 807976189
    0x503060f0a11160602031f080d08360f030403020a090b030304031401150509040b0a0b03070b0a080405061003020a060507080d2409020c07060c020f03010603030f030e010515 76
    0x4210b601410101000c0701c10b4200003a100c0c054410703907008800c3c8005a207800d03408501c02c0480320040450f1724604202c1c140c95003080c2d8603901c18428118000369802c6000030a4460b408180c404c2c0d07000070118440c203403014188a5010240c50b1040e50707000c61401c18000211010b41c0c0e00100a04801403810060802525418a400d43c0500080c48000001010690481d80398002540003084a4071484200c0c00c881c00c090303000c036100d032482c0b00c180000324182140554009594640c04100c80110030042441c21400b42e0100e000007100040307410980d50300641301b80c01507210b0300584060391281c104682222400d80000796004a080c0c80c20031410303004100620f040e034442c0e0a00340c1072545000f107040813100b0a400d04c0c10f250004001c41c06107403014000358000b800c5c44401c118104042440b4550340c4100701c1c010081070010515020007503548440580b800e108006009024503610307440c0003044041c6500c0303200082820104080310303829041c010a0320856450b040000000764180800890600e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 807978669 1250 807977419 807977441
    0x32004090b041b050d0506060f0a030b01200a030207090218190b040f05040f2a020f010204090605011805180c1207030209120105270709020d0903090503060f0a 70
    0xb503540c00110b640b0394500f00501449405403100c81e190620264030200340d80000380b540384075200400c0f485c82410710303141c01d9a400d038409203000203082d41c0c00e00041c1d48820025940d824017204092a40740e03010b40004184824900c242d09465029598856035070a82c065444070340a0f16403128414081e81c205484e417800342030348000034014a5981d403100c2c010168020741242d0910078100b40300740000d042c1405110078810064200b000004203100c42c00d04100200d90410f06805e1864140c40b510074800c0107414400b07200740000715074807552001c80c9001030800d4803030103001c0344291111000540705d1280200803168081c0410b482140c46584a00800c50020000c01c01a2028040191140111045148100602c3d02d0050303440000500304105030005034400e00c20350b810304c03013003122a0001c11426400040821950303409071547d2081c090410381550481f11040d0f10100c0d5075042c2501031381041410500980340d0704d10840d19841459102d032011109441c41003004c8000c103030913001c2584142ca99403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 807979919 1250 807978669 807978671
    0xf11190e0f2701150e1b090103091403030106020f0313060f0302040b0a120b0609061903020c0f01050f13030206060d0c180911060c19030201021e0307032004090b04 72
    0xc80c1805110320120b04072100e09244e54138841c10107080001c2040c00007404551071002c507140303407000c0c0542e414011080c90700b201c08408140d2408590003074001030351407075215441e01c494041185c40960b49800034401c0100620520954048840c0c0100869490681ca803a0342c4030864105030341074440741241200c81040541c20000028042100c401818000000b81d45140c81c59041d000c0880a580c5071000c2d252040c00c1c20402d10b041581d94000715803c0e040c011114100714011050140e0080c017400c40441d40d07a00411030078a800c10410760086100350402510981c20791031714059165050480b40000340560301880c08505240780c40520798050074482ca0b5a8490188c4034a03500c580410544900c0884981b2244600104141c0f400580000c22003075485a05104020301e18543d1845032800400e00e569100100c1d10a052003901143c500d10005a49040c02411400301c2007006e910866010340000c1c5040410404403d02000c8100c1d4114181000b5003801d042280d4440203000c0034504035885 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 807981169 1250 807979919 807979951
    0xf05040f0b060f0d05030307030b0a0609170a0b04121b08180f19050a050414071803050102030112051e1f020705070b07150e1e0a0f11190e0f 62
    0xb0384e602c4140e45091841800079540300c1c01c02000c040e003511480c00c01c162003101c042c4030922085901510710b01c115101202460040807016803010300706080504040c142d654500c1c100700520010410000d04800320f0354070500c4211600f000005100c400100080c040b0740200304001561a22503400300c080c3d0001890103081442c0c1600144512a420407480030340d0000d028100601d240c00601b10b070091800ba0390034010040e00241105081e54014060411f214071080c085201002d1003c4400203154004000c554950b1980241e120703400031180100c80b02e100c1e0b4001e507280d8807031031a01d016004041d8030041c034048000d070f504d010100a030345170303003601d0207a0902160004c260304006080080c8444110640c0e204d4131400c01340982c902c3c084100e8481c90501809001e0380034001058a6600104903040c246107840002d00b50070300303610690140200408507461403d0200e00c000e00d03e1103d804482d8254240345541642d20400348500c00d4603040402e03803000500000d82410034642c410398182c500481c17 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 807982419 1250 807981169 807981199
    0x402010201140f010f0602030301030209010e0718140f01110604030503090a050a060c09051002061f3501091709060918090d1d040b040e03040314010f05040f0b06 71
    0x1c141000c5640c210f050400e003004020750320384194800043c182900c0514a9581150082102c460045c4111704070700809500188001d84030b0070100443d14039881c00c0b40c4299030b60b01020040c03241440f0b4a94852803950605031401c3d8003412498000c40c580d100502000d0b62a42c03402d9440b81c200070003420140c0210b0307038914000b410a1202c0b46605110380c0c40007a028204180041c8052038035089640580c8031003c0c03415103183c001035031300ea0080b09680b41c5000d078000d41850b00e400c4560b5500c10604000a000c00c4040d80c501d500014141000e41d0700e207054030f11448403c00c1d080c2d40042002506031a48801c50700c02d4070540c034004003071841028252502c2d1000c0d8001040c14441c40d4506145280d41110501103020410301c40c0c8500054945001d100e42520044c0513441440c981d142c0c01e10482d5200701110341a00c1d02d07007041850000c0181030300d85555030b9040150300d04012907d4000d1551070051f542113941c40900c10140078940020446104000c541d90f81900c01e03002910541e8400040e80c68420703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 807983669 1250 807982419 807982451
    0xc1302041206020c060109110313031b0303020909060618061303050a0f050f03090a060c06060e0720030f0304080c010f020d0209130501081f0e010e0706091203080402090402010201 79
    0x726031032040e00016030300c203c01c403080d03400d00e8010382040b4440c604200050a526108005807070300840580701e09144001c00b4507080c1c40c180c031551400c29800e200b42c1c10441c28140c03d0340c013034402d00d40c0c01d41e0840c0c040e40e02d4004120041c4075803401ca9860010a080380036503801c000c8050450003d00e43c038802060f5849840d0740e4a0404051b030203d0320050006881e00821009214800307407401008000c40c00c1441e0f03c4c001840d1490f07035000319020030072030b01410014054160030250081c014801d08400500345032400401c00c80300034031107184895645580c516112000412100c5006104d401e0746d0070340d280c03a03403294002c4e44000d40840c0303550348500c0c03100244d040c21702c0204401c3c0145c0741c005039120b190300280904413100402d101901860680100140140850040001c600d4032202031032807180606010010480d040030350000350b10b44080c4800913003000503c102075607010745a50325900d40c3d034004450122072480300103000500c3c00000c41d0050401808803038201c1d00c1400040b90034211002c000c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 807984919 1250 807983669 807983699
    0x1f030207020418020307090b090411040f0608010b01020c06070803150d170405090f07090e060d0b0c090103051b0405060d140411130b09040f0302010e0706030608010c030501080c130204 81
    0xc903c8001801e80f00b01140b0f000c202c4000204444441031040f011414001030000a00800113000c105c895182c404180e541c0b0750000d4507140c0c08000810120791240880c40c000c100340f9100601501c02c00c8003002c4586402400c1e95111340e4481c014925640d00e804440383c0c58820f00300780540010500200348002041d55000751041e078100c002c01c94071940340104104000d43d0251081d003084981c1c0c4180100f084c4d201310001c1c140c90360342801d15050784440000c1000114109400703025003145c1410700807242010030081050200076601840161101240360072901c520005003400321100304010019810b20902600554025400024080102c02602036418904890450700600202c003071503080d1900200311980000e00d14020442200f180f0049420604050406010400100442c4007050301c00d4101d460000d040034140c9000035a40e00303003d40a000280150352265081602402e0301e1032180c482c0c02d04894424004040c1624001c0510521109984000400a40800001c00c81110b036010380 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 807986169 1250 807984919 807984941
    0x31808010509010c1d150f1305030f07080a0b040206040308030106050d1a01050406111c1d0103091205030403090b0414011107050a0e191406040506010e1f0302070204 73
    0x1180c0c62070111000ca0071101c4d11401c4c1c0080c043c807480500040c840b240d442c000c950b0801e5075500011240b08034a0301840c0158081c0080311440094140c0070b18003024041d0302211402e60444110381c8095a55a0b01c50000d030007917034265481b00c8513120204212150183e00140050070b041c2c941516511006a9130b8026000700020400c0003500300c41e08081d6214104240412240e40c1c0142461640028440e1003a485000c0401048010405041c0c8041c0b020101c681c040c9118040e01080c003400123003490614144d404143c06d1448480000741d4080d0003021000b0354469aa003540e10003128042d0f51607080503000b54100701c19090041600000d804c01400501680310001004000b140001094020b91580c085a65044403074104100c0c2c84082e404400d40d1855490256640d580000a031450b24580d00c24008190814148031a0140f01700d001d18090039003960300780b0040e56010010b507248849145105c0e04051b022020742002d001c4111907131520042d40c9405490440f0940004003694000651 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 807987419 1250 807986169 807986171
    0x108011a0306013501031e03021209030f0304030b07080a0603020108040803040f0506040302101104081902220b100201200c120c100b09010b091302250201080a020f0d0903180801 78
    0x50007808510500511f180341660b800000c4a18580c1c0d0003911110003204a0341042004140c0300d0341f030340d01031121694a16011003143e0301c071550b0b400d00c01441902542d20343d010807400c7d0b01044501c500d0f40030720000e0701d8042c5c50380802911540d45460044d40000c20aa07403c5059416a000041080c429980500d000740c2c010070508101c42d840301c00b12079444034400100d034003c04c001c1050040100700c1c941d441c2040d9401c05850103860000c20420f24151821485000110b02500003040140c8c0c0211100c0340241e4010404040300c0304103034200c400b4094885a15a00711107084600c0170300000030811600c8000a540d2100000341203401203400c1035110504a4000589403949040c2c54442d40f210300e8400c6600c1c194551400858030310910440b80709a0080039113a0309590418066012140040316410785051000440814401903007810603040340080c500780c3c01728080300703454001e4841001e20401e041c1c2c9060380d224407450060001e64800c0f4140106419440c00780000d6004401c010f0100ca00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 807988669 1250 807987419 807987421
    0xb0c0c010206061c02091308031303090b0f03191104030b0f091c082208090f0102010b061803012a0f1412070c140c0108011a03060135 59
    0x10001e401c01c40002e01c443d004414600e06403c01000c00b8540070740140d01035030610340d0b1383c464680032402400c000502601c0080000203110b6101c0401c19949078642c026580c0341315072500c41089102c140b14204621135403120030310128512061610314a00e444120f81d00c00290b0780c1c2000c21400103a0065031003941c0172200942080024050180c8040e807010041010340b00c0e0190002c95804aa02294007c008002001c000107401d030580c107136012514412100804099060b038503010040740e21644109014021188420001c2d50050003240c1c9c040300010045030130440300b42d00002c81c50700800b010302c1c0d00d0341d280d01180fa5040055240140d100b40c4407141d222000c18100d802030841081d600d910020461107900340c0c01401c103007070144c40e80316070700c0c2c4c00c40b01e070319150b0b614101c6d080207040402606410440c00d00840c4258002031200c0040020b0b01e5514050380e0b03525007a50800004800b51101e12020400a40c441d8400c0403440511844898907036800070320000c207003020144145560b400080040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 807989919 1250 807988669 807988693
    0x2030709180618200a0908070f031505070207060c02030712030302300a2f0a030609050c040b0306060f0304061a0402072604080a061d030a0f050d060b0c 67
    0x2143d1030250303482108148800304665250300c40c003030440c12000c50320300f00200301050b9051062551000800c46001200c4145403141e01b070880e110014802143c118045043c4800380b00040e000d01803152482d81c000d060028901082940d074210240b00032030303260084e1200441c19046800c410100d603400b90354016120344e09085080d20448140147c01c2c000f1100035402542081d0491056038800322018011401d400d4075080615054035980c038a0380c4200c000c158414001d409007010f046102c070184c1c0c00707100c420354902e020001c4032400d0b110b0404640007080180040c141c02c1c00110781222010f8582850900032000708040d580040e034040b86d04a440e4a03070340101500a154040320f041044a085180050301d5858204024540a4038026420488010780000c40307a041501c0c010840e00040e5440da0045d071034103400608d941410000e68040034051103a0603203002090310110b14441c1c070b88114081a2102c1a241c80d00b104a02a00280d1a05404038507170b10190050103400303c1040092441a070a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 807991169 1250 807989919 807989939
    0x4180903111203040305210906040b070f0c0602030903090d030f1d0117071101090f050d0908030304060506190b0c07090b0307090504060e0a0b07080108011a04020307091806 76
    0x810021074641d032010128014001039182107a8001d98541032095592100c1141242c4616403140d0f410748600700c1c0713000c2040d02040450894411441568400c0943da03410780c081d500c1d002540010800500c401d00303640c0005006074015030f0001520320441c1c1c14034a11030001406a051420101c000990300400140384942022840c0100800b000d0400c1c3d4002300e090001308041c05c1d142c10f0f09103090060b8049aa4076000784c80342900c0e002900c0c024011241039052802c51401090270450f4240308291200040a01c201000f4007910141c0c4041d502c0e41d01c81e500c8150141030040c00781d5a01c034003680c01121810a51126010040002101c002c0c0c40302c0c5038103041e0341400c0c003981c0b080c1c0390241017541c1e29202e6680442d060054480381c000010b81c0ba100c1e400d10314014480080914510302c40c05c5121824418116a030764801c80706070391078904603a22800f240b801c0e24000b0101e01c48045070000001140d28103034018580c00f15447c507001c070216540d101002412032401d841d10314086c0c3d456006028003050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 807992419 1250 807991169 807991187
    0x706091208010b09010f0c03030b03010513020901050a15050d0e06011502061b0d322205030306010c0f0f060b0f06070b011a0d02040e15011b02060d0204180903 70
    0x3449441e4184504040082c0181c998480040c6c100001c004054081601a0b40718030400d000c0075000704410f141915840c1034841820001b68858900500001024078051414030241e65003118064002860040d0584a076044080416407403601e03680c00400150041148174020702e00c00605441d10050010040e00709070300501803030740c1040d014103038101c40702100040b070b00200c01c1e20b20005441200014015101e02c5220119095280c080c01403045240121029500600117181b8400354491035406151410601d00c0b00100903401c140005030056015254070041c05010f22a4904800b80341c1d601d4000e401310080c030440c0c91a581c1c1340d00c00302500340b04140da500ea100c03c1d6442c518107021500d035039102c2c80c01440b410113900440d00ea10a0800b0b001d1081d02c801c4c4d03505074001e645031511003924082c80c2d40c048035001000090784181140d1507202d006015a204920401e10030ba0a0b03941c1c0170b001c0c0507840700141c2501250204000540b4500070000074a04002001000411070a0703885c0c002c0108038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 807993669 1250 807992419 807992429
    0x210f030c0a150504051f020c0106080a0c05010804170906040b0c0109171317190501061e051008070201023f1006030510150804330b0303070609120801 66
    0x40f502e002c12000507400600c01000709031422a00492a0490b0082ca0180c4900c1d00408155420401d00203048100010444811403085456968042c1c40d1001100d182c58107c401416800c4010006101c5002c014001c043d0306e04c01401941c42c0c5519000c1c800c0b0b2652044615416586d56400c0d00c1c01030044040c044c25400c0b1142c03100520305481c514103800c6048041c003480b045072640201c3c00c030038081c0400005c00c0c1c01c516240131230380101c2d0504140d4000c00c440d11609002c0c41281654050420b49043d18506561008007030b070031a141720b064110340d08003005044105665003040441e5242e01030100c0001d041c02104091800604442e444030301c0003007130101400ba100400000c2c000c00861400c00030095454500c0c0c00601941c40d80c900d40050340c0d481d40106041d0044009150b54964001c9645210b0340c010300c0d009814003072851200126a03a40c2110700c11845006c803102141c1030b0103400541d500240142100c2c1040083c0c0c03610300460342032200460304d2645281143c2092030b003000000d40148 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 807994919 1250 807993669 807993671
    0xd18061104080a03030f0603120c0c290a03090b10080705040b060703140d02071416030201051603211e0b240c070608070210050105210f030c0a15 64
    0x103481c2c40c0b0510303540c90550000030141074840900f030030700081d607601040040d0703009000c0d0112128100c8016000c1d184081d01a20442001e07200400c542010308140e4548507180301100c0e2652070080f42050440c1c020340700794810184c856600c800850a00d00740c050007202084001c507441071819823414a00821580800d006034149010503441d55107100c107864100e9010300b0610540198450740004501c103278002c41a58510119131901806407450b0301100c0e0740c40e510b04454403002900700350040b44202d440300a000810030408004881414031800d40601d00c242460208103080b28803c0841c0c5000f00400c445030b596444408080c4a9603d0081c4c4142100760010007400d181000422000b00702075006150b046d0b090421004c10207a454100c5814206680642c3c44141d01c40307600508102003035900000503c50301104076404289440340c0c2d4100c1d44014041440c994810041004403e890481141d250181c0c0502c40c1d600241407009010081c828000f13009080e0280c0340c40c0d20442645003082d0285 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 807996169 1250 807994919 807994927
    0xf0c040b04150519081218011806120605041103060102010b0108190207230607141305090402030a200a0b0301031119050a060e130b060301030f02060d180611 69
    0xd1010144840aa50043e58131140141c0d0140d80c5890302040c95000100601c903081034040520300000181040700c200011080d000d0742031000440c1d08400c150091703888403007190b000304601c42c003d0b0001c999482d0301000103c0c81a0b500c000250440302129506030110740c0000401519690a2007240c180303050900703251105003030504a4a00c80c0c00e0f201101300025500003401020701a02c003441c0e80b10410205242002d01e440303101c82540702d00b015501d080100f40c00090204015010b102500d1035240e44c000201805454101040300f0440044c0040c1d03014001d440e20038006c68006440282101104080412004202001d00840a10a5010107510f940520044c8001100176015072900c0700104e4560b428080a098110a02ca98603440151301000e52880003a40b1504002c0b004c0c01601c3c2180c840c0102d442040e028401d498410780e9a0364044401c100500004001c0b1705c1c24400640058030040c280302060300310f04104c80a404880004031114001c0d5003c00205004110b13003d50708228140c01c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 807997419 1250 807996169 807996191
    0x310321030507171902070f26090103050c090d0b1005010f050f0a030b0a12030e0303040f060c0602040e13150902030606040207020315041b080d17090f0f0c040b04 71
    0x80200c3c2d2100b59103600100c202180c451015080781c038001c034004000842d5078002501d82500000b511390011592900d401c007214081217070801d112020b8800340900d140c60151040b0044000340700c01008500841c0c0306001c04283d50300e0f0003480090b060b11804d01090340c0c0c05c1400d50300800011541c0901e0402c1501c3e041c4130070390340d8403005075100810000030141d1a11020002907018140c0d542185410100b411400110041a44002c2d042a4040d460300d46c8074a075135100345516031003940070b00842c414280c0e008000da02d00c1002c2401c070081c090a001800c00b500d40c20040da03020780036208041548034080285045c400f0f2241500481c100781101003240743c6040d0701080e00c611000b0503040c8140c3e40410344100b55242408142c2c000b42d03802601e01e269103014130b000c645280340031080c0b66141c00e400401090424001640594500280d01d4a005440705441241340da084000c02650040c0110310b030440302d41c1020030200516102d100081c2441888140a120440e000c1103000d0344039034140f00080c21 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 807998669 1250 807997419 807997427
    0x10f0905120c073303020418110712120501030c060801080a170306040b03100614060309150601050909040b0a0c030b011d01090803030c0c0c040c05310321030507 71
    0x21900e624404520780802c5003a04e040c0303210ba84264440070700c43c00354002491a8943c0c000c00541c6c0e550503115911207a09016071049400c03010405010510401480d004101c6c0340c0c4159a101001d450b00c201481d500c0d024240680c0e0081e8400c80c0d00000305d0b0402d101c4107810055450140c04800700820340c0d02019220800784002003001004100c100002180e0300340c580d43c000b02d01d05440070f030466507620402369030a001400755116000b8074481d510525011450280d0440340921109001844039001c04207440000d140090415418050300f0402007030703587c1f030300d5801034440c40c012090110765180540700c403007d603400035001e40d08251a16541c00c41580c1c1056410790349060854010344131024620051303a0851081d0032542072032002104101004000900502102d0052800c0c0c8103401888414081070340c03200d809100200e2028849000d1500c04040c250054000300d019600c40d90f80d03074031201c038818a455082a0381010161018030803c40801441c032070001410303c1c1c100628030300180024 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 807999919 1250 807998669 807998683
    0x1e0506060f0904140f0f0609010c0c02011d0109050a0e06040e0304080a0b1017070f050105030403090501080a14090109021e0f060307210207120918110705010f0905120c 74
    0x8069940829000c07048000c208645d10b100107440c01140c401481c0902c1d005c2da0348800f141c21104039800d02d0440400385108031014090b90340d060710365a12400d0085003a0310b0440003260b0075030400c0301d00d580005840d66800c039490f0081203070030019821410300c0350500c010364000204507070242d030081000b0001c92800040c120724a50f0030020a1039180c851403030549420a01e644510240b0038904c0300c0040049022480404440f041225000c4a42c1e03580010746071030204036800b5020036200d200130802c55020700c5100b41d0052030a13600190072640c100c41040046025200158540c0d074030035921085042c1005000307080c22000108506280303a510009040300805081070380101808004520382500468000000700c8040004d0401c15401e410000000d41046006403000400440101314841c02540b043e000c1d5005512000c56007406014540701030001c80b11910440c0f08104202d0700810303428420b0100c112000c00c0c010900c0102401c01e9450081002d6003400165400c110054402400103030301 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 808001169 1250 807999919 807999923
    0x80f0a111903090b101503060602210c0105042906060a03090201021009050a0c0b09012003041a0417070b0d0902040b03030d14010602010e1f091e0506060f0904 70
    0x1e4074512001c00d0490241240707807001400005001d05109103031014580e0b20f815034954035512080300d0542d8000704d00380e40c2184141b10241c0c10012070406003c0300c100e400380c1d4422500790000d18200304214000d003100c6003114140d500b04040065800d03a900c2d41069a082148541313451211428007000240c1d040c8142502a41410f81d90505c0c101164006e120600d8848442e1030700f080034841604013070361603458040d07080390481c14183c004100030301d594054610115045e91880340b0f401e0300c0d60748103942c0b010181209555201c103000004101010208580c20a4005503910b9225407920075a0369415440302d0030860b50fa001a003041c4141d200e030a0690b514000100da010501c3c100f580040703801400418400b540500001810034072060164001812080d41c0a80c1080142e0fa1010f04078221000e504071a0016080100b10f1401102070f07071089009407440b10400610381460b5a2002454400350601c110350404424604042c01010f00c0416408102600d803209650b2250000030341e0b9120007000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 808002419 1250 808001169 808001197
    0x801050907110604050d0201141311130608010e010f06030f031206030614040213050610200304030510180c12050f12090901140105040612090501020a080f0a11 70
    0x41d940c91107510b000b01104030b86015551242460706240303031038180d8915980055800c0444071050401400b92851040340b200201050894860350341d1480400c80302c80061303005152907428280b00d061131240500a1030700e1000081c010070043e411030309503191010b01020882ca414400c1001c5104101c083c150181c0c1483d1070400c81080d0b818034801409a508007900151034115030a07803441001d4401c50095008492140040600e0100302c1c040e10f80c21a209500310010b04581e0702001d001d1021151302c429401080307a643e07000780b0802032440d0403590046c2c5080c0e004194122100a151040e160070f0b901286800d5000805c1d81c5961844c41001d1080c607000481c100d00c102c041c33200c10f1101d844c5040359a41910b4030b4586034400107009403c010343d124426a6100300002d0070702418004101d00410684616003003502d452001d0302c417110301004850009460302611070000380b01b880141001c00142e1a0300320a4184001d0398421020010000308c002d030300e0000341c181c221541e4426145401d008c405 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 808003669 1250 808002419 808002421
    0x100e06060111030f0403061e0509030f0a02070314160b16080c010b030714120601031109040201090f06021c050a020a02040c1b12031113030f110622090c08010509 71
    0x8400d00d0f6124a04101802d07850105002c82040602c2d04000460030720010400001c0c043c1d404403e003201c000b9188002036500c01c000c0200b01081e040060003030000540140c817061039883e01c0b03100d081c2c4181c02e8008080d801070a042103c00b034892007160003a2180855550030218075414900512aa241018200850100f00c41051000940141c2d2603800c018081c1c0303040555400b1150155640a901c05c0d2162040c2c4159600b944000a4407a04030307a01309041c0351504400c0018400c11002c081e0060341045001000414403460859000c80100a00c0d40200840c3d611040d440900c5c901c1e0880003010014104a0007041c1640003501d5812681c048030006070f40c401c0440f080c3c6040c00f00b0503501c42c01c1d800003032060782480854400203640c0079241c1c03820b110603038007056411071600c510822500001803140050021810301040606014403921644007864441c000251080c3c000140441800c030f02826440c600a8121a0801c002c3c142c00c2010701c1440592a00a460801c050103054016810a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 808004919 1250 808003669 808003697
    0x90a0203270640031b1104090f0c0b090109091a0114090a12060c1403040b040f170a090b040b0423060c03030a0b010810030f05151008100e060601 64
    0x1412500c203054040400c801032102c0340e03454010400c41614140c0106407000b42403541742001140c0160200d501040c007501d503040003420040180f60001c000da40354050358013030200140d107213400b41000c2d050040509489100b404001445c000c41c43c2c0040c0645820011880312f0030002056612140c1000d0a03c056400d08001c030a010600a48030f44c0e5a02c10070380000010ba12000e40c40d103c06041c0200700c05c0c000c1e0020008260b0742c03071088040c81c40540750101b001401082c50740d00c80030f0300548640310004e111409902d8070190b0ba0385071150018507a000084850b0303132032f8018550100500c00b08080c9070806140080103100d900851040b003880c1a03c0a0805045c800c10740c20314884940d0060405031144d4030000b0710380e940c1d04200c0c1c40c00a000c0c0307420940401d40d0300610908d881030030402c446d240e9182c1569030b04040c640d10800d00b141e0394850701511507000744504030881d2040400a2094203000d02c2c16000e02d280c14454400c0c00d01030f034545000c0124511002c510154803c10030700700300a44a4400d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 808006169 1250 808004919 808004971
    0x82a090f1201060f0509101202011d03060c0c010c020f0d051e040b1309020414060901021608060709062606180403020303060a060f121802090a02032706 67
    0x800707599900d0754a010780200d640941482a9801d440f025166024143e44030b16020207020824041c407400c203072581018a0042d0720079200728140f42000310344440090641070100707191130030564202c07842c22008100c04004007000d10800880700b14500c001c00d00f00002c4a4401d44034140b420149041140014558030381900300e8800e40c4000b500d82400b41e40c0c4990b500b032044c0aa03003044000443c0c688644600195141650007501d0a407054a1085018292280100000c40d0f0007000c21505500804100180d145e182c080e0a03c018002034026100754078082d07000520110860b0020428015a10190f0100801d5440070400300588000703100241c0c0c65202c00500301c0720180110400080c030301002c00040680c044040d500864003910041c034081d403681c800344d03880c25004025000007a0b002c42086080041500304241c8210b801810440609241d000308141c1d0b4001c84443e2040d940000a001c1101d604882148804c140100700c2d502486498283c65100d1038054012406410001480c49050004d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 808007419 1250 808006169 808006189
    0x40b15060c0a050609151501052a0a120203041a03060a030b090f010507050703020a060b01051909030c060503090709020a0215040b0403020705060c280c06082a090f 72
    0xc0d01c07045076034814451030140d0390f03080116910102030090480b11035400000010440c0215003401e1700340138241d505401141c0a0b002448608004941c0d644007866140e8801800041440349801810140d121402e01580300b2041318403400441d072040004010038800000926084904426502e030b0301c1e201c030b1001503e0301611703400c0a4000401c80b02804002140080d040384003a0785034000303200075665110180c03418099980041e000d030304020391080004004d0703405150a010141415800c03d40b03180400082800c1034040314002c11407010061040c451050359600090510f4908103185103002d10820b40c0701c0e8058420300a00c0c80c1c010070380c0c0b0582d60080c800d40d4503014400359901c420b4940350402c609049015207042d80580148240071800b82003407001c840c21614080d004009108409000c1002c440c0c04200c4100900d01c80f40c9900000303400c072107040c0014825a5500d200c3c03400e11640042c000710603c5420a40030200c840b4015500c601001a500420f108032440760828502101003a11002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 808008669 1250 808007419 808007437
    0x20303070206040f1503020a0507110301090507080307060f02040b090d0f02060f251e0c0506030403090816080d0f050c060906160c0b1f0b040b0a17040b1506 69
    0x70100d008240d000d900c2052504544121401700b1810080072802d804902c60a100b0b40005041000700340c0c0803840c00807014049034070207000000d02d40e50765103ea6003440b01940090096800024045040c81400e01a100d00c0b030341e40c800111703e41403410060314071910036084024010705821043d001448140541d4070025900a0182e5507541500c1906c441e207070703010900840d280e03032440310050724105900c1d074500080e0380e126042860141c508607010302041c10503481120b807004014400f20f0782d80c6444010310300462203078654520395810180c50740d040014017183e0030284020301174100700c00f07a00082c07003000c400200e003840d04003114000411a0184600350541da410310130700080c0194240002019803040b0f040300611650210320050441e00c1d10440d1001820202c5440c01040e02181c18485e04400103450750100c03031405a480812214640150340500043d0780003140060701550496108001400101c0c24411680781c84d6a0705800e81e60090190f1030f980100052111603600c4410403101030340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 808009919 1250 808008669 808008679
    0x518070e1b0c0102031501120c121517010507090e13030e01120e070303120908030f13020909010c12060b030711101424010f18050a0605030405070e010b0f070203030702 74
    0x45001b4007244240400220742c54000b80d103001040310415214132602d04e01040b01c1c2e9502c1d102070014070804029003415030191900040d80000000c960703078141c603c0f036403008d500d50000c1403524250030003900000090b440124080098401c000351944200304010659926013010102c2d000e80100403180399000366040000b643c41c0103d40c1b8400180000c40c80e04692086c0e68a000311344800c030348082034660719800100040410301c08107134190000c1c0d02c0c841d40290251035285244d12281c0000f1000c00d0103841e5a0426551110f08034400d50f440b400b2040361142104081c442507162502c10074091100801200420070044d10b030740c0e0a00070910040c219a440d034001401030721128160440e50100607a00403c2030182c00c6403c510140d28042060f00f1705005840300070010341105000e84141d851034001b110040208000800c96645000b0b02d20301402e4542d032030580760701c0d0500c0d040c0d180041b9500068540b00780b800040110b14100e004039809000411191a241c20161002c40d1660240d440020340c04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 808011169 1250 808009919 808009921
    0x101b09080d050a1709150a021603031a060f070b0105090c0a030e0c04020307030c0e030c09010e040309150e270c1b031204020a090b030a2003010f0518070e1b0c010203 73
    0x8200041c0090340d800328030841b910a0744820500030200e114902c10070f01c0c0c080040102c0c4000c81e000b5403001c03200c40825201e51440314102c60002e4080d0388070380102c001240c0089041c20502c480014014054141901e49407034038201584412854003a400b5454101030b2a100d4078550104180544440404041c0c000c0d5268200114050007420600481400103054071000e0101e030710b03001800c20000c00c00503260712002c0e400c01f440c0c50f421690040c003e506005908400240501500400d0480182c1d43e90780e003212031140b5001c000c1003446617220803105184070712200544002c041131a035042449c04858541d580101c00400e108c1c64800f891410141c0004111071101015814030350f8803662081300d4901d8415100c1550f58101c612101c2c80d103405078406803603400040c01402040e00b81c0914841d0101c03801c034483d40002d0a45c1c00500c14549d03e1034548045c40b6001d894002400240c00f800c07400341040311b00741484102d1490b0000e1000d50164005050951a03603400c1c0111600744540c20025962 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 808012419 1250 808011169 808011181
    0x1509090307052b0c12030c200601060801060302031509071b050a0212070e0a09030e040c0e011211092b08041802030c0702120f101b09080d050a17 64
    0xc00480f422014200561401440102880794082c1c080480d40100b490f001c114042e03100710300410610300043d0610103003c14940303544003403040e0105200d030701200408156040c20002007050304180c0c005000d060040c403d00403407028020b040b180741b00090315243c0050359440070458480c12908003009011032000c0651003071040c0031a0160794140291010414020040741190741c0f061513128107001c9001a001203640798042e504103440c914080c3c43e000b0007412400d0009011110039900d220049042d901e0111074550700103800003c070b0300340da22080094110302c56400005100342120f00d840b8081000185800420030074800c01c100300395405900354803144c0d1804d41d125074045d004800c2100041580c42c2000c4a060080301c0c400e60800e403030141443c2c440d6081c040c0c4c80f040100300c004103020340107509400d41410082c070a42c4400043c804100c409180444d5654000780364100d0b82002180c1c0d2040c86044030024184a0b0704400d450301990b1042110812529860360720b88a8141c040303580c080c009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 808013669 1250 808012419 808012453
    0x90d05010e01060503030307021024090b0a09020f09190902040e18030a09030212100e071406040312050d02090d0f030809010603020a0603020f0c0303041a090105150909030705 77
    0x140d8a07400700080080ca500c40d410140d49001c100e9135400168449400c0e888064034075084070140101c0003258007500301e4004003504a41030f040e0083e0251716503401941d906407420b8020f41000305682e400441c0b40c00d1190609200300c2c031404d003409010300c42c5110900310300710301c40000c00001d003070410045403201e4840303148003400003054074052440702080043c0c00b43c0b500040103d4103c92610740741c15034403a1442d402d00848a208107425520344c0030b0f03484483e0654016005d40d0b05c00740c1c0c2c8a0301900c82141081c0b402d04031454551403407070040d90140024000148400c1540d9101e503403604003180c40c1c0201d0300b03010300a4420541d065402c0030302031044100700611094041c112902c281c0720507a403603480303680403801c990043c400071350321244600c420803003103000764000c041155603104400e203007004c64020b2510310380c02501c0454110102010a0840c5c9000e5202507400840300d074024800c505112030220420b405ca0f40031144664280030204244030010800c4480c030710b41c0305080c0c88010704540f020303032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 808014919 1250 808013669 808013681
    0x61303020d1404050a091424010c02010c06050a150b1c2703051e03090d050a03090b0405070825090209013506040e151b0f04180209030d0305040206090d0501 69
    0x32800c424050100340b00040e2501070055408c02c6242001c10304042d9001101c21103132404083e4188545010300c400800d085004651198041200c081002100301046007600d0030b0552284001080c10721214514000c900ca441180601c03420000c60301010b90013000100e9070700d156441103055200d0b1395030010580c000010b0030203541c4a50428038561140d03078410217688000c17a8185000e07040800410f0110f40640060010745101c0d2800003070b5045e290b0b6400000640c1036500303582a0340000700030440c0d104100000c0d8041104c80300d000c8281c000311804000c0d113508900074001c643e500442e1800c510f9218000e032005800035010500424980211508900c000c50209a42d83c002e0090000b826401e0501801100f003508100425840800408040c61312001400440ca00b070005803505001000c94009018a00d1a40075942d560724601070101648210803c2640da180f401842400c3c2a81d40100354030100380481d09001c40e26540764400034005100c1c1ba81d089600032400100c0405110b4158084 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 808016169 1250 808014919 808014941
    0xa0801050901050a05010203090103050406110c061b0405090106080405010f1409010c111915050c0c0c0a0b0301030b041406010f03170708040b1309051305061303020d1404050a09 78
    0x20400c2c0d07210b00500c001c0142c540038160140c0d10400c070441680d48258000c6074480d00890000500d4100588004e1455001e42c0700030b02568032000030710032400181050280607126903000c2e6403800349000041000c901c014400d54080c0700c0c80300e000505020003900101c1464040328001c00208281d003c40f01040b039030580e600c3d400d644ca0012058400c41c064000001064011001090700404a404d03500070a45845022600305c084280a0200f410300c50248500414984d40c0907501c0d50805c0510034500b407440800c0f5403040d0500903003080f40503202011241900c0c1c004004050700d585905007525240e24030062010307203204003400041c0c1c121031940180d00703507482a01a40b005080c1c450b100991809450006085010200f0040041204180c020300010620142c0d40034126a0340707100e103040307071400c507001030141c50003113540d604200c42030103442d5004c140084041a41c16060318000d50311084c90b840070091100d189014071940d42104191001000010480c1c0c440c41d89032a10200504004811 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 808017419 1250 808016169 808016179
    0x3030415080610120b011101060f05120a03080a050408070b0906010512070b1801020a060903030f0509011404060506010207031b06020d09030f020114070816140c1f050f0a080105 78
    0x100b0018a022540e140c80701d0035990b11000d240010346a003400500e83c0c400c40a0600201d603100003240d07030302800b0700002400c965081d880003d2030401400201320340041010029044100d180c0c0020342c10450342d50300402404000115641c880c0350400e141e1041140280080801e8803c100146d480043ea0034145e4406581c00c211142005540564420050140300d007184401d00c0460200005050020b4140c10305204465001c0d510751510011182007c10603000281c4603508d02c42010000e008a42d0007498541c0200201c3c5048500d80340c0320b0324043c00062020741c80d44040b070f0890b0f00c00c1203004007540c0c1200b046510b1b41528500e0643c5041c10b4816500035010b011103031641c1500601e900811660401d9a06000f00307459801100c1d200e8640104c0a91060140300c40004075050b41e000d040d480d010400d0308040c1048606004240141078540c3c2030ba1a03000e000c01c581c20b42c031242d81b04c0b00d40080300e6044040b500ca18040039030f45805500302007024120007254424640340d100d03030414101c40058030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 808018669 1250 808017419 808017421
    0x61725030f0b150a0515070203071e0302100e0d0f06021b250303170a020d0f0c03060806060d020402030901060b0307120605060f0f0a090f180506040b210c0303041508 73
    0x404e0080a0080d0f120351759209a101c000600c50720405801030030603030f2008040e0746056496800061000c000b641d00461a581105402d008504060a10600c042c05509007400c0305a1210001a2045139500f0014114000e10428a00704a001e40644401d60580a6420030100c5180d0b9900c0e0360310031102c94603e440d00200d403044050115202100c040c0d98055664581083d059082c490303540001508006207070340c0c20440120209240c1c0324501344900003610100d10309201a81c000c05440e1035800051042e0010b0050080319a01c54004000055040c0c03805038583d540c80c5101c0d03006048541c440009044000104480c80d507009202c01c0058600106c1009017a8584062211a0160030000707056114208203080f0350b5013820000d850184107520b02007081588960140340e0500c0b40360700154541e1028402c91059485a004103948240199001c0181c5031028000070f5882051200c20190504003410242d80f4240038401c0408032040507044903030311946e848040d6080d0421206030300010311064 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 808019919 1250 808018669 808018711
    0x201080c0708030619030b0705070212010507021e010b0616021804051209030a02030f010e0d08040f02091e09100f02090901030221060c0301060201061725030f0b 71
    0x80640d40710a401416040c21075950b076003400344002c01040c3e80002c06003c4880040003442d64041c0b14801d0030709a6800381c035003005105010300040010041c0f0f840713904100c100f11a66500103040c440a00003054000800e143c0c0c4c0f40c906004124100943d03400810004109694074202d1039505082882070b02c450304129029104640591000c3d500149243c011a0940800808140140c04118401000d59030f48820941c0000c0c42c1444000c40440265180d0354140c2c10b03401c091090350f908080340d040c01040380c5881d42d6241d00289808000900c030b54090030100740c2003000c03002207418203540850846030605102e99001e80d6100c80000c8c0800c1780741030482100380c0400038001d0318009007010340b858680d07900b90360800511300003035540d541000007605d10142501c6403c020842c011446071401b00e5507541084402820340b500754008044840d00007001b200c4e00c003000107052040041440e4254019600c103d454040040da540c0302800b09182c000040c0e06002c0301d031740b9940c002c105180d07000301e01707210391 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 808021169 1250 808019919 808019941
    0x61312031b0b0f040602040b12060102010b04060303050909220303020c01060f051f110d0905030c0307050108010e1306060303030c02010f0509190206090a0f06080906040c0603150f060507020108 85
    0x48400030250244070010884003c200749200390014824800541031a4661240e18042e801c4401c400140c944d0b4003040c009156020b00c200000e80360182c800784070342e074103544000d0886d11401071024000c840100c002a02160218502140314103013401a8442225a00f0020003940104c02400703442d520b030001c000b8103a0200030750300c801c580000d006c1201126078100300740580e1114461007020302c101a4103240c4116000d000118900742d40d61035045005081506152825040303140d560300030760102c0e074244a6a81c100601074111b6000c280b80718865565054050040503841400500300c4e82804404002c15070580c0185034a290740b9402080818905040f14003541c074240c40550494205422403807054913013580c510007803800030b00741c1860401d501000c540c2c140302c25032282e41180c820301018050146d00c07840c0c0c0c03600040f50030001c1076242800d8442c040092400c0c03040a041c07507600c10032118002e8003204140c1c002c0042c00303004030140d6600c08018140703a000700022030009a82900041200a034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 808022419 1250 808021169 808021217
    0x606090612290f071205101203090f1e050402070503190201180b070e0d031409010522061106100e1e0405030a020c041404020d140f0706031a031b06131203 68
    0x1e1400100302d8501e810400c1201418141c825000c000f90803101207144140101c2c40802003850448003003d644102330103000800d0190480c0e44505d004020550204400000780c03820044c524850110382009090309038010103541c62400d914003040040001401900c1089071f1160403203864284916002c1c00401c2008440d007080200400c40003607004410032010307c0a4072401c001810960710b0404049000400c0e10101c06480c0003d03440581c1c103011080c0d00c42440709031000e0340301c0140720504001c3c112000d005218080e003001c41c400100010b03d468090300b18040b070b1840b842100c03009801c00f820134649951104c4c1480015201d0304420070102d0509120741c1d4509403140c00c1218807901c2d41c0e0300300302031b080c0c64080c1901d00b01404c03460821050f909001c00f04404031640010805145401e5011f001c2d01c0c160b200322a6080c0d84012418801d03180441c040c005404804403020004a8100003c0e0082c0036982c0400010f1118031404503003510a40b032440441e41c000c2d200c459a0340290410884280c207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 808023669 1250 808022419 808022431
    0x3140402030a35040501030c0203070b0412120c03090b0721050c091002071a03010e15121e070e1608040f060c020a0606090612290f071205 61
    0x1110060782008114085452000703100c0ca00031595941a505103c0c00054820211040510000203802c002a60b0181b065030390f842828000b0350f003000340743c0d1250041c1c0f9800070f001802008003000f825801600c540e4088910708000305081061207801d1034000d00070003070301c10100d9404000d1408140264040c01c600d014100c42c48c2c1c3e00044106540c9400c90150501400211220b101400629890303918a100203980d0b4015038003c08401e440d2010006818680c0c0c1c0501417005010001401081c10311b1000d03541c400e82200c0d9805000401c000455108110080320ba891070141402d05500803191032070041f45641ca25003101c082948070100c0d0031509405495201960140000801310030b4003814041e98058082e18280c0b00d41e49158a540083c0c590010013800141c0182211104005903449800c016240700744042003841c0c10209050610000f152000d043d08903c02d4006c82200341c0707a04e0042210701104280030141c20000e04103001c1c0b401c02e884460205010100c0c006104241d032142c140310308 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 808024919 1250 808023669 808023673
    0xa17040506040321020705031e15090d0210021e090f0a12051e0d21060b09012c040902191511011b0c050319050a020f06010803070813180c0314040203 66
    0x5070703500300c09410828240d440440e4020118803244ac110408100c030702c0380f0601c1002d01030b5010400002828200c0410140c80014410302c00480b002c4c092802e205508003404000698482004000070b07c005200f50f03040d5170012480034081200d0300410140840284034400700c4441410903003440d54404154034081d0703910f43c0107040f00c403001c3d0302c95080b40754080c5140045c0c5000c418281d100c542502c030b10b070b00504844407000540203000d5074009459841e0a601e12964a1140c0500c0c45104803000190725241c440c07078465603104155a1640344645012003682603001c4243c3d6655100c460b44140c002c21807010510070020b003000450180140c0302d1009102d9070714120340900e41c00907910110b40c040300355020311044c4080b1001e14502910380442c141c813a03c0700b40c0c42d05800e1000a18003241c200e40c0c043c841e0007850040001312000015034084960010070b03d9124034101400d001d006c016584009290311502c80d840c610842d00e0b0b4042003058916940c00d000840d0301855480c06424147c0e0025055 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 808026169 1250 808024919 808024933
    0x2c040e0a17070f051515030607080f0901150f030201080601080405030a031122290d020a170c030109050c0a0f0f030e2b110a1704050604032102070503 66
    0xe400800c01000310310703c2801d10a03800010341e11080e1600c220314491054810010b010b1008035000006500c115210407401071a041c64101d00050240ba000b51900d603010340010b000c0f489040e000e400c10001044034284a21109589000300c998a4049100903404038643d070340070903038030351007803240e41e100d42e0300640110b15240c14400102e00420684d100d02c40408002e10508910b859801300c0d042804074680e51450a09040c0322000e6500030b000e2041064082441400c0c0c820078803140240c4110740640540140c8031072601741c0c251074852845d0b682e007115440070003c001e003210b81440914140c071070681082140340da40707814001451140c00c100b04085401c1100c45a0207a00c559044001c0d100549004111a040ca4200604c2d0043c1607000500c4d030b40c544441340c2055411041c400f01c080150340b800c049180400312102e510303005502e04c054501070518078422900d11240e800ca6005003005806160b9903035a85c10044503400c3c0c404400498030464818a0801a20024418066450041c0513100f6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 808027419 1250 808026169 808026203
    0x30103120507020607140109020f01020c0a140609090f070206070905010c3003020a020c0a03111c0b0f01090b041a0f040603020603040506091009050a02102c040e0a 72
    0x2a0700882c0302280c0c0081d080100c140014504202d5540b0450a10000f00300b1001920400c0900105034402c241150302c8a5050701c00b59484100c00011101101e0347c134403801c90f841c0040340c081d108d81610650070140d000c1c2480a003140042c140c510444050742941c0e00d645441400b210b0b040442d2041900003401098114082034041c1c0150703903c00c0300d4a000c00d1100c00480d84038004c4424801c0c40b00046507000c1250018650140070400074107104031902c2c02c1041c1199140c50071001c01036000c50180c40ba02c4030f501d0a084c0b4841c0400951b03604401e000c5c002d45010741c03c1c1901410f003401000d592174200460010203040134080c00c03041d00c0e030040c001500d0728411400d10420720000722140e54469140c050000250310307034900960007207005d01c001c1d09031854405082c51030841c07003011000704145030904000114001040c9282c0c0d0f1a1704488030444161401011078040c800e521001000c8070958052881b120080c03a61200b1096090360240072011101405a0b1038440e50b2001404a800c01c20945907 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 808028669 1250 808027419 808027427
    0x515010f180b03010f0204050307090509030a030203090f06091f0e07092313022e050a1710150203120112020103151205071a0a11070506070303090b0c03010312 70
    0x480d40c0d40412000850b00701d05400203007918071040c07044081e2580001e06000c2c3e41003d00460002d451102c4051105c0e0400005142e520300c61030f01868105640170011444154081c0903c8501e019030f50304035072250800440507074461200c001440c905951000d00d00f101790409004014502c00c2070303000380c50007514017580c020151140d00e0764200042d00c00780604005840360700b0000c1c092134685091400030001031050280e8000d500c0e09504401400101140303d00c1103244c9141c00710b901c3c614081b03071500300b48002581c1204061810b0400c3c00c901504001c1d02c42c866980c803104580710f110b03524224010f401001e0340c9a11410704000c0342e0b4108840107010210011190941403481071400040440e440d00f12618041019000804011806201141400320801108024001640226400d070078120091140381c852261460113001c44600c4008050a05000c528002d2502405a550715480e034030f0300500034a0b4000302150440b8440003c1850402100c0543c1d060306c0e40540e20f5503002400f81c80c20380e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 808029919 1250 808028669 808028699
    0x15060f0d03180314060105010905060706091506060c02031c0e220c1107061b0f020d0222050a0b09040f1502160b060d021309021c0b040515010f 63
    0x140034020b00c1000300404965001c90000258001d9142400c2501d1841c5040d0910f801a0300150401c40301d444203001a949280480c2d170703101d502100001e589185407401e2068942c0489610100d00d00c0d0200c0000d4040c1c200107102c0c50396100301c0a5032100441c80340e140310b4040926842e02c0002e512100700b00c2050030802d9200c03010340040c064640d0401226080c1100f69622103a0301800103465850395440c4d0314007017210b1030141c1003504000c1403050300802c0d4611302901849015149951401c0c0f0743c801d40d102c00744280142034024080f2400d07045807030000016400d01c2c40d031852540d480c080000c1ca40500e5882001c8a030721000b0304070000354599440e44090040c00ba1416200380c4074604110500081520007020000c007807421008a1806d07904101c0012840201281d00070204203e000340165941c0314081101c50300d9200000d84100b10380081544550403200503441d1f005046260014402070560039441540b00303008031054580d000e44c26100e8588288101003e0701e2a014050140030aa80004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 808031169 1250 808029919 808029923
    0xf010b0409110c01060609080f01090b06040507050c07030b01061403043f08071e0906120e190209100605030a20130f0b0c1e01061a04050315060f0d 65
    0x1c1d90034210300001560840340355900038804520109030410280c0410f119580d88440d13909e000704840300d2240c0351200100c10040490f4400c5681ea400500280d000310180ca5414035490b044070f4000d43c880c5441c040701c0c6003e000b00c40205003402c56018651070844100c81c469607208483c1d140e540e0407810442904451942c2440d41a00c402032502c64600705040203100425041d80ca0b000d1509100c038024203020200900701224100c110140041c003604070340344500b100c09500d403d161191000101d0401405188209507150040e85540c4001c0c0c80503000803011103000b1680b00469071200a07080016a40c80e1144101046090002403500715103548141c400410303d4006107540c81c40e90143e03501c10760150031009019031a80360280483ca0710141743c207019100041d101482c1c84119040c03140d6582d44c00c0304031030080d60100c22080e0b0200003074001000600c00001300f0082081c0e1312009810740d801c6401124001d10620300008101c0d4058280c41c0d0003540041d00910806030403c05006001c0465501 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 808032419 1250 808031169 808031201
    0x140f12100b07050304031a15210d02010b100305010e2d0a050702010b0102120d02030c2a0606010c02010e040e1c0905010306051807050c0c03030f0904050f010b0409 72
    0x34000d5198004020562082c0302130360f0342d03038114a003012030306546a103001c01c419100703020000c1014811500c840c00707400480704400340500101104c2250220106410228012036001c9000725070150400b21402404803054109064414821011a0424800d58072a481d0314404905207a10345820042500c0e0b0f030340400207010b51000d000c90320620041d0386080f182a80c074000c005560f85d0a03c12036900100034806007103807402c0d21000c0b50040c020300d000d0820300c0350b0010100d000304441008070391103140a200185850300c55040c0f040010030f040150103882d4003d09000601540c458156200f203c3d605842d12002d2404500910005080e8440000c00714444c4140e134040c100d550a2250420035250398444006a04110005042d01c3c0c1d268001802903200c84401c001e9200841c1e1030640c403800c00d15100303440380018643c0301c3c6407841c02d500d010b805010001c3c2590300030a2035002803420038001d44050003c0c0d1244034085003a80f0f1b0034825096054000d00c4280011405034010150000c0d2440b1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 808033669 1250 808032419 808032451
    0x60f0c0503040303080601170705030117160311010f0f090b210a0b040606020f060a270813060c11060a0c0c080307020a0b0a05090d14030d0507140f12 66
    0x184952440d4030540050340070505d00010000150f80c010410a00c01e00b820810495600f001030700503250f400103000b600303070314001c8000549802400700700191480c29450203200186079a410030480c1d0f80084052180040c4c200305081203003d0040344107100f00155a640c0c20400742c1f61803a844a69007108114403190048c0342c5e8103a01c2401c2400300d0a00038441c8060004001da203007000c0008590007a031080080d904090b10400300b1001c0840c10381d80c00304941c3c2000c15240410541b2449213412000a00c08080c04031405205001c0303000003900000d840102041059a00ca03001610b500c989000f008008419480519080303040900190200c400c450070401048541a62214044110741c1c0103515140d00102e046000d500e07018000e540209841c084441c40c106982c400141188941245140a410094284000c0000160301e15a4209482c010b4035205c85031812442701500d8190b545a00060400c00171486d080d0342c660031180d900300448a070b1307860308440b800440490314009220324281c171a402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 808034919 1250 808033669 808033673
    0x3070b01030305091809060132041a030307140709050c0304141009051506060301050a03060902150f13050303090109140d06021b190c0e0406290a051801060f0c 70
    0x91700703882c0101e44000c0580507940c100719040b0103131401ea850b003c2c0c803230740c4070004080400f90b80c580035028800d09840101d0341c003540400c080307003010100c00d107950584000202401481011010b4421202e06902030355141982c540785081500c02c2910742c9502e00d503081010800055a0540a8100503010b0041d80d068020800d139080854008100680b141d8204c03990300d25041102d440751692207001180d20300d040d5411b0101054140d240c90000070601962960444150360301c0ca211100d1204405012907a0fa040c40a02400300d60416103d965000c0b462901c04516440c022064a00401c0183c0d0f4060400d49084500000c640074000000e810403150100c10340070070100d00042c402c5021140c240070b6144205a03140c1c0c581a003e4141a20a0403004000380005080c00100411200045002c5403262654288480200041e01242c01a03465012000c00c030b0000c602420b0345481d008071a03000d49242e40b0414042945440507a01e42c10030030348401484114003450308840c40341c00500d0569526849a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 808036169 1250 808034919 808034959
    0x3021006081006150c031107031b0306050702060c0d09110306130b01080c010f0503091f1a0607050a020d030212030a0203060901091a130e01050412020105060303070b0103030509 78
    0x5900701c120242c020a81100744040d450042c00014501c0c950110903100d4003040c018640d0380340003070050820410080001500904018840280d070700300c0350000f00003e5280380503c03060114441210380a05010000729118000b1500a1160018042032450841c00710104d038018120707e04100c40e1400045030b10b0500740c07810810240f06507115041500c801000382030000340088140e100426070b50000c3c20303002e00359a000035000307100d05486c2402c9849480b002c0401e03051408545c3d889003140d10014a801c0220840c1d0040790b512084800d0802030780a4240500c4428425040040c1080d40003100d56001070820412070516180644156070024200c9030256909030310640d0540215a0007005208a0b454002206401441e6211042000041d09100c00c04202c20043d00326100d0703510109124652816504075686c2d00c1c1740c1c0402004107180518082e08020107000710b030b4005600e4003000030341c0d6050010413240c0e40c1e5008035106005d40c1c80c2d0f0740c00b1500ea030b0165296542100410b44010009261 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 808037419 1250 808036169 808036181
    0x41407080601030f1a0c040312030b12151e0f0702150420010e1e0109050406080a1505060a090c0201020706020304030c0b0705041d0c161212060311010c030210 70
    0x21820b0100c2599a00d42000d007064104170100d2092a1140c0b814041180409000c03502100d83c000f005a41015207042e068000b0207038407003080d0f0070140c840d503121816031010815010084049110441d075031038001c09540c07042001e00503101d0f0382c922480460040041d88403c0f681c0f10721181704540d00712103007041c2d60150120554040b00c01d07407100c40c507182d0260300e94a41c5034282d940a107840c0307903030000100024507004000d0544003600c80700c007075490003035903c1215250068440580244a81c0d40d0358404aa071f90441034205a070040c0c0c00300541c0410202c10301605004203801400c001c0302506103004100203084a4503c1c00540d98204030400000301c01d400a07501c00c0b402501c6041030180e150900703040350365004003e8000c008041205125032a642d14080400d90801028102d042d9950381c0c404e01e06108007400002406140c241e42010814000c607000d020300000c0da5411821040650005c00b6504a404020002c0440041c0c00400b54450782c4903001c224042c0c4100d5242e020401040c1c5e040b152 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 808038669 1250 808037419 808037423
    0x30b040204080d051b06070f0302030a27030914060703080907120804090506010804150902060c070f051504080601060318060501030303050711032701090911030103110306040b04140708060103 84
    0x343c046a1583c905e0525294182c403800e4040140806240c45d040041500140220b01001c1c10303400b0004c0f840500c4542d110683e40c11403c80300f448280c100d0701c0d10803664001007a080b000035685000102d131000c419000038821303040107041242406071726030341a40d01400041c9008224896904009a0140d4280c200882c1c43e000320400f0341d41c0c50800c2c0c02003041e40d030000d05c1da6040c003010500340030014560400301e581e40702d4080303000965483c56100142c0180708081d10354010303104100c004500900c600c0003e100300e62089640c00500071000764040c01c540600d100d085269000f41c0010030003640645c000c00841381d2040017a19203001c1c203650f20303400c9600c03c0c0c1094000982c1da004001c0740c01d800081c05040000f69000560810b90307407900c00c810054842c400300d550003110083c9505142d000b00003100c0500002c04040c880d00861803048080ca8000341b02c01e446146241c0c43c10925801c003c188203000b560000c1146032141d90700d84502000107131600003401d051044020000e54540c0030300c0903030f020f98 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 808039919 1250 808038669 808038677
    0x1e0106080c10141c0b04021323090901061401090608040b060f120f0d03180f110603041a0a0e1e07050d0c030b150a140301020d0c050a03051605070201030b040204080d 73
    0x542101034904176080301940c03e001e036104020403940350f0502070580341211620b560416000d200740c3c0c40a907807007031900b104982081c00d540c1030201200f01900000169054903006920740b4080f0001190110918400d58022580142c08100401c401c510030541c4194081e02c42c2d110310b90b020002c522a0601c945074100316401ca00b098030041d100074040301e4040d001600e07040c042e46200e00b100c550040d100e04001810910600c0d104c3c0c0410211418004060600602440d1280303401d0501e250502680007200040350001000180c2525591044044001071036005103440300e840302d40344d105440c420080309400d01c1500400103440e1b651600d1280320390f1203080200c4060b07103507140455a1060281103000c0d20721035460402c004ae1628001d03101141c0c030042c016003c1c0c40c0c010020900921a2080701e081080c10643c403034250720b8218004100300030640d50100a941d4900d059920380e403500303191950010750100a4640590320980007a08910001400180742c142c2c1d8030140e51030000b0020160b400f103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 808041169 1250 808039919 808039957
    0x521090a1a0105031e070504050c040e0a020a0f0e0a080601090f050c0a0c03080a090507170f0a0b1506040b030a09120c030801050112020d09051e0106080c1014 70
    0x401c01a11030100840c020384509007035414800040c0c0c8130003c022580003481005400c070170000108220420007000c011300b08200e02d003000b4582007682e80c8203001c0c0c40b6815555101150300012284202c402c4880341d0f640d03c594512107444200c40ca04d0548101a9101d500d0543c00b056142062000314000d01d0040c40025840710f41d5040d610580c0e0004203036000c451014026040419004106020709581c03600e000c0d0039641d13680d00c45000415450001030f06501c0340420109035165070302030b8032121800c804101e50030000900d00c00380d5100d545074001440400c402c03000c184c0d0806607083d4100100c60050030765003032036141e5200c0081d40d081101c3c0e4420b415103032070134041480700da0700d800c1011030905d00d08010500c500e80c4015041550611605041010000d0f6015002015905480c000c01468006110030501800c00d81e546030900002002120f20315040350001440c140f0a80c07049540b02c00140031141c0c0c02404109454008400e0b100c2441303808410707001d0170b91182c2d00030005640808011180 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 808042419 1250 808041169 808041173
    0x3090f120a02011d030403060c111203070305130f0210020109140c0114040e13060902100309030818060a02070302070510050705210d0b04020d060b03010302040b010c0f030521090a 79
    0xa444816240308880580c412211320380540200480301901c0c2c121b880420b502514520440702e095203a00521924050f0b55480820100341d5001140900b89617035051216480d85005001d680d074415100524034061004100c0050904901c11414201980000203100e041c0ea280c950f542c226002901c1c0340c1d40c000003164481c03903800441112001804003e11802d040c2007401c006030300107028103014148106450a4020001e407500400f01056010300902d254208030003015010300903200c0203d02041400d000284030a841d82540c41c0c0380602d50004081c2616041c0206c802580089001c1c1c1c11030280a00c04645170703c40500c103981d5440642d5925075251030318200709040045e051308120481c0041403d0155001c6a4025170f070745101d1080c0300043c00441040000d0080c0318000195403820b0a1420018034075400401131412240250703001c3c04004904e5004440c802040c07400140600c85100b60003010034824400781201c1c11642120a45a41b504915000c0c408805ca0740982107a10009481d01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 808043669 1250 808042419 808042421
    0xf0f08070b1c092a05030d0f08040605060d0f0b06010f030218061309180b09060709060807200703150204030f03180503100207140d050d0f06050603090a142103090f120a0201 76
    0x80392030580d24048d200712000340e07001022401c02600103030116854401190655503100c50a403c2154001050300464230300b441e003c1c2903108221500b501003505207840d107a03110300034001c8901c065209014039000c00c01c0c0008002261b0008500d10106403088100400c503203600d8030608060043c40c3c0709046121803140b420301410400207002807003035008001071040c0c40350452a450103540541c20003420075902c0c1d540450301c07140c20343d001e04006200c050a409240314040740307210a0324000c0e040d4044120f510700d041030603446107100051190403000e600342d0210307205000b15400210004440071001d6500c4000038500000c80c20705035103a035030000b0882e08000c40310540c03034818200d01c4c0140048000c0000003502d83d00901d504103060035281c00e407502034000503030f2100c405030000900c125240d0a0010810ba0348950481c03007280c1902c0d81f00c501e2614540e0008a0940f80844400404c500c1c501d40907950615810290541426224007a40410f5540302400f80c1c890307404000303540300d4a81060201c028 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 808044919 1250 808043669 808043683
    0x1b040906031b0605121b16061a030703110105030c160305181012020d0b09090c0109080601140d170d1a060c030906070c0f0f08070b1c092a0503 63
    0xf0007800410029003254109002c00c080d4030103407202c040c1d040d4180d150030048080c0714001e0400c10380400b034203003442003000c00d80c070080340d090342030004000c0d02800c0c0c42410365408490001074aa4203040f8a0300c815503100304010747e0311864201200381880102203884219006a0004501013072000c101240289000c03e00e52540701c0e81240d01ca9180341080d80041c1c4854482803030b040600b034000400c07803120748081e049114041c0018044c0c6a0354a4143c2c800c0d07856207081d031801c0f80002c10703e290004d038071100042c820303050741d00070720815000905890800400c0340c22800304a400c0b030102110421854810030140941101e00c1d040420034000e0031018851813405881c44620503801070001503d080000019602c240d003081c0c418039130701d9049041c02c40240f0a2540040d08441c510b1402091110f14100031400302c44012085079001902d81114030324a000300e0001c40707001400410300001810458004001507800398000e05003e1404d130307ca44072510352941035501c02305050340c420482420204401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 808046169 1250 808044919 808044929
    0xa021513300f1e090f0b0d0c02030c3003010b0a0e01051312050a0209040f0605090a03120213081207020906030a0c03170408100b03060f06091b040906031b 68
    0x9003480d00710041c005002007540c01c081510a45124086098a50007401200050605c41c400c070040e0559400c1c9a032400c0d404401100012070038041803501c3c8900000a40d4204008900a403c102200c0d0001c1c0140220703289031000030070031421424004100b64001507001c0c3c10300300d0307005503200c1c600320001d007090301c90205560412004220601c421118070082c00e081d0384812242c594800440c1c140140b904498042c040d44c8501c81b00d050200300441c003c403030205d50348030310018881039882c00e03803964881c2c00128015010aa5160a001c2000c0165004080050f510188861102c3e140d8a803a850310004100340402110000384400542c60041c0403140d110310304400410b400a55641c5114000d40c7d544401814902031007540b5095680002c10b64014120700da013250176102c1d18441c5032010f05042101f00d03000303000e40c2006ca0b51040749595518840c260140c15501d05803a52054002080a5440140b0a1410621000c100e8550341d00031040194064951449405002c4c01510b003003a09592003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 808047419 1250 808046169 808046177
    0xc1e030a0912021c050a050717090901080604020607060b01030f05090c04110f0409200d02120f060916090803121006020303010f061b08220603020a02151330 69
    0x128007142d441d0601010741003084d4079115880350a514020f45a50040d803c004003e0485007070420030003070400c400b07004269000c4485848503680e50000350b803201c01c141c030061b41054003004500d0104400343c00103c2c09030810316002035661100f48008040f58016220341c42d058001284200e26840c0900880b182550388001d05450b182407426015510f22131446034500d0076464070020148001e221810b02121043c07a00101d0fa5002c00840c110b00039401899409440f40f41100400d12480c00108500c0c490b440180c4040e5554035104181010801030140480c00c0007506000032603441c3d000c1c000340c01000c0312010480180c5c107020a18650b03407265a0098411517005000400110195203480c2c000c45825003445d05c40b470599a0081c1c4039891015030040d007452400284120100d403083c204981003408081020b0174982c4401048060744180002d4400503800304c814001d002c003100031095041180e04c1c2c0c00411443c107658031308824005600c3c40c0040c00c94410782107030781d4040504000c3c07518006898 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 808048669 1250 808047419 808047433
    0x5090d03210605010c0f0f140303010f090204122301020c0c0a06141914070813061407060218030607021c08040803010e06030a0c0b071e0b0c1e030a091202 68
    0x1c0005c0c284100502c0c060018000740d100304081c8504000083c1600e5048007c02c3e4240c1d46d454001d503520345c400c0c8138060600740b50b43c0001900c00f82c58070070341d0281c0ba070005802050225684502d440da08420522031007019541501101c02c001c02d10040c841e4600c02800381205081e00d2040008410349030380040203102c0c0c0c140200e07200001c0c8104440c4816030000ce10302400700c004204030f0707007803014414103110b100000580c1010300003c4006001303030000d5024240801a210241201d03401052203a8689a54051003818009041078020b000c00038821001c01c40001446070005e464824280c82d8100035070009031460741c4044060260342c00c1030440341444a80790415555004032484140b243d5a41c4a01d0310000c40c000765824400e0161540c3c2003401540c800c0d071207110b42704250313200520441d42504104280c44508007202c4801d034069421003000031003551401d96546090f4131000b40320003503600f06e241c6500100c880d44003035030007800c4100000a40801e540381075140a4003070603043c020355003c44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 808049919 1250 808048669 808048679
    0x31023090105060306032d3a09060e130c08010305160317071b06030c110a0f080a0c14061803070b06100e221d0601060c0305090d032106 60
    0x1268500103d1001405103c0d6034203100c498030781c1201040c0c0c4031084c0144040c007030900000000c1c0c000d50b01500843c00040c2c0461b239044100420881ca81d241c04560b003004100011402120700da8014603001c0d101010170090310607510101c495020089001c02e00010051003031140801203010981c00700078010801030704546074108410b00820008442d94000121081081092546442d00d841d002e540c03036a4154030303410050302030b02812044000003201b0f03160100382c6081c005890b0b01e0040d04441c2d105c45515142e150074030158412002c14081c40042c01c1e4107400614030000f20a00000504041d0802c0e0800301c0750284500f8002c01c600c00541e0003400002c010908072623409410000031501c00c1c10381c2295103c00e4503041c460110b600c0e4000040341604a803440362031242d01d0280c5201804002d00600c96101d0f220a1001424202d40c0c1d60090b0b0052002034003820045101a001c3d062442c1001000d01c0015100400180105d0000d4540c011079419030080b283c201d010709010fa0028040c00c0c2c101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 808051169 1250 808049919 808049923
    0x102070e0a051f030507032d03030b01020d0e060409020a14030117060f01050f09071209080409060f0e070f021f0903090515070209041e0b040515010f090203102309010506030603 78
    0x540000303802010401c0d1007008050380d00034108c60301c031100b007100d0917000a2401c2c042c0051000108560140c0109109001d20754860300c0f041c1c050703a00080525003010304014240e0000c2d0040000c0fa0140280c2d800403404440801e4041d42c0213002000350303030200340c0004030007500b0028060540c585000080005010030382d1052080c0c8000602a100c8264964800074115045030b04850040c8640c5d103040450700600c0700030002801500d0903100d05101140e591254444407800510980350700010000201d03091a2050700306100c0840300e441104c00712200209103803004407100103542441940c810b01c1d0350415421018440c000c22044a0130700000300385038005803e078400d04800a100b400c04200040c02c00c130040303a02829030301c90240c201d80350300c0b07180c0761107000c040f815902520140301302ca00c107068111500c4159410703030b100b43e10040141c500d0401484080d41002c4c0c0304280061040c040413907892987e901988c0e80700341285154030310303c044800744103041c641a00810301441c000c00400a1303a41f00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 808052419 1250 808051169 808051183
    0x60b0d0e100c0c0605060a0302090f04061103010609180b060f0a09121a0a180f030c14061014030d0819020c0c2107030209060102070e0a051f0305 64
    0x11010010900106840d0000d041100c0c034500c40c040d0500d400c914070052503001a591020b244900c80030060380d1100820000090243d110082d440701c0c140c00001c080ca4500321080c0d4100344199008507800c0031055400400c1e40098110b41c00041a544040003941300c86000458844070000c010400400c0c0400820603511900481b001d03108000600a0a100d100e2300c2c1c00c1c00100800100300000c00c000d4070300030609030080c1d4101103c0503980c0b004624101c40320f01c0f42d01105c07503242c8540810007070b0590703e615a5036a810415801d00681c02443d2002c65506a0349030043c600b62406440c65203081400600500615000001000340807000c140706524005204150688603080c0089242d544114000ca43e809880004604034000329440e03404c0300d03001071070f141c55940440f81800d100780440d0684051520b004c0d021115a07002500801c05070038000307800341e0060310601c10780d1803080d01c03a106000c5c07184c401e82e800040b0710303506c004000020030b4401804591a0450a40040885c80d5440b8241e807412 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 808053669 1250 808052419 808052437
    0x13060c05070620010e1014010e042d11041d03030f10050a030305030403030c05030405030711130212271b04090209040302010212010803041a030c07021206040312060b 73
    0x29640d10400c4204414208a0442011110084c0a48812440e11706d0302d0310104500044030b6030a00c00300c9400780d100d204010341030303401d4480d680245a503a0303205c0c080c034146001010444815406441185028000080d82800d406080881e180648103002c0c81300312045880340010403000655103e0311140d022045a410100903000c005c0301d6159261701c0710307000c076040d0310890f400210b03410008209a0003e01542c483d60094808121601002d40c1c00e603100d00c000c4500400507001005040d0020b0031054003803000c41070103003469040d020030310f07140740403a4450503104074518100010055918240708030404504641c150020b066115000c4c90f5030b442e0760340044c012000c8110b070701c0b2f0314181c0c44560118004980003045141c43d0304090801038000e601444845110f400003000100e11260700008580071107c0c03044100305060100740e140b0016400c06003100312040c0301001407074090b035920b1022114078440c01c006401c09041a28004e04420307460304404009030f041050800c00c008510b015950004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 808054919 1250 808053669 808053677
    0x20f28020c010507152c0f0c1315050402030a020d0e01020a0203090d031101050f160c050303060121090809012006061c061b020d0509030606191a13060c050706 70
    0x8086500101034006000165019158510342d020402c03d45c0e41e02c201b41c0143c010548a0b043e0707840414a0701c0e066020000d5800c0241ea0110541d541035540c4980c00c0440f5818883e011591104000b8045e030f40184ca20740520360300071032006008070640c801c50f069004002c008624000707064001940b2805000c41c411f204161106291040c0350203901c20031070840c44000200100e10300b50301610300b2600140c1c3e0400c4403800c00c441446c0c5907405401d0303001b585900b20000390b08581d00c0c803004580700a02102c5100595058401102d1401c005001d000a91446417445e1a150200c540c00100f5031402d02e040c0000011168800f034007540c0000c100306070001d50641c1c540380c41981421107520210b00c90080104118580394880c420403010260458100360140c0c299412078811401c101d41c0c1740145000c40b070389a040703540414407610300700c490742142481007094a0442540e89560390b89128034410784900c281030002d4692280d10070050088041d1003d03042843c44403406171912503940f1070501680d401c0c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 808056169 1250 808054919 808054943
    0x20a0e030a1a040807240b0d0b0a0218030a121715040902060f1303020a050d030503061c0c030b0f0609090307020108061c0309050a0b0f0f0a03020f28020c010507 71
    0x104c020002200c06a50704440121001401c0038003d00542c20908070924180345080010300381c034a040d0303600c10318403a0045058419a114445428004d6000204480380c00d400030081d0540390f1002e1040104450040f54200400c48140c500030f00880d90900c1c409031803a4640c81088003800d0310b5031402eaa00c03141964009400041803000c120a407003200358041a0413008906400f40c00300440d110f10907240700b42d440c83e010790b40e5101441610108810004d010900170700000da5113041183c944001030843c00d0780280d84001d29160a4010b41d03141d0816240d0101c1501040080703807080100540204040e0340c060341e03a00c0d040c40d200e9104e008405000341088004004600959655114500c0740280210300850061040c900036000c03031524824540103c4000ca00003031f0b1001e441c41074a440c4405640c540c0e20340003d0401740c02059215030080414140d01307202410741002c1080182c0114079605030070802a403c8640c0f1035003004070321981d50046500201603000c0a0740e0000c15102c000e980841140c00b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 808057419 1250 808056169 808056173
    0x705060703021b240a030c020606370f080f071203030902180a0902041b0f0804150606110c10120e0f0303040501090b01150906051b070603020a0e030a1a04 68
    0x7422011011302c015840390003005a07500340c030070005106860700364034204021080c0010036070301da400450f2455404403030340078080b0803c100c170f4442660b400f650300124011000801100f08080e00d41d50071044030340c1100e00040c003026800300080d2602400c0702d401040c0091502c1c04441190320402c40c003c003015110800402103440300906008a03125514880d03c4a29207094160010307e00c480e03040c0c0c440d40c03d0100e40a110341d001002184202c5090b6501035048107a0002130f034000e40f002d8022035030311b424a144082c010802d0f1141601802c001d6031880380500c43c18250514240b60b1030360301d620500700400982e003003682298025000c141c4600c8003140821042100c01e04008100481c040030780400030410042020660140ca2528860350322107440340d03214203a00080402d100610400b060b50750006000460141010301050703060303200201c981e184c140901d142005003c2c1d00c03007000b10f900451180c2000e50000381901201344250000d01d04010a501c40348503050266580070403500410011801b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 808058669 1250 808057419 808057429
    0x105040335010b0c0a050a150606031a0603091009050d0e040203101509090203010e07180806130816230c03120a180e0a0b010c0b0411031f0603050705060703021b 71
    0x12181d1b030401d00b41c80003015281441c2c103c80d03903a200707107100031407800b000802c4032406031041ca0389143ca000c0300d9000880c0c1c02801d05c9466030000e400d5441d07a10522001421556050180f03030030151083d0f002d424040c4c0c248001811f100070380d0745110321483c0140104221031b0b045103181000ca45070300010b20301c441c241103807d0b10b1292071034000d5501240000000309022640281660180314507551307800091081d09443e080456180c02224410341186000c070700340f1508800c08103201070140c404d04d0f20b0403944071001904034016000440e00d120b69101000042c100c88035034403c00098000240c0711035030540c000a40c5610504943e041c03c2900482c440203100d101c0c80f9000f40d4601e40b035030402c1da041d0312800085040c100845011100d181031200b00f040d154070680c031110456138411009266521556540c1610030303804007069801d4440c1e1039500b880b0b814003910303075100c4070003040c80002c0240c2141002420412540c00c62400351808100b5040003a0307000840031701e04840c1221000e408c21b03401002030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 808059919 1250 808058669 808058683
    0x414102d051c020c06060d08040b0304111e1f020a020d0f0b070c05010c2604020d02040c0e03060a11040e0703020f0a0905030f0115180605030105040335010b0c 70
    0x50442024841098154581c0c1c004d11003407126404076070840d594601003080585044400034002c2c58140402c0000709c580350b02468101e441443c02d0070290401e180416283c4030410b4290141c0c1090310f5105c207503820030850140c0c15074140000054480030f03500c000782d69000c0c1800e00074001d40c41c940c190020700c54442104910b155000c0104620750a2480004040d8051244262140e518041000300130358041c04600300c0f0071114150701340c2a0307030424040024048009200380d8015030180d002a0040c0c1c0e0b01c1c03044d4621000d00c0e450700882c6090010616180c294000d1000d98814600071035011000c510300c090720308680d804c080f0310343e00343d0f500d020440180c01086c15001c07071100c0c0070a400304000e800c502e201090301c200b6000c849401043d4241c0728280c0382c8110b8842143c4040f1101408018103031003000e580c035230020318041034555980003c642125003c40e020390001c0d01d90702c0035040c0380c0f0100103072088200740c003200c030008003c0d01000540e0040043c4112681c1c2c2c44000307190001c0031420b00041c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 808061169 1250 808059919 808059937
    0xb01030504240b13091b060206070e010e031005012d050f0a0f031214090a06050c03040f141014030a05150303210105041505040c0201110414102d05 65
    0x101d10018131261510040c0c251210100e85207280e114000c0900c5402004510460340c5560042c01c0c103440d5031078191404c040503002d4904000007070307485d0001c586081084031030845002078001040e601d090044000307100c0c401c80c1c4107090350700b100b01080125408150a030688104582400b4441103800024150002d1a4080e121001c80d0507800000e004504001c2e0b080da1041e511401001403030b2182890083c4504000303140c1c4641c1c1122b00703220b118468005044146950030489103059101c4103604c3e5000c2d03c0c1d5201c2c42454000310001322032070624403001d01701996142011082c8003c040e1300d0b20340ca40402801701c04103035134400018082c4d81d4500c41a80303041c003014080d655038440114168406e03c418030020300c20116003800000f20f5003041d21480711015010040c4080d40303400e00c4c00f0480138001c519a00400c66407a0880603656441c0100240002c3c0b03904e0241c01c03109410b000503c100c035152860740d0014808594102c14885030840d41e0a4101c44042014610301d9400d81800c0c1c0d4107004074960 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 808062419 1250 808061169 808061179
    0xb0709053102092803021e09070c0201020f03180418080304140106050d11010201060806010f050d08124b130813031a0c070311240a0b01030504240b 65
    0x4a1111510000340f00c01680d0081d070341d8125080c1d100388030a01f02a100014540c1060920300061403003482006002c540904c1441030b50310410300399210f41d2540e00140f00400c0040ca0f40101c084891070076102e11078202009000805000c3c80b81e40b103003015400300820203001c0700c0c407401c0c20868440b030a602201c050403000b0030070450103003030b0700f0840180000707441400d01640ca0110007048141d00054486e0494001c0c0c00d100340c0c898284810700ca10041d4043c801c58010341c0078070100d149010a89245485094600a0b48555070440503618048134540c50103080204214203003180c1d6484648442c406114050800d00310a41352261700a030240f5138140c020f08040e4010490013101c0c02805184800c6a00ac2d0f190500e01640d60040d06028800680e000818214100310080000f4014038001c1c221b01e48540517100c6a000c003a1208080d200c40807004107101000600f04400095244150300c004038080c0385c204030503d0b00d980c803465506c0d86802440d1a855230684452032021094000c8540e40c000600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 808063669 1250 808062419 808062469
    0x209040f020d150e0c0a02030904050f073b060c070b0c0706050f07060506030a0c03050109030f03091106030c0f040902031008190611070b070905310209 67
    0x508a0002c0d0032040e40010b4080c1015100074003c100b041445080d220141c801a60903103540c150903050340e0045801c001036000c01e01002c0856691445110310507000d0301c1100b1039034581034000400b400300381c076000b6480d01042007007560260241d0868480403c541442507809100c0000094114001e03500002e0162003121030208041d034950001d072032580d41020455854039103801c0241c802e8081c41190004505e0244000f401207981038001d1500820058103541c1c010b40c05449070841d0f030700541c0041d21160b44135900e1404140c1d010350b00523003903e05403408029200391540d4502a07803a0303004030b9501c11300011020030200002c600c116165611965600341d95140d40392191340c043d420840300b01e1580035020000040407200400d4440309003000d42000121b0701015900d4400070141040c004846e403030188030120000c0c12b212a504d0192400c1d48892980c2c41c686001c1040714001d01044480482741b039078008000d401020010042400c2c030010140c0c40d1840c0c840400e820003248903480e003a08580c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 808064919 1250 808063669 808063691
    0x1b2a080f1b040e0613210315060305010501050702010c0c0b1605120412151d010e01060533090d0f12031802041802130b0a23100201020904 61
    0x40c9201c94100a05401d6607508414000c10045900b000e50242540c1c21450004040414001c15400c2030303807250590900400400c5604545040104489000b00b0307070f100f944070081800d4158403001003c0510b801d1060350b0511000820714082c0140c000d0501c0b10a802c0034040101d107502d0400540180507005403280e10b144404030304062544000d47c0c3c0b41c003503103a81c101e98103092421a02561031844460818000f10381d503000b000c981c0000041c520903075070782480d02481911002105a091200e00100340000c00e240980d003150140d91149102d80005900c1071a6141c0e2a081c16000c10603c40b2400c5a030540d000e9424694421494407a07405981400e2040401441e10401d0b50a14010306619603500c0420509078200c6a006a004d50b9007800050000700516050b00030842503130340b00e0f41c91410a0315030307408100e00035040e4882e0650340ba00c504c1c546100b814414410002451181c100c0b00d41c1c090005040b208244264030318034050002c8000c201c1c0034600075011194541d4003e0070410440c0c3c20a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 808066169 1250 808064919 808064923
    0xb030a060801151e050616080d1a031c02100c020a080a0f08070201110711011b05010e150408030a2c070f0b1c020307120501030c03031b2a080f 63
    0x2a00a408024100743c90111381012201040404e84101500301071510440399420b10052240c0c420441d440c072030800180e00c005829000342c1142443c1d60b2180d030050b04150007054100140307100110400c41002000e0390800360b0000b6018030007841240f002560907a191422420012440800340c183d52000900c81700c00c0340d22540b00381d0111100d0307880c040b0740e49030004100d00f42d600100d16004850780a02c4245c0110b8002013400078100d00c14100180003042c8283e00c5013928140c5e2109850030307551940500700004041c03200e42171041c01c0a89110591a00355a040d00c140400707014a07660654405040d0340e01142402407001610700d84081c2c002105103442542d80d241d0300e5010f4000e00400c040b00001c0d106144c042616405200d445e46490b12018154942d0001d4100901580800c0040024200c00444501c07c4a010714000d1080552150441c00e01500c0c00994000000036004010305d5200400c80441079203004108018994540b8401144280c111185c1c60300880003d0240c504114044500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 808067419 1250 808066169 808066211
    0x150c0906130308031e072705090405070e010f0f260303090f15010b0715061e0f120f032706020c120105010b1210030f0b100902070201090b030a060801 66
    0x5003114180e0348550030170700328406040c0d40410220341d200b41e5043d0300301144103c055000c1c10400303060340c0c0c5541d00c0e000145c80760401d60b41074444c0c0c1c00840b410b000708980034980c9409061000020b0941c0c520300741460560b44024030075103040318004101200407010034001c1603140d940b040d0840fa00e070f0403c010859102c8000201446051069035242340c101d082040b14581260321036075545043c19426191410900700195000780f9555441c8004201100201c01e19140c41d04500000c1000030705140200348201e00a030042c000b26500b1b810440d002444100400d44215854a80240e42c0700d5030008202c0c1416801c52002104600000f012445039400190310101901c111905904012102002d608981c02801008405032041021510500c6400205500b01d041d1548d281e80d19656034546c400086613000007110080d04910611003045114960300020341100324045180203040d500181c40e254061088e480070790300200009030501d0465100790020310b4044001e200c0000690210303600d00c28 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 808068669 1250 808067419 808067431
    0x120b0a1e0f050d23060c04030b0a0b06040b07050a0b0c181816050904020c03130b090d060906390503010e0112050a120801090c02150c090613030803 65
    0x100304000205007080d46012821104080d019150084154888019600d040715208900341c1c4001c10180103e2400c10843d0303ca400c07820926a1141c0c103502d00000701c040c0c06010f041c411400c2400c40c84007640c8580841d422a1001030b00c0782ea4814403071910030b080c1028404003411020703900e0100031110102c0801410601c0c04070043e14203000e000030810031545900b050005440c04c5140015100065110002c1d0b4442447e040c02170400075000b0026059911800c1c180d0360541011441c00413420042c69100041c0a142d8079050901013000c010600e21213450b4800760100303031034a4068041c09046d6000d100000c403080d0300d99110fa0003842440d0f08455109071351000c0d80b81c1215144001c980702d582034a041c2c1d60a0071800b625a440c15000900503101e03c00c0943c1c480c022818440b00044601d0303603160680905441e024610362522680c0801c650b4180308001c2076401840a2071a0713034080700c01641d4440300114030f00c0e40f181d00d040f000c2801802150f503c0040c0c80301003040841802048405588190 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 808069919 1250 808068669 808068719
    0xd051002041d1f0b090105041e0609050319080a0c02280506041a0c15010f0503061b2a07060e040e0c010504230d081c0615120b0a 57
    0xe1100c000c089041484409290f9000c00c04400a00c26807044100404011005252050510fa15501c45094a084a603800383c00c841d00c1300000c00ca01900300030010004c1c1422401b50400d5a40b0080c890802003c1c881c000344224800124400b5090044c030340c1500840e00034000d61042d81c00022440348807240c110700d00d0601e01c0058000140b40c58200200e41c00c0d0344481e440c410043e141040310001c0c0b900602c0c1d0405185c012400386013480490452441d0003441415a070804c094941400c0c14288a800742581103d0101c88a42000180761442112410784084003811040c407415105141c4c003444034941140c1c00c1c052803100250090380700d0140e4a600100300c40400401d24a0514a5613501c60740c1072280c00705800b07100400200e20780790640706c0d00311010300784010303008072040000307513200041d030000c880084021401b955031001801c1d4424915090060030401e040c241460075962902c5100c881c010048070812859040b5015000700d00c103000080c207500442c64890141e0b611190301034454007041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 808071169 1250 808069919 808069921
    0x5060a05180d03020d02070b0f0114010c020604060c020a05030f0d090f1202010518060a030501030311210a020120041517011208071202030c0d0804110d051002041d 72
    0x716444144141d64000000140301d100c40c00708069010390460180a1000c650901a000204e400c0000c9544142e040054859103036041610201142404503412070402220345914001a182c00040381c041d00c0c41414004d41080f624800180d004185400180c1c050140d51840c0c0c41100001070020080041034031a1301503561100220300110007184507641201149604080240d4003500c010320220510035801820000907201003040c60b44004a000c0c00640d50300010005d1552041920000c02e8080c6c2c0a481d83c00741c03007001c808414285000c1d0f5140000300107002c102c0c5a0017584900e81e4010740d00c02c605581b509041840c0080d421500c211031515550f0f8000c2d550701403084140343c810030a803c0226402ea428000d28220251604404462002c0d08100f4800842c04151100720303200500e9000f16681c1408c510310a0401c0381d401121411301800e107041c0000114600345d0b0803040301c000c0e10b1034820001e2a007400c03460000151441082144001000300b500700c1c801640500784c08440d00d180020f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 808072419 1250 808071169 808071181
    0x160506100e060310021b0a050d08151305090f01090f0b01060203131208041d2403150601022503021e061602191214010203091c0309080705060a05 64
    0x31203007046070207580c1500300da4195000c68240741d001c2c00c2207071003885e400d660442400324a41e24084880e0819a40c40e41b141c035080071040c4e8030001159001107603141c40c91aa8507d000407940c840241c12181d000c10f0388030b0000651460003001115501e0080740002d01684c0c0d400c1c1004080341d06118416030743c948030500003141c004e0001003221400d9a41d200c0794000240392010050130300100c40d00071141c03448204400035030702d0595410f203041036080c0d070442645c40c1003441703102401d500d01c00385c2803100e503100c001c5030304583e81c000c6408103c003406000000503e9458100403802c0480c600e407e4400c10385008102108000101c0c0100c040d00d101f0b860b504400d0f000d0010034402008451a10f5500500401c100d492526600241c0c032075081c40076142ea016041410b861180c40040354004500016085c4041c1c01072113004042e817243c0940f684000c601c2c5d414070905850302d0f0000700e503034800300c0340c8466090f10503184294051090f6582107441151140300a241007074a070f09090360103000301c2d4140008141 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 808073669 1250 808072419 808072439
    0x906060402030c2d0703080907080c01020a03051e0703050a0e01030b09011e030c090e120906070b0408070f080319060b09010f1107030503120901020a05040e0402040216050610 77
    0x70141c411010340c44d05041039025008802425a15a90052034200e54519100500c01000e005014826111a00d151508180313603440c00c6110f07813140b002a44052400d504698000c581c80c091076800d032030310941e10494029201030210707148500410010300050f0103000c0c1a4030801800350040c0030755425034010392940044058883c07040100b64003036580d000411141210304514841442c04440c0e40410f140d0ba92914051150a50f00100d201e40e11400822030031a4103010044a20340354407056800e1041b44804035201e03010380c3c00c00429004100d80410140036800043d01d0317041c0d40c0a4021a4655500d10f0501030f141c1040d1019400b02040305444940d280950240c40107480c005045941486400c0c00115a511140d010400c03d200505081c201488014003104000d5400780000355503940c80c1e444841c090300001070412034264414441900340c980e00100f103c1c11201c04000060032900c56000260081c0f24108603d040c080c2c0c14160340c3e00304200414400c0c032030246201405882e070303a10404a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 808074919 1250 808073669 808073671
    0x10902030607180905061801080726070b1c020d061d06030c01210504110a0b1204030f030e1f06120f0b100803070516060c050a021e0d0b090606040203 66
    0xb1500343c548120521501c09103501c0140d01000003400300d2404100440d007200c0800007a003040c003194021050901285600502200c0040102e01c40040d88a09100c509030f1100c541e801202c40106e030010b44a66905594044002146120201156525a6100003800a1401c1d1299a030084202d075200c820701d440880f1603e00c54a4042c003e842d0360b010580045803401035401c640c0068001504822900d80c14501c40c5c03900c03551058501001ca0a06c2404110882d006030780b1038106040104002c581c80d00c1010881c40d040703035060a041107003400a800c1500545401c0b2400b802d94480c10205000b510b040d000c400c082d5900b1180208145925031490f42c03691001c49a000d4501125109450009410b04134419884200034a036a240b041d01c0c3c00c9580c0c00c2d50b0022006075400d9100404489445000045c024001c1889040c054048501d980d1069190f0a5030b8034064482ca108032407651821005062441805c040105180d0034402903103415a01045c0a0b25440c00d41e22503080000c42e242414400c803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 808076169 1250 808074919 808074947
    0x150a0b030c060c0a060b041e091103010603120c0c1a0318031e030c070602120711010902090c0a0909050a020a0905030106060516080706021c0c09032301021308010902030607 76
    0x98800c00780700752100809006d142a00742e4100369620400811000a01340d90842111080c0c0045a07034816801c040c0c000000340d882e124031903454240100001441030015020382801801c2072010043c02d0b0415281400050340500c801e842060802042d12030301c03100551103410f02c150300441c4891500780075035503030040c0c21180c001700f40c41c2d10000c800c0325060700246912001400030300b4600866075a48a0036a0005101094201e00704800d2194240c0c128146d0300d0210390220007007201c1550780c6c000401c0024080c041c0a00b809c000a0401541c912803000c0c40013410058100788228101165070380c0083d8041c588050000c1d450304404aa0703460180180c3e012903400d641d40c40e003001c80d01c0c2c43c0410141c10b1803504444145041043c940010b115001410f40c1c01100b00e5880c881c00d40d40002103041e0340d0000080f40410600030818070029010101d04030b80c0c0d5824031005000c0100111200f802407203981e00807020340b005000005190001504262402d41c0b00341c09942076a29074000645000d4505c41c06 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 808077419 1250 808076169 808076173
    0x303020309010c0c050307081e0c09040f020f0405181b06030402041503050a0f1e0b0718031a0916030c1512091a070509060304020909150a0b030c060c 66
    0x1c0445158030521890030071030b019120780403a9950740c41c0002d00e4611341e030f8080039407130b0000c820121151841d170701500f060500300310141005d288081300051b1203a0000344000d00c0426000c0340340c8155142d080c440b218210019000704154145451003218690010901c0140782c4180035582d261035070300031034a4240380c0e00686840e0458036590308000140010f800c050349082120381000021800410010300094001c0400440c00c0d10385003407985450214004810401415400050005241000300c6900492910b0120040c0c4103006e41e5124200c150782c0090403e1038016901c03104c078200107500382e008103c0c0380c040368010764806a203403000c00c030079220160110004880420940041140e034008102c02441d000030f0020144c4082003c41c2e0300f46900780c844e02070000710402d407005d4a02c05d807078000c80182001410300c01c40c0c3c400213569100042000340201c0200c0040781d03141d0404c018102850003041036441031481d00381c85050050240d01115032003481411100101ba09104040303c4d050b030200c3d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 808078669 1250 808077419 808077427
    0x6090c090610180609061202030106320706150e0601140a05040906120b010915090b130e031e070c0314101b02060a060e070c0f021e0108090703030203 66
    0x410456450340c80c158020030b0003220f40d07804511001e03420743d20300a459180c0342c543c100c5042410040203d10060861480c03e4070400050100c0c03500101c00b690683c40c1010b8031505490400c500c03203159903c5103007a110009011a0503000c00507030703411200907201c0410005000c1640c0e500c96400100007a102c1c00d0100740302c0c000481145650070018030103108103041180c54035a9400c8903c04442041d446480005241c05043c0c04001d04880c00314014010032a040c0725040413503e042d80760b00030612882c0011690384144031803a031102405409039404100c0104010407524400c9a201d92204510b10028100c0c0004d4521882600f0f00f515041d641010950590f80e003159034446244424940e806a40d2180c20002c003da146240200c07009043c01001d50140c44071210070185c640f10707000e040b80a8280c1040420300401400281269000c5110310f03100c40260010300344511002280600a9080440e014191a00c04196420404400001e07a2806265500c1d201d07810303104c1d4010300008006801c108 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 808079919 1250 808078669 808078681
    0xd180e01030f0c030f1202150f0c0a030b04050a150e09100504031707120b0103181b030b0c03161b020f030f1f0c1d0907110609060906090c09 62
    0x305049400d81c1c8030f0302d002030100f42c481d121715184407010700c0111401c1031141d4000400c0e580c1070120300801d50851282960b07908080e41d5089520134020001201b12402142c180c4c101e61191300201040300c0090020405030810004c1070b40039000540d100311461890340b800040286041c403841d841061508064221081040c060b50003a01e07002d4001d0b170802c8524060000021307401102c2c03500401c1c45484803030000d08a09140b0058540f40e203a464107052915215210f0002c1c020f0382c0d401d002d0340c0f00240703880d41440c20302401c03009216500b003e0546000c1d9000c021380c040088004500070541c0d105510080c0c105554110792611030750107440b1014551030750b05001420881d50720071185500a080e65030a10344203490718a071002c0c4080401003900c0e02c0c110302c4414903481c0318501c4500c8041c03074842c09520341c070690303142c602003a041014010800100001c41440c480c41305a4a000c202006441003400d213980000c0d6581000e507200000c0c3d00801001c01c0310140f0015801e800701002806402c60f6507580 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 808081169 1250 808079919 808079933
    0x60a0e010e0d02040219021e0606040507021e070e06040207031d030c04090302010218010e09070e0105042c01090e0c040e01020f0406090e0604060320030f0d020d180e0103 75
    0xd040d000d41200360b800a41c0010395a90019152040b681c0f045643c09802081c00203262501d965aa0007072a00d81c4880c0c180d45d03510126404d94001000d03903011900d51201031080b450201c00b0f4a40a510605240b600b00148802140c22821540c0301c0c400302d03103551038110400c01240304000b0000d01250608030500c600d07015501c032001c0d41d0640101554078002c0410f0109055526450b011001071354000b6200f4081d80c0c0c20350b26500c68180c20b28050040c0c00c0c0180120f68228000342c9030340c040c007070000d11418250380b04908803005884c5098581799542441d2102401020000f50890101065107001040c444400c4c421104030310000030040818154031820b000061075019000e12995400f0400c58106c1416000200010203085d9510f001151801000721443c500c05072080d4804c42c109003003040841e0480c160100001003224000320040700090000e4503000c2c402038610040d019540070b54600c00d4022a9031180e00702c48e41c540015001c4ac0d900c2d0b1202000541c054140d203076040100601c041010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 808082419 1250 808081169 808081187
    0x1324030903030f050c0405041d0d0804050f030f07060b0415090209030a08040f06021c0f080c120f0703110c0a12120203340804030f1205090c040b060a0e01 68
    0x30b414002841805504141c0540701c04441944015030001001c11860401d4880d21580c5000c0030b440300c005848074452281c551005058043c02c007e180320205003804000d20040c9000c004100441e80d82d00700300c007100d1090740c10440080d40c11a1070520001c0311401c040c014100f0b030b05804c4664140b402d04059100b00203401484034260144100500d200c0020001c400420140c41060708aa601c0740c5811802480c281c03044c0700070411b00410010400500d50016000c180201c15400e011034999908060044079000e2051460b103a0300186c420320802c0407000f542030b03010b000076035004d200c0310203080d2920005200700701f03248080c2c0c2d1100840304081000d14210269140c82c61034000302d4180300960410a80c1c106070351100f0130908041d0503258407824903802c1800f003aa00300003080406405000541303071160040000c1c046c4000035507107401c0c2500c04d4540c2d1031074048260040020b0708082400a50710044101500c0c041c40c50310309410040d1501005462007405551356812061103100011100240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 808083669 1250 808082419 808082423
    0x912030c0d0f021914090906010309020607030e040e0a0314031b0d0f0c0806060a1d1903050d09080d050a2a0b01150903110f040c020313240309 63
    0x2014064114504070501525441910348000903803958a00801120500030f4001c0340f01c284a1050300c0d51609607103040940d243c800c011105825940d98410050300a8101c0c070000039409800001c051040541001269030320030001d0b5001c1000381040fa60300ba681c0c03800b0150140124044070341c944d40a6500300c000b5907020f80f03c4100d40c1d01e94070680c040100d203900003134581d000c1103480f100880041e000714440c022182109103850034130b0b0b040120214041c5c2c425aa000d40400400103084061200c0600580f80c02c44c0f0007900c4603080c00c08221011416410600003110074ac081c0484032800c0510542c140819108003201a16810a203070304140c40e158007002c1d0003030034015045c00089a1555000704c0000001d850042007610360300e246051254203e05801003070f0040d90682002054a91100d0310505070380e4032415501c410f650380c200180c48109904400c0e940301c4e0801e01601125075012000d0b20341510140c06020382e07252260b402c0c00004c80c51403001c03000c43c102e482039040c5003071103030700300c1c0e16264 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 808084919 1250 808083669 808083691
    0x22020d060b0901030c090e030717071b150e030d0503180f07090204061806081f0f06200f1c030f1103070f02010b030a03081b030103030c020a0905091203 67
    0x1562660120b15080b009910036034010b070600b5810003c0003821f0003080c10b09802c0d6400b0b540f0300340b86a41e400700c80c502d0070300360803c103850041123887c200400031035070480700001c3c3c0c0121400b050b913410416081c192210045000078417000c691614904000800300c50409442c1c694a04540d5911414400a0042000500c007442820305040540d8400e0000300d001d0810b8810159895080040281115101800505025280700010040c0e04d500481c2681c00c4840d450304c0c040100740c24a55540b008400307410010b08007a41d040c0000d61140c10280401c00c0402888000c0300d100c00c3e8151094607101d018120301419040202042203111100c000850b0404060a001541d4a561030350807080b11040e048510030040300106100030280c012603000c92688251009015030400b050200b030f15030400803002001d101d54070001c07415000b41031261100390000803a00544943e5641001006c00351510020780c011840d601c0049a400310500525206032541e9009241d03141940b603500d81143c0c401000c0110361 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 808086169 1250 808084919 808084931
    0xf0b16060e10020c100b06031e0604110d06090612050601090c050c01022106040e10050615030a050a200702010c06021312050d081b09040b13021222020d06 68
    0x1c2c0c0d90920103400c05a00700e0005140c80385861180208450b02208034910a0b0418400c010180e4003400c11601180700e602c034440119110100844c001d410b00307098801c0d01e40310205010100190350750005040700c01c03648091240e1070b070b5590302c028000d40a8801a0858000c48010b00001e89142c20014500c400c3d46841403415440f02c0c4594220b0300f12520720140c840004508598110b010307000740e0f401c00400c031000c010303000e031181e080d40c0c1c0c038440000c12a242503190b0000800c039507940d0b0070601240717040c40c1d07403280d0382d1920315030000c01060203c4200010901e0064900c0e414001440c000c00b5410103111614a03041c40c54005491102484c0b85c111182070f02002150b8a032a01c1c1490b040003441e10b00c400c0a101c400e03600c0c1540c18508040502d00c20000c0090400115042001507010541c01c44410560b40d6101b800c04280038101d400c524507001201e00f8402c0c460300d41e5650080c0400d1090100450154a40c42c1002d100505020410942e806c0261744180141c43d1a41014880e5403140c2c0c800101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 808087419 1250 808086169 808086193
    0xc1207020c040e0a020f10020a1b0314030c0d020a02010c08090a05100e0405090f0627030a0507050c10051e130b0a11060c0d0914160f0b16060e 63
    0x68810010f801c5186401c900156421401c240c0206104207200300c600e0b002c1c0407801d00000303641780c51001018150243c2407000001140007454004003968004c00c40480841006500c140e0302d511020761152540308100e0b425001134800710300b41702ca450f8141c1d04e0584451071516211441d40022303140c154002c542040003c2c566451f8156418880c0f40b64403a091502e00340010002114001403c80f0195040000900012000401c046901c440c00002070300c80e05404550384c0401120000d40180c040c032000501000d4540c014000e000481e21a004030350420324039106108208960005801c0400c0c0c0501504500fa16440e9890941035000740360103050562405000130080c0c0c166115000e0b071900040c0c3e21038040d511154211209c000390f4000c101c1424180e402020700d00c111100b62602c5551101e40704200440c03a0301d010110306040084031000d941d458980b05114010b03225009140640d10f00004650f900c02040c0c904041e00c4c0401d10780821519140c0c01d01800204440d184d8070301a040d10b00714 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 808088669 1250 808087419 808087421
    0x10b0c0718021306080601020d0504030c0302060a0507060608060627071d42161104091a0a0b01081b0f03010603061e051e0102160902210c1207020c04 66
    0x4020030305561000514107084001906103641c4000c0c0c801000ac0400051001c0707000006480226541901c4899580140f903a00b10b50500030f072130000300310500b4524001148040055000d014000c02c80700c8002d2540191580d11580f648001e59580000c865030029004a00800d2404c4500443e22101b05034242c5500c0000d0203141603024101840070281281d24194040800c1c4407900c082101c0c0d4507103039007241d001d66409405040c1410842907920141d0304100700380041ea41540c540040c00600c0f0300c7c42d0328501400c25044c410901c00e41c030000140000c00c000224000d202d91480103844400854641041406411003c102554100b100800001c2c0c503480800d8006d500030900d994000900d54100184900c0040d406900f1200c0141314900910099071012002e060398150140d00d5030007011031000503420584031040010f100c86403003600080c009d03007035001070124016a0a0113403600d200b40c0750508110b41d00340c803407021405051004e40407911554070304582007941401250340e48000c040001d8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 808089919 1250 808088669 808088707
    0x806150f04090212060102070602060a090204020405130507021015140d1a07030b03070b04090b0f090115120c051207170a0c020f010b01050904020a0311031806010b0c071802 76
    0x282d009600040c200c0e4141c40080b0b695410a6007440604101440c0c204001d5440601801c111140303560349024008550319581120f004100c09480385000079000702c07140d801003004407044800741c022902047d0603840203209171098400b0801c1c003100c4590502c490007a2600c040100160800310581000b0041000e400d0a09029202c042203100d880c80d0143e0000e00b038130f2003411964041c2e03010300b60070710100e0b000a003a5000d6815111001070500341c0540081c0b042140302e01101e4005100030000b08820079046421010003a142e00c500314034070b000110300710032203c0d0200382c000000d409101d52a4a20701041249400a145107040026601c1c544078000c0d000400f560f40351004d90365203080344a03058040c0601d10480203210000c110100c00c500010340944998210381c0e100e29800140990350500a500c100000c1d01220351040c1c9a140111403030001d40d8090850543c0c900c0751100000754518079408039800c4000c088054443c152034034441c0030342e11605840c402c0301075809108070200464295840 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 808091169 1250 808089919 808089929
    0x1c020708070506090d020616030b01020c041a180402300d02060f010e10051201060e010b13050307060c2d050105011e1a03070306031b03060c030209010806150f04 71
    0x40d03c06810302141c540d14100b030200030102550480d10801503585980040d0384040c2840342004180a071149004034280701d92421f80541c081c0c0381a0044003031054030400307040002c1082e50052210a5440d03900d40110804480080d4488501098064249030380f27071703441482881499403000480c002400e01030420200440002c0141c1c09042005080b8561003407541c0102030a0300144401d0030048800019982180509030150721402c00650b031820302588540700a11043c80300c2e260550b140c000283d2254042d0341406583d1800700720214051038003140304000c079482c0b52101600180b6a42d281c550601e194001c0e8102004800014900c540056964002072071140c0c00014103581406000c0103041261f0840c0840200d19003014480c910018a03c0544102101007281d200d17500d441f022005003840d80c200504072203c2d08100741d94011031120310402e50f403082c00244030ba103400c0c00c002c80403805080c02d524002403902011907143d040818014240240c5014a54600345074444482403942c850381c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 808092419 1250 808091169 808091173
    0x5040917070f0507031a15010f080c0c12071205090a06110c060a0f171302062805071101050304080711010e09070507050609060108031b0705040f06060e04060b1c0207080705 76
    0x2000446c4c1681c2c60725035600000690480d000f000030800001e001ea21401c003940c1c18481020301080544900318103660204100314200c0f19203e0314180b032001c0a4000e840100c800340c000b52000ac503014021812303100600c40240035000c44034680341e81140e504c0c10003520741e0810300031031050004c242c40d0390000b080311050030340702c2e1020203e44460060041d603c080012000390a00300503c0002401004003036170803038040301c44035200c86c0c0718082400d5105c281840c801c40300043c800c0c1c540001c0d400c00050407a46000b03010418003841810015981e910040300d006007000803c00074a00010001101c100040c0d8043c03401c0404c0320180d40100d094000705131030243c04a440810307680f0400030b00b0822183d0100c110740c050544c651524034665500c0c00703461501c5210302c0104804203003149080181200400d0014003d00525160106180040c80d060041c1d10020f00403904036601c07070901d8040c0780221084040d5407490504042d0740f54900b240c030781044c003001c03035020000c0d0710106084402900c0d41c1401480 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 808093525 1106 808092419 808092443
    0x1120b1e0f090f0103020111030c0a0f0501020d060906090b0d0542240d060b0f04050108030a02060618130f050d03050604050105040917070f050703 65
    0x820705402480300020816107030652540581224000c3e21291180345013042841c0c0c4074460096600b42540c440401c02d00094078203402185501e000398001803c0500c011410021750300315900c400100358440341d050003982d62174800c00c8017036081212003451080260780c40a8680744110303105031390712a03044405a4090011144200403c071400cd0003040c146010005081c2c821040d2110740102001d00244210016040400f48111030b00508081405034a0754805002d0619003080980203100c0143c44065030701c50f401400c1c00b8120503c00b4640314500100024074148004000754071988000c004c4009d441c07145a291504289081c140742c0303034800305090041c0220140d8000070640e2041c9241c0303000841e4140d0000d80140011201403060341d80c1c5004100544a030b0220161440d15a03a18005c038040d2007000501c0002d20407900c0c40303681e860f1512058182866640255042410030b8 = true := by decide +kernel

theorem cover : BRFrame.Cov 807913669 808093525 := by
  have h0 := BRFrame.cov_init 807913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 807913669 ≤ n) (h2 : n < 808093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
