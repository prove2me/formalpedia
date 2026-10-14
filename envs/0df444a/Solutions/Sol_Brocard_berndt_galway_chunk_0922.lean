-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0922
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:58:00.448977+00:00
-- url     : https://prove2.me/submissions/b6617b1a-bb19-4191-ae7f-0bcc90027b5b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 165647482 ≤ n < 165827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 165648732 1250 165647482 165647501
    0x5010911160813030f0f1a130f020301091b03030206010902180105220b04050a080a03050f0304050708011d011a090604020c0111030c03010509010b0406021b300118080409 75
    0x11100c05030755070340d40c5d240300f616503200222562002107400c0d130207020b00601c0410f1078101c00c3c03520b244d0340d213880c2c0c8002c22092071050005002c11528203c203010754400750301044140358032407103021a048050048200c5858913110440061080c14008100515140240c460180321041800d0000014400640701c1e80c00815814034881194020300c1c10300302241a08800070300e0210051070f030325418601030191025036030f040740d507582d80b014000c0c400103a07100f000c5a030318908400d001e944176203941c6400e80c1000d5040e81300c40b01c198203088440d01201d0700e00041d654071605c9800208480c80e10702c50703c69042d424800c00e940d03208031039200013202c5081640041c03010b106480000601050348201c00d002036001500e90800440f00440140700c2c50400c051020301402c0c27658400d908051810314000d50761188940549402d4051020b007002545580000b0003503440e105c20000441e501001c14942150810307240c07044650709091811960904108a0000441c1c210340e103180340030b046c51441c40140c50041d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 165649982 1250 165648732 165648757
    0x60b0a2103142a010b01020102090604060f0c050d02010b210c06031905131202030415050d02040e040f05010b0a120b070509060a03140a0606050706090c05060a0201050109111608 78
    0x40707443e07510201c8184441505a24485480455200d00b8070b190856812281e85819603104000190031542c5000699003101d00500d0030800201907042e08542d0880714150090051046c03a40d800b003000d8042d0440305034083c007600c100300140c03622410382440d0348496440003807039003101ca0503013401c2c140403004543c07103030030741c1c8079040c2e5903c4c6090382e24100c410071903902e88a891a035502008000f84a8003103100800144000c6003000d0500881f10114034840c1841414844005803035030206050fa0141c5c0c009000100100d80d091419080c01c07210422200d0085070300c3d502e03068050782d5900d1304601001c00e0f40e400d001d80e8400000c1981c0c0c0d1101c0c110000d891401408401d00ca1840c10742c3e14840205101a920340c3c0200d0701e4a880700c16100440710242c404030b991401c1540510a080d88101a04d40c00d9802100c040b5064030a0300708034000010399007010340c0008000801c24030315a0150040c5040310513100c020402c0002044146849000d101550000220705e44121004101480003800c0c881520a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 165651232 1250 165649982 165649987
    0x71101081b1810030203010e0c0306010318120908070807090504050c03060106050c010515011b06110d140603030a0f05071103160e070c02030304060f1b060b0a210314 73
    0x70702045456030070568510200c1070005440c034809003403441690758184070a0409504550500c2080c00d9075108c010031400042a001c0000f503d030f61b120780c1001c2d008c03504030140d040c813407802802c00c3c41301d0003542100c90010a044100c002208000001c2c0802243c1c0400082c0c022142800b4201000e4030340030b001950f2901c0354680180441c1c1d01802854000e2545880b2280c1e140000c3e0b1b1003e080d030300c0040050030710004120880c4042c1c1d07040450400708490441c1e28202c4e0030180c1c64004018081c5941c0403411002c040781460b404d04e440d62145c40c111a80c244071740219548c00c020155039104032041c0b034001480d0083c01c801c00ca40a034000d041d04612841c583c3e010020040082880c2009102c0c1c601024a60f80303108004246084040b42d80040a038980808081c0c91500466600d1007a880b8030010042c0210140e0140b07442100200d00e0a050252482040300c01c90074000081d0031050038803407048003000380c00600030400b080081112062028540302682807500d0039540c00d80c507840005400c9008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 165652482 1250 165651232 165651271
    0x9020d0b03010c02150f04050604080901020a0b181603050714130c020c130b100f020304080616171e062701030b1513020c01110a0302040806070507110108 68
    0x3805150448501c035401022041c8040143c0200454003074040411b80001001340008100d012410a074441d4004040301d81d1115031200403450300c043c000703010b03152031694010f118560381180540e4025003800d1080b0f030007080e1f03080d034072141c1030189120091555005610400c9202e060310101c10002074000d180003800c103034030140c000a17101c490b130807040140c0003815925242d2801c0c50007010b0f20341406600b0450b8078002c501040c0392009424241d4203108007907101080d21442042203d02500304036003911501c3c100240d101844072040701d001c1020800c5208960170402116041031710609600046a0103c54200c4c90710440c140050000b035041903217407001c580301c00e0600102c009180700c0210a89000d601d0360804094148020f403081350030210540715070b80195a40b03021184500355941d0016522a00d03051414018007010255440c8800c0120300d130080c454041e800b60040b640d0241c2510b039903540d14001210148100400100090202c62015140b03501c00c070a03080d48401502000c2c03008c80e45 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 165653732 1250 165652482 165652489
    0x313030c05030d02030609010f050303071121030c15070c0809030312040f060e0d0203071b031b1503060f090c0905120d0e06030402011b08070b010611012409020d0b 72
    0x22843d07107040d0300d40000600c00349003801000c0030300400b540e0303d00d00c20150500c00043e8032803040c01c0c00946101001c10110715290756030103800c2c40c00d20040e00442d070707110300701c04003140c6175008483d40e034407540110f082d0840f04102d0580070503c00d140130340d40c0052040341603403209100c4e00408010341d00340c4401c0c403040a0800482c507084d40140d00950802d2121032162600e20300303442c007800720658150007a000104405030000240c503441c560000c4209504030440051441d100350a5202414602c0d03610440c07400748580750528003d40351403140e041d124003031103403090702a60303c248101c1d40040c404000030000040f082d404541f11505c145044010190744c3e90004040706200095604c060308103248140c90190804a1031101440a440b094103500d407640001e0455480c420000019000c11800c0b04100072a400440b039810b0307404140c49229584604000740502071815244545600e00390400602e600700042d089801c0c0c100300758641c5c855050410b6540650441c0c042074101d42c0c0c55550300d00c6903a4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 165654982 1250 165653732 165653737
    0x203041a0301080f0c0a05120c10080717010321170702010617070f17030d0905030702120f100c11030c0a0309060507050303060d08070203030a02060103050607030e030313030c0503 79
    0xc200c019510780d4188000c281c1000030034802d0b40455402050304054648801078120100c0d001110510303080a8140e144a040560a442941d4040c1122940003191a00003e2503401556296100080f12a00c2228201008030a00020780304281200d01942105e000d9800b0b80300b080f00354980118021100d15401d4a5007909842800140c1d4441350b00b880380580100c159a240c029000040071044c0c6440c450b82d1019106024501d03000100e0480c200c08100708008413103400c03401c0e4204025100060410b1510780c4c0154408911440c105604411020360004014000120b0312014144121040c1940750041c9401030180b0140414510009040c4100b400503203501d0b4030030b402800c40952141b8000301554401e802c00b10a001e400d01c8004003003440002030303e6000d1429183c848580f1240c0c14002c186010340e0800940c18880001c44546c866800300c1c1d80f5040701d21800495a01e0f0b11844400d50644075000c110a0f5158014030010380800c6008d40c1c40c620107402810a00d1101c485602d9403070a40d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 165656232 1250 165654982 165655019
    0xa06090602071a040203061006050f0903030415030209090a0c021e1626010524030c0a090b041a0d020f18010618120206031518091014010501080610020304 68
    0x496401003005608090101c554011841c2041d1488d85e42071000140050250182c1d204100502181c801c00c0c03620300b0812100a001c25014080b070b00004010004c010b0740c0310041c454058013041020400141d040d001c3c12443c030307601d60060400c50608034094000e04035246001d180354403884400c0041034181c4e15040e0060079014101842d404103a00007080240d400d40c8459110340c0c5030404100c1804071145d0751101500340d40c44030742c0c542700050700040d140240e2844265400307081d0400002c0c4036021580900400a000c0d40c0a00804001510744403110345144510f0340c00c4482c0d840c4600052411114035040280700401411040c540040c030026080b00903040b4030042042c013925034000301d01e45440c000c002d1281d240070700701000d250b501191403800050880400c0d10004c0e0001c4400c0d0742c0d10b241002032244403150071003280c03411071030555440d40d03600840014280b420108803101c14031071030410706882068440c2c2025031201e00600442e640b6032100c607030840c002404041450114054002c416 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 165657482 1250 165656232 165656273
    0x3030e0c1f030623100302040b03070c050d021b0f0a09051501111f020c0124091103060303070f0f080a200d0906180801050f040c0506030106020a0609060207 69
    0x205101d1280107821a003094019210604103110308881c0c22086484503e0440e4043d2910880940d00e80d4094029002e150440413038110080104400c013644490f170814080d000c0e604031035407a2201ea0099848a14030040202202d02030b84c42c0b1001400d100140920101c1e01a1144041b10382e5001c1c040c0488405880e101141d40c1f250320700d0303c06583c0c8029102c4607102d82102522054003074004400380c1020651042c00d1158010441a1180304290700c440f041221080103141000494a07681405045500958906515251800000074945015680701d203601030001c0d40b43c10681d440e500041a000340046410814040e45880020303015000740454400a89408940c002c940205000740c40b0201d00b00c83f855407140d84e8205016034031031240d02c121038039820005a08150f4024428014083e0340128006600300010b002c03a103555a143c442c455805044100e006a86403410450b140c8400e10a9000580c040c4490101154207170f808651604e108480041c58900e081c1d481d5546c1640140c02c9204 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 165658732 1250 165657482 165657529
    0x114040e01090f0606050a1b02040605060703020d0909020a0203090613050d060c080f13020f01110a0b06130204030210050a03060e0408030a0b04020903120f07060e06220201050703030e0c 82
    0x1104050f50007160050301c0a030400c00d0800700c1101c0000c0c143d9414107005a61480880141402d5458590218000c4d003405000980d55a4041c00c000e565950701c40303007910025260040004182d4158401d6071401c448941c0a5403915810340100030403034006c1e0103850080c4461003000101c59548110700352900e845100c2c082452904204040c004900050941d030100c5180310801082508904030a84596811034940d4084040e01c001241e0280604141048612400100070203100790301491500c030340300403107100200b0300041e42008241c5c002c61000a420811000c04064a02e004001030004070806113000a111556560344071418407003521f06950703042c000014000f40048070301070a0b120020a460a40c0382056000c0829a24404040c12004100740480c06450400824086505250b005402881600c8007040040e882d41f8050702d40100c03400543c01340803052101d0307884900003660161511824000945c600380c001e405041505503aa004a240d01801070380c0d200000c801c031100c2c3c4204101c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 165659982 1250 165658732 165658751
    0x6020706020c090f010312020a06110c010614010818100c0905040b0a14013605030d030c02070501031802090114040e0f0c0103020c2a0108240114040e0109 68
    0x90516054404082c083d528070010010161301d41c001480c1100d9018a02c40200782c42048101d0130201c44c030800400581c10030090194004100000d01101c4040c00004c0000310b40e01c15403a031060310901140e50105d17400d80001401c6402e070100418140001e0f0b4140c0e41403004001c202e804a800154030180450210002406541460300c1151a01741007500d501084504003035070035015000e440e01c498108035110844c00c00e02200c2040001e6100c10349c1481c004900f0703110702c80424800707141c0529402071040d0b161684480d03105e80621000400c80b50080e14240c2d0400e401100a0000204608810300c00d4248a200588810406500a14a0503401504640d000c0104001d65441d43c42c0100d169010854600c500200481c8201e5000c40900b0f00503540d034104264241040c0781c10115000e0441c144050601e0241d00212020f41240243d840c000c8958844c0c0c102c0c80c02d40b0241d80d01d0050000500c031400c0c03040d4001d080ca001760540007030859045c5640c42c0720072180030400340c122080150700c0303104d0304 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 165661232 1250 165659982 165659987
    0x5010204180504020a09020a0c06020c0714030312060f0d053906030f1f08100b0a1203080a0e16031a040203060c450102160b03040501020d0606020706 66
    0x688070041001000c0c0403a0a003900019032085d000c4c0101400c0c60b600040e01d003503450287c01c00d4034405610000540d120102c0c0c4034a1515104a841f03201c0d0802900c1b0b00e20301d5945008002c4070b680306414190054562181c40c10710440300b0a0405098000da44000724401242c01001402c000c03030030010002180c0421500d01d01e4a50401440d1500d2680780c00b8801a003130395840d03007601d1b4072401221500400b80d41d04809d0700704454902004000e903565401c8041052140450200d504681c40c2506002010400c81440b0f071020240c4079281850340042c02100002c2c1c400d42000f6000300d0803110104811940d02000c0d400c000d0403901c12207050b40344200400800c4941c078007240700040340c030070080034604d4190086a29000018440c1c4403410000036401d028025060f00d0840c58a80c601190b40c3c3d624a000190b090a100c1c8420b10034a511010705880066200180311203c0c812480120b400c0c42d841c24140301c505400c05081140d55540920021045a41d0b41c81144c2c01045694020103002d40b070414007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 165662482 1250 165661232 165661259
    0x20a06110a020c0901150e04110a0908010b01090b12041104020c0d09080109030206010510031e0207061d030d0209040e060c04051003050108030f0708070b0408031f0806131703010305010204 83
    0xa540c010600e0fa001040240406d1101d01c24040035824000d02c90b206a90009008205c1801c00d6120b401012520219180d4070804130011348416600800084503e2801524040d50601c2001c0f0444c070304002d40542c091104190070780003442101d0804a1700030906c0005e090303800c114400c2c4825071020509491059004084e4002462207070300800803038115450007911428140280b501030804603081d208010300c258010086900b00d1102da56043c0550000d43c4040d40c00980c098030304030304004d401e4000e040b00c200c0565014902000071803412035240001400ba410050b441948141d5462488015507414001d03a07102d0100c040941d9500c0381007104000b00e01c1490380400c810540303071000501c0300342400000c40d4049040001e0450300d50400345401000341c07240c058001c00d05105d00060204000b03015000e035006d05901c4681c443c44506107801d180d440c503406e218198050b4413a202169000c03c10008600606015107c0d84160405150800d00c46510a0f401114035030350001d41008a1401000c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 165663732 1250 165662482 165662503
    0xb0a0b091014070f0516030b18150613020c0109080408120315090a020c01021201032117060a0503070806150f01020c0909160305010b09070309150b01020a06110a02 72
    0x50240d030500b03540c0400031203400743c0314006140381c81c8180d401d0144442000141c0480c50fa008840b404140c581c42c1100c403250f07045e42c41000c0c603084101826144a404140d501107545203d120190703540c1c8180403c0008140152040c2c4056804c100b50300e00d4403003e010713074005580a140d020303560714a01581c0c02d00c1c000085031a840000f8080c002d12801411405900c180c1850460310105149c444064450081c840c4091081c9950310000e1694000340c000c0c03070040d04890050b1034048403603074001801441c07001d0204e018400100380140c80c1900950b001709a41d08010f000d485506c2482c1c4600c0400e1500310950400c03541076000004000405000421907148000c0507a18111507242c07110020b0b60300d40c41044110300c20491400000c40104080052101040b4020301044071107a407410114004d07d005031102e80a650404001000c4a01a006c0c0d507038801d500c002c0010744003c4e1300401c48010641c240d2002c0c1180034480c200390116500c5c2c010b00707202c40c0004001c40d69070384d840720300649000071185 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 165664982 1250 165663732 165663737
    0x3021506120a06020c0309040608011a0603091207060f02040609090e01020a0503130f02040c09090f0213060507030903051605030105061008130f020a0305150a09050a060b0102010b0a0b0910 83
    0x7924226521070104035031400301da002e140507032940b1040c2201c50642c0155004560424504000044c003503005400155017080403042220b14410820706010a9110031100f00ca441e07844401c42e0300d000c007107c5000b000e030a4019840000d4118200c080d52080e071740a07512100005003094818028059141f0070b50701c404079100021464400c40080203041800b00502290b0030084c603088020500142035855a0490343c000d01c2088102c4001c1406040340701e1714051081e6807440c02c55001d42c09007c600c00c6031158444115031000a528083e4200e4031507001e0b4000b101001100360380080000c1003002005510403011555104503801c00f820b02d421242c00404842c80f4001c042d6030207120941004805400201e109030701c455050050814590300509100000d4100036600c07000410302c203000c505400c842c1040719500340142c5800b83d000c000d4490740c4c0e5024050750010034496000803010b5103c114200313411700010880d0f454180c0000c001c1101740c0d218280d09040046c9010103407410b000344451802690 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 165666232 1250 165664982 165664999
    0x705090a0b0a09180e06010f15020c030601290310320f0d0b0903030609090607050f03071b060905010506030327010e060a090510090506120c041203021506 68
    0x60401052064940b14404c0041c2240c3c0030038504c0e01582c0c02c45810851a0011150696500d0442314100303d17044c0301c0c4a0905011400e00128148042030b01840c0c1d80009008007050390803d4101d5001080070200502d115401c1c41e811444030200c48041d6100c1c4c4a86002d28003c9840c1590141095040880321004c42d449141a001c01c00c0c1600124003d22005440c60789070034a030358000c03840c80c2c50420806422a00039604100124400100031441040c1c2034400010305d84690348000d035181025502a808503a00b880f16020844040c005103a00450f03601d06414822091480c1c0220404018400d4503115101c00441080c40024013a264100a090b0f000b5890702c074004100100d1411001401d2950300700303d02490303010340e105101d10082600000d01141d0f44050810000d0034042c813074401e00703000d031100315008076220b4010340350042202d5001d0140c0b4584072a460b001b0b21490340051240103050018800805d211507804c10385200d40d4440d800810700e000d448844420060300003480188100d101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 165667482 1250 165666232 165666247
    0xb011b080d0e011806021e0c03180625020316140607020607050115180207021e0301061503020a110118020111030d050a14070c030206070c02060904050705090a0b 71
    0x40c422900d1200c12103030001405600c01407100d014042c0b5800c3c01c1209100e549642083c48030340d500902940d540da0101741c0f46580c83c0d25036442140201080210315800612003040c80080550042c00b001c140244240d15194510b01e181806030390640c01c222050403854441400c50500300200825064481000c00c501440e1003c418403050007011514040c03800403a1110441d140c0a003a100810f40c410001d002454014290400c07070740a032310664a01002100d01a0b11396940392003259030564014002403181e5480c0404e01c421991040409500f40d03594000014060700e101048502d0b100c807031381e4003690b6034000240003001540302c04421f0b0156490104810b00e8100058020703030060f5428200240e400c2c12202d03059046000d901c459804043c202070070003c00c6440303544140c548800c01c03140141d103a1911102220b4003124070710020003581c40745001c15181d0340140d070701c40306451000301030381e14041d82e070300114050303900c2510480085071010640145601c0e0002003440a081c0d14080c090414a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 165668732 1250 165667482 165667493
    0xa0507120c0b16020708010501060804031d01050d18021e0a0608010e0402121615080a020a0c150b030102190201050c07150c0c120c0c060314010308090d020a03060b011b 74
    0x405415403041003003d009460b070040c0207121141c01007107804002c10407903a40c0c10003c0d101e484100c4040300090a041c3e00d110a501035407010400070b65041c1e5409040000c13200000d0024080c2901034170886540c000c60100680d41c1000500c0c01080d0401d5035403090482e40184031220070560082400c0c480800010300030341c15840e0190f41d2003901115102d0a5642074104242010500b40c101c064202c080c0001141c00314000c07080210544890b5515002907480307480c0340d8201d028682c18030000079468004080416002d242c2580c0724440d01d140041e20061800010742241d00880b1100c0d90004100600302c0c40703580a11406900c109000f500c1407038100f01c0e41c3c2d0140c8500700d07400c00340340b00c55941c050590014451920145480d0780480e11076259001c0000160061181070000c4804c40624500450080d04c82d00540c52164511030794000c00d13908550720181160440c15545420000700100000965600742c0b52000650003110001101c58a9200051000340300782d410036000c880240001c00000d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 165669982 1250 165668732 165668753
    0x317040602060c0f120403020601150e0d110301020c0d030b1f0813030207031e0b0105041a06163807050a180e180f0703020303030c0307050f0a0507120c 67
    0x1249003070f1983d03130365011040d2041c0c18054138060030030b55213031a0204010150000f0f0010305031100b06002003d40c113503200003143e6001424190a410132040c800e00710002c0d42e10145031802040050000d4200211090726134500024071a07640002600c8040401c007a08101d80c0c5151441c000d01011103105208000c003411017240544466444144d40f588801894824001c070f40142d030740140030556252140035120091207500000307954510112000080a140c9071042e1a041340b501c100c12850b10f0070503c204201604858072408102041000c0c07800003e989140c205044694131488080800b0030948072040044246843c1401d0080a000c2c0490103400c801a0740400030a4542400d1180c003001d8030312020183c0d503002c000801041001c0c0310640000480000801449400710342c401140401807698446941c400030b07400d9042040400c24184562000b513034065802d04000b0314046a20a0b4003040b079000000d00d030b00088009c21020100034030107004518070744080c0740140179036425032510028070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 165671232 1250 165669982 165669991
    0xf0d0203250f080f03270604090c0f18050d060e030d020a09060e0a0504020c0f010f0f0b1c0602090114120601091e060509030c0a120b18210c0115031704060206 70
    0x25420424102d11a00f60a2000306d03208018120b5525541c0d1008500043c10185407100d0118000c003c090002074030484c42d004038240c1650b18140550319141c140507007007800c00c909550f11925811502d00f1803000700002c00702c0450210700142c0c0c55000c040002c00c0507086402040070403ca81107034003119a101120340003a1141118010780c3c802c2c0c28107005203440480c000306815075080240294505034668003402d00134200c080d040c0a800d812804024600c40d015042c2060405d0701f4030f03c0d80111b07495901078014180181080601c4c0d16141b8000103803904000d14a070411030180042041c0795038810100c400501d00c7c2c1c000780b82d00800000082c0d1f103000d841d01841003041404109482e0a55081020640190010744400031840e00ca005005041003076900c291442c10002002c11044030014080306446170340d05020701305070711042c0fa44110030202e00820072840401172024081030709007072280c0c0c4000009450503840d0039185140070941200441c0528030b80443c180001c0103400d8021484030340c003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 165672482 1250 165671232 165671257
    0x40e0415060302031509011d060a050403020118080406090603020a0e04051b0414041128020307060c050d050109020a02030d090807060903020303070806040b0f0d0203250f080f03 78
    0x100e01401480310091100340d0010354544140314031490004d0f24005400d00851141c0000c0c0045008400101090b4244601c861a55800031001650382011a409181c116201c4c0c8004554207502009165411210b0b000c207840c02d1000003004c11002c4d810000c030000a10480c1402d5040c880140070141200004201c5140540c0d01c0b5000031f20089240d14480d50800c0c610350425442d030344c030380e410080700c229204e8150303000d6407a002a2003a0b510300d2505a88e849840320301e01d110101c54041c61903101c41d03445d040c640c0a51106101c61000a1000e000d000d44001d983c1d0341d0140c6a140e00c14420003a5001030707106150080c41001380030421940882200d5a10b003400d140402c50000c280b414051b1440390000c0600f21030f2610540320101640403008500035900c5541e07440705902d0f880704120480d05102c1a0a0740300041c621445d680d42001004c40d1740940c0000d05035600032401911142d20021000140c1650344d4501c101401003101c600840c1d00a8051500104803407840b0902d240d075a4442d4030300d65501c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 165673732 1250 165672482 165672503
    0x7030501031505041401050c040306200f1e1c2f0a09120303020304050709051014010210052805040c0608220b010e010803031e091005010806060312040e04 68
    0xb0302000b02045c05410500c00001c00841c642449010003e0700301d4002180c13924244040f420401c0b5071404101d800595890009140c20030f000e00030b0781141d200344192501740000400c086090900440600907180000701221580c0c2030400142c411a4645001d080f1224102407440080c088031060b03031001807100201169071105076540a4075454500c2e407040e07588080b14003111040540c590043d5014a1040040b141d003103407201402c1c01039070800c46242c41c810074090000c108543c1c00301c0c800c404030f80042c015070b1100e04500d035002c41030750001c580198001d907002c403050312500101d18505401103020202003106080a0baa42100008948140da042211034408100280c10302054607035002440c040c2c0a410351801d140c41406d901c42442420010092034000007421a03000c400c8a1044e10000c40701881c540179642100516800940080e0b0f061150340d40b080b185c0c40081c81414044c18040000b0081ca281080800d8900140500c4410115005100400c02040f00e08032441c0c010741e0240b070601 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 165674982 1250 165673732 165673741
    0x5060601120b0a0b04031122021303140d02070b0906090405150303040303080108190f03180f0b2206020601060f12050a020703120204050a06121b02030a0807030501031505 75
    0xd0107440c501084540c0110020070000742c02613104010000c403482054038200c00e001c41c004106112000c0c6000c0340348194201c2d240d00c0390120726402803000c0300d880d205007007100307031281c07a0040c031404030390320000c1164009092201050b0b0108640001001d03c010024604266240414202d00035102c3c0c6034080e644503400b207428000152150700c0c4d642009412641c42d180d40f801d0040c0740550a10400c0030780d00840d440c2854a0304403440036510280c026075007078507010080e070f0200d40c0260116070301c9040003050f01c00842c091a00e51382d103070000c00702540e1140d281c8101c1c140506410641c400c0d1004000c2c00e0440400c802900270545504542c15802c044101003103002d02980d9500b06000c440400301d103070408000d0011915400390485a009540e900801010b00611104904c0707940102580107000070000c001c09071195103805005080410049071000d540039984051204280d8034401680001c00c2d044111a40005420307402401481d0502c4954555215040f0640501d1141206140c440c400903 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 165676232 1250 165674982 165675017
    0x30a1b26150d02030f15040c0e010f1e081b041a0913170304030c050f0a05100902120102120f0903040302060f09041401080619020f0301050d17031302040501060c05060601 75
    0x192185c115081554076220b056600e0308003040007214200c0c0c2d403000e079402c046030107a0090078241c182c0f0f00c4611507000182c10503c0490950103480d0a204001c1c4203110003081c040740911400415600302d00c00c00e80c140c0d60341030422060b0b90442000c01454044001d103150b540e520f4081041c1c0040c200320741184800c0d90307818440d4418a541c0380e17a000420000041c03004155218090250f9140942d0070344d44828491104107442d52024800070b0b100b80d0100300301160082c0c0b250b001540d00fa2005001c2c8010498403940203083ea00082400e02c0d0042e041c10401c084444c2408003141e00c9803c0c14040c5140c14250b0380051600c0c0600710b1030070041e01010a06450903100d907070000c100c440d9103040c1d036070b03596942e0300d260765440d8400ca80450700d400050308914600c040d00c2c000d1f80c012600e400c4e051800d50782407000344a8440e1040801b0b4903000c10300c91002c40204444001540102e284640c000f049070007a00500c419900181c2c010001c01c00c040c40c510005c41d40102e81c240d00550709103440c0c8003c1c14125000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 165677482 1250 165676232 165676243
    0x6050705040f080c09060301050f061513030b011401020a0c060e04090b0421020309010e0907180806010f12030206062e0201050603010c0e01021002030a1b26150d0203 73
    0x3880d509202c0c400b140d00030000800b201181012150807001b40d813480c040c1030a0b241c0541d101600405000d020440d14030300301082040c441e1000d410b8906101d1101c00c152000903840d44117848807140c0784018000c03840d800d007080711124801e00007004000c04981d1055151541840303003904011054400110030341d116009440c1c643c2d081820110782c1d040c01d041110448014a40c15820071041d50b514030051800401030390305101058450051218580040c040200c84c01480b07001000758a02a0041d8010500789c10005072045000a280642c141308a012000140c0c0e00040900c45690f001440040d81c0005c03003543c800000d031038441c0344c0c0c1c1d1104c0f85648003141d545580e0010340b41d0b82501c80b581c0ca50543c00144030700f404600900681494030380079688946c01445590041e044038401040d081002d80003190010440f103000680e0900d480d09020401c0300b20b8140000045400b00c082d8150f49241120071070512210340079116500f0b00200204800c84844903080c081d4241d94030150655070144030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 165678732 1250 165677482 165677489
    0x30509030d0e01021201050108100314010207080406020a0507050102070f14030c06031302090a0b01050301170309090408030109051006021e01060807030c0f0b04260c0a060305180a08070605070504 86
    0x505000c034118094100b8080c1d0403403400d1005c503010340000000c0942c481c1c00310600662411034030605650841c3c64501031031a10052810b5159001c00c0a280003460210050006001c590f000d09001500c5280c0b642c240b03001a40003504651100b8014030082c0d400c56034a0702203d511610007224406400c011900701000228820f90042000c01004441c0300001c103100380d86072086440a1555071000c00c1c0000701c0d850010b030740d0700042041c40140044090002c2520360f143c210000c4a0420003e640056034800046400300d4404401000420040015014042d044992010210280790510500035900c50380002410195540402c0c480d8000d0400c0d0b00c0000035003541c0e4196103210340c4909112a501b0790030b2245604d010b00501c800100c00c01e107c0c1c152010b0f01c11884294448013610140c007050060401e02586650080142e0340c0741507554004200001c0074141c03800b20340791400301503001c00e03401101c0c80c80000c1c0c0c00006103000004d840c0380c2194000b81c2c0c0031100040d2501c070710f00c0446440c001d0b0740 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 165679982 1250 165678732 165678757
    0x180c030215031e2a1917010308031f15080604020a08150622141807120f0c020c010e030a0213090303021b071802040b07020f040f021b070807030b0703050903 69
    0xa40421382c9182d20390013800c54510003521340c2c2d4007100a42c0704950b4000b01010b0310040d628103c00510029945400568200031190004a40028081e0503641d040c0304540c01580341a0140020020301030300802082c2c2e00500448045082c07242072400034180e128010100480a813411130540c00c544e0b240310580341000f8045144a440100309c0000210052280c0115418031110f881415100c1c901015005411803155082c0c108907115042c09556001e00703200001d503040e13150b02403504000800d115000200d68158010001494100e00140c0781c1071a002e4644c0c040e0300042c80d9600540c89509103514901c040c0200054042400d040c110024003c40f08204503202c0c004020b40520040080d00c202628002d18810828190041c054070483c03145204070007407031105100950152616002403014014041d2020980c1280c5610290481e80050407100007828640e940080c03c0c08208001000385c04c440f0700034080b0307500790303100c030180340c04020050810552a83d0008840035014801c1d940c03003000d0103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 165681232 1250 165679982 165680041
    0x4020d061d06040b0622020a05040b07060b09090d020d08091c022401050f040905010b04050c070516060507021201061a181f0f0201180c030215031e 65
    0x2845a03603110300c419681911803e0000c4045496480d101d1254100e07509400381000c203001b6030070380c81e001035004071510b8018407074140000100601d8000050503400d2103000002807a0102008000c1490006082204190700c03042441d60100c4d00043d02000f070280d80d0400b845107550b428041c9142042e14008a82d048120303800408030796400240c0b40307522405011403005501e144150b5402061400d21032079034006c013501c5896002c1e0900e54007a84900d40140700103c0c1e0600038201140681d48140c60203544e106c80002c1030018840c0a02144002140351140c01d442d661030100014158040c141d8042d1080c801101c4448081c6000d6018800901050f22034250b03550b0607032451243d40e005400c0f1191b24800d80304c1c0c01021807030841681c180070203080d0030101200b40c502c1c004980d0030210704050b0f415590b03035103100c4145401450b0407020140c45a110000d81e6030462041c40301c08900d4902c8498001c01c107000340146400c1c0c0b0760266020903003400b402c44c800d94440e065030305e000221032414034504560 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 165682482 1250 165681232 165681281
    0x4060311091302281a04030b070c1208180d12060f0b07030806030a060e010c0306150206040303020c030408060a090c06080c250206180f0d02060f0a020102040512010e16030b04020d06 80
    0xc5d003001e070003202c1c002c6000040690300d10b00c0c140c40405600200401d001101140c4c0411180038545032500502480603a5050f5503803810420b182c400031581c500040f0380c80d200309284602d1940500400303802108030f60a03089140c941561094041e2040040c00c0c080448001203803a281000b68250281d0014001c0c0041102c00d80054001d00840c2d000800207800e040e004a1a108664841c0051b066254000c203084c2d0b580b924101c3c002d40154407600e00d50b0000700300000c0c0c9035900300020f5010300d01049002907000c00c90f10b04030803500320795888034080c4150b40f8100b2a150452109030344064040c8600038040021344a2078900b0200480d00095110b480402d940440304414001c100c02580255505030f128880c040401004901030300e0001e42c002d0f010059040741d000c1d00c102038190462680005810f00751541c0000b8000326818031300450300c0c1e41d00c0c0141c3d0280d25080000801d00004101070880305030460301c40c04051203000300f001c3d001d1a8100001c80800256a2120204040040740300b09100d45 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 165683732 1250 165682482 165682529
    0x305090a0f030605060616060e0304050d050304050a080c030a0305070203070b0301061205090f03160c050a15090902041805070210150303090b0f1b0c0406031109130228 74
    0x4060105842031803411002920321b0030600304540401c0c198850035a4010707040d0362954090300c1c11100300d0034036010a200001c0c058882c0001191854451000b45885900f007009105094030b15034031440c1d0950000600031915100881c00706280741d01407400320f66070f80d51800817901e8100a5031102c220000000000906580d100c1c0006200b80c0c44441c040c0055110240e10030f9030f074614194032040e01d80040003407055050b030560002e64481e1182c0000300b14241e40d2400034003162800da100e004600b40c0305403540302e080e5001d005a40504a40c038400c42c03c2070304125078101e04003200509003005030b036190b0215000a00801400c525000307007041c140903005c143c00901c0113000070b034441203010035032000740460322903188000d4032a80b6010011403800d101420b016117040b85840700f6255100d000d180c0981c0c0142d100d5000d4440514020754004280c01c044006001030004010030544070394001d4500a401651251040240e120300e0b8910403c1c03540348640c098808040035408480d0307002d0f2000400c211841c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 165684982 1250 165683732 165683759
    0x200c0a15031112041a060f060d0902090109020a11060408030f0406020d0c050d0b04060b071212050901052205060411060409060311030d050f030109021c09030815010f0207050d0305090a 81
    0xa05c0f0303510001000000e5600300a000e4020707204143c0c4106103581c500214184580940540f10b08100d0200310500c03d6000f041c0344a0080c0c010074031032500019041c4a140c1c00843c0d40d6074064030800140401e203440d07250b804040c0405000c085541030b207140420240802501030b115481c480440c208080d440c000006031481e80145560540542061420b1402d8980791044208407224400c01a24044e03003a6100c3d2140800023000c2c801303021007498141042400c91007842d00c5020740030000100e90424030018500644003824900004000d00b00d2840020030224806030444d40c8441080c4440f00d4070300001c1c0d01d600407900700e0113581d8980f850000c2403001c48440c49660f210260f044d50800c0d0f4002804440c288100315140030036000800c01040200c1e1694001e0160041600519100e41d106003403800a890345c01806800040407100ac0c1300e0340c0c04055511040c00300f02400c00c2480e200e0041d1000c1d4588003144141c80c4504000c003800010316010360210340386111b0082016920681341c239410f0306d110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 165686232 1250 165684982 165684991
    0xc09040e07090f060506070215070b0109020d0b090403051204062403150b151c02030a2a0f0e060f0c1b04150302090403030608010507200c0a15031112 66
    0x95041507680c680054441c031900099030070191041d842e06919230280506411000d40a040b00300c4100140744c08290426409800380c00840e40260341d138000040c550040d1512201040d224000e88414040025003040c101d5440d001c405610a0550390740d414018014180907031608081080b441d61108100c00500080c0c081d2449170740006400d8907145000300803541c0d54110940c02101c101040030203480100e029002150356004011b00a081c50681d110503a002900c00c440c00c9074a48031805401160050754610300659122918004585580d005241e03a24254421051200400080403a51035600446142c03a60955145555813000c1c21400e55504c0c036a4161000d1604c1d560546150b868a4010078407070074024211411018216020055040005801203007071503650407001030105030038002c4904c200d04540b02d998180041c4403100b0507000702c3d8540940d164100c3d410320030b541d94465003588142d9041281900c4544188601079004122095801032440b0002c034031a103441e40e410120b203202c2c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 165687482 1250 165686232 165686249
    0x3231509010e090604020d0501020f07081c0506090105061605010905070f0b0301030203120c01181b050604030c121509060504140a11060f0706050c0301050a0f0317030c09040e07 78
    0x1680c1c1d071400c00280307400c82501c0510440c1c010300007007005490490216400d01d07000714001031500c4015134203d02c01341c0c030cc0c800407030390100007064000a510142003001d0107240c00c5071003886540780c40e800241e49044140a41442044040349841488008056041009a10038020003402942e4140159174010070721403008130300c0104d640480c01820310b400781d034103c0b81e010b030007055046003a03119100550008503581c8070546da5810750700b80e202025024410701ca03000e92480220381e0900f0080c8800c159150b08264080c060401042000071101e01c415070807200d05000c4030454142625007000f0b21444050002c42e468201641301d0280111a441140140c1c0b040d2000180701090310b485645914180d080545031103140303451802103040c040300900c0000c03c450609403601400d640d401c801c40741c044e070300b030f5004040105c0148030301d003080200d0b44050013850035002096891540d400301e0008620000c1c10801c00c001c008510181100e400352080d8040050040c0200040114110341d642c60f28410901d6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 165688732 1250 165687482 165687499
    0xa0e07060207210201030e0607081b0406020703060902010c0f081215060901030b010207092a14030a090f200118080a0b0405030d0501120c080d050703032315 69
    0x100300c0e0002500c0d00840c0d10940c40391145840500c1c14007071000800c00d09a050549542001c030745c00100303004603441945a511004c034035003040c03500b401c0607029540344221110700800081c400c0303e030005607500440f58000400f050200c0c8520040b1444041180e0051100214040d07150030400003501a01c0141800c84605c041583c800220300501030580c18403580009040000704180c1d482a08549464041801120402aa00e140c114121009084611140307502c040480303003401c07400d00ca280d0107810301d031501c103052480c12100c80f0f03003070300c006001400c003150340d000244200300446022035071054102c41e80c0342c000c5090f001c2d42c000d00d61008441c10300154090350b0b142d03905200400440242c405440040c14200c10329a10f0003202c40c00134000390707a140310902c68503101160740d00816018000180424420300e541d450401000241904043c00507007001c1002d413080c0307500505892905405142c00301d9594003642c884101210981441d40c100307100007040020740c11030814042c20014080e1000320 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 165689982 1250 165688732 165688739
    0x406050d11030f0612010e100906050903090a15031b0f0f03060321050f0a090e010803040308090904060f09061d030309030a031523090f06090601050c030c01050a0e07 73
    0x10703050302c8111030380e2401998103004100c140c2002103c0a4210750014000540c14685080311464900d11140c1c680d80303240c40d480f00e00c080141c0d9024035a0090301c2d0380000e500f48080317540001e154103001c0c003c1201440103c0b480c003180e6880390700012a54032280054408170b003071940005000503a00f52860780412000d10074051410f120388902000c89400031b009070412580b0100d64106083c40c03803010000c00805000d1015010030040041c802c0c085143c0710100034038a000b030898032004050b4000c0f16560024401000403a05030b60489643c103808441d0b0703010b0f50399140f411100170700c8615418112180740c207002404004140c2d01402c4150411542100c0101c40001201d540b07100480d00354040d90014031031080310600a80000e541c0e108058415602291200d810304401d003214141c002825600d4105e011007804d003140d00603009601e82c5003400c12032804401107a901c42000d041141002030000c0c10107500d01091058410301c084150003400301d0b0404004103009020b500000d100303640241c11000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 165691232 1250 165689982 165690011
    0x13060c0e03120f0f030c070b070c050709090804080303040c0503011b021005101206050f0c09010c1202100204091a09040506010915050a18061a0405040e120406050d 72
    0x14084660041c001d100307410014258903201c2c1c11540ca070420303101c42482000b02080072603000d14030803402d84101c070362908440d0a1000009001030100000e000c00c40d28610003094010a880d0107a900850b400b00c1d1030302031890050203a01c21035014140b10301020040c4410400e000c00d0303600803070350100c0080c0012107411a017001d000088040307100240e03106102c02c0190f05010f401c801d42c840341c40184180305230750b140e0002c002000340f40030441c1c1e1140c0c0c0c0c0c020003174004661811380741c0018030751510505001910002070442d054062018100e4110200d1100b440d620800011502c61000b1005644443c1d6901c0c5070000f6000141002c007001c42041d8191790702e414001c2c04a0312a03a00300004200a03482e200d1110001c160307419000008030482000403400e51a5112000b00402103c0c03070310714407804043d00080c2202c203103400080c9a007015031001c00c400c4900d0410fa50941b03004540016000102003031540c070303110160f071000100040126000541c0e50300080940091400002e00b4050880400c204 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 165692482 1250 165691232 165691247
    0x812070e01020705010206072f031303120305430903051203100b033403180209070e240901090b0a020d0309050a0203010f02030a0f05060609042313060c 67
    0x9508c0064002040402d0480803041c0c142c001090030240c61a451000304911411503110b2100a441c80528036410010032411004080800b04189000c21090600b10509030455424001184c400f1141c0501e0381c00c104441c9408038507901820303003042010210300c000036200340c001e88002d40b2580110a888004c010b42d5408a03071044021000c01c022050416a01381055000904040c0f640200908000790290341134003640e152684040c01e451602c002c045009054441244140d0400c40900003000010780b01e90304007942045507400c0c40c1428083d10030105400840c0c000c00d01095000000114a201401d28000c015440c020307a6031481032501c0e180c0d800d440d880307496144801640004030a0050724071a40c0f00c200c02c0ea01c100141c0320f060f245078002a080d0743c0700c1d03205450300f90b6000052052841492040e03003100d1011007405e01841c80c0c158000782d003500480158900682d1680845403c00802c454402c1004042e4101d4800c42c1c1090381001c0c040300411081140e40710310380b1450702c0410303020b00c10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 165693732 1250 165692482 165692491
    0x23010f060207050d1101200111040905090a170901030b040f0b0f0303030112081b010e0f010b030d02030403110d080d0b03010b0108010302060a0c03020709020417070b0a0801030f0812070e01020705010206 89
    0x5055441817000044071840960b050303600ca582c0030203490100703000081c00360308047c0c2d841007507154032581001d4544086030400b4103900c041d60b001c10f00d0f070800140c1544514640f10709038044152113216450050b00a072800302131040c0e1140ca05000300800754225800f00d4110744043d24240039000440c1c1c10315607644001e000e204418600000a0700020310000020b0010200b01c03080e00c52155001c8a110b03003075079141d01e05400190002d40300e55030300d410b00748260f41702c0c0708045000302a12108003002944a2140d0b00001c0c4c2148401150840252169240050444d0744000a40c5ea1009100000c400a0905a611903c00d5003010350341a499803180c24981e059940007808030346405518401030381c94503001c0303d0850550040b4000081d500e18544090401005510b62240020500e0079001d420300c0e0716074200881e0941e0a000e604801c2e640481041d041d25800600d038000c00072581000c1400f40990040904120210302c100105180e2201d01c8424071842a001c60b0074641c0c9a00043e40c03951821107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 165694982 1250 165693732 165693743
    0x9030304030f060b060706050f250513030b0403050322020604090f0f0e0f07090c0c080d060b1c0c02011103071209020303031e09070609050423010f060207050d 70
    0x14030100d80200b107501c01d020701c1400c000403102d54120129030690801c800545160ba560070030404007000c0113008039400171800504148410700b4014050040450f440500c04011780030584490000350144141d000c6c54102503103211501d07113440e00400d43c2d0f1044810318102c40404c5014288203805480309441181e0042221b8142420001d01300000c00580c4000ca181070703200c4070b240c02a08810300c299002c0001410150030300b049040401407810005603c010380f014600081c0411155110100340c02c00d40d0f10980d019550540c00e001c410240c00f0070342060003200b200042060041c0190070252103005140d034018400b000b4051410389c04c070341018410b400c84000c100002400c5074407446500b02c041030600c0d8001030032003030780c1c0200340b441d0000c8680e01010b0300c20041e40d44120101180403a4050303588001880083e090071402402c807a80c501c51640076503100e04611448641030b1516042004140b0482c100c25a501c854031806410300d0b1180a0141c014840e0107d0b550424500300c5a00a8018 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 165696232 1250 165694982 165694987
    0x2040504061e020f1e160b070f050c0601050d0201020a151a030610050105090411070b040209091c0309031e030b01080901060605030c07080408190201020d0f0206160908100203090111090303 83
    0xb08040700e140c2c2c0b011040b40c05c074040208070b48078064030801d0014030818001c1e451074582c0d280804019181402c903000c004107015041c400ea0a00000024030a41520026113002241c420700d840140c2c506041120000d001c5044030100011007481070b031124000b420b120607400e0b03042e0081014907842e45010745107004840d030840400d000d154041d8004103680341c00078000041e0844009550f494603008800100e07070072429030080c0400d6140504c100c2d9040448a40640340c11103c580301c0e0b00a900704400c0c1c6030141a16880342006060050089001c81d121811191945140c0400002c004000b1480480d010403034260124030701c408141320701825602c0546406146841e14000340c051600030b000100d441e40b004000104000005000312076031100e5858403000214050310000e0f080000e003264000c100019000b80104013940011100d40000d2004d08810300242900d80c106c480d165560003259191041c5104400c00c00c4655006502c10040ca10080088440c0744800c4941d03481000c504951540c0203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 165697482 1250 165696232 165696247
    0xa0905010e13150e0a1103030a0215070302070210020a050f01110f13080114010914070503060105071b1206060b1801110109020d12030b1f0c050a02040504061e020f 72
    0x10685003600c040e00038402d00d0f031500d9034804407600b514040750601c003060b00840a1003081110006040d205d1800450140d8182085404001e50b146035100d0010b030604003020100d50203a0013a811070704002d401411802120840741d001a58544001000320b17400e1060603400440e400040c03007804004400201c4251404070006a850459004850941c42002c110f070000901402d0920440d030000c0325040f0150300c0d07076250950b51400c41c0c0605000b03500f41803002c0c040000c5d29070b00c041200c1d845002400d0849d100d031164149282c0200d079140348442d90342881c45021401c0e001c00320f05140070301d100d0701090009a445070320030f500c20f024211002c0308400d00c09610b40810f41c0185807179456410007400009117448150005000f945010200b598400014240c114855a0500800d40140400e07507179802c001d8070a0511007680191102c4030002c21500f01401030400c0818804101d280fa00104240018201070408000500703001108010034030032184604515512030082e514403141900e030003400d0921 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 165698732 1250 165697482 165697501
    0x30e0601060f0207330309080a030203040602071220070b040501081e0406020918060d1e0206030c030105041503030f081b0703031e02070b04020f0414090a020a0905010e 74
    0x42d4841c9410a6000728407010400720740641c40d1160780200048159040b82007504004040d46010b481e8108060070451000302142040c4d04990f000c42162400607525505c0e414007000a0080040040805402e64104442d0503071294030070b503d1040400d41d0f0a0340b040d20a005952703ca4580c822401c50070001d00042000350b00440c4002c0d030000081404a0f14490b68101e400c680c00c1045504031740640c1c0c00302d6600081d0804800310700012500808019440c20100c000442140072108001d01c1c1d6500e04080a0600c1410b00826000590240085490307003411094098250404d000d014011032524141900720400381424008032501a2903200108800d00400c032245800200aa002c2205078032010380c082d0101e074002d10402d0301036500000d0717018504c0040399a61032100c2030048143c1c01401000701094120b110160004e50485010f0704440204000c03c0241481a403040c4a1440c284100032106070f0108900c08010301c2110300305007480d142c10350070040720300a0182c030600c44032810005100e80d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 165699982 1250 165698732 165698747
    0x609020c1c0c14070602070609060816030209030a060b1305071b111026100b0c01060b1903110304030804020904020112050106020309121c0f111009050d030e060106 72
    0x41c2103103090851040542c031010000807800c0d03149030300d691243d031082001d150f06100403000760450b4500701c5000b5243c400b0081c001000641801c1e0386151120005190724084e6044844883c0060250750428405d81000c500400f14140981d0080c80902410244070b003ca12130548a4031003501c8500341d4540f820000300070001000d20072640041c00a004080d59540c03400091446001641c5a01038650040c40b00289100c541500b50b013500380c200c00f4000c0b03c82c041d003004010b070ba1054100a80b40c0c141c1081c2c4a015183e15440807840d1900007503815100c03c0b81801a9201007069141401040c403512010b5020307100441d03006e40041c807280c010400515101c840300313804c20700501d00341c2c0c01c2852650000781281d400382c1c428070145c0e00028000c0340790b00b091502803003085601e2003d403042c0035140750b104041e20036205a040130003802180d603100f003600170070341c240140043d001224070315230503050a00000c1016010a40c0c1c548210390700200030780e110380242074049804a0142c03000d6464580d0507181c0d00c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 165701232 1250 165699982 165700033
    0x40f0c052209020403061a0d170a05040b030a09021801030b16030209040c08070e0105040506030711030d060312141602060d23150d03020303160306091802040609020c 73
    0xc8511a41c00900d94502c0d0010300003843c0603146c00a042e032000300c4504680c01160b003042c1d0040360103203c8000495500981038500707103030301d1090b60364070003003104c080702d440c4250b4000c030807204408000c1c803002000700da0005c100306200742d07a407100108080e0300404a412091200800b00c3c054540003800190340c0043e413840315600b50601604240716a030014040c1c4034440c01d094009030103907041155440c0c1c00400400314100c2820906e142c03038107100114543d403200400c94070611140020240c1202c00800403110900c0e0f02400c20032016450f0315120001034040410f1400088010038210b8100e041482254803005108009030100c50399642800340c6a0071440c00c0700140b40c2c0e22409030403400c5440c00045002200d1030300f100350515145e45c0c0c42410000c4060500e024180d008803510000307400104898011200005032040c01c00216400c5015048036080103030400d00f00040c201c440d120a040395200e05200b01c800340241030b01c03010304504a0055004400859000b81400c051006a00740d02c2041c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 165702482 1250 165701232 165701287
    0x1170f06010e0a08250902040b09210d050408010c0e0f040e0c0d08040302040e0c210718051005041107030806060702060309060a050703092315090705040f0c05 70
    0x54944da103107058100b4201c1400d6104413114640aa0310228003030ba8110060319464900710700740740c104032590071036010301d0100e14043e400b44600b05180c5485100e02c0d008a10300903084480c000000900149580c001d4403410106600700070740605c50340d000e42c4024840400190440403010712100400c805030071405951400303030150100300511a1a0f0202c191001e43c010f101c1c081d82c3d10b2071071060108503141075680428903080613100001e1580c03603100c020000310080c00f01103802070000300301504108466100244c40c000708102c48820f0320041e0040340c804c1c0c0b00a8504c40c948c0c1d984000b4030040c0c440205200c54041010810f9000003401080e089420210240503581051710540c0400d4140d84180d9006540b80e100000b0400f1156440c0292070344018503280034084071403607030780303520840095109800c50700c28050030704011540304004500300016001d42d030503c641000307486181c0b41c90380f034028039015a0070310380c0c119400c6038203001d002c200c4501556114940341071070441941412000c2080100c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 165703732 1250 165702482 165702499
    0x6130507030f1b141303080309030f1801170105031c0201110417061807030209130f03030b150301080c04020c030d0f020a0806030c150a050c0f03030601170f06010e 72
    0x90340c850744035000d80070f00115001c955041c81e10b4030180a40c410540e41991140080003000000c4a0b20311400d01225032101c02c8580302d0f01d030401c0c041c1c1903000300c41210014000c0032030701c0d0f03404058075811310801c03810a88480011410314001410054000d014003509540940d9082074014000071004018803120702c00020001d14205405080e90b0050f40f040c0c0441c0c082e0b10303210a10321800d024040c0c0220340b0094071200c000005420944402940c80064031524031500043c0f9000f101d40324081c5801e51214000c11002018540600200300070b00718a80501a8031229412140201044a0607106132100034842c88003410201700295000713214855003070006204500305003459004001c0d00e140c2e105009611544c102c80002c00424004008522aa122410b042240e486055807095090301240d1465540d9050850a5a00d849000b048413250f12a0fa1014011420044065030060304241d80d02d003100055560003403000300701562007400c0010410f01180d030940c01102c24a69480c0041c18030034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 165704982 1250 165703732 165703751
    0x60302120609010507050301060905190308031603050702030c0714010c020a0308040602100b090f2e0302030d050306182706180102130b09030106150215010e0613050703 74
    0x101652810358800c80c05900040c14014085402c3c0512039025070103282041c210b62502c0360040100480c1c0c0b01d0240111003442c0f00440f854840000800903581081079940d5030300700a60002511a843d038000d4000a260001190300c03648040b00b10380408241c0c0b00207000c00b50515a40042c21011b0340110b6061100108090f4010380751404010010740c040c204858079146804800b9090420340d00d5032280c803500d8422a0051603440324000798000d402883e5014241d80c90040945405032400c0c10410040c4924500c002d44a08140c204d005880c429030230b50340b45464080d4190b4040c007041d0f032541e42c40b8942c0c01c0703982a21035900e00c2c1d00d80e02c004a4903080d0f10001041d81c0d800c10903100d400c000f0085030451010003c03903200d8540241c0c000d41c05d0380c0003149000c9055180000308100d5000300320001400054101460383c0940204010307002140c2140960211a0000395841c00700130900c1500780113840000401818440425129040c090a05109030451000d03850080400030402d41c1490781c0c074204107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 165706232 1250 165704982 165704989
    0xc01051003060b1c0b0910181106120402060c150a0506030d021c051c020a0917010c05030c0f1603020f0717120a0908060a022701020c06030a060302 65
    0x114064038958016040050550030401d060f00d940c1d003903a03400764441c00200b01c0549a41008400c05640182c01c0b800300b6200c0c510100d0a0940c540131441c04141480401000550702c12200300c600ca1181c55540442a812000d000c8103010f04d00000d0349586820002401505200008080c0b00c80c40302c06803540c1c40540c1180501da00c1c0196401c0e0341c80c0e0341c2c0b0400c00c60141002c0040640e604068001481c1c0892110a1b228540d44600052000c104c0046050740700340504da11441c01c81c100c0480159210000344500400d41030452160499100725090002500b01e418400c0200400c50b594556155564007d0044150390080c0113144d200402040800700c84a5900801d004c06803003507000d0f03c842d016017140c10703183c621150003140c5000041e00ea4201d20050005517002c0d4802e80c80d02403030300c508907110300b0303206072070580d1000015000c0c50b02000100340c844d50080030f00249502a0f0010140c240002101c0b2a040300d1026016a01c4084802c0240ca0800061070b40500303074402c00b00310b0720b4481c0c0c0030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 165707482 1250 165706232 165706241
    0xa0e060412210f02070309050303030f071416140c12071211090a2a1706030304030804120507090e0606090603190b04060b030a121101060b0315030f0d120509030c01 72
    0x3c009101c1c0d4040380c844101075109418400800301100250b080d8105140248500c0d040500341c130f03041c402c44901840748021044283e41403080301038440c01040080c3d0401d610303000000c14500300107000d40c645024140c03420700450440362407040020070806061401c0c11001559050b001e581d091400301c9540300a0b034408007032600c600c14583d001702d25000111550614480c0e0b0b0500c480440d1140448032681c0380d4000102c0701403110001003240340b500c41c540801e0a6204036080079212703100019003c250f6030035a040c0d02e45268442c070b003102c2040e6640e40007a0101c1d600141888282d8010001148003481c107003120f80e400c03050007403d90743c07029518001d401011102c40c034100d80c1a58200f0802042c0041e5100b04140e1203400d802801c40401c269840fa001001006008414001004600e00580609502c203401038400701440b00c0d620b080c2100c0074445011603580180c03103441040d20b07080f07800c180031526060b00e0a00d900c1d0060410742c3e8240340c1e005001c2c02001c1c8a11072005019002e10341c0c44c01d018 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 165708732 1250 165707482 165707501
    0x120305100f090e0c0108090a020108150406060f02070801050c090d060e030307020c01030506090106081906030515160221070f0c0f0f06090509040201080402010c0b0f0a0e06041221 79
    0x1001445a0841c40f840341420300041d02ca50500001c2e0f03003003100180010602c0d00005509285c091860382d1104e01a69030041525101c5401c5850310902003090358008030300240010140e000c03502044d948400d92400d80d20b08031402e9000c401c060042004900308021080040741c0316040205901015204c094030356082100d601c801030b4801d800711203041d40c0500c502c40d0482c0c000d5800790465810518060200e400181503a040c000c50302803506503107503081c1d000c0c40c0610340c018242c50f1400100c5403131004131001952072899260303e0050061920340009900060030740110030b50031840c520a0503003039941d0404101501c4000100030850700085a52450320040c06800920700001410400403030040d006680280c414800605020712440c2c2d24805100e90050307092801d82d03159030701c61004031440c40c4900300040c01c0300009024032040c0e4441144039489119102c10420044c0104c0c10704c0c9995100c00d44015045000c15003d180300c071403041c40203541078540d801c1d080c00340916051594040342d10252 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 165709982 1250 165708732 165708749
    0x40201021005070306052b02090c1b030711090f010308030901020c0316110108040b040b1003150e160f290c0703020a05010c03171803070b0919120305100f 68
    0x20700c1071006c0c0c504180c180d9144240c8103201c0e042098140f076081ca0300c4850240c068450b44c4441c00064441d81480106d80e00c550700551a105854007140076555aa0803d02d030444104218a10f400300707a040c0750702e80d14402c8407544c800d00703c564615100c2118690000c0c0542d10155001c01c4452050341c0f0400061542a1070107400400b80d40d581d0800130399240342024403504001c0701d6010b0002080ea4841c0494008d41c0040d103000094894003c540d148010903400140319040c00302001d40720110550102c0e81114140065a1000c0d0309100c40003108020350143c52010304030940d00340030400c0c81090791800f4007500e07c080c107134000f400400300c00540c1048080f0320540d8003010050085060817072a00008000070301704010841000d42e03016140da6070303035941c00c0c451400d40300025800c079682c00e01160b681c0f50700400340c03039407101c0e00c0c00d000120b100c04540b441e40f18840d5051503012207503807030b07035070280983c201001c00c102c0c2032125002c0300501030280525111400c4203101080350b14241400c40014040d05 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 165711232 1250 165709982 165709991
    0xe0415050a05060c1b01030b04050106020307060509030a120e071d040c0f0b030606091801060507140d0c03110a0b010e1603050903250f0c03170a170402010210050703 73
    0x8040062806854102c00d001c3d00050007102d0201d40001554211071081c401c04000b2a808040120018003004012135030203805d200000600c66004001448820702a030001d116543d03880b5842e65603445041c5400c1d00080203400e100ea5044c0303090b4064090200c40509031140b0980d5074003d114005e50407072940d030b400c146a00900c403c0080380c04125000303004404a800045207042107200c6a030000500300750140707000180300c1e0115514100304801d0a100c10070040e40e0f13540c5855000f4070a410290b01121136101a1a0030f03800c20740d0000b020840c50a59580711400954141d07800ca4409000ca60286003901c513800500d000100030403041e9006e0504a00d400c406443c00d000a0041c10a242c040e0740141413508080c00700c084030101c200c1d41844051140c050701082c1c60080083c02c620022406803158034140c00c0704d0100000032000400f102c1c007030416103400b64042c007a2410700d4402d103144400070405098940407850b41d11740525a200b801401a10300d2264a45102c0c41503850480310034001075a40d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 165712482 1250 165711232 165711239
    0x1020a08070f090501020c060c0f01050a060f0603020403050c150c07030302240f0402100e03010608010c0f020d170601210501080d11150c190806090a0203040b0601030c0e0415 77
    0x441018092a0150f2a209241c24074000000c2e407248090903000d4000c1030300003512410001c00b0040750246010200c000c000c00d00e0080c2201c801051103019416140311900c0740000c030b50340b103030080d503058a0b000b40280c24004081c42c208a0110300b021004241c1c0c60040c172420121990900004000b107010740c003e40b180b901c64801d024003091403400759400700c0040c9814410b400d021520960b034442d9050320071742c080b000000c10070340e000304801401355072540c20b090b00400c0300c0e00190004002c81c1c803e911849152889580160380f81c012050504001400345502031440d407190303554040e002007040c1400804a24141032000c100b01441000181c0b507a19a00101b041c6c1e801041240c000f9041c03072600000c01c0d1900709141d07441d82030640c00d1507080c0c0c0085c0085500c3c2c454035011603210714002404003451075400c41c1e01418401049580034420389564000a00b00f2005000b00da204991144c1840d0003981c6e10390041d2f00600d4803403440c00c104035244180390300340d40300c1344102081c035080d00f010201d41070b18 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 165713732 1250 165712482 165712487
    0xd06050604050a020412021201061a070b1008101a0603040f0c051e12010b06120a05070c1713051909050c071115090a0608070807020703050d2001020a0807 68
    0x80601a0f20300c0f18410801086290808480200369a038100c5094540e62419030701c4901401090304400f003030104500c140d03510340410308014040b5900c0388484d15126a42c000425100c12400d00c40c04e0682d42100400c00c001d880140e02800c01001105500ca900761900d002003440394100302d9040f03071011384218400c4240014420050001c241c12182c0c040c04d007007408940d111140c900080a805440d230a025211000001c0d00090101e0202405590b124840d02d1000003110b1000e031092105545040e01046119110358603004c03405401c0425001d0340ca0764011103c60560055000d902440c84010002c03d80e0365410400381d41088141007004912400c100000007200d40181c0300c03c20021080000100003140b60765288030a20003181e0710604c81001e800c15090307a1260300c10041e4001e8100e00041f030095008814103001e80450b40d200441e582e6581e505981e24031680c0409006c0394001404844035511400c440c2902c49880e880d0340016804035520f05099801040320380020030700e0882046442c59 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 165714982 1250 165713732 165713741
    0x503040c24031b020d0e030a05010906020318010b010503160e030d120b0108040b040b0405070b07053304060e0f01090501020c0c1f0f05070209160909091e0309050d06050604 76
    0x103c42c1c03001c1460400c4074401030b640b034900740400000c2c4800040d110625030345c140b0100c00c0d8103030028000d0241c08a24074082c0000c0d4011076542c6018030040720b2541c1c040d80b05210f996143c3c0d806840b502d103035840e0300c000845445d4040c00304104104450408050340e460912504216145588410440030070b0580150107507400d444040341008280320030800480e01190741070340c1207034000494001603151410041d00345040c64209507103080c03001503501d0800900107400c000e929080181018111941d07510060780849045501d04041c95032408103000ca03d85e40e0109548030124001c40d4585000c445803103080d15003c040940d103d941c04280c04524480078400d4170416082100c1d000740d151310b01c6000c00070200c940740310320003003007024400c0b05240390040080b03403211500142148482d10b00800c0e00750782030907448802000550447c1000400710300034010390008517401303038424104454620104001949202040d01004450300e00020640c80310140703030b11a180240404546031408106000c10796 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 165716232 1250 165714982 165715001
    0xd020111090604090b0d050601032004090213051510180f030309030f0204060e0f0a060e06180907030c061106010b040b09040903030f051602010b06030609070503040c2403 75
    0x1848200044506640c0d82e00442c3c040d64000c07000018a604010007113414189041c90003002841142c001000384410091030b80707014208440d41c8003140100f00705000c203548422034000d40140ca14161421130303031540d81100b580401075041e1388400781d01890000e8884040406441e01184d012141e90680c0340b0841e03070100241074144400001c1c40c2c1382d60740040000380340e403002511200151190808565964018000421182c00c40486a060200d442034803094103460204509103030680000764050001c1c4440d1180c0d000504144806c0145000d508900710010640c030035901031000c001c0001a00c1884880180503196942c41c0c9a041c40b151003460402c040c0c21041c00c5960602040140b030408204603601000e041d40c2c081183d02e41403606070301a01610400c0456182042e00700170701d10b04502c401110703114060303009000d6002c861007809510311095034007076000a094000680228054030003940c110707100d95802c620207541c560480d039206180c54044082c108003400c0c400c2100d64140501840d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 165717482 1250 165716232 165716261
    0x10806090309010f18090b04050708010308041a0c01020c030702190f09020901020a050f0d020c090c0406030b0105130807030b1f090b0a030506090c150309070e040c0302120d0201 78
    0x440c100a48100d65034021411a941001000700c12000014465188280b000c000c0c138000d908100e8645d0300c0d000c060301011802c580103074030f03020016501034817070303884141202e40100070340d4602800c103c8040542015040303070a1411104000c00c0b45540024802031134600d00d420007a5407100c2240c8100092048140c0c4180742e41c90b03481c00309000c45426054524100c480000005a86a015400503410200394907030141c034a02500c2a55200282c0c041480300007034002e6401d80da0b1a04224003040340b44181520301001c00c1c07600740030a000c0c46005c0e07403081c0702c3c4060505002e400d0444081041c2e0f00c03451190040c1c042034001c040108100507050280300e130000004041d0b071050201c07001500805145034407c0701d0242d52a0140e804c455110701100c20082c6800109641041c90481d5406a540c034401440b00d0040d0419810345910142c40f0f01940e0003900d404015003001c501c2c0100405407104c01501c25100484c5a05000006a0f0740740102024401c40502800c0c01034001c220183c21075500d841030808 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 165718732 1250 165717482 165717493
    0x7050c03030c030901031d0604030f030501081902040b0f0603010909120e1c08130803040f1d070c0305090607210e0a03290c1c110403030e1906170108 66
    0x4586070b022003510031441003881d0000d507038000c04148501b5843c1d0b440582110f40142170602c01170560120a000ca01107290f1018411a607955403415546c410840703050111101001c02d060040c506500400310001c0014401c8451420030b0f40040c285070300c21b0344009890795690040d070040108110070302c0d904602e2400c0c0303807408880d80070204101c803003481c3c9a00ea50400c141c206004010303910341600c040602c00300001e12002d841b030f40015503940c001d00861038090b0116100169403040c0050080703140d00560020910350311402c0c401d40b5103050b080c2d42102480f600384410a0319407580ba000d005068025540c6090110894400c0e00c07409201040c808200111412a10829121440c5c21811658030981c54441468072a4a1880c034401641041c01300c4c0c1d200005200f01001148041c0084291948a4044070010024080201c0f5941d240f512119039080c802000460301604109440c0e1402614403040311000400c4450113041035004a004280c3c48480448042c0f04064401e0150401800401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 165719982 1250 165718732 165718747
    0x10031103070308043303021206030703020d1407150e1926030c010f06050a090903090b0703020c04090510240b1605120904051e011a04050901030807050c0303 69
    0xe4580c82a8040c1c1d03604d600541501442c00c404001303007103c48262403c5681170740100e90400030b002c1c1d840680f000780c0c01581b0f030b40030920901d03001c01c0c05801c80303600900301c02602c00d0540c1d40342d4107034814001a84103402082000a030b40314484000440204160707586144a03040e040420030410300540000c504003a002006010340044031010006101881094040c903461402c00750345103206210800c001e65003062141c0b0401c0c0f400e900328800b0744400b2039515041030380740c0103005d0440c1c40c3c3c3c03140940001c3d06000e0400101d00704200500045000e0720544100c640c500c0c001c82c00b9034050030002c4803c2c0d03021a900d403504018521800c0c1c030020000ca4030a103a80407010400816100380e009440d94000700280c0d51400c0a0034115641e00b0715803010940313401d00c8120851a44039000110f003036002ea4184000141c8008024070117800120300110481d2899013410400d40402282c41030601d0011400c010101703440e40c60300010390003144a00e9105986200034074000b81040761005840f0302a520a1140f603 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 165721232 1250 165719982 165719993
    0x6031e0213140409021e0906030a1a0601052208010e0a020a0e0601050c060a020403031b0b0f041b0e0405100203010605070807021f0503070e01080c0403080c1005100311030703 77
    0x400c40b14101d4102107403080100003d4010b14140e50000d41c4100d0402401d15580302c161001001d51b54211010103040d41d401c41816144c03038224100030590003400d41860b001107001034000c0c0d003014042c5042ca081454442c4840040e4414420352400d00340c140030100070004090181c0e4400401000180852b241654080781e0360104500a40354489007480c0002c0042c1d1083e010b8590041e1550201c482d00d003024520003000394803a00040d00003501403044844c0d02c102c0886080c000f6503001a403903d075699035180682030716070050400c0f10788581c0c10a01d01c200f00b492042580141542070340c9d050950030240f810b20315241c039190900040c1070040c401040700903002001c0d110416004005541c1d42c02151001601040d0360201d408203c804161640c8040c1d84e00001852058545448040000900c900159015201120015090301080005000060910303010304071200c261402c640e00d03007420030110f0b4107480046840804103d240c03e0100244a50051301c2850100700b1b4025110081c21034540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 165722482 1250 165721232 165721267
    0x7120305120106053c0708070c0909170304060e010615120603050309100507020303030a05180606090703020a020a02030d0c0b150d20040c0806040c090506070f0f0c06031e02 76
    0x10709020300d61660511141985005d81c1c2001030351600c1460b55100060314103150503421182083c0c03a084012400410200e1381d80c03041110094018100010a5040112100c0c5130f40c0010f00880d20140c0712006451400c009010306c1300a001c001461013140084007000825903900314106011441c2045000c1011400100032102031040544414000c442d0000e0191100d2188500083d00340c40b000007040345101c62644002d0080400138015202c044040c0035540d551082500d049500122050201d0501c9029a006040d046c070360303005481004069800007810302e000494294042080c21401c002040b18400110794088001c0c000084140801c40100d8211020700000a22154070b1501c0350211444000c0ca54140740c000500521840d0030540001389450003d03942c03a030140341130a6401c455103000710120802d458001d041503003002065110941a041502010341e01642c209003004042800a400e400242400d5200881e00f0039544000307201c4c103500ca903105101c4a206001a2001c454001c0c031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 165723732 1250 165722482 165722527
    0x4050f01050d1a1c210c0c0e15010203070209010e1302090129130302060901200a050f0a0803040b040204060302130212010e060f010c03050c030d060806070507080301170712030512010605 82
    0x1c80d000e241a00380e030191b40d440c95030007000d02101c94000000031400c60500c5d0300b601c0340c070400b403800c45030980603070040e81d0380e00800300025803201c07a81e00103216402c202150503501540c0041c0420071001c5c55004188041030030b03007080701103580c1580c040c0c9140440170038003411440440c03041403a2540d00d2016100c41c080742c2c00700030300c2401c000500c045181c1c8103d00442120b20090404158580c1001e180355490810b808200d070705000e40c0c200d5480d03041000c111540c0c0345401250a9195541b15524182a014001c1007280c1c0a9034400001c00541c5a4071420a09a40070200042c2e07a0b41c4605401001311005030b003d04030941c2c10070200301e40b5407106030280d0803400d02820041c0512040345425109401482e2205040e44404503140c80035647e032790800c104888a58060340c1c250b45803040125418406c8070409826000100f004000b200b4003150603e04554600080d1140d040c0c41d02032041c6c010484000550001e070b000b06e6620040d90640e41070a00425440c1005480e04001240d6104544901403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 165724982 1250 165723732 165723773
    0x3020309031216020c03010c050a0509030a05032a030a1d01090503010c090f0902030105100c1a04030503010518011401030c020a0c0e07140a0504050f01050d1a1c 71
    0x20224000300c0041064401880c4000e60700300041c980082c641c550000741844080c018411420040d0240c00d041c4a00f01071394031150303111490150f06010070780d840c3c1e01165040744c00d03200d0b5100d04030100e8401d01c050a40300074281115250540d050400c80d410b1407503030001400980082058840030303a04945004d5001440200302c1035803020440050751075080e144d12030b03501542412400081650310400c600160341185031207a00007600d880c03083d030803804240102a000407061081e500005e000b160b00714001403084c002c8a010011500c80c14400020548040b80401d10100051169252030b418840c03841d00c0000690741ca6604d0074008016004e00242414145940c0341c1560300c00700d100344090000030b50002403503103010782d86601c041272070b00c0210358100005100002000c40d1304140000c8410041c2e06a592608040c10035080119501e079181106042c008200102d1490764800e00500902c0c42c6a0302e501140360078040c0911213828403007528220168400d000040009802040c030800f48103040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 165726232 1250 165724982 165724987
    0x1060609030f1a0108010c030f0504020f0f06071e0c0503010218040f020f0f0703030605030f0c04020f0d0e010b011d1c02030c090903040305010605011b03081924050f030a030302 78
    0x7401d00401c10a43c1c00180c00c1d05107090380010400c030303505400c41d003480f140a907010011490503d40d40720403600c058500035030002da200100f19044c5480c00303804000407002404545080c00b2583d40d0030003180506260a0030b07010031101013041c0071042100c4401884154029842c000702d041c1444403040d8201c501910403607a56080700503002486d4165080c40700c070304440d43d179070b00460000c0280b26040b038201100000d0402d82d02181c14100824881035407401c440c014030444d2402c004100181d04614131203d0500340900c005404821a8080d070289104d801e00000b514854200005019075000d5052102e048506100513005441e00118001c0f100401c5910743e000100c0c520029041220034001154800001d0091144a050110090044a00c81c200070000d0740d0b86c420041d60b0a11640404400c0c503100c5128001c00b00b4003941c00c8950002ea54180085180d0900c90054111170500018030458001407095245858407039801d140a001d0031200100098048400a0f03070b10100c07901d00404140c3c01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 165727482 1250 165726232 165726263
    0xe06010933050406030305030a06050612071d09010e040b07031a04090c0b040b03090d02010c080703051008070902040806010f1a0a03151d06040b01120e0709150e07020106060903 78
    0x21079802002e480c0c000c1090040503500d040062090300103940681c030182c9052400101403a201040700d4a9900007a0ba0301d11035961084240c80041c200c520a030304604c400d41c0d004005030359020b4020b0290001c1e8084c8041f03810300b400c4c54002104020040824549800f9000c3c8544d0442c810010848134120741c0450139540ca03142c544010145503001c01e4002d140454085480c1a500c40514030900d60712003250904000210201c1c02d07640c441907420041216040458030f2680310b60840c941c407061a8400c0340219030b903100101d182072626807203107405542c0072a0074000c010080c000107005114100d00381c459907043c00c42c46411201071854121851000042c544d2120f402900502158a86107241d012056585c20100c1d4215003020302c0840703180c0761100020b4082c0745c00e00c1080c00d411810383d03c030101f960103010070100404c482500c240541c031070301000041c1254907024000359070340c2028136052903d182103a0f190210741c0141c00d0106590401809105841c1c0c03100522085a400810b2a41c0380f110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 165728732 1250 165727482 165727571
    0x706120f0c031e06030c15050c0d030606020f030315010e0418080a020106090e06010618080607030b0114070b01090f02040305160510020a0807110105040b07110108010b091807020111030a0e060109 86
    0x40800708111801802c02080c450bd401d40c1c0843e0413240d0680990b0700201c05060090703241e05c02124181040185145c2210380c952054045000448000c0d20016070030301c26008404840034035a0b4121003a460010750150282e42c28050303a001030282c614148080304001403000d450300301c1401281c0030080d001e150010000142c4030b45000810380358081d40d90310708002c00010090404903036540e0100340151142c14003183d4140448180340c0c0c101030501036990900c1c00545c05001d0002c442c0640d241c0078413010000c2034040c032041140640103039a40090a1400c030a00c83c1c42040d0401d9403003990098030314400030481d040b04990740c250380b00c0c0c1e003662860303c1c910042c0c41c0360065401c90101c4a002050500400c04440b02980c4040000d895900071030307980d0034100c0c0c983e20072000b0b419008540b58040c0f804601050400b41d4100000c0d00010502c02d0318204901c0440e017003255503044180d00c400040003240301c14408240500b0000301d00b032003499036244207104c0254820710208a0710b690aa0b956072102d1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 165729982 1250 165728732 165728737
    0x507050d031e0f03110a0503071d03030d020316020a021503060409150203150a06140d0b04050c040e0f070516020d0b09100506040e0706120f0c031e06030c1505 70
    0x801052051512464254000d10704020300109101191800c3c05500340da1170000c068400784115940d90a00d150b440140403105081d46030310300484808150003400d0786a8092014141c1c0c1180140c0041c1c980ca0400100120710b6848012502550400c640800143e150340381e540c0121003501109030340e0303030700c80b040414000e08034a0806481c10118400d1505103143c03680056000e0f060701000030100c001c0d064200002500706115520101e42e003091341c0303218011f512025040d0b0344d80e9001d00080c0b00655001040c243c6e0310481c0c540800700b20000c1c040c02281403010840703800a840540603a468a08084060103621035851402c51900780c0540460455441c405881700030f55201c03c02401900300511040d039101c1441c0d000881da80d00b050000f071611704082c45800120320344000100415894544251b8080f180304805903104c4d81c5a0070716801d02d0a05000c4d420940d5090390700081e83c04082c040c02203440d180380d50408000d508124041000c2280d0b04082000c2da249040040010a5010380646e111f1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 165731232 1250 165729982 165730007
    0x607050c030c01090818040506010905130e07030f0c080601030309050f031905060105040e0c061e190804060c0e101101090605010f051002061e0a0608010504060609060906030507050d03 81
    0x3d608015020042080c4038028010b4201e0f444007518609401c0400c00c004d54000300d0300c040c0040c003480020840c5260151042c07491903142a8001039810340e10414508104582c1c00640da6040811040401c0010b0b100301e0000809000c0098042c550442c0e0b4000c0014400788103081c480d18113140e050001d0381e8148085080b2490f840075252001d0041d1602d00e0300c401c0c00740f040900c12403a21102e29404000840d40500e2141e001b003840340f40c11a180800803002d456603412030000801800901c2c0b4100340904c404071854402d07242c0c1c00076032030286000c500740c51070146d20301c04000b070400c090384890b103401d86d0b9040448014145510006d103d91100360040901c0b6034040c200c075003440e00004014070011490740964906885891024001d00e000fa40ea8120540720b02c3c07445d500e02c448852400c2c03143d20070107400a109080220b4030a0b039998030a42550415502602c0c078541c1c4030130400c00c2c041e5a200703400050118140500c0024a5500c600e80c0f00c0c13103d449045c0c09000082100303020076219910341a030b030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 165732482 1250 165731232 165731257
    0x40e0312090c030102090105090904050106050d060e010c1e030e1228030203100e0405030f0d0c0806040b012309030304240c02330d020706110c0607050c03 68
    0x1586049012041844400d803840c41c124007503100c60710910308040c0200ca498000c180c4401d031401005609014905800034410354043d5070b681c802054030361300c04005400b80750040304049003640c9c103024107038211060800103400740518005041c10b01031a076000318050545a080020752101c41c00840750404e40600890301c0800000201240b41121490400700e01d0240d0055a4400c201707082026000c0384020343d000080810b90403000c00c50700c440001210b0340710b4422400c2d241001c01c40b44060565800100407050309944072401035685c0c80d4400e03001644a0001c407000c0c0710b20405c032000648002c1018a880c001800c50b0303c440c9032050220411250040b1000e001c07694ac6031b956861060811031802c58107180e007640007441d40e8003144184900162540c000380000f86a1b4240907214602000602800119034005141101c0c0e403480d020207040518104103015030b07125200d2400f0710490b00712500f03007007103008180640042600700098159011030301b420301c1079840204c071003103d01c0d40c007950020001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 165733732 1250 165732482 165732487
    0x6160807090e0a320f0403030605040f0227060f0a020109020a0815010b0c06060609040e100501050f030a080901110709020328090f02040b010c0c121a0c031302040e03 73
    0x140fa043e194000d0000c100b01d040300940c098001d200c003903580700c03040c0c1a00380034420100c045019204001c1442d90024441d080010b1752076904c4012070103446084114040c0c4650120381d0904040c1c020101035200f6070303840d182031004030500f40090058040d8100900d141000400c210114a0003540581425600208010980c59071a40025035070109048090104201240000f854020400c01c0d5403404a081c00070706140e584180038014190409805154001d803102d8101c4e940300b10620507114415000c06000c5040d42c10702d024013004071000030b541030103079106161240205030380405940c00c0340c01c05d01c5c1c0f610030040c44c1191389290840c0f41c0c00000885200205120f0b4140300120142440420300030100702d8040b0450380c090807140000009460701840300c00500c014901079000c0703207805c101410800007411042d01c0d50b94011074140c00003d11000c074905104180115003100b5083c081c0c40010944a0346820714042e40540400b428084032640300702070032803c642d20341d040400101b6442044a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 165734982 1250 165733732 165733741
    0x307140313030f0206041505070c0629030d1b02010c05100b0916051806130603021b010917070204020403060c020a12090501020a03210207210206160807090e 69
    0x4140155074080300841c5046002c0704000c0d00218220b4416500711440e140f01031403484442c0e0103042d00605500c1003101840003000001d90074804c03000540c208003070800019121942c0050000d0303040503c54401d41c04229003121a940c000c509a4174800400c2c90511034014a10040c0c070302c1d005001c001822802174202028801c4850345c030084c4400c50071100a1400c0c0c40315110451540c4450200d0030001c1c0c130810100200e10a920f020340012040500080c0c03801c80055140011406030741c21a4000a40000304080c9050005e0b08003844041c0707900082105810715a43c3c2a0307001d0425003100d8919201240300303015951141e060364010f50700543e0a2044101541000b91281e141000498104820000300c2c5110781c45100740500792601a001450080d1107a24252010b60a00000141c03070001001548921040d0b80090710042d441a142003c1c4a00902d0b0840d402040012510045500890802101703168100f1201e50307400d070b03600b007a50082c0c458080c211074000c02e903000386013001110020311 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 165736232 1250 165734982 165735001
    0xe010e010219030507050406090b0c070b0408030a0305060f090f040f0203030d0e0f011b0302070501240303090b030906042a141518040b01090f140916021203071403 72
    0xc40d031201c1c540c0d04004d555104503041d962401540140c0000802c4518140148860000140703100c1055004888081744c0c1c40c246038501d94410f4101ca5066000403400c0180540c15015154006204444540a111021000c0780d21007000034244a00d40d802100401c00b440700b07807009540707110340160a690752215268014400340150500300700c400d2091440c2d82c1c0078a9010b1050124030342160341c81046035841030a00324065044414103840d15580d805c014025039404104180b10307440e01042803034000b455400c0c042c00c0c000060744000d10b850401c00c100318008002044507a400f55028100f08081c980d4000c4e4901c1008500030307418103040b280e80c6d000c02e8100503040600c008a4003180c086e07200c1403200038044030702c0c0900c2084441410040c0c0080c46c071454940c11030b055442041c5002c0043c150f075004820b400072061f504c40100c041449011507103604107020f141d540a540040c4514005880440c025611640b80c003924190020100104030f4003485600300c8007078041c004058a03200e091040c100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 165737482 1250 165736232 165736267
    0x90f0818031b042c07030c06030b011707050d02040f050405060a0f0605030a0207021809010c0e0121110d090528020904080c0703030315050d150507021203010303020a030905031b040e010e0102 84
    0x1c0d0b507c0e83c85100001540e0b40309024402c2c0542c3c0c1a5108190303c02d400d8000c08403140003400310f038240709050110240307118692010f00000c0120300d602062507450304060008448010f0041401840070010a008940f0f2965001003182d220f807502550f02d0342c40001d41e030020300503800c00a510010219003000b0042901071814042c070441c000030000c001c481c60b402c0d10350710b47e004180ca01181d4441c0101e00c403003003081040790b01e0700d1910401007090683c1c2002410329038030445580500b15525400302d41401000c0181c406010282c0100641000b5030502511203080c11100c02440381d214100000c08201ca8141900c40e21404141100c40c03a948030f240140c0074040402100000b81c41003440003c2c01d2400e150103880f015004160300c061080082d4000024140c020800000d500c55500b41c8030004030080c0045000b58004d03406040403000f5840d00800300300c2940e01041c425408210000c0710421125030080000c50200e4000607100d104001c000e02400007000c2c0c1c05059440490042070f400550b450 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 165738732 1250 165737482 165737489
    0x4e0f08180316080c010b0105130e0606090405160e1e0f010e03060703091b0b0417010b0d0305040510020d090504091511120a02120f040501090f0818031b042c07 70
    0x9118100c1b0003c0112142d010315081c0680240e2145020000c8190240c1c040d50401d0010305214900980c17480443d00380e0b0003d8501802c2c1c145013402c501000c543c090210280d046049601c401d03d41040c2c0d07443c144075130090f8034140c03091320f11351242c01542e07020f80e00640c6543e4003d41500c6503403400007000740040030321520079690b00022100c014580c8205110035000d0b10300350080542020b04000e00880141280410034505650300d0030800704c6a5107203115054854440d58450b95164140014452480307555007070f500035513000d61010401c03a6000041141682c505413000a43c0203e5401c4c05c2d0941e07088100b141d0751041c981300300f102d01d845030080140425034480c41100030b5a1643c0f10b00500728420001d000014040020101e1b22a000c204095a0041d0281b400410b0b40010b5454110302c4503100001111036080015501c180400c101030001e802c21011005080400403010004003203407144101c0c035110b25910318810303442d4904c0701011039900e083c4405001c0407040c1c49103010340e181450701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 165739982 1250 165738732 165738757
    0x1101050f0901060609030803040b070c080403060c14191116090504030306050303070302070303030b0a0302040203070e01110f070b130b040b0c010f02030606074e0f0818031608 77
    0x1600400d03018013903400c071401c49078841c9403a403035561035482c0c0803e140c0c030240081080040000e580cc001c90000d0001d84003550180c03400007030708109058040c02c80c901d09030010030000170038421a02c0e030744074070812100304905a05018035600b010980c031604221000c20001861446180085400380d07040c3d102c2e5100360b1080d01d04000b459140e074105035980c0550000140181d010403410700000340303c1d412110f6400e2015160201d42901c0341e000500303903041154003000280c0f1001c01586035603032160540d040e150740304014091840c030700001ea85d00c85001c1d004402c1c1d039071400078010501d608513101500c0103000034404162600d8541a80c00000d922004510b80c0360b42c240044071010400c20700c2100c0c080da070700420480c03901c8441d948040c111450710341d1000c080042ea0340205040c0c0c80c0450302c03041000000c580c04003d4100401e040d4100000621058100440d88004071101034104804139005020724454006092440710241d28611642000c8403030f41520104400412400c0c20143c50b0350158071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 165741232 1250 165739982 165739991
    0x6091c05070605070c1401051204030302070b010e0105152107080901050a060501120b0d020303030a0e060f0108030307051324020c012102070f060203040f02030d0309050304151101050f0901 83
    0x90380121954084d6400181036424006420045400d00400307503210140e0605009042103441c60311610b8030002100c1c240c0200e80c00190580030000340381603140c058209000e100002e94145000706586500c0c400c0060601d000002c5c1a185440503101484001c40c0d41b000d1035449403a142074010407500040d1540180c96003000003090840119000301001d45d04180e5480c002c11103042c0941c40500b0203160040d801400c0c00f6411005030b1010b0004600c5800c24440108203c181c00c06403038a8100010002c1c103c000100c0018041d1042c08004c0f40c5c5c00c820a89012500e85c0d0702c070780c0751409880441e40000c4001e0210b050401500000c0e010305503504070640c09482c4100f61000040d10406940e0030091070b49810b00450828510442e07014144840c040c03030740365940300501e03550182241c0c030030f0310305850740c1101c0b61000d801c601d803c2100903400c46091506014a00880c0d8480d9a0307406a801158407020303110112580302c51140311608881159240288003a081903400c1c403084413000c1d1780d0b4036150350030b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 165742482 1250 165741232 165741239
    0x162d1401110118030c06090515180102030114041d0304080a0201030c08060a050909120705010605090c04060e09071b06060e09070e0a0510050a08031908090309040b06091c0507 77
    0x61142e001015400d1080010300f0100e640d08441071901c84e0011244503984060250105504110f00301c5e030002d4610109c0c83c1801c01c94000c046107070b130b20388207014660f00400051004081c05480500000c2d010344003c1058104103110081c404520282a00240b101040c00203044400244800700c80f4000e880030844826040300403104a80c0850310950440350b00d9004020b24104080c0050b844001c00c401d460018060b4222001143c1c0403c0b4182d4480c0e440d448144480d182c2140c2594014208140041c0b074540b41075005450301340007404261140c01e00c240080c41d014002c06200c840350300f40c8040d0307840600c0c880c03610300d0040c0b5150240821054001e000120041e4000076080c042e84c0090b03261050320350b2000c46000180c0b1707004110101591207050002180c0c0c682000000107060a40003454452030080c001c01346035900000600c1c00c0000703190601001a4010080b5400030b001520041040b1540f100406c01600c00c902c00c141e000400340c2480303841c540f41c0110051516200c3c0b42501c1490341d9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 165743732 1250 165742482 165742517
    0x403020d240902030d0f03020d0c090e0a0608060a15030209011d0c03060102030702040e010b1504150c080d05060f130b011b050616020c04090c1403162d1401 69
    0x6040303030000c2d019441462a88051741c0581072400d5000164500549414006192002070710b442072488404620a4041400b81c20748170003000741c0c080360760315003000810f180c141c40303a41e10100581103070311b100c1d030318410401d07000d1011880c00c001d1a0098004c201d156980c2c03040f501503000f219030540e411040840031135006911202101c1c01104140e0040d400e003221502044024091000c02078401d41d614031212200340c507202c80d00a0840c0c2c0301c02d51162610b103031130b109070960b1040d01c1d00c00c41008000c1030b07034800040410041e03031510f50b110340c00000d40e6501c22000c6a02003d0082c1c02d6540300030646081500c0b0a4682c0090f00e200d0002c3c0c2c1d03420080c1c041c07910504024801320f00004d01d07a401c01c8000846032030702070b0700303400380720f00d1a104503003034210017502080490760500000e54484810440601c40c280c0c584142e46425902a0000d1001441000b0480b0f07420040b80115001052030f103030340e032515856540b105010800404494070300c0c950307100030704d143ca86005088540070074200035070242c4080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 165744982 1250 165743732 165743741
    0x103120e01090b0c1914060a1401150219061a030a020a09020903030d0507180501110714040e03130518010e04020609040f0203090606010801051203040e04080403020d24 74
    0x40c0306844029841e810210141a1900045421100d43c4030b0042d03100056400030000e10380941c019018882c030301c01820a41c030700742440180311502d4603040001107a01c0b101c500f01c0460455410150518012b19100001c81c240804016011002d4508041410a01030240d22140440311004031028450032100241611100111406544507202400800c03060ba0740c0c0c5c0040400b0078006060302e280040d001c08240c03c55200b41e8580e000a00c582446140000095600201410090070314141e9003c44030000c81d9205d03610f00501c210744a40b449442c4907a11107400c05200764900301c042e2034581c00300d290b100f41031400750b1003004d1145140704078031690100100351081c182c5800c02c1c500c2e03030f00313564640a00035658020000c1c82d42040d0b884288803011251071001d5801580350402600136828030350001800c41c40c068004a210714010303818440d00c030f1000001c8900700c0c1c1e129410a02d0036940c6080c403404030300580d4000394001c450013001c00100203131141703074041030b04201804405a2000040c440101ea = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 165746232 1250 165744982 165745007
    0x21e070b0409090507031211010b18040f020f0a031a0109020306060d020a0e09010b070b0708060a050d080c030a170a0b06070201030b0406150507061803020c0d0c1d010312 75
    0x4640030041400304070540c0e0020105240100202d50240e9520b0751201c030f003180047c0704640002c0c2c0041c1c20000e43c900070700400e4194441141d141c035110392050000a2884000ba00092891400f0000b640442d15603a14030801a00c005040c26045a40e03402d00c0001c4008203002c42405002500000c225801e00e0b2090341d0140e140500413074280346141305481c009500c020f03008814030070280c1164034030380d988500c2140a45555a0341d540c0316031842c40d00c0103458102401c081c00784030201c02008120388070490440f003200d02c103c440b01505605410704400300c0c840c030501c1d54100d00001035024221070308005004e01c0d500a02409075201d640f590b80b290b0892f6480884558000800c0160002661180e0041034842d04000c100040352a518000c107841c58101100d07a0020580226014061104511400185511070050004003a109a600a48400917158014810702c1144225401d101520007540d0123000b883c070f96040511455003c1045541c002d101c11918941c00c08403500f0035501c22060303070581 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 165747482 1250 165746232 165746249
    0x11070204060509130f030909050c0912120d020703030e0607020706090e1b2b0b012705100c0506010807170d12052d0703060e0115080c040312021e07 65
    0xa02c2944e514000d030b01d46100c05404005c1d054a021540d23130094410342e8056203030340d410300741d80b544620300b4001d89900c2b0ba170062803a80c1200e2003076a0500000801c80b910042c40744001a9500ca840c5401e400610301071039940128400c001c01c010100b50001603400c180c6a02e51600c001441c0e46144070300e60b0003812030320603c4102201a40040d078120101c050910006401c00000c14074003008542039003081e00250b0f08009613106c2c0d0143c14903580140140884805507a07810f180c10110b0101911282c2c0c09129040c000c15100b1141764106200780140f17180030b0f0b44007080d64141c3d6910060142d4607802c40c01580d100464102a1884a04d0b0000d248406d9600d15119145403488032031a00004150050520600445110746d043c100c004114258205076041a4525054180020300408641843d084050f800200c04014020b4021480120411407020700e402c032201d41c0d45121040301809541c0c030061a2080402c60700c80c9850f00401c2614008a4a0460b407500522282c500ea5940c000352080840 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 165748732 1250 165747482 165747511
    0x10602030a08180f0a0308090705010e06030603011103040804030510020c0c0405071407140d0c0c09021606110d05070305150f030a05161505041d04050106030611070204060509 77
    0x89603801103442c954080c0038441c41c040140f20b024441c0b0304103c400e07040460140c10070803103041050b8121030584c1d00410814001c16205081c480040c02030b1840c0314035144162008000100389503800d400400d0b0344088503440c03175141c2c00c0070b203411031880d04540021a62070154102d8003042e001d1520a84040026240081c07a41100301010b01009010290443d000c0014400d611800240e00340000d00015100c0c84550224590700761141d030600002c1050081085000d0308000b0124401ca0b035003405a4100000040c2d4900141001c0300b405009607000820150511860300a031984142c007808070241d050209000a40d6504000c50885a089801c0015560844468403032030404940d40c2c005130802404840600b00d05803940780c5800c000d07040380d801403040c000c4180710650314032000f4042807100c1c0c2401424142012a070110300750540b804a0542c004020000d014400250490401140c11800c10803a0001180f40301c08180e00c8100705900031414440f00003003a05201d40f13260320401e81132020b140c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 165749982 1250 165748732 165748747
    0x301020f030a0e0f0303070507030801170601031704180c0e040b090703090203010f060f05132702011b0302060106140c0604021c050d02160905060d1401020f04030b0103140601060203 80
    0xc000300f849036521816442501c0850b04040720030002980100070a0300e400ba101c050310300e0000c01c440c4050b0402e080c50480200110300750500000e2144c1900e600c8a2026106008000b6080c0c0c0d42c01164003446444180d034000d1241044603a00c4558034003610390300c00c240340502109000550721812000d5400041110024820f90300c250320200c1c106200a00108110b00e41c1084e100650304150855100401103950400840c81c2070144c084090328040014040c05444108003031001201c070b58070303074850802c55003e103045a208400c00702030050546000703032007000c1c4e608000795079290034040c40000c10b03440240560100d0703076141980d12075001d6900030400c59985a0910043c003403030705260303001e81d81c15030550700005000303000d901c0036460240d0040108020010100a0700103540e0301c0380e0407152408040c015252030382c02807540d429421840300700712210350b4801d0324024452a070300c1244469011a003c8100b002182005048038000c08010b105031003402c400c507403211004e10520001da8400c00280 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 165751232 1250 165749982 165750001
    0x5100b031003110a0509010b0d06060f0203031f08060709081b0f060706110705030c060601050c0d081f0b07020a0501020c01050a121b020105070f0e0a030f05120c0a0605060301020f03 80
    0xc042071002130100e100199950780811804042070b004000744180106011100c0035091080700c00a0000b80740a901003444d4400194481c44090490005089030540d12091f0340b030700300c100000404591040b00c5a40c41e00c2c1100901a503018040ca40d100c3c0240305403104045004849035420410003804510200300751401c001055220b00401c03903d841d15200b5203a0007480701005080c40d2800780c805160b4945462145604180c00180291b06014007401007040c2c00d1b4000800141d00c2d091f0382400039041d26280c10313200c030302c0c44194402c016030303d0038074804920310700c5c01405098010303c00d4a2100c1d002e511140103a0311b03000f200b844540060740c10b016501200f4031802803098120302460000072046000e0007144016101840710a01503916141030010030f90b402141a400412030b0f00d0800348007003150000071100324052201420384580e9400038000c0c041d00784031040101c2d15141d41e0917510350080e20050340718501035000b5a001ca02d44000207850342018005c894a80c0401c610f401e280d6514101d40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 165752482 1250 165751232 165751253
    0x16050907090905061c0f030207090216030309050f010f0b010206060402120c0d0f090b0105130614041d0a03020f0601060f09090e0c0d0303021e04080a080a02150a05100b031003 77
    0x10356200b119400c91030030010001018007205400344000b03034076507006c0c0d04000e4170700f03496944044506841041600071a54003c41d110900c90352510b40456940c5c494101039240240350000072025510f40035200c22031f080e640d84900a010070030b0302a10710b0360341da11081204900400340399002e80d020315030001c5c00711407102d0004c0200d40014000042c0a00d0b01a814074100d5803c103000702c3e142d0420000600c0b0525003a8520002159200001d2021904020004c8070715121400014012a1555042800c00c0d850306003094a00725140108c48545074641002551000c0880c5c110881e401f941c0004a203007071051000c00d481c80e0143d225070003402d14109030b00c80108050304945401d40030384400c0c1c86103076490711100600c00c0c1c025500540c1b00c407a00c3d403c0d05102801885030000c09002017004101440011910820040d00a80040d0310b039120500d00787d0800c0d5407030f5044020001c000c410801a0121580558000d010511054a6143d110b40b2003040e07510040d582c0c03000c0007016107010000109000300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 165753732 1250 165752482 165752491
    0x231c02010c0c031505010515130303030f0609020d02040509090712080306011e1107060f140f09030a1b06080408120a0b03010603150e0303060a210f0516050907090905 73
    0x100041100da50fa11846043e00304e401e928070b20390380c172880100082d290241002801d140f0003801603241078500300b0802c41100c260310000381899124500c280188a2030340c494001084400c0d41990f6a904400e003010007944240529841340500502040d2042030004414056609180c030030400340e9030503107e1250a41008000707034100100501070300310b01008040d0700b8542d407140b82c0300c0710040c11a6103000390400300160024810400d00444034052982d000c0603507076075800e980e02d02c1603031004644103001c0395100e03844009815200f01d00c611010030012000c203445000c0c0da16502c00105403191003c4910f020181d40150854030240800b11341108000744103600030300c014030000b5001c8844000b00c0d094440c00da00549000024011102085c050341c0035001c0c002c8584405076183d071a0400002d1014090f40c01108540820001c0c100303c80c0351035454200243d40c1104002c803184c16545041c40c0d4410346100d40751780c001c2c0455000074880c00d0078003685024103942c0d203c1d0301e411b42c10300d8481002020002c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 165754982 1250 165753732 165753743
    0x40206090a030b0f0a020a0e09060d0506130c0b0711040510051c050f010b062a06010b03091b011d0d020a120b01080c03071203031401231c02010c 64
    0x2450368940c0caa00a0000451048494605920b4020f50300039040034000c010480d0540100107203000c0f190310440c0010b040e40d045078024955101c4001144001041642c000d01d10300ca50414001104030b180b02d0600124401d202e518002511940d1095842c007600718001d10710500381c940d4401500d010b4014561103001c0d0040c800d44180d840000442c0d01480305880c0d01903030b5a0300d001106021341401b400e042c0c2101c0b280244019040d100105200e4841e41c00407441540640854100102181519002c04002030046502c10750b11100f8a200942c0140c1c3e2400ba5480790150078000b80751618103612119005854000b6428548081c041724070f820325140d20f504c002c100c842c020050741d800345400c01030300c4d0b0b01401c80b9174210103190541c052001a0842e09031603001003d109603542c2d0005818054844010441135100140d10702a03001c3c146859240c0c41260704500042211000c4544400030303e000207202c200c81c10f5015060294415444c03009a12800004502c0303005540969800c2490702e2040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 165756232 1250 165754982 165754987
    0x207140616052e020301030b0601050705030706021c060509270316050303060f010219020d060b04020307110d0f080414030c0609240606071202030f0a030f1103090d0503040206 77
    0x50361441c0c00d082409550b103082254808194003200000c9440006a900c0ea41c3c0c11407640d4119120f048802c100280080d0402c4400181881086010700507190300c40c5c1e0000b81951141c00008914915208000060404c5032801030700080614018403414068046600c5420303200c0300c0c44503104803440c0000e06481640c4410800484200e8030340d006459210700490103180c803810718208008500b040b00d091941154840f40360381c07075003074103034023034001d2582d4100c0d16868400101e113082006000500e101070781c854804420022002c2c2c1001d9103880350300c2088161801d00c1c7c107019082e02c5107440c0c1c80080d0b00041420340010009145080c0c2c0140c1483c40d0b40032242012038213100c0a140120403030740c0303103800c4c0c2180c50603801d020040b60022041c0071010142d47d100d80b40010101e0864010681e0250a681c0ca00b24440141c90003401241c0600e040c0619482d524035604001901070140d500c60b84107414a1700034000c070010780f44d2051b01c0c01004201c000c1d00c184419a01c046601b07410162091303a004404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 165757482 1250 165756232 165756277
    0xe030304060201050103140705030607030b0109030609080705010e03030c0f07080d0204060507060b0105090d110a080f011a0904030c080307120204090e06070c0c05040c180b1902071406 81
    0x40000e031004101d95400480d40b5030440c1740c10828107034490100311306603201910901c49070ba408a02e141d030000d0280740025240c03130b0320350040701c01070306a0740081e1415103485007140501c03403e40e00404010740a14000d01003c1940c19119540c1c1c4821507042041020610507092035100f00402000e445000c0e103515410800014002000c90744542d10130307008a01d0000b0716208008042c0106000c0301000d00b0000e007820f81030720208055451060700200a44040c00c00b1035040c0e92121154405004070030211221030f074604c10698001c0440186068120880c0a120b51841c9800340f0a40e2049515549405001d10039540350801504050003c03410700c4484803a856500c0c04a201604c003d01d0301000210392036030750148a600b84100501107004001c1c800801c840843d240e0490042140d1040c0e4001030781c444808030440d80c7c0300503401c45e4400310005400c0003804010f620003800e4a64034007488203161602c0004260b070341d408e01d4441c0c011406035402c00000c86143c900003403c150440281d01941c400702 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 165758732 1250 165757482 165757489
    0x3121107030c1206060305150115180902071a0405030306131109060a170a0b011b030c0b0c1213030212040806010e07110109030c030306090b060708031806160f1409100e 74
    0x5509a0b6841d40c190380310010070441030b02904543c9450100d0402c440008202ea10b00c0c0c4c4c43c0c4601d0700645a332190001800700c204104540c6420703403200181e4110290b8180b500d005610b17030380b00f0381e01184501d0707980c9a40c09240905100d40079100381d41610013481d01400a0034002c080d00440203500a226158800e40c10321000c010b00d4030300c68400e00500041188d103001c009840c4181c0407129614800b0400010800240c201e2502d90500e50030140424440c0d555882d0000e09100340d100c02403983c9070440c02d05c4102c1d0900712000015a101c0c3c3c0079200c03845030151916a4a020b00d114650840c3d00240041040c0522402100d400c90600c2c5071607003081100ea0000c1c0e007980c000e6401200000c1e140404401810f90600c5400c016049000d824080c1c1c01034100054000c1c001c1b5000544003900010100e062400c1480507260048250030a0342c0d814540000c000c00d06c503101152450104051030b031a003141e030b88200e1a803541c2d114218181d5003442c880c641880100100781d903a140c14400307062003c404954 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 165759982 1250 165758732 165758743
    0x150405010e0706080109050f0f18030c010903090504050610080a0906060b0406050a02010b03030307050714031605030c010b060f07060b1809030a02100912050f0d020403121107030c1206060305 84
    0x9110b8848a60b01d501d000388a02c1103031030060122800811008c20300c000300c0041041c8542040340c81540d049021818018641503101d00d000c52456903203050310190405400000d00c1d411203004640400c0750783e4410041c000c401c180816544000f84028000802810a9620580046000b06000a00d1a4071600100103e51064100e0008200c1c08118841c10b29824000d0002c0040180c002d1030441c00c055001600e039002e1480014050301851031a905098010000d803a0843c642d26504540294141080d41e240e92140c1850707900d41d42061961442414400c00300c441c4d0490614010349040c629131030310030050042c1ba52941c1c0c07001d1311090000c1441134203565503001d0041d0401545d595001c4e40300103232074101506e48000455050000400105002010a41c03800c90142400f0f0342d40d680d05140b8142e80d11410303828000c124400b05021082c0400505588060130158844148181207000e13910f0340c98400c0d100080c07240ca0400018401c10000015440b0b80c14030404000ca00d0b1600c907a0348a0408 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 165761232 1250 165759982 165759989
    0x9020409090b06040e0d050f09150c070902030606120603030705011506271e0305070803120c03060312090402090d0f03140a0e04020315060a03060609090e150405010e07 74
    0x95072034488490038405003480154200c8021a820000320310743e803540986581c200d074901070078000301080c0514000078000494007542070040005401c045030208071480b0350000207402c0100c3c07040c01408100480b03503108403400703400c1c020812810801c00b040381d100d00794030060041c1d816000c00d00c09100064401d0007001c2c40b0602d4041500c0c0b4107810aa0700038054407424000000400b6924110315036080810034043c00d032854203a480016420391102206941a00d5100038030310320986a001801050100c0600a00d1401003d00c1c095929501da85507039034001940e034140e141d0011180e205100407200002c21500074007400140c1801c2d080030016056413951182a200c481d006a00f0208056000f48100d0fa1054908841410296800d0340141180054540b240c002e81d80000400d5803007101c0d02d240b038031085008140c41c0d510945280d009001c0c040e1813081ca00032800e034000100383d90701103000b0308920005e01c0c8000d100b14007080301990161031002e88140c1321950303200c4100d84100d10901c5004040c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 165762482 1250 165761232 165761249
    0x1150e0a1d061b210414010b09060d02120d020102070b16050a0809010f02070c0801050c03040803181e100e010c020a0605040f08270a0f050118080717190209040201050c010204090204 80
    0x545c502400c00500c21a06120311554691412240028507642c031000c25820400c266422200e110052020070f00301c143d1442e000700316101e940744058165905400400001c3c0c4101e0f5940083d4441c070741c0740040108900e803844040380c014440c0500e030502c90203009500003001000844d201c2d0030510580100da025410548412070075070401c2c800301800340552034110407092070042c034514154650900c82d00010708840280c0703040303111080014100300085e0700c1600e5400309407801d030320741c0325204c590707404040d140840064203204408403200c00610642c0040503075074024100d000c103030740d803090001c3c42c00600490700441e02103001030210b80b6440182400003c9204c0400c0d0b103c600441c0340c1c3d280068007110902c5101c489106001030003041103500c0c07c40d1828200049040039448034240500b80d0b80e00010081d228a41c1d0005080d115100a0041c5d07100c1801524450a40041000071065050501a42000741400400c0040d44a070000b000b040003644001418682ca401c6110b003a17a00070b5200440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 165763732 1250 165762482 165762547
    0x9040302100618060b04030f020907111203010503190302071403030f040303030606120b13020901030216030f09080f030307140c06090d03050c09030709050901150e0a1d061b 76
    0x3e5100c0d100d1100a84404041319042a280d50340e41520500700740002070254000c2d01c00b04122034010032071205070604200170b86032006040c18200c40107800903c946803003480784182c80b1011340d00341400d000c41d09070198082c265450609848407401e10114480c250584010050381030400d11000240002e54882d0b84c2c04904030303107001d01c0284003048242002d0344091801c0c104410350782c1c1d805501d08116210003c056140c00b000c20050340240601e03030000d2420100d81d00306408140d4000032107048188540c990707003601e0791a0810a65904508030303003841c80d03604c1003002c900c0b8240036413503000710049801030080c6050300038680c5d1420408260707500038459002030851145c0780d405005a5a20402c42e1400c6401d0030705820000b40c0e80e040c540308100800e03039281e01040341c1460a42240640c0b409496103016103590728004621707a0401100d01d81c0b061850310100814098a1100c54285282440001c000a8a6040c141c4501c109250386100707003c1b004000960b207940d4941c10703980b00c0381e410501e00c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 165764982 1250 165763732 165763769
    0x20c0105160b090a0b0c04080d0305270705010f03020a02190804170303010602190206030609222301060518070903150c020d080c040303030f0204030f0b0a0b0f0d02090403021006 78
    0x1703c0c4100900118078000003844240404030b000500321000444901d00400c054640c26014034210a6400c401e50402691403000400324600241c02c0046038001c1e65102101c80c05100100d0880c0100c000600c0107070400321925000c144290001c0413400e0107050554a01070341c485c0380f40710001400e446080260004001000a50703014010514510311515040e00401c1195000541c1803100a140900c51a148404150b82242042c1000c0b6140c803940d0f10032900c5800345c1408544a0790004c66540c0c0c84a408000784400041030107101d0448401500303900c10107108459010449900915010070026241c00010100e40300301c808041590640d5400503c450200100a0400040741240c0d414010102e09000d509411a03048500700c98052400052524482801d040684121750014040205081e43d0743c0a00c04407a000c10b0248901d01c03410804503403443c06011840b01f100d500c0c594003000070f080440150401c00d9805500c10b20910648008072000443c81e0b0480d801500030b04a00c1c00c1614400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 165766232 1250 165764982 165764993
    0x5180f0108071a0c010f0c2a0f0b090307020402031e070f0912032001052e0b030604290307060305060f0409021305070c0c06050307020c0105160b090a 66
    0x85016141c4000036011880c00c080008804000040e00003101480000d0140d070402001e600420000201000c2445070401403500140701203c000c032410800d0702441c4080462040366045140859401518170074042e542c0d4980d40840c4400401082103400704110070740c0140c1d141e10045100e10603010036441510f802d10119980c25200400c0d58040c0301c903103d001d8541c1d5400c05404c0e001c8030501a060065018a86001c5403008108000c1c202c106401014921001e503064120910400241080b10700306084030b0b10409603941c91004d00101440c10080c1403060050007802554014400f800c0451b0641820464455100700348041c0c0200359606084201e05160a2080c04020210381c0b80501060a1500025400250f440002841256142c0f0340c0390854585002506c41d402c01441300b00950318041c1c44c064001c0000d60705c02c85c0c03500800800411902d00940c00c0d071b4001e208950003480d4581c1c0010064030607a010344d0740c0d00024032607160060000748400315810b00c103450302c80c00b90407488180e1600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 165767482 1250 165766232 165766261
    0x106020307051509031611090903040b090d1103100b040e0307050c09060409050609010203040218040807060f0605060d090b07020106180c050405040603031e020c0a031b0518 76
    0x4421900100900d1020507070000c0d4020324000681c112aa2070b44030400d04070714510a0120789480030342e041c1000010700c90074400181c00b115064652440350b07604c4a02158036446a03014081d0680700c144070001c040e081c10240005400d200d4400380c00a094a00000703890050290442540c003519100440518201401074148440101c4019410402541c0c5c80707940751460b680140c0e000703042840010740350f40d035039800111600b0340200c191245400c021410034003079402214164050110800d40071844004c032444a4800d50f0090b4010341082520354a140113001840403180704a5195440480e203541d507a00100750320995201c0006814440b80f81110b004030000308810196450b001d82001200d51b268401c68003000c1f2a04005840140600c050f640c2c0d010760b41069070090b01d0305802108064000305103484480c0301d0000c540082d11501002c0f40c1d140440040c0c240c2000e040d8004000103141c181e2590881c1c2684404140c109480f1000725450070041440e080740250768109000c000070b441d980c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 165768732 1250 165767482 165767489
    0xc010305010b0a0521160f020a080a08040507030203060903090f03120415030e0d08040303050a050709120201030609050709030b0c12040b0612070b0d06050103020c0d03050903040f1d01 81
    0x2000d014640c54812000028060101c3d001c050010000360250f81c0f03500380840c0e80c0400c1003113200c00c0312420449210035822000d00d44000124070b91072822000107000040054042d1340c810004c07880c000215400b101d8070b07080504201c0c0c0c03510400d90301000503682400118400c00c6840010354489011324100520a1401d0507041d02030b4201500034004a0141412a07080d81c000301c0801c0700b031007000d000442c02000c503004031003070074001c41c00d544a9035644045a41d010700c1c000d80d070a2003c0d441d40f1100c00101c8809440716400324062a504008140041042115650050500140661307444080d04141c1e941116103a000580c40041801000416840250400318108103581441c01c4c4000880000801810182c000d8141e01c002804694507038180f0261091041d040d2807105030b41c0c0c0c071038080540204140c00c81150402401150551203482a05c2d51101c052000303150302184034000768024070340034204079818081000003242031b401d80e000040c01010507c01e00761200309003883c00a07000b9410380 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 165769982 1250 165768732 165768737
    0xc010c0c02060702091b030405030a140c07060f02011d010504021801030804030602030c040302060d29130c18031b091a09060406050d03020a02040b0109030c0315020403061d0c01 78
    0xa005401503101d29043e07400b6160306071480295034449500178080d02000705284100341000100700030400c00d01001078a00092580c580d40503849800c104401a802881d01802103980404c00412040c0c0c0b04071300b403407110b048a0000080202d02c5854901030300e40c5915940305180c3d110001d120841c201388021541400b40200302c4600c03541107517582c00e96445a440b018040e1500130010440c00034603a81110b00441d401412180e450b41700940d000d028000b01c0e1815104621009840000a55410418401d0000c0200600001c0ca030f225845c500900c01034020030100010012401543c174001a1a0409140110b0100030750a04005c11204528400e41010840c1800d210162039924070700711701580303400703821102c20801d40c0e80d92000c68028040b642c403d0b07034885842081a400d00d6000f041369640e080c02605d0510514104000549852490b4800100707000b01540c406c0020500704000c0e0040c81a07070000c0540f50960b0382c0c072920140c511800c107a1220002480d00e180c406401017041070038130442030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 165771232 1250 165769982 165769997
    0x120705030f070b0a031a10020c04060504052806091d01050c0a121e050a0b030139020a021f0e0906100c021302041403060109090c06031109030a080c010c 67
    0x85401d54103005442600c82403540712a14055006c1c029140800d0361000940f00d000002d4100100a59801c1e5840360f250045203040da010855003424040c15100780e4002100514402d49031011080c0241c0450b10385c04000d40d1070b01c0124000c1d80500401040e03007014581e0850a40202001d582164030142c4580724444d0b040160007100f9411040c0f10303031610450800021303440d10941c2c1d421003114443c050f40a44601d800d0402260f40b070150701030448050f06900801244e800118010000201c210841c0044003c6802d90032000585000c01c0b40c0c0d411161040e18003032072007540481e5400304902801d40603480e12450203c02c0903404003044004110890b1f214541f82070002c080b0b400018503102d80000c00c109201e03c0c03020b41d1502001c1c0890856446170466840d030707850f2140e0464141e00c010180c03182c042c54000050442107030240e080c3c0c950b0025002041c103032601c1025001800c103040d0094114105200c15a500d80d0f0500254403924000d0a11035a6069140700035070131903100012190038840078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 165772482 1250 165771232 165771239
    0x50304020d02060a0c120503090c030c03060105060318030307020a020405150d02011215080c0a05090c0d0b01110d17070207030302062202060a030603020f150711010e120705030f07 79
    0x1980701003040650180d90f4140c0e620a840400c5808200c07004000e841c4800004a421116502030020746c40340f989001500c42005545e410103480c0e410404c100343e450b41c0320341c005001c0c0f49001d400654000985003100c0910b5070100941c14110740044965001503005081d051056040c10702a07503910244190130381e0b038015654400034550450f086400703810020490383c03144402a40380c0c4042130072000e02110546d82ca541c0d094003030b40c40c5441031145014404c071483c001243d040411215000e041516000c070304011034800c800f401040c40c0344901e410070065609a1485503c1480a0000c01c5071a07514011642c001506010080c2da01800984c2107510480f41000400d0707001c50070641205042080d284944241403013140403c101841c0694840d4000413502c03100c50700742d0b0006040300d109543d4058001c0d0030350200036450700c0d200ca1140460a0070480c038000120720711140003030024141044100300c42d140d4003140e00251240345142d1164003100e1f0610882c9400c2101c59058040c1c0030052803102d04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 165773732 1250 165772482 165772489
    0x2011b0f0314161410060b04031403090406090e07080f1f06030b0907060e040504030507030e130509010b090c0f07120203090415060f0c050d120f09120f05030402 71
    0x4495902a041004154424030800420701c1140c1c5a1800f50064520720419410089090211803202c42168030404120f41c985078003138001c81c0c0448494400c1e0a083c149161030724440b29403060528a0103010400c6580f0030350351703148100030140c803100500080b1454001d0000345403580d40d402c500d52542c0f00c0c40c0e042e50098800144c1c00382d025115842e0386900e9803481646000b0b06016040201880014070810684410000b140011038182c0c0c0c0ea0880d80d0400401800204d503010740b40500090001c010f45004240a040700c217001d48000b07805958881c2280784950b08494060303642903450b03511040e03003100c9450408442c0c0d4001c642596518500541c0e1680c0806234170030210020720410101c1e100c42c0019000b80f050b5412107034040d1040c4107a540959044101c0c0c0c003240107490100340205089404075200e406c0b1a04400d5112000303003016441200c041e034283c20480329040249403903121911826035540120241c9070311459000d81050250385001c0c0000030401e240804000080c4200300240e41c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 165774982 1250 165773732 165773753
    0x60611060c0d02071103060108030702030d0905030a080a2106090e1506040b03030c01140414030702010909110c0703050a170c100b0414070f08010f0e06040506061608030402011b 78
    0x1280b014016a00c8200746040e81201840010f516414000c91000140c154004001092010300c00c8003919004040c1803426601c02a181c09195015407040840e0000906580004e10328104242800100301d40310349180c080040c1e51b8007130740c444135032980c0382004100414010f0880b0107030700002810765041541401d06401c172000740103500c22912410004015142401182c0f00b000701c180c0240400720804104083c601020703107080320384043e10407580e0842c01011050ba90a039905030340e0a00c1052400000794041d09180020b001491000c0011075070006d41000b01e1001948a80040c10a62244d400c040080c0071059000507110350b81000078044c000404201d150144200389800130b92400d03004040303001041180008a046506034041c400416000124000c82e9005030380c3e1f0b20826a21040d605074802207502c550207041940e000030903001d1030aa04040d51008000d0841c45c10841e10120350340180d00c0c0400165010007001003070205550384410b0f03118900550164048006100366920200c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 165776232 1250 165774982 165774997
    0x1109060f1602030307030e0307060318150e0a0302061b0705030f0a02030403021512150f010e1206041b0503010212040f15020f0d0f0c0f0c1401020d060611060c 70
    0x1040000300020019120329154401c80d0300a4201c0e07850303010303a140140c02100380c800414403a1181c200c0c0010303903600c02c1c0547d0741c0012010240380c005110558804d000007038806890b0130800d4503074440d0701401d0380c01c00c05030041c40d01036401441b51b428140f04800e2852501074155900400c100301c0c083c0840c100004444540c82c05200741d0303584480c8020101d0440c003c0b5003001750301461074500380e41c1400e01c0300c0c0585005c841040c0c281e0350726210718200c2004c0d1080902121b07080f40c0c42c04424007240d8040d100a510a42018012407a02c9281030006e906000c0c3c111070840e029a120090120241002080c1901600302a0001c42c540001d0002880d89030000510007007100c00441d040004005404204004401c8114815034840021000109064000c0034522503150308d40344150004658038082c9480008403500c8890b401c0704030300d008503001c03560054160b45000c07000803001190002407004082d40c0c0003220000407a203040c883c1c0207050b1280b850b800c926981c010340920218101d0300341100c46a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 165777482 1250 165776232 165776257
    0x140607120e1908010510060e15120a090b0c03091209030109020a0e01050f011d101710032a0e100503010608070e0112030903030c03030603020d11010201110906 70
    0x8a0346030202118406524614141c02ca4405541c01d02840e11003040502541c003d100284600d50b1001802c10a000c201d02c40d0790001010b10120f8003403800c04000d190305010203800300c581f87c030000300c5600fa11544140c8521000540d03a50b40f0360144156242c0107a042000a1640c3d0f14609241c8109565280031101048508400180042d1903070703001d51042d000d456024028107442a5200b40c2c012485200340b103034a00070901130b00070042c10741c414820340703402e803c036070b1441c0e079203080180309102102c601e4182039018403202d52252040d03c000122890f02c501b00761039203c4401412b602c1c1542c0c2c900e01383c05140307941014030442c2003000401e00b02840141e03054025041440c1d99a01846001d040d09648101d405500e40301021810100208044058070a0345a1401c02d59903a80305260341c0c10390181001e400110110020700001c0d1007100c01c800d004d030083ca00442c1e0603483c0c2c0c0004a1039420214125000044240c801c2c0340340d60203009440c1c0c441c01d00b1120714180b20b40304010540621031b04405202 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 165778732 1250 165777482 165777503
    0x203190507140a030c03062607121a060402040314010b0a05090f0f0603070b0a091401050702030307110a03080d09110303160209061809101103041245140607 69
    0x204e8501c2640001d00500060034042d030710b002034000c5640b800b90a80723004111402003c10200303c035000b800d0180743d1141d1207040d02c9a003440c440700800000700091300c0d059102c3d07001c00000000c41c3c00007500b0600541c01800004501400c0c800b085052101a40024003d26400c0304200145c0d10300c0c1c407a83d90280b40c002070035810755940b9000a080c00d50940010000240204a545c4100d80c0401442e00340c60402da80d440014440e44015030b60f40c001c1e40d80c02981540100240c0300051610005e4002060002c4d00e040113a07034482d80c40a1003a002211038a03601550341c5030301c90a22040c422040388031b00301079024625096068460110500406034007070b01500d02c0a01040003501d40034802d2450514102409900d030170309c1281d0179160150041c6050000d030422403440394020040381124015a44500c4031003c01e208070701c058501c115001c680010b00741a032009441e00030b1074a0800a4560b5020b00c442110240078000b0301c1c03000384079401460404400c2071005541e900c40d40d04580144e07803c1010314a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 165779982 1250 165778732 165778751
    0x902010207030b0903121305030301150c121706040b0306010b22030606150206010b030a090305070b01180f060308181c050d0f0e130f06090203190507140a03 69
    0x345000050707800101001100703c00c1144603940480a0240c0c21440d1030f41441c00c0c1c03211802c80d840f440d42480081d05940040004008101109221100c0d08001d410402c0f40180e4603222503031211244a0302c2e034040741220b01600034442004482d968027040440b42001184941804a55070300c44c14003503090340440000348100038005c0300444410320b0145464440c1215180e103824005441c6921448040b4010311040c040d246002103800c0d416141007440d0b103402d580c1c1d000f8100c000303841811003e50a1140c1045101c002c04c1e140640580600460b0703860005800400c25114100d81c3da54544644003440c2080a0001503032020441c2c541655080c9041c94080c040000180009421102940c00020b0808044104100401c10070100a92a10f603080301651210058a1000c00b010465a100316080c82d80c50006d2b400e40d0008111491400c00090310a842d411100200d9200703031507038800480c915162440703203a00b6004666204005250044003000030202e0103c05020303000d03075001455150f00404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 165781232 1250 165779982 165779987
    0x90308090d0f030f1e0209012a02150702030a06150503120d05100f0914060103020301051c05010f11030406060b0418020c030f04030303050402010f0e060a030905101d0c01080105010c0204090201 85
    0x5c41c05d00140d401218600e07200c40c0008001d500c181c260700d01240100e440344144c3e415142c00b60214000007484090000b04c1a820441c1013010301580000c00b207024043c50300961001c100d00921984034501c0000c04540305900342110400d50780c011482a401003543c40f041d1b0b541da409507180300d4860040806d294482618004005d8021303040a134000c6400000062400e980d0b80281142c142e450b0074110854890f0700c011000d0348002d0213015000700600100358003240c0e4102e402c800c602c1c0510700000b14120080082c006580c0c4942c0b00381c031400008020b01062018620503d0020030052034103d103002e02d44265240c04144085550b4880c035800304818085110a104491901906000b5540e4598492030f01a000308019142030740080d22502c101ca030486d000e81c8411040c14802800e41b03040483c10f100c21405850b008404503000c0c01450303d80f0400e83c0c400c1c007924100140e41403440201c03a0701d00c01002d19103d165428241003080140c0108420790708420110041601620f010690321842d0005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 165782482 1250 165781232 165781241
    0x7060e03031b060a050c070c030f0f141b040212060904050309060304030f0e030c01051803010b0d0317070201020f03010902070305090a09240b09062a01090308090d0f030f 75
    0x102d440d2a40c40c40d000012464000c20054403c0c8400001040282c461007401081c5009048008188504094043c80803070200601e1900483c0b0407541003410010541d5202441d5218801c924110303440302410801c21140c0000d600304000003a102181030104c0c0381e0100c545a07101400030750165004d940802d045c40070a1080301c840c05006014169603080c9131900030b010001001c6908001844c04003107200514020500c48100c20b0145c1d42c45040241c40344651801d40c901c907440380e915659510b038401c42620307203200c120030003806030b200d0b024240301c50151a007250000508000071648100114150749411a080c1c2e030542d14040700041c2c8038182460262900d105010b1403c1d8424000c98000651a0300d5400c8800c040c03402d100001860b0b03200186003034480781140541901074200380405002c500b0140007424108e808410142da004003010501e03110510540f12840050351070354010028160004461a000110f4100401c250002c140f0001d004040c3e00400f05c040644407503078600000725a801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 165783732 1250 165782482 165782497
    0xf1801090302100b01170708100513020919030309290c0a050709090302030409020f19080702010605120607031d010e07090f0902010c0b0604090b040f0201081807060e0303 75
    0x20440d00e542030030003942c0c408040c0c440250103424040d41c1c6105500c40da80d00882d410030010340d4601501c440205a40a902c01401c000002415400000e01582e4220300350f400080070800c01030b60380e20401d0034041850a2a202100c0c1c11400c000101700181d40070501608841c08044041c1d05640c2030784050305c00d28885581104007042c01700342086000b20100d8603040d254401e908460404d40c0c0d41904006036541e154000d00942c10510040180c0600e90700200442c050b08001c82e490440303d00c0000e2000500c000c030b18400948682d04010320309070244150405884200d80788200003010588690360750340024041c4082584801c412004914854040305410381078400900880c0b180c1000039239200100d00c202c8070b0040c2068000b1010f00b6051049412007901a03507454103400b083d0b165451040005040f4a800558414004000c640e01182e4a03000d503203c0d980303644461901c1c0c0001400d01001400c00403041c860010180c050b0080081d4010854915090249910560800280c2140603019 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 165784982 1250 165783732 165783781
    0xc0b03040512030a05060a0e1e06030115060f110303060d0201050c0106080d0f03140906060118151214071b02030703080d06030b070302130611030d2a020c0303030f 72
    0x3c1840380060458100d6031240c5010b55460542d1540c0710464150a03500352a90035003502503001c0c034100301d21074070681603211034083c0000c0f4507020f095900604030692a4031407400240107103100a803040d803054030304174043d01b910001c5065042100c0007884c80c514550b0028181300f00010003d07070145080d04040c008160b19000e94034884200300003d07041a8507680301c000001e141140c0030000c11440600180a00c03004001004a40d8038000150b074100340e440d0b481d69060f24582c00000e84e210b000440d41d282096a44d9034000c0c004280c01c54041034079100001a070420019000300304034075a208009280350340c2565040940c880540c000329040c030b43c0d0b0307410103000c6810018a0400c2983d05070802c00c02c8030300c03800603c05503a840c00390490413400394042c5009504e40000c000c11a180c03050030001070010110b82500d24004a8480100c100c40f0611055150100e04200810107035004001c0003203400c500340042c080c1c80d1b0f980000281c480c4001401e80064071326500c04110b2121803d8035129000b80403e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 165786232 1250 165784982 165784987
    0xd1a0a0b18030a3216060e04090b0403030b180c120112050c04020a051b07050a050303120406050a0603050d020705030606120d030b0301020904090606080606040203040c0b03040512 79
    0x85002025641c4072401e12507040003240c03a1400caa003400070356994210f4100450520010300103120869140c04290075441000c03001e18450b400721418840490307054a2585048070703a03440d25401a02c0d04240010440c130680c81c2c081524041401401d64039441035140c0f0700011032490071000100d503203041d030a20030700580004040110080d00030000f8190b403020002142042e03a40c03009000010b420f0a40010400d42050480002e076023450f4000e07008100c10340c1086402c0c1840100c0c40c1c0390b10b1a039100c01c403507039900c040b00411203801c20405000286c5001d03000380d840e026807880e060383d80d620098001440583c5c3e40c4001850005e003030b88600c02541e8880c00756079107519041c100940d5613440307001e40e5100b40240743c04140380c0c0c50481a035441201c07521016000d0414a2001500105001d20105401d075400b080301c103045549911400b41c03440d1103503400150213410461030504d800c3c40213100318002e0388104140008030340207404800c200c1c2c02451685540ba9200d240c41e50510601e500d101c841481c02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 165787482 1250 165786232 165786239
    0x10f060914060301150905070504090e0a02130c02032b020708030a06060c0b06090a09050d05071a221104090f050c0d030801150504030c03110a060c080d1a0a 69
    0x4581110305071050400354084107444200405080b03458650707802920b4002c0c4401080560880d4016a5001e4801e0030101d042a40e6604038909907604041103601c1e44e00100320341400c40c600114058020b8100300d40400900016100280d5a80310300350110180203520f1003401001c401ca80359185692261800641d09c9803c28a41072a00350029250103194905081c2c011611030b10072501d1803859600441c1343c5d203140d1104014440d6050340501001201d50701c0780c0c2c022010030010050032402d1001c1c2d55515940c1e081506002040c0c04480c040000c1d424821030071b1100c509001444c482c0000e110012443c6010054500381c004d0402007401107030014106000308051043d40c0c100d43c54a00e00a02c180ca13590a61041080810141000c004020400b41701c018030a00e0070006066101122504202d0320b840d440e900c0e42c90160200f6842214680b0035028200080c0c142844000010a4681407078020750100d0390704c4282500403000d44841e015511000000d1008090120304100c450103440303031100545 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 165788732 1250 165787482 165787499
    0x71404020d14010302100e030723040501080f0d091511190302010f11032707080a051b0a08030f030c2205040b150f0315060a17070c03080a0e010f06 65
    0x3091000380d1003907001401c046c40c40c43c0118142113a11000034050000903040040c008100319984030080340126152910350500c0c2c80d0340c4076060107403003600c5c02000c02030503612400d0326084d410307000d20082110b8850100147d05805190305030f0680709007011003402c030048110038030f0070150481034006a41c4850000d010f258040d4058042810100700074481c0101090700d804141c80140c0700484000f45c008140041040030182c11141d03c1496801c0c0c50130160384180d66441c0031682c0c8404c1e0f076241c000d0300e0f9016807010f1b902c06000b1390b1030094612041151130110711603101c0c007983e00c642c2040c943c0040003a030009294400ca0303500d00700841d8040c81070309001d54244020712003800b800d8011403030700c010344040303140241569401d06004600149000f402d0801e1a0700e5400c00742804010b28000d1149020980d2034001810305585660359283c03940c410b503250034650160180107002400b89100b40003000c0385e0711140055200d40a080013245c048400344040e4018407200c610b0060f141c1c038186001ca00000b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 165789982 1250 165788732 165788771
    0x150c1207111f030c080601020303060d0305160602090a0509040302031603090e010815060f031b06070212030a02070909150c171006030509010e150a02041e170d02071404020d 76
    0x30150f41c04019110b0f4001043d00c40c00c0050302c0085c00350348140009074942c504642c1d40c080143c0702c5d02c1c0c0181014040c8030052034540c0300880c111942070700071801d0011428a0003100c40208011201d0b11018102910b0194136841003413041e80c554082d0706580001c0c0741c0122007440040c150000ea100c611f41e52030900546030b54400740b10039180c03c41080465070a1030400140e910865000b40070b4802d2030900b034403034440032170121f94082d0031030b0003440b6080150717541520f412a08034030b51028554031411420002d0900c5903503000060f629180c2950000420b5510360300e07102000c4180c0300001e04031601c2405070703440031030440d80120140c01c2c00d0800c004159540c03642c0c0308031a025107090060b0780b00d62682c1400d80d80c01c1c0341400c0d0194801e13a0480c0650303885482c025000714040100600c0e16488604615042078682c41c101210401c07201d00b0040d9410b260381d546c0f02000d040303024041c00300600c83c0094a88206110f0900d2407442e074070145105640d943e044900959024030104440c4030081000011035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 165791232 1250 165789982 165790039
    0x40608040b06030c0901061808030d0207020a0801050403080a1d060a0b100915051b030f0a090b070c0e0601030e07080a0203060105090f01090f020903060a0902150c120711 75
    0x1d4588000c207001d400c00203060f2609070402030081e0241e03030074000e04032a10f443c0182c0c000700213414110b000034503901c1071009281e944080c49016990303005a005000d01c1550b9035003e03100342e80c50700c42088040395011000d550003c26220000c6804d2126080760100d2a00381c0c10705283d58055076060001d0800c00e5440540010380c15900030900116102050700c09100030310038804400f0711010543c40b418440d000a0404211107070084000751071007846240703135400881742e01e141e00000141804859030000100310081680d08056860011030313568078400da03910f030300c5001b48496040012071510f80c000d4110317161000520341151040c03035132403108507501d0f41c625200343c0c040e001c0c803800469a410b0070500c40d0310400000740711090591924407410021f28401e02040e44159090119044a43d01800400c0c01791000c0785010850352000d0042203a5841070381078020000d02c0c200803100a000c6c022070700300c03206103040d0521505e0700d0340c9040441d02102c0d0320f40c0c010744c44281c080b01c0c030301a07012500068108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 165792482 1250 165791232 165791243
    0x20903160312020a1e03021606090603060e090a0b0601260a06050609090f07020a0803010806070329040515030304080f010f0c0c020d020109090614011704030504030b091204060804 79
    0x1c0310b1100381641c403040010409030041c1c6224842124201248031840d40c0c1d948284121203024143c00348514083c2c0300e0b1303000040007400c192000c1040551500560026140480040c441420400030700c0d81e460040f298001e1485400d00f001a000e80e00480d02503c004601c441c0d4030100c64140000c40d10780403821582e24203004c0ca080f01c0070419041940565081c1d480240404019444080c0d902e011a0300c000c00f880111301c0343c0c8070014006101c44024600030a881c800901590502c20300c007801703451039285107144800b00942d034810500031800304003030851400e070380009581d180c108003844c4000e0f4440c61240c1500c000500090009000202026111403c0000300103541c48580c60038151150764280ca400101641c12050240c600004078100d014814101204d003199103454440030b56415501c0342141c4070b40f0030480005540c1000a241594900c41b003c010b1a24080d9000b811a0103a8080a0300c61504000050f51a220811504c1d0f4601c0200e0351a646942c1c1d204001443d5820407603003100c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 165793732 1250 165792482 165792503
    0xc0f09091e0606050d0f330305120c0615030607050f07020402040f0e0f01050607060e011e06170a080a14040e04060f0608060402180a02090405090a0302010c08010e010b09040209031603 81
    0x6040b191f031040c02c2c0c020040d1251240b05040502c0c18841d00d003015071180080d1030049400000040c0b04100b000c0208848504403902c869403988800d06100008042c0382d07071403407030702584400c13a900400c400d036108149080454036a82080081e284501032040c0c020b4006100050101e41e807290116003108603851141c001105a681070010380e034844080c0300e02d80d001401400740c600007d11903008040440300b0000000781e240c5d0784080d02114800000d0300d490030365684180074006481d0045211080724480c400030080006540c0d80c0b004244075a20b00c2c402086499038003280811480400c4030001c3c00c0ca90001603c50501d400c0810081c80340c0754094081d80c1c50b00c00d001a0303e00780880c40034442e980041040d0b42c010340140896145107001006916403550811078140290340304c2c85a036010309a007100504c1902c0440c54040d0856503a100c02800340103510004110200b84046254150303180505519140c503089001300300139015214403203a043c011a02e06000c0c03820300810103001c80703001e40100c14 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 165794982 1250 165793732 165793751
    0x111e0d0c150507030203070308040f060f05040b0a1a151b010b0306010906150c060617030702030c04021207050d140708070f0915210c05070302010c0f09091e0606050d 73
    0x2d415109106004001d44c00030310154010074003c0c0100750344580241030300a80c1003156a500411682c000b03c0d010b116940d940306000900c140601003e03805040c24804000c580600712004200140707003509036202e0311040134400b600f003400d072040d40d02c0b1591846811129640c2d021840f4003908900c00214028850440005004400ba01481085410902007522281e4520108842141e509a0140d85080c4c45510000381591b103050114220052200030f10f481f944180304050400100d02a2548200c2c01480104542260105c585030417054904010740d4402d1a9010040600b00c1810f8114141d00311038200402983c000c05410f01c140315650300c4030110b0410600548500000d4025000f4072507a034803c20b20000d0148014000c40d101451040300e01000110000c000d861001c54018002100441e0500805809004010304d010310760070f0400340c0c941d00040007403200f29548110683d0302d454141c2a01662501d28000003030122210003400740e1031b1900d01c058115440305c04c80903070703481c606085034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 165796232 1250 165794982 165794987
    0x80702030102070b2a0f0f030a0b1215010b03040b13060f06060e1804050c0f031f022203020d060b01050705151021120519080a05060904111e0d0c15 65
    0x694460b150411b80600f001034400524421b03400050401900581e54440e203403440d075400310b94030f01c00c0c1160002440b51000e4503505074204c1d84180d1196981c5403051062000150142454640c08410b00c1c0100c000c4841608065000e0700b4200c140740511450401c0100e5542d40c01944000c0100e019100180000e182941034500702e40104ca0241c41c075008030307911840c02e10784500704143c40c92000702240c02000310600740d11092000310012882003a40020039042d5042a284031810321008402016803ca2564000c206070900d428401400b1607600c2e2541c6126a0003a0f041e1090349800008940424001c03800200b280401078841d18010050018001000d6850502c0c016540640300b1102030710140d10355034066041d640c80c1d00b10342480300900c65140010890703103040400010346d907580e10050031b010259104845015002038024071051081201003004141c0c030101d188070903207404160304189903ca0041c2c5820705292507018580020344000c0c000e072280220255440010503000646c40140306 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 165797482 1250 165796232 165796237
    0xa020306060907171626130611030f01030203060a06060e060c0106210218070c020f0307051309050606030c010207090c12050403020102070605060604050607080702030102070b2a 78
    0x2945030384004006034690500551a81d08a2024100064031062801e0b9440c1d40c02001c65902d08401215090f0072210707688030003100312148800524019120004032001440c4c04000e00f4030100800e0169020100726140c1d000c031780440f81300c400194990034803c801001c200c41c00e1000340e00c0391040034080741c064040e40c4202022580292541003500001000340303c41600240c00b0b4030810f541e28200044c41c101c0990102c1c0350043c540b07081f0440401c8910400241711051203080c408080380008004416811103480b10505404840b00011042140e0000c1d1521680e500129000000e0788144625980c0582200506e2480381d42a14500d903254001e02d60307501805850700340140d1118038100103465181d0f201c1ca40500c050720301402041c0c0039034805420740d0700c20b68040380140e6001404105000451041d6900402d086075181d01c0d0911f000009461750045e8031015055002c0003541c0d00456900354101d41005074024000d202c54546450404131820b0514008403640d0702a040340d00c0d004552204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 165798732 1250 165797482 165797503
    0x80109060815040218040c060f030c0e0409060609110d0e0102130302011101020c060106080910050709051201020403120c050d03060302010507110418060c110a1e1a13020f03 76
    0x40041c02c5010002220301c0394041c100340d0700151384c1c0c0246104c1d0400e0801940c41280244146403585140010041c4040c404510070b00405d46096501c101c010782c4241c1000000c10300b113801007940413550414070000c20a036401455260f1605840901c200c1c0400b02401c0d80d0b0a00c00d004000e2500303801c0a05090b403141c031449500b50164224141300540c05607466140b124200d03000181006040300f041c0c2d240c5074007a0041004203909104010340c0000400075044071a0a0341c10034042070800f410060f0280040e4015036104138a07425203030007400d0003541510000c0d03801510300c5042e82c5000c0e401603c1c045200c80c4c143c0b854001c0b4500a003546011f8096041140e5043c2e41d910b14111480d01e980303e04c001000101c0354890340b2002400300c14250b45000742d0034540a00c0000030403c02403039001e04504800e5116400a80100301d2441c04551826403e01d250800394a041143c030f48145080c1d01c13000c4d514a0110307048660b010034000d51410740c00c02c0b40c66140c8240c5020841004042c10182d80f50302000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 165799982 1250 165798732 165798749
    0x207180219030903050c010c050d1d0a083603010b1e040207020d02090a0b0108061c0b0705040e07030c08060d0b16030b0d15050606120411060403020402070503030708010906 76
    0x1d140e41070103840b990043d07284a019150240c10aa5441051425144001c650030002100031500c0d21001d45c151042d00d0702c10030b001460840081480c1c5200e51500010340010380f10b003030b006c51800004611810704855443c284441c007820f804003046001886040d208065001c0d40c40c1c0106040d84e401e05a1100b02c0303030304010b440c44403410024001c000282d40114412a003044007507007101c0c0141c4945544d24041c00c00648041045104a0001008501c0c0101440e10901914048100d6001400400300605410013000902e9036604041543c1500c2903502a00d48000800c0400c10026495800070030303042074950740c000d403a4441100300045d030520007001800030b0b1000d03004580c041000c40c102a103801c0070f60070041121000b440c00250321208106050310754a04900380045d43e10070610400d41d102b102101e11909265082074030402c5107000a0004107607440b10011644250f481c0c4081e40d00441d0b006100799951419450015102c6d001940c805020410301c0380080f421001c280110001e603052030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 165801232 1250 165799982 165800017
    0x11b02210904180303020315030601060c02090406060e040b01090e0106061e09210203060f1302060c0f0307082a0d0c030e1309050709141302120105040302071802 71
    0x12011550380300e0788620b94015a80c0074911219240091046840c6000b038074016101c0c42c100964810841100c082c42e4440c2d00040014048240c21118840780c1c16015141d28010b42d0f600c0c0380610050a254100d0005001000200700030007402103d864181c40c2140001d001100c48454060700380d07422400b032480419440c54400d88800c0894021140114143c80c2111005070340301c0c00c003400102d944c400c0c9080c14110140000c1541401c200c00c0e900302c00f200000340150f281210706200c1a004041e40244104400540e116202000700043c060009a0b0742c02d99036034007507601c0c0c01070050b400030561341c0001d003d0841000740d000c0300c0b42e81030041007882c00c090581c003a010708007100c406c1900c0e41c0403818440040c00340c50140d1a01d8181140c1104161310010b0400c0143c01c11520700f078010341c0500809824080c41c40301c0c00c0d512145aa811010304040e50b02c4458003480003640198132101d030124258600030402082c50350000c0c0b054101e50090060300038021903c44084141c0c8a007001404a11001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 165802482 1250 165801232 165801283
    0xc051f17040602070c0b0904060501140d0509150c070b13050607050c01020d0216060e070f031727011b0503030f0c0c0712050618060a200c011b02 64
    0x20308110707a119109440c01484c01034140d40d15107250400303401c645450b001c00304100020b42803a114a901410090074007452110700c01030b01d2421803107070251080321162600301040042c00204080c80494210300311700241840c14101d40e070a25000030000351580d40c0ca80002c140208116102182c00580000141c11707942d40c1c500c0152415407200c00c80c04150b40d420030122000c844540b002c1e001ca200c2401151200381c1150619a00f5981d11a13035200c03060704224001c0043c0e0000400c4001100d42c0403441d100400036440000c1a907000d83c030420840d1182a54640700c0e160710381500e00c910004c0076207444208101201d252003041c0c954910080c03050380100049a00040341c002c00715440a2290560303440c145807024071900349440344e84140c400200b811140c20401c01c0034009294000d00f001e165428400300104c1495a4003806404441200e94a044403034510781c21490000d2220768101070305955000000b0600c0c003c0080d260510901c5042d030905142d182d1010880c540040141400c250380b1602 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 165803732 1250 165802482 165802517
    0x105040204120f1103010e03030f07030b030a030f0207050a0632121f03050f0118020a030f050709150303030f05040804060f090f0b19090303140a120204030c051f 71
    0x4264042c0e8054503040341d02410342d5000d000e1f25080b13021a101450704ea091513281e0000e0100d010b001c840505080c40c040c090681c13400550541c1454044c64018400310480805034204100e81d00f00d5604010b0a110214082d604101010301c41c1001018201c07489003084017202c440044100046c01070007040103040c52001c5400c14003038028800f58075031950340d6104402d40170711007903552045a081d08090f9082c0503202080c40391080d5180c054605c0080b0755210360000e200301e01c0c03e00001304458505001c82c401d2040800c802000b0300354030f8008204030482e661041c0340094040c40120000b03414141c61980c215000e000f402c1c01242d1002070181041c1c20113030103452848950800d8001c0002055000920440c018060401010100c4915503100107544c1c2c6403489042d5000700b00140300440108000180d070000c030080c407000c00d0501d125116011400c045501e408041060400980081404001c0c40a0150b600c01200c00842d00f400007501610703d40c00010f035507a91074601140c0842d8010300103c070b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 165804982 1250 165803732 165803753
    0x815090c03070c020a09060303080906180c131b020c040f0b09280903051305060910050a0306120c0f051503060607060e0a050604030f051e090a1d070305010504020412 73
    0x600c01852142d445890381b210380c2c1100c50a603c1600003542090030701c04002030500540d50030041c0a54011600301c880e52031940c0e52135001901501a480712001c504038800303c1e13800140c146041c082010a80c40440ca4000d5a132407000030420300c203901c4d103481040400f125200b040f200080c0600300c1c01150303176030090313041070310550500a0b0900111242c0d000c40d090031350311800d0101c0340719403681070716513181a500304503003a400d400940c0106020401f00c02c0d40e81d22030743c1c051080001c80c0350490b55034242c01e00c00c401030326207940207142004090f541042041000c3c0e81c40d009880c0348496424000d541d8a00f00302d140304050301c0c2100f01d00c400300f0115066040000080500c00d000d2000495203400b600d90d254030f40840c0c00d10582e11078101718140310405130700c2803540300b0344001031030705c02c0c181500004859107000441d00d1441030358074000382006040e150044618001c118000c110015028030300c844040345003088404c500001e181100120329864503100f524266141c03440c80305175640e015500c0034202c0d0b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 165806232 1250 165804982 165805007
    0xc0f140903010b18010f050a1404052511010c020d05160201210b01140903030d18020d05030409051014060a1202030c040303020f06090d0507061b0815090c0307 70
    0x155202d0140000f25110400041c0002c960250901c5003581340c40d0340d03201c0e400501d8212034414001880100700413090f240e04940410310407030b00051141c844400060490601c015114003200c8460ba9801c00380d904915040c0e030014414000f8001141c400c6c0741261038100034040b0314041030050150100b4000210070b03540d0680d1041c102031070030003054140c81700c1980d480c0000600d02604c801c442c13031403560310079a44455492030008441c1000fa001d00000d0700e0340150f0643d0961941c0e650043c00a48445803500380341150082c7c40040c1c21440c0e410090703140c1c2d10034003c46a0041c14000850548140d011f01c080c111000c101241804c1000d00c01003145982c0041d640008124903201d4640c0c100c9081c0c0b0003180681480c1041690f518a10b00d4040e082118184150007150030a40070080d8403030011550101c400034501d0155914a00f9181c40c030003c1c407010041c4120904266010703090540c02480e0740c1d004403285011818a03016501c200b0524940c200c4403010282e105101240000c0d01554420040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 165807482 1250 165806232 165806239
    0x5060115170a0219030501030b0109090215070c0518010302030d0f0203090307080d020c120307080702010516030305010302012007050402030a0603050102030a14180d0c02061614010c0f1409 83
    0x280401440065039410709035058880c540c0e0008042450300200c0c40c2241320004a41018462589541c95401e00050b05218090035152541c124800319554242c40308040c81c0724202003a03c0b1000340c02c081c60041102c1c021030303000d617814191414078400c000749030034100c950090040503003502500b41221010b0000c094142588020301c58003c5590f01440210040e064860007003031003005e0420020b28240540e40702c24024444050401213060000c070071114482d8000d80d1090b6605441e20040b80c0034840e0002401503d4400e112040400d6490340003141200e0007680e880400d024010360110602d558100503903503560003041c00704030b2814903030041c6502c0030703180034006807450780c9489413400d982c0704542c070740c1040d0340c1d40c401d40081b07140507050507400103011558800507010641c0c0301c55903415606200b509101c00b46c101c01c011583d651003110740c4505441c0c16888413048070725055405540c020700c40ca240307500b0a1008001e80d44902e003900807001150703132900000c1007028915042c590112205a40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 165808732 1250 165807482 165807497
    0x906070908030f09010c0b0708040b0601050406020a02090907030c031406070807020a0b04051204090b15040515071e21080907061404090e0a110d020904020906130e03180306010305060115 82
    0x1c9070f80304031f1203803003854591241099494141342070640220000c0076a030501c00184400c0c000903a00150707000c2500d90548401606480b100e5502e4039190440d0300003400540d220002104000e0b442c080c0a14800c41c0104a5280b504c41e004147c40e900750440f042c0d00147d0100444401180304450603e030001d000d41c05645100000c441700903003e91080d041014110303115200820b083c2404202c806c603c5004041090a281c10b042c002080500d088210380940d80002c10100144268546691910803400c4861140154a03251205010b40007054016402180380c1c4c1401c40745000b9a40d080c030401d47d102c050300e42c0314240042920142ca0403c031a01800d01e0078070010403010854842c40d00d40c452018010b208030103561410f0342c000f034060310716680036003043c0c2c0c0550010380f505107005802c2035044804900690320741c008280c955204c00d00c2d00f284507003031135440d4160400110091240000300303034a103012200190f023403650310b06003880000d18a030300010041101d4040146500da45c03040c240b602c43e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 165809982 1250 165808732 165808757
    0x23061c060e090703050601050a030b0f0a020d09200d02090109090f1a040c1a040e1306051504140103020906090c12010e07120c0806190317030906070908030f0901 71
    0x2401d840781100e8140281c0e01c00301d000d009015040020034010b040448400300c10710305565070f03c2800c03800a070011444a620703c1c00710740c02e03070b0042d0103440d4103801d048070800c401815800c141c0b81c040c6c041d81c0000842400c40f10341070a04e04250481c60002c0350060a064400d17487e00e0681002800e200c8410740d5642294160200090b003d61480c00c000d07402c0e0b000c40500b034102424031280192483d0300c1902030600801e81d030600301a003003040d1401c641e4500c61002d41551201e01c0814007d504201c014480b500d0482040b050000100c99a0008082942c04210f2188803290311210b0b600207000182d803120b00034001070300d186028000345520072503003040c8905013245180301141050302038000e4418003568104001400d0b600280040d461001c21105021540c030000300a440c2d03410250405020f446404c603000411410909410021540260b03000000401c1148155240d0420390764000c03e8011040412041403107800e40009441d10140594035150300704540c5409540001c903c40c1c14001c600800c0d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 165811232 1250 165809982 165809999
    0x708090d0503090309090a0507090e090703060b0a0b030a05010e090d05030114010e0303070b061804230102040b0f04090b10080c09030705121b090c0a11120a050423061c06 75
    0xd80120403480d00070506040c01c0794003800000c0d01c0d812450be03503040c0c0010040d0301c1e800022110100c0c0e80002e000590704c030340c28020940c2d01c4442c0e04100e5800c1400402d221103010b01d940218100c2d44c0440c03400d015074a8000380c07562a50031401d151000644c4c2480144455001070300110030110050500d0960a1040c00c00300381160004001503482e141e1100401003113081900c1821100c01074058006a540341a5440300f907e80b944442110281e402941e40002000003541110041c22002000c1511524901ca264407964024003071452031600789800e0b02c505060034280e03c00070741111b49a00b1031030f0b40c0d110003241054211a400135414070601c10001900c2e01c4801e40c44403101465805030850b5004091840f20807510b5141041c0594001810810780300103500948004c60005d1a046440342e120103c05441d09030b04102100c2203843c00103805c000c0603004030090003103078820924050440d010000c0b081111040601c0a07070849000c00c4001078420180c042e407204071903246000140c0300d4a91810 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 165812482 1250 165811232 165811249
    0x1009060305030703082802030612011d1005160c150c080f130b010b0a1701080a050d020f0703110103020c0a080d0b0d1a071103210708090d0503090309 66
    0x1950580c00000f60b00b0103159000082c280e00c0205000c5403a02800800e2a0000300c0a40c1481551540d41c00310129006a03900c1522000340300030035009204c2c0c01410700074145030495140c143e803094412502e80c0c0d0070280c0355029580c4100c40051581a00704045501580e460340d90740c0c1c04465410b405002c1445281c2d0a00c24146001100d0350358040b2481c200d140503080c44400341c24810100d10b042c42c0d07100000e004020150648a03402881038a400700610705646030f60602d00748502c0e0031040e42c004a9184000130302a00c2090041d0102e40200c032046e101030b07840d605039800000a90f081403105001181030320402c0e0442003010f250052824036011212410440700d0f0200f1603001c2c10008000408240794003030704040d01002c4a06240c016401d80d24580c1618400141e40500040b00e40065001805400d0300f0100355900f00513a566240e00001004a1080c2c9515442d83e410050011900c5544500700040c425207083d802080c104001c80c0741681c16410042c104001031004100740720701030721460f40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 165813732 1250 165812482 165812489
    0x30406030507030501080c131104050d051c170103120c050105090a03020106050f0f0411090d030c1b0312211a0f01051303060e0304030f0b0609060102031c05100906 72
    0x500054505102000505581301a0b000b031001d40e004034a60b00650780d030300394211110404010006030300c0c040751602200b203000741c0d07002a81c4100c005044101340701e00400e88642e0700712941c50900c04e0100c07142c8240c443c46141d110ba40f2908222800600000d00000c0700742c071048415041a10f060b1f44030303070707076003801d40d14100c44107182d907045810654101602405a8001380a00f00d4908078200410008a88030300c150003034162080d40c03655600240d01202c1022240d144001505400340c41005080152044000010884120000c50442120481c3e42c006d03480c10340e980001e0548881241560442d03118000c2c00f586d10f1104c0441000c40c0c0011a2171064042ea000281400d0b0000318040c4e08000c1d000b614110b0547c18050200f02c21a0112004180002645d5000800044c0f281012084501d5400349800007003484401c5001d50007403103c00d0102e00d10698041f96214004e0b41c42c5801242c40313000320b144802000d140410901301d00c4420390040d0b940401602d40300c0701810384e2055054241ca1640d030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 165814982 1250 165813732 165813737
    0xf12090f020312180f0a05031204030b0c030106140c01141906080706052a120702100201091e020f03030417070e2701180c0f380c030406 60
    0x205504500b030a0020300005510305450606207085200700d5030f2080380d080da490384540001141100603a82d0350340804050100a800c03948144c48040c540c00c0e4523030060100303490500e01c04d0001071009121804490680d00240d6507408803210314264000b07140c018003800305441d500c419042015108a4082e44d1081c000d070b81046400708050a10903040318030703d130801406038110090a20a440e00f00040314110146a11880f205a12000d2800f01944081c1d203030056a0140c209908a583c0d00040905040d80c003c641030741038038580d10816402c941c291a0002c0100c59245101d40700d0049540807814142d001403c0d1050282c441000a410340c0d02a8102400181103600b2921034104100b1102000c1e05c0c802040710210f0400c181055000d034145036144924400401e8107980c59002908032920056001902d0a0141200d2510b035030010f0160054903e09644880c2c00510509501c9801d9003203519181d07083c104120214100c0e0806a400011405503182009521f41c421400c1000340006e01860703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 165816232 1250 165814982 165815003
    0xf03060d1202030d0b0301022a0a170a1b0f022b0f0b010e040b0402090c04090c0f02100b0a0302120a0b04060203090118031205190207030206011d04050d0f1209 70
    0x150060100c0d80c5c48100c25002c0ea106011446e600007a200422400c0c4061004150703402080341102c51074041c102100801e5450031500c009031b00715440d03014254400b042e4680004a40809481c00403042c4600300280c403071410085407001600707010070103c001e00c0d0b5594210f00800e80e0648130940f519900c07001250384072422800c1200f8458440d40785800341c0f40080145480f800e05132a035a083e1440948081e2241b4400404a100e034440e100480e8010001c41030b06012881200d00040c0c00c0c01452401c540240c090760a59110710000e612406800c00380c0144020340407400d5800380b05c3c1040d00107503141040e1080c14690008107020108031072003103110301c2015a03249041100c41c0d0075a00c5200b54030461000e0601c406d000a074000303100110190b90854001303500c0e034554501d110307905040c9410025071480083c190080c50345c04180d40d4140e640510204442a030030419001c4410800c84026003650003001110132403e00c5044210140d110901d81103428044c1c8404400071201440750440700d00c88070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 165817482 1250 165816232 165816247
    0x19051b0604140118060507030603020a0e060406140607060e12030c0c0c100e060a140d09140303072001060506040f0e0601080405073003081b0a050f03060d120203 71
    0x1003042c50410180e040080c0300d0b5020745910011408100300000744203503203510021724182e110794004d60003103400804401d94246c0d03a00759505210401d1361180d0040b030a11201140c1001c040221401030000600041e1604d038082d04d801c401003005000f01560b0303003d80f0410500c0b149241010b1805510142e40d140d6550056914052400881002d0540248042d1800b0b5510a400901d0102d91000940710036550f20343c281c400301e644040000380010446004141401d80b180580d1010b00080d11070044000380c0d403041c1107682d83d6404103c80c190001100d103421480c602a042032848d95050001c80041039142e194000510350b17800c240c01401605072038241c04c004800e0b01e03284944c0c00c00ca0a00f003000e00c45c20181c0750703181c03503c0e130a019400b0400901803144140303645901e106120f1111031880712215030341915008000c01c40a65100c80e20007110f01070010100d1005044a8005103a038176568540061000c2007811508028002e039488070b203021030903000c940d2010682890004a6028541d103912 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 165818732 1250 165817482 165817493
    0x30601020d03060506160503070203011b0e240c07080613030807080403120e030403050102030c0301300b0a0e190b010f050d0b0c09030a03030b090a05090319051b0604 73
    0x6090380ca08080605011082100e03440303000803228011b460701200304000c17840307081440c036611543e10000c0d0150301e412000c418003080c0c003994400ca0407948d500c10661a0026080200ca103020355242c1c080911040c0c40402c0d2850914000c0001d452281c2c140d54445560362016800c1481c00c891030280c104012001b50109548000b02d540c1c099200d04003201d0908044c0c03001042100e42d06207c0030f503250b4414503403000950400980380195030120095689142c5155000c0458000b03218148950b0080c16581d0542d07080c4011750142590004d4031a0b00304400d54403100039226010305903400351175460300c0903800c1c1041031080155180540740c1885480d040e40c40c1c040d28220301640181c4109404400a01c200d41d545215070822641107000e001180d1a5031420340c01912034844020340c10303c22071600004041d0142c003c0c10084200311404040c96032070300e00ca134041d03510844102c00d03960000c0040110042042c004002d160002d464020708004403002d00c1f1100c0000c06903030019550216041208210 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 165819982 1250 165818732 165818743
    0xa150203040603110406020c0d26090301050603070305121e070501051024030902041410030c06080601050301060804030207031b05150405010507240207060c02010b0f151308030307030203060102 85
    0x41a9413891910349400402501c03180142c0d16244641700010400080c010021002c013044220003d403491120031080c2d17248050b80c40103c8140c0139500b001d0010b0701601d000b0501e682280e4021000e032a4000c080d1441c101e560744504200105c46120103101800d401c0000003a22002c1e00c64800003c4d613007405422850358014a87c0103960185001c185214034200c4a01e240d0315100f52410041140c1c1c01c281700041c060504400c01050b2040c1040c1000010818a12200210390190301207040c043e0310341c04202c0703103207a00301c6045000c5001003004000d070500c524071841c0e20034001d02c1a50203290f22691074481c41c1c010304100f8042c42d40c11501c00d2002e0b2030102403600455600d601e042d85001d00d41000a48103004428000c0d110140c1c1010030711070005450341c159041c2c0c40c0c1c2003086590301e420385031a000602c001c401002c0190f2800000d00840d080c1040004401c0c0c4e4010110800241501c0c1d04482a6120b10001d01c00e88000301030004031000104003541c000c1c05580c40260710392600b0301c002840e00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 165821232 1250 165819982 165820001
    0x9010e01020a0e091b0a03110f130315021e0315030109030306080d051c0c091706011a0309060a021b101a03070b0406030b010516030c15021206040203060a150203040603 74
    0xe15070000c3c107a6071003000500b101c41b0070f40d007420045540b80c1c1004241503280202da0b00224070359800507007070860407520101c003010ba912032003680c2010203d9900c03290884c09110440b604500050380000d10b00b1180d08051a4032158501d44249084000e1011070700b13440c1084012408207840355018810071109100703035076194055280990406108032625a20210204480d03801700341d41e001e0040f804c80c40390480d8405010a403510414012084071a20f6450350240300d482c40c50f0035066034100a2554007022070307016900e81c4000f03181e50b88880c8400802036000c510203070700c1c1040900b5140140102441100d6800c0c100760300020318101005900e104022907581c82c50b00c01d8202c80d90034450311a0030707000d03102600c8481c80c0000d0174000b10340050303c05100f00d1007961000c0410300e01200401d503021300b208410324411304c1c05d405000d8030812008240c1c01101400c80b15981000d0000740c05050a5002d50352121008082940705680c0c0e108001d0040003841008005810010302440016014024002071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 165822482 1250 165821232 165821251
    0x2040603062a05070201050f03071b08030405160501051e160b060a06050a020604060e0c061c06060e010207181d1b0a06080105120a05030d0b01020f01020c03040e09010e01020a0e09 79
    0x1400e03150385c00207209109042a0b10074490b804000304002a225403010441000000180d01c1e0b45940e13418001039036041201d04950f1481419094510740c1c0f410343c0d04004076070040c1c4030715040101c0c2d4401c02003003030b905d0700b01e0780e00110060001000d260002580c031710400e40103400712015800c0501c00d2110f00c2102e0740042c1d091203c2080707901c4216500080d419802900b040e80042c1c003e10b0500340505142210503490780c017900101c0c0020300a1050307510043d115810003810401180d47d2481904d030240c0d07812a01d0b0258200d036800300f000c02041c001100240700040310024564158004046240b804800c440b442c6034080c5028080b08507214000d0103000204035a0440702500e0071800820b5820140100d81c05074041a540000700070042008100d80350b4040306403034850449204441c001c02e5065a1580144505051680a00710605c01c46140d140c7c0700020714600750070030310861a40100601024901c1d0750781c80328000e40200a102400b003a458554810014078688803c018219402900300c400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 165823732 1250 165822482 165822487
    0xf03020f060315060a020f1c0e09190f02090a03030c0309120c0303050913050109050907050d0b01060c031701080106091b0206071b060501080c120318010c02040603062a05 75
    0x525181084100f8210044031003650701d83e01e00100300c5c03c1020007031242083e44501c0100081516003108541e140020350b90352080c142c198038007002100c800a071184050800d540641060701261600081c002c5a482180540f8006000c4042600341c0d400d50300503400195000320711400c0540c4440e900c001844403445c61207000790b00761102418064984001000d1010004480e074031900d8100c5800c0e55120302100c00c01541d0b9541e110440903103422902d0700320078018000042040d2800300081c0303840365000300c0343d60300d642e0902109454940158006409105100740202c1042201c601c10740d010b002d20100100f101e502d0110182d06891105c2c5a6400b40440401940c0b6150b600080840e4056400c0c03501c209090745200b00618007680301c00780504440c0c01c1400115100c0d100150003452800151550b0b00844540503a25850703000d100750580c0301c007201c09000c2840398414074000304420300007803000414560326540d202c101c406810241d0300701c0c40f00c01444c1c20721840035101866000b026003410ba1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 165824982 1250 165823732 165823741
    0x303050601021b09130615030507170318011403012403230a0204080d0302040312080106021e101e06082404150905030c061510050309160f03020f0603 66
    0x70b10fa00015100602a0340400001041e800a040134902002c3d0041c0e4100b12024039480d06100341401e42c0825a1b06116017103000440707107000c0c41402c0044030410701542c100b802244004000c10b8003028251b04008050142e001195004c0c0c00541c020702030001100e000c00d2000c95040141c0010032010010f040c60640d0901e01e0410741020b001e400080f02d9503000e2603a90b1b0302908402030184d0b403c015903510490211020301d541603401003055901440032181078103003410044032400424001c00005030002400c10f00803005000120900d0b00044082c0c0314900d0103500c02d0403c0b03c441810254110f00001d803c808020710702d01c9524041d1000502401610040c001d440740b030883c800d20f110a03010f06040014051003507608580030050f800e1207041c000c0d12658184160750f0307003001881080a01544e000304146a4850b21100810b140c00f4220b00402080d40c20142c40c0c5400043c4640340c0d07800303400307061039984004d10ba510010b4000d11110000c070304c1c158018030048c1100e07641c615006903410414070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 165826232 1250 165824982 165825013
    0xf010609060813061b020601090b0d2303130302010e090106091a130608060a0902030402131a12060a0606050f0d0b030a0510060306050703090f0308060d1e030305060102 74
    0x60081d1000c509204030b490311005254818102c100308054012482c20490451004031007030030000e4060207078200e491590301e03001004e003210311001c070890740f0240074482c140c00209115054181000f01154641003d015000140e003194003c1d1040c006900d2902022320440d038026040b1807210b039058481554070740c1410b40180c0001c0c050700404d042d40074020b1011003d096040c0403115a44000c4000d0341d08586d403030202900c440c80580d01d60b41300c1c070741c02500441c103e05940300b660320454006001c21200100d10000d20010305400c190323004c4401c50203080c072240d51240009405201c2c0d9400080090345488501d01041f0758094001c1d04c10060100f0800010b0041d4900380c80340d040c1c500d8000250350740c981e00003030300d4201c0481c0010b100d8000d024030380107400d2590f404201101d0040005002a41d00d000d0b00f141102c0054000400308010100c1d0301c40480e115000d01f540c00702c03024080c204081c9254581040700d0400010030990b4031400351020042540c1400b03500c0d0411401c0c001041c42540a1102 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 165827338 1106 165826232 165826247
    0x1b210108120c0703060504030c0f11010305060a0f030213060e010b0405040c05071a1807080105090f0f0703060c0210110c070b130506090f0919050f0106 67
    0x8031010700044012514980e040001411000e8150b90f21a4024840500300741d04001e0300580751000160040c10464580e030207050419102c004407000101903070300041156000b14261720041000e40c11904447d0b00b541e5040b9102c002c01d1181c6100c40004107101c1d4810225100500000501140408010815030b002902d080c0620607010201303807214802c5d0344000b0125140b240c2004006031200440070f422111104045055041420b40e01340b070015141c00203907083e507440003400620242001101000100100900717580d508458190340c68040d507100c054540c585940c42090704078424041c0400691021004010380160400400c2c15904001c0303041c441e0303101d40c010106095018405813003500080d44000d0854605007000d03c00399170404000c3c181c110007000d0400b2250389c3c421400d036102c0e240280154007806030f00c1554800b80d4802606084111081d0001030040e80d074410304 = true := by decide +kernel

theorem cover : BRFrame.Cov 165647482 165827338 := by
  have h0 := BRFrame.cov_init 165647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 165647482 ≤ n) (h2 : n < 165827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
