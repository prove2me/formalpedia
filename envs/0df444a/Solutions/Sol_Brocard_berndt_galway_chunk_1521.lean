-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1521
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:23:17.903549+00:00
-- url     : https://prove2.me/submissions/0eb0e623-0b7d-4f9c-8f87-85141e882018

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 273381294 ≤ n < 273561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 273382544 1250 273381294 273381299
    0xc0f06140313050109080705150c0c0304050d050a0c0605120105090106050306040e010b0301240b030108190501020c030a170603010b150a11060702060405060906191112040b0a0f0207020307 83
    0x254180c0b1001c02c821900b554a80b6901000b184802024007421030042e0050903901025070404140b4100c0103100e001c0c88101404606181d031000401d580035100306980d24881c9840d40d042c10391401d200c802c001003c114040d24041100c0f6440006490302c1541e4501012069898104008082c0f00900901e00004d00c140700149451a10fa000200700c1d080e450000601568000046801e4560020030216805818901030640300c1041c40594000c0c201402c0c1c4a00b954185841c03a501e480d40c00e04c410040f43d408905400078040c080d8102d0390540154000c4070b96440e246e10b0080c1c400c103d1298145d4072000c0b83d500148540c201070052144d04007000303000070250f8013a026001d426410072030007003081026881458411603820818140600f440c0e400604452420789415450800020a10300e2660480d0b02800b060320320480c0d045400498102010519440c00d6260b60807078011080e9002074001640140420721288168141c0a114010001c0c008000031162401c181d2080a600940507400102c04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 273383794 1250 273382544 273382561
    0xc1504061112030411040207050111210405060601050a02030418091a1611070e0408030f0718150e0607120f1409040506010512070315051f080705090d0c0f061403 71
    0x6a89200020801400c2c603641e5202e4500711990b4400049290400080d402141c41c09074034041ccc008407010280740c07158581592680d0b120440a403c03981806404a403a884041c000d1066a010340100c001441d40140e003910010003501611038265480140d43c0d102c8030f404050740c0303030300d511030003201c096880c184402000485e010115141d000d202c40c000c9041c081030384e10509004500813400f4454450716410107a0001800103000f0340400140000011a400c00d00e0400e0b1819044800e0050b04294030340e00c444084d5410104112000c0d0700000014070b2038200300c0c074030145d160520306560390080303680d42981c000d44407003000c1c0c00100729400080c020070b0b02e24609a0051b6a011506240482c18094120042140e01e842910742d100460380712001001c004040e602804010102129003000601030b103c076103500a6000203e8204002841c00001c030068001e400329442064080d01d034034079041c401c3c24880742140b441e01500450032050b5100040d101e214206001044112140d030300e1071134469a40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 273385044 1250 273383794 273383813
    0x506160801092706060f030803010f14010912020a09090305070b070504140d0615030b040510090206030c0d06210501060e040519050c0a0f030b0708270c15040611120304 74
    0x4135039161310b8060103c0e8904460240000039480f80241584139410300305281d01460f01d54000c10201114104440c800381c0c1d100402c036048030310018004130003105a0001c203010038074940002c0c01d00c6080995a80030142d11a00900c01d440c01890100301c240c660000c110b85900c03039441000d102015204040d40c141c500f4408401c1518802d500001c2c1903818108010078100040c2d1041d03844c6034075102040181300382402080d80a480040c0c0422080d40e0981c0020340c1c40c000980b17200846000400c1d00340c2041c00c50f6008002501140170072680542c1c1d00f440707922981c1d0218404944a50808800045920350809494021507114028140d4040f1231000e01e058500008429100c610400c0800c40c1152180785400025061550382c0d4000c4908500b002480b6400182c14030381004800c5080000040c8440d006001c0882e40c04400241d100e070900b0018900240711781441d60100e074210720003100d546a200203200300d40c000d803a4030124182000d0b00d90345030a188015203001103030800004000801c040c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 273386294 1250 273385044 273385121
    0x20f011b0b0c0c100209181518150906090112170307090e01120309030b060d06020f0c0f0613150e01090606090f02090303071707050616080109 63
    0x1540481080d941c0c607402454401900c10580d0030b400024407000000040c05420120300103100705600e420041d00c00700d008000700e4000d100b80750b82c25501152a0b2032501c0f407034150f00280282004c0d0701c081c0d4402042d0201d4419a82903030050307113140011400c5d040414446208120003071103261244c0c600450020200c0d0340920403100c0c0c5000c007420000304441503001e07500807421607441c407029909000f03001b241900c042e005401442c00c00781884000980c007445500a99601c2450311009031030b1a40410403101d61810010320b018008904d030054450303610090083e5240c4041110100403014540584134401a039141d5030140350b0703104060100c0c03040d1849414816946000050810114000c03d0031207080d40c6088800720b403104070070040320500e8001c11001035002e050861a2410400c00250342c2d01c1018802010201e941c01001e1094a8104c103882281d43c001d01a00e0582c90000d46502203405c2d1000c2c120003060003440081001110b620820100c1a0001c1c440c0c1d08016400f000355100b10450b4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 273387544 1250 273386294 273386327
    0x4020f041203020c0901092a020f031206100908030a05160816060c090501020c01032003090f010c020c01050301030b06030a0c06020c040e0102090d02060d0e030a0f1209020f01 77
    0x810000a68001461456201e14000da003e007140c0d007002010003440e440d042c1d0110000e5030a018856113080d54864a10380d00510f00c4071081c60310380641505909004441d003608005010119142c482c44106414881c85207004440c20048000d028030191221101070150040c613503c1807094040040c0114024000701ca181a8403010b22030940e600c106596002c4c0360f008078a00b403011007070010000d043c004d01100070003c2c20000006403c110000755a401d440c05036504042e15014400d90941034130209941e030306103e1090903924502444030f1541c410307a0070341b81c517240d41c40c1c0f8108007070740c2e403002c01c9810161105239601407660340b940d201c090000501410f440ea060003031810210004031081e82c55001403405401500007000004208001c4402c3c524003071320103900400c80c55915540d08011406420340c111401038451210419820007456106041201403000246a500260700003150360500302060756244204000c812202003910030b03041000390003000302152840329600402c615901010712 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 273388794 1250 273387544 273387547
    0x316050304050a060c031e0e1003140a021201060c0c1205010219020f0d08040507381806070f02060f0903070f030c050a080712150c32030604020f 64
    0x60341c0016100030030325030220002c1744802040100b0541c100345c018410780c0c1d91440c100a0b0035070034107010f04081c2294410a01c94811038044a445174040c2d404802032941c42203501c4035601e40640284001e40c400744a806869184d0000001d01921400d200340b0210752200c1c00c2347c0c17000c0c6070190b11900440c5080d001c441c103540078044492000d904541440b00741c0429402000b154130624102400c1000003e040340c1008064020030000c00c00000340c400807960b9400c4a0243e446c8684050482c0d0040c2d8400032420966180482c0c80c1065050702400032a003110402104001d403200800190744542c4400030141800d460800d005468002c0140c251031000c248000c0c80c004035a0300103400c0c171100740c0104501051041d4240140000403011501800c3c050324443c1a060402c05007a544e200a4400c0300c4101141c01c1c2c5400401c122401070141d580704072581481241184a0064103040d0041f0445410140c5041c07440842100e081d100c410f11496420050b1550315108140300c041c0d0700808040354074810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 273390044 1250 273388794 273388799
    0xe0f04020903012912060c16020d080304050105010b030402010c030c021908010504060f0c0c1101020304170102031501030c12090f0f0804030524010b090301140a0c020c120316050304 80
    0x4013030080c01459185180c4405081c2001041c2191034421402064080e03040740d00f0508040c40001031803600106d42808840e03c0d40b01e189000684201e040e81c000b500030b411607001000708400c04014600a510410081c011681c807114582c0d6140405c81e0041e00142c05804110042405034071910003107800580303441c03010800e194500754081410340c00010700d0780d95001000188104e44c40390f03004200e9014001d020364041640300421202720220b010307105000815000d80184c1c020000c44005110000141030581129a6801e000390001c8a48031b00e05060030489103000c0d03210384219001d113103090f114103403070080000b40c0700010304141d407040b100141e5416250000c101d24403507403a005403003901415601d50940c54903600b00700c0300644822000c240e02004e62003011001180300d06603425001c60544a00350940040c0c003500e6018156400000c40c58148484a000c90b0080b5090038419002c41c0c40d07a15901d4140161a100c2c80500800f81c4c00500400540d030302d21042c111030300c9000e00e04032801c0c0354 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 273391294 1250 273390044 273390049
    0x1715100207080f0304030506090109020a031719031a0a0317090d0501020705030a090f030206030c03060105090a060809120f0405010c0c0905070e0108130b16030f051801060b0a0e0f040209 82
    0x9440f10762406241c2e00200d820010070030108a010f82c440d0101009116091055000c1172002a86000041001d0000d9603d0351a15105006562a0091f4850200419605200068001c003200e1400c0780482c501041d00038480c2c00c04c600b60381c0403a0b0340304072040c1031010820104032081c0c02c184052a84a0100064000421800d00107030048500500c0a1980d41c00c1d4194050040c061a030f1000c2c4401802200405c056a6a00181c0740e00641001c442c5d5565502c6d1001200c02c1c0c0300303204010f070f03101000000c003080e81940324803020301c6504404100c030351005014503400241c1c001d108070708130403c20802c001c0c891035210b1404a40c000748500818400d05840d425800143d50f0b084413401c002075222105959075607842400c09070800e894034100001f424050b01c0e00b07148803a005095207a01c90018109600c154800d901003010241362140401031410400d02030116001d0180321981503601b000030114130100c03180211500c04aa03911040d0b0030070407880070301003e03a4900514991041c2c2c02e0000841e8ad4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 273392544 1250 273391294 273391303
    0x801090b0c03180703060c080702060106020d0c0204090807110306070215040f0302030c0709050f13050c040515031204090b0603011d0a02120114040e0705060904110403020a060f171510020708 84
    0x11740c483c41d4049007904881200520381d6100400710700841d440724004016040d00030a02600404081c40c00c0915038800c3e001140c0942130f508170060842d80006a031006111005054844081c0228161480354071400801c9a81d0190103200e44184c00807200400d0005111100d1019458400c0c0107807420300e450b465040381030801d030b40d101c4072149446070f041289500081c6d10f11a403200103c0b0b00c0c0317500146c907600c90720303951801540c3c9140070300d81c1c0f500450000c5440c18058290130710700030100c1c3e50211641e03a8903140c0c0d400070301c50070620303d0400704000243e10740802981c1c10380701040c0440d401504145c0f12000c0d005d101500d4400c030310790f08220462940c003800b49801d001c0e200140c0c468000925060600c411200c900032046416080914140b185a403000200e800b04a0201c80100d200034494600220074800c55000030b40c04200303094001003e54000108440160341500e1f04008034220524400f4200030440b18001000300364801d001c01ca10b003220200c03580140300d10448106a4039006400d250 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 273393794 1250 273392544 273392549
    0x9140a05091e010f030f0b130c08010b03070b03012403020c030307080f0a0c02330a050103021f0207030609050a0501240803090307060e031011070c0801090b0c031807 73
    0x3103103100b200303407280c540c1292101d9004040c0c0c0e10503c1c49451030b58403421420441b542e001001100f510002c44e801003108014008040d4004824620302584c46000e035000b441c4c101150b60081c016140f0004508460100783d074100c85000d031291100c4c2e000c810000e192046521404014981d00742326820400c901080510f208101940300c099550800c2c0f2040c43d064580105120701541c10418000700407a07000c07500b1703178208980205800c004800c5c0b0351500750b91030100b1500c3d401d0304503400801a6210b0070f41c0200c2d0403280255228010300787c4c03d1440c1c1c1c0c000c9900003501c01c0540d110038020000540b03291b210010050041c000d0b140700c0d000b0b540e141703800d40b503212801c071640c1c801e0100719107048000d01a11100030041d2500441c81c0050410110f622a100d911031642800700900c000c0409071400d100e00895200385140c00c0190300400344880c005a0041e0070160380c4104849004611402d05116880030290816004d00003a5910510049070b42d10081c8000c0e0058a60f4102002d05442017009902 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 273395044 1250 273393794 273393811
    0x20306012703021201021c1107050a0503030a0e0703240605060a0e010e191e03140105090d03050705071112010c020f10111902031e0a02070602010c09140a0509 70
    0x301d855401040321074120514000140e900c108450f02000036481140c044102c00ba440105070440d02d40d0496491b03009140c0c01a02d180111080541048408801103100e15480311042000e4018800303034135514002404020103e0107018051034501c01d0105850700121500140480c1c03040d226404254581c109242d06000f00c1d400088512156820441e07602d044441518820329150880e0f041c28081d444500c85c411400c640e503075902c400e1406103511403000e142c204200c0311078207800c418500d00801003100c00e05958040c4501d24103015209004d00e44c00344429030385039400c0015a03124008000d01d0418000ea0080c07c0e800310303426018080c040c540041e94290041e0091460402415017420300d54503500c491a841e210107405250708403416076103140e00183c4420250110700c0c4041e440c1d482a1800240714010040e252510001c1c108001d02065600303600780c0d0320066030784100740c1c00c0e56009003120001c80c50301002070010140c1c07900c0000d0010b4008104a904031340c0c480200b040f100040d900b001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 273396294 1250 273395044 273395117
    0xa1407150e0405010501031817132301030c05040e101502010902041109100f02030702031501050111010c1d0a050901030804030b01121208130b010f08071a070602030601 74
    0x101620b018403905004001c2030034180641e4070500c11741240d440c118400284181602481125150400c40a4452860000c8065078109407074003001c4050303999401d41c0d0410102c90910405940d4824040c1882c3c015250701c40a0800d0300b0b20203003c580020041200041000e111000a01030380d0380540083c914145800005001d000c3e401848182c0f03001004010a600042005007001d440d148900301c08a039040ca803c1c680d03060000c1040f81148607901c4081d506200b10362402d2151103000b400703181200c0090325115052a45250120700b0b07646000c02901c0482d00c44081c0707248600301034051030080b48000700561a01c82e2200b0004605080c01c2c0c000742c03503606011509104114100a180740134040c112190040c060030342da1075100328912800c1301c004002003031000c0b410410800300a5015181e100f992000c4960712240207003c2c0980610850070180f2680c1e000142c5440100ca14100002005812a02e41840d82c0c651101235800984098100074003c1817840d0030091100741c002d00b0841180020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 273397544 1250 273396294 273396317
    0x13050a030e041a0f2e030515190302100c05060109050a0e071815170c0301050601111e15010b0a09060327060b040f02120702030a020a140715 62
    0x102c1200c14405425254a104590707451955031098100110500102c407611144002641255218103e113401c2d800c401c42c101084451154040c0c00248c85110080c1414940314540010402107810700f5080405541d80c03c0d0040c80941071040c0800e41200080c200f011811106542d03240c0ba16609030b00c00300c00540d450007130004460b0a40201600001d0340401841c0300c906041203249000407035504a81401d0341d4028400c01c031003042c2803001c0100603200412901d00e11900f200f070b449049410041d4030075440c0030005075407076008e4540d9807141300340b400081c0310345410340b070002d0401a908000c0c22440e203c0c0100c807960400780d009056018000d901d68841c0c032400e42500c0a04128200e0700540c4c141070516003a001a520421315245010b4081004081015800e086c590020071080304007541060500d4003980316489650001c1080c03587c40c403540d890503646c0000032030f22401858520300040c2c1214029a0125440450155202080200341d074181a0365140046900d082c000b040310101b0b42c205d201 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 273398794 1250 273397544 273397549
    0x213060c0b010e0f0106121b020a02040b040203010803040b090d020d05030c0d0e06030c070c030804171c080c0a020f030703031b030b0a18090602160c1502030a030513050a030e 77
    0x441c1d004003072400303041c01c9074200307800080d01e0080c05000b104100403210005104a0401c2d0b00413820350b54481c2d004808100c80f1390002074a1304880102a409039040540345c0400307007418802c8038102c8220300c0c09542001d05101064a0590001e5801076000c411041300d0400360765200c040f80e0610344504015640c59224000c054100402030801c107080c050103008015450b21070704104c80d446080748107250f913240010b1500004d40711043c1c00141c00580085404a0152500142001031841c41c0301118140e0307441d201805400104100c00764006101013001c100300311184000b41810f07800d0ba0041da8a11035410740320302e14581290b602a000640c90f89000c20700300d00e205516103032800d41840c0c00d0045560307c101054034051948038452800710000e038010b420b0354580d4030460145034012000d40d9500403811284d99004450b2100b82c80151801800145010007905001c15003840d580285040400c203a0043d401020005c100c20340070030138103054800040003071240c1c2c09524401c0e140d03e11540700d0a0b09 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 273400044 1250 273398794 273398813
    0x806040c0339050405030a02101e0504050111030f0d0b06070b0c0a0e030606102703120305090303131502071203150605070c0e0a0e030c0a021e0d12030213060c 70
    0x48a50038840c01304800d10654031b022410f020b00c00e80503504c03100b1a03003101c54121480901c886104c424030f13821305080301c10f585c0c0c80b00040c4100c440981c0c51050f8441e140c5d5020792244500840ca50b50503800308910390081c03429030001c105405c4010195403d000b501d440d06004504201d03404400f0b117900082e44a44290028850090030b03909030000d0103545000000300d48440741c4400c41d4800c1c0840d11704141c1c00340c61020205407580402c00d400395603c607a2440d0000442e92042c04680109041400144002c031001058034420101e8801030341c0d661940740c903410140c0d1042c0c140d01808a03020042500403900495000013a404590707000030305600c0f58135180e00b01d00c05a800402c10000104034107004601000120025034040006101d0340341c0f074181310100145501581f03c20b40d070002255001030342d500803070550070306402076038100c90100c000389003907001c1410b0300452a4030840f84100c46021900b000206032003580d45040041c90480d0100505000b10318a9001c000014508080c50080140050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 273401294 1250 273400044 273400151
    0x60f030f0c030c0922060b04050306010b0a0f051303060216050c1e0915031203040c0b0304021305091005010f180516230f0909090705010806040c03 65
    0xe4542142841e030218201489000304c1c19200d0103403000040c070030100c440e91290440120401c2004210759410001e6040d802910801c0c3c800e001e24000000d10780142011900580d02c66500d4200b071581000e020744d03058028a100314205040d211011000a80500c001c08541c0781d1038801c081e814080c1d00e02141352002e0344000c2400707648010740404492507801e01791550201d0031212082c103917503451f0340d01c104044030303001440d0f042c4545006038200e4003018008500942c00380d07685013421a11451600700d81d03c0700740ca000390030070710501175020b4400d243d40c0230070340221020042c0c40a03002a655180c069076001c1c0c00c414800e50719200200142200000c25001070981504103100e030785005038410940c0300b03643c0c0304070f0b051204414101c100c480f2000f10b60703580c003910003001c02d45829084d0588903d640120480600501030140821845100010100122501690b8030711607507650006000c0034100c00000e000c18551104221031441510360386940d60700b1010900c1c07004032200c1c0d15980a0810710702 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 273402544 1250 273401294 273401311
    0xa051e090f0f010e01050c21091f0507060906021909090c080c0301050f0a09090302030a0305181b0402070c09090201081f090c0c060e0105010602070510050301170c060f030f 76
    0x2112626590f0340c201d61300307840c404000d080190b1074145140c07101d4202144800c00c461540988020082c00c40700a00c050070041500342c501d1800348040c1c4099404107101003012502248041c40242c0002c0d035950843c490040c41a000903041114502d40f1040d01d10301c010255010a40c0d0303440a220a40c0c1e50300c280c0b1174400c0b42c1c1c83c1c282c16070f060411403080e81e4441806250301442c52052501d00b07644502074280000c0c024403404000c00f10150900079102e40082035068002403c4c5030100317110140c03c5207040031205015001d80a660310040c8804045401c00342d2075a000782d02404240081600702c40c068004013041c8101060307a03411071000410b500002000350000c56000c1c01c000b14100c3d5814410410369800440020781d0850160050310042d0000c24001c0ca00c500b0280d0100c0024419086241240c41e08e8080340c80e15a100e008120314622007880707480000f039017403004100c400c02819505404c2405c8405031680750302e41c00302081c03140d4000310145201002c000113001c6c01d111003000c10759114022 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 273403794 1250 273402544 273402559
    0xe06030c25260714031c0203090118020315060f12070305010f0e030a120612060b0a0e090d080612030309071403010b06040603020a18060c060e0a03140a051e090f 71
    0xb00b62800d2250003010005840704c1c101145502c800786007041200c012820848042d040c010600700500302075801150b81102c1d9500307141c02c0c1d03c07014403039400d00700030b1907070040260914056035481e0702d076481c0c0d00400b00e9900509070b002c4801d50b030300d911300d46410702101038010304007031030542c1410303030a440152105680e03003840e19a0749044a680482034502d02070342842c0c40c00d2248104610f100252106800074481c20300e030480c86104000aa90207803c1111050342d200e40d415503100ca00e01c800348011941070441da04021f0a80301800e1190080c168420b10003080301030100303004c840851a42d00304075070103400e541c4203000500c91003c1c2a0501190344408500078854090b031880031803d21300451003180c00740b580100e0041c5415015400a01103203c0d2070107420100c0f079075594010003030342041405903092481e0403030078134154801107080407990350580c03210200000001d0350381d1215803105241c0c10400c82c040c0050f5007034103030440084041d1207066995a480e00d0716141005144900328020900c281c05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 273405044 1250 273403794 273403853
    0x117010308070f0302030906030a06080606040b060301090e01090f0515090a08040303110f0a1110051305150c010207110a05010f09050108070e0d081b06070e06030c25 73
    0x10070034220341c5100d03031250320000c40560070710f000e9103580940754003a60300c110007008021a041035580454220f03540720049031419190042400300b10780f0065132098001004000500089c1d0454208000701000c0c54000a0652000e0b1034088a00c0116081212030b50480740c2d40403500040740b4606a0464100006404d00305203659800c003061256100040a11511840c04a4200c07030602c09070441c4105202540e004800c1494220100c081240c0190f200b11015180e0300c0c141c52007401501c0f441007121941034115801e14003017201c0c5080c102040361002e01c0811094800c0507080c005052032500c1110035040c508245810007040d82c42c15007050381080182048469116030103001e400483d01c0030300f00400140c840e00381c1140e442c101d103180300780c00c0381d00e4030400f02c03c004090380208021003060003004c2d5480a8080f8054546201f0b8824400040b46594949101e161010095400c8014040c0603072800b2a10b5243d00f0801c030710b22440d0085014012101c070188041c01d8030240d101306250300300c02623000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 273406294 1250 273405044 273405053
    0x509150405061c150513050a02060309010914010b01020c0d0b0403030b010908071710060614030c0d0f05070806060a090b0d02120f010603061220210c01170103 70
    0x650200428800c548440100d0320342d858071421024600720100b01c00103458400e051000c0789542ca000c004a20a00c1e14000941d005c056810859690354003030301620f00443c8075001c11207a50000382080c81306550301c1406c90000f420440340404c4032103e0b14008074260400e10b0000e402c2c07000420a650258168070403010005100c4203406503c10340c136040c00590f8103032540c0120751030036042d0001d0102d0300c9484004200c0b4600400e0014185808104a404000c240d007030003026244544034480c003007105006070082c003411000c003444d03200c03e20001050901f1000154030041d194001581a20b8a507210241f1100715403003492075a00000681e000c1d407400d220100010080151485003141888002c2174801000510341c049074200b1114194803405422b16030301c0041141401c1c4580000310340740c5103002501c007034541200100e098100301d0141d103c2c804030b03002909944205034a2036002034030055142040c1c5810031000948242400101801407180b40094040e0b10240310900d6412034403c0100b0005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 273407544 1250 273406294 273406321
    0x2100c0c0204090c44030301180b030102040b03010e0f04121409030102130509091501060c03020a0b040302010609060b030108060115020a050a03120f0c0c060b010c02030102160b010509 81
    0x607906079000a00c08419040414400e100342d0800d03d02c0d001c180481100140c2805a030911321622010329007a44014074241d0800485803999145040e0014001042802a00e210050310714444003404103005004100080c00ca900a402c40e4012000100043c0030312103a05a00c180c2c03145c0b000c60120350b1802c0a4544100260a1040140401510302c00c2200144035182c2500d241c00d00280c000d5440d0108007232000100c030380380d00985004000000000b034028100040c1100c1d803405000c088030407a4203280c800c5a00d6201c3e92003d90030b42c030601661344005000241c605100b54020703400010800d0030004294140e172181c1e4414a1068030070302c01070001d140e01082d41c5045a15008160441c11606441a403c0420000010b0300600440310660181074000d8031810b4012045001000019420542c42007161030f004200c80009181207010300c00650305502c0710b201c54005040184042c3c2d01940042d003683c0c009070783e003980d02543d0000c000c204040303541207a015083c1218481c860f0726089070f913080702 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 273408794 1250 273407544 273407567
    0x60203070f020d121e050405010207140615041d0303100e010504020a021f2a0206070305040308060f01140a0c151404062c06060a050f030d031d0d0c0302100c 69
    0xa2981c8407030038240e00c2541c40d4101744141e807207138003803260345400c0c2800741c000e4110002c00c0d0740403203903040c65050407500170600c42d105005000104003218a004c06100050109138034042c001003904c0111072181800304080d40c0310741070b1064184141424503210346a5601d060b03001d240141c4c010311000e210140c000c81c2d19802c0401204440001c42041410340c400b8183c2e0720040d119042800d0b020162000101c00c0406040342c0c281c00320783e095115400d084003150400c50713001d0005000b010102c0d0040c60500e03162040c02e0701c145440140328070030100c00761090b4800201180400c030314807900b50420121003a4450220524082041000c0c04825035219846008100804850f554800e240d00b14480d140c44483c901c0d940e5250080041f00d00d400c0a94030300040d1505441181160700c0000c891510f950303807949a400180107808111000f07032054010704003030040b10102e460401103101d02c100042004c20242103d580e5843c070031403020b05029003081c005604030689036040a407a103c9140c3c00c032480080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 273410044 1250 273408794 273408827
    0xf09071401050403111c03090602070e06150c1204091a0d050706050c0a0606140915130207021f020604030809060c03010302011409031605040c03061d040c0f03060203070f020d 77
    0x18910b0300c000007040620191110b469412003a000e200515900c523074080d00b0744001750222000c03144c4841445075540407c807585503002e0006510703500d00070031240c0074144180d41c44080307412055000d241004107821541010642960f542c001803445c0c5000540c01c0c00720b600642c1d44181400d01a120b0340d03241e000500451041c040001114100260108080006142c2100c5c08100b06500e500300030407064403d0b100d181c414618000400c4400304105001710728a00010001c554141c082e0704900c020303400201c070071b03603000c100c2d941c0b01100200c0d0340303000c00d028050303550241038070b45403518015020b0040030386400d4007684160200030200210704203c0b4192502400c003076003910192a00c90080c0e10502480a8040c021a5040c010401d4003004180c1982d6084406100c3e4071004e80c411011101580308540381a140e0806001a00854642442d00640500340b103072441a2100d8a0b100344950700d43c02124190390010801904907400b180c072070380c17400c51307440070740f549840303400f001004c291031101a00c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 273411294 1250 273410044 273410063
    0x6040c031b081f0f17010b0d0209070509120a0b07020a050a1502040315050103050d020f060406090203070e0403120b0411030f10270609180602070201090e0f09071401050403 76
    0x710050780c5a40300c4181c40d0061030040441985481584135408568400c01c2c3c00e0100040311486412030600030144031440107011102641065020010b021201034052001d1110030054150305407a50110403044c0c20101d0010b2071040401c2c81e040100c454024072110454010300c20510010b007010460001d0103401030b071817006e4515a03190500082c031455000401d801000c0032240250805ca40115040300e0265080da09074169852050341c41c2c801d080702e203102c140c2003100082c0018802d80c0c0000d100314005004c4581c0b1035100c0000300041d60707040c1d03001c2e000f040c84031040003141a110301442740400c105843c107100c4005440c5522090f4000501000d0800e010103000440d10034202030100001e11682c8822001444515048004110144400c001d054208140807070710080c0d41c000c0000030b9422085c48065683c4075200d0350003d4011003412810031207019800100180c000c0e0a00340100c070042150001d5003002c82c0c080d8900701e02503000c4040724250001000843e0f0700481a10100da4000c1800b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 273412544 1250 273411294 273411301
    0x3020903100504080d05150402120612030f0927040c0350060114150901050304030c0f1b0512060123010201060b0409020c0609060c070204020a0e040905030306040c031b08 75
    0x4c010342080d03a18040d005440400e4ac00b40b0006000b10640c020038094440609010b20b90300b1a40d20b80c800c0c90301c0100c0c588401c0000041a081040d150a00006417855140004007110204040310001303640c00e03a00480340c0a02841401844410800080e2011880b40d4408a851884083c84108038042212600084c01100003089410210921240d41725040d1080d40da1070343e04d035400c040200241d031030140a40e40c1e0810001103040d0100c64480005031151800c40e80c5941c1c4c00c0302d5401800c0411100c6c0101248140e0000d80805c1c903040304041c04110001c50f0504100500501c2440d00f40750b0109584400d00400850401b04140c0c0350821950b00d403035014541850041c0c0c054100d9a2141001c102c00180000f070448965019100a20551041c3e890341d031205540c07076984540940b990310b4680303000c00c602001450a40c2c02020710700c007113003080b41d028512400014222030203000c2c21355840c0c00c000200710700c42c0fa161142419445c00c1e0709040041c40920300298101101c490350400c140424103010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 273413794 1250 273412544 273412561
    0x6080f07170109051e040c03140304030501050c040302010318020d020f0a0e01030f060e0d0906030903030e10060f1d010506030703061a04150c0b1b1903020903100504080d05 76
    0x10516085441d84a041d4a503920311080008190444030690001525007101c60110017500d400750045412008840e806420b607114407400036240440c2d20f240e03100800000000030001c2c0076040c800c00480035104c0e2607074611300001d81555000f00c0380003480304c0700b030641c1401681c8a42e144d04003107405484e1040300d4503020f0049229955550001c2c55100000c0d070001042000d00715496a00500c2080c06100064003104c030995140941c000d008049103034420180b010710702c030b9070190540c07901a160101d580420320395801d060004c03c0d0b120301310740c64981b24180f2800e4075090720000140554203109445168111129000f80c0040c09650302c51f04001000ca03046520030340080d000b0b82248040d41d28240310a5480700700302c1d44503200300d50b80100c0d121550f0480c603000d4040394107440c2e0000300e8070205640b801c020340050f100c2c044640d45008018000485100c4940c100e19411f228581c80040e611040401094600025800300c050803505100400c0300040d500400d441100907030090114054079011031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 273415044 1250 273413794 273413807
    0x3120a06120c031a100605180a1d0708070210020d060305030328021920060a06060206010905040302030714070b121608091b0604380406080f07 63
    0x8640c40300e9070400c002034148100c03140c042007240d10804100003000403049400c60050022500c0b44028410b107002000a9801407008000306a01c014000c41c1c00c3e000800016a000341d1600007080d9411079941c80142d10402d0048150448a01c0c1071000c0301d07241032031000b969a142c1340501d861103900428110303140800c9d42c00100180d03500405607a2280b400d0850601c5210060303c08080180d03101c17024020740b10903842241c10000300346481c0d12428015803829100110215850081105441c1c04500400410701c40c0c14004c00a40d5004100180f078641d00038a002d00680140c20139a20302030500000a40000884001c1c40d0b00460720780e031440c803510743a26052507041d60080f886928001003403481c1c860351070810740c13090000061a0182703501d240811600e814040707a0916582d400307441e46070100101410605522030005240a01d03050300c0328200300041c208850440c0b10507010000b03400009400c0b0300d0721a003d03281030001e10704091416a00800c682805801d0350000b900341000300396001e10541c1c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 273416294 1250 273415044 273415049
    0x9071403101d1006030b01050d05030706050916050301060b030406150b04080a200a0504020c070302040f0b100c080f030709030f0b06011404080303040b060d05060106031a1203120a06 80
    0x10800c001c030301081c0350b294410050520420310035028505480b900c1211a01c42c00041d2500181c9000c901e81c00d007410f100600ba82e190f4240d074103110901121000070520300a040c45062048040d020803105902c903100320001c290030240c481e034180003040c041c8261b490140c9612a4106101007000014004007440081041c0c2214000c0000018080b49480340000c1603800c1c644143d2036102c01d001000d944070f101950055605a00444a8034108024034054002c0c113801000f0b5400d84901640d01da00080454040c03900c6070f00040c1d00c135a01e141c0d4500d010041c4611048a90421016a070a030350395003000b5110710440625070740b0000c00403a4050b07204191074009954002c00c03000c00c5100c10700707200168175000c840d42800201c41001d100c1040d00a2400d560440d07080c10011411515a9514030350010f100500d01c2d81c1100c49110b5000210fa0704012040c000c180760b49000400c42c0c0750002034105c01e603000450342d00850f40c07220744c103503a110004102d61100086490001c181e4642c0444035001d0103017079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 273417544 1250 273416294 273416323
    0xa06051c02061602280602150112150204120c050906010201020f0324090103030507060f020405060d1a06030c030a0605010521090a0c06030218030a170a0c150203010e06040509071403 80
    0x2d002140f00c06814800981034817155001c541c5422880142c00b4920202408ac030f01d21000488806800500984001950403400041c090300b0b05490701c004082d04030a885040d034000c01c0402040225044c03c1d13a135541c100b9402c1c402035150000142d0340d030640d440090b00c015061441c100700305031401e4901540d5000c04c80021f025280e2543d403030030002c095030060031003510450314154000816107620301c04c4604449010300301c5418449a8101940101141040c0401c3c1018100b05038545641d220000c610582e60454000d032641040010401200c507240c02c41410b01c007082120511680302075005076244840902c030300c09035136101c0c011641000d140400040004100c40b0020590f250541c001e000848140032140c0e491149050405070340d0301e031090018041081d0f016104526a900400401c201c03007290800e5056402c4d5540c555401907041c1c10441d040f140c0c088010320601124403900d039001001150107001504001c0036490301e03401c1600c01e209104145030300502c40764900b888058001e5090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 273418794 1250 273417544 273417589
    0x1e09030206130b0721020d1b241d011413050a020301290612270a05030301060305060105181003110c0f070f030321090501050a06051c02061602 63
    0x1786031041e00f010001c002c801a030350fa03245103480c07101e100154400305004161784207661440e22191803600107800e180161031230680310040c1001c160303c030b0f04258020b1101e403000140502c0b03000c1c02900104407402c48000c0c2d1740d040c1003000c00f014912050980e0001c5400400c113400440078a050303450074060340b81c029055400c0a441200d01141801003144a000c0200c910414821200801005118108000c0d80351882d4a01090b0044071400b00341e50511a010b10040201000c06101c518000404104031420340c00080103100650f8103000301604583c0038201581481d8113a8006034130341800600f114050300c8501e000c4440c080c402e4000c1e4400486002403142e0383c0d01103002280d1181d010400e041d185114509000039403a0003085994100d0350140d580d101c80b002a58902c11400c200c0b5103142c817a09840c0c0d0158800b0034020b1280a009807a000000100c19203440280107006258400c411201250740d4002c50141c0c98440c01c0b2581c2c00c81000c3c91101310001e41c0f00113151044100004c1c2c1e0002ca2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 273420044 1250 273418794 273418807
    0x240a0b0d060f0b09010b0c06041b0f080a03020c090c070213060f0f0807060f080a0506010909020a0f090f0807050906190305210304030c0206090102011e0b011e09030206130b 76
    0x5a600101c4a10740a0700d0748400c0d40c6c1c8410795004240300e51000000d641e40700400240126001241149006c00303054402c001c00c1da07507540b14444042141e04807100303a400c403c0c1c80c4800c0503010884514007c0d070954140740c02e482c2a4440d003143d80035501c400b80c090b449130b21742c0030042c001c9079200780017034195450345102594994800761000e01940c0100001c44c4620030000c12050700070406481c09200503030310b48030545c0d10000040080d11001d03000c2410311003000008110201c641c005042c01e64042c0e0b0ba1b01200f0006454004e040b08040c3c1d00c00000900801024030020b42c000c42d80001303843c01542d1583d156184d04002c03c01c51080d07141c000e250f01001100200070000089900340440036100b401c080381001da1012442d07240300c282c1d0000c010034400b5018800608219024040c0c18005000000e52080d034401005000304040170600300645d914196903902c0e6801541c0c503129244034040000408201c120302401060310360001910135080802c005220703244000862000d003100105070350311307803a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 273421294 1250 273420044 273420071
    0x1d0102040302010e060f040b130801050a0b030618030324031903020706031b080a231009060b0f0702061b01090b0f06031b040906110a02240a0b0d06 65
    0x40007800101d0000740310b00c00c0b000292074510290b503428040d80d180540307014688444204140d0101c40c0034a40c0c1c0d24190800070303003030400380316061141c243c51030701040c020700d0141050304100c0001c041126255150100500c85103000041d6a400340b001e000010405050f0103640e114501e43c4c031100c50b454401c1e00321403490481c6904d1341c2c1d030398a4801d408483c170321030700e0b0300b01907064851050a0084a008100c0c0000111348503400b4250002e660240009080007a0301d403c011404403907001c8100084000241305278044001c2d181c2c0020301d90310004007c05d506159000e050f0b0711804100c40a000c2c4042000402d541c1c40d5030468807a003103280c11103490003034118443d90280543c03e10964113050701d1000207005d45c820b00d18440c0310b400d00501400c1c00c0c3c010050071034400b000b034542c840d802555039411440020702e544142c02036107038006120394454a501c0002450102905001000409405680860600c43d00f1180750400300146000c11090ad5100c085030103100ca204028115170308100d18500401c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 273422544 1250 273421294 273421297
    0x305060a0c0311190e0d1e050d05091c020a0b030106020d02010614010203031f0504020403050c0f030c1806030a0c090f06050108090a08071a0c030a05010905040209040f061d0102 78
    0x124a1034805208001544074030450501482c0b01405050081414109100d031051107032481070030000303000241c034001d1500c42d0321840003585007e5104000a601c4101400020011510058400d190a40c9800c02c168003080d0000c1c000c10355058041e21410343c540455071034840040150011010044c0c59680d10a4029035590b2617204d0080554608003010035004842c0001c108036a5060b001103103540c0f90304009034048070850417040c041d103405080110f07280d621400204002c6000344e00400084040104021030380c2009000103110780c1c800d122440b4581c640400381c203840085005140080c1d5904404203040004240c00180940503144000c41c54011540c4000d0030601c1e030322010401145c0b03620054901200a84900ca510303480340340807500048141c401090752600c0303800507140c80e02c15050911504001500c00c0f641b840c202104104080e10180f0030b803401800025401c3c031960a00d9000f041002401800161114442c0501ca40601c45c441e0000f2850219804c001303c8050056010302d03000303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 273423794 1250 273422544 273422561
    0xa0203040e010f03020a1e05030f010213091a1005070b0106090e07141c0207060203130b0c04030206070803180d08061819090317040308160c030206040204020a0201060305060a 77
    0x1070720300c800c004207481c04480da031070701525405071440b00c0190415642040100000c0c5a8102580c003503600411251014810100da00c0040800981c5505411018080002040e0004000146083c400300c280032a051060100d02e541a40c181a481074401000c484d01d21503104003606900010b40000795641c0c1c0000c044085800002402c07140340c482c400d0889060204a52a2100580902c80c0080e2050201024030305103625410062a24189560b5041a42c204441a03152071001c0110f610500903014081030f0322042ea440c07004d240504603400035890380100c541c040c0c1120008030004201d84001001d00010245000850303040400c3c407a002094100c04030365440c09481d41e00c9944901d8041c00d00c0c680d000d120040d44070203603200e20400345801030840c48801c1d010469440401100141c4030850b1901544c065503649426142c480d114038009070142c0710f550200180d0a0040d0003182d0302040743ca030030950444001d0390702c08610314121301410f0a90006051401200e050044404480d44149103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 273425044 1250 273423794 273423809
    0xc06050f010e071701030303050c07060e100c09030c0b030414010e011d01060f031104021902070819050303040b090f19050f01060302030a0f03180602030a0305010e07090b0705010b060a020304 84
    0x142d40e5440303008075100c06440710107108141c055401400024065004643d00802400035142425041d882c3e00d010388a80b0305546903190409210070100c81110f004005124036981805503241c3d181d03a90304401c80d00b0070321400c0c0940c0320100104081101440c03201c8105010100203114140040e02554002e008208450400d40b0660340071118210042c0584030884003038000c00e9804518549400030694100d40415070300650810501070711440400c00709486145582c000c040c11801c218401c1d15050100f0100d5244003200346460000503000812a540507921050403205515140b04452a200c1305d50b11520b40d5010f0a4010360300183c40c00d2041034110b010300200c0c5c22906003000d11600301c074900c7c000690035070080d20758000031507160401815618402c0c40c0a0076000413030701035030101d26440e40280c00140c1000030914503007907060080c04c0c05800e40b4900f016160034600406009820148501049890081841000e0100c20b42c0a015505c5020300119a91001480020340320340c0300303002c0c0e031301e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 273426294 1250 273425044 273425069
    0xa0210020c1f18030309051606260103080429040b222d030204090b0103030f02010b03100c0215040321050606090111190c15020c0607060c0c06050f01 66
    0x30b182062a004103219030304003114010758209141c50480240c102442d0549080c0314406800060200207450b031002844903540e1500c2001e1005d11021111036039219803116503072034000600c00310340f044088808481c420b80d0185441c0d074803500584400c0080d9440340068880104000445c55400c1c1e000f00740d0407030811407039180c001480c0c6801070342c6070b114010160071000c140075074807001904d406491071104003075410100c0e40b80d41380d000070203980020504851010304100100201a001000345000e482680020b100f08080d10b00420f81c4d6001c543d0808000b240c85511a1540e14002d101507440c80b12884000d800b1450503007800340c0390641c0d5107902016039a580524681081032445018041c0f40020a41c0d460281c0c030348011900750b100c03031115280e24040d161600000e004d031543c82c0d00c0300a10034a00d641d04149080481c1006482c460b43c1e0606641143c03106920655510003103680081c2e01000c0000c40c0341511000703d03014508450004e01007442c220a1002d00f0b0202c0d900f40c1c0c101c0b03520f4550071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 273427544 1250 273426294 273426343
    0x6040c12050f070e062704030c0213090c090b370b12010f1a0d020f091c0b06040605011407051905030c011b0507060e011107031e0809030307050a0210020c 68
    0x1500c6d4074003c22001400703004030041000a80f142180c0341003a80000c5c5180c095038500c00c40401218070444c1c00310b0b81c10400708000c20241e19980038005221b1300071603500c150030240c591446922003003403078041c501520102444010201210086018006044001d038541015440310355900b1402c3c000c1c088154494140040d000c600301d234040f201e8040e901042401c0c00d8043c07503004044c5d042200040004c1c03405000c107096584034003280c01002030b8446c0030042c1c0c400060800846007000602494001c40c10a5424042a60007e4900c0c9100c18400041c3d1358903100e504005041010303d80101c040429074030449018000000041d2040410f1a0020040710030f032a201551004480c03e40000030500c240400c1d004120b1603884510900c0b43c81c0004502004d80c0c4001000d030b5409a40c0803400b250041c000e80400360220500700f00545514100307038556062400106a881c0001080300080100025202c0c408034400d114a0406181c2c1000954a84c140180c0440c1c442002e0301c58928001c031640c04a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 273428794 1250 273427544 273427579
    0x1090c090c0f1d090a020a03050109180b06060d090305071208151207080601090f0506030303070503040b0a0b18040b060405040c0b07030507020d080702010f0206040c12050f070e06 79
    0x408240440350b466085000042c80010748140d5202c0b9180320141040d00506442912034000c5684542c803c43c80061b541c0041600207400ca44040c0c0003031031054505101c0700788500b4a0706a210000e500446040c805607140000141c0c0c80c841e00c0d04d00d0782d500e81481034102c101600103024241151042002d140c500c0398a00007154144012140244070180c40403482d140340c00c1611162541840d44002d039036020703480321811480e001d801e070701010503a6070f6803000c0000c00929104881d005070040b806145107050405004007540030280c405440d170004100480d503540c00d01d40c0b258140c803801600481c02080349200d0800a0102182c0649480e42c640000800501d001c0c41000d20541e030141143c0c00107410040d20840316003101c40c0440a103d81008003401580d50a40c82141544c0310740d000a0303581c03440c0d1000400d580390302c04203101958001810701001428481d20a400d070352680c20f0400f000c503003605000e403804c00000c00c0c00945004151020403c1c3c02a0483c0b0f500c075110940704060501d113000c06 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 273430044 1250 273428794 273428801
    0x30705060906061f050d0e1b0405150114120403032a0f05031f080d0e0306010308090d060b0d050f0d0e1f0c0c0806010806010f030210110f0102040801090c09 69
    0xb8081e6008003080403000c9002c0c0e42070742c003482a0710903113005e0b8100300178110118100c50441c2e1101c0300c02e503c40342908812084030b10520081100644040c069410000011850031a20f154110b0622030814406104201128143c3da0000c101c034004020600302800c01070000d1113100f0600c28040d90300c3c10b580c4241100c0b208140d5880000781da801b0441d02102e0b03412215138002500c070880700e1010207805520720640d01081805840d002c4094410794001e00d00c00780201d095052242e0007501321400410116030f41b1001d88003208002e407925803071810a4606000180341450946501044d545c3c0035105002c40082c0128060015030111407007021003c0050320a039032044552544003d9801460000c074585c41040c89103500d003401c000c6281a0749960320003800d04182c001600541c0b044004005001c02000300307900401c440c1d490340004500316008280c06411940d4100d05020b000c80502031404001c110122714810840c00840d1034540b0741560601901e090041541ca2407041c42c004202e4048520 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 273431294 1250 273430044 273430051
    0x6011b0318090c0e0909010f090305030105030610270f020304061a041a060d060503071707061b03080717010f0302040e030a08010501081003060908030105010f0c03090b1317030705060906 82
    0x84130200e40b011008100a40380000174102402c035520b496014130000310b140100d805035032003070b01d4203926581030030149490030b48000c02e8120b044079050310402280001d02e01c1118a1200c40e010043d10640000085002e07283c58490070349490310000c10081403204941c4004000048803a0b0720003032250312810030003550300313664030307100c860340003a00c01036031441e040005003080303080d070480801d20903039800029080c20300350f6000c02c68800b04240c2d507890080c024454000948543c2c2040045034042c03142900c404071700005e00800341301d02e030000318085500901c4082e0260344c42c00ea0310203103580c643c4094030504c0c2607444224003450a1201171500300030048145c4010780b02c03da5501040b40e10300001100e83c284054141c18068821180110102d42036000d901c2c503d900454045030382c1d52500000404145603203042104219120783c14400082d8091905400c90324440007042d00d880140101d43e01640c3c00b0790004201070352035090030b4034000c030100c00341040601076821b4130915a01e40ca802900c808044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 273432544 1250 273431294 273431297
    0x110706050d0b0d082a0304031a0a06060e040e010b03060a15091107060506061204031e020a0f120e03070801060501080c0412060903140a0e0a1205060a020306011b0318090c 75
    0x900582e40aa030305d0542c0c004001900718032000300320900d060810300315441900203a444482e0b0480e45509803101203601a007061600c0e00400c251031030724200a0181917408201841561180c2506a5002094000da0075040009081e20094200004100000c0c000310400c241405082000000d40d0405445000504044190400c0c50024181c0e10003004080c014491a4402d0040c81102d1291120b0680340303214070f102e9212010300c461f007070340345c24518000f5007100c00c01c41d4040b03030b100c00009000003408683c180c1c2c0f001c00d88040302a80a000d503020b21401303c0540d010301c20307464001401d42c4150403203001c580c82078031401c0d0651030f0303482d40b034102c3d1090380512a410860700003041c0c00a00b01b0381c8140c41c0c080c068039003900c00c1600e661008005900c009540701c00101100b140e034480d4540404684024034041901507004042c03030b07aa2507103420000f01040d5956a02100244490340a1100c81d00c40c0e000c03c0c1c0d0b40c02007040b01450081c1c12801e00f160581200c03107010301c020680c02e5580c42a0040d20155 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 273433794 1250 273432544 273432547
    0x20d0e0a032d0305031f0308070b100b0c0307110402071e0312060b09030d110a0f020a0305010903020d02010c021b060a0e04060b0c010f06050a05010807110706050d0b0d08 75
    0x468031540040b09848040e0060720000d40303030007900d01215950342120680329075030700d5036641008500380c2100c0d140c011408030801d04030b80003080010540003c84801a0f84164148595580c0511070358884542c2c0c2c2c000010f22100003246041d2040c0030000f040003520403c0d5003172201a40701e061100300d000c1c6140c0104240340f007101c0722560314009403002c00010300c01c1c54001c0d003040000d00d8240684550790705c21610820007107007001140c41c050292a10101271468030310100800641c005a4270070944901510342e01c03580040c10306540754804044007464201b07000b03116203411403400a5484944820369030041d440c0c1801c610386144041543c060218003984201600f00960082203181d40c000d1a14000b8000144046503244e242c50007104000c3c10305000340313500c82480401d4079094901c00449401400c1c5000410301c0941d59108004054800c203181c10001a030714104103803001440d9004114091203000030005825501400a1101d01401354082c007082c407510701488100f008070711008004110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 273435044 1250 273433794 273433799
    0x30a151509180e0d0c030210110d09020f04050403021515090403111c080601030f0203010509040b06010210090b01050a0e0702151e190506060c030403080f041e06020d0e0a 75
    0x6010782d003001032120300703280003c07000728000ea4140f50440b080d11810110f200c04001c0342c181b54050140000c004501c0000340f0a00096425001003440751560800c111980c4d02c1444081d034070303001040520440d001e0000c1050342440c1c03c0195644091030480c4580004a400081038603903020030758211954042c205180c6900c2c1d81d60306494841800308241410300c140401c0160000440078545202c00ea5038a40401c20306080c00018244c814004045c603c20f40100010411a160420a40e80c01500080341c4541d6031100340040781400400d246141206003441000b105100440140504890040702c60303000d400c0d41e41002094820b811108000582c1244070013040083c09004007a500030504541c00418019501c4000f0480b00103854034401d040040c625078040b060141b044541180c4200d5199042c15112220302d6564072940c0002080307140040341c0103044031110010740d00030f8001c864a140d441c8418a45500c04901644183c400500c074089440744031900481c103008060601600080c0b4903030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 273436294 1250 273435044 273435059
    0x512060603180607120b0303040513090f0f1b091802010c11060a1e030209030622021c060c030b0d1b090507021b010201020313032003030a151509 64
    0x308014101d0703104601106640d012500144201e9200f10081d071101802010645d4141c0c0454200d2072940b406540204000d219998500305914501102c1140204011049103041e040311142107900500d04481d00c48140c0c100311255140c044100c14410f40f120983c0d585031180c0c404c1d0b9880c0d603030b001805440c84185074050b500c980411159036010312480400c205840020664950106001030001348500c0c1e0601d1041e88840c0c2c400c03225910750700d01941030551400000e0745850002d0328919000603c400a0a403414041c4400c80a86400500307250251104c149510240040b031141114903610b440c8190f8419800307889600c0c10f03048050410021403400390754650060641c0d5076500341000d0203400000d1401500d001d00c52155003158040c1049020030641072120703075424859030741564011720801c64070341c0124001c5401d541d014a8a8801c0010044030105224042030082c415801300104110b640000b0750861729040120340502100030b56941c04190f011a1000250400150101030402940 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 273437544 1250 273436294 273436297
    0x317060904080306150f0903190206030c2215020c01080405030315061207090302090f010311040513050609010b01120b0f0603041b03050d033c0207050a1b0605120606 73
    0x10038082c007481104000d84411a403180c06c004e124010700c0000040c46070381c1e400c1c00d00c1410303c00010909800e030805595800103803075010062140180000102e0154100800340d4010500340d11a5002900d229841d2541c0a070f2620f9401e0302c2c640584a658009003455108199a43c859a00304001d141503072100c01ca000109903041600582c000414040b0580314104220b0150044c9200d464803611149103106104298074002c01001007450030302c004001082c0004401c005e61071007118001180e50b141c0c22102503104400001a20610403441001424001544641c801c004240c81c0c0084441001020005903269051425003141200c19401c52a00f070001c040c681184c82650600881140f5260104d4900305650080c2d815600004e8004c059a40600c6007680c0001c0c0414050000c4180c8641583c2c0c82c1d00c046130004a1307041c40c01c0c01e821180d050340e040e202d00542c000250744180320f0500b0840070390780707821160142000282000154041c020710465800510300100148151344907002c02c88039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 273438794 1250 273437544 273437551
    0x813030f0201020f0301090501080f03070f0b0c0d1a0a0503010b06070204020d0e061003060c0c02030a23070b1305030109020109090b03031b0d030509010501080703200a0b040303170609040803 84
    0x307641d02840b41140c5020904040c40c040c28000600050540c94041c0e410b1030120569408103054104202c55404a030302003880038a076680141c1109140c0d2603018290035070340304103003035807501500e409140d4190314030303481030740000c80411185029002d80b20000c0500301c0d20241c1900e0b0b0304c007000f000680010300309034018088000724504001843c3e541c0130159030034011308a600020f4031000400c20301c1040034620450301084114a05282a84029804a6a6003231003c0340601541e041d1140810118411180e10135403850f020b0903503950690303032600305c9825004204010010f40380a400850f90317090509c2a8400c20313405944500b00c3d14a0f040e074034001801c07035158040c0c16000421114500c101e12000d5150711115050041079403c03584a001800c1703500141c460038550341030400400900400050403010350b0780040c101c1551464070200c0c480d1007072000304026000300d9541800107900720f04001038002c99001c0e4a03040040f00c070500d0a034400000c1214515404112280440e0205186402a560 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 273440044 1250 273438794 273438797
    0x1506060c010c09091503080f03042109060806093c13061406060f0c0705040606020307030909020a022e09060f060b03090a26040815070813030f 63
    0x9014003404400742035a0111150401080d10500300f003103060424450100d401319042601049070f42182d442c0100e0f031203245c0e1a10310000010011900340860f1130009070908111000c140808810240e020f003040c0204d104641c04510450700041450506402540c400c1e82a0000f46441d694081c110740c5181c002d0000d95641140400381c1c0034820a100350095000750044007101e44400c4403450b0103c182c8100d40b02000c0c4100050041c8040b030b41300c81085c0c0f4201a618801c90741c8800c01030441c2ea1500c0016070040358054100b280008010f0f802000403c81c5602031380d1078200c42902c48605405038402d0714421303030041e07002580782c410118080103030109500158181140d044032010520b4151307081804165040741c1d60720040d100c00c0c1d40342c0c0300b1074000304920802581103280600c10b480c2c8502c20600086c04685900d07240244082400000c1c40640502c0d2410380e49a58941d10096542c1d0b0707802000c2000312154a0200d0116800342c1a018410380c0c2c02c84e0001010642c55804032403040381102180c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 273441294 1250 273440044 273440047
    0x71110021014060411090109090203130f0f03200c090a02040306050a0507020f01060b1b0c03060106080a151410090801020703030b130b011d1302070302010914060702150606 76
    0x40107052540540c403803000b81007034944994104601040102d40e1034400d03e040860003080640740f1640c00c0441c40085401c0741200688030303038034400c0c013034802d00002c0e00c010b0000210303150303000070040d546260078126406a45e0340034114014032031541f076052011103e070006a201198843c0245458200315510011b104005030030542ea03a901d002c141c0d007050b140718541e03a07128400c00101d10341c100b00400d41d03c002c1d8002441400d1801c48040e03850720600403031508526440344c1c4080b03d020100404080950094129402981e48420041c55144190b95002a40742080c00c4c401094007800310781c106603021000310415980a0408003d10409590802d0080c810075100c00606044284090b0201030f0082d100418140180c108202401c0b09240318060a0351902e0020000c1c1d981c00b40c00c0c6d082500e1029015080b880112000840da4910b641c1c2d02c0b000c4c54000150002095410f42001140921460b66460301c5501c0c0d002d216101d80d0105c55400c0140d20420045426003090045a9040340000d0400c0303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 273442544 1250 273441294 273441313
    0xb0606031306050c07060f0c0215010b0a030f060b160303140601080a020705010608060115020115080a0f14031c140105010e0123030403171f03030507032d09090207111002 75
    0xd503010b040050442a03548da05c01c406d61901407048090769481c0858855466043c186400c000b0302542040004050b0b0b600540c04155043da80410043c1245441036a190103110980c011103500c8280300710300190400304c510440310704840c015401080140c5a42c501070390307003201040085d00102020703220b940d260f22002401100c10701000d4081c01c08035409142041d1080e20190075035070b0418034602024004517080002403070104054a41c15171111494115400900700b8401c05110386040100d603000000d408001c0701c220340b2070712014408002052022041c82244031018500902c00d02d4003103580411002c1c40f544c0314004c481c8403a000ac40e100d01c2c401c43c03604a4005640c000b20307001c0300070620303c039901e80350008503c0c00a548050354055009080e65000030600d83c2c8a4140720041c240000400e0000406010b440b01d01007545a480b00721510584911000c198003800074004404a0340c511408115401ea81c005c480c1503030b42200032118181540d005000c0c8520b1981840d10460080ba407a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 273443794 1250 273442544 273442553
    0xf0304110d060f0c0207030c0b0318030c01090201030f05070e011809090506090f12090d030504081b0a0501090b09061605030c061605030402090f0703020913090b0606031306050c07 79
    0x601507030181c0b0000035440100c3d20a18111001c0c2407000c0195800707075508000041040f00c5a1050360545501e5988940360a240d140c046104140c80c80424040440c1d41240c2c42415800f5641c400c0c000d030f80c01e03c065450030700150122002560040c0005590a002c10040c0d401080852030740c058900114501a42c0c1d049074100f00e03100c44c0340c22640382d040300c000d201c2c000d0010031003c0188000a401f42001c904218911103481c8100c418140c094815201c0f042d05050142c03050f940100b0700042620039480300c0100340c0e8402405140302a22541002c6400309403544204164000c1d04d4000c01c400d0324207038105080044a402c840780320305150501c0c40030900024000d0000d44100f18100000f815981444940071200120b002200c2d420403400b403013008050b070360302001c16070425440811401d15860700103040300a071140400c0140c020261900449841c045c079401440c406d401042c2110060f00c841042004a20080d142076502240a840c0c1c5008949590300407600101003140342072030910b8a90700c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 273445044 1250 273443794 273443809
    0x30420060c070f0f0e07080417070b0906090607090623070c0303080a05010605070b06041d060106090303080a090305040509090a0c0b04241b110402031005130e030f030411 75
    0x405141d05000f0b50342003115500290b03100740600a212010680391910342c00041400c07200030b00180031001e00d502c00c04002000c46088030301c065085540c01841c0c0c6000000320b40e4500d4155140790251041c03d0000e080144104500703415190295561521186901305180840004140c2010245030401c10240000c00c0002550000c6100c0e4031403a9851601c0014501140c3e016407216080c8842001103030000380300c0401c2c09900110450f00015911160b000705800e06107101c60b4000c00340708041c000305607a500000c1d18401c0382e10994660501d591646822000e503900f41c540100400c00070b00003480545002401c695001500c18110741c10b11446480700801500f007a840001d101500182c2403210070030408010404500c804030846011090b230344002d04241911607503c0c0444601c0c100d000400450300050401d00d0f200500564480c2409046001c00e000710384983c500c01d200c1501c00c0c910350030040c041c2c4070490020704082e60800c00341002c2d1819503800104100d8400b00300302e00c0c003101680c0d00c44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 273446294 1250 273445044 273445049
    0x190521100501030213020403080706090f0f080c0f0c03150711100f060b1e0d2d0c0c05030d021e0703020a060506120a060902040e0303040f020a0b030420060c07 70
    0x10000c00c41c0e502d58018004248000a072803011140104030074004240b0741000c03a100140d0001c0002444040e0303051071090031601200041150341001202001d210402d0050911400040241d4051038640d810466030f94200c61802d58140c2c0055404005070782040e20425400307281d909010100455400c2c403203040c2040b112103142d1195482203c000198400e21070000540706001d0803900d00788106005400b181c0f821403250344410400a0480d20440440d008030003443c858130484081f00c03000300596910318070056291401c00c0e1600800308595840b5400d2260030640000c05103190508003c18003001e5406200880700090040c101e8030800c54200d03000f8200c1c180681c2c0600121400ea203030010668070082c10f800d11403c10641e04407140350340810081810707a44044006402c810900c00b09001d01031400c0c4200c014000402044280000c141651240f039200f107a801d45030945481440300c03e800203071070150421082ea00100c4117188591040300121728000c1176142841e2211150310315003010794 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 273447544 1250 273446294 273446323
    0x1b1209060106021e0a020d0302120a08090c01030504080f03101205030c0d0f0203250204020c0d0305090a0b040204051005090a15081207080706060308030a0e0c190521 73
    0x400c0100700960b0305002c80b1020460319004c101c0d032007680c450b4036580d4003043d41d4041d00c502c2c0c40f0b0403440c04060003001040c0b6648014183c0b5a154100000c001e04046400c64804110b4042d076140c50324958482e200300c6226030361089039181007a1420108150300d8000800c2c0c0c580c01107840c1d8012036450120ba0310758038001d100344011a641c0d00040311032801e101c01040c00109000f004130910400a03008400e0f03034800302480c0c481e22400c044903014071080804220b00030b50841d10006680c4150000810103190580f4a51003c1c015034407200109660b030402480c01800320008000490011315058010700d420541c010809a80d2030b440340001200780100395a50020960b13100d4403080f00c0c07980310380034100401a20010308042100280d040001d0311440c00000c3c072400c40010042c0421881d0340c0448080c3d50403d02c0f0319140d181c118008000fd0903070f80c0340503440e07116070062017031a4905001b45240a0fa8015155862240f804060156402070401c4600c05d00010f4071100181c104100894102c0e036042 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 273448794 1250 273447544 273447553
    0x903080c1002030c070213090b0711010f0f0b030706081015050720010e0303040b0403112206061d0a05040f27120c05030a0f03180b01090b0f03061b1209 67
    0x5d6104110340441d18124044886051540120204003d44045039204c50a400c2c41440c850b403829030310340105100182e00312464a041c5e441d0130404115032208114200c254221242c90352036040c140e840030011034849c1c2074699061018024060000032084194002e03090a50030850396985c0c10b14010040d6031110002e21520000034503139a44524a5089084c06401551410b42442e48100c03440c421341c04050f06924643e03209940c0394540d03441120640900304410200c9c02c580c910010701070042ea05c100c00000344284605401c070341c1e8203e0a8015034a005000d60b80710340c90082400050881c49010603546992040034042c034100402c20b00d151a0340801d1440c510034138030b18101c2c0700444ca990340ba50030030810142c0300002034000000c8800320941d07400c01821001c0c640100b01c015004100304550740842c1c1c10904020440d04441080c142c400c0b0050a00c200710001301808800140c03828990b92640c40400032900701c0c0c204103038480ca0340041c008442e25120018081905a00307080c0c40b000030f198032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 273450044 1250 273448794 273448807
    0x3170322060e150a0f090209040f0c050d0302060f01050604080a152d0c081611120705010c0806030f070603090204020c011514030d140901030f0509030903120301060903080c1002030c 80
    0x219205800600c2d044c1c03030040186c000150013040c8a120001c0004190561090200081c8035045501d040240001071520024501c9450029201d4009880d20080d01c0da12100110b51898000c01f5901654082030042920480b65114035030780c1d09480d0305074441d0035034840001140c1006c1880d0100c0c41101041c109000da030100f00c0007803c42d000a41c959080141c81030600190102c4940514074800c994170f40200010030400c2401d04102650700c2001c0c200701e000403803008225040d04408030001c0243c03101c200580d6503100389078403243c0081c140749280d00300c098240030b25030280d0b0028416500203400182080b040501440c01c403860000d102032020280c810800104512121680701c00d03a040d4041c000302d0428036006001d40341c0c91f82c0a05070003e400714048105074801c0d405a040548102320503c4a030170a04969500c071b5001001e014007a0003452500c1c061180a0740c1120b048640d1f543d2880e401d10300d1610782c0c22854101000c40150b602036140c0403061207810b40061070017844003440c016616038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 273451294 1250 273450044 273450061
    0x602031c1406040c170711070b03010609031410050f0a0507090510110109020301020406020114130203030f090d150c020c1206070503090a0c0b0a1e1e0e040504050703170322060e15 79
    0x23034482c1e11085000c802080148400d90348258004201c95014400c0070a0740385913113040b4203005903112110600340c41d204c200410030f070341d00c0800707801040100d10420140d12030100031115807480303000c0d041d004440c1285034400385125860400280c009080000b030f1040407980042c0c20b980c41031b80b140340143c2d1114414074a036a911280950020304944c0340b400600580c3d80403079103034014030501c000c50f002c01044642007912042d9070007100c01c0c0e0080d2401007010311030030404020a0003060b894010f1107002c44800b0181049211b40a80c2c4591030002d0900b1340d038001c000c03076880d44000c020884c1d038000c14034030328002040408420003070080007825940b14200070780c0017081e0b180103081e50008031200c00c801c503014903002815881c3c4040c0300003240910104851041d11340c0e041d09200c00750454940000c01091050200c1c000040da031246200c4c2c81c059140c60280c15440c00180c3e00901d143c045020074541004210345a001c150313201d484040380100d0000d803258209042500242d011035481b10410240e0b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 273452544 1250 273451294 273451303
    0xe0903181905130902060c0607022107020411070f030207090f06290c150117010b03071701060f060203070629010e0d0803010602031c1406040c170711 66
    0x14000d860992110840e51140c0c841d8590501c99940162582200c820750815603070006850f181d0090442c2d940c60400a901598500c011901000140100488d521142d48030b96a40d200c0000c8030510a0f05040382d40e003c200060036400100c0314080da08000550020b001000019807590080e005410a20715011892098481d9009104101c07072521409000c601c54034201090800c0301c800324030300004803a055110300b9100351a9070380d035180710b8240803018bc0b0b007100c0c050a05881040224100081d00d50010900340c40581c2e00607981608001004d2017014551240441102c1500c07001081c01540c0340c80640c40308215401180040e0130000305041840072034041c220001181d12800c40e181c0c0d280742044614421f41113002810440030300b80c0b07040c0f00e507912581c1d03402260308091261343d81d503554280603560b9480302416030042d90394140d0b000d1400c0405d00c01d6660f071111481a811541d59050204002408007258074001c2c40384010304a448160002040340c860107407904e5403108003c0c00e036001480d2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 273453794 1250 273452544 273452587
    0x90b1501090f030311010609110a030f022a03190309050613050d030b0a080601080312160207090b040e060f0105130515010e030304030812010302040f0911060c01060e0903 75
    0x14080d01c10340c20004050038940c0c0340116501403401d9040c20b072454405c18003514065109110781403d001030011848400d000400900c0e40689007040040f544204850507805521418408100f034010f450002115144503005061180801d0742e141c00781c0c91100c0000d0b28640d5084200007035a070410fa0703040040820081d03800407075004501000f51519510650b07104001e81e543c00c1010b498000680158590242000203002d40c1800e80d111988c4030b0038141d50300c0d0000707403401000c81d00075004074124040c069180c5064094907805042085c5c02c040502c40544210b1407401e410595507105005503070310600c0554014050a8a038901d5549440100000910061f10304c02d069481e0800b4000e000e036a105270104525028248440047c0c81540000d003180210b80c0090215580060107071542070320b45900e241628400c5400300701d80c160301c120b514101e6030841c1c0d005003104240707010114640352030b10251810b4650300e40046610b030340380d40c0710000c590810b0300c0c485401d620100d0000003003041220017044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 273455044 1250 273453794 273453797
    0x30c05010305090d20030304210c030504090207030e1f0f1713020a18020903150108061323061e0c0f031009050403020c0a0f18050603030d090b1501 65
    0x40d5040807412182c0320a040044031041c4500c003c0f4450f0100041000c0c00000b0501406980c0c403031400742410050350329052030185d00b50000c5904127a62a01800c1c2c3c95941d0b580565855040c141082c2044d402503205d00b106405021500c455240d0594400032558592965901d620084182c0148041d15144504204005010454001111142c0280c10896101900842c0d003100382002d400407900e034044da50410b244070548003c400300e0b03004150300100400c03a025012100034502490880d40c15540a0203085080d404c00030100700143d01d421100c220690180d40e0b8100c030b003414401d00d0a05040041d0103450590403000820140301c28184890b181340107403903050040e6190030301c08194184509c03415007102c4e41000c400b04200f9298655200040c1c0690301040149080c40cac203002e0750b12507285402910501c14144040342441e4190804400c4803080e0301540100c035a181c1c1484040c101c0100384e280c05100c02d00c1801d5040856001d14182a40180b0900e4401d040c110001c00724040840c88003070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 273456294 1250 273455044 273455051
    0xc020a06091224051602071d0f090c0307150305010b0702091602010213120525050f010c050105070e100207120303020304020f0a0b0d06080a0507050909070b040b04030c050103 77
    0x1019106004000208950148403644041e62032aa40f00100364043e007264042d91914040041007003d80e00400d6242001da0219148256607104030000c03194040300f000f50700b80c2e052002c10b034034100307039590a03412403030082c191404024104042171030b086403981700305003c0c8500002d0503042d2b074040c821103001d000a114646e18080b516008640390072800b0b0300c2c4045680c0346039075204007035100f9410341d074140d0701e4900b103058440ea17120900e040001170600241c0d80c50003003c041090036500c168480c55581403110899000034500310030060b0320741055010034140904941039600244080c807516100e41c0d04c3c0c0d2a40f407100c1c62002c060280b05016110300209550040c8000d1204200e280380b1452020761500d40542c0ea56039070700c041084d09040e91a0903400c0002008007051406143d400f40c10204c5401c2020440030342e482e0031700707543d9640303c6c4005401034002103018465803d10002140c1e001603250100c074052a96141c024409902940c842202001701050610401c1044c0b1003080061000740781c00e1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 273457544 1250 273456294 273456299
    0x30807090506070210180e040b0403081806010b0903031308030a030b100801120807241505060d020c01022502010e060901080a090606051e03122a010f020a0c020a0609 73
    0x40c10000400952409100d484020500c1e989a1895103c0c0902040f192580c95030070a46040303520180113540072000315005400180704042d501c04440340dc0b4002d513004154591070812604481e40c02034085a0301030004004071904040c580b01890003d1035080003c507521890050003c0459840e40e080611802c0409080110560300c9030500d030543d1640008000600da851800090510a0440081003541013072003d03840c252034003540d440300005840d0180911000a001400c90846030301541e6071249050091164200159006d05640d511003000145413084911100503400700040c4c16002944d8100519411541d02c10341ca8044c0d420203039441420240c1c007000180c9202d4004007264242c035a200c15441c00d00c000d41d040507009040240c8205144242c3c2c2c003800702244003034402540248166000181504020402c40356200940e40c07a5006124803c0700c00080c0f40800c01c407041c6c981d920742ca40d2403c1c0c3c907030728030080480c160103444d801d0f0300300140e00c144047c4035010b50200c41440f4580104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 273458794 1250 273457544 273457549
    0xc0d0e030f040320060f0f0d180f140c0105180a080a0b0a0f02040501050d0c0905040203101e05060702010c030c08120f060d0c091503060e0c15090109050405070c050a0308070905060702 81
    0x19580c7c0014580c28075501e03207801c4042030008140300301c141400c0185080002c01403000c000d030125142c1c1e00030b4840c2400b054080e83c8046d9030700001c0e10050b001a40800424120228043c6150368080006040250040c3c0ea480b82602c4e10310100025190130100e0014444203c07040c2c49640b07509c1104800550034545400000380082c00390125000f02c042d1140040c44007a48503c120310041d1100410454590410b0210454142c01b180540c0c003010a044071058910021f8196590031510005e010f05d28026032503004480007140c0b4901201030100d03440b90b00000451000141c08940c580c05545507251070300480b041e03d081005454640190701e0004040c3c04034504040310001d0300c5000c40b0118802c1d50000a2000e210410ba00181c0040e1900d2004c101d6210086140002c0d0781044402c21160100c140c44a56030f4800d070852070b404038024150400c42820180c108030760000d0f8a040221540b0020707219503003044413541c0210f00050400e13003041070403a0001e000c2d00c06081c00380ca10364100700480c0d01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 273460044 1250 273458794 273458797
    0x1209060f020d020604020d050a05061006090801020301080304120c1a070b13050a020603150a0b07020306010e0f040b1005060c010b0415081b030705030f030408060f0c0d0e030f040320060f 82
    0x8040d007d101102020b20a00504104820348907a004081f02c005207000c40c003004601c02c281c002c0b44001040c50702c00040f41032050013030328140c0329032001030f5251030724201c0110004c9800c1d140484068000c0d200000e00d404240e02d8034100022440242c542c3c0c0c800e603151000d003000c030046c1000320340580c862000020850000c0e100100640c107845042ea80c0e19200204d0060190000d0025403151304142e020030300d00c01c1d40f0041c0205030b1098040380d41c16604c410700c03014115012103011008000b1500018013203404655595003191642c1a035610898443c0041829544100710701d20b42a03464540602c0320303041c90301ca54003122124002e403041d1b47d41040c9601da1079a4a20590242000105401c03002c3e69505228003070013031400074101c1c1c4400ba020040c4644a0b0018400c00d0500d014180000f2081d00f101e03808980b00f00380d2848424908500c40d0707034030401807401014801181c40180440c54042113410b0007080514061084103250280040391020500c40d8107403c640075050501003000200c01410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 273461294 1250 273460044 273460051
    0xa0503100b1f05090118050a060203070b01060e0306160c0236060102030703111e0d0915050901031e0e0a060b03010212040b091501090e0606180705090d1209060f020d0206 75
    0x18240c18007140d04241074001144075080140d00003680000000d07030302e03000801050b43340d10514026480e071380e0320388041d00d800c07801d80060f60705900140000743ea610003011211500304554100302030741c1d8159801040c446681d0820f2150b020401000c0b180c2071030000c045081e00a0901c0743d400a1500e031960000b9224021a20001d05001140c454265022014030104c601105451071072418000f683c402a981e6418500350798000c82c1c88003402103518641320300c080344504865141c0900c2e140c002001140141000311011003040c020401000c182403085c041c480c6488414001006038041e2414030b441118000c0641c0e9200760b10410051741b243c2900110b07142d019410040e80703440da41d9001007140c01d007508401c01d501c40c01224400480c00c1e4117103901414041d003006c01102c040756074050503c042c2c5801c08840f110306110b4580010840c510450040640030406031002004031050b682e8405c0c92022a040c55002ca203000344140726081d48600c2a1000340911b2000b02000c903200b6101039210a800b4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 273462544 1250 273461294 273461297
    0x20f0a020a090f0f09060c090603200307020f0a0c050a0e0f1f090509030409140714030c0c0f010b032523100c020f0d0b150a0503100b1f050901 63
    0x2840c1c0549031043c154001001150130040c184502c4406290150080894900e1807012448015010510318881d00c035811002e209407202844803410480000161f42004204204510a5182c101c40c008418026416044c0c4203aa0200d2540d060108010b6001e1840d084189c12812030010041d2280c0103d503000d0300003480380400858820032030110f41084809030080d40ca600c0c140f10602646440000041044031550b0004000841c01c009403a2102c01040d51110300082c1c462480e0f03000400020001c40d04403010b07024103484c0a150603461814016108140d060302c0e55501c00b203904905003405180002c902c46540c104d219107141e00d0f0034901c0d05441c003440c3c008801d10901c1c0e100e408009541e11028803801000b00030350012500c40104031405151040f40101c1214010f0800da04005103c0c0802c0c680c8043d81c201c0c0342c0d40f0021030f902d90b070a108030b00c0c9600c403007200000551603c0038070482c0d0050030710b9500130640850050900440384000e2400703003404507044c1e420804080c0e0100540300d060340f09 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 273463794 1250 273462544 273462551
    0x80111041509030203070e01080105070519030b0102010e1005180601050d03030905100e03030604060b1611060906040b1b0705010f0e0f0406060c03081e040201140c070f0303020f0a020a09 82
    0x140301048501142c1504000d40600c20080b000c40d9038241003011504842c603d000a20003a0384500040300c65004c0d14040500c5441c000c2564800c440c0030390010b019840040c03000050160180480c14176201406a0340009a41c1c0c5100740940c01a81039038015050300300f540140100d51501d80800c004414a01c0040c003016540c82a403410003209001604078180c0e5180f050005a004140050302c1c0d600c1603400900c29481c01c600050511944819030b05651061644440d0b1800652500313004049000300c460b44c040c1b020456280b0590780c02015001601030320400d41c2d180d590130038103902038a0700b100300c0c41d01c258400001003000341e074041960103083c803451904094103281c0c40c0c00710b0902c051742c01d0403507031080c241000401c81d1940012042110f0340640d072150031507211900301060501031400c90140d18008600003d0140d40551122428864151516841c001b1100c9c41b65050290075000b83d0f006c1c400c5501c0130403d040d0304000480850701c950300a021030000950000300b56480b00d1041c501000e44 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 273465044 1250 273463794 273463829
    0x3090b060f1810150915080c04120c030b0405031201080c1f0c02130b18060f0f0102151f0611060f0a0212090106060305090a050c0f04020c0a03020c0a08011104 70
    0xb040102c5000410024181c0781c0100c400d18001740501c00740780140c0006180208221401c14421020940100f014444e443d103170030b0070310f10100b000c1c2e5400d44d415111407202d440c00100141c86c005c40300d1710450240011303644903140011040e0400c1d1040c1c1c0001800e600448070f00e41c00e1b03030b15419000090f4101d280300b07208628104400b944c090740d0010029512403040400003440d002c0359000f11401d072030105d418103031100d02c5040f0024805815211340d44c224103100200f0445090100140080140500448004001d65102c1504400b0102ca2441d83c10140248141c9120881054800070300350340d051008052040745001035603407100a00380c0c40e2407120800464800441035040381c00100b030500c03d08600b171a1452800d4040e018910511380041d2800c070001e0702d624404101d20503d15800006000780b02c90320300802c503210b88081ea610354070a6080051940e100c400b0844402c2640c4290080c0001c840100700b04461042c0030303440480075134106907030222480c0d03500e02204c0603100c1d03142c00217581d000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 273466294 1250 273465044 273465061
    0x90b03061603270b0118062304060e01140906010507030e090c0d0e010b09061c0602030718091e0b100813050619381f03090b060f18 58
    0x2d802c641c1c62440d0002c400f20800e211a07020094145d4102d106400440d90741030110b001251b40742d205100364540c0b022074203188501000e00058440384001d1002c81c1940c0c4074500801c860740b0a0b840761762149010020002c540c280640c820340d01100c00d0902d40e080002e162409410030308070000e8180300f04030ba400091000c1100e1400d0b54000c0083c5901008869181100203009015a449107403007814610001402d51600384171040541500d1702562180c40800e95580b000380d00007400301c00c180020301003100060800100d45500505602401043c1d103410303800c481802480d2400c0b01c0c0c404500f0400e01c0340300c41d1904450300303584084a10f41000b00b9960090b01200c90240b0300402002405900103200451145201c0591442868078040140b103400d1400e0b1070840c9800001d105000001900c1c2d843d585800902a840207100901512598030141c00d0f08864043c0034464400401e5403548541c09210b1005903240d84a41309607118441103407084001a41e04c8407460342055000c48a50000b032020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 273467544 1250 273466294 273466331
    0x411010908030310090608061b030a061d0f180d0509040e03040306090209010801050403020d030f0f0e0106060e0906090114120609070e091c050a0507150204090b03061603 75
    0x1c04103030040c0da440c2d00b800980684c1e101e09600c140040c060401d040856000004920a03011300c0b465080100360351001c2d1680b40f12131704020640203980d5900c81c000210300c00c51284007699401c003444426500d2034003640300c6030300c09030180140c40d1030340c3c0741d400390b0406400010341524100c60744d0409588500c00100010041c290940c1e00d000280000b1400000304040c82c0c01c403900c43d49c42141c050b02960b88400186d8201c0700c0c00c55005e00103900c0424181201d03030186c2d0081f0340e07007120b030100442e0400450740c081d000e4442c1041442105d0395034440402100380e0003228a44084001c0351600102d0415400044e0340c200c06006400600c4560080341d01166900300309035200820030700680d041440c0c01d070040c1d6101c21045c80b560a40302d820070b001070040d120200781030900413003404106444099819044410b82c100114909c10720900300b013544045060301400d4806000443c1016a540f81051244010344092a519034020341c42603080c0509a00c048120804485140c03500040d84000c3c0703002d40b0042d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 273468794 1250 273467544 273467549
    0x90f0406090207050607020d090e04031205040302061602070506030f1302090c07050610030308070c060204090227010806010f0c05030702060406021c1b0308040c0b030907031208010b0304110109 85
    0x5403a00344001080e003600d8028020701070040d000e071101581e8920090383c0790209128440d000800c543c01c01d0116030101641241c006009281001800703058840038011900c3c286d6050300503074004801c11549035140202552560203500c05070a100e441c0c5804144140800351000c4900b20805d00003640018035070348641f0040e40c004110550354104000080d0b156444942d00381c5450142c1e4000410300650507030310004695145da5012481c2d41d4148044a5078001c500c4100d608903000c00000840303074418000362002d803491540032501141e00346060041d5071052281d10703051004c050104566a80c010710400072604050804980104040c0b034100c0c214842c000b0000e511600108002c5a00c81e40050038848001c0040003400030302160000039502d2104d0095100c0c0030018103007050002a10075180c00f40c0082c442d21003544000c0e103540703980c00c10350000c81e0001400d60149a00300144205c80701810002d1560742049603441d4184020f0003190710006101800c80c140020503100700740d1089503242c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 273470044 1250 273468794 273468799
    0x4210309110f310c110c060403651512160b090415030512091c050303041b050906040209060d0504080d0c05310b0301060302040603050a020c0c06090f 66
    0x12001c0c1d6403030040c00f0b16030052a505c0c182c0c401c0004075041401c00c03201b11021b494201403041442e02030f840100c4400140c4800030030390b0082159000203840004145004006d0000c611004046188485c07600c03028040f001210f043c1c2120300620101d209042c042c401d1303204007600c002032540340f481d02c400c4c90049160128a031117615048001031050250300600701d03081c0100d03400d0000d49408402c0e114002ca66020243c1030390004845d00d40300407140001418075001c090455840d50310000c68146590140400c103881941002040008201c20082c803008a04a682d0039000800c0c2444085120004c1c0200301a01440d40026804030b10307601c00301a034440c230015000c24003640c985840e02d2269a00030700d0681c242c850400c103401c40e095000740c058945544491050801e55891710301004150754045c80f840f218820003040100300145a0002940600f20544001da6241d141040040032910014000c803007461042c0a11901108081508101200e0481c1c1c4151100311020005020398121601583e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 273471294 1250 273470044 273470051
    0x603061c0b0423010207111014030109090b0f0106090e18030a0903032003030a0b040603021c030e0a0311090709080d020a020307060215010306020304210309110f31 72
    0x400065210f4464190319415588102c00c00c8000072034240c1c051444010078440c5000103041d06070404003407030288800310786003600000f10449145907065000f070700032442054440c19a4802d000407400f8a036002040509102c12540c0f44c20070080caa4603042c0140441c41301c400000c642c0c141400da0300050b481c081001501d59a00032b04a0140008000344401c43c041485612840248801425505000d0156401861640c2e98143c945401850041d21959010741d407100044003584a422a10381c0303e198280017030034140f5081c14090b1401ca48031001034842c0060f5101800001c0080c0b1003070803a0030041c0e5100b48a510b40b00400d54016013141c200c00807606c201404800b105a00080d8107031154025420f589005444080407a1142050001d511101e541c40c4010030008441e0f5004640c0b00b4003480e0818041042e0f0b014010503107030100c580400003a10b030071800b024041c8107c2084081c590449082d940e942c0940007061100c041c500e04c0740c0211b2036940c08100c441d00003000c10f5488020050040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 273472544 1250 273471294 273471301
    0x406020d0c031509020406050a0503090a051213090504080421020424091b1112070f02040b0307030b06130608030c0303100905010b090411120108030c0d0e0603061c0b 73
    0x30000c003d10000910702c00c11030b00000903501014800c071402c1d0380150759100d1601f000e41e00155182d5001030440112881200500300204a050000c04400e0001d0300f01e065892003640c0c5c200040b10380c41e8001080803481d100078000054041e80446048071400ba941c13102540a8803003002c0542407400740a5003060400c1c0f8031014000c1040742140d0705121468507011110b454141800840d4a140032108400403907000c0100e0041c0142400c00714065540200c800440300c228444a15400c8040c04958806602c1200400c500d0540202c81d000384050f001000f81501d10344a05e12143d90142c044d900401c0700310803080d9182040c0d040f01004c0c01c0b0020032283d85002c250081a5281e2080703074146401020f528000c01d807141c0c1d0b40100c40c121441401c0d0030341410182030801000740a020039141a904040003a81c20b14200340403014020f0046501440d11400c81d00d2034a400c11803218248402c02140030b016461980c4c4541c107036030f040401514036183c4c0d0310003c04540c03d10140351402074105504031003003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 273473794 1250 273472544 273472547
    0x60801060812091804020307230f09090d030203101a07140a050d1d09040309030201020d0c020a210b090705030706080903190302090d05060f010f0b030f0406020d0c 72
    0x510100c48000741200c00c221601d0400540c14040c52607980d5001d4940480044900045422240c00500040c00e440798a41ea4541001d4600c4002d080102c4d10400210548421701e41010107819150040c0c440c8145403516006558540d10a0a021001e040d40031021580a814111184002e0000300e1042e5541021010314201560014601120b40c1c01c030240c80381e40d04a90200b250081d19078018014503030910983c0c800d4541a400603403506a03045020342c3c60340a0756603041c1d81c40c000c0d030094035035115503070641c00020700300040107214405012000401c0307401611780c0c03407030481280c07003440ca58401d030507029002e920a5003000c04054000c0c9003010a010442201041c030404a0740201c0c2164042c41d6500000e40340f219044844072010340042c803210800b01d2003440c1054072818035280041c078041c01e9070000365107044d18203c20b0b10144d01a030104500c020401d20420302414070146200416484c14100c2705e010300c0010b000c880700b40c10440c007241c10000b4030f8040d42c408010300e2005102d0200e41420 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 273475044 1250 273473794 273473801
    0x905040c0201060f0f03020d060f02271206090c04090203010f230115050703030c02010603080d06030c090b0619090909080304051009020a06111606050408070b04081506010e04060801 80
    0x21904411040d900000e40e120340b103017031002100d07806040105408159111000181214801c10300c0140d002c0018494842080c00b10701000002d24040c02d911407684801d002481d2a80810403100d0340c816401d010705120001400a101c1000301c0d1b01140b8119a803022a000d40035498135000006d040040440a543d650003052202c2080104040d5880c0c1ea907540400407280c01d071000b00302046c41040100e001c00e1180c0c00007180683e2900011403034964950321000c15500443d82d44480564840043c420800c901080c80003c0652aa09204e0305c0d030143c000940900c0342d50759107000d00b00c105080c203c02170301861481c4000c10003854100203003203e9050801055108540031245805065a840881410f42c440c03441e40d241c0180400d1101e50402c0d0302580c3c1c5401070610484036214510400c16401403208000000c1e18460b81c40c240c90303a01c4c09000c40d240000c2d9800c40705a01a05200601c81d0500c0060310710301d0380340301030222849501c0e411b0060b5030414001c55000d4003e0b08019003c140e0080540 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 273476294 1250 273475044 273475049
    0x20403151e15051e0a03050c0301060f0807050909120708090a0510090b0a1103030a020d060609030528140615040e12030603010b090a060e06011d010f0905040c020106 73
    0x20000c48500d000400c41c00100c84070124040e05061a0503000e108a0501201d0450304507400701184200c3c00113480081d055117610750040300c4950208483e5016800c3c00c0c0590001401c505000d01081030410038090f49890760340c0512801241c4810004100700300400401c031b10f181c008190703180d1b241b1460130044825801802c800b0700036821810000380c54280409032543c803000b60340e9400d03100c50070903a280700c15500c80f40c0303000d0030080b200c6004a010441400114040c1000c1c200c010b036200300e120561800d42e4107640c01401404a502d03001c0000c510302050403040326810036904801031400e5840e412041c0d01003007014100c003480f4000b120b01c44000040050081c04c050300a9180114040100010346002c07141540c2950025814094100a00b03030245400c4a40140080f603221440f10115903c0102107441111064480a003001400c09581d107a84e041003017072030b0510f0001c8401c0c8006503000c00d00c4001c503040100380c1c03410241c054800d180754000ba04004009002c54482103800a0191510b070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 273477544 1250 273476294 273476321
    0x408030a0c050c100b01020309150301030c0b0a05031303090b0a0807080603030c1519051603050702010b0105090904020a1e08100207050c01140c072d21050102040315 73
    0x22180c428000d01035803c1e40e084008a00041104140d0714820720054580c1c00e0066055100510800f016980c1c0c1c6120780601e40000180301e40c880d80745043c0021101500d0b844007050f007104100c07215017554808102e960020b4511810000007031107141c02c440d441c0c840c0e44202151000490003000141d0f110a101b4003d801540d2502002c1e1141c504050b140c0c8a40340e00081743e90301008a941000c05010019036008528034400c403110841c500c50442603407401c03280000c120404200818a00390588207180d040405c40c402001914030f550000380040c03080004c50f0340309402031030006085556248a82c0060406070801c502c029006220030440e821960003680c40702e00602d41504810300942c4295514550088000d09040099000540305c006014031001c8910030200900000013004009072801400c00c082502905281c9600420641d00c020303450307083c04c050301c1c001003185075a0b1901d80d4400c1c00e40740792025440300c110b15040e40244202e0784000c00240b1303050140107224060ba03009240702d0180303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 273478794 1250 273477544 273477551
    0x8030114010e0a0f060c0302010608070602030406090b03060603010e09010e010c0201022703030301260a0c30080d2309070e0c1e0d0f051b0711090a140408030a 70
    0x10b40c01040081001c034041c562401402101c00c0008601c24603200000301e0007400006003c0341c03100c0c609130170800640c020b100580c1c000a41004490340c80b080d040003d0890180017411410100300250240c401882091101baa890300030545c9814290320a804000040008104965807070101034081e4001c60aa040b18940f000d10308844146100c241c140f50020040c00f030b5256a00f46001c044001c0c085540a44070003481c80c0854900840401c00401c40f0360040310840142481c040d407007007001000d054504003148200c9407003000c203480303410f043d0a10344d8013a0791a43c0360301195106900400310300e1080314204580084040c611105010440e024590f94003e0b41c1203181c07a01e80ca110003642c00d84903008400e4080180003550140102041c10290900200c5850a031404022105840184c5c0000b001c0950300e00030f2114204241074a48464018400140e05080b00c0751201140c1c80911344d030090007038100d40005031007211b090340400814084040c60441c20f00300f50400c2074054000701c607800c0c8101d18 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 273480044 1250 273478794 273478817
    0x1b0d0c0507090606020a0b09120c0a0b010f0b091e0607080415020109080a1d041a03060105041109041a19140402040e0112150507050903010f0504050a0305160803011401 74
    0x103015030810f440943d0002c081014159441c520741f0b582c02000d1280a014000c203081c00c4001e4a0b00074250b8008110003001d18641d5414020854007060b807100445203d003040c03c0000c40d041c4410368212200441c0d211803120b540c0d1900b1f424404411859580c0100001707540703800c2000301000340041e21680b0a10820603249007400741d00703d85401760041c100e64414480d00090500c0340c0310b008451250281c0040714540e00501040a4440300800f6407400450f15100008a00341009000c3c01081d08a60500c140d400b624059209032103400c007024003503a280c5024a031410802d010f01001c0d1074015181e07040e0f5143e01e2030600181c84c098000c80c00351821440000681c0d00c8c103402541d050b220b900d80d4507900d40e4a40b0040c00a0b07806401000c60f80440628010701c0a00550711031a84501001e4864603500c02a03401054210380d018156144080e2824043c000480d200007825811168035040c45680d5103405010031640f1000304100405414001002141400c407480600100312001e0301c80c0034450341c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 273481294 1250 273480044 273480059
    0x70506040621052a1903020a11060403082a0d0902010212040f050f030a061b261b071e0201030f0209010e010302030606090901031110051204081b0d0c0507 68
    0x140f0903283d5207003081488a407000e03056441c03000c0c8081c1a480b0743c5911310f800500951300c81405000368145010035404070b1000f400a801c403080d00000e29400d0041c0585180c0396602a050341c070060a2210550504442c496001c010b600d2540c040c0c0e101048041e440340c4001d05818050a441c0d54101d0041c06160304400f900c8003002d05a90617220030444d04250ba41c10a000e012090710010a0380782d040c403e02020101150203481400c0d1041d070010054010800382c4100074002c000450b90801003201003901c095840a00180d03450703046a0920301003044808035004001141c0030706603000c0c0021901a2a0f452210610085800c1c1ea078401c4c1c9003440f100348401243c1e0103e0243c016203a0200d2070380340710b00d80c2543c42a402542d0000c0300a000c00e04000c5000041002c0c54400d030000c03550081056602c0c8013070700d000145a41e60203004d150035450070740d44e90361591503070801400041055101061900d0f030082c1e0000c4680c41440320504540c1d030b120031000001e2481d03101480c10345050081140100f40007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 273482544 1250 273481294 273481301
    0xd0b10051e01120b090901092001270305030f0301140a030302101d0f0a111c0f052a1207050a0b0c0703021008090d0c0f080c070506040621 61
    0x70100c6200c01c119240c2008010b5079410203c40b00310f6007060f40c6441c400029035602ca00305000d02601c0e0000544004180380c8114201c0320107a1440d5401061040c9210030784c2e004118655102443e1880b0304807000144405270250000d8000070a140004150704003071aa41e04003850413a00b0072039160f40506020b01c24071102d44194040500160014040e051030b984158004602c0400e0301d00751441003a00e250300f002d04000c6c1c2d00701d0307003143d079000861880700b80400c01708813000c0f0210481e04040410352091a182c00101b05000041c400d00b58040d4203010302001307000540360386166501c0717111005940085d00da04072a45522003840740d4000b524be4540440000b613030f001a128090003807030109003484c124090982000e40d103d42a44910700c000300041c1c881d00240c2003569155114259241007558001381411483c0300701c20200109030084002003602001c00c0d500c6650045042a95000041c80c121b013001c04a822441d0800d00000c1c0004040313510183c0150b41040c14030610944599007008402038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 273483794 1250 273482544 273482569
    0xa1b02010801150207031202010b091024020a0501020d0e060a140a02130306140105090c0c030301031101020f120d0609050603370b190b10030507020c0d0b1005 70
    0x1c400344018000300358184000c2940c11118012501e00f1552036540400205100500c480180d440300403004242c02c02c40440341e04050f4014420080c0b07410300311041002880b920f14030400c8004128410007541c000e002100d04180c010b002517640d40da1750380c440c1c00600861184400c8610814000540040061003110b6409400c691a50b109849a40d43d690181d0000204400f6010b1187c600000144c5e807032060064902015000303c1c015890301c420440704100044c941d1074150300800003d0744140e008030849041d20fa10410300b41038242c440c00100e160070b4091070f07207541622616100d401605a00f07070183c254840500c074180030742c45d141c3c035500c01942c0090b038100350503034020010718507018400f01c00d00501a0486030140d00715501c0c044407142000c25102c01b92a02403209080c011020903048521405900c050000d00080d02c545001c00d2010403038402c03017020591354001045080d4424401c001000070000c04606403902c460900c210020350954481c007040d4501e28000415003015500f940c1c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 273485044 1250 273483794 273483797
    0x1031b140f0f0a0504050109050609180d12060e101703210705190509031501150c020402040902072004050403090b07080d0c1e0206010b0405041e09080a1b0201 70
    0x1e202900c10a21084584100140390b00c20510032000ca802d031514400c1c4c5008280101010a80341006020301c0f04608000c0d05c21086045429505c14001c01c00044800d0309004030b00e040a910801c00c00a03600600c42d5801c690b201040000a1140300e8981d02058400d0f40c0c0243d2940300500c8140d201241d8900c101e0101c00c161415000440d4060b00c1c0340c4141c181e10a076141030031843c01c541c0d000d40020000710300a100f00072800c00b142c0e40b411800c08121051204110042000311135040455503611101244110800c100183c4c04840c115156034050300c00800d03001400359141c0d000c40c503000344854516078201401000444203807441e490075000381d5000e150552074200003241081d6030307801181d10001c003d65590004100b030b2403006c0e015100d035250407141d40d86c94030800340401c00300c841c15200c070f09a500c00310750001c801071041c61034107011142142d000715030005000c0400c440e2520686107480b4210240d61510385500705003c1e00400410604456542c0e800743d00c1c1c0c81049820701c0882d100b0b000b90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 273486294 1250 273485044 273485059
    0x60604180b011d100318060c0906020d03200c01090503030907030311060c0702060a0908070e190630080a030207050d090b12090f0618280807031701031b14 68
    0x180000d001c2d9000041005204241b080040d1080e11000195420440c4000000308494410000940d060103400203038589403030140b0040d002820703a40c0000d030b840658404002400503072041c1c500c400b5800010b00ca03500a054a07107a03d099060540c6071040352000364081a07104542e20240a801300350300b4418400844100e043c40116003d02c90f140d00036004d100c080c00128507022950704820001c0c0c100070204111149040d1503c0b402660404200400c19440c80741000c20602c11252036041e03030355102c12014410944d0070a2401d45610354a84a01c0c05010702900007a144d03441c3e61b16400034624103000d50221141e82300410b030100e910700c82e1481006014901840000800a512100c16400820120442e400d01c142091400e003400015101211803032249902803018401c24030070703407190841c1c01d00030100c4203815045c00b04c1c01d007000074070090040d18001440780415004014075410303025100103000540d03840785000b8001d40725003070305000d5010902c100001c18241d184412300d00d20a0107030840 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 273487544 1250 273486294 273486319
    0x60c0a02010c2c18010b0703030e010917090102101103011502070e0606031503060f09011802011707140304030e1f0c0209040303061d040615050603040b060604180b011d 74
    0x21030007905400400d6131001c2412003000c40c20f142152000d010f07001a80744d41e65100c541c0d25020b411618850050010344c4d04202900020525911004840000313660b05030b5550606000100c0c28590580401ea911524000310000390350072101c091030582d020300c00b410103440c1d600d5070166a60595880b85040400400c00052031508080c0c015503004904024040751115a01d80041d0410108481e010001e12214040004008090154200c00c4004901c2c46e5040d400d182c0008080c00342c0040ca0134010070300c21000c154045c1c03090003600e10803194070500a483e13040500d0014800c40c500d048040c4200844141c0411450343c449980c0d030342030001c0e06d60810740c001950a0116035840140700354143341e40e49c040003a5103c00d4039141d20f0b40b480c0841500b9101d142034035100b000c440602c1014107a00d60858410b200c80d860360400c40e074000360440c00803031941d980c1d100001d14a01c16038025882e00e11210000d46d11401c11900041401c0700242c0341c800d05540c0010b0120341d010002241c1940c000e2081048 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 273488794 1250 273487544 273487607
    0x20a02131116050106030b151f020d08090a02270106140702010e03010e030307030b0a0803090f060304110d0807031e2c0d110a0602060f06040e0f060c0a02010c 70
    0xc2c2d0b000034461000451403a550b80c807061550304007140c440c8108a0050306640c2c0c1403410700944180c444440f201d4031041021404000d540700105001e500500c0362010104185003403c002c0c4600181c1d000b0300c03042d821115640d00309014101802c890621014208c0085405400394102c00c0390f03040c50091681c01c1104076001103034003816040c1c0403509956910b68006440c0710034001184100d4990724042101b180207000c0c0000000240c0c40720140f80c20a1000c00626506c1e071900400b015801c40e2901e0b101d40b2182007907012002051881d590110044000508000c2c402c0050803d0038004d45404640003100c1444512007071107100d030f50000070040007046009034140301d8607090401c50342208c494851950701c085044041c031044142c0d4142c03200c0c03020300c40d946007540303028020b480140301600d2107044c40d2081318001500503100300c1c45513449424010800408011454a405001003103d81c6400c1910b0007e03499401880040c0055081a94030290303035004481d4818007602d41034841c0304400800c0c1c00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 273490044 1250 273488794 273488827
    0x402060706020c01060e090c060403020303030112080f1206010f110607031e020304060b04060501140717220311030c0306160311070b0703270303050a021306020a021311 74
    0xa040750030550900100e8054003092061101500d40b021842c0454141440b40c5031420300d007030306828410700e030800060006803004020b8a04550f02603c0d00124040540707041c48050049080b0045208404592034800f0b81c0e205c8035050040c4000c0c0c8808140900b0040e0072100c140100d0940c803010b034040d00c080781d03400d8426881225003507143d4050f41d501d01d16112002c001e030f0303105981c1038032110345a1400140c50b00e018030451008210034280011803107843d022803012070280c09009058801e02c8422008680c18240444440800f442503441c81c014034401c1044e4000d945000540300300325041034020b80da040014068201a80c014002c2ca030554440220172100c0d09401503102c10542ca4038050004d41c0307210009030000500c03d403280c5e0000d181202008003244c2e00308400140e00c81c40ea40c0402d48040038848589407442e007500c3c010609507147c0210002a12880070624214040e00000213400e0b81d01060f0021160b2007166003101000c0c3c0e6410b83c80507192400040c07018610304200755000c44800c007a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 273491294 1250 273490044 273490057
    0x60a03050c1005130b0309010507030e070605070215041205060c0c15090115081c0306230102012408010605060307020607082806170f1902010311030702031e12040206 73
    0x180084c944603d195001885000552101d21301d01c4000c01030040068082c01925401400c925040150720042404240c1e0742c1c50030f20038041408000262107040d5290018030b0041000e10584c001d580740d981d0004031802c0680c3c00000e45281c007814007c030360400003e40840b03110b070000100038072210f0030a141110901d00043c200d034100350350b5070081c28155410203c071074000700710140140c02c5541d035049114405011881461040500c0d02505100f0f050b0082486011002e0101c004079100b081040180e005003442e40c0b00303c0241c0000412012400c603194000c40940e11242c00038000255684240901c60200341c03404809a0003c1b40002c90740d51040036541c0e8468003510502e4000c010400031407000322083d21407030240ba92170314414040c210180c0d050180041c0700c8030042900d10144601207456038841075000322140103210b0b80f0001c1da80310b40c001400466603401c200382e480c144508080e50b664400f44000c0c030003150b600700c14a031307000d000c105a03209911205800c0085948960820282c1d90000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 273492544 1250 273491294 273491297
    0x30402121209041e1a12120a05250c1703160602090d060c0c0c1203020706120b06040b04090c05070b1902190c020127051509130c0305060a03050c10 65
    0x294848007054841c1c06000d002501c000c0c820440c158801d000d0041c1111540d100421581c010f442298621f514181268818042494203035290032030303070460444002500f41c0408106a0320003140d01031104103002c1c1c8044981e103400d44d44801c21001c0b0340035240e000341400001807819500c0f042002c00c6144d0001c141c10f203030060094082d01e0741640c5100803265880c40482c0002d40c040500e000b0443c24501880c0908040740b9240d00790381460703400035901c100902508040000603002410429801d80245004800c000c04854070b83e9140d030030450580d00144203000d02681001144c205807405441118006608200c1115a03036807500b030014a04071080402224469007000151940e503a05000d051083c92140d94241d5007400070300004005001409058061582940c650794400c0411003131442140c03000c1e54851004ca2070580f80581702d0044c49001070b0010b080c04e030107029208250748099070081c040c0d101002035480c0c03541440410071490000a000754010801000d141c505415041c0c03c0c0c0015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 273493794 1250 273492544 273492581
    0x90b0108220f0b190603020306130201090810200f0a03111b0c0901080316110307090908120112020109032010090612050411100c1703040212120904 65
    0x140d42d00d0000481409000399124082d40c0203200441201c42603401168031040c200f4440c40303080d500001c1e00c0d010041d1004800c0c00e0291622070444e40180c1c641c00082000d2000d9078150b02c072416246000d80481c0580044110700540d406441014403001d032001d0388144a01a81401070108045e001050754a501d58114403042c1701584079042d2555500c2601c60812001d000e800c1174607402c0c01240c1006070005405c541040c080a081d2045520052494641004892a81d00b42d494042070030411540c108103041400c0089401c1440480301c01800e29000d42d101394810341e1f80c1c90f01c030450100320003000240044c220030f10030000b06040c80d41c001030071714209a000541901c1c4c0d1002a82800c1c0540044020070b5503c2820402c903030300500c0039030100003044810300213846c0a6444d020442c030128070b0541b0030059240c88100c1c070340c4181d8400d21450f5100c4861800e101e60200c00380d81039002283d0481c4a15441a4a0300c201c440100302040740710b105042490400040e04200805825000c0070441420386 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 273495044 1250 273493794 273493861
    0x51608090309040207030c060b0103060311100e100804030f020d0c0314090a0905010f0f03050a021507060903021605041b081803130e0c03091015080d0f09090b0108 72
    0x80c3c81c801000d0071403003a250381d40701b5543e0b0300c0d00200b503522442969061520300002000450010340d408041c107942220541d1443d030407080c050341c01e40400070913543c0003002240e05090254112032203d001c0c9019440e0401c80d00e5644c0012607866445071000c40009401505500c00280514040c4030a00301c0c07890a80c2c10301a0900c08200c180b80346030300940c40c2e03076100c1c40100511400c81010b50094007200e1000c1c01d416007140c9034189c2e02c0c5100980240100c2c149544000d03002d9003075098901d480e51084085c0104203540c2002075070b402425414424084410740300003051b03d403e01c9802c280f00e802000140c02c1d520440c4d0b00781c41003a0000c015000400301088102e41442040c0000d05c0c0182d9012385000a0909166210b89080f1004005100c601302c00c00c280315550100180d540011500c071240400d070814140d400d14250007443d0300c103504610070281d80d00c4109402c800c0b1204040301030b6076042841999491084242d5440182203400301c1c8074040410f540e0b20a490b2104418000003102009110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 273496294 1250 273495044 273495049
    0x3072a15090e0912070b0a090f050d090501050306030d030903020c030a0515060609010c060504080f030403050d0b030601050a0e1815090115051507021305010909030e04051608090309 80
    0xc0008001000031880326041c0044440c503448030341c00016102c01020b50405404400400303104040018044801c00c00c0050340c2030060790070580c0515480f03c001c910440280c0303080d5541e505581103203404a0601d40c1c000c01e0651140c41031301e00c5090001c1c01044604641c113001e40007001d0310354055045010b9503030003110a0701d04102d0142400c2c803500061442003100e42e01100d4810004d01120302c22901002007091683e8448240c802d40394101600007020344881c6040c030b8040c402c5101c0c9845e500e101108000626030440081c000d00c032800c00050294000e504101a10392100340074040d80050003a009026018990344442e030300c41c802140203e60051111003947c07810b25660880780312490550b00b0050300050a001d4820a03004181e005200c0700d0500380029442c884a0440a1444601003480400d643d5082004c64000d100050b082149513118041000504a5108240c022801048220165040034070a0b00d2180b8074010700110a80c181d41c00c122400e03140504114000e20081c041e207161907 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 273497544 1250 273496294 273496319
    0x10c20030111040e0108060f1f03020307091406091b1e0408010e0f0111190507020909031b0703020d08030907091104060306090212060609010309060518070803072a 72
    0x1166030600d15100d9140c0138500ca0910016000306d29240c102c5814441c03108000c90743c40303800c0000d2019111040c1d42203d0202031380791256102030351502c40c5442c00641d000540e40b000300c030141041101084c6a450740c0c20301c400b050040d618417500d003094034001240584074601401c07080728440c2d5240c806030340720005007001c0d401c0b0350044100369540340b80c1d00c1c0d80c5050030024501d410307804100a000e0b01680c011a81d132180502020355070a000c00880300c0c03000034030860840d200c0340d80c010000c83d0681020342c42d940d501c0e080401d5401c0950300c8500060500308002842c00308036a8001c040715060a5203989031403407500060103039030183c8610366001c00c041085014002c640c107041250f080d202d514080004055030b1150380a4643c00f0720410030810102c55206e8103a51001065034204e40d11a800d40049000300331028002e41150704c0c000c2403188540c12800c0b01101a42c1c900c0071540302a4440c0d00c680e440344241030008040082441c982013002200844294000011010705002c030340d5500c1211400d07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 273498794 1250 273497544 273497561
    0xa030f1e090e090a1a0604021204050c040e06070c03030902060c0d090603110c060606130503070305030a18050108060904020a180b03010b01050f07060e03120c030405060106081308131e090515010c200301 89
    0x147c0000c3c1d290343316070400d84140798140720000010100c90518450151880340c50013405010962150784075015512080111005401d001c0c0c211400c41851070001400318030540181d400107410041480041c3d0900302c05da034010681c0002400090311580d0400c00680c0c4000c4401c81c008201140c00201943e05126074801140a98051035490780c0c000d03001007403480c50841c800c0325413003214000c0c07010703903030081c01c5036401107042e182d4140c5900c40c1d00004004079140d61100d055103005105d2040700c108160032a103001e074010340081c45031306000d00055689001da12841d103800b000500044001c40c1e90760f080390400e9424241a0303864600c84e10300074900114111015103d07142e002045c0020800c0801c10580142880c0c83c2459407070402505660103900e910703038013910b50100896080c0400c55100c2031240200030340966030344040684940c61800d062184a160034052803c40003481c00700384101100150041655000062920795541d64000e4883c0a0b00c079456100c00c4915600d561800d22a00c00c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 273500044 1250 273498794 273498803
    0x9020303042706120b04060906020c1605093310090e0a0605031b01030209120c0a0602060601050f07060b04050106081b04080a030f1e090e090a1a0604021204 69
    0x16410350705400c04403404101e0032000b401d03030318100c1e040180302c503c1425024000d51120a20355241c441d420094007a0900307042c080e1160303200003101d00640700d000540b044ea407140358910a0302d00e03507100f00708010010b040316102c04203025050b1581e000010803460b0805002840100d5501d80c0721003000c507044800700354019012402841c01072080b000c0d00b980b010391000c61800180300840c00c0001194896000c0380a00301c001e86894000300c00c50380a90140e420310761002d8050400746060281c0580c0c3c1d40c01d40c0c850b5078000e480e01140440c030184089142441484113840d030a1404203002c44101150380000030550704070b6551116110320340d9460041600a01da15514810541015104001094004080111030352410031040000041c007146603801c035074044c10008039000520303005403401c0345104020006105070340858440650030030341031002d8401c04001c084d0190351701082142d860304400800780642d24071600044041c0c0c0c02c0b075099070780000044d01c058100386008000c480018010b8500700c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 273501294 1250 273500044 273500069
    0x1112070507050304231009060302130e0a0501090518070510090306020a030b0102011a0a0302040908120a02030a0b0a0e13050304050301060303411e0304060c080105010f020717010902030304 83
    0x121082c045d80f8110f40703030900f2207100c942ca4070342c0140544030aa10340324140500d60045403881c0480314a4012000624030003055007204d1400e510001700401090007901006c0785498040381c0c54100502c5890506101c40f402486c580381030030200a11140b0f406040e40402003803aa0200000c3c1d56800074007032129080d01d0208203c0341c02ca00180c20b60391103903c20000c110b18100c0d400d0b92680c51104140890fa0150f400061240c00d9040846840c45100c4910a40017100c500f8003c0132982036005610451405600b0040d44030501d0800800544030310551a40680c94004203040885802c050104281306030101d03894541d40d200030900799141d55005801240c0c40030702d2440d900c000c1c2c10328040f50b0012000801c2030344050012071414190070880c3c5a18900d400b0035107a180e420345184080f030090010f04040d859250078940310010700031640074103000030141000042c03c0d50040049090185164001e09066810240d284130504803070082000c103507488107441005a201480280041d00b901120f00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 273502544 1250 273501294 273501329
    0xc090302210319030c020d050a092c040506040c08010204141e1905010917061305031303111311031909020a0f17030703020d05090d060510140102011112070507050304 73
    0x6e410060203410002c1441001c000040d6056400400b40c000c0d161000c07001400380380d880070303a0401091031880c0380c0b03174030a60b0780180001e0040c000781c0140b140b8030a0300302c8000e55840da807000d400e0f03015511030640d8164920210034014544041c401e500c9108440c81c50182c030010000080085400c60090000d4010040c0c0602c0f036075a00c50800740103441c0a00c01d03490490003500d0100d94a5100412520444640102c1c00041150a200300c445107440115a244d07129100c5c1000d101c240703083c01c0d215102e14803806105100220701d008603001041c03031480380350440c0d4409107454000540610300500c5035580341e45280040c0d68903405400035011105816100ea810610f20030100502c1840a50480d817050041d48006070f80043c0b483c0803100c8900e082a114000302c40410306115003020000c0c4814100300c00c1088014020815100712030903c07102ea50f0715002c44005a080f5001018441a0b02c001044207801c610007203003005421000a241407490021a42c0b00c040c1550002e800c00445102820f001c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 273503794 1250 273502544 273502547
    0xf0312031608010f030201050c1c02010c030b01030902030a0b090703060e0307050f07080604080f04090507230f0412030e1e0f0913030f050408010c080a0c090302210319030c 76
    0x2005400410740c20101d00079410143d88100c9025588802070401c2400103130303040a109d051100300142e0161145c051044281d00c0c030064040c10a070b960b0480000c0c609120302e407a9600c81e000304000701d078000e0098605d0b1201a11042c3c585240180900018419050000b000400c1d0744540c0000101c0000599180c80141c5000b9003018440000d4003490341c0b22107403d2210942c00320b815134020360b00461040c3e6640a00f40340610601503a80208650792800003001305090304440005140c0d80440d00350707005007840043c040c41d81e01038001042d4180c0d00070302c414884072502211aa1046003c0d007010501000c00b840020b61110300a004401e600c20400c040700300301c2c01c142070361820f0b4280031281c1c0c20003031600e03060558070501c038001e0180800420341c41950b01d4078052001c0300c1c09009918020700182510b00c0c0b0140520405035140308025240c0860010224803440f0a0010380b03078003d050f00d02455503954005028020b086c4194081d000c20445200390250f45a807903100002c46072000704000c91411130 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 273505044 1250 273503794 273503821
    0x180b04030b1509040804060503150a0308090901060315050103020d110715050a09030503061003090510021b0705060909100905010f05030f0d050a140f0c150a02040b0304030e0f031203 80
    0xc0250003066004140400140c40d04151007d813101e52420945907a05c20080280741c44191054680024502d0404000d008858000340388605003038a1000260360380d040d04a0485041c038501840c02c4038424402d2010303600c00d4005000c061940240800d17842084d428500d410352050340110b40400d8901c003200c002e11410300442d0740c44404200c08102c04082d6803005040c500c0300400061042d00e900301c00c90540b44c060b501140c816508031048504501c50b03203180d00000d5010300480b00f48800785012541c446a0002152000d50f10040c20040c180b003801018002d0403140a001e01c041c10741600e801050000c160b10615008000318a00c2d500c03e03e10305003c0c0b5003004280c41c141c000035040305030320110700c0ba0841d046440150300391a10300c180783e800b4111000c05000d06200078403c030000241c842c406820000703228070044001d0034414420744996036100c0c22440350744100802e9400500004011a00803d000c410f00074014180180c01040e03100082c0c00d0403041030340648450004418440740e25801f1f507 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 273506294 1250 273505044 273505081
    0x207230d08090c010509120a0501050604060f120f23030403020a12020a0302060901120f2a0804060b010903051c02060a02040305030313111801140a0312180b04030b 72
    0x30940002c0c10080d40c41a110710820a155060002c005000c0c1a10780310305003588981c2d62158241d8103c4000361500c2400b0b00f10980c1c2c070324411420160040782d2400b440201c9070444201c2550880031043c640d803445050054a08280d5030b80c007100c0d4100d2848015559001c42c020340a801071582d490542c41008007070079050300545030300300c4030750100343c01a103230022082d0603203404544c50b0b40c0b41c00c02680100c4041103d10061002d0707505256204c80344a07002c0d00070100303c0178103245c5410701040901600c0c0c40c1d80304d031540c0080040d021802060201d041503004602034081072512200440c1c498580c60320b07003850202e05064010000400c460000e906118407030700030b454601c055145c50700c2e40d140d0903920f01020b071441204880755589032041007100285641d2705c4c1d0700540544003141c0f0501842984001c01d106e81290711103d4215150720f403034200350b07100c00e403035200c407041981f07401d29030088407008072942040c00344140c401004205880d60001a000440c8078204000e294a0a854007131003072281d15 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 273507544 1250 273506294 273506297
    0x11706010b031504090c09020f07060509010b03120a02010603020a060804050c010f0f080a0b1c0501060e0402060a03181b330804061e050106020d081b07060207230d 72
    0xa100f4056003d00c0d07000c45075030000c1c0484010030083c00508060b0448101c9a0004894603c0090542007000118001d070000307a000744800c00144d580c10313000900341c501c2c400195a154010303412046154100340080d00c0c00d4085413000040e19074681c2d02141105600360002d0b00407030801400c10081003001c00010744030a17804e2070007140654580001504142000b0380301001d00002c03000161601500b5403184022080c001d102001481018070074140c0d05014001c2610194204100420740b075402c519264010355000d0000e40c43e10480710383c100c004011101400328041001d00b120804140c100040c2c911000b61320345060074661500360398810040319a90301d003d07030300d0804000c0b00c000000c2c4040c5c1032080015041c20303040c83d6142c0c64241d00811020540c444620f01840300404141ca1503070086050300c402d50210b403217140840c0020303102904100e5400440401070340c0c40e02d01082100e4003920a442c882c010150504a107a139824032440c018907900d0046c0307a40c240b651404003c0c06c00001d600304443d07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 273508794 1250 273507544 273507547
    0xe0a0201050d021e040f080d0c0209060f03011e020d0b0a1a031008030c06074a030109060911060720060f03130606141c03020a0b011706010b 62
    0x1550019105019101010258641c00724070025004c82200c11203503210301c0b508046989544541d500f88600d8024002c8030700e0742c171410400c0f942483c05009120071541d00100640c509659003010007520441c01c3c4031158055484200c200c5d18444680c4800452001c00340000da2940401041c2804841c1c1d502103403031003414840010002c019800340350700142c00704c801303040380d83c0d603540c00c00c00070881401d600602c110701c00000c50304108480452420f000780000e540701403005086400980c2a14441100c4001000303401807a0081041d045030000107400e1400030106403b018000004c0c2150078141c0c040c3e480b2500e4041c00010000320480c406054242201c0081c24041140c039801c4200804100e00800c040403008940f813560740e403000b600c00200f0110125039803807600340c13018030f404400048125406401c160000c03801b120344101c0c001c83e420700641500d511030500c08818803203503240001030b030542c0a000311180c040380c90006070341e01a00da910040140c100b1182c61580c58140141e0020000500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 273510044 1250 273508794 273508813
    0xf03030e100902090c1e0a03110328050103080d1a130209040c0206040c06080601020309042414010f18030501090507080c03060714210a0e010e060601020a0b130602030a050a0e 77
    0x19100200041c0c046e0b41911261a50176041c4140c00500801d01002c08440020040010255685002440b240c041240d4854041003101d4001c059440030300000700204010b20010f0a105090390000140300b040c03192040700401540041410760f0511649036451540004000c14681401d01401082244c14801800030f4502a190b4010901d100d00a410801c09038101180c8668800c01c01d0350030076400100b0412808509040245082e07034100001c079081d2100202c00640c0c0c03000d034081040202010703100c1c440310003410032080310f010f418010200300034008034402101048003440350a85c8030f842a4014030b140c6040040701440d010038400e44a110f40c0c004000c210082c1d41c40326843c0d1200205038442078840c51000071082c45202a1300c4000d201c121040c3c100700f00b848454022079001090302c0300801000e100304c03020644a140c103c0da1079025a12140320840096400c1807078940c400c0300e443c907144501c4c000c1d80d604021f0340c1c01681c1e84a4000d496009000c07e01d4040c1c40340038802c50220005003000703003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 273511294 1250 273510044 273510067
    0x4140a0308160521071e0b1503160b07021810030201050c010f0c030614010206010b180a03050d0804031b02030a060b010e030601030c0603060806130f03030e100902090c 74
    0xc035211040c00a9002c6150b00400c0203004c00c0b01c5468801890354040711120411280c42183d0031081041e200e5100000e1004a402e207802d414031200c90b0460b09610842d684c0000102c4541907444000307416120340b15004a11880c00c01d03008014111440f881e075564071150041100c02081c98004007141e0b01d0f09014045a1455221844101c03070b030a00b4250340b2001400c20392030041010008070030301942013003555886e0542c16070042d026a56025040c00ca0480300400490360388809000740a078400c010420b9165462014002c001c5007440144550310040e00d07903442c035091481045d0003c002c10206403d2000b007540040b405155550100005031808a07150002aa140c0443c48003501e1035a90350800a210b900c0382d9404400f10310040c0858540c2d5a6034070300404c42a40903c1002c1c0001d24000c80840c4884021803132a0050050f0118001400c1c59929a078510b109044801c4051580d01c0500f040e041509214481a2001c000070006000f12280140a01000010040d0201000822170318103100c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 273512544 1250 273511294 273511297
    0xc061006170c09090405060402030d0f08061c0c0e06031c0c02010e040b040207080d050c0c0703030e0102010f05071e0f02031218030c0f0c0405010e061009090606020304140a0308 78
    0x1092004400341e2901c4100032040380b4402c00c607186400014481c1088240f000c0040e545006501c2a03088480359105500110703444140204c07508001140030000c90200d15203a0755004040407400104d0220031401d40d80d01e600d1b0205907010502c1c45441204022030340c07606100a031105282c106002c25020b1040310020a42401c00100a0602032807001c40c1001d51525444482e0005c4003400031540c038003550910902603006180d10291041c02d140005034006141002e0f6601445000300070302c01141181da05450f1f0602c0f034017580341190b503114111505002e581c0941c80c0580003c1d00c070710503c082d81d83d03c51410303586196502c03014046001805200d580c0c9c00000c444884421004203202030300d8502c00c540c803071050310b201e41d045844049024064658041494002c800f0103c0880703008805600034842030310070912550b4030301d0b40002c000486905040c1031500418900c0e01d030100380309440b140c0b02c00455015400c03001c0180c0c030118003446940b11408d581c0f00044c40c1110b00003003842c030310394420006 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 273513794 1250 273512544 273512567
    0xa0503040b070905190e01090b0307210501020d060303020d03151509050306010b1210150507080c0d080702010609050c0a0507020d080703080609011d0a020c0717030c061006 76
    0x3005801c800140d0741c0380700d108244080e14006082d207581c2109a00012900041d40c000c020070400000c00001e00348007244503501c81000094050208241b52601d12801c0c4103040e15010181070200c0c1c09a00020400c0c40249240803441d80006200e60035810000d161440f82c113614010b1601d8103100641c0c80d0b058807240421900f03030401501c0252003200040719a0b0304a644032030340521401c400811841c4641c0d0150101d0f0b10700f40e141e010b455481603543c101c40d140034403406075404140051b41541074400c5e030060140340d00940740103141201040d100b0b8a0984850351000c00100070105100045e079080c000e02000b0060b0b280300340443d003055072a6141c988a030340619014004002811011501d9003900312107000c1d00300c07070507503201c61441c200a840840110b913000d1007000c2d11400410608072283e130b0040703a91081c421100c0103650705140c3e04003c4d801100398031072a1041620015180040c0c500140000100601864030b5900a200117460280c024009800c1c40407925000c0c03200720b80c1321040000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 273515044 1250 273513794 273513803
    0xc230303070317060112050a0f0b270703060305030a0806030c01030204030506060d061e05041b080d030f02091c1110020d120b150a1d220e0d12050108030a050304 71
    0x40d2a2203010050314a840c0045541004031f06040420007103914581c003542c0c0d140b0941800b032006071020400c0140c0c1100d40d1421080304088800199030004845c0349550f442040d17410001104c68484d100c103841c42d00702c810040b000400203020046581024440312802200a0a040d41001c2c2540e0b581c0c0d46414000f007045015a221044001c248510358000c1901103509a42c80b64003030a80d840e030b00020308002c40d800d42d5040d4102d81492800880c28881e101100d20303500103008a02941c1d20110040c0c1071842c0c0016140f60203000f86c005599a02030f0b500307410060108001d0107143d261405083c100b04055a4500c240840300142480340c0d0041009181c0c003102d85451400592403d10090041500991103600310307100c015544010038a1600910514042c2d880350310750303031903170107003030034441c4034880340344c0e401c020307018044030201c00150380280c18516108000318501d4211a1001c3c900100c004e9620001000c840060000044030306c0303144d026001c1351014518000c0001c40c003401600c000b074001031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 273516294 1250 273515044 273515087
    0x9100503100b03090a020a0609031a01140409050106030c06020a0b090304080d0f0507062d150501050a030608121e1207121d060106020709060510110a0c2303030703 72
    0x1000b007031085c00403000155008010008003916400d004040141c14081101c02c3c40c0342e0181e500c1c000c000083c9071412078601e20b00e041e071401c0060302031101600c00c0e04021101036480300804800507142d17002c05400360025500800118146041440064074060700386131407600100403e104424020a48000e00c0050303061420317040324848022107180c0308105003d800e0328903201450048111000c60080301c2d8400c1c03030400f801e0743c5101c2041000c5809408005015000380c803030810555000b48013400021049080000d409035440322500c2c10041da401d100e400480d00007039a111900003190144c41e01e07000c0e411201e824280785940b0380540200c0681104184600d01425400070001a0446e036200f6152001d42c1c580c3c1f501828005a8980c1b003802801c015002e08400401d0316000740c4940c0c0121940141140c0041c0c1050f841600d48004181d40303442e883c010800000081781e180e5034082e008003014103821003181c0000c2820410f1807140302a5600c642c00421280000c0382c0d001412409044203603c100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 273517544 1250 273516294 273516301
    0x7020d0605040c0e01090b01080604020a1d010c051e1203040b010b09060f1204030306080109030e1509090106020d020613112b0c0e090304030209150310060b09100503100b03 76
    0x4009000644d02a14400405900210302890030b03030054900e40c0c00a0700e50044940f02d110812041c1d01561068800080000030b040440d2150000081c104010604181c0d100b9a1640c07200c5080403c0c0c02890603401c444100c4604d40030108201015602c080ca03400305055003000d603606000e45006101d410303451040841d072511540c0c2d8042c11a000494002040740c1c0d070710b801c0d103000c0741072180c1110f0a901091801a00049040041c05400003007603256031103803800906001003020903848a454038011000600881c80039440b0014010701814443d0010040c00c00180c8000b490600000c00311000900b443d008400040c0103914880c5041504503071420340300d401c014468965000c2e65016540007903250a05409100d8020f40070707000d59411a030b071620319907540c9420a40c1c82c8598030000750048000342c0002c0d500d0800c1c40740003240340c00c0142607810404441240409480a90700092008070000512181c03d01e80001002010a034a003081d50451419405130f038014085ca2045905041c1d000000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 273518794 1250 273517544 273517553
    0x21e010e1f06090f050f0901060810021315181512020c0f0102130801060503010e06070804050a0b040c0905060a050109060c0f1a071403100311060d09050c03070b07020d060504 77
    0x300a043c0301078081250300364801011024140030303514448200c40000c0801d001d004103001e1003041d1901b8000602031211200c040720001e5000c641820114515a000860101c80c0c099800c0d680e00c0240d0341c2c681000203040c07101001210154452001c0c803407003039041102c0340d421014203072180391080d500507103d4140ca2038450801c01d001410703111a52002031801c1103502d0303802c450800d645002c2c008001c09038850007814221a540c0d40c0490090b03004c5400a510b49200d070b00314590182c40741e419241009046c0d03a4103400c844054600b01e5100d00550030500408015201d51580004103d8020f4002807030800081c0c40c00c1603901031001000440740304035007440f0161081c00703901e9510001000080c00c00340005e112800c01130b2078504c00202c016018149e51560700c01564090b80051007c003952500d55507458060140032000c4a4000720b091000398603503007143c030507051490701130740c040c00c3d610003104205800c0030360359040151850001c4c004200540c5911901c0c00300c9550015000490b5206c6090 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 273520044 1250 273518794 273518801
    0xc0907050304080715060f050409081206031c0e01080f07080613060b1603020f150f06120d0305070f0207061e09051203040302040b0904050c09040809060406021e010e1f 74
    0x14185090318005c912083d0000d50044086503100b01d207814065413034500304001d540c038075080548000d1062003449000352a0b0030301141c001000400305c60080079103c0391586078010700c41200011600401e400e040c0c81d60013840f03c581c494030204805034113180ca98005040c2003805000e5501030103403922002050840c0358010700107807801c606031a840340c1045079410409121741204030014090144000c1c03001c9070004452400d0054a05240301ca547d139a24104040000284030b0b03644800384002b6400091414001880c001941342e4002c81c8625101d0400344c921b4060703460f50011076000d0002000456480400850300901d0407415041c0d401c0359040840710240240c00c820340c8010140d1402010490010040c0100d910a482c18010081c0038410480042000c03038000d004c94201801d04000d42c640400009d60091040303841c2c0303003468405d501281c25a00070f0f800160142c0e1002a1300400c19590f80410804030034503800030700104d44c8980401d03444545510228400145403402d101c3c88035850381 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 273521294 1250 273520044 273520057
    0xb06040515030613020c03040b0d060b16141207080706090b010f030605070e1c0c09060f2603041505090315060906010e0109150c0206030a0212090c090705030408 71
    0x40c0030340c0a003104858041d680d5407050f42c080303100f03814030150028001803a0095a0702036040801071400e040c6040c011445552108080b88901c5650311b10100e040800f290140140d6511904040a98026882c1244002e12454882c1d04254008280c0b501f680d007248044510315a48a0002500c0308494540f43c0050209c00e00f00400314022076001003001040f0b007616600300ca0203a0000c0c446034507204001d07514601e0304210702e50011a40307000c1030400c182d5400101300c0c1d188101054500c407642c4842c19822107449800c0310004101e50078041101842c076401100c5ca500054002506260074000c1d000d559115510844c411a400c0c68120341c00280a0015074035150710141c1616996602ca10442141141c2129801d20440703208022504035481100310b1138200c801030311200509030170110605a41c0d8028801c0e0403c01074854052001070711900f0141d070255400f030902603150403102c1d002100c0001c0042010740341d0b911090700d6441d5a500d48208035004841d604019540b5202e90400300c7c401d20821 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 273522544 1250 273521294 273521299
    0x10f0203040b090706090e01030f1b23190504090c0e161e021002030912040b0405011b05060a0203181b090705041802090f0306010902030a060b0a0c060b060405 70
    0xc410071080c400280e500074420301c040400d40d8040c1e500c425003900c80f8500c2d8010708500d480280010301c00252040b00f455130340c601900801458900c900c209000340085a000700c400b9000c600034030045480d0407801c0702c130304140444484d5203032a40644501040c41c15441881c0c85181c845000300107100080101c5005405140c510b84680d04e0406074030050085a0021100091104004c040000e0703c40401c007000f11010f0342c080e200c0400031741011b10182d04054206e00c410f0203181c003064415043e00009100078201c4540041c0c8951409001400d0040604111030601410741c000c800040c034003080ca1a48010070460060b103a4590340c5a2610881c180801c40754284164064891110101000d51620200c1103902c407403182d8400a01315124040c80c813030b600100603c10101d0b1003495458000d0989104054001c0241641c2080081c5c51f200c002c0e03008504450340082842420303429030107441c01501c00b100708a85005803111006110301401c41024250079a01c041020320b99881c0b41c00c480060600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 273523794 1250 273522544 273522547
    0xc12140703030911060901051606151d010b07050a030f050d061202360415150e090a0305030f07030e010203010807170703020a1502011104060c06150e0606070203010f02 74
    0x354600600241240302c02038440941c500b10048132460b2110440c0d04d2010706035140c0d0f081400c40d1280842c410b0108004035500307505d40b050101e000f9528032036000102250000d0450500c11030310800402881038220000404080101c2004180005119038203140d01d49003501d10106040000c035034074003409200740400c074240040040c031841000004100a070080b2030545031001d0040b03106000c0040994580b0130500c09400188200d1103003116035503c10f0082e50340200c3d402040300d0502c00c0303800e0406031000b03182001c4c0c401d00c24070704c2030480036601050000c01804001020f480141080c0401440a140c10180c1c20009400901c207803c40b040040c0d115009640702d58441c010b480c0c0f80e6010b401148218804410741542540c000100f000449130003800b0310039000d0801110603070085851405009564a0744812200c034990500100002c1c230140c0e950829000951410301c0c196284202e00c800c480c829550144401c560002c0c105800072012a040c580c0c0d10220f10102c0e014003190101030007100d10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 273525044 1250 273523794 273523807
    0x80402010c11090a06030b090d2f0d05190206010b04090b0f0d061a012307031b060b0901080607170912031f0e07020c0112021204230d0c1214 62
    0x26600300b0701c142c0380310384031100303299660480c1c06035288102c41c80c030400502915141c11210302d4180440000300401c0a0011522515450f01d51521401400690003304002000381030341c0c4000c4000a5603414a101611655242410a01950040e03025240c0c0a0b40c1e42c411014003591001074048041d400a06020500d071600d040440080c41001203101d41c40b0b04c84500c1d60543d42c030440c10880c8906505e0b460300021a18120070000035004500100c0034406000204504070082d1342004900c41e1040c1d002040c49aa00000c0c03111800d010f9214442c4c60b802481408140c070740084500650b0488169402e1055071390781c03c0c85203400d410b5000b00d5090540042840ba00800c0c18080341550b03042145009002030b50f401881c1ca00d101d003282c1d0f10006811891500e001984103042d0302d031081d000000003508041150008201c80c075000e40d422665400152100404800680104000201c0c204050454034031031090161080d400348100602c004034000581a4250080000191750180d040500d82c0350705 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 273526294 1250 273525044 273525061
    0xa03020319060b040b06040308031e0c09040c03050c07110a0b18040608070b030a0504060213060e030c0402041d0c040b2d0406050a030b031e1516080402010c1109 71
    0x40007204142da086041240c81c510500300b40c060300c0d15800d8003510310313450545183c17200d144541010b00780c031044002520001a0780241100c034540174004100c4042c4d5a40c064000f000102da41454042040c03600b40700030000c9900141080e22a96500011140380c011840400a10409010f03084046070b698045200b0450708030490b0b05805082041d80d041120649961803595540d45034495111414070400021700714000039081607801c00d03c0b40c0350150405000d6028108584580e802050024903c10341e400c07420b1500700104050308500327a400314645820180e480506d80c2a10000c8046d00c01c0000c007184420580c1d5089400a104000324251900200341c60400c41c80380c01581d110028031414540030300407225500301ca007101c0c1207884461400840b84010742c040c043c0e000703900d43c0c0350040c04035002c42110403c400004528880380a014038210409458162000c06840114203c03003039040c2c00310b1150030481d4540c015409081100f00710b0f95500d004005c4000726004560800841000d010540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 273527544 1250 273526294 273526333
    0x1e040f1119110c03070315020903150915060f0402180d050a1a010806012601050a0b13060308090906190f090e010e0a080c01090501090f0b010e01030b040b060a030203 73
    0x10031259a151280349118640b9540d80303802c0280e0903851741001c00c00b0400940007000c210b42d01150b800000d07080039a040d00007428150300d207051540080c0c10303c040104400c1c062040c00008492403050080c50308100c000300d00c815060302038003402030303500145a000124040401456603500102091203020151805540307a1b95140021250714880030304601c41d0b03040c00741610703051380c0e05840201305982c81c0541c403200411103041c01c40d90b0031130510001540301400780209446002440000b080d40801c01c414003069071111629030301e2840c80c105c0d0a00020f003d02c0201c030703862401100d06803000d4a600c40010301c2005400c4050880828201c40007400c403110300440ca04595501074100090410680014241d034410309200c44540c0242030004000383d8108080d00b8002088000003c0100d520303034440d800c4600c54202600c5620401401c0410400c100040501500d501060300056500d1507541141840000e00020030741c2e1050400903009483d00c2d103180b80110340040488201090804408188 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 273528794 1250 273527544 273527587
    0x403120c03060302060c0a030305240d030903050303090106060806030c0105031f05091509060406120b0a110c010207050706051303080904090b0a0c112e0f0606050a0306051e040f11 79
    0x42780c14440025400b860100188489840548100c0405584441008a1000c00c12070071414000d6560001c0086a000c201452040d901c00000003401401c007403014000311b00c002c0849200340d20140081c030301030341e0100603a6002900c14024002e0340b2020381042142c2049a0003040c6c216101d541004280c03a404502203c80b010190788502d016100e404c184002c5d0740583c0145001016a58005c40008415600490b031050480400140c0c01a020545103400d1b4032540b001c500c0390b9000724541081c01000d01901c2d00811190800e80c0c9004038034000c21070703558900d200280c01c0400204101d101747d103458100001095001c4200d410901e09011030400910358151218001140d40c1d070b2590b00c3c0c2100180c1e10034240b1007021070101d00ca1141c224040110040e040c080200e030f8a907100841051024005d07000500707040d4888685403074400c90004e040740c485500082c45840300d1507038240c40310040b4500540c114000e4401146c008030450b091801b401c01e03000d04038510703500020544100744180a03007000707 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 273530044 1250 273528794 273528797
    0x3060c080f06010e090403120912090e181203040311120a1205041110030b0301110712020d0813140a06050105040608120f0c070e0702100b030102030403120c03060302060c0a03 77
    0x8075407264401101c0c0c280400143c1d43d0070a500c1c0000c200401d01840515240c50b10020700420b40e4a4260b0f10b1441000940e11030f4004034017507000922203000d0081802d548006042044007403411417031141c5640c0c1903a020421040b6000201050a2510860000305072291480454403022942840e41209604c0b1f04001000036002c001211300010700e41c002c1c40d024035003186ca41a60080c40030104010842400000d800345941d420007040c00303807002e000d0080b8600d1850300e00707501e8088908240c01c1503e9060440e40454100c540c20820b00c98010f00681c1c0c0022011591040d003a42501d8060105120401d0340711107803081d01e0010040050b9a00142d0503070303400703403014030041e03648241c42541d520a203414180d6910091011008402c1504060071070814002c0413113004d590341e12407265404009448510050b085840380003404041030007140c00a00040d8021480c500d083d0f28021300c0480c4112005c1d154036207945003c504c0c24400d401610103503400510042c0d0f1502d5480815aa81e091000d0480 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 273531294 1250 273530044 273530071
    0x9030215010b041502010e0a06020f160c03020f0901030512090402070501050a0f060909020f06090a03080705010902030c0d080a0c11040e25030201170c0f07050604061b090902090a03060c08 83
    0x81c03c0ca407040c01f0b503010345902c182c010304020360345a89041c003a401965900e8042d5400340000701c0c4c0540c1400194520501410018448506600603c12910381812980c0e0181c1da51038010000528000307864030209101240c85511031040e00c00080c061b11403008090413642c2003d05124045009a0244607041c003025000c016842d07584802809560070f20380c000c1d601c0159400c48400a042802c0101114203005112005e03150b12a40c501c00240c10401c0c003925540e544890140c00c6081c00c1050045840e41140c10905156055440302c0440c42a0f080c03035801c001c500058201046540180888680001041401000e4010f0b0102e9610710325056280342c8000c50340c84042c171801c12424143d040d641c0603940e000000303021608800780d00e1070180040c00040010040032034990640f40240003002d208001a040074145410200c081d81e6007240e06c0e01c2c00e1000719000540640c1c010042c202180c0395842c026031110b49860000e0320002d4a41c1c805030505e0304020358514400d50042d00b0030b104404407000b81 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 273532544 1250 273531294 273531329
    0x414010f140d02090a0f1d0c09060403030507050f0706020312160e22020d02040e0601090503031c1d0d09090c140c1f06060e0603061309030215010b04 66
    0x119400c400503035868103140300c1040302c0c000b02a050b40081c40d41c10805001e02c2c40e030781e0380d900152180e003070300354070580c10741c20a4502d485602c100540c485802090050001707052883d036800140c07040c4a136101c02014403030700050400403c28240906000450307148140c648040d03544001075184d500c208407982948210000050402d010120241007200e400d07550664a2a8000140003850840d40240e1f900180488600781000f5a0f60005246002c1541c50160300da80c81d00700541448140030305883d05000b11600c0504c242d0700d0000540d42d00d01c46520892100b000d0640141008002103034a40207104140e42c0c80c0e5840b07905c0000d0410302d0002035964911425038810260f0225050600004001120000d102105000341406000d80c60b8401003940c4540e181c44480141da980004003071500661100400c02c4906e0300300261082c0c0342003c0ea5454903510701080001c4080880350440407600380d0b1a0340c1c11092520800101c1a1400e2104204a01d0b50312aa041c03841c58006110754081e40d11901400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 273533794 1250 273532544 273532547
    0x8010503120705070b0a0c060c0207061b02010804030302030c070c030605060a0f06020709022a0f070b070804032d060504020a050f011d1f0e030d090510030c050f0414010f 75
    0x1242c1c0031980140140a500f81801c03203c141c3c030350001c134030321003040900b118482c00305009200f41101041c0039002007114502d082c401070600c4201d111400c0c4107007440061040982d030070001d090743c85507141c5801030342ca80d606a40f048440c022988090036950702250084104412030f032001d801040c1c216003840c41c107a610074141881f601503001c3c04005801202e010460a641c980107800d2024403252440c4c0f01c0da484410001c560071480d0350b2441c0c10380c040400501002e0040c0582c0001c0c2018042661402c071709a141d181091045102c001c04400501c0c0c65500200c50305e20b403401c440c07050a100c0c032403001a030f8185140030382800d540a074810303d4200400151480c0601d10b1540c040b9043e141d0b4991110090b41c030084001c0320300c1a40303402c1030341054042c0038118690140f050003070441c0c403582c4600090400745403501041c5076924051000c1e1540520403552610002c1188000514001c074400601490803280c5014401c8aa21003420126020590030700000900203108420380c1c4118040c02032010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 273535044 1250 273533794 273533797
    0x3050601051909050a08030a0917070504091a1b0405061e040e1b030103030c11011e0302070507080316080d150e071707090501260a0606120e070927030801050312 71
    0x50240114074800d82c00c2014800214002b495144070001b03541c50b00707035190007290903120701906c12a28186e0142440003200143c0d480c4036000003400e20342100104101103c21440d11031070054a10410000c10040078400f9200b030300d003503428442c0c1c01c11038449581d40c1812042c0c010a403400c01c4403070142405032556012902c1624100c98140c0e64030b500c0c94519448844090318646440c904000301002504080d018035040401442c03174a9030016606e035010300b010340c01d1540d99000b003036903600304200307484407003103881d803040c4555400c1400c43c2c0e078580409016000030019101e5848041103031781800120108000c403030b02c1c855142c544410307802d114070b01d181500d0720300d0031280e20000c5401c041051107107500c10300b0b445401038007000004440300c495500c0c020401004580092180351140c07018030015070302901140d424808600280710f891403440200d074641c541c41c02a13940095a407114400924002d07042000c60440c002103094004119003001007180c1c1d400d0040502034441e000b0800040c031107040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 273536294 1250 273535044 273535057
    0x1206060f170d1d01120b03120310060323180a05030a0807030207032109080c010c0f020d05070b0a090206120f060a030c050603040222060503160b0a03050601051909050a0803 76
    0x3401e0906030044001500e1120310a01040c06940d6186c00004054404102010f20b0019540c6043e0304e030725040b4503018a0302d8a40d085041007609140100e8580c5000e84c1000034468407428070b030909940e4042c0c0040d52660070390100d44061140c40341c103005008010009094400b41c981e03c90b14035540e00343c0c0640680c03040b40002800100390441c2000d5815103900030306802c03a103208012840c0e03201d6840d20401504403064410782039550725210409507400800b01c0c2d03d6000d00d40050034074540301140180c514003d004010348138080d4207000800310056580040c5c0440c2d0f006103002e1f100d2043e881c00000e00e68007200d08403051030648001c1140e615080c0c24034000c69900c070489040803420031003803000076003001e04202c2c7c10119031007070160384c00500c0c01a80d003901021000040c40d18500b038101031402403603d0f60728001503440003040c4180044541120401d03103081c1008217075602c0d0840100c8051290a480e00710014050340c443c420b565000b403611080761003c8600d40b074032075140c11a8540303d101b6070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 273537544 1250 273536294 273536327
    0x1403060a2702030705060a0504150f0c110102120d020a081f030602070501020906040b0d0b040507080105040c170c090406080f0c2803080309010f060602071206060f170d 74
    0x10400400c56000d124505640d480c800f8080e82d19079a911000f1510a80004a4003000301d900442d09102c5c4920891170300d43c0640c124500450190300012002d0400904078501900f190300f50500c00440364000c000c070440210380d040a6907a5a01c26000301002500f212241500040031640820000e110301100c09900e20a41d01c0f805d51789520315560140252302100003103801d5502400000c0f810350b1080080c0c001092a100c000340d0b258000070981301203c4035031901030b103c0d138503001c10300c500e15620050280c10740d5000d035400251100a02c10658688400c000d41e11031440c6000200b01400c0160380240060503402d54003800a907031501d109503120307815060381c480781c0d43c0f010818002d1072401501110010ba0b184682503154010500300c90302e0301000c0e410a91301e000b400414010004400d20a140311707094010380401c6142c0c144100292143e03c03501c1150000f0f102e20007040203001b42a40b00074020031000c0d444d20720056490000c2c00c07002c180d4000700181c41c044c3d022800d20722400380e0542e0304441c015 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 273538794 1250 273537544 273537581
    0x50c1c0915140703060b040611010e030a0f021002031009050403231b0a0203030a05090a080102070c050a140901051e19080606090106090e04080c0f0a0212070602030f0702191403060a 80
    0x240709040758042740c07040c80c0390415904c48074140b00000052008205403a843d0fa1112001440381101078074010045420ba184035104008100081d03005010102c1079440c9141d000c10b10303440b242012503281c1c114044011a0f90a807107181e4490402c400018100354a240803194201030b800440b660b180d615012000c1e4141d08100401c0280034822401424802e100800000d0a55110001142260005d0b4800c4900b030642020901052030310f100350b400101503200102c60400f2244c804610305100c184222402006140414001441d440c4041100d4040150045040525240500c018404c0038403c140c03140c00303024003061040c1030241006040c0c0d50369403500040140ba040302c070f04000400502c142d42040c2c1c1070220100c1607a050000440c2642d210f8001c0c00130072800e00410803500940c0103d41050383c03081d602002040d0300401074030703190f1081d0485c0c2c41e00d0b03c8040c0003242c02c07003040c6040010510514400420f440b140745404cc00c01c030209400325210742d0b5a080c0c0b88011140b6022440280840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 273540044 1250 273538794 273538799
    0x316050312071a0408070c0b09061905270916170705070b0f06010807051608161407090c0e01082a0d0b13050c1c0915140703060b04 58
    0x11a00040c62480d209041c04402c040c03207200ca180910f501910200e1340381400045400c1402500f1420307002504c1801482c3e40744c2181c3e400050454132940241c1c03082006008001111b480c001c4050300e500022074481c0080c030301480040940c0b485004122503102d0b400420124001d801220b803800f41d140f446407235a0480e084c0800314280c948000800c91001c01030104443e4001a00da4103102c0e0051445000030035484c20480009014142e00500380400c0000c14000300e40301c03c4c055412241c03001d412401b00f558904000241040f488691140a0400045154158928040050710304200c0340141800c102540003518110780f1a045078038254001403203140401c0350080d4140c00c2100030410310a40c0b80c240c00d00804000780c9500003d00040c242c1d079584645070500e04128a07440741c0200c028100700321034508202442001c0c012002a810046140d01c1202d20402055111203142900551090040300710078091070090310803d900c0302041140c40c004110010300074051403080d9101c89200c98289070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 273541294 1250 273540044 273540073
    0xb04141003142d0606030a1203021305040c0e01020709091208071205070206010f0806041a0612070e0a0b180601050a0909051512070b0f0a11011a03160503 68
    0x28440c1c00310300054083d1000103d40e10406080070460b640c0181001d0b844458642e0005040000c000c2c503082c040c0d040003111300c0000d0307a034008520480d08a03017801a16914540c012100e102c039a90802604140360001f10245503420844034811000264201c1c1c100945075814601070310b4821100500080d1500c0505200b580205100780d171103c601d00c1c280966041d50581c00b000e590064490202681202c0d00602550900584800c05450010b0007042a0f0415684013041403040010310b1840c101010042080b0f03a8840d000420804001e4040303031503964503200e02490303481c42a580700c106149003802c0d00d6031a082492103040d4224038610400e600356030f548019581c9501c014040301c2000810000810b6820300c900c1014081d58041211a005014650a0107141c51401c001010217502c40d120400c0f9500c10748080340c034000d02407583e1648900d0000426102003a180441030041d500704401101c00500e40c006c1c94440c07800850031a0520000e844004000c00b050303000f50b42d015004644000c1040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 273542544 1250 273541294 273541313
    0x5161b110f04021621020a060b0604080d031b0e060d0f06051c1e210201270302010c211a061215030606090a1505130b04141003 56
    0x2510050440600c40d10140d001600f207a102440b40080d60b102098150180f140b910507862280c41e00c42c8601d22480700b40c1c0d2000e507448040440040003e900c0e08a46d52098a941c0700381d40042480c4070449601c8040004058013602c00452071000181c0f0340c0c192120307814400c541d5480c203030002134401890500350704d5440000e41012824003c45a458880002c1d0355103400b842c010701280715038403482e0311507030b1890010f400200d0a03400c024007041c0c4980c40e002096000741039219121003148141c2d00307141c00d0081a805040c01e440c800702e60100ca03c00d01804909207040103411513100341e0003006403a403c0042515a1700741002c010200390192001c03001d02c90800c0d401440c100718000c01c941d42045420000a0300c0340e103c50309101070401030f003041c040300448101c865581d21030308801400041ca80100841c0b09402c005160340d41f900c1e210090b80300a0404c000f0b0080103020050b0104200691080001000d0b0207030043d500c7c01285403480d5421010000c13801c0070b015620b510b0507900103130b1039a160075840 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 273543794 1250 273542544 273542573
    0x9050a0e07110706050a080c03090312040f021e010e0307030c0512030408070815010e07142508030612070f141315090c0e10030e011d0105161b 63
    0x148409410004402c00040001d200201410744d201656100700040041112002a0240c15070300000d10920010364030100c00e03101410150800402c0940e1242400f098071001c410020390044103117804455a050710b01d81d1481500c00c00e0300c403502c880044070141962481c0e0349c44080c084400a100c01d0141e4585594801960b45801045904081d180d017038807402d001c4198441c035072540c0101e42a500f00055030001c47c2c01049403003120f1865242410300074044002c0c0c00c00d801c0301c0150006003a12030284025041c188044414241000c5a2452602040310b0344252200c0b031080410341840004490f00041901c1615400c000d01800985040b040704100d60708a0341c6554045c00341d07448114401c03407034403500350f41101051522444e14504400c08003260307105c1094030100075613196004419244d02011100303c124601d03002809940540d5000c0c0100251548064115840c001040900c0015008a4091082d102030400c156000d14002e561681d828002d07292188281059100800c2203192900035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 273545044 1250 273543794 273543797
    0x8071107091b0e010203070b070302130305100501030212010b010219020607080c01050a0b0d0201051b010f0f05060901080a0b0a050415021605161409060a0e040c080d09050a0e07 78
    0x245961940503078016181075102100d0100d148108002c2c202d580907090814281082c00514030302205501e0340e041c84040109504c0078950001240b000c002280d9801c0c800075501714050380e60300ea180389580780150000f884180d2007284021f180895a007810300c83c010000c10140c0080c42c040c075040d041a06101c0c0f00c6203040e80d0102d010300441c0c0c003203080e0078000e014010790000002160318281c903600003212440c00f4045d0048529051140c0141d070048103c4458017040588000d070b00b1814120940502028466a0081810140321030204c80389500000d01594048441485503a03c5151041d9142c1c0e2b009405844030307010794041810303190310358052900140501c00c50340c000400c0e00a10410303a400344600b640001441c0d03421000f4000300b0301c00d00d40d4000031005895903940c50548003400c0d01d00143c1c4141e10a0254901041d4103946158400d8003c204d50b22225995141c90b0401c0b4040214511482500380145040703141568801c0000100b601c0c00105800b240790704208070010b520700020007110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 273546294 1250 273545044 273545053
    0xf07030305130813030312060e010909050a0210170606121b0712111506030303220c030b100b04051302071a160e031f0207030203130e0421080711 64
    0x6010603400f800511212803c0c80f14540201d25514006040d00b984810815016241201c180504500860600c4c1110898140850119018101607007090610b4000942c04095088a5054039800001d042c50030b00c2c0100140b459a0381e107005000c0b843c82000003910344460503500280d00c4182d00700e569140d15012105003418044c00d0b54075012100e41d50f900340f801007070103402c014150300c4041006507400040350044002a090a6011a42d07030300020f081c0c00402040140703032148819080560210203030308003c100801c250b8a051004c00c4000590356800c810b6420a03011074a0400c0343c00310b40843e00e000c2d0260400c480301424000094200080845803552402c44032a00104010300301c034015072038000e201c0386030480858060440e0844c000454045d401c00c02101902c001b020300f001f0070b074403209000580c0d100d401e864102c1c110301c610304001403000039121021900280c8890201d03c1035110341030015400007541e00864a02d11131005141c0092071101c0041e42d01d51080010b416507443d401d003201d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 273547544 1250 273546294 273546331
    0x4030c2d080312071707120f050a0c020f0601080606040203100b07050d1803110603090f070b040807050f0f040b01030b04181a040c06030e10021b060c0f07030305 71
    0xc0020500c5511460701d903403000c9a80011003c90a000ca03401584a0826114404041980780e1040700300903d00f0b0180030166000095144290b003100910980b00b403400c00141c03402940f244001c0c441844800010f204200841194400000d4814103a40d00c0e040145120f6640300c00b00400380d40020171213141003007440c200291401d95880503001040c0306401038403488002c280010586840343c07413840000c0b54141d0042002c10030702d6660910f800c200f0354050740d40e580e9040c035641c0341c41e500d00c040c80d00e94460a1000141d13609031a002d00155250002900d00b80b694400820591007220350940d5800400614004407920303080d8000030b104413042c1004211074201400240403102c110074403503851040e0025042c00c00003603909404c4e4480c0c4148501c41070782884d4440e080002e10b03a008035001d140e40c4141640c800181000752049030b402208083d5941c02e98848c0310140560501c1c1000342c98400c0f0804140d45101a4040e40d03500d4800301401da00b004160384086002d40f070040c107030040010150100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 273548794 1250 273547544 273547619
    0x807092c0702010b01120c0c060e032101031704060905040c1101061214030307080718050a060f020606010c0203030f0d1409030a020601080109030207030f1407030302160b04030c 78
    0x426100710516000081c2e8601ca030f200240540b01c441a80710105480c06040d07200d03941c0c202c031441c1e1886801c0700002510f00c1d07001c60702d00d01c1d52107040c2c401e0807400301c4400100011840119040e040e40e2003240c90b841815030040b4420454000c601540d0701080a624083c4000e06040e403080c8010091840c0c0206000100452242103529030b401500c2204111401c10042c40550900c401100010000035031452810000080c01c848000d0704600030000c40000010039884030252400c05800010203100b00305640720070190403580c00c2140c0ca8054001c3c070707000490f070b90b00400b800c504254018024520340031a980d0fa0b44d00e1940300c0c0480c1211503596800042e0700201307010703940344140411001075580da2080c4002900d0305030164400c40403681080131160000303a0101b5488112503101452025020140c078000e00030082034120031202d4855038000109065001880c02d0318030000e602d0030052903466203d604198400d41c003000d0700c5004400000c00c0030f03000004000c44064000b10000c281c0c0c0480000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 273550044 1250 273548794 273548879
    0x3060108060d021f03020c0c06041404090c080111090414090c151b15090d2307050307061a0f01050421020607060e010f06051f020102090a0f030c06080709 68
    0x4d0800001d0f80442c50a214400402a202040f1812a55681020700c2e042400c0c00b56520980c00500440e00ca5036034004201100342c00802074610034001380407214410f0380044168001000062241c0d0416a8074404a074022b90610702400074500546489003840d028041e84d250881211418454200913000811034148030480c000344c150300281a1600f071600350800340c0000641440c1150704081c100c0394406412040d0518400250038002e01c644100c40c0d442c20342402000000f03082070100240b07a504000e00c91b0b0050446442c0801806282c0214038140610f50000c080400c1c0801c00c2007205206100500c4004c08221000020205007901c480c0d0114280c2d4002c03603400ca4016881c0c1840c0340c80c5000a01400490742d1103a0010040706150000250031140080c0341d5084400c1c1d01d543d003044152007901201e01208003d810603400c2a61504c1c154602c401d40d20081d1161007150300f011559038428001a030103809151f03600c0003402c1c20281003100110300000b4030189991507a28013506c0504054 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 273551294 1250 273550044 273550099
    0x10c171608091e07090f06080a0f06020702060f13092706060503030c03070605010605030403300501140310020a050a2a120305070e090c13080102042903060108060d02 73
    0xc1c041c0c000c092501c0c4942c0184e83c0c01030744a14050741047c2041c440810002040c031003141c3c110690704d003040c0c50b41c2060f031b001f032040e500041d400400c00540c64181c000d4150041c26188046134401807410790398506803049542c40070715980010020f4032005240403280605246c42c6000c0d0000080e50703a076a20000e4035691140c140c2141c590408141e00c000c0c00030ba032042500400300c40c00e040d0314510349035500400d01c6103107072842d140032601d80e03503032040c1140c07560392040008014440812039542c54400101046048151040c401e01ca580c0540060520314000e89091910390346170542400101c10382540c2418800c2c50b0313103001c50303031030102e4491100303882058510803170040300c5250003d1050400141070354802046042803107900010524551504e407100c0b98070140400b4215200d505418160400070200e0b4003210003903001003400700c0e2200000c16107102d03a0358810f00c13824000215010707110090004441190220b80300d40c0c00544d1900b410040c101c078103072004055607400b9149800d020034441404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 273552544 1250 273551294 273551353
    0xb12060108010e06090d0e010c03110f01020d0b040902130902060d0f020403021002060712050c0403050f070503160810090204090f0309050a09141801110309010c17160809 75
    0x2c3d90381c0b08800100707000391078000c041e0801428104021b07601c090301000e03180700903504010204041d0024548200a010124680304c0140c401101c40e08900318040e41105e5040d400507498404240302d2031a10380714a203007456000d081c9409070b0301000f9460700100f0044006031303005442044552030b2140c15114200b03101c4031544005842c2c0e8150b00600c02c05480100a28055501c0101400032054104038112110b001654000c03407580c2d00c403094003903613000307640c0024103511543c01c1c1504810408a544415980103a0807242a0440c1008003c1d2050503813144881c01e4005503140c0b00300e8682c03600460800c0f80040c0000c24050030703d81d141c0c0004902240150005003030018140102d10305180a8401429001420700807015481c0c186281845c0c064040b0b01b05d80c07240c1c1d00c001041c0a00b900100c800b0b01d40024a19120310b0b092030054042d20082c03122000040010180c590032164402015003e03000787c0020014210360700328251420b24002d00510302c03a1052f6402d041c40c91082d0200500c0e0281b20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 273553794 1250 273552544 273552551
    0xe120304121b05010305040209150103060f08030409050f060a030b06010207120605040201390f05010608100506040618090201030e1911030309010807080c040902030f061305010f06030b1206010801 86
    0x10310303a03000c082c9070740040e410941058140720259582800306c1c0d402c0b0744a940001c4400d040c03c0016001841203a000250b41c0b48c2d901c100060340c1c10080081c004480144005210a40e81c102401c43c00031401c0f02d41c194000c510017024404200300c03d00850b8450010300442c2c0c0140c2d181d83c285d401c021807010701290b801d80c039681040110750380420103010400c42c0c12103100e03107a001e000d882c101d00400510500e10100300451441e061201d02500c00303860315003000c02080620344903014641c403218100e03c0d000c2914188800301d10181442d03c03504088803040c040e1150341d50000a400006003505141c26410140c031b9015851400006004e6249a80c000c46030b07410100d0312500d00050f0420028450701d00c0303900284106241a60000b40007540300c0340750315104c1702d23076929110740368014043e5030818080f036840403040003e2104880001d500a4500b214040c07440032016028400340c800074000c46a1041c040e100c00c000701c074001d4015054210b0003c00740944400e90240c010720b864026031144503203a44 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 273555044 1250 273553794 273553823
    0x60303020f06071d0616060b090c09031b0f04060f051309020d08070f080c011406030303090c040b010c0503030f0403201507030b0d03020c0102010f0c0e12030412 71
    0x4041000c100d00c041c21001030a0907162400d0050302c0503a8813400d000301c9507000e12092081740d403101d04175894410503000411440d5034600b8141c0061510070001c6004041050101e009040403500b036654118004000f88106401417403400b030506c030390b00400c0d500042104680341d41030340c1da030043c80c02502c504c0300c1c1904158070b03102c01c120030100410307109204039181040060141c0c950091220105412840c02903980200385410303d007800801c4401340c642c80c0081480e140044040d0000104400349030461f9403aa04c90000b01b40d140e2000341c610b091107500244803070495041540000c0c0c140c03201410000c545040039290303541151720031901100b281c501c1c0010807003090f030061719801d0507620094a0a0011100c010103039501c2208265045914895400080403c1c2c82504400c3c41c92030050407807000c296892602a54640c449180b481c099403c26140c008004413a03c10043c500c0340329510b1240398000715051002a203142040c1407944c0c0010003000c1405103a481c0c02070300a0b481100b07030700d00312003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 273556294 1250 273555044 273555047
    0x30c091f0c0c120c050904020a17160b0313062403030207090f0207030f0e04180503190219140703050f07090c03050f0114030109060e03070b090c0619020102120109060303 75
    0x4081d4004014940e210720000e00820780100184c2c0030780300b066503c84400d07162400040c5440c18a6030280f40c40c40039905010145103404a80c00030060784800c00e058801e034503800c64901e40d0208a0380c4402c0c0060100d120000304140d81c02050244064004444000d82c91003000b01102400790400d501582c00368008001c8401240b01ea41c02d400000072085051012a9030010b0803a001c1c00d07440b0080080500c0e10504d140d8480d030046d4100c070000e11880b014140240303819034480e000f0101c80000b22000070030030000180041070458070014049007940c1001d01680d50041c0d001c034542c4249826204181011001850030003886440c4c0e0301040050130301c036250070700c003100351420f1000c0081094100b80c20321817a400481c0c80f0324117417000c52200100e05042c1401103030040500b0341001e02560704080da100b10054000c001858140c1c095180402c0d155034211405540e404042012500004200001c18458814480104a01056100240c0340010300920756034413000c281c100090030380d03079035a0800415 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 273557544 1250 273556294 273556313
    0x905190602120712050d06050607060b0910030c1a0f0a02070e13080306010c030203281704120e01050714030901030e0f0d0e010504050a12020a05030f03030c091f0c 72
    0x1101840c62440c0f400100d540c5100c400c0e02d00c010168140300001c508440003203603580000e4043c040c007400c50344c0c56460302d0402e6005040c1043e05c07540148011070128040c1c406130b80c2c800003a641c000c0352120038280362070100545400c0713104941119003810700c90100e03030003020306c000e10200c102940109042424910000140c00700540345410002a880d1300c1d500241d4240140c0364483c500b4200014199000c0c2000d81c150300c06d06054090141e900c41800c43c4041542e5501843c800c902e5644e40324404210100f50301e1000e0070794000d070083d0400d803001d41103640b0411680056540600d0101c0c00e01005969a81c0c20b0405281421070b0b40d0000308030f1003401d5034144190918810f4042c0241128920b2f80c0c0303c140c403408010581010050101014600e50740201c080700c00400c0003400d92a22076650b5601001e0003014614220300c1404140d200058500d00014034058000646025500e181c03038401104070160302c00b90b001d5411a42144c00f6000c080c03c5001c003810320000d26103400c9a02142481c0071901c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 273558794 1250 273557544 273557563
    0xc0a0609060e011d1c09090f05070e03010b0303030c160209040c080123060108040c0f06020f0708151504090f03020c0112050108151801062301080c0f0a0905190602 72
    0x404c40710101088501400007080310075569036100d1202c01c1040d004040750350900130303082841c00901b480014894008603500542c4540400e0760b8004110340d01600301420303035031400c00d41030b80340c0d1080c0701080558a00310020500c0c14035200400e403581082d9070208015500444081d28290301505040061303510038000d0310100c2450810b481d07005030404d88090704026018201c2410415050001030400103031844d6000613080c13207100e11916690b2848000d65076000340d5041403290041220006001c040000c0112100703404a5040b4500c0d0ba55100d102d080b98a41c0c10201c0d40039072540c1e099401b194042507000380c8140a503000e060315480900001d012018940c06440d81c261030000100140d010100309200d44284c9013102100644491441d070121000a21207801035518094001903031030741d031468018146510301c5110380914032010054403801002c450364045a8800c10064001844102c020700c54141030b4285a1a100d07200c0c1c0110310540d8005a42c03402000e0124001d20a0701d4040108a56 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 273560044 1250 273558794 273558821
    0x2030a0c15081603090f0b011707150e09040501021201030803040204140103020108270601060206072a02060703021c050309151e040f0b040f061812050c0a0609060e01 73
    0xb4a003403504856241260b00300315402007540d42e200c02c5040110302c000c0d00c0c0e0100d4015054800d1544c5035010312011180c1c0c6e940100c424468103000095205000d0441d01c0318580d19155805280e09110500640060082088401b07542c200312440141c1034000c803140c061070041c0d500d03a0712490644103000840d04145c8004150200c03500042005030380c00580d16610411010742c0c000002980407400341e0310702150b00d10360460300503100049021503000a000340700704580d6030746030905002e480300f42041d0440e1107030700d140d03501007407508070f000d4103155000300620f520a10440d80e0380c943c10001521680000703040240065000424011043c101b001101d00310307403640035880b80703070304024071a08a116180e0182c4074103842c03900c00080c10300114241850708143c101c200c002241c60301307251a00c00940c000d042226000d1401c0e5142c042135019001000030107500c14144180c0400300b200540d61500901d6a08159200d50324a40b000101d15019241d80310348902400314a845d030f04a070b51801c0d202d120700c1901 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 273561151 1107 273560044 273560057
    0x31b05130e15040b06251a09010b0112140a0b0a08070602030c150402030c12010e0a0507090c020129040207170901030b0108010b180d02030a0c15 64
    0x2001c042c103c40c01c00043d03503440200034980c0600070071903140ca080640ca00842001d600110075038035018464003c400c1c02020070202c04600d04a0722542c1d981d4451181c1c2420356040b1a019509040350070040c1b00341c024500303045190050040441d499503031281d0030110203854140d82040942202420f4504058440382c0195890b4046420032901e84a41416100a0845000c4041c0a19802805000b0f40d00c200e1003004580c4d00c41d092415201d55031803502504451003000801045403007030b80540080b030318043c9100103c03507030316500c0310959042000da4131803114400715051840001112901080e18000d011034001c3c0240c0d00d00800c00307040004902481c40651000e407402d010b0980c1c080c41500f100400464050302c081c894005101c0c020700c0606403840d00030041e000c0b002c1c8068201482400d8940001e80b6003c2410404c1d0341801c11510f00740401110070142c800300d010507081c202e = true := by decide +kernel

theorem cover : BRFrame.Cov 273381294 273561151 := by
  have h0 := BRFrame.cov_init 273381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 273381294 ≤ n) (h2 : n < 273561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
