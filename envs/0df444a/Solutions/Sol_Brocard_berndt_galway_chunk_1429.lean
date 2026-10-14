-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1429
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:56:38.128029+00:00
-- url     : https://prove2.me/submissions/c3ed32d9-7dfa-4044-bcc3-6ba290fb1d95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 256834532 ≤ n < 257014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 256835782 1250 256834532 256834549
    0x8100e100b0c010e15040c0503032104050c1f080109061a1e03011d1b0a0c020d17040611060402030a080a0e04050103261201032307080c04050702010b010c02 69
    0x3040c0c000054502d00e40b0721607820b1802d4038807901e40101e045c000340720034810901c0300503000b4078046004514004059040c08076036071182e0b00c0c5081c1300074450001401c1c00418880c0f03580024008011030540c40710b4102000c0309115400041c000101841c00104250010b440352500b59010f10740e01103041c4080c40c50040c615400585a065030307106180e807040020780d0701303c0594080e04090fa942d000d2003a044074020340c0c048005252420715138050340c17100c01d8100c656040328a000c09034074240c290703904103002041a69070034a50041400402002c2c02c031900503008003900980d0020707070f03c1c0c100034104030b410243e80301c900703481c046c4d03041e0070051b030000001e170700d034001040c003202c182c14044420300390040081c04a40c002d0b4815503404200070b0700342c4101c0300c03512001088605689400c42c107013440c0b400d8030719448105020060840d504103480d0104210180d20b03445281c403c0c5c00803540c43c180c80e40f100e592a0486030703902e140641e0500c0f000ca082c00c1c0c018020241a0403041e9103000d111183c54080001c9103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 256837032 1250 256835782 256835797
    0x1082a0d020d1403191b0b1b0706020c0c0109060e093115090b0105040203090304051215010609060f08070306092a03020c07090207021f08100e100b 65
    0x707000000400001c08803110f40c040c0744080310246446030b0340340c035605903103c40d0500143d00b040309030f90420708802000510003070104c0d000b001c0e984141e504c1243c1c213541308840c062049840320300440d006041202940003000038a00301d80c20744442c2040c20700190f4a9012900600c2c001c80c00d080600d030028200403810680c000c2c0751620040f401140c880c00c00304107c0000e81030a8001c1082e4032103c00b0720484544981411440c5402040860855120304000361818055913110701d40010229404403010416100948001040c5104007444074454030b80c1d038902445040003160b8014000980c06010791a40001c507203041e00e07200c1540584400455110b42d008001c40705040d42d034940402d80c1c26040c45003030441800f241902c400599080c80501d15050710604010825004011500c0c1400d00812040100c542e40e401c09601c89046100190542c6110f0304d400241d08003648000096552140c0240c1c06044416207080d00b260f11034400007100c400441d51038030790850541040000f07030300000c0180f55070b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 256838282 1250 256837032 256837039
    0x3040501120f14180d0e06040504020d0b06031311100c02040b2803170a02071206090602030c0304030e0f100f09150206012606160e030f01020301082a0d02 68
    0x15510001082c43c0540010b80b100740c0c011a441d071040060f04020811807a442a0b10700f0035210395000d01000480c141b145d8000c1e98040c5401280c00700c10880c0541001122410050406449140610071400040311480e402c0d07441c030031510003180c010306000d107512a2250b51995007406803e419024030000d0401c01715080d80006580104040d800c04806003562450540c0360421810742c07442c2080c820104040744801c003400010403000802c0b0f03800040d05400c680d08210324211003e990706001c002003910328405403041340004100319544c0c51035401148298804e8640c6041d41d050030702130000208400c20352540016001c207051004500070203250141205910b4201e00142e102c500b080150021000300e076000d64850f030f0040c031506404001c00c410110080305201003a12004040c40e580e44030251251a00250340c0da0f12103280c1b0b1007013034856072103032001d030450300c040da02e10490354003e5009100741c00041c007400322001020010000220110f0780f01c2ca10540112020f402081800c08088500301c0c0d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 256839532 1250 256838282 256838291
    0x31103030112050d030c17041b090507170f010509181c09061b0809030325060b220f0f0e07060f0507050c210f06040213050108060f04020f0a0f090b0303040501120f 72
    0x300c0079041d110040140c607884500bc00c640c2007001011f07004250005058000d403d40710100000070788014030f202e04540045800c8881f1361920800c5641c000f58450b9107010500640e00110108048404410300280d955a01c2000450751000c0440700e250a01801c4910000b203500c02c9004207025002078207200303a000b0103982c07502244031665207110a003a4a07600000b50384c00c41490a000d194032801211880035035038900c442c4c0d440d24003a2525400501112100c90342d60404607540710b405d5101c481040d0300c018080000030302d10b60700b5980d03c04d5a48228400501c0408000c4003151042040c0d030601f40e1700000602249808108005034005a1440b0807e500802042e00e070000c00100b00b184640d46a80003c0e00e15804c20780184007100444200c052542c2d8140340041219400001d00305a12100d0400107a0703247d02d0390b100090b181c0c82c1404150760b02800251000c181e03148100100d800326101120100803100d24442816100d0145201d890b000c58048615034006080740d40200007c3c5452450016 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 256840782 1250 256839532 256839563
    0x19110304090c0e0306100501120e070512010e16120305030c070c030f200a03021012020a0302180a080a02061303050d0504060201050a0501030c0b07031103030112050d030c1704 77
    0x40440d10302459000000703410b02002d0750581005e028081e0040c01c2100701046107410721740003900154000311440701c3d482c0d60b070380c0c488000d80c0700b8041900544001000c0c00c142e4511030940c41d0180c160700c11400b049000b06807800e0320071811540b91070100c0c1c0f81d501160380220000c0d00e0540c1c0a0700000d00300d11a03c3c40c2001480c00041c00c90b040c01c2c018500c200703840105403407141449c2481045261613032a44c0811190000000d951b44440801100da049510582c038038180072007200c07103a0704154035206460000c51007407000764058000e003848109065111401100c000700f009a802824403c4030b00641040c1d10040160030194014000201a201c6c101c1b001640c03991404d14188400b00b80000080d804242485420303820b0052603080320411801748038035410340d00c074105c42180910421022200010721807080601404e401c04501c245542565101d6944800c418556244d4250486460003105a4a02400c0c003070321425207801c4850765503079014450324581c03800151000d0400e545a0704a5a40b01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 256842032 1250 256840782 256840799
    0x504021827160306090314030f2214011b0237080a090501091205100c030e030301030606050907051e070f020907020c090912030c0702010e102319110304 67
    0xc1000f54491007000804036100d041c0204118110040900c1d1850104140f040d05080214516008071800900112921020300c202e840a0b040001c01010741410070410004a8019405294402c0d20b408989090980b030b2482280c40310b211403510304102015000e070442e40350000246100301d04991a0400040046488501094000c000340a0010340201824030183d6070022944004180d200c40d000b110100c540c1e2001c4e107030890350b981103100350799603610110300c035100750820f10200300c0d041c051780e950356180e06040340600181e003c6c10b406680b001001c1a030442c03107001120030026103240c40100b0340968070781c0a0540e6200e14000d54001d0340000b07040002d80d94a944c69400b81c034058000f428140e4041c0c1c140408404e0080c603001c100e801903010300003030040b0541166402003442442650390f10589c0300580c0d0703103408015040d4100800c06241504907410a00015965032490401e0380720201e2049900511311031320285811a5681d62203620115005000b040fa040e00840103603070030180c448581 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 256843282 1250 256842032 256842073
    0xe070f210b1309060b0105070203031602060f0705030c0106082b140c030310090b010e09180a080304140102071110110316060e0102040806060925030504021827 70
    0x20b808941c0d9102428020442580300365822400c0a00340705003050f007650002030b182c1c0070382d07003030214200742c8020b50310215500c2000b21909026190403854441c0d040741040d56482c0c1008030304c1000ca41c6010000708005400086410101c1c0c562040e00c0b400c90320f80d9100c64248540c24450340c1c24840142950009521004041c00c0718038000c000550701ca141440003046883d059601c0328002c20303c1d000c4d8401c0c480c0d84c03000b030426074440d00b80c408c1d0038030780c94148281080c010880c0d240c2c2d94902511142c2d07020012114015402036024441c18400e852000b5165800c0340b041c082c00074000d100c0302409141ea0300340300d00d03528008800c41c2030411000780224000d50465000211b4003000200c2070081804012549c4100349810108900850500e03050554059961001400d41d030703c00c0c0000400141c03040c41318031803110f990320040c0e80b424000c82c4104000d0040c03c03040d2400c0b4420720a400c007800ba010b20032140c9034400e00300015042007048d41c000040701038400c4072020f60314a00828025040d1080300024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 256844532 1250 256843282 256843309
    0x6240c020d060b041803050d0e070305010c0302190503060f0d0204021326120a05131d06130905060f221104051006120c0c02040906060e070f210b 64
    0x8030f8408044000c10084904140c0a6103004ca464800440800d901c0003c0e80d15400c4440d030005450700d912054070b4906080c40c2e000401960822880001c52541174028000d64030b508800d200e10100980c45c1a07605010403149e232600605841c541d10300618190009032a45400a4170061074020505940352106541e60003420b1007240010300d000c5162114403030b06992100d9003000d07246041024030480f20a21aa003d15001c200b00895562124400401c0b24030080295900c0c0c50942299440007055a4000322000f500c9140751079128164003a8501134070080b158420081e0003a5661001402000400a000c41e05080c1d03006080c1054408041101c42c2800d02070048025140000000c10003542d000900d05030f094200b10300f0410040c0e41040f03030410b002141e01d80100b006616280304607a2240c1409001c0e60050401e000d03070060140c00e5100000752a080c800040a40e9036401003a906404c0b0a580f500000710721140301003540c5c04000c58402c07603545400011614a41d040f0006900d48815031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 256845782 1250 256844532 256844543
    0xb03090d1d09060d02030c0a03110103050c3c130801050903090312030702100614030c0103050603100519050711010b09040c050907021509031b0106240c020d 69
    0x201010304542000041c4040040e05502a0501190002041c2d040d04040d203080d004103903c1c8480c1046503814450903146042c00380107100c0d056501d0034142144403020654a010030710381008154151031110858001c0d4100c3c41c98082250600213407110710904038810600c0150f0b080440d142102110700c010500c4031202c0020390750701410300c0b590608668015004045036032007000180d2036614003040f82e0070344820303088000e40c40e5511220241e0074011045140b43c429490114040b0381c10709601031b00c109460081d01256206008003006508654003170f03070455455401400c0780480440e50303400096002212103050201003810490761030030741d0310544203031300411000baa05400c0c0e10000d200b14214002c048541d90b00e0342c101a01c0320b82034052540a480e00444000300000c9585000708030500007110030207140804c0d850010b11950b1247c02613015544091000c4844030314444050285509507403105403800d4047d004c1200c410360b0a8201c602e82820700100c00d44210259803041800300303041d030080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 256847032 1250 256845782 256845793
    0x130212070e0109022503030b041b020c0d030504051306050306041112030304020619030207050f100609110a05071b1413050f04060f060e0109020c1203131b0b0309 71
    0x242030741101c05070580100c0401441400a0810111200400c07024104200394800041085040031006000c00704c030b500d5002420708003c216034401d140740320603031002141e003170700c8281241c03408200401d0200030001d0000788007030000740581c0c41c0100707100503282581d042c000f0f50b03a176a0340007090a202c1d08590541315110082d4a00e02d19041050842508000e248051482c2d03180c1580080e00341d0080b2084640c00c0103264a14001090280c3d0441c2c4021f504007040b2890041c001e00003656407041c10444003926414244001610440d901840840d03104030f4082c14201049818100c03801d0300070580036070301082580741c040440ca203000395a401901480354141c5c0c03e84444002d01660610042c1400d060601e807404000c40c40c4044c0340c3c40d540044c4c0c404030200d02c07811a00300d40350113400310340c1151440c6540b85000084241c0700e81d00a00da100743c3c900503556007400c080074400307503400201c44c802a0481e00700c4598001641c821040e95208182c05510719a05841d201030000c90340088505e081c02d903105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 256848282 1250 256847032 256847039
    0xf1201141012030503040809040b03030d06050127030b06010c120302040305210a0e13111b0a080304121803030e31020d06090c181a040e13021207 64
    0x1c100a140c090709003150b411540841641e4010702c90310004001400403c00426100c545075a1170700841c0007120010112a1100c0305002c101000381868400c15011070f80c11251405080f02c07900c01c40351314801000a00004500c2c54941108500d401000f107410030010050303800c005103180341800c8040c82c40f540e005883d1415850607074038005d140900002c001592041817065044018116859582d980c41c007a0710240f000740200e9100c1c0d0900703048901060402e01c0e030b5480c450b4180003400b5040e005191032808454180000d40e101c0420313a901400042c1e003000014040f541030203000d10010250303e00980f198a44a00c2480074844503002200040c00c0508a0700c000d10313007a91641c41c1c1043c0380e220b4100d201c10b20300f80030894409464403103144c00d03004902084140c1e2240d1108000381032100c070034448004010303001015407003000700080a410110034040340d0266080d00360104521101a0030b0b1405081190003110560024207001004100c820750100684400300301e04980c0120780020084c0c1d070704 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 256849532 1250 256848282 256848301
    0x70609050f0607020d0e01180501030f0b1f091406030402090903040e010b0a0f02012c03070f06060305100203040b0f090f0a08040f080f0307020103020c1501081b0904020a050f120114 80
    0x2c00b286c9040101503180c09059800140007030301118000d081c0010101c3d105107450010340014040e01d80d000c02208500760440348100a00b0130000d90079610350002907141d845c0440c1000c100118103800c80414000100181404e41d030361908900024201c81c10700d035a40c807000307046c80c000b6048031000c14000318681103281c0d00202042c880b90f140340024001c003942a9a0300010b202550700c0042080035030032008484010910844020a0b040790014100d406c40f4202500034040a2004450f144142d1089581e44441882609d00440c0c3c0154100c1081e01c03100408110694007800041c0d50740504034080d40c4e440000c0085400303052181050603101c2c0c0c50b01048290f070f0741c91076020400307030782001031071200c51030b0301100302c0c3e000c00da09090050303c40c1889421180b03008028000412001c0e0b81c1000403d0404000a01089030008101c541c02e0b00b545100501074040c2d010384000f504541d043e10240090b2a0000c00c00416103004ec002c80660346030211203d09480c121030b40e004140c00e4400030b1140518 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 256850782 1250 256849532 256849547
    0xe0307061a18060402040b03151f09031b0e0906040308060a06050d020a05041a090f180a110c1509070f05030a0b0c04030606140103050615070609050f0607020d 70
    0x14501c07440d00984107158008a412005100c40800001140c01c002030007540d030b107a054034043c10340d82e0115078503460520800b2a50088044d41d183c821303142c01210144900388131440a840320720540d1483c5100b440e6942c0c403400101100f8000e01221080e51010030890a540b107000d00c601c0740f00004100500706410013800070180030b40142e020344402007050011540110403502c200d82c54010044e07031125205400c4506000d03d401c660340f00f00100c148410300ca00490080c100b181c400f140c003581000005070400807075140030b042106095130844006000ba80c91684189823010190154500e0804811f580c5c1c0e04089080740a0034007801040107012540d58108190030107002c01a103003076032a600700340c002a9290180380f4014640c903000d00c0011991034101040d18015a0711140502007903407074a40d41c40e564503010b80c02e1400245010f00142c07451500f201c00c51142420241c020780707000016107810300034180e003000541d928172602481d842804400c1104030b1260351268050400e01c40d460b58000c0000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 256852032 1250 256850782 256850801
    0x30a020703031406010e06030a0b03060c0c06100e01090b010306090606120b0301050c091009030203150f07020610142808060a020c0d0806030f0d0206070e03120a0f120e030706 77
    0x181a0f400704141c0f80d810500e40740100304111111901d070343e01d540c800b9014058640031241c05024510500680d260b02c14050000c0c0f001c0340c81550800d2352402e1828101088610a40000c0614540104101c501c82d43c40030481010604d004603185440341c01d084299403a40d4803203030002d03220300c152241a03100c1784101417041070100c00910203420881c503205414010813043c41d118000c5d0703100b0094681d018114040040d580a0165103502440f0003031100d07001001c0382c103554564081c000144020f40b000c1880c1c1e100381200b03110704c0740305400c00000340c010100c040c05068101039103858450054584024140300036a0101713038100843d00b400d09503810b01c031340580301610060040c00030448401c00030440780c00c007100d1450034583c16924800000d02c1c2c8084840900407500503404034802e0b480c0d0200f5480c0c401c90f0103844007400c549240d8181561a4059119282900302c140f182c83c0c0c03000d01c0f90b901002e0a4825240040c1800c040e0304144c2d0440c0c00511340c5560b00e51001601204102c0310340541c40c1305 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 256853282 1250 256852032 256852061
    0x5220807050111120702040b0a030b16030b030a022d0909241b0f09130e0d020d050f0d09021c12031109131b09030c0803030c0f0309070b030a02070303 66
    0x20b00d045050682003e0040420003441123440790301451154a540c8010001141c200500c801c542c100006000c001c001c03041d40103800282004040d0348036090005010640359805000000942e01802d80d80951048480c0c50700ca1140f49400c90310032036a1103030384850140d4085405060b140c60585121100e810118440070320382407100c401c04c02140000302c040300d090000d840c121942c40703d03038440d00f204502c10f03100e07010750000400c0000745510190303a11106035040c00d40101c13024122541000d82e5100b1111484000040082000c03400c1d440240000c0d003d00d82041034003241643ca650300081101e4034451105664526a010400902c418000c0b000720540460a08001030701c15503805802d01d00c100c102d5180112412105900c0d010300c5a400401960300203540c120240c12300200040940803141b2041c0c5031640c41010104079580040200d0303003e1b2030305038042c510f4031500342007d0f041d0340c10041407400320b800f45101c0001c00460010055201e070b07010080c01680d40d074003442c01408942d06419107608 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 256854532 1250 256853282 256853293
    0xe07080610050d0906020d02070b0c04050f010c0c031202030309010501060c0f020f01090906140f060a020a0b1510031d010b0105030712020d02040b0a140a0c0305220807050111 77
    0x1240d4461203101c408003110391818a984032806002c0c03c010b0300c84130200900d4907100141c1512526160341c00340c200c00d4480d051154440c0c0300e07801c01c01e01c039002d54012503a1054815400c0c0140e50300a400c2100f4803442001d280716070941d00d44403440e04003204c04100025801c000b04101d070a290070f101d424054812400c00d0421500c45440e08100e02820f1803000f4020340100c0d002c1d007444c0c2e00489100340101020b10007031040a880b442441c00010b02c151500c0d0241c01c92642d0700c62a4a4004152900301980340e004109801c507545030a064a00017405c040d01e1090203802601c1141c6611b104000e58407416200441c070580d80508400d490b1b54800c0d000505a450b003000340310182c8c2d010080f207401c404a40340c01010400c0c1c55604034001d1080d25541d33041d50703100080001e201e01d2a04060b0403080c4081d143c8069800d840f01c00c105c4e4078898020f00c40001445c0381d800c01c00090044c00580b80c0780c1003900a400807055810341c86901049c40f604049200c6d0312a80c0100700c0e13903900c10a00107880a07441c0c090030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 256855782 1250 256854532 256854541
    0x60902060304031e1b0b22050313050d1122020c150f1b0c0115030c0303020c0108010f030b04030e0301050901050613020406051806211b0f030a05060a1a03010e0708 72
    0xc9010756205c10050440c101c650105d440104003116001e642500713010445401103203480c0a5569522404070480040b0b8460800202c9150000700980d031650040346a10200c0c0c07003103041048000500c0400104002d8140d002c020305032480c80a848540d60100040c401010441c1075400300b60304c0144144030301107904081001c0480c0580000c00e16180c042e520f182c0743c06070061080d01405101009000031860702000000780030301048400e040f01d020750280c0b10306011755001124003400900400190641c9143d040001881003224144d02600924041c1c069000201c002800e441082d102901242e4540341440114503180305c0c2d980d0f0098042104500e03051070043e000d0058024090504500e00003030b13a044015071600012124001c0c00000100303140100c40001e04a202400c0d0381410003103d600468182240c0010100d6004070314500c400360075a41c68803000703c0a02402404190410300c110800a86003000091500b08062100304440e120340c14101c282c0d03075898000303108008000d40310f414003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 256857032 1250 256855782 256855817
    0x1e0f16061b050d0c0207122d120f230d0b0108240a05120607030509031c1e1d0f160b0705070e01170d08060a12060902060304031e 57
    0x440142e07a80500c01306810799154002d0b800c0000e664000407100118070b03414070800c04006000152200440298a06c61040012002c4142e040c0d860040640b0442040301d02024019407408001000d03d280825052101c01d80590180a806868080381700c0b012a0031041d441c4240142c1c1c03800c81c828030701100c1318a03207940300b0000707050740c6100010900065850310010f83c07a152410b501500703000d08a140d081032500007056076581e0495040b0006460040441c01c01c010100469801c15a0381690040107904840b40e4402000d00c0032050000c03002c80020681411000e020300c8044515900321098850002290f083c101180100703485003640021703021102403a594040e420640307102e01c211507111080c615005160885540040d41c041c694000006582c032034071800444140680d0069912245116600703480b101801e440999225212140601c40407035840b040c83c070101e00903017001c41c1921454010030659881170b181607000070f00420031601c0d41071303036400c2c2038140400b00e01c0c285258000f80340c1c51 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 256858282 1250 256857032 256857037
    0x12060411040b0a03020403050d05070c0e130602031302030d0e0307060c0c031415010f1505031608090a0807060f051003080405060a1e020c040c050c031e0f16061b05 72
    0x242d01c15075502044030003855100b45e0545000d5030344141100c0d01c50309001c402403c81c0d04240022206c2d0f000d5048003042807896a007600340580c0f10003149145140031660b41d0000394100800100d00b040d042908003025030b8040040c0c0c0311000b8184c85114110a0b15028942401c4444d00282e050140300b040f2540059402806002102c1e00241501200341c0030900246c1060502e0800c041c550801c280082516589070620308103d50990403e407110402d400c0060b1941e002c216807902c20004800d8501c3c00d902c4c01869903d50001843c01540c0880d42c1c96961210603401c5034806035103040e0350300400303004c101e00c601c1451f421450708203200781c4c0d483c0385964210a44c8940d0242c24001c0e00c000c18130f15002d50003086400d00d0740354184040341c6c4001b03848100035602c0b1030703148180c2c0c400c60601d240fa080f418051011241c60800d45009580f51045502055040241622815020510811403070420280c100081d00070b0142c01c08042d6036151850600005903000b150a04082d040301d8142900340a41104c01c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 256859532 1250 256858282 256858289
    0x9031e0c05101806150317030a0501060f1205060604050a030b0619030b0109200711040f0b010c170c03130303031116060504020a05030d03090303050a0e030703180504111206041104 79
    0xc0403442980c205d00010007051a036100401d0408048488150302c0c0c04038010798840c52860324100010784e40c5042c12135039a071010b110000458540c01c00084443c149801c160760190f03002d08002e01e00b80c1e03280e002c10140d0823145c0c001d440d400c901c5d4003404018685241c02c201500409001d0b550481d045858500b403810040c80ad440800784d44510310348480c81c07010040c01003c0142236500341c0b103511505160600c8801138000502c41d510b080020b20700c10245210f2000098010fa40b20325440f000341da600942240702c4c041020081d4402d0004400340f070400c000400d2966001070855014901d103150140c103403182c03d090354846401c140b1135002c24a50500c400443c56800040c0451319403694004115801d01640000e0b130103016086102000d150103030040200c00d803299500f00519540c0b440400304565403c2c00981003600f00f00120b4011a10980420300000420024502103a603140002411147c0f01000124100f002040d080c0c60b4200c4000d00301e0740040c05840c10f102080c00d80348540050701c220300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 256860782 1250 256859532 256859543
    0xf03080a050a110304180b041b030c050708040f17010e06071b1202010204060905270709120302100e010509060a180611040e010b04061209031e0c051018 67
    0x20500945840b40490760b01e400f50100c2503c2d034540d1180c802048095140310000c00740c0d410081d0049580c1818450680c040040844452085150040c00c401814020030b4402c10440c0031300c23405012030b4065004200402150b40707941d01e82450002440302540c0008901e9440343d25111422613a000080350496001682e8071f40365042c4030620004071001c550280028280840c10a541c1440301d030154000c00c1500c91070385a88143e15695402c0000000c020054011041000510340c44ca03c0b00305540b881d000241410981d00b955201c403c0d240c0043d00304401940140c0c80b10f11420305081d40c03403162a40c2351041d40300038051703031420b4004641c0e1030070007600c50925290351718004403080c0404101006006d40c440028400b1000e12809407c0b150003d00468162907004400000c80910701c6044500700c0d926a100c0c5031207a5801c0307085000501e8201c42c1038041c00300c051244c0d008140c0c11481c000081d152920741b020f425016003805441e04040301160720240385410704081c5215000d1100302021940030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 256862032 1250 256860782 256860787
    0xb01020d08010e0c1207080702160803091c212c010e1306141305040b180106050a06020d02060708090a0b0a0b060a0c0b0f06011b030903080309010204030c0f03080a05 73
    0x40d41c00031800d214007854001c5c41e901e13060a00030702aa0044c00140500b615900725280342c82e00c1c07c208000170f0007070301c6041e00c00d0b40204041c2e0348908107154200a607805045441c1d04460780c58403912410013500d8105a03802d21080040c2000710b801c1242d6421204511801420b01d20022082d0a03100365081083ea06000304000460b81e5903840031401d01540f0614401401890381d40e0080d0300c140070740ca903100b5100d071a200c060650300d104a480743c14071507074200301808280d8481600b88007240c80703003a401a80039501d550003c606c40d204e0090300d40c000d140d41d070300070980d83c1c01c4090000d04081000c1d005c034041040b07590903c86400d40002c3c0c3c3d80800383d08946450410b0312203205250051484a806070b0b00800040b484000d51a005105d07140c045008543c40281d80c3e03515010000814421550319020620710140050001c9220140100c41032107810030b04003040c3c4076201d5800e650402c4074104101e0703400003024410005e600c02080020021203256140440c00c0d40e17210501401001d0452041004c007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 256863282 1250 256862032 256862041
    0x30902030c13090209130507060c0807061b0e0907350108070303080f06032109030a06060801061418060a0b07050d0311070302070603150f080a060b01020d08010e 71
    0x50280c1604800000e140b0300316200c10319922009080c8280b02684074414903c00105400012906250340c01d44c000301500301c180c01d1010a4644005500d019a00b1480034440880080c503e88150b030560420040a014180e1a07130100425142c1e40c2c00700d640c004d4180380144108503030032450561420030100760191007808042030600465a880c0c0082302d020a089000241c00c02c1c001c02c000c801c2c1d80c029a10385200340d49961034250700f014207440440c5c02d0b910004c0003804c00200c2d15813002150704c040039118906800d20000030315143c000300003500c1c090f40d00c21003009860002d10a00009040c2c00b0b00ba83c241d52a0800015940c403110036001400d401c0381c0300011070940d030350503102c805003201c3c001483e103c0e0000d081840d0345905840900d000b0030314021047c1c01c1004464155560039506a0041c01c446040800c1140030300311404401c1e0004007103a0303000c50280841c0e0010340c0900b882070000c2c84000100c1c100001503c040c2e5881d1419034101c040b6803641c40f41d10003929415140520135902003a01e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 256864532 1250 256863282 256863289
    0x2301050711060a17040c05030c010503090601120312050906090c01020721060b060301080a060605010e030618070512030c0106090203040c17070e0f1509060a14040905030a1725030902 80
    0x90f4810601c1d040f41c4d101e4100410000031303141440076a24103034110340c94400c8a100648403840305940900c45988038000400095010130078000f8194841d2802480c5041e41801c0070050f90001e450b41c080c1504100704006000d40200400051003600b44000c004032803600c212a150b189030600002550341030b481d02d00060210270341000150010203000b15684c0d40c0d44080340c07612004051400c0700c00c1404c10300000f80e29882414028031622300140608281d03120b00714070021103031000c1207030443c60007030480c0040c5583e500d100420282501e000a10703581d00c0c1c096001c5003111403e40003d00018810300500c4003161403082c00c07106544d0302300100b09510b1651960f0350701d8006a6400b8149081000e002c10005001100c85035006550700420905510f240380104100700704219100d81e000a56031800700044a4282c00014034450041c00005d440d080395122641160312110203034011401c0c0451030001c007001c100e145a445031100201414217413800600d80c1e0080c8000c2551801c064441520300300b03554 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 256865782 1250 256864532 256864547
    0x4090212060106021b04150501033303021f0801031509050604110f0901030215160c0801060e070c020315040201020c12010506030d1103070b041505012301050711060a 73
    0x4040c032040310681d43c0e543c08000c0d590780141c5c40c0480018007002c40c484c20b81c14580116084000f1007146040c070315040000450040042060040209581d12116502e810304540024203529180740c1d000e040383d0540c0140030307800511224480281c0d0f0700c102c007a120340e9445008241940e0340445040407001184103d00003400c0001070141140c007031a0103100800c181258030f01e00350780c410348911a080d0341040802c5440c0c0e00034800030f174001107089000000c580340e0303400410b411100c0e000c42d0804d00f0182d80b81c0140a400036044240b042e95904001e0100708684050389034400140c1c034180d04d421490303501194507005000309585000c00440089001c41e80244805c00340e47c10043c14100d080705152175010b010700700903541d95020340100d41040d040c041c820030740b00c42d400243c61b004514051140d9220500e08100400c1900ca800da0705078440103204450040500900c01c0301d44040724810078a0680030b0101c41542d1880c1407040401001c0006049050105130308030040300c0701c07a1903003c410002d41360351 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 256867032 1250 256865782 256865809
    0xb0304020d0501050a0b130b0907030f111809010e0c0904152301030608010b010c2d0507050307060903120e03010b040606030203100b0f03041412120411011805040902 73
    0x107500f004100b080c40d17240340c1e00080c503080044400301c421115186104d81103590b50306105420000010009503854020380000b00260240c060000b010a40004e02c00b0441d008600b040b80e000406400500c003a14041c403e480c050240760001d440b15081a15120040344620381c141c80c0243d40b140454506154505800c600405040c80f0a91801001002041580c0c0c1c1502e010380c04a0b140003400f00d4908014420b0b00101c0c941038542180306105d64851039640d007090010503040d90100c1c0300d250604000c85418a9015108070003c20003241004205410054079801060421690000c20000320b294903801011301340b00d03810014108203008010034050120300e120541c009040840001d1b245070f265008510502140030f42c400c82c2925840b107100107114508440c080c0c07003805d20101d00420660f06250311001e60900c1190800c1140038110349803500101a520b04504840c400c00c01489040b504c05140b00c1c0d17003464503481c101d9468148035607000190081c20701450342e0f24204000c5441d0b210f0301811a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 256868282 1250 256867032 256867043
    0xc030605010605030703050108070501020a170408011503060c030c050a0807030e030f07150203070e0603090a0c0f090509060c180a03050322120213180209040b060102250b0304020d 79
    0x7582c40700c20280c180d91003600d034900020701d0000000b40c040404541d22096400c16030240a00c3d840a44902030350004590700608009070401c80054040d109201d03125562001401d01001c0c0380c80c40c204101110340700030145003130604220742c18842c2640141101c0402c0d0090501c500c039038403014003c034000e01e124454184588000a6841e0442c1c15240c0a0001140b01d0045c110292074a0080c046c140d010583c1d10002203a5070054051003890010044c582c40034a80d4200c0e500c5508540b254120f0740e40581c8604c0c05144401e0060001d0090741c0101e0780c0c0301005500138407140c101104030100d107206a41003c03440b120700d4610040c283d07480b00112002503801004494403081d0b04204984081d100b0503198488801a400000705080b03410224111150000d04410004207421826000303080034017540c0901c0d42d140542000142d40d0308580900590003070121818a1500c003002900e01450079070348a80c04408103855094460000c0b16000030f54050300c80454817078440f48089104604841ca00420 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 256869532 1250 256868282 256868291
    0xf011401030209091f1e15030b07050c070f03030e0301091104050624191b1b03080703020a0308010f0b040506180d050a0506010e0702150903091206010e09010b09130c0306 75
    0x12a007403039800c0320f81280e1079210080d10500301c14204400301c1d0b9060100e106407041009042020038489c040c000d81c888a5070804c58070b0002124070f001e0612010343c101801d001c940341814000e065010a0040c000e44d003d9000300a10601030701c5844421030b1801d680ba01c2035454200007189078442c1038803940b0030384030201d03500040704880e081c12105401c1081c142c00132850b00301645002500c00c0d800c000d0703091900f50094a100451f601c40e4003082e00c0c01c9560860850347c00d0400000910b0b04c00003028528060f901409044071585401040c030320040e2f0140200a001140600440403103070100c03812143c0c200c80c01584c4100c0100090b0304030241908503135002018000107007c0c0400445c1d80080341d4400c2003038405507070b2101a039401c035540c142d031098010381c007403240142c008070580704894001051004403424a84550700241c05845031554402840d040781c1c004002d01c0c410242c00e20b40003503030600244203841032280800c05606000700b401000e000f49142c103a05101110f43c408002c0d5803c040140b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 256870782 1250 256869532 256869583
    0xc030a030905040e0303390a1101060603050c0406080901060f030f03020d0201021c0507020715050a110d0e150c0109060b030607020703030e0d210c02030f01140103020909 75
    0x5003040c18920890f4000c9040c50860302090101100b00c034420a250482030007181c1c00b0f85c1c0d69600b005000c4c280d086e00320008082e0568803407861405801500415611081090440542c1c0c900751465a0300400030705060030240f1594164640564041d0340e002d2804071800d5594070102805804c043c2c2c051104034001c07203004410300002900b200c0c101c901a408984c1183c0701101300f03e00701c0c03164032201c900c003803034042400c070a000721600075a41217010392044a0001d83c89100c580c0c03e01c00401d0340b46010030400100307a12541e41100040541400401c00760251080c0850060101c0c10040e8031f8a114031260b0103403d806220020566840c4061080200414040d03840c01d14002d08100000511030300c9100002020244009600c600b50317680b44e0781d00c150600d0300c4001d00030019610074044a0b0f503114000b1000904c015501072955a60103036540022404250041c507060100d81101013900b17034100228280060312a10140341103da0503503540e0860741d1119015400c0c180c4822014041200090a18 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 256872032 1250 256870782 256870787
    0x21309060f08150c072012010c03150506040b030c0c070609050a052707051b061b0301030302150601210f0b03030901080c13030203120c01140c09040e0c030a03 70
    0x7081d5540c1c44226801207250301003400b0001c4046842d07a02e901410003860000802c0a40d402e0100070484640081550502c0000f600361b0310711000c2504669510304d0700c0445250b0600513508441d85214001c4945400c2c44003040c16889036020340e40818000002198503610010116440180c2c49001e0345e616a440382c000601c0100d640c03007154442c1c030407070102180c03519069080380b5076680744600013290842221003046148034000c00c0402448414080d8010351400760a030310320b0712040d0002030411850903032141c3c07103c500e25002a03200b040c1d05000510010360009904005480001220040d0f84d03071320001210142000c42031484a441c100c0307245d8400c0c1c110740e0064075180c040b409041c0800302d01181803503a80e010f06503540703001800c0070f030104940c0102800209a00440c00507850065500c1e50046440d000c450071514585080000300740c80540300030311640010081c81d600000381c901f005031980485028828107540f02c0d50341e541011740481d42c02c0114284202c0050141e41d51f002d09411301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 256873282 1250 256872032 256872059
    0x30a020105010e010b040b0a080406020f0c15011d0703090804050d12020c120307030e040f06030b090115050d080c100f09110d0203061801020c0a060e1905030301060302130906 77
    0x41d140710f41448030010845603803e030242d400303680c9100d4a071414607100c0b0760f007115650f1000c2d10903112154208410380c1d01d510068010705e606225000200500c441203010300c114010168000f0120700ba407080040c258400c000e2042d80c00950f1854003080385282420070001c14400e9038801e55000340122094810400300030040d0000c2440780d02500c1499503903209110801408406d0320a03076030010015480001e0045044410b2114050400201200c80040e603008551440d0400ea46000c3c100d002c00845510900980c01165240500c0c050b4491511010411081c2c5078071004120407004900700082d031004000a04c42855500c0040c405408807488000062100031420385124400c40409201403c0c005801d5002c03590141c001d01e61640c540400d6103a180c59107a4011165400700f10014520004101460421b4043c3c03800140076404584c0b2903190280010301c030221144a03003ca100480c80c003009480c11070385a03040240c0c0d540c0c2d0040f10800c0504183c0c0060b11802d2038800d000c10255441d815 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 256874532 1250 256873282 256873289
    0x11010510090c0206090d0315080f010203060901060903020307090c030b030601140a0b031006030c14040e0106080f060a210b0c0a0801060908030703031e05041104060b0412060914030a02010501 84
    0x40004000980c412038690301304a4030000d80d42e00c6660002c984902c20351014480c42c801e00c501e013155540301c050b4503081040b540c101d8561690044184189454604200c500421050a04107070881c0307198046602d0340900d100f2881c46664030081091101c0c040d03003007030300d80c0300b40203050307078055a1100a40600401c1081850b03025102b00e20300803541d0f80400701141d000d200305c02603030300c02c09181001c210054038055603c441003018004c0766202521241c8c01804c0604000806409a981050001840080010f08294102c2051020f211403502c07034111400c150b070034017440b1015201010901c004149030500d07004080c240d0301070800c400c0c081900090044800d803961030209990762a207084661840500444a0b140c0040000c1c6000901071f6000003c80b5a1300340d00700c051a820140c1102c215a4120380a071800b080401030f0085500e403030b03c20750019100070702c05113003030a09003108026031003801c602c01811030b956011501e0078803a2200e00c0480c0444402d003101d5032400681c10081c040c060038072 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 256875782 1250 256874532 256874549
    0x71e0b0a3b060c0604120c080f03011802180f01030e0307060506040509010207021c0c03150209010e03010c170903070b011e09090f022110060302011116120311010510 73
    0x30001d503451400c48112101030480340024a0940c9a50700c41c455403411048115092040d5401c003040042d60040c043c010558480200b0350710b0350316000107003202101840187c000740340304000e124070440800084c0080c1c80800d0700d2a030400314016006070024030860642c6030039480f000c80c12004110003a048070380300300c40a172401d1065072260650103080c0d004921000307510002d040b03074180b00c042c512200904003e001d4580c0102d440da990701c803518842d10380181c2004075030b000600c00c1c1280d43c0015038001c100320281c00820403440c40080c01040d00000c40c0d14000c0c000045004200e81103010810303200c426802c00c540a1007569140f18086402c16042c1550b811040541d4000a03510602d00c2044280c540085442c1e00001e49542004120481c00c010005025120109003040e800100314650000e6a1035800066003415800050190075130300210400581c4400c080820b0100499001c00854001c2107180011000030310f000d5401e8013190b2618489986071104000101c102c04c0800d01c01c595114 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 256877032 1250 256875782 256875887
    0x320a03020c092a191106160e0d020307091a090a06141c06050f0a0e0102030105030d050705030d0c031407020316030509031518071e0b0a 60
    0x8a09104035948202c40d4011241c60390303c03c0b0800126403048030700310301c501c0d001c0080c40c02400441c0d00510701d00f0012182c0014003102420405010204800ea800800c2881c09940048951134010020300041c031440f4000c0100304100750842d10104104005408482000d000002c41ca03421204010a9400a00d100c0c10b480c0021404240c00c501c2000151460200d6007048100b41c002404640044c0d00761440d0a284080800b2000c5019071190f40d000304c800c0020610f10b814003152220581d4580401d003001d0707902c10001082166000100789840e02a1424441d80710141401d00c03a0460003441408140e05081c01e007185025a072540c8423240241480d20710704001e03202c44034126540d01806403001c6441044ea0038000200f030241740131b4034503194014200c94003003c5007208154070749001d54012001704010a90015110820300c00b21000c1c021540c40c0000c048086403060051590358810b00b080440c0c001045d912140c4507540c41040c040160498094460403a1014201700c43c0c0800d6025500612 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 256878282 1250 256877032 256877053
    0x304050102090910061209020604180c0206151f0c14010b0a060c0809010315090e010b1e01090608330f091306050907031b0905010819320a0302 63
    0x450100c1010b91700c2079541e22005280794280b420052000340403e0f070780190300b448000340e128940d0655880c008074400780032460301c6e24808040d10300038005e04403c001c0c2070310413520100c81e01c1c0c0342c848000d1010b0445203690403219801c0140c40005041801811134176480b01e0046111405400c41500c2c80015141242180c1d5200c0f070880d020501e0a00040400c0000c00c009141c644c4280c00214034030b43d0b540f0b9200d48140c0e40c3c80407034048883c540e00745c0000e81d4480b100780c80545000f030048514441050941c1340f88417030980000300700b940a402071800b84440e401c0450700d034144000c2011003844c0d1110700d03508003801d41544860818000c0400d0b0748684022642c1c00402d081040308503010301c02c910f044c0b441c00c810654481002d014010801001d612415100001003100f03201c0d01c2036030003040100500310508001011003a140140c004080741c4d400703040000803a014941d041c40348a90050200780f80303401c1d150740d45000785a1840916074407107503210954400d0786003c40d96200d0903119070200c4156421 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 256879532 1250 256878282 256878301
    0x3020601150518010212040f18090c030219080106030c08010f0e1b1f0302030603100b1309060e1006080f0a0507050603190204030b07030501170d0e060d0203040501020909 75
    0x1021200703000103102030200030740d145018008403182d49014015111941550743c20704106e0380050740300c080380082c3c076903007003120300320b45101452042c1c010303030040c850f503000394460300c03c0940d1030300c4000d021b42d00036005c00c8c2c1d0240382c0a5040300900f503990002e0004c10b64038206050890b169009600184d4602415610031103d0391007461044144007002d08000c2c000e1521204400d0103644409410094060306103400d400c040c10242010326503600d005889041034014140340c6041544086612880c0142c0f0300700b0390750f4401a44012410031100800c044166261010180c10241e51030f0f0420701c10f0f0307000026200d1803500000c044e62000300407503507100080a022a40d943d03c56901401c1c40d001541c0501681c2030180041d640156440304000c030141480c984141280e00030b03071058402d02100c8084c0910300b5858098140102405580c08020b400118540354880304900000b6050003441d105c82c22250720f55005845441074250170854a9151600300310b4040d5000000c424898030550b40055a07205 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 256880782 1250 256879532 256879559
    0x403200103151412010501080601080c010f1211070803070c02190302180c04080a0c141e04091e030504090e0f03030c0c01060314010903030b0f0d0303050604090f03080403020601 78
    0xd44601e510500903203486103000e4180619480150070074414801305800f15401d01445000702540402850550f140201c1c0034140070760029014100300601d110602c0c0154480e0172009060710b03007140000c1858403130421041d203106000d0000c00c0c0741000b10400c806660401c0c001030603140282c402e0801250a824482d407001d03242c2c00b009503c400d43c0c1d00c0c81c41001d00d6250086038080071910a591600d40c44103400341c80e141c440c05080310505104101844068007100b21058241d4041d582807840000e298112000310240380ea07002d000b1a5101c84800a0280710500044590a004071480307080c5600d04009000307a106016120358281462540864184c00260121310351100c14051802e6898000d41c48540350f0100420600564a50b1808404109090807a0a010110900010b05894140b40160513220203498041c800c2514505a841ca511402402c00e0b0980c2d25243c000b546940b142c0000d4014140d0101c040c05031801491440b04042c1c120366114080d5000c0e400301c1d02c00d44ea81e4032154207241c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 256882032 1250 256880782 256880801
    0x80102091003020903071a1b03091309150203010b040e1b03130f021f08090f0304120611071b0e16030902030309281202090601051e0403200103 63
    0x20340703041c0c010300840e031007a405449020001000d46800d41d94407900049182000c03810704001c0c0000045010300011400e146243c4201d054015505103c0e85034001060206030004200315543c0741e4505004101c41e42c66800d480d42d07111b2004646958681d051342080e50040d028900c401c00128011424181402d2020482010f008848600d59038611104001c0054400400c803988910b4003103c80040e5125982d040701c455100e04400036002d80001d0040a082c40502660075036009049048505000441128142c0e220144419400c60440c9813a1008101800d9103042409002c07c6a17002c1004401e83c5d2204407400100f5002210b44a4112807500001604d0300403807002000c400c1d86030580242c0094461500040c10b6038108400b06012031180904850a2001ba100b18410039058290a0158202400003000c03403585501c25980412181c0c0c0000d4099414000b011900101601c64048920b07101e03104510340d40d45072a6030f4502038250141405190340030708100710ba0260203501c24070501e0003e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 256883282 1250 256882032 256882039
    0x40e03040f1e03050303160f0c0201080c0c0f0304030c030506160e0f131401051e030a2d080307080c03040209060904110a170c040c050406030c0513030803060a08010209 74
    0x312841c0110703402101191441c401500030a0100003c003044041c0f02440c0b00721001c0c40340d280c020380c1e854401040500f208a4a0b0280308000c140d100250740d02025040d4083d0b000344a0598039081c01141d00d14081e110440c00c0c0c8603100000d000710070014802400d03c03c0320301c5030301251501e0310381904001003000c4c8080f43c14000f402d100d840c086039103421400000046005841d100742c1511101803d03040d940c20440e2501520612001004182400d845045248966640f010a580360f00300019450f8000c08030007500c00000340121441c207504603000840d0a03010801c01e14030768900380c600500180c008030348071404180810000b0308980041c5040740d204c2c82c0d00804400c0103586040030045254006042951340b140c02403140300103515121100320203840d1044001502003030b0980c0e01e6140c4035146d4005030065003003480340003038560031800761404d0300c501e0f0802040c9192825404c6074940104800c441c0490103003a000424401c1800085001d018181d0300d800381c01e038540c880d2131309030310410009981 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 256884532 1250 256883282 256883309
    0x5030615061905040f0314060906160809160806041a070912060f0e0c1e010c020d030c05010f140a0603050c010c03170702150a060303020a14100f02030105040e0304 72
    0x210b14000c0b48111900300075040c41d85820340c500034a1100d400031283e0207180c0751002c0c070942042006036403013541c01006008910f00582e00c4040c59502070b4191080c403030140c0c08954100000d00501c041848440070f680002c5907910056917a075030007500d0948640f0719401d031091207000040426485110a81c03070750000c07545007115000820b0f484401c141c0e03039140d03a500e41c4000c03440ba40c01868610380d9050001c21900002d681000f9842c204041d00103609007c0303056008299030800f403490074141c3c0444426030a140b20703082c142c4141000d440001d1442d441d2150242070130001742e00c4103e081c1c00d010880c1c641603590340000812601326000c040e00582c0055101c1e44558400c50028030404d21030324101100130ec6a0144040180e400e03107a240140e00300c0c980022490085200c00c07035129180704810710100789103440103911607100c03000181049039484950a0300d00401c01c00c160003200d0f900d004020301da119000b005d000390420b0042900c51800c0c400c0b07a8452040010546040c1e60b0210340521 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 256885782 1250 256884532 256884547
    0x2010605060f030411040504030e0102010b03011413030c151a0108190c0201110f0a02010c0801140d1103061608070908060f06030c0d0f1b240207050a06090503061506 73
    0x34581c3c10040086503000465030001d003030360b2100c1c012039004038440c1c0ca41c01180c071200400a400e42e414210200c0c000d030324108441c08402d250f038040c01d421510b402e440790a65230290400301c0b0034003200300025007084280030f0b000454680307560000c039858170340b4080c0c1c58404600c60011284160183c0300f804000c00420400440ba4a42d60300400149506000015409240c401c16880e503410440400c18640d07004102008a55020f0040b0460040c1c689441d1480350b04214849000e600d524a00a0050008140d040100300a5101004520400404440e5180380c040311261920b41d4440000c00060481e0010500c11030080d4044400d44409001810f10756840f0020200b0856000b0306c0b00358580b10707c6025594507224400c0114100c1c1c05025845e19116850a046000700c4840c0b681441303200708100208600c41e003508800006a85000200c0280c41803010700700d1030880e8580280d03a10060078040002d42e2074014080c2d40491740700794107441041c2d5030b82044400d10b50f00844a075402c050308105030f1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 256887032 1250 256885782 256885807
    0x1e04051509010503310501020c0c040204050a0b0a0512150307090c05042706181515080709030204020c0d02100b01020c1207090f0903031b09090f020405060a02010207030f0201060506 80
    0x3801407090291204240041150007182c017150710040a541c982d6000828450042050118012111707007510700750b1825241c440403403d040014842e88008150100e541c281062081c0203c8030301d18079051020f141410101c0f04c0d84c01341e0300640c1c1e4040c82481045e0000034004c00c1801000000017032500ca0a0809142118a041407491055650f01d00c8084025410b8184c405100e00f901901e12540380d801c544415400140899980380003281c16014030800810000304800a4201036550903c0d221605855040c07042d00c408186800003944240082448000b1a02c0083d1500c810000d075400c45100700307150044407044072554200c3c01c0c010b0b0031122040d4081d051904022841c0d40c6a0780880300c10366a02c0c2c211074100c5000c92a00000c454591205506269043c094a490030100246401c4142c4081d0005010f8403520300c2001812900e450803e19900199030640e0000c4c04041c101c2907503903800c1c98000307000f503111800890103d80c580043e480c073f480c0305116070400e03124050801440d00400c02e0301c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 256888282 1250 256887032 256887061
    0xf0a140103090b0906071b02030616050d110309070b031323030a09031a091b0d050616140f040e18010c080a0c031a040b01051e04051509010503 63
    0x180d0505440e0b00c1c0001c00110750365506072107041c4500c050181c0381041030b4000c1402c032074044042c8558411100010141c1e80c045007081c1c010031150f07030007540815450425200c0340a4601001f094924141c4140380400200c4015407141d901002526900c03529a02100140d01043c2c0300d004106440225000004000c15454800c9411100e0000d1111040004c01031541d071041c000c10002400700313802001000741507011f40c880c5440e50500c00580d031900d80c2a083da51162880d4500384000c07200d0074131003a81c0f50a1906550b4641280603035070755180c4020108110309403041c1c204001180b4600c21803101d28203030262219102c1800c0d40b18605480c085104064080103850030312300755a000e0011810360303030910804c86541003a40320545107241100600f400c641c290b1880304141401d115076441300a21113030410400b4042118005003559288004a03402e00806501c0110100040c00380c8140c440c0c140058000c0790011210900081782a0300d045109e4020fa036112401b0807410702c003041514100800c6d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 256889532 1250 256888282 256888319
    0x90e07050f040807060e01030507021c0908300f22090501080c09060102010c0e150d020309060411030a080304150912030905070906050d031107080d030c02010b0f0a 72
    0x526038107042000109010507401540a0b8480340e01007102045100e401140c1e080b8803d000f42006c00840c0b90071300b0081d4a4603c110900115036104c5206517200e03c1c0240c1c00714000d4120042195141c1c143c0c50320841d5048078480c52a204404052892a40c0d0540041207600100c200303030b1a641060b4507280d0124905c007001c00b500310703602c03104c11010521103803511902c0c0c0240360442c01880480000014003d40348000b030810350459040c2007200f40c0c0726801c800c4000701a10181c40c50300500b2a0091013098070700400c29501500350000092240f04580003074010b02440c084c5031500708202c60f080030952b90301010b92008092141c03d01c0054086203000e6160041130721a40f0001c5600344942e902d407021110000d101002080da50107140702803207010000c0c4d5014140325001088060f050000240601050700002000c00c8204034100c9194070090000e02c0c005d240300d0045452102a0300f03809405894210440c1005603c4d00c607820f00310f85410060120000d4011344104821418071285200000c034406 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 256890782 1250 256889532 256889537
    0x21b03070807140f0109150c0c020f012102070b01030c0f03050705010f02030d050f0709080a1703041509031716120209040209030a060e061308030c0304060b03030703020d0e04020406090e07 83
    0x1c82812602c00b0b00a01d084244152210000d102150840200308c0391a00c8801c0308010a10030301000589401401c420244024207048042d0482c0700003c21584c45d01004031050580041800c0e410000340101440c180d0344100300c04001240c5410100b0007214036884040c01644c010341081060b54011030030403a8203c01881070303900d1b02c0c40711812076040e103074280c6416500040d80f004010003168001094030103080b0f050080c00450410317854070013000301c50880a220b40f4000001080810840e032412500100c2e10b1602405901024140913000c40100c50741d14154400650001e00115044007000d50b020b01540c0b100403210040035035500003500031a074101d81240d401c00040405940c10000821964802c0c4400700e89600d680b80b000e41000b40180040e80b829240e1003150b800640c201c415290b201d034010b00181c1d126500c50422001800f000314005030103000000e10700d010300d503010403427101511250710b800c002e024081041c04124440c500c0ba050006680301c0003800907520410065810000a1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 256892032 1250 256890782 256890793
    0x40f12050f1903110a02030706051005031501060806100f080406020c030f0c0709061a07060b180709170d080414070b041406120f04050a06020d021b0307080714 70
    0xa41210362940007040d46003501a21070030b03071807240d60b00d405044504500c404042d41020507401c0041c0d5207010b81c205c0141403d40702c60019084203d0140c3c60002007000400b15840100c1c414218400703400e0a0243c400003800840000b0441d08040306ca440041196a40b040c10410142108072103201c005442100c546030200f00c0450384540420103000080c3c0007881495841110014880c5022440e0b4050700d1160b082003001c004010301c0c40c1c40c81c6c05100010304071a5031009986041402410302940e41b0b948150408090850007240908803813040c00b9680310300882a8560105210000340080d211105a001180c10020a80709a1010707401c184030300c283c0c0c00803280300c035a80d6080c8045a042030b070384400003040801101d6401a00090604400d5550516050451203010f500e000020640807110003094042010013408001c1008820f810100454490103e0030341e85c00603501c022402080b10000d1f14107092495004011601020b52003c0443e2514946a440603011411003d10a541e070080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 256893282 1250 256892032 256892047
    0x10e010f0b0714030c011a030105010803040e100302030610050418170d090b180616020a0f030203090a0e180102031303030b030a121e0f020a0308131407080c09040f1205 74
    0x200081d003945c214a00011030608402c1d01451200e04178101d1952180c5c0c1000010440c10b04003004440503180742914107841c654500c0c019040d4824140c0c0020341510030441007100c422600803c0d078007640d104640c1030083c02d02801407030404038140c146c068041d80e01d010f1184480a0508001d00344e088090001084504568130760b18031244048481e501039007c0044121030b507a82c00e00010398091030081ca044501c0c003280c03c0080d0f68659a40c40202461081d8104005040c0200b00740c0308040c00040c0220b944a4a031100c031100381c2001e468882050040c0002103000b01c6060080c0c0e4440d401401d100c503883e00d100d032804c401805110488a8060003040d284101064083c509040f000480380c646e007100d403200d074000394036029111b1036000c10000c04001c4e5800310780e404241c5080d899003625180c800354984c100306040f6100603902c0203048030b010081c80000c840380421354004880d02903040c0e980001d015800e0049990089500510780c400050a0b2400182c02c040d20440b110703124034242e410881d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 256894532 1250 256893282 256893323
    0x40c03060909120206220b1009180201020f07061713020d0f030906090e0628030f0b06040b060304080f1b100b0f0a0306050603030f070c0608010e010f0b07 68
    0xd620030290f0b28690101940035400b50100082c80d040f04401050598000090b824450814440c0d0001000a01c4030000b080d207600000d8000b10280101e20700800580004070401d00100340401800c90250260190003800590086600c3c0c1c1295038540752151404004e40031202d0f0f210000f08030790340c2420910302c03040140e00c03031050907500b0383d209200d0140346420b0303400c000c1e02c40aa941c0c80f80c000c002c00480d0034402c94108501181d0008011b4452140561907443d0002450446a0960301900500800001800024280240c4c3c1c14007822101c011915094240b05c00e40700991102e90300b1020030030200b030028178000005c0078803000070002c0d282800c1410700003c851020302865400158020344140d0311400b014402c6500d02807085404030315141100c0041400a9442d00c00a04403561340e0000a400d9241030089401004902c6d20301c5548002d5460842c03803c500c1809a500000c185a0000c5039203200142c01c1070580e2400c0d41c2124106182038a955030a6004040450380c03d589000d02441010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 256895782 1250 256894532 256894541
    0x15070215060d1a04030806040504120c021201050c040e0901021615020c0a210c170c0a0f06050108070803040f0e09101401061103070c17030c030403110109091a040c030609 75
    0x110309501a034034a003085c0c00c0060021902034043c80c840d5142c002440001030b944c0d60101c0c503041031400d000c60310340500d00000304054400300b00f411140d401c000801006140c404010010f90b020540d107110a910f079100104c0c200d00807801c1101c50613039044004400b0407a43c0e120f8015120828030007602e40250f2400d118205050034204440a210b451214811054040070344081142185003403645859507071106c105c6001190602851180c00103012000e1801c148558040345420003e03020900d040c514088006000c02d11420190340111003000c6000c4001200320b408031001d6216003040e0310f003044d81c0c0e4102010081c0094145210311207694040ca0003d0082202c14060782040c1c26443d89411805480c22080072000241500b0401c564400500c0001000050b500c2c94081c240c503000998500502d54400c2c00300d40d22541c0b00200e80081003166000f8103040d914403c0c0c0c0c809030616034074420041900c00c0c48072005092001d0a501c9007a500300369026012009035407030082011507558510b481280d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 256897032 1250 256895782 256895813
    0x80c04080111270d0201081302040203010b030a0608060c120c090d03020703020a0f0303050f030a23041a0c0304060e010f09080403060506010c0b0408071a01150215070215060d 77
    0x1203058942c0007030001c801e06800780659100002c0006040000d110803804c1c41009041c0001d403c08101001383d0700200c034030204d078081d20440d52542c441e20702882035002280c681404c14104940411001d401003000343c001e01070b0107031442c00c04a110644c002c482c50010080d0440280c1032002d9a5296290711400310710a01031340241100341d0842c01408071310b119a4100a8003107002c0b031070420010307a00400b00d803d90620308007600d1f120b4840c0d10210000c0d1002c03101100c5a103218105200710000719000e414000c0303104003040d12004d203140040300b407517010845200850417420700000700031404641240700c1264004000007a042150700310307a011680544025600c01c0004070301441040140e2041e40d07007001d424284078203150301c0e17613803a02c46040006000901c008004500720b800c12621010303811007001540780712242176845141e4460389407890700c1c000c0010300c6401c0d41d019810701d4140919000318190707800707404624000804030310300a402425051b0040340105244000c110210070f400e60390b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 256898282 1250 256897032 256897061
    0xa0b09030d140415151403210c060709060e06090f090108010c0e040504050718060f090902101806210501080309010f020106150c06140f06030d030504050706080c040801 74
    0x80c149814901e8403403c802c00d108000918050301411038500d110202011a1102c03040c20b00e240d0341c1071001c6414035018648d9041c1c0b0030002d054001c0d5010104001d051075004050885400d65a01e8904807000e142d0340c80b0b0140400c4201000140134200f01c001030034240c4000e41030940805030400070884202090303110b0036140e50344680c2d4250591b03101702c050400c5502141d00703000508054481c2601d8004601ca000010a07403000017815103005a00880d000b4905510052889959100395601800c41500300703d1040301c0900084055500402c21082010000002c4c1c0c0e00d250f0500406450000c0c02000e4034441030070181900d0100302c528001d080c06040c1c800040c41c0c58100e81c0002411005001520f5010359050120600003440b03040d9108201e56110302d00000d2040003420700728000d141003074a01c1c2401003501d0401052503101c1d03103000c2c05000240c04640b075805006600310101c800c160b03002461034000f131000f0020309101301c03c02a04440301414452419659020180c00c580f603081303450a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 256899532 1250 256898282 256898321
    0x40e0d080712110d050417070302010f0c03050f0f0c040905040602040f05150f0307050405061308121213050c0603040f0308010605190c0602090409030801051903050a0b09030d 77
    0x1180380e446182040c0c000450300003804100d183c800f002c180c0e4080c0c001e480042542c0c0b0b20000e014840700d0541d01401003c00e0760712903626425410000d02030902846404101406d001c078101c10b040c8a0311030b51303114443c20220104075898401010004460103070404a502609000200d002100d91248070700581c8640001a640c500e0f0040c1032040149541c0318510903072200b4030b0340400c4107080d003c40c0e403000d440060039903490b83c80510584040c0155000310390001008110b445000010745896070546d682001203800003170450b170070408180b1a01451030300004000c008504030580e486001900c07107100e242690800119640071603205d0700112415200703040340b201c0d4a024581c000172518007401e0b051030160300e0310b0146418a106c1d10114001e42041050807500b40b01405040c2e4103861588000800901c582d1442c0d050080c6241c8007801801e01c2607410b6111030740f201144500400c01ca070707801303400b42181100703544800c006c3d808002c000c10400c0c0002c105583c46205284110282c1303600b42c0d0342d00203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 256900782 1250 256899532 256899541
    0x110a08010905010b040303020a151b0314010b0901090e06030a0821090307020603040f0c0e07110c0307051807120c0503090c030105070806060702030a0503030f0402100306030305090f040e0d08 84
    0x680d01d040e48110740201c42007201b440071a0707001c5405400150441c0001c000d45001141c0c15008044a40f140b40540c03d2100c83c0c00140c80c1c0c16000440c002c10511a04a43ea03601d803690040144a8401c1444c003040d954001004048562001503a0040d402000d0311040e003c036403169070107503002d4030810300d07500503101b08012030f001c0e040304c46904031116900440c1400c585502082d02c0d484040d20260200107410b09070030400c04005c41c1e8801030b00251694607080d051507000030303064410703d140040c83c60040300c95202060400060b0305080300d00c0240030310030740c012100d186185410050b01c1c02c01008408200101244024014540300ca00380303644445d42d0740707018117596081081100510b4801d074107210911007000c2d8490b20894000ea000ca07009643c2d1101f500c002407401600400052040c00040100f0030300d002d0b91030344e2502c1240244c50300013803414050700481c100ca0050200801180e002c0c402c01c1c0441c10590440b06060402400000760103030101d9107103140603070721501a000540d5100402c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 256902032 1250 256900782 256900799
    0xa0e06070206040c030204020711040e1b03341a04050a0501050309060105010e0111061302150c1f0207020904060b01091205280b180d1b15110a0801 65
    0x260340c000128406004141050f559420004881c3c0c4006445240c010688205101d5001002c41a00600800c10003074502c00041d02501c489000d2810320754401203050071035041c1000303d51180c075207009414075a520100240d05010200010010400100040b94081342c20010440300e94100c0a50521494481e4034100800602c8441c81d0015810000c0500621070706c088001406410b480302401d10b6a100c0d10164012500c5414081c1c0c1500e50788502c0c011711a002100d6196140880e0098510015850241b08080c1c0c5a01c00c002000d00d1941c000c140201c514814148480664070000318007500e007980710f400144034142d0640d81600d5042c1d03100c0b070100c0d040d030f003010003074006003e4029500400c09040d03c4203621a0781211900030443d9400b040c801d20381044000c0d0700b2846501c80044ea1190412a24200307941034607041c40011840b40c0000d041c001070058260b054007411410021341400c0d0f15607284ca6404250210902804e0784039503008896204402c090b1440c02e1880d40d80008030740c54074181 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 256903282 1250 256902032 256902043
    0x1005190e0106030b1f120f0603150213090b010207030f11010201061406041e080105100e06041401120204093c02010f14090307091b030e100905030408060a0e 69
    0x1142070502c0c01d82404ca0544170111541031116584001d4484011030100a4a502010038007540c100c92800300071900d2107044d03500c00001c1e02c0c000c409003149060070240ca8022440340d0f45107a5100e4006102c00c0011104a40056684950605c182c5203c00e0341c95544200b000c420500440390109036080b14109540d092203418002c0802c84c801c2c000ba000c034603000c24240d10403400b42445081000e00c50b034081e8103181622030003d003c1e2200030401450030300484581c0164900500c0c41c0720b0400f0002c85c0951505006038422042070800c030707030a80d0f441d10044181510300b421003243c1103612250908045a044240c04e100b8800c403600071000380d003403641c0303d2880078480540749983c41c072481e84260150340d100184164035291414894030003100140b40e0711690003003030700080d818811040d010074001c080750041d8442101d100c174155829803803c0300035419100000c812400640c003619040000a181d50400801103016106503071405423280601420048112041d10300c16482d911b9690072501c04000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 256904532 1250 256903282 256903289
    0xd090515060306070c03051c02040803070507080d030501080c040b030a4419110f010c092111010909141614040510091d01090e010902030606091005190e01 68
    0x45c800212036041c3d401800e031340218940750a6060f41d0005440301034065a04070303400313400d10750103d0303844800c1840d010b039a6440e180100e50340343c0100410301c05907134000d002d0786050b950003001800766580e41d08140002000020665a4148128039040300800c07100e141c003240d00c003201c0c0803004645840d100c201d401c02a5990300076955082c010041042c20440d1800e59074000303082c100324914017414200856440c2d40d0076012084034014a04002910305055010101d00581da440d40e020140d510f043c0ca52400203000b50400440c03013500f0f424000160126a101c1c02d440050418510303080d164850380085517000d03039061412084410920900c03076101c1207460b004500502e413400c448110740c2c3c1d5418480c0200d105240c01030348084802d11b50b1600070310001c0301400f43e8110344038000440ba25400c514150038491001110300d0301030040c0c42d160060050400060b00640280b44a0725404280722200c8030040401c038120507040030111700c6903210745110441e0107001400d08642d904120441c4c81042040c1d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 256905782 1250 256904532 256904537
    0x305100e0f070806010e0607060e0f0f03040e010f05031903050f0703020a02090c130b0c21070201200c011107031707030314060906060d0605120a14030703080105060d09051506030607 80
    0x50380c5c49070342d03a05c987c103c445081c0d0012020504003a1200b8a52800c000610010024051984010120540040035000f11803555460155a0340d0310388403060031302c0c0e440c01665003640204100044504020b01c21000c81c0e880781c40c00e9483c14268a0000045401c6a0700880042e040031260206500c0c2130880309800c40d0b11500c4071841c1c44113000c0060940b40080c0304103003c00788042807003000c0020600c409015000123024046039020901c050302d03e81e91010360200c0c04200e82617010400001c603a0b0765002c050080c14000c04100399440b0054900c05006000c449032880381d040d0100c006088561600e030306c80f902103000d81e150861880c010b800c0e40c1200202c00c2042d50100104070f043d50701d90402c1c0c0d800c0b18054440316943c07040a840c0070060005a084a90482c009601c05901000700141d10f0750814043c0d2020014218910b0340c498480c4500c0c074021300003800d42c0006108030310b05540100210003001d140051801c040f682c68034204004100d50004841c1035208001482c00d09101040e07205c809032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 256907032 1250 256905782 256905797
    0xf05010311030c070b1504060306050402180708060d050c060d02030403110118060506010c0209040302030901021b0a0b090d061503020f0f0916210f0605030d0f0305100e0f07080601 79
    0x520240d0030b024550000e0a417102c00000702c0e00c04072004c42e9165200310003078001e20103a41c480c10712710081c09059400700c0c001c0340d1051519030411070102c8442d00070f1401d035850407500d864031070421030a500c01030810f803494000c445150030ba5658a0000305143d0a036000d000d030700d0380780c103040280c800e0030508626000c0343d050510300340b036400718580c461036165030010b40001d1a444001c0100c416000c011030080d0400803042c1404180750b0000081c1603220000d13030858081c44160007450540c03001c031100e071941180c0845010f02842c4001809407903d00300c05810654406001c2d1560700640e00c1c42030380303500c0c125007110062042d4200441c851a1540c0283d03102c05243c81458003003102c102c001050740720b00f2244102c040000707d100300448445810f202c18005400800c0006410007095000e51003a400c9191440c005002d04001c0380c0e0594030407164490701c1004007070f108260060080140600840d070500f44d4042542d0039020950341c020702c1030043c0d12015140040014000c214042c1030103041c031044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 256908282 1250 256907032 256907041
    0x7050f0c06070f02130905190b07020d020a260f070512040501051204020a05060a0e0301060f0e010b070c090203091f050c09061602040219030c180e070903020a0f0501031103 76
    0x150102c0f40e4000341d041c0c1e04c240b04018031400700c0c0011318034142c00034114060440110005041d007802d00701081d001d802900d00649541703009a0b43e6410ba518900007580108100a0200302d04d02d2595208100074008400c24200c80207001c101c9610040c10004000b1000c1801018004c080011409009544180618140c10301002800e2802412510507400100c840020110b40750000d00c2d00051101400e01500c94a17125405000d50300300341c01c1e180c00ec0d03280c8100050f68420320418076084600c001e18850450f400c14034808900e5000c11000e44a01c409150009a400c02d6403006511403808800540302d510b00d007023070241000e403000b0360110a207410700041c041248020400ca541c4140c0072122a5a1101a40d41d58640c921041401a41c0036201094051044903288062440c08846a600b003003003c04035601a180381c506052a0030940c074002c041400719061109015820021b541808100340b0780e41d50014032050f4141c0c1021216100c0d16200b00940d5030103021b410600c000d00d58406d400c40c0352 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 256909532 1250 256908282 256908293
    0x80105040b01180b09011101060b0708070302010204080a0b0406051509010b0c010902040c0c1e08030c070516031412071a072102040e0a0506031e0c0607050f0c0607 72
    0x6004492180d55100040d44550b800303401c1d0800302d0350105006040959490800001075000848141d01056851000c60087c1c2c0041c420101603445c03907031146051907260f84070148035070000301e412800c2d90b5003080045050b02080004140722846130780d440b4440d142c503140080c02c0e5140038120302840c4480c0603c040740c0d6075920100606603115204c681c0d440c2ea90f8050540e0140c07a150801039001898500c07116206031f803003803d030a041809011401d000d80c60740c00b000c9424a0b915500502114024004580d225076090003c0170098010401c84182c00c0c1c04850141118445500403a2074244032403c0c2d408001c0c050066900340d0401011150400e082078071040003901c0700015150f031882d400c0b4001440c0c00d01034070300d5500d07903c002c03502c5000c1c80c103e845d0070b88001d40c42406203045044607000010761086050041a01c01c200c06005450b03002c411394941d1142c2c0e003070080345c10b090340a0102410079649500005e00780050180004041c00132000106a06050501a01d140a02c10400c4000041b54 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 256910782 1250 256909532 256909547
    0x10f1a01021c03060b03010b0903010c050a020613170c0604060f0b0303190207081e01060b0702011e03020c010e1606050708040612090c060302120703061a0903030c0a121b03 76
    0x404001030ba10140d102c411045004007103a422400007403802000115104030030a0207007035180e03400c0d0006c02154444c15425144c500400410100680c02040094a0300e007844031040085841344498150071600e048443d00c23160064604500c0c9a0f01c401d0401c01400150b00402852051008041015092a20119480344600411100100f00d001c201c5a0803520070050070005040101c141e414500c0d1014240a03403406420342c00e0700d0b560030030390f000c2862080c8070100d0303d0701a4161a83c690780c0207030a64801c11001b9000c040b10a1560912400c04401030a01030010b243c0c101c0b00240c082c007114404480c1c0700003e240c020000b0010180403103400111450112402d07505c480c1007030070404213848807050152200c41c100404a606c20a40010890382507005404003414104401c051681c6031402281290071a1044190040117244130060164550300204080c0c0e901030240c03450041c00600643c0707000300c1d0301e00448842d2707d41780480d584c00b45d1001d00140824403100b4003e0b8031444075107000b8503c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 256912032 1250 256910782 256910803
    0xa0c060c17031603150f0b04170309010906030e01060e07030b090109090809061315120506010f05041202030313030812090102030907140d02090a020c0d03090f24020705010f1a0102 79
    0xd952040305d19a0035583d00d0382800200213042c0241546600c4903031011250300184114203498698180401d403040011040d69046501a55400d0801d0311744141180500454100188075558541002c2030781b095182072a40b1803882503d0115050801105000d0380120590084040d5480c2051400015040204a40303d02d00112401030b101e035290500c486c40402290311000d00c1000342c4800212080d044030000c016054007200402c503a0303640a0045d204589200c0f12080028402c20050180c141d40c4021403103420b0001d41200c4c20301c80104500f110031051a041640c2e407403030103d0205100c00c034551850740c1c0051a10001c1d8103504000c6070140e170780c1d8a40e005a08500d500302c880340c145601c62409a00005400410001c1c540c1080c855283c025800590481160f0090070040d40e0704d02e002e40505d1045907482844081d004000b5110480308540301c420280c07450031190101c5411a1581c00a82059030003080006004001045c902c42201d0802881c1900e00c0e0491500e10b502e40e0700800d807207828 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 256913282 1250 256912032 256912037
    0xa03020f0303061c08070b0718054f05160201090221010f060902040510020703150b180712050603070305070b0a03020c0a08090315060d0b06011206060c0b1b0d090201020a0c060c170316 81
    0x1618030840bc1e10320588040c06500c5d45050072510040c110305540c0e01718a00885409407010320044010f80200d00781e648200d0065001101c1d50044403041c041d600d1096030100310340d000080e0a4410380000b47c10345020781e10040b08160041000d0241d8500030042d00015100f40c0014017400d403444e69074514400ca0b5400020110707a90b01d0480072507132650780424101d0840442402c13503900d05500041c101041e4403110a184074034000004501d400c0000d215419070750043c00400c15545400c10342c105a17802108c4c5c81d000c164081c0600080c2140c104240360f1450b1282404076143d403001d00c01d041c0307070808440c0045103041420f400c0c0722540d00e400801c00c00980e00000301030320316070f901001610001c10343c080c019600d524008000400c20752041410703010f80e100b1080003d103074071034030381d14070074820b2106031070445402c03c1013148028080355001865080c810700550318404207540b50300c5003100031940541d001c207410030022010080e60040540c000c1c2d205103a80b0f41182043c0d8044003c07400c0c550f00c003805 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 256914532 1250 256913282 256913359
    0x120e2b08061509060712030e16060e06211602010509010606050a030c03140109020d0506030a020907180f062016060c0c0503060403020a03020f0303061c08070b071805 73
    0x10f10f44445089401c61500844003081403001608014014070040c041c0c00210300850b00b4444412104d0f080100460740c0c41e94492801000704410050103030700c1310031030098540c10041404400c0f103004010a1044207907911881e00d82407041006825524001c01408560749004810720541d900002a07903a40101850001400091103034242c00910400c5603400d510070160000041c4000cca8005120130503c20f07409210303a0f00c4407414160b4404803484001d5000110320700040d00c03203114058502180b071950508102686e503c204001d0381100781d07041388001078540b07050700b41e08a92440040103450030305401440204c0d0131080361414040344d4001e00301000a42c280031001e014403003103c440a00b000506481e4182442c0c64069950703410100220054040d502240d2181b1201005a81c40341c1c401170720b0702c80b010f6046a0020002d050010003250910000e01880010030600c2c0e003c588160190346880803200c2c1f00a00400c180b2043d035101510070310560b40c10288050b103040854600d514070303018104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 256915782 1250 256914532 256914547
    0x17010306022109070513090f02041e0207050a061b0207030602030a06031a070206070c0507030602070201120c0305010f05060f0f03040302030f0c0102250506040201120e2b080615 78
    0x4002c00b865480c040c10840c801d0042c403440e01008a00c3c20110744d022076610b074248082c82d5a0780e054440c0590064a4202c5c036210000140c14035400c1285420542c18429000c0c0ca1130950000403600000d8040c0c40c1948080185010080e085c850b05416070240029159101c3e2034020096640c0c0703990000510f240d40110210303c0440194200c107016650007007031090480030141a9100c004030480701000148266404592510b024544441840d81c008e8003500f4160304584500d8081d52248900301d041100c3d00c048108221928800e2660800c950350340070610b945080c00b404510030302d03508524404c02d8100041d40c22041d91004503019840c84104483e05c80d503460806034114003502d00150700122001501c03220030981075006208244190001241c07694155001070490440c1c2e440081060b88608085000741d80600000d4554a510340c4011a1626400815034281010094900c41c07204181100f08804c20f40c1c181000c07071940302031a111240d4985400002d480004106141c0031b0090005001c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 256917032 1250 256915782 256915807
    0x30c04090201030b060f0c07050901081011070b090a0203070b161e0506010f08070b0702060405012102182d0907020a0c0e09010b09160e03010b0a06030b0109061701030602 75
    0x1c03211300c04014030164981d400e01002c42966800410796003031502403620046014501645520705980c01c0800510070001510541c20091108010b618202d241c14003061740042d10400b0303041c0c0b04000d00b17405010005071a20601d0300d010540d810800c4151030500c00c0135050b00d0711a03440035000343c00040803142260452000c001010300350502401c24004d01d00085005107204100c00c0840700d100c000c07100302545e581c0d9480c010703008910000758801410042007013250311030345000b806100203405c1c2d41d07540405002c40100300d9200c01204410341071225054421440d020800c8880c0e507415078800412000303402a0500c101e500005500e02c22030700c3c0008107499910030000da1401c107a201010746660303921030242e07504c0580104c0b00c00c10f05608000c45111030b4102107689034082c0d0007406107602c1305a480e00050f246141d620f50010b416650721b131a08006aa500c28880d80101940e03200040c20300c103a1b00004000e041560441c03414080404082c42d0421210701456045079003003240103072106c0300e80e4a017 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 256918282 1250 256917032 256917041
    0x306060703090e0901090309060f21020c0129040504080a0305180307050a0c05030109110103020f07020607060b04060e010f051309050114070815130c020304050d0606050915030c0409020103 83
    0xa031a43e110444104000f010056100740c4082d8001e44400b009982d03584012034012001c4c07102c0800250344031409200c0710060120044130203d04e240c3c0941045054000e503421200d490404002885021b0324a0f42a03d104040100f41d40b40180ca0a005600e810f0315090887d200b0003030501300700b640d14000036060b80043c0070a01c000c2519001030703943c0c1d42e1072402c1c00c0d0fa0300d044511040e202c486802c0700015883c9414491207501590203503942c038070500040c1c019002504a6203010800b418108080c000581d224401003d082d03206640000b8100c071030b8000e10040b9503168100140c1c1c4001c0074010f000e0301825036660000c0f1802120b00004451000c480e00c03018008001001b445e541c00c0121740c94044101d4405144641910340e10203030707195034070301c0300803003500880b070303d07203402c22003a900c103103401e4072560001110654240100c070314096903040850407082540e2400e0710100e55840085c0003038030705409541d0f04450001c0712503403080c20b490006915640b410340018483c5543e0381d04602164042e410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 256919532 1250 256918282 256918289
    0x606090903140304050102160f060c03091a0403051c0e010b0f031908090607030c0312021608030603070b1603090816060c021201050a020d05010909030509100e060d0606110c06030606070309 83
    0x18907003094848c0d20301402c410404c04800c590032402e00e8a880f903003074824440c0b00c3e031040c1c020262100010190f81030507000480070740309608000041110b0071030102481d070150403031243c1c1d100020f0b55281c1c580c502c1c0c0c21105240c0c02c5921880c421306105c640e035030740000d002003c810000419400d20029140211551080400b0650401c0010851505060300240040d102500903100e03038400c4540c1d00c45c240d00305e101310b00342c0318403039002d82881340046501800619032220000c2c007203810b11070700c41d2070301c0d941c64000c226000c0044903140d07602c1c02016403000301d4600400304000100f0a020518120114030341d240d0044038108458400340405540c0c90017a6003081240820080106040911050001e94032030384031049036900700700000854903833a1103500005601992898186010402000162808451a40208100142d1403d06551114002c1280c5090380e00c0c0020348030310302040604543d4400071203c070582c004034400105510b0f5042100d5201e4000c40303400340da8421610f01070f11604ca00d0740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 256920782 1250 256919532 256919557
    0x3070b3702041806090513080a0c0311011503050d050c030d05070c021806011b080409020306010c050d0c0611090109031101051608033309041406090a0606090903140304050102 77
    0x1420748440c0c1e003d952003901921401c01003030119030303910310b039048506007000c1d03009001030401c101d81610305114140c1114440d1091a22040c501024544242523400d181503031011800c2d01d01d002c2040000800c0700103000c0100c0c0c02c00c0f60500d0b40e544412500ca0048485109000e0b860740006500d4030311910303045011950040c802e942501203a07881c840c0d130447c2200d4260125004c45140a640640c020444500a0b80100d0103481e087c28030f001400a500054041ca05025200e01d911000500902005418600980d1011500b45190403c5015190800890200351108000c0304103e642e110301c01b80b0036281c00c2542064000b0092004807a0761290200c9590b5100450364400100490600214012440340841c200040d411800301b05e90300c030a00c401079591000d0b00740c6200341410203490036035005020b03e40308a420032950460605100f13084500e003000380c0100083c5030811050f440340324040d201007030f010003450b10340703542c082c042000c601c83d043e42c00c4c800840040c003042001d4048030002c0c81c840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 256922032 1250 256920782 256920809
    0x1a1602060c0f0c03070902070b01030206091c0614070f170c0408070603060503010c020609030301060804150204032901050616060b03121b0307020f04020705010605030f03070b370204 80
    0x320307440c2c0e46540061010358441c0c0502c860024414a0030700a0b1000c0a80008040c5126441c542c00c0060a0740060346207038110700d004521403035480a03102d00b1f4454900419002c02c01c0280c400304043c4500c401000c40c000e024040c001541070030380c00601c0b0b10b800c038001c0c501030a060b202d42407400a64000e0b0307404600f00d4032a605010443d05d500d43c0114089802c150001e104e1907a50200603030300e4010031580a5150780c4244010484ac9100c0d4240e107400500035a00c0140141240340144207a90060b08140c03081c15452200044841c0a10a100b4a80c0e1040f4180c1010303505180025010b44540000c0c00032949800d907a2030217100b83c503032201d9184680203084647c000300c00b0703101c00081d03044659513102e000e02d4880c2400c000702020080b28000c40d40248190011050380c400c2200a421414095035250740e104400300711030724204020000383e0070b540006c0d03071a01b90601e410a86d85000a154003001182e0f010b0f041100d210460500849109402c40c294a03020007201c0c5c0c1009000f9a40044880c0f02003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 256923282 1250 256922032 256922053
    0xd061104080705031203280207060908030618010f1707051f1d0f041e091b0602010b060711011b030503070809011a060a090f0905101a1602060c 63
    0x7495004480d02a000c0e1001010140182c0c03170103010803103901c50007110741c24012a0800600080c0c0c0303840045003400605195154843c41c0071101440c2044851080020034403a0303915000c00d440c2501180c3c120050075560500c122107002d888a0300c1050510381d001c070303e00103030440c0600c10480036141c0600241d0020440c1c04603044441d42d0304850501180d41c503221900012000004508110340241c208501e821056041c080102190000c5005249a020156140040d103004801102c2d0262840c80030002e58080d8a000c0305881d0b5102c6021b41e8507005a205c00c944800c010340701001c7d04030030002d030541070202c01658454400a468200d81364000d5204c1708040e08070020b1070007038185030307904403069490701541030803502a40454031041150102001e000e1402d88000c002c075a01616200010a5aa5907a00403016841c0c2007644002d4950301002080342403509504018034140440440030480f203941000d2038032926249500c0b00782c00c1c07107862040d921001c045418402100c400c54201000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 256924532 1250 256923282 256923299
    0x50913020d090b09070f0312050f030a0603060f0e07050d0809090108010218010905031f060816171203010b03060f0607030c0c0510020304060e0301061d090c090f060d061104 76
    0x3410a0100c90604a4501041c1058400645d00c0e056607800015503810300c0c01e54a803607a15081e840b040000b0071100308404081c1c51030f0031010f50700510724408046401405c41c6000000e8441441441c140d062810341e01154041c0c0002e80c1404030b0300242c80c2185202c0f59030074050300b00d10810002c2600043c206c8000129804154020403480080070541c1b80c0440c5004011105a0103600c11564180e02002210300a203030100182400310742100c10010702c140c0d0744c425041c24040e565100114103c9500000c00c42d810143c00e03805880c5421101915030700035038001250031804103006060241d0404000200d254072001c05941803150000e0985869016a103002030003075880040031103940c0315000002580e400c202c1c2c0010140301c0290081e42c1403908103003046070160b08182c0f0396075040d13480340030015010046172001840a10015564942403400050443c684042310b522580111003040070008022803c040c1c40e50007500031a802079010714981496005031000f501c84945103030300000e00203450032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 256925782 1250 256924532 256924541
    0x3050109081c060e06010818010e070602011a09041e060204230411030a0906060b0a093201030c020336030c0306040201030509070b030c0a081f030201050913020d 71
    0x244450000d00695540b080c40010348140b8410a0150001c40020440310341c0a00305c2c542e8890304a41005038212011014a400e4034481041d0784d071039070007181040c8642c40d82030088040c2d190001c00302907441016940840c501180081c8084d0481c05600d80840c1c0c0485c21006070b44049812078829500c0d13388410064003840385403003206240303c1124048a900d030525015540300010203014003400c569a03035140307101418100c00c0840710103641d81c00100c0e007005c1c00000342024102a556650800303060020301c10b042900d841d031102c02c600130780750b100807120703400c0300d61034080c000c00c0c030700407030111045a4140c0c81c500074420110100d103d00c3c0307150441401d04494480c0d16600000105201021031018036840799500380300d440c1c041d00404000750241d4041c4d0409900f0600d84c008070b0b590f91380d580c02460a50f81003a285445605400503001c840c6544c003c81154101148a01d48042c042c4861108425241c06201c005e044c8000418064580d50391081406d0301c9500d8000c0a40d031b0303039100c165800000e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 256927032 1250 256925782 256925797
    0xf0906061e0d060e0f0106030e0f060f090f120307030c030b040903020f0d050f040504020a0e0907080a0510080a0308060a051201020306031603080a05091c05010c0905150909060a0305010908 83
    0x4034500b0314005008000c03d4007030360003505c0b00c45d00d0000e60b90a0a100700d000e4480489022094490054070481c42c1204002091045008100052035414400a014101f495110360101d41d0350090840382401404801100d4010031a42800581c0040e010015800703060070342d0565501c2407078a1140000d05401003003038515100103030140e440c1c042c40c0c05c00659860041a62151030a80140300500603400d069005003604185820b0240d1155002000540781500c100c0e00440010400360a0205005140c00b8954102030811080601682400505a6a81020a0060200035041004c51540d84400c41d003000505000344c00410094900405c0728040d50042e2002070003071150079288644000911100c2080e01e07440512a0719111048008480310380118040350761000761014840c16070701c00c10a02c401090301c80c000200701004d40c4100604441c1042d4401070207040f4108441c420301e2519801c07030341d041c0c600311201800380d1948008a070311007810741c01c0240190f2070300c40b4002c180b0200382d021348400c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 256928282 1250 256927032 256927057
    0x6050603030901021c020c270f01060e01120209040531030c0209040f080309011d0309030d0507051f06031101030510062708150112020603040807020d12050301080c09060f0906061e 79
    0x65100c09c0300100c1518402d1181034001100d07580d00200c5e540c8138600c00c011101d0288000360404c614500000e08682d0f042e40d00140300245181c4c00ea100403440a031000d1203190509422501481d203880240c01d844d41c10f20002c0c403600036400050100712810850256080c1c001080710f8481c5480e5014034000e00000320381054021314049100a1001b0000444075000c6000d03000d4855607400c2c550580701900004801c85035401006102c48854a0b00811184425000400131440341d2546c1030441b2000035100a050405050904000e41d030142c8900b401d084640700d24140e61908050400894461041c02c00c03586008208080014001c40009102040701344064100605980e903015000c94480080ea00a411807001d100290100d074003039010313001d42800503101c5600651140d56000700807240c960a4408900e0102c0180810301c401c0040d000c0c10801030b5130075002400c00b0000941000c1d000c034003c0d80b00b1610600054501e07101c3c40103581c0185040a12090680d00f0301444540039041014032406 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 256929532 1250 256928282 256928359
    0xa0317270f072310050f0d020403060507030903200a0206030a020d0e061003081b01020c06070801061d04090204090c0e1902070803180f07030506010306050603030901021c020c 77
    0x4980402c407074151900707502c21070825a40396841c001d0051a80c4200013102c203208041c0b142041c8500b41e003004009490304004016501c50440c9000c004a8030081c251004152801c8649000690030502c8c0c5002003032020540b078103801c220801a032a000e01c0200080d0031a40110511820800680103003642181ca00c00c244a418084444269107040456420080106008003080030404890060110440300000100d500305140036007426a03100c0d400c7c0d010241d1121040020050f03211076460f01426207449d042c0601400307c5d98001c082c540b400101446650307103880b01411599660f00c001d0300184d200207140346036541c40340c400126410032a0141040040c9601d682d4802d112442100c40a036072000559007941c40701d031182c0704125551030480300340d445001c14000094a0803c82c1c600152b12613402040f03158154174140060700e1004d010f0900a600a1200b01c020b030b03030081085031104420300800701035031007105000ca14000c1404540703900079103103454613540d102c4401904440501445010007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 256930782 1250 256929532 256929539
    0xc05130e0403050d090c270605091b0d14090a03020f01050601080f040201090302060c0309040b0d0302210412030c140c1507050a0c0f170a0317270f07 66
    0x3010440c040314018009541080580140c0801c0e60002102d540541e081001c0c15448405100b08150292000c00321414000c0c21b1aa41c01158020301000e801c060310711002d9810f100b101d000350408a402101c40190010800000c01225a8411003103a50519010901d50515414290b25030007000000c0e001401b030120300c59141c410501480b0300078901139450140701d41d01e806040750b2040c00540200c0c100b14121000001613a01c1d20060640c01c10003401465036214104100400c0f14005410380d401f0705174048161001c0390f008034039402000f00200c1c155004040a4811003002c0c0b1070350304210840c0c0c481004410a166200600da82010300c958070342d060104001d00080d540e5224000303001e9000041d03c880203250100c81d4003404141d842a811210444481c0c0c1d00c0c0c00c941d00b9030340c01c800044500034800300040c0001c401c600c2d5108076000090146000c00d0348005120400d0603c00316501c1d600e02c804280c03400c0720800701f2107610030700d42c10800803840038105807521b0b0203110000d500c80c3c0c4540800171 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 256932032 1250 256930782 256930799
    0x80c0f070b090603040f0b0a020301060306050a080a060e0a050d020123090c221a090f1915030609030905010e0a0608041203020c150603010609140a0e100c0513 70
    0x803425181c0e00525207082035140c804000e15a0700062080340c640c00680344400019078010740c528000c1b404001c000d42c982d030400c40f005089801980c45603209101146c0d0030050140c0225202002e190411400b280510217000014a0060603060040c030302e01c9201440380125a0650000503a01c4208070a04803070019091a940d03a400255036540b0036821001116202c0d20b81900441d20111008800d0b030607010380701030400300300c90316050a030000c054140501a0341c0d2410701c1000760b12003a40c04a1070460304260080c2c440900308a001100c15660b141605480c85c3c0c01c54000100456205406001c2d0942c0c034580105665018030a00d03020a1385110003140702c0c0b401c2c96010041d10b400c0d5454074480d607140c0c1c032006565400d0103845400d055003040079400c4110203102c10f80c5020341181608080d42000000d05003181c0e03c40d03104004151a2035103c60443d941c8840d8076400c1303001100003281404010310064140345500035050038007813800c2c00300d400340c40e0000082c012800482c00240045079030790068 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 256933282 1250 256932032 256932043
    0x3050711030a080a200405090619090e030d020d0f0614010f0c060f06171c090b0702031e100e0601030c0b1b01050403030506130905060a0c02031204080c0f 68
    0xe11903800600410100621943ea004e81c0f001e0742e980c000c03907160195585201420f102d03e1101a20110005080c000d03810003500054010005070307500c020000c03110700c0302c0104900500503034151545941c4d117105155010000e44a00700c02150f0300719502d03815607000100501c6071024441155040800000364a44412124211584180c4481e42c0c030340da5a027030454501110180440d0441d40d1601800c0d4150350600c1880d029007500b2007043c20a04610743c1c1e0701c1c540364803c4800050314000c2e421881509500103205000c0b100410748107900c60a0a00c000b07401d1900030103201d1034210003240b03c4501c2a90010b006001000c9200c000c109902809150a40710b0a09010240141001403410800d20058100a041e81d4414080704c00d592004860b2081c25510107039810b034002900c0d4410701a10703190980b444020103030070322010480c40c1119030fa04c98072441c0080003903003000e56400003480000d000b4400c0362440824092500d4162400d0b03e00309a0780c2e008501384940d248503904015100100000302c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 256934532 1250 256933282 256933307
    0x201050601111f020708041409010e060a060f030e15221205070212250b0a12050a061703070b0108070807140a21061a0f120c06030c0307030507 63
    0xb80c03181c855440701101c00d001080702035424013642004200081807510003c0c2025200d1f050700c80184000e1401002201e60041c0c004090142c076140c240940c2c0d549500c160022624141003001c2d00006811b021340c02001e00142684550085046130301d146001101e02c0c0b403045105031030140b04941e890b208240c1e03142081900038080c503900410490514081d20160903c20700c000c02d000d0341c0180341c0c440c0d582003e501c503000060480c0101d400003003030702626813400098086200030604112032240000c0103c403101d001500c0e400d9035100810005401600010043c3c240c2101c19645e100e030071071200d5a294001d96007500c0b02c42040002169001d00401c202d0f04840107100108500d80c28401c4640901c0c0250380000d034080380c0500c0010b580e45000b800304030054105802806040c1e0142440010f85090240c2028450701a001c0442c035960780c00b01d420814041664100050301d44024940c1c81d00385880c3d0581e50061021003089110b001010045101d0b00c07007560244010b48600605480b00c000600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 256935782 1250 256934532 256934567
    0xc02030901050d1a03030a08071202070201170a020d020c10050702010b030703080a05070c0b03160e1003090501060801051f09060e0a0903021c09060206092b0215160201050601 77
    0x301c3d6403003c10154105071150140000769000340101c48000a00e0f66202d41300d001e000c036200c1c008024240d034004011030170b8600b180d60309501d0a00741c1c0e40020600e0807080a064600c140041c0411446915507041c1c1300c0e02002c0ca8400c560383d000011446584850164090302018100400038100500c1070140980c80380d4060001c09100781590350360030070f03604000304441c1041011701078080410a51460407008040c0b11001a41d01d00700f01201c805201d401c1c0c8001401d0208030000e90a0680700c104041d0494034143ca400140e42d40140340c041d0240c0034550001e20306600386030520204045060300301a4600ea0311140500d00c0d550b48119034259400c82c03085050410050000582420313950f0007640c10140310307106440c500d241e66040402c001c400010f03250002a0555824000550100115034100c4a100e0091148150000c1030b1840105100c0c002e00010180302c20b18012035000700410b401c2401400c54007034080c50194800444084600c688000541c00c1c00c0c0842d205500494141c1786038810310 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 256937032 1250 256935782 256935787
    0xc040b040302060304110a090b010f3906241e0509090a0c03080309071e0902160b19050a020c0c09060a03080408060403030c18050904030905060c0a060c0203090105 72
    0x142c08104181d00018029038245002400c00b60b420780c0e4050f5030402821244400040c0d805000000511050750007042030140003e000c22070415040103094102440d40400500001c482c0200e242c012489400800511990038a618800300c40c003080381c0381c00c440070a94003544050b40d0707491001142c6980301d400101e007011865014017142c00d1581415510406050841c0d0704c1d0002a40c44002000c6030ba84140d800c2000070061001c549800d02241c0010620b8245e404201400c030144590806041e00ca80e03040c0c55400280030414010150b00c1040c180e40240d031141c107501d00285402c0c000342d2106c81d1305031102e1410f0001a141c4140b44251070b14505008000c00794a10744509000003410041c001d41c0c1c2c40281c1500020009880c000100081d00500000c0c003001d08051a000e0180c0741041c03007140500400001e02030180c011402003004644044075034041a481e681825030306004280c21480d08801d0000b4000c1c1d580e580094290300c0d143c800c41003000451100345040b6243e000341035619000130000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 256938282 1250 256937032 256937039
    0x503040b060a0b0d0c0206060f0108160c12030902011701030807140705060412110a06211b051308031303020d050316050703030e030a0804061b05071205060c040b04 72
    0x11454030341c041c6024280014203038681c51625420341200680c90714840c3c6402501d40d01e2941445010380100b03090302c0b0450541011030000c1c0c040000100a02c000080c0d00180d045914403803c6a211825000841806034568240300140603141010f0241c4c04509a2a802015030031000d41d0700381201d803c00072050038503191b82d60750384041c4864010700426100d800c001013000e0340d40d0b50091009000008501108034841e00d01080612032009281d48039421000082000039000700103603841081e04c2e030681003d14101c8842500806401051882e11002c0c10210401903030014001c0100c1c410070040808010b0303655203196030360302c42c9445440b880401c00104000501340f00407070891551050051b6400d14002c0344102070f100c0b02c0c1820a442d02e6001d500c082041c190802a601000340007035028044016240c2c0f91032035540703358820f0744104000a20180c102e08101030801b901d581e40002910030081e5542400e0806e12801107080e2880d0203a0004941c40411050803203088500c9000c1486c1403518 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 256939532 1250 256938282 256938293
    0x12080f0106051312020d05010204080c0f0f0a0b030403020102041d01081c02190201090308160b0a1103161818140103051b03030409141909020904020f01050403050f0c010305090d050304 81
    0x4c860310105d030003014904103000020805e00260000e0003a10b4000c0a90540e91002c1014226041414500615150b111030105440c1c6c020124161181c05141c0f680c4c0c1d84452604a00910031548020b2004091101402440640b4640766040712010400c480d202e4500c04100d4042800014040e4050ba010b6640240d00c04d81c000c8001d00414014140f03a1301c06680e0303494a90711a40000c0489144203040351a000c100000a407604d50007030000d41040200400455800f582d07484082c203100110a142c00528108901c540030032400302d107008241c0b8043d00da903042800d294500300412048031a040100c002500e10048030030364101d0f9040402040c602030f42c0202e801121116031603150b01400200320126204c0302d9070003a03840c030040d0f1103061041450030001205603c41800c00003450142451412b5000d40d45070000c4681103a0105da8031403003c0d610a0041e0380a21450f800100300e4046d40100003454000820000103002081e241030203a036513170380911341d03c2d400c0741001c02020440c10300c0403801044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 256940782 1250 256939532 256939559
    0xf0e101806261c17010e07020d051215060405040e010905010f110702122a0f04090317060109090e0106080706050405030a06020c0309040914070f0f0501120912080f01060513 76
    0x16541000308800d14400101800135209030040078404e00750106016190f40d0410003032003003450b540380c00c6061000d003140070049100e014290410200304a10502034560340c3c8400c0710020b22008200f044903e2510302054041c149900040c1d4030341d40707441c200c0036000b4400d010740030306040400452440d2490a07401c001d242491081c400301780d44a420088285050481c402a60104981d0111a0007103400c404210511010b01f001078040ea041040074000a90002d41c400f0209605c8054240583d85250040740d1200d9550701009109040450f1a40785050640c04401074030002c0c1c094440d0983c0750b00b019101881188580c030341581c0610b007044081401c0b0307809041002420001c0d28a40107a1100107425208a0b240c2584c0d00d0050780c580c16500f10041100c1c400410b000200a540755180520030000c0291520482c0d06001280300201e0740d04003d0790044490507880800040c00c080c201ca0300410000046071590120510840045411350248041c2c41d035800e030344445080150700388000b45c1c400380d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 256942032 1250 256940782 256940833
    0xf06040b03090c10050d0501090209010c1e0c12140c18150a06090e06030615100e0402040902030717090c01030c11120901020c0a0f0e10180626 63
    0x14083c40e0168500d941d540ba030003d290444940d101c035110140015041c00322070041c0d00000303281c3d00c100500d980380c0c0d0b000000c41e80f5160b0082008144a560084040c40011602d20010158080b50501240d00c01c1003d08154816002d002d861459401ca01c4140343c1d14030707030041180d50140702503042c3d0001c0c1080729003480d417004a01c02d08070a084902c1011800d00f108039042240031404100c0140120560340c0c51031a4001000c03002042d460034110f080e00740300b2006181c2e40740600d005e21070a4041d18010b0b540c684012038043d008540d215580d4005100940003520384100084c1d41101040d4221a002c582c103000307600c00c50250404180317020045d001441c0c07a5124506200d046024500e61003030034458101d8142074030b00400d42d500301803400241058040c48070380e4072403810240140301c12204800e01409665000788840c50b19211b0410075000501c80d68401c0f45445a032044c21680d03801140c001c801180c0c65850314503080a8080c410920066a180001190f1340c03205070400007070b03541589010000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 256943282 1250 256942032 256942051
    0x60307030809120d030b040b010c02010806240403060b0a050105070b0c03130b0f01030506100806041b0b0f090f01111b01110106240201020c0706030c030b090a0b040b0f06040b03 78
    0x180d000100e10315082407a240d1051010942c0c441c403182c543c7c00e160168010418003441c081c065090b0540c00070303110420150090f8003c2071411442071621030038900180181035520042502d07a5901d180c0f240240910301201c90103282c0550300001d055000b0000d80e5819548030310391894684c1d032064000850380008010720501d000303641045000c200c180040d40c2c0501c04045203902e881d07045040030703403600300c010703040b000345840668080040040109146070800e600c5000c1004e41211070340001c6e40840250880d10b6562030008241403404050402450780310003d840daa80709150590054071012501e4034510300769000340454035000c00549083d103c039180b050405000c1c0a00d490394080c215a0682c000d0b0034018046030244a019905900e00c00c103815a9200a52816545250450321448140305000506881d0030301185558000c0e040450b078520060100b14483c680301501d000504a40d46100d80a81d240251238812401c3c110020080190090a003924140c0340c06411003881d40000c040451 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 256944532 1250 256943282 256943299
    0x3030c181903080309070509091b1206070f0e0f011b0c0314030d1a06120702121218121c060e0702150c0915031e180f010203060307030809 61
    0x540c200084800c0040c1d400f540c0c4444e140d1a0080c080d078130b014250f41200d44500f08400070003144141c000b8810080b10344540300f000c010304112020403010348040301c039110b56001d00d904000140c0c0d8428030060103c0d2080d81c0303d1110490365802d01c40484202c09000d80026aa4039000c1d406030700c03080c24026018802c4a50202a07982ca84910070382e034401025074891030b0400a03003200310341d0f0540201c08440d0920090700c940d030200e5900059042c031801c0704e94807010342032400040c042030090282c03085d40c1e0791041c0e0050303079200010110031403094111019046140100031081e0345050001d01c0000c030010703001c48070345400243d0142c40d00941130802e00c1d40100d41c85060214504541010390340c082d0907550001c010144000e000f81d425402c0003003400307498000912802540c0d0ba14040007031140b00c41c08100c96544d4540d906208280ca150300340c944519042c0c5d0b002d12161a10540648012010700e009440384040c02c0d000031820f03071106849055044d4045d0a0078008920000d00420440754010400c05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 256945782 1250 256944532 256944559
    0x305090312130605040b030a05100801020d15150801030b18071d071803060c14131721090301020c0f03041e050d03080606090d110301060803030c18 65
    0x1e261007090000614041c00101c1c166002c8200b00c241103020f400c0030f05100e8141810003451500900004010400c09070303ca80c00718440810200a2401030075400e8001c0d95100281301481c0c028180311071084541114114000603d8031800e8001107160315940c0da110140d9286071a00521400054030310002211105c13a2404980d0040000701c00a00c440300d143d091032205003110581e0960014000d4050050004928000c05420010f07041926441080003440c912454002c440c1101c2003802540b4620000032085c101c2e0312208451070844404910f540d407013450800e031442d00ca035850f400d20f207002304042840d2508640268003801c0410000303000103041401d244040352502401c5151039085410010301800701c10b518a604104440400244142d801e182c000454000d04680c617001d820040380c800841d1096444204607404800014154400300c046414021620309000443d248a5071a11000040e4a84080b0a07240300740740c142c0c031503130038112200c5000b4004205903020960064120b026907 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 256947032 1250 256945782 256945789
    0xc0616080406051b0406090f0807060f1809050c0912010c0516080c120d0f092a09060f1e05011403070909060f0302040c110601050f04061d190b0901030b04030509 71
    0x3403009244070347c0c644c09040c1c60100f0301c442081c3d00e604450410780010740e00344881904244012443c100c0e52420160f50030300031140000c840d000d074003d41d0103981840300f40000700f00c1403009001c03220021101030b2000d400368591542242c040351904004648103000c010341d44100b00a400a00c039005100d890f24002901c030085040006021030400d46074004500b10b030604a461042c60381d402c032201c00c10000742202e510b07040042002c0001d81000808210542600c0098161040c0d004240d1500d041c0041621200d69176200241401002c5e9420742c000007440c0e0b8560f0100200c0d08130b820607180c2c4d03074180002c04454141c66000601c000103000564030300041aa185109070001030103501e00505196085104004c1602c860b07410440c20424085440f683c6201c01240990450791308480010500c2d03580d8003c01c1c0036001a6000d141e0341c9455850b00300304208898841c9100d1050141422003036001c0208540072110002411030b0005440741c01440014900392446401c00d009082060034a603001001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 256948282 1250 256947032 256947037
    0x8153702030f040b0907030b0a0b030a020a0932060405090a12020105072705061303060e07050f060f0a030f020c0a0f1209060804020d060b06040b0c0616080406051b 72
    0x200d100d111410b074200002d1021458115410000e0341d030280c100c0138030f5030b02e42c1c00765008003512101c0420b940e031010010658081004854103640900490b0000780d50704d60f104000c01c01c46090049a07100c4c1d00304140c0c2000d00040c04411018501c6000c070b40340c3c4941003408003c08004214840c984181c1e050400494003280d140484020300da8004141e900d0702c00d500411603106c001d4004840600350107620170001128001400b9142c0c00d4800586502200d1945a01c8a60b00d030b001500d1280b900b4004014240042402c0050b83c00584a501d0151050300a001c200d01c90130540401045060000078201403017508078400c690f0500344054104080302070a00d05102e1005011140f40c58090103943c1001042425101d2116031400c02c1c0b20210f14054000e09582c40c0144000e100da004030002408011071540600c903a4034000d407840f5195130b1182050040c681c031801240b40d0a10881c030000303201d0101081a41c00c0070b603065981c6100782c0c40e150745501c0500340241c100c0503c1c09194419201c0d01c08401c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 256949532 1250 256948282 256948291
    0x70509010b0403050d0e060a08071418040510030203030406050a05090603010b0705010b1c0308040807120906030b0418080903010906050a0207020109051203120a0608030301030305040815370203 85
    0x1c1d1907070740340c1c51413903d40c0c9441d4000703c880c0700340407a4254103507079030742c696050b0b50344000f4500340580e550703480040488821001000b292010880031503141d245607403002400040000541c0c04002035100c080f03000c02d10b4103140c4002541940100410b012841c450300140140c4845420000d0600c0c140c27000040054000b6001180b4120001c200042400400d0041c0745601d1015120700018010340400200038010340903001c3c06021001c0081020081d060044074480c03600200a0260880c80507401410203502d849030341c0c0000d040440216031440c143c0300340c0032080ea42c540c6034814002c8954603504503800c600c902caa819580d8203000f202040050049510030022804c0040c0d40303104600c0050072081164118501482d8421015449071400004035a11004000001c20f06550b9a0001c0006021160040e1043e4080440000704041d00100074200b501c0d2408280d03841c4400744025809800c0c8121010046140d4890101c1c1d611100c590fa4000403c034111035400c2061384588480003030f40d01c103a8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 256950782 1250 256949532 256949549
    0x207090906090b0f0405030306061b061e0a020307080106080406150b0d060f0b030c0913090c0302130b0102070501050d02160f020411030c030606090406030b04120e0607081b07050901 80
    0x80e40c0c604008003100f0882d8040c4c10f60707401c940c440c00d2680302c255880c040184810700903900000c461141d04030741c0b0040c40b00d800d80402210740d00d1800281141c03d0481c1c950207410b81c04124400308400c041c2600a0700e110b40a1036880c1021031b0303e400411104190090410b07240d4a682d40c42a65020021800398030140c000c0c05986590307003090750144002c0b0744c580d5128901c0c0102403103040c4030384021442141d0f00007190103100b545801c200d00001d10b40801c500c801c011142d162050090820000f0030b040c404a034000c4031004a12181e840e152800d4031040d004450040c0c0084105005642c054000b400c0c01011741040182081c4119280c0c00070f00d034038218141c0c0c004040c81c0980c011032615000306816030061003c4c403403c41c10030f1412a015070001610080c07040a021420166503162684014010f6400501c200f0507401c1c54101150703980340a221100c00500070148144860405034216019507034806021460321036044001d144040100d400b86403c0c0c082d109000401d0b0780c0741120340c5d010b0071aa1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 256952032 1250 256950782 256950791
    0xc0503010504060e06072309120d020706021005151201111606060f03120507020d060603080306130e120d0209150c0712030801031103100216020306060d020d030f0207090906 76
    0x6900760b4a0b0150040091040203c1d080c284d80465072000d03060b440111f881c0c8200c135107403504200090491a00310a40c80301e01d1041c1980e128065900003082c108662a5400ba03138040d46022005034152031086a0400c01c0810380c10300c4111030304042031380e100a15950b600000b10b41d10600e00a600a6100100d001c09180c2c2d0b050780c4c2000d00c1010300c01d20004100c00311007c58183d20b10303500c100489007100c001c0414400b0210301d05096480c2da10b1074405940d800f8200f088560381300c3c50f10b0155504241c5505000c1c552601e0020140c44040c1310781040081c3c04402480c0c1f114501da81c0c902950311543c0c50041d480d40030311600c599620f0764028207482c00142d1003540d0716810b2280c905c501d003802981c044040d51200100640119801594043c1500c0e0000e200001030b1031900301007460070820300d42d0180c0b65840010404010a4441059000c1e00d10071426984a502c8440800c20392140e505000780d07010b401609042c0011b4010b0240000c1c84442d801941c1000c0c2d40d621040c4112804140c0680798140c44 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 256953282 1250 256952032 256952051
    0x9040f0c080a032007052107090519060807090b0a0302090c09240306042d0b03010b0a08190219031b080a030e01080601050d1a03060c250c050301050406 67
    0x3103165210090a07522000703140d203508169407a900e04046c410b090141c1194011400320189515010400c48103c00881d0203c40d0b59280c44402000c0c12510064195007000c031090360000c980c0036400440f00d02e88001d04070641060010b0000701041c12400364004040030740040180c441104581c46102e0800015071192180c0e030a100c01090030000100041054691007280101c0c08000c1d03035000030056600203002c120310b54140c40110569141d24504000c9412401082c40c01604042c1c44d00505038024003440141e1310510081e00d081d4021200f0743d420007844280040130303d200c012413483c0000c101c11032031003002c000c46911003c250401e640b5410846c080303816140100146900429502004004110759034074001d11021994052604000480f804554580c1c411400c1d1404021400305c00c101c011010002100100121a0501d00a000e030900254128066006503030204501d40304500d01110409002c1d202442c10301812501d403985d000012403291424881e4911583c412039000070b000e1034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 256954532 1250 256953282 256953287
    0x15130e0703050c100207122301091b0501050702040207020d0b0a0b011d0f011107051c050d03060501120203130f0b073f020f0f0a030c0302070b0609040f0c080a03 71
    0x100f01103030a000e007040d40b00346002c4d181d0015520049481c18103a070181c0d083c03a0318042d940702d064615001000240d544181c102080c0642c80a100b09110300d0100d407503640340e013a51116014107407140501084050041d80c0240c01d01d50003c00d90184020417540b010a0030356260b40e048401924103013011640d4010340095560400c0910a80c05004c40780302d940011680c0024000100d0341240c1810480c80345a1041695000c000c2174020700030091880b50941200411380124010100f4242c40130b1180c090350280c040d01034410502a500103075950856588160b20540c00303540093f10018405903200d44010102c0c0e05200720308102031040850b0a01d509083c1c8000340040e1200000b03117004007250740380482041040e0b003120490100d210702c40303038241e80568030382000740504141b14811600001d48c07240700195420003030000a00d0303070300d04001a00d0340c400c040f0220700030756500400e40c4881070007056492901050581c0d125200d0740360340408100039a00c0308400c15155002c01c025900c415180c2c0c08058 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 256955782 1250 256954532 256954543
    0x1060b0708180301020f0d020a03141509010e13030c0f080313060b040b130903020a0c0306020c120309100e0a02131d010203310f0803010f080c010815130e070305 71
    0xc4220f00039401c007240784201c041c030b0b407048950545406900103101200340e401394111503880c90802d02c041249203070250205982148003420207108520b03400020a071401b803018894001c088003900c20176408101d54080c2d920060206003511030501a408901c000343c050002584990b07400082c1560000c003074586402614000c034100341c41a410f0540854944e10760880a010b00015000b01240c141c0e42410141d0a140555034082d08511001c0303004006c2c03085075002080c4007020381d4111400e811007070318403041c0e9001c190761040030750700940d81d5001907210301c1e00a504410103890581c1c803000702e540d0008000c0d07030003592500392481e05c589000c401450001c4941c04104004002545036103042c1501c42005840c040d12580802d410b481010082e44031041401050ba070700007009004801c403400d015603684c00c00d10490880c0301e4203280100b072900000c100c2c80b05601c011784072002c598580e40d8003201003051020050390004140d81c180103145440b80101a00703d840040945011800c50800b0341c2880c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 256957032 1250 256955782 256955827
    0x10e040209030c060f0c070b03070801050a030b0c0d1b0903030e0d03050304150b1009090501060c081206010e100309021503060a0e09011119080610050a080901060b0708 74
    0x440c03060000389882d4501140c803104038002224045d543d68841d81d031203680c5010344900b00241d0300c070360b11000c6281d04002c8004c4d8020400d54490350203903030b41c0c0d80410001441c6c5000003440d500c0100080340c495030b1080054080904005000300d040070031540d29609000000312138800003004034000704281504101e564001120503a80150340f1161510098000c1c032010700010302c5148100914004243d4950011042e003a004003440d681400c158030080002045005844401c0d182000000e90203025248e0109400e07031110826041ca882d01c1c0c070b142ca83c0c40c00100080e040c482c54a969540503520b060184400009507100000c100e500ba0051080c0c00d800c00d444909820410070501045580c2e82c1c51140c00c42e203c1910b06038566a0300a00d4a0151410034420030001a02203140c134400d04003014090007115444c0d1b0b5600a56544d13404100a89191031540e10100d9420004209214070803c510b0740d2010342800041070003603803001c16444940c40921305407246800443e00446a001d040c010764181c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 256958282 1250 256957032 256957039
    0x40206091f09210312020d11041401021f09111011070506160f030306090203161b080a0e03150702010e0601080304060e040f090219050f0a0e06010507030c05030a020c010e 75
    0x4441e1260022100f2012040000d400e2102c0030010740381c82001c40d01290030400702c00314203208511040e039100c03000c0e405c540225044030442c1da000314a0303544002250401e40c001e41c40b010184103507082c0901c00038000d658007070700d86031228840b010141d1a2180d0205c0560103641d22070781d2859030716480d40d082c0b003420b4001c1380c4951000c100c010450b94481350b08140b11500485011000c00443c5001d80080a040c0d1258001500100420007000f8803038014950045c440d0b114103404006040103481d41103480c1c00020000341e81401100314075403180e420000b1041c1c024040725103820348401d034209030000846044005070346a801d55440c0c05028000c02d0b0040440c40d00450401b07007000d20140c02e0305003c90085014075a110300c50300305400a5003044826580282014080070184c10100d01e00c950709000c0d1501400c01c00c1c0040c46181410184101141c2800b041290a07845520046500354800d5009034208202c41c0558004503209000500407640d45400034400a4040d50001d440070030f940d01110710 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 256959532 1250 256958282 256958309
    0x60901180c030303110c1207030305010e06130e0304090e030a030e030c070b03070e180a06050d17030705090a0603140a05190921030209120606011205040206091f09 72
    0x8044070886029a80d060401140242c40e00380114518020301d80c081003188511a048050842200000e21440380203640602c8140c1c0c86074511000d058040e0360729508070403911001001d030f02081c0e103c0552020800140d81c540303950344649005950074401c121050303403c000340710301724a60140301c1c0c0301d04002800040c40c140010128904d458108600c1840d80342400000020031031441140318440300b46004201d54108404050f40c00d2021500b02e81c0e40c600107152090204482c90941140320550b1741c0700013a65110b1000a80980c1540c00140c2420140b0109100b90105940e610b500c4401504060360006429401d0190000002d440070b0521100381e490181840b00d80a28070300c480d14501407021020031917190b0707442c0000100d00c1c2c015100d85103941101c0116000f82e4141c008055002c0100c4842d0b000405080b07000d51503590965109001c18001c0c280c610800606030811940540020041400d0503501c00101d2000000034181c0c0301e841c03880880e900345464001c105800982015110b41a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 256960782 1250 256959532 256959581
    0x608010c121d060c03090c100807032703050f04090e0604150504020f011b05070906140f010e010c06020c06040606030b0718060e1906021c050a02120706090212060901 73
    0x40d00e91001520100016200000050486e03004114495400700003900300d1508030746030040100010b006482d2880020f09007010001c4800034542d210000d00701c0c2507800070381384c1030b15541a0741c650701202c10700011110034000059407041c2485804a00d58003880545a1840c00d4038202c0305a00c10100c848400340e1030003041c4005610744080c4412026400c0c02c0240c4495100400c5055821211000524038469282e0101761031103290000c400301c0b40c035604820008040c5408200f00030f0550700300315002400240240c034166115404205049015210062800c03888543c03490505204071015146e560300c840c1c04201700b10020b00c0150f4459a41e18120141d451290085451481d0f03a2040344208200191079020030396800b044611502007185004500b0f6507100d01c0607465100d4004105010b094403040017840da8010000c6400c02c0d6032075400341420b40340200384021035401c00380059404c50361355408400181c451189030101c064581c802003a0528002c1040d03425105068142c40d01d03010f41d402e002c3c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 256962032 1250 256960782 256960841
    0x171002070c14030a1202011a030a0f0803070c060608010501050a091e050901020904050133050301050d0f02040504061d011404020904050f0615030d110a060903030608010c12 76
    0x81c0d0a8490400300c0300d1400090301e00003803400507001c001400704c444140c58180c610b0f405521800703154414542040c4010034070000c05454a52601003d41200381403500c04000a030700c00c00655101049040c2001680c04070303116074040381e1507900403400aa42d0b0b58018422481c10002040c024000c3c01d0051080120401041644001203105441e000b43c4440100344841020b405580c48500094401c01c01580d640700e0b0b41e940400c039446581d44080010110441282031049801524580c070307103510f0b146034a8078040c000c011041c080705840284440c8078041c0141d450b401428000c0d800f035a408546801c2a00002c084244500080002a032400c0541d400f4201410003180d4480d030110b505500c65a1345040c040c1c1031288540c0caa295030f010b04001c101c1301c0c1001000b0101c1c40d90058045584d50400002d054912071403004c502032141e840340c50404000351090b08020740c030a200745004104070342d40e85101400d5400e40015000810203071100f4080310403440c4140c1050603018013813a552714003011841c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 256963282 1250 256962032 256962053
    0x1b0d02030c15130f08091207150315030f1e0303021e1c09020a080304030c0603050c120103110310022a0c090106140403120503180d020309010c1b17100207 68
    0x207080c1500e494428007402801d50070f440080201600380c418103040e0404c8035403250314a00401c00c80c13005030360f0500074031840bd2040f07401c00300c030070f11106400c00d0030344d104d5102c00406040d0440b0304013045042552401c008603003040300e445c42034a0150712000042c40d120905070003900c0e2020606d1041c03141c81b0540500c044442e120909155000031802410300205010303074038542040c40343e884000350010810405503003040032a012a43d0400140d2034000c00c3c041203205403e10807500034209001407020031001d60410a40c00c0c0e0060841d490000c0b9190f040c2c0c2681c002c4c5501c1180820001401801e010101d06031401d52036088028181407801000011904034041c020301d400c01409822049036110004129005141c12018210f5400388000c00248241d02c00c030703800f40040c41800306410300c5000001c1c007500061203c2e0040c41c1096404401110001c6030b003001920782ca0040e134010034003140320034070000141c0a501502501001c43c41440340c83c00016203810340754203204001550204840c3c007803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 256964532 1250 256963282 256963321
    0x51225080618071d04060911070210031a060318070806071b05030d02030c070f080a1e0905131409030304140601060e0d030306080613110111030306061b0d02030c15 72
    0x244c42c010240c40380400c00a04a5401c00300c0024541600c074500031181d10042d224440c0300304c0b800d240741d50800c6022000d6440801c6102d0110100018002c020700c1e000c0042e40d800f9600e403135400702c841482c0840614000c0c1c2a403003200c49030050428010b0032580720340c00d60541444484000b4a4070010394400d41d59204010b645071400b5408408240c601d02000c1c100d0342c3d9190400c8100016400358240050207a102605600204010070746445011002651130241c021a646508040601c1e107428404140841d0882661442c1c1d00c2c00c00c5a0380640c1030345454050105000116240d01d407500e84a145600e50b5540500c0580c003200041018030781c880581c030000074007503e51801c040124902a405000302d60001d014a000c3c0b002044280704102c0610902c1c0e600901e15900c844420380015600415030321041c40b416001000040c4060801c1030050050700b00041442d4008503110000784d0905288050b52070041c0c000207206040d00008100712144a98004090b40c02402e002d80303408041000c655 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 256965782 1250 256964532 256964567
    0x80301090b03031314030c040902010206130615230103090c03120203130e0415181403070b04050f07061403070f111212090703020105122508061807 65
    0x4620300d41d41c1c4040c8190b03480209080c80700c101c1140c0382c1107500d000c21403508003180248501b209002c182e2825001e20320703825806030080c2c8842d40300e1001268a40000350001e40300c10340c0350300f240c2103a01c0c010310780c0000030840004d8101d003444039829003004500d1036001e42070425042081c00700c0400c55580070101140d600c0300c559060700c02c281c0c1042c2c0c11030041c01401c08180b802c046000421200c4074206922641c8500130030704020419a03002d07000ca0305001d0a80d9100c811603a40100010a001c2603200c40041d417104a03814582035640d40e01c0c50100c111022203240d0003814000c01e40500410880b0068199030402c40b0208541c2c2c41d0103c0e407808001d10550810003a02c03c403c20882c02413000b070301110304c040d0644044508a0310001031682c0041481288a03800c0c8000946a20340810f00e0703820b49505940315071802c4c4e590601801c210401900361203e4480d100041f41540168150350320b1420110740340e1844600d0b0000c01c2007180b012040440803112001c10070418802c1d4007844e05000e0582c0007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 256967032 1250 256965782 256965791
    0x1240506030a0f0614030f01050705030a02090a03050d0314090a02030d0f050d091b060e06040302040b0111101d0d0807081302030a0501020c061b0a1b02041b0e01020a08030109 77
    0x2002d48201a000c5020b010b80180c0c40d220021a45c3d541e11182c60400341019000c80d584169241c4100e03080f12011101000051800d1010a650b00c80781c1e00249224080281950b95036a2a601c035541026102d80d08100441e5441c44c07000021420011303042d0f84800c002c3c000e030128000c65000b0a482da40c241e0f107a10100004c00032650b910354040c00680f2100703039082c81d0410400c1d540d89410a0b90342004001d9000360220b50000146040c82102e901e50450009400282010301e59806d002c0548030001c3c6180c140015a0104c0c4142c1d1030030000c2128600c0b1510010072030340d076070100441c505050544181d910b5048580007006903030300618402c2c1c002810345015612640c1c0c5050b42220754000c28002036040c0150101c42050100540103405100c8444050f103126807a0142e08072030b0701c640c46107107614910003400311900550040c84c4040042805045446042c40c10354005411038540d1080c50304e0303a50307810070310001c0341e60721541224040c2c20a00062075000ca660b00c5d10502400144501072909445 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 256968282 1250 256967032 256967041
    0x31c09030221030a0c050606030307050c0f0612070221041d0a15031113060612020304060f090f2006040b0903070305010e06010303020111040506040e070207081209030124050603 78
    0x142c41c0e038074038a41e01260540362194501403008203110f800396006d80b4984503c00c086801850017008441545501000030701c0c0e5070cc100400c0c0003640d0b02c000340450744003205112540f46500c00c00099445488150301070944034200c00040141c0440c0c2101000103103d081c0001c0c42a0170031040c8030303160784808001540c1e03640d840310440000380c42203002c0b024040204410020410005100017940250116800d84c1c01c40000c03080ba1040301c4071446004000b07082021001c0410406500131600039000303440100300b071880150800c0c11b8640c0100c0c1100d05000c20001d10f0f0910171440780700601224181414106d0390344000000d10b040c0518003a600004100040c0d0010340d95040002e40b0045a01c2402802507424407400503854003400d11003034001d035003415002c103149002e2a0844042c1c8400404460403e410014020032019000f4900c0095128080001c02c0045040049006070003115121607503074a00d40c02891700351040039000803002c000010701100058465100d150540d10b0903100d1360f86070fa58 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 256969532 1250 256968282 256968319
    0x10b1209120406020109020906041a150702030105010303051c14010603180b0a02030402120102120a0222090e0c040905030708070201051e0d050c0c0d080702030903060a0209031c090302 81
    0x710042266085800100003685980640081004a0003160f9403440c0e175688406000a45d100508180801c110f01c00803924a850440c03030381030250302c018001c07504044a56012908480d42a0004c2c3d02184011030010070a102014034100c81c0741ca1a00c050003941026180c000d54a40107014510030315071140030000003008013240803020150000005207081c03c200c0c0400c030084d40f041e03600360f005044031007092080e100140212494400312101c030903850380d0b0700340301070000390444a8020481141e03159901c01c111601d0a200e4003410035541c001414004a440c801d03d0244980b00c0503000d0703420403200e2808038402100384c1e1845034109000903919481440121128807031500c107161080825001508d41c1804d02c8084e101c00c1c994004100519120f03000d24440f10b001d000905c101941c82980c40710b029038031410401e5080703034850044a080000100020341070003011215280701c00e0780401c0c01c2e01c1500d400c002203041d41c1d80c1001010580001108000c060b03150b40d0201901500e615294881c0104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 256970782 1250 256969532 256969543
    0x20903060403110f0124050910030201030923010c1101110712111603021005070206090f13020711091003080a05090307050d0503030702280312090b07090f0b03010b1209 74
    0x106820020808810111b84920854010300070130030400910036004030356401c000e000a40034402035136041c1d40d02c40c6150b00450241c100b5520407a4000c10850f00340052490444030319908c0030b17103280042110320403c0c800030000550303139a60082d03581c102440d5180c1000740307204a540c07041c0c000c04000c032900160207040d41c0c40c0d00803000b03103a4148240300c85c5004d40011000c422080c0c4c2c0c4204c80c0c15503003641d616011180b40c00b4520001c1e510450401a080e12890840b00130148400c000e0a02642040d0005511040f80c00030a41035031203c444030805207041c6410100035910544042c40b070143c060941d203680300c80c0d01602c0014814007800080614141d5010000310b402018010000320402c40766280a0340c4940040c0c40c1c210241c03180c03c00b8502c40d400800c0309540e0071644090700503020704441e1000c0f03910034901c106d450002503648041c2c4021448a281c110720880c2640c84200500d80341038144001a0065800303803c68a05c2840140a114006000c0b00c018501c440c500302e06c50b44802c008281001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 256972032 1250 256970782 256970803
    0x306010605030f010602030a1e02070803030106050702031e0a08070317040f061a010e060f070f080301150e06030f070509040f24050906012001050a0515030102090306040311 76
    0x5114440000515660220086109011900c030414840c0d80c2c032842644c1c0d0740141c10f4404c0215078550606a04101c02103040901000c061045036001aa2906000d003554000e070400000604000750100c25414100f058140d035030500c503980c1100c0130074804000e49072100954014407200b000500c0d40c1c03c1c10b1003480002c0c80c0403900b0b0004005804c0502d000900003120503022070351141003200c001c6e00441200e01c008822041030b1a0903420a103800b04100b084d030300c440700c040c2076207505200070000700d511200c4000780c1d54482c0060543ea541020f22101c50b5411410422003041022041420540c482030146c0c1d400c41c250107a00c66640c0c85402d01039480d4000d414036180c1291900c070089034903081d5078106080e140c0704440c228040c48011146141e03080914041c154114823400085401ca51103000d0701d60281c3d1411072080100c605041d444d80c00d4800995121110644460900004602603404a6030903c001c40c0210324101544003c29141d00000b0720190901c02d5451440300e20280610061012 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 256973282 1250 256972032 256972039
    0x71403030c190c14090402150408251a1602120607080a050723090f060c0102030709060318170f070605011401140409051e151306060e04090c05 63
    0x710360700700b91004035a071400300c81565040c0303e4000000d03410300420f0303003240482009003540000b43d480d5000d00c0720840250a1b0345003012010440040c0e0040c05100f040c003a07402d801404281c040c060080f149000400d508212800120b4030600c044407007400b400c490800d491510180002880341c000100c1c280015010b00d451801503500304040c2c244d105051510440541a0402507034860000454041184461030802c00c003e402d598945200c504001e801c812400030b25555004017150301141140d0030242000f11a6034010080c44542074000000c00042c117200c3c039042141d200d0207200c41807101603502c00900341c4002202e0141c907020004c01203540c03070300c4554442a919601c61600b075000b04000d10581e40394500c3e110a443da550300c01c10281c0c60483c2000d022506044c10851410002d01c0301800340c06441e6400c680ca0580380000505451140d031400c030380d542c40d1071103100500c101010040307016101286086021b110907900152a00982a019100040ca248662404024401d425000b4590 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 256974532 1250 256973282 256973293
    0x71d0a05010f140625060609020c1b040605060c060412020105060a060c050109060203130312021222020a14040e0a0b130606030c0b09150a0903080c2526071403030c 72
    0x100c02085c101c1080389403042004004003581d964058089018004440265401c1003640d03500b680c00000350401c1a1800910000d00786039614002541a4441c80340c4a0140e0000c0040009000b5a000a07000c1c7d0071860009005514044000841070803442c0500380c28040510710650501200754401c486281d40803200b103660b0f0421200220404030510f0048001a0905d54218060513041c0223440100c0d1010860094903241c9610404a41d980d00d00c4a02c55480441d441d40096030b076a5034000018045200c0c00d40206e401d6400340416225200e80210b013a9100c8040200094840001554094020032441e074070701c3c801e4900038014110030340c4003405603422401d01190900042000b48019002110350a90344884120829654040e503800500803c010010070004501e80030000c00031544001c0685e050185006100c14420310300348503070418220035000038004002d030100764182ca0251400c6a01d00f490152038003690f00c0c141030007981c03800794102c04109041c2e1000c1080e10030012482050380c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 256975782 1250 256974532 256974577
    0xa020f07090614150405060306240a0906050901090e3303070519030818030a0506012607051908071401080a0903020a0b0711071d0a05010f1406 63
    0x2030190482d4020030200810080c0b040c40c05290040c002944c0b000300ca1100350501d0725180402c5000c2e00020440e9400000c003c2c0c3c1e1038100d580584011554034440d100705600e60910180003429664507402003403d1283c20040d0038a00c1e078101d1250011501c001c0684140ba0ba18441c1c2c42c0d11601c4074a207038501407194502c2c2d40700b01c1e1018400c03101c2004425421524250750f164100502a03503040100704800c5185c407400d10105039288010070030b14400e90002d010b20f90751000030a06e004008074055807141c1101006010036290701002c0d4140d0300201c10b4409040e002e00303d0851b180d0720a88034a0b8801d803e0701b1001e0f0545000400444003e0080e5000c0c1c50100b684c80140b1410030714122912030000703030900001007ca060622a0307640b000d4141e8014000010182c3d030381941c0c100d01900200030320800c4c000d103403000b0f102000950054541c0408010100543c1032030103005e0407014000d1064a030030b16005000302e002c429001f000b141c0d0304031031406040003240301049aa03c1601d8100718114101c08440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 256977032 1250 256975782 256975799
    0xa0506190306170a111c030e040b090901051005031f090c030f0b01060207060f08040803041a07020a060e07030f080f0d020a030e0d0906080612150103030c03080106080c030109020a020f07 82
    0x186180b03170007860304652400704207041010a0f10120075071100780e004d02c240c0601007441461400b6080c1f001410000e05500c0000c00545103602c1105c06130016034561003002014001c07801034000909090b0001e01809a8000604850020f08c040002d130580c4d58241c1d550512503003400d5240295081020040006074a00304411101000d0203803001520030500e00049580c428000000c1140c215615450a84c0352342d5681056540043e00c2520088454102da480b18111208498050314141d0000c084182c064035241702a0b500301d0000104d5500440410804100c002c84e04030301d16a40a2101c42d80c542d02c070000c6600c140102d071145890544003044a90f0616010307404481c2c428460012103200007102c05c400c541c2c5918502410000400440101d0103038100403002c9200780e80ca0409856401d070a81e10140410078090340160300007080c03803c610081c541c11072030103030242220740303407100c0d0510b490b100e10a0a4441889a1070b0181d50000c6e0050b810340c402c0c4250014211070100b5101d80680d00c9050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 256978282 1250 256977032 256977043
    0x90602180901080a02030325020a0b031012080415050d050f060f0301091a07020703080708070215030f07200d170c0c0a11010e0603010306060e060a050619030617 71
    0x1e0041048800124040c01c0010300d04401d41d40c000d00641c0f4040d00900341160b4120180451400c142d06401080016595508040e001c2c0003042c51054891800d07103010b00d800705107039100e41c1c0064640c00c40840441c82200859098030221a4687d03000040c3d01000c840a1003072a000c0e1a89034600400d2115034085183c4880c010707070081341c1800d070219010b01090300701c7c2e00030702d07000384103000a0751728411a901881d0159841551030068034021b681d00d844400050303200c0c034402c80340e0b41c80000c1c01504600d80340d6145038000c050007039a42d00b10f1030000d040003642c00e005001003003400480244010f1940e211002141c101c0810380c151031900c00c0080f03001e06041102c000d1181c000b00d14070b00144100c4070b01015142e0810070b078001002d039003065856100c400b410301c4c0b588074104040880c644000b604c43c20300850013140b02d000c000a07110703c0c10070745400c0d59070050501441804044020005030f580c00065483e5442c4034004058003108043c01036005001c180d10001c180501e0440d00c41054102048 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 256979532 1250 256978282 256978327
    0x8100b0102120d05060306070e01020613020a0b04030b0a051806191b02060a0e030915070f060203250801181503020310090606080d0917070506070827060904020706090602 75
    0x101c52050300c0d20300c0240d5101c070840c9d0105005038001c1000440001c69100840404e500107049039000c241c0340ea1080302658055001030781d01111500904c9000d0090384507650b030200a640b035001850102826840e103506025019410440d00104c0940c2e190042c4e03400f002000301c1d15141e00b421440c040901135140c120480310411003a10340028801d007180003000302e50361690014a0810f45a0054180c025a60030010341030b00c0700c2d05140c44c04000113000748021400381207140e09042150b28a8a0b20840c008010200b040070850340d40010017140c1071181c1c000e1424481880d02044076006c2d03040c0025604400d51000e5414806c0c3d40c1d1644a42d40f266003c1216140212804e0290540f507050556449e0020740e50f2000044c2140410401a0560000c0c085094800016150025074030030000e138560700018415500d00500003142110300b20000c100c05c121030110402c46160522040c00201280160303402c040c000c03600022004100103c0354020204190301803030454448944140c0d02d69104031101c07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 256980782 1250 256979532 256979539
    0x2003160e07090b0a0f0210022208030a08061e0301090b18060103080f0f160b01060f080906011a040909060203040b0c1c0213050603070810060908100b0102120d0506 72
    0xc04124914030801d6401c2c155440d001c8403502e40910305070211040500c00c0b0b039000c1180281075000210425600040c400180c40d4010382c4265000c0f400e40060404041d40302201c01e07407042003502c1c22103800c00c020a45c810800c0780c165602207052403540441c00307101c030542603265103080d69000070407400c94441402030040400f0841161603d440840e9200e00a010142842030184881940001004020301500f20350000c81e40c2440c51080e20404991200c04046545020707050042c00045d40c01501d006014019140c120550b05124a001e40c41c0c4006004500020315000d2001c901644c8a0084400070090b030541004035100306d0a10708001d4000f40c9046640920000c0400c048540c2d94096950304c0c01c00320145130440301c100d19042d000303503c0300e540201200000440041c03103030368080c05584503210984814070f091400d411303070340d14189080d013000d0240004548284a442400580e1048001e03105c0c2001031084040c00c010b0f4030f00600c000d1419003009000481240c481c0c0e842c0c111078001c26094 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 256982032 1250 256980782 256980809
    0xe040c0f05060906030a0203040309080a060209090a0c1b1b06050c070e0c041403010b0d110102161401080a0b0306042f0d06050a0b030d090509130c03200316 69
    0x5508000782c511518a005920000600214255400c0366006680180c880d0500801403a0341e0000903090200005007681c0c41380d4086484505410304402c402d40c0710740849001c2001c83c0c9558006004082e65200c40200c450340102c10710200600d00e01c402502800c0d05402c0000301d980c6210080007a0301c400b502c1481c500400d00c000406400c1340201c035000b02854074205042c40d040052120340001d2250f40d6aa16648a03041d40d1441c0e280d040d903002c2258091960a000f08039250f00182c50081c81c4040d01c070391015401380400c04083c4960710102458000d107070154807501c949410002400042e000c1da0f038103000e1315081c04200045500c01d041c000207240440d949400208000d1078681c1c800d50b80042e00722025001d000d0020303125500c01d541c8801d503c400065103c42c1ca030086842e04001078035810100c0c5801e881803003030385880100150702070b02c2d01c0c1c2d5070001c010903990744800301d2103a844028013407030410000e0820306000c100f0210156901600f101c62100f100c0b0b00c41501c0c230304070344113515111011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 256983282 1250 256982032 256982039
    0x7140109060627060b09101202130e100501120c0e0406060503010302031011030a2315150304051c0207170a0b01050d05070e070c06020705010e2a190e040c0f 69
    0x25030044c0400c0319424020300303007010b4924092028256041c04c9900401003a05040c80a480e1540b0103001405002400a091241000564800f408003e445d45110f10300405040025aa20641580e0107a20040004c60410384080b801e440c0a00041d03200d0758480d08005010030125031110103581228002c03400c032044211840d41e04070440340c0c280d401c000c10007010400104c0c0b598182e0881d51001042c1d0208042c00d86021441c18213101d0b09403080030200a040904010741d22303000400c428005803d4900b5881d41c1081e540302a91851882c581301d416420444481920030b000703021900003000b02c0308150382c0c01c6800c220303416201c140942080395181c118400100e0542001030740c0e581e09a9000c0d0003010902d003001000312a865000740b000040000031526800041c0190003c0d02d0900d200b4400401ca07820380452280c10070125041d4010b5403a01800e00c8403101000c0c41844140b20b40c03e440d40c0300703810308046400200d01d942c1e400ca0320010080005000c2001119440d039001c440c800c2c08885d803582d45 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 256984532 1250 256983282 256983359
    0x70f0609090629131d040b07050711060f0c0607080108070501090f14030304080f060601020d0815150906210108060709180b0411030402012a081c09030504030b07090506071401090606 80
    0x1441001400bd1408086107140e00d08005004105a1840000b01030508040d54200e40c0390000c00c85910002581800040100200401100001e04002d003070011000d1304001c1d80c11009045440780c0030349050311401c0072516403014000c41e0043c00350b200a550440181c21000c0365100c00551b2a540103214a080e4280e555200e2030000380592004a0300358034010813a402c0001901500903031084030322040003100392a5071000d00030402c0c049d100c0c49010121800034000254044164040c1030786820210400581d030340e00050070000c0c3ca88101e90020300f0244080076000900c40c008101b90090f207007441d0708162121003c080d5108501c00d030385011300c1c0400242076160844584607204800d112000c1180c00084800b00076150807000c41d14281c141d18442c04140c01550380507541640821030020701071091045050b0000c0d0300c000c4070f060440c1114a0300c0045180c604c00c0341406170890b0712054101e070011500703411850b101500301c078080c000c1d26285e984900d1042100c91f900104040e24200c00202c50070b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 256985782 1250 256984532 256984537
    0x603080307091d0601050a271806050d0201050c0c03011a040e0c0102190218010906030b0c03060105070f05011d0f0114090d08060102070f0609090629131d040b0705 72
    0x80307624121240d1a802e00640c0c00c0e4201c1c96a1400380030f103d01c810620340d214043c818642e010341039100641340d45410409e0b440c1118200c4036010650a0100502c041c0d00c803810318160040e07081c80d1841d55024180304140c10180d140925607419401c1800112003030340d24950188001710100d0341040000300e8241c60650380e00c2c02402c0300d40541c00562004610111401403059121700260000e540458501641302c07510384260041c180180c2c0e41c0d1024814420316007942d40d80000c0400c01c040c654145400080d0040c00b070881c2c01000701d03902005420802000b900503086c080c04560541c041c00064031200d68445030800181c2c000d9610b4000c0c2d030407602c0c040f603098a01410104001d004c001d00d0b0170350200c0e00034100414807415840b41d803000103000c1a000c4014001000700c4d55500c0002030505000d001a0350955014030005140740070046400080f4070000316500c120590b01c2540c401d90f19903440295802580803540401c130b0300703c005000d040880d0f88039200d1441101c0c4150a9503800c4000d403900d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 256987032 1250 256985782 256985819
    0x605120a0b0f0a06180f0b010c0f080f0c010e0c0111070f030204020703050903030c060901140708310c0504060b04030c03030507111f0206100b12061201060308030709 73
    0x70700920042035004412590b401d0700024000750110320581c032181c00c290f42c0e101c0ca06079018040c0e035038884000700100510480c00c5101d1309181c032800c11410342e01c900342220100b51000e041d403400014812981d0000104840b0060074000003407184802c8149100c0d121591554080c0c0400e0725101c08051040307022684500741d40792640d03031750400ca0850302070000a4100003002c17070500c041005040890b541c1080503205c0c82ea0b414008121a15000342c840b802c2d15640384008400f02e0440091156841d0070404003903200100c04146013001880700c4002c1d00040701d8500c15080c280b401c40000091201041d80002074801c25101444465a1000c48181c0c6108038400a401002880400d0001030711031030061400d20302618101c86074801c00700008501000040010540b25916851145056014000550b00800346401c40940c14502408180d2a1250120880b41204894006800c0b680c400e241ca215006a6600801840e912860013190f07551081d600980407400400000410320a20a91503e01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 256988282 1250 256987032 256987043
    0x30203070906030b0f0a0e01030519030c0f0218070306030501140907231504060201290f030f060a02040501080109060f0302210109030206011701050919020111010e010605120a 77
    0x3903403034008214014040b0052065200e0002c10403840316940780c406c0c0801516180500407015403643c43d2007032824080380c000c8110718096460500c0460340049203049503503000f243d140004003032413000842c0404c03802c2404803840c912001b80b08103980e240d072041003a644a0002004510b1840b0180400760300c0848608409a00c00030040c0116500f400300b00e00c10052401c1d1903012891540000361584144a0118205140200c6c0400c00f003642401118070310418031f428101e0203840c00741460491452220802e005c1d542006880d41551800c01603c00c0301e42e03c0c1c1040d5145070420341442c00195002c2e22406001486000000c160381d4294810302040f90301440041035070b50b00d15800e008407220f18655035900c58441d2064001024820302172812110300c87c0c0e0241107150304128005030301c0e041c0d8107140c564981c984401c102881c0340c0000c020100d801070081a41505d1120710040313440c40000d200340384c81035080015948210805400500503100111040e0411801008280c2e58801000201619 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 256989532 1250 256988282 256988297
    0x120109060c0f0e0d17040e09010c0e1e090c0906121e0106210608030d0902090c0906160f0813060207090905060a0509010b15040e010f0305070e0a06030f0302030702040c03020307 78
    0x6095401000a0300c11001901800c141d92400d42d06407c40086030030f004507944488659000c594403449020001000301e445078107400d9509010a48200042c0c4000c1c003c1d9400400b00d40710001d003a05803140048014003d0303582d050b200c111000750050070f541da0155441e07015006868030031901507181c1610a195140300150400a12400d0503503172821072880c8040da16030020410290030701c024114201e0040001c41c140d819481404a1440000e24404d4088024441c2d21051380da03403002c80d4207503031a001c00034a1011743c41c20142140d02000c00001c01c2d40400150041c4c4485624082c842151096000d540c0010b60b40c101c40c0701668003c1100524a820140014900e00310641c0450b401132243c40001074084004804500003d0030092000400803003c40d040042e00b04d01a1010b000d0282050401002495a81c0e43d564031000c502800d1000c162400025610032140c2c2c5c8000010350704402007270b0a40728941170180d1258007100d01070703000d1030603e8039981c8624000d0088a005000e540c1d190300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 256990782 1250 256989532 256989559
    0x807021203070e0901060804030e030f030a0e0307090e0a03030606030b090621010e03090a090e030405150702060d09020306150a050f0d06050c220e04030c02120109060c0f0e 76
    0x1051507000420790003c1c0800c00d441c08006848808503680030b88425194072200d0300746400e01030001050030440601c41d0b4002c0980c880000d05c00310682e1306541d40d500340041d088000c0d000081c10030b01c81b9001070402c80d1030130b20002c0e044107000840407540340c0a81c03010032425881d04800c03002e0310350300b5012541025030301c2c0c0030460604044001101070b49106281130718500540b000c880c2035a0f002d0492803002d0780041204401850700d40e08410091480c030350104a901380c052041130f1240a41d118440c841c44035442c5800d040482101100c180329401414181d50b84000c62421005000d00082070703000f841210000380c1080b115000d03080c1520401008061954503000c100071020b0325829120350080c1141c02c1100c00920b150280e01c1c0189656a50680c4904800031380541401c9244171400328a4500b400800c000c8880c1c400d4075400540600d014100c0650031f00104e404800c444070009c01070740c6064440802d1180382d9001c80441c102c581e071040140c0f0b590610071615480e03060902548103282043d2003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 256992032 1250 256990782 256990813
    0x907062309150921070f080a11030a0c0602010c2012031504091a060907050904020f2205150a090e180f060901050a020a0c02100509030a03051207080702 67
    0xd909054800102038a0120100e0205294030f04e4422405040c0c1e01342c0b80314024404007444000b002c2c0900320381c0d414100c0d14208440b0390350001c81001621000302200b424800e91014000040342d079411910310446242c4d40e000003070081c100c641a8a0019214001c48501e820a04130045480b0640c10002c0ca04030442400e03180c200c4d400a0a400d20f44042e0400c2d40d9001d807910b0042d6030f03855000b40109000c1c6090f048a580021500810300c620500094042004058010060307078a0700130700390343c01078550152842c03400c40c5210341a441c030500038070702d4090031b00140107800039401c0e030300d00b6240d4850b0308031103c085854600a09d40c11001240d1503103001c4c440ca60901e21a03543c82000c0c2803d110100075071b03401d010b0621501005140d042c0d0801810005240800d00030950050b92240d402c40c68040d64400c010f0440041d03d030005d224403007071042070031050302c200c0c19149045401416a48a5000e501d005800381d071000f000350103488070b52000201000c0c000d45890303124461a40140040c8102003125 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 256993282 1250 256992032 256992049
    0x6010c0b060f0a0305010510080c030601030b04031403010305030901030608011104060503042d120215070804021318031404060c0f050a06140a14010506191202030907062309 76
    0x6031900021030440740b40c1c6559640c07086100444c080c600000c0d90f8140b1a0b1034042e118140e8104078515482004503641645002900604403504040c2008007500e03185070480301d0222000640c441c0a01c040004024010040001c107640c05090b02e0801c862035480b40e8031800eaa038a00c41003c502c0d0740c248003c0050038010703001540d20510940c0d0740ca1800c0198842c01e84580d11104001c00701c100b000310458104030030070042e5265030703016000600d8141451030400c1108640100303400304016005011504648032241d91072050b0280c180c0900048020089040490040403810740000e080e1401200d0f04012580072a070640c0c4180da541c610705007640d280d0504600c0c90b0001140c80744201c1098902007280c40c4211901410083c51451090600d1003050080d14152203683c4480001880104903c1da1010704866803860384d840c0240401091020640b0800307580c00d58010b043d40000100204100042030b090242c0300303247c07196052805501d000d00306410040a502c411050708004121061810000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 256994532 1250 256993282 256993291
    0xc030703110c0a0503030907090513030e2106063316150207141501090b13051611150402041a060a030603020f040e03121012050706030c0806010c0b 65
    0x504510b8000c00702c00c0070340780122a58082d6501d0b0030210a0003115201441101c008010388041802141401407140c2450004068000e05000350507a6010240c0c075910381c0c403203000300d2012198101880c1d459880c2d41714101220392a20a1091140c071a09000303080e4015001c1440084111280030f010110040013907001280800011044449813000682c5d65152100300c05041d100150311001c0030310f403903002d41095094905d03044c0c106210b0380420910381403010381103e200c03002c0825205404030200310182c5e40c40c02c100304450700b040d082114415280c500500301d03100c180c2d04c2c0b2040c003002903903564603507580c400b0f482e40f201c10050204015240c15044180400160042e403205425044005066a07010812910100384c43d94401c205519003079103041c959000030754007440314030108507820781c0700d1089041c9200d1002100c0041405108205a410b000c0d054000d450b13140c0c00700c1401e15a07529941440303020000780c28000075031000c078415102d00e406000181c44902d000075007955410b040c3c450061 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 256995782 1250 256994532 256994561
    0x612060909070e0702030d0606111507140c010605030606010306060212070813080f070b03150d050c06040b0c0f0703020a060f02010e0303010f03060501080a1721101403060c030703 79
    0x2200400c04880d0828014044c1c9002d0300107599541c56a00310a0944010380e100c2014007150811900e00714401007248060402c6031240d0301415035840c2e40541c0d480d00700a40c1307106404404500c81c030300050154029820341300c00320111003283d9a568011016581d1a0161000503084958044190f0254038003030041075200340c40c00f0742895201691207441c1001944041c8456110118082c1105818010304018281c0076020b240746242c0400720f02800c404840c070703550151501c101000144079007841065141980200340311780c0d85171358490300f450a402c8000707400418006c1c5103995003050b0000a0b18400c50f40c1c05401d000202e45040000d441d04a0150011410355403100120701c0d20840502c021070203045144444806141542082c03005c0b260160800b01c0c9a42c0070075101c0e000b048030030b01649102d2106413452aa102148243c0180041d542c0e100078004035180b40510003882c0c1000141000d0301c5406443d030104c81f10076410981d54440c1566101800c02c01040170640b86840782d003000e4030111079074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 256997032 1250 256995782 256995793
    0x6030307121e08160810050105090a08100212010e04050a020418020405010b0c070e0f06190308030103030903060506060901140903070506072102030a020706050d11160606050612060909 81
    0xb1440c00c0c41e003608071104900162240007004503a00c4290b101c040c0c0001207103000031881c60300403480c01005225024160603c48042540c070099074070814070002802e82301d01a0b86c0349480f40c1a00c0c40c082d4003c0c030311506041141e030002199030844840782a00c2180c0140003000c00c0308868007444014560104000d88140c1c45580080c050b0f165805400e000340358480302540e90359004001141840b60603044050b010304200d042c040c81041100d4035a4220100700d0700e00c0c5443c6031484c0782c2c00e00c4198541c001020004084000801e240d00a016182200e0145030180100c1d515001008000c0c441c030006c160105a000300c000749403240d680050554004043c00321005142c03141d00040481d000302404841c0c00001702c000341d0351800d400d04202000c0405000540c10104c101d08041c2d1905001c0c012441080741c0412844107032001501314641400021040c69602d04401507444241c2c2180c80041d24114103180b030024150038107208440da44146046202d031180c491800b00b2214040152140041e031042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 256998282 1250 256997032 256997057
    0xa0b0a1e0c0804050f0109021806030109140a02041506050d0b0a050a090b040b03010501050904081804020708070507150c020405091e0304080c01021615020a05070609090f050603030712 81
    0xd031044040380401620303000701034070301032410520704000048807940a0341403070507580040e220504400000000e1181c002c00076502c203408070b0b00401880070003400ca1900903180380d00500c8049041401c80b8002c0e90244101c01d94000001c2c1581024400c64000500410800507505178550288122000003096078241581e203d0002d04c02c064140c00c00c150340d556800f004495840c00d4070031001290700c150028481503241c00d002822290700184007034030443d000500d8048814124600700c10008006208541ba0754282c185045541c2001d03d04035200e00c103402012503901000c0c01c1d40c103039400c0e26a80700603444113681c0c280000f81c000900b040d1010310959100344c40c20001101848250640c1c880119101c1c1d113000c0f01549800c003505480c0341590084a455400d1210240b004015207500010180040003075041c1280b910b0040e860180c202c1c01883e2010882681c4040e031034048420901c4c05100080c0f034000780f802110001c4d61201d61582c41001440c0000f00121024000c4c24010700300700040c0303000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 256999532 1250 256998282 256998341
    0x70f020106030203011104060e1005040612140c0a030f0e10180501020d14010b0a120e24010602070603111806040e040f03120b0307031b0f0f080606030a0b0a 69
    0x800e0b990706c141e0858045070502c041940280060116002140e0121541e50170110240892142e80941c0040280500101800200603040140ca01010f640125014074203604102c80070703040b1034803640010b401c010400c0041c44940c0035041010341e0500180c041c0c08042070034403000340381da5a40c0708200d01c9141c02031404a00b007807001d403020550050020030098807002c0d1034020a24140c00003459620180040c06c16a40d00c0b10003444011042000054803401256405280c003092480c480b80d6805031242007500e0b6200041c959048035100c2d021a20b4194545000b5410b03600d0b042c40143c01e4a02c1030022092540c00c050301444d50001c081c21140c509902c0380e402340c0c00340404440560f0217a07803506125080542c800c11741010200074620402c062890340000075100d120720310000d012040c00700a44410701c114030390b0310700040c031100050b585020359400403040100190310400074940500c50020f100ba08000c80c09034201984100e03c1c0481c3da07144151400108014001d07074402c440c080e0100c10240c0ba = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 257000782 1250 256999532 256999541
    0x80a0e060c09040b0907020a1b050d050c090a061a03071103071109060904020d1b0b0c0601090c090602060c030901020d0c050c0c2704110402071b1d070f02010603020301 74
    0x400c46041d00d561a19410107000035502000304060040c88240c0400c16039907404503000140650010600a000802c0804040f1440054000c942d00500c80c40002042110002d009000c00100361b6101340b90b542c4009032601141c4c114412454110814100e414101503120010b5910031400d0070121013140e0b6040251345103800407282101c2d003145050741c2c401c1500e805001b450740000110399801c030350320b041d13400b05030b0010800400402c84030103041c2d9010300e90103282c01200a0060040344070f844276800c03c42c05039035040070311038590103c0c60036156112152186080380c0584019400908054540341014030403988000c1070088a03550078818601d00207010700404c00c503099956182519100e0402015092540104460381b2071140b01c80221441e401c050140c082d505203c103010b0708959694200f800c2000704080ea01507100d84001020003c00610300103c4101c0214806022281038139000100b541803140380d48411420290300001d140c5520440461040003494400811b10580ea42d021070300b0758 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 257002032 1250 257000782 257000791
    0x3050f0412050601091515030218040c03090c0905040201080606031803070c1404060315022d0c0f010207031205060f0d0c0611070f06080711121c05090706080a0e06 72
    0x58210f10300410004085010346d8110140b000d6100c490140740c80180300605645030801000e054000c0303010803c01c03604c0c241482645c14050300c03d01407000c000c90000d000308522601118000d114800120380307444030b4840c05c0e100b036074181c603008056115241080455000106202101c00d03800c44004100c45080c4050064a44105c010103020b509085c1d0308204000200030384d81c0190306e070440402c0400e05019114130480d100b400c0040e9118034030301c864803044502d101404064582480400c6e290b1145500900154201d4000d50700c000941000c814240c9c85100c001600180080ea0000d9814045d0303030245030005c4000305540c07681d0b110b80b80420104800050203079941e08940e0001c208040c1c000200514403100c050107400e00a040440c440502c0001e4002e49040280380d5001611590144280c80007010070b001c103e4421002c8444010302036880f018507124480402050741c00150380030700495004801910107031902c182046c0017121103010040c41c0051b1540c0b901c005004090b0b080c8a407078080c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 257003282 1250 257002032 257002043
    0xc040306021c1803020703150209060408070806060315040b0a06081005061e030a170c0a050709060504021213020103020f04090e060f07140f1c020307090f0f0303050f0412 75
    0x2040c0072003000800700c503443c249855440c88010421030000e40d011030721105903603000c031015140340340c00d8440800a00030714a12542158000902003401580051403c1c00c0700d6819040310903e5071070b031051688401040c0e080741c22000c001004900002d1a688015a104200030000614580e5a40306a85001c0d0b040300010b039441d41d030382e0900c00b41e4140102c0111320400c0b48032062019110b00350200b80c1c1d0f030000c14006000743c04461161510070200034122054610001c04844c0044103074101191501c03080c0c4500460030340350000000d1903090a000b40c030019101e1100320fa44541c1d401d8501c90940700405812410107500700100503a000c2401d000d040a0401d070580040d0403070720341e80304030301e850b4003c0c0081c00c0408142041181440c0e000d0b510020219081c45503503141d070726007076030542a4000d071a201281c8407000e408211a02000d58040c512030304150341c400e4000d0395a51000b2050038414003a02c800000100c50600100c0c0c058030040070b51185a0f40d1052400c0d40e19030302c1c51000000800210759 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 257004532 1250 257003282 257003317
    0xd05130b0906280b030f160f050a06050306030a02061b06090313060c0c080307030f1d030606040b010507050706030b1003050f131406090c0a14090403080c04030602 72
    0x40c080c500040690045918004088508200841209400f50400d100807800071204610904000c43e4105502d5050090f089130106e01d02e9200840c1c441e80460007202da40e400350800000c0032034190b0b045602301c56001e01400d4210307003001400c0304c15030f0001f4400c1b60180b20f40301651005888400041c00395030112000c42c0140083c24640d1410550054002c1c134442d4414040e0070704924070701c4446812101a41001a81400f8503d40384030340e40c01701d40c42040c0c5400046010000e040c0c101c0306d0619903203103944d600c044102c074140f030381d0a601215401940d05a44141300246071800d0070384c0058401e000504056003801060303a40c00c1e2416006401501c0069114540140e075820304000417040808141020700071860304071400c0d048030000506442402da581110101401219440524034010042c162140c6242c0030001703951361580d0107000c1d40555032110000519015103da14800081d00400c0f030790441d100c680341281d11000240000e1401c032001c01c000000203456100410440c100201d43c0700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 257005782 1250 257004532 257004571
    0xe0f0303090d1e08010905181b01021204140d03090914151f1d030109060603020a0b040b0a030903030905101407020a05070b070812040b01090b060412020111070f170d0212030c0f0d05 80
    0xa00f01008030780c5285411034140008e00420710140d000c0000c00c40241c48fd19255001410202c1e5240c1d019400b404207189030a1014801c900c248824034131900241c5400d9540d00c20240c184504c45000d003207051481060310024005680c4611303100c0c0c01d1080d90320340c1101581c1003140003a0031034141c40710884103e90744000800c03c5080c11a10180101100c90044d1308103486d10000e042c0e54800d8021540425580c1c0e900c044c1054041c1d80200c16154101040b0b4030394a90f85218540200a150070000511216400103214540b0000b01c1010040d07010003e0041c0500d0100001041c0d00500001c6680fa81c0901c50300b01070f801d40a11291140c1e000c0c2041d071405514001c080422903211050035401048104024084800300d004980791055080c80c0040c59022224110350410329150800502c1051a00780050b000081f1032110050f400c20100766410006031500903641c4e4507519690b0032040c041840000e0f1780090140181184411203001c15161001e016110070403148100c0d5044111402c0d44000e8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 257007032 1250 257005782 257005787
    0x803040e01080f0705180c040b030103120e030c011d12030c15060a0501050403020f010e120102070b060603102705180d0801060504090e0f0303090d1e08010905181b01 73
    0xc6101c41c0a840c06070210b9410300380402c43e244000d1400c0c19994086030040b441c03180890b400c40300102745c1c01c06504c0e12940c507450440d00032010340c640b9000164090002c1d50300c1d4030b40484e0303811140703074143c4640c40325665400040a4640b0f04001c0c0950002c6808080c0007141c00a000920007154490007030984142049090980d400003c0c101d580100096441808182d0b0000221800c1d00d40445a14016aa20500480e000f510004c081500082c040200b5840c0800540160441c00e00c80e00c2c00c40800d42e00d14080c44010f00044482c0444248410420400407001e81d180c0c18580c0622221185681c03030950940b8241c860503164142c0000305110620040b10041c80604061107652501d20b2040d45803034802001c0303010f103010304501241d440100000903c410445c28903200e61400c2625241d2501801c141d0310785441000400c0401c01114404001d1598208030110221142c0c07900d044d26420301e00e03010010b0400130440e402d6503400521440c2c600c60f04100c200c000b45580c1d00760300601c04510000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 257008282 1250 257007032 257007043
    0x90b040c15020d1202030c0c01060305060105010e04090c0302010f2a1a041104020901030605030a0803100e09031204020409140c01020d050406090909020411070308100e0c0d0c03060803040e0108 85
    0x30070854205030300c0c00740d0340c6920080c802940c0300000f4001d0707104e0b1110102101e551003020784c4030b003070780d8a045000001c0041c04a40da80c12650262075104403400030030184016181141c400410500d0f00440c10b0005600a00c84040311050b28500b4140c1095901007410b840100010b20350144400501c100080000315420901c0d21300b200e0703004907802c0c20150754010000d24001c42c2903103e25004500c60322680d210f603001c02d00074840181201c08120203802c1039809940280c40030116840300b028041282070b086424103000740c6102d070055192042c114011840703104090000c030380c015141c0e2642000f2070b50700e60140c2410003844000d003005a201c103002918000800d81c246c014090140001c0040ba50005010710032601c422030b022515025510020f002800e04c1c1d102c4107144540810b906090541c80b0241610590002150408407500d428108944400460f00c1c4c0e607901d0b01c10403440240100c260000343c040380090401040d0745454159060441c0c00039009841c1d01100c4000410950104010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 257009532 1250 257008282 257008319
    0xe040c1401050c0606091b0706020d0b010509010c03030b040b04140601080f060f1201110307051b1c21020d0207020102070f06021e0c09010605070302010b092206090b040c 75
    0xc1540ca0100f40d681502e40302d1034020005c03485007449400150340341a600c20780d042c19001009401e40e0703411503407810400941201e40020903680c40d12a43c02550350207101201d0034410161140c0e80380342d1155404074040e0042c0701c3d120f074115403540490001500c540c0100110b50f020705003061418a032540c001003200740c0090450742d02c0030080050051540382c2182407121207105a807420024417a0300c41c0c845c05000d4441020100f081c0010811000343c1d8414003401c5086070140f03900c4003030a6011002c50380c1d880540740d00c0784500030076883d010245016052500910340c1c50241c0440c01c1c201112281e00300e801a17100c2400d4103030005003000c1150703418814440580b5002c1c4207050402d061145c025503400600d5140e60100d6000c0d0340042c5c189200300034510307008600500d07240503580c50b4000102140c002c0c0f0b80c00c81c0550300b4110f4050403868086070381c83c883c5560080040c840d031080e10031290700c102c80ea0000d43c0c560b039450f0344883c0450301c0050000c1c8100d00804035078280d13a00d0080c81c12800c41d007050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 257010782 1250 257009532 257009537
    0x2006130602010b01031116030e0904050a0c0f030b131a0f10050909060106030903051312140c0108040201030f02040b130e07050f090f2b03090b0405060d0c05040e040c1401 75
    0x280c05906d04128401d940302000b0480b103403840e40b50a4130341990401d034113001d4150710840380800c0000b003000020b414004140b0910036452019620441b802e850700d034600006242c24030b01c1d40002c10000c1075181c1507104500542a5028011040d9120020b0395015030325143c0b401d50003c100119100300354007003030080c0030544001065150807184e15440b41d0040c0141801c1503101e003800014144181c05070341c0419950f81081d010180d59600740101019003e40c1180c00c002c150320308822800300840e00030740c0760206071a2885079a0701e40d0300440c0184002c00402009035801d0202091342680b0001601445180802d0096140e08016980074800001441c890401504200348041891004203807000041d0603106504030801c0f20b03001a403054006c4400f01c040101c4544071208100c00c000105401b20700070303100c01c4255a111000703211688180d0041c00d030024020440d1112241d01c941c0542c8902840d07150040c201516814542031044094070295421003000750184581003405162620462090 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 257012032 1250 257010782 257010791
    0x509070e1503060a05060409080316080c04080606130e010c1d040506060d0207021302030a0f06051c0b0c0c07032105070c0506030a0b030d02010e0708030a020a2006130602010b0103 79
    0x600001d80d1950004c0400c00010780350004148a0388854100d0380006501c01d1100351245460030038030b2003030030310803465500040740c50001c298800b8491003140c054a00701d00c060b200c1d9544400a01c2460340c04401d0210f150703943c40b00000c0c0700945c2803040701d45102196a6001e605a181c0600444003015580c081d40304910300307014000c40f03650b10402c441c2403000c80e201c050784425480c000502d840310707564202c81006000208216190300e043d84403a0440b180000100100ca0f140c0c3d041c845100c040e0305c1c01c0068810300503020b42c0132408000e5410707441099141c1e91490901a030301c0507403c01072107a00480b000032912140c40da00c40300c551003252522640340380c018103210340d035240c801c0017140506c6442d009560020100d140c54625402c0b20f407084074054210f030011010440000e000300480c0000c0211801400c4010984640c04011503d1015040d4000d2183e20415185c0074503907082d4118241c3d040180004c4040962504405020518011140550003500c0c2c2140a401e60b5a03850400307040600c0c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 257013282 1250 257012032 257012071
    0x140109020f040507052d030a05181b01030f020415090602060702010b06070f02030f01060e01170a0203120a0c0c03060203040b060303070309060e0103091509060e0f070618090509070e 80
    0xd400d44000e20b8011101004800844020303841c0c8165039040700c406d003000081040501c84280e007119004410542c1001c02030083c40040d81d44034000d03401d101429031452401c419040d0321903089600000c601c094018500f40e13884044003403288031100500f012a041c29410014190113001141d4041d010340028442c070716460740003803014800c0b90001801c80c2e1900c440c0740c096403801c20540090b00c4000001700305c0d5a403140b15020180d00b0900c034030b40c2009003014005041001c0070800400d80d90380940108000b1a92504403021900040300000400492010150100d0610034400c00110301038a4010307680c0c01c03e401c00440345840100107038000d6208008807400294030003507030400c840303503458203d02c403c80c2c03400100c000e0040b05d800035101214a081104031100c460303002080301071145108010b03022100052648407601080702902130340043c5410495180910340d0512101c0c650020b2040e2251200310340c80494105482da00f0315588452401d101c00001004101d0b000031510321000d508080307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 257014388 1106 257013282 257013287
    0xa020307060507030228050d0f08070305130b0408090a1e053a0210050d05061507111c2d080301050f0d140109020f040507 54
    0xc6200019a00380a0022180c1d941c2d8150058100e030620710108a14003d034404681c44800b000c0e0f0203900002d0010b01124902c100300e40c0f0344014484018800a11f0003000a01440c10301d0b00c2c080034482c228002c0e1000040b0254401d5a1040c1541c5500d0140e50038018443d540741c10200c1c0da200410360203070342c1c000d50282c500003110011030103998008100307070b04900e22400d14000f081c95169510b80f0590583d12004100001540c0c444100940c1c00700345641c1028521038000b030000f003282000260700e4060150852011612020301241c0100e5010b00c03403055a0005000d040710210326491070f215450f03d007200c0c100c400e0440130034030400e081c032410050129201080460b0303066030200911006030000c002a9400c41c908070304603801d107018491040f11002c18554044011003540d40015941280c0d400403103862000801c82070564070602080030001d2140c1c0c1c0c030075401c15042084195 = true := by decide +kernel

theorem cover : BRFrame.Cov 256834532 257014388 := by
  have h0 := BRFrame.cov_init 256834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 256834532 ≤ n) (h2 : n < 257014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
