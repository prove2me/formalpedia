-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4313
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:12:56.450985+00:00
-- url     : https://prove2.me/submissions/5be03456-610a-48b4-87c2-efa132f39792

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 775539568 ≤ n < 775719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 775540818 1250 775539568 775539577
    0x1318050a140706021e0114240607020d02060c071805040308180703112e1b0b01091802090a0510060e1e041b0302040503060f042003030f0a050409060b0c030708 70
    0x60a00115940300099986451100182c0340318909150a29250384804900800001c23100000d85220b42011420340028011140032503000e8041d102c0042d0b03508000c0014400b0801512900c4441d4480700090709201c40100700c11502580000c14010101d0031220079020b46031103500125000700b40181c03d6131940c130300c0700c066002c1c1d05a04c504002d5846510300846454107842000e4a10f03014816117611034050004508540c90b20513a214040c0700c000010481c4401d41d0640e03000443c001080b034910502a48014800d030806075004480904000c0102c003140c103c1e43c41404013401800000c0d81d40d0609075500d0048040c03042e8090003e0075544c0c0c82c00d009403650741441400910101e02040110708460180032211120360009400080c248042d082c10024590002806010409945025100c42c5001080810003500301180e50040c42c5041e80c0030002d88003403400403a400c0e580e4049080c00a042030b40036128010820742451000200b1203995001e13507081415400241d481d00c1071650711090603500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 775542068 1250 775540818 775540873
    0x16080f16020c0a081608191709060c01020904060f15030e1032060d060207051501060e0f04021911011b0801090b04050105030c1318050a14070602 64
    0x1d000e5581c01c007030f038500c0e1915005240746000751601c0081c002810351642016000300701c0c19402554425202d84a40c10b80c654801c1d0080b88025019088458804092040c448500c0c0e1018020505003244407041d801403021080445081011701d5a426021100d004030388640d00f0503441840141c3c8000b40240c1090001107a01415138040b403500e01c42c800100c0d00d902640b8041d0219059031a01035280841e400241c441c9102031001591034200002481841201001481c194021400b001006400c00c0203610055000005d0300080d0303182c1c40d008007100550b00c0c1703252003680401510821740c10a482103985517040510f585180384500c60054443c0e040c80c804da8986903603a008114442e115801c0e43c001c2d0f11650340d48205035945010007020681320002e850510452030400100020381d40040e20f11203902c0251303600050005902d00c4000100340b100c168540c815500c003600c0041100118200c031081d80f041004000c0340e0b800c41c0c102550340340e0394050311001d60b0124030280826840e0310480d452030324 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 775543318 1250 775542068 775542073
    0x1020a2f0607030302070b0c0c0319020a061a0103060b07020319020102100903121a010c060f06030c0305060604150e130f0602131401111908070212030316080f1602 72
    0xc0000400d030680e0140c1d41c01d40001c5c0d40826142c08002d0700c0d414841e04640030481d010708082001300d0807512072003405462254242c0582c55012140d00911201011a420030000c22000a40d203807251030004070199a2400a4036080010840072200b00c1901c113030317a8000d00249070393302c1a1080031074402805a0140d0541c45600c410750454010307406881940361080d0703203030307440c4490302a80802514105004041c00d00c0d04245040c000340d138003c0b00080042e803c000049504501507403028000d00e03640d08041c01030f90110314040244800000c145015030307015a000c0281e002118190b50140c4614014102079150301c0c0b0106200903213104d81c0092003805035010705130244403070356072038100d0f4804803102c0401c2a680070100200068882903850110702800c000c0d103101074444802d40c603070b600c02c040c03080019205d0322200e0034882044162104190b0280c92880a4080b1403201956030700f049440c00324295100f0000c0d02494403030040c49015448100010003aa2205600041001d2064010b0700461 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 775544568 1250 775543318 775543403
    0x1b02060a090806040309031b24030e010204030b1506031003030c080d0c020604020315100509190c0903060f0213050105360109080705151c020a0302041401020a 70
    0x80c1c00c00c3c000503005034071070f4655048040c507518202c210340c4c003403007906444107100340b5003040a101955000d60041006001483d00f41100a000385d0041c6400c2154290643c40031038007104000d51a0035080c040c00d5072400c012071040001080240d2848202c03042103c070385415100704000380c041d20b00700f006a40314180482c02c01032481600c9085842411510700182d0001041c081581814007402007540301c4c1034030f02d05662601c4680700041c8401071223031500030404000015a01c120f4070744030007000c90f015070090080e110000c1000b4900c0420740021b44880c3e103000c00c400745425842c1700f160072204a6015110031180b80c000195010342106417040c10702e1800b954500000020300001e503090b140ca40080a0807080d0250004140d90304a402036181a4011101030000b034fc0c880442900c1c0100c010705207a9100c0c000401c0ca80300b0364407048480c152a00100348124820b4054002e88140d8454844654204114a004a9132688101005001d2a02c2041902013048580d01d40380c441c40d035244c8041011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 775545818 1250 775544568 775544579
    0x3040306150905060d0c060f0c0b070215070516030311090316090b040213030f020a0305010612020f04051e092a2e2d030f0c1b02060a09 60
    0x6490141c4080241c0051041c018000700303900340324040c1c2001081c0c1c2c0c80030401600ea680c01c0e81250701d03400303090306210803201410f100502c2a200791070155840070158a10707091428010b580d8058038906186100030304400248043d1280d0162800c1021821482d6003484a07910203400410100d10118003100c0b0401c001c0d840c41c1c40c204076405c1c41901480b03190084e80e2414211a08940461807610707c180d0040011418200c10070713002c1c00603250410110200d0ba0000c5c80002c60400c0d0381d0740001e00035420420000f6804030345a403003148007802501c3c444c803100c1480d01000101d4801300e0394140070711445131b10001b546131010002580710041e00221880800c00071032034001c02c0311020260190500c082800502400c100c1003020f1203401000302c144000c4014240341061540800c1c400301001214800ca1200011440d0854005140c0140d10a849501600010060808288205001801d00c003020718134500c42c01e542c1201a005003900d9103d61411340c00c111265010320008402c0203420f5030301182 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 775547068 1250 775545818 775545821
    0x30f18010e161e0b0a030216060b030d1e080c04052206080c0102030a0c230606031204270e011130070f02070b0f0a091505120903040306 60
    0x2603540c0890001d0207606840c0c0d4156481034000d81105514044555584429491204801c4144c64411a005480e000140400c60081c007903012500360a201100030780003408400d83c8441d41d0706101f642501c5940001080a880c08420341c03212040c2c100701c6940b00204c1c80e00c9030300d601e600b01003400d05803460030b0350b903a00140c4007034010b40c0690384501008100407100b03545881450010000c2d80040e00c0420442c40005c0d4403402151680c0c1d06110001d01c03090100316040c1c060382080450284104a18640043d0345503a03400100e138014080d2184200784000c2002c1d2809580440702d00c111004030306021009984a0360050342c100c5a5040e46440480c50f4000081c0607000c846024081c036242c40d110056080407a030780c1d03c1c40c50380c0c500300c40500060071a030880c003880380ea201460342402c000100d0900e10880ca06080f95124040404010440d80703850201100108804040c1e5074540000d2520b03854803c100c514070203424004140100007c600480919000c0ea40c0568800103407810190f8a448060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 775548318 1250 775547068 775547081
    0x405090c06040b0406030b03070602070b030a1401030326060f0d02130c0f23090405062707030b120a060c1e050a141305120c1905010801050114030f1801 67
    0xc07550010405210546d0700d41b0964410a03411030080c48030070703c4e00300c0c040e490301c0d418019801d504400000042ca030030305542041c0101c98100d50317800403941e03503401d00500f120420b0fa6042ca134000d1503400d50b8554800481024043c00004000403442030b0070000b00045541c40070022604142000887c003c1000c01b4881c50680300d003a900e07042d40d2030440380c400070580c40b505c202198a1450800002e00300107400015160107074010344000449484041c001200180b0500c801458400b45181c001c0f640c0c524101e1040c00b500340e07a2002c0c40000c0501007003303000e40401a5074806039000280100201e80c5507002142d00c880c0c01e06100c070881008001c4c020020031041c0721800840d6002560303017107040d800707500c0c0c03c030380344407604114180f41c042c540001c840b81d247d104091003290181c2c805454680c00384540000380b240181000701031100080c50781e8041c002445483e0229803414000280d65020340c400c851030706490300d82c8502c5c651300c000f408102e030340010345840e071460241480240110024030400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 775549568 1250 775548318 775548329
    0x1a071208090a06140f010509090d03020310080307061533030b15030403080a06060516081c0509060702010204031a070903231002090105071106071a0f0a1a0405090c0604 74
    0x180300390305d0302191482d900501039001c03d00801d0340f8020494404004289440f0203084da217009a5203032070700c0740301e001180034681101c0c40d280800540002003200640c0028040e01180020180240d5a4540800010300e1050440da24140b002c0300c01030303441800c1503145540404c500300010746d041300c540441d046440d501c42ca045440310000a000626812104442d8040c600d10024484a41004d2000300345003e03030012401c1c084081c65505040008070401d440310207a00141141162031501003d0015017070a4450741124050300004c87d18661041c002c581c2901d8210311051007000c28040c0e0b4035002e0000411482c1000a4000040000350701c80101d4003449030040d4002d440400e003100b03c5800e014012071000f03003140c410819000183d0b04442503c1c0c01c141c00021200d410304018005c10118442c805006144e01e4400708032081c160101d101050103a401f024108100da0344908a42d0100d0fa032106420003245190302c4640201c0c5001d4110315444604c000c2a1070003a00064045140b079049034014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 775550818 1250 775549568 775549601
    0x50106020a050c04180206090109090c05070311070e070507050109080d0b040b0409020901060c051c021c020106050901030206070201111e12132d030c1a071208090a06 73
    0x329070501408220210004404540c10000ca0548401c0c040f4280c100d244003d00072200030400300c440b6070150400400a2401d16018032400e182d050005103039902450040300840c500e055000b520300d00c0000c940095030801d1800740c2c81d546030300b40b068603281c001460403180da40d20303840003100060788500984245a20b6070340101d802c00b4180204800d9070650520a402645854401c40160317513090090740c1140c0403800d00d6400025a418028102101c0200c002001440405080c000b0b9a000544a441000300c0d10030281040004004030300fa600d56100c0c895000e111704006002500d4108010031941e4414140946240d03011050305060805680440d6400780140c130004881000034400098008800d0380640d2502610004103544c103141e50007806080d1035811590b81390b038548112040c4061700c3c0c900d038001c1e41580d40d18209600350164001c00140d0301c5501c3c41102c44144c1a01626107243d40826840f07003135061030f0070450f00c2d12001800300009104058401000c02c643d813046d110a0787c540c100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 775552068 1250 775550818 775550833
    0xb0c010c1409010f030216023f0a1104061e0905060f010c0809030f0f03181e0f01091e03050708030f0d110d0614010806060c0a150f05010602 62
    0x140a0301e01203001444001541e020440015507a9103c040c80c50b030301d01142801601c5080e80300c05895180e01c00c100003034022208060f604a40a43c145043d502030300174034240d05641c1d459210003416200c40581c1000700e603200301140303400170301403c818000c4020040c100040080e582c062102000050841104d0007048507503080c802c0c00c03002e0060507400039090303c08010031820180020319403159802e000d400c103000443c40c0101650188405180d0080040407501408410280345d03484e42d1242040d01011107050265003058200200070080c192000640525072403089d03018441c1c1d407269040c43c40e0400600d074001250120a807000c0c0210386c1c450114098406046107412272511600d038001c000300390f00501030b03500c080d0f0607a4100d4041600d192404214400300c0425a0702e0307401050402090981040004900c603482c0410101858000342e07501000350700c5440030b0204600c04c0046c03840c80341e007000e5030903008203920980012100804840004524810800050881380203070409401600943d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 775553318 1250 775552068 775552091
    0x1061206050105131a0c03040b030901050108070605090909070b0c070504050603030f0f1c1e0b09163516051206040b031504140d11060a02070206040b0c01 68
    0x4100d0000c0d080c01e09003a4038000da00d008100c0081c540d841215082c4680201c42d04085c409241501d0941c4052802c994a41c1c1d200c1c0309011b000c2e00121840000c56180000000c0c03000b0000501004a983c2a22920300c0c000140041c0300c04120000d00f000c50520401c600060b1000c0c1d58001000048038400280c4015410f14040006a45010740003d1003903106000a0840c0c101c0d10382142d8050340e071400b45a9070341c25103110100d908140e41601025951400d040c2d8034003201004503800d28414654002c0008544800c104a903611095842c032401c0501c103481130610714001d0072448004030303644261601c029000c1d012a00c0c40c1c0c8400604031600c450400901804044404d281441140182825070810700f2003e06903078650302c000c103600d11031916900044a9501c0130b2009442e080c8014000c03940a14087c1040030300000d0030134095481d40f140030484414180b2400b840440701c400c1c100a032050b81c40324640b28000c0d401c1024143d90084041100141c000c82000040030540b10300d0b400480c4105240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 775554568 1250 775553318 775553321
    0xa03050306042409020c070e0f0f0105010f020c040f14091c02061b0d0b0d1109070c08030a0e07051003140109090203031c110c06040209090a05070b160b010612 70
    0x24416030840d1001d28441d007940800d980860f410364200003c01600d0300d5140300b5261a01c50964040d203051208403013030055a81c0d090f10801d00c02e00c10101201c6080c5d0383c1c1d1004441141d004040306005800c2024101001e01d81781e0440500d030003a034640401c03503200185100002031019110f403841540881d0411103042080e810100381c81c10039001501107481c0c036a030045122140c1c40c00c0030300ca83c6400500c80e030032000568842846100f0250941c40d5800076894402c0490721000041c7d03104015030760002d81c00c41e101c0e220207048a0f90051805045403502c034400e001420451820046030700400d04003040c0b032707141d858620b405011581d40204980d0741c000d03410a19020180c103c07040e01c5040c82811409600d00000300c844180c80645600841c074011441c0f003000744420031103410b266000148000703048000150940c043c5008030350500c41ca45038815460307076804e00703685e004215030892802009111000c00160a80d842d00e242941c14180c140d58032080c01110980101c0042131034506042e615011a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 775555818 1250 775554568 775554581
    0x2101060603140a020703090b03090d02061b0d0f0f020703080f0705090d080325110c0a030f330c020f07030818040f180b090d0905060f09030a0305030604 67
    0x1107050800c468840711a040886440c000d21082c1c04070380009440080502c60680100101074800c0c08c2d40d1a800c08071011900e440c00d1151200c01441030303c02003031380060642c1900710501e03007640c000c1c0d15120408880c84041c00451800311509540c1e25200411400c050008004143c03180c4d50b0040613140c15160800104c2e0050040c404000040c00203a0301e41e21152007194510307810400d595280d42e1505101014a02102c1c01010a0361100603450300d0347ea04a56140110b1a000d002c1d02e8102c801075051120b010068400980303e840d08442482c041052404446420100c00100c807110707041c088030215441c032441180315200c917a00c6c28407000709581803004141e146403c0001d00030740f500e16141c3e108103001b030352400c1e5203094543c0801b0a0550340d55100383c0542c0d65448080c040d00d06d1245003400c036207607006416548020030720001103040382e002c1100480d008103521042d594a00b080244001508031120f08402c0c00d50402803004541d40821500c8122440ba40d12642c1d42e28000051200f500d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 775557068 1250 775555818 775555829
    0x90905060f06150706180506101a191b0c030606050603040317150d05061503120d021303021305070f0e0120030415030603050706050c060402130605210106 68
    0x41c0d41003403145070380d1825003c4031006034076000e483d11924141000c000500c4207030300a40c6c010755003aa105041080105015103d6400d481c40320104607600d5201c40341c80b101c20551180b405c01c00b0010f03034181c503103003118001007030819207070035042d41440d0f100300c9000d480d20560680c0c01d42c5040a0420400c5030a00860014120031341d0801c1c01d6040a41d00036001c0c51040ca4800c0c1103da8100c001100392410300100508000c0080c0b03081c203524102d050440e100c2c2c100b0b5030b000617030603000407000046040000d10800042601d102e29858a1180c5009000a42050900c2400c2510400000002d40c1c1c400c600003480e105090400503460400000182524001d28024414040d0780000381100c0d070f800a404000d4150081040c00c145104503802c42c0c01c602c0703030703400040d5650b00070700b070038200039605611040a90707119070103c03501c19481d010290f640380108554042e480e84903500180c01801d0484007400e60f10240040480c826444600084501c0c00c0644e0b00d181f640c40400081c01440424042ca400521 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 775558318 1250 775557068 775557091
    0x7030e1c0c15081503032104050111070b07050306150a0e01020d0306050307170a0819020d080c09010f02010f0c052206020601050904050a20190e130609060609090506 73
    0x2001241d0240000c1c030011300070041c94400880c44081601c0500440300c0d40410f15104c42c41624009000c02404041560142c1d02ca610b07142680d040c00c0003000450f0b101c143c11162040e000d42d0727009400c891680c80244a160010606164074030003645050141c06050202d4940e110705540c417a00091804913004c242001b05805c0141c20009911702240071029071b01580207254003070400120840c909160031170020906580001c0001d24a00d00c0c0c80517280c2108103034290b500742022454119842d400948012030085410068050075600486c2c2101c20010a40004910f01c0b001805580c21101e102c81d60b940800c0c0c0010340c4400000c05104114190765180c1c15499506007451402940c0b0b040500800f070040c030484002c43d040c4581048043c0d4600d51048a03c10940b4614041130129050031007400c5c000d600070f0540c41c146d80303003010480040d544804209601580c0f10609582c402ca0741103403d855035a510064440404d0b9240101070103400c4900012600c001c25203015450039400503c200a1103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 775559568 1250 775558318 775558349
    0x608031b0c0301061a07050102040b180108010b0901090e04050c090103210c150c051303110405090a260c011b1b0c0e06040e0a03030b090a091707030e1c0c 68
    0x4480682d20f5032402850785c40c00340c1b9110146410343c0244115000b440c24032001003060055050190f040c044101030a2341c80e020540d90301e0100c00440d01441001c0c03404607103001c0c0b007401029000a10700e03611900882c00c480801140e0404214221000e030000d503000380c0b990940c0140d1118400004540c119030303181103400004240c03501702c20240b0803031908500136103591615143c1485041540c0d200510b450000c1200342d580d24010400300c440b5052207008504020006002241c00708040120680050303424004000c03243c0314602000c5025040107040358240142004284e09101e089613028101410030340c81902028007500b6003003140011865100307484090b5000030070070307200c000854629180040c400d448100005001e002e17000f81c0d4410501ca80e01c21a824980e0540082c0c0181d2400d0b9614203942c1c0351007419a098400c1d00700045c10403400d0041c0f00c1054180600100b0005000b840c1c451808845580091725071517842c0071a010640c403101b030b000148100521424020820b4043c080000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 775560818 1250 775559568 775559579
    0x8010b0c07031101020a02100201050a050c03011211130f05180106081009080910050a0801050f010f2111130602030301050f0f012a0c0506030403080402130608031b0c030106 76
    0x11801d90b400000d024642000c941a050b034003c0003d000c0b2641e0080010101909201e0000d009203012515988090b05150114140b120b40b030007203034162066107042c000300c0c011545414120580504045411003014028110076040714414810580a245008a41400c04a422440040a84001040c1d030791404204121648c80000c43d40d04444052001081c2c0b044142848902800364a0706543c2014241403180c0001d81e0100c001e10741c0d0040d0780c4458009980700c0e010302000c04001021203010030424040158a1409800d075480c8200c7c48001501c60032012503d000195941e2160390358a8100200e86160043c82201800001e032410b031005508640c9040c1c0007400005602055600500c4019058a05a4400c0b000342c1010f01e040107000036024181d0100d1400d540b0109429664a000900041220f18240040380e000355007560b01e1011540300c0703800b0400100520000d105c80e01d6601e13080012038070818005042c1851016040c281c01e400d0050042c0e0402d403840704160f2081e450500d045c000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 775562068 1250 775560818 775560823
    0x80a021519080405070f0306020c0d11030d090c030c061e030e0c280e0a06082d03120915090a0b0109110c120c0d09060503040605070507080c06060108010b0c 69
    0x140e08a20b8901106a51501d0522500f80b44c81600a8080c480c4803101c08010700100d03400401e203003d90a012111402c1420004a904910040740c0b4003898004100e0300d550143e03140c02610040740590060214a07580b80d036002c801040503484100440c2100c0d000104c2c01c0c3c140e12107106604120f0806015803200c42803582e0700d0350f03440000c5034440e03040c0000403405008000031001100b22008145910151503400c121043c4404940d0040f40703a050280c00302d00c644006c1109080c89008a0160114050b10391807005401c02da501180c0040c4401c0c001d030f0068160b00a0840d001c1d00429025000700d0100c5c40300e186101000404482003030344550004800580030b84d10050450340c4840002805002d8441443d01e280306140c28400e4511a000a0050900503d401018401346802c200e92030b2000b001c0041d00c0c001164440d01c00402d20900003d00440e1003034120315070103c40b83c1350082ca444a83c3d80c0d076450341d0700420705071142540400b0800100b540c00007021400b500075459071034205025111181e5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 775563318 1250 775562068 775562107
    0xd060609060c0c090c050d0c0c1203020c070b0901020f0d180504020a0f2a0c09051807030305090105090a09140109110a050d0e030f190f0e0d1b080a0215 67
    0x1041560f0701c58005c840c2c2403040e019612248030140007400b401e035800500074102c000c0c8200540e1183d81d24100851082e0103482140c0303207800d01101418042d85000d052602039040a0301d80c0741980140c00c501a030790b403414490801300915071307210b204040c405880c00e5000d4940507002507014902c1000310388407450b002802592100350300e14001d021a4882092111300070310307502001510241092494080000074010b40042d200300080410003a80c8156046100343c5840750290215040948244042803085009004849040c1407151401441c007000c1800020307035500c010f0006c0e55070140362090400e0280c556006007040340e000c1c88440204035a08900744a05140d08017406170003d0180803060150704039010018044054a8464143c80c56503056a0312001e03540710110b0f010000c50128a002c1d010414085410790386607000e4a06103814030504000321201506c0c003000c0300e24002c4101140c1d41090024100840203011030381410310622a007060b01d0f0410000132034050103400d02d0303a5500c40094 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 775564568 1250 775563318 775563329
    0x409081c060501092c0a140a0504020a0b0331120212030a09020a09060b07030906020115050603181c0e15090906180c0417160b130b0d060609060c0c 65
    0xc0030349640020088020401481901782d0155400e4100310420200e41d1020b8182e00d00080e12405030f80e00c2c02440d208840c2c08880c02984400c02c4030f82442001e4030303140910703031240e540c0d489500b00c60031000c400040d111440b900c1d1903010402d40d1070882003100c080005a000c0d58140001c0c07007501c01c2250601e0703080c00020074406c1660f40d901e05400555407844116001820501010001e10752504000015584000429000b2803040500022424814800c10501c5140300e0a1400c040d414441001b4591b132000e440542d03590320700341c2d0388885031406014400d00c0300542c2c2c4550080208000d0302802c0322440c00ca030188909500404200482c01c5a800c440840c401220750300015510301000411814061889001783d040160412000f079184500500c25600c80c994010354488101c044136940b20544018080403c60905e030410201240300060a54039403030908145401d51243c881e882180c00c00c441c0507201c00d8443d0810407420350090034070805421145080c03142610107031070328500d107000f42c0300700c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 775565818 1250 775564568 775564589
    0x80d0806062a01060e0603060f0f181b010906090f03020d1a0c031b09281503150909030507080c0a06140f0f22110409081c06050109 58
    0x240801a099400c1c403000c2040250500000348014101c1c0500031302440c0520729400341990003040d0b461500190301449400485a4440e903540c2d00e00c56401052400f415460220380b0040b6440006903060010b6090000c02201e10b0038000c00100006100c0c000561200c0b050240001c0244030383c040c4178401d00256901540c0d20702d0740b52020314100d04140e044040540250700c0c170201340100d00c84820000c501401b041c1012086a4400e00e260392110721850f000641d10170b0359112207901c11000c0c1d515406604170100d070140420b13940d590700119800e8002d040d24000913925620303110810000c24181c8003038078040000b0480f68240743d60150561103000c4004d44480c001041038074624000300301901005900403828014510305840300c100410041d44c81100034414040007402000400800601c14482c032040c412892151410004d81c80009210944039a00e00ea400003003940c5890040180c02817083d642b603a034a8140394050031195803070701d030a900c803a8104441049a61381c002090429174252514 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 775567068 1250 775565818 775565827
    0x305070807140c0f07060809010b030c0105040513060801020c1e0609030406080a06080a0c0303020609121e0f0313020a14130203060f1f02010c0302130b030c0f130609080d080606 78
    0xc850b2500c089680500d0303245c8291403003c122180e1080c10607000e41c0c030440091040d2842c81d0105500c03402c10316001c81c00282d0501040113135141c280c05c8045110350f000030009415480c2c0c508503080e60f011034605521a400030f50400364010f0041d20000b42140250050301c86400c003410959100e1059105c0d14041201c4c43c0041000071046034860350040031030b0070840b9410551850310787c0035940684002c1d030140c000c4200081c940390f00410420231012802002500e4003140c0070700d2802a1080070450709440700706100d41d1508011510040d03009034118404004c19003d1481005076028003900098002914180c1100c241c2d00c6400e140303c00b04000d124007507203a0341d580d4042890881c0d041d803c5580200100106550f168080015007a00742507503000f8090f0621114080c0c09a10408020414100d582c102c10030212070b15101842d008900d80c02e03d1881e007030710441e00000e1500641744080c044001e4036010060380d904802058000c244010207084c1d1001d00300c001030203010009150340d010340400203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 775568318 1250 775567068 775567087
    0x50f03010501150c1a040b04061a1011070513020d0c1103270612071206030507030809151210090c120c0207080a0305040e06010309020d110a090615030507080714 71
    0x345e800c81943e5182651851841c00d4240311610300c5066400341c0715580b420b00c5001c1c0309040d500c1840103140000c0c00340c0d1414a11000e0481d40504414010191800740100228035a40c2d2110301c40100f100c200f05c0541c5659000f07120030120b0700c0c041d04043c14099842c0182145c0e42c0040150fa1501c6040181e03d607410450301204e00e540c9100b14030785075000100040c0e1960010a1925080c0210b80c207a513111071154454071404101c0b0414003014059138051041040041d0400d80100309200024002090445071888146013136000070014140400790041040f4502543d03007618001000944014407a6003c45400517140080380c1120104c0c00c1e88448040d503e460080090000a0041008807203c80729181001000d6400c540600a10703280c0c4003000c134050398441c3c040c80d007001d90002c2a885000030700d0b5a443e080706104107407035900922800f80004140c849882850300411150846205204c0c41c4000142114030040416041c0b00400043c440c019620040100700d049014240507650002003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 775569568 1250 775568318 775568333
    0x170901020904060602031308061b03040519050a0506060411030c1b1218090405030f1303020d0309061209120e0301020f0a2106081f020c0d09050f03010501150c 70
    0x2152142c0c1c01ca414001c0c0041d4a6034000020203200c0035914101e0081926842d5440c2c80d5a81560100c41c004150f401e40d46003a0104401150403030700c82c01c22200c0180018018030b012504000080c1ea1907085503101b13a003440018440c0c41e600c40d50480301001030313002807840d081c00c600000d0580f0480510109401d603d20307501110b044148981003040319210114002010348541c00f40c650903010060801820005040400d034090189500c000514140780c00400c5200950b00508954159004249000400743c1c13588101c48482601035541d4079696810060007510f158001c103a5007040601d4011444042001a910340036035084614051104004c0800020f0182c042d02000700302c1c5070340000390381c4002500710b0300a40707140c46607400f0800442d007500d038428100c0c1d01e01c2c0f161481c1e5401440c003004080000142c00b50014058800c018204011201d0461800d5100486071000c180e02d44014049407a0094030381007040c104400038040c0f5030504203a01d6085a142c41d880051003a042400720802641 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 775570818 1250 775569568 775569577
    0xf0603191401090b1e15061321060608030a02100c03140907290409090c170f060c0a09120201031805070e0f060108040f05120d0603051005010617090102 67
    0x801d4000e0000c50b20300d080142c6141c8041da400020b503504a0364900c0c5564450100304d2103072a41901071131800301c04006100d221f0348402a4805070802e04074002c200720096891240c8041d016039808111500c01d407034000c04450968004c02d181d94020301012415650004070150b0700c00c280c01003c2040d829104040c1c1c00780040340c00300501d02983c0402c200c1031150028041e400c03641c04c4900803501072001e4180703040e050b881111680b2a080c04020502624005405c260800e901c05e40d49002c0042e84c0e8a40c502844a0340d54841480d608448070899070b19070704000082d08002c0d4001074070319215100101511502d458852400b20503010b00052082d68040c2d40070604141c82c0801034411044c1c0d61600315195640b90141d09000c010043c0400c10b250b899592a40c41010183c444d9106903c40d511032408203003400300110350f140704820319114a6458040682000e031100c0d0404240b8034250b140c410f0402011101440c001403810300100003940c3d0184610354043c101c8012000326131241007465019200c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 775572068 1250 775570818 775570853
    0x309040e031c0e07140916021f050618010807030b09010603170c01110f07020609040b0307171c02070b0a03110f210714251a0f060319 59
    0x600e100440310b202003500401c41c0601504140c0320043e0311040042604115030104a80014901c4005072501d421011201c2c88040302c1c1c01152a03440d0140d440c00d0303541065809203c00a80c0701c200b44081410a803151240c58200304c02000c009604002d4910b594004078480a0700e04249080440d203088400c0d4481406507070451143d030045109202c0e004180e50207041003443c59860b2118811415501c0c005840f8841005042c06180041503002c0103010b0300120321256100307981d2152496035990400000000301021050303c61184040000141001c1e021084007855042100d210003c45a02107041c0040d40c550580c100d4640311601c904800403d26540c0b42d04980c1b000017a00c070203c050007009042e80c030f8407003203403041426070180c040c007050309003512140b0115680a0082da0850750080140c42e91840c248028400c0101000740c01000c002815030a6035a105a03803900703030103520070000c2990b00040d07503a400001740c01d0070300c04690758914802002e48400d6148810350304014101100714041038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 775573318 1250 775572068 775572097
    0x10b151809042604030c0317120109060609240c05030708130e0a0213030b060114070b0f060307060c030806010924030e0a1a1003020907020d0e010c050309040e03 71
    0x2c1d1514090203884403d0b000c144019a001c501006540d41c1c5a0848013904d50000307442462602c0c40d074916121012070403002e40e0b104020311502e8110852000c21900a00c0c1100003c00c0b1180703000720280090000b5000b201591100f488002060842c0c8100d2410b0401c0754640713005840103070309107a801d6028007040140195000500c40c4a80b00c14801d800d000d0b1000305050103d5074441c4502007089101d0640100d00d8401d0104c5c1c10408107200140095110700c06040010f00202c8049200240e50b001800c00c84d55080100240a051a089514280c1c04a07080e00140915802c184010b001e60800100c010100304c0c418002910a9114a00d4030000707111042c210385030b2030481d54900c5140034105500310006403600c004000b400c00d0000c2c00541c0190440d03d02032080a130000055100403000341050035040c416000040107807a0744d10422300c51031195026100d01c180a00380145288010411141000b42c1d5400001c040783c4040211070780780303000f00c900180410285200a055001d508401c0c040070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 775574568 1250 775573318 775573321
    0x71e06090b18070f061e1202040906030b010501030e120a2a1a15120304120515090604120e031618111201061407020d06090212010b151809 61
    0xc80c10542c1c0e5100d100780c401925a042d48408400d00d1105692090b04002a055540410355101d0610703506440340017413900d200c020040540080a0b80d015503c07250000303503200c0c0100144600007400d580500024a0240710002d800702a03181c0e10780c0c00072840700c4005800107003c041316000e152100b110840741d16401001131601026000d85010200c000d03258101154000161031911405842c0300e2000c41101003004864541800b006420080c14103603244400c00c00030481300210340040200c03a101d500100b00105d542d112003881c65402034203d04190307110700184000919000281d2442d01d00e5440c04001032408140005e2401c0c458240ca400c1c401840200415100441c4e04104020040c1010510013250f412840305085d104040303c1126a010715001440082d20841800380d8040b907500c076560500c0480d400140b41040e15103003c4500994481c055402c500b411810200300020700c000070000c20100c05c003c14046440c1c000e1a000d003003070018080000e9003da03544492169009482111103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 775575818 1250 775574568 775574581
    0x31603150b1509040c0c03020d110a0c0b030603100c02030403023001020c12030906010b0a090f0b04050a0603090b071809110304050105060907210e1b040c020102071e06090b 76
    0x240d801103069134020b5052514001016000301c0c051184954140d0041800c5514180c8c104c4d2004000000100240031f41c0c050440403840e110341c004040c15541e528180d6a041c20000c040c0740141c81900103000710304040f008600c2079008402c2d2404c494040c1d030444a500c1c08044484083c040c40d400840c0c04041c1184e0301301d1304e180158046c00c800b41d2403004590004c881e030041000c60b40001c95052003258032010050099886c10300281c040107079a42420001c2d152145005a070f102055000303006a06c1011408002c14601100501d0050047e4102045001c00301e45070100d49680040104082c00704007015410888042a050300c01411458420018446980141c800951040d5030680d819828440400c0ba58900428124040c101d15114089a0100f031344509400c00000d045648520307a903072905d6101c41d001840f12000074000307440c01580940b2400d007044100d41c0c1c888c0c0503408682c0b06215107000540d0321180d000e9218041e11074005440550718140000c1c02060000130803280d83d00702030021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 775577068 1250 775575818 775575859
    0x30d0e1608061f27051b1b0c1011061003081905090402070606030b1f060e040f0e0c2407140a020d03050301090e0d0507080336010b031603150b 63
    0x400d8013140c0050003d07444590003600f4205500712100f0f5844c208100c031407000400c0541413140f85070050291000000305200080f090a0201c0510021640080f02c541c03540d40c042c06015440507000314005001c0d820354403080c4460040300c0c06c850b000b9011101080d0283c0c012001d803020344030010800c1d9a40c405a18001c80917065500c8100c403001210310200d00d02500c0315500e40b1006107a40001e04031745183c10001c80f84820b500c44810740166484400f2409100d582c0102c0451041d040c00406d0841ca520f0213015001242814411604841490580c862540b440071a05403a402c244007042c00c1c011450024203001c000c000007580181d00c0c102100030103400c0006541200c27502d11003045100400d0301440d40300d04c81200345a001403404c008500004503840080c1d86c200200128018109400b521801100754000f10400c20f00901001d101d00310840c02d001d00d4a0088040d0043c1180c0c80818039500755100c020300004100038400801500b02c0041603002c2145901c0040040020160340d010180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 775578318 1250 775577068 775577129
    0x421140309010e040c02150a0605090f0402010f02010b01080612121207180e1b0702041125020603040609080c01020313060b011805040c030e030d0e1608061f 69
    0x2d0124600780707904015440c00c0e20484070710340e101e50054011800340c04901031904600900703c015199072140c1c00702d51519000f4910344601d00b0300c101e00000381001e00014044500d1200d03181c04581c1403032203900703890341d010201c00d030000c01c00e9818034103030700b075142510781800b480c0001c49541e0500800d244100e41000107030240108443e4441e0f22900151800080d007411b100e005880c0d040d100c100c081442001c44158405d0941c2c10b5484841c06c02c1d0241d0700040a991849003122001903000c00e401c0c003100c5124000d074590104d190780883c4003040982c04151180002400600695520184001404480e50032142108002030003155280780c500500184251080c00035195145094007d030002e5001d080100e0301c01000342502d00400340380600700400381080d61310880c101034540d0710040c04414208054036403068010000b03d402001031030310703503c5c02489802d440e12078030320003034200022540850300681000190801e940f400081d8a034a40610040307078410300100f8501170242a10345484032008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 775579568 1250 775578318 775578337
    0x120a05133201180209070203030702190c0506070317010b090d060e2104080d0905060d200706052202011209061509050703050702010b0f0d0c030804300804211403 71
    0x340c202d1b10b039503104036502e000846120016910040704640302286540900c0078091240e404d140040341c480c0c01254694001c924101c01113921404040480c3ca02686110b01600d40c4522090074001a8000078860600201004c0d012a581c0da0031090484800e000710444d0300780185c1180c071030500041a07000c165000e4400d0102900030703204100503103485000850100d030001094103003082c02c403581440080c04141c0c0706c03a07100f04680c4540c05d41403c6c1880038241c2c0074024040052186003098490010516402c00360710020059268080142c0c0c00c403101d114880c82e0103500152015441c070f044802010280c900c25801c0ca000240043d082c1c92079088140715407190358081c0f280c0d803101c0005909840b10712110661201c43c0c0c4010008504103030203030040c1cad00e0003981114441952515115060707440b9030040c08950741d4010801410300e10b9203000103c10740e90000444003c80750360700c600721a4080c0340503842007621111190206146404e042c00a51900701d42d0642300413608001c543d0f03407540000d850 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 775580818 1250 775579568 775579579
    0xa080715090c090c0221031315090203070b0307051b0102090a0e040218040c06050a180f03140303010e0f0c1902101a09010306150902120a051332011802 67
    0x707131a9440c4041118030002142840815010703074441c40c1240707113400c02049030100700e92911000000ca000e80000070784440e82c45400090090460040c07504004090b0010407500d1410418020120b0b44202211600090300103e0461000d625040f203001e8440c1315207483d842000c1e43c070082101107030b03096441d002c0c510803500890406400004100316250880f00503049124440c803c0140f94040c0004041340b20461814119810a4010202c000e84007a0000002d900a0740014810401400031848007a103d0300002c5086601d070107400e1020078401081c2501510740003000c1000600e00205840060b8184140c1c2c804804002000075514003004120300000707401c01010302200c04582c6074603944500040c02c11210b0b030f07095840d42c402404100b14400307143d400021000030302c982d0600c040c0800341d070285c1683c1c499092248251050b00c80151541c401118170307001200c0020f40e00d864202c084c030200d445c40c0e5003541d80e40c404100d2040030700100600d19420505e00d0f46d02440340c1d01c1c14640c0700d071080301d6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 775582068 1250 775580818 775580831
    0xc0b010e07031b080c0a051e0405120f071a0706051906060e01080a090f08220b030c0a0c060221180604050601030318030210020c03010501090b030a080715090c09 71
    0xa140c10560010004601052500c0c010604030140300f4002c1c1034158490904a2401c805180307841c5041c4200742d6a230359402000b00b01403103030b8500004c4003010140c00c00000c1200d4201324130560f0304c1c0d50161294441c0c415800f000c02d0302072508601601c0d041c54014000300610700d490404042c8240030304510740e190914050010520a00540a6400400042e502c6c5443c5903140d00081004044501081d0344003001c100c1203400007000ea20040003210801c40e500701641001c0882820301207000d1b0026862480240304110456411500b5181d420140c2e2030808400402410600002d1003907200c400000c000b00a175962440d124000401d001d0f1200c20300326003101403080381046c0c803080e0a44005050390821001040401d225503580d40c0ca001c8109a0101410360fa039000800001c0000382060150b000000400800e00e804c5c425a030040001c480213000d20846400065116542800000d04811010810109000120200301c2001080300003c00100b14181803c0860754410302c20b400586041c040d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 775583318 1250 775582068 775582091
    0x14040b09040b0405150105070f02043603050703080417040b1c02040621020c0a0b060102060f0702060127060b032205070e130606030b07090b040b0412030c0b010e0703 73
    0x104551040c0745440412170000060001103440e5407140c581980d401185812901c0540d482d40f15851701400108009804804a43caa02590150311980360541200c1620920040303900074044410041d41031810800c50b591701d140400a511b480820310f030002c5004100400e031070a0700d10050030300d045061100700c0c0c241012801d910503442180500d20008074004102ca10500800311104820100024090304202c0c02c1d5801a2820030700480540e0000c0c0d10000303200155805000c1d058108254600031812850710740f001039070712403040c490881081c20444001461120420407201d045503c82c1c03007030003211b54850f8450000d800507103410b4002050310110190b103415544845510b20340c0302003e060303a80d2820360102c1c00c0003801811b449024603c0400300d4001200c91042d400510f2090f643c8501c2c0d810003000042010400d03400101c0c20b00810881801403480410643c0c0817110f08070001000d40c1c559280803900c114029000402e840c040300d001040d002c9400c082148201180c0ea01080307142c0303290 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 775584568 1250 775583318 775583321
    0x10e010320130e0c0403030302090307150e040f29040b030a06060609150c060b130219030c2105040c0b0a0e01141204030804021f050c0f0105100b0a14040b09040b04 72
    0x984d020b90300790400300310400c00039009801600e403040b401010740308681c0d91040c0d001c40c00b00906241d0380010350211003040c02407620384104080c03140360301010400106203034560320800e002c2c04000110b02100d030b00c0c2c0b000c50380d540781c00280d0f04050240036181e51900c20300d8803202404160083d000481c04654010070898001e420141c40548150350b0450101d02030f03260072000304031036607545800039500410031035020020f000802046400c20070912804c01400e00003421202c1003440030f401c20040384418040700a051561411a0075450310008a0781c4851910794403076002540451034603400800d0302a10190801242d0940b802c0c2a01c9420180800007801001d61190f0816055008051008600032a104020165200340b0142c40e040c44203520340301c1c1d12147c880c01c0b184c1c0000150000b405482440c024800c4600c0a0340050091240e07040c54007500c6000078a038014140280c50214010019907c101001c4039507614a800c01503840c5c0d03c4141e101201d0340062810b5004508091003405a400e00d07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 775585818 1250 775584568 775584571
    0x230d0b0907020c1021020f0903070501090b0403021c061b0306050a030b160216080d0905060906070803070309200108070807120b040b090c0a11060702060105010e010320130e 76
    0xd000490540d0404d00a4602d13102e555030341c0000e0004010b0251000c0c00c02d100905248001c8506c450b2190f10031810186824a56002941082581c2c20300f040080041c13000c1c0c0d0300f981c1c1d048440008941030700e80d640c020350860a0700030f0440d03801c0400031500304250814104444400e0303681400b09a4540090141c05401840020f0540c0031500c00134a1859181762400f4240701036106551014510000e0329501840d40d4218808035040042d120b00c41d1504442c0d00c1d00144001e940c05800c1465000c001003840c01001c0c0040c0840d000040094140e901c41d41c403884d0441c1d44000300051000100d0b070607050742000541c1c058007142026000c11400350058200600c51000d90b0398003091400c24444150180c840f20040940043c3c40d89909001030340c4140e0407074802e004880c5425114107510b0b0b17008041c981c0c0d01c802094190440014403610b40d0b4046072442c190f8500782003a080011716030004900034020044c0343c070214003040401001040802c8020404800040c140c1200527807115000d14040c1d40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 775587068 1250 775585818 775585843
    0x30b090a030503040f140a0303060603060905090703080c1515010e0402090307141903050f060c040e01140a030812070810081c0504230301060e040f0201230d0b090702 73
    0x81c00042c00017203850701c600340c85510846201082d0300d40a51542d20380404000100c0c04a5150002440902e62603c03944d0010002480188824201032003241c0d2907015038040a4042d0000042d106501d105c20801c4400340845010703102400d140031001700300c1e40c0c1c480d9500180050141c940010380f501d054000c0d915082d40c0100900a082d03c0c00c46d9040050120841c050340180101c5501522020540c0b041300086000300023070401180c800c6442c500b030100c010071000802c0c0c0d0522041c0b12403207152400d103054412048090b4080501540090505400380c1c0c0f00418010000801640307214501d0200b90141d4410746440c0c40e591203410b400562040940180e024590100c3c80c440141c64822085c1c1e44100c505042c241d02c0c1c039444a410610185805540d8614200806524101c50a0921a001c02844c2d00a4210b18500f01070352008002c600d11303c0040d040100c5040c51589500c1070143d00028452002c0440d40d54100711600c00024100d0301046600c0f80c0b40d0030001542071400884e0030904010b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 775588318 1250 775587068 775587077
    0x912100f020a05221a07110105030103051002091c05031c110d020306040e1515044110050a08010902011e181d09070501082802040b04030b090a03 64
    0x10752000301e400c0130440d00d4582c1d1500d5582800005048600700500e9603404a02c100300b650f604481d0034890042078014200714100182000104003042000c0340521102281c4100135a40c0c0c1e0481000810400301081c8030301110145500c03440c100300c4004000c00346203850f00020340700030f000c0074140002c41d0212082440b81800c02c204043c12001e650303004581c4810014000a1505005807140e803529125041500c51802c20406110a000c441c0c40d44c0c10000c84110340c03d00a608410951002c00c041c04a0388000347d1210a030344c0220b1880144010300941a0403a0301c1c1d00d6443d003010000c44010b940d1242a0143c5801003003c9000e284c18082d8400b481c1e01a1141b000d82003180c3c080c030f49903620170030f0310301c042000d20303d4000d014450312801d41009044a030071080c05034559200303110a000025216540951140b0004c00481e604852000c0c0c3c48a40c00e103605d41541000380007010981c0c5485c605002c42480010702086500841c800391041e6800342c41641d5140e6160182169201001c140140104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 775589568 1250 775588318 775588327
    0x1d060d0e15270a0b010902030f010803091f210b10020703111005040801020c03030402010f0201050403140f04031e05011b210608150610090621020912100f020a05 71
    0x14004a011005101a24215820040607844605680744c0c20307000016041d4000040c444112201070031603024015000103180380c0315600700024403040000039050401004801c040342c43c079001d10340035a445564418a9061111404200d0005140d03000042e03100d066102218200244002603841c2541d174440e407502c040e0620002004100703119074064204003c01000b001ca41c1c004280041c0065500840007582c403030800d03100141507076079800b180c40110380c500030801000c258030941c550452114024880d0341c0c0c1e448144121043c1c0709540000d000000c1c45000d4114035240640300c80710b158002d0000b0481c1201902c10118040c03500c090480c001070821b5a07a0219000c440600500400d05010008140e43e64015550030005005002c06000703080c0010081c3ea4180300191918071a25460411a23440c1445c2d80a0111801622158240340310701034032600340d100711ba0441d2f03064007008046071082111000c070940c0e101100c02581c0706840c1860040b06c4040305d035000340c50844250361699400d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 775590818 1250 775589568 775589611
    0x1005090d081503160f05044b02070507031e0812070203040f0909021527040f0501030b090729090103150f031e050c011d060d0e15 57
    0x140e070000c0d502d82d40342c00345510440d02c1d913000502100090603511035252003503260004020440304450082003c0c0840c41e07012403030806010072101451098050102500c0d52400310b1326031050244005403042c0d501c000390141c1400f05c00141201200d100760180741c00300804102d42d07080301031004402002002c0078002d1a1040011140441e4080d00b0781c0704490030580c1d11300c0703c00d21440942e40001c038060b90b203501c540d0643c01c0c5081a5640c401c0c0da4040c0b41e00c1d108101041424510b00030f0f0300444000b1381e030005030030156a03d81090f48100d8410000f13012650710ba04045000d52001e40e1054082e200d01580040c50300703403c4500609448807441000c1325203001202c002c0c1194068400c0504040c1d035002da001070100c4400c84580580908a04007840ca801e51030103901d5a1010280343c0c01071907000c03c0c2c090010320300207100c100040e42072030014054030240550000d40c20700c0c9050380d42d0040021810350a06c8201d640807418400e210f40844a00d0142c040c1c19407004c103001d07904000c00000020b600070a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 775592068 1250 775590818 775590841
    0x15030103030f0c050601170c010e1c0f05010213180b0d0b04051c0e030d020c030a110a0f0602011a120c01110f032d1c051005040203091005090d08 64
    0x16901c0c0c10305050200d0001c2c0c4e0750b80c07820f0440980111a02101d80c509103400c052081011403a4031a081c204522800315860004400b4826500c1c403445503403102c640181084105013403c144558858001d545031508001d1202d2111440d00500840300c51080071110440303900c0c020541642000b03800f4a6183c8080d464000712140c00038816140da200303506010503940316808aa1250b05103560703c004044005004042c2414650f691146c00c5500807108501c50355804200c2002265200456031514030150011402c045d20307541c024030700ca140d05000058a5501908405851411500c0c100c040d0452001007102c0ca18000c001c940c51984450104581c650181c190034101d04112002c82d02d0101d441011340740b46501002060302d4807116030000e1079903498046c65811003141192034082c00e0820f030000c05140d000345074a40600c601d496901058801c001c090034403010b02000f820a40d030360700c0c020072042c0d5501c1c0100d1404d0303902450400010b40400010510300d00b0840107a41c1c01c2ca240d11030f48800d25 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 775593318 1250 775592068 775592087
    0x1204210f0201050d110310141203030a0b030a05031c140103230c0409050f0f070621060504090b060a060f140d181a06030606130203090a021504030c051503010303 71
    0x8080c1aa90718007400d5154144016520525588108010756410040d6000b80c0c0c003030b50008c190140750744091041c0a50004410307030707910201e189400039055820b00300081c80e0246040010f0903600001900310116801d0000e40b03040303508500000c0c02180001805041d01301000d10015004008400541d500060051250721400c0009407c03142c00c000218006012217150312400c8a02d41d000704c2094410540038021604110580c4000e06400d82c90b102e4003901c80210141041c0e0880a280da001c494100b996100c42c003c5c1402410411400003d443d060603031280640301603122703120000b00090410b104048112180e1001ea941c141032048000d50f001940c2c01525003501181c6d1154410210484e6503140140c4a074054020030004010000e008044d004000d0800760081d08400100482d68640c08104018402d000c00016604c4d91200316041c20010441402036000190000312100c2c07a43c0b94000d40140d034003400090403120360760710411060001e1b1000d5510416014401003021034000c0c403140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 775594568 1250 775593318 775593337
    0x106031802100c14331005060703030906183309060902030d17090712290124020309150c030d2309030a0921051204210f020105 56
    0x5442c144104084c904040d9200c4001d1520303240109111440c04030507800303801d003134800c0e8100013240c2003071080c51415104a020760f50252600080e0758041510a91004000603045034040180b03500c140c00888095810740403e03142002a5090710b900070b0218117403050240f0b0005040200c0044808951001c0d005030441030311500c0c5da41990b140503071000d11003d091800c6c595160300101015001001c49160041e05040070755000f0302e024092a11181d43c0c600050f60003a0048140c40c60b1000c4440590600054010072502518000540c002c122042c426968900034919682c2842d1200b0881c0c5d240500400750794000c0b01c246001691110707040003040b0300800e810580c0c0c40d1100100e210713003e03182000721210406401c600886ea0801d400c403109600040c43e20003039131070080380c2180140659114040c194a00902504001e118501e00c65010540c9621405540c105814507464032010b0700144541b62031402140700800255103205051082c03144c0c40084000c0603c169001100c071500402c203d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 775595818 1250 775594568 775594583
    0x140a0c0f0b030f190e03030f04170c0304050f060c240123040906061509050315240307181401050108011503181410110a05040501111c080106031802100c 67
    0x2170400410381031000f903120340341c40e401c2070700d0904040c640085009603415220800c0001804040b80d1140080300700ca04440d81101c81c00016031804001540c144613019001240e4820500001115500348103440340c041d4144240080582c0e0740e010702c4043c0d044440c0820141c080c5010003042c42d05d803551003000a18011540024025164101c04921a60b01c18002c0003113106c0340c40801c07541c90204140040341902c03204076142030070f080c0c0c0c122000c481c0d9158100343d21518146000c4c0c40da18100041401055000d1030b50300b403ca01c1c140100c008044a000460000300c4602c0007042950081c181c0904940c50b61000c5001c400021008400600ba034441c0c840745e10031840c40a80104a1040c0b54403030030200c1002501011031010a40030440f242035400103d25101800401341c4140c1000c02d580866800b800d21082d006080c07540c450404580b48114480120741002e001c4130b150b44041e03014140d507400c1d01c041202c2c0101d203d40e42c40180000d01c0095120342c0e80c5d10603031401807085100b420041d00c198038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 775597068 1250 775595818 775595831
    0x302060f120106050403141209010507020d0804060302131205030a0503090319030204080d0e0f06090a030f110108180709020904020702211e0712140a0c0f0b030f19 72
    0x7403410110500303070300c0800040c01c042818030500440d01d00400846440d100200124256a08071000c1406609050742c10b001c0046008402c0d0344440b0f1328004910340c801c05481e62580c0b1007078060025005251307904040506004046034860360401500d1140b030b004401182803101c04181140d25a20040c5804400c2c0000c0c080080340095415a500000903030391809610b139800c02002c80e250095416000d002c01585001c42c0141d9151000d80980c0d4003002d5622543c1c0b00711910106e84034100c035600c020841c2c0034803941d907000d202c3c411440c01d140403c242d903410041e803107001000d140712081103100012600300d56010003400235554010001614050405428868540c0003c0c0c01c00884c0000c1400246404000c81c150a0061155900245841d11b40302180e14000c0c17078441e9541c100d40a601d00d0001078025490511420300030034200c9600210865800400e00d18129214040c1c5e0301c2404018400c481000c20141c8804042da4403030b1428030b40004140d9030700e80c043e914000b280728241d04168ad403070b075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 775598318 1250 775597068 775597087
    0x405060a1704080301030605091b1002010e060c18030d0e0108060d02030a0f0b060a03030518030307020604330c02300c13060803030a0f060e070c03020105060a0f0302060f 75
    0x208442c45075014100700c5072a50300d103040001c10307160010104d11b0150071204012180e030224500c1d00e0400241503401030301e8140c012906a00610341c010380b61080c0d00c102c0b0208406400844010640070080991320500d02c45401c0501d40d540c002c140b00040450740800b0061703160b511a10170036501a2004103075040e08038a0340c0100741020140b4005079499110000d0704000d10465800c0b0030781209068400c100b1940c9036407001041030117050504080700c2442850040789a60810980d088550014501540c9660b1614084c0260400d01e007803048002903060442c142c9180762051203101c594680b10b12460089a60030400c130b031400181c110034091264814441a8002403ca00702c07013204a80090003014201e404200d00c0d44031340451030000c80c2c20540107225960340030043d41d4020203504008a4800004260360300600f240360082691070007020200700715a43d20000d00c80c90710b8029002003100380c81c0e8006022031031102c0d004000070f42e071404c6810401130500e0f00c0142a03404456003410b0070f190f40031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 775599568 1250 775598318 775598357
    0x901120509190f0b090d020a061e02191101020304021c03110319140c0d08071407080304151b051b010c0e010f030e070e0705070b01030302070f08010509030405060a 72
    0xc4000d403250540c03262140f00f042061650290420b100c48018a1282e440d034400039622031068500500c803d803a240348540c01e000420056004590b4800150340340d099018803201c1318425584440c0001d5091401402c00c2e20042c421a40281d0f006011a18115420000010102440102142009001c41201841280c1130001e049000072000041082c220a07202c001c1403219011007402124204000035500980c0004071030444914504180c0610707959a0825512a61402d0320350480440c00102002007000810003144924822810460280081541c0c0c83c00c8034101844400c0d2840726211400c100c0d400703071002d040c561404a2038540205c214480480c00e44c1c00d00820348011950580c1c540e0070640e009012a043c0c403400d860100300d030540076003e15a440b0030b188030f0500c20400e140049450107128208451030960020105482540e403032500950f41d000a20030090b01d42c000203000b04a000c0180205802440c8400c015420941402d00300b00e895400940b442080c443c0d510f90300042c943e1807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 775600818 1250 775599568 775599613
    0x6063c0f04060b040f0501091d061207030501140106080403120506220b030105060d0c0e060f03011509050718150c0c09020a031a18041401020c070305010c050901120509 74
    0x70107250384980c900200640c0d5607150746c1041341480858a010b01c24407810040c1640008900b081270b29568440c0d1000ca0505108610380d8042c9004880011041c080150000080d402e0202150702d41682c1c0c8090850341c0f030344169001400140c07908065806049250002a000b0100400d106404200c000c0c0d0628012840ca001c80007a07030300d078241403c4601d02849003640c0b10070300341e8190140d07031078070798845003600514054107c81c0f82c0c0c2d1801291454440400b24061148080c8c000c0000070746000c18000000540d1107040d4059051000141c000303407140b40000483c40002002201c0d1909114509900b0070210030341c070b0300f04070551304400d01054000381c00d5070092103140c10040e03446440c4040202a5100b0340c9100b031000720014040c2e0100e840d02100c1354902c123189061505d0305e44492600380c2c1b403442c0100c00c01c041d43d0b0000c03a64428154001c40c090088a02c07941c001c20803681a40c40c1607940f4065044a02c1c007203954282049281500340d00201d078414000029102c11291200004c401c0600 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 775602068 1250 775600818 775600829
    0x2c070f1d0a1107061109060a0503041b080a03051803121201210308070216090b0a150806010c0305040b040e04020112060b0307110304030b0906063c0f0406 68
    0x22568804446500008103560411030008050081c0c01040001000c584140d03a4001d01080d0340c3ca400450848030b01042e210600d800415083c1e40d101222001421a0000d44007940c00c0c108161404101803d1030030814112542d003005808400b0b9642c0781512150400411211801c001500c92003990340c06100981141e0b1801d4103507030315203106d0600b005040303205030414440110800041d020301260f82a4503030f111981464095130076541c4d0201281056040e0440f00080003a14501156011968100c030201c00e205951400d6219600c4d8540c1c0030310701481c0c83c18404a8a82000308800d03522030414044000c0c0a4145545440d40d903d59500c8a98415401f00c0d1407808640203100441d030780823031484415002180144020350504480c13042a12000d00240140701b00c14030b0800c00000140152002141c02c01d4842c0f905182c009462501c0d00340071030f130141c420070080e06090180c80040c0014100402d540207100410031404144950781c1400e07004450340400c0213891090aa130b40c41c01084050030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 775603318 1250 775602068 775602089
    0x103060510210506150304050a020d0b090d1704060e160f05012c04200309010e0c19060c020a09051f0b1204020d060905031611042c070f 60
    0x120100c140103840c5032040250b00c1a2424802070261640e03c2e50b10a903504482c0748980c07566030b119480c04902c1d0045e907080094102c0203805000060151641c034892051103404140d03a009022042e00b201c04043e40241c1c02101032200c804900401c0107540541d005002c40c0e03089a07405c058407414041c003500c0982c418285182542d40501007540c0c848410103084517021510b400ba410352001a080100c040c1c0c2ea07081c0201d0b80c1d50030100078480141c08142d11074121008440c0c0c0ca041025010340039107208501100d0610904400d145117040c409610b0b441041c89403c1710b403466050003411614034501203005d82c5c0c0050801c1010840c00000c1c0304250190403e0240010000814843c83c58480039580c06011240001e1100c0c0403070a00303952006070f0180e412075643c240c840c10f0b03150550091400c80c40140c01807102085040e88640c1040c8900c07481030051a001e4110f50f00c0c001080260780100300e40104504001c1d04410910900000c1880e0300302c00e00081d11100340c1c54039038140b044442a031004c0e982c0b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 775604568 1250 775603318 775603337
    0x3090c0d0c0312080103020d0b1504060f03050d1b0308061503011e1e0909080f030108060a1b0507060506030c0301150612060e060607050f0106030b0f24040b0103060510 74
    0x101c4a04202500003203031382082c16207903145030000768480c0310442c0003070320b908d2400000511084040806540044009008100750354032a41030317584a100c0c40c041120f075445159118010a07001d0304041d00d000000079015100003507a0340c1c04642485002d045541c0200500d0010300d0145c50380005103001e400d80180d83c00340002001002d514405950b80700003903107062084042024404004040705950b205d410214800c030191415a00e0786c49907000540c41c80c000400040780a10300130419500403030281d0720034814001000800034000e8444001080466802c01c01403000411a402c2142d04c202e00905555155104e1404a400d5465103d625000103080e800240401500301200c91802054042c0c20001c2d0350501d0564034941c5006070020b4814803000c00d01004000b0704000301901225100d00074040c3e1640c1c4d10b0b200524040985000305100c20640020710501c2d10f030300d94240055014180c0c04c4512a205083c00010440307801c00c14101902c903c40800d80c1c0c0c8451822510000f210b685441d0312 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 775605818 1250 775604568 775604573
    0x1e15020c060a0b0105030a2403060c020f0d0903060504030c0b0a0b210d0c051c031b050c100b03030c1c110a0b06010305310303051b0f03090c0d0c03 65
    0xa1640003010260120726001c800c3e2440e990003403d40b070744205800d80020307600403140210480f90f8540702a060303840074810300200420089800c40d48008207a0b4003200e031000c01014610303450b18400100480000c1c0440e0080000c5805a00101c1e0840d00a08090302c0e514519160722498a4007164013220742c0380c44c0c00740a41c0f18185844600701d480b01e02006942d418082d01990380c0c0780c000c400310000400000c1c16030344090207424040301da281561000d01c0f10030080514005405040e810f11000740400b420010340998078003403412100350038044405080710028820025000301031208ac82901480240b090b18107001c02004000c60440f0228100b1201d8040050300a1186001d91142c0b2101d400180380e1800241d454a69030740c00c001c0034240443e451380d42e00144580490782003800d00d07551070049402c00d4000a003154445203103020359014001ca5540110742d0300c100107040b982c03e505230010080b06004a107440043e5401c03110003800c0c1c0c4d48518400d00000c1810360140801d41d11040c009204004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 775607068 1250 775605818 775605823
    0x1018050601021207150504111903050c060427020c010905031209010e1002032a0d050f010b07030e03010f0213080f0a11010c0320030706050f01030f1e15020c 69
    0x80160b10f425001c0e00c0d1040660310b0000000d002104921a20348a0021804000e0f2540510350304c1c80c00941203102014980354680b88405c8a03100a90312802854a10359990402d54112016580b20815412041d407040c02040c10068164444554403903092068101002080c001d101305240100f00640c4c4501241244608100303024045020302e038500901d01f040c200011801d240c214400800c0141c6950303c034500348400140054490009195060354242003c2882c805000401000d0408000c155038a06a84140b8003081c02a0303150303808207201110000b880358948408107900503001080daa141030040b10140e802c4280e45080c00d40c8243c00500a1041c00c000d074166889da00e0000700710030b2200d030312600d0040c220800103e0400801c0b03000c0c00185070042e0400d04880c0800c030b850780f102a000003900d90310380d0014181114260b0070720000c28801e140c1518401e060301d40201c1c4d120ba0300c514075500c00d64040321400d17a001d040114514104081140d4100303000b220a00d190002d80d40d82e070305106090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 775608318 1250 775607068 775607083
    0x9020c0d0315030c05060a0c020a030308010e101a1309050a0c110c060301090b030f0d0e030c04110f0a0210020c0a020916320c07050910030b040b101805060102 70
    0x460b0304120710300304086440c10072a50212942940e60a61b1414408411107851a42c0c0602075000440302c00000200750b4071031030981c12038000103407c441d1901c0741c56800032038142c64441e2801e41c000c3c2084015a03036100500400c000320101d180f020b0790700c1d981d502410031b07a481102c600708100d5840a10030091908011102100c400e0400a441d2540f240c1c000a40140410701500302e02c50b0b91101c1c0e0002a44042083c0140210b000080342c84500c49050000c10404076114a14024000c2c584020000c0c03c0c64010001e203100200000ba0500005501890042e0015241c4104520826200c41105841b07440240228032a0340054500310640d80180640d070640540040075400c0c5803030a0383c4180d94441c041c18030306203144e8100e11200798044a0350f45d08a41a10000c2d01c2c00c0c5000a18150410001461000300c070760690319007070290743c3d40b040038040070302c2448045d040c1d41d46100007800003884100c400e64052081c2c01d50044503511000b8004180c07008070002409980e443c0c082c0034403980c0400103203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 775609568 1250 775608318 775608341
    0x20c010e21120109050a0e060a0b01110f0a06091109071806140a030b0f03100504020a060905030a0303020903280b090d0f05030c1e040f150905120709020c0d03 70
    0x120300c0c0c0b0710518200c02075400d0510070341410301e9403240821118400f5412a80741c502c0c2d0700085078a141017a03601c00001708030600d452804150080c001900504021880701d9100805c40b000d448400541e858490290503c213400f1580d0040b81c07001c241e13890342e0344c0c1103072409089155520082c100013502061580c94040e00100140071545149610602c0346208890f1303078600518010800c90703881000700c0e05000c80c54022540c140242c0e80a18aa140680d0146110314002c907410303109581d4440054510070894010103401d0740080c200500400c2c0244c000f4040c0c00707000b82c00ca03100310103d084001d0132801c01e4011f94000c8a5220b46204c180025602c0742c6400641480151215810b604000307064080d400f140d000504c40040001285011500f0595000211010208409072000c034141407141c4c1c82405020308030403c1000103d0403642c40454941282816201c001c0c110b4281010040182c0d80c0b40b040820714803e5540208881030680090b060b0306003c170b0003c00340c541c9001c0c400381c20344030140c044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 775610818 1250 775609568 775609633
    0xc0801092a050a060507030917370b130501050a0b12070f062303090c1003020423060c01090605100509040c03080a0210020f1903020309150604020c010e 67
    0xd02041e0380f0a099601254202c1c00c00c50755845d03103490261034005c420ba00a4100300110400c1c0d0824410108140341c464000e131090300f000c41e02502110f0707604480d0b01244c0d80300d1044003501400090762800c40c0e036040b00240010164bc0c01d40c640d205400d695080300d05c1d900c45511404a070130700c0e040114038059a201000c1c0941540c60410301c10030038103101c51050300104034080356130031031401e8400d003100c18810070342c0c0c12259a40b80c150030890742e6241c001c807014007580c1c402c2040906c00c5d21920a460580c0c07030f080911400c4420112007010800724800c0d0303450f0702120821400c0c803504c00910a404101d1712030103010589250461501d4220841c0398881030041d1000010040000c0c0c8281d03070503007943d034005103040e19054043c3c4124030b0001801e01c02c101d5240300240240d10100000090041260740300000002100500c00071000da00094a00416039801203035050700010381e41403074545c0300341d02030401402c000410f0301c42400d64105a0f8030350030541010701551400000c000c010080235042080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 775612068 1250 775610818 775610903
    0x50c0102040b041a1801140702030f0f12040e06010309140a0303050411041a0405131e0605060d051b010302130e0906010608040b1807051302092e0c0c080109 69
    0xc180103865486d04111526403800040b0300480103039600707280c000e03044980f1112032402c440d59404000003140360920031035659031496500c650403941958403036480c0c44255100e540055025201d0150103c844400151010198000030080c0d110b0950003070341c2c0821942014200003e20310581c0764194055801d1140200014590105600c00000d0588000640742d840c0301c00d0b082a103054000c010700d00301180c0e681d4521208401c003d0704895000310340c01c120a0301c440e410002c4c404880350b0003d01c20340080d1003080e600444880803c0c24840c060601502d4040010181c00040210f500714280440401c81440b000c0801001a60f0142556085c09140c81c01c01c3d4407051011580104040f014030400540801c101c84240160b01c0101006805900c041b80c1c0d1071000c50194101000c141d01411000b1502401c13612849031684604140c07690740180c02c108840102d039000415803040da09840c0c410000035031181c091042203081e0380118031880c4844144603000c0104030300324500d1a5000c42002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 775613318 1250 775612068 775612087
    0x90f050a031b03170a020f0a020a090507020106081c030b180f13020d03090e06010f0f0e010903050304030c031a0402150c010b04090302010e121206010c03050c0102040b041a 76
    0x314909403500b1100c0e90715000140c200c00429a07100b5080108010341c0140c43c92002c01c0200c0103420f1001c20307030f002d5a0030240340c03002d03082ea07640207004040c0d880740c140d00c400c00c9902d4803940900e030031103403a100202d107045e19003422511340072014041030096104503148070413081e4140b00e0089440011104120300400d500910f0700988400b920582e42c0700b1102002c1080c400e108840e0400312580540604c10400720b40c1409004480d041c45107680c84101da01c0028283d62241c051b2009201146d219100c0c0d804034940120303082d0101c003c03000c0c1804500040880880c200708091700c015031080c0f0f81054040d0a5242039014502d0501c01c40058400c00c1c414000141d60341040c480b691290b0b01c440030b44800102c0c16013409480c410003000e40181c03030401d1300e205156040d0044d070700802640303086803011075481e6001d444030300c98011644060307002180402c2c503561084c0e45c40b45806000e86405400c0040c80c5103c0c5007241d000341d02056444400107410000d40c813174460072102452801203220308201440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 775614568 1250 775613318 775613329
    0x10e060f092107020105090604080105010b090a210b060f03060c0c0106050d080409050402012f0f0d0519090f300203030a032d020403110d050714010201090819090f05 73
    0x10f4024148100800c01c9030341521114240c0b00100781500c002d09c15565034910884655012004449c0254441c210225288107254203000c400e10300014001006141d5071208513003620b001c2d1289a006080249884403540c0070045a4000d810421000703960b5906841c0c40c0e400c48203e540304078083da840034100d9003c01d40000c196000c84181c14800715242d070340d910040b1a0322404400101c03009010101e10300c10b01c1c88240c2d07443d1072010940304490380000890f45071030b41c5c3c818001810300059010000344019401d02c101e4440340b9490780c10b000c0c0f811600e5071101e2041039159000044600010210700d644056030172402403035041c0e030044141c0c0001c816008242c0300e12410030180103141d100d01800101107682003401e480c0144084c503c440881412110501070751040c8025210a40b200c2503d181e58504400124130a03580400108581454150404ca64542a0344040d0641d581c07808010041401c141c000c040c42040b0307082020800100e0b44014248800c075030401c0000f110090000d100704d40300c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 775615818 1250 775614568 775614577
    0x12070608040b07030f05090307020a1a040302190b161106040320010c02101215080706080a2a08090106030b07031806060305161a090d05010e060f0921 66
    0xb01d41514003503500c1c40703c241c0c050b00c40e00b07541c18416440c000412099100202c00740c00c0003442240c0018261380d0b100d13030001910350350441001482008000400040c640300c1800f03905120b150071894246952440c43c4c01031900118007010190450a5002d030810600128144403000102d40a80c10309080d516805045080300b001901004600c030300740c0540380c0c00f810180086070703401068441e14105480004101c0203603c0709690074181405600713409501c3c252070443c2a030b41c641c001007030200c0c500705003125030342405081480300e00e5882d082c0c8100390060b01d80404545501c0c8020307040c880b401810080c464007000b4490540340c2d04d00b403c2400003c141060b800d070801048d01e40825030074544c5800031510700d40c0f03c0e00148072500d810300000801c075000c5150142c21200014401c00303143d0b28144080301c9941020091101d060412110300c0914000d1507100005000300000a07036404101a010715240c425200f94204601d01002c005199100f04a00450304111070f208522485031301441d45014000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 775617068 1250 775615818 775615823
    0x10803070f060b2101060e01050d030f17041a0106021902220e010b0909070b0703050307030b12060402030d03180f05150f07090608070c0f0c090c030203061207060804 73
    0xd1425403400b40482c0360409100b421004200710303d940c1550541360503036041c003400b19115508250000a0140604c10000d04855010f4207170007000381c65076411a081d6000f001c1034802d000520103041020380382c20200c07070300c918407481c140c07000b8401a070711070000d92105910030404c55011401d00a2407109820084050035419503603c201060040a000d000c1000c0e02c40004405140007186c03250a501500035080700f02c1c09940f605801d032100001c150711510700f8024089618010802c280000707104900942e400121860006081101e0000044140b40300ca042c800640c8d119a0034071081d443d081c09020340400642c1002c00003a8555030800c01c0111141e100645420301d030100c403000b0b214060182c4510041401e03400c66652414042c05543c8140585186d000560b00c408089041c1c1d0094072680e0042841d9143d4140041066491200403440800222080060b42c00c000a41d00c80f1070066890698640e140540c40385040b01c1440328403144102c031815a90f000c0541001600d40041d2040d03001034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 775618318 1250 775617068 775617083
    0x901121a04050f0f010203041b03030807110118030e01080c21060d02030105011508060105030c030c0d060e0a0b040e07030c170309220f05010b0d090f1509020a080601080307 76
    0x15607600b0310500f408101602030106000305020184c0f2108198000e51080d0310401d00c6046217080da41c030120180c00d49000c010049120100864800c034040c0e5a0008860341400003c90480400c0941004403181010100c000c1110602e16040541c0c0003030410b9800050600800d00789900a403800d03c91004041258400d9030034580400c1582d207408040002c03198002d8004c0c003647d607540c100d10200340c0c3d0b07110000d000135420340c01280040d8452000c0b41d004000055843d4250b4840000d05042640540c0207104820307501c101c001082c0084250380c6200c2c404106000514180c0d11043c4000d881c140d900d46400c680240c2e4083c030021751f841c4014410b680d4807140441d03800304854400c502d10320400c09150341c440300b104000c94002c40c82400c1c1c1181c80ca805076040c00a9600d012a51013a0381080c000d6030110203090150100d0a00c0310350007980c1c2da0380240c0c10300d81100c2d100e8561040c2c140304031107002c0c0c500e900e8042480135130030118006030080080c8802030035150302d003003a543e469001d5810014100f8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 775619568 1250 775618318 775618321
    0x2a03090d02130204030803041a0f01050906011b0506010f0f0f03030315091a011e0c030e03031b012007080a031a040e060702011a01080a020f160606050901121a 70
    0x54407030200030365012240361000c644d56901d07410001600d8204603030840d41007140e00444d0016009009440e8001c0b0801800c50b00e103a42070a0802c041a0801400581080103200c00c0d051082d5039428900001070107280030302595410000407144440360f9030404e594141d0341d440f04010700070a85c000b02c4c00b143c1e003600d00000c401585280003201c410f21948110351260402c20001c41d8005400c121141802c800d072500ca0402450010907010608800500b2012a00745c0000f2030102e40140103030b07110404010240e070b2804580c43c9044030000001c01c152503c0e41c0d551025500385401280c00c4d9070603514000b4102d4281043c0d541c0d072182602c1082c000608154031107007070341420141042907011081c0010401d00102d42040c100d50b82ea0f91084034060f005608150080440d5803046017521503501c4180e407818010307503840c2a038401a40c0030015492401a04000c0c219001c0c41110500450328400c0c0710210b20b00b03280208001c1f8901d41a040003c0307402641884e14000f0745070a024042020301c1c00c4c1c13070b80c005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 775620818 1250 775619568 775619573
    0x1020618160b0a030501120b04110102030c010e071e150f0504050d0b060906040218010e0303070501060b0408210a0e012a061a060306060c010b060a03022a03090d 71
    0x105200010000200c0610320800700b4149510342c041c0800084507038040081d80e0b40e4019204004110030340c06054030146c2004900130400c9045c1c1010640710600480c0e03c0c100c0240c00b1642152000d0280c8011307504225421f00400156190700d009031420150b800d00d40b1420700d04081d440454904005042c049004a01c0f5041401001171300d0084c00300410b0079010800324200071208240c00c07500144210480350003c0c4592400d40300b9106050811146c0040a000c003100540c1c010000c10102c03549441b0500c0030100007602401180060204003c80d6030310780d0b2a1039101c0d0b1402c041122400c11000340c0c580024040c0c007000094a40b002980e00c1d01802d55804400181d90001801000c0407000400d4502c0543c0f200c0c2a1030b003141038612030300b4104501ca817030425482d0342c0607503038444581c0158104040741c3c1ca4a01500039107185400b120000404500301c07800140b055202c0d40e1072002094010946151004210040b02c140101c4c10003101450500c0da000c0944a110707403020140300742e215900b00e805 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 775622068 1250 775620818 775620823
    0x102090307061b0b0a0e0d0f050904110706090f1208070e010e04020c070603020a11060903090d1e050c0103060e06150a140f041418060405041a1302040605030a0201020618 75
    0x140f6500101c411429051202d040e101078801d468900415201308500881210b106034503e900341e05150750b44904028440d001c02004d400c0c8004880d180003014070140c400320300b440c4190186940314202d645401d04191806820350f030703000c084030000d02243d10208071180360000144040003100340303000024410b41d1400100203000d41102804144603d80c800315020360141e00901078001903464125400040340040755a030003040702c094001e600181300b00c002900304620251a12441005500325003003140e40072000059100000f6261944081c081946550b09441b0707075000b4141c880c0310149a85001d402160751549000c5142c00e542c2c50009110783c255104040d03500c2200b5044440f541e0b40c008040000c66142c0050003100c0401c0d4031764414180c0d40c0703081c1c2c804100019408140a00039520b08040000800c0d0041060707034031541211140a40070b000072203c40c407821007060681300058180c01440200c42039900560b000c2d03400b4607600b40150fa0001185a131003400348080d4801e4091140c030250 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 775623318 1250 775622068 775622117
    0x115050705011a0a08070311040b030c131a2b08090a030c031502120a1509061d0c030705160c030c0602060405160f06050706060e010f050102060108010209030706 71
    0x10125440e01007900c1c0340720150010f4526180040381c0704106242c60b00305207515031400b807100a02c1201d0b180307624082c03400d00303821500203450000c0540d0030046624010840d0140c001c844100500da0703646488001e4108000701294449041e202000c03055101c0f130298004a040d1200c0c80d490400d60f140807403c016120045a424500241030b901660b9030300d00c2c040004c01d070140002c940f00d500840c0400190081e500c295054850f00c41048041038480c1c81d2544010a04500b1200c5c0301c1c4c109140c045181d4580d07006160061040504500d000760b605000c2814007800601008407000c81042401002540a42900d4404580041e00351070006140b52640080074a80d100500648001c000002c040c0d8020900502c0340d07018105417561010003105070071410743c40d8041c0c0e0f0039075401c40005000b0b00d44241d0103045d140388942d1001642980b10354141804410036031044440041c00744040c0401d503814400c03940100070110007036003081810b40002c0c2d15041c0074042c81c02005520303001d50342211102503030740 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 775624568 1250 775623318 775623323
    0x117211b010e1509010e0d12111218060105030309010e0d020a090c090f0b0d05041e0602041503050f060405100b0a0323190b191d060904050601150507 66
    0x800c03a800b035080d009902c03442c80321088840d40759000c002882c07000060080307801c2d14500d2030203407402c03000c1b2070010b48180c1403100240c0c07405076582451040007030b81c400042c09081200c0300308100038549205000b009000740b245846c125001440104451f4800200743c40f0400f40034200008101d4901d40481c800e0130b90308002139489001e00000080c020065802000f09064a40c0d61240b13a603200c0641e181c2300340c518460026607100802c06a10325043c40c0d40590f030418032841c2c202e1a032400c0c01d28007101003444400c064404507400641007120f1405840f00c0d02403503605003003d0140c0e03c0e00d640c0341c0b1040480240418000c6031100c0018404601d042e40000280510684054a848030700000900500d1503c210040d880f842603580e000da1952070b60750700e208680405403000020309035040c0c0005484403244a6801c811140f482028a050400081c4090501c0001002c0c001404101100c03a4440191281340195240c0041c4804228082103807810340340c1c0008041c00e081f10080c01200c0c580f2808001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 775625818 1250 775624568 775624571
    0x9080304060606090b1c18140f0f0c1f030b06030103060f18081614032209051003030503090c1f0905010206090c09040c0506040e0117211b01 62
    0x1040200041e0794005400d030b51050356407012440d00c42ca40c0b054144540715a00c4a005900742e10070b885982250817201115900c010143c4039280180d550b02c40e22000e032204032071140c0201d401140036410400101c0d0030181c4100043c1600690070022076001306a0407040440180044c00c0c00038018008c0e040041c010701c0c05440240e030b03980d407403c01070002c150004d405c24001d42050400301195050038a84030b089500408840e18101e034001a003009004d1101c070849801301524080c55442c3c8080c0040c0c080356403240c20314400c134a54140c1c0e00304000e516030001d0178840e00c1d0406118208080352452001d076541130614641c0c945444000728a0a101c030f0354440d0344900000030710520118800da400001c0032003904c0c1d6000b00c2e41c85a0040e1f855440480e400c3d41c0315400700c820050640742c18056142c200b4080e1448055141c0c40388041801c03035001da0802c2400c01c009500400036181c03c40700c00e88070b8007010405001240848403021031030521402200d04400d01c0803a884200f400703101d00c0380c1030031800d0000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 775627068 1250 775625818 775625821
    0x1a070f0b0f090c030307021309172a0f210f0d0b0906030a031d0103110a09050915010504180e1c090911190c050a03172401050904090803 60
    0x2000a81c111048900508600880144580900340082541c00b40390780100100014038000d004803000b09095001503a410765186925141e44910304024a4030400706959130341c00041001d5101d00c000700d0200c0c00202d0303510984050400e46004a0030710001d0403080804151081c0003041d040c840c0c0903c401740e203055000003404c0740e0801c160b0f50003101810b0301500e100d120342c0c0e1480308050715040c001c08041c2c08105d02d200d041c0d00480040c1c0140f6403121050400040031080c5000311401307900410003850118020a03414441c515164070410781c011450003c60040350502400203085008910032103410741d0980c02910700c00c080035000414005155411520028203050307080c0c20b042c03040e00022001c107035002e00120321800c0c3c0d8002c08c4061101e082c022413070200107084141440841504c1c24041000300f410220004101303021a10303032540240e40795a18145040c24552000318042d01000070301081120302c4420075400c01c3c004035401424200141c51f8090200841c014116000c0001c0c40e8500010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 775628318 1250 775627068 775627081
    0x5060403060c091d071403090606060a090e040807170304080906071a0f040312020a3219030506040c0c020d0c1703122206020702040204030f030f08060306011a070f0b 73
    0x203c0030b4401c41c0c0e41e41d202d05a80d6a051b004510030700c070036604400c0c81e80040c0e001030040c1c2840c800600401945180c4030301001e40c0da80360140d41d0802541e08803500d1200040d0381f424050206070030b01c00d040341080d0561030740c24956128030491049145a60140c140428023506014400c000d50202e1429a00036000700e05d03091401d600c15000031a030480c041440c84440c5002500c092003078600100c46901c5002d0b80c480580101c1d1100814a0100019207200c0b400109940f50448042d080f0103603a03030907414a642d450103014040d140014441c0e4000c0c1d1500e046c00a40691000ca40c1d1484c58058550001080050a000d55120410b4004070040c40401c1c0700b8608081c0c1c008000e01003d001c80b19002c050f9202d5407581509841d800740300d03800740074400360b0aa002c9649a80203001e120301c000d0006180c55504e9403004108001a0010b9000c0350b014104000c035070703802c08902648094100c024284641c113000c6c410311181c0403008043c03001200403175080c0c04c20000c3ea000440c0c1c143c02a940d11039a18149 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 775629568 1250 775628318 775628369
    0x4020a030f05011b08010f0603050423030415030b01050318070e10050901140307062d0c11120d0c060f050109051605030c030c1c0606050d0608030405060403060c09 72
    0x441300da0051000c1c10702007203106040a9040e40c900c41d508030b604501d0507404402612010b44141c4419403000c0c464054110200c1141d260b81800901451b159072400382d846079900c00801100c81450306005400a240e1380c42000c03242c2c0154079007020440c03000c560b0340c82480d001c19030f003040064043c1d007800d01510b50441e0103031384202c910468115515a032656100c1191088281c03a42da09036001410910a140c021176000c1c0e0f41c403480301000000d400e0700c03d2281d003601e00c82c0f04c000b10100700c0003000a81403058484035003041010035a2884110081008030950310544e0480c040b08000c981d181d094100111030f0801d4400120707120341800596140c4617220300410301564845445501000e405507964000c6055922075520420b2050460340c880460f4161580002003000e2421708000b070788050034070342d4451304001d02401e90343d039500e8001e568046030441c0d1003504001010f51091004101f81ea0b1740c074080b0303410341e507100001150a00b0428426035031200e10b41c21403d03000080065511010352403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 775630818 1250 775629568 775629581
    0x90a2d0902180f030a03111203010f0e07020a0510051005041d0601060f050403061d06240d0b1909050d020f060a06050108132102013204060504020a030f0501 69
    0x201d00c818030302c941c540c41085120041103940c190142c000428000c0440d000d1210520340703118000941b0310003014044815000d90007608100b01402d09040148100e0052010403980303c40300e40000e18011f0b001c0d80304c040c1d450701c1490402010548400c001035103080201e81d00001043c007e0000d00034082c044807003403401c0c20000000041d5104080c00018036511503400c2081b02c00340c646406141508548070440034044150a08206c620081580302d01d20504000183c4074250b04d20352a41c5e008403505031020032026403001144103004c2d020022011075521101c8a41180c0c0c420b144040b941c104859810282c0400603001c0c080340200900c068076140c000c0392a10000107a00c0541c0d03965640c4034200c4045405c54010ac6000031507810004100f12440403010380e25074012101601030080d05914a00e040150001d40070061b515008206681c1804609210008561140007203084c140b080785004608001440505010f40721400305041d9166021200080c44e041103000302c0304101c82c20114048d049 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 775632068 1250 775630818 775630837
    0x2010f0e011d06010b0706090201030207240c0809101e090c0303090b03010b03040305480d0206190e070f060813231009030908060903090a2d0902 64
    0x502c600c074141000c00103c1d105041c3c035445159241021015190440105805441241403681c03c101c5040402c003d9040102481d103d9017000d20901c40402100e03003500c0b171403400b007011b00584030207001160360082046180b0304100003000501e01c00c00382995654030303e8001c2c020303181403a1008010900045441110a8a000b51134285455540f0011090984401d12882074100418008140001d20800041100078030702ca010080b42c4200c482a552200e160700344810014540c0c2640d41c2088040640a400c000c0c0404058a0720010542019403100c100034490340c6102411046e4039246440b41d48201c000280710070403252140d0300daa44852400b042400740700c002c1a60a00007441c60103880b054128400d51148050009100341c14960440c00001c400c001e20901404410441d580114841c0c0462039000341d5418000350320342400c0c0f42c00c042c0003a20314522904104401c80c5140c03500307d0031608482d58814021406069041e400f0342a03041c2580303020000841c0c0c60009011481a006001b80b5070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 775633318 1250 775632068 775632101
    0x123071b0608040f03080903070215031b0c1506060d020d0f0e010903021b0616060501060f0906020c0910080d020601180204050321041502010c0210092102010f0e01 72
    0x81d1181015240300004030740080c80e411590328000c000910580b030081d08251040700300d03400d00100f9400507407224801d08102046000c04000c000308038101e0341c880c214140a0700d00891500340310703000d1580c5464481250690117118080820816203d41d02210200b000d414421501c900c0e0451a00d00981310105601001d02d0506513100d540c036030184141240307103078140c0040c01a40311006030087d2005403c420158002414001d03404548400c01c0754417406e51103070034001510740c10f050025040c0d0700c803060114100001e2030010b010b01500010a402030260450388030748079075600c201e10780108009402800640c001c403855040c1d40b980024159060f00c2e2161407030700d803006500c4010b2080340140e1042c0c42d45544110001440005545003010400005401c0d640c42e00740c131401004042e1654110090060390341d00e0039182401e03810f2042c800300600c4400103000c00f0320350f92607800302c1e80c424010b0321106011109904400c0ca000b503101e0b80f11440028400d0003003540300300540f4020500c108a0340d0040c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 775634568 1250 775633318 775633373
    0x30307060527031c1107111008090703080304050c130515060a1b020612190f0c050406050307030b1905011106090a030c320c03010603020f012307 64
    0xa00400550b0b90050b00356400a60803d001c1d1145055801c085098003034180c0d81d1440c09005044102e00105045802407048400403581141401640c5040320104401c1101d200180310440f41c010030b02e042141e404c1000d41da01c0b51140d00b0094101004038603116440745050740c0c180c0f088049904102d11440040401451150444041c800b243c8150000c00d40040d800c103601890030920803806c00c0f80b250014040a0030445501d60390070a43e41e081e230f18805401d020440740382089205020f15080c9a041140900c11410f0240c0c000d03201d80540c2c098401413110100000710310700e03c40d034007440d51204c005180d8482500e8440d0b106800e500c1c14080e10740094501403c86c005490b00284203400781d01c0c400e0090064483d140c40440380a540050212800e841100c15000d400c4203045102000d074100342d407040742122810fa0301d14a071046a146544c0664107045040025030703079000041d1101c0000307080c01440302e030801280107100c401d1406070f04da81080c04501c41b0180b009244a80760308200040301034094 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 775635818 1250 775634568 775634611
    0x5040e010e06071b0503071a1609050607080d0903050301060e04050405061303052110050d1106090f04020409020714070e01090c11030307020f1002071e0201020304050303070605 78
    0x1d9403401e541850082d4003840216450511890044007aa0302d0301d400600700043c03541d01c003411544840400d840300321001e08040c00d000340c41030030700da00511041c00401d9170548446019044004501c02c85c0d204940100342c42003030024031402c58000c0c50b40c0080c10090780401d860060580c2c0c00a0003203a0000302000707a10340c1d96040c81d120f114004c0b41c2100040c8601d65407a0849001403cfe0754108500300941070111031030601401d13101d500d203100300c070300702c41c0c0d01d071404030340750356070074407282d1000e481030700011105000b24a40340c40c80c141d110015500c5555920f0aa0041402e24a100c214550090320001c1d000070500741c0780d1701800d00984a80c01040c0b00c0c89010020079942c002c1030241d090b9070304802d00100802c180ca98400cc00b840d0341804d08629181c0003001c0107007182c20071a03985003d03810910410a03000000e0250b100c814060b400118101007032522640300c0941c141c0768403007107404074144e105c0039603008100390b0340200340003421241c1d5100d0b03501e000303c003412060b41c040440c0c04441d0252040c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 775637068 1250 775635818 775635821
    0x8090118110609010c05150906070807050315010e180f060d031d030a0b0f060405160210020918070c050c040501050907180807090e0613051203040305090901090605040e01 75
    0x410398001d00030340300c2409020100081c0341c1c08200c3c840d050101681c1300b03030001141030143d203140041881c200d17150f900d00000d0003800d2002c010b0101041201660400c080180c00c4001c3d2038000700346000b036561000e10980161a030442d100c4450f80d201189001302c491406500032514800c408001520340b190700d86e00c0c14070050b1000e900703000b0f02043c14004480f40c2c4201d200d84010344200c00504851b101c1c03200f52509010701c6070070b4810303800401e80e09040003240d040c180141600046c108400c0040100300c042c0003919404114000d801c0c0c641c00007052a107503503a038114511aa10f2148039803d8900b01a180608004c0c8054000c0707070f0f80e00511642510341c0c5002d2042c1d80c12106d0182c00b200381a505e08204440305002c4040203415038900300700118a00c4020003a58014003a81c220005440020350000307842d00400911aa030743c80b00602c1540000b0b00045441c49003d0b041001c3c964407074546140aa9140c003420401d02c1d00000c183d07000113580469074028008841c41542c04104d81c8100102c2c050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 775638318 1250 775637068 775637111
    0x90a0e011505030718060306051302040b011106150d0b0a0207050708030301060c11040e0601140109050427080d020f12010806150907020f0303040506041a0907061419080901 76
    0x30b03455002001c040094900b140d80ca171614030200c260004041e03803256030700343c100e07001554400c102203040d044010071030505118001810609080840c110b07100503840703a588150080c9175160603502d40e0318525050300c80c00c01c00e000460740301514100d40c1c54420b00c140c00135044102e061f10b0900c100140080c00d1400401228140c1d030b00e580d50310060003455190031030a4401c28908540089d9a4047c1076102641448130a010707140d55007080328140d503083c0004201450a8011520a03440c003400000390820084900807509550149050800c1480c00c0580c02c1340108802060710b81e00008071b6410305100403008116410040385500306598858440c29540c1208070780f8142c2303240800041084524225901c942d00130021b20442c0d00140d4468021815500259411036a41d072290b0248000c00c1050060008100c00d5185142011b1402161036035a03200c6611840007402080a01c40520390b6605049602c544030302c1d01505200c1c5140c00004260400448030382c040d55183c210010042e800c101c0410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 775639568 1250 775638318 775638329
    0xe0604020f011418120313180204230d050a0506060901060807121a04060b0304020a15050316021216050c0301050105010c020111250914190b010905090a0e0115 70
    0x714104a00d02c0c1355840b8210007181310950080d6144000003403818200001c021030f040884003600c58924098103c090070805080c0c09007041e00610003031296000030b65404d0b166800711840d0000600d8808013107805104203140160040c01410305c10070074002c0c009440703401460b080c0e42029440c0c0c0d13a904110785c4500140d5041c80000c4000f181e0300040c21240e004110407440b1150004c0d0b00303078800c600040494034240d10060f1550404410070041d460600e002800800301e104985403407050510009142c1e2100a0000c00780940c0b92203d214118800c101d41c11408503601c032500d42e15010840590800b40e070303007a02118244507098a01c151410306009a030b040341d0781a1a075030304601c00c1cac3d070044d1003000b80d4815203407041c0b0541621410300d03c100070200a1012800640590032420024540281d900900c900007070080040144000d14403101c80d10030410b1594680061419410070048a80c01080e0f03100a0303003e01e446040c44911641039001125419442001b0843c4200307084c0d084100a1252080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 775640818 1250 775639568 775639607
    0x9020f041d13080706110c1b030d050702150c03040303120b01020f0d030c02150106030b01020d0201050c0304020d06090b04082703030d052707320f030f010e0604020f01 74
    0xa0000503483c10190140070300c5081d002c1808075072420b68071001c2c0c0100c1c0042c00e0a80c00141540da102d0303003070715004003c000107a01074260805e409501400340d2082c06402400b940300d0800780c02c0c070f84034072005071801c0c0d204103429603079501d5030b90a00400c01203842907851145403a18030400ea440d0300000c3c40d46207070340002000c1d0425030b122450960007410802c228a0650140450f449201c40c11103450501800c07103a140041c1d4080d80c203000a281001104142c3d055a1500040c44030541c08041525031244d41184e02440054851401401800940c203004000003901d005000401880c040984140c15500045a0107103403c01a1180f6142c10043c50310307056001001402604002a00070a0b4082c0c0000341070228040480c03040d140d10f504500701da80e0142c010350b4090040c04000840c64402c5e1500c2c2d0a141389800c9142e9103016807211410a652103a07440070030091082d14203200a58180c5e100000805c40304102201c400e88030101103908030321aa50104103200e0560181000c001c40803d460034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 775642068 1250 775640818 775640851
    0x4060e100207090b060408011d063106020d020d06140f060f1b030d06030302070e0601050d201c050105010c0b18150a0c09052202031009020f041d 64
    0x8842000301320070381302d243c0c20207820000030803904001d0040e054080c2d03120402c20340c00383c1c0c0617450a05292000d0000b00c00d40030b1a908649010807840b2404c02011003d44d860300ca40c5896280600091045502c483c102900200d0030342507041459100303c089402c99640710181220003000c004d0b00144886101f03905c10001e01210045040040260000701030003400e20766046000e420351461900510101c44a071512074209204040c0c0c1401004002c0412603000041401c080300003070041d0051000c40100d17150b80b100001c0c2d05402c0080d00500300880d13801503aa46400b0b4031020020303004042101c191042c204800040d855100d0b1010b031507141c0d04109580f09075103451994005445e0305078802c5196102e500018440305003d43e0000d8028800740b4000107401000b260068080760042e0300032481181d21f496011020401348203902003072030100100581c0c03a030340d51404c400654003e1300000c0c040f0380f001c100102010120002032081e2840b0000800303608045aa00d0091300ca411966140145c2c000c11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 775643318 1250 775642068 775642079
    0x7020a17070e060406030c0b030907090902010806040e15011503150f03240f0b030c03211c0e030301050102150402030d2f0c0109060314060d0201091a04060e100207 72
    0x9820ba40048000f4004a140707956500c4010341000160049030000c14000244061000200820f8004200304801030004502540018040e0744008240c507014580751030f01c61490705014031070480b040944a1002c403583d40c5071903039602980782c41041080030034984060707410010160301d4100200c6900c8641c6200c400d09564911700c500203000120500030036655a25191100180a40c60040c0b0480c600080c425900d001018500f125001400380070b5000841c4020541c24251007100c400d06d0050081681c0d1660b8891115103407401104001c001d9140c031040001741c0e103020000710f040365401d03800c4a02c03450002d400200c0210003a64001c4d41507004071850b4462500482d220030708042010030400a03050320000e1144101d0200e11050203641004202c80c080b0b6030005014009440180703002c2020984201c4e524107800e0340a45a90301c0b5102d110313851011a881803a01c440035001710b0b2580c0483e00d00b034442124081c0c1040c024140403e0780c4042000355030a00c4144140c0000c01a4000c0c0500b0346000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 775644568 1250 775643318 775643339
    0x70b011e09110a050a1823060307120b030f0a14120a0c0605070c0f2102030c0601140a08070e09283e1c050d0f030f1107020a1707 57
    0x210042000d101c0051b8039640b141c030790010b001c5c000300407840220b21800070700380c49035030b88641605015104038030610500c2031076544141c404500b448601030000300c05282e0000680b40401a11520446110368500d020400030381d042019000900b01c011524440082a04182c603070040514140010b01807414000c0410410381119802c4402401d007804140c510345c603101707002880c10340c003a15541401401100c0c0072200c0c0c41c120441002078801b550a003124000e21589882040c41801c40109260036000d031203956901040b0014031502040300c0e22260f581e0b0407400302d03a5044502084a0007443c1c1d4080100c03001841d0508000300344d400d039800b461140d90b19440b0100d0320f4007880312211a44d40124814034441948003410400b000801712451601000300300207103c42161410039816100d14440c0041d000240c1410300c0841402d01118511002e00100c0081c40071490350310071380b802c1411007811140c00e50000c2903002d0007070365000304054a9607a400120b080030061408580e110f50010444840c50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 775645818 1250 775644568 775644577
    0x1e0309031e032702090702010b060715020c0d090e06010e180a091e11060c0705090408070c090b0906220e01060b03090c0a1203020a0803040305070b011e09110a05 71
    0x46040002c0e10003294456200e64498420401038000c4072000040f00307524004100310b500210a10080c4105040280403c05901070801d00a04119034841c04805a0007190140c800d2496003604880601c1d9000038000c008214504c2011100000703000810320b294030584c40c0a041c504040c201e00e101c100301003001e82d25050003c00c10082a0b6aa101e03560003e400b0384000c1291032945030214403982100d0402c01265030b000d00000344240c01c20071144038030040c041035100407a0340c2218410300c1640d550800c00d10900c00c9050040c50004001e001066690141e4801da0365154161800d11665643c82c040c00058400040c4021580e00c1d0150107031140149034200c0d04200c4566030001ca00c17551b6451818079030350419110440036800c0050b00491509008104000400704101040c2c1041016240079441d00d100040c09018080700100080506000310300722003041e640600300700d8896949034222200e4403045002e29403110080e03000021030a0090080344102a0092862031400d1000302e0240c41e503034807 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 775647068 1250 775645818 775645877
    0x2032d0d0b120714010807031812020d0206091c0909050a1a0409020a15090b070605010801110f03010303232b0605010e091e011502010b0625060b040c1e030903 70
    0x4541d000d8100b29101082e11040c9c0910484040c0000d04507548081d0401400b012580c003103510072810449603c1c0d0005404003032456130000ca0700e1202e4011380443c0c86102c43d03040000c4090030102032101c41030180d402401411400e004601c0c00c100b0305402c102c16a0b0001038040d51240001000348008130001d450210b21520300c1c10607100041d070710141e0a805411400058500e03555910041020302ca01703004400d6074040f200e06061030720310150b900a03030324081808050100001441c540ba5808013810b0010174113000e1840e6a9106d5025003000750181d103c0080c00c1c420f00020f40c0315007850034082c1c0942d009959050316500006028841407101c9640002c00302c12454203c900300c0a0900078500c0028080c16041891021202c007082d0007a00391840d000055018810070030000c800550700001d44210784d007164038021100607036414484003500b5100407440d4814500104803140e10740000390021241e130a00021180341c0079050b4154103c901d0000042d010034164030000b041c20281c003200c440e1105 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 775648318 1250 775647068 775647071
    0x904020f041e181a070203180406050d050d0905061c020918161e08072f0309040f06291603090617060102032d0d0b12071401080703 58
    0x1e03002140c042991511080d90301150fa455419005014101c4113a450441c040c1240d0001424406030080d620302c11039400340722030300941218014503911600104002d0034000d010140c092010705200da140d41a20384900085a801d00000545060440a84820301650064a00e110f90a01003040296004d5454103510044003031030704036041c003031880306801142d28070501d102c041c00c0110003401c190a010300d84500d1a02032001091915440181c09900092600d8034031404821020500307007200b0b0740c1c4136842d070b8403038461400d00d0b03410400009410705070400c0307800344011402c2c00b21601c1180c2d001e0107440d403211300301d1000c01c41c0500c54507600320507940400d126924101341e40c10010303403c02500c2c01c11400a044a0010481d66500c80292031500329888145c4039503081c42d9001035980e02c01c000d04140d00044503044c00d825032400403100890451151582d0381e41e502d405403850700922040d400b00d803090b01641f95400490500140381c90580d54880703008220051644015114001c9c010030381020103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 775649568 1250 775648318 775648361
    0x1b0c01210b0a0f1802031603091b0b090a050105070c060c0c03143406080a060810020301050a080a081806040504020a0e010e0111150417070f050c0904020f04 69
    0x15101c0da40050020103080001150f1107080c10106045540c0c0320683d10328560040c001e0116044040c1d41d1194a80a00d080008a50509280c9041081d1200080c02e41c00e04080200040c41c011160080501450448208404640341c80040d01d060003080702c060620246003805104e41c40c0244001e84200e4012222015540d540b6a101700c42d60b0f00071a007030302080d0041025075001e09030100076031249081101c48410078060840101c03c1d0103105101d0101013080d10b901083d01070b405030b4401405803905105480a040ca200403d90207540280301d09400ba40c1e6001c0d00103070040d000b0070303945200c503030194803140b80192007108614044030907605180e0140d01040002400e98480c80100740090142e12201d6000300080c0c00500303981103109109041c002e4000f4502c510200110341840f021251103000340c81500c4e00d04007042c8004030000e68a90070080001c00d9002d004840b44204480b138841c1c02100d48028a074400e00c200c404081d18000d4000380740c080c40d02d0343c502d010340000c110b03108055140e2905 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 775650818 1250 775649568 775649591
    0x51c0b1c050304030c05040908070221010f060f050904080a0e13050726061503150904080301080f030f0414010c05060703020c060f010509160e03060c1b0c0121 70
    0x4000c030030201c0c1c103907000160400801c00ca003a040c134014102201c0400401900c1d071584600d92103910002846003000074052989030070180171140e68002100300803c1400c0c42c8400d480c008040500440c450b081ca10007000600d03141251041d4412139018854904090a88200b40d0344802c400107820303807183d000400c00f100c80d0840e218079846104295101c110b10350f10200740440244103824285000316800b000c00420341c541d082d18200c1185854510340c2c2c2c80da04c140c91640f003030482c0b8006590100f2418140402e00071500b020318180c4680d881662142a44401550740d644241d40d5009040f450500080206070407a04840301600302c1070404003aa60f00c1641c840c0d04000d0b085a211002c264081030f1a03408407800c029040d404100903080000d95410100041c2103804020a070341c80c0c41d001c0e9020b0716500c5209075911480c88002030103c03115403c10380303200606504921150080b20f0425000d82204400001d04070600301c034103031219181d80140002814900a02008085144d070301c41010844 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 775652068 1250 775650818 775650859
    0x70e31030212030717130c0506070201050412060e0d03180b0402041d01020316091208160803010312030f0b090109020a03020423030105062d01090815060907051c0b 72
    0x4510b84c0d681c1c590612080c1e0b005010f25000e8058070901c90002c1102c2d24070002503900d042d03001950740880b0165100e503450710048402d440340b50403015148242444040c2005201c4d00500320502001c030030341d880322800100850031070b210340c0c200141d10034080c4a0803011455099034550001d002910104042080903000060038070030031641c0d00a69400010000003162500c520070780d071191441c1c00c40d0f0151410340c14044054070001c02505108002070036015025040d240c078910540d02c2103003503840b036075a4280107a200030b4922004010078206654410310141c0c5109084010100404002c6241d0800203584000d401c4003484d0000d060382000045400c590704403008500d000003440c84000c180d5490305041c01c1d0340c0040d216a02407204806014030301880070a031951414280e01000001c014050012520b0b04c0e0a58401e0585000e08100c460484c0c200303c180a11524043d210020ba640f40d4500c100c8041c825101c0e001c1219416418400102c280c80e004000007041c0205603900c10805800c4021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 775653318 1250 775652068 775652071
    0xd110405070e0a05030a11060a09120f1509020d03031d010e1e07051c050114010e090105160e010c021f05030f09010b0a05090604140108070e3103021203 67
    0x2008605810a500e2051a2030f10800c0090034040c0c0103080509610b640d01300f000c4a4151155102e0800402d50131542c500c90b0002c10010300c8100b200d00c4940020b802c01070754202c00c1500988968110181e4854110b070f250140042c10355001e0b00044142610351021001080c08000015401c401c040c610442810240518070009a100014149070010002d41d4603c4140c0000000200d40221404001c195070744003011028129480c440e802035515440c00f24010042004550711031000c0380004569940c08004052082d01194020010303a04c916035801c2d00c003c0f003107402100290088400d003660794442c4181c2c0186500c0604000d000150050f40000100c81000c079034000104081b0030408807408000c240c541000709607008000c8440c102c40807600c4014540200790040d00c0e490086081c82e01d070355000070911660842641c2c05541c444c411a526461648103490012078800302103140b80503400405144004c0d44040880c1c00000009160340d501510f1800b5410b40c05080749003420801c3c0507000b035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 775654568 1250 775653318 775653331
    0x290a11120405010e0d0f1b090c08070f0903020604180e01140603060a060f06050f0c0703150b060310030f0305160827010c1e02120d0206061804020d110405 68
    0x1240ca69007408001001c940550034040e05c2070ba00d06900c6004110204803d180312078000410b10184040010402586070187d40100c01d454a80f845182003a9400115940102084ea4900d0740400282c3c4045880b07100500020713500ca40100700803c03d40c000540031a141c50408400480c02c1d41d00220310390b085442000031a6514101c40040100918062050300e43c0942068420043d00d800d05401c0d000302d00d0140036107014000000782004c60050960103403000d2007a0482190140380d220b00d0520b0510911484001044e41401d41c1d0300c9451404d003082e6840750100e0307402d041e9618a15160050320a105010076000c2c020b00300318a07881c038400000d0424004d40101c03080b669510305520764031210045402c007031845030801c07002c0d485903a91141e5070700c4009400c003001b202c003c1d0803541c1b01400c0184c681c0009600000b07111060f9500d040110701d081180034070781c085e0380b81c0c0e1b6190400d2010022601c201071040c4580e100c0080c1c010701d007520179925640d00841401c40d0715290b80001c10100d17a019540c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 775655818 1250 775654568 775654603
    0x90a0b071e0c0c060305090c063f340c02040515010518150708190302040b0d09020307050a030327050a0e07030b04020d02030a05220605060d02042301290a11 69
    0x10990f03000701454042c030102d8244a0701c41c0700104ac00c90140c502103000d41841d19201c0e10328000b8015480d10740080a40442c03051468141060b600d0001c2c24880c04540200c0c0903074100f0000400c030300e0340007101207104807040c2c40d111304d80301400d10f2050081c0351600072241d21002441044d044408544060b20380715200700c41c0c10f9a0758010629035042020850390010801d401000b050110000c1032050b22806a034040d80418842407510000c4d00702009900301c036800201c2600c001040c1b40d03008070130115425400e10180e18030060030b58180c0d25400c030790044542086815000300505070110284aa010b0842d107000296102400c000805aa01c001c0075003c00e25000700a00100703403424842d2a07000255804150b010920044140154500d4000c024141650300d000040c1c0685902c0314941006600031310400c070702c2103a4075204541d02c4070020201c11848114001040e5518499420381c03003c4811103105442404500c40044154000d000e048204440d150900c071044004101c42080301e45003848 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 775657068 1250 775655818 775655857
    0xa0219052d07090501140d02240d0f050c030606030c0405040204060903032c06090a0513021e030702030d0b030a0203010c03050702010f060e01030b090a0b071e0c0c060305090c06 78
    0x10114078110701c2c0e8018140c0c1c0380c40d0000410414540007404000020207480000c110419800080c1100c1089035102a5003004010303c0303182c41d11048018005e50344142402c001d00e11703c00b50200111807003280c00d030040030000c0003c5566898184040d69001c4190760055107040d4035600030900b0b907009944000081034100c6014410903401c03000309101b00c4100859a0000308510260010307203503d0080550051000040b60b07146a150303c8140e401038880a003080c2c0d504110040004025440005901c40c060042148441c0c1c130302c092412a17002d0100303a80190305080110303281d00c008204404095501d48a00950180142c0b028011600301c51990703140011a403800c44c40203820f40340407810b11140a0315141c82031200c100c40c80e0182d0305480d0003402001860741c4060b0840d00d04040d980d00079042c82010000c0001059000506500c009000318403110b0441800d801a41c00c0e4194440080400840c204c090040610035030215500070b030900c04030b44c1710400c044089122940300c480c0e03008910400d00d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 775658318 1250 775657068 775657153
    0xf0f03020d030c0203031b13030204090809090c071a101502010507020c040605010c06050a090c0803040612110702150f070c05041803020d0e0112140703050a020a021905 74
    0x820f00840e480d0310f002851031490311809650b00d203403419020450309071000c142410f5002811700400080d40d4050010000c074101d90400307000c0c0b504059000c13441455000006850000c244040c0e0740301ca60b20440f05800b00a080020914181c0014140084110140303000111400032040620250707003940c000003075034240082d00908000d00303001418040d0f820300504201c41e990242c050034a6a8020b4000510341e228516244054039101c0d0014064990800740440c0004c808001001120b0040d160040c403807582c250a10300350740041420030700034902803024401504003201d4000418541c1000585803101340b0b9803035441c0e074205020583d5010b003882c8040c03003070341400c1c40381880ba4028506000081c4541e503500030350300d40740c1c0314240007042951380761109540d0103020b10035980d0b1a552024407203c04180c0000e013164204880c2c000000c0d05002c0442c034002040c0c821118030610660181600c42c01d1211400740400c2d45e5241214140704085401d40078446060741e88264004045a00341040c0042 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 775659568 1250 775658318 775658321
    0x3100218100908030f030c040902040b131e12033608032803022502010f0309080417030c0304030b1f14040b01050c07062c18040f0f03020d03 62
    0xa03003407900303026400740140082c20300041902c042c0d10880c1e40003650380e555510308014a009a40c02421001e00120f00400c6014044010702400760030440d900101c1c43e80c0744040754002483c0b40028400150100e070a11403c000040641602d5010341440111409007001d00340ea195441645848100320441403000d4181030b00c47c0c5040109003920065062000c183e0f002020b05546451001b2a094044440040c00707000b0380540d1051900e80900002002440c0c04903102005503403001c80c00580698110340c9001d0180c4601e60348550050021414107082800e034081d0407020307401d4809248020f120340405400b0800051010358031130780402d1341030700300011402c0c000c1028a030114044450340d1030900040701c041c0440700790400c1c21280800c1d41c2507401d005136424460344010781803078003409030045425a00302e1116000c0c04c616014200141034080c52109440440503030740ca6000e07024806088a20030301c440c40b5600140540402c030401d0307115591301c100e001c800740021400b68020610f40400c0070f806 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 775660818 1250 775659568 775659589
    0x50702090c0d140f1326180301090302250e01090209150f09091003020409050705190b07060c03020903070305010f0b0d0203063c0103050c0312030f0603100218 70
    0x141801c0b540c03a091001c258218290300915461130081481c100380d041c4100101c0d01c1031061421b44d044202900701e02202011580410320840c000a580791410a80c0c0c01c051180320140794141d030181c880d110b04003d10100c460040b5a142141238080c2e480841e0101031070020ba4001c041110005a0b225110018000c0410704500c094002902c103100c011032462680c0d044800c564000c4071401d0165652050506000915400213500140f42640c41ca080180000e4500192007049900301c80001340010341c002d4413101c0d40541407809006001010000e4801d8202d014062240c0c10054105090360000c20f280804680c019503250f034560304440810486841800c0b44010242c600e140104210b03000319036034401c09401c204c09190b100f01c0c075001c0e440b00d103942002c42e645484030709031003000c580e5a8800122020b01040d00c1c0c1d4040c08072281014980098158462a15011207605603640c00070380e40c60700e6800801c01505805110204102d0040620042603c04010000d10b00803400010034412440107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 775662068 1250 775660818 775660841
    0xe07031401060f170102070f12091a0703031a0411040e0a050606040630060e0903070b0708070212040b120603060907090c0905091312080c07020f01050702090c0d 71
    0xb61140070b1002c0080c0041400030b07500c242c00414003d0358950a5280244540314014011940d105546c0c1d04201c00402d1102568640b0356400c10101d49518900d030043c20710607018040000100502d80000c0d0198005c150060b1104202520524004020505584c4440000b5211100008047c0903001d8041069508034501510030025441c164020442a1041d4002c900a014000044014240c0e584c5140f402c1c103074001d40f4400c4c4c100c0702d40e0500806000c45009401c85c2c8042c100010742e05500c00815120000e4001f1104407960300c0f01581a0340200c0040c0402045006103010035000c0d00c0048010401400018400ba03038030410202c0c0108220406441e9600c00c0d042a41804a1804002141d1f015181e402c1000a40000c0703019003504e0390540360788040c1c0c000d2006001c00880c441c4407144040000e0040a80340020310320b118040703440d07079000c407410103031403034207200e0304026041c440b00d920481101814620b2130490301d50001001d103202124420481c24001076206c2014090f8019107202e8003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 775663318 1250 775662068 775662071
    0x110303180607031505040e100f06091a0306041218031b0611060a0b06070b0115110307030804170c03030f090d030b13020d0b1824010f110c040e07031401 67
    0x1131502030103901001510489102d1030300d40d84030161b000030031700040742e07e610f0354101001600303007104418024004911030701e04c059103400082d020184509400c20342c0020000c02078090b60303483e80d0700d40344540144d050900c204060a40c0081403034001d90343c010059809181c002c4d5400706043c451001183c81500f0103400c01c071413802c092100d0500082c155410001c1c0b50400b081c3c02c0c164401181c82806202d0740504030840c0240002041e9032035030411440c80d002551800c0c03c13000ca18080340c0d524410200010f00007100807002078041a0868440e502110684500c07500d03100d850020140b558100751101c80e080a00c4c60103010056004100310340c2c590009003400c1c421214400000744165000d0140740580c82d400040e4825540604d030310183c4d801000a001001641090782c1c9868040c50403103148040720004040c440d0b20a050f04104d0182c0c0d4416510240e484410210032103005800e0f100301d002038032a207030b1012600d0781c0354000c10a2400da0f600091001c586182030805109901441d0390380140d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 775664568 1250 775663318 775663331
    0xf1a0705040e0f090f10020903120313120e06040305150708070905040f110403050a1a04021003090c0503060106050a09090c0507030c0c09050a06031a012411030318060703 75
    0x300c0600b42d0750741c4030b5078040c60440e03d81d494112080c1440a80300c060035030350040341000851265a9800307401a0001034003141d5580241003d83c03030980c4419241480705850144007980010503204580c1114110717460701c215071610403030205801d6000354100300c441e500401c2c541c801e10405604100e5000d101840c102483c0d0a008002401450150013450300a80c0c60b590001c041000031f030000c1d400041007004c9556282c0c0d40c3c0c10000d1703c03204e010038103d1750004004814142c0240182a0600603a0004d1201521402d100410743c0101841d0704111088010008009141d5406000c2c050080120b078542564500820900522280030703030f048500581d10701459800c03400e0b4071100b603607416940340c1040c0e8042c03251800c04200224281d8400c101c1ca50500c030030008064210340110045078449c18290042407040c05580e4100002400307103445200301c56003d101c4860a0102681103282503050850708121480e01c030380e08680c0201d410610040713071640d40300c8140c44104580c5030712040625080010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 775665818 1250 775664568 775664579
    0x120e030c010e0d110303030108010c020712020105090108040219030606060f0302030906040201110a060507020309010f080f0c25060c0908120f0a030e0f0703150b090a020a0c0f1a070504 81
    0x2c04228140c09805044090a410300700481c080704240062402000c8a40343d40c0d40f03840060107401c40b110b407000180541200050b0040c480c2118410255058541ea81441040320044402e030304010300581c2d014010801042202c84403c190b24055401400003042c0d41d030400201400d0a903020300400300f050b20400800c08602c00c049042d64103e642440d01d90180700c82c07401c00519044800001a02051500061004203030700003004043c41039080c2c0301c0c084180081711b41640d120008039101c60a80c1d84c02d0303002a4a00388620000c0298007805c42c3c0300803440d50040d0161010b01010902200e20541e1002c0030018140c0000350301000700310703040040c00d14030320208403c00c0500a152001e21910008200c1b02ca0103802038101c0400b80001e1001c55148801c80700d9101e90b504120310041d5480b6100c2003925140c88618080e03400e0101014082c1841509c8004001000390710001c40c130400c102800a10f1000510004200030b200760241004980f0700c1d40c5984840c0a981c0d000c0c0c01d0780700744002000100030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 775667068 1250 775665818 775665827
    0x160b0f0709030f0809030a0c0909050c09040302033a14180714210a03031a0a23060a082d0703231816030c0b030c16120e030c01 56
    0x80c0d15502504e00c41d1a000e060303000c03a18001340ca50000700401c4401c43c0c00f00f070070030080d4001c603407240c010350864592094403814850705003400d580150041e0000c20203207000040d10f25074275041050352400e4202002103504107800094a441000750302e01d0b1a03005424122141100254100b0b401c1001000c0c40d100e54426a80d94154034802c420701c1500c60164045966030f071900b0020fa40321042c00ba00d201e07116030904c6941b25071307042000310007280c030303041200300740300440000407101c0c1b80d02400c0c110411342803171903c003221090030200800903000700320503000f942c980c20082c041a2880f9140c00c040d034108454519000350304483c072000422001c0340303a1681c5007542401150000441d040000d69a44401c0311101404c00369442030700c403104003800380500d048484c1d4030905800c041105684101030005603840038504e0301d2002401e203440c0c8150034010002d80303800031034005165139003a43c6040850520220043c0580c0c80a44074001880300c103003078458101c0942c0780c002804402130244050207600280 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 775668318 1250 775667068 775667093
    0xb1f170d081e010e01050306161b060f14180f0307030806030c04060806160908030301030209102409061817010603080304120f091a030705160b0f070903 67
    0x50400000901044000342d0582c0000c0541c1c812150005032503071900c041d40c46004080c46190300900c21007002a00b507083d030b0258503403c20b41c0d542c0e80345021040604003419000d1644401e03542030b980c1e07a0058042c9907041c4074119402000145558075482d00303da0300585001080d040f090660496203441900c1c00740030084400103a4035003001d04503502c0300c2c804245050044600150080e107007170320105e0010000150280f09a200c01c1d08151062500300c400c036901112841100c2c1140d0061006000518040310040d600484c86907116000a0352500c080e2031940000c001d00401501e10341c15403840c2a8045001c102038a40b134145203c41013801500d03407003415001d10880c519100c40c15408031605000303400c200000d513008030341240c481c02e050500099070740d800c02d20320001c202d880350001c06075400b501c0b1102c00c44510700c0204030702920311100801c1d00e600c024442d00411004000f1203e00300401c040c0f2220f901e00483c1150b41500d0911510728520034043c1c84041444444442040020001000381 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 775669568 1250 775668318 775668343
    0x708031326010e0a0611090307030f02011707081f05010e01180503070b030105030606010912140703210e010905240d0212040302012703110a0b1f17 65
    0x104500200c40c050764840500341039001540d5080c403070718052200300003402900c140d001d424200040181b41075604280d100e0564810b8150304460410000300c1d0072a060887d00034018100150b055226552200d180d240489504010600c90814001c00394656440500e900c12440c035211125800d00e400600445001090241002204003840b00141090280d80000b40740c0682111915a1220279411140d0400d00034030f03019110b00c1c000503405600c10040001101c0d41d007201f1400d45a1035488030080110260b225000300e200346034000000501120000392844584121344501c0003010b04c008128074403100d5800e04001960b85c09026036668184415648000008070420f500d02c000c240700c0003800741c2c03100482034510105840399280421081244194800d83c001c1010035044422020f904410383c5500742c28800d01001000000d000341d69000c40c60039190126925003950341e464a500440882e0290307007101c0d000420f0f09050720141526806000030005c141c601c4092000a10b58440d2080c051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 775670818 1250 775669568 775669589
    0x304030207030b0c070311010902090103020d0c0f06080a0c0f0905130608060a3c020a02030c060c090f010e030d05030c0412050a030f051206041a0307120507080313 72
    0x10404140c02000701d40001c40e03010f4140030403032804210703c1e00c4541141c002940132a62002c01d5090700325042c030540f901240d0003007800c00241d083d5024000440c00302c20b000c65220312114808100c00b05d5041000e001095513640d951058503040e03e401c011b84a520300c1c1074040c464901c1c424958150440c138140f03780c07081510304444d50a6803180c040050416070380b114409005845c1408120103ca0300011420085614007550008016101c1185d400d26900307007005024241c8690900100c45400a041d10502c52044038241242c0d40c03010741c240001502c94046440300014107074481e0030b00310301c0200603071005d0802540f06048003010a0302d405001000c1c0d030402c40e0000000e6445c284032025075001d400410f001c0b924450b8580703000c695a14414106402007088000500c41592042c0c08940b056085642c50039155180c00080c8000b4111120b8150811200d0003a01c07a10f644041101100400c0050b40c83c020f81007043c2003083c01d03c03403075800c08002d075001000200c0c0c4003092500b004d400c40d0b003c00b04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 775672068 1250 775670818 775670821
    0x150906080d1b050a0206094c1202090a03081209100612080d1107151118010804061805061006050309070e06150403030201200a0f050f090301020403150b0603041703 72
    0x81c24420f58000020300312092501032400e40d108681d0803d42c19044642ca00d50003442c103040380d4040c999880e5108001403450f2840c15060040c0d9002f904001502030a0100348a0b126501d44045400c0b542d1000d2a8100c403200b0003400f501c0c20845076001042387d4004014003400e004c003940c0c03280c0800301f025285010014051048101a900c404050b0040001041e2039007139034604030b0141d0313031000764810039541404c1165211001041c1140c1c01591319100c49508001000015102c40034010401c3d1065542c2d48802c514020400082100a42c40780001d090789141ca40000000c1081c2504034500300711050040056000002803150280c810190764181d03250f4034207000500c600550803d01c0d1100c1c60207d400800c0640542005444409011902540002000c180741c00340c000e8000b10400128061032024405001c0c10007880700c0f80d03500c0e040b285080410303800b1900ba81d025510440b040851062420b030000c445228042e0002e50031a0b00170f29505190b100d02103803890206604c468040c0010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 775673318 1250 775672068 775672087
    0x2120a17040f02060a080a0b09010b0d050403030b090c0702010201060b09090103080d02090301021c0506090f0a0f09140601051008151c05060f01140303070c09150906080d1b050a0206 80
    0x41e0740c080c2c1c0b5402010903548040e400d90041c802c6005681d48850682400080c031200e140c03158115060300e404000041c1481901b0144002406000d04240d062682d10f00c4000c03e1034440303000d00d900c82e0442070780d01c2d59500032a00c0020300310340e1640d010701c040c03882c180030080041e600c01001d13504694020480907200d01011001343c000b440b550070165815807000865000c942d0340303100c46007a1025003110800040d610301d828490480300c00c4510703504081504000074000d1440d46d128498039618070707000041031000399450005804a1400c160340c0d5500500c01000540b40c0702288071540700300c91a209000b41000c01d14400241c0b408040144130307a546110409003403040c0042103162907000021502981008103006000074030a000f024040281c0110b07010150074008200c45045a014102102080c50440444001d0400c00d1890384003008410303002500b400b182c0110b40140190034003030000003000200180010401039a4042d080b10003130741c540d01150021800c850120f0b0182d0702d85640d1507015 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 775674568 1250 775673318 775673333
    0x11808010207110f040c0c1b0f0801090c151e031e05160507020102030306040e2b0909060b09040b041803030b03060711060408130e150102120a1704 65
    0x1a044215250300c0480c0d11014449000651404aa4150703080802c00c8401d0040c4020364400101c0da10105144400d1240020140d2520901c01c0302100c41000b074040d11400703c0307039040015512641c8269184c0030003074144446144550010091a4042c0c074503029400c002a041c1008841d003d1460030304021000107060003074010903804c1da5100704640e011005c0001500044c40c1c16100521070a540c4448441807030702501c00c4901d0745805030019825640c981007048050300b64400801c0d017030300407288000e034520324050040b48002c0c8590144803042c2c81400005118a18541c0700043e070074140242048030725210000c4405d07000d0300b524045084a40d4001240160101030280d00540039042d000c031060517410390240486100480c241c0e8295124114220f480c080001c40802050b045000401c2c00100c00304002d000d90b1450b500d42101c15552005a200621400c440c94180e813a0f00c40c00039030166905002001095a88a140034180b10382000000c002e07803100e10306805080950000f00d0b080c080384 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 775675818 1250 775674568 775674617
    0x5072003070905190509030d0f0b06090918120c0c1801032307060903020301050618060d110d03111005091e010f2c0601080a062c030901020f0309060901 67
    0x898805d2100f81040d500c1346503250701c10450900054904050486801000d01503001264030007071020307045c182c40b8020000401c60280c0300103640300210b03011500c1d0b4007092103080890210100111f45502d8000505410903c1c0ba5078000d2155000e00003000718145003040300c50540e034200480c801900042c8043e45e100d0181401c6039400c500c92104c0000d065070b8407251070004d83e442a030080c081900c5007014080041d1070f4401001c03618118100091040c240390301c0c050885405055040c21110b00d041c0803800040c4108400d4002400250505006140c200080c1140c04210300c010862440e00c0420b0301d88480c030311103500b05180c101482000c0c0000342500051070001d03840c4001c002c1019003400b800b400700c20302440f041710b805007074585040070403002c600a03040b0b40000000d0040303401a40d850a008090010280c0400380d0b080c481c01c0420400c141080d07841710403240045a407010503c0002e40b800341000e60150b03169008200000c41ca03120b580c06d80754591b5003801e120400038002031651099081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 775677068 1250 775675818 775675861
    0xc190c050c090a0c020f0105060f010f0c080d060e06010c11040b0117160e120601050d03031e090b0c070c0510030227190b181f05072003070905 63
    0x40ea0030520035009150342c0302c0750480e013494003221180001e464426003038510803078031a81c1c400720740d40b0410500e500803040d0720010145894aa04044266514029141c0011036429611560780f130701806194a080c0f0f100350481c8007402d2541c2d00e00c5c6a9500c4000600a004850f4003035900c42d0855103081c0d01603401d032080201c400fa070b0455240350a08505a030800d1203003c0784001b505c002c007100300c1810f10343c4584c207101600d90042c5c02240e003004107000522100d50011001c0554852614000408400101c04214030f000c402003800301c2d02d070400400c00032010380f203217105003402c1011800251106840301e040391416202c018044402000030350003801070001c80d9080079110b254001078110b4031217041c0c09110b0102d842000e074840c032910840d40c07003e590090280c0030400f0000301007480000f040b02110140d00074028101d02014522074070a06600f01c071098082907003c0307000320420a010b030742e0244100ca0180c52416501c04100007039a54406413050701000ea5032000072403030300313800d030050ba144402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 775678318 1250 775677068 775677079
    0xe04022206150503060a0b070203030415051e0a0306050a08031b0307021f09090c0503070c1b09230c0301030b04080705060705040816240e0a09090b0c190c050c 70
    0xb00c101009450f0340d10403101d46100e11038140e008281e40c401c01042c0c0300295005001142414100514003250f41041000741c002d01c42c05200100344020a80c604004448042c11115282c031700024010b4141d8403070b42c00042c86181c82d07c01c00e10041d03100005941102d40400c50344018920300c800074904610440e04044d40100101140d9040c4000c0000003a0710b00c5204e54401461940c0c07102c4410032980074080300c100040c81080422881e51158002d0b103640c1d4081c03060180381240105100e04030218036070001901d152290100240e80304141d81048040c140e10000d01c40c2c0d8030306541103130b08902c0140002082c041300000445c040c4404801a2540c00c1d6020046880c81d09201c00042d016070020b100e03102044c0705c0c445034814582803981c0c40707104488030000440520f41940d007481c1d041d00280c140150801c412204003140c0340d5900c02a4a0041002c840005407048140c101059120030007400780410b41c4c400c0046600d58409001c00c0818a209450f01043c141c44034500181403000603d80c031540706 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 775679568 1250 775678318 775678349
    0x16180b010c15021e0304020915030312040c0504061a03220515010e0702010e120904090c0f03020f0d2f040c03050f1006020307260706020c070e04022206 67
    0x5019a802070044038441400a10201d01c41a804e6107030384002c4800035041082e04000c10010307050241d4610b00040003c0c00d8a0602804414409040500300e4054a01c040321200400c024200361045070040c00884541a644860300302202065200c0500300d00344104c00c4d0980c2c1200700304107011003401260f10805407001c400c407400205080110a000b0240c1081e0200b01148983e03005118903000303007925801420242e0003045902d0300075007050441c035800c6910f5854031030000b03450b5030018000e00107202c40e00c0c89003811801170054820310042c07038a0107194000300700c0c004140205c400100c0704403101318609400700c0d90200341b070b0007108214207160064201003840b1403041e0507401082c4a0f501e030035139080c9113558445082e00300480510528004d60401c114081c0810018040044000c03080c030b6a07010104010586828161b00140341a42d540758081084c055003034003882100001c0c038440c48006160305140d0009481c80e80e0b12222041a54280c10495409030304c141c10481c0148041243c0700c2c2c41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 775680818 1250 775679568 775679603
    0xe0307240201020702120a05060a14040609060b18040b0a0203091e0304030209040f020f04060b07030e1c0c090c020636010203400308100308040f030516180b010c 71
    0x1147c4803801c04413024000c03032001600d00c1d4254401d2124440000100251a4403135480d04401054054000e0719031079242d0390011690386410307185034114107a10584a410349000e040c26040c0c010003803e010b0350a4010414413056480001c0c400421000480c0740c441d00000c04034081d403461056a00c02500306828208000178411441410000c844c000e96a0f03000a2100034100030071186d06000c0c4c0c90a18505011003800700e0310a2080c443c0e5444080d00d11246800c0808900300000040c0c107044414024000b400e21040b441d0740a441000e84081c00244101c0c00c0001031001c450780101c5a6402c0c0c5042802d403001c0706000f43c0700c0c0020694255008565a003405200242c0001c44485403003003041004030840d2030002e5241200041c0c0f55105007a242c1c400f031a5400315507c00f03000d06131001c03c00c0c00c0007011010840300030040c00184580000c1c07409840c0b0314642503040940f2601c0e9284500d202e00c8007004801400e0101d030414500050b80014003881a400688010400c0b14020300074040c0c400e402c0b6039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 775682068 1250 775680818 775680823
    0x10020a1703073b180103230a02090708041a090601061727070305010501150306090e0606040f020c120a030b102a140d0e030724020102070212 62
    0x41d501035038501e03004403801c000e80d8030600b00d0003043c40300c208811200034100301100c252203c3d4110000b0000c41010b00d6000700004d002900380c205071250345103840399100c0c0c10448401451030555610181040b5012600000c0c44208001c1243c4140104240010100131000144032030204078801841c001c0d040c402d0708580e444100740982000314911a0707140310790716400582c041c428000c0d1454020440000800d6622290880c00003926a201b41003000c07000640c28081c1d103000c0c000640001c40301000300980182501d0300d5a00c184045840c040c0134000c190300100b100356200100b07450200e18040e440b50050300030701c100c04514520303001c2c0035031150042c98440010140d030b0b905607409224a41d03c600402280300c0b19075544070040b60f5a0302c515042c008440503a40c00c410031500b09041010440d0710303054004030785404010b1464114000c400c0005400c8401e00b400103a043e001482ca4038101003a902903030f015000d940c0e031902d0510b42c954001358801d4045440442e40602150038050855083c0e43c1d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 775683318 1250 775682068 775682071
    0x3912060102060106050f0301120c051512150907030504020f04060618060302042301051606090b0907060c06020702030f0a0506190b0f0d0f080c100509150610020a1703 73
    0x500602402d0300014601748544256101040e0f0400302c54956440c000600d1010210720303030704032451004580d0002e026130700d2200345542e020342d444985640f80010454400210b030001c140c004817206950070800244c89000483e0780c000c0140c100010981c4481c000a03d040388014801544242001004030705664440c0c21102e20120b6213068113050b82d00c40806400380c1c0990b01801624075500f5464081e01201d50880041500b8181003851820800d0055040044070034001a10030301e4940c0a51400c1252403d849a8443c11803401b030080182040f00042590340c81580c041c10181e0080f0300d0109541c2c09025a0801ca0402011100c4410503440c215884a83c101ca00440500013804c000b840b4044c68020075501c10401064001065903203400c03c22200580d004c00c5d100c01040460002c000f4030342c0300c018501c81032084014040c4090403000c200544000400107813442d00400d01c10b28800103144000751f08101c1c11582403040008a10080b8900380d507810f40600f0303c0e5003201c00301120340705c0f010065 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 775684568 1250 775683318 775683331
    0x9020a0e090d0e0301020c0a0b04080c011d0d0f050a1206080d020f100504080901080703020d0906060906050102031806031e2401081e090a050a0c0e0f3912 68
    0x280c0e483c51041500702d001b542003c58094111110000c00a8940c0302c440d03602620034084141081c00b183c0e0a1403c5508440003400500d5034003640411100f010402002a0700c16481d1020071803c0c0c8000c01802d5020ba100c1280074400c400d44524900b0080e9000003010301504801c9400c090641c120080d074880e40301a9000090081e00b4104d1040030b039030700805200d15048290f41d407400f0403038001100c4010004100400b0186c2c02d100340c091207031242c02400400c03806602c0108070b103410182c0b1001210410b600c0241513520401c0540c10300720031040c0100c4410400c461441c0c480d902c5641e010300010021f181c43d071800000c01c041103200281e58101d555040600c1110340e1007806400c006442a000135a03600b10300d072034400030525401072507000d041d0380040b681d0241c0fa1320200c00d564043c58031529090031100c2e0022400180242d03140100c00c180d01143c2540744240c00e003440d014004003d15200c030401c90511a1894441007040308480b1025001c4182c03001c0c0d540d031010111044040034041d61803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 775685818 1250 775684568 775684577
    0x2411101b03150e010510031b0c020901060e09010302060714030412050106050d031b06111201090b0303030705070b0c2b05063015010608012c040609020a0e090d 70
    0x25a140010640b40e000e042c1e80f000d512020a5900f00820084a407407242804000c15131991840e0111802e452441c240c49240c80c0c07201100604140f04000040005030020810170400c050715000304e03515501041e04403034040d1a079a0742c0308031780d0078038510080301c24012030820b2000140000d4000109910100340f180907000801c40b0645035002c200304400e002e440540020a21500c200d80083d5101406020754451000010206000c12120f005600003004520401505400402100c4d00c5401010b4801408902443c034500c1c044002501c2400b0b484005014220030100043c00c042c0103804803002c80440180c440070804e05410800e203040a1100300d616064240008142c1d41d051803031822440078200900c034030254002d210240c0d2110014004010a4400c00d5049415520103c442501030500f51392108002d60400c40c84234080351a903a040a190090fa0000c0c056444000d400c198009512a901084200e501c0c00007400702c103402c0e001162844258414081c0400c2c001404958410307982c2c54 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 775687068 1250 775685818 775685831
    0x60f010c1416060f030f06050f01030e010902130e060f010e1b13032009040b01180b040f0203040b0c120408090111070b03061c1e031416020a2411101b03 67
    0x3640300a82d0840d22500c0d801aa27210320b0495158000d8001c0e0481c049071000003d4508247d80025052072411008203612541d02d6100295000d000c1c003d880e070050540035284405e5240110b81080c3c200024020301d803031280e00440a102e0000d02048845811143c000e4208041e00c9040c5481c10038003880617a00712400070181c510702c40c00c01181903403140c2c1d00825000a02d03031a20482c4460039202d40843c454040da50528101d0550b1240301d186070003c001da2005849250502d401d840381c8c0c0024210b4000050f05000400240d14080e54041e44035501403072051700c0709201001030b2401e29a00403000f20a010740751020036030303d194101842c41800c0850707801010325100c00e4002000222460b01a013515030b900401140700000400b0701e448244030f440c060200c42c41640c0400c4090300107180c1f104074409410744800035480c11800303440c0a0040c01d4500141000c000403c400a5241d0b01403e0051000c0c07401070b001c4012050103000140c3c4203040b401e0250201400b03c1100c402c41550341c03100400d1070510b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 775688318 1250 775687068 775687091
    0x70c091112070f0f0f0c0206032d0c0304110411030702100b12030d15180501060e090702190309120305030a050c040302010c080708040902070807020108060f010c1416060f03 76
    0x240540f180b405a215401440c00d0010220345100200850400303000c0303800682e40050300c540008510a0300b02e5010507100f0705034100c0342102d0304902c01c0c02c80300044030001404a50205042144e8000e940206400c21450201012030f0180418100c156103007a4040104080141c011802d41041d01c2409c80c104001041c90040010300e21083e643c5800c50f034030500400b80e0040382a031140e9034150030081e5841419648509100070098500c12103010a41c5800042000d20340058030394110800031039100626140c8004c00958039032200300000f030720342c008000100a240c0030b40001c1003d400b07002030a91446540742006400c541c030070380d08000440d00d007400240c0c1144079002907806403581651807054808054440440e03a8100070402d944001c81080001200701240c8010032089200ea40881e483d000140009020840e00900040c0200806881c1c40c840341c0e400314040300b0b1541c3c040207040b802151820501d1034800e4581c0001201032510300702103102908648100341c0c0c4091a90280032149038607 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 775689568 1250 775688318 775688327
    0x91b030b2a0d0515090414010c050f180d020405070f0908070302011e0908150a0b0a030c0b0c030c070e06030f1c05030402130f02041e030503070305070c09111207 71
    0x200400d15405040c0004242d0003040c2d04426000641c5a03202400700500720009920030707905645c112410245004802004002809040000d90705402c00905002103003444486601c101c12214401e10f007020044810360381c0c0c20b083c81c0450b540251040000f854844009444280303000309100c0400c1c104440015081c078001005800d403a0b040c3c5d6104100103ca144201da82c00c03103464140203020000d000407a4942040255040780e03000a8001e500c10b0400640d040300701c0c1c40324002d15025014804050000c500c1004c28602100c4503c413806a4800518401070300350f0080d2a0501034502030f06a0000b0720619a40e016400381c0e500f1001eaa080d964140c0d0b03615524a854401c000588402814410340d081c02100a19400703030010f4810f113001009908804225204024441c80c49940824188160300300c004840455103164444041060305580381c031035032405804801402c0000c005912010042034004000050655040900003010902071a07200350b0085034074004207000ca00c001a0146103c0e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 775690818 1250 775689568 775689631
    0xf0607080612190303181707110306060a1509050a0806011406130510051b010c0f050414040f061211010f03020702222306030714060d091b030b 63
    0xc222010403403110030b039426005400700603085c080d5244405014004a1708445415504521155802e988e40c201458141020220848400c0c06548003400300500342c1c1310318110005641c01c280c524051075591880442d105143e540042e5000348154100091101d800920b46040c3e0703541106002c40c000026003482028040c401c100c02042650309c0c41008941084005991130108030f10708140b81104051460340320300200a52005103a650702c0846c4080d9034003d200d50140946441c10381d10389131514448042032000031207507610440e6206981080781001b07a110900a20140c422050700b0009402c101550101c03107000180410003010381c40d041148030340300715103c1590091504081100c0c68040e0800c110141c1d03450382100c0e5682c800c2c9258041c0da542c00107944030000792800200d241030428541040391540c0824030503210000440e01680d55402590440031155070006284002810701c1d0000c9030740140e60203000c0e203040e0404007d010748804101c1c460040602c011248640280b46582c00200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 775692068 1250 775690818 775690843
    0x5100c0201020f070f0f0618030212030c0a120b0301090f0c1a0f0318010e07031b0b0a0f030230091609090204023f01080a030c050f0607080612 63
    0x2c00c01900c1300240c1c40805800d02113000d0601080319003415501c42c03007101d6150060441032902c0440c0b803810554104540b02072040700b2040c4900b90706124008070418020b0485400a00510601d82d101e524010b42c0001e021032801802400202c4490030f00c0040081c1580080c2c5169a1507140407130031801080812031011940310b0b81c10301c0c01c1c03003009071801c0f10780028046210004240540c0249800c00340100303c441411600a0030000e403071460400234908084214040641110700b041082210b40380a885103c490380c1030000f020207034540110003d100300403d072288180c01c03400701c0e0b100b50031104c0c800c0d080e010460600300058a03800c96495540500248c0c10280100b000d00901240019400c240b1800e84017800c05130a00740c46401c45584000c0020b240300e20303d030100f1400a103010514502c80000100804040140d50500f28140d4585007040c002505018428807208100300d010069840500d5a2a055503010b01300f14500502619007a0ad00c184203800300c0035400848200401d94004040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 775693318 1250 775692068 775692097
    0x3050709051608091009080415031e1805030f090405010605070f030e1801090905060f012907061d07150509090c0c0f100f0b210304090905100c020102 66
    0x262264400c84400a000380b0f130072128090310134100f038100c41074050000402c0c414491561180c0c10200210054081651102c0405081002e03c02080280b105054600e10b04050b002c80d4459241075000b50080d21120000c11911002881c0e0080c0402c0f880a00101c0f00121014001a6683c01c0111401c0c02500005080d00d2120400100042d0003041c20103c0f03500003820300c0d030440d100081900b80031384007603100c0c0c8400c2743c0728807042c0108042032213803950114442d03000c0803d55040624502c203541030407002d0409000880304134402c040c80c0780d058a2445511440c180134a41000d85412401c440d03011841d1901c1c401c840700070901c0b0b8410105601c160169a41d86400d2490310b004010440d01c1c0078120388060f6108001126014005008101380c0342c0ba204001c0c20300303544004041013102d4000a4400c0b00381d140c072841c012290390700d0301c918401c0502d421480d80d51204a420700360440c8900d900981c01e6601d030800c548100180440d104010f0036003104100b2071844001380c142d0a0f0b219191500c0342d00d2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 775694568 1250 775693318 775693351
    0xe0f0901060225051008100e190504240c11010507120b0409020a27020a090905060f040e1e031e130f030b150f100e03010e0d05040305070905 62
    0x80324180b03800f100303105122503103004442d52030b40031810040c0030006900000d10940308110503412061007900080c500c540d0822a28078200c4048038541800701000f9003926101d801150a001c00c1811450200b0512410f031842800701100590061110103050f03c08641c4001c4900e52006040c89800d11070065516110b400c40d00113500d40004242c03994240781d0140d0307283c1031213025886203620b540250460460f40e03255080c50800c5417000e40c0141101c7e160700f5004200d10b03074030b50768401c0e0014101e5a412001052a85aa030009080d5142d01c009641d0028a002403044280c1d000041c0d024110702c100240d05600100070020f107842e03104441c40d02040c040c0310100480001400070003040525005142c0c81c40c0151162010503009555900c180c400351042400d00190b0482d031501410200c908588111400303110502040040c110000310005014003100c61000a46003904884034180030401030307920f003051000340545550454003040e0f0745403046d10404a060407142c03140358040d9601081c0c1003041d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 775695818 1250 775694568 775694593
    0xc01030e070906090222080307060c1e08150a030b04030c081207020c010f18030b1005130c0315080709092d050c0126070c0f030e0f09010602 62
    0x94040301003446290310031048001514080c2c2d100e100090504107a02603a0b409262103003044d120912104510005003880b020845203a0002c210f4a400382e01030000300d030061001e8401c0d5030307281c81c807492480001c032014040400c081d40440d955115880d412240d0807151488030074400c1250150000809514868002c01c022034042c807401c4443d42e1050140c94540350140e03c4140d017164040e20303070b6000350340843d00080c407a6800030740f583c45900f20791604080c206001c4050203220040c41c80050840d115120100300031007104048480540000780c11020b004582650b01c200420280070301d07000080c070344081c0c603c84042500a40b4220b6004400070b00c0c10030704000300d540c01001500d03012a0715030703106205c50300440000b8900e2251009203907941413441c10907091107402c00500f060b0320350400a0040082000c1040d01c560051803288d2150030000d00e13138076520161210005410081c5c40445882410000c040c0d0240071008114000e65800900c16203201c180046c040c030a0103201c025070000d24603500c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 775697068 1250 775695818 775695821
    0xa060c050c0309122a0a12050c13061e140d050d0315050d121709120d0603060920030a02010c060b0a0b04090f0e0609030f030408070c120b07110c0103 66
    0x3c4c091104040e41d402c81e01000c08082c5e00807801002000d06421007810550500d03040c61000d004000301140c01586022594400351140c02703000341c5c2c902c945001c294034201022540d1140004d417009010315a6841245010744c00c10704e425200e0710580b107071400280299820030803c00081954040003d18000f421100150040c0810444179807144030b440380005566503400d0b1348104a039000303205410350181c0c030780c0700241082c40202110341c03142c68001c1400031500001800450406555400984804184c1010400b130006a030015180030300b480844424032403a950040010001840c0d07000f5511a40010302da240e2405076000780c040390380c01c01c0540c0418000e4010824507100148002e440b2619450004526001900030780e520680d100b0f1186c03a03159451044004d43c0c40094028103035440c11141e400d60340c3c42003000b040903c09021010400b00320700d540540c0c01d003903444801604010348520700480080002c450613104540700e41c01042e00103001d07202091500c0d40c0d400c0500b200000f040300660 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 775698318 1250 775697068 775697089
    0x51201020903031603051c060602060a20090102030f121f0f091e0501030305090102010e07050f060717040603140604200f0d15030b0711030304030e0f040e0a060c050c0309 75
    0x2411b100302040f0b028102c1c1e10141c4255202062581e001542070700305000240782c03500003000c45480301c2c40c0500400d640800781142140141c030801006944101c0200101c0c00c500461610b00788515010802880d6515901c0807203100b011040301c0b1288200300010034000c003002c1842140180749815605201c00c0c1c82503044003440f100a08003c0498049107103811040751301c2680141c0c0019004136010320f02c6e603420b009138101d00c081c3d4801001c619042800050407480c1800903076101d1440040c00e50700300324132441070382d0300441c2c080c0206031910b0f03171a00d0250103001082d1000074010801d20001d9a2441d082c820745202ca44207090090303003c040b100554003660f10400018000c040b003031008198247d1a0f01501041030783c0c80c44940d4074240f0b07603e0800141d03c4040e1170b001c18807440b0040c10001420010980c2c0d07010b50940790078424800102c0c0130400681d0381c050f100e134205040038500404e05400040c08110241b06080030440115008000c445500a01071020000c0d04104a01190b0703140181860 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 775699568 1250 775698318 775698323
    0xc0109391206090b0f1b0403050c09100f03080a030c050a080402041e1508060a09050a030f1b060207230307030c0203070905131412030103120e0a0f0512010209030316 73
    0x1805005544510000400c2158080d1180e064901000b4041d00840c3c1030386d050940c003160050410341903980301520307102e00c410058052580400002c0c00703001c509550200074581e110420115586038201010030f64400360300180030a0600c04407a804900c10070454aa4852941c4c913420181c03180c0d070801010389a040403211103006c100e0340c000040c42061044c806074002080340d03404001d00c1c1008145c1043c20040070b00001038130f455000da0100300c000c00c42680c0c807a0701d40b41280860380440804d950410b1240074466100709000e2802041080d25402400c14a00500600c010003d5103181c1d0010808580e2034510130350002e1003120002401070340ea03001c10b60b2005055034085a180c400701c02c120385040b82d0b140505040403200e0b0007440008050251603c80c1031020749011121b010141c0c0c0300380302c103200041003480d07a803003910075461054001e5042c022000344003110680d80c408440760112464001c051003140da0f0304030350f8040d0005100b111400380d000380143d0704000c0354007442d0059024800f0b05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 775700818 1250 775699568 775699571
    0xc0d0305161e1104110f0c07030803040305091305222f0a09050c091309021e040e1606050913111806090f0f04020c0109391206 56
    0x210400250016564401610082c2000808035590304000b11902d00e1000c0c0749004034a82020780c5440000c0000300d07009806404101c643e1103441c045a94581451a400030f818200040144001c15502c8801029a0f24049403000c0c00a00e5084150b02225000c0e215895146c0248142c030420140949911103054043c2900c08800c540071444040100030070100f1039022465861120141d203400b0400c00044c1082d4a801c207c240381000c5420114850650b81c14401d88503116450300b6181241c00c0028501c1e0f018107116640301c000218041c00398115500c541c810340c2060910000b916000600d040301249080e98280020f00c1c12109581551204c88000d40007803450100c441011851300400c52003c0200c0301c1150740b0784c84828504144003076580b40d607114860030003482c01c5964401c1258490070f0803c41d4040c02c0148424006130080c4207040345500c90703500300b0f501d81d0103015071040c1c26003040031080d000d101031508110100303511440d803850b01c2164860300c400c01e00c03d24085c440044e1070540310700340 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 775702068 1250 775700818 775700857
    0x3152a0e0d1a0403080702030f0f071110030e070801020a1b17030903190c03021b03010b0a030602040807050d15050603100f02092b08160c08030304050d020c0d0305 72
    0xb224007200400b01000c107000ba60074424403041540c001081a44081684047c605108800188c08094440d440824128680c082899420b02c40d000b01c00400c0c00e18010501e4505104100d40580a00354281d213055041c0203840300014906418001c5964801036030b80c907441d01c400d0204114010b01c0c0340010503601e0700c800301003600034038140304021800384101c20000c54a81d50307020243c2003541c03400c001030003c011801072844000398002490000c400e108040d05070007501080c001c20300410004a1065116044034400018014603500030001c1e00c58403015500065121014801042e0b03102c08010a0386695103da210000d62651006030451001002e82e00150440d80f8664155411040424070096002071080003610701240c0444420040c032070358016041149094100307000200b82c000d84010380001e01c8034000c0c40301d84000c0f0a0140d010b41c4082c02c1c5030300e5210342070b503070340003102c048806109405001401a0001a1281c0d105200504401d40c90350159070445143d00000c0115005040304d45 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 775703318 1250 775702068 775702073
    0x7090b0d112206020c090c031f140102010f051b0a0e0607060506041b05041e0b0408070e0f0f160201140a0e0d0314060411070501050103152a0e0d 64
    0x180142000b000c0960030726500500e01c03040c0c2035a40840e500140a5500c40102110035484450106620510b54071000ea06c0341d42c2e090842c0340150002441e218505000c080115004282c00c45040d40d0050030790080240c807250340304400403210f00f51a2a91110b9001c10440510503005005240301002854110b040740d007101d022803002e80000c501100c0c819200d004100d80740c2028030a00c2503408400d9000445508401d8002c2d2452066000300e5046920460041d83c0292802d2104001028281d08051b5210b5454034204d0301c2d1240350050480743e0f9040d20101da0105503500c055400340c598200d1039132441c0c540418041060410710207200a55488000c501100300350301d41c5507071103240c0c40000030918480c2087c5a83c01c00c121900e94500703244c40c041d10821603c201981c000d0b4051000c1c1c40002e00d41c43e4490306083c4902605000801c958241000402044181041444d10925581040c002034096000041e00d001d00f50028640c02031103441300c00303005032017500040c00c1c81001400d400d00c0603007070780c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 775704568 1250 775703318 775703351
    0x106121101120513060f051b1e072d030e0609040609090c03030e01020f0304090b0d05370b060d060e0d020105090d05040e0414011103071e0807090b0d 66
    0x101c2d4644113a031002c169003424480d2502400303402902c445010426440e001013007a240030035014102d50700500104510345074002209016124000e100146a1507440618250802e40b80e40c0d03900319900030307141c0b46104541c495803042c042c5041d41a265603912518100c00d101071908603081c56030384503840f0f41000904964034440e21541074083e8040803d03080c194203010302100d4180d8034080c11075200c3d416003540b148011060703a06450210401144c05644100040c001d0000300402502da4000c015441c0600c4419007500c0040c0900d45005107020101d003100050844140e4501a01d0020404c00180140c60550301c020170b0300d407184030002400042412490318052a081c01000541c0d99141800b87c945803c000c40d0005029a242013450a400d002d951480188003a1004000b00c01310381d190b00c120442900000d502d0303041d02e004940c60f0b29003880001c14200840c2d0b00010a400c1d00719450040510540340d852248075140c50707440d03401d4504084641d00e50b00c01c1c05441c0042e961400c9080740c55004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 775705818 1250 775704568 775704571
    0x2d18010212041412092b120c290f1003170d0605060306030a021003140406050f07110c0622060e1c0f02011d03010e0d02070801061211011205 62
    0x184011184003222801481d02d0004200c2521314079601c00d00c80c4820a07501e080000b40e0010301440d0038030590007072002c80281504031030002844803442d40707803003c0d006d6848002180c0b0785000d080050521290701068149180781e2403940401032400c40e0011b42c52480004d60182c021040c4019007021b07075aa500c40c0c8006620b02042d00703111407400030b000c1009039290300503003000d00f02c101c440c07901d036007010400242d07262614070009000741403407003001c5007481c029441044116503490703800109161900c2e0031401020300b214041200074050002c11001846101c100c1114580c00006200d0b0101000170880c0c00d400444140c0400320308a0b11490070320f034280e5003030f000424860700c031a0915001c00c0200311400360511a07281d40e5030404107414000c07034442200d40211980a0030030215904c80400307130310b0346010344010003a0150b007000c10400710302d10002025800480c5507800d5808054403410071600307852072403140070344881c081312655012466510300952030f144141408000e911032840c0100c140c1c1c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 775707068 1250 775705818 775705823
    0x20616020f0d0201020d060b090a1413110a11160621060308030906130f02040b010521060f030a02030a110a180608120304052d030f032d1801021204 65
    0x10080386082842c1b92600943c00038041d10042c007818112070501040d02d0002c203204201d403001000049030303081e031075002d6440c004030648141801503500f4804d0800b000d070302c0888407000040c02240148400c07000410011020501da45851040519100c000c0714400d20601c240540d02400d1620f1a00d60b2003d4070402d80298401d444d080e03141d04d41043c00340d00b400f10003403060b10062901140540011200070b42e031020664101c400103940740b0400c004a50174000c0210b5899480b19681c03602603020008030b0418400c0904540e00041005480c05045d121000b0031002505980807010040005900d0685a2101440541582c116640d10b0414998418070502a1112180c0c1e0344000d20003800c0510103d5000c001c40303020280344d0304150b5101e968414000310f0380f000405602d4400001c034400c0c0d8443c4119402e407041203035118640100a400c140e48107a500f0801003120703103511a00044580103c000c015400c4800000b143c0d034013040410110104800307090300355402c01414809440f041d4440d03014a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 775708318 1250 775707068 775707071
    0x140d020a020f011e0f051c090b0c09030718020d020316020c0a0b09010e0102210901201510031e1a0609060607140601062d020616020f0d0201 62
    0xe00d40144140d04182082d8a410000c01c4240f103d00d2079500a11030f4207025541ca404180342007482403c031203d020b1000481256561050b510704104180d0300540e02d8140035000302c009035211026402c0d024450f1020300303605604800030030041104d101e041e4940f0702c505500054980003050250101720380c4200c45000c0c10b4030f4964040c692281c2d04001c82011a0310035902001c1440c10228456030754041c0300d80c19030420150000d4009141d1080c00745011000700c54282e424441e42000740300d0029001003025038001400c2c507070290a1003841ca156207804500302d202070029018192100c0c500c28600504a201319289010000001004803480c0369a500d07510304812040502071800b640e210342c0b0040c80e01e503081e100b4000e1060668422034115000310040fa250b5640304070701d15011090804042c000c040501680b400000c40c550003c0c41e210000c40552031201d445840103054482e8040c403041c1c0a4010703404000085c44010500807042428803490040ba82d000c035440310800e01d048484511400182d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 775709568 1250 775708318 775708333
    0x1401140f06091819090b0406230114011101060b030406050402180702060403030f0c02070612140a020a1b0c03030507020f1e12070302150f19090303090504050705090d140d02 76
    0xfa25901c005100609014011310249007a42c65140901b01c010340050f01007980d542003000c402e500e55410304d44084400302d2401d100d681d078603420194400141e40c0b00b804106014a0014242f006100300400d481d0305803180c0c4e0454880c1d80b280c00c001d21008000b240c106100200c940d00c1ca00c2941c00c0c0f203200d000c55a00a09041c905450001c06441c00c0105000380366080c880081c0d09180c020a1000607100c0f2881d00a8050114141e8000030b0507034a004031180c502603100384411031000d07800401c0490402e441d2aa030f8425450003007401307400d480b0000343c490003500700d0600000b403081c80105204c500061600419062250000c0e003481a903068149a002054049041909110340e242d40c1b5804954040c00501b840e50300071403032139242c0320036901400710005a190041c02034801603c04032002480214000700403c580944000002d01061303000c035140107000105460310b40650343c801d03035060782c640781040c4001e0207202000b0340c02a0100c80380559950103200c501e000300403031824081c4640c01000c81d07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 775710818 1250 775709568 775709581
    0x60307120c06140f03042a12021c1e0812131109060a050405100306090311060a051311030c04111b0309030d050a0c170d1401140f060918 60
    0x3101c25041c0300403d01c14140540882c584440d400d403544a0307004800043c4072007100f0303061200900794803400315502c0c01004002c180c07007a52900d240d2840d0b2007070703801c017560304101c1544400443c6803810080500d0001000c0d142c810040281d0b502104d0301c02c80f81c0e1414800d05d01c0d60042150002c880004240346003d240e41d05010840740314003030fa1401640c501c221810110080b800c03c201e10302403c5e018548820104581d611001a0040215003040041212380001d180040c48003502806010491045001042020800f441840e005036018105004480710565480010206429150f903050141005140032929180503440502c00c8440c600c56030b85c1c10303c41c0382003440106410541d01c15442071010708440e40307001a14004240e040c0c01c0540e1034084e6184110340e010001d03540203080c0c1007600415214158030340061302c003502d8200f000b80080000c04c04101800d0400f48a10004201c10840b6030b40541802249c4401d10100588507528011465002c204009015402441501d51030300c1003055 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 775712068 1250 775710818 775710827
    0x60c012c0d14070c171c08010b180409050109030807080709030222110903010c050c030a08040f0618030e0d03020607081b13050109050108012916060b0a1502070905060307120c06 78
    0x1002c86d0000300b284984984080b0042c00007005004010284000040e81540d4681c1c45031150003100000713105001c00c91041c6407040c0078104904003280032070000744c00305086c203019041041c03203a072280c0d5a4518080c07a64007080101d5000d18000f02c81c11803080009041c01e08a07001c1e04000030000100a942c4e00c409000341400c4546a80101d401c024040c010011650f0001c000c4401c010740c180707001d4405880341c2c2009040340c054cd00700201254030703001c14603511029030f10000349501d010362140070b280081d03070040c0210380c07800c000000c0040e08540c00280295003d00a80f81d000700d00c4002c0d11030940c81ca270052403650b03882410094005210a68104031b01d681c4001780102a200c02e02c0e00e410294500200741a040d014080500345400001192507a000d18003070a41e003148a42d818503410901c0607050031002001140000d40c0114a15a40800d0074a20040e01615040c21a401040a036190813002d100a010103004580e260084807c005004030402201e90500d9001d803201440c4035103001800740 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 775713318 1250 775712068 775712083
    0xc091403010e0316031103030403080601090b030c0a030906020408121902011b03020c2802040609200706090b1e010608010f030209090c060c012c0d14070c17 69
    0x5100741e040214822603000044150703601c614007442c910784180e41510307040d507400f50305800b4492644004400c100a06910003103050007200c0c01c1e02d40f0710003d500c0c0c0312071000318482140d061021200800c10080c2d4248a80e000b1402c841c02614014181600d440b041810f00b240440c504c0740204c401324018280c00c1090090812107502130000b04015020381c0c05031510b8562044401080c154003080700000200144030614070b500034041d00c0d509803440d0503400d041c04410054142c0c015803820202150409051140e08000ca101000507281801414040c48a950080000b02d54958460101600041c4036401944c0070740c3c0c86595002c9220690b08000c01c4001d0140c0c040d10400403104010491010104c4125041d6034046d42c6001b0150340343e40c0c4191800c094402202d4010500041d0075403080740c10b501504240100c1021142e1010600301d1601c4101e80149100a00d40c011480300e03c00e440c054504810803085880c030301030030306407130f0780700c100e41d00d45158080382900c00c902c001d1001410b024010071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 775714568 1250 775713318 775713359
    0x60504140115050a030609060603050a1a010509061602060a03020903240a0c030b0306042a050916020a050f030d0e1914010e010e150c0408190f060c09 66
    0x8031250324000d8203040d000000c900031014808000f64146501e4440c1d040320010341590182400707496540d4000400515003140c904515920700f900d102101c801c000e11641e205c0340b059407000c0c144002c403410024140d02400000d4070f60496281c0c00d00058a40a028110000043d100143c0740d0f51104241800e081041f114215540d00708409040c0b403444121030305400c0320f50394100007800c4088480540092410700215030703162055004200402000010043c40d002052a14102d22030802c0c3e40e8442041a600485901503140c0e0001a02c250380341e4044070000742c03144110b0302c6020660b2659401d140f1071120028840d040016010005149402100005180840205420031a160040454800c0b58038000d210340711140c0d0605903820250009810341c16074100030800e4140a86010f0394800440032040c100002010000d1f0034405040709139411607403c40042c000342c0a0485040c40500c035a05401c071188840c072003c1c5800314030315106512091032141c5908901a050088107a01451003c1c0d60 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 775715818 1250 775714568 775714601
    0x5010b0403051c111f0608010605092a1606050601050c0a02010f09150804051e150c160506090f010c20100203160905040b0a1e03020301050a060504 65
    0x420000328005022103580041c0304510b403c5821042044440700c0540e085580d4620426038840c0000d181ca2201c04002c510303080d410400705079143c01ca41c1c241c6d1040c0c030945500502e510700068250300804101d070803600c0517501c1049003008250440401da00410850707502070b803803141d1340c1040140700c0c8510b64101d8005d080003070401150368171095441444030002810095001421400c1c24001d070500d034050111100085452807120000074020f541c01c84041c0c400b407146242c42c070313045800d481c00d0350040c0900e00050600e1180c41111a091044e001d00070310100d00c01006201c5600602e510f418240d07a200e80050000c6050071100da518041c2e03041028410340e4548500301e01100d4001c11001c104050f050368400c0d00d01300208100b8180011540811000d070300000c100001c955207520074041c445074076250442d0070340e1030750b0074002140c03500e00f140c64002404400c14806000c01d104410368011a0551004840f5101c0c1e0110f800e481c800d492080c2c0d04c075200c2005001ba49000d01421180c560340550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 775717068 1250 775715818 775715827
    0x30c0305150409140f0d080f060901031709061c0e011a0409050709020d2406140d0e0f0f011a03030417190f121806120f0f0f05010b 58
    0x42020070345051180901c255aa80c007100104804c403030004000c460303502d054406605c1d6460380f19031204201018180020201400681d0408100803290701481d8058030a14150703086944405083c01c415086103070404d400d0000800e0740da00c030310080c20140044d10302078060031201041c0b001656100d0140764156410701c40b035075000c84084070318040c029501712000300703294007241090390421100340c11118074107000140007800e8104039082240c00c014082103a0441020440c566140d000c40d40c020782000940b1100200703c20f814910241c448503044280002d1072080c4400b859140c104030010400880d000b0003040f1040354402e204400c4481407144150240c25100c01c002510b030b10131401401e5003c850710084940c03e600070402c10390590030310901e064248103175050240c814441504103c03054010180040c1e8443c0c0f05002240c00d49007004070040c159410203a0035540340d40e4887c080900c07955103130968404c400140c09101c403140c041c03180004101501c10694015944140c0041c0b642100400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 775718318 1250 775717068 775717081
    0x21040501120c0f030c0c050307080403120503070203030402010c290f010902210921032a1e0f0f1801140a030213030c2607050f0909100219030c0305 65
    0x10122143e15402c2c0b50002c1c1c07081c800841604c0240c92030002402500c000301d240e400b0000890028010307240500d0440c0c1034841c3c2c0390303801c48492004450140058006001050065003e076005081c214425250b40008164007100c2620034044404c0911552009006001d1416134276100c00c1d001d045000820b6145c20b1410714100b811150081421514041010005403511814044241107071001c541c10103804d241c240c680704030340d001901d1443c44503600c2002e110106d0b5054900f00700e54003840740100d050801100e41c60f90401c4d0240c140702410350301040b0f415444040031008011040240e081c194440302d4245101c2121160086041c2c140100c0e0040c02c01c800d150101500d581d8042c5240241e0f441c0c03918501556984002d50005000101001021072a10b41824a020064100d44500d01e006003e8040c26961110701d4031600350801d1030480801858107103400115800074251084074415510310710480201da002801804400003000300d0210318903450b000d80d21080020707107800c0c08a4200b00c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 775719424 1106 775718318 775718327
    0x1080c0111210d110717031905090706091a0301031b15030204050310060f05150702100806030609011103070e1c050106090b04090803011721040501120c 67
    0x3603407039248810341109171806030f41c0115810300c07410380c0d0366204202584081e04004004042c8151450344c1070312802141d01450700030f4001d164091034040000c20420544d044250501448800040c0c6c1c1469003041c0d90549400101340500c004480d40e001c0f4040c4010350050013480b00c501c40204920f500341e40074200b201d006a05541800b034000301c00200b11750042c000d01d00314408404040c0070504012020040102c1c81011151404500f43c00291600009400c01400240c1034010884542018400c030368101901200038403062042d4425a4140e00004113948204030800a031045595660340644080041d091422214a01503091840c06020303103000c1c4c2c10f41142804591191420544101ea00e07203500000c8003401c40e403d00c1e1010040301e5540301004d4072031103414080c040622411410484e60444000c0d0950384502e000000741c5039544604580031218a082000f01034550031 = true := by decide +kernel

theorem cover : BRFrame.Cov 775539568 775719424 := by
  have h0 := BRFrame.cov_init 775539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 775539568 ≤ n) (h2 : n < 775719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
